import argparse
import re
import subprocess
import tempfile
import contextlib
import io
import logging
import struct
import hashlib
import time
import json
import os
from dataclasses import dataclass, field
from typing import List, Tuple, Optional, Dict, Any
from enum import Enum
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor, Future
from collections import defaultdict
from threading import Lock

from uefi_firmware import AutoParser


class FirmwareArchitecture(Enum):
    UNKNOWN = 0
    QUALCOMM_LK = 1
    QUALCOMM_ABL = 2
    MEDIATEK_PRELOADER = 3
    MEDIATEK_LK = 4
    EXYNOS_UBOOT = 5
    UEFI_EDK2 = 6
    SPRD_BOOTLOADER = 7
    HUAWEI_DHTB = 8
    XIAOMI_FBPK = 9


class CommandExecutionResult(Enum):
    SUCCESS = "SUCCESS"
    FAILED_UNKNOWN = "FAILED_UNKNOWN"
    FAILED_NOT_ALLOWED = "FAILED_NOT_ALLOWED"
    FAILED_TIMEOUT = "FAILED_TIMEOUT"
    BLOCKED_REBOOT = "BLOCKED_REBOOT"
    DEVICE_DISCONNECTED = "DEVICE_DISCONNECTED"


@dataclass
class OemCommand:
    command_string: str
    source_offset: Optional[int] = None
    source_file: Optional[str] = None
    is_critical: bool = False
    requires_unlocked: bool = False
    execution_result: Optional[CommandExecutionResult] = None
    execution_output: str = ""
    execution_time_ms: float = 0.0


@dataclass
class FirmwareAnalysisResult:
    architecture: FirmwareArchitecture
    commands: List[OemCommand]
    total_strings_found: int
    hash_sha256: str
    file_size: int
    extraction_method: str
    metadata: Dict[str, Any] = field(default_factory=dict)


class AdvancedFirmwareParser:
    
    VALID_OEM_COMMANDS = [
        'unlock', 'lock', 'device-info', 'off-mode-charge', 'enable-charger-screen',
        'disable-charger-screen', 'reset-charger', 'select-display-panel',
        'get_unlock_data', 'unlock-critical', 'lock-critical', 'flashing-unlock',
        'flashing-lock', 'flashing-get-unlock-data', 'flashing-unlock-critical',
        'flashing-lock-critical', 'verified_cmd', 'get-psid', 'get-soc-id',
        'get-security-version', 'get-board-id', 'get-warranty-bit', 'get-unlock-ability',
        'get-unlock-data', 'at-factory', 'factory-reset', 'fb_mode_set',
        'fb_mode_clear', 'erase-config', 'read-config', 'write-config',
        'append-cmdline', 'boot-sd', 'boot-partition', 'boot-mmc'
    ]
    
    def __init__(self, logger: logging.Logger):
        self.logger = logger
        self._string_cache: Dict[str, List[str]] = {}
        self._lock = Lock()
    
    def _is_valid_oem_command(self, cmd: str) -> bool:
        cmd_lower = cmd.lower().strip()
        
        if len(cmd_lower) < 3 or len(cmd_lower) > 40:
            return False
        
        if not re.match(r'^[a-z0-9][a-z0-9_\-]*$', cmd_lower, re.IGNORECASE):
            return False
        
        if cmd_lower in ['x2', 'x3', 'x4', 'x5', 'x6', 'x7', 'x8', 'x9', 'x10']:
            return False
        
        if cmd_lower.startswith('x') and len(cmd_lower) <= 3:
            return False
        
        if re.match(r'^[0-9]+$', cmd_lower):
            return False
        
        for valid in self.VALID_OEM_COMMANDS:
            if valid in cmd_lower or cmd_lower in valid:
                return True
        
        if re.match(r'^[a-z]+(_[a-z]+)+$', cmd_lower):
            return True
        
        if cmd_lower in ['test', 'demo', 'debug', 'eng', 'user', 'factory', 'prod']:
            return True
        
        return False
    
    def _calculate_entropy(self, data: bytes, window: int = 256) -> float:
        if len(data) < window:
            return 0.0
        
        import math
        
        entropy_sum = 0.0
        chunks = 0
        
        for i in range(0, len(data) - window + 1, window):
            chunk = data[i:i+window]
            byte_counts = defaultdict(int)
            for byte in chunk:
                byte_counts[byte] += 1
            
            chunk_entropy = 0.0
            for count in byte_counts.values():
                probability = count / window
                if probability > 0:
                    chunk_entropy -= probability * math.log2(probability)
            entropy_sum += chunk_entropy
            chunks += 1
        
        if chunks == 0:
            return 0.0
        
        return entropy_sum / chunks
    
    def _find_obfuscated_strings(self, data: bytes, start_offset: int = 0) -> List[Tuple[int, str]]:
        results = []
        xor_keys = [0x00, 0xFF, 0xAA, 0x55, 0x5A, 0xA5]
        
        for key in xor_keys:
            for alignment in range(4):
                for offset in range(start_offset, min(len(data) - 64, start_offset + 0x100000), 4):
                    if offset % 4 != alignment:
                        continue
                    
                    decrypted = bytearray()
                    for i, byte in enumerate(data[offset:offset+64]):
                        decrypted.append(byte ^ key)
                    
                    strings = re.findall(rb'oem\s+([a-z_][a-z0-9_]{2,32})', decrypted, re.IGNORECASE)
                    for match in strings:
                        try:
                            cmd_str = match.decode('ascii')
                            if self._is_valid_oem_command(cmd_str):
                                results.append((offset, f'fastboot oem {cmd_str}'))
                        except UnicodeDecodeError:
                            pass
        
        return list(set(results))
    
    def _parse_lk_bootloader(self, data: bytes) -> List[OemCommand]:
        commands = []
        
        lk_magic = b'\x88\x16\x88\x58'
        lk_offsets = [i for i in range(len(data) - 4) if data[i:i+4] == lk_magic]
        
        for lk_offset in lk_offsets:
            cmd_table_offset = lk_offset + 0x200
            if cmd_table_offset + 0x100 > len(data):
                continue
            
            for i in range(0, 0x100, 8):
                ptr_offset = cmd_table_offset + i
                if ptr_offset + 8 > len(data):
                    break
                
                cmd_ptr = struct.unpack('<I', data[ptr_offset:ptr_offset+4])[0]
                name_ptr = struct.unpack('<I', data[ptr_offset+4:ptr_offset+8])[0]
                
                if cmd_ptr < len(data) and name_ptr < len(data) and name_ptr > 0:
                    try:
                        name_end = data.find(b'\x00', name_ptr, name_ptr + 64)
                        if name_end != -1:
                            cmd_name = data[name_ptr:name_end].decode('ascii', errors='ignore')
                            
                            if self._is_valid_oem_command(cmd_name):
                                commands.append(OemCommand(
                                    command_string=f'fastboot oem {cmd_name}',
                                    source_offset=name_ptr,
                                    source_file='lk_bootloader'
                                ))
                    except Exception:
                        continue
        
        return commands
    
    def _parse_mtk_bootloader(self, data: bytes) -> List[OemCommand]:
        commands = []
        
        mtk_magic = b'MTK'
        mtk_offsets = [i for i in range(len(data) - 3) if data[i:i+3] == mtk_magic]
        
        for offset in mtk_offsets:
            search_range = data[offset:offset+0x10000]
            strings = re.findall(rb'oem\s+([a-z_][a-z0-9_\-]{3,30})', search_range, re.IGNORECASE)
            for match in strings:
                try:
                    cmd_str = match.decode('ascii').lower()
                    if self._is_valid_oem_command(cmd_str):
                        commands.append(OemCommand(
                            command_string=f'fastboot oem {cmd_str}',
                            source_offset=offset,
                            source_file='mtk_bootloader'
                        ))
                except UnicodeDecodeError:
                    pass
        
        return commands
    
    def _parse_uefi_protocols(self, parser: AutoParser) -> List[OemCommand]:
        commands = []
        
        with tempfile.TemporaryDirectory() as tmpdir:
            old_stdout = io.StringIO()
            with contextlib.redirect_stdout(old_stdout):
                parsed = parser.parse()
                if parsed is not None:
                    parsed.dump(tmpdir)
            
            pe_files = list(Path(tmpdir).rglob('*.pe'))
            for pe_file in pe_files:
                pe_data = pe_file.read_bytes()
                
                strings = re.findall(rb'oem\s+([a-z_][a-z0-9_\-]{3,30})', pe_data, re.IGNORECASE)
                for match in strings:
                    try:
                        cmd_str = match.decode('ascii').lower()
                        if self._is_valid_oem_command(cmd_str):
                            commands.append(OemCommand(
                                command_string=f'fastboot oem {cmd_str}',
                                source_file=str(pe_file.name)
                            ))
                    except UnicodeDecodeError:
                        pass
        
        return commands
    
    def analyze_firmware(self, firmware_path: Path, force_string: bool = False) -> FirmwareAnalysisResult:
        
        firmware_data = firmware_path.read_bytes()
        file_hash = hashlib.sha256(firmware_data).hexdigest()
        file_size = len(firmware_data)
        
        detected_arch = FirmwareArchitecture.UNKNOWN
        all_commands = []
        extraction_method = "none"
        raw_strings = []
        
        entropy = self._calculate_entropy(firmware_data)
        self.logger.debug(f"Firmware entropy: {entropy:.4f}")
        
        if firmware_data[:2] == b'MZ':
            detected_arch = FirmwareArchitecture.UEFI_EDK2
            
            with tempfile.NamedTemporaryFile(suffix='.bin', delete=False) as tmp:
                tmp.write(firmware_data)
                tmp_path = Path(tmp.name)
            
            try:
                parser = AutoParser(tmp_path.read_bytes(), search=True)
                all_commands = self._parse_uefi_protocols(parser)
                extraction_method = "uefi_protocol_parsing"
            finally:
                tmp_path.unlink()
        
        elif firmware_data[:4] == b'\x88\x16\x88\x58':
            detected_arch = FirmwareArchitecture.QUALCOMM_LK
            all_commands = self._parse_lk_bootloader(firmware_data)
            extraction_method = "lk_symbol_table_parsing"
        
        elif b'MTK' in firmware_data[:0x1000]:
            detected_arch = FirmwareArchitecture.MEDIATEK_LK
            all_commands = self._parse_mtk_bootloader(firmware_data)
            extraction_method = "mtk_string_extraction"
        
        if not all_commands or force_string:
            raw_strings = re.findall(rb'oem\s+([a-z_][a-z0-9_\-]{3,30})', firmware_data, re.IGNORECASE)
            for match in raw_strings:
                try:
                    cmd_str = match.decode('ascii').lower()
                    if self._is_valid_oem_command(cmd_str):
                        cmd_obj = OemCommand(command_string=f'fastboot oem {cmd_str}')
                        if cmd_obj not in all_commands:
                            all_commands.append(cmd_obj)
                except UnicodeDecodeError:
                    pass
            extraction_method += "+string_extraction"
            
            obfuscated = self._find_obfuscated_strings(firmware_data, 0)
            for offset, cmd_str in obfuscated:
                cmd_obj = OemCommand(command_string=cmd_str, source_offset=offset)
                if cmd_obj not in all_commands:
                    all_commands.append(cmd_obj)
            extraction_method += "+obfuscated_extraction"
        
        unique_commands = []
        seen = set()
        for cmd in all_commands:
            if cmd.command_string not in seen:
                seen.add(cmd.command_string)
                unique_commands.append(cmd)
        
        return FirmwareAnalysisResult(
            architecture=detected_arch,
            commands=unique_commands,
            total_strings_found=len(raw_strings),
            hash_sha256=file_hash,
            file_size=file_size,
            extraction_method=extraction_method,
            metadata={'entropy': entropy, 'detected_by': extraction_method}
        )


class FastbootOEMHarness:
    
    def __init__(self, logger: logging.Logger, fastboot_path: str):
        self.logger = logger
        self.fastboot_path = fastboot_path
        self._device_state_cache = None
        self._cache_lock = Lock()
        self._execution_history: List[OemCommand] = []
    
    def _check_device_connection(self) -> bool:
        try:
            result = subprocess.run(
                [self.fastboot_path, 'devices'],
                capture_output=True,
                text=True,
                timeout=5,
                shell=False
            )
            devices = [line.strip() for line in result.stdout.strip().split('\n') if line.strip()]
            return len(devices) > 0
        except Exception:
            return False
    
    def _execute_with_retry(self, command: List[str], max_retries: int = 2, retry_delay: float = 1.0) -> Tuple[int, str, str]:
        last_error = None
        
        for attempt in range(max_retries):
            try:
                result = subprocess.run(
                    command,
                    capture_output=True,
                    text=True,
                    timeout=15,
                    shell=False
                )
                return result.returncode, result.stdout, result.stderr
            except subprocess.TimeoutExpired as e:
                last_error = e
                if attempt < max_retries - 1:
                    time.sleep(retry_delay)
            except Exception as e:
                last_error = e
        
        return -1, "", str(last_error) if last_error else "Unknown error"
    
    def _classify_fastboot_response(self, stdout: str, stderr: str) -> CommandExecutionResult:
        combined = (stdout + stderr).lower()
        
        if 'unknown command' in combined:
            return CommandExecutionResult.FAILED_UNKNOWN
        elif 'not allowed' in combined or 'permission denied' in combined:
            return CommandExecutionResult.FAILED_NOT_ALLOWED
        elif 'timeout' in combined:
            return CommandExecutionResult.FAILED_TIMEOUT
        else:
            return CommandExecutionResult.SUCCESS
    
    def _is_reboot_command_advanced(self, cmd: str) -> bool:
        cmd_lower = cmd.lower()
        
        reboot_patterns = [
            r'(^|\s)reboot(\s|$)',
            r'reboot-bootloader',
            r'reboot\s+recovery',
            r'reboot\s+fastboot',
            r'reboot\s+edl',
            r'reboot\s+download',
            r'reboot\s+fb',
            r'(^|\s)restart(\s|$)',
        ]
        
        for pattern in reboot_patterns:
            if re.search(pattern, cmd_lower):
                return True
        
        return False
    
    def execute_command_harness(self, command: OemCommand, simulate: bool = False) -> OemCommand:
        
        if self._is_reboot_command_advanced(command.command_string):
            command.execution_result = CommandExecutionResult.BLOCKED_REBOOT
            command.execution_output = "Blocked by reboot protection filter"
            return command
        
        if not simulate:
            if not self._check_device_connection():
                command.execution_result = CommandExecutionResult.DEVICE_DISCONNECTED
                command.execution_output = "No fastboot device detected"
                return command
            
            start_time = time.perf_counter()
            
            oem_param = command.command_string.replace('fastboot oem', '').strip()
            full_command = [self.fastboot_path, 'oem', oem_param]
            
            retcode, stdout, stderr = self._execute_with_retry(full_command)
            
            end_time = time.perf_counter()
            command.execution_time_ms = (end_time - start_time) * 1000
            
            if retcode == 0:
                command.execution_result = CommandExecutionResult.SUCCESS
                command.execution_output = stdout if stdout else "OKAY"
            else:
                command.execution_result = self._classify_fastboot_response(stdout, stderr)
                command.execution_output = stderr if stderr else stdout
        else:
            command.execution_result = CommandExecutionResult.SUCCESS
            command.execution_output = "Simulation mode"
        
        with self._cache_lock:
            self._execution_history.append(command)
        
        return command
    
    def batch_execute(self, commands: List[OemCommand], max_workers: int = 1, simulate: bool = False) -> List[OemCommand]:
        results = []
        
        for idx, cmd in enumerate(commands, 1):
            self.logger.info(f"[{idx}/{len(commands)}] Testing: {cmd.command_string}")
            result = self.execute_command_harness(cmd, simulate)
            
            if result.execution_result == CommandExecutionResult.SUCCESS:
                self.logger.info(f"       Result: SUCCESS")
                clean_output = result.execution_output.replace('\r', '').strip()
                if clean_output and clean_output != "OKAY":
                    for line in clean_output.split('\n')[:2]:
                        if line.strip():
                            self.logger.info(f"       {line.strip()[:150]}")
            elif result.execution_result == CommandExecutionResult.BLOCKED_REBOOT:
                self.logger.info(f"       Result: BLOCKED (reboot command)")
            elif result.execution_result == CommandExecutionResult.FAILED_NOT_ALLOWED:
                self.logger.info(f"       Result: FAILED (command exists but bootloader locked)")
            else:
                self.logger.info(f"       Result: FAILED (unknown command)")
            
            self.logger.info("")
            results.append(result)
        
        return results


class OemCommandReporter:
    
    def __init__(self, logger: logging.Logger):
        self.logger = logger
    
    def generate_report(self, analysis: FirmwareAnalysisResult, execution_results: List[OemCommand]) -> str:
        
        report_lines = []
        report_lines.append("=" * 70)
        report_lines.append("FASTBOOT OEM COMMAND EXTRACTION REPORT")
        report_lines.append("=" * 70)
        report_lines.append(f"File: {analysis.hash_sha256[:16]}...")
        report_lines.append(f"Size: {analysis.file_size} bytes")
        report_lines.append(f"Commands Found: {len(analysis.commands)}")
        report_lines.append("")
        
        report_lines.append("-" * 70)
        report_lines.append("COMMAND EXECUTION SUMMARY")
        report_lines.append("-" * 70)
        
        stats = defaultdict(int)
        for cmd in execution_results:
            if cmd.execution_result:
                stats[cmd.execution_result] += 1
        
        for result_type, count in stats.items():
            report_lines.append(f"  {result_type.value}: {count}")
        
        report_lines.append("")
        report_lines.append("-" * 70)
        report_lines.append("DETAILED COMMAND LIST")
        report_lines.append("-" * 70)
        
        for idx, cmd in enumerate(execution_results, 1):
            report_lines.append(f"\n{idx}. {cmd.command_string}")
            if cmd.execution_result:
                report_lines.append(f"   Result: {cmd.execution_result.value}")
            if cmd.execution_output and cmd.execution_output not in ["OKAY", "Simulation mode"]:
                output_preview = cmd.execution_output[:200].replace('\n', '\n   ')
                report_lines.append(f"   Output: {output_preview}")
        
        report_lines.append("")
        report_lines.append("=" * 70)
        
        return '\n'.join(report_lines)
    
    def export_json(self, analysis: FirmwareAnalysisResult, execution_results: List[OemCommand]) -> str:
        export_data = {
            'analysis': {
                'hash': analysis.hash_sha256,
                'size': analysis.file_size,
                'extraction_method': analysis.extraction_method,
                'metadata': analysis.metadata
            },
            'commands': [
                {
                    'command': cmd.command_string,
                    'result': cmd.execution_result.value if cmd.execution_result else None,
                    'output': cmd.execution_output[:500] if cmd.execution_output else ''
                }
                for cmd in execution_results
            ]
        }
        return json.dumps(export_data, indent=2)


def setup_logging(verbose: bool = False) -> logging.Logger:
    log = logging.getLogger('FastbootOEMHarness')
    log.setLevel(logging.DEBUG if verbose else logging.INFO)
    log.propagate = False
    
    if log.handlers:
        for handler in log.handlers[:]:
            log.removeHandler(handler)
    
    console_handler = logging.StreamHandler()
    console_handler.setLevel(logging.DEBUG if verbose else logging.INFO)
    
    if verbose:
        formatter = logging.Formatter('[%(levelname)s] %(asctime)s - %(message)s', datefmt='%H:%M:%S')
    else:
        formatter = logging.Formatter('%(message)s')
    
    console_handler.setFormatter(formatter)
    log.addHandler(console_handler)
    
    return log


BL_MAGIC_PATTERNS = [
    b'MZ',
    b'\x88\x16\x88\x58',
    b'FBPK',
    b'DHTB',
    b'\x7FELF',
    b'ANDROID!'
]


def main():
    parser = argparse.ArgumentParser(
        description='Fastboot OEM Command Extraction and Testing Framework'
    )
    parser.add_argument('file', type=str, help='Firmware or bootloader file name')
    parser.add_argument('--test', action='store_true', help='Execute commands on connected fastboot device')
    parser.add_argument('--simulate', action='store_true', help='Simulate execution without actual device')
    parser.add_argument('--force-string', action='store_true', help='Force string-based extraction')
    parser.add_argument('--verbose', action='store_true', help='Enable verbose debug output')
    parser.add_argument('--json', type=str, help='Export results to JSON file')
    
    args = parser.parse_args()
    
    logger = setup_logging(args.verbose)
    
    firmware_path = Path.cwd() / args.file
    
    if not firmware_path.exists():
        logger.error(f"File not found: {firmware_path}")
        return 1
    
    logger.info(f"Analyzing: {args.file}")
    logger.info("=" * 50)
    
    firmware_parser = AdvancedFirmwareParser(logger)
    
    try:
        analysis_result = firmware_parser.analyze_firmware(firmware_path, args.force_string)
    except Exception as e:
        logger.error(f"Firmware analysis failed: {e}")
        if args.verbose:
            import traceback
            traceback.print_exc()
        return 1
    
    logger.info(f"Extracted {len(analysis_result.commands)} valid OEM commands")
    
    if not analysis_result.commands:
        logger.warning("No valid OEM commands found in firmware")
        if not args.force_string:
            logger.info("Try using --force-string to extract all possible strings")
        return 0
    
    logger.info("")
    for idx, cmd in enumerate(analysis_result.commands[:20], 1):
        logger.info(f"  {idx}. {cmd.command_string}")
    
    if len(analysis_result.commands) > 20:
        logger.info(f"  ... and {len(analysis_result.commands) - 20} more")
    
    if args.test or args.simulate:
        logger.info("")
        logger.info("=" * 50)
        logger.info("Initializing Fastboot OEM Harness")
        logger.info("=" * 50)
        
        fastboot_path = Path.cwd() / 'fastboot.exe'
        if not fastboot_path.exists():
            logger.error("fastboot.exe not found in current directory")
            return 1
        
        harness = FastbootOEMHarness(logger, str(fastboot_path))
        
        if args.simulate:
            logger.info("Running in SIMULATION mode")
        else:
            if not harness._check_device_connection():
                logger.error("No fastboot device detected")
                return 1
            logger.info("Fastboot device detected")
        
        logger.info(f"Testing {len(analysis_result.commands)} commands")
        logger.info("")
        
        execution_results = harness.batch_execute(
            analysis_result.commands,
            simulate=args.simulate
        )
        
        reporter = OemCommandReporter(logger)
        report = reporter.generate_report(analysis_result, execution_results)
        logger.info(report)
        
        if args.json:
            json_path = Path.cwd() / args.json
            json_data = reporter.export_json(analysis_result, execution_results)
            json_path.write_text(json_data, encoding='utf-8')
            logger.info(f"JSON report saved to: {args.json}")
    
    return 0


if __name__ == '__main__':
    exit(main())