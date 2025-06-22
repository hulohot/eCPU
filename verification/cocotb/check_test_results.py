#!/usr/bin/env python3
"""
eCPU Test Results Checker

This script parses XML test result files in the sim_build directory to provide
a quick overview of verification status without rerunning tests.
"""

import os
import xml.etree.ElementTree as ET
from collections import defaultdict, Counter
import glob
import argparse
from datetime import datetime

# Rich imports for better terminal output
from rich.console import Console
from rich.table import Table
from rich.panel import Panel
from rich.text import Text
from rich.progress import Progress, SpinnerColumn, TextColumn
from rich.columns import Columns
from rich.tree import Tree
from rich.status import Status
from rich import box

console = Console()

def parse_xml_result(xml_file):
    """Parse a single XML result file and extract test information."""
    try:
        tree = ET.parse(xml_file)
        root = tree.getroot()
        
        # Initialize result structure
        result = {
            'file': os.path.basename(xml_file),
            'tests': [],
            'total_tests': 0,
            'passed': 0,
            'failed': 0,
            'errors': 0,
            'skipped': 0,
            'module': 'unknown',
            'timestamp': datetime.fromtimestamp(os.path.getmtime(xml_file))
        }
        
        # Try to extract module name from various possible sources
        if 'name' in root.attrib:
            result['module'] = root.attrib['name']
        
        # Look for test cases and determine module from classnames
        module_candidates = []
        
        for testcase in root.findall('.//testcase'):
            test_info = {
                'name': testcase.get('name', 'unknown'),
                'classname': testcase.get('classname', ''),
                'time': float(testcase.get('time', 0)),
                'status': 'passed'
            }
            
            # Extract module name from classname
            if test_info['classname']:
                if 'test_' in test_info['classname']:
                    module_name = test_info['classname'].replace('test_', '')
                    # Handle special cases
                    if module_name == 'memory_stage':
                        module_name = 'memory'
                    module_candidates.append(module_name)
            
            # Check for failures, errors, or skips
            if testcase.find('failure') is not None:
                test_info['status'] = 'failed'
                failure = testcase.find('failure')
                test_info['message'] = failure.get('message', '')
                result['failed'] += 1
            elif testcase.find('error') is not None:
                test_info['status'] = 'error'
                error = testcase.find('error')
                test_info['message'] = error.get('message', '')
                result['errors'] += 1
            elif testcase.find('skipped') is not None:
                test_info['status'] = 'skipped'
                result['skipped'] += 1
            else:
                result['passed'] += 1
            
            result['tests'].append(test_info)
            result['total_tests'] += 1
        
        # Determine the most common module name from candidates
        if module_candidates:
            # Use the most frequent module name
            module_counter = Counter(module_candidates)
            result['module'] = module_counter.most_common(1)[0][0]
        
        return result
        
    except ET.ParseError as e:
        console.print(f"[yellow]Warning: Could not parse {xml_file}: {e}[/yellow]")
        return None
    except Exception as e:
        console.print(f"[yellow]Warning: Error processing {xml_file}: {e}[/yellow]")
        return None

def find_xml_files(sim_build_dir):
    """Find all XML result files in the sim_build directory."""
    xml_pattern = os.path.join(sim_build_dir, "*_results.xml")
    xml_files = glob.glob(xml_pattern)
    
    # Filter out empty files
    valid_files = []
    for xml_file in xml_files:
        if os.path.getsize(xml_file) > 0:
            valid_files.append(xml_file)
    
    return valid_files

def group_results_by_module(results):
    """Group test results by module name, keeping only the most recent result per module."""
    modules = defaultdict(list)
    
    for result in results:
        if result:
            # Try to determine module from test names or file patterns
            module_name = result['module']
            
            # If still unknown, try to extract from test names or classnames
            if module_name == 'unknown' and result['tests']:
                # First try classname from any test
                for test in result['tests']:
                    if test['classname'] and 'test_' in test['classname']:
                        classname = test['classname']
                        module_name = classname.replace('test_', '')
                        # Handle special cases
                        if module_name == 'memory_stage':
                            module_name = 'memory'
                        elif module_name == 'instruction_memory':
                            module_name = 'instruction_memory'
                        elif module_name == 'data_memory':
                            module_name = 'data_memory'
                        elif module_name == 'hazard_unit':
                            module_name = 'hazard_unit'
                        break
                
                # If still unknown, try from test names
                if module_name == 'unknown':
                    test_name = result['tests'][0]['name']
                    if 'test_' in test_name:
                        for module in ['alu', 'regfile', 'fetch', 'decode', 'execute', 
                                      'memory', 'writeback', 'hazard_unit', 'instruction_memory', 'data_memory']:
                            if module in test_name.lower():
                                module_name = module
                                break
            
            modules[module_name].append(result)
    
    # Keep only the most recent result for each module
    filtered_modules = {}
    for module_name, module_results in modules.items():
        if len(module_results) == 1:
            # Only one result, keep it
            filtered_modules[module_name] = module_results
        else:
            # Multiple results, keep only the most recent one
            most_recent = max(module_results, key=lambda r: r['timestamp'])
            filtered_modules[module_name] = [most_recent]
            
            # Log which files were ignored for transparency
            ignored_files = [r['file'] for r in module_results if r != most_recent]
            if ignored_files:
                console.print(f"[dim]Note: Ignoring older {module_name} results: {', '.join(ignored_files)}[/dim]")
    
    return filtered_modules

def get_status_style(passed, failed, errors):
    """Get Rich style for test status."""
    if errors > 0:
        return ("🔴 ERROR", "red bold")
    elif failed > 0:
        return ("🟡 FAILING", "yellow bold")
    elif passed > 0:
        return ("🟢 PASSING", "green bold")
    else:
        return ("⚫ NO TESTS", "dim")

def print_summary(modules):
    """Print a summary of test results using Rich formatting."""
    # Create main summary table
    summary_table = Table(
        title="eCPU Verification Status Summary",
        box=box.ROUNDED,
        show_header=True,
        header_style="bold cyan"
    )
    
    summary_table.add_column("Module", style="cyan", no_wrap=True, width=20)
    summary_table.add_column("Status", justify="center", width=12)
    summary_table.add_column("Tests", justify="right", style="blue", width=6)
    summary_table.add_column("Passed", justify="right", style="green", width=6)
    summary_table.add_column("Failed", justify="right", style="red", width=6)
    summary_table.add_column("Errors", justify="right", style="red bold", width=6)
    summary_table.add_column("Last Run", style="dim", width=12)
    
    total_modules = len(modules)
    total_tests = 0
    total_passed = 0
    total_failed = 0
    total_errors = 0
    
    for module_name, results in sorted(modules.items()):
        if not results:
            continue
            
        # Aggregate results for this module
        module_tests = sum(r['total_tests'] for r in results)
        module_passed = sum(r['passed'] for r in results)
        module_failed = sum(r['failed'] for r in results)
        module_errors = sum(r['errors'] for r in results)
        
        total_tests += module_tests
        total_passed += module_passed
        total_failed += module_failed
        total_errors += module_errors
        
        # Get the most recent timestamp
        latest_timestamp = max(r['timestamp'] for r in results)
        
        # Determine module status
        status_text, status_style = get_status_style(module_passed, module_failed, module_errors)
        
        summary_table.add_row(
            module_name.upper(),
            Text(status_text, style=status_style),
            str(module_tests),
            str(module_passed),
            str(module_failed) if module_failed > 0 else "",
            str(module_errors) if module_errors > 0 else "",
            latest_timestamp.strftime("%m/%d %H:%M")
        )
    
    console.print(summary_table)
    
    # Create overall summary panel
    if total_tests > 0:
        pass_rate = (total_passed / total_tests) * 100
        
        if total_errors > 0:
            overall_status = Text("🔴 CRITICAL ISSUES", style="red bold")
        elif total_failed > 0:
            overall_status = Text("🟡 NEEDS ATTENTION", style="yellow bold")
        else:
            overall_status = Text("🟢 ALL TESTS PASSING", style="green bold")
    else:
        overall_status = Text("⚫ NO TEST RESULTS", style="dim")
        pass_rate = 0
    
    # Create summary statistics
    stats_table = Table(box=None, show_header=False, padding=(0, 2))
    stats_table.add_column("Metric", style="cyan")
    stats_table.add_column("Value", style="bold")
    
    stats_table.add_row("Modules tested:", str(total_modules))
    stats_table.add_row("Total tests:", str(total_tests))
    stats_table.add_row("Passed:", f"[green]{total_passed}[/green]")
    stats_table.add_row("Failed:", f"[red]{total_failed}[/red]" if total_failed > 0 else "0")
    stats_table.add_row("Errors:", f"[red bold]{total_errors}[/red bold]" if total_errors > 0 else "0")
    stats_table.add_row("Pass rate:", f"{pass_rate:.1f}%")
    stats_table.add_row("Status:", overall_status)
    
    summary_panel = Panel(
        stats_table,
        title="Overall Summary",
        border_style="blue",
        box=box.ROUNDED
    )
    
    console.print()
    console.print(summary_panel)

def print_failing_tests(modules):
    """Print a focused view of failing tests."""
    failing_modules = []
    
    for module_name, results in sorted(modules.items()):
        module_failed = sum(r['failed'] for r in results)
        module_errors = sum(r['errors'] for r in results)
        
        if module_failed > 0 or module_errors > 0:
            failing_modules.append((module_name, results))
    
    if not failing_modules:
        console.print("\n🎉 [green bold]No failing tests found![/green bold]")
        return
    
    console.print(f"\n[red bold]Found {len(failing_modules)} modules with failures:[/red bold]")
    
    for module_name, results in failing_modules:
        # Create a tree for this module
        tree = Tree(f"[red bold]{module_name.upper()}[/red bold]")
        
        for result in results:
            for test in result['tests']:
                if test['status'] in ['failed', 'error']:
                    status_icon = "❌" if test['status'] == 'failed' else "🔴"
                    test_node = tree.add(f"{status_icon} {test['name']} [dim]({test['time']:.3f}s)[/dim]")
                    
                    if 'message' in test and test['message']:
                        # Show first few lines of error message
                        lines = test['message'].split('\n')[:3]
                        for line in lines:
                            if line.strip():
                                test_node.add(f"[red]{line.strip()[:100]}[/red]")
        
        console.print(tree)

def print_detailed_results(modules, show_passed=False):
    """Print detailed test results using Rich formatting."""
    console.print("\n")
    console.rule("[bold blue]Detailed Test Results[/bold blue]")
    
    for module_name, results in sorted(modules.items()):
        if not results:
            continue
        
        # Create table for this module
        module_table = Table(
            title=f"{module_name.upper()} Module",
            box=box.SIMPLE,
            show_header=True,
            header_style="bold magenta"
        )
        
        module_table.add_column("Test Name", style="cyan", no_wrap=True)
        module_table.add_column("Status", justify="center", width=10)
        module_table.add_column("Time", justify="right", style="blue", width=8)
        module_table.add_column("Details", style="dim", width=50)
        
        for result in results:
            for test in result['tests']:
                if test['status'] != 'passed' or show_passed:
                    status_styles = {
                        'passed': ('✅ PASS', 'green'),
                        'failed': ('❌ FAIL', 'red'),
                        'error': ('🔴 ERROR', 'red bold'),
                        'skipped': ('⏭️ SKIP', 'yellow')
                    }
                    
                    status_text, status_style = status_styles.get(test['status'], ('❓ UNKNOWN', 'dim'))
                    
                    details = ""
                    if 'message' in test and test['message']:
                        # Show first line of error message
                        lines = test['message'].split('\n')
                        if lines:
                            details = lines[0][:50] + "..." if len(lines[0]) > 50 else lines[0]
                    
                    module_table.add_row(
                        test['name'],
                        Text(status_text, style=status_style),
                        f"{test['time']:.3f}s",
                        details
                    )
        
        if module_table.row_count > 0:
            console.print(module_table)
            console.print()

def main():
    parser = argparse.ArgumentParser(
        description='Check eCPU test results from XML files',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s                          # Show summary
  %(prog)s --detailed               # Show detailed results
  %(prog)s --show-passed --detailed # Show all tests including passed
  %(prog)s --failures-only          # Show only failing tests
        """
    )
    parser.add_argument('--sim-build', default='sim_build', 
                       help='Path to sim_build directory (default: sim_build)')
    parser.add_argument('--detailed', action='store_true',
                       help='Show detailed test results')
    parser.add_argument('--show-passed', action='store_true',
                       help='Show passed tests in detailed view')
    parser.add_argument('--failures-only', action='store_true',
                       help='Show only failing tests')
    
    args = parser.parse_args()
    
    # Show startup message
    console.print(Panel.fit(
        "[bold blue]eCPU Test Results Checker[/bold blue]\n"
        "Analyzing verification results...",
        border_style="blue"
    ))
    
    # Check if sim_build directory exists
    if not os.path.exists(args.sim_build):
        console.print(f"[red]Error: sim_build directory not found: {args.sim_build}[/red]")
        return 1
    
    # Find and parse XML files with progress indication
    with Status("[bold green]Searching for XML result files...") as status:
        xml_files = find_xml_files(args.sim_build)
        
        if not xml_files:
            console.print(f"[yellow]No XML result files found in {args.sim_build}[/yellow]")
            return 1
        
        status.update(f"[bold green]Found {len(xml_files)} XML files, parsing...")
        
        # Parse all XML files
        results = []
        for xml_file in xml_files:
            result = parse_xml_result(xml_file)
            if result:
                results.append(result)
    
    if not results:
        console.print("[red]No valid test results found[/red]")
        return 1
    
    # Group by module
    modules = group_results_by_module(results)
    
    # Print appropriate output based on arguments
    if args.failures_only:
        print_failing_tests(modules)
    else:
        # Print summary
        print_summary(modules)
        
        # Print detailed results if requested
        if args.detailed:
            print_detailed_results(modules, args.show_passed)
    
    return 0

if __name__ == "__main__":
    exit(main()) 