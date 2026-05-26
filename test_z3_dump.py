#!/usr/bin/env python3
"""
Test script for Z3 dump functionality
"""

import sys
from pathlib import Path

# Add src to path
sys.path.insert(0, "src")

from axiomander.verification.orchestrator import VerificationOrchestrator


def test_z3_dump():
    """Test the Z3 constraint dumping functionality."""
    print("Testing Z3 Dump Functionality")
    print("=" * 30)

    # Create orchestrator
    orchestrator = VerificationOrchestrator()

    # Verify a file with contracts
    print(f"Verifying: examples/simple_contracts.py")
    results = orchestrator.verify_file("examples/simple_contracts.py")

    if not results:
        print("No functions found or verification failed")
        return

    # Print results
    for result in results:
        print(f"\n--- Function: {result.function_name} ---")
        print(f"Verified assertions: {len(result.verified_assertions)}")
        print(f"Failed assertions: {len(result.failed_assertions)}")
        print(f"Errors: {len(result.errors)}")
        print(f"Execution time: {result.execution_time:.3f}s")

    # Test dumping constraints to file
    dump_file = "z3_constraints_dump.smt2"
    print(f"\nDumping Z3 constraints to: {dump_file}")
    orchestrator.dump_z3_constraints(dump_file)

    # Read and display first few lines
    try:
        with open(dump_file, "r") as f:
            lines = f.readlines()[:20]  # First 20 lines
        print(f"\nFirst 20 lines of {dump_file}:")
        print("".join(lines))

        print(
            f"\n✓ Successfully dumped {len(open(dump_file).readlines())} lines to {dump_file}"
        )
    except Exception as e:
        print(f"Error reading dump file: {e}")

    # Test dumping as string
    print(f"\nDumping Z3 constraints as string:")
    dump_str = orchestrator.dump_z3_constraints()
    if dump_str:
        lines = dump_str.split("\n")[:10]  # First 10 lines
        print("First 10 lines:")
        for line in lines:
            print(line)
        print(f"\n✓ String dump successful ({len(dump_str)} characters)")
    else:
        print("String dump failed or empty")


if __name__ == "__main__":
    test_z3_dump()
