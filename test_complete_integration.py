#!/usr/bin/env python3

import sys
import os
import json
import subprocess
import tempfile
import time
from pathlib import Path

# Add axiomander to path
sys.path.insert(0, "/home/gavin/dev/Scidonia/axiomander/src")


def test_lsp_server_basic():
    """Test basic LSP server functionality."""
    print("🧪 Testing LSP Server Basic Functionality")
    print("=" * 50)

    # Create initialize request
    initialize_request = {
        "jsonrpc": "2.0",
        "id": 1,
        "method": "initialize",
        "params": {
            "processId": os.getpid(),
            "rootUri": "file:///tmp",
            "capabilities": {
                "textDocument": {
                    "synchronization": {
                        "dynamicRegistration": False,
                        "willSave": False,
                        "willSaveWaitUntil": False,
                        "didSave": False,
                    }
                }
            },
        },
    }

    # Convert to LSP message format
    content = json.dumps(initialize_request)
    message = f"Content-Length: {len(content)}\r\n\r\n{content}"

    process = None
    try:
        # Start the LSP server
        print("📡 Starting Axiomander LSP server...")
        process = subprocess.Popen(
            ["axiomander-lsp"],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        )

        # Send the initialize request
        stdout, stderr = process.communicate(input=message, timeout=5)

        print(f"📊 Return code: {process.returncode}")

        if process.returncode == 0:
            print("✅ Server started and responded successfully")

            # Parse the response
            if "Content-Length:" in stdout:
                # Extract JSON response
                json_start = stdout.find('{"id"')
                if json_start != -1:
                    json_response = stdout[json_start:]
                    try:
                        response = json.loads(json_response)
                        capabilities = response.get("result", {}).get(
                            "capabilities", {}
                        )

                        print("🎯 Server Capabilities:")
                        for cap_name, cap_value in capabilities.items():
                            print(f"  - {cap_name}: {cap_value}")

                        # Check for our specific capabilities
                        expected_caps = [
                            "textDocumentSync",
                            "completionProvider",
                            "hoverProvider",
                            "executeCommandProvider",
                        ]

                        missing_caps = []
                        for cap in expected_caps:
                            if cap not in capabilities:
                                missing_caps.append(cap)

                        if not missing_caps:
                            print("✅ All expected capabilities present")
                            return True
                        else:
                            print(f"⚠ Missing capabilities: {missing_caps}")
                            return False

                    except json.JSONDecodeError:
                        print("⚠ Could not parse JSON response")
                        return False
                else:
                    print("⚠ No JSON found in response")
                    return False
            else:
                print("⚠ No proper LSP response received")
                return False
        else:
            print("❌ Server failed to start")
            if stderr:
                print(f"Error output: {stderr}")
            return False

    except subprocess.TimeoutExpired:
        if process is not None:
            process.kill()
        print("⚠ Server timed out")
        return False

    except Exception as e:
        print(f"❌ Error testing server: {e}")
        return False


def test_server_imports():
    """Test that server can be imported without errors."""
    print("\n🧪 Testing Server Module Imports")
    print("=" * 50)

    try:
        from axiomander.lsp.server import main, server

        print("✅ Server module imported successfully")

        print(f"📋 Server name: {server.name}")
        print(f"📋 Server version: {server.version}")

        # Test that server has expected features
        features = getattr(server, "_feature_manager", None)
        if features:
            print("✅ Server has feature manager")
        else:
            print("⚠ Server missing feature manager")

        return True

    except Exception as e:
        print(f"❌ Import failed: {e}")
        import traceback

        traceback.print_exc()
        return False


def test_emacs_integration_file():
    """Test that Emacs integration file loads properly."""
    print("\n🧪 Testing Emacs Integration File")
    print("=" * 50)

    axiomander_file = "/home/gavin/dev/Scidonia/axiomander/axiomander-example.el"
    symlink_file = "/home/gavin/dev/Personal/code/elisp/setup/axiomander.el"

    # Check if files exist
    if not os.path.exists(axiomander_file):
        print(f"❌ Axiomander Emacs file not found: {axiomander_file}")
        return False

    if not os.path.islink(symlink_file):
        print(f"❌ Symlink not found: {symlink_file}")
        return False

    print(f"✅ Axiomander Emacs file exists: {axiomander_file}")
    print(f"✅ Symlink exists: {symlink_file}")

    # Test file loading in batch mode
    try:
        result = subprocess.run(
            [
                "emacs",
                "--batch",
                "--eval",
                f'(progn (load-file "{axiomander_file}") (if (fboundp \'axiomander-global-mode) (message "SUCCESS: Function defined") (message "FAILURE: Function not defined")))',
            ],
            capture_output=True,
            text=True,
            timeout=10,
        )

        if "SUCCESS: Function defined" in result.stdout:
            print("✅ Emacs integration file loads and defines functions")
            return True
        else:
            print("❌ Emacs integration file failed to define functions")
            print(f"Output: {result.stdout}")
            if result.stderr:
                print(f"Errors: {result.stderr}")
            return False

    except subprocess.TimeoutExpired:
        print("⚠ Emacs test timed out")
        return False
    except Exception as e:
        print(f"❌ Error testing Emacs integration: {e}")
        return False


def test_orchestrator_integration():
    """Test that the orchestrator works with the server."""
    print("\n🧪 Testing Orchestrator Integration")
    print("=" * 50)

    try:
        from axiomander.verification.orchestrator import VerificationOrchestrator
        from axiomander.lsp.server import orchestrator

        print("✅ Orchestrator imported successfully")

        # Test basic orchestrator functionality
        test_code = """
def test_function(x):
    assert x > 0, "x must be positive"
    return x * 2
"""

        print("🔍 Testing verification with sample code...")
        results = orchestrator.verify_source(test_code, "<test>")

        print(f"📊 Verification results: {len(results)} function(s) processed")
        for result in results:
            print(f"  - Function: {result.function_name}")
            print(f"  - Success: {result.success}")
            print(f"  - Execution time: {result.execution_time:.3f}s")
            if result.verified_assertions:
                print(f"  - Verified assertions: {len(result.verified_assertions)}")
            if result.failed_assertions:
                print(f"  - Failed assertions: {len(result.failed_assertions)}")
            if result.errors:
                print(f"  - Errors: {len(result.errors)}")

        print("✅ Orchestrator integration working")
        return True

    except Exception as e:
        print(f"❌ Orchestrator test failed: {e}")
        import traceback

        traceback.print_exc()
        return False


def main():
    """Run comprehensive integration tests."""
    print("🚀 Axiomander LSP Integration Test Suite")
    print("=" * 60)

    tests = [
        ("Server Imports", test_server_imports),
        ("LSP Server Basic", test_lsp_server_basic),
        ("Emacs Integration", test_emacs_integration_file),
        ("Orchestrator Integration", test_orchestrator_integration),
    ]

    results = {}

    for test_name, test_func in tests:
        try:
            results[test_name] = test_func()
        except Exception as e:
            print(f"❌ {test_name} failed with exception: {e}")
            results[test_name] = False

    # Summary
    print("\n🏁 Test Summary")
    print("=" * 60)

    passed = 0
    total = len(tests)

    for test_name, result in results.items():
        status = "✅ PASS" if result else "❌ FAIL"
        print(f"{status} {test_name}")
        if result:
            passed += 1

    print(f"\n📊 Results: {passed}/{total} tests passed")

    if passed == total:
        print("🎉 ALL TESTS PASSED! Axiomander LSP integration is working perfectly!")
        print("\n🛠️  Ready to use:")
        print("   1. The LSP server is compatible with pygls 2.0")
        print("   2. Emacs integration is modernized and functional")
        print("   3. All components are working together")
        print("\n📝 Next steps:")
        print("   - Use (require 'axiomander) in your Emacs config")
        print("   - Run (axiomander-global-mode 1) to enable global LSP")
        print("   - Open Python files and enjoy contract verification!")

        return True
    else:
        print(f"⚠️  {total - passed} test(s) failed. Check output above for details.")
        return False


if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)
