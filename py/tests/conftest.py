import shutil
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent.parent))

# ---------------------------------------------------------------------------
# Shared skip condition: tests that invoke the Coq toolchain (coqc / coq-lsp)
# are marked slow and skipped when the toolchain is absent.
# ---------------------------------------------------------------------------

_COQC_AVAILABLE = shutil.which("coqc") is not None

requires_coqc = pytest.mark.skipif(
    not _COQC_AVAILABLE,
    reason="Coq toolchain (coqc) not on PATH -- run `eval $(opam env)` first",
)
