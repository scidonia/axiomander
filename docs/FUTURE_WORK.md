# Future Work: Verified LLM Pipelines

## 1. Structured LLM Output with Retry and Monadic Error Handling

A Python function that calls an LLM, parses structured JSON into a Pydantic model,
with up to 3 retries, stream-based JSON boundary detection, and a monadic
`Result[Model, None]` return type.

### Python Source (to be verified)

```python
from pydantic import BaseModel
from typing import Optional, TypeVar, Callable
from py.contracts import requires, ensures

T = TypeVar("T", bound=BaseModel)

# ─── Monadic result type ──────────────────────────────────────────

class Result(BaseModel):
    ok: bool
    value: Optional[T] = None

# ─── Stream-search JSON object ────────────────────────────────────

@requires(lambda text: len(text) > 0)
@ensures(lambda text, result: result == -1 or text[result] == "{")
def find_json_start(text: str) -> int:
    """Find the first '{' in text. Returns -1 if not found."""
    for i, ch in enumerate(text):
        if ch == "{":
            return i
    return -1

@requires(lambda text, start: start >= 0 and text[start] == "{")
@ensures(lambda text, start, result: result > start)
def find_json_end(text: str, start: int) -> int:
    """Find the matching '}' for the JSON object starting at `start`.
    Handles nested braces, strings, and escapes."""
    depth = 0
    in_string = False
    escape = False
    i = start
    while i < len(text):
        ch = text[i]
        if escape:
            escape = False
        elif ch == "\\":
            escape = True
        elif ch == '"':
            in_string = not in_string
        elif not in_string:
            if ch == "{":
                depth += 1
            elif ch == "}":
                depth -= 1
                if depth == 0:
                    return i
        i += 1
    return -1

# ─── LLM call with retry ──────────────────────────────────────────

@requires(lambda model_cls: issubclass(model_cls, BaseModel))
@ensures(lambda model_cls, prompt, result:
    result.ok == True or result.ok == False)  # always returns a Result
def llm_structured_call(
    model_cls: type[T],
    prompt: str,
    max_retries: int = 3
) -> Result:
    """
    Call the LLM up to `max_retries` times, parse the streamed response
    as JSON, and validate into `model_cls`. Returns Result.ok=True with
    the model on success, or Result.ok=False on failure.

    Black holes: the LLM API call (CHavoc on response_text).
    Recovery: re-parse after each black hole.
    """
    for attempt in range(max_retries):
        # ── Black hole: LLM API call ──────────────────────────────
        response_text = call_llm_api(prompt)  # HAVOC on response_text

        # ── Recovery: parse JSON ──────────────────────────────────
        start = find_json_start(response_text)
        if start == -1:
            continue

        end = find_json_end(response_text, start)
        if end == -1:
            continue

        json_str = response_text[start:end + 1]

        # ── Black hole: JSON parsing ──────────────────────────────
        try:
            data = json.loads(json_str)      # HAVOC on data
            model = model_cls(**data)         # pydantic validation
            return Result(ok=True, value=model)
        except (json.JSONDecodeError, ValidationError):
            continue

    return Result(ok=False, value=None)
```

### Properties to Verify

| Property | Type | Affected by black hole? |
|---|---|---|
| `find_json_start` returns index of `{` or `-1` | Completeness | No (pure function) |
| `find_json_end` returns matching `}` or `-1` | Completeness | No (pure function) |
| Braces are balanced in `find_json_end` when result ≠ -1 | Safety | No (pure function) |
| `llm_structured_call` always returns a `Result` | Soundness | No (Result constructor is pure) |
| On success, `result.value` is a valid instance of `model_cls` | Soundness | Pydantic validation guarantees |
| On failure after 3 retries, `result.value` is `None` | Completeness | Loop invariant |
| The LLM call does not corrupt `model_cls` or `prompt` | Preservation | Yes — but they're arguments (read-only) |

### Black Hole Analysis

```
Black hole:         call_llm_api(prompt)
Affected set:       {response_text}
Unaffected set:     {prompt, model_cls, max_retries, attempt, ...}
Q_keep:             prompt is unchanged, model_cls is unchanged
Q_drop:             response_text has expected structure

Recovery assertion: find_json_start(response_text) >= 0
                    ∧ find_json_end(response_text, ...) >= 0
                    ∧ json.loads(response_text[start:end+1]) is valid model_cls
```

---

## 2. LaTeX Citation Cross-Checker with AI

A pipeline that reads a `.tex` file, extracts `\cite{...}` references, parses
the bibliography (`\bibitem{...}` entries), and cross-checks each citation
against an LLM for semantic support.

### Pipeline Stages

```
┌─────────────────────────────────────────────────────────────────┐
│  Stage 1: Parse LaTeX                                           │
│    extract_citations(tex) → list[CitationRef]                    │
│    extract_bibliography(tex) → list[BibEntry]                    │
│    (pure functions)                                             │
├─────────────────────────────────────────────────────────────────┤
│  Stage 2: Cross-reference                                       │
│    match citations to bib entries by key                        │
│    (pure function)                                              │
├─────────────────────────────────────────────────────────────────┤
│  Stage 3: AI citation verification                              │
│    For each (citation, bib_entry, paper_context):                │
│      Black hole: call LLM API                                   │
│      Recovery: parse structured response                        │
│    Produces: list[CitationVerdict]                              │
├─────────────────────────────────────────────────────────────────┤
│  Stage 4: Report generation                                     │
│    Compile results into a structured report                     │
│    (pure function)                                              │
└─────────────────────────────────────────────────────────────────┘
```

### Pydantic Models

```python
from pydantic import BaseModel
from typing import Optional

class CitationRef(BaseModel):
    key: str
    line: int
    context: str           # surrounding sentence for AI

class BibEntry(BaseModel):
    key: str
    author: str
    title: str
    year: int

class CitationVerdict(BaseModel):
    citation_key: str
    bib_key: str
    status: str            # "supported" | "unsupported" | "error"
    confidence: float      # 0.0 – 1.0
    explanation: str       # LLM reasoning

class CheckReport(BaseModel):
    total_citations: int
    matched: int
    dangling: int           # cited but not in bibliography
    uncited: int            # in bibliography but never cited
    verdicts: list[CitationVerdict]
```

### Python Source

```python
from py.contracts import requires, ensures

@requires(lambda tex: len(tex) > 0)
@ensures(lambda tex, result: all(isinstance(c, CitationRef) for c in result))
def extract_citations(tex: str) -> list[CitationRef]:
    """Extract \\cite{...} references from LaTeX source."""
    ...

@requires(lambda tex: len(tex) > 0)
@ensures(lambda tex, result: all(isinstance(b, BibEntry) for b in result))
def extract_bibliography(tex: str) -> list[BibEntry]:
    """Extract \\bibitem{...} entries from LaTeX source."""
    ...

@requires(
    lambda citations, bib: len(citations) > 0 and len(bib) > 0
)
@ensures(
    lambda citations, bib, result:
        len(result.verdicts) == len(citations)
        and result.total_citations == len(citations)
        and result.dangling == len([v for v in result.verdicts if v.status == "dangling"])
)
def cross_check(
    citations: list[CitationRef],
    bib: list[BibEntry],
    paper_text: str
) -> CheckReport:
    """
    For each citation, find its bib entry, construct a prompt with the
    surrounding context and bib details, and ask the LLM to evaluate
    whether the paper's use of the citation is semantically supported.
    """
    verdicts: list[CitationVerdict] = []

    for ref in citations:
        entry = find_bib_entry(ref.key, bib)
        if entry is None:
            verdicts.append(CitationVerdict(
                citation_key=ref.key,
                bib_key="",
                status="dangling",
                confidence=0.0,
                explanation="No matching bibliography entry",
            ))
            continue

        prompt = build_verification_prompt(ref, entry, paper_text)

        # ── Black hole: LLM call ─────────────────────────────────
        result = llm_structured_call(CitationVerdict, prompt, max_retries=3)

        if result.ok and result.value is not None:
            verdicts.append(result.value)
        else:
            verdicts.append(CitationVerdict(
                citation_key=ref.key,
                bib_key=entry.key,
                status="error",
                confidence=0.0,
                explanation="LLM failed to produce valid output",
            ))

    matched = sum(1 for v in verdicts if v.status == "supported")
    dangling = sum(1 for v in verdicts if v.status == "dangling")
    uncited = 0  # computed separately

    return CheckReport(
        total_citations=len(citations),
        matched=matched,
        dangling=dangling,
        uncited=uncited,
        verdicts=verdicts,
    )
```

### Properties to Verify

| Property | WP challenge |
|---|---|
| Extraction functions match all `\cite`/`\bibitem` patterns | Pure: regex/parser WP |
| `cross_check` always returns `len(verdicts) == len(citations)` | Loop invariant + Result.ok guarantee |
| Dangling count is correct | Pure arithmetic on verdicts |
| Each verdict has a valid status string | Enum invariant |
| LLM failure → verdict.status == "error" | By construction (else branch) |
| LLM success → verdict.value is valid `CitationVerdict` | Pydantic validation in `llm_structured_call` |

### Black Hole Surface Analysis

```
Function:                   Affected sets:
extract_citations           (none – pure)
extract_bibliography        (none – pure)
find_bib_entry              (none – pure dict lookup)
build_verification_prompt   (none – pure string template)
llm_structured_call         A = {result}        ← main black hole
cross_check                 propagates upward   ← summary report constructor is pure
```

---

## Implementation Sequence

1. Write Pydantic models for `CitationRef`, `BibEntry`, `CitationVerdict`, `CheckReport`
2. Implement `find_json_start` and `find_json_end` in pure Python + Coq proofs
3. Implement `llm_structured_call` with monadic Result pattern
4. Verify the loop invariant: after 0..3 iterations, either we have a valid model or we don't
5. Verify that on success, `result.value` passes Pydantic validation
6. Implement LaTeX extraction functions + prove completeness of regex patterns
7. Implement `cross_check` + prove the contract: `len(verdicts) == len(citations)`
8. End-to-end: run on real papers, collect verdicts, display in web UI
