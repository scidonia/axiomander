
# Component Development Guide  
_(For AI Agents and Automated Tooling)_

This guide defines how AI agents should read, write, organize, check, and compile Axiomander components. It standardizes the workflow so that linting, typing, testing, and compilation all work cleanly without complex virtual file systems.

---

## 1. Source of Truth: The Component Library

All editable component code lives in:

```
.axiomander/
  components/
    {component_uid}/
      component.json
      logical.py
      implementation.py
      test.py
```

These are real Python files and should be treated as the primary source of truth.

### AI Responsibilities
- Edit only within `components/{uid}/`
- Never edit compiled output directly
- Maintain invariants described in `component.json`

---

## 2. File-System–Like Hierarchy for Development

Each component is stored in a UUID directory but can be treated conceptually as a library module.  
If a nicer import surface is needed for humans or tools, generate a view package:

```
.axiomander/view/
```

Each file in that view re-exports the component’s functions.

---

## 3. Compilation Produces a Shippable Module

Running the compiler generates:

```
src/<module_name>/
tests/
```

The output is what end-users import.

### Compiler Responsibilities
- Resolve dependency references
- Generate valid Python imports
- Apply name-uniquification
- Build test suite

### AI Responsibilities
- Never modify `src/` or `tests/`
- Fix issues in component source only

---

## 4. Development Workflow (For AI Agents)

### Step 1 — Edit Components
Modify `logical.py`, `implementation.py`, `component.json`, or `test.py` inside `.axiomander/components`.

### Step 2 — Compile
```
axiomander compile <entry_uid> --module-name <pkgname>
```

### Step 3 — Run Static Tools
```
mypy src/<pkgname>
ruff check src/<pkgname> tests
pytest tests
```

### Step 4 — Fix Errors
Only change component source files, then recompile.

---

## 5. Tooling Integration

### Editors
Add `.axiomander/components` to the workspace.

### Mypy Example
```toml
[mypy]
mypy_path = .axiomander/components
```

### Linters / Formatters
```
ruff check .axiomander/components
black .axiomander/components
```

---

## 6. Import Resolution Model

Component source files may include symbolic or placeholder imports.  
The compiler rewrites all imports into valid Python during compilation.

**AI Rule:** never attempt to compute final import paths manually.

---

## 7. What Not To Do

AI agents must never:

- Edit files under `src/<module_name>/`
- Edit compiled tests
- Manipulate final import paths
- Treat component storage as virtual

---

## 8. Summary

| Stage | Location | Editable? | Purpose |
|-------|----------|-----------|---------|
| Component Source | `.axiomander/components/{uid}/` | Yes | Logical + implementation code |
| View Package | `.axiomander/view/` | No | Optional ergonomic layer |
| Compiled Output | `src/<module_name>/` | No | Final package |
| Compiled Tests | `tests/` | No | Executable test suite |

---

## Final Guidelines

✔ Treat `.axiomander/components` as the source of truth  
✔ Compile to generate shippable modules  
✔ Run static tools on compiled output  
✔ Fix issues only in components  
✔ Let the compiler resolve structure and imports  
