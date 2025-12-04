import typer
from pathlib import Path
from typing import List, Optional
from rich.console import Console
from rich.table import Table

from .storage.manager import ComponentStorageManager
from .storage.models import Component, ComponentType, AxiomanderConfig
from .compiler.models import CompilerConfig, CompilerMode
from .compiler.compiler import ComponentCompiler

console = Console()
error_console = Console(stderr=True)

app = typer.Typer(help="Axiomander - Design-by-Contract Agent System")


@app.command("init")
def init_storage(
    project_root: Path = typer.Option(
        Path.cwd(),
        "--project-root",
        "-p",
        help="Root directory of the project"
    )
) -> None:
    """Initialize .axiomander storage in a project."""
    try:
        manager = ComponentStorageManager(project_root)
        config = AxiomanderConfig(project_root=str(project_root))
        manager.initialize_project(config)
        console.print(f"[green]Initialized Axiomander storage in {project_root}[/green]")
    except Exception as e:
        error_console.print(f"[red]Error initializing storage: {e}[/red]")
        raise typer.Exit(1)


@app.command("validate")
def validate_storage(
    project_root: Path = typer.Option(
        Path.cwd(),
        "--project-root", 
        "-p",
        help="Root directory of the project"
    )
) -> None:
    """Validate the consistency of component storage."""
    try:
        manager = ComponentStorageManager(project_root)
        errors = manager.validate_storage()
        
        if not errors:
            console.print("[green]Storage validation passed - no errors found[/green]")
        else:
            error_console.print("[red]Storage validation failed with errors:[/red]")
            for error in errors:
                error_console.print(f"  • {error}")
            raise typer.Exit(1)
            
    except Exception as e:
        error_console.print(f"[red]Error validating storage: {e}[/red]")
        raise typer.Exit(1)


@app.command("list")
def list_components(
    project_root: Path = typer.Option(
        Path.cwd(),
        "--project-root",
        "-p", 
        help="Root directory of the project"
    )
) -> None:
    """List all components in the project."""
    try:
        manager = ComponentStorageManager(project_root)
        component_uids = manager.list_components()
        
        if not component_uids:
            console.print("No components found")
            return
        
        table = Table(title="Components")
        table.add_column("UID", style="cyan")
        table.add_column("Name", style="green")
        table.add_column("Type", style="yellow")
        table.add_column("Path", style="magenta")
        table.add_column("Language", style="blue")
        
        for uid in component_uids:
            component = manager.load_component(uid)
            if component:
                table.add_row(
                    uid[:8] + "...",  # Truncate UID for display
                    component.name,
                    component.component_type.value,
                    component.path or "",
                    component.language.value
                )
        
        console.print(table)
        
    except Exception as e:
        error_console.print(f"[red]Error listing components: {e}[/red]")
        raise typer.Exit(1)


@app.command("create")
def create_component(
    name: str = typer.Argument(..., help="Name of the component"),
    component_type: ComponentType = typer.Option(
        ComponentType.FUNCTION,
        "--type",
        "-t",
        help="Type of component"
    ),
    description: str = typer.Option(
        None,
        "--description",
        "-d", 
        help="Description of the component"
    ),
    path: str = typer.Option(
        None,
        "--path",
        help="Optional path designation for organizing component in subdirectories"
    ),
    project_root: Path = typer.Option(
        Path.cwd(),
        "--project-root",
        "-p",
        help="Root directory of the project"
    )
) -> None:
    """Create a new component."""
    try:
        manager = ComponentStorageManager(project_root)
        
        component = Component(
            name=name,
            component_type=component_type,
            description=description,
            path=path
        )
        
        manager.create_component(component)
        console.print(f"[green]Created component '{name}' with UID {component.uid}[/green]")
        
    except Exception as e:
        error_console.print(f"[red]Error creating component: {e}[/red]")
        raise typer.Exit(1)


@app.command("compile")
def compile_components(
    component_uids: List[str] = typer.Argument(..., help="Component UIDs to compile"),
    module_name: str = typer.Option(..., "--module-name", "-m", help="Name of the target module"),
    entry_point: Optional[str] = typer.Option(None, "--entry-point", "-e", help="Entry point component UID"),
    mode: CompilerMode = typer.Option(CompilerMode.DEVELOPMENT, "--mode", help="Compilation mode"),
    target_dir: Path = typer.Option(Path("src"), "--target-dir", "-t", help="Target directory for generated code"),
    no_tests: bool = typer.Option(False, "--no-tests", help="Exclude test files from compilation"),
    no_contracts: bool = typer.Option(False, "--no-contracts", help="Exclude contract validation from output"),
    optimize: bool = typer.Option(False, "--optimize", help="Enable import optimization"),
    type_stubs: bool = typer.Option(False, "--type-stubs", help="Generate type stub files"),
    project_root: Path = typer.Option(
        Path.cwd(),
        "--project-root",
        "-p",
        help="Root directory of the project"
    )
) -> None:
    """Compile components into a Python module."""
    try:
        storage_manager = ComponentStorageManager(project_root)
        
        config = CompilerConfig(
            mode=mode,
            target_directory=target_dir,
            include_contracts=not no_contracts,
            include_tests=not no_tests,
            optimize_imports=optimize,
            generate_type_stubs=type_stubs
        )
        
        compiler = ComponentCompiler(storage_manager, config)
        result = compiler.compile_components(component_uids, module_name, entry_point)
        
        if result.success:
            console.print(f"[green]✓[/green] Successfully compiled {len(result.compiled_components)} components")
            console.print(f"[blue]Module:[/blue] {result.module_name}")
            console.print(f"[blue]Generated files:[/blue] {len(result.generated_files)}")
            
            if result.warnings:
                console.print("\n[yellow]Warnings:[/yellow]")
                for warning in result.warnings:
                    console.print(f"  [yellow]•[/yellow] {warning}")
        else:
            error_console.print("[red]✗[/red] Compilation failed")
            for error in result.errors:
                error_console.print(f"  [red]•[/red] {error}")
            raise typer.Exit(1)
            
    except Exception as e:
        error_console.print(f"[red]Error during compilation: {e}[/red]")
        raise typer.Exit(1)


@app.command("compile-all")
def compile_all_components(
    output_dir: Path = typer.Option(Path("dist"), "--output-dir", "-o", help="Output directory for compiled modules"),
    mode: CompilerMode = typer.Option(CompilerMode.DEVELOPMENT, "--mode", help="Compilation mode"),
    project_root: Path = typer.Option(
        Path.cwd(),
        "--project-root",
        "-p",
        help="Root directory of the project"
    )
) -> None:
    """Compile all components in the project."""
    try:
        storage_manager = ComponentStorageManager(project_root)
        component_uids = storage_manager.list_components()
        
        if not component_uids:
            console.print("[yellow]No components found to compile[/yellow]")
            return
        
        config = CompilerConfig(
            mode=mode,
            target_directory=output_dir
        )
        
        compiler = ComponentCompiler(storage_manager, config)
        
        # For now, compile all components into a single module
        # In the future, this could be smarter about grouping
        result = compiler.compile_components(component_uids, "axiomander_compiled")
        
        if result.success:
            console.print(f"[green]✓[/green] Successfully compiled all {len(result.compiled_components)} components")
            console.print(f"[blue]Output directory:[/blue] {output_dir}")
        else:
            error_console.print("[red]✗[/red] Compilation failed")
            for error in result.errors:
                error_console.print(f"  [red]•[/red] {error}")
            raise typer.Exit(1)
            
    except Exception as e:
        error_console.print(f"[red]Error during compilation: {e}[/red]")
        raise typer.Exit(1)


@app.command("resync")
def resync_components(
    module_name: Optional[str] = typer.Option(None, "--module-name", "-m", help="Module name to resync from"),
    component_uids: Optional[List[str]] = typer.Option(None, "--components", "-c", help="Specific component UIDs to resync"),
    validate: bool = typer.Option(True, "--validate/--no-validate", help="Validate changes before applying"),
    resolve_conflicts: bool = typer.Option(False, "--resolve-conflicts", help="Automatically resolve simple conflicts"),
    dry_run: bool = typer.Option(False, "--dry-run", help="Show what would be resynced without making changes"),
    force: bool = typer.Option(False, "--force", help="Force resync even if validation fails"),
    backup: bool = typer.Option(True, "--backup/--no-backup", help="Create backup before resync"),
    project_root: Path = typer.Option(
        Path.cwd(),
        "--project-root",
        "-p",
        help="Root directory of the project"
    )
) -> None:
    """Resync changes from compiled files back to component storage."""
    # This is a placeholder for the resync functionality
    # The actual implementation would be quite complex
    console.print("[yellow]Resync functionality not yet implemented[/yellow]")
    console.print("This feature will allow syncing changes from compiled Python files back to component storage")


def main():
    app()


if __name__ == "__main__":
    main()
