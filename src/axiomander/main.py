import typer
from pathlib import Path
from typing import List, Optional
from rich.console import Console
from rich.table import Table

from .storage.manager import ComponentStorageManager
from .storage.models import Component, ComponentType, AxiomanderConfig

# Import compiler modules - these will be created
try:
    from .compiler.models import CompilerConfig, CompilerMode
    from .compiler.compiler import ComponentCompiler
    COMPILER_AVAILABLE = True
except ImportError:
    COMPILER_AVAILABLE = False

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




def main():
    app()


if __name__ == "__main__":
    main()
