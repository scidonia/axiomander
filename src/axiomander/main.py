import typer
from .cli.storage import storage_app

app = typer.Typer(help="Axiomander - Design-by-Contract Agent System")
app.add_typer(storage_app, name="storage")


def main():
    app()


if __name__ == "__main__":
    main()
