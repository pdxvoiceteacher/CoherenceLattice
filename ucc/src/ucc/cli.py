from __future__ import annotations

from pathlib import Path
import typer

from .core import load_yaml, load_schema, validate_module, run_module

app = typer.Typer(help="UCC CLI: schema-validated modules + safe step runner + audit bundles.")


@app.command()
def validate(
    module: Path = typer.Argument(..., help="Path to a UCC module YAML"),
    schema: Path = typer.Option(Path("ucc/schema/ucc_module.schema.json"), help="Path to module JSON schema"),
) -> None:
    module_doc = load_yaml(module)
    schema_doc = load_schema(schema)
    validate_module(module_doc, schema_doc)
    typer.echo(f"OK: {module}")


@app.command()
def run(
    module: Path = typer.Argument(..., help="Path to a UCC module YAML"),
    input: Path = typer.Option(..., "--input", help="Path to input JSON"),
    outdir: Path = typer.Option(Path("ucc/out/run"), help="Output directory for report + audit bundle"),
    schema: Path = typer.Option(Path("ucc/schema/ucc_module.schema.json"), help="Path to module JSON schema"),
) -> None:
    metrics, flags = run_module(module, input, outdir, schema)
    typer.echo(f"Metrics: {metrics}")
    typer.echo(f"Flags: {flags}")
    typer.echo(f"Wrote audit bundle to: {outdir / 'audit_bundle.json'}")


if __name__ == "__main__":
    app()