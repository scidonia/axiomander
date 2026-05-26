"""
Command-line client for axiomander agent backend.

This module provides the main CLI entry point and imports all commands
from the client package structure.
"""

from .client import main

# Re-export main for backwards compatibility
__all__ = ['main']


def _get_api_key_for_provider(provider: str) -> str:
    """Get the appropriate API key for the provider."""
    import os
    
    if provider == "anthropic":
        api_key = os.getenv("ANTHROPIC_API_KEY")
        if not api_key:
            console.print("[red]Error: ANTHROPIC_API_KEY environment variable not set[/red]")
            console.print("[yellow]Set your Anthropic API key with: export ANTHROPIC_API_KEY=your_api_key_here[/yellow]")
            raise typer.Exit(1)
        return api_key
    elif provider == "openai":
        api_key = os.getenv("OPENAI_API_KEY")
        if not api_key:
            console.print("[red]Error: OPENAI_API_KEY environment variable not set[/red]")
            console.print("[yellow]Set your OpenAI API key with: export OPENAI_API_KEY=your_api_key_here[/yellow]")
            raise typer.Exit(1)
        return api_key
    else:
        console.print(f"[red]Error: Unsupported provider '{provider}'[/red]")
        raise typer.Exit(1)


def _validate_api_key_for_provider(provider: str):
    """Validate that the appropriate API key is set for the provider."""
    _get_api_key_for_provider(provider)  # This will raise an error if key is missing


def get_server_config() -> tuple[str, str]:
    """Get server URL and API key from environment."""
    import os
    server_url = os.getenv("AXIOMANDER_SERVER_URL", DEFAULT_SERVER_URL)
    
    # Try to get API key from provider-specific environment variables
    # The client will send the appropriate key based on the provider
    api_key = os.getenv("ANTHROPIC_API_KEY") or os.getenv("OPENAI_API_KEY")
    
    if not api_key:
        console.print("[red]Error: No API key found[/red]")
        console.print("[yellow]Set your API key with one of:[/yellow]")
        console.print("  export ANTHROPIC_API_KEY=your_anthropic_key")
        console.print("  export OPENAI_API_KEY=your_openai_key")
        raise typer.Exit(1)
    
    return server_url, api_key


def make_request(method: str, endpoint: str, data: Optional[Dict] = None) -> Dict[str, Any]:
    """Make an HTTP request to the axiomander backend."""
    server_url, _ = get_server_config()
    
    # Get the appropriate API key based on the provider in the request data
    provider = data.get("provider", "anthropic") if data else "anthropic"
    api_key = _get_api_key_for_provider(provider)
    
    headers = {
        "Authorization": f"Bearer {api_key}",
        "Content-Type": "application/json"
    }
    
    url = f"{server_url}{endpoint}"
    
    try:
        with httpx.Client(timeout=30.0) as client:
            if method.upper() == "GET":
                response = client.get(url, headers=headers)
            elif method.upper() == "POST":
                response = client.post(url, headers=headers, json=data)
            else:
                raise ValueError(f"Unsupported HTTP method: {method}")
            
            response.raise_for_status()
            return response.json()
            
    except httpx.ConnectError:
        console.print(f"[red]Error: Could not connect to axiomander server at {server_url}[/red]")
        console.print(f"[yellow]Make sure the server is running with: axiomander-server backend[/yellow]")
        raise typer.Exit(1)
    except httpx.HTTPStatusError as e:
        console.print(f"[red]HTTP Error {e.response.status_code}: {e.response.text}[/red]")
        raise typer.Exit(1)
    except Exception as e:
        console.print(f"[red]Error: {e}[/red]")
        raise typer.Exit(1)


async def stream_sse_request(endpoint: str, params: Dict[str, str] = None) -> Dict[str, Any]:
    """Make an SSE request and handle streaming events with file operations."""
    server_url, _ = get_server_config()
    
    # Get the appropriate API key based on the provider
    provider = params.get("provider", "anthropic") if params else "anthropic"
    api_key = _get_api_key_for_provider(provider)
    
    headers = {
        "Authorization": f"Bearer {api_key}",
        "Accept": "text/event-stream",
        "Cache-Control": "no-cache"
    }
    
    url = f"{server_url}{endpoint}"
    if params:
        query_string = "&".join(f"{k}={v}" for k, v in params.items())
        url = f"{url}?{query_string}"
    
    ai_response_buffer = ""
    final_result = {}
    ai_panel_started = False
    
    try:
        with Progress(
            SpinnerColumn(),
            TextColumn("[progress.description]{task.description}"),
            console=console,
        ) as progress:
            task = progress.add_task("Connecting...", total=None)
            
            # Create a Live display for the AI response panel
            ai_panel = Panel("", title="🤖 AI Response", border_style="green")
            
            with Live(ai_panel, console=console, refresh_per_second=10) as live:
                async with httpx.AsyncClient(timeout=300.0) as client:
                    async with aconnect_sse(client, "GET", url, headers=headers) as event_source:
                        async for sse in event_source.aiter_sse():
                            try:
                                event = json.loads(sse.data)
                                event_type = event.get("type")
                                
                                if event_type == "progress":
                                    step = event.get("step", "Processing")
                                    progress_pct = event.get("progress", 0)
                                    message = event.get("message", "")
                                    progress.update(task, description=f"{step} ({progress_pct}%) - {message}")
                                
                                elif event_type == "ai_response":
                                    content = event.get("content", "")
                                    complete = event.get("complete", False)
                                    
                                    if content:
                                        ai_response_buffer += content
                                        # Update the live panel with streaming content
                                        if not ai_panel_started:
                                            ai_panel_started = True
                                            progress.update(task, description="🤖 AI responding...")
                                        
                                        # Update the panel content in real-time
                                        updated_panel = Panel(
                                            ai_response_buffer,
                                            title="🤖 AI Response",
                                            border_style="green"
                                        )
                                        live.update(updated_panel)
                                    
                                    if complete:
                                        # Final update to the panel
                                        final_panel = Panel(
                                            ai_response_buffer,
                                            title="🤖 AI Response",
                                            border_style="green"
                                        )
                                        live.update(final_panel)
                                
                                elif event_type == "file_operation":
                                    await execute_file_operation(event)
                                
                                elif event_type == "git_operation":
                                    await execute_git_operation(event)
                                
                                elif event_type == "error":
                                    error_msg = event.get("message", "Unknown error")
                                    console.print(f"[red]Error: {error_msg}[/red]")
                                    raise Exception(error_msg)
                                
                                elif event_type == "complete":
                                    success = event.get("success", False)
                                    if success:
                                        progress.update(task, description="✓ Completed successfully")
                                        final_result = event
                                    else:
                                        error = event.get("error", "Unknown error")
                                        progress.update(task, description="✗ Failed")
                                        raise Exception(error)
                                    break
                                    
                            except json.JSONDecodeError:
                                # Skip invalid JSON events
                                continue
                            except Exception as e:
                                console.print(f"[red]Error processing event: {e}[/red]")
                                raise
    
    except httpx.ConnectError:
        console.print(f"[red]Error: Could not connect to axiomander server at {server_url}[/red]")
        console.print(f"[yellow]Make sure the server is running with: axiomander-server backend[/yellow]")
        raise typer.Exit(1)
    except Exception as e:
        console.print(f"[red]Streaming error: {e}[/red]")
        raise typer.Exit(1)
    
    return final_result


async def execute_file_operation(operation: Dict[str, Any]):
    """Execute file operations locally."""
    op_type = operation.get("operation")
    path = operation.get("path")
    content = operation.get("content", "")
    encoding = operation.get("encoding", "utf-8")
    
    try:
        path_obj = Path(path)
        
        if op_type == "create_directory":
            path_obj.mkdir(parents=True, exist_ok=True)
            console.print(f"[dim]Created directory: {path}[/dim]")
        
        elif op_type == "create_file":
            path_obj.parent.mkdir(parents=True, exist_ok=True)
            path_obj.write_text(content, encoding=encoding)
            console.print(f"[dim]Created file: {path}[/dim]")
        
        elif op_type == "update_file":
            path_obj.write_text(content, encoding=encoding)
            console.print(f"[dim]Updated file: {path}[/dim]")
        
        elif op_type == "update_index":
            # Special handling for index updates
            if path_obj.exists():
                existing_data = json.loads(path_obj.read_text())
                new_data = json.loads(content)
                existing_data.update(new_data)
                path_obj.write_text(json.dumps(existing_data, indent=2), encoding=encoding)
            else:
                path_obj.parent.mkdir(parents=True, exist_ok=True)
                path_obj.write_text(content, encoding=encoding)
            console.print(f"[dim]Updated index: {path}[/dim]")
        
        elif op_type == "delete_file":
            if path_obj.exists():
                path_obj.unlink()
                console.print(f"[dim]Deleted file: {path}[/dim]")
        
    except Exception as e:
        console.print(f"[red]File operation failed: {e}[/red]")
        raise


async def execute_git_operation(operation: Dict[str, Any]):
    """Execute git operations locally."""
    op_type = operation.get("operation")
    message = operation.get("message", "")
    files = operation.get("files", [])
    
    try:
        if op_type == "commit":
            # Add files to git
            if files:
                for file_pattern in files:
                    result = subprocess.run(
                        ["git", "add", file_pattern],
                        capture_output=True,
                        text=True,
                        cwd="."
                    )
                    if result.returncode != 0:
                        console.print(f"[yellow]Warning: git add failed for {file_pattern}: {result.stderr}[/yellow]")
            
            # Commit changes
            result = subprocess.run(
                ["git", "commit", "-m", message],
                capture_output=True,
                text=True,
                cwd="."
            )
            
            if result.returncode == 0:
                console.print(f"[dim]Committed: {message}[/dim]")
            else:
                # Check if it's just "nothing to commit"
                if "nothing to commit" in result.stdout:
                    console.print(f"[dim]No changes to commit[/dim]")
                else:
                    console.print(f"[yellow]Git commit warning: {result.stderr}[/yellow]")
        
        elif op_type == "branch":
            branch_name = operation.get("branch_name", "")
            result = subprocess.run(
                ["git", "checkout", "-b", branch_name],
                capture_output=True,
                text=True,
                cwd="."
            )
            
            if result.returncode == 0:
                console.print(f"[dim]Created branch: {branch_name}[/dim]")
            else:
                console.print(f"[yellow]Branch creation warning: {result.stderr}[/yellow]")
    
    except Exception as e:
        console.print(f"[red]Git operation failed: {e}[/red]")
        # Don't raise - git operations are not critical


def wait_for_task(task_id: str, show_progress: bool = True) -> Dict[str, Any]:
    """Wait for a background task to complete and return the result."""
    if show_progress:
        with Progress(
            SpinnerColumn(),
            TextColumn("[progress.description]{task.description}"),
            console=console,
        ) as progress:
            task = progress.add_task("Processing...", total=None)
            
            while True:
                result = make_request("GET", f"/task/{task_id}")
                
                if result["status"] == "completed":
                    progress.update(task, description="✓ Completed")
                    return result
                elif result["status"] == "failed":
                    progress.update(task, description="✗ Failed")
                    console.print(f"[red]Task failed: {result.get('error', 'Unknown error')}[/red]")
                    raise typer.Exit(1)
                else:
                    current_step = result.get("current_step", "Processing")
                    progress_pct = result.get("progress", 0)
                    progress.update(task, description=f"{current_step} ({progress_pct}%)")
                
                time.sleep(1)
    else:
        while True:
            result = make_request("GET", f"/task/{task_id}")
            if result["status"] in ["completed", "failed"]:
                return result
            time.sleep(1)


@app.command()
def analyze(
    project: str = typer.Option(".", "--project", "-p", help="Project root directory"),
    mode: str = typer.Option("specification", "--mode", "-m", help="Analysis mode"),
    focus_areas: Optional[List[str]] = typer.Option(None, "--focus", help="Specific areas to focus on"),
    model: str = typer.Option("sonnet", "--model", help="LLM model to use (supports aliases like 'sonnet', 'opus', 'haiku')"),
    provider: str = typer.Option("anthropic", "--provider", help="LLM provider (anthropic, openai)"),
    wait: bool = typer.Option(True, "--wait/--no-wait", help="Wait for analysis to complete"),
):
    """Analyze a project and get AI-powered recommendations."""
    # Validate API key for the selected provider
    _validate_api_key_for_provider(provider)
    
    console.print(f"[blue]Analyzing project:[/blue] {Path(project).resolve()}")
    
    data = {
        "project_root": str(Path(project).resolve()),
        "mode": mode,
        "focus_areas": focus_areas or [],
        "model": model,
        "provider": provider
    }
    
    result = make_request("POST", "/analyze-project", data)
    
    if not result.get("success"):
        console.print(f"[red]Analysis failed: {result}[/red]")
        raise typer.Exit(1)
    
    # Show immediate results
    console.print(f"[green]✓ Analysis started[/green] (Task ID: {result['task_id']})")
    
    # Display statistics
    stats = result.get("statistics", {})
    if stats:
        _display_statistics(stats)
    
    # Display recommendations
    recommendations = result.get("recommendations", [])
    if recommendations:
        console.print(Panel(
            "\n".join(f"• {rec}" for rec in recommendations),
            title="🎯 Recommendations",
            border_style="green"
        ))
    
    # Wait for detailed analysis if requested
    if wait and result.get("task_id"):
        console.print("\n[cyan]Waiting for detailed analysis...[/cyan]")
        final_result = wait_for_task(result["task_id"])
        
        if final_result.get("result"):
            detailed = final_result["result"]
            console.print(Panel(
                "\n".join(f"• {rec}" for rec in detailed.get("recommendations", [])),
                title="📋 Detailed Analysis",
                border_style="blue"
            ))


@app.command()
def generate(
    aim: str = typer.Argument(..., help="High-level aim or requirement"),
    project: str = typer.Option(".", "--project", "-p", help="Project root directory"),
    target_files: Optional[List[str]] = typer.Option(None, "--target", help="Specific files to target"),
    mode: str = typer.Option("specification", "--mode", "-m", help="Generation mode"),
    model: str = typer.Option("sonnet", "--model", help="LLM model to use (supports aliases like 'sonnet', 'opus', 'haiku')"),
    provider: str = typer.Option("anthropic", "--provider", help="LLM provider (anthropic, openai)"),
    wait: bool = typer.Option(True, "--wait/--no-wait", help="Wait for generation to complete"),
):
    """Generate contracts based on an aim or requirement."""
    # Validate API key for the selected provider
    _validate_api_key_for_provider(provider)
    
    console.print(f"[blue]Generating contracts for:[/blue] {aim}")
    
    data = {
        "project_root": str(Path(project).resolve()),
        "aim": aim,
        "target_files": target_files or [],
        "mode": mode,
        "model": model,
        "provider": provider
    }
    
    result = make_request("POST", "/generate-contracts", data)
    
    if not result.get("success"):
        console.print(f"[red]Generation failed: {result}[/red]")
        raise typer.Exit(1)
    
    console.print(f"[green]✓ Generation started[/green] (Task ID: {result['task_id']})")
    
    # Display immediate results
    contracts = result.get("generated_contracts", [])
    if contracts:
        console.print(Panel(
            _format_contracts(contracts),
            title="📝 Generated Contracts",
            border_style="green"
        ))
    
    rationale = result.get("rationale")
    if rationale:
        console.print(Panel(rationale, title="💭 Rationale", border_style="blue"))
    
    # Wait for detailed generation if requested
    if wait and result.get("task_id"):
        console.print("\n[cyan]Waiting for detailed generation...[/cyan]")
        final_result = wait_for_task(result["task_id"])
        
        if final_result.get("result"):
            detailed = final_result["result"]
            detailed_contracts = detailed.get("generated_contracts", [])
            if detailed_contracts:
                console.print(Panel(
                    _format_contracts(detailed_contracts),
                    title="📋 Detailed Contracts",
                    border_style="blue"
                ))


@app.command()
def decompose(
    aim: str = typer.Argument(..., help="High-level aim to decompose"),
    project: str = typer.Option(".", "--project", "-p", help="Project root directory"),
    model: str = typer.Option("sonnet", "--model", help="LLM model to use (supports aliases like 'sonnet', 'opus', 'haiku')"),
    provider: str = typer.Option("anthropic", "--provider", help="LLM provider (anthropic, openai)"),
    wait: bool = typer.Option(True, "--wait/--no-wait", help="Wait for decomposition to complete"),
):
    """Decompose a high-level aim into subcontracts and implementation plan."""
    # Validate API key for the selected provider
    _validate_api_key_for_provider(provider)
    
    console.print(f"[blue]Decomposing aim:[/blue] {aim}")
    
    data = {
        "project_root": str(Path(project).resolve()),
        "aim": aim,
        "model": model,
        "provider": provider
    }
    
    result = make_request("POST", "/decompose-aim", data)
    
    if not result.get("success"):
        console.print(f"[red]Decomposition failed: {result}[/red]")
        raise typer.Exit(1)
    
    console.print(f"[green]✓ Decomposition started[/green] (Task ID: {result['task_id']})")
    
    # Display immediate results
    subcontracts = result.get("subcontracts", [])
    if subcontracts:
        console.print(Panel(
            _format_subcontracts(subcontracts),
            title="🔧 Subcontracts",
            border_style="green"
        ))
    
    architecture = result.get("architecture_suggestions", [])
    if architecture:
        console.print(Panel(
            "\n".join(f"• {suggestion}" for suggestion in architecture),
            title="🏗️ Architecture Suggestions",
            border_style="blue"
        ))
    
    plan = result.get("implementation_plan", [])
    if plan:
        console.print(Panel(
            "\n".join(f"{i+1}. {step}" for i, step in enumerate(plan)),
            title="📋 Implementation Plan",
            border_style="cyan"
        ))
    
    # Wait for detailed decomposition if requested
    if wait and result.get("task_id"):
        console.print("\n[cyan]Waiting for detailed decomposition...[/cyan]")
        final_result = wait_for_task(result["task_id"])
        
        if final_result.get("result", {}).get("decomposition"):
            detailed = final_result["result"]["decomposition"]
            console.print(Panel(
                json.dumps(detailed, indent=2),
                title="📊 Detailed Decomposition",
                border_style="blue"
            ))


@app.command()
def refactor(
    project: str = typer.Option(".", "--project", "-p", help="Project root directory"),
    target_files: Optional[List[str]] = typer.Option(None, "--target", help="Specific files to analyze"),
    goals: Optional[List[str]] = typer.Option(None, "--goals", help="Refactoring goals"),
    model: str = typer.Option("sonnet", "--model", help="LLM model to use (supports aliases like 'sonnet', 'opus', 'haiku')"),
    provider: str = typer.Option("anthropic", "--provider", help="LLM provider (anthropic, openai)"),
    wait: bool = typer.Option(True, "--wait/--no-wait", help="Wait for analysis to complete"),
):
    """Analyze code for refactoring opportunities with contract preservation."""
    # Validate API key for the selected provider
    _validate_api_key_for_provider(provider)
    
    console.print(f"[blue]Analyzing refactoring opportunities in:[/blue] {Path(project).resolve()}")
    
    data = {
        "project_root": str(Path(project).resolve()),
        "target_files": target_files or [],
        "goals": goals or [],
        "model": model,
        "provider": provider
    }
    
    result = make_request("POST", "/refactor", data)
    
    if not result.get("success"):
        console.print(f"[red]Refactor analysis failed: {result}[/red]")
        raise typer.Exit(1)
    
    console.print(f"[green]✓ Refactor analysis started[/green] (Task ID: {result['task_id']})")
    
    # Display immediate results
    suggestions = result.get("refactoring_suggestions", [])
    if suggestions:
        console.print(Panel(
            _format_refactor_suggestions(suggestions),
            title="🔧 Refactoring Suggestions",
            border_style="green"
        ))
    
    impact = result.get("impact_analysis", {})
    if impact:
        console.print(Panel(
            _format_impact_analysis(impact),
            title="📊 Impact Analysis",
            border_style="blue"
        ))
    
    risks = result.get("risk_assessment", [])
    if risks:
        console.print(Panel(
            "\n".join(f"• {risk}" for risk in risks),
            title="⚠️ Risk Assessment",
            border_style="yellow"
        ))
    
    # Wait for detailed analysis if requested
    if wait and result.get("task_id"):
        console.print("\n[cyan]Waiting for detailed refactor analysis...[/cyan]")
        final_result = wait_for_task(result["task_id"])
        
        if final_result.get("result"):
            detailed = final_result["result"]
            console.print(Panel(
                json.dumps(detailed, indent=2),
                title="📋 Detailed Refactor Plan",
                border_style="blue"
            ))


@app.command()
def status(
    task_id: str = typer.Argument(..., help="Task ID to check"),
):
    """Check the status of a background task."""
    result = make_request("GET", f"/task/{task_id}")
    
    status_color = {
        "pending": "yellow",
        "running": "blue", 
        "completed": "green",
        "failed": "red"
    }.get(result["status"], "white")
    
    console.print(f"[{status_color}]Status:[/{status_color}] {result['status']}")
    console.print(f"[cyan]Progress:[/cyan] {result.get('progress', 0)}%")
    
    if result.get("current_step"):
        console.print(f"[cyan]Current Step:[/cyan] {result['current_step']}")
    
    if result.get("result"):
        console.print(Panel(
            json.dumps(result["result"], indent=2),
            title="📋 Result",
            border_style="green"
        ))
    
    if result.get("error"):
        console.print(Panel(
            result["error"],
            title="❌ Error",
            border_style="red"
        ))


@app.command()
def create_spec(
    name: str = typer.Argument(..., help="Name for the specification"),
    description: str = typer.Argument(..., help="Initial description of the behavior"),
    project: str = typer.Option(".", "--project", "-p", help="Project root directory"),
    model: str = typer.Option("sonnet", "--model", help="LLM model to use (supports aliases like 'sonnet', 'opus', 'haiku')"),
    provider: str = typer.Option("anthropic", "--provider", help="LLM provider (anthropic, openai)"),
):
    """Create a new behavioral specification with real-time AI interaction."""
    # Validate API key for the selected provider
    _validate_api_key_for_provider(provider)
    
    console.print(f"[blue]Creating specification:[/blue] {name}")
    console.print(f"[cyan]Description:[/cyan] {description}")
    console.print()
    
    params = {
        "project_root": str(Path(project).resolve()),
        "specification_name": name,
        "initial_description": description,
        "model": model,
        "provider": provider
    }
    
    # Use asyncio to run the streaming request
    import asyncio
    result = asyncio.run(stream_sse_request("/stream/create-specification", params))
    
    if result.get("success"):
        spec_id = result.get("specification_id")
        console.print(f"\n[green]✓ Specification created successfully![/green]")
        console.print(f"[cyan]Specification ID:[/cyan] {spec_id}")
        
        next_steps = result.get("next_steps", [])
        if next_steps:
            console.print(Panel(
                "\n".join(f"{i+1}. {step}" for i, step in enumerate(next_steps)),
                title="📋 Next Steps",
                border_style="green"
            ))
        
        console.print(f"\n[cyan]Use 'axiomander refine-spec {spec_id} \"your response\"' to continue[/cyan]")
    else:
        console.print(f"[red]Specification creation failed[/red]")
        raise typer.Exit(1)


@app.command()
def refine_spec(
    specification_id: str = typer.Argument(..., help="Specification ID to refine"),
    response: str = typer.Argument(..., help="Your response to AI questions or additional details"),
    model: str = typer.Option("sonnet", "--model", help="LLM model to use (supports aliases like 'sonnet', 'opus', 'haiku')"),
    provider: str = typer.Option("anthropic", "--provider", help="LLM provider (anthropic, openai)"),
):
    """Refine an existing specification with real-time AI interaction."""
    # Validate API key for the selected provider
    _validate_api_key_for_provider(provider)
    
    console.print(f"[blue]Refining specification:[/blue] {specification_id}")
    console.print(f"[cyan]Your input:[/cyan] {response}")
    console.print()
    
    params = {
        "specification_id": specification_id,
        "user_response": response,
        "model": model,
        "provider": provider
    }
    
    # Use asyncio to run the streaming request
    import asyncio
    result = asyncio.run(stream_sse_request("/stream/refine-specification", params))
    
    if result.get("success"):
        console.print(f"\n[green]✓ Specification refined successfully![/green]")
        
        ready = result.get("ready_for_contracts", False)
        if ready:
            console.print(Panel(
                "🎉 Specification is ready for contract generation!",
                title="Ready for Contracts",
                border_style="bright_green"
            ))
            console.print(f"[cyan]Use 'axiomander generate-contracts {specification_id}' to proceed[/cyan]")
        
        next_steps = result.get("next_steps", [])
        if next_steps:
            console.print(Panel(
                "\n".join(f"{i+1}. {step}" for i, step in enumerate(next_steps)),
                title="📋 Next Steps",
                border_style="blue"
            ))
    else:
        console.print(f"[red]Specification refinement failed[/red]")
        raise typer.Exit(1)


@app.command()
def generate_contracts(
    specification_id: str = typer.Argument(..., help="Specification ID to generate contracts from"),
    model: str = typer.Option("sonnet", "--model", help="LLM model to use (supports aliases like 'sonnet', 'opus', 'haiku')"),
    provider: str = typer.Option("anthropic", "--provider", help="LLM provider (anthropic, openai)"),
):
    """Generate contract descriptions from a specification with real-time AI analysis."""
    # Validate API key for the selected provider
    _validate_api_key_for_provider(provider)
    
    console.print(f"[blue]Generating contracts for specification:[/blue] {specification_id}")
    console.print()
    
    params = {
        "specification_id": specification_id,
        "model": model,
        "provider": provider
    }
    
    # Use asyncio to run the streaming request
    import asyncio
    result = asyncio.run(stream_sse_request("/stream/generate-contracts", params))
    
    if result.get("success"):
        console.print(f"\n[green]✓ Contract descriptions generated successfully![/green]")
        
        contracts_file = result.get("contracts_file")
        if contracts_file:
            console.print(f"[cyan]Contracts saved to:[/cyan] {contracts_file}")
        
        ready = result.get("ready_for_implementation", False)
        if ready:
            console.print(Panel(
                "🎉 Ready for implementation!",
                title="Next Phase",
                border_style="bright_green"
            ))
        
        next_steps = result.get("next_steps", [])
        if next_steps:
            console.print(Panel(
                "\n".join(f"{i+1}. {step}" for i, step in enumerate(next_steps)),
                title="📋 Next Steps",
                border_style="green"
            ))
    else:
        console.print(f"[red]Contract generation failed[/red]")
        raise typer.Exit(1)


@app.command()
def show_contracts(
    specification_id: str = typer.Argument(..., help="Specification ID to show contracts for"),
):
    """Show detailed contract descriptions for a specification."""
    result = make_request("GET", f"/specification/{specification_id}")
    
    contracts = result.get("contracts", {})
    if not contracts:
        console.print(f"[yellow]No contracts found for specification {specification_id}[/yellow]")
        console.print(f"[cyan]Use 'axiomander generate-contracts {specification_id}' to generate contracts[/cyan]")
        return
    
    console.print(f"[blue]Contracts for:[/blue] {result.get('name', 'Unknown')}")
    console.print(f"[cyan]Generated:[/cyan] {contracts.get('generated_at', 'Unknown')}")
    console.print()
    
    # Show AI analysis
    ai_analysis = contracts.get("ai_analysis", "")
    if ai_analysis:
        console.print(Panel(
            ai_analysis,
            title="🤖 AI Contract Analysis",
            border_style="cyan"
        ))
    
    # Show contract descriptions
    contract_descriptions = contracts.get("contract_descriptions", [])
    if contract_descriptions:
        console.print(Panel(
            _format_contract_descriptions(contract_descriptions),
            title="📋 Contract Descriptions",
            border_style="yellow"
        ))
    else:
        console.print("[yellow]No detailed contract descriptions found[/yellow]")


@app.command()
def list_specs(
    project: Optional[str] = typer.Option(None, "--project", "-p", help="Filter by project root directory"),
):
    """List all specifications."""
    params = {}
    if project:
        params["project_root"] = str(Path(project).resolve())
    
    # Build query string manually since httpx.get doesn't handle params well with our make_request
    query_string = "&".join(f"{k}={v}" for k, v in params.items()) if params else ""
    endpoint = f"/specifications?{query_string}" if query_string else "/specifications"
    
    result = make_request("GET", endpoint)
    
    specifications = result.get("specifications", {})
    
    if not specifications:
        console.print("[yellow]No specifications found[/yellow]")
        return
    
    # Create table
    table = Table(title="📝 Specifications")
    table.add_column("ID", style="cyan")
    table.add_column("Name", style="green")
    table.add_column("Project", style="blue")
    table.add_column("Ready for Contracts", style="yellow")
    table.add_column("Created", style="dim")
    
    for spec_id, spec in specifications.items():
        ready = "✓" if spec.get("ready_for_contracts", False) else "✗"
        created = spec.get("created_at", "").split("T")[0]  # Just the date
        table.add_row(
            spec_id,
            spec.get("name", "Unknown"),
            spec.get("project_root", "Unknown"),
            ready,
            created
        )
    
    console.print(table)


@app.command()
def show_spec(
    specification_id: str = typer.Argument(..., help="Specification ID to show"),
    verbose: bool = typer.Option(False, "--verbose", "-v", help="Show detailed contract information"),
):
    """Show details of a specification."""
    result = make_request("GET", f"/specification/{specification_id}")
    
    console.print(f"[blue]Specification:[/blue] {result.get('name', 'Unknown')}")
    console.print(f"[cyan]ID:[/cyan] {specification_id}")
    console.print(f"[cyan]Project:[/cyan] {result.get('project_root', 'Unknown')}")
    console.print(f"[cyan]Ready for Contracts:[/cyan] {'✓' if result.get('ready_for_contracts', False) else '✗'}")
    console.print(f"[cyan]Created:[/cyan] {result.get('created_at', 'Unknown')}")
    
    if result.get('contracts_generated'):
        console.print(f"[cyan]Contracts Generated:[/cyan] ✓ at {result.get('contracts_generated_at', 'Unknown')}")
    
    # Show specification description/content
    spec_text = result.get("specification_text", "")
    if spec_text:
        console.print(Panel(
            spec_text,
            title="📝 Specification Description",
            border_style="green"
        ))
    
    # Show conversation history (condensed by default, full if verbose)
    history = result.get("conversation_history", [])
    if history:
        if verbose:
            console.print(Panel(
                _format_conversation_history(history),
                title="💬 Full Conversation History",
                border_style="blue"
            ))
        else:
            # Show just the summary
            console.print(Panel(
                _format_conversation_summary(history),
                title="💬 Conversation Summary",
                border_style="blue"
            ))
    
    # Show contract descriptions if available
    contracts = result.get("contracts", {})
    if contracts:
        contract_descriptions = contracts.get("contract_descriptions", [])
        ai_analysis = contracts.get("ai_analysis", "")
        
        if ai_analysis:
            console.print(Panel(
                ai_analysis,
                title="🤖 AI Contract Analysis",
                border_style="cyan"
            ))
        
        if contract_descriptions:
            console.print(Panel(
                _format_contract_descriptions(contract_descriptions),
                title="📋 Contract Descriptions",
                border_style="yellow"
            ))
    
    if not verbose and (history or contracts):
        console.print(f"[dim]Use --verbose to see full conversation history and detailed contract information[/dim]")


@app.command()
def analyze_decomposition(
    specification_id: str = typer.Argument(..., help="Specification ID to analyze for decomposition"),
    model: str = typer.Option("sonnet", "--model", help="LLM model to use"),
    provider: str = typer.Option("anthropic", "--provider", help="LLM provider"),
):
    """Analyze specification and suggest decomposition opportunities."""
    _validate_api_key_for_provider(provider)
    
    console.print(f"[blue]Analyzing decomposition opportunities for:[/blue] {specification_id}")
    
    params = {
        "specification_id": specification_id,
        "model": model,
        "provider": provider
    }
    
    import asyncio
    result = asyncio.run(stream_sse_request("/stream/analyze-decomposition", params))
    
    if result.get("success"):
        console.print(f"[green]✓ Analysis completed[/green]")
        
        opportunities = result.get("decomposition_opportunities", [])
        if opportunities:
            console.print(Panel(
                "\n".join(f"• {opp}" for opp in opportunities),
                title="🔍 Decomposition Opportunities",
                border_style="green"
            ))
        
        suggested_components = result.get("suggested_components", [])
        if suggested_components:
            console.print(Panel(
                "\n".join(f"• {comp}" for comp in suggested_components),
                title="🧩 Suggested Components",
                border_style="blue"
            ))
    else:
        console.print("[red]Analysis failed[/red]")
        raise typer.Exit(1)


@app.command()
def decompose_interactive(
    specification_id: str = typer.Argument(..., help="Specification ID to decompose interactively"),
    model: str = typer.Option("sonnet", "--model", help="LLM model to use"),
    provider: str = typer.Option("anthropic", "--provider", help="LLM provider"),
):
    """Interactively decompose specification with component preview and approval."""
    _validate_api_key_for_provider(provider)
    
    console.print(f"[blue]Starting interactive decomposition for:[/blue] {specification_id}")
    console.print("[dim]AI will analyze the specification and suggest components for your approval[/dim]")
    console.print()
    
    params = {
        "specification_id": specification_id,
        "model": model,
        "provider": provider
    }
    
    import asyncio
    result = asyncio.run(stream_sse_request("/stream/decompose-interactive", params))
    
    if result.get("success"):
        console.print(f"[green]✓ Component analysis completed[/green]")
        
        component_suggestions = result.get("component_suggestions", [])
        if component_suggestions:
            console.print(Panel(
                f"Found {len(component_suggestions)} component suggestions",
                title="🔍 Analysis Complete",
                border_style="green"
            ))
            
            # Start interactive approval process
            approved_components = []
            
            for i, suggestion in enumerate(component_suggestions, 1):
                console.print(f"\n[bold blue]Component {i} of {len(component_suggestions)}[/bold blue]")
                
                # Show component preview
                _show_component_preview(suggestion)
                
                # Get user decision
                decision = _get_component_decision(suggestion)
                
                if decision == "approved":
                    approved_components.append(suggestion)
                    console.print(f"[green]✓ Approved: {suggestion['name']}[/green]")
                elif decision == "edited":
                    # Component was edited and approved
                    approved_components.append(suggestion)
                    console.print(f"[green]✓ Approved (edited): {suggestion['name']}[/green]")
                else:
                    console.print(f"[yellow]✗ Skipped: {suggestion['name']}[/yellow]")
            
            # Create approved components
            if approved_components:
                console.print(f"\n[cyan]Creating {len(approved_components)} approved components...[/cyan]")
                _create_approved_components(specification_id, approved_components, model, provider)
            else:
                console.print("[yellow]No components were approved for creation[/yellow]")
        else:
            console.print("[yellow]No component suggestions were generated[/yellow]")
    else:
        console.print("[red]Interactive decomposition failed[/red]")
        raise typer.Exit(1)


@app.command()
def decompose_spec(
    specification_id: str = typer.Argument(..., help="Specification ID to decompose"),
    component_names: str = typer.Argument(..., help="Comma-separated component names"),
    model: str = typer.Option("sonnet", "--model", help="LLM model to use"),
    provider: str = typer.Option("anthropic", "--provider", help="LLM provider"),
):
    """Decompose specification into named components (batch mode)."""
    _validate_api_key_for_provider(provider)
    
    console.print(f"[blue]Decomposing specification:[/blue] {specification_id}")
    console.print(f"[cyan]Components:[/cyan] {component_names}")
    
    params = {
        "specification_id": specification_id,
        "component_names": component_names,
        "model": model,
        "provider": provider
    }
    
    import asyncio
    result = asyncio.run(stream_sse_request("/stream/decompose-specification", params))
    
    if result.get("success"):
        console.print(f"[green]✓ Specification decomposed successfully[/green]")
        
        components = result.get("created_components", [])
        if components:
            console.print(Panel(
                "\n".join(f"• {comp['name']} ({comp['id']})" for comp in components),
                title="🧩 Created Components",
                border_style="green"
            ))
        
        next_steps = result.get("next_steps", [])
        if next_steps:
            console.print(Panel(
                "\n".join(f"{i+1}. {step}" for i, step in enumerate(next_steps)),
                title="📋 Next Steps",
                border_style="blue"
            ))
    else:
        console.print("[red]Decomposition failed[/red]")
        raise typer.Exit(1)


@app.command()
def create_component(
    parent_spec_id: str = typer.Argument(..., help="Parent specification ID"),
    component_name: str = typer.Argument(..., help="Component name"),
    description: str = typer.Argument(..., help="Component description"),
    model: str = typer.Option("sonnet", "--model", help="LLM model to use"),
    provider: str = typer.Option("anthropic", "--provider", help="LLM provider"),
):
    """Create new component under parent specification."""
    _validate_api_key_for_provider(provider)
    
    console.print(f"[blue]Creating component:[/blue] {component_name}")
    console.print(f"[cyan]Parent:[/cyan] {parent_spec_id}")
    console.print(f"[cyan]Description:[/cyan] {description}")
    
    params = {
        "parent_spec_id": parent_spec_id,
        "component_name": component_name,
        "description": description,
        "model": model,
        "provider": provider
    }
    
    import asyncio
    result = asyncio.run(stream_sse_request("/stream/create-component", params))
    
    if result.get("success"):
        component_id = result.get("component_id")
        console.print(f"[green]✓ Component created:[/green] {component_id}")
        
        next_steps = result.get("next_steps", [])
        if next_steps:
            console.print(Panel(
                "\n".join(f"{i+1}. {step}" for i, step in enumerate(next_steps)),
                title="📋 Next Steps",
                border_style="green"
            ))
    else:
        console.print("[red]Component creation failed[/red]")
        raise typer.Exit(1)


@app.command()
def refine_component(
    parent_spec_id: str = typer.Argument(..., help="Parent specification ID"),
    component_id: str = typer.Argument(..., help="Component ID to refine"),
    response: str = typer.Argument(..., help="Your response or refinement input"),
    model: str = typer.Option("sonnet", "--model", help="LLM model to use"),
    provider: str = typer.Option("anthropic", "--provider", help="LLM provider"),
):
    """Refine component with automatic parent synchronization."""
    _validate_api_key_for_provider(provider)
    
    console.print(f"[blue]Refining component:[/blue] {component_id}")
    console.print(f"[cyan]Parent:[/cyan] {parent_spec_id}")
    console.print(f"[cyan]Input:[/cyan] {response}")
    
    params = {
        "parent_spec_id": parent_spec_id,
        "component_id": component_id,
        "user_response": response,
        "model": model,
        "provider": provider
    }
    
    import asyncio
    result = asyncio.run(stream_sse_request("/stream/refine-component", params))
    
    if result.get("success"):
        console.print(f"[green]✓ Component refined with parent sync[/green]")
        
        sync_summary = result.get("sync_summary", {})
        if sync_summary:
            console.print(Panel(
                f"Component updated: {sync_summary.get('component_changes', 'No changes')}\n"
                f"Parent updated: {sync_summary.get('parent_changes', 'No changes')}\n"
                f"Conflicts: {sync_summary.get('conflicts', 'None')}",
                title="🔄 Synchronization Summary",
                border_style="cyan"
            ))
        
        ready_for_contracts = result.get("ready_for_contracts", False)
        if ready_for_contracts:
            console.print("[bright_green]🎉 Component is ready for contract generation![/bright_green]")
    else:
        console.print("[red]Component refinement failed[/red]")
        raise typer.Exit(1)


@app.command()
def show_hierarchy(
    specification_id: str = typer.Argument(..., help="Specification ID to show hierarchy for"),
):
    """Show specification hierarchy."""
    try:
        result = make_request("GET", f"/specification/{specification_id}/hierarchy")
        
        spec_name = result.get("name", "Unknown")
        console.print(f"[blue]Specification Hierarchy:[/blue] {spec_name}")
        console.print(f"[cyan]ID:[/cyan] {specification_id}")
        
        spec_type = result.get("type", "monolithic")
        if spec_type == "composite":
            console.print(f"[cyan]Type:[/cyan] Composite (has components)")
            
            components = result.get("components", [])
            if components:
                hierarchy_table = Table(title="🧩 Components")
                hierarchy_table.add_column("Component ID", style="cyan")
                hierarchy_table.add_column("Name", style="green")
                hierarchy_table.add_column("Ready for Contracts", style="yellow")
                hierarchy_table.add_column("Last Sync", style="dim")
                
                for comp in components:
                    ready = "✓" if comp.get("ready_for_contracts", False) else "✗"
                    last_sync = comp.get("last_sync", "Never")
                    if last_sync != "Never":
                        last_sync = last_sync.split("T")[0]  # Just the date
                    
                    hierarchy_table.add_row(
                        comp.get("id", "Unknown"),
                        comp.get("name", "Unknown"),
                        ready,
                        last_sync
                    )
                
                console.print(hierarchy_table)
            
            dependencies = result.get("dependencies", {})
            if dependencies:
                console.print(Panel(
                    "\n".join(f"• {comp} depends on: {', '.join(deps)}" for comp, deps in dependencies.items()),
                    title="🔗 Dependencies",
                    border_style="blue"
                ))
        else:
            console.print(f"[cyan]Type:[/cyan] Monolithic (no components)")
            console.print("[dim]Use 'axiomander analyze-decomposition' to explore decomposition opportunities[/dim]")
        
    except Exception as e:
        console.print(f"[red]Error showing hierarchy:[/red] {e}")
        raise typer.Exit(1)


@app.command()
def sync_status(
    specification_id: str = typer.Argument(..., help="Specification ID to check sync status for"),
):
    """Check synchronization status for specification family."""
    try:
        result = make_request("GET", f"/specification/{specification_id}/sync-status")
        
        console.print(f"[blue]Sync Status for:[/blue] {result.get('name', 'Unknown')}")
        
        overall_status = result.get("overall_status", "unknown")
        status_color = {
            "synced": "green",
            "pending": "yellow", 
            "conflicts": "red",
            "unknown": "dim"
        }.get(overall_status, "white")
        
        console.print(f"[{status_color}]Overall Status:[/{status_color}] {overall_status}")
        
        components = result.get("components", [])
        if components:
            sync_table = Table(title="🔄 Component Sync Status")
            sync_table.add_column("Component", style="cyan")
            sync_table.add_column("Status", style="white")
            sync_table.add_column("Last Sync", style="dim")
            sync_table.add_column("Pending Changes", style="yellow")
            
            for comp in components:
                status = comp.get("sync_status", "unknown")
                last_sync = comp.get("last_sync", "Never")
                if last_sync != "Never":
                    last_sync = last_sync.split("T")[0]
                
                pending = str(comp.get("pending_changes", 0))
                
                sync_table.add_row(
                    comp.get("name", "Unknown"),
                    status,
                    last_sync,
                    pending
                )
            
            console.print(sync_table)
        
        conflicts = result.get("conflicts", [])
        if conflicts:
            console.print(Panel(
                "\n".join(f"• {conflict}" for conflict in conflicts),
                title="⚠️ Conflicts",
                border_style="red"
            ))
        
    except Exception as e:
        console.print(f"[red]Error checking sync status:[/red] {e}")
        raise typer.Exit(1)


@app.command()
def sync_component(
    parent_spec_id: str = typer.Argument(..., help="Parent specification ID"),
    component_id: str = typer.Argument(..., help="Component ID to sync"),
    force: bool = typer.Option(False, "--force", help="Force sync even if conflicts exist"),
):
    """Manually trigger component synchronization."""
    console.print(f"[blue]Syncing component:[/blue] {component_id}")
    console.print(f"[cyan]Parent:[/cyan] {parent_spec_id}")
    
    try:
        data = {
            "parent_spec_id": parent_spec_id,
            "component_id": component_id,
            "force": force
        }
        result = make_request("POST", "/sync-component", data)
        
        if result.get("success"):
            console.print(f"[green]✓ Component synchronized successfully[/green]")
            
            changes = result.get("changes", {})
            if changes:
                console.print(Panel(
                    f"Component changes: {changes.get('component', 'None')}\n"
                    f"Parent changes: {changes.get('parent', 'None')}\n"
                    f"Conflicts resolved: {changes.get('conflicts_resolved', 0)}",
                    title="🔄 Sync Results",
                    border_style="green"
                ))
        else:
            error = result.get("error", "Unknown error")
            console.print(f"[red]Sync failed:[/red] {error}")
            raise typer.Exit(1)
        
    except Exception as e:
        console.print(f"[red]Error syncing component:[/red] {e}")
        raise typer.Exit(1)


@app.command()
def models():
    """List available LLM models and aliases."""
    from .llm_service import get_available_claude_models
    
    models = get_available_claude_models()
    
    # Group by actual model
    model_groups = {}
    for alias, actual in models.items():
        if actual not in model_groups:
            model_groups[actual] = []
        if alias != actual:  # Don't include the actual name as an alias
            model_groups[actual].append(alias)
    
    console.print("[bold blue]Available Claude Models:[/bold blue]\n")
    
    for actual_model, aliases in model_groups.items():
        console.print(f"[green]• {actual_model}[/green]")
        if aliases:
            console.print(f"  [dim]Aliases: {', '.join(sorted(aliases))}[/dim]")
        console.print()
    
    console.print("[cyan]Usage examples:[/cyan]")
    console.print("  axiomander generate 'user auth' --model sonnet")
    console.print("  axiomander generate 'user auth' --model opus-4")
    console.print("  axiomander generate 'user auth' --model claude-sonnet-4-20250514")


@app.command()
def config(
    server_url: Optional[str] = typer.Option(None, "--server-url", help="Set server URL"),
    api_key: Optional[str] = typer.Option(None, "--api-key", help="Set API key"),
    show: bool = typer.Option(False, "--show", help="Show current configuration"),
):
    """Configure axiomander client settings."""
    if show:
        current_url, current_key = get_server_config()
        console.print(f"[cyan]Server URL:[/cyan] {current_url}")
        console.print(f"[cyan]API Key:[/cyan] {'*' * (len(current_key) - 4) + current_key[-4:] if len(current_key) > 4 else '****'}")
        return
    
    if server_url or api_key:
        console.print("[yellow]Configuration via environment variables:[/yellow]")
        if server_url:
            console.print(f"export AXIOMANDER_SERVER_URL={server_url}")
        if api_key:
            console.print(f"export AXIOMANDER_API_KEY={api_key}")
        console.print("\n[cyan]Or add them to your shell profile (.bashrc, .zshrc, etc.)[/cyan]")
    else:
        console.print("[yellow]Usage:[/yellow]")
        console.print("  axiomander config --show")
        console.print("  axiomander config --server-url http://localhost:8000")
        console.print("  axiomander config --api-key your-api-key")


def _format_contracts(contracts: List[Dict]) -> str:
    """Format contracts for display."""
    lines = []
    for contract in contracts:
        lines.append(f"**{contract.get('name', 'Unknown')}**")
        if contract.get('description'):
            lines.append(f"  {contract['description']}")
        
        preconditions = contract.get('preconditions', [])
        if preconditions:
            lines.append(f"  Preconditions: {', '.join(preconditions)}")
        
        postconditions = contract.get('postconditions', [])
        if postconditions:
            lines.append(f"  Postconditions: {', '.join(postconditions)}")
        
        lines.append("")
    
    return "\n".join(lines)


def _format_subcontracts(subcontracts: List[Dict]) -> str:
    """Format subcontracts for display."""
    lines = []
    for subcontract in subcontracts:
        lines.append(f"**{subcontract.get('name', 'Unknown')}**")
        if subcontract.get('purpose'):
            lines.append(f"  Purpose: {subcontract['purpose']}")
        
        dependencies = subcontract.get('dependencies', [])
        if dependencies:
            lines.append(f"  Dependencies: {', '.join(dependencies)}")
        
        lines.append("")
    
    return "\n".join(lines)


def _format_refactor_suggestions(suggestions: List[Dict]) -> str:
    """Format refactoring suggestions for display."""
    lines = []
    for suggestion in suggestions:
        lines.append(f"**{suggestion.get('type', 'Unknown').replace('_', ' ').title()}**")
        if suggestion.get('description'):
            lines.append(f"  {suggestion['description']}")
        if suggestion.get('file'):
            lines.append(f"  File: {suggestion['file']}")
        if suggestion.get('line_range'):
            lines.append(f"  Lines: {suggestion['line_range']}")
        lines.append("")
    
    return "\n".join(lines)


def _format_impact_analysis(impact: Dict) -> str:
    """Format impact analysis for display."""
    lines = []
    for key, value in impact.items():
        formatted_key = key.replace('_', ' ').title()
        lines.append(f"**{formatted_key}:** {value}")
    
    return "\n".join(lines)


def _format_contract_descriptions(contracts: List[Dict]) -> str:
    """Format contract descriptions for display."""
    lines = []
    for contract in contracts:
        lines.append(f"**{contract.get('function_name', 'Unknown Function')}**")
        
        preconditions = contract.get('preconditions', [])
        if preconditions:
            lines.append("  Preconditions:")
            for pre in preconditions:
                desc = pre.get('description', 'No description')
                rationale = pre.get('rationale', '')
                lines.append(f"    • {desc}")
                if rationale:
                    lines.append(f"      → {rationale}")
        
        postconditions = contract.get('postconditions', [])
        if postconditions:
            lines.append("  Postconditions:")
            for post in postconditions:
                desc = post.get('description', 'No description')
                rationale = post.get('rationale', '')
                lines.append(f"    • {desc}")
                if rationale:
                    lines.append(f"      → {rationale}")
        
        invariants = contract.get('invariants', [])
        if invariants:
            lines.append("  Invariants:")
            for inv in invariants:
                desc = inv.get('description', 'No description')
                rationale = inv.get('rationale', '')
                lines.append(f"    • {desc}")
                if rationale:
                    lines.append(f"      → {rationale}")
        
        lines.append("")
    
    return "\n".join(lines)


def _format_conversation_history(history: List[Dict]) -> str:
    """Format conversation history for display."""
    lines = []
    for i, msg in enumerate(history):
        role = msg.get('role', 'unknown')
        content = msg.get('content', '')
        
        if role == 'user':
            lines.append(f"[bold blue]User:[/bold blue] {content}")
        elif role == 'assistant':
            lines.append(f"[bold green]AI:[/bold green] {content}")
        else:
            lines.append(f"[bold]{role.title()}:[/bold] {content}")
        
        if i < len(history) - 1:
            lines.append("")
    
    return "\n".join(lines)


def _format_conversation_summary(history: List[Dict]) -> str:
    """Format conversation history summary for display."""
    if not history:
        return "No conversation history"
    
    lines = []
    lines.append(f"[bold]Total Messages:[/bold] {len(history)}")
    
    # Show first user message (initial description)
    first_user_msg = next((msg for msg in history if msg.get('role') == 'user'), None)
    if first_user_msg:
        content = first_user_msg.get('content', '')
        preview = content[:100] + "..." if len(content) > 100 else content
        lines.append(f"[bold blue]Initial Request:[/bold blue] {preview}")
    
    # Show last AI message (latest response)
    last_ai_msg = None
    for msg in reversed(history):
        if msg.get('role') == 'assistant':
            last_ai_msg = msg
            break
    
    if last_ai_msg:
        content = last_ai_msg.get('content', '')
        preview = content[:150] + "..." if len(content) > 150 else content
        lines.append(f"[bold green]Latest AI Response:[/bold green] {preview}")
    
    return "\n".join(lines)


def _show_component_preview(suggestion: ComponentSuggestion):
    """Show detailed component preview."""
    name = suggestion.name
    scope = suggestion.suggested_scope
    sections = suggestion.parent_sections
    dependencies = suggestion.dependencies
    complexity = suggestion.complexity
    rationale = suggestion.rationale
    preview_content = suggestion.preview_content
    
    # Main component info
    info_text = f"""[bold]Scope:[/bold] {scope}

[bold]Parent Sections:[/bold] {', '.join(sections) if sections else 'None specified'}

[bold]Dependencies:[/bold] {', '.join(dependencies) if dependencies else 'None'}

[bold]Complexity:[/bold] {complexity.title()}

[bold]Rationale:[/bold] {rationale}"""
    
    console.print(Panel(
        info_text,
        title=f"🧩 Component: {name}",
        border_style="blue"
    ))
    
    if preview_content:
        # Truncate if too long
        if len(preview_content) > 400:
            preview_content = preview_content[:400] + "\n\n[dim]... (truncated)[/dim]"
        
        console.print(Panel(
            preview_content,
            title="📝 Content Preview",
            border_style="dim"
        ))


def _get_component_decision(suggestion: ComponentSuggestion) -> str:
    """Get user decision for a component suggestion."""
    while True:
        choice = Prompt.ask(
            "\n[bold]What would you like to do with this component?[/bold]",
            choices=["approve", "edit", "skip", "preview"],
            default="approve"
        )
        
        if choice == "approve":
            return "approved"
        elif choice == "skip":
            return "skipped"
        elif choice == "preview":
            _show_full_component_preview(suggestion)
            continue  # Ask again
        elif choice == "edit":
            if _edit_component_suggestion(suggestion):
                return "edited"
            else:
                continue  # Ask again if editing was cancelled
        
        return choice


def _show_full_component_preview(suggestion: ComponentSuggestion):
    """Show full component preview including complete content."""
    preview_content = suggestion.preview_content or 'No preview content available'
    name = suggestion.name
    
    console.print(Panel(
        preview_content,
        title=f"📝 Full Preview: {name}",
        border_style="cyan"
    ))


def _edit_component_suggestion(suggestion: ComponentSuggestion) -> bool:
    """Allow user to edit component suggestion. Returns True if changes were made."""
    console.print("\n[cyan]What would you like to edit?[/cyan]")
    console.print("1. Component name")
    console.print("2. Scope description")
    console.print("3. Add custom instructions")
    console.print("4. Cancel editing")
    
    choice = Prompt.ask("Select option", choices=["1", "2", "3", "4"], default="4")
    
    if choice == "1":
        current_name = suggestion.name
        new_name = Prompt.ask(f"New component name", default=current_name)
        if new_name and new_name != current_name:
            suggestion.name = new_name
            console.print(f"[green]✓ Updated name to: {new_name}[/green]")
            return True
    
    elif choice == "2":
        current_scope = suggestion.suggested_scope
        console.print(f"[dim]Current scope: {current_scope}[/dim]")
        new_scope = Prompt.ask("New scope description")
        if new_scope and new_scope != current_scope:
            suggestion.suggested_scope = new_scope
            console.print(f"[green]✓ Updated scope[/green]")
            return True
    
    elif choice == "3":
        instructions = Prompt.ask("Additional instructions for this component")
        if instructions:
            # Add instructions to rationale
            current_rationale = suggestion.rationale
            suggestion.rationale = f"{current_rationale}\n\nUser instructions: {instructions}"
            console.print(f"[green]✓ Added custom instructions[/green]")
            return True
    
    elif choice == "4":
        console.print("[yellow]Editing cancelled[/yellow]")
        return False
    
    return False


def _create_approved_components(
    specification_id: str, 
    approved_components: List[ComponentSuggestion], 
    model: str, 
    provider: str
):
    """Create the approved components using the batch decomposition endpoint."""
    # Convert approved components to comma-separated names
    component_names = ",".join(comp.name for comp in approved_components)
    
    console.print(f"[blue]Creating components:[/blue] {component_names}")
    
    params = {
        "specification_id": specification_id,
        "component_names": component_names,
        "model": model,
        "provider": provider
    }
    
    import asyncio
    result = asyncio.run(stream_sse_request("/stream/decompose-specification", params))
    
    if result.get("success"):
        components = result.get("created_components", [])
        console.print(f"[green]✓ Successfully created {len(components)} components[/green]")
        
        # Show created components
        if components:
            component_table = Table(title="🧩 Created Components")
            component_table.add_column("Name", style="green")
            component_table.add_column("ID", style="cyan")
            component_table.add_column("Status", style="yellow")
            
            for comp in components:
                component_table.add_row(
                    comp.get('name', 'Unknown'),
                    comp.get('id', 'Unknown'),
                    "Ready for refinement"
                )
            
            console.print(component_table)
        
        console.print(Panel(
            f"Use 'axiomander show-hierarchy {specification_id}' to see the component structure\n"
            f"Use 'axiomander refine-component {specification_id} <component_id> \"your input\"' to refine components",
            title="📋 Next Steps",
            border_style="green"
        ))
    else:
        console.print("[red]Failed to create approved components[/red]")
        error = result.get("error", "Unknown error")
        console.print(f"[red]Error: {error}[/red]")


def _display_statistics(stats: Dict[str, Any]):
    """Display contract statistics using Rich formatting."""
    # Overview panel
    overview_text = f"""
[bold]Total Contracts:[/bold] {stats.get('total_contracts', 0)}
[bold]Modules with Contracts:[/bold] {stats.get('modules_with_contracts', 0)}
[bold]Average Conditions per Contract:[/bold] {stats.get('average_conditions_per_contract', 0):.1f}
"""
    console.print(Panel(overview_text.strip(), title="📊 Contract Overview", border_style="blue"))
    
    # Condition counts
    conditions = stats.get('condition_counts', {})
    if conditions:
        condition_text = f"""
[bold]Preconditions:[/bold] {conditions.get('preconditions', 0)}
[bold]Postconditions:[/bold] {conditions.get('postconditions', 0)}
[bold]Invariants:[/bold] {conditions.get('invariants', 0)}
[bold]Total Conditions:[/bold] {conditions.get('total', 0)}
"""
        console.print(Panel(condition_text.strip(), title="🔍 Condition Breakdown", border_style="green"))


class InteractiveSession:
    """Interactive session manager for axiomander."""
    
    def __init__(self):
        self.project_root = Path(".").resolve()
        self.current_spec_id = None
        self.current_mode = "exploration"  # exploration, specification, refinement, implementation
        self.provider = "anthropic"
        self.model = "sonnet"
        self.console = Console()
        self.session_active = True
        self.readline_available = False
        self._setup_completion()
    
    def _setup_completion(self):
        """Set up tab completion for the interactive session."""
        try:
            import readline
            # Set up readline for tab completion and history
            readline.set_completer(self._completer)
            readline.parse_and_bind("tab: complete")
            
            # Set word delimiters (space and common punctuation, but NOT /)
            readline.set_completer_delims(' \t\n`!@#$%^&*()=+[{]}\\|;:\'",<>?')
            
            # Enable command history
            readline.set_history_length(1000)
            
            # Try to load existing history
            history_file = Path.home() / ".axiomander_history"
            try:
                readline.read_history_file(str(history_file))
            except FileNotFoundError:
                pass  # No history file yet
            
            # Save history on exit
            import atexit
            atexit.register(lambda: readline.write_history_file(str(history_file)))
            
            self.readline_available = True
        except ImportError:
            # readline not available on all platforms
            self.readline_available = False
    
    def _completer(self, text: str, state: int) -> Optional[str]:
        """Tab completion function for interactive commands."""
        try:
            import readline
            # Get the current line and parse it
            line = readline.get_line_buffer()
            
            # Handle completion for both command and natural language modes
            if line.startswith('/'):
                # Command mode - complete commands and their arguments
                return self._complete_command_mode(line, text, state)
            else:
                # Natural language mode - no completion for now
                # Could add context-aware completion later
                return None
            
        except Exception:
            # Don't let completion errors break the session
            return None
    
    def _complete_command_mode(self, line: str, text: str, state: int) -> Optional[str]:
        """Handle completion in command mode (lines starting with /)."""
        # Remove the leading / for parsing
        command_line = line[1:]
        parts = command_line.split()
        
        # If we're at the beginning or only have one word, complete commands
        if len(parts) <= 1:
            commands = [cmd["cmd"].split()[0] for cmd in self.get_available_commands()]
            # Add the / prefix back to matches
            matches = [f"/{cmd}" for cmd in commands if cmd.startswith(text.lstrip('/'))]
            return matches[state] if state < len(matches) else None
        
        # Get the command and current argument position
        command = parts[0].lower()
        
        # Complete specification IDs for relevant commands
        spec_commands = ['select-spec', 'show-spec', 'refine', 'generate-contracts', 'implement', 'edit-spec', 
                        'show-hierarchy', 'analyze-decomposition', 'decompose', 'create-component', 'sync-status']
        if command in spec_commands:
            # Check if we're completing the first argument (spec ID)
            completing_first_arg = (line.endswith(' ') and len(parts) == 1) or (not line.endswith(' ') and len(parts) == 2)
            
            if completing_first_arg:
                # Get available specification IDs
                spec_ids = self._get_available_spec_ids()
                if spec_ids:  # Only try to match if we have spec IDs
                    matches = [spec_id for spec_id in spec_ids if spec_id.startswith(text)]
                    return matches[state] if state < len(matches) else None
        
        # Complete component IDs for component-specific commands
        component_commands = ['refine-component']
        if command in component_commands:
            # Check if we're completing the second argument (component ID)
            completing_second_arg = (line.endswith(' ') and len(parts) == 2) or (not line.endswith(' ') and len(parts) == 3)
            
            if completing_second_arg and len(parts) >= 2:
                parent_spec_id = parts[1] if len(parts) >= 2 else None
                if parent_spec_id:
                    component_ids = self._get_available_component_ids(parent_spec_id)
                    if component_ids:
                        matches = [comp_id for comp_id in component_ids if comp_id.startswith(text)]
                        return matches[state] if state < len(matches) else None
        
        # Complete model names for model command
        if command == 'model':
            if (line.endswith(' ') and len(parts) == 1) or (not line.endswith(' ') and len(parts) == 2):
                from .llm_service import get_available_claude_models
                models = list(get_available_claude_models().keys())
                matches = [model for model in models if model.startswith(text)]
                return matches[state] if state < len(matches) else None
        
        # Complete provider names for provider command
        if command == 'provider':
            if (line.endswith(' ') and len(parts) == 1) or (not line.endswith(' ') and len(parts) == 2):
                providers = ['anthropic', 'openai']
                matches = [provider for provider in providers if provider.startswith(text)]
                return matches[state] if state < len(matches) else None
        
        # Complete mode names for mode command
        if command == 'mode':
            if (line.endswith(' ') and len(parts) == 1) or (not line.endswith(' ') and len(parts) == 2):
                modes = ['exploration', 'specification', 'refinement', 'implementation']
                matches = [mode for mode in modes if mode.startswith(text)]
                return matches[state] if state < len(matches) else None
        
        # Complete directory paths for project command
        if command == 'project':
            if (line.endswith(' ') and len(parts) == 1) or (not line.endswith(' ') and len(parts) == 2):
                # Simple directory completion
                try:
                    if text.startswith('/'):
                        # Absolute path
                        base_dir = Path(text).parent if '/' in text else Path('/')
                        prefix = Path(text).name
                    elif text.startswith('./') or text.startswith('../'):
                        # Relative path
                        base_dir = Path(text).parent if '/' in text else Path('.')
                        prefix = Path(text).name
                    else:
                        # Current directory
                        base_dir = Path('.')
                        prefix = text
                    
                    if base_dir.exists():
                        dirs = [d.name for d in base_dir.iterdir() if d.is_dir() and d.name.startswith(prefix)]
                        # Add trailing slash for directories
                        matches = [f"{d}/" for d in dirs]
                        return matches[state] if state < len(matches) else None
                except:
                    pass
        
        return None
    
    def _get_available_spec_ids(self) -> List[str]:
        """Get list of available specification IDs for completion."""
        try:
            # Directly scan the filesystem for spec IDs
            specs_dir = Path(".axiomander/specs")
            if not specs_dir.exists():
                return []
            
            spec_ids = []
            for spec_path in specs_dir.iterdir():
                if spec_path.is_dir() and spec_path.name.startswith("spec_"):
                    # Verify it's a valid spec by checking for metadata
                    metadata_file = spec_path / "metadata.json"
                    if metadata_file.exists():
                        spec_ids.append(spec_path.name)
            
            return sorted(spec_ids)
        except Exception as e:
            # Debug: print error to help troubleshoot
            # print(f"Debug: Error getting spec IDs: {e}")
            return []
    
    def _get_available_component_ids(self, parent_spec_id: str) -> List[str]:
        """Get list of available component IDs for a parent specification."""
        try:
            components_dir = Path(f".axiomander/specs/{parent_spec_id}/components")
            if not components_dir.exists():
                return []
            
            component_ids = []
            for comp_path in components_dir.iterdir():
                if comp_path.is_dir():
                    # Verify it's a valid component by checking for metadata
                    metadata_file = comp_path / "metadata.json"
                    if metadata_file.exists():
                        component_ids.append(comp_path.name)
            
            return sorted(component_ids)
        except Exception as e:
            return []
        
    def get_context_info(self) -> Dict[str, Any]:
        """Get current context information."""
        context = {
            "project_root": str(self.project_root),
            "current_spec": self.current_spec_id,
            "mode": self.current_mode,
            "provider": self.provider,
            "model": self.model
        }
        
        # Check for existing specifications
        specs_dir = Path(".axiomander/specs")
        if specs_dir.exists():
            specs = []
            for spec_path in specs_dir.iterdir():
                if spec_path.is_dir() and spec_path.name.startswith("spec_"):
                    metadata_file = spec_path / "metadata.json"
                    if metadata_file.exists():
                        try:
                            with open(metadata_file, 'r') as f:
                                metadata = json.load(f)
                            specs.append({
                                "id": spec_path.name,
                                "name": metadata.get("name", "Unknown"),
                                "ready_for_contracts": metadata.get("ready_for_contracts", False)
                            })
                        except:
                            continue
            context["available_specs"] = specs
        else:
            context["available_specs"] = []
        
        return context
    
    def display_status(self):
        """Display current session status."""
        context = self.get_context_info()
        
        # Main status panel
        status_text = f"""
[bold blue]Project:[/bold blue] {context['project_root']}
[bold green]Mode:[/bold green] {context['mode'].title()}
[bold yellow]Model:[/bold yellow] {context['model']} ({context['provider']})
[bold cyan]Current Spec:[/bold cyan] {context['current_spec'] or 'None'}
"""
        
        self.console.print(Panel(
            status_text.strip(),
            title="🦎 Axiomander Interactive Session",
            border_style="blue"
        ))
        
        # Available specifications
        specs = context.get("available_specs", [])
        if specs:
            spec_table = Table(title="📝 Available Specifications")
            spec_table.add_column("ID", style="cyan")
            spec_table.add_column("Name", style="green")
            spec_table.add_column("Ready for Contracts", style="yellow")
            
            for spec in specs:
                ready = "✓" if spec.get("ready_for_contracts", False) else "✗"
                spec_table.add_row(
                    spec["id"],
                    spec["name"],
                    ready
                )
            
            self.console.print(spec_table)
    
    def get_available_commands(self) -> List[Dict[str, str]]:
        """Get available commands based on current context."""
        context = self.get_context_info()
        commands = []
        
        # Always available commands
        commands.extend([
            {"cmd": "status", "desc": "Show current session status"},
            {"cmd": "project <path>", "desc": "Change project directory (TAB completes paths)"},
            {"cmd": "model <model>", "desc": "Change LLM model (TAB completes model names)"},
            {"cmd": "provider <provider>", "desc": "Change LLM provider (TAB completes providers)"},
            {"cmd": "mode <mode>", "desc": "Change mode (TAB completes mode names)"},
            {"cmd": "help", "desc": "Show available commands"},
            {"cmd": "completion-help", "desc": "Show tab completion help"},
            {"cmd": "debug-completion", "desc": "Show completion debug info"},
            {"cmd": "quit", "desc": "Exit interactive session"},
        ])
        
        # Context-specific commands
        if context["mode"] == "exploration":
            commands.extend([
                {"cmd": "analyze", "desc": "Analyze current project for contract opportunities"},
                {"cmd": "scan", "desc": "Scan project and build contract graph"},
                {"cmd": "stats", "desc": "Show contract statistics"},
                {"cmd": "create-spec <name> <description>", "desc": "Create new specification"},
                {"cmd": "list-specs", "desc": "List all specifications"},
            ])
        
        elif context["mode"] == "specification":
            if context["current_spec"]:
                commands.extend([
                    {"cmd": "show-spec", "desc": "Show current specification details"},
                    {"cmd": "show-hierarchy", "desc": "Show specification hierarchy and components"},
                    {"cmd": "refine <response>", "desc": "Refine current specification with your input"},
                    {"cmd": "edit-spec <instructions>", "desc": "Direct specification editing with AI assistance"},
                    {"cmd": "generate-contracts", "desc": "Generate contracts from current specification"},
                    {"cmd": "analyze-decomposition", "desc": "Analyze decomposition opportunities"},
                    {"cmd": "decompose <component_names>", "desc": "Decompose into components (comma-separated names)"},
                    {"cmd": "decompose-interactive", "desc": "Interactive decomposition with component preview and approval"},
                    {"cmd": "create-component <name> <description>", "desc": "Create new component"},
                    {"cmd": "refine-component <component_id> <response>", "desc": "Refine component with parent sync"},
                    {"cmd": "sync-status", "desc": "Check synchronization status"},
                ])
            else:
                commands.extend([
                    {"cmd": "select-spec <spec_id>", "desc": "Select a specification to work with (TAB completes IDs)"},
                    {"cmd": "create-spec <name> <description>", "desc": "Create new specification"},
                ])
        
        elif context["mode"] == "refinement":
            commands.extend([
                {"cmd": "decompose <aim>", "desc": "Decompose high-level aim into components"},
                {"cmd": "generate <aim>", "desc": "Generate contracts for specific aim"},
            ])
        
        elif context["mode"] == "implementation":
            commands.extend([
                {"cmd": "refactor", "desc": "Analyze refactoring opportunities"},
                {"cmd": "implement <spec_id>", "desc": "Generate implementation for specification (TAB completes IDs)"},
            ])
        
        # Specification selection commands
        specs = context.get("available_specs", [])
        if specs and not context["current_spec"]:
            commands.append({"cmd": "select-spec <spec_id>", "desc": "Select specification to work with (TAB completes IDs)"})
        
        return commands
    
    def display_commands(self):
        """Display available commands."""
        commands = self.get_available_commands()
        
        cmd_table = Table(title="🎯 Available Commands")
        cmd_table.add_column("Command", style="cyan", width=30)
        cmd_table.add_column("Description", style="white")
        
        for cmd in commands:
            cmd_table.add_row(cmd["cmd"], cmd["desc"])
        
        self.console.print(cmd_table)
        
        # Show completion hints
        spec_ids = self._get_available_spec_ids()
        if spec_ids:
            self.console.print(f"\n[dim]💡 Use TAB to complete specification IDs: {', '.join(spec_ids[:3])}{'...' if len(spec_ids) > 3 else ''}[/dim]")
        
        self.console.print("[dim]💡 Use TAB to complete commands, models, providers, and paths[/dim]")
    
    async def execute_command(self, command: str, args: List[str]):
        """Execute a command with arguments."""
        try:
            if command == "status":
                self.display_status()
            
            elif command == "help":
                self.display_commands()
            
            elif command == "completion-help":
                self._show_completion_help()
            
            elif command == "debug-completion":
                self._show_completion_debug()
            
            elif command == "quit":
                self.session_active = False
                self.console.print("[green]Goodbye! 🦎[/green]")
            
            elif command == "project":
                if args:
                    new_path = Path(args[0]).resolve()
                    if new_path.exists():
                        self.project_root = new_path
                        os.chdir(new_path)
                        self.console.print(f"[green]Changed project to:[/green] {new_path}")
                    else:
                        self.console.print(f"[red]Directory not found:[/red] {args[0]}")
                else:
                    self.console.print(f"[cyan]Current project:[/cyan] {self.project_root}")
            
            elif command == "model":
                if args:
                    self.model = args[0]
                    self.console.print(f"[green]Changed model to:[/green] {self.model}")
                else:
                    self.console.print(f"[cyan]Current model:[/cyan] {self.model}")
            
            elif command == "provider":
                if args:
                    if args[0] in ["anthropic", "openai"]:
                        self.provider = args[0]
                        self.console.print(f"[green]Changed provider to:[/green] {self.provider}")
                    else:
                        self.console.print(f"[red]Invalid provider:[/red] {args[0]}. Use 'anthropic' or 'openai'")
                else:
                    self.console.print(f"[cyan]Current provider:[/cyan] {self.provider}")
            
            elif command == "mode":
                if args:
                    valid_modes = ["exploration", "specification", "refinement", "implementation"]
                    if args[0] in valid_modes:
                        self.current_mode = args[0]
                        self.console.print(f"[green]Changed mode to:[/green] {self.current_mode}")
                        self.display_commands()  # Show new commands for this mode
                    else:
                        self.console.print(f"[red]Invalid mode:[/red] {args[0]}. Use: {', '.join(valid_modes)}")
                else:
                    self.console.print(f"[cyan]Current mode:[/cyan] {self.current_mode}")
            
            elif command == "analyze":
                await self._run_analyze()
            
            elif command == "scan":
                await self._run_scan()
            
            elif command == "stats":
                await self._run_stats()
            
            elif command == "create-spec":
                if len(args) >= 2:
                    name = args[0]
                    description = " ".join(args[1:])
                    await self._run_create_spec(name, description)
                else:
                    self.console.print("[red]Usage:[/red] create-spec <name> <description>")
            
            elif command == "list-specs":
                await self._run_list_specs()
            
            elif command == "select-spec":
                if args:
                    self.current_spec_id = args[0]
                    self.current_mode = "specification"
                    self.console.print(f"[green]Selected specification:[/green] {args[0]}")
                    self.console.print(f"[cyan]Switched to specification mode[/cyan]")
                else:
                    self.console.print("[red]Usage:[/red] select-spec <spec_id>")
            
            elif command == "show-spec":
                if self.current_spec_id:
                    await self._run_show_spec(self.current_spec_id)
                else:
                    self.console.print("[red]No specification selected[/red]")
            
            elif command == "refine":
                if self.current_spec_id and args:
                    response = " ".join(args)
                    await self._run_refine_spec(self.current_spec_id, response)
                else:
                    self.console.print("[red]Usage:[/red] refine <your response>")
            
            elif command == "edit-spec":
                if self.current_spec_id and args:
                    instructions = " ".join(args)
                    await self._run_edit_spec(self.current_spec_id, instructions)
                else:
                    self.console.print("[red]Usage:[/red] edit-spec <editing instructions>")
            
            elif command == "generate-contracts":
                if self.current_spec_id:
                    await self._run_generate_contracts(self.current_spec_id)
                else:
                    self.console.print("[red]No specification selected[/red]")
            
            elif command == "show-hierarchy":
                if self.current_spec_id:
                    await self._run_show_hierarchy(self.current_spec_id)
                else:
                    self.console.print("[red]No specification selected[/red]")
            
            elif command == "analyze-decomposition":
                if self.current_spec_id:
                    await self._run_analyze_decomposition(self.current_spec_id)
                else:
                    self.console.print("[red]No specification selected[/red]")
            
            elif command == "decompose":
                if self.current_spec_id and args:
                    component_names = " ".join(args)
                    await self._run_decompose_spec(self.current_spec_id, component_names)
                elif not self.current_spec_id:
                    self.console.print("[red]No specification selected[/red]")
                else:
                    self.console.print("[red]Usage:[/red] decompose <component_names>")
            
            elif command == "decompose-interactive":
                if self.current_spec_id:
                    await self._run_decompose_interactive(self.current_spec_id)
                else:
                    self.console.print("[red]No specification selected[/red]")
            
            elif command == "create-component":
                if self.current_spec_id and len(args) >= 2:
                    component_name = args[0]
                    description = " ".join(args[1:])
                    await self._run_create_component(self.current_spec_id, component_name, description)
                elif not self.current_spec_id:
                    self.console.print("[red]No specification selected[/red]")
                else:
                    self.console.print("[red]Usage:[/red] create-component <name> <description>")
            
            elif command == "refine-component":
                if self.current_spec_id and len(args) >= 2:
                    component_id = args[0]
                    response = " ".join(args[1:])
                    await self._run_refine_component(self.current_spec_id, component_id, response)
                elif not self.current_spec_id:
                    self.console.print("[red]No specification selected[/red]")
                else:
                    self.console.print("[red]Usage:[/red] refine-component <component_id> <response>")
            
            elif command == "sync-status":
                if self.current_spec_id:
                    await self._run_sync_status(self.current_spec_id)
                else:
                    self.console.print("[red]No specification selected[/red]")
            
            elif command == "generate":
                if args:
                    aim = " ".join(args)
                    await self._run_generate(aim)
                else:
                    self.console.print("[red]Usage:[/red] generate <aim>")
            
            elif command == "refactor":
                await self._run_refactor()
            
            else:
                self.console.print(f"[red]Unknown command:[/red] {command}")
                self.console.print("[cyan]Type '/help' to see available commands or just type naturally to chat with AI[/cyan]")
        
        except Exception as e:
            self.console.print(f"[red]Error executing command:[/red] {e}")
    
    async def handle_conversation(self, user_input: str):
        """Handle natural conversation with mode-specific AI agent."""
        try:
            # Get mode-specific system prompt
            system_prompt = self._get_mode_system_prompt()
            
            # Get current context for the AI
            context = self.get_context_info()
            context_str = self._format_context_for_ai(context)
            
            # Build conversation with context
            full_prompt = f"{context_str}\n\nUser: {user_input}"
            
            self.console.print("[dim]🤖 AI is thinking...[/dim]")
            
            # Make request to AI
            data = {
                "project_root": str(self.project_root),
                "mode": self.current_mode,
                "user_input": user_input,
                "context": context,
                "model": self.model,
                "provider": self.provider
            }
            
            # Use different endpoints based on mode
            if self.current_mode == "specification" and self.current_spec_id:
                # Use specification refinement
                params = {
                    "specification_id": self.current_spec_id,
                    "user_response": user_input,
                    "model": self.model,
                    "provider": self.provider
                }
                result = await stream_sse_request("/stream/refine-specification", params)
                
                if result.get("success"):
                    if result.get("ready_for_contracts"):
                        self.console.print("\n[bright_green]🎉 Specification is ready for contract generation![/bright_green]")
                        self.console.print("[cyan]Say 'generate contracts' to proceed[/cyan]")
                
            elif self.current_mode == "exploration":
                # Use general analysis and conversation
                data["mode"] = "exploration"  # Ensure mode is set correctly
                result = make_request("POST", "/analyze-project", data)
                
                if result.get("success"):
                    recommendations = result.get("recommendations", [])
                    if recommendations:
                        self.console.print("\n[green]💡 AI Recommendations:[/green]")
                        for rec in recommendations:
                            self.console.print(f"  • {rec}")
                
            else:
                # For other modes, use a simple conversation approach
                # This could be enhanced with mode-specific endpoints
                self.console.print(f"[yellow]Mode '{self.current_mode}' conversation not fully implemented yet.[/yellow]")
                self.console.print(f"[cyan]Your input:[/cyan] {user_input}")
                self.console.print("[dim]Use /commands for explicit actions[/dim]")
        
        except Exception as e:
            self.console.print(f"[red]Error in conversation:[/red] {e}")
    
    def _get_mode_system_prompt(self) -> str:
        """Get system prompt based on current mode."""
        if self.current_mode == "exploration":
            return """You are an expert software architect helping explore a codebase for design-by-contract opportunities. 
            
Your role is to:
- Analyze code structure and identify functions that would benefit from contracts
- Suggest areas where preconditions, postconditions, and invariants would improve code quality
- Help the user understand the current state of their project
- Guide them toward creating specifications for new features

Be conversational and helpful. Ask clarifying questions when needed."""

        elif self.current_mode == "specification":
            return """You are an expert in behavioral specification and design-by-contract programming.

Your role is to:
- Help refine behavioral specifications through conversation
- Ask clarifying questions about edge cases, error conditions, and requirements
- Guide the user toward complete, unambiguous specifications
- Determine when a specification is ready for contract generation
- Modify and update specification documents based on user feedback
- Maintain clear, well-structured specification documents

You can modify specifications by:
- Adding new behavioral requirements
- Clarifying existing requirements
- Reorganizing content for better clarity
- Adding examples and edge cases
- Updating status and readiness indicators

Be thorough but conversational. Focus on understanding the intended behavior completely and maintaining high-quality specification documents."""

        elif self.current_mode == "refinement":
            return """You are an expert software architect specializing in system decomposition.

Your role is to:
- Break down high-level aims into manageable components
- Suggest architectural patterns and design approaches
- Help identify the key contracts and interfaces needed
- Guide implementation planning

Be strategic and think about long-term maintainability."""

        elif self.current_mode == "implementation":
            return """You are an expert programmer specializing in design-by-contract implementation.

Your role is to:
- Help implement contracts in actual code
- Suggest refactoring opportunities to improve contract clarity
- Guide test-driven development with contracts
- Help with debugging contract violations

Be practical and focus on working, maintainable code."""

        else:
            return "You are a helpful AI assistant for design-by-contract programming."
    
    def _format_context_for_ai(self, context: Dict[str, Any]) -> str:
        """Format context information for AI consumption."""
        lines = []
        lines.append(f"Current Mode: {context['mode']}")
        lines.append(f"Project: {context['project_root']}")
        lines.append(f"Model: {context['model']} ({context['provider']})")
        
        if context.get('current_spec'):
            lines.append(f"Current Specification: {context['current_spec']}")
        
        specs = context.get('available_specs', [])
        if specs:
            lines.append(f"Available Specifications: {len(specs)}")
            for spec in specs[:3]:  # Show first 3
                status = "✓" if spec.get('ready_for_contracts') else "○"
                lines.append(f"  {status} {spec['name']} ({spec['id']})")
        
        return "\n".join(lines)
    
    async def _run_analyze(self):
        """Run project analysis."""
        self.console.print("[blue]Analyzing project...[/blue]")
        try:
            data = {
                "project_root": str(self.project_root),
                "mode": "specification",
                "model": self.model,
                "provider": self.provider
            }
            result = make_request("POST", "/analyze-project", data)
            
            if result.get("success"):
                self.console.print("[green]✓ Analysis completed[/green]")
                stats = result.get("statistics", {})
                if stats:
                    _display_statistics(stats)
                
                recommendations = result.get("recommendations", [])
                if recommendations:
                    self.console.print(Panel(
                        "\n".join(f"• {rec}" for rec in recommendations),
                        title="🎯 Recommendations",
                        border_style="green"
                    ))
            else:
                self.console.print(f"[red]Analysis failed:[/red] {result}")
        except Exception as e:
            self.console.print(f"[red]Analysis error:[/red] {e}")
    
    async def _run_scan(self):
        """Run project scan."""
        self.console.print("[blue]Scanning project...[/blue]")
        try:
            result = make_request("POST", f"/scan?project_root={self.project_root}")
            if result.get("success"):
                self.console.print(f"[green]✓ Found {result.get('contracts_found', 0)} contracts[/green]")
            else:
                self.console.print(f"[red]Scan failed:[/red] {result}")
        except Exception as e:
            self.console.print(f"[red]Scan error:[/red] {e}")
    
    async def _run_stats(self):
        """Show contract statistics."""
        try:
            result = make_request("GET", f"/stats?project_root={self.project_root}")
            if result.get("success"):
                stats = result.get("statistics", {})
                _display_statistics(stats)
            else:
                self.console.print(f"[red]Stats failed:[/red] {result}")
        except Exception as e:
            self.console.print(f"[red]Stats error:[/red] {e}")
    
    async def _run_create_spec(self, name: str, description: str):
        """Create a new specification."""
        self.console.print(f"[blue]Creating specification:[/blue] {name}")
        params = {
            "project_root": str(self.project_root),
            "specification_name": name,
            "initial_description": description,
            "model": self.model,
            "provider": self.provider
        }
        
        result = await stream_sse_request("/stream/create-specification", params)
        
        if result.get("success"):
            self.current_spec_id = result.get("specification_id")
            self.current_mode = "specification"
            self.console.print(f"[green]✓ Specification created:[/green] {self.current_spec_id}")
            self.console.print("[cyan]Switched to specification mode[/cyan]")
        else:
            self.console.print("[red]Specification creation failed[/red]")
    
    async def _run_list_specs(self):
        """List all specifications."""
        try:
            result = make_request("GET", "/specifications")
            specs = result.get("specifications", {})
            
            if not specs:
                self.console.print("[yellow]No specifications found[/yellow]")
                return
            
            spec_table = Table(title="📝 Specifications")
            spec_table.add_column("ID", style="cyan")
            spec_table.add_column("Name", style="green")
            spec_table.add_column("Ready for Contracts", style="yellow")
            
            for spec_id, spec in specs.items():
                ready = "✓" if spec.get("ready_for_contracts", False) else "✗"
                spec_table.add_row(spec_id, spec.get("name", "Unknown"), ready)
            
            self.console.print(spec_table)
        except Exception as e:
            self.console.print(f"[red]List specs error:[/red] {e}")
    
    async def _run_show_spec(self, spec_id: str):
        """Show specification details."""
        try:
            result = make_request("GET", f"/specification/{spec_id}")
            
            self.console.print(f"[blue]Specification:[/blue] {result.get('name', 'Unknown')}")
            self.console.print(f"[cyan]ID:[/cyan] {spec_id}")
            self.console.print(f"[cyan]Project:[/cyan] {result.get('project_root', 'Unknown')}")
            self.console.print(f"[cyan]Ready for Contracts:[/cyan] {'✓' if result.get('ready_for_contracts', False) else '✗'}")
            self.console.print(f"[cyan]Created:[/cyan] {result.get('created_at', 'Unknown')}")
            
            # Show specification description/content
            spec_content = result.get('specification_text', '')
            if spec_content:
                self.console.print(Panel(
                    spec_content,
                    title="📝 Specification Description",
                    border_style="green"
                ))
            
            # Show conversation history
            history = result.get("conversation_history", [])
            if history:
                self.console.print(Panel(
                    _format_conversation_history(history),
                    title="💬 Conversation History",
                    border_style="blue"
                ))
            
            # Show contract descriptions if available
            contracts = result.get("contracts", {})
            if contracts:
                contract_descriptions = contracts.get("contract_descriptions", [])
                ai_analysis = contracts.get("ai_analysis", "")
                
                if ai_analysis:
                    self.console.print(Panel(
                        ai_analysis,
                        title="🤖 AI Contract Analysis",
                        border_style="cyan"
                    ))
                
                if contract_descriptions:
                    self.console.print(Panel(
                        _format_contract_descriptions(contract_descriptions),
                        title="📋 Contract Descriptions",
                        border_style="yellow"
                    ))
            
        except Exception as e:
            self.console.print(f"[red]Show spec error:[/red] {e}")
    
    async def _run_refine_spec(self, spec_id: str, response: str):
        """Refine a specification."""
        self.console.print(f"[blue]Refining specification:[/blue] {spec_id}")
        params = {
            "specification_id": spec_id,
            "user_response": response,
            "model": self.model,
            "provider": self.provider
        }
        
        result = await stream_sse_request("/stream/refine-specification", params)
        
        if result.get("success"):
            self.console.print("[green]✓ Specification refined[/green]")
            if result.get("ready_for_contracts"):
                self.console.print("[bright_green]🎉 Ready for contract generation![/bright_green]")
        else:
            self.console.print("[red]Specification refinement failed[/red]")
    
    async def _run_edit_spec(self, spec_id: str, instructions: str):
        """Edit a specification with direct AI assistance."""
        self.console.print(f"[blue]Editing specification:[/blue] {spec_id}")
        self.console.print(f"[cyan]Instructions:[/cyan] {instructions}")
        
        # Use the refine endpoint but with editing-focused instructions
        edit_prompt = f"Please modify the specification according to these instructions: {instructions}"
        
        params = {
            "specification_id": spec_id,
            "user_response": edit_prompt,
            "model": self.model,
            "provider": self.provider
        }
        
        result = await stream_sse_request("/stream/refine-specification", params)
        
        if result.get("success"):
            self.console.print("[green]✓ Specification edited successfully[/green]")
            self.console.print("[cyan]Use 'show-spec' to see the updated content[/cyan]")
        else:
            self.console.print("[red]Specification editing failed[/red]")
    
    async def _run_generate_contracts(self, spec_id: str):
        """Generate contracts from specification."""
        self.console.print(f"[blue]Generating contracts for:[/blue] {spec_id}")
        params = {
            "specification_id": spec_id,
            "model": self.model,
            "provider": self.provider
        }
        
        result = await stream_sse_request("/stream/generate-contracts", params)
        
        if result.get("success"):
            self.console.print("[green]✓ Contracts generated[/green]")
            self.current_mode = "implementation"
            self.console.print("[cyan]Switched to implementation mode[/cyan]")
        else:
            self.console.print("[red]Contract generation failed[/red]")
    
    async def _run_decompose(self, aim: str):
        """Decompose an aim."""
        self.console.print(f"[blue]Decomposing aim:[/blue] {aim}")
        try:
            data = {
                "project_root": str(self.project_root),
                "aim": aim,
                "model": self.model,
                "provider": self.provider
            }
            result = make_request("POST", "/decompose-aim", data)
            
            if result.get("success"):
                self.console.print("[green]✓ Decomposition completed[/green]")
                
                subcontracts = result.get("subcontracts", [])
                if subcontracts:
                    self.console.print(Panel(
                        _format_subcontracts(subcontracts),
                        title="🔧 Subcontracts",
                        border_style="green"
                    ))
            else:
                self.console.print(f"[red]Decomposition failed:[/red] {result}")
        except Exception as e:
            self.console.print(f"[red]Decompose error:[/red] {e}")
    
    async def _run_generate(self, aim: str):
        """Generate contracts for an aim."""
        self.console.print(f"[blue]Generating contracts for:[/blue] {aim}")
        try:
            data = {
                "project_root": str(self.project_root),
                "aim": aim,
                "model": self.model,
                "provider": self.provider
            }
            result = make_request("POST", "/generate-contracts", data)
            
            if result.get("success"):
                self.console.print("[green]✓ Generation completed[/green]")
                
                contracts = result.get("generated_contracts", [])
                if contracts:
                    self.console.print(Panel(
                        _format_contracts(contracts),
                        title="📝 Generated Contracts",
                        border_style="green"
                    ))
            else:
                self.console.print(f"[red]Generation failed:[/red] {result}")
        except Exception as e:
            self.console.print(f"[red]Generate error:[/red] {e}")
    
    async def _run_refactor(self):
        """Run refactoring analysis."""
        self.console.print("[blue]Analyzing refactoring opportunities...[/blue]")
        try:
            data = {
                "project_root": str(self.project_root),
                "model": self.model,
                "provider": self.provider
            }
            result = make_request("POST", "/refactor", data)
            
            if result.get("success"):
                self.console.print("[green]✓ Refactor analysis completed[/green]")
                
                suggestions = result.get("refactoring_suggestions", [])
                if suggestions:
                    self.console.print(Panel(
                        _format_refactor_suggestions(suggestions),
                        title="🔧 Refactoring Suggestions",
                        border_style="green"
                    ))
            else:
                self.console.print(f"[red]Refactor analysis failed:[/red] {result}")
        except Exception as e:
            self.console.print(f"[red]Refactor error:[/red] {e}")
    
    async def _run_show_hierarchy(self, spec_id: str):
        """Show specification hierarchy."""
        try:
            result = make_request("GET", f"/specification/{spec_id}/hierarchy")
            
            spec_name = result.get("name", "Unknown")
            self.console.print(f"[blue]Specification Hierarchy:[/blue] {spec_name}")
            
            spec_type = result.get("type", "monolithic")
            if spec_type == "composite":
                self.console.print(f"[cyan]Type:[/cyan] Composite (has components)")
                
                components = result.get("components", [])
                if components:
                    hierarchy_table = Table(title="🧩 Components")
                    hierarchy_table.add_column("Component ID", style="cyan")
                    hierarchy_table.add_column("Name", style="green")
                    hierarchy_table.add_column("Ready for Contracts", style="yellow")
                    hierarchy_table.add_column("Last Sync", style="dim")
                    
                    for comp in components:
                        ready = "✓" if comp.get("ready_for_contracts", False) else "✗"
                        last_sync = comp.get("last_sync", "Never")
                        if last_sync != "Never":
                            last_sync = last_sync.split("T")[0]  # Just the date
                        
                        hierarchy_table.add_row(
                            comp.get("id", "Unknown"),
                            comp.get("name", "Unknown"),
                            ready,
                            last_sync
                        )
                    
                    self.console.print(hierarchy_table)
                
                dependencies = result.get("dependencies", {})
                if dependencies:
                    self.console.print(Panel(
                        "\n".join(f"• {comp} depends on: {', '.join(deps)}" for comp, deps in dependencies.items()),
                        title="🔗 Dependencies",
                        border_style="blue"
                    ))
            else:
                self.console.print(f"[cyan]Type:[/cyan] Monolithic (no components)")
                self.console.print("[dim]Use 'analyze-decomposition' to explore decomposition opportunities[/dim]")
            
        except Exception as e:
            self.console.print(f"[red]Error showing hierarchy:[/red] {e}")
    
    async def _run_analyze_decomposition(self, spec_id: str):
        """Analyze decomposition opportunities."""
        self.console.print(f"[blue]Analyzing decomposition opportunities for:[/blue] {spec_id}")
        
        params = {
            "specification_id": spec_id,
            "model": self.model,
            "provider": self.provider
        }
        
        result = await stream_sse_request("/stream/analyze-decomposition", params)
        
        if result.get("success"):
            self.console.print(f"[green]✓ Analysis completed[/green]")
            
            opportunities = result.get("decomposition_opportunities", [])
            if opportunities:
                self.console.print(Panel(
                    "\n".join(f"• {opp}" for opp in opportunities),
                    title="🔍 Decomposition Opportunities",
                    border_style="green"
                ))
            
            suggested_components = result.get("suggested_components", [])
            if suggested_components:
                self.console.print(Panel(
                    "\n".join(f"• {comp}" for comp in suggested_components),
                    title="🧩 Suggested Components",
                    border_style="blue"
                ))
                
                self.console.print(f"[cyan]Use 'decompose {', '.join(suggested_components[:3])}' to proceed[/cyan]")
        else:
            self.console.print("[red]Analysis failed[/red]")
    
    async def _run_decompose_interactive(self, spec_id: str):
        """Run interactive decomposition with component preview and approval."""
        self.console.print(f"[blue]Starting interactive decomposition for:[/blue] {spec_id}")
        self.console.print("[dim]AI will analyze and suggest components for your approval[/dim]")
        
        params = {
            "specification_id": spec_id,
            "model": self.model,
            "provider": self.provider
        }
        
        result = await stream_sse_request("/stream/decompose-interactive", params)
        
        if result.get("success"):
            self.console.print(f"[green]✓ Component analysis completed[/green]")
            
            component_suggestions = result.get("component_suggestions", [])
            if component_suggestions:
                self.console.print(Panel(
                    f"Found {len(component_suggestions)} component suggestions",
                    title="🔍 Analysis Complete",
                    border_style="green"
                ))
                
                # Start interactive approval process
                approved_components = []
                
                for i, suggestion in enumerate(component_suggestions, 1):
                    self.console.print(f"\n[bold blue]Component {i} of {len(component_suggestions)}[/bold blue]")
                    
                    # Show component preview
                    _show_component_preview(suggestion)
                    
                    # Get user decision
                    decision = _get_component_decision(suggestion)
                    
                    if decision == "approved":
                        approved_components.append(suggestion)
                        self.console.print(f"[green]✓ Approved: {suggestion['name']}[/green]")
                    elif decision == "edited":
                        approved_components.append(suggestion)
                        self.console.print(f"[green]✓ Approved (edited): {suggestion['name']}[/green]")
                    else:
                        self.console.print(f"[yellow]✗ Skipped: {suggestion['name']}[/yellow]")
                
                # Create approved components
                if approved_components:
                    self.console.print(f"\n[cyan]Creating {len(approved_components)} approved components...[/cyan]")
                    _create_approved_components(spec_id, approved_components, self.model, self.provider)
                else:
                    self.console.print("[yellow]No components were approved for creation[/yellow]")
            else:
                self.console.print("[yellow]No component suggestions were generated[/yellow]")
        else:
            self.console.print("[red]Interactive decomposition failed[/red]")

    async def _run_decompose_spec(self, spec_id: str, component_names: str):
        """Decompose specification into components (batch mode)."""
        self.console.print(f"[blue]Decomposing specification:[/blue] {spec_id}")
        self.console.print(f"[cyan]Components:[/cyan] {component_names}")
        
        params = {
            "specification_id": spec_id,
            "component_names": component_names,
            "model": self.model,
            "provider": self.provider
        }
        
        result = await stream_sse_request("/stream/decompose-specification", params)
        
        if result.get("success"):
            self.console.print(f"[green]✓ Specification decomposed successfully[/green]")
            
            components = result.get("created_components", [])
            if components:
                self.console.print(Panel(
                    "\n".join(f"• {comp['name']} ({comp['id']})" for comp in components),
                    title="🧩 Created Components",
                    border_style="green"
                ))
            
            self.console.print("[cyan]Use 'show-hierarchy' to see the new structure[/cyan]")
        else:
            self.console.print("[red]Decomposition failed[/red]")
    
    async def _run_create_component(self, parent_spec_id: str, component_name: str, description: str):
        """Create a new component."""
        self.console.print(f"[blue]Creating component:[/blue] {component_name}")
        self.console.print(f"[cyan]Description:[/cyan] {description}")
        
        params = {
            "parent_spec_id": parent_spec_id,
            "component_name": component_name,
            "description": description,
            "model": self.model,
            "provider": self.provider
        }
        
        result = await stream_sse_request("/stream/create-component", params)
        
        if result.get("success"):
            component_id = result.get("component_id")
            self.console.print(f"[green]✓ Component created:[/green] {component_id}")
            self.console.print(f"[cyan]Use 'refine-component {component_id} \"your input\"' to refine it[/cyan]")
        else:
            self.console.print("[red]Component creation failed[/red]")
    
    async def _run_refine_component(self, parent_spec_id: str, component_id: str, response: str):
        """Refine a component with parent synchronization."""
        self.console.print(f"[blue]Refining component:[/blue] {component_id}")
        self.console.print(f"[cyan]Input:[/cyan] {response}")
        
        params = {
            "parent_spec_id": parent_spec_id,
            "component_id": component_id,
            "user_response": response,
            "model": self.model,
            "provider": self.provider
        }
        
        result = await stream_sse_request("/stream/refine-component", params)
        
        if result.get("success"):
            self.console.print(f"[green]✓ Component refined with parent sync[/green]")
            
            sync_summary = result.get("sync_summary", {})
            if sync_summary:
                self.console.print(Panel(
                    f"Component: {sync_summary.get('component_changes', 'No changes')}\n"
                    f"Parent: {sync_summary.get('parent_changes', 'No changes')}\n"
                    f"Conflicts: {sync_summary.get('conflicts', 'None')}",
                    title="🔄 Sync Summary",
                    border_style="cyan"
                ))
            
            ready_for_contracts = result.get("ready_for_contracts", False)
            if ready_for_contracts:
                self.console.print("[bright_green]🎉 Component is ready for contract generation![/bright_green]")
        else:
            self.console.print("[red]Component refinement failed[/red]")
    
    async def _run_sync_status(self, spec_id: str):
        """Check synchronization status."""
        try:
            result = make_request("GET", f"/specification/{spec_id}/sync-status")
            
            self.console.print(f"[blue]Sync Status for:[/blue] {result.get('name', 'Unknown')}")
            
            overall_status = result.get("overall_status", "unknown")
            status_color = {
                "synced": "green",
                "pending": "yellow", 
                "conflicts": "red",
                "unknown": "dim"
            }.get(overall_status, "white")
            
            self.console.print(f"[{status_color}]Overall Status:[/{status_color}] {overall_status}")
            
            components = result.get("components", [])
            if components:
                sync_table = Table(title="🔄 Component Sync Status")
                sync_table.add_column("Component", style="cyan")
                sync_table.add_column("Status", style="white")
                sync_table.add_column("Last Sync", style="dim")
                sync_table.add_column("Pending", style="yellow")
                
                for comp in components:
                    status = comp.get("sync_status", "unknown")
                    last_sync = comp.get("last_sync", "Never")
                    if last_sync != "Never":
                        last_sync = last_sync.split("T")[0]
                    
                    pending = str(comp.get("pending_changes", 0))
                    
                    sync_table.add_row(
                        comp.get("name", "Unknown"),
                        status,
                        last_sync,
                        pending
                    )
                
                self.console.print(sync_table)
            
            conflicts = result.get("conflicts", [])
            if conflicts:
                self.console.print(Panel(
                    "\n".join(f"• {conflict}" for conflict in conflicts),
                    title="⚠️ Conflicts",
                    border_style="red"
                ))
            
        except Exception as e:
            self.console.print(f"[red]Error checking sync status:[/red] {e}")
    
    async def run(self):
        """Run the interactive session."""
        self.console.print("[bold green]🦎 Welcome to Axiomander Interactive Mode![/bold green]")
        self.console.print("[dim]Type '/help' for commands or just chat naturally with AI[/dim]")
        self.console.print("[dim]Commands start with '/' - everything else is conversation[/dim]")
        
        if self.readline_available:
            self.console.print("[dim]✓ TAB completion enabled[/dim]\n")
        else:
            self.console.print("[dim]⚠ TAB completion not available (readline module missing)[/dim]\n")
        
        self.display_status()
        self.console.print()
        
        # Show mode-specific welcome message
        mode_welcome = self._get_mode_welcome_message()
        if mode_welcome:
            self.console.print(Panel(
                mode_welcome,
                title=f"🎯 {self.current_mode.title()} Mode",
                border_style="green"
            ))
        
        self.console.print("\n[dim]💡 Try saying something like:[/dim]")
        example_inputs = self._get_mode_example_inputs()
        for example in example_inputs:
            self.console.print(f"[dim]  • {example}[/dim]")
        self.console.print(f"[dim]  • /help (for commands)[/dim]")
        
        while self.session_active:
            try:
                # Get user input with readline support for tab completion
                mode_indicator = f"[{self.current_mode}]"
                if self.readline_available:
                    try:
                        # Use readline-compatible prompt with proper escape sequences
                        # \001 and \002 tell readline that the enclosed characters are non-printing
                        colored_mode = f"\001\033[1;33m\002{mode_indicator}\001\033[0m\002"
                        colored_prompt = f"\001\033[1;36m\002axiomander>\001\033[0m\002"
                        prompt = f"\n{colored_mode} {colored_prompt} "
                        user_input = input(prompt)
                    except (EOFError, KeyboardInterrupt):
                        if self._confirm_exit():
                            break
                        else:
                            continue
                else:
                    # Fallback to Rich prompt if readline not available
                    user_input = Prompt.ask(f"\n[bold yellow]{mode_indicator}[/bold yellow] [bold cyan]axiomander>[/bold cyan]", console=self.console)
                
                if not user_input.strip():
                    continue
                
                # Check if input is a command (starts with /) or natural conversation
                if user_input.startswith('/'):
                    # Handle as command
                    command_input = user_input[1:]  # Remove the /
                    parts = command_input.strip().split()
                    if parts:
                        command = parts[0].lower()
                        args = parts[1:] if len(parts) > 1 else []
                        await self.execute_command(command, args)
                    else:
                        self.console.print("[yellow]Empty command. Type '/help' for available commands.[/yellow]")
                else:
                    # Handle as natural conversation with AI
                    await self.handle_conversation(user_input)
                
            except KeyboardInterrupt:
                if self._confirm_exit():
                    break
                else:
                    continue
            except EOFError:
                break
        
        self.console.print("[green]Session ended. Goodbye! 🦎[/green]")
    
    def _show_completion_help(self):
        """Show detailed tab completion help."""
        help_text = """
[bold blue]Interactive Mode Guide[/bold blue]

[cyan]Two Ways to Interact:[/cyan]
• [bold]Natural Conversation:[/bold] Just type normally - AI will understand and help
• [bold]Commands:[/bold] Start with '/' for explicit commands

[cyan]Commands (start with /):[/cyan] Press TAB after typing partial command names
  Example: [dim]/hel<TAB> → /help[/dim]

[cyan]Specification IDs:[/cyan] Press TAB when commands expect spec IDs
  Commands: [dim]/select-spec, /show-spec, /refine, /generate-contracts[/dim]
  Example: [dim]/select-spec spec_<TAB> → spec_20241202_231752_9210[/dim]

[cyan]Model Names:[/cyan] Press TAB for model completion
  Command: [dim]/model[/dim]
  Example: [dim]/model son<TAB> → sonnet[/dim]

[cyan]Conversation Examples:[/cyan]
• "What functions need contracts in my project?"
• "Help me specify user authentication behavior"
• "How should I handle validation errors?"
• "Generate contracts for my specification"

[yellow]Tips:[/yellow]
• Use '/' for commands, natural language for conversation
• AI understands context and can perform actions
• Press TAB twice to see all available completions
• Each mode has a specialized AI assistant
"""
        self.console.print(Panel(help_text.strip(), title="💡 Interactive Mode Help", border_style="blue"))
    
    def _show_completion_debug(self):
        """Show completion debug information."""
        spec_ids = self._get_available_spec_ids()
        
        debug_text = f"""
[bold blue]Completion Debug Information[/bold blue]

[cyan]Available Specification IDs:[/cyan] {len(spec_ids)}
"""
        
        if spec_ids:
            debug_text += "\n".join(f"  • {spec_id}" for spec_id in spec_ids[:10])
            if len(spec_ids) > 10:
                debug_text += f"\n  ... and {len(spec_ids) - 10} more"
        else:
            debug_text += "  [dim]No specifications found[/dim]"
        
        debug_text += f"""

[cyan]Specs Directory:[/cyan] {Path('.axiomander/specs').exists()}
[cyan]Current Directory:[/cyan] {Path('.').resolve()}
[cyan]Readline Available:[/cyan] {self.readline_available}
"""
        
        self.console.print(Panel(debug_text.strip(), title="🐛 Debug Info", border_style="yellow"))
    
    def _get_mode_welcome_message(self) -> str:
        """Get welcome message for current mode."""
        if self.current_mode == "exploration":
            return """I'll help you explore your codebase and identify opportunities for design-by-contract programming.

Ask me about:
• Analyzing your project structure
• Finding functions that need contracts
• Understanding contract coverage
• Planning specification work"""

        elif self.current_mode == "specification":
            if self.current_spec_id:
                return f"""I'll help you refine the specification: {self.current_spec_id}

We can discuss:
• Clarifying requirements and edge cases
• Defining expected behaviors
• Identifying error conditions
• Preparing for contract generation"""
            else:
                return """I'll help you create and refine behavioral specifications.

We can:
• Create new specifications
• Select existing ones to work on
• Discuss requirements and behaviors
• Plan contract structures"""

        elif self.current_mode == "refinement":
            return """I'll help you decompose high-level aims into manageable components.

We can work on:
• Breaking down complex requirements
• Designing system architecture
• Planning implementation phases
• Identifying key contracts"""

        elif self.current_mode == "implementation":
            return """I'll help you implement contracts and refactor code.

We can focus on:
• Writing actual contract code
• Refactoring for better contracts
• Implementing specifications
• Debugging contract issues"""

        return ""
    
    def _get_mode_example_inputs(self) -> List[str]:
        """Get example inputs for current mode."""
        if self.current_mode == "exploration":
            return [
                "What functions in my project need contracts?",
                "Analyze my codebase for contract opportunities",
                "Show me the current contract coverage"
            ]
        elif self.current_mode == "specification":
            if self.current_spec_id:
                return [
                    "What happens when the input is invalid?",
                    "How should errors be handled?",
                    "This specification is getting complex - should I break it into components?",
                    "/analyze-decomposition (analyze for component opportunities)",
                    "/decompose authentication,validation,business_logic (break into components)",
                    "/decompose-interactive (interactive component creation with preview)",
                    "/show-hierarchy (see component structure)"
                ]
            else:
                return [
                    "I want to specify user authentication behavior",
                    "Create a specification for data validation",
                    "Help me work on an existing specification"
                ]
        elif self.current_mode == "refinement":
            return [
                "Break down 'user management system' into components",
                "How should I structure a payment processing system?",
                "What contracts do I need for a REST API?"
            ]
        elif self.current_mode == "implementation":
            return [
                "Help me implement contracts for user validation",
                "How do I refactor this function to use contracts?",
                "Generate tests for my contract specifications"
            ]
        return ["How can you help me?"]
    
    def _confirm_exit(self) -> bool:
        """Confirm exit with the user."""
        try:
            return Confirm.ask("\n[yellow]Exit interactive mode?[/yellow]", console=self.console)
        except (KeyboardInterrupt, EOFError):
            return True


@app.command()
def interactive():
    """Start interactive mode for contextual AI-powered development."""
    session = InteractiveSession()
    asyncio.run(session.run())


def main():
    """Main entry point for the CLI."""
    app()


if __name__ == "__main__":
    main()
