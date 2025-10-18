# Modal Effect Types in Lean 4

## Setup

Running this project requires `lake`. Run `lake build` to download dependencies and build the proofs.

For using Claude Code with a MCP for typechecking Lean 4 modules, clone `linyxus/ucw` and execute the following command.

```bash
claude mcp add lean4check -- uv --directory <some_path>/ucw/lean4check/ run lean4check --root <some_path>/met-lean4
```

