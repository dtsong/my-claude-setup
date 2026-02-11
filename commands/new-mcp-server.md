# New MCP Server Setup

Initialize an MCP server with opinionated tooling (TypeScript, Zod, pnpm, Vitest).

## Stack

- **Language**: TypeScript (preferred for SDK quality)
- **Validation**: Zod
- **Transport**: STDIO (local) or Streamable HTTP (remote)
- **Package manager**: pnpm
- **Testing**: Vitest

## Setup Steps

1. Initialize:
```bash
mkdir <server-name>-mcp && cd <server-name>-mcp
pnpm init
```

2. Add dependencies:
```bash
pnpm add @modelcontextprotocol/sdk zod
pnpm add -D typescript @types/node vitest
```

3. Create `tsconfig.json`:
```json
{
  "compilerOptions": {
    "target": "ES2022",
    "module": "NodeNext",
    "moduleResolution": "NodeNext",
    "strict": true,
    "noUncheckedIndexedAccess": true,
    "esModuleInterop": true,
    "skipLibCheck": true,
    "outDir": "dist",
    "rootDir": "src"
  },
  "include": ["src"]
}
```

4. Create `src/index.ts` scaffold:
```typescript
import { McpServer } from "@modelcontextprotocol/sdk/server/mcp.js";
import { StdioServerTransport } from "@modelcontextprotocol/sdk/server/stdio.js";
import { z } from "zod";

const server = new McpServer({
  name: "<server-name>",
  version: "0.1.0",
});

// Register tools
server.tool(
  "example_tool",
  "Description of what this tool does",
  {
    param: z.string().describe("Parameter description"),
  },
  async ({ param }) => {
    return {
      content: [{ type: "text", text: `Result: ${param}` }],
    };
  }
);

// Start server
const transport = new StdioServerTransport();
await server.connect(transport);
```

5. Add scripts to `package.json`:
```json
{
  "type": "module",
  "bin": {
    "<server-name>-mcp": "dist/index.js"
  },
  "scripts": {
    "build": "tsc",
    "dev": "tsc --watch",
    "test": "vitest",
    "inspect": "npx @anthropic-ai/mcp-inspector dist/index.js"
  }
}
```

6. Create project CLAUDE.md:
```markdown
# <Server Name> MCP

## Commands
pnpm build              # compile
pnpm test               # tests
pnpm inspect            # test with MCP Inspector

## Adding Tools
See src/index.ts for tool registration pattern.
Use Zod for input validation.

## Testing with Claude Code
Add to ~/.claude/mcp.json after building.
```

7. Create README.md:
```markdown
# <Server Name> MCP Server

MCP server for [purpose].

## Installation

\`\`\`bash
pnpm install
pnpm build
\`\`\`

## Usage with Claude Code

Add to `~/.claude/mcp.json`:
\`\`\`json
{
  "mcpServers": {
    "<server-name>": {
      "command": "node",
      "args": ["/path/to/<server-name>-mcp/dist/index.js"]
    }
  }
}
\`\`\`

## Tools

| Tool | Description |
|------|-------------|
| `example_tool` | Does X |
```

8. Initialize git:
```bash
git init
echo "node_modules/\ndist/" > .gitignore
git add .
git commit -m "chore: initial MCP server setup"
```

## Verification

```bash
pnpm build && pnpm inspect
```

Test tools in MCP Inspector before integrating with Claude Code.
