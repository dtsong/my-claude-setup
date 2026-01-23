# New TypeScript Project Setup

Initialize a TypeScript project with Daniel's preferred tooling.

## Stack

- **Runtime**: Node 22+
- **Package manager**: pnpm
- **Linting**: ESLint + TypeScript
- **Formatting**: Prettier
- **Testing**: Vitest
- **TypeScript**: Strict mode

## Setup Steps

1. Initialize:
```bash
mkdir <project-name> && cd <project-name>
pnpm init
```

2. Add TypeScript and dev deps:
```bash
pnpm add -D typescript @types/node vitest eslint prettier
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
    "noImplicitReturns": true,
    "esModuleInterop": true,
    "skipLibCheck": true,
    "outDir": "dist",
    "rootDir": "src"
  },
  "include": ["src"],
  "exclude": ["node_modules", "dist"]
}
```

4. Add scripts to `package.json`:
```json
{
  "scripts": {
    "build": "tsc",
    "dev": "tsc --watch",
    "test": "vitest",
    "lint": "eslint src",
    "typecheck": "tsc --noEmit"
  }
}
```

5. Create initial structure:
```
src/
    index.ts
tests/
    example.test.ts
```

6. Create project CLAUDE.md:
```markdown
# <Project Name>

## Commands
pnpm test        # tests
pnpm lint        # lint
pnpm typecheck   # type check
pnpm build       # compile

## Structure
src/    - source code
tests/  - vitest tests
dist/   - compiled output (gitignored)
```

7. Create `.gitignore`:
```
node_modules/
dist/
```

8. Initialize git:
```bash
git init
git add .
git commit -m "chore: initial project setup"
```

## Verification

```bash
pnpm typecheck && pnpm test
```
