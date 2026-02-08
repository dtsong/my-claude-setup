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
    "format": "prettier --write 'src/**/*.ts' 'tests/**/*.ts'",
    "typecheck": "tsc --noEmit"
  }
}
```

5. Create `.prettierrc`:
```json
{
  "semi": true,
  "singleQuote": true,
  "trailingComma": "all",
  "printWidth": 100
}
```

6. Create `.pre-commit-config.yaml`:
```yaml
repos:
  - repo: https://github.com/pre-commit/pre-commit-hooks
    rev: v5.0.0
    hooks:
      - id: trailing-whitespace
      - id: end-of-file-fixer
      - id: check-yaml
      - id: check-added-large-files

  - repo: local
    hooks:
      - id: prettier
        name: prettier
        entry: bash -c 'source ~/.nvm/nvm.sh && nvm use default --silent && npx prettier --write "$@"' --
        language: system
        types_or: [ts, tsx, js, jsx, json, css, md]

      - id: eslint
        name: eslint
        entry: bash -c 'source ~/.nvm/nvm.sh && nvm use default --silent && npx eslint --fix "$@"' --
        language: system
        types_or: [ts, tsx, js, jsx]
```

7. Create `.gitignore`:
```
node_modules/
dist/
```

8. Create initial structure:
```
src/
    index.ts
tests/
    example.test.ts
```

9. Create project CLAUDE.md:
```markdown
# <Project Name>

## Commands
```bash
pnpm test        # tests
pnpm lint        # lint
pnpm format      # format
pnpm typecheck   # type check
pnpm build       # compile
```

## Structure
src/    - source code
tests/  - vitest tests
dist/   - compiled output (gitignored)
```

10. Initialize git and install pre-commit:
```bash
git init
pre-commit install
git add .
git commit -m "chore: initial project setup"
```

## Verification

```bash
pnpm typecheck && pnpm test
```
