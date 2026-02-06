# Git Branch Naming Conventions

## Branch Prefixes

| Prefix | Use For | Example |
|--------|---------|---------|
| `feat/` | New features | `feat/dark-mode` |
| `fix/` | Bug fixes | `fix/login-validation` |
| `refactor/` | Code refactoring | `refactor/auth-module` |
| `docs/` | Documentation | `docs/api-reference` |
| `test/` | Test additions/fixes | `test/auth-coverage` |
| `chore/` | Maintenance tasks | `chore/update-deps` |
| `hotfix/` | Urgent production fixes | `hotfix/security-patch` |

## Naming Rules

1. **Use lowercase** - All branch names should be lowercase
2. **Use hyphens** - Separate words with hyphens, not underscores or spaces
3. **Be concise** - Keep names under 50 characters
4. **Be descriptive** - Names should convey the purpose

## Good Examples

```
feat/user-authentication
feat/dark-mode-toggle
fix/login-form-validation
fix/memory-leak-theme-hook
refactor/api-client
docs/installation-guide
test/unit-auth-module
chore/upgrade-react-19
hotfix/xss-vulnerability
```

## Bad Examples

```
feature/Add_New_User_Auth    # Uppercase, underscores
my-branch                    # No prefix, unclear purpose
fix                          # Too vague
feat/implement-the-new-user-authentication-system-with-oauth  # Too long
feat/dark mode               # Contains space
```

## Including Issue Numbers

When working on a specific issue, include the number:

```
feat/123-dark-mode
fix/456-login-bug
```

This enables:
- Automatic issue linking in GitHub
- Easy tracking between issue and code
- Clear commit references

## Protected Branches

These branches have special meaning and shouldn't be used for features:

- `main` or `master` - Production code
- `develop` - Development integration
- `staging` - Pre-production testing
- `release/*` - Release preparation

## Conventional Commits

When committing to branches, use conventional commit messages:

```
feat: add dark mode toggle
fix: resolve login validation bug
docs: update API documentation
refactor: simplify auth module
test: add unit tests for auth
chore: update dependencies
```

### Breaking Changes

For breaking changes, add `!` or use `BREAKING CHANGE:` in footer:

```
feat!: change API response format

BREAKING CHANGE: The API now returns objects instead of arrays
```

## Related Workflows

- `/git-branch` - Create branches with naming validation
- `/commit` - Create commits with conventional messages
- `/gh-issue` - Link branches to issues
