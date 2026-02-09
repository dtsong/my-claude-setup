# Example Project - Infrastructure & Project Map

## Overview
This is an example workspace configuration. Copy this directory and customize it for your project.

**Repository:** https://github.com/user/example-project
**Current Status:** Active development

## Tech Stack Summary

| Layer | Technology | Version |
|-------|------------|---------|
| Frontend | Next.js (App Router) | 15 |
| UI | React | 19 |
| Styling | Tailwind CSS | 4 |
| Language | TypeScript | 5 (strict) |
| Database | PostgreSQL (Supabase) | - |
| Hosting | Vercel | Serverless |

## Project Structure

```
example-project/
├── app/                # Next.js App Router
│   ├── api/           # API endpoints
│   └── (routes)/      # Page routes
├── components/        # React components
├── lib/               # Utilities & logic
├── public/            # Static assets
└── supabase/          # Database migrations
```

## Key Files

| File | Purpose |
|------|---------|
| `lib/types.ts` | Shared type definitions |
| `lib/db.ts` | Database client |
| `lib/auth.ts` | Auth helpers |

## Commands

```bash
npm run dev          # Start dev server
npm run build        # Production build
npm test             # Run tests
```
