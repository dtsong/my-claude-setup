## Contents

- [httpx Client Patterns](#httpx-client-patterns)
  - [Configured Client (Recommended Base)](#configured-client-recommended-base)
  - [Context Manager Usage](#context-manager-usage)
- [Pagination Patterns](#pagination-patterns)
  - [Cursor-Based Pagination](#cursor-based-pagination)
  - [Offset-Based Pagination](#offset-based-pagination)
  - [Link Header Pagination (GitHub-Style)](#link-header-pagination-github-style)
- [Rate Limiting](#rate-limiting)
  - [Token Bucket Rate Limiter](#token-bucket-rate-limiter)
  - [Retry-After Header Handling](#retry-after-header-handling)
- [Async Extraction](#async-extraction)
  - [Concurrent Fetching with Semaphore](#concurrent-fetching-with-semaphore)
  - [Async Pagination](#async-pagination)
- [Complete Extraction Pipeline](#complete-extraction-pipeline)
- [Testing Extraction Code](#testing-extraction-code)

---

# Extraction Patterns Reference

> Production API extraction patterns with httpx, async, pagination, and rate limiting. Part of the [Python Data Engineering Skill](../SKILL.md).

---

## httpx Client Patterns

### Configured Client (Recommended Base)

```python
import httpx
import os
from typing import Any

class APIClient:
    """
    Base API client with standard configuration.

    Subclass and add endpoint-specific methods.
    """

    # ── Credential boundary ──────────────────────────────────────
    # Configure: export API_BASE_URL="https://api.example.com/v1"
    # Configure: export API_KEY="your-api-key"
    # ─────────────────────────────────────────────────────────────

    def __init__(
        self,
        base_url: str | None = None,
        api_key: str | None = None,
        timeout: float = 30.0,
    ):
        self.client = httpx.Client(
            base_url=base_url or os.environ["API_BASE_URL"],
            headers={
                "Authorization": f"Bearer {api_key or os.environ['API_KEY']}",
                "Content-Type": "application/json",
            },
            timeout=timeout,
            follow_redirects=True,
        )

    def get(self, path: str, params: dict | None = None) -> dict:
        response = self.client.get(path, params=params)
        response.raise_for_status()
        return response.json()

    def close(self):
        self.client.close()

    def __enter__(self):
        return self

    def __exit__(self, *args):
        self.close()
```

### Context Manager Usage

```python
with APIClient() as client:
    users = client.get("/users", params={"limit": 100})
    orders = client.get("/orders", params={"status": "active"})
# Client automatically closed
```

---

## Pagination Patterns

### Cursor-Based Pagination

```python
from typing import Iterator

def paginate_cursor(
    client: APIClient,
    path: str,
    params: dict | None = None,
    cursor_field: str = "next_cursor",
    data_field: str = "data",
    limit: int = 100,
) -> Iterator[dict]:
    """Generic cursor-based pagination."""
    params = {**(params or {}), "limit": limit}
    cursor = None

    while True:
        if cursor:
            params["cursor"] = cursor

        response = client.get(path, params=params)
        items = response.get(data_field, [])

        yield from items

        cursor = response.get(cursor_field)
        if not cursor or not items:
            break
```

### Offset-Based Pagination

```python
def paginate_offset(
    client: APIClient,
    path: str,
    params: dict | None = None,
    data_field: str = "results",
    total_field: str = "total",
    limit: int = 100,
) -> Iterator[dict]:
    """Generic offset-based pagination."""
    params = {**(params or {}), "limit": limit}
    offset = 0

    while True:
        params["offset"] = offset
        response = client.get(path, params=params)
        items = response.get(data_field, [])

        yield from items

        total = response.get(total_field, 0)
        offset += limit
        if offset >= total or not items:
            break
```

### Link Header Pagination (GitHub-Style)

```python
def paginate_link_header(
    client: httpx.Client,
    url: str,
    params: dict | None = None,
) -> Iterator[dict]:
    """Paginate using Link header (RFC 5988)."""
    while url:
        response = client.get(url, params=params)
        response.raise_for_status()

        yield from response.json()

        # Parse Link header for next URL
        links = response.headers.get("Link", "")
        url = None
        params = None  # Params are in the next URL
        for part in links.split(","):
            if 'rel="next"' in part:
                url = part.split(";")[0].strip().strip("<>")
                break
```

---

## Rate Limiting

### Token Bucket Rate Limiter

```python
import time
import threading

class RateLimiter:
    """Token bucket rate limiter."""

    def __init__(self, requests_per_second: float):
        self.rate = requests_per_second
        self.tokens = requests_per_second
        self.last_refill = time.monotonic()
        self.lock = threading.Lock()

    def acquire(self):
        """Block until a token is available."""
        while True:
            with self.lock:
                now = time.monotonic()
                elapsed = now - self.last_refill
                self.tokens = min(self.rate, self.tokens + elapsed * self.rate)
                self.last_refill = now

                if self.tokens >= 1:
                    self.tokens -= 1
                    return

            time.sleep(1 / self.rate)

# Usage with API client
rate_limiter = RateLimiter(requests_per_second=10)

def fetch_with_rate_limit(client: APIClient, path: str) -> dict:
    rate_limiter.acquire()
    return client.get(path)
```

### Retry-After Header Handling

```python
from tenacity import retry, stop_after_attempt, wait_exponential, retry_if_exception_type
import httpx

class RateLimitedError(Exception):
    def __init__(self, retry_after: float):
        self.retry_after = retry_after

@retry(
    stop=stop_after_attempt(5),
    wait=wait_exponential(multiplier=1, min=2, max=60),
    retry=retry_if_exception_type((httpx.HTTPStatusError, RateLimitedError)),
)
def fetch_with_retry(client: httpx.Client, url: str, params: dict = None) -> dict:
    """Fetch with automatic retry on rate limit or server error."""
    response = client.get(url, params=params)

    if response.status_code == 429:
        retry_after = float(response.headers.get("Retry-After", 30))
        time.sleep(retry_after)
        raise RateLimitedError(retry_after)

    response.raise_for_status()
    return response.json()
```

---

## Async Extraction

### Concurrent Fetching with Semaphore

```python
import httpx
import asyncio
from typing import AsyncIterator

async def fetch_all_pages(
    base_url: str,
    api_key: str,
    endpoints: list[str],
    concurrency: int = 10,
) -> list[dict]:
    """Fetch multiple endpoints concurrently."""
    semaphore = asyncio.Semaphore(concurrency)

    async with httpx.AsyncClient(
        base_url=base_url,
        headers={"Authorization": f"Bearer {api_key}"},
        timeout=30.0,
    ) as client:

        async def fetch_one(endpoint: str) -> dict:
            async with semaphore:
                response = await client.get(endpoint)
                response.raise_for_status()
                return response.json()

        tasks = [fetch_one(ep) for ep in endpoints]
        results = await asyncio.gather(*tasks, return_exceptions=True)

        # Separate successes from failures
        successes = [r for r in results if not isinstance(r, Exception)]
        failures = [r for r in results if isinstance(r, Exception)]

        if failures:
            print(f"Warning: {len(failures)} requests failed")

        return successes
```

### Async Pagination

```python
async def async_paginate(
    client: httpx.AsyncClient,
    path: str,
    params: dict | None = None,
    limit: int = 100,
) -> AsyncIterator[dict]:
    """Async cursor-based pagination."""
    params = {**(params or {}), "limit": limit}
    cursor = None

    while True:
        if cursor:
            params["cursor"] = cursor

        response = await client.get(path, params=params)
        response.raise_for_status()
        data = response.json()

        for item in data.get("data", []):
            yield item

        cursor = data.get("next_cursor")
        if not cursor:
            break
```

---

## Complete Extraction Pipeline

```python
import httpx
import polars as pl
from pydantic import BaseModel
from datetime import datetime
from typing import Iterator
import os

# ── Credential boundary ──────────────────────────────────────────────
# Configure: export STRIPE_API_KEY="sk_live_xxx"
# Never inline credentials — use environment variables or secrets manager.
# ─────────────────────────────────────────────────────────────────────

class StripeCharge(BaseModel):
    id: str
    amount: int
    currency: str
    status: str
    created: int

class StripeExtractor:
    """Extract Stripe charges with pagination and validation."""

    def __init__(self, api_key: str | None = None):
        self.client = httpx.Client(
            base_url="https://api.stripe.com/v1",
            auth=(api_key or os.environ["STRIPE_API_KEY"], ""),
            timeout=30.0,
        )

    def extract_charges(self, created_gte: int | None = None) -> Iterator[StripeCharge]:
        """Extract all charges with cursor pagination."""
        params = {"limit": 100}
        if created_gte:
            params["created[gte]"] = created_gte

        while True:
            response = self.client.get("/charges", params=params)
            response.raise_for_status()
            data = response.json()

            for item in data["data"]:
                yield StripeCharge.model_validate(item)

            if not data["has_more"]:
                break
            params["starting_after"] = data["data"][-1]["id"]

    def to_polars(self, charges: Iterator[StripeCharge]) -> pl.DataFrame:
        """Convert validated charges to Polars DataFrame."""
        records = [c.model_dump() for c in charges]
        return (
            pl.DataFrame(records)
            .with_columns(
                (pl.col("amount") / 100).alias("amount_dollars"),
                pl.from_epoch("created", time_unit="s").alias("created_at"),
            )
        )

    def close(self):
        self.client.close()

# Usage
extractor = StripeExtractor()
try:
    charges = extractor.extract_charges(created_gte=1704067200)
    df = extractor.to_polars(charges)
    df.write_parquet("raw/stripe_charges.parquet")
finally:
    extractor.close()
```

---

## Testing Extraction Code

```python
import httpx
import pytest
from unittest.mock import patch

def test_stripe_pagination():
    """Test pagination follows cursor correctly."""
    mock_responses = [
        httpx.Response(200, json={
            "data": [{"id": "ch_1", "amount": 100, "currency": "usd", "status": "succeeded", "created": 1704067200}],
            "has_more": True,
        }),
        httpx.Response(200, json={
            "data": [{"id": "ch_2", "amount": 200, "currency": "usd", "status": "succeeded", "created": 1704067300}],
            "has_more": False,
        }),
    ]

    with patch.object(httpx.Client, "get", side_effect=mock_responses):
        extractor = StripeExtractor(api_key="test_key")
        charges = list(extractor.extract_charges())

    assert len(charges) == 2
    assert charges[0].id == "ch_1"
    assert charges[1].id == "ch_2"

def test_validation_rejects_bad_data():
    """Test Pydantic validation catches invalid records."""
    with pytest.raises(Exception):
        StripeCharge(id="", amount="not_a_number", currency="usd", status="bad", created=0)
```
