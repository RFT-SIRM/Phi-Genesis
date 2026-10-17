#!/usr/bin/env python3
"""Read-only latest-run monitor for the RFT-SIRM research ecosystem."""
import argparse
import json
import os
import sys
import time
import urllib.error
import urllib.request
from datetime import datetime, timezone
from pathlib import Path

REPOS = [
    ("Phi-Genesis", "RFT-SIRM/Phi-Genesis", "Spectral computation and selection audit"),
    ("UltraCore-RFT", "RFT-SIRM/UltraCore-RFT", "Research portal and ecosystem coordination"),
    ("Theory of Everything", "RFT-SIRM/Evgeny-s-Theory-of-Everything", "Dissertation and higher-moment research"),
    ("Evgeny Theorem", "RFT-SIRM/Evgeny-Theorem", "Lean 4 formalization"),
    ("Rift Network", "RFT-SIRM/Rift-Network", "Network engineering CI"),
    ("Rift-L1 Blockchain", "RFT-SIRM/Rift-L1-Blockchain", "Blockchain engineering CI"),
    ("Agave Rift Scheduler", "RFT-SIRM/agave-rift-scheduler", "Scheduler CI and fuzzing"),
    ("RFT-QPU-Sierpinski", "RFT-SIRM/RFT-QPU-Sierpinski", "Pre-experimental architecture"),
    ("RFT-Invariant-Battery", "RFT-SIRM/RFT-Invariant-Battery", "Exploratory energy-system model"),
]

def get(url):
    headers = {
        "Accept": "application/vnd.github+json",
        "X-GitHub-Api-Version": "2022-11-28",
        "User-Agent": "Phi-Genesis-Ecosystem-Control",
    }
    if os.getenv("GITHUB_TOKEN"):
        headers["Authorization"] = "Bearer " + os.environ["GITHUB_TOKEN"]
    request = urllib.request.Request(url, headers=headers)
    with urllib.request.urlopen(request, timeout=20) as response:
        return json.load(response)

def collect(label, repository, purpose):
    actions_url = "https://github.com/" + repository + "/actions"
    try:
        runs = get(
            "https://api.github.com/repos/" + repository + "/actions/runs?per_page=10"
        ).get("workflow_runs", [])
        if not runs:
            return {
                "label": label, "repository": repository, "purpose": purpose,
                "state": "NOT RUN", "detail": "No public workflow runs found",
                "url": actions_url,
            }
        run = runs[0]
        status, conclusion = run.get("status"), run.get("conclusion")
        if status != "completed":
            state = "RUNNING"
        elif conclusion == "success":
            state = "PASS"
        elif conclusion in ("failure", "timed_out", "startup_failure", "action_required"):
            state = "FAIL"
        else:
            state = (conclusion or "unknown").upper()
        return {
            "label": label, "repository": repository, "purpose": purpose,
            "state": state, "workflow": run.get("name"),
            "branch": run.get("head_branch"), "sha": (run.get("head_sha") or "")[:7],
            "updated_at": run.get("updated_at"), "url": run.get("html_url", actions_url),
            "detail": run.get("display_title") or run.get("name"),
        }
    except urllib.error.HTTPError as error:
        if error.code == 404:
            state, detail = "NOT FOUND", "Repository or Actions endpoint unavailable"
        elif error.code == 403:
            state, detail = "API LIMITED", "GitHub API rate limit or access restriction"
        else:
            state, detail = "ERROR", "GitHub API HTTP " + str(error.code)
        return {"label": label, "repository": repository, "purpose": purpose,
                "state": state, "detail": detail, "url": actions_url}
    except (urllib.error.URLError, TimeoutError, json.JSONDecodeError) as error:
        return {"label": label, "repository": repository, "purpose": purpose,
                "state": "ERROR", "detail": str(error), "url": actions_url}

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", default="ecosystem-status.json")
    parser.add_argument("--markdown", default="ecosystem-status.md")
    args = parser.parse_args()

    rows = []
    for item in REPOS:
        rows.append(collect(*item))
        time.sleep(0.15)

    report = {
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "mode": "read-only latest-run monitor",
        "note": "PASS applies only to the latest reported workflow run, not every test or the whole repository.",
        "repositories": rows,
    }
    Path(args.json).write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    lines = [
        "# Phi-Genesis — RFT-SIRM ecosystem status", "",
        f"Generated (UTC): {report['generated_at']}", "",
        "> PASS applies only to the latest reported workflow run. NOT RUN, NOT FOUND, API LIMITED and ERROR are not passes. This monitor does not dispatch tests.", "",
        "| Project | State | Latest run | Branch / SHA | Updated (UTC) |",
        "|---|---|---|---|---|",
    ]
    for row in rows:
        title = row.get("workflow", row.get("detail", "Open Actions"))
        branch_sha = f"`{row.get('branch', '—')}` / `{row.get('sha', '—')}`"
        lines.append(
            f"| [{row['label']}](https://github.com/{row['repository']}) "
            f"| **{row['state']}** | [{title}]({row['url']}) | {branch_sha} "
            f"| {row.get('updated_at') or '—'} |"
        )
    lines += [
        "", "## Evidence scope", "",
        "This report monitors public workflow runs. Each repository remains responsible for executing its own tests. Missing runs are never interpreted as success.", "",
    ]
    Path(args.markdown).write_text("\n".join(lines), encoding="utf-8")
    print("\n".join(lines))
    return 0

if __name__ == "__main__":
    sys.exit(main())
