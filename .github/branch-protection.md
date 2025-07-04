# Branch Protection Configuration

This document outlines the required branch protection settings for the eCPU project to ensure code quality and prevent merging of failing PRs.

## Required Branch Protection Rules

### Main Branch Protection

The `main` branch should have the following protection rules enabled:

#### General Settings
- ✅ **Require a pull request before merging**
- ✅ **Require approvals**: 1 review required
- ✅ **Dismiss stale PR approvals when new commits are pushed**
- ✅ **Require review from code owners** (if CODEOWNERS file exists)

#### Status Checks
- ✅ **Require status checks to pass before merging**
- ✅ **Require branches to be up to date before merging**

**Required Status Checks:**
- `Code Quality & Linting` 
- `Unit Tests`
- `Synthesis Check`
- `Documentation Build`

#### Additional Restrictions
- ✅ **Restrict pushes that create files that are larger than 100 MB**
- ✅ **Include administrators** (admins must follow these rules too)
- ✅ **Allow force pushes**: ❌ (disabled)
- ✅ **Allow deletions**: ❌ (disabled)

## How to Configure

### Via GitHub Web Interface

1. Go to repository **Settings** → **Branches**
2. Click **Add rule** or edit existing rule for `main`
3. Configure the settings as listed above
4. Save the protection rule

### Via GitHub CLI (if available)

```bash
# Install GitHub CLI if not available
# Configure branch protection for main branch
gh api repos/:owner/:repo/branches/main/protection \
  --method PUT \
  --field required_status_checks='{"strict":true,"contexts":["Code Quality & Linting","Unit Tests","Synthesis Check","Documentation Build"]}' \
  --field enforce_admins=true \
  --field required_pull_request_reviews='{"required_approving_review_count":1,"dismiss_stale_reviews":true}' \
  --field restrictions=null
```

## Status Check Names

The following status check names must match exactly with the job names in `.github/workflows/ci.yml`:

- `Code Quality & Linting` (lint job)
- `Unit Tests` (unit-tests job) 
- `Synthesis Check` (synthesis-check job)
- `Documentation Build` (documentation job)

**Note:** The `Project Status` and `Integration Tests` jobs are not required status checks as they are either summary jobs or contain tests that are expected to be added later during development.

## Verification

After setting up branch protection:

1. Create a test branch with intentionally failing code
2. Open a PR to main
3. Verify that the PR cannot be merged when checks fail
4. Verify that the "Merge" button is disabled until all required checks pass

## Troubleshooting

### Common Issues

1. **Status check names don't match**: Ensure the required status check names exactly match the job names in the CI workflow
2. **Checks not appearing**: Push a commit to trigger the workflow and verify jobs are running
3. **Admin bypass**: Ensure "Include administrators" is enabled to prevent admins from bypassing rules

### Testing the Setup

Create a test PR that intentionally fails by:
- Adding syntactically incorrect SystemVerilog code
- Adding improperly formatted Python code  
- Breaking an existing test

The PR should show failing checks and prevent merging until fixed.