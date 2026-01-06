# Security Policy

## Supported Versions

Trale is currently in active development. Security updates will be provided for:

| Version | Supported          |
| ------- | ------------------ |
| main    | :white_check_mark: |

## Reporting a Vulnerability

We take security seriously. If you discover a security vulnerability in Trale, please follow these steps:

### How to Report

**Please do not report security vulnerabilities through public GitHub issues.**

Instead, please report security vulnerabilities by:
1. Opening a private security advisory on GitHub: [Report a vulnerability](https://github.com/vkuhlmann/trale/security/advisories/new)
2. Or by opening a regular issue marked as "security" if you believe the vulnerability is low risk

### What to Include

Please include the following information in your report:
- Type of vulnerability
- Full paths of source file(s) related to the vulnerability
- Location of the affected code (tag/branch/commit or direct URL)
- Step-by-step instructions to reproduce the issue
- Proof-of-concept or exploit code (if possible)
- Impact of the issue, including how an attacker might exploit it

### What to Expect

- You will receive an acknowledgment within 48 hours
- We will investigate and provide updates on the status
- Once the vulnerability is confirmed and fixed, we will coordinate disclosure with you
- We will credit you in the security advisory (unless you prefer to remain anonymous)

## Security Best Practices

When using Trale:
- Keep your Lean installation and dependencies up to date
- Review any transport lemmas you define to ensure they maintain the intended mathematical properties
- Be cautious with proof transfer when working with security-critical properties

## Scope

This security policy applies to:
- The Trale library code (`Trale/` directory)
- Documentation and examples that could affect security
- Build and CI/CD configurations

Test code (`TraleTest/`) and research code (`TraleTest/Research/`) are not covered by this security policy as they are not intended for production use.

## Attribution

Thank you to all security researchers who help keep Trale and its users safe!
