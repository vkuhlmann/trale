# Contributing to Trale

Thank you for your interest in contributing to Trale! We welcome contributions from the community.

## Getting Started

1. **Fork the repository** and clone it locally
2. **Set up the development environment** following the instructions in [README.md](README.md)
3. **Get Mathlib cache** before building: `lake exe cache get`
4. **Build the project**: `lake build`

## Ways to Contribute

### Bug Reports

If you find a bug, please open an issue with:
- A clear, descriptive title
- Steps to reproduce the issue
- Expected vs. actual behavior
- Your Lean version (from `lean-toolchain`)
- Any relevant code snippets or error messages

### Feature Requests

We welcome suggestions for new features! Please open an issue describing:
- The problem you're trying to solve
- Your proposed solution
- Any alternatives you've considered

### Code Contributions

1. **Create a branch** for your changes
2. **Make your changes**:
   - Follow the existing code style
   - Add tests for new functionality
   - Update documentation as needed
3. **Test your changes**: `lake build TraleTest`
4. **Commit with clear messages** describing your changes
5. **Open a pull request**

#### Code Style

- Use meaningful variable and function names
- Add docstrings to public definitions
- Keep functions focused and modular
- Follow existing patterns in the codebase

### Documentation

Improvements to documentation are always welcome! This includes:
- Fixing typos or unclear explanations
- Adding examples
- Improving API documentation
- Creating tutorials

## Development Guidelines

### Adding New Features

When adding new transport theorems or tactics:
1. Add the implementation in the appropriate `Trale/` subdirectory
2. Mark transport lemmas with `@[trale]` attribute
3. Add test cases in `TraleTest/`
4. Document the feature in `docs/`

### Testing

- Test files go in `TraleTest/`
- Examples should be in `TraleTest/Transfer/` or `TraleTest/Lemmas/`
- Research/experimental code goes in `TraleTest/Research/`

### Commit Messages

Use clear, descriptive commit messages:
- Start with a verb in present tense (e.g., "Add", "Fix", "Update")
- Keep the first line under 72 characters
- Add more details in the body if needed

Example:
```
Add support for List transport

- Implement R_cons and R_nil lemmas
- Add tests for list operations
- Update documentation with examples
```

## Questions?

If you have questions about contributing:
- Open an issue with the "question" label
- Check existing issues and pull requests
- Refer to the [documentation](docs/) for implementation details

## Code of Conduct

This project adheres to a code of conduct that we expect all contributors to follow. Please be respectful and constructive in all interactions.

## License

By contributing to Trale, you agree that your contributions will be licensed under the Apache License 2.0.
