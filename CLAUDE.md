# Claude Code Configuration

This file contains configuration and commands for Claude Code to work effectively with this project.

## Build Commands

To check for broken links and build the project:

```bash
pnpm run build
```

To re-format markdown files after editing them, run:

```bash
pnpm run fmt
```

## Project Structure

This is a VuePress documentation site for a systems verification course. The main content is in:

- `docs/notes/` - Course notes and lectures
- `docs/assignments/` - Course assignments
- `docs/program-proofs/demos/` - Program proof demonstrations

## Common Tasks

- **Fix broken links**: Run `pnpm run build` to identify broken links, then update the file paths accordingly
- **Add new content**: Follow the existing structure and markdown format
- **Verify changes**: Always run the build command after making changes to ensure no broken links

## Development Notes

- The site uses VuePress with a links checker plugin that validates all internal links
- Auto-generated files should not be edited directly (marked with "Auto-generated from literate source. DO NOT EDIT")
