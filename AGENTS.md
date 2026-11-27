# AGENTS.md

## Setup commands

- `lake update -R --keep-toolchain` followed by `lake build`

## Coding Process

- After changes to the game's English text, `lake build` should be called and you should validate
  that the changes are present in `.i18n/en/Game.pot`.
- Translations: simple text changes can be directly applied to all languages simultaneously.
  However, larger changes in wording should not be made to all translations at once.
  Instead, updating the translations should be left to a dedicated translator of the language.

## Commits and Merge Requests

- do not add the agent as a coauthor of the commit. Concretely, do not add `Co-authored-by` to
  denote which agent was involved.
