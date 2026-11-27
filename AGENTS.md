# AGENTS.md

## Setup commands

- `lake update -R --keep-toolchain` followed by `lake build`

## Coding Process

### Translations

- After changes to the game's English text, `lake build` should be called and you should validate
  that the changes are present in `.i18n/en/Game.pot`.
- Translation updates should happen in the `.po` files and the `.json` files inside `.i18n/` should
  be generated using `lake exe i18n -e`.
- Simple text changes can be directly applied to all languages simultanously.
- For any changes which changes the structure of sentences, agents should either
  not adjust the translations or mark
  the changed translation with the `fuzzy`-attribute in the .po file.
  Concretely, this means adding a line `#, fuzzy` before the
  relevant `msgid`, so that a dedicated translator of the language
  can then easily find and validate the suggested translations.

## Commits and Merge Requests

- do not add the agent as a coauthor of the commit. Concretely, do not add `Co-authored-by` to
  denote which agent was involved.
