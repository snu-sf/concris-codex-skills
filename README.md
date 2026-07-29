# ConCRIS Codex Skills

Codex skills for ConCRIS/Rocq proof engineering.

This repository contains three skills:

- `concris-proof`: general ConCRIS/Rocq proof engineering.
- `concris-helping-proof`: proofs involving `Helping.run`, `Helping.help`, pending jobs, and helping resources.
- `concris-tame-proof`: proofs against tame specifications such as `tame_triple` and `tame_update`.

The specialized skills track current ConCRIS development APIs. They instruct
Codex to inspect the checked-out definitions and lemma statements before using
version-specific proof patterns. Some APIs may be unavailable in older CRIS
releases or workshop snapshots.

## Install

Clone this repository, then run:

```bash
./scripts/install.sh
```

The script installs the skills by symlink into:

```bash
${CODEX_HOME:-$HOME/.codex}/skills
```

Restart Codex after installing or updating skills.

## Update

Pull the latest repository contents:

```bash
git pull
```

Because installation uses symlinks, no reinstall is needed unless the symlinks were removed.
Restart Codex after pulling updates.

## Manual Install

If you prefer not to run the script:

```bash
mkdir -p "${CODEX_HOME:-$HOME/.codex}/skills"
ln -s "$PWD/skills/concris-proof" "${CODEX_HOME:-$HOME/.codex}/skills/concris-proof"
ln -s "$PWD/skills/concris-helping-proof" "${CODEX_HOME:-$HOME/.codex}/skills/concris-helping-proof"
ln -s "$PWD/skills/concris-tame-proof" "${CODEX_HOME:-$HOME/.codex}/skills/concris-tame-proof"
```

## Notes for Maintainers

- Keep human-facing docs in this repository root, not inside individual skill folders.
- Keep each skill folder focused on files Codex should load: `SKILL.md`, `agents/openai.yaml`, and any necessary `references/`, `scripts/`, or `assets/`.

## License

MIT
