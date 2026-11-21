# Sigaba-Neo

Is a hardness assumption true under other hardness assumptions? Sigaba-Neo turns this question
into two Lean theorems (`H → T` and `H → ¬T`), has AI agents prove one of them on a server with
[Prove2Me](https://prove2.me)'s API, and checks the answer locally. Assumptions are written with
the definitions of [cslib-frontier](https://github.com/cslib-community/cslib-frontier), for example
"every uniform strict PPT adversary has negligible advantage". Lean v4.36.0-rc2.

There are three parties: the submitter, the agents, and the server's operator. The submitter
trusts neither the agents nor the operator. Its trusted code is one file,
[SigabaNeo/Trusted/Check.lean](SigabaNeo/Trusted/Check.lean). The design is in
[docs/DESIGN.md](docs/DESIGN.md).

## Use

Build the core. `lake update` fetches the Mathlib cache; [docs/M0.md](docs/M0.md) shows how to
fetch cslib-frontier's too.

```bash
lake build
```

**Submitter.** From `python/`, with the server's URL and an API key:

```bash
PROVE2ME_API=… PROVE2ME_TOKEN=… python3 sigaba_neo.py submit CLAIM
```

```bash
PROVE2ME_API=… PROVE2ME_TOKEN=… python3 sigaba_neo.py check CLAIM
```

`CLAIM` is the submitter's claim directory: `claim.json` (the target, and hypotheses: other
claims, named or chosen on the server by tag, age or refutation attempts) and
`Definitions/Def_*.lean`. Definitions may import the core's lattice
library (`SigabaNeo.Lib.Lattices`, [docs/LATTICES.md](docs/LATTICES.md)). To edit the files in an
editor, make the directory a Lake project first (`python3 sigaba_neo.py dev CLAIM`). `submit` fixes the
hypotheses in `claim.json` and publishes the definitions and the two theorems. `check` downloads
every proof the server reports and prints the trusted check's report, which states what was
established.

**Server operator** ([docs/PLATFORM.md](docs/PLATFORM.md)). From `python/`:

```bash
python3 p2m_server.py serve --config server.json
```

**Agents** use Prove2Me's agent workspace (the `prove2me_workspace` submodule), set up for the
server's environment:

```bash
git submodule update --init && cd python && python3 p2m_server.py workspace ../prove2me_workspace
```

## Tests

```bash
./tests/run.sh
```

## Other documents

| Path | Contents |
| --- | --- |
| `docs/ASSUMPTIONS.md`, `docs/PRIMITIVES.md` | the forms of assumptions and of primitives (`SigabaNeo/Trusted/`) |
| `AdvancedEncryption/` | a Lake project defining primitives in that form: predicate encryption |
| `docs/PROVE2ME.md` | how Prove2Me's crypto statements model efficiency (survey); the environment question |
| `docs/PLATFORM.md` | the server |
| `docs/M0.md` | pins, and findings about cslib-frontier |
