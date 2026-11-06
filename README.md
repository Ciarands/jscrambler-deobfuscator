# jscrambler-deobfuscator

Deobfuscator for JavaScript protected with Jscrambler. Works as a CLI and as a library.

## Handles

- control flow flattening
- string revealing
- resolving global object proxying
- inlining steps
  * setup aliases
  * wrapper functions
  * call aliases
  * arguments arrays
  * storage object aliases
- code lock removal
- anti-debug detection removal
- domain lock removal
- opaque predicates
  * hash variant
  * matrix variant
- calculator object resolution
- runtime removal (storage object, decoder, setup and wrapperss)
- beautification
- constant folding
- dead code elimination (DCE)
- declaration sinking

## Requirements

- Node 22.12 or newer to build from source
- (optional) Docker

## Install

### - Build from source:

```
git clone https://github.com/Ciarands/jscrambler-deobfuscator
cd jscrambler-deobfuscator
npm install
npm run build
npm link
```

### - Docker:

```
docker pull ghcr.io/ciarands/jsd
docker run --rm -v "$PWD:/work" ghcr.io/ciarands/jsd input.js -o output.js
```

To use as `jsd`, add an alias.

> bash/zsh:

```
alias jsd='docker run --rm -i -u "$(id -u):$(id -g)" -v "$PWD:/work" ghcr.io/ciarands/jsd'
```

> PowerShell:

```
function jsd { docker run --rm -i -v "${PWD}:/work" ghcr.io/ciarands/jsd @args }
```

## CLI

```
jsd input.js -o output.js
```

| Option | |
|---|---|
| `-o, --output <path>` | output file, or output folder when the input is a folder |
| `-f, --force` | overwrite existing output |
| `--passes <list>` | only run these passes |
| `--skip <list>` | skip these passes |
| `--list-passes` | list the passes and exit |
| `--report <file>` | write a JSON report |
| `--dump-dir <dir>` | write the code after every pass |
| `-v, --verbose` | say what each pass did, `-vv` for every decision with source locations |
| `-q, --quiet` | only print errors |

## Library

```js
import { deobfuscate } from "jscrambler-deobfuscator";

const { code, report } = await deobfuscate(source);
```

Options:

- `passes` / `skip`: pick which passes run
- `logger`: anything with `error`, `warn`, `info` and `debug` methods, or `createLogger(level, write)`. Silent by default
- `filename`: used in log messages
- `afterPass(report, code)`: called after each pass with the code so far

`deobfuscate` throws `ParseError` if the input doesn't parse and `UnknownPassError` for a pass name that doesn't exist.

## Limitations

- Large files take a while. A 2.7 MB script takes around 15 seconds.
- Anything it can't prove is left as it was, so some code may stay obfuscated.

## Development

```
npm install
npm run check
npm run build
```
