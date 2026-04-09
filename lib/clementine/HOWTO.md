# Clementine: writing and running a `.clem` protocol

This is the practical user guide. For the design rationale, see the
commit history and the long-form discussion in the project root.

## TL;DR

```bash
cd lib/clementine

# 1. Build the compiler (one-time)
cabal build clemc --flag with-sapic

# 2. Compile a .clem file
cabal run -v0 clemc --flag with-sapic -- test/Fixtures/hello.clem

# 3. Verify the resulting Tamarin theory
tamarin-prover --prove test/Fixtures/hello.clem.spthy
```

You should see:

```
analyzed: test/Fixtures/hello.clem.spthy

  executable (exists-trace): verified (2 steps)
  secrecy_s (all-traces): verified (5 steps)
  auto_sources (all-traces): verified (8 steps)
```

That's the entire pipeline: a 30-line `.clem` file ⟶ a verified
Tamarin proof of secrecy.

## Prerequisites

* **GHC + cabal.** GHC 9.14 (homebrew default on macOS) works.
  Older GHCs likely also work; they're not currently tested.
* **`tamarin-prover` binary on `$PATH`** if you want to actually
  run the proofs. Homebrew's `tamarin-prover` formula installs
  version 1.10, which is what `clemc`'s output targets.
* **Maude** (Tamarin's dependency) — comes in via `tamarin-prover`.

## Two build modes

`clemc` has two cabal flags' worth of behaviour:

### Default mode (no flag)

```bash
cabal build clemc
cabal run clemc -- path/to/file.clem
```

* Parses the `.clem` file
* Runs every wellformedness check (the §3.4 invariants)
* Reports a `CompiledTheory` summary (role count, step count, lemma count)
* Writes a JSON sourcemap sidecar
* Does **not** produce a `.spthy` file

This is the lightweight path. Useful for quickly checking that
a file parses cleanly and passes the soundness invariants. The
default-mode build has zero `tamarin-prover-*` library
dependencies, so it works even if the wider workspace is
broken.

### `--flag with-sapic`

```bash
cabal build clemc --flag with-sapic
cabal run clemc --flag with-sapic -- path/to/file.clem
```

Everything default mode does, **plus**:

* Builds a real `Theory.OpenTheory` value via the Sapic
  translation pipeline
* Runs `Sapic.translate` (which generates the multiset rewriting
  rules from the Sapic process)
* Pretty-prints the result and writes `path/to/file.clem.spthy`

This is the path you want when you actually want to verify a
protocol. The `.spthy` file it writes is a real Tamarin theory
that `tamarin-prover --prove` will accept.

## Writing your first protocol

The simplest meaningful Clementine file is `test/Fixtures/hello.clem`:

```clem
protocol Hello {

  builtins { asymmetric_encryption }

  principal A {
    generates    skA
    knows public pkA = PK(skA)
    knows public pkB
  }

  principal B {
    generates    skB
    knows public pkB = PK(skB)
    knows public pkA
  }

  step m1 : A -> B {
    new s
    send AENC(<'msg', s>, pkB)
    claim secret(s)
  }

  verify {
    executable
    secrecy(s)
  }
}
```

What it does:

* Two principals (`A` and `B`) each have a fresh long-term
  keypair. They both know each other's public key.
* Step `m1` is a network step from A to B. Inside the step body:
  * `new s` — A picks a fresh secret nonce
  * `send AENC(<'msg', s>, pkB)` — A encrypts `s` to B's public key
    and puts it on the wire. The `'msg'` is a literal tag (any
    constant string in single quotes is a public constant).
  * `claim secret(s)` — A asserts to the verifier that `s` should
    remain secret
* The `verify` block:
  * `executable` — assert at least one honest run reaches protocol
    startup (mandatory; `clemc` rejects files that omit it)
  * `secrecy(s)` — generate a secrecy lemma over the variable `s`

Compile and verify:

```bash
$ cd lib/clementine
$ cabal run clemc --flag with-sapic -- test/Fixtures/hello.clem
compiled test/Fixtures/hello.clem
  2 role(s)
  1 step(s)
  2 lemma(s)
  source map: test/Fixtures/hello.clem.sourcemap.json
  spthy:      test/Fixtures/hello.clem.spthy

$ tamarin-prover --prove test/Fixtures/hello.clem.spthy
...
analyzed: test/Fixtures/hello.clem.spthy

  executable (exists-trace): verified (2 steps)
  secrecy_s (all-traces): verified (5 steps)
  auto_sources (all-traces): verified (8 steps)
```

`auto_sources` is Clementine's automatically-generated `[sources]`
lemma — you don't write it; the compiler emits it for you to help
Tamarin's matcher.

## Surface language reference

### Top-level structure

```clem
protocol <Name> {
  builtins { <list> }     // optional, comma-separated
  principal <Name> { ... } // one or more
  step <label> : ...       // zero or more
  verify { <queries> }     // mandatory; must include `executable`
}
```

### Builtins

| Builtin | What you get |
|---|---|
| `diffie_hellman` | `'g'^x`, `^` exponentiation, the DH equational theory |
| `signing` | `SIGN(sk, m)`, `VERIFY(pk, m, sig)`, `PK(sk)` |
| `hashing` | `H(m)` (one-way hash) |
| `symmetric_encryption` | `ENC(k, m)`, `DEC(k, c)` |
| `asymmetric_encryption` | `AENC(m, pk)`, `ADEC(c, sk)`, `PK(sk)` |

Combine them: `builtins { diffie_hellman, signing, hashing }`.

### Principal blocks

```clem
principal P {
  generates    skP                  // fresh long-term private key
  knows public pkP = PK(skP)        // derived public key (with equation)
  knows public pkQ                  // peer's public key (no equation;
                                    //   becomes a flat constant unless
                                    //   another principal declares
                                    //   `pkQ = PK(skQ)`)
  knows private psk                 // pre-shared symmetric secret
}
```

Important: when a principal declares `knows public pkQ = PK(skQ)`,
Clementine collects that equation **globally** and resolves any
reference to `pkQ` from any principal as `pk(~skQ)`. This is what
makes encrypted messages decrypt correctly on the receiver side.

### Steps

A network step:

```clem
step <label> : <Sender> -> <Receiver> {
  // body statements run on the sender's side; the receiver
  // implicitly does an `in()` for the `send`
}
```

A local step (no wire transfer):

```clem
step <label> : <Principal> local {
  // body statements run on this principal only
}
```

### Step body statements

| Statement | Meaning |
|---|---|
| `new x` | Sapic `new ~x` — fresh nonce, scoped to this step's principal |
| `let v = e` | Bind `v` to the expression `e`; `v` is in scope for the rest of the body |
| `require <expr>` | Continue only if `<expr>` evaluates to `true`. Typical use: `require VERIFY(pk, body, sig)` |
| `send <expr>` | Put `<expr>` on the wire (only valid in network steps). The receiver implicitly receives. |
| `claim secret(v)` | Assert `v` should be kept secret. Generates a `Secret` action fact that secrecy lemmas quantify over. |

### Expressions

* `var` — bare identifier (variable, principal name, or `knows public` parameter)
* `'literal'` — single-quoted public constant, e.g. `'msg'`, `'g'`, `'1'`
* `<a, b, c>` — n-ary tuple
* `PRIMOP(arg, ...)` — uppercase primitive operator (`AENC`, `SIGN`, `VERIFY`, `H`, `MAC`, `PK`, `DEC`, `ADEC`, `ENC`)
* `b ^ x` — DH exponentiation (left-associative; `'g'^x ^ y` parses as `(g^x)^y`)

### Verify block

```clem
verify {
  executable                                 // mandatory
  secrecy(<term>)                            // weak secrecy
  forward_secrecy(<term>)                    // FS (excuses pre-claim reveals)
  injective_agreement(<I>, <R>, [<terms>])   // Lowe injective agreement
  non_injective_agreement(<I>, <R>, [<terms>])
  authentication(<I>, <R>)                   // Lowe aliveness
}
```

Each query becomes one Tamarin lemma in the generated `.spthy`.

## Diagnostics

Clementine has a stable error code taxonomy. When compilation
fails, `clemc` prints a rustc-style diagnostic:

```
error[E0103]: duplicate principal name `A`
  --> test/Fixtures/broken.clem:3:3
  | Each principal name must appear at most once in a protocol.
  | Rename one of the duplicates.
  = help: run `clemc --explain E0103` for the long form
```

Other useful `clemc` commands:

```bash
clemc --list-codes        # every error/warning code with one-line desc
clemc --explain E0206     # long-form explanation for one code
clemc --explain-all       # every code's full explanation
clemc --help              # this list
```

The current set of enforced wellformedness checks (more land
incrementally):

| Code | Trigger |
|---|---|
| `E0001` | parser failure (syntax error in the `.clem` file) |
| `E0102` | `verify` block references a term that's not bound anywhere |
| `E0103` | duplicate principal name |
| `E0104` | duplicate step label |
| `E0205` | `claim secret(v)` references an undefined variable |
| `E0206` | `verify` block has no `executable` query |
| `E0207` | identifier shadows a reserved prefix (`pat`, `Init`, `Setup_`, `Step_`, `Reveal_`, `KeyGen_`) |
| `E0209` | agreement query references a principal that isn't declared |

## Output files

After `clemc --flag with-sapic protocol.clem`, you get:

| File | What it is |
|---|---|
| `protocol.clem.spthy` | The generated Tamarin theory. Pass this to `tamarin-prover --prove`. |
| `protocol.clem.sourcemap.json` | JSON sidecar mapping every generated rule and lemma name back to `(file, line, col)` in the original `.clem` source. Useful for IDE integration. |

Both are gitignored (see `.gitignore` at the repo root). Don't
commit them.

## Test fixtures

The repo ships three positive fixtures and six negative ones:

| File | Purpose |
|---|---|
| `test/Fixtures/hello.clem` | This walkthrough — minimal `aenc` secrecy |
| `test/Fixtures/iso_dh.clem` | ISO 9798-3 signed Diffie-Hellman, all 9 lemmas verify |
| `test/Fixtures/nsl.clem` | Lowe-fixed Needham-Schroeder PK, secrecy + aliveness verify |
| `test/Fixtures/errors/*.clem` | Six negative cases, each triggering a specific `E####` code |

Run the full test suite with:

```bash
cabal test tamarin-prover-clementine                      # default mode
cabal test tamarin-prover-clementine --flag with-sapic    # with sapic backend
```

Both should be green. The harness asserts that positive fixtures
compile and lower successfully, and that negative fixtures fail
with exactly the expected error code.

## When something goes wrong

* **`clemc` exits 1 with an `E####` code.** Read the diagnostic;
  the file:line:col points at the offending construct. Run
  `clemc --explain E####` for the long form.

* **`clemc` succeeds but `tamarin-prover --prove` fails to load
  the `.spthy`.** This usually means a version mismatch between
  the `tamarin-prover` library Clementine builds against
  (1.13.0) and the homebrew binary (1.10.0). Most format issues
  are post-processed away in `Clementine.LowerSapic`, but new
  ones may still surface. File an issue with the `.clem` source.

* **`tamarin-prover --prove` says a lemma is `falsified`.**
  That's actually a valuable signal — it means tamarin found a
  trace where your protocol is broken. Read the counter-example
  trace; it usually shows exactly which adversary action breaks
  your security claim. Sometimes this means your protocol is
  genuinely insecure (good — you caught a bug). Sometimes it
  means the model is too weak (e.g., you're missing a `require
  VERIFY(...)` somewhere). Sometimes it's a Clementine
  limitation around how lemmas are generated — see the design
  notes for known cases.

* **`auto_sources` fails to verify.** This is a Clementine bug,
  not a user error. The `[sources]` lemma we generate should
  always be provable for well-formed protocols. File an issue
  with the `.clem`.

## Next steps

1. Modify `hello.clem` — break it in interesting ways and see
   what tamarin / clemc say. Try removing `executable`, removing
   the `pkB` recipient, adding a typo in `secrecy(...)`,
   duplicating the principal name.
2. Write your own protocol from scratch. The challenge-response
   skeleton in the project notes is a good 2-message starting
   point.
3. Read `test/Fixtures/iso_dh.clem` to see the full vocabulary
   in action.
4. When you hit something that doesn't work the way you expect,
   the source files in `src/Clementine/` are deliberately
   readable — start with `Clementine/AST.hs` for the data
   model, then `Clementine/Parser.hs` for the surface syntax,
   then `Clementine/LowerSapic.hs` for the translation.
