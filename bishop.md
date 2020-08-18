# Bishop: A content-addressed optimal λ-calculus

> Well, that explains it then. The A2s always were a bit twitchy. That could
> never happen now with our behavioral inhibitors.

This repository implements the a λ-calcus which features optimal reductions via
an implementation of the [Lambdascope interaction net system](https://pdfs.semanticscholar.org/6104/2374787bf6514706b49a5a4f0b74996979a0.pdf)
and content-addressed [InterPlanetary Linked Data](https://ipld.io) references,
allowing Bishop expressions to be stored and distributed via the decentralized (IPFS
protocol)(https://ipfs.io/)

These two features might seem like a surprising combination at first, but it
turns out embedding of λ-calculus terms in an IPLD directed-acyclic reference
graph imposes constraints on the way terms can recurse which enables various
interesting optimizations in an interaction-net system. For example, mutual
recursion of separately defined expressions is incompatible with an IPLD DAG,
since both expressions *cyclically* reference one another, making
content-identifiers difficult to compute (see
[the Unison
language[(https://www.unisonweb.org/docs/faq/#how-does-hashing-work-for-mutually-recursive-definitions)
for a clever solution to this problem ). However, such mutually
recursive terms can also cause various problems in interaction-net systems, such
as incorrect normalization (in some systems) or degraded performance through
increased book-keeping requirements. We conjecture that Bishop's
recursion and referencing constraints will also greatly facilitate certain
optimizations proposed by the Lambdascope paper, namely, the integration of the
King's College Lambda Evaluator (KCLE) technique of identifying closed lambda
abstractions (https://rd.springer.com/chapter/10.1007/978-3-540-25979-4_11).

Interestingly, mutual recursion does not add any expressive power to the
λ-calculus. All terms definable via mutual recursion can be transformed into
definitions which [use direct
recursion](https://en.wikipedia.org/wiki/Mutual_recursion#Conversion_to_direct_recursion).
Furthermore, Bishop's direct recursion restriction, does not even necessarily
impose usability constraints on some future front-end language built on top of
it. The lambda-encoded datatypes of the [Formality proof
language](https://github.com/moonad/Formality), for example, can be defined
using direct recursion, and on on top of these datatypes it is possible to
define dependently-typed [first-class
modules](https://github.com/moonad/Moonad/blob/master/lib/Module.type.fm). This
allows the effective recovery of mutually recursive code blocks packaged in a
single expression of the `Module` type.

In the future, we plan to use this technique to develop a convenient
dependently-typed language using Bishop as a reduction backend.

## Repository Contents:

- **Language.Bishop.Term**:  Implements the λ-terms and the IPLD encoding

- **Language.Bishop.Parse**: Parses `.bish` files which have an approximately
  Haskell-like syntax:

  ```
  -- Scott-encoded Natural numbers
  zero z s   = z
  succ n z s = s n

  -- The first five Nats
  one   = succ zero
  two   = succ one
  three = succ two
  four  = succ three
  five  = succ four

  -- Double a nat
  double n = (n zero) (|x| succ (succ (double x)))

  -- returns `four`
  test = double two
  ```

- **Language.Bishop.Net**: Implements the Lambdascope reduction system.

- **Language.Bishop.Eval**: Reduces Bishop terms via GHC higher-order abstract
syntax.

- **ipld.js**: A simple JavaScript file that uses the `ipld-dag-cbor` library to
encode a few test Bishop terms (encoded as JSON). The encoding and content ids
are bit-identical to the Haskell modules. [TODO: test extensively.]

- **test/Spec.Parse**: A collection of test cases for the parser

### Planned:

- **test**: More test cases for everything

- **benchmarks**: Comparing GHC and Net based reduction, probably using criterion.
Also compare with Formality/Symmetric Interaction Calculus

- **Language.Bishop.Compile**: Compiles Terms to Net and reads back Nets
to Terms

- **Language.Bishop.IPFS**: Utilities for directly interacting with
an IPFS node

- **bide** (planned): A haskeline interactive repl and IPLD dag brower


## Instructions

`git clone` this repo and then `cd` into it and run `stack build` (using [the
Haskell Tool Stack](https://docs.haskellstack.org/en/stable/README/))

`stack ghci` will load you a repl with all the relevant files loaded.

```
> normDef "test.bish" "test"
|z,s| s (|z,s| s (|z,s| s (|z,s| s (|z,s| z))))
```

to test the normalization. 

[TODO: Currently normalizes via HOAS, change to Net with readback]


you can see the IPLD content ids for the terms in a file with `prettyFile`
```
> prettyFile "test.bish"

zero@zDPWYqFD5RthUytX2uCVjQuNnjNCFu5JN2vCG5ZHMy2o25gYNJk9 =
  |z,s| z
two@zDPWYqFCtfNdVZziXU6qTvij6sQhnL6SD1SNsJ17UCXnNhDGDKfZ =
  succ one
three@zDPWYqFD2JLjRz5AKYrLjzZVGpq6kyKWJj7ubkJcGsFCM6phfBou =
  succ two
test@zDPWYqFCsdUmyCygWrTYic8WggmWo3AdtaSpFN7vP696CFY5PpE4 =
  double two
succ@zDPWYqFCtueAsx9V8y8FEWoZSnWrXck7xgKCRD1VtuFxrPTtgmPW =
  |n,z,s| s n
snd@zDPWYqFD3LLvvs6uyXa4KGk7m1cKXQsFgt7P2Jr3GcDKXbWugJHo =
  |x,y| y
one@zDPWYqFD7mznqh5o3KtDM1Rmkk3o54JvgPsdQyfbqfTVCT5ndJpv =
  succ zero
id@zDPWYqFD2v52VBESyj6jEezvRBXatX7rVzxZe4J7NQf6ACbtM2yz =
  |x| x
fst@zDPWYqFD21VZsuaD5VNtnQCzkGMdCCU6ds9rmgQrpzDwzXRmgJqp =
  |x,y| x
four@zDPWYqFCsSrGo3UUSxjp8RKE4Pj6dUUj5TDaras3BrAkNJ61rWSm =
  succ three
foo@zDPWYqFD2eTd4N613kEVZHCgzfqZBrJrrJjduZFB354Xi713PN6G =
  |x| x x
five@zDPWYqFD6EdYua8iJ7jfX1q8FkEeaCgSqGqBAYMmaLxs22s6wRHQ =
  succ four
double@zDPWYqFD56S9bn6MTo721ZMiKkDc8tr9aDBVUWDYe1R5Seb9uT2u =
  |n| n zero (|x| succ (succ (double x)))
baz@zDPWYqFD2MrAtNoBvbYazTLY7hzcEpeh2ZqGqJzKEASAY8Eahmy5 =
  |x,y,z| foo x y z
bar@zDPWYqFCqyews9mfA5ZRDUjf5tyE7veeVif2SKG1tFfBMrCJyYev =
  |x| x
app_id@zDPWYqFD4ZC77CSuSNzXc5bS6tUg8TEAKu5boqKCyxv1tgJGTVcD =
  id id
```

You can run the test cases with `stack test`


## FAQ:

### Why content-addressing and IPFS?

Because content addresses are *awesome*. If you have a Bishop reference, you
know that that reference represents exactly one computation, and the way it runs
the first time is the way it will run anytime. Your reference points to an
expression, which *cannot* change underneath you. A Bishop reference is just the
Blake2b_256 (by default) hash of the expression's serial encoding. A different
expression will generate a totally different address.

---
Actually, you can generate Bishop reference using *any* algorithm supported by the self-identifying
[Multihash](https://multiformats.io/multihash/) library, and we'd *dearly* love
to use Blake3 as the Bishop default once support for it [gets
added ot multihash](https://github.com/multiformats/go-multihash/issues/121) and
then IPFS downstream.

---

The [Nix build system], for example, uses content-addressing to give you
referentially transparent and atomic package installations. If it builds once,
it builds the same way every time. If your power goes out half-way through a
NixOS system upgrade, no worries, your machine is either going to end up in the
old state or the new state, never halfway between. Accidentally installed a
kernel module you don't like? Just rollback to previous system configuration
helpfully listed in your BIOS. Essentially, Nix's content-addressing gives you
Linux super-powers.

Another example of a content-addressed system that gives you superpowers: Git.
Every commit hash is an address that uniquely specifies a repository state. The
code under that hash is *always* going to be the same, and as long as you run it
the same way (a really really big caveat!) it will run the same way.

Here's something weird though, even though both Nix and Git use
content-addressing and are in principle decentralized systems, in practice most
people get their Nix packages from `nixos.org` and most people get
their git repos from the `github.com` (or gitlab or bitbucket or whereever).
And every programming language seems to have a totally different mechanism for
doing their own packages and libraries. JavaScript has npm, Rust has cargo,
Haskell has hackage/stackage/cabal. This renders all your careful
content-addressing via Git less than entirely effective. Your code is
referentialy-transparent by commit-hash, cool, but what about your dependencies?
[Oops.](http://left-pad.io/)

In Bishop, your dependencies are all IPLD content ids. Your packages are IPLD
content ids. Your metadata are content ids. Your code comments, your config
files, everything can be a content id. IPLD is happy to talk to Git, it's happy
to talk to blockchains. [It'll probably talk to Nix pretty
soon](https://github.com/NixOS/nix/issues/859).

Part of the inspiration for Bishop is to explore what programming languages look
like when they're completly built around modern cryptographic and decentralized
technologies. What does a server-less package manager look like? We don't know
yet, but embedding the lambda calculus in IPLD and using IPFS to share programs
seems like a promising place to start.

"But isn't IPFS slow?," I hear you ask. "Don't you have worry about
pinning/hosting/whatever?", "What if files disappear from the swarm?". I'm
pleased to report that much effort, many coins, and, to quote [Yaron
Minsky](https://twitter.com/yminsky/status/1088891690793005056), the bodies of
many grad students are [being thrown at this problem](https://filecoin.io/).

### Why Interaction Nets?

Here Bishop has a somewhat contrarian view: Optimality actually doesn't really
matter that much. Optimality is not the same as efficiency. The former is your
asymptotics for theoretically large programs/inputes, the latter is the
performance characteristics for the kind of code you're probably actually going
run.  There are tons of useful optimizations in functional languages that don't
meaningfully affect your asymptotics; they just make your code run fast.

There are a various parlor tricks you can perform to show how an optimal
reducer can normalize some weird term, like factorials of church-encoded natural
numbers, thousands of times faster than Chez Scheme or the Glasgow Haskell
Compiler. Bishop excels at all these feats of prestidigitation of course, but
it's not really all that meaningful in practice. GHC represents thousands of
person-years of work by some of the most brilliant engineers on the plant.
Bishop was made by a handful of twenty-somethings. Let's be realistic in our
expectations: If your goal is to run lambda calculus expressions as fast as
possible, then for the forseeable future, Bishop is probably not your first
choice (until *we* get thousands, or least hundreds, of person-years of
engineering effort, that is).

The reason Bishop is still really cool though is that it's *radically* simpler:

1. GHC is >500,000 lines of extremely dense and complex code. The interaction
   net part of Bishop is less than a thousand.
2. It's easily implementable in highly imperative/stateful environments, like
   Rust or WASM. You're probably not going to want to carry around GHC's runtime
   in your webapp (although GHCJS and asterius are trying *heroically*), but
   maybe you still want pure functions that don't runtime error after 3000
   recursions.
3. It's still pretty fast. You get *acceptable* time/space performance compared
   to lots of languages, like Python and Ruby, that people use a lot. Compared
   to Rust closures Bishop does pretty well too.
   [TODO: Benchmark all these wild speculations.]
4. Bishop as it is right now is as slow as it's ever going to be. You want more
   performance? Just wait.

λ
