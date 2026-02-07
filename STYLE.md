# Coding Style Guide

This is a short document describing the preferred coding style for
this project. If something is not covered by this guide try to be
consistent with the code of the already existing modules. The guide
should be considered a strong suggestion, but should not be
dogmatically applied - if there is a good reason for breaking the
rules, then _do it_. If you cannot or do not want to apply a
particular guideline or think some guidelines are missing, consider:
 - **How will your style affect future changes?** Does changing part
   of your style cause a lot of realignments? Is it easily extendable
   by copy-pasting lines?
 -  **Is whitespace effectively used?** Do new indent blocks
   start 2 spaces deeper than the previous one? Is it easy to see
   with your style which block is which?
 -  **How does it scale?** Is your style applicable to small examples as
   well as to large ones?

The guidelines below try to balance these mentioned points.

## Language

Use American English (e.g., initiali**z**ation,
synchroni**z**ation). We encourage the use of a spell checker,
especially for documentation.

## Warnings and Linting

Code should be compilable with `-Wall -Werror`. There should be no
warnings.

We encourage the usage of
[hlint](https://hackage.haskell.org/package/hlint) with the freedom to
deviate from the generated suggestions if there is a good reason to do
so, e.g., if applying the suggestion would reduce the readability of
the code.

## Formatting

### Line Length

Try to keep below *80 characters* (soft), never exceed *90* (hard).

### Type Signatures

We use end-of-line positioning for the `::`, `=>`, and `->` operators
in type signatures and at-the-start positioning for multi-line tuple
elements like `(` and `,`. Have a look at the [Silly Haskell
Formatting
post](https://yairchu.github.io/posts/silly-haskell-formatting) for
some more background on this choice. The `forall`-dot shall be on the
same line as the `forall`-keyword and is the only type operator
exception that does not need to have a space in front, i.e., both
variants `forall .` and `forall.` are allowed. If the `forall` and
constraint lines are short and closely related, then they can be
joined into a single line for improved readability.

Your type signature should look kind of similar to the following
example code in the end:

```haskell
unconsMsbAndCons ::
  forall n. KnownNat n =>
  -- | first input vector
  BitVector (n + 1) ->
  -- | (second input vector, third input vector)
  (BitVector n, BitVector n) ->
  -- | ( most significant bit of the first input vector
  --   , remainder + second and third input concatenated
  --   )
  (Bool, BitVector (3 * n))
```

Also be aware of Haddock only breaking type signatures into multiple
lines at `=>` and `->`. Hence, always consider splitting long
constraint blocks into multiple `(...) =>` groups joining semantically
related constraints wherever possible.

### Indentation

Tabs are illegal! Use spaces for indentation instead. Indent your code
blocks with _2 spaces_. Indent the `where` keyword by _1 space_ to set
it apart from the rest of the code and then indent the definitions in
a `where` clause by one more space.

Examples:

```haskell
sayHello :: IO ()
sayHello = do
  name <- getLine
  putStrLn $ greeting name
 where
  greeting name = "Hello, " ++ name ++ "!"

filter :: (a -> Bool) -> [a] -> [a]
filter _ [] = []
filter p (x:xs)
  | p x       = x : filter p xs
  | otherwise = filter p xs
```

### Blank Lines

Use one blank line between top-level definitions and no blank lines
between type signatures and function definitions. Add one blank line
between functions in a type class instance declaration, if the function
bodies are large. Use your judgment.

### Whitespace

We recommend surrounding binary operators with a single space on
either side. Do not insert spaces after a lambda. Adding a space after
each comma in a tuple is also recommended but not strictly necessary:

```haskell
wonderful = (a, b, c)
acceptable = (a,b,c)
```

Refuse the temptation to use the latter when almost hitting the
line-length limit. Restructure your code or use multiline notation
instead. An example for a multiline tuple declaration is:

```haskell
goodMulti =
  ( a
  , b
  , c
  )
```

Structure nested tuples as such:

```haskell
nested =
  ( ( a1
    , a2
    )
  , b
  , c
  )
```

### Data Declarations

Align the constructors in a data type definition. If a data type has
multiple constructors, each constructor will get its own line.

Example:

```haskell
data Tree a
  = Branch a (Tree a) (Tree a)
  | Leaf
  deriving (Eq, Show)
```

Data types deriving lots of instances may be written like:

```haskell
data Tree a
  = Branch a (Tree a) (Tree a)
  | Leaf
  deriving
    ( Eq, Show, Ord, Read, Functor, Generic, NFData
    , NFDataX, BitPack, ShowX
    )
```

Data types with a single constructor shall be written on a single line:

```haskell
data Foo = Foo Int
```

Format records as follows:

```haskell
data Person = Person
  { -- | First name
    firstName :: String
  , -- | Last name
    lastName :: String
  , -- | Age
    age :: Int
  } deriving (Eq, Show)
```

### List Declarations

Align the elements in the list.

Example:

```haskell
exceptions =
  [ InvalidStatusCode
  , MissingContentHeader
  , InternalServerError
  ]
```

You may not skip the first newline:

```haskell
-- WRONG!
directions = [ North
             , East
             , South
             , West
             ]
```

_Unless_ it fits on a single line:

```haskell
directions = [North, East, South, West]
```

### Vector Declarations

Small vectors may be written on a single line:

```haskell
nrs = 1 :> 2 :> 3 :> 4 :> 5 :> Nil
```

Large vectors should be written like:

```haskell
exceptions
  =  North
  :> East
  :> South
  :> West
  :> Nil
```

Or:

```haskell
exceptions
  =  North :> East :> South
  :> West :> Middle :> Nil
```

### Point-free style

Avoid overusing point-free style. For example, this is hard to read:

```haskell
-- Bad:
f = (g .) . h
```

### Language pragmas

Place LANGUAGE pragmas right after a module's documentation and keep
them alphabetically sorted. Use one line per pragma and do not align
the `#-}` s.

Example:

```haskell
{-|
  .. docs ..
-}

{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE QuasiQuotes #-}

{-# LANGUAGE Safe #-}
```

### Pragmas

Put pragmas immediately after the function they apply to.

Example:

```haskell
id :: a -> a
id x = x
{-# NOINLINE id #-}
```

### Export Lists

Format export lists as follows:

```haskell
module Data.Set
  ( -- * The @Set@ type
    Set
  , empty
  , singleton
  , -- * Querying
    member
  ) where
```

### Imports

Imports should be grouped in the following order:

0. `clash-prelude`¹
1. standard library imports
2. related third party imports
3. local application/library specific imports

Put a blank line between each group of imports. Create subgroups per
your own judgment. The imports in each group should be sorted
alphabetically, by module name.

Always use explicit import lists or `qualified` imports for standard
and third party libraries. This makes the code more robust against
changes in these libraries.

¹ _When writing circuit designs. Does not apply when hacking on the
compiler itself._

## Documentation

### Punctuation

Write proper sentences; start with a capital letter and use proper
punctuation.

### Top-Level Definitions

Comment every top level function (particularly exported functions),
and provide a type signature; use
[Haddock](https://haskell-haddock.readthedocs.io/latest) syntax in the
comments. Comment every exported data type.

**Function example**

```haskell
-- | Send a message on a socket. The socket must be in a connected
-- state. Returns the number of bytes sent. Applications are
-- responsible for ensuring that all data has been sent.
send ::
  -- | Connected socket
  Socket ->
  -- | Data to send
  ByteString ->
  -- | Bytes sent
  IO Int
```

For functions the documentation should give enough information to
apply the function without looking at the function's definition.

**Record example:**

```haskell
-- | Bla bla bla.
data Person = Person
  { -- | Age
    age  :: Int
  , -- | First name
    name :: String
  }
```

For fields that require longer comments format them like so:

```haskell
data Record = Record
  { -- | This is a very very very long comment that is split over
    -- multiple lines.
    field1 :: Text
  , -- | This is a second very very very long comment that is split
    -- over multiple lines.
    field2 :: Int
  }
```

### End-of-Line Comments

Separate end-of-line comments from the code using 2 spaces. Align
comments for data type definitions.

Some examples:

```haskell
data Parser =
  Parser
    Int         -- Current position
    ByteString  -- Remaining input

foo :: Int -> Int
foo n = salt * 32 + 9
 where
  salt = 453645243  -- Magic hash salt.
```

### Links

Use in-line links economically. You are encouraged to add links for API
names. It is not necessary to add links for all API names in a Haddock
comment. We therefore recommend adding a link to an API name if
 - the user might actually want to click on it for more information (in
   your judgment), and
 - only for the first occurrence of each API name in the comment (do
   not bother repeating a link).

## Naming

Use camel case (e.g. `functionName`) when naming functions and upper
camel case (e.g. `DataType`) when naming data types.

For readability reasons, do not capitalize all letters when using an
abbreviation. For example, write `HttpServer` instead of
`HTTPServer`. Exceptions are two letter abbreviations like `IO` or
three letter abbreviations like `SHA`.

## Modules

Use singular when naming modules e.g. use `Data.Map` and
`Data.ByteString.Internal` instead of `Data.Maps` and
`Data.ByteString.Internals`.

## Unicode Syntax

Some people hate them (aka, those who do not have a setup to easily
write them down) and others love them (aka, those who can write them
down). We are trying to settle somewhere in the middle between both
parties here.

Cryptography often relies on writing down many mathematical
definitions, which we also like to connect with proof assistants and
other formal verification tooling. Hence, Unicode symbols may become
reasonably useful at several places to improve code readability and
compatibility a lot. Moreover, one of our goals is to enable
correct-by-design definitions, which turns out to be much easier, if
we can just copy-paste them from the specification documents. Hence,
if these documents for example use `∧` or `∨` symbols to denote
Boolean operations, then it helps if we can keep them in the matching
implementation as well.

Nevertheless, there are many Unicode symbols available and extensive
use can also turn readability worse. Therefore, we impose some simple
rules, we like you to respect:

* Only use symbols that are recognizable and well distinguishable from
  the standard ASCII ones, e.g. using `∀ ∷ ⇒ → ← ≤ ≥ ∧ ∨ ⊕` is fine,
  but ambiguities like `∪ u 𝑢 𝐮` or `⋆ · . ● ∘` may hurt peoples' eyes.
* Unicode symbols should not appear at all in the generated Haddock
  documentation. This makes sure that exported function names, data
  types and type variables can always be used without `{-# LANGUAGE
  UnicodeSyntax #-}` being enabled. Moreover, type variables and
  function arguments cannot use Unicode symbols either, although this
  would not affect usage in the first place. We impose this
  restriction to not confuse users not being familiar with the
  `UnicodeSyntax` extension in the first place. The only exceptions
  are `∀`, `∷,` `⇒`, `→`, and `←`, as Haddock automatically translates
  those to their ASCII equivalents.
* Primarily reserve the use of those symbols for operators and short
  variable names, but do not make them too long. So, it may be
  appropriate to use `γ` or `δ` for local bindings, but introducing
  some variable name `βαδ` needs to be avoided, as this may require to
  type `\beta\alpha\delta` (depending on your setup) to write it down,
  which quickly becomes a lot of typing just for producing a few
  letters in the end.

If you feel uncomfortable or unsure about any of these rules, then
avoid the usage of Unicode in the first place.

## Other Noteworthy Remarks

* We encourage the usage of `where`-clauses in favor of `let`-blocks,
  but be your own judge in each particular case.
* Only put definitions into a local scope if there is a connection to
  the corresponding top-level one. Move definitions to the top level
  otherwise.
* Use Haddock comments in a local scope, as you would also do for
  top-level definitions. This makes it easier if you decide to move
  things to the top level at a later point.
* Avoid using `case`-constructs when pattern matching on
  singletons to bring constraints into scope. Use
  [PatternGuards](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/pattern_guards.html)
  instead, e.g.
  ```haskell
  myFun a b
    | Dict ← lemma₁ a
    , Dict ← lemma₂ b
    , Dict ← lemma₃ c
    = ...
  ```
  looks much more appealing than
  ```haskell
  myFun a b = case lemma₁ a of
    Dict → case lemma₂ b of
      Dict → case lemma₃ a b of
        Dict → ...
  ```
  or
  ```haskell
  myFun a b = case (lemma₁ a, lemma₂ b, lemma₃ a b) of
    (Dict, Dict, Dict) →
      ...
  ```
* Feel free to use common syntactic language extensions, such as
  * [LambdaCase](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/lambda_case.html)
  * [PatternSynonyms](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/pattern_synonyms.html)
  * [RecordWildCards](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/record_wildcards.html),
    [NamedFieldPuns](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/record_puns.html), and
    [OverloadedRecordDot](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/overloaded_record_dot.html)
  * [ViewPatterns](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/view_patterns.html)
  * ...

  Enable them per module and only on demand. If you are not sure
  whether the extension you like to use is common enough, either just
  try (reviewers will complain if they do not like them) or ask
  around.
* Be aware that Clash libraries often make use of the
  [MagicHash](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/magic_hash.html),
  which needs to be enabled explicitly, if required.

## Attribution

This style guide has been adapted and extended from an older version of the
[Clash / Haskell Style
Guide](https://github.com/clash-lang/clash-compiler/blob/381ce892380652d2230895e256de054eb519bf44/STYLE.rst).