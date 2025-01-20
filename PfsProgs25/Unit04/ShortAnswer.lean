/-!
## Inductive Types

The main type construction in Lean is the inductive type. We will see how to define inductive types and how to define functions by recursion on these types.

We have already seen one special case of inductive types: structures. We will now see two other special cases before the general case. Thus, we see:

* Enumerated types
* Non-recursive Inductive types
* Recursive Inductive types
-/

inductive ShortAnswer where
| yes | no | maybe

def ShortAnswer.or (a b : ShortAnswer) : ShortAnswer :=
  match a, b with
  | yes, _ => yes
  | _, yes => yes
  | maybe, no => maybe
  | maybe, maybe  => maybe
  | no, no => no
  | no, maybe => maybe

#eval  ShortAnswer.or .no ShortAnswer.maybe

-- `open blah` means that we can write `blah.damn` as just `damn`.
open ShortAnswer in
#eval or no yes

/--
error: invalid pattern, variable 'maybe' occurred more than once
---
warning: Local variable 'yes' resembles constructor 'ShortAnswer.yes' - write '.yes' (with a dot) or 'ShortAnswer.yes' to use the constructor.
note: this linter can be disabled with `set_option linter.constructorNameAsVariable false`
---
warning: Local variable 'yes' resembles constructor 'ShortAnswer.yes' - write '.yes' (with a dot) or 'ShortAnswer.yes' to use the constructor.
note: this linter can be disabled with `set_option linter.constructorNameAsVariable false`
---
warning: Local variable 'maybe' resembles constructor 'ShortAnswer.maybe' - write '.maybe' (with a dot) or 'ShortAnswer.maybe' to use the constructor.
note: this linter can be disabled with `set_option linter.constructorNameAsVariable false`
---
warning: Local variable 'no' resembles constructor 'ShortAnswer.no' - write '.no' (with a dot) or 'ShortAnswer.no' to use the constructor.
note: this linter can be disabled with `set_option linter.constructorNameAsVariable false`
-/
#guard_msgs in
def wrongOr (a b : ShortAnswer) : ShortAnswer :=
  match a, b with
  | yes, _ => yes
  | _, yes => yes
  | maybe, no => maybe
  | maybe, maybe  => by
    exact maybe
  | no, no => no
  | no, maybe => maybe

def ShortAnswer.not (a : ShortAnswer) : ShortAnswer :=
  match p:a with
  | yes => by
    exact no
  | no => by
    apply yes
  | maybe => maybe
