/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Lean

/-!
# The `lyons_tag` attribute

`@[lyons_tag "TAG"]` labels a declaration with the name of the mathematical
statement it realizes. The label is a string literal matching
`^(def|not|lem|prop|thm)_[A-Za-z0-9_]+$`, and a statement spread over several
declarations carries the same label on each of them.
-/

open Lean

namespace Lyons

/-- Attribute syntax: `@[lyons_tag "TAG"]`.

The trailing space in the atom is deliberate: without it the whitespace style
linter demands `@[lyons_tag"TAG"]`, which is unreadable. -/
syntax (name := lyonsTag) "lyons_tag " str : attr

initialize lyonsTagAttr : ParametricAttribute String ←
  registerParametricAttribute {
    name := `lyonsTag
    descr := "tag of the mathematical statement realized by this declaration"
    getParam := fun _ stx => match stx with
      | `(attr| lyons_tag $s:str) => return s.getString
      | _ => throwError "invalid `lyons_tag` attribute: expected a string literal"
  }

end Lyons
