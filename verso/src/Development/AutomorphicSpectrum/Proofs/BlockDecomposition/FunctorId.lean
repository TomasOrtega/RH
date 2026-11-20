import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.HT CrystallineSemistableComparison.Pb GlobalTheory.LogCris

namespace GlobalTheory.CompanionTheory.HodgePull

variable {K : Type} [CommRing K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}

/- English proof (translation)
Establish `hs : T.s = 1` using `s_eq_one (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T`. Establish `hs' : T'.s = 1` using `s_eq_one (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T'`. Consider the cases of `T with`. Consider the case `@mk B ring i J δ adm compat α y inα w x v s hx hs0 hv`. Consider the cases of `T' with`.

Consider the case `@mk B' ring' i' J' δ' adm' compat' α' y' inα' w' x' v' s' hx' hs0' hv'`. Simplify using `only at hB hr hi hJ hδ hy hs hs'`. Substitute `hB` using the available equality. Take `rfl` from `eq_of_heq hr`. Take `rfl` from `eq_of_heq hi`.

Take `rfl` from `eq_of_heq hJ`. Take `rfl` from `eq_of_heq hδ`. Take `rfl` from `eq_of_heq hy`. Take `rfl : x = x'` from `funext fun j => Empty.elim j`. Take `rfl : v = v'` from `funext fun j => Empty.elim j`.

Take `rfl : s = s'` from `hs.trans hs'.symm`. Both sides reduce to the same expression.
-/
theorem thick_ext {T T' : Thick (smFun X q)} (hB : T.B = T'.B) (hr : HEq T.ring T'.ring) (hi : HEq T.i T'.i)
    (hJ : HEq T.J T'.J) (hδ : HEq T.δ T'.δ) (hy : HEq T.y T'.y) : T = T' := by
  have hs : T.s = 1 := s_eq_one (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T
  have hs' : T'.s = 1 := s_eq_one (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T'
  cases T with
  | @mk B ring i J δ adm compat α y inα w x v s hx hs0 hv =>
  cases T' with
  | @mk B' ring' i' J' δ' adm' compat' α' y' inα' w' x' v' s' hx' hs0' hv' =>
  dsimp only at hB hr hi hJ hδ hy hs hs'
  subst hB
  obtain rfl := eq_of_heq hr
  obtain rfl := eq_of_heq hi
  obtain rfl := eq_of_heq hJ
  obtain rfl := eq_of_heq hδ
  obtain rfl := eq_of_heq hy
  obtain rfl : x = x' := funext fun j => Empty.elim j
  obtain rfl : v = v' := funext fun j => Empty.elim j
  obtain rfl : s = s' := hs.trans hs'.symm
  rfl

/- English proof (translation)
Substitute `h h'` using the available equality. Conclude with `heq_of_eq (Thick.Hom.ext (eq_of_heq hφ) (funext fun j => Empty.elim j))`.
-/
theorem hom_heq {T₁ T₂ T₁' T₂' : Thick (smFun X q)} (h : T₁ = T₂) (h' : T₁' = T₂') (f : T₁ ⟶ T₁') (g : T₂ ⟶ T₂')
    (hφ : HEq f.φ g.φ) : HEq f g := by
  subst h h'
  exact heq_of_eq (Thick.Hom.ext (eq_of_heq hφ) (funext fun j => Empty.elim j))

/- English proof (translation)
The claim follows from `thick_ext rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl (heq_of_eq (Subtype.ext (Prod.ext rfl (Category.comp_id _))))`.
-/
theorem obj_id (T : Thick (smFun X q)) : (smMor (𝟙 X) (Category.id_comp q)).obj T = T :=
  thick_ext rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl (heq_of_eq (Subtype.ext (Prod.ext rfl (Category.comp_id _))))

/- English proof (translation)
The claim follows from `Functor.hext obj_id fun T T' f => hom_heq (obj_id T) (obj_id T') _ _ HEq.rfl`.
-/
theorem functor_id : (smMor (𝟙 X) (Category.id_comp q)).functor = 𝟭 _ :=
  Functor.hext obj_id fun T T' f => hom_heq (obj_id T) (obj_id T') _ _ HEq.rfl

abbrev idMor (q : X ⟶ Spec (CommRingCat.of K)) (a : ℕ) : CH.Mor (grT (smFun X q) a) (grT (smFun X q) a) (RingHom.id K) :=
  (smS (𝟙 X) (Category.id_comp q)).sq (a := thFil _ (a : ℤ)) (b := thFil _ ((a : ℤ) + 1)) (a' := thFil _ (a : ℤ))
    (b' := thFil _ ((a : ℤ) + 1)) (fun _ _ hx => hx) fun _ _ hx => hx

/- English proof (translation)
Take `⟨x, hx⟩` from `y`. Take `⟨z, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Both sides reduce to the same expression.
-/
theorem τ_id (a : ℕ) (T : Thick (smFun X q)) (y : (grT (smFun X q) a).obj T) :
    (idMor q a).τ T y = y := by
  obtain ⟨x, hx⟩ := y
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/- English proof (translation)
Use function extensionality and compare the values at `s`. Establish `h : s ⋙ (idMor q a).G = s`. Express the relevant statement in the definitionally equal form `s ⋙ (smMor (𝟙 X) (Category.id_comp q)).functor = s`. Rewrite using `[functor_id]`. Conclude with `Functor.comp_id s`.

Conclude with `(τ_id a _ _).trans (eq_of_heq (congr_arg_heq z h))`.
-/
theorem pullC_id (a n : ℕ) (z : CH.Cn (grT (smFun X q) a) n) : (idMor q a).pullC n z = z := by
  funext s
  have h : s ⋙ (idMor q a).G = s := by
    change s ⋙ (smMor (𝟙 X) (Category.id_comp q)).functor = s
    rw [functor_id]
    exact Functor.comp_id s
  exact (τ_id a _ _).trans (eq_of_heq (congr_arg_heq z h))

/- English proof (translation)
Introduce `K _ X q a n x`. Take `⟨⟨z, hz⟩, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Conclude with `congrArg (Submodule.Quotient.mk (p := _)) (Subtype.ext (pullC_id a n z))`.
-/
theorem pullH_id : ∀ (K : Type) [Field K] (X : Scheme.{0}) (q : X ⟶ Spec (CommRingCat.of K)) (a n : ℕ) (x : Hdg q a n),
    pullH (𝟙 X) (Category.id_comp q) a n x = x := by
  intro K _ X q a n x
  obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact congrArg (Submodule.Quotient.mk (p := _)) (Subtype.ext (pullC_id a n z))

end GlobalTheory.CompanionTheory.HodgePull

end
