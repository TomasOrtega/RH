import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmpOfIsCocycle

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory.CechCmp

variable {R : Type} [CommRing R] {Z : Scheme.{0}} (s : Z ⟶ Sp R) {J : Type} (W : J → Z.Opens)

def cocVal (z : Z1 (incl W ⋙ OAff s)) (V V' : Bas W) (h : V'.1.1 ≤ V.1.1) : Γ(Z, V'.1.1) :=
  z.1 (Opposite.op V) (Opposite.op V') (homOfLE (show V' ≤ V from h)).op

/- English proof (translation)
The claim follows from `eq_sub_of_add_eq (Z1.comp z (homOfLE (show B ≤ A from h)).op (homOfLE (show C ≤ B from h')).op).symm`.
-/
theorem cocVal_comp (z : Z1 (incl W ⋙ OAff s)) (A B C : Bas W) (h : B.1.1 ≤ A.1.1)
    (h' : C.1.1 ≤ B.1.1) :
    resG Z h' (cocVal s W z A B h) = cocVal s W z A C (h'.trans h) - cocVal s W z B C h' :=
  eq_sub_of_add_eq (Z1.comp z (homOfLE (show B ≤ A from h)).op
    (homOfLE (show C ≤ B from h')).op).symm

/- English proof (translation)
Take `⟨z, hz⟩` from `H1.mk_surjective _ (resEquiv s W hW x)`. Set `O1 : J → Bas W` to `fun i ↦ ⟨⟨W i, h1 i⟩, i, le_rfl⟩`. Set `O2 : J → J → Bas W` to `fun i i' ↦ ⟨⟨W i ⊓ W i', h2 i i'⟩, i, inf_le_left⟩`. Set `O3 : J → J → J → Bas W` to `fun i i' i'' ↦ ⟨⟨W i ⊓ W i' ⊓ W i'', h3 i i' i''⟩, i, inf_le_left.trans inf_le_left⟩`. Set `c : ∀ i i' : J, Γ(Z, W i ⊓ W i')` to `fun i i' ↦ cocVal s W z (O1 i) (O2 i i') inf_le_left - cocVal s W z (O1 i') (O2 i i') inf_le_right`.

Establish `key : ∀ (i i' : J) (V : Bas W) (h : V.1.1 ≤ W i ⊓ W i'), resG Z h (c i i') = cocVal s W z (O1 i) V (h.trans inf_le_left) - cocVal s W z (O1 i') V (h.trans inf_le_right)`. Introduce `i i' V h`. Establish `e1` using `cocVal_comp s W z (O1 i) (O2 i i') V inf_le_left h`. Establish `e2` using `cocVal_comp s W z (O1 i') (O2 i i') V inf_le_right h`. Establish `e : resG Z h (c i i') = resG Z h (cocVal s W z (O1 i) (O2 i i') inf_le_left) - resG Z h (cocVal s W z (O1 i') (O2 i i') inf_le_right)` using `map_sub _ _ _`.

Rewrite using `[e]`. Use `(congrArg₂ (· - ·) e1 e2).trans ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `hc : IsCocycle W c`. Introduce `i i' i''`.

Establish `e1` using `key i i' (O3 i i' i'') inf_le_left`. Establish `e2` using `key i' i'' (O3 i i' i'') (le_inf (inf_le_left.trans inf_le_right) inf_le_right)`. Establish `e3` using `key i i'' (O3 i i' i'') (le_inf (inf_le_left.trans inf_le_left) inf_le_right)`. Use `(congrArg₂ (· + ·) e1 e2).trans (Eq.trans ?_ e3.symm)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Use `⟨c, hc, ?_⟩` and prove the remaining obligations. Rewrite using `[cmp_of_isCocycle s W hW hc, LinearEquiv.symm_apply_eq, ← hz, H1.mk_eq_mk]`. Use `⟨fun V ↦ -cocVal s W z (O1 (idx V.unop)) V.unop (le_idx V.unop), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `V V' a`. Establish `e1` using `key (idx V.unop) (idx V'.unop) V'.unop (le_inf ((le_of_hom a).trans (le_idx V.unop)) (le_idx V'.unop))`.

Establish `e2` using `cocVal_comp s W z (O1 (idx V.unop)) V.unop V'.unop (le_idx V.unop) (le_of_hom a)`. Establish `goal : -cocVal s W z (O1 (idx V'.unop)) V'.unop (le_idx V'.unop) - resG Z (le_of_hom a) (-cocVal s W z (O1 (idx V.unop)) V.unop (le_idx V.unop)) = resG Z (le_inf ((le_of_hom a).trans (le_idx V.unop)) (le_idx V'.unop)) (c (idx V.unop) (idx V'.unop)) - cocVal s W z V.unop V'.unop ( …`. Rewrite using `[map_neg, e1, e2]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `goal`.
-/
theorem exists_isCocycle_cmp_eq (R : Type) [CommRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (J : Type)
    (W : J → Z.Opens) (hW : ⨆ i, W i = ⊤) (h1 : ∀ i, IsAffineOpen (W i))
    (h2 : ∀ i i', IsAffineOpen (W i ⊓ W i'))
    (h3 : ∀ i i' i'', IsAffineOpen (W i ⊓ W i' ⊓ W i'')) (x : GlobalTheory.CechDR.HO1 s) :
    ∃ c : ∀ i i' : J, Γ(Z, W i ⊓ W i'), IsCocycle W c ∧ cmp s W hW c = x := by
  obtain ⟨z, hz⟩ := H1.mk_surjective _ (resEquiv s W hW x)
  let O1 : J → Bas W := fun i ↦ ⟨⟨W i, h1 i⟩, i, le_rfl⟩
  let O2 : J → J → Bas W := fun i i' ↦ ⟨⟨W i ⊓ W i', h2 i i'⟩, i, inf_le_left⟩
  let O3 : J → J → J → Bas W := fun i i' i'' ↦
    ⟨⟨W i ⊓ W i' ⊓ W i'', h3 i i' i''⟩, i, inf_le_left.trans inf_le_left⟩
  let c : ∀ i i' : J, Γ(Z, W i ⊓ W i') := fun i i' ↦
    cocVal s W z (O1 i) (O2 i i') inf_le_left - cocVal s W z (O1 i') (O2 i i') inf_le_right
  have key : ∀ (i i' : J) (V : Bas W) (h : V.1.1 ≤ W i ⊓ W i'),
      resG Z h (c i i') = cocVal s W z (O1 i) V (h.trans inf_le_left) -
        cocVal s W z (O1 i') V (h.trans inf_le_right) := by
    intro i i' V h
    have e1 := cocVal_comp s W z (O1 i) (O2 i i') V inf_le_left h
    have e2 := cocVal_comp s W z (O1 i') (O2 i i') V inf_le_right h
    have e : resG Z h (c i i') =
        resG Z h (cocVal s W z (O1 i) (O2 i i') inf_le_left) -
          resG Z h (cocVal s W z (O1 i') (O2 i i') inf_le_right) := map_sub _ _ _
    rw [e]
    refine (congrArg₂ (· - ·) e1 e2).trans ?_
    ring
  have hc : IsCocycle W c := by
    intro i i' i''
    have e1 := key i i' (O3 i i' i'') inf_le_left
    have e2 := key i' i'' (O3 i i' i'') (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
    have e3 := key i i'' (O3 i i' i'') (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
    refine (congrArg₂ (· + ·) e1 e2).trans (Eq.trans ?_ e3.symm)
    ring
  refine ⟨c, hc, ?_⟩
  rw [cmp_of_isCocycle s W hW hc, LinearEquiv.symm_apply_eq, ← hz, H1.mk_eq_mk]
  refine ⟨fun V ↦ -cocVal s W z (O1 (idx V.unop)) V.unop (le_idx V.unop), ?_⟩
  funext V V' a
  have e1 := key (idx V.unop) (idx V'.unop) V'.unop
    (le_inf ((le_of_hom a).trans (le_idx V.unop)) (le_idx V'.unop))
  have e2 := cocVal_comp s W z (O1 (idx V.unop)) V.unop V'.unop (le_idx V.unop) (le_of_hom a)
  have goal : -cocVal s W z (O1 (idx V'.unop)) V'.unop (le_idx V'.unop) -
      resG Z (le_of_hom a) (-cocVal s W z (O1 (idx V.unop)) V.unop (le_idx V.unop)) =
      resG Z (le_inf ((le_of_hom a).trans (le_idx V.unop)) (le_idx V'.unop))
        (c (idx V.unop) (idx V'.unop)) - cocVal s W z V.unop V'.unop (le_of_hom a) := by
    rw [map_neg, e1, e2]
    ring
  exact goal

end GlobalTheory.CechCmp
