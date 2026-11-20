import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ImportsAlt
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

namespace DivCycleGeneric

open MvPolynomial

section Localization

variable {A A' : Type*} [CommRing A] [CommRing A'] [Algebra A A'] (S : Submonoid A)
  [IsLocalization S A']

/- English proof (translation)
Use `set W' := W.map (algebraMap A A')`. Use `set L := Localization.AtPrime W'`. Establish `hc : W'.comap (algebraMap A A') = W` using `IsLocalization.under_map_of_isPrime_disjoint S A' ‹_› hW`. Establish `hL : IsLocalization.AtPrime L W`. Use `IsLocalization.isLocalization_isLocalization_atPrime_isLocalization S L W'` as an intermediate fact.

Use `this using 2` and compare the differences between its conclusion and the goal. Conclude with `hc.symm`. Set `e : Localization.AtPrime W ≃ₐ[A] L` to `IsLocalization.algEquiv W.primeCompl _ _`. Set `_ : Algebra (Localization.AtPrime W) L` to `e.toAlgHom.toRingHom.toAlgebra`. Establish `: IsScalarTower A (Localization.AtPrime W) L` using `IsScalarTower.of_algebraMap_eq fun a => (e.commutes a).symm`.

Set `g` to `(J : Submodule A A).toLocalizedQuotient' L W.primeCompl (Algebra.linearMap A L)`. Establish `h1` using `((IsLocalizedModule.iso W.primeCompl g).extendScalarsOfIsLocalization W.primeCompl (Localization.AtPrime W)).length_eq`. Establish `h2` using `Module.length_eq_of_surjective (S := Localization.AtPrime W) (R := L) (M := L ⧸ (J : Submodule A A).localized' L W.primeCompl (Algebra.linearMap A L)) e.surjective`. Establish `h3 : (J : Submodule A A).localized' L W.primeCompl (Algebra.linearMap A L) = (J.map (algebraMap A A')).map (algebraMap A' L)`. Rewrite using `[Submodule.localized'_eq_span, Ideal.map_map, ← IsScalarTower.algebraMap_eq, Ideal.map]`.

Both sides reduce to the same expression. Rewrite using `[h1, h2, h3]`.
-/
theorem length_eq (J W : Ideal A) [W.IsPrime] (hW : Disjoint (S : Set A) W)
    [(W.map (algebraMap A A')).IsPrime] :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ J)) =
      Module.length (Localization.AtPrime (W.map (algebraMap A A')))
        (Localization.AtPrime (W.map (algebraMap A A')) ⧸
          (J.map (algebraMap A A')).map (algebraMap A' (Localization.AtPrime (W.map (algebraMap A A'))))) := by
  set W' := W.map (algebraMap A A')
  set L := Localization.AtPrime W'
  have hc : W'.comap (algebraMap A A') = W :=
    IsLocalization.under_map_of_isPrime_disjoint S A' ‹_› hW
  have hL : IsLocalization.AtPrime L W := by
    have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization S L W'
    convert this using 2 ; exact hc.symm
  let e : Localization.AtPrime W ≃ₐ[A] L := IsLocalization.algEquiv W.primeCompl _ _
  let _ : Algebra (Localization.AtPrime W) L := e.toAlgHom.toRingHom.toAlgebra
  have : IsScalarTower A (Localization.AtPrime W) L :=
    IsScalarTower.of_algebraMap_eq fun a => (e.commutes a).symm
  let g := (J : Submodule A A).toLocalizedQuotient' L W.primeCompl (Algebra.linearMap A L)
  have h1 := ((IsLocalizedModule.iso W.primeCompl g).extendScalarsOfIsLocalization W.primeCompl
    (Localization.AtPrime W)).length_eq
  have h2 := Module.length_eq_of_surjective (S := Localization.AtPrime W) (R := L)
    (M := L ⧸ (J : Submodule A A).localized' L W.primeCompl (Algebra.linearMap A L)) e.surjective
  have h3 : (J : Submodule A A).localized' L W.primeCompl (Algebra.linearMap A L) =
      (J.map (algebraMap A A')).map (algebraMap A' L) := by
    rw [Submodule.localized'_eq_span, Ideal.map_map, ← IsScalarTower.algebraMap_eq, Ideal.map]
    rfl
  rw [h1, h2, h3]

end Localization

section Generic

variable {n : ℕ}

def blkEquiv (n : ℕ) : (Σ _ : Unit, ReciprocityTheory.ChartRestriction.G.Geo.PBlk n ()) ≃ Fin n where
  toFun p := p.2
  invFun := blk n
  left_inv _ := rfl
  right_inv _ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem blkEquiv_apply (i : Fin n) : blkEquiv n ⟨(), i⟩ = i := rfl

def toGeneric (n : ℕ) : ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n) →+* MvPolynomial (Fin n) ℚ :=
  (MvPolynomial.map (Int.castRingHom ℚ)).comp (rename (R := ℤ) (blkEquiv n)).toRingHom

abbrev genericAlgebra (n : ℕ) :
    Algebra (ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n)) (MvPolynomial (Fin n) ℚ) :=
  (toGeneric n).toAlgebra

attribute [local instance] genericAlgebra

abbrev intUnits (n : ℕ) : Submonoid (ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n)) :=
  (nonZeroDivisors ℤ).map (C : ℤ →+* ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n))

instance isLocalization_generic (n : ℕ) : IsLocalization (intUnits n) (MvPolynomial (Fin n) ℚ) := by
  let _ := MvPolynomial.algebraMvPolynomial (σ := Σ _ : Unit, ReciprocityTheory.ChartRestriction.G.Geo.PBlk n ()) (R := ℤ) (S := ℚ)
  have : IsLocalization (intUnits n) (MvPolynomial (Σ _ : Unit, ReciprocityTheory.ChartRestriction.G.Geo.PBlk n ()) ℚ) :=
    MvPolynomial.isLocalization (nonZeroDivisors ℤ) ℚ
  refine IsLocalization.isLocalization_of_algEquiv (intUnits n)
    (AlgEquiv.ofRingEquiv (f := (renameEquiv ℚ (blkEquiv n)).toRingEquiv) fun x => ?_)
  show (renameEquiv ℚ (blkEquiv n)) (MvPolynomial.map (algebraMap ℤ ℚ) x) =
    MvPolynomial.map (Int.castRingHom ℚ) (rename (blkEquiv n) x)
  rw [renameEquiv_apply, map_rename, algebraMap_int_eq]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem algebraMap_generic :
    algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n)) (MvPolynomial (Fin n) ℚ) =
      toGeneric n := rfl

/- English proof (translation)
Establish `h : IndefiniteRowSideFullHecke.ArithBezout.finIdeal W = W.map (renameEquiv ℤ (blkEquiv n)).toRingEquiv`. Rewrite using `[IndefiniteRowSideFullHecke.ArithBezout.finIdeal, ← Ideal.comap_symm]`. Both sides reduce to the same expression. Rewrite using `[genericIdeal, h]`. Use `show Ideal.map _ (Ideal.map (rename (R := ℤ) (blkEquiv n)).toRingHom W) = _`.

Rewrite using `[Ideal.map_map, algebraMap_generic]`. Both sides reduce to the same expression.
-/
theorem genericIdeal_eq (W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n))) :
    genericIdeal W = W.map (algebraMap _ (MvPolynomial (Fin n) ℚ)) := by
  have h : IndefiniteRowSideFullHecke.ArithBezout.finIdeal W = W.map (renameEquiv ℤ (blkEquiv n)).toRingEquiv := by
    rw [IndefiniteRowSideFullHecke.ArithBezout.finIdeal, ← Ideal.comap_symm]
    rfl
  rw [genericIdeal, h]
  show Ideal.map _ (Ideal.map (rename (R := ℤ) (blkEquiv n)).toRingHom W) = _
  rw [Ideal.map_map, algebraMap_generic]
  rfl

/- English proof (translation)
Rewrite using `[ReciprocityTheory.ChartRestriction.G.Geo.IsHorizontal, Set.disjoint_left, eq_bot_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h m hm`. Rewrite using `[Ideal.mem_bot]`. Assume the negation of the conclusion as `h0`.

Conclude with `h ⟨m, mem_nonZeroDivisors_of_ne_zero h0, rfl⟩ hm`. Introduce and unpack `h _ ⟨m, hm, rfl⟩ hW`. Conclude with `nonZeroDivisors.ne_zero hm (Ideal.mem_bot.mp (h hW))`.
-/
theorem disjoint_iff_isHorizontal (W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n))) :
    Disjoint (intUnits n : Set (ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n)))
      (W : Set (ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n))) ↔ ReciprocityTheory.ChartRestriction.G.Geo.IsHorizontal W := by
  rw [ReciprocityTheory.ChartRestriction.G.Geo.IsHorizontal, Set.disjoint_left, eq_bot_iff]
  constructor
  · intro h m hm
    rw [Ideal.mem_bot]
    by_contra h0
    exact h ⟨m, mem_nonZeroDivisors_of_ne_zero h0, rfl⟩ hm
  · rintro h _ ⟨m, hm, rfl⟩ hW
    exact nonZeroDivisors.ne_zero hm (Ideal.mem_bot.mp (h hW))

/- English proof (translation)
Simplify using `[algebraMap_generic, toGeneric, IndefiniteRowSideFullHecke.ArithBezout.linForm, linForm, blkEquiv_apply, ReciprocityTheory.ChartRestriction.G.Geo.Xc]`.
-/
theorem algebraMap_linForm (u : Fin n → ℤ) :
    algebraMap _ (MvPolynomial (Fin n) ℚ) (IndefiniteRowSideFullHecke.ArithBezout.linForm u) = linForm fun j => (u j : ℚ) := by
  simp [algebraMap_generic, toGeneric, IndefiniteRowSideFullHecke.ArithBezout.linForm, linForm, blkEquiv_apply,
    ReciprocityTheory.ChartRestriction.G.Geo.Xc]

/- English proof (translation)
The claim follows from `IsLocalization.under_map_of_isPrime_disjoint (intUnits n) (MvPolynomial (Fin n) ℚ) hW ((disjoint_iff_isHorizontal W).mpr hh)`.
-/
theorem map_comap_horizontal (W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n)))
    (hW : W.IsPrime) (hh : ReciprocityTheory.ChartRestriction.G.Geo.IsHorizontal W) :
    (W.map (algebraMap _ (MvPolynomial (Fin n) ℚ))).comap (algebraMap _ (MvPolynomial (Fin n) ℚ)) = W :=
  IsLocalization.under_map_of_isPrime_disjoint (intUnits n) (MvPolynomial (Fin n) ℚ) hW
    ((disjoint_iff_isHorizontal W).mpr hh)

open Classical in

/- English proof (translation)
Introduce `n e P u _ _`. Use `set J := P ⊔ Ideal.span {IndefiniteRowSideFullHecke.ArithBezout.linForm u}`. Establish `hJ : genericIdeal P ⊔ Ideal.span {linForm fun j => (u j : ℚ)} = J.map (algebraMap _ (MvPolynomial (Fin n) ℚ))`. Rewrite using `[Ideal.map_sup, Ideal.map_span, Set.image_singleton, algebraMap_linForm, genericIdeal_eq]`. Establish `hX : ∀ j : Fin n, algebraMap _ (MvPolynomial (Fin n) ℚ) (X ⟨(), j⟩ : ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n)) = X j` using `fun j => by`.

Simplify using `[algebraMap_generic, toGeneric, blkEquiv_apply]`. Establish `hsub : (↑((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P (IndefiniteRowSideFullHecke.ArithBezout.linForm u)).filter ReciprocityTheory.ChartRestriction.G.Geo.IsHorizontal).support : Set (Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestrictio …`. Introduce `W hW`. Rewrite `hW` using `[Finset.mem_coe, Finsupp.mem_support_iff, Finsupp.filter_apply]`. Use `split_ifs at hW with hh`.

Use `⟨?_, hh⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hp`. Apply `hW` to reduce the goal to its premises. Use `show (if W ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P (IndefiniteRowSideFullHecke.ArithBezout.linForm u) then _ else 0) = 0`. Rewrite using `[if_neg fun h => hp h.1.1.1]`.

Conclude with `absurd rfl hW`. Establish `hinj : Set.InjOn genericIdeal {W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n)) | W.IsPrime ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsHorizontal W}`. Introduce `W₁ h₁ W₂ h₂ h`. Rewrite `h` using `[genericIdeal_eq, genericIdeal_eq]`. Use `congrArg (Ideal.comap (algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n)) (MvPolynomial (Fin n) ℚ))) h` as an intermediate fact.

Rewrite `this` using `[map_comap_horizontal W₁ h₁.1 h₁.2, map_comap_horizontal W₂ h₂.1 h₂.2]`. Then use the resulting hypothesis. Use extensionality with `W'`. Rewrite using `[divCycle, fundCycle, Finsupp.onFinset_apply, hJ]`. Distinguish the cases in `hW' : W'.IsPrime`. Choose the witnesses or unpack the hypotheses as in `⟨W, hWp, hWd, rfl⟩ : ∃ W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n)), W.IsPrime ∧ Disjoint (intUnits n : Set (ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n))) (W : Set …`.

Rewrite `hW'` using `[IsLocalization.isPrime_iff_isPrime_disjoint (intUnits n) (MvPolynomial (Fin n) ℚ)]`. Conclude with `⟨_, hW'.1, hW'.2, IsLocalization.map_under (intUnits n) (MvPolynomial (Fin n) ℚ) W'⟩`. Establish `hh` using `(disjoint_iff_isHorizontal W).mp hWd`. Establish `hc` using `map_comap_horizontal W hWp hh`. Use `conv_rhs => rw [← genericIdeal_eq W, Finsupp.mapDomain_apply' _ _ hsub hinj ⟨hWp, hh⟩]`.

Rewrite using `[Finsupp.filter_apply, if_pos hh]`. Use `show _ = if W ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P (IndefiniteRowSideFullHecke.ArithBezout.linForm u) then ReciprocityTheory.ChartRestriction.G.Geo.multAt J W else 0`. Establish `hmem : W.map (algebraMap _ (MvPolynomial (Fin n) ℚ)) ∈ relComps (J.map (algebraMap _ (MvPolynomial (Fin n) ℚ))) ↔ W ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P (IndefiniteRowSideFullHecke.ArithBezout.linForm u)`. Establish `hrel : IsRelevant (W.map (algebraMap _ (MvPolynomial (Fin n) ℚ))) ↔ ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant W`. Establish `hXm : ∀ j : Fin n, X j ∈ W.map (algebraMap _ (MvPolynomial (Fin n) ℚ)) ↔ (X ⟨(), j⟩ : ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n)) ∈ W` using `fun j => by`.

Rewrite using `[← hX, ← Ideal.mem_comap, hc]`. Simplify using `only [IsRelevant, ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant, hXm]`. Conclude with `⟨fun ⟨j, hj⟩ k => ⟨j, by cases k; exact hj⟩, fun h => h ()⟩`. Simplify using `only [relComps, ReciprocityTheory.ChartRestriction.G.Geo.divSupp, Set.mem_ofPred_eq, hrel, IsLocalization.minimalPrimes_map (intUnits n) (MvPolynomial (Fin n) ℚ), Set.mem_preimage]`. Rewrite using `[show Ideal.under _ (W.map (algebraMap _ (MvPolynomial (Fin n) ℚ))) = W from hc]`.

Establish `: (W.map (algebraMap _ (MvPolynomial (Fin n) ℚ))).IsPrime` using `IsLocalization.isPrime_of_isPrime_disjoint (intUnits n) _ W hWp hWd`. Distinguish the cases in `hm : W ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P (IndefiniteRowSideFullHecke.ArithBezout.linForm u)`. Rewrite using `[if_pos (hmem.mpr hm), if_pos hm, localMult, dif_pos this, ReciprocityTheory.ChartRestriction.G.Geo.multAt, dif_pos hWp, length_eq (A' := MvPolynomial (Fin n) ℚ) (intUnits n) J W hWd]`. Rewrite using `[if_neg (fun h => hm (hmem.mp h)), if_neg hm]`. Rewrite using `[if_neg fun h => hW' h.1.1.1]`.

Use `symm`. Rewrite using `[Finsupp.mapDomain, Finsupp.sum_apply]`. Use `Finset.sum_eq_zero fun W hW => ?_` and prove the remaining obligations. Simplify using `only`. Rewrite using `[Finsupp.single_apply, if_neg]`.

Introduce and unpack `rfl`. Take `⟨hWp, hh⟩` from `hsub hW`. Apply `hW'` to reduce the goal to its premises. Rewrite using `[genericIdeal_eq]`. Conclude with `IsLocalization.isPrime_of_isPrime_disjoint (intUnits n) _ W hWp ((disjoint_iff_isHorizontal W).mpr hh)`.
-/
theorem proof : Statement := by
  intro n e P u _ _
  set J := P ⊔ Ideal.span {IndefiniteRowSideFullHecke.ArithBezout.linForm u}
  have hJ : genericIdeal P ⊔ Ideal.span {linForm fun j => (u j : ℚ)} =
      J.map (algebraMap _ (MvPolynomial (Fin n) ℚ)) := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, algebraMap_linForm, genericIdeal_eq]
  have hX : ∀ j : Fin n, algebraMap _ (MvPolynomial (Fin n) ℚ)
      (X ⟨(), j⟩ : ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n)) = X j := fun j => by
    simp [algebraMap_generic, toGeneric, blkEquiv_apply]
  have hsub : (↑((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P (IndefiniteRowSideFullHecke.ArithBezout.linForm u)).filter
      ReciprocityTheory.ChartRestriction.G.Geo.IsHorizontal).support :
        Set (Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n)))) ⊆
        {W | W.IsPrime ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsHorizontal W} := by
    intro W hW
    rw [Finset.mem_coe, Finsupp.mem_support_iff, Finsupp.filter_apply] at hW
    split_ifs at hW with hh
    · refine ⟨?_, hh⟩
      by_contra hp
      apply hW
      show (if W ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P (IndefiniteRowSideFullHecke.ArithBezout.linForm u) then _ else 0) = 0
      rw [if_neg fun h => hp h.1.1.1]
    · exact absurd rfl hW
  have hinj : Set.InjOn genericIdeal {W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n)) |
      W.IsPrime ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsHorizontal W} := by
    intro W₁ h₁ W₂ h₂ h
    rw [genericIdeal_eq, genericIdeal_eq] at h
    have := congrArg (Ideal.comap (algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n))
      (MvPolynomial (Fin n) ℚ))) h
    rwa [map_comap_horizontal W₁ h₁.1 h₁.2, map_comap_horizontal W₂ h₂.1 h₂.2] at this
  ext W'
  rw [divCycle, fundCycle, Finsupp.onFinset_apply, hJ]
  by_cases hW' : W'.IsPrime
  · obtain ⟨W, hWp, hWd, rfl⟩ : ∃ W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n)),
        W.IsPrime ∧ Disjoint (intUnits n : Set (ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n)))
          (W : Set (ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n))) ∧
          W.map (algebraMap _ (MvPolynomial (Fin n) ℚ)) = W' := by
      rw [IsLocalization.isPrime_iff_isPrime_disjoint (intUnits n) (MvPolynomial (Fin n) ℚ)] at hW'
      exact ⟨_, hW'.1, hW'.2, IsLocalization.map_under (intUnits n) (MvPolynomial (Fin n) ℚ) W'⟩
    have hh := (disjoint_iff_isHorizontal W).mp hWd
    have hc := map_comap_horizontal W hWp hh
    conv_rhs => rw [← genericIdeal_eq W, Finsupp.mapDomain_apply' _ _ hsub hinj ⟨hWp, hh⟩]
    rw [Finsupp.filter_apply, if_pos hh]
    show _ = if W ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P (IndefiniteRowSideFullHecke.ArithBezout.linForm u) then
      ReciprocityTheory.ChartRestriction.G.Geo.multAt J W else 0
    have hmem : W.map (algebraMap _ (MvPolynomial (Fin n) ℚ)) ∈
        relComps (J.map (algebraMap _ (MvPolynomial (Fin n) ℚ))) ↔
          W ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P (IndefiniteRowSideFullHecke.ArithBezout.linForm u) := by
      have hrel : IsRelevant (W.map (algebraMap _ (MvPolynomial (Fin n) ℚ))) ↔
          ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant W := by
        have hXm : ∀ j : Fin n, X j ∈ W.map (algebraMap _ (MvPolynomial (Fin n) ℚ)) ↔
            (X ⟨(), j⟩ : ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n)) ∈ W := fun j => by
          rw [← hX, ← Ideal.mem_comap, hc]
        simp only [IsRelevant, ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant, hXm]
        exact ⟨fun ⟨j, hj⟩ k => ⟨j, by cases k; exact hj⟩, fun h => h ()⟩
      simp only [relComps, ReciprocityTheory.ChartRestriction.G.Geo.divSupp, Set.mem_ofPred_eq, hrel,
        IsLocalization.minimalPrimes_map (intUnits n) (MvPolynomial (Fin n) ℚ), Set.mem_preimage]
      rw [show Ideal.under _ (W.map (algebraMap _ (MvPolynomial (Fin n) ℚ))) = W from hc]
    have : (W.map (algebraMap _ (MvPolynomial (Fin n) ℚ))).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint (intUnits n) _ W hWp hWd
    by_cases hm : W ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P (IndefiniteRowSideFullHecke.ArithBezout.linForm u)
    · rw [if_pos (hmem.mpr hm), if_pos hm, localMult, dif_pos this, ReciprocityTheory.ChartRestriction.G.Geo.multAt, dif_pos hWp,
        length_eq (A' := MvPolynomial (Fin n) ℚ) (intUnits n) J W hWd]
    · rw [if_neg (fun h => hm (hmem.mp h)), if_neg hm]
  · rw [if_neg fun h => hW' h.1.1.1]
    symm
    rw [Finsupp.mapDomain, Finsupp.sum_apply]
    refine Finset.sum_eq_zero fun W hW => ?_
    dsimp only
    rw [Finsupp.single_apply, if_neg]
    rintro rfl
    obtain ⟨hWp, hh⟩ := hsub hW
    apply hW'
    rw [genericIdeal_eq]
    exact IsLocalization.isPrime_of_isPrime_disjoint (intUnits n) _ W hWp ((disjoint_iff_isHorizontal W).mpr hh)

end Generic

end DivCycleGeneric

end ObjectsChow

end GroundTheory.Heights₂.Heights
