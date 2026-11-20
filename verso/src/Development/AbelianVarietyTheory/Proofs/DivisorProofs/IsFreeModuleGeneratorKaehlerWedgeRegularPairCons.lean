import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair

open IsLocalRing KaehlerDifferential Module

/- English proof (translation)
Assume the negation of the conclusion as `ha`. Establish `hau : IsUnit a` using `by simpa [mem_maximalIdeal, mem_nonunits_iff] using ha`. Establish `hu : u ∈ maximalIdeal R` using `h ▸ Ideal.subset_span (by simp)`. Establish `hle : maximalIdeal R ≤ Ideal.span {u} ⊔ maximalIdeal R ^ 2` using `by conv_lhs => rw [← h]`. Rewrite using `[Ideal.span_le]`.

Introduce and unpack `x (rfl | rfl)`. Take `⟨c, hc⟩` from `hau.exists_left_inv`. Establish `e : x = c * (a * x + b * u) + (-(c * b)) * u`. Take the linear combination `(-x) * hc`. Rewrite using `[e]`.

Conclude with `add_mem (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ hab)) (Ideal.mem_sup_left (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self u)))`. Conclude with `Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)`. Establish `h1` using `spanFinrank_maximalIdeal_le_ncard_of_le_sup_sq (Set.finite_singleton u) ((Ideal.span_singleton_le_iff_mem _).2 hu) hle`. Rewrite `h1` using `[Set.ncard_singleton]`. Establish `h2` using `ringKrullDim_le_spanFinrank_maximalIdeal R`.

Rewrite `h2` using `[hd]`. Establish `h3 : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) ≤ 1` using `by exact_mod_cast h1`. Use `h2.trans h3` as an intermediate fact. Evaluate the numerical expressions using `at this`.
-/
theorem mem_maximalIdeal_of_mul_add_mul_mem_sq {R : Type} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {t u : R} (h : Ideal.span {t, u} = maximalIdeal R)
    (hd : ringKrullDim R = 2) {a b : R} (hab : a * t + b * u ∈ maximalIdeal R ^ 2) :
    a ∈ maximalIdeal R := by
  by_contra ha
  have hau : IsUnit a := by simpa [mem_maximalIdeal, mem_nonunits_iff] using ha
  have hu : u ∈ maximalIdeal R := h ▸ Ideal.subset_span (by simp)
  have hle : maximalIdeal R ≤ Ideal.span {u} ⊔ maximalIdeal R ^ 2 := by
    conv_lhs => rw [← h]
    rw [Ideal.span_le]
    rintro x (rfl | rfl)
    · obtain ⟨c, hc⟩ := hau.exists_left_inv
      have e : x = c * (a * x + b * u) + (-(c * b)) * u := by
        linear_combination (-x) * hc
      rw [e]
      exact add_mem (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ hab))
        (Ideal.mem_sup_left (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self u)))
    · exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
  have h1 := spanFinrank_maximalIdeal_le_ncard_of_le_sup_sq (Set.finite_singleton u)
    ((Ideal.span_singleton_le_iff_mem _).2 hu) hle
  rw [Set.ncard_singleton] at h1
  have h2 := ringKrullDim_le_spanFinrank_maximalIdeal R
  rw [hd] at h2
  have h3 : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) ≤ 1 := by exact_mod_cast h1
  have := h2.trans h3
  norm_num at this

/- English proof (translation)
Introduce `L _ cL Q hQ t u hspan hdim`. Use `letI := hQ.isLocalRing`. Use `letI : Algebra ℂ Q := (cL.codRestrict Q hQ.const_mem).toAlgebra`. Use `haveI : Algebra.EssFiniteType ℂ Q := hQ.essFiniteType`. Use `haveI : IsNoetherianRing Q := Algebra.EssFiniteType.isNoetherianRing ℂ Q`.

Use `haveI : IsRegularLocalRing Q := by`. Use `IsRegularLocalRing.of_spanFinrank_maximalIdeal_le Q ?_` and prove the remaining obligations. Rewrite using `[hdim, ← hspan]`. Establish `h1` using `Submodule.spanFinrank_span_le_ncard_of_finite (R := Q) (Set.toFinite ({t, u} : Set Q))`. Establish `h2 : ({t, u} : Set Q).ncard ≤ 2` using `(Set.ncard_insert_le _ _).trans (by simp)`.

Conclude with `h1.trans h2` after adjusting the coercions. Use `haveI : Algebra.FormallySmooth ℂ Q := formallySmooth_of_isRegularLocalRing_of_perfectField ℂ Q`. Establish `hs : Function.Surjective (algebraMap Q (ResidueField Q))` using `residue_surjective`. Use `haveI : Algebra.EssFiniteType ℂ (ResidueField Q) := .comp ℂ Q _`. Establish `hinj` using `(Algebra.FormallySmooth.kerCotangentToTensor_injective_iff (R := ℂ) hs).mpr inferInstance`.

Establish `hker : RingHom.ker (algebraMap Q (ResidueField Q)) = maximalIdeal Q` using `ker_residue`. Establish `htm : t ∈ maximalIdeal Q` using `hspan ▸ Ideal.subset_span (by simp)`. Establish `hum : u ∈ maximalIdeal Q` using `hspan ▸ Ideal.subset_span (by simp)`. Establish `ht0 : algebraMap Q (ResidueField Q) t = 0` using `(residue_eq_zero_iff t).mpr htm`. Establish `hu0 : algebraMap Q (ResidueField Q) u = 0` using `(residue_eq_zero_iff u).mpr hum`.

Take `⟨s, hsb⟩` from `exists_isTranscendenceBasis ℂ (ResidueField Q)`. Use `haveI := hsb.isAlgebraic_field`. Use `haveI : Algebra.IsSeparable (IntermediateField.adjoin ℂ (Set.range ((↑) : s → ResidueField Q))) (ResidueField Q) := Algebra.IsAlgebraic.isSeparable_of_perfectField`. Take `⟨bκ, hbκ⟩` from `exists_basis_kaehler_of_algebraicIndependent hsb.1`. Use `haveI : Finite s := Module.Finite.finite_basis bκ`.

Set `e : Fin (Nat.card s) ≃ s` to `(Finite.equivFin s).symm`. Set `b'` to `bκ.reindex e.symm`. Establish `hb' : ∀ i, b' i = D ℂ (ResidueField Q) (e i)` using `fun i => by`. Rewrite using `[Basis.reindex_apply, Equiv.symm_symm, hbκ]`. Set `z : Fin (Nat.card s) → Q` to `fun i => Function.surjInv hs (e i : ResidueField Q)`.

Establish `hz : ∀ i, algebraMap Q (ResidueField Q) (z i) = e i` using `fun i => Function.surjInv_eq hs _`. Use `⟨Nat.card s, z, fun P hP => ?_, ?_⟩` and prove the remaining obligations. Establish `e1 : algebraMap Q (ResidueField Q) (MvPolynomial.eval₂ (cL.codRestrict Q hQ.const_mem) z P) = MvPolynomial.aeval (fun i => (e i : ResidueField Q)) P`. Rewrite using `[show (fun i => (e i : ResidueField Q)) = algebraMap Q (ResidueField Q) ∘ z from`. Use function extensionality and compare the values at `fun i => (hz i).symm, MvPolynomial.aeval_algebraMap_apply]`.

Both sides reduce to the same expression. Use `(residue_ne_zero_iff_isUnit _).mp ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `algebraMap Q (ResidueField Q) _ ≠ 0`. Rewrite using `[e1]`. Conclude with `fun h0 => hP ((algebraicIndependent_iff.1 (hsb.1.comp e e.injective)) P h0)`.

Set `v : Fin (Nat.card s + 2) → Q` to `Fin.cons t (Fin.cons u z : Fin (Nat.card s + 1) → Q)`. Set `w : Fin (Nat.card s + 2) → (ResidueField Q) ⊗[Q] Ω[Q⁄ℂ]` to `TensorProduct.mk Q (ResidueField Q) Ω[Q⁄ℂ] 1 ∘ fun i => D ℂ Q (v i)`. Establish `hw0 : w 0 = (1 : (ResidueField Q)) ⊗ₜ[Q] D ℂ Q t` using `rfl`. Establish `hw1 : w (Fin.succ 0) = (1 : (ResidueField Q)) ⊗ₜ[Q] D ℂ Q u` using `rfl`. Establish `hwz : ∀ i : Fin (Nat.card s), w i.succ.succ = (1 : (ResidueField Q)) ⊗ₜ[Q] D ℂ Q (z i)` using `fun i => rfl`.

Establish `hmb : ∀ x : Q, mapBaseChange ℂ Q (ResidueField Q) ((1 : (ResidueField Q)) ⊗ₜ[Q] D ℂ Q x) = D ℂ (ResidueField Q) (algebraMap Q (ResidueField Q) x)` using `fun x => by rw [mapBaseChange_tmul, one_smul, map_D]`. Establish `hpair : ∀ a b : Q, (1 : (ResidueField Q)) ⊗ₜ[Q] D ℂ Q (a * t + b * u) = algebraMap Q (ResidueField Q) a • w 0 + algebraMap Q (ResidueField Q) b • w (Fin.succ 0)` using `fun a b => by`. Rewrite using `[hw0, hw1]`. Simplify using `only [map_add, Derivation.leibniz, TensorProduct.tmul_add, TensorProduct.tmul_smul]`. Rewrite using `[← algebraMap_smul (ResidueField Q) t, ← algebraMap_smul (ResidueField Q) u, ht0, hu0]`.

Simplify using `only [zero_smul, add_zero, algebraMap_smul]`. Establish `hkc : ∀ x (hx : x ∈ RingHom.ker (algebraMap Q (ResidueField Q))), kerCotangentToTensor ℂ Q (ResidueField Q) ((RingHom.ker (algebraMap Q (ResidueField Q))).toCotangent ⟨x, hx⟩) = (1 : (ResidueField Q)) ⊗ₜ[Q] D ℂ Q x` using `fun x hx => kerCotangentToTensor_toCotangent _ _ _ _`. Establish `hsp : Submodule.span (ResidueField Q) (Set.range w) = ⊤`. Rewrite using `[eq_top_iff]`. Introduce `y _`.

Set `c` to `b'.repr (mapBaseChange ℂ Q (ResidueField Q) y)`. Establish `hy0 : mapBaseChange ℂ Q (ResidueField Q) (y - ∑ i, c i • w i.succ.succ) = 0`. Rewrite using `[map_sub, map_sum, sub_eq_zero]`. Use `conv_lhs => rw [← b'.sum_repr (mapBaseChange ℂ Q (ResidueField Q) y)]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[map_smul, hwz, hmb, hz, hb']`. Take `⟨c', hc'⟩` from `(exact_kerCotangentToTensor_mapBaseChange ℂ Q (ResidueField Q) hs _).mp hy0`. Take `⟨⟨x, hx⟩, rfl⟩` from `Ideal.toCotangent_surjective _ c'`. Establish `hx'` using `hx`. Rewrite `hx'` using `[hker, ← hspan, Ideal.mem_span_pair]`.

Take `⟨a, b, rfl⟩` from `hx'`. Rewrite `hc'` using `[hkc, hpair]`. Establish `hy : y = (algebraMap Q (ResidueField Q) a • w 0 + algebraMap Q (ResidueField Q) b • w (Fin.succ 0)) + ∑ i, c i • w i.succ.succ`. Rewrite using `[hc', sub_add_cancel]`. Rewrite using `[hy]`.

Use `add_mem (add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)) (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Fin.succ 0, rfl⟩))) (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))` and prove the remaining obligations. Establish `hli : LinearIndependent (ResidueField Q) w`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg`. Rewrite `hg` using `[Fin.sum_univ_succ, Fin.sum_univ_succ]`.

Establish `hφ` using `congrArg (mapBaseChange ℂ Q (ResidueField Q)) hg`. Simplify using `only [map_add, map_sum, map_smul, map_zero] at hφ`. Rewrite `hφ` using `[hw0, hmb, ht0, Derivation.map_zero, smul_zero, zero_add]`. Rewrite `hφ` using `[hw1, hmb, hu0, Derivation.map_zero, smul_zero, zero_add]`. Simplify using `only [hwz, hmb, hz, ← hb'] at hφ`.

Establish `hrest : ∀ i : Fin (Nat.card s), g i.succ.succ = 0` using `Fintype.linearIndependent_iff.mp b'.linearIndependent (fun i => g i.succ.succ) hφ`. Simplify using `only [hrest, zero_smul, Finset.sum_const_zero, add_zero] at hg`. Take `⟨a, ha⟩` from `hs (g 0)`. Take `⟨b, hb⟩` from `hs (g (Fin.succ 0))`. Establish `hg' : (1 : (ResidueField Q)) ⊗ₜ[Q] D ℂ Q (a * t + b * u) = 0`.

Rewrite using `[hpair, ha, hb]`. Conclude with `hg`. Establish `hmem : a * t + b * u ∈ RingHom.ker (algebraMap Q (ResidueField Q))`. Rewrite using `[hker]`. Conclude with `add_mem (Ideal.mul_mem_left _ _ htm) (Ideal.mul_mem_left _ _ hum)`.

Establish `hsq : a * t + b * u ∈ maximalIdeal Q ^ 2`. Establish `h1 : (RingHom.ker (algebraMap Q (ResidueField Q))).toCotangent ⟨_, hmem⟩ = 0` using `hinj (by rw [hkc, map_zero]; exact hg')`. Establish `h2 : a * t + b * u ∈ RingHom.ker (algebraMap Q (ResidueField Q)) ^ 2` using `(Ideal.toCotangent_eq_zero _ _).mp h1`. Rewrite `h2` using `[hker]`. Then use the resulting hypothesis. Establish `ham : a ∈ maximalIdeal Q` using `mem_maximalIdeal_of_mul_add_mul_mem_sq hspan hdim hsq`.

Establish `hbm : b ∈ maximalIdeal Q`. Use `mem_maximalIdeal_of_mul_add_mul_mem_sq (t := u) (u := t) (a := b) (b := a) (by rw [Set.pair_comm]; exact hspan) hdim ?_` and prove the remaining obligations. Rewrite using `[add_comm]`. Conclude with `hsq`. Establish `h0 : g 0 = 0` using `by rw [← ha]; exact (residue_eq_zero_iff a).mpr ham`.

Establish `h1 : g (Fin.succ 0) = 0` using `by rw [← hb]; exact (residue_eq_zero_iff b).mpr hbm`. Introduce `i`. Use `Fin.cases h0 (fun j => Fin.cases h1 (fun k => hrest k) j) i` and prove the remaining obligations. Use `haveI : Module.FinitePresentation Q Ω[Q⁄ℂ] := Module.finitePresentation_of_finite Q _`. Take `⟨b, hb⟩` from `Module.exists_basis_of_basis_baseChange (R := Q) (fun i => D ℂ Q (v i)) hli hsp (Module.Flat.rTensor_preserves_injective_linearMap (maximalIdeal Q).subtype Subtype.val_injective)`.

Conclude with `isFreeGen_dForm v b hb`.
-/
theorem isFreeGen_dForm_regularPair_cons : ∀ {L : Type} [Field L] (cL : ℂ →+* L) (Q : Subring L)
    (hQ : IsLocModel cL Q) (t u : Q),
    Ideal.span {t, u} = (letI := hQ.isLocalRing; IsLocalRing.maximalIdeal Q) →
    ringKrullDim Q = 2 →
    ∃ (m : ℕ) (z : Fin m → Q),
      (∀ P : MvPolynomial (Fin m) ℂ, P ≠ 0 →
        IsUnit (MvPolynomial.eval₂ (cL.codRestrict Q hQ.const_mem) z P)) ∧
      IsFreeGen Q (dForm (cL.codRestrict Q hQ.const_mem)
        (Fin.cons t (Fin.cons u z : Fin (m + 1) → Q) : Fin (m + 2) → Q)) := by
  intro L _ cL Q hQ t u hspan hdim
  letI := hQ.isLocalRing
  letI : Algebra ℂ Q := (cL.codRestrict Q hQ.const_mem).toAlgebra
  haveI : Algebra.EssFiniteType ℂ Q := hQ.essFiniteType
  haveI : IsNoetherianRing Q := Algebra.EssFiniteType.isNoetherianRing ℂ Q
  haveI : IsRegularLocalRing Q := by
    refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le Q ?_
    rw [hdim, ← hspan]
    have h1 := Submodule.spanFinrank_span_le_ncard_of_finite (R := Q) (Set.toFinite ({t, u} : Set Q))
    have h2 : ({t, u} : Set Q).ncard ≤ 2 := (Set.ncard_insert_le _ _).trans (by simp)
    exact_mod_cast h1.trans h2
  haveI : Algebra.FormallySmooth ℂ Q := formallySmooth_of_isRegularLocalRing_of_perfectField ℂ Q
  have hs : Function.Surjective (algebraMap Q (ResidueField Q)) := residue_surjective
  haveI : Algebra.EssFiniteType ℂ (ResidueField Q) := .comp ℂ Q _
  have hinj := (Algebra.FormallySmooth.kerCotangentToTensor_injective_iff (R := ℂ) hs).mpr
    inferInstance
  have hker : RingHom.ker (algebraMap Q (ResidueField Q)) = maximalIdeal Q := ker_residue
  have htm : t ∈ maximalIdeal Q := hspan ▸ Ideal.subset_span (by simp)
  have hum : u ∈ maximalIdeal Q := hspan ▸ Ideal.subset_span (by simp)
  have ht0 : algebraMap Q (ResidueField Q) t = 0 := (residue_eq_zero_iff t).mpr htm
  have hu0 : algebraMap Q (ResidueField Q) u = 0 := (residue_eq_zero_iff u).mpr hum

  obtain ⟨s, hsb⟩ := exists_isTranscendenceBasis ℂ (ResidueField Q)
  haveI := hsb.isAlgebraic_field
  haveI : Algebra.IsSeparable
      (IntermediateField.adjoin ℂ (Set.range ((↑) : s → ResidueField Q))) (ResidueField Q) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  obtain ⟨bκ, hbκ⟩ := exists_basis_kaehler_of_algebraicIndependent hsb.1
  haveI : Finite s := Module.Finite.finite_basis bκ
  let e : Fin (Nat.card s) ≃ s := (Finite.equivFin s).symm
  let b' := bκ.reindex e.symm
  have hb' : ∀ i, b' i = D ℂ (ResidueField Q) (e i) := fun i => by
    rw [Basis.reindex_apply, Equiv.symm_symm, hbκ]
  let z : Fin (Nat.card s) → Q := fun i => Function.surjInv hs (e i : ResidueField Q)
  have hz : ∀ i, algebraMap Q (ResidueField Q) (z i) = e i := fun i => Function.surjInv_eq hs _
  refine ⟨Nat.card s, z, fun P hP => ?_, ?_⟩
  · have e1 : algebraMap Q (ResidueField Q) (MvPolynomial.eval₂ (cL.codRestrict Q hQ.const_mem) z P)
        = MvPolynomial.aeval (fun i => (e i : ResidueField Q)) P := by
      rw [show (fun i => (e i : ResidueField Q)) = algebraMap Q (ResidueField Q) ∘ z from
        funext fun i => (hz i).symm, MvPolynomial.aeval_algebraMap_apply]
      rfl
    refine (residue_ne_zero_iff_isUnit _).mp ?_
    change algebraMap Q (ResidueField Q) _ ≠ 0
    rw [e1]
    exact fun h0 => hP ((algebraicIndependent_iff.1 (hsb.1.comp e e.injective)) P h0)
  · let v : Fin (Nat.card s + 2) → Q := Fin.cons t (Fin.cons u z : Fin (Nat.card s + 1) → Q)
    let w : Fin (Nat.card s + 2) → (ResidueField Q) ⊗[Q] Ω[Q⁄ℂ] := TensorProduct.mk Q (ResidueField Q) Ω[Q⁄ℂ] 1 ∘ fun i => D ℂ Q (v i)
    have hw0 : w 0 = (1 : (ResidueField Q)) ⊗ₜ[Q] D ℂ Q t := rfl
    have hw1 : w (Fin.succ 0) = (1 : (ResidueField Q)) ⊗ₜ[Q] D ℂ Q u := rfl
    have hwz : ∀ i : Fin (Nat.card s), w i.succ.succ = (1 : (ResidueField Q)) ⊗ₜ[Q] D ℂ Q (z i) := fun i => rfl
    have hmb : ∀ x : Q, mapBaseChange ℂ Q (ResidueField Q) ((1 : (ResidueField Q)) ⊗ₜ[Q] D ℂ Q x) = D ℂ (ResidueField Q) (algebraMap Q (ResidueField Q) x) :=
      fun x => by rw [mapBaseChange_tmul, one_smul, map_D]
    have hpair : ∀ a b : Q, (1 : (ResidueField Q)) ⊗ₜ[Q] D ℂ Q (a * t + b * u) =
        algebraMap Q (ResidueField Q) a • w 0 + algebraMap Q (ResidueField Q) b • w (Fin.succ 0) := fun a b => by
      rw [hw0, hw1]
      simp only [map_add, Derivation.leibniz, TensorProduct.tmul_add, TensorProduct.tmul_smul]
      rw [← algebraMap_smul (ResidueField Q) t, ← algebraMap_smul (ResidueField Q) u, ht0, hu0]
      simp only [zero_smul, add_zero, algebraMap_smul]
    have hkc : ∀ x (hx : x ∈ RingHom.ker (algebraMap Q (ResidueField Q))),
        kerCotangentToTensor ℂ Q (ResidueField Q) ((RingHom.ker (algebraMap Q (ResidueField Q))).toCotangent ⟨x, hx⟩) =
          (1 : (ResidueField Q)) ⊗ₜ[Q] D ℂ Q x := fun x hx => kerCotangentToTensor_toCotangent _ _ _ _

    have hsp : Submodule.span (ResidueField Q) (Set.range w) = ⊤ := by
      rw [eq_top_iff]
      intro y _
      let c := b'.repr (mapBaseChange ℂ Q (ResidueField Q) y)
      have hy0 : mapBaseChange ℂ Q (ResidueField Q) (y - ∑ i, c i • w i.succ.succ) = 0 := by
        rw [map_sub, map_sum, sub_eq_zero]
        conv_lhs => rw [← b'.sum_repr (mapBaseChange ℂ Q (ResidueField Q) y)]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, hwz, hmb, hz, hb']
      obtain ⟨c', hc'⟩ := (exact_kerCotangentToTensor_mapBaseChange ℂ Q (ResidueField Q) hs _).mp hy0
      obtain ⟨⟨x, hx⟩, rfl⟩ := Ideal.toCotangent_surjective _ c'
      have hx' := hx
      rw [hker, ← hspan, Ideal.mem_span_pair] at hx'
      obtain ⟨a, b, rfl⟩ := hx'
      rw [hkc, hpair] at hc'
      have hy : y = (algebraMap Q (ResidueField Q) a • w 0 + algebraMap Q (ResidueField Q) b • w (Fin.succ 0)) + ∑ i, c i • w i.succ.succ := by
        rw [hc', sub_add_cancel]
      rw [hy]
      refine add_mem (add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Fin.succ 0, rfl⟩)))
        (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))

    have hli : LinearIndependent (ResidueField Q) w := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at hg
      have hφ := congrArg (mapBaseChange ℂ Q (ResidueField Q)) hg
      simp only [map_add, map_sum, map_smul, map_zero] at hφ
      rw [hw0, hmb, ht0, Derivation.map_zero, smul_zero, zero_add] at hφ
      rw [hw1, hmb, hu0, Derivation.map_zero, smul_zero, zero_add] at hφ
      simp only [hwz, hmb, hz, ← hb'] at hφ
      have hrest : ∀ i : Fin (Nat.card s), g i.succ.succ = 0 :=
        Fintype.linearIndependent_iff.mp b'.linearIndependent (fun i => g i.succ.succ) hφ
      simp only [hrest, zero_smul, Finset.sum_const_zero, add_zero] at hg
      obtain ⟨a, ha⟩ := hs (g 0)
      obtain ⟨b, hb⟩ := hs (g (Fin.succ 0))
      have hg' : (1 : (ResidueField Q)) ⊗ₜ[Q] D ℂ Q (a * t + b * u) = 0 := by
        rw [hpair, ha, hb]
        exact hg
      have hmem : a * t + b * u ∈ RingHom.ker (algebraMap Q (ResidueField Q)) := by
        rw [hker]
        exact add_mem (Ideal.mul_mem_left _ _ htm) (Ideal.mul_mem_left _ _ hum)
      have hsq : a * t + b * u ∈ maximalIdeal Q ^ 2 := by
        have h1 : (RingHom.ker (algebraMap Q (ResidueField Q))).toCotangent ⟨_, hmem⟩ = 0 :=
          hinj (by rw [hkc, map_zero]; exact hg')
        have h2 : a * t + b * u ∈ RingHom.ker (algebraMap Q (ResidueField Q)) ^ 2 :=
          (Ideal.toCotangent_eq_zero _ _).mp h1
        rwa [hker] at h2
      have ham : a ∈ maximalIdeal Q := mem_maximalIdeal_of_mul_add_mul_mem_sq hspan hdim hsq
      have hbm : b ∈ maximalIdeal Q := by
        refine mem_maximalIdeal_of_mul_add_mul_mem_sq (t := u) (u := t) (a := b) (b := a)
          (by rw [Set.pair_comm]; exact hspan) hdim ?_
        rw [add_comm]; exact hsq
      have h0 : g 0 = 0 := by rw [← ha]; exact (residue_eq_zero_iff a).mpr ham
      have h1 : g (Fin.succ 0) = 0 := by rw [← hb]; exact (residue_eq_zero_iff b).mpr hbm
      intro i
      refine Fin.cases h0 (fun j => Fin.cases h1 (fun k => hrest k) j) i
    haveI : Module.FinitePresentation Q Ω[Q⁄ℂ] := Module.finitePresentation_of_finite Q _
    obtain ⟨b, hb⟩ := Module.exists_basis_of_basis_baseChange (R := Q) (fun i => D ℂ Q (v i)) hli hsp
      (Module.Flat.rTensor_preserves_injective_linearMap (maximalIdeal Q).subtype
        Subtype.val_injective)
    exact isFreeGen_dForm v b hb

end GlobalTheory.FieldPair
