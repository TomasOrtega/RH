import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SetIntegralNormRmulLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousIntegralInvMulOfLocallyIntegrable

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalBoundedInfiniteCompactFinitePolyCountStatement

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory

namespace GlobalTheory

/- English proof (translation)
Introduce `E _ _ _ a`. Take `⟨m, hm⟩` from `GlobalTheory.T.rational_boundedInfinite_compactFinite_polyCount E`. Use `⟨m * (a * a), fun Kf hKf => ?_⟩` and prove the remaining obligations. Set `Kf' : Set (Af E)` to `⋃ i : Fin a, ⋃ j : Fin a, (fun g : GL (Fin a) (Af E) => g.val i j) '' Kf`. Establish `hc : IsCompact Kf'`.

Use `isCompact_iUnion fun i => isCompact_iUnion fun j => hKf.image ?_` and prove the remaining obligations. Conclude with `(Units.continuous_val (M := Matrix (Fin a) (Fin a) (Af E))).matrix_elem i j`. Take `⟨C, hC0, hC⟩` from `hm Kf' hc`. Use `⟨C ^ (a * a), pow_nonneg hC0 _, fun T hT => ?_⟩` and prove the remaining obligations. Take `⟨hNf, hNc⟩` from `hC T hT`.

Set `N : Set E` to `{ξ : E | ‖pInf E (algebraMap E (Ad E) ξ)‖ ≤ T ∧ pFin E (algebraMap E (Ad E) ξ) ∈ Kf'}`. Set `S : Set (GL (Fin a) E)` to `{γ : GL (Fin a) E | ‖toL (Matrix.GeneralLinearGroup.map (pInf E) (ratGL E a γ)).val‖ ≤ T ∧ Matrix.GeneralLinearGroup.map (pFin E) (ratGL E a γ) ∈ Kf}`. Express the relevant statement in the definitionally equal form `S.Finite ∧ (S.ncard : ℝ) ≤ C ^ (a * a) * T ^ (m * (a * a))`. Establish `hsub : ∀ γ ∈ S, ∀ i j, γ.val i j ∈ N`. Introduce `γ hγ i j`.

Take `⟨h1, h2⟩` from `hγ`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `he : pInf E (algebraMap E (Ad E) (γ.val i j)) = (toL (Matrix.GeneralLinearGroup.map (pInf E) (ratGL E a γ)).val) i j` using `rfl`. Rewrite using `[he]`. Conclude with `((norm_le_pi_norm _ j).trans (norm_le_pi_norm _ i)).trans h1`.

Conclude with `Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, ⟨_, h2, rfl⟩⟩⟩`. Set `F : Finset E` to `hNf.toFinset`. Set `P : Finset (Fin a → Fin a → E)` to `Fintype.piFinset fun _ => Fintype.piFinset fun _ => F`. Set `f : GL (Fin a) E → (Fin a → Fin a → E)` to `fun γ => γ.val`. Establish `hf : Function.Injective f` using `fun x y h => Units.ext h`.

Establish `himg : f '' S ⊆ (P : Set (Fin a → Fin a → E))`. Introduce and unpack `_ ⟨γ, hγ, rfl⟩`. Simplify using `only [P, F, Finset.mem_coe, Fintype.mem_piFinset, Set.Finite.mem_toFinset]`. Conclude with `fun i j => hsub γ hγ i j`. Establish `hSfin : S.Finite` using `Set.Finite.of_finite_image ((P.finite_toSet).subset himg) hf.injOn`.

Use `⟨hSfin, ?_⟩` and prove the remaining obligations. Establish `hcardP : P.card = (F.card ^ a) ^ a`. Simplify using `[P, Fintype.card_piFinset, Finset.prod_const]`. Establish `hS : S.ncard ≤ (F.card ^ a) ^ a`. Rewrite using `[← Set.ncard_image_of_injective S hf, ← hcardP, ← Set.ncard_coe_finset]`.

Conclude with `Set.ncard_le_ncard himg P.finite_toSet`. Establish `hF : (F.card : ℝ) ≤ C * T ^ m`. Rewrite using `[← Set.ncard_eq_toFinset_card N hNf]`. Conclude with `hNc`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem ratGL_bounded_count : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), ∃ m : ℕ, ∀ Kf : Set (GL (Fin a) (Af E)), IsCompact Kf → ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T → {γ : GL (Fin a) E | ‖toL (Matrix.GeneralLinearGroup.map (pInf E) (ratGL E a γ)).val‖ ≤ T ∧ Matrix.GeneralLinearGroup.map (pFin E) (ratGL E a γ) ∈ Kf}.Finite ∧ ({γ : GL (Fin a) E | ‖toL (Matrix.GeneralLinearGroup.map (pInf E) (ratGL E a γ)).val‖ ≤ T ∧ Matrix.GeneralLinearGroup.map (pFin E) (ratGL E a γ) ∈ Kf}.ncard : ℝ) ≤ C * T ^ m := by
  intro E _ _ _ a
  obtain ⟨m, hm⟩ := GlobalTheory.T.rational_boundedInfinite_compactFinite_polyCount E
  refine ⟨m * (a * a), fun Kf hKf => ?_⟩
  let Kf' : Set (Af E) := ⋃ i : Fin a, ⋃ j : Fin a, (fun g : GL (Fin a) (Af E) => g.val i j) '' Kf
  have hc : IsCompact Kf' := by
    refine isCompact_iUnion fun i => isCompact_iUnion fun j => hKf.image ?_
    exact (Units.continuous_val (M := Matrix (Fin a) (Fin a) (Af E))).matrix_elem i j
  obtain ⟨C, hC0, hC⟩ := hm Kf' hc
  refine ⟨C ^ (a * a), pow_nonneg hC0 _, fun T hT => ?_⟩
  obtain ⟨hNf, hNc⟩ := hC T hT
  let N : Set E := {ξ : E | ‖pInf E (algebraMap E (Ad E) ξ)‖ ≤ T ∧ pFin E (algebraMap E (Ad E) ξ) ∈ Kf'}
  let S : Set (GL (Fin a) E) := {γ : GL (Fin a) E | ‖toL (Matrix.GeneralLinearGroup.map (pInf E) (ratGL E a γ)).val‖ ≤ T ∧ Matrix.GeneralLinearGroup.map (pFin E) (ratGL E a γ) ∈ Kf}
  change S.Finite ∧ (S.ncard : ℝ) ≤ C ^ (a * a) * T ^ (m * (a * a))
  have hsub : ∀ γ ∈ S, ∀ i j, γ.val i j ∈ N := by
    intro γ hγ i j
    obtain ⟨h1, h2⟩ := hγ
    refine ⟨?_, ?_⟩
    · have he : pInf E (algebraMap E (Ad E) (γ.val i j)) = (toL (Matrix.GeneralLinearGroup.map (pInf E) (ratGL E a γ)).val) i j := rfl
      rw [he]
      exact ((norm_le_pi_norm _ j).trans (norm_le_pi_norm _ i)).trans h1
    · exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, ⟨_, h2, rfl⟩⟩⟩
  classical
  let F : Finset E := hNf.toFinset
  let P : Finset (Fin a → Fin a → E) := Fintype.piFinset fun _ => Fintype.piFinset fun _ => F
  let f : GL (Fin a) E → (Fin a → Fin a → E) := fun γ => γ.val
  have hf : Function.Injective f := fun x y h => Units.ext h
  have himg : f '' S ⊆ (P : Set (Fin a → Fin a → E)) := by
    rintro _ ⟨γ, hγ, rfl⟩
    simp only [P, F, Finset.mem_coe, Fintype.mem_piFinset, Set.Finite.mem_toFinset]
    exact fun i j => hsub γ hγ i j
  have hSfin : S.Finite := Set.Finite.of_finite_image ((P.finite_toSet).subset himg) hf.injOn
  refine ⟨hSfin, ?_⟩
  have hcardP : P.card = (F.card ^ a) ^ a := by
    simp [P, Fintype.card_piFinset, Finset.prod_const]
  have hS : S.ncard ≤ (F.card ^ a) ^ a := by
    rw [← Set.ncard_image_of_injective S hf, ← hcardP, ← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard himg P.finite_toSet
  have hF : (F.card : ℝ) ≤ C * T ^ m := by
    rw [← Set.ncard_eq_toFinset_card N hNf]; exact hNc
  calc (S.ncard : ℝ) ≤ ((F.card ^ a) ^ a : ℕ) := by exact_mod_cast hS
    _ = (F.card : ℝ) ^ (a * a) := by push_cast; rw [← pow_mul]
    _ ≤ (C * T ^ m) ^ (a * a) := pow_le_pow_left₀ (Nat.cast_nonneg _) hF _
    _ = C ^ (a * a) * T ^ (m * (a * a)) := by rw [mul_pow, ← pow_mul]

end GlobalTheory
