import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel

open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

namespace GlobalTheory.SymplecticPeriods

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Establish `hinj : Function.Injective F`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `u hu`. Establish `h0 : ∀ v : (ι → ℚ) × (ι → ℚ), u.1 ⬝ᵥ v.2 - u.2 ⬝ᵥ v.1 = 0` using `fun v => by`. Rewrite using `[← hF, hu]`.

Simplify using the standard rewrite rules. Use extensionality with `i`. Simplify using `using h0 (0, Pi.single i 1)`. Simplify using `using h0 (Pi.single i 1, 0)`. Establish `hsurj : Function.Surjective F` using `LinearMap.injective_iff_surjective.mp hinj`.

Use `choose r hr using fun j : ι ⊕ ι => hsurj ((fun i => (Pi.single j 1 : ι ⊕ ι → ℚ) (Sum.inr i)), fun i => (Pi.single j 1 : ι ⊕ ι → ℚ) (Sum.inl i))`. Set `σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ` to `Matrix.of fun j => Sum.elim (fun i => (r j).2 i) (fun i => (r j).1 i)`. Establish `hrow : ∀ j, ((fun i => σ j (Sum.inr i)), (fun i => σ j (Sum.inl i))) = r j` using `fun j => rfl`. Use `⟨σ, ?_, fun j => by rw [hrow]; exact hr j⟩` and prove the remaining obligations. Rewrite using `[SymplecticGroup.mem_iff]`.

Use extensionality with `a b`. Establish `e1 : (σ * Matrix.J ι ℚ * σᵀ) a b = (r a).1 ⬝ᵥ (r b).2 - (r a).2 ⬝ᵥ (r b).1`. Simplify using `[Matrix.mul_apply, Matrix.J, Fintype.sum_sum_type, σ, dotProduct, Matrix.one_apply, Finset.sum_neg_distrib, sub_eq_add_neg, add_comm]`. Rewrite using `[e1, ← hF, hr, hr]`. Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b <;>`.

Simplify using `[Matrix.J, dotProduct, Pi.single_apply, Matrix.one_apply, eq_comm]`.
-/
theorem exists_symplectic_rows (F : ((ι → ℚ) × (ι → ℚ)) →ₗ[ℚ] ((ι → ℚ) × (ι → ℚ)))
    (hF : ∀ u v, (F u).1 ⬝ᵥ (F v).2 - (F u).2 ⬝ᵥ (F v).1 = u.1 ⬝ᵥ v.2 - u.2 ⬝ᵥ v.1) :
    ∃ σ ∈ Matrix.symplecticGroup ι ℚ, ∀ j,
      F (fun i => σ j (Sum.inr i), fun i => σ j (Sum.inl i)) =
        (fun i => (Pi.single j 1 : ι ⊕ ι → ℚ) (Sum.inr i),
          fun i => (Pi.single j 1 : ι ⊕ ι → ℚ) (Sum.inl i)) := by
  classical

  have hinj : Function.Injective F := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have h0 : ∀ v : (ι → ℚ) × (ι → ℚ), u.1 ⬝ᵥ v.2 - u.2 ⬝ᵥ v.1 = 0 := fun v => by
      rw [← hF, hu]; simp
    ext i
    · simpa using h0 (0, Pi.single i 1)
    · simpa using h0 (Pi.single i 1, 0)
  have hsurj : Function.Surjective F := LinearMap.injective_iff_surjective.mp hinj

  choose r hr using fun j : ι ⊕ ι => hsurj
    ((fun i => (Pi.single j 1 : ι ⊕ ι → ℚ) (Sum.inr i)), fun i => (Pi.single j 1 : ι ⊕ ι → ℚ) (Sum.inl i))
  let σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ := Matrix.of fun j => Sum.elim (fun i => (r j).2 i) (fun i => (r j).1 i)
  have hrow : ∀ j, ((fun i => σ j (Sum.inr i)), (fun i => σ j (Sum.inl i))) = r j := fun j => rfl
  refine ⟨σ, ?_, fun j => by rw [hrow]; exact hr j⟩
  rw [SymplecticGroup.mem_iff]
  ext a b

  have e1 : (σ * Matrix.J ι ℚ * σᵀ) a b = (r a).1 ⬝ᵥ (r b).2 - (r a).2 ⬝ᵥ (r b).1 := by
    simp [Matrix.mul_apply, Matrix.J, Fintype.sum_sum_type, σ, dotProduct, Matrix.one_apply,
      Finset.sum_neg_distrib, sub_eq_add_neg, add_comm]
  rw [e1, ← hF, hr, hr]
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Matrix.J, dotProduct, Pi.single_apply, Matrix.one_apply, eq_comm]

/- English proof (translation)
Take `⟨σ, hσ, hrows⟩` from `exists_symplectic_rows F hF`. Use `⟨σ, hσ, fun τ hτ τ' M hτ' hM => ?_⟩` and prove the remaining obligations. Establish `hτs : τ.IsSymm` using `hτ.1`. Use `set X := spDen σ τ with hX`. Use `set Y := qm σ.toBlocks₁₁ * τ + qm σ.toBlocks₁₂ with hY`.

Establish `colX : ∀ k, (fun l => Xᵀ l k) = qv (fun i => σ (Sum.inr k) (Sum.inr i)) + τ *ᵥ qv (fun i => σ (Sum.inr k) (Sum.inl i))`. Introduce `k`. Use function extensionality and compare the values at `l`. Simplify using `only [hX, spDen, Matrix.transpose_apply, Matrix.add_apply, Matrix.mul_apply, qm, Matrix.map_apply, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.of_apply, Pi.add_apply, qv, Matrix.mulVec, dotProduct]`. Rewrite using `[add_comm]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[hτs.apply m l, mul_comm]`. Establish `columnBlock : ∀ k, (fun l => Yᵀ l k) = qv (fun i => σ (Sum.inl k) (Sum.inr i)) + τ *ᵥ qv (fun i => σ (Sum.inl k) (Sum.inl i))`. Introduce `k`.

Use function extensionality and compare the values at `l`. Simplify using `only [hY, Matrix.transpose_apply, Matrix.add_apply, Matrix.mul_apply, qm, Matrix.map_apply, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.of_apply, Pi.add_apply, qv, Matrix.mulVec, dotProduct]`. Rewrite using `[add_comm]`. Use `congr 1`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations.

Rewrite using `[hτs.apply m l, mul_comm]`. Establish `hA : M * Xᵀ = 1`. Use extensionality with `i k`. Establish `h` using `hM (fun i => σ (Sum.inr k) (Sum.inr i), fun i => σ (Sum.inr k) (Sum.inl i))`. Rewrite `h` using `[hrows (Sum.inr k), ← colX k]`.

Rewrite using `[show (M * Xᵀ) i k = (M *ᵥ fun l => Xᵀ l k) i from rfl, congrFun h i]`. Simplify using `[qv, Pi.single_apply, Matrix.one_apply, Matrix.mulVec, dotProduct]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hB : τ' = M * Yᵀ`. Use extensionality with `i k`.

Establish `h` using `hM (fun i => σ (Sum.inl k) (Sum.inr i), fun i => σ (Sum.inl k) (Sum.inl i))`. Rewrite `h` using `[hrows (Sum.inl k), ← columnBlock k]`. Rewrite using `[show (M * Yᵀ) i k = (M *ᵥ fun l => Yᵀ l k) i from rfl, congrFun h i]`. Simplify using `[qv, Pi.single_apply, Matrix.mulVec, dotProduct]`. Rewrite using `[Finset.sum_eq_single k (fun j _ hj => by simp [hj]) (by simp)]`.

Simplify using the standard rewrite rules. Establish `hMeq : M = (X⁻¹)ᵀ`. Rewrite using `[Matrix.transpose_nonsing_inv, Matrix.inv_eq_left_inv hA]`. Use `⟨?_, hMeq⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_symplectic_action (ι : Type) [Fintype ι] [DecidableEq ι]
    (F : ((ι → ℚ) × (ι → ℚ)) →ₗ[ℚ] ((ι → ℚ) × (ι → ℚ)))
    (hF : ∀ u v, (F u).1 ⬝ᵥ (F v).2 - (F u).2 ⬝ᵥ (F v).1 = u.1 ⬝ᵥ v.2 - u.2 ⬝ᵥ v.1) :
    ∃ σ ∈ Matrix.symplecticGroup ι ℚ, ∀ τ ∈ Siegel ι, ∀ τ' M : Matrix ι ι ℂ, τ'.IsSymm →
      (∀ u, M *ᵥ (qv u.1 + τ *ᵥ qv u.2) = qv (F u).1 + τ' *ᵥ qv (F u).2) →
      τ' = spAct σ τ ∧ M = ((spDen σ τ)⁻¹)ᵀ := by
  obtain ⟨σ, hσ, hrows⟩ := exists_symplectic_rows F hF
  refine ⟨σ, hσ, fun τ hτ τ' M hτ' hM => ?_⟩
  have hτs : τ.IsSymm := hτ.1
  set X := spDen σ τ with hX
  set Y := qm σ.toBlocks₁₁ * τ + qm σ.toBlocks₁₂ with hY

  have colX : ∀ k, (fun l => Xᵀ l k) =
      qv (fun i => σ (Sum.inr k) (Sum.inr i)) + τ *ᵥ qv (fun i => σ (Sum.inr k) (Sum.inl i)) := by
    intro k; funext l
    simp only [hX, spDen, Matrix.transpose_apply, Matrix.add_apply, Matrix.mul_apply, qm, Matrix.map_apply,
      Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.of_apply, Pi.add_apply, qv, Matrix.mulVec, dotProduct]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hτs.apply m l, mul_comm]
  have columnBlock : ∀ k, (fun l => Yᵀ l k) =
      qv (fun i => σ (Sum.inl k) (Sum.inr i)) + τ *ᵥ qv (fun i => σ (Sum.inl k) (Sum.inl i)) := by
    intro k; funext l
    simp only [hY, Matrix.transpose_apply, Matrix.add_apply, Matrix.mul_apply, qm, Matrix.map_apply,
      Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.of_apply, Pi.add_apply, qv, Matrix.mulVec, dotProduct]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hτs.apply m l, mul_comm]

  have hA : M * Xᵀ = 1 := by
    ext i k
    have h := hM (fun i => σ (Sum.inr k) (Sum.inr i), fun i => σ (Sum.inr k) (Sum.inl i))
    rw [hrows (Sum.inr k), ← colX k] at h
    rw [show (M * Xᵀ) i k = (M *ᵥ fun l => Xᵀ l k) i from rfl, congrFun h i]
    simp [qv, Pi.single_apply, Matrix.one_apply, Matrix.mulVec, dotProduct]
    split_ifs <;> simp
  have hB : τ' = M * Yᵀ := by
    ext i k
    have h := hM (fun i => σ (Sum.inl k) (Sum.inr i), fun i => σ (Sum.inl k) (Sum.inl i))
    rw [hrows (Sum.inl k), ← columnBlock k] at h
    rw [show (M * Yᵀ) i k = (M *ᵥ fun l => Yᵀ l k) i from rfl, congrFun h i]
    simp [qv, Pi.single_apply, Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single k (fun j _ hj => by simp [hj]) (by simp)]
    simp
  have hMeq : M = (X⁻¹)ᵀ := by
    rw [Matrix.transpose_nonsing_inv, Matrix.inv_eq_left_inv hA]
  refine ⟨?_, hMeq⟩
  calc τ' = τ'ᵀ := hτ'.eq.symm
    _ = (M * Yᵀ)ᵀ := by rw [← hB]
    _ = Y * Mᵀ := by rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    _ = spAct σ τ := by rw [hMeq, Matrix.transpose_transpose]; rfl

end GlobalTheory.SymplecticPeriods
