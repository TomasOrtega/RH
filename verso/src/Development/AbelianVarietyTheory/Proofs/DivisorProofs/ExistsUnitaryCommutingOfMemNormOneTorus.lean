import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusOfSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralSummandGoodPlaceIndicator
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical

noncomputable section
namespace GlobalTheory.KapOrb

/- English proof (translation)
Introduce `E _ _ _ w K e B u x n γ ψ hψ s hs`. Take `⟨hsl, hu, hh⟩` from `hψ`. Establish `hs' : (s : B.A) * B.σ (s : B.A) = 1` using `hs`. Set `Lm : B.A → (Fin n → w.adicCompletion E) →ₗ[w.adicCompletion E] (Fin n → w.adicCompletion E)` to `fun a => { toFun := fun v => ψ (a * ψ.symm v) map_add' := by intro v v'; simp [mul_add] map_smul' := by`. Introduce `c v`.

Establish `h1 : ψ.symm (c • v) = e.symm c • ψ.symm v`. Apply `ψ.injective` to reduce the goal to its premises. Rewrite using `[ψ.apply_symm_apply, hsl, ψ.apply_symm_apply, e.apply_symm_apply]`. Simplify using `only [RingHom.id_apply]`. Rewrite using `[h1, Algebra.mul_smul_comm, hsl, e.apply_symm_apply] }`.

Establish `hLm : ∀ a y, Lm a (ψ y) = ψ (a * y)`. Introduce `a y`. Simplify using `[Lm]`. Establish `hLmul : ∀ a b, Lm a ∘ₗ Lm b = Lm (a * b)`. Introduce `a b`.

Use extensionality with `v`. Simplify using `[Lm, mul_assoc]`. Establish `hLone : Lm 1 = LinearMap.id`. Use extensionality with `v`. Simplify using `[Lm]`.

Set `h : GLw n w` to `⟨LinearMap.toMatrix' (Lm (s : B.A)), LinearMap.toMatrix' (Lm ((s⁻¹ : B.Aˣ) : B.A)), by rw [← LinearMap.toMatrix'_comp, hLmul, Units.mul_inv, hLone, LinearMap.toMatrix'_id], by rw [← LinearMap.toMatrix'_comp, hLmul, Units.inv_mul, hLone, LinearMap.toMatrix'_id]⟩`. Establish `hmv : ∀ v, h.val *ᵥ v = Lm (s : B.A) v` using `fun v => LinearMap.toMatrix'_mulVec _ v`. Establish `hpres : ∀ v v', stdH w (h.val *ᵥ v) (h.val *ᵥ v') = stdH w v v'`. Introduce `v v'`. Take `⟨y, rfl⟩` from `ψ.surjective v`.

Take `⟨z, rfl⟩` from `ψ.surjective v'`. Rewrite using `[hmv, hmv, hLm, hLm, hh, hh]`. Use `congr 1`. Unfold `GlobalTheory.UnitLemma.InvAlg.herm`. Use `congr 1`.

Rewrite using `[map_mul]`. Combine the equalities or inequalities in the displayed calculation. Use `⟨h, ?_, ?_, ?_⟩` and prove the remaining obligations. Unfold `UL split_ifs`. Conclude with `Subgroup.mem_top _`.

Use `show cT (cj w) h.val * 1 * h.val = 1`. Use extensionality with `i j`. Establish `hp` using `hpres (Pi.single j 1) (Pi.single i 1)`. Rewrite `hp` using `[Matrix.mulVec_single_one, Matrix.mulVec_single_one]`. Rewrite using `[Matrix.mul_one, Matrix.mul_apply, Matrix.one_apply]`.

Simplify using `only [stdH, Matrix.transpose_apply, Matrix.col_apply] at hp`. Simplify using `only [cT, Matrix.transpose_apply, Matrix.map_apply]`. Rewrite using `[Finset.sum_congr rfl (fun k _ => mul_comm (cj w (h.val k i)) (h.val k j)), hp]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality.

Simplify using `[Pi.single_apply]`. Rewrite using `[if_neg hij, Finset.sum_eq_zero]`. Introduce `k _`. Distinguish the cases in `hk : k = j`. Substitute `hk` using the available equality.

Simplify using `[Pi.single_apply, Ne.symm hij, hij]`. Simplify using `[Pi.single_apply, hk]`. Apply `Units.ext` to reduce the goal to its premises. Apply `Matrix.toLin'.injective` to reduce the goal to its premises. Rewrite using `[Units.val_mul, Units.val_mul, Matrix.toLin'_mul, Matrix.toLin'_mul]`.

Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Take `⟨y, rfl⟩` from `ψ.surjective v`. Simplify using `only [LinearMap.comp_apply, Matrix.toLin'_apply]`. Rewrite using `[← hu, hmv, hmv, hLm, hLm, ← hu, mul_left_comm]`. Introduce `y`.

Rewrite using `[hmv, hLm]`.
-/
theorem exists_unitary_of_torus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E) (B : GlobalTheory.UnitLemma.InvAlg K) (u x : B.A) (n : ℕ) (γ : GLw n w) (ψ : B.A ≃+ (Fin n → w.adicCompletion E)), IsModelMap w e B u x γ ψ → ∀ s ∈ B.T, ∃ h : GLw n w, h ∈ UL n w ∧ h * γ = γ * h ∧ ∀ y, ψ ((s : B.A) * y) = h.val *ᵥ ψ y := by
  intro E _ _ _ w K e B u x n γ ψ hψ s hs
  obtain ⟨hsl, hu, hh⟩ := hψ
  have hs' : (s : B.A) * B.σ (s : B.A) = 1 := hs
  let Lm : B.A → (Fin n → w.adicCompletion E) →ₗ[w.adicCompletion E] (Fin n → w.adicCompletion E) := fun a =>
    { toFun := fun v => ψ (a * ψ.symm v)
      map_add' := by intro v v'; simp [mul_add]
      map_smul' := by
        intro c v
        have h1 : ψ.symm (c • v) = e.symm c • ψ.symm v := by
          apply ψ.injective
          rw [ψ.apply_symm_apply, hsl, ψ.apply_symm_apply, e.apply_symm_apply]
        simp only [RingHom.id_apply]
        rw [h1, Algebra.mul_smul_comm, hsl, e.apply_symm_apply] }
  have hLm : ∀ a y, Lm a (ψ y) = ψ (a * y) := by
    intro a y; simp [Lm]
  have hLmul : ∀ a b, Lm a ∘ₗ Lm b = Lm (a * b) := by
    intro a b; ext v; simp [Lm, mul_assoc]
  have hLone : Lm 1 = LinearMap.id := by
    ext v; simp [Lm]
  let h : GLw n w :=
    ⟨LinearMap.toMatrix' (Lm (s : B.A)), LinearMap.toMatrix' (Lm ((s⁻¹ : B.Aˣ) : B.A)),
      by rw [← LinearMap.toMatrix'_comp, hLmul, Units.mul_inv, hLone, LinearMap.toMatrix'_id],
      by rw [← LinearMap.toMatrix'_comp, hLmul, Units.inv_mul, hLone, LinearMap.toMatrix'_id]⟩
  have hmv : ∀ v, h.val *ᵥ v = Lm (s : B.A) v := fun v => LinearMap.toMatrix'_mulVec _ v
  have hpres : ∀ v v', stdH w (h.val *ᵥ v) (h.val *ᵥ v') = stdH w v v' := by
    intro v v'
    obtain ⟨y, rfl⟩ := ψ.surjective v
    obtain ⟨z, rfl⟩ := ψ.surjective v'
    rw [hmv, hmv, hLm, hLm, hh, hh]
    congr 1
    unfold GlobalTheory.UnitLemma.InvAlg.herm
    congr 1
    rw [map_mul]
    calc x * ((s : B.A) * y) * (B.σ (s : B.A) * B.σ z) = x * y * B.σ z * ((s : B.A) * B.σ (s : B.A)) := by ring
      _ = x * y * B.σ z := by rw [hs', mul_one]
  refine ⟨h, ?_, ?_, ?_⟩
  · unfold UL
    split_ifs
    · exact Subgroup.mem_top _
    · show cT (cj w) h.val * 1 * h.val = 1
      ext i j
      have hp := hpres (Pi.single j 1) (Pi.single i 1)
      rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one] at hp
      rw [Matrix.mul_one, Matrix.mul_apply, Matrix.one_apply]
      simp only [stdH, Matrix.transpose_apply, Matrix.col_apply] at hp
      simp only [cT, Matrix.transpose_apply, Matrix.map_apply]
      rw [Finset.sum_congr rfl (fun k _ => mul_comm (cj w (h.val k i)) (h.val k j)), hp]
      by_cases hij : i = j
      · subst hij; simp [Pi.single_apply]
      · rw [if_neg hij, Finset.sum_eq_zero]
        intro k _
        by_cases hk : k = j
        · subst hk; simp [Pi.single_apply, Ne.symm hij, hij]
        · simp [Pi.single_apply, hk]
  · apply Units.ext
    apply Matrix.toLin'.injective
    rw [Units.val_mul, Units.val_mul, Matrix.toLin'_mul, Matrix.toLin'_mul]
    refine LinearMap.ext fun v => ?_
    obtain ⟨y, rfl⟩ := ψ.surjective v
    simp only [LinearMap.comp_apply, Matrix.toLin'_apply]
    rw [← hu, hmv, hmv, hLm, hLm, ← hu, mul_left_comm]
  · intro y
    rw [hmv, hLm]

end GlobalTheory.KapOrb
