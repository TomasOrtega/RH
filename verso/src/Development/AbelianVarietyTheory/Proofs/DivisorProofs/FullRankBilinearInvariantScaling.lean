import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledBoxRadiiAtEntry
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentInvariantFunctionalTwoDim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClopenIntegrabilityFullRankOrbit

open ValuativeRel Matrix GlobalTheory.SplitFlip GlobalTheory.FullRankCoinv GlobalTheory.RankCoinv GlobalTheory.NormalCore

noncomputable section
namespace GlobalTheory.NormalCore.PvTransport

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Establish `h1` using `Reduce.lact_mem ν g (JacReduce.fullRk_rtr h hΨ)`. Establish `hc : ((ν (gdet g) : ℂ) * apow (gdet g) ((d : ℂ) / 2)) ≠ 0` using `mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _)`. Establish `h2` using `(fullRk k n d).smul_mem ((ν (gdet g) : ℂ) * apow (gdet g) ((d : ℂ) / 2))⁻¹ h1`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `Y`.

Simplify using `only [lact, JacReduce.rtr_apply, Pi.smul_apply, smul_eq_mul, Matrix.mul_assoc]`. Rewrite using `[← mul_assoc, inv_mul_cancel₀ hc, one_mul]`.
-/
theorem comp_mem {n d : ℕ} (ν : kˣ →* ℂˣ) (g : GL (Fin n) k) (h : GL (Fin d) k)
    {Ψ : Matrix (Fin n) (Fin d) k → ℂ} (hΨ : Ψ ∈ fullRk k n d) :
    (fun Y => Ψ ((g.1)ᵀ * Y * h.1)) ∈ fullRk k n d := by
  have h1 := Reduce.lact_mem ν g (JacReduce.fullRk_rtr h hΨ)
  have hc : ((ν (gdet g) : ℂ) * apow (gdet g) ((d : ℂ) / 2)) ≠ 0 :=
    mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _)
  have h2 := (fullRk k n d).smul_mem ((ν (gdet g) : ℂ) * apow (gdet g) ((d : ℂ) / 2))⁻¹ h1
  convert h2 using 1
  funext Y
  simp only [lact, JacReduce.rtr_apply, Pi.smul_apply, smul_eq_mul, Matrix.mul_assoc]
  rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

/- English proof (translation)
Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem alg_id (X c : ℂ) (m : ℝ) (hm : (m : ℂ) ≠ 0) (hc : c ≠ 0) :
    X = ((m⁻¹ : ℝ) : ℂ) * c⁻¹ * ((m : ℂ) * (c * X)) := by
  push_cast
  field_simp

end GlobalTheory.NormalCore.PvTransport

open GlobalTheory.NormalCore.PvTransport in

/- English proof (translation)
Introduce `k _ _ _ _ n d ν Bf hG hH g h B₁ B₂`. Establish `hc0 : ((ν (gdet g) : ℂ) * apow (gdet g) ((d : ℂ) / 2)) ≠ 0` using `mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _)`. Establish `e₁ : ({Y | (g.1)ᵀ * Y * h.1 ∈ B₁}.indicator (1 : Matrix (Fin n) (Fin d) k → ℂ)) = fun Y => B₁.indicator 1 ((g.1)ᵀ * Y * h.1)`. Use function extensionality and compare the values at `Y`. Simplify using `only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]`.

Establish `e₂ : ({Y | Y * h.1 ∈ B₂}.indicator (1 : Matrix (Fin n) (Fin d) k → ℂ)) = fun Y => B₂.indicator 1 (Y * h.1)`. Use function extensionality and compare the values at `Y`. Simplify using `only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]`. Distinguish the cases in `hB : B₁.indicator (1 : Matrix (Fin n) (Fin d) k → ℂ) ∈ fullRk k n d ∧ B₂.indicator (1 : Matrix (Fin n) (Fin d) k → ℂ) ∈ fullRk k n d`. Take `⟨m, hm0, hm⟩` from `hH h`.

Establish `hm' : (m : ℂ) ≠ 0` using `by exact_mod_cast hm0.ne'`. Use `⟨m⁻¹, inv_pos.2 hm0, ?_⟩` and prove the remaining obligations. Set `P₁ : fullRk k n d` to `⟨_, hB.1⟩`. Set `P₂ : fullRk k n d` to `⟨_, hB.2⟩`. Set `Φ : fullRk k n d` to `⟨_, JacReduce.fullRk_rtr h hB.1⟩`.

Set `Ψ₂' : fullRk k n d` to `⟨_, JacReduce.fullRk_rtr h hB.2⟩`. Establish `hS₁ : {Y | (g.1)ᵀ * Y * h.1 ∈ B₁}.indicator (1 : Matrix (Fin n) (Fin d) k → ℂ) ∈ fullRk k n d`. Rewrite using `[e₁]`. Conclude with `comp_mem ν g h hB.1`. Establish `hS₂ : {Y | Y * h.1 ∈ B₂}.indicator (1 : Matrix (Fin n) (Fin d) k → ℂ) ∈ fullRk k n d`.

Rewrite using `[e₂]`. Conclude with `JacReduce.fullRk_rtr h hB.2`. Set `S₁ : fullRk k n d` to `⟨_, hS₁⟩`. Set `S₂ : fullRk k n d` to `⟨_, hS₂⟩`. Establish `hpvB : pv Bf B₁ B₂ = Bf P₁ P₂` using `pv_eq Bf P₁ P₂ rfl rfl`.

Establish `hpvS : pv Bf {Y | (g.1)ᵀ * Y * h.1 ∈ B₁} {Y | Y * h.1 ∈ B₂} = Bf S₁ S₂` using `pv_eq Bf S₁ S₂ rfl rfl`. Establish `hmB` using `hm P₁ Φ P₂ Ψ₂' (JacReduce.rtr_apply h _) (JacReduce.rtr_apply h _)`. Establish `hS₂eq : S₂ = Ψ₂'` using `Subtype.ext (by`. Express the relevant statement in the definitionally equal form `{Y | Y * h.1 ∈ B₂}.indicator (1 : Matrix (Fin n) (Fin d) k → ℂ) = JacReduce.rtr h (B₂.indicator 1)`. Rewrite using `[e₂, JacReduce.rtr_apply])`.

Establish `hlact : (((ν (gdet g) : ℂ) * apow (gdet g) ((d : ℂ) / 2)) • S₁).1 = lact ν g Φ.1`. Use function extensionality and compare the values at `Y`. Express the relevant statement in the definitionally equal form `((ν (gdet g) : ℂ) * apow (gdet g) ((d : ℂ) / 2)) • {Y | (g.1)ᵀ * Y * h.1 ∈ B₁}.indicator (1 : Matrix (Fin n) (Fin d) k → ℂ) Y = lact ν g (JacReduce.rtr h (B₁.indicator 1)) Y`. Rewrite using `[e₁]`. Simplify using `only [lact, JacReduce.rtr_apply, smul_eq_mul, Matrix.mul_assoc]`.

Establish `hg` using `hG g Φ _ Ψ₂' hlact`. Rewrite `hg` using `[map_smul, LinearMap.smul_apply, smul_eq_mul]`. Rewrite using `[hpvS, hpvB, ← hmB, hS₂eq, ← hg]`. Conclude with `alg_id _ _ _ hm' hc0`. Use `⟨1, one_pos, ?_⟩` and prove the remaining obligations.

Rewrite using `[show pv Bf B₁ B₂ = 0 from by rw [pv, dif_neg hB], mul_zero, pv, dif_neg]`. Introduce and unpack `⟨h₁, h₂⟩`. Apply `hB` to reduce the goal to its premises. Establish `key : ∀ Y : Matrix (Fin n) (Fin d) k, (g.1)ᵀ * (((g⁻¹).1)ᵀ * Y * (h⁻¹).1) * h.1 = Y`. Introduce `Y`.

Simplify using `only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one, Matrix.one_mul]`. Establish `keyh : ∀ Y : Matrix (Fin n) (Fin d) k, Y * (h⁻¹).1 * h.1 = Y`. Introduce `Y`. Rewrite using `[Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]`.

Prove the components needed by the constructor for the conclusion. Establish `h3` using `comp_mem ν g⁻¹ h⁻¹ h₁`. Rewrite `h3` using `[e₁]`. Use `h3 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `Y`.

Simplify using `only [key]`. Establish `h3` using `JacReduce.fullRk_rtr h⁻¹ h₂`. Rewrite `h3` using `[e₂, JacReduce.rtr_apply]`. Use `h3 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `Y`.

Simplify using `only [keyh]`.
-/
theorem GlobalTheory.NormalCore.pv_transport : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ) (ν : kˣ →* ℂˣ) (Bf : fullRk k n d →ₗ[ℂ] fullRk k n d →ₗ⋆[ℂ] ℂ), (∀ (g : GL (Fin n) k) (Ψ₁ Ψ₁' Ψ₂ : fullRk k n d), Ψ₁'.1 = lact ν g Ψ₁.1 → Bf Ψ₁' Ψ₂ = Bf Ψ₁ Ψ₂) → (∀ h : GL (Fin d) k, ∃ m : ℝ, 0 < m ∧ ∀ Ψ₁ Ψ₁' Ψ₂ Ψ₂' : fullRk k n d, Ψ₁'.1 = (fun Y => Ψ₁.1 (Y * h.1)) → Ψ₂'.1 = (fun Y => Ψ₂.1 (Y * h.1)) → (m : ℂ) * Bf Ψ₁' Ψ₂' = Bf Ψ₁ Ψ₂) → ∀ (g : GL (Fin n) k) (h : GL (Fin d) k) (B₁ B₂ : Set (Matrix (Fin n) (Fin d) k)), ∃ r : ℝ, 0 < r ∧ pv Bf {Y | (g.1)ᵀ * Y * h.1 ∈ B₁} {Y | Y * h.1 ∈ B₂} = (r : ℂ) * ((ν (gdet g) : ℂ) * apow (gdet g) ((d : ℂ) / 2))⁻¹ * pv Bf B₁ B₂ := by
  intro k _ _ _ _ n d ν Bf hG hH g h B₁ B₂
  classical
  have hc0 : ((ν (gdet g) : ℂ) * apow (gdet g) ((d : ℂ) / 2)) ≠ 0 :=
    mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _)
  have e₁ : ({Y | (g.1)ᵀ * Y * h.1 ∈ B₁}.indicator (1 : Matrix (Fin n) (Fin d) k → ℂ)) =
      fun Y => B₁.indicator 1 ((g.1)ᵀ * Y * h.1) := by
    funext Y; simp only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
  have e₂ : ({Y | Y * h.1 ∈ B₂}.indicator (1 : Matrix (Fin n) (Fin d) k → ℂ)) =
      fun Y => B₂.indicator 1 (Y * h.1) := by
    funext Y; simp only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
  by_cases hB : B₁.indicator (1 : Matrix (Fin n) (Fin d) k → ℂ) ∈ fullRk k n d ∧
      B₂.indicator (1 : Matrix (Fin n) (Fin d) k → ℂ) ∈ fullRk k n d
  · obtain ⟨m, hm0, hm⟩ := hH h
    have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm0.ne'
    refine ⟨m⁻¹, inv_pos.2 hm0, ?_⟩
    let P₁ : fullRk k n d := ⟨_, hB.1⟩
    let P₂ : fullRk k n d := ⟨_, hB.2⟩
    let Φ : fullRk k n d := ⟨_, JacReduce.fullRk_rtr h hB.1⟩
    let Ψ₂' : fullRk k n d := ⟨_, JacReduce.fullRk_rtr h hB.2⟩
    have hS₁ : {Y | (g.1)ᵀ * Y * h.1 ∈ B₁}.indicator (1 : Matrix (Fin n) (Fin d) k → ℂ) ∈ fullRk k n d := by
      rw [e₁]; exact comp_mem ν g h hB.1
    have hS₂ : {Y | Y * h.1 ∈ B₂}.indicator (1 : Matrix (Fin n) (Fin d) k → ℂ) ∈ fullRk k n d := by
      rw [e₂]; exact JacReduce.fullRk_rtr h hB.2
    let S₁ : fullRk k n d := ⟨_, hS₁⟩
    let S₂ : fullRk k n d := ⟨_, hS₂⟩
    have hpvB : pv Bf B₁ B₂ = Bf P₁ P₂ := pv_eq Bf P₁ P₂ rfl rfl
    have hpvS : pv Bf {Y | (g.1)ᵀ * Y * h.1 ∈ B₁} {Y | Y * h.1 ∈ B₂} = Bf S₁ S₂ := pv_eq Bf S₁ S₂ rfl rfl
    have hmB := hm P₁ Φ P₂ Ψ₂' (JacReduce.rtr_apply h _) (JacReduce.rtr_apply h _)
    have hS₂eq : S₂ = Ψ₂' := Subtype.ext (by
      change {Y | Y * h.1 ∈ B₂}.indicator (1 : Matrix (Fin n) (Fin d) k → ℂ) = JacReduce.rtr h (B₂.indicator 1)
      rw [e₂, JacReduce.rtr_apply])
    have hlact : (((ν (gdet g) : ℂ) * apow (gdet g) ((d : ℂ) / 2)) • S₁).1 = lact ν g Φ.1 := by
      funext Y
      change ((ν (gdet g) : ℂ) * apow (gdet g) ((d : ℂ) / 2)) •
          {Y | (g.1)ᵀ * Y * h.1 ∈ B₁}.indicator (1 : Matrix (Fin n) (Fin d) k → ℂ) Y =
        lact ν g (JacReduce.rtr h (B₁.indicator 1)) Y
      rw [e₁]
      simp only [lact, JacReduce.rtr_apply, smul_eq_mul, Matrix.mul_assoc]
    have hg := hG g Φ _ Ψ₂' hlact
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul] at hg
    rw [hpvS, hpvB, ← hmB, hS₂eq, ← hg]
    exact alg_id _ _ _ hm' hc0
  · refine ⟨1, one_pos, ?_⟩
    rw [show pv Bf B₁ B₂ = 0 from by rw [pv, dif_neg hB], mul_zero, pv, dif_neg]
    rintro ⟨h₁, h₂⟩
    apply hB
    have key : ∀ Y : Matrix (Fin n) (Fin d) k, (g.1)ᵀ * (((g⁻¹).1)ᵀ * Y * (h⁻¹).1) * h.1 = Y := by
      intro Y
      simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
      rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one, Matrix.one_mul]
    have keyh : ∀ Y : Matrix (Fin n) (Fin d) k, Y * (h⁻¹).1 * h.1 = Y := by
      intro Y
      rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
    constructor
    · have h3 := comp_mem ν g⁻¹ h⁻¹ h₁
      rw [e₁] at h3
      convert h3 using 1
      funext Y
      simp only [key]
    · have h3 := JacReduce.fullRk_rtr h⁻¹ h₂
      rw [e₂, JacReduce.rtr_apply] at h3
      convert h3 using 1
      funext Y
      simp only [keyh]
