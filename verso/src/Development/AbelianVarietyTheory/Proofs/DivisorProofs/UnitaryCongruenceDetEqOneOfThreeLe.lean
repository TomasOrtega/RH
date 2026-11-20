import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualTr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetEqOneUnitaryPrincipalCongruenceLevelThree
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

open Matrix Polynomial

namespace GlobalTheory.UnitaryCongruenceDetAny

/- English proof (translation)
Introduce `E _ _ _ r M G Λ γ hM hG hfg hspan hst hcong`. Take `⟨hherm, -⟩` from `hst`. Use `set g : Matrix (Fin r) (Fin r) E := (γ : Matrix (Fin r) (Fin r) E) with hg`. Set `φ : E →+* AlgebraicClosure E` to `algebraMap E (AlgebraicClosure E)`. Establish `hM0 : (M : AlgebraicClosure E) ≠ 0` using `by exact_mod_cast (by omega : M ≠ 0)`.

Establish `hME : (M : E) ≠ 0` using `by exact_mod_cast (by omega : M ≠ 0)`. Use `set A : Matrix (Fin r) (Fin r) E := (M : E)⁻¹ • (g - 1) with hA`. Establish `hAΛ : ∀ x ∈ Λ, A *ᵥ x ∈ Λ`. Introduce `x hx`. Take `⟨y, hy, hxy⟩` from `hcong x hx`.

Establish `: A *ᵥ x = y`. Rewrite using `[hA, smul_mulVec, sub_mulVec, one_mulVec, hxy, ← Nat.cast_smul_eq_nsmul E, smul_smul, inv_mul_cancel₀ hME, one_smul]`. Rewrite using `[this]`. Conclude with `hy`. Establish `hAmap : A.map φ = (M : AlgebraicClosure E)⁻¹ • (g.map φ - 1)`.

Use extensionality with `i j`. Apply the tactic sequence `by_cases hij : i = j <;> simp [hA, Matrix.one_apply, hij]`. Establish `hroot : ∀ l ∈ (g.map φ).charpoly.roots, IsIntegral ℤ ((l - 1) / (M : AlgebraicClosure E))`. Introduce `l hl`. Establish `hdet : (scalar (Fin r) l - g.map φ).det = 0`.

Rewrite using `[← Matrix.eval_charpoly]`. Conclude with `(mem_roots'.1 hl).2`. Take `⟨u, hu, hu0⟩` from `Matrix.exists_vecMul_eq_zero_iff.2 hdet`. Apply `GlobalTheory.UnitaryCongruenceDet.isIntegral_of_left_eigen A Λ hfg hspan hAΛ _ u hu` to reduce the goal to its premises. Establish `hgu : u ᵥ* g.map φ = l • u`.

Rewrite `hu0` using `[vecMul_sub, sub_eq_zero]`. Rewrite using `[← hu0]`. Use function extensionality and compare the values at `j`. Simplify using `[scalar_apply, vecMul_diagonal, mul_comm]`. Rewrite using `[hAmap, vecMul_smul, vecMul_sub, vecMul_one, hgu]`.

Use function extensionality and compare the values at `j`. Simplify using `only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts. Take `⟨z, hz, hprod⟩` from `GlobalTheory.UnitaryCongruenceDet.prod_eq_one_add M hM0 _ hroot`. Establish `hφdet : φ g.det = 1 + M * z`.

Rewrite using `[RingHom.map_det, ← hprod]`. Conclude with `Matrix.det_eq_prod_roots_charpoly _`. Use `set z₀ : E := (g.det - 1) / (M : E) with hz₀`. Establish `hφz : φ z₀ = z`. Rewrite using `[hz₀, map_div₀, map_sub, map_one, map_natCast, hφdet]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hz₀int : IsIntegral ℤ z₀`. Establish `h1 : IsIntegral ℤ (φ z₀)` using `by rw [hφz]; exact hz`. Conclude with `(isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ E (AlgebraicClosure E)) (algebraMap E (AlgebraicClosure E)).injective).1 h1`.

Establish `hcc` using `GlobalTheory.UnitaryCongruenceDet.det_mul_cc_det G g hG hherm`. Establish `hnorm : ∀ ψ : E →+* ℂ, ‖ψ g.det‖ = 1`. Introduce `ψ`. Establish `h1` using `congrArg ψ hcc`. Rewrite `h1` using `[map_mul, map_one, cc, IsCMField.complexEmbedding_complexConj, Complex.mul_conj]`.

Establish `h2 : Complex.normSq (ψ g.det) = 1` using `by exact_mod_cast h1`. Rewrite `h2` using `[Complex.normSq_eq_norm_sq]`. Conclude with `(pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).1 (h2.trans (one_pow 2).symm)`. Establish `hsmall : ∀ ψ : E →+* ℂ, ‖ψ z₀‖ < 1`. Introduce `ψ`.

Establish `hMR : (3 : ℝ) ≤ M` using `by exact_mod_cast hM`. Rewrite using `[hz₀, map_div₀, map_sub, map_one, map_natCast, norm_div, Complex.norm_natCast, div_lt_one (by linarith)]`. Combine the equalities or inequalities in the displayed calculation. Establish `hz0 : z₀ = 0`. Assume the negation of the conclusion as `hne`.

Set `α : 𝓞 E` to `⟨z₀, hz₀int⟩`. Establish `hα : α ≠ 0`. Introduce `h`. Apply `hne` to reduce the goal to its premises. Use `congrArg (fun a : 𝓞 E => (a : E)) h` as an intermediate fact.

Conclude with `this`. Take `⟨σ, hσ⟩` from `NumberField.exists_conjugate_one_le_norm hα`. Conclude with `absurd hσ (not_le.2 (hsmall σ))`. Establish `: g.det - 1 = 0`. Establish `h` using `hz0`.

Rewrite `h` using `[hz₀, div_eq_zero_iff]`. Conclude with `h.resolve_right hME`. Conclude with `sub_eq_zero.1 this`.
-/
theorem det_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (γ : GL (Fin r) E), 3 ≤ M → G.det ≠ 0 → Λ.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → IsUStab G Λ γ → (∀ x ∈ Λ, ∃ y ∈ Λ, (γ : Matrix (Fin r) (Fin r) E).mulVec x - x = M • y) → (γ : Matrix (Fin r) (Fin r) E).det = 1 := by
  intro E _ _ _ r M G Λ γ hM hG hfg hspan hst hcong
  classical
  obtain ⟨hherm, -⟩ := hst
  set g : Matrix (Fin r) (Fin r) E := (γ : Matrix (Fin r) (Fin r) E) with hg
  let φ : E →+* AlgebraicClosure E := algebraMap E (AlgebraicClosure E)
  have hM0 : (M : AlgebraicClosure E) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  have hME : (M : E) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  set A : Matrix (Fin r) (Fin r) E := (M : E)⁻¹ • (g - 1) with hA
  have hAΛ : ∀ x ∈ Λ, A *ᵥ x ∈ Λ := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hcong x hx
    have : A *ᵥ x = y := by
      rw [hA, smul_mulVec, sub_mulVec, one_mulVec, hxy, ← Nat.cast_smul_eq_nsmul E,
        smul_smul, inv_mul_cancel₀ hME, one_smul]
    rw [this]; exact hy
  have hAmap : A.map φ = (M : AlgebraicClosure E)⁻¹ • (g.map φ - 1) := by
    ext i j
    by_cases hij : i = j <;> simp [hA, Matrix.one_apply, hij]
  have hroot : ∀ l ∈ (g.map φ).charpoly.roots,
      IsIntegral ℤ ((l - 1) / (M : AlgebraicClosure E)) := by
    intro l hl
    have hdet : (scalar (Fin r) l - g.map φ).det = 0 := by
      rw [← Matrix.eval_charpoly]; exact (mem_roots'.1 hl).2
    obtain ⟨u, hu, hu0⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
    apply GlobalTheory.UnitaryCongruenceDet.isIntegral_of_left_eigen A Λ hfg hspan hAΛ _ u hu
    have hgu : u ᵥ* g.map φ = l • u := by
      rw [vecMul_sub, sub_eq_zero] at hu0
      rw [← hu0]
      funext j
      simp [scalar_apply, vecMul_diagonal, mul_comm]
    rw [hAmap, vecMul_smul, vecMul_sub, vecMul_one, hgu]
    funext j
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp
  obtain ⟨z, hz, hprod⟩ := GlobalTheory.UnitaryCongruenceDet.prod_eq_one_add M hM0 _ hroot
  have hφdet : φ g.det = 1 + M * z := by
    rw [RingHom.map_det, ← hprod]
    exact Matrix.det_eq_prod_roots_charpoly _

  set z₀ : E := (g.det - 1) / (M : E) with hz₀
  have hφz : φ z₀ = z := by
    rw [hz₀, map_div₀, map_sub, map_one, map_natCast, hφdet]
    field_simp
    ring
  have hz₀int : IsIntegral ℤ z₀ := by
    have h1 : IsIntegral ℤ (φ z₀) := by rw [hφz]; exact hz
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ E (AlgebraicClosure E))
      (algebraMap E (AlgebraicClosure E)).injective).1 h1

  have hcc := GlobalTheory.UnitaryCongruenceDet.det_mul_cc_det G g hG hherm
  have hnorm : ∀ ψ : E →+* ℂ, ‖ψ g.det‖ = 1 := by
    intro ψ
    have h1 := congrArg ψ hcc
    rw [map_mul, map_one, cc, IsCMField.complexEmbedding_complexConj, Complex.mul_conj] at h1
    have h2 : Complex.normSq (ψ g.det) = 1 := by exact_mod_cast h1
    rw [Complex.normSq_eq_norm_sq] at h2
    exact (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).1 (h2.trans (one_pow 2).symm)

  have hsmall : ∀ ψ : E →+* ℂ, ‖ψ z₀‖ < 1 := by
    intro ψ
    have hMR : (3 : ℝ) ≤ M := by exact_mod_cast hM
    rw [hz₀, map_div₀, map_sub, map_one, map_natCast, norm_div, Complex.norm_natCast,
      div_lt_one (by linarith)]
    calc ‖ψ g.det - 1‖ ≤ ‖ψ g.det‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [hnorm, norm_one]; norm_num
      _ < M := by linarith
  have hz0 : z₀ = 0 := by
    by_contra hne
    let α : 𝓞 E := ⟨z₀, hz₀int⟩
    have hα : α ≠ 0 := by
      intro h; apply hne
      have := congrArg (fun a : 𝓞 E => (a : E)) h
      exact this
    obtain ⟨σ, hσ⟩ := NumberField.exists_conjugate_one_le_norm hα
    exact absurd hσ (not_le.2 (hsmall σ))
  have : g.det - 1 = 0 := by
    have h := hz0
    rw [hz₀, div_eq_zero_iff] at h
    exact h.resolve_right hME
  exact sub_eq_zero.1 this

end GlobalTheory.UnitaryCongruenceDetAny
