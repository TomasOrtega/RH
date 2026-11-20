import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ZetaUr
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLocallyConstantCycMod
import Development.AbelianVarietyTheory.Definitions.Foundations.IwSys2
import Development.AbelianVarietyTheory.Definitions.Foundations.IsZetaTW
import Development.AbelianVarietyTheory.Definitions.Foundations.IsZetaSystemFixedExponent
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA
open scoped Matrix MatrixGroups

namespace GlobalTheory.K4

/- English proof (translation)
Introduce `l _ Ω _ _ ε X pr W e ψ N _ x c d k g cf c₀ m Y hadd hsmul hZ r n`. Take `⟨bB, hB, b, hb, hY⟩` from `hZ r n`. Establish `hl : ‖((l : ℕ) : Qbar l)‖ ≤ 1` using `IsUltrametricDist.norm_natCast_le_one _ l`. Establish `hlm : ‖((l : ℕ) : Qbar l) ^ m‖ ≤ 1` using `by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hl`. Establish `hpr : ∀ v : X.Fn l, pr (((l : ℤ_[l]) ^ m) • v) = ((l : ℕ) : Qbar l) ^ m • pr v`.

Introduce `v`. Rewrite using `[hsmul]`. Use `congr 1`. Simplify using the standard rewrite rules. Use `⟨fun σ => ((l : ℤ_[l]) ^ m) • bB σ, ?_, fun y => ((l : ℕ) : Qbar l) ^ m • b y, ?_, ?_⟩` and prove the remaining obligations.

Introduce `σ hσ`. Take `⟨h1, h2⟩` from `hB σ hσ`. Use `⟨Submodule.smul_mem _ _ h1, fun u => ?_⟩` and prove the remaining obligations. Establish `: (((l : ℤ_[l]) ^ m) • bB σ) u - ((l : ℤ_[l]) ^ (c₀ + m)) • clsBmu X l n r N x c d k g σ u = ((l : ℤ_[l]) ^ m) • (bB σ u - ((l : ℤ_[l]) ^ c₀) • clsBmu X l n r N x c d k g σ u)`. Rewrite using `[smul_sub, smul_smul, ← pow_add, add_comm m c₀]`.

Both sides reduce to the same expression. Rewrite using `[this, LinearMap.map_smul, h2 u, smul_zero]`. Introduce `y i`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Conclude with `cf.O.mul_mem (cf.O.pow_mem (cf.O.natCast_mem l) m) (hb y i)`.

Introduce `s y`. Establish `hYf : YfB X l pr W e ψ n r N (fun σ => ((l : ℤ_[l]) ^ m) • bB σ) s y = ((l : ℕ) : Qbar l) ^ m • YfB X l pr W e ψ n r N bB s y`. Unfold `YfB GlobalTheory.KA.push`. Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_congr rfl fun z _ => ?_` and prove the remaining obligations.

Simplify using `only [hpr, Matrix.mulVec_smul]`. Rewrite using `[hYf]`. Introduce `i`. Establish `h` using `hY s y i`. Unfold `Cg at h ⊢`.

Establish `hrw : ((l : ℕ) : Qbar l) ^ m • Y r s y i - (((l : ℕ) : Qbar l) ^ m • YfB X l pr W e ψ n r N bB s y + (rhoK W e ψ s *ᵥ (((l : ℕ) : Qbar l) ^ m • b (y * (cycMod (F` using `ℚ) (Ω := Ω) l r s)⁻¹)) - ((l : ℕ) : Qbar l) ^ m • b y)) i = ((l : ℕ) : Qbar l) ^ m * (Y r s y i - (YfB X l pr W e ψ n r N bB s y + (rhoK W e ψ s *ᵥ b (y * (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹) - b y)) i) := by`. Simplify using `only [Matrix.mulVec_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Use `show ‖_‖ ≤ _`. Simplify using `only [Pi.smul_apply, smul_eq_mul] at hrw ⊢`.

Rewrite using `[hrw, norm_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem zetaSystem_exponent_raise_of_prime_pow_smul : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε)
  (pr : X.Fn l → Fin 2 → Qbar l) (W : R2 Ω l) (e : ℕ) (ψ : ZMod l → Qbar l) (N : ℕ) [NeZero N] (x : ZMod N)
  (c d k : ℕ) (g : (ZMod l)ˣ → SL(2, ℤ)) (cf : Coef l) (c₀ m : ℕ)
  (Y : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l),
  (∀ b b', pr (b + b') = pr b + pr b') →
  (∀ (a : ℤ_[l]) b, pr (a • b) = algebraMap ℚ_[l] (Qbar l) (a : ℚ_[l]) • pr b) →
  IsZetaSystemFixedExponent X l pr W e ψ N x c d k g cf c₀ Y →
  IsZetaSystemFixedExponent X l pr W e ψ N x c d k g cf (c₀ + m) (fun r s y => ((l : Qbar l) ^ m) • Y r s y) := by
  intro l _ Ω _ _ ε X pr W e ψ N _ x c d k g cf c₀ m Y hadd hsmul hZ r n
  obtain ⟨bB, hB, b, hb, hY⟩ := hZ r n
  have hl : ‖((l : ℕ) : Qbar l)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ l
  have hlm : ‖((l : ℕ) : Qbar l) ^ m‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hl
  have hpr : ∀ v : X.Fn l, pr (((l : ℤ_[l]) ^ m) • v) = ((l : ℕ) : Qbar l) ^ m • pr v := by
    intro v
    rw [hsmul]
    congr 1
    simp
  refine ⟨fun σ => ((l : ℤ_[l]) ^ m) • bB σ, ?_, fun y => ((l : ℕ) : Qbar l) ^ m • b y, ?_, ?_⟩
  · intro σ hσ
    obtain ⟨h1, h2⟩ := hB σ hσ
    refine ⟨Submodule.smul_mem _ _ h1, fun u => ?_⟩
    have : (((l : ℤ_[l]) ^ m) • bB σ) u - ((l : ℤ_[l]) ^ (c₀ + m)) • clsBmu X l n r N x c d k g σ u
        = ((l : ℤ_[l]) ^ m) • (bB σ u - ((l : ℤ_[l]) ^ c₀) • clsBmu X l n r N x c d k g σ u) := by
      rw [smul_sub, smul_smul, ← pow_add, add_comm m c₀]
      rfl
    rw [this, LinearMap.map_smul, h2 u, smul_zero]
  · intro y i
    simp only [Pi.smul_apply, smul_eq_mul]
    exact cf.O.mul_mem (cf.O.pow_mem (cf.O.natCast_mem l) m) (hb y i)
  · intro s y
    have hYf : YfB X l pr W e ψ n r N (fun σ => ((l : ℤ_[l]) ^ m) • bB σ) s y
        = ((l : ℕ) : Qbar l) ^ m • YfB X l pr W e ψ n r N bB s y := by
      unfold YfB GlobalTheory.KA.push
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      simp only [hpr, Matrix.mulVec_smul]
    rw [hYf]
    intro i
    have h := hY s y i
    unfold Cg at h ⊢
    have hrw : ((l : ℕ) : Qbar l) ^ m • Y r s y i -
        (((l : ℕ) : Qbar l) ^ m • YfB X l pr W e ψ n r N bB s y +
          (rhoK W e ψ s *ᵥ (((l : ℕ) : Qbar l) ^ m • b (y * (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹)) -
            ((l : ℕ) : Qbar l) ^ m • b y)) i
        = ((l : ℕ) : Qbar l) ^ m * (Y r s y i - (YfB X l pr W e ψ n r N bB s y +
          (rhoK W e ψ s *ᵥ b (y * (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹) - b y)) i) := by
      simp only [Matrix.mulVec_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    show ‖_‖ ≤ _
    simp only [Pi.smul_apply, smul_eq_mul] at hrw ⊢
    rw [hrw, norm_mul]
    calc _ ≤ 1 * ‖Y r s y i - (YfB X l pr W e ψ n r N bB s y +
          (rhoK W e ψ s *ᵥ b (y * (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹) - b y)) i‖ :=
          mul_le_mul_of_nonneg_right hlm (norm_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact h

end GlobalTheory.K4
