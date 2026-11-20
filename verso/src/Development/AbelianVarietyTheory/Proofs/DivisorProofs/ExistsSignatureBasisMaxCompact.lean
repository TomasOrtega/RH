import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaxCompactConjugate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixMulVecBasis

noncomputable section

open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct

namespace GlobalTheory.MaxCptFrame

/- English proof (translation)
Rewrite using `[← Matrix.exp_conjTranspose, conjTranspose_smul, hX, star_trivial, smul_neg, ← Matrix.exp_add_of_commute _ _ (Commute.refl (s • X)).neg_left, neg_add_cancel, NormedSpace.exp_zero]`.
-/
theorem exp_unitary_of_skew {n : ℕ} {X : Matrix (Fin n) (Fin n) ℂ} (hX : Xᴴ = -X) (s : ℝ) :
    (NormedSpace.exp (s • X))ᴴ * NormedSpace.exp (s • X) = 1 := by
  rw [← Matrix.exp_conjTranspose, conjTranspose_smul, hX, star_trivial, smul_neg,
    ← Matrix.exp_add_of_commute _ _ (Commute.refl (s • X)).neg_left, neg_add_cancel, NormedSpace.exp_zero]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ h n J hJ K hK w τ`. Use `choose c ε hc using Frames.exists_arch_frame h hJ`. Take `⟨a, ha, e⟩` from `GlobalTheory.MaxCptConj.exists_conj_majCpt h (fun w => ⟨ε w, hc w⟩) hK`. Establish `one : (1 : Matrix (Fin n) (Fin n) (w.Completion ⊗[F] E)).map (infEmb τ) = 1` using `Matrix.map_one _ (map_zero _) (map_one _)`. Establish `inj` using `Matrix.map_injective (m := Fin n) (n := Fin n) (infEmb_bijective h τ).1`.

Use `set g : GL (Fin n) (w.Completion ⊗[F] E) := matHom _ σ J (projArch σ J w a)⁻¹ * c w with hg`. Establish `hinv : (g⁻¹).1.map (infEmb τ) = (g.1.map (infEmb τ))⁻¹` using `(Matrix.inv_eq_left_inv (by rw [← Matrix.map_mul, Units.inv_mul, one])).symm`. Establish `hu : IsUnit (g.1.map (infEmb τ))` using `IsUnit.of_mul_eq_one ((g⁻¹).1.map (infEmb τ)) (by rw [← Matrix.map_mul, Units.mul_inv, one])`. Use `⟨g.1.map (infEmb τ), ε w, ?_, fun Z ζ hζ hZ s => ?_⟩` and prove the remaining obligations. Establish `h2 : (JR w.Completion J).map (infEmb τ) = J.map τ.1` using `by ext r s; simp [JR, inclR]`.

Establish `h3 : Formalism.UG.cT (sigR _ σ) (matHom _ σ J (projArch σ J w a)⁻¹).1 * JR w.Completion J * (matHom _ σ J (projArch σ J w a)⁻¹).1 = JR w.Completion J` using `((projArch σ J w a)⁻¹).2`. Establish `h4` using `congrArg (Matrix.map · (infEmb τ)) h3`. Establish `h5` using `congrArg (Matrix.map · (infEmb τ)) (hc w)`. Simplify using `only [Matrix.map_mul, Frames.map_cT_sigR h, h2] at h4 h5`. Rewrite `h5` using `[Matrix.diagonal_map (map_zero _)]`.

Rewrite using `[hg, Units.val_mul, Matrix.map_mul, conjTranspose_mul]`. Use `Eq.trans ?_ (h5.trans ?_)` and prove the remaining obligations. Use `conv_rhs => rw [← h4]`. Simplify using `only [Matrix.mul_assoc]`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Apply the tactic sequence `split_ifs <;> simp`. Take `⟨y, hy, hyZ⟩` from `hζ s`. Rewrite using `[e, hy, mem_majCpt]`. Use `⟨mul_mem (mul_mem ha (mem_infPts.2 (projFin_embArch _ _ _ _))) (inv_mem ha), fun v => ?_⟩` and prove the remaining obligations.

Distinguish the cases in `hv : v = w`. Substitute `hv` using the available equality. Rewrite using `[map_mul, map_mul, map_inv, projArch_embArch_self, mem_stabArch]`. Establish `h1 : (c v)⁻¹ * matHom _ σ J (projArch σ J v a * y * (projArch σ J v a)⁻¹) * c v = g⁻¹ * matHom _ σ J y * g`. Simplify using `only [hg, map_mul, map_inv]`.

Use `group`. Rewrite using `[h1]`. Express the relevant statement in the definitionally equal form `Formalism.UG.cT _ (g⁻¹ * matHom _ σ J y * g).1 * 1 * (g⁻¹ * matHom _ σ J y * g).1 = 1`. Use `inj ?_` and prove the remaining obligations. Establish `h2 : (g⁻¹ * matHom _ σ J y * g).1.map (infEmb τ) = NormedSpace.exp (s • ((g.1.map (infEmb τ))⁻¹ * Z * g.1.map (infEmb τ)))`.

Rewrite using `[← Matrix.smul_mul, ← Matrix.mul_smul, Matrix.exp_conj' _ _ hu, ← hyZ, GlobalTheory.Orb.archMat_apply, Units.val_mul, Units.val_mul, Matrix.map_mul, Matrix.map_mul, hinv]`. Use `beta_reduce`. Rewrite using `[mul_one, Matrix.map_mul, Frames.map_cT_sigR h, one, h2]`. Conclude with `exp_unitary_of_skew hZ s`. Rewrite using `[map_mul, map_mul, map_inv, projArch_embArch_ne _ _ hv, mul_one, mul_inv_cancel]`.

Conclude with `one_mem _`.
-/
theorem exists_frame_lines_mem : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ K : Subgroup (GAd σ J), GlobalTheory.UAut.IsMaxCpt σ J K → ∀ (w : InfinitePlace F) (τ : EmbOver E w),
      ∃ (R : Matrix (Fin n) (Fin n) ℂ) (ε : Fin n → Bool),
        Rᴴ * J.map τ.1 * R = Matrix.diagonal (fun i => if ε i then (1 : ℂ) else -1) ∧
        ∀ (Z : Matrix (Fin n) (Fin n) ℂ) (ζ : ℝ → GAd σ J), GlobalTheory.LeviHC.IsLineOf σ J τ Z ζ →
          (R⁻¹ * Z * R)ᴴ = -(R⁻¹ * Z * R) → ∀ s, ζ s ∈ K := by
  intro F E _ _ _ _ _ σ h n J hJ K hK w τ
  choose c ε hc using Frames.exists_arch_frame h hJ
  obtain ⟨a, ha, e⟩ := GlobalTheory.MaxCptConj.exists_conj_majCpt h (fun w => ⟨ε w, hc w⟩) hK
  have one : (1 : Matrix (Fin n) (Fin n) (w.Completion ⊗[F] E)).map (infEmb τ) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  have inj := Matrix.map_injective (m := Fin n) (n := Fin n) (infEmb_bijective h τ).1
  set g : GL (Fin n) (w.Completion ⊗[F] E) := matHom _ σ J (projArch σ J w a)⁻¹ * c w with hg
  have hinv : (g⁻¹).1.map (infEmb τ) = (g.1.map (infEmb τ))⁻¹ :=
    (Matrix.inv_eq_left_inv (by rw [← Matrix.map_mul, Units.inv_mul, one])).symm
  have hu : IsUnit (g.1.map (infEmb τ)) :=
    IsUnit.of_mul_eq_one ((g⁻¹).1.map (infEmb τ)) (by rw [← Matrix.map_mul, Units.mul_inv, one])
  refine ⟨g.1.map (infEmb τ), ε w, ?_, fun Z ζ hζ hZ s => ?_⟩
  · have h2 : (JR w.Completion J).map (infEmb τ) = J.map τ.1 := by ext r s; simp [JR, inclR]
    have h3 : Formalism.UG.cT (sigR _ σ) (matHom _ σ J (projArch σ J w a)⁻¹).1 * JR w.Completion J *
        (matHom _ σ J (projArch σ J w a)⁻¹).1 = JR w.Completion J := ((projArch σ J w a)⁻¹).2
    have h4 := congrArg (Matrix.map · (infEmb τ)) h3
    have h5 := congrArg (Matrix.map · (infEmb τ)) (hc w)
    simp only [Matrix.map_mul, Frames.map_cT_sigR h, h2] at h4 h5
    rw [Matrix.diagonal_map (map_zero _)] at h5
    rw [hg, Units.val_mul, Matrix.map_mul, conjTranspose_mul]
    refine Eq.trans ?_ (h5.trans ?_)
    · conv_rhs => rw [← h4]
      simp only [Matrix.mul_assoc]
    · congr 1
      funext i
      split_ifs <;> simp
  · obtain ⟨y, hy, hyZ⟩ := hζ s
    rw [e, hy, mem_majCpt]
    refine ⟨mul_mem (mul_mem ha (mem_infPts.2 (projFin_embArch _ _ _ _))) (inv_mem ha), fun v => ?_⟩
    by_cases hv : v = w
    · subst hv
      rw [map_mul, map_mul, map_inv, projArch_embArch_self, mem_stabArch]
      have h1 : (c v)⁻¹ * matHom _ σ J (projArch σ J v a * y * (projArch σ J v a)⁻¹) * c v =
          g⁻¹ * matHom _ σ J y * g := by
        simp only [hg, map_mul, map_inv]; group
      rw [h1]
      change Formalism.UG.cT _ (g⁻¹ * matHom _ σ J y * g).1 * 1 * (g⁻¹ * matHom _ σ J y * g).1 = 1
      refine inj ?_
      have h2 : (g⁻¹ * matHom _ σ J y * g).1.map (infEmb τ) =
          NormedSpace.exp (s • ((g.1.map (infEmb τ))⁻¹ * Z * g.1.map (infEmb τ))) := by
        rw [← Matrix.smul_mul, ← Matrix.mul_smul, Matrix.exp_conj' _ _ hu, ← hyZ, GlobalTheory.Orb.archMat_apply,
          Units.val_mul, Units.val_mul, Matrix.map_mul, Matrix.map_mul, hinv]
      beta_reduce
      rw [mul_one, Matrix.map_mul, Frames.map_cT_sigR h, one, h2]
      exact exp_unitary_of_skew hZ s
    · rw [map_mul, map_mul, map_inv, projArch_embArch_ne _ _ hv, mul_one, mul_inv_cancel]
      exact one_mem _

end GlobalTheory.MaxCptFrame

end
