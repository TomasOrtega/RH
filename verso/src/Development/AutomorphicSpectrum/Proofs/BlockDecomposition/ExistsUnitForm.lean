import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.lift_levelP_alt₂
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalEqTwistNormalised
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantHermitianFormCuspidalRep
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspRapidDecaySiegelGL

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.LFun PositivityTheory.JacquetShalikaLocal

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.JSUnit

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

/- English proof (translation)
Use `Submodule.nontrivial_iff_ne_bot.2 π.ne_bot` as an intermediate fact. Take `⟨x, hx⟩` from `exists_ne (0 : π.V)`. Establish `h1 : π.op (.fin (GeneralLinearGroup.scalar (Fin a) z)) x = ((ω.1 (finId E z) : ℂˣ) : ℂ) • x` using `hω z x`. Establish `h2` using `hi (GeneralLinearGroup.scalar (Fin a) z) x x`. Rewrite `h2` using `[h1]`.

Generalize the expression as in `((ω.1 (finId E z) : ℂˣ) : ℂ) = c at h2 ⊢`. Simplify using `only [map_smulₛₗ, map_smul, LinearMap.smul_apply, smul_eq_mul] at h2`. Establish `hne : H x x ≠ 0` using `fun e => by`. Establish `h` using `hp x hx`. Simplify using `[e] at h`.

Establish `h3 : starRingEnd ℂ c * c = 1` using `mul_right_cancel₀ hne (by linear_combination h2)`. Rewrite `h3` using `[Complex.conj_mul']`. Establish `h4 : ‖c‖ ^ 2 = 1` using `by exact_mod_cast h3`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h4`.
-/
theorem norm_central (π : CuspSub E a) (H : π.V →ₗ⋆[ℂ] π.V →ₗ[ℂ] ℂ) (hp : ∀ φ, φ ≠ 0 → 0 < (H φ φ).re)
    (hi : ∀ k φ ψ, H (π.op (.fin k) φ) (π.op (.fin k) ψ) = H φ ψ) {ω : HChar E} (hω : π.HasCentChar ω) (z) :
    ‖((ω.1 (finId E z) : ℂˣ) : ℂ)‖ = 1 := by
  have := Submodule.nontrivial_iff_ne_bot.2 π.ne_bot
  obtain ⟨x, hx⟩ := exists_ne (0 : π.V)
  have h1 : π.op (.fin (GeneralLinearGroup.scalar (Fin a) z)) x = ((ω.1 (finId E z) : ℂˣ) : ℂ) • x := hω z x
  have h2 := hi (GeneralLinearGroup.scalar (Fin a) z) x x
  rw [h1] at h2
  generalize ((ω.1 (finId E z) : ℂˣ) : ℂ) = c at h2 ⊢
  simp only [map_smulₛₗ, map_smul, LinearMap.smul_apply, smul_eq_mul] at h2
  have hne : H x x ≠ 0 := fun e => by
    have h := hp x hx
    simp [e] at h
  have h3 : starRingEnd ℂ c * c = 1 := mul_right_cancel₀ hne (by linear_combination h2)
  rw [Complex.conj_mul'] at h3
  have h4 : ‖c‖ ^ 2 = 1 := by exact_mod_cast h3
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h4

/- English proof (translation)
Establish `e : (π.twist χ).twist χ⁻¹ = π`. Rewrite using `[← CuspSub.twist_mul, mul_inv_cancel, CuspSub.twist_one]`. Establish `h2` using `hω.twist χ⁻¹`. Rewrite `h2` using `[e]`. Establish `h3` using `norm_central π H hp hi h2 (GeneralLinearGroup.det (locGL E a w g))`.

Rewrite `h3` using `[finId_det_locGL]`. Generalize the expression as in `GeneralLinearGroup.det g = u at h3 ⊢`. Establish `h4 : ‖((ω.loc w u : ℂˣ) : ℂ)‖ = 1` using `hu _`. Establish `h5 : (ω * χ⁻¹ ^ a).loc w u = ω.loc w u * (χ.loc w u)⁻¹ ^ a` using `rfl`. Express the relevant statement in the definitionally equal form `‖(((ω * χ⁻¹ ^ a).loc w u : ℂˣ) : ℂ)‖ = 1 at h3`.

Rewrite `h3` using `[h5]`. Simplify using `only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, norm_mul, norm_pow, norm_inv, h4, one_mul] at h3`. Establish `h6` using `(pow_eq_one_iff_of_nonneg (by positivity) ha).1 h3`. Conclude with `inv_eq_one.1 h6`.
-/
theorem norm_loc (π : CuspSub E a) (H : π.V →ₗ⋆[ℂ] π.V →ₗ[ℂ] ℂ) (hp : ∀ φ, φ ≠ 0 → 0 < (H φ φ).re)
    (hi : ∀ k φ ψ, H (π.op (.fin k) φ) (π.op (.fin k) ψ) = H φ ψ) (χ : HChar E) {ω : HChar E} (hu : ω.IsUnitary)
    (hω : (π.twist χ).HasCentChar ω) (ha : a ≠ 0) (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin a) (w.adicCompletion E)) :
    ‖((χ.loc w (GeneralLinearGroup.det g) : ℂˣ) : ℂ)‖ = 1 := by
  have e : (π.twist χ).twist χ⁻¹ = π := by
    rw [← CuspSub.twist_mul, mul_inv_cancel, CuspSub.twist_one]
  have h2 := hω.twist χ⁻¹
  rw [e] at h2
  have h3 := norm_central π H hp hi h2 (GeneralLinearGroup.det (locGL E a w g))
  rw [finId_det_locGL] at h3
  generalize GeneralLinearGroup.det g = u at h3 ⊢
  have h4 : ‖((ω.loc w u : ℂˣ) : ℂ)‖ = 1 := hu _
  have h5 : (ω * χ⁻¹ ^ a).loc w u = ω.loc w u * (χ.loc w u)⁻¹ ^ a := rfl
  change ‖(((ω * χ⁻¹ ^ a).loc w u : ℂˣ) : ℂ)‖ = 1 at h3
  rw [h5] at h3
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, norm_mul, norm_pow, norm_inv, h4,
    one_mul] at h3
  have h6 := (pow_eq_one_iff_of_nonneg (by positivity) ha).1 h3
  exact inv_eq_one.1 h6

/- English proof (translation)
Introduce `E _ _ _ a π hu w`. Take `⟨ω, hωu, hω⟩` from `hu`. Rewrite `hω` using `[CG.hasCentChar_mk]`. Take `⟨π₀, χ, hn, rfl⟩` from `GlobalTheory.CompanionTheory.TwistNorm.exists_twist_normalised π`. Take `⟨H, h1, h2, h3, -, -⟩` from `GlobalTheory.GelfandKazhdanHerm.exists_invariant_hermitian GlobalTheory.CompanionTheory.CuspFinGL.cuspFormsBoundedGL E a π₀ hn`.

Set `T` to `π₀.toTwist χ`. Establish `hT : ∀ g x, (π₀.twist χ).locRep w g (T x) = ((χ.loc w (GeneralLinearGroup.det g) : ℂˣ) : ℂ) • T (π₀.locRep w g x)` using `fun g x => by`. Rewrite using `[CuspSub.locRep_eq, CuspSub.op_toTwist, opAdd, zero_smul, add_zero, map_smul, opMul, CuspSub.chiDet_locGL]`. Both sides reduce to the same expression. Establish `hn1 : ∀ g : GL (Fin a) (w.adicCompletion E), ‖((χ.loc w (GeneralLinearGroup.det g) : ℂˣ) : ℂ)‖ = 1` using `fun g => by`.

Break down `eq_or_ne a 0 with rfl | ha` into its components or cases. Rewrite using `[show GeneralLinearGroup.det g = 1 from Units.ext (by simp [Matrix.det_isEmpty]), map_one]`. Simplify using the standard rewrite rules. Conclude with `norm_loc π₀ H h2 h3 χ hωu hω ha w g`. Use `⟨(H.comp T.symm.toLinearMap).compl₂ T.symm.toLinearMap, ?_⟩` and prove the remaining obligations.

Use `And.intro (fun u v => ?_) (And.intro (fun u hu => ?_) fun g u v => ?_)` and prove the remaining obligations. Simplify using `using h1 (T.symm u) (T.symm v)`. Conclude with `h2 _ (T.symm.map_ne_zero_iff.2 hu)`. Take `⟨u, rfl⟩` from `T.surjective u`. Take `⟨v, rfl⟩` from `T.surjective v`.

Rewrite using `[hT, hT]`. Generalize the expression as in `hc : ((χ.loc w (GeneralLinearGroup.det g) : ℂˣ) : ℂ) = c`. Establish `hcc : starRingEnd ℂ c * c = 1`. Rewrite using `[Complex.conj_mul', ← hc, hn1 g]`. Simplify using the standard rewrite rules.

Simplify using `only [LinearMap.compl₂_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, map_smulₛₗ, map_smul, LinearMap.smul_apply, LinearEquiv.symm_apply_apply, smul_eq_mul]`. Rewrite using `[CuspSub.locRep_eq, h3, ← mul_assoc, RingHom.id_apply, mul_comm c, hcc, one_mul]`.
-/
theorem exists_unit_form : G1 := by
  intro E _ _ _ a π hu w
  obtain ⟨ω, hωu, hω⟩ := hu
  rw [CG.hasCentChar_mk] at hω
  obtain ⟨π₀, χ, hn, rfl⟩ := GlobalTheory.CompanionTheory.TwistNorm.exists_twist_normalised π
  obtain ⟨H, h1, h2, h3, -, -⟩ := GlobalTheory.GelfandKazhdanHerm.exists_invariant_hermitian
    GlobalTheory.CompanionTheory.CuspFinGL.cuspFormsBoundedGL E a π₀ hn
  let T := π₀.toTwist χ
  have hT : ∀ g x, (π₀.twist χ).locRep w g (T x) =
      ((χ.loc w (GeneralLinearGroup.det g) : ℂˣ) : ℂ) • T (π₀.locRep w g x) := fun g x => by
    rw [CuspSub.locRep_eq, CuspSub.op_toTwist, opAdd, zero_smul, add_zero, map_smul, opMul, CuspSub.chiDet_locGL]
    rfl
  have hn1 : ∀ g : GL (Fin a) (w.adicCompletion E), ‖((χ.loc w (GeneralLinearGroup.det g) : ℂˣ) : ℂ)‖ = 1 := fun g => by
    rcases eq_or_ne a 0 with rfl | ha
    · rw [show GeneralLinearGroup.det g = 1 from Units.ext (by simp [Matrix.det_isEmpty]), map_one]
      simp
    · exact norm_loc π₀ H h2 h3 χ hωu hω ha w g
  refine ⟨(H.comp T.symm.toLinearMap).compl₂ T.symm.toLinearMap, ?_⟩
  refine And.intro (fun u v => ?_) (And.intro (fun u hu => ?_) fun g u v => ?_)
  · simpa using h1 (T.symm u) (T.symm v)
  · exact h2 _ (T.symm.map_ne_zero_iff.2 hu)
  · obtain ⟨u, rfl⟩ := T.surjective u
    obtain ⟨v, rfl⟩ := T.surjective v
    rw [hT, hT]
    generalize hc : ((χ.loc w (GeneralLinearGroup.det g) : ℂˣ) : ℂ) = c
    have hcc : starRingEnd ℂ c * c = 1 := by
      rw [Complex.conj_mul', ← hc, hn1 g]
      simp
    simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, map_smulₛₗ, map_smul, LinearMap.smul_apply,
      LinearEquiv.symm_apply_apply, smul_eq_mul]
    rw [CuspSub.locRep_eq, h3, ← mul_assoc, RingHom.id_apply, mul_comm c, hcc, one_mul]

end GlobalTheory.CompanionTheory.JSUnit

end
