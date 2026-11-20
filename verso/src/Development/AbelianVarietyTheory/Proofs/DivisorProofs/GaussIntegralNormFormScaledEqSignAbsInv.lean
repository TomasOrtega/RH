import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnipVal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactOpenNormClosedBallQuadraticStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussIntegralNormFormNonNormCancelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussIntegralQuadraticCharEventuallyConstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasGaussIntegralCompAddEquivRescaleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactOpenSubgroupExhaustionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadExtTopologyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualBicharacterPairingOfSymmBilinFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapMulLeftEqNormSmulStatement

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

noncomputable section

namespace GlobalTheory.KSp.GaussNorm

open GlobalTheory.SplitWeil (cball)

section Ball

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/- English proof (translation)
Break down `le_total (ValuativeRel.valuation F (a : F)) (ValuativeRel.valuation F (b : F)) with h | h` into its components or cases. Conclude with `⟨b, fun x (hx : ValuativeRel.valuation F x ≤ _) => (le_trans hx h : ValuativeRel.valuation F x ≤ _), Set.Subset.rfl⟩`. Conclude with `⟨a, Set.Subset.rfl, fun x (hx : ValuativeRel.valuation F x ≤ _) => (le_trans hx h : ValuativeRel.valuation F x ≤ _)⟩`.
-/
theorem exists_cball_sup (a b : Fˣ) : ∃ s : Fˣ, cball a ⊆ cball s ∧ cball b ⊆ cball s := by
  rcases le_total (ValuativeRel.valuation F (a : F)) (ValuativeRel.valuation F (b : F)) with h | h
  · exact ⟨b, fun x (hx : ValuativeRel.valuation F x ≤ _) => (le_trans hx h : ValuativeRel.valuation F x ≤ _),
      Set.Subset.rfl⟩
  · exact ⟨a, Set.Subset.rfl,
      fun x (hx : ValuativeRel.valuation F x ≤ _) => (le_trans hx h : ValuativeRel.valuation F x ≤ _)⟩

/- English proof (translation)
Establish `hcov : K ⊆ ⋃ s : Fˣ, cball s`. Introduce `x _`. Distinguish the cases in `hx : x = 0`. Conclude with `Set.mem_iUnion.mpr ⟨1, by simp [cball, hx]⟩`. Conclude with `Set.mem_iUnion.mpr ⟨Units.mk0 x hx, by simp [cball]⟩`.

Establish `hd : Directed (· ⊆ ·) (fun s : Fˣ => cball s)`. Introduce `a b`. Take `⟨s, h1, h2⟩` from `exists_cball_sup a b`. Conclude with `⟨s, h1, h2⟩`. Conclude with `hK.elim_directed_cover _ (fun s => GlobalTheory.SplitWeil.isOpen_cball s) hcov hd`.
-/
theorem exists_cball_of_isCompact {K : Set F} (hK : IsCompact K) : ∃ s : Fˣ, K ⊆ cball s := by
  have hcov : K ⊆ ⋃ s : Fˣ, cball s := by
    intro x _
    by_cases hx : x = 0
    · exact Set.mem_iUnion.mpr ⟨1, by simp [cball, hx]⟩
    · exact Set.mem_iUnion.mpr ⟨Units.mk0 x hx, by simp [cball]⟩
  have hd : Directed (· ⊆ ·) (fun s : Fˣ => cball s) := by
    intro a b
    obtain ⟨s, h1, h2⟩ := exists_cball_sup a b
    exact ⟨s, h1, h2⟩
  exact hK.elim_directed_cover _ (fun s => GlobalTheory.SplitWeil.isOpen_cball s) hcov hd

/- English proof (translation)
Simplify using `only [cball, Set.mem_setOf_eq, Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀]`. Rewrite using `[le_inv_mul_iff₀ (by simp [zero_lt_iff])]`.
-/
theorem mul_mem_cball_iff (t s : Fˣ) (x : F) : (t : F) * x ∈ cball s ↔ x ∈ cball (t⁻¹ * s) := by
  simp only [cball, Set.mem_setOf_eq, Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀]
  rw [le_inv_mul_iff₀ (by simp [zero_lt_iff])]

end Ball

section Polar

variable {F : Type} [Field F] [CharZero F] {E : Type} [Field E] [Algebra F E] {c : E →ₐ[F] E} {δ : E}

/- English proof (translation)
Use `haveI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero`. Rewrite using `[map_sub, map_sub, hE.algebraMap_norm, hE.algebraMap_norm, hE.algebraMap_norm, map_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem algebraMap_norm_add (hE : IsQuad c δ) (x y : E) :
    algebraMap F E (Algebra.norm F (x + y) - Algebra.norm F x - Algebra.norm F y) = x * c y + y * c x := by
  haveI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  rw [map_sub, map_sub, hE.algebraMap_norm, hE.algebraMap_norm, hE.algebraMap_norm, map_add]
  ring

def polar (hE : IsQuad c δ) : E →ₗ[F] E →ₗ[F] F :=
  LinearMap.mk₂ F (fun x y => Algebra.norm F (x + y) - Algebra.norm F x - Algebra.norm F y)
    (fun x x' y => hE.algebraMap_injective (by
      simp only [map_add, algebraMap_norm_add hE]; ring))
    (fun a x y => hE.algebraMap_injective (by
      show algebraMap F E (Algebra.norm F (a • x + y) - Algebra.norm F (a • x) - Algebra.norm F y) =
        algebraMap F E (a • (Algebra.norm F (x + y) - Algebra.norm F x - Algebra.norm F y))
      rw [algebraMap_norm_add hE, smul_eq_mul, map_mul, algebraMap_norm_add hE, Algebra.smul_def, map_mul,
        AlgHom.commutes]; ring))
    (fun x y y' => hE.algebraMap_injective (by
      simp only [map_add, algebraMap_norm_add hE]; ring))
    (fun a x y => hE.algebraMap_injective (by
      show algebraMap F E (Algebra.norm F (x + a • y) - Algebra.norm F x - Algebra.norm F (a • y)) =
        algebraMap F E (a • (Algebra.norm F (x + y) - Algebra.norm F x - Algebra.norm F y))
      rw [algebraMap_norm_add hE, smul_eq_mul, map_mul, algebraMap_norm_add hE, Algebra.smul_def, map_mul,
        AlgHom.commutes]; ring))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem polar_apply (hE : IsQuad c δ) (x y : E) :
    polar hE x y = Algebra.norm F (x + y) - Algebra.norm F x - Algebra.norm F y := rfl

/- English proof (translation)
The claim follows from `algebraMap_norm_add hE x y`.
-/
theorem algebraMap_polar (hE : IsQuad c δ) (x y : E) : algebraMap F E (polar hE x y) = x * c y + y * c x :=
  algebraMap_norm_add hE x y

/- English proof (translation)
Rewrite using `[polar_apply, polar_apply, add_comm x y]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem polar_symm (hE : IsQuad c δ) (x y : E) : polar hE x y = polar hE y x := by
  rw [polar_apply, polar_apply, add_comm x y]; ring

/- English proof (translation)
Establish `h1` using `congrArg (algebraMap F E) (hy y)`. Rewrite `h1` using `[algebraMap_polar, map_zero]`. Establish `h2 : (2 : E) ≠ 0`. Rewrite using `[← map_ofNat (algebraMap F E) 2]`. Conclude with `(map_ne_zero _).mpr two_ne_zero`.

Establish `h3 : (2 : E) * (y * c y) = 0` using `by rw [two_mul]; exact h1`. Break down `mul_eq_zero.mp ((mul_eq_zero.mp h3).resolve_left h2) with h | h` into its components or cases. Conclude with `h`. Rewrite using `[← hE.invol y, h, map_zero]`.
-/
theorem polar_nondeg (hE : IsQuad c δ) (y : E) (hy : ∀ x, polar hE x y = 0) : y = 0 := by
  have h1 := congrArg (algebraMap F E) (hy y)
  rw [algebraMap_polar, map_zero] at h1
  have h2 : (2 : E) ≠ 0 := by
    rw [← map_ofNat (algebraMap F E) 2]; exact (map_ne_zero _).mpr two_ne_zero
  have h3 : (2 : E) * (y * c y) = 0 := by rw [two_mul]; exact h1
  rcases mul_eq_zero.mp ((mul_eq_zero.mp h3).resolve_left h2) with h | h
  · exact h
  · rw [← hE.invol y, h, map_zero]

/- English proof (translation)
Use `haveI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero`. Apply `hE.algebraMap_injective` to reduce the goal to its premises. Rewrite using `[algebraMap_polar, hE.algebraMap_norm, Algebra.smul_def, map_mul, AlgHom.commutes]`. Establish `h2 : algebraMap F E (2 : F)⁻¹ * 2 = 1`. Rewrite using `[← map_ofNat (algebraMap F E) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]`.

Take the linear combination `(z * c z) * h2`.
-/
theorem polar_half (hE : IsQuad c δ) (z : E) : polar hE ((2 : F)⁻¹ • z) z = Algebra.norm F z := by
  haveI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  apply hE.algebraMap_injective
  rw [algebraMap_polar, hE.algebraMap_norm, Algebra.smul_def, map_mul, AlgHom.commutes]
  have h2 : algebraMap F E (2 : F)⁻¹ * 2 = 1 := by
    rw [← map_ofNat (algebraMap F E) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]
  linear_combination (z * c z) * h2

/- English proof (translation)
Rewrite using `[polar_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem norm_add_eq (hE : IsQuad c δ) (x y : E) :
    Algebra.norm F (x + y) = Algebra.norm F x + Algebra.norm F y + polar hE x y := by
  rw [polar_apply]; ring

end Polar

end GlobalTheory.KSp.GaussNorm

namespace GlobalTheory.KSp

open GlobalTheory.KSp.GaussNorm GlobalTheory.SplitWeil

/- English proof (translation)
Introduce `F _ _ _ _ _ E _ _ _ _ c δ hE ψ hψ hψ1 hψ0 _ _ μ _`. Take `⟨hfin, htr, -, -, -, hNc, -, -⟩` from `GlobalTheory.T.quadExt_topological_properties F E c δ hE`. Use `haveI := hfin`. Use `haveI := htr`. Establish `hgood : Good E` using `GlobalTheory.T.isSelfDualCompactOpenGroup_of_finiteDimensional F E`.

Establish `hpair : IsPair fun x y => ψ (polar hE x y)` using `GlobalTheory.T.isSelfDualBicharacterPairing_of_symmBilinForm F E ψ hψ hψ1 hψ0 (polar hE) (polar_symm hE) (polar_nondeg hE)`. Use `set f : E → ℂ := fun z => ψ (Algebra.norm F z) with hf`. Establish `hlc : IsLocallyConstant f`. Establish `h` using `hpair.lc.comp_continuous (show Continuous fun z : E => ((2 : F)⁻¹ • z, z) by fun_prop)`. Establish `heq : ((fun p : E × E => ψ (polar hE p.1 p.2)) ∘ fun z : E => ((2 : F)⁻¹ • z, z)) = f`.

Use function extensionality and compare the values at `z`. Simplify using `only [Function.comp_apply, f, polar_half]`. Rewrite `h` using `[heq]`. Then use the resulting hypothesis. Establish `hf0 : f 0 = 1` using `by simp [f]`. Establish `hfadd : ∀ x y, f (x + y) = f x * f y * ψ (polar hE x y)`.

Introduce `x y`. Simplify using `only [f]`. Rewrite using `[norm_add_eq hE, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]`. Take `⟨γ, K₁, hK₁, hγ⟩` from `GlobalTheory.T.gaussIntegral_quadraticChar_eventually_const E hgood μ _ hpair f hlc hf0 hfadd`. Establish `hG : HasGauss μ f γ`.

Introduce `K hK`. Take `⟨L, hLc, hLo, hL⟩` from `hgood.large (K ∪ K₁) (hK.union hK₁)`. Conclude with `⟨L, hLc, hLo, Set.subset_union_left.trans hL, hγ L hLc hLo (Set.subset_union_right.trans hL)⟩`. Use `⟨γ, fun t => ?_⟩` and prove the remaining obligations. Distinguish the cases in `ht : t ∈ (Units.map (Algebra.norm F : E →* F)).range`.

Take `⟨w, hw⟩` from `ht`. Set `T : E ≃ₜ+ E` to `{ toFun := fun z => (w : E) * z invFun := fun z => ((w⁻¹ : Eˣ) : E) * z left_inv := fun z => by simp right_inv := fun z => by simp map_add' := fun x y => mul_add _ _ _ continuous_toFun := continuous_const.mul continuous_id continuous_invFun := continuous_const.mul continuous_id }`. Establish `hT : μ.map T = (distribHaarChar F t)⁻¹ • μ`. Establish `h` using `GlobalTheory.T.map_mul_left_eq_inv_norm_haarChar_smul F E c δ hE μ w`. Rewrite `h` using `[hw]`.

Conclude with `h`. Establish `h` using `GlobalTheory.T.hasGaussIntegral_comp_addEquiv_rescale E E μ μ T _ f γ hT hG`. Establish `e1 : (fun z : E => ψ ((t : F) * Algebra.norm F z)) = fun x => f (T x)`. Use function extensionality and compare the values at `z`. Use `show ψ ((t : F) * Algebra.norm F z) = ψ (Algebra.norm F ((w : E) * z))`.

Rewrite using `[MonoidHom.map_mul (Algebra.norm F) (w : E) z, ← hw, Units.coe_map]`. Establish `hs : sgn E t = 1` using `by rw [sgn, if_pos ⟨w, hw⟩]`. Establish `e2 : γ * (sgn E t * (((nabs F t)⁻¹ : ℝ) : ℂ)) = (((((distribHaarChar F t)⁻¹ : NNReal) : ℝ)) : ℂ) * γ`. Rewrite using `[hs, one_mul, mul_comm]`. Simplify using `[nabs]`.

Rewrite using `[e1, e2]`. Conclude with `h`. Take `⟨s₀, hcan⟩` from `GlobalTheory.T.gaussIntegral_normForm_nonNorm_cancel F E c δ hE ψ hψ hψ1 hψ0 μ t ht`. Establish `hs : sgn E t = -1` using `by rw [sgn, if_neg ht]`. Introduce `K hK`.

Take `⟨a₁, ha₁⟩` from `exists_cball_of_isCompact (hK.image hNc)`. Take `⟨a₂, ha₂⟩` from `exists_cball_of_isCompact (hK₁.image hNc)`. Take `⟨s', hs'1, hs'2⟩` from `exists_cball_sup (t * a₁) a₂`. Take `⟨s, hs1, hs2⟩` from `exists_cball_sup s' s₀`. Take `⟨L, hLeq, hLc, hLo⟩` from `GlobalTheory.T.exists_compactOpen_normClosedBall_quadratic F E c δ hE (t⁻¹ * s)`.

Take `⟨L₁, hL₁eq, hL₁c, hL₁o⟩` from `GlobalTheory.T.exists_compactOpen_normClosedBall_quadratic F E c δ hE s`. Establish `hset : {z : E | (t : F) * Algebra.norm F z ∈ cball s} = (L : Set E)`. Rewrite using `[hLeq]`. Use extensionality with `z`. Conclude with `mul_mem_cball_iff t s _`.

Establish `hK₁L₁ : K₁ ⊆ L₁`. Introduce `z hz`. Rewrite using `[hL₁eq]`. Conclude with `hs1 (hs'2 (ha₂ ⟨z, hz, rfl⟩))`. Establish `hKL : K ⊆ L`.

Introduce `z hz`. Rewrite using `[← hset]`. Establish `h1 : Algebra.norm F z ∈ cball a₁` using `ha₁ ⟨z, hz, rfl⟩`. Establish `h2 : (t : F) * Algebra.norm F z ∈ cball (t * a₁)`. Rewrite using `[mul_mem_cball_iff, inv_mul_cancel_left]`.

Conclude with `h1`. Conclude with `hs1 (hs'1 h2)`. Establish `hs₀ : (s₀ : F) ∈ cball s` using `hs2 (show ValuativeRel.valuation F (s₀ : F) ≤ ValuativeRel.valuation F (s₀ : F) from le_refl _)`. Establish `h1` using `hcan s hs₀`. Rewrite `h1` using `[← hL₁eq, hγ L₁ hL₁c hL₁o hK₁L₁, hset]`.

Use `⟨L, hLc, hLo, hKL, ?_⟩` and prove the remaining obligations. Establish `hn : (nabs F t : ℂ) ≠ 0` using `by exact_mod_cast (nabs_pos F t).ne'`. Rewrite using `[hs, Complex.ofReal_inv]`. Clear the denominators using the available nonvanishing facts. Take the linear combination `h1`.
-/
theorem hasGauss_norm_mul : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure], ∃ g : ℂ, ∀ t : Fˣ, HasGauss μ (fun z => ψ ((t : F) * Algebra.norm F z)) (g * (sgn E t * ((nabs F t)⁻¹ : ℝ))) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE ψ hψ hψ1 hψ0 _ _ μ _
  obtain ⟨hfin, htr, -, -, -, hNc, -, -⟩ := GlobalTheory.T.quadExt_topological_properties F E c δ hE
  haveI := hfin
  haveI := htr
  have hgood : Good E := GlobalTheory.T.isSelfDualCompactOpenGroup_of_finiteDimensional F E
  have hpair : IsPair fun x y => ψ (polar hE x y) :=
    GlobalTheory.T.isSelfDualBicharacterPairing_of_symmBilinForm F E ψ hψ hψ1 hψ0 (polar hE) (polar_symm hE) (polar_nondeg hE)
  set f : E → ℂ := fun z => ψ (Algebra.norm F z) with hf
  have hlc : IsLocallyConstant f := by
    have h := hpair.lc.comp_continuous (show Continuous fun z : E => ((2 : F)⁻¹ • z, z) by fun_prop)
    have heq : ((fun p : E × E => ψ (polar hE p.1 p.2)) ∘ fun z : E => ((2 : F)⁻¹ • z, z)) = f := by
      funext z; simp only [Function.comp_apply, f, polar_half]
    rwa [heq] at h
  have hf0 : f 0 = 1 := by simp [f]
  have hfadd : ∀ x y, f (x + y) = f x * f y * ψ (polar hE x y) := by
    intro x y
    simp only [f]
    rw [norm_add_eq hE, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
  obtain ⟨γ, K₁, hK₁, hγ⟩ := GlobalTheory.T.gaussIntegral_quadraticChar_eventually_const E hgood μ _ hpair f hlc hf0 hfadd
  have hG : HasGauss μ f γ := by
    intro K hK
    obtain ⟨L, hLc, hLo, hL⟩ := hgood.large (K ∪ K₁) (hK.union hK₁)
    exact ⟨L, hLc, hLo, Set.subset_union_left.trans hL, hγ L hLc hLo (Set.subset_union_right.trans hL)⟩
  refine ⟨γ, fun t => ?_⟩
  by_cases ht : t ∈ (Units.map (Algebra.norm F : E →* F)).range
  · obtain ⟨w, hw⟩ := ht
    let T : E ≃ₜ+ E :=
      { toFun := fun z => (w : E) * z
        invFun := fun z => ((w⁻¹ : Eˣ) : E) * z
        left_inv := fun z => by simp
        right_inv := fun z => by simp
        map_add' := fun x y => mul_add _ _ _
        continuous_toFun := continuous_const.mul continuous_id
        continuous_invFun := continuous_const.mul continuous_id }
    have hT : μ.map T = (distribHaarChar F t)⁻¹ • μ := by
      have h := GlobalTheory.T.map_mul_left_eq_inv_norm_haarChar_smul F E c δ hE μ w
      rw [hw] at h
      exact h
    have h := GlobalTheory.T.hasGaussIntegral_comp_addEquiv_rescale E E μ μ T _ f γ hT hG
    have e1 : (fun z : E => ψ ((t : F) * Algebra.norm F z)) = fun x => f (T x) := by
      funext z
      show ψ ((t : F) * Algebra.norm F z) = ψ (Algebra.norm F ((w : E) * z))
      rw [MonoidHom.map_mul (Algebra.norm F) (w : E) z, ← hw, Units.coe_map]
    have hs : sgn E t = 1 := by rw [sgn, if_pos ⟨w, hw⟩]
    have e2 : γ * (sgn E t * (((nabs F t)⁻¹ : ℝ) : ℂ)) = (((((distribHaarChar F t)⁻¹ : NNReal) : ℝ)) : ℂ) * γ := by
      rw [hs, one_mul, mul_comm]
      simp [nabs]
    rw [e1, e2]
    exact h
  · obtain ⟨s₀, hcan⟩ := GlobalTheory.T.gaussIntegral_normForm_nonNorm_cancel F E c δ hE ψ hψ hψ1 hψ0 μ t ht
    have hs : sgn E t = -1 := by rw [sgn, if_neg ht]
    intro K hK
    obtain ⟨a₁, ha₁⟩ := exists_cball_of_isCompact (hK.image hNc)
    obtain ⟨a₂, ha₂⟩ := exists_cball_of_isCompact (hK₁.image hNc)
    obtain ⟨s', hs'1, hs'2⟩ := exists_cball_sup (t * a₁) a₂
    obtain ⟨s, hs1, hs2⟩ := exists_cball_sup s' s₀
    obtain ⟨L, hLeq, hLc, hLo⟩ := GlobalTheory.T.exists_compactOpen_normClosedBall_quadratic F E c δ hE (t⁻¹ * s)
    obtain ⟨L₁, hL₁eq, hL₁c, hL₁o⟩ := GlobalTheory.T.exists_compactOpen_normClosedBall_quadratic F E c δ hE s
    have hset : {z : E | (t : F) * Algebra.norm F z ∈ cball s} = (L : Set E) := by
      rw [hLeq]; ext z; exact mul_mem_cball_iff t s _
    have hK₁L₁ : K₁ ⊆ L₁ := by
      intro z hz
      rw [hL₁eq]
      exact hs1 (hs'2 (ha₂ ⟨z, hz, rfl⟩))
    have hKL : K ⊆ L := by
      intro z hz
      rw [← hset]
      have h1 : Algebra.norm F z ∈ cball a₁ := ha₁ ⟨z, hz, rfl⟩
      have h2 : (t : F) * Algebra.norm F z ∈ cball (t * a₁) := by
        rw [mul_mem_cball_iff, inv_mul_cancel_left]; exact h1
      exact hs1 (hs'1 h2)
    have hs₀ : (s₀ : F) ∈ cball s := hs2 (show ValuativeRel.valuation F (s₀ : F) ≤ ValuativeRel.valuation F (s₀ : F) from le_refl _)
    have h1 := hcan s hs₀
    rw [← hL₁eq, hγ L₁ hL₁c hL₁o hK₁L₁, hset] at h1
    refine ⟨L, hLc, hLo, hKL, ?_⟩
    have hn : (nabs F t : ℂ) ≠ 0 := by exact_mod_cast (nabs_pos F t).ne'
    rw [hs, Complex.ofReal_inv]
    field_simp
    linear_combination h1
end GlobalTheory.KSp
