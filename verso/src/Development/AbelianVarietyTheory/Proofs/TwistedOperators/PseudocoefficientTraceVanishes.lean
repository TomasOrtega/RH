import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace

open GlobalTheory.HCChar GlobalTheory.Orb GlobalTheory.FlagLeviGroup

namespace GlobalTheory.IndTraceZero

variable {n a : ℕ} {ε : Fin n → Bool} {j : Fin a → ℕ} {W : GlobalTheory.RealInd.Flag n a}

/- English proof (translation)
Establish `hgi : g⁻¹ ∈ flagM ε W` using `(leviSub ε W).inv_mem hg`. Establish `hgg : uMat g * uMat g⁻¹ = 1`. Rewrite using `[← show uMat (g * g⁻¹) = uMat g * uMat g⁻¹ from rfl, mul_inv_cancel]`. Both sides reduce to the same expression. Establish `hJ : Jm ε * uMat g⁻¹ = (uMat g)ᴴ * Jm ε`.

Use `conjTranspose_inv_mul_Jm (ε := ε) g⁻¹` as an intermediate fact. Rewrite `this` using `[inv_inv]`. Conclude with `this.symm`. Establish `hm : uMat (g * t * g⁻¹) = uMat g * uMat t * uMat g⁻¹` using `rfl`. Establish `h' : IsSplit ε W x (g * t * g⁻¹)`.

Use `⟨(leviSub ε W).mul_mem ((leviSub ε W).mul_mem hg ht.1) hgi, fun i y hy => ?_, fun y hy => ?_⟩` and prove the remaining obligations. Establish `hy' : uMat g⁻¹ *ᵥ y ∈ W i.succ` using `(hgi _ y hy).1`. Establish `h1` using `(hg _ _ (ht.2.1 i _ hy')).1`. Establish `e : uMat g *ᵥ (uMat t *ᵥ (uMat g⁻¹ *ᵥ y) - (Real.exp (x i) : ℂ) • (uMat g⁻¹ *ᵥ y)) = uMat (g * t * g⁻¹) *ᵥ y - (Real.exp (x i) : ℂ) • y`. Rewrite using `[Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hgg, Matrix.one_mulVec, hm]`.

Rewrite `h1` using `[e]`. Then use the resulting hypothesis. Establish `hy' : ∀ z ∈ W (Fin.last a), star z ⬝ᵥ (Jm ε *ᵥ (uMat g⁻¹ *ᵥ y)) = 0` using `fun z hz => by`. Rewrite using `[Matrix.mulVec_mulVec, hJ, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]`. Conclude with `hy _ (hg _ z hz).1`. Establish `h1` using `(hg _ _ (ht.2.2 _ hy')).1`.

Establish `e : uMat g *ᵥ (uMat t *ᵥ (uMat g⁻¹ *ᵥ y) - uMat g⁻¹ *ᵥ y) = uMat (g * t * g⁻¹) *ᵥ y - y`. Rewrite using `[Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hgg, Matrix.one_mulVec, hm]`. Rewrite `h1` using `[e]`. Then use the resulting hypothesis. Establish `e` using `(existsUnique_isSplit hW x).unique h' ht`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem IsSplit.commute (hW : IsIsoFlag ε j W) {x : Fin a → ℝ} {t g : UJ ε} (ht : IsSplit ε W x t)
    (hg : g ∈ flagM ε W) : g * t = t * g := by
  have hgi : g⁻¹ ∈ flagM ε W := (leviSub ε W).inv_mem hg
  have hgg : uMat g * uMat g⁻¹ = 1 := by
    rw [← show uMat (g * g⁻¹) = uMat g * uMat g⁻¹ from rfl, mul_inv_cancel]; rfl
  have hJ : Jm ε * uMat g⁻¹ = (uMat g)ᴴ * Jm ε := by
    have := conjTranspose_inv_mul_Jm (ε := ε) g⁻¹
    rw [inv_inv] at this
    exact this.symm
  have hm : uMat (g * t * g⁻¹) = uMat g * uMat t * uMat g⁻¹ := rfl
  have h' : IsSplit ε W x (g * t * g⁻¹) := by
    refine ⟨(leviSub ε W).mul_mem ((leviSub ε W).mul_mem hg ht.1) hgi, fun i y hy => ?_, fun y hy => ?_⟩
    · have hy' : uMat g⁻¹ *ᵥ y ∈ W i.succ := (hgi _ y hy).1
      have h1 := (hg _ _ (ht.2.1 i _ hy')).1
      have e : uMat g *ᵥ (uMat t *ᵥ (uMat g⁻¹ *ᵥ y) - (Real.exp (x i) : ℂ) • (uMat g⁻¹ *ᵥ y)) =
          uMat (g * t * g⁻¹) *ᵥ y - (Real.exp (x i) : ℂ) • y := by
        rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
          hgg, Matrix.one_mulVec, hm]
      rwa [e] at h1
    · have hy' : ∀ z ∈ W (Fin.last a), star z ⬝ᵥ (Jm ε *ᵥ (uMat g⁻¹ *ᵥ y)) = 0 := fun z hz => by
        rw [Matrix.mulVec_mulVec, hJ, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
        exact hy _ (hg _ z hz).1
      have h1 := (hg _ _ (ht.2.2 _ hy')).1
      have e : uMat g *ᵥ (uMat t *ᵥ (uMat g⁻¹ *ᵥ y) - uMat g⁻¹ *ᵥ y) = uMat (g * t * g⁻¹) *ᵥ y - y := by
        rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hgg,
          Matrix.one_mulVec, hm]
      rwa [e] at h1
  have e := (existsUnique_isSplit hW x).unique h' ht
  calc g * t = g * t * g⁻¹ * g := by group
    _ = t * g := by rw [e]

/- English proof (translation)
Take `⟨a', rfl⟩` from `Nat.exists_eq_succ_of_ne_zero ha`. Set `i₀ : Fin (a' + 1)` to `0`. Establish `hr : Module.finrank ℂ (W i₀.succ) = j i₀`. Rewrite using `[hW.2.2.1 i₀, show i₀.castSucc = 0 from rfl, hW.1, finrank_bot, zero_add]`. Establish `hne : W i₀.succ ≠ ⊥` using `fun e => by`.

Use `hj i₀` as an intermediate fact. Rewrite `hr` using `[e, finrank_bot]`. Use linear arithmetic over natural numbers and integers. Take `⟨y, hy, hy0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hne`. Establish `hc : Continuous fun g : UJ ε => uMat g *ᵥ y` using `(continuous_ujMat (ε := ε)).matrix_mulVec continuous_const`.

Take `⟨C, hC⟩` from `hK.exists_bound_of_continuousOn hc.continuousOn`. Establish `hyn : 0 < ‖y‖` using `norm_pos_iff.2 hy0`. Take `⟨t, htK, ht⟩` from `h (C / ‖y‖)`. Establish `h1` using `ht.2.1 i₀ y hy`. Rewrite `h1` using `[show i₀.castSucc = 0 from rfl, hW.1, Submodule.mem_bot, sub_eq_zero]`.

Establish `h2` using `hC t htK`. Rewrite `h2` using `[h1, norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]`. Establish `h3` using `Real.add_one_le_exp (C / ‖y‖)`. Establish `h4 : (C / ‖y‖ + 1) * ‖y‖ ≤ C` using `(mul_le_mul_of_nonneg_right h3 hyn.le).trans h2`. Rewrite `h4` using `[add_mul, div_mul_cancel₀ _ hyn.ne', one_mul]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem not_isSplit_subset_compact (hW : IsIsoFlag ε j W) (hj : ∀ i, 1 ≤ j i) (ha : a ≠ 0) {K : Set (UJ ε)}
    (hK : IsCompact K) (h : ∀ r : ℝ, ∃ t ∈ K, IsSplit ε W (fun _ => r) t) : False := by
  obtain ⟨a', rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha
  let i₀ : Fin (a' + 1) := 0
  have hr : Module.finrank ℂ (W i₀.succ) = j i₀ := by
    rw [hW.2.2.1 i₀, show i₀.castSucc = 0 from rfl, hW.1, finrank_bot, zero_add]
  have hne : W i₀.succ ≠ ⊥ := fun e => by
    have := hj i₀
    rw [e, finrank_bot] at hr
    omega
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hc : Continuous fun g : UJ ε => uMat g *ᵥ y :=
    (continuous_ujMat (ε := ε)).matrix_mulVec continuous_const
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  have hyn : 0 < ‖y‖ := norm_pos_iff.2 hy0
  obtain ⟨t, htK, ht⟩ := h (C / ‖y‖)
  have h1 := ht.2.1 i₀ y hy
  rw [show i₀.castSucc = 0 from rfl, hW.1, Submodule.mem_bot, sub_eq_zero] at h1
  have h2 := hC t htK
  rw [h1, norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le] at h2
  have h3 := Real.add_one_le_exp (C / ‖y‖)
  have h4 : (C / ‖y‖ + 1) * ‖y‖ ≤ C := (mul_le_mul_of_nonneg_right h3 hyn.le).trans h2
  rw [add_mul, div_mul_cancel₀ _ hyn.ne', one_mul] at h4
  linarith

/- English proof (translation)
Introduce `hx`. Use `not_isSplit_subset_compact hW hj ha (hK.image (f := fun g => x * g * x⁻¹) ((continuous_const.mul continuous_id).mul continuous_const)) fun r => ?_` and prove the remaining obligations. Take `⟨t, ht, -⟩` from `exists_isSplit hW (fun _ => r)`. Establish `hc` using `IsSplit.commute hW ht hx`. Use `⟨t, ⟨x⁻¹ * t * x, mem_cent.2 ?_, by group⟩, ht⟩` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem not_conj_mem_flagM (hW : IsIsoFlag ε j W) (hj : ∀ i, 1 ≤ j i) (ha : a ≠ 0) {s : UJ ε}
    (hK : IsCompact (cent s : Set (UJ ε))) (x : UJ ε) : x * s * x⁻¹ ∉ flagM ε W := by
  intro hx
  refine not_isSplit_subset_compact hW hj ha (hK.image (f := fun g => x * g * x⁻¹)
    ((continuous_const.mul continuous_id).mul continuous_const)) fun r => ?_
  obtain ⟨t, ht, -⟩ := exists_isSplit hW (fun _ => r)
  have hc := IsSplit.commute hW ht hx
  refine ⟨t, ⟨x⁻¹ * t * x, mem_cent.2 ?_, by group⟩, ht⟩
  calc x⁻¹ * t * x * s = x⁻¹ * (t * (x * s * x⁻¹)) * x := by group
    _ = x⁻¹ * ((x * s * x⁻¹) * t) * x := by rw [hc]
    _ = s * (x⁻¹ * t * x) := by group

end GlobalTheory.IndTraceZero

namespace GlobalTheory.IndTraceZero

open GlobalTheory.HCChar GlobalTheory.Published

/- English proof (translation)
Introduce `hHC n ε μ _ X _ _ _ δ f hf I ha`. Take `⟨Θ, hΘ, hvan⟩` from `hHC.2.2.2.indModule μ I ha`. Establish `htr` using `hΘ.1.2.2 f hf.mem`. Use `htr using 1` and compare the differences between its conclusion and the goal. Use `symm`.

Use `hHC.2.2.1.integral_mul_eq_zero μ (continuous_of_mem_ccSmooth isInducing_matCoord.continuous hf.mem) hf.mem.1 hΘ.1.1 (fun s x hs => (hΘ.2 s hs).2 x) fun s hs => ?_` and prove the remaining obligations. Distinguish the cases in `hK : IsCompact (cent s : Set (UJ ε))`. Conclude with `Or.inl (hvan s hs fun x => not_conj_mem_flagM I.flag I.pos ha hK x)`. Conclude with `Or.inr fun ds _ _ => hf.orb_noncompact s hs hK ds`.
-/
theorem hasTrace_indModule_eq_zero : GlobalTheory.Published.HarishChandraCharacters → ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X] (δ : UJ ε →* (X →L[ℂ] X)) (f : UJ ε → ℂ), IsPseudoCoeff (ujMat ε) μ δ f → ∀ I : IndModule ε, I.a ≠ 0 → HasTrace (repOp I.rep μ f) 0 := by
  intro hHC n ε μ _ X _ _ _ δ f hf I ha
  obtain ⟨Θ, hΘ, hvan⟩ := hHC.2.2.2.indModule μ I ha
  have htr := hΘ.1.2.2 f hf.mem
  convert htr using 1
  symm
  refine hHC.2.2.1.integral_mul_eq_zero μ (continuous_of_mem_ccSmooth isInducing_matCoord.continuous hf.mem)
    hf.mem.1 hΘ.1.1 (fun s x hs => (hΘ.2 s hs).2 x) fun s hs => ?_
  by_cases hK : IsCompact (cent s : Set (UJ ε))
  · exact Or.inl (hvan s hs fun x => not_conj_mem_flagM I.flag I.pos ha hK x)
  · exact Or.inr fun ds _ _ => hf.orb_noncompact s hs hK ds

end GlobalTheory.IndTraceZero
