import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.SphComm2
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiInvTop
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiVecExHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiSeenC
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.ImportsAlt
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteRestrictionVanishing
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ArchimedeanCompact.AutomorphicFormsLeSm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfLocalLevelsUnitaryIsOpenIsCompactIsLeve

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

/- English proof (translation)
Establish `hc : Continuous fun u : GL (Fin n) (Af E) => logAbs (finGL E n u).val.det` using `(DiscreteGroups.T1.G.continuous_logAbs_det (E := E) (n := n)).comp GlobalTheory.BCT.GlobLev.continuous_finGL_ad`. Take `⟨C, hC⟩` from `(GlobalTheory.CompanionTheory.EulerV.isCompact_Kf (E := E) (n := n)).exists_bound_of_continuousOn hc.continuousOn`. Use `DiscreteGroups.T1.G.CP.eq_zero_of_nat_mul_le (C := C) fun m => ?_` and prove the remaining obligations. Establish `h` using `hC (u ^ m) (pow_mem hu m)`. Rewrite `h` using `[map_pow, Real.norm_eq_abs, DiscreteGroups.T1.G.CP.lAbs_pow, abs_mul, Nat.abs_cast]`.

Conclude with `h`.
-/
private theorem lAbs_fin {u : GL (Fin n) (Af E)} (hu : u ∈ Kf E n) : logAbs (finGL E n u).val.det = 0 := by
  have hc : Continuous fun u : GL (Fin n) (Af E) => logAbs (finGL E n u).val.det :=
    (DiscreteGroups.T1.G.continuous_logAbs_det (E := E) (n := n)).comp GlobalTheory.BCT.GlobLev.continuous_finGL_ad
  obtain ⟨C, hC⟩ := (GlobalTheory.CompanionTheory.EulerV.isCompact_Kf (E := E) (n := n)).exists_bound_of_continuousOn hc.continuousOn
  refine DiscreteGroups.T1.G.CP.eq_zero_of_nat_mul_le (C := C) fun m => ?_
  have h := hC (u ^ m) (pow_mem hu m)
  rw [map_pow, Real.norm_eq_abs, DiscreteGroups.T1.G.CP.lAbs_pow, abs_mul, Nat.abs_cast] at h
  exact h

/- English proof (translation)
Rewrite using `[← UpperTheory.V.Cm.infEmb_cptEq]`. Conclude with `DiscreteGroups.T1.G.CP.lAbs_maxCompact (UpperTheory.V.Cm.cptEq E n k).2`.
-/
private theorem lAbs_inf (k : Kinf E n) : logAbs (infGL E n (Unitary.toUnits k)).val.det = 0 := by
  rw [← UpperTheory.V.Cm.infEmb_cptEq]
  exact DiscreteGroups.T1.G.CP.lAbs_maxCompact (UpperTheory.V.Cm.cptEq E n k).2

/- English proof (translation)
Establish `hψ : ∀ y, ψ.1 y = Complex.exp (-(z * logAbs y.val.det)) * φ.1 y` using `fun y => by`. Rewrite using `[h y, mul_comm (ψ.1 y), ← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]`. Use `⟨fun u hu g => ?_, fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[hψ, hψ g, hT.1 u hu g, DiscreteGroups.T1.G.CP.lAbs_mul, lAbs_fin (hK hu), add_zero]`. Establish `e : (fun k : Kinf E n => ψ.1 (g * infGL E n (Unitary.toUnits k))) = Complex.exp (-(z * logAbs g.val.det)) • fun k : Kinf E n => φ.1 (g * infGL E n (Unitary.toUnits k))`.

Use function extensionality and compare the values at `k`. Rewrite using `[hψ, DiscreteGroups.T1.G.CP.lAbs_mul, lAbs_inf, add_zero]`. Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `W.smul_mem _ (hT.2 g)`.
-/
private theorem typeB_untwist {K : Subgroup (GL (Fin n) (Af E))} {W : Submodule ℂ (Kinf E n → ℂ)} (hK : K ≤ Kf E n)
    {φ ψ : Sm E n} {z : ℂ} (h : ∀ y, φ.1 y = ψ.1 y * Complex.exp (z * logAbs y.val.det)) (hT : TypeB K W φ) :
    TypeB K W ψ := by
  have hψ : ∀ y, ψ.1 y = Complex.exp (-(z * logAbs y.val.det)) * φ.1 y := fun y => by
    rw [h y, mul_comm (ψ.1 y), ← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]
  refine ⟨fun u hu g => ?_, fun g => ?_⟩
  · rw [hψ, hψ g, hT.1 u hu g, DiscreteGroups.T1.G.CP.lAbs_mul, lAbs_fin (hK hu), add_zero]
  · have e : (fun k : Kinf E n => ψ.1 (g * infGL E n (Unitary.toUnits k))) =
        Complex.exp (-(z * logAbs g.val.det)) • fun k : Kinf E n => φ.1 (g * infGL E n (Unitary.toUnits k)) := by
      funext k
      rw [hψ, DiscreteGroups.T1.G.CP.lAbs_mul, lAbs_inf, add_zero]
      rfl
    rw [e]
    exact W.smul_mem _ (hT.2 g)

/- English proof (translation)
Introduce `i j`. Use `⟨Complex.continuous_conj.comp ((h j i).1.comp continuous_inv), ?_⟩` and prove the remaining obligations. Establish `h1 : HasCompactSupport fun y : H E a b => Φ j i y⁻¹` using `(h j i).2.comp_homeomorph (Homeomorph.inv _)`. Conclude with `h1.comp_left (g := starRingEnd ℂ) (map_zero _)`.
-/
private theorem adjM_test {a b : ℕ} {ι : Type} {Φ : Matrix ι ι (H E a b → ℂ)} (h : IsTestM Φ) : IsTestM (adjM Φ) := by
  intro i j
  refine ⟨Complex.continuous_conj.comp ((h j i).1.comp continuous_inv), ?_⟩
  have h1 : HasCompactSupport fun y : H E a b => Φ j i y⁻¹ := (h j i).2.comp_homeomorph (Homeomorph.inv _)
  exact h1.comp_left (g := starRingEnd ℂ) (map_zero _)

/- English proof (translation)
Introduce `f hf`. Rewrite `hf`, the goal using `[Submodule.mem_orthogonal]`. Introduce `q hq`. Establish `hadj : IsROp D (adjM Φ) (ContinuousLinearMap.adjoint T)` using `((PositivityTheory.Rg.BcB.E1.opEx_holds E n 0 D ι).2 Φ Φ T T hΦ hΦ hT hT).2.2`. Establish `hq'` using `DiscreteGroups.T1.G.piInv E n hn D π hθ ι (adjM Φ) _ (adjM_test hΦ) hadj q hq`.

Rewrite using `[← ContinuousLinearMap.adjoint_inner_left]`. Conclude with `hf _ hq'`.
-/
private theorem keepsOrth {ι : Type} [Fintype ι] (hn : 1 ≤ n) (D : Dom E n 0) (π : CuspSub E n) (hθ : ThetaFix π)
    (Φ : Matrix ι ι (H E n 0 → ℂ)) (T : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) (hΦ : IsTestM Φ) (hT : IsROp D Φ T) :
    ∀ f ∈ (piSp D π ι)ᗮ, T f ∈ (piSp D π ι)ᗮ := by
  intro f hf
  rw [Submodule.mem_orthogonal] at hf ⊢
  intro q hq
  have hadj : IsROp D (adjM Φ) (ContinuousLinearMap.adjoint T) :=
    ((PositivityTheory.Rg.BcB.E1.opEx_holds E n 0 D ι).2 Φ Φ T T hΦ hΦ hT hT).2.2
  have hq' := DiscreteGroups.T1.G.piInv E n hn D π hθ ι (adjM Φ) _ (adjM_test hΦ) hadj q hq
  rw [← ContinuousLinearMap.adjoint_inner_left]
  exact hf _ hq'

/- English proof (translation)
Take `⟨hm, hw⟩` from `DiscreteGroups.T1.G.Dcy.piVecEx_holds E n hn D π hθ ψ hψ u hu hc`. Use `set w : Lp ℂ 2 D.ν := hm.toLp _ with hwd`. Establish `hwe : (w : H E n 0 → ℂ) =ᵐ[D.ν] fun x => ψ.1 x.1 * u (ldet x)` using `hm.coeFn_toLp`. Use `set v : Hs (ι := ι) D := WithLp.toLp 2 (Pi.single i w) with hv`. Establish `hvi : v i = w` using `by simp [hv]`.

Establish `hv0 : ∀ i', i' ≠ i → v i' = 0` using `fun i' h => by simp [hv, h]`. Establish `hz : ∀ i', i' ≠ i → (v i' : H E n 0 → ℂ) =ᵐ[D.ν] 0` using `fun i' h => by`. Rewrite using `[hv0 i' h]`. Conclude with `Lp.coeFn_zero _ _ _`. Use `⟨v, ?_, fun i' M => ?_, fun f => ?_⟩` and prove the remaining obligations.

Use `Submodule.le_topologicalClosure _ (Submodule.subset_span ?_)` and prove the remaining obligations. Introduce `i'`. Distinguish the cases in `h : i' = i`. Substitute `h` using the available equality. Conclude with `⟨ψ, hψ, u, hu, hc, by rw [hvi]; exact hwe⟩`.

Use `⟨0, Submodule.zero_mem _, 0, continuous_const, HasCompactSupport.zero, ?_⟩ filter_upwards [hz i' h] with x hx` and prove the remaining obligations. Simplify using `[hx]`. Distinguish the cases in `h : i' = i`. Substitute `h` using the available equality. Rewrite using `[hvi]`.

Use `lt_of_eq_of_lt (lintegral_congr_ae ?_) (hw M)` and prove the remaining obligations. Use `filter_upwards [hwe] with x hx`. Rewrite using `[hx]`. Use `lt_of_eq_of_lt (lintegral_congr_ae (g := fun _ => 0) ?_) (by simp) filter_upwards [hz i' h] with x hx` and prove the remaining obligations. Simplify using `[hx]`.

Rewrite using `[Finset.sum_eq_single i]`. Rewrite using `[hvi]`. Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [hwe] with x hx`. Rewrite using `[hx]`.

Introduce `i' _ h`. Use `(integral_congr_ae (g := fun _ => 0) ?_).trans (by simp)` and prove the remaining obligations. Use `filter_upwards [hz i' h] with x hx`. Simplify using `[hx]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ i) h`.
-/
private theorem vecEx {ι : Type} [Fintype ι] (hn : 1 ≤ n) (D : Dom E n 0) (π : CuspSub E n) (hθ : ThetaFix π)
    (ψ : Sm E n) (hψ : ψ ∈ π.V) (u : ℝ → ℂ) (hu : Continuous u) (hc : HasCompactSupport u) (i : ι) :
    ∃ v : Hs (ι := ι) D, v ∈ piSp D π ι ∧
      (∀ i' (M : ℕ), ∫⁻ x, ENNReal.ofReal (wt x ^ (2 * M)) * ‖(v i' : H E n 0 → ℂ) x‖ₑ ^ 2 ∂D.ν < ⊤) ∧
      ∀ f : ι → H E n 0 → ℂ, ∑ i', ∫ x, starRingEnd ℂ ((v i' : H E n 0 → ℂ) x) * f i' x ∂D.ν =
        ∫ x, starRingEnd ℂ (ψ.1 x.1 * u (ldet x)) * f i x ∂D.ν := by
  obtain ⟨hm, hw⟩ := DiscreteGroups.T1.G.Dcy.piVecEx_holds E n hn D π hθ ψ hψ u hu hc
  set w : Lp ℂ 2 D.ν := hm.toLp _ with hwd
  have hwe : (w : H E n 0 → ℂ) =ᵐ[D.ν] fun x => ψ.1 x.1 * u (ldet x) := hm.coeFn_toLp
  set v : Hs (ι := ι) D := WithLp.toLp 2 (Pi.single i w) with hv
  have hvi : v i = w := by simp [hv]
  have hv0 : ∀ i', i' ≠ i → v i' = 0 := fun i' h => by simp [hv, h]
  have hz : ∀ i', i' ≠ i → (v i' : H E n 0 → ℂ) =ᵐ[D.ν] 0 := fun i' h => by
    rw [hv0 i' h]; exact Lp.coeFn_zero _ _ _
  refine ⟨v, ?_, fun i' M => ?_, fun f => ?_⟩
  · refine Submodule.le_topologicalClosure _ (Submodule.subset_span ?_)
    intro i'
    by_cases h : i' = i
    · subst h
      exact ⟨ψ, hψ, u, hu, hc, by rw [hvi]; exact hwe⟩
    · refine ⟨0, Submodule.zero_mem _, 0, continuous_const, HasCompactSupport.zero, ?_⟩
      filter_upwards [hz i' h] with x hx
      simp [hx]
  · by_cases h : i' = i
    · subst h
      rw [hvi]
      refine lt_of_eq_of_lt (lintegral_congr_ae ?_) (hw M)
      filter_upwards [hwe] with x hx
      rw [hx]
    · refine lt_of_eq_of_lt (lintegral_congr_ae (g := fun _ => 0) ?_) (by simp)
      filter_upwards [hz i' h] with x hx
      simp [hx]
  · rw [Finset.sum_eq_single i]
    · rw [hvi]
      refine integral_congr_ae ?_
      filter_upwards [hwe] with x hx
      rw [hx]
    · intro i' _ h
      refine (integral_congr_ae (g := fun _ => 0) ?_).trans (by simp)
      filter_upwards [hz i' h] with x hx
      simp [hx]
    · intro h
      exact absurd (Finset.mem_univ i) h

/- English proof (translation)
Introduce `hAdm E _ _ _ n hn l₁ l₂ D A π hθ K W hK hKf hW`. Use `⟨fun Φ T hΦ hT f hf => DiscreteGroups.T1.G.piInv E n hn D π hθ _ Φ T hΦ hT f hf, fun Φ T hΦ hT f hf => keepsOrth hn D π hθ Φ T hΦ hT f hf, ?_⟩` and prove the remaining obligations. Take `⟨Y, hYπ, hYf, hY⟩` from `hAdm E n hn π hθ K W hK hW`. Take `⟨ψ, u, hψu, hS⟩` from `DiscreteGroups.T1.G.Dcy.piSeen_holds E n hn D π hθ Y hYπ hYf`. Use `choose v hvm hvw hvs using fun p : A.blk.I × ℕ => vecEx (ι := A.blk.I) hn D π hθ (ψ p.2) (hψu p.2).1 (u p.2) (hψu p.2).2.1 (hψu p.2).2.2 p.1`.

Take `⟨e, he⟩` from `exists_surjective_nat (Option (A.blk.I × ℕ))`. Establish `key : ∀ o : Option (A.blk.I × ℕ), o.elim (0 : Hs (ι` using `A.blk.I) D) v ∈ piSp D π A.blk.I ∧ ∀ i (M : ℕ), ∫⁻ x, ENNReal.ofReal (wt x ^ (2 * M)) * ‖((o.elim (0 : Hs (ι := A.blk.I) D) v) i : H E n 0 → ℂ) x‖ₑ ^ 2 ∂D.ν < ⊤ := by`. Introduce and unpack `(_ | p)`. Use `⟨Submodule.zero_mem _, fun i M => ?_⟩` and prove the remaining obligations. Use `lt_of_eq_of_lt (lintegral_congr_ae (g := fun _ => 0) ?_) (by simp)` and prove the remaining obligations.

Establish `h0 : (((0 : Hs (ι` using `A.blk.I) D) i : Lp ℂ 2 D.ν) : H E n 0 → ℂ) =ᵐ[D.ν] 0 := Lp.coeFn_zero _ _ _`. Use `filter_upwards [h0] with x hx`. Use `show ENNReal.ofReal _ * ‖(((0 : Hs (ι := A.blk.I) D) i : Lp ℂ 2 D.ν) : H E n 0 → ℂ) x‖ₑ ^ 2 = 0`. Rewrite using `[hx]`. Simplify using the standard rewrite rules.

Conclude with `⟨hvm p, hvw p⟩`. Use `⟨fun j => (e j).elim 0 v, ⟨fun j => ?_, fun j i M => (key (e j)).2 i M⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.orthogonal_orthogonal]`. Conclude with `(key (e j)).1`. Introduce `f hO i m₂ φ hφ hne hT π' hπ' ψ' hψ' z hz`.

Take `rfl : π' = π` from `hπ'`. Establish `hT' : TypeB K W ψ'` using `typeB_untwist hKf hz hT`. Use `hne (Subtype.ext (funext fun y => ?_))` and prove the remaining obligations. Establish `h0 : ψ' = 0` using `hS ψ' (hY ψ' hψ' hT') z fun k => ?_`. Rewrite using `[hz y, h0]`.

Simplify using the standard rewrite rules. Take `⟨j, hj⟩` from `he (some (i, k))`. Establish `h1` using `hO j`. Simplify using `only [hj, Option.elim_some] at h1`. Rewrite `h1` using `[hvs (i, k) f]`.

Rewrite using `[← h1]`. Use `integral_congr_ae (Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Establish `e2 : x = (x.1, m₂)` using `Prod.ext rfl (Subsingleton.elim _ _)`. Establish `e3 : f i x = φ.1 x.1` using `by rw [hφ]; exact congrArg (f i) e2`. Simplify using `only [e3, hz x.1, ldet]`.
-/
theorem testsEx : PiAdm → TestsEx := by
  intro hAdm E _ _ _ n hn l₁ l₂ D A π hθ K W hK hKf hW
  refine ⟨fun Φ T hΦ hT f hf => DiscreteGroups.T1.G.piInv E n hn D π hθ _ Φ T hΦ hT f hf,
    fun Φ T hΦ hT f hf => keepsOrth hn D π hθ Φ T hΦ hT f hf, ?_⟩
  obtain ⟨Y, hYπ, hYf, hY⟩ := hAdm E n hn π hθ K W hK hW
  obtain ⟨ψ, u, hψu, hS⟩ := DiscreteGroups.T1.G.Dcy.piSeen_holds E n hn D π hθ Y hYπ hYf
  choose v hvm hvw hvs using fun p : A.blk.I × ℕ =>
    vecEx (ι := A.blk.I) hn D π hθ (ψ p.2) (hψu p.2).1 (u p.2) (hψu p.2).2.1 (hψu p.2).2.2 p.1
  obtain ⟨e, he⟩ := exists_surjective_nat (Option (A.blk.I × ℕ))
  have key : ∀ o : Option (A.blk.I × ℕ), o.elim (0 : Hs (ι := A.blk.I) D) v ∈ piSp D π A.blk.I ∧
      ∀ i (M : ℕ), ∫⁻ x, ENNReal.ofReal (wt x ^ (2 * M)) *
        ‖((o.elim (0 : Hs (ι := A.blk.I) D) v) i : H E n 0 → ℂ) x‖ₑ ^ 2 ∂D.ν < ⊤ := by
    rintro (_ | p)
    · refine ⟨Submodule.zero_mem _, fun i M => ?_⟩
      refine lt_of_eq_of_lt (lintegral_congr_ae (g := fun _ => 0) ?_) (by simp)
      have h0 : (((0 : Hs (ι := A.blk.I) D) i : Lp ℂ 2 D.ν) : H E n 0 → ℂ) =ᵐ[D.ν] 0 := Lp.coeFn_zero _ _ _
      filter_upwards [h0] with x hx
      show ENNReal.ofReal _ * ‖(((0 : Hs (ι := A.blk.I) D) i : Lp ℂ 2 D.ν) : H E n 0 → ℂ) x‖ₑ ^ 2 = 0
      rw [hx]
      simp
    · exact ⟨hvm p, hvw p⟩
  refine ⟨fun j => (e j).elim 0 v, ⟨fun j => ?_, fun j i M => (key (e j)).2 i M⟩, ?_⟩
  · rw [Submodule.orthogonal_orthogonal]
    exact (key (e j)).1
  · intro f hO i m₂ φ hφ hne hT π' hπ' ψ' hψ' z hz
    obtain rfl : π' = π := hπ'
    have hT' : TypeB K W ψ' := typeB_untwist hKf hz hT
    refine hne (Subtype.ext (funext fun y => ?_))
    have h0 : ψ' = 0 := hS ψ' (hY ψ' hψ' hT') z fun k => ?_
    · rw [hz y, h0]; simp
    obtain ⟨j, hj⟩ := he (some (i, k))
    have h1 := hO j
    simp only [hj, Option.elim_some] at h1
    rw [hvs (i, k) f] at h1
    rw [← h1]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    have e2 : x = (x.1, m₂) := Prod.ext rfl (Subsingleton.elim _ _)
    have e3 : f i x = φ.1 x.1 := by rw [hφ]; exact congrArg (f i) e2
    simp only [e3, hz x.1, ldet]

end UpperTheory.Zero.ConvolutionTheory.EB
