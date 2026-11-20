import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.Intersections.ArithVarZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterOsgood
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ADensStC
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology MeasureTheory

noncomputable section

set_option linter.unusedSectionVars false

namespace G1

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
The claim follows from `| 0, V, b, _ => by unfold geoNum split_ifs <;> positivity | n + 1, V, b, hb => by rw [geoNum] split_ifs with h · refine Finset.sum_nonneg fun k _ => mul_nonneg (hb _ k) ?_ exact finsum_nonneg fun W => finsum_nonneg fun _ => mul_nonneg (Nat.cast_nonneg _) (geoNum_nonneg n W (Fin.i …`.
-/
theorem geoNum_nonneg : ∀ (n : ℕ) (V : Ideal (MRing ι)) (b : Fin n → K → ℤ),
    (∀ j k, 0 ≤ b j k) → 0 ≤ geoNum n V b
  | 0, V, b, _ => by
    unfold geoNum
    split_ifs <;> positivity
  | n + 1, V, b, hb => by
    rw [geoNum]
    split_ifs with h
    · refine Finset.sum_nonneg fun k _ => mul_nonneg (hb _ k) ?_
      exact finsum_nonneg fun W => finsum_nonneg fun _ =>
        mul_nonneg (Nat.cast_nonneg _) (geoNum_nonneg n W (Fin.init b) fun j k => hb _ k)
    · exact le_rfl

/- English proof (translation)
Establish `h0 : 0 ≤ ∑ᶠ x, -g x` using `finsum_nonneg fun x => neg_nonneg.2 (h x)`. Rewrite `h0` using `[finsum_neg_distrib]`. Conclude with `neg_nonneg.1 h0`.
-/
theorem finsum_nonpos' {α : Sort*} {g : α → ℝ} (h : ∀ x, g x ≤ 0) : ∑ᶠ x, g x ≤ 0 := by
  have h0 : 0 ≤ ∑ᶠ x, -g x := finsum_nonneg fun x => neg_nonneg.2 (h x)
  rw [finsum_neg_distrib] at h0
  exact neg_nonneg.1 h0

/- English proof (translation)
Introduce `_ hz` and use `⟨hz.1, fun f hf => hz.2 f (h hf)⟩`.
-/
theorem mcPts_anti {P W : Ideal (MRing ι)} (h : P ≤ W) : mcPts W ⊆ mcPts P :=
  fun _ hz => ⟨hz.1, fun f hf => hz.2 f (h hf)⟩

/- English proof (translation)
Establish `e : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0}`. Use extensionality with `z`. Simplify using the standard rewrite rules. Rewrite using `[e]`. Conclude with `isOpen_iInter_of_finite fun k => isOpen_iUnion fun i => isOpen_ne_fun (continuous_apply _) continuous_const`.
-/
theorem isOpen_blocksNonzero : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have e : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0} := by
    ext z
    simp
  rw [e]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

/- English proof (translation)
Use `choose c hc using hP.2.2`. Set `μ : (Σ k, ι k) →₀ ℕ` to `Finsupp.equivFunOnFinite.symm fun p => if p.2 = c p.1 then a p.1 else 0`. Use `⟨μ, fun k => ?_, ?_⟩` and prove the remaining obligations. Simplify using `[μ]`. Introduce `hmem`.

Use `hP.1` as an intermediate fact. Rewrite `hmem` using `[monomial_eq, C_1, one_mul, Finsupp.prod]`. Take `⟨p, hp, hpP⟩` from `Ideal.IsPrime.prod_mem_iff.1 hmem`. Establish `hX` using `hP.1.mem_of_pow_mem _ hpP`. Establish `hμp : μ p ≠ 0` using `Finsupp.mem_support_iff.1 hp`.

Take `⟨k, j⟩` from `p`. Distinguish the cases in `hj : j = c k`. Substitute `hj` using the available equality. Conclude with `hc k hX`. Conclude with `hμp (by simp [μ, hj])`.
-/
theorem exists_monomial_not_mem {P : Ideal (MRing ι)} (hP : IsMultiProjPrime P) (a : K → ℕ) :
    ∃ μ : (Σ k, ι k) →₀ ℕ, (∀ k, ∑ i, μ ⟨k, i⟩ = a k) ∧ monomial μ (1 : ℤ) ∉ P := by
  classical
  choose c hc using hP.2.2
  let μ : (Σ k, ι k) →₀ ℕ :=
    Finsupp.equivFunOnFinite.symm fun p => if p.2 = c p.1 then a p.1 else 0
  refine ⟨μ, fun k => ?_, ?_⟩
  · simp [μ]
  · intro hmem
    have := hP.1
    rw [monomial_eq, C_1, one_mul, Finsupp.prod] at hmem
    obtain ⟨p, hp, hpP⟩ := Ideal.IsPrime.prod_mem_iff.1 hmem
    have hX := hP.1.mem_of_pow_mem _ hpP
    have hμp : μ p ≠ 0 := Finsupp.mem_support_iff.1 hp
    obtain ⟨k, j⟩ := p
    by_cases hj : j = c k
    · subst hj
      exact hc k hX
    · exact hμp (by simp [μ, hj])

/- English proof (translation)
Introduce `m hm k`. Rewrite using `[Finset.mem_singleton.1 (support_monomial_subset hm)]`. Conclude with `hμ k`.
-/
theorem isMultiHomog_monomial {μ : (Σ k, ι k) →₀ ℕ} {a : K → ℕ} (hμ : ∀ k, ∑ i, μ ⟨k, i⟩ = a k) :
    IsMultiHomog (monomial μ (1 : ℤ)) a := by
  intro m hm k
  rw [Finset.mem_singleton.1 (support_monomial_subset hm)]
  exact hμ k

/- English proof (translation)
Rewrite using `[map_monomial, eval_monomial, map_one, one_mul, Finsupp.prod_fintype]`. Introduce `p`. Simplify using the standard rewrite rules.
-/
theorem eval_monomial_one (μ : (Σ k, ι k) →₀ ℕ) (z : (Σ k, ι k) → ℂ) :
    eval z (map (Int.castRingHom ℂ) (monomial μ (1 : ℤ))) = ∏ p, z p ^ μ p := by
  rw [map_monomial, eval_monomial, map_one, one_mul, Finsupp.prod_fintype]
  intro p
  simp

/- English proof (translation)
Introduce `f hf`. Use `set F := map (Int.castRingHom ℂ) f`. Establish `hzero : (fun w => eval w F) ∘ γ =ᶠ[𝓝 y] fun _ => (0 : ℂ)` using `by filter_upwards [hpts] with w hw`. Conclude with `hw.2 f (hP0 hf)`. Establish `hd` using `(ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_hasFDerivAt_eval F (γ y)).comp y hγ.differentiableAt.hasFDerivAt`.

Establish `h0 : HasFDerivAt ((fun w => eval w F) ∘ γ) (0 : (Fin e → ℂ) →L[ℂ] ℂ) y` using `(hasFDerivAt_const (0 : ℂ) y).congr_of_eventuallyEq hzero`. Use `congrArg (fun L => L ξ) (hd.unique h0)` as an intermediate fact. Simplify `this` using `[ContinuousLinearMap.sum_apply, smul_eq_mul]`.
-/
theorem isConeTangent_of_sheet {P0 P : Ideal (MRing ι)} (hP0 : P0 ≤ P) {e : ℕ}
    {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {y : Fin e → ℂ} (hγ : AnalyticAt ℂ γ y)
    (hpts : ∀ᶠ y' in 𝓝 y, γ y' ∈ mcPts P) (ξ : Fin e → ℂ) :
    IsConeTangent (Int.castRingHom ℂ) P0 (γ y) (fderiv ℂ γ y ξ) := by
  intro f hf
  set F := map (Int.castRingHom ℂ) f
  have hzero : (fun w => eval w F) ∘ γ =ᶠ[𝓝 y] fun _ => (0 : ℂ) := by
    filter_upwards [hpts] with w hw
    exact hw.2 f (hP0 hf)
  have hd := (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_hasFDerivAt_eval F (γ y)).comp y
    hγ.differentiableAt.hasFDerivAt
  have h0 : HasFDerivAt ((fun w => eval w F) ∘ γ) (0 : (Fin e → ℂ) →L[ℂ] ℂ) y :=
    (hasFDerivAt_const (0 : ℂ) y).congr_of_eventuallyEq hzero
  have := congrArg (fun L => L ξ) (hd.unique h0)
  simpa [ContinuousLinearMap.sum_apply, smul_eq_mul] using this

/- English proof (translation)
Establish `hA : AnalyticAt ℂ γ y` using `sheet_analyticAt osgood h`. Establish `hpts : ∀ᶠ y' in 𝓝 y, γ y' ∈ mcPts P` using `h.2.mono fun _ hy' => hy'.2.1`. Establish `hy : γ y ∈ mcPts P` using `hpts.self_of_nhds`. Establish `hh : ContDiffAt ℝ 2 A.h (γ y)` using `(hsp.1.contDiffAt (isOpen_blocksNonzero.mem_nhds hy.1)).of_le (WithTop.coe_le_coe.2 le_top)`. Establish `hlog : ContDiffAt ℝ 2 (fun z => Real.log (A.h z)) (γ y)` using `hh.log (A.pos _ hy.1).ne'`.

Establish `h2 : ContDiffAt ℝ 2 (fun y' => Real.log (A.h (γ y'))) y` using `hlog.comp y (hA.contDiffAt.restrict_scalars ℝ)`. Rewrite using `[ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_maDensity_eq_maDens]`. Use `ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ _ fun _ => ?_` and prove the remaining obligations. Use `ReciprocityTheory.AnForm.A.hessC_posSemidef_of_levi _ _ h2 fun ξ => ?_` and prove the remaining obligations. Establish `hl` using `ReciprocityTheory.AnForm.levi_comp (φ := fun z => Real.log (A.h z)) ξ hA hlog`.

Express the relevant statement in the definitionally equal form `0 ≤ ReciprocityTheory.AnForm.levi ((fun z => Real.log (A.h z)) ∘ γ) y ξ`. Rewrite using `[hl]`. Conclude with `hsp.2 _ hy _ (isConeTangent_of_sheet hP0 hA hpts ξ)`.
-/
theorem maDensity_nonneg_of_sheet {P0 P : Ideal (MRing ι)} (hP0 : P0 ≤ P) {A : HermLine ι}
    (hsp : IsSemipositiveRel P0 P A) {e : ℕ} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    {y : Fin e → ℂ} {w : ((k : K) → ι k) → ℂ} {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ}
    (h : IsSheet P Ψ y w γ) :
    0 ≤ maDensity (fun _ y' => Real.log (A.h (γ y'))) y := by
  have hA : AnalyticAt ℂ γ y := sheet_analyticAt osgood h
  have hpts : ∀ᶠ y' in 𝓝 y, γ y' ∈ mcPts P := h.2.mono fun _ hy' => hy'.2.1
  have hy : γ y ∈ mcPts P := hpts.self_of_nhds
  have hh : ContDiffAt ℝ 2 A.h (γ y) :=
    (hsp.1.contDiffAt (isOpen_blocksNonzero.mem_nhds hy.1)).of_le (WithTop.coe_le_coe.2 le_top)
  have hlog : ContDiffAt ℝ 2 (fun z => Real.log (A.h z)) (γ y) := hh.log (A.pos _ hy.1).ne'
  have h2 : ContDiffAt ℝ 2 (fun y' => Real.log (A.h (γ y'))) y :=
    hlog.comp y (hA.contDiffAt.restrict_scalars ℝ)
  rw [ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_maDensity_eq_maDens]
  refine ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ _ fun _ => ?_
  refine ReciprocityTheory.AnForm.A.hessC_posSemidef_of_levi _ _ h2 fun ξ => ?_
  have hl := ReciprocityTheory.AnForm.levi_comp (φ := fun z => Real.log (A.h z)) ξ hA hlog
  change 0 ≤ ReciprocityTheory.AnForm.levi ((fun z => Real.log (A.h z)) ∘ γ) y ξ
  rw [hl]
  exact hsp.2 _ hy _ (isConeTangent_of_sheet hP0 hA hpts ξ)

/- English proof (translation)
Unfold `arInt ptsIntegral`. Use `split_ifs with hΨ`. Unfold `ptsIntegralAt`. Use `integral_nonpos fun y => ?_` and prove the remaining obligations. Establish `key : ∀ w, sheetDensity P hΨ.choose (fun (_ : Fin e) z => Real.log (A.h z)) (logNorm A s) y w ≤ 0`.

Introduce `w`. Unfold `sheetDensity`. Use `split_ifs with hγ`. Establish `hsh` using `hγ.choose_spec`. Establish `hz : hγ.choose y ∈ mcPts P` using `hsh.2.self_of_nhds.2.1`.

Establish `hpos` using `A.pos _ hz.1`. Establish `hg : logNorm A s (hγ.choose y) ≤ 0` using `Real.log_nonpos (div_nonneg (norm_nonneg _) hpos.le) ((div_le_one hpos).2 (hs _ hz))`. Conclude with `mul_nonpos_of_nonpos_of_nonneg hg (maDensity_nonneg_of_sheet hP0 hsp hsh)`. Conclude with `le_rfl`. Conclude with `finsum_nonpos' fun w => finsum_nonpos' fun _ => key w`.

Conclude with `le_rfl`.
-/
theorem arInt_nonpos {P0 P : Ideal (MRing ι)} (hP0 : P0 ≤ P) {A : HermLine ι}
    (hsp : IsSemipositiveRel P0 P A) {s : MRing ι}
    (hs : ∀ z ∈ mcPts P, ‖eval z (map (Int.castRingHom ℂ) s)‖ ≤ A.h z) (e : ℕ) :
    arInt P s A (fun _ : Fin e => A) ≤ 0 := by
  classical
  unfold arInt ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    refine integral_nonpos fun y => ?_
    have key : ∀ w, sheetDensity P hΨ.choose (fun (_ : Fin e) z => Real.log (A.h z))
        (logNorm A s) y w ≤ 0 := by
      intro w
      unfold sheetDensity
      split_ifs with hγ
      · have hsh := hγ.choose_spec
        have hz : hγ.choose y ∈ mcPts P := hsh.2.self_of_nhds.2.1
        have hpos := A.pos _ hz.1
        have hg : logNorm A s (hγ.choose y) ≤ 0 :=
          Real.log_nonpos (div_nonneg (norm_nonneg _) hpos.le)
            ((div_le_one hpos).2 (hs _ hz))
        exact mul_nonpos_of_nonpos_of_nonneg hg (maDensity_nonneg_of_sheet hP0 hsp hsh)
      · exact le_rfl
    exact finsum_nonpos' fun w => finsum_nonpos' fun _ => key w
  · exact le_rfl

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `P hP`. Conclude with `(GroundTheory.Heights₂.Heights.Inter.arithVarZero K ι P hP).elim`. Consider the case `succ m ih`.

Introduce `P hP hP0 hsp hmb`. Take `⟨μ, hμ, hμP⟩` from `exists_monomial_not_mem hP.2.1 a`. Use `set s : MRing ι := monomial μ (1 : ℤ) with hsdef`. Establish `hsa : IsMultiHomog s a` using `isMultiHomog_monomial hμ`. Establish `hAa : ∀ k, A.a k = a k` using `fun k => by rw [hA]`.

Establish `hsmall : ∀ z ∈ mcPts P, ‖eval z (map (Int.castRingHom ℂ) s)‖ ≤ A.h z`. Introduce `z hz`. Rewrite using `[hsdef, eval_monomial_one]`. Conclude with `hmb z hz μ hμ`. Establish `hR` using `hI.2.2 P m (fun _ => A) A s a hP (fun _ => hsp.1) hsp.1 hAa hsa hμP`.

Establish `hconst : (Fin.snoc (fun _ : Fin m => A) A : Fin (m + 1) → HermLine ι) = fun _ => A`. Use function extensionality and compare the values at `j`. Apply the tactic sequence `refine Fin.lastCases ?_ (fun j => ?_) j <;> simp`. Rewrite `hR` using `[hconst]`. Rewrite using `[hR, recR]`.

Use `sub_nonneg.2 (le_trans (arInt_nonpos hP0 hsp hsmall m) (finsum_nonneg fun W => finsum_nonneg fun hW => mul_nonneg (Nat.cast_nonneg _) ?_))` and prove the remaining obligations. Establish `hPW : P ≤ W` using `le_sup_left.trans hW.1.1.2`. Use `split_ifs with hH`. Establish `hWar` using `(divSuppArith K ι P m A s W hP ⟨a, hAa, hsa, hμP⟩ hW).1 hH`. Conclude with `ih W hWar (hP0.trans hPW) ⟨hsp.1, fun z hz w hw => hsp.2 z (mcPts_anti hPW hz) w hw⟩ (fun z hz μ' hμ' => hmb z (mcPts_anti hPW hz) μ' hμ')`.

Use `mul_nonneg (Int.cast_nonneg (geoNum_nonneg m W _ fun j k => ?_)) (Real.log_natCast_nonneg _)` and prove the remaining obligations. Simplify using `[hA]`.
-/
theorem nonneg_of_family (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ)
    (hI : IsIntersectionFamily I) (a : K → ℕ) (A : HermLine ι) (hA : A.a = fun k => (a k : ℤ))
    (P0 : Ideal (MRing ι)) (n : ℕ) :
    ∀ P : Ideal (MRing ι), IsArithVar P n → P0 ≤ P → IsSemipositiveRel P0 P A →
      MonomialsBounded P A a → 0 ≤ I P n (fun _ => A) := by
  induction n with
  | zero =>
    intro P hP
    exact (GroundTheory.Heights₂.Heights.Inter.arithVarZero K ι P hP).elim
  | succ m ih =>
    intro P hP hP0 hsp hmb
    obtain ⟨μ, hμ, hμP⟩ := exists_monomial_not_mem hP.2.1 a
    set s : MRing ι := monomial μ (1 : ℤ) with hsdef
    have hsa : IsMultiHomog s a := isMultiHomog_monomial hμ
    have hAa : ∀ k, A.a k = a k := fun k => by rw [hA]
    have hsmall : ∀ z ∈ mcPts P, ‖eval z (map (Int.castRingHom ℂ) s)‖ ≤ A.h z := by
      intro z hz
      rw [hsdef, eval_monomial_one]
      exact hmb z hz μ hμ
    have hR := hI.2.2 P m (fun _ => A) A s a hP (fun _ => hsp.1) hsp.1 hAa hsa hμP
    have hconst : (Fin.snoc (fun _ : Fin m => A) A : Fin (m + 1) → HermLine ι) = fun _ => A := by
      funext j
      refine Fin.lastCases ?_ (fun j => ?_) j <;> simp
    rw [hconst] at hR
    rw [hR, recR]
    refine sub_nonneg.2 (le_trans (arInt_nonpos hP0 hsp hsmall m)
      (finsum_nonneg fun W => finsum_nonneg fun hW => mul_nonneg (Nat.cast_nonneg _) ?_))
    have hPW : P ≤ W := le_sup_left.trans hW.1.1.2
    split_ifs with hH
    · have hWar := (divSuppArith K ι P m A s W hP ⟨a, hAa, hsa, hμP⟩ hW).1 hH
      exact ih W hWar (hP0.trans hPW) ⟨hsp.1, fun z hz w hw => hsp.2 z (mcPts_anti hPW hz) w hw⟩
        (fun z hz μ' hμ' => hmb z (mcPts_anti hPW hz) μ' hμ')
    · refine mul_nonneg (Int.cast_nonneg (geoNum_nonneg m W _ fun j k => ?_))
        (Real.log_natCast_nonneg _)
      simp [hA]

end G1

/- English proof (translation)
Introduce `K _ ι _ Ω _ y D a A P0 II _ hII hP _ hA hP0 hsp hmb _`. Conclude with `G1.nonneg_of_family (II K ι) (hII K ι) a A hA P0 (D + 1) _ hP hP0 hsp hmb`.
-/
theorem G1.proof : G1.Statement := by
  intro K _ ι _ Ω _ y D a A P0 II _ hII hP _ hA hP0 hsp hmb _
  exact G1.nonneg_of_family (II K ι) (hII K ι) a A hA P0 (D + 1) _ hP hP0 hsp hmb

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
