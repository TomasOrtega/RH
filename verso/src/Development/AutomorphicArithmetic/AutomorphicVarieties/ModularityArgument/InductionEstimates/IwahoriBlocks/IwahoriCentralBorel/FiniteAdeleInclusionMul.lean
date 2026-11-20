import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.SimpleIn
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.ParLaw
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.LevBlock
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.TensLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.BlockFrameConjugationIdentity
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.OpenStab
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.RepsSmul

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

/- English proof (translation)
The claim follows from `map_one (MultiplicityOne.finProj K n)`.
-/
private theorem finite_projection_one {K : Type} [Field K] [NumberField K] {n : ℕ} : fin1 (1 : FA K n) = 1 :=
  map_one (MultiplicityOne.finProj K n)

/- English proof (translation)
The claim follows from `map_mul (MultiplicityOne.finProj K n) a b`.
-/
private theorem finite_adele_inclusion_mul {K : Type} [Field K] [NumberField K] {n : ℕ} (a b : FA K n) : fin1 (a * b) = fin1 a * fin1 b :=
  map_mul (MultiplicityOne.finProj K n) a b

/- English proof (translation)
Establish `h : (⟨Real.exp 0, Real.exp_pos 0⟩ : {r : ℝ // 0 < r}) = 1` using `Subtype.ext (by simp)`. Rewrite using `[zt, h, map_one]`.
-/
private theorem zt0 {K : Type} [Field K] [NumberField K] : zt K 0 = 1 := by
  have h : (⟨Real.exp 0, Real.exp_pos 0⟩ : {r : ℝ // 0 < r}) = 1 := Subtype.ext (by simp)
  rw [zt, h, map_one]

/- English proof (translation)
Rewrite using `[blkLaws.1, neg_zero, zt0, mul_one, mul_one]`.
-/
private theorem lv0 {K : Type} [Field K] [NumberField K] (a b : G1 K 2) :
    ((lv a b 0 : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) =
      blk (a : AdelicGLn.AdelicGL K 2) (b : AdelicGLn.AdelicGL K 2) := by
  rw [blkLaws.1, neg_zero, zt0, mul_one, mul_one]

/- English proof (translation)
Establish `h` using `(hpSpec (K := K)).1 0 a b 0 x`. Establish `h0 : (nn 0 : G1 K (2 + 2)) = 1` using `unipOne_zero 2`. Rewrite `h` using `[h0, one_mul, zero_add]`. Then use the resulting hypothesis.
-/
private theorem hh0 {K : Type} [Field K] [NumberField K] (a b : G1 K 2) (x : G1 K (2 + 2)) :
    HH (lv a b 0 * x) = HH x := by
  have h := (hpSpec (K := K)).1 0 a b 0 x
  have h0 : (nn 0 : G1 K (2 + 2)) = 1 := unipOne_zero 2
  rwa [h0, one_mul, zero_add] at h

/- English proof (translation)
Use `hs.ray ⟨Real.exp t, Real.exp_pos t⟩ _ g ?_` and prove the remaining obligations. Establish `h : (⟨Real.exp (-t), Real.exp_pos (-t)⟩ : {r : ℝ // 0 < r}) = (⟨Real.exp t, Real.exp_pos t⟩ : {r : ℝ // 0 < r})⁻¹`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `Real.exp (-t) = (Real.exp t)⁻¹`. Rewrite using `[Real.exp_neg]`.

Rewrite using `[Subgroup.coe_mul, blkLaws.1, zt, zt, h]`. Simplify using the standard rewrite rules.
-/
private theorem sec_ray {K : Type} [Field K] [NumberField K] {μ₂ : Measure (G1 K 2)} {τ₁ τ₂ : Submodule ℂ (L2 μ₂)}
    {f : G1 K (2 + 2) → ℂ} (hs : IsSec τ₁ τ₂ f) (t : ℝ) (g : G1 K (2 + 2)) : f (lv 1 1 t * g) = f g := by
  refine hs.ray ⟨Real.exp t, Real.exp_pos t⟩ _ g ?_
  have h : (⟨Real.exp (-t), Real.exp_pos (-t)⟩ : {r : ℝ // 0 < r}) = (⟨Real.exp t, Real.exp_pos t⟩ : {r : ℝ // 0 < r})⁻¹ := by
    apply Subtype.ext
    change Real.exp (-t) = (Real.exp t)⁻¹
    rw [Real.exp_neg]
  rw [Subgroup.coe_mul, blkLaws.1, zt, zt, h]
  simp

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Use `⟨0, τ.zero_mem, ?_⟩` and prove the remaining obligations. Use `filter_upwards [(quasiMeasurePreserving_mk (Gam K n) μ).ae (Lp.coeFn_zero ℂ 2 (quotientMeasure (Gam K n) μ))] with y hy`. Simplify using `using hy`.

Consider the case `insert i s hi ih`. Take `⟨v, hv, hr⟩` from `ih`. Take `⟨u, hu, hq⟩` from `h i`. Use `⟨c i • u + v, τ.add_mem (τ.smul_mem _ hu) hv, ?_⟩` and prove the remaining obligations. Use `filter_upwards [(quasiMeasurePreserving_mk (Gam K n) μ).ae (Lp.coeFn_add (c i • u) v), (quasiMeasurePreserving_mk (Gam K n) μ).ae (Lp.coeFn_smul (c i) u), hr, hq] with y e₁ e₂ e₃ e₄`.

Rewrite using `[e₁, Pi.add_apply, e₂, Pi.smul_apply, e₃, e₄, Finset.sum_insert hi, smul_eq_mul]`.
-/
private theorem reps_comb {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure]
    (τ : Submodule ℂ (L2 μ)) {ι : Type} (s : Finset ι) (φ : ι → G1 K n → ℂ) (c : ι → ℂ)
    (h : ∀ i, ∃ v ∈ τ, Reps μ v (φ i)) : ∃ v ∈ τ, Reps μ v (fun y => ∑ i ∈ s, c i * φ i y) := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨0, τ.zero_mem, ?_⟩
    filter_upwards [(quasiMeasurePreserving_mk (Gam K n) μ).ae (Lp.coeFn_zero ℂ 2 (quotientMeasure (Gam K n) μ))] with y hy
    simpa using hy
  | insert i s hi ih =>
    obtain ⟨v, hv, hr⟩ := ih
    obtain ⟨u, hu, hq⟩ := h i
    refine ⟨c i • u + v, τ.add_mem (τ.smul_mem _ hu) hv, ?_⟩
    filter_upwards [(quasiMeasurePreserving_mk (Gam K n) μ).ae (Lp.coeFn_add (c i • u) v),
      (quasiMeasurePreserving_mk (Gam K n) μ).ae (Lp.coeFn_smul (c i) u), hr, hq] with y e₁ e₂ e₃ e₄
    rw [e₁, Pi.add_apply, e₂, Pi.smul_apply, e₃, e₄, Finset.sum_insert hi, smul_eq_mul]

/- English proof (translation)
Simplify using `only [flat, zero_add]`. Rewrite using `[show HP 2 2 (lv a b 0 * x) = HH x from hh0 a b x]`.
-/
private theorem flat_lv {K : Type} [Field K] [NumberField K] (f : G1 K (2 + 2) → ℂ) (a b : G1 K 2) (x : G1 K (2 + 2)) :
    flat 0 f (lv a b 0 * x) = Complex.exp (2 * (HH x : ℂ)) * f (lv a b 0 * x) := by
  simp only [flat, zero_add]
  rw [show HP 2 2 (lv a b 0 * x) = HH x from hh0 a b x]

/- English proof (translation)
Take `⟨d, φ, ψ, hφ, hψ, hx⟩` from `hs.levi (arc1 k₀ * fin1 (ι₄ g))`. Establish `hx' : ∀ a b, f (lv a b 0 * arc1 k₀ * fin1 (ι₄ g)) = ∑ i, φ i a * ψ i b` using `fun a b => hx a b _ (by rw [mul_assoc, Subgroup.coe_mul (x := lv a b 0), lv0])`. Take `⟨U₂, hU₂, hlev⟩` from `levBlock w ι₄ hw h₄ U hU g`. Establish `hv` using `hL.val f hs hfa (ι₄ g)`. Establish `hcl : Continuous fun p : G1 K 2 × G1 K 2 => f (lv p.1 p.2 0 * arc1 k₀ * fin1 (ι₄ g))` using `hs.cont.comp (((blkLaws (K := K)).2.2.2.1.comp (continuous_fst.prodMk (continuous_snd.prodMk continuous_const))).mul continuous_const |>.mul continuous_const)`.

Establish `hsplit₁ : ∀ a b (u : G1 K 2), lv (a * u) b 0 = lv a b 0 * lv u 1 0` using `fun a b u => by`. Rewrite using `[blkLaws.2.1]`. Simplify using the standard rewrite rules. Establish `hsplit₂ : ∀ a b (u : G1 K 2), lv a (b * u) 0 = lv a b 0 * lv 1 u 0` using `fun a b u => by`. Rewrite using `[blkLaws.2.1]`.

Simplify using the standard rewrite rules. Establish `hF : (fun m : G1 K 2 × G1 K 2 => flat 0 f (lv m.1 m.2 0 * arc1 k₀ * fin1 (ι₄ g))) = Complex.exp (2 * (HH (arc1 k₀ * fin1 (ι₄ g)) : ℂ)) • fun m : G1 K 2 × G1 K 2 => f (lv m.1 m.2 0 * arc1 k₀ * fin1 (ι₄ g))`. Use function extensionality and compare the values at `m`. Rewrite using `[mul_assoc, flat_lv]`. Simplify using `[mul_assoc]`.

Rewrite using `[hF]`. Use `Submodule.smul_mem _ _ ((tensLaws _ _).2 _ d φ ψ (fun x => hx' x.1 x.2) (fun b => ?_) (fun a => ?_))` and prove the remaining obligations. Use `Submodule.subset_span ⟨hcl.comp (continuous_id.prodMk continuous_const), ?_, hv.1 b, U₂, hU₂, fun u hu a => ?_⟩` and prove the remaining obligations. Establish `h` using `reps_comb μ₂ τ₁ Finset.univ φ (fun i => ψ i b) (fun i => let ⟨v, hv, hr⟩ := (hφ i).2; ⟨v, hv, hr⟩)`. Simplify `h` using `only [hx', mul_comm]`.

Take `⟨u', hu', hk⟩` from `hlev u hu 1 (one_mem _)`. Establish `h1` using `hk k₀`. Rewrite `h1` using `[finite_projection_one]`. Establish `h2 : lv (a * fin1 u) b 0 * arc1 k₀ * fin1 (ι₄ g) = lv a b 0 * arc1 k₀ * fin1 (ι₄ g) * fin1 u'`. Rewrite using `[hsplit₁, mul_assoc (lv a b 0), mul_assoc (lv a b 0), h1]`.

Simplify using `only [mul_assoc]`. Use `show f (lv (a * fin1 u) b 0 * arc1 k₀ * fin1 (ι₄ g)) = f (lv a b 0 * arc1 k₀ * fin1 (ι₄ g))`. Rewrite using `[h2]`. Conclude with `hfU u' hu' _`. Use `Submodule.subset_span ⟨hcl.comp (continuous_const.prodMk continuous_id), ?_, hv.2 a, U₂, hU₂, fun u hu b => ?_⟩` and prove the remaining obligations.

Establish `h` using `reps_comb μ₂ τ₂ Finset.univ ψ (fun i => φ i a) (fun i => let ⟨v, hv, hr⟩ := (hψ i).2; ⟨v, hv, hr⟩)`. Simplify `h` using `only [hx']`. Take `⟨u', hu', hk⟩` from `hlev 1 (one_mem _) u hu`. Establish `h1` using `hk k₀`. Rewrite `h1` using `[finite_projection_one]`.

Establish `h2 : lv a (b * fin1 u) 0 * arc1 k₀ * fin1 (ι₄ g) = lv a b 0 * arc1 k₀ * fin1 (ι₄ g) * fin1 u'`. Rewrite using `[hsplit₂, mul_assoc (lv a b 0), mul_assoc (lv a b 0), h1]`. Simplify using `only [mul_assoc]`. Use `show f (lv a (b * fin1 u) 0 * arc1 k₀ * fin1 (ι₄ g)) = f (lv a b 0 * arc1 k₀ * fin1 (ι₄ g))`. Rewrite using `[h2]`.

Conclude with `hfU u' hu' _`.
-/
private theorem val_mem {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] {μ₂ : Measure (G1 K 2)} [μ₂.IsHaarMeasure]
    {τ₁ τ₂ : Submodule ℂ (L2 μ₂)} {κ : Measure (archCompact K (2 + 2))} {e : archCompact K (2 + 2) → ℂ} {κ₂ p₁ p₂ k₀}
    (hL : ArchLine τ₁ τ₂ κ e κ₂ p₁ p₂ k₀) {r : ℕ} (w : Fin r → Pl K) (ι₄ : GS (2 + 2) w →* FA K (2 + 2))
    (hw : Function.Injective w) (h₄ : IsEmb w ι₄) {f : G1 K (2 + 2) → ℂ} (hs : IsSec τ₁ τ₂ f) (hfa : FixA κ e f)
    {U : ∀ v : Pl K, Subgroup (Gw (2 + 2) v)} (hU : Lev U) (hfU : FixF (levOn (im w) U) f) (g : GS (2 + 2) w) :
    (fun m : G1 K 2 × G1 K 2 => flat 0 f (lv m.1 m.2 0 * arc1 k₀ * fin1 (ι₄ g))) ∈
      tensFn (Xs μ₂ τ₁ κ₂ p₁ (im w)) (Xs μ₂ τ₂ κ₂ p₂ (im w)) := by
  obtain ⟨d, φ, ψ, hφ, hψ, hx⟩ := hs.levi (arc1 k₀ * fin1 (ι₄ g))
  have hx' : ∀ a b, f (lv a b 0 * arc1 k₀ * fin1 (ι₄ g)) = ∑ i, φ i a * ψ i b := fun a b =>
    hx a b _ (by rw [mul_assoc, Subgroup.coe_mul (x := lv a b 0), lv0])
  obtain ⟨U₂, hU₂, hlev⟩ := levBlock w ι₄ hw h₄ U hU g
  have hv := hL.val f hs hfa (ι₄ g)
  have hcl : Continuous fun p : G1 K 2 × G1 K 2 => f (lv p.1 p.2 0 * arc1 k₀ * fin1 (ι₄ g)) :=
    hs.cont.comp (((blkLaws (K := K)).2.2.2.1.comp
      (continuous_fst.prodMk (continuous_snd.prodMk continuous_const))).mul continuous_const |>.mul continuous_const)
  have hsplit₁ : ∀ a b (u : G1 K 2), lv (a * u) b 0 = lv a b 0 * lv u 1 0 := fun a b u => by
    rw [blkLaws.2.1]; simp
  have hsplit₂ : ∀ a b (u : G1 K 2), lv a (b * u) 0 = lv a b 0 * lv 1 u 0 := fun a b u => by
    rw [blkLaws.2.1]; simp
  have hF : (fun m : G1 K 2 × G1 K 2 => flat 0 f (lv m.1 m.2 0 * arc1 k₀ * fin1 (ι₄ g))) =
      Complex.exp (2 * (HH (arc1 k₀ * fin1 (ι₄ g)) : ℂ)) • fun m : G1 K 2 × G1 K 2 => f (lv m.1 m.2 0 * arc1 k₀ * fin1 (ι₄ g)) := by
    funext m
    rw [mul_assoc, flat_lv]
    simp [mul_assoc]
  rw [hF]
  refine Submodule.smul_mem _ _ ((tensLaws _ _).2 _ d φ ψ (fun x => hx' x.1 x.2) (fun b => ?_) (fun a => ?_))
  · refine Submodule.subset_span ⟨hcl.comp (continuous_id.prodMk continuous_const), ?_, hv.1 b, U₂, hU₂, fun u hu a => ?_⟩
    · have h := reps_comb μ₂ τ₁ Finset.univ φ (fun i => ψ i b) (fun i => let ⟨v, hv, hr⟩ := (hφ i).2; ⟨v, hv, hr⟩)
      simpa only [hx', mul_comm] using h
    · obtain ⟨u', hu', hk⟩ := hlev u hu 1 (one_mem _)
      have h1 := hk k₀
      rw [finite_projection_one] at h1
      have h2 : lv (a * fin1 u) b 0 * arc1 k₀ * fin1 (ι₄ g) = lv a b 0 * arc1 k₀ * fin1 (ι₄ g) * fin1 u' := by
        rw [hsplit₁, mul_assoc (lv a b 0), mul_assoc (lv a b 0), h1]
        simp only [mul_assoc]
      show f (lv (a * fin1 u) b 0 * arc1 k₀ * fin1 (ι₄ g)) = f (lv a b 0 * arc1 k₀ * fin1 (ι₄ g))
      rw [h2]
      exact hfU u' hu' _
  · refine Submodule.subset_span ⟨hcl.comp (continuous_const.prodMk continuous_id), ?_, hv.2 a, U₂, hU₂, fun u hu b => ?_⟩
    · have h := reps_comb μ₂ τ₂ Finset.univ ψ (fun i => φ i a) (fun i => let ⟨v, hv, hr⟩ := (hψ i).2; ⟨v, hv, hr⟩)
      simpa only [hx'] using h
    · obtain ⟨u', hu', hk⟩ := hlev 1 (one_mem _) u hu
      have h1 := hk k₀
      rw [finite_projection_one] at h1
      have h2 : lv a (b * fin1 u) 0 * arc1 k₀ * fin1 (ι₄ g) = lv a b 0 * arc1 k₀ * fin1 (ι₄ g) * fin1 u' := by
        rw [hsplit₂, mul_assoc (lv a b 0), mul_assoc (lv a b 0), h1]
        simp only [mul_assoc]
      show f (lv a (b * fin1 u) 0 * arc1 k₀ * fin1 (ι₄ g)) = f (lv a b 0 * arc1 k₀ * fin1 (ι₄ g))
      rw [h2]
      exact hfU u' hu' _

/- English proof (translation)
Take `⟨hA, hB⟩` from `parLaw w ι₂ ι₄ hw h₂ h₄`. Take `⟨X, t, hX, ht⟩` from `hB p`. Take `⟨X', hX'⟩` from `hA m.1 m.2 0 X`. Establish `hc : Commute (arc1 k₀) (fin1 (ι₄ (piIncl (fun i => PW (w i)) p)))` using `(levLaws (K := K) (2 + 2) (im w)).2.2.1 k₀ _`. Establish `key : lv m.1 m.2 0 * arc1 k₀ * fin1 (ι₄ (piIncl (fun i => PW (w i)) p * g)) = nn X' * lv (m.1 * (blocks ι₂ p).1) (m.2 * (blocks ι₂ p).2) t * (arc1 k₀ * fin1 (ι₄ g))`.

Establish `hl : lv m.1 m.2 0 * lv (blocks ι₂ p).1 (blocks ι₂ p).2 t = lv (m.1 * (blocks ι₂ p).1) (m.2 * (blocks ι₂ p).2) t`. Rewrite using `[blkLaws.2.1, zero_add]`. Rewrite using `[map_mul, finite_adele_inclusion_mul, ← hl]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hX]`.

Simplify using `only [mul_assoc]`. Use `_ = _ := by rw [hX']; simp only [mul_assoc]`. Establish `hray : lv (m.1 * (blocks ι₂ p).1) (m.2 * (blocks ι₂ p).2) t = lv 1 1 t * lv (m.1 * (blocks ι₂ p).1) (m.2 * (blocks ι₂ p).2) 0`. Rewrite using `[blkLaws.2.1]`. Simplify using the standard rewrite rules.

Establish `hf : f (nn X' * lv (m.1 * (blocks ι₂ p).1) (m.2 * (blocks ι₂ p).2) t * (arc1 k₀ * fin1 (ι₄ g))) = f (lv (m.1 * (blocks ι₂ p).1) (m.2 * (blocks ι₂ p).2) 0 * (arc1 k₀ * fin1 (ι₄ g)))`. Rewrite using `[mul_assoc, hs.unip, hray, mul_assoc, sec_ray hs]`. Establish `hh` using `(hpSpec (K := K)).1 X' (m.1 * (blocks ι₂ p).1) (m.2 * (blocks ι₂ p).2) t (arc1 k₀ * fin1 (ι₄ g))`. Rewrite using `[key, mul_assoc (lv _ _ 0), flat_lv, ← ht]`. Simplify using `only [flat, zero_add]`.

Rewrite using `[show HP 2 2 (nn X' * lv (m.1 * (blocks ι₂ p).1) (m.2 * (blocks ι₂ p).2) t * (arc1 k₀ * fin1 (ι₄ g))) = t + HH (arc1 k₀ * fin1 (ι₄ g)) from hh, hf]`. Use `push_cast`. Rewrite using `[mul_add, Complex.exp_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem law_eq {K : Type} [Field K] [NumberField K] {μ₂ : Measure (G1 K 2)}
    {τ₁ τ₂ : Submodule ℂ (L2 μ₂)} {r : ℕ} (w : Fin r → Pl K) (ι₂ : GS 2 w →* FA K 2) (ι₄ : GS (2 + 2) w →* FA K (2 + 2))
    (hw : Function.Injective w) (h₂ : IsEmb w ι₂) (h₄ : IsEmb w ι₄) {f : G1 K (2 + 2) → ℂ} (hs : IsSec τ₁ τ₂ f)
    (k₀ : archCompact K (2 + 2)) (p : ∀ i, PW (w i)) (g : GS (2 + 2) w) (m : G1 K 2 × G1 K 2) :
    flat 0 f (lv m.1 m.2 0 * arc1 k₀ * fin1 (ι₄ (piIncl (fun i => PW (w i)) p * g))) =
      (dS w p : ℂ) * flat 0 f (lv (m.1 * (blocks ι₂ p).1) (m.2 * (blocks ι₂ p).2) 0 * arc1 k₀ * fin1 (ι₄ g)) := by
  obtain ⟨hA, hB⟩ := parLaw w ι₂ ι₄ hw h₂ h₄
  obtain ⟨X, t, hX, ht⟩ := hB p
  obtain ⟨X', hX'⟩ := hA m.1 m.2 0 X
  have hc : Commute (arc1 k₀) (fin1 (ι₄ (piIncl (fun i => PW (w i)) p))) := (levLaws (K := K) (2 + 2) (im w)).2.2.1 k₀ _
  have key : lv m.1 m.2 0 * arc1 k₀ * fin1 (ι₄ (piIncl (fun i => PW (w i)) p * g)) =
      nn X' * lv (m.1 * (blocks ι₂ p).1) (m.2 * (blocks ι₂ p).2) t * (arc1 k₀ * fin1 (ι₄ g)) := by
    have hl : lv m.1 m.2 0 * lv (blocks ι₂ p).1 (blocks ι₂ p).2 t = lv (m.1 * (blocks ι₂ p).1) (m.2 * (blocks ι₂ p).2) t := by
      rw [blkLaws.2.1, zero_add]
    rw [map_mul, finite_adele_inclusion_mul, ← hl]
    calc lv m.1 m.2 0 * arc1 k₀ * (fin1 (ι₄ (piIncl (fun i => PW (w i)) p)) * fin1 (ι₄ g))
        = lv m.1 m.2 0 * (arc1 k₀ * fin1 (ι₄ (piIncl (fun i => PW (w i)) p))) * fin1 (ι₄ g) := by simp only [mul_assoc]
      _ = lv m.1 m.2 0 * (fin1 (ι₄ (piIncl (fun i => PW (w i)) p)) * arc1 k₀) * fin1 (ι₄ g) := by rw [hc.eq]
      _ = (lv m.1 m.2 0 * nn X) * lv (blocks ι₂ p).1 (blocks ι₂ p).2 t * (arc1 k₀ * fin1 (ι₄ g)) := by
          rw [hX]; simp only [mul_assoc]
      _ = _ := by rw [hX']; simp only [mul_assoc]
  have hray : lv (m.1 * (blocks ι₂ p).1) (m.2 * (blocks ι₂ p).2) t =
      lv 1 1 t * lv (m.1 * (blocks ι₂ p).1) (m.2 * (blocks ι₂ p).2) 0 := by
    rw [blkLaws.2.1]; simp
  have hf : f (nn X' * lv (m.1 * (blocks ι₂ p).1) (m.2 * (blocks ι₂ p).2) t * (arc1 k₀ * fin1 (ι₄ g))) =
      f (lv (m.1 * (blocks ι₂ p).1) (m.2 * (blocks ι₂ p).2) 0 * (arc1 k₀ * fin1 (ι₄ g))) := by
    rw [mul_assoc, hs.unip, hray, mul_assoc, sec_ray hs]
  have hh := (hpSpec (K := K)).1 X' (m.1 * (blocks ι₂ p).1) (m.2 * (blocks ι₂ p).2) t (arc1 k₀ * fin1 (ι₄ g))
  rw [key, mul_assoc (lv _ _ 0), flat_lv, ← ht]
  simp only [flat, zero_add]
  rw [show HP 2 2 (nn X' * lv (m.1 * (blocks ι₂ p).1) (m.2 * (blocks ι₂ p).2) t * (arc1 k₀ * fin1 (ι₄ g))) = t + HH (arc1 k₀ * fin1 (ι₄ g)) from hh, hf]
  push_cast
  rw [mul_add, Complex.exp_add]
  ring

/- English proof (translation)
Introduce `K _ _ _ μ₂ _ τ₁ τ₂ κ e κ₂ p₁ p₂ k₀ _ hL r w ι₂ ι₄ hw h₂ h₄ φ hφ`. Take `⟨hiff, hsm⟩` from `zMem μ₂ τ₁ τ₂ κ e hL.idem`. Establish `hop` using `(hsm w ι₄ hw h₄ φ hφ).1`. Take `⟨f, hs, hfa, ⟨U, hU, hfU⟩, rfl⟩` from `(hiff _ φ).1 hφ`. Use `Submodule.mem_inf.2 ⟨?_, ?_⟩` and prove the remaining obligations.

Use `⟨fun g => val_mem hL w ι₄ hw h₄ hs hfa hU hfU g, fun p g => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `m`. Establish `h` using `law_eq (τ₁ := τ₁) (τ₂ := τ₂) w ι₂ ι₄ hw h₂ h₄ hs k₀ p g m`. Simplify `h` using `[ev, xS, twist, rightReg, LinearMap.funLeft]`. Establish `hst : ∀ g, rS ι₄ g (flat 0 f) = flat 0 f → rightReg ℂ (GS (2 + 2) w) (G1 K 2 × G1 K 2 → ℂ) g (ev ι₄ k₀ (flat 0 f)) = ev ι₄ k₀ (flat 0 f)`.

Introduce `g hg`. Use `conv_rhs => rw [← hg]`. Use function extensionality and compare the values at `x m`. Simplify using `[ev, rS, rightReg, LinearMap.funLeft, mul_assoc]`. Use `show IsOpen {g | rightReg ℂ (GS (2 + 2) w) (G1 K 2 × G1 K 2 → ℂ) g (ev ι₄ k₀ (flat 0 f)) = ev ι₄ k₀ (flat 0 f)}`.

Use `isOpen_iff_mem_nhds.2 fun g₀ hg₀ => ?_` and prove the remaining obligations. Establish `h1 : (1 : GS (2 + 2) w) ∈ {g | rS ι₄ g (flat 0 f) = flat 0 f}` using `by simp`. Establish `hn : (fun x => g₀⁻¹ * x) ⁻¹' {g | rS ι₄ g (flat 0 f) = flat 0 f} ∈ 𝓝 g₀` using `((continuous_const.mul continuous_id).continuousAt (x := g₀)).preimage_mem_nhds (hop.mem_nhds (by simpa using h1))`. Use `filter_upwards [hn] with x hx`. Establish `h2` using `hst _ hx`.

Establish `h3 : x = g₀ * (g₀⁻¹ * x)` using `by group`. Use `show rightReg ℂ (GS (2 + 2) w) (G1 K 2 × G1 K 2 → ℂ) x _ = _`. Rewrite using `[h3, map_mul, Module.End.mul_apply, h2]`. Conclude with `hg₀`.
-/
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.evMem :
    ∀ {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)) (κ : Measure (archCompact K (2 + 2))) (e : archCompact K (2 + 2) → ℂ) κ₂ p₁ p₂ k₀, Pair μ₂ τ₁ τ₂ → ArchLine τ₁ τ₂ κ e κ₂ p₁ p₂ k₀ →
      ∀ {r : ℕ} (w : Fin r → Pl K) (ι₂ : GS 2 w →* FA K 2) (ι₄ : GS (2 + 2) w →* FA K (2 + 2)), Function.Injective w → IsEmb w ι₂ → IsEmb w ι₄ →
      ∀ φ ∈ Zs τ₁ τ₂ κ e (im w), ev ι₄ k₀ φ ∈ IndF (piIncl fun i => PW (w i)) (xS ι₂) (tensFn (Xs μ₂ τ₁ κ₂ p₁ (im w)) (Xs μ₂ τ₂ κ₂ p₂ (im w))) := by
  intro K _ _ _ μ₂ _ τ₁ τ₂ κ e κ₂ p₁ p₂ k₀ _ hL r w ι₂ ι₄ hw h₂ h₄ φ hφ
  obtain ⟨hiff, hsm⟩ := zMem μ₂ τ₁ τ₂ κ e hL.idem
  have hop := (hsm w ι₄ hw h₄ φ hφ).1
  obtain ⟨f, hs, hfa, ⟨U, hU, hfU⟩, rfl⟩ := (hiff _ φ).1 hφ
  refine Submodule.mem_inf.2 ⟨?_, ?_⟩
  · refine ⟨fun g => val_mem hL w ι₄ hw h₄ hs hfa hU hfU g, fun p g => ?_⟩
    funext m
    have h := law_eq (τ₁ := τ₁) (τ₂ := τ₂) w ι₂ ι₄ hw h₂ h₄ hs k₀ p g m
    simpa [ev, xS, twist, rightReg, LinearMap.funLeft] using h
  · have hst : ∀ g, rS ι₄ g (flat 0 f) = flat 0 f →
        rightReg ℂ (GS (2 + 2) w) (G1 K 2 × G1 K 2 → ℂ) g (ev ι₄ k₀ (flat 0 f)) = ev ι₄ k₀ (flat 0 f) := by
      intro g hg
      conv_rhs => rw [← hg]
      funext x m
      simp [ev, rS, rightReg, LinearMap.funLeft, mul_assoc]
    show IsOpen {g | rightReg ℂ (GS (2 + 2) w) (G1 K 2 × G1 K 2 → ℂ) g (ev ι₄ k₀ (flat 0 f)) = ev ι₄ k₀ (flat 0 f)}
    refine isOpen_iff_mem_nhds.2 fun g₀ hg₀ => ?_
    have h1 : (1 : GS (2 + 2) w) ∈ {g | rS ι₄ g (flat 0 f) = flat 0 f} := by simp
    have hn : (fun x => g₀⁻¹ * x) ⁻¹' {g | rS ι₄ g (flat 0 f) = flat 0 f} ∈ 𝓝 g₀ :=
      ((continuous_const.mul continuous_id).continuousAt (x := g₀)).preimage_mem_nhds
        (hop.mem_nhds (by simpa using h1))
    filter_upwards [hn] with x hx
    have h2 := hst _ hx
    have h3 : x = g₀ * (g₀⁻¹ * x) := by group
    show rightReg ℂ (GS (2 + 2) w) (G1 K 2 × G1 K 2 → ℂ) x _ = _
    rw [h3, map_mul, Module.End.mul_apply, h2]
    exact hg₀
