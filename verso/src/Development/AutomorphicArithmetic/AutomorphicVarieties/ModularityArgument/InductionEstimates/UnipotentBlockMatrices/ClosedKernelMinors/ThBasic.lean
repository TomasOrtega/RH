import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.LocFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.SumField
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.PkLaws

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

/- English proof (translation)
Establish `h : (QuotientGroup.rightRel P) ((Quotient.mk (QuotientGroup.rightRel P) a).out) a` using `Quotient.mk_out (s := QuotientGroup.rightRel P) a`. Use `Quotient.sound ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(QuotientGroup.rightRel P) _ _`. Rewrite `h`, the goal using `[QuotientGroup.rightRel_apply]`. Simplify `h` using `[mul_assoc]`.
-/
private theorem mk_out_mul {G : Type*} [Group G] (P : Subgroup G) (a b : G) :
    (Quotient.mk _ ((Quotient.mk (QuotientGroup.rightRel P) a).out * b) : Quotient (QuotientGroup.rightRel P)) =
      Quotient.mk _ (a * b) := by
  have h : (QuotientGroup.rightRel P) ((Quotient.mk (QuotientGroup.rightRel P) a).out) a := Quotient.mk_out (s := QuotientGroup.rightRel P) a
  refine Quotient.sound ?_
  change (QuotientGroup.rightRel P) _ _
  rw [QuotientGroup.rightRel_apply] at h ⊢
  simpa [mul_assoc] using h

/- English proof (translation)
Use `Function.bijective_iff_has_inverse.2 ⟨fun q => Quotient.mk _ (q.out * b⁻¹), fun q => ?_, fun q => ?_⟩` and prove the remaining obligations. Simplify using `only [mk_out_mul, mul_inv_cancel_right, Quotient.out_eq]`. Simplify using `only [mk_out_mul, inv_mul_cancel_right, Quotient.out_eq]`.
-/
private theorem bij_shift {G : Type*} [Group G] (P : Subgroup G) (b : G) :
    Function.Bijective fun q : Quotient (QuotientGroup.rightRel P) =>
      (Quotient.mk _ (q.out * b) : Quotient (QuotientGroup.rightRel P)) := by
  refine Function.bijective_iff_has_inverse.2 ⟨fun q => Quotient.mk _ (q.out * b⁻¹), fun q => ?_, fun q => ?_⟩
  · simp only [mk_out_mul, mul_inv_cancel_right, Quotient.out_eq]
  · simp only [mk_out_mul, inv_mul_cancel_right, Quotient.out_eq]

/- English proof (translation)
Use `isFiniteMeasure_quotientMeasure (K := K) (n := n) μ` as an intermediate fact. Set `f : RightCosetSpace (Gam K n) → ℂ` to `fun x => φ x.out`. Establish `hf : ∀ g, f (mk (Gam K n) g) = φ g` using `fun g => by`. Take `⟨γ, hγ⟩` from `(mk_eq_mk_iff (Γ := Gam K n) (g := (mk (Gam K n) g).out) (h := g)).1 (Quotient.out_eq _)`. Express the relevant statement in the definitionally equal form `φ _ = _`.

Rewrite using `[← hγ]`. Conclude with `hi γ γ.2 g`. Establish `hfc : Continuous f`. Rewrite using `[(isOpenQuotientMap_mk (Gam K n)).isQuotientMap.continuous_iff]`. Establish `: f ∘ mk (Gam K n) = φ` using `funext hf`.

Rewrite using `[this]` and apply the resulting hypothesis. Establish `hm : MemLp f 2 (quotientMeasure (Gam K n) μ)` using `MemLp.of_bound hfc.aestronglyMeasurable C (Eventually.of_forall fun x => hC _)`. Use `⟨hm.toLp f, ?_⟩` and prove the remaining obligations. Establish `h1` using `hm.coeFn_toLp`. Establish `h2 : ∀ᵐ y ∂μ.restrict (fundamentalDomain (Gam K n)), (hm.toLp f) (mk (Gam K n) y) = f (mk (Gam K n) y)` using `ae_of_ae_map (measurable_mk (Gam K n)).aemeasurable h1`.

Establish `hF` using `isFundamentalDomain_fundamentalDomain (Gam K n) μ`. Establish `h3 : μ {y | ¬ (hm.toLp f) (mk (Gam K n) y) = f (mk (Gam K n) y)} = 0`. Use `hF.measure_zero_of_invariant _ (fun γ => ?_) ?_` and prove the remaining obligations. Use extensionality with `y`. Simplify using `[Set.mem_smul_set_iff_inv_smul_mem]`.

Rewrite `h2` using `[ae_restrict_iff' (measurableSet_fundamentalDomain (Gam K n)), ae_iff]`. Use `measure_mono_null (fun y hy => ?_) h2` and prove the remaining obligations. Conclude with `fun h => hy.1 (h hy.2)`. Establish `h4 : ∀ᵐ y ∂μ, (hm.toLp f) (mk (Gam K n) y) = f (mk (Gam K n) y)` using `ae_iff.2 h3`. Use `filter_upwards [h4] with y hy`.

Rewrite using `[hy, hf]`.
-/
private theorem exists_rep {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure]
    (φ : G1 K n → ℂ) (hc : Continuous φ) (hi : ∀ γ ∈ Gam K n, ∀ g, φ (γ * g) = φ g) (C : ℝ) (hC : ∀ g, ‖φ g‖ ≤ C) :
    ∃ v : L2 μ, Reps μ v φ := by
  have := isFiniteMeasure_quotientMeasure (K := K) (n := n) μ
  let f : RightCosetSpace (Gam K n) → ℂ := fun x => φ x.out
  have hf : ∀ g, f (mk (Gam K n) g) = φ g := fun g => by
    obtain ⟨γ, hγ⟩ := (mk_eq_mk_iff (Γ := Gam K n) (g := (mk (Gam K n) g).out) (h := g)).1 (Quotient.out_eq _)
    change φ _ = _
    rw [← hγ]
    exact hi γ γ.2 g
  have hfc : Continuous f := by
    rw [(isOpenQuotientMap_mk (Gam K n)).isQuotientMap.continuous_iff]
    have : f ∘ mk (Gam K n) = φ := funext hf
    rwa [this]
  have hm : MemLp f 2 (quotientMeasure (Gam K n) μ) :=
    MemLp.of_bound hfc.aestronglyMeasurable C (Eventually.of_forall fun x => hC _)
  refine ⟨hm.toLp f, ?_⟩
  have h1 := hm.coeFn_toLp
  have h2 : ∀ᵐ y ∂μ.restrict (fundamentalDomain (Gam K n)), (hm.toLp f) (mk (Gam K n) y) = f (mk (Gam K n) y) :=
    ae_of_ae_map (measurable_mk (Gam K n)).aemeasurable h1
  have hF := isFundamentalDomain_fundamentalDomain (Gam K n) μ
  have h3 : μ {y | ¬ (hm.toLp f) (mk (Gam K n) y) = f (mk (Gam K n) y)} = 0 := by
    refine hF.measure_zero_of_invariant _ (fun γ => ?_) ?_
    · ext y
      simp [Set.mem_smul_set_iff_inv_smul_mem]
    · rw [ae_restrict_iff' (measurableSet_fundamentalDomain (Gam K n)), ae_iff] at h2
      refine measure_mono_null (fun y hy => ?_) h2
      exact fun h => hy.1 (h hy.2)
  have h4 : ∀ᵐ y ∂μ, (hm.toLp f) (mk (Gam K n) y) = f (mk (Gam K n) y) := ae_iff.2 h3
  filter_upwards [h4] with y hy
  rw [hy, hf]

/- English proof (translation)
Introduce `K _ _ μ _ F hc hP hB`. Take `⟨R, hR⟩` from `hB`. Establish `hfin : ∀ C : Set (G1 K (2 + 2)), IsCompact C → {q : Cos K | ∃ g ∈ C, F ((q.out : G1 K (2 + 2)) * g) ≠ 0}.Finite` using `fun C hC => (locFin C (-R) hC).subset fun q ⟨g, hg, h⟩ => ⟨g, hg, (abs_le.1 (hR _ h)).1⟩`. Establish `hout : ∀ (γ : Gam K (2 + 2)) (g : G1 K (2 + 2)), F ((((Quotient.mk _ γ : Cos K).out : Gam K (2 + 2)) : G1 K (2 + 2)) * g) = F (γ * g)` using `fun γ g => by`. Take `⟨δ, hδ, h⟩` from `(pkLaws (K := K)).2.2.2 γ`.

Rewrite using `[h, mul_assoc, hP δ hδ]`. Establish `hcont : Continuous (th F)`. Use `continuous_finsum (fun q => hc.comp (continuous_const.mul continuous_id)) fun x => ?_` and prove the remaining obligations. Take `⟨C, hC, hx⟩` from `exists_compact_mem_nhds x`. Conclude with `⟨C, hx, (hfin C hC).subset fun q ⟨g, hg, h⟩ => ⟨g, h, hg⟩⟩`.

Establish `hinv : ∀ γ ∈ Gam K (2 + 2), ∀ g, th F (γ * g) = th F g` using `fun γ hγ g => by`. Use `finsum_eq_of_bijective _ (bij_shift (ParΓ K 2 2) ⟨γ, hγ⟩) fun q => ?_` and prove the remaining obligations. Rewrite using `[hout, Subgroup.coe_mul, mul_assoc]`. Use `⟨hfin, hcont, hinv, fun hD => ?_⟩` and prove the remaining obligations. Take `⟨N, C₀, hC₀, hs⟩` from `sumHt (K := K) (2 + 2)`.

Take `⟨C, hC⟩` from `hD N R`. Establish `hsum : ∀ g, ∑' q : Cos K, ‖F ((q.out : G1 K (2 + 2)) * g)‖ₑ ≤ ENNReal.ofReal C * C₀` using `fun g => by`. Establish `key : ∀ q : Cos K, ∃ δ : Gam K (2 + 2), (Quotient.mk _ δ : Cos K) = q ∧ ‖F ((q.out : G1 K (2 + 2)) * g)‖ₑ ≤ ENNReal.ofReal C * ENNReal.ofReal ((AutomorphicForm.height (((δ : G1 K (2 + 2)) * g : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) ^ N)⁻¹)`. Introduce `q`. Distinguish the cases in `h0 : F ((q.out : G1 K (2 + 2)) * g) = 0`.

Conclude with `⟨q.out, Quotient.out_eq q, by simp [h0]⟩`. Take `⟨_, ⟨γ, hγ, rfl⟩, hb⟩` from `hC _ (hR _ h0)`. Use `⟨γ * q.out, ?_, ?_⟩` and prove the remaining obligations. Use `Eq.trans (Quotient.sound ?_) (Quotient.out_eq q)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(QuotientGroup.rightRel (ParΓ K 2 2)) _ _`.

Rewrite using `[QuotientGroup.rightRel_apply]`. Simplify using `using hγ`. Rewrite using `[Subgroup.coe_mul (Gam K (2 + 2)), mul_assoc]`. Rewrite `hb` using `[Subgroup.subtype_apply]`. Establish `hp` using `pow_pos (height_pos (((γ : G1 K (2 + 2)) * ((q.out : G1 K (2 + 2)) * g) : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2))) N`.

Establish `hC0 : 0 ≤ C` using `le_trans (mul_nonneg (norm_nonneg _) hp.le) hb`. Rewrite using `[← ENNReal.ofReal_mul hC0, ← ofReal_norm_eq_enorm]`. Use `ENNReal.ofReal_le_ofReal ?_` and prove the remaining obligations. Rewrite using `[← div_eq_mul_inv, le_div_iff₀ hp]`. Conclude with `hb`.

Use `choose δ hδ hb using key`. Establish `hinj : Function.Injective δ` using `fun q q' h => by rw [← hδ q, h, hδ]`. Use `(ENNReal.tsum_le_tsum hb).trans ?_` and prove the remaining obligations. Rewrite using `[ENNReal.tsum_mul_left]`. Conclude with `mul_le_mul_right ((ENNReal.tsum_comp_le_tsum_of_injective hinj _).trans (hs g)) _`.

Establish `hne : ENNReal.ofReal C * C₀ ≠ ⊤` using `ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC₀`. Establish `hbd : ∀ g, ‖th F g‖ ≤ (ENNReal.ofReal C * C₀).toReal` using `fun g => by`. Establish `hf : (Function.support fun q : Cos K => F ((q.out : G1 K (2 + 2)) * g)).Finite` using `(hfin {g} isCompact_singleton).subset fun q hq => ⟨g, rfl, hq⟩`. Rewrite using `[← toReal_enorm]`. Use `ENNReal.toReal_mono hne (le_trans ?_ (hsum g))` and prove the remaining obligations.

Unfold `th`. Rewrite using `[finsum_eq_sum _ hf]`. Conclude with `(enorm_sum_le _ _).trans (ENNReal.sum_le_tsum _)`. Conclude with `⟨⟨_, hne, hsum⟩, ⟨_, hbd⟩, exists_rep μ _ hcont hinv _ hbd⟩`.
-/
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.thBasic :
    ∀ {K : Type} [Field K] [NumberField K] (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure] (F : G1 K (2 + 2) → ℂ), Continuous F → (∀ γ ∈ PK K, ∀ g, F (γ * g) = F g) → InBand F →
      (∀ C : Set (G1 K (2 + 2)), IsCompact C → {q : Cos K | ∃ g ∈ C, F ((q.out : G1 K (2 + 2)) * g) ≠ 0}.Finite) ∧ Continuous (th F) ∧
      (∀ γ ∈ Gam K (2 + 2), ∀ g, th F (γ * g) = th F g) ∧ (Decays F →
        (∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ g, ∑' q : Cos K, ‖F ((q.out : G1 K (2 + 2)) * g)‖ₑ ≤ C) ∧ (∃ C : ℝ, ∀ g, ‖th F g‖ ≤ C) ∧ ∃ v : L2 μ, Reps μ v (th F)) := by
  intro K _ _ μ _ F hc hP hB
  obtain ⟨R, hR⟩ := hB
  have hfin : ∀ C : Set (G1 K (2 + 2)), IsCompact C →
      {q : Cos K | ∃ g ∈ C, F ((q.out : G1 K (2 + 2)) * g) ≠ 0}.Finite := fun C hC =>
    (locFin C (-R) hC).subset fun q ⟨g, hg, h⟩ => ⟨g, hg, (abs_le.1 (hR _ h)).1⟩
  have hout : ∀ (γ : Gam K (2 + 2)) (g : G1 K (2 + 2)),
      F ((((Quotient.mk _ γ : Cos K).out : Gam K (2 + 2)) : G1 K (2 + 2)) * g) = F (γ * g) := fun γ g => by
    obtain ⟨δ, hδ, h⟩ := (pkLaws (K := K)).2.2.2 γ
    rw [h, mul_assoc, hP δ hδ]
  have hcont : Continuous (th F) := by
    refine continuous_finsum (fun q => hc.comp (continuous_const.mul continuous_id)) fun x => ?_
    obtain ⟨C, hC, hx⟩ := exists_compact_mem_nhds x
    exact ⟨C, hx, (hfin C hC).subset fun q ⟨g, hg, h⟩ => ⟨g, h, hg⟩⟩
  have hinv : ∀ γ ∈ Gam K (2 + 2), ∀ g, th F (γ * g) = th F g := fun γ hγ g => by
    refine finsum_eq_of_bijective _ (bij_shift (ParΓ K 2 2) ⟨γ, hγ⟩) fun q => ?_
    rw [hout, Subgroup.coe_mul, mul_assoc]
  refine ⟨hfin, hcont, hinv, fun hD => ?_⟩
  obtain ⟨N, C₀, hC₀, hs⟩ := sumHt (K := K) (2 + 2)
  obtain ⟨C, hC⟩ := hD N R
  have hsum : ∀ g, ∑' q : Cos K, ‖F ((q.out : G1 K (2 + 2)) * g)‖ₑ ≤ ENNReal.ofReal C * C₀ := fun g => by
    have key : ∀ q : Cos K, ∃ δ : Gam K (2 + 2), (Quotient.mk _ δ : Cos K) = q ∧
        ‖F ((q.out : G1 K (2 + 2)) * g)‖ₑ ≤ ENNReal.ofReal C * ENNReal.ofReal
          ((AutomorphicForm.height (((δ : G1 K (2 + 2)) * g : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) ^ N)⁻¹) := by
      intro q
      by_cases h0 : F ((q.out : G1 K (2 + 2)) * g) = 0
      · exact ⟨q.out, Quotient.out_eq q, by simp [h0]⟩
      obtain ⟨_, ⟨γ, hγ, rfl⟩, hb⟩ := hC _ (hR _ h0)
      refine ⟨γ * q.out, ?_, ?_⟩
      · refine Eq.trans (Quotient.sound ?_) (Quotient.out_eq q)
        change (QuotientGroup.rightRel (ParΓ K 2 2)) _ _
        rw [QuotientGroup.rightRel_apply]
        simpa using hγ
      · rw [Subgroup.coe_mul (Gam K (2 + 2)), mul_assoc]
        rw [Subgroup.subtype_apply] at hb
        have hp := pow_pos (height_pos (((γ : G1 K (2 + 2)) * ((q.out : G1 K (2 + 2)) * g) : G1 K (2 + 2)) :
          AdelicGLn.AdelicGL K (2 + 2))) N
        have hC0 : 0 ≤ C := le_trans (mul_nonneg (norm_nonneg _) hp.le) hb
        rw [← ENNReal.ofReal_mul hC0, ← ofReal_norm_eq_enorm]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← div_eq_mul_inv, le_div_iff₀ hp]
        exact hb
    choose δ hδ hb using key
    have hinj : Function.Injective δ := fun q q' h => by rw [← hδ q, h, hδ]
    refine (ENNReal.tsum_le_tsum hb).trans ?_
    rw [ENNReal.tsum_mul_left]
    exact mul_le_mul_right ((ENNReal.tsum_comp_le_tsum_of_injective hinj _).trans (hs g)) _
  have hne : ENNReal.ofReal C * C₀ ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC₀
  have hbd : ∀ g, ‖th F g‖ ≤ (ENNReal.ofReal C * C₀).toReal := fun g => by
    have hf : (Function.support fun q : Cos K => F ((q.out : G1 K (2 + 2)) * g)).Finite :=
      (hfin {g} isCompact_singleton).subset fun q hq => ⟨g, rfl, hq⟩
    rw [← toReal_enorm]
    refine ENNReal.toReal_mono hne (le_trans ?_ (hsum g))
    unfold th
    rw [finsum_eq_sum _ hf]
    exact (enorm_sum_le _ _).trans (ENNReal.sum_le_tsum _)
  exact ⟨⟨_, hne, hsum⟩, ⟨_, hbd⟩, exists_rep μ _ hcont hinv _ hbd⟩
