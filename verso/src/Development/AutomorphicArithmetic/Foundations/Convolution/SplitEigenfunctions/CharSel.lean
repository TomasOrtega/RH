import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.SplitEig
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.UILaws
import GroundTheory.AutomorphicForms.CompactAbelianCharacters
import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Action
import GroundTheory.GlobalFields.TateThesis.IdeleMeasureQuotient
import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.EllipticTorusNorm
import Development.AutomorphicArithmetic.AdelicQuotients.CentralSectionBaseChange

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.V.Z.Bc
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.RankTwoDescent

section Abs
open GroundTheory.Automorphic.CompactAbelianFourier
open scoped Pointwise

variable {G : Type} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

/- English proof (translation)
The claim follows from `(hf.continuousOn.integrableOn_compact hc).mono_set subset_closure`.
-/
private lemma intF (μ : Measure G) [μ.IsHaarMeasure] {F : Set G} (hc : IsCompact (closure F)) {f : G → ℂ}
    (hf : Continuous f) : IntegrableOn f F μ :=
  (hf.continuousOn.integrableOn_compact hc).mono_set subset_closure

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Use `haveI hcl : IsClosed (N : Set G) := Subgroup.isClosed_of_discrete`. Use `haveI : CompactSpace (G ⧸ N) := ⟨by`. Establish `: (Set.univ : Set (G ⧸ N)) = QuotientGroup.mk '' closure F`.

Use `symm`. Use `Set.eq_univ_of_forall fun q => ?_` and prove the remaining obligations. Take `⟨u, rfl⟩` from `QuotientGroup.mk_surjective q`. Take `⟨k, hk, hu⟩` from `hs u`. Conclude with `⟨u * k, subset_closure hu, QuotientGroup.mk_mul_of_mem u hk⟩`.

Rewrite using `[this]`. Conclude with `hc.image QuotientGroup.continuous_mk⟩`. Set `π : G →ₜ* G ⧸ N` to `⟨QuotientGroup.mk' N, continuous_quotient_mk'⟩`. Establish `hπc : Continuous fun x => π x` using `π.continuous`. Take `⟨M₀, hM₀⟩` from `hc.exists_bound_of_continuousOn hb.continuousOn`.

Take `⟨M, hM⟩ : ∃ M : ℝ, ∀ x ∈ closure F, ‖b x‖ ≤ M` from `⟨M₀, hM₀⟩`. Establish `hfin : μ F < ⊤` using `(measure_mono subset_closure).trans_lt hc.measure_lt_top`. Establish `hint : ∀ f : C(G ⧸ N, ℂ), IntegrableOn (fun x => f (π x) * b x) F μ` using `fun f => intF μ hc ((f.continuous.comp hπc).mul hb)`. Set `L0 : C(G ⧸ N, ℂ) →ₗ[ℂ] ℂ` to `{ toFun := fun f => ∫ x in F, f (π x) * b x ∂μ map_add' := fun f g => by`. Simplify using `only [ContinuousMap.add_apply, add_mul]`.

Conclude with `integral_add (hint f) (hint g)`. Use the proof step `map_smul' := fun c f => by`. Simplify using `only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]`. Conclude with `integral_const_mul _ _ }`. Establish `hbd : ∀ f, ‖L0 f‖ ≤ (M * μ.real F) * ‖f‖`.

Introduce `f`. Use `norm_setIntegral_le_of_norm_le_const (μ := μ) (s := F) (f := fun x => f (π x) * b x) (C := ‖f‖ * M) hfin (fun x hx => by` as an intermediate fact. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul (f.norm_coe_le_norm _) (hM x (subset_closure hx)) (norm_nonneg _) (norm_nonneg _))`. Combine the equalities or inequalities in the displayed calculation.

Set `L : C(G ⧸ N, ℂ) →L[ℂ] ℂ` to `L0.mkContinuous _ hbd`. Establish `hL : ∀ f, L f = ∫ x in F, f (π x) * b x ∂μ` using `fun f => rfl`. Establish `hspan : (Submodule.span ℂ (Set.range (charCM (C` using `G ⧸ N)))).topologicalClosure ≤ LinearMap.ker (L : C(G ⧸ N, ℂ) →ₗ[ℂ] ℂ) := by`. Use `Submodule.topologicalClosure_minimal _ ?_ (ContinuousLinearMap.isClosed_ker L)` and prove the remaining obligations. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨ψ, rfl⟩`. Use `hcon (ψ.comp π) (fun k hk => by` as an intermediate fact. Express the relevant statement in the definitionally equal form `ψ (QuotientGroup.mk k) = 1`. Rewrite using `[(QuotientGroup.eq_one_iff k).2 hk, map_one])`. Conclude with `this`.

Establish `hall : ∀ f, L f = 0` using `fun f => hspan (by rw [span_charCM_dense]; trivial)`. Set `bq : C(G ⧸ N, ℂ)` to `⟨fun q => Quotient.liftOn' q b (fun x y h => by`. Establish `h' : x⁻¹ * y ∈ N` using `QuotientGroup.leftRel_apply.1 h`. Use `hi _ h' x` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel_left]`.

Conclude with `this.symm), hb.quotient_liftOn' _⟩`. Establish `hbq : ∀ x, bq (π x) = b x` using `fun x => rfl`. Establish `h1` using `hall (star bq)`. Rewrite `h1` using `[hL]`. Establish `h2 : ∫ x in F, ((‖b x‖ ^ 2 : ℝ) : ℂ) ∂μ = 0`.

Rewrite using `[← h1]`. Use `integral_congr_ae (ae_of_all _ fun x => ?_)` and prove the remaining obligations. Simplify using `only [ContinuousMap.star_apply, hbq]`. Rewrite using `[RCLike.star_def, Complex.conj_mul']`. Simplify using the standard rewrite rules.

Establish `h3 : ∫ x in F, ‖b x‖ ^ 2 ∂μ = 0`. Establish `h` using `integral_ofReal (μ := μ.restrict F) (𝕜 := ℂ) (f := fun x => ‖b x‖ ^ 2)`. Establish `h' : ((∫ x in F, ‖b x‖ ^ 2 ∂μ : ℝ) : ℂ) = 0`. Rewrite using `[← h2]`. Conclude with `h.symm`.

Conclude with `h'` after adjusting the coercions. Establish `hc2 : Continuous fun x => ‖b x‖ ^ 2` using `by fun_prop`. Establish `h4` using `(setIntegral_eq_zero_iff_of_nonneg_ae (ae_of_all _ fun x => by positivity) (by`. Conclude with `(hc2.continuousOn.integrableOn_compact hc).mono_set subset_closure)).1 h3`. Establish `hT : IsOpen {x | b x ≠ 0}` using `isOpen_ne_fun hb continuous_const`.

Establish `hTF : μ ({x | b x ≠ 0} ∩ F) = 0`. Rewrite using `[← Measure.restrict_apply hT.measurableSet]`. Use `measure_mono_null ?_ (ae_iff.1 h4)` and prove the remaining obligations. Introduce `x hx`. Simplify using `only [Set.mem_setOf_eq, Pi.zero_apply] at hx ⊢`.

Simplify using `using hx`. Establish `hinv : ∀ g : N.op, g • {x | b x ≠ 0} = {x | b x ≠ 0}`. Introduce and unpack `⟨g, hg⟩`. Use extensionality with `x`. Rewrite using `[Set.mem_smul_set_iff_inv_smul_mem]`.

Establish `hg' : g.unop ∈ N` using `Subgroup.mem_op.1 hg`. Establish `: ((⟨g, hg⟩ : N.op)⁻¹ • x) = x * g.unop⁻¹` using `rfl`. Simplify using `only [Set.mem_setOf_eq, this]`. Rewrite using `[hi _ (N.inv_mem hg')]`. Establish `hz` using `hF.measure_zero_of_invariant _ hinv hTF`.

Conclude with `(hT.measure_pos μ ⟨x₀, h0⟩).ne' hz`.
-/
private theorem char_integral_ne (μ : Measure G) [μ.IsHaarMeasure] (N : Subgroup G) [Countable N] [DiscreteTopology N]
    (F : Set G) (hF : IsFundamentalDomain N.op F μ) (hc : IsCompact (closure F))
    (hs : ∀ u : G, ∃ k ∈ N, u * k ∈ F)
    (b : G → ℂ) (hb : Continuous b) (hi : ∀ k ∈ N, ∀ x, b (x * k) = b x) (x₀ : G) (h0 : b x₀ ≠ 0) :
    ∃ χ : G →ₜ* Circle, (∀ k ∈ N, χ k = 1) ∧ ∫ x in F, (χ x : ℂ) * b x ∂μ ≠ 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  haveI hcl : IsClosed (N : Set G) := Subgroup.isClosed_of_discrete
  haveI : CompactSpace (G ⧸ N) := ⟨by
    have : (Set.univ : Set (G ⧸ N)) = QuotientGroup.mk '' closure F := by
      symm
      refine Set.eq_univ_of_forall fun q => ?_
      obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨k, hk, hu⟩ := hs u
      exact ⟨u * k, subset_closure hu, QuotientGroup.mk_mul_of_mem u hk⟩
    rw [this]
    exact hc.image QuotientGroup.continuous_mk⟩
  let π : G →ₜ* G ⧸ N := ⟨QuotientGroup.mk' N, continuous_quotient_mk'⟩
  have hπc : Continuous fun x => π x := π.continuous
  obtain ⟨M₀, hM₀⟩ := hc.exists_bound_of_continuousOn hb.continuousOn
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ x ∈ closure F, ‖b x‖ ≤ M := ⟨M₀, hM₀⟩
  have hfin : μ F < ⊤ := (measure_mono subset_closure).trans_lt hc.measure_lt_top
  have hint : ∀ f : C(G ⧸ N, ℂ), IntegrableOn (fun x => f (π x) * b x) F μ := fun f =>
    intF μ hc ((f.continuous.comp hπc).mul hb)
  let L0 : C(G ⧸ N, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∫ x in F, f (π x) * b x ∂μ
      map_add' := fun f g => by
        simp only [ContinuousMap.add_apply, add_mul]
        exact integral_add (hint f) (hint g)
      map_smul' := fun c f => by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
        exact integral_const_mul _ _ }
  have hbd : ∀ f, ‖L0 f‖ ≤ (M * μ.real F) * ‖f‖ := by
    intro f
    have := norm_setIntegral_le_of_norm_le_const (μ := μ) (s := F) (f := fun x => f (π x) * b x) (C := ‖f‖ * M) hfin
      (fun x hx => by
        rw [norm_mul]
        exact mul_le_mul (f.norm_coe_le_norm _) (hM x (subset_closure hx)) (norm_nonneg _) (norm_nonneg _))
    calc ‖L0 f‖ ≤ ‖f‖ * M * μ.real F := this
      _ = _ := by ring
  let L : C(G ⧸ N, ℂ) →L[ℂ] ℂ := L0.mkContinuous _ hbd
  have hL : ∀ f, L f = ∫ x in F, f (π x) * b x ∂μ := fun f => rfl
  have hspan : (Submodule.span ℂ (Set.range (charCM (C := G ⧸ N)))).topologicalClosure ≤ LinearMap.ker (L : C(G ⧸ N, ℂ) →ₗ[ℂ] ℂ) := by
    refine Submodule.topologicalClosure_minimal _ ?_ (ContinuousLinearMap.isClosed_ker L)
    rw [Submodule.span_le]
    rintro _ ⟨ψ, rfl⟩
    have := hcon (ψ.comp π) (fun k hk => by
      change ψ (QuotientGroup.mk k) = 1
      rw [(QuotientGroup.eq_one_iff k).2 hk, map_one])
    exact this
  have hall : ∀ f, L f = 0 := fun f => hspan (by rw [span_charCM_dense]; trivial)
  let bq : C(G ⧸ N, ℂ) := ⟨fun q => Quotient.liftOn' q b (fun x y h => by
      have h' : x⁻¹ * y ∈ N := QuotientGroup.leftRel_apply.1 h
      have := hi _ h' x
      rw [mul_inv_cancel_left] at this
      exact this.symm), hb.quotient_liftOn' _⟩
  have hbq : ∀ x, bq (π x) = b x := fun x => rfl
  have h1 := hall (star bq)
  rw [hL] at h1
  have h2 : ∫ x in F, ((‖b x‖ ^ 2 : ℝ) : ℂ) ∂μ = 0 := by
    rw [← h1]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [ContinuousMap.star_apply, hbq]
    rw [RCLike.star_def, Complex.conj_mul']
    simp
  have h3 : ∫ x in F, ‖b x‖ ^ 2 ∂μ = 0 := by
    have h := integral_ofReal (μ := μ.restrict F) (𝕜 := ℂ) (f := fun x => ‖b x‖ ^ 2)
    have h' : ((∫ x in F, ‖b x‖ ^ 2 ∂μ : ℝ) : ℂ) = 0 := by
      rw [← h2]
      exact h.symm
    exact_mod_cast h'
  have hc2 : Continuous fun x => ‖b x‖ ^ 2 := by fun_prop
  have h4 := (setIntegral_eq_zero_iff_of_nonneg_ae (ae_of_all _ fun x => by positivity) (by
    exact (hc2.continuousOn.integrableOn_compact hc).mono_set subset_closure)).1 h3
  have hT : IsOpen {x | b x ≠ 0} := isOpen_ne_fun hb continuous_const
  have hTF : μ ({x | b x ≠ 0} ∩ F) = 0 := by
    rw [← Measure.restrict_apply hT.measurableSet]
    refine measure_mono_null ?_ (ae_iff.1 h4)
    intro x hx
    simp only [Set.mem_setOf_eq, Pi.zero_apply] at hx ⊢
    simpa using hx
  have hinv : ∀ g : N.op, g • {x | b x ≠ 0} = {x | b x ≠ 0} := by
    rintro ⟨g, hg⟩
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    have hg' : g.unop ∈ N := Subgroup.mem_op.1 hg
    have : ((⟨g, hg⟩ : N.op)⁻¹ • x) = x * g.unop⁻¹ := rfl
    simp only [Set.mem_setOf_eq, this]
    rw [hi _ (N.inv_mem hg')]
  have hz := hF.measure_zero_of_invariant _ hinv hTF
  exact (hT.measure_pos μ ⟨x₀, h0⟩).ne' hz

/- English proof (translation)
Establish `hD'` using `hF.smul_of_comm d`. Establish `hI : ∀ (γ : N.op) (x : G), f (γ • x) = f x`. Introduce and unpack `⟨γ, hγ⟩ x`. Conclude with `hi _ (Subgroup.mem_op.1 hγ) x`. Establish `h1` using `hF.setIntegral_eq hD' hI`.

Establish `h2` using `(measurePreserving_mul_left μ d).setIntegral_image_emb (MeasurableEquiv.mulLeft d).measurableEmbedding f F`. Rewrite using `[h1]`. Repeatedly rewrite using `[mul_comm _ d]`. Conclude with `h2.symm`.
-/
private lemma transl (μ : Measure G) [μ.IsHaarMeasure] (N : Subgroup G) [Countable N]
    (F : Set G) (hF : IsFundamentalDomain N.op F μ) (f : G → ℂ) (hi : ∀ k ∈ N, ∀ x, f (x * k) = f x) (d : G) :
    ∫ t in F, f (t * d) ∂μ = ∫ t in F, f t ∂μ := by
  have hD' := hF.smul_of_comm d
  have hI : ∀ (γ : N.op) (x : G), f (γ • x) = f x := by
    rintro ⟨γ, hγ⟩ x
    exact hi _ (Subgroup.mem_op.1 hγ) x
  have h1 := hF.setIntegral_eq hD' hI
  have h2 := (measurePreserving_mul_left μ d).setIntegral_image_emb
    (MeasurableEquiv.mulLeft d).measurableEmbedding f F
  rw [h1]
  simp_rw [mul_comm _ d]
  exact h2.symm

end Abs

section AbsB
variable {G : Type} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G]

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨B, hB⟩ : ∃ B : ℝ, ∀ x, ‖β x‖ ≤ B := by`. Take `⟨B, hB⟩` from `hc.exists_bound_of_continuousOn hβ.continuousOn`. Use `⟨B, fun x => ?_⟩` and prove the remaining obligations. Take `⟨k, hk, hx⟩` from `hs x`. Use `hB _ (subset_closure hx)` as an intermediate fact.

Rewrite `this` using `[hβi k hk]`. Then use the resulting hypothesis. Establish `hfin : μ F < ⊤` using `(measure_mono subset_closure).trans_lt hc.measure_lt_top`. Use `haveI : IsFiniteMeasure (μ.restrict F) := ⟨by simpa using hfin⟩`. Set `b : G → ℂ` to `fun t => ∫ z in F, β (t * c z) ∂μ`. Establish `hbc : Continuous b`.

Use `continuous_of_dominated (bound := fun _ => B) (fun t => ?_) (fun t => ae_of_all _ fun z => hB _) (integrable_const _) (ae_of_all _ fun z => ?_)` and prove the remaining obligations. Conclude with `(hβ.comp (continuous_const.mul hcc)).aestronglyMeasurable`. Conclude with `hβ.comp (continuous_id.mul continuous_const)`. Establish `hbN : ∀ k ∈ N, ∀ x, b (x * k) = b x`. Introduce `k hk x`.

Use `integral_congr_ae (ae_of_all _ fun z => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `β (x * k * c z) = β (x * c z)`. Rewrite using `[mul_right_comm, hβi k hk]`. Establish `hbw : ∀ w t, b (t * c w) = b t`. Introduce `w t`.

Establish `h1` using `transl μ N F hF (fun z => β (t * c z)) (fun k hk x => by`. Simplify using `only [map_mul]`. Rewrite using `[← mul_assoc, hβi _ (hcN k hk)]) w`. Use `Eq.trans (integral_congr_ae (ae_of_all _ fun z => ?_)) h1` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `β (t * c w * c z) = β (t * c (z * w))`.

Rewrite using `[map_mul, mul_assoc, mul_comm (c w)]`. Establish `hb1 : b 1 ≠ 0` using `by simpa [b] using h`. Take `⟨χ, hχN, hχ⟩` from `char_integral_ne μ N F hF hc hs b hbc hbN 1 hb1`. Establish `hχc : Continuous fun x => (χ x : ℂ)` using `continuous_subtype_val.comp χ.continuous`. Establish `hχw : ∀ z, χ (c z) = 1`.

Introduce `w`. Establish `h1` using `transl μ N F hF (fun t => (χ t : ℂ) * b t) (fun k hk x => by`. Simplify using `only [map_mul, hχN k hk, mul_one]`. Rewrite using `[hbN k hk]) (c w)`. Establish `h2 : ∫ t in F, (χ (t * c w) : ℂ) * b (t * c w) ∂μ = (χ (c w) : ℂ) * ∫ t in F, (χ t : ℂ) * b t ∂μ`.

Rewrite using `[← integral_const_mul]`. Use `integral_congr_ae (ae_of_all _ fun t => ?_)` and prove the remaining obligations. Simplify using `only [hbw, map_mul, Circle.coe_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h1` using `[h2]`.

Establish `h3 : (χ (c w) : ℂ) = 1` using `mul_right_cancel₀ hχ (h1.trans (one_mul _).symm)`. Conclude with `Circle.coe_injective (by simpa using h3)`. Use `⟨χ, hχN, hχw, ?_⟩` and prove the remaining obligations. Establish `hint : Integrable (Function.uncurry fun t z => (χ t : ℂ) * β (t * c z)) ((μ.restrict F).prod (μ.restrict F))`. Use `Integrable.of_bound (Continuous.aestronglyMeasurable ?_) B (ae_of_all _ fun p => ?_)` and prove the remaining obligations.

Conclude with `(hχc.comp continuous_fst).mul (hβ.comp (continuous_fst.mul (hcc.comp continuous_snd)))`. Simplify using `only [Function.uncurry, norm_mul, Circle.norm_coe, one_mul]`. Conclude with `hB _`. Establish `e1 : ∫ t in F, (χ t : ℂ) * b t ∂μ = ∫ t in F, ∫ z in F, (χ t : ℂ) * β (t * c z) ∂μ ∂μ`. Use `integral_congr_ae (ae_of_all _ fun t => ?_)` and prove the remaining obligations.

Conclude with `(integral_const_mul _ _).symm`. Establish `e3 : ∀ z, ∫ t in F, (χ t : ℂ) * β (t * c z) ∂μ = ∫ t in F, (χ t : ℂ) * β t ∂μ`. Introduce `z`. Establish `h1` using `transl μ N F hF (fun t => (χ t : ℂ) * β t) (fun k hk x => by`. Simplify using `only [map_mul, hχN k hk, mul_one]`.

Rewrite using `[hβi k hk]) (c z)`. Use `Eq.trans (integral_congr_ae (ae_of_all _ fun t => ?_)) h1` and prove the remaining obligations. Simplify using `only [map_mul, hχw, mul_one]`. Introduce `hJ`. Apply `hχ` to reduce the goal to its premises.

Rewrite using `[e1, integral_integral_swap hint]`. Repeatedly rewrite using `[e3, hJ]`. Simplify using the standard rewrite rules.
-/
private theorem char_sel (μ : Measure G) [μ.IsHaarMeasure] (N : Subgroup G) [Countable N] [DiscreteTopology N]
    (F : Set G) (hF : IsFundamentalDomain N.op F μ) (hc : IsCompact (closure F))
    (hs : ∀ u : G, ∃ k ∈ N, u * k ∈ F)
    (c : G →* G) (hcc : Continuous c) (hcN : ∀ k ∈ N, c k ∈ N)
    (β : G → ℂ) (hβ : Continuous β) (hβi : ∀ k ∈ N, ∀ x, β (x * k) = β x)
    (h : ∫ z in F, β (c z) ∂μ ≠ 0) :
    ∃ χ : G →ₜ* Circle, (∀ k ∈ N, χ k = 1) ∧ (∀ z, χ (c z) = 1) ∧ ∫ t in F, (χ t : ℂ) * β t ∂μ ≠ 0 := by
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ x, ‖β x‖ ≤ B := by
    obtain ⟨B, hB⟩ := hc.exists_bound_of_continuousOn hβ.continuousOn
    refine ⟨B, fun x => ?_⟩
    obtain ⟨k, hk, hx⟩ := hs x
    have := hB _ (subset_closure hx)
    rwa [hβi k hk] at this
  have hfin : μ F < ⊤ := (measure_mono subset_closure).trans_lt hc.measure_lt_top
  haveI : IsFiniteMeasure (μ.restrict F) := ⟨by simpa using hfin⟩
  let b : G → ℂ := fun t => ∫ z in F, β (t * c z) ∂μ
  have hbc : Continuous b := by
    refine continuous_of_dominated (bound := fun _ => B) (fun t => ?_)
      (fun t => ae_of_all _ fun z => hB _) (integrable_const _) (ae_of_all _ fun z => ?_)
    · exact (hβ.comp (continuous_const.mul hcc)).aestronglyMeasurable
    · exact hβ.comp (continuous_id.mul continuous_const)
  have hbN : ∀ k ∈ N, ∀ x, b (x * k) = b x := by
    intro k hk x
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    change β (x * k * c z) = β (x * c z)
    rw [mul_right_comm, hβi k hk]
  have hbw : ∀ w t, b (t * c w) = b t := by
    intro w t
    have h1 := transl μ N F hF (fun z => β (t * c z)) (fun k hk x => by
      simp only [map_mul]
      rw [← mul_assoc, hβi _ (hcN k hk)]) w
    refine Eq.trans (integral_congr_ae (ae_of_all _ fun z => ?_)) h1
    change β (t * c w * c z) = β (t * c (z * w))
    rw [map_mul, mul_assoc, mul_comm (c w)]
  have hb1 : b 1 ≠ 0 := by simpa [b] using h
  obtain ⟨χ, hχN, hχ⟩ := char_integral_ne μ N F hF hc hs b hbc hbN 1 hb1
  have hχc : Continuous fun x => (χ x : ℂ) := continuous_subtype_val.comp χ.continuous
  have hχw : ∀ z, χ (c z) = 1 := by
    intro w
    have h1 := transl μ N F hF (fun t => (χ t : ℂ) * b t) (fun k hk x => by
      simp only [map_mul, hχN k hk, mul_one]
      rw [hbN k hk]) (c w)
    have h2 : ∫ t in F, (χ (t * c w) : ℂ) * b (t * c w) ∂μ = (χ (c w) : ℂ) * ∫ t in F, (χ t : ℂ) * b t ∂μ := by
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun t => ?_)
      simp only [hbw, map_mul, Circle.coe_mul]
      ring
    rw [h2] at h1
    have h3 : (χ (c w) : ℂ) = 1 := mul_right_cancel₀ hχ (h1.trans (one_mul _).symm)
    exact Circle.coe_injective (by simpa using h3)
  refine ⟨χ, hχN, hχw, ?_⟩
  have hint : Integrable (Function.uncurry fun t z => (χ t : ℂ) * β (t * c z))
      ((μ.restrict F).prod (μ.restrict F)) := by
    refine Integrable.of_bound (Continuous.aestronglyMeasurable ?_) B (ae_of_all _ fun p => ?_)
    · exact (hχc.comp continuous_fst).mul (hβ.comp (continuous_fst.mul (hcc.comp continuous_snd)))
    · simp only [Function.uncurry, norm_mul, Circle.norm_coe, one_mul]
      exact hB _
  have e1 : ∫ t in F, (χ t : ℂ) * b t ∂μ = ∫ t in F, ∫ z in F, (χ t : ℂ) * β (t * c z) ∂μ ∂μ := by
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    exact (integral_const_mul _ _).symm
  have e3 : ∀ z, ∫ t in F, (χ t : ℂ) * β (t * c z) ∂μ = ∫ t in F, (χ t : ℂ) * β t ∂μ := by
    intro z
    have h1 := transl μ N F hF (fun t => (χ t : ℂ) * β t) (fun k hk x => by
      simp only [map_mul, hχN k hk, mul_one]
      rw [hβi k hk]) (c z)
    refine Eq.trans (integral_congr_ae (ae_of_all _ fun t => ?_)) h1
    simp only [map_mul, hχw, mul_one]
  intro hJ
  apply hχ
  rw [e1, integral_integral_swap hint]
  simp_rw [e3, hJ]
  simp

end AbsB

section Conc
open GroundTheory.Automorphic.Reduction GroundTheory.Automorphic GroundTheory.Global.AdeleBaseChange

variable (E : Type) [Field E] [NumberField E]

private noncomputable def rho : {r : ℝ // 0 < r} →* IdeleGroup E :=
  (posIdeleHom E).comp (rpowHom ((Module.finrank ℚ E : ℝ))⁻¹)

/- English proof (translation)
The claim follows from `continuous_posIdeleHom.comp (continuous_rpowHom _)`.
-/
private lemma continuous_rho : Continuous (rho E) :=
  continuous_posIdeleHom.comp (continuous_rpowHom _)

/- English proof (translation)
Use `Subtype.ext ?_` and prove the remaining obligations. Establish `hd : (Module.finrank ℚ E : ℝ) ≠ 0` using `Nat.cast_ne_zero.2 Module.finrank_pos.ne'`. Establish `h` using `ideleModule_posIdele (K := E) (rpowHom ((Module.finrank ℚ E : ℝ))⁻¹ r).1 (rpowHom ((Module.finrank ℚ E : ℝ))⁻¹ r).2`. Use `h.trans ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(r.1 ^ ((Module.finrank ℚ E : ℝ))⁻¹) ^ Module.finrank ℚ E = r.1`.

Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul r.2.le, inv_mul_cancel₀ hd, Real.rpow_one]`.
-/
private lemma module_rho (r : {r : ℝ // 0 < r}) : IdeleGroup.ideleModule E (rho E r) = r := by
  refine Subtype.ext ?_
  have hd : (Module.finrank ℚ E : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have h := ideleModule_posIdele (K := E) (rpowHom ((Module.finrank ℚ E : ℝ))⁻¹ r).1
    (rpowHom ((Module.finrank ℚ E : ℝ))⁻¹ r).2
  refine h.trans ?_
  change (r.1 ^ ((Module.finrank ℚ E : ℝ))⁻¹) ^ Module.finrank ℚ E = r.1
  rw [← Real.rpow_natCast, ← Real.rpow_mul r.2.le, inv_mul_cancel₀ hd, Real.rpow_one]

/- English proof (translation)
Both sides reduce to the same expression.
-/
private lemma rho_rpow (s : {r : ℝ // 0 < r}) : rho E s = posIdeleHom E (rpowHom ((Module.finrank ℚ E : ℝ))⁻¹ s) := rfl

private noncomputable def proj : IdeleGroup E →* IdeleGroup.normOneSubgroup E where
  toFun x := ⟨x * (rho E (IdeleGroup.ideleModule E x))⁻¹, by
    refine MonoidHom.mem_ker.2 ?_
    rw [map_mul, map_inv, module_rho, mul_inv_cancel]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by
    simp only [map_mul, Subgroup.coe_mul, mul_inv]
    exact mul_mul_mul_comm _ _ _ _)

/- English proof (translation)
The claim follows from `(continuous_id.mul ((continuous_rho E).comp IdeleGroup.continuous_ideleModule).inv).subtype_mk _`.
-/
private lemma continuous_proj : Continuous (proj E) :=
  (continuous_id.mul ((continuous_rho E).comp IdeleGroup.continuous_ideleModule).inv).subtype_mk _

/- English proof (translation)
Use `Subtype.ext ?_` and prove the remaining obligations. Establish `hz : IdeleGroup.ideleModule E (z : IdeleGroup E) = 1` using `z.2`. Express the relevant statement in the definitionally equal form `(z : IdeleGroup E) * (rho E (IdeleGroup.ideleModule E z))⁻¹ = z`. Rewrite using `[hz, map_one, inv_one, mul_one]`.
-/
private lemma proj_coe (z : IdeleGroup.normOneSubgroup E) : proj E (z : IdeleGroup E) = z := by
  refine Subtype.ext ?_
  have hz : IdeleGroup.ideleModule E (z : IdeleGroup E) = 1 := z.2
  change (z : IdeleGroup E) * (rho E (IdeleGroup.ideleModule E z))⁻¹ = z
  rw [hz, map_one, inv_one, mul_one]

/- English proof (translation)
Set `f : IdeleGroup E →* ℂˣ` to `Circle.toUnits.comp ((χ₁ : _ →* Circle).comp (proj E))`. Establish `hfv : ∀ x, ((f x : ℂˣ) : ℂ) = (χ₁ (proj E x) : ℂ)` using `fun x => rfl`. Establish `hc : Continuous f`. Use `Units.continuous_iff.2 ⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `continuous_subtype_val.comp (χ₁.continuous.comp (continuous_proj E))`.

Establish `h1 : Continuous fun x => (((χ₁ (proj E x))⁻¹ : Circle) : ℂ)` using `continuous_subtype_val.comp (χ₁.continuous.comp (continuous_proj E)).inv`. Conclude with `h1`. Establish `hd : ∀ k : Eˣ, f (IdeleGroup.diagonal E k) = 1`. Introduce `k`. Establish `e : proj E (IdeleGroup.diagonal E k) = diagonalToNormOne E k` using `proj_coe E (diagonalToNormOne E k)`.

Use `Units.ext ?_` and prove the remaining obligations. Rewrite using `[hfv, e, h]`. Simplify using the standard rewrite rules. Use `⟨⟨f, hc, hd⟩, fun z => ?_, hfv⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((f (z : IdeleGroup E) : ℂˣ) : ℂ) = _`.

Rewrite using `[hfv, proj_coe]`.
-/
private theorem ext_char (χ₁ : IdeleGroup.normOneSubgroup E →ₜ* Circle)
    (h : ∀ k : Eˣ, χ₁ (diagonalToNormOne E k) = 1) :
    ∃ χ : HChar E, (∀ z : IdeleGroup.normOneSubgroup E, ((χ.1 (z : IdeleGroup E) : ℂˣ) : ℂ) = (χ₁ z : ℂ)) ∧
      (∀ x, ((χ.1 x : ℂˣ) : ℂ) = (χ₁ (proj E x) : ℂ)) := by
  let f : IdeleGroup E →* ℂˣ := Circle.toUnits.comp ((χ₁ : _ →* Circle).comp (proj E))
  have hfv : ∀ x, ((f x : ℂˣ) : ℂ) = (χ₁ (proj E x) : ℂ) := fun x => rfl
  have hc : Continuous f := by
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · exact continuous_subtype_val.comp (χ₁.continuous.comp (continuous_proj E))
    · have h1 : Continuous fun x => (((χ₁ (proj E x))⁻¹ : Circle) : ℂ) :=
        continuous_subtype_val.comp (χ₁.continuous.comp (continuous_proj E)).inv
      exact h1
  have hd : ∀ k : Eˣ, f (IdeleGroup.diagonal E k) = 1 := by
    intro k
    have e : proj E (IdeleGroup.diagonal E k) = diagonalToNormOne E k := proj_coe E (diagonalToNormOne E k)
    refine Units.ext ?_
    rw [hfv, e, h]
    simp
  refine ⟨⟨f, hc, hd⟩, fun z => ?_, hfv⟩
  change ((f (z : IdeleGroup E) : ℂˣ) : ℂ) = _
  rw [hfv, proj_coe]

/- English proof (translation)
Use `Subtype.ext ?_` and prove the remaining obligations. Establish `hd : (Module.finrank ℚ E : ℝ) ≠ 0` using `Nat.cast_ne_zero.2 Module.finrank_pos.ne'`. Express the relevant statement in the definitionally equal form `((t ^ Module.finrank ℚ E : {r : ℝ // 0 < r}) : ℝ) ^ ((Module.finrank ℚ E : ℝ))⁻¹ = t.1`. Rewrite using `[Positive.val_pow, ← Real.rpow_natCast, ← Real.rpow_mul t.2.le, mul_inv_cancel₀ hd, Real.rpow_one]`.
-/
private lemma rpow_pow (t : {r : ℝ // 0 < r}) :
    rpowHom ((Module.finrank ℚ E : ℝ))⁻¹ (t ^ Module.finrank ℚ E) = t := by
  refine Subtype.ext ?_
  have hd : (Module.finrank ℚ E : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  change ((t ^ Module.finrank ℚ E : {r : ℝ // 0 < r}) : ℝ) ^ ((Module.finrank ℚ E : ℝ))⁻¹ = t.1
  rw [Positive.val_pow, ← Real.rpow_natCast, ← Real.rpow_mul t.2.le, mul_inv_cancel₀ hd, Real.rpow_one]

/- English proof (translation)
Rewrite using `[rho_rpow, rpow_pow]`.
-/
private lemma pos_rho (t : {r : ℝ // 0 < r}) : posIdeleHom E t = rho E (t ^ Module.finrank ℚ E) := by
  rw [rho_rpow, rpow_pow]

/- English proof (translation)
Use `Subtype.ext ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `rho E r * (rho E (IdeleGroup.ideleModule E (rho E r)))⁻¹ = 1`. Rewrite using `[module_rho, mul_inv_cancel]`.
-/
private lemma proj_rho (r : {r : ℝ // 0 < r}) : proj E (rho E r) = 1 := by
  refine Subtype.ext ?_
  change rho E r * (rho E (IdeleGroup.ideleModule E (rho E r)))⁻¹ = 1
  rw [module_rho, mul_inv_cancel]

/- English proof (translation)
Establish `h` using `UpperTheory.centralSection_baseChange ℚ E 1 t`. Establish `e : rpowHom (((1 : ℕ) * Module.finrank ℚ E : ℝ))⁻¹ (t ^ Module.finrank ℚ E) = t`. Rewrite using `[Nat.cast_one, one_mul]`. Conclude with `rpow_pow E t`. Establish `h2 : centralSection E 1 (t ^ Module.finrank ℚ E) = diagUnits 1 fun _ => posIdeleHom E t`.

Rewrite using `[centralSection, MonoidHom.comp_apply, MonoidHom.comp_apply, e, scalarUnits_apply]`. Rewrite `h` using `[h2]`. Establish `h3` using `congrArg (fun g : AdelicGLn.AdelicGL E 1 => g.val 0 0) h`. Use `beta_reduce at h3`. Rewrite `h3` using `[coe_diagUnits, Matrix.diagonal_apply_eq]`.

Establish `h4 : adeleMap ℚ E ((centralSection ℚ 1 t).val 0 0) = ((posIdeleHom E t : IdeleGroup E) : A E)` using `h3`. Use `Units.ext ?_` and prove the remaining obligations. Rewrite using `[coe_smul_idele, ← h4, smul_adeleMap]`.
-/
private lemma gal_fix_pos (σ : E ≃ₐ[ℚ] E) (t : {r : ℝ // 0 < r}) : σ • posIdeleHom E t = posIdeleHom E t := by
  have h := UpperTheory.centralSection_baseChange ℚ E 1 t
  have e : rpowHom (((1 : ℕ) * Module.finrank ℚ E : ℝ))⁻¹ (t ^ Module.finrank ℚ E) = t := by
    rw [Nat.cast_one, one_mul]
    exact rpow_pow E t
  have h2 : centralSection E 1 (t ^ Module.finrank ℚ E) = diagUnits 1 fun _ => posIdeleHom E t := by
    rw [centralSection, MonoidHom.comp_apply, MonoidHom.comp_apply, e, scalarUnits_apply]
  rw [h2] at h
  have h3 := congrArg (fun g : AdelicGLn.AdelicGL E 1 => g.val 0 0) h
  beta_reduce at h3
  rw [coe_diagUnits, Matrix.diagonal_apply_eq] at h3
  have h4 : adeleMap ℚ E ((centralSection ℚ 1 t).val 0 0) = ((posIdeleHom E t : IdeleGroup E) : A E) := h3
  refine Units.ext ?_
  rw [coe_smul_idele, ← h4, smul_adeleMap]

end Conc

/- English proof (translation)
Introduce `E _ _ D β hc hinv h`. Establish `hbar : ∀ z : (A E)ˣ, Units.map (D.bar : A E →* A E) z = D.σ • (z : IdeleGroup E)` using `fun z => Units.ext rfl`. Set `c : IdeleGroup.normOneSubgroup E →* IdeleGroup.normOneSubgroup E` to `{ toFun := fun z => ⟨(z : IdeleGroup E) * (D.σ • (z : IdeleGroup E))⁻¹, by`. Use `MonoidHom.mem_ker.2 ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_inv, ← GroundTheory.Automorphic.EllipticTorus.ideleModule_ideleNorm (K := ℚ) (D.σ • (z : IdeleGroup E)), ideleNorm_smul, GroundTheory.Automorphic.EllipticTorus.ideleModule_ideleNorm, mul_inv_cancel]⟩`.

Use the proof step `map_one' := Subtype.ext (by simp)`. Use the proof step `map_mul' := fun x y => Subtype.ext (by`. Simplify using `only [Subgroup.coe_mul, smul_mul', mul_inv]`. Conclude with `mul_mul_mul_comm _ _ _ _) }`. Establish `hcv : ∀ z, ((c z : IdeleGroup.normOneSubgroup E) : IdeleGroup E) = (z : IdeleGroup E) * (D.σ • (z : IdeleGroup E))⁻¹` using `fun z => rfl`.

Establish `hcc : Continuous c` using `(continuous_subtype_val.mul ((continuous_const_smul D.σ).comp continuous_subtype_val).inv).subtype_mk _`. Establish `hcN : ∀ k ∈ diagonalNormOne E, c k ∈ diagonalNormOne E`. Introduce `k hk`. Take `⟨e, he⟩` from `Subgroup.mem_subgroupOf.1 hk`. Use `Subgroup.mem_subgroupOf.2 ⟨e * (D.σ • e)⁻¹, ?_⟩` and prove the remaining obligations.

Rewrite using `[hcv, ← he, map_mul, map_inv, smul_diagonal]`. Establish `hs : ∀ u : IdeleGroup.normOneSubgroup E, ∃ k ∈ diagonalNormOne E, u * k ∈ normOneFundamentalDomain E`. Introduce `u`. Take `⟨e, he, -⟩` from `existsUnique_mul_mem_normOneFundamentalDomain E u`. Conclude with `⟨_, ⟨e, rfl⟩, he⟩`.

Establish `hβc : Continuous fun z : IdeleGroup.normOneSubgroup E => β (z : IdeleGroup E)` using `hc.comp continuous_subtype_val`. Establish `hβi : ∀ k ∈ diagonalNormOne E, ∀ x : IdeleGroup.normOneSubgroup E, β ((x * k : IdeleGroup.normOneSubgroup E) : IdeleGroup E) = β (x : IdeleGroup E)`. Introduce `k hk x`. Take `⟨e, he⟩` from `Subgroup.mem_subgroupOf.1 hk`. Rewrite using `[Subgroup.coe_mul, ← he, mul_comm]`.

Conclude with `hinv e _`. Take `⟨χ₁, h1N, h1c, h1⟩` from `char_sel (normOneMeasure E) (diagonalNormOne E) (normOneFundamentalDomain E) (isFundamentalDomain_normOneFundamentalDomain E _) (isCompact_closure_normOneFundamentalDomain E) hs c hcc hcN _ hβc hβi (by`. Introduce `h0`. Apply `h` to reduce the goal to its premises. Rewrite using `[← h0]`.

Unfold `UI`. Use `integral_congr_ae (ae_of_all _ fun z => ?_)` and prove the remaining obligations. Simplify using `only [hbar, hcv])`. Take `⟨χ, hχ1, hχp⟩` from `ext_char E χ₁ (fun k => h1N _ ⟨k, rfl⟩)`. Use `⟨χ, fun z => ?_, fun z hz => ?_, ?_⟩` and prove the remaining obligations.

Establish `hfix : D.σ • rho E (IdeleGroup.ideleModule E z) = rho E (IdeleGroup.ideleModule E z)` using `gal_fix_pos E D.σ _`. Establish `e : z * (Units.map (D.bar : A E →* A E) z)⁻¹ = ((c (proj E z) : IdeleGroup.normOneSubgroup E) : IdeleGroup E)`. Rewrite using `[hbar, hcv]`. Express the relevant statement in the definitionally equal form `_ = z * (rho E (IdeleGroup.ideleModule E z))⁻¹ * (D.σ • (z * (rho E (IdeleGroup.ideleModule E z))⁻¹))⁻¹`. Rewrite using `[smul_mul', smul_inv', hfix]`.

Establish `key : ∀ a b r : IdeleGroup E, a * b⁻¹ = a * r⁻¹ * (b * r⁻¹)⁻¹` using `fun a b r => by`. Rewrite using `[mul_inv, inv_inv, mul_assoc, ← mul_assoc r⁻¹, mul_comm r⁻¹, mul_assoc, inv_mul_cancel, mul_one]`. Conclude with `key _ _ _`. Use `Units.ext ?_` and prove the remaining obligations. Rewrite using `[e, hχ1, h1c]`.

Simplify using the standard rewrite rules. Take `⟨s, hs'⟩` from `hz`. Establish `h2 : GroundTheory.Automorphic.Reduction.centralSection E 2 s = GroundTheory.Automorphic.Reduction.diagUnits 2 fun _ => GroundTheory.Automorphic.Reduction.posIdeleHom E (GroundTheory.Automorphic.Reduction.rpowHom ((2 * Module.finrank ℚ E : ℝ))⁻¹ s)`. Rewrite using `[GroundTheory.Automorphic.Reduction.centralSection, MonoidHom.comp_apply, MonoidHom.comp_apply, GroundTheory.Automorphic.Reduction.scalarUnits_apply]`. Simplify using the standard rewrite rules.

Rewrite `hs'` using `[h2]`. Establish `h3` using `congrArg (fun g : GL (Fin 2) (A E) => g.val 0 0) hs'`. Use `beta_reduce at h3`. Rewrite `h3` using `[GroundTheory.Automorphic.Reduction.coe_diagUnits, Matrix.diagonal_apply_eq]`. Establish `h4 : z = GroundTheory.Automorphic.Reduction.posIdeleHom E (GroundTheory.Automorphic.Reduction.rpowHom ((2 * Module.finrank ℚ E : ℝ))⁻¹ s)`.

Use `Units.ext ?_` and prove the remaining obligations. Rewrite using `[← h3]`. Simplify using the standard rewrite rules. Use `Units.ext ?_` and prove the remaining obligations. Rewrite using `[hχp, h4, pos_rho, proj_rho]`.

Simplify using the standard rewrite rules. Introduce `h0`. Apply `h1` to reduce the goal to its premises. Rewrite using `[← h0]`. Unfold `UI`.

Use `integral_congr_ae (ae_of_all _ fun t => ?_)` and prove the remaining obligations. Simplify using `only [hχ1]`.
-/
theorem UpperTheory.ConvolutionTheory.RankTwoDescent.charSel :
    CharSel := by
  intro E _ _ D β hc hinv h
  have hbar : ∀ z : (A E)ˣ, Units.map (D.bar : A E →* A E) z = D.σ • (z : IdeleGroup E) := fun z => Units.ext rfl
  let c : IdeleGroup.normOneSubgroup E →* IdeleGroup.normOneSubgroup E :=
    { toFun := fun z => ⟨(z : IdeleGroup E) * (D.σ • (z : IdeleGroup E))⁻¹, by
        refine MonoidHom.mem_ker.2 ?_
        rw [map_mul, map_inv, ← GroundTheory.Automorphic.EllipticTorus.ideleModule_ideleNorm (K := ℚ) (D.σ • (z : IdeleGroup E)),
          ideleNorm_smul, GroundTheory.Automorphic.EllipticTorus.ideleModule_ideleNorm, mul_inv_cancel]⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        simp only [Subgroup.coe_mul, smul_mul', mul_inv]
        exact mul_mul_mul_comm _ _ _ _) }
  have hcv : ∀ z, ((c z : IdeleGroup.normOneSubgroup E) : IdeleGroup E) =
      (z : IdeleGroup E) * (D.σ • (z : IdeleGroup E))⁻¹ := fun z => rfl
  have hcc : Continuous c :=
    (continuous_subtype_val.mul ((continuous_const_smul D.σ).comp continuous_subtype_val).inv).subtype_mk _
  have hcN : ∀ k ∈ diagonalNormOne E, c k ∈ diagonalNormOne E := by
    intro k hk
    obtain ⟨e, he⟩ := Subgroup.mem_subgroupOf.1 hk
    refine Subgroup.mem_subgroupOf.2 ⟨e * (D.σ • e)⁻¹, ?_⟩
    rw [hcv, ← he, map_mul, map_inv, smul_diagonal]
  have hs : ∀ u : IdeleGroup.normOneSubgroup E, ∃ k ∈ diagonalNormOne E, u * k ∈ normOneFundamentalDomain E := by
    intro u
    obtain ⟨e, he, -⟩ := existsUnique_mul_mem_normOneFundamentalDomain E u
    exact ⟨_, ⟨e, rfl⟩, he⟩
  have hβc : Continuous fun z : IdeleGroup.normOneSubgroup E => β (z : IdeleGroup E) := hc.comp continuous_subtype_val
  have hβi : ∀ k ∈ diagonalNormOne E, ∀ x : IdeleGroup.normOneSubgroup E,
      β ((x * k : IdeleGroup.normOneSubgroup E) : IdeleGroup E) = β (x : IdeleGroup E) := by
    intro k hk x
    obtain ⟨e, he⟩ := Subgroup.mem_subgroupOf.1 hk
    rw [Subgroup.coe_mul, ← he, mul_comm]
    exact hinv e _
  obtain ⟨χ₁, h1N, h1c, h1⟩ := char_sel (normOneMeasure E) (diagonalNormOne E) (normOneFundamentalDomain E)
    (isFundamentalDomain_normOneFundamentalDomain E _) (isCompact_closure_normOneFundamentalDomain E) hs
    c hcc hcN _ hβc hβi (by
      intro h0
      apply h
      rw [← h0]
      unfold UI
      refine integral_congr_ae (ae_of_all _ fun z => ?_)
      simp only [hbar, hcv])
  obtain ⟨χ, hχ1, hχp⟩ := ext_char E χ₁ (fun k => h1N _ ⟨k, rfl⟩)
  refine ⟨χ, fun z => ?_, fun z hz => ?_, ?_⟩
  · have hfix : D.σ • rho E (IdeleGroup.ideleModule E z) = rho E (IdeleGroup.ideleModule E z) := gal_fix_pos E D.σ _
    have e : z * (Units.map (D.bar : A E →* A E) z)⁻¹ = ((c (proj E z) : IdeleGroup.normOneSubgroup E) : IdeleGroup E) := by
      rw [hbar, hcv]
      change _ = z * (rho E (IdeleGroup.ideleModule E z))⁻¹ * (D.σ • (z * (rho E (IdeleGroup.ideleModule E z))⁻¹))⁻¹
      rw [smul_mul', smul_inv', hfix]
      have key : ∀ a b r : IdeleGroup E, a * b⁻¹ = a * r⁻¹ * (b * r⁻¹)⁻¹ := fun a b r => by
        rw [mul_inv, inv_inv, mul_assoc, ← mul_assoc r⁻¹, mul_comm r⁻¹, mul_assoc, inv_mul_cancel, mul_one]
      exact key _ _ _
    refine Units.ext ?_
    rw [e, hχ1, h1c]
    simp
  · obtain ⟨s, hs'⟩ := hz
    have h2 : GroundTheory.Automorphic.Reduction.centralSection E 2 s = GroundTheory.Automorphic.Reduction.diagUnits 2 fun _ =>
        GroundTheory.Automorphic.Reduction.posIdeleHom E (GroundTheory.Automorphic.Reduction.rpowHom ((2 * Module.finrank ℚ E : ℝ))⁻¹ s) := by
      rw [GroundTheory.Automorphic.Reduction.centralSection, MonoidHom.comp_apply, MonoidHom.comp_apply, GroundTheory.Automorphic.Reduction.scalarUnits_apply]
      simp
    rw [h2] at hs'
    have h3 := congrArg (fun g : GL (Fin 2) (A E) => g.val 0 0) hs'
    beta_reduce at h3
    rw [GroundTheory.Automorphic.Reduction.coe_diagUnits, Matrix.diagonal_apply_eq] at h3
    have h4 : z = GroundTheory.Automorphic.Reduction.posIdeleHom E (GroundTheory.Automorphic.Reduction.rpowHom ((2 * Module.finrank ℚ E : ℝ))⁻¹ s) := by
      refine Units.ext ?_
      rw [← h3]
      simp
    refine Units.ext ?_
    rw [hχp, h4, pos_rho, proj_rho]
    simp
  · intro h0
    apply h1
    rw [← h0]
    unfold UI
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp only [hχ1]
