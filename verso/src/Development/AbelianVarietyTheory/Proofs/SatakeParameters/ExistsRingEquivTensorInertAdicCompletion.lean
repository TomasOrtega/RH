import Mathlib
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Formalism.SatakeDualWeyl.StatementG
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsFieldAdicCompletionTensorOfInert

open IsDedekindDomain NumberField Formalism.UG GlobalTheory.SelfDualGenus
open scoped TensorProduct Matrix

namespace GlobalTheory.InertCompletion

open scoped WithZeroTopology in

/- English proof (translation)
Establish `h' : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal` using `h`. Establish `: P.asIdeal.LiesOver v.asIdeal` using `⟨v.isMaximal.eq_of_le (Ideal.comap_ne_top _ P.isPrime.ne_top) (h' ▸ Ideal.le_comap_map)⟩`. Establish `he : Ideal.ramificationIdx' v.asIdeal P.asIdeal = 1`. Assume the negation of the conclusion as `hne`. Use `(Ideal.ramificationIdx'_ne_one_iff h'.le).1 hne` as an intermediate fact.

Rewrite `this` using `[h']`. Conclude with `absurd this (not_le_of_gt (Ideal.pow_lt_self _ P.ne_bot P.isPrime.ne_top 2 le_rfl))`. Establish `hc` using `(HeightOneSpectrum.uniformContinuous_algebraMap_liesOver F E v P).continuous`. Set `φ : v.adicCompletion F →+* P.adicCompletion E` to `((HeightOneSpectrum.adicCompletion.equiv E P).symm.toRingHom.comp (UniformSpace.Completion.mapRingHom (algebraMap (WithVal (v.valuation F)) (WithVal (P.valuation E))) hc)).comp (HeightOneSpectrum.adicCompletion.equiv F v).toRingHom`. Establish `hφ : ∀ x : F, φ (algebraMap F _ x) = algebraMap E _ (algebraMap F E x)` using `fun x => by`.

Apply `HeightOneSpectrum.adicCompletion.ext` to reduce the goal to its premises. Conclude with `UniformSpace.Completion.mapRingHom_coe hc (WithVal.toVal _ x)`. Establish `hcont : Continuous φ` using `(HeightOneSpectrum.adicCompletion.continuous_ofCompletion E P).comp ((UniformSpace.Completion.continuous_map (f := algebraMap (WithVal (v.valuation F)) (WithVal (P.valuation E)))).comp (HeightOneSpectrum.adicCompletion.continuous_toCompletion F v))`. Use `⟨φ, hcont, hφ, fun x => ?_⟩` and prove the remaining obligations. Use `(HeightOneSpectrum.denseRange_algebraMap F v).induction_on (p := fun x => Valued.v (φ x) = Valued.v x) x (isClosed_eq ((Valued.continuous_valuation_of_surjective (P.valuedAdicCompletion_surjective E)).comp hcont) (Valued.continuous_valuation_of_surjective (v.valuedAdicCompletion_ …` and prove the remaining obligations.

Rewrite using `[hφ, Idele.valued_algebraMap, Idele.valued_algebraMap, ← HeightOneSpectrum.valuation_liesOver E v P, he, pow_one]`.
-/
theorem exists_completion_map {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E))
    (h : IsInertAt F E v P) :
    ∃ φ : v.adicCompletion F →+* P.adicCompletion E, Continuous φ ∧
      (∀ x : F, φ (algebraMap F _ x) = algebraMap E _ (algebraMap F E x)) ∧
      ∀ x, Valued.v (φ x) = Valued.v x := by
  have h' : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal := h
  have : P.asIdeal.LiesOver v.asIdeal := ⟨v.isMaximal.eq_of_le
    (Ideal.comap_ne_top _ P.isPrime.ne_top) (h' ▸ Ideal.le_comap_map)⟩
  have he : Ideal.ramificationIdx' v.asIdeal P.asIdeal = 1 := by
    by_contra hne
    have := (Ideal.ramificationIdx'_ne_one_iff h'.le).1 hne
    rw [h'] at this
    exact absurd this (not_le_of_gt (Ideal.pow_lt_self _ P.ne_bot P.isPrime.ne_top 2 le_rfl))
  have hc := (HeightOneSpectrum.uniformContinuous_algebraMap_liesOver F E v P).continuous
  let φ : v.adicCompletion F →+* P.adicCompletion E :=
    ((HeightOneSpectrum.adicCompletion.equiv E P).symm.toRingHom.comp
    (UniformSpace.Completion.mapRingHom
      (algebraMap (WithVal (v.valuation F)) (WithVal (P.valuation E))) hc)).comp
      (HeightOneSpectrum.adicCompletion.equiv F v).toRingHom
  have hφ : ∀ x : F, φ (algebraMap F _ x) = algebraMap E _ (algebraMap F E x) := fun x => by
    apply HeightOneSpectrum.adicCompletion.ext
    exact UniformSpace.Completion.mapRingHom_coe hc (WithVal.toVal _ x)
  have hcont : Continuous φ :=
    (HeightOneSpectrum.adicCompletion.continuous_ofCompletion E P).comp
      ((UniformSpace.Completion.continuous_map
        (f := algebraMap (WithVal (v.valuation F)) (WithVal (P.valuation E)))).comp
        (HeightOneSpectrum.adicCompletion.continuous_toCompletion F v))
  refine ⟨φ, hcont, hφ, fun x => ?_⟩
  refine (HeightOneSpectrum.denseRange_algebraMap F v).induction_on
    (p := fun x => Valued.v (φ x) = Valued.v x) x
    (isClosed_eq
      ((Valued.continuous_valuation_of_surjective (P.valuedAdicCompletion_surjective E)).comp hcont)
      (Valued.continuous_valuation_of_surjective (v.valuedAdicCompletion_surjective F))) fun k => ?_
  rw [hφ, Idele.valued_algebraMap, Idele.valued_algebraMap,
    ← HeightOneSpectrum.valuation_liesOver E v P, he, pow_one]

/- English proof (translation)
Use `(AddMonoidHomClass.isometry_of_norm σ fun x => ?_).continuous` and prove the remaining obligations. Conclude with `le_antisymm (Valued.toNormedField.norm_le_iff.2 (h x).le) (Valued.toNormedField.norm_le_iff.2 (h x).ge)`.
-/
theorem continuous_of_valued_eq {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))
    (σ : P.adicCompletion E →+* P.adicCompletion E) (h : ∀ x, Valued.v (σ x) = Valued.v x) :
    Continuous σ := by
  refine (AddMonoidHomClass.isometry_of_norm σ fun x => ?_).continuous
  exact le_antisymm (Valued.toNormedField.norm_le_iff.2 (h x).le) (Valued.toNormedField.norm_le_iff.2 (h x).ge)

/- English proof (translation)
Use `letI : Algebra (v.adicCompletion F) (P.adicCompletion E) := φ.toAlgebra`. Use `haveI : ContinuousSMul (v.adicCompletion F) (P.adicCompletion E) := continuousSMul_of_algebraMap _ _ hc`. Use `letI : NontriviallyNormedField (v.adicCompletion F) := Valued.toNontriviallyNormedField _ _`. Set `f : v.adicCompletion F ⊗[F] E →ₐ[v.adicCompletion F] P.adicCompletion E` to `⟨ψ, fun a => (hψ a 1).trans (by rw [map_one, mul_one]; rfl)⟩`. Establish `hcl : IsClosed (LinearMap.range f.toLinearMap : Set (P.adicCompletion E))` using `Submodule.closed_of_finiteDimensional _`.

Introduce `y`. Use `(HeightOneSpectrum.denseRange_algebraMap E P).induction_on (p := fun y => y ∈ (LinearMap.range f.toLinearMap : Set (P.adicCompletion E))) y hcl fun x => ?_` and prove the remaining obligations. Conclude with `⟨1 ⊗ₜ x, (hψ 1 x).trans (by rw [map_one, one_mul])⟩`.
-/
theorem surjective_of_continuous {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E))
    (φ : v.adicCompletion F →+* P.adicCompletion E) (hc : Continuous φ)
    (ψ : v.adicCompletion F ⊗[F] E →+* P.adicCompletion E)
    (hψ : ∀ a x, ψ (a ⊗ₜ x) = φ a * algebraMap E _ x) : Function.Surjective ψ := by
  letI : Algebra (v.adicCompletion F) (P.adicCompletion E) := φ.toAlgebra
  haveI : ContinuousSMul (v.adicCompletion F) (P.adicCompletion E) :=
    continuousSMul_of_algebraMap _ _ hc
  letI : NontriviallyNormedField (v.adicCompletion F) := Valued.toNontriviallyNormedField _ _
  let f : v.adicCompletion F ⊗[F] E →ₐ[v.adicCompletion F] P.adicCompletion E :=
    ⟨ψ, fun a => (hψ a 1).trans (by rw [map_one, mul_one]; rfl)⟩
  have hcl : IsClosed (LinearMap.range f.toLinearMap : Set (P.adicCompletion E)) :=
    Submodule.closed_of_finiteDimensional _
  intro y
  refine (HeightOneSpectrum.denseRange_algebraMap E P).induction_on
    (p := fun y => y ∈ (LinearMap.range f.toLinearMap : Set (P.adicCompletion E))) y hcl fun x => ?_
  exact ⟨1 ⊗ₜ x, (hψ 1 x).trans (by rw [map_one, one_mul])⟩

/- English proof (translation)
Introduce `E _ _ _ _ v P h σ hσ hσv`. Take `⟨φ, hc, hφ, hv⟩` from `exists_completion_map v P h`. Choose the witnesses or unpack the hypotheses as in `⟨ψ, hψ⟩ : ∃ ψ : LocAlg v →+* P.adicCompletion E, ∀ a x, ψ (a ⊗ₜ x) = φ a * algebraMap E _ x := by`. Use `letI : Algebra (maximalRealSubfield E) (P.adicCompletion E) := ((algebraMap E (P.adicCompletion E)).comp (algebraMap (maximalRealSubfield E) E)).toAlgebra`. Set `f : E →ₐ[maximalRealSubfield E] P.adicCompletion E` to `⟨algebraMap E _, fun _ => rfl⟩`.

Set `g : v.adicCompletion (maximalRealSubfield E) →ₐ[maximalRealSubfield E] P.adicCompletion E` to `⟨φ, hφ⟩`. Conclude with `⟨(Algebra.TensorProduct.productMap g f).toRingHom, fun a x => rfl⟩`. Establish `hF : IsField (LocAlg v)` using `InertField.isField_of_inert _ E (Algebra.IsQuadraticExtension.finrank_eq_two _ E) v (by`. Rewrite using `[show Ideal.map _ v.asIdeal = P.asIdeal from h]`. Conclude with `P.isPrime)`.

Establish `hinj : Function.Injective ψ`. Use `letI := hF.toField`. Conclude with `ψ.injective`. Establish `hE : ∀ x : E, ψ (locEmb v x) = algebraMap E _ x` using `fun x => (hψ 1 x).trans (by rw [map_one, one_mul])`. Establish `hA : ∀ a, ψ (algebraMap _ (LocAlg v) a) = φ a` using `fun a => (hψ a 1).trans (by rw [map_one, mul_one])`.

Establish `hσφ : ∀ a, σ (φ a) = φ a` using `fun a => congrFun ((HeightOneSpectrum.denseRange_algebraMap (maximalRealSubfield E) v).equalizer ((continuous_of_valued_eq P σ hσv).comp hc) hc (funext fun x => by`. Simplify using `only [Function.comp_apply, hφ, hσ]`. Conclude with `congrArg _ ((IsCMField.complexConj E).commutes x))) a`. Establish `hconj : ∀ z, ψ (locConj v z) = σ (ψ z)` using `fun z => by`. Proceed by induction on `z using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul a x => rw [locConj_tmul, hψ, hψ, map_mul, hσφ, hσ]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Establish `hint : ∀ s : 𝓞 E, Valued.v (algebraMap E (P.adicCompletion E) (s : E)) ≤ 1` using `fun s => (Idele.valued_algebraMap P (s : E)).trans_le (P.valuation_le_one s)`. Use `⟨RingEquiv.ofBijective ψ ⟨hinj, surjective_of_continuous v P φ hc ψ hψ⟩, hE, hconj, fun z => ⟨fun hz => ?_, fun hz => ?_⟩⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `Valued.v (ψ z) ≤ 1`. Proceed by induction on `hz using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Take `⟨a, rfl⟩` from `hx`. Conclude with `(congrArg Valued.v (hE a)).trans_le (hint a)`.

Consider the case `algebraMap a => exact ((congrArg Valued.v (hA a)).trans (hv a)).trans_le a.2`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `Valuation.map_add_le _ hx hy`. Consider the case `mul x y _ _ hx hy => rw [map_mul, map_mul]`. Conclude with `mul_le_one' hx hy`.

Use `replace hz : Valued.v (ψ z) ≤ 1 := hz`. Establish `fix : ∀ w : LocAlg v, locConj v w = w → Valued.v (ψ w) ≤ 1 → w ∈ locOrder v`. Introduce `w hw hw1`. Take `⟨a, rfl⟩` from `exists_of_locConj_eq v hw`. Rewrite `hw1` using `[hA, hv]`.

Conclude with `(locOrder v).algebraMap_mem ⟨a, hw1⟩`. Take `⟨θ, hθ⟩` from `exists_sub_conj_notMem P.asIdeal P.isPrime.ne_top`. Establish `hδ1 : P.valuation E ((θ : E) - ReciprocityTheory.ChartRestriction.G.FD.cc (θ : E)) = 1` using `(HeightOneSpectrum.valuation_eq_one_iff_notMem (K := E) P).2 hθ`. Use `set δ : E := (θ : E) - ReciprocityTheory.ChartRestriction.G.FD.cc (θ : E) with hδ`. Establish `hδ0 : δ ≠ 0`.

Introduce `h0`. Rewrite `hδ1` using `[h0, map_zero]`. Conclude with `zero_ne_one hδ1`. Establish `hcδ : ReciprocityTheory.ChartRestriction.G.FD.cc δ⁻¹ = -δ⁻¹`. Establish `: ReciprocityTheory.ChartRestriction.G.FD.cc δ = -δ` using `by simp [hδ, ReciprocityTheory.ChartRestriction.G.FD.cc]`.

Rewrite using `[← inv_neg, ← this]`. Conclude with `map_inv₀ (IsCMField.complexConj E) δ`. Establish `hone : locEmb v δ⁻¹ * (locEmb v θ - locEmb v (ReciprocityTheory.ChartRestriction.G.FD.cc (θ : E))) = 1`. Rewrite using `[← map_sub, ← map_mul, inv_mul_cancel₀ hδ0, map_one]`. Use `set b : LocAlg v := (z - locConj v z) * locEmb v δ⁻¹ with hb`.

Establish `hb1 : locConj v b = b`. Rewrite using `[hb, map_mul, map_sub, locConj_locConj, locConj_locEmb, hcδ, map_neg]`. Expand and normalize the polynomial expressions, which then agree. Establish `hb2 : Valued.v (ψ b) ≤ 1`. Rewrite using `[hb, map_mul, map_mul, hE, Idele.valued_algebraMap, map_inv₀, hδ1, inv_one, mul_one, map_sub, hconj]`.

Conclude with `Valuation.map_sub_le _ hz ((hσv _).trans_le hz)`. Establish `ha1 : locConj v (z - b * locEmb v θ) = z - b * locEmb v θ`. Rewrite using `[map_sub, map_mul, hb1, locConj_locEmb, hb]`. Take the linear combination `(z - locConj v z) * hone`. Establish `ha2 : Valued.v (ψ (z - b * locEmb v θ)) ≤ 1`.

Rewrite using `[map_sub, map_mul, hE]`. Use `Valuation.map_sub_le _ hz ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `mul_le_one' hb2 (hint θ)`. Rewrite using `[← sub_add_cancel z (b * locEmb v θ)]`.

Conclude with `add_mem (fix _ ha1 ha2) (mul_mem (fix _ hb1 hb2) (locEmb_mem_locOrder v θ))`.
-/
theorem exists_ringEquiv_completion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)] (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (P : HeightOneSpectrum (𝓞 E)), IsInertAt (maximalRealSubfield E) E v P → ∀ σ : P.adicCompletion E →+* P.adicCompletion E, (∀ x : E, σ (algebraMap E (P.adicCompletion E) x) = algebraMap E (P.adicCompletion E) (ReciprocityTheory.ChartRestriction.G.FD.cc x)) → (∀ x, Valued.v (σ x) = Valued.v x) → ∃ ψ : LocAlg v ≃+* P.adicCompletion E, (∀ x : E, ψ (locEmb v x) = algebraMap E (P.adicCompletion E) x) ∧ (∀ z, ψ (locConj v z) = σ (ψ z)) ∧ ∀ z, z ∈ locOrder v ↔ Valued.v (ψ z) ≤ 1 := by
  intro E _ _ _ _ v P h σ hσ hσv
  obtain ⟨φ, hc, hφ, hv⟩ := exists_completion_map v P h
  obtain ⟨ψ, hψ⟩ : ∃ ψ : LocAlg v →+* P.adicCompletion E,
      ∀ a x, ψ (a ⊗ₜ x) = φ a * algebraMap E _ x := by
    letI : Algebra (maximalRealSubfield E) (P.adicCompletion E) :=
      ((algebraMap E (P.adicCompletion E)).comp (algebraMap (maximalRealSubfield E) E)).toAlgebra
    let f : E →ₐ[maximalRealSubfield E] P.adicCompletion E := ⟨algebraMap E _, fun _ => rfl⟩
    let g : v.adicCompletion (maximalRealSubfield E) →ₐ[maximalRealSubfield E] P.adicCompletion E :=
      ⟨φ, hφ⟩
    exact ⟨(Algebra.TensorProduct.productMap g f).toRingHom, fun a x => rfl⟩
  have hF : IsField (LocAlg v) := InertField.isField_of_inert _ E
    (Algebra.IsQuadraticExtension.finrank_eq_two _ E) v (by
      rw [show Ideal.map _ v.asIdeal = P.asIdeal from h]; exact P.isPrime)
  have hinj : Function.Injective ψ := by
    letI := hF.toField
    exact ψ.injective
  have hE : ∀ x : E, ψ (locEmb v x) = algebraMap E _ x := fun x =>
    (hψ 1 x).trans (by rw [map_one, one_mul])
  have hA : ∀ a, ψ (algebraMap _ (LocAlg v) a) = φ a := fun a =>
    (hψ a 1).trans (by rw [map_one, mul_one])
  have hσφ : ∀ a, σ (φ a) = φ a := fun a =>
    congrFun ((HeightOneSpectrum.denseRange_algebraMap (maximalRealSubfield E) v).equalizer
      ((continuous_of_valued_eq P σ hσv).comp hc) hc (funext fun x => by
        simp only [Function.comp_apply, hφ, hσ]
        exact congrArg _ ((IsCMField.complexConj E).commutes x))) a
  have hconj : ∀ z, ψ (locConj v z) = σ (ψ z) := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => rw [locConj_tmul, hψ, hψ, map_mul, hσφ, hσ]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hint : ∀ s : 𝓞 E, Valued.v (algebraMap E (P.adicCompletion E) (s : E)) ≤ 1 := fun s =>
    (Idele.valued_algebraMap P (s : E)).trans_le (P.valuation_le_one s)
  refine ⟨RingEquiv.ofBijective ψ ⟨hinj, surjective_of_continuous v P φ hc ψ hψ⟩, hE, hconj,
    fun z => ⟨fun hz => ?_, fun hz => ?_⟩⟩
  · change Valued.v (ψ z) ≤ 1
    induction hz using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact (congrArg Valued.v (hE a)).trans_le (hint a)
    | algebraMap a => exact ((congrArg Valued.v (hA a)).trans (hv a)).trans_le a.2
    | add x y _ _ hx hy => rw [map_add]; exact Valuation.map_add_le _ hx hy
    | mul x y _ _ hx hy => rw [map_mul, map_mul]; exact mul_le_one' hx hy
  · replace hz : Valued.v (ψ z) ≤ 1 := hz
    have fix : ∀ w : LocAlg v, locConj v w = w → Valued.v (ψ w) ≤ 1 → w ∈ locOrder v := by
      intro w hw hw1
      obtain ⟨a, rfl⟩ := exists_of_locConj_eq v hw
      rw [hA, hv] at hw1
      exact (locOrder v).algebraMap_mem ⟨a, hw1⟩
    obtain ⟨θ, hθ⟩ := exists_sub_conj_notMem P.asIdeal P.isPrime.ne_top
    have hδ1 : P.valuation E ((θ : E) - ReciprocityTheory.ChartRestriction.G.FD.cc (θ : E)) = 1 :=
      (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := E) P).2 hθ
    set δ : E := (θ : E) - ReciprocityTheory.ChartRestriction.G.FD.cc (θ : E) with hδ
    have hδ0 : δ ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hδ1
      exact zero_ne_one hδ1
    have hcδ : ReciprocityTheory.ChartRestriction.G.FD.cc δ⁻¹ = -δ⁻¹ := by
      have : ReciprocityTheory.ChartRestriction.G.FD.cc δ = -δ := by simp [hδ, ReciprocityTheory.ChartRestriction.G.FD.cc]
      rw [← inv_neg, ← this]
      exact map_inv₀ (IsCMField.complexConj E) δ
    have hone : locEmb v δ⁻¹ * (locEmb v θ - locEmb v (ReciprocityTheory.ChartRestriction.G.FD.cc (θ : E))) = 1 := by
      rw [← map_sub, ← map_mul, inv_mul_cancel₀ hδ0, map_one]
    set b : LocAlg v := (z - locConj v z) * locEmb v δ⁻¹ with hb
    have hb1 : locConj v b = b := by
      rw [hb, map_mul, map_sub, locConj_locConj, locConj_locEmb, hcδ, map_neg]; ring
    have hb2 : Valued.v (ψ b) ≤ 1 := by
      rw [hb, map_mul, map_mul, hE, Idele.valued_algebraMap, map_inv₀, hδ1, inv_one, mul_one,
        map_sub, hconj]
      exact Valuation.map_sub_le _ hz ((hσv _).trans_le hz)
    have ha1 : locConj v (z - b * locEmb v θ) = z - b * locEmb v θ := by
      rw [map_sub, map_mul, hb1, locConj_locEmb, hb]
      linear_combination (z - locConj v z) * hone
    have ha2 : Valued.v (ψ (z - b * locEmb v θ)) ≤ 1 := by
      rw [map_sub, map_mul, hE]
      refine Valuation.map_sub_le _ hz ?_
      rw [map_mul]
      exact mul_le_one' hb2 (hint θ)
    rw [← sub_add_cancel z (b * locEmb v θ)]
    exact add_mem (fix _ ha1 ha2) (mul_mem (fix _ hb1 hb2) (locEmb_mem_locOrder v θ))

end GlobalTheory.InertCompletion
