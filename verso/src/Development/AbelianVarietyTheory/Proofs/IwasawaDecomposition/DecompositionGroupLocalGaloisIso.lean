import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocDec

open Polynomial

/- English proof (translation)
Use `letI : NormedField (AlgebraicClosure K) := spectralNorm.normedField K (AlgebraicClosure K)`. Use `letI : NormedAlgebra K (AlgebraicClosure K) := spectralNorm.normedAlgebra K (AlgebraicClosure K)`. Use `show DenseRange ι`. Rewrite using `[Metric.denseRange_iff]`. Introduce `a δ δpos`.

Establish `hint : IsIntegral K a` using `Algebra.IsIntegral.isIntegral a`. Use `set f := minpoly K a with hf`. Establish `fmon : f.Monic` using `minpoly.monic hint`. Establish `fa0 : f.aeval a = 0` using `minpoly.aeval _ _`. Establish `fnatdeg0 : f.natDegree ≠ 0` using `(minpoly.natDegree_pos hint).ne'`.

Establish `hε : (δ / (max ‖a‖ 1)) ^ f.natDegree / (f.natDegree + 1) > 0` using `by positivity`. Take `⟨g, gmon, gdeg, gcoeff⟩` from `exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt hE fmon hε`. Take `⟨b, hb, hab⟩` from `exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt hε fa0 fmon (gmon.map _) (gdeg ▸ (g.natDegree_map _)) gcoeff (IsAlgClosed.splits _)`. Establish `hab : ‖a - b‖ < δ`. Rewrite `hab` using `[← Real.rpow_natCast, ← mul_comm_div, div_self, one_mul, ← Real.rpow_mul (div_pos δpos (by positivity)).le, mul_inv_cancel₀]`.

Simplify `hab` using `[mul_assoc, div_mul_cancel₀ _ (by positivity : (max ‖a‖ 1) > 0).ne']`. Simplify using `[fnatdeg0]`. Check the signs of the components of the expression. Establish `e : (g.map (algebraMap E K)).map (algebraMap K (AlgebraicClosure K)) = (g.map (algebraMap E Ω)).map (ι : Ω →+* AlgebraicClosure K)`. Rewrite using `[Polynomial.map_map, Polynomial.map_map, ι.comp_algebraMap]`.

Use `congr 1`. Rewrite `hb` using `[Polynomial.aroots_def, e, Splits.roots_map (IsAlgClosed.splits _), Multiset.mem_map]`. Take `⟨y, -, rfl⟩` from `hb`. Conclude with `⟨y, by rwa [dist_eq_norm]⟩`.
-/
theorem denseRange_of_isAlgClosed (K : Type) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
    [CharZero K] (E Ω : Type) [Field E] [Algebra E K] [Field Ω] [Algebra E Ω] [IsAlgClosed Ω]
    (hE : DenseRange (algebraMap E K)) (ι : Ω →ₐ[E] AlgebraicClosure K) :
    letI : NormedField (AlgebraicClosure K) := spectralNorm.normedField K (AlgebraicClosure K)
    DenseRange ι := by
  letI : NormedField (AlgebraicClosure K) := spectralNorm.normedField K (AlgebraicClosure K)
  letI : NormedAlgebra K (AlgebraicClosure K) := spectralNorm.normedAlgebra K (AlgebraicClosure K)
  show DenseRange ι
  rw [Metric.denseRange_iff]
  intro a δ δpos
  have hint : IsIntegral K a := Algebra.IsIntegral.isIntegral a
  set f := minpoly K a with hf
  have fmon : f.Monic := minpoly.monic hint
  have fa0 : f.aeval a = 0 := minpoly.aeval _ _
  have fnatdeg0 : f.natDegree ≠ 0 := (minpoly.natDegree_pos hint).ne'
  have hε : (δ / (max ‖a‖ 1)) ^ f.natDegree / (f.natDegree + 1) > 0 := by positivity
  obtain ⟨g, gmon, gdeg, gcoeff⟩ :=
    exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt hE fmon hε
  obtain ⟨b, hb, hab⟩ := exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt
      hε fa0 fmon (gmon.map _) (gdeg ▸ (g.natDegree_map _)) gcoeff (IsAlgClosed.splits _)
  have hab : ‖a - b‖ < δ := by
    rw [← Real.rpow_natCast, ← mul_comm_div, div_self, one_mul,
        ← Real.rpow_mul (div_pos δpos (by positivity)).le, mul_inv_cancel₀] at hab
    · simpa [mul_assoc, div_mul_cancel₀ _ (by positivity : (max ‖a‖ 1) > 0).ne'] using hab
    · simp [fnatdeg0]
    · positivity
  have e : (g.map (algebraMap E K)).map (algebraMap K (AlgebraicClosure K)) =
      (g.map (algebraMap E Ω)).map (ι : Ω →+* AlgebraicClosure K) := by
    rw [Polynomial.map_map, Polynomial.map_map, ι.comp_algebraMap]
    congr 1
  rw [Polynomial.aroots_def, e, Splits.roots_map (IsAlgClosed.splits _), Multiset.mem_map] at hb
  obtain ⟨y, -, rfl⟩ := hb
  exact ⟨y, by rwa [dist_eq_norm]⟩

/- English proof (translation)
Use `letI : NormedField (AlgebraicClosure K) := spectralNorm.normedField K (AlgebraicClosure K)`. Use `letI : NormedAlgebra K (AlgebraicClosure K) := spectralNorm.normedAlgebra K (AlgebraicClosure K)`. Introduce `j j' hd h`. Set `Kb` to `AlgebraicClosure K`. Set `C` to `UniformSpace.Completion Kb`.

Set `: NormedField Ω` to `NormedField.induced Ω Kb j.toRingHom j.injective`. Apply the tactic sequence `have hj : Isometry j := AddMonoidHomClass.isometry_of_norm j fun _ => rfl`. Set `f : Ω →+* C` to `(UniformSpace.Completion.coeRingHom : Kb →+* C).comp j'.toRingHom`. Apply the tactic sequence `have hf : Isometry f := AddMonoidHomClass.isometry_of_norm f fun x => by`. Express the relevant statement in the definitionally equal form `‖((j' x : Kb) : C)‖ = ‖j x‖`.

Rewrite using `[UniformSpace.Completion.norm_coe, h]`. Set `t : Kb →+* C` to `IsDenseInducing.extendRingHom hj.isUniformInducing hd hf.uniformContinuous`. Establish `ht : ∀ x, t (j x) = f x` using `fun x => uniformly_extend_of_ind hj.isUniformInducing hd hf.uniformContinuous x`. Establish `htc : Continuous t` using `(uniformContinuous_uniformly_extend hj.isUniformInducing hd hf.uniformContinuous).continuous`. Establish `: IsScalarTower K Kb C` using `inferInstance`.

Establish `hcoe : ∀ y : Kb, algebraMap Kb C y = (y : C)` using `fun y => rfl`. Establish `hq : ∀ x : K, t (algebraMap K Kb x) = algebraMap K C x`. Establish `hcC : Continuous (algebraMap K C)`. Establish `e : (algebraMap K C : K → C) = fun x => ((algebraMap K Kb x : Kb) : C)`. Use function extensionality and compare the values at `fun x => IsScalarTower.algebraMap_apply K Kb C x`.

Rewrite using `[e]`. Conclude with `(UniformSpace.Completion.continuous_coe Kb).comp (continuous_algebraMap K Kb)`. Use `hE.equalizer (htc.comp (continuous_algebraMap K Kb)) hcC (by` as an intermediate fact. Use function extensionality and compare the values at `e`. Simplify using `only [Function.comp_apply]`.

Establish `e1 : algebraMap K Kb (algebraMap E K e) = j (algebraMap E Ω e)`. Rewrite using `[AlgHom.commutes]`. Conclude with `(IsScalarTower.algebraMap_apply E K Kb e).symm`. Rewrite using `[e1, ht]`. Express the relevant statement in the definitionally equal form `((j' (algebraMap E Ω e) : Kb) : C) = ((algebraMap K Kb (algebraMap E K e) : Kb) : C)`.

Rewrite using `[AlgHom.commutes, IsScalarTower.algebraMap_apply E K Kb e])`. Conclude with `congrFun this`. Set `ta : Kb →ₐ[K] C` to `⟨t, hq⟩`. Use `⟨ta.restrictNormal' Kb, fun x => ?_⟩` and prove the remaining obligations. Apply `(algebraMap Kb C).injective` to reduce the goal to its premises.

Conclude with `(ta.restrictNormal_commutes Kb (j x)).trans (ht x)`.
-/
theorem exists_algEquiv_of_norm_eq (K : Type) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
    [CharZero K] (E Ω : Type) [Field E] [Algebra E K] [Field Ω] [Algebra E Ω]
    (hE : DenseRange (algebraMap E K)) :
    letI : NormedField (AlgebraicClosure K) := spectralNorm.normedField K (AlgebraicClosure K)
    ∀ (j j' : Ω →ₐ[E] AlgebraicClosure K), DenseRange j → (∀ x, ‖j' x‖ = ‖j x‖) →
      ∃ τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, ∀ x, τ (j x) = j' x := by
  letI : NormedField (AlgebraicClosure K) := spectralNorm.normedField K (AlgebraicClosure K)
  letI : NormedAlgebra K (AlgebraicClosure K) := spectralNorm.normedAlgebra K (AlgebraicClosure K)
  intro j j' hd h
  let Kb := AlgebraicClosure K
  let C := UniformSpace.Completion Kb
  let : NormedField Ω := NormedField.induced Ω Kb j.toRingHom j.injective
  have hj : Isometry j := AddMonoidHomClass.isometry_of_norm j fun _ => rfl
  let f : Ω →+* C := (UniformSpace.Completion.coeRingHom : Kb →+* C).comp j'.toRingHom
  have hf : Isometry f := AddMonoidHomClass.isometry_of_norm f fun x => by
    change ‖((j' x : Kb) : C)‖ = ‖j x‖
    rw [UniformSpace.Completion.norm_coe, h]
  let t : Kb →+* C :=
    IsDenseInducing.extendRingHom hj.isUniformInducing hd hf.uniformContinuous
  have ht : ∀ x, t (j x) = f x := fun x =>
    uniformly_extend_of_ind hj.isUniformInducing hd hf.uniformContinuous x
  have htc : Continuous t :=
    (uniformContinuous_uniformly_extend hj.isUniformInducing hd hf.uniformContinuous).continuous
  have : IsScalarTower K Kb C := inferInstance
  have hcoe : ∀ y : Kb, algebraMap Kb C y = (y : C) := fun y => rfl
  have hq : ∀ x : K, t (algebraMap K Kb x) = algebraMap K C x := by
    have hcC : Continuous (algebraMap K C) := by
      have e : (algebraMap K C : K → C) = fun x => ((algebraMap K Kb x : Kb) : C) :=
        funext fun x => IsScalarTower.algebraMap_apply K Kb C x
      rw [e]
      exact (UniformSpace.Completion.continuous_coe Kb).comp (continuous_algebraMap K Kb)
    have := hE.equalizer (htc.comp (continuous_algebraMap K Kb)) hcC (by
      funext e
      simp only [Function.comp_apply]
      have e1 : algebraMap K Kb (algebraMap E K e) = j (algebraMap E Ω e) := by
        rw [AlgHom.commutes]; exact (IsScalarTower.algebraMap_apply E K Kb e).symm
      rw [e1, ht]
      change ((j' (algebraMap E Ω e) : Kb) : C) = ((algebraMap K Kb (algebraMap E K e) : Kb) : C)
      rw [AlgHom.commutes, IsScalarTower.algebraMap_apply E K Kb e])
    exact congrFun this
  let ta : Kb →ₐ[K] C := ⟨t, hq⟩
  refine ⟨ta.restrictNormal' Kb, fun x => ?_⟩
  apply (algebraMap Kb C).injective
  exact (ta.restrictNormal_commutes Kb (j x)).trans (ht x)

/- English proof (translation)
Use `letI : NontriviallyNormedField (w.adicCompletion E) := Valued.toNontriviallyNormedField _ _`. Use `letI : NormedField (Kbar w) := spectralNorm.normedField (w.adicCompletion E) (Kbar w)`. Introduce `y`. Set `K` to `w.adicCompletion E`. Set `O` to `w.adicCompletionIntegers E`.

Establish `hO : ∀ x : K, ‖x‖ ≤ 1 ↔ x ∈ O` using `fun x => by`. Rewrite using `[Valued.toNormedField.norm_le_one_iff]`. Both sides reduce to the same expression. Establish `hy : IsIntegral K y` using `Algebra.IsIntegral.isIntegral y`. Establish `hn : ‖y‖ = spectralValue (minpoly K y)` using `rfl`.

Rewrite using `[hn, spectralValue_le_one_iff (minpoly.monic hy)]`. Prove the components needed by the constructor for the conclusion. Introduce `hi n`. Rewrite using `[minpoly.isIntegrallyClosed_eq_field_fractions' K hi, Polynomial.coeff_map, hO]`. Conclude with `((minpoly O y).coeff n).2`.

Introduce `hc`. Establish `hl : minpoly K y ∈ Polynomial.lifts (algebraMap O K)`. Rewrite using `[Polynomial.lifts_iff_coeff_lifts]`. Introduce `n`. Conclude with `⟨⟨_, (hO _).1 (hc n)⟩, rfl⟩`.

Take `⟨q, hq, -, hqm⟩` from `Polynomial.lifts_and_natDegree_eq_and_monic hl (minpoly.monic hy)`. Use `⟨q, hqm, ?_⟩` and prove the remaining obligations. Rewrite using `[← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap K, hq]`. Conclude with `minpoly.aeval K y`.
-/
theorem isIntegral_iff_norm_le_one (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    letI : NontriviallyNormedField (w.adicCompletion E) := Valued.toNontriviallyNormedField _ _
    letI : NormedField (Kbar w) := spectralNorm.normedField (w.adicCompletion E) (Kbar w)
    ∀ y : Kbar w, IsIntegral (w.adicCompletionIntegers E) y ↔ ‖y‖ ≤ 1 := by
  letI : NontriviallyNormedField (w.adicCompletion E) := Valued.toNontriviallyNormedField _ _
  letI : NormedField (Kbar w) := spectralNorm.normedField (w.adicCompletion E) (Kbar w)
  intro y
  let K := w.adicCompletion E
  let O := w.adicCompletionIntegers E
  have hO : ∀ x : K, ‖x‖ ≤ 1 ↔ x ∈ O := fun x => by
    rw [Valued.toNormedField.norm_le_one_iff]; rfl
  have hy : IsIntegral K y := Algebra.IsIntegral.isIntegral y
  have hn : ‖y‖ = spectralValue (minpoly K y) := rfl
  rw [hn, spectralValue_le_one_iff (minpoly.monic hy)]
  constructor
  · intro hi n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' K hi, Polynomial.coeff_map, hO]
    exact ((minpoly O y).coeff n).2
  · intro hc
    have hl : minpoly K y ∈ Polynomial.lifts (algebraMap O K) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨_, (hO _).1 (hc n)⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl (minpoly.monic hy)
    refine ⟨q, hqm, ?_⟩
    rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap K, hq]
    exact minpoly.aeval K y

end GlobalTheory.LocDec

namespace GlobalTheory.LocDec

open GlobalTheory.LocDict

/- English proof (translation)
Set `v : AbsoluteValue Ω ℝ` to `(NormedField.toAbsoluteValue L).comp j.injective`. Set `v' : AbsoluteValue Ω ℝ` to `(NormedField.toAbsoluteValue L).comp j'.injective`. Establish `hv : ∀ y, v y = ‖j y‖` using `fun _ => rfl`. Establish `hv' : ∀ y, v' y = ‖j' y‖` using `fun _ => rfl`. Establish `he : v.IsEquiv v'`.

Introduce `a b`. Break down `eq_or_ne b 0 with rfl | hb` into its components or cases. Simplify using the standard rewrite rules. Use `h (a / b)` as an intermediate fact. Rewrite `this` using `[map_div₀, map_div₀, norm_div, norm_div, div_le_one (by simpa using hb), div_le_one (by simpa using hb)]`.

Conclude with `this`. Take `⟨c, hc, hcv⟩` from `AbsoluteValue.isEquiv_iff_exists_rpow_eq.1 he`. Establish `e₁` using `congrFun hcv x₀`. Simplify using `only [hv, hv'] at e₁`. Establish `hc1 : c = 1` using `(Real.rpow_right_inj h₁ h₂.ne).1 ((e₁.trans h₀).trans (Real.rpow_one _).symm)`.

Establish `e₂` using `congrFun hcv x`. Simplify using `only [hv, hv', hc1, Real.rpow_one] at e₂`. Conclude with `e₂.symm`.
-/
theorem norm_eq_of_le_one_iff {Ω L : Type} [Field Ω] [NormedField L] (j j' : Ω →+* L)
    (h : ∀ x, ‖j x‖ ≤ 1 ↔ ‖j' x‖ ≤ 1) (x₀ : Ω) (h₀ : ‖j' x₀‖ = ‖j x₀‖) (h₁ : 0 < ‖j x₀‖)
    (h₂ : ‖j x₀‖ < 1) (x : Ω) : ‖j' x‖ = ‖j x‖ := by
  let v : AbsoluteValue Ω ℝ := (NormedField.toAbsoluteValue L).comp j.injective
  let v' : AbsoluteValue Ω ℝ := (NormedField.toAbsoluteValue L).comp j'.injective
  have hv : ∀ y, v y = ‖j y‖ := fun _ => rfl
  have hv' : ∀ y, v' y = ‖j' y‖ := fun _ => rfl
  have he : v.IsEquiv v' := by
    intro a b
    rcases eq_or_ne b 0 with rfl | hb
    · simp
    · have := h (a / b)
      rw [map_div₀, map_div₀, norm_div, norm_div, div_le_one (by simpa using hb),
        div_le_one (by simpa using hb)] at this
      exact this
  obtain ⟨c, hc, hcv⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.1 he
  have e₁ := congrFun hcv x₀
  simp only [hv, hv'] at e₁
  have hc1 : c = 1 := (Real.rpow_right_inj h₁ h₂.ne).1 ((e₁.trans h₀).trans (Real.rpow_one _).symm)
  have e₂ := congrFun hcv x
  simp only [hv, hv', hc1, Real.rpow_one] at e₂
  exact e₂.symm

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]

/- English proof (translation)
Use `letI : NontriviallyNormedField (w.adicCompletion E) := Valued.toNontriviallyNormedField _ _`. Use `letI : NormedField (Kbar w) := spectralNorm.normedField (w.adicCompletion E) (Kbar w)`. Establish `: IsAlgClosed Ω` using `IsAlgClosure.isAlgClosed E`. Establish `: CharZero (w.adicCompletion E)` using `charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective`. Establish `hdE : DenseRange (algebraMap E (w.adicCompletion E))` using `HeightOneSpectrum.denseRange_algebraMap E w`.

Establish `hA : ∀ z, z ∈ A ↔ ‖ι z‖ ≤ 1` using `fun z => (hι z).trans (isIntegral_iff_norm_le_one E w (ι z))`. Establish `hd : DenseRange ι` using `denseRange_of_isAlgClosed (w.adicCompletion E) E Ω hdE ι`. Establish `hnorm : ∀ (g : GalLoc w) (y : Kbar w), ‖g y‖ = ‖y‖` using `fun g y => (spectralNorm_eq_of_equiv g y).symm`. Establish `hcont : ∀ g : GalLoc w, Continuous g` using `fun g => (AddMonoidHomClass.isometry_of_norm g (hnorm g)).continuous`. Establish `hres : ∀ g : GalLoc w, ∃ σ ∈ Dec (F` using `E) A, Lifts ι g σ := by`.

Introduce `g`. Use `letI : Algebra Ω (Kbar w) := ι.toRingHom.toAlgebra`. Establish `: IsScalarTower E Ω (Kbar w)` using `IsScalarTower.of_algebraMap_eq fun x => (ι.commutes x).symm`. Set `ta : Kbar w →ₐ[E] Kbar w` to `g.toAlgHom.restrictScalars E`. Set `σ : Ω ≃ₐ[E] Ω` to `ta.restrictNormal' Ω`.

Establish `hσ : ∀ x, g (ι x) = ι (σ x)` using `fun x => (ta.restrictNormal_commutes Ω x).symm`. Use `⟨σ, ?_, hσ⟩` and prove the remaining obligations. Rewrite using `[mem_Dec]`. Use extensionality with `x`. Rewrite using `[ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, hA, hA, ← hnorm g, hσ]`.

Simplify using the standard rewrite rules. Use `choose r hr hr' using hres`. Set `ρ : GalLoc w →* Dec (F` to `E) A := MonoidHom.mk' (fun g => ⟨r g, hr g⟩) fun g g' => by`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `AlgEquiv.ext` to reduce the goal to its premises.

Introduce `x`. Apply `ι.toRingHom.injective` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `ι (r (g * g') x) = ι (r g (r g' x))`. Rewrite using `[← hr', ← hr', ← hr']`. Both sides reduce to the same expression.

Establish `hρ : ∀ (g : GalLoc w) (x : Ω), g (ι x) = ι ((ρ g : Ω ≃ₐ[E] Ω) x)` using `hr'`. Establish `hinj : Function.Injective ρ` using `fun g g' hgg => by`. Use `hd.equalizer (hcont g) (hcont g') (funext fun x => by simp only [Function.comp_apply]; rw [hρ, hρ, hgg])` as an intermediate fact. Conclude with `AlgEquiv.ext (congrFun this)`. Choose the witnesses or unpack the hypotheses as in `⟨x₀, hx₀, hx₀'⟩ : ∃ x₀ : E, 0 < ‖ι (algebraMap E Ω x₀)‖ ∧ ‖ι (algebraMap E Ω x₀)‖ < 1 := by`.

Take `⟨a, ha, ha0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot`. Establish `hn : ∀ y : E, ‖ι (algebraMap E Ω y)‖ = ‖algebraMap E (w.adicCompletion E) y‖` using `fun y => by`. Rewrite using `[AlgHom.commutes, IsScalarTower.algebraMap_apply E (w.adicCompletion E) (Kbar w)]`. Conclude with `spectralNorm_extends _`. Apply the tactic sequence `have hv : ∀ y : E, Valued.v (algebraMap E (w.adicCompletion E) y) = w.valuation E y := fun y => by first | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w y | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation w y | simp | rfl`.

Use `⟨(a : E), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hn, norm_pos_iff, map_ne_zero]`. Conclude with `ha0` after adjusting the coercions. Rewrite using `[hn, Valued.toNormedField.norm_lt_one_iff, hv]`. Conclude with `(HeightOneSpectrum.valuation_lt_one_iff_mem w a).2 ha`.

Establish `hsurj : Function.Surjective ρ` using `fun σ => by`. Set `j' : Ω →ₐ[E] Kbar w` to `ι.comp (σ : Ω ≃ₐ[E] Ω).toAlgHom`. Establish `hj' : ∀ x, ‖j' x‖ = ‖ι x‖` using `norm_eq_of_le_one_iff ι.toRingHom j'.toRingHom (fun x => by`. Express the relevant statement in the definitionally equal form `‖ι x‖ ≤ 1 ↔ ‖ι ((σ : Ω ≃ₐ[E] Ω) x)‖ ≤ 1`. Rewrite using `[← hA, ← hA, apply_mem_iff_of_mem_Dec σ.2])`.

Use the proof step `(algebraMap E Ω x₀) (by`. Express the relevant statement in the definitionally equal form `‖ι ((σ : Ω ≃ₐ[E] Ω) (algebraMap E Ω x₀))‖ = _`. Rewrite using `[AlgEquiv.commutes]`. Use the proof step `rfl) hx₀ hx₀'`. Take `⟨τ, hτ⟩` from `exists_algEquiv_of_norm_eq (w.adicCompletion E) E Ω hdE ι j' hd hj'`.

Use `⟨τ, Subtype.ext (AlgEquiv.ext fun x => ι.toRingHom.injective ?_)⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `ι ((ρ τ : Ω ≃ₐ[E] Ω) x) = ι ((σ : Ω ≃ₐ[E] Ω) x)`. Rewrite using `[← hρ, hτ]`. Both sides reduce to the same expression. Establish `hc : Continuous ρ`.

Use `continuous_induced_rng.2 ?_` and prove the remaining obligations. Use `continuous_of_continuousAt_one ((Dec (F := E) A).subtype.comp ρ) ?_` and prove the remaining obligations. Introduce `s hs`. Rewrite `hs` using `[map_one, krullTopology_mem_nhds_one_iff]`. Take `⟨L, hL, hsub⟩` from `hs`.

Set `b` to `Module.finBasis E L`. Establish `hi : ∀ i, ∀ᶠ g : GalLoc w in nhds 1, g (ι (b i)) = ι (b i)` using `fun i => (stabilizer_isOpen_of_isIntegral (K := w.adicCompletion E) (ι (b i))).mem_nhds (show (1 : GalLoc w) • ι (b i) = ι (b i) from rfl)`. Rewrite using `[Filter.mem_map]`. Use `filter_upwards [Filter.eventually_all.2 hi] with g hg`. Apply `hsub` to reduce the goal to its premises.

Rewrite using `[SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]`. Introduce `x hx`. Establish `: ((ρ g : Ω ≃ₐ[E] Ω).toLinearMap.comp L.val.toLinearMap) = L.val.toLinearMap` using `b.ext fun i => ι.toRingHom.injective ((hρ g _).symm.trans (hg i))`. Conclude with `LinearMap.congr_fun this ⟨x, hx⟩`. Set `e` to `MulEquiv.ofBijective ρ ⟨hinj, hsurj⟩`.

Use `⟨e.symm, Continuous.continuous_symm_of_equiv_compact_to_t2 (f := e.toEquiv) hc, hc, fun σ x => ?_⟩` and prove the remaining obligations. Rewrite using `[hρ]`. Conclude with `congrArg (fun σ : Dec (F := E) A => ι ((σ : Ω ≃ₐ[E] Ω) x)) (e.apply_symm_apply σ)`.
-/
theorem exists_mulEquiv_galLoc (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (ι : Ω →ₐ[E] Kbar w) (hι : IsLocEmb A w ι) :
    ∃ θ : Dec (F := E) A ≃* GalLoc w, Continuous θ ∧ Continuous θ.symm ∧
      ∀ σ : Dec (F := E) A, Lifts ι (θ σ) (σ : G E Ω) := by
  letI : NontriviallyNormedField (w.adicCompletion E) := Valued.toNontriviallyNormedField _ _
  letI : NormedField (Kbar w) := spectralNorm.normedField (w.adicCompletion E) (Kbar w)
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have : CharZero (w.adicCompletion E) :=
    charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective
  have hdE : DenseRange (algebraMap E (w.adicCompletion E)) := HeightOneSpectrum.denseRange_algebraMap E w
  have hA : ∀ z, z ∈ A ↔ ‖ι z‖ ≤ 1 := fun z => (hι z).trans (isIntegral_iff_norm_le_one E w (ι z))
  have hd : DenseRange ι := denseRange_of_isAlgClosed (w.adicCompletion E) E Ω hdE ι
  have hnorm : ∀ (g : GalLoc w) (y : Kbar w), ‖g y‖ = ‖y‖ := fun g y =>
    (spectralNorm_eq_of_equiv g y).symm
  have hcont : ∀ g : GalLoc w, Continuous g := fun g =>
    (AddMonoidHomClass.isometry_of_norm g (hnorm g)).continuous

  have hres : ∀ g : GalLoc w, ∃ σ ∈ Dec (F := E) A, Lifts ι g σ := by
    intro g
    letI : Algebra Ω (Kbar w) := ι.toRingHom.toAlgebra
    have : IsScalarTower E Ω (Kbar w) := IsScalarTower.of_algebraMap_eq fun x => (ι.commutes x).symm
    let ta : Kbar w →ₐ[E] Kbar w := g.toAlgHom.restrictScalars E
    let σ : Ω ≃ₐ[E] Ω := ta.restrictNormal' Ω
    have hσ : ∀ x, g (ι x) = ι (σ x) := fun x => (ta.restrictNormal_commutes Ω x).symm
    refine ⟨σ, ?_, hσ⟩
    rw [mem_Dec]
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, hA, hA, ← hnorm g, hσ]
    simp
  choose r hr hr' using hres
  let ρ : GalLoc w →* Dec (F := E) A := MonoidHom.mk' (fun g => ⟨r g, hr g⟩) fun g g' => by
    apply Subtype.ext
    apply AlgEquiv.ext
    intro x
    apply ι.toRingHom.injective
    change ι (r (g * g') x) = ι (r g (r g' x))
    rw [← hr', ← hr', ← hr']
    rfl
  have hρ : ∀ (g : GalLoc w) (x : Ω), g (ι x) = ι ((ρ g : Ω ≃ₐ[E] Ω) x) := hr'
  have hinj : Function.Injective ρ := fun g g' hgg => by
    have := hd.equalizer (hcont g) (hcont g') (funext fun x => by simp only [Function.comp_apply]; rw [hρ, hρ, hgg])
    exact AlgEquiv.ext (congrFun this)

  obtain ⟨x₀, hx₀, hx₀'⟩ : ∃ x₀ : E, 0 < ‖ι (algebraMap E Ω x₀)‖ ∧ ‖ι (algebraMap E Ω x₀)‖ < 1 := by
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
    have hn : ∀ y : E, ‖ι (algebraMap E Ω y)‖ = ‖algebraMap E (w.adicCompletion E) y‖ := fun y => by
      rw [AlgHom.commutes, IsScalarTower.algebraMap_apply E (w.adicCompletion E) (Kbar w)]
      exact spectralNorm_extends _
    have hv : ∀ y : E, Valued.v (algebraMap E (w.adicCompletion E) y) = w.valuation E y := fun y => by
      first | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w y | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation w y | simp | rfl
    refine ⟨(a : E), ?_, ?_⟩
    · rw [hn, norm_pos_iff, map_ne_zero]
      exact_mod_cast ha0
    · rw [hn, Valued.toNormedField.norm_lt_one_iff, hv]
      exact (HeightOneSpectrum.valuation_lt_one_iff_mem w a).2 ha
  have hsurj : Function.Surjective ρ := fun σ => by
    let j' : Ω →ₐ[E] Kbar w := ι.comp (σ : Ω ≃ₐ[E] Ω).toAlgHom
    have hj' : ∀ x, ‖j' x‖ = ‖ι x‖ := norm_eq_of_le_one_iff ι.toRingHom j'.toRingHom
      (fun x => by
        change ‖ι x‖ ≤ 1 ↔ ‖ι ((σ : Ω ≃ₐ[E] Ω) x)‖ ≤ 1
        rw [← hA, ← hA, apply_mem_iff_of_mem_Dec σ.2])
      (algebraMap E Ω x₀) (by
        change ‖ι ((σ : Ω ≃ₐ[E] Ω) (algebraMap E Ω x₀))‖ = _
        rw [AlgEquiv.commutes]; rfl) hx₀ hx₀'
    obtain ⟨τ, hτ⟩ := exists_algEquiv_of_norm_eq (w.adicCompletion E) E Ω hdE ι j' hd hj'
    refine ⟨τ, Subtype.ext (AlgEquiv.ext fun x => ι.toRingHom.injective ?_)⟩
    change ι ((ρ τ : Ω ≃ₐ[E] Ω) x) = ι ((σ : Ω ≃ₐ[E] Ω) x)
    rw [← hρ, hτ]
    rfl
  have hc : Continuous ρ := by
    refine continuous_induced_rng.2 ?_
    refine continuous_of_continuousAt_one ((Dec (F := E) A).subtype.comp ρ) ?_
    intro s hs
    rw [map_one, krullTopology_mem_nhds_one_iff] at hs
    obtain ⟨L, hL, hsub⟩ := hs
    let b := Module.finBasis E L
    have hi : ∀ i, ∀ᶠ g : GalLoc w in nhds 1, g (ι (b i)) = ι (b i) := fun i =>
      (stabilizer_isOpen_of_isIntegral (K := w.adicCompletion E) (ι (b i))).mem_nhds
        (show (1 : GalLoc w) • ι (b i) = ι (b i) from rfl)
    rw [Filter.mem_map]
    filter_upwards [Filter.eventually_all.2 hi] with g hg
    apply hsub
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have : ((ρ g : Ω ≃ₐ[E] Ω).toLinearMap.comp L.val.toLinearMap) = L.val.toLinearMap :=
      b.ext fun i => ι.toRingHom.injective ((hρ g _).symm.trans (hg i))
    exact LinearMap.congr_fun this ⟨x, hx⟩
  let e := MulEquiv.ofBijective ρ ⟨hinj, hsurj⟩
  refine ⟨e.symm, Continuous.continuous_symm_of_equiv_compact_to_t2 (f := e.toEquiv) hc, hc,
    fun σ x => ?_⟩
  rw [hρ]
  exact congrArg (fun σ : Dec (F := E) A => ι ((σ : Ω ≃ₐ[E] Ω) x)) (e.apply_symm_apply σ)

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ A w h ι hι` and use `exists_mulEquiv_galLoc A w h ι hι`.
-/
theorem decomposition_mulEquiv_galLoc : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (ι : Ω →ₐ[E] Kbar w), IsLocEmb A w ι → ∃ θ : Dec (F := E) A ≃* GalLoc w, Continuous θ ∧ Continuous θ.symm ∧ ∀ σ : Dec (F := E) A, Lifts ι (θ σ) (σ : G E Ω) :=
  fun _ _ _ _ _ _ _ A w h ι hι => exists_mulEquiv_galLoc A w h ι hι

end GlobalTheory.LocDec
