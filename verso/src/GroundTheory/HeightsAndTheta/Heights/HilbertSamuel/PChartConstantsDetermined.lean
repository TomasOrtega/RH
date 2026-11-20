import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChartConstantsDetermined
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry NumberField

namespace ChartConstantsDetermined

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

/- English proof (translation)
Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem aeval_chart_eq (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (f : MRing ι) :
    aeval (fun p => y p / y ⟨p.1, c p.1⟩) f = eval (fun k => (y ⟨k, c k⟩)⁻¹) (mConeMap y f) := by
  have h := MvPolynomial.ringHom_ext
    (f := (aeval (fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) : MRing ι →ₐ[ℤ] Ω).toRingHom)
    (g := (eval (fun k => (y ⟨k, c k⟩)⁻¹)).comp (mConeMap y).toRingHom)
    (fun r => by simp) (fun p => by simp [mConeMap, div_eq_mul_inv])
  exact RingHom.congr_fun h f

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem aeval_chart_of_isMultiHomog (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) {f : MRing ι} {d : K → ℕ}
    (hf : IsMultiHomog f d) :
    aeval (fun p => y p / y ⟨p.1, c p.1⟩) f = aeval y f * ∏ k, (y ⟨k, c k⟩)⁻¹ ^ d k := by
  rw [aeval_chart_eq, ProjLine.mConeMap_eq_of_isMultiHomog y hf]
  simp only [map_mul, eval_C, map_prod, map_pow, eval_X]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem aeval_chart_eq_zero (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) {f : MRing ι} (hf : f ∈ mCoordIdeal y) :
    aeval (fun p => y p / y ⟨p.1, c p.1⟩) f = 0 := by
  rw [aeval_chart_eq, show mConeMap y f = 0 from RingHom.mem_ker.mp hf, map_zero]

variable (F : Type) [Field F] [NumberField F] [Algebra F Ω]

def chartCoord (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (p : Σ k, ι k) : ↥(chartRingZ y c ⊔ intsIn F Ω) :=
  ⟨y p / y ⟨p.1, c p.1⟩, le_sup_left (a := chartRingZ y c) (Algebra.subset_adjoin (Set.mem_range_self p))⟩

variable {F}

def pointOf (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (w : ↥(chartRingZ y c ⊔ intsIn F Ω) →+* ℂ) : (Σ k, ι k) → ℂ :=
  fun p => w (chartCoord F y c p)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem coe_aeval_chartCoord (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (f : MRing ι) :
    ((aeval (chartCoord F y c) f : ↥(chartRingZ y c ⊔ intsIn F Ω)) : Ω) =
      aeval (fun p => y p / y ⟨p.1, c p.1⟩) f := by
  show (Subalgebra.val _) (aeval (chartCoord F y c) f) = _
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem eval_pointOf (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (w : ↥(chartRingZ y c ⊔ intsIn F Ω) →+* ℂ)
    (f : MRing ι) :
    eval (pointOf y c w) (map (Int.castRingHom ℂ) f) = w (aeval (chartCoord F y c) f) := by
  rw [eval_map]
  have h := MvPolynomial.ringHom_ext (f := eval₂Hom (Int.castRingHom ℂ) (pointOf y c w))
    (g := w.comp (aeval (chartCoord F y c) : MRing ι →ₐ[ℤ] _).toRingHom)
    (fun r => by simp) (fun p => by simp [pointOf])
  exact RingHom.congr_fun h f

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Simplify using the standard rewrite rules.
-/
theorem pointOf_mem (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (w : ↥(chartRingZ y c ⊔ intsIn F Ω) →+* ℂ) : pointOf y c w ∈ mcPts (mCoordIdeal y) := by
  refine ⟨fun k => ⟨c k, ?_⟩, fun f hf => ?_⟩
  · have h1 : chartCoord F y c ⟨k, c k⟩ = 1 := Subtype.ext (by simp [chartCoord, hc k])
    simp [pointOf, h1]
  · rw [eval_pointOf]
    have h0 : aeval (chartCoord F y c) f = 0 :=
      Subtype.ext (by rw [coe_aeval_chartCoord]; simpa using aeval_chart_eq_zero y c hf)
    simp [h0]

def intsMap {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (w : ↥(chartRingZ y c ⊔ intsIn F Ω) →+* ℂ) : 𝓞 F →+* ℂ :=
  w.comp ((Subalgebra.inclusion (le_sup_right : intsIn F Ω ≤ chartRingZ y c ⊔ intsIn F Ω)).toRingHom.comp
    (((algebraMap F Ω).comp (algebraMap (𝓞 F) F)).toIntAlgHom.rangeRestrict).toRingHom)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem intsMap_apply {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (w : ↥(chartRingZ y c ⊔ intsIn F Ω) →+* ℂ) (a : 𝓞 F) :
    intsMap w a = w ⟨algebraMap F Ω (algebraMap (𝓞 F) F a),
      le_sup_right (a := chartRingZ y c) (AlgHom.mem_range_self _ a)⟩ := rfl

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts.
-/
theorem intsMap_injective {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (w : ↥(chartRingZ y c ⊔ intsIn F Ω) →+* ℂ) :
    Function.Injective (intsMap w) := by
  refine (RingHom.injective_iff_ker_eq_bot _).mpr (Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_)
  refine eq_bot_iff.2 fun n hn => ?_
  rw [Ideal.mem_bot]
  simpa [Ideal.mem_comap, RingHom.mem_ker] using hn

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Clear the denominators using the available nonvanishing facts.
-/
theorem liesOver_pointOf (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (w : ↥(chartRingZ y c ⊔ intsIn F Ω) →+* ℂ) :
    LiesOver y (IsFractionRing.lift (K := F) (intsMap_injective w)) (pointOf y c w) := by
  intro d g h θ hg hh hrel
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (𝓞 F) θ
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hψb : intsMap w b ≠ 0 := (map_ne_zero_iff _ (intsMap_injective w)).mpr hb0
  have hB : algebraMap F Ω (algebraMap (𝓞 F) F b) ≠ 0 := by simpa using hb0
  rw [map_div₀, IsFractionRing.lift_algebraMap, IsFractionRing.lift_algebraMap, eval_pointOf, eval_pointOf,
    div_mul_eq_mul_div, eq_div_iff hψb, intsMap_apply, intsMap_apply, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  simp only [MulMemClass.coe_mul, coe_aeval_chartCoord]
  rw [aeval_chart_of_isMultiHomog y c hg, aeval_chart_of_isMultiHomog y c hh, hrel, map_div₀]
  field_simp

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

By extensionality, compare the relevant components. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem proof : Statement := by
  intro K _ ι _ Ω _ F _ _ _ y hU c hc w w' hw
  have hz : pointOf y c w = pointOf y c w' := funext fun p =>
    RingHom.congr_fun hw ⟨y p / y ⟨p.1, c p.1⟩, Algebra.subset_adjoin (Set.mem_range_self p)⟩
  obtain ⟨sg, -, huniq⟩ := hU _ (pointOf_mem y c hc w)
  have e1 := huniq _ (liesOver_pointOf y c w)
  have e2 := huniq (IsFractionRing.lift (K := F) (intsMap_injective w'))
    (by rw [hz]; exact liesOver_pointOf y c w')
  ext x
  rcases x with ⟨_, a, rfl⟩
  show intsMap w a = intsMap w' a
  rw [← IsFractionRing.lift_algebraMap (K := F) (intsMap_injective w) a,
    ← IsFractionRing.lift_algebraMap (K := F) (intsMap_injective w') a, e1, e2]

end ChartConstantsDetermined

end GroundTheory.Heights₂.Heights.HilbertSamuel
