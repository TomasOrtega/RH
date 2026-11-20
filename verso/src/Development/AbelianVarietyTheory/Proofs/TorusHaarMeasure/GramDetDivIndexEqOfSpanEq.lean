import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.GramDetMul
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Establish `h1 : ∀ a, ∃ c : ι → E, ∑ b, c b • w b = w' a` using `fun a => (Submodule.mem_span_range_iff_exists_fun E).1 (h ▸ Submodule.subset_span (Set.mem_range_self a))`. Use `choose B hB using h1`. Take `⟨c, hc⟩` from `IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 E)) (fun p : ι × ι => B p.1 p.2)`. Establish `hc' : ∀ a b, ∃ y : 𝓞 E, (y : E) = ((c : 𝓞 E) : E) * B a b`. Introduce `a b`.

Take `⟨y, hy⟩` from `hc (a, b)`. Use `⟨y, ?_⟩` and prove the remaining obligations. Establish `: (y : E) = algebraMap (𝓞 E) E y` using `rfl`. Rewrite using `[this, hy, Algebra.smul_def]`. Use `choose A hA using hc'`.

Establish `hc0 : (c : 𝓞 E) ≠ 0` using `nonZeroDivisors.coe_ne_zero c`. Establish `hcE : ((c : 𝓞 E) : E) ≠ 0`. Simplify using the standard rewrite rules. Establish `key : ∀ a, ∑ b, ((A a b : 𝓞 E) : E) • w b = ((c : 𝓞 E) : E) • w' a`. Introduce `a`.

Rewrite using `[← hB a, Finset.smul_sum]`. Conclude with `Finset.sum_congr rfl fun b _ => by rw [hA, mul_smul]`. Use `⟨Matrix.of fun b a => A a b, Matrix.diagonal fun _ => (c : 𝓞 E), ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `h0`. Take `⟨v, hv0, hv⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 h0`.

Apply `hv0` to reduce the goal to its premises. Establish `h2 : ∑ a, (((v a : 𝓞 E) : E) * ((c : 𝓞 E) : E)) • w' a = 0`. Establish `: ∀ a, (((v a : 𝓞 E) : E) * ((c : 𝓞 E) : E)) • w' a = ∑ b, (((A a b * v a : 𝓞 E)) : E) • w b`. Introduce `a`. Rewrite using `[mul_smul, ← key, Finset.smul_sum]`.

Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_smul, mul_comm]`. Simplify using the standard rewrite rules. Rewrite using `[Finset.sum_congr rfl fun a _ => this a, Finset.sum_comm]`. Use `Finset.sum_eq_zero fun b _ => ?_` and prove the remaining obligations.

Rewrite using `[← Finset.sum_smul]`. Establish `hb : ∑ a, A a b * v a = 0`. Use `congrFun hv b` as an intermediate fact. Simplify `this` using `[Matrix.mulVec, dotProduct]`. Establish `hb' : ∑ a, (((A a b * v a : 𝓞 E)) : E) = 0`.

Use `congrArg (algebraMap (𝓞 E) E) hb` as an intermediate fact. Rewrite `this` using `[map_sum, map_zero]`. Conclude with `this`. Rewrite using `[hb', zero_smul]`. Use function extensionality and compare the values at `a`.

Establish `h3` using `Fintype.linearIndependent_iff.1 hw' _ h2 a`. Establish `h4 : ((v a : 𝓞 E) : E) = 0` using `(mul_eq_zero.1 h3).resolve_right hcE`. Simplify using `using h4`. Rewrite using `[Matrix.det_diagonal]`. Conclude with `Finset.prod_ne_zero_iff.2 fun _ _ => hc0`.

Use function extensionality and compare the values at `a`. Simplify using `only [Matrix.of_apply]`. Rewrite using `[key, Finset.sum_eq_single a]`. Simplify using the standard rewrite rules. Introduce `b _ hb`.

Simplify using `[Matrix.diagonal_apply_ne _ hb]`. Simplify using the standard rewrite rules.
-/
theorem exists_common_integral_refinement {V ι : Type} [AddCommGroup V] [Module E V]
    [Fintype ι] [DecidableEq ι] (w w' : ι → V) (hw' : LinearIndependent E w')
    (h : Submodule.span E (Set.range w) = Submodule.span E (Set.range w')) :
    ∃ A A' : Matrix ι ι (𝓞 E), A.det ≠ 0 ∧ A'.det ≠ 0 ∧
      (fun a => ∑ b, ((A b a : 𝓞 E) : E) • w b) = (fun a => ∑ b, ((A' b a : 𝓞 E) : E) • w' b) := by
  have h1 : ∀ a, ∃ c : ι → E, ∑ b, c b • w b = w' a := fun a =>
    (Submodule.mem_span_range_iff_exists_fun E).1
      (h ▸ Submodule.subset_span (Set.mem_range_self a))
  choose B hB using h1
  obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 E))
    (fun p : ι × ι => B p.1 p.2)
  have hc' : ∀ a b, ∃ y : 𝓞 E, (y : E) = ((c : 𝓞 E) : E) * B a b := by
    intro a b
    obtain ⟨y, hy⟩ := hc (a, b)
    refine ⟨y, ?_⟩
    have : (y : E) = algebraMap (𝓞 E) E y := rfl
    rw [this, hy, Algebra.smul_def]
  choose A hA using hc'
  have hc0 : (c : 𝓞 E) ≠ 0 := nonZeroDivisors.coe_ne_zero c
  have hcE : ((c : 𝓞 E) : E) ≠ 0 := by
    simp
  have key : ∀ a, ∑ b, ((A a b : 𝓞 E) : E) • w b = ((c : 𝓞 E) : E) • w' a := by
    intro a
    rw [← hB a, Finset.smul_sum]
    exact Finset.sum_congr rfl fun b _ => by rw [hA, mul_smul]
  refine ⟨Matrix.of fun b a => A a b, Matrix.diagonal fun _ => (c : 𝓞 E), ?_, ?_, ?_⟩
  · intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    apply hv0
    have h2 : ∑ a, (((v a : 𝓞 E) : E) * ((c : 𝓞 E) : E)) • w' a = 0 := by
      have : ∀ a, (((v a : 𝓞 E) : E) * ((c : 𝓞 E) : E)) • w' a
          = ∑ b, (((A a b * v a : 𝓞 E)) : E) • w b := by
        intro a
        rw [mul_smul, ← key, Finset.smul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [← mul_smul, mul_comm]
        simp
      rw [Finset.sum_congr rfl fun a _ => this a, Finset.sum_comm]
      refine Finset.sum_eq_zero fun b _ => ?_
      rw [← Finset.sum_smul]
      have hb : ∑ a, A a b * v a = 0 := by
        have := congrFun hv b
        simpa [Matrix.mulVec, dotProduct] using this
      have hb' : ∑ a, (((A a b * v a : 𝓞 E)) : E) = 0 := by
        have := congrArg (algebraMap (𝓞 E) E) hb
        rw [map_sum, map_zero] at this
        exact this
      rw [hb', zero_smul]
    funext a
    have h3 := Fintype.linearIndependent_iff.1 hw' _ h2 a
    have h4 : ((v a : 𝓞 E) : E) = 0 := (mul_eq_zero.1 h3).resolve_right hcE
    simpa using h4
  · rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun _ _ => hc0
  · funext a
    simp only [Matrix.of_apply]
    rw [key, Finset.sum_eq_single a]
    · simp
    · intro b _ hb
      simp [Matrix.diagonal_apply_ne _ hb]
    · simp

/- English proof (translation)
Introduce `r X x ι _ _ w w' hw hΛ hw' hΛ' h`. Take `⟨A, A', hA, hA', he⟩` from `exists_common_integral_refinement w w' hw' h`. Establish `h1` using `GlobalTheory.ValMul.value_mul_eq r X x ι w hw hΛ A hA`. Establish `h2` using `GlobalTheory.ValMul.value_mul_eq r X x ι w' hw' hΛ' A' hA'`. Rewrite using `[← h1, ← h2, he]`.
-/
theorem gram_div_index_eq_of_span_eq [IsCMField E] : (∀ (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) (ι : Type) [Fintype ι] [DecidableEq ι] (w w' : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → LinearIndependent E w' → (∀ a, w' a ∈ X.Λ) → Submodule.span E (Set.range w) = Submodule.span E (Set.range w') → ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w' a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w' a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w')).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w')).toAddSubgroup)) : ℝ))) := by
  intro r X x ι _ _ w w' hw hΛ hw' hΛ' h
  obtain ⟨A, A', hA, hA', he⟩ := exists_common_integral_refinement w w' hw' h
  have h1 := GlobalTheory.ValMul.value_mul_eq r X x ι w hw hΛ A hA
  have h2 := GlobalTheory.ValMul.value_mul_eq r X x ι w' hw' hΛ' A' hA'
  rw [← h1, ← h2, he]

end GlobalTheory
