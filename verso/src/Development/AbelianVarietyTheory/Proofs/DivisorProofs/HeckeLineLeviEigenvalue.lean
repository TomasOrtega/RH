import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KStab
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.LeviLineDeriv

/- English proof (translation)
Use `set G : ℝ → ℂ := fun x => ∫ u in (0:ℝ)..x, f u with hG`. Establish `hGd : ∀ x, HasDerivAt G (f x) x` using `fun x => intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable _ _) hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt`. Establish `hne : ∀ᶠ x in 𝓝[≠] (0:ℝ), G x ≠ G 0` using `(hGd 0).eventually_ne (by rw [h0]; exact one_ne_zero)`. Take `⟨h, hh⟩` from `hne.exists`. Establish `hG0 : G 0 = 0` using `by simp [hG]`.

Rewrite `hh` using `[hG0]`. Establish `key : ∀ s, G (s + h) - G s = f s * G h`. Introduce `s`. Simplify using `only [hG]`. Rewrite using `[intervalIntegral.integral_interval_sub_left (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)]`.

Establish `h1` using `intervalIntegral.integral_comp_add_left (fun u => f u) s (a := 0) (b := h)`. Simplify using `only [add_zero] at h1`. Rewrite using `[← h1]`. Simplify using `only [hmul]`. Conclude with `intervalIntegral.integral_const_mul _ _`.

Establish `hd : HasDerivAt (fun s => (G (s + h) - G s) / G h) ((f (0 + h) - f 0) / G h) 0` using `(((hGd (0 + h)).comp_add_const 0 h).sub (hGd 0)).div_const (G h)`. Use `⟨_, hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)⟩` and prove the remaining obligations. Simplify using `only`. Rewrite using `[key s]`. Clear the denominators using the available nonvanishing facts.
-/
theorem hasDerivAt_zero_of_continuous_hom (f : ℝ → ℂ) (hf : Continuous f)
    (hmul : ∀ s u, f (s + u) = f s * f u) (h0 : f 0 = 1) : ∃ c : ℂ, HasDerivAt f c 0 := by
  set G : ℝ → ℂ := fun x => ∫ u in (0:ℝ)..x, f u with hG
  have hGd : ∀ x, HasDerivAt G (f x) x := fun x =>
    intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable _ _)
      hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  have hne : ∀ᶠ x in 𝓝[≠] (0:ℝ), G x ≠ G 0 := (hGd 0).eventually_ne (by rw [h0]; exact one_ne_zero)
  obtain ⟨h, hh⟩ := hne.exists
  have hG0 : G 0 = 0 := by simp [hG]
  rw [hG0] at hh
  have key : ∀ s, G (s + h) - G s = f s * G h := by
    intro s
    simp only [hG]
    rw [intervalIntegral.integral_interval_sub_left (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)]
    have h1 := intervalIntegral.integral_comp_add_left (fun u => f u) s (a := 0) (b := h)
    simp only [add_zero] at h1
    rw [← h1]
    simp only [hmul]
    exact intervalIntegral.integral_const_mul _ _
  have hd : HasDerivAt (fun s => (G (s + h) - G s) / G h) ((f (0 + h) - f 0) / G h) 0 :=
    (((hGd (0 + h)).comp_add_const 0 h).sub (hGd 0)).div_const (G h)
  refine ⟨_, hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)⟩
  simp only
  rw [key s]; field_simp

end GlobalTheory.LeviLineDeriv

namespace GlobalTheory.IndLine

open GlobalTheory.LeviLineDeriv in

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B d d₁ W W₁ H' i₀ i₁ hA χ hχ z γ hγ γ₁ t hL`. Use `haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens`. Use `set T : ℝ → (AE F E)ˣ := fun s => t (Multiplicative.ofAdd s) with hT`. Establish `hTadd : ∀ s u, T (s + u) = T s * T u` using `fun s u => by`. Simplify using `only [hT, ofAdd_add, map_mul]`.

Establish `hT0 : T 0 = 1` using `by simp only [hT, ofAdd_zero, map_one]`. Establish `hTneg : ∀ s, (T s)⁻¹ = T (-s)` using `fun s => by`. Rewrite using `[eq_comm, ← mul_eq_one_iff_eq_inv, ← hTadd, neg_add_cancel, hT0]`. Establish `hx : H'.x ≠ 0`. Introduce `h0`.

Use `hA.xy` as an intermediate fact. Rewrite `this` using `[h0]`. Simplify using `[form] at this`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, H'.x i ≠ 0 := by`. Assume the negation of the conclusion as `hc`.

Use `push_neg at hc`. Conclude with `hx (funext hc)`. Use `set u : (AE F E)ˣ := Units.map (inclR (F := F) (AF F)).toMonoidHom (Units.mk0 (H'.x i) hi) with hu`. Establish `hval : ∀ s, (T s : AE F E) = (mat (γ (Multiplicative.ofAdd s)) *ᵥ incV F H'.x) i * (u⁻¹ : (AE F E)ˣ)`. Introduce `s`.

Establish `h1` using `congrFun (hL (Multiplicative.ofAdd s)).1 i`. Rewrite using `[h1]`. Simplify using `only [Pi.smul_apply, smul_eq_mul, incV, hu, hT]`. Rewrite using `[mul_assoc]`. Establish `: inclR (F` using `F) (AF F) (H'.x i) * ((Units.map (inclR (F := F) (AF F)).toMonoidHom (Units.mk0 (H'.x i) hi))⁻¹ : (AE F E)ˣ) = 1 := by`.

Use `(Units.map (inclR (F := F) (AF F)).toMonoidHom (Units.mk0 (H'.x i) hi)).mul_inv` as an intermediate fact. Simplify using `using this`. Rewrite using `[this, mul_one]`. Establish `hcv : Continuous fun s : ℝ => (T s : AE F E)`. Repeatedly rewrite using `[hval]`.

Use `Continuous.mul ?_ continuous_const` and prove the remaining obligations. Establish `hg : Continuous fun s : ℝ => γ (Multiplicative.ofAdd s)` using `hγ.1.comp continuous_ofAdd`. Establish `hm : Continuous fun s : ℝ => mat (γ (Multiplicative.ofAdd s)) *ᵥ incV F H'.x` using `Continuous.matrix_mulVec (Units.continuous_val.comp (continuous_subtype_val.comp hg)) continuous_const`. Conclude with `(continuous_apply i).comp hm`. Establish `hcT : Continuous T`.

Use `Units.continuous_iff.2 ⟨hcv, ?_⟩` and prove the remaining obligations. Repeatedly rewrite using `[hTneg]`. Conclude with `hcv.comp continuous_neg`. Establish `hpos : ∀ s, (absE F E (T s) : ℝ) ≠ 0`. Introduce `s h`.

Establish `h2 : absE F E (T s) * absE F E (T (-s)) = 1`. Rewrite using `[← map_mul, ← hTadd, add_neg_cancel, hT0, map_one]`. Establish `h3 : absE F E (T s) = 0` using `by exact_mod_cast h`. Rewrite `h2` using `[h3, zero_mul]`. Conclude with `zero_ne_one h2`.

Use `set g : ℝ → ℂ := fun s => (χ (T s) : ℂ) * (((absE F E (T s) : ℝ) ^ z : ℝ) : ℂ) with hg`. Establish `hgc : Continuous g`. Use `Continuous.mul ?_ ?_` and prove the remaining obligations. Conclude with `continuous_subtype_val.comp (hχ.1.comp hcT)`. Use `Complex.continuous_ofReal.comp ?_` and prove the remaining obligations.

Conclude with `((NNReal.continuous_coe.comp (GlobalTheory.Doubling.continuous_absE.comp hcT)).rpow_const fun s => Or.inl (hpos s))`. Establish `hgm : ∀ s u, g (s + u) = g s * g u`. Introduce `s u`. Simplify using `only [hg, hTadd, map_mul, Circle.coe_mul, NNReal.coe_mul]`. Rewrite using `[Real.mul_rpow (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hg0 : g 0 = 1`. Simplify using `[hg, hT0]`. Conclude with `hasDerivAt_zero_of_continuous_hom g hgc hgm hg0`.
-/
theorem hasDerivAt_chi_abs_levi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ),
    H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ χ : Chr F E, IsHecke F E χ → ∀ z : ℝ, ∀ γ ∈ Lines σ W,
    ∀ (γ₁ : Multiplicative ℝ →* UA σ W₁.J) (t : Multiplicative ℝ →* (AE F E)ˣ), (∀ s, IsLevi H' (t s) (γ₁ s) (γ s)) →
      ∃ c : ℂ, HasDerivAt (fun s : ℝ => (χ (t (Multiplicative.ofAdd s)) : ℂ) *
        (((absE F E (t (Multiplicative.ofAdd s)) : ℝ) ^ z : ℝ) : ℂ)) c 0 := by
  intro F E _ _ _ _ _ σ B d d₁ W W₁ H' i₀ i₁ hA χ hχ z γ hγ γ₁ t hL
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  set T : ℝ → (AE F E)ˣ := fun s => t (Multiplicative.ofAdd s) with hT
  have hTadd : ∀ s u, T (s + u) = T s * T u := fun s u => by
    simp only [hT, ofAdd_add, map_mul]
  have hT0 : T 0 = 1 := by simp only [hT, ofAdd_zero, map_one]
  have hTneg : ∀ s, (T s)⁻¹ = T (-s) := fun s => by
    rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← hTadd, neg_add_cancel, hT0]

  have hx : H'.x ≠ 0 := by
    intro h0
    have := hA.xy
    rw [h0] at this
    simp [form] at this
  obtain ⟨i, hi⟩ : ∃ i, H'.x i ≠ 0 := by
    by_contra hc; push_neg at hc; exact hx (funext hc)
  set u : (AE F E)ˣ := Units.map (inclR (F := F) (AF F)).toMonoidHom (Units.mk0 (H'.x i) hi) with hu
  have hval : ∀ s, (T s : AE F E) = (mat (γ (Multiplicative.ofAdd s)) *ᵥ incV F H'.x) i * (u⁻¹ : (AE F E)ˣ) := by
    intro s
    have h1 := congrFun (hL (Multiplicative.ofAdd s)).1 i
    rw [h1]
    simp only [Pi.smul_apply, smul_eq_mul, incV, hu, hT]
    rw [mul_assoc]
    have : inclR (F := F) (AF F) (H'.x i) * ((Units.map (inclR (F := F) (AF F)).toMonoidHom
        (Units.mk0 (H'.x i) hi))⁻¹ : (AE F E)ˣ) = 1 := by
      have := (Units.map (inclR (F := F) (AF F)).toMonoidHom (Units.mk0 (H'.x i) hi)).mul_inv
      simpa using this
    rw [this, mul_one]
  have hcv : Continuous fun s : ℝ => (T s : AE F E) := by
    simp_rw [hval]
    refine Continuous.mul ?_ continuous_const
    have hg : Continuous fun s : ℝ => γ (Multiplicative.ofAdd s) := hγ.1.comp continuous_ofAdd
    have hm : Continuous fun s : ℝ => mat (γ (Multiplicative.ofAdd s)) *ᵥ incV F H'.x :=
      Continuous.matrix_mulVec (Units.continuous_val.comp (continuous_subtype_val.comp hg)) continuous_const
    exact (continuous_apply i).comp hm
  have hcT : Continuous T := by
    refine Units.continuous_iff.2 ⟨hcv, ?_⟩
    simp_rw [hTneg]
    exact hcv.comp continuous_neg
  have hpos : ∀ s, (absE F E (T s) : ℝ) ≠ 0 := by
    intro s h
    have h2 : absE F E (T s) * absE F E (T (-s)) = 1 := by
      rw [← map_mul, ← hTadd, add_neg_cancel, hT0, map_one]
    have h3 : absE F E (T s) = 0 := by exact_mod_cast h
    rw [h3, zero_mul] at h2
    exact zero_ne_one h2
  set g : ℝ → ℂ := fun s => (χ (T s) : ℂ) * (((absE F E (T s) : ℝ) ^ z : ℝ) : ℂ) with hg
  have hgc : Continuous g := by
    refine Continuous.mul ?_ ?_
    · exact continuous_subtype_val.comp (hχ.1.comp hcT)
    · refine Complex.continuous_ofReal.comp ?_
      exact ((NNReal.continuous_coe.comp (GlobalTheory.Doubling.continuous_absE.comp hcT)).rpow_const
        fun s => Or.inl (hpos s))
  have hgm : ∀ s u, g (s + u) = g s * g u := by
    intro s u
    simp only [hg, hTadd, map_mul, Circle.coe_mul, NNReal.coe_mul]
    rw [Real.mul_rpow (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)]
    push_cast
    ring
  have hg0 : g 0 = 1 := by
    simp [hg, hT0]
  exact hasDerivAt_zero_of_continuous_hom g hgc hgm hg0

end GlobalTheory.IndLine
