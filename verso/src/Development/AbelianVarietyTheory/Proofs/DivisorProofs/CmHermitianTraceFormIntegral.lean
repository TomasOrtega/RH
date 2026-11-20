import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsHolFormConst
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
open NumberField GlobalTheory.CMVal GlobalTheory.RealMult

namespace GlobalTheory.PolGen

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Assume the negation of the conclusion as `hD`. Establish `halg : IsAlgebraic ℤ D⁻¹` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic _)`. Take `⟨m, hm, hint⟩` from `halg.exists_integral_multiple`. Establish `h1 : Algebra.trace ℚ F ((m • D⁻¹) * D) = 0` using `h ⟨m • D⁻¹, hint⟩`. Establish `e : (m • D⁻¹) * D = algebraMap ℚ F (m : ℚ)`.

Rewrite using `[zsmul_eq_mul, mul_assoc, inv_mul_cancel₀ hD]`. Simplify using the standard rewrite rules. Rewrite `h1` using `[e, Algebra.trace_algebraMap, nsmul_eq_mul]`. Establish `h2 : (Module.finrank ℚ F : ℚ) ≠ 0` using `by exact_mod_cast Module.finrank_pos.ne'`. Establish `h3 : (m : ℚ) ≠ 0` using `by exact_mod_cast hm`.

Conclude with `mul_ne_zero h2 h3 h1`.
-/
theorem eq_zero_of_trace {F : Type} [Field F] [NumberField F] (D : F)
    (h : ∀ a : 𝓞 F, Algebra.trace ℚ F ((a : F) * D) = 0) : D = 0 := by
  by_contra hD
  have halg : IsAlgebraic ℤ D⁻¹ :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic _)
  obtain ⟨m, hm, hint⟩ := halg.exists_integral_multiple
  have h1 : Algebra.trace ℚ F ((m • D⁻¹) * D) = 0 := h ⟨m • D⁻¹, hint⟩
  have e : (m • D⁻¹) * D = algebraMap ℚ F (m : ℚ) := by
    rw [zsmul_eq_mul, mul_assoc, inv_mul_cancel₀ hD]; simp
  rw [e, Algebra.trace_algebraMap, nsmul_eq_mul] at h1
  have h2 : (Module.finrank ℚ F : ℚ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  have h3 : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  exact mul_ne_zero h2 h3 h1

omit [IsCMField E] in

/- English proof (translation)
Rewrite using `[← Algebra.trace_trace (S := maximalRealSubfield E)]`. Use `congr 1`. Rewrite using `[← smul_eq_mul k, ← map_smul]`. Both sides reduce to the same expression.
-/
theorem trace_coe_mul (k : maximalRealSubfield E) (w : E) :
    Algebra.trace ℚ E ((k : E) * w) =
      Algebra.trace ℚ (maximalRealSubfield E) (k * Algebra.trace (maximalRealSubfield E) E w) := by
  rw [← Algebra.trace_trace (S := maximalRealSubfield E)]
  congr 1
  rw [← smul_eq_mul k, ← map_smul]
  rfl

/- English proof (translation)
Introduce `E _ _ _ L 𝔠 mu c1 Q l c₀ h1 h2 h3 h4 h5 h6 h7`. Establish `hL : ∀ (a : OF E), ∀ x ∈ L, algebraMap (OF E) E a * x ∈ L` using `fun a x hx => by`. Rewrite using `[← Algebra.smul_def]`. Conclude with `L.smul_mem a hx`. Establish `hcoe : ∀ a : OF E, algebraMap (OF E) E a = ((a : maximalRealSubfield E) : E)` using `fun a => rfl`.

Establish `hc0 : (𝔠 : FractionalIdeal (nonZeroDivisors (𝓞 (maximalRealSubfield E))) (maximalRealSubfield E)) ≠ 0` using `𝔠.ne_zero`. Establish `hd0 : dualLat 𝔠 ≠ 0` using `FractionalIdeal.dual_ne_zero ℤ ℚ hc0`. Establish `key : ∀ x ∈ L, ∀ x' ∈ L, Algebra.trace (maximalRealSubfield E) E (mu * x * IsCMField.complexConj E x') = 2 * c1 * Q x x'`. Introduce `x hx x' hx'`. Rewrite using `[← sub_eq_zero]`.

Apply `eq_zero_of_trace` to reduce the goal to its premises. Introduce `a`. Establish `h` using `h4 _ (hL a x hx) x' hx'`. Rewrite `h` using `[h3 a x hx x' hx']`. Establish `e : mu * (algebraMap (OF E) E a * x) * IsCMField.complexConj E x' = ((a : maximalRealSubfield E) : E) * (mu * x * IsCMField.complexConj E x')`.

Rewrite using `[hcoe]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h` using `[e, trace_coe_mul]`. Establish `e2 : (a : maximalRealSubfield E) * (2 * c1 * Q x x') = c1 * (a * Q x x') + c1 * (a * Q x x')` using `by ring`. Rewrite using `[mul_sub, map_sub, h, e2, map_add]`.

Expand and normalize the polynomial expressions, which then agree. Establish `key2 : ∀ (k : maximalRealSubfield E), ∀ x ∈ L, ∀ x' ∈ L, Algebra.trace ℚ E ((k : E) * mu * x * IsCMField.complexConj E x') = Algebra.trace ℚ (maximalRealSubfield E) (k * (2 * c1 * Q x x'))`. Introduce `k x hx x' hx'`. Rewrite using `[← key x hx x' hx', ← trace_coe_mul]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Establish `h2c : (2 * c1 : maximalRealSubfield E) ≠ 0` using `mul_ne_zero two_ne_zero h1`. Establish `hmu : mu ≠ 0`. Introduce and unpack `rfl`. Apply `hd0` to reduce the goal to its premises.

Rewrite using `[FractionalIdeal.eq_zero_iff]`. Introduce `t ht`. Establish `h` using `h6 t ht`. Establish `hle : Submodule.span (𝓞 (maximalRealSubfield E)) {t | ∃ x ∈ L, ∃ x' ∈ L, t = Q x x'} ≤ ⊥`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨x, hx, x', hx', rfl⟩`. Use `key x hx x' hx'` as an intermediate fact. Rewrite `this` using `[zero_mul, zero_mul, map_zero]`. Conclude with `(mul_eq_zero.1 this.symm).resolve_left h2c`. Conclude with `hle h`.

Establish `hfix : ∀ k : maximalRealSubfield E, IsCMField.complexConj E (k : E) = k` using `fun k => (IsCMField.complexConj E).commutes k`. Use `⟨hmu, ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Use `show IsCMField.complexConj E _ = _`. Rewrite using `[map_mul, hfix, h2]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `x hx x' hx'`. Take `⟨n, hn⟩` from `(FractionalIdeal.mem_dual hc0).1 (h5 x hx x' hx') c₀ c₀.2`. Use `⟨n, ?_⟩` and prove the remaining obligations. Use `(key2 _ x hx x' hx').trans ?_` and prove the remaining obligations. Rewrite `hn` using `[Algebra.traceForm_apply]`.

Establish `e : (c₀ : maximalRealSubfield E) / (2 * c1) * (2 * c1 * Q x x') = Q x x' * c₀`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e, ← hn]`. Simplify using the standard rewrite rules. Introduce and unpack `ν ⟨hν1, hν2⟩`.

Establish `hs : IsCMField.complexConj E (ν / mu) = ν / mu`. Establish `hν1' : IsCMField.complexConj E ν = -ν` using `hν1`. Rewrite using `[map_div₀, hν1', h2, neg_div_neg_eq]`. Set `s : maximalRealSubfield E` to `⟨ν / mu, (IsCMField.complexConj_eq_self_iff E _).1 hs⟩`. Establish `hνs : ν = (s : E) * mu` using `by show ν = ν / mu * mu`.

Clear the denominators using the available nonvanishing facts. Establish `hmem : 2 * c1 * s ∈ (𝔠 : FractionalIdeal (nonZeroDivisors (𝓞 (maximalRealSubfield E))) (maximalRealSubfield E))`. Rewrite using `[← FractionalIdeal.dual_dual ℤ ℚ (𝔠 : FractionalIdeal (nonZeroDivisors (𝓞 (maximalRealSubfield E))) (maximalRealSubfield E))]`. Use `(FractionalIdeal.mem_dual hd0).2 ?_` and prove the remaining obligations. Introduce `t ht`.

Establish `h : ∀ a : OF E, Algebra.trace ℚ (maximalRealSubfield E) (2 * c1 * s * (a * t)) ∈ (algebraMap ℤ ℚ).range`. Establish `h` using `h6 t ht`. Use `clear ht`. Proceed by induction on `h using Submodule.span_induction with`. Consider the case `mem t ht`.

Take `⟨x, hx, x', hx', rfl⟩` from `ht`. Introduce `a`. Take `⟨n, hn⟩` from `hν2 _ (hL a x hx) x' hx'`. Use `⟨n, ?_⟩` and prove the remaining obligations. Rewrite `hn` using `[hνs]`.

Establish `h` using `(key2 s _ (hL a x hx) x' hx').symm.trans hn`. Rewrite `h` using `[h3 a x hx x' hx']`. Establish `e : 2 * c1 * s * (a * Q x x') = s * (2 * c1 * (a * Q x x'))` using `by ring`. Rewrite using `[e, h]`. Simplify using the standard rewrite rules.

Consider the case `zero => intro a`. Simplify using the standard rewrite rules. Consider the case `add t u _ _ ht hu`. Introduce `a`. Rewrite using `[mul_add, mul_add, map_add]`.

Conclude with `add_mem (ht a) (hu a)`. Consider the case `smul b t _ ht`. Introduce `a`. Establish `e : (a : maximalRealSubfield E) * b • t = ((a * b : OF E) : maximalRealSubfield E) * t`. Rewrite using `[Algebra.smul_def, ← mul_assoc]`.

Use `congr 1`. Rewrite using `[e]`. Conclude with `ht _`. Use `h 1` as an intermediate fact. Rewrite using `[Algebra.traceForm_apply]`.

Simplify using `using this`. Take `⟨n, t, hn, hnt⟩` from `h7 ⟨2 * c1 * s, hmem⟩`. Use `⟨n, hn, t, ?_⟩` and prove the remaining obligations. Establish `e : (n : maximalRealSubfield E) * (2 * c1 * s) = (t : maximalRealSubfield E) * c₀`. Use `congrArg Subtype.val hnt` as an intermediate fact.

Simplify `this` using `[nsmul_eq_mul, Algebra.smul_def]`. Establish `e2 : (n : maximalRealSubfield E) * s = (t : maximalRealSubfield E) * (c₀ / (2 * c1))`. Rewrite using `[mul_div_assoc', ← e]`. Clear the denominators using the available nonvanishing facts. Establish `e3` using `congrArg (fun z : maximalRealSubfield E => (z : E)) e2`.

Simplify using `only [Subfield.coe_mul, SubringClass.coe_natCast] at e3`. Rewrite using `[hcoe, hνs, ← mul_assoc, ← mul_assoc, e3]`.
-/
theorem genAt_polMod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (L : Submodule (OF E) E) (𝔠 : FracId (maximalRealSubfield E))
    (mu : E) (c1 : maximalRealSubfield E) (Q : E → E → maximalRealSubfield E) (l : ℕ) (c₀ : 𝔠.elt), c1 ≠ 0 →
    IsCMField.complexConj E mu = -mu →
    (∀ (a : OF E), ∀ x ∈ L, ∀ x' ∈ L, Q (algebraMap (OF E) E a * x) x' = (a : maximalRealSubfield E) * Q x x') →
    (∀ x ∈ L, ∀ x' ∈ L, Algebra.trace ℚ E (mu * x * IsCMField.complexConj E x') =
      2 * Algebra.trace ℚ (maximalRealSubfield E) (c1 * Q x x')) →
    (∀ x ∈ L, ∀ x' ∈ L, Q x x' ∈ dualLat 𝔠) →
    (∀ t ∈ dualLat 𝔠, t ∈ Submodule.span (𝓞 (maximalRealSubfield E)) {t | ∃ x ∈ L, ∃ x' ∈ L, t = Q x x'}) →
    (∀ c : 𝔠.elt, ∃ (n : ℕ) (t : 𝓞 (maximalRealSubfield E)), n.Coprime l ∧ n • c = t • c₀) →
    mu ≠ 0 ∧ GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.GenAt l (GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.polMod L)
      ((((c₀ : maximalRealSubfield E) / (2 * c1) : maximalRealSubfield E) : E) * mu) := by
  intro E _ _ _ L 𝔠 mu c1 Q l c₀ h1 h2 h3 h4 h5 h6 h7
  have hL : ∀ (a : OF E), ∀ x ∈ L, algebraMap (OF E) E a * x ∈ L := fun a x hx => by
    rw [← Algebra.smul_def]; exact L.smul_mem a hx
  have hcoe : ∀ a : OF E, algebraMap (OF E) E a = ((a : maximalRealSubfield E) : E) := fun a => rfl
  have hc0 : (𝔠 : FractionalIdeal (nonZeroDivisors (𝓞 (maximalRealSubfield E))) (maximalRealSubfield E)) ≠ 0 :=
    𝔠.ne_zero
  have hd0 : dualLat 𝔠 ≠ 0 := FractionalIdeal.dual_ne_zero ℤ ℚ hc0
  have key : ∀ x ∈ L, ∀ x' ∈ L, Algebra.trace (maximalRealSubfield E) E (mu * x * IsCMField.complexConj E x') =
      2 * c1 * Q x x' := by
    intro x hx x' hx'
    rw [← sub_eq_zero]
    apply eq_zero_of_trace
    intro a
    have h := h4 _ (hL a x hx) x' hx'
    rw [h3 a x hx x' hx'] at h
    have e : mu * (algebraMap (OF E) E a * x) * IsCMField.complexConj E x' =
        ((a : maximalRealSubfield E) : E) * (mu * x * IsCMField.complexConj E x') := by
      rw [hcoe]; ring
    rw [e, trace_coe_mul] at h
    have e2 : (a : maximalRealSubfield E) * (2 * c1 * Q x x') =
        c1 * (a * Q x x') + c1 * (a * Q x x') := by ring
    rw [mul_sub, map_sub, h, e2, map_add]; ring
  have key2 : ∀ (k : maximalRealSubfield E), ∀ x ∈ L, ∀ x' ∈ L,
      Algebra.trace ℚ E ((k : E) * mu * x * IsCMField.complexConj E x') =
        Algebra.trace ℚ (maximalRealSubfield E) (k * (2 * c1 * Q x x')) := by
    intro k x hx x' hx'
    rw [← key x hx x' hx', ← trace_coe_mul]
    congr 1; ring
  have h2c : (2 * c1 : maximalRealSubfield E) ≠ 0 := mul_ne_zero two_ne_zero h1
  have hmu : mu ≠ 0 := by
    rintro rfl
    apply hd0
    rw [FractionalIdeal.eq_zero_iff]
    intro t ht
    have h := h6 t ht
    have hle : Submodule.span (𝓞 (maximalRealSubfield E)) {t | ∃ x ∈ L, ∃ x' ∈ L, t = Q x x'} ≤ ⊥ := by
      rw [Submodule.span_le]
      rintro _ ⟨x, hx, x', hx', rfl⟩
      have := key x hx x' hx'
      rw [zero_mul, zero_mul, map_zero] at this
      exact (mul_eq_zero.1 this.symm).resolve_left h2c
    exact hle h
  have hfix : ∀ k : maximalRealSubfield E, IsCMField.complexConj E (k : E) = k := fun k =>
    (IsCMField.complexConj E).commutes k
  refine ⟨hmu, ⟨?_, ?_⟩, ?_⟩
  · show IsCMField.complexConj E _ = _
    rw [map_mul, hfix, h2]; ring
  · intro x hx x' hx'
    obtain ⟨n, hn⟩ := (FractionalIdeal.mem_dual hc0).1 (h5 x hx x' hx') c₀ c₀.2
    refine ⟨n, ?_⟩
    refine (key2 _ x hx x' hx').trans ?_
    rw [Algebra.traceForm_apply] at hn
    have e : (c₀ : maximalRealSubfield E) / (2 * c1) * (2 * c1 * Q x x') = Q x x' * c₀ := by
      field_simp
    rw [e, ← hn]; simp
  · rintro ν ⟨hν1, hν2⟩
    have hs : IsCMField.complexConj E (ν / mu) = ν / mu := by
      have hν1' : IsCMField.complexConj E ν = -ν := hν1
      rw [map_div₀, hν1', h2, neg_div_neg_eq]
    let s : maximalRealSubfield E := ⟨ν / mu, (IsCMField.complexConj_eq_self_iff E _).1 hs⟩
    have hνs : ν = (s : E) * mu := by
      show ν = ν / mu * mu
      field_simp
    have hmem : 2 * c1 * s ∈ (𝔠 : FractionalIdeal (nonZeroDivisors (𝓞 (maximalRealSubfield E))) (maximalRealSubfield E)) := by
      rw [← FractionalIdeal.dual_dual ℤ ℚ (𝔠 : FractionalIdeal (nonZeroDivisors (𝓞 (maximalRealSubfield E))) (maximalRealSubfield E))]
      refine (FractionalIdeal.mem_dual hd0).2 ?_
      intro t ht
      have h : ∀ a : OF E, Algebra.trace ℚ (maximalRealSubfield E) (2 * c1 * s * (a * t)) ∈ (algebraMap ℤ ℚ).range := by
        have h := h6 t ht
        clear ht
        induction h using Submodule.span_induction with
        | mem t ht =>
          obtain ⟨x, hx, x', hx', rfl⟩ := ht
          intro a
          obtain ⟨n, hn⟩ := hν2 _ (hL a x hx) x' hx'
          refine ⟨n, ?_⟩
          rw [hνs] at hn
          have h := (key2 s _ (hL a x hx) x' hx').symm.trans hn
          rw [h3 a x hx x' hx'] at h
          have e : 2 * c1 * s * (a * Q x x') = s * (2 * c1 * (a * Q x x')) := by ring
          rw [e, h]; simp
        | zero => intro a; simp
        | add t u _ _ ht hu =>
          intro a
          rw [mul_add, mul_add, map_add]
          exact add_mem (ht a) (hu a)
        | smul b t _ ht =>
          intro a
          have e : (a : maximalRealSubfield E) * b • t = ((a * b : OF E) : maximalRealSubfield E) * t := by
            rw [Algebra.smul_def, ← mul_assoc]
            congr 1
          rw [e]; exact ht _
      have := h 1
      rw [Algebra.traceForm_apply]
      simpa using this
    obtain ⟨n, t, hn, hnt⟩ := h7 ⟨2 * c1 * s, hmem⟩
    refine ⟨n, hn, t, ?_⟩
    have e : (n : maximalRealSubfield E) * (2 * c1 * s) = (t : maximalRealSubfield E) * c₀ := by
      have := congrArg Subtype.val hnt
      simpa [nsmul_eq_mul, Algebra.smul_def] using this
    have e2 : (n : maximalRealSubfield E) * s = (t : maximalRealSubfield E) * (c₀ / (2 * c1)) := by
      rw [mul_div_assoc', ← e]; field_simp
    have e3 := congrArg (fun z : maximalRealSubfield E => (z : E)) e2
    simp only [Subfield.coe_mul, SubringClass.coe_natCast] at e3
    rw [hcoe, hνs, ← mul_assoc, ← mul_assoc, e3]

end GlobalTheory.PolGen
