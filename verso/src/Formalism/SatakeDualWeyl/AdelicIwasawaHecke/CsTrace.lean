import Formalism.SatakeDualWeyl.DefsCS

noncomputable section

open NumberField

namespace Formalism.UG.P

/- English proof (translation)
Establish `key : algebraMap ℚ ℂ (Algebra.trace ℚ F b) = ∑ σ : F →ₐ[ℚ] ℂ, σ b` using `trace_eq_sum_embeddings ℂ`. Establish `hre : ∀ σ : F →ₐ[ℚ] ℂ, 0 < (σ b).re`. Introduce `σ`. Establish `hr : NumberField.ComplexEmbedding.IsReal (σ : F →+* ℂ)` using `NumberField.InfinitePlace.isReal_mk_iff.mp (IsTotallyReal.isReal _)`. Establish `e` using `hr.coe_embedding_apply b`.

Establish `e' : (σ : F →+* ℂ) b = σ b` using `rfl`. Rewrite using `[← e', ← e, Complex.ofReal_re]`. Conclude with `hb _`. Establish `hne : Nonempty (F →ₐ[ℚ] ℂ)` using `⟨IsAlgClosed.lift⟩`. Establish `h2` using `congrArg Complex.re key`.

Rewrite `h2` using `[Complex.re_sum]`. Establish `h3 : 0 < ∑ σ : F →ₐ[ℚ] ℂ, (σ b).re` using `Finset.sum_pos (fun σ _ => hre σ) Finset.univ_nonempty`. Rewrite `h3` using `[← h2]`. Simplify using `using h3`.
-/
theorem csTrace_trace_pos {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (b : F)
    (hb : ∀ ι : F →+* ℝ, 0 < ι b) : 0 < Algebra.trace ℚ F b := by
  have key : algebraMap ℚ ℂ (Algebra.trace ℚ F b) = ∑ σ : F →ₐ[ℚ] ℂ, σ b :=
    trace_eq_sum_embeddings ℂ
  have hre : ∀ σ : F →ₐ[ℚ] ℂ, 0 < (σ b).re := by
    intro σ
    have hr : NumberField.ComplexEmbedding.IsReal (σ : F →+* ℂ) :=
      NumberField.InfinitePlace.isReal_mk_iff.mp (IsTotallyReal.isReal _)
    have e := hr.coe_embedding_apply b
    have e' : (σ : F →+* ℂ) b = σ b := rfl
    rw [← e', ← e, Complex.ofReal_re]
    exact hb _
  have hne : Nonempty (F →ₐ[ℚ] ℂ) := ⟨IsAlgClosed.lift⟩
  have h2 := congrArg Complex.re key
  rw [Complex.re_sum] at h2
  have h3 : 0 < ∑ σ : F →ₐ[ℚ] ℂ, (σ b).re :=
    Finset.sum_pos (fun σ _ => hre σ) Finset.univ_nonempty
  rw [← h2] at h3
  simpa using h3

/- English proof (translation)
Use `haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Rewrite using `[← Algebra.trace_trace (S := F), Algebra.trace_algebraMap, map_nsmul]`. Conclude with `nsmul_pos (csTrace_trace_pos b hb) Module.finrank_pos.ne'`.
-/
theorem csTrace_trace_algebraMap_pos {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] [IsTotallyReal F] (b : F) (hb : ∀ ι : F →+* ℝ, 0 < ι b) :
    0 < Algebra.trace ℚ E (algebraMap F E b) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  rw [← Algebra.trace_trace (S := F), Algebra.trace_algebraMap, map_nsmul]
  exact nsmul_pos (csTrace_trace_pos b hb) Module.finrank_pos.ne'

/- English proof (translation)
Introduce `F E _ _ _ _ _ n _ _ σ J hJ`. Take `⟨hF, hdef⟩` from `hJ`. Use `haveI : IsTotallyReal F := hF`. Set `φ0 : F →+* ℂ` to `(IsAlgClosed.lift : F →ₐ[ℚ] ℂ).toRingHom`. Set `ι0 : F →+* ℝ` to `(NumberField.InfinitePlace.isReal_mk_iff.mp (IsTotallyReal.isReal (NumberField.InfinitePlace.mk φ0))).embedding`.

Establish `hval : ∀ x : n → E, x ≠ 0 → ∃ a : F, algebraMap F E a = hform (σ : E →+* E) J x x`. Introduce `x hx`. Break down `hdef ι0 with h | h` into its components or cases. Take `⟨a, ha, -⟩` from `h x hx`. Conclude with `⟨a, ha⟩`.

Take `⟨a, ha, -⟩` from `h x hx`. Conclude with `⟨a, ha⟩`. Establish `same : ∀ x y : n → E, x ≠ 0 → y ≠ 0 → ∀ a b : F, algebraMap F E a = hform (σ : E →+* E) J x x → algebraMap F E b = hform (σ : E →+* E) J y y → ∀ ι : F →+* ℝ, 0 < ι a * ι b`. Introduce `x y hx hy a b ha hb ι`. Break down `hdef ι with h | h` into its components or cases.

Take `⟨a', ha', hap⟩` from `h x hx`. Take `⟨b', hb', hbp⟩` from `h y hy`. Establish `e1 : a' = a` using `(algebraMap F E).injective (ha'.trans ha.symm)`. Establish `e2 : b' = b` using `(algebraMap F E).injective (hb'.trans hb.symm)`. Substitute `e1 e2` using the available equality.

Conclude with `mul_pos hap hbp`. Take `⟨a', ha', hap⟩` from `h x hx`. Take `⟨b', hb', hbp⟩` from `h y hy`. Establish `e1 : a' = a` using `(algebraMap F E).injective (ha'.trans ha.symm)`. Establish `e2 : b' = b` using `(algebraMap F E).injective (hb'.trans hb.symm)`.

Substitute `e1 e2` using the available equality. Conclude with `mul_pos_of_neg_of_neg hap hbp`. Distinguish the cases in `hx : ∃ x0 : n → E, x0 ≠ 0`. Take `⟨x0, hx0⟩` from `hx`. Take `⟨a0, ha0⟩` from `hval x0 hx0`.

Establish `ha0ne : a0 ≠ 0`. Introduce `h0`. Use `same x0 x0 hx0 hx0 a0 a0 ha0 ha0 ι0` as an intermediate fact. Rewrite `this` using `[h0, map_zero, zero_mul]`. Conclude with `lt_irrefl _ this`.

Take `⟨p, q, hq, hpq⟩` from `IsFractionRing.div_surjective (A := 𝓞 F) a0`. Establish `hqF : algebraMap (𝓞 F) F q ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr (nonZeroDivisors.ne_zero hq)`. Establish `hp : algebraMap (𝓞 F) F p = a0 * algebraMap (𝓞 F) F q`. Rewrite using `[← hpq, div_mul_cancel₀ _ hqF]`. Establish `hc : ((p * q : 𝓞 F) : F) = a0 * algebraMap (𝓞 F) F q * algebraMap (𝓞 F) F q`.

Establish `: ((p * q : 𝓞 F) : F) = algebraMap (𝓞 F) F p * algebraMap (𝓞 F) F q`. Rewrite using `[← map_mul]`. Rewrite using `[this, hp]`. Use `⟨p * q, ?_, ?_⟩` and prove the remaining obligations. Introduce `h0`.

Establish `: ((p * q : 𝓞 F) : F) = 0` using `by simp [h0]`. Rewrite `this` using `[hc]`. Conclude with `mul_ne_zero (mul_ne_zero ha0ne hqF) hqF this`. Introduce `x hx`. Take `⟨a, ha⟩` from `hval x hx`.

Rewrite using `[← ha, ← map_mul]`. Apply `csTrace_trace_algebraMap_pos` to reduce the goal to its premises. Introduce `ι`. Establish `hs` using `same x0 x hx0 hx a0 a ha0 ha ι`. Establish `hq2 : 0 < ι (algebraMap (𝓞 F) F q) * ι (algebraMap (𝓞 F) F q)` using `mul_self_pos.mpr ((map_ne_zero_iff _ ι.injective).mpr hqF)`.

Rewrite using `[hc, map_mul, map_mul, map_mul]`. Use polynomial arithmetic with `[mul_pos hs hq2]`. Use `push_neg at hx`. Use `⟨1, one_ne_zero, fun x hx' => absurd (hx x) hx'⟩` and prove the remaining obligations.
-/
theorem trace_form_positive : Formalism.UG.CS.TracePos := by
  intro F E _ _ _ _ _ n _ _ σ J hJ
  obtain ⟨hF, hdef⟩ := hJ
  haveI : IsTotallyReal F := hF

  let φ0 : F →+* ℂ := (IsAlgClosed.lift : F →ₐ[ℚ] ℂ).toRingHom
  let ι0 : F →+* ℝ :=
    (NumberField.InfinitePlace.isReal_mk_iff.mp (IsTotallyReal.isReal (NumberField.InfinitePlace.mk φ0))).embedding
  have hval : ∀ x : n → E, x ≠ 0 → ∃ a : F, algebraMap F E a = hform (σ : E →+* E) J x x := by
    intro x hx
    rcases hdef ι0 with h | h
    · obtain ⟨a, ha, -⟩ := h x hx; exact ⟨a, ha⟩
    · obtain ⟨a, ha, -⟩ := h x hx; exact ⟨a, ha⟩

  have same : ∀ x y : n → E, x ≠ 0 → y ≠ 0 → ∀ a b : F,
      algebraMap F E a = hform (σ : E →+* E) J x x →
      algebraMap F E b = hform (σ : E →+* E) J y y → ∀ ι : F →+* ℝ, 0 < ι a * ι b := by
    intro x y hx hy a b ha hb ι
    rcases hdef ι with h | h
    · obtain ⟨a', ha', hap⟩ := h x hx
      obtain ⟨b', hb', hbp⟩ := h y hy
      have e1 : a' = a := (algebraMap F E).injective (ha'.trans ha.symm)
      have e2 : b' = b := (algebraMap F E).injective (hb'.trans hb.symm)
      subst e1 e2
      exact mul_pos hap hbp
    · obtain ⟨a', ha', hap⟩ := h x hx
      obtain ⟨b', hb', hbp⟩ := h y hy
      have e1 : a' = a := (algebraMap F E).injective (ha'.trans ha.symm)
      have e2 : b' = b := (algebraMap F E).injective (hb'.trans hb.symm)
      subst e1 e2
      exact mul_pos_of_neg_of_neg hap hbp
  by_cases hx : ∃ x0 : n → E, x0 ≠ 0
  · obtain ⟨x0, hx0⟩ := hx
    obtain ⟨a0, ha0⟩ := hval x0 hx0
    have ha0ne : a0 ≠ 0 := by
      intro h0
      have := same x0 x0 hx0 hx0 a0 a0 ha0 ha0 ι0
      rw [h0, map_zero, zero_mul] at this
      exact lt_irrefl _ this
    obtain ⟨p, q, hq, hpq⟩ := IsFractionRing.div_surjective (A := 𝓞 F) a0
    have hqF : algebraMap (𝓞 F) F q ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr (nonZeroDivisors.ne_zero hq)
    have hp : algebraMap (𝓞 F) F p = a0 * algebraMap (𝓞 F) F q := by
      rw [← hpq, div_mul_cancel₀ _ hqF]
    have hc : ((p * q : 𝓞 F) : F) = a0 * algebraMap (𝓞 F) F q * algebraMap (𝓞 F) F q := by
      have : ((p * q : 𝓞 F) : F) = algebraMap (𝓞 F) F p * algebraMap (𝓞 F) F q := by
        rw [← map_mul]
      rw [this, hp]
    refine ⟨p * q, ?_, ?_⟩
    · intro h0
      have : ((p * q : 𝓞 F) : F) = 0 := by simp [h0]
      rw [hc] at this
      exact mul_ne_zero (mul_ne_zero ha0ne hqF) hqF this
    · intro x hx
      obtain ⟨a, ha⟩ := hval x hx
      rw [← ha, ← map_mul]
      apply csTrace_trace_algebraMap_pos
      intro ι
      have hs := same x0 x hx0 hx a0 a ha0 ha ι
      have hq2 : 0 < ι (algebraMap (𝓞 F) F q) * ι (algebraMap (𝓞 F) F q) :=
        mul_self_pos.mpr ((map_ne_zero_iff _ ι.injective).mpr hqF)
      rw [hc, map_mul, map_mul, map_mul]
      nlinarith [mul_pos hs hq2]
  · push_neg at hx
    refine ⟨1, one_ne_zero, fun x hx' => absurd (hx x) hx'⟩

end Formalism.UG.P
