import Formalism.SharpRestriction.CuspSpanNormBounds.LinQRawRange

noncomputable section

open ValuativeRel MeasureTheory
open Formalism.MainNotions.S.Loc

namespace PI.LocHerm.SlopeTestRemainingChoices

open Polynomial Topology

section Top

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

/- English proof (translation)
Rewrite using `[L.O_def]`. Use `⟨(X ^ 2 + (C (-t) * X + C n) : Polynomial 𝒪[F]), ?_, ?_⟩` and prove the remaining obligations. Use `monicity!`. Establish `ht : algebraMap 𝒪[F] E t = algebraMap F E t` using `rfl`. Establish `hn : algebraMap 𝒪[F] E n = algebraMap F E n` using `rfl`.

Simplify using `only [eval₂_add, eval₂_mul, eval₂_neg, eval₂_X_pow, eval₂_X, eval₂_C, map_neg, ht, hn]`. Take the linear combination `h`.
-/
theorem mem_O_of_quad (L : LocE F E) (z : E) (t n : 𝒪[F])
    (h : z * z - algebraMap F E t * z + algebraMap F E n = 0) : z ∈ L.O := by
  rw [L.O_def]
  refine ⟨(X ^ 2 + (C (-t) * X + C n) : Polynomial 𝒪[F]), ?_, ?_⟩
  · monicity!
  · have ht : algebraMap 𝒪[F] E t = algebraMap F E t := rfl
    have hn : algebraMap 𝒪[F] E n = algebraMap F E n := rfl
    simp only [eval₂_add, eval₂_mul, eval₂_neg, eval₂_X_pow, eval₂_X, eval₂_C, map_neg, ht, hn]
    linear_combination h

/- English proof (translation)
The claim follows from `mem_O_of_quad L _ a 0 (by simp)`.
-/
theorem algebraMap_mem_O (L : LocE F E) (a : 𝒪[F]) : algebraMap F E a ∈ L.O :=
  mem_O_of_quad L _ a 0 (by simp)

/- English proof (translation)
Establish `hE : Function.Injective (algebraMap F E)` using `(algebraMap F E).injective`. Rewrite `h` using `[L.O_def]`. Establish `hF : IsIntegral 𝒪[F] a`. Take `⟨p, hp, he⟩` from `h`. Use `⟨p, hp, ?_⟩` and prove the remaining obligations.

Apply `hE` to reduce the goal to its premises. Establish `hc : (algebraMap F E).comp (algebraMap 𝒪[F] F) = algebraMap 𝒪[F] E`. Use extensionality with `r`. Both sides reduce to the same expression. Rewrite using `[Polynomial.hom_eval₂, map_zero, hc, he]`.

Conclude with `(Valuation.integer.integers _).mem_of_integral hF`.
-/
theorem mem_OF_of_mem_O [Nontrivial E] (L : LocE F E) (a : F) (h : algebraMap F E a ∈ L.O) : a ∈ 𝒪[F] := by
  have hE : Function.Injective (algebraMap F E) := (algebraMap F E).injective
  rw [L.O_def] at h
  have hF : IsIntegral 𝒪[F] a := by
    obtain ⟨p, hp, he⟩ := h
    refine ⟨p, hp, ?_⟩
    apply hE
    have hc : (algebraMap F E).comp (algebraMap 𝒪[F] F) = algebraMap 𝒪[F] E := by
      ext r
      rfl
    rw [Polynomial.hom_eval₂, map_zero, hc, he]
  exact (Valuation.integer.integers _).mem_of_integral hF

/- English proof (translation)
Rewrite `h`, the goal using `[L.O_def]`. Take `⟨p, hp, he⟩` from `h`. Use `⟨p, hp, ?_⟩` and prove the remaining obligations. Establish `hc : L.cj.toRingEquiv.toRingHom.comp (algebraMap 𝒪[F] E) = algebraMap 𝒪[F] E`. Use extensionality with `r`.

Use `show L.cj (algebraMap F E (r : F)) = algebraMap F E (r : F)`. Conclude with `L.cj.commutes _`. Establish `h2` using `congrArg L.cj.toRingEquiv.toRingHom he`. Rewrite `h2` using `[Polynomial.hom_eval₂, map_zero, hc]`. Conclude with `h2`.
-/
theorem cj_mem_O (L : LocE F E) (x : E) (h : x ∈ L.O) : L.cj x ∈ L.O := by
  rw [L.O_def] at h ⊢
  obtain ⟨p, hp, he⟩ := h
  refine ⟨p, hp, ?_⟩
  have hc : L.cj.toRingEquiv.toRingHom.comp (algebraMap 𝒪[F] E) = algebraMap 𝒪[F] E := by
    ext r
    show L.cj (algebraMap F E (r : F)) = algebraMap F E (r : F)
    exact L.cj.commutes _
  have h2 := congrArg L.cj.toRingEquiv.toRingHom he
  rw [Polynomial.hom_eval₂, map_zero, hc] at h2
  exact h2

end Top

section Top2

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

/- English proof (translation)
Establish `h'` using `h`. Rewrite `h'` using `[Valuation.mem_integer_iff]`. Rewrite using `[Valuation.mem_integer_iff, map_inv₀]`. Conclude with `inv_le_one_of_one_le₀ (le_of_lt (not_le.mp h'))`.
-/
theorem inv_mem_OF (a : F) (h : a ∉ 𝒪[F]) : a⁻¹ ∈ 𝒪[F] := by
  have h' := h
  rw [Valuation.mem_integer_iff] at h'
  rw [Valuation.mem_integer_iff, map_inv₀]
  exact inv_le_one_of_one_le₀ (le_of_lt (not_le.mp h'))

/- English proof (translation)
Distinguish the cases in `ha : a ∈ 𝒪[F]`. Conclude with `⟨1, by simp, by simpa using ha⟩`. Establish `ha0 : a ≠ 0` using `fun h0 => ha (h0 ▸ zero_mem _)`. Use `⟨⟨a⁻¹, inv_mem_OF a ha⟩, ?_, ?_⟩` and prove the remaining obligations. Use `show a⁻¹ ≠ 0`.

Conclude with `inv_ne_zero ha0`. Use `show a⁻¹ * a ∈ 𝒪[F]`. Rewrite using `[inv_mul_cancel₀ ha0]`. Conclude with `one_mem _`.
-/
theorem exists_scale (a : F) : ∃ r : 𝒪[F], (r : F) ≠ 0 ∧ (r : F) * a ∈ 𝒪[F] := by
  by_cases ha : a ∈ 𝒪[F]
  · exact ⟨1, by simp, by simpa using ha⟩
  · have ha0 : a ≠ 0 := fun h0 => ha (h0 ▸ zero_mem _)
    refine ⟨⟨a⁻¹, inv_mem_OF a ha⟩, ?_, ?_⟩
    · show a⁻¹ ≠ 0
      exact inv_ne_zero ha0
    · show a⁻¹ * a ∈ 𝒪[F]
      rw [inv_mul_cancel₀ ha0]
      exact one_mem _

variable (L : LocE F E)

/- English proof (translation)
The claim follows from `(L.cj_fix _).1 (by rw [map_add, L.cj_cj, add_comm])`.
-/
theorem tr_ex (x : E) : ∃ a : F, algebraMap F E a = x + L.cj x :=
  (L.cj_fix _).1 (by rw [map_add, L.cj_cj, add_comm])

/- English proof (translation)
The claim follows from `(L.cj_fix _).1 (by rw [map_mul, L.cj_cj, mul_comm])`.
-/
theorem nm_ex (x : E) : ∃ a : F, algebraMap F E a = x * L.cj x :=
  (L.cj_fix _).1 (by rw [map_mul, L.cj_cj, mul_comm])

/- English proof (translation)
Assume the negation of the conclusion as `hn`. Rewrite `hn` using `[not_nontrivial_iff_subsingleton]`. Establish `h2` using `L.rank`. Rewrite `h2` using `[Module.finrank_zero_of_subsingleton]`. Use linear arithmetic over natural numbers and integers.
-/
theorem nontrivial_E (L : LocE F E) : Nontrivial E := by
  by_contra hn
  rw [not_nontrivial_iff_subsingleton] at hn
  have h2 := L.rank
  rw [Module.finrank_zero_of_subsingleton] at h2
  omega

/- English proof (translation)
Establish `hx : ∃ x : E, L.cj x ≠ x`. Assume the negation of the conclusion as `hex`. Establish `hall : ∀ w : E, L.cj w = w` using `fun w => not_not.mp (not_exists.mp hex w)`. Establish `hle : Module.finrank F E ≤ 1`. Use `L.free` as an intermediate fact.

Establish `hw : ∀ w : E, ∃ c : F, c • (1 : E) = w`. Introduce `w`. Take `⟨a, ha⟩` from `(L.cj_fix w).1 (hall w)`. Conclude with `⟨a, by rw [Algebra.smul_def, mul_one, ha]⟩`. Conclude with `finrank_le_one (1 : E) hw`.

Establish `h2` using `L.rank`. Use linear arithmetic over natural numbers and integers. Take `⟨x, hx⟩` from `hx`. Establish `hc0 : L.cj (x - L.cj x) = -(x - L.cj x)`. Rewrite using `[map_sub, L.cj_cj]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hθ0ne : x - L.cj x ≠ 0`. Introduce `h0`. Apply `hx` to reduce the goal to its premises. Conclude with `(sub_eq_zero.mp h0).symm`.

Take `⟨D0, hD0⟩` from `(L.cj_fix ((x - L.cj x) * (x - L.cj x))).1 (by rw [map_mul, hc0, neg_mul_neg])`. Establish `hD0ne : D0 ≠ 0`. Introduce and unpack `rfl`. Rewrite `hD0` using `[map_zero]`. Use `L.reduced` as an intermediate fact.

Conclude with `hθ0ne (IsReduced.eq_zero _ ⟨2, by rw [pow_two]; exact hD0.symm⟩)`. Take `⟨r, hr0, hrD⟩` from `exists_scale D0`. Use `⟨algebraMap F E r * (x - L.cj x), ?_, ?_, ⟨r * ⟨(r : F) * D0, hrD⟩, ?_, ?_⟩⟩` and prove the remaining obligations. Apply `mem_O_of_quad L _ 0 (-(r * ⟨(r : F) * D0, hrD⟩))` to reduce the goal to its premises. Establish `e : ((-(r * ⟨(r : F) * D0, hrD⟩) : 𝒪[F]) : F) = -((r : F) * ((r : F) * D0))` using `rfl`.

Establish `e0 : ((0 : 𝒪[F]) : F) = 0` using `rfl`. Rewrite using `[e, e0, map_zero, map_neg, map_mul, map_mul]`. Take the linear combination `(-(algebraMap F E r) ^ 2) * hD0`. Rewrite using `[map_mul, L.cj.commutes, hc0, mul_neg]`. Use `show (r : F) * ((r : F) * D0) ≠ 0`.

Conclude with `mul_ne_zero hr0 (mul_ne_zero hr0 hD0ne)`. Use `show _ = algebraMap F E ((r : F) * ((r : F) * D0))`. Rewrite using `[map_mul, map_mul, hD0]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_theta : ∃ θ ∈ L.O, L.cj θ = -θ ∧ ∃ D : 𝒪[F], (D : F) ≠ 0 ∧ θ * θ = algebraMap F E D := by
  have hx : ∃ x : E, L.cj x ≠ x := by
    by_contra hex
    have hall : ∀ w : E, L.cj w = w := fun w => not_not.mp (not_exists.mp hex w)
    have hle : Module.finrank F E ≤ 1 := by
      have := L.free
      have hw : ∀ w : E, ∃ c : F, c • (1 : E) = w := by
        intro w
        obtain ⟨a, ha⟩ := (L.cj_fix w).1 (hall w)
        exact ⟨a, by rw [Algebra.smul_def, mul_one, ha]⟩
      exact finrank_le_one (1 : E) hw
    have h2 := L.rank
    omega
  obtain ⟨x, hx⟩ := hx
  have hc0 : L.cj (x - L.cj x) = -(x - L.cj x) := by
    rw [map_sub, L.cj_cj]
    ring
  have hθ0ne : x - L.cj x ≠ 0 := by
    intro h0
    apply hx
    exact (sub_eq_zero.mp h0).symm
  obtain ⟨D0, hD0⟩ := (L.cj_fix ((x - L.cj x) * (x - L.cj x))).1 (by rw [map_mul, hc0, neg_mul_neg])
  have hD0ne : D0 ≠ 0 := by
    rintro rfl
    rw [map_zero] at hD0
    have := L.reduced
    exact hθ0ne (IsReduced.eq_zero _ ⟨2, by rw [pow_two]; exact hD0.symm⟩)
  obtain ⟨r, hr0, hrD⟩ := exists_scale D0
  refine ⟨algebraMap F E r * (x - L.cj x), ?_, ?_, ⟨r * ⟨(r : F) * D0, hrD⟩, ?_, ?_⟩⟩
  · apply mem_O_of_quad L _ 0 (-(r * ⟨(r : F) * D0, hrD⟩))
    have e : ((-(r * ⟨(r : F) * D0, hrD⟩) : 𝒪[F]) : F) = -((r : F) * ((r : F) * D0)) := rfl
    have e0 : ((0 : 𝒪[F]) : F) = 0 := rfl
    rw [e, e0, map_zero, map_neg, map_mul, map_mul]
    linear_combination (-(algebraMap F E r) ^ 2) * hD0
  · rw [map_mul, L.cj.commutes, hc0, mul_neg]
  · show (r : F) * ((r : F) * D0) ≠ 0
    exact mul_ne_zero hr0 (mul_ne_zero hr0 hD0ne)
  · show _ = algebraMap F E ((r : F) * ((r : F) * D0))
    rw [map_mul, map_mul, hD0]
    ring

end Top2

section Top3

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

/- English proof (translation)
Take `⟨t, ht⟩` from `(L.cj_fix (x + L.cj x)).1 (by rw [map_add, L.cj_cj, add_comm])`. Take `⟨c, hc⟩` from `(L.cj_fix ((x - L.cj x) * θ)).1 (by rw [map_mul, map_sub, L.cj_cj, hθc]; ring)`. Use `⟨t, c, ht, hc, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, map_ofNat, ht, hc]`. Take the linear combination `(-(x - L.cj x)) * hD`.
-/
theorem decomp (L : LocE F E) (θ : E) (hθc : L.cj θ = -θ) (D : F) (hD : θ * θ = algebraMap F E D) (x : E) :
    ∃ t c : F, algebraMap F E t = x + L.cj x ∧ algebraMap F E c = (x - L.cj x) * θ ∧
      algebraMap F E (2 * D) * x = algebraMap F E (D * t) + algebraMap F E c * θ := by
  obtain ⟨t, ht⟩ := (L.cj_fix (x + L.cj x)).1 (by rw [map_add, L.cj_cj, add_comm])
  obtain ⟨c, hc⟩ := (L.cj_fix ((x - L.cj x) * θ)).1 (by rw [map_mul, map_sub, L.cj_cj, hθc]; ring)
  refine ⟨t, c, ht, hc, ?_⟩
  rw [map_mul, map_mul, map_ofNat, ht, hc]
  linear_combination (-(x - L.cj x)) * hD

end Top3

end PI.LocHerm.SlopeTestRemainingChoices
