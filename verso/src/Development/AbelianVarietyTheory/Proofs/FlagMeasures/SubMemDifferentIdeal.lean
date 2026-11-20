import Mathlib
import Formalism.LocalRingCardinality.DataSpaces
import Formalism.FlagUnipotentLattices.CardSubmodulesAndLinearEquivBounds

open NumberField Module Matrix Formalism.BasicNotions
open scoped ENNReal

namespace GlobalTheory.CMDiscrSq

open Polynomial

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

open NumberField Module Matrix in
open scoped ENNReal in
open Polynomial in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] in
/- English proof (translation)
Express the relevant statement in the definitionally equal form `(t : E) = star (θ : E) at ht`. Establish `hst : star (t : E) = θ` using `by rw [ht, star_star]`. Distinguish the cases in `hθ : (θ : E) ∈ (algebraMap F E).range`. Establish `: t = θ` using `RingOfIntegers.coe_injective (by`. Express the relevant statement in the definitionally equal form `(t : E) = θ`.

Rewrite using `[ht]`. Conclude with `(h.fixed _).2 hθ)`. Rewrite using `[this, sub_self]`. Conclude with `zero_mem _`. Establish `hF : ∀ x : 𝓞 E, star (x : E) = x → ∃ s : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) s = x`.

Introduce `x hx`. Take `⟨a, ha⟩` from `(h.fixed _).1 hx`. Establish `hai : IsIntegral ℤ a` using `(isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ F E) (algebraMap F E).injective).1 (by rw [IsScalarTower.coe_toAlgHom', ha]; exact x.isIntegral_coe)`. Conclude with `⟨⟨a, hai⟩, RingOfIntegers.coe_injective ha⟩`. Take `⟨s, hs⟩` from `hF (θ + t) (by`.

Express the relevant statement in the definitionally equal form `star ((θ : E) + t) = (θ : E) + t`. Rewrite using `[star_add, hst, ht, add_comm])`. Take `⟨n, hn⟩` from `hF (θ * t) (by`. Express the relevant statement in the definitionally equal form `star ((θ : E) * t) = (θ : E) * t`. Rewrite using `[star_mul, hst, ht])`.

Use `set p : (𝓞 F)[X] := X ^ 2 - C s * X + C n with hp_def`. Establish `hpdeg : p.natDegree = 2` using `by rw [hp_def]; compute_degree!`. Establish `hpm : p.Monic` using `by rw [hp_def]; monicity!`. Establish `hroot : aeval θ p = 0`. Simplify using `only [hp_def, map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C, hs, hn]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hint : IsIntegral (𝓞 F) θ` using `Algebra.IsIntegral.isIntegral θ`. Establish `hdvd` using `minpoly.isIntegrallyClosed_dvd hint hroot`. Establish `hmdeg : (minpoly (𝓞 F) θ).natDegree = 2`. Establish `hle : (minpoly (𝓞 F) θ).natDegree ≤ 2` using `hpdeg ▸ natDegree_le_of_dvd hdvd hpm.ne_zero`.

Establish `hne1 : (minpoly (𝓞 F) θ).natDegree ≠ 1`. Introduce `h1`. Take `⟨s', hs'⟩` from `minpoly.natDegree_eq_one_iff.1 h1`. Conclude with `hθ ⟨(s' : F), by rw [← hs']; rfl⟩`. Establish `hpos` using `minpoly.natDegree_pos hint`.

Use linear arithmetic over natural numbers and integers. Establish `hmin : minpoly (𝓞 F) θ = p` using `(eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hpm hdvd (by omega)).symm`. Establish `hint' : IsIntegral (𝓞 F) (θ : E)` using `hint.algebraMap`. Establish `hFdeg : (minpoly F (θ : E)).natDegree = 2`. Rewrite using `[minpoly.isIntegrallyClosed_eq_field_fractions' F hint', minpoly.algebraMap_eq RingOfIntegers.coe_injective, natDegree_map_eq_of_injective (IsFractionRing.injective (𝓞 F) F), hmdeg]`.

Establish `htop : IntermediateField.adjoin F {(θ : E)} = ⊤` using `IntermediateField.eq_of_le_of_finrank_eq le_top (by`. Rewrite using `[IntermediateField.finrank_top', IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral _), hFdeg, h.deg2])`. Establish `hgen : Algebra.adjoin F {algebraMap (𝓞 E) E θ} = ⊤`. Rewrite using `[← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (Algebra.IsAlgebraic.isAlgebraic _)]`. Express the relevant statement in the definitionally equal form `(IntermediateField.adjoin F {(θ : E)}).toSubalgebra = ⊤`.

Rewrite using `[htop, IntermediateField.top_toSubalgebra]`. Establish `hd` using `aeval_derivative_mem_differentIdeal (𝓞 F) F E θ hgen`. Rewrite `hd` using `[hmin]`. Use `hd using 1` and compare the differences between its conclusion and the goal. Simplify using `[hp_def, hs]`.

Expand and normalize the polynomial expressions, which then agree.
-/
private lemma sub_mem_differentIdeal_of_eq_star (h : _root_.Formalism.BasicNotions.CMData F E) (θ t : 𝓞 E)
    (ht : algebraMap (𝓞 E) E t = star (algebraMap (𝓞 E) E θ)) :
    θ - t ∈ differentIdeal (𝓞 F) (𝓞 E) := by
  change (t : E) = star (θ : E) at ht
  have hst : star (t : E) = θ := by rw [ht, star_star]
  by_cases hθ : (θ : E) ∈ (algebraMap F E).range
  · have : t = θ := RingOfIntegers.coe_injective (by
      change (t : E) = θ
      rw [ht]
      exact (h.fixed _).2 hθ)
    rw [this, sub_self]
    exact zero_mem _
  have hF : ∀ x : 𝓞 E, star (x : E) = x → ∃ s : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) s = x := by
    intro x hx
    obtain ⟨a, ha⟩ := (h.fixed _).1 hx
    have hai : IsIntegral ℤ a :=
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ F E) (algebraMap F E).injective).1
        (by rw [IsScalarTower.coe_toAlgHom', ha]; exact x.isIntegral_coe)
    exact ⟨⟨a, hai⟩, RingOfIntegers.coe_injective ha⟩
  obtain ⟨s, hs⟩ := hF (θ + t) (by
    change star ((θ : E) + t) = (θ : E) + t
    rw [star_add, hst, ht, add_comm])
  obtain ⟨n, hn⟩ := hF (θ * t) (by
    change star ((θ : E) * t) = (θ : E) * t
    rw [star_mul, hst, ht])
  set p : (𝓞 F)[X] := X ^ 2 - C s * X + C n with hp_def
  have hpdeg : p.natDegree = 2 := by rw [hp_def]; compute_degree!
  have hpm : p.Monic := by rw [hp_def]; monicity!
  have hroot : aeval θ p = 0 := by
    simp only [hp_def, map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C, hs, hn]
    ring
  have hint : IsIntegral (𝓞 F) θ := Algebra.IsIntegral.isIntegral θ
  have hdvd := minpoly.isIntegrallyClosed_dvd hint hroot
  have hmdeg : (minpoly (𝓞 F) θ).natDegree = 2 := by
    have hle : (minpoly (𝓞 F) θ).natDegree ≤ 2 := hpdeg ▸ natDegree_le_of_dvd hdvd hpm.ne_zero
    have hne1 : (minpoly (𝓞 F) θ).natDegree ≠ 1 := by
      intro h1
      obtain ⟨s', hs'⟩ := minpoly.natDegree_eq_one_iff.1 h1
      exact hθ ⟨(s' : F), by rw [← hs']; rfl⟩
    have hpos := minpoly.natDegree_pos hint
    omega
  have hmin : minpoly (𝓞 F) θ = p :=
    (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hpm hdvd (by omega)).symm
  have hint' : IsIntegral (𝓞 F) (θ : E) := hint.algebraMap
  have hFdeg : (minpoly F (θ : E)).natDegree = 2 := by
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' F hint',
      minpoly.algebraMap_eq RingOfIntegers.coe_injective, natDegree_map_eq_of_injective
        (IsFractionRing.injective (𝓞 F) F), hmdeg]
  have htop : IntermediateField.adjoin F {(θ : E)} = ⊤ := IntermediateField.eq_of_le_of_finrank_eq le_top (by
    rw [IntermediateField.finrank_top', IntermediateField.adjoin.finrank
      (Algebra.IsIntegral.isIntegral _), hFdeg, h.deg2])
  have hgen : Algebra.adjoin F {algebraMap (𝓞 E) E θ} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic _)]
    change (IntermediateField.adjoin F {(θ : E)}).toSubalgebra = ⊤
    rw [htop, IntermediateField.top_toSubalgebra]
  have hd := aeval_derivative_mem_differentIdeal (𝓞 F) F E θ hgen
  rw [hmin] at hd
  convert hd using 1
  simp [hp_def, hs]
  ring

open NumberField Module Matrix in
open scoped ENNReal in
open Polynomial in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] in

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Take `⟨P, hP, hle⟩` from `Ideal.exists_le_maximal _ hne`. Take `⟨θ, t, ht, hθt⟩` from `h.cmUnram.2.2 P hP`. Conclude with `hθt (hle (sub_mem_differentIdeal_of_eq_star h θ t ht))`.
-/
theorem _root_.GlobalTheory.CMDiscrSq.differentIdeal_eq_top (h : _root_.Formalism.BasicNotions.CMData F E) : differentIdeal (𝓞 F) (𝓞 E) = ⊤ := by
  by_contra hne
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨θ, t, ht, hθt⟩ := h.cmUnram.2.2 P hP
  exact hθt (hle (sub_mem_differentIdeal_of_eq_star h θ t ht))

end GlobalTheory.CMDiscrSq

open NumberField Module Matrix in
open scoped ENNReal in

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ h`. Establish `hd` using `_root_.GlobalTheory.CMDiscrSq.differentIdeal_eq_top h`. Establish `hE` using `natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow F (𝓞 F) E (𝓞 E)`. Rewrite `hE` using `[hd, Ideal.absNorm_top, one_mul, h.deg2]`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Int.abs_eq_natAbs, hE]`. Use `push_cast`. Conclude with `sq_abs _`. Establish `hmul` using `differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 F) (𝓞 E)`. Rewrite `hmul` using `[hd, Ideal.top_mul]`.

Rewrite using `[← hmul, absNorm_differentIdeal E (𝓞 E), hE]`.
-/
theorem _root_.GlobalTheory.cm_discr_sq : ∀ (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [StarRing E] [Algebra F E], _root_.Formalism.BasicNotions.CMData F E → |discr E| = discr F ^ 2 ∧
      Ideal.absNorm (Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (differentIdeal ℤ (𝓞 F))) =
        (discr F).natAbs ^ 2 := by
  intro F E _ _ _ _ _ _ h
  have hd := _root_.GlobalTheory.CMDiscrSq.differentIdeal_eq_top h
  have hE := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow F (𝓞 F) E (𝓞 E)
  rw [hd, Ideal.absNorm_top, one_mul, h.deg2] at hE
  refine ⟨?_, ?_⟩
  · rw [Int.abs_eq_natAbs, hE]
    push_cast
    exact sq_abs _
  · have hmul := differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 F) (𝓞 E)
    rw [hd, Ideal.top_mul] at hmul
    rw [← hmul, absNorm_differentIdeal E (𝓞 E), hE]
