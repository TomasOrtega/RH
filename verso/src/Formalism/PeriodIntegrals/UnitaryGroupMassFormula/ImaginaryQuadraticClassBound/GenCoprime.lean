import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ImaginaryQuadraticClassBound.Development

open NumberField
open scoped nonZeroDivisors

namespace PI.RayBoundIQW

variable {K0 : Type} [Field K0] [NumberField K0] (qq : Ideal (𝓞 K0))

abbrev PrimeTo := {I : Ideal (𝓞 K0) // I ≠ ⊥ ∧ I ⊔ qq = ⊤}

noncomputable def cls (J : PrimeTo qq) : ClassGroup (𝓞 K0) :=
  ClassGroup.mk0 ⟨J.1, mem_nonZeroDivisors_of_ne_zero J.2.1⟩

noncomputable def base (c : ClassGroup (𝓞 K0)) : PrimeTo qq := by
  classical
  exact if h : ∃ I : PrimeTo qq, cls qq I = c then h.choose else ⟨⊤, top_ne_bot, top_sup_eq _⟩

/- English proof (translation)
Establish `h : ∃ I : PrimeTo qq, cls qq I = cls qq J` using `⟨J, rfl⟩`. Unfold `base`. Rewrite using `[dif_pos h]`. Conclude with `h.choose_spec`.
-/
theorem cls_base (J : PrimeTo qq) : cls qq (base qq (cls qq J)) = cls qq J := by
  classical
  have h : ∃ I : PrimeTo qq, cls qq I = cls qq J := ⟨J, rfl⟩
  unfold base
  rw [dif_pos h]
  exact h.choose_spec

/- English proof (translation)
Use `set B := base qq (cls qq J) with hB`. Establish `hJ0 : J.1 ∈ (Ideal (𝓞 K0))⁰` using `mem_nonZeroDivisors_of_ne_zero J.2.1`. Establish `hB0 : B.1 ∈ (Ideal (𝓞 K0))⁰` using `mem_nonZeroDivisors_of_ne_zero B.2.1`. Establish `hP0 : J.1 * B.1 ^ (classNumber K0 - 1) ∈ (Ideal (𝓞 K0))⁰` using `((⟨J.1, hJ0⟩ : (Ideal (𝓞 K0))⁰) * (⟨B.1, hB0⟩ : (Ideal (𝓞 K0))⁰) ^ (classNumber K0 - 1)).2`. Establish `hone : ClassGroup.mk0 ⟨J.1 * B.1 ^ (classNumber K0 - 1), hP0⟩ = 1`.

Establish `e : (⟨J.1 * B.1 ^ (classNumber K0 - 1), hP0⟩ : (Ideal (𝓞 K0))⁰) = (⟨J.1, hJ0⟩ : (Ideal (𝓞 K0))⁰) * (⟨B.1, hB0⟩ : (Ideal (𝓞 K0))⁰) ^ (classNumber K0 - 1)`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using the standard rewrite rules. Rewrite using `[e, map_mul, map_pow]`. Establish `h1 : ClassGroup.mk0 (⟨B.1, hB0⟩ : (Ideal (𝓞 K0))⁰) = cls qq J` using `cls_base qq J`.

Establish `h2 : ClassGroup.mk0 (⟨J.1, hJ0⟩ : (Ideal (𝓞 K0))⁰) = cls qq J` using `rfl`. Rewrite using `[h1, h2, ← pow_succ']`. Establish `hpos : 0 < classNumber K0` using `classNumber_pos K0`. Rewrite using `[Nat.sub_add_cancel hpos]`. Conclude with `pow_card_eq_one`.

Establish `hpr` using `(ClassGroup.mk0_eq_one_iff hP0).mp hone`. Conclude with `⟨Submodule.IsPrincipal.generator _, Submodule.IsPrincipal.span_singleton_generator _⟩`.
-/
theorem principal (J : PrimeTo qq) : ∃ m : 𝓞 K0,
    Ideal.span {m} = J.1 * (base qq (cls qq J)).1 ^ (classNumber K0 - 1) := by
  set B := base qq (cls qq J) with hB
  have hJ0 : J.1 ∈ (Ideal (𝓞 K0))⁰ := mem_nonZeroDivisors_of_ne_zero J.2.1
  have hB0 : B.1 ∈ (Ideal (𝓞 K0))⁰ := mem_nonZeroDivisors_of_ne_zero B.2.1
  have hP0 : J.1 * B.1 ^ (classNumber K0 - 1) ∈ (Ideal (𝓞 K0))⁰ :=
    ((⟨J.1, hJ0⟩ : (Ideal (𝓞 K0))⁰) * (⟨B.1, hB0⟩ : (Ideal (𝓞 K0))⁰) ^ (classNumber K0 - 1)).2
  have hone : ClassGroup.mk0 ⟨J.1 * B.1 ^ (classNumber K0 - 1), hP0⟩ = 1 := by
    have e : (⟨J.1 * B.1 ^ (classNumber K0 - 1), hP0⟩ : (Ideal (𝓞 K0))⁰) =
        (⟨J.1, hJ0⟩ : (Ideal (𝓞 K0))⁰) * (⟨B.1, hB0⟩ : (Ideal (𝓞 K0))⁰) ^ (classNumber K0 - 1) := by
      apply Subtype.ext
      simp
    rw [e, map_mul, map_pow]
    have h1 : ClassGroup.mk0 (⟨B.1, hB0⟩ : (Ideal (𝓞 K0))⁰) = cls qq J := cls_base qq J
    have h2 : ClassGroup.mk0 (⟨J.1, hJ0⟩ : (Ideal (𝓞 K0))⁰) = cls qq J := rfl
    rw [h1, h2, ← pow_succ']
    have hpos : 0 < classNumber K0 := classNumber_pos K0
    rw [Nat.sub_add_cancel hpos]
    exact pow_card_eq_one
  have hpr := (ClassGroup.mk0_eq_one_iff hP0).mp hone
  exact ⟨Submodule.IsPrincipal.generator _, Submodule.IsPrincipal.span_singleton_generator _⟩

noncomputable def gen (J : PrimeTo qq) : 𝓞 K0 := (principal qq J).choose

/- English proof (translation)
The claim follows from `(principal qq J).choose_spec`.
-/
theorem gen_spec (J : PrimeTo qq) :
    Ideal.span {gen qq J} = J.1 * (base qq (cls qq J)).1 ^ (classNumber K0 - 1) :=
  (principal qq J).choose_spec

/- English proof (translation)
Introduce `h`. Establish `e` using `gen_spec qq J`. Rewrite `e` using `[h, Ideal.span_singleton_eq_bot.mpr rfl]`. Establish `hJ : J.1 ≠ 0` using `J.2.1`. Establish `hB : (base qq (cls qq J)).1 ^ (classNumber K0 - 1) ≠ 0` using `pow_ne_zero _ (base qq (cls qq J)).2.1`.

Conclude with `mul_ne_zero hJ hB (by rw [← e]; rfl)`.
-/
theorem gen_ne_zero (J : PrimeTo qq) : gen qq J ≠ 0 := by
  intro h
  have e := gen_spec qq J
  rw [h, Ideal.span_singleton_eq_bot.mpr rfl] at e
  have hJ : J.1 ≠ 0 := J.2.1
  have hB : (base qq (cls qq J)).1 ^ (classNumber K0 - 1) ≠ 0 :=
    pow_ne_zero _ (base qq (cls qq J)).2.1
  exact mul_ne_zero hJ hB (by rw [← e]; rfl)

/- English proof (translation)
Rewrite using `[gen_spec, ← Ideal.isCoprime_iff_sup_eq]`. Conclude with `IsCoprime.mul_left (Ideal.isCoprime_iff_sup_eq.mpr J.2.2) (IsCoprime.pow_left (Ideal.isCoprime_iff_sup_eq.mpr (base qq (cls qq J)).2.2))`.
-/
theorem gen_coprime (J : PrimeTo qq) : Ideal.span {gen qq J} ⊔ qq = ⊤ := by
  rw [gen_spec, ← Ideal.isCoprime_iff_sup_eq]
  exact IsCoprime.mul_left (Ideal.isCoprime_iff_sup_eq.mpr J.2.2)
    (IsCoprime.pow_left (Ideal.isCoprime_iff_sup_eq.mpr (base qq (cls qq J)).2.2))

noncomputable def inv (J : PrimeTo qq) : ClassGroup (𝓞 K0) × (𝓞 K0 ⧸ qq) :=
  (cls qq J, Ideal.Quotient.mk qq (gen qq J))

/- English proof (translation)
Establish `hc : cls qq J = cls qq J'` using `congrArg Prod.fst h`. Establish `hr : Ideal.Quotient.mk qq (gen qq J) = Ideal.Quotient.mk qq (gen qq J')` using `congrArg Prod.snd h`. Establish `hJ` using `gen_spec qq J`. Establish `hJ'` using `gen_spec qq J'`. Rewrite `hJ'` using `[← hc]`.

Establish `hdiff : gen qq J - gen qq J' ∈ qq` using `Ideal.Quotient.eq.mp hr`. Establish `hmul : Ideal.span {gen qq J'} * J.1 = Ideal.span {gen qq J} * J'.1`. Rewrite using `[hJ, hJ']`. Expand and normalize the polynomial expressions, which then agree. Take `⟨t, q, hq, htq⟩` from `Ideal.mem_span_singleton_sup.mp ((gen_coprime qq J).symm ▸ Submodule.mem_top : (1 : 𝓞 K0) ∈ Ideal.span {gen qq J} ⊔ qq)`.

Distinguish the cases in `ht : t = 0`. Establish `htop : qq = ⊤`. Rewrite using `[Ideal.eq_top_iff_one]`. Rewrite `htq` using `[ht, zero_mul, zero_add]`. Conclude with `htq ▸ hq`.

Use `⟨gen qq J', gen qq J, gen_ne_zero qq J', gen_ne_zero qq J, ?_, ?_, ?_, hmul⟩` and prove the remaining obligations. Conclude with `(mul_one (gen qq J' - 1)) ▸ qq.mul_mem_left _ ((Ideal.eq_top_iff_one qq).mp htop)`. Conclude with `(mul_one (gen qq J - 1)) ▸ qq.mul_mem_left _ ((Ideal.eq_top_iff_one qq).mp htop)`. Introduce `σ`. Conclude with `isEmptyElim σ`.

Use `⟨t * gen qq J', t * gen qq J, mul_ne_zero ht (gen_ne_zero qq J'), mul_ne_zero ht (gen_ne_zero qq J), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `e : t * gen qq J' - 1 = (-t) * (gen qq J - gen qq J') + -q`. Take the linear combination `htq`. Rewrite using `[e]`. Conclude with `qq.add_mem (qq.mul_mem_left _ hdiff) (qq.neg_mem hq)`.

Establish `e : t * gen qq J - 1 = -q` using `by linear_combination htq`. Rewrite using `[e]`. Conclude with `qq.neg_mem hq`. Introduce `σ`. Conclude with `isEmptyElim σ`.

Rewrite using `[← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton, mul_assoc, mul_assoc, hmul]`.
-/
theorem key (hre : IsEmpty (K0 →+* ℝ)) (J J' : PrimeTo qq) (h : inv qq J = inv qq J') :
    rayRel K0 qq J J' := by
  have hc : cls qq J = cls qq J' := congrArg Prod.fst h
  have hr : Ideal.Quotient.mk qq (gen qq J) = Ideal.Quotient.mk qq (gen qq J') :=
    congrArg Prod.snd h
  have hJ := gen_spec qq J
  have hJ' := gen_spec qq J'
  rw [← hc] at hJ'
  have hdiff : gen qq J - gen qq J' ∈ qq := Ideal.Quotient.eq.mp hr
  have hmul : Ideal.span {gen qq J'} * J.1 = Ideal.span {gen qq J} * J'.1 := by
    rw [hJ, hJ']; ring
  obtain ⟨t, q, hq, htq⟩ := Ideal.mem_span_singleton_sup.mp
    ((gen_coprime qq J).symm ▸ Submodule.mem_top : (1 : 𝓞 K0) ∈ Ideal.span {gen qq J} ⊔ qq)
  by_cases ht : t = 0
  · have htop : qq = ⊤ := by
      rw [Ideal.eq_top_iff_one]; rw [ht, zero_mul, zero_add] at htq; exact htq ▸ hq
    refine ⟨gen qq J', gen qq J, gen_ne_zero qq J', gen_ne_zero qq J, ?_, ?_, ?_, hmul⟩
    · exact (mul_one (gen qq J' - 1)) ▸ qq.mul_mem_left _ ((Ideal.eq_top_iff_one qq).mp htop)
    · exact (mul_one (gen qq J - 1)) ▸ qq.mul_mem_left _ ((Ideal.eq_top_iff_one qq).mp htop)
    · intro σ; exact isEmptyElim σ
  · refine ⟨t * gen qq J', t * gen qq J, mul_ne_zero ht (gen_ne_zero qq J'),
      mul_ne_zero ht (gen_ne_zero qq J), ?_, ?_, ?_, ?_⟩
    · have e : t * gen qq J' - 1 = (-t) * (gen qq J - gen qq J') + -q := by
        linear_combination htq
      rw [e]; exact qq.add_mem (qq.mul_mem_left _ hdiff) (qq.neg_mem hq)
    · have e : t * gen qq J - 1 = -q := by linear_combination htq
      rw [e]; exact qq.neg_mem hq
    · intro σ; exact isEmptyElim σ
    · rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton,
        mul_assoc, mul_assoc, hmul]

end PI.RayBoundIQW
