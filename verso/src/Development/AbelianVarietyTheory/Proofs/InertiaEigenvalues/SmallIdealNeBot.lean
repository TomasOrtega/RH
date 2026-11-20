import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharpolySmulOfProd
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L

namespace GlobalTheory.SmallPrimeIdeal

open NumberField

/- English proof (translation)
Take `⟨p, hp, hpy⟩` from `hy`. Assume the negation of the conclusion as `hlt`. Rewrite `hlt` using `[not_le]`. Establish `heq : y ^ p.natDegree + ∑ i ∈ Finset.range p.natDegree, (p.coeff i : K) * y ^ i = 0`. Rewrite `hpy` using `[hp.as_sum]`.

Simplify using `only [Polynomial.eval₂_add, Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow] at hpy`. Simplify using `only [algebraMap_int_eq, eq_intCast] at hpy`. Conclude with `hpy`. Break down `Nat.eq_zero_or_pos p.natDegree with h0 | hpos` into its components or cases. Rewrite `heq` using `[h0]`.

Simplify using `at heq`. Take `⟨i, hi, hle⟩` from `IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty (Finset.nonempty_range_iff.mpr hpos.ne') (fun i => (p.coeff i : K) * y ^ i)`. Establish `hnorm : ‖y‖ ^ p.natDegree = ‖∑ i ∈ Finset.range p.natDegree, (p.coeff i : K) * y ^ i‖`. Rewrite using `[← norm_pow, eq_neg_of_add_eq_zero_left heq, norm_neg]`. Establish `hterm : ‖(p.coeff i : K) * y ^ i‖ < ‖y‖ ^ p.natDegree`.

Rewrite using `[norm_mul, norm_pow]`. Combine the equalities or inequalities in the displayed calculation. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem norm_le_one_of_isIntegral {K : Type} [NormedField K] [IsUltrametricDist K] {y : K}
    (hy : IsIntegral ℤ y) : ‖y‖ ≤ 1 := by
  obtain ⟨p, hp, hpy⟩ := hy
  by_contra hlt
  rw [not_le] at hlt

  have heq : y ^ p.natDegree + ∑ i ∈ Finset.range p.natDegree, (p.coeff i : K) * y ^ i = 0 := by
    rw [hp.as_sum] at hpy
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.eval₂_X_pow] at hpy
    simp only [algebraMap_int_eq, eq_intCast] at hpy
    exact hpy
  rcases Nat.eq_zero_or_pos p.natDegree with h0 | hpos
  · rw [h0] at heq
    simp at heq
  obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty
    (Finset.nonempty_range_iff.mpr hpos.ne') (fun i => (p.coeff i : K) * y ^ i)
  have hnorm : ‖y‖ ^ p.natDegree = ‖∑ i ∈ Finset.range p.natDegree, (p.coeff i : K) * y ^ i‖ := by
    rw [← norm_pow, eq_neg_of_add_eq_zero_left heq, norm_neg]
  have hterm : ‖(p.coeff i : K) * y ^ i‖ < ‖y‖ ^ p.natDegree := by
    rw [norm_mul, norm_pow]
    calc ‖(p.coeff i : K)‖ * ‖y‖ ^ i ≤ 1 * ‖y‖ ^ i :=
          mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_intCast_le_one K _) (by positivity)
      _ = ‖y‖ ^ i := one_mul _
      _ < ‖y‖ ^ p.natDegree := pow_lt_pow_right₀ hlt (Finset.mem_range.mp hi)
  linarith

/- English proof (translation)
Conclude with `norm_le_one_of_isIntegral ((NumberField.RingOfIntegers.isIntegral_coe x).map a.toIntAlgHom)`.
-/
theorem norm_int_le_one {L K : Type} [Field L] [NormedField K] [IsUltrametricDist K]
    (a : L →+* K) (x : 𝓞 L) : ‖a (x : L)‖ ≤ 1 := by

  exact norm_le_one_of_isIntegral ((NumberField.RingOfIntegers.isIntegral_coe x).map a.toIntAlgHom)

def smallIdeal {L K : Type} [Field L] [NormedField K] [IsUltrametricDist K]
    (a : L →+* K) : Ideal (𝓞 L) where
  carrier := {x | ‖a (x : L)‖ < 1}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    have h : ‖a (x : L) + a (y : L)‖ ≤ max ‖a (x : L)‖ ‖a (y : L)‖ :=
      IsUltrametricDist.norm_add_le_max _ _
    have e : a ((x + y : 𝓞 L) : L) = a (x : L) + a (y : L) := by simp
    change ‖a ((x + y : 𝓞 L) : L)‖ < 1
    rw [e]
    exact lt_of_le_of_lt h (max_lt hx hy)
  smul_mem' := by
    intro c x hx
    have e : a ((c • x : 𝓞 L) : L) = a (c : L) * a (x : L) := by simp
    change ‖a ((c • x : 𝓞 L) : L)‖ < 1
    rw [e, norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right (norm_int_le_one a c) (norm_nonneg _) hx

/- English proof (translation)
Conclude with `Iff.rfl`.
-/
theorem mem_smallIdeal {L K : Type} [Field L] [NormedField K] [IsUltrametricDist K]
    (a : L →+* K) (x : 𝓞 L) : x ∈ smallIdeal a ↔ ‖a (x : L)‖ < 1 := by
  exact Iff.rfl

/- English proof (translation)
Conclude with `le_antisymm (norm_int_le_one a x) (not_lt.mp h)`.
-/
theorem norm_eq_one {L K : Type} [Field L] [NormedField K] [IsUltrametricDist K]
    (a : L →+* K) (x : 𝓞 L) (h : ¬ ‖a (x : L)‖ < 1) : ‖a (x : L)‖ = 1 := by
  exact le_antisymm (norm_int_le_one a x) (not_lt.mp h)

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.ne_top_iff_one, mem_smallIdeal]`. Simplify using the standard rewrite rules. Introduce `x y hxy`. Rewrite `hxy` using `[mem_smallIdeal]`.

Rewrite using `[mem_smallIdeal, mem_smallIdeal]`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Take `⟨hx, hy⟩` from `hc`. Establish `e : a ((x * y : 𝓞 L) : L) = a (x : L) * a (y : L)` using `by simp`.

Rewrite `hxy` using `[e, norm_mul, norm_eq_one a x (not_lt.mpr hx), norm_eq_one a y (not_lt.mpr hy)]`. Evaluate the numerical expressions using `at hxy`.
-/
theorem smallIdeal_isPrime {L K : Type} [Field L] [NormedField K] [IsUltrametricDist K]
    (a : L →+* K) : (smallIdeal a).IsPrime := by
  refine ⟨?_, ?_⟩
  ·
    rw [Ideal.ne_top_iff_one, mem_smallIdeal]
    simp
  · intro x y hxy
    rw [mem_smallIdeal] at hxy
    rw [mem_smallIdeal, mem_smallIdeal]
    by_contra hc
    push Not at hc
    obtain ⟨hx, hy⟩ := hc
    have e : a ((x * y : 𝓞 L) : L) = a (x : L) * a (y : L) := by simp
    rw [e, norm_mul, norm_eq_one a x (not_lt.mpr hx), norm_eq_one a y (not_lt.mpr hy)] at hxy
    norm_num at hxy

/- English proof (translation)
Set `Rp` to `Localization.AtPrime P`. Establish `: IsDiscreteValuationRing Rp` using `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 L) hP Rp`. Establish `hinj : Function.Injective (algebraMap (𝓞 L) Rp)` using `IsLocalization.injective Rp P.primeCompl_le_nonZeroDivisors`. Break down `ValuationRing.dvd_total (algebraMap (𝓞 L) Rp u) (algebraMap (𝓞 L) Rp v) with ⟨c, hc⟩ | ⟨c, hc⟩` into its components or cases. Take `⟨⟨r, s⟩, rfl⟩` from `IsLocalization.mk'_surjective P.primeCompl c`.

Use `⟨r, s, s.2, Or.inl (hinj ?_)⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, hc, mul_assoc, IsLocalization.mk'_spec]`. Take `⟨⟨r, s⟩, rfl⟩` from `IsLocalization.mk'_surjective P.primeCompl c`. Use `⟨r, s, s.2, Or.inr (hinj ?_)⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, hc, mul_assoc, IsLocalization.mk'_spec]`.
-/
theorem exists_local_dvd {L : Type} [Field L] [NumberField L] (P : Ideal (𝓞 L)) [P.IsPrime]
    (hP : P ≠ ⊥) (u v : 𝓞 L) :
    ∃ r s : 𝓞 L, s ∉ P ∧ (u * r = v * s ∨ v * r = u * s) := by

  let Rp := Localization.AtPrime P
  have : IsDiscreteValuationRing Rp :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 L) hP Rp
  have hinj : Function.Injective (algebraMap (𝓞 L) Rp) :=
    IsLocalization.injective Rp P.primeCompl_le_nonZeroDivisors
  rcases ValuationRing.dvd_total (algebraMap (𝓞 L) Rp u) (algebraMap (𝓞 L) Rp v) with ⟨c, hc⟩ | ⟨c, hc⟩
  · obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl c
    refine ⟨r, s, s.2, Or.inl (hinj ?_)⟩
    rw [map_mul, map_mul, hc, mul_assoc, IsLocalization.mk'_spec]
  · obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl c
    refine ⟨r, s, s.2, Or.inr (hinj ?_)⟩
    rw [map_mul, map_mul, hc, mul_assoc, IsLocalization.mk'_spec]

/- English proof (translation)
Introduce `hbot`. Establish `hl : ((l : 𝓞 L)) ∈ smallIdeal a`. Rewrite using `[mem_smallIdeal]`. Establish `e : a ((l : 𝓞 L) : L) = (l : PadicAlgCl l)` using `by simp`. Establish `hext` using `PadicAlgCl.norm_extends (p := l) (l : ℚ_[l])`.

Rewrite `hext` using `[map_natCast]`. Rewrite using `[e, hext, Padic.norm_p]`. Conclude with `inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)`. Rewrite `hl` using `[hbot, Ideal.mem_bot]`. Establish `h0 : ((l : 𝓞 L) : L) = 0` using `by rw [hl]; simp`.

Conclude with `(Fact.out : l.Prime).ne_zero (by exact_mod_cast h0)`.
-/
theorem smallIdeal_ne_bot {L : Type} [Field L] [NumberField L] {l : ℕ} [Fact l.Prime]
    (a : L →+* PadicAlgCl l) : smallIdeal a ≠ ⊥ := by

  intro hbot
  have hl : ((l : 𝓞 L)) ∈ smallIdeal a := by
    rw [mem_smallIdeal]
    have e : a ((l : 𝓞 L) : L) = (l : PadicAlgCl l) := by simp
    have hext := PadicAlgCl.norm_extends (p := l) (l : ℚ_[l])
    rw [map_natCast] at hext
    rw [e, hext, Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  rw [hbot, Ideal.mem_bot] at hl
  have h0 : ((l : 𝓞 L) : L) = 0 := by rw [hl]; simp
  exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast h0)

/- English proof (translation)
Establish `hb : ∀ y : 𝓞 L, y ∈ smallIdeal a ↔ ‖b (y : L)‖ < 1` using `fun y => (mem_smallIdeal a y).trans (h y)`. Use `smallIdeal_isPrime a` as an intermediate fact. Take `⟨u, w, hw, rfl⟩` from `IsFractionRing.div_surjective (𝓞 L) x`. Express the relevant statement in the definitionally equal form `‖a ((u : L) / (w : L))‖ ≤ 1 at hx`. Express the relevant statement in the definitionally equal form `‖b ((u : L) / (w : L))‖ ≤ 1`.

Establish `hw0 : (w : L) ≠ 0`. Use `nonZeroDivisors.ne_zero hw` as an intermediate fact. Conclude with `this` after adjusting the coercions. Take `⟨r, s, hs, hrs⟩` from `exists_local_dvd (smallIdeal a) (smallIdeal_ne_bot a) u w`. Establish `hs0 : (s : L) ≠ 0`.

Introduce `h0`. Apply `hs` to reduce the goal to its premises. Establish `: s = 0` using `by exact_mod_cast h0`. Rewrite using `[this]`. Conclude with `(smallIdeal a).zero_mem`.

Establish `hbs : ‖b (s : L)‖ = 1` using `norm_eq_one b s (fun hlt => hs ((hb s).mpr hlt))`. Establish `has : ‖a (s : L)‖ = 1` using `norm_eq_one a s (fun hlt => hs ((mem_smallIdeal a s).mpr hlt))`. Break down `hrs with h1 | h1` into its components or cases. Establish `h1' : (u : L) * r = w * s` using `by exact_mod_cast congrArg (fun z : 𝓞 L => (z : L)) h1`. Establish `hr0 : (r : L) ≠ 0`.

Introduce `h0`. Rewrite `h1'` using `[h0, mul_zero]`. Conclude with `mul_ne_zero hw0 hs0 h1'.symm`. Establish `e : (u : L) / w = s / r`. Rewrite using `[div_eq_div_iff hw0 hr0]`.

Take the linear combination `h1'`. Rewrite `hx`, the goal using `[e]`. Rewrite `hx` using `[map_div₀, norm_div, has]`. Establish `hpos : 0 < ‖a (r : L)‖` using `norm_pos_iff.mpr ((map_ne_zero a).mpr hr0)`. Establish `har : ¬ ‖a (r : L)‖ < 1`.

Introduce `hlt`. Rewrite `hx` using `[div_le_iff₀ hpos]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hbr : ‖b (r : L)‖ = 1` using `norm_eq_one b r (fun hlt => har ((h r).mpr hlt))`. Rewrite using `[map_div₀, norm_div, hbs, hbr, div_one]`.

Establish `h1' : (w : L) * r = u * s` using `by exact_mod_cast congrArg (fun z : 𝓞 L => (z : L)) h1`. Establish `e : (u : L) / w = r / s`. Rewrite using `[div_eq_div_iff hw0 hs0]`. Take the linear combination `-h1'`. Rewrite using `[e, map_div₀, norm_div, hbs, div_one]`.

Conclude with `norm_int_le_one b r`.
-/
theorem le_one_of_le_one {L : Type} [Field L] [NumberField L] {l : ℕ} [Fact l.Prime]
    (a b : L →+* PadicAlgCl l)
    (h : ∀ x : 𝓞 L, ‖a (x : L)‖ < 1 ↔ ‖b (x : L)‖ < 1) (x : L) (hx : ‖a x‖ ≤ 1) :
    ‖b x‖ ≤ 1 := by
  classical
  have hb : ∀ y : 𝓞 L, y ∈ smallIdeal a ↔ ‖b (y : L)‖ < 1 := fun y => (mem_smallIdeal a y).trans (h y)
  have := smallIdeal_isPrime a

  obtain ⟨u, w, hw, rfl⟩ := IsFractionRing.div_surjective (𝓞 L) x
  change ‖a ((u : L) / (w : L))‖ ≤ 1 at hx
  change ‖b ((u : L) / (w : L))‖ ≤ 1
  have hw0 : (w : L) ≠ 0 := by
    have := nonZeroDivisors.ne_zero hw
    exact_mod_cast this

  obtain ⟨r, s, hs, hrs⟩ := exists_local_dvd (smallIdeal a) (smallIdeal_ne_bot a) u w
  have hs0 : (s : L) ≠ 0 := by
    intro h0
    apply hs
    have : s = 0 := by exact_mod_cast h0
    rw [this]
    exact (smallIdeal a).zero_mem
  have hbs : ‖b (s : L)‖ = 1 := norm_eq_one b s (fun hlt => hs ((hb s).mpr hlt))
  have has : ‖a (s : L)‖ = 1 := norm_eq_one a s (fun hlt => hs ((mem_smallIdeal a s).mpr hlt))
  rcases hrs with h1 | h1
  ·
    have h1' : (u : L) * r = w * s := by exact_mod_cast congrArg (fun z : 𝓞 L => (z : L)) h1
    have hr0 : (r : L) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at h1'
      exact mul_ne_zero hw0 hs0 h1'.symm
    have e : (u : L) / w = s / r := by
      rw [div_eq_div_iff hw0 hr0]
      linear_combination h1'
    rw [e] at hx ⊢
    rw [map_div₀, norm_div, has] at hx
    have hpos : 0 < ‖a (r : L)‖ := norm_pos_iff.mpr ((map_ne_zero a).mpr hr0)
    have har : ¬ ‖a (r : L)‖ < 1 := by
      intro hlt
      rw [div_le_iff₀ hpos] at hx
      linarith
    have hbr : ‖b (r : L)‖ = 1 := norm_eq_one b r (fun hlt => har ((h r).mpr hlt))
    rw [map_div₀, norm_div, hbs, hbr, div_one]
  ·
    have h1' : (w : L) * r = u * s := by exact_mod_cast congrArg (fun z : 𝓞 L => (z : L)) h1
    have e : (u : L) / w = r / s := by
      rw [div_eq_div_iff hw0 hs0]
      linear_combination -h1'
    rw [e, map_div₀, norm_div, hbs, div_one]
    exact norm_int_le_one b r

/- English proof (translation)
Conclude with `⟨le_one_of_le_one a b h x, le_one_of_le_one b a (fun y => (h y).symm) x⟩`.
-/
theorem norm_le_one_iff {L : Type} [Field L] [NumberField L] {l : ℕ} [Fact (Nat.Prime l)]
    (a b : L →+* Formalism.ConjugateSelfDual.Qbar l)
    (h : ∀ x : 𝓞 L, ‖a (x : L)‖ < (1 : ℝ) ↔ ‖b (x : L)‖ < (1 : ℝ)) (x : L) :
    ‖a x‖ ≤ (1 : ℝ) ↔ ‖b x‖ ≤ (1 : ℝ) := by
  exact ⟨le_one_of_le_one a b h x, le_one_of_le_one b a (fun y => (h y).symm) x⟩

end GlobalTheory.SmallPrimeIdeal
