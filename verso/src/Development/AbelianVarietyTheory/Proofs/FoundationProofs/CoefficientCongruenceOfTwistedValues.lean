import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotZeroChi
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormLeOneOfIsIntegralBis

noncomputable section

open GlobalTheory.KZ GlobalTheory.Ord2 UpperTheory.V.HV Formalism.ConjugateSelfDual PowerSeries

namespace GlobalTheory.KZ.CoefVal

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.IntegralNormAlgebraMap.norm_le_one_of_isIntegral`. Consider the case `exact _root_.GlobalTheory.IntegralNormAlgebraMap.norm_le_one_of_isIntegral`. Consider the case `(apply _root_.GlobalTheory.IntegralNormAlgebraMap.norm_le_one_of_isIntegral <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.IntegralNormAlgebraMap.norm_le_one_of_isIntegral <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.IntegralNormAlgebraMap.norm_le_one_of_isIntegral <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.IntegralNormAlgebraMap.norm_le_one_of_isIntegral ..)`.
-/
private theorem norm_le_one_of_int' (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.IntegralNormAlgebraMap.norm_le_one_of_isIntegral
  | exact _root_.GlobalTheory.IntegralNormAlgebraMap.norm_le_one_of_isIntegral
  | (apply _root_.GlobalTheory.IntegralNormAlgebraMap.norm_le_one_of_isIntegral <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralNormAlgebraMap.norm_le_one_of_isIntegral <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralNormAlgebraMap.norm_le_one_of_isIntegral <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralNormAlgebraMap.norm_le_one_of_isIntegral ..)

/- English proof (translation)
Use `haveI := c.fin`. Conclude with `norm_le_one_of_int' x ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨x, hx⟩ : c.O)).map c.O.val)`.
-/
theorem norm_le_one_of_mem (c : Coef l) {x : PadicAlgCl l} (hx : x ∈ c.O) : ‖x‖ ≤ 1 := by
  haveI := c.fin
  exact norm_le_one_of_int' x ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨x, hx⟩ : c.O)).map c.O.val)

/- English proof (translation)
Establish `h1 : ‖((u : c.O) : PadicAlgCl l)‖ * ‖(((u⁻¹ : c.Oˣ) : c.O) : PadicAlgCl l)‖ = 1`. Rewrite using `[← norm_mul, ← Subalgebra.coe_mul, Units.mul_inv]`. Simplify using the standard rewrite rules. Establish `h2` using `norm_le_one_of_mem c (u : c.O).2`. Establish `h3` using `norm_le_one_of_mem c ((u⁻¹ : c.Oˣ) : c.O).2`.

Establish `h4` using `norm_nonneg ((u : c.O) : PadicAlgCl l)`. Establish `h5` using `norm_nonneg (((u⁻¹ : c.Oˣ) : c.O) : PadicAlgCl l)`. Use `le_antisymm h2 ?_` and prove the remaining obligations. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem norm_unit (c : Coef l) (u : c.Oˣ) : ‖((u : c.O) : PadicAlgCl l)‖ = 1 := by
  have h1 : ‖((u : c.O) : PadicAlgCl l)‖ * ‖(((u⁻¹ : c.Oˣ) : c.O) : PadicAlgCl l)‖ = 1 := by
    rw [← norm_mul, ← Subalgebra.coe_mul, Units.mul_inv]; simp
  have h2 := norm_le_one_of_mem c (u : c.O).2
  have h3 := norm_le_one_of_mem c ((u⁻¹ : c.Oˣ) : c.O).2
  have h4 := norm_nonneg ((u : c.O) : PadicAlgCl l)
  have h5 := norm_nonneg (((u⁻¹ : c.Oˣ) : c.O) : PadicAlgCl l)
  refine le_antisymm h2 ?_
  nlinarith

/- English proof (translation)
Rewrite using `[← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), norm_algebraMap', Padic.norm_p]`.
-/
theorem norm_l : ‖((l : ℕ) : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), norm_algebraMap', Padic.norm_p]

/- English proof (translation)
Use `haveI := c.dvr`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible c.O`. Establish `key : ∀ y : c.O, y ≠ 0 → ∃ j : ℕ, ‖(y : PadicAlgCl l)‖ = ‖(ϖ : PadicAlgCl l)‖ ^ j`. Introduce `y hy`. Take `⟨n, u, hu⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ`.

Use `⟨n, ?_⟩` and prove the remaining obligations. Rewrite using `[hu, Subalgebra.coe_mul, Subalgebra.coe_pow, norm_mul, norm_pow, norm_unit, one_mul]`. Establish `hlp : (l : ℝ)⁻¹ < 1` using `inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)`. Establish `hl0 : ((l : ℕ) : c.O) ≠ 0`. Introduce `h`.

Establish `h' : (((l : ℕ) : c.O) : PadicAlgCl l) = 0` using `by rw [h]; rfl`. Establish `: ((l : ℕ) : PadicAlgCl l) = 0` using `by simpa using h'`. Conclude with `(Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) this`. Take `⟨n, u, hu⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ`. Establish `hnorm : ‖((l : ℕ) : PadicAlgCl l)‖ = ‖(ϖ : PadicAlgCl l)‖ ^ n`.

Establish `h' : (((l : ℕ) : c.O) : PadicAlgCl l) = ((u : c.O) : PadicAlgCl l) * (ϖ : PadicAlgCl l) ^ n`. Rewrite using `[hu, Subalgebra.coe_mul, Subalgebra.coe_pow]`. Establish `h'' : (((l : ℕ) : c.O) : PadicAlgCl l) = ((l : ℕ) : PadicAlgCl l)` using `by simp`. Rewrite using `[← h'', h', norm_mul, norm_pow, norm_unit, one_mul]`. Use `⟨ϖ, n, ?_, hnorm, ?_⟩` and prove the remaining obligations.

Break down `Nat.eq_zero_or_pos n with h | h` into its components or cases. It suffices to derive a contradiction. Rewrite `hnorm` using `[h, pow_zero, norm_l]`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `h`.

Introduce `x hx`. Distinguish the cases in `h : x = 0`. Conclude with `Or.inl h`. Use `right`. Conclude with `key ⟨x, hx⟩ (fun h' => h (congrArg Subtype.val h'))`.
-/
theorem exists_unif (c : Coef l) : ∃ ϖ : PadicAlgCl l, ∃ s : ℕ, 0 < s ∧ ‖((l : ℕ) : PadicAlgCl l)‖ = ‖ϖ‖ ^ s ∧
    ∀ x ∈ c.O, x = 0 ∨ ∃ j : ℕ, ‖x‖ = ‖ϖ‖ ^ j := by
  haveI := c.dvr
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  have key : ∀ y : c.O, y ≠ 0 → ∃ j : ℕ, ‖(y : PadicAlgCl l)‖ = ‖(ϖ : PadicAlgCl l)‖ ^ j := by
    intro y hy
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ
    refine ⟨n, ?_⟩
    rw [hu, Subalgebra.coe_mul, Subalgebra.coe_pow, norm_mul, norm_pow, norm_unit, one_mul]
  have hlp : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  have hl0 : ((l : ℕ) : c.O) ≠ 0 := by
    intro h
    have h' : (((l : ℕ) : c.O) : PadicAlgCl l) = 0 := by rw [h]; rfl
    have : ((l : ℕ) : PadicAlgCl l) = 0 := by simpa using h'
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) this
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ
  have hnorm : ‖((l : ℕ) : PadicAlgCl l)‖ = ‖(ϖ : PadicAlgCl l)‖ ^ n := by
    have h' : (((l : ℕ) : c.O) : PadicAlgCl l) = ((u : c.O) : PadicAlgCl l) * (ϖ : PadicAlgCl l) ^ n := by
      rw [hu, Subalgebra.coe_mul, Subalgebra.coe_pow]
    have h'' : (((l : ℕ) : c.O) : PadicAlgCl l) = ((l : ℕ) : PadicAlgCl l) := by simp
    rw [← h'', h', norm_mul, norm_pow, norm_unit, one_mul]
  refine ⟨ϖ, n, ?_, hnorm, ?_⟩
  · rcases Nat.eq_zero_or_pos n with h | h
    · exfalso
      rw [h, pow_zero, norm_l] at hnorm
      linarith
    · exact h
  · intro x hx
    by_cases h : x = 0
    · exact Or.inl h
    · right
      exact key ⟨x, hx⟩ (fun h' => h (congrArg Subtype.val h'))

/- English proof (translation)
Establish `: ‖z‖ ^ N = 1` using `by rw [← norm_pow, hz, norm_one]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) hN.ne').1 this`.
-/
theorem norm_eq_one_of_pow {z : PadicAlgCl l} {N : ℕ} (hN : 0 < N) (hz : z ^ N = 1) : ‖z‖ = 1 := by
  have : ‖z‖ ^ N = 1 := by rw [← norm_pow, hz, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hN.ne').1 this

/- English proof (translation)
Establish `: 1 - z ^ b = (1 - z) * ∑ i ∈ Finset.range b, z ^ i`. Rewrite using `[mul_comm, geom_sum_mul_neg]`. Rewrite using `[this, norm_mul]`. Use `mul_le_of_le_one_right (norm_nonneg _) ?_` and prove the remaining obligations. Conclude with `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun i _ => by rw [norm_pow, hz, one_pow])`.
-/
theorem norm_one_sub_pow_le {z : PadicAlgCl l} (hz : ‖z‖ = 1) (b : ℕ) : ‖1 - z ^ b‖ ≤ ‖1 - z‖ := by
  have : 1 - z ^ b = (1 - z) * ∑ i ∈ Finset.range b, z ^ i := by
    rw [mul_comm, geom_sum_mul_neg]
  rw [this, norm_mul]
  refine mul_le_of_le_one_right (norm_nonneg _) ?_
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
    (fun i _ => by rw [norm_pow, hz, one_pow])

/- English proof (translation)
Establish `hpos : 0 < l ^ (m + 1)` using `pow_pos (Fact.out : l.Prime).pos _`. Establish `hcyc` using `Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hz`. Establish `h1 : Polynomial.eval 1 (Polynomial.cyclotomic (l ^ (m + 1)) (PadicAlgCl l)) = l` using `Polynomial.eval_one_cyclotomic_prime_pow m`. Rewrite `h1` using `[hcyc, Polynomial.eval_prod]`. Simplify using `only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h1`.

Establish `hz1 : ‖z‖ = 1` using `norm_eq_one_of_pow hpos hz.pow_eq_one`. Establish `h2 : ∀ μ ∈ primitiveRoots (l ^ (m + 1)) (PadicAlgCl l), ‖1 - μ‖ = ‖1 - z‖`. Introduce `μ hμ`. Establish `hμ'` using `(mem_primitiveRoots hpos).1 hμ`. Establish `hμ1 : ‖μ‖ = 1` using `norm_eq_one_of_pow hpos hμ'.pow_eq_one`.

Take `⟨i, -, hi⟩` from `hz.eq_pow_of_pow_eq_one hμ'.pow_eq_one`. Take `⟨j, -, hj⟩` from `hμ'.eq_pow_of_pow_eq_one hz.pow_eq_one`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[← hi]`. Conclude with `norm_one_sub_pow_le hz1 i`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← h1, norm_prod, Finset.prod_congr rfl h2, Finset.prod_const, hz.card_primitiveRoots]`.
-/
theorem norm_one_sub_prim {z : PadicAlgCl l} {m : ℕ} (hz : IsPrimitiveRoot z (l ^ (m + 1))) :
    ‖1 - z‖ ^ Nat.totient (l ^ (m + 1)) = ‖((l : ℕ) : PadicAlgCl l)‖ := by
  have hpos : 0 < l ^ (m + 1) := pow_pos (Fact.out : l.Prime).pos _
  have hcyc := Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hz
  have h1 : Polynomial.eval 1 (Polynomial.cyclotomic (l ^ (m + 1)) (PadicAlgCl l)) = l :=
    Polynomial.eval_one_cyclotomic_prime_pow m
  rw [hcyc, Polynomial.eval_prod] at h1
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h1
  have hz1 : ‖z‖ = 1 := norm_eq_one_of_pow hpos hz.pow_eq_one
  have h2 : ∀ μ ∈ primitiveRoots (l ^ (m + 1)) (PadicAlgCl l), ‖1 - μ‖ = ‖1 - z‖ := by
    intro μ hμ
    have hμ' := (mem_primitiveRoots hpos).1 hμ
    have hμ1 : ‖μ‖ = 1 := norm_eq_one_of_pow hpos hμ'.pow_eq_one
    obtain ⟨i, -, hi⟩ := hz.eq_pow_of_pow_eq_one hμ'.pow_eq_one
    obtain ⟨j, -, hj⟩ := hμ'.eq_pow_of_pow_eq_one hz.pow_eq_one
    apply le_antisymm
    · rw [← hi]; exact norm_one_sub_pow_le hz1 i
    · calc ‖1 - z‖ = ‖1 - μ ^ j‖ := by rw [hj]
        _ ≤ ‖1 - μ‖ := norm_one_sub_pow_le hμ1 j
  rw [← h1, norm_prod, Finset.prod_congr rfl h2, Finset.prod_const, hz.card_primitiveRoots]

/- English proof (translation)
Introduce `l _ c F k m₁ hF hval n₀`. Establish `hlP : l.Prime` using `Fact.out`. Unfold `Cg`. Rewrite using `[sub_zero]`. Assume the negation of the conclusion as `hlt`.

Use `push_neg at hlt`. Take `⟨ϖ, s, hs, hls, hdisc⟩` from `exists_unif c`. Use `set q := ‖ϖ‖ with hq`. Establish `hlpos : (0 : ℝ) < (l : ℝ)⁻¹` using `by have := hlP.pos; positivity`. Establish `hlone : (l : ℝ)⁻¹ < 1` using `inv_lt_one_of_one_lt₀ (by exact_mod_cast hlP.one_lt)`.

Establish `hl0 : 0 < q ^ s` using `by rw [← hls, norm_l]; exact hlpos`. Establish `hl1 : q ^ s < 1` using `by rw [← hls, norm_l]; exact hlone`. Establish `hq0 : 0 < q`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`.

Establish `h0 : q = 0` using `le_antisymm hc (norm_nonneg _)`. Rewrite `hl0` using `[h0, zero_pow hs.ne']`. Conclude with `lt_irrefl _ hl0`. Establish `hq1 : q < 1` using `(pow_lt_one_iff_of_nonneg hq0.le hs.ne').1 hl1`. Establish `hlk : ‖((l : ℕ) : Qbar l) ^ k‖ = q ^ (s * k)`.

Rewrite using `[norm_pow, pow_mul]`. Use `congr 1`. Establish `hex : ∃ J, ∃ n, ‖F.coeff n‖ = q ^ J`. Break down `hdisc _ (hF n₀) with h | ⟨j, hj⟩` into its components or cases. It suffices to derive a contradiction.

Rewrite `hlt` using `[h, norm_zero]`. Conclude with `absurd hlt (not_lt.2 (norm_nonneg _))`. Conclude with `⟨j, n₀, hj⟩`. Establish `hJ` using `Nat.find_spec hex`. Use `set J := Nat.find hex with hJdef`.

Establish `hle : ∀ n, ‖F.coeff n‖ ≤ q ^ J`. Introduce `n`. Break down `hdisc _ (hF n) with h | ⟨j, hj⟩` into its components or cases. Rewrite using `[h, norm_zero]`. Check the signs of the components of the expression.

Rewrite using `[hj]`. Conclude with `pow_le_pow_of_le_one hq0.le hq1.le (Nat.find_min' hex ⟨n, hj⟩)`. Establish `hd` using `Nat.find_spec hJ`. Use `set d := Nat.find hJ with hddef`. Establish `hbefore : ∀ n < d, ‖F.coeff n‖ ≤ q ^ (J + 1)`.

Introduce `n hn`. Break down `hdisc _ (hF n) with h | ⟨j, hj⟩` into its components or cases. Rewrite using `[h, norm_zero]`. Check the signs of the components of the expression. Rewrite using `[hj]`.

Apply `pow_le_pow_of_le_one hq0.le hq1.le` to reduce the goal to its premises. Establish `h1 : J ≤ j` using `Nat.find_min' hex ⟨n, hj⟩`. Establish `h2 : j ≠ J` using `fun h => Nat.find_min hJ hn (by rw [hj, h])`. Use linear arithmetic over natural numbers and integers. Establish `hJk : J + 1 ≤ s * k`.

Establish `h1 : q ^ (s * k) < q ^ J`. Rewrite using `[← hlk]`. Conclude with `lt_of_lt_of_le hlt (hle n₀)`. Use `(pow_lt_pow_iff_right_of_lt_one₀ hq0 hq1).1 h1` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Use `set M := m₁ + d * s + 1 with hM`. Use `haveI : NeZero (l ^ (M + 1)) := ⟨pow_ne_zero _ hlP.ne_zero⟩`. Take `⟨z, hz⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl l) (l ^ (M + 1))`. Establish `h` using `hval (M + 1) (by omega) z hz`. Unfold `Cg at h`.

Rewrite `h` using `[sub_zero, hlk]`. Use `set a := ‖z - 1‖ with ha`. Establish `hphi` using `norm_one_sub_prim hz`. Rewrite `hphi` using `[norm_sub_rev, ← ha, hls]`. Establish `htot : d * s < Nat.totient (l ^ (M + 1))`.

Rewrite using `[Nat.totient_prime_pow_succ hlP]`. Establish `h1 : M < l ^ M` using `Nat.lt_pow_self hlP.one_lt`. Establish `h2 : 1 ≤ l - 1` using `by have := hlP.two_le; omega`. Combine the equalities or inequalities in the displayed calculation. Establish `htpos : 0 < Nat.totient (l ^ (M + 1))` using `by omega`.

Establish `ha0 : 0 < a`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Establish `h0 : a = 0` using `le_antisymm hc (norm_nonneg _)`. Rewrite `hphi` using `[h0, zero_pow htpos.ne']`.

Rewrite `hl0` using `[← hphi]`. Conclude with `lt_irrefl _ hl0`. Establish `ha1 : a < 1`. Establish `: a ^ Nat.totient (l ^ (M + 1)) < 1` using `by rw [hphi]; exact hl1`. Conclude with `(pow_lt_one_iff_of_nonneg ha0.le htpos.ne').1 this`.

Establish `hqa : q < a ^ d`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Establish `h1 : a ^ (d * s) ≤ a ^ Nat.totient (l ^ (M + 1))`. Rewrite using `[hphi, pow_mul]; exact pow_le_pow_left₀ (by positivity) hc s`.

Use `(pow_le_pow_iff_right_of_lt_one₀ ha0 ha1).1 h1` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `set N := l ^ (3 * (M + 1)) with hN`. Establish `hdN : d < N`. Establish `: 3 * (M + 1) < l ^ (3 * (M + 1))` using `Nat.lt_pow_self hlP.one_lt`.

Establish `: d ≤ d * s` using `Nat.le_mul_of_pos_right d hs`. Use linear arithmetic over natural numbers and integers. Establish `hdmem : d ∈ Finset.range N` using `Finset.mem_range.2 hdN`. Establish `hsplit : tval F N z = F.coeff d * (z - 1) ^ d + ∑ n ∈ (Finset.range N).erase d, F.coeff n * (z - 1) ^ n`. Unfold `tval`.

Conclude with `(Finset.add_sum_erase _ _ hdmem).symm`. Establish `hmain : ‖F.coeff d * (z - 1) ^ d‖ = q ^ J * a ^ d`. Rewrite using `[norm_mul, norm_pow, hd]`. Establish `hB : max (q ^ (J + 1)) (q ^ J * a ^ (d + 1)) < q ^ J * a ^ d`. Establish `hqJ : 0 < q ^ J` using `pow_pos hq0 J`.

Apply `max_lt` to reduce the goal to its premises. Rewrite using `[pow_succ]`. Conclude with `mul_lt_mul_of_pos_left hqa hqJ`. Rewrite using `[pow_succ, ← mul_assoc]`. Conclude with `mul_lt_of_lt_one_right (mul_pos hqJ (pow_pos ha0 d)) ha1`.

Establish `hrest : ‖∑ n ∈ (Finset.range N).erase d, F.coeff n * (z - 1) ^ n‖ ≤ max (q ^ (J + 1)) (q ^ J * a ^ (d + 1))`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun n hn => ?_` and prove the remaining obligations. Establish `hnd : n ≠ d` using `(Finset.mem_erase.1 hn).1`. Rewrite using `[norm_mul, norm_pow, ← ha]`. Break down `lt_or_gt_of_ne hnd with h' | h'` into its components or cases.

Use `le_max_of_le_left ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `le_max_of_le_right ?_` and prove the remaining obligations. Conclude with `mul_le_mul (hle n) (pow_le_pow_of_le_one ha0.le ha1.le h') (by positivity) (by positivity)`. Establish `hval' : ‖tval F N z‖ = q ^ J * a ^ d`.

Rewrite using `[hsplit, ← hmain]`. Establish `hne : ‖F.coeff d * (z - 1) ^ d‖ ≠ ‖∑ n ∈ (Finset.range N).erase d, F.coeff n * (z - 1) ^ n‖`. Rewrite using `[hmain]`. Conclude with `(lt_of_le_of_lt hrest hB).ne'`. Rewrite using `[IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, max_eq_left]`.

Rewrite using `[hmain]`. Conclude with `hrest.trans hB.le`. Rewrite `h` using `[hval']`. Establish `h1 : q ^ (s * k) ≤ q ^ (J + 1)` using `pow_le_pow_of_le_one hq0.le hq1.le hJk`. Establish `h2 : q ^ (J + 1) < q ^ J * a ^ d`.

Rewrite using `[pow_succ]`. Conclude with `mul_lt_mul_of_pos_left hqa (pow_pos hq0 J)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem coeff_cg_of_values : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (F : PowerSeries (Qbar l)) (k m₁ : ℕ),
    (∀ n, F.coeff n ∈ c.O) → (∀ m, m₁ ≤ m → ∀ z : Qbar l, IsPrimitiveRoot z (l ^ m) → Cg k (tval F (l ^ (3 * m)) z) 0) →
    ∀ n, Cg k (F.coeff n) 0 := by
  intro l _ c F k m₁ hF hval n₀
  have hlP : l.Prime := Fact.out
  unfold Cg
  rw [sub_zero]
  by_contra hlt
  push_neg at hlt
  obtain ⟨ϖ, s, hs, hls, hdisc⟩ := exists_unif c
  set q := ‖ϖ‖ with hq
  have hlpos : (0 : ℝ) < (l : ℝ)⁻¹ := by have := hlP.pos; positivity
  have hlone : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hlP.one_lt)
  have hl0 : 0 < q ^ s := by rw [← hls, norm_l]; exact hlpos
  have hl1 : q ^ s < 1 := by rw [← hls, norm_l]; exact hlone
  have hq0 : 0 < q := by
    by_contra hc
    push_neg at hc
    have h0 : q = 0 := le_antisymm hc (norm_nonneg _)
    rw [h0, zero_pow hs.ne'] at hl0
    exact lt_irrefl _ hl0
  have hq1 : q < 1 := (pow_lt_one_iff_of_nonneg hq0.le hs.ne').1 hl1
  have hlk : ‖((l : ℕ) : Qbar l) ^ k‖ = q ^ (s * k) := by
    rw [norm_pow, pow_mul]; congr 1
  have hex : ∃ J, ∃ n, ‖F.coeff n‖ = q ^ J := by
    rcases hdisc _ (hF n₀) with h | ⟨j, hj⟩
    · exfalso; rw [h, norm_zero] at hlt; exact absurd hlt (not_lt.2 (norm_nonneg _))
    · exact ⟨j, n₀, hj⟩
  classical
  have hJ := Nat.find_spec hex
  set J := Nat.find hex with hJdef
  have hle : ∀ n, ‖F.coeff n‖ ≤ q ^ J := by
    intro n
    rcases hdisc _ (hF n) with h | ⟨j, hj⟩
    · rw [h, norm_zero]; positivity
    · rw [hj]; exact pow_le_pow_of_le_one hq0.le hq1.le (Nat.find_min' hex ⟨n, hj⟩)
  have hd := Nat.find_spec hJ
  set d := Nat.find hJ with hddef
  have hbefore : ∀ n < d, ‖F.coeff n‖ ≤ q ^ (J + 1) := by
    intro n hn
    rcases hdisc _ (hF n) with h | ⟨j, hj⟩
    · rw [h, norm_zero]; positivity
    · rw [hj]
      apply pow_le_pow_of_le_one hq0.le hq1.le
      have h1 : J ≤ j := Nat.find_min' hex ⟨n, hj⟩
      have h2 : j ≠ J := fun h => Nat.find_min hJ hn (by rw [hj, h])
      omega
  have hJk : J + 1 ≤ s * k := by
    have h1 : q ^ (s * k) < q ^ J := by
      rw [← hlk]; exact lt_of_lt_of_le hlt (hle n₀)
    have := (pow_lt_pow_iff_right_of_lt_one₀ hq0 hq1).1 h1
    omega

  set M := m₁ + d * s + 1 with hM
  haveI : NeZero (l ^ (M + 1)) := ⟨pow_ne_zero _ hlP.ne_zero⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl l) (l ^ (M + 1))
  have h := hval (M + 1) (by omega) z hz
  unfold Cg at h
  rw [sub_zero, hlk] at h
  set a := ‖z - 1‖ with ha
  have hphi := norm_one_sub_prim hz
  rw [norm_sub_rev, ← ha, hls] at hphi
  have htot : d * s < Nat.totient (l ^ (M + 1)) := by
    rw [Nat.totient_prime_pow_succ hlP]
    have h1 : M < l ^ M := Nat.lt_pow_self hlP.one_lt
    have h2 : 1 ≤ l - 1 := by have := hlP.two_le; omega
    calc d * s < M := by omega
      _ < l ^ M := h1
      _ ≤ l ^ M * (l - 1) := Nat.le_mul_of_pos_right _ h2
  have htpos : 0 < Nat.totient (l ^ (M + 1)) := by omega
  have ha0 : 0 < a := by
    by_contra hc
    push_neg at hc
    have h0 : a = 0 := le_antisymm hc (norm_nonneg _)
    rw [h0, zero_pow htpos.ne'] at hphi
    rw [← hphi] at hl0
    exact lt_irrefl _ hl0
  have ha1 : a < 1 := by
    have : a ^ Nat.totient (l ^ (M + 1)) < 1 := by rw [hphi]; exact hl1
    exact (pow_lt_one_iff_of_nonneg ha0.le htpos.ne').1 this
  have hqa : q < a ^ d := by
    by_contra hc
    push_neg at hc
    have h1 : a ^ (d * s) ≤ a ^ Nat.totient (l ^ (M + 1)) := by
      rw [hphi, pow_mul]; exact pow_le_pow_left₀ (by positivity) hc s
    have := (pow_le_pow_iff_right_of_lt_one₀ ha0 ha1).1 h1
    omega

  set N := l ^ (3 * (M + 1)) with hN
  have hdN : d < N := by
    have : 3 * (M + 1) < l ^ (3 * (M + 1)) := Nat.lt_pow_self hlP.one_lt
    have : d ≤ d * s := Nat.le_mul_of_pos_right d hs
    omega
  have hdmem : d ∈ Finset.range N := Finset.mem_range.2 hdN
  have hsplit : tval F N z = F.coeff d * (z - 1) ^ d +
      ∑ n ∈ (Finset.range N).erase d, F.coeff n * (z - 1) ^ n := by
    unfold tval
    exact (Finset.add_sum_erase _ _ hdmem).symm
  have hmain : ‖F.coeff d * (z - 1) ^ d‖ = q ^ J * a ^ d := by
    rw [norm_mul, norm_pow, hd]
  have hB : max (q ^ (J + 1)) (q ^ J * a ^ (d + 1)) < q ^ J * a ^ d := by
    have hqJ : 0 < q ^ J := pow_pos hq0 J
    apply max_lt
    · rw [pow_succ]; exact mul_lt_mul_of_pos_left hqa hqJ
    · rw [pow_succ, ← mul_assoc]
      exact mul_lt_of_lt_one_right (mul_pos hqJ (pow_pos ha0 d)) ha1
  have hrest : ‖∑ n ∈ (Finset.range N).erase d, F.coeff n * (z - 1) ^ n‖ ≤
      max (q ^ (J + 1)) (q ^ J * a ^ (d + 1)) := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun n hn => ?_
    have hnd : n ≠ d := (Finset.mem_erase.1 hn).1
    rw [norm_mul, norm_pow, ← ha]
    rcases lt_or_gt_of_ne hnd with h' | h'
    · refine le_max_of_le_left ?_
      calc ‖F.coeff n‖ * a ^ n ≤ q ^ (J + 1) * 1 :=
            mul_le_mul (hbefore n h') (pow_le_one₀ ha0.le ha1.le) (by positivity) (by positivity)
        _ = q ^ (J + 1) := mul_one _
    · refine le_max_of_le_right ?_
      exact mul_le_mul (hle n) (pow_le_pow_of_le_one ha0.le ha1.le h') (by positivity) (by positivity)
  have hval' : ‖tval F N z‖ = q ^ J * a ^ d := by
    rw [hsplit, ← hmain]
    have hne : ‖F.coeff d * (z - 1) ^ d‖ ≠ ‖∑ n ∈ (Finset.range N).erase d, F.coeff n * (z - 1) ^ n‖ := by
      rw [hmain]; exact (lt_of_le_of_lt hrest hB).ne'
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, max_eq_left]
    rw [hmain]; exact hrest.trans hB.le
  rw [hval'] at h
  have h1 : q ^ (s * k) ≤ q ^ (J + 1) := pow_le_pow_of_le_one hq0.le hq1.le hJk
  have h2 : q ^ (J + 1) < q ^ J * a ^ d := by
    rw [pow_succ]; exact mul_lt_mul_of_pos_left hqa (pow_pos hq0 J)
  linarith

end GlobalTheory.KZ.CoefVal
