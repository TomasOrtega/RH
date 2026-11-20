import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SquarefreeLabelTorusMassDivisorBound
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumPrimePowerPartPowSubOneLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumLeProdOfTwoLeNat
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowPadicValEqOneOfPrimePow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SquarefreeLabelTorusMassUnionBounds

open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare

/- English proof (translation)
Use `haveI : NeZero g := ⟨(Fact.out : g.Prime).ne_zero⟩`. Establish `hi : IsIntegral (ZMod g) x` using `Algebra.IsIntegral.isIntegral x`. Use `haveI := IntermediateField.adjoin.finiteDimensional hi`. Use `haveI : Finite (IntermediateField.adjoin (ZMod g) {x}) := Module.finite_of_finite (ZMod g)`. Use `haveI : Fintype (IntermediateField.adjoin (ZMod g) {x}) := Fintype.ofFinite _`.

Set `y : IntermediateField.adjoin (ZMod g) {x}` to `⟨x, IntermediateField.mem_adjoin_simple_self _ x⟩`. Establish `hy : y ≠ 0` using `fun h => hx (congrArg Subtype.val h)`. Establish `h1` using `FiniteField.pow_card_sub_one_eq_one y hy`. Rewrite `h1` using `[Module.card_eq_pow_finrank (K := ZMod g), ZMod.card, IntermediateField.adjoin.finrank hi]`. Simplify `congrArg Subtype.val h1` using `[y]`.
-/
theorem avoid_pow_natDegree_minpoly {g : ℕ} [Fact g.Prime] {x : AlgebraicClosure (ZMod g)} (hx : x ≠ 0) :
    x ^ (g ^ (minpoly (ZMod g) x).natDegree - 1) = 1 := by
  haveI : NeZero g := ⟨(Fact.out : g.Prime).ne_zero⟩
  have hi : IsIntegral (ZMod g) x := Algebra.IsIntegral.isIntegral x
  haveI := IntermediateField.adjoin.finiteDimensional hi
  haveI : Finite (IntermediateField.adjoin (ZMod g) {x}) := Module.finite_of_finite (ZMod g)
  haveI : Fintype (IntermediateField.adjoin (ZMod g) {x}) := Fintype.ofFinite _
  let y : IntermediateField.adjoin (ZMod g) {x} := ⟨x, IntermediateField.mem_adjoin_simple_self _ x⟩
  have hy : y ≠ 0 := fun h => hx (congrArg Subtype.val h)
  have h1 := FiniteField.pow_card_sub_one_eq_one y hy
  rw [Module.card_eq_pow_finrank (K := ZMod g), ZMod.card, IntermediateField.adjoin.finrank hi] at h1
  simpa [y] using congrArg Subtype.val h1

/- English proof (translation)
Establish `hg : 1 < g` using `(Fact.out : g.Prime).one_lt`. Establish `hn : 0 < g ^ d - 1` using `Nat.sub_pos_of_lt (Nat.one_lt_pow (by omega) hg)`. Establish `hdv : g - 1 ∣ g ^ d - 1` using `by simpa using Nat.sub_dvd_pow_sub_pow g 1 d`. Use `set n := g ^ d - 1 with hndef`. Use `set c' : AlgebraicClosure (ZMod g) := algebraMap (ZMod g) (AlgebraicClosure (ZMod g)) (c : ZMod g) with hc'`.

Establish `hc0 : c' ≠ 0` using `by simp [hc']`. Establish `hcn : c' ^ n = 1`. Take `⟨k, hk⟩` from `hdv`. Rewrite using `[hk, pow_mul, hc', ← map_pow, ZMod.pow_card_sub_one_eq_one c.ne_zero, map_one, one_pow]`. Establish `hS` using `fun l (hl : l ∈ n.primeFactors) => (GlobalTheory.BadShare.samePart_roots_finite_ncard (AlgebraicClosure (ZMod g)) n l hn (Nat.prime_of_mem_primeFactors hl)).2 c'`.

Set `T : Finset (AlgebraicClosure (ZMod g))` to `n.primeFactors.attach.biUnion fun l => (hS l.1 l.2).1.toFinset`. Establish `hT : T.card ≤ ∑ l ∈ n.primeFactors, l ^ padicValNat l n`. Use `Finset.card_biUnion_le.trans ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_attach n.primeFactors]`. Use `Finset.sum_le_sum fun l _ => ?_` and prove the remaining obligations.

Rewrite using `[← Set.ncard_eq_toFinset_card _ (hS l.1 l.2).1]`. Conclude with `(hS l.1 l.2).2`. Use `le_trans ?_ hT` and prove the remaining obligations. Use `set B := (sqSet g d).filter fun P => Irreducible P ∧ ¬ RootsAvoid g c P with hB`. Establish `h1 : ∑ P ∈ B, (T.filter fun x => minpoly (ZMod g) x = P).card ≤ T.card`.

Rewrite using `[Finset.sum_card_fiberwise_eq_card_filter]`. Conclude with `Finset.card_filter_le _ _`. Use `le_trans ?_ h1` and prove the remaining obligations. Rewrite using `[mul_comm, ← smul_eq_mul]`. Use `Finset.card_nsmul_le_sum _ _ _ fun P hP => ?_` and prove the remaining obligations.

Take `⟨hP1, hirr, hbad⟩` from `Finset.mem_filter.1 hP`. Take `⟨hm, hdeg, -, h0⟩` from `mem_sqSet.1 hP1`. Rewrite `hbad` using `[rootsAvoid_iff h0]`. Use `push Not at hbad`. Take `⟨l, hl, -, x, hx, a, ha⟩` from `hbad`.

Establish `hmin : ∀ y ∈ P.aroots (AlgebraicClosure (ZMod g)), minpoly (ZMod g) y = P` using `fun y hy => (minpoly.eq_of_irreducible_of_monic hirr (mem_aroots.1 hy).2 hm).symm`. Establish `hdvd : P ∣ X ^ (l ^ a) - C ((c : ZMod g) ^ (l ^ a))`. Rewrite using `[← hmin x hx, minpoly.dvd_iff]`. Simplify using `[ha, hc']`. Establish `hcard : (P.aroots (AlgebraicClosure (ZMod g))).toFinset.card = d`.

Establish `hsep : P.Separable` using `PerfectField.separable_of_irreducible hirr`. Use `Polynomial.card_rootSet_eq_natDegree (K := AlgebraicClosure (ZMod g)) hsep (IsAlgClosed.splits _)` as an intermediate fact. Rewrite using `[← hdeg, ← this]`. Simplify using `only [rootSet, Finset.coe_sort_coe]`. Use `(Fintype.card_coe _).symm` and compare the differences between its conclusion and the goal.

Rewrite using `[← hcard]`. Use `Finset.card_le_card fun y hy => ?_` and prove the remaining obligations. Rewrite `hy` using `[Multiset.mem_toFinset]`. Establish `hy0` using `root_ne_zero h0 hy`. Establish `hyn : y ^ n = 1`.

Use `avoid_pow_natDegree_minpoly hy0` as an intermediate fact. Rewrite `this` using `[hmin y hy, hdeg]`. Then use the resulting hypothesis. Establish `hya : y ^ (l ^ a) = c' ^ (l ^ a)`. Establish `h3 : minpoly (ZMod g) y ∣ X ^ (l ^ a) - C ((c : ZMod g) ^ (l ^ a))` using `by rwa [hmin y hy]`. Rewrite `h3` using `[minpoly.dvd_iff]`.

Simplify `h3` using `[sub_eq_zero, hc']`. Use `Finset.mem_filter.2 ⟨?_, hmin y hy⟩` and prove the remaining obligations. Simplify using `only [T, Finset.mem_biUnion, Finset.mem_attach, true_and, Set.Finite.mem_toFinset, Set.mem_setOf_eq]`. Distinguish the cases in `hln : l ∣ n`. Conclude with `⟨⟨l, Nat.mem_primeFactors.2 ⟨hl, hln, hn.ne'⟩⟩, hyn, (samePart_iff_of_ne_zero hl hy0 hc0).2 ⟨a, hya⟩⟩`.

Establish `: y = c'` using `eq_of_pow_eq ((hl.coprime_iff_not_dvd.2 hln).symm) hyn hcn hn.ne' hya`. Use `⟨⟨2, Nat.mem_primeFactors.2 ⟨Nat.prime_two, h2.trans hdv, hn.ne'⟩⟩, hyn, ?_⟩` and prove the remaining obligations. Rewrite using `[this]`. Both sides reduce to the same expression.
-/
theorem avoid_card_irreducible_le {g : ℕ} [Fact g.Prime] (c : (ZMod g)ˣ) (d : ℕ) (hd : 1 ≤ d) (h2 : 2 ∣ g - 1) :
    d * ((sqSet g d).filter fun P => Irreducible P ∧ ¬ RootsAvoid g c P).card ≤
      ∑ l ∈ (g ^ d - 1).primeFactors, l ^ padicValNat l (g ^ d - 1) := by
  have hg : 1 < g := (Fact.out : g.Prime).one_lt
  have hn : 0 < g ^ d - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow (by omega) hg)
  have hdv : g - 1 ∣ g ^ d - 1 := by simpa using Nat.sub_dvd_pow_sub_pow g 1 d
  set n := g ^ d - 1 with hndef
  set c' : AlgebraicClosure (ZMod g) := algebraMap (ZMod g) (AlgebraicClosure (ZMod g)) (c : ZMod g) with hc'
  have hc0 : c' ≠ 0 := by simp [hc']
  have hcn : c' ^ n = 1 := by
    obtain ⟨k, hk⟩ := hdv
    rw [hk, pow_mul, hc', ← map_pow, ZMod.pow_card_sub_one_eq_one c.ne_zero, map_one, one_pow]
  have hS := fun l (hl : l ∈ n.primeFactors) =>
    (GlobalTheory.BadShare.samePart_roots_finite_ncard (AlgebraicClosure (ZMod g)) n l hn (Nat.prime_of_mem_primeFactors hl)).2 c'
  let T : Finset (AlgebraicClosure (ZMod g)) :=
    n.primeFactors.attach.biUnion fun l => (hS l.1 l.2).1.toFinset
  have hT : T.card ≤ ∑ l ∈ n.primeFactors, l ^ padicValNat l n := by
    refine Finset.card_biUnion_le.trans ?_
    rw [← Finset.sum_attach n.primeFactors]
    refine Finset.sum_le_sum fun l _ => ?_
    rw [← Set.ncard_eq_toFinset_card _ (hS l.1 l.2).1]
    exact (hS l.1 l.2).2
  refine le_trans ?_ hT
  set B := (sqSet g d).filter fun P => Irreducible P ∧ ¬ RootsAvoid g c P with hB
  have h1 : ∑ P ∈ B, (T.filter fun x => minpoly (ZMod g) x = P).card ≤ T.card := by
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    exact Finset.card_filter_le _ _
  refine le_trans ?_ h1
  rw [mul_comm, ← smul_eq_mul]
  refine Finset.card_nsmul_le_sum _ _ _ fun P hP => ?_
  obtain ⟨hP1, hirr, hbad⟩ := Finset.mem_filter.1 hP
  obtain ⟨hm, hdeg, -, h0⟩ := mem_sqSet.1 hP1
  rw [rootsAvoid_iff h0] at hbad
  push Not at hbad
  obtain ⟨l, hl, -, x, hx, a, ha⟩ := hbad
  have hmin : ∀ y ∈ P.aroots (AlgebraicClosure (ZMod g)), minpoly (ZMod g) y = P := fun y hy =>
    (minpoly.eq_of_irreducible_of_monic hirr (mem_aroots.1 hy).2 hm).symm
  have hdvd : P ∣ X ^ (l ^ a) - C ((c : ZMod g) ^ (l ^ a)) := by
    rw [← hmin x hx, minpoly.dvd_iff]
    simp [ha, hc']
  have hcard : (P.aroots (AlgebraicClosure (ZMod g))).toFinset.card = d := by
    have hsep : P.Separable := PerfectField.separable_of_irreducible hirr
    have := Polynomial.card_rootSet_eq_natDegree (K := AlgebraicClosure (ZMod g)) hsep (IsAlgClosed.splits _)
    rw [← hdeg, ← this]
    simp only [rootSet, Finset.coe_sort_coe]
    convert (Fintype.card_coe _).symm
  rw [← hcard]
  refine Finset.card_le_card fun y hy => ?_
  rw [Multiset.mem_toFinset] at hy
  have hy0 := root_ne_zero h0 hy
  have hyn : y ^ n = 1 := by
    have := avoid_pow_natDegree_minpoly hy0
    rwa [hmin y hy, hdeg] at this
  have hya : y ^ (l ^ a) = c' ^ (l ^ a) := by
    have h3 : minpoly (ZMod g) y ∣ X ^ (l ^ a) - C ((c : ZMod g) ^ (l ^ a)) := by rwa [hmin y hy]
    rw [minpoly.dvd_iff] at h3
    simpa [sub_eq_zero, hc'] using h3
  refine Finset.mem_filter.2 ⟨?_, hmin y hy⟩
  simp only [T, Finset.mem_biUnion, Finset.mem_attach, true_and, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  by_cases hln : l ∣ n
  · exact ⟨⟨l, Nat.mem_primeFactors.2 ⟨hl, hln, hn.ne'⟩⟩, hyn, (samePart_iff_of_ne_zero hl hy0 hc0).2 ⟨a, hya⟩⟩
  · have : y = c' := eq_of_pow_eq ((hl.coprime_iff_not_dvd.2 hln).symm) hyn hcn hn.ne' hya
    refine ⟨⟨2, Nat.mem_primeFactors.2 ⟨Nat.prime_two, h2.trans hdv, hn.ne'⟩⟩, hyn, ?_⟩
    rw [this]; rfl

/- English proof (translation)
Proceed by induction on `N with`. Consider the case `zero => simp`. Consider the case `succ N ih`. Rewrite using `[Finset.sum_Icc_succ_top (by omega)]`. Establish `hg1 : 0 < g - 1` using `by linarith`.

Establish `hp : 1 ≤ g ^ N` using `one_le_pow₀ (by linarith)`. Establish `hq : 0 < g ^ (N + 1 + 1) - 1`. Establish `: g ^ (N + 1 + 1) = g ^ N * g * g` using `by ring`. Establish `h5 : 2 ≤ g ^ N * g` using `by nlinarith`. Rewrite using `[this]`.

Use the polynomial consequences of the given equalities and inequalities. Establish `e1 : (g - 1) / (g ^ (N + 1 + 1) - 1) ≤ 1 / g ^ (N + 1)`. Rewrite using `[div_le_div_iff₀ hq (by positivity)]`. Establish `: g ^ (N + 1 + 1) = g ^ N * g * g` using `by ring`. Rewrite using `[this, pow_succ]`.

Use the polynomial consequences of the given equalities and inequalities. Establish `e2 : 1 / ((N + 1 + 1 : ℕ) : ℝ) ≤ Real.log ((N + 1 + 1 : ℕ) : ℝ) - Real.log ((N + 1 : ℕ) : ℝ)`. Establish `h` using `Real.log_le_sub_one_of_pos (x := ((N + 1 : ℕ) : ℝ) / ((N + 1 + 1 : ℕ) : ℝ)) (by positivity)`. Rewrite `h` using `[Real.log_div (by positivity) (by positivity)]`. Establish `h' : ((N + 1 : ℕ) : ℝ) / ((N + 1 + 1 : ℕ) : ℝ) - 1 = - (1 / ((N + 1 + 1 : ℕ) : ℝ))` using `by push_cast; field_simp; ring`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `e3 : 1 / (((N + 1 + 1 : ℕ) : ℝ) * (g - 1)) ≤ (Real.log ((N + 1 + 1 : ℕ) : ℝ) - Real.log ((N + 1 : ℕ) : ℝ)) / (g - 1)`. Rewrite using `[← div_div]`. Conclude with `div_le_div_of_nonneg_right e2 hg1.le`. Establish `e4 : (1 - 1 / g ^ (N + 1) + Real.log ((N + 1 + 1 : ℕ) : ℝ)) / (g - 1) = (1 - 1 / g ^ N + Real.log ((N + 1 : ℕ) : ℝ)) / (g - 1) + 1 / g ^ (N + 1) + (Real.log ((N + 1 + 1 : ℕ) : ℝ) - Real.log ((N + 1 : ℕ) : ℝ)) / (g - 1)`.

Establish `: g ≠ 0` using `by linarith`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e4]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem avoid_sum_le (g : ℝ) (hg : 2 ≤ g) (N : ℕ) :
    ∑ d ∈ Finset.Icc 2 (N + 1), ((g - 1) / (g ^ d - 1) + 1 / (d * (g - 1))) ≤
      (1 - 1 / g ^ N + Real.log ((N + 1 : ℕ) : ℝ)) / (g - 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hg1 : 0 < g - 1 := by linarith
    have hp : 1 ≤ g ^ N := one_le_pow₀ (by linarith)
    have hq : 0 < g ^ (N + 1 + 1) - 1 := by
      have : g ^ (N + 1 + 1) = g ^ N * g * g := by ring
      have h5 : 2 ≤ g ^ N * g := by nlinarith
      rw [this]; nlinarith
    have e1 : (g - 1) / (g ^ (N + 1 + 1) - 1) ≤ 1 / g ^ (N + 1) := by
      rw [div_le_div_iff₀ hq (by positivity)]
      have : g ^ (N + 1 + 1) = g ^ N * g * g := by ring
      rw [this, pow_succ]; nlinarith
    have e2 : 1 / ((N + 1 + 1 : ℕ) : ℝ) ≤ Real.log ((N + 1 + 1 : ℕ) : ℝ) - Real.log ((N + 1 : ℕ) : ℝ) := by
      have h := Real.log_le_sub_one_of_pos (x := ((N + 1 : ℕ) : ℝ) / ((N + 1 + 1 : ℕ) : ℝ)) (by positivity)
      rw [Real.log_div (by positivity) (by positivity)] at h
      have h' : ((N + 1 : ℕ) : ℝ) / ((N + 1 + 1 : ℕ) : ℝ) - 1 = - (1 / ((N + 1 + 1 : ℕ) : ℝ)) := by
        push_cast; field_simp; ring
      linarith
    have e3 : 1 / (((N + 1 + 1 : ℕ) : ℝ) * (g - 1)) ≤
        (Real.log ((N + 1 + 1 : ℕ) : ℝ) - Real.log ((N + 1 : ℕ) : ℝ)) / (g - 1) := by
      rw [← div_div]
      exact div_le_div_of_nonneg_right e2 hg1.le
    have e4 : (1 - 1 / g ^ (N + 1) + Real.log ((N + 1 + 1 : ℕ) : ℝ)) / (g - 1) =
        (1 - 1 / g ^ N + Real.log ((N + 1 : ℕ) : ℝ)) / (g - 1) + 1 / g ^ (N + 1) +
        (Real.log ((N + 1 + 1 : ℕ) : ℝ) - Real.log ((N + 1 : ℕ) : ℝ)) / (g - 1) := by
      have : g ≠ 0 := by linarith
      field_simp; ring
    rw [e4]; linarith

/- English proof (translation)
Establish `hg : 1 < g` using `(Fact.out : g.Prime).one_lt`. Set `B : ℕ → Finset (ZMod g)[X]` to `fun d => (sqSet g d).filter fun P => Irreducible P ∧ ¬ RootsAvoid g c P`. Establish `hU` using `(GlobalTheory.BadShare.mass_union_bounds g N).2.2.1`. Use `(hU ℕ (Finset.Icc 1 N) _ (fun d f => ∃ P ∈ B d, P ∣ f) ?_).trans (Finset.sum_le_sum fun d hd => ?_)` and prove the remaining obligations. Introduce `f hf hbad`.

Take `⟨hm, hdeg, -, h0⟩` from `mem_sqSet.1 hf`. Unfold `RootsAvoid at hbad`. Use `push Not at hbad`. Take `⟨l, hl, hlg, x, hx, hs⟩` from `hbad`. Establish `hi : IsIntegral (ZMod g) x` using `Algebra.IsIntegral.isIntegral x`.

Establish `hdvd : minpoly (ZMod g) x ∣ f` using `minpoly.dvd _ _ (mem_aroots.1 hx).2`. Use `⟨(minpoly (ZMod g) x).natDegree, Finset.mem_Icc.2 ⟨minpoly.natDegree_pos hi, hdeg ▸ natDegree_le_of_dvd hdvd hm.ne_zero⟩, minpoly (ZMod g) x, Finset.mem_filter.2 ⟨mem_sqSet.2 ⟨minpoly.monic hi, rfl, (minpoly.irreducible hi).squarefree, minpoly.coeff_zero_ne_zero hi (root_ne_zero …` and prove the remaining obligations. Conclude with `h l hl hlg x (mem_aroots.2 ⟨minpoly.ne_zero hi, minpoly.aeval _ _⟩) hs`. Establish `hd1` using `(Finset.mem_Icc.1 hd).1`. Establish `hpow : 1 < g ^ d` using `Nat.one_lt_pow (by omega) hg`.

Establish `hq : (0 : ℝ) < (g : ℝ) ^ d - 1`. Establish `: (1 : ℝ) < (g : ℝ) ^ d` using `by exact_mod_cast hpow`. Combine the linear equalities and inequalities to obtain the conclusion. Use `(hU _ (B d) _ (fun P f => P ∣ f) fun f _ h => h).trans ?_` and prove the remaining obligations. Establish `h3 : ∑ P ∈ B d, mass g N (fun f => P ∣ f) ≤ (B d).card • ((g : ℝ) ^ d - 1)⁻¹`.

Use `Finset.sum_le_card_nsmul _ _ _ fun P hP => ?_` and prove the remaining obligations. Take `⟨hP1, hirr, -⟩` from `Finset.mem_filter.1 hP`. Use `((GlobalTheory.BadShare.divisor_bound g).2 N d P hP1).trans_eq ?_` and prove the remaining obligations. Rewrite using `[torusCard_irreducible hirr, (mem_sqSet.1 hP1).2.1, Nat.cast_sub hpow.le]`. Simplify using the standard rewrite rules.

Use `h3.trans ?_` and prove the remaining obligations. Establish `h4 : (d : ℝ) * (B d).card ≤ ∑ l ∈ (g ^ d - 1).primeFactors, ((l ^ padicValNat l (g ^ d - 1) : ℕ) : ℝ)`. Conclude with `avoid_card_irreducible_le c d hd1 h2` after adjusting the coercions. Establish `hd0 : (0 : ℝ) < d` using `by exact_mod_cast hd1`. Rewrite using `[nsmul_eq_mul, le_div_iff₀ (by positivity)]`.

Use `le_trans (le_of_eq ?_) h4` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts.
-/
theorem avoid_mass_le_sum {g : ℕ} [Fact g.Prime] (c : (ZMod g)ˣ) (N : ℕ) (h2 : 2 ∣ g - 1) :
    (mass g N fun f => ¬ RootsAvoid g c f) ≤ ∑ d ∈ Finset.Icc 1 N,
      (∑ l ∈ (g ^ d - 1).primeFactors, ((l ^ padicValNat l (g ^ d - 1) : ℕ) : ℝ)) / (d * ((g : ℝ) ^ d - 1)) := by
  have hg : 1 < g := (Fact.out : g.Prime).one_lt
  let B : ℕ → Finset (ZMod g)[X] := fun d => (sqSet g d).filter fun P => Irreducible P ∧ ¬ RootsAvoid g c P
  have hU := (GlobalTheory.BadShare.mass_union_bounds g N).2.2.1
  refine (hU ℕ (Finset.Icc 1 N) _ (fun d f => ∃ P ∈ B d, P ∣ f) ?_).trans (Finset.sum_le_sum fun d hd => ?_)
  · intro f hf hbad
    obtain ⟨hm, hdeg, -, h0⟩ := mem_sqSet.1 hf
    unfold RootsAvoid at hbad
    push Not at hbad
    obtain ⟨l, hl, hlg, x, hx, hs⟩ := hbad
    have hi : IsIntegral (ZMod g) x := Algebra.IsIntegral.isIntegral x
    have hdvd : minpoly (ZMod g) x ∣ f := minpoly.dvd _ _ (mem_aroots.1 hx).2
    refine ⟨(minpoly (ZMod g) x).natDegree, Finset.mem_Icc.2 ⟨minpoly.natDegree_pos hi,
      hdeg ▸ natDegree_le_of_dvd hdvd hm.ne_zero⟩, minpoly (ZMod g) x, Finset.mem_filter.2 ⟨mem_sqSet.2
        ⟨minpoly.monic hi, rfl, (minpoly.irreducible hi).squarefree,
          minpoly.coeff_zero_ne_zero hi (root_ne_zero h0 hx)⟩, minpoly.irreducible hi, fun h => ?_⟩, hdvd⟩
    exact h l hl hlg x (mem_aroots.2 ⟨minpoly.ne_zero hi, minpoly.aeval _ _⟩) hs
  · have hd1 := (Finset.mem_Icc.1 hd).1
    have hpow : 1 < g ^ d := Nat.one_lt_pow (by omega) hg
    have hq : (0 : ℝ) < (g : ℝ) ^ d - 1 := by
      have : (1 : ℝ) < (g : ℝ) ^ d := by exact_mod_cast hpow
      linarith
    refine (hU _ (B d) _ (fun P f => P ∣ f) fun f _ h => h).trans ?_
    have h3 : ∑ P ∈ B d, mass g N (fun f => P ∣ f) ≤ (B d).card • ((g : ℝ) ^ d - 1)⁻¹ := by
      refine Finset.sum_le_card_nsmul _ _ _ fun P hP => ?_
      obtain ⟨hP1, hirr, -⟩ := Finset.mem_filter.1 hP
      refine ((GlobalTheory.BadShare.divisor_bound g).2 N d P hP1).trans_eq ?_
      rw [torusCard_irreducible hirr, (mem_sqSet.1 hP1).2.1, Nat.cast_sub hpow.le]
      simp
    refine h3.trans ?_
    have h4 : (d : ℝ) * (B d).card ≤ ∑ l ∈ (g ^ d - 1).primeFactors, ((l ^ padicValNat l (g ^ d - 1) : ℕ) : ℝ) := by
      exact_mod_cast avoid_card_irreducible_le c d hd1 h2
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
    rw [nsmul_eq_mul, le_div_iff₀ (by positivity)]
    refine le_trans (le_of_eq ?_) h4
    field_simp

/- English proof (translation)
Introduce and unpack `g _ N q d c ⟨hq, hd, hq2, hd2, hqd, hmax, hdvd⟩`. Establish `hg : 2 ≤ g` using `(Fact.out : g.Prime).two_le`. Establish `hgR : (2 : ℝ) ≤ g` using `by exact_mod_cast hg`. Establish `hg1 : (0 : ℝ) < (g : ℝ) - 1` using `by linarith`. Establish `h4 : 4 ∣ g - 1` using `Dvd.dvd.trans ⟨4 * q * d, by ring⟩ hdvd`.

Use `(avoid_mass_le_sum c N (Dvd.dvd.trans (by norm_num) h4)).trans ?_` and prove the remaining obligations. Consider the cases of `N with`. Consider the case `zero => simp only [Nat.cast_zero, Real.log_zero]`. Simplify using the standard rewrite rules. Check the signs of the components of the expression.

Consider the case `succ N`. Rewrite using `[← Finset.insert_Icc_add_one_left_eq_Icc (by omega), Finset.sum_insert (by simp)]`. Use `add_le_add ?_ ?_` and prove the remaining obligations. Establish `h` using `GlobalTheory.BadShare.sum_primePowerParts_le (g - 1) q d (by omega) hq hd hq2 hd2 hqd hmax hdvd`. Rewrite `h` using `[Nat.cast_sub (by omega)]`.

Simplify using `only [pow_one, Nat.cast_one, one_mul] at h ⊢`. Rewrite using `[div_le_iff₀ hg1]`. Use `h.trans_eq ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Use `le_trans (Finset.sum_le_sum fun e he => ?_) ((avoid_sum_le g hgR N).trans ?_)` and prove the remaining obligations.

Establish `he2 : 2 ≤ e` using `(Finset.mem_Icc.1 he).1`. Establish `he0 : (0 : ℝ) < e` using `by exact_mod_cast (by omega : 0 < e)`. Establish `hq : (0 : ℝ) < (g : ℝ) ^ e - 1`. Establish `: (1 : ℝ) < (g : ℝ) ^ e` using `one_lt_pow₀ (by linarith) (by omega)`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[div_le_iff₀ (by positivity)]`. Use `(GlobalTheory.BadShare.sum_primePowerPart_pow_sub_one_le g e hg h4 he2).trans_eq ?_` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts. Use `div_le_div_of_nonneg_right ?_ hg1.le` and prove the remaining obligations. Establish `: (0 : ℝ) ≤ 1 / (g : ℝ) ^ N` using `by positivity`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem mass_not_rootsAvoid_le : ∀ (g : ℕ) [Fact g.Prime], ∀ (N q d : ℕ) (c : (ZMod g)ˣ), (q.Prime ∧ d.Prime ∧ q ≠ 2 ∧ d ≠ 2 ∧ q ≠ d ∧ 16 ≤ max q d ∧ 16 * q * d ∣ g - 1) → (mass g N fun f => ¬ RootsAvoid g c f) ≤ 1 / (4 * ((min q d : ℕ) : ℝ)) + (1 + Real.log N) / ((g : ℝ) - 1) := by
  rintro g _ N q d c ⟨hq, hd, hq2, hd2, hqd, hmax, hdvd⟩
  have hg : 2 ≤ g := (Fact.out : g.Prime).two_le
  have hgR : (2 : ℝ) ≤ g := by exact_mod_cast hg
  have hg1 : (0 : ℝ) < (g : ℝ) - 1 := by linarith
  have h4 : 4 ∣ g - 1 := Dvd.dvd.trans ⟨4 * q * d, by ring⟩ hdvd
  refine (avoid_mass_le_sum c N (Dvd.dvd.trans (by norm_num) h4)).trans ?_
  cases N with
  | zero => simp only [Nat.cast_zero, Real.log_zero]; simp; positivity
  | succ N =>
    rw [← Finset.insert_Icc_add_one_left_eq_Icc (by omega), Finset.sum_insert (by simp)]
    refine add_le_add ?_ ?_
    · have h := GlobalTheory.BadShare.sum_primePowerParts_le (g - 1) q d (by omega) hq hd hq2 hd2 hqd hmax hdvd
      rw [Nat.cast_sub (by omega)] at h
      simp only [pow_one, Nat.cast_one, one_mul] at h ⊢
      rw [div_le_iff₀ hg1]
      refine h.trans_eq ?_
      ring
    · refine le_trans (Finset.sum_le_sum fun e he => ?_) ((avoid_sum_le g hgR N).trans ?_)
      · have he2 : 2 ≤ e := (Finset.mem_Icc.1 he).1
        have he0 : (0 : ℝ) < e := by exact_mod_cast (by omega : 0 < e)
        have hq : (0 : ℝ) < (g : ℝ) ^ e - 1 := by
          have : (1 : ℝ) < (g : ℝ) ^ e := one_lt_pow₀ (by linarith) (by omega)
          linarith
        rw [div_le_iff₀ (by positivity)]
        refine (GlobalTheory.BadShare.sum_primePowerPart_pow_sub_one_le g e hg h4 he2).trans_eq ?_
        field_simp
      · refine div_le_div_of_nonneg_right ?_ hg1.le
        have : (0 : ℝ) ≤ 1 / (g : ℝ) ^ N := by positivity
        linarith

end GlobalTheory.BadShare
