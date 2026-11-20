import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvDer
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrobCoef

/- English proof (translation)
Establish `hp0 : p ≠ 0` using `hp.out.ne_zero`. Establish `hs : HasSubst (fun i => (X i : MvPowerSeries (Fin d) Q) ^ p)` using `hasSubst_of_constantCoeff_zero fun i => by simp [hp0]`. Rewrite using `[frob, coeff_subst hs]`. Establish `key : ∀ e : Fin d →₀ ℕ, (e.prod fun i n => ((X i : MvPowerSeries (Fin d) Q) ^ p) ^ n) = monomial (p • e) 1`. Introduce `e`.

Proceed by induction on `e using Finsupp.induction with`. Consider the case `zero => simp`. Consider the case `single_add i n e hi hn ih`. Rewrite using `[Finsupp.prod_add_index' (by simp) (by intros; rw [pow_add]), ih, Finsupp.prod_single_index (by simp), ← pow_mul, X_pow_eq, monomial_mul_monomial, one_mul, smul_add, Finsupp.smul_single, smul_eq_mul]`. Repeatedly rewrite using `[key]`.

Rewrite using `[finsum_eq_single _ (Finsupp.single j 1)]`. Rewrite using `[coeff_monomial, if_pos (by rw [Finsupp.smul_single, smul_eq_mul, mul_one]), smul_eq_mul, mul_one, coeff_map, lin]`. Introduce `e he`. Rewrite using `[coeff_monomial, if_neg, smul_zero]`. Introduce `h`.

Apply `he` to reduce the goal to its premises. Use extensionality with `i`. Use `congrArg (fun g => g i) h` as an intermediate fact. Simplify using `only [Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply] at this ⊢`. Use `split_ifs at this ⊢ with h1`.

Conclude with `Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hp0) (this.symm.trans (mul_one p).symm)`. Conclude with `(mul_eq_zero.1 this.symm).resolve_left hp0`.
-/
theorem coeff_frob_single (p : ℕ) [hp : Fact p.Prime] {Q : Type} [CommRing Q] {d : ℕ}
    (s : Q →+* Q) (f : MvPowerSeries (Fin d) Q) (j : Fin d) :
    coeff (Finsupp.single j p) (frob p s f) = s (lin f j) := by
  classical
  have hp0 : p ≠ 0 := hp.out.ne_zero
  have hs : HasSubst (fun i => (X i : MvPowerSeries (Fin d) Q) ^ p) :=
    hasSubst_of_constantCoeff_zero fun i => by simp [hp0]
  rw [frob, coeff_subst hs]
  have key : ∀ e : Fin d →₀ ℕ, (e.prod fun i n => ((X i : MvPowerSeries (Fin d) Q) ^ p) ^ n) =
      monomial (p • e) 1 := by
    intro e
    induction e using Finsupp.induction with
    | zero => simp
    | single_add i n e hi hn ih =>
      rw [Finsupp.prod_add_index' (by simp) (by intros; rw [pow_add]), ih, Finsupp.prod_single_index
        (by simp), ← pow_mul, X_pow_eq, monomial_mul_monomial, one_mul, smul_add,
        Finsupp.smul_single, smul_eq_mul]
  simp_rw [key]
  rw [finsum_eq_single _ (Finsupp.single j 1)]
  · rw [coeff_monomial, if_pos (by rw [Finsupp.smul_single, smul_eq_mul, mul_one]), smul_eq_mul,
      mul_one, coeff_map, lin]
  · intro e he
    rw [coeff_monomial, if_neg, smul_zero]
    intro h
    apply he
    ext i
    have := congrArg (fun g => g i) h
    simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply] at this ⊢
    split_ifs at this ⊢ with h1
    · exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hp0) (this.symm.trans (mul_one p).symm)
    · exact (mul_eq_zero.1 this.symm).resolve_left hp0

/- English proof (translation)
Introduce `p _ B Q _ _ _ s σ hs _ d k e U hU h hlin hint`. Use `set x : Fin d → Fin d ⊕ Fin k → Q := fun j l => (p : Q) * coeff (Finsupp.single j p) (e l) with hx`. Establish `hD : ∀ l i, (U * blk d k (p : B) 1) l i = U l i * Sum.elim (fun _ => (p : B)) (fun _ => 1) i`. Introduce `l i`. Simplify using `[blk, Matrix.mul_diagonal]`.

Establish `hco : ∀ i j, coeff (Finsupp.single j p) (frob p s (e i) - comb (fun l => (U * blk d k (p : B) 1) l i) e) = s (lin (e i) j) - ∑ l, algebraMap B Q (U l i * Sum.elim (fun _ => (p : B)) (fun _ => 1) i) * coeff (Finsupp.single j p) (e l)`. Introduce `i j`. Rewrite using `[map_sub, GlobalTheory.FrobCoef.coeff_frob_single, comb, map_sum]`. Repeatedly rewrite using `[coeff_smul, hD]`. Establish `key : ∀ j, ∃ y : Fin d ⊕ Fin k → B, (∀ i, ∑ l, algebraMap B Q (U l i) * x j l = algebraMap B Q (y i)) ∧ ∀ i, ∃ t, y i - (Pi.single (Sum.inl j) (1 : B) : Fin d ⊕ Fin k → B) i = p * t`.

Introduce `j`. Establish `H : ∀ i, ∃ yi : B, ∑ l, algebraMap B Q (U l i) * x j l = algebraMap B Q yi ∧ ∃ t, yi - (Pi.single (Sum.inl j) (1 : B) : Fin d ⊕ Fin k → B) i = p * t`. Introduce and unpack `(a | r)`. Take `⟨b, hb, hbe⟩` from `(h (Sum.inl a)).2 a rfl (Finsupp.single j p)`. Take `⟨β, rfl⟩` from `Ideal.mem_span_singleton'.1 hb`.

Rewrite `hbe` using `[hco, hlin]`. Use `⟨(Pi.single a (1 : B) : Fin d → B) j - β * p, ?_, -β, ?_⟩` and prove the remaining obligations. Establish `h1 : s ((Pi.single a (1 : Q) : Fin d → Q) j) = algebraMap B Q ((Pi.single a (1 : B) : Fin d → B) j)`. Distinguish the cases in `haj : j = a`. Substitute `haj` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, haj]`. Establish `hS : ∑ l, algebraMap B Q (U l (Sum.inl a)) * x j l = ∑ l, algebraMap B Q (U l (Sum.inl a) * (p : B)) * coeff (Finsupp.single j p) (e l)` using `Finset.sum_congr rfl fun l _ => by simp only [hx, Sum.elim_inl, map_mul, map_natCast]; ring`. Simplify using `only [Sum.elim_inl] at hbe`. Rewrite using `[hS, map_sub, ← h1]`.

Take the linear combination `-hbe`. Distinguish the cases in `haj : a = j`. Substitute `haj` using the available equality. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.

Simplify using `[Pi.single_apply, haj, Ne.symm haj]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨b1, -, hb1⟩` from `(h (Sum.inr r)).1 (Finsupp.single j p)`. Take `⟨b0, hb0⟩` from `hint (Sum.inr r) j`. Rewrite `hb1` using `[hco, hb0, hs]`.

Use `⟨p * (σ b0 - b1), ?_, σ b0 - b1, by simp⟩` and prove the remaining obligations. Simplify using `only [Sum.elim_inr, mul_one] at hb1`. Establish `: ∑ l, algebraMap B Q (U l (Sum.inr r)) * coeff (Finsupp.single j p) (e l) = algebraMap B Q (σ b0 - b1)`. Rewrite using `[map_sub, ← hb1]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [hx, map_mul, map_natCast, ← this, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun l _ => by ring` and prove the remaining obligations. Use `choose y hy1 hy2 using H`. Conclude with `⟨y, hy1, hy2⟩`. Use `choose y hy1 hy2 using key`.

Establish `hUU : U * U⁻¹ = 1` using `Matrix.mul_nonsing_inv U ((Matrix.isUnit_iff_isUnit_det U).1 hU)`. Use `⟨fun a j => ∑ i, U⁻¹ i (Sum.inl a) * y j i, fun a j => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Establish `: ∀ m, algebraMap B Q (∑ i, U⁻¹ i m * y j i) = x j m`. Introduce `m`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [map_sum, map_mul, hy1]`. Use `_ = ∑ l, algebraMap B Q ((U * U⁻¹) l m) * x j l := by`. Simplify using `only [Matrix.mul_apply, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => by ring` and prove the remaining obligations.

Use `_ = x j m := by`. Rewrite using `[hUU]`. Simplify using `[Matrix.one_apply]`. Conclude with `this _`. Use `choose t ht using hy2 j`.

Use `⟨∑ i, U⁻¹ i (Sum.inl a) * t i, ?_⟩` and prove the remaining obligations. Establish `h1 : U⁻¹ (Sum.inl j) (Sum.inl a) = ∑ i, U⁻¹ i (Sum.inl a) * (Pi.single (Sum.inl j) (1 : B) : Fin d ⊕ Fin k → B) i`. Simplify using `[Pi.single_apply]`. Rewrite using `[h1, ← Finset.sum_sub_distrib, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[← mul_sub, ht i]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem coef_logs_inv_frob : ∀ (p : ℕ) [Fact p.Prime] (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] (s : Q →+* Q) (σ : B →+* B), (∀ b, s (algebraMap B Q b) = algebraMap B Q (σ b)) → Function.Injective (algebraMap B Q) → ∀ (d k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) Q) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) B), IsUnit U → (∀ i, In (⊤ : Ideal B) (frob p s (e i) - comb (fun l => (U * blk d k (p : B) 1) l i) e) ∧ ∀ i', i = Sum.inl i' → In (Ideal.span {(p : B)}) (frob p s (e i) - comb (fun l => (U * blk d k (p : B) 1) l i) e)) → (∀ a, lin (e (Sum.inl a)) = Pi.single a 1) → (∀ r j, ∃ b, lin (e r) j = algebraMap B Q b) → ∃ c : Fin d → Fin d → B, ∀ a j, algebraMap B Q (c a j) = (p : Q) * coeff (Finsupp.single j p) (e (Sum.inl a)) ∧ ∃ b, c a j - U⁻¹ (Sum.inl j) (Sum.inl a) = p * b := by
  intro p _ B Q _ _ _ s σ hs _ d k e U hU h hlin hint
  classical
  set x : Fin d → Fin d ⊕ Fin k → Q := fun j l => (p : Q) * coeff (Finsupp.single j p) (e l) with hx
  have hD : ∀ l i, (U * blk d k (p : B) 1) l i =
      U l i * Sum.elim (fun _ => (p : B)) (fun _ => 1) i := by
    intro l i
    simp [blk, Matrix.mul_diagonal]
  have hco : ∀ i j, coeff (Finsupp.single j p)
      (frob p s (e i) - comb (fun l => (U * blk d k (p : B) 1) l i) e) =
      s (lin (e i) j) - ∑ l, algebraMap B Q (U l i * Sum.elim (fun _ => (p : B)) (fun _ => 1) i) *
        coeff (Finsupp.single j p) (e l) := by
    intro i j
    rw [map_sub, GlobalTheory.FrobCoef.coeff_frob_single, comb, map_sum]
    simp_rw [coeff_smul, hD]
  have key : ∀ j, ∃ y : Fin d ⊕ Fin k → B, (∀ i, ∑ l, algebraMap B Q (U l i) * x j l =
      algebraMap B Q (y i)) ∧ ∀ i, ∃ t, y i - (Pi.single (Sum.inl j) (1 : B) : Fin d ⊕ Fin k → B) i = p * t := by
    intro j
    have H : ∀ i, ∃ yi : B, ∑ l, algebraMap B Q (U l i) * x j l = algebraMap B Q yi ∧
        ∃ t, yi - (Pi.single (Sum.inl j) (1 : B) : Fin d ⊕ Fin k → B) i = p * t := by
      rintro (a | r)
      · obtain ⟨b, hb, hbe⟩ := (h (Sum.inl a)).2 a rfl (Finsupp.single j p)
        obtain ⟨β, rfl⟩ := Ideal.mem_span_singleton'.1 hb
        rw [hco, hlin] at hbe
        refine ⟨(Pi.single a (1 : B) : Fin d → B) j - β * p, ?_, -β, ?_⟩
        · have h1 : s ((Pi.single a (1 : Q) : Fin d → Q) j) = algebraMap B Q ((Pi.single a (1 : B) : Fin d → B) j) := by
            by_cases haj : j = a
            · subst haj; simp
            · simp [Pi.single_apply, haj]
          have hS : ∑ l, algebraMap B Q (U l (Sum.inl a)) * x j l = ∑ l, algebraMap B Q
              (U l (Sum.inl a) * (p : B)) * coeff (Finsupp.single j p) (e l) :=
            Finset.sum_congr rfl fun l _ => by simp only [hx, Sum.elim_inl, map_mul, map_natCast]; ring
          simp only [Sum.elim_inl] at hbe
          rw [hS, map_sub, ← h1]
          linear_combination -hbe
        · by_cases haj : a = j
          · subst haj; simp; ring
          · simp [Pi.single_apply, haj, Ne.symm haj]; ring
      · obtain ⟨b1, -, hb1⟩ := (h (Sum.inr r)).1 (Finsupp.single j p)
        obtain ⟨b0, hb0⟩ := hint (Sum.inr r) j
        rw [hco, hb0, hs] at hb1
        refine ⟨p * (σ b0 - b1), ?_, σ b0 - b1, by simp⟩
        simp only [Sum.elim_inr, mul_one] at hb1
        have : ∑ l, algebraMap B Q (U l (Sum.inr r)) * coeff (Finsupp.single j p) (e l) =
            algebraMap B Q (σ b0 - b1) := by
          rw [map_sub, ← hb1]; ring
        simp only [hx, map_mul, map_natCast, ← this, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => by ring
    choose y hy1 hy2 using H
    exact ⟨y, hy1, hy2⟩
  choose y hy1 hy2 using key
  have hUU : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv U ((Matrix.isUnit_iff_isUnit_det U).1 hU)
  refine ⟨fun a j => ∑ i, U⁻¹ i (Sum.inl a) * y j i, fun a j => ⟨?_, ?_⟩⟩
  · have : ∀ m, algebraMap B Q (∑ i, U⁻¹ i m * y j i) = x j m := by
      intro m
      calc algebraMap B Q (∑ i, U⁻¹ i m * y j i)
          = ∑ i, algebraMap B Q (U⁻¹ i m) * ∑ l, algebraMap B Q (U l i) * x j l := by
            simp only [map_sum, map_mul, hy1]
        _ = ∑ l, algebraMap B Q ((U * U⁻¹) l m) * x j l := by
            simp only [Matrix.mul_apply, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => by ring
        _ = x j m := by
            rw [hUU]
            simp [Matrix.one_apply]
    exact this _
  · choose t ht using hy2 j
    refine ⟨∑ i, U⁻¹ i (Sum.inl a) * t i, ?_⟩
    have h1 : U⁻¹ (Sum.inl j) (Sum.inl a) = ∑ i, U⁻¹ i (Sum.inl a) * (Pi.single (Sum.inl j) (1 : B) : Fin d ⊕ Fin k → B) i := by
      simp [Pi.single_apply]
    rw [h1, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_sub, ht i]; ring

end GlobalTheory.FrobCoef
