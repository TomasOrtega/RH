import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdxEqRelIndex
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QuadraticCharNegOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AbsNormCmPrimeInertPrimeSignStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.RatEqui GlobalTheory.InertParity
open scoped BigOperators Pointwise
open Formalism.FrobeniusOrbits GlobalTheory.NormSign

namespace GlobalTheory.NormSignInert

/- English proof (translation)
Establish `key` using `descent hq hne (quadraticChar_neg_one_iff_not_isSquare.1 hu) _ (C.num * X.den * Y.den) (X.num * C.den * Y.den) (Y.num * C.den * X.den) rfl (by`. Apply `Int.cast_injective (α := ℚ)` to reduce the goal to its premises. Use `push_cast`. Rewrite using `[← Rat.mul_den_eq_num C, ← Rat.mul_den_eq_num X, ← Rat.mul_den_eq_num Y]`. Take the linear combination `((C.den : ℚ) ^ 2 * X.den ^ 2 * Y.den ^ 2) * h)`.

Simplify `key` using `[X.den_nz, Y.den_nz]`.
-/
theorem descent_rat {d q : ℕ} [Fact d.Prime] (hq : q.Prime) (hne : q ≠ d) {u : ℤ}
    (hu : quadraticChar (ZMod d) (-(u : ZMod d)) = -1) (C X Y : ℚ)
    (h : C ^ 2 * u + X ^ 2 = q * d * Y ^ 2) : C = 0 := by
  have key := descent hq hne (quadraticChar_neg_one_iff_not_isSquare.1 hu) _ (C.num * X.den * Y.den)
    (X.num * C.den * Y.den) (Y.num * C.den * X.den) rfl (by
      apply Int.cast_injective (α := ℚ)
      push_cast
      rw [← Rat.mul_den_eq_num C, ← Rat.mul_den_eq_num X, ← Rat.mul_den_eq_num Y]
      linear_combination ((C.den : ℚ) ^ 2 * X.den ^ 2 * Y.den ^ 2) * h)
  simpa [X.den_nz, Y.den_nz] using key

/- English proof (translation)
Establish `hl2 : ringChar (ZMod d) ≠ 2` using `by rw [ZMod.ringChar_zmod_n]; omega`. Establish `h` using `quadraticChar_card_card hl2 (F' := ZMod q) (by rwa [ZMod.ringChar_zmod_n]) (by rwa [ZMod.ringChar_zmod_n, ZMod.ringChar_zmod_n])`. Rewrite `h` using `[quadraticChar_neg_one' hd, ZMod.card, ZMod.card]`. Rewrite using `[h]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem char_eq {d q : ℕ} [Fact d.Prime] [Fact q.Prime] (hd : d % 4 = 3) (h2 : q ≠ 2) (hne : q ≠ d) :
    quadraticChar (ZMod d) q = quadraticChar (ZMod q) (-(d : ZMod q)) := by
  have hl2 : ringChar (ZMod d) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
  have h := quadraticChar_card_card hl2 (F' := ZMod q) (by rwa [ZMod.ringChar_zmod_n])
    (by rwa [ZMod.ringChar_zmod_n, ZMod.ringChar_zmod_n])
  rw [quadraticChar_neg_one' hd, ZMod.card, ZMod.card] at h
  rw [h]
  congr 1
  push_cast
  ring

/- English proof (translation)
Take `⟨hq, hd, hq8, hd16, hj⟩` from `h`. Use `haveI : Fact q.Prime := ⟨hq⟩`. Use `haveI : Fact p.Prime := ⟨hp⟩`. Take `⟨k, u, rfl, hu⟩` from `hm`. Establish `h1` using `hq.pos`.

Establish `h2` using `hd.pos`. Introduce `hW`. Move the coercions through the operations in `at hW`. Distinguish the cases in `hpd' : p = d`. Substitute `hpd'` using the available equality.

Take `⟨j, rfl⟩` from `hf`. Rewrite `hj` using `[← jacobiSym.legendreSym.to_jacobiSym, legendreSym]`. Move the coercions through the operations in `at hj`. Rewrite `hj` using `[← char_eq (d := p) (q := q) (by omega) (by omega) (by omega)]`. Establish `key` using `descent_rat (d := p) hq (by omega) (u := q * u) (by`.

Rewrite using `[← neg_one_mul, map_mul, quadraticChar_neg_one' (by omega)]`. Use `push_cast`. Rewrite using `[map_mul, hj, hu]; norm_num) (2 * p ^ (j + k + 1)) W A (by`. Use `push_cast`. Take the linear combination `hW)`.

Establish `: (0 : ℚ) < 2 * p ^ (j + k + 1)` using `by positivity`. Conclude with `this.ne' key`. Establish `h3` using `quadraticChar_neg_one_iff_not_isSquare.2 (hpd hpd')`. Rewrite `h3` using `[← char_eq (d := d) (q := p) (by omega) hp2 hpd']`. Establish `key` using `descent_rat (d := d) hq (by omega) (u := -(p ^ f * u)) (by`.

Use `push_cast`. Rewrite using `[neg_neg, map_mul, map_pow, h3, hu, hf.neg_one_pow]; norm_num) (2 * q * d * d ^ k) (q * d * A) W (by`. Use `push_cast`. Take the linear combination `(-(q * d : ℚ)) * hW)`. Establish `: (0 : ℚ) < 2 * q * d * d ^ k` using `by positivity`.

Conclude with `this.ne' key`.
-/
theorem no_rat_inert {q d : ℕ} [Fact d.Prime] (h : HostHyp q d) {m : ℕ} (hm : EvenSq d m) {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : Odd f) (hpd : p ≠ d → ¬ IsSquare (-(d : ZMod p))) (A W : ℚ) :
    W ^ 2 ≠ q * d * (A ^ 2 - 4 * (p ^ f * m)) := by
  obtain ⟨hq, hd, hq8, hd16, hj⟩ := h
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, u, rfl, hu⟩ := hm
  have h1 := hq.pos
  have h2 := hd.pos
  intro hW
  push_cast at hW
  by_cases hpd' : p = d
  · subst hpd'
    obtain ⟨j, rfl⟩ := hf
    rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym] at hj
    push_cast at hj
    rw [← char_eq (d := p) (q := q) (by omega) (by omega) (by omega)] at hj
    have key := descent_rat (d := p) hq (by omega) (u := q * u) (by
      rw [← neg_one_mul, map_mul, quadraticChar_neg_one' (by omega)]
      push_cast
      rw [map_mul, hj, hu]; norm_num) (2 * p ^ (j + k + 1)) W A (by
      push_cast
      linear_combination hW)
    have : (0 : ℚ) < 2 * p ^ (j + k + 1) := by positivity
    exact this.ne' key
  · have h3 := quadraticChar_neg_one_iff_not_isSquare.2 (hpd hpd')
    rw [← char_eq (d := d) (q := p) (by omega) hp2 hpd'] at h3
    have key := descent_rat (d := d) hq (by omega) (u := -(p ^ f * u)) (by
      push_cast
      rw [neg_neg, map_mul, map_pow, h3, hu, hf.neg_one_pow]; norm_num) (2 * q * d * d ^ k) (q * d * A) W (by
      push_cast
      linear_combination (-(q * d : ℚ)) * hW)
    have : (0 : ℚ) < 2 * q * d * d ^ k := by positivity
    exact this.ne' key

/- English proof (translation)
Establish `ha : H.sqq ^ 2 = -(H.q : H.E)` using `H.sqq_sq`. Establish `hb : H.sqd ^ 2 = -(H.d : H.E)` using `H.sqd_sq`. Use `set s := part H (t : H.E) (1, 1) with hs`. Use `set s' := part H (t : H.E) (-1, 1) with hs'`. Establish `e1 : part H (t : H.E) (-1, -1) = s` using `by rw [part_neg H ht]; simp [hs]`.

Establish `e2 : part H (t : H.E) (1, -1) = s'` using `by rw [part_neg H ht]; simp [hs']`. Establish `key : ∀ g : R.GG, (g.1.1 * g.1.2 = 1 ∧ H.sigmaOf g s = s ∧ H.sigmaOf g s' = s') ∨ (g.1.1 * g.1.2 = -1 ∧ H.sigmaOf g s = s' ∧ H.sigmaOf g s' = s)`. Introduce and unpack `⟨⟨u, v⟩, h⟩`. Rewrite using `[hs, hs', sigmaOf_part, sigmaOf_part]`. Apply the tactic sequence `rcases Int.units_eq_one_or u with rfl | rfl <;> rcases Int.units_eq_one_or v with rfl | rfl <;>`.

Simplify using `[e1, e2, ← hs, ← hs']`. Take `⟨n, hn⟩` from `exists_rat H (x := s * s') fun g => by`. Apply the tactic sequence `rcases key g with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ <;> rw [map_mul, h1, h2]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨A, hA⟩` from `exists_rat H (x := s + s') fun g => by`.

Apply the tactic sequence `rcases key g with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ <;> rw [map_add, h1, h2]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨W, hW⟩` from `exists_rat H (x := (s - s') * (H.sqq * H.sqd)) fun g => by`. Rewrite using `[map_mul, map_mul, map_sub, sigmaOf_aE, sigmaOf_bE, mul_mul_mul_comm, ← Int.cast_mul, ← Units.val_mul]`. Apply the tactic sequence `rcases key g with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ <;> rw [h0, h1, h2] <;> push_cast <;> ring`.

Use `⟨n, A, W, hn, ?_⟩` and prove the remaining obligations. Apply `Rat.cast_injective (α := H.E)` to reduce the goal to its premises. Use `push_cast`. Rewrite using `[hW, hA, hn, mul_pow, mul_pow, ha, hb]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_norm {R : Ranks} (H : Host R) (t : H.E) (ht : H.conj t = t) :
    ∃ n A W : ℚ, (n : H.E) = part H t (1, 1) * part H t (-1, 1) ∧ W ^ 2 = H.q * H.d * (A ^ 2 - 4 * n) := by
  have ha : H.sqq ^ 2 = -(H.q : H.E) := H.sqq_sq
  have hb : H.sqd ^ 2 = -(H.d : H.E) := H.sqd_sq
  set s := part H (t : H.E) (1, 1) with hs
  set s' := part H (t : H.E) (-1, 1) with hs'
  have e1 : part H (t : H.E) (-1, -1) = s := by rw [part_neg H ht]; simp [hs]
  have e2 : part H (t : H.E) (1, -1) = s' := by rw [part_neg H ht]; simp [hs']
  have key : ∀ g : R.GG, (g.1.1 * g.1.2 = 1 ∧ H.sigmaOf g s = s ∧ H.sigmaOf g s' = s') ∨
      (g.1.1 * g.1.2 = -1 ∧ H.sigmaOf g s = s' ∧ H.sigmaOf g s' = s) := by
    rintro ⟨⟨u, v⟩, h⟩
    rw [hs, hs', sigmaOf_part, sigmaOf_part]
    rcases Int.units_eq_one_or u with rfl | rfl <;> rcases Int.units_eq_one_or v with rfl | rfl <;>
      simp [e1, e2, ← hs, ← hs']
  obtain ⟨n, hn⟩ := exists_rat H (x := s * s') fun g => by
    rcases key g with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ <;> rw [map_mul, h1, h2]
    ring
  obtain ⟨A, hA⟩ := exists_rat H (x := s + s') fun g => by
    rcases key g with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ <;> rw [map_add, h1, h2]
    ring
  obtain ⟨W, hW⟩ := exists_rat H (x := (s - s') * (H.sqq * H.sqd)) fun g => by
    rw [map_mul, map_mul, map_sub, sigmaOf_aE, sigmaOf_bE, mul_mul_mul_comm, ← Int.cast_mul, ← Units.val_mul]
    rcases key g with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ <;> rw [h0, h1, h2] <;> push_cast <;> ring
  refine ⟨n, A, W, hn, ?_⟩
  apply Rat.cast_injective (α := H.E)
  push_cast
  rw [hW, hA, hn, mul_pow, mul_pow, ha, hb]
  ring

/- English proof (translation)
Introduce `D t P B ht0 ht hP hc hB`. Take `⟨-, p, f, hp, -, hp2, -, hf, hN, hpd⟩` from `(GlobalTheory.T.absNorm_cmPrime_inertPrime_sign D P hP).2.1 hc`. Rewrite using `[prod_embT]`. Generalize the expression as in `D.host = H at *`. Use `haveI : Fact H.d.Prime := ⟨H.hyp.2.1⟩`.

Establish `ha : H.sqq ^ 2 = -(H.q : H.E)` using `H.sqq_sq`. Establish `hb : H.sqd ^ 2 = -(H.d : H.E)` using `H.sqd_sq`. Establish `hB0 : B ≠ ⊥`. Introduce and unpack `rfl`. Conclude with `ht0 (by simpa using hB)`.

Establish `hm` using `evenSq_absNorm H.hyp ha hb B hB0`. Establish `hm0 : 0 < Ideal.absNorm B` using `Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff])`. Take `⟨n, A, W, hn, hWn⟩` from `exists_norm H (t : H.E) ht`. Establish `hn2 : n ^ 2 = ((p : ℚ) ^ f * (Ideal.absNorm B : ℚ)) ^ 2`. Establish `h1 : Algebra.norm ℚ (t : H.E) = n ^ 2`.

Apply `Rat.cast_injective (α := H.E)` to reduce the goal to its premises. Rewrite using `[norm_eq H ht]`. Use `push_cast`. Rewrite using `[hn]`. Establish `h2` using `congrArg Ideal.absNorm hB`.

Rewrite `h2` using `[map_mul, map_mul, absNorm_smul, Ideal.absNorm_span_singleton, hN]`. Establish `h3` using `congrArg (fun k : ℕ => ((k : ℤ) : ℚ)) h2`. Simplify using `only [Int.natCast_natAbs] at h3`. Move the coercions through the operations in `at h3`. Rewrite `h3` using `[Algebra.coe_norm_int, h1, abs_of_nonneg (sq_nonneg _)]`.

Rewrite using `[h3]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← hn, map_ratCast, Complex.ratCast_re]`. Break down `sq_eq_sq_iff_eq_or_eq_neg.1 hn2 with h | h` into its components or cases. Conclude with `absurd (by rw [hWn, h]) (no_rat_inert H.hyp hm hp hp2 hf hpd A W)`.

Use `hp.pos` as an intermediate fact. Establish `h0 : (0 : ℚ) < (p : ℚ) ^ f * (Ideal.absNorm B : ℚ)` using `by positivity`. Establish `h1 : n < 0` using `by rw [h]; exact neg_neg_of_pos h0`. Conclude with `h1` after adjusting the coercions.
-/
theorem norm_neg : ∀ (D : D7) (t : 𝓞 D.host.E) (P B : Ideal (𝓞 D.host.E)), t ≠ 0 →
    D.host.conj (t : D.host.E) = t → P.IsMaximal → D.host.conj • P = P →
    Ideal.span {t} = P * B * (D.host.conj • B) → (∏ τ, embT D τ (t : D.host.E)).re < 0 := by
  intro D t P B ht0 ht hP hc hB
  obtain ⟨-, p, f, hp, -, hp2, -, hf, hN, hpd⟩ := (GlobalTheory.T.absNorm_cmPrime_inertPrime_sign D P hP).2.1 hc
  rw [prod_embT]
  generalize D.host = H at *
  haveI : Fact H.d.Prime := ⟨H.hyp.2.1⟩
  have ha : H.sqq ^ 2 = -(H.q : H.E) := H.sqq_sq
  have hb : H.sqd ^ 2 = -(H.d : H.E) := H.sqd_sq
  have hB0 : B ≠ ⊥ := by
    rintro rfl
    exact ht0 (by simpa using hB)
  have hm := evenSq_absNorm H.hyp ha hb B hB0
  have hm0 : 0 < Ideal.absNorm B := Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  obtain ⟨n, A, W, hn, hWn⟩ := exists_norm H (t : H.E) ht
  have hn2 : n ^ 2 = ((p : ℚ) ^ f * (Ideal.absNorm B : ℚ)) ^ 2 := by
    have h1 : Algebra.norm ℚ (t : H.E) = n ^ 2 := by
      apply Rat.cast_injective (α := H.E)
      rw [norm_eq H ht]
      push_cast
      rw [hn]
    have h2 := congrArg Ideal.absNorm hB
    rw [map_mul, map_mul, absNorm_smul, Ideal.absNorm_span_singleton, hN] at h2
    have h3 := congrArg (fun k : ℕ => ((k : ℤ) : ℚ)) h2
    simp only [Int.natCast_natAbs] at h3
    push_cast at h3
    rw [Algebra.coe_norm_int, h1, abs_of_nonneg (sq_nonneg _)] at h3
    rw [h3]; ring
  rw [← hn, map_ratCast, Complex.ratCast_re]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hn2 with h | h
  · exact absurd (by rw [hWn, h]) (no_rat_inert H.hyp hm hp hp2 hf hpd A W)
  · have := hp.pos
    have h0 : (0 : ℚ) < (p : ℚ) ^ f * (Ideal.absNorm B : ℚ) := by positivity
    have h1 : n < 0 := by rw [h]; exact neg_neg_of_pos h0
    exact_mod_cast h1

end GlobalTheory.NormSignInert
