import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.SatakeEigenvalues

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace LocalAlgebraPowers

/- English proof (translation)
Use function extensionality and compare the values at `a`. Simplify using `[pad, a.2]`.
-/
theorem pad_self {k : ℕ} (l : Fin k → ℤ) : pad k l = l := by
  funext a
  simp [pad, a.2]

/- English proof (translation)
Take `⟨d, rfl⟩ : ∃ d, m = k + d` from `⟨m - k, by omega⟩`. Simplify using `only [rhoPair, pad, Fin.sum_univ_add, Fin.coe_castAdd, Fin.coe_natAdd, Fin.is_lt, dif_pos]`. Simplify using `only [show ∀ j : Fin d, ¬ (k + (j : ℕ) < k) from fun j => by omega, dif_neg, not_false_eq_true, mul_zero, Finset.sum_const_zero, add_zero]`. Rewrite using `[Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rhoPair_pad {m k : ℕ} (hkm : k ≤ m) (l : Fin k → ℤ) :
    rhoPair (pad m l) = rhoPair l + ((m : ℤ) - k) * ∑ i, l i := by
  obtain ⟨d, rfl⟩ : ∃ d, m = k + d := ⟨m - k, by omega⟩
  simp only [rhoPair, pad, Fin.sum_univ_add, Fin.coe_castAdd, Fin.coe_natAdd, Fin.is_lt, dif_pos]
  simp only [show ∀ j : Fin d, ¬ (k + (j : ℕ) < k) from fun j => by omega, dif_neg, not_false_eq_true,
    mul_zero, Finset.sum_const_zero, add_zero]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  ring

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨fun i j hij => ?_, fun i => ?_⟩` and prove the remaining obligations. Use `h (show (⟨i, by omega⟩ : Fin m) ≤ ⟨j, by omega⟩ from hij)` as an intermediate fact. Simplify `this` using `[pad, i.isLt, j.isLt]`.

Use `h (show (⟨i, by omega⟩ : Fin m) ≤ ⟨k, hkm⟩ from Fin.mk_le_mk.mpr i.isLt.le)` as an intermediate fact. Simplify `this` using `[pad, i.isLt]`. Introduce and unpack `⟨hl, h0⟩ a b hab`. Establish `hab' : (a : ℕ) ≤ b` using `hab`. Distinguish the cases in `hb : (b : ℕ) < k`.

Establish `ha : (a : ℕ) < k` using `lt_of_le_of_lt hab' hb`. Simplify using `only [pad, ha, hb, dif_pos]`. Conclude with `hl (Fin.mk_le_mk.mpr hab')`. Simplify using `only [pad, hb, dif_neg, not_false_eq_true] split_ifs`. Conclude with `h0 _`.

Conclude with `le_rfl`.
-/
theorem antitone_pad {m k : ℕ} (hkm : k < m) (l : Fin k → ℤ) :
    Antitone (pad m l) ↔ Antitone l ∧ ∀ i, 0 ≤ l i := by
  constructor
  · intro h
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · have := h (show (⟨i, by omega⟩ : Fin m) ≤ ⟨j, by omega⟩ from hij)
      simpa [pad, i.isLt, j.isLt] using this
    · have := h (show (⟨i, by omega⟩ : Fin m) ≤ ⟨k, hkm⟩ from Fin.mk_le_mk.mpr i.isLt.le)
      simpa [pad, i.isLt] using this
  · rintro ⟨hl, h0⟩ a b hab
    have hab' : (a : ℕ) ≤ b := hab
    by_cases hb : (b : ℕ) < k
    · have ha : (a : ℕ) < k := lt_of_le_of_lt hab' hb
      simp only [pad, ha, hb, dif_pos]
      exact hl (Fin.mk_le_mk.mpr hab')
    · simp only [pad, hb, dif_neg, not_false_eq_true]
      split_ifs
      · exact h0 _
      · exact le_rfl

/- English proof (translation)
Break down `lt_or_eq_of_le hkm with hlt | heq` into its components or cases. Rewrite using `[antitone_pad hlt l]`. Simplify using `[hl]`. Substitute `heq` using the available equality. Establish `h'` using `h.resolve_left (lt_irrefl _)`.

Establish `hall : ∀ i, 0 ≤ l i`. Introduce `i`. Establish `hlast : 0 ≤ l ⟨k - 1, by omega⟩` using `h' _ (by simp; omega)`. Conclude with `le_trans hlast (hl (Fin.mk_le_mk.mpr (by omega)))`. Rewrite using `[pad_self]`.

Conclude with `⟨fun _ => hall, fun _ => hl⟩`.
-/
theorem antitone_pad_iff {m k : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) (l : Fin k → ℤ) (hl : Antitone l)
    (h : k < m ∨ ∀ i : Fin k, (i : ℕ) + 1 = k → 0 ≤ l i) : Antitone (pad m l) ↔ ∀ i, 0 ≤ l i := by
  rcases lt_or_eq_of_le hkm with hlt | heq
  · rw [antitone_pad hlt l]
    simp [hl]
  · subst heq
    have h' := h.resolve_left (lt_irrefl _)
    have hall : ∀ i, 0 ≤ l i := by
      intro i
      have hlast : 0 ≤ l ⟨k - 1, by omega⟩ := h' _ (by simp; omega)
      exact le_trans hlast (hl (Fin.mk_le_mk.mpr (by omega)))
    rw [pad_self]
    exact ⟨fun _ => hall, fun _ => hl⟩

variable {E : Type} [Field E] [NumberField E] {S : Finset (Pl E)}

/- English proof (translation)
Use `Nat.pos_of_ne_zero fun h => ?_` and prove the remaining obligations. Rewrite `h` using `[nq, Ideal.absNorm_eq_zero_iff]`. Conclude with `w.1.ne_bot h`.
-/
theorem nq_pos (w : Off E S) : 0 < nq w := by
  refine Nat.pos_of_ne_zero fun h => ?_
  rw [nq, Ideal.absNorm_eq_zero_iff] at h
  exact w.1.ne_bot h

/- English proof (translation)
The claim follows from `PositivityTheory.JacquetShalikaLocal.SatakeEigenvalues.qF_eq w.1`.
-/
theorem qF_eq' (w : Off E S) : qF (w.1.adicCompletion E) = nq w := PositivityTheory.JacquetShalikaLocal.SatakeEigenvalues.qF_eq w.1

/- English proof (translation)
Establish `hpos : (0 : ℝ) < nq w` using `by exact_mod_cast nq_pos w`. Rewrite using `[sqrtQ, qF_eq', ← Complex.ofReal_exp]`. Use `norm_cast`. Rewrite using `[Real.sqrt_eq_rpow, Real.rpow_def_of_pos hpos]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem sqrtQ_eq (w : Off E S) :
    sqrtQ (w.1.adicCompletion E) = Complex.exp ((Real.log (nq w) / 2 : ℝ)) := by
  have hpos : (0 : ℝ) < nq w := by exact_mod_cast nq_pos w
  rw [sqrtQ, qF_eq', ← Complex.ofReal_exp]
  norm_cast
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hpos]
  congr 1
  ring

/- English proof (translation)
Rewrite using `[map_zpow₀]`. Use `congr 1`. Simplify using `[sqrtQ, Complex.conj_ofReal]`.
-/
theorem conj_sqrtQ_zpow (w : Off E S) (j : ℤ) :
    conj (sqrtQ (w.1.adicCompletion E) ^ j) = sqrtQ (w.1.adicCompletion E) ^ j := by
  rw [map_zpow₀]
  congr 1
  simp [sqrtQ, Complex.conj_ofReal]

/- English proof (translation)
Establish `hpos : (0 : ℝ) < nq w` using `by exact_mod_cast nq_pos w`. Rewrite using `[← Complex.ofReal_natCast, ← Complex.ofReal_exp, Real.exp_log hpos]`.
-/
theorem cast_eq_exp (w : Off E S) : (nq w : ℂ) = Complex.exp (Real.log (nq w)) := by
  have hpos : (0 : ℝ) < nq w := by exact_mod_cast nq_pos w
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_exp, Real.exp_log hpos]

/- English proof (translation)
Establish `hpos : (0 : ℝ) < nq w` using `by exact_mod_cast nq_pos w`. Rewrite using `[Complex.cpow_def_of_ne_zero (by exact_mod_cast (nq_pos w).ne'), ← Complex.ofReal_natCast, ← Complex.ofReal_log hpos.le]`.
-/
theorem cpow_eq (w : Off E S) (z : ℂ) : (nq w : ℂ) ^ z = Complex.exp (Real.log (nq w) * z) := by
  have hpos : (0 : ℝ) < nq w := by exact_mod_cast nq_pos w
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (nq_pos w).ne'), ← Complex.ofReal_natCast,
    ← Complex.ofReal_log hpos.le]

/- English proof (translation)
Rewrite using `[cast_eq_exp, ← Complex.exp_int_mul]`.
-/
theorem zpow_eq (w : Off E S) (j : ℤ) : (nq w : ℂ) ^ j = Complex.exp (j * Real.log (nq w)) := by
  rw [cast_eq_exp, ← Complex.exp_int_mul]

/- English proof (translation)
Rewrite using `[sqrtQ_eq, ← Complex.exp_int_mul]`.
-/
theorem sqrt_zpow_eq (w : Off E S) (j : ℤ) :
    sqrtQ (w.1.adicCompletion E) ^ j = Complex.exp (j * (Real.log (nq w) / 2 : ℝ)) := by
  rw [sqrtQ_eq, ← Complex.exp_int_mul]

/- English proof (translation)
Establish `hq : (0 : ℝ) < nq w` using `by exact_mod_cast nq_pos w`. Establish `hx : (0 : ℝ) < (nq w : ℝ) ^ N` using `zpow_pos hq N`. Rewrite using `[Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), ← Complex.ofReal_log hx.le, Real.log_zpow]`.
-/
theorem rpow_cpow_eq (w : Off E S) (N : ℤ) (z : ℂ) :
    ((((nq w : ℝ) ^ N : ℝ)) : ℂ) ^ z = Complex.exp ((N * Real.log (nq w) : ℝ) * z) := by
  have hq : (0 : ℝ) < nq w := by exact_mod_cast nq_pos w
  have hx : (0 : ℝ) < (nq w : ℝ) ^ N := zpow_pos hq N
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), ← Complex.ofReal_log hx.le, Real.log_zpow]

/- English proof (translation)
Unfold `loc`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem local_inputs_from_literature {m k : ℕ} (q : ℕ) (α : Fin m → ℂˣ) (β : Fin k → ℂˣ) (s : ℂ) (l : Fin k → ℤ) :
    loc q α β s l = loc q α β 0 l * (q : ℂ) ^ (-s * ((∑ i, l i : ℤ) : ℂ)) := by
  unfold loc
  split_ifs <;> simp

end LocalAlgebraPowers

open LocalAlgebraPowers in
/- English proof (translation)
Introduce `E _ _ S m k α α' w χ hχ hk hkm`. Establish `hψ` using `hχ.1`. Establish `hq : (0 : ℝ) < nq w` using `by exact_mod_cast nq_pos w`. Use `⟨?_, fun l => ⟨fun s => ?_, fun hcase => ?_, fun hneg => ?_⟩⟩` and prove the remaining obligations. Establish `hp : pad m (0 : Fin k → ℤ) = 0`.

Use function extensionality and compare the values at `a`. Simplify using `[pad]`. Establish `hA : Antitone (0 : Fin k → ℤ) ∧ ∀ i, 0 ≤ (0 : Fin k → ℤ) i` using `⟨fun _ _ _ => le_rfl, fun _ => le_rfl⟩`. Simplify using `only [aLoc, loc, if_pos hA, hp, halfModulus_zero, schur_zero, map_one, Pi.zero_apply, Finset.sum_const_zero, Int.cast_zero, mul_zero, neg_zero, Complex.cpow_zero, one_pow, mul_one]`. Simplify using `[hA.1]`.

Establish `key : ∀ a b c d g : ℂ, a + 2 * b + c + d = g → ∀ L : ℂ, Complex.exp a * (Complex.exp b ^ 2 * Complex.exp c * L * Complex.exp d) = L * Complex.exp g`. Introduce `a b c d g h L`. Rewrite using `[← h, Complex.exp_add, Complex.exp_add, Complex.exp_add, two_mul, Complex.exp_add]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[local_inputs_from_literature]`.

Simplify using `only [aLoc, halfModulus_eq]`. Rewrite using `[rpow_cpow_eq, sqrt_zpow_eq, zpow_eq, cpow_eq, cpow_eq]`. Use `key _ _ _ _ _ ?_ _` and prove the remaining obligations. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[sphericalWhittaker_torusPow hψ, sphericalWhittaker_torusPow hψ]`. Distinguish the cases in `hA : Antitone l ∧ ∀ i, 0 ≤ l i`. Establish `hpA : Antitone (pad m l)` using `(antitone_pad_iff hk hkm l hA.1 hcase).mpr hA.2`. Establish `hfac : halfModulus (w.1.adicCompletion E) (pad m l) * conj (halfModulus (w.1.adicCompletion E) l) = halfModulus (w.1.adicCompletion E) l ^ 2 * (nq w : ℂ) ^ (-(((m : ℂ) - k) / 2) * ((∑ i, l i : ℤ) : ℂ))`. Rewrite using `[halfModulus_eq, halfModulus_eq, rhoPair_pad hkm, conj_sqrtQ_zpow, sqrt_zpow_eq, sqrt_zpow_eq, cpow_eq, sq, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_pos hpA, if_pos hA.1]`. Simplify using `only [aLoc, loc, if_pos hA, neg_zero, zero_mul, Complex.cpow_zero, mul_one, map_mul]`.

Take the linear combination `((evalAt (α w)) (schur (pad m l)) * conj ((evalAt (α' w)) (schur l))) * hfac`. Establish `hR : aLoc α α' w l = 0`. Simplify using `only [aLoc, loc, if_neg hA, mul_zero]`. Rewrite using `[hR]`. Distinguish the cases in `hl : Antitone l`.

Establish `hpA : ¬ Antitone (pad m l)` using `fun h => hA ⟨hl, (antitone_pad_iff hk hkm l hl hcase).mp h⟩`. Rewrite using `[if_neg hpA, zero_mul]`. Rewrite using `[if_neg hl, map_zero, mul_zero]`. Establish `hA : ¬ (Antitone l ∧ ∀ i, 0 ≤ l i)`. Introduce and unpack `⟨-, h⟩`.

Take `⟨i, hi⟩` from `hneg`. Conclude with `absurd (h i) (not_le.mpr hi)`. Simplify using `only [aLoc, loc, if_neg hA, mul_zero]`.
-/
theorem localHeckeAlgebra_statement : LocalHeckeAlgebra := by
  intro E _ _ S m k α α' w χ hχ hk hkm
  have hψ := hχ.1
  have hq : (0 : ℝ) < nq w := by exact_mod_cast nq_pos w
  refine ⟨?_, fun l => ⟨fun s => ?_, fun hcase => ?_, fun hneg => ?_⟩⟩
  · have hp : pad m (0 : Fin k → ℤ) = 0 := by
      funext a
      simp [pad]
    have hA : Antitone (0 : Fin k → ℤ) ∧ ∀ i, 0 ≤ (0 : Fin k → ℤ) i :=
      ⟨fun _ _ _ => le_rfl, fun _ => le_rfl⟩
    simp only [aLoc, loc, if_pos hA, hp, halfModulus_zero, schur_zero, map_one, Pi.zero_apply,
      Finset.sum_const_zero, Int.cast_zero, mul_zero, neg_zero, Complex.cpow_zero, one_pow, mul_one]
    simp [hA.1]
  · have key : ∀ a b c d g : ℂ, a + 2 * b + c + d = g → ∀ L : ℂ,
        Complex.exp a * (Complex.exp b ^ 2 * Complex.exp c * L * Complex.exp d) = L * Complex.exp g := by
      intro a b c d g h L
      rw [← h, Complex.exp_add, Complex.exp_add, Complex.exp_add, two_mul, Complex.exp_add]
      ring
    rw [local_inputs_from_literature]
    simp only [aLoc, halfModulus_eq]
    rw [rpow_cpow_eq, sqrt_zpow_eq, zpow_eq, cpow_eq, cpow_eq]
    refine key _ _ _ _ _ ?_ _
    push_cast
    ring
  · rw [sphericalWhittaker_torusPow hψ, sphericalWhittaker_torusPow hψ]
    by_cases hA : Antitone l ∧ ∀ i, 0 ≤ l i
    · have hpA : Antitone (pad m l) := (antitone_pad_iff hk hkm l hA.1 hcase).mpr hA.2
      have hfac : halfModulus (w.1.adicCompletion E) (pad m l) * conj (halfModulus (w.1.adicCompletion E) l) =
          halfModulus (w.1.adicCompletion E) l ^ 2 *
            (nq w : ℂ) ^ (-(((m : ℂ) - k) / 2) * ((∑ i, l i : ℤ) : ℂ)) := by
        rw [halfModulus_eq, halfModulus_eq, rhoPair_pad hkm, conj_sqrtQ_zpow, sqrt_zpow_eq, sqrt_zpow_eq,
          cpow_eq, sq, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
        congr 1
        push_cast
        ring
      rw [if_pos hpA, if_pos hA.1]
      simp only [aLoc, loc, if_pos hA, neg_zero, zero_mul, Complex.cpow_zero, mul_one, map_mul]
      linear_combination ((evalAt (α w)) (schur (pad m l)) * conj ((evalAt (α' w)) (schur l))) * hfac
    · have hR : aLoc α α' w l = 0 := by
        simp only [aLoc, loc, if_neg hA, mul_zero]
      rw [hR]
      by_cases hl : Antitone l
      · have hpA : ¬ Antitone (pad m l) := fun h => hA ⟨hl, (antitone_pad_iff hk hkm l hl hcase).mp h⟩
        rw [if_neg hpA, zero_mul]
      · rw [if_neg hl, map_zero, mul_zero]
  · have hA : ¬ (Antitone l ∧ ∀ i, 0 ≤ l i) := by
      rintro ⟨-, h⟩
      obtain ⟨i, hi⟩ := hneg
      exact absurd (h i) (not_le.mpr hi)
    simp only [aLoc, loc, if_neg hA, mul_zero]

end PositivityTheory.AdelicQuotientData

end
