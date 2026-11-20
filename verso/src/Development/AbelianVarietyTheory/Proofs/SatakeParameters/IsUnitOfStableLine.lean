import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LMulBeta

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

namespace GlobalTheory.Pst.StLine

/- English proof (translation)
Introduce `l _ P _ K hno hLU b hb hst`. Unfold `GlobalTheory.RegularRing.LineUnit at hLU`. Use `haveI : CharZero P.R.B := charZero_of_injective_algebraMap (algebraMap ℚ_[l] P.R.B).injective`. Establish `hact : ∀ (g : GQ l) (p : Bst P), actSt P g p = stHom P (P.actQ g) (X + C ((kummer P g : ℚ_[l]) • P.tB)) p` using `fun g p => rfl`. Establish `hder : ∀ (g : GQ l) (p : Bst P), derivative (actSt P g p) = actSt P g (derivative p)`.

Introduce `g p`. Rewrite using `[hact, hact, derivative_stHom]`. Simplify using the standard rewrite rules. Establish `hiter : ∀ (k : ℕ) (g : GQ l) (p : Bst P), actSt P g (derivative^[k] p) = derivative^[k] (actSt P g p)`. Introduce `k g`.

Proceed by induction on `k with`. Consider the case `zero => intro p`. Both sides reduce to the same expression. Consider the case `succ k ih`. Introduce `p`.

Rewrite using `[Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih, hder]`. Establish `heig : ∀ (k : ℕ) (g : ↥(GK K)), ∃ x : ℚ_[l], actSt P (g : GQ l) (derivative^[k] b) = algebraMap ℚ_[l] (Bst P) x * derivative^[k] b`. Introduce `k g`. Take `⟨x, hx⟩` from `hst g`. Use `⟨x, ?_⟩` and prove the remaining obligations.

Rewrite using `[hiter, hx, Polynomial.algebraMap_apply, iterate_derivative_C_mul]`. Establish `hlin : ∀ p : Bst P, p.natDegree ≤ 1 → p.coeff 1 ≠ 0 → (∀ g : ↥(GK K), ∃ x : ℚ_[l], actSt P (g : GQ l) p = algebraMap ℚ_[l] (Bst P) x * p) → False`. Introduce `p hp1 hp0 hpe`. Take `⟨u, v, rfl⟩ : ∃ u v, p = C u * X + C v` from `⟨p.coeff 1, p.coeff 0, eq_X_add_C_of_natDegree_le_one hp1⟩`. Establish `hu0 : u ≠ 0` using `by simpa using hp0`.

Establish `hco : ∀ (g : GQ l), g ∈ GK K → ∃ x : ℚ_[l], P.actQ g u = algebraMap ℚ_[l] P.R.B x * u ∧ P.actQ g u * ((kummer P g : ℚ_[l]) • P.tB) + P.actQ g v = algebraMap ℚ_[l] P.R.B x * v`. Introduce `g hg`. Take `⟨x, hx⟩` from `hpe ⟨g, hg⟩`. Use `⟨x, ?_, ?_⟩` and prove the remaining obligations. Establish `h1` using `congrArg (fun q => Polynomial.coeff q 1) hx`.

Simplify `h1` using `[Polynomial.algebraMap_apply, mul_add]`. Establish `h0` using `congrArg (fun q => Polynomial.coeff q 0) hx`. Simplify `h0` using `[Polynomial.algebraMap_apply, mul_add]`. Establish `hU : IsUnit u` using `hLU u hu0 (fun g => by`. Take `⟨x, h1, -⟩` from `hco (g : GQ l) g.2`.

Conclude with `⟨x, by rw [P.PD_actB]; exact h1⟩)`. Take `⟨w, hw⟩ : ∃ w, w = v * ↑hU.unit⁻¹` from `⟨_, rfl⟩`. Establish `hwu : w * u = v` using `by rw [hw, mul_assoc, IsUnit.val_inv_mul, mul_one]`. Use `hno (-w) (fun g hg => ?_)` and prove the remaining obligations. Take `⟨x, h1, h0⟩` from `hco g hg`.

Establish `hne : P.actQ g u ≠ 0` using `(hU.map (P.actQ g)).ne_zero`. Establish `key : P.actQ g w * P.actQ g u = (w - (kummer P g : ℚ_[l]) • P.tB) * P.actQ g u`. Rewrite using `[← map_mul, hwu]`. Take the linear combination `h0 - w * h1 - (algebraMap ℚ_[l] P.R.B x) * hwu`. Establish `hgw : P.actQ g w = w - (kummer P g : ℚ_[l]) • P.tB` using `mul_right_cancel₀ hne key`.

Rewrite using `[map_neg, hgw]`. Expand and normalize the polynomial expressions, which then agree. Distinguish the cases in `hn : b.natDegree = 0`. Take `⟨c, rfl⟩ : ∃ c, b = C c` from `⟨_, eq_C_of_natDegree_eq_zero hn⟩`. Apply `IsUnit.map C` to reduce the goal to its premises.

Use `hLU c (fun h => hb (by rw [h, C_0])) (fun g => ?_)` and prove the remaining obligations. Take `⟨x, hx⟩` from `hst g`. Use `⟨x, ?_⟩` and prove the remaining obligations. Rewrite using `[P.PD_actB]`. Rewrite `hx` using `[actSt_C, Polynomial.algebraMap_apply, ← C_mul]`.

Conclude with `C_injective hx`. It suffices to derive a contradiction. Apply `hlin (derivative^[b.natDegree - 1] b)` to reduce the goal to its premises. Use `natDegree_iterate_derivative b (b.natDegree - 1)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Rewrite using `[coeff_iterate_derivative, show 1 + (b.natDegree - 1) = b.natDegree by omega]`. Use `smul_ne_zero ?_ (leadingCoeff_ne_zero.mpr hb)` and prove the remaining obligations. Introduce `h`. Rewrite `h` using `[Nat.descFactorial_eq_zero_iff_lt]`. Use linear arithmetic over natural numbers and integers.

Conclude with `heig (b.natDegree - 1)`.
-/
theorem isUnit_of_stable_line : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) [IsDomain P.R.B] (K : FinExt l),
  (∀ b : P.R.B, ¬ ∀ g ∈ GK K, P.actQ g b - b = (kummer P g : ℚ_[l]) • P.tB) → GlobalTheory.RegularRing.LineUnit (P.PD K) →
  ∀ b : Bst P, b ≠ 0 → (∀ g : ↥(GK K), ∃ x : ℚ_[l], actSt P (g : GQ l) b = algebraMap ℚ_[l] (Bst P) x * b) → IsUnit b := by
  intro l _ P _ K hno hLU b hb hst
  unfold GlobalTheory.RegularRing.LineUnit at hLU
  haveI : CharZero P.R.B := charZero_of_injective_algebraMap (algebraMap ℚ_[l] P.R.B).injective

  have hact : ∀ (g : GQ l) (p : Bst P),
      actSt P g p = stHom P (P.actQ g) (X + C ((kummer P g : ℚ_[l]) • P.tB)) p := fun g p => rfl

  have hder : ∀ (g : GQ l) (p : Bst P), derivative (actSt P g p) = actSt P g (derivative p) := by
    intro g p
    rw [hact, hact, derivative_stHom]
    simp
  have hiter : ∀ (k : ℕ) (g : GQ l) (p : Bst P),
      actSt P g (derivative^[k] p) = derivative^[k] (actSt P g p) := by
    intro k g
    induction k with
    | zero => intro p; rfl
    | succ k ih =>
      intro p
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih, hder]

  have heig : ∀ (k : ℕ) (g : ↥(GK K)), ∃ x : ℚ_[l],
      actSt P (g : GQ l) (derivative^[k] b) = algebraMap ℚ_[l] (Bst P) x * derivative^[k] b := by
    intro k g
    obtain ⟨x, hx⟩ := hst g
    refine ⟨x, ?_⟩
    rw [hiter, hx, Polynomial.algebraMap_apply, iterate_derivative_C_mul]

  have hlin : ∀ p : Bst P, p.natDegree ≤ 1 → p.coeff 1 ≠ 0 →
      (∀ g : ↥(GK K), ∃ x : ℚ_[l], actSt P (g : GQ l) p = algebraMap ℚ_[l] (Bst P) x * p) → False := by
    intro p hp1 hp0 hpe
    obtain ⟨u, v, rfl⟩ : ∃ u v, p = C u * X + C v := ⟨p.coeff 1, p.coeff 0, eq_X_add_C_of_natDegree_le_one hp1⟩
    have hu0 : u ≠ 0 := by simpa using hp0
    have hco : ∀ (g : GQ l), g ∈ GK K → ∃ x : ℚ_[l],
        P.actQ g u = algebraMap ℚ_[l] P.R.B x * u ∧
        P.actQ g u * ((kummer P g : ℚ_[l]) • P.tB) + P.actQ g v = algebraMap ℚ_[l] P.R.B x * v := by
      intro g hg
      obtain ⟨x, hx⟩ := hpe ⟨g, hg⟩
      refine ⟨x, ?_, ?_⟩
      · have h1 := congrArg (fun q => Polynomial.coeff q 1) hx
        simpa [Polynomial.algebraMap_apply, mul_add] using h1
      · have h0 := congrArg (fun q => Polynomial.coeff q 0) hx
        simpa [Polynomial.algebraMap_apply, mul_add] using h0
    have hU : IsUnit u := hLU u hu0 (fun g => by
      obtain ⟨x, h1, -⟩ := hco (g : GQ l) g.2
      exact ⟨x, by rw [P.PD_actB]; exact h1⟩)
    obtain ⟨w, hw⟩ : ∃ w, w = v * ↑hU.unit⁻¹ := ⟨_, rfl⟩
    have hwu : w * u = v := by rw [hw, mul_assoc, IsUnit.val_inv_mul, mul_one]
    refine hno (-w) (fun g hg => ?_)
    obtain ⟨x, h1, h0⟩ := hco g hg
    have hne : P.actQ g u ≠ 0 := (hU.map (P.actQ g)).ne_zero
    have key : P.actQ g w * P.actQ g u = (w - (kummer P g : ℚ_[l]) • P.tB) * P.actQ g u := by
      rw [← map_mul, hwu]
      linear_combination h0 - w * h1 - (algebraMap ℚ_[l] P.R.B x) * hwu
    have hgw : P.actQ g w = w - (kummer P g : ℚ_[l]) • P.tB := mul_right_cancel₀ hne key
    rw [map_neg, hgw]
    ring
  by_cases hn : b.natDegree = 0
  · obtain ⟨c, rfl⟩ : ∃ c, b = C c := ⟨_, eq_C_of_natDegree_eq_zero hn⟩
    apply IsUnit.map C
    refine hLU c (fun h => hb (by rw [h, C_0])) (fun g => ?_)
    obtain ⟨x, hx⟩ := hst g
    refine ⟨x, ?_⟩
    rw [P.PD_actB]
    rw [actSt_C, Polynomial.algebraMap_apply, ← C_mul] at hx
    exact C_injective hx
  · exfalso
    apply hlin (derivative^[b.natDegree - 1] b)
    · have := natDegree_iterate_derivative b (b.natDegree - 1)
      omega
    · rw [coeff_iterate_derivative, show 1 + (b.natDegree - 1) = b.natDegree by omega]
      refine smul_ne_zero ?_ (leadingCoeff_ne_zero.mpr hb)
      intro h
      rw [Nat.descFactorial_eq_zero_iff_lt] at h
      omega
    · exact heig (b.natDegree - 1)

end GlobalTheory.Pst.StLine
