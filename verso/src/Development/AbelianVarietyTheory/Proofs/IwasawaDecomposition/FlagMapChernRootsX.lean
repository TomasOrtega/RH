import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchubGamApply
import Formalism.DegreeFormula.PointDegree.PowSum

noncomputable section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric
open Classical

namespace GlobalTheory.Schubert.RelKill

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem esymm_cons_succ {R : Type*} [CommSemiring R] (a : R) (s : Multiset R) (n : ℕ) :
    (a ::ₘ s).esymm (n + 1) = s.esymm (n + 1) + a * s.esymm n := by
  simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_map, Multiset.sum_map_mul_left]

/- English proof (translation)
Proceed by induction. Treat this case separately. Split into cases according to the possible forms of the given data. Treat this case separately. Treat this case separately.

Treat this case separately. Rewrite the conclusion using the stated equalities. Split into cases according to the possible forms of the given data. Treat this case separately. Treat this case separately.
-/
theorem coeff_prod_one_add {R : Type*} [CommSemiring R] (s : Multiset R) (n : ℕ) :
    ((s.map fun a => (1 + Polynomial.C a * Polynomial.X : Polynomial R)).prod).coeff n = s.esymm n := by
  induction s using Multiset.induction_on generalizing n with
  | empty =>
    cases n with
    | zero => simp [Multiset.esymm]
    | succ n => simp [Multiset.esymm, Polynomial.coeff_one, Multiset.powersetCard_zero_right]
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, add_mul, one_mul, mul_assoc, Polynomial.coeff_add,
      Polynomial.coeff_C_mul]
    cases n with
    | zero => simp [ih, Multiset.esymm]
    | succ n => rw [Polynomial.coeff_X_mul, ih, ih, esymm_cons_succ]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem esymm_add {R : Type*} [CommSemiring R] (s t : Multiset R) (n : ℕ) :
    (s + t).esymm n = ∑ i ∈ Finset.range (n + 1), s.esymm i * t.esymm (n - i) := by
  rw [← coeff_prod_one_add, Multiset.map_add, Multiset.prod_add, Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_prod_one_add]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules.
-/
theorem univ_map_eq_range {R : Type*} [Zero R] (m : ℕ) (f : Fin m → R) :
    (Finset.univ : Finset (Fin m)).val.map f =
      (Multiset.range m).map (fun i => if h : i < m then f ⟨i, h⟩ else 0) := by
  have h1 : Multiset.range m = (Finset.univ : Finset (Fin m)).val.map Fin.val := by
    rw [Fin.univ_val_map, List.ofFn_eq_map, List.map_coe_finRange_eq_range]; rfl
  rw [h1, Multiset.map_map]
  refine Multiset.map_congr rfl fun i _ => ?_
  simp [i.2]

variable {H : Host E} (Dw : Datum H)

def rootSeq (τ : GlobalTheory.AllWt.Psi H) (i : ℕ) : MvPolynomial (GlobalTheory.AllWt.Psi H × Fin (Dw.p + Dw.q)) ℝ :=
  if h : i < Dw.p + Dw.q then X (τ, ⟨i, h⟩) else 0

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem flagMap_chernRoots_X (x : E →+* ℂ) (a : ℕ) :
    flagMap Dw (chernRoots Dw.mult (X (x, a))) =
      ((Finset.univ : Finset (Fin (Dw.mult x))).val.map (fun i => flagRoot Dw ⟨x, i⟩)).esymm a := by
  rw [chernRoots, aeval_X, flagMap, aeval_rename, aeval_esymm_eq_multiset_esymm]
  rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem roots_mem (τ : GlobalTheory.AllWt.Psi H) :
    (Finset.univ : Finset (Fin (Dw.mult τ.1))).val.map (fun i => flagRoot Dw ⟨τ.1, i⟩) =
      (Multiset.range Dw.p).map (rootSeq Dw τ) := by
  rw [univ_map_eq_range]
  have hm := GlobalTheory.PointChern.mult_of_mem Dw τ.2
  rw [show Multiset.range (Dw.mult τ.1) = Multiset.range Dw.p by rw [hm]]
  refine Multiset.map_congr rfl fun i hi => ?_
  rw [Multiset.mem_range] at hi
  have hi' : i < Dw.mult τ.1 := by omega
  have hi2 : i < Dw.p + Dw.q := by omega
  rw [dif_pos hi', rootSeq, dif_pos hi2, flagRoot, dif_pos τ.2]

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Use linear arithmetic over natural numbers and integers. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Use linear arithmetic over natural numbers and integers. Fix the arbitrary inputs or assume the hypotheses.
-/
theorem range_reflect (q : ℕ) : (Multiset.range q).map (fun i => q - 1 - i) = Multiset.range q := by
  have hinj : ∀ x ∈ Multiset.range q, ∀ y ∈ Multiset.range q, q - 1 - x = q - 1 - y → x = y := by
    intro x hx y hy h; rw [Multiset.mem_range] at hx hy; omega
  refine (Multiset.Nodup.ext ((Multiset.nodup_range q).map_on hinj) (Multiset.nodup_range q)).2 fun a => ?_
  simp only [Multiset.mem_map, Multiset.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; omega
  · intro ha; exact ⟨q - 1 - a, by omega, by omega⟩

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem roots_conj (τ : GlobalTheory.AllWt.Psi H) :
    (Finset.univ : Finset (Fin (Dw.mult (conjEmb τ.1)))).val.map
        (fun i => flagRoot Dw ⟨conjEmb τ.1, i⟩) =
      ((Multiset.range Dw.q).map (fun i => rootSeq Dw τ (Dw.p + i))).map Neg.neg := by
  rw [univ_map_eq_range]
  have hn := GlobalTheory.AllWt.conj_not_mem τ
  have hm := GlobalTheory.PointChern.mult_of_not_mem Dw hn
  rw [show Multiset.range (Dw.mult (conjEmb τ.1)) = Multiset.range Dw.q by rw [hm]]
  conv_rhs => rw [← range_reflect Dw.q, Multiset.map_map, Multiset.map_map]
  refine Multiset.map_congr rfl fun i hi => ?_
  rw [Multiset.mem_range] at hi
  have hi' : i < Dw.mult (conjEmb τ.1) := by omega
  have hi2 : Dw.p + (Dw.q - 1 - i) < Dw.p + Dw.q := by omega
  have h' : conjEmb (conjEmb τ.1) (H.rt : E) = H.rt0 := by
    rw [GlobalTheory.AllWt.conjEmb_conjEmb]; exact τ.2
  have e : (⟨conjEmb (conjEmb τ.1), h'⟩ : GlobalTheory.AllWt.Psi H) = τ :=
    Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb _)
  simp only [dif_pos hi', flagRoot, dif_neg hn, Function.comp_apply, rootSeq, dif_pos hi2, e]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem rename_esymm (τ : GlobalTheory.AllWt.Psi H) (k : ℕ) :
    rename (fun i : Fin (Dw.p + Dw.q) => (τ, i)) (esymm (Fin (Dw.p + Dw.q)) ℝ k) =
      ((Multiset.range Dw.p).map (rootSeq Dw τ) +
        (Multiset.range Dw.q).map (fun i => rootSeq Dw τ (Dw.p + i))).esymm k := by
  rw [← aeval_X_left_apply (rename _ _), aeval_rename, aeval_esymm_eq_multiset_esymm, univ_map_eq_range, Multiset.range_add, Multiset.map_add,
    Multiset.map_map]
  rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Take a linear combination of the given relations to obtain the conclusion.
-/
theorem flagMap_relPoly (τ : GlobalTheory.AllWt.Psi H) (k : ℕ) :
    flagMap Dw (chernRoots Dw.mult (GlobalTheory.PointChern.relPoly τ k)) =
      rename (fun i : Fin (Dw.p + Dw.q) => (τ, i)) (esymm (Fin (Dw.p + Dw.q)) ℝ k) := by
  rw [rename_esymm, esymm_add, GlobalTheory.PointChern.relPoly, map_sum, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, map_mul, map_mul, map_mul, flagMap_chernRoots_X, flagMap_chernRoots_X, roots_mem, roots_conj,
    Multiset.esymm_neg]
  have hC : flagMap Dw (chernRoots Dw.mult (C ((-1 : ℝ) ^ (k - a)))) = (-1) ^ (k - a) := by
    simp [flagMap, chernRoots]
  rw [hC]
  have h1 : ((-1 : MvPolynomial (GlobalTheory.AllWt.Psi H × Fin (Dw.p + Dw.q)) ℝ) ^ (k - a)) * (-1) ^ (k - a) = 1 := by
    rw [← mul_pow]; simp
  linear_combination (((Multiset.range Dw.p).map (rootSeq Dw τ)).esymm a *
    ((Multiset.range Dw.q).map (fun i => rootSeq Dw τ (Dw.p + i))).esymm (k - a)) * h1

end GlobalTheory.Schubert.RelKill

namespace GlobalTheory.Schubert

end GlobalTheory.Schubert
