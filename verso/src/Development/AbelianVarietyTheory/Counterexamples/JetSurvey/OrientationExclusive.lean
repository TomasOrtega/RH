import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.H1algStatement
import Formalism.LocalToGlobal.ProjectiveLattices.DepRun
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.SpanResCharNeBot
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.WeightFloorInequalities

noncomputable section

namespace GlobalTheory.DepthBoundProbe

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1

variable {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L}

/- English proof (translation)
Proceed by induction on `q with`. Consider the case `zero => simp`. Consider the case `succ q ih`. Rewrite using `[← add_assoc, Nat.choose_succ_succ' (p + q) 1, Nat.choose_succ_succ' q 1, ih]`. Simplify using `only [Nat.choose_one_right]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem choose_two_add (p q : ℕ) : (p + q).choose 2 = p * q + p.choose 2 + q.choose 2 := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [← add_assoc, Nat.choose_succ_succ' (p + q) 1, Nat.choose_succ_succ' q 1, ih]
    simp only [Nat.choose_one_right]
    ring

/- English proof (translation)
Rewrite using `[Tp.Dp_eq]`. Unfold `WeightFamilies.dimY`. Use `congr 1`. Establish `hr : D.R.r = (D.R.sigW j).1 + (D.R.sigW j).2`. Use `hj.1` as an intermediate fact.

Use `hj.2` as an intermediate fact. Simplify using `only [Ranks.sigW, Ranks.r]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hr, choose_two_add, Nat.choose_two_right, Nat.choose_two_right]`.
-/
theorem dimY_eq (Tp : ParamsT D L P) {j : ℕ} (hj : InR D j) : WeightFamilies.dimY D j = Tp.Dp := by
  rw [Tp.Dp_eq]
  unfold WeightFamilies.dimY
  congr 1
  have hr : D.R.r = (D.R.sigW j).1 + (D.R.sigW j).2 := by
    have := hj.1; have := hj.2
    simp only [Ranks.sigW, Ranks.r]; omega
  rw [hr, choose_two_add, Nat.choose_two_right, Nat.choose_two_right]

/- English proof (translation)
Establish `h1` using `hj.1`. Establish `h2` using `hj.2`. Establish `hk : 5 ≤ D.R.k` using `by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega`. Establish `hs : (D.R.sigW j).1 = D.R.k + j - 1` using `rfl`. Establish `e1` using `kaWt_big D hK (even_nV Tp) j h1 h2 τ i`.

Establish `e2` using `(hK j h1 h2 τ).1 i`. Establish `hc` using `P.e_centred τ ⟨j - 1, by omega⟩`. Establish `h0` using `Tp.heightBound_ge_order_sq`. Establish `hi1 : ¬ (i.1 < D.R.k - 1)` using `by omega`. Establish `hb : i.1 - (D.R.k - 1) < D.R.m` using `by omega`.

Establish `hidx : (⟨i.1 - (D.R.k - 1), hb⟩ : Fin D.R.m) = ⟨j - 1, by omega⟩` using `Fin.ext (by show i.1 - (D.R.k - 1) = j - 1; omega)`. Establish `hcast : ((i.1 : ℕ) : ℚ) = (D.R.k : ℚ) + j - 1 - 1`. Establish `: i.1 + 2 = D.R.k + j` using `by omega`. Establish `: ((i.1 : ℕ) : ℚ) + 2 = (D.R.k : ℚ) + j` using `by exact_mod_cast this`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite `e2` using `[DV.aPlusQ_eq, hcast]`. Unfold `DV.sigPar DV.eQ at e2`. Rewrite `e2` using `[dif_neg hi1, dif_pos hb, dif_pos ⟨h1, h2⟩, hidx]`. Establish `ht : 5 ≤ D.R.t`. Establish `a1` using `Tp.split`.

Establish `a2` using `Tp.nP_eq`. Establish `a3` using `Tp.TO_nW`. Establish `a4` using `Tp.nW_40`. Establish `: 1 * Tp.nWn ≤ Tp.TO * Tp.nWn` using `Nat.mul_le_mul_right _ (by have := Tp.TO_40; omega)`. Establish `: Tp.TO * 40 ≤ Tp.TO * Tp.nWn` using `Nat.mul_le_mul_left _ a4`.

Use linear arithmetic over natural numbers and integers. Establish `ht' : (5 : ℝ) ≤ D.R.t` using `by exact_mod_cast ht`. Establish `e3 : ((D.what₂.kaBig j τ i : ℤ) : ℝ) = ((((D.hc τ).e ⟨j - 1, by omega⟩ - (D.hc τ).b ⟨j - 1, by omega⟩ : ℚ)) : ℝ) - ((D.R.t : ℝ) + 1) / 2`. Use `congrArg (fun q : ℚ => (q : ℝ)) e2` as an intermediate fact. Move the coercions through the operations in `at this ⊢`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h4` using `(abs_le.1 hc).1`. Establish `: (2 * (Tp.TO : ℝ) ^ 2) ≤ ((D.what₂.kaBig j τ i : ℤ) : ℝ)` using `by rw [e3]; linarith`. Unfold `kaR`. Rewrite using `[e1]`.

Conclude with `this` after adjusting the coercions.
-/
theorem kappa_last (Tp : ParamsT D L P) (hK : DV.KapDef D) {j : ℕ} (hj : InR D j) (τ : D.what₂.Tau)
    (i : Fin (D.R.sigW j).1) (hi : i.1 + 1 = (D.R.sigW j).1) :
    2 * (Tp.TO : ℤ) ^ 2 ≤ ((kaR Tp hK j).aP τ i : ℤ) := by
  have h1 := hj.1
  have h2 := hj.2
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hs : (D.R.sigW j).1 = D.R.k + j - 1 := rfl
  have e1 := kaWt_big D hK (even_nV Tp) j h1 h2 τ i
  have e2 := (hK j h1 h2 τ).1 i
  have hc := P.e_centred τ ⟨j - 1, by omega⟩
  have h0 := Tp.heightBound_ge_order_sq
  have hi1 : ¬ (i.1 < D.R.k - 1) := by omega
  have hb : i.1 - (D.R.k - 1) < D.R.m := by omega
  have hidx : (⟨i.1 - (D.R.k - 1), hb⟩ : Fin D.R.m) = ⟨j - 1, by omega⟩ := Fin.ext (by show i.1 - (D.R.k - 1) = j - 1; omega)
  have hcast : ((i.1 : ℕ) : ℚ) = (D.R.k : ℚ) + j - 1 - 1 := by
    have : i.1 + 2 = D.R.k + j := by omega
    have : ((i.1 : ℕ) : ℚ) + 2 = (D.R.k : ℚ) + j := by exact_mod_cast this
    linarith
  rw [DV.aPlusQ_eq, hcast] at e2
  unfold DV.sigPar DV.eQ at e2
  rw [dif_neg hi1, dif_pos hb, dif_pos ⟨h1, h2⟩, hidx] at e2
  have ht : 5 ≤ D.R.t := by
    have a1 := Tp.split; have a2 := Tp.nP_eq; have a3 := Tp.TO_nW; have a4 := Tp.nW_40
    have : 1 * Tp.nWn ≤ Tp.TO * Tp.nWn := Nat.mul_le_mul_right _ (by have := Tp.TO_40; omega)
    have : Tp.TO * 40 ≤ Tp.TO * Tp.nWn := Nat.mul_le_mul_left _ a4
    omega
  have ht' : (5 : ℝ) ≤ D.R.t := by exact_mod_cast ht
  have e3 : ((D.what₂.kaBig j τ i : ℤ) : ℝ) =
      ((((D.hc τ).e ⟨j - 1, by omega⟩ - (D.hc τ).b ⟨j - 1, by omega⟩ : ℚ)) : ℝ) - ((D.R.t : ℝ) + 1) / 2 := by
    have := congrArg (fun q : ℚ => (q : ℝ)) e2
    push_cast at this ⊢
    linarith
  have h4 := (abs_le.1 hc).1
  have : (2 * (Tp.TO : ℝ) ^ 2) ≤ ((D.what₂.kaBig j τ i : ℤ) : ℝ) := by rw [e3]; linarith
  unfold kaR
  rw [e1]
  exact_mod_cast this

/- English proof (translation)
Introduce `τ i hi`. Establish `hn : ¬ i.1 + 1 < (D.R.sigW j).1` using `by omega`. Establish `hk` using `kappa_last Tp hK hj τ i hi`. Use `show 1 ≤ ofGaps (lGapP D (kaR Tp hK j) Tp.TO Tp.nWn τ) i`. Rewrite using `[ofGaps_last _ _ hn]`.

Unfold `lGapP`. Rewrite using `[if_neg hn]`. Establish `hp : (0 : ℤ) < (WeightAlgebra.Tp D j Tp.TO : ℤ)` using `by unfold WeightAlgebra.Tp; push_cast; omega`. Rewrite using `[Int.fdiv_eq_ediv_of_nonneg _ hp.le]`. Establish `h1 : ((Tp.Dp : ℤ) + 2) * Tp.nWn + 2 * D.R.r ≤ Tp.TO` using `by exact_mod_cast Tp.TO_nW`.

Establish `h40 : 40 * ((Tp.Dp : ℤ) + 2) ≤ Tp.TO` using `by exact_mod_cast Tp.TO_40`. Establish `: (1 : ℤ) ≤ (((kaR Tp hK j).aP τ i : ℤ) - ((WeightFamilies.dimY D j : ℤ) + 2) * Tp.nWn - 2 * D.R.r) / (WeightAlgebra.Tp D j Tp.TO : ℤ)`. Rewrite using `[Int.le_ediv_iff_mul_le hp]`. Unfold `WeightAlgebra.Tp`. Rewrite using `[dimY_eq Tp hj]`.

Use `push_cast`. Use the polynomial consequences of the given equalities and inequalities. Use linear arithmetic over natural numbers and integers.
-/
theorem lR_lastPos (Tp : ParamsT D L P) (hK : DV.KapDef D) {j : ℕ} (hj : InR D j) : (lR Tp hK j).LastPos := by
  intro τ i hi
  have hn : ¬ i.1 + 1 < (D.R.sigW j).1 := by omega
  have hk := kappa_last Tp hK hj τ i hi
  show 1 ≤ ofGaps (lGapP D (kaR Tp hK j) Tp.TO Tp.nWn τ) i
  rw [ofGaps_last _ _ hn]
  unfold lGapP
  rw [if_neg hn]
  have hp : (0 : ℤ) < (WeightAlgebra.Tp D j Tp.TO : ℤ) := by unfold WeightAlgebra.Tp; push_cast; omega
  rw [Int.fdiv_eq_ediv_of_nonneg _ hp.le]
  have h1 : ((Tp.Dp : ℤ) + 2) * Tp.nWn + 2 * D.R.r ≤ Tp.TO := by exact_mod_cast Tp.TO_nW
  have h40 : 40 * ((Tp.Dp : ℤ) + 2) ≤ Tp.TO := by exact_mod_cast Tp.TO_40
  have : (1 : ℤ) ≤ (((kaR Tp hK j).aP τ i : ℤ) - ((WeightFamilies.dimY D j : ℤ) + 2) * Tp.nWn - 2 * D.R.r) / (WeightAlgebra.Tp D j Tp.TO : ℤ) := by
    rw [Int.le_ediv_iff_mul_le hp]
    unfold WeightAlgebra.Tp
    rw [dimY_eq Tp hj]
    push_cast
    nlinarith
  omega

/- English proof (translation)
Establish `hk : 5 ≤ D.R.k` using `by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega`. Establish `hs : (D.R.sigW j).1 = D.R.k + j - 1` using `rfl`. Establish `h1` using `lR_lastPos Tp hK hj τ ⟨(D.R.sigW j).1 - 1, by omega⟩ (by show (D.R.sigW j).1 - 1 + 1 = _; omega)`. Unfold `WeightAlgebra.DF WeightAlgebra.degP`. Use `le_trans ?_ (Finset.single_le_sum (f := fun τ => (∑ i, (lR Tp hK j).aP τ i) + ∑ i, (lR Tp hK j).aM τ i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ τ))` and prove the remaining obligations.

Conclude with `le_trans (le_trans h1 (Finset.single_le_sum (f := fun i => (lR Tp hK j).aP τ i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _))) (Nat.le_add_right _ _)`.
-/
theorem one_le_DF (Tp : ParamsT D L P) (hK : DV.KapDef D) {j : ℕ} (hj : InR D j) (τ : D.what₂.Tau) :
    1 ≤ WeightAlgebra.DF (lR Tp hK j) := by
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hs : (D.R.sigW j).1 = D.R.k + j - 1 := rfl
  have h1 := lR_lastPos Tp hK hj τ ⟨(D.R.sigW j).1 - 1, by omega⟩ (by show (D.R.sigW j).1 - 1 + 1 = _; omega)
  unfold WeightAlgebra.DF WeightAlgebra.degP
  refine le_trans ?_ (Finset.single_le_sum (f := fun τ => (∑ i, (lR Tp hK j).aP τ i) + ∑ i, (lR Tp hK j).aM τ i)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ τ))
  exact le_trans (le_trans h1 (Finset.single_le_sum (f := fun i => (lR Tp hK j).aP τ i) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ _))) (Nat.le_add_right _ _)

end GlobalTheory.DepthBoundProbe
