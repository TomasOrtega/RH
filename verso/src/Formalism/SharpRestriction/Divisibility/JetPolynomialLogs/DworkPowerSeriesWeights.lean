import Mathlib
import Formalism.SharpRestriction.Divisibility.ProductZerothFirstParts
import Formalism.GaussJetBounds.ThmAGauss
import Formalism.GaussJetBounds.OneLetterGauss
import Formalism.GaussJetBounds.GaussJetProofs.WeightsAddOverOrbitFamily

noncomputable section

open scoped BigOperators

namespace Formalism.MainNotions.DIV.Bridge.DworkPowerSeriesWeights

open Formalism.MainNotions Formalism.DworkPowerSeriesWeights Formalism.IncomingBounds

/- English proof (translation)
Establish `h : (0, (c : ℕ)) ∈ μ` using `YoungDiagram.mem_iff_lt_rowLen.2 c.2`. Conclude with `YoungDiagram.mem_iff_lt_colLen.1 h`.
-/
theorem yd_one_le_colLen (μ : YoungDiagram) (c : Fin (μ.rowLen 0)) : 1 ≤ μ.colLen c := by
  have h : (0, (c : ℕ)) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.2 c.2
  exact YoungDiagram.mem_iff_lt_colLen.1 h

/- English proof (translation)
The claim follows from `μ.colLen_anti 0 c (Nat.zero_le c)`.
-/
theorem yd_colLen_le (μ : YoungDiagram) (c : ℕ) : μ.colLen c ≤ μ.colLen 0 := μ.colLen_anti 0 c (Nat.zero_le c)

/- English proof (translation)
Rewrite using `[← Finset.card_range (μ.rowLen 1)]`. Use `Finset.card_bij (fun (c : Fin (μ.rowLen 0)) _ => (c : ℕ)) ?_ ?_ ?_` and prove the remaining obligations. Introduce `c hc`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hc`. Rewrite using `[Finset.mem_range, ← YoungDiagram.mem_iff_lt_rowLen, YoungDiagram.mem_iff_lt_colLen]`.

Conclude with `hc`. Introduce `a _ b _ h`. Conclude with `Fin.ext h`. Introduce `b hb`. Rewrite `hb` using `[Finset.mem_range]`.

Use `⟨⟨b, lt_of_lt_of_le hb (μ.rowLen_anti 0 1 zero_le_one)⟩, ?_, rfl⟩` and prove the remaining obligations. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Establish `h1 : (1, b) ∈ μ` using `YoungDiagram.mem_iff_lt_rowLen.2 hb`. Conclude with `YoungDiagram.mem_iff_lt_colLen.1 h1`.
-/
theorem young_second_row_length_count (μ : YoungDiagram) :
    (Finset.univ.filter (fun c : Fin (μ.rowLen 0) => 2 ≤ μ.colLen c)).card = μ.rowLen 1 := by
  rw [← Finset.card_range (μ.rowLen 1)]
  refine Finset.card_bij (fun (c : Fin (μ.rowLen 0)) _ => (c : ℕ)) ?_ ?_ ?_
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    rw [Finset.mem_range, ← YoungDiagram.mem_iff_lt_rowLen, YoungDiagram.mem_iff_lt_colLen]
    exact hc
  · intro a _ b _ h
    exact Fin.ext h
  · intro b hb
    rw [Finset.mem_range] at hb
    refine ⟨⟨b, lt_of_lt_of_le hb (μ.rowLen_anti 0 1 zero_le_one)⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have h1 : (1, b) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.2 hb
    exact YoungDiagram.mem_iff_lt_colLen.1 h1

/- English proof (translation)
Establish `H : ∀ p ∈ μ.cells, p.2 ∈ Finset.range (μ.rowLen 0)`. Introduce `p hp`. Rewrite using `[Finset.mem_range]`. Establish `h0 : (0, p.2) ∈ μ` using `μ.up_left_mem (Nat.zero_le p.1) le_rfl ((YoungDiagram.mem_cells p).1 hp)`. Conclude with `YoungDiagram.mem_iff_lt_rowLen.1 h0`.

Rewrite using `[Finset.card_eq_sum_card_fiberwise H, Finset.sum_range]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[YoungDiagram.colLen_eq_card]`. Both sides reduce to the same expression.
-/
theorem yd_size (μ : YoungDiagram) : μ.cells.card = ∑ c : Fin (μ.rowLen 0), μ.colLen c := by
  have H : ∀ p ∈ μ.cells, p.2 ∈ Finset.range (μ.rowLen 0) := by
    intro p hp
    rw [Finset.mem_range]
    have h0 : (0, p.2) ∈ μ := μ.up_left_mem (Nat.zero_le p.1) le_rfl ((YoungDiagram.mem_cells p).1 hp)
    exact YoungDiagram.mem_iff_lt_rowLen.1 h0
  rw [Finset.card_eq_sum_card_fiberwise H, Finset.sum_range]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [YoungDiagram.colLen_eq_card]
  rfl

/- English proof (translation)
Establish `hset : Formalism.BasicNotions.lpFeasible l d D = {t : ℝ | ∃ x, Formalism.IncomingBounds.IsFlow l d D x ∧ Formalism.IncomingBounds.flowVal d x = t}`. Use extensionality with `y`. Simplify using `only [Formalism.BasicNotions.lpFeasible, Formalism.IncomingBounds.IsFlow, Formalism.IncomingBounds.flowVal, Formalism.IncomingBounds.oddLevels, Set.mem_setOf_eq, Finset.sum_filter]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨xs, h0, hz, hc, rfl⟩`.

Establish `hz' : ∀ s i, (if Odd i then xs s i else 0) = xs s i`. Introduce `s i`. Distinguish the cases in `ho : Odd i`. Rewrite using `[if_pos ho]`. Rewrite using `[if_neg ho, hz s i (Or.inl ho)]`.

Use `⟨xs, ⟨h0, fun s => ?_⟩, ?_⟩` and prove the remaining obligations. Establish `e1 : ∑ i ∈ Finset.range d, (if Odd i then (l : ℝ) ^ i * xs s i else 0) = ∑ i ∈ Finset.range d, (l : ℝ) ^ i * xs s i`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `ho : Odd i`. Rewrite using `[if_pos ho]`.

Rewrite using `[if_neg ho, hz s i (Or.inl ho), mul_zero]`. Establish `e2 : ∑ i ∈ Finset.range d, (if Odd i then xs (s - (i : ZMod d)) i else 0) = ∑ i ∈ Finset.range d, xs (s - (i : ZMod d)) i` using `Finset.sum_congr rfl fun i _ => hz' _ _`. Rewrite using `[e1, e2]`. Conclude with `hc s`. Conclude with `Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i _ => hz' s i`.

Introduce and unpack `⟨x, ⟨h0, hc⟩, rfl⟩`. Use `⟨fun s i => if Odd i ∧ i < d then x s i else 0, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `s i dsimp only split_ifs`. Conclude with `h0 s i`. Conclude with `le_rfl`.

Introduce `s i h dsimp only`. Rewrite using `[if_neg]`. Introduce and unpack `⟨h1, h2⟩`. Break down `h with h | h` into its components or cases. Conclude with `h h1`.

Use linear arithmetic over natural numbers and integers. Introduce `s`. Establish `e1 : ∑ i ∈ Finset.range d, (l : ℝ) ^ i * (if Odd i ∧ i < d then x s i else 0) = ∑ i ∈ Finset.range d, (if Odd i then (l : ℝ) ^ i * x s i else 0)`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Establish `hid` using `Finset.mem_range.1 hi`.

Apply the tactic sequence `by_cases ho : Odd i <;> simp [ho, hid]`. Establish `e2 : ∑ i ∈ Finset.range d, (if Odd i ∧ i < d then x (s - (i : ZMod d)) i else 0) = ∑ i ∈ Finset.range d, (if Odd i then x (s - (i : ZMod d)) i else 0)`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Establish `hid` using `Finset.mem_range.1 hi`. Apply the tactic sequence `by_cases ho : Odd i <;> simp [ho, hid]`.

Rewrite using `[e1, e2]`. Conclude with `hc s`. Use `Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Establish `hid` using `Finset.mem_range.1 hi`. Apply the tactic sequence `by_cases ho : Odd i <;> simp [ho, hid]`.

Unfold `Formalism.BasicNotions.lpF Formalism.IncomingBounds.Fnum Formalism.IncomingBounds.maxFlow Formalism.IncomingBounds.gam`. Rewrite using `[hset]`.
-/
theorem lpF_eq_Fnum (l d : ℕ) [NeZero d] (D : ZMod d → ℝ) : Formalism.BasicNotions.lpF l d D = Fnum l d D := by
  have hset : Formalism.BasicNotions.lpFeasible l d D = {t : ℝ | ∃ x, Formalism.IncomingBounds.IsFlow l d D x ∧ Formalism.IncomingBounds.flowVal d x = t} := by
    ext y
    simp only [Formalism.BasicNotions.lpFeasible, Formalism.IncomingBounds.IsFlow, Formalism.IncomingBounds.flowVal, Formalism.IncomingBounds.oddLevels,
      Set.mem_setOf_eq, Finset.sum_filter]
    constructor
    · rintro ⟨xs, h0, hz, hc, rfl⟩
      have hz' : ∀ s i, (if Odd i then xs s i else 0) = xs s i := by
        intro s i
        by_cases ho : Odd i
        · rw [if_pos ho]
        · rw [if_neg ho, hz s i (Or.inl ho)]
      refine ⟨xs, ⟨h0, fun s => ?_⟩, ?_⟩
      · have e1 : ∑ i ∈ Finset.range d, (if Odd i then (l : ℝ) ^ i * xs s i else 0) =
            ∑ i ∈ Finset.range d, (l : ℝ) ^ i * xs s i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          by_cases ho : Odd i
          · rw [if_pos ho]
          · rw [if_neg ho, hz s i (Or.inl ho), mul_zero]
        have e2 : ∑ i ∈ Finset.range d, (if Odd i then xs (s - (i : ZMod d)) i else 0) =
            ∑ i ∈ Finset.range d, xs (s - (i : ZMod d)) i :=
          Finset.sum_congr rfl fun i _ => hz' _ _
        rw [e1, e2]
        exact hc s
      · exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i _ => hz' s i
    · rintro ⟨x, ⟨h0, hc⟩, rfl⟩
      refine ⟨fun s i => if Odd i ∧ i < d then x s i else 0, ?_, ?_, ?_, ?_⟩
      · intro s i
        dsimp only
        split_ifs
        · exact h0 s i
        · exact le_rfl
      · intro s i h
        dsimp only
        rw [if_neg]
        rintro ⟨h1, h2⟩
        rcases h with h | h
        · exact h h1
        · omega
      · intro s
        have e1 : ∑ i ∈ Finset.range d, (l : ℝ) ^ i * (if Odd i ∧ i < d then x s i else 0) =
            ∑ i ∈ Finset.range d, (if Odd i then (l : ℝ) ^ i * x s i else 0) := by
          refine Finset.sum_congr rfl fun i hi => ?_
          have hid := Finset.mem_range.1 hi
          by_cases ho : Odd i <;> simp [ho, hid]
        have e2 : ∑ i ∈ Finset.range d, (if Odd i ∧ i < d then x (s - (i : ZMod d)) i else 0) =
            ∑ i ∈ Finset.range d, (if Odd i then x (s - (i : ZMod d)) i else 0) := by
          refine Finset.sum_congr rfl fun i hi => ?_
          have hid := Finset.mem_range.1 hi
          by_cases ho : Odd i <;> simp [ho, hid]
        rw [e1, e2]
        exact hc s
      · refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i hi => ?_
        have hid := Finset.mem_range.1 hi
        by_cases ho : Odd i <;> simp [ho, hid]
  unfold Formalism.BasicNotions.lpF Formalism.IncomingBounds.Fnum Formalism.IncomingBounds.maxFlow Formalism.IncomingBounds.gam
  rw [hset]

/- English proof (translation)
Establish `h1 : ((l : ℕ) : ℂ_[l]) = (((l : ℕ) : PadicAlgCl l) : ℂ_[l])` using `by simp`. Rewrite using `[h1, PadicComplex.norm_extends]`. Establish `h2 : ((l : ℕ) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l])` using `by simp`. Rewrite using `[h2, PadicAlgCl.norm_extends, Padic.norm_p]`.
-/
theorem norm_l (l : ℕ) [Fact l.Prime] : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  have h1 : ((l : ℕ) : ℂ_[l]) = (((l : ℕ) : PadicAlgCl l) : ℂ_[l]) := by simp
  rw [h1, PadicComplex.norm_extends]
  have h2 : ((l : ℕ) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
  rw [h2, PadicAlgCl.norm_extends, Padic.norm_p]

/- English proof (translation)
Rewrite using `[norm_l, Real.inv_rpow (Nat.cast_nonneg _), Real.rpow_neg (Nat.cast_nonneg _)]`.
-/
theorem norm_l_rpow (l : ℕ) [Fact l.Prime] (x : ℝ) : ‖(l : ℂ_[l])‖ ^ x = (l : ℝ) ^ (-x) := by
  rw [norm_l, Real.inv_rpow (Nat.cast_nonneg _), Real.rpow_neg (Nat.cast_nonneg _)]

section Loc

variable (L : product_zeroth_first_parts.Loc)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cap_eq (s : ZMod L.d) :
    L.cap s = capL L.d L.TT (fun s => (L.nu s).rowLen 0) (fun s => (L.nu s).rowLen 1) s := by
  rfl

/- English proof (translation)
Unfold `product_zeroth_first_parts.Loc.Wc Formalism.IncomingBounds.Wcap`. Use `congr 1`. Use extensionality with `c`. Simplify using `only [Set.mem_setOf_eq, Set.mem_image]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨i, hi, hl, rfl⟩`. Conclude with `⟨i, ⟨hi, hl⟩, (cap_eq L _).symm⟩`. Introduce and unpack `⟨i, ⟨hi, hl⟩, rfl⟩`. Conclude with `⟨i, hi, hl, (cap_eq L _).symm⟩`.
-/
theorem Wc_eq (s : ZMod L.d) :
    L.Wc s = Wcap L.l L.d L.TT (fun s => (L.nu s).rowLen 0) (fun s => (L.nu s).rowLen 1)
      (fun s => (L.nu s).cells.card) s := by
  unfold product_zeroth_first_parts.Loc.Wc Formalism.IncomingBounds.Wcap
  congr 1
  ext c
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨i, hi, hl, rfl⟩
    exact ⟨i, ⟨hi, hl⟩, (cap_eq L _).symm⟩
  · rintro ⟨i, ⟨hi, hl⟩, rfl⟩
    exact ⟨i, hi, hl, (cap_eq L _).symm⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem topTerm_eq (s : ZMod L.d) :
    L.topTerm s = topTerm L.l L.d L.TT (fun s => (L.nu s).rowLen 0) (fun s => (L.nu s).rowLen 1) s := by
  rfl

/- English proof (translation)
Unfold `product_zeroth_first_parts.Loc.FD`. Rewrite using `[lpF_eq_Fnum]`. Both sides reduce to the same expression.
-/
theorem FD_eq : L.FD = Fnum L.l L.d
    (fun s => (Dl L.d L.TT (fun s => (L.nu s).rowLen 0) (fun s => (L.nu s).cells.card) s : ℝ)) := by
  unfold product_zeroth_first_parts.Loc.FD
  rw [lpF_eq_Fnum]
  rfl

end Loc

def TieB : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (d : ℕ) [NeZero d], 5 ≤ l → 2 ≤ d → Even d →
    ∀ be : MvPowerSeries (ZMod d) ℂ_[l], product_zeroth_first_parts.B1 l d be → product_zeroth_first_parts.B2 l d be → product_zeroth_first_parts.B3 l d be → product_zeroth_first_parts.B4 l d be →
      ∃ (K0 : Subfield ℂ_[l]) (ζ : ℂ_[l]), Unram l K0 ∧ IsPrimitiveRoot ζ (l ^ d - 1) ∧ BHyp l d K0 ζ be

def KernelFromExponentialTwist : Prop :=
  ∀ (L : product_zeroth_first_parts.Loc) (ep : ℂ_[L.l]) (be : MvPowerSeries (ZMod L.d) ℂ_[L.l]), ‖ep‖ = 1 → L.B0 ep be →
    ∃ (g : ZV L.d L.N0 L.N1 → MvPowerSeries (ZV L.d L.N0 L.N1) ℂ_[L.l])
      (U : MvPowerSeries (ZV L.d L.N0 L.N1) ℂ_[L.l]) (ε : ℂ_[L.l]),
      (∀ y, MvPowerSeries.constantCoeff (g y) = 0) ∧
      (∀ y, MvPowerSeries.subst g (entLog (K := ℂ_[L.l]) L.l y) = MvPowerSeries.X y) ∧
      Integral U ∧ (ε = 1 ∨ ε = -1) ∧
      MvPowerSeries.subst (fun v : ZV L.d L.N0 L.N1 =>
        MvPowerSeries.C ep * (MvPowerSeries.X v : MvPowerSeries (ZV L.d L.N0 L.N1) ℂ_[L.l])) L.Th =
        thetaZ g U ε be

def TieFrame : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (d N0 N1 : ℕ) [NeZero d] (nu : ZMod d → YoungDiagram)
    (hp : ∀ s (c : Fin ((nu s).rowLen 0)), (nu s).colLen c ≤ N0)
    (Th : MvPowerSeries (ZMod d × Fin N0 × Fin N1) ℂ_[l]) (ep : ℂ_[l]) (B : ℝ), ‖ep‖ = 1 →
    (∀ (I : ∀ s (c : Fin ((nu s).rowLen 0)), Fin ((nu s).colLen c) → Fin N1)
      (n : (ZMod d × Fin N0 × Fin N0) →₀ ℕ),
      ‖MvPolynomial.coeff n (frameJet (fun s => (nu s).rowLen 0) (fun s c => (nu s).colLen c) hp I
        (MvPowerSeries.subst (fun v : ZMod d × Fin N0 × Fin N1 =>
          MvPowerSeries.C ep * (MvPowerSeries.X v : MvPowerSeries (ZMod d × Fin N0 × Fin N1) ℂ_[l])) Th))‖ ≤
        (l : ℝ) ^ (-B)) →
    product_zeroth_first_parts.KvalGe N0 N1 l nu Th B

/- English proof (translation)
Introduce `a ha`. Take `⟨hla, hsz, hN0⟩` from `ha`. Take `⟨ep, hep, be, h0, h1, h2, h3, h4⟩` from `hL`. Take `⟨K0, ζ, hK0, hζ, hBH⟩` from `hB L.l L.d L.J.five_le_l L.J.two_le_d L.J.d_even be h1 h2 h3 h4`. Take `⟨g, U, ε, hg0, hg, hU, hε, hTh⟩` from `hB0 L ep be hep h0`.

Establish `hp : ∀ s (c : Fin ((L.nu s).rowLen 0)), (L.nu s).colLen c ≤ L.N0` using `fun s c => (yd_colLen_le _ _).trans (L.nu_rows s)`. Establish `hl1 : (1 : ℝ) < L.l` using `by exact_mod_cast (Fact.out : Nat.Prime L.l).one_lt`. Establish `ha1 : (1 : ℝ) ≤ a` using `hl1.le.trans hla`. Establish `hfl : 1 ≤ ⌊a⌋₊` using `Nat.le_floor (by exact_mod_cast ha1)`. Establish `hsz' : ∀ s, (L.nu s).cells.card ≤ ⌊a⌋₊` using `fun s => Nat.le_floor (hsz s)`.

Establish `hlog : Real.logb L.l (⌊a⌋₊ : ℝ) ≤ Real.logb L.l a` using `Real.logb_le_logb_of_le hl1 (by exact_mod_cast hfl) (Nat.floor_le (by linarith))`. Establish `hN0' : 2 * Real.logb L.l (⌊a⌋₊ : ℝ) + 2 ≤ (L.N0 : ℝ) - 1` using `by linarith`. Establish `h3l : 3 ≤ L.l` using `(by norm_num : 3 ≤ 5).trans L.J.five_le_l`. Use `hF L.l L.d L.N0 L.N1 L.nu hp L.Th ep _ hep fun I n => ?_` and prove the remaining obligations. Rewrite using `[hTh]`.

Use `(thmAGauss L.l L.d L.N0 L.N1 h3l L.J.two_le_d L.J.d_even K0 hK0 ζ hζ be hBH g hg0 hg U hU ε hε L.TT (fun s => (L.nu s).rowLen 0) (fun s c => (L.nu s).colLen c) hp (fun s c => yd_one_le_colLen _ c) I (fun s => (L.nu s).rowLen 0) (fun s => (L.nu s).rowLen 1) (fun s => (L.nu s).cell …` and prove the remaining obligations. Rewrite using `[norm_l_rpow]`. Apply `Real.rpow_le_rpow_of_exponent_le hl1.le` to reduce the goal to its premises. Establish `e1 : ∀ s, L.topTerm s - product_zeroth_first_parts.gam L.l * (L.Wc s : ℝ) = topTerm L.l L.d L.TT (fun s => (L.nu s).rowLen 0) (fun s => (L.nu s).rowLen 1) s - gam L.l * (Wcap L.l L.d L.TT (fun s => (L.nu s).rowLen 0) (fun s => (L.nu s).rowLen 1) (fun s => (L.nu s).cells.card) s : …`. Introduce `s`.

Rewrite using `[topTerm_eq, Wc_eq]`. Both sides reduce to the same expression. Simplify using `only [e1, FD_eq]`. Establish `hd : 0 ≤ (L.d : ℝ) * L.N0 * L.N1` using `by positivity`. Use `mul_le_mul_of_nonneg_left hlog hd` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem thmA_of (hB : TieB) (hB0 : KernelFromExponentialTwist) (hF : TieFrame) (L : product_zeroth_first_parts.Loc) (hL : L.AdmB) : L.ThmA 1 := by
  intro a ha
  obtain ⟨hla, hsz, hN0⟩ := ha
  obtain ⟨ep, hep, be, h0, h1, h2, h3, h4⟩ := hL
  obtain ⟨K0, ζ, hK0, hζ, hBH⟩ := hB L.l L.d L.J.five_le_l L.J.two_le_d L.J.d_even be h1 h2 h3 h4
  obtain ⟨g, U, ε, hg0, hg, hU, hε, hTh⟩ := hB0 L ep be hep h0
  have hp : ∀ s (c : Fin ((L.nu s).rowLen 0)), (L.nu s).colLen c ≤ L.N0 :=
    fun s c => (yd_colLen_le _ _).trans (L.nu_rows s)
  have hl1 : (1 : ℝ) < L.l := by exact_mod_cast (Fact.out : Nat.Prime L.l).one_lt
  have ha1 : (1 : ℝ) ≤ a := hl1.le.trans hla
  have hfl : 1 ≤ ⌊a⌋₊ := Nat.le_floor (by exact_mod_cast ha1)
  have hsz' : ∀ s, (L.nu s).cells.card ≤ ⌊a⌋₊ := fun s => Nat.le_floor (hsz s)
  have hlog : Real.logb L.l (⌊a⌋₊ : ℝ) ≤ Real.logb L.l a :=
    Real.logb_le_logb_of_le hl1 (by exact_mod_cast hfl) (Nat.floor_le (by linarith))
  have hN0' : 2 * Real.logb L.l (⌊a⌋₊ : ℝ) + 2 ≤ (L.N0 : ℝ) - 1 := by linarith
  have h3l : 3 ≤ L.l := (by norm_num : 3 ≤ 5).trans L.J.five_le_l
  refine hF L.l L.d L.N0 L.N1 L.nu hp L.Th ep _ hep fun I n => ?_
  rw [hTh]
  refine (thmAGauss L.l L.d L.N0 L.N1 h3l L.J.two_le_d L.J.d_even K0 hK0 ζ hζ be hBH g hg0 hg U hU ε hε
    L.TT (fun s => (L.nu s).rowLen 0) (fun s c => (L.nu s).colLen c) hp (fun s c => yd_one_le_colLen _ c) I
    (fun s => (L.nu s).rowLen 0) (fun s => (L.nu s).rowLen 1) (fun s => (L.nu s).cells.card)
    (fun s => rfl) (fun s => (young_second_row_length_count _).symm) (fun s => yd_size _) ⌊a⌋₊ hfl hsz' hN0' n).trans ?_
  rw [norm_l_rpow]
  apply Real.rpow_le_rpow_of_exponent_le hl1.le
  have e1 : ∀ s, L.topTerm s - product_zeroth_first_parts.gam L.l * (L.Wc s : ℝ) =
      topTerm L.l L.d L.TT (fun s => (L.nu s).rowLen 0) (fun s => (L.nu s).rowLen 1) s -
        gam L.l * (Wcap L.l L.d L.TT (fun s => (L.nu s).rowLen 0) (fun s => (L.nu s).rowLen 1)
          (fun s => (L.nu s).cells.card) s : ℝ) := by
    intro s
    rw [topTerm_eq, Wc_eq]
    rfl
  simp only [e1, FD_eq]
  have hd : 0 ≤ (L.d : ℝ) * L.N0 * L.N1 := by positivity
  have := mul_le_mul_of_nonneg_left hlog hd
  linarith

def KernelFromTwistOneLetter : Prop :=
  ∀ (L : product_zeroth_first_parts.Loc1) (ep0 : ℂ_[L.l]) (be : MvPowerSeries (ZMod 2) ℂ_[L.l]), ‖ep0‖ = 1 → product_zeroth_first_parts.B3 L.l 2 be → L.B0 ep0 be →
    ∃ (g : Fin L.N0 × Fin L.N1 → MvPowerSeries (Fin L.N0 × Fin L.N1) ℂ_[L.l])
      (U : MvPowerSeries (Fin L.N0 × Fin L.N1) ℂ_[L.l]) (sgn ep : ℂ_[L.l]), ‖ep‖ = 1 ∧
      (∀ y, MvPowerSeries.constantCoeff (g y) = 0) ∧
      (∀ y, MvPowerSeries.subst g (oneLog (K := ℂ_[L.l]) L.l y) = MvPowerSeries.X y) ∧
      Integral U ∧ (sgn = 1 ∨ sgn = -1) ∧
      MvPowerSeries.subst (fun v : ZMod 1 × Fin L.N0 × Fin L.N1 =>
        MvPowerSeries.C ep0 * (MvPowerSeries.X v.2 : MvPowerSeries (Fin L.N0 × Fin L.N1) ℂ_[L.l])) L.Th =
        thetaOne g U sgn ep be

def TieFrameOne : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ) (nu : YoungDiagram)
    (hp : ∀ c : Fin (nu.rowLen 0), nu.colLen c ≤ N0)
    (Th : MvPowerSeries (ZMod 1 × Fin N0 × Fin N1) ℂ_[l]) (ep0 : ℂ_[l]) (B : ℝ), ‖ep0‖ = 1 →
    (∀ (I : ∀ c : Fin (nu.rowLen 0), Fin (nu.colLen c) → Fin N1) (n : (Fin N0 × Fin N0) →₀ ℕ),
      ‖MvPolynomial.coeff n (frameJetOne (fun c : Fin (nu.rowLen 0) => nu.colLen c) hp I
        (MvPowerSeries.subst (fun v : ZMod 1 × Fin N0 × Fin N1 =>
          MvPowerSeries.C ep0 * (MvPowerSeries.X v.2 : MvPowerSeries (Fin N0 × Fin N1) ℂ_[l])) Th))‖ ≤
        (l : ℝ) ^ (-B)) →
    product_zeroth_first_parts.KvalGe N0 N1 l (fun _ : ZMod 1 => nu) Th B

/- English proof (translation)
Introduce `a ha`. Take `⟨hla, hsz⟩` from `ha`. Take `⟨ep0, hep0, be, h0, h1, h2, h3, h4⟩` from `hL`. Take `⟨K0, ζ, hK0, hζ, hBH⟩` from `hB L.l 2 L.J.five_le_l le_rfl even_two be h1 h2 h3 h4`. Take `⟨g, U, sgn, ep, hep, hg0, hg, hU, hsg, hTh⟩` from `hB0 L ep0 be hep0 h3 h0`.

Establish `hp : ∀ c : Fin (L.nu.rowLen 0), L.nu.colLen c ≤ L.N0` using `fun c => (yd_colLen_le _ _).trans L.nu_rows`. Establish `hl1 : (1 : ℝ) < L.l` using `by exact_mod_cast (Fact.out : Nat.Prime L.l).one_lt`. Establish `ha1 : (1 : ℝ) ≤ a` using `hl1.le.trans hla`. Establish `hfl : 1 ≤ ⌊a⌋₊` using `Nat.le_floor (by exact_mod_cast ha1)`. Establish `hsum : (∑ c : Fin (L.nu.rowLen 0), L.nu.colLen c) = L.nu.cells.card` using `(yd_size _).symm`.

Establish `hsa : (∑ c : Fin (L.nu.rowLen 0), L.nu.colLen c) ≤ ⌊a⌋₊`. Rewrite using `[hsum]`. Conclude with `Nat.le_floor hsz`. Establish `hlog : Real.logb L.l (⌊a⌋₊ : ℝ) ≤ Real.logb L.l a` using `Real.logb_le_logb_of_le hl1 (by exact_mod_cast hfl) (Nat.floor_le (by linarith))`. Establish `h3l : 3 ≤ L.l` using `(by norm_num : 3 ≤ 5).trans L.J.five_le_l`.

Use `hF L.l L.N0 L.N1 L.nu hp L.Th ep0 _ hep0 fun I n => ?_` and prove the remaining obligations. Rewrite using `[hTh]`. Use `(oneLetterGauss L.l L.N0 L.N1 (L.nu.rowLen 0) h3l K0 hK0 ζ hζ be hBH ep hep g hg0 hg U hU sgn hsg (fun c => L.nu.colLen c) hp I ⌊a⌋₊ hfl hsa n).trans ?_` and prove the remaining obligations. Rewrite using `[norm_l_rpow]`. Apply `Real.rpow_le_rpow_of_exponent_le hl1.le` to reduce the goal to its premises.

Rewrite using `[hsum]`. Express the relevant statement in the definitionally equal form `-(product_zeroth_first_parts.rho L.l * _ - _) ≤ -(product_zeroth_first_parts.rho L.l * _ - _)`. Establish `hd : 0 ≤ (L.N0 : ℝ) * L.N1` using `by positivity`. Use `mul_le_mul_of_nonneg_left hlog hd` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem thmOne_of (hB : TieB) (hB0 : KernelFromTwistOneLetter) (hF : TieFrameOne) (L : product_zeroth_first_parts.Loc1) (hL : L.AdmB) : L.ThmOne 1 := by
  intro a ha
  obtain ⟨hla, hsz⟩ := ha
  obtain ⟨ep0, hep0, be, h0, h1, h2, h3, h4⟩ := hL
  obtain ⟨K0, ζ, hK0, hζ, hBH⟩ := hB L.l 2 L.J.five_le_l le_rfl even_two be h1 h2 h3 h4
  obtain ⟨g, U, sgn, ep, hep, hg0, hg, hU, hsg, hTh⟩ := hB0 L ep0 be hep0 h3 h0
  have hp : ∀ c : Fin (L.nu.rowLen 0), L.nu.colLen c ≤ L.N0 := fun c => (yd_colLen_le _ _).trans L.nu_rows
  have hl1 : (1 : ℝ) < L.l := by exact_mod_cast (Fact.out : Nat.Prime L.l).one_lt
  have ha1 : (1 : ℝ) ≤ a := hl1.le.trans hla
  have hfl : 1 ≤ ⌊a⌋₊ := Nat.le_floor (by exact_mod_cast ha1)
  have hsum : (∑ c : Fin (L.nu.rowLen 0), L.nu.colLen c) = L.nu.cells.card := (yd_size _).symm
  have hsa : (∑ c : Fin (L.nu.rowLen 0), L.nu.colLen c) ≤ ⌊a⌋₊ := by
    rw [hsum]
    exact Nat.le_floor hsz
  have hlog : Real.logb L.l (⌊a⌋₊ : ℝ) ≤ Real.logb L.l a :=
    Real.logb_le_logb_of_le hl1 (by exact_mod_cast hfl) (Nat.floor_le (by linarith))
  have h3l : 3 ≤ L.l := (by norm_num : 3 ≤ 5).trans L.J.five_le_l
  refine hF L.l L.N0 L.N1 L.nu hp L.Th ep0 _ hep0 fun I n => ?_
  rw [hTh]
  refine (oneLetterGauss L.l L.N0 L.N1 (L.nu.rowLen 0) h3l K0 hK0 ζ hζ be hBH ep hep g hg0 hg U hU sgn hsg
    (fun c => L.nu.colLen c) hp I ⌊a⌋₊ hfl hsa n).trans ?_
  rw [norm_l_rpow]
  apply Real.rpow_le_rpow_of_exponent_le hl1.le
  rw [hsum]
  change -(product_zeroth_first_parts.rho L.l * _ - _) ≤ -(product_zeroth_first_parts.rho L.l * _ - _)
  have hd : 0 ≤ (L.N0 : ℝ) * L.N1 := by positivity
  have := mul_le_mul_of_nonneg_left hlog hd
  linarith

/- English proof (translation)
Unfold `product_zeroth_first_parts.KvalGe at h ⊢`. Introduce `I m`. Use `(h I m).trans ?_` and prove the remaining obligations. Apply `Real.rpow_le_rpow_of_exponent_le` to reduce the goal to its premises. Conclude with `(Fact.out : Nat.Prime l).one_lt.le` after adjusting the coercions.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem kval_mono {N0 N1 l : ℕ} [Fact l.Prime] {Lt : Type} [Fintype Lt] [DecidableEq Lt] {nu : Lt → YoungDiagram}
    {Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]} {B B' : ℝ} (h : product_zeroth_first_parts.KvalGe N0 N1 l nu Th B) (hB : B' ≤ B) :
    product_zeroth_first_parts.KvalGe N0 N1 l nu Th B' := by
  unfold product_zeroth_first_parts.KvalGe at h ⊢
  intro I m
  refine (h I m).trans ?_
  apply Real.rpow_le_rpow_of_exponent_le
  · exact_mod_cast (Fact.out : Nat.Prime l).one_lt.le
  · linarith

/- English proof (translation)
Unfold `product_zeroth_first_parts.Loc.baseTerm product_zeroth_first_parts.Loc.topTerm product_zeroth_first_parts.Loc.A`. Establish `hl : (1 : ℝ) < L.l` using `by exact_mod_cast (Fact.out : Nat.Prime L.l).one_lt`. Establish `hpos : ∀ e : ℕ, (0 : ℝ) < (L.l : ℝ) ^ e` using `fun e => pow_pos (by linarith) e`. Establish `hc : ∀ x : ZMod L.d, (0 : ℝ) ≤ (L.cap x : ℝ)` using `fun x => Nat.cast_nonneg _`. Establish `hB : (0 : ℝ) ≤ ((L.nu s).rowLen 1 : ℝ)` using `Nat.cast_nonneg _`.

Establish `hA0 : (0 : ℝ) ≤ ((L.nu s).rowLen 0 : ℝ)` using `Nat.cast_nonneg _`. Establish `hq : ∀ e : ℕ, 0 ≤ ((L.nu s).rowLen 0 : ℝ) / (L.l : ℝ) ^ e` using `fun e => div_nonneg hA0 (hpos e).le`. Establish `hsub : ∀ e : ℕ, (((L.nu s).rowLen 0 : ℝ) - ((L.nu s).rowLen 1 : ℝ)) / (L.l : ℝ) ^ e ≤ ((L.nu s).rowLen 0 : ℝ) / (L.l : ℝ) ^ e` using `fun e => by`. Rewrite using `[div_eq_mul_inv, div_eq_mul_inv]`. Conclude with `mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.2 (hpos e).le)`.

Establish `hdiv : ∀ e : ℕ, ((L.nu s).rowLen 0 : ℝ) / (L.l : ℝ) ^ e = ((L.nu s).rowLen 0 : ℝ) * (1 / (L.l : ℝ)) ^ e` using `fun e => by`. Rewrite using `[one_div, inv_pow, div_eq_mul_inv]`. Establish `hgeo : Summable (fun e : ℕ => ((L.nu s).rowLen 0 : ℝ) * (1 / (L.l : ℝ)) ^ e)` using `(summable_geometric_of_lt_one (by positivity) ((div_lt_one (by linarith)).2 hl)).mul_left _`. Use `Summable.tsum_le_tsum (fun e => ?_) (Summable.of_nonneg_of_le (fun e => ?_) (fun e => ?_) hgeo) (Summable.of_nonneg_of_le (fun e => ?_) (fun e => ?_) hgeo)` and prove the remaining obligations. Distinguish the cases in `h1 : Odd e ∧ (e : ℕ∞) ≠ L.dTop s`.

Rewrite using `[if_pos h1]`. Distinguish the cases in `h2 : Odd e ∧ (e : ℕ∞) < L.dTop s`. Rewrite using `[if_pos h2]`. Conclude with `max_le_max (sub_le_sub_right (hsub e) _) le_rfl`. Rewrite using `[if_neg h2]`.

Distinguish the cases in `h3 : Odd e ∧ L.dTop s < (e : ℕ∞)`. Rewrite using `[if_pos h3]`. Use `hc (s + (e : ZMod L.d))` as an intermediate fact. Use `hsub e` as an intermediate fact. Conclude with `max_le (by linarith) (hq e)`.

It suffices to derive a contradiction. Break down `lt_trichotomy (e : ℕ∞) (L.dTop s) with h | h | h` into its components or cases. Conclude with `h2 ⟨h1.1, h⟩`. Conclude with `h1.2 h`. Conclude with `h3 ⟨h1.1, h⟩`.

Rewrite using `[if_neg h1] split_ifs`. Conclude with `le_max_right _ _`. Conclude with `hq e`. Conclude with `le_rfl`. Use `split_ifs`.

Conclude with `le_max_right _ _`. Conclude with `le_rfl`. Rewrite using `[← hdiv] split_ifs`. Use `hc (s + (e : ZMod L.d))` as an intermediate fact. Use `hsub e` as an intermediate fact.

Conclude with `max_le (by linarith) (hq e)`. Conclude with `hq e`. Use `split_ifs`. Conclude with `le_max_right _ _`. Conclude with `hq e`.

Conclude with `le_rfl`. Rewrite using `[← hdiv] split_ifs`. Use `hc (s + (e : ZMod L.d))` as an intermediate fact. Conclude with `max_le (by linarith) (hq e)`. Conclude with `le_rfl`.

Conclude with `hq e`.
-/
theorem base_term_le_top_term (L : product_zeroth_first_parts.Loc) (s : ZMod L.d) : L.baseTerm s ≤ L.topTerm s := by
  unfold product_zeroth_first_parts.Loc.baseTerm product_zeroth_first_parts.Loc.topTerm product_zeroth_first_parts.Loc.A
  have hl : (1 : ℝ) < L.l := by exact_mod_cast (Fact.out : Nat.Prime L.l).one_lt
  have hpos : ∀ e : ℕ, (0 : ℝ) < (L.l : ℝ) ^ e := fun e => pow_pos (by linarith) e
  have hc : ∀ x : ZMod L.d, (0 : ℝ) ≤ (L.cap x : ℝ) := fun x => Nat.cast_nonneg _
  have hB : (0 : ℝ) ≤ ((L.nu s).rowLen 1 : ℝ) := Nat.cast_nonneg _
  have hA0 : (0 : ℝ) ≤ ((L.nu s).rowLen 0 : ℝ) := Nat.cast_nonneg _
  have hq : ∀ e : ℕ, 0 ≤ ((L.nu s).rowLen 0 : ℝ) / (L.l : ℝ) ^ e := fun e => div_nonneg hA0 (hpos e).le
  have hsub : ∀ e : ℕ, (((L.nu s).rowLen 0 : ℝ) - ((L.nu s).rowLen 1 : ℝ)) / (L.l : ℝ) ^ e ≤
      ((L.nu s).rowLen 0 : ℝ) / (L.l : ℝ) ^ e := fun e => by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.2 (hpos e).le)
  have hdiv : ∀ e : ℕ, ((L.nu s).rowLen 0 : ℝ) / (L.l : ℝ) ^ e =
      ((L.nu s).rowLen 0 : ℝ) * (1 / (L.l : ℝ)) ^ e := fun e => by
    rw [one_div, inv_pow, div_eq_mul_inv]
  have hgeo : Summable (fun e : ℕ => ((L.nu s).rowLen 0 : ℝ) * (1 / (L.l : ℝ)) ^ e) :=
    (summable_geometric_of_lt_one (by positivity) ((div_lt_one (by linarith)).2 hl)).mul_left _
  refine Summable.tsum_le_tsum (fun e => ?_) (Summable.of_nonneg_of_le (fun e => ?_) (fun e => ?_) hgeo)
    (Summable.of_nonneg_of_le (fun e => ?_) (fun e => ?_) hgeo)
  · by_cases h1 : Odd e ∧ (e : ℕ∞) ≠ L.dTop s
    · rw [if_pos h1]
      by_cases h2 : Odd e ∧ (e : ℕ∞) < L.dTop s
      · rw [if_pos h2]
        exact max_le_max (sub_le_sub_right (hsub e) _) le_rfl
      · rw [if_neg h2]
        by_cases h3 : Odd e ∧ L.dTop s < (e : ℕ∞)
        · rw [if_pos h3]
          have := hc (s + (e : ZMod L.d))
          have := hsub e
          exact max_le (by linarith) (hq e)
        · exfalso
          rcases lt_trichotomy (e : ℕ∞) (L.dTop s) with h | h | h
          · exact h2 ⟨h1.1, h⟩
          · exact h1.2 h
          · exact h3 ⟨h1.1, h⟩
    · rw [if_neg h1]
      split_ifs
      · exact le_max_right _ _
      · exact hq e
      · exact le_rfl
  · split_ifs
    · exact le_max_right _ _
    · exact le_rfl
  · rw [← hdiv]
    split_ifs
    · have := hc (s + (e : ZMod L.d))
      have := hsub e
      exact max_le (by linarith) (hq e)
    · exact hq e
  · split_ifs
    · exact le_max_right _ _
    · exact hq e
    · exact le_rfl
  · rw [← hdiv]
    split_ifs
    · have := hc (s + (e : ZMod L.d))
      exact max_le (by linarith) (hq e)
    · exact le_rfl
    · exact hq e

/- English proof (translation)
Simplify using `[topTerm, capL]`.
-/
theorem top0 (l d : ℕ) [NeZero d] (TT : Finset (ZMod d)) (s : ZMod d) :
    topTerm l d TT (fun _ => 0) (fun _ => 0) s = 0 := by
  simp [topTerm, capL]

end Formalism.MainNotions.DIV.Bridge.DworkPowerSeriesWeights
