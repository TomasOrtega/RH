import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FactorBounds
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeightedNormSquareRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OrthogonalNormSquareSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightsInterlaceSameShift
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows

namespace GlobalTheory.ColRows.LastSideProof

def ext {N : ℕ} (lam : DomWeight N) (i : ℕ) : ℤ := if h : i < N then lam.w ⟨i, h⟩ else 0

/- English proof (translation)
Simplify using `[ext, i.2]`.
-/
theorem ext_of {N : ℕ} (lam : DomWeight N) (i : Fin N) : ext lam i = lam.w i := by
  simp [ext, i.2]

/- English proof (translation)
Rewrite using `[Br.d0, ← Fin.sum_univ_eq_sum_range (fun i => ext sg i - ext lam (i + 1))]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Br.aBr, ← ext_of sg i, ← ext_of lam]`. Both sides reduce to the same expression.
-/
theorem first_difference_eq_range_sum {N n : ℕ} (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n) :
    Br.d0 hN lam sg = ∑ i ∈ Finset.range n, (ext sg i - ext lam (i + 1)) := by
  rw [Br.d0, ← Fin.sum_univ_eq_sum_range (fun i => ext sg i - ext lam (i + 1))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Br.aBr, ← ext_of sg i, ← ext_of lam]
  rfl

/- English proof (translation)
Substitute `hN` using the available equality. Establish `h : ∀ i : Fin n, lam.w (Br.iS rfl i) = lam.w i.succ` using `fun i => rfl`. Simplify using `only [Br.nBr, Br.d0, Br.aBr, h, Finset.sum_sub_distrib, Fin.sum_univ_succ]`. Establish `h0 : lam.w 0 = lam.w ⟨0, by omega⟩` using `rfl`. Rewrite using `[h0]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem nBr_eq_sub {N n : ℕ} (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n) :
    Br.nBr lam sg = lam.w ⟨0, by omega⟩ - Br.d0 hN lam sg := by
  subst hN
  have h : ∀ i : Fin n, lam.w (Br.iS rfl i) = lam.w i.succ := fun i => rfl
  simp only [Br.nBr, Br.d0, Br.aBr, h, Finset.sum_sub_distrib, Fin.sum_univ_succ]
  have h0 : lam.w 0 = lam.w ⟨0, by omega⟩ := rfl
  rw [h0]
  ring

/- English proof (translation)
Introduce `p hp1 hpn`. Proceed by induction on `p with`. Consider the case `zero => omega`. Consider the case `succ p ih`. Break down `Nat.eq_zero_or_pos p with rfl | hp` into its components or cases.

Simplify using the standard rewrite rules. Rewrite using `[Finset.sum_range_succ]`. Establish `h1` using `ih hp (by omega)`. Establish `h2` using `(hI ⟨p, by omega⟩).2`. Rewrite `h2` using `[Br.bBr, ← ext_of sg, ← ext_of lam]`.

Establish `e : ((Br.iC hN ⟨p, by omega⟩ : Fin N) : ℕ) = p` using `rfl`. Rewrite `h2` using `[e]`. Simplify using `only at h2`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem first_difference_head_le {N n : ℕ} (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n) (hI : Br.Interlace hN lam sg) :
    ∀ p, 1 ≤ p → p ≤ n → ∑ i ∈ Finset.range p, (ext sg i - ext lam (i + 1)) ≤ ext sg 0 - ext lam p := by
  intro p hp1 hpn
  induction p with
  | zero => omega
  | succ p ih =>
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · simp
    · rw [Finset.sum_range_succ]
      have h1 := ih hp (by omega)
      have h2 := (hI ⟨p, by omega⟩).2
      rw [Br.bBr, ← ext_of sg, ← ext_of lam] at h2
      have e : ((Br.iC hN ⟨p, by omega⟩ : Fin N) : ℕ) = p := rfl
      rw [e] at h2
      simp only at h2
      linarith

/- English proof (translation)
Use `set D := Br.d0 hN lam sg`. Establish `e1 : GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne hN lam sg = ∑ i ∈ Finset.range n, min (ext lam i - ext lam (i + 1)) D`. Rewrite using `[GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne, ← Fin.sum_univ_eq_sum_range (fun i => min (ext lam i - ext lam (i + 1)) D)]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← ext_of lam, ← ext_of lam]`.

Both sides reduce to the same expression. Rewrite using `[e1]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun i _ => ?_` and prove the remaining obligations. Use `split_ifs`.

Use `min_le_right (ext lam i - ext lam (i + 1)) D` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `min_le_left (ext lam i - ext lam (i + 1)) D` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `_ = (ext lam 0 - ext lam n) + ((D - (ext lam 0 - ext lam (0 + 1))) + (D - (ext lam p - ext lam (p + 1)))) := by`.

Rewrite using `[Finset.sum_add_distrib, Finset.sum_range_sub' (fun i => ext lam i)]`. Use `congr 1`. Rewrite using `[Finset.sum_eq_add (f := fun i => if i = 0 ∨ i = p then D - (ext lam i - ext lam (i + 1)) else 0) 0 p (by omega : 0 ≠ p)]`. Simplify using `[hp0.ne']`. Introduce `c _ hc`.

Simplify using `[hc.1, hc.2]`. Introduce `h; exact absurd (Finset.mem_range.2 (by omega)) h`. Introduce `h`. Conclude with `absurd (Finset.mem_range.2 hpn) h`. Use `_ = 2 * D + (ext lam 1 - ext lam p) + (ext lam (p + 1) - ext lam n) := by ring`.
-/
theorem dOne_le {N n : ℕ} (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n) (p : ℕ) (hp0 : 0 < p) (hpn : p < n) :
    GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne hN lam sg ≤ 2 * Br.d0 hN lam sg + (ext lam 1 - ext lam p) + (ext lam (p + 1) - ext lam n) := by
  set D := Br.d0 hN lam sg
  have e1 : GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne hN lam sg = ∑ i ∈ Finset.range n, min (ext lam i - ext lam (i + 1)) D := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne, ← Fin.sum_univ_eq_sum_range (fun i => min (ext lam i - ext lam (i + 1)) D)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← ext_of lam, ← ext_of lam]
    rfl
  rw [e1]
  calc ∑ i ∈ Finset.range n, min (ext lam i - ext lam (i + 1)) D
      ≤ ∑ i ∈ Finset.range n, ((ext lam i - ext lam (i + 1)) +
          (if i = 0 ∨ i = p then D - (ext lam i - ext lam (i + 1)) else 0)) := by
        refine Finset.sum_le_sum fun i _ => ?_
        split_ifs
        · have := min_le_right (ext lam i - ext lam (i + 1)) D; linarith
        · have := min_le_left (ext lam i - ext lam (i + 1)) D; linarith
    _ = (ext lam 0 - ext lam n) + ((D - (ext lam 0 - ext lam (0 + 1))) + (D - (ext lam p - ext lam (p + 1)))) := by
        rw [Finset.sum_add_distrib, Finset.sum_range_sub' (fun i => ext lam i)]
        congr 1
        rw [Finset.sum_eq_add (f := fun i => if i = 0 ∨ i = p then D - (ext lam i - ext lam (i + 1)) else 0)
          0 p (by omega : 0 ≠ p)]
        · simp [hp0.ne']
        · intro c _ hc; simp [hc.1, hc.2]
        · intro h; exact absurd (Finset.mem_range.2 (by omega)) h
        · intro h; exact absurd (Finset.mem_range.2 hpn) h
    _ = 2 * D + (ext lam 1 - ext lam p) + (ext lam (p + 1) - ext lam n) := by ring

end GlobalTheory.ColRows.LastSideProof

namespace GlobalTheory.ColRows.LastSideProof

/- English proof (translation)
The claim follows from `| 0 => by simp | m + 1 => by rw [Nat.succ_mul, Finset.sum_range_add, sum_range_mul f c m, Finset.sum_range_succ]`.
-/
theorem sum_range_mul (f : ℕ → ℚ) (c : ℕ) : ∀ m : ℕ,
    ∑ x ∈ Finset.range (m * c), f x = ∑ B ∈ Finset.range m, ∑ ρ ∈ Finset.range c, f (B * c + ρ)
  | 0 => by simp
  | m + 1 => by
    rw [Nat.succ_mul, Finset.sum_range_add, sum_range_mul f c m, Finset.sum_range_succ]

section Place

variable {X : Fields} {Word : Type} {R : Ranks} (W : Wts X Word R) (u : Word) (τ : X.Tau)

/- English proof (translation)
Establish `hiN : i < R.N R.m` using `by unfold Ranks.N; omega`. Rewrite using `[ext, dif_pos hiN]`. Conclude with `GlobalTheory.BranchMembers.lamTrue_lo W u τ ⟨i, hiN⟩ ⟨i, hi⟩ rfl`.
-/
theorem ext_lam_lo (i : ℕ) (hi : i < R.k) :
    (ext (W.lamTrue u R.m τ) i : ℚ) =
      (W.hc u τ).u ⟨i, hi⟩ - ((R.k : ℚ) - 1) / 2 + (i : ℚ) - (R.m : ℚ) * (((R.t : ℚ) + 1) / 2) := by
  have hiN : i < R.N R.m := by unfold Ranks.N; omega
  rw [ext, dif_pos hiN]
  exact GlobalTheory.BranchMembers.lamTrue_lo W u τ ⟨i, hiN⟩ ⟨i, hi⟩ rfl

/- English proof (translation)
Establish `h1 : (B + 1) * (R.t + 1) ≤ R.m * (R.t + 1)` using `Nat.mul_le_mul_right _ hB`. Establish `hiN : R.k + B * (R.t + 1) + ρ < R.N R.m`. Unfold `Ranks.N`. Rewrite `h1` using `[Nat.succ_mul]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[ext, dif_pos hiN]`. Conclude with `GlobalTheory.BranchMembers.lamTrue_hi W u τ ⟨_, hiN⟩ B ρ hρ rfl`.
-/
theorem ext_lam_hi (B ρ : ℕ) (hB : B < R.m) (hρ : ρ < R.t + 1) :
    (ext (W.lamTrue u R.m τ) (R.k + B * (R.t + 1) + ρ) : ℚ) =
      -(RowPar.of (W.hc u τ)).eAt B + (R.k : ℚ) / 2 + (2 * (B : ℚ) + 1) * (((R.t : ℚ) + 1) / 2) -
        (R.m : ℚ) * (((R.t : ℚ) + 1) / 2) := by
  have h1 : (B + 1) * (R.t + 1) ≤ R.m * (R.t + 1) := Nat.mul_le_mul_right _ hB
  have hiN : R.k + B * (R.t + 1) + ρ < R.N R.m := by
    unfold Ranks.N; rw [Nat.succ_mul] at h1; omega
  rw [ext, dif_pos hiN]
  exact GlobalTheory.BranchMembers.lamTrue_hi W u τ ⟨_, hiN⟩ B ρ hρ rfl

/- English proof (translation)
Rewrite using `[ext, dif_pos hi]`. Apply the tactic sequence `exact GlobalTheory.BranchMembers.sgTrue_entry W hW u τ ⟨i, hi⟩`.
-/
theorem ext_sg (hW : W.Ok) (i : ℕ) (hi : i < R.N R.m - 1) :
    (ext (W.sgTrue τ) i : ℚ) =
      (RowPar.of (W.hc u τ)).sgHC i - RowPar.sh R - ((R.k : ℚ) - 2) / 2 - (R.m : ℚ) * (((R.t : ℚ) + 1) / 2) + (i : ℚ) := by
  rw [ext, dif_pos hi]
  exact GlobalTheory.BranchMembers.sgTrue_entry W hW u τ ⟨i, hi⟩

end Place

end GlobalTheory.ColRows.LastSideProof

namespace GlobalTheory.ColRows.LastSideProof

section Place2

variable {X : Fields} {Word : Type} {R : Ranks} (W : Wts X Word R) (hW : W.Ok) (u : Word) (τ : X.Tau)
include hW

/- English proof (translation)
Establish `hk` using `R.m_add_three_le_k`. Establish `h1 : (B + 1) * (R.t + 1) ≤ R.m * (R.t + 1)` using `Nat.mul_le_mul_right _ hB`. Rewrite `h1` using `[Nat.succ_mul]`. Establish `hn : ∀ ρ, ρ < R.t + 1 → R.k - 1 + (B * (R.t + 1) + ρ) < R.N R.m - 1`. Introduce `ρ hρ`.

Unfold `Ranks.N`. Use linear arithmetic over natural numbers and integers. Establish `ck : ((R.k - 1 : ℕ) : ℚ) = (R.k : ℚ) - 1` using `by rw [Nat.cast_sub (by omega)]; simp`. Rewrite using `[Finset.sum_range_succ']`. Establish `e0 : R.k - 1 + (B * (R.t + 1) + 0) = R.k - 1 + B * (R.t + 1)` using `by omega`.

Establish `e0' : R.k - 1 + (B * (R.t + 1) + 0) + 1 = R.k + B * (R.t + 1) + 0` using `by omega`. Establish `z0` using `ext_sg W u τ hW _ (hn 0 (by omega))`. Rewrite `z0` using `[e0, RowPar.sgHC_b]`. Establish `l0` using `ext_lam_hi W u τ B 0 hB (by omega)`. Establish `hzero : ∀ ρ ∈ Finset.range R.t, ((ext (W.sgTrue τ) (R.k - 1 + (B * (R.t + 1) + (ρ + 1))) -`.

Use extensionality with `(W.lamTrue u R.m τ) (R.k - 1 + (B * (R.t + 1) + (ρ + 1)) + 1) : ℤ) : ℚ) = 0 := by`. Introduce `ρ hρ`. Rewrite `hρ` using `[Finset.mem_range]`. Establish `e1 : R.k - 1 + (B * (R.t + 1) + (ρ + 1)) = R.k - 1 + B * (R.t + 1) + (ρ + 1)` using `by omega`. Establish `e1' : R.k - 1 + (B * (R.t + 1) + (ρ + 1)) + 1 = R.k + B * (R.t + 1) + (ρ + 1)` using `by omega`.

Establish `z1` using `ext_sg W u τ hW _ (hn (ρ + 1) (by omega))`. Rewrite `z1` using `[e1, RowPar.sgHC_e _ B (ρ + 1) (by omega) (by omega)]`. Establish `l1` using `ext_lam_hi W u τ B (ρ + 1) hB (by omega)`. Rewrite using `[e1', e1]`. Use `push_cast`.

Rewrite using `[z1, l1]`. Move the coercions through the operations in `[ck]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Finset.sum_eq_zero hzero, zero_add]`. Rewrite using `[e0', e0]`.

Use `push_cast`. Rewrite using `[z0, l0]`. Move the coercions through the operations in `[ck]`. Unfold `RowPar.sh`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem block_sum (B : ℕ) (hB : B < R.m) :
    ∑ ρ ∈ Finset.range (R.t + 1),
        ((ext (W.sgTrue τ) (R.k - 1 + (B * (R.t + 1) + ρ)) - ext (W.lamTrue u R.m τ) (R.k - 1 + (B * (R.t + 1) + ρ) + 1) : ℤ) : ℚ) =
      (RowPar.of (W.hc u τ)).eAt B - (RowPar.of (W.hc u τ)).bAt B - ((R.t : ℚ) + 1) / 2 := by
  have hk := R.m_add_three_le_k
  have h1 : (B + 1) * (R.t + 1) ≤ R.m * (R.t + 1) := Nat.mul_le_mul_right _ hB
  rw [Nat.succ_mul] at h1
  have hn : ∀ ρ, ρ < R.t + 1 → R.k - 1 + (B * (R.t + 1) + ρ) < R.N R.m - 1 := by
    intro ρ hρ; unfold Ranks.N; omega
  have ck : ((R.k - 1 : ℕ) : ℚ) = (R.k : ℚ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  rw [Finset.sum_range_succ']
  have e0 : R.k - 1 + (B * (R.t + 1) + 0) = R.k - 1 + B * (R.t + 1) := by omega
  have e0' : R.k - 1 + (B * (R.t + 1) + 0) + 1 = R.k + B * (R.t + 1) + 0 := by omega
  have z0 := ext_sg W u τ hW _ (hn 0 (by omega))
  rw [e0, RowPar.sgHC_b] at z0
  have l0 := ext_lam_hi W u τ B 0 hB (by omega)
  have hzero : ∀ ρ ∈ Finset.range R.t,
      ((ext (W.sgTrue τ) (R.k - 1 + (B * (R.t + 1) + (ρ + 1))) -
        ext (W.lamTrue u R.m τ) (R.k - 1 + (B * (R.t + 1) + (ρ + 1)) + 1) : ℤ) : ℚ) = 0 := by
    intro ρ hρ
    rw [Finset.mem_range] at hρ
    have e1 : R.k - 1 + (B * (R.t + 1) + (ρ + 1)) = R.k - 1 + B * (R.t + 1) + (ρ + 1) := by omega
    have e1' : R.k - 1 + (B * (R.t + 1) + (ρ + 1)) + 1 = R.k + B * (R.t + 1) + (ρ + 1) := by omega
    have z1 := ext_sg W u τ hW _ (hn (ρ + 1) (by omega))
    rw [e1, RowPar.sgHC_e _ B (ρ + 1) (by omega) (by omega)] at z1
    have l1 := ext_lam_hi W u τ B (ρ + 1) hB (by omega)
    rw [e1', e1]
    push_cast
    rw [z1, l1]
    push_cast [ck]
    ring
  rw [Finset.sum_eq_zero hzero, zero_add]
  rw [e0', e0]
  push_cast
  rw [z0, l0]
  push_cast [ck]
  unfold RowPar.sh
  ring

/- English proof (translation)
Establish `hk` using `R.m_add_three_le_k`. Establish `hI` using `GlobalTheory.BranchMembers.interlace W hW u τ`. Establish `hn : R.N R.m - 1 = (R.k - 1) + R.m * (R.t + 1)` using `by unfold Ranks.N; omega`. Establish `hhead` using `first_difference_head_le (N_m_succ R) _ _ hI (R.k - 1) (by omega) (by omega)`. Establish `hsplit : ∀ f : ℕ → ℤ, ∑ i ∈ Finset.range (R.N R.m - 1), f i = ∑ i ∈ Finset.range (R.k - 1), f i + ∑ x ∈ Finset.range (R.m * (R.t + 1)), f (R.k - 1 + x)` using `fun f => by`.

Rewrite using `[hn, Finset.sum_range_add]`. Rewrite using `[first_difference_eq_range_sum, hsplit]`. Use `push_cast`. Establish `hhead' : (∑ i ∈ Finset.range (R.k - 1), ((ext (W.sgTrue τ) i : ℚ) - (ext (W.lamTrue u R.m τ) (i + 1) : ℚ))) ≤ (ext (W.sgTrue τ) 0 : ℚ) - (ext (W.lamTrue u R.m τ) (R.k - 1) : ℚ)` using `by exact_mod_cast hhead`. Establish `htail : ∑ x ∈ Finset.range (R.m * (R.t + 1)), ((ext (W.sgTrue τ) (R.k - 1 + x) : ℚ) - (ext (W.lamTrue u R.m τ) (R.k - 1 + x + 1) : ℚ)) = ∑ B ∈ Finset.range R.m, ((RowPar.of (W.hc u τ)).eAt B - (RowPar.of (W.hc u τ)).bAt B - ((R.t : ℚ) + 1) / 2)`.

Rewrite using `[sum_range_mul (fun x => (ext (W.sgTrue τ) (R.k - 1 + x) : ℚ) - (ext (W.lamTrue u R.m τ) (R.k - 1 + x + 1) : ℚ))]`. Use `Finset.sum_congr rfl fun B hB => ?_` and prove the remaining obligations. Rewrite using `[← block_sum W hW u τ B (Finset.mem_range.1 hB)]`. Use `push_cast`. Both sides reduce to the same expression.

Rewrite using `[htail]`. Establish `s0` using `ext_sg W u τ hW 0 (by unfold Ranks.N; omega)`. Rewrite `s0` using `[RowPar.sgHC_lo _ (by omega), RowPar.vb_lo _ (by omega)]`. Establish `l1` using `ext_lam_lo W u τ (R.k - 1) (by omega)`. Establish `ck : ((R.k - 1 : ℕ) : ℚ) = (R.k : ℚ) - 1` using `by rw [Nat.cast_sub (by omega)]; simp`.

Rewrite `hhead'` using `[s0, l1, ck]`. Unfold `RowPar.sh at hhead'`. Move the coercions through the operations in `at hhead'`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem bottomRank_sum_le_two_mul_totalRank :
    ((Br.d0 (N_m_succ R) (W.lamTrue u R.m τ) (W.sgTrue τ) : ℤ) : ℚ) ≤
      (W.hc u τ).v ⟨0, by have := R.m_add_three_le_k; omega⟩ - (W.hc u τ).u ⟨R.k - 1, by have := R.m_add_three_le_k; omega⟩ -
        (R.k : ℚ) + 3 / 2 +
        ∑ B ∈ Finset.range R.m, ((RowPar.of (W.hc u τ)).eAt B - (RowPar.of (W.hc u τ)).bAt B - ((R.t : ℚ) + 1) / 2) := by
  have hk := R.m_add_three_le_k
  have hI := GlobalTheory.BranchMembers.interlace W hW u τ
  have hn : R.N R.m - 1 = (R.k - 1) + R.m * (R.t + 1) := by unfold Ranks.N; omega
  have hhead := first_difference_head_le (N_m_succ R) _ _ hI (R.k - 1) (by omega) (by omega)
  have hsplit : ∀ f : ℕ → ℤ, ∑ i ∈ Finset.range (R.N R.m - 1), f i =
      ∑ i ∈ Finset.range (R.k - 1), f i + ∑ x ∈ Finset.range (R.m * (R.t + 1)), f (R.k - 1 + x) := fun f => by
    rw [hn, Finset.sum_range_add]
  rw [first_difference_eq_range_sum, hsplit]
  push_cast
  have hhead' : (∑ i ∈ Finset.range (R.k - 1), ((ext (W.sgTrue τ) i : ℚ) - (ext (W.lamTrue u R.m τ) (i + 1) : ℚ))) ≤
      (ext (W.sgTrue τ) 0 : ℚ) - (ext (W.lamTrue u R.m τ) (R.k - 1) : ℚ) := by exact_mod_cast hhead
  have htail : ∑ x ∈ Finset.range (R.m * (R.t + 1)),
      ((ext (W.sgTrue τ) (R.k - 1 + x) : ℚ) - (ext (W.lamTrue u R.m τ) (R.k - 1 + x + 1) : ℚ)) =
      ∑ B ∈ Finset.range R.m, ((RowPar.of (W.hc u τ)).eAt B - (RowPar.of (W.hc u τ)).bAt B - ((R.t : ℚ) + 1) / 2) := by
    rw [sum_range_mul (fun x => (ext (W.sgTrue τ) (R.k - 1 + x) : ℚ) - (ext (W.lamTrue u R.m τ) (R.k - 1 + x + 1) : ℚ))]
    refine Finset.sum_congr rfl fun B hB => ?_
    rw [← block_sum W hW u τ B (Finset.mem_range.1 hB)]
    push_cast
    rfl
  rw [htail]
  have s0 := ext_sg W u τ hW 0 (by unfold Ranks.N; omega)
  rw [RowPar.sgHC_lo _ (by omega), RowPar.vb_lo _ (by omega)] at s0
  have l1 := ext_lam_lo W u τ (R.k - 1) (by omega)
  have ck : ((R.k - 1 : ℕ) : ℚ) = (R.k : ℚ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  rw [s0, l1, ck] at hhead'
  unfold RowPar.sh at hhead'
  push_cast at hhead'
  linarith

end Place2

end GlobalTheory.ColRows.LastSideProof

namespace GlobalTheory.ColRows.LastSideProof

section Place3

variable {X : Fields} {Word : Type} {R : Ranks} (W : Wts X Word R) (hW : W.Ok) (u : Word) (τ : X.Tau)
include hW

/- English proof (translation)
Establish `hk` using `R.m_add_three_le_k`. Establish `hm` using `R.two_le_m`. Establish `hI` using `GlobalTheory.BranchMembers.interlace W hW u τ`. Establish `hNn : R.N R.m - 1 = R.k + (R.m - 1) * (R.t + 1) + R.t`. Establish `e : (R.m - 1) * (R.t + 1) + (R.t + 1) = R.m * (R.t + 1)`.

Rewrite using `[← Nat.succ_mul]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers. Unfold `Ranks.N`. Generalize the expression as in `(R.m - 1) * (R.t + 1) = A at e ⊢`.

Generalize the expression as in `R.m * (R.t + 1) = A' at e ⊢`. Use linear arithmetic over natural numbers and integers. Establish `hpn : R.k - 1 < R.N R.m - 1` using `by rw [hNn]; omega`. Establish `h1` using `dOne_le (N_m_succ R) (W.lamTrue u R.m τ) (W.sgTrue τ) (R.k - 1) (by omega) hpn`. Establish `hnonneg : ∀ i ∈ Finset.range (R.N R.m - 1), 0 ≤ ext (W.sgTrue τ) i - ext (W.lamTrue u R.m τ) (i + 1)`.

Introduce `i hi`. Rewrite `hi` using `[Finset.mem_range]`. Establish `h2` using `(hI ⟨i, hi⟩).1`. Rewrite `h2` using `[Br.aBr, ← ext_of (W.sgTrue τ), ← ext_of (W.lamTrue u R.m τ)]`. Conclude with `h2`.

Establish `hsingle` using `Finset.single_le_sum hnonneg (Finset.mem_range.2 (by omega : R.k - 2 < R.N R.m - 1))`. Rewrite `hsingle` using `[← first_difference_eq_range_sum (N_m_succ R)]`. Establish `e2 : R.k - 2 + 1 = R.k - 1` using `by omega`. Rewrite `hsingle` using `[e2]`. Establish `e3 : R.k - 1 + 1 = R.k + 0 * (R.t + 1) + 0` using `by omega`.

Establish `hext : ext (W.lamTrue u R.m τ) (R.N R.m - 1) = ext (W.lamTrue u R.m τ) (R.k + (R.m - 1) * (R.t + 1) + R.t)` using `congrArg _ hNn`. Rewrite `h1` using `[e3, hext]`. Establish `l1` using `ext_lam_lo W u τ 1 (by omega)`. Establish `lk` using `ext_lam_lo W u τ (R.k - 1) (by omega)`. Establish `lh0` using `ext_lam_hi W u τ 0 0 (by omega) (by omega)`.

Establish `lh1` using `ext_lam_hi W u τ (R.m - 1) R.t (by omega) (by omega)`. Establish `s2` using `ext_sg W u τ hW (R.k - 2) (by omega)`. Rewrite `s2` using `[RowPar.sgHC_lo _ (by omega), RowPar.vb_lo _ (by omega)]`. Establish `h1q : ((GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne (N_m_succ R) (W.lamTrue u R.m τ) (W.sgTrue τ) : ℤ) : ℚ) ≤ 2 * ((Br.d0 (N_m_succ R) (W.lamTrue u R.m τ) (W.sgTrue τ) : ℤ) : ℚ) + ((ext (W.lamTrue u R.m τ) 1 : ℚ) - (ext (W.lamTrue u R.m τ) (R.k - 1) : ℚ)) …` using `by exact_mod_cast h1`. Establish `hsq : (ext (W.sgTrue τ) (R.k - 2) : ℚ) - (ext (W.lamTrue u R.m τ) (R.k - 1) : ℚ) ≤ ((Br.d0 (N_m_succ R) (W.lamTrue u R.m τ) (W.sgTrue τ) : ℤ) : ℚ)` using `by exact_mod_cast hsingle`.

Establish `ck1 : ((R.k - 1 : ℕ) : ℚ) = (R.k : ℚ) - 1` using `by rw [Nat.cast_sub (by omega)]; simp`. Establish `ck2 : ((R.k - 2 : ℕ) : ℚ) = (R.k : ℚ) - 2` using `by rw [Nat.cast_sub (by omega)]; simp`. Establish `cm1 : ((R.m - 1 : ℕ) : ℚ) = (R.m : ℚ) - 1` using `by rw [Nat.cast_sub (by omega)]; simp`. Rewrite `h1q` using `[l1, lk, lh0, lh1]`. Rewrite `hsq` using `[s2, lk]`.

Simplify using `only [ck1, ck2, cm1, Nat.cast_zero, Nat.cast_one] at h1q hsq`. Unfold `RowPar.sh at hsq`. Establish `e4 : (⟨R.k - 2, by omega⟩ : Fin (R.k - 1)) = ⟨R.k - 2, by omega⟩` using `rfl`. Use polynomial arithmetic with `[h1q, hsq]`.
-/
theorem dOne_le_place :
    ((GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne (N_m_succ R) (W.lamTrue u R.m τ) (W.sgTrue τ) : ℤ) : ℚ) ≤
      3 * ((Br.d0 (N_m_succ R) (W.lamTrue u R.m τ) (W.sgTrue τ) : ℤ) : ℚ) +
        ((W.hc u τ).u ⟨1, by have := R.m_add_three_le_k; omega⟩ - (W.hc u τ).v ⟨R.k - 2, by have := R.m_add_three_le_k; omega⟩ +
          5 / 2 - (R.k : ℚ)) +
        ((RowPar.of (W.hc u τ)).eAt (R.m - 1) - (RowPar.of (W.hc u τ)).eAt 0 - ((R.m : ℚ) - 1) * ((R.t : ℚ) + 1)) := by
  have hk := R.m_add_three_le_k
  have hm := R.two_le_m
  have hI := GlobalTheory.BranchMembers.interlace W hW u τ
  have hNn : R.N R.m - 1 = R.k + (R.m - 1) * (R.t + 1) + R.t := by
    have e : (R.m - 1) * (R.t + 1) + (R.t + 1) = R.m * (R.t + 1) := by
      rw [← Nat.succ_mul]; congr 1; omega
    unfold Ranks.N
    generalize (R.m - 1) * (R.t + 1) = A at e ⊢
    generalize R.m * (R.t + 1) = A' at e ⊢
    omega
  have hpn : R.k - 1 < R.N R.m - 1 := by rw [hNn]; omega
  have h1 := dOne_le (N_m_succ R) (W.lamTrue u R.m τ) (W.sgTrue τ) (R.k - 1) (by omega) hpn

  have hnonneg : ∀ i ∈ Finset.range (R.N R.m - 1), 0 ≤ ext (W.sgTrue τ) i - ext (W.lamTrue u R.m τ) (i + 1) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have h2 := (hI ⟨i, hi⟩).1
    rw [Br.aBr, ← ext_of (W.sgTrue τ), ← ext_of (W.lamTrue u R.m τ)] at h2
    exact h2
  have hsingle := Finset.single_le_sum hnonneg (Finset.mem_range.2 (by omega : R.k - 2 < R.N R.m - 1))
  rw [← first_difference_eq_range_sum (N_m_succ R)] at hsingle
  have e2 : R.k - 2 + 1 = R.k - 1 := by omega
  rw [e2] at hsingle
  have e3 : R.k - 1 + 1 = R.k + 0 * (R.t + 1) + 0 := by omega
  have hext : ext (W.lamTrue u R.m τ) (R.N R.m - 1) = ext (W.lamTrue u R.m τ) (R.k + (R.m - 1) * (R.t + 1) + R.t) :=
    congrArg _ hNn
  rw [e3, hext] at h1
  have l1 := ext_lam_lo W u τ 1 (by omega)
  have lk := ext_lam_lo W u τ (R.k - 1) (by omega)
  have lh0 := ext_lam_hi W u τ 0 0 (by omega) (by omega)
  have lh1 := ext_lam_hi W u τ (R.m - 1) R.t (by omega) (by omega)
  have s2 := ext_sg W u τ hW (R.k - 2) (by omega)
  rw [RowPar.sgHC_lo _ (by omega), RowPar.vb_lo _ (by omega)] at s2
  have h1q : ((GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne (N_m_succ R) (W.lamTrue u R.m τ) (W.sgTrue τ) : ℤ) : ℚ) ≤
      2 * ((Br.d0 (N_m_succ R) (W.lamTrue u R.m τ) (W.sgTrue τ) : ℤ) : ℚ) +
        ((ext (W.lamTrue u R.m τ) 1 : ℚ) - (ext (W.lamTrue u R.m τ) (R.k - 1) : ℚ)) +
        ((ext (W.lamTrue u R.m τ) (R.k + 0 * (R.t + 1) + 0) : ℚ) -
          (ext (W.lamTrue u R.m τ) (R.k + (R.m - 1) * (R.t + 1) + R.t) : ℚ)) := by exact_mod_cast h1
  have hsq : (ext (W.sgTrue τ) (R.k - 2) : ℚ) - (ext (W.lamTrue u R.m τ) (R.k - 1) : ℚ) ≤
      ((Br.d0 (N_m_succ R) (W.lamTrue u R.m τ) (W.sgTrue τ) : ℤ) : ℚ) := by exact_mod_cast hsingle
  have ck1 : ((R.k - 1 : ℕ) : ℚ) = (R.k : ℚ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  have ck2 : ((R.k - 2 : ℕ) : ℚ) = (R.k : ℚ) - 2 := by rw [Nat.cast_sub (by omega)]; simp
  have cm1 : ((R.m - 1 : ℕ) : ℚ) = (R.m : ℚ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  rw [l1, lk, lh0, lh1] at h1q
  rw [s2, lk] at hsq
  simp only [ck1, ck2, cm1, Nat.cast_zero, Nat.cast_one] at h1q hsq
  unfold RowPar.sh at hsq
  have e4 : (⟨R.k - 2, by omega⟩ : Fin (R.k - 1)) = ⟨R.k - 2, by omega⟩ := rfl
  nlinarith [h1q, hsq]

end Place3

end GlobalTheory.ColRows.LastSideProof

namespace GlobalTheory.ColRows.LastSideProof

/- English proof (translation)
Simplify using `[NumDatum.uW]`.
-/
theorem uW_first (N : NumDatum) (δ : Code N) (z : RPl N.R) (h : 0 < N.R.k) : N.uW δ z ⟨0, h⟩ = (N.hc z).u ⟨0, h⟩ := by
  simp [NumDatum.uW]

/- English proof (translation)
Unfold `NumDatum.uW`. Rewrite using `[dif_neg (by simp only; omega)]`.
-/
theorem uW_last (N : NumDatum) (δ : Code N) (z : RPl N.R) (h : N.R.k - 1 < N.R.k) :
    N.uW δ z ⟨N.R.k - 1, h⟩ = (N.hc z).u ⟨N.R.k - 1, h⟩ := by
  unfold NumDatum.uW
  rw [dif_neg (by simp only; omega)]

/- English proof (translation)
The claim follows from `Rat.cast_le.mpr h`.
-/
theorem castQ {a b : ℚ} (h : a ≤ b) : (a : ℝ) ≤ (b : ℝ) := Rat.cast_le.mpr h

/- English proof (translation)
Introduce `hO N X Pr W pl u δ J _ eJ R hWT hS hSR hT hR`. Take `⟨C, hC⟩` from `hO`. Establish `hW : W.Ok` using `hWT.1`. Establish `hk` using `N.R.m_add_three_le_k`. Establish `hm` using `N.R.two_le_m`.

Take `⟨hL, ha, -, -, hmR, -, hkR, hNn, hSc, hη, hb', -⟩` from `hR.nums`. Take `⟨-, -, hlogT, -, -, hnodes, hcloud, -, hbT, hoff⟩` from `id hSR`. Establish `hNq : ((N.Nm : ℕ) : ℝ) = (N.R.k : ℝ) + (N.R.m : ℝ) * ((N.R.t : ℝ) + 1)`. Unfold `NumDatum.Nm Ranks.N`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Set `lam1 : RPl N.R → ℝ` to `fun z => (ext (W.lamTrue u N.R.m (pl z)) 0 : ℝ)`. Set `D0 : RPl N.R → ℝ` to `fun z => ((Br.d0 (N_m_succ N.R) (W.lamTrue u N.R.m (pl z)) (W.sgTrue (pl z)) : ℤ) : ℝ)`. Set `D1 : RPl N.R → ℝ` to `fun z => ((GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne (N_m_succ N.R) (W.lamTrue u N.R.m (pl z)) (W.sgTrue (pl z)) : ℤ) : ℝ)`. Set `logc : RPl N.R → ℝ` to `fun z => (R.Nn - 1) * D1 z * Real.log (2 * R.a)`.

Set `logxi : RPl N.R → ℝ` to `fun _ => R.Nn * (R.Nn - 1) / 2 * Real.log (2 * R.a)`. Set `bT : RPl N.R → ℝ` to `fun z => ((N.bT z.2 : ℚ) : ℝ)`. Establish `hrow : ∀ z, (W.hc u (pl z)).v = (N.hc z).v ∧ (W.hc u (pl z)).b = (N.hc z).b ∧ (W.hc u (pl z)).e = (N.hc z).e` using `fun z => ⟨congrArg RowPar.v (hWT.2.2 z).1, congrArg RowPar.b (hWT.2.2 z).1, congrArg RowPar.e (hWT.2.2 z).1⟩`. Establish `hu0 : ∀ z, (W.hc u (pl z)).u ⟨0, by omega⟩ = (N.hc z).u ⟨0, by omega⟩` using `fun z => ((hWT.2.2 z).2 _).trans (uW_first N δ z _)`. Establish `hul : ∀ z, (W.hc u (pl z)).u ⟨N.R.k - 1, by omega⟩ = (N.hc z).u ⟨N.R.k - 1, by omega⟩` using `fun z => ((hWT.2.2 z).2 _).trans (uW_last N δ z _)`.

Establish `hlam1 : ∀ z, lam1 z = (((N.hc z).u ⟨0, by omega⟩ : ℚ) : ℝ) - ((N.R.k : ℝ) - 1) / 2 - (N.R.m : ℝ) * (((N.R.t : ℝ) + 1) / 2)`. Introduce `z`. Establish `h` using `congrArg (fun q : ℚ => (q : ℝ)) (ext_lam_lo W u (pl z) 0 (by omega))`. Rewrite `h` using `[hu0 z]`. Move the coercions through the operations in `at h`.

Use `show (ext (W.lamTrue u N.R.m (pl z)) 0 : ℝ) = _`. Rewrite using `[h]`. Expand and normalize the polynomial expressions, which then agree. Establish `hsumB : ∀ z, ((∑ B ∈ Finset.range N.R.m, ((RowPar.of (W.hc u (pl z))).eAt B - (RowPar.of (W.hc u (pl z))).bAt B - ((N.R.t : ℚ) + 1) / 2) : ℚ) : ℝ) ≤ (N.R.m : ℝ) * N.eta`. Introduce `z`.

Use `push_cast`. Establish `: ∀ B ∈ Finset.range N.R.m, (((RowPar.of (W.hc u (pl z))).eAt B : ℚ) : ℝ) - (((RowPar.of (W.hc u (pl z))).bAt B : ℚ) : ℝ) - ((N.R.t : ℝ) + 1) / 2 ≤ N.eta`. Introduce `B hB`. Rewrite `hB` using `[Finset.mem_range]`. Rewrite using `[RowPar.eAt_of _ hB, RowPar.bAt_of _ hB, (hrow z).2.1, (hrow z).2.2]`.

Establish `h1` using `hnodes z ⟨B, hB⟩ ⟨B, hB⟩`. Establish `h2` using `neg_abs_le ((((N.hc z).b ⟨B, hB⟩ - (N.hc z).e ⟨B, hB⟩ : ℚ) : ℝ))`. Move the coercions through the operations in `at h1 h2`. Establish `ht : (0 : ℝ) ≤ N.R.t` using `Nat.cast_nonneg _`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `(Finset.sum_le_sum this).trans ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_const, Finset.card_range, nsmul_eq_mul]`. Establish `hD0 : ∀ z, D0 z ≤ N.Sc + (N.R.m : ℝ) * N.eta + (if z ∈ R.TT then bT z else 0)`. Introduce `z`. Establish `h` using `castQ (bottomRank_sum_le_two_mul_totalRank W hW u (pl z))`.

Move the coercions through the operations in `at h`. Establish `hB` using `hsumB z`. Move the coercions through the operations in `at hB`. Establish `hv0` using `hcloud z ⟨0, by omega⟩`. Rewrite `hv0` using `[← (hrow z).1]`.

Establish `hv0' : (((W.hc u (pl z)).v ⟨0, by omega⟩ : ℚ) : ℝ) ≤ N.Sc` using `hv0.2`. Establish `hkR' : (5 : ℝ) ≤ N.R.k` using `by exact_mod_cast (by omega : 5 ≤ N.R.k)`. Use `show ((Br.d0 (N_m_succ N.R) (W.lamTrue u N.R.m (pl z)) (W.sgTrue (pl z)) : ℤ) : ℝ) ≤ _`. Use `split_ifs with htop`. Take `⟨h1, h2⟩` from `(hR.tops z).1 htop`.

Establish `hbz : bT z = -(((N.hc z).u ⟨N.R.k - 1, by omega⟩ : ℚ) : ℝ) - ((N.R.k : ℝ) - 1) / 2` using `by show ((N.bT z.2 : ℚ) : ℝ) = _`. Take `⟨b, t⟩` from `z`. Simplify using `only at h1`. Substitute `h1` using the available equality. Unfold `NumDatum.bT`.

Use `push_cast`. Both sides reduce to the same expression. Rewrite using `[hbz, ← hul z]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hzero : (0 : ℚ) ≤ (N.hc z).v ⟨N.R.k - 2, by omega⟩` using `(hcloud z ⟨N.R.k - 2, by omega⟩).1`.

Take `⟨hlast, -, -⟩` from `hoff z (fun h => htop ((hR.tops z).2 h)) (by omega)`. Establish `hl : (((W.hc u (pl z)).u ⟨N.R.k - 1, by omega⟩ : ℚ) : ℝ) = (((N.hc z).v ⟨N.R.k - 2, by omega⟩ : ℚ) : ℝ) - 1 / 2`. Rewrite using `[hul z, hlast]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hzero' : (0 : ℝ) ≤ (((N.hc z).v ⟨N.R.k - 2, by omega⟩ : ℚ) : ℝ)` using `by exact_mod_cast hzero`. Rewrite `h` using `[hl]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hD1 : ∀ z, D1 z ≤ 3 * D0 z + N.Sc + N.eta`. Introduce `z`.

Establish `h` using `castQ (dOne_le_place W hW u (pl z))`. Move the coercions through the operations in `at h`. Establish `hv0` using `(hcloud z ⟨0, by omega⟩).2`. Establish `hvk` using `(hcloud z ⟨N.R.k - 2, by omega⟩).1`. Rewrite `hv0`, `hvk` using `[← (hrow z).1]`.

Establish `hvk' : (0 : ℝ) ≤ (((W.hc u (pl z)).v ⟨N.R.k - 2, by omega⟩ : ℚ) : ℝ)` using `by exact_mod_cast hvk`. Establish `hu1 : (((W.hc u (pl z)).u ⟨1, by omega⟩ : ℚ) : ℝ) < (((W.hc u (pl z)).v ⟨0, by omega⟩ : ℚ) : ℝ)`. Conclude with `(W.hc u (pl z)).v_gt_u ⟨0, by omega⟩` after adjusting the coercions. Rewrite `h` using `[RowPar.eAt_of _ (by omega : N.R.m - 1 < N.R.m), RowPar.eAt_of _ (by omega : 0 < N.R.m)]`. Establish `hg` using `(W.hc u (pl z)).gap_be ⟨0, by omega⟩`.

Establish `hg' : ((((W.hc u (pl z)).b ⟨0, by omega⟩ : ℚ)) : ℝ) ≤ (((W.hc u (pl z)).e ⟨0, by omega⟩ : ℚ) : ℝ)`. Establish `ht : (0 : ℚ) ≤ N.R.t` using `Nat.cast_nonneg _`. Conclude with `(by linarith : (W.hc u (pl z)).b ⟨0, by omega⟩ ≤ (W.hc u (pl z)).e ⟨0, by omega⟩)` after adjusting the coercions. Establish `hn` using `hnodes z ⟨0, by omega⟩ ⟨N.R.m - 1, by omega⟩`. Rewrite `hn` using `[← (hrow z).2.1, ← (hrow z).2.2]`.

Establish `hn'` using `neg_abs_le ((((W.hc u (pl z)).b ⟨0, by omega⟩ - (W.hc u (pl z)).e ⟨N.R.m - 1, by omega⟩ : ℚ) : ℝ))`. Move the coercions through the operations in `at hn hn'`. Establish `hkR' : (5 : ℝ) ≤ N.R.k` using `by exact_mod_cast (by omega : 5 ≤ N.R.k)`. Establish `hmt : (0 : ℝ) ≤ ((N.R.m : ℝ) - 1) * ((N.R.t : ℝ) + 1)`. Establish `: (1 : ℝ) ≤ N.R.m` using `by exact_mod_cast (by omega : 1 ≤ N.R.m)`.

Establish `: (0 : ℝ) ≤ N.R.t` using `Nat.cast_nonneg _`. Use the polynomial consequences of the given equalities and inequalities. Use `show ((GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne (N_m_succ N.R) (W.lamTrue u N.R.m (pl z)) (W.sgTrue (pl z)) : ℤ) : ℝ) ≤ 3 * ((Br.d0 (N_m_succ N.R) (W.lamTrue u N.R.m (pl z)) (W.sgTrue (pl z)) : ℤ) : ℝ) + N.Sc + N.eta`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨bT, fun z => lam1 z - D0 z, lam1, D0, D1, logc, logxi, ?_, fun z => le_rfl, fun z => le_rfl, fun z => rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Establish `hI` using `weights_interlace_sameShift N X Pr W pl u δ hWT hSR`. Establish `hsp : ∀ τ, (((W.lamTrue u N.R.m τ).spread : ℤ) : ℝ) ≤ 2 * N.sc.a` using `fun τ => hS.spread_le u N.R.m le_rfl τ`. Take `⟨-, hlog, -⟩` from `hC X.Tau (N.R.N N.R.m) (N.R.N N.R.m - 1) (N_m_succ N.R) (fun τ => W.lamTrue u N.R.m τ) W.sgTrue hI.1 N.sc.a hsp`. Establish `hA : lastLog W u = -((∑ τ, Br.nBr (W.lamTrue u N.R.m τ) (W.sgTrue τ) : ℤ) : ℝ) * Real.log (Pr.T u : ℝ) + Real.log (GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.orthNormSq (N_m_succ N.R) (fun τ => W.lamTrue u N.R.m τ) W.sgTrue)` using `rfl`. Establish `h0 : ∀ z, ext (W.lamTrue u N.R.m (pl z)) 0 = (W.lamTrue u N.R.m (pl z)).w ⟨0, N.R.N_pos N.R.m⟩` using `fun z => ext_of _ ⟨0, _⟩`.

Establish `hn : ((∑ τ, Br.nBr (W.lamTrue u N.R.m τ) (W.sgTrue τ) : ℤ) : ℝ) = ∑ z, (lam1 z - D0 z)`. Rewrite using `[Int.cast_sum, ← Equiv.sum_comp pl]`. Use `Finset.sum_congr rfl fun z _ => ?_` and prove the remaining obligations. Rewrite using `[nBr_eq_sub (N_m_succ N.R)]`. Use `show _ = ((ext (W.lamTrue u N.R.m (pl z)) 0 : ℤ) : ℝ) - ((Br.d0 (N_m_succ N.R) (W.lamTrue u N.R.m (pl z)) (W.sgTrue (pl z)) : ℤ) : ℝ)`.

Rewrite using `[h0]`. Use `push_cast`. Both sides reduce to the same expression. Establish `hre : ∑ τ, (2 * (((N.R.N N.R.m : ℕ) : ℝ) - 1) * ((GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne (N_m_succ N.R) (W.lamTrue u N.R.m τ) (W.sgTrue τ) : ℤ) : ℝ) + ((N.R.N N.R.m : ℕ) : ℝ) * (((N.R.N N.R.m : ℕ) : ℝ) - 1) / 2) * Real.log (2 * N.sc.a) = ∑ z, (2 * lo …`. Rewrite using `[← Equiv.sum_comp pl]`.

Use `Finset.sum_congr rfl fun z _ => ?_` and prove the remaining obligations. Use `show _ = 2 * ((R.Nn - 1) * ((GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne (N_m_succ N.R) (W.lamTrue u N.R.m (pl z)) (W.sgTrue (pl z)) : ℤ) : ℝ) * Real.log (2 * R.a)) + R.Nn * (R.Nn - 1) / 2 * Real.log (2 * R.a)`. Rewrite using `[hNn, ha]`. Unfold `NumDatum.Nm`. Expand and normalize the polynomial expressions, which then agree.

Use `show lastLog W u ≤ -(∑ z, (lam1 z - D0 z) * R.logT) + ∑ z, (2 * logc z + logxi z)`. Rewrite using `[hA, hn, hR.logT, ← Finset.sum_mul, ← hre]`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `z hz`. Take `⟨h1, h2⟩` from `(hR.tops z).1 hz`.

Take `⟨b, t⟩` from `z`. Simplify using `only at h1`. Substitute `h1` using the available equality. Rewrite using `[hlam1, hR.aT t h2, hNn, hkR, hNq]`. Unfold `NumDatum.aT`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Introduce `z hz`. Take `⟨-, hS1, -⟩` from `hoff z (fun h => hz ((hR.tops z).2 h)) (by omega)`. Establish `hv` using `(hcloud z ⟨0, by omega⟩).1`.

Establish `hv' : (0 : ℝ) ≤ (((N.hc z).v ⟨0, by omega⟩ : ℚ) : ℝ)` using `by exact_mod_cast hv`. Rewrite using `[hlam1, hSc, hNn, hNq]`. Move the coercions through the operations in `at hS1`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `z`.

Rewrite using `[hSc, hmR, hη]`. Conclude with `hD0 z`. Introduce `z`. Rewrite using `[hSc, hη]`. Conclude with `hD1 z`.

Introduce `z hz`. Take `⟨h1, h2⟩` from `(hR.tops z).1 hz`. Take `⟨b, t⟩` from `z`. Simplify using `only at h1`. Substitute `h1` using the available equality.

Rewrite using `[hb']`. Conclude with `(hbT t h2).2`. Rewrite using `[hR.logT]`. Conclude with `Real.log_nonneg (by exact_mod_cast hT)`. Rewrite using `[hR.logT, hmR, hL]`.

Conclude with `hlogT`.
-/
theorem lastSide : GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.OrthNormLogBound → ∀ (N : NumDatum) (X : Fields) (Pr : Primes X) (W : Wts X Pr.Word N.R)
    (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N) (J : Type) [Fintype J] (eJ : J ≃ Fin N.R.m) (R : RecNums J (RPl N.R)),
    WeightTie N W pl u δ → Sizes Pr W N.sc.a → SizeRows N δ (Pr.T u) → 1 ≤ Pr.T u → Reads N eJ δ (Pr.T u) R →
    LastSide R 25 (lastLog W u) := by
  intro hO N X Pr W pl u δ J _ eJ R hWT hS hSR hT hR
  obtain ⟨C, hC⟩ := hO
  have hW : W.Ok := hWT.1
  have hk := N.R.m_add_three_le_k
  have hm := N.R.two_le_m
  obtain ⟨hL, ha, -, -, hmR, -, hkR, hNn, hSc, hη, hb', -⟩ := hR.nums
  obtain ⟨-, -, hlogT, -, -, hnodes, hcloud, -, hbT, hoff⟩ := id hSR
  have hNq : ((N.Nm : ℕ) : ℝ) = (N.R.k : ℝ) + (N.R.m : ℝ) * ((N.R.t : ℝ) + 1) := by
    unfold NumDatum.Nm Ranks.N; push_cast; ring

  let lam1 : RPl N.R → ℝ := fun z => (ext (W.lamTrue u N.R.m (pl z)) 0 : ℝ)
  let D0 : RPl N.R → ℝ := fun z => ((Br.d0 (N_m_succ N.R) (W.lamTrue u N.R.m (pl z)) (W.sgTrue (pl z)) : ℤ) : ℝ)
  let D1 : RPl N.R → ℝ := fun z =>
    ((GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne (N_m_succ N.R) (W.lamTrue u N.R.m (pl z)) (W.sgTrue (pl z)) : ℤ) : ℝ)
  let logc : RPl N.R → ℝ := fun z => (R.Nn - 1) * D1 z * Real.log (2 * R.a)
  let logxi : RPl N.R → ℝ := fun _ => R.Nn * (R.Nn - 1) / 2 * Real.log (2 * R.a)
  let bT : RPl N.R → ℝ := fun z => ((N.bT z.2 : ℚ) : ℝ)

  have hrow : ∀ z, (W.hc u (pl z)).v = (N.hc z).v ∧ (W.hc u (pl z)).b = (N.hc z).b ∧ (W.hc u (pl z)).e = (N.hc z).e := fun z =>
    ⟨congrArg RowPar.v (hWT.2.2 z).1, congrArg RowPar.b (hWT.2.2 z).1, congrArg RowPar.e (hWT.2.2 z).1⟩
  have hu0 : ∀ z, (W.hc u (pl z)).u ⟨0, by omega⟩ = (N.hc z).u ⟨0, by omega⟩ := fun z =>
    ((hWT.2.2 z).2 _).trans (uW_first N δ z _)
  have hul : ∀ z, (W.hc u (pl z)).u ⟨N.R.k - 1, by omega⟩ = (N.hc z).u ⟨N.R.k - 1, by omega⟩ := fun z =>
    ((hWT.2.2 z).2 _).trans (uW_last N δ z _)
  have hlam1 : ∀ z, lam1 z = (((N.hc z).u ⟨0, by omega⟩ : ℚ) : ℝ) - ((N.R.k : ℝ) - 1) / 2 -
      (N.R.m : ℝ) * (((N.R.t : ℝ) + 1) / 2) := by
    intro z
    have h := congrArg (fun q : ℚ => (q : ℝ)) (ext_lam_lo W u (pl z) 0 (by omega))
    rw [hu0 z] at h
    push_cast at h
    show (ext (W.lamTrue u N.R.m (pl z)) 0 : ℝ) = _
    rw [h]; ring
  have hsumB : ∀ z, ((∑ B ∈ Finset.range N.R.m, ((RowPar.of (W.hc u (pl z))).eAt B - (RowPar.of (W.hc u (pl z))).bAt B -
      ((N.R.t : ℚ) + 1) / 2) : ℚ) : ℝ) ≤ (N.R.m : ℝ) * N.eta := by
    intro z
    push_cast
    have : ∀ B ∈ Finset.range N.R.m, (((RowPar.of (W.hc u (pl z))).eAt B : ℚ) : ℝ) - (((RowPar.of (W.hc u (pl z))).bAt B : ℚ) : ℝ) -
        ((N.R.t : ℝ) + 1) / 2 ≤ N.eta := by
      intro B hB
      rw [Finset.mem_range] at hB
      rw [RowPar.eAt_of _ hB, RowPar.bAt_of _ hB, (hrow z).2.1, (hrow z).2.2]
      have h1 := hnodes z ⟨B, hB⟩ ⟨B, hB⟩
      have h2 := neg_abs_le ((((N.hc z).b ⟨B, hB⟩ - (N.hc z).e ⟨B, hB⟩ : ℚ) : ℝ))
      push_cast at h1 h2
      have ht : (0 : ℝ) ≤ N.R.t := Nat.cast_nonneg _
      linarith
    refine (Finset.sum_le_sum this).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hD0 : ∀ z, D0 z ≤ N.Sc + (N.R.m : ℝ) * N.eta + (if z ∈ R.TT then bT z else 0) := by
    intro z
    have h := castQ (bottomRank_sum_le_two_mul_totalRank W hW u (pl z))
    push_cast at h
    have hB := hsumB z
    push_cast at hB
    have hv0 := hcloud z ⟨0, by omega⟩
    rw [← (hrow z).1] at hv0
    have hv0' : (((W.hc u (pl z)).v ⟨0, by omega⟩ : ℚ) : ℝ) ≤ N.Sc := hv0.2
    have hkR' : (5 : ℝ) ≤ N.R.k := by exact_mod_cast (by omega : 5 ≤ N.R.k)
    show ((Br.d0 (N_m_succ N.R) (W.lamTrue u N.R.m (pl z)) (W.sgTrue (pl z)) : ℤ) : ℝ) ≤ _
    split_ifs with htop
    · obtain ⟨h1, h2⟩ := (hR.tops z).1 htop
      have hbz : bT z = -(((N.hc z).u ⟨N.R.k - 1, by omega⟩ : ℚ) : ℝ) - ((N.R.k : ℝ) - 1) / 2 := by
        show ((N.bT z.2 : ℚ) : ℝ) = _
        obtain ⟨b, t⟩ := z
        simp only at h1
        subst h1
        unfold NumDatum.bT
        push_cast
        rfl
      rw [hbz, ← hul z]
      linarith
    · have hzero : (0 : ℚ) ≤ (N.hc z).v ⟨N.R.k - 2, by omega⟩ := (hcloud z ⟨N.R.k - 2, by omega⟩).1
      obtain ⟨hlast, -, -⟩ := hoff z (fun h => htop ((hR.tops z).2 h)) (by omega)
      have hl : (((W.hc u (pl z)).u ⟨N.R.k - 1, by omega⟩ : ℚ) : ℝ) = (((N.hc z).v ⟨N.R.k - 2, by omega⟩ : ℚ) : ℝ) - 1 / 2 := by
        rw [hul z, hlast]; push_cast; ring
      have hzero' : (0 : ℝ) ≤ (((N.hc z).v ⟨N.R.k - 2, by omega⟩ : ℚ) : ℝ) := by exact_mod_cast hzero
      rw [hl] at h
      linarith
  have hD1 : ∀ z, D1 z ≤ 3 * D0 z + N.Sc + N.eta := by
    intro z
    have h := castQ (dOne_le_place W hW u (pl z))
    push_cast at h
    have hv0 := (hcloud z ⟨0, by omega⟩).2
    have hvk := (hcloud z ⟨N.R.k - 2, by omega⟩).1
    rw [← (hrow z).1] at hv0 hvk
    have hvk' : (0 : ℝ) ≤ (((W.hc u (pl z)).v ⟨N.R.k - 2, by omega⟩ : ℚ) : ℝ) := by exact_mod_cast hvk
    have hu1 : (((W.hc u (pl z)).u ⟨1, by omega⟩ : ℚ) : ℝ) < (((W.hc u (pl z)).v ⟨0, by omega⟩ : ℚ) : ℝ) := by
      exact_mod_cast (W.hc u (pl z)).v_gt_u ⟨0, by omega⟩
    rw [RowPar.eAt_of _ (by omega : N.R.m - 1 < N.R.m), RowPar.eAt_of _ (by omega : 0 < N.R.m)] at h
    have hg := (W.hc u (pl z)).gap_be ⟨0, by omega⟩
    have hg' : ((((W.hc u (pl z)).b ⟨0, by omega⟩ : ℚ)) : ℝ) ≤ (((W.hc u (pl z)).e ⟨0, by omega⟩ : ℚ) : ℝ) := by
      have ht : (0 : ℚ) ≤ N.R.t := Nat.cast_nonneg _
      exact_mod_cast (by linarith : (W.hc u (pl z)).b ⟨0, by omega⟩ ≤ (W.hc u (pl z)).e ⟨0, by omega⟩)
    have hn := hnodes z ⟨0, by omega⟩ ⟨N.R.m - 1, by omega⟩
    rw [← (hrow z).2.1, ← (hrow z).2.2] at hn
    have hn' := neg_abs_le ((((W.hc u (pl z)).b ⟨0, by omega⟩ - (W.hc u (pl z)).e ⟨N.R.m - 1, by omega⟩ : ℚ) : ℝ))
    push_cast at hn hn'
    have hkR' : (5 : ℝ) ≤ N.R.k := by exact_mod_cast (by omega : 5 ≤ N.R.k)
    have hmt : (0 : ℝ) ≤ ((N.R.m : ℝ) - 1) * ((N.R.t : ℝ) + 1) := by
      have : (1 : ℝ) ≤ N.R.m := by exact_mod_cast (by omega : 1 ≤ N.R.m)
      have : (0 : ℝ) ≤ N.R.t := Nat.cast_nonneg _
      nlinarith
    show ((GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne (N_m_succ N.R) (W.lamTrue u N.R.m (pl z)) (W.sgTrue (pl z)) : ℤ) : ℝ) ≤
      3 * ((Br.d0 (N_m_succ N.R) (W.lamTrue u N.R.m (pl z)) (W.sgTrue (pl z)) : ℤ) : ℝ) + N.Sc + N.eta
    linarith
  refine ⟨bT, fun z => lam1 z - D0 z, lam1, D0, D1, logc, logxi, ?_, fun z => le_rfl, fun z => le_rfl, fun z => rfl,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have hI := weights_interlace_sameShift N X Pr W pl u δ hWT hSR
    have hsp : ∀ τ, (((W.lamTrue u N.R.m τ).spread : ℤ) : ℝ) ≤ 2 * N.sc.a := fun τ => hS.spread_le u N.R.m le_rfl τ
    obtain ⟨-, hlog, -⟩ := hC X.Tau (N.R.N N.R.m) (N.R.N N.R.m - 1) (N_m_succ N.R) (fun τ => W.lamTrue u N.R.m τ) W.sgTrue
      hI.1 N.sc.a hsp
    have hA : lastLog W u = -((∑ τ, Br.nBr (W.lamTrue u N.R.m τ) (W.sgTrue τ) : ℤ) : ℝ) * Real.log (Pr.T u : ℝ) +
        Real.log (GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.orthNormSq (N_m_succ N.R) (fun τ => W.lamTrue u N.R.m τ) W.sgTrue) := rfl
    have h0 : ∀ z, ext (W.lamTrue u N.R.m (pl z)) 0 = (W.lamTrue u N.R.m (pl z)).w ⟨0, N.R.N_pos N.R.m⟩ := fun z =>
      ext_of _ ⟨0, _⟩
    have hn : ((∑ τ, Br.nBr (W.lamTrue u N.R.m τ) (W.sgTrue τ) : ℤ) : ℝ) = ∑ z, (lam1 z - D0 z) := by
      rw [Int.cast_sum, ← Equiv.sum_comp pl]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [nBr_eq_sub (N_m_succ N.R)]
      show _ = ((ext (W.lamTrue u N.R.m (pl z)) 0 : ℤ) : ℝ) -
        ((Br.d0 (N_m_succ N.R) (W.lamTrue u N.R.m (pl z)) (W.sgTrue (pl z)) : ℤ) : ℝ)
      rw [h0]
      push_cast
      rfl
    have hre : ∑ τ, (2 * (((N.R.N N.R.m : ℕ) : ℝ) - 1) *
          ((GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne (N_m_succ N.R) (W.lamTrue u N.R.m τ) (W.sgTrue τ) : ℤ) : ℝ) +
          ((N.R.N N.R.m : ℕ) : ℝ) * (((N.R.N N.R.m : ℕ) : ℝ) - 1) / 2) * Real.log (2 * N.sc.a) =
        ∑ z, (2 * logc z + logxi z) := by
      rw [← Equiv.sum_comp pl]
      refine Finset.sum_congr rfl fun z _ => ?_
      show _ = 2 * ((R.Nn - 1) * ((GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne (N_m_succ N.R) (W.lamTrue u N.R.m (pl z)) (W.sgTrue (pl z)) : ℤ) : ℝ) *
        Real.log (2 * R.a)) + R.Nn * (R.Nn - 1) / 2 * Real.log (2 * R.a)
      rw [hNn, ha]
      unfold NumDatum.Nm
      ring
    show lastLog W u ≤ -(∑ z, (lam1 z - D0 z) * R.logT) + ∑ z, (2 * logc z + logxi z)
    rw [hA, hn, hR.logT, ← Finset.sum_mul, ← hre]
    linarith
  · intro z hz
    obtain ⟨h1, h2⟩ := (hR.tops z).1 hz
    obtain ⟨b, t⟩ := z
    simp only at h1
    subst h1
    rw [hlam1, hR.aT t h2, hNn, hkR, hNq]
    unfold NumDatum.aT
    push_cast
    ring
  · intro z hz
    obtain ⟨-, hS1, -⟩ := hoff z (fun h => hz ((hR.tops z).2 h)) (by omega)
    have hv := (hcloud z ⟨0, by omega⟩).1
    have hv' : (0 : ℝ) ≤ (((N.hc z).v ⟨0, by omega⟩ : ℚ) : ℝ) := by exact_mod_cast hv
    rw [hlam1, hSc, hNn, hNq]
    push_cast at hS1
    linarith
  · intro z
    rw [hSc, hmR, hη]
    exact hD0 z
  · intro z
    rw [hSc, hη]
    exact hD1 z
  · intro z hz
    obtain ⟨h1, h2⟩ := (hR.tops z).1 hz
    obtain ⟨b, t⟩ := z
    simp only at h1
    subst h1
    rw [hb']
    exact (hbT t h2).2
  · rw [hR.logT]
    exact Real.log_nonneg (by exact_mod_cast hT)
  · rw [hR.logT, hmR, hL]
    exact hlogT

end GlobalTheory.ColRows.LastSideProof
