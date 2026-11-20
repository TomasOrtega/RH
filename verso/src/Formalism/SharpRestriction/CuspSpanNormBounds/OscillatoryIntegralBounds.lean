import Formalism.SharpRestriction.CuspSpanNormBounds.RadialChainStatements
import Formalism.SharpRestriction.CuspSpanNormBounds.BlockEstimateTheorem
import Formalism.SharpRestriction.CuspSpanNormBounds.HereditaryPositivity
import Formalism.SharpRestriction.CuspSpanNormBounds.RadialLemmaE
import Formalism.SharpRestriction.CuspSpanNormBounds.DiagonalEntryIdentity
import Formalism.YangianSpanCharacter.YangianRelationFirst
import Formalism.FormalDegreeBessel.FinalWR
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BoxOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DualVolumePowerIdentity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChebyshevExtremalPolynomials
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FacSuccOfNotMem
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdditiveCharacterPsi
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AffineChangeOfVariables
import Formalism.HermitianCurvature.HermitianCurvatureProofs.StabilizerBlockPoint
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousInvUpper
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralConvergesAbs
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Markov
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OneLevelInequality
import Formalism.LatticeTheta.ThetaShiftInversion
import Mathlib
import Formalism.FormalDegreeBessel.FinalBF
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalDataRealPlace
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LatticeRigidity.RecursionUnrestrictedFalse
import Formalism.HermitianCurvature.StatementTA

section PartA3c

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA

namespace Formalism.MainNotions.InterlacingSignCuts

section Cut

variable {k0 : ℕ}

/- English proof (translation)
Conclude with `Fin.strictAnti_iff_succ_lt.2 fun j => (h j).2.trans (h j).1`.
-/
theorem interlace_strictAnti {u : Fin (k0 + 1) → ℝ} {ρ : Fin k0 → ℝ} (h : Interlace u ρ) : StrictAnti u := by
  exact Fin.strictAnti_iff_succ_lt.2 fun j => (h j).2.trans (h j).1

/- English proof (translation)
Establish `ha` using `(interlace_strictAnti h).antitone`. Establish `hle : j.succ ≤ l`. Rewrite using `[Fin.le_def, Fin.val_succ]`. Use linear arithmetic over natural numbers and integers. Conclude with `lt_of_le_of_lt (ha hle) (h j).2`.
-/
theorem rho_gt {u : Fin (k0 + 1) → ℝ} {ρ : Fin k0 → ℝ} (h : Interlace u ρ) (l : Fin (k0 + 1)) (j : Fin k0)
    (hj : j.val < l.val) : u l < ρ j := by
  have ha := (interlace_strictAnti h).antitone
  have hle : j.succ ≤ l := by
    rw [Fin.le_def, Fin.val_succ]; omega
  exact lt_of_le_of_lt (ha hle) (h j).2

/- English proof (translation)
Establish `ha` using `(interlace_strictAnti h).antitone`. Establish `hle : l ≤ j.castSucc`. Rewrite using `[Fin.le_def, Fin.coe_castSucc]`. Conclude with `hj`. Conclude with `lt_of_lt_of_le (h j).1 (ha hle)`.
-/
theorem rho_lt {u : Fin (k0 + 1) → ℝ} {ρ : Fin k0 → ℝ} (h : Interlace u ρ) (l : Fin (k0 + 1)) (j : Fin k0)
    (hj : l.val ≤ j.val) : ρ j < u l := by
  have ha := (interlace_strictAnti h).antitone
  have hle : l ≤ j.castSucc := by
    rw [Fin.le_def, Fin.coe_castSucc]; exact hj
  exact lt_of_lt_of_le (h j).1 (ha hle)

/- English proof (translation)
Take `⟨hYa, hYb⟩` from `hY`. Break down `le_total (u l) (u' l) with h | h` into its components or cases. Use `right`. Establish `e1 : min (-u l) (-u' l) = -u' l` using `min_eq_right (by linarith)`. Establish `e2 : max (-u l) (-u' l) = -u l` using `max_eq_left (by linarith)`.

Rewrite `h1` using `[e1]`. Rewrite `h2` using `[e2]`. Establish `p1 : 0 < Y + u' l` using `by linarith`. Establish `p2 : Y + u l < 0` using `by linarith`. Rewrite `h4` using `[abs_of_pos p1]`.

Rewrite `h3` using `[abs_of_neg p2]`. Apply the tactic sequence `constructor <;> linarith`. Use `left`. Establish `e1 : min (-u l) (-u' l) = -u l` using `min_eq_left (by linarith)`. Establish `e2 : max (-u l) (-u' l) = -u' l` using `max_eq_right (by linarith)`.

Rewrite `h1` using `[e1]`. Rewrite `h2` using `[e2]`. Establish `p1 : 0 < Y + u l` using `by linarith`. Establish `p2 : Y + u' l < 0` using `by linarith`. Rewrite `h3` using `[abs_of_pos p1]`.

Rewrite `h4` using `[abs_of_neg p2]`. Apply the tactic sequence `constructor <;> linarith`.
-/
theorem cut_bounds {k : ℕ} {u u' : Fin k → ℝ} {l : Fin k} {a b Y : ℝ}
    (h1 : min (-u l) (-u' l) < a) (h2 : b < max (-u l) (-u' l)) (hY : Y ∈ Set.Icc a b)
    (h3 : 2 ≤ |Y + u l|) (h4 : 2 ≤ |Y + u' l|) :
    (2 ≤ Y + u l ∧ Y + u' l ≤ -2) ∨ (2 ≤ Y + u' l ∧ Y + u l ≤ -2) := by
  obtain ⟨hYa, hYb⟩ := hY
  rcases le_total (u l) (u' l) with h | h
  · right
    have e1 : min (-u l) (-u' l) = -u' l := min_eq_right (by linarith)
    have e2 : max (-u l) (-u' l) = -u l := max_eq_left (by linarith)
    rw [e1] at h1
    rw [e2] at h2
    have p1 : 0 < Y + u' l := by linarith
    have p2 : Y + u l < 0 := by linarith
    rw [abs_of_pos p1] at h4
    rw [abs_of_neg p2] at h3
    constructor <;> linarith
  · left
    have e1 : min (-u l) (-u' l) = -u l := min_eq_left (by linarith)
    have e2 : max (-u l) (-u' l) = -u' l := max_eq_right (by linarith)
    rw [e1] at h1
    rw [e2] at h2
    have p1 : 0 < Y + u l := by linarith
    have p2 : Y + u' l < 0 := by linarith
    rw [abs_of_pos p1] at h3
    rw [abs_of_neg p2] at h4
    constructor <;> linarith

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hj`. Establish `h1` using `rho_gt hu l j hj`. Establish `h2` using `rho_gt hu' l j hj`. Apply the tactic sequence `rcases hc with ⟨a, b⟩ | ⟨a, b⟩ <;> linarith`.

Introduce `hj`. Establish `h1` using `rho_lt hu l j hj`. Establish `h2` using `rho_lt hu' l j hj`. Apply the tactic sequence `rcases hc with ⟨a, b⟩ | ⟨a, b⟩ <;> linarith`.
-/
theorem factor_sign {u u' : Fin (k0 + 1) → ℝ} {ρ : Fin k0 → ℝ} (hu : Interlace u ρ) (hu' : Interlace u' ρ)
    (l : Fin (k0 + 1)) {Y : ℝ}
    (hc : (2 ≤ Y + u l ∧ Y + u' l ≤ -2) ∨ (2 ≤ Y + u' l ∧ Y + u l ≤ -2)) (j : Fin k0) :
    (j.val < l.val → 2 < Y + ρ j) ∧ (l.val ≤ j.val → Y + ρ j < -2) := by
  constructor
  · intro hj
    have h1 := rho_gt hu l j hj
    have h2 := rho_gt hu' l j hj
    rcases hc with ⟨a, b⟩ | ⟨a, b⟩ <;> linarith
  · intro hj
    have h1 := rho_lt hu l j hj
    have h2 := rho_lt hu' l j hj
    rcases hc with ⟨a, b⟩ | ⟨a, b⟩ <;> linarith

noncomputable def sgnCut (k0 : ℕ) (l : Fin (k0 + 1)) : ℝ := ∏ j : Fin k0, (if j.val < l.val then 1 else -1)

/- English proof (translation)
Unfold `sgnCut`. Rewrite using `[Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]`. Conclude with `neg_one_pow_eq_or ℝ _`.
-/
theorem sgnCut_eq_one_or_neg_one (l : Fin (k0 + 1)) : sgnCut k0 l = 1 ∨ sgnCut k0 l = -1 := by
  unfold sgnCut
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
  exact neg_one_pow_eq_or ℝ _

/- English proof (translation)
Unfold `sgnCut`. Rewrite using `[← Finset.prod_mul_distrib]`. Apply `Finset.prod_pos` to reduce the goal to its premises. Introduce `j _`. Establish `hf` using `factor_sign hu hu' l hc j`.

Establish `he'` using `abs_le.mp he`. Use `split_ifs with hj`. Use `hf.1 hj` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `hf.2 (by omega)` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem x_sign {u u' : Fin (k0 + 1) → ℝ} {ρ : Fin k0 → ℝ} (hu : Interlace u ρ) (hu' : Interlace u' ρ)
    (l : Fin (k0 + 1)) {Y : ℝ}
    (hc : (2 ≤ Y + u l ∧ Y + u' l ≤ -2) ∨ (2 ≤ Y + u' l ∧ Y + u l ≤ -2)) (e : ℝ) (he : |e| ≤ 1) :
    0 < sgnCut k0 l * ∏ j : Fin k0, (Y + e + ρ j) := by
  unfold sgnCut
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_pos
  intro j _
  have hf := factor_sign hu hu' l hc j
  have he' := abs_le.mp he
  split_ifs with hj
  · have := hf.1 hj
    linarith
  · have := hf.2 (by omega)
    linarith

/- English proof (translation)
Establish `e : (∏ l : Fin k0, ((y : ℂ) + (ρ l : ℂ))) = ((∏ l : Fin k0, (y + ρ l) : ℝ) : ℂ)`. Apply the tactic sequence `push_cast <;> rfl`. Unfold `xPoly`. Rewrite using `[e, Complex.ofReal_re]`.
-/
theorem xPoly_re (ρ : Fin k0 → ℝ) (y : ℝ) : (xPoly ρ (y : ℂ)).re = ∏ j, (y + ρ j) := by
  have e : (∏ l : Fin k0, ((y : ℂ) + (ρ l : ℂ))) = ((∏ l : Fin k0, (y + ρ l) : ℝ) : ℂ) := by
    push_cast <;> rfl
  unfold xPoly
  rw [e, Complex.ofReal_re]

/- English proof (translation)
Establish `e : (∏ i : Fin k, (((y : ℂ) + 1 / 2 + (u i : ℂ)) * ((y : ℂ) + 1 / 2 + (u' i : ℂ)))) = ((∏ i : Fin k, ((y + 1 / 2 + u i) * (y + 1 / 2 + u' i)) : ℝ) : ℂ)`. Apply the tactic sequence `push_cast <;> rfl`. Unfold `qPoly`. Rewrite using `[e, ← Complex.ofReal_neg, ← Complex.ofReal_mul, Complex.ofReal_re]`.
-/
theorem qPoly_re {k : ℕ} (T T' : ℝ) (u u' : Fin k → ℝ) (y : ℝ) :
    (qPoly T T' u u' (y : ℂ)).re = -(T * T') * ∏ i, ((y + 1 / 2 + u i) * (y + 1 / 2 + u' i)) := by
  have e : (∏ i : Fin k, (((y : ℂ) + 1 / 2 + (u i : ℂ)) * ((y : ℂ) + 1 / 2 + (u' i : ℂ)))) =
      ((∏ i : Fin k, ((y + 1 / 2 + u i) * (y + 1 / 2 + u' i)) : ℝ) : ℂ) := by
    push_cast <;> rfl
  unfold qPoly
  rw [e, ← Complex.ofReal_neg, ← Complex.ofReal_mul, Complex.ofReal_re]

/- English proof (translation)
Establish `hTT : 0 < T * T'` using `mul_pos hT hT'`. Establish `hlt` using `l.isLt`. Rewrite using `[← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ l)]`. Establish `hpos : 0 < ∏ i ∈ Finset.univ.erase l, ((Y + 1 / 2 + u i) * (Y + 1 / 2 + u' i))`. Apply `Finset.prod_pos` to reduce the goal to its premises.

Introduce `i hi`. Establish `hil : i ≠ l` using `Finset.ne_of_mem_erase hi`. Establish `hilt` using `i.isLt`. Break down `lt_or_gt_of_ne hil with h | h` into its components or cases. Establish `h' : i.val < l.val` using `h`.

Set `j : Fin k0` to `⟨l.val - 1, by omega⟩`. Establish `hjl : j.val < l.val` using `by show l.val - 1 < l.val`. Use linear arithmetic over natural numbers and integers. Establish `hij : i.val ≤ j.val` using `by show i.val ≤ l.val - 1`. Use linear arithmetic over natural numbers and integers.

Establish `hf` using `(factor_sign hu hu' l hc j).1 hjl`. Establish `a1` using `rho_lt hu i j hij`. Establish `a2` using `rho_lt hu' i j hij`. Apply the tactic sequence `apply mul_pos <;> linarith`. Establish `h' : l.val < i.val` using `h`.

Set `j : Fin k0` to `⟨l.val, by omega⟩`. Establish `hjl : l.val ≤ j.val` using `le_refl _`. Establish `hij : j.val < i.val` using `h'`. Establish `hf` using `(factor_sign hu hu' l hc j).2 hjl`. Establish `a1` using `rho_gt hu i j hij`.

Establish `a2` using `rho_gt hu' i j hij`. Apply the tactic sequence `apply mul_pos_of_neg_of_neg <;> linarith`. Establish `hneg : (Y + 1 / 2 + u l) * (Y + 1 / 2 + u' l) < 0`. Break down `hc with ⟨a, b⟩ | ⟨a, b⟩` into its components or cases. Conclude with `mul_neg_of_pos_of_neg (by linarith) (by linarith)`.

Conclude with `mul_neg_of_neg_of_pos (by linarith) (by linarith)`. Establish `hm` using `mul_neg_of_neg_of_pos hneg hpos`. Establish `hm2` using `mul_neg_of_pos_of_neg hTT hm`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem q_pos {u u' : Fin (k0 + 1) → ℝ} {ρ : Fin k0 → ℝ} (hu : Interlace u ρ) (hu' : Interlace u' ρ)
    (l : Fin (k0 + 1)) {Y T T' : ℝ} (hT : 0 < T) (hT' : 0 < T')
    (hc : (2 ≤ Y + u l ∧ Y + u' l ≤ -2) ∨ (2 ≤ Y + u' l ∧ Y + u l ≤ -2)) :
    0 < -(T * T') * ∏ i : Fin (k0 + 1), ((Y + 1 / 2 + u i) * (Y + 1 / 2 + u' i)) := by
  have hTT : 0 < T * T' := mul_pos hT hT'
  have hlt := l.isLt
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ l)]
  have hpos : 0 < ∏ i ∈ Finset.univ.erase l, ((Y + 1 / 2 + u i) * (Y + 1 / 2 + u' i)) := by
    apply Finset.prod_pos
    intro i hi
    have hil : i ≠ l := Finset.ne_of_mem_erase hi
    have hilt := i.isLt
    rcases lt_or_gt_of_ne hil with h | h
    · have h' : i.val < l.val := h
      let j : Fin k0 := ⟨l.val - 1, by omega⟩
      have hjl : j.val < l.val := by
        show l.val - 1 < l.val
        omega
      have hij : i.val ≤ j.val := by
        show i.val ≤ l.val - 1
        omega
      have hf := (factor_sign hu hu' l hc j).1 hjl
      have a1 := rho_lt hu i j hij
      have a2 := rho_lt hu' i j hij
      apply mul_pos <;> linarith
    · have h' : l.val < i.val := h
      let j : Fin k0 := ⟨l.val, by omega⟩
      have hjl : l.val ≤ j.val := le_refl _
      have hij : j.val < i.val := h'
      have hf := (factor_sign hu hu' l hc j).2 hjl
      have a1 := rho_gt hu i j hij
      have a2 := rho_gt hu' i j hij
      apply mul_pos_of_neg_of_neg <;> linarith
  have hneg : (Y + 1 / 2 + u l) * (Y + 1 / 2 + u' l) < 0 := by
    rcases hc with ⟨a, b⟩ | ⟨a, b⟩
    · exact mul_neg_of_pos_of_neg (by linarith) (by linarith)
    · exact mul_neg_of_neg_of_pos (by linarith) (by linarith)
  have hm := mul_neg_of_neg_of_pos hneg hpos
  have hm2 := mul_neg_of_pos_of_neg hTT hm
  linarith

/- English proof (translation)
Take `⟨ρ0, hρ0, hρ0'⟩` from `hρ`. Take `⟨l, a, b, -, -, hIab, h1, h2, h34⟩` from `hI`. Establish `hc : ∀ Y ∈ I, (2 ≤ Y + u l ∧ Y + u' l ≤ -2) ∨ (2 ≤ Y + u' l ∧ Y + u l ≤ -2)`. Introduce `Y hY`. Establish `hY' : Y ∈ Set.Icc a b`.

Rewrite using `[← hIab]`. Conclude with `hY`. Conclude with `cut_bounds h1 h2 hY' (h34 Y hY).1 (h34 Y hY).2`. Use `⟨⟨sgnCut k0 l, sgnCut_eq_one_or_neg_one l, fun ρ hu hu' Y hY => ?_⟩, fun Y hY => ?_⟩` and prove the remaining obligations. Establish `e1 : ((Y : ℂ) + 1) = ((Y + 1 : ℝ) : ℂ)` using `by simp`.

Establish `e2 : ((Y : ℂ) - 1) = ((Y + -1 : ℝ) : ℂ)` using `by simp [sub_eq_add_neg]`. Rewrite using `[e1, e2, xPoly_re, xPoly_re, xPoly_re]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Use `x_sign hu hu' l (hc Y hY) 0 (by norm_num)` as an intermediate fact. Simplify using `using this`.

Conclude with `x_sign hu hu' l (hc Y hY) 1 (by norm_num)`. Conclude with `x_sign hu hu' l (hc Y hY) (-1) (by norm_num)`. Rewrite using `[qPoly_re]`. Conclude with `q_pos hρ0 hρ0' l hT hT' (hc Y hY)`.
-/
theorem cut_signs (k0 : ℕ) (u u' : Fin (k0 + 1) → ℝ) (T T' : ℝ) (I : Set ℝ) (hT : 0 < T) (hT' : 0 < T')
    (hI : Formalism.MainNotions.S.IsCutS u u' I) (hρ : ∃ ρ : Fin k0 → ℝ, Interlace u ρ ∧ Interlace u' ρ) :
    (∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ ρ : Fin k0 → ℝ, Interlace u ρ → Interlace u' ρ → ∀ Y ∈ I,
      0 < s * (xPoly ρ (Y : ℂ)).re ∧ 0 < s * (xPoly ρ ((Y : ℂ) + 1)).re ∧ 0 < s * (xPoly ρ ((Y : ℂ) - 1)).re) ∧
    ∀ Y ∈ I, 0 < (qPoly T T' u u' (Y : ℂ)).re := by
  obtain ⟨ρ0, hρ0, hρ0'⟩ := hρ
  obtain ⟨l, a, b, -, -, hIab, h1, h2, h34⟩ := hI
  have hc : ∀ Y ∈ I, (2 ≤ Y + u l ∧ Y + u' l ≤ -2) ∨ (2 ≤ Y + u' l ∧ Y + u l ≤ -2) := by
    intro Y hY
    have hY' : Y ∈ Set.Icc a b := by
      rw [← hIab]
      exact hY
    exact cut_bounds h1 h2 hY' (h34 Y hY).1 (h34 Y hY).2
  refine ⟨⟨sgnCut k0 l, sgnCut_eq_one_or_neg_one l, fun ρ hu hu' Y hY => ?_⟩, fun Y hY => ?_⟩
  · have e1 : ((Y : ℂ) + 1) = ((Y + 1 : ℝ) : ℂ) := by simp
    have e2 : ((Y : ℂ) - 1) = ((Y + -1 : ℝ) : ℂ) := by simp [sub_eq_add_neg]
    rw [e1, e2, xPoly_re, xPoly_re, xPoly_re]
    refine ⟨?_, ?_, ?_⟩
    · have := x_sign hu hu' l (hc Y hY) 0 (by norm_num)
      simpa using this
    · exact x_sign hu hu' l (hc Y hY) 1 (by norm_num)
    · exact x_sign hu hu' l (hc Y hY) (-1) (by norm_num)
  · rw [qPoly_re]
    exact q_pos hρ0 hρ0' l hT hT' (hc Y hY)

/- English proof (translation)
Unfold `sgnCut`. Establish `h` using `Fin.prod_univ_eq_prod_range (fun i => if i < l.val then (1 : ℝ) else -1) k0`. Use `beta_reduce at h`. Rewrite using `[h, Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]`. Establish `hs : (Finset.range k0).filter (fun i => ¬ i < l.val) = Finset.Ico l.val k0`.

Use extensionality with `i`. Simplify using `only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hs, Nat.card_Ico]`.
-/
theorem sgnCut_eq_neg_one_pow (l : Fin (k0 + 1)) : sgnCut k0 l = (-1) ^ (k0 - l.val) := by
  unfold sgnCut
  have h := Fin.prod_univ_eq_prod_range (fun i => if i < l.val then (1 : ℝ) else -1) k0
  beta_reduce at h
  rw [h, Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
  have hs : (Finset.range k0).filter (fun i => ¬ i < l.val) = Finset.Ico l.val k0 := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hs, Nat.card_Ico]

/- English proof (translation)
Take `⟨l, a, b, -, -, hIab, h1, h2, h34⟩` from `hI`. Establish `hex : ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ ρ : Fin k0 → ℝ, Interlace u ρ → Interlace u' ρ → ∀ Y ∈ I, 0 < s * (xPoly ρ (Y : ℂ)).re`. Use `⟨sgnCut k0 l, sgnCut_eq_one_or_neg_one l, fun ρ hu hu' Y hY => ?_⟩` and prove the remaining obligations. Establish `hY' : Y ∈ Set.Icc a b`. Rewrite using `[← hIab]`.

Conclude with `hY`. Rewrite using `[xPoly_re]`. Simplify using `using x_sign hu hu' l (cut_bounds h1 h2 hY' (h34 Y hY).1 (h34 Y hY).2) 0 (by norm_num)`. Establish `hs : sCut u u' I = Classical.choose hex`. Unfold `sCut`.

Conclude with `dif_pos hex`. Rewrite using `[hs]`. Conclude with `Classical.choose_spec hex`.
-/
theorem sCut_spec (u u' : Fin (k0 + 1) → ℝ) (I : Set ℝ) (hI : Formalism.MainNotions.S.IsCutS u u' I) :
    (sCut u u' I = 1 ∨ sCut u u' I = -1) ∧ ∀ ρ : Fin k0 → ℝ, Interlace u ρ → Interlace u' ρ →
      ∀ Y ∈ I, 0 < sCut u u' I * (xPoly ρ (Y : ℂ)).re := by
  obtain ⟨l, a, b, -, -, hIab, h1, h2, h34⟩ := hI
  have hex : ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ ρ : Fin k0 → ℝ, Interlace u ρ → Interlace u' ρ →
      ∀ Y ∈ I, 0 < s * (xPoly ρ (Y : ℂ)).re := by
    refine ⟨sgnCut k0 l, sgnCut_eq_one_or_neg_one l, fun ρ hu hu' Y hY => ?_⟩
    have hY' : Y ∈ Set.Icc a b := by
      rw [← hIab]
      exact hY
    rw [xPoly_re]
    simpa using x_sign hu hu' l (cut_bounds h1 h2 hY' (h34 Y hY).1 (h34 Y hY).2) 0 (by norm_num)
  have hs : sCut u u' I = Classical.choose hex := by
    unfold sCut
    exact dif_pos hex
  rw [hs]
  exact Classical.choose_spec hex

end Cut

/- English proof (translation)
Unfold `Formalism.MainNotions.S.UnitaryLevelOperators.stA_signs`. Conclude with `fun k0 u u' T T' I hT hT' hI hρ => cut_signs k0 u u' T T' I hT hT' hI hρ`.
-/
theorem stA_signs_of_core : Formalism.MainNotions.S.UnitaryLevelOperators.stA_signs := by
  unfold Formalism.MainNotions.S.UnitaryLevelOperators.stA_signs
  exact fun k0 u u' T T' I hT hT' hI hρ => cut_signs k0 u u' T T' I hT hT' hI hρ

end Formalism.MainNotions.InterlacingSignCuts

end PartA3c

section PartA4

open Matrix
open scoped ContDiff

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts

open Formalism.QuantumDeterminants Formalism.YangianSpanCharacter.T

variable {m : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def Rep (M : Op m E) (M' : Module.End ℂ (WSm m E)) : Prop :=
  ∀ f : WSm m E, M (f : (Fin m → ℂ) → E) = ((M' f : WSm m E) : (Fin m → ℂ) → E)

/- English proof (translation)
Introduce `a b f`. Simplify using `only [opMatMul, Matrix.mul_apply, LinearMap.sum_apply, Module.End.mul_apply, Submodule.coe_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[hN c b f, hM a c]`.
-/
theorem rep_opMatMul {M N : Matrix (Fin 2) (Fin 2) (Op m E)}
    {M' N' : Matrix (Fin 2) (Fin 2) (Module.End ℂ (WSm m E))}
    (hM : ∀ a b, Rep (M a b) (M' a b)) (hN : ∀ a b, Rep (N a b) (N' a b)) :
    ∀ a b, Rep (opMatMul M N a b) ((M' * N') a b) := by
  intro a b f
  simp only [opMatMul, Matrix.mul_apply, LinearMap.sum_apply, Module.End.mul_apply, Submodule.coe_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [hN c b f, hM a c]

/- English proof (translation)
Introduce `a b` and use `hM b a`.
-/
theorem rep_transpose {M : Matrix (Fin 2) (Fin 2) (Op m E)}
    {M' : Matrix (Fin 2) (Fin 2) (Module.End ℂ (WSm m E))} (hM : ∀ a b, Rep (M a b) (M' a b)) :
    ∀ a b, Rep (M.transpose a b) (M'.transpose a b) := fun a b => hM b a

/- English proof (translation)
Introduce `a b f`. Apply the tactic sequence `fin_cases a <;> fin_cases b <;> rfl`.
-/
theorem rep_Tmat (l : Fin m) (Y : ℂ) :
    ∀ a b, Rep (Tmat (E := E) l Y a b) (Tm Y (pEnd (E := E) l) (cEnd l) (ciEnd l) a b) := by
  intro a b f
  fin_cases a <;> fin_cases b <;> rfl

/- English proof (translation)
Introduce `a b f`. Apply the tactic sequence `fin_cases a <;> fin_cases b`. Use `show Y • (f : (Fin m → ℂ) → E) - pbOp l f = Y • (f : (Fin m → ℂ) → E) + -(pbOp l f)`. Rewrite using `[sub_eq_add_neg]`. Both sides reduce to the same expression.

Both sides reduce to the same expression. Both sides reduce to the same expression.
-/
theorem rep_TmatV (l : Fin m) (Y : ℂ) :
    ∀ a b, Rep (TmatV (E := E) l Y a b) (Tm Y (-pbEnd (E := E) l) (cbEnd l) (cbiEnd l) a b) := by
  intro a b f
  fin_cases a <;> fin_cases b
  · show Y • (f : (Fin m → ℂ) → E) - pbOp l f = Y • (f : (Fin m → ℂ) → E) + -(pbOp l f)
    rw [sub_eq_add_neg]
  · rfl
  · rfl
  · rfl

/- English proof (translation)
Introduce `a b f`. Apply the tactic sequence `fin_cases a <;> fin_cases b`. Use `show Y • (f : (Fin m → ℂ) → E) - pbOp l f = Y • (f : (Fin m → ℂ) → E) + -(pbOp l f)`. Rewrite using `[sub_eq_add_neg]`. Both sides reduce to the same expression.

Both sides reduce to the same expression. Both sides reduce to the same expression.
-/
theorem rep_TmatStar (l : Fin m) (Y : ℂ) :
    ∀ a b, Rep (TmatStar (E := E) l Y a b) ((Tm Y (-pbEnd (E := E) l) (cbEnd l) (cbiEnd l)).transpose a b) := by
  intro a b f
  fin_cases a <;> fin_cases b
  · show Y • (f : (Fin m → ℂ) → E) - pbOp l f = Y • (f : (Fin m → ℂ) → E) + -(pbOp l f)
    rw [sub_eq_add_neg]
  · rfl
  · rfl
  · rfl

/- English proof (translation)
Introduce `a b f`. Apply the tactic sequence `fin_cases a <;> fin_cases b <;> rfl`.
-/
theorem rep_Jop : ∀ a b, Rep (Formalism.MainNotions.S.UnitaryLevelOperators.Jop (m := m) (E := E) a b) (Formalism.YangianSpanCharacter.T.J (Module.End ℂ (WSm m E)) a b) := by
  intro a b f
  fin_cases a <;> fin_cases b <;> rfl

/- English proof (translation)
Introduce `p q f`. Simplify using `only [Formalism.MainNotions.S.UnitaryLevelOperators.op4Mul, Matrix.mul_apply, LinearMap.sum_apply, Module.End.mul_apply, Submodule.coe_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[hN c q f, hM p c]`.
-/
theorem rep_op4Mul {M N : Formalism.MainNotions.S.UnitaryLevelOperators.Op4 m E}
    {M' N' : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) (Module.End ℂ (WSm m E))}
    (hM : ∀ p q, Rep (M p q) (M' p q)) (hN : ∀ p q, Rep (N p q) (N' p q)) :
    ∀ p q, Rep (Formalism.MainNotions.S.UnitaryLevelOperators.op4Mul M N p q) ((M' * N') p q) := by
  intro p q f
  simp only [Formalism.MainNotions.S.UnitaryLevelOperators.op4Mul, Matrix.mul_apply, LinearMap.sum_apply, Module.End.mul_apply, Submodule.coe_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [hN c q f, hM p c]

/- English proof (translation)
Introduce `p q f`. Simplify using `only [Formalism.MainNotions.S.UnitaryLevelOperators.tens1, T1, Matrix.of_apply]`. Use `split_ifs`. Conclude with `rep_Tmat l Y _ _ f`. Both sides reduce to the same expression.
-/
theorem rep_tens1 (l : Fin m) (Y : ℂ) :
    ∀ p q, Rep (Formalism.MainNotions.S.UnitaryLevelOperators.tens1 (Tmat (E := E) l Y) p q) (T1 Y (pEnd (E := E) l) (cEnd l) (ciEnd l) p q) := by
  intro p q f
  simp only [Formalism.MainNotions.S.UnitaryLevelOperators.tens1, T1, Matrix.of_apply]
  split_ifs
  · exact rep_Tmat l Y _ _ f
  · rfl

/- English proof (translation)
Introduce `p q f`. Simplify using `only [Formalism.MainNotions.S.UnitaryLevelOperators.tens2, T2, Matrix.of_apply]`. Use `split_ifs`. Conclude with `rep_Tmat l Y _ _ f`. Both sides reduce to the same expression.
-/
theorem rep_tens2 (l : Fin m) (Y : ℂ) :
    ∀ p q, Rep (Formalism.MainNotions.S.UnitaryLevelOperators.tens2 (Tmat (E := E) l Y) p q) (T2 Y (pEnd (E := E) l) (cEnd l) (ciEnd l) p q) := by
  intro p q f
  simp only [Formalism.MainNotions.S.UnitaryLevelOperators.tens2, T2, Matrix.of_apply]
  split_ifs
  · exact rep_Tmat l Y _ _ f
  · rfl

/- English proof (translation)
Introduce `p q f`. Simplify using `only [Formalism.MainNotions.S.UnitaryLevelOperators.RhOp, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, Pf, Matrix.of_apply]`. Apply the tactic sequence `split_ifs <;>`. Apply the tactic sequence `simp only [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.neg_apply, Submodule.coe_neg, Module.End.one_apply, LinearMap.zero_apply, Submodule.coe_smul, Submodule.coe_sub, Submodule.coe_zero, smul_zero, mul_one, mul_zero, sub_zero, zero_sub] <;> module`.
-/
theorem rep_Rh (D : ℂ) : ∀ p q, Rep (Formalism.MainNotions.S.UnitaryLevelOperators.RhOp (m := m) (E := E) D p q)
    (((D - 1)⁻¹ • (D • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) (Module.End ℂ (WSm m E))) -
      Pf (Module.End ℂ (WSm m E)))) p q) := by
  intro p q f
  simp only [Formalism.MainNotions.S.UnitaryLevelOperators.RhOp, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, Pf, Matrix.of_apply]
  split_ifs <;>
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.neg_apply, Submodule.coe_neg, Module.End.one_apply,
      LinearMap.zero_apply, Submodule.coe_smul, Submodule.coe_sub, Submodule.coe_zero, smul_zero, mul_one, mul_zero,
      sub_zero, zero_sub] <;> module

/- English proof (translation)
Introduce `m E _ _ l f hf`. Use `⟨fun Y a b => ⟨?_, ?_⟩, fun Y Y' _ p q => ?_⟩` and prove the remaining obligations. Establish `h` using `rep_opMatMul (rep_opMatMul (rep_transpose (rep_Tmat (E := E) l (Y + 1))) rep_Jop) (rep_Tmat l Y) a b ⟨f, hf⟩`. Rewrite `h` using `[Formalism.YangianSpanCharacter.Final.B_TJTReal m E l Y]`. Conclude with `h.trans (rep_Jop a b ⟨f, hf⟩).symm`.

Establish `h` using `rep_opMatMul (rep_opMatMul (rep_TmatV (E := E) l (Y + 1)) rep_Jop) (rep_TmatStar l Y) a b ⟨f, hf⟩`. Rewrite `h` using `[Formalism.YangianSpanCharacter.Final.B_TvJTsReal m E l Y]`. Conclude with `h.trans (rep_Jop a b ⟨f, hf⟩).symm`. Establish `h1` using `rep_op4Mul (rep_op4Mul (rep_Rh (m := m) (E := E) (Y' - Y)) (rep_tens1 l Y')) (rep_tens2 l Y) p q ⟨f, hf⟩`. Establish `h2` using `rep_op4Mul (rep_op4Mul (rep_tens2 (E := E) l Y) (rep_tens1 l Y')) (rep_Rh (Y' - Y)) p q ⟨f, hf⟩`.

Rewrite `h1` using `[Matrix.smul_mul, Matrix.smul_mul, Formalism.YangianSpanCharacter.Final.B_RTTReal m E l Y Y', ← Matrix.mul_smul]`. Conclude with `h1.trans h2.symm`.
-/
theorem stLetters_of_core : Formalism.MainNotions.S.UnitaryLevelOperators.stLetters := by
  intro m E _ _ l f hf
  refine ⟨fun Y a b => ⟨?_, ?_⟩, fun Y Y' _ p q => ?_⟩
  · have h := rep_opMatMul (rep_opMatMul (rep_transpose (rep_Tmat (E := E) l (Y + 1))) rep_Jop) (rep_Tmat l Y) a b ⟨f, hf⟩
    rw [Formalism.YangianSpanCharacter.Final.B_TJTReal m E l Y] at h
    exact h.trans (rep_Jop a b ⟨f, hf⟩).symm
  · have h := rep_opMatMul (rep_opMatMul (rep_TmatV (E := E) l (Y + 1)) rep_Jop) (rep_TmatStar l Y) a b ⟨f, hf⟩
    rw [Formalism.YangianSpanCharacter.Final.B_TvJTsReal m E l Y] at h
    exact h.trans (rep_Jop a b ⟨f, hf⟩).symm
  · have h1 := rep_op4Mul (rep_op4Mul (rep_Rh (m := m) (E := E) (Y' - Y)) (rep_tens1 l Y')) (rep_tens2 l Y) p q ⟨f, hf⟩
    have h2 := rep_op4Mul (rep_op4Mul (rep_tens2 (E := E) l Y) (rep_tens1 l Y')) (rep_Rh (Y' - Y)) p q ⟨f, hf⟩
    rw [Matrix.smul_mul, Matrix.smul_mul, Formalism.YangianSpanCharacter.Final.B_RTTReal m E l Y Y', ← Matrix.mul_smul] at h1
    exact h1.trans h2.symm

section PlaneWaves

open Formalism.QuantumDeterminants.WirtingerDerivatives

variable {m : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/- English proof (translation)
Establish `h1 : HasFDerivAt (fun y : Fin m → ℂ => y l) (ContinuousLinearMap.proj (R` using `ℝ) l) x := hasFDerivAt_apply l x`. Establish `h2` using `h1.const_mul s`. Establish `h3` using `(Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp x h2`. Establish `h4` using `h2.sub h3`. Establish `h5` using `(h4.cexp).const_mul c`.

Use `⟨_, h5, fun v => ?_⟩` and prove the remaining obligations. Simplify using `[Formalism.MainNotions.S.UnitaryLevelOperators.fsFun]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hasFDerivAt_fs (s c : ℂ) (l : Fin m) (x : Fin m → ℂ) :
    ∃ L : (Fin m → ℂ) →L[ℝ] ℂ, HasFDerivAt (fun y : Fin m → ℂ => c * Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l y) L x ∧
      ∀ v, L v = c * Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l x * (s * v l - star (s * v l)) := by
  have h1 : HasFDerivAt (fun y : Fin m → ℂ => y l) (ContinuousLinearMap.proj (R := ℝ) l) x := hasFDerivAt_apply l x
  have h2 := h1.const_mul s
  have h3 := (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp x h2
  have h4 := h2.sub h3
  have h5 := (h4.cexp).const_mul c
  refine ⟨_, h5, fun v => ?_⟩
  simp [Formalism.MainNotions.S.UnitaryLevelOperators.fsFun]
  ring

/- English proof (translation)
Take `⟨L, hL, hLv⟩` from `hasFDerivAt_fs s c l x`. Establish `hgd : DifferentiableAt ℝ g x` using `diff_of_reg (reg_of_mem hg x hx)`. Establish `hI : star Complex.I = -Complex.I` using `Complex.conj_I`. Establish `k1 : Wc (Pi.single l 1) (Pi.single l Complex.I) (-Complex.I) L = c * s * Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l x`. Rewrite using `[Wc_apply, hLv, hLv]`.

Simplify using `only [Pi.single_eq_same, smul_eq_mul, mul_one, star_mul', hI]`. Take the linear combination `(-(c * Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l x * s) / 2 - (c * Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l x * star s) / 2) * Complex.I_sq`. Establish `k2 : Wc (Pi.single l 1) (Pi.single l Complex.I) Complex.I L = -(c * star s * Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l x)`. Rewrite using `[Wc_apply, hLv, hLv]`. Simplify using `only [Pi.single_eq_same, smul_eq_mul, mul_one, star_mul', hI]`.

Take the linear combination `((c * Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l x * s) / 2 + (c * Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l x * star s) / 2) * Complex.I_sq`. Prove the components needed by the constructor for the conclusion. Rewrite using `[wirt_eq l g, wirt_eq, Wc_smul hL.differentiableAt hgd, hL.fderiv, k1]`. Rewrite using `[wirtBar_eq l g, wirtBar_eq, Wc_smul hL.differentiableAt hgd, hL.fderiv, k2]`.
-/
theorem wirt_fs (s c : ℂ) (l : Fin m) {g : (Fin m → ℂ) → E} (hg : g ∈ WSm m E) {x : Fin m → ℂ} (hx : x ∈ OmX m) :
    wirt l (fun y => (c * Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l y) • g y) x =
        (c * s * Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l x) • g x + (c * Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l x) • wirt l g x ∧
      wirtBar l (fun y => (c * Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l y) • g y) x =
        (-(c * star s * Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l x)) • g x + (c * Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l x) • wirtBar l g x := by
  obtain ⟨L, hL, hLv⟩ := hasFDerivAt_fs s c l x
  have hgd : DifferentiableAt ℝ g x := diff_of_reg (reg_of_mem hg x hx)
  have hI : star Complex.I = -Complex.I := Complex.conj_I
  have k1 : Wc (Pi.single l 1) (Pi.single l Complex.I) (-Complex.I) L = c * s * Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l x := by
    rw [Wc_apply, hLv, hLv]
    simp only [Pi.single_eq_same, smul_eq_mul, mul_one, star_mul', hI]
    linear_combination (-(c * Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l x * s) / 2 - (c * Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l x * star s) / 2) * Complex.I_sq
  have k2 : Wc (Pi.single l 1) (Pi.single l Complex.I) Complex.I L = -(c * star s * Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l x) := by
    rw [Wc_apply, hLv, hLv]
    simp only [Pi.single_eq_same, smul_eq_mul, mul_one, star_mul', hI]
    linear_combination ((c * Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l x * s) / 2 + (c * Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l x * star s) / 2) * Complex.I_sq
  constructor
  · rw [wirt_eq l g, wirt_eq, Wc_smul hL.differentiableAt hgd, hL.fderiv, k1]
  · rw [wirtBar_eq l g, wirtBar_eq, Wc_smul hL.differentiableAt hgd, hL.fderiv, k2]

/- English proof (translation)
Apply `Matrix.inv_eq_right_inv` to reduce the goal to its premises. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Formalism.MainNotions.S.UnitaryLevelOperators.Umat, Matrix.mul_apply, Fin.sum_univ_two]`.
-/
theorem Umat_inv (s : ℂ) : (Formalism.MainNotions.S.UnitaryLevelOperators.Umat s)⁻¹ = !![1, 0; s, 1] := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Formalism.MainNotions.S.UnitaryLevelOperators.Umat, Matrix.mul_apply, Fin.sum_univ_two]

/- English proof (translation)
Distinguish the cases in `hx : x ∈ OmX m`. Simplify using `only [pOp, hx, if_true, (wirt_fs s c l hg hx).1] module`. Simplify using `[pOp, hx, hg.2 x hx]`.
-/
theorem pOp_fs (s c : ℂ) (l : Fin m) {g : (Fin m → ℂ) → E} (hg : g ∈ WSm m E) (x : Fin m → ℂ) :
    pOp l (fun y => (c * Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l y) • g y) x =
      (c * s * x l * Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l x) • g x + (c * Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l x) • pOp l g x := by
  by_cases hx : x ∈ OmX m
  · simp only [pOp, hx, if_true, (wirt_fs s c l hg hx).1]
    module
  · simp [pOp, hx, hg.2 x hx]

/- English proof (translation)
Distinguish the cases in `hx : x ∈ OmX m`. Simplify using `only [pbOp, hx, if_true, (wirt_fs s c l hg hx).2] module`. Simplify using `[pbOp, hx, hg.2 x hx]`.
-/
theorem pbOp_fs (s c : ℂ) (l : Fin m) {g : (Fin m → ℂ) → E} (hg : g ∈ WSm m E) (x : Fin m → ℂ) :
    pbOp l (fun y => (c * Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l y) • g y) x =
      (-(c * star s * star (x l) * Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l x)) • g x + (c * Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l x) • pbOp l g x := by
  by_cases hx : x ∈ OmX m
  · simp only [pbOp, hx, if_true, (wirt_fs s c l hg hx).2]
    module
  · simp [pbOp, hx, hg.2 x hx]

/- English proof (translation)
Use `⟨fun m E _ _ l s Y f hf a b => ⟨?_, ?_⟩, fun s => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x`. Rewrite using `[Umat_inv]`. Establish `h00 : opMatMul (Tmat (E` using `E) l Y) (Formalism.MainNotions.S.UnitaryLevelOperators.scalMat (Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l) !![1, 0; s, 1]) 0 0 f x = Formalism.MainNotions.S.UnitaryLevelOperators.mulAfter (Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l) (Tmat l Y) 0 0 f x : …`. Rewrite using `[Fin.sum_univ_two]`.

Use `show Y • (((1 : ℂ) * Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l x) • f x) + pOp l (fun y => ((1 : ℂ) * Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l y) • f y) x + -(x l • ((s * Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l x) • f x)) = Formalism.M …`. Rewrite using `[pOp_fs s 1 l hf x]`. Use `module`. Establish `h01 : opMatMul (Tmat (E` using `E) l Y) (Formalism.MainNotions.S.UnitaryLevelOperators.scalMat (Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l) !![1, 0; s, 1]) 0 1 f x = Formalism.MainNotions.S.UnitaryLevelOperators.mulAfter (Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l) (Tmat l Y) 0 1 f x : …`. Rewrite using `[Fin.sum_univ_two]`.

Use `show Y • (((0 : ℂ) * Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l x) • f x) + pOp l (fun y => ((0 : ℂ) * Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l y) • f y) x + -(x l • (((1 : ℂ) * Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l x) • f x)) = Forma …`. Rewrite using `[pOp_fs s 0 l hf x]`. Use `module`. Establish `h10 : opMatMul (Tmat (E` using `E) l Y) (Formalism.MainNotions.S.UnitaryLevelOperators.scalMat (Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l) !![1, 0; s, 1]) 1 0 f x = Formalism.MainNotions.S.UnitaryLevelOperators.mulAfter (Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l) (Tmat l Y) 1 0 f x : …`. Rewrite using `[Fin.sum_univ_two]`.

Use `show (x l)⁻¹ • (((1 : ℂ) * Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l x) • f x) + 0 = Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l x • ((x l)⁻¹ • f x)`. Use `module`. Establish `h11 : opMatMul (Tmat (E` using `E) l Y) (Formalism.MainNotions.S.UnitaryLevelOperators.scalMat (Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l) !![1, 0; s, 1]) 1 1 f x = Formalism.MainNotions.S.UnitaryLevelOperators.mulAfter (Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l) (Tmat l Y) 1 1 f x : …`. Rewrite using `[Fin.sum_univ_two]`. Use `show (x l)⁻¹ • (((0 : ℂ) * Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l x) • f x) + 0 = Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l x • (0 : E)`.

Use `module`. Apply the tactic sequence `fin_cases a <;> fin_cases b`. Conclude with `h00`. Conclude with `h01`. Conclude with `h10`.

Conclude with `h11`. Use function extensionality and compare the values at `x`. Rewrite using `[Umat_inv]`. Establish `h00 : opMatMul (TmatV (E` using `E) l Y) (Formalism.MainNotions.S.UnitaryLevelOperators.scalMat (Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l) !![1, 0; star s, 1]) 0 0 f x = Formalism.MainNotions.S.UnitaryLevelOperators.mulAfter (Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l) (TmatV l Y) 0 0 …`. Rewrite using `[Fin.sum_univ_two]`.

Use `show Y • (((1 : ℂ) * Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l x) • f x) - pbOp l (fun y => ((1 : ℂ) * Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l y) • f y) x + -(star (x l) • ((star s * Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l x) • f x)) …`. Rewrite using `[pbOp_fs s 1 l hf x]`. Use `module`. Establish `h01 : opMatMul (TmatV (E` using `E) l Y) (Formalism.MainNotions.S.UnitaryLevelOperators.scalMat (Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l) !![1, 0; star s, 1]) 0 1 f x = Formalism.MainNotions.S.UnitaryLevelOperators.mulAfter (Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l) (TmatV l Y) 0 1 …`. Rewrite using `[Fin.sum_univ_two]`.

Use `show Y • (((0 : ℂ) * Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l x) • f x) - pbOp l (fun y => ((0 : ℂ) * Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l y) • f y) x + -(star (x l) • (((1 : ℂ) * Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l x) • f x)) …`. Rewrite using `[pbOp_fs s 0 l hf x]`. Use `module`. Establish `h10 : opMatMul (TmatV (E` using `E) l Y) (Formalism.MainNotions.S.UnitaryLevelOperators.scalMat (Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l) !![1, 0; star s, 1]) 1 0 f x = Formalism.MainNotions.S.UnitaryLevelOperators.mulAfter (Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l) (TmatV l Y) 1 0 …`. Rewrite using `[Fin.sum_univ_two]`.

Use `show (star (x l))⁻¹ • (((1 : ℂ) * Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l x) • f x) + 0 = Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l x • ((star (x l))⁻¹ • f x)`. Use `module`. Establish `h11 : opMatMul (TmatV (E` using `E) l Y) (Formalism.MainNotions.S.UnitaryLevelOperators.scalMat (Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l) !![1, 0; star s, 1]) 1 1 f x = Formalism.MainNotions.S.UnitaryLevelOperators.mulAfter (Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l) (TmatV l Y) 1 1 …`. Rewrite using `[Fin.sum_univ_two]`. Use `show (star (x l))⁻¹ • (((0 : ℂ) * Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l x) • f x) + 0 = Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l x • (0 : E)`.

Use `module`. Apply the tactic sequence `fin_cases a <;> fin_cases b`. Conclude with `h00`. Conclude with `h01`. Conclude with `h10`.

Conclude with `h11`. Conclude with `Formalism.YangianSpanCharacter.Final.T_UJU ℂ ℂ s`.
-/
theorem stWaveLetters_of_core : Formalism.MainNotions.S.UnitaryLevelOperators.stWaveLetters := by
  refine ⟨fun m E _ _ l s Y f hf a b => ⟨?_, ?_⟩, fun s => ?_⟩
  · funext x
    rw [Umat_inv]
    have h00 : opMatMul (Tmat (E := E) l Y) (Formalism.MainNotions.S.UnitaryLevelOperators.scalMat (Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l) !![1, 0; s, 1]) 0 0 f x =
        Formalism.MainNotions.S.UnitaryLevelOperators.mulAfter (Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l) (Tmat l Y) 0 0 f x := by
      show (∑ c : Fin 2, Tmat (E := E) l Y 0 c (Formalism.MainNotions.S.UnitaryLevelOperators.scalMat (Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l) !![1, 0; s, 1] c 0 f)) x = _
      rw [Fin.sum_univ_two]
      show Y • (((1 : ℂ) * Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l x) • f x) + pOp l (fun y => ((1 : ℂ) * Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l y) • f y) x +
        -(x l • ((s * Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l x) • f x)) = Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l x • (Y • f x + pOp l f x)
      rw [pOp_fs s 1 l hf x]; module
    have h01 : opMatMul (Tmat (E := E) l Y) (Formalism.MainNotions.S.UnitaryLevelOperators.scalMat (Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l) !![1, 0; s, 1]) 0 1 f x =
        Formalism.MainNotions.S.UnitaryLevelOperators.mulAfter (Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l) (Tmat l Y) 0 1 f x := by
      show (∑ c : Fin 2, Tmat (E := E) l Y 0 c (Formalism.MainNotions.S.UnitaryLevelOperators.scalMat (Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l) !![1, 0; s, 1] c 1 f)) x = _
      rw [Fin.sum_univ_two]
      show Y • (((0 : ℂ) * Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l x) • f x) + pOp l (fun y => ((0 : ℂ) * Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l y) • f y) x +
        -(x l • (((1 : ℂ) * Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l x) • f x)) = Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l x • (-(x l • f x))
      rw [pOp_fs s 0 l hf x]; module
    have h10 : opMatMul (Tmat (E := E) l Y) (Formalism.MainNotions.S.UnitaryLevelOperators.scalMat (Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l) !![1, 0; s, 1]) 1 0 f x =
        Formalism.MainNotions.S.UnitaryLevelOperators.mulAfter (Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l) (Tmat l Y) 1 0 f x := by
      show (∑ c : Fin 2, Tmat (E := E) l Y 1 c (Formalism.MainNotions.S.UnitaryLevelOperators.scalMat (Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l) !![1, 0; s, 1] c 0 f)) x = _
      rw [Fin.sum_univ_two]
      show (x l)⁻¹ • (((1 : ℂ) * Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l x) • f x) + 0 = Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l x • ((x l)⁻¹ • f x)
      module
    have h11 : opMatMul (Tmat (E := E) l Y) (Formalism.MainNotions.S.UnitaryLevelOperators.scalMat (Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l) !![1, 0; s, 1]) 1 1 f x =
        Formalism.MainNotions.S.UnitaryLevelOperators.mulAfter (Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l) (Tmat l Y) 1 1 f x := by
      show (∑ c : Fin 2, Tmat (E := E) l Y 1 c (Formalism.MainNotions.S.UnitaryLevelOperators.scalMat (Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l) !![1, 0; s, 1] c 1 f)) x = _
      rw [Fin.sum_univ_two]
      show (x l)⁻¹ • (((0 : ℂ) * Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l x) • f x) + 0 = Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l x • (0 : E)
      module
    fin_cases a <;> fin_cases b
    · exact h00
    · exact h01
    · exact h10
    · exact h11
  · funext x
    rw [Umat_inv]
    have h00 : opMatMul (TmatV (E := E) l Y) (Formalism.MainNotions.S.UnitaryLevelOperators.scalMat (Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l) !![1, 0; star s, 1]) 0 0 f x =
        Formalism.MainNotions.S.UnitaryLevelOperators.mulAfter (Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l) (TmatV l Y) 0 0 f x := by
      show (∑ c : Fin 2, TmatV (E := E) l Y 0 c (Formalism.MainNotions.S.UnitaryLevelOperators.scalMat (Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l) !![1, 0; star s, 1] c 0 f)) x = _
      rw [Fin.sum_univ_two]
      show Y • (((1 : ℂ) * Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l x) • f x) - pbOp l (fun y => ((1 : ℂ) * Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l y) • f y) x +
        -(star (x l) • ((star s * Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l x) • f x)) = Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l x • (Y • f x - pbOp l f x)
      rw [pbOp_fs s 1 l hf x]; module
    have h01 : opMatMul (TmatV (E := E) l Y) (Formalism.MainNotions.S.UnitaryLevelOperators.scalMat (Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l) !![1, 0; star s, 1]) 0 1 f x =
        Formalism.MainNotions.S.UnitaryLevelOperators.mulAfter (Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l) (TmatV l Y) 0 1 f x := by
      show (∑ c : Fin 2, TmatV (E := E) l Y 0 c (Formalism.MainNotions.S.UnitaryLevelOperators.scalMat (Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l) !![1, 0; star s, 1] c 1 f)) x = _
      rw [Fin.sum_univ_two]
      show Y • (((0 : ℂ) * Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l x) • f x) - pbOp l (fun y => ((0 : ℂ) * Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l y) • f y) x +
        -(star (x l) • (((1 : ℂ) * Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l x) • f x)) = Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l x • (-(star (x l) • f x))
      rw [pbOp_fs s 0 l hf x]; module
    have h10 : opMatMul (TmatV (E := E) l Y) (Formalism.MainNotions.S.UnitaryLevelOperators.scalMat (Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l) !![1, 0; star s, 1]) 1 0 f x =
        Formalism.MainNotions.S.UnitaryLevelOperators.mulAfter (Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l) (TmatV l Y) 1 0 f x := by
      show (∑ c : Fin 2, TmatV (E := E) l Y 1 c (Formalism.MainNotions.S.UnitaryLevelOperators.scalMat (Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l) !![1, 0; star s, 1] c 0 f)) x = _
      rw [Fin.sum_univ_two]
      show (star (x l))⁻¹ • (((1 : ℂ) * Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l x) • f x) + 0 = Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l x • ((star (x l))⁻¹ • f x)
      module
    have h11 : opMatMul (TmatV (E := E) l Y) (Formalism.MainNotions.S.UnitaryLevelOperators.scalMat (Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l) !![1, 0; star s, 1]) 1 1 f x =
        Formalism.MainNotions.S.UnitaryLevelOperators.mulAfter (Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l) (TmatV l Y) 1 1 f x := by
      show (∑ c : Fin 2, TmatV (E := E) l Y 1 c (Formalism.MainNotions.S.UnitaryLevelOperators.scalMat (Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l) !![1, 0; star s, 1] c 1 f)) x = _
      rw [Fin.sum_univ_two]
      show (star (x l))⁻¹ • (((0 : ℂ) * Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l x) • f x) + 0 = Formalism.MainNotions.S.UnitaryLevelOperators.fsFun s l x • (0 : E)
      module
    fin_cases a <;> fin_cases b
    · exact h00
    · exact h01
    · exact h10
    · exact h11
  · exact Formalism.YangianSpanCharacter.Final.T_UJU ℂ ℂ s

end PlaneWaves

end Formalism.MainNotions.InterlacingSignCuts

end

end PartA4

section PartA9

open Formalism.QuantumDeterminants Matrix
open scoped ContDiff

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/- English proof (translation)
Establish `h1` using `(hasDerivAt_inv h0).comp_hasFDerivAt x hd.hasFDerivAt`. Establish `h2` using `Complex.ofRealCLM.hasFDerivAt.comp x h1`. Establish `e : (fun y => ((h y : ℂ))⁻¹) = (⇑Complex.ofRealCLM ∘ (Inv.inv ∘ h))`. Use function extensionality and compare the values at `y`. Simplify using the standard rewrite rules.

Rewrite using `[e]`. Conclude with `h2`.
-/
theorem fderiv_hinv {h : (Fin m → ℂ) → ℝ} {x : Fin m → ℂ} (hd : DifferentiableAt ℝ h x) (h0 : h x ≠ 0) :
    HasFDerivAt (fun y => ((h y : ℂ))⁻¹)
      (Complex.ofRealCLM.comp ((-(h x ^ 2)⁻¹) • fderiv ℝ h x)) x := by
  have h1 := (hasDerivAt_inv h0).comp_hasFDerivAt x hd.hasFDerivAt
  have h2 := Complex.ofRealCLM.hasFDerivAt.comp x h1
  have e : (fun y => ((h y : ℂ))⁻¹) = (⇑Complex.ofRealCLM ∘ (Inv.inv ∘ h)) := by
    funext y; simp
  rw [e]; exact h2

/- English proof (translation)
Establish `h1` using `(Real.hasDerivAt_log h0).comp_hasFDerivAt x hd.hasFDerivAt`. Establish `h2` using `Complex.ofRealCLM.hasFDerivAt.comp x h1`. Conclude with `h2`.
-/
theorem fderiv_hlog {h : (Fin m → ℂ) → ℝ} {x : Fin m → ℂ} (hd : DifferentiableAt ℝ h x) (h0 : h x ≠ 0) :
    HasFDerivAt (fun y => ((Real.log (h y) : ℝ) : ℂ))
      (Complex.ofRealCLM.comp ((h x)⁻¹ • fderiv ℝ h x)) x := by
  have h1 := (Real.hasDerivAt_log h0).comp_hasFDerivAt x hd.hasFDerivAt
  have h2 := Complex.ofRealCLM.hasFDerivAt.comp x h1
  exact h2

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `[pOp, wirt]`.
-/
theorem pOp_zero (l : Fin m) : pOp l (fun _ : Fin m → ℂ => (0 : E)) = fun _ => 0 := by
  funext x; simp [pOp, wirt]

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `[pbOp, wirtBar]`.
-/
theorem pbOp_zero (l : Fin m) : pbOp l (fun _ : Fin m → ℂ => (0 : E)) = fun _ => 0 := by
  funext x; simp [pbOp, wirtBar]

/- English proof (translation)
Establish `hi` using `fderiv_hinv hd h0`. Establish `hl` using `fderiv_hlog hd h0`. Simplify using `only [pOp, hx, if_true, wirt, wirtBar, Formalism.MainNotions.S.UnitaryLevelOperators.thLog, WirtingerDerivatives.fderiv_smul_apply hi.differentiableAt hf, hi.fderiv, hl.fderiv]`. Simplify using `only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, Complex.ofRealCLM_apply, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_inv, Complex.ofReal_pow, star_mul', star_add, star_star, Complex.star_def, Complex.conj_ofReal, map_mul, map_add, map …`. Use `module`.
-/
theorem pOp_hinv {h : (Fin m → ℂ) → ℝ} {x : Fin m → ℂ} (hx : x ∈ OmX m) (hd : DifferentiableAt ℝ h x)
    (h0 : h x ≠ 0) {f : (Fin m → ℂ) → E} (hf : DifferentiableAt ℝ f x) (l : Fin m) :
    pOp l (fun y => ((h y : ℂ))⁻¹ • f y) x =
      ((h x : ℂ))⁻¹ • (pOp l f x - star (Formalism.MainNotions.S.UnitaryLevelOperators.thLog l h x) • f x) := by
  have hi := fderiv_hinv hd h0
  have hl := fderiv_hlog hd h0
  simp only [pOp, hx, if_true, wirt, wirtBar, Formalism.MainNotions.S.UnitaryLevelOperators.thLog,
    WirtingerDerivatives.fderiv_smul_apply hi.differentiableAt hf, hi.fderiv, hl.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, Complex.ofRealCLM_apply, smul_eq_mul,
    Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_inv, Complex.ofReal_pow, star_mul', star_add, star_star,
    Complex.star_def, Complex.conj_ofReal, map_mul, map_add, map_inv₀, Complex.conj_I, map_div₀, map_one, map_ofNat,
    Complex.conj_conj]
  module

/- English proof (translation)
Establish `hi` using `fderiv_hinv hd h0`. Establish `hl` using `fderiv_hlog hd h0`. Simplify using `only [pbOp, hx, if_true, wirt, wirtBar, Formalism.MainNotions.S.UnitaryLevelOperators.thLog, WirtingerDerivatives.fderiv_smul_apply hi.differentiableAt hf, hi.fderiv, hl.fderiv]`. Simplify using `only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, Complex.ofRealCLM_apply, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_inv, Complex.ofReal_pow]`. Use `module`.
-/
theorem pbOp_hinv {h : (Fin m → ℂ) → ℝ} {x : Fin m → ℂ} (hx : x ∈ OmX m) (hd : DifferentiableAt ℝ h x)
    (h0 : h x ≠ 0) {f : (Fin m → ℂ) → E} (hf : DifferentiableAt ℝ f x) (l : Fin m) :
    pbOp l (fun y => ((h y : ℂ))⁻¹ • f y) x =
      ((h x : ℂ))⁻¹ • (pbOp l f x - Formalism.MainNotions.S.UnitaryLevelOperators.thLog l h x • f x) := by
  have hi := fderiv_hinv hd h0
  have hl := fderiv_hlog hd h0
  simp only [pbOp, hx, if_true, wirt, wirtBar, Formalism.MainNotions.S.UnitaryLevelOperators.thLog,
    WirtingerDerivatives.fderiv_smul_apply hi.differentiableAt hf, hi.fderiv, hl.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, Complex.ofRealCLM_apply, smul_eq_mul,
    Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_inv, Complex.ofReal_pow]
  module

/- English proof (translation)
Use function extensionality and compare the values at `y`. Simplify using `[Formalism.MainNotions.S.UnitaryLevelOperators.scalMat]`.
-/
theorem scalMat_same (φ : (Fin m → ℂ) → ℂ) (a : Fin 2) (f : (Fin m → ℂ) → E) :
    Formalism.MainNotions.S.UnitaryLevelOperators.scalMat φ 1 a a f = fun y => φ y • f y := by
  funext y; simp [Formalism.MainNotions.S.UnitaryLevelOperators.scalMat]

/- English proof (translation)
Use function extensionality and compare the values at `y`. Simplify using `[Formalism.MainNotions.S.UnitaryLevelOperators.scalMat, hab]`.
-/
theorem scalMat_ne (φ : (Fin m → ℂ) → ℂ) {a b : Fin 2} (hab : a ≠ b) (f : (Fin m → ℂ) → E) :
    Formalism.MainNotions.S.UnitaryLevelOperators.scalMat φ 1 a b f = fun _ => 0 := by
  funext y; simp [Formalism.MainNotions.S.UnitaryLevelOperators.scalMat, hab]

/- English proof (translation)
Introduce `m E _ _ l h hpos hsm Y f hf a b x hx`. Establish `hdh : DifferentiableAt ℝ h x` using `(hsm.differentiableOn (by simp)).differentiableAt ((WRPres.isOpen_omX m).mem_nhds hx)`. Establish `hdf` using `WRPres.differentiableAt_of_mem hf hx`. Establish `h0 : h x ≠ 0` using `(hpos x).ne'`. Establish `k1` using `pOp_hinv hx hdh h0 hdf l`.

Establish `k2` using `pbOp_hinv hx hdh h0 hdf l`. Establish `z1` using `pOp_zero (E := E) l`. Establish `z2` using `pbOp_zero (E := E) l`. Apply the tactic sequence `fin_cases a <;> fin_cases b <;>`. Apply the tactic sequence `simp [opMatMul, Tmat, TmatV, scalMat_same, scalMat_ne, Fin.sum_univ_two, k1, k2, z1, z2, cOp, ciOp, cbOp, cbiOp, smul_smul, mul_comm, smul_sub, smul_add, sub_eq_add_neg, add_assoc] <;> abel`.
-/
theorem stThLog_of_core : Formalism.MainNotions.S.UnitaryLevelOperators.stThLog := by
  intro m E _ _ l h hpos hsm Y f hf a b x hx
  have hdh : DifferentiableAt ℝ h x :=
    (hsm.differentiableOn (by simp)).differentiableAt ((WRPres.isOpen_omX m).mem_nhds hx)
  have hdf := WRPres.differentiableAt_of_mem hf hx
  have h0 : h x ≠ 0 := (hpos x).ne'
  have k1 := pOp_hinv hx hdh h0 hdf l
  have k2 := pbOp_hinv hx hdh h0 hdf l
  have z1 := pOp_zero (E := E) l
  have z2 := pbOp_zero (E := E) l
  fin_cases a <;> fin_cases b <;>
    simp [opMatMul, Tmat, TmatV, scalMat_same, scalMat_ne, Fin.sum_univ_two, k1, k2, z1, z2, cOp, ciOp, cbOp, cbiOp,
      smul_smul, mul_comm, smul_sub, smul_add, sub_eq_add_neg, add_assoc] <;> abel

/- English proof (translation)
Introduce `x₁ x₂ y` and use `by simp smul_left := fun c x y => by have e : (c • x : E) = ((c : ℂ)) • x := (Complex.coe_smul c x).symm show B (c • x) y = c • B x y rw [e, map_smulₛₗ] simp add_right := fun x y₁ y₂ => by simp smul_right := fun c x y => by have e : (c • y : E) = ((c : ℂ)) • y := (Complex.coe_smu …`.
-/
theorem isBB (B : E →L⋆[ℂ] E →L[ℂ] ℂ) : IsBoundedBilinearMap ℝ (fun p : E × E => B p.1 p.2) where
  add_left := fun x₁ x₂ y => by simp
  smul_left := fun c x y => by
    have e : (c • x : E) = ((c : ℂ)) • x := (Complex.coe_smul c x).symm
    show B (c • x) y = c • B x y
    rw [e, map_smulₛₗ]
    simp
  add_right := fun x y₁ y₂ => by simp
  smul_right := fun c x y => by
    have e : (c • y : E) = ((c : ℂ)) • y := (Complex.coe_smul c y).symm
    show B x (c • y) = c • B x y
    rw [e, map_smul]
    simp
  bound := ⟨‖B‖ + 1, by positivity, fun x y => by
    refine (B.le_opNorm₂ x y).trans ?_
    have : 0 ≤ ‖x‖ * ‖y‖ := by positivity
    nlinarith⟩

/- English proof (translation)
Establish `h` using `((isBB B).hasFDerivAt (x c, z c)).comp c (hx.hasFDerivAt.prodMk hz.hasFDerivAt)`. Establish `h' : HasFDerivAt (fun c' => B (x c') (z c')) _ c` using `h`. Rewrite using `[h'.fderiv]`. Simplify using `[IsBoundedBilinearMap.deriv_apply, add_comm]`.
-/
theorem fderiv_B (B : E →L⋆[ℂ] E →L[ℂ] ℂ) {x z : (Fin m → ℂ) → E} {c : Fin m → ℂ}
    (hx : DifferentiableAt ℝ x c) (hz : DifferentiableAt ℝ z c) (v : Fin m → ℂ) :
    fderiv ℝ (fun c' => B (x c') (z c')) c v = B (fderiv ℝ x c v) (z c) + B (x c) (fderiv ℝ z c v) := by
  have h := ((isBB B).hasFDerivAt (x c, z c)).comp c (hx.hasFDerivAt.prodMk hz.hasFDerivAt)
  have h' : HasFDerivAt (fun c' => B (x c') (z c')) _ c := h
  rw [h'.fderiv]
  simp [IsBoundedBilinearMap.deriv_apply, add_comm]

/- English proof (translation)
Establish `h` using `((isBB B).hasFDerivAt (x c, z c)).comp c (hx.hasFDerivAt.prodMk hz.hasFDerivAt)`. Establish `h' : HasFDerivAt (fun c' => B (x c') (z c')) _ c` using `h`. Conclude with `h'.differentiableAt`.
-/
theorem diff_B (B : E →L⋆[ℂ] E →L[ℂ] ℂ) {x z : (Fin m → ℂ) → E} {c : Fin m → ℂ}
    (hx : DifferentiableAt ℝ x c) (hz : DifferentiableAt ℝ z c) :
    DifferentiableAt ℝ (fun c' => B (x c') (z c')) c := by
  have h := ((isBB B).hasFDerivAt (x c, z c)).comp c (hx.hasFDerivAt.prodMk hz.hasFDerivAt)
  have h' : HasFDerivAt (fun c' => B (x c') (z c')) _ c := h
  exact h'.differentiableAt

/- English proof (translation)
Simplify using `only [wirt, wirtBar, fderiv_B B hx hz]`. Simplify using `[map_ofNat (starRingEnd ℂ) 2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem wirtBar_B (B : E →L⋆[ℂ] E →L[ℂ] ℂ) {x z : (Fin m → ℂ) → E} {c : Fin m → ℂ}
    (hx : DifferentiableAt ℝ x c) (hz : DifferentiableAt ℝ z c) (l : Fin m) :
    wirtBar l (fun c' => B (x c') (z c')) c = B (wirt l x c) (z c) + B (x c) (wirtBar l z c) := by
  simp only [wirt, wirtBar, fderiv_B B hx hz]
  simp [map_ofNat (starRingEnd ℂ) 2]
  ring

/- English proof (translation)
Simplify using `only [wirt, wirtBar, fderiv_B B hx hz]`. Simplify using `[map_ofNat (starRingEnd ℂ) 2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem wirt_B (B : E →L⋆[ℂ] E →L[ℂ] ℂ) {x z : (Fin m → ℂ) → E} {c : Fin m → ℂ}
    (hx : DifferentiableAt ℝ x c) (hz : DifferentiableAt ℝ z c) (l : Fin m) :
    wirt l (fun c' => B (x c') (z c')) c = B (wirtBar l x c) (z c) + B (x c) (wirt l z c) := by
  simp only [wirt, wirtBar, fderiv_B B hx hz]
  simp [map_ofNat (starRingEnd ℂ) 2]
  ring

/- English proof (translation)
Establish `hi` using `WirtingerDerivatives.hasFDerivAt_inv_apply l hc`. Simplify using `only [wirtBar, WirtingerDerivatives.fderiv_smul_apply hi.differentiableAt hβ, hi.fderiv]`. Simplify using the standard rewrite rules. Take the linear combination `(-(1 / 2 : ℂ) * ((c l) ^ 2)⁻¹ * β c) * Complex.I_sq`.
-/
theorem wirtBar_inv_mul {β : (Fin m → ℂ) → ℂ} {c : Fin m → ℂ} (hβ : DifferentiableAt ℝ β c) (l : Fin m)
    (hc : c l ≠ 0) :
    wirtBar l (fun c' => (c' l)⁻¹ • β c') c = (c l)⁻¹ * wirtBar l β c := by
  have hi := WirtingerDerivatives.hasFDerivAt_inv_apply l hc
  simp only [wirtBar, WirtingerDerivatives.fderiv_smul_apply hi.differentiableAt hβ, hi.fderiv]
  simp
  linear_combination (-(1 / 2 : ℂ) * ((c l) ^ 2)⁻¹ * β c) * Complex.I_sq

/- English proof (translation)
Establish `hi : HasFDerivAt (fun c' : Fin m → ℂ => star ((c' l)⁻¹)) ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (-(c l ^ 2)⁻¹)).restrictScalars ℝ).comp (ContinuousLinearMap.proj l))) c` using `(Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp c (WirtingerDerivatives.hasFDerivAt_inv_apply l hc)`. Establish `e : (fun c' : Fin m → ℂ => (star (c' l))⁻¹) = fun c' : Fin m → ℂ => star ((c' l)⁻¹)`. Use function extensionality and compare the values at `y`. Simplify using the standard rewrite rules. Establish `hi'` using `hi`.

Rewrite `hi'` using `[← e]`. Simplify using `only [wirt, WirtingerDerivatives.fderiv_smul_apply hi'.differentiableAt hβ, hi'.fderiv]`. Simplify using the standard rewrite rules. Take the linear combination `(-(1 / 2 : ℂ) * ((starRingEnd ℂ (c l)) ^ 2)⁻¹ * β c) * Complex.I_sq`.
-/
theorem wirt_conjInv_mul {β : (Fin m → ℂ) → ℂ} {c : Fin m → ℂ} (hβ : DifferentiableAt ℝ β c) (l : Fin m)
    (hc : c l ≠ 0) :
    wirt l (fun c' => (star (c' l))⁻¹ • β c') c = (star (c l))⁻¹ * wirt l β c := by
  have hi : HasFDerivAt (fun c' : Fin m → ℂ => star ((c' l)⁻¹))
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp
        (((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (-(c l ^ 2)⁻¹)).restrictScalars ℝ).comp
          (ContinuousLinearMap.proj l))) c :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp c (WirtingerDerivatives.hasFDerivAt_inv_apply l hc)
  have e : (fun c' : Fin m → ℂ => (star (c' l))⁻¹) = fun c' : Fin m → ℂ => star ((c' l)⁻¹) := by
    funext y; simp
  have hi' := hi
  rw [← e] at hi'
  simp only [wirt, WirtingerDerivatives.fderiv_smul_apply hi'.differentiableAt hβ, hi'.fderiv]
  simp
  linear_combination (-(1 / 2 : ℂ) * ((starRingEnd ℂ (c l)) ^ 2)⁻¹ * β c) * Complex.I_sq

/- English proof (translation)
Apply the tactic sequence `have h : fderiv ℝ (fun y => -g y) c = -fderiv ℝ g c := by first | exact fderiv_fun_neg | exact fderiv_neg`. Simplify using `only [wirtBar, h]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem wirtBar_neg' (l : Fin m) (g : (Fin m → ℂ) → ℂ) (c : Fin m → ℂ) :
    wirtBar l (fun y => -g y) c = -wirtBar l g c := by
  have h : fderiv ℝ (fun y => -g y) c = -fderiv ℝ g c := by
    first | exact fderiv_fun_neg | exact fderiv_neg
  simp only [wirtBar, h]
  simp
  ring

/- English proof (translation)
Apply the tactic sequence `have h : fderiv ℝ (fun y => -g y) c = -fderiv ℝ g c := by first | exact fderiv_fun_neg | exact fderiv_neg`. Simplify using `only [wirt, h]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem wirt_neg' (l : Fin m) (g : (Fin m → ℂ) → ℂ) (c : Fin m → ℂ) :
    wirt l (fun y => -g y) c = -wirt l g c := by
  have h : fderiv ℝ (fun y => -g y) c = -fderiv ℝ g c := by
    first | exact fderiv_fun_neg | exact fderiv_neg
  simp only [wirt, h]
  simp
  ring

/- English proof (translation)
Rewrite using `[Complex.star_def, Complex.mul_conj]`.
-/
theorem normSq_c (w : ℂ) : ((Complex.normSq w : ℝ) : ℂ) = w * star w := by
  rw [Complex.star_def, Complex.mul_conj]

/- English proof (translation)
Introduce `m E _ _ B l Y x z hx hz c hc`. Establish `hx0` using `WRPres.differentiableAt_of_mem (hx 0) hc`. Establish `hz0` using `WRPres.differentiableAt_of_mem (hz 0) hc`. Establish `hcl : c l ≠ 0` using `hc l`. Establish `hcs : star (c l) ≠ 0` using `by simpa using hcl`.

Establish `hβ` using `diff_B B hx0 hz0`. Establish `e1 : (fun c' => B (x 0 c') (opMatApply (TmatStar l (Y : ℂ)) z 1 c') / (Complex.normSq (c' l) : ℂ)) = fun c' => -((c' l)⁻¹ • B (x 0 c') (z 0 c'))`. Use function extensionality and compare the values at `c'`. Distinguish the cases in `h0 : c' l = 0`. Simplify using `[h0]`.

Establish `h0s : (starRingEnd ℂ) (c' l) ≠ 0` using `by simpa using h0`. Simplify using `only [opMatApply, TmatStar, Fin.sum_univ_two, normSq_c]`. Simplify using `[cbOp]`. Clear the denominators using the available nonvanishing facts. Establish `e2 : (fun c' => B (x 0 c') (opMatApply (Formalism.MainNotions.S.UnitaryLevelOperators.TmatVStar l (Y : ℂ)) z 1 c') / (Complex.normSq (c' l) : ℂ)) = fun c' => -((star (c' l))⁻¹ • B (x 0 c') (z 0 c'))`.

Use function extensionality and compare the values at `c'`. Distinguish the cases in `h0 : c' l = 0`. Simplify using `[h0]`. Establish `h0s : (starRingEnd ℂ) (c' l) ≠ 0` using `by simpa using h0`. Simplify using `only [opMatApply, Formalism.MainNotions.S.UnitaryLevelOperators.TmatVStar, Fin.sum_univ_two, normSq_c]`.

Simplify using `[cOp]`. Clear the denominators using the available nonvanishing facts. Establish `hcs' : (starRingEnd ℂ) (c l) ≠ 0` using `by simpa using hcl`. Establish `hY : ∀ u v : E, B (Y • u) v = (Y : ℂ) * B u v` using `fun u v => by`. Establish `h` using `(isBB B).smul_left Y u v`.

Simplify using `using h`. Prove the components needed by the constructor for the conclusion. Rewrite using `[e1, wirtBar_neg', wirtBar_inv_mul hβ l hcl, wirtBar_B B hx0 hz0, normSq_c]`. Simplify using `only [opMatApply, Tmat, TmatStar, Fin.sum_univ_two]`. Simplify using `[pOp, pbOp, hc, cOp, ciOp, cbOp, cbiOp, hY]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2, wirt_neg', wirt_conjInv_mul hβ l hcl, wirt_B B hx0 hz0, normSq_c]`. Simplify using `only [opMatApply, TmatV, Formalism.MainNotions.S.UnitaryLevelOperators.TmatVStar, Fin.sum_univ_two]`. Simplify using `[pOp, pbOp, hc, cOp, ciOp, cbOp, cbiOp, hY]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pointwise_integration_by_parts : Formalism.MainNotions.S.UnitaryLevelOperators.stIBP := by
  intro m E _ _ B l Y x z hx hz c hc
  have hx0 := WRPres.differentiableAt_of_mem (hx 0) hc
  have hz0 := WRPres.differentiableAt_of_mem (hz 0) hc
  have hcl : c l ≠ 0 := hc l
  have hcs : star (c l) ≠ 0 := by simpa using hcl
  have hβ := diff_B B hx0 hz0
  have e1 : (fun c' => B (x 0 c') (opMatApply (TmatStar l (Y : ℂ)) z 1 c') / (Complex.normSq (c' l) : ℂ)) =
      fun c' => -((c' l)⁻¹ • B (x 0 c') (z 0 c')) := by
    funext c'
    by_cases h0 : c' l = 0
    · simp [h0]
    · have h0s : (starRingEnd ℂ) (c' l) ≠ 0 := by simpa using h0
      simp only [opMatApply, TmatStar, Fin.sum_univ_two, normSq_c]
      simp [cbOp]
      field_simp
  have e2 : (fun c' => B (x 0 c') (opMatApply (Formalism.MainNotions.S.UnitaryLevelOperators.TmatVStar l (Y : ℂ)) z 1 c') /
      (Complex.normSq (c' l) : ℂ)) = fun c' => -((star (c' l))⁻¹ • B (x 0 c') (z 0 c')) := by
    funext c'
    by_cases h0 : c' l = 0
    · simp [h0]
    · have h0s : (starRingEnd ℂ) (c' l) ≠ 0 := by simpa using h0
      simp only [opMatApply, Formalism.MainNotions.S.UnitaryLevelOperators.TmatVStar, Fin.sum_univ_two, normSq_c]
      simp [cOp]
      field_simp
  have hcs' : (starRingEnd ℂ) (c l) ≠ 0 := by simpa using hcl
  have hY : ∀ u v : E, B (Y • u) v = (Y : ℂ) * B u v := fun u v => by
    have h := (isBB B).smul_left Y u v
    simpa using h
  constructor
  · rw [e1, wirtBar_neg', wirtBar_inv_mul hβ l hcl, wirtBar_B B hx0 hz0, normSq_c]
    simp only [opMatApply, Tmat, TmatStar, Fin.sum_univ_two]
    simp [pOp, pbOp, hc, cOp, ciOp, cbOp, cbiOp, hY]
    field_simp
    ring
  · rw [e2, wirt_neg', wirt_conjInv_mul hβ l hcl, wirt_B B hx0 hz0, normSq_c]
    simp only [opMatApply, TmatV, Formalism.MainNotions.S.UnitaryLevelOperators.TmatVStar, Fin.sum_univ_two]
    simp [pOp, pbOp, hc, cOp, ciOp, cbOp, cbiOp, hY]
    field_simp
    ring

end Formalism.MainNotions.InterlacingSignCuts

end

end PartA9

section PartA14

open Polynomial Finset

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts

def supN (p : ℝ[X]) : ℝ := sSup ((fun y => |p.eval y|) '' Set.Icc (-1 : ℝ) 1)

/- English proof (translation)
Unfold `supN`. Conclude with `le_csSup (isCompact_Icc.bddAbove_image (continuous_abs.comp p.continuous).continuousOn) ⟨x, hx, rfl⟩`.
-/
lemma le_supN (p : ℝ[X]) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) : |p.eval x| ≤ supN p := by
  unfold supN
  exact le_csSup (isCompact_Icc.bddAbove_image (continuous_abs.comp p.continuous).continuousOn) ⟨x, hx, rfl⟩

/- English proof (translation)
Conclude with `(abs_nonneg _).trans (le_supN p (⟨le_refl _, by norm_num⟩ : (-1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1))`.
-/
lemma supN_nonneg (p : ℝ[X]) : 0 ≤ supN p := by
  exact (abs_nonneg _).trans (le_supN p (⟨le_refl _, by norm_num⟩ : (-1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1))

def vmC (n k : ℕ) : ℝ := ∏ j ∈ Finset.range k, (((n : ℝ) ^ 2 - (j : ℝ) ^ 2) / (2 * (j : ℝ) + 1))

def VMarkovAt (n k : ℕ) : Prop :=
  ∀ p : ℝ[X], p.natDegree ≤ n → ∀ x ∈ Set.Icc (-1 : ℝ) 1,
    |(derivative^[k] p).eval x| ≤ vmC n k * supN p

/- English proof (translation)
Unfold `Formalism.MainNotions.S.UnitaryLevelOperators.stMarkov`. Prove the components needed by the constructor for the conclusion. Introduce `h n k hk p hp x hx`. Conclude with `h n k p hp hk x hx`. Introduce `h n k p hp hk x hx`.

Conclude with `h n k hk p hp x hx`.
-/
theorem stMarkov_iff : Formalism.MainNotions.S.UnitaryLevelOperators.stMarkov ↔ ∀ n k : ℕ, k ≤ n → VMarkovAt n k := by
  unfold Formalism.MainNotions.S.UnitaryLevelOperators.stMarkov
  constructor
  · intro h n k hk p hp x hx
    exact h n k p hp hk x hx
  · intro h n k p hp hk x hx
    exact h n k hk p hp x hx

/- English proof (translation)
Introduce `p hp x hx`. Simplify using `only [Function.iterate_zero, id, vmC, Finset.range_zero, Finset.prod_empty, one_mul]`. Conclude with `le_supN p hx`.
-/
theorem vMarkovAt_zero (n : ℕ) : VMarkovAt n 0 := by
  intro p hp x hx
  simp only [Function.iterate_zero, id, vmC, Finset.range_zero, Finset.prod_empty, one_mul]
  exact le_supN p hx

/- English proof (translation)
Introduce `p hp x hx`. Establish `h` using `Formalism.FourierDecayAlt.P.markov_inequality p n (supN p) hp (fun y hy => le_supN p hy) x hx`. Establish `hc : vmC n 1 = (n : ℝ) ^ 2` using `by simp [vmC]`. Rewrite using `[hc, Function.iterate_one]`. Conclude with `h`.
-/
theorem vMarkovAt_one (n : ℕ) : VMarkovAt n 1 := by
  intro p hp x hx
  have h := Formalism.FourierDecayAlt.P.markov_inequality p n (supN p) hp (fun y hy => le_supN p hy) x hx
  have hc : vmC n 1 = (n : ℝ) ^ 2 := by simp [vmC]
  rw [hc, Function.iterate_one]
  exact h

/- English proof (translation)
Proceed by induction on `k generalizing p with`. Consider the case `zero`. Introduce `x hx`. Simplify using `using le_supN p hx`. Consider the case `succ k ih`.

Introduce `x hx`. Establish `hd : (derivative p).natDegree ≤ n` using `(natDegree_derivative_le p).trans ((Nat.sub_le _ _).trans hp)`. Establish `h1` using `ih (derivative p) hd x hx`. Establish `h2 : supN (derivative p) ≤ (n : ℝ) ^ 2 * supN p`. Unfold `supN`.

Apply `csSup_le ((Set.nonempty_Icc.2 (by norm_num)).image _)` to reduce the goal to its premises. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `Formalism.FourierDecayAlt.P.markov_inequality p n (supN p) hp (fun z hz => le_supN p hz) y hy`. Rewrite using `[Function.iterate_succ_apply]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem markov_iter (n k : ℕ) (p : ℝ[X]) (hp : p.natDegree ≤ n) :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1, |(derivative^[k] p).eval x| ≤ ((n : ℝ) ^ 2) ^ k * supN p := by
  induction k generalizing p with
  | zero =>
    intro x hx
    simpa using le_supN p hx
  | succ k ih =>
    intro x hx
    have hd : (derivative p).natDegree ≤ n := (natDegree_derivative_le p).trans ((Nat.sub_le _ _).trans hp)
    have h1 := ih (derivative p) hd x hx
    have h2 : supN (derivative p) ≤ (n : ℝ) ^ 2 * supN p := by
      unfold supN
      apply csSup_le ((Set.nonempty_Icc.2 (by norm_num)).image _)
      rintro _ ⟨y, hy, rfl⟩
      exact Formalism.FourierDecayAlt.P.markov_inequality p n (supN p) hp (fun z hz => le_supN p hz) y hy
    rw [Function.iterate_succ_apply]
    calc |(derivative^[k] (derivative p)).eval x| ≤ ((n : ℝ) ^ 2) ^ k * supN (derivative p) := h1
      _ ≤ ((n : ℝ) ^ 2) ^ k * ((n : ℝ) ^ 2 * supN p) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = ((n : ℝ) ^ 2) ^ (k + 1) * supN p := by ring

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `m hm`. Establish `: m = n' + 1` using `by omega`.

Substitute `this` using the available equality. Simplify using `[vmC, Nat.factorial_succ]`. Consider the case `succ k ih`. Introduce `m hm`. Establish `h` using `ih (m + 1) (by omega)`.

Establish `hn : ((n' : ℝ) + 1) = (k : ℝ) + 1 + (m : ℝ)`. Establish `: ((n' + 1 : ℕ) : ℝ) = ((k + 1 + m : ℕ) : ℝ)` using `by rw [hm]`. Move the coercions through the operations in `at this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2k : (2 * (k : ℝ) + 1) ≠ 0` using `by positivity`.

Establish `e1 : vmC (n' + 1) (k + 1) = vmC (n' + 1) k * (((((n' + 1 : ℕ) : ℝ)) ^ 2 - (k : ℝ) ^ 2) / (2 * (k : ℝ) + 1))`. Unfold `vmC`. Rewrite using `[Finset.prod_range_succ]`. Establish `e2 : ((2 * (k + 1)).factorial : ℝ) = (2 * (k : ℝ) + 2) * (2 * (k : ℝ) + 1) * ((2 * k).factorial : ℝ)`. Establish `: 2 * (k + 1) = (2 * k + 1) + 1` using `by ring`.

Rewrite using `[this, Nat.factorial_succ, Nat.factorial_succ]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `e3 : ((m + 1).factorial : ℝ) = ((m : ℝ) + 1) * (m.factorial : ℝ)`. Rewrite using `[Nat.factorial_succ]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `e4 : ((n' + (k + 1)).factorial : ℝ) = ((n' : ℝ) + (k : ℝ) + 1) * ((n' + k).factorial : ℝ)`. Establish `: n' + (k + 1) = (n' + k) + 1` using `by ring`. Rewrite using `[this, Nat.factorial_succ]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `e5 : ((k + 1).factorial : ℝ) = ((k : ℝ) + 1) * (k.factorial : ℝ)`. Rewrite using `[Nat.factorial_succ]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `h` using `[e3]`. Rewrite using `[e1, e2, e4, e5]`. Use `push_cast`. Establish `hm' : (m : ℝ) + 1 = (n' : ℝ) + 1 - (k : ℝ)` using `by linarith`.

Establish `key : vmC (n' + 1) k * ((((n' : ℝ) + 1) ^ 2 - (k : ℝ) ^ 2) / (2 * (k : ℝ) + 1)) * (m.factorial : ℝ) * ((2 * (k : ℝ) + 2) * (2 * (k : ℝ) + 1) * ((2 * k).factorial : ℝ)) = (vmC (n' + 1) k * (((m : ℝ) + 1) * (m.factorial : ℝ)) * ((2 * k).factorial : ℝ)) * (((n' : ℝ) + 1 + (k : ℝ)) * …`. Rewrite using `[hm']`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key, h]`.

Expand and normalize the polynomial expressions, which then agree.
-/
lemma vmC_closed (n' : ℕ) : ∀ k m : ℕ, k + m = n' + 1 →
    vmC (n' + 1) k * (m.factorial : ℝ) * ((2 * k).factorial : ℝ) =
      ((n' : ℝ) + 1) * ((n' + k).factorial : ℝ) * 2 ^ k * (k.factorial : ℝ) := by
  intro k
  induction k with
  | zero =>
    intro m hm
    have : m = n' + 1 := by omega
    subst this
    simp [vmC, Nat.factorial_succ]
  | succ k ih =>
    intro m hm
    have h := ih (m + 1) (by omega)
    have hn : ((n' : ℝ) + 1) = (k : ℝ) + 1 + (m : ℝ) := by
      have : ((n' + 1 : ℕ) : ℝ) = ((k + 1 + m : ℕ) : ℝ) := by rw [hm]
      push_cast at this; linarith
    have h2k : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
    have e1 : vmC (n' + 1) (k + 1) =
        vmC (n' + 1) k * (((((n' + 1 : ℕ) : ℝ)) ^ 2 - (k : ℝ) ^ 2) / (2 * (k : ℝ) + 1)) := by
      unfold vmC; rw [Finset.prod_range_succ]
    have e2 : ((2 * (k + 1)).factorial : ℝ) = (2 * (k : ℝ) + 2) * (2 * (k : ℝ) + 1) * ((2 * k).factorial : ℝ) := by
      have : 2 * (k + 1) = (2 * k + 1) + 1 := by ring
      rw [this, Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring
    have e3 : ((m + 1).factorial : ℝ) = ((m : ℝ) + 1) * (m.factorial : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have e4 : ((n' + (k + 1)).factorial : ℝ) = ((n' : ℝ) + (k : ℝ) + 1) * ((n' + k).factorial : ℝ) := by
      have : n' + (k + 1) = (n' + k) + 1 := by ring
      rw [this, Nat.factorial_succ]; push_cast; ring
    have e5 : ((k + 1).factorial : ℝ) = ((k : ℝ) + 1) * (k.factorial : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [e3] at h
    rw [e1, e2, e4, e5]
    push_cast
    have hm' : (m : ℝ) + 1 = (n' : ℝ) + 1 - (k : ℝ) := by linarith
    have key : vmC (n' + 1) k * ((((n' : ℝ) + 1) ^ 2 - (k : ℝ) ^ 2) / (2 * (k : ℝ) + 1)) * (m.factorial : ℝ) *
        ((2 * (k : ℝ) + 2) * (2 * (k : ℝ) + 1) * ((2 * k).factorial : ℝ)) =
        (vmC (n' + 1) k * (((m : ℝ) + 1) * (m.factorial : ℝ)) * ((2 * k).factorial : ℝ)) *
          (((n' : ℝ) + 1 + (k : ℝ)) * (2 * (k : ℝ) + 2)) := by
      rw [hm']; field_simp; ring
    rw [key, h]; ring

/- English proof (translation)
Establish `h` using `vmC_closed n' (n' + 1) 0 (by omega)`. Establish `e : ((2 * (n' + 1)).factorial : ℝ) = (2 * ((n' : ℝ) + 1)) * ((n' + (n' + 1)).factorial : ℝ)`. Establish `: 2 * (n' + 1) = (n' + (n' + 1)) + 1` using `by ring`. Rewrite using `[this, Nat.factorial_succ]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hf : ((n' + (n' + 1)).factorial : ℝ) ≠ 0` using `by positivity`. Establish `hn : ((n' : ℝ) + 1) ≠ 0` using `by positivity`. Rewrite `h` using `[e]`. Simplify using `only [Nat.factorial_zero, Nat.cast_one, mul_one] at h`.

Establish `h' : vmC (n' + 1) (n' + 1) * 2 * (((n' : ℝ) + 1) * ((n' + (n' + 1)).factorial : ℝ)) = (((n' + 1).factorial : ℝ) * 2 ^ n') * 2 * (((n' : ℝ) + 1) * ((n' + (n' + 1)).factorial : ℝ))`. Combine the equalities or inequalities in the displayed calculation. Establish `h2` using `mul_right_cancel₀ (mul_ne_zero hn hf) h'`. Conclude with `mul_right_cancel₀ (two_ne_zero) h2`.
-/
lemma vmC_self (n' : ℕ) : vmC (n' + 1) (n' + 1) = ((n' + 1).factorial : ℝ) * 2 ^ n' := by
  have h := vmC_closed n' (n' + 1) 0 (by omega)
  have e : ((2 * (n' + 1)).factorial : ℝ) = (2 * ((n' : ℝ) + 1)) * ((n' + (n' + 1)).factorial : ℝ) := by
    have : 2 * (n' + 1) = (n' + (n' + 1)) + 1 := by ring
    rw [this, Nat.factorial_succ]; push_cast; ring
  have hf : ((n' + (n' + 1)).factorial : ℝ) ≠ 0 := by positivity
  have hn : ((n' : ℝ) + 1) ≠ 0 := by positivity
  rw [e] at h
  simp only [Nat.factorial_zero, Nat.cast_one, mul_one] at h
  have h' : vmC (n' + 1) (n' + 1) * 2 * (((n' : ℝ) + 1) * ((n' + (n' + 1)).factorial : ℝ)) =
      (((n' + 1).factorial : ℝ) * 2 ^ n') * 2 * (((n' : ℝ) + 1) * ((n' + (n' + 1)).factorial : ℝ)) := by
    calc _ = vmC (n' + 1) (n' + 1) * (2 * ((n' : ℝ) + 1) * ((n' + (n' + 1)).factorial : ℝ)) := by ring
      _ = _ := by rw [h]; ring
  have h2 := mul_right_cancel₀ (mul_ne_zero hn hf) h'
  exact mul_right_cancel₀ (two_ne_zero) h2

/- English proof (translation)
Break down `n with _ | n'` into its components or cases. Conclude with `vMarkovAt_zero 0`. Introduce `p hp x _`. Establish `hdeg : (derivative^[n' + 1] p).natDegree ≤ 0` using `(natDegree_iterate_derivative p (n' + 1)).trans (by omega)`. Establish `hconst : (derivative^[n' + 1] p).eval x = ((n' + 1).factorial : ℝ) * p.coeff (n' + 1)`.

Rewrite using `[eq_C_of_natDegree_le_zero hdeg, eval_C, coeff_iterate_derivative, zero_add, Nat.descFactorial_self, nsmul_eq_mul]`. Establish `hev : ∀ y : ℝ, (∑ k : Fin (n' + 1 + 1), ((y : ℂ) ^ (k : ℕ)) • ((p.coeff (k : ℕ) : ℝ) : ℂ)) = ((p.eval y : ℝ) : ℂ)`. Introduce `y`. Rewrite using `[eval_eq_sum_range' (Nat.lt_succ_of_le hp), ← Fin.sum_univ_eq_sum_range (fun i => p.coeff i * y ^ i)]`. Use `push_cast`.

Conclude with `Finset.sum_congr rfl fun k _ => by rw [smul_eq_mul, mul_comm]`. Establish `hB` using `Formalism.FourierDecayAlt.P.chebyshev_leading_coeff_bound ℂ (-1) 1 (n' + 1) (fun k : Fin (n' + 1 + 1) => ((p.coeff (k : ℕ) : ℝ) : ℂ)) (supN p) (by norm_num) (by omega) (fun j => by`. Rewrite using `[hev, Complex.norm_real, Real.norm_eq_abs]`. Use `le_supN p ?_` and prove the remaining obligations. Establish `e : Formalism.SA.C.chebPt (-1) 1 (n' + 1) j = Real.cos (Real.pi * ((j : ℕ) : ℝ) / ((n' + 1 : ℕ) : ℝ))`.

Unfold `Formalism.SA.C.chebPt`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)`. Establish `hB' : |p.coeff (n' + 1)| ≤ 2 ^ n' * supN p`.

Establish `: ‖((p.coeff ((Fin.last (n' + 1) : Fin (n' + 1 + 1)) : ℕ) : ℝ) : ℂ)‖ = |p.coeff (n' + 1)|`. Rewrite using `[Complex.norm_real, Real.norm_eq_abs]`. Both sides reduce to the same expression. Rewrite using `[← this]`. Use `hB.trans (le_of_eq ?_)` and prove the remaining obligations.

Establish `: (4 : ℝ) / (1 - (-1)) = 2` using `by norm_num`. Rewrite using `[this, pow_succ]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hconst, vmC_self, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((n' + 1).factorial : ℝ)), mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_left hB' (by positivity)`.
-/
theorem vMarkovAt_self (n : ℕ) : VMarkovAt n n := by
  rcases n with _ | n'
  · exact vMarkovAt_zero 0
  intro p hp x _
  have hdeg : (derivative^[n' + 1] p).natDegree ≤ 0 :=
    (natDegree_iterate_derivative p (n' + 1)).trans (by omega)
  have hconst : (derivative^[n' + 1] p).eval x = ((n' + 1).factorial : ℝ) * p.coeff (n' + 1) := by
    rw [eq_C_of_natDegree_le_zero hdeg, eval_C, coeff_iterate_derivative, zero_add, Nat.descFactorial_self,
      nsmul_eq_mul]
  have hev : ∀ y : ℝ, (∑ k : Fin (n' + 1 + 1), ((y : ℂ) ^ (k : ℕ)) • ((p.coeff (k : ℕ) : ℝ) : ℂ)) =
      ((p.eval y : ℝ) : ℂ) := by
    intro y
    rw [eval_eq_sum_range' (Nat.lt_succ_of_le hp), ← Fin.sum_univ_eq_sum_range (fun i => p.coeff i * y ^ i)]
    push_cast
    exact Finset.sum_congr rfl fun k _ => by rw [smul_eq_mul, mul_comm]
  have hB := Formalism.FourierDecayAlt.P.chebyshev_leading_coeff_bound ℂ (-1) 1 (n' + 1)
    (fun k : Fin (n' + 1 + 1) => ((p.coeff (k : ℕ) : ℝ) : ℂ)) (supN p) (by norm_num) (by omega)
    (fun j => by
      rw [hev, Complex.norm_real, Real.norm_eq_abs]
      refine le_supN p ?_
      have e : Formalism.SA.C.chebPt (-1) 1 (n' + 1) j = Real.cos (Real.pi * ((j : ℕ) : ℝ) / ((n' + 1 : ℕ) : ℝ)) := by
        unfold Formalism.SA.C.chebPt; ring
      rw [e]
      exact ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)
  have hB' : |p.coeff (n' + 1)| ≤ 2 ^ n' * supN p := by
    have : ‖((p.coeff ((Fin.last (n' + 1) : Fin (n' + 1 + 1)) : ℕ) : ℝ) : ℂ)‖ = |p.coeff (n' + 1)| := by
      rw [Complex.norm_real, Real.norm_eq_abs]; rfl
    rw [← this]
    refine hB.trans (le_of_eq ?_)
    have : (4 : ℝ) / (1 - (-1)) = 2 := by norm_num
    rw [this, pow_succ]; ring
  rw [hconst, vmC_self, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((n' + 1).factorial : ℝ)), mul_assoc]
  exact mul_le_mul_of_nonneg_left hB' (by positivity)

/- English proof (translation)
Unfold `vmC`. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.prod_le_prod` to reduce the goal to its premises. Introduce `j hj`. Establish `hj' : j < k` using `Finset.mem_range.1 hj`.

Establish `hjn : (j : ℝ) ≤ n` using `by exact_mod_cast (by omega : j ≤ n)`. Establish `hj0 : (0 : ℝ) ≤ j` using `Nat.cast_nonneg j`. Apply `div_nonneg _ (by positivity)` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities. Introduce `j _`.

Establish `hj0 : (0 : ℝ) ≤ j` using `Nat.cast_nonneg j`. Rewrite using `[div_le_iff₀ (by positivity)]`. Use polynomial arithmetic with `[mul_nonneg (sq_nonneg (n : ℝ)) hj0, sq_nonneg (j : ℝ)]`. Use `_ = ((n : ℝ) ^ 2) ^ k := by rw [Finset.prod_const, Finset.card_range]`.
-/
theorem vmC_le (n k : ℕ) (hk : k ≤ n) : vmC n k ≤ ((n : ℝ) ^ 2) ^ k := by
  unfold vmC
  calc ∏ j ∈ Finset.range k, (((n : ℝ) ^ 2 - (j : ℝ) ^ 2) / (2 * (j : ℝ) + 1))
      ≤ ∏ _j ∈ Finset.range k, ((n : ℝ) ^ 2) := by
        apply Finset.prod_le_prod
        · intro j hj
          have hj' : j < k := Finset.mem_range.1 hj
          have hjn : (j : ℝ) ≤ n := by exact_mod_cast (by omega : j ≤ n)
          have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
          apply div_nonneg _ (by positivity)
          nlinarith
        · intro j _
          have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
          rw [div_le_iff₀ (by positivity)]
          nlinarith [mul_nonneg (sq_nonneg (n : ℝ)) hj0, sq_nonneg (j : ℝ)]
    _ = ((n : ℝ) ^ 2) ^ k := by rw [Finset.prod_const, Finset.card_range]

/- English proof (translation)
Rewrite using `[Chebyshev.iterate_derivative_T_eval_one_eq_div]`. Unfold `vmC`. Rewrite using `[Finset.prod_div_distrib]`. Use `push_cast`. Both sides reduce to the same expression.
-/
lemma markov_coeff_eq_chebyshev_derivative (n k : ℕ) : vmC n k = (derivative^[k] (Chebyshev.T ℝ n)).eval 1 := by
  rw [Chebyshev.iterate_derivative_T_eval_one_eq_div]
  unfold vmC
  rw [Finset.prod_div_distrib]
  push_cast
  rfl

/- English proof (translation)
Unfold `vmC`. Apply `Finset.prod_nonneg` to reduce the goal to its premises. Introduce `j hj`. Establish `hj' : j < k` using `Finset.mem_range.1 hj`. Establish `hjn : (j : ℝ) ≤ n` using `by exact_mod_cast (by omega : j ≤ n)`.

Establish `hj0 : (0 : ℝ) ≤ j` using `Nat.cast_nonneg j`. Apply `div_nonneg _ (by positivity)` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities.
-/
lemma vmC_nonneg (n k : ℕ) (hk : k ≤ n) : 0 ≤ vmC n k := by
  unfold vmC
  apply Finset.prod_nonneg
  intro j hj
  have hj' : j < k := Finset.mem_range.1 hj
  have hjn : (j : ℝ) ≤ n := by exact_mod_cast (by omega : j ≤ n)
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  apply div_nonneg _ (by positivity)
  nlinarith

/- English proof (translation)
Break down `(supN_nonneg p).eq_or_lt with h0 | hpos` into its components or cases. Establish `hz : p = 0`. Use `Polynomial.eq_zero_of_infinite_isRoot p ((Set.Icc_infinite (by norm_num : (-1 : ℝ) < 1)).mono fun x hx => ?_)` and prove the remaining obligations. Use `le_supN p hx` as an intermediate fact. Rewrite `this` using `[← h0]`.

Conclude with `abs_nonpos_iff.1 this`. Substitute `hz` using the available equality. Simplify using `[← h0]`. Establish `hb : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |(C (supN p)⁻¹ * p).eval x| ≤ 1`. Introduce `x hx`.

Rewrite using `[eval_mul, eval_C, abs_mul, abs_of_pos (inv_pos.2 hpos), inv_mul_le_iff₀ hpos, mul_one]`. Conclude with `le_supN p hx`. Establish `hd : (C (supN p)⁻¹ * p).degree ≤ n` using `degree_le_of_natDegree_le ((natDegree_C_mul_le _ _).trans hp)`. Establish `h` using `Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one (k := k) (le_refl (1 : ℝ)) hd hb`. Rewrite `h` using `[iterate_derivative_C_mul, eval_mul, eval_C, ← markov_coeff_eq_chebyshev_derivative, inv_mul_le_iff₀ hpos]`.

Combine the linear relations using `[h, mul_comm (supN p) (vmC n k)]`.
-/
lemma end_one_le (n k : ℕ) (p : ℝ[X]) (hp : p.natDegree ≤ n) :
    (derivative^[k] p).eval 1 ≤ vmC n k * supN p := by
  rcases (supN_nonneg p).eq_or_lt with h0 | hpos
  · have hz : p = 0 := by
      refine Polynomial.eq_zero_of_infinite_isRoot p
        ((Set.Icc_infinite (by norm_num : (-1 : ℝ) < 1)).mono fun x hx => ?_)
      have := le_supN p hx
      rw [← h0] at this
      exact abs_nonpos_iff.1 this
    subst hz
    simp [← h0]
  · have hb : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |(C (supN p)⁻¹ * p).eval x| ≤ 1 := by
      intro x hx
      rw [eval_mul, eval_C, abs_mul, abs_of_pos (inv_pos.2 hpos), inv_mul_le_iff₀ hpos, mul_one]
      exact le_supN p hx
    have hd : (C (supN p)⁻¹ * p).degree ≤ n :=
      degree_le_of_natDegree_le ((natDegree_C_mul_le _ _).trans hp)
    have h := Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one (k := k) (le_refl (1 : ℝ)) hd hb
    rw [iterate_derivative_C_mul, eval_mul, eval_C, ← markov_coeff_eq_chebyshev_derivative, inv_mul_le_iff₀ hpos] at h
    linarith [h, mul_comm (supN p) (vmC n k)]

/- English proof (translation)
Unfold `supN`. Simplify using `only [eval_neg, abs_neg]`.
-/
lemma supN_neg (p : ℝ[X]) : supN (-p) = supN p := by
  unfold supN
  simp only [eval_neg, abs_neg]

/- English proof (translation)
The claim follows from `|(derivative^[k] p).eval 1| ≤ vmC n k * supN p := by refine abs_le.2 ⟨?_, end_one_le n k p hp⟩ have h := end_one_le n k (-p) (by rwa [natDegree_neg]) rw [iterate_derivative_neg, eval_neg, supN_neg] at h linarith`.
-/
lemma end_one (n k : ℕ) (p : ℝ[X]) (hp : p.natDegree ≤ n) :
    |(derivative^[k] p).eval 1| ≤ vmC n k * supN p := by
  refine abs_le.2 ⟨?_, end_one_le n k p hp⟩
  have h := end_one_le n k (-p) (by rwa [natDegree_neg])
  rw [iterate_derivative_neg, eval_neg, supN_neg] at h
  linarith

/- English proof (translation)
Proceed by induction on `k generalizing p with`. Consider the case `zero => simp`. Consider the case `succ k ih => simp [ih (derivative p), derivative_comp, pow_succ]`.
-/
lemma iter_comp_neg (p : ℝ[X]) (k : ℕ) :
    derivative^[k] (p.comp (-X)) = (-1) ^ k * (derivative^[k] p).comp (-X) := by
  induction k generalizing p with
  | zero => simp
  | succ k ih => simp [ih (derivative p), derivative_comp, pow_succ]

/- English proof (translation)
Unfold `supN`. Use `congr 1`. Use extensionality with `t`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`.

Conclude with `⟨-y, ⟨by linarith [hy.2], by linarith [hy.1]⟩, by simp⟩`. Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `⟨-y, ⟨by linarith [hy.2], by linarith [hy.1]⟩, by simp⟩`.
-/
lemma supN_comp_neg (p : ℝ[X]) : supN (p.comp (-X)) = supN p := by
  unfold supN
  congr 1
  ext t
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨-y, ⟨by linarith [hy.2], by linarith [hy.1]⟩, by simp⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨-y, ⟨by linarith [hy.2], by linarith [hy.1]⟩, by simp⟩

/- English proof (translation)
The claim follows from `|(derivative^[k] p).eval (-1)| ≤ vmC n k * supN p := by have hd : (p.comp (-X)).natDegree ≤ n := by refine natDegree_comp_le.trans ?_ simpa using hp have h := end_one n k (p.comp (-X)) hd rw [iter_comp_neg, supN_comp_neg, eval_mul, eval_pow, eval_neg, eval_one, abs_mul, abs_pow, …`.
-/
lemma end_neg_one (n k : ℕ) (p : ℝ[X]) (hp : p.natDegree ≤ n) :
    |(derivative^[k] p).eval (-1)| ≤ vmC n k * supN p := by
  have hd : (p.comp (-X)).natDegree ≤ n := by
    refine natDegree_comp_le.trans ?_
    simpa using hp
  have h := end_one n k (p.comp (-X)) hd
  rw [iter_comp_neg, supN_comp_neg, eval_mul, eval_pow, eval_neg, eval_one, abs_mul, abs_pow, abs_neg, abs_one,
    one_pow, one_mul, eval_comp, eval_neg, eval_X] at h
  exact h

/- English proof (translation)
Introduce `p hp x hx`. Establish `hdeg : (derivative^[n] p).natDegree ≤ 1` using `(natDegree_iterate_derivative p n).trans (by omega)`. Take `⟨a, b, hab⟩` from `exists_eq_X_add_C_of_natDegree_le_one hdeg`. Establish `h1` using `end_one (n + 1) n p hp`. Establish `h2` using `end_neg_one (n + 1) n p hp`.

Rewrite `h1`, `h2`, the goal using `[hab]`. Simplify using `only [eval_add, eval_mul, eval_C, eval_X] at h1 h2 ⊢`. Establish `e : a * x + b = (1 + x) / 2 * (a * 1 + b) + (1 - x) / 2 * (a * (-1) + b)` using `by ring`. Rewrite using `[e]`. Establish `hx1 : 0 ≤ (1 + x) / 2` using `by linarith [hx.1]`.

Establish `hx2 : 0 ≤ (1 - x) / 2` using `by linarith [hx.2]`. Combine the equalities or inequalities in the displayed calculation. Use `(abs_add_le _ _).trans ?_` and prove the remaining obligations. Rewrite using `[abs_mul, abs_mul, abs_of_nonneg hx1, abs_of_nonneg hx2]`. Use `_ ≤ (1 + x) / 2 * (vmC (n + 1) n * supN p) + (1 - x) / 2 * (vmC (n + 1) n * supN p) := add_le_add (mul_le_mul_of_nonneg_left h1 hx1) (mul_le_mul_of_nonneg_left h2 hx2)`.

Use `_ = vmC (n + 1) n * supN p := by ring`.
-/
theorem vMarkovAt_pred (n : ℕ) : VMarkovAt (n + 1) n := by
  intro p hp x hx
  have hdeg : (derivative^[n] p).natDegree ≤ 1 :=
    (natDegree_iterate_derivative p n).trans (by omega)
  obtain ⟨a, b, hab⟩ := exists_eq_X_add_C_of_natDegree_le_one hdeg
  have h1 := end_one (n + 1) n p hp
  have h2 := end_neg_one (n + 1) n p hp
  rw [hab] at h1 h2 ⊢
  simp only [eval_add, eval_mul, eval_C, eval_X] at h1 h2 ⊢
  have e : a * x + b = (1 + x) / 2 * (a * 1 + b) + (1 - x) / 2 * (a * (-1) + b) := by ring
  rw [e]
  have hx1 : 0 ≤ (1 + x) / 2 := by linarith [hx.1]
  have hx2 : 0 ≤ (1 - x) / 2 := by linarith [hx.2]
  calc |(1 + x) / 2 * (a * 1 + b) + (1 - x) / 2 * (a * (-1) + b)|
      ≤ (1 + x) / 2 * |a * 1 + b| + (1 - x) / 2 * |a * (-1) + b| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_nonneg hx1, abs_of_nonneg hx2]
    _ ≤ (1 + x) / 2 * (vmC (n + 1) n * supN p) + (1 - x) / 2 * (vmC (n + 1) n * supN p) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 hx1) (mul_le_mul_of_nonneg_left h2 hx2)
    _ = vmC (n + 1) n * supN p := by ring

/- English proof (translation)
Rewrite using `[stMarkov_iff]`. Introduce `n k hk p hp x hx`. Break down `Nat.lt_or_ge k 2 with hk2 | hk2` into its components or cases. Use `interval_cases k`. Conclude with `vMarkovAt_zero n p hp x hx`.

Conclude with `vMarkovAt_one n p hp x hx`. Break down `Nat.lt_or_ge (k + 1) n with hkn | hkn` into its components or cases. Break down `eq_or_lt_of_le hx.1 with h1 | h1` into its components or cases. Rewrite using `[← h1]`. Conclude with `end_neg_one n k p hp`.

Break down `eq_or_lt_of_le hx.2 with h2 | h2` into its components or cases. Rewrite using `[h2]`. Conclude with `end_one n k p hp`. Conclude with `h n k hk2 (by omega) p hp x ⟨h1, h2⟩`. Break down `eq_or_lt_of_le hk with hkn' | hkn'` into its components or cases.

Substitute `hkn'` using the available equality. Conclude with `vMarkovAt_self k p hp x hx`. Establish `hn : n = k + 1` using `by omega`. Substitute `hn` using the available equality. Conclude with `vMarkovAt_pred k p hp x hx`.
-/
theorem stMarkov_of_mid
    (h : ∀ n k : ℕ, 2 ≤ k → k + 2 ≤ n → ∀ p : ℝ[X], p.natDegree ≤ n → ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
      |(derivative^[k] p).eval x| ≤ vmC n k * supN p) : Formalism.MainNotions.S.UnitaryLevelOperators.stMarkov := by
  rw [stMarkov_iff]
  intro n k hk p hp x hx
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · interval_cases k
    · exact vMarkovAt_zero n p hp x hx
    · exact vMarkovAt_one n p hp x hx
  rcases Nat.lt_or_ge (k + 1) n with hkn | hkn
  · rcases eq_or_lt_of_le hx.1 with h1 | h1
    · rw [← h1]
      exact end_neg_one n k p hp
    rcases eq_or_lt_of_le hx.2 with h2 | h2
    · rw [h2]
      exact end_one n k p hp
    exact h n k hk2 (by omega) p hp x ⟨h1, h2⟩
  · rcases eq_or_lt_of_le hk with hkn' | hkn'
    · subst hkn'
      exact vMarkovAt_self k p hp x hx
    · have hn : n = k + 1 := by omega
      subst hn
      exact vMarkovAt_pred k p hp x hx

end Formalism.MainNotions.InterlacingSignCuts

end

end PartA14

section PartA14v

open Polynomial Finset

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Introduce `p`. Simplify using the standard rewrite rules. Consider the case `succ k ih`.

Introduce `p`. Establish `hq : derivative (C a * X + C b) = C a` using `by simp`. Rewrite using `[Function.iterate_succ_apply, Function.iterate_succ_apply, derivative_comp, hq, iterate_derivative_C_mul, ih (derivative p), ← mul_assoc, ← C_mul, ← pow_succ']`.
-/
lemma iter_comp_affine (a b : ℝ) (k : ℕ) : ∀ p : ℝ[X],
    derivative^[k] (p.comp (C a * X + C b)) = C (a ^ k) * (derivative^[k] p).comp (C a * X + C b) := by
  induction k with
  | zero =>
    intro p
    simp
  | succ k ih =>
    intro p
    have hq : derivative (C a * X + C b) = C a := by simp
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, derivative_comp, hq,
      iterate_derivative_C_mul, ih (derivative p), ← mul_assoc, ← C_mul, ← pow_succ']

/- English proof (translation)
Unfold `supN`. Apply `csSup_le ((Set.nonempty_Icc.2 (by norm_num)).image _)` to reduce the goal to its premises. Introduce and unpack `_ ⟨u, hu, rfl⟩`. Use `le_supN p (h u hu)` as an intermediate fact. Simplify using `only [eval_comp, eval_add, eval_mul, eval_C, eval_X]`.

Conclude with `this`.
-/
lemma supN_comp_affine_le (p : ℝ[X]) (a b : ℝ) (h : ∀ u ∈ Set.Icc (-1 : ℝ) 1, a * u + b ∈ Set.Icc (-1 : ℝ) 1) :
    supN (p.comp (C a * X + C b)) ≤ supN p := by
  unfold supN
  apply csSup_le ((Set.nonempty_Icc.2 (by norm_num)).image _)
  rintro _ ⟨u, hu, rfl⟩
  have := le_supN p (h u hu)
  simp only [eval_comp, eval_add, eval_mul, eval_C, eval_X]
  exact this

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
lemma natDegree_comp_affine_le (p : ℝ[X]) (a b : ℝ) : (p.comp (C a * X + C b)).natDegree ≤ p.natDegree := by
  calc (p.comp (C a * X + C b)).natDegree ≤ p.natDegree * (C a * X + C b).natDegree := natDegree_comp_le
    _ ≤ p.natDegree * 1 := Nat.mul_le_mul_left _ natDegree_linear_le
    _ = p.natDegree := mul_one _

/- English proof (translation)
Take `⟨hx1, hx2⟩` from `hx`. Establish `ha : (0 : ℝ) ≤ (1 + x) / 2` using `by linarith`. Establish `hmap : ∀ u ∈ Set.Icc (-1 : ℝ) 1, (1 + x) / 2 * u + (x - 1) / 2 ∈ Set.Icc (-1 : ℝ) 1`. Introduce and unpack `u ⟨hu1, hu2⟩`. Apply the tactic sequence `constructor <;> nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + x) (by linarith : (0 : ℝ) ≤ u + 1), mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + x) (by linarith : (0 : ℝ) ≤ 1 - u)]`.

Establish `h1` using `end_one n k (p.comp (C ((1 + x) / 2) * X + C ((x - 1) / 2))) ((natDegree_comp_affine_le p _ _).trans hp)`. Rewrite `h1` using `[iter_comp_affine]`. Simplify using `only [eval_mul, eval_C, eval_comp, eval_add, eval_X, mul_one] at h1`. Rewrite `h1` using `[show (1 + x) / 2 + (x - 1) / 2 = x by ring, abs_mul, abs_of_nonneg (pow_nonneg ha k)]`. Conclude with `h1.trans (mul_le_mul_of_nonneg_left (supN_comp_affine_le p _ _ hmap) (vmC_nonneg n k hk))`.
-/
lemma dilate_right (n k : ℕ) (hk : k ≤ n) (p : ℝ[X]) (hp : p.natDegree ≤ n) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    ((1 + x) / 2) ^ k * |(derivative^[k] p).eval x| ≤ vmC n k * supN p := by
  obtain ⟨hx1, hx2⟩ := hx
  have ha : (0 : ℝ) ≤ (1 + x) / 2 := by linarith
  have hmap : ∀ u ∈ Set.Icc (-1 : ℝ) 1, (1 + x) / 2 * u + (x - 1) / 2 ∈ Set.Icc (-1 : ℝ) 1 := by
    rintro u ⟨hu1, hu2⟩
    constructor <;> nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + x) (by linarith : (0 : ℝ) ≤ u + 1),
      mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + x) (by linarith : (0 : ℝ) ≤ 1 - u)]
  have h1 := end_one n k (p.comp (C ((1 + x) / 2) * X + C ((x - 1) / 2))) ((natDegree_comp_affine_le p _ _).trans hp)
  rw [iter_comp_affine] at h1
  simp only [eval_mul, eval_C, eval_comp, eval_add, eval_X, mul_one] at h1
  rw [show (1 + x) / 2 + (x - 1) / 2 = x by ring, abs_mul, abs_of_nonneg (pow_nonneg ha k)] at h1
  exact h1.trans (mul_le_mul_of_nonneg_left (supN_comp_affine_le p _ _ hmap) (vmC_nonneg n k hk))

/- English proof (translation)
Take `⟨hx1, hx2⟩` from `hx`. Establish `ha : (0 : ℝ) ≤ (1 - x) / 2` using `by linarith`. Establish `hmap : ∀ u ∈ Set.Icc (-1 : ℝ) 1, (1 - x) / 2 * u + (x + 1) / 2 ∈ Set.Icc (-1 : ℝ) 1`. Introduce and unpack `u ⟨hu1, hu2⟩`. Apply the tactic sequence `constructor <;> nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - x) (by linarith : (0 : ℝ) ≤ u + 1), mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - x) (by linarith : (0 : ℝ) ≤ 1 - u)]`.

Establish `h1` using `end_neg_one n k (p.comp (C ((1 - x) / 2) * X + C ((x + 1) / 2))) ((natDegree_comp_affine_le p _ _).trans hp)`. Rewrite `h1` using `[iter_comp_affine]`. Simplify using `only [eval_mul, eval_C, eval_comp, eval_add, eval_X, mul_neg, mul_one] at h1`. Rewrite `h1` using `[show -((1 - x) / 2) + (x + 1) / 2 = x by ring, abs_mul, abs_of_nonneg (pow_nonneg ha k)]`. Conclude with `h1.trans (mul_le_mul_of_nonneg_left (supN_comp_affine_le p _ _ hmap) (vmC_nonneg n k hk))`.
-/
lemma dilate_left (n k : ℕ) (hk : k ≤ n) (p : ℝ[X]) (hp : p.natDegree ≤ n) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    ((1 - x) / 2) ^ k * |(derivative^[k] p).eval x| ≤ vmC n k * supN p := by
  obtain ⟨hx1, hx2⟩ := hx
  have ha : (0 : ℝ) ≤ (1 - x) / 2 := by linarith
  have hmap : ∀ u ∈ Set.Icc (-1 : ℝ) 1, (1 - x) / 2 * u + (x + 1) / 2 ∈ Set.Icc (-1 : ℝ) 1 := by
    rintro u ⟨hu1, hu2⟩
    constructor <;> nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - x) (by linarith : (0 : ℝ) ≤ u + 1),
      mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - x) (by linarith : (0 : ℝ) ≤ 1 - u)]
  have h1 := end_neg_one n k (p.comp (C ((1 - x) / 2) * X + C ((x + 1) / 2))) ((natDegree_comp_affine_le p _ _).trans hp)
  rw [iter_comp_affine] at h1
  simp only [eval_mul, eval_C, eval_comp, eval_add, eval_X, mul_neg, mul_one] at h1
  rw [show -((1 - x) / 2) + (x + 1) / 2 = x by ring, abs_mul, abs_of_nonneg (pow_nonneg ha k)] at h1
  exact h1.trans (mul_le_mul_of_nonneg_left (supN_comp_affine_le p _ _ hmap) (vmC_nonneg n k hk))

/- English proof (translation)
Break down `le_total 0 x with h0 | h0` into its components or cases. Rewrite using `[abs_of_nonneg h0]`. Conclude with `dilate_right n k hk p hp hx`. Rewrite using `[abs_of_nonpos h0]`. Use `dilate_left n k hk p hp hx` as an intermediate fact.

Rewrite `this` using `[sub_eq_add_neg]`. Then use the resulting hypothesis.
-/
theorem vMarkov_dilate (n k : ℕ) (hk : k ≤ n) (p : ℝ[X]) (hp : p.natDegree ≤ n) {x : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    ((1 + |x|) / 2) ^ k * |(derivative^[k] p).eval x| ≤ vmC n k * supN p := by
  rcases le_total 0 x with h0 | h0
  · rw [abs_of_nonneg h0]
    exact dilate_right n k hk p hp hx
  · rw [abs_of_nonpos h0]
    have := dilate_left n k hk p hp hx
    rwa [sub_eq_add_neg] at this

/- English proof (translation)
The claim follows from `|(derivative^[k] p).eval x| ≤ 2 ^ k * (vmC n k * supN p) := by have h := vMarkov_dilate n k hk p hp hx have h1 : (1 : ℝ) ≤ 2 ^ k * ((1 + |x|) / 2) ^ k := by rw [← mul_pow] apply one_le_pow₀ have := abs_nonneg x linarith have hD := abs_nonneg ((derivative^[k] p).eval x) calc |(der …`.
-/
theorem vMarkov_two_pow (n k : ℕ) (hk : k ≤ n) (p : ℝ[X]) (hp : p.natDegree ≤ n) {x : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(derivative^[k] p).eval x| ≤ 2 ^ k * (vmC n k * supN p) := by
  have h := vMarkov_dilate n k hk p hp hx
  have h1 : (1 : ℝ) ≤ 2 ^ k * ((1 + |x|) / 2) ^ k := by
    rw [← mul_pow]
    apply one_le_pow₀
    have := abs_nonneg x
    linarith
  have hD := abs_nonneg ((derivative^[k] p).eval x)
  calc |(derivative^[k] p).eval x| ≤ 2 ^ k * ((1 + |x|) / 2) ^ k * |(derivative^[k] p).eval x| :=
        le_mul_of_one_le_left hD h1
    _ = 2 ^ k * (((1 + |x|) / 2) ^ k * |(derivative^[k] p).eval x|) := by ring
    _ ≤ 2 ^ k * (vmC n k * supN p) := mul_le_mul_of_nonneg_left h (by positivity)

end Formalism.MainNotions.InterlacingSignCuts

end

end PartA14v

section PartA15

open MeasureTheory Filter Topology
open scoped ComplexConjugate BoundedContinuousFunction NNReal ENNReal

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts

namespace Hz

abbrev Tor (d : ℕ) := Fin d → UnitAddCircle

def ch {d : ℕ} (n : Fin d → ℤ) (x : Tor d) : ℂ := ∏ j, fourier (n j) (x j)

/- English proof (translation)
Unfold `ch`. Conclude with `continuous_finset_prod _ fun j _ => (fourier (n j)).continuous.comp (continuous_apply j)`.
-/
theorem ch_cont {d : ℕ} (n : Fin d → ℤ) : Continuous (ch n) := by
  unfold ch
  exact continuous_finset_prod _ fun j _ => (fourier (n j)).continuous.comp (continuous_apply j)

/- English proof (translation)
Simplify using `only [ch, Pi.add_apply, fourier_add, Finset.prod_mul_distrib]`.
-/
theorem ch_add {d : ℕ} (m n : Fin d → ℤ) (x : Tor d) : ch (m + n) x = ch m x * ch n x := by
  simp only [ch, Pi.add_apply, fourier_add, Finset.prod_mul_distrib]

/- English proof (translation)
Simplify using `only [ch, Pi.neg_apply, fourier_neg, map_prod]`.
-/
theorem ch_neg {d : ℕ} (n : Fin d → ℤ) (x : Tor d) : ch (-n) x = conj (ch n x) := by
  simp only [ch, Pi.neg_apply, fourier_neg, map_prod]

/- English proof (translation)
Simplify using `[ch, fourier_zero]`.
-/
theorem ch_zero {d : ℕ} (x : Tor d) : ch (0 : Fin d → ℤ) x = 1 := by
  simp [ch, fourier_zero]

/- English proof (translation)
Rewrite using `[sub_eq_add_neg, ch_add, ch_neg]`.
-/
theorem ch_sub {d : ℕ} (m n : Fin d → ℤ) (x : Tor d) : ch (n - m) x = ch n x * conj (ch m x) := by
  rw [sub_eq_add_neg, ch_add, ch_neg]

/- English proof (translation)
The claim follows from `(ch_cont n).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)`.
-/
theorem ch_int {d : ℕ} (μ : Measure (Tor d)) [IsFiniteMeasure μ] (n : Fin d → ℤ) : Integrable (ch n) μ :=
  (ch_cont n).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/- English proof (translation)
Introduce `a`. Establish `key : (∑ m ∈ a.support, ∑ n ∈ a.support, star (a m) * a n * φ (n - m)) = ((∫ x, Complex.normSq (∑ n ∈ a.support, a n * ch n x) ∂μ : ℝ) : ℂ)`. Rewrite using `[← integral_complex_ofReal]`. Establish `: ∀ x : Tor d, ((Complex.normSq (∑ n ∈ a.support, a n * ch n x) : ℝ) : ℂ) = ∑ m ∈ a.support, ∑ n ∈ a.support, star (a m) * a n * ch (n - m) x`. Introduce `x`.

Rewrite using `[Complex.normSq_eq_conj_mul_self, map_sum, Finset.sum_mul_sum]`. Use `Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations. Rewrite using `[ch_sub, map_mul]`. Simplify using `only [Complex.star_def]`. Expand and normalize the polynomial expressions, which then agree.

Repeatedly rewrite using `[this]`. Rewrite using `[integral_finsetSum _ (fun m _ => integrable_finsetSum _ (fun n _ => (ch_int μ _).const_mul _))]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[integral_finsetSum _ (fun n _ => (ch_int μ _).const_mul _)]`. Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations.

Rewrite using `[integral_const_mul, h]`. Rewrite using `[key]`. Use `⟨?_, Complex.ofReal_im _⟩` and prove the remaining obligations. Rewrite using `[Complex.ofReal_re]`. Conclude with `integral_nonneg fun x => Complex.normSq_nonneg _`.
-/
theorem posDef_of_measure {d : ℕ} (φ : (Fin d → ℤ) → ℂ) (μ : Measure (Tor d)) [IsFiniteMeasure μ]
    (h : ∀ n, φ n = ∫ x, ch n x ∂μ) : Formalism.MainNotions.S.UnitaryLevelOperators.IsPosDefZ φ := by
  intro a
  have key : (∑ m ∈ a.support, ∑ n ∈ a.support, star (a m) * a n * φ (n - m)) =
      ((∫ x, Complex.normSq (∑ n ∈ a.support, a n * ch n x) ∂μ : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    have : ∀ x : Tor d, ((Complex.normSq (∑ n ∈ a.support, a n * ch n x) : ℝ) : ℂ) =
        ∑ m ∈ a.support, ∑ n ∈ a.support, star (a m) * a n * ch (n - m) x := by
      intro x
      rw [Complex.normSq_eq_conj_mul_self, map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
      rw [ch_sub, map_mul]
      simp only [Complex.star_def]
      ring
    simp_rw [this]
    rw [integral_finsetSum _ (fun m _ => integrable_finsetSum _ (fun n _ => (ch_int μ _).const_mul _))]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [integral_finsetSum _ (fun n _ => (ch_int μ _).const_mul _)]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [integral_const_mul, h]
  rw [key]
  refine ⟨?_, Complex.ofReal_im _⟩
  rw [Complex.ofReal_re]
  exact integral_nonneg fun x => Complex.normSq_nonneg _

/- English proof (translation)
Set `a : (Fin d → ℤ) →₀ ℂ` to `Finsupp.onFinset S (fun m => if m ∈ S then c m else 0) (fun m hm => by by_contra hS; simp [hS] at hm)`. Establish `ha : ∀ m ∈ S, a m = c m` using `fun m hm => by simp [a, hm]`. Establish `hsub : a.support ⊆ S` using `Finsupp.support_onFinset_subset`. Establish `e : (∑ m ∈ a.support, ∑ n ∈ a.support, star (a m) * a n * φ (n - m)) = ∑ m ∈ S, ∑ n ∈ S, star (c m) * c n * φ (n - m)`. Rewrite using `[Finset.sum_subset hsub (fun m _ hm => by`.

Establish `: a m = 0` using `Finsupp.notMem_support_iff.1 hm`. Simplify using `[this])]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_subset hsub (fun n _ hn => by`. Establish `: a n = 0` using `Finsupp.notMem_support_iff.1 hn`.

Simplify using `[this])]`. Conclude with `Finset.sum_congr rfl fun n hn => by rw [ha m hm, ha n hn]`. Rewrite using `[← e]`. Conclude with `h a`.
-/
theorem posDef_finset {d : ℕ} {φ : (Fin d → ℤ) → ℂ} (h : Formalism.MainNotions.S.UnitaryLevelOperators.IsPosDefZ φ)
    (S : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ) :
    0 ≤ (∑ m ∈ S, ∑ n ∈ S, star (c m) * c n * φ (n - m)).re ∧
      (∑ m ∈ S, ∑ n ∈ S, star (c m) * c n * φ (n - m)).im = 0 := by
  classical
  let a : (Fin d → ℤ) →₀ ℂ := Finsupp.onFinset S (fun m => if m ∈ S then c m else 0)
    (fun m hm => by by_contra hS; simp [hS] at hm)
  have ha : ∀ m ∈ S, a m = c m := fun m hm => by simp [a, hm]
  have hsub : a.support ⊆ S := Finsupp.support_onFinset_subset
  have e : (∑ m ∈ a.support, ∑ n ∈ a.support, star (a m) * a n * φ (n - m)) =
      ∑ m ∈ S, ∑ n ∈ S, star (c m) * c n * φ (n - m) := by
    rw [Finset.sum_subset hsub (fun m _ hm => by
      have : a m = 0 := Finsupp.notMem_support_iff.1 hm
      simp [this])]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.sum_subset hsub (fun n _ hn => by
      have : a n = 0 := Finsupp.notMem_support_iff.1 hn
      simp [this])]
    exact Finset.sum_congr rfl fun n hn => by rw [ha m hm, ha n hn]
  rw [← e]
  exact h a

/- English proof (translation)
Simplify `h (Finsupp.single 0 1)` using `[Finsupp.support_single_ne_zero _ one_ne_zero]`.
-/
theorem posDef_zero {d : ℕ} {φ : (Fin d → ℤ) → ℂ} (h : Formalism.MainNotions.S.UnitaryLevelOperators.IsPosDefZ φ) :
    0 ≤ (φ 0).re ∧ (φ 0).im = 0 := by
  simpa [Finsupp.support_single_ne_zero _ one_ne_zero] using h (Finsupp.single 0 1)

/- English proof (translation)
Establish `h0` using `posDef_zero h`. Distinguish the cases in `hn : n = 0`. Substitute `hn` using the available equality. Simplify using `only [neg_zero]`. Apply the tactic sequence `apply Complex.ext <;> simp [h0.2]`.

Establish `hn' : (0 : Fin d → ℤ) ≠ n` using `fun e => hn e.symm`. Establish `h1` using `(posDef_finset h {0, n} (fun _ => 1)).2`. Establish `h2` using `(posDef_finset h {0, n} (fun m => if m = 0 then 1 else Complex.I)).2`. Rewrite `h1`, `h2` using `[Finset.sum_pair hn', Finset.sum_pair hn', Finset.sum_pair hn']`. Simplify using `[hn, h0.2] at h1 h2`.

Apply `Complex.ext` to reduce the goal to its premises. Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem posDef_herm {d : ℕ} {φ : (Fin d → ℤ) → ℂ} (h : Formalism.MainNotions.S.UnitaryLevelOperators.IsPosDefZ φ) (n : Fin d → ℤ) :
    φ (-n) = conj (φ n) := by
  classical
  have h0 := posDef_zero h
  by_cases hn : n = 0
  · subst hn
    simp only [neg_zero]
    apply Complex.ext <;> simp [h0.2]
  have hn' : (0 : Fin d → ℤ) ≠ n := fun e => hn e.symm
  have h1 := (posDef_finset h {0, n} (fun _ => 1)).2
  have h2 := (posDef_finset h {0, n} (fun m => if m = 0 then 1 else Complex.I)).2
  rw [Finset.sum_pair hn', Finset.sum_pair hn', Finset.sum_pair hn'] at h1 h2
  simp [hn, h0.2] at h1 h2
  apply Complex.ext
  · simp; linarith
  · simp; linarith

/- English proof (translation)
Use `split_ifs with hk`. Substitute `hk` using the available equality. Simplify using `[measureReal_def, AddCircle.measure_univ]`. Conclude with `integral_eq_zero_of_add_right_eq_neg (fourier_add_half_inv_index hk one_pos)`.
-/
theorem int_fourier (k : ℤ) : ∫ x : UnitAddCircle, fourier k x = if k = 0 then 1 else 0 := by
  split_ifs with hk
  · subst hk
    simp [measureReal_def, AddCircle.measure_univ]
  · exact integral_eq_zero_of_add_right_eq_neg (fourier_add_half_inv_index hk one_pos)

/- English proof (translation)
Unfold `ch`. Rewrite using `[integral_fintype_prod_volume_eq_prod (fun j (y : UnitAddCircle) => (fourier (n j) y : ℂ))]`. Repeatedly rewrite using `[int_fourier]`. Rewrite using `[Finset.prod_ite_zero]`. Simplify using `[funext_iff]`.
-/
theorem int_ch {d : ℕ} (n : Fin d → ℤ) : ∫ x : Tor d, ch n x = if n = 0 then 1 else 0 := by
  unfold ch
  rw [integral_fintype_prod_volume_eq_prod (fun j (y : UnitAddCircle) => (fourier (n j) y : ℂ))]
  simp_rw [int_fourier]
  rw [Finset.prod_ite_zero]
  simp [funext_iff]

/- English proof (translation)
Simplify using `only [ch, fourier_coe_apply]`. Rewrite using `[Finset.mul_sum, Complex.exp_sum]`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem ch_coe {d : ℕ} (σ : Fin d → ℤ) (t : Fin d → ℝ) :
    ch σ (fun j => ((t j : ℝ) : UnitAddCircle)) =
      Complex.exp (2 * Real.pi * Complex.I * ∑ j, ((σ j : ℝ) : ℂ) * (t j : ℂ)) := by
  simp only [ch, fourier_coe_apply]
  rw [Finset.mul_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun j _ => ?_
  congr 1
  push_cast
  ring

def box (d N : ℕ) : Finset (Fin d → ℤ) := Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(N : ℤ)) N)

def fw {d : ℕ} (N : ℕ) (σ : Fin d → ℤ) : ℝ := ∏ j, (1 - |((σ j : ℤ) : ℝ)| / ((N : ℝ) + 1))

def fej {d : ℕ} (φ : (Fin d → ℤ) → ℂ) (N : ℕ) (x : Tor d) : ℂ :=
  ∑ σ ∈ box d N, ((fw N σ : ℝ) : ℂ) * φ (-σ) * ch σ x

/- English proof (translation)
Unfold `fej`. Conclude with `continuous_finset_sum _ fun σ _ => continuous_const.mul (ch_cont σ)`.
-/
theorem fej_cont {d : ℕ} (φ : (Fin d → ℤ) → ℂ) (N : ℕ) : Continuous (fej φ N) := by
  unfold fej
  exact continuous_finset_sum _ fun σ _ => continuous_const.mul (ch_cont σ)

/- English proof (translation)
Use `choose t ht using fun j => QuotientAddGroup.mk_surjective (x j)`. Establish `hx : x = fun j => ((t j : ℝ) : UnitAddCircle)` using `funext fun j => (ht j).symm`. Establish `hyp : ∀ (S : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ), 0 ≤ (∑ σ ∈ S, ∑ σ' ∈ S, (fun τ => φ (-τ)) (σ - σ') * c σ * starRingEnd ℂ (c σ')).re`. Introduce `S c`. Use `(posDef_finset h S (fun m => conj (c m))).1` as an intermediate fact.

Use `this using 2` and compare the differences between its conclusion and the goal. Use `Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations. Simplify using `only [neg_sub, Complex.star_def, Complex.conj_conj]`. Expand and normalize the polynomial expressions, which then agree. Establish `core` using `Formalism.FourierDecayAlt.P.herglotz_fejer_Zd d (fun τ => φ (-τ)) hyp N t`.

Rewrite using `[hx]`. Simplify using `only [fej, ch_coe]`. Conclude with `core`.
-/
theorem fej_nonneg {d : ℕ} {φ : (Fin d → ℤ) → ℂ} (h : Formalism.MainNotions.S.UnitaryLevelOperators.IsPosDefZ φ) (N : ℕ) (x : Tor d) :
    0 ≤ (fej φ N x).re := by
  choose t ht using fun j => QuotientAddGroup.mk_surjective (x j)
  have hx : x = fun j => ((t j : ℝ) : UnitAddCircle) := funext fun j => (ht j).symm
  have hyp : ∀ (S : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ),
      0 ≤ (∑ σ ∈ S, ∑ σ' ∈ S, (fun τ => φ (-τ)) (σ - σ') * c σ * starRingEnd ℂ (c σ')).re := by
    intro S c
    have := (posDef_finset h S (fun m => conj (c m))).1
    convert this using 2
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
    simp only [neg_sub, Complex.star_def, Complex.conj_conj]
    ring
  have core := Formalism.FourierDecayAlt.P.herglotz_fejer_Zd d (fun τ => φ (-τ)) hyp N t
  rw [hx]
  simp only [fej, ch_coe]
  exact core

/- English proof (translation)
Unfold `box`. Simplify using `only [Fintype.mem_piFinset, Finset.mem_Icc]`.
-/
theorem mem_box {d N : ℕ} {σ : Fin d → ℤ} : σ ∈ box d N ↔ ∀ j, -(N : ℤ) ≤ σ j ∧ σ j ≤ N := by
  unfold box
  simp only [Fintype.mem_piFinset, Finset.mem_Icc]

/- English proof (translation)
Simplify using `only [fw, Pi.neg_apply, Int.cast_neg, abs_neg]`.
-/
theorem fw_neg {d : ℕ} (N : ℕ) (σ : Fin d → ℤ) : fw N (-σ) = fw N σ := by
  simp only [fw, Pi.neg_apply, Int.cast_neg, abs_neg]

def fmu {d : ℕ} (φ : (Fin d → ℤ) → ℂ) (N : ℕ) : Measure (Tor d) :=
  volume.withDensity (fun x => ((Real.toNNReal (fej φ N x).re : ℝ≥0) : ℝ≥0∞))

/- English proof (translation)
Conclude with `Complex.continuous_re.comp (fej_cont φ N)`.
-/
theorem fre_cont {d : ℕ} (φ : (Fin d → ℤ) → ℂ) (N : ℕ) : Continuous (fun x => (fej φ N x).re) := by
  exact Complex.continuous_re.comp (fej_cont φ N)

instance {d : ℕ} (φ : (Fin d → ℤ) → ℂ) (N : ℕ) : IsFiniteMeasure (fmu φ N) := by
  apply isFiniteMeasure_withDensity
  have hi : Integrable (fun x : Tor d => (fej φ N x).re) volume :=
    (fre_cont φ N).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  exact hi.lintegral_lt_top.ne

/- English proof (translation)
Establish `e : ∀ x : Tor d, fej φ N x * ch n x = ∑ σ ∈ box d N, (((fw N σ : ℝ) : ℂ) * φ (-σ)) * ch (σ + n) x`. Introduce `x`. Rewrite using `[fej, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun σ _ => by rw [ch_add]; ring`. Repeatedly rewrite using `[e]`.

Rewrite using `[integral_finsetSum _ (fun σ _ => (ch_int _ _).const_mul _)]`. Repeatedly rewrite using `[integral_const_mul, int_ch]`. Establish `: ∀ σ : Fin d → ℤ, (σ + n = 0) ↔ (σ = -n)` using `fun σ => eq_neg_iff_add_eq_zero.symm`. Repeatedly rewrite using `[this, mul_ite, mul_one, mul_zero]`. Rewrite using `[Finset.sum_ite_eq' , if_pos hn, fw_neg, neg_neg]`.
-/
theorem int_fej_ch {d : ℕ} (φ : (Fin d → ℤ) → ℂ) (N : ℕ) (n : Fin d → ℤ) (hn : -n ∈ box d N) :
    ∫ x : Tor d, fej φ N x * ch n x = ((fw N n : ℝ) : ℂ) * φ n := by
  classical
  have e : ∀ x : Tor d, fej φ N x * ch n x = ∑ σ ∈ box d N, (((fw N σ : ℝ) : ℂ) * φ (-σ)) * ch (σ + n) x := by
    intro x
    rw [fej, Finset.sum_mul]
    exact Finset.sum_congr rfl fun σ _ => by rw [ch_add]; ring
  simp_rw [e]
  rw [integral_finsetSum _ (fun σ _ => (ch_int _ _).const_mul _)]
  simp_rw [integral_const_mul, int_ch]
  have : ∀ σ : Fin d → ℤ, (σ + n = 0) ↔ (σ = -n) := fun σ => eq_neg_iff_add_eq_zero.symm
  simp_rw [this, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' , if_pos hn, fw_neg, neg_neg]

/- English proof (translation)
Establish `e : ∀ x : Tor d, conj (fej φ N x) * ch n x = ∑ σ ∈ box d N, (((fw N σ : ℝ) : ℂ) * conj (φ (-σ))) * ch (-σ + n) x`. Introduce `x`. Rewrite using `[fej, map_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[ch_add, ch_neg, map_mul, map_mul, Complex.conj_ofReal]`.

Expand and normalize the polynomial expressions, which then agree. Repeatedly rewrite using `[e]`. Rewrite using `[integral_finsetSum _ (fun σ _ => (ch_int _ _).const_mul _)]`. Repeatedly rewrite using `[integral_const_mul, int_ch]`. Establish `: ∀ σ : Fin d → ℤ, (-σ + n = 0) ↔ (σ = n)` using `fun σ => by`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `eq_neg_of_add_eq_zero_right h` as an intermediate fact. Simplify using `using this.symm`. Introduce and unpack `rfl`.

Simplify using the standard rewrite rules. Repeatedly rewrite using `[this, mul_ite, mul_one, mul_zero]`. Rewrite using `[Finset.sum_ite_eq', if_pos hn]`.
-/
theorem int_conj_fej_ch {d : ℕ} (φ : (Fin d → ℤ) → ℂ) (N : ℕ) (n : Fin d → ℤ) (hn : n ∈ box d N) :
    ∫ x : Tor d, conj (fej φ N x) * ch n x = ((fw N n : ℝ) : ℂ) * conj (φ (-n)) := by
  classical
  have e : ∀ x : Tor d, conj (fej φ N x) * ch n x =
      ∑ σ ∈ box d N, (((fw N σ : ℝ) : ℂ) * conj (φ (-σ))) * ch (-σ + n) x := by
    intro x
    rw [fej, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [ch_add, ch_neg, map_mul, map_mul, Complex.conj_ofReal]
    ring
  simp_rw [e]
  rw [integral_finsetSum _ (fun σ _ => (ch_int _ _).const_mul _)]
  simp_rw [integral_const_mul, int_ch]
  have : ∀ σ : Fin d → ℤ, (-σ + n = 0) ↔ (σ = n) := fun σ => by
    constructor
    · intro h; have := eq_neg_of_add_eq_zero_right h; simpa using this.symm
    · rintro rfl; simp
  simp_rw [this, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq', if_pos hn]

/- English proof (translation)
Establish `hn' : -n ∈ box d N`. Rewrite `hn`, the goal using `[mem_box]`. Introduce `j`. Use `hn j` as an intermediate fact. Simplify using `only [Pi.neg_apply]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[fmu, integral_withDensity_eq_integral_smul (fre_cont φ N).measurable.real_toNNReal]`. Establish `e : ∀ x : Tor d, (Real.toNNReal (fej φ N x).re) • ch n x = (1 / 2 : ℂ) * (fej φ N x * ch n x) + (1 / 2 : ℂ) * (conj (fej φ N x) * ch n x)`. Introduce `x`. Rewrite using `[NNReal.smul_def, Real.coe_toNNReal _ (fej_nonneg h N x), Complex.real_smul, Complex.re_eq_add_conj]`.

Expand and normalize the polynomial expressions, which then agree. Repeatedly rewrite using `[e]`. Establish `i1 : Integrable (fun x : Tor d => fej φ N x * ch n x) volume` using `((fej_cont φ N).mul (ch_cont n)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)`. Establish `i2 : Integrable (fun x : Tor d => conj (fej φ N x) * ch n x) volume` using `((Complex.continuous_conj.comp (fej_cont φ N)).mul (ch_cont n)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)`. Rewrite using `[integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul, int_fej_ch φ N n hn', int_conj_fej_ch φ N n hn, posDef_herm h n, Complex.conj_conj]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem int_fmu {d : ℕ} {φ : (Fin d → ℤ) → ℂ} (h : Formalism.MainNotions.S.UnitaryLevelOperators.IsPosDefZ φ) (N : ℕ) (n : Fin d → ℤ)
    (hn : n ∈ box d N) : ∫ x, ch n x ∂(fmu φ N) = ((fw N n : ℝ) : ℂ) * φ n := by
  have hn' : -n ∈ box d N := by
    rw [mem_box] at hn ⊢
    intro j
    have := hn j
    simp only [Pi.neg_apply]
    omega
  rw [fmu, integral_withDensity_eq_integral_smul (fre_cont φ N).measurable.real_toNNReal]
  have e : ∀ x : Tor d, (Real.toNNReal (fej φ N x).re) • ch n x =
      (1 / 2 : ℂ) * (fej φ N x * ch n x) + (1 / 2 : ℂ) * (conj (fej φ N x) * ch n x) := by
    intro x
    rw [NNReal.smul_def, Real.coe_toNNReal _ (fej_nonneg h N x), Complex.real_smul, Complex.re_eq_add_conj]
    ring
  simp_rw [e]
  have i1 : Integrable (fun x : Tor d => fej φ N x * ch n x) volume :=
    ((fej_cont φ N).mul (ch_cont n)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have i2 : Integrable (fun x : Tor d => conj (fej φ N x) * ch n x) volume :=
    ((Complex.continuous_conj.comp (fej_cont φ N)).mul (ch_cont n)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul,
    int_fej_ch φ N n hn', int_conj_fej_ch φ N n hn, posDef_herm h n, Complex.conj_conj]
  ring

/- English proof (translation)
Unfold `fw`. Establish `hj : ∀ j, Tendsto (fun N : ℕ => (1 - |((n j : ℤ) : ℝ)| / ((N : ℝ) + 1))) atTop (𝓝 1)`. Introduce `j`. Establish `h0 : Tendsto (fun N : ℕ => |((n j : ℤ) : ℝ)| / ((N : ℝ) + 1)) atTop (𝓝 0)` using `tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)`. Simplify using `using (tendsto_const_nhds (x := (1 : ℝ))).sub h0`.

Establish `h` using `tendsto_finset_prod Finset.univ (fun j _ => hj j)`. Simplify using `using h`.
-/
theorem fw_tendsto {d : ℕ} (n : Fin d → ℤ) : Tendsto (fun N : ℕ => fw N n) atTop (𝓝 1) := by
  unfold fw
  have hj : ∀ j, Tendsto (fun N : ℕ => (1 - |((n j : ℤ) : ℝ)| / ((N : ℝ) + 1))) atTop (𝓝 1) := by
    intro j
    have h0 : Tendsto (fun N : ℕ => |((n j : ℤ) : ℝ)| / ((N : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h0
  have h := tendsto_finset_prod Finset.univ (fun j _ => hj j)
  simpa using h

/- English proof (translation)
Use `Filter.eventually_atTop.2 ⟨∑ j, (n j).natAbs, fun N hN => mem_box.2 fun j => ?_⟩` and prove the remaining obligations. Establish `h1 : (n j).natAbs ≤ N` using `(Finset.single_le_sum (fun i _ => Nat.zero_le ((n i).natAbs)) (Finset.mem_univ j)).trans hN`. Establish `h2 : ((n j).natAbs : ℤ) ≤ N` using `by exact_mod_cast h1`. Rewrite `h2` using `[← Int.abs_eq_natAbs]`. Conclude with `abs_le.mp h2`.
-/
theorem eventually_mem_box {d : ℕ} (n : Fin d → ℤ) : ∀ᶠ N : ℕ in atTop, n ∈ box d N := by
  refine Filter.eventually_atTop.2 ⟨∑ j, (n j).natAbs, fun N hN => mem_box.2 fun j => ?_⟩
  have h1 : (n j).natAbs ≤ N :=
    (Finset.single_le_sum (fun i _ => Nat.zero_le ((n i).natAbs)) (Finset.mem_univ j)).trans hN
  have h2 : ((n j).natAbs : ℤ) ≤ N := by exact_mod_cast h1
  rw [← Int.abs_eq_natAbs] at h2
  exact abs_le.mp h2

/- English proof (translation)
Establish `h0 : (0 : Fin d → ℤ) ∈ box d N`. Rewrite using `[mem_box]`. Introduce `j`. Simplify using the standard rewrite rules. Use `int_fmu h N 0 h0` as an intermediate fact.

Simplify using `only [ch_zero, integral_const, fw] at this`. Establish `h2` using `congrArg Complex.re this`. Simplify using `using h2`.
-/
theorem mass_fmu {d : ℕ} {φ : (Fin d → ℤ) → ℂ} (h : Formalism.MainNotions.S.UnitaryLevelOperators.IsPosDefZ φ) (N : ℕ) :
    (fmu φ N).real Set.univ = (φ 0).re := by
  have h0 : (0 : Fin d → ℤ) ∈ box d N := by
    rw [mem_box]; intro j; simp
  have := int_fmu h N 0 h0
  simp only [ch_zero, integral_const, fw] at this
  have h2 := congrArg Complex.re this
  simpa using h2

/- English proof (translation)
Set `C : ℝ≥0` to `(φ 0).re.toNNReal`. Set `ν : ℕ → FiniteMeasure (Tor d)` to `fun N => ⟨fmu φ N, inferInstance⟩`. Establish `hK` using `isCompact_setOfPred_finiteMeasure_le_of_compactSpace (Tor d) C`. Establish `hmem : ∀ N, ν N ∈ {μ : FiniteMeasure (Tor d) | μ.mass ≤ C}`. Introduce `N`.

Use `show (ν N).mass ≤ C`. Rewrite using `[← NNReal.coe_le_coe, Real.coe_toNNReal _ (posDef_zero h).1, ← mass_fmu h N]`. Conclude with `le_of_eq rfl`. Take `⟨μ, -, hμ⟩` from `hK.ultrafilter_le_nhds ((hyperfilter ℕ).map ν) (by`. Rewrite using `[le_principal_iff]`.

Conclude with `Filter.mem_map.2 (Filter.univ_mem' hmem))`. Establish `ht : Tendsto ν (hyperfilter ℕ : Filter ℕ) (𝓝 μ)` using `hμ`. Rewrite `ht` using `[FiniteMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ]`. Use `⟨μ, inferInstance, fun n => ?_⟩` and prove the remaining obligations. Establish `t1` using `ht (BoundedContinuousFunction.mkOfCompact ⟨ch n, ch_cont n⟩)`.

Establish `t2 : Tendsto (fun N => ∫ x, ch n x ∂(fmu φ N)) atTop (𝓝 (φ n))`. Establish `a1 : Tendsto (fun N : ℕ => ((fw N n : ℝ) : ℂ) * φ n) atTop (𝓝 (((1 : ℝ) : ℂ) * φ n))` using `((Complex.continuous_ofReal.tendsto _).comp (fw_tendsto n)).mul_const _`. Rewrite `a1` using `[Complex.ofReal_one, one_mul]`. Use `a1.congr' ?_` and prove the remaining obligations. Conclude with `(eventually_mem_box n).mono fun N hN => (int_fmu h N n hN).symm`.

Establish `t3` using `t2.mono_left Nat.hyperfilter_le_atTop`. Conclude with `tendsto_nhds_unique t3 t1`.
-/
theorem measure_of_posDef {d : ℕ} {φ : (Fin d → ℤ) → ℂ} (h : Formalism.MainNotions.S.UnitaryLevelOperators.IsPosDefZ φ) :
    ∃ μ : Measure (Tor d), IsFiniteMeasure μ ∧ ∀ n, φ n = ∫ x, ch n x ∂μ := by
  let C : ℝ≥0 := (φ 0).re.toNNReal
  let ν : ℕ → FiniteMeasure (Tor d) := fun N => ⟨fmu φ N, inferInstance⟩
  have hK := isCompact_setOfPred_finiteMeasure_le_of_compactSpace (Tor d) C
  have hmem : ∀ N, ν N ∈ {μ : FiniteMeasure (Tor d) | μ.mass ≤ C} := by
    intro N
    show (ν N).mass ≤ C
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (posDef_zero h).1, ← mass_fmu h N]
    exact le_of_eq rfl
  obtain ⟨μ, -, hμ⟩ := hK.ultrafilter_le_nhds ((hyperfilter ℕ).map ν)
    (by
      rw [le_principal_iff]
      exact Filter.mem_map.2 (Filter.univ_mem' hmem))
  have ht : Tendsto ν (hyperfilter ℕ : Filter ℕ) (𝓝 μ) := hμ
  rw [FiniteMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ] at ht
  refine ⟨μ, inferInstance, fun n => ?_⟩
  have t1 := ht (BoundedContinuousFunction.mkOfCompact ⟨ch n, ch_cont n⟩)
  have t2 : Tendsto (fun N => ∫ x, ch n x ∂(fmu φ N)) atTop (𝓝 (φ n)) := by
    have a1 : Tendsto (fun N : ℕ => ((fw N n : ℝ) : ℂ) * φ n) atTop (𝓝 (((1 : ℝ) : ℂ) * φ n)) :=
      ((Complex.continuous_ofReal.tendsto _).comp (fw_tendsto n)).mul_const _
    rw [Complex.ofReal_one, one_mul] at a1
    refine a1.congr' ?_
    exact (eventually_mem_box n).mono fun N hN => (int_fmu h N n hN).symm
  have t3 := t2.mono_left Nat.hyperfilter_le_atTop
  exact tendsto_nhds_unique t3 t1

end Hz

/- English proof (translation)
Introduce `d φ`. Prove the components needed by the constructor for the conclusion. Conclude with `fun h => Hz.measure_of_posDef h`. Introduce and unpack `⟨μ, hμ, h⟩`. Conclude with `Hz.posDef_of_measure φ μ h`.
-/
theorem stHerglotz_of_core : Formalism.MainNotions.S.UnitaryLevelOperators.stHerglotz := by
  intro d φ
  constructor
  · exact fun h => Hz.measure_of_posDef h
  · rintro ⟨μ, hμ, h⟩
    exact Hz.posDef_of_measure φ μ h

end Formalism.MainNotions.InterlacingSignCuts

end

end PartA15

section PartA16

open Complex Real MeasureTheory
open scoped SchwartzMap FourierTransform RealInnerProductSpace

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts

section Std

variable (d : ℕ)

abbrev stB : Module.Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)) := (EuclideanSpace.basisFun (Fin d) ℝ).toBasis

abbrev stL : Submodule ℤ (EuclideanSpace ℝ (Fin d)) := Submodule.span ℤ (Set.range (stB d))

variable {d}

def zp (n : Fin d → ℤ) : EuclideanSpace ℝ (Fin d) := (WithLp.equiv 2 _).symm (fun j => (n j : ℝ))

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma zp_apply (n : Fin d → ℤ) (j : Fin d) : (zp n).ofLp j = (n j : ℝ) := rfl

/- English proof (translation)
Simplify using `[stB]`.
-/
lemma stB_eq (i : Fin d) : stB d i = EuclideanSpace.single i (1 : ℝ) := by
  simp [stB]

/- English proof (translation)
Rewrite using `[stB_eq]`. Simplify using `[PiLp.single_apply]`.
-/
lemma stB_apply (i j : Fin d) : (stB d i).ofLp j = if j = i then (1 : ℝ) else 0 := by
  rw [stB_eq]; simp [PiLp.single_apply]

/- English proof (translation)
Rewrite using `[stB_eq, EuclideanSpace.inner_single_right]`. Simplify using the standard rewrite rules.
-/
lemma inner_stB (x : EuclideanSpace ℝ (Fin d)) (j : Fin d) : ⟪x, stB d j⟫ = x.ofLp j := by
  rw [stB_eq, EuclideanSpace.inner_single_right]; simp

/- English proof (translation)
Use extensionality with `j`. Simplify using `only [WithLp.ofLp_sum, zp_apply]`. Rewrite using `[Finset.sum_apply]`. Simplify using `only [PiLp.smul_apply, stB_apply, smul_ite, smul_zero]`. Simplify using `[zsmul_eq_mul]`.
-/
lemma stB_sum (m : Fin d → ℤ) : ∑ i, m i • stB d i = zp m := by
  ext j
  simp only [WithLp.ofLp_sum, zp_apply]
  rw [Finset.sum_apply]
  simp only [PiLp.smul_apply, stB_apply, smul_ite, smul_zero]
  simp [zsmul_eq_mul]

/- English proof (translation)
Introduce `x y h`. Use function extensionality and compare the values at `i`. Use `congrArg (fun v : EuclideanSpace ℝ (Fin d) => v.ofLp i) h` as an intermediate fact. Simplify using `only [zp_apply] at this`. Conclude with `this` after adjusting the coercions.
-/
lemma zp_injective : Function.Injective (zp (d := d)) := by
  intro x y h
  funext i
  have := congrArg (fun v : EuclideanSpace ℝ (Fin d) => v.ofLp i) h
  simp only [zp_apply] at this
  exact_mod_cast this

variable (d) in

def latE : (Fin d → ℤ) ≃ stL d :=
  Equiv.ofBijective (fun m => ⟨zp m, by
      rw [← stB_sum]
      exact (Submodule.mem_span_range_iff_exists_fun ℤ).2 ⟨m, rfl⟩⟩)
    ⟨fun m m' h => zp_injective (congrArg Subtype.val h),
     fun v => by
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 v.2
      exact ⟨c, Subtype.ext (by simp only; rw [← stB_sum, hc])⟩⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma latE_apply (m : Fin d → ℤ) : ((latE d m : stL d) : EuclideanSpace ℝ (Fin d)) = zp m := rfl

/- English proof (translation)
Use extensionality with `j`. Establish `h` using `Formalism.H.inner_dualVec_basis (stB d) k j`. Rewrite `h` using `[inner_stB]`. Rewrite using `[zp_apply, h]`.
-/
lemma dualVec_stB (k : Fin d → ℤ) : Formalism.H.dualVec (stB d) k = zp k := by
  ext j
  have h := Formalism.H.inner_dualVec_basis (stB d) k j
  rw [inner_stB] at h
  rw [zp_apply, h]

/- English proof (translation)
Establish `hli : LinearIndependent ℤ (stB d)` using `(stB d).linearIndependent.restrict_scalars' ℤ`. Rewrite using `[ZLattice.covolume_eq_det_mul_measureReal (stL d) volume (Module.Basis.span hli) (EuclideanSpace.basisFun (Fin d) ℝ).toBasis]`. Establish `: ((↑) : stL d → EuclideanSpace ℝ (Fin d)) ∘ (Module.Basis.span hli) = stB d`. Use function extensionality and compare the values at `i`. Conclude with `congrArg Subtype.val (Module.Basis.span_apply hli i)`.

Rewrite using `[this, Formalism.H.covolDual_vol_fd, mul_one, Module.Basis.det_self]`. Simplify using the standard rewrite rules.
-/
lemma covolume_stL : ZLattice.covolume (stL d) = 1 := by
  classical
  have hli : LinearIndependent ℤ (stB d) := (stB d).linearIndependent.restrict_scalars' ℤ
  rw [ZLattice.covolume_eq_det_mul_measureReal (stL d) volume (Module.Basis.span hli)
    (EuclideanSpace.basisFun (Fin d) ℝ).toBasis]
  have : ((↑) : stL d → EuclideanSpace ℝ (Fin d)) ∘ (Module.Basis.span hli) = stB d := by
    funext i; exact congrArg Subtype.val (Module.Basis.span_apply hli i)
  rw [this, Formalism.H.covolDual_vol_fd, mul_one, Module.Basis.det_self]
  simp

/- English proof (translation)
Rewrite using `[Formalism.H.dualEquiv_apply, dualVec_stB]`.
-/
lemma dualEquiv_stB (k : Fin d → ℤ) :
    ((Formalism.H.dualEquiv (stB d) k : Formalism.H.dual (stL d)) : EuclideanSpace ℝ (Fin d)) = zp k := by
  rw [Formalism.H.dualEquiv_apply, dualVec_stB]

/- English proof (translation)
Take `⟨hs, hh⟩` from `Formalism.H.poissonSchwartz (EuclideanSpace ℝ (Fin d)) (stL d) Ψ 0`. Establish `key : ∀ k : Fin d → ℤ, (𝓕 (Ψ : EuclideanSpace ℝ (Fin d) → ℂ) : EuclideanSpace ℝ (Fin d) → ℂ) ((Formalism.H.dualEquiv (stB d) k : Formalism.H.dual (stL d)) : EuclideanSpace ℝ (Fin d)) * Complex.exp (2 * Real.pi * Complex.I * (⟪((Formalism.H.dualEquiv (stB d) k : Formalism.H.dual ( …`. Introduce `k`. Rewrite using `[dualEquiv_stB]`. Simplify using the standard rewrite rules.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `h1` using `(Equiv.summable_iff (Formalism.H.dualEquiv (stB d))).2 hs`. Simplify `h1` using `only [Function.comp_def, key]`. Establish `h2` using `(Equiv.hasSum_iff (latE d)).2 hh`. Rewrite `h2` using `[covolume_stL, ← Equiv.tsum_eq (Formalism.H.dualEquiv (stB d))]`.

Simplify using `only [key] at h2`. Simplify `h2` using `[Function.comp_def, latE_apply]`.
-/
lemma poisson_std (Ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) :
    Summable (fun k : Fin d → ℤ =>
      (𝓕 (Ψ : EuclideanSpace ℝ (Fin d) → ℂ) : EuclideanSpace ℝ (Fin d) → ℂ) (zp k)) ∧
    HasSum (fun l : Fin d → ℤ => Ψ (zp l))
      (∑' k : Fin d → ℤ, (𝓕 (Ψ : EuclideanSpace ℝ (Fin d) → ℂ) : EuclideanSpace ℝ (Fin d) → ℂ) (zp k)) := by
  obtain ⟨hs, hh⟩ := Formalism.H.poissonSchwartz (EuclideanSpace ℝ (Fin d)) (stL d) Ψ 0
  have key : ∀ k : Fin d → ℤ,
      (𝓕 (Ψ : EuclideanSpace ℝ (Fin d) → ℂ) : EuclideanSpace ℝ (Fin d) → ℂ)
          ((Formalism.H.dualEquiv (stB d) k : Formalism.H.dual (stL d)) : EuclideanSpace ℝ (Fin d)) *
        Complex.exp (2 * Real.pi * Complex.I *
          (⟪((Formalism.H.dualEquiv (stB d) k : Formalism.H.dual (stL d)) : EuclideanSpace ℝ (Fin d)),
            (0 : EuclideanSpace ℝ (Fin d))⟫ : ℝ)) =
      (𝓕 (Ψ : EuclideanSpace ℝ (Fin d) → ℂ) : EuclideanSpace ℝ (Fin d) → ℂ) (zp k) := by
    intro k
    rw [dualEquiv_stB]; simp
  refine ⟨?_, ?_⟩
  · have h1 := (Equiv.summable_iff (Formalism.H.dualEquiv (stB d))).2 hs
    simpa only [Function.comp_def, key] using h1
  · have h2 := (Equiv.hasSum_iff (latE d)).2 hh
    rw [covolume_stL, ← Equiv.tsum_eq (Formalism.H.dualEquiv (stB d))] at h2
    simp only [key] at h2
    simpa [Function.comp_def, latE_apply] using h2

/- English proof (translation)
Rewrite using `[Real.fourier_eq']`. Use `integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Simplify using `only [smul_eq_mul]`. Use `congr 2`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
lemma fhat_eq (f : EuclideanSpace ℝ (Fin d) → ℂ) (w : EuclideanSpace ℝ (Fin d)) :
    (∫ x, Complex.exp (-(2 * Real.pi * Complex.I * (inner ℝ x w : ℝ))) * f x) = (𝓕 f : _ → ℂ) w := by
  rw [Real.fourier_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul]
  congr 2
  push_cast
  ring

end Std

/- English proof (translation)
Introduce `d f`. Take `⟨hs, hh⟩` from `poisson_std f`. Establish `e : (fun m : Fin d → ℤ => Formalism.MainNotions.S.UnitaryLevelOperators.fhat (fun x => f x) (Formalism.MainNotions.S.UnitaryLevelOperators.zpt m)) = fun k : Fin d → ℤ => (𝓕 (f : EuclideanSpace ℝ (Fin d) → ℂ) : EuclideanSpace ℝ (Fin d) → ℂ) (zp k)`. Use function extensionality and compare the values at `m`. Conclude with `fhat_eq _ _`.

Use `⟨hh.summable, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[e]`. Conclude with `hs`. Rewrite using `[e]`. Conclude with `hh.tsum_eq`.
-/
theorem stPoisson_of_core : Formalism.MainNotions.S.UnitaryLevelOperators.stPoisson := by
  intro d f
  obtain ⟨hs, hh⟩ := poisson_std f
  have e : (fun m : Fin d → ℤ => Formalism.MainNotions.S.UnitaryLevelOperators.fhat (fun x => f x) (Formalism.MainNotions.S.UnitaryLevelOperators.zpt m)) =
      fun k : Fin d → ℤ => (𝓕 (f : EuclideanSpace ℝ (Fin d) → ℂ) : EuclideanSpace ℝ (Fin d) → ℂ) (zp k) := by
    funext m
    exact fhat_eq _ _
  refine ⟨hh.summable, ?_, ?_⟩
  · rw [e]; exact hs
  · rw [e]; exact hh.tsum_eq

end Formalism.MainNotions.InterlacingSignCuts

end

end PartA16

section PartA17m

open MeasureTheory Complex Filter
open scoped FourierTransform ContDiff SchwartzMap Real

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts.SP

/- English proof (translation)
Establish `h` using `Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℂ) (f := cexp) (C := 1) (s := {w : ℂ | w.re ≤ 0}) (x := 0) (y := -z) (fun x _ => Complex.differentiableAt_exp) (fun x hx => by`. Rewrite using `[Complex.deriv_exp, Complex.norm_exp]`. Conclude with `Real.exp_le_one_iff.2 hx)`. Use the proof step `(convex_halfSpace_re_le 0) (by simp) (by simpa using hz)`. Simplify using `using h`.
-/
theorem norm_exp_neg_sub_one_le {z : ℂ} (hz : 0 ≤ z.re) : ‖cexp (-z) - 1‖ ≤ ‖z‖ := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℂ) (f := cexp) (C := 1) (s := {w : ℂ | w.re ≤ 0})
    (x := 0) (y := -z) (fun x _ => Complex.differentiableAt_exp)
    (fun x hx => by
      rw [Complex.deriv_exp, Complex.norm_exp]
      exact Real.exp_le_one_iff.2 hx)
    (convex_halfSpace_re_le 0) (by simp) (by simpa using hz)
  simpa using h

/- English proof (translation)
Rewrite using `[Real.fourier_real_eq_integral_exp_smul]`. Establish `h` using `fourierIntegral_gaussian hb (-2 * π * ξ)`. Establish `hb0 : b ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hb`.

Establish `e : (-(-2 * (π : ℂ) * ξ) ^ 2 / (4 * b)) = -(π ^ 2 * ξ ^ 2 / b)`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite `h` using `[e]`. Rewrite using `[← h]`.

Use `congr 1`. Use extensionality with `v`. Rewrite using `[smul_eq_mul]`. Use `congr 2`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem fourier_gauss (b : ℂ) (hb : 0 < b.re) (ξ : ℝ) :
    𝓕 (fun v : ℝ => cexp (-b * v ^ 2)) ξ = (π / b) ^ (1 / 2 : ℂ) * cexp (-(π ^ 2 * ξ ^ 2 / b)) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have h := fourierIntegral_gaussian hb (-2 * π * ξ)
  have hb0 : b ≠ 0 := by
    rintro rfl; simp at hb
  have e : (-(-2 * (π : ℂ) * ξ) ^ 2 / (4 * b)) = -(π ^ 2 * ξ ^ 2 / b) := by
    field_simp
    ring
  rw [e] at h
  rw [← h]
  congr 1
  ext v
  rw [smul_eq_mul]
  congr 2
  push_cast
  ring

/- English proof (translation)
Establish `hg : 𝓕 (𝓕⁻ g) = g` using `FourierTransform.fourier_fourierInv_eq g`. Establish `J : Integrable (fun v : ℝ => cexp (-b * v ^ 2))`. Simplify using `using GaussianFourier.integrable_cexp_neg_mul_sq_add_real_mul_I hb 0`. Establish `key : ∫ ξ : ℝ, 𝓕 (fun v : ℝ => cexp (-b * v ^ 2)) ξ • (𝓕⁻ g) ξ = ∫ v : ℝ, cexp (-b * v ^ 2) • 𝓕 ((𝓕⁻ g : 𝓢(ℝ, ℂ)) : ℝ → ℂ) v`. Simplify using `using! (VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ) Real.continuous_fourierChar continuous_inner J (𝓕⁻ g).integrable)`.

Establish `h2 : ∀ v : ℝ, 𝓕 ((𝓕⁻ g : 𝓢(ℝ, ℂ)) : ℝ → ℂ) v = g v`. Introduce `v`. Rewrite using `[← SchwartzMap.fourier_coe, hg]`. Simplify using `only [h2, smul_eq_mul] at key`. Rewrite using `[← key, ← integral_const_mul]`.

Use `congr 1`. Use extensionality with `ξ`. Rewrite using `[fourier_gauss b hb]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gauss_schwartz (g : 𝓢(ℝ, ℂ)) (b : ℂ) (hb : 0 < b.re) :
    ∫ v : ℝ, cexp (-b * v ^ 2) * g v =
      (π / b) ^ (1 / 2 : ℂ) * ∫ ξ : ℝ, cexp (-(π ^ 2 * ξ ^ 2 / b)) * (𝓕⁻ g) ξ := by
  have hg : 𝓕 (𝓕⁻ g) = g := FourierTransform.fourier_fourierInv_eq g
  have J : Integrable (fun v : ℝ => cexp (-b * v ^ 2)) := by
    simpa using GaussianFourier.integrable_cexp_neg_mul_sq_add_real_mul_I hb 0
  have key : ∫ ξ : ℝ, 𝓕 (fun v : ℝ => cexp (-b * v ^ 2)) ξ • (𝓕⁻ g) ξ =
      ∫ v : ℝ, cexp (-b * v ^ 2) • 𝓕 ((𝓕⁻ g : 𝓢(ℝ, ℂ)) : ℝ → ℂ) v := by
    simpa using! (VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
      Real.continuous_fourierChar continuous_inner J (𝓕⁻ g).integrable)
  have h2 : ∀ v : ℝ, 𝓕 ((𝓕⁻ g : 𝓢(ℝ, ℂ)) : ℝ → ℂ) v = g v := by
    intro v
    rw [← SchwartzMap.fourier_coe, hg]
  simp only [h2, smul_eq_mul] at key
  rw [← key, ← integral_const_mul]
  congr 1
  ext ξ
  rw [fourier_gauss b hb]
  ring

/- English proof (translation)
Establish `: ((π : ℂ) ^ 2 * ξ ^ 2 / b) = ((π ^ 2 * ξ ^ 2 : ℝ) : ℂ) * b⁻¹` using `by push_cast; rw [div_eq_mul_inv]`. Rewrite using `[this, Complex.re_ofReal_mul, Complex.inv_re]`. Establish `h1 : 0 < Complex.normSq b` using `Complex.normSq_pos.2 (by rintro rfl; simp at hb)`. Check the signs of the components of the expression.
-/
theorem re_quot_nonneg (b : ℂ) (hb : 0 < b.re) (ξ : ℝ) : 0 ≤ ((π : ℂ) ^ 2 * ξ ^ 2 / b).re := by
  have : ((π : ℂ) ^ 2 * ξ ^ 2 / b) = ((π ^ 2 * ξ ^ 2 : ℝ) : ℂ) * b⁻¹ := by push_cast; rw [div_eq_mul_inv]
  rw [this, Complex.re_ofReal_mul, Complex.inv_re]
  have h1 : 0 < Complex.normSq b := Complex.normSq_pos.2 (by rintro rfl; simp at hb)
  positivity

/- English proof (translation)
Rewrite using `[norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem norm_quot (b : ℂ) (ξ : ℝ) : ‖((π : ℂ) ^ 2 * ξ ^ 2 / b)‖ = π ^ 2 / ‖b‖ * ‖ξ‖ ^ 2 := by
  rw [norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  ring

/- English proof (translation)
Rewrite using `[gauss_schwartz g b hb]`. Establish `h0 : g 0 = ∫ ξ : ℝ, (𝓕⁻ g) ξ`. Establish `hg : 𝓕 (𝓕⁻ g) = g` using `FourierTransform.fourier_fourierInv_eq g`. Use `conv_lhs => rw [← hg]`. Rewrite using `[SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]`.

Simplify using the standard rewrite rules. Establish `hle : ∀ ξ : ℝ, ‖cexp (-((π : ℂ) ^ 2 * ξ ^ 2 / b))‖ ≤ 1`. Introduce `ξ`. Rewrite using `[Complex.norm_exp]`. Apply `Real.exp_le_one_iff.2` to reduce the goal to its premises.

Simplify using `using re_quot_nonneg b hb ξ`. Establish `int1 : Integrable (fun ξ : ℝ => cexp (-((π : ℂ) ^ 2 * ξ ^ 2 / b)) * (𝓕⁻ g) ξ)`. Use `(𝓕⁻ g).integrable.mono ?_ (Filter.Eventually.of_forall fun ξ => ?_)` and prove the remaining obligations. Apply `Continuous.aestronglyMeasurable` to reduce the goal to its premises. Use `(𝓕⁻ g).continuous` as an intermediate fact.

Use `fun_prop`. Rewrite using `[norm_mul]`. Conclude with `(mul_le_mul_of_nonneg_right (hle ξ) (norm_nonneg _)).trans (one_mul _).le`. Rewrite using `[h0, ← mul_sub, norm_mul]`. Use `gcongr`.

Rewrite using `[← integral_sub int1 (𝓕⁻ g).integrable, ← integral_const_mul]`. Use `(norm_integral_le_integral_norm _).trans ?_` and prove the remaining obligations. Use `integral_mono (int1.sub (𝓕⁻ g).integrable).norm (((𝓕⁻ g).integrable_pow_mul volume 2).const_mul _) fun ξ => ?_` and prove the remaining obligations. Use `show ‖cexp (-((π : ℂ) ^ 2 * ξ ^ 2 / b)) * (𝓕⁻ g) ξ - (𝓕⁻ g) ξ‖ ≤ π ^ 2 / ‖b‖ * (‖ξ‖ ^ 2 * ‖(𝓕⁻ g) ξ‖)`. Establish `: cexp (-((π : ℂ) ^ 2 * ξ ^ 2 / b)) * (𝓕⁻ g) ξ - (𝓕⁻ g) ξ = (cexp (-((π : ℂ) ^ 2 * ξ ^ 2 / b)) - 1) * (𝓕⁻ g) ξ` using `by ring`.

Rewrite using `[this, norm_mul, ← mul_assoc, ← norm_quot]`. Use `gcongr`. Conclude with `norm_exp_neg_sub_one_le (re_quot_nonneg b hb ξ)`.
-/
theorem gauss_schwartz_bound (g : 𝓢(ℝ, ℂ)) (b : ℂ) (hb : 0 < b.re) :
    ‖(∫ v : ℝ, cexp (-b * v ^ 2) * g v) - (π / b) ^ (1 / 2 : ℂ) * g 0‖ ≤
      ‖((π : ℂ) / b) ^ (1 / 2 : ℂ)‖ * (π ^ 2 / ‖b‖ * ∫ ξ : ℝ, ‖ξ‖ ^ 2 * ‖(𝓕⁻ g) ξ‖) := by
  rw [gauss_schwartz g b hb]
  have h0 : g 0 = ∫ ξ : ℝ, (𝓕⁻ g) ξ := by
    have hg : 𝓕 (𝓕⁻ g) = g := FourierTransform.fourier_fourierInv_eq g
    conv_lhs => rw [← hg]
    rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]
    simp
  have hle : ∀ ξ : ℝ, ‖cexp (-((π : ℂ) ^ 2 * ξ ^ 2 / b))‖ ≤ 1 := by
    intro ξ
    rw [Complex.norm_exp]
    apply Real.exp_le_one_iff.2
    simpa using re_quot_nonneg b hb ξ
  have int1 : Integrable (fun ξ : ℝ => cexp (-((π : ℂ) ^ 2 * ξ ^ 2 / b)) * (𝓕⁻ g) ξ) := by
    refine (𝓕⁻ g).integrable.mono ?_ (Filter.Eventually.of_forall fun ξ => ?_)
    · apply Continuous.aestronglyMeasurable
      have := (𝓕⁻ g).continuous
      fun_prop
    · rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (hle ξ) (norm_nonneg _)).trans (one_mul _).le
  rw [h0, ← mul_sub, norm_mul]
  gcongr
  rw [← integral_sub int1 (𝓕⁻ g).integrable, ← integral_const_mul]
  refine (norm_integral_le_integral_norm _).trans ?_
  refine integral_mono (int1.sub (𝓕⁻ g).integrable).norm (((𝓕⁻ g).integrable_pow_mul volume 2).const_mul _) fun ξ => ?_
  show ‖cexp (-((π : ℂ) ^ 2 * ξ ^ 2 / b)) * (𝓕⁻ g) ξ - (𝓕⁻ g) ξ‖ ≤ π ^ 2 / ‖b‖ * (‖ξ‖ ^ 2 * ‖(𝓕⁻ g) ξ‖)
  have : cexp (-((π : ℂ) ^ 2 * ξ ^ 2 / b)) * (𝓕⁻ g) ξ - (𝓕⁻ g) ξ =
      (cexp (-((π : ℂ) ^ 2 * ξ ^ 2 / b)) - 1) * (𝓕⁻ g) ξ := by ring
  rw [this, norm_mul, ← mul_assoc, ← norm_quot]
  gcongr
  exact norm_exp_neg_sub_one_le (re_quot_nonneg b hb ξ)

/- English proof (translation)
Break down `hσ with rfl | rfl` into its components or cases. Establish `: I * ((π : ℂ) * (1 : ℝ) / 4) = ((π / 4 : ℝ) : ℂ) * I` using `by push_cast; ring`. Rewrite using `[this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_four, Real.sin_pi_div_four]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `: I * ((π : ℂ) * ((-1 : ℝ) : ℂ) / 4) = ((-(π / 4) : ℝ) : ℂ) * I` using `by push_cast; ring`. Rewrite using `[this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four, Real.sin_pi_div_four]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem w_eq (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    cexp (I * (π * σ / 4)) = ((√2 / 2 : ℝ) : ℂ) * (1 + σ * I) := by
  rcases hσ with rfl | rfl
  · have : I * ((π : ℂ) * (1 : ℝ) / 4) = ((π / 4 : ℝ) : ℂ) * I := by push_cast; ring
    rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_four,
      Real.sin_pi_div_four]
    push_cast; ring
  · have : I * ((π : ℂ) * ((-1 : ℝ) : ℂ) / 4) = ((-(π / 4) : ℝ) : ℂ) * I := by push_cast; ring
    rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg,
      Real.cos_pi_div_four, Real.sin_pi_div_four]
    push_cast; ring

/- English proof (translation)
Rewrite using `[one_div]`. Conclude with `Complex.cpow_nat_inv_pow x two_ne_zero` after adjusting the coercions.
-/
theorem cpow_half_sq (x : ℂ) : (x ^ (1 / 2 : ℂ)) ^ 2 = x := by
  rw [one_div]
  exact_mod_cast Complex.cpow_nat_inv_pow x two_ne_zero

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Substitute `hx` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[Complex.cpow_def_of_ne_zero hx, Complex.exp_re]`. Apply `mul_nonneg (Real.exp_pos _).le` to reduce the goal to its premises.

Establish `him : (Complex.log x * (1 / 2 : ℂ)).im = Complex.arg x / 2`. Establish `: (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ)` using `by push_cast; rfl`. Rewrite using `[this, Complex.im_mul_ofReal, Complex.log_im]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[him]`.

Apply `Real.cos_nonneg_of_neg_pi_div_two_le_of_le` to reduce the goal to its premises. Use `Complex.neg_pi_lt_arg x` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `Complex.arg_le_pi x` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem cpow_half_re_nonneg (x : ℂ) : 0 ≤ (x ^ (1 / 2 : ℂ)).re := by
  by_cases hx : x = 0
  · subst hx; simp
  rw [Complex.cpow_def_of_ne_zero hx, Complex.exp_re]
  apply mul_nonneg (Real.exp_pos _).le
  have him : (Complex.log x * (1 / 2 : ℂ)).im = Complex.arg x / 2 := by
    have : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.im_mul_ofReal, Complex.log_im]; ring
  rw [him]
  apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le
  · have := Complex.neg_pi_lt_arg x; linarith
  · have := Complex.arg_le_pi x; linarith

/- English proof (translation)
Use `set x : ℂ := (π : ℂ) / ((1 - I * σ * l) / 2) with hx`. Use `set A : ℂ := x ^ (1 / 2 : ℂ) with hA`. Use `set s : ℝ := √(2 * π / l) with hs`. Use `set B : ℂ := (s : ℂ) * cexp (I * (π * σ / 4)) with hB`. Apply the tactic sequence `have hσ2 : σ ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num`.

Establish `hσ2c : (σ : ℂ) ^ 2 = 1` using `by exact_mod_cast hσ2`. Establish `hs2 : s ^ 2 = 2 * π / l` using `Real.sq_sqrt (by positivity)`. Establish `hs2c : (s : ℂ) ^ 2 = 2 * π / l` using `by exact_mod_cast hs2`. Establish `h2 : ((√2 / 2 : ℝ) : ℂ) ^ 2 = 1 / 2`. Establish `: (√2 / 2 : ℝ) ^ 2 = 1 / 2` using `by rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num`.

Rewrite using `[← Complex.ofReal_pow, this]`. Use `push_cast`. Both sides reduce to the same expression. Establish `hB2 : B ^ 2 = 2 * π / l * (σ * I)`. Rewrite using `[hB, w_eq σ hσ, mul_pow, mul_pow, hs2c, h2]`.

Establish `: (1 + (σ : ℂ) * I) ^ 2 = 2 * (σ * I)`. Establish `: (1 + (σ : ℂ) * I) ^ 2 = 1 + 2 * (σ * I) + σ ^ 2 * I ^ 2` using `by ring`. Rewrite using `[this, hσ2c, Complex.I_sq]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hBre : B.re = s * (√2 / 2)`. Rewrite using `[hB, w_eq σ hσ, Complex.re_ofReal_mul, Complex.re_ofReal_mul]`. Simplify using the standard rewrite rules. Establish `hd : (1 - I * σ * l : ℂ) ≠ 0`.

Introduce `h`. Use `congrArg Complex.re h` as an intermediate fact. Simplify using `at this`. Establish `hlc : (l : ℂ) ≠ 0` using `by exact_mod_cast hl.ne'`. Establish `hdiff : A ^ 2 - B ^ 2 = -(2 * π * σ * I) / (l * (1 - I * σ * l))`.

Rewrite using `[hA, cpow_half_sq, hB2, hx]`. Clear the denominators using the available nonvanishing facts. Establish `: (σ : ℂ) * I * (1 - I * σ * l) = σ * I - σ ^ 2 * I ^ 2 * l` using `by ring`. Put the polynomial expressions in normal form. Rewrite using `[hσ2c, Complex.I_sq]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hnd : l ≤ ‖(1 - I * σ * l : ℂ)‖`. Establish `h1 : |(1 - I * σ * l : ℂ).im| ≤ ‖(1 - I * σ * l : ℂ)‖` using `Complex.abs_im_le_norm _`. Establish `h3 : (1 - I * σ * l : ℂ).im = -(σ * l)` using `by simp`. Rewrite `h1` using `[h3, abs_neg, abs_mul, abs_of_pos hl]`.

Apply the tactic sequence `have : |σ| = 1 := by rcases hσ with rfl | rfl <;> simp`. Rewrite `h1` using `[this, one_mul]`. Conclude with `h1`. Establish `hnorm : ‖A ^ 2 - B ^ 2‖ ≤ 2 * π / l ^ 2`. Rewrite using `[hdiff, norm_div, norm_neg, norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_real, Complex.norm_real]`.

Apply the tactic sequence `have : ‖σ‖ = 1 := by rcases hσ with rfl | rfl <;> simp`. Rewrite using `[this, Real.norm_of_nonneg Real.pi_pos.le, Real.norm_of_nonneg hl.le]`. Simplify using `only [Complex.norm_ofNat, mul_one]`. Rewrite using `[sq]`. Use `gcongr`.

Establish `hsum : s * (√2 / 2) ≤ ‖A + B‖`. Combine the equalities or inequalities in the displayed calculation. Establish `hprod : ‖A - B‖ * ‖A + B‖ = ‖A ^ 2 - B ^ 2‖`. Rewrite using `[← norm_mul]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Establish `hspos : 0 < s * (√2 / 2)` using `by positivity`. Establish `hsval : s * (√2 / 2) = √π / √l`. Rewrite using `[hs, Real.sqrt_div (by positivity), Real.sqrt_mul (by norm_num)]`. Establish `: √2 * √2 = 2` using `Real.mul_self_sqrt (by norm_num)`.

Clear the denominators using the available nonvanishing facts. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hfin : ‖A - B‖ * (√π / √l) ≤ 2 * π / l ^ 2`. Rewrite using `[← hsval]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hsl : 0 < √l` using `Real.sqrt_pos.2 hl`. Establish `hsp : 0 < √π` using `Real.sqrt_pos.2 Real.pi_pos`. Establish `hll : √l * √l = l` using `Real.mul_self_sqrt hl.le`. Establish `hpp : √π * √π = π` using `Real.mul_self_sqrt Real.pi_pos.le`. Establish `: ‖A - B‖ ≤ 2 * π / l ^ 2 / (√π / √l)`.

Rewrite using `[le_div_iff₀ (by positivity)]; exact hfin`. Use `this.trans (le_of_eq ?_)` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts. Use polynomial arithmetic with `[hll, hpp]`.
-/
theorem sqrt_asymp (σ l : ℝ) (hσ : σ = 1 ∨ σ = -1) (hl : 0 < l) :
    ‖((π : ℂ) / ((1 - I * σ * l) / 2)) ^ (1 / 2 : ℂ) - ((√(2 * π / l) : ℝ) : ℂ) * cexp (I * (π * σ / 4))‖ ≤
      2 * √π / (l * √l) := by
  set x : ℂ := (π : ℂ) / ((1 - I * σ * l) / 2) with hx
  set A : ℂ := x ^ (1 / 2 : ℂ) with hA
  set s : ℝ := √(2 * π / l) with hs
  set B : ℂ := (s : ℂ) * cexp (I * (π * σ / 4)) with hB
  have hσ2 : σ ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hσ2c : (σ : ℂ) ^ 2 = 1 := by exact_mod_cast hσ2
  have hs2 : s ^ 2 = 2 * π / l := Real.sq_sqrt (by positivity)
  have hs2c : (s : ℂ) ^ 2 = 2 * π / l := by exact_mod_cast hs2
  have h2 : ((√2 / 2 : ℝ) : ℂ) ^ 2 = 1 / 2 := by
    have : (√2 / 2 : ℝ) ^ 2 = 1 / 2 := by rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
    rw [← Complex.ofReal_pow, this]; push_cast; rfl
  have hB2 : B ^ 2 = 2 * π / l * (σ * I) := by
    rw [hB, w_eq σ hσ, mul_pow, mul_pow, hs2c, h2]
    have : (1 + (σ : ℂ) * I) ^ 2 = 2 * (σ * I) := by
      have : (1 + (σ : ℂ) * I) ^ 2 = 1 + 2 * (σ * I) + σ ^ 2 * I ^ 2 := by ring
      rw [this, hσ2c, Complex.I_sq]; ring
    rw [this]; ring
  have hBre : B.re = s * (√2 / 2) := by
    rw [hB, w_eq σ hσ, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
    simp
  have hd : (1 - I * σ * l : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have hlc : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  have hdiff : A ^ 2 - B ^ 2 = -(2 * π * σ * I) / (l * (1 - I * σ * l)) := by
    rw [hA, cpow_half_sq, hB2, hx]
    field_simp
    have : (σ : ℂ) * I * (1 - I * σ * l) = σ * I - σ ^ 2 * I ^ 2 * l := by ring
    ring_nf
    rw [hσ2c, Complex.I_sq]
    ring
  have hnd : l ≤ ‖(1 - I * σ * l : ℂ)‖ := by
    have h1 : |(1 - I * σ * l : ℂ).im| ≤ ‖(1 - I * σ * l : ℂ)‖ := Complex.abs_im_le_norm _
    have h3 : (1 - I * σ * l : ℂ).im = -(σ * l) := by simp
    rw [h3, abs_neg, abs_mul, abs_of_pos hl] at h1
    have : |σ| = 1 := by rcases hσ with rfl | rfl <;> simp
    rw [this, one_mul] at h1
    exact h1
  have hnorm : ‖A ^ 2 - B ^ 2‖ ≤ 2 * π / l ^ 2 := by
    rw [hdiff, norm_div, norm_neg, norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
      Complex.norm_real, Complex.norm_real]
    have : ‖σ‖ = 1 := by rcases hσ with rfl | rfl <;> simp
    rw [this, Real.norm_of_nonneg Real.pi_pos.le, Real.norm_of_nonneg hl.le]
    simp only [Complex.norm_ofNat, mul_one]
    rw [sq]
    gcongr
  have hsum : s * (√2 / 2) ≤ ‖A + B‖ := by
    calc s * (√2 / 2) = B.re := hBre.symm
      _ ≤ (A + B).re := by rw [Complex.add_re]; linarith [cpow_half_re_nonneg x]
      _ ≤ ‖A + B‖ := Complex.re_le_norm _
  have hprod : ‖A - B‖ * ‖A + B‖ = ‖A ^ 2 - B ^ 2‖ := by
    rw [← norm_mul]; congr 1; ring
  have hspos : 0 < s * (√2 / 2) := by positivity
  have hsval : s * (√2 / 2) = √π / √l := by
    rw [hs, Real.sqrt_div (by positivity), Real.sqrt_mul (by norm_num)]
    have : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
    field_simp
    linarith
  have hfin : ‖A - B‖ * (√π / √l) ≤ 2 * π / l ^ 2 := by
    rw [← hsval]
    calc ‖A - B‖ * (s * (√2 / 2)) ≤ ‖A - B‖ * ‖A + B‖ := by gcongr
      _ = _ := hprod
      _ ≤ _ := hnorm
  have hsl : 0 < √l := Real.sqrt_pos.2 hl
  have hsp : 0 < √π := Real.sqrt_pos.2 Real.pi_pos
  have hll : √l * √l = l := Real.mul_self_sqrt hl.le
  have hpp : √π * √π = π := Real.mul_self_sqrt Real.pi_pos.le
  have : ‖A - B‖ ≤ 2 * π / l ^ 2 / (√π / √l) := by
    rw [le_div_iff₀ (by positivity)]; exact hfin
  refine this.trans (le_of_eq ?_)
  field_simp
  nlinarith [hll, hpp]

/- English proof (translation)
Establish `h1 : |(1 - I * σ * l : ℂ).im| ≤ ‖(1 - I * σ * l : ℂ)‖` using `Complex.abs_im_le_norm _`. Establish `h3 : (1 - I * σ * l : ℂ).im = -(σ * l)` using `by simp`. Rewrite `h1` using `[h3, abs_neg, abs_mul, abs_of_pos hl]`. Apply the tactic sequence `have : |σ| = 1 := by rcases hσ with rfl | rfl <;> simp`. Rewrite `h1` using `[this, one_mul]`.

Conclude with `h1`.
-/
theorem norm_den_ge (σ l : ℝ) (hσ : σ = 1 ∨ σ = -1) (hl : 0 < l) : l ≤ ‖(1 - I * σ * l : ℂ)‖ := by
  have h1 : |(1 - I * σ * l : ℂ).im| ≤ ‖(1 - I * σ * l : ℂ)‖ := Complex.abs_im_le_norm _
  have h3 : (1 - I * σ * l : ℂ).im = -(σ * l) := by simp
  rw [h3, abs_neg, abs_mul, abs_of_pos hl] at h1
  have : |σ| = 1 := by rcases hσ with rfl | rfl <;> simp
  rw [this, one_mul] at h1
  exact h1

/- English proof (translation)
Establish `hsm : ContDiff ℝ ∞ (fun v : ℝ => cexp ((v : ℂ) ^ 2 / 2) * η v)`. Establish `h1 : ContDiff ℝ ∞ (fun v : ℝ => (v : ℂ))` using `Complex.ofRealCLM.contDiff`. Establish `h2 : ContDiff ℝ ∞ (fun v : ℝ => cexp ((v : ℂ) ^ 2 / 2))` using `((h1.pow 2).div_const 2).cexp`. Conclude with `h2.mul hη`. Establish `hcs : HasCompactSupport (fun v : ℝ => cexp ((v : ℂ) ^ 2 / 2) * η v)` using `hc.mul_left`.

Use `set g : 𝓢(ℝ, ℂ) := hcs.toSchwartzMap hsm with hg`. Establish `hg0 : g 0 = η 0` using `by simp [hg]`. Use `set M : ℝ := ∫ ξ : ℝ, ‖ξ‖ ^ 2 * ‖(𝓕⁻ g) ξ‖ with hM`. Establish `hM0 : 0 ≤ M` using `integral_nonneg fun ξ => by positivity`. Use `⟨√(2 * π) * (2 * π ^ 2) * M + 2 * √π * ‖η 0‖, by positivity, fun l hl => ?_⟩` and prove the remaining obligations.

Establish `hl0 : 0 < l` using `by linarith`. Use `set b : ℂ := (1 - I * σ * l) / 2 with hb`. Establish `hbre : 0 < b.re`. Rewrite using `[hb]`. Simplify using the standard rewrite rules.

Establish `hbn : l / 2 ≤ ‖b‖`. Rewrite using `[hb, norm_div]`. Simplify using `only [Complex.norm_ofNat]`. Use `gcongr`. Conclude with `norm_den_ge σ l hσ hl0`.

Establish `hbpos : 0 < ‖b‖` using `by linarith`. Establish `hint : (∫ v : ℝ, cexp (I * ((l : ℂ) * ((σ : ℂ) * (v : ℂ) ^ 2 / 2))) * η v) = ∫ v : ℝ, cexp (-b * v ^ 2) * g v`. Use `congr 1`. Use extensionality with `v`. Establish `: g v = cexp ((v : ℂ) ^ 2 / 2) * η v` using `rfl`.

Rewrite using `[this, show cexp (-b * (v : ℂ) ^ 2) * (cexp ((v : ℂ) ^ 2 / 2) * η v) = (cexp (-b * (v : ℂ) ^ 2) * cexp ((v : ℂ) ^ 2 / 2)) * η v by ring, ← Complex.exp_add]`. Use `congr 2`. Rewrite using `[hb]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hint]`.

Use `set A : ℂ := ((π : ℂ) / b) ^ (1 / 2 : ℂ) with hA`. Establish `hAn : ‖A‖ ≤ √(2 * π / l)`. Apply `Real.le_sqrt_of_sq_le` to reduce the goal to its premises. Rewrite using `[← norm_pow, hA, cpow_half_sq, norm_div, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]`. Rewrite using `[div_le_div_iff₀ hbpos hl0]`.

Use polynomial arithmetic with `[Real.pi_pos]`. Establish `h1` using `gauss_schwartz_bound g b hbre`. Rewrite `h1` using `[hg0]`. Establish `h2` using `sqrt_asymp σ l hσ hl0`. Rewrite `h2` using `[← hb, ← hA]`.

Establish `hsl : 0 < √l` using `Real.sqrt_pos.2 hl0`. Establish `hq : π ^ 2 / ‖b‖ ≤ 2 * π ^ 2 / l`. Rewrite using `[div_le_div_iff₀ hbpos hl0]`. Use polynomial arithmetic with `[Real.pi_pos, sq_nonneg π]`. Establish `h3 : ‖A‖ * (π ^ 2 / ‖b‖ * M) ≤ √(2 * π) * (2 * π ^ 2) * M / (l * √l)`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.sqrt_div (by positivity)]`. Clear the denominators using the available nonvanishing facts. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← norm_mul]`.

Conclude with `norm_add_le _ _`. Use `_ ≤ √(2 * π) * (2 * π ^ 2) * M / (l * √l) + 2 * √π / (l * √l) * ‖η 0‖ := by gcongr`. Conclude with `h1.trans h3`. Use `_ = _ := by ring`.
-/
theorem model_asymp (η : ℝ → ℂ) (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) (σ : ℝ)
    (hσ : σ = 1 ∨ σ = -1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ l : ℝ, 1 ≤ l →
      ‖(∫ v : ℝ, cexp (I * ((l : ℂ) * ((σ : ℂ) * (v : ℂ) ^ 2 / 2))) * η v) -
        ((√(2 * π / l) : ℝ) : ℂ) * cexp (I * (π * σ / 4)) * η 0‖ ≤ C / (l * √l) := by
  have hsm : ContDiff ℝ ∞ (fun v : ℝ => cexp ((v : ℂ) ^ 2 / 2) * η v) := by
    have h1 : ContDiff ℝ ∞ (fun v : ℝ => (v : ℂ)) := Complex.ofRealCLM.contDiff
    have h2 : ContDiff ℝ ∞ (fun v : ℝ => cexp ((v : ℂ) ^ 2 / 2)) := ((h1.pow 2).div_const 2).cexp
    exact h2.mul hη
  have hcs : HasCompactSupport (fun v : ℝ => cexp ((v : ℂ) ^ 2 / 2) * η v) := hc.mul_left
  set g : 𝓢(ℝ, ℂ) := hcs.toSchwartzMap hsm with hg
  have hg0 : g 0 = η 0 := by simp [hg]
  set M : ℝ := ∫ ξ : ℝ, ‖ξ‖ ^ 2 * ‖(𝓕⁻ g) ξ‖ with hM
  have hM0 : 0 ≤ M := integral_nonneg fun ξ => by positivity
  refine ⟨√(2 * π) * (2 * π ^ 2) * M + 2 * √π * ‖η 0‖, by positivity, fun l hl => ?_⟩
  have hl0 : 0 < l := by linarith
  set b : ℂ := (1 - I * σ * l) / 2 with hb
  have hbre : 0 < b.re := by
    rw [hb]; simp
  have hbn : l / 2 ≤ ‖b‖ := by
    rw [hb, norm_div]
    simp only [Complex.norm_ofNat]
    gcongr
    exact norm_den_ge σ l hσ hl0
  have hbpos : 0 < ‖b‖ := by linarith
  have hint : (∫ v : ℝ, cexp (I * ((l : ℂ) * ((σ : ℂ) * (v : ℂ) ^ 2 / 2))) * η v) =
      ∫ v : ℝ, cexp (-b * v ^ 2) * g v := by
    congr 1
    ext v
    have : g v = cexp ((v : ℂ) ^ 2 / 2) * η v := rfl
    rw [this, show cexp (-b * (v : ℂ) ^ 2) * (cexp ((v : ℂ) ^ 2 / 2) * η v) =
      (cexp (-b * (v : ℂ) ^ 2) * cexp ((v : ℂ) ^ 2 / 2)) * η v by ring, ← Complex.exp_add]
    congr 2
    rw [hb]; ring
  rw [hint]
  set A : ℂ := ((π : ℂ) / b) ^ (1 / 2 : ℂ) with hA
  have hAn : ‖A‖ ≤ √(2 * π / l) := by
    apply Real.le_sqrt_of_sq_le
    rw [← norm_pow, hA, cpow_half_sq, norm_div, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    rw [div_le_div_iff₀ hbpos hl0]
    nlinarith [Real.pi_pos]
  have h1 := gauss_schwartz_bound g b hbre
  rw [hg0] at h1
  have h2 := sqrt_asymp σ l hσ hl0
  rw [← hb, ← hA] at h2
  have hsl : 0 < √l := Real.sqrt_pos.2 hl0
  have hq : π ^ 2 / ‖b‖ ≤ 2 * π ^ 2 / l := by
    rw [div_le_div_iff₀ hbpos hl0]
    nlinarith [Real.pi_pos, sq_nonneg π]
  have h3 : ‖A‖ * (π ^ 2 / ‖b‖ * M) ≤ √(2 * π) * (2 * π ^ 2) * M / (l * √l) := by
    calc ‖A‖ * (π ^ 2 / ‖b‖ * M) ≤ √(2 * π / l) * (2 * π ^ 2 / l * M) := by gcongr
      _ = _ := by
        rw [Real.sqrt_div (by positivity)]
        field_simp
  calc ‖(∫ v : ℝ, cexp (-b * v ^ 2) * g v) - ((√(2 * π / l) : ℝ) : ℂ) * cexp (I * (π * σ / 4)) * η 0‖
      = ‖((∫ v : ℝ, cexp (-b * v ^ 2) * g v) - A * η 0) +
          (A - ((√(2 * π / l) : ℝ) : ℂ) * cexp (I * (π * σ / 4))) * η 0‖ := by congr 1; ring
    _ ≤ ‖(∫ v : ℝ, cexp (-b * v ^ 2) * g v) - A * η 0‖ +
          ‖A - ((√(2 * π / l) : ℝ) : ℂ) * cexp (I * (π * σ / 4))‖ * ‖η 0‖ := by
        rw [← norm_mul]; exact norm_add_le _ _
    _ ≤ √(2 * π) * (2 * π ^ 2) * M / (l * √l) + 2 * √π / (l * √l) * ‖η 0‖ := by
        gcongr
        exact h1.trans h3
    _ = _ := by ring

end Formalism.MainNotions.InterlacingSignCuts.SP

end

end PartA17m

section PartA17d

open MeasureTheory Filter Topology Set
open scoped ContDiff

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts.SP

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def Hd (g : ℝ → E) (x₀ : ℝ) (k : ℕ) (x : ℝ) : E := ∫ t in (0 : ℝ)..1, t ^ k • g (x₀ + t * (x - x₀))

/- English proof (translation)
Establish `hgc : Continuous g` using `hg.continuous`. Establish `hg'c : Continuous (deriv g)` using `hg.continuous_deriv (by simp)`. Establish `hgd : Differentiable ℝ g` using `hg.differentiable (by simp)`. Take `⟨Mb, hMb⟩` from `(isCompact_closedBall x₀ (|x - x₀| + 1)).exists_bound_of_continuousOn (f := deriv g) hg'c.continuousOn`. Establish `key` using `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (a := 0) (b := 1) (F := fun x t => t ^ k • g (x₀ + t * (x - x₀))) (F' := fun x t => t ^ (k + 1) • deriv g (x₀ + t * (x - x₀))) (x₀ := x) (s := Metric.ball x 1) (bound := fun _ => Mb) (Metric.ball_mem_ …`.

Rewrite `ht` using `[uIoc_of_le zero_le_one]`. Establish `hmem : x₀ + t * (y - x₀) ∈ Metric.closedBall x₀ (|x - x₀| + 1)`. Rewrite using `[Metric.mem_closedBall, Real.dist_eq]`. Establish `h1 : |y - x| < 1` using `by simpa [Real.dist_eq] using hy`. Establish `h2 : |y - x₀| ≤ |x - x₀| + 1`.

Combine the equalities or inequalities in the displayed calculation. Establish `: x₀ + t * (y - x₀) - x₀ = t * (y - x₀)` using `by ring`. Rewrite using `[this, abs_mul, abs_of_pos ht.1]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ht.1.le _)]`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `pow_le_one₀ ht.1.le ht.2`. Conclude with `hMb _ hmem`. Use `_ = Mb := one_mul _)`. Use `intervalIntegrable_const`.

Use the proof step `(Eventually.of_forall fun t _ y _ => by`. Establish `h1 : HasDerivAt (fun y : ℝ => x₀ + t * (y - x₀)) t y`. Simplify using `using ((hasDerivAt_id y).sub_const x₀).const_mul t |>.const_add x₀`. Establish `h2 : HasDerivAt (fun y : ℝ => g (x₀ + t * (y - x₀))) (t • deriv g (x₀ + t * (y - x₀))) y` using `(hgd _).hasDerivAt.scomp y h1`. Establish `h3` using `h2.const_smul (t ^ k)`.

Rewrite `h3` using `[smul_smul, ← pow_succ]`. Conclude with `h3)`. Conclude with `key.2`.
-/
theorem hasDerivAt_Hd (g : ℝ → E) (hg : ContDiff ℝ ∞ g) (x₀ : ℝ) (k : ℕ) (x : ℝ) :
    HasDerivAt (Hd g x₀ k) (Hd (deriv g) x₀ (k + 1) x) x := by
  have hgc : Continuous g := hg.continuous
  have hg'c : Continuous (deriv g) := hg.continuous_deriv (by simp)
  have hgd : Differentiable ℝ g := hg.differentiable (by simp)
  obtain ⟨Mb, hMb⟩ := (isCompact_closedBall x₀ (|x - x₀| + 1)).exists_bound_of_continuousOn
    (f := deriv g) hg'c.continuousOn
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (a := 0) (b := 1)
    (F := fun x t => t ^ k • g (x₀ + t * (x - x₀)))
    (F' := fun x t => t ^ (k + 1) • deriv g (x₀ + t * (x - x₀))) (x₀ := x) (s := Metric.ball x 1)
    (bound := fun _ => Mb) (Metric.ball_mem_nhds x one_pos)
    (Eventually.of_forall fun y => (by fun_prop : Continuous fun t : ℝ => t ^ k • g (x₀ + t * (y - x₀))).aestronglyMeasurable)
    ((by fun_prop : Continuous fun t : ℝ => t ^ k • g (x₀ + t * (x - x₀))).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun t : ℝ => t ^ (k + 1) • deriv g (x₀ + t * (x - x₀))).aestronglyMeasurable)
    (Eventually.of_forall fun t ht y hy => by
      rw [uIoc_of_le zero_le_one] at ht
      have hmem : x₀ + t * (y - x₀) ∈ Metric.closedBall x₀ (|x - x₀| + 1) := by
        rw [Metric.mem_closedBall, Real.dist_eq]
        have h1 : |y - x| < 1 := by simpa [Real.dist_eq] using hy
        have h2 : |y - x₀| ≤ |x - x₀| + 1 := by
          calc |y - x₀| = |(y - x) + (x - x₀)| := by ring_nf
            _ ≤ |y - x| + |x - x₀| := abs_add_le _ _
            _ ≤ |x - x₀| + 1 := by linarith
        have : x₀ + t * (y - x₀) - x₀ = t * (y - x₀) := by ring
        rw [this, abs_mul, abs_of_pos ht.1]
        calc t * |y - x₀| ≤ 1 * |y - x₀| := by gcongr; exact ht.2
          _ ≤ _ := by linarith
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ht.1.le _)]
      calc t ^ (k + 1) * ‖deriv g (x₀ + t * (y - x₀))‖ ≤ 1 * Mb := by
            gcongr
            · exact pow_le_one₀ ht.1.le ht.2
            · exact hMb _ hmem
        _ = Mb := one_mul _)
    intervalIntegrable_const
    (Eventually.of_forall fun t _ y _ => by
      have h1 : HasDerivAt (fun y : ℝ => x₀ + t * (y - x₀)) t y := by
        simpa using ((hasDerivAt_id y).sub_const x₀).const_mul t |>.const_add x₀
      have h2 : HasDerivAt (fun y : ℝ => g (x₀ + t * (y - x₀))) (t • deriv g (x₀ + t * (y - x₀))) y :=
        (hgd _).hasDerivAt.scomp y h1
      have h3 := h2.const_smul (t ^ k)
      rw [smul_smul, ← pow_succ] at h3
      exact h3)
  exact key.2

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `g hg k`. Rewrite using `[Nat.cast_zero, contDiff_zero]`.

Conclude with `continuous_iff_continuousAt.2 fun x => (hasDerivAt_Hd g hg x₀ k x).continuousAt`. Consider the case `succ n ih`. Introduce `g hg k`. Establish `hd : deriv (Hd g x₀ k) = Hd (deriv g) x₀ (k + 1)` using `funext fun x => (hasDerivAt_Hd g hg x₀ k x).deriv`. Rewrite using `[Nat.cast_succ, contDiff_succ_iff_deriv]`.

Use `⟨fun x => (hasDerivAt_Hd g hg x₀ k x).differentiableAt, by simp, ?_⟩` and prove the remaining obligations. Rewrite using `[hd]`. Conclude with `ih _ (contDiff_infty_iff_deriv.1 hg).2 _`.
-/
theorem contDiff_Hd_nat (x₀ : ℝ) : ∀ (n : ℕ) (g : ℝ → E), ContDiff ℝ ∞ g → ∀ k : ℕ, ContDiff ℝ n (Hd g x₀ k) := by
  intro n
  induction n with
  | zero =>
    intro g hg k
    rw [Nat.cast_zero, contDiff_zero]
    exact continuous_iff_continuousAt.2 fun x => (hasDerivAt_Hd g hg x₀ k x).continuousAt
  | succ n ih =>
    intro g hg k
    have hd : deriv (Hd g x₀ k) = Hd (deriv g) x₀ (k + 1) := funext fun x => (hasDerivAt_Hd g hg x₀ k x).deriv
    rw [Nat.cast_succ, contDiff_succ_iff_deriv]
    refine ⟨fun x => (hasDerivAt_Hd g hg x₀ k x).differentiableAt, by simp, ?_⟩
    rw [hd]
    exact ih _ (contDiff_infty_iff_deriv.1 hg).2 _

/- English proof (translation)
The claim follows from `contDiff_infty.2 fun n => contDiff_Hd_nat x₀ n g hg k`.
-/
theorem contDiff_Hd (x₀ : ℝ) (g : ℝ → E) (hg : ContDiff ℝ ∞ g) (k : ℕ) : ContDiff ℝ ∞ (Hd g x₀ k) :=
  contDiff_infty.2 fun n => contDiff_Hd_nat x₀ n g hg k

/- English proof (translation)
Establish `hg' : ContDiff ℝ ∞ (deriv g)` using `(contDiff_infty_iff_deriv.1 hg).2`. Establish `hgd : Differentiable ℝ g` using `hg.differentiable (by simp)`. Use `⟨Hd (deriv g) x₀ 0, contDiff_Hd x₀ _ hg' 0, fun x => ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => g (x₀ + t * (x - x₀))) ((x - x₀) • deriv g (x₀ + t * (x - x₀))) t`. Introduce `t _`.

Establish `h1 : HasDerivAt (fun t : ℝ => x₀ + t * (x - x₀)) (x - x₀) t`. Simplify using `using ((hasDerivAt_id t).mul_const (x - x₀)).const_add x₀`. Conclude with `(hgd _).hasDerivAt.scomp t h1`. Establish `hc : Continuous fun t : ℝ => (x - x₀) • deriv g (x₀ + t * (x - x₀))`. Use `hg'.continuous` as an intermediate fact.

Use `fun_prop`. Establish `h2` using `intervalIntegral.integral_eq_sub_of_hasDerivAt h1 (hc.intervalIntegrable _ _)`. Rewrite `h2` using `[intervalIntegral.integral_smul]`. Simplify using `only [one_mul, zero_mul, add_zero, add_sub_cancel] at h2`. Unfold `Hd`.

Simplify using `only [pow_zero, one_smul]`. Rewrite using `[h2]`. Normalize the expressions using the abelian group laws. Unfold `Hd`. Simplify using the standard rewrite rules.
-/
theorem division (g : ℝ → E) (hg : ContDiff ℝ ∞ g) (x₀ : ℝ) :
    ∃ g₁ : ℝ → E, ContDiff ℝ ∞ g₁ ∧ (∀ x, g x = g x₀ + (x - x₀) • g₁ x) ∧ g₁ x₀ = deriv g x₀ := by
  have hg' : ContDiff ℝ ∞ (deriv g) := (contDiff_infty_iff_deriv.1 hg).2
  have hgd : Differentiable ℝ g := hg.differentiable (by simp)
  refine ⟨Hd (deriv g) x₀ 0, contDiff_Hd x₀ _ hg' 0, fun x => ?_, ?_⟩
  · have h1 : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => g (x₀ + t * (x - x₀)))
        ((x - x₀) • deriv g (x₀ + t * (x - x₀))) t := by
      intro t _
      have h1 : HasDerivAt (fun t : ℝ => x₀ + t * (x - x₀)) (x - x₀) t := by
        simpa using ((hasDerivAt_id t).mul_const (x - x₀)).const_add x₀
      exact (hgd _).hasDerivAt.scomp t h1
    have hc : Continuous fun t : ℝ => (x - x₀) • deriv g (x₀ + t * (x - x₀)) := by
      have := hg'.continuous
      fun_prop
    have h2 := intervalIntegral.integral_eq_sub_of_hasDerivAt h1 (hc.intervalIntegrable _ _)
    rw [intervalIntegral.integral_smul] at h2
    simp only [one_mul, zero_mul, add_zero, add_sub_cancel] at h2
    unfold Hd
    simp only [pow_zero, one_smul]
    rw [h2]; abel
  · unfold Hd
    simp

end Formalism.MainNotions.InterlacingSignCuts.SP

end

end PartA17d

section PartA17a

open MeasureTheory Complex Filter Set
open scoped ContDiff Real

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts.SP

def Iph (φ : ℝ → ℝ) (l : ℝ) (f : ℝ → ℂ) : ℂ := ∫ x : ℝ, cexp (I * ((l : ℂ) * (φ x : ℂ))) * f x

/- English proof (translation)
Rewrite using `[show I * ((l : ℂ) * (t : ℂ)) = ((l * t : ℝ) : ℂ) * I by push_cast; ring]`. Conclude with `Complex.norm_exp_ofReal_mul_I _`.
-/
theorem norm_e (l t : ℝ) : ‖cexp (I * ((l : ℂ) * (t : ℂ)))‖ = 1 := by
  rw [show I * ((l : ℂ) * (t : ℂ)) = ((l * t : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/- English proof (translation)
Conclude with `(continuous_const.mul (continuous_const.mul (Complex.continuous_ofReal.comp hφ))).cexp`.
-/
theorem cont_e (φ : ℝ → ℝ) (hφ : Continuous φ) (l : ℝ) :
    Continuous fun x : ℝ => cexp (I * ((l : ℂ) * (φ x : ℂ))) := by
  exact (continuous_const.mul (continuous_const.mul (Complex.continuous_ofReal.comp hφ))).cexp

/- English proof (translation)
Conclude with `((cont_e φ hφ l).mul hf).integrable_of_hasCompactSupport hc.mul_left`.
-/
theorem int_e (φ : ℝ → ℝ) (hφ : Continuous φ) (l : ℝ) (f : ℝ → ℂ) (hf : Continuous f) (hc : HasCompactSupport f) :
    Integrable fun x : ℝ => cexp (I * ((l : ℂ) * (φ x : ℂ))) * f x := by
  exact ((cont_e φ hφ l).mul hf).integrable_of_hasCompactSupport hc.mul_left

/- English proof (translation)
Unfold `Iph`. Use `(norm_integral_le_integral_norm _).trans (le_of_eq ?_)` and prove the remaining obligations. Use `congr 1`. Use function extensionality and compare the values at `x`. Rewrite using `[norm_mul, norm_e, one_mul]`.
-/
theorem norm_Iph_le (φ : ℝ → ℝ) (l : ℝ) (f : ℝ → ℂ) : ‖Iph φ l f‖ ≤ ∫ x, ‖f x‖ := by
  unfold Iph
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1
  funext x
  rw [norm_mul, norm_e, one_mul]

/- English proof (translation)
Establish `hφc : Continuous φ` using `hφ.continuous`. Establish `hφ'c : Continuous (deriv φ)` using `hφ.continuous_deriv (by simp)`. Establish `hφ'cc : Continuous fun x : ℝ => ((deriv φ x : ℝ) : ℂ)` using `Complex.continuous_ofReal.comp hφ'c`. Establish `hc'c : Continuous (deriv c)` using `hc.continuous_deriv (by simp)`. Establish `hφd : Differentiable ℝ φ` using `hφ.differentiable (by simp)`.

Establish `hcd : Differentiable ℝ c` using `hc.differentiable (by simp)`. Establish `hder : ∀ x, HasDerivAt (fun x : ℝ => cexp (I * ((l : ℂ) * (φ x : ℂ))) * c x) (cexp (I * ((l : ℂ) * (φ x : ℂ))) * (I * ((l : ℂ) * ((deriv φ x : ℝ) : ℂ))) * c x + cexp (I * ((l : ℂ) * (φ x : ℂ))) * deriv c x) x`. Introduce `x`. Establish `h1 : HasDerivAt (fun x : ℝ => (φ x : ℂ)) ((deriv φ x : ℝ) : ℂ) x` using `(hφd x).hasDerivAt.ofReal_comp`. Establish `h2` using `((h1.const_mul (l : ℂ)).const_mul I).cexp`.

Conclude with `h2.mul (hcd x).hasDerivAt`. Establish `i1 : Integrable fun x : ℝ => cexp (I * ((l : ℂ) * (φ x : ℂ))) * (I * ((l : ℂ) * ((deriv φ x : ℝ) : ℂ))) * c x` using `(((cont_e φ hφc l).mul (by fun_prop)).mul hc.continuous).integrable_of_hasCompactSupport hcs.mul_left`. Establish `i2 : Integrable fun x : ℝ => cexp (I * ((l : ℂ) * (φ x : ℂ))) * deriv c x` using `int_e φ hφc l _ hc'c hcs.deriv`. Establish `i0 : Integrable fun x : ℝ => cexp (I * ((l : ℂ) * (φ x : ℂ))) * c x` using `int_e φ hφc l _ hc.continuous hcs`. Establish `hz` using `integral_eq_zero_of_hasDerivAt_of_integrable hder (i1.add i2) i0`.

Rewrite `hz` using `[integral_add i1 i2]`. Establish `e1 : (∫ x : ℝ, cexp (I * ((l : ℂ) * (φ x : ℂ))) * (I * ((l : ℂ) * ((deriv φ x : ℝ) : ℂ))) * c x) = (I * l) * Iph φ l (fun x => ((deriv φ x : ℝ) : ℂ) * c x)`. Unfold `Iph`. Rewrite using `[← integral_const_mul]`. Use `congr 1`.

Use extensionality with `x`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hz` using `[e1]`. Establish `hlc : (l : ℂ) ≠ 0` using `by exact_mod_cast hl`. Establish `hz' : (I * l) * Iph φ l (fun x => ((deriv φ x : ℝ) : ℂ) * c x) = -Iph φ l (deriv c)`.

Unfold `Iph at hz ⊢`. Take the linear combination `hz`. Establish `: Iph φ l (fun x => ((deriv φ x : ℝ) : ℂ) * c x) = -Iph φ l (deriv c) / (I * l)`. Rewrite using `[eq_div_iff (mul_ne_zero Complex.I_ne_zero hlc), mul_comm]`. Conclude with `hz'`.

Rewrite using `[this]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[Complex.I_sq]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ibp (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (c : ℝ → ℂ) (hc : ContDiff ℝ ∞ c) (hcs : HasCompactSupport c)
    (l : ℝ) (hl : l ≠ 0) :
    Iph φ l (fun x => ((deriv φ x : ℝ) : ℂ) * c x) = (I / l) * Iph φ l (deriv c) := by
  have hφc : Continuous φ := hφ.continuous
  have hφ'c : Continuous (deriv φ) := hφ.continuous_deriv (by simp)
  have hφ'cc : Continuous fun x : ℝ => ((deriv φ x : ℝ) : ℂ) := Complex.continuous_ofReal.comp hφ'c
  have hc'c : Continuous (deriv c) := hc.continuous_deriv (by simp)
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hcd : Differentiable ℝ c := hc.differentiable (by simp)
  have hder : ∀ x, HasDerivAt (fun x : ℝ => cexp (I * ((l : ℂ) * (φ x : ℂ))) * c x)
      (cexp (I * ((l : ℂ) * (φ x : ℂ))) * (I * ((l : ℂ) * ((deriv φ x : ℝ) : ℂ))) * c x +
        cexp (I * ((l : ℂ) * (φ x : ℂ))) * deriv c x) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => (φ x : ℂ)) ((deriv φ x : ℝ) : ℂ) x := (hφd x).hasDerivAt.ofReal_comp
    have h2 := ((h1.const_mul (l : ℂ)).const_mul I).cexp
    exact h2.mul (hcd x).hasDerivAt
  have i1 : Integrable fun x : ℝ => cexp (I * ((l : ℂ) * (φ x : ℂ))) * (I * ((l : ℂ) * ((deriv φ x : ℝ) : ℂ))) * c x :=
    (((cont_e φ hφc l).mul (by fun_prop)).mul hc.continuous).integrable_of_hasCompactSupport hcs.mul_left
  have i2 : Integrable fun x : ℝ => cexp (I * ((l : ℂ) * (φ x : ℂ))) * deriv c x :=
    int_e φ hφc l _ hc'c hcs.deriv
  have i0 : Integrable fun x : ℝ => cexp (I * ((l : ℂ) * (φ x : ℂ))) * c x := int_e φ hφc l _ hc.continuous hcs
  have hz := integral_eq_zero_of_hasDerivAt_of_integrable hder (i1.add i2) i0
  rw [integral_add i1 i2] at hz
  have e1 : (∫ x : ℝ, cexp (I * ((l : ℂ) * (φ x : ℂ))) * (I * ((l : ℂ) * ((deriv φ x : ℝ) : ℂ))) * c x) =
      (I * l) * Iph φ l (fun x => ((deriv φ x : ℝ) : ℂ) * c x) := by
    unfold Iph
    rw [← integral_const_mul]
    congr 1
    ext x
    ring
  rw [e1] at hz
  have hlc : (l : ℂ) ≠ 0 := by exact_mod_cast hl
  have hz' : (I * l) * Iph φ l (fun x => ((deriv φ x : ℝ) : ℂ) * c x) = -Iph φ l (deriv c) := by
    unfold Iph at hz ⊢
    linear_combination hz
  have : Iph φ l (fun x => ((deriv φ x : ℝ) : ℂ) * c x) = -Iph φ l (deriv c) / (I * l) := by
    rw [eq_div_iff (mul_ne_zero Complex.I_ne_zero hlc), mul_comm]; exact hz'
  rw [this]
  field_simp
  rw [Complex.I_sq]; ring

/- English proof (translation)
Conclude with `(support_deriv_subset).trans (closure_minimal hc hS)`.
-/
theorem supp_deriv {S : Set ℝ} (hS : IsClosed S) (c : ℝ → ℂ) (hc : Function.support c ⊆ S) :
    Function.support (deriv c) ⊆ S := by
  exact (support_deriv_subset).trans (closure_minimal hc hS)

/- English proof (translation)
Conclude with `hS.of_isClosed_subset (isClosed_tsupport c) (closure_minimal hc hS.isClosed)`.
-/
theorem cs_of_supp {S : Set ℝ} (hS : IsCompact S) (c : ℝ → ℂ) (hc : Function.support c ⊆ S) :
    HasCompactSupport c := by
  exact hS.of_isClosed_subset (isClosed_tsupport c) (closure_minimal hc hS.isClosed)

/- English proof (translation)
Establish `hφc : Continuous φ` using `hφ.continuous`. Establish `hφ'cc : Continuous fun x : ℝ => ((deriv φ x : ℝ) : ℂ)` using `Complex.continuous_ofReal.comp (hφ.continuous_deriv (by simp))`. Establish `hpc : HasCompactSupport p` using `cs_of_supp hS p hpS`. Establish `lin : ∀ (f c : ℝ → ℂ) (A : ℂ), ContDiff ℝ ∞ c → Function.support c ⊆ S → (∀ x, f x = A * p x + ((deriv φ x : ℝ) : ℂ) * c x) → ∀ l : ℝ, l ≠ 0 → Iph φ l f = A * Iph φ l p + (I / l) * Iph φ l (deriv c)`. Introduce `f c A hc hcS hf l hl`.

Establish `hcc` using `cs_of_supp hS c hcS`. Rewrite using `[← ibp φ hφ c hc hcc l hl]`. Unfold `Iph`. Rewrite using `[← integral_const_mul, ← integral_add]`. Use `congr 1`.

Use extensionality with `x`. Rewrite using `[hf x]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `(int_e φ hφc l p hp.continuous hpc).const_mul A`. Conclude with `int_e φ hφc l _ (hφ'cc.mul hc.continuous) hcc.mul_left`.

Take `⟨c₁, hc₁, hc₁S, h1⟩` from `hstep a ha haS`. Establish `hf₂ : ContDiff ℝ ∞ (deriv c₁)` using `(contDiff_infty_iff_deriv.1 hc₁).2`. Take `⟨c₂, hc₂, hc₂S, h2⟩` from `hstep (deriv c₁) hf₂ (supp_deriv hS.isClosed c₁ hc₁S)`. Take `⟨C₀, hC₀, hmod⟩` from `model_asymp η hη hηc σ hσ`. Use `set A₁ : ℂ := a x₀ / (√μ : ℝ) with hA₁`.

Use `set A₂ : ℂ := deriv c₁ x₀ / (√μ : ℝ) with hA₂`. Use `set N : ℝ := ∫ x, ‖deriv c₂ x‖ with hN`. Establish `hN0 : 0 ≤ N` using `integral_nonneg fun _ => norm_nonneg _`. Use `⟨‖A₁‖ * C₀ + ‖A₂‖ * (√(2 * π) + C₀) + N, fun l hl => ?_⟩` and prove the remaining obligations. Establish `hl0 : 0 < l` using `by linarith`.

Establish `hsl : 0 < √l` using `Real.sqrt_pos.2 hl0`. Establish `hsl1 : 1 ≤ √l` using `Real.one_le_sqrt.2 hl`. Establish `hsll : √l ≤ l`. Combine the equalities or inequalities in the displayed calculation. Use `set e₀ : ℂ := cexp (I * ((l : ℂ) * (φ x₀ : ℂ))) with he₀`.

Use `set Md : ℂ := ∫ v : ℝ, cexp (I * ((l : ℂ) * ((σ : ℂ) * (v : ℂ) ^ 2 / 2))) * η v with hMd`. Use `set B : ℂ := ((√(2 * π / l) : ℝ) : ℂ) * cexp (I * (π * σ / 4)) with hB`. Establish `hm` using `hmod l hl`. Rewrite `hm` using `[hη0, mul_one, ← hMd, ← hB]`. Establish `he₀n : ‖e₀‖ = 1` using `norm_e l (φ x₀)`.

Establish `hBn : ‖B‖ = √(2 * π) / √l`. Rewrite using `[hB, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]`. Establish `: I * ((π : ℂ) * σ / 4) = ((π * σ / 4 : ℝ) : ℂ) * I` using `by push_cast; ring`. Rewrite using `[this, Complex.norm_exp_ofReal_mul_I, mul_one, Real.sqrt_div (by positivity)]`. Establish `hMdn : ‖Md‖ ≤ (√(2 * π) + C₀) / √l`.

Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Use `_ = _ := by ring`. Establish `E1` using `lin a c₁ A₁ hc₁ hc₁S h1 l hl0.ne'`. Establish `E2` using `lin (deriv c₁) c₂ A₂ hc₂ hc₂S h2 l hl0.ne'`.

Rewrite `E1`, `E2` using `[hsub l, ← he₀, ← hMd]`. Establish `hIl : ‖(I / (l : ℂ))‖ = 1 / l`. Rewrite using `[norm_div, Complex.norm_I, Complex.norm_real, Real.norm_of_nonneg hl0.le]`. Establish `key : Iph φ l a - e₀ * B * A₁ = A₁ * e₀ * (Md - B) + (I / l) * (A₂ * (e₀ * Md)) + (I / l) * ((I / l) * Iph φ l (deriv c₂))`. Rewrite using `[E1, E2]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [norm_mul, he₀n, hIl, mul_one, one_mul]`. Use `_ ≤ ‖A₁‖ * (C₀ / (l * √l)) + 1 / l * (‖A₂‖ * ((√(2 * π) + C₀) / √l)) + 1 / l * (1 / √l * N) := by gcongr`.

Conclude with `norm_Iph_le φ l _`. Use `_ = _ := by field_simp`.
-/
theorem assemble (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (x₀ σ μ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (S : Set ℝ) (hS : IsCompact S) (p : ℝ → ℂ) (hp : ContDiff ℝ ∞ p) (hpS : Function.support p ⊆ S)
    (η : ℝ → ℂ) (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η) (hη0 : η 0 = 1)
    (hsub : ∀ l : ℝ, Iph φ l p = cexp (I * ((l : ℂ) * (φ x₀ : ℂ))) *
      ∫ v : ℝ, cexp (I * ((l : ℂ) * ((σ : ℂ) * (v : ℂ) ^ 2 / 2))) * η v)
    (hstep : ∀ f : ℝ → ℂ, ContDiff ℝ ∞ f → Function.support f ⊆ S → ∃ c : ℝ → ℂ, ContDiff ℝ ∞ c ∧
      Function.support c ⊆ S ∧ ∀ x, f x = (f x₀ / (√μ : ℝ)) * p x + ((deriv φ x : ℝ) : ℂ) * c x)
    (a : ℝ → ℂ) (ha : ContDiff ℝ ∞ a) (haS : Function.support a ⊆ S) :
    ∃ C : ℝ, ∀ l : ℝ, 1 ≤ l →
      ‖Iph φ l a - cexp (I * ((l : ℂ) * (φ x₀ : ℂ))) *
        (((√(2 * π / l) : ℝ) : ℂ) * cexp (I * (π * σ / 4))) * (a x₀ / (√μ : ℝ))‖ ≤ C / (l * √l) := by
  have hφc : Continuous φ := hφ.continuous
  have hφ'cc : Continuous fun x : ℝ => ((deriv φ x : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (hφ.continuous_deriv (by simp))
  have hpc : HasCompactSupport p := cs_of_supp hS p hpS

  have lin : ∀ (f c : ℝ → ℂ) (A : ℂ), ContDiff ℝ ∞ c → Function.support c ⊆ S →
      (∀ x, f x = A * p x + ((deriv φ x : ℝ) : ℂ) * c x) → ∀ l : ℝ, l ≠ 0 →
      Iph φ l f = A * Iph φ l p + (I / l) * Iph φ l (deriv c) := by
    intro f c A hc hcS hf l hl
    have hcc := cs_of_supp hS c hcS
    rw [← ibp φ hφ c hc hcc l hl]
    unfold Iph
    rw [← integral_const_mul, ← integral_add]
    · congr 1
      ext x
      rw [hf x]; ring
    · exact (int_e φ hφc l p hp.continuous hpc).const_mul A
    · exact int_e φ hφc l _ (hφ'cc.mul hc.continuous) hcc.mul_left
  obtain ⟨c₁, hc₁, hc₁S, h1⟩ := hstep a ha haS
  have hf₂ : ContDiff ℝ ∞ (deriv c₁) := (contDiff_infty_iff_deriv.1 hc₁).2
  obtain ⟨c₂, hc₂, hc₂S, h2⟩ := hstep (deriv c₁) hf₂ (supp_deriv hS.isClosed c₁ hc₁S)
  obtain ⟨C₀, hC₀, hmod⟩ := model_asymp η hη hηc σ hσ
  set A₁ : ℂ := a x₀ / (√μ : ℝ) with hA₁
  set A₂ : ℂ := deriv c₁ x₀ / (√μ : ℝ) with hA₂
  set N : ℝ := ∫ x, ‖deriv c₂ x‖ with hN
  have hN0 : 0 ≤ N := integral_nonneg fun _ => norm_nonneg _
  refine ⟨‖A₁‖ * C₀ + ‖A₂‖ * (√(2 * π) + C₀) + N, fun l hl => ?_⟩
  have hl0 : 0 < l := by linarith
  have hsl : 0 < √l := Real.sqrt_pos.2 hl0
  have hsl1 : 1 ≤ √l := Real.one_le_sqrt.2 hl
  have hsll : √l ≤ l := by
    calc √l = √l * 1 := (mul_one _).symm
      _ ≤ √l * √l := by gcongr
      _ = l := Real.mul_self_sqrt hl0.le
  set e₀ : ℂ := cexp (I * ((l : ℂ) * (φ x₀ : ℂ))) with he₀
  set Md : ℂ := ∫ v : ℝ, cexp (I * ((l : ℂ) * ((σ : ℂ) * (v : ℂ) ^ 2 / 2))) * η v with hMd
  set B : ℂ := ((√(2 * π / l) : ℝ) : ℂ) * cexp (I * (π * σ / 4)) with hB
  have hm := hmod l hl
  rw [hη0, mul_one, ← hMd, ← hB] at hm
  have he₀n : ‖e₀‖ = 1 := norm_e l (φ x₀)
  have hBn : ‖B‖ = √(2 * π) / √l := by
    rw [hB, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    have : I * ((π : ℂ) * σ / 4) = ((π * σ / 4 : ℝ) : ℂ) * I := by push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I, mul_one, Real.sqrt_div (by positivity)]
  have hMdn : ‖Md‖ ≤ (√(2 * π) + C₀) / √l := by
    calc ‖Md‖ = ‖(Md - B) + B‖ := by congr 1; ring
      _ ≤ ‖Md - B‖ + ‖B‖ := norm_add_le _ _
      _ ≤ C₀ / (l * √l) + √(2 * π) / √l := by rw [hBn]; gcongr
      _ ≤ C₀ / √l + √(2 * π) / √l := by
          gcongr
          calc √l = 1 * √l := (one_mul _).symm
            _ ≤ l * √l := by gcongr
      _ = _ := by ring
  have E1 := lin a c₁ A₁ hc₁ hc₁S h1 l hl0.ne'
  have E2 := lin (deriv c₁) c₂ A₂ hc₂ hc₂S h2 l hl0.ne'
  rw [hsub l, ← he₀, ← hMd] at E1 E2
  have hIl : ‖(I / (l : ℂ))‖ = 1 / l := by
    rw [norm_div, Complex.norm_I, Complex.norm_real, Real.norm_of_nonneg hl0.le]
  have key : Iph φ l a - e₀ * B * A₁ =
      A₁ * e₀ * (Md - B) + (I / l) * (A₂ * (e₀ * Md)) + (I / l) * ((I / l) * Iph φ l (deriv c₂)) := by
    rw [E1, E2]; ring
  rw [key]
  calc ‖A₁ * e₀ * (Md - B) + (I / l) * (A₂ * (e₀ * Md)) + (I / l) * ((I / l) * Iph φ l (deriv c₂))‖
      ≤ ‖A₁ * e₀ * (Md - B)‖ + ‖(I / l) * (A₂ * (e₀ * Md))‖ + ‖(I / l) * ((I / l) * Iph φ l (deriv c₂))‖ :=
        norm_add₃_le
    _ = ‖A₁‖ * ‖Md - B‖ + 1 / l * (‖A₂‖ * ‖Md‖) + 1 / l * (1 / l * ‖Iph φ l (deriv c₂)‖) := by
        simp only [norm_mul, he₀n, hIl, mul_one, one_mul]
    _ ≤ ‖A₁‖ * (C₀ / (l * √l)) + 1 / l * (‖A₂‖ * ((√(2 * π) + C₀) / √l)) + 1 / l * (1 / √l * N) := by
        gcongr
        exact norm_Iph_le φ l _
    _ = _ := by field_simp

end Formalism.MainNotions.InterlacingSignCuts.SP

end

end PartA17a

section PartA17p

open MeasureTheory Complex Filter Set Topology
open scoped ContDiff Real

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts.SP

/- English proof (translation)
Apply the tactic sequence `have hσσ : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num`. Take `⟨φ₁, hφ₁, eφ₁, vφ₁⟩` from `division φ hφ x₀`. Take `⟨h, hh, eh, -⟩` from `division φ₁ hφ₁ x₀`. Establish `hφ' : ContDiff ℝ ∞ (deriv φ)` using `(contDiff_infty_iff_deriv.1 hφ).2`. Take `⟨φ₂, hφ₂, eφ₂, vφ₂⟩` from `division (deriv φ) hφ' x₀`.

Establish `eq1 : ∀ x, φ x = φ x₀ + (x - x₀) ^ 2 * h x`. Introduce `x`. Rewrite using `[eφ₁ x, eh x, vφ₁, h1]`. Simplify using `only [smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Establish `eq2 : ∀ x, deriv φ x = (x - x₀) * φ₂ x`. Introduce `x`. Rewrite using `[eφ₂ x, h1]`. Simplify using the standard rewrite rules. Establish `hhd : Differentiable ℝ h` using `hh.differentiable (by simp)`.

Establish `hh'c : Continuous (deriv h)` using `hh.continuous_deriv (by simp)`. Establish `eq3 : ∀ x, deriv φ x = 2 * (x - x₀) * h x + (x - x₀) ^ 2 * deriv h x`. Introduce `x`. Establish `a1 : HasDerivAt (fun x : ℝ => (x - x₀) ^ 2) (2 * (x - x₀)) x`. Establish `a0 : HasDerivAt (fun x : ℝ => x - x₀) 1 x` using `(hasDerivAt_id x).sub_const x₀`.

Establish `hm : HasDerivAt (fun z : ℝ => (z - x₀) * (z - x₀)) (1 * (x - x₀) + (x - x₀) * 1) x` using `a0.mul a0`. Establish `e : (fun z : ℝ => (z - x₀) ^ 2) = fun z => (z - x₀) * (z - x₀)` using `by ext z; ring`. Establish `e2 : 2 * (x - x₀) = 1 * (x - x₀) + (x - x₀) * 1` using `by ring`. Rewrite using `[e, e2]`. Conclude with `hm`.

Establish `a2 : HasDerivAt (fun x : ℝ => φ x₀ + (x - x₀) ^ 2 * h x) (2 * (x - x₀) * h x + (x - x₀) ^ 2 * deriv h x) x` using `(a1.mul (hhd x).hasDerivAt).const_add _`. Conclude with `(a2.congr_of_eventuallyEq (Eventually.of_forall eq1)).deriv`. Establish `eq4 : φ₂ = fun x => 2 * h x + (x - x₀) * deriv h x`. Establish `hc` using `hh.continuous`. Apply `Continuous.ext_on (dense_compl_singleton x₀) hφ₂.continuous (by fun_prop)` to reduce the goal to its premises.

Introduce `x hx`. Establish `hx' : x - x₀ ≠ 0` using `sub_ne_zero.2 hx`. Apply `mul_left_cancel₀ hx'` to reduce the goal to its premises. Use `(eq2 x).symm.trans (eq3 x)` as an intermediate fact. Take the linear combination `this`.

Establish `vh2 : 2 * h x₀ = deriv (deriv φ) x₀`. Use `congrFun eq4 x₀` as an intermediate fact. Simplify using `only [sub_self, zero_mul, add_zero] at this`. Rewrite using `[← vφ₂, this]`. Establish `hk0 : 2 * σ * h x₀ = μ` using `by rw [← hσμ, ← vh2]; ring`.

Establish `hopen : IsOpen {x : ℝ | μ / 2 < 2 * σ * h x ∧ φ₂ x ≠ 0}`. Establish `hc` using `hh.continuous`. Conclude with `(isOpen_lt continuous_const (continuous_const.mul hc)).inter (isOpen_ne_fun hφ₂.continuous continuous_const)`. Establish `hmem : x₀ ∈ {x : ℝ | μ / 2 < 2 * σ * h x ∧ φ₂ x ≠ 0}` using `⟨by rw [hk0]; linarith, by rw [vφ₂]; exact h2⟩`. Take `⟨ρ, hρ, hball⟩` from `Metric.isOpen_iff.1 hopen x₀ hmem`.

Set `χ : ContDiffBump x₀` to `⟨ρ / 2, ρ, by positivity, by linarith⟩`. Use `set k : ℝ → ℝ := fun x => χ x * (2 * σ * h x) + (1 - χ x) * μ with hkdef`. Establish `hk : ContDiff ℝ ∞ k` using `(χ.contDiff.mul (contDiff_const.mul hh)).add ((contDiff_const.sub χ.contDiff).mul contDiff_const)`. Establish `hkge : ∀ x, μ / 2 ≤ k x`. Introduce `x`.

Distinguish the cases in `hx : x ∈ Metric.ball x₀ ρ`. Establish `b1` using `(hball hx).1`. Establish `c0 : 0 ≤ χ x` using `χ.nonneg`. Establish `c1 : χ x ≤ 1` using `χ.le_one`. Simplify using `only [hkdef]`.

Use the polynomial consequences of the given equalities and inequalities. Establish `: χ x = 0` using `χ.zero_of_le_dist (by simpa [Metric.mem_ball, not_lt] using hx)`. Simplify using `only [hkdef, this]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hkpos : ∀ x, 0 < k x` using `fun x => lt_of_lt_of_le (by positivity) (hkge x)`.

Establish `hsk : ContDiff ℝ ∞ (fun x => √(k x))` using `hk.sqrt fun x => (hkpos x).ne'`. Use `set y : ℝ → ℝ := fun x => (x - x₀) * √(k x) with hydef`. Establish `hy : ContDiff ℝ ∞ y` using `(contDiff_id.sub contDiff_const).mul hsk`. Establish `hy' : ContDiff ℝ ∞ (deriv y)` using `(contDiff_infty_iff_deriv.1 hy).2`. Establish `hyd : Differentiable ℝ y` using `hy.differentiable (by simp)`.

Establish `hχ1 : ∀ x, |x - x₀| ≤ ρ / 2 → χ x = 1` using `fun x hx => χ.one_of_mem_closedBall (by rw [Metric.mem_closedBall, Real.dist_eq]; exact hx)`. Establish `hkx0 : k x₀ = μ`. Establish `: χ x₀ = 1` using `hχ1 x₀ (by simp; positivity)`. Simplify using `only [hkdef, this]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hy'0 : deriv y x₀ = √μ`. Establish `d1 : HasDerivAt (fun x : ℝ => x - x₀) 1 x₀` using `(hasDerivAt_id x₀).sub_const x₀`. Establish `d2 : DifferentiableAt ℝ (fun x => √(k x)) x₀` using `(hsk.differentiable (by simp)) x₀`. Use `(d1.mul d2.hasDerivAt).deriv` as an intermediate fact. Simplify using `only [sub_self, zero_mul, add_zero, one_mul, hkx0] at this`.

Conclude with `this`. Establish `hy0 : y x₀ = 0` using `by simp [hydef]`. Establish `hs2 : 0 < √(μ / 2)` using `Real.sqrt_pos.2 (by positivity)`. Establish `hyabs : ∀ x, |x - x₀| * √(μ / 2) ≤ |y x|`. Introduce `x`.

Simplify using `only [hydef]`. Rewrite using `[abs_mul, abs_of_nonneg (Real.sqrt_nonneg (k x))]`. Use `gcongr`. Conclude with `hkge x`. Use `set ε : ℝ := ρ / 2 * √(μ / 2) with hεdef`.

Establish `hε : 0 < ε` using `by positivity`. Set `η₀ : ContDiffBump (0 : ℝ)` to `⟨ε / 2, ε, by positivity, by linarith⟩`. Use `set η : ℝ → ℂ := fun v => ((η₀ v : ℝ) : ℂ) with hηdef`. Establish `hη : ContDiff ℝ ∞ η` using `Complex.ofRealCLM.contDiff.comp η₀.contDiff`. Establish `hηc : HasCompactSupport η` using `η₀.hasCompactSupport.comp_left (g := fun t : ℝ => (t : ℂ)) Complex.ofReal_zero`.

Establish `hη0 : η 0 = 1`. Establish `: η₀ 0 = 1` using `η₀.one_of_mem_closedBall (Metric.mem_closedBall_self (by positivity))`. Simplify using `only [hηdef, this, Complex.ofReal_one]`. Establish `hsupp0 : ∀ v, η₀ v ≠ 0 → |v| < ε`. Introduce `v hv`.

Establish `: v ∈ Metric.ball (0 : ℝ) ε`. Use `η₀.support_eq` as an intermediate fact. Rewrite using `[← this]`. Conclude with `hv`. Simplify `this` using `[Real.dist_eq]`.

Establish `hnear : ∀ x, η₀ (y x) ≠ 0 → |x - x₀| < ρ / 2`. Introduce `x hx`. Use `(hyabs x).trans_lt (hsupp0 _ hx)` as an intermediate fact. Conclude with `lt_of_mul_lt_mul_right this hs2.le`. Establish `hphase : ∀ x, η₀ (y x) ≠ 0 → φ x = φ x₀ + σ * (y x) ^ 2 / 2`.

Introduce `x hx`. Establish `hkx : k x = 2 * σ * h x`. Simplify using `only [hkdef, hχ1 x (hnear x hx).le]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[eq1 x]`.

Simplify using `only [hydef]`. Rewrite using `[mul_pow, Real.sq_sqrt (hkpos x).le, hkx]`. Take the linear combination `(-(x - x₀) ^ 2 * h x) * hσσ`. Use `set p : ℝ → ℂ := fun x => η (y x) * ((deriv y x : ℝ) : ℂ) with hpdef`. Establish `hp : ContDiff ℝ ∞ p` using `(hη.comp hy).mul (Complex.ofRealCLM.contDiff.comp hy')`.

Use `set S : Set ℝ := tsupport a ∪ Metric.closedBall x₀ (ρ / 2) with hSdef`. Establish `hS : IsCompact S` using `hac.isCompact.union (isCompact_closedBall _ _)`. Establish `hpS : Function.support p ⊆ S`. Introduce `x hx`. Use `right`.

Establish `: η₀ (y x) ≠ 0`. Introduce `h0`. Apply `hx` to reduce the goal to its premises. Simplify using `[hpdef, hηdef, h0]`. Rewrite using `[Metric.mem_closedBall, Real.dist_eq]`.

Conclude with `(hnear x this).le`. Establish `hx0S : x₀ ∈ S` using `Or.inr (Metric.mem_closedBall_self (by positivity))`. Establish `hφ₂S : ∀ x ∈ S, φ₂ x ≠ 0`. Introduce and unpack `x (hx | hx)`. Distinguish the cases in `hxx : x = x₀`.

Rewrite using `[hxx, vφ₂]`. Conclude with `h2`. Introduce `h0`. Apply `h3 x hx hxx` to reduce the goal to its premises. Rewrite using `[eq2 x, h0, mul_zero]`.

Conclude with `(hball (Metric.closedBall_subset_ball (by linarith) hx)).2`. Establish `hp0 : p x₀ = ((√μ : ℝ) : ℂ)`. Simplify using `only [hpdef, hy0, hη0, hy'0, one_mul]`. Establish `hsμ : ((√μ : ℝ) : ℂ) ≠ 0`. Conclude with `(Real.sqrt_pos.2 hμ).ne'` after adjusting the coercions.

Establish `hsub : ∀ l : ℝ, Iph φ l p = cexp (I * ((l : ℂ) * (φ x₀ : ℂ))) * ∫ v : ℝ, cexp (I * ((l : ℂ) * ((σ : ℂ) * (v : ℂ) ^ 2 / 2))) * η v`. Introduce `l`. Use `set G : ℝ → ℂ := fun v => cexp (I * ((l : ℂ) * ((σ : ℂ) * (v : ℂ) ^ 2 / 2))) * η v with hGdef`. Establish `hG : Continuous G`. Use `hη.continuous` as an intermediate fact.

Establish `h5 : Continuous fun v : ℝ => (v : ℂ)` using `Complex.continuous_ofReal`. Use `fun_prop`. Establish `e1 : ∀ x, cexp (I * ((l : ℂ) * (φ x : ℂ))) * p x = cexp (I * ((l : ℂ) * (φ x₀ : ℂ))) * (deriv y x • G (y x))`. Introduce `x`. Distinguish the cases in `hx : η₀ (y x) = 0`.

Simplify using `[hpdef, hGdef, hηdef, hx]`. Rewrite using `[hphase x hx]`. Simplify using `only [hpdef, hGdef, Complex.real_smul]`. Use `push_cast`. Rewrite using `[show I * ((l : ℂ) * ((φ x₀ : ℂ) + (σ : ℂ) * (y x : ℂ) ^ 2 / 2)) = I * ((l : ℂ) * (φ x₀ : ℂ)) + I * ((l : ℂ) * ((σ : ℂ) * (y x : ℂ) ^ 2 / 2)) by ring, Complex.exp_add]`.

Expand and normalize the polynomial expressions, which then agree. Unfold `Iph`. Repeatedly rewrite using `[e1]`. Rewrite using `[integral_const_mul]`. Use `congr 1`.

Establish `s1 : Function.support (fun x => deriv y x • G (y x)) ⊆ Ioc (x₀ - ρ) (x₀ + ρ)`. Introduce `x hx`. Establish `: η₀ (y x) ≠ 0`. Introduce `h0`. Apply `hx` to reduce the goal to its premises.

Simplify using `[hGdef, hηdef, h0]`. Use `hnear x this` as an intermediate fact. Rewrite `this` using `[abs_lt]`. Apply the tactic sequence `constructor <;> linarith [this.1, this.2]`. Establish `y1 : 2 * ε ≤ y (x₀ + ρ)`.

Use `hyabs (x₀ + ρ)` as an intermediate fact. Establish `e : x₀ + ρ - x₀ = ρ` using `by ring`. Establish `hpos : 0 ≤ y (x₀ + ρ)`. Simplify using `only [hydef, e]`. Check the signs of the components of the expression.

Rewrite `this` using `[e, abs_of_pos hρ, abs_of_nonneg hpos]`. Combine the equalities or inequalities in the displayed calculation. Establish `y2 : y (x₀ - ρ) ≤ -(2 * ε)`. Use `hyabs (x₀ - ρ)` as an intermediate fact. Establish `e : x₀ - ρ - x₀ = -ρ` using `by ring`.

Establish `hneg : y (x₀ - ρ) ≤ 0`. Simplify using `only [hydef, e]`. Establish `: 0 ≤ ρ * √(k (x₀ - ρ))` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite `this` using `[e, abs_neg, abs_of_pos hρ, abs_of_nonpos hneg]`.

Establish `e2 : 2 * ε = ρ * √(μ / 2)` using `by rw [hεdef]; ring`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `s2 : Function.support G ⊆ Ioc (y (x₀ - ρ)) (y (x₀ + ρ))`. Introduce `v hv`. Establish `: η₀ v ≠ 0`.

Introduce `h0`. Apply `hv` to reduce the goal to its premises. Simplify using `[hGdef, hηdef, h0]`. Use `hsupp0 v this` as an intermediate fact. Rewrite `this` using `[abs_lt]`.

Apply the tactic sequence `constructor <;> linarith [this.1, this.2]`. Rewrite using `[← intervalIntegral.integral_eq_integral_of_support_subset s1, ← intervalIntegral.integral_eq_integral_of_support_subset s2]`. Conclude with `intervalIntegral.integral_deriv_smul_comp (fun x _ => (hyd x).hasDerivAt) hy'.continuous.continuousOn hG`. Establish `hstep : ∀ f : ℝ → ℂ, ContDiff ℝ ∞ f → Function.support f ⊆ S → ∃ c : ℝ → ℂ, ContDiff ℝ ∞ c ∧ Function.support c ⊆ S ∧ ∀ x, f x = (f x₀ / (√μ : ℝ)) * p x + ((deriv φ x : ℝ) : ℂ) * c x`. Introduce `f hf hfS`.

Use `set A : ℂ := f x₀ / (√μ : ℝ) with hA`. Use `set F : ℝ → ℂ := fun x => f x - A * p x with hFdef`. Establish `hF : ContDiff ℝ ∞ F` using `hf.sub (contDiff_const.mul hp)`. Establish `hF0 : F x₀ = 0`. Simplify using `only [hFdef, hA, hp0]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hFS : ∀ x, x ∉ S → F x = 0`. Introduce `x hxS`. Establish `f0 : f x = 0`.

Assume the negation of the conclusion as `hne`. Conclude with `hxS (hfS hne)`. Establish `p0 : p x = 0`. Assume the negation of the conclusion as `hne`. Conclude with `hxS (hpS hne)`.

Simplify using `only [hFdef, f0, p0]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨F₁, hF₁, eF₁, -⟩` from `division F hF x₀`. Establish `eF : ∀ x, F x = (x - x₀) • F₁ x`. Introduce `x`.

Rewrite using `[eF₁ x, hF0, zero_add]`. Establish `hF₁S : ∀ x, x ∉ S → F₁ x = 0`. Introduce `x hxS`. Establish `hne : x ≠ x₀` using `fun e => hxS (e ▸ hx0S)`. Use `eF x` as an intermediate fact.

Rewrite `this` using `[hFS x hxS]`. Conclude with `(smul_eq_zero.1 this.symm).resolve_left (sub_ne_zero.2 hne)`. Use `⟨fun x => F₁ x * (((φ₂ x : ℝ) : ℂ))⁻¹, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[contDiff_iff_contDiffAt]`. Introduce `x`.

Distinguish the cases in `hx : φ₂ x = 0`. Establish `hxS : x ∉ S` using `fun hh => hφ₂S x hh hx`. Establish `hev : ∀ᶠ x' in 𝓝 x, x' ∉ S` using `hS.isClosed.isOpen_compl.mem_nhds hxS`. Establish `: (fun x => F₁ x * (((φ₂ x : ℝ) : ℂ))⁻¹) =ᶠ[𝓝 x] fun _ => 0` using `by filter_upwards [hev] with x' hx'`. Rewrite using `[hF₁S x' hx', zero_mul]`.

Conclude with `contDiffAt_const.congr_of_eventuallyEq this`. Establish `hc2 : ContDiff ℝ ∞ (fun x => ((φ₂ x : ℝ) : ℂ))` using `Complex.ofRealCLM.contDiff.comp hφ₂`. Conclude with `hF₁.contDiffAt.mul (hc2.contDiffAt.inv (by exact_mod_cast hx))`. Introduce `x hx`. Assume the negation of the conclusion as `hxS`.

Apply `hx` to reduce the goal to its premises. Use `show F₁ x * (((φ₂ x : ℝ) : ℂ))⁻¹ = 0`. Rewrite using `[hF₁S x hxS, zero_mul]`. Introduce `x`. Establish `e0 : f x = A * p x + F x` using `by simp only [hFdef]; ring`.

Rewrite using `[e0, eq2 x, eF x]`. Use `congr 1`. Distinguish the cases in `hx : φ₂ x = 0`. Establish `hxS : x ∉ S` using `fun hh => hφ₂S x hh hx`. Simplify using `[hF₁S x hxS]`.

Establish `hxc : ((φ₂ x : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hx`. Rewrite using `[Complex.real_smul]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Conclude with `assemble φ hφ x₀ σ μ hσ S hS p hp hpS η hη hηc hη0 hsub hstep a ha ((subset_tsupport a).trans subset_union_left)`.
-/
theorem stat_phase_core (a : ℝ → ℂ) (φ : ℝ → ℝ) (x₀ : ℝ) (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport a)
    (hφ : ContDiff ℝ ∞ φ) (h1 : deriv φ x₀ = 0) (h2 : deriv (deriv φ) x₀ ≠ 0)
    (h3 : ∀ x ∈ tsupport a, x ≠ x₀ → deriv φ x ≠ 0) (σ μ : ℝ) (hσ : σ = 1 ∨ σ = -1) (hμ : 0 < μ)
    (hσμ : σ * deriv (deriv φ) x₀ = μ) :
    ∃ C : ℝ, ∀ l : ℝ, 1 ≤ l →
      ‖Iph φ l a - cexp (I * ((l : ℂ) * (φ x₀ : ℂ))) *
        (((√(2 * π / l) : ℝ) : ℂ) * cexp (I * (π * σ / 4))) * (a x₀ / (√μ : ℝ))‖ ≤ C / (l * √l) := by
  have hσσ : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num

  obtain ⟨φ₁, hφ₁, eφ₁, vφ₁⟩ := division φ hφ x₀
  obtain ⟨h, hh, eh, -⟩ := division φ₁ hφ₁ x₀
  have hφ' : ContDiff ℝ ∞ (deriv φ) := (contDiff_infty_iff_deriv.1 hφ).2
  obtain ⟨φ₂, hφ₂, eφ₂, vφ₂⟩ := division (deriv φ) hφ' x₀
  have eq1 : ∀ x, φ x = φ x₀ + (x - x₀) ^ 2 * h x := by
    intro x
    rw [eφ₁ x, eh x, vφ₁, h1]
    simp only [smul_eq_mul]
    ring
  have eq2 : ∀ x, deriv φ x = (x - x₀) * φ₂ x := by
    intro x
    rw [eφ₂ x, h1]
    simp
  have hhd : Differentiable ℝ h := hh.differentiable (by simp)
  have hh'c : Continuous (deriv h) := hh.continuous_deriv (by simp)
  have eq3 : ∀ x, deriv φ x = 2 * (x - x₀) * h x + (x - x₀) ^ 2 * deriv h x := by
    intro x
    have a1 : HasDerivAt (fun x : ℝ => (x - x₀) ^ 2) (2 * (x - x₀)) x := by
      have a0 : HasDerivAt (fun x : ℝ => x - x₀) 1 x := (hasDerivAt_id x).sub_const x₀
      have hm : HasDerivAt (fun z : ℝ => (z - x₀) * (z - x₀)) (1 * (x - x₀) + (x - x₀) * 1) x := a0.mul a0
      have e : (fun z : ℝ => (z - x₀) ^ 2) = fun z => (z - x₀) * (z - x₀) := by ext z; ring
      have e2 : 2 * (x - x₀) = 1 * (x - x₀) + (x - x₀) * 1 := by ring
      rw [e, e2]
      exact hm
    have a2 : HasDerivAt (fun x : ℝ => φ x₀ + (x - x₀) ^ 2 * h x)
        (2 * (x - x₀) * h x + (x - x₀) ^ 2 * deriv h x) x := (a1.mul (hhd x).hasDerivAt).const_add _
    exact (a2.congr_of_eventuallyEq (Eventually.of_forall eq1)).deriv
  have eq4 : φ₂ = fun x => 2 * h x + (x - x₀) * deriv h x := by
    have hc := hh.continuous
    apply Continuous.ext_on (dense_compl_singleton x₀) hφ₂.continuous (by fun_prop)
    intro x hx
    have hx' : x - x₀ ≠ 0 := sub_ne_zero.2 hx
    apply mul_left_cancel₀ hx'
    have := (eq2 x).symm.trans (eq3 x)
    linear_combination this
  have vh2 : 2 * h x₀ = deriv (deriv φ) x₀ := by
    have := congrFun eq4 x₀
    simp only [sub_self, zero_mul, add_zero] at this
    rw [← vφ₂, this]
  have hk0 : 2 * σ * h x₀ = μ := by rw [← hσμ, ← vh2]; ring

  have hopen : IsOpen {x : ℝ | μ / 2 < 2 * σ * h x ∧ φ₂ x ≠ 0} := by
    have hc := hh.continuous
    exact (isOpen_lt continuous_const (continuous_const.mul hc)).inter
      (isOpen_ne_fun hφ₂.continuous continuous_const)
  have hmem : x₀ ∈ {x : ℝ | μ / 2 < 2 * σ * h x ∧ φ₂ x ≠ 0} :=
    ⟨by rw [hk0]; linarith, by rw [vφ₂]; exact h2⟩
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hopen x₀ hmem
  let χ : ContDiffBump x₀ := ⟨ρ / 2, ρ, by positivity, by linarith⟩
  set k : ℝ → ℝ := fun x => χ x * (2 * σ * h x) + (1 - χ x) * μ with hkdef
  have hk : ContDiff ℝ ∞ k :=
    (χ.contDiff.mul (contDiff_const.mul hh)).add ((contDiff_const.sub χ.contDiff).mul contDiff_const)
  have hkge : ∀ x, μ / 2 ≤ k x := by
    intro x
    by_cases hx : x ∈ Metric.ball x₀ ρ
    · have b1 := (hball hx).1
      have c0 : 0 ≤ χ x := χ.nonneg
      have c1 : χ x ≤ 1 := χ.le_one
      simp only [hkdef]
      nlinarith
    · have : χ x = 0 := χ.zero_of_le_dist (by simpa [Metric.mem_ball, not_lt] using hx)
      simp only [hkdef, this]
      linarith
  have hkpos : ∀ x, 0 < k x := fun x => lt_of_lt_of_le (by positivity) (hkge x)
  have hsk : ContDiff ℝ ∞ (fun x => √(k x)) := hk.sqrt fun x => (hkpos x).ne'
  set y : ℝ → ℝ := fun x => (x - x₀) * √(k x) with hydef
  have hy : ContDiff ℝ ∞ y := (contDiff_id.sub contDiff_const).mul hsk
  have hy' : ContDiff ℝ ∞ (deriv y) := (contDiff_infty_iff_deriv.1 hy).2
  have hyd : Differentiable ℝ y := hy.differentiable (by simp)
  have hχ1 : ∀ x, |x - x₀| ≤ ρ / 2 → χ x = 1 := fun x hx =>
    χ.one_of_mem_closedBall (by rw [Metric.mem_closedBall, Real.dist_eq]; exact hx)
  have hkx0 : k x₀ = μ := by
    have : χ x₀ = 1 := hχ1 x₀ (by simp; positivity)
    simp only [hkdef, this]
    linarith
  have hy'0 : deriv y x₀ = √μ := by
    have d1 : HasDerivAt (fun x : ℝ => x - x₀) 1 x₀ := (hasDerivAt_id x₀).sub_const x₀
    have d2 : DifferentiableAt ℝ (fun x => √(k x)) x₀ := (hsk.differentiable (by simp)) x₀
    have := (d1.mul d2.hasDerivAt).deriv
    simp only [sub_self, zero_mul, add_zero, one_mul, hkx0] at this
    exact this
  have hy0 : y x₀ = 0 := by simp [hydef]
  have hs2 : 0 < √(μ / 2) := Real.sqrt_pos.2 (by positivity)
  have hyabs : ∀ x, |x - x₀| * √(μ / 2) ≤ |y x| := by
    intro x
    simp only [hydef]
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg (k x))]
    gcongr
    exact hkge x
  set ε : ℝ := ρ / 2 * √(μ / 2) with hεdef
  have hε : 0 < ε := by positivity
  let η₀ : ContDiffBump (0 : ℝ) := ⟨ε / 2, ε, by positivity, by linarith⟩
  set η : ℝ → ℂ := fun v => ((η₀ v : ℝ) : ℂ) with hηdef
  have hη : ContDiff ℝ ∞ η := Complex.ofRealCLM.contDiff.comp η₀.contDiff
  have hηc : HasCompactSupport η := η₀.hasCompactSupport.comp_left (g := fun t : ℝ => (t : ℂ)) Complex.ofReal_zero
  have hη0 : η 0 = 1 := by
    have : η₀ 0 = 1 := η₀.one_of_mem_closedBall (Metric.mem_closedBall_self (by positivity))
    simp only [hηdef, this, Complex.ofReal_one]
  have hsupp0 : ∀ v, η₀ v ≠ 0 → |v| < ε := by
    intro v hv
    have : v ∈ Metric.ball (0 : ℝ) ε := by
      have := η₀.support_eq
      rw [← this]; exact hv
    simpa [Real.dist_eq] using this
  have hnear : ∀ x, η₀ (y x) ≠ 0 → |x - x₀| < ρ / 2 := by
    intro x hx
    have := (hyabs x).trans_lt (hsupp0 _ hx)
    exact lt_of_mul_lt_mul_right this hs2.le
  have hphase : ∀ x, η₀ (y x) ≠ 0 → φ x = φ x₀ + σ * (y x) ^ 2 / 2 := by
    intro x hx
    have hkx : k x = 2 * σ * h x := by
      simp only [hkdef, hχ1 x (hnear x hx).le]
      ring
    rw [eq1 x]
    simp only [hydef]
    rw [mul_pow, Real.sq_sqrt (hkpos x).le, hkx]
    linear_combination (-(x - x₀) ^ 2 * h x) * hσσ
  set p : ℝ → ℂ := fun x => η (y x) * ((deriv y x : ℝ) : ℂ) with hpdef
  have hp : ContDiff ℝ ∞ p := (hη.comp hy).mul (Complex.ofRealCLM.contDiff.comp hy')
  set S : Set ℝ := tsupport a ∪ Metric.closedBall x₀ (ρ / 2) with hSdef
  have hS : IsCompact S := hac.isCompact.union (isCompact_closedBall _ _)
  have hpS : Function.support p ⊆ S := by
    intro x hx
    right
    have : η₀ (y x) ≠ 0 := by
      intro h0
      apply hx
      simp [hpdef, hηdef, h0]
    rw [Metric.mem_closedBall, Real.dist_eq]
    exact (hnear x this).le
  have hx0S : x₀ ∈ S := Or.inr (Metric.mem_closedBall_self (by positivity))
  have hφ₂S : ∀ x ∈ S, φ₂ x ≠ 0 := by
    rintro x (hx | hx)
    · by_cases hxx : x = x₀
      · rw [hxx, vφ₂]; exact h2
      · intro h0
        apply h3 x hx hxx
        rw [eq2 x, h0, mul_zero]
    · exact (hball (Metric.closedBall_subset_ball (by linarith) hx)).2
  have hp0 : p x₀ = ((√μ : ℝ) : ℂ) := by
    simp only [hpdef, hy0, hη0, hy'0, one_mul]
  have hsμ : ((√μ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hμ).ne'

  have hsub : ∀ l : ℝ, Iph φ l p = cexp (I * ((l : ℂ) * (φ x₀ : ℂ))) *
      ∫ v : ℝ, cexp (I * ((l : ℂ) * ((σ : ℂ) * (v : ℂ) ^ 2 / 2))) * η v := by
    intro l
    set G : ℝ → ℂ := fun v => cexp (I * ((l : ℂ) * ((σ : ℂ) * (v : ℂ) ^ 2 / 2))) * η v with hGdef
    have hG : Continuous G := by
      have := hη.continuous
      have h5 : Continuous fun v : ℝ => (v : ℂ) := Complex.continuous_ofReal
      fun_prop
    have e1 : ∀ x, cexp (I * ((l : ℂ) * (φ x : ℂ))) * p x =
        cexp (I * ((l : ℂ) * (φ x₀ : ℂ))) * (deriv y x • G (y x)) := by
      intro x
      by_cases hx : η₀ (y x) = 0
      · simp [hpdef, hGdef, hηdef, hx]
      · rw [hphase x hx]
        simp only [hpdef, hGdef, Complex.real_smul]
        push_cast
        rw [show I * ((l : ℂ) * ((φ x₀ : ℂ) + (σ : ℂ) * (y x : ℂ) ^ 2 / 2)) =
          I * ((l : ℂ) * (φ x₀ : ℂ)) + I * ((l : ℂ) * ((σ : ℂ) * (y x : ℂ) ^ 2 / 2)) by ring, Complex.exp_add]
        ring
    unfold Iph
    simp_rw [e1]
    rw [integral_const_mul]
    congr 1
    have s1 : Function.support (fun x => deriv y x • G (y x)) ⊆ Ioc (x₀ - ρ) (x₀ + ρ) := by
      intro x hx
      have : η₀ (y x) ≠ 0 := by
        intro h0
        apply hx
        simp [hGdef, hηdef, h0]
      have := hnear x this
      rw [abs_lt] at this
      constructor <;> linarith [this.1, this.2]
    have y1 : 2 * ε ≤ y (x₀ + ρ) := by
      have := hyabs (x₀ + ρ)
      have e : x₀ + ρ - x₀ = ρ := by ring
      have hpos : 0 ≤ y (x₀ + ρ) := by
        simp only [hydef, e]; positivity
      rw [e, abs_of_pos hρ, abs_of_nonneg hpos] at this
      calc 2 * ε = ρ * √(μ / 2) := by rw [hεdef]; ring
        _ ≤ _ := this
    have y2 : y (x₀ - ρ) ≤ -(2 * ε) := by
      have := hyabs (x₀ - ρ)
      have e : x₀ - ρ - x₀ = -ρ := by ring
      have hneg : y (x₀ - ρ) ≤ 0 := by
        simp only [hydef, e]
        have : 0 ≤ ρ * √(k (x₀ - ρ)) := by positivity
        linarith
      rw [e, abs_neg, abs_of_pos hρ, abs_of_nonpos hneg] at this
      have e2 : 2 * ε = ρ * √(μ / 2) := by rw [hεdef]; ring
      linarith
    have s2 : Function.support G ⊆ Ioc (y (x₀ - ρ)) (y (x₀ + ρ)) := by
      intro v hv
      have : η₀ v ≠ 0 := by
        intro h0
        apply hv
        simp [hGdef, hηdef, h0]
      have := hsupp0 v this
      rw [abs_lt] at this
      constructor <;> linarith [this.1, this.2]
    rw [← intervalIntegral.integral_eq_integral_of_support_subset s1,
      ← intervalIntegral.integral_eq_integral_of_support_subset s2]
    exact intervalIntegral.integral_deriv_smul_comp (fun x _ => (hyd x).hasDerivAt)
      hy'.continuous.continuousOn hG

  have hstep : ∀ f : ℝ → ℂ, ContDiff ℝ ∞ f → Function.support f ⊆ S → ∃ c : ℝ → ℂ, ContDiff ℝ ∞ c ∧
      Function.support c ⊆ S ∧ ∀ x, f x = (f x₀ / (√μ : ℝ)) * p x + ((deriv φ x : ℝ) : ℂ) * c x := by
    intro f hf hfS
    set A : ℂ := f x₀ / (√μ : ℝ) with hA
    set F : ℝ → ℂ := fun x => f x - A * p x with hFdef
    have hF : ContDiff ℝ ∞ F := hf.sub (contDiff_const.mul hp)
    have hF0 : F x₀ = 0 := by
      simp only [hFdef, hA, hp0]
      field_simp
      ring
    have hFS : ∀ x, x ∉ S → F x = 0 := by
      intro x hxS
      have f0 : f x = 0 := by
        by_contra hne
        exact hxS (hfS hne)
      have p0 : p x = 0 := by
        by_contra hne
        exact hxS (hpS hne)
      simp only [hFdef, f0, p0]
      ring
    obtain ⟨F₁, hF₁, eF₁, -⟩ := division F hF x₀
    have eF : ∀ x, F x = (x - x₀) • F₁ x := by
      intro x
      rw [eF₁ x, hF0, zero_add]
    have hF₁S : ∀ x, x ∉ S → F₁ x = 0 := by
      intro x hxS
      have hne : x ≠ x₀ := fun e => hxS (e ▸ hx0S)
      have := eF x
      rw [hFS x hxS] at this
      exact (smul_eq_zero.1 this.symm).resolve_left (sub_ne_zero.2 hne)
    refine ⟨fun x => F₁ x * (((φ₂ x : ℝ) : ℂ))⁻¹, ?_, ?_, ?_⟩
    · rw [contDiff_iff_contDiffAt]
      intro x
      by_cases hx : φ₂ x = 0
      · have hxS : x ∉ S := fun hh => hφ₂S x hh hx
        have hev : ∀ᶠ x' in 𝓝 x, x' ∉ S := hS.isClosed.isOpen_compl.mem_nhds hxS
        have : (fun x => F₁ x * (((φ₂ x : ℝ) : ℂ))⁻¹) =ᶠ[𝓝 x] fun _ => 0 := by
          filter_upwards [hev] with x' hx'
          rw [hF₁S x' hx', zero_mul]
        exact contDiffAt_const.congr_of_eventuallyEq this
      · have hc2 : ContDiff ℝ ∞ (fun x => ((φ₂ x : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp hφ₂
        exact hF₁.contDiffAt.mul (hc2.contDiffAt.inv (by exact_mod_cast hx))
    · intro x hx
      by_contra hxS
      apply hx
      show F₁ x * (((φ₂ x : ℝ) : ℂ))⁻¹ = 0
      rw [hF₁S x hxS, zero_mul]
    · intro x
      have e0 : f x = A * p x + F x := by simp only [hFdef]; ring
      rw [e0, eq2 x, eF x]
      congr 1
      by_cases hx : φ₂ x = 0
      · have hxS : x ∉ S := fun hh => hφ₂S x hh hx
        simp [hF₁S x hxS]
      · have hxc : ((φ₂ x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx
        rw [Complex.real_smul]
        push_cast
        field_simp
  exact assemble φ hφ x₀ σ μ hσ S hS p hp hpS η hη hηc hη0 hsub hstep a ha
    ((subset_tsupport a).trans subset_union_left)

end Formalism.MainNotions.InterlacingSignCuts.SP

end

end PartA17p

section PartA17s

open MeasureTheory Complex Filter Set Topology
open scoped ContDiff Real

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts

open SP

/- English proof (translation)
Rewrite using `[neg_div, Real.rpow_neg hl.le, Real.sqrt_eq_rpow, one_div]`. Use `congr 1`. Rewrite using `[show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hl, Real.rpow_one]`.
-/
theorem rpow_neg_three_half (l : ℝ) (hl : 0 < l) : l ^ (-(3 : ℝ) / 2) = 1 / (l * √l) := by
  rw [neg_div, Real.rpow_neg hl.le, Real.sqrt_eq_rpow, one_div]
  congr 1
  rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hl, Real.rpow_one]

/- English proof (translation)
Introduce `a φ x₀ ha hac hφ h1 h2 h3`. Use `set d : ℝ := deriv (deriv φ) x₀ with hd`. Use `set σ : ℝ := ((SignType.sign d : SignType) : ℝ) with hσdef`. Establish `hσ : σ = 1 ∨ σ = -1`. Break down `lt_or_gt_of_ne h2 with hneg | hpos` into its components or cases.

Use `right`. Simplify using `[hσdef, sign_neg hneg]`. Use `left`. Simplify using `[hσdef, sign_pos hpos]`. Establish `hσμ : σ * d = |d|`.

Break down `lt_or_gt_of_ne h2 with hneg | hpos` into its components or cases. Simplify using `[hσdef, sign_neg hneg, abs_of_neg hneg]`. Simplify using `[hσdef, sign_pos hpos, abs_of_pos hpos]`. Establish `hμ : 0 < |d|` using `abs_pos.2 h2`. Take `⟨C, hC⟩` from `stat_phase_core a φ x₀ ha hac hφ h1 h2 h3 σ |d| hσ hμ hσμ`.

Use `Asymptotics.IsBigO.of_bound C ?_` and prove the remaining obligations. Use `filter_upwards [eventually_ge_atTop (1 : ℝ)] with l hl`. Establish `hl0 : 0 < l` using `by linarith`. Establish `hb` using `hC l hl`. Rewrite using `[rpow_neg_three_half l hl0, Real.norm_of_nonneg (by positivity), mul_one_div]`.

Use `le_of_eq_of_le ?_ hb` and prove the remaining obligations. Use `congr 1`. Unfold `Iph`. Use `congr 1`. Establish `e1 : cexp (I * ((l : ℂ) * (φ x₀ : ℂ) + (π : ℂ) * (σ : ℂ) / 4)) = cexp (I * ((l : ℂ) * (φ x₀ : ℂ))) * cexp (I * ((π : ℂ) * (σ : ℂ) / 4))`.

Rewrite using `[mul_add, Complex.exp_add]`. Establish `e2 : √(2 * π / (l * |d|)) = √(2 * π / l) / √|d|`. Rewrite using `[← Real.sqrt_div (by positivity)]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[e1, e2]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem stStatPhase_of_core : Formalism.MainNotions.S.UnitaryLevelOperators.stStatPhase := by
  intro a φ x₀ ha hac hφ h1 h2 h3
  set d : ℝ := deriv (deriv φ) x₀ with hd
  set σ : ℝ := ((SignType.sign d : SignType) : ℝ) with hσdef
  have hσ : σ = 1 ∨ σ = -1 := by
    rcases lt_or_gt_of_ne h2 with hneg | hpos
    · right; simp [hσdef, sign_neg hneg]
    · left; simp [hσdef, sign_pos hpos]
  have hσμ : σ * d = |d| := by
    rcases lt_or_gt_of_ne h2 with hneg | hpos
    · simp [hσdef, sign_neg hneg, abs_of_neg hneg]
    · simp [hσdef, sign_pos hpos, abs_of_pos hpos]
  have hμ : 0 < |d| := abs_pos.2 h2
  obtain ⟨C, hC⟩ := stat_phase_core a φ x₀ ha hac hφ h1 h2 h3 σ |d| hσ hμ hσμ
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with l hl
  have hl0 : 0 < l := by linarith
  have hb := hC l hl
  rw [rpow_neg_three_half l hl0, Real.norm_of_nonneg (by positivity), mul_one_div]
  refine le_of_eq_of_le ?_ hb
  congr 1
  unfold Iph
  congr 1
  have e1 : cexp (I * ((l : ℂ) * (φ x₀ : ℂ) + (π : ℂ) * (σ : ℂ) / 4)) =
      cexp (I * ((l : ℂ) * (φ x₀ : ℂ))) * cexp (I * ((π : ℂ) * (σ : ℂ) / 4)) := by
    rw [mul_add, Complex.exp_add]
  have e2 : √(2 * π / (l * |d|)) = √(2 * π / l) / √|d| := by
    rw [← Real.sqrt_div (by positivity)]
    congr 1
    field_simp
  rw [e1, e2]
  push_cast
  ring

end Formalism.MainNotions.InterlacingSignCuts

end

end PartA17s

section PartAOm

open Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LevR

namespace Formalism.MainNotions.InterlacingSignCuts

/- English proof (translation)
Unfold `herm Hb`. Simplify using `only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply]`.
-/
theorem herm_Hb (k : ℕ) (x y : Fin (k + 1) → ℂ) :
    herm (Hb k) x y = ∑ j, star (y j) * ((if j = Fin.last k then (-1 : ℂ) else 1) * x j) := by
  unfold herm Hb
  simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply]

/- English proof (translation)
Introduce `a b h`. Unfold `wI at h`. Rewrite `h` using `[Fin.mk.injEq]`. Conclude with `Fin.ext (by omega)`.
-/
theorem wI_inj (k r : ℕ) : Function.Injective (wI k r) := by
  intro a b h
  unfold wI at h
  rw [Fin.mk.injEq] at h
  exact Fin.ext (by omega)

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Apply `hi` to reduce the goal to its premises. Use `⟨⟨i.val - r, by omega⟩, ?_⟩` and prove the remaining obligations. Unfold `wI`.

Use `ext`. Use `show r + (i.val - r) = i.val`. Use linear arithmetic over natural numbers and integers.
-/
theorem not_range_wI (k r : ℕ) (i : Fin (2 * r + k + 1)) (hi : i ∉ Set.range (wI k r)) :
    i.val < r ∨ r + k < i.val := by
  by_contra hc
  push_neg at hc
  apply hi
  refine ⟨⟨i.val - r, by omega⟩, ?_⟩
  unfold wI
  ext
  show r + (i.val - r) = i.val
  omega

/- English proof (translation)
Establish `hj` using `j.isLt`. Establish `hv : (wI k r j).val = r + j.val` using `rfl`. Unfold `Hpk`. Rewrite using `[if_neg (by rw [hv]; omega), if_neg (by rw [hv]; omega)]`. Distinguish the cases in `hq : q = wI k r j`.

Rewrite using `[if_pos hq, if_pos ⟨by rw [hv]; omega, by rw [hv]; omega, hq.symm⟩]`. Distinguish the cases in `hl : j = Fin.last k`. Rewrite using `[if_pos hl, if_pos (by rw [hv, hl]; rfl)]`. Rewrite using `[if_neg hl, if_neg (by`. Rewrite using `[hv]`.

Introduce `h`. Conclude with `hl (Fin.ext (by rw [Fin.val_last]; omega)))]`. Rewrite using `[if_neg hq, if_neg (by rintro ⟨_, _, h⟩; exact hq h.symm)]`.
-/
theorem Hpk_wI (k r : ℕ) (j : Fin (k + 1)) (q : Fin (2 * r + k + 1)) :
    Hpk k r (wI k r j) q = if q = wI k r j then (if j = Fin.last k then (-1 : ℂ) else 1) else 0 := by
  have hj := j.isLt
  have hv : (wI k r j).val = r + j.val := rfl
  unfold Hpk
  rw [if_neg (by rw [hv]; omega), if_neg (by rw [hv]; omega)]
  by_cases hq : q = wI k r j
  · rw [if_pos hq, if_pos ⟨by rw [hv]; omega, by rw [hv]; omega, hq.symm⟩]
    by_cases hl : j = Fin.last k
    · rw [if_pos hl, if_pos (by rw [hv, hl]; rfl)]
    · rw [if_neg hl, if_neg (by
        rw [hv]
        intro h
        exact hl (Fin.ext (by rw [Fin.val_last]; omega)))]
  · rw [if_neg hq, if_neg (by rintro ⟨_, _, h⟩; exact hq h.symm)]

/- English proof (translation)
Rewrite using `[herm_Hb]`. Unfold `herm`. Simplify using `only [dotProduct, Pi.star_apply]`. Use `symm`. Apply `Fintype.sum_of_injective (wI k r) (wI_inj k r)` to reduce the goal to its premises.

Introduce `i hi`. Rewrite using `[hw i (not_range_wI k r i hi)]`. Simplify using the standard rewrite rules. Introduce `j`. Establish `: (Hpk k r *ᵥ v) (wI k r j) = (if j = Fin.last k then (-1 : ℂ) else 1) * v (wI k r j)`.

Simplify using `only [Matrix.mulVec, dotProduct, Hpk_wI]`. Simplify using the standard rewrite rules. Rewrite using `[this]`. Both sides reduce to the same expression.
-/
theorem herm_Hpk_wb (k r : ℕ) (v w : Fin (2 * r + k + 1) → ℂ) (hw : inWb k r w) :
    herm (Hpk k r) v w = herm (Hb k) (wbPart k r v) (wbPart k r w) := by
  rw [herm_Hb]
  unfold herm
  simp only [dotProduct, Pi.star_apply]
  symm
  apply Fintype.sum_of_injective (wI k r) (wI_inj k r)
  · intro i hi
    rw [hw i (not_range_wI k r i hi)]
    simp
  · intro j
    have : (Hpk k r *ᵥ v) (wI k r j) = (if j = Fin.last k then (-1 : ℂ) else 1) * v (wI k r j) := by
      simp only [Matrix.mulVec, dotProduct, Hpk_wI]
      simp
    rw [this]
    rfl

/- English proof (translation)
Use function extensionality and compare the values at `j`. Simplify using `only [wbPart, Matrix.mulVec, dotProduct]`. Use `symm`. Apply `Fintype.sum_of_injective (wI k r) (wI_inj k r)` to reduce the goal to its premises. Introduce `q hq`.

Rewrite using `[hz' q (not_range_wI k r q hq)]`. Simplify using the standard rewrite rules. Introduce `j'`. Establish `hj` using `j.isLt`. Establish `hj'` using `j'.isLt`.

Establish `h1 : ¬ (wI k r j').val < r` using `by show ¬ (r + j'.val < r); omega`. Establish `h2 : (wI k r j').val ≤ r + k` using `by show r + j'.val ≤ r + k; omega`. Establish `h3 : r ≤ (wI k r j).val ∧ (wI k r j).val ≤ r + k`. Prove the components needed by the constructor for the conclusion. Use `show r ≤ r + j.val`.

Use linear arithmetic over natural numbers and integers. Use `show r + j.val ≤ r + k`. Use linear arithmetic over natural numbers and integers. Establish `: bigCell k r c μ (wI k r j) (wI k r j') = μ j j'`. Unfold `bigCell`.

Rewrite using `[dif_neg h1, dif_pos h2, dif_pos h3]`. Apply the tactic sequence `congr 1 <;> exact Fin.ext (by show r + _ - r = _; omega)`. Rewrite using `[this]`.
-/
theorem wbPart_bigCell (k r : ℕ) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (z' : Fin (2 * r + k + 1) → ℂ) (hz' : inWb k r z') :
    wbPart k r (bigCell k r c μ *ᵥ z') = μ *ᵥ wbPart k r z' := by
  funext j
  simp only [wbPart, Matrix.mulVec, dotProduct]
  symm
  apply Fintype.sum_of_injective (wI k r) (wI_inj k r)
  · intro q hq
    rw [hz' q (not_range_wI k r q hq)]
    simp
  · intro j'
    have hj := j.isLt
    have hj' := j'.isLt
    have h1 : ¬ (wI k r j').val < r := by show ¬ (r + j'.val < r); omega
    have h2 : (wI k r j').val ≤ r + k := by show r + j'.val ≤ r + k; omega
    have h3 : r ≤ (wI k r j).val ∧ (wI k r j).val ≤ r + k := by
      constructor
      · show r ≤ r + j.val; omega
      · show r + j.val ≤ r + k; omega
    have : bigCell k r c μ (wI k r j) (wI k r j') = μ j j' := by
      unfold bigCell
      rw [dif_neg h1, dif_pos h2, dif_pos h3]
      congr 1 <;> exact Fin.ext (by show r + _ - r = _; omega)
    rw [this]

/- English proof (translation)
Unfold `herm`. Rewrite using `[Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]`.
-/
theorem herm_unitary {n : ℕ} (H g : Matrix (Fin n) (Fin n) ℂ) (v w : Fin n → ℂ) :
    herm H (g *ᵥ v) (g *ᵥ w) = herm (gᴴ * H * g) v w := by
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

/- English proof (translation)
Unfold `Hb`. Rewrite using `[Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Apply the tactic sequence `split_ifs <;> norm_num`.
-/
theorem Hb_sq (k : ℕ) : Hb k * Hb k = 1 := by
  unfold Hb
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext j
  split_ifs <;> norm_num

/- English proof (translation)
Unfold `herm`. Rewrite using `[Matrix.mulVec_add, dotProduct_add]`.
-/
theorem ip_add (k : ℕ) (x y w : Fin (k + 1) → ℂ) :
    herm (Hb k) (x + y) w = herm (Hb k) x w + herm (Hb k) y w := by
  unfold herm
  rw [Matrix.mulVec_add, dotProduct_add]

/- English proof (translation)
Unfold `herm`. Rewrite using `[Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]`.
-/
theorem ip_smul (k : ℕ) (s : ℂ) (x y : Fin (k + 1) → ℂ) :
    herm (Hb k) (s • x) y = s * herm (Hb k) x y := by
  unfold herm
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

/- English proof (translation)
Simplify using `only [herm_Hb, map_sum, map_mul]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp [mul_comm]`.
-/
theorem ip_conj (k : ℕ) (x y : Fin (k + 1) → ℂ) :
    herm (Hb k) y x = starRingEnd ℂ (herm (Hb k) x y) := by
  simp only [herm_Hb, map_sum, map_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp [mul_comm]

/- English proof (translation)
Establish `h1` using `ip_conj k (wbPart k r z) (wbPart k r z)`. Establish `h2 : (herm (Hb k) (wbPart k r z) (wbPart k r z)).im = 0`. Use `congrArg Complex.im h1` as an intermediate fact. Rewrite `this` using `[Complex.conj_im]`. Combine the linear equalities and inequalities to obtain the conclusion.

Unfold `Tz`. Rewrite using `[herm_Hpk_wb k r z z hz]`. Apply `Complex.ext` to reduce the goal to its premises. Simplify using the standard rewrite rules. Simplify using `[h2]`.
-/
theorem ip_self (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) :
    herm (Hb k) (wbPart k r z) (wbPart k r z) = -((Tz k r z : ℝ) : ℂ) := by
  have h1 := ip_conj k (wbPart k r z) (wbPart k r z)
  have h2 : (herm (Hb k) (wbPart k r z) (wbPart k r z)).im = 0 := by
    have := congrArg Complex.im h1
    rw [Complex.conj_im] at this
    linarith
  unfold Tz
  rw [herm_Hpk_wb k r z z hz]
  apply Complex.ext
  · simp
  · simp [h2]

/- English proof (translation)
Take `⟨m1, -, m3⟩` from `Formalism.QuantumDeterminants.bigCellMinors k r z z' c μ hz hz'`. Establish `hDr : Dmin k r z z' (bigCell k r c μ) ⟨r, by omega⟩ ≠ 0`. Establish `h` using `m1 (Fin.last r)`. Simplify using `only [Fin.val_last] at h`. Rewrite using `[h]`.

Conclude with `Finset.prod_ne_zero_iff.2 fun a _ => hc a`. Use `⟨hDr, ?_⟩` and prove the remaining obligations. Establish `h` using `m3 hc`. Unfold `zeta at h`. Rewrite `h` using `[herm_Hpk_wb k r _ z hz, wbPart_bigCell k r c μ z' hz', div_eq_iff hDr]`.

Rewrite using `[h, mul_comm]`.
-/
theorem bigCell_D (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hz' : inWb k r z')
    (c : Fin r → ℂ) (hc : ∀ a, c a ≠ 0) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    Dmin k r z z' (bigCell k r c μ) ⟨r, by omega⟩ ≠ 0 ∧
    Dmin k r z z' (bigCell k r c μ) (Fin.last (r + 1)) =
      Dmin k r z z' (bigCell k r c μ) ⟨r, by omega⟩ * herm (Hb k) (μ *ᵥ wbPart k r z') (wbPart k r z) := by
  obtain ⟨m1, -, m3⟩ := Formalism.QuantumDeterminants.bigCellMinors k r z z' c μ hz hz'
  have hDr : Dmin k r z z' (bigCell k r c μ) ⟨r, by omega⟩ ≠ 0 := by
    have h := m1 (Fin.last r)
    simp only [Fin.val_last] at h
    rw [h]
    exact Finset.prod_ne_zero_iff.2 fun a _ => hc a
  refine ⟨hDr, ?_⟩
  have h := m3 hc
  unfold zeta at h
  rw [herm_Hpk_wb k r _ z hz, wbPart_bigCell k r c μ z' hz', div_eq_iff hDr] at h
  rw [h, mul_comm]

/- English proof (translation)
Establish `hμ' : μᴴ * Hb k * μ = Hb k` using `hμ`. Establish `hzz` using `ip_self k r z hz`. Establish `hxx : herm (Hb k) (μ *ᵥ wbPart k r z') (μ *ᵥ wbPart k r z') = -((Tz k r z' : ℝ) : ℂ)`. Rewrite using `[herm_unitary, hμ', ip_self k r z' hz']`. Establish `key` using `(Formalism.FourierDecayAlt.P.omega_norm_formula (Fin (k + 1) → ℂ) (herm (Hb k)) (ip_add k) (ip_smul k) (ip_conj k) (wbPart k r z) (μ *ᵥ wbPart k r z') (Tz k r z) (Tz k r z') (Dmin k r z z' (bigCell k r c μ) ⟨r, by omega⟩) hT hzz hxx).2`.

Establish `hom : omF k r z z' c μ = Dmin k r z z' (bigCell k r c μ) ⟨r, by omega⟩ • (μ *ᵥ wbPart k r z' + (herm (Hb k) (μ *ᵥ wbPart k r z') (wbPart k r z) / ((Tz k r z : ℝ) : ℂ)) • wbPart k r z)`. Unfold `omF prW`. Rewrite using `[hzz, div_neg, neg_smul, sub_neg_eq_add]`. Rewrite using `[hom, key, Complex.ofReal_re]`. Unfold `Gf`.

Rewrite using `[(bigCell_D k r z z' hz hz' c hc μ).2]`.
-/
theorem om_norm (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hz' : inWb k r z')
    (hT : 0 < Tz k r z) (c : Fin r → ℂ) (hc : ∀ a, c a ≠ 0) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (hμ : μ ∈ UH (Hb k)) :
    (herm (Hb k) (omF k r z z' c μ) (omF k r z z' c μ)).re = Gf k r z z' (bigCell k r c μ) / Tz k r z := by
  have hμ' : μᴴ * Hb k * μ = Hb k := hμ
  have hzz := ip_self k r z hz
  have hxx : herm (Hb k) (μ *ᵥ wbPart k r z') (μ *ᵥ wbPart k r z') = -((Tz k r z' : ℝ) : ℂ) := by
    rw [herm_unitary, hμ', ip_self k r z' hz']
  have key := (Formalism.FourierDecayAlt.P.omega_norm_formula (Fin (k + 1) → ℂ) (herm (Hb k)) (ip_add k) (ip_smul k) (ip_conj k)
    (wbPart k r z) (μ *ᵥ wbPart k r z') (Tz k r z) (Tz k r z')
    (Dmin k r z z' (bigCell k r c μ) ⟨r, by omega⟩) hT hzz hxx).2
  have hom : omF k r z z' c μ = Dmin k r z z' (bigCell k r c μ) ⟨r, by omega⟩ •
      (μ *ᵥ wbPart k r z' +
        (herm (Hb k) (μ *ᵥ wbPart k r z') (wbPart k r z) / ((Tz k r z : ℝ) : ℂ)) • wbPart k r z) := by
    unfold omF prW
    rw [hzz, div_neg, neg_smul, sub_neg_eq_add]
  rw [hom, key, Complex.ofReal_re]
  unfold Gf
  rw [(bigCell_D k r z z' hz hz' c hc μ).2]

/- English proof (translation)
Establish `hl : Hb k * μᴴ * Hb k * μ = 1`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc μᴴ, hμ, Hb_sq]`. Establish `hinv : μ⁻¹ = Hb k * μᴴ * Hb k` using `Matrix.inv_eq_left_inv hl`. Use `⟨hinv, ?_⟩` and prove the remaining obligations. Conclude with `Matrix.mul_nonsing_inv μ (Matrix.isUnit_det_of_left_inverse hl)`.
-/
theorem mu_inv (k : ℕ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hμ : μᴴ * Hb k * μ = Hb k) :
    μ⁻¹ = Hb k * μᴴ * Hb k ∧ μ * μ⁻¹ = 1 := by
  have hl : Hb k * μᴴ * Hb k * μ = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc μᴴ, hμ, Hb_sq]
  have hinv : μ⁻¹ = Hb k * μᴴ * Hb k := Matrix.inv_eq_left_inv hl
  refine ⟨hinv, ?_⟩
  exact Matrix.mul_nonsing_inv μ (Matrix.isUnit_det_of_left_inverse hl)

/- English proof (translation)
Establish `hμ' : μᴴ * Hb k * μ = Hb k` using `hμ`. Establish `hiso : ∀ v w, herm (Hb k) v w = herm (Hb k) (μ *ᵥ v) (μ *ᵥ w)` using `fun v w => by`. Rewrite using `[herm_unitary, hμ']`. Establish `hback : μ *ᵥ (μ⁻¹ *ᵥ wbPart k r z) = wbPart k r z`. Rewrite using `[Matrix.mulVec_mulVec, (mu_inv k μ hμ').2, Matrix.one_mulVec]`.

Establish `hzz` using `ip_self k r z' hz'`. Establish `hxx : herm (Hb k) (μ⁻¹ *ᵥ wbPart k r z) (μ⁻¹ *ᵥ wbPart k r z) = -((Tz k r z : ℝ) : ℂ)`. Rewrite using `[hiso, hback, ip_self k r z hz]`. Establish `hxz : herm (Hb k) (μ⁻¹ *ᵥ wbPart k r z) (wbPart k r z') = starRingEnd ℂ (herm (Hb k) (μ *ᵥ wbPart k r z') (wbPart k r z))`. Rewrite using `[hiso, hback, ip_conj]`.

Establish `key` using `(Formalism.FourierDecayAlt.P.omega_norm_formula (Fin (k + 1) → ℂ) (herm (Hb k)) (ip_add k) (ip_smul k) (ip_conj k) (wbPart k r z') (μ⁻¹ *ᵥ wbPart k r z) (Tz k r z') (Tz k r z) (star (Dmin k r z z' (bigCell k r c μ) ⟨r, by omega⟩)) hT' hzz hxx).2`. Establish `hom : omF' k r z z' c μ = star (Dmin k r z z' (bigCell k r c μ) ⟨r, by omega⟩) • (μ⁻¹ *ᵥ wbPart k r z + (herm (Hb k) (μ⁻¹ *ᵥ wbPart k r z) (wbPart k r z') / ((Tz k r z' : ℝ) : ℂ)) • wbPart k r z')`. Unfold `omF' prW`. Rewrite using `[hzz, div_neg, neg_smul, sub_neg_eq_add]`. Rewrite using `[hom, key, Complex.ofReal_re]`.

Unfold `Gf`. Rewrite using `[(bigCell_D k r z z' hz hz' c hc μ).2, hxz, Complex.star_def, ← map_mul, Complex.normSq_conj, Complex.normSq_conj, mul_comm (Tz k r z') (Tz k r z)]`.
-/
theorem om'_norm (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hz' : inWb k r z')
    (hT' : 0 < Tz k r z') (c : Fin r → ℂ) (hc : ∀ a, c a ≠ 0) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (hμ : μ ∈ UH (Hb k)) :
    (herm (Hb k) (omF' k r z z' c μ) (omF' k r z z' c μ)).re = Gf k r z z' (bigCell k r c μ) / Tz k r z' := by
  have hμ' : μᴴ * Hb k * μ = Hb k := hμ
  have hiso : ∀ v w, herm (Hb k) v w = herm (Hb k) (μ *ᵥ v) (μ *ᵥ w) := fun v w => by
    rw [herm_unitary, hμ']
  have hback : μ *ᵥ (μ⁻¹ *ᵥ wbPart k r z) = wbPart k r z := by
    rw [Matrix.mulVec_mulVec, (mu_inv k μ hμ').2, Matrix.one_mulVec]
  have hzz := ip_self k r z' hz'
  have hxx : herm (Hb k) (μ⁻¹ *ᵥ wbPart k r z) (μ⁻¹ *ᵥ wbPart k r z) = -((Tz k r z : ℝ) : ℂ) := by
    rw [hiso, hback, ip_self k r z hz]
  have hxz : herm (Hb k) (μ⁻¹ *ᵥ wbPart k r z) (wbPart k r z') =
      starRingEnd ℂ (herm (Hb k) (μ *ᵥ wbPart k r z') (wbPart k r z)) := by
    rw [hiso, hback, ip_conj]
  have key := (Formalism.FourierDecayAlt.P.omega_norm_formula (Fin (k + 1) → ℂ) (herm (Hb k)) (ip_add k) (ip_smul k) (ip_conj k)
    (wbPart k r z') (μ⁻¹ *ᵥ wbPart k r z) (Tz k r z') (Tz k r z)
    (star (Dmin k r z z' (bigCell k r c μ) ⟨r, by omega⟩)) hT' hzz hxx).2
  have hom : omF' k r z z' c μ = star (Dmin k r z z' (bigCell k r c μ) ⟨r, by omega⟩) •
      (μ⁻¹ *ᵥ wbPart k r z +
        (herm (Hb k) (μ⁻¹ *ᵥ wbPart k r z) (wbPart k r z') / ((Tz k r z' : ℝ) : ℂ)) • wbPart k r z') := by
    unfold omF' prW
    rw [hzz, div_neg, neg_smul, sub_neg_eq_add]
  rw [hom, key, Complex.ofReal_re]
  unfold Gf
  rw [(bigCell_D k r z z' hz hz' c hc μ).2, hxz, Complex.star_def, ← map_mul, Complex.normSq_conj,
    Complex.normSq_conj, mul_comm (Tz k r z') (Tz k r z)]

def IsPolyG {n : ℕ} (a : Matrix (Fin n) (Fin n) ℂ → ℂ) : Prop :=
  ∃ P : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ, ∀ g, evG g P = a g

namespace IsPolyG

variable {n : ℕ}

/- English proof (translation)
Assemble the required witnesses or components as `⟨MvPolynomial.C c, fun g => by simp [evG]⟩`.
-/
theorem const (c : ℂ) : IsPolyG (n := n) (fun _ => c) := ⟨MvPolynomial.C c, fun g => by simp [evG]⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨MvPolynomial.X (Sum.inl (i, j)), fun g => by simp [evG]⟩`.
-/
theorem entry (i j : Fin n) : IsPolyG (n := n) (fun g => g i j) :=
  ⟨MvPolynomial.X (Sum.inl (i, j)), fun g => by simp [evG]⟩

/- English proof (translation)
Take `⟨P, hP⟩` from `ha`. Take `⟨Q, hQ⟩` from `hb`. Conclude with `⟨P + Q, fun g => by show evG g (P + Q) = a g + b g; rw [← hP, ← hQ]; simp [evG]⟩`.
-/
theorem add {a b : Matrix (Fin n) (Fin n) ℂ → ℂ} (ha : IsPolyG a) (hb : IsPolyG b) :
    IsPolyG (fun g => a g + b g) := by
  obtain ⟨P, hP⟩ := ha
  obtain ⟨Q, hQ⟩ := hb
  exact ⟨P + Q, fun g => by show evG g (P + Q) = a g + b g; rw [← hP, ← hQ]; simp [evG]⟩

/- English proof (translation)
Take `⟨P, hP⟩` from `ha`. Take `⟨Q, hQ⟩` from `hb`. Conclude with `⟨P - Q, fun g => by show evG g (P - Q) = a g - b g; rw [← hP, ← hQ]; simp [evG]⟩`.
-/
theorem sub {a b : Matrix (Fin n) (Fin n) ℂ → ℂ} (ha : IsPolyG a) (hb : IsPolyG b) :
    IsPolyG (fun g => a g - b g) := by
  obtain ⟨P, hP⟩ := ha
  obtain ⟨Q, hQ⟩ := hb
  exact ⟨P - Q, fun g => by show evG g (P - Q) = a g - b g; rw [← hP, ← hQ]; simp [evG]⟩

/- English proof (translation)
Take `⟨P, hP⟩` from `ha`. Take `⟨Q, hQ⟩` from `hb`. Conclude with `⟨P * Q, fun g => by show evG g (P * Q) = a g * b g; rw [← hP, ← hQ]; simp [evG]⟩`.
-/
theorem mul {a b : Matrix (Fin n) (Fin n) ℂ → ℂ} (ha : IsPolyG a) (hb : IsPolyG b) :
    IsPolyG (fun g => a g * b g) := by
  obtain ⟨P, hP⟩ := ha
  obtain ⟨Q, hQ⟩ := hb
  exact ⟨P * Q, fun g => by show evG g (P * Q) = a g * b g; rw [← hP, ← hQ]; simp [evG]⟩

/- English proof (translation)
Use `choose P hP using h`. Conclude with `⟨∑ i ∈ s, P i, fun g => by simp only [← hP]; simp [evG]⟩`.
-/
theorem sum {ι : Type*} (s : Finset ι) {a : ι → Matrix (Fin n) (Fin n) ℂ → ℂ} (h : ∀ i, IsPolyG (a i)) :
    IsPolyG (fun g => ∑ i ∈ s, a i g) := by
  choose P hP using h
  exact ⟨∑ i ∈ s, P i, fun g => by simp only [← hP]; simp [evG]⟩

/- English proof (translation)
Use `choose P hP using h`. Conclude with `⟨∏ i ∈ s, P i, fun g => by simp only [← hP]; simp [evG]⟩`.
-/
theorem prod {ι : Type*} (s : Finset ι) {a : ι → Matrix (Fin n) (Fin n) ℂ → ℂ} (h : ∀ i, IsPolyG (a i)) :
    IsPolyG (fun g => ∏ i ∈ s, a i g) := by
  choose P hP using h
  exact ⟨∏ i ∈ s, P i, fun g => by simp only [← hP]; simp [evG]⟩

/- English proof (translation)
Take `⟨P, hP⟩` from `ha`. Use `⟨MvPolynomial.rename Sum.swap (MvPolynomial.map (starRingEnd ℂ) P), fun g => ?_⟩` and prove the remaining obligations. Use `show evG g _ = starRingEnd ℂ (a g)`. Rewrite using `[← hP]`. Establish `key : ((MvPolynomial.eval (Sum.elim (fun ij : Fin n × Fin n => g ij.1 ij.2) (fun ij => Star.star (g ij.1 ij.2)))).comp ((MvPolynomial.rename (Sum.swap : (Fin n × Fin n) ⊕ (Fin n × Fin n) → _)).toRingHom.comp (MvPolynomial.map (starRingEnd ℂ)))) = (starRingEnd ℂ).comp (MvPolynomia …`.

Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `c`. Simplify using the standard rewrite rules. Apply the tactic sequence `rintro (ij | ij) <;> simp`. Conclude with `congrArg (fun f : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ →+* ℂ => f P) key`.
-/
theorem star {a : Matrix (Fin n) (Fin n) ℂ → ℂ} (ha : IsPolyG a) : IsPolyG (fun g => starRingEnd ℂ (a g)) := by
  obtain ⟨P, hP⟩ := ha
  refine ⟨MvPolynomial.rename Sum.swap (MvPolynomial.map (starRingEnd ℂ) P), fun g => ?_⟩
  show evG g _ = starRingEnd ℂ (a g)
  rw [← hP]
  have key : ((MvPolynomial.eval (Sum.elim (fun ij : Fin n × Fin n => g ij.1 ij.2)
        (fun ij => Star.star (g ij.1 ij.2)))).comp
      ((MvPolynomial.rename (Sum.swap : (Fin n × Fin n) ⊕ (Fin n × Fin n) → _)).toRingHom.comp
        (MvPolynomial.map (starRingEnd ℂ)))) =
      (starRingEnd ℂ).comp (MvPolynomial.eval (Sum.elim (fun ij : Fin n × Fin n => g ij.1 ij.2)
        (fun ij => Star.star (g ij.1 ij.2)))) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp
    · rintro (ij | ij) <;> simp
  exact congrArg (fun f : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ →+* ℂ => f P) key

/- English proof (translation)
Simplify using `only [Matrix.det_apply']`. Conclude with `sum _ fun σ => mul (const _) (prod _ fun i => h (σ i) i)`.
-/
theorem det {m : ℕ} {M : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin m) (Fin m) ℂ} (h : ∀ a b, IsPolyG (fun g => M g a b)) :
    IsPolyG (fun g => (M g).det) := by
  simp only [Matrix.det_apply']
  exact sum _ fun σ => mul (const _) (prod _ fun i => h (σ i) i)

/- English proof (translation)
Simplify using `only [Matrix.mulVec, dotProduct]`. Apply the tactic sequence `exact sum _ fun j => mul (entry i j) (const _)`.
-/
theorem mulVec_right (v : Fin n → ℂ) (i : Fin n) : IsPolyG (n := n) (fun g => (g *ᵥ v) i) := by
  simp only [Matrix.mulVec, dotProduct]
  exact sum _ fun j => mul (entry i j) (const _)

/- English proof (translation)
Simplify using `only [Matrix.mulVec, dotProduct]`. Conclude with `sum _ fun j => mul (const _) (hV j)`.
-/
theorem mulVec_const {m m' : ℕ} (A : Matrix (Fin m') (Fin m) ℂ) {V : Matrix (Fin n) (Fin n) ℂ → Fin m → ℂ}
    (hV : ∀ i, IsPolyG (fun g => V g i)) (i : Fin m') : IsPolyG (fun g => (A *ᵥ V g) i) := by
  simp only [Matrix.mulVec, dotProduct]
  exact sum _ fun j => mul (const _) (hV j)

/- English proof (translation)
Simplify using `only [herm, dotProduct]`. Conclude with `sum _ fun i => mul (const _) (mulVec_const H hV i)`.
-/
theorem herm_left {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) {V : Matrix (Fin n) (Fin n) ℂ → Fin m → ℂ}
    (hV : ∀ i, IsPolyG (fun g => V g i)) (w : Fin m → ℂ) : IsPolyG (fun g => herm H (V g) w) := by
  simp only [herm, dotProduct]
  exact sum _ fun i => mul (const _) (mulVec_const H hV i)

/- English proof (translation)
Simplify using `only [prW, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]`. Conclude with `sub (hV j) (mul (mul (herm_left _ hV zb) (const _)) (const _))`.
-/
theorem prW' (k : ℕ) (zb : Fin (k + 1) → ℂ) {V : Matrix (Fin n) (Fin n) ℂ → Fin (k + 1) → ℂ}
    (hV : ∀ i, IsPolyG (fun g => V g i)) (j : Fin (k + 1)) : IsPolyG (fun g => prW k zb (V g) j) := by
  simp only [prW, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
  exact sub (hV j) (mul (mul (herm_left _ hV zb) (const _)) (const _))

end IsPolyG

/- English proof (translation)
Unfold `Dmin`. Apply `IsPolyG.det` to reduce the goal to its premises. Introduce `a b`. Simplify using `only [Matrix.submatrix_apply, Zhat]`. Conclude with `IsPolyG.herm_left _ (fun i => IsPolyG.mulVec_right _ i) _`.
-/
theorem isPoly_Dmin (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) :
    IsPolyG (fun g => Dmin k r z z' g l) := by
  unfold Dmin
  apply IsPolyG.det
  intro a b
  simp only [Matrix.submatrix_apply, Zhat]
  exact IsPolyG.herm_left _ (fun i => IsPolyG.mulVec_right _ i) _

/- English proof (translation)
Use extensionality with `j j'`. Establish `hj` using `j.isLt`. Establish `hj'` using `j'.isLt`. Establish `h1 : ¬ (wI k r j').val < r` using `by show ¬ (r + j'.val < r); omega`. Establish `h2 : (wI k r j').val ≤ r + k` using `by show r + j'.val ≤ r + k; omega`.

Establish `h3 : r ≤ (wI k r j).val ∧ (wI k r j).val ≤ r + k`. Prove the components needed by the constructor for the conclusion. Use `show r ≤ r + j.val`. Use linear arithmetic over natural numbers and integers. Use `show r + j.val ≤ r + k`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[Matrix.submatrix_apply]`. Unfold `bigCell`. Rewrite using `[dif_neg h1, dif_pos h2, dif_pos h3]`. Apply the tactic sequence `congr 1 <;> exact Fin.ext (by show r + _ - r = _; omega)`.
-/
theorem bigCell_wI (k r : ℕ) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    (bigCell k r c μ).submatrix (wI k r) (wI k r) = μ := by
  ext j j'
  have hj := j.isLt
  have hj' := j'.isLt
  have h1 : ¬ (wI k r j').val < r := by show ¬ (r + j'.val < r); omega
  have h2 : (wI k r j').val ≤ r + k := by show r + j'.val ≤ r + k; omega
  have h3 : r ≤ (wI k r j).val ∧ (wI k r j).val ≤ r + k := by
    constructor
    · show r ≤ r + j.val; omega
    · show r + j.val ≤ r + k; omega
  rw [Matrix.submatrix_apply]
  unfold bigCell
  rw [dif_neg h1, dif_pos h2, dif_pos h3]
  congr 1 <;> exact Fin.ext (by show r + _ - r = _; omega)

/- English proof (translation)
Establish `h1 : ∀ j : Fin (k + 1), IsPolyG (fun g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ => Dmin k r z z' g ⟨r, by omega⟩ * prW k (wbPart k r z) (wbPart k r (g *ᵥ z')) j)` using `fun j => IsPolyG.mul (isPoly_Dmin k r z z' _) (IsPolyG.prW' k _ (fun i => IsPolyG.mulVec_right z' (wI k r i)) j)`. Establish `h2 : ∀ j : Fin (k + 1), IsPolyG (fun g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ => starRingEnd ℂ (Dmin k r z z' g ⟨r, by omega⟩) * prW k (wbPart k r z') (Hb k *ᵥ ((g.submatrix (wI k r) (wI k r))ᴴ *ᵥ (Hb k *ᵥ wbPart k r z))) j)` using `fun j => IsPolyG.mul (isPoly_Dmin k r z z' _).star (IsPolyG.prW' k _ (fun i => IsPolyG.mulVec_const _ (fun i' => by`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Matrix.submatrix_apply]`. Apply the tactic sequence `exact IsPolyG.sum _ fun q => IsPolyG.mul (IsPolyG.entry _ _).star (IsPolyG.const _)) i) j)`. Use `choose p hp using h1`.

Use `choose p' hp' using h2`. Use `⟨p, p', fun c hc μ hμ => ⟨?_, ?_, om_norm k r z z' hz hz' hT c hc μ hμ, om'_norm k r z z' hz hz' hT' c hc μ hμ⟩⟩` and prove the remaining obligations. Use function extensionality and compare the values at `j`. Rewrite using `[hp j]`. Use `beta_reduce`.

Rewrite using `[wbPart_bigCell k r c μ z' hz']`. Both sides reduce to the same expression. Use function extensionality and compare the values at `j`. Rewrite using `[hp' j]`. Use `beta_reduce`.

Rewrite using `[bigCell_wI]`. Unfold `omF'`. Rewrite using `[(mu_inv k μ hμ).1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]`. Both sides reduce to the same expression.
-/
theorem stOm_of_core (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hz' : inWb k r z')
    (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z') : Formalism.MainNotions.S.UnitaryLevelOperators.stOm k r z z' := by
  have h1 : ∀ j : Fin (k + 1), IsPolyG (fun g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ =>
      Dmin k r z z' g ⟨r, by omega⟩ * prW k (wbPart k r z) (wbPart k r (g *ᵥ z')) j) := fun j =>
    IsPolyG.mul (isPoly_Dmin k r z z' _) (IsPolyG.prW' k _ (fun i => IsPolyG.mulVec_right z' (wI k r i)) j)
  have h2 : ∀ j : Fin (k + 1), IsPolyG (fun g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ =>
      starRingEnd ℂ (Dmin k r z z' g ⟨r, by omega⟩) * prW k (wbPart k r z')
        (Hb k *ᵥ ((g.submatrix (wI k r) (wI k r))ᴴ *ᵥ (Hb k *ᵥ wbPart k r z))) j) := fun j =>
    IsPolyG.mul (isPoly_Dmin k r z z' _).star (IsPolyG.prW' k _ (fun i => IsPolyG.mulVec_const _ (fun i' => by
      simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Matrix.submatrix_apply]
      exact IsPolyG.sum _ fun q => IsPolyG.mul (IsPolyG.entry _ _).star (IsPolyG.const _)) i) j)
  choose p hp using h1
  choose p' hp' using h2
  refine ⟨p, p', fun c hc μ hμ => ⟨?_, ?_, om_norm k r z z' hz hz' hT c hc μ hμ,
    om'_norm k r z z' hz hz' hT' c hc μ hμ⟩⟩
  · funext j
    rw [hp j]
    beta_reduce
    rw [wbPart_bigCell k r c μ z' hz']
    rfl
  · funext j
    rw [hp' j]
    beta_reduce
    rw [bigCell_wI]
    unfold omF'
    rw [(mu_inv k μ hμ).1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rfl

end Formalism.MainNotions.InterlacingSignCuts

end PartAOm

section PartAImg

open Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Topology Filter
open scoped ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Formalism.MainNotions.InterlacingSignCuts

/- English proof (translation)
Establish `h1 : IsOpen (OmX (r + 1))`. Establish `: OmX (r + 1) = ⋂ l : Fin (r + 1), {x : Fin (r + 1) → ℂ | x l ≠ 0}`. Use extensionality with `x`. Simplify using `[OmX]`. Rewrite using `[this]`.

Conclude with `isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const`. Establish `h2 : IsOpen {x : Fin (r + 1) → ℂ | Tz k r z * Tz k r z' < Complex.normSq (zOf x)}` using `isOpen_lt continuous_const (Complex.continuous_normSq.comp (continuous_apply _))`. Conclude with `h1.inter h2`.
-/
theorem isOpen_BDom (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : IsOpen (BDom k r z z') := by
  have h1 : IsOpen (OmX (r + 1)) := by
    have : OmX (r + 1) = ⋂ l : Fin (r + 1), {x : Fin (r + 1) → ℂ | x l ≠ 0} := by
      ext x
      simp [OmX]
    rw [this]
    exact isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const
  have h2 : IsOpen {x : Fin (r + 1) → ℂ | Tz k r z * Tz k r z' < Complex.normSq (zOf x)} :=
    isOpen_lt continuous_const (Complex.continuous_normSq.comp (continuous_apply _))
  exact h1.inter h2

/- English proof (translation)
Establish `hc : ∀ a : Fin r, ContDiffAt ℝ ∞ (fun y : Fin (r + 1) → ℂ => cOf y a) x` using `fun a => (contDiff_apply ℝ ℂ a.castSucc).contDiffAt`. Establish `hz : ContDiffAt ℝ ∞ (fun y : Fin (r + 1) → ℂ => zOf y) x` using `(contDiff_apply ℝ ℂ (Fin.last r)).contDiffAt`. Establish `hS : {ζ : ℂ | Tz k r z * Tz k r z' < Complex.normSq ζ} ∈ 𝓝 (zOf x)` using `(isOpen_lt continuous_const Complex.continuous_normSq).mem_nhds hx.2`. Use `contDiffAt_pi' fun i => contDiffAt_pi' fun j => ?_` and prove the remaining obligations. Distinguish the cases in `hj : j.val < r`.

Simplify using `only [bigCell, dif_pos hj] split_ifs`. Conclude with `hc _`. Conclude with `contDiffAt_const`. Distinguish the cases in `hj2 : j.val ≤ r + k`. Simplify using `only [bigCell, dif_neg hj, dif_pos hj2] split_ifs with hi`.

Conclude with `((hsec.1 _ _).contDiffAt hS).comp x hz`. Conclude with `contDiffAt_const`. Simplify using `only [bigCell, dif_neg hj, dif_neg hj2] split_ifs`. Use `ContDiffAt.inv ((Complex.conjCLE.contDiff.contDiffAt).comp x (hc _)) ?_` and prove the remaining obligations. Conclude with `star_ne_zero.2 (hx.1 _)`.

Conclude with `contDiffAt_const`.
-/
theorem contDiffAt_bc (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (hsec : IsSection k r z z' μsec) (x : Fin (r + 1) → ℂ) (hx : x ∈ BDom k r z z') :
    ContDiffAt ℝ ∞ (fun y : Fin (r + 1) → ℂ => bigCell k r (cOf y) (μsec (zOf y))) x := by
  have hc : ∀ a : Fin r, ContDiffAt ℝ ∞ (fun y : Fin (r + 1) → ℂ => cOf y a) x := fun a =>
    (contDiff_apply ℝ ℂ a.castSucc).contDiffAt
  have hz : ContDiffAt ℝ ∞ (fun y : Fin (r + 1) → ℂ => zOf y) x := (contDiff_apply ℝ ℂ (Fin.last r)).contDiffAt
  have hS : {ζ : ℂ | Tz k r z * Tz k r z' < Complex.normSq ζ} ∈ 𝓝 (zOf x) :=
    (isOpen_lt continuous_const Complex.continuous_normSq).mem_nhds hx.2
  refine contDiffAt_pi' fun i => contDiffAt_pi' fun j => ?_
  by_cases hj : j.val < r
  · simp only [bigCell, dif_pos hj]
    split_ifs
    · exact hc _
    · exact contDiffAt_const
  · by_cases hj2 : j.val ≤ r + k
    · simp only [bigCell, dif_neg hj, dif_pos hj2]
      split_ifs with hi
      · exact ((hsec.1 _ _).contDiffAt hS).comp x hz
      · exact contDiffAt_const
    · simp only [bigCell, dif_neg hj, dif_neg hj2]
      split_ifs
      · refine ContDiffAt.inv ((Complex.conjCLE.contDiff.contDiffAt).comp x (hc _)) ?_
        exact star_ne_zero.2 (hx.1 _)
      · exact contDiffAt_const

/- English proof (translation)
Establish `hc : ∀ a, cOf y a ≠ 0` using `fun a => hy.1 a.castSucc`. Establish `h1` using `(bigCell_D k r z z' hz hz' (cOf y) hc (μsec (zOf y))).2`. Rewrite `h1` using `[(hsec.2 (zOf y) hy.2).2]`. Establish `h2` using `(Formalism.QuantumDeterminants.bigCellMinors k r z z' (cOf y) (μsec (zOf y)) hz hz').1 (Fin.last r)`. Simplify using `only [Fin.val_last] at h2`.

Unfold `Gf`. Rewrite using `[h1, h2, Complex.normSq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Gf_bc (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hz' : inWb k r z')
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hsec : IsSection k r z z' μsec)
    (y : Fin (r + 1) → ℂ) (hy : y ∈ BDom k r z z') :
    Gf k r z z' (bigCell k r (cOf y) (μsec (zOf y))) =
      Complex.normSq (∏ a : Fin r with a.val < r, cOf y a) * (Complex.normSq (zOf y) - Tz k r z * Tz k r z') := by
  have hc : ∀ a, cOf y a ≠ 0 := fun a => hy.1 a.castSucc
  have h1 := (bigCell_D k r z z' hz hz' (cOf y) hc (μsec (zOf y))).2
  rw [(hsec.2 (zOf y) hy.2).2] at h1
  have h2 := (Formalism.QuantumDeterminants.bigCellMinors k r z z' (cOf y) (μsec (zOf y)) hz hz').1 (Fin.last r)
  simp only [Fin.val_last] at h2
  unfold Gf
  rw [h1, h2, Complex.normSq_mul]
  ring

/- English proof (translation)
Use `⟨?_, fun x hx => ?_⟩` and prove the remaining obligations. Introduce `x hx`. Apply `ContDiffAt.contDiffWithinAt` to reduce the goal to its premises. Distinguish the cases in `hB : x ∈ BDom k r z z'`. Establish `hmem : ∀ y ∈ BDom k r z z', bigCell k r (cOf y) (μsec (zOf y)) ∈ UH (Hpk k r)` using `fun y hy => Formalism.QuantumDeterminants.bigCellMem k r _ _ (fun a => hy.1 a.castSucc) (hsec.2 (zOf y) hy.2).1`.

Take `⟨U, F, hU, hxU, hF, hJF⟩` from `hJ _ (hmem x hB)`. Establish `hβ` using `contDiffAt_bc k r z z' μsec hsec x hB`. Establish `hev : Btr k r z z' μsec J =ᶠ[𝓝 x] fun y => ((((∏ a : Fin r, ‖cOf y a‖ ^ (Mdim k r a - 1)) * (Complex.normSq (zOf y) - Tz k r z * Tz k r z') ^ (((k : ℝ) - 1) / 2) : ℝ) : ℂ) • F (bigCell k r (cOf y) (μsec (zOf y))))` using `by filter_upwards [(isOpen_BDom k r z z').mem_nhds hB, hβ.continuousAt.preimage_mem_nhds (hU.mem_nhds hxU)] with y hy hyU`. Unfold `Btr`. Rewrite using `[if_pos hy, hJF _ hyU (hmem y hy)]`.

Use `ContDiffAt.congr_of_eventuallyEq ?_ hev` and prove the remaining obligations. Apply `ContDiffAt.smul` to reduce the goal to its premises. Use `Complex.ofRealCLM.contDiff.contDiffAt.comp x (ContDiffAt.mul ?_ ?_)` and prove the remaining obligations. Use `contDiffAt_prod fun a _ => ContDiffAt.pow ?_ _` and prove the remaining obligations. Conclude with `ContDiffAt.norm ℝ (contDiff_apply ℝ ℂ a.castSucc).contDiffAt (hB.1 a.castSucc)`.

Use `ContDiffAt.rpow_const_of_ne ?_ (ne_of_gt (sub_pos.2 hB.2))` and prove the remaining obligations. Use `ContDiffAt.sub ?_ contDiffAt_const` and prove the remaining obligations. Simplify using `only [Complex.normSq_eq_norm_sq]`. Conclude with `ContDiffAt.norm_sq ℝ (contDiff_apply ℝ ℂ (Fin.last r)).contDiffAt`. Conclude with `(hF.contDiffAt (hU.mem_nhds hxU)).comp x hβ`.

Establish `hcont : Continuous fun y : Fin (r + 1) → ℂ => Complex.normSq (∏ a : Fin r with a.val < r, cOf y a) * (Complex.normSq (zOf y) - Tz k r z * Tz k r z')` using `(Complex.continuous_normSq.comp (continuous_finsetProd _ fun a _ => continuous_apply _)).mul ((Complex.continuous_normSq.comp (continuous_apply _)).sub continuous_const)`. Establish `hx0 : Complex.normSq (∏ a : Fin r with a.val < r, cOf x a) * (Complex.normSq (zOf x) - Tz k r z * Tz k r z') < ε`. Establish `h1 : Complex.normSq (zOf x) - Tz k r z * Tz k r z' ≤ 0`. Establish `: ¬ Tz k r z * Tz k r z' < Complex.normSq (zOf x)` using `fun h => hB ⟨hx, h⟩`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h2` using `Complex.normSq_nonneg (∏ a : Fin r with a.val < r, cOf x a)`. Use the polynomial consequences of the given equalities and inequalities. Establish `hev : Btr k r z z' μsec J =ᶠ[𝓝 x] fun _ => (0 : E)` using `by filter_upwards [(isOpen_lt hcont continuous_const).mem_nhds hx0] with y hy`. Unfold `Btr`. Distinguish the cases in `hyB : y ∈ BDom k r z z'`.

Rewrite using `[if_pos hyB]`. Establish `: J (bigCell k r (cOf y) (μsec (zOf y))) = 0`. Assume the negation of the conclusion as `hne`. Establish `h` using `hK _ hne`. Rewrite `h` using `[Gf_bc k r z z' hz hz' μsec hsec y hyB]`.

Conclude with `absurd hy (not_lt.2 h)`. Rewrite using `[this, smul_zero]`. Rewrite using `[if_neg hyB]`. Conclude with `contDiffAt_const.congr_of_eventuallyEq hev`. Unfold `Btr`.

Rewrite using `[if_neg (fun h => hx h.1)]`.
-/
theorem Btr_mem_WSm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ)
    (z z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hz' : inWb k r z')
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hsec : IsSection k r z z' μsec)
    (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → E) (hJ : SmoothOnH (Hpk k r) J)
    (ε : ℝ) (hε : 0 < ε) (hK : ∀ g, J g ≠ 0 → ε ≤ Gf k r z z' g) :
    Btr k r z z' μsec J ∈ WSm (r + 1) E := by
  refine ⟨?_, fun x hx => ?_⟩
  · intro x hx
    apply ContDiffAt.contDiffWithinAt
    by_cases hB : x ∈ BDom k r z z'
    · have hmem : ∀ y ∈ BDom k r z z', bigCell k r (cOf y) (μsec (zOf y)) ∈ UH (Hpk k r) := fun y hy =>
        Formalism.QuantumDeterminants.bigCellMem k r _ _ (fun a => hy.1 a.castSucc) (hsec.2 (zOf y) hy.2).1
      obtain ⟨U, F, hU, hxU, hF, hJF⟩ := hJ _ (hmem x hB)
      have hβ := contDiffAt_bc k r z z' μsec hsec x hB
      have hev : Btr k r z z' μsec J =ᶠ[𝓝 x] fun y =>
          ((((∏ a : Fin r, ‖cOf y a‖ ^ (Mdim k r a - 1)) *
            (Complex.normSq (zOf y) - Tz k r z * Tz k r z') ^ (((k : ℝ) - 1) / 2) : ℝ) : ℂ) •
          F (bigCell k r (cOf y) (μsec (zOf y)))) := by
        filter_upwards [(isOpen_BDom k r z z').mem_nhds hB,
          hβ.continuousAt.preimage_mem_nhds (hU.mem_nhds hxU)] with y hy hyU
        unfold Btr
        rw [if_pos hy, hJF _ hyU (hmem y hy)]
      refine ContDiffAt.congr_of_eventuallyEq ?_ hev
      apply ContDiffAt.smul
      · refine Complex.ofRealCLM.contDiff.contDiffAt.comp x (ContDiffAt.mul ?_ ?_)
        · refine contDiffAt_prod fun a _ => ContDiffAt.pow ?_ _
          exact ContDiffAt.norm ℝ (contDiff_apply ℝ ℂ a.castSucc).contDiffAt (hB.1 a.castSucc)
        · refine ContDiffAt.rpow_const_of_ne ?_ (ne_of_gt (sub_pos.2 hB.2))
          refine ContDiffAt.sub ?_ contDiffAt_const
          simp only [Complex.normSq_eq_norm_sq]
          exact ContDiffAt.norm_sq ℝ (contDiff_apply ℝ ℂ (Fin.last r)).contDiffAt
      · exact (hF.contDiffAt (hU.mem_nhds hxU)).comp x hβ
    · have hcont : Continuous fun y : Fin (r + 1) → ℂ =>
          Complex.normSq (∏ a : Fin r with a.val < r, cOf y a) *
            (Complex.normSq (zOf y) - Tz k r z * Tz k r z') :=
        (Complex.continuous_normSq.comp (continuous_finsetProd _ fun a _ => continuous_apply _)).mul
          ((Complex.continuous_normSq.comp (continuous_apply _)).sub continuous_const)
      have hx0 : Complex.normSq (∏ a : Fin r with a.val < r, cOf x a) *
          (Complex.normSq (zOf x) - Tz k r z * Tz k r z') < ε := by
        have h1 : Complex.normSq (zOf x) - Tz k r z * Tz k r z' ≤ 0 := by
          have : ¬ Tz k r z * Tz k r z' < Complex.normSq (zOf x) := fun h => hB ⟨hx, h⟩
          linarith
        have h2 := Complex.normSq_nonneg (∏ a : Fin r with a.val < r, cOf x a)
        nlinarith
      have hev : Btr k r z z' μsec J =ᶠ[𝓝 x] fun _ => (0 : E) := by
        filter_upwards [(isOpen_lt hcont continuous_const).mem_nhds hx0] with y hy
        unfold Btr
        by_cases hyB : y ∈ BDom k r z z'
        · rw [if_pos hyB]
          have : J (bigCell k r (cOf y) (μsec (zOf y))) = 0 := by
            by_contra hne
            have h := hK _ hne
            rw [Gf_bc k r z z' hz hz' μsec hsec y hyB] at h
            exact absurd hy (not_lt.2 h)
          rw [this, smul_zero]
        · rw [if_neg hyB]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  · unfold Btr
    rw [if_neg (fun h => hx h.1)]

/- English proof (translation)
Introduce and unpack `φ ⟨J, ⟨hJ, ε, hε, hK⟩, rfl⟩`. Conclude with `Btr_mem_WSm (L.k0 + 1) L.r L.z L.z' h.1 h.2.1 L.μsec h.2.2.2.2 J hJ.1 ε hε hK`.
-/
theorem Img_subset_WSm (L : Lev) (h : L.Std) : L.Img ⊆ (WSm (L.r + 1) L.Hom : Set L.PF) := by
  rintro φ ⟨J, ⟨hJ, ε, hε, hK⟩, rfl⟩
  exact Btr_mem_WSm (L.k0 + 1) L.r L.z L.z' h.1 h.2.1 L.μsec h.2.2.2.2 J hJ.1 ε hε hK

/- English proof (translation)
Take `⟨J, ⟨-, ε, hε, hK⟩, rfl⟩` from `hφ`. Use `⟨ε, hε, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hB : x ∈ BDom (L.k0 + 1) L.r L.z L.z'`. Assume the negation of the conclusion as `hB`. Apply `hx` to reduce the goal to its premises.

Use `show Btr (L.k0 + 1) L.r L.z L.z' L.μsec J x = 0`. Unfold `Btr`. Rewrite using `[if_neg hB]`. Use `⟨hB, ?_⟩` and prove the remaining obligations. Establish `hJ : J (bigCell (L.k0 + 1) L.r (cOf x) (L.μsec (zOf x))) ≠ 0`.

Introduce `h0`. Apply `hx` to reduce the goal to its premises. Use `show Btr (L.k0 + 1) L.r L.z L.z' L.μsec J x = 0`. Unfold `Btr`. Rewrite using `[if_pos hB, h0, smul_zero]`.

Establish `h1` using `hK _ hJ`. Rewrite `h1` using `[Gf_bc (L.k0 + 1) L.r L.z L.z' h.1 h.2.1 L.μsec h.2.2.2.2 x hB]`. Establish `h2 : (Finset.univ.filter fun a : Fin L.r => a.val < L.r) = Finset.univ` using `Finset.filter_true_of_mem fun a _ => a.isLt`. Rewrite `h1` using `[h2]`. Conclude with `h1`.
-/
theorem Img_support (L : Lev) (h : L.Std) (φ : L.PF) (hφ : φ ∈ L.Img) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x, φ x ≠ 0 → x ∈ L.BD ∧
      ε ≤ Complex.normSq (∏ a : Fin L.r, cOf x a) * (Complex.normSq (zOf x) - L.T * L.T') := by
  obtain ⟨J, ⟨-, ε, hε, hK⟩, rfl⟩ := hφ
  refine ⟨ε, hε, fun x hx => ?_⟩
  have hB : x ∈ BDom (L.k0 + 1) L.r L.z L.z' := by
    by_contra hB
    apply hx
    show Btr (L.k0 + 1) L.r L.z L.z' L.μsec J x = 0
    unfold Btr
    rw [if_neg hB]
  refine ⟨hB, ?_⟩
  have hJ : J (bigCell (L.k0 + 1) L.r (cOf x) (L.μsec (zOf x))) ≠ 0 := by
    intro h0
    apply hx
    show Btr (L.k0 + 1) L.r L.z L.z' L.μsec J x = 0
    unfold Btr
    rw [if_pos hB, h0, smul_zero]
  have h1 := hK _ hJ
  rw [Gf_bc (L.k0 + 1) L.r L.z L.z' h.1 h.2.1 L.μsec h.2.2.2.2 x hB] at h1
  have h2 : (Finset.univ.filter fun a : Fin L.r => a.val < L.r) = Finset.univ :=
    Finset.filter_true_of_mem fun a _ => a.isLt
  rw [h2] at h1
  exact h1

end Formalism.MainNotions.InterlacingSignCuts

end PartAImg

section PartAGb

open MeasureTheory Matrix
open scoped ContDiff

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts.Gm

open Formalism.MainNotions.S.UnitaryLevelOperators Formalism.FourierDecayAlt.G

def GermHyp (C₁ : ℝ) (s : ℕ) {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (Φ : Msq s → E) (A : ℝ) : Prop :=
  ContDiffOn ℝ ∞ Φ {Z | mdet Z ≠ 0} ∧
    ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K → ∃ CK : ℝ, ∀ (j : ℕ), (j : ℝ) ≤ C₁ * (s : ℝ) ^ 2 →
      ∀ Z : Msq s, mdet Z ∈ K → ‖iteratedFDeriv ℝ j Φ Z‖ ≤ CK * fNorm Z ^ (-A)

/- English proof (translation)
Introduce `h`. Establish `hsq : wMat n * wMat n = 1`. Use extensionality with `i j`. Simplify using `only [wMat, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Fin.rev_rev]`. Distinguish the cases in `hij : i = j`.

Simplify using `[hij]`. Simplify using `[hij, Ne.symm hij]`. Use `congrArg Matrix.det hsq` as an intermediate fact. Rewrite `this` using `[Matrix.det_mul, h, zero_mul, Matrix.det_one]`. Conclude with `zero_ne_one this`.
-/
theorem wMat_det_ne (n : ℕ) : (wMat n).det ≠ 0 := by
  intro h
  have hsq : wMat n * wMat n = 1 := by
    ext i j
    simp only [wMat, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Fin.rev_rev]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Ne.symm hij]
  have := congrArg Matrix.det hsq
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

/- English proof (translation)
Unfold `fNorm`. Establish `h0 : 0 ≤ Real.sqrt (∑ i, ∑ j, Complex.normSq (Z i j))` using `Real.sqrt_nonneg _`. Use `(pi_norm_le_iff_of_nonneg h0).2 fun i => (pi_norm_le_iff_of_nonneg h0).2 fun j => ?_` and prove the remaining obligations. Establish `h1 : ‖Z i j‖ ^ 2 ≤ ∑ i, ∑ j, Complex.normSq (Z i j)`. Rewrite using `[Complex.sq_norm]`.

Conclude with `(Finset.single_le_sum (f := fun j => Complex.normSq (Z i j)) (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ j)).trans (Finset.single_le_sum (f := fun i => ∑ j, Complex.normSq (Z i j)) (fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ i))`. Simplify using `using Real.abs_le_sqrt h1`.
-/
theorem norm_le_fNorm {s : ℕ} (Z : Msq s) : ‖Z‖ ≤ fNorm Z := by
  unfold fNorm
  have h0 : 0 ≤ Real.sqrt (∑ i, ∑ j, Complex.normSq (Z i j)) := Real.sqrt_nonneg _
  refine (pi_norm_le_iff_of_nonneg h0).2 fun i => (pi_norm_le_iff_of_nonneg h0).2 fun j => ?_
  have h1 : ‖Z i j‖ ^ 2 ≤ ∑ i, ∑ j, Complex.normSq (Z i j) := by
    rw [Complex.sq_norm]
    exact (Finset.single_le_sum (f := fun j => Complex.normSq (Z i j)) (fun j _ => Complex.normSq_nonneg _)
      (Finset.mem_univ j)).trans (Finset.single_le_sum (f := fun i => ∑ j, Complex.normSq (Z i j))
      (fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ i))
  simpa using Real.abs_le_sqrt h1

/- English proof (translation)
Unfold `mdet`. Conclude with `Continuous.matrix_det continuous_id`.
-/
theorem continuous_mdet (s : ℕ) : Continuous (mdet (s := s)) := by
  unfold mdet
  exact Continuous.matrix_det continuous_id

end Formalism.MainNotions.InterlacingSignCuts.Gm

end

end PartAGb

section PartAGw

open MeasureTheory

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts.Gm

section Abstract

variable {X Y K Q : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace K] [MeasurableSpace Q]

structure WeilData (M ν : Measure X) (Sm : Measure Y) (act : X → Y → X) (LUs : Set X)
    (μK : Measure K) (μQ : Measure Q) (κ : K → Y) (Ψ : K × Q → X) (kc : X → K) (γ : K → ℝ) : Prop where
  weil : ∀ F : X → ℂ, Integrable F M → ∫ p, F p ∂M = ∫ p, (∫ u', F (act p u') ∂Sm) ∂ν
  conc : ν LUsᶜ = 0
  emb : MeasurableEmbedding κ
  stab : Sm = Measure.map κ μK
  mp : MeasurePreserving Ψ (μK.prod μQ) M
  kc_meas : Measurable kc
  kc_Ψ : ∀ k q, kc (Ψ (k, q)) = k
  trans : ∀ p ∈ LUs, MeasurePreserving (fun k => kc (act p (κ k))) μK μK
  γ_meas : Measurable γ
  γ_int : Integrable γ μK
  γ_one : ∫ k, γ k ∂μK = 1

variable {M ν : Measure X} {Sm : Measure Y} {act : X → Y → X} {LUs : Set X}
  {μK : Measure K} {μQ : Measure Q} [SFinite μK] [SFinite μQ] {κ : K → Y} {Ψ : K × Q → X} {kc : X → K} {γ : K → ℝ}

/- English proof (translation)
Use `set F : X → ℂ := fun p => (γ (kc p) : ℂ) * f p with hF`. Establish `hγc : Measurable fun p => ((γ (kc p) : ℝ) : ℂ)` using `Complex.measurable_ofReal.comp (W.γ_meas.comp W.kc_meas)`. Establish `hFm : AEStronglyMeasurable F M` using `hγc.aestronglyMeasurable.mul hfm`. Establish `hFΨ : (F ∘ Ψ) = fun z : K × Q => ((γ z.1 : ℝ) : ℂ) * fq z.2`. Use function extensionality and compare the values at `z`.

Take `⟨k, q⟩` from `z`. Simplify using `only [hF, Function.comp, W.kc_Ψ, hfΨ]`. Establish `hγi : Integrable (fun k => ((γ k : ℝ) : ℂ)) μK` using `W.γ_int.ofReal`. Establish `hFi : Integrable F M`. Rewrite using `[← W.mp.map_eq]`.

Rewrite `hFm` using `[← W.mp.map_eq]`. Rewrite using `[integrable_map_measure hFm W.mp.measurable.aemeasurable, hFΨ]`. Conclude with `hγi.mul_prod hfq`. Establish `hI : ∫ p, F p ∂M = ∫ q, fq q ∂μQ`. Rewrite using `[← W.mp.map_eq]`.

Rewrite `hFm` using `[← W.mp.map_eq]`. Rewrite using `[integral_map W.mp.measurable.aemeasurable hFm]`. Establish `: (fun z => F (Ψ z)) = fun z : K × Q => ((γ z.1 : ℝ) : ℂ) * fq z.2` using `hFΨ`. Rewrite using `[this, integral_prod_mul (fun k => ((γ k : ℝ) : ℂ)) fq, integral_complex_ofReal, W.γ_one]`. Simplify using the standard rewrite rules.

Establish `hin : ∀ p ∈ LUs, (∫ u', F (act p u') ∂Sm) = f p`. Introduce `p hp`. Rewrite using `[W.stab, W.emb.integral_map]`. Establish `h1 : (fun k => F (act p (κ k))) = fun k => ((γ (kc (act p (κ k))) : ℝ) : ℂ) * f p`. Use function extensionality and compare the values at `k`.

Simplify using `only [hF, hinv p hp k]`. Rewrite using `[h1, integral_mul_const]`. Establish `h2 : ∫ k, ((γ (kc (act p (κ k))) : ℝ) : ℂ) ∂μK = ∫ k, ((γ k : ℝ) : ℂ) ∂μK`. Establish `hm : AEStronglyMeasurable (fun k => ((γ k : ℝ) : ℂ)) (Measure.map (fun k => kc (act p (κ k))) μK)` using `(Complex.measurable_ofReal.comp W.γ_meas).aestronglyMeasurable`. Use `integral_map (W.trans p hp).measurable.aemeasurable hm` as an intermediate fact.

Rewrite `this` using `[(W.trans p hp).map_eq]`. Conclude with `this.symm`. Rewrite using `[h2, integral_complex_ofReal, W.γ_one]`. Simplify using the standard rewrite rules. Rewrite using `[← hI, W.weil F hFi]`.

Use `integral_congr_ae ?_` and prove the remaining obligations. Establish `: ∀ᵐ p ∂ν, p ∈ LUs`. Rewrite using `[ae_iff]`. Conclude with `W.conc`. Use `filter_upwards [this] with p hp`.

Conclude with `(hin p hp).symm`.
-/
theorem WeilData.scalar (W : WeilData M ν Sm act LUs μK μQ κ Ψ kc γ)
    (f : X → ℂ) (fq : Q → ℂ) (hinv : ∀ p ∈ LUs, ∀ k, f (act p (κ k)) = f p) (hfΨ : ∀ k q, f (Ψ (k, q)) = fq q)
    (hfm : AEStronglyMeasurable f M) (hfq : Integrable fq μQ) :
    ∫ p, f p ∂ν = ∫ q, fq q ∂μQ := by
  set F : X → ℂ := fun p => (γ (kc p) : ℂ) * f p with hF
  have hγc : Measurable fun p => ((γ (kc p) : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp (W.γ_meas.comp W.kc_meas)
  have hFm : AEStronglyMeasurable F M := hγc.aestronglyMeasurable.mul hfm
  have hFΨ : (F ∘ Ψ) = fun z : K × Q => ((γ z.1 : ℝ) : ℂ) * fq z.2 := by
    funext z
    obtain ⟨k, q⟩ := z
    simp only [hF, Function.comp, W.kc_Ψ, hfΨ]
  have hγi : Integrable (fun k => ((γ k : ℝ) : ℂ)) μK := W.γ_int.ofReal
  have hFi : Integrable F M := by
    rw [← W.mp.map_eq]
    rw [← W.mp.map_eq] at hFm
    rw [integrable_map_measure hFm W.mp.measurable.aemeasurable, hFΨ]
    exact hγi.mul_prod hfq
  have hI : ∫ p, F p ∂M = ∫ q, fq q ∂μQ := by
    rw [← W.mp.map_eq]
    rw [← W.mp.map_eq] at hFm
    rw [integral_map W.mp.measurable.aemeasurable hFm]
    have : (fun z => F (Ψ z)) = fun z : K × Q => ((γ z.1 : ℝ) : ℂ) * fq z.2 := hFΨ
    rw [this, integral_prod_mul (fun k => ((γ k : ℝ) : ℂ)) fq, integral_complex_ofReal, W.γ_one]
    simp
  have hin : ∀ p ∈ LUs, (∫ u', F (act p u') ∂Sm) = f p := by
    intro p hp
    rw [W.stab, W.emb.integral_map]
    have h1 : (fun k => F (act p (κ k))) = fun k => ((γ (kc (act p (κ k))) : ℝ) : ℂ) * f p := by
      funext k
      simp only [hF, hinv p hp k]
    rw [h1, integral_mul_const]
    have h2 : ∫ k, ((γ (kc (act p (κ k))) : ℝ) : ℂ) ∂μK = ∫ k, ((γ k : ℝ) : ℂ) ∂μK := by
      have hm : AEStronglyMeasurable (fun k => ((γ k : ℝ) : ℂ))
          (Measure.map (fun k => kc (act p (κ k))) μK) :=
        (Complex.measurable_ofReal.comp W.γ_meas).aestronglyMeasurable
      have := integral_map (W.trans p hp).measurable.aemeasurable hm
      rw [(W.trans p hp).map_eq] at this
      exact this.symm
    rw [h2, integral_complex_ofReal, W.γ_one]
    simp
  rw [← hI, W.weil F hFi]
  refine integral_congr_ae ?_
  have : ∀ᵐ p ∂ν, p ∈ LUs := by
    rw [ae_iff]
    exact W.conc
  filter_upwards [this] with p hp
  exact (hin p hp).symm

/- English proof (translation)
Distinguish the cases in `hi : Integrable h ν`. Use `(SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2 fun ℓ => ?_` and prove the remaining obligations. Rewrite using `[← ContinuousLinearMap.integral_comp_comm ℓ hi, ← ContinuousLinearMap.integral_comp_comm ℓ hqi]`. Conclude with `W.scalar (fun p => ℓ (h p)) (fun q => ℓ (hq q)) (fun p hp k => by simp only [hinv p hp k]) (fun k q => by simp only [hΨ]) (ℓ.continuous.comp_aestronglyMeasurable hmM) (ℓ.integrable_comp hqi)`. Rewrite using `[integral_undef hi]`.

Establish `hn` using `W.scalar (fun p => ((‖h p‖ : ℝ) : ℂ)) (fun q => ((‖hq q‖ : ℝ) : ℂ)) (fun p hp k => by simp only [hinv p hp k]) (fun k q => by simp only [hΨ]) (Complex.continuous_ofReal.comp_aestronglyMeasurable hmM.norm) hqi.norm.ofReal`. Establish `hni : ¬ Integrable (fun p => ((‖h p‖ : ℝ) : ℂ)) ν`. Introduce `hh`. Apply `hi` to reduce the goal to its premises. Establish `h2 : Integrable (fun p => ‖h p‖) ν`.

Use `hh.re` as an intermediate fact. Simplify using `using this`. Conclude with `(integrable_norm_iff hmν).1 h2`. Rewrite `hn` using `[integral_undef hni, integral_complex_ofReal]`. Establish `h0 : ∫ q, ‖hq q‖ ∂μQ = 0` using `by exact_mod_cast hn.symm`.

Establish `h1` using `(integral_eq_zero_iff_of_nonneg (fun q => norm_nonneg (hq q)) hqi.norm).1 h0`. Use `symm`. Use `integral_eq_zero_of_ae ?_` and prove the remaining obligations. Use `filter_upwards [h1] with q hq0`. Simplify using `using hq0`.
-/
theorem WeilData.vector {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (W : WeilData M ν Sm act LUs μK μQ κ Ψ kc γ)
    (h : X → E) (hq : Q → E) (hinv : ∀ p ∈ LUs, ∀ k, h (act p (κ k)) = h p) (hΨ : ∀ k q, h (Ψ (k, q)) = hq q)
    (hmM : AEStronglyMeasurable h M) (hmν : AEStronglyMeasurable h ν) (hqi : Integrable hq μQ) :
    ∫ p, h p ∂ν = ∫ q, hq q ∂μQ := by
  by_cases hi : Integrable h ν
  · refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2 fun ℓ => ?_
    rw [← ContinuousLinearMap.integral_comp_comm ℓ hi, ← ContinuousLinearMap.integral_comp_comm ℓ hqi]
    exact W.scalar (fun p => ℓ (h p)) (fun q => ℓ (hq q)) (fun p hp k => by simp only [hinv p hp k])
      (fun k q => by simp only [hΨ]) (ℓ.continuous.comp_aestronglyMeasurable hmM) (ℓ.integrable_comp hqi)
  · rw [integral_undef hi]
    have hn := W.scalar (fun p => ((‖h p‖ : ℝ) : ℂ)) (fun q => ((‖hq q‖ : ℝ) : ℂ))
      (fun p hp k => by simp only [hinv p hp k]) (fun k q => by simp only [hΨ])
      (Complex.continuous_ofReal.comp_aestronglyMeasurable hmM.norm) hqi.norm.ofReal
    have hni : ¬ Integrable (fun p => ((‖h p‖ : ℝ) : ℂ)) ν := by
      intro hh
      apply hi
      have h2 : Integrable (fun p => ‖h p‖) ν := by
        have := hh.re
        simpa using this
      exact (integrable_norm_iff hmν).1 h2
    rw [integral_undef hni, integral_complex_ofReal] at hn
    have h0 : ∫ q, ‖hq q‖ ∂μQ = 0 := by exact_mod_cast hn.symm
    have h1 := (integral_eq_zero_iff_of_nonneg (fun q => norm_nonneg (hq q)) hqi.norm).1 h0
    symm
    refine integral_eq_zero_of_ae ?_
    filter_upwards [h1] with q hq0
    simpa using hq0

end Abstract

end Formalism.MainNotions.InterlacingSignCuts.Gm

end

end PartAGw

section PartAGj

open MeasureTheory Matrix

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts.Gm

open Formalism.MainNotions.S.UnitaryLevelOperators

/- English proof (translation)
Use function extensionality and compare the values at `i j`. Simplify using `[mm, Matrix.mul_apply]`.
-/
theorem mm_zero_left {s : ℕ} (a : Msq s) : mm (0 : Msq s) a = 0 := by
  funext i j
  simp [mm, Matrix.mul_apply]

/- English proof (translation)
Use function extensionality and compare the values at `i j`. Simplify using `[mm, Matrix.mul_apply]`.
-/
theorem mm_zero_right {s : ℕ} (a : Msq s) : mm a (0 : Msq s) = 0 := by
  funext i j
  simp [mm, Matrix.mul_apply]

/- English proof (translation)
Introduce `F hF`. Rewrite using `[h F hF]`. Use `set G : Msq s × Msq s → ℂ := fun p => ∫ u', F (mm p.1 (mm g (mm (minv u') (minv g))), mm u' p.2) ∂(muStab c g) with hG`. Establish `h0 : G ((0 : Msq s), (0 : Msq s)) = 0`. Simplify using `only [hG, mm_zero_left, mm_zero_right, integral_const, Measure.real, hS, ENNReal.toReal_top, zero_smul]`.

Distinguish the cases in `hi : Integrable G ν`. Rewrite using `[integral_add_measure hi (integrable_dirac (by simp [h0])), integral_dirac, h0, add_zero]`. Establish `hi' : ¬ Integrable G (ν + Measure.dirac ((0 : Msq s), (0 : Msq s)))` using `fun hh => hi hh.left_of_add_measure`. Rewrite using `[integral_undef hi, integral_undef hi']`.
-/
theorem isOrbMeas_add_dirac {s : ℕ} (c : ℂ) (g : Msq s) (ν : Measure (Msq s × Msq s))
    (hS : muStab c g Set.univ = ⊤) (h : IsOrbMeas c g ν) :
    IsOrbMeas c g (ν + Measure.dirac ((0 : Msq s), (0 : Msq s))) := by
  intro F hF
  rw [h F hF]
  set G : Msq s × Msq s → ℂ := fun p =>
    ∫ u', F (mm p.1 (mm g (mm (minv u') (minv g))), mm u' p.2) ∂(muStab c g) with hG
  have h0 : G ((0 : Msq s), (0 : Msq s)) = 0 := by
    simp only [hG, mm_zero_left, mm_zero_right, integral_const, Measure.real, hS, ENNReal.toReal_top, zero_smul]
  by_cases hi : Integrable G ν
  · rw [integral_add_measure hi (integrable_dirac (by simp [h0])), integral_dirac, h0, add_zero]
  · have hi' : ¬ Integrable G (ν + Measure.dirac ((0 : Msq s), (0 : Msq s))) :=
      fun hh => hi hh.left_of_add_measure
    rw [integral_undef hi, integral_undef hi']

/- English proof (translation)
Unfold `OmG`. Rewrite using `[integral_add_measure hi (integrable_dirac (by simp)), integral_dirac]`. Simplify using `[mm_zero_left, mm_zero_right, psiLow, psiUp, psiC]`.
-/
theorem OmG_add_dirac {s : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (c : ℂ) (g : Msq s)
    (ν : Measure (Msq s × Msq s)) (Φ : Msq s → E)
    (hi : Integrable (fun p : Msq s × Msq s => (psiLow c p.1 * psiUp c p.2) • Φ (mm (mm p.1 g) p.2)) ν) :
    OmG c (ν + Measure.dirac ((0 : Msq s), (0 : Msq s))) Φ g = OmG c ν Φ g + Φ 0 := by
  unfold OmG
  rw [integral_add_measure hi (integrable_dirac (by simp)), integral_dirac]
  simp [mm_zero_left, mm_zero_right, psiLow, psiUp, psiC]

end Formalism.MainNotions.InterlacingSignCuts.Gm

end

end PartAGj

section PartAGo1

open MeasureTheory Matrix
open scoped ContDiff

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts.Gm

open Formalism.MainNotions.S.UnitaryLevelOperators Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P

def toM {s : ℕ} (A : Matrix (Fin s) (Fin s) ℂ) : Msq s := fun i j => A i j

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mm_toM {s : ℕ} (A B : Matrix (Fin s) (Fin s) ℂ) : mm (toM A) (toM B) = toM (A * B) := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem minv_toM {s : ℕ} (A : Matrix (Fin s) (Fin s) ℂ) : minv (toM A) = toM A⁻¹ := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toM_of {s : ℕ} (a : Msq s) : toM (Matrix.of a) = a := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem of_toM {s : ℕ} (A : Matrix (Fin s) (Fin s) ℂ) : Matrix.of (toM A) = A := rfl

/- English proof (translation)
Unfold `toM`. Conclude with `continuous_pi fun i => continuous_pi fun j => continuous_id.matrix_elem i j`.
-/
theorem continuous_toM (s : ℕ) : Continuous (toM (s := s)) := by
  unfold toM
  exact continuous_pi fun i => continuous_pi fun j => continuous_id.matrix_elem i j

/- English proof (translation)
Introduce `A B h`. Use extensionality with `i j`. Conclude with `congrFun (congrFun h i) j`.
-/
theorem toM_injective (s : ℕ) : Function.Injective (toM (s := s)) := by
  intro A B h
  ext i j
  exact congrFun (congrFun h i) j

def actG {s : ℕ} (g : Msq s) (p : Msq s × Msq s) (u' : Msq s) : Msq s × Msq s :=
  (mm p.1 (mm g (mm (minv u') (minv g))), mm u' p.2)

def hfun {s : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (c : ℂ) (g : Msq s) (Φ : Msq s → E)
    (p : Msq s × Msq s) : E := (psiLow c p.1 * psiUp c p.2) • Φ (mm (mm p.1 g) p.2)

def LUs (s : ℕ) : Set (Msq s × Msq s) := {p | IsLowerUni (Matrix.of p.1) ∧ IsUpperUni (Matrix.of p.2)}

/- English proof (translation)
Establish `h : LUs s = ((⋂ i, {p : Msq s × Msq s | p.1 i i = 1}) ∩ (⋂ i, ⋂ j, ⋂ (_ : j < i), {p : Msq s × Msq s | p.1 j i = 0})) ∩ ((⋂ i, {p : Msq s × Msq s | p.2 i i = 1}) ∩ (⋂ i, ⋂ j, ⋂ (_ : j < i), {p : Msq s × Msq s | p.2 i j = 0}))`. Use extensionality with `p`. Simplify using `only [LUs, IsLowerUni, IsUpperUni, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Matrix.transpose_apply, Matrix.of_apply]`. Rewrite using `[h]`. Establish `c1 : ∀ i j : Fin s, Continuous fun p : Msq s × Msq s => p.1 i j` using `fun i j => (continuous_apply j).comp ((continuous_apply i).comp continuous_fst)`.

Establish `c2 : ∀ i j : Fin s, Continuous fun p : Msq s × Msq s => p.2 i j` using `fun i j => (continuous_apply j).comp ((continuous_apply i).comp continuous_snd)`. Use `IsClosed.inter (IsClosed.inter ?_ ?_) (IsClosed.inter ?_ ?_)` and prove the remaining obligations. Conclude with `isClosed_iInter fun i => isClosed_eq (c1 i i) continuous_const`. Conclude with `isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_eq (c1 j i) continuous_const`. Conclude with `isClosed_iInter fun i => isClosed_eq (c2 i i) continuous_const`.

Conclude with `isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_eq (c2 i j) continuous_const`.
-/
theorem isClosed_LUs (s : ℕ) : IsClosed (LUs s) := by
  have h : LUs s = ((⋂ i, {p : Msq s × Msq s | p.1 i i = 1}) ∩ (⋂ i, ⋂ j, ⋂ (_ : j < i), {p : Msq s × Msq s | p.1 j i = 0})) ∩
      ((⋂ i, {p : Msq s × Msq s | p.2 i i = 1}) ∩ (⋂ i, ⋂ j, ⋂ (_ : j < i), {p : Msq s × Msq s | p.2 i j = 0})) := by
    ext p
    simp only [LUs, IsLowerUni, IsUpperUni, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Matrix.transpose_apply,
      Matrix.of_apply]
  rw [h]
  have c1 : ∀ i j : Fin s, Continuous fun p : Msq s × Msq s => p.1 i j := fun i j =>
    (continuous_apply j).comp ((continuous_apply i).comp continuous_fst)
  have c2 : ∀ i j : Fin s, Continuous fun p : Msq s × Msq s => p.2 i j := fun i j =>
    (continuous_apply j).comp ((continuous_apply i).comp continuous_snd)
  refine IsClosed.inter (IsClosed.inter ?_ ?_) (IsClosed.inter ?_ ?_)
  · exact isClosed_iInter fun i => isClosed_eq (c1 i i) continuous_const
  · exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_eq (c1 j i) continuous_const
  · exact isClosed_iInter fun i => isClosed_eq (c2 i i) continuous_const
  · exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_eq (c2 i j) continuous_const

/- English proof (translation)
Rewrite using `[G5.muPi_eq, sdScale, ENNReal.ofReal_pow (by positivity)]`. Both sides reduce to the same expression.
-/
theorem sd_smul_volume (c : ℂ) (ι : Type) [Fintype ι] :
    sdScale c (Fintype.card ι) • (volume : Measure (ι → ℂ)) = muPi c ι := by
  rw [G5.muPi_eq, sdScale, ENNReal.ofReal_pow (by positivity)]
  rfl

def iU {s : ℕ} (v : UT s → ℂ) : Msq s := toM (upper v)
def iL {s : ℕ} (v : UT s → ℂ) : Msq s := toM (upper v)ᵀ

/- English proof (translation)
The claim follows from `G5.continuous_upper s`.
-/
theorem continuous_iU (s : ℕ) : Continuous (iU (s := s)) := G5.continuous_upper s
/- English proof (translation)
The claim follows from `(G5.continuous_upper s).matrix_transpose`.
-/
theorem continuous_iL (s : ℕ) : Continuous (iL (s := s)) := (G5.continuous_upper s).matrix_transpose

/- English proof (translation)
Use function extensionality and compare the values at `x i j`. Simplify using `only [upOf, iU, toM, upper, strictUpper, Matrix.add_apply, Matrix.one_apply, Matrix.of_apply]`. Distinguish the cases in `h : i < j`. Simplify using `[h, h.ne]`. Simplify using `[h]`.
-/
theorem upOf_eq {s : ℕ} : (upOf : ({p : Fin s × Fin s // p.1 < p.2} → ℂ) → Msq s) = iU := by
  funext x i j
  simp only [upOf, iU, toM, upper, strictUpper, Matrix.add_apply, Matrix.one_apply, Matrix.of_apply]
  by_cases h : i < j
  · simp [h, h.ne]
  · simp [h]

/- English proof (translation)
Unfold `muUp`. Rewrite using `[upOf_eq, ← sd_smul_volume, Measure.map_smul]`.
-/
theorem muUp_eq (s : ℕ) (c : ℂ) : muUp s c = Measure.map iU (muPi c (UT s)) := by
  unfold muUp
  rw [upOf_eq, ← sd_smul_volume, Measure.map_smul]

def swapE (s : ℕ) : UT s ≃ {p : Fin s × Fin s // p.2 < p.1} where
  toFun p := ⟨(p.1.2, p.1.1), p.2⟩
  invFun p := ⟨(p.1.2, p.1.1), p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/- English proof (translation)
Use function extensionality and compare the values at `x i j`. Simplify using `only [lowOf, iL, toM, upper, strictUpper, Matrix.add_apply, Matrix.one_apply, Matrix.of_apply, Function.comp, Matrix.transpose_apply, swapE, Equiv.coe_fn_mk]`. Distinguish the cases in `h : j < i`. Simplify using `[h, h.ne]`. Distinguish the cases in `h2 : i = j`.

Substitute `h2` using the available equality. Simplify using the standard rewrite rules. Establish `: ¬ j = i` using `fun e => h2 e.symm`. Simplify using `[h, h2, this]`.
-/
theorem lowOf_eq {s : ℕ} : (lowOf : ({p : Fin s × Fin s // p.2 < p.1} → ℂ) → Msq s) = iL ∘ fun x => x ∘ swapE s := by
  funext x i j
  simp only [lowOf, iL, toM, upper, strictUpper, Matrix.add_apply, Matrix.one_apply, Matrix.of_apply, Function.comp,
    Matrix.transpose_apply, swapE, Equiv.coe_fn_mk]
  by_cases h : j < i
  · simp [h, h.ne]
  · by_cases h2 : i = j
    · subst h2; simp
    · have : ¬ j = i := fun e => h2 e.symm
      simp [h, h2, this]

/- English proof (translation)
Unfold `muLow`. Rewrite using `[← Measure.map_smul, sd_smul_volume, lowOf_eq, ← Measure.map_map (continuous_iL s).measurable (G5.mp_comp_equiv c (swapE s)).measurable, (G5.mp_comp_equiv c (swapE s)).map_eq]`.
-/
theorem muLow_eq (s : ℕ) (c : ℂ) : muLow s c = Measure.map iL (muPi c (UT s)) := by
  unfold muLow
  rw [← Measure.map_smul, sd_smul_volume, lowOf_eq,
    ← Measure.map_map (continuous_iL s).measurable (G5.mp_comp_equiv c (swapE s)).measurable,
    (G5.mp_comp_equiv c (swapE s)).map_eq]

/- English proof (translation)
The claim follows from `MeasurePreserving.prod ⟨(continuous_iL s).measurable, (muLow_eq s c).symm⟩ ⟨(continuous_iU s).measurable, (muUp_eq s c).symm⟩`.
-/
theorem mp_iLU (s : ℕ) (c : ℂ) :
    MeasurePreserving (Prod.map (iL (s := s)) (iU (s := s))) ((muPi c (UT s)).prod (muPi c (UT s)))
      ((muLow s c).prod (muUp s c)) :=
  MeasurePreserving.prod ⟨(continuous_iL s).measurable, (muLow_eq s c).symm⟩
    ⟨(continuous_iU s).measurable, (muUp_eq s c).symm⟩

/- English proof (translation)
Unfold `iU`. Rewrite using `[G4.upper_coordU h]`.
-/
theorem iU_coordU {s : ℕ} {A : Matrix (Fin s) (Fin s) ℂ} (h : IsUpperUni A) : iU (coordU A) = toM A := by
  unfold iU; rw [G4.upper_coordU h]

/- English proof (translation)
Unfold `iL`. Rewrite using `[G4.upper_coordU h, Matrix.transpose_transpose]`.
-/
theorem iL_coordU {s : ℕ} {A : Matrix (Fin s) (Fin s) ℂ} (h : IsLowerUni A) : iL (coordU Aᵀ) = toM A := by
  unfold iL; rw [G4.upper_coordU h, Matrix.transpose_transpose]

/- English proof (translation)
Unfold `psiLow psiC psi subSum`. Use `congr 5`. Rewrite using `[Finset.sum_comm, Fin.sum_univ_castSucc]`. Establish `h0 : (∑ i : Fin (n + 1), if i.val = (Fin.last n).val + 1 then l i (Fin.last n) else 0) = 0`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations.

Establish `: ¬ i.val = (Fin.last n).val + 1` using `by simp only [Fin.val_last]; omega`. Rewrite using `[if_neg this]`. Rewrite using `[h0, add_zero]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single k.succ]`.

Simplify using the standard rewrite rules. Introduce `b _ hb`. Establish `: ¬ b.val = k.castSucc.val + 1` using `fun e => hb (Fin.ext (by simpa using e))`. Rewrite using `[if_neg this]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem psiLow_eq {n : ℕ} (c : ℂ) (l : Msq (n + 1)) : psiLow c l = psi c (subSum (Matrix.of l)) := by
  unfold psiLow psiC psi subSum
  congr 5
  rw [Finset.sum_comm, Fin.sum_univ_castSucc]
  have h0 : (∑ i : Fin (n + 1), if i.val = (Fin.last n).val + 1 then l i (Fin.last n) else 0) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    have : ¬ i.val = (Fin.last n).val + 1 := by simp only [Fin.val_last]; omega
    rw [if_neg this]
  rw [h0, add_zero]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single k.succ]
  · simp
  · intro b _ hb
    have : ¬ b.val = k.castSucc.val + 1 := fun e => hb (Fin.ext (by simpa using e))
    rw [if_neg this]
  · intro h; exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Unfold `psiUp psiC psi superSum`. Use `congr 5`. Rewrite using `[Fin.sum_univ_castSucc]`. Establish `h0 : (∑ j : Fin (n + 1), if j.val = (Fin.last n).val + 1 then u (Fin.last n) j else 0) = 0`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations.

Establish `: ¬ i.val = (Fin.last n).val + 1` using `by simp only [Fin.val_last]; omega`. Rewrite using `[if_neg this]`. Rewrite using `[h0, add_zero]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single k.succ]`.

Simplify using the standard rewrite rules. Introduce `b _ hb`. Establish `: ¬ b.val = k.castSucc.val + 1` using `fun e => hb (Fin.ext (by simpa using e))`. Rewrite using `[if_neg this]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem psiUp_eq {n : ℕ} (c : ℂ) (u : Msq (n + 1)) : psiUp c u = psi c (superSum (Matrix.of u)) := by
  unfold psiUp psiC psi superSum
  congr 5
  rw [Fin.sum_univ_castSucc]
  have h0 : (∑ j : Fin (n + 1), if j.val = (Fin.last n).val + 1 then u (Fin.last n) j else 0) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    have : ¬ i.val = (Fin.last n).val + 1 := by simp only [Fin.val_last]; omega
    rw [if_neg this]
  rw [h0, add_zero]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single k.succ]
  · simp
  · intro b _ hb
    have : ¬ b.val = k.castSucc.val + 1 := fun e => hb (Fin.ext (by simpa using e))
    rw [if_neg this]
  · intro h; exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Unfold `psi`. Rewrite using `[← Complex.exp_add]`. Use `congr 1`. Rewrite using `[mul_add, Complex.add_re]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem psi_add (c x y : ℂ) : psi c (x + y) = psi c x * psi c y := by
  unfold psi
  rw [← Complex.exp_add]
  congr 1
  rw [mul_add, Complex.add_re]
  push_cast
  ring

/- English proof (translation)
Simplify using `[psi]`.
-/
theorem psi_zero (c : ℂ) : psi c 0 = 1 := by simp [psi]

end Formalism.MainNotions.InterlacingSignCuts.Gm

end

end PartAGo1

section PartAGo2

open MeasureTheory Matrix
open scoped ContDiff

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts.Gm

open Formalism.MainNotions.S.UnitaryLevelOperators Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P

/- English proof (translation)
Take `⟨a, b⟩` from `p`. Take `⟨hl, hu⟩` from `hp`. Use `set l : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := Matrix.of a with hl'`. Use `set u : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := Matrix.of b with hu''`. Establish `hact : actG (toM G) (a, b) (toM u') = (toM (l * (G * u'⁻¹ * G⁻¹)), toM (u' * u))` using `by show (toM (l * (G * (u'⁻¹ * G⁻¹))), toM (u' * u)) = _`.

Rewrite using `[Matrix.mul_assoc G]`. Rewrite using `[hact]`. Unfold `hfun`. Establish `e1 : mm (mm (toM (l * (G * u'⁻¹ * G⁻¹))) (toM G)) (toM (u' * u)) = mm (mm a (toM G)) b` using `by show toM (l * (G * u'⁻¹ * G⁻¹) * G * (u' * u)) = toM (l * G * u)`. Use `congr 1`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = l * G * u := by rw [hG, Matrix.mul_one, G4.upper_inv_mul hu', Matrix.mul_one]`. Simplify using `only []`. Rewrite using `[e1, psiLow_eq, psiUp_eq, psiLow_eq, psiUp_eq, of_toM, of_toM, ((Formalism.FourierDecayAlt.P.character_additive n l (G * u'⁻¹ * G⁻¹)).2 hl hA), ((Formalism.FourierDecayAlt.P.character_additive n u' u).1 hu' hu)]`.

Use `congr 1`. Rewrite using `[← psi_add, ← psi_add]`. Use `congr 1`. Establish `: subSum l + subSum (G * u'⁻¹ * G⁻¹) + (superSum u' + superSum u) = subSum l + superSum u + (subSum (G * u'⁻¹ * G⁻¹) + superSum u')` using `by ring`. Rewrite using `[this, hch, add_zero]`.
-/
theorem hfun_inv {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (c : ℂ)
    (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hG : G⁻¹ * G = 1) (Φ : Msq (n + 1) → E)
    (p : Msq (n + 1) × Msq (n + 1)) (hp : p ∈ LUs (n + 1)) (u' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hu' : IsUpperUni u') (hA : IsLowerUni (G * u'⁻¹ * G⁻¹)) (hch : subSum (G * u'⁻¹ * G⁻¹) + superSum u' = 0) :
    hfun c (toM G) Φ (actG (toM G) p (toM u')) = hfun c (toM G) Φ p := by
  obtain ⟨a, b⟩ := p
  obtain ⟨hl, hu⟩ := hp
  set l : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := Matrix.of a with hl'
  set u : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := Matrix.of b with hu''
  have hact : actG (toM G) (a, b) (toM u') = (toM (l * (G * u'⁻¹ * G⁻¹)), toM (u' * u)) := by
    show (toM (l * (G * (u'⁻¹ * G⁻¹))), toM (u' * u)) = _
    rw [Matrix.mul_assoc G]
  rw [hact]
  unfold hfun
  have e1 : mm (mm (toM (l * (G * u'⁻¹ * G⁻¹))) (toM G)) (toM (u' * u)) = mm (mm a (toM G)) b := by
    show toM (l * (G * u'⁻¹ * G⁻¹) * G * (u' * u)) = toM (l * G * u)
    congr 1
    calc l * (G * u'⁻¹ * G⁻¹) * G * (u' * u) = l * G * (u'⁻¹ * (G⁻¹ * G) * u') * u := by
          simp only [Matrix.mul_assoc]
      _ = l * G * u := by rw [hG, Matrix.mul_one, G4.upper_inv_mul hu', Matrix.mul_one]
  simp only []
  rw [e1, psiLow_eq, psiUp_eq, psiLow_eq, psiUp_eq, of_toM, of_toM,
    ((Formalism.FourierDecayAlt.P.character_additive n l (G * u'⁻¹ * G⁻¹)).2 hl hA),
    ((Formalism.FourierDecayAlt.P.character_additive n u' u).1 hu' hu)]
  congr 1
  rw [← psi_add, ← psi_add]
  congr 1
  have : subSum l + subSum (G * u'⁻¹ * G⁻¹) + (superSum u' + superSum u) =
      subSum l + superSum u + (subSum (G * u'⁻¹ * G⁻¹) + superSum u') := by ring
  rw [this, hch, add_zero]

/- English proof (translation)
Unfold `psiC`. Use `fun_prop`.
-/
theorem continuous_psiC (c : ℂ) : Continuous (psiC c) := by
  unfold psiC
  fun_prop

/- English proof (translation)
Unfold `psiLow`. Use `(continuous_psiC c).comp (continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_)` and prove the remaining obligations. Use `split_ifs`. Conclude with `(continuous_apply j).comp (continuous_apply i)`. Conclude with `continuous_const`.
-/
theorem continuous_psiLow {s : ℕ} (c : ℂ) : Continuous (psiLow (s := s) c) := by
  unfold psiLow
  refine (continuous_psiC c).comp (continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_)
  split_ifs
  · exact (continuous_apply j).comp (continuous_apply i)
  · exact continuous_const

/- English proof (translation)
Unfold `psiUp`. Use `(continuous_psiC c).comp (continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_)` and prove the remaining obligations. Use `split_ifs`. Conclude with `(continuous_apply j).comp (continuous_apply i)`. Conclude with `continuous_const`.
-/
theorem continuous_psiUp {s : ℕ} (c : ℂ) : Continuous (psiUp (s := s) c) := by
  unfold psiUp
  refine (continuous_psiC c).comp (continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_)
  split_ifs
  · exact (continuous_apply j).comp (continuous_apply i)
  · exact continuous_const

/- English proof (translation)
Establish `h : Continuous fun p : Matrix (Fin s) (Fin s) ℂ × Matrix (Fin s) (Fin s) ℂ => p.1 * G * p.2` using `(continuous_fst.matrix_mul continuous_const).matrix_mul continuous_snd`. Conclude with `h`.
-/
theorem continuous_mmm {s : ℕ} (G : Matrix (Fin s) (Fin s) ℂ) :
    Continuous fun p : Msq s × Msq s => mm (mm p.1 (toM G)) p.2 := by
  have h : Continuous fun p : Matrix (Fin s) (Fin s) ℂ × Matrix (Fin s) (Fin s) ℂ => p.1 * G * p.2 :=
    (continuous_fst.matrix_mul continuous_const).matrix_mul continuous_snd
  exact h

/- English proof (translation)
Establish `hc : ContinuousOn (hfun c (toM G) Φ) (LUs s)`. Unfold `hfun`. Use `ContinuousOn.smul ?_ ?_` and prove the remaining obligations. Conclude with `(((continuous_psiLow c).comp continuous_fst).mul ((continuous_psiUp c).comp continuous_snd)).continuousOn`. Use `hΦ.comp (continuous_mmm G).continuousOn ?_` and prove the remaining obligations.

Introduce `p hp`. Use `show (Matrix.of p.1 * G * Matrix.of p.2).det ≠ 0`. Rewrite using `[Matrix.det_mul, Matrix.det_mul, G4.lowerUni_det hp.1, G4.upperUni_det hp.2]`. Simplify using `using hdet`. Establish `h1` using `hc.aestronglyMeasurable (μ := μ) (isClosed_LUs s).measurableSet`.

Establish `h2 : μ.restrict (LUs s) = μ`. Use `Measure.restrict_eq_self_of_ae_mem ?_` and prove the remaining obligations. Rewrite using `[ae_iff]`. Conclude with `hμ`. Rewrite `h1` using `[h2]`. Then use the resulting hypothesis.
-/
theorem hfun_aesm {s : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (c : ℂ)
    (G : Matrix (Fin s) (Fin s) ℂ) (hdet : G.det ≠ 0) (Φ : Msq s → E) (hΦ : ContinuousOn Φ {Z | mdet Z ≠ 0})
    (μ : Measure (Msq s × Msq s)) (hμ : μ (LUs s)ᶜ = 0) : AEStronglyMeasurable (hfun c (toM G) Φ) μ := by
  have hc : ContinuousOn (hfun c (toM G) Φ) (LUs s) := by
    unfold hfun
    refine ContinuousOn.smul ?_ ?_
    · exact (((continuous_psiLow c).comp continuous_fst).mul ((continuous_psiUp c).comp continuous_snd)).continuousOn
    · refine hΦ.comp (continuous_mmm G).continuousOn ?_
      intro p hp
      show (Matrix.of p.1 * G * Matrix.of p.2).det ≠ 0
      rw [Matrix.det_mul, Matrix.det_mul, G4.lowerUni_det hp.1, G4.upperUni_det hp.2]
      simpa using hdet
  have h1 := hc.aestronglyMeasurable (μ := μ) (isClosed_LUs s).measurableSet
  have h2 : μ.restrict (LUs s) = μ := by
    refine Measure.restrict_eq_self_of_ae_mem ?_
    rw [ae_iff]
    exact hμ
  rwa [h2] at h1

/- English proof (translation)
Establish `h` using `((G5.mp_invU β n).comp (G5.mp_lmulU β n (coordU (upper b)⁻¹))).comp (G5.mp_invU β n)`. Establish `he : (fun k : UT n → ℂ => coordU (upper k * upper b)) = ((fun v : UT n → ℂ => coordU (upper v)⁻¹) ∘ fun u : UT n → ℂ => coordU (upper (coordU (upper b)⁻¹) * upper u)) ∘ fun v : UT n → ℂ => coordU (upper v)⁻¹`. Use function extensionality and compare the values at `k`. Simplify using `only [Function.comp]`. Establish `hb` using `G4.upperUni_upper b`.

Establish `hk` using `G4.upperUni_upper k`. Rewrite using `[G4.upper_coordU (G4.upperUni_inv hb), G4.upper_coordU (G4.upperUni_inv hk), G4.upper_coordU (G4.upperUni_mul (G4.upperUni_inv hb) (G4.upperUni_inv hk)), ← Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv]`. Rewrite using `[Matrix.det_mul, G4.upperUni_det hk, G4.upperUni_det hb]`. Simplify using the standard rewrite rules. Rewrite using `[he]`.

Conclude with `h`.
-/
theorem mp_rmulU (β : ℂ) (n : ℕ) (b : UT n → ℂ) :
    MeasurePreserving (fun k : UT n → ℂ => coordU (upper k * upper b)) (muPi β (UT n)) (muPi β (UT n)) := by
  have h := ((G5.mp_invU β n).comp (G5.mp_lmulU β n (coordU (upper b)⁻¹))).comp (G5.mp_invU β n)
  have he : (fun k : UT n → ℂ => coordU (upper k * upper b)) =
      ((fun v : UT n → ℂ => coordU (upper v)⁻¹) ∘ fun u : UT n → ℂ => coordU (upper (coordU (upper b)⁻¹) * upper u)) ∘
        fun v : UT n → ℂ => coordU (upper v)⁻¹ := by
    funext k
    simp only [Function.comp]
    have hb := G4.upperUni_upper b
    have hk := G4.upperUni_upper k
    rw [G4.upper_coordU (G4.upperUni_inv hb), G4.upper_coordU (G4.upperUni_inv hk),
      G4.upper_coordU (G4.upperUni_mul (G4.upperUni_inv hb) (G4.upperUni_inv hk)), ← Matrix.mul_inv_rev,
      Matrix.nonsing_inv_nonsing_inv]
    rw [Matrix.det_mul, G4.upperUni_det hk, G4.upperUni_det hb]
    simp
  rw [he]
  exact h

/- English proof (translation)
Establish `hd : (B * k⁻¹).det = 1`. Rewrite using `[Matrix.det_mul, G4.upperUni_det hB, G4.upperUni_det (G4.upperUni_inv hk), one_mul]`. Establish `h1 : (B * k⁻¹)⁻¹ = (B * k⁻¹).adjugate`. Rewrite using `[Matrix.inv_def, hd, Ring.inverse_one, one_smul]`. Rewrite using `[← h1, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv]`.

Rewrite using `[G4.upperUni_det hk]`. Conclude with `isUnit_one`.
-/
theorem adj_core {d : ℕ} {B k : Matrix (Fin d) (Fin d) ℂ} (hB : IsUpperUni B) (hk : IsUpperUni k) :
    (B * k⁻¹).adjugate = k * B⁻¹ := by
  have hd : (B * k⁻¹).det = 1 := by
    rw [Matrix.det_mul, G4.upperUni_det hB, G4.upperUni_det (G4.upperUni_inv hk), one_mul]
  have h1 : (B * k⁻¹)⁻¹ = (B * k⁻¹).adjugate := by
    rw [Matrix.inv_def, hd, Ring.inverse_one, one_smul]
  rw [← h1, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv]
  rw [G4.upperUni_det hk]
  exact isUnit_one

/- English proof (translation)
Use `set B : Set (ι → ℂ) := Metric.closedBall 0 1 with hB`. Establish `hBm : MeasurableSet B` using `measurableSet_closedBall`. Establish `hc : Real.toNNReal (‖β‖ / (2 * Real.pi)) ≠ 0`. Establish `: 0 < ‖β‖ / (2 * Real.pi)` using `div_pos (norm_pos_iff.2 hβ) (by positivity)`. Conclude with `(Real.toNNReal_pos.2 this).ne'`.

Establish `hval : muPi β ι B = ((Real.toNNReal (‖β‖ / (2 * Real.pi)) ^ Fintype.card ι : NNReal) : ENNReal) * volume B`. Rewrite using `[G5.muPi_eq]`. Both sides reduce to the same expression. Establish `hpos : muPi β ι B ≠ 0`. Rewrite using `[hval]`.

Use `mul_ne_zero ?_ (Metric.measure_closedBall_pos volume _ one_pos).ne'` and prove the remaining obligations. Conclude with `pow_ne_zero _ hc` after adjusting the coercions. Establish `hfin : muPi β ι B ≠ ⊤`. Rewrite using `[hval]`. Conclude with `ENNReal.mul_ne_top ENNReal.coe_ne_top measure_closedBall_lt_top.ne`.

Use `⟨B.indicator fun _ => ((muPi β ι).real B)⁻¹, measurable_const.indicator hBm, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[integrable_indicator_iff hBm]`. Conclude with `integrableOn_const hfin`. Rewrite using `[integral_indicator_const _ hBm, smul_eq_mul]`. Use `mul_inv_cancel₀ ?_` and prove the remaining obligations.

Conclude with `(ENNReal.toReal_pos hpos hfin).ne'`.
-/
theorem exists_gamma (β : ℂ) (hβ : β ≠ 0) (ι : Type) [Fintype ι] :
    ∃ γ : (ι → ℂ) → ℝ, Measurable γ ∧ Integrable γ (muPi β ι) ∧ ∫ k, γ k ∂(muPi β ι) = 1 := by
  set B : Set (ι → ℂ) := Metric.closedBall 0 1 with hB
  have hBm : MeasurableSet B := measurableSet_closedBall
  have hc : Real.toNNReal (‖β‖ / (2 * Real.pi)) ≠ 0 := by
    have : 0 < ‖β‖ / (2 * Real.pi) := div_pos (norm_pos_iff.2 hβ) (by positivity)
    exact (Real.toNNReal_pos.2 this).ne'
  have hval : muPi β ι B = ((Real.toNNReal (‖β‖ / (2 * Real.pi)) ^ Fintype.card ι : NNReal) : ENNReal) * volume B := by
    rw [G5.muPi_eq]
    rfl
  have hpos : muPi β ι B ≠ 0 := by
    rw [hval]
    refine mul_ne_zero ?_ (Metric.measure_closedBall_pos volume _ one_pos).ne'
    exact_mod_cast pow_ne_zero _ hc
  have hfin : muPi β ι B ≠ ⊤ := by
    rw [hval]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top measure_closedBall_lt_top.ne
  refine ⟨B.indicator fun _ => ((muPi β ι).real B)⁻¹, measurable_const.indicator hBm, ?_, ?_⟩
  · rw [integrable_indicator_iff hBm]
    exact integrableOn_const hfin
  · rw [integral_indicator_const _ hBm, smul_eq_mul]
    refine mul_inv_cancel₀ ?_
    exact (ENNReal.toReal_pos hpos hfin).ne'

end Formalism.MainNotions.InterlacingSignCuts.Gm

end

end PartAGo2

section PartAGo3

open MeasureTheory Matrix
open scoped ContDiff

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts.Gm

open Formalism.MainNotions.S.UnitaryLevelOperators Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P

/- English proof (translation)
Use function extensionality and compare the values at `i j`. Simplify using `only [gTC, toM, ptBlock, Formalism.MainNotions.S.ptEntry, Nat.add_sub_cancel]`. Proceed by induction on `i using Fin.lastCases with`. Consider the case `last`. Proceed by induction on `j using Fin.lastCases with`.

Consider the case `last => simp [G5.blk_ll]`. Consider the case `cast j`. Establish `hj : j.val < n` using `j.2`. Establish `: ¬ n ≤ j.val` using `by omega`. Simplify using `[G5.blk_lc, this]`.

Consider the case `cast i`. Establish `hi : i.val < n` using `i.2`. Proceed by induction on `j using Fin.lastCases with`. Consider the case `last`. Establish `: ¬ n ≤ i.val` using `by omega`.

Simplify using `[G5.blk_cl, this]`. Consider the case `cast j`. Establish `hj : j.val < n` using `j.2`. Rewrite using `[G5.blk_cc]`. Simplify using `only [Fin.val_castSucc, hi, hj, and_self, if_true, Matrix.smul_apply, wMat, Matrix.of_apply, smul_eq_mul]`.

Distinguish the cases in `h : j = i.rev`. Establish `: i.val + j.val + 1 = n` using `by rw [h, Fin.val_rev]; omega`. Rewrite using `[if_pos this, if_pos h, mul_one]`. Establish `: ¬ i.val + j.val + 1 = n`. Introduce `e`.

Apply `h` to reduce the goal to its premises. Apply `Fin.ext` to reduce the goal to its premises. Rewrite using `[Fin.val_rev]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg this, if_neg h, mul_zero]`.
-/
theorem gTC_eq (n : ℕ) (t c : ℂ) : gTC (n + 1) t c = toM (ptBlock n t c) := by
  funext i j
  simp only [gTC, toM, ptBlock, Formalism.MainNotions.S.ptEntry, Nat.add_sub_cancel]
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp [G5.blk_ll]
    | cast j =>
      have hj : j.val < n := j.2
      have : ¬ n ≤ j.val := by omega
      simp [G5.blk_lc, this]
  | cast i =>
    have hi : i.val < n := i.2
    induction j using Fin.lastCases with
    | last =>
      have : ¬ n ≤ i.val := by omega
      simp [G5.blk_cl, this]
    | cast j =>
      have hj : j.val < n := j.2
      rw [G5.blk_cc]
      simp only [Fin.val_castSucc, hi, hj, and_self, if_true, Matrix.smul_apply, wMat, Matrix.of_apply, smul_eq_mul]
      by_cases h : j = i.rev
      · have : i.val + j.val + 1 = n := by rw [h, Fin.val_rev]; omega
        rw [if_pos this, if_pos h, mul_one]
      · have : ¬ i.val + j.val + 1 = n := by
          intro e
          apply h
          apply Fin.ext
          rw [Fin.val_rev]; omega
        rw [if_neg this, if_neg h, mul_zero]

def kapB {n : ℕ} (k : UT n → ℂ) : Msq (n + 1) := toM (blk (upper k) 0 0 1)

def PsiB (n : ℕ) : (UT n → ℂ) × BlockCoord n → Msq (n + 1) × Msq (n + 1) :=
  Prod.map iL iU ∘ quotMap n

def TL {n : ℕ} (a : Msq (n + 1)) : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => a i.castSucc j.castSucc

def kcB {n : ℕ} (p : Msq (n + 1) × Msq (n + 1)) : UT n → ℂ := coordU (wMat n * TL p.1 * wMat n).adjugate

def secB {n : ℕ} (q : BlockCoord n) : Msq (n + 1) × Msq (n + 1) := (toM (lowRow q.1), toM (blk (upper q.2.1) q.2.2 0 1))

/- English proof (translation)
Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Proceed by induction on `i using Fin.lastCases with`. Consider the case `last`. Proceed by induction on `j using Fin.lastCases with`. Consider the case `last => simp only [G5.blk_ll]`.

Conclude with `continuous_const`. Consider the case `cast j => simp only [G5.blk_lc]`. Conclude with `continuous_const`. Consider the case `cast i`. Proceed by induction on `j using Fin.lastCases with`.

Consider the case `last => simp only [G5.blk_cl]`. Conclude with `continuous_const`. Consider the case `cast j => simp only [G5.blk_cc]`. Conclude with `(G5.continuous_upper n).matrix_elem i j`.
-/
theorem continuous_blkU (n : ℕ) : Continuous fun k : UT n → ℂ => (blk (upper k) 0 0 1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by
  refine continuous_matrix fun i j => ?_
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp only [G5.blk_ll]; exact continuous_const
    | cast j => simp only [G5.blk_lc]; exact continuous_const
  | cast i =>
    induction j using Fin.lastCases with
    | last => simp only [G5.blk_cl]; exact continuous_const
    | cast j => simp only [G5.blk_cc]; exact (G5.continuous_upper n).matrix_elem i j

/- English proof (translation)
Establish `hc : Continuous (kapB (n` using `n)) := continuous_blkU n`. Use `haveI : T2Space (Msq (n + 1)) := inferInstanceAs (T2Space (Fin (n + 1) → Fin (n + 1) → ℂ))`. Use `hc.measurableEmbedding ?_` and prove the remaining obligations. Introduce `k k' h`. Establish `h2 : upper k = upper k'`.

Use extensionality with `i j`. Use `congrFun (congrFun h i.castSucc) j.castSucc` as an intermediate fact. Simplify `this` using `[kapB, toM, G5.blk_cc]`. Rewrite using `[← G5.coordU_upper k, h2, G5.coordU_upper]`.
-/
theorem kapB_emb (n : ℕ) : MeasurableEmbedding (kapB (n := n)) := by
  have hc : Continuous (kapB (n := n)) := continuous_blkU n
  haveI : T2Space (Msq (n + 1)) := inferInstanceAs (T2Space (Fin (n + 1) → Fin (n + 1) → ℂ))
  refine hc.measurableEmbedding ?_
  intro k k' h
  have h2 : upper k = upper k' := by
    ext i j
    have := congrFun (congrFun h i.castSucc) j.castSucc
    simpa [kapB, toM, G5.blk_cc] using this
  rw [← G5.coordU_upper k, h2, G5.coordU_upper]

/- English proof (translation)
Use `Matrix.inv_eq_right_inv ?_` and prove the remaining obligations. Unfold `ptBlock`. Rewrite using `[G5.blk_mul]`. Simplify using `only [Matrix.smul_mul, Matrix.mul_smul, G5.wMat_mul_self, smul_smul, mul_inv_cancel₀ ht, inv_mul_cancel₀ ht, mul_inv_cancel₀ hc, one_smul, Matrix.vecMulVec_zero, add_zero, Matrix.mulVec_zero, smul_zero, Matrix.zero_vecMul, zero_dotProduct, zero_add]`. Conclude with `G5.blk_one n`.
-/
theorem ptBlock_inv (n : ℕ) (t c : ℂ) (ht : t ≠ 0) (hc : c ≠ 0) :
    (ptBlock n t c)⁻¹ = blk (t⁻¹ • wMat n) 0 0 c⁻¹ := by
  refine Matrix.inv_eq_right_inv ?_
  unfold ptBlock
  rw [G5.blk_mul]
  simp only [Matrix.smul_mul, Matrix.mul_smul, G5.wMat_mul_self, smul_smul, mul_inv_cancel₀ ht, inv_mul_cancel₀ ht, mul_inv_cancel₀ hc, one_smul,
    Matrix.vecMulVec_zero, add_zero, Matrix.mulVec_zero, smul_zero, Matrix.zero_vecMul, zero_dotProduct, zero_add]
  exact G5.blk_one n

/- English proof (translation)
Rewrite using `[ptBlock_inv n t c ht hc]`. Unfold `ptBlock`. Rewrite using `[G5.blk_mul]`. Simplify using `only [Matrix.smul_mul, Matrix.mul_smul, G5.wMat_mul_self, smul_smul, inv_mul_cancel₀ ht, mul_inv_cancel₀ ht, inv_mul_cancel₀ hc, one_smul, Matrix.vecMulVec_zero, add_zero, Matrix.mulVec_zero, smul_zero, Matrix.zero_vecMul, zero_dotProduct, zero_add]`. Conclude with `G5.blk_one n`.
-/
theorem ptBlock_inv_mul (n : ℕ) (t c : ℂ) (ht : t ≠ 0) (hc : c ≠ 0) : (ptBlock n t c)⁻¹ * ptBlock n t c = 1 := by
  rw [ptBlock_inv n t c ht hc]
  unfold ptBlock
  rw [G5.blk_mul]
  simp only [Matrix.smul_mul, Matrix.mul_smul, G5.wMat_mul_self, smul_smul, inv_mul_cancel₀ ht, mul_inv_cancel₀ ht, inv_mul_cancel₀ hc, one_smul,
    Matrix.vecMulVec_zero, add_zero, Matrix.mulVec_zero, smul_zero, Matrix.zero_vecMul, zero_dotProduct, zero_add]
  exact G5.blk_one n

/- English proof (translation)
Rewrite using `[ptBlock_inv n t c ht hc, G5.inv_blk]`. Unfold `ptBlock`. Rewrite using `[G5.blk_mul, G5.blk_mul]`. Simplify using `only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ ht, mul_inv_cancel₀ hc, one_smul, Matrix.vecMulVec_zero, Matrix.zero_vecMulVec, add_zero, Matrix.mulVec_zero, smul_zero, Matrix.zero_vecMul, zero_dotProduct, zero_add, mul_one, inv_mul_cancel₀ ht]`.
-/
theorem conjB (n : ℕ) (t c : ℂ) (ht : t ≠ 0) (hc : c ≠ 0) (k : UT n → ℂ) :
    ptBlock n t c * (blk (upper k) 0 0 1)⁻¹ * (ptBlock n t c)⁻¹ = blk (wMat n * (upper k)⁻¹ * wMat n) 0 0 1 := by
  rw [ptBlock_inv n t c ht hc, G5.inv_blk]
  unfold ptBlock
  rw [G5.blk_mul, G5.blk_mul]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ ht, mul_inv_cancel₀ hc, one_smul,
    Matrix.vecMulVec_zero, Matrix.zero_vecMulVec, add_zero, Matrix.mulVec_zero, smul_zero, Matrix.zero_vecMul, zero_dotProduct,
    zero_add, mul_one, inv_mul_cancel₀ ht]

/- English proof (translation)
Rewrite using `[← conjB n t c ht hc k, Matrix.mul_assoc (ptBlock n t c)]`. Both sides reduce to the same expression.
-/
theorem actB_eq (n : ℕ) (t c : ℂ) (ht : t ≠ 0) (hc : c ≠ 0) (p : Msq (n + 1) × Msq (n + 1)) (k : UT n → ℂ) :
    actG (toM (ptBlock n t c)) p (kapB k) =
      (toM (Matrix.of p.1 * blk (wMat n * (upper k)⁻¹ * wMat n) 0 0 1), toM (blk (upper k) 0 0 1 * Matrix.of p.2)) := by
  rw [← conjB n t c ht hc k, Matrix.mul_assoc (ptBlock n t c)]
  rfl

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show IsLowerUni (lowRow q.1)`. Unfold `lowRow`. Rewrite using `[G4.lowerUni_blk_iff]`. Use `⟨?_, rfl, rfl⟩` and prove the remaining obligations.

Use `show IsUpperUni (1 : Matrix (Fin n) (Fin n) ℂ)ᵀ`. Rewrite using `[Matrix.transpose_one]`. Conclude with `G4.upperUni_one`. Use `show IsUpperUni (blk (upper q.2.1) q.2.2 0 1)`. Rewrite using `[G4.upperUni_blk_iff]`.

Conclude with `⟨G4.upperUni_upper _, rfl, rfl⟩`.
-/
theorem secB_mem {n : ℕ} (q : BlockCoord n) : secB q ∈ LUs (n + 1) := by
  refine ⟨?_, ?_⟩
  · show IsLowerUni (lowRow q.1)
    unfold lowRow
    rw [G4.lowerUni_blk_iff]
    refine ⟨?_, rfl, rfl⟩
    show IsUpperUni (1 : Matrix (Fin n) (Fin n) ℂ)ᵀ
    rw [Matrix.transpose_one]
    exact G4.upperUni_one
  · show IsUpperUni (blk (upper q.2.1) q.2.2 0 1)
    rw [G4.upperUni_blk_iff]
    exact ⟨G4.upperUni_upper _, rfl, rfl⟩

/- English proof (translation)
Rewrite using `[actB_eq n t c ht hc]`. Establish `h1 : IsLowerUni (lowRow q.1 * blk (wMat n * (upper k)⁻¹ * wMat n) 0 0 1)`. Rewrite using `[G5.lowRow_mul, G4.lowerUni_blk_iff]`. Conclude with `⟨G4.lowerUni_conj (G4.upperUni_inv (G4.upperUni_upper k)), rfl, rfl⟩`. Establish `h2 : IsUpperUni (blk (upper k) 0 0 1 * blk (upper q.2.1) q.2.2 0 1)` using `G4.upperUni_mul ((G4.upperUni_blk_iff _ _ _ _).2 ⟨G4.upperUni_upper _, rfl, rfl⟩) ((G4.upperUni_blk_iff _ _ _ _).2 ⟨G4.upperUni_upper _, rfl, rfl⟩)`.

Use `show (iL (coordU (lowRow q.1 * blk (wMat n * (upper k)⁻¹ * wMat n) 0 0 1)ᵀ), iU (coordU (blk (upper k) 0 0 1 * blk (upper q.2.1) q.2.2 0 1))) = _`. Rewrite using `[iL_coordU h1, iU_coordU h2]`. Both sides reduce to the same expression.
-/
theorem PsiB_eq (n : ℕ) (t c : ℂ) (ht : t ≠ 0) (hc : c ≠ 0) (k : UT n → ℂ) (q : BlockCoord n) :
    PsiB n (k, q) = actG (toM (ptBlock n t c)) (secB q) (kapB k) := by
  rw [actB_eq n t c ht hc]
  have h1 : IsLowerUni (lowRow q.1 * blk (wMat n * (upper k)⁻¹ * wMat n) 0 0 1) := by
    rw [G5.lowRow_mul, G4.lowerUni_blk_iff]
    exact ⟨G4.lowerUni_conj (G4.upperUni_inv (G4.upperUni_upper k)), rfl, rfl⟩
  have h2 : IsUpperUni (blk (upper k) 0 0 1 * blk (upper q.2.1) q.2.2 0 1) :=
    G4.upperUni_mul ((G4.upperUni_blk_iff _ _ _ _).2 ⟨G4.upperUni_upper _, rfl, rfl⟩)
      ((G4.upperUni_blk_iff _ _ _ _).2 ⟨G4.upperUni_upper _, rfl, rfl⟩)
  show (iL (coordU (lowRow q.1 * blk (wMat n * (upper k)⁻¹ * wMat n) 0 0 1)ᵀ),
    iU (coordU (blk (upper k) 0 0 1 * blk (upper q.2.1) q.2.2 0 1))) = _
  rw [iL_coordU h1, iU_coordU h2]
  rfl

/- English proof (translation)
Rewrite using `[actB_eq n t c ht hc]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show IsUpperUni (Matrix.of p.1 * blk (wMat n * (upper k)⁻¹ * wMat n) 0 0 1)ᵀ`. Rewrite using `[Matrix.transpose_mul]`. Use `G4.upperUni_mul ?_ hp.1` and prove the remaining obligations.

Conclude with `(G4.lowerUni_blk_iff _ _ _ _).2 ⟨G4.lowerUni_conj (G4.upperUni_inv (G4.upperUni_upper k)), rfl, rfl⟩`. Conclude with `G4.upperUni_mul ((G4.upperUni_blk_iff _ _ _ _).2 ⟨G4.upperUni_upper _, rfl, rfl⟩) hp.2`.
-/
theorem actB_mem (n : ℕ) (t c : ℂ) (ht : t ≠ 0) (hc : c ≠ 0) (p : Msq (n + 1) × Msq (n + 1)) (hp : p ∈ LUs (n + 1))
    (k : UT n → ℂ) : actG (toM (ptBlock n t c)) p (kapB k) ∈ LUs (n + 1) := by
  rw [actB_eq n t c ht hc]
  refine ⟨?_, ?_⟩
  · show IsUpperUni (Matrix.of p.1 * blk (wMat n * (upper k)⁻¹ * wMat n) 0 0 1)ᵀ
    rw [Matrix.transpose_mul]
    refine G4.upperUni_mul ?_ hp.1
    exact (G4.lowerUni_blk_iff _ _ _ _).2 ⟨G4.lowerUni_conj (G4.upperUni_inv (G4.upperUni_upper k)), rfl, rfl⟩
  · exact G4.upperUni_mul ((G4.upperUni_blk_iff _ _ _ _).2 ⟨G4.upperUni_upper _, rfl, rfl⟩) hp.2

/- English proof (translation)
Rewrite using `[actB_eq n t c ht hc]`. Take `⟨l', a, hl', hl⟩` from `G4.exists_blk_lower hp.1`. Establish `hTL : TL p.1 = l'`. Use extensionality with `i j`. Use `show (Matrix.of p.1) i.castSucc j.castSucc = l' i j`.

Rewrite using `[hl, G5.blk_cc]`. Establish `hB` using `G4.upperUni_conj hl'`. Rewrite using `[hTL]`. Use `⟨?_, hB⟩` and prove the remaining obligations. Unfold `kcB`.

Establish `h2 : TL (toM (Matrix.of p.1 * blk (wMat n * (upper k)⁻¹ * wMat n) 0 0 1)) = l' * (wMat n * (upper k)⁻¹ * wMat n)`. Rewrite using `[hl, G5.blk_mul]`. Use extensionality with `i j`. Use `show blk _ _ _ _ i.castSucc j.castSucc = _`. Rewrite using `[G5.blk_cc]`.

Simplify using the standard rewrite rules. Simplify using `only []`. Rewrite using `[h2]`. Establish `h3 : wMat n * (l' * (wMat n * (upper k)⁻¹ * wMat n)) * wMat n = (wMat n * l' * wMat n) * (upper k)⁻¹`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[h3, adj_core hB (G4.upperUni_upper k)]`.
-/
theorem kcB_act (n : ℕ) (t c : ℂ) (ht : t ≠ 0) (hc : c ≠ 0) (p : Msq (n + 1) × Msq (n + 1)) (hp : p ∈ LUs (n + 1))
    (k : UT n → ℂ) :
    kcB (actG (toM (ptBlock n t c)) p (kapB k)) = coordU (upper k * (wMat n * TL p.1 * wMat n)⁻¹) ∧
      IsUpperUni (wMat n * TL p.1 * wMat n) := by
  rw [actB_eq n t c ht hc]
  obtain ⟨l', a, hl', hl⟩ := G4.exists_blk_lower hp.1
  have hTL : TL p.1 = l' := by
    ext i j
    show (Matrix.of p.1) i.castSucc j.castSucc = l' i j
    rw [hl, G5.blk_cc]
  have hB := G4.upperUni_conj hl'
  rw [hTL]
  refine ⟨?_, hB⟩
  unfold kcB
  have h2 : TL (toM (Matrix.of p.1 * blk (wMat n * (upper k)⁻¹ * wMat n) 0 0 1)) = l' * (wMat n * (upper k)⁻¹ * wMat n) := by
    rw [hl, G5.blk_mul]
    ext i j
    show blk _ _ _ _ i.castSucc j.castSucc = _
    rw [G5.blk_cc]
    simp
  simp only []
  rw [h2]
  have h3 : wMat n * (l' * (wMat n * (upper k)⁻¹ * wMat n)) * wMat n = (wMat n * l' * wMat n) * (upper k)⁻¹ := by
    calc wMat n * (l' * (wMat n * (upper k)⁻¹ * wMat n)) * wMat n
        = wMat n * l' * wMat n * (upper k)⁻¹ * (wMat n * wMat n) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [G5.wMat_mul_self, Matrix.mul_one]
  rw [h3, adj_core hB (G4.upperUni_upper k)]

/- English proof (translation)
Unfold `kcB`. Use `(G5.continuous_coordU n).comp (Continuous.matrix_adjugate ?_)` and prove the remaining obligations. Use `(continuous_const.matrix_mul ?_).matrix_mul continuous_const` and prove the remaining obligations. Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Conclude with `(continuous_apply j.castSucc).comp ((continuous_apply i.castSucc).comp continuous_fst)`.
-/
theorem continuous_kcB (n : ℕ) : Continuous (kcB (n := n)) := by
  unfold kcB
  refine (G5.continuous_coordU n).comp (Continuous.matrix_adjugate ?_)
  refine (continuous_const.matrix_mul ?_).matrix_mul continuous_const
  refine continuous_matrix fun i j => ?_
  exact (continuous_apply j.castSucc).comp ((continuous_apply i.castSucc).comp continuous_fst)

def StabMeasBlock : Prop :=
  ∀ (n : ℕ) (β t c : ℂ), β ≠ 0 → t ≠ 0 → c ≠ 0 →
    muStab β (gTC (n + 1) t c) = Measure.map (kapB (n := n)) (muPi β (UT n))

/- English proof (translation)
Take `⟨γ, hγm, hγi, hγ1⟩` from `exists_gamma β hβ (UT n)`. Use `⟨γ, ?_⟩` and prove the remaining obligations. Establish `hstab : muStab β (toM (ptBlock n t c)) = Measure.map (kapB (n` using `n)) (muPi β (UT n)) := by`. Rewrite using `[← gTC_eq]`. Conclude with `hS n β t c hβ ht hc`.

Establish `hmp : MeasurePreserving (PsiB n) ((muPi β (UT n)).prod (muBlock β n)) ((muLow (n + 1) β).prod (muUp (n + 1) β))` using `(mp_iLU (n + 1) β).comp (Formalism.FourierDecayAlt.P.quotient_measure n β)`. Use `WeilData.mk hν hconc (kapB_emb n) hstab hmp (continuous_kcB n).measurable ?_ ?_ hγm hγi hγ1` and prove the remaining obligations. Introduce `k q`. Rewrite using `[PsiB_eq n t c ht hc, (kcB_act n t c ht hc _ (secB_mem q) k).1]`. Establish `: TL (secB q).1 = 1`.

Use extensionality with `i j`. Use `show lowRow q.1 i.castSucc j.castSucc = _`. Unfold `lowRow`. Rewrite using `[G5.blk_cc]`. Rewrite using `[this, Matrix.mul_one, G5.wMat_mul_self, inv_one, Matrix.mul_one, G5.coordU_upper]`.

Introduce `p hp`. Establish `hB` using `(kcB_act n t c ht hc p hp 0).2`. Establish `he : (fun k => kcB (actG (toM (ptBlock n t c)) p (kapB k))) = fun k => coordU (upper k * upper (coordU (wMat n * TL p.1 * wMat n)⁻¹))`. Use function extensionality and compare the values at `k`. Rewrite using `[(kcB_act n t c ht hc p hp k).1, G4.upper_coordU (G4.upperUni_inv hB)]`.

Rewrite using `[he]`. Conclude with `mp_rmulU β n _`.
-/
theorem weilBlock (hS : StabMeasBlock) (n : ℕ) (β t c : ℂ) (hβ : β ≠ 0) (ht : t ≠ 0) (hc : c ≠ 0)
    (ν : Measure (Msq (n + 1) × Msq (n + 1))) (hν : IsOrbMeas β (toM (ptBlock n t c)) ν) (hconc : ν (LUs (n + 1))ᶜ = 0) :
    ∃ γ, WeilData ((muLow (n + 1) β).prod (muUp (n + 1) β)) ν (muStab β (toM (ptBlock n t c)))
      (actG (toM (ptBlock n t c))) (LUs (n + 1)) (muPi β (UT n)) (muBlock β n) kapB (PsiB n) kcB γ := by
  obtain ⟨γ, hγm, hγi, hγ1⟩ := exists_gamma β hβ (UT n)
  refine ⟨γ, ?_⟩
  have hstab : muStab β (toM (ptBlock n t c)) = Measure.map (kapB (n := n)) (muPi β (UT n)) := by
    rw [← gTC_eq]; exact hS n β t c hβ ht hc
  have hmp : MeasurePreserving (PsiB n) ((muPi β (UT n)).prod (muBlock β n)) ((muLow (n + 1) β).prod (muUp (n + 1) β)) :=
    (mp_iLU (n + 1) β).comp (Formalism.FourierDecayAlt.P.quotient_measure n β)
  refine WeilData.mk hν hconc (kapB_emb n) hstab hmp (continuous_kcB n).measurable ?_ ?_ hγm hγi hγ1
  · intro k q
    rw [PsiB_eq n t c ht hc, (kcB_act n t c ht hc _ (secB_mem q) k).1]
    have : TL (secB q).1 = 1 := by
      ext i j
      show lowRow q.1 i.castSucc j.castSucc = _
      unfold lowRow
      rw [G5.blk_cc]
    rw [this, Matrix.mul_one, G5.wMat_mul_self, inv_one, Matrix.mul_one, G5.coordU_upper]
  · intro p hp
    have hB := (kcB_act n t c ht hc p hp 0).2
    have he : (fun k => kcB (actG (toM (ptBlock n t c)) p (kapB k))) =
        fun k => coordU (upper k * upper (coordU (wMat n * TL p.1 * wMat n)⁻¹)) := by
      funext k
      rw [(kcB_act n t c ht hc p hp k).1, G4.upper_coordU (G4.upperUni_inv hB)]
    rw [he]
    exact mp_rmulU β n _

/- English proof (translation)
Rewrite using `[← (mp_iLU s β).map_eq, Measure.map_apply (mp_iLU s β).measurable (isClosed_LUs s).measurableSet.compl]`. Establish `: (Prod.map (iL (s` using `s)) (iU (s := s))) ⁻¹' (LUs s)ᶜ = ∅ := by`. Use extensionality with `z`. Simplify using `only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false, not_not]`. Use `⟨?_, G4.upperUni_upper z.2⟩` and prove the remaining obligations.

Use `show IsUpperUni ((upper z.1)ᵀ)ᵀ`. Rewrite using `[Matrix.transpose_transpose]`. Conclude with `G4.upperUni_upper z.1`. Rewrite using `[this, measure_empty]`.
-/
theorem M_conc (s : ℕ) (β : ℂ) : ((muLow s β).prod (muUp s β)) (LUs s)ᶜ = 0 := by
  rw [← (mp_iLU s β).map_eq, Measure.map_apply (mp_iLU s β).measurable (isClosed_LUs s).measurableSet.compl]
  have : (Prod.map (iL (s := s)) (iU (s := s))) ⁻¹' (LUs s)ᶜ = ∅ := by
    ext z
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false, not_not]
    refine ⟨?_, G4.upperUni_upper z.2⟩
    show IsUpperUni ((upper z.1)ᵀ)ᵀ
    rw [Matrix.transpose_transpose]
    exact G4.upperUni_upper z.1
  rw [this, measure_empty]

/- English proof (translation)
Introduce `h`. Use `congrArg Matrix.det (ptBlock_inv_mul n t c ht hc)` as an intermediate fact. Rewrite `this` using `[Matrix.det_mul, h]`. Simplify using `at this`.
-/
theorem ptBlock_det_ne (n : ℕ) (t c : ℂ) (ht : t ≠ 0) (hc : c ≠ 0) : (ptBlock n t c).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (ptBlock_inv_mul n t c ht hc)
  rw [Matrix.det_mul, h] at this
  simp at this

/- English proof (translation)
Rewrite `hν`, the goal using `[gTC_eq]`. Take `⟨γ, W⟩` from `weilBlock hS n β t c hβ ht hc ν hν hconc`. Establish `hinv : ∀ p ∈ LUs (n + 1), ∀ k, hfun β (toM (ptBlock n t c)) Φ (actG (toM (ptBlock n t c)) p (kapB k)) = hfun β (toM (ptBlock n t c)) Φ p`. Introduce `p hp k`. Use `hfun_inv β _ (ptBlock_inv_mul n t c ht hc) Φ p hp _ ((G4.upperUni_blk_iff _ _ _ _).2 ⟨G4.upperUni_upper k, rfl, rfl⟩) ?_ ?_` and prove the remaining obligations.

Rewrite using `[conjB n t c ht hc]`. Conclude with `(G4.lowerUni_blk_iff _ _ _ _).2 ⟨G4.lowerUni_conj (G4.upperUni_inv (G4.upperUni_upper k)), rfl, rfl⟩`. Rewrite using `[conjB n t c ht hc]`. Conclude with `G4.char_blk (G4.upperUni_upper k)`. Establish `hd` using `ptBlock_det_ne n t c ht hc`.

Use `W.vector (hfun β (toM (ptBlock n t c)) Φ) (blockIntegrand β n Φ t c) hinv ?_ (hfun_aesm β _ hd Φ hΦ _ (M_conc (n + 1) β)) (hfun_aesm β _ hd Φ hΦ _ hconc) hi` as an intermediate fact. Conclude with `this`. Introduce `k q`. Rewrite using `[PsiB_eq n t c ht hc, hinv _ (secB_mem q)]`. Unfold `hfun blockIntegrand secB`.

Simplify using `only []`. Rewrite using `[psiLow_eq, psiUp_eq]`. Both sides reduce to the same expression.
-/
theorem OmG_block (hS : StabMeasBlock) (n : ℕ) (β t c : ℂ) (hβ : β ≠ 0) (ht : t ≠ 0) (hc : c ≠ 0)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (Φ : Msq (n + 1) → E)
    (hΦ : ContinuousOn Φ {Z | mdet Z ≠ 0}) (hi : Integrable (blockIntegrand β n Φ t c) (muBlock β n))
    (ν : Measure (Msq (n + 1) × Msq (n + 1))) (hν : IsOrbMeas β (gTC (n + 1) t c) ν) (hconc : ν (LUs (n + 1))ᶜ = 0) :
    OmG β ν Φ (gTC (n + 1) t c) = OmBlock β n Φ t c := by
  rw [gTC_eq] at hν ⊢
  obtain ⟨γ, W⟩ := weilBlock hS n β t c hβ ht hc ν hν hconc
  have hinv : ∀ p ∈ LUs (n + 1), ∀ k, hfun β (toM (ptBlock n t c)) Φ (actG (toM (ptBlock n t c)) p (kapB k)) =
      hfun β (toM (ptBlock n t c)) Φ p := by
    intro p hp k
    refine hfun_inv β _ (ptBlock_inv_mul n t c ht hc) Φ p hp _
      ((G4.upperUni_blk_iff _ _ _ _).2 ⟨G4.upperUni_upper k, rfl, rfl⟩) ?_ ?_
    · rw [conjB n t c ht hc]
      exact (G4.lowerUni_blk_iff _ _ _ _).2 ⟨G4.lowerUni_conj (G4.upperUni_inv (G4.upperUni_upper k)), rfl, rfl⟩
    · rw [conjB n t c ht hc]
      exact G4.char_blk (G4.upperUni_upper k)
  have hd := ptBlock_det_ne n t c ht hc
  have := W.vector (hfun β (toM (ptBlock n t c)) Φ) (blockIntegrand β n Φ t c) hinv ?_
    (hfun_aesm β _ hd Φ hΦ _ (M_conc (n + 1) β)) (hfun_aesm β _ hd Φ hΦ _ hconc) hi
  · exact this
  · intro k q
    rw [PsiB_eq n t c ht hc, hinv _ (secB_mem q)]
    unfold hfun blockIntegrand secB
    simp only []
    rw [psiLow_eq, psiUp_eq]
    rfl

end Formalism.MainNotions.InterlacingSignCuts.Gm

end

end PartAGo3

section PartAGo4

open MeasureTheory Matrix
open scoped ContDiff

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts.Gm

open Formalism.MainNotions.S.UnitaryLevelOperators Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P

/- English proof (translation)
Use function extensionality and compare the values at `i j`. Establish `hi : i.val < s` using `i.2`. Establish `hj : j.val < s` using `j.2`. Simplify using `only [gZW, toM, ptLong, Formalism.MainNotions.S.ptEntry, hi, hj, and_self, if_true, Matrix.smul_apply, wMat, Matrix.of_apply, smul_eq_mul]`. Distinguish the cases in `h : j = i.rev`.

Establish `: i.val + j.val + 1 = s` using `by rw [h, Fin.val_rev]; omega`. Rewrite using `[if_pos this, if_pos h, mul_one]`. Establish `: ¬ i.val + j.val + 1 = s`. Introduce `e`. Apply `h` to reduce the goal to its premises.

Apply `Fin.ext` to reduce the goal to its premises. Rewrite using `[Fin.val_rev]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg this, if_neg h, mul_zero]`.
-/
theorem gZW_eq (s : ℕ) (z : ℂ) : gZW s z = toM (ptLong s z) := by
  funext i j
  have hi : i.val < s := i.2
  have hj : j.val < s := j.2
  simp only [gZW, toM, ptLong, Formalism.MainNotions.S.ptEntry, hi, hj, and_self, if_true, Matrix.smul_apply, wMat, Matrix.of_apply,
    smul_eq_mul]
  by_cases h : j = i.rev
  · have : i.val + j.val + 1 = s := by rw [h, Fin.val_rev]; omega
    rw [if_pos this, if_pos h, mul_one]
  · have : ¬ i.val + j.val + 1 = s := by
      intro e
      apply h
      apply Fin.ext
      rw [Fin.val_rev]; omega
    rw [if_neg this, if_neg h, mul_zero]

def qL (d : ℕ) (x : (UT d → ℂ) × (UT d → ℂ)) : (UT d → ℂ) × (UT d → ℂ) :=
  (coordU (wMat d * (upper x.1)⁻¹ * wMat d)ᵀ, coordU (upper x.1 * upper x.2))

def PsiL (d : ℕ) : (UT d → ℂ) × (UT d → ℂ) → Msq d × Msq d := Prod.map iL iU ∘ qL d

def kcL {d : ℕ} (p : Msq d × Msq d) : UT d → ℂ := coordU (wMat d * Matrix.of p.1 * wMat d).adjugate

def secL {d : ℕ} (q : UT d → ℂ) : Msq d × Msq d := (toM 1, toM (upper q))

/- English proof (translation)
Establish `hι : MeasurePreserving (fun k : UT d → ℂ => coordU (wMat d * (upper k)⁻¹ * wMat d)ᵀ) (muPi β (UT d)) (muPi β (UT d))`. Simplify using `only [G5.coordU_conj]`. Conclude with `(G5.mp_comp_equiv β (G5.revEquiv d)).comp (G5.mp_invU β d)`. Establish `hm : Measurable (Function.uncurry fun (k : UT d → ℂ) (q : UT d → ℂ) => coordU (upper k * upper q))`. Use `Continuous.measurable ?_` and prove the remaining obligations.

Conclude with `(G5.continuous_coordU d).comp (((G5.continuous_upper d).comp continuous_fst).matrix_mul ((G5.continuous_upper d).comp continuous_snd))`. Conclude with `hι.skew_product (μc := muPi β (UT d)) (μd := muPi β (UT d)) hm (Filter.Eventually.of_forall fun k => (G5.mp_lmulU β d k).map_eq)`.
-/
theorem mp_qL (d : ℕ) (β : ℂ) :
    MeasurePreserving (qL d) ((muPi β (UT d)).prod (muPi β (UT d))) ((muPi β (UT d)).prod (muPi β (UT d))) := by
  have hι : MeasurePreserving (fun k : UT d → ℂ => coordU (wMat d * (upper k)⁻¹ * wMat d)ᵀ)
      (muPi β (UT d)) (muPi β (UT d)) := by
    simp only [G5.coordU_conj]
    exact (G5.mp_comp_equiv β (G5.revEquiv d)).comp (G5.mp_invU β d)
  have hm : Measurable (Function.uncurry fun (k : UT d → ℂ) (q : UT d → ℂ) => coordU (upper k * upper q)) := by
    refine Continuous.measurable ?_
    exact (G5.continuous_coordU d).comp
      (((G5.continuous_upper d).comp continuous_fst).matrix_mul ((G5.continuous_upper d).comp continuous_snd))
  exact hι.skew_product (μc := muPi β (UT d)) (μd := muPi β (UT d)) hm
    (Filter.Eventually.of_forall fun k => (G5.mp_lmulU β d k).map_eq)

/- English proof (translation)
Establish `hc : Continuous (iU (s` using `d)) := continuous_iU d`. Establish `: T2Space (Msq d)` using `inferInstanceAs (T2Space (Fin d → Fin d → ℂ))`. Use `hc.measurableEmbedding ?_` and prove the remaining obligations. Introduce `k k' h`. Establish `h2 : upper k = upper k'` using `h`.

Rewrite using `[← G5.coordU_upper k, h2, G5.coordU_upper]`.
-/
theorem iU_emb (d : ℕ) : MeasurableEmbedding (iU (s := d)) := by
  have hc : Continuous (iU (s := d)) := continuous_iU d
  have : T2Space (Msq d) := inferInstanceAs (T2Space (Fin d → Fin d → ℂ))
  refine hc.measurableEmbedding ?_
  intro k k' h
  have h2 : upper k = upper k' := h
  rw [← G5.coordU_upper k, h2, G5.coordU_upper]

/- English proof (translation)
Use `Matrix.inv_eq_right_inv ?_` and prove the remaining obligations. Unfold `ptLong`. Rewrite using `[Matrix.smul_mul, Matrix.mul_smul, G5.wMat_mul_self, smul_smul, mul_inv_cancel₀ hz, one_smul]`.
-/
theorem ptLong_inv (d : ℕ) (z : ℂ) (hz : z ≠ 0) : (ptLong d z)⁻¹ = z⁻¹ • wMat d := by
  refine Matrix.inv_eq_right_inv ?_
  unfold ptLong
  rw [Matrix.smul_mul, Matrix.mul_smul, G5.wMat_mul_self, smul_smul, mul_inv_cancel₀ hz, one_smul]

/- English proof (translation)
Rewrite using `[ptLong_inv d z hz]`. Unfold `ptLong`. Rewrite using `[Matrix.smul_mul, Matrix.mul_smul, G5.wMat_mul_self, smul_smul, inv_mul_cancel₀ hz, one_smul]`.
-/
theorem ptLong_inv_mul (d : ℕ) (z : ℂ) (hz : z ≠ 0) : (ptLong d z)⁻¹ * ptLong d z = 1 := by
  rw [ptLong_inv d z hz]
  unfold ptLong
  rw [Matrix.smul_mul, Matrix.mul_smul, G5.wMat_mul_self, smul_smul, inv_mul_cancel₀ hz, one_smul]

/- English proof (translation)
Rewrite using `[ptLong_inv d z hz]`. Unfold `ptLong`. Rewrite using `[Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hz, one_smul]`.
-/
theorem conjL (d : ℕ) (z : ℂ) (hz : z ≠ 0) (A : Matrix (Fin d) (Fin d) ℂ) :
    ptLong d z * A * (ptLong d z)⁻¹ = wMat d * A * wMat d := by
  rw [ptLong_inv d z hz]
  unfold ptLong
  rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hz, one_smul]

/- English proof (translation)
Rewrite using `[← conjL d z hz, Matrix.mul_assoc (ptLong d z)]`. Both sides reduce to the same expression.
-/
theorem actL_eq (d : ℕ) (z : ℂ) (hz : z ≠ 0) (p : Msq d × Msq d) (k : UT d → ℂ) :
    actG (toM (ptLong d z)) p (iU k) =
      (toM (Matrix.of p.1 * (wMat d * (upper k)⁻¹ * wMat d)), toM (upper k * Matrix.of p.2)) := by
  rw [← conjL d z hz, Matrix.mul_assoc (ptLong d z)]
  rfl

/- English proof (translation)
Use `⟨?_, G4.upperUni_upper q⟩` and prove the remaining obligations. Use `show IsUpperUni (1 : Matrix (Fin d) (Fin d) ℂ)ᵀ`. Rewrite using `[Matrix.transpose_one]`. Conclude with `G4.upperUni_one`.
-/
theorem secL_mem {d : ℕ} (q : UT d → ℂ) : secL q ∈ LUs d := by
  refine ⟨?_, G4.upperUni_upper q⟩
  show IsUpperUni (1 : Matrix (Fin d) (Fin d) ℂ)ᵀ
  rw [Matrix.transpose_one]
  exact G4.upperUni_one

/- English proof (translation)
Rewrite using `[actL_eq d z hz]`. Establish `h1 : IsLowerUni (wMat d * (upper k)⁻¹ * wMat d)` using `G4.lowerUni_conj (G4.upperUni_inv (G4.upperUni_upper k))`. Establish `h2 : IsUpperUni (upper k * upper q)` using `G4.upperUni_mul (G4.upperUni_upper _) (G4.upperUni_upper _)`. Use `show (iL (coordU (wMat d * (upper k)⁻¹ * wMat d)ᵀ), iU (coordU (upper k * upper q))) = _`. Rewrite using `[iL_coordU h1, iU_coordU h2]`.

Use `show _ = (toM (1 * (wMat d * (upper k)⁻¹ * wMat d)), toM (upper k * upper q))`. Rewrite using `[Matrix.one_mul]`.
-/
theorem PsiL_eq (d : ℕ) (z : ℂ) (hz : z ≠ 0) (k q : UT d → ℂ) :
    PsiL d (k, q) = actG (toM (ptLong d z)) (secL q) (iU k) := by
  rw [actL_eq d z hz]
  have h1 : IsLowerUni (wMat d * (upper k)⁻¹ * wMat d) := G4.lowerUni_conj (G4.upperUni_inv (G4.upperUni_upper k))
  have h2 : IsUpperUni (upper k * upper q) := G4.upperUni_mul (G4.upperUni_upper _) (G4.upperUni_upper _)
  show (iL (coordU (wMat d * (upper k)⁻¹ * wMat d)ᵀ), iU (coordU (upper k * upper q))) = _
  rw [iL_coordU h1, iU_coordU h2]
  show _ = (toM (1 * (wMat d * (upper k)⁻¹ * wMat d)), toM (upper k * upper q))
  rw [Matrix.one_mul]

/- English proof (translation)
Rewrite using `[actL_eq d z hz]`. Establish `hB` using `G4.upperUni_conj hp.1`. Use `⟨?_, hB⟩` and prove the remaining obligations. Unfold `kcL`. Simplify using `only [of_toM]`.

Establish `h3 : wMat d * (Matrix.of p.1 * (wMat d * (upper k)⁻¹ * wMat d)) * wMat d = (wMat d * Matrix.of p.1 * wMat d) * (upper k)⁻¹`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h3, adj_core hB (G4.upperUni_upper k)]`.
-/
theorem kcL_act (d : ℕ) (z : ℂ) (hz : z ≠ 0) (p : Msq d × Msq d) (hp : p ∈ LUs d) (k : UT d → ℂ) :
    kcL (actG (toM (ptLong d z)) p (iU k)) = coordU (upper k * (wMat d * Matrix.of p.1 * wMat d)⁻¹) ∧
      IsUpperUni (wMat d * Matrix.of p.1 * wMat d) := by
  rw [actL_eq d z hz]
  have hB := G4.upperUni_conj hp.1
  refine ⟨?_, hB⟩
  unfold kcL
  simp only [of_toM]
  have h3 : wMat d * (Matrix.of p.1 * (wMat d * (upper k)⁻¹ * wMat d)) * wMat d =
      (wMat d * Matrix.of p.1 * wMat d) * (upper k)⁻¹ := by
    calc wMat d * (Matrix.of p.1 * (wMat d * (upper k)⁻¹ * wMat d)) * wMat d
        = wMat d * Matrix.of p.1 * wMat d * (upper k)⁻¹ * (wMat d * wMat d) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [G5.wMat_mul_self, Matrix.mul_one]
  rw [h3, adj_core hB (G4.upperUni_upper k)]

/- English proof (translation)
Unfold `kcL`. Use `(G5.continuous_coordU d).comp (Continuous.matrix_adjugate ?_)` and prove the remaining obligations. Use `(continuous_const.matrix_mul ?_).matrix_mul continuous_const` and prove the remaining obligations. Conclude with `continuous_fst`.
-/
theorem continuous_kcL (d : ℕ) : Continuous (kcL (d := d)) := by
  unfold kcL
  refine (G5.continuous_coordU d).comp (Continuous.matrix_adjugate ?_)
  refine (continuous_const.matrix_mul ?_).matrix_mul continuous_const
  exact continuous_fst

def StabMeasLong : Prop :=
  ∀ (d : ℕ) (β z : ℂ), β ≠ 0 → z ≠ 0 → muStab β (gZW d z) = Measure.map (iU (s := d)) (muPi β (UT d))

/- English proof (translation)
Take `⟨γ, hγm, hγi, hγ1⟩` from `exists_gamma β hβ (UT d)`. Use `⟨γ, ?_⟩` and prove the remaining obligations. Establish `hstab : muStab β (toM (ptLong d z)) = Measure.map (iU (s` using `d)) (muPi β (UT d)) := by`. Rewrite using `[← gZW_eq]`. Conclude with `hS d β z hβ hz`.

Establish `hmp : MeasurePreserving (PsiL d) ((muPi β (UT d)).prod (muPi β (UT d))) ((muLow d β).prod (muUp d β))` using `(mp_iLU d β).comp (mp_qL d β)`. Use `WeilData.mk hν hconc (iU_emb d) hstab hmp (continuous_kcL d).measurable ?_ ?_ hγm hγi hγ1` and prove the remaining obligations. Introduce `k q`. Rewrite using `[PsiL_eq d z hz, (kcL_act d z hz _ (secL_mem q) k).1]`. Establish `: Matrix.of (secL q).1 = (1 : Matrix (Fin d) (Fin d) ℂ)` using `rfl`.

Rewrite using `[this, Matrix.mul_one, G5.wMat_mul_self, inv_one, Matrix.mul_one, G5.coordU_upper]`. Introduce `p hp`. Establish `hB` using `(kcL_act d z hz p hp 0).2`. Establish `he : (fun k => kcL (actG (toM (ptLong d z)) p (iU k))) = fun k => coordU (upper k * upper (coordU (wMat d * Matrix.of p.1 * wMat d)⁻¹))`. Use function extensionality and compare the values at `k`.

Rewrite using `[(kcL_act d z hz p hp k).1, G4.upper_coordU (G4.upperUni_inv hB)]`. Rewrite using `[he]`. Conclude with `mp_rmulU β d _`.
-/
theorem weilLong (hS : StabMeasLong) (d : ℕ) (β z : ℂ) (hβ : β ≠ 0) (hz : z ≠ 0)
    (ν : Measure (Msq d × Msq d)) (hν : IsOrbMeas β (toM (ptLong d z)) ν) (hconc : ν (LUs d)ᶜ = 0) :
    ∃ γ, WeilData ((muLow d β).prod (muUp d β)) ν (muStab β (toM (ptLong d z)))
      (actG (toM (ptLong d z))) (LUs d) (muPi β (UT d)) (muPi β (UT d)) iU (PsiL d) kcL γ := by
  obtain ⟨γ, hγm, hγi, hγ1⟩ := exists_gamma β hβ (UT d)
  refine ⟨γ, ?_⟩
  have hstab : muStab β (toM (ptLong d z)) = Measure.map (iU (s := d)) (muPi β (UT d)) := by
    rw [← gZW_eq]; exact hS d β z hβ hz
  have hmp : MeasurePreserving (PsiL d) ((muPi β (UT d)).prod (muPi β (UT d))) ((muLow d β).prod (muUp d β)) :=
    (mp_iLU d β).comp (mp_qL d β)
  refine WeilData.mk hν hconc (iU_emb d) hstab hmp (continuous_kcL d).measurable ?_ ?_ hγm hγi hγ1
  · intro k q
    rw [PsiL_eq d z hz, (kcL_act d z hz _ (secL_mem q) k).1]
    have : Matrix.of (secL q).1 = (1 : Matrix (Fin d) (Fin d) ℂ) := rfl
    rw [this, Matrix.mul_one, G5.wMat_mul_self, inv_one, Matrix.mul_one, G5.coordU_upper]
  · intro p hp
    have hB := (kcL_act d z hz p hp 0).2
    have he : (fun k => kcL (actG (toM (ptLong d z)) p (iU k))) =
        fun k => coordU (upper k * upper (coordU (wMat d * Matrix.of p.1 * wMat d)⁻¹)) := by
      funext k
      rw [(kcL_act d z hz p hp k).1, G4.upper_coordU (G4.upperUni_inv hB)]
    rw [he]
    exact mp_rmulU β d _

/- English proof (translation)
Introduce `h`. Use `congrArg Matrix.det (ptLong_inv_mul d z hz)` as an intermediate fact. Rewrite `this` using `[Matrix.det_mul, h]`. Simplify using `at this`.
-/
theorem ptLong_det_ne (d : ℕ) (z : ℂ) (hz : z ≠ 0) : (ptLong d z).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (ptLong_inv_mul d z hz)
  rw [Matrix.det_mul, h] at this
  simp at this

/- English proof (translation)
Unfold `subSum`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `i _`. Conclude with `Matrix.one_apply_ne (by rw [Ne, Fin.ext_iff, Fin.val_succ, Fin.coe_castSucc]; omega)`.
-/
theorem subSum_one {n : ℕ} : subSum (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) = 0 := by
  unfold subSum
  apply Finset.sum_eq_zero
  intro i _
  exact Matrix.one_apply_ne (by rw [Ne, Fin.ext_iff, Fin.val_succ, Fin.coe_castSucc]; omega)

/- English proof (translation)
Rewrite `hν`, the goal using `[gZW_eq]`. Take `⟨γ, W⟩` from `weilLong hS (n + 1) β z hβ hz ν hν hconc`. Establish `hinv : ∀ p ∈ LUs (n + 1), ∀ k, hfun β (toM (ptLong (n + 1) z)) Φ (actG (toM (ptLong (n + 1) z)) p (iU k)) = hfun β (toM (ptLong (n + 1) z)) Φ p`. Introduce `p hp k`. Use `hfun_inv β _ (ptLong_inv_mul (n + 1) z hz) Φ p hp _ (G4.upperUni_upper k) ?_ ?_` and prove the remaining obligations.

Rewrite using `[conjL (n + 1) z hz]`. Conclude with `G4.lowerUni_conj (G4.upperUni_inv (G4.upperUni_upper k))`. Rewrite using `[conjL (n + 1) z hz, G4.subSum_conj]`. Conclude with `G4.superSum_inv (G4.upperUni_upper k)`. Establish `hd` using `ptLong_det_ne (n + 1) z hz`.

Use `W.vector (hfun β (toM (ptLong (n + 1) z)) Φ) (fun v : UT (n + 1) → ℂ => psi β (superSum (upper v)) • Φ (ptLong (n + 1) z * upper v)) hinv ?_ (hfun_aesm β _ hd Φ hΦ _ (M_conc (n + 1) β)) (hfun_aesm β _ hd Φ hΦ _ hconc) hi` as an intermediate fact. Conclude with `this`. Introduce `k q`. Rewrite using `[PsiL_eq (n + 1) z hz, hinv _ (secL_mem q)]`. Unfold `hfun secL`.

Simplify using `only []`. Rewrite using `[psiLow_eq, psiUp_eq, of_toM, of_toM, subSum_one, psi_zero, one_mul]`. Use `show _ • Φ (toM (1 * ptLong (n + 1) z * upper q)) = _`. Rewrite using `[Matrix.one_mul]`. Both sides reduce to the same expression.
-/
theorem OmG_long (hS : StabMeasLong) (n : ℕ) (β z : ℂ) (hβ : β ≠ 0) (hz : z ≠ 0)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (Φ : Msq (n + 1) → E)
    (hΦ : ContinuousOn Φ {Z | mdet Z ≠ 0})
    (hi : Integrable (fun v : UT (n + 1) → ℂ => psi β (superSum (upper v)) • Φ (ptLong (n + 1) z * upper v))
      (muPi β (UT (n + 1))))
    (ν : Measure (Msq (n + 1) × Msq (n + 1))) (hν : IsOrbMeas β (gZW (n + 1) z) ν) (hconc : ν (LUs (n + 1))ᶜ = 0) :
    OmG β ν Φ (gZW (n + 1) z) = OmLong β n Φ z := by
  rw [gZW_eq] at hν ⊢
  obtain ⟨γ, W⟩ := weilLong hS (n + 1) β z hβ hz ν hν hconc
  have hinv : ∀ p ∈ LUs (n + 1), ∀ k, hfun β (toM (ptLong (n + 1) z)) Φ (actG (toM (ptLong (n + 1) z)) p (iU k)) =
      hfun β (toM (ptLong (n + 1) z)) Φ p := by
    intro p hp k
    refine hfun_inv β _ (ptLong_inv_mul (n + 1) z hz) Φ p hp _ (G4.upperUni_upper k) ?_ ?_
    · rw [conjL (n + 1) z hz]
      exact G4.lowerUni_conj (G4.upperUni_inv (G4.upperUni_upper k))
    · rw [conjL (n + 1) z hz, G4.subSum_conj]
      exact G4.superSum_inv (G4.upperUni_upper k)
  have hd := ptLong_det_ne (n + 1) z hz
  have := W.vector (hfun β (toM (ptLong (n + 1) z)) Φ)
    (fun v : UT (n + 1) → ℂ => psi β (superSum (upper v)) • Φ (ptLong (n + 1) z * upper v)) hinv ?_
    (hfun_aesm β _ hd Φ hΦ _ (M_conc (n + 1) β)) (hfun_aesm β _ hd Φ hΦ _ hconc) hi
  · exact this
  · intro k q
    rw [PsiL_eq (n + 1) z hz, hinv _ (secL_mem q)]
    unfold hfun secL
    simp only []
    rw [psiLow_eq, psiUp_eq, of_toM, of_toM, subSum_one, psi_zero, one_mul]
    show _ • Φ (toM (1 * ptLong (n + 1) z * upper q)) = _
    rw [Matrix.one_mul]
    rfl

end Formalism.MainNotions.InterlacingSignCuts.Gm

end

end PartAGo4

section PartAGo

open MeasureTheory Matrix
open scoped ContDiff

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts.Gm

open Formalism.MainNotions.S.UnitaryLevelOperators Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P

/- English proof (translation)
Use extensionality with `p`. Simplify using `only [LUs, Set.mem_compl_iff, Set.mem_setOf_eq, not_iff_not]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩`. Conclude with `⟨fun i j => ⟨fun h => h2 j i h, fun h => h ▸ h1 i⟩, fun i j => ⟨fun h => h4 i j h, fun h => h ▸ h3 i⟩⟩`.

Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨⟨fun i => (h1 i i).2 rfl, fun i j h => (h1 j i).1 h⟩, ⟨fun i => (h2 i i).2 rfl, fun i j h => (h2 i j).1 h⟩⟩`.
-/
theorem LUs_compl (s : ℕ) :
    (LUs s)ᶜ = {p | ¬ (Formalism.MainNotions.S.IsLoUni (Matrix.of p.1) ∧ Formalism.MainNotions.S.IsUpUni (Matrix.of p.2))} := by
  ext p
  simp only [LUs, Set.mem_compl_iff, Set.mem_setOf_eq, not_iff_not]
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    exact ⟨fun i j => ⟨fun h => h2 j i h, fun h => h ▸ h1 i⟩, fun i j => ⟨fun h => h4 i j h, fun h => h ▸ h3 i⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨fun i => (h1 i i).2 rfl, fun i j h => (h1 j i).1 h⟩, ⟨fun i => (h2 i i).2 rfl, fun i j h => (h2 i j).1 h⟩⟩

def OrbCoordC (C₁ C₂ : ℝ) : Prop :=
  ∀ (m : ℕ) (β : ℂ), β ≠ 0 → ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (Φ : Msq (m + 1 + 1) → E) (A : ℝ), C₂ * ((m + 1 + 1 : ℕ) : ℝ) ^ 3 ≤ A → GermHyp C₁ (m + 1 + 1) Φ A →
    ∀ (ν : Msq (m + 1 + 1) → Measure (Msq (m + 1 + 1) × Msq (m + 1 + 1))),
      (∀ g, mdet g ≠ 0 → IsOrbMeasLU β g (ν g)) →
      (∀ t c : ℂ, t ≠ 0 → c ≠ 0 →
        OmG β (ν (gTC (m + 1 + 1) t c)) Φ (gTC (m + 1 + 1) t c) = OmBlock β (m + 1) Φ t c) ∧
      (∀ z : ℂ, z ≠ 0 → OmG β (ν (gZW (m + 1 + 1) z)) Φ (gZW (m + 1 + 1) z) = OmLong β (m + 1) Φ z)

/- English proof (translation)
Take `⟨C, hC⟩` from `hG`. Use `⟨(C : ℝ), fun C₁ h1 C₂ h2 hO s cψ hs hc => ?_⟩` and prove the remaining obligations. Take `⟨m, rfl⟩ : ∃ m, s = m + 1 + 1` from `⟨s - 2, by omega⟩`. Take `⟨ph, hph, H⟩` from `hC m cψ hc`. Use `⟨ph, hph, ?_⟩` and prove the remaining obligations.

Introduce `E _ _ _ Φ A hA hsm hbd ν hν K hK h0 ε hε`. Establish `hcast : ((m + 1 + 1 : ℕ) : ℝ) = (m : ℝ) + 2` using `by push_cast; ring`. Establish `hCnn : (0 : ℝ) ≤ C` using `Nat.cast_nonneg C`. Establish `hs0 : (0 : ℝ) ≤ (m : ℝ) + 2` using `by positivity`. Establish `hA' : (C : ℝ) * ((m : ℝ) + 2) ^ 3 ≤ A`.

Rewrite `hA` using `[hcast]`. Conclude with `le_trans (mul_le_mul_of_nonneg_right h2 (by positivity)) hA`. Establish `hA0 : 0 ≤ A` using `le_trans (by positivity) hA'`. Establish `hKd : IsCompact (detSet (m + 1) K)` using `hK.image (continuous_const.mul continuous_id)`. Establish `h0d : (0 : ℂ) ∉ detSet (m + 1) K`.

Introduce and unpack `⟨D, hD, hD0⟩`. Break down `mul_eq_zero.1 hD0 with h | h` into its components or cases. Conclude with `wMat_det_ne _ h`. Conclude with `h0 (h ▸ hD)`. Take `⟨CK, hCK⟩` from `hbd _ hKd h0d`.

Take `⟨δ, hδ, Hδ⟩` from `H A hA' K hK h0 |CK| ε hε`. Establish `hDB : DerivBound (C * (m + 2) ^ 2) (detSet (m + 1) K) (fun Z => |CK| * ‖Z‖ ^ (-A)) Φ`. Introduce `Z hZ`. Establish `hZ0 : mdet Z ≠ 0` using `fun h => h0d (h ▸ hZ)`. Use `⟨?_, fun j hj => ?_⟩` and prove the remaining obligations.

Establish `hopen : IsOpen {Z : Msq (m + 1 + 1) | mdet Z ≠ 0}` using `isOpen_ne_fun (continuous_mdet _) continuous_const`. Conclude with `contDiffAt_infty.1 (hsm.contDiffAt (hopen.mem_nhds hZ0)) _`. Establish `hj' : (j : ℝ) ≤ C₁ * ((m + 1 + 1 : ℕ) : ℝ) ^ 2`. Rewrite using `[hcast]`. Establish `: (j : ℝ) ≤ (C : ℝ) * ((m : ℝ) + 2) ^ 2` using `by exact_mod_cast hj`.

Conclude with `le_trans this (mul_le_mul_of_nonneg_right h1 (by positivity))`. Use `le_trans (hCK j hj' Z hZ) ?_` and prove the remaining obligations. Establish `hZne : Z ≠ 0`. Introduce and unpack `rfl`. Apply `hZ0` to reduce the goal to its premises.

Unfold `mdet`. Establish `: (Matrix.of (0 : Msq (m + 1 + 1))) = (0 : Matrix (Fin (m + 1 + 1)) (Fin (m + 1 + 1)) ℂ)` using `rfl`. Rewrite using `[this, Matrix.det_zero]`. Establish `hpos : 0 < ‖Z‖` using `norm_pos_iff.2 hZne`. Establish `hle : fNorm Z ^ (-A) ≤ ‖Z‖ ^ (-A)` using `Real.rpow_le_rpow_of_nonpos hpos (norm_le_fNorm Z) (by linarith)`.

Combine the equalities or inequalities in the displayed calculation. Use `⟨δ, hδ, fun t c ht hlt hD => ?_⟩` and prove the remaining obligations. Establish `hrem` using `Hδ E Φ hDB t c ht hlt hD`. Take `⟨hB, hL⟩` from `hO m cψ hc E Φ A hA ⟨hsm, hbd⟩ ν hν`. Establish `hc0 : c ≠ 0`.

Introduce and unpack `rfl`. Apply `h0` to reduce the goal to its premises. Simplify using `using hD`. Establish `hDne : c * t ^ (m + 1) ≠ 0` using `mul_ne_zero hc0 (pow_ne_zero _ ht)`. Rewrite using `[hB t c ht hc0]`.

Establish `hsum : ∀ z ∈ (Polynomial.nthRoots (m + 1 + 1) ((-1) ^ (m + 1 + 1 + 1) * (c * t ^ (m + 1 + 1 - 1)))).toFinset, ((‖z‖ ^ ((m + 1 + 1 - 1) ^ 2) : ℝ) * ph z * psiC cψ (((m + 1 + 1 : ℕ) : ℂ) * z / t)) • OmG cψ (ν (gZW (m + 1 + 1) z)) Φ (gZW (m + 1 + 1) z) = (((‖z‖ ^ ((m + 1) ^ 2) : ℝ) …`. Introduce `z hz`. Establish `hz0 : z ≠ 0`. Introduce and unpack `rfl`. Rewrite `hz` using `[Multiset.mem_toFinset, Polynomial.mem_nthRoots (by omega)]`.

Establish `: (0 : ℂ) ^ (m + 1 + 1) = 0` using `by simp`. Rewrite `hz` using `[this]`. Establish `h1 : ((-1 : ℂ)) ^ (m + 1 + 1 + 1) ≠ 0` using `pow_ne_zero _ (by norm_num)`. Conclude with `(mul_ne_zero h1 (by simpa using hDne)) hz.symm`. Rewrite using `[hL z hz0]`.

Establish `e1 : ((m + 1 + 1 : ℕ) : ℂ) = (m : ℂ) + 2` using `by push_cast; ring`. Rewrite using `[e1]`. Both sides reduce to the same expression. Rewrite using `[Finset.sum_congr rfl hsum]`. Establish `e1 : ((m + 1 + 1 : ℕ) : ℂ) = (m : ℂ) + 2` using `by push_cast; ring`.

Rewrite using `[e1]`. Simplify using `only [remainder, mainTerm, rootSet] at hrem`. Rewrite using `[← Complex.coe_smul]`. Conclude with `hrem`.
-/
theorem stGerm_of_orbCoordC (hG : Germ) :
    ∃ C : ℝ, ∀ C₁ ≥ C, ∀ C₂ ≥ C, OrbCoordC C₁ C₂ → stGerm C₁ C₂ := by
  obtain ⟨C, hC⟩ := hG
  refine ⟨(C : ℝ), fun C₁ h1 C₂ h2 hO s cψ hs hc => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, s = m + 1 + 1 := ⟨s - 2, by omega⟩
  obtain ⟨ph, hph, H⟩ := hC m cψ hc
  refine ⟨ph, hph, ?_⟩
  intro E _ _ _ Φ A hA hsm hbd ν hν K hK h0 ε hε
  have hcast : ((m + 1 + 1 : ℕ) : ℝ) = (m : ℝ) + 2 := by push_cast; ring
  have hCnn : (0 : ℝ) ≤ C := Nat.cast_nonneg C
  have hs0 : (0 : ℝ) ≤ (m : ℝ) + 2 := by positivity
  have hA' : (C : ℝ) * ((m : ℝ) + 2) ^ 3 ≤ A := by
    rw [hcast] at hA
    exact le_trans (mul_le_mul_of_nonneg_right h2 (by positivity)) hA
  have hA0 : 0 ≤ A := le_trans (by positivity) hA'

  have hKd : IsCompact (detSet (m + 1) K) := hK.image (continuous_const.mul continuous_id)
  have h0d : (0 : ℂ) ∉ detSet (m + 1) K := by
    rintro ⟨D, hD, hD0⟩
    rcases mul_eq_zero.1 hD0 with h | h
    · exact wMat_det_ne _ h
    · exact h0 (h ▸ hD)
  obtain ⟨CK, hCK⟩ := hbd _ hKd h0d
  obtain ⟨δ, hδ, Hδ⟩ := H A hA' K hK h0 |CK| ε hε
  have hDB : DerivBound (C * (m + 2) ^ 2) (detSet (m + 1) K) (fun Z => |CK| * ‖Z‖ ^ (-A)) Φ := by
    intro Z hZ
    have hZ0 : mdet Z ≠ 0 := fun h => h0d (h ▸ hZ)
    refine ⟨?_, fun j hj => ?_⟩
    · have hopen : IsOpen {Z : Msq (m + 1 + 1) | mdet Z ≠ 0} :=
        isOpen_ne_fun (continuous_mdet _) continuous_const
      exact contDiffAt_infty.1 (hsm.contDiffAt (hopen.mem_nhds hZ0)) _
    · have hj' : (j : ℝ) ≤ C₁ * ((m + 1 + 1 : ℕ) : ℝ) ^ 2 := by
        rw [hcast]
        have : (j : ℝ) ≤ (C : ℝ) * ((m : ℝ) + 2) ^ 2 := by exact_mod_cast hj
        exact le_trans this (mul_le_mul_of_nonneg_right h1 (by positivity))
      refine le_trans (hCK j hj' Z hZ) ?_
      have hZne : Z ≠ 0 := by
        rintro rfl
        apply hZ0
        unfold mdet
        have : (Matrix.of (0 : Msq (m + 1 + 1))) = (0 : Matrix (Fin (m + 1 + 1)) (Fin (m + 1 + 1)) ℂ) := rfl
        rw [this, Matrix.det_zero]
      have hpos : 0 < ‖Z‖ := norm_pos_iff.2 hZne
      have hle : fNorm Z ^ (-A) ≤ ‖Z‖ ^ (-A) :=
        Real.rpow_le_rpow_of_nonpos hpos (norm_le_fNorm Z) (by linarith)
      calc CK * fNorm Z ^ (-A) ≤ |CK| * fNorm Z ^ (-A) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
        _ ≤ |CK| * ‖Z‖ ^ (-A) := mul_le_mul_of_nonneg_left hle (abs_nonneg _)
  refine ⟨δ, hδ, fun t c ht hlt hD => ?_⟩
  have hrem := Hδ E Φ hDB t c ht hlt hD
  obtain ⟨hB, hL⟩ := hO m cψ hc E Φ A hA ⟨hsm, hbd⟩ ν hν
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply h0
    simpa using hD
  have hDne : c * t ^ (m + 1) ≠ 0 := mul_ne_zero hc0 (pow_ne_zero _ ht)
  rw [hB t c ht hc0]
  have hsum : ∀ z ∈ (Polynomial.nthRoots (m + 1 + 1) ((-1) ^ (m + 1 + 1 + 1) * (c * t ^ (m + 1 + 1 - 1)))).toFinset,
      ((‖z‖ ^ ((m + 1 + 1 - 1) ^ 2) : ℝ) * ph z * psiC cψ (((m + 1 + 1 : ℕ) : ℂ) * z / t)) •
          OmG cψ (ν (gZW (m + 1 + 1) z)) Φ (gZW (m + 1 + 1) z) =
        (((‖z‖ ^ ((m + 1) ^ 2) : ℝ) : ℂ) * ph z * psi cψ (((m : ℂ) + 2) * z / t)) • OmLong cψ (m + 1) Φ z := by
    intro z hz
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots (by omega)] at hz
      have : (0 : ℂ) ^ (m + 1 + 1) = 0 := by simp
      rw [this] at hz
      have h1 : ((-1 : ℂ)) ^ (m + 1 + 1 + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
      exact (mul_ne_zero h1 (by simpa using hDne)) hz.symm
    rw [hL z hz0]
    have e1 : ((m + 1 + 1 : ℕ) : ℂ) = (m : ℂ) + 2 := by push_cast; ring
    rw [e1]
    rfl
  rw [Finset.sum_congr rfl hsum]
  have e1 : ((m + 1 + 1 : ℕ) : ℂ) = (m : ℂ) + 2 := by push_cast; ring
  rw [e1]
  simp only [remainder, mainTerm, rootSet] at hrem
  rw [← Complex.coe_smul]
  exact hrem

def normAbv : AbsoluteValue ℂ ℝ where
  toFun := norm
  map_mul' := norm_mul
  nonneg' := norm_nonneg
  eq_zero' := fun _ => norm_eq_zero
  add_le' := norm_add_le

/- English proof (translation)
Take `⟨hsm, hbd⟩` from `h`. Take `⟨CK, hCK⟩` from `hbd {D} isCompact_singleton (by simpa using hD.symm)`. Use `set ρ : ℝ := ‖D‖ / (s.factorial : ℝ) with hρ`. Establish `hρ0 : 0 < ρ` using `div_pos (norm_pos_iff.2 hD) (by exact_mod_cast Nat.factorial_pos s)`. Use `⟨|CK| * max 1 (ρ ^ (-A / s)), fun Z hZ => ?_⟩` and prove the remaining obligations.

Establish `hZD : mdet Z = D` using `hZ`. Establish `hZ0 : mdet Z ≠ 0` using `by rw [hZD]; exact hD`. Establish `hopen : IsOpen {Z : Msq s | mdet Z ≠ 0}` using `isOpen_ne_fun (continuous_mdet _) continuous_const`. Use `⟨contDiffAt_infty.1 (hsm.contDiffAt (hopen.mem_nhds hZ0)) _, fun j hj => ?_⟩` and prove the remaining obligations. Establish `hj0 : (j : ℝ) ≤ C₁ * (s : ℝ) ^ 2`.

Establish `: j = 0` using `Nat.le_zero.1 hj`. Rewrite using `[this]`. Simplify using `only [Nat.cast_zero]`. Check the signs of the components of the expression. Use `le_trans (hCK j hj0 Z hZ) ?_` and prove the remaining obligations.

Establish `hZne : Z ≠ 0`. Introduce and unpack `rfl`. Apply `hZ0` to reduce the goal to its premises. Unfold `mdet`. Establish `h00 : (Matrix.of (0 : Msq s)) = (0 : Matrix (Fin s) (Fin s) ℂ)` using `rfl`.

Establish `: Nonempty (Fin s)` using `⟨⟨0, hs⟩⟩`. Rewrite using `[h00, Matrix.det_zero]`. Establish `hpos : 0 < ‖Z‖` using `norm_pos_iff.2 hZne`. Establish `hle : fNorm Z ^ (-A) ≤ ‖Z‖ ^ (-A)` using `Real.rpow_le_rpow_of_nonpos hpos (norm_le_fNorm Z) (by linarith)`. Establish `hdet : ρ ≤ ‖Z‖ ^ s`.

Establish `h1` using `Matrix.det_le (A := Matrix.of Z) (abv := normAbv) (x := ‖Z‖) (fun i j => (norm_le_pi_norm (Z i) j).trans (norm_le_pi_norm Z i))`. Establish `h2 : ‖D‖ ≤ (s.factorial : ℝ) * ‖Z‖ ^ s`. Establish `: normAbv (Matrix.of Z).det = ‖D‖` using `by rw [← hZD]; rfl`. Rewrite `h1` using `[this]`. Simplify `h1` using `[nsmul_eq_mul]`.

Rewrite using `[hρ, div_le_iff₀ (by exact_mod_cast Nat.factorial_pos s)]`. Combine the linear relations using `[h2, mul_comm (s.factorial : ℝ) (‖Z‖ ^ s)]`. Establish `hs' : (s : ℝ) ≠ 0` using `by exact_mod_cast hs.ne'`. Establish `hZA : ‖Z‖ ^ (-A) ≤ ρ ^ (-A / s)`. Establish `e : ‖Z‖ ^ (-A) = (‖Z‖ ^ s) ^ (-A / s)`.

Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul hpos.le]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`. Conclude with `Real.rpow_le_rpow_of_nonpos hρ0 hdet (div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity))`.

Establish `hmin : ‖Z‖ ^ (-A) ≤ max 1 (ρ ^ (-A / s)) * min 1 (‖Z‖ ^ (-A))`. Establish `hp : 0 ≤ ‖Z‖ ^ (-A)` using `Real.rpow_nonneg hpos.le _`. Break down `le_total (‖Z‖ ^ (-A)) 1 with h1 | h1` into its components or cases. Rewrite using `[min_eq_right h1]`. Conclude with `le_mul_of_one_le_left hp (le_max_left _ _)`.

Rewrite using `[min_eq_left h1, mul_one]`. Conclude with `hZA.trans (le_max_right _ _)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem derivBound_zero {s : ℕ} (hs : 0 < s) {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (C₁ : ℝ) (hC₁ : 0 ≤ C₁)
    (Φ : Msq s → E) (A : ℝ) (hA : 0 ≤ A) (h : GermHyp C₁ s Φ A) (D : ℂ) (hD : D ≠ 0) :
    ∃ K : ℝ, DerivBound 0 {D} (fun Z => K * min 1 (‖Z‖ ^ (-A))) Φ := by
  obtain ⟨hsm, hbd⟩ := h
  obtain ⟨CK, hCK⟩ := hbd {D} isCompact_singleton (by simpa using hD.symm)
  set ρ : ℝ := ‖D‖ / (s.factorial : ℝ) with hρ
  have hρ0 : 0 < ρ := div_pos (norm_pos_iff.2 hD) (by exact_mod_cast Nat.factorial_pos s)
  refine ⟨|CK| * max 1 (ρ ^ (-A / s)), fun Z hZ => ?_⟩
  have hZD : mdet Z = D := hZ
  have hZ0 : mdet Z ≠ 0 := by rw [hZD]; exact hD
  have hopen : IsOpen {Z : Msq s | mdet Z ≠ 0} := isOpen_ne_fun (continuous_mdet _) continuous_const
  refine ⟨contDiffAt_infty.1 (hsm.contDiffAt (hopen.mem_nhds hZ0)) _, fun j hj => ?_⟩
  have hj0 : (j : ℝ) ≤ C₁ * (s : ℝ) ^ 2 := by
    have : j = 0 := Nat.le_zero.1 hj
    rw [this]
    simp only [Nat.cast_zero]
    positivity
  refine le_trans (hCK j hj0 Z hZ) ?_
  have hZne : Z ≠ 0 := by
    rintro rfl
    apply hZ0
    unfold mdet
    have h00 : (Matrix.of (0 : Msq s)) = (0 : Matrix (Fin s) (Fin s) ℂ) := rfl
    have : Nonempty (Fin s) := ⟨⟨0, hs⟩⟩
    rw [h00, Matrix.det_zero]
  have hpos : 0 < ‖Z‖ := norm_pos_iff.2 hZne
  have hle : fNorm Z ^ (-A) ≤ ‖Z‖ ^ (-A) := Real.rpow_le_rpow_of_nonpos hpos (norm_le_fNorm Z) (by linarith)
  have hdet : ρ ≤ ‖Z‖ ^ s := by
    have h1 := Matrix.det_le (A := Matrix.of Z) (abv := normAbv) (x := ‖Z‖)
      (fun i j => (norm_le_pi_norm (Z i) j).trans (norm_le_pi_norm Z i))
    have h2 : ‖D‖ ≤ (s.factorial : ℝ) * ‖Z‖ ^ s := by
      have : normAbv (Matrix.of Z).det = ‖D‖ := by rw [← hZD]; rfl
      rw [this] at h1
      simpa [nsmul_eq_mul] using h1
    rw [hρ, div_le_iff₀ (by exact_mod_cast Nat.factorial_pos s)]
    linarith [h2, mul_comm (s.factorial : ℝ) (‖Z‖ ^ s)]
  have hs' : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have hZA : ‖Z‖ ^ (-A) ≤ ρ ^ (-A / s) := by
    have e : ‖Z‖ ^ (-A) = (‖Z‖ ^ s) ^ (-A / s) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
      congr 1
      field_simp
    rw [e]
    exact Real.rpow_le_rpow_of_nonpos hρ0 hdet (div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity))
  have hmin : ‖Z‖ ^ (-A) ≤ max 1 (ρ ^ (-A / s)) * min 1 (‖Z‖ ^ (-A)) := by
    have hp : 0 ≤ ‖Z‖ ^ (-A) := Real.rpow_nonneg hpos.le _
    rcases le_total (‖Z‖ ^ (-A)) 1 with h1 | h1
    · rw [min_eq_right h1]
      exact le_mul_of_one_le_left hp (le_max_left _ _)
    · rw [min_eq_left h1, mul_one]
      exact hZA.trans (le_max_right _ _)
  calc CK * fNorm Z ^ (-A) ≤ |CK| * fNorm Z ^ (-A) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
    _ ≤ |CK| * ‖Z‖ ^ (-A) := mul_le_mul_of_nonneg_left hle (abs_nonneg _)
    _ ≤ |CK| * (max 1 (ρ ^ (-A / s)) * min 1 (‖Z‖ ^ (-A))) := mul_le_mul_of_nonneg_left hmin (abs_nonneg _)
    _ = _ := by ring

/- English proof (translation)
Introduce `m β hβ E _ _ _ Φ A hA hG ν hν`. Establish `hcast : ((m + 1 + 1 : ℕ) : ℝ) = (m : ℝ) + 2` using `by push_cast; ring`. Establish `hm0 : (0 : ℝ) ≤ m` using `Nat.cast_nonneg m`. Establish `hA1 : ((m : ℝ) + 1) * ((m : ℝ) + 4) < A`. Rewrite `hA` using `[hcast]`.

Establish `: ((m : ℝ) + 2) ^ 3 ≤ C₂ * ((m : ℝ) + 2) ^ 3` using `le_mul_of_one_le_left (by positivity) h2`. Use polynomial arithmetic with `[this, hA, hm0, mul_nonneg hm0 hm0, mul_nonneg (mul_nonneg hm0 hm0) hm0]`. Establish `hA0 : 0 ≤ A` using `le_trans (by positivity) hA1.le`. Establish `hΦ : ContinuousOn Φ {Z | mdet Z ≠ 0}` using `hG.1.continuousOn`. Establish `key : ∀ t c : ℂ, t ≠ 0 → c ≠ 0 → Integrable (blockIntegrand β (m + 1) Φ t c) (muBlock β (m + 1)) ∧ ∀ z : ℂ, z ^ (m + 2) = (-1) ^ (m + 3) * (c * t ^ (m + 1)) → Integrable (fun v : UT (m + 1 + 1) → ℂ => psi β (superSum (upper v)) • Φ (ptLong (m + 1 + 1) z * upper v)) (muPi β (UT (m …`.

Introduce `t c ht hc`. Establish `hD : (wMat (m + 1)).det * (c * t ^ (m + 1)) ≠ 0` using `mul_ne_zero (wMat_det_ne _) (mul_ne_zero hc (pow_ne_zero _ ht))`. Take `⟨K, hK⟩` from `derivBound_zero (by omega) C₁ h1 Φ A hA0 hG _ hD`. Conclude with `Formalism.FourierDecayAlt.P.orbital_integral_converges_abs m β A K hA1 E Φ t c ht hc hK`. Use `⟨fun t c ht hc => ?_, fun z hz => ?_⟩` and prove the remaining obligations.

Establish `hdet : mdet (gTC (m + 1 + 1) t c) ≠ 0`. Rewrite using `[gTC_eq]`. Conclude with `ptBlock_det_ne (m + 1) t c ht hc`. Take `⟨hw, hcn⟩` from `hν _ hdet`. Rewrite `hcn` using `[← LUs_compl]`.

Conclude with `OmG_block hSB (m + 1) β t c hβ ht hc Φ hΦ (key t c ht hc).1 _ hw hcn`. Establish `hdet : mdet (gZW (m + 1 + 1) z) ≠ 0`. Rewrite using `[gZW_eq]`. Conclude with `ptLong_det_ne (m + 1 + 1) z hz`. Take `⟨hw, hcn⟩` from `hν _ hdet`.

Rewrite `hcn` using `[← LUs_compl]`. Establish `hc : ((-1 : ℂ)) ^ (m + 3) * z ^ (m + 2) ≠ 0` using `mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hz)`. Establish `hi` using `(key 1 ((-1) ^ (m + 3) * z ^ (m + 2)) one_ne_zero hc).2 z (by`. Rewrite using `[one_pow, mul_one, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]`. Use the proof step `simp)`.

Conclude with `OmG_long hSL (m + 1) β z hβ hz Φ hΦ hi _ hw hcn`.
-/
theorem orbCoordC (hSB : StabMeasBlock) (hSL : StabMeasLong) (C₁ C₂ : ℝ) (h1 : 0 ≤ C₁) (h2 : 1 ≤ C₂) : OrbCoordC C₁ C₂ := by
  intro m β hβ E _ _ _ Φ A hA hG ν hν
  have hcast : ((m + 1 + 1 : ℕ) : ℝ) = (m : ℝ) + 2 := by push_cast; ring
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hA1 : ((m : ℝ) + 1) * ((m : ℝ) + 4) < A := by
    rw [hcast] at hA
    have : ((m : ℝ) + 2) ^ 3 ≤ C₂ * ((m : ℝ) + 2) ^ 3 := le_mul_of_one_le_left (by positivity) h2
    nlinarith [this, hA, hm0, mul_nonneg hm0 hm0, mul_nonneg (mul_nonneg hm0 hm0) hm0]
  have hA0 : 0 ≤ A := le_trans (by positivity) hA1.le
  have hΦ : ContinuousOn Φ {Z | mdet Z ≠ 0} := hG.1.continuousOn
  have key : ∀ t c : ℂ, t ≠ 0 → c ≠ 0 →
      Integrable (blockIntegrand β (m + 1) Φ t c) (muBlock β (m + 1)) ∧
      ∀ z : ℂ, z ^ (m + 2) = (-1) ^ (m + 3) * (c * t ^ (m + 1)) →
        Integrable (fun v : UT (m + 1 + 1) → ℂ =>
          psi β (superSum (upper v)) • Φ (ptLong (m + 1 + 1) z * upper v)) (muPi β (UT (m + 1 + 1))) := by
    intro t c ht hc
    have hD : (wMat (m + 1)).det * (c * t ^ (m + 1)) ≠ 0 :=
      mul_ne_zero (wMat_det_ne _) (mul_ne_zero hc (pow_ne_zero _ ht))
    obtain ⟨K, hK⟩ := derivBound_zero (by omega) C₁ h1 Φ A hA0 hG _ hD
    exact Formalism.FourierDecayAlt.P.orbital_integral_converges_abs m β A K hA1 E Φ t c ht hc hK
  refine ⟨fun t c ht hc => ?_, fun z hz => ?_⟩
  · have hdet : mdet (gTC (m + 1 + 1) t c) ≠ 0 := by
      rw [gTC_eq]; exact ptBlock_det_ne (m + 1) t c ht hc
    obtain ⟨hw, hcn⟩ := hν _ hdet
    rw [← LUs_compl] at hcn
    exact OmG_block hSB (m + 1) β t c hβ ht hc Φ hΦ (key t c ht hc).1 _ hw hcn
  · have hdet : mdet (gZW (m + 1 + 1) z) ≠ 0 := by
      rw [gZW_eq]; exact ptLong_det_ne (m + 1 + 1) z hz
    obtain ⟨hw, hcn⟩ := hν _ hdet
    rw [← LUs_compl] at hcn
    have hc : ((-1 : ℂ)) ^ (m + 3) * z ^ (m + 2) ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hz)
    have hi := (key 1 ((-1) ^ (m + 3) * z ^ (m + 2)) one_ne_zero hc).2 z (by
      rw [one_pow, mul_one, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
      simp)
    exact OmG_long hSL (m + 1) β z hβ hz Φ hΦ hi _ hw hcn

/- English proof (translation)
Take `⟨C, hC⟩` from `stGerm_of_orbCoordC hG`. Use `⟨max C 1, fun C₁ h1 C₂ h2 => hC C₁ (le_trans (le_max_left _ _) h1) C₂ (le_trans (le_max_left _ _) h2) ?_⟩` and prove the remaining obligations. Conclude with `orbCoordC hSB hSL C₁ C₂ (le_trans zero_le_one (le_trans (le_max_right _ _) h1)) (le_trans (le_max_right _ _) h2)`.
-/
theorem stGerm_of_core (hSB : StabMeasBlock) (hSL : StabMeasLong) (hG : Germ) :
    ∃ C : ℝ, ∀ C₁ ≥ C, ∀ C₂ ≥ C, stGerm C₁ C₂ := by
  obtain ⟨C, hC⟩ := stGerm_of_orbCoordC hG
  refine ⟨max C 1, fun C₁ h1 C₂ h2 => hC C₁ (le_trans (le_max_left _ _) h1) C₂ (le_trans (le_max_left _ _) h2) ?_⟩
  exact orbCoordC hSB hSL C₁ C₂ (le_trans zero_le_one (le_trans (le_max_right _ _) h1)) (le_trans (le_max_right _ _) h2)

/- English proof (translation)
The claim follows from `stGerm_of_core hSB hSL (Formalism.FourierDecayAlt.P.germ_of_rate hR)`.
-/
theorem stGerm_of_rate (hSB : StabMeasBlock) (hSL : StabMeasLong) (hR : GermRate) :
    ∃ C : ℝ, ∀ C₁ ≥ C, ∀ C₂ ≥ C, stGerm C₁ C₂ :=
  stGerm_of_core hSB hSL (Formalism.FourierDecayAlt.P.germ_of_rate hR)

end Formalism.MainNotions.InterlacingSignCuts.Gm

end

end PartAGo

section PartAGk

open MeasureTheory Matrix
open scoped ContDiff

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts.Gm

open Formalism.MainNotions.S.UnitaryLevelOperators Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P Formalism.MainNotions.S

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

def bivariateExponentMonomial (n : ℕ) : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ := Matrix.single 0 1 1

/- English proof (translation)
Unfold `bivariateExponentMonomial`. Rewrite using `[Matrix.single_mul_single_of_ne]`. Conclude with `(Fin.zero_ne_one (n := n)).symm`.
-/
theorem elementary_matrix_sq_eq_zero (n : ℕ) : bivariateExponentMonomial n * bivariateExponentMonomial n = 0 := by
  unfold bivariateExponentMonomial
  rw [Matrix.single_mul_single_of_ne]
  exact (Fin.zero_ne_one (n := n)).symm

/- English proof (translation)
Rewrite using `[NormedSpace.exp_eq_tsum ℂ]`. Simplify using `only []`. Rewrite using `[tsum_eq_sum (s := Finset.range 2)]`. Simplify using `[Finset.sum_range_succ]`. Introduce `k hk`.

Establish `hk2 : 2 ≤ k`. Establish `: ¬ k < 2` using `by simpa using hk`. Use linear arithmetic over natural numbers and integers. Take `⟨j, rfl⟩` from `Nat.exists_eq_add_of_le hk2`. Establish `: (a • bivariateExponentMonomial n) ^ 2 = 0`.

Rewrite using `[pow_two, Matrix.smul_mul, Matrix.mul_smul, elementary_matrix_sq_eq_zero]`. Simplify using the standard rewrite rules. Rewrite using `[pow_add, this]`. Simplify using the standard rewrite rules.
-/
theorem exp_nilpotent_elementary_matrix (n : ℕ) (a : ℂ) : NormedSpace.exp (a • bivariateExponentMonomial n) = 1 + a • bivariateExponentMonomial n := by
  rw [NormedSpace.exp_eq_tsum ℂ]
  simp only []
  rw [tsum_eq_sum (s := Finset.range 2)]
  · simp [Finset.sum_range_succ]
  · intro k hk
    have hk2 : 2 ≤ k := by
      have : ¬ k < 2 := by simpa using hk
      omega
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk2
    have : (a • bivariateExponentMonomial n) ^ 2 = 0 := by
      rw [pow_two, Matrix.smul_mul, Matrix.mul_smul, elementary_matrix_sq_eq_zero]; simp
    rw [pow_add, this]; simp

/- English proof (translation)
Use `⟨fun i => ?_, fun i j hij => ?_⟩` and prove the remaining obligations. Establish `: ¬ ((0 : Fin (n + 2)) = i ∧ (1 : Fin (n + 2)) = i)`. Introduce and unpack `⟨h1, h2⟩`. Conclude with `absurd (h1.trans h2.symm) (Fin.zero_ne_one (n := n))`. Simplify using `[bivariateExponentMonomial, Matrix.single_apply, this]`.

Establish `: ¬ ((0 : Fin (n + 2)) = i ∧ (1 : Fin (n + 2)) = j)`. Introduce and unpack `⟨h1, h2⟩`. Substitute `h1 h2` using the available equality. Conclude with `absurd hij (by simp)`. Simplify using `[bivariateExponentMonomial, Matrix.single_apply, this, Matrix.one_apply, hij.ne']`.
-/
theorem elementary_matrix_unipotent_upper (n : ℕ) (a : ℂ) : IsUpperUni (1 + a • bivariateExponentMonomial n) := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · have : ¬ ((0 : Fin (n + 2)) = i ∧ (1 : Fin (n + 2)) = i) := by
      rintro ⟨h1, h2⟩
      exact absurd (h1.trans h2.symm) (Fin.zero_ne_one (n := n))
    simp [bivariateExponentMonomial, Matrix.single_apply, this]
  · have : ¬ ((0 : Fin (n + 2)) = i ∧ (1 : Fin (n + 2)) = j) := by
      rintro ⟨h1, h2⟩
      subst h1 h2
      exact absurd hij (by simp)
    simp [bivariateExponentMonomial, Matrix.single_apply, this, Matrix.one_apply, hij.ne']

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => ⟨fun i => (h i i).2 rfl, fun i j hij => (h i j).1 hij⟩, fun h i j => ⟨fun hij => h.2 i j hij, fun e => e ▸ h.1 i⟩⟩`.
-/
theorem isUpUni_iff {d : ℕ} (u : Matrix (Fin d) (Fin d) ℂ) : IsUpUni u ↔ IsUpperUni u :=
  ⟨fun h => ⟨fun i => (h i i).2 rfl, fun i j hij => (h i j).1 hij⟩,
    fun h i j => ⟨fun hij => h.2 i j hij, fun e => e ▸ h.1 i⟩⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => ⟨fun i => (h i i).2 rfl, fun i j hij => (h j i).1 hij⟩, fun h i j => ⟨fun hij => h.2 j i hij, fun e => e ▸ h.1 i⟩⟩`.
-/
theorem isLoUni_iff {d : ℕ} (l : Matrix (Fin d) (Fin d) ℂ) : IsLoUni l ↔ IsLowerUni l :=
  ⟨fun h => ⟨fun i => (h i i).2 rfl, fun i j hij => (h j i).1 hij⟩,
    fun h i j => ⟨fun hij => h.2 j i hij, fun e => e ▸ h.1 i⟩⟩

/- English proof (translation)
Use `⟨(isUpUni_iff u).2 hu, (isLoUni_iff _).2 ?_⟩` and prove the remaining obligations. Rewrite using `[gZW_eq, of_toM, conjL d z hz]`. Conclude with `G4.lowerUni_conj (G4.upperUni_inv hu)`.
-/
theorem stabU_long {d : ℕ} (z : ℂ) (hz : z ≠ 0) (u : Matrix (Fin d) (Fin d) ℂ) (hu : IsUpperUni u) :
    u ∈ stabU (gZW d z) := by
  refine ⟨(isUpUni_iff u).2 hu, (isLoUni_iff _).2 ?_⟩
  rw [gZW_eq, of_toM, conjL d z hz]
  exact G4.lowerUni_conj (G4.upperUni_inv hu)

/- English proof (translation)
Introduce `t`. Rewrite using `[exp_nilpotent_elementary_matrix]`. Conclude with `stabU_long z hz _ (elementary_matrix_unipotent_upper n _)`.
-/
theorem elementary_matrix_mem_stabilizer_lie (n : ℕ) (z : ℂ) (hz : z ≠ 0) : bivariateExponentMonomial n ∈ lieOf (stabU (gZW (n + 2) z)) := by
  intro t
  rw [exp_nilpotent_elementary_matrix]
  exact stabU_long z hz _ (elementary_matrix_unipotent_upper n _)

/- English proof (translation)
Use `⟨⟨⟨(WithLp.equiv 2 _).symm (realifyFun (bivariateExponentMonomial n)), Submodule.subset_span ⟨bivariateExponentMonomial n, elementary_matrix_mem_stabilizer_lie n z hz, rfl⟩⟩, 0, ?_⟩⟩` and prove the remaining obligations. Introduce `h`. Establish `h1` using `congrArg (fun x : lieE (stabU (gZW (n + 2) z)) => (x : EuclideanSpace ℝ (Fin (n + 2) × Fin (n + 2) × Bool)) ((0 : Fin (n + 2)), (1 : Fin (n + 2)), false)) h`. Simplify using `[realifyFun, bivariateExponentMonomial] at h1`.
-/
theorem lieE_nontrivial (n : ℕ) (z : ℂ) (hz : z ≠ 0) : Nontrivial (lieE (stabU (gZW (n + 2) z))) := by
  refine ⟨⟨⟨(WithLp.equiv 2 _).symm (realifyFun (bivariateExponentMonomial n)), Submodule.subset_span ⟨bivariateExponentMonomial n, elementary_matrix_mem_stabilizer_lie n z hz, rfl⟩⟩, 0, ?_⟩⟩
  intro h
  have h1 := congrArg (fun x : lieE (stabU (gZW (n + 2) z)) =>
    (x : EuclideanSpace ℝ (Fin (n + 2) × Fin (n + 2) × Bool)) ((0 : Fin (n + 2)), (1 : Fin (n + 2)), false)) h
  simp [realifyFun, bivariateExponentMonomial] at h1

/- English proof (translation)
Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Establish `h1 : Continuous fun x : EuclideanSpace ℝ (Fin m × Fin m × Bool) => x (i, j, false)` using `(EuclideanSpace.proj (𝕜 := ℝ) (i, j, false)).continuous`. Establish `h2 : Continuous fun x : EuclideanSpace ℝ (Fin m × Fin m × Bool) => x (i, j, true)` using `(EuclideanSpace.proj (𝕜 := ℝ) (i, j, true)).continuous`. Establish `: (fun x : EuclideanSpace ℝ (Fin m × Fin m × Bool) => unrealify x i j) = fun x => ((x (i, j, false) : ℝ) : ℂ) + ((x (i, j, true) : ℝ) : ℂ) * Complex.I`. Use function extensionality and compare the values at `x`.

Apply the tactic sequence `apply Complex.ext <;> simp [unrealify]`. Rewrite using `[this]`. Conclude with `(Complex.continuous_ofReal.comp h1).add ((Complex.continuous_ofReal.comp h2).mul continuous_const)`.
-/
theorem continuous_unrealify (m : ℕ) : Continuous (unrealify (m := m)) := by
  refine continuous_matrix fun i j => ?_
  have h1 : Continuous fun x : EuclideanSpace ℝ (Fin m × Fin m × Bool) => x (i, j, false) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (i, j, false)).continuous
  have h2 : Continuous fun x : EuclideanSpace ℝ (Fin m × Fin m × Bool) => x (i, j, true) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (i, j, true)).continuous
  have : (fun x : EuclideanSpace ℝ (Fin m × Fin m × Bool) => unrealify x i j) =
      fun x => ((x (i, j, false) : ℝ) : ℂ) + ((x (i, j, true) : ℝ) : ℂ) * Complex.I := by
    funext x
    apply Complex.ext <;> simp [unrealify]
  rw [this]
  exact (Complex.continuous_ofReal.comp h1).add ((Complex.continuous_ofReal.comp h2).mul continuous_const)

/- English proof (translation)
Use `haveI := lieE_nontrivial n z hz`. Unfold `muStab`. Establish `hm : Measurable (fun x : lieE (stabU (gZW (n + 2) z)) => (fun i j => NormedSpace.exp (unrealify ((x : lieE (stabU (gZW (n + 2) z))) : EuclideanSpace ℝ (Fin (n + 2) × Fin (n + 2) × Bool))) i j : Msq (n + 2)))`. Use `Continuous.measurable ?_` and prove the remaining obligations. Establish `h1 : Continuous fun x : lieE (stabU (gZW (n + 2) z)) => NormedSpace.exp (unrealify ((x : lieE (stabU (gZW (n + 2) z))) : EuclideanSpace ℝ (Fin (n + 2) × Fin (n + 2) × Bool)))` using `NormedSpace.exp_continuous.comp ((continuous_unrealify _).comp continuous_subtype_val)`.

Conclude with `h1`. Rewrite using `[Measure.smul_apply, Measure.map_apply hm MeasurableSet.univ, Set.preimage_univ]`. Use `haveI : NoncompactSpace (lieE (stabU (gZW (n + 2) z))) := NormedSpace.noncompactSpace ℝ _`. Rewrite using `[measure_univ_of_isAddLeftInvariant, smul_eq_mul, ENNReal.mul_top]`. Unfold `sdScale`.

Establish `: 0 < ‖c‖ / (2 * Real.pi)` using `div_pos (norm_pos_iff.2 hc) (by positivity)`. Conclude with `(ENNReal.ofReal_pos.2 (pow_pos this _)).ne'`.
-/
theorem muStab_long_top (n : ℕ) (c z : ℂ) (hc : c ≠ 0) (hz : z ≠ 0) : muStab c (gZW (n + 2) z) Set.univ = ⊤ := by
  haveI := lieE_nontrivial n z hz
  unfold muStab
  have hm : Measurable (fun x : lieE (stabU (gZW (n + 2) z)) =>
      (fun i j => NormedSpace.exp (unrealify ((x : lieE (stabU (gZW (n + 2) z))) :
        EuclideanSpace ℝ (Fin (n + 2) × Fin (n + 2) × Bool))) i j : Msq (n + 2))) := by
    refine Continuous.measurable ?_
    have h1 : Continuous fun x : lieE (stabU (gZW (n + 2) z)) =>
        NormedSpace.exp (unrealify ((x : lieE (stabU (gZW (n + 2) z))) :
          EuclideanSpace ℝ (Fin (n + 2) × Fin (n + 2) × Bool))) :=
      NormedSpace.exp_continuous.comp ((continuous_unrealify _).comp continuous_subtype_val)
    exact h1
  rw [Measure.smul_apply, Measure.map_apply hm MeasurableSet.univ, Set.preimage_univ]
  haveI : NoncompactSpace (lieE (stabU (gZW (n + 2) z))) := NormedSpace.noncompactSpace ℝ _
  rw [measure_univ_of_isAddLeftInvariant, smul_eq_mul, ENNReal.mul_top]
  unfold sdScale
  have : 0 < ‖c‖ / (2 * Real.pi) := div_pos (norm_pos_iff.2 hc) (by positivity)
  exact (ENNReal.ofReal_pos.2 (pow_pos this _)).ne'

/- English proof (translation)
The claim follows from `isOrbMeas_add_dirac c _ ν (muStab_long_top n c z hc hz) h`.
-/
theorem isOrbMeas_long_add_dirac (n : ℕ) (c z : ℂ) (hc : c ≠ 0) (hz : z ≠ 0)
    (ν : Measure (Msq (n + 2) × Msq (n + 2))) (h : IsOrbMeas c (gZW (n + 2) z) ν) :
    IsOrbMeas c (gZW (n + 2) z) (ν + Measure.dirac ((0 : Msq (n + 2)), (0 : Msq (n + 2)))) :=
  isOrbMeas_add_dirac c _ ν (muStab_long_top n c z hc hz) h

end Formalism.MainNotions.InterlacingSignCuts.Gm

end

end PartAGk

section PartAGs1

open Matrix MeasureTheory

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts.Gm

open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G5

def SUk {d : ℕ} (k : ℕ) (X : Matrix (Fin d) (Fin d) ℂ) : Prop := ∀ i j : Fin d, (j : ℕ) < i + k → X i j = 0

/- English proof (translation)
Introduce `i j h`. Rewrite using `[Matrix.mul_apply]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `l _`. Distinguish the cases in `hl : (l : ℕ) < i + a`.

Rewrite using `[hX i l hl, zero_mul]`. Rewrite using `[hY l j (by omega), mul_zero]`.
-/
theorem SUk.mul {d a b : ℕ} {X Y : Matrix (Fin d) (Fin d) ℂ} (hX : SUk a X) (hY : SUk b Y) : SUk (a + b) (X * Y) := by
  intro i j h
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro l _
  by_cases hl : (l : ℕ) < i + a
  · rw [hX i l hl, zero_mul]
  · rw [hY l j (by omega), mul_zero]

/- English proof (translation)
Introduce `i j h`. Conclude with `Matrix.one_apply_ne (fun hij => by subst hij; omega)`.
-/
theorem SUk_one (d : ℕ) : SUk 0 (1 : Matrix (Fin d) (Fin d) ℂ) := by
  intro i j h
  exact Matrix.one_apply_ne (fun hij => by subst hij; omega)

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Rewrite using `[pow_zero]`. Conclude with `SUk_one d`. Consider the case `succ k ih`.

Rewrite using `[pow_succ]`. Conclude with `ih.mul hX`.
-/
theorem SUk.pow {d : ℕ} {X : Matrix (Fin d) (Fin d) ℂ} (hX : SUk 1 X) (k : ℕ) : SUk k (X ^ k) := by
  induction k with
  | zero =>
    rw [pow_zero]
    exact SUk_one d
  | succ k ih =>
    rw [pow_succ]
    exact ih.mul hX

/- English proof (translation)
Use extensionality with `i j`. Use `j.isLt` as an intermediate fact. Conclude with `h i j (by omega)`.
-/
theorem SUk.eq_zero {d k : ℕ} {X : Matrix (Fin d) (Fin d) ℂ} (h : SUk k X) (hk : d ≤ k) : X = 0 := by
  ext i j
  have := j.isLt
  exact h i j (by omega)

/- English proof (translation)
Introduce `i j h`. Establish `hij : ¬ i < j`. Introduce `hij`. Establish `: (i : ℕ) < j` using `hij`. Use linear arithmetic over natural numbers and integers.

Simplify using `[strictUpper, hij]`.
-/
theorem SUk_strictUpper {d : ℕ} (v : UT d → ℂ) : SUk 1 (strictUpper v) := by
  intro i j h
  have hij : ¬ i < j := by
    intro hij
    have : (i : ℕ) < j := hij
    omega
  simp [strictUpper, hij]

/- English proof (translation)
Conclude with `(hX.pow N).eq_zero hN`.
-/
theorem pow_eq_zero_of_SUk {d : ℕ} {X : Matrix (Fin d) (Fin d) ℂ} (hX : SUk 1 X) {N : ℕ} (hN : d ≤ N) : X ^ N = 0 := by
  exact (hX.pow N).eq_zero hN

/- English proof (translation)
Rewrite using `[NormedSpace.exp_eq_tsum ℂ]`. Simplify using `only []`. Rewrite using `[tsum_eq_sum (s := Finset.range N)]`. Introduce `k hk`. Establish `hk2 : N ≤ k` using `by simpa using hk`.

Take `⟨j, rfl⟩` from `Nat.exists_eq_add_of_le hk2`. Rewrite using `[pow_add, h]`. Simplify using the standard rewrite rules.
-/
theorem exp_of_pow_eq_zero {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) (N : ℕ) (h : M ^ N = 0) :
    NormedSpace.exp M = ∑ k ∈ Finset.range N, ((k.factorial : ℂ)⁻¹) • M ^ k := by
  rw [NormedSpace.exp_eq_tsum ℂ]
  simp only []
  rw [tsum_eq_sum (s := Finset.range N)]
  intro k hk
  have hk2 : N ≤ k := by simpa using hk
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk2
  rw [pow_add, h]
  simp

/- English proof (translation)
Establish `hp` using `fun k => hX.pow k`. Prove the components needed by the constructor for the conclusion. Introduce `i`. Rewrite using `[Matrix.sum_apply, Finset.sum_range_succ', Finset.sum_eq_zero]`. Simplify using `[ha]`.

Introduce `k _`. Rewrite using `[Matrix.smul_apply, hp (k + 1) i i (by omega), smul_zero]`. Introduce `i j hij`. Rewrite using `[Matrix.sum_apply]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises.

Introduce `k _`. Establish `: (j : ℕ) < i` using `hij`. Rewrite using `[Matrix.smul_apply, hp k i j (by omega), smul_zero]`.
-/
theorem upperUni_series {d : ℕ} {X : Matrix (Fin d) (Fin d) ℂ} (hX : SUk 1 X) (a : ℕ → ℂ) (ha : a 0 = 1) (N : ℕ) :
    IsUpperUni (∑ k ∈ Finset.range (N + 1), a k • X ^ k) := by
  have hp := fun k => hX.pow k
  constructor
  · intro i
    rw [Matrix.sum_apply, Finset.sum_range_succ', Finset.sum_eq_zero]
    · simp [ha]
    · intro k _
      rw [Matrix.smul_apply, hp (k + 1) i i (by omega), smul_zero]
  · intro i j hij
    rw [Matrix.sum_apply]
    apply Finset.sum_eq_zero
    intro k _
    have : (j : ℕ) < i := hij
    rw [Matrix.smul_apply, hp k i j (by omega), smul_zero]

/- English proof (translation)
Rewrite using `[exp_of_pow_eq_zero X (d + 1) (pow_eq_zero_of_SUk hX (by omega))]`. Conclude with `upperUni_series hX (fun k => ((k.factorial : ℂ))⁻¹) (by simp) d`.
-/
theorem upperUni_exp {d : ℕ} {X : Matrix (Fin d) (Fin d) ℂ} (hX : SUk 1 X) : IsUpperUni (NormedSpace.exp X) := by
  rw [exp_of_pow_eq_zero X (d + 1) (pow_eq_zero_of_SUk hX (by omega))]
  exact upperUni_series hX (fun k => ((k.factorial : ℂ))⁻¹) (by simp) d

def phiS {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  ∑ k ∈ Finset.range (d + 1), (((k + 1).factorial : ℂ)⁻¹) • X ^ k

/- English proof (translation)
Unfold `phiS`. Conclude with `upperUni_series hX (fun k => (((k + 1).factorial : ℂ))⁻¹) (by simp) d`.
-/
theorem upperUni_phiS {d : ℕ} {X : Matrix (Fin d) (Fin d) ℂ} (hX : SUk 1 X) : IsUpperUni (phiS X) := by
  unfold phiS
  exact upperUni_series hX (fun k => (((k + 1).factorial : ℂ))⁻¹) (by simp) d

/- English proof (translation)
Establish `h` using `upperUni_phiS hX`. Establish `hbt : (phiS X).BlockTriangular id`. Introduce `i j hij`. Conclude with `h.2 i j hij`. Rewrite using `[Matrix.det_of_upperTriangular hbt]`.

Simplify using `[h.1]`.
-/
theorem det_phiS {d : ℕ} {X : Matrix (Fin d) (Fin d) ℂ} (hX : SUk 1 X) : (phiS X).det = 1 := by
  have h := upperUni_phiS hX
  have hbt : (phiS X).BlockTriangular id := by
    intro i j hij
    exact h.2 i j hij
  rw [Matrix.det_of_upperTriangular hbt]
  simp [h.1]

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>`. Simplify using `[Matrix.add_apply, blk_cc, blk_cl, blk_lc, blk_ll]`.
-/
theorem blk_add {n : ℕ} (A A' : Matrix (Fin n) (Fin n) ℂ) (b a b' a' : Fin n → ℂ) (e e' : ℂ) :
    blk A b a e + blk A' b' a' e' = blk (A + A') (b + b') (a + a') (e + e') := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [Matrix.add_apply, blk_cc, blk_cl, blk_lc, blk_ll]

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>`. Simplify using `[Matrix.smul_apply, blk_cc, blk_cl, blk_lc, blk_ll]`.
-/
theorem blk_smul {n : ℕ} (x : ℂ) (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) :
    x • blk A b a e = blk (x • A) (x • b) (x • a) (x * e) := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [Matrix.smul_apply, blk_cc, blk_cl, blk_lc, blk_ll]

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>`. Simplify using `[blk_cc, blk_cl, blk_lc, blk_ll]`.
-/
theorem blk_zero (n : ℕ) : blk (0 : Matrix (Fin n) (Fin n) ℂ) 0 0 0 = 0 := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [blk_cc, blk_cl, blk_lc, blk_ll]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [blk_zero]`. Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha, ih, blk_add]`. Simplify using the standard rewrite rules.
-/
theorem blk_sum {n : ℕ} {ι : Type} (s : Finset ι) (A : ι → Matrix (Fin n) (Fin n) ℂ) (b : ι → Fin n → ℂ) :
    ∑ k ∈ s, blk (A k) (b k) 0 0 = blk (∑ k ∈ s, A k) (∑ k ∈ s, b k) 0 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [blk_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha, ih, blk_add]; simp

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[pow_succ', ih, blk_mul]`. Use `congr 1`.

Rewrite using `[pow_succ' X (k + 1)]`. Use extensionality with `i j`. Simplify using `[Matrix.vecMulVec_apply]`. Rewrite using `[Matrix.mulVec_mulVec, ← pow_succ']`. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem blk_pow_succ {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (b : Fin n → ℂ) (k : ℕ) :
    (blk X b 0 0) ^ (k + 1) = blk (X ^ (k + 1)) (X ^ k *ᵥ b) 0 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', ih, blk_mul]
    congr 1
    · rw [pow_succ' X (k + 1)]
      ext i j
      simp [Matrix.vecMulVec_apply]
    · rw [Matrix.mulVec_mulVec, ← pow_succ']
      simp
    · simp
    · simp

/- English proof (translation)
Establish `h0 : (blk X b 0 0) ^ (n + 1 + 1) = 0`. Rewrite using `[blk_pow_succ, pow_eq_zero_of_SUk hX (by omega), pow_eq_zero_of_SUk hX (by omega : n ≤ n + 1)]`. Simplify using `[blk_zero]`. Rewrite using `[exp_of_pow_eq_zero _ (n + 1 + 1) h0, exp_of_pow_eq_zero X (n + 1 + 1) (pow_eq_zero_of_SUk hX (by omega)), Finset.sum_range_succ', Finset.sum_range_succ' (fun k => ((k.factorial : ℂ)⁻¹) • X ^ k)]`. Simplify using `only [blk_pow_succ, blk_smul, smul_zero, mul_zero]`.

Rewrite using `[blk_sum]`. Simplify using `only [pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul]`. Rewrite using `[← blk_one, blk_add]`. Use `congr 1`. Simplify using `only [phiS, Matrix.sum_mulVec, Matrix.smul_mulVec, add_zero]`.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem exp_blk {n : ℕ} {X : Matrix (Fin n) (Fin n) ℂ} (hX : SUk 1 X) (b : Fin n → ℂ) :
    NormedSpace.exp (blk X b 0 0) = blk (NormedSpace.exp X) (phiS X *ᵥ b) 0 1 := by
  have h0 : (blk X b 0 0) ^ (n + 1 + 1) = 0 := by
    rw [blk_pow_succ, pow_eq_zero_of_SUk hX (by omega), pow_eq_zero_of_SUk hX (by omega : n ≤ n + 1)]
    simp [blk_zero]
  rw [exp_of_pow_eq_zero _ (n + 1 + 1) h0, exp_of_pow_eq_zero X (n + 1 + 1) (pow_eq_zero_of_SUk hX (by omega)),
    Finset.sum_range_succ', Finset.sum_range_succ' (fun k => ((k.factorial : ℂ)⁻¹) • X ^ k)]
  simp only [blk_pow_succ, blk_smul, smul_zero, mul_zero]
  rw [blk_sum]
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul]
  rw [← blk_one, blk_add]
  congr 1
  · simp only [phiS, Matrix.sum_mulVec, Matrix.smul_mulVec, add_zero]
  · simp
  · simp

def expU (d : ℕ) (v : UT d → ℂ) : UT d → ℂ := coordU (NormedSpace.exp (strictUpper v))

/- English proof (translation)
The claim follows from `G4.upper_coordU (upperUni_exp (SUk_strictUpper v))`.
-/
theorem upper_expU {d : ℕ} (v : UT d → ℂ) : upper (expU d v) = NormedSpace.exp (strictUpper v) :=
  G4.upper_coordU (upperUni_exp (SUk_strictUpper v))

/- English proof (translation)
Establish `h` using `upper_joinU v b`. Establish `h2 : blk (upper v) b 0 1 = 1 + blk (strictUpper v) b 0 0`. Rewrite using `[← blk_one, blk_add]`. Simplify using `[upper]`. Rewrite `h` using `[h2]`.

Conclude with `add_left_cancel h`.
-/
theorem strictUpper_joinU {n : ℕ} (v : UT n → ℂ) (b : Fin n → ℂ) :
    strictUpper (joinU (v, b)) = blk (strictUpper v) b 0 0 := by
  have h := upper_joinU v b
  have h2 : blk (upper v) b 0 1 = 1 + blk (strictUpper v) b 0 0 := by
    rw [← blk_one, blk_add]; simp [upper]
  rw [h2] at h
  exact add_left_cancel h

/- English proof (translation)
Establish `h : (strictUpper : (UT d → ℂ) → Matrix (Fin d) (Fin d) ℂ) = fun v => upper v - 1`. Use function extensionality and compare the values at `v`. Simplify using `[upper]`. Rewrite using `[h]`. Conclude with `(continuous_upper d).sub continuous_const`.
-/
theorem continuous_strictUpper (d : ℕ) : Continuous (strictUpper : (UT d → ℂ) → Matrix (Fin d) (Fin d) ℂ) := by
  have h : (strictUpper : (UT d → ℂ) → Matrix (Fin d) (Fin d) ℂ) = fun v => upper v - 1 := by
    funext v; simp [upper]
  rw [h]
  exact (continuous_upper d).sub continuous_const

/- English proof (translation)
The claim follows from `continuous_finsetSum _ fun k _ => (continuous_pow k).const_smul (a k)`.
-/
theorem continuous_series {d : ℕ} (a : ℕ → ℂ) (N : ℕ) :
    Continuous fun X : Matrix (Fin d) (Fin d) ℂ => ∑ k ∈ Finset.range N, a k • X ^ k :=
  continuous_finsetSum _ fun k _ => (continuous_pow k).const_smul (a k)

/- English proof (translation)
Establish `h : (fun v : UT d → ℂ => NormedSpace.exp (strictUpper v)) = fun v => ∑ k ∈ Finset.range (d + 1), ((k.factorial : ℂ)⁻¹) • (strictUpper v) ^ k`. Use function extensionality and compare the values at `v`. Conclude with `exp_of_pow_eq_zero _ _ (pow_eq_zero_of_SUk (SUk_strictUpper v) (by omega))`. Rewrite using `[h]`. Conclude with `(continuous_series _ _).comp (continuous_strictUpper d)`.
-/
theorem continuous_exp_strictUpper (d : ℕ) :
    Continuous fun v : UT d → ℂ => NormedSpace.exp (strictUpper v) := by
  have h : (fun v : UT d → ℂ => NormedSpace.exp (strictUpper v)) =
      fun v => ∑ k ∈ Finset.range (d + 1), ((k.factorial : ℂ)⁻¹) • (strictUpper v) ^ k := by
    funext v
    exact exp_of_pow_eq_zero _ _ (pow_eq_zero_of_SUk (SUk_strictUpper v) (by omega))
  rw [h]
  exact (continuous_series _ _).comp (continuous_strictUpper d)

/- English proof (translation)
The claim follows from `(continuous_coordU d).comp (continuous_exp_strictUpper d)`.
-/
theorem continuous_expU (d : ℕ) : Continuous (expU d) := (continuous_coordU d).comp (continuous_exp_strictUpper d)

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Establish `h : expU 0 = id`. Use function extensionality and compare the values at `v p`.

Conclude with `p.1.1.elim0`. Rewrite using `[h]`. Conclude with `MeasurePreserving.id _`. Consider the case `succ n ih`. Use `mp_of_comp (mp_joinU β n) (continuous_expU _).measurable ?_` and prove the remaining obligations.

Establish `hm : Measurable (Function.uncurry fun (v : UT n → ℂ) (b : Fin n → ℂ) => phiS (strictUpper v) *ᵥ b)`. Use `Continuous.measurable ?_` and prove the remaining obligations. Use `Continuous.matrix_mulVec ?_ continuous_snd` and prove the remaining obligations. Conclude with `((continuous_series _ _).comp (continuous_strictUpper n)).comp continuous_fst`. Establish `hS` using `ih.skew_product (μc := muPi β (Fin n)) (μd := muPi β (Fin n)) hm (Filter.Eventually.of_forall fun v => (mp_mulVec β (phiS (strictUpper v)) (by rw [det_phiS (SUk_strictUpper v)]; simp)).map_eq)`.

Establish `he : expU (n + 1) ∘ joinU = joinU ∘ fun p : (UT n → ℂ) × (Fin n → ℂ) => (expU n p.1, phiS (strictUpper p.1) *ᵥ p.2)`. Use function extensionality and compare the values at `p`. Take `⟨v, b⟩` from `p`. Simplify using `only [Function.comp, expU]`. Rewrite using `[strictUpper_joinU, exp_blk (SUk_strictUpper v), coordU_blk]`.

Rewrite using `[he]`. Conclude with `(mp_joinU β n).comp hS`.
-/
theorem mp_expU (β : ℂ) : ∀ n : ℕ, MeasurePreserving (expU n) (muPi β (UT n)) (muPi β (UT n)) := by
  intro n
  induction n with
  | zero =>
    have h : expU 0 = id := by
      funext v p
      exact p.1.1.elim0
    rw [h]
    exact MeasurePreserving.id _
  | succ n ih =>
    refine mp_of_comp (mp_joinU β n) (continuous_expU _).measurable ?_
    have hm : Measurable (Function.uncurry fun (v : UT n → ℂ) (b : Fin n → ℂ) => phiS (strictUpper v) *ᵥ b) := by
      refine Continuous.measurable ?_
      refine Continuous.matrix_mulVec ?_ continuous_snd
      exact ((continuous_series _ _).comp (continuous_strictUpper n)).comp continuous_fst
    have hS := ih.skew_product (μc := muPi β (Fin n)) (μd := muPi β (Fin n)) hm
      (Filter.Eventually.of_forall fun v => (mp_mulVec β (phiS (strictUpper v))
        (by rw [det_phiS (SUk_strictUpper v)]; simp)).map_eq)
    have he : expU (n + 1) ∘ joinU =
        joinU ∘ fun p : (UT n → ℂ) × (Fin n → ℂ) => (expU n p.1, phiS (strictUpper p.1) *ᵥ p.2) := by
      funext p
      obtain ⟨v, b⟩ := p
      simp only [Function.comp, expU]
      rw [strictUpper_joinU, exp_blk (SUk_strictUpper v), coordU_blk]
    rw [he]
    exact (mp_joinU β n).comp hS

end Formalism.MainNotions.InterlacingSignCuts.Gm

end

end PartAGs1

section PartAGs2

open MeasureTheory Matrix

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts.Gm

open Formalism.MainNotions.S

variable {s : ℕ} {ι : Type} [Fintype ι]

def emb (e : ι → Fin s × Fin s) (v : ι → ℂ) : Matrix (Fin s) (Fin s) ℂ :=
  fun i j => ∑ k, if e k = (i, j) then v k else 0

def phiR (e : ι → Fin s × Fin s) : ι ⊕ ι → Fin s × Fin s × Bool
  | Sum.inl k => ((e k).1, (e k).2, false)
  | Sum.inr k => ((e k).1, (e k).2, true)

/- English proof (translation)
Introduce `a b h`. Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b <;> simp only [phiR, Prod.mk.injEq] at h <;> first`. Consider the case `exact congrArg Sum.inl (he (Prod.ext h.1 h.2.1))`. Consider the case `exact congrArg Sum.inr (he (Prod.ext h.1 h.2.1))`. Consider the case `exact congrArg Sum.inl (he (Prod.ext h.1 h.2))`.

Consider the case `exact congrArg Sum.inr (he (Prod.ext h.1 h.2))`. Consider the case `exact absurd h.2.2 (by decide)`. Consider the case `simp at h`.
-/
theorem phiR_injective {e : ι → Fin s × Fin s} (he : Function.Injective e) : Function.Injective (phiR e) := by
  intro a b h
  rcases a with a | a <;> rcases b with b | b <;> simp only [phiR, Prod.mk.injEq] at h <;>
    first
    | exact congrArg Sum.inl (he (Prod.ext h.1 h.2.1))
    | exact congrArg Sum.inr (he (Prod.ext h.1 h.2.1))
    | exact congrArg Sum.inl (he (Prod.ext h.1 h.2))
    | exact congrArg Sum.inr (he (Prod.ext h.1 h.2))
    | exact absurd h.2.2 (by decide)
    | simp at h

def JLin (e : ι → Fin s × Fin s) :
    EuclideanSpace ℝ (ι ⊕ ι) →ₗ[ℝ] EuclideanSpace ℝ (Fin s × Fin s × Bool) :=
  (EuclideanSpace.basisFun (ι ⊕ ι) ℝ).toBasis.constr ℝ (fun k => EuclideanSpace.single (phiR e k) (1 : ℝ))

/- English proof (translation)
Rewrite using `[JLin, Module.Basis.constr_apply_fintype]`. Simplify using `[Pi.single_apply, eq_comm (a := p)]`.
-/
theorem JLin_apply (e : ι → Fin s × Fin s) (y : EuclideanSpace ℝ (ι ⊕ ι)) (p : Fin s × Fin s × Bool) :
    JLin e y p = ∑ k, if phiR e k = p then y k else 0 := by
  classical
  rw [JLin, Module.Basis.constr_apply_fintype]
  simp [Pi.single_apply, eq_comm (a := p)]

def JIso {e : ι → Fin s × Fin s} (he : Function.Injective e) :
    EuclideanSpace ℝ (ι ⊕ ι) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin s × Fin s × Bool) :=
  (JLin e).isometryOfOrthonormal (v := (EuclideanSpace.basisFun (ι ⊕ ι) ℝ).toBasis)
    (by rw [OrthonormalBasis.coe_toBasis]; exact (EuclideanSpace.basisFun (ι ⊕ ι) ℝ).orthonormal)
    (by
      have h : (JLin e) ∘ (EuclideanSpace.basisFun (ι ⊕ ι) ℝ).toBasis =
          (EuclideanSpace.basisFun (Fin s × Fin s × Bool) ℝ) ∘ phiR e := by
        funext k
        simp only [Function.comp, JLin]
        rw [Module.Basis.constr_basis]
        simp
      rw [h]
      exact (EuclideanSpace.basisFun (Fin s × Fin s × Bool) ℝ).orthonormal.comp _ (phiR_injective he))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem JIso_apply {e : ι → Fin s × Fin s} (he : Function.Injective e) (y : EuclideanSpace ℝ (ι ⊕ ι)) :
    JIso he y = JLin e y := rfl

def reals (v : ι → ℂ) : EuclideanSpace ℝ (ι ⊕ ι) :=
  WithLp.toLp 2 (Sum.elim (fun k => (v k).re) (fun k => (v k).im))

/- English proof (translation)
Introduce `y`. Use `⟨fun k => ⟨y (Sum.inl k), y (Sum.inr k)⟩, ?_⟩` and prove the remaining obligations. Use extensionality with `k`. Apply the tactic sequence `rcases k with k | k <;> simp [reals]`.
-/
theorem reals_surjective : Function.Surjective (reals : (ι → ℂ) → EuclideanSpace ℝ (ι ⊕ ι)) := by
  intro y
  refine ⟨fun k => ⟨y (Sum.inl k), y (Sum.inr k)⟩, ?_⟩
  ext k
  rcases k with k | k <;> simp [reals]

/- English proof (translation)
Establish `m1` using `volume_preserving_pi (ι := ι) (α' := fun _ => ℂ) (β' := fun _ => ℝ × ℝ) (f := fun _ => Complex.measurableEquivRealProd) (fun _ => Complex.volume_preserving_equiv_real_prod)`. Establish `m2` using `volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ ι`. Establish `m3` using `volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : ι ⊕ ι => ℝ)`. Establish `m4` using `PiLp.volume_preserving_toLp (ι ⊕ ι)`. Establish `h` using `m4.comp (m3.comp (m2.comp m1))`.

Establish `he : (reals : (ι → ℂ) → EuclideanSpace ℝ (ι ⊕ ι)) = (WithLp.toLp 2 ∘ ⇑(MeasurableEquiv.sumPiEquivProdPi fun _ : ι ⊕ ι => ℝ).symm ∘ ⇑(MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ι) ∘ fun a i => Complex.measurableEquivRealProd (a i))`. Use function extensionality and compare the values at `v`. Use extensionality with `k`. Apply the tactic sequence `rcases k with k | k <;> rfl`. Rewrite using `[he]`.

Conclude with `h`.
-/
theorem mp_reals : MeasurePreserving (reals : (ι → ℂ) → EuclideanSpace ℝ (ι ⊕ ι)) volume volume := by
  have m1 := volume_preserving_pi (ι := ι) (α' := fun _ => ℂ) (β' := fun _ => ℝ × ℝ)
    (f := fun _ => Complex.measurableEquivRealProd) (fun _ => Complex.volume_preserving_equiv_real_prod)
  have m2 := volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ ι
  have m3 := volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : ι ⊕ ι => ℝ)
  have m4 := PiLp.volume_preserving_toLp (ι ⊕ ι)
  have h := m4.comp (m3.comp (m2.comp m1))
  have he : (reals : (ι → ℂ) → EuclideanSpace ℝ (ι ⊕ ι)) =
      (WithLp.toLp 2 ∘ ⇑(MeasurableEquiv.sumPiEquivProdPi fun _ : ι ⊕ ι => ℝ).symm ∘
        ⇑(MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ι) ∘ fun a i => Complex.measurableEquivRealProd (a i)) := by
    funext v
    ext k
    rcases k with k | k <;> rfl
  rw [he]
  exact h

/- English proof (translation)
Use extensionality with `i j`. Apply `Complex.ext` to reduce the goal to its premises. Simplify using `only [unrealify, emb, JLin_apply, Fintype.sum_sum_type, phiR, reals]`. Simplify using `[Complex.re_sum, apply_ite Complex.re, Prod.ext_iff, and_assoc]`. Simplify using `only [unrealify, emb, JLin_apply, Fintype.sum_sum_type, phiR, reals]`.

Simplify using `[Complex.im_sum, apply_ite Complex.im, Prod.ext_iff, and_assoc]`.
-/
theorem unrealify_J (e : ι → Fin s × Fin s) (v : ι → ℂ) : unrealify (JLin e (reals v)) = emb e v := by
  ext i j
  apply Complex.ext
  · simp only [unrealify, emb, JLin_apply, Fintype.sum_sum_type, phiR, reals]
    simp [Complex.re_sum, apply_ite Complex.re, Prod.ext_iff, and_assoc]
  · simp only [unrealify, emb, JLin_apply, Fintype.sum_sum_type, phiR, reals]
    simp [Complex.im_sum, apply_ite Complex.im, Prod.ext_iff, and_assoc]

/- English proof (translation)
Use extensionality with `p`. Take `⟨i, j, b⟩` from `p`. Rewrite using `[JLin_apply]`. Consider the cases of `b`. Simplify using `only [Fintype.sum_sum_type, phiR, reals]`.

Simplify using `[realifyFun, emb, Complex.re_sum, apply_ite Complex.re, Prod.ext_iff, and_assoc]`. Simplify using `only [Fintype.sum_sum_type, phiR, reals]`. Simplify using `[realifyFun, emb, Complex.im_sum, apply_ite Complex.im, Prod.ext_iff, and_assoc]`.
-/
theorem realify_emb (e : ι → Fin s × Fin s) (v : ι → ℂ) :
    (WithLp.equiv 2 _).symm (realifyFun (emb e v)) = JLin e (reals v) := by
  ext p
  obtain ⟨i, j, b⟩ := p
  rw [JLin_apply]
  cases b
  · simp only [Fintype.sum_sum_type, phiR, reals]
    simp [realifyFun, emb, Complex.re_sum, apply_ite Complex.re, Prod.ext_iff, and_assoc]
  · simp only [Fintype.sum_sum_type, phiR, reals]
    simp [realifyFun, emb, Complex.im_sum, apply_ite Complex.im, Prod.ext_iff, and_assoc]

/- English proof (translation)
Establish `h : (fun X => (WithLp.equiv 2 _).symm (realifyFun X)) '' lieOf S = (LinearMap.range (JIso he).toLinearMap : Set (EuclideanSpace ℝ (Fin s × Fin s × Bool)))`. Rewrite using `[hS]`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨v, rfl⟩, rfl⟩`.

Conclude with `⟨reals v, (realify_emb e v).symm⟩`. Introduce and unpack `⟨y, rfl⟩`. Take `⟨v, rfl⟩` from `reals_surjective y`. Conclude with `⟨_, ⟨v, rfl⟩, realify_emb e v⟩`. Rewrite using `[lieE, h, Submodule.span_eq]`.
-/
theorem lieE_eq_range {e : ι → Fin s × Fin s} (he : Function.Injective e) {S : Set (Matrix (Fin s) (Fin s) ℂ)}
    (hS : lieOf S = Set.range (emb e)) : lieE S = LinearMap.range (JIso he).toLinearMap := by
  have h : (fun X => (WithLp.equiv 2 _).symm (realifyFun X)) '' lieOf S =
      (LinearMap.range (JIso he).toLinearMap : Set (EuclideanSpace ℝ (Fin s × Fin s × Bool))) := by
    rw [hS]
    ext x
    constructor
    · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
      exact ⟨reals v, (realify_emb e v).symm⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨v, rfl⟩ := reals_surjective y
      exact ⟨_, ⟨v, rfl⟩, realify_emb e v⟩
  rw [lieE, h, Submodule.span_eq]

def lieIso {e : ι → Fin s × Fin s} (he : Function.Injective e) {S : Set (Matrix (Fin s) (Fin s) ℂ)}
    (hS : lieOf S = Set.range (emb e)) : EuclideanSpace ℝ (ι ⊕ ι) ≃ₗᵢ[ℝ] lieE S :=
  (JIso he).equivRange.trans (LinearIsometryEquiv.ofEq _ _ (lieE_eq_range he hS).symm)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lieIso_coe {e : ι → Fin s × Fin s} (he : Function.Injective e) {S : Set (Matrix (Fin s) (Fin s) ℂ)}
    (hS : lieOf S = Set.range (emb e)) (y : EuclideanSpace ℝ (ι ⊕ ι)) :
    ((lieIso he hS y : lieE S) : EuclideanSpace ℝ (Fin s × Fin s × Bool)) = JLin e y := rfl

/- English proof (translation)
Rewrite using `[← (lieIso he hS).toLinearEquiv.finrank_eq, finrank_euclideanSpace, Fintype.card_sum]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem finrank_lieE {e : ι → Fin s × Fin s} (he : Function.Injective e) {S : Set (Matrix (Fin s) (Fin s) ℂ)}
    (hS : lieOf S = Set.range (emb e)) : Module.finrank ℝ (lieE S) = 2 * Fintype.card ι := by
  rw [← (lieIso he hS).toLinearEquiv.finrank_eq, finrank_euclideanSpace, Fintype.card_sum]
  ring

/- English proof (translation)
Establish `hΨ : MeasurePreserving (fun v : ι → ℂ => lieIso he hS (reals v)) volume volume` using `(lieIso he hS).measurePreserving.comp mp_reals`. Establish `hG' : Measurable (fun x : lieE S => G (x : EuclideanSpace ℝ (Fin s × Fin s × Bool)))` using `hG.comp measurable_subtype_coe`. Rewrite using `[← hΨ.map_eq, Measure.map_map hG' hΨ.measurable]`. Both sides reduce to the same expression.
-/
theorem map_lieE {e : ι → Fin s × Fin s} (he : Function.Injective e) {S : Set (Matrix (Fin s) (Fin s) ℂ)}
    (hS : lieOf S = Set.range (emb e)) {Y : Type*} [MeasurableSpace Y]
    (G : EuclideanSpace ℝ (Fin s × Fin s × Bool) → Y) (hG : Measurable G) :
    Measure.map (fun x : lieE S => G (x : EuclideanSpace ℝ (Fin s × Fin s × Bool))) volume =
      Measure.map (fun v : ι → ℂ => G (JLin e (reals v))) volume := by
  have hΨ : MeasurePreserving (fun v : ι → ℂ => lieIso he hS (reals v)) volume volume :=
    (lieIso he hS).measurePreserving.comp mp_reals
  have hG' : Measurable (fun x : lieE S => G (x : EuclideanSpace ℝ (Fin s × Fin s × Bool))) :=
    hG.comp measurable_subtype_coe
  rw [← hΨ.map_eq, Measure.map_map hG' hΨ.measurable]
  rfl

end Formalism.MainNotions.InterlacingSignCuts.Gm

end

end PartAGs2

section PartAGs3

open MeasureTheory Matrix

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts.Gm

open Formalism.MainNotions.S Formalism.MainNotions.S.UnitaryLevelOperators Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P

/- English proof (translation)
Use `letI : SeminormedRing (Matrix (Fin d) (Fin d) ℂ) := Matrix.linftyOpSemiNormedRing`. Use `letI : NormedRing (Matrix (Fin d) (Fin d) ℂ) := Matrix.linftyOpNormedRing`. Use `letI : NormedAlgebra ℝ (Matrix (Fin d) (Fin d) ℂ) := Matrix.linftyOpNormedAlgebra`. Establish `h1 : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • X)) (NormedSpace.exp ((0 : ℝ) • X) * X) 0` using `hasDerivAt_exp_smul_const X 0`. Set `L : Matrix (Fin d) (Fin d) ℂ →L[ℝ] ℂ` to `LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)`.

Establish `h2` using `L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1`. Establish `h3 : (L ∘ fun u : ℝ => NormedSpace.exp (u • X)) = fun _ => c`. Use function extensionality and compare the values at `u`. Establish `hu : (u • X) = ((u : ℂ) • X)` using `by ext a b; simp`. Simplify using `only [Function.comp, hu]`.

Conclude with `h u`. Rewrite `h2` using `[h3]`. Establish `h4` using `h2.unique (hasDerivAt_const (0 : ℝ) c)`. Establish `h5 : (NormedSpace.exp ((0 : ℝ) • X) * X) i j = 0` using `h4`. Simplify using `using h5`.
-/
theorem entry_zero_of_const {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) (c : ℂ)
    (h : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) i j = c) : X i j = 0 := by
  letI : SeminormedRing (Matrix (Fin d) (Fin d) ℂ) := Matrix.linftyOpSemiNormedRing
  letI : NormedRing (Matrix (Fin d) (Fin d) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin d) (Fin d) ℂ) := Matrix.linftyOpNormedAlgebra
  have h1 : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • X)) (NormedSpace.exp ((0 : ℝ) • X) * X) 0 :=
    hasDerivAt_exp_smul_const X 0
  let L : Matrix (Fin d) (Fin d) ℂ →L[ℝ] ℂ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)
  have h2 := L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  have h3 : (L ∘ fun u : ℝ => NormedSpace.exp (u • X)) = fun _ => c := by
    funext u
    have hu : (u • X) = ((u : ℂ) • X) := by ext a b; simp
    simp only [Function.comp, hu]
    exact h u
  rw [h3] at h2
  have h4 := h2.unique (hasDerivAt_const (0 : ℝ) c)
  have h5 : (NormedSpace.exp ((0 : ℝ) • X) * X) i j = 0 := h4
  simpa using h5

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `by_cases h : i < j <;> simp [strictUpper, h]`.
-/
theorem strictUpper_smul {d : ℕ} (a : ℂ) (v : UT d → ℂ) : a • strictUpper v = strictUpper (a • v) := by
  ext i j
  by_cases h : i < j <;> simp [strictUpper, h]

/- English proof (translation)
Use extensionality with `i j`. Distinguish the cases in `h : i < j`. Simplify using `[strictUpper, coordU, h]`. Simplify using `[strictUpper, h, hX i j (not_lt.1 h)]`.
-/
theorem strictUpper_coordU {d : ℕ} {X : Matrix (Fin d) (Fin d) ℂ} (hX : IsStrictUpper X) : strictUpper (coordU X) = X := by
  ext i j
  by_cases h : i < j
  · simp [strictUpper, coordU, h]
  · simp [strictUpper, h, hX i j (not_lt.1 h)]

section ExpCont

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/- English proof (translation)
The claim follows from `NormedSpace.exp_continuous.comp (continuous_unrealify d)`.
-/
theorem continuous_expM (d : ℕ) :
    Continuous fun x : EuclideanSpace ℝ (Fin d × Fin d × Bool) => NormedSpace.exp (unrealify x) :=
  NormedSpace.exp_continuous.comp (continuous_unrealify d)

end ExpCont

/- English proof (translation)
Use `Continuous.measurable ?_` and prove the remaining obligations. Conclude with `continuous_expM d`.
-/
theorem measurable_expE (d : ℕ) : Measurable (fun x : EuclideanSpace ℝ (Fin d × Fin d × Bool) =>
    (fun i j => NormedSpace.exp (unrealify x) i j : Msq d)) := by
  refine Continuous.measurable ?_
  exact continuous_expM d

def eL (d : ℕ) : UT d → Fin d × Fin d := Subtype.val

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [emb, strictUpper, Matrix.of_apply]`. Distinguish the cases in `h : i < j`. Rewrite using `[dif_pos h, Finset.sum_eq_single (⟨(i, j), h⟩ : UT d)]`. Conclude with `if_pos rfl`.

Introduce `b _ hb`. Conclude with `if_neg fun e => hb (Subtype.ext e)`. Introduce `hh`. Conclude with `absurd (Finset.mem_univ _) hh`. Rewrite using `[dif_neg h]`.

Use `Finset.sum_eq_zero fun k _ => if_neg fun e => h ?_` and prove the remaining obligations. Establish `hk : (eL d k).1 < (eL d k).2` using `k.2`. Rewrite `hk` using `[e]`. Conclude with `hk`.
-/
theorem emb_eL {d : ℕ} (v : UT d → ℂ) : emb (eL d) v = strictUpper v := by
  ext i j
  simp only [emb, strictUpper, Matrix.of_apply]
  by_cases h : i < j
  · rw [dif_pos h, Finset.sum_eq_single (⟨(i, j), h⟩ : UT d)]
    · exact if_pos rfl
    · intro b _ hb
      exact if_neg fun e => hb (Subtype.ext e)
    · intro hh; exact absurd (Finset.mem_univ _) hh
  · rw [dif_neg h]
    refine Finset.sum_eq_zero fun k _ => if_neg fun e => h ?_
    have hk : (eL d k).1 < (eL d k).2 := k.2
    rw [e] at hk
    exact hk

/- English proof (translation)
Use extensionality with `X`. Prove the components needed by the constructor for the conclusion. Introduce `hX`. Establish `hs : IsStrictUpper X`. Introduce `i j hij`.

Break down `hij.lt_or_eq with h | h` into its components or cases. Conclude with `entry_zero_of_const X i j 0 fun t => ((hX t).1 i j).1 h`. Conclude with `entry_zero_of_const X i j 1 fun t => ((hX t).1 i j).2 h.symm`. Conclude with `⟨coordU X, by rw [emb_eL, strictUpper_coordU hs]⟩`. Introduce and unpack `⟨v, rfl⟩ t`.

Rewrite using `[emb_eL, strictUpper_smul]`. Conclude with `stabU_long z hz _ (upperUni_exp (SUk_strictUpper _))`.
-/
theorem lie_long (d : ℕ) (z : ℂ) (hz : z ≠ 0) : lieOf (stabU (gZW d z)) = Set.range (emb (eL d)) := by
  ext X
  constructor
  · intro hX
    have hs : IsStrictUpper X := by
      intro i j hij
      rcases hij.lt_or_eq with h | h
      · exact entry_zero_of_const X i j 0 fun t => ((hX t).1 i j).1 h
      · exact entry_zero_of_const X i j 1 fun t => ((hX t).1 i j).2 h.symm
    exact ⟨coordU X, by rw [emb_eL, strictUpper_coordU hs]⟩
  · rintro ⟨v, rfl⟩ t
    rw [emb_eL, strictUpper_smul]
    exact stabU_long z hz _ (upperUni_exp (SUk_strictUpper _))

/- English proof (translation)
Introduce `d β z _ hz`. Unfold `muStab`. Rewrite using `[finrank_lieE (e := eL d) Subtype.val_injective (lie_long d z hz), Nat.mul_div_cancel_left _ (by norm_num : 0 < 2), map_lieE (e := eL d) Subtype.val_injective (lie_long d z hz) _ (measurable_expE d)]`. Simplify using `only [unrealify_J, emb_eL]`. Rewrite using `[← Measure.map_smul, sd_smul_volume]`.

Establish `he : (fun v : UT d → ℂ => (fun i j => NormedSpace.exp (strictUpper v) i j : Msq d)) = iU ∘ expU d`. Use function extensionality and compare the values at `v`. Simplify using `only [Function.comp, iU, upper_expU]`. Both sides reduce to the same expression. Rewrite using `[he, ← Measure.map_map (continuous_iU d).measurable (continuous_expU d).measurable, (mp_expU β d).map_eq]`.
-/
theorem stabMeasLong : StabMeasLong := by
  intro d β z _ hz
  unfold muStab
  rw [finrank_lieE (e := eL d) Subtype.val_injective (lie_long d z hz), Nat.mul_div_cancel_left _ (by norm_num : 0 < 2),
    map_lieE (e := eL d) Subtype.val_injective (lie_long d z hz) _ (measurable_expE d)]
  simp only [unrealify_J, emb_eL]
  rw [← Measure.map_smul, sd_smul_volume]
  have he : (fun v : UT d → ℂ => (fun i j => NormedSpace.exp (strictUpper v) i j : Msq d)) = iU ∘ expU d := by
    funext v
    simp only [Function.comp, iU, upper_expU]
    rfl
  rw [he, ← Measure.map_map (continuous_iU d).measurable (continuous_expU d).measurable, (mp_expU β d).map_eq]

def eB (n : ℕ) : UT n → Fin (n + 1) × Fin (n + 1) := fun p => (p.1.1.castSucc, p.1.2.castSucc)

/- English proof (translation)
Introduce `p q h`. Unfold `eB at h`. Rewrite `h` using `[Prod.mk.injEq, Fin.castSucc_inj, Fin.castSucc_inj]`. Conclude with `Subtype.ext (Prod.ext h.1 h.2)`.
-/
theorem eB_injective (n : ℕ) : Function.Injective (eB n) := by
  intro p q h
  unfold eB at h
  rw [Prod.mk.injEq, Fin.castSucc_inj, Fin.castSucc_inj] at h
  exact Subtype.ext (Prod.ext h.1 h.2)

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [emb]`. Proceed by induction on `i using Fin.lastCases with`. Consider the case `last`. Establish `h0 : blk (strictUpper v) 0 0 0 (Fin.last n) j = 0`.

Apply the tactic sequence `induction j using Fin.lastCases <;> simp [G5.blk_lc, G5.blk_ll]`. Rewrite using `[h0]`. Conclude with `Finset.sum_eq_zero fun k _ => if_neg fun e => (Fin.castSucc_lt_last k.1.1).ne (congrArg Prod.fst e)`. Consider the case `cast i`. Proceed by induction on `j using Fin.lastCases with`.

Consider the case `last`. Rewrite using `[G5.blk_cl]`. Conclude with `Finset.sum_eq_zero fun k _ => if_neg fun e => (Fin.castSucc_lt_last k.1.2).ne (congrArg Prod.snd e)`. Consider the case `cast j`. Rewrite using `[G5.blk_cc, ← emb_eL]`.

Simplify using `only [emb]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Establish `: (eB n k = (i.castSucc, j.castSucc)) ↔ (eL n k = (i, j))`. Prove the components needed by the constructor for the conclusion. Introduce `e`.

Conclude with `Prod.ext (Fin.castSucc_injective _ (congrArg Prod.fst e)) (Fin.castSucc_injective _ (congrArg Prod.snd e))`. Introduce `e`. Establish `e1 : k.1.1 = i` using `congrArg Prod.fst e`. Establish `e2 : k.1.2 = j` using `congrArg Prod.snd e`. Use `show (k.1.1.castSucc, k.1.2.castSucc) = _`.

Rewrite using `[e1, e2]`. Conclude with `if_congr this rfl rfl`.
-/
theorem emb_eB {n : ℕ} (v : UT n → ℂ) : emb (eB n) v = blk (strictUpper v) 0 0 0 := by
  ext i j
  simp only [emb]
  induction i using Fin.lastCases with
  | last =>
    have h0 : blk (strictUpper v) 0 0 0 (Fin.last n) j = 0 := by
      induction j using Fin.lastCases <;> simp [G5.blk_lc, G5.blk_ll]
    rw [h0]
    exact Finset.sum_eq_zero fun k _ => if_neg fun e => (Fin.castSucc_lt_last k.1.1).ne (congrArg Prod.fst e)
  | cast i =>
    induction j using Fin.lastCases with
    | last =>
      rw [G5.blk_cl]
      exact Finset.sum_eq_zero fun k _ => if_neg fun e => (Fin.castSucc_lt_last k.1.2).ne (congrArg Prod.snd e)
    | cast j =>
      rw [G5.blk_cc, ← emb_eL]
      simp only [emb]
      refine Finset.sum_congr rfl fun k _ => ?_
      have : (eB n k = (i.castSucc, j.castSucc)) ↔ (eL n k = (i, j)) := by
        constructor
        · intro e
          exact Prod.ext (Fin.castSucc_injective _ (congrArg Prod.fst e)) (Fin.castSucc_injective _ (congrArg Prod.snd e))
        · intro e
          have e1 : k.1.1 = i := congrArg Prod.fst e
          have e2 : k.1.2 = j := congrArg Prod.snd e
          show (k.1.1.castSucc, k.1.2.castSucc) = _
          rw [e1, e2]
      exact if_congr this rfl rfl

/- English proof (translation)
Use `⟨(isUpUni_iff _).2 ((G4.upperUni_blk_iff _ _ _ _).2 ⟨hk, rfl, rfl⟩), (isLoUni_iff _).2 ?_⟩` and prove the remaining obligations. Rewrite using `[gTC_eq, of_toM, ← G4.upper_coordU hk, conjB n t c ht hc, G4.lowerUni_blk_iff]`. Conclude with `⟨G4.lowerUni_conj (G4.upperUni_inv (G4.upperUni_upper _)), rfl, rfl⟩`.
-/
theorem stabU_block (n : ℕ) (t c : ℂ) (ht : t ≠ 0) (hc : c ≠ 0) (k : Matrix (Fin n) (Fin n) ℂ) (hk : IsUpperUni k) :
    blk k 0 0 1 ∈ stabU (gTC (n + 1) t c) := by
  refine ⟨(isUpUni_iff _).2 ((G4.upperUni_blk_iff _ _ _ _).2 ⟨hk, rfl, rfl⟩), (isLoUni_iff _).2 ?_⟩
  rw [gTC_eq, of_toM, ← G4.upper_coordU hk, conjB n t c ht hc, G4.lowerUni_blk_iff]
  exact ⟨G4.lowerUni_conj (G4.upperUni_inv (G4.upperUni_upper _)), rfl, rfl⟩

/- English proof (translation)
Take `⟨h1, h2⟩` from `hu`. Rewrite `h2` using `[gTC_eq, of_toM]`. Establish `hU` using `(isUpUni_iff _).1 h1`. Establish `hL` using `(isLoUni_iff _).1 h2`. Establish `hdet : IsUnit u.det` using `by rw [G4.upperUni_det hU]; exact isUnit_one`.

Establish `hfix : ptBlock n t c * u⁻¹ * (ptBlock n t c)⁻¹ * ptBlock n t c * u = ptBlock n t c`. Rewrite using `[Matrix.mul_assoc (ptBlock n t c * u⁻¹), ptBlock_inv_mul n t c ht hc, Matrix.mul_one, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.mul_one]`. Take `⟨k, hk, hku, -⟩` from `((Formalism.FourierDecayAlt.P.stabilizer_block_point n t c ht _ u hL hU).1).1 hfix`. Conclude with `⟨k, hk, hku⟩`.
-/
theorem stabU_block_form (n : ℕ) (t c : ℂ) (ht : t ≠ 0) (hc : c ≠ 0) (u : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hu : u ∈ stabU (gTC (n + 1) t c)) : ∃ k : Matrix (Fin n) (Fin n) ℂ, IsUpperUni k ∧ u = blk k 0 0 1 := by
  obtain ⟨h1, h2⟩ := hu
  rw [gTC_eq, of_toM] at h2
  have hU := (isUpUni_iff _).1 h1
  have hL := (isLoUni_iff _).1 h2
  have hdet : IsUnit u.det := by rw [G4.upperUni_det hU]; exact isUnit_one
  have hfix : ptBlock n t c * u⁻¹ * (ptBlock n t c)⁻¹ * ptBlock n t c * u = ptBlock n t c := by
    rw [Matrix.mul_assoc (ptBlock n t c * u⁻¹), ptBlock_inv_mul n t c ht hc, Matrix.mul_one, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hdet, Matrix.mul_one]
  obtain ⟨k, hk, hku, -⟩ := ((Formalism.FourierDecayAlt.P.stabilizer_block_point n t c ht _ u hL hU).1).1 hfix
  exact ⟨k, hk, hku⟩

/- English proof (translation)
Use extensionality with `X`. Prove the components needed by the constructor for the conclusion. Introduce `hX`. Establish `hform : ∀ τ : ℝ, ∃ k : Matrix (Fin n) (Fin n) ℂ, IsUpperUni k ∧ NormedSpace.exp ((τ : ℂ) • X) = blk k 0 0 1` using `fun τ => stabU_block_form n t c ht hc _ (hX τ)`. Establish `hcl : ∀ i : Fin n, X i.castSucc (Fin.last n) = 0` using `fun i => entry_zero_of_const X _ _ 0 fun τ => by`.

Take `⟨k, _, hk⟩` from `hform τ`. Rewrite using `[hk, G5.blk_cl]`. Both sides reduce to the same expression. Establish `hlc : ∀ j : Fin n, X (Fin.last n) j.castSucc = 0` using `fun j => entry_zero_of_const X _ _ 0 fun τ => by`. Take `⟨k, _, hk⟩` from `hform τ`.

Rewrite using `[hk, G5.blk_lc]`. Both sides reduce to the same expression. Establish `hll : X (Fin.last n) (Fin.last n) = 0` using `entry_zero_of_const X _ _ 1 fun τ => by`. Take `⟨k, _, hk⟩` from `hform τ`. Rewrite using `[hk, G5.blk_ll]`.

Establish `hcc : IsStrictUpper (Matrix.of fun i j : Fin n => X i.castSucc j.castSucc)`. Introduce `i j hij`. Break down `hij.lt_or_eq with h | h` into its components or cases. Conclude with `entry_zero_of_const X _ _ 0 fun τ => by`. Take `⟨k, hk1, hk⟩` from `hform τ`.

Rewrite using `[hk, G5.blk_cc]`. Conclude with `hk1.2 i j h`. Substitute `h` using the available equality. Conclude with `entry_zero_of_const X _ _ 1 fun τ => by`. Take `⟨k, hk1, hk⟩` from `hform τ`.

Rewrite using `[hk, G5.blk_cc]`. Conclude with `hk1.1 _`. Use `⟨coordU (Matrix.of fun i j : Fin n => X i.castSucc j.castSucc), ?_⟩` and prove the remaining obligations. Rewrite using `[emb_eB, strictUpper_coordU hcc]`. Use extensionality with `i j`.

Apply the tactic sequence `induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>`. Simplify using `[G5.blk_cc, G5.blk_cl, G5.blk_lc, G5.blk_ll, hcl, hlc, hll]`. Introduce and unpack `⟨v, rfl⟩ τ`. Rewrite using `[emb_eB, blk_smul, strictUpper_smul]`. Simplify using `only [smul_zero, mul_zero]`.

Rewrite using `[exp_blk (SUk_strictUpper _), Matrix.mulVec_zero]`. Conclude with `stabU_block n t c ht hc _ (upperUni_exp (SUk_strictUpper _))`.
-/
theorem lie_block (n : ℕ) (t c : ℂ) (ht : t ≠ 0) (hc : c ≠ 0) :
    lieOf (stabU (gTC (n + 1) t c)) = Set.range (emb (eB n)) := by
  ext X
  constructor
  · intro hX
    have hform : ∀ τ : ℝ, ∃ k : Matrix (Fin n) (Fin n) ℂ, IsUpperUni k ∧ NormedSpace.exp ((τ : ℂ) • X) = blk k 0 0 1 :=
      fun τ => stabU_block_form n t c ht hc _ (hX τ)

    have hcl : ∀ i : Fin n, X i.castSucc (Fin.last n) = 0 := fun i =>
      entry_zero_of_const X _ _ 0 fun τ => by
        obtain ⟨k, _, hk⟩ := hform τ
        rw [hk, G5.blk_cl]; rfl
    have hlc : ∀ j : Fin n, X (Fin.last n) j.castSucc = 0 := fun j =>
      entry_zero_of_const X _ _ 0 fun τ => by
        obtain ⟨k, _, hk⟩ := hform τ
        rw [hk, G5.blk_lc]; rfl
    have hll : X (Fin.last n) (Fin.last n) = 0 :=
      entry_zero_of_const X _ _ 1 fun τ => by
        obtain ⟨k, _, hk⟩ := hform τ
        rw [hk, G5.blk_ll]
    have hcc : IsStrictUpper (Matrix.of fun i j : Fin n => X i.castSucc j.castSucc) := by
      intro i j hij
      rcases hij.lt_or_eq with h | h
      · exact entry_zero_of_const X _ _ 0 fun τ => by
          obtain ⟨k, hk1, hk⟩ := hform τ
          rw [hk, G5.blk_cc]; exact hk1.2 i j h
      · subst h
        exact entry_zero_of_const X _ _ 1 fun τ => by
          obtain ⟨k, hk1, hk⟩ := hform τ
          rw [hk, G5.blk_cc]; exact hk1.1 _
    refine ⟨coordU (Matrix.of fun i j : Fin n => X i.castSucc j.castSucc), ?_⟩
    rw [emb_eB, strictUpper_coordU hcc]
    ext i j
    induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
      simp [G5.blk_cc, G5.blk_cl, G5.blk_lc, G5.blk_ll, hcl, hlc, hll]
  · rintro ⟨v, rfl⟩ τ
    rw [emb_eB, blk_smul, strictUpper_smul]
    simp only [smul_zero, mul_zero]
    rw [exp_blk (SUk_strictUpper _), Matrix.mulVec_zero]
    exact stabU_block n t c ht hc _ (upperUni_exp (SUk_strictUpper _))

/- English proof (translation)
Introduce `n β t c _ ht hc`. Unfold `muStab`. Rewrite using `[finrank_lieE (eB_injective n) (lie_block n t c ht hc), Nat.mul_div_cancel_left _ (by norm_num : 0 < 2), map_lieE (eB_injective n) (lie_block n t c ht hc) _ (measurable_expE (n + 1))]`. Simplify using `only [unrealify_J, emb_eB]`. Rewrite using `[← Measure.map_smul, sd_smul_volume]`.

Establish `he : (fun v : UT n → ℂ => (fun i j => NormedSpace.exp (blk (strictUpper v) 0 0 0) i j : Msq (n + 1))) = kapB ∘ expU n`. Use function extensionality and compare the values at `v`. Simplify using `only [Function.comp, kapB, upper_expU]`. Rewrite using `[exp_blk (SUk_strictUpper v), Matrix.mulVec_zero]`. Both sides reduce to the same expression.

Rewrite using `[he, ← Measure.map_map (kapB_emb n).measurable (continuous_expU n).measurable, (mp_expU β n).map_eq]`.
-/
theorem stabMeasBlock : StabMeasBlock := by
  intro n β t c _ ht hc
  unfold muStab
  rw [finrank_lieE (eB_injective n) (lie_block n t c ht hc), Nat.mul_div_cancel_left _ (by norm_num : 0 < 2),
    map_lieE (eB_injective n) (lie_block n t c ht hc) _ (measurable_expE (n + 1))]
  simp only [unrealify_J, emb_eB]
  rw [← Measure.map_smul, sd_smul_volume]
  have he : (fun v : UT n → ℂ => (fun i j => NormedSpace.exp (blk (strictUpper v) 0 0 0) i j : Msq (n + 1))) =
      kapB ∘ expU n := by
    funext v
    simp only [Function.comp, kapB, upper_expU]
    rw [exp_blk (SUk_strictUpper v), Matrix.mulVec_zero]
    rfl
  rw [he, ← Measure.map_map (kapB_emb n).measurable (continuous_expU n).measurable, (mp_expU β n).map_eq]

end Formalism.MainNotions.InterlacingSignCuts.Gm

end

end PartAGs3

section PartAGs

namespace Formalism.MainNotions.InterlacingSignCuts.Gm

open Formalism.FourierDecayAlt.G Formalism.MainNotions.S.UnitaryLevelOperators

/- English proof (translation)
The claim follows from `orbCoordC stabMeasBlock stabMeasLong C₁ C₂ h1 h2`.
-/
theorem orbCoordC' (C₁ C₂ : ℝ) (h1 : 0 ≤ C₁) (h2 : 1 ≤ C₂) : OrbCoordC C₁ C₂ :=
  orbCoordC stabMeasBlock stabMeasLong C₁ C₂ h1 h2

/- English proof (translation)
The claim follows from `stGerm_of_core stabMeasBlock stabMeasLong hG`.
-/
theorem stGerm_of_core' (hG : Germ) : ∃ C : ℝ, ∀ C₁ ≥ C, ∀ C₂ ≥ C, stGerm C₁ C₂ :=
  stGerm_of_core stabMeasBlock stabMeasLong hG

/- English proof (translation)
The claim follows from `stGerm_of_rate stabMeasBlock stabMeasLong hR`.
-/
theorem stGerm_of_rate' (hR : GermRate) : ∃ C : ℝ, ∀ C₁ ≥ C, ∀ C₂ ≥ C, stGerm C₁ C₂ :=
  stGerm_of_rate stabMeasBlock stabMeasLong hR

/- English proof (translation)
Take `⟨C, h⟩` from `stGerm_of_rate' hR`. Conclude with `⟨C, fun C₁ h1 C₂ h2 _ => h C₁ h1 C₂ h2⟩`.
-/
theorem valuation_stationary_phase_of_germ_rate (hR : GermRate) :
    ∃ C : ℝ, ∀ C₁ ≥ C, ∀ C₂ ≥ C, ∀ D : Formalism.BasicNotions.D7, Formalism.MainNotions.RadialChainStatements.adm17 D C₁ C₂ := by
  obtain ⟨C, h⟩ := stGerm_of_rate' hR
  exact ⟨C, fun C₁ h1 C₂ h2 _ => h C₁ h1 C₂ h2⟩

/- English proof (translation)
Take `⟨C, h⟩` from `stGerm_of_rate' hR`. Conclude with `⟨C, fun C₁ h1 C₂ h2 _ => h C₁ h1 C₂ h2⟩`.
-/
theorem germ_stationary_phase_of_germ_rate (hR : GermRate) :
    ∃ C : ℝ, ∀ C₁ ≥ C, ∀ C₂ ≥ C, ∀ D : Formalism.BasicNotions.D7, Formalism.MainNotions.BlockEstimateTheorem.adm17 D C₁ C₂ := by
  obtain ⟨C, h⟩ := stGerm_of_rate' hR
  exact ⟨C, fun C₁ h1 C₂ h2 _ => h C₁ h1 C₂ h2⟩

end Formalism.MainNotions.InterlacingSignCuts.Gm

end PartAGs

section PartAPk

open Polynomial

namespace Formalism.MainNotions.InterlacingSignCuts

def VMarkovMid : Prop :=
  ∀ n k : ℕ, 2 ≤ k → k + 2 ≤ n → ∀ p : ℝ[X], p.natDegree ≤ n → ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
    |(derivative^[k] p).eval x| ≤ vmC n k * supN p

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h n k hk2 hkn p hp x hx`. Conclude with `(stMarkov_iff.1 h) n k (by omega) p hp x (Set.Ioo_subset_Icc_self hx)`. Introduce `h`. Conclude with `stMarkov_of_mid h`.
-/
theorem stMarkov_iff_mid : Formalism.MainNotions.S.UnitaryLevelOperators.stMarkov ↔ VMarkovMid := by
  constructor
  · intro h n k hk2 hkn p hp x hx
    exact (stMarkov_iff.1 h) n k (by omega) p hp x (Set.Ioo_subset_Icc_self hx)
  · intro h
    exact stMarkov_of_mid h

/- English proof (translation)
The claim follows from `stOm_of_core _ _ _ _ h.1 h.2.1 h.2.2.1 h.2.2.2.1`.
-/
theorem stOm_of_Std (Lt : Formalism.MainNotions.S.TopsChoicePartA.Lev) (h : Lt.Std) : Formalism.MainNotions.S.UnitaryLevelOperators.stOm (Lt.k0 + 1) Lt.r Lt.z Lt.z' :=
  stOm_of_core _ _ _ _ h.1 h.2.1 h.2.2.1 h.2.2.2.1

/- English proof (translation)
Use `first`. Consider the case `exact stA_signs_of_core`. Consider the case `exact stLetters_of_core`. Consider the case `exact stWaveLetters_of_core`. Consider the case `exact stThLog_of_core`.

Consider the case `exact pointwise_integration_by_parts`. Consider the case `exact ⟨stThLog_of_core, pointwise_integration_by_parts⟩`. Consider the case `exact ⟨stLetters_of_core, stWaveLetters_of_core⟩`. Consider the case `exact stHerglotz_of_core`. Consider the case `exact stPoisson_of_core`.

Consider the case `exact stStatPhase_of_core`.
-/
theorem valuation_third_clause_of_known (D : Formalism.BasicNotions.D7) : RadialChainStatements.IntegralityRemainder D := by
  first
    | exact stA_signs_of_core
    | exact stLetters_of_core
    | exact stWaveLetters_of_core
    | exact stThLog_of_core
    | exact pointwise_integration_by_parts
    | exact ⟨stThLog_of_core, pointwise_integration_by_parts⟩
    | exact ⟨stLetters_of_core, stWaveLetters_of_core⟩
    | exact stHerglotz_of_core
    | exact stPoisson_of_core
    | exact stStatPhase_of_core
/- English proof (translation)
Use `first`. Consider the case `exact stA_signs_of_core`. Consider the case `exact stLetters_of_core`. Consider the case `exact stWaveLetters_of_core`. Consider the case `exact stThLog_of_core`.

Consider the case `exact pointwise_integration_by_parts`. Consider the case `exact ⟨stThLog_of_core, pointwise_integration_by_parts⟩`. Consider the case `exact ⟨stLetters_of_core, stWaveLetters_of_core⟩`. Consider the case `exact stHerglotz_of_core`. Consider the case `exact stPoisson_of_core`.

Consider the case `exact stStatPhase_of_core`.
-/
theorem valuation_fourth_clause_of_known (D : Formalism.BasicNotions.D7) : RadialChainStatements.ArithmeticRiemannRochThetaCond D := by
  first
    | exact stA_signs_of_core
    | exact stLetters_of_core
    | exact stWaveLetters_of_core
    | exact stThLog_of_core
    | exact pointwise_integration_by_parts
    | exact ⟨stThLog_of_core, pointwise_integration_by_parts⟩
    | exact ⟨stLetters_of_core, stWaveLetters_of_core⟩
    | exact stHerglotz_of_core
    | exact stPoisson_of_core
    | exact stStatPhase_of_core
/- English proof (translation)
Use `first`. Consider the case `exact stA_signs_of_core`. Consider the case `exact stLetters_of_core`. Consider the case `exact stWaveLetters_of_core`. Consider the case `exact stThLog_of_core`.

Consider the case `exact pointwise_integration_by_parts`. Consider the case `exact ⟨stThLog_of_core, pointwise_integration_by_parts⟩`. Consider the case `exact ⟨stLetters_of_core, stWaveLetters_of_core⟩`. Consider the case `exact stHerglotz_of_core`. Consider the case `exact stPoisson_of_core`.

Consider the case `exact stStatPhase_of_core`.
-/
theorem valuation_integration_by_parts_of_known (D : Formalism.BasicNotions.D7) : RadialChainStatements.IntegrationByPartsAlt D := by
  first
    | exact stA_signs_of_core
    | exact stLetters_of_core
    | exact stWaveLetters_of_core
    | exact stThLog_of_core
    | exact pointwise_integration_by_parts
    | exact ⟨stThLog_of_core, pointwise_integration_by_parts⟩
    | exact ⟨stLetters_of_core, stWaveLetters_of_core⟩
    | exact stHerglotz_of_core
    | exact stPoisson_of_core
    | exact stStatPhase_of_core
/- English proof (translation)
Use `first`. Consider the case `exact stA_signs_of_core`. Consider the case `exact stLetters_of_core`. Consider the case `exact stWaveLetters_of_core`. Consider the case `exact stThLog_of_core`.

Consider the case `exact pointwise_integration_by_parts`. Consider the case `exact ⟨stThLog_of_core, pointwise_integration_by_parts⟩`. Consider the case `exact ⟨stLetters_of_core, stWaveLetters_of_core⟩`. Consider the case `exact stHerglotz_of_core`. Consider the case `exact stPoisson_of_core`.

Consider the case `exact stStatPhase_of_core`.
-/
theorem valuation_theta_log_of_known (D : Formalism.BasicNotions.D7) : RadialChainStatements.LogThetaIdentity D := by
  first
    | exact stA_signs_of_core
    | exact stLetters_of_core
    | exact stWaveLetters_of_core
    | exact stThLog_of_core
    | exact pointwise_integration_by_parts
    | exact ⟨stThLog_of_core, pointwise_integration_by_parts⟩
    | exact ⟨stLetters_of_core, stWaveLetters_of_core⟩
    | exact stHerglotz_of_core
    | exact stPoisson_of_core
    | exact stStatPhase_of_core
/- English proof (translation)
Assemble the required witnesses or components as `⟨pointwise_integration_by_parts, stThLog_of_core⟩`.
-/
theorem valuation_ibp_and_theta_log_of_known (D : Formalism.BasicNotions.D7) : RadialChainStatements.adm9 D := ⟨pointwise_integration_by_parts, stThLog_of_core⟩
/- English proof (translation)
The claim follows from `stWaveLetters_of_core`.
-/
theorem valuation_wave_letters_of_known (D : Formalism.BasicNotions.D7) : RadialChainStatements.PlaneWaveLetters D := stWaveLetters_of_core
/- English proof (translation)
The claim follows from `stMarkov_of_mid h`.
-/
theorem valuation_markov_of_middle_bound (D : Formalism.BasicNotions.D7) (h : VMarkovMid) : RadialChainStatements.adm14 D := stMarkov_of_mid h
/- English proof (translation)
Use `first`. Consider the case `exact stA_signs_of_core`. Consider the case `exact stLetters_of_core`. Consider the case `exact stWaveLetters_of_core`. Consider the case `exact stThLog_of_core`.

Consider the case `exact pointwise_integration_by_parts`. Consider the case `exact ⟨stThLog_of_core, pointwise_integration_by_parts⟩`. Consider the case `exact ⟨stLetters_of_core, stWaveLetters_of_core⟩`. Consider the case `exact stHerglotz_of_core`. Consider the case `exact stPoisson_of_core`.

Consider the case `exact stStatPhase_of_core`.
-/
theorem valuation_herglotz_of_known (D : Formalism.BasicNotions.D7) : RadialChainStatements.adm15 D := by
  first
    | exact stA_signs_of_core
    | exact stLetters_of_core
    | exact stWaveLetters_of_core
    | exact stThLog_of_core
    | exact pointwise_integration_by_parts
    | exact ⟨stThLog_of_core, pointwise_integration_by_parts⟩
    | exact ⟨stLetters_of_core, stWaveLetters_of_core⟩
    | exact stHerglotz_of_core
    | exact stPoisson_of_core
    | exact stStatPhase_of_core
/- English proof (translation)
Use `first`. Consider the case `exact stA_signs_of_core`. Consider the case `exact stLetters_of_core`. Consider the case `exact stWaveLetters_of_core`. Consider the case `exact stThLog_of_core`.

Consider the case `exact pointwise_integration_by_parts`. Consider the case `exact ⟨stThLog_of_core, pointwise_integration_by_parts⟩`. Consider the case `exact ⟨stLetters_of_core, stWaveLetters_of_core⟩`. Consider the case `exact stHerglotz_of_core`. Consider the case `exact stPoisson_of_core`.

Consider the case `exact stStatPhase_of_core`.
-/
theorem valuation_poisson_summation_of_known (D : Formalism.BasicNotions.D7) : RadialChainStatements.adm16 D := by
  first
    | exact stA_signs_of_core
    | exact stLetters_of_core
    | exact stWaveLetters_of_core
    | exact stThLog_of_core
    | exact pointwise_integration_by_parts
    | exact ⟨stThLog_of_core, pointwise_integration_by_parts⟩
    | exact ⟨stLetters_of_core, stWaveLetters_of_core⟩
    | exact stHerglotz_of_core
    | exact stPoisson_of_core
    | exact stStatPhase_of_core
/- English proof (translation)
Introduce `_ _` and use `valuation_ibp_and_theta_log_of_known _`.
-/
theorem valuation_family_ibp_theta_of_known {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : RadialChainStatements.admF9 Fm := fun _ _ => valuation_ibp_and_theta_log_of_known _
/- English proof (translation)
Introduce `_ _` and use `valuation_herglotz_of_known _`.
-/
theorem valuation_family_herglotz_of_known {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : RadialChainStatements.FamilyFifteenthHypothesis Fm := fun _ _ => valuation_herglotz_of_known _
/- English proof (translation)
Introduce `_ _` and use `valuation_poisson_summation_of_known _`.
-/
theorem valuation_family_poisson_of_known {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : RadialChainStatements.FamilySixteenthHypothesis Fm := fun _ _ => valuation_poisson_summation_of_known _

/- English proof (translation)
The claim follows from `stA_signs_of_core`.
-/
theorem germ_third_clause_of_known (D : Formalism.BasicNotions.D7) : BlockEstimateTheorem.IntegralityRemainder D := stA_signs_of_core
/- English proof (translation)
The claim follows from `stLetters_of_core`.
-/
theorem germ_fourth_clause_of_known (D : Formalism.BasicNotions.D7) : BlockEstimateTheorem.ArithmeticRiemannRochThetaCond D := stLetters_of_core
/- English proof (translation)
The claim follows from `pointwise_integration_by_parts`.
-/
theorem germ_integration_by_parts_of_known (D : Formalism.BasicNotions.D7) : BlockEstimateTheorem.IntegrationByPartsAlt D := pointwise_integration_by_parts
/- English proof (translation)
The claim follows from `stThLog_of_core`.
-/
theorem germ_theta_log_of_known (D : Formalism.BasicNotions.D7) : BlockEstimateTheorem.LogThetaIdentity D := stThLog_of_core
/- English proof (translation)
Assemble the required witnesses or components as `⟨pointwise_integration_by_parts, stThLog_of_core⟩`.
-/
theorem germ_ibp_and_theta_log_of_known (D : Formalism.BasicNotions.D7) : BlockEstimateTheorem.adm9 D := ⟨pointwise_integration_by_parts, stThLog_of_core⟩
/- English proof (translation)
The claim follows from `stWaveLetters_of_core`.
-/
theorem germ_wave_letters_of_known (D : Formalism.BasicNotions.D7) : BlockEstimateTheorem.PlaneWaveLetters D := stWaveLetters_of_core
/- English proof (translation)
The claim follows from `stMarkov_of_mid h`.
-/
theorem germ_markov_of_middle_bound (D : Formalism.BasicNotions.D7) (h : VMarkovMid) : BlockEstimateTheorem.adm14 D := stMarkov_of_mid h
/- English proof (translation)
The claim follows from `stHerglotz_of_core`.
-/
theorem germ_herglotz_of_known (D : Formalism.BasicNotions.D7) : BlockEstimateTheorem.adm15 D := stHerglotz_of_core
/- English proof (translation)
The claim follows from `stPoisson_of_core`.
-/
theorem germ_poisson_summation_of_known (D : Formalism.BasicNotions.D7) : BlockEstimateTheorem.adm16 D := stPoisson_of_core
/- English proof (translation)
Introduce `_ _` and use `germ_ibp_and_theta_log_of_known _`.
-/
theorem germ_family_ibp_theta_of_known {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : BlockEstimateTheorem.admF9 Fm := fun _ _ => germ_ibp_and_theta_log_of_known _
/- English proof (translation)
Introduce `_ _` and use `germ_herglotz_of_known _`.
-/
theorem germ_family_herglotz_of_known {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : BlockEstimateTheorem.FamilyFifteenthHypothesis Fm := fun _ _ => germ_herglotz_of_known _
/- English proof (translation)
Introduce `_ _` and use `germ_poisson_summation_of_known _`.
-/
theorem germ_family_poisson_of_known {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : BlockEstimateTheorem.FamilySixteenthHypothesis Fm := fun _ _ => germ_poisson_summation_of_known _

/- English proof (translation)
The claim follows from `stA_signs_of_core`.
-/
theorem germ_model_third_clause_of_known (D : Formalism.BasicNotions.D7) : HereditaryPositivity.IntegralityRemainder D := stA_signs_of_core
/- English proof (translation)
The claim follows from `stLetters_of_core`.
-/
theorem germ_model_fourth_clause_of_known (D : Formalism.BasicNotions.D7) : HereditaryPositivity.ArithmeticRiemannRochThetaCond D := stLetters_of_core
/- English proof (translation)
The claim follows from `pointwise_integration_by_parts`.
-/
theorem germ_model_integration_by_parts_of_known (D : Formalism.BasicNotions.D7) : HereditaryPositivity.IntegrationByPartsAlt D := pointwise_integration_by_parts
/- English proof (translation)
The claim follows from `stThLog_of_core`.
-/
theorem germ_model_theta_log_of_known (D : Formalism.BasicNotions.D7) : HereditaryPositivity.LogThetaIdentity D := stThLog_of_core
/- English proof (translation)
Assemble the required witnesses or components as `⟨pointwise_integration_by_parts, stThLog_of_core⟩`.
-/
theorem germ_model_ibp_and_theta_log_of_known (D : Formalism.BasicNotions.D7) : HereditaryPositivity.adm9 D := ⟨pointwise_integration_by_parts, stThLog_of_core⟩
/- English proof (translation)
The claim follows from `stWaveLetters_of_core`.
-/
theorem germ_model_wave_letters_of_known (D : Formalism.BasicNotions.D7) : HereditaryPositivity.PlaneWaveLetters D := stWaveLetters_of_core
/- English proof (translation)
The claim follows from `stMarkov_of_mid h`.
-/
theorem germ_model_markov_of_middle_bound (D : Formalism.BasicNotions.D7) (h : VMarkovMid) : HereditaryPositivity.adm14 D := stMarkov_of_mid h
/- English proof (translation)
The claim follows from `stHerglotz_of_core`.
-/
theorem germ_model_herglotz_of_known (D : Formalism.BasicNotions.D7) : HereditaryPositivity.adm15 D := stHerglotz_of_core
/- English proof (translation)
The claim follows from `stPoisson_of_core`.
-/
theorem germ_model_poisson_summation_of_known (D : Formalism.BasicNotions.D7) : HereditaryPositivity.adm16 D := stPoisson_of_core
/- English proof (translation)
Introduce `_ _` and use `germ_model_ibp_and_theta_log_of_known _`.
-/
theorem germ_model_family_ibp_theta_of_known {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : HereditaryPositivity.admF9 Fm := fun _ _ => germ_model_ibp_and_theta_log_of_known _
/- English proof (translation)
Introduce `_ _` and use `germ_model_herglotz_of_known _`.
-/
theorem germ_model_family_herglotz_of_known {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : HereditaryPositivity.FamilyFifteenthHypothesis Fm := fun _ _ => germ_model_herglotz_of_known _
/- English proof (translation)
Introduce `_ _` and use `germ_model_poisson_summation_of_known _`.
-/
theorem germ_model_family_poisson_of_known {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : HereditaryPositivity.FamilySixteenthHypothesis Fm := fun _ _ => germ_model_poisson_summation_of_known _

/- English proof (translation)
The claim follows from `stA_signs_of_core`.
-/
theorem two_bound_third_clause_of_known (D : Formalism.BasicNotions.D7) : RadialRuleConsequences.IntegralityRemainder D := stA_signs_of_core
/- English proof (translation)
The claim follows from `stLetters_of_core`.
-/
theorem two_bound_fourth_clause_of_known (D : Formalism.BasicNotions.D7) : RadialRuleConsequences.ArithmeticRiemannRochThetaCond D := stLetters_of_core
/- English proof (translation)
The claim follows from `pointwise_integration_by_parts`.
-/
theorem two_bound_integration_by_parts_of_known (D : Formalism.BasicNotions.D7) : RadialRuleConsequences.IntegrationByPartsAlt D := pointwise_integration_by_parts
/- English proof (translation)
The claim follows from `stThLog_of_core`.
-/
theorem two_bound_theta_log_of_known (D : Formalism.BasicNotions.D7) : RadialRuleConsequences.LogThetaIdentity D := stThLog_of_core
/- English proof (translation)
Assemble the required witnesses or components as `⟨pointwise_integration_by_parts, stThLog_of_core⟩`.
-/
theorem two_bound_ibp_and_theta_log_of_known (D : Formalism.BasicNotions.D7) : RadialRuleConsequences.adm9 D := ⟨pointwise_integration_by_parts, stThLog_of_core⟩
/- English proof (translation)
The claim follows from `stWaveLetters_of_core`.
-/
theorem two_bound_wave_letters_of_known (D : Formalism.BasicNotions.D7) : RadialRuleConsequences.PlaneWaveLetters D := stWaveLetters_of_core
/- English proof (translation)
The claim follows from `stMarkov_of_mid h`.
-/
theorem two_bound_markov_of_middle_bound (D : Formalism.BasicNotions.D7) (h : VMarkovMid) : RadialRuleConsequences.adm14 D := stMarkov_of_mid h
/- English proof (translation)
The claim follows from `stHerglotz_of_core`.
-/
theorem two_bound_herglotz_of_known (D : Formalism.BasicNotions.D7) : RadialRuleConsequences.adm15 D := stHerglotz_of_core
/- English proof (translation)
The claim follows from `stPoisson_of_core`.
-/
theorem two_bound_poisson_summation_of_known (D : Formalism.BasicNotions.D7) : RadialRuleConsequences.adm16 D := stPoisson_of_core
/- English proof (translation)
Introduce `_ _` and use `two_bound_ibp_and_theta_log_of_known _`.
-/
theorem two_bound_family_ibp_theta_of_known {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : RadialRuleConsequences.admF9 Fm := fun _ _ => two_bound_ibp_and_theta_log_of_known _
/- English proof (translation)
Introduce `_ _` and use `two_bound_herglotz_of_known _`.
-/
theorem two_bound_family_herglotz_of_known {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : RadialRuleConsequences.FamilyFifteenthHypothesis Fm := fun _ _ => two_bound_herglotz_of_known _
/- English proof (translation)
Introduce `_ _` and use `two_bound_poisson_summation_of_known _`.
-/
theorem two_bound_family_poisson_of_known {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : RadialRuleConsequences.FamilySixteenthHypothesis Fm := fun _ _ => two_bound_poisson_summation_of_known _

end Formalism.MainNotions.InterlacingSignCuts

end PartAPk

section PartALev

open Matrix MeasureTheory TensorProduct
open scoped ContDiff
open Formalism.QuantumDeterminants Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.LevR Formalism.MainNotions.S.UnitaryLevelOperators

namespace Formalism.MainNotions.InterlacingSignCuts

def stLevelOpen (C Cv C1 C2 : ℝ) : Prop :=
  ∀ (Lt : Lev) (u u' : Fin (Lt.k0 + 1) → ℝ) (I : Set ℝ) (hr : Lt.r + 0 = Lt.r),
    HypC Lt u u' I → HypC (Lt.down Lt.r 0 hr) u u' I →
    ∀ R : ℂ → Matrix (Fin 2) (Fin 2) (Lt.down Lt.r 0 hr).POp, (Lt.down Lt.r 0 hr).IsRadQQ R →
    ∃ (h : (Fin 1 → ℂ) → Lt.Hom →L[ℂ] Lt.Hom) (SS : Fin Lt.k0 → (Fin 1 → ℂ) → Lt.Hom →L[ℂ] Lt.Hom),
      (∀ (hh : (Lt.down Lt.r 0 hr).Haar) (A : ℝ) (mm : ℕ), hh.Ok → Big C Lt 0 A mm →
        stLevR (ctxR Lt u u' I hr R ((Lt.down Lt.r 0 hr).ImgK hh A mm)) h SS) ∧
      stLev0 (ctx0 Lt u u' I hr R) (gctxOf Lt) (pullZ h) (fun l => pullZ (SS l)) ∧
      stRules (ctx0 Lt u u' I hr R) (pullZ h) (fun l => pullZ (SS l)) ∧
      stProd (ctx0 Lt u u' I hr R) Cv (pullZ h) (fun l => pullZ (SS l)) ∧
      (∀ (hh : (Lt.down Lt.r 0 hr).Haar) (A : ℝ) (mm : ℕ), hh.Ok →
        stFrameR (ctxR Lt u u' I hr R ((Lt.down Lt.r 0 hr).ImgK hh A mm)) (fun N => Big C Lt N A mm) h SS) ∧
      stFrameG (ctxR Lt u u' I hr R (Lt.down Lt.r 0 hr).Img) (ctx0 Lt u u' I hr R) (Lt.liftDown Lt.r 0 hr)
        pullZ h SS ∧
      stRes (ctxR Lt u u' I hr R (Lt.down Lt.r 0 hr).Img) C1 C2 SS

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `H Lt u u' I hr h1 h2 R hR`. Take `⟨h, SS, a, b, c, d, e, f, -, g⟩` from `H Lt u u' I hr h1 h2 R hR`. Conclude with `⟨h, SS, a, b, c, d, e, f, g⟩`. Introduce `H Lt u u' I hr h1 h2 R hR`.

Take `⟨h, SS, a, b, c, d, e, f, g⟩` from `H Lt u u' I hr h1 h2 R hR`. Conclude with `⟨h, SS, a, b, c, d, e, f, stOm_of_Std Lt h1.1, g⟩`.
-/
theorem stLevel_iff_open (C Cv C1 C2 : ℝ) : stLevel C Cv C1 C2 ↔ stLevelOpen C Cv C1 C2 := by
  constructor
  · intro H Lt u u' I hr h1 h2 R hR
    obtain ⟨h, SS, a, b, c, d, e, f, -, g⟩ := H Lt u u' I hr h1 h2 R hR
    exact ⟨h, SS, a, b, c, d, e, f, g⟩
  · intro H Lt u u' I hr h1 h2 R hR
    obtain ⟨h, SS, a, b, c, d, e, f, g⟩ := H Lt u u' I hr h1 h2 R hR
    exact ⟨h, SS, a, b, c, d, e, f, stOm_of_Std Lt h1.1, g⟩

end Formalism.MainNotions.InterlacingSignCuts

end PartALev

section PartAOpen

open Polynomial

namespace Formalism.MainNotions.InterlacingSignCuts

/- English proof (translation)
The claim follows from `stStatPhase_of_core`.
-/
theorem germ_model_stationary_phase_of_known (D : Formalism.BasicNotions.D7) : HereditaryPositivity.adm17 D := stStatPhase_of_core
/- English proof (translation)
The claim follows from `stStatPhase_of_core`.
-/
theorem two_bound_stationary_phase_of_known (D : Formalism.BasicNotions.D7) : RadialRuleConsequences.adm17 D := stStatPhase_of_core

/- English proof (translation)
The claim follows from `stMarkov_iff_mid.1 h`.
-/
theorem markov_middle_bound_of_admissible (D : Formalism.BasicNotions.D7) (h : Formalism.MainNotions.RadialRuleConsequences.adm14 D) : VMarkovMid := stMarkov_iff_mid.1 h

def twoBoundHypotheses (D : Formalism.BasicNotions.D7) (CB Co Cd Cv C1 C2 Cs c C₁ : ℝ) : Prop :=
  RadialRuleConsequences.adm1 D CB ∧ RadialRuleConsequences.adm2 D CB ∧ (RadialRuleConsequences.adm3a D ∧ RadialRuleConsequences.adm3b D) ∧ RadialRuleConsequences.RTTRelation D ∧ RadialRuleConsequences.adm5 D ∧ RadialRuleConsequences.adm6 D CB ∧
    RadialRuleConsequences.adm7 D ∧ RadialRuleConsequences.adm8 D CB Co Cd ∧ RadialRuleConsequences.PlaneWaveIsometry D ∧ RadialRuleConsequences.adm11 D CB Cv C1 C2 ∧ RadialRuleConsequences.adm12 D CB Cs ∧
    RadialRuleConsequences.adm13 D c C₁ ∧ VMarkovMid ∧ RadialRuleConsequences.adm18 D

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a1, a2, ⟨a3a, a3b, -⟩, ⟨-, a4b⟩, a5, a6, a7, a8, -, ⟨-, a10b⟩, a11, a12, a13, a14, -, -, -, a18⟩`. Conclude with `⟨a1, a2, ⟨a3a, a3b⟩, a4b, a5, a6, a7, a8, a10b, a11, a12, a13, markov_middle_bound_of_admissible D a14, a18⟩`. Introduce and unpack `⟨a1, a2, ⟨a3a, a3b⟩, a4b, a5, a6, a7, a8, a10b, a11, a12, a13, a14, a18⟩`. Conclude with `⟨a1, a2, ⟨a3a, a3b, two_bound_third_clause_of_known D⟩, ⟨two_bound_fourth_clause_of_known D, a4b⟩, a5, a6, a7, a8, two_bound_ibp_and_theta_log_of_known D, ⟨two_bound_wave_letters_of_known D, a10b⟩, a11, a12, a13, two_bound_markov_of_middle_bound D a14, two_bound_herglotz_of_known …`.
-/
theorem two_bound_admissible_iff_open (D : Formalism.BasicNotions.D7) (CB Co Cd Cv C1 C2 Cs c C₁ : ℝ) :
    RadialRuleConsequences.admitted D CB Co Cd Cv C1 C2 Cs c C₁ ↔ twoBoundHypotheses D CB Co Cd Cv C1 C2 Cs c C₁ := by
  constructor
  · rintro ⟨a1, a2, ⟨a3a, a3b, -⟩, ⟨-, a4b⟩, a5, a6, a7, a8, -, ⟨-, a10b⟩, a11, a12, a13, a14, -, -, -, a18⟩
    exact ⟨a1, a2, ⟨a3a, a3b⟩, a4b, a5, a6, a7, a8, a10b, a11, a12, a13, markov_middle_bound_of_admissible D a14, a18⟩
  · rintro ⟨a1, a2, ⟨a3a, a3b⟩, a4b, a5, a6, a7, a8, a10b, a11, a12, a13, a14, a18⟩
    exact ⟨a1, a2, ⟨a3a, a3b, two_bound_third_clause_of_known D⟩, ⟨two_bound_fourth_clause_of_known D, a4b⟩, a5, a6, a7, a8, two_bound_ibp_and_theta_log_of_known D,
      ⟨two_bound_wave_letters_of_known D, a10b⟩, a11, a12, a13, two_bound_markov_of_middle_bound D a14, two_bound_herglotz_of_known D,
      two_bound_poisson_summation_of_known D, stStatPhase_of_core, a18⟩

/- English proof (translation)
Unfold `RadialRuleConsequences.Stmt`. Rewrite using `[two_bound_admissible_iff_open]`.
-/
theorem two_bound_statement_iff_open (D : Formalism.BasicNotions.D7) (CB Co Cd Cv C1 C2 Cs c C₁ Cg CI C0 CA : ℝ) :
    RadialRuleConsequences.Stmt D CB Co Cd Cv C1 C2 Cs c C₁ Cg CI C0 CA ↔
      (twoBoundHypotheses D CB Co Cd Cv C1 C2 Cs c C₁ → RadialRuleConsequences.Conclusion1 D Cg CI ∧ RadialRuleConsequences.Conclusion2 D C0 CA) := by
  unfold RadialRuleConsequences.Stmt; rw [two_bound_admissible_iff_open]

def valuationHypotheses (D : Formalism.BasicNotions.D7) (CB Co Cd Cv C1 C2 Cs c C₁ Cg₁ Cg₂ : ℝ) : Prop :=
  RadialChainStatements.adm1 D CB ∧ RadialChainStatements.adm2 D CB ∧ (RadialChainStatements.adm3a D ∧ RadialChainStatements.adm3b D) ∧ RadialChainStatements.RTTRelation D ∧ RadialChainStatements.adm5 D ∧ RadialChainStatements.adm6 D CB ∧
    RadialChainStatements.adm7 D ∧ RadialChainStatements.adm8 D CB Co Cd ∧ RadialChainStatements.PlaneWaveIsometry D ∧ RadialChainStatements.adm11 D CB Cv C1 C2 ∧ (RadialChainStatements.adm12 D CB Cs ∧ RadialChainStatements.SliceBoundE D Cs) ∧
    RadialChainStatements.adm13 D c C₁ ∧ VMarkovMid ∧ RadialChainStatements.adm17 D Cg₁ Cg₂ ∧ RadialChainStatements.adm18 D

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a1, a2, ⟨a3a, a3b, -⟩, ⟨-, a4b⟩, a5, a6, a7, a8, -, ⟨-, a10b⟩, a11, a12, a13, a14, -, -, a17, a18⟩`. Conclude with `⟨a1, a2, ⟨a3a, a3b⟩, a4b, a5, a6, a7, a8, a10b, a11, a12, a13, markov_middle_bound_of_admissible D a14, a17, a18⟩`. Introduce and unpack `⟨a1, a2, ⟨a3a, a3b⟩, a4b, a5, a6, a7, a8, a10b, a11, a12, a13, a14, a17, a18⟩`. Conclude with `⟨a1, a2, ⟨a3a, a3b, valuation_third_clause_of_known D⟩, ⟨valuation_fourth_clause_of_known D, a4b⟩, a5, a6, a7, a8, valuation_ibp_and_theta_log_of_known D, ⟨valuation_wave_letters_of_known D, a10b⟩, a11, a12, a13, valuation_markov_of_middle_bound D a14, valuation_herglotz_of_known …`.
-/
theorem valuation_admissible_iff_open (D : Formalism.BasicNotions.D7) (CB Co Cd Cv C1 C2 Cs c C₁ Cg₁ Cg₂ : ℝ) :
    RadialChainStatements.admitted D CB Co Cd Cv C1 C2 Cs c C₁ Cg₁ Cg₂ ↔ valuationHypotheses D CB Co Cd Cv C1 C2 Cs c C₁ Cg₁ Cg₂ := by
  constructor
  · rintro ⟨a1, a2, ⟨a3a, a3b, -⟩, ⟨-, a4b⟩, a5, a6, a7, a8, -, ⟨-, a10b⟩, a11, a12, a13, a14, -, -, a17, a18⟩
    exact ⟨a1, a2, ⟨a3a, a3b⟩, a4b, a5, a6, a7, a8, a10b, a11, a12, a13, markov_middle_bound_of_admissible D a14, a17, a18⟩
  · rintro ⟨a1, a2, ⟨a3a, a3b⟩, a4b, a5, a6, a7, a8, a10b, a11, a12, a13, a14, a17, a18⟩
    exact ⟨a1, a2, ⟨a3a, a3b, valuation_third_clause_of_known D⟩, ⟨valuation_fourth_clause_of_known D, a4b⟩, a5, a6, a7, a8, valuation_ibp_and_theta_log_of_known D,
      ⟨valuation_wave_letters_of_known D, a10b⟩, a11, a12, a13, valuation_markov_of_middle_bound D a14, valuation_herglotz_of_known D,
      valuation_poisson_summation_of_known D, a17, a18⟩

/- English proof (translation)
Unfold `RadialChainStatements.Stmt`. Rewrite using `[valuation_admissible_iff_open]`.
-/
theorem valuation_statement_iff_open (D : Formalism.BasicNotions.D7) (CB Co Cd Cv C1 C2 Cs c C₁ Cg₁ Cg₂ C C' : ℝ) (Kst : ℕ)
    (Vm : Formalism.MainNotions.S.ValMap D.R.k D.R.rS) :
    RadialChainStatements.Stmt D CB Co Cd Cv C1 C2 Cs c C₁ Cg₁ Cg₂ C C' Kst Vm ↔
      (valuationHypotheses D CB Co Cd Cv C1 C2 Cs c C₁ Cg₁ Cg₂ → RadialChainStatements.aux₃ D C C' Kst Vm) := by
  unfold RadialChainStatements.Stmt; rw [valuation_admissible_iff_open]

def germValuationHypotheses (D : Formalism.BasicNotions.D7) (CB Co Cd Cv C1 C2 Cs c C₁ Cg₁ Cg₂ : ℝ) : Prop :=
  BlockEstimateTheorem.adm1 D CB ∧ BlockEstimateTheorem.adm2 D CB ∧ (BlockEstimateTheorem.adm3a D ∧ BlockEstimateTheorem.adm3b D) ∧ BlockEstimateTheorem.RTTRelation D ∧ BlockEstimateTheorem.adm5 D ∧ BlockEstimateTheorem.adm6 D CB ∧
    BlockEstimateTheorem.adm7 D ∧ BlockEstimateTheorem.adm8 D CB Co Cd ∧ BlockEstimateTheorem.PlaneWaveIsometry D ∧ BlockEstimateTheorem.adm11 D CB Cv C1 C2 ∧ BlockEstimateTheorem.adm12 D CB Cs ∧
    BlockEstimateTheorem.adm13 D c C₁ ∧ VMarkovMid ∧ BlockEstimateTheorem.adm17 D Cg₁ Cg₂ ∧ BlockEstimateTheorem.adm18 D

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a1, a2, ⟨a3a, a3b, -⟩, ⟨-, a4b⟩, a5, a6, a7, a8, -, ⟨-, a10b⟩, a11, a12, a13, a14, -, -, a17, a18⟩`. Conclude with `⟨a1, a2, ⟨a3a, a3b⟩, a4b, a5, a6, a7, a8, a10b, a11, a12, a13, markov_middle_bound_of_admissible D a14, a17, a18⟩`. Introduce and unpack `⟨a1, a2, ⟨a3a, a3b⟩, a4b, a5, a6, a7, a8, a10b, a11, a12, a13, a14, a17, a18⟩`. Conclude with `⟨a1, a2, ⟨a3a, a3b, germ_third_clause_of_known D⟩, ⟨germ_fourth_clause_of_known D, a4b⟩, a5, a6, a7, a8, germ_ibp_and_theta_log_of_known D, ⟨germ_wave_letters_of_known D, a10b⟩, a11, a12, a13, germ_markov_of_middle_bound D a14, germ_herglotz_of_known D, germ_poisson_summation_of_ …`.
-/
theorem germ_first_list_iff_open (D : Formalism.BasicNotions.D7) (CB Co Cd Cv C1 C2 Cs c C₁ Cg₁ Cg₂ : ℝ) :
    BlockEstimateTheorem.AdmA D CB Co Cd Cv C1 C2 Cs c C₁ Cg₁ Cg₂ ↔ germValuationHypotheses D CB Co Cd Cv C1 C2 Cs c C₁ Cg₁ Cg₂ := by
  constructor
  · rintro ⟨a1, a2, ⟨a3a, a3b, -⟩, ⟨-, a4b⟩, a5, a6, a7, a8, -, ⟨-, a10b⟩, a11, a12, a13, a14, -, -, a17, a18⟩
    exact ⟨a1, a2, ⟨a3a, a3b⟩, a4b, a5, a6, a7, a8, a10b, a11, a12, a13, markov_middle_bound_of_admissible D a14, a17, a18⟩
  · rintro ⟨a1, a2, ⟨a3a, a3b⟩, a4b, a5, a6, a7, a8, a10b, a11, a12, a13, a14, a17, a18⟩
    exact ⟨a1, a2, ⟨a3a, a3b, germ_third_clause_of_known D⟩, ⟨germ_fourth_clause_of_known D, a4b⟩, a5, a6, a7, a8, germ_ibp_and_theta_log_of_known D,
      ⟨germ_wave_letters_of_known D, a10b⟩, a11, a12, a13, germ_markov_of_middle_bound D a14, germ_herglotz_of_known D,
      germ_poisson_summation_of_known D, a17, a18⟩

/- English proof (translation)
Unfold `BlockEstimateTheorem.Stmt BlockEstimateTheorem.admitted`. Rewrite using `[germ_first_list_iff_open]`.
-/
theorem germ_statement_iff_open (D : Formalism.BasicNotions.D7) (Gm : BlockEstimateTheorem.GM) (Kst : ℕ)
    (CB Co Cd Cv C1 C2 Cs c C₁ Cg₁ Cg₂ E₀ Eg E₁ E₂ E₃ C C' : ℝ) :
    BlockEstimateTheorem.Stmt D Gm Kst CB Co Cd Cv C1 C2 Cs c C₁ Cg₁ Cg₂ E₀ Eg E₁ E₂ E₃ C C' ↔
      (germValuationHypotheses D CB Co Cd Cv C1 C2 Cs c C₁ Cg₁ Cg₂ ∧ BlockEstimateTheorem.AdmE D Gm Kst E₀ Eg E₁ E₂ E₃ →
        BlockEstimateTheorem.aux₃ D Gm C C' Kst) := by
  unfold BlockEstimateTheorem.Stmt BlockEstimateTheorem.admitted; rw [germ_first_list_iff_open]

def germModelHypotheses (D : Formalism.BasicNotions.D7) (Gm : HereditaryPositivity.GM) (CB Co Cd Cv C1 C2 Cs c C₁ : ℝ) (Ks : ℕ) (C₀ Cg : ℝ) : Prop :=
  HereditaryPositivity.adm1 D CB ∧ HereditaryPositivity.adm2 D CB ∧ (HereditaryPositivity.adm3a D ∧ HereditaryPositivity.adm3b D) ∧ HereditaryPositivity.RTTRelation D ∧ HereditaryPositivity.adm5 D ∧ HereditaryPositivity.adm6 D CB ∧
    HereditaryPositivity.adm7 D ∧ HereditaryPositivity.adm8 D CB Co Cd ∧ HereditaryPositivity.PlaneWaveIsometry D ∧ HereditaryPositivity.adm11 D CB Cv C1 C2 ∧ HereditaryPositivity.adm12 D CB Cs ∧
    HereditaryPositivity.SliceBoundE D Gm Ks C₀ Cg ∧ HereditaryPositivity.TopLevelPlaneWave D Gm Ks C₀ Cg ∧ HereditaryPositivity.LowerLevelPositivity D Ks C₀ Cg ∧ HereditaryPositivity.adm13 D c C₁ ∧ VMarkovMid ∧ HereditaryPositivity.adm18 D

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a1, a2, ⟨a3a, a3b, -⟩, ⟨-, a4b⟩, a5, a6, a7, a8, -, ⟨-, a10b⟩, a11, a12, a12e, a12f, a12g, a13, a14, -, -, -, a18⟩`. Conclude with `⟨a1, a2, ⟨a3a, a3b⟩, a4b, a5, a6, a7, a8, a10b, a11, a12, a12e, a12f, a12g, a13, markov_middle_bound_of_admissible D a14, a18⟩`. Introduce and unpack `⟨a1, a2, ⟨a3a, a3b⟩, a4b, a5, a6, a7, a8, a10b, a11, a12, a12e, a12f, a12g, a13, a14, a18⟩`. Conclude with `⟨a1, a2, ⟨a3a, a3b, germ_model_third_clause_of_known D⟩, ⟨germ_model_fourth_clause_of_known D, a4b⟩, a5, a6, a7, a8, germ_model_ibp_and_theta_log_of_known D, ⟨germ_model_wave_letters_of_known D, a10b⟩, a11, a12, a12e, a12f, a12g, a13, germ_model_markov_of_middle_bound D a14, germ …`.
-/
theorem germ_model_admissible_iff_open (D : Formalism.BasicNotions.D7) (Gm : HereditaryPositivity.GM) (CB Co Cd Cv C1 C2 Cs c C₁ : ℝ) (Ks : ℕ) (C₀ Cg : ℝ) :
    HereditaryPositivity.admitted D Gm CB Co Cd Cv C1 C2 Cs c C₁ Ks C₀ Cg ↔ germModelHypotheses D Gm CB Co Cd Cv C1 C2 Cs c C₁ Ks C₀ Cg := by
  constructor
  · rintro ⟨a1, a2, ⟨a3a, a3b, -⟩, ⟨-, a4b⟩, a5, a6, a7, a8, -, ⟨-, a10b⟩, a11, a12, a12e, a12f, a12g, a13, a14, -, -, -, a18⟩
    exact ⟨a1, a2, ⟨a3a, a3b⟩, a4b, a5, a6, a7, a8, a10b, a11, a12, a12e, a12f, a12g, a13, markov_middle_bound_of_admissible D a14, a18⟩
  · rintro ⟨a1, a2, ⟨a3a, a3b⟩, a4b, a5, a6, a7, a8, a10b, a11, a12, a12e, a12f, a12g, a13, a14, a18⟩
    exact ⟨a1, a2, ⟨a3a, a3b, germ_model_third_clause_of_known D⟩, ⟨germ_model_fourth_clause_of_known D, a4b⟩, a5, a6, a7, a8, germ_model_ibp_and_theta_log_of_known D,
      ⟨germ_model_wave_letters_of_known D, a10b⟩, a11, a12, a12e, a12f, a12g, a13, germ_model_markov_of_middle_bound D a14, germ_model_herglotz_of_known D,
      germ_model_poisson_summation_of_known D, stStatPhase_of_core, a18⟩

/- English proof (translation)
Unfold `HereditaryPositivity.Stmt`. Rewrite using `[germ_model_admissible_iff_open]`.
-/
theorem germ_model_statement_iff_open (D : Formalism.BasicNotions.D7) (Gm : HereditaryPositivity.GM) (CB Co Cd Cv C1 C2 Cs c Cd₁ : ℝ) (Ks : ℕ)
    (C₀ Cg C₁ C₂ C₃ : ℝ) :
    HereditaryPositivity.Stmt D Gm CB Co Cd Cv C1 C2 Cs c Cd₁ Ks C₀ Cg C₁ C₂ C₃ ↔
      (germModelHypotheses D Gm CB Co Cd Cv C1 C2 Cs c Cd₁ Ks C₀ Cg → HereditaryPositivity.aux₃ D Gm Ks C₀ Cg C₁ C₂ C₃) := by
  unfold HereditaryPositivity.Stmt; rw [germ_model_admissible_iff_open]

end Formalism.MainNotions.InterlacingSignCuts

end PartAOpen

section PartALat

open NumberField
open scoped nonZeroDivisors

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.FrobeniusOrbits

variable (D : D7)

/- English proof (translation)
Use `D.host.isCMField_hostE` as an intermediate fact. Use `infer_instance`.
-/
theorem host_totallyComplex : NumberField.IsTotallyComplex D.host.E := by
  have := D.host.isCMField_hostE
  infer_instance

def plOf (v : D.what₂.Tau) : InfinitePlace D.host.E := InfinitePlace.mk (plEmb D v)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem plOf_apply (v : D.what₂.Tau) (l : D.host.E) : plOf D v l = ‖plEmb D v l‖ := rfl

/- English proof (translation)
The claim follows from `((factEmb D.R D.host).2 _).2 (D.eTau v).2`.
-/
theorem plEmb_mem (v : D.what₂.Tau) : plEmb D v ∈ D.host.cmType :=
  ((factEmb D.R D.host).2 _).2 (D.eTau v).2

/- English proof (translation)
Introduce `v w h`. Establish `h1` using `(factEmb D.R D.host).1.1 h`. Conclude with `D.eTau.injective (Subtype.ext h1)`.
-/
theorem plEmb_injective : Function.Injective (plEmb D) := by
  intro v w h
  have h1 := (factEmb D.R D.host).1.1 h
  exact D.eTau.injective (Subtype.ext h1)

/- English proof (translation)
Establish `hcm` using `D.host.der.cmType.1`. Prove the components needed by the constructor for the conclusion. Introduce `v w h`. Break down `InfinitePlace.mk_eq_iff.1 h with h | h` into its components or cases. Conclude with `plEmb_injective D h`.

It suffices to derive a contradiction. Establish `h1` using `(hcm (plEmb D v)).1 (plEmb_mem D v)`. Apply `h1` to reduce the goal to its premises. Establish `: (starRingEnd ℂ).comp (plEmb D v) = plEmb D w` using `h`. Rewrite using `[this]`.

Conclude with `plEmb_mem D w`. Introduce `w`. Distinguish the cases in `hw : w.embedding ∈ D.host.cmType`. Take `⟨g, hg⟩` from `(factEmb D.R D.host).1.2 w.embedding`. Establish `hgP : g ∈ D.R.Psi` using `((factEmb D.R D.host).2 g).1 (hg ▸ hw)`.

Use `⟨D.eTau.symm ⟨g, hgP⟩, ?_⟩` and prove the remaining obligations. Establish `: plEmb D (D.eTau.symm ⟨g, hgP⟩) = w.embedding`. Unfold `plEmb`. Rewrite using `[Equiv.apply_symm_apply]`. Conclude with `hg`.

Unfold `plOf`. Rewrite using `[this, InfinitePlace.mk_embedding]`. Establish `hw' : (starRingEnd ℂ).comp w.embedding ∈ D.host.cmType`. Assume the negation of the conclusion as `hc`. Conclude with `hw ((hcm w.embedding).2 hc)`.

Take `⟨g, hg⟩` from `(factEmb D.R D.host).1.2 ((starRingEnd ℂ).comp w.embedding)`. Establish `hgP : g ∈ D.R.Psi` using `((factEmb D.R D.host).2 g).1 (hg ▸ hw')`. Use `⟨D.eTau.symm ⟨g, hgP⟩, ?_⟩` and prove the remaining obligations. Establish `: plEmb D (D.eTau.symm ⟨g, hgP⟩) = ComplexEmbedding.conjugate w.embedding`. Unfold `plEmb`.

Rewrite using `[Equiv.apply_symm_apply]`. Conclude with `hg`. Unfold `plOf`. Rewrite using `[this, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]`.
-/
theorem plOf_bijective : Function.Bijective (plOf D) := by
  have hcm := D.host.der.cmType.1
  constructor
  · intro v w h
    rcases InfinitePlace.mk_eq_iff.1 h with h | h
    · exact plEmb_injective D h
    · exfalso
      have h1 := (hcm (plEmb D v)).1 (plEmb_mem D v)
      apply h1
      have : (starRingEnd ℂ).comp (plEmb D v) = plEmb D w := h
      rw [this]
      exact plEmb_mem D w
  · intro w
    by_cases hw : w.embedding ∈ D.host.cmType
    · obtain ⟨g, hg⟩ := (factEmb D.R D.host).1.2 w.embedding
      have hgP : g ∈ D.R.Psi := ((factEmb D.R D.host).2 g).1 (hg ▸ hw)
      refine ⟨D.eTau.symm ⟨g, hgP⟩, ?_⟩
      have : plEmb D (D.eTau.symm ⟨g, hgP⟩) = w.embedding := by
        unfold plEmb
        rw [Equiv.apply_symm_apply]
        exact hg
      unfold plOf
      rw [this, InfinitePlace.mk_embedding]
    · have hw' : (starRingEnd ℂ).comp w.embedding ∈ D.host.cmType := by
        by_contra hc
        exact hw ((hcm w.embedding).2 hc)
      obtain ⟨g, hg⟩ := (factEmb D.R D.host).1.2 ((starRingEnd ℂ).comp w.embedding)
      have hgP : g ∈ D.R.Psi := ((factEmb D.R D.host).2 g).1 (hg ▸ hw')
      refine ⟨D.eTau.symm ⟨g, hgP⟩, ?_⟩
      have : plEmb D (D.eTau.symm ⟨g, hgP⟩) = ComplexEmbedding.conjugate w.embedding := by
        unfold plEmb
        rw [Equiv.apply_symm_apply]
        exact hg
      unfold plOf
      rw [this, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]

/- English proof (translation)
Rewrite using `[← D.what₂.card_Tau]`. Conclude with `(Fintype.card_of_bijective (plOf_bijective D)).symm`.
-/
theorem card_places : Fintype.card (InfinitePlace D.host.E) = D.R.f := by
  rw [← D.what₂.card_Tau]
  exact (Fintype.card_of_bijective (plOf_bijective D)).symm

/- English proof (translation)
Rewrite using `[← card_places D]`. Conclude with `Fintype.card_pos`.
-/
theorem f_pos : 0 < D.R.f := by
  rw [← card_places D]
  exact Fintype.card_pos

/- English proof (translation)
Conclude with `(Fintype.prod_bijective (plOf D) (plOf_bijective D) (fun v => F (plOf D v)) F (fun v => rfl)).symm`.
-/
theorem prod_places (F : InfinitePlace D.host.E → ℝ) : ∏ w, F w = ∏ v, F (plOf D v) := by
  exact (Fintype.prod_bijective (plOf D) (plOf_bijective D) (fun v => F (plOf D v)) F (fun v => rfl)).symm

def plInv : InfinitePlace D.host.E → D.what₂.Tau := (Equiv.ofBijective _ (plOf_bijective D)).symm

/- English proof (translation)
Conclude with `(Equiv.ofBijective _ (plOf_bijective D)).symm_apply_apply v`.
-/
theorem plInv_plOf (v : D.what₂.Tau) : plInv D (plOf D v) = v := by
  exact (Equiv.ofBijective _ (plOf_bijective D)).symm_apply_apply v

/- English proof (translation)
Unfold `minFac`. Establish `hne : ‖plEmb D v l‖ ≠ 0`. Rewrite using `[norm_ne_zero_iff]`. Conclude with `(map_ne_zero _).2 hl`. Rewrite using `[if_neg hne, plOf_apply, Real.rpow_natCast]`.
-/
theorem minFac_eq (x : ℝ) (v : D.what₂.Tau) (l : D.host.E) (hl : l ≠ 0) (K : ℕ) :
    minFac x ‖plEmb D v l‖ K = min 1 ((x / plOf D v l) ^ (K : ℝ)) := by
  unfold minFac
  have hne : ‖plEmb D v l‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    exact (map_ne_zero _).2 hl
  rw [if_neg hne, plOf_apply, Real.rpow_natCast]

/- English proof (translation)
Unfold `minFac`. Use `split_ifs`. Conclude with `zero_le_one`. Conclude with `le_min zero_le_one (pow_nonneg (div_nonneg hx hy) K)`.
-/
theorem minFac_nonneg (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (K : ℕ) : 0 ≤ minFac x y K := by
  unfold minFac
  split_ifs
  · exact zero_le_one
  · exact le_min zero_le_one (pow_nonneg (div_nonneg hx hy) K)

/- English proof (translation)
Use `Finset.sum_congr rfl fun l hl => ?_` and prove the remaining obligations. Rewrite using `[prod_places D]`. Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations. Rewrite using `[plInv_plOf D v, minFac_eq D (x v) v l (hS l hl) K]`.
-/
theorem sum_eq (x : D.what₂.Tau → ℝ) (K : ℕ) (S : Finset D.host.E) (hS : ∀ l ∈ S, l ≠ 0) :
    ∑ l ∈ S, ∏ v, minFac (x v) ‖plEmb D v l‖ K =
      ∑ l ∈ S, ∏ w : InfinitePlace D.host.E, min 1 ((x (plInv D w) / w l) ^ (K : ℝ)) := by
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [prod_places D]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [plInv_plOf D v, minFac_eq D (x v) v l (hS l hl) K]

/- English proof (translation)
Conclude with `Fintype.prod_equiv (Equiv.ofBijective _ (plOf_bijective D)).symm _ _ (fun w => rfl)`.
-/
theorem prod_infinitePlace_plInv_eq_prod (x : D.what₂.Tau → ℝ) : ∏ w : InfinitePlace D.host.E, x (plInv D w) = ∏ v, x v := by
  exact Fintype.prod_equiv (Equiv.ofBijective _ (plOf_bijective D)).symm _ _ (fun w => rfl)

end Formalism.MainNotions.InterlacingSignCuts

namespace Formalism.MainNotions.InterlacingSignCuts

open Formalism.BasicNotions Formalism.MainNotions.S

/- English proof (translation)
Take `⟨C, hC⟩` from `Formalism.SA.Final.boxSum`. Use `⟨C, fun D aa haa x Θ K hx hΘ hK hEq S hS => ?_⟩` and prove the remaining obligations. Use `haveI := host_totallyComplex D`. Rewrite using `[sum_eq D x K S (fun l hl => (hS l hl).2), ← card_places D]`. Use `hC D.host.E aa haa (fun w => x (plInv D w)) Θ K (fun w => hx _) hΘ (by exact_mod_cast hK) ?_ S hS` and prove the remaining obligations.

Rewrite using `[card_places D, prod_infinitePlace_plInv_eq_prod D x, hEq]`. Both sides reduce to the same expression.
-/
theorem latSum_eq_of_core : ∃ C : ℝ, ∀ (D : D7) (aa : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E), aa ≠ 0 →
    ∀ (x : D.what₂.Tau → ℝ) (Θ : ℝ) (K : ℕ), (∀ v, 0 < x v) → 2 < Θ → 3 ≤ K →
      Θ ^ D.R.f = nrmHalf D aa / ∏ v, x v →
      ∀ S : Finset D.host.E, (∀ l ∈ S, l ∈ aa ∧ l ≠ 0) →
        ∑ l ∈ S, ∏ v, minFac (x v) ‖plEmb D v l‖ K ≤ (C * Θ ^ (-((K : ℝ) - 5 / 2))) ^ D.R.f := by
  obtain ⟨C, hC⟩ := Formalism.SA.Final.boxSum
  refine ⟨C, fun D aa haa x Θ K hx hΘ hK hEq S hS => ?_⟩
  haveI := host_totallyComplex D
  rw [sum_eq D x K S (fun l hl => (hS l hl).2), ← card_places D]
  refine hC D.host.E aa haa (fun w => x (plInv D w)) Θ K (fun w => hx _) hΘ (by exact_mod_cast hK) ?_ S hS
  rw [card_places D, prod_infinitePlace_plInv_eq_prod D x, hEq]
  rfl

/- English proof (translation)
Take `⟨C, hC⟩` from `Formalism.FourierDecayAlt.P.box_weights_sum_to_one (K : ℝ) (by exact_mod_cast hK)`. Use `⟨C, fun D aa haa x hx hle S hS => ?_⟩` and prove the remaining obligations. Use `haveI := host_totallyComplex D`. Rewrite using `[sum_eq D x K S (fun l hl => (hS l hl).2), ← card_places D]`. Use `hC D.host.E aa haa (fun w => x (plInv D w)) (fun w => hx _) ?_ S hS` and prove the remaining obligations.

Rewrite using `[prod_infinitePlace_plInv_eq_prod D x]`. Conclude with `hle`.
-/
theorem latSumOne_of_core (K : ℕ) (hK : 2 < K) : ∃ C : ℝ, ∀ (D : D7) (aa : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E),
    aa ≠ 0 → ∀ (x : D.what₂.Tau → ℝ), (∀ v, 0 < x v) → ∏ v, x v ≤ nrmHalf D aa →
      ∀ S : Finset D.host.E, (∀ l ∈ S, l ∈ aa ∧ l ≠ 0) →
        ∑ l ∈ S, ∏ v, minFac (x v) ‖plEmb D v l‖ K ≤ C ^ D.R.f := by
  obtain ⟨C, hC⟩ := Formalism.FourierDecayAlt.P.box_weights_sum_to_one (K : ℝ) (by exact_mod_cast hK)
  refine ⟨C, fun D aa haa x hx hle S hS => ?_⟩
  haveI := host_totallyComplex D
  rw [sum_eq D x K S (fun l hl => (hS l hl).2), ← card_places D]
  refine hC D.host.E aa haa (fun w => x (plInv D w)) (fun w => hx _) ?_ S hS
  rw [prod_infinitePlace_plInv_eq_prod D x]
  exact hle

end Formalism.MainNotions.InterlacingSignCuts

end

end PartALat

section PartALat2

open NumberField
open scoped nonZeroDivisors

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts

open Formalism.BasicNotions Formalism.MainNotions.S

/- English proof (translation)
Unfold `nrmHalf`. Apply `Real.sqrt_pos.2` to reduce the goal to its premises. Establish `h0 : (0 : ℚ) ≤ FractionalIdeal.absNorm aa` using `FractionalIdeal.absNorm_nonneg aa`. Establish `h1 : FractionalIdeal.absNorm aa ≠ 0` using `fun e => h (FractionalIdeal.absNorm_eq_zero_iff.1 e)`. Conclude with `lt_of_le_of_ne h0 (Ne.symm h1)` after adjusting the coercions.
-/
theorem nrmHalf_pos (D : D7) (aa : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (h : aa ≠ 0) : 0 < nrmHalf D aa := by
  unfold nrmHalf
  apply Real.sqrt_pos.2
  have h0 : (0 : ℚ) ≤ FractionalIdeal.absNorm aa := FractionalIdeal.absNorm_nonneg aa
  have h1 : FractionalIdeal.absNorm aa ≠ 0 := fun e => h (FractionalIdeal.absNorm_eq_zero_iff.1 e)
  exact_mod_cast lt_of_le_of_ne h0 (Ne.symm h1)

/- English proof (translation)
Take `⟨C, hC⟩` from `latSum_eq_of_core`. Use `⟨|C|, abs_nonneg C, fun D aa haa x Θ K hx hΘ hK hle S hS => ?_⟩` and prove the remaining obligations. Establish `hf : D.R.f ≠ 0` using `(f_pos D).ne'`. Use `set Q : ℝ := nrmHalf D aa / ∏ v, x v with hQ`. Establish `hQ0 : 0 ≤ Q` using `div_nonneg (nrmHalf_pos D aa haa).le (Finset.prod_nonneg fun v _ => (hx v).le)`.

Use `set Θ' : ℝ := Q ^ ((D.R.f : ℝ)⁻¹) with hΘ'`. Establish `hpow : Θ' ^ D.R.f = Q` using `Real.rpow_inv_natCast_pow hQ0 hf`. Establish `hΘ'0 : 0 ≤ Θ'` using `Real.rpow_nonneg hQ0 _`. Establish `hΘle : Θ ≤ Θ'`. Use `(pow_le_pow_iff_left₀ (by linarith) hΘ'0 hf).1 ?_` and prove the remaining obligations.

Rewrite using `[hpow]`. Conclude with `hle`. Establish `h1` using `hC D aa haa x Θ' K hx (lt_of_lt_of_le hΘ hΘle) hK hpow S hS`. Use `le_trans h1 ?_` and prove the remaining obligations. Establish `hK' : (3 : ℝ) ≤ (K : ℝ)` using `by exact_mod_cast hK`.

Establish `hexp : -((K : ℝ) - 5 / 2) ≤ 0` using `by linarith`. Establish `h2 : Θ' ^ (-((K : ℝ) - 5 / 2)) ≤ Θ ^ (-((K : ℝ) - 5 / 2))` using `Real.rpow_le_rpow_of_nonpos (by linarith) hΘle hexp`. Establish `h3 : 0 ≤ Θ' ^ (-((K : ℝ) - 5 / 2))` using `Real.rpow_nonneg hΘ'0 _`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem latSum_of_core : ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (aa : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E), aa ≠ 0 →
    ∀ (x : D.what₂.Tau → ℝ) (Θ : ℝ) (K : ℕ), (∀ v, 0 < x v) → 2 < Θ → 3 ≤ K →
      Θ ^ D.R.f ≤ nrmHalf D aa / ∏ v, x v →
      ∀ S : Finset D.host.E, (∀ l ∈ S, l ∈ aa ∧ l ≠ 0) →
        ∑ l ∈ S, ∏ v, minFac (x v) ‖plEmb D v l‖ K ≤ (C * Θ ^ (-((K : ℝ) - 5 / 2))) ^ D.R.f := by
  obtain ⟨C, hC⟩ := latSum_eq_of_core
  refine ⟨|C|, abs_nonneg C, fun D aa haa x Θ K hx hΘ hK hle S hS => ?_⟩
  have hf : D.R.f ≠ 0 := (f_pos D).ne'
  set Q : ℝ := nrmHalf D aa / ∏ v, x v with hQ
  have hQ0 : 0 ≤ Q := div_nonneg (nrmHalf_pos D aa haa).le (Finset.prod_nonneg fun v _ => (hx v).le)
  set Θ' : ℝ := Q ^ ((D.R.f : ℝ)⁻¹) with hΘ'
  have hpow : Θ' ^ D.R.f = Q := Real.rpow_inv_natCast_pow hQ0 hf
  have hΘ'0 : 0 ≤ Θ' := Real.rpow_nonneg hQ0 _
  have hΘle : Θ ≤ Θ' := by
    refine (pow_le_pow_iff_left₀ (by linarith) hΘ'0 hf).1 ?_
    rw [hpow]; exact hle
  have h1 := hC D aa haa x Θ' K hx (lt_of_lt_of_le hΘ hΘle) hK hpow S hS
  refine le_trans h1 ?_
  have hK' : (3 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hexp : -((K : ℝ) - 5 / 2) ≤ 0 := by linarith
  have h2 : Θ' ^ (-((K : ℝ) - 5 / 2)) ≤ Θ ^ (-((K : ℝ) - 5 / 2)) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) hΘle hexp
  have h3 : 0 ≤ Θ' ^ (-((K : ℝ) - 5 / 2)) := Real.rpow_nonneg hΘ'0 _
  calc (C * Θ' ^ (-((K : ℝ) - 5 / 2))) ^ D.R.f ≤ |(C * Θ' ^ (-((K : ℝ) - 5 / 2))) ^ D.R.f| := le_abs_self _
    _ = (|C| * Θ' ^ (-((K : ℝ) - 5 / 2))) ^ D.R.f := by rw [abs_pow, abs_mul, abs_of_nonneg h3]
    _ ≤ (|C| * Θ ^ (-((K : ℝ) - 5 / 2))) ^ D.R.f :=
        pow_le_pow_left₀ (mul_nonneg (abs_nonneg _) h3) (mul_le_mul_of_nonneg_left h2 (abs_nonneg _)) _

/- English proof (translation)
Unfold `minFac`. Rewrite using `[norm_mul]`. Distinguish the cases in `hz : ‖z‖ = 0`. Rewrite using `[hz, mul_zero, if_pos rfl, if_pos rfl]`. Establish `ha' : ‖a‖ ≠ 0` using `norm_ne_zero_iff.2 ha`.

Rewrite using `[if_neg (mul_ne_zero ha' hz), if_neg hz, div_div]`.
-/
theorem minFac_scale (x : ℝ) (a z : ℂ) (ha : a ≠ 0) (K : ℕ) :
    minFac x ‖a * z‖ K = minFac (x / ‖a‖) ‖z‖ K := by
  unfold minFac
  rw [norm_mul]
  by_cases hz : ‖z‖ = 0
  · rw [hz, mul_zero, if_pos rfl, if_pos rfl]
  · have ha' : ‖a‖ ≠ 0 := norm_ne_zero_iff.2 ha
    rw [if_neg (mul_ne_zero ha' hz), if_neg hz, div_div]

/- English proof (translation)
Take `⟨C, hC0, hC⟩` from `latSum_of_core`. Use `⟨C, hC0, fun D aa haa a x Θ K ha hx hΘ hK hle S hS => ?_⟩` and prove the remaining obligations. Establish `hna : ∀ v, 0 < ‖a v‖` using `fun v => norm_pos_iff.2 (ha v)`. Establish `h1` using `hC D aa haa (fun v => x v / ‖a v‖) Θ K (fun v => div_pos (hx v) (hna v)) hΘ hK (by`. Rewrite using `[Finset.prod_div_distrib]`.

Establish `e : nrmHalf D aa / ((∏ v, x v) / ∏ v, ‖a v‖) = nrmHalf D aa * (∏ v, ‖a v‖) / ∏ v, x v`. Rewrite using `[div_div_eq_mul_div]`. Rewrite using `[e]`. Conclude with `hle) S hS`. Use `le_trans (le_of_eq ?_) h1` and prove the remaining obligations.

Use `Finset.sum_congr rfl fun l _ => Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations. Conclude with `minFac_scale _ _ _ (ha v) K`.
-/
theorem latSumScaled_of_core : ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (aa : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E), aa ≠ 0 →
    ∀ (a : D.what₂.Tau → ℂ) (x : D.what₂.Tau → ℝ) (Θ : ℝ) (K : ℕ), (∀ v, a v ≠ 0) → (∀ v, 0 < x v) → 2 < Θ → 3 ≤ K →
      Θ ^ D.R.f ≤ nrmHalf D aa * (∏ v, ‖a v‖) / ∏ v, x v →
      ∀ S : Finset D.host.E, (∀ l ∈ S, l ∈ aa ∧ l ≠ 0) →
        ∑ l ∈ S, ∏ v, minFac (x v) ‖a v * plEmb D v l‖ K ≤ (C * Θ ^ (-((K : ℝ) - 5 / 2))) ^ D.R.f := by
  obtain ⟨C, hC0, hC⟩ := latSum_of_core
  refine ⟨C, hC0, fun D aa haa a x Θ K ha hx hΘ hK hle S hS => ?_⟩
  have hna : ∀ v, 0 < ‖a v‖ := fun v => norm_pos_iff.2 (ha v)
  have h1 := hC D aa haa (fun v => x v / ‖a v‖) Θ K (fun v => div_pos (hx v) (hna v)) hΘ hK (by
    rw [Finset.prod_div_distrib]
    have e : nrmHalf D aa / ((∏ v, x v) / ∏ v, ‖a v‖) = nrmHalf D aa * (∏ v, ‖a v‖) / ∏ v, x v := by
      rw [div_div_eq_mul_div]
    rw [e]; exact hle) S hS
  refine le_trans (le_of_eq ?_) h1
  refine Finset.sum_congr rfl fun l _ => Finset.prod_congr rfl fun v _ => ?_
  exact minFac_scale _ _ _ (ha v) K

/- English proof (translation)
Take `⟨C, hC0, hC⟩` from `latSumScaled_of_core`. Use `⟨C, hC0, fun D aa haa a x Θ K ha hx hΘ hK hle large₂ hLg => ⟨fun l => ?_, fun S hS => ?_⟩⟩` and prove the remaining obligations. Conclude with `Finset.prod_nonneg fun v _ => minFac_nonneg _ _ (hx v).le (norm_nonneg _) K`. Conclude with `hC D aa haa a x Θ K ha hx hΘ hK hle S (fun l hl => ⟨hLg l (hS l hl).1, (hS l hl).2⟩)`.
-/
theorem latSumTA_of_core : ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (aa : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E), aa ≠ 0 →
    ∀ (a : D.what₂.Tau → ℂ) (x : D.what₂.Tau → ℝ) (Θ : ℝ) (K : ℕ), (∀ v, a v ≠ 0) → (∀ v, 0 < x v) → 2 < Θ → 3 ≤ K →
      Θ ^ D.R.f ≤ nrmHalf D aa * (∏ v, ‖a v‖) / ∏ v, x v →
      ∀ large₂ : AddSubgroup D.host.E, (∀ l ∈ large₂, l ∈ aa) →
        Formalism.FourierDecayAlt.TA.LatSum large₂ (fun l => ∏ v, minFac (x v) ‖a v * plEmb D v l‖ K)
          ((C * Θ ^ (-((K : ℝ) - 5 / 2))) ^ D.R.f) := by
  obtain ⟨C, hC0, hC⟩ := latSumScaled_of_core
  refine ⟨C, hC0, fun D aa haa a x Θ K ha hx hΘ hK hle large₂ hLg => ⟨fun l => ?_, fun S hS => ?_⟩⟩
  · exact Finset.prod_nonneg fun v _ => minFac_nonneg _ _ (hx v).le (norm_nonneg _) K
  · exact hC D aa haa a x Θ K ha hx hΘ hK hle S (fun l hl => ⟨hLg l (hS l hl).1, (hS l hl).2⟩)

section Theta

variable (D : D7) (C1 C2 N T T' : ℝ) (δ : D.host.E) (x : D.what₂.Tau → LocalDataRealPlace D) (L : LatticeDataWithDual D)

/- English proof (translation)
Apply `Set.Finite.bddAbove` to reduce the goal to its premises. Use `Set.Finite.union (Set.Finite.union ?_ ?_) ?_` and prove the remaining obligations. Use `Set.Finite.subset ((Finset.Icc 1 (D.R.rS + 1)).image (fun i => (∏ v, xSz D C1 C2 N (kaV D δ v) T T' (x v) i) / nrmHalf D (L.aaV i 1))).finite_toSet ?_` and prove the remaining obligations. Introduce and unpack `y ⟨i, h1, h2, rfl⟩`. Conclude with `Finset.mem_coe.2 (Finset.mem_image.2 ⟨i, Finset.mem_Icc.2 ⟨h1, h2⟩, rfl⟩)`.

Use `Set.Finite.subset (((Finset.Icc 1 (D.R.rS + 1)) ×ˢ (Finset.Icc 2 (D.R.rS + 2))).image (fun p : ℕ × ℕ => (∏ v, LamSz D C1 C2 N (kaV D δ v) T T' (x v) p.1 p.2) / min (nrmHalf D (L.aaV p.1 p.2)) (nrmHalf D (L.aaP p.1 (p.2 - 1))))).finite_toSet ?_` and prove the remaining obligations. Introduce and unpack `y ⟨i, s, h1, h2, h3, rfl⟩`. Use `Finset.mem_coe.2 (Finset.mem_image.2 ⟨(i, s), ?_, rfl⟩)` and prove the remaining obligations. Rewrite using `[Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]`. Apply the tactic sequence `refine ⟨⟨h1, ?_⟩, ⟨h2, ?_⟩⟩ <;> simp only <;> omega`.

Use `Set.Finite.subset ((Finset.Icc 1 D.R.rS).image (fun i => (∏ v, LamPSz D C1 C2 N (kaV D δ v) T T' (x v) i) / nrmHalf D (L.aaP i (D.R.rS + 2 - i)))).finite_toSet ?_` and prove the remaining obligations. Introduce and unpack `y ⟨i, h1, h2, rfl⟩`. Conclude with `Finset.mem_coe.2 (Finset.mem_image.2 ⟨i, Finset.mem_Icc.2 ⟨h1, h2⟩, rfl⟩)`.
-/
theorem ThSet_bdd : BddAbove
    ({y | ∃ i, 1 ≤ i ∧ i ≤ D.R.rS + 1 ∧
          y = (∏ v, xSz D C1 C2 N (kaV D δ v) T T' (x v) i) / nrmHalf D (L.aaV i 1)} ∪
        {y | ∃ i s, 1 ≤ i ∧ 2 ≤ s ∧ i - 1 + s ≤ D.R.rS + 1 ∧
          y = (∏ v, LamSz D C1 C2 N (kaV D δ v) T T' (x v) i s) /
            min (nrmHalf D (L.aaV i s)) (nrmHalf D (L.aaP i (s - 1)))} ∪
        {y | ∃ i, 1 ≤ i ∧ i ≤ D.R.rS ∧
          y = (∏ v, LamPSz D C1 C2 N (kaV D δ v) T T' (x v) i) / nrmHalf D (L.aaP i (D.R.rS + 2 - i))}) := by
  apply Set.Finite.bddAbove
  refine Set.Finite.union (Set.Finite.union ?_ ?_) ?_
  · refine Set.Finite.subset ((Finset.Icc 1 (D.R.rS + 1)).image (fun i =>
      (∏ v, xSz D C1 C2 N (kaV D δ v) T T' (x v) i) / nrmHalf D (L.aaV i 1))).finite_toSet ?_
    rintro y ⟨i, h1, h2, rfl⟩
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨i, Finset.mem_Icc.2 ⟨h1, h2⟩, rfl⟩)
  · refine Set.Finite.subset (((Finset.Icc 1 (D.R.rS + 1)) ×ˢ (Finset.Icc 2 (D.R.rS + 2))).image (fun p : ℕ × ℕ =>
      (∏ v, LamSz D C1 C2 N (kaV D δ v) T T' (x v) p.1 p.2) /
        min (nrmHalf D (L.aaV p.1 p.2)) (nrmHalf D (L.aaP p.1 (p.2 - 1))))).finite_toSet ?_
    rintro y ⟨i, s, h1, h2, h3, rfl⟩
    refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨(i, s), ?_, rfl⟩)
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    refine ⟨⟨h1, ?_⟩, ⟨h2, ?_⟩⟩ <;> simp only <;> omega
  · refine Set.Finite.subset ((Finset.Icc 1 D.R.rS).image (fun i =>
      (∏ v, LamPSz D C1 C2 N (kaV D δ v) T T' (x v) i) / nrmHalf D (L.aaP i (D.R.rS + 2 - i)))).finite_toSet ?_
    rintro y ⟨i, h1, h2, rfl⟩
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨i, Finset.mem_Icc.2 ⟨h1, h2⟩, rfl⟩)

/- English proof (translation)
The claim follows from `le_csSup (ThSet_bdd D C1 C2 N T T' δ x L) (Or.inl (Or.inl ⟨i, h1, h2, rfl⟩))`.
-/
theorem x_le_ThInvF (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ D.R.rS + 1) :
    (∏ v, xSz D C1 C2 N (kaV D δ v) T T' (x v) i) / nrmHalf D (L.aaV i 1) ≤ ThInvF D C1 C2 N T T' δ x L :=
  le_csSup (ThSet_bdd D C1 C2 N T T' δ x L) (Or.inl (Or.inl ⟨i, h1, h2, rfl⟩))

/- English proof (translation)
The claim follows from `le_csSup (ThSet_bdd D C1 C2 N T T' δ x L) (Or.inl (Or.inr ⟨i, s, h1, h2, h3, rfl⟩))`.
-/
theorem Lam_le_ThInvF (i s : ℕ) (h1 : 1 ≤ i) (h2 : 2 ≤ s) (h3 : i - 1 + s ≤ D.R.rS + 1) :
    (∏ v, LamSz D C1 C2 N (kaV D δ v) T T' (x v) i s) /
      min (nrmHalf D (L.aaV i s)) (nrmHalf D (L.aaP i (s - 1))) ≤ ThInvF D C1 C2 N T T' δ x L :=
  le_csSup (ThSet_bdd D C1 C2 N T T' δ x L) (Or.inl (Or.inr ⟨i, s, h1, h2, h3, rfl⟩))

/- English proof (translation)
The claim follows from `le_csSup (ThSet_bdd D C1 C2 N T T' δ x L) (Or.inr ⟨i, h1, h2, rfl⟩)`.
-/
theorem prod_div_norm_le_sup (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ D.R.rS) :
    (∏ v, LamPSz D C1 C2 N (kaV D δ v) T T' (x v) i) / nrmHalf D (L.aaP i (D.R.rS + 2 - i)) ≤
      ThInvF D C1 C2 N T T' δ x L :=
  le_csSup (ThSet_bdd D C1 C2 N T T' δ x L) (Or.inr ⟨i, h1, h2, rfl⟩)

/- English proof (translation)
Establish `hf : (D.R.f : ℝ) ≠ 0` using `by exact_mod_cast (f_pos D).ne'`. Unfold `ThS`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul h.le]`. Establish `: -(1 / (D.R.f : ℝ)) * (D.R.f : ℝ) = -1` using `by field_simp`. Rewrite using `[this, Real.rpow_neg_one]`.
-/
theorem ThS_pow (h : 0 < ThInvF D C1 C2 N T T' δ x L) :
    ThS D C1 C2 N T T' δ x L ^ D.R.f = (ThInvF D C1 C2 N T T' δ x L)⁻¹ := by
  have hf : (D.R.f : ℝ) ≠ 0 := by exact_mod_cast (f_pos D).ne'
  unfold ThS
  rw [← Real.rpow_natCast, ← Real.rpow_mul h.le]
  have : -(1 / (D.R.f : ℝ)) * (D.R.f : ℝ) = -1 := by field_simp
  rw [this, Real.rpow_neg_one]

/- English proof (translation)
Establish `h0 : 0 < P / n` using `div_pos hP hn`. Rewrite using `[ThS_pow D C1 C2 N T T' δ x L (lt_of_lt_of_le h0 h)]`. Use `inv_anti₀ h0 h` as an intermediate fact. Rewrite `this` using `[inv_div]`. Then use the resulting hypothesis.
-/
theorem ThS_pow_le {P n : ℝ} (hP : 0 < P) (hn : 0 < n) (h : P / n ≤ ThInvF D C1 C2 N T T' δ x L) :
    ThS D C1 C2 N T T' δ x L ^ D.R.f ≤ n / P := by
  have h0 : 0 < P / n := div_pos hP hn
  rw [ThS_pow D C1 C2 N T T' δ x L (lt_of_lt_of_le h0 h)]
  have := inv_anti₀ h0 h
  rwa [inv_div] at this

end Theta

/- English proof (translation)
Take `⟨C, hC0, hC⟩` from `latSum_of_core`. Use `⟨C, hC0, fun D C1 C2 N T T' δ x L K i h1 h2 haa hx hΘ hK S hS => ?_⟩` and prove the remaining obligations. Conclude with `hC D _ haa _ _ K hx hΘ hK (ThS_pow_le D C1 C2 N T T' δ x L (Finset.prod_pos fun v _ => hx v) (nrmHalf_pos D _ haa) (x_le_ThInvF D C1 C2 N T T' δ x L i h1 h2)) S hS`.
-/
theorem latSum_x_ThS : ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (C1 C2 N T T' : ℝ) (δ : D.host.E) (x : D.what₂.Tau → LocalDataRealPlace D)
    (L : LatticeDataWithDual D) (K i : ℕ), 1 ≤ i → i ≤ D.R.rS + 1 → L.aaV i 1 ≠ 0 →
    (∀ v, 0 < xSz D C1 C2 N (kaV D δ v) T T' (x v) i) → 2 < ThS D C1 C2 N T T' δ x L → 3 ≤ K →
    ∀ S : Finset D.host.E, (∀ l ∈ S, l ∈ L.aaV i 1 ∧ l ≠ 0) →
      ∑ l ∈ S, ∏ v, minFac (xSz D C1 C2 N (kaV D δ v) T T' (x v) i) ‖plEmb D v l‖ K ≤
        (C * ThS D C1 C2 N T T' δ x L ^ (-((K : ℝ) - 5 / 2))) ^ D.R.f := by
  obtain ⟨C, hC0, hC⟩ := latSum_of_core
  refine ⟨C, hC0, fun D C1 C2 N T T' δ x L K i h1 h2 haa hx hΘ hK S hS => ?_⟩
  exact hC D _ haa _ _ K hx hΘ hK
    (ThS_pow_le D C1 C2 N T T' δ x L (Finset.prod_pos fun v _ => hx v) (nrmHalf_pos D _ haa)
      (x_le_ThInvF D C1 C2 N T T' δ x L i h1 h2)) S hS

/- English proof (translation)
Take `⟨C, hC0, hC⟩` from `latSum_of_core`. Use `⟨C, hC0, fun D C1 C2 N T T' δ x L K i s h1 h2 h3 haV haP hx hΘ hK S hS => ?_⟩` and prove the remaining obligations. Establish `hP : 0 < ∏ v, LamSz D C1 C2 N (kaV D δ v) T T' (x v) i s` using `Finset.prod_pos fun v _ => hx v`. Establish `hnV` using `nrmHalf_pos D _ haV`. Establish `hnP` using `nrmHalf_pos D _ haP`.

Use `hC D _ haP _ _ K hx hΘ hK (ThS_pow_le D C1 C2 N T T' δ x L hP hnP ?_) S hS` and prove the remaining obligations. Use `le_trans ?_ (Lam_le_ThInvF D C1 C2 N T T' δ x L i s h1 h2 h3)` and prove the remaining obligations. Conclude with `div_le_div_of_nonneg_left hP.le (lt_min hnV hnP) (min_le_right _ _)`.
-/
theorem latSum_Lam_ThS : ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (C1 C2 N T T' : ℝ) (δ : D.host.E) (x : D.what₂.Tau → LocalDataRealPlace D)
    (L : LatticeDataWithDual D) (K i s : ℕ), 1 ≤ i → 2 ≤ s → i - 1 + s ≤ D.R.rS + 1 → L.aaV i s ≠ 0 → L.aaP i (s - 1) ≠ 0 →
    (∀ v, 0 < LamSz D C1 C2 N (kaV D δ v) T T' (x v) i s) → 2 < ThS D C1 C2 N T T' δ x L → 3 ≤ K →
    ∀ S : Finset D.host.E, (∀ l ∈ S, l ∈ L.aaP i (s - 1) ∧ l ≠ 0) →
      ∑ l ∈ S, ∏ v, minFac (LamSz D C1 C2 N (kaV D δ v) T T' (x v) i s) ‖plEmb D v l‖ K ≤
        (C * ThS D C1 C2 N T T' δ x L ^ (-((K : ℝ) - 5 / 2))) ^ D.R.f := by
  obtain ⟨C, hC0, hC⟩ := latSum_of_core
  refine ⟨C, hC0, fun D C1 C2 N T T' δ x L K i s h1 h2 h3 haV haP hx hΘ hK S hS => ?_⟩
  have hP : 0 < ∏ v, LamSz D C1 C2 N (kaV D δ v) T T' (x v) i s := Finset.prod_pos fun v _ => hx v
  have hnV := nrmHalf_pos D _ haV
  have hnP := nrmHalf_pos D _ haP
  refine hC D _ haP _ _ K hx hΘ hK (ThS_pow_le D C1 C2 N T T' δ x L hP hnP ?_) S hS
  refine le_trans ?_ (Lam_le_ThInvF D C1 C2 N T T' δ x L i s h1 h2 h3)
  exact div_le_div_of_nonneg_left hP.le (lt_min hnV hnP) (min_le_right _ _)

/- English proof (translation)
Establish `hP : 0 < ∏ v, LamSz D C1 C2 N (kaV D δ v) T T' (x v) i s` using `Finset.prod_pos fun v _ => hx v`. Establish `hnV` using `nrmHalf_pos D _ haV`. Establish `hnP` using `nrmHalf_pos D _ haP`. Establish `hq : (∏ v, LamSz D C1 C2 N (kaV D δ v) T T' (x v) i s) / nrmHalf D (L.aaV i s) ≤ ThInvF D C1 C2 N T T' δ x L` using `le_trans (div_le_div_of_nonneg_left hP.le (lt_min hnV hnP) (min_le_left _ _)) (Lam_le_ThInvF D C1 C2 N T T' δ x L i s h1 h2 h3)`. Establish `h4` using `ThS_pow_le D C1 C2 N T T' δ x L hP hnV hq`.

Establish `h5 : (1 : ℝ) ≤ ThS D C1 C2 N T T' δ x L ^ D.R.f` using `one_le_pow₀ hΘ`. Establish `h6 : 1 ≤ nrmHalf D (L.aaV i s) / ∏ v, LamSz D C1 C2 N (kaV D δ v) T T' (x v) i s` using `le_trans h5 h4`. Rewrite `h6` using `[one_le_div hP]`. Then use the resulting hypothesis.
-/
theorem local_size_product_le_half_norm (D : D7) (C1 C2 N T T' : ℝ) (δ : D.host.E) (x : D.what₂.Tau → LocalDataRealPlace D) (L : LatticeDataWithDual D) (i s : ℕ)
    (h1 : 1 ≤ i) (h2 : 2 ≤ s) (h3 : i - 1 + s ≤ D.R.rS + 1) (haV : L.aaV i s ≠ 0) (haP : L.aaP i (s - 1) ≠ 0)
    (hx : ∀ v, 0 < LamSz D C1 C2 N (kaV D δ v) T T' (x v) i s) (hΘ : 1 ≤ ThS D C1 C2 N T T' δ x L) :
    ∏ v, LamSz D C1 C2 N (kaV D δ v) T T' (x v) i s ≤ nrmHalf D (L.aaV i s) := by
  have hP : 0 < ∏ v, LamSz D C1 C2 N (kaV D δ v) T T' (x v) i s := Finset.prod_pos fun v _ => hx v
  have hnV := nrmHalf_pos D _ haV
  have hnP := nrmHalf_pos D _ haP
  have hq : (∏ v, LamSz D C1 C2 N (kaV D δ v) T T' (x v) i s) / nrmHalf D (L.aaV i s) ≤
      ThInvF D C1 C2 N T T' δ x L :=
    le_trans (div_le_div_of_nonneg_left hP.le (lt_min hnV hnP) (min_le_left _ _))
      (Lam_le_ThInvF D C1 C2 N T T' δ x L i s h1 h2 h3)
  have h4 := ThS_pow_le D C1 C2 N T T' δ x L hP hnV hq
  have h5 : (1 : ℝ) ≤ ThS D C1 C2 N T T' δ x L ^ D.R.f := one_le_pow₀ hΘ
  have h6 : 1 ≤ nrmHalf D (L.aaV i s) / ∏ v, LamSz D C1 C2 N (kaV D δ v) T T' (x v) i s := le_trans h5 h4
  rwa [one_le_div hP] at h6

/- English proof (translation)
Take `⟨C, hC0, hC⟩` from `latSum_of_core`. Use `⟨C, hC0, fun D C1 C2 N T T' δ x L K i h1 h2 haP hx hΘ hK S hS => ?_⟩` and prove the remaining obligations. Establish `hP : 0 < ∏ v, LamPSz D C1 C2 N (kaV D δ v) T T' (x v) i` using `Finset.prod_pos fun v _ => hx v`. Establish `hnP` using `nrmHalf_pos D _ haP`. Use `hC D _ haP _ _ K (fun v => mul_pos two_pos (hx v)) (by linarith) hK ?_ S hS` and prove the remaining obligations.

Establish `h4` using `ThS_pow_le D C1 C2 N T T' δ x L hP hnP (prod_div_norm_le_sup D C1 C2 N T T' δ x L i h1 h2)`. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, D.what₂.card_Tau, div_pow, div_mul_eq_div_div_swap]`. Conclude with `div_le_div_of_nonneg_right h4 (by positivity)`.
-/
theorem latSum_LamP_ThS : ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (C1 C2 N T T' : ℝ) (δ : D.host.E) (x : D.what₂.Tau → LocalDataRealPlace D)
    (L : LatticeDataWithDual D) (K i : ℕ), 1 ≤ i → i ≤ D.R.rS → L.aaP i (D.R.rS + 2 - i) ≠ 0 →
    (∀ v, 0 < LamPSz D C1 C2 N (kaV D δ v) T T' (x v) i) → 4 < ThS D C1 C2 N T T' δ x L → 3 ≤ K →
    ∀ S : Finset D.host.E, (∀ l ∈ S, l ∈ L.aaP i (D.R.rS + 2 - i) ∧ l ≠ 0) →
      ∑ l ∈ S, ∏ v, minFac (2 * LamPSz D C1 C2 N (kaV D δ v) T T' (x v) i) ‖plEmb D v l‖ K ≤
        (C * (ThS D C1 C2 N T T' δ x L / 2) ^ (-((K : ℝ) - 5 / 2))) ^ D.R.f := by
  obtain ⟨C, hC0, hC⟩ := latSum_of_core
  refine ⟨C, hC0, fun D C1 C2 N T T' δ x L K i h1 h2 haP hx hΘ hK S hS => ?_⟩
  have hP : 0 < ∏ v, LamPSz D C1 C2 N (kaV D δ v) T T' (x v) i := Finset.prod_pos fun v _ => hx v
  have hnP := nrmHalf_pos D _ haP
  refine hC D _ haP _ _ K (fun v => mul_pos two_pos (hx v)) (by linarith) hK ?_ S hS
  have h4 := ThS_pow_le D C1 C2 N T T' δ x L hP hnP (prod_div_norm_le_sup D C1 C2 N T T' δ x L i h1 h2)
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, D.what₂.card_Tau, div_pow, div_mul_eq_div_div_swap]
  exact div_le_div_of_nonneg_right h4 (by positivity)

end Formalism.MainNotions.InterlacingSignCuts

end

end PartALat2

section PartAAx

open scoped ComplexConjugate ComplexOrder

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.FourierDecayAlt.TA

attribute [local instance] Classical.propDecidable

/- English proof (translation)
Use `hK {p} (fun _ => 1)` as an intermediate fact. Simplify using `using this`.
-/
theorem PSDK.diag_real {α : Type*} {K : α → α → ℂ} (hK : PSDK K) (p : α) : 0 ≤ K p p := by
  have := hK {p} (fun _ => 1)
  simpa using this

/- English proof (translation)
Distinguish the cases in `h : p = q`. Substitute `h` using the available equality. Establish `h1` using `(Complex.le_def.1 (PSDK.diag_real hK p)).2`. Apply `Complex.ext` to reduce the goal to its premises. Simplify using the standard rewrite rules.

Simplify using `only [Complex.conj_im]`. Simplify using `only [Complex.zero_im] at h1`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hp` using `(Complex.le_def.1 (PSDK.diag_real hK p)).2`. Establish `hq` using `(Complex.le_def.1 (PSDK.diag_real hK q)).2`.

Establish `h3` using `(Complex.le_def.1 (hK {p, q} (fun _ => 1))).2`. Establish `h4` using `(Complex.le_def.1 (hK {p, q} (fun z => if z = p then 1 else Complex.I))).2`. Establish `hqp : ¬ q = p` using `fun e => h e.symm`. Simplify using `only [Finset.sum_pair h, star_one, one_mul, mul_one, Complex.zero_im, Complex.add_im] at h3`. Simplify using `only [Finset.sum_pair h, if_true, if_neg hqp, one_mul, mul_one, Complex.zero_im, Complex.add_im, Complex.star_def, Complex.conj_I, Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im, neg_zero, zero_mul, mul_zero, map_one, add_zero, zero_add …`.

Simplify using `only [Complex.zero_im] at hp hq`. Apply `Complex.ext` to reduce the goal to its premises. Simplify using `only [Complex.conj_re]`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `only [Complex.conj_im]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem PSDK.herm {α : Type*} {K : α → α → ℂ} (hK : PSDK K) (p q : α) : K q p = conj (K p q) := by
  by_cases h : p = q
  · subst h
    have h1 := (Complex.le_def.1 (PSDK.diag_real hK p)).2
    apply Complex.ext
    · simp
    · simp only [Complex.conj_im]
      simp only [Complex.zero_im] at h1
      linarith
  · have hp := (Complex.le_def.1 (PSDK.diag_real hK p)).2
    have hq := (Complex.le_def.1 (PSDK.diag_real hK q)).2
    have h3 := (Complex.le_def.1 (hK {p, q} (fun _ => 1))).2
    have h4 := (Complex.le_def.1 (hK {p, q} (fun z => if z = p then 1 else Complex.I))).2
    have hqp : ¬ q = p := fun e => h e.symm
    simp only [Finset.sum_pair h, star_one, one_mul, mul_one, Complex.zero_im, Complex.add_im] at h3
    simp only [Finset.sum_pair h, if_true, if_neg hqp, one_mul, mul_one, Complex.zero_im, Complex.add_im,
      Complex.star_def, Complex.conj_I, Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.neg_re,
      Complex.neg_im, neg_zero, zero_mul, mul_zero, map_one, add_zero, zero_add] at h4
    simp only [Complex.zero_im] at hp hq
    apply Complex.ext
    · simp only [Complex.conj_re]; linarith
    · simp only [Complex.conj_im]; linarith

/- English proof (translation)
Use `⟨fun x _ y _ => PSDK.herm hK _ _, fun a => ?_⟩` and prove the remaining obligations. Establish `hinj : Set.InjOn φ (P : Set α)` using `fun x hx y hy e => by`. Rewrite using `[← hψ x hx, ← hψ y hy, e]`. Establish `h` using `hK (P.image φ) (fun q => conj (a (ψ q)))`. Rewrite `h` using `[Finset.sum_image hinj]`.

Establish `h2 : (∑ x ∈ P, ∑ y ∈ P, conj (a x) * K (φ y) (φ x) * a y) = ∑ x ∈ P, ∑ q ∈ P.image φ, star (conj (a (ψ (φ x)))) * K (φ x) q * conj (a (ψ q))`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun y hy => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_image hinj]`. Use `Finset.sum_congr rfl fun x hx => ?_` and prove the remaining obligations.

Rewrite using `[hψ x hx, hψ y hy]`. Simplify using `only [Complex.star_def, Complex.conj_conj]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h2]`. Conclude with `(Complex.le_def.1 h).1`.
-/
theorem pull_psd {α β : Type} {K : β → β → ℂ} (hK : PSDK K) (P : Finset α) (φ : α → β) (ψ : β → α)
    (hψ : ∀ x ∈ P, ψ (φ x) = x) : PSDOn P (fun x y => K (φ y) (φ x)) := by
  refine ⟨fun x _ y _ => PSDK.herm hK _ _, fun a => ?_⟩
  have hinj : Set.InjOn φ (P : Set α) := fun x hx y hy e => by
    rw [← hψ x hx, ← hψ y hy, e]
  have h := hK (P.image φ) (fun q => conj (a (ψ q)))
  rw [Finset.sum_image hinj] at h
  have h2 : (∑ x ∈ P, ∑ y ∈ P, conj (a x) * K (φ y) (φ x) * a y) =
      ∑ x ∈ P, ∑ q ∈ P.image φ, star (conj (a (ψ (φ x)))) * K (φ x) q * conj (a (ψ q)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [hψ x hx, hψ y hy]
    simp only [Complex.star_def, Complex.conj_conj]
    ring
  rw [h2]
  exact (Complex.le_def.1 h).1

section Points

variable {E : Type} [Field E]

def sw (p : Pt E) : List (E × ℕ) := p.map Prod.swap

/- English proof (translation)
Use `⟨fun b hb => ?_, ?_⟩` and prove the remaining obligations. Take `⟨c, hc, rfl⟩` from `List.mem_map.1 hb`. Conclude with `⟨(h.2 c hc).2, (h.2 c hc).1⟩`. Establish `: (sw p).map Prod.snd = p.map Prod.fst`. Simplify using `[sw, List.map_map, Function.comp_def]`.

Rewrite using `[this]`. Conclude with `h.1`.
-/
theorem sw_ok {i : ℕ} {p : Pt E} (h : IsPt i p) :
    (∀ b ∈ sw p, b.1 ≠ 0 ∧ 1 ≤ b.2) ∧ ((sw p).map Prod.snd).sum = i := by
  refine ⟨fun b hb => ?_, ?_⟩
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hb
    exact ⟨(h.2 c hc).2, (h.2 c hc).1⟩
  · have : (sw p).map Prod.snd = p.map Prod.fst := by
      simp [sw, List.map_map, Function.comp_def]
    rw [this]; exact h.1

def dflt (i : ℕ) : Point E i :=
  if h : i = 0 then ⟨[], by simp [h]⟩ else ⟨[((1 : E), i)], by
    refine ⟨fun b hb => ?_, by simp⟩
    rw [List.mem_singleton.1 hb]; exact ⟨one_ne_zero, by simp only; omega⟩⟩

def ph (i : ℕ) (p : Pt E) : Point E i := if h : IsPt i p then ⟨sw p, sw_ok h⟩ else dflt i

def unsw {i : ℕ} (q : Point E i) : Pt E := q.1.map Prod.swap

/- English proof (translation)
Simplify using `[ph, h]`.
-/
theorem ph_val {i : ℕ} {p : Pt E} (h : IsPt i p) : (ph i p).1 = sw p := by
  simp [ph, h]

/- English proof (translation)
Simplify using `[unsw, ph, h, sw, List.map_map]`.
-/
theorem unsw_ph {i : ℕ} {p : Pt E} (h : IsPt i p) : unsw (ph i p) = p := by
  simp [unsw, ph, h, sw, List.map_map]

/- English proof (translation)
Use `⟨?_, fun b hb => ?_⟩` and prove the remaining obligations. Use `hh.1` as an intermediate fact. Simplify using `only [lvl] at this`. Simplify using `[lvl, ext, this]`. Break down `List.mem_append.1 hb with hb | hb` into its components or cases.

Conclude with `hh.2 b hb`. Rewrite using `[List.mem_singleton.1 hb]`. Conclude with `⟨hs, ht⟩`.
-/
theorem isPt_ext {j s : ℕ} {h : Pt E} {t : E} (hh : IsPt j h) (hs : 1 ≤ s) (ht : t ≠ 0) : IsPt (j + s) (ext h s t) := by
  refine ⟨?_, fun b hb => ?_⟩
  · have := hh.1
    simp only [lvl] at this
    simp [lvl, ext, this]
  · rcases List.mem_append.1 hb with hb | hb
    · exact hh.2 b hb
    · rw [List.mem_singleton.1 hb]; exact ⟨hs, ht⟩

end Points

section Data

variable (D : D7) (L : LatticeDataWithDual D) (Kd : KernelData D) (Lv : ℕ → AddSubgroup D.host.E)

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Establish `h2` using `isPt_ext hh hs ht`. Rewrite using `[ph_val h2]`. Use `show _ = (ph j h).1 ++ [(t, s)]`. Rewrite using `[ph_val hh]`.

Simplify using `[sw, ext]`.
-/
theorem ph_ext {j s : ℕ} {h : Pt D.host.E} {t : D.host.E} (hh : IsPt j h) (hs : 1 ≤ s) (ht : t ≠ 0) :
    ph (j + s) (ext h s t) = ptSnoc D (ph j h) t ht s hs := by
  apply Subtype.ext
  have h2 := isPt_ext hh hs ht
  rw [ph_val h2]
  show _ = (ph j h).1 ++ [(t, s)]
  rw [ph_val hh]
  simp [sw, ext]

def taData : Formalism.FourierDecayAlt.TA.Data D.host.E where
  r := D.R.rS
  K := fun i p p' => Kd.K i (ph i p') (ph i p)
  Th := fun i s t h h' => Kd.Th (i - s) s t (ph (i - s) h') (ph (i - s) h)
  e := Kd.e
  La := fun i s => (L.La (i - s + 1) s).toAddSubgroup
  Lf := fun i s => if i = D.R.rS + 1 ∧ s = 1 then ⊤ else (L.La' (i - s + 1) s).toAddSubgroup
  Lv := Lv

variable {D L Kd}

/- English proof (translation)
Use `⟨h.1 _ _, fun i hi P hP => ?_⟩` and prove the remaining obligations. Conclude with `pull_psd (h.2.1 i hi) P (ph i) unsw (fun x hx => unsw_ph (hP x hx))`.
-/
theorem axK_of_ArithAx (h : ArithAx D L Kd) : AxK (taData D L Kd Lv) := by
  refine ⟨h.1 _ _, fun i hi P hP => ?_⟩
  exact pull_psd (h.2.1 i hi) P (ph i) unsw (fun x hx => unsw_ph (hP x hx))

/- English proof (translation)
Introduce `i h1 h2` and use `h.2.2.1 i h1 h2`.
-/
theorem axE_of_ArithAx (h : ArithAx D L Kd) : AxE (taData D L Kd Lv) := fun i h1 h2 => h.2.2.1 i h1 h2

/- English proof (translation)
Introduce `i s hs hsi hi p p' t t' hp hp' ht ht' hor`. Take `⟨j, rfl⟩ : ∃ j, i = j + s` from `⟨i - s, by omega⟩`. Rewrite `hp`, `hp'` using `[Nat.add_sub_cancel]`. Use `show Kd.K (j + s) (ph (j + s) (ext p' s t')) (ph (j + s) (ext p s t)) = 0`. Rewrite using `[ph_ext D hp hs ht, ph_ext D hp' hs ht']`.

Assume the negation of the conclusion as `hne`. Establish `h2` using `h.2.2.2.1 j s hs hi (ph j p') (ph j p) t' t ht' ht hne`. Distinguish the cases in `htop : j + s = D.R.rS + 1 ∧ s = 1`. Rewrite `h2` using `[if_pos htop]`. Break down `hor with hor | hor` into its components or cases.

Apply `hor show _ ∈ (if j + s = D.R.rS + 1 ∧ s = 1 then (⊤ : AddSubgroup D.host.E) else _)` to reduce the goal to its premises. Rewrite using `[if_pos htop]`. Conclude with `AddSubgroup.mem_top _`. Conclude with `hor.2.2 h2.symm`. Rewrite `h2` using `[if_neg htop]`.

Break down `hor with hor | hor` into its components or cases. Apply `hor show _ ∈ (if j + s = D.R.rS + 1 ∧ s = 1 then (⊤ : AddSubgroup D.host.E) else _)` to reduce the goal to its premises. Rewrite using `[if_neg htop, Nat.add_sub_cancel, Submodule.mem_toAddSubgroup]`. Use `(L.La' (j + 1) s).neg_mem h2` as an intermediate fact. Establish `e : 1 / t - 1 / t' = -(t'⁻¹ - t⁻¹)` using `by simp only [one_div]; ring`.

Rewrite using `[e]`. Conclude with `this`. Conclude with `htop ⟨hor.1, hor.2.1⟩`.
-/
theorem arith_axiom_second_of_arith_axioms (h : ArithAx D L Kd) : KernelSupport (taData D L Kd Lv) := by
  intro i s hs hsi hi p p' t t' hp hp' ht ht' hor
  obtain ⟨j, rfl⟩ : ∃ j, i = j + s := ⟨i - s, by omega⟩
  rw [Nat.add_sub_cancel] at hp hp'
  show Kd.K (j + s) (ph (j + s) (ext p' s t')) (ph (j + s) (ext p s t)) = 0
  rw [ph_ext D hp hs ht, ph_ext D hp' hs ht']
  by_contra hne
  have h2 := h.2.2.2.1 j s hs hi (ph j p') (ph j p) t' t ht' ht hne
  by_cases htop : j + s = D.R.rS + 1 ∧ s = 1
  · rw [if_pos htop] at h2
    rcases hor with hor | hor
    · apply hor
      show _ ∈ (if j + s = D.R.rS + 1 ∧ s = 1 then (⊤ : AddSubgroup D.host.E) else _)
      rw [if_pos htop]; exact AddSubgroup.mem_top _
    · exact hor.2.2 h2.symm
  · rw [if_neg htop] at h2
    rcases hor with hor | hor
    · apply hor
      show _ ∈ (if j + s = D.R.rS + 1 ∧ s = 1 then (⊤ : AddSubgroup D.host.E) else _)
      rw [if_neg htop, Nat.add_sub_cancel, Submodule.mem_toAddSubgroup]
      have := (L.La' (j + 1) s).neg_mem h2
      have e : 1 / t - 1 / t' = -(t'⁻¹ - t⁻¹) := by simp only [one_div]; ring
      rw [e]; exact this
    · exact htop ⟨hor.1, hor.2.1⟩

/- English proof (translation)
Introduce `i s hs hsi hi`. Take `⟨j, rfl⟩ : ∃ j, i = j + s` from `⟨i - s, by omega⟩`. Take `⟨hdom, hper, hpsd, hsum⟩` from `h.2.2.2.2 j s hs hi`. Establish `e : j + s - s = j` using `by omega`. Use `⟨fun t Hd hHd => ?_, fun t l hl => ?_, fun t Hd ht hHd => ?_, fun R Hd hR hHd => ?_⟩` and prove the remaining obligations.

Use `show PSDOn Hd (fun p p' => Kd.Th (j + s - s) s t (ph (j + s - s) p') (ph (j + s - s) p))`. Rewrite `hHd`, the goal using `[e]`. Conclude with `pull_psd (hpsd t) Hd (ph j) unsw (fun x hx => unsw_ph (hHd x hx))`. Use `show (fun p p' => Kd.Th (j + s - s) s (t + l) (ph (j + s - s) p') (ph (j + s - s) p)) = fun p p' => Kd.Th (j + s - s) s t (ph (j + s - s) p') (ph (j + s - s) p)`. Establish `hl' : l ∈ L.La (j + 1) s`.

Establish `: l ∈ (L.La (j + s - s + 1) s).toAddSubgroup` using `hl`. Rewrite `this` using `[e, Submodule.mem_toAddSubgroup]`. Then use the resulting hypothesis. Rewrite using `[e, hper t l hl']`. Use `show PSDOn Hd (fun p p' => Kd.Th (j + s - s) s t (ph (j + s - s) p') (ph (j + s - s) p) - Kd.K (j + s) (ph (j + s) (ext p' s t)) (ph (j + s) (ext p s t)))`. Rewrite `hHd`, the goal using `[e]`.

Establish `h1` using `pull_psd (hdom t ht) Hd (ph j) unsw (fun x hx => unsw_ph (hHd x hx))`. Use `⟨fun x hx y hy => ?_, fun a => ?_⟩` and prove the remaining obligations. Use `h1.1 x hx y hy beta_reduce at this ⊢` as an intermediate fact. Rewrite using `[ph_ext D (hHd x hx) hs ht, ph_ext D (hHd y hy) hs ht]`. Conclude with `this`.

Use `h1.2 a` as an intermediate fact. Use `le_of_le_of_eq this ?_` and prove the remaining obligations. Use `congr 1`. Use `Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_` and prove the remaining obligations. Use `beta_reduce`.

Rewrite using `[ph_ext D (hHd x hx) hs ht, ph_ext D (hHd y hy) hs ht]`. Use `show PSDOn Hd (fun p p' => ((1 + Kd.e (j + s) : ℝ) : ℂ) * Kd.K (j + s - s) (ph (j + s - s) p') (ph (j + s - s) p) - ∑ t ∈ R, Kd.Th (j + s - s) s t (ph (j + s - s) p') (ph (j + s - s) p))`. Establish `hR' : ∀ t ∈ R, ∀ t' ∈ R, t - t' ∈ L.La (j + 1) s → t = t'` using `fun t ht t' ht' hm => by`. Use `hR t ht t' ht' ?_` and prove the remaining obligations. Use `show t - t' ∈ (L.La (j + s - s + 1) s).toAddSubgroup`.

Rewrite using `[e, Submodule.mem_toAddSubgroup]`. Conclude with `hm`. Rewrite `hHd`, the goal using `[e]`. Establish `h1` using `pull_psd (hsum R hR') Hd (ph j) unsw (fun x hx => unsw_ph (hHd x hx))`. Establish `e2 : ((1 + Kd.e (j + s) : ℝ) : ℂ) = 1 + (Kd.e (j + s) : ℂ)` using `by push_cast; ring`.

Rewrite using `[e2]`. Conclude with `h1`.
-/
theorem arith_axiom_thirteenth_of_arith_axioms (h : ArithAx D L Kd) : ThetaDomination (taData D L Kd Lv) := by
  intro i s hs hsi hi
  obtain ⟨j, rfl⟩ : ∃ j, i = j + s := ⟨i - s, by omega⟩
  obtain ⟨hdom, hper, hpsd, hsum⟩ := h.2.2.2.2 j s hs hi
  have e : j + s - s = j := by omega
  refine ⟨fun t Hd hHd => ?_, fun t l hl => ?_, fun t Hd ht hHd => ?_, fun R Hd hR hHd => ?_⟩
  · show PSDOn Hd (fun p p' => Kd.Th (j + s - s) s t (ph (j + s - s) p') (ph (j + s - s) p))
    rw [e] at hHd ⊢
    exact pull_psd (hpsd t) Hd (ph j) unsw (fun x hx => unsw_ph (hHd x hx))
  · show (fun p p' => Kd.Th (j + s - s) s (t + l) (ph (j + s - s) p') (ph (j + s - s) p)) =
      fun p p' => Kd.Th (j + s - s) s t (ph (j + s - s) p') (ph (j + s - s) p)
    have hl' : l ∈ L.La (j + 1) s := by
      have : l ∈ (L.La (j + s - s + 1) s).toAddSubgroup := hl
      rwa [e, Submodule.mem_toAddSubgroup] at this
    rw [e, hper t l hl']
  · show PSDOn Hd (fun p p' => Kd.Th (j + s - s) s t (ph (j + s - s) p') (ph (j + s - s) p) -
      Kd.K (j + s) (ph (j + s) (ext p' s t)) (ph (j + s) (ext p s t)))
    rw [e] at hHd ⊢
    have h1 := pull_psd (hdom t ht) Hd (ph j) unsw (fun x hx => unsw_ph (hHd x hx))
    refine ⟨fun x hx y hy => ?_, fun a => ?_⟩
    · have := h1.1 x hx y hy
      beta_reduce at this ⊢
      rw [ph_ext D (hHd x hx) hs ht, ph_ext D (hHd y hy) hs ht]
      exact this
    · have := h1.2 a
      refine le_of_le_of_eq this ?_
      congr 1
      refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_
      beta_reduce
      rw [ph_ext D (hHd x hx) hs ht, ph_ext D (hHd y hy) hs ht]
  · show PSDOn Hd (fun p p' => ((1 + Kd.e (j + s) : ℝ) : ℂ) * Kd.K (j + s - s) (ph (j + s - s) p') (ph (j + s - s) p) -
      ∑ t ∈ R, Kd.Th (j + s - s) s t (ph (j + s - s) p') (ph (j + s - s) p))
    have hR' : ∀ t ∈ R, ∀ t' ∈ R, t - t' ∈ L.La (j + 1) s → t = t' := fun t ht t' ht' hm => by
      refine hR t ht t' ht' ?_
      show t - t' ∈ (L.La (j + s - s + 1) s).toAddSubgroup
      rw [e, Submodule.mem_toAddSubgroup]; exact hm
    rw [e] at hHd ⊢
    have h1 := pull_psd (hsum R hR') Hd (ph j) unsw (fun x hx => unsw_ph (hHd x hx))
    have e2 : ((1 + Kd.e (j + s) : ℝ) : ℂ) = 1 + (Kd.e (j + s) : ℂ) := by push_cast; ring
    rw [e2]
    exact h1

/- English proof (translation)
Establish `h1` using `pull_psd (h R) P (ph (D.R.rS + 1)) unsw (fun x hx => unsw_ph (hP x hx))`. Establish `e : (fun p p' : Pt D.host.E => (taData D L Kd Lv).K ((taData D L Kd Lv).r + 1) p p' - ∑ x ∈ R, conj (c x (ph (D.R.rS + 1) p)) * c x (ph (D.R.rS + 1) p')) = fun x y => Kd.K (D.R.rS + 1) (ph (D.R.rS + 1) y) (ph (D.R.rS + 1) x) - ∑ ρ ∈ R, c ρ (ph (D.R.rS + 1) y) * star (c ρ (ph (D.R …`. Use function extensionality and compare the values at `p p'`. Use `show Kd.K (D.R.rS + 1) (ph (D.R.rS + 1) p') (ph (D.R.rS + 1) p) - _ = _`. Use `congr 1`.

Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.star_def, mul_comm]`. Rewrite using `[e]`. Conclude with `h1`.
-/
theorem rows_of_KLE {ι : Type} (c : ι → Point D.host.E (D.R.rS + 1) → ℂ)
    (h : ∀ R : Finset ι, KLE (fun p p' => ∑ ρ ∈ R, c ρ p * star (c ρ p')) (Kd.K (D.R.rS + 1)))
    (P : Finset (Pt D.host.E)) (R : Finset ι) (hP : ∀ p ∈ P, IsPt ((taData D L Kd Lv).r + 1) p) :
    PSDOn P (fun p p' => (taData D L Kd Lv).K ((taData D L Kd Lv).r + 1) p p' -
      ∑ x ∈ R, conj (c x (ph (D.R.rS + 1) p)) * c x (ph (D.R.rS + 1) p')) := by
  have h1 := pull_psd (h R) P (ph (D.R.rS + 1)) unsw (fun x hx => unsw_ph (hP x hx))
  have e : (fun p p' : Pt D.host.E => (taData D L Kd Lv).K ((taData D L Kd Lv).r + 1) p p' -
      ∑ x ∈ R, conj (c x (ph (D.R.rS + 1) p)) * c x (ph (D.R.rS + 1) p')) =
      fun x y => Kd.K (D.R.rS + 1) (ph (D.R.rS + 1) y) (ph (D.R.rS + 1) x) -
        ∑ ρ ∈ R, c ρ (ph (D.R.rS + 1) y) * star (c ρ (ph (D.R.rS + 1) x)) := by
    funext p p'
    show Kd.K (D.R.rS + 1) (ph (D.R.rS + 1) p') (ph (D.R.rS + 1) p) - _ = _
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Complex.star_def, mul_comm]
  rw [e]
  exact h1

end Data

end Formalism.MainNotions.InterlacingSignCuts

end

end PartAAx

section PartASz

open NumberField Finset
open scoped nonZeroDivisors

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.FourierDecayAlt.TA

attribute [local instance] Classical.propDecidable

/- English proof (translation)
Take `⟨n, rfl⟩ : ∃ n, s = n + 1` from `⟨s - 1, by omega⟩`. Establish `hn : n ≠ 0` using `by omega`. Simplify using `only [Nat.add_sub_cancel] at hB ⊢`. Establish `hpi0 : 0 ≤ Real.pi` using `Real.pi_pos.le`. Establish `hpi4 : Real.pi ≤ 4` using `Real.pi_le_four`.

Establish `hC40 : 0 ≤ C4` using `by linarith`. Use `set q : ℝ := Real.pi ^ f * Y ^ 2 with hq`. Establish `hq0 : 0 ≤ q` using `by positivity`. Establish `hc1 : 1 ≤ C4 ^ f` using `one_le_pow₀ hC4`. Establish `h1 : u * w * B ≤ 4 * (C4 ^ (f * (n + 1)) * q ^ n)`.

Establish `h2 : u * w ≤ 4` using `by nlinarith`. Combine the equalities or inequalities in the displayed calculation. Establish `h3 : C4 ^ (f * (n + 1)) = C4 ^ f * (C4 ^ f) ^ n`. Rewrite using `[← pow_mul, ← pow_add]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Establish `h4 : 4 * C4 ^ f ≤ (4 * C4 ^ f) ^ n` using `le_self_pow₀ (by linarith) hn`. Establish `h5 : 4 * (C4 ^ (f * (n + 1)) * q ^ n) ≤ (4 * C4 ^ f * C4 ^ f * q) ^ n`. Rewrite using `[h3]`. Combine the equalities or inequalities in the displayed calculation.

Establish `h6 : 4 * C4 ^ f * C4 ^ f * q ≤ (C0 ^ f * Y) ^ 2`. Establish `h7 : (4 * C4) ^ f ≤ C0 ^ f` using `pow_le_pow_left₀ (by linarith) hC0 f`. Establish `h8 : (4 : ℝ) ≤ 4 ^ f` using `le_self_pow₀ (by norm_num) (by omega)`. Establish `h9 : Real.pi ^ f ≤ 4 ^ f` using `pow_le_pow_left₀ hpi0 hpi4 f`. Establish `h10 : 4 * Real.pi ^ f ≤ (4 : ℝ) ^ f * 4 ^ f` using `mul_le_mul h8 h9 (by positivity) (by positivity)`.

Establish `h11 : 4 * C4 ^ f * C4 ^ f * Real.pi ^ f ≤ ((4 * C4) ^ f) ^ 2`. Rewrite using `[mul_pow, mul_pow, sq, sq]`. Establish `: 0 ≤ C4 ^ f * C4 ^ f` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Establish `h12 : ((4 * C4) ^ f) ^ 2 ≤ (C0 ^ f) ^ 2` using `pow_le_pow_left₀ (by positivity) h7 2`.

Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
theorem num_block {C4 C0 Y u w B : ℝ} {f s : ℕ} (hC4 : 1 ≤ C4) (hC0 : 4 * C4 ≤ C0) (hY : 0 ≤ Y) (hf : 1 ≤ f) (hs : 2 ≤ s)
    (hu0 : 0 ≤ u) (hu : u ≤ 2) (hw0 : 0 ≤ w) (hw : w ≤ 2) (hB0 : 0 ≤ B)
    (hB : B ≤ C4 ^ (f * s) * (Real.pi ^ f * Y ^ 2) ^ (s - 1)) :
    u * w * B ≤ (C0 ^ f * Y) ^ (2 * (s - 1)) := by
  obtain ⟨n, rfl⟩ : ∃ n, s = n + 1 := ⟨s - 1, by omega⟩
  have hn : n ≠ 0 := by omega
  simp only [Nat.add_sub_cancel] at hB ⊢
  have hpi0 : 0 ≤ Real.pi := Real.pi_pos.le
  have hpi4 : Real.pi ≤ 4 := Real.pi_le_four
  have hC40 : 0 ≤ C4 := by linarith
  set q : ℝ := Real.pi ^ f * Y ^ 2 with hq
  have hq0 : 0 ≤ q := by positivity
  have hc1 : 1 ≤ C4 ^ f := one_le_pow₀ hC4
  have h1 : u * w * B ≤ 4 * (C4 ^ (f * (n + 1)) * q ^ n) := by
    have h2 : u * w ≤ 4 := by nlinarith
    calc u * w * B ≤ 4 * B := mul_le_mul_of_nonneg_right h2 hB0
      _ ≤ 4 * (C4 ^ (f * (n + 1)) * q ^ n) := by linarith
  have h3 : C4 ^ (f * (n + 1)) = C4 ^ f * (C4 ^ f) ^ n := by
    rw [← pow_mul, ← pow_add]; congr 1; ring
  have h4 : 4 * C4 ^ f ≤ (4 * C4 ^ f) ^ n := le_self_pow₀ (by linarith) hn
  have h5 : 4 * (C4 ^ (f * (n + 1)) * q ^ n) ≤ (4 * C4 ^ f * C4 ^ f * q) ^ n := by
    rw [h3]
    calc 4 * (C4 ^ f * (C4 ^ f) ^ n * q ^ n) = (4 * C4 ^ f) * ((C4 ^ f) ^ n * q ^ n) := by ring
      _ ≤ (4 * C4 ^ f) ^ n * ((C4 ^ f) ^ n * q ^ n) := mul_le_mul_of_nonneg_right h4 (by positivity)
      _ = (4 * C4 ^ f * C4 ^ f * q) ^ n := by ring
  have h6 : 4 * C4 ^ f * C4 ^ f * q ≤ (C0 ^ f * Y) ^ 2 := by
    have h7 : (4 * C4) ^ f ≤ C0 ^ f := pow_le_pow_left₀ (by linarith) hC0 f
    have h8 : (4 : ℝ) ≤ 4 ^ f := le_self_pow₀ (by norm_num) (by omega)
    have h9 : Real.pi ^ f ≤ 4 ^ f := pow_le_pow_left₀ hpi0 hpi4 f
    have h10 : 4 * Real.pi ^ f ≤ (4 : ℝ) ^ f * 4 ^ f := mul_le_mul h8 h9 (by positivity) (by positivity)
    have h11 : 4 * C4 ^ f * C4 ^ f * Real.pi ^ f ≤ ((4 * C4) ^ f) ^ 2 := by
      rw [mul_pow, mul_pow, sq, sq]
      have : 0 ≤ C4 ^ f * C4 ^ f := by positivity
      nlinarith
    have h12 : ((4 * C4) ^ f) ^ 2 ≤ (C0 ^ f) ^ 2 := pow_le_pow_left₀ (by positivity) h7 2
    calc 4 * C4 ^ f * C4 ^ f * q = (4 * C4 ^ f * C4 ^ f * Real.pi ^ f) * Y ^ 2 := by rw [hq]; ring
      _ ≤ (C0 ^ f) ^ 2 * Y ^ 2 := mul_le_mul_of_nonneg_right (le_trans h11 h12) (by positivity)
      _ = (C0 ^ f * Y) ^ 2 := by rw [mul_pow]
  calc u * w * B ≤ (4 * C4 ^ f * C4 ^ f * q) ^ n := le_trans h1 h5
    _ ≤ ((C0 ^ f * Y) ^ 2) ^ n := pow_le_pow_left₀ (by positivity) h6 n
    _ = (C0 ^ f * Y) ^ (2 * n) := by rw [← pow_mul]

/- English proof (translation)
Rewrite using `[sq]`. Conclude with `mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)`.
-/
theorem num_first {X Y' ep : ℝ} (hX0 : 0 ≤ X) (hX : X ≤ ep) (hY0 : 0 ≤ Y') (hY : Y' ≤ ep) :
    (1 + X) * (1 + Y') ≤ (1 + ep) ^ 2 := by
  rw [sq]
  exact mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)

section Sizes

variable (D : D7) (C1 C2 N T T' : ℝ) (δ : D.host.E) (x : D.what₂.Tau → LocalDataRealPlace D) (L : LatticeDataWithDual D) (K : ℕ)

def szX (i : ℕ) (v : D.what₂.Tau) : ℝ := xSz D C1 C2 N (kaV D δ v) T T' (x v) i
def szL (b s : ℕ) (v : D.what₂.Tau) : ℝ := LamSz D C1 C2 N (kaV D δ v) T T' (x v) b s
def szP (b : ℕ) (v : D.what₂.Tau) : ℝ := LamPSz D C1 C2 N (kaV D δ v) T T' (x v) b

def szG (b s' : ℕ) (v : D.what₂.Tau) : ℝ := if s' = 1 then szX D C1 C2 N T T' δ x b v else szL D C1 C2 N T T' δ x b s' v

def thr3 (i s : ℕ) (v : D.what₂.Tau) : ℝ :=
  if i ≤ D.R.rS then szL D C1 C2 N T T' δ x (i - s + 1) (s + 1) v else 2 * szP D C1 C2 N T T' δ x (i - s + 1) v

def prof1 (i : ℕ) (l : D.host.E) : ℝ := ∏ v, minFac (szX D C1 C2 N T T' δ x i v) ‖plEmb D v l‖ K
def prof3 (i s : ℕ) (l : D.host.E) : ℝ := ∏ v, minFac (thr3 D C1 C2 N T T' δ x i s v) ‖plEmb D v l‖ K

def volB (b s' : ℕ) : ℝ := (∏ v, szG D C1 C2 N T T' δ x b s' v) ^ 2 / nrmHalf D (L.aaV b s') ^ 2

def bdB (C4 : ℝ) (i s : ℕ) : ℝ :=
  C4 ^ (D.R.f * s) * ∏ s' ∈ Ico 1 s, (Real.pi ^ D.R.f * volB D C1 C2 N T T' δ x L (i - s + 1) s')

structure SzOK (Lv : ℕ → AddSubgroup D.host.E) : Prop where
  x_pos : ∀ i v, 0 < szX D C1 C2 N T T' δ x i v
  l_pos : ∀ b s v, 0 < szL D C1 C2 N T T' δ x b s v
  p_pos : ∀ b v, 0 < szP D C1 C2 N T T' δ x b v
  aaV_ne : ∀ b s, IsBlockSL2Embedding D b s → L.aaV b s ≠ 0
  aaP_ne : ∀ b s, IsBlockSL2Embedding D b s → L.aaP b s ≠ 0
  lift_mem : ∀ b s, IsBlockSL2Embedding D b s → ∀ l ∈ L.La' b s, l ∈ L.aaP b s
  dual_mem : ∀ i, 1 ≤ i → i ≤ D.R.rS + 1 → ∀ l ∈ Lv i, l ∈ L.aaV i 1

variable {D C1 C2 N T T' δ x L}

/- English proof (translation)
Use `lt_of_lt_of_le ?_ (x_le_ThInvF D C1 C2 N T T' δ x L 1 le_rfl (by omega))` and prove the remaining obligations. Conclude with `div_pos (Finset.prod_pos fun v _ => h.x_pos 1 v) (nrmHalf_pos D _ (h.aaV_ne 1 1 ⟨le_rfl, le_rfl, by omega⟩))`.
-/
theorem ThInvF_pos {Lv : ℕ → AddSubgroup D.host.E} (h : SzOK D C1 C2 N T T' δ x L Lv) :
    0 < ThInvF D C1 C2 N T T' δ x L := by
  refine lt_of_lt_of_le ?_ (x_le_ThInvF D C1 C2 N T T' δ x L 1 le_rfl (by omega))
  exact div_pos (Finset.prod_pos fun v _ => h.x_pos 1 v)
    (nrmHalf_pos D _ (h.aaV_ne 1 1 ⟨le_rfl, le_rfl, by omega⟩))

/- English proof (translation)
Establish `hnV` using `nrmHalf_pos D _ (h.aaV_ne b s' ⟨hb, hs, hbs⟩)`. Establish `hP : 0 < ∏ v, szG D C1 C2 N T T' δ x b s' v` using `Finset.prod_pos fun v _ => by`. Unfold `szG`. Use `split_ifs`. Conclude with `h.x_pos b v`.

Conclude with `h.l_pos b s' v`. Use `⟨by unfold volB; positivity, ?_⟩` and prove the remaining obligations. Establish `hq : (∏ v, szG D C1 C2 N T T' δ x b s' v) / nrmHalf D (L.aaV b s') ≤ ThInvF D C1 C2 N T T' δ x L`. Distinguish the cases in `h1 : s' = 1`. Substitute `h1` using the available equality.

Use `x_le_ThInvF D C1 C2 N T T' δ x L b hb (by omega)` as an intermediate fact. Simplify `this` using `[szG, szX]`. Establish `hs2 : 2 ≤ s'` using `by omega`. Establish `hnP` using `nrmHalf_pos D _ (h.aaP_ne b (s' - 1) ⟨hb, by omega, by omega⟩)`. Establish `h2` using `Lam_le_ThInvF D C1 C2 N T T' δ x L b s' hb hs2 hbs`.

Establish `h3 : (∏ v, szG D C1 C2 N T T' δ x b s' v) = ∏ v, LamSz D C1 C2 N (kaV D δ v) T T' (x v) b s'` using `Finset.prod_congr rfl fun v _ => by simp [szG, h1, szL]`. Rewrite `hP`, the goal using `[h3]`. Conclude with `le_trans (div_le_div_of_nonneg_left hP.le (lt_min hnV hnP) (min_le_left _ _)) h2`. Unfold `volB`. Rewrite using `[← div_pow]`.

Conclude with `pow_le_pow_left₀ (div_pos hP hnV).le hq 2`.
-/
theorem volB_le {Lv : ℕ → AddSubgroup D.host.E} (h : SzOK D C1 C2 N T T' δ x L Lv) (b s' : ℕ) (hb : 1 ≤ b) (hs : 1 ≤ s')
    (hbs : b - 1 + s' ≤ D.R.rS + 1) :
    0 ≤ volB D C1 C2 N T T' δ x L b s' ∧ volB D C1 C2 N T T' δ x L b s' ≤ ThInvF D C1 C2 N T T' δ x L ^ 2 := by
  have hnV := nrmHalf_pos D _ (h.aaV_ne b s' ⟨hb, hs, hbs⟩)
  have hP : 0 < ∏ v, szG D C1 C2 N T T' δ x b s' v := Finset.prod_pos fun v _ => by
    unfold szG; split_ifs
    · exact h.x_pos b v
    · exact h.l_pos b s' v
  refine ⟨by unfold volB; positivity, ?_⟩
  have hq : (∏ v, szG D C1 C2 N T T' δ x b s' v) / nrmHalf D (L.aaV b s') ≤ ThInvF D C1 C2 N T T' δ x L := by
    by_cases h1 : s' = 1
    · subst h1
      have := x_le_ThInvF D C1 C2 N T T' δ x L b hb (by omega)
      simpa [szG, szX] using this
    · have hs2 : 2 ≤ s' := by omega
      have hnP := nrmHalf_pos D _ (h.aaP_ne b (s' - 1) ⟨hb, by omega, by omega⟩)
      have h2 := Lam_le_ThInvF D C1 C2 N T T' δ x L b s' hb hs2 hbs
      have h3 : (∏ v, szG D C1 C2 N T T' δ x b s' v) = ∏ v, LamSz D C1 C2 N (kaV D δ v) T T' (x v) b s' :=
        Finset.prod_congr rfl fun v _ => by simp [szG, h1, szL]
      rw [h3] at hP ⊢
      exact le_trans (div_le_div_of_nonneg_left hP.le (lt_min hnV hnP) (min_le_left _ _)) h2
  unfold volB
  rw [← div_pow]
  exact pow_le_pow_left₀ (div_pos hP hnV).le hq 2

end Sizes

/- English proof (translation)
Take `⟨C, hC0, hC⟩` from `latSum_of_core`. Establish `hKr : (4 : ℝ) ≤ (K : ℝ)` using `by exact_mod_cast hK`. Use `set E : ℝ := (K : ℝ) - 5 / 2 with hE`. Establish `hE1 : 1 ≤ E` using `by rw [hE]; linarith`. Use `set B2 : ℝ := (2 : ℝ) ^ E with hB2`.

Establish `hB21 : 1 ≤ B2` using `Real.one_le_rpow (by norm_num) (by linarith)`. Use `⟨4 * C4 + 3 * C * B2 + 1, by nlinarith [mul_nonneg hC0 (by linarith : (0 : ℝ) ≤ B2)], ?_⟩` and prove the remaining obligations. Introduce `D C1 C2 N T T' δ x L Kd Lv hAx hOK hΘC hΘ4`. Use `set C0 : ℝ := 4 * C4 + 3 * C * B2 + 1 with hC0def`. Use `set Θ : ℝ := ThS D C1 C2 N T T' δ x L with hΘ`.

Establish `hCB : 0 ≤ C * B2` using `mul_nonneg hC0 (by linarith)`. Establish `hC01 : 1 ≤ C0` using `by rw [hC0def]; nlinarith`. Establish `hΘ0 : 0 < Θ` using `by linarith`. Use `set A : ℝ := Θ ^ (-E) with hA`. Establish `hA0 : 0 ≤ A` using `Real.rpow_nonneg hΘ0.le _`.

Establish `hhalf : (Θ / 2) ^ (-E) = A * B2`. Rewrite using `[Real.div_rpow hΘ0.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]`. Establish `hf` using `f_pos D`. Establish `hY` using `ThInvF_pos hOK`. Use `set Y : ℝ := ThInvF D C1 C2 N T T' δ x L with hYdef`.

Establish `hΘf : Θ ^ D.R.f = Y⁻¹` using `ThS_pow D C1 C2 N T T' δ x L hY`. Establish `hA1 : C0 * A ≤ 1`. Establish `h1 : A ≤ Θ ^ (-(1 : ℝ))` using `Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)`. Rewrite `h1` using `[Real.rpow_neg_one]`. Combine the equalities or inequalities in the displayed calculation.

Use `set ep : ℝ := (C0 * A) ^ D.R.f with hep`. Establish `hep0 : 0 ≤ ep` using `by positivity`. Establish `hep1 : ep ≤ 1` using `pow_le_one₀ (by positivity) hA1`. Use `set ep1 : ℝ := (C * A) ^ D.R.f with hep1def`. Use `set ep3 : ℝ := (C * (Θ / 2) ^ (-E)) ^ D.R.f with hep3def`.

Establish `hcard : (Fintype.card (D.what₂.Tau → Option Bool) : ℝ) = 3 ^ D.R.f`. Simplify using `[D.what₂.card_Tau]`. Establish `hep3_0 : 0 ≤ ep3` using `by rw [hep3def, hhalf]; positivity`. Establish `h3ep : (Fintype.card (D.what₂.Tau → Option Bool) : ℝ) * ep3 ≤ ep`. Rewrite using `[hcard, hep3def, hhalf, ← mul_pow]`.

Use `pow_le_pow_left₀ (by positivity) ?_ _` and prove the remaining obligations. Establish `: 3 * (C * (A * B2)) = (3 * C * B2) * A` using `by ring`. Rewrite using `[this]`. Conclude with `mul_le_mul_of_nonneg_right (by rw [hC0def]; linarith) hA0`. Establish `h3ep0 : 0 ≤ (Fintype.card (D.what₂.Tau → Option Bool) : ℝ) * ep3` using `by positivity`.

Establish `hep1le : ep1 ≤ ep`. Use `pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right ?_ hA0) _` and prove the remaining obligations. Rewrite using `[hC0def]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hep1_0 : 0 ≤ ep1` using `by positivity`.

Establish `ha : (C0 / Θ) ^ D.R.f = C0 ^ D.R.f * Y`. Rewrite using `[div_pow, hΘf, div_inv_eq_mul]`. Use `⟨ep1, ep3, fun i hi => ?_⟩` and prove the remaining obligations. Take `⟨hi1, hi2⟩` from `Finset.mem_Icc.1 hi`. Use `⟨⟨fun l => ?_, fun S hS => ?_⟩, fun s hs hnt => ⟨fun l => ?_, fun S hS => ?_⟩, hep3_0, ?_, fun s hs => ?_⟩` and prove the remaining obligations.

Conclude with `Finset.prod_nonneg fun v _ => minFac_nonneg _ _ (hOK.x_pos i v).le (norm_nonneg _) K`. Establish `haa` using `hOK.aaV_ne i 1 ⟨hi1, le_rfl, by omega⟩`. Conclude with `hC D _ haa _ Θ K (hOK.x_pos i) (by linarith) (by omega) (ThS_pow_le D C1 C2 N T T' δ x L (Finset.prod_pos fun v _ => hOK.x_pos i v) (nrmHalf_pos D _ haa) (x_le_ThInvF D C1 C2 N T T' δ x L i hi1 hi2)) S (fun l hl => ⟨hOK.dual_mem i hi1 hi2 l (hS l hl).1, (hS l hl).2⟩)`. Use `Finset.prod_nonneg fun v _ => minFac_nonneg _ _ ?_ (norm_nonneg _) K` and prove the remaining obligations. Unfold `thr3`.

Use `split_ifs`. Conclude with `(hOK.l_pos _ _ v).le`. Conclude with `(mul_pos two_pos (hOK.p_pos _ v)).le`. Take `⟨hs1, hs2⟩` from `Finset.mem_Icc.1 hs`. Establish `hnt' : ¬ (i = D.R.rS + 1 ∧ s = 1)` using `hnt`.

Establish `hblk : IsBlockSL2Embedding D (i - s + 1) s` using `⟨by omega, hs1, by omega⟩`. Establish `haP` using `hOK.aaP_ne _ _ hblk`. Establish `hnP` using `nrmHalf_pos D _ haP`. Establish `hmem : ∀ l ∈ S, l ∈ L.aaP (i - s + 1) s ∧ l ≠ 0` using `fun l hl => by`. Use `⟨hOK.lift_mem _ _ hblk l ?_, (hS l hl).2⟩` and prove the remaining obligations.

Establish `h1 : l ∈ (if i = D.R.rS + 1 ∧ s = 1 then (⊤ : AddSubgroup D.host.E) else (L.La' (i - s + 1) s).toAddSubgroup)` using `(hS l hl).1`. Rewrite `h1` using `[if_neg hnt', Submodule.mem_toAddSubgroup]`. Conclude with `h1`. Establish `hpos : ∀ v, 0 < thr3 D C1 C2 N T T' δ x i s v` using `fun v => by`. Unfold `thr3`.

Use `split_ifs`. Conclude with `hOK.l_pos _ _ v`. Conclude with `mul_pos two_pos (hOK.p_pos _ v)`. Use `hC D _ haP _ (Θ / 2) K hpos (by linarith) (by omega) ?_ S hmem` and prove the remaining obligations. Distinguish the cases in `hir : i ≤ D.R.rS`.

Establish `hnV` using `nrmHalf_pos D _ (hOK.aaV_ne (i - s + 1) (s + 1) ⟨by omega, by omega, by omega⟩)`. Establish `hP : 0 < ∏ v, LamSz D C1 C2 N (kaV D δ v) T T' (x v) (i - s + 1) (s + 1)` using `Finset.prod_pos fun v _ => hOK.l_pos _ _ v`. Establish `e1 : (∏ v, thr3 D C1 C2 N T T' δ x i s v) = ∏ v, LamSz D C1 C2 N (kaV D δ v) T T' (x v) (i - s + 1) (s + 1)` using `Finset.prod_congr rfl fun v _ => by simp [thr3, hir, szL]`. Rewrite using `[e1]`. Establish `h2` using `Lam_le_ThInvF D C1 C2 N T T' δ x L (i - s + 1) (s + 1) (by omega) (by omega) (by omega)`.

Rewrite `h2` using `[Nat.add_sub_cancel]`. Establish `h3` using `ThS_pow_le D C1 C2 N T T' δ x L hP hnP (le_trans (div_le_div_of_nonneg_left hP.le (lt_min hnV hnP) (min_le_right _ _)) h2)`. Use `le_trans (pow_le_pow_left₀ (by linarith) (by linarith) _) h3` and prove the remaining obligations. Establish `hi3 : i = D.R.rS + 1` using `by omega`. Establish `hs3 : 2 ≤ s`.

Assume the negation of the conclusion as `hc`. Conclude with `hnt' ⟨hi3, by omega⟩`. Establish `hP : 0 < ∏ v, LamPSz D C1 C2 N (kaV D δ v) T T' (x v) (i - s + 1)` using `Finset.prod_pos fun v _ => hOK.p_pos _ v`. Establish `e1 : (∏ v, thr3 D C1 C2 N T T' δ x i s v) = 2 ^ D.R.f * ∏ v, LamPSz D C1 C2 N (kaV D δ v) T T' (x v) (i - s + 1)`. Rewrite using `[← D.what₂.card_Tau, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]`.

Conclude with `Finset.prod_congr rfl fun v _ => by simp [thr3, hir, szP]`. Rewrite using `[e1]`. Establish `h2` using `prod_div_norm_le_sup D C1 C2 N T T' δ x L (i - s + 1) (by omega) (by omega)`. Establish `e2 : D.R.rS + 2 - (i - s + 1) = s` using `by omega`. Rewrite `h2` using `[e2]`.

Establish `h3` using `ThS_pow_le D C1 C2 N T T' δ x L hP hnP h2`. Rewrite using `[div_pow, div_mul_eq_div_div_swap]`. Conclude with `div_le_div_of_nonneg_right h3 (by positivity)`. Conclude with `num_first h3ep0 h3ep hep1_0 hep1le`. Take `⟨hs1, hs2⟩` from `Finset.mem_Icc.1 hs`.

Establish `he` using `hAx.2.2.1 i hi1 hi2`. Establish `hvol : ∀ s' ∈ Ico 1 s, 0 ≤ Real.pi ^ D.R.f * volB D C1 C2 N T T' δ x L (i - s + 1) s' ∧ Real.pi ^ D.R.f * volB D C1 C2 N T T' δ x L (i - s + 1) s' ≤ Real.pi ^ D.R.f * Y ^ 2` using `fun s' hs' => by`. Take `⟨h1, h2⟩` from `Finset.mem_Ico.1 hs'`. Establish `h3` using `volB_le hOK (i - s + 1) s' (by omega) h1 (by omega)`. Establish `hpi : 0 ≤ Real.pi ^ D.R.f` using `by positivity`.

Conclude with `⟨mul_nonneg hpi h3.1, mul_le_mul_of_nonneg_left h3.2 hpi⟩`. Establish `hprod0 : 0 ≤ ∏ s' ∈ Ico 1 s, (Real.pi ^ D.R.f * volB D C1 C2 N T T' δ x L (i - s + 1) s')` using `Finset.prod_nonneg fun s' hs' => (hvol s' hs').1`. Establish `hprod : ∏ s' ∈ Ico 1 s, (Real.pi ^ D.R.f * volB D C1 C2 N T T' δ x L (i - s + 1) s') ≤ (Real.pi ^ D.R.f * Y ^ 2) ^ (s - 1)`. Use `Finset.prod_le_prod (fun s' hs' => (hvol s' hs').1) (fun s' hs' => (hvol s' hs').2)` as an intermediate fact. Simplify using `using this`.

Establish `hC4p : 0 ≤ C4 ^ (D.R.f * s)` using `by positivity`. Establish `hB0 : 0 ≤ bdB D C1 C2 N T T' δ x L C4 i s` using `mul_nonneg hC4p hprod0`. Use `⟨hB0, ?_⟩` and prove the remaining obligations. Rewrite using `[ha]`. Use `num_block hC4 (by rw [hC0def]; linarith) hY.le hf hs1 (by linarith) (by linarith) ?_ ?_ hB0 (mul_le_mul_of_nonneg_left hprod hC4p)` and prove the remaining obligations.

Use `show 0 ≤ 1 + Kd.e i`. Combine the linear relations using `[he.1]`. Use `show 1 + Kd.e i ≤ 2`. Combine the linear relations using `[he.2]`.
-/
theorem levelSizes_of_ThS (K : ℕ) (hK : 4 ≤ K) (C4 : ℝ) (hC4 : 1 ≤ C4) : ∃ C0 : ℝ, 1 ≤ C0 ∧
    ∀ (D : D7) (C1 C2 N T T' : ℝ) (δ : D.host.E) (x : D.what₂.Tau → LocalDataRealPlace D) (L : LatticeDataWithDual D) (Kd : KernelData D)
      (Lv : ℕ → AddSubgroup D.host.E), ArithAx D L Kd → SzOK D C1 C2 N T T' δ x L Lv →
      C0 ≤ ThS D C1 C2 N T T' δ x L → 4 < ThS D C1 C2 N T T' δ x L →
      ∃ ep1 ep3 : ℝ, ∀ i ∈ Icc 1 (D.R.rS + 1),
        LevelSizes (taData D L Kd Lv) (D.what₂.Tau → Option Bool) (prof1 D C1 C2 N T T' δ x K i)
          (prof3 D C1 C2 N T T' δ x K i) ep1 (fun _ => ep3) (bdB D C1 C2 N T T' δ x L C4 i)
          ((C0 * ThS D C1 C2 N T T' δ x L ^ (-((K : ℝ) - 5 / 2))) ^ D.R.f)
          ((C0 / ThS D C1 C2 N T T' δ x L) ^ D.R.f) i := by
  obtain ⟨C, hC0, hC⟩ := latSum_of_core
  have hKr : (4 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  set E : ℝ := (K : ℝ) - 5 / 2 with hE
  have hE1 : 1 ≤ E := by rw [hE]; linarith
  set B2 : ℝ := (2 : ℝ) ^ E with hB2
  have hB21 : 1 ≤ B2 := Real.one_le_rpow (by norm_num) (by linarith)
  refine ⟨4 * C4 + 3 * C * B2 + 1, by nlinarith [mul_nonneg hC0 (by linarith : (0 : ℝ) ≤ B2)], ?_⟩
  intro D C1 C2 N T T' δ x L Kd Lv hAx hOK hΘC hΘ4
  set C0 : ℝ := 4 * C4 + 3 * C * B2 + 1 with hC0def
  set Θ : ℝ := ThS D C1 C2 N T T' δ x L with hΘ
  have hCB : 0 ≤ C * B2 := mul_nonneg hC0 (by linarith)
  have hC01 : 1 ≤ C0 := by rw [hC0def]; nlinarith
  have hΘ0 : 0 < Θ := by linarith
  set A : ℝ := Θ ^ (-E) with hA
  have hA0 : 0 ≤ A := Real.rpow_nonneg hΘ0.le _
  have hhalf : (Θ / 2) ^ (-E) = A * B2 := by
    rw [Real.div_rpow hΘ0.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]
  have hf := f_pos D
  have hY := ThInvF_pos hOK
  set Y : ℝ := ThInvF D C1 C2 N T T' δ x L with hYdef
  have hΘf : Θ ^ D.R.f = Y⁻¹ := ThS_pow D C1 C2 N T T' δ x L hY

  have hA1 : C0 * A ≤ 1 := by
    have h1 : A ≤ Θ ^ (-(1 : ℝ)) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    rw [Real.rpow_neg_one] at h1
    calc C0 * A ≤ C0 * Θ⁻¹ := mul_le_mul_of_nonneg_left h1 (by linarith)
      _ ≤ Θ * Θ⁻¹ := mul_le_mul_of_nonneg_right hΘC (inv_nonneg.2 hΘ0.le)
      _ = 1 := mul_inv_cancel₀ hΘ0.ne'
  set ep : ℝ := (C0 * A) ^ D.R.f with hep
  have hep0 : 0 ≤ ep := by positivity
  have hep1 : ep ≤ 1 := pow_le_one₀ (by positivity) hA1
  set ep1 : ℝ := (C * A) ^ D.R.f with hep1def
  set ep3 : ℝ := (C * (Θ / 2) ^ (-E)) ^ D.R.f with hep3def
  have hcard : (Fintype.card (D.what₂.Tau → Option Bool) : ℝ) = 3 ^ D.R.f := by
    simp [D.what₂.card_Tau]
  have hep3_0 : 0 ≤ ep3 := by rw [hep3def, hhalf]; positivity
  have h3ep : (Fintype.card (D.what₂.Tau → Option Bool) : ℝ) * ep3 ≤ ep := by
    rw [hcard, hep3def, hhalf, ← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    have : 3 * (C * (A * B2)) = (3 * C * B2) * A := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right (by rw [hC0def]; linarith) hA0
  have h3ep0 : 0 ≤ (Fintype.card (D.what₂.Tau → Option Bool) : ℝ) * ep3 := by positivity
  have hep1le : ep1 ≤ ep := by
    refine pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right ?_ hA0) _
    rw [hC0def]; nlinarith
  have hep1_0 : 0 ≤ ep1 := by positivity
  have ha : (C0 / Θ) ^ D.R.f = C0 ^ D.R.f * Y := by
    rw [div_pow, hΘf, div_inv_eq_mul]
  refine ⟨ep1, ep3, fun i hi => ?_⟩
  obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.1 hi
  refine ⟨⟨fun l => ?_, fun S hS => ?_⟩, fun s hs hnt => ⟨fun l => ?_, fun S hS => ?_⟩, hep3_0, ?_, fun s hs => ?_⟩
  · exact Finset.prod_nonneg fun v _ => minFac_nonneg _ _ (hOK.x_pos i v).le (norm_nonneg _) K
  ·
    have haa := hOK.aaV_ne i 1 ⟨hi1, le_rfl, by omega⟩
    exact hC D _ haa _ Θ K (hOK.x_pos i) (by linarith) (by omega)
      (ThS_pow_le D C1 C2 N T T' δ x L (Finset.prod_pos fun v _ => hOK.x_pos i v) (nrmHalf_pos D _ haa)
        (x_le_ThInvF D C1 C2 N T T' δ x L i hi1 hi2)) S
      (fun l hl => ⟨hOK.dual_mem i hi1 hi2 l (hS l hl).1, (hS l hl).2⟩)
  · refine Finset.prod_nonneg fun v _ => minFac_nonneg _ _ ?_ (norm_nonneg _) K
    unfold thr3; split_ifs
    · exact (hOK.l_pos _ _ v).le
    · exact (mul_pos two_pos (hOK.p_pos _ v)).le
  ·
    obtain ⟨hs1, hs2⟩ := Finset.mem_Icc.1 hs
    have hnt' : ¬ (i = D.R.rS + 1 ∧ s = 1) := hnt
    have hblk : IsBlockSL2Embedding D (i - s + 1) s := ⟨by omega, hs1, by omega⟩
    have haP := hOK.aaP_ne _ _ hblk
    have hnP := nrmHalf_pos D _ haP
    have hmem : ∀ l ∈ S, l ∈ L.aaP (i - s + 1) s ∧ l ≠ 0 := fun l hl => by
      refine ⟨hOK.lift_mem _ _ hblk l ?_, (hS l hl).2⟩
      have h1 : l ∈ (if i = D.R.rS + 1 ∧ s = 1 then (⊤ : AddSubgroup D.host.E)
          else (L.La' (i - s + 1) s).toAddSubgroup) := (hS l hl).1
      rw [if_neg hnt', Submodule.mem_toAddSubgroup] at h1
      exact h1
    have hpos : ∀ v, 0 < thr3 D C1 C2 N T T' δ x i s v := fun v => by
      unfold thr3; split_ifs
      · exact hOK.l_pos _ _ v
      · exact mul_pos two_pos (hOK.p_pos _ v)
    refine hC D _ haP _ (Θ / 2) K hpos (by linarith) (by omega) ?_ S hmem
    by_cases hir : i ≤ D.R.rS
    · have hnV := nrmHalf_pos D _ (hOK.aaV_ne (i - s + 1) (s + 1) ⟨by omega, by omega, by omega⟩)
      have hP : 0 < ∏ v, LamSz D C1 C2 N (kaV D δ v) T T' (x v) (i - s + 1) (s + 1) :=
        Finset.prod_pos fun v _ => hOK.l_pos _ _ v
      have e1 : (∏ v, thr3 D C1 C2 N T T' δ x i s v) =
          ∏ v, LamSz D C1 C2 N (kaV D δ v) T T' (x v) (i - s + 1) (s + 1) :=
        Finset.prod_congr rfl fun v _ => by simp [thr3, hir, szL]
      rw [e1]
      have h2 := Lam_le_ThInvF D C1 C2 N T T' δ x L (i - s + 1) (s + 1) (by omega) (by omega) (by omega)
      rw [Nat.add_sub_cancel] at h2
      have h3 := ThS_pow_le D C1 C2 N T T' δ x L hP hnP
        (le_trans (div_le_div_of_nonneg_left hP.le (lt_min hnV hnP) (min_le_right _ _)) h2)
      refine le_trans (pow_le_pow_left₀ (by linarith) (by linarith) _) h3
    · have hi3 : i = D.R.rS + 1 := by omega
      have hs3 : 2 ≤ s := by
        by_contra hc
        exact hnt' ⟨hi3, by omega⟩
      have hP : 0 < ∏ v, LamPSz D C1 C2 N (kaV D δ v) T T' (x v) (i - s + 1) :=
        Finset.prod_pos fun v _ => hOK.p_pos _ v
      have e1 : (∏ v, thr3 D C1 C2 N T T' δ x i s v) =
          2 ^ D.R.f * ∏ v, LamPSz D C1 C2 N (kaV D δ v) T T' (x v) (i - s + 1) := by
        rw [← D.what₂.card_Tau, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun v _ => by simp [thr3, hir, szP]
      rw [e1]
      have h2 := prod_div_norm_le_sup D C1 C2 N T T' δ x L (i - s + 1) (by omega) (by omega)
      have e2 : D.R.rS + 2 - (i - s + 1) = s := by omega
      rw [e2] at h2
      have h3 := ThS_pow_le D C1 C2 N T T' δ x L hP hnP h2
      rw [div_pow, div_mul_eq_div_div_swap]
      exact div_le_div_of_nonneg_right h3 (by positivity)
  · exact num_first h3ep0 h3ep hep1_0 hep1le
  ·
    obtain ⟨hs1, hs2⟩ := Finset.mem_Icc.1 hs
    have he := hAx.2.2.1 i hi1 hi2
    have hvol : ∀ s' ∈ Ico 1 s, 0 ≤ Real.pi ^ D.R.f * volB D C1 C2 N T T' δ x L (i - s + 1) s' ∧
        Real.pi ^ D.R.f * volB D C1 C2 N T T' δ x L (i - s + 1) s' ≤ Real.pi ^ D.R.f * Y ^ 2 := fun s' hs' => by
      obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hs'
      have h3 := volB_le hOK (i - s + 1) s' (by omega) h1 (by omega)
      have hpi : 0 ≤ Real.pi ^ D.R.f := by positivity
      exact ⟨mul_nonneg hpi h3.1, mul_le_mul_of_nonneg_left h3.2 hpi⟩
    have hprod0 : 0 ≤ ∏ s' ∈ Ico 1 s, (Real.pi ^ D.R.f * volB D C1 C2 N T T' δ x L (i - s + 1) s') :=
      Finset.prod_nonneg fun s' hs' => (hvol s' hs').1
    have hprod : ∏ s' ∈ Ico 1 s, (Real.pi ^ D.R.f * volB D C1 C2 N T T' δ x L (i - s + 1) s') ≤
        (Real.pi ^ D.R.f * Y ^ 2) ^ (s - 1) := by
      have := Finset.prod_le_prod (fun s' hs' => (hvol s' hs').1) (fun s' hs' => (hvol s' hs').2)
      simpa using this
    have hC4p : 0 ≤ C4 ^ (D.R.f * s) := by positivity
    have hB0 : 0 ≤ bdB D C1 C2 N T T' δ x L C4 i s := mul_nonneg hC4p hprod0
    refine ⟨hB0, ?_⟩
    rw [ha]
    refine num_block hC4 (by rw [hC0def]; linarith) hY.le hf hs1 (by linarith) (by linarith) ?_ ?_ hB0
      (mul_le_mul_of_nonneg_left hprod hC4p)
    · show 0 ≤ 1 + Kd.e i
      linarith [he.1]
    · show 1 + Kd.e i ≤ 2
      linarith [he.2]

end Formalism.MainNotions.InterlacingSignCuts

end

end PartASz

section PartAKol

open scoped ComplexConjugate ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts

open Formalism.MainNotions.S

/- English proof (translation)
Introduce `X a`. Establish `h` using `hg X (fun p => conj (a p))`. Rewrite `h` using `[Finset.sum_comm]`. Use `le_of_le_of_eq h ?_` and prove the remaining obligations. Use `Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations.

Simplify using `only [Complex.star_def, Complex.conj_conj]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem PSDK.transpose {α : Type*} {g : α → α → ℂ} (hg : PSDK g) : PSDK (fun p q => g q p) := by
  intro X a
  have h := hg X (fun p => conj (a p))
  rw [Finset.sum_comm] at h
  refine le_of_le_of_eq h ?_
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  simp only [Complex.star_def, Complex.conj_conj]
  ring

def opKer {α : Type} (K : α → α → ℂ) : Matrix α α (ℂ →L[ℂ] ℂ) :=
  Matrix.of fun x y => K x y • (1 : ℂ →L[ℂ] ℂ)

/- English proof (translation)
Establish `key` using `(RKHS.posSemidef_tfae (𝕜 := ℂ) (K := opKer K)).out 0 2`. Use `key.2 ⟨?_, fun vv => ?_⟩` and prove the remaining obligations. Use `Matrix.ext fun x y => ?_` and prove the remaining obligations. Simplify using `only [Matrix.conjTranspose_apply, opKer, Matrix.of_apply]`. Rewrite using `[PSDK.herm hK y x, star_smul, star_one, Complex.star_def]`.

Establish `h` using `hK vv.support (fun p => vv p)`. Establish `h2 : (vv.sum fun x w => vv.sum fun x' w' => ⟪opKer K x' x w, w'⟫_ℂ) = conj (∑ p ∈ vv.support, ∑ q ∈ vv.support, star (vv p) * K p q * vv q)`. Simplify using `only [Finsupp.sum, map_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations.

Simplify using `[opKer, RCLike.inner_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h2]`. Express the relevant statement in the definitionally equal form `0 ≤ (conj (∑ p ∈ vv.support, ∑ q ∈ vv.support, star (vv p) * K p q * vv q) : ℂ).re`. Rewrite using `[Complex.conj_re]`.

Conclude with `(Complex.le_def.1 h).1`.
-/
theorem opKer_posSemidef {α : Type} {K : α → α → ℂ} (hK : PSDK K) : (opKer K).PosSemidef := by
  have key := (RKHS.posSemidef_tfae (𝕜 := ℂ) (K := opKer K)).out 0 2
  refine key.2 ⟨?_, fun vv => ?_⟩
  · refine Matrix.ext fun x y => ?_
    simp only [Matrix.conjTranspose_apply, opKer, Matrix.of_apply]
    rw [PSDK.herm hK y x, star_smul, star_one, Complex.star_def]
  · have h := hK vv.support (fun p => vv p)
    have h2 : (vv.sum fun x w => vv.sum fun x' w' => ⟪opKer K x' x w, w'⟫_ℂ) =
        conj (∑ p ∈ vv.support, ∑ q ∈ vv.support, star (vv p) * K p q * vv q) := by
      simp only [Finsupp.sum, map_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
      simp [opKer, RCLike.inner_apply]
      ring
    rw [h2]
    change 0 ≤ (conj (∑ p ∈ vv.support, ∑ q ∈ vv.support, star (vv p) * K p q * vv q) : ℂ).re
    rw [Complex.conj_re]
    exact (Complex.le_def.1 h).1

/- English proof (translation)
Establish `: Fact (opKer K).PosSemidef` using `⟨opKer_posSemidef hK⟩`. Use `⟨RKHS.OfKernel (opKer K), inferInstance, inferInstance, inferInstance, fun p => RKHS.kerFun (RKHS.OfKernel (opKer K)) p 1, fun p q => ?_⟩` and prove the remaining obligations. Rewrite using `[← RKHS.kernel_inner, RKHS.OfKernel.kernel_ofKernel]`. Simplify using `only [opKer, Matrix.of_apply]`. Rewrite using `[PSDK.herm hK p q]`.

Simplify using `[RCLike.inner_apply]`.
-/
theorem exists_gram {α : Type} {K : α → α → ℂ} (hK : PSDK K) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H) (V : α → H),
      ∀ p q, ⟪V p, V q⟫_ℂ = K p q := by
  have : Fact (opKer K).PosSemidef := ⟨opKer_posSemidef hK⟩
  refine ⟨RKHS.OfKernel (opKer K), inferInstance, inferInstance, inferInstance,
    fun p => RKHS.kerFun (RKHS.OfKernel (opKer K)) p 1, fun p q => ?_⟩
  rw [← RKHS.kernel_inner, RKHS.OfKernel.kernel_ofKernel]
  simp only [opKer, Matrix.of_apply]
  rw [PSDK.herm hK p q]
  simp [RCLike.inner_apply]

/- English proof (translation)
Conclude with `exists_gram (PSDK.transpose hg)`.
-/
theorem exists_gram_transpose {α : Type} {g : α → α → ℂ} (hg : PSDK g) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H) (V : α → H),
      ∀ p q, ⟪V p, V q⟫_ℂ = g q p := by
  exact exists_gram (PSDK.transpose hg)

end Formalism.MainNotions.InterlacingSignCuts

end

end PartAKol

section PartAPsd

open scoped ComplexConjugate ComplexOrder

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts

open Formalism.MainNotions.S

attribute [local instance] Classical.propDecidable

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hK`. Use `⟨Matrix.ext fun x y => ?_, fun x => ?_⟩` and prove the remaining obligations. Simplify using `only [Matrix.conjTranspose_apply, Matrix.of_apply]`. Rewrite using `[PSDK.herm hK y x, Complex.star_def]`.

Conclude with `hK x.support x`. Introduce `hK X a`. Establish `h` using `hK.2 (Finsupp.onFinset X (fun p => if p ∈ X then a p else 0) (by`. Introduce `p hp`. Assume the negation of the conclusion as `hc`.

Simplify using `[hc] at hp))`. Rewrite `h` using `[Finsupp.onFinset_sum _ (by intro p; simp)]`. Use `le_of_le_of_eq h ?_` and prove the remaining obligations. Use `Finset.sum_congr rfl fun p hp => ?_` and prove the remaining obligations. Rewrite using `[Finsupp.onFinset_sum _ (by intro q; simp)]`.

Use `Finset.sum_congr rfl fun q hq => ?_` and prove the remaining obligations. Simplify using `[hp, hq]`.
-/
theorem psdk_iff {α : Type*} (K : α → α → ℂ) : PSDK K ↔ (Matrix.of K : Matrix α α ℂ).PosSemidef := by
  constructor
  · intro hK
    refine ⟨Matrix.ext fun x y => ?_, fun x => ?_⟩
    · simp only [Matrix.conjTranspose_apply, Matrix.of_apply]
      rw [PSDK.herm hK y x, Complex.star_def]
    · exact hK x.support x
  · intro hK X a
    have h := hK.2 (Finsupp.onFinset X (fun p => if p ∈ X then a p else 0) (by
      intro p hp
      by_contra hc
      simp [hc] at hp))
    rw [Finsupp.onFinset_sum _ (by intro p; simp)] at h
    refine le_of_le_of_eq h ?_
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finsupp.onFinset_sum _ (by intro q; simp)]
    refine Finset.sum_congr rfl fun q hq => ?_
    simp [hp, hq]

/- English proof (translation)
The claim follows from `(psdk_iff _).2 (((psdk_iff K).1 hK).submatrix φ)`.
-/
theorem PSDK.comap {α β : Type*} {K : α → α → ℂ} (hK : PSDK K) (φ : β → α) : PSDK (fun p q => K (φ p) (φ q)) :=
  (psdk_iff _).2 (((psdk_iff K).1 hK).submatrix φ)

/- English proof (translation)
The claim follows from `(psdk_iff _).2 (((psdk_iff K).1 hK).hadamard ((psdk_iff L).1 hL))`.
-/
theorem PSDK.mul {α : Type*} {K L : α → α → ℂ} (hK : PSDK K) (hL : PSDK L) : PSDK (fun p q => K p q * L p q) :=
  (psdk_iff _).2 (((psdk_iff K).1 hK).hadamard ((psdk_iff L).1 hL))

/- English proof (translation)
Introduce `X a`. Establish `e : (∑ p ∈ X, ∑ q ∈ X, star (a p) * (w p * conj (w q)) * a q) = (∑ p ∈ X, star (a p) * w p) * conj (∑ p ∈ X, star (a p) * w p)`. Rewrite using `[map_sum, Finset.sum_mul_sum]`. Use `Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Simplify using `only [map_mul, Complex.star_def, Complex.conj_conj]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, Complex.mul_conj]`. Conclude with `Complex.normSq_nonneg _` after adjusting the coercions.
-/
theorem PSDK.rankOne {α : Type*} (w : α → ℂ) : PSDK (fun p q => w p * conj (w q)) := by
  intro X a
  have e : (∑ p ∈ X, ∑ q ∈ X, star (a p) * (w p * conj (w q)) * a q) =
      (∑ p ∈ X, star (a p) * w p) * conj (∑ p ∈ X, star (a p) * w p) := by
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    simp only [map_mul, Complex.star_def, Complex.conj_conj]
    ring
  rw [e, Complex.mul_conj]
  exact_mod_cast Complex.normSq_nonneg _

/- English proof (translation)
Simplify using `using PSDK.rankOne (fun _ : α => (1 : ℂ))`.
-/
theorem PSDK.one {α : Type*} : PSDK (fun _ _ : α => (1 : ℂ)) := by
  simpa using PSDK.rankOne (fun _ : α => (1 : ℂ))

/- English proof (translation)
Introduce `X a`. Use `add_nonneg (hK X a) (hL X a)` as an intermediate fact. Use `le_of_le_of_eq this ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations.

Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun q _ => by ring` and prove the remaining obligations.
-/
theorem PSDK.add {α : Type*} {K L : α → α → ℂ} (hK : PSDK K) (hL : PSDK L) : PSDK (fun p q => K p q + L p q) := by
  intro X a
  have := add_nonneg (hK X a) (hL X a)
  refine le_of_le_of_eq this ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => by ring

/- English proof (translation)
Introduce `X a`. Establish `hc' : (0 : ℂ) ≤ (c : ℂ)` using `by exact_mod_cast hc`. Use `mul_nonneg hc' (hK X a)` as an intermediate fact. Use `le_of_le_of_eq this ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun q _ => by ring` and prove the remaining obligations.
-/
theorem PSDK.smul {α : Type*} {K : α → α → ℂ} (hK : PSDK K) {c : ℝ} (hc : 0 ≤ c) : PSDK (fun p q => (c : ℂ) * K p q) := by
  intro X a
  have hc' : (0 : ℂ) ≤ (c : ℂ) := by exact_mod_cast hc
  have := mul_nonneg hc' (hK X a)
  refine le_of_le_of_eq this ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => by ring

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using PSDK.one`. Consider the case `insert v s hv ih`. Establish `h1` using `PSDK.mul (hK v (Finset.mem_insert_self v s)) (ih fun w hw => hK w (Finset.mem_insert_of_mem hw))`. Simplify `h1` using `[Finset.prod_insert hv]`.
-/
theorem PSDK.prod {α ι : Type*} (s : Finset ι) {K : ι → α → α → ℂ} (hK : ∀ v ∈ s, PSDK (K v)) :
    PSDK (fun p q => ∏ v ∈ s, K v p q) := by
  induction s using Finset.induction_on with
  | empty => simpa using PSDK.one
  | insert v s hv ih =>
    have h1 := PSDK.mul (hK v (Finset.mem_insert_self v s)) (ih fun w hw => hK w (Finset.mem_insert_of_mem hw))
    simpa [Finset.prod_insert hv] using h1

/- English proof (translation)
Establish `h1 : PSDK (fun p q : α => ((n p : ℝ) : ℂ) * conj ((n q : ℝ) : ℂ))` using `PSDK.rankOne (fun p => ((n p : ℝ) : ℂ))`. Establish `h2 : PSDK (fun p q : α => ∏ v, g v (loc v p) (loc v q))` using `PSDK.prod Finset.univ fun v _ => PSDK.comap (hg v) (loc v)`. Take `⟨H, i1, i2, i3, V, hV⟩` from `exists_gram_transpose (PSDK.mul h1 h2)`. Use `⟨H, i1, i2, i3, V, fun p q => ?_⟩` and prove the remaining obligations. Rewrite using `[hV p q, Complex.conj_ofReal]`.
-/
theorem exists_gram_places {α ι : Type} [Fintype ι] {β : ι → Type} (g : ∀ v, β v → β v → ℂ) (hg : ∀ v, PSDK (g v))
    (loc : ∀ v, α → β v) (n : α → ℝ) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H) (V : α → H),
      ∀ p q, inner ℂ (V p) (V q) = ((n q : ℝ) : ℂ) * ((n p : ℝ) : ℂ) * ∏ v, g v (loc v q) (loc v p) := by
  have h1 : PSDK (fun p q : α => ((n p : ℝ) : ℂ) * conj ((n q : ℝ) : ℂ)) := PSDK.rankOne (fun p => ((n p : ℝ) : ℂ))
  have h2 : PSDK (fun p q : α => ∏ v, g v (loc v p) (loc v q)) :=
    PSDK.prod Finset.univ fun v _ => PSDK.comap (hg v) (loc v)
  obtain ⟨H, i1, i2, i3, V, hV⟩ := exists_gram_transpose (PSDK.mul h1 h2)
  refine ⟨H, i1, i2, i3, V, fun p q => ?_⟩
  rw [hV p q, Complex.conj_ofReal]

end Formalism.MainNotions.InterlacingSignCuts

end

end PartAPsd

section PartARow

open scoped ComplexConjugate ComplexOrder InnerProductSpace ENNReal

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts

open Formalism.MainNotions.S

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/- English proof (translation)
Establish `hu : Summable fun h => ‖c h • W h‖` using `by simpa [norm_smul] using hs`. Establish `hsum : Summable fun h => c h • W h` using `hu.of_norm`. Establish `hterm : ∀ q : P × P, c q.1 * star (c q.2) * ⟪W q.2, W q.1⟫_ℂ = ⟪c q.2 • W q.2, c q.1 • W q.1⟫_ℂ` using `fun q => by`. Rewrite using `[inner_smul_left, inner_smul_right, Complex.star_def]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hprod : Summable fun q : P × P => ⟪c q.2 • W q.2, c q.1 • W q.1⟫_ℂ`. Use `Summable.of_norm_bounded (g := fun q : P × P => ‖c q.1 • W q.1‖ * ‖c q.2 • W q.2‖) (hu.mul_of_nonneg hu (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)) fun q => ?_` and prove the remaining obligations. Rewrite using `[mul_comm]`. Conclude with `norm_inner_le_norm _ _`. Repeatedly rewrite using `[hterm]`.

Rewrite using `[hprod.tsum_prod' (fun b => ?_)]`. Establish `h1 : ∀ b : P, (∑' b' : P, ⟪c b' • W b', c b • W b⟫_ℂ) = ⟪∑' h, c h • W h, c b • W b⟫_ℂ` using `fun b => by`. Use `(hsum.hasSum.mapL (innerSL ℂ (c b • W b))).tsum_eq` as an intermediate fact. Establish `h2 : ⟪∑' h, c h • W h, c b • W b⟫_ℂ = conj ⟪c b • W b, ∑' h, c h • W h⟫_ℂ` using `(inner_conj_symm _ _).symm`. Rewrite using `[h2]`.

Simplify using `only [innerSL_apply_apply] at this`. Rewrite using `[← this, Complex.conj_tsum]`. Conclude with `tsum_congr fun b' => (inner_conj_symm _ _).symm`. Repeatedly rewrite using `[h1]`. Use `(hsum.hasSum.mapL (innerSL ℂ (∑' h, c h • W h))).tsum_eq` as an intermediate fact.

Simplify using `only [innerSL_apply_apply] at this`. Rewrite using `[this, inner_self_eq_norm_sq_to_K]`. Use `norm_cast`. Conclude with `hprod.prod_factor b`.
-/
theorem normSq_tsum {P : Type*} (c : P → ℂ) (W : P → H) (hs : Summable fun h => ‖c h‖ * ‖W h‖) :
    (∑' q : P × P, c q.1 * star (c q.2) * ⟪W q.2, W q.1⟫_ℂ) = ((‖∑' h, c h • W h‖ ^ 2 : ℝ) : ℂ) := by
  have hu : Summable fun h => ‖c h • W h‖ := by simpa [norm_smul] using hs
  have hsum : Summable fun h => c h • W h := hu.of_norm
  have hterm : ∀ q : P × P, c q.1 * star (c q.2) * ⟪W q.2, W q.1⟫_ℂ = ⟪c q.2 • W q.2, c q.1 • W q.1⟫_ℂ := fun q => by
    rw [inner_smul_left, inner_smul_right, Complex.star_def]; ring
  have hprod : Summable fun q : P × P => ⟪c q.2 • W q.2, c q.1 • W q.1⟫_ℂ := by
    refine Summable.of_norm_bounded (g := fun q : P × P => ‖c q.1 • W q.1‖ * ‖c q.2 • W q.2‖)
      (hu.mul_of_nonneg hu (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)) fun q => ?_
    rw [mul_comm]; exact norm_inner_le_norm _ _
  simp_rw [hterm]
  rw [hprod.tsum_prod' (fun b => ?_)]
  · have h1 : ∀ b : P, (∑' b' : P, ⟪c b' • W b', c b • W b⟫_ℂ) = ⟪∑' h, c h • W h, c b • W b⟫_ℂ := fun b => by
      have := (hsum.hasSum.mapL (innerSL ℂ (c b • W b))).tsum_eq
      have h2 : ⟪∑' h, c h • W h, c b • W b⟫_ℂ = conj ⟪c b • W b, ∑' h, c h • W h⟫_ℂ := (inner_conj_symm _ _).symm
      rw [h2]
      simp only [innerSL_apply_apply] at this
      rw [← this, Complex.conj_tsum]
      exact tsum_congr fun b' => (inner_conj_symm _ _).symm
    simp_rw [h1]
    have := (hsum.hasSum.mapL (innerSL ℂ (∑' h, c h • W h))).tsum_eq
    simp only [innerSL_apply_apply] at this
    rw [this, inner_self_eq_norm_sq_to_K]
    norm_cast
  · exact hprod.prod_factor b

/- English proof (translation)
Rewrite using `[ENNReal.tsum_eq_iSup_sum]`. Use `iSup_le fun R => ?_` and prove the remaining obligations. Establish `: ∀ ρ, (∑' q : P × P, c ρ q.1 * star (c ρ q.2) * ⟪W q.2, W q.1⟫_ℂ).re = ‖∑' h, c ρ h • W h‖ ^ 2` using `fun ρ => by`. Rewrite using `[normSq_tsum (c ρ) W (hs ρ), Complex.ofReal_re]`. Repeatedly rewrite using `[this]`.

Rewrite using `[← ENNReal.ofReal_sum_of_nonneg (fun ρ _ => by positivity)]`. Conclude with `ENNReal.ofReal_le_ofReal (hB R)`.
-/
theorem rows_le {ι P : Type*} (c : ι → P → ℂ) (W : P → H) (hs : ∀ ρ, Summable fun h => ‖c ρ h‖ * ‖W h‖) (B : ℝ)
    (hB : ∀ R : Finset ι, ∑ ρ ∈ R, ‖∑' h, c ρ h • W h‖ ^ 2 ≤ B) :
    ∑' ρ, ENNReal.ofReal (∑' q : P × P, c ρ q.1 * star (c ρ q.2) * ⟪W q.2, W q.1⟫_ℂ).re ≤ ENNReal.ofReal B := by
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun R => ?_
  have : ∀ ρ, (∑' q : P × P, c ρ q.1 * star (c ρ q.2) * ⟪W q.2, W q.1⟫_ℂ).re = ‖∑' h, c ρ h • W h‖ ^ 2 := fun ρ => by
    rw [normSq_tsum (c ρ) W (hs ρ), Complex.ofReal_re]
  simp_rw [this]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun ρ _ => by positivity)]
  exact ENNReal.ofReal_le_ofReal (hB R)

/- English proof (translation)
Establish `hre : ∀ v, ip v (V v h) (V v h) = (((ip v (V v h) (V v h)).re : ℝ) : ℂ)` using `fun v => by`. Establish `h0` using `Complex.le_def.1 (PSDK.diag_real (hip v) (V v h))`. Apply `Complex.ext` to reduce the goal to its premises. Simplify using the standard rewrite rules. Simplify using `only [Complex.ofReal_im]`.

Conclude with `h0.2.symm`. Establish `hnn : ∀ v, 0 ≤ (ip v (V v h) (V v h)).re` using `fun v => (Complex.le_def.1 (PSDK.diag_real (hip v) (V v h))).1`. Establish `h1 : ((‖W h‖ ^ 2 : ℝ) : ℂ) = (((Real.sqrt (n h) * ∏ v, Real.sqrt (ip v (V v h) (V v h)).re) ^ 2 : ℝ) : ℂ)`. Use `hW h h` as an intermediate fact. Rewrite `this` using `[inner_self_eq_norm_sq_to_K]`.

Establish `e : (∏ v, ip v (V v h) (V v h)) = ((∏ v, (ip v (V v h) (V v h)).re : ℝ) : ℂ)`. Rewrite using `[Complex.ofReal_prod]`. Conclude with `Finset.prod_congr rfl fun v _ => hre v`. Rewrite `this` using `[e]`. Establish `e2 : (∏ v, Real.sqrt (ip v (V v h) (V v h)).re) ^ 2 = ∏ v, (ip v (V v h) (V v h)).re`.

Rewrite using `[← Finset.prod_pow]`. Conclude with `Finset.prod_congr rfl fun v _ => Real.sq_sqrt (hnn v)`. Rewrite using `[mul_pow, e2]`. Move the coercions through the operations in `at this ⊢`. Use `Eq.trans this ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Establish `h2 : ‖W h‖ ^ 2 = (Real.sqrt (n h) * ∏ v, Real.sqrt (ip v (V v h) (V v h)).re) ^ 2` using `by exact_mod_cast h1`. Conclude with `(pow_left_inj₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Finset.prod_nonneg fun v _ => Real.sqrt_nonneg _)) two_ne_zero).1 h2`.
-/
theorem norm_places {P Tau : Type} [Fintype Tau] {HSv : Tau → Type} (ip : ∀ v, HSv v → HSv v → ℂ) (hip : ∀ v, PSDK (ip v))
    (n : P → ℝ) (V : ∀ v, P → HSv v) (W : P → H)
    (hW : ∀ p q, ⟪W p, W q⟫_ℂ = ((Real.sqrt (n q) : ℝ) : ℂ) * ((Real.sqrt (n p) : ℝ) : ℂ) * ∏ v, ip v (V v q) (V v p)) (h : P) :
    ‖W h‖ = Real.sqrt (n h) * ∏ v, Real.sqrt (ip v (V v h) (V v h)).re := by
  have hre : ∀ v, ip v (V v h) (V v h) = (((ip v (V v h) (V v h)).re : ℝ) : ℂ) := fun v => by
    have h0 := Complex.le_def.1 (PSDK.diag_real (hip v) (V v h))
    apply Complex.ext
    · simp
    · simp only [Complex.ofReal_im]; exact h0.2.symm
  have hnn : ∀ v, 0 ≤ (ip v (V v h) (V v h)).re := fun v => (Complex.le_def.1 (PSDK.diag_real (hip v) (V v h))).1
  have h1 : ((‖W h‖ ^ 2 : ℝ) : ℂ) = (((Real.sqrt (n h) * ∏ v, Real.sqrt (ip v (V v h) (V v h)).re) ^ 2 : ℝ) : ℂ) := by
    have := hW h h
    rw [inner_self_eq_norm_sq_to_K] at this
    have e : (∏ v, ip v (V v h) (V v h)) = ((∏ v, (ip v (V v h) (V v h)).re : ℝ) : ℂ) := by
      rw [Complex.ofReal_prod]; exact Finset.prod_congr rfl fun v _ => hre v
    rw [e] at this
    have e2 : (∏ v, Real.sqrt (ip v (V v h) (V v h)).re) ^ 2 = ∏ v, (ip v (V v h) (V v h)).re := by
      rw [← Finset.prod_pow]; exact Finset.prod_congr rfl fun v _ => Real.sq_sqrt (hnn v)
    rw [mul_pow, e2]
    push_cast at this ⊢
    refine Eq.trans this ?_
    ring
  have h2 : ‖W h‖ ^ 2 = (Real.sqrt (n h) * ∏ v, Real.sqrt (ip v (V v h) (V v h)).re) ^ 2 := by exact_mod_cast h1
  exact (pow_left_inj₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _)
    (Finset.prod_nonneg fun v _ => Real.sqrt_nonneg _)) two_ne_zero).1 h2

/- English proof (translation)
Establish `hs' : ∀ ρ, Summable fun h => ‖c ρ h‖ * ‖W h‖` using `fun ρ => by`. Use `(hs ρ).congr fun h => ?_` and prove the remaining obligations. Rewrite using `[norm_places ip hip n V W hW h, mul_assoc]`. Use `le_of_eq_of_le ?_ (rows_le c W hs' B hB)` and prove the remaining obligations. Unfold `SRowForm`.

Use `tsum_congr fun ρ => ?_` and prove the remaining obligations. Use `congr 2`. Use `tsum_congr fun q => ?_` and prove the remaining obligations. Rewrite using `[hW q.2 q.1]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem sRowForm_le {ι P Tau : Type} [Fintype Tau] {HSv : Tau → Type} (ip : ∀ v, HSv v → HSv v → ℂ) (hip : ∀ v, PSDK (ip v))
    (n : P → ℝ) (c : ι → P → ℂ) (V : ∀ v, P → HSv v) (W : P → H)
    (hW : ∀ p q, ⟪W p, W q⟫_ℂ = ((Real.sqrt (n q) : ℝ) : ℂ) * ((Real.sqrt (n p) : ℝ) : ℂ) * ∏ v, ip v (V v q) (V v p))
    (hs : ∀ ρ, Summable (fun h => ‖c ρ h‖ * Real.sqrt (n h) * ∏ v, Real.sqrt (ip v (V v h) (V v h)).re)) (B : ℝ)
    (hB : ∀ R : Finset ι, ∑ ρ ∈ R, ‖∑' h, c ρ h • W h‖ ^ 2 ≤ B) :
    SRowForm HSv ip n c V ≤ ENNReal.ofReal B := by
  have hs' : ∀ ρ, Summable fun h => ‖c ρ h‖ * ‖W h‖ := fun ρ => by
    refine (hs ρ).congr fun h => ?_
    rw [norm_places ip hip n V W hW h, mul_assoc]
  refine le_of_eq_of_le ?_ (rows_le c W hs' B hB)
  unfold SRowForm
  refine tsum_congr fun ρ => ?_
  congr 2
  refine tsum_congr fun q => ?_
  rw [hW q.2 q.1]
  push_cast
  ring

end Formalism.MainNotions.InterlacingSignCuts

end

end PartARow

section PartATop

open NumberField Finset Filter Topology
open scoped nonZeroDivisors ComplexConjugate ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.MainNotions.InterlacingSignCuts

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.FourierDecayAlt.TA

attribute [local instance] Classical.propDecidable

section Points

variable {E : Type} [Field E]

/- English proof (translation)
Use `⟨?_, fun b hb => ?_⟩` and prove the remaining obligations. Establish `: (unsw q).map Prod.fst = q.1.map Prod.snd`. Simplify using `[unsw, List.map_map, Function.comp_def]`. Rewrite using `[lvl, this]`. Conclude with `q.2.2`.

Take `⟨c, hc, rfl⟩` from `List.mem_map.1 hb`. Conclude with `⟨(q.2.1 c hc).2, (q.2.1 c hc).1⟩`.
-/
theorem isPt_unsw {i : ℕ} (q : Point E i) : IsPt i (unsw q) := by
  refine ⟨?_, fun b hb => ?_⟩
  · have : (unsw q).map Prod.fst = q.1.map Prod.snd := by
      simp [unsw, List.map_map, Function.comp_def]
    rw [lvl, this]; exact q.2.2
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hb
    exact ⟨(q.2.1 c hc).2, (q.2.1 c hc).1⟩

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[ph_val (isPt_unsw q)]`. Simplify using `[sw, unsw, List.map_map]`.
-/
theorem ph_unsw {i : ℕ} (q : Point E i) : ph i (unsw q) = q := by
  apply Subtype.ext
  rw [ph_val (isPt_unsw q)]
  simp [sw, unsw, List.map_map]

def ptEquiv (i : ℕ) : {p : Pt E // IsPt i p} ≃ Point E i where
  toFun p := ph i p.1
  invFun q := ⟨unsw q, isPt_unsw q⟩
  left_inv p := Subtype.ext (unsw_ph p.2)
  right_inv q := ph_unsw q

end Points

/- English proof (translation)
Take `⟨C0, hC01, hSz⟩` from `levelSizes_of_ThS K hK C4 hC4`. Take `⟨C', C, hTA⟩` from `Formalism.FourierDecayAlt.P.theorem_a_reduction C0 hC01`. Use `⟨C0, max C' (max C0 5), C, hC01, ?_⟩` and prove the remaining obligations. Introduce `D C1 C2 N T T' δ x L Kd Lv hAx hOK hΘ hr H _ _ _ Wd _ len Pat1 pat1 pat3 Φ tr w0 jn ι c Wv hEst hE hw0 hcut hrow hsum R`. Establish `hΘ1 : C' ≤ ThS D C1 C2 N T T' δ x L` using `le_trans (le_max_left _ _) hΘ`.

Establish `hΘ2 : C0 ≤ ThS D C1 C2 N T T' δ x L` using `le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hΘ`. Establish `hΘ3 : 4 < ThS D C1 C2 N T T' δ x L` using `lt_of_lt_of_le (by norm_num) (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hΘ)`. Take `⟨ep1, ep3, hLS⟩` from `hSz D C1 C2 N T T' δ x L Kd Lv hAx hOK hΘ2 hΘ3`. Establish `key` using `hTA D.host.E H Wd len K D.R.f (ThS D C1 C2 N T T' δ x L) (taData D L Kd Lv) Pat1 (D.what₂.Tau → Option Bool) pat1 pat3 (prof1 D C1 C2 N T T' δ x K) (prof3 D C1 C2 N T T' δ x K) (fun _ => ep1) (fun _ _ => ep3) (bdB D C1 C2 N T T' δ x L C4) Φ tr w0 (fun p => Wv (ph (D.R.rS + 1) p)) …`. Use `le_of_eq_of_le ?_ key` and prove the remaining obligations.

Use `Finset.sum_congr rfl fun ρ _ => ?_` and prove the remaining obligations. Use `congr 2`. Conclude with `((ptEquiv (E := D.host.E) (D.R.rS + 1)).tsum_eq (fun h => c ρ h • Wv h)).symm`.
-/
theorem rowSums_of_levelEst (K : ℕ) (hK : 4 ≤ K) (C4 : ℝ) (hC4 : 1 ≤ C4) : ∃ C0 C' C : ℝ, 1 ≤ C0 ∧
    ∀ (D : D7) (C1 C2 N T T' : ℝ) (δ : D.host.E) (x : D.what₂.Tau → LocalDataRealPlace D) (L : LatticeDataWithDual D) (Kd : KernelData D)
      (Lv : ℕ → AddSubgroup D.host.E), ArithAx D L Kd → SzOK D C1 C2 N T T' δ x L Lv →
      C' ≤ ThS D C1 C2 N T T' δ x L → (D.R.rS : ℝ) * (C0 / ThS D C1 C2 N T T' δ x L) ^ D.R.f ≤ 1 →
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (Wd : Type) [Fintype Wd] (len : Wd → ℕ)
        (Pat1 : Type) (pat1 : ℕ → D.host.E → Pat1) (pat3 : ℕ → ℕ → D.host.E → D.host.E → (D.what₂.Tau → Option Bool))
        (Φ : ℝ → Wd → Pt D.host.E → H)
        (tr : ℝ → ℕ → Wd → Finset (Pt D.host.E) → (Pt D.host.E → Pt D.host.E → ℂ) → D.host.E → ℂ)
        (w0 : Wd) (jn : ℝ) (ι : Type) (c : ι → Point D.host.E (D.R.rS + 1) → ℂ) (Wv : Point D.host.E (D.R.rS + 1) → H),
        (∀ eps : ℝ, 0 < eps → ∀ i ∈ Icc 1 (D.R.rS + 1),
          LevelEst len K (taData D L Kd Lv) (Φ eps) (tr eps i) (pat1 i) (pat3 i) (prof1 D C1 C2 N T T' δ x K i)
            (prof3 D C1 C2 N T T' δ x K i) (bdB D C1 C2 N T T' δ x L C4 i) i) →
        (∀ w, len w ≤ 4 * K * (D.R.rS + 1) → Tendsto (fun eps => ‖Φ eps w []‖ ^ 2) (𝓝[>] 0) (𝓝 jn)) →
        len w0 = 0 →
        (∀ p, IsPt (D.R.rS + 1) p → ∀ᶠ eps in 𝓝[>] (0 : ℝ), Φ eps w0 p = Wv (ph (D.R.rS + 1) p)) →
        (∀ R : Finset ι, KLE (fun p p' => ∑ ρ ∈ R, c ρ p * star (c ρ p')) (Kd.K (D.R.rS + 1))) →
        (∀ ρ, Summable fun h => ‖c ρ h‖ * ‖Wv h‖) →
        ∀ R : Finset ι, ∑ ρ ∈ R, ‖∑' h, c ρ h • Wv h‖ ^ 2 ≤
          (1 + C * ((D.R.rS : ℝ) + 1) * (C0 / ThS D C1 C2 N T T' δ x L) ^ D.R.f) *
            (∏ i ∈ Icc 1 (D.R.rS + 1), (1 + Kd.e i)) * jn := by
  obtain ⟨C0, hC01, hSz⟩ := levelSizes_of_ThS K hK C4 hC4
  obtain ⟨C', C, hTA⟩ := Formalism.FourierDecayAlt.P.theorem_a_reduction C0 hC01
  refine ⟨C0, max C' (max C0 5), C, hC01, ?_⟩
  intro D C1 C2 N T T' δ x L Kd Lv hAx hOK hΘ hr H _ _ _ Wd _ len Pat1 pat1 pat3 Φ tr w0 jn ι c Wv hEst hE hw0 hcut hrow hsum R
  have hΘ1 : C' ≤ ThS D C1 C2 N T T' δ x L := le_trans (le_max_left _ _) hΘ
  have hΘ2 : C0 ≤ ThS D C1 C2 N T T' δ x L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hΘ
  have hΘ3 : 4 < ThS D C1 C2 N T T' δ x L :=
    lt_of_lt_of_le (by norm_num) (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hΘ)
  obtain ⟨ep1, ep3, hLS⟩ := hSz D C1 C2 N T T' δ x L Kd Lv hAx hOK hΘ2 hΘ3
  have key := hTA D.host.E H Wd len K D.R.f (ThS D C1 C2 N T T' δ x L) (taData D L Kd Lv) Pat1 (D.what₂.Tau → Option Bool)
    pat1 pat3 (prof1 D C1 C2 N T T' δ x K) (prof3 D C1 C2 N T T' δ x K) (fun _ => ep1) (fun _ _ => ep3)
    (bdB D C1 C2 N T T' δ x L C4) Φ tr w0 (fun p => Wv (ph (D.R.rS + 1) p)) jn ι (fun ρ p => c ρ (ph (D.R.rS + 1) p))
    hK (f_pos D) hΘ1 hr (axK_of_ArithAx Lv hAx) (arith_axiom_second_of_arith_axioms Lv hAx) (arith_axiom_thirteenth_of_arith_axioms Lv hAx) (axE_of_ArithAx Lv hAx)
    hLS hEst hE hw0 hcut (fun P R hP => rows_of_KLE Lv c hrow P R hP)
    (fun ρ => ((ptEquiv (E := D.host.E) (D.R.rS + 1)).summable_iff (f := fun h => ‖c ρ h‖ * ‖Wv h‖)).2 (hsum ρ)) R
  refine le_of_eq_of_le ?_ key
  refine Finset.sum_congr rfl fun ρ _ => ?_
  congr 2
  exact ((ptEquiv (E := D.host.E) (D.R.rS + 1)).tsum_eq (fun h => c ρ h • Wv h)).symm

/- English proof (translation)
Take `⟨C0, C', C, hC01, h⟩` from `rowSums_of_levelEst K hK C4 hC4`. Use `⟨C0, C', C, hC01, ?_⟩` and prove the remaining obligations. Introduce `D C1 C2 N T T' δ x L Kd Lv hAx hOK hΘ hr HSv ip hip n ι c V hRows H _ _ _ Wv hW Wd _ len Pat1 pat1 pat3 Φ tr w0 jn hEst hE hw0 hcut`. Use `sRowForm_le ip hip n c V Wv hW hRows.2 _ ?_` and prove the remaining obligations. Use `h D C1 C2 N T T' δ x L Kd Lv hAx hOK hΘ hr H Wd len Pat1 pat1 pat3 Φ tr w0 jn ι c Wv hEst hE hw0 hcut hRows.1 ?_` and prove the remaining obligations.

Introduce `ρ`. Use `(hRows.2 ρ).congr fun p => ?_` and prove the remaining obligations. Rewrite using `[norm_places ip hip n V Wv hW p, mul_assoc]`.
-/
theorem sRowForm_of_levelEst (K : ℕ) (hK : 4 ≤ K) (C4 : ℝ) (hC4 : 1 ≤ C4) : ∃ C0 C' C : ℝ, 1 ≤ C0 ∧
    ∀ (D : D7) (C1 C2 N T T' : ℝ) (δ : D.host.E) (x : D.what₂.Tau → LocalDataRealPlace D) (L : LatticeDataWithDual D) (Kd : KernelData D)
      (Lv : ℕ → AddSubgroup D.host.E), ArithAx D L Kd → SzOK D C1 C2 N T T' δ x L Lv →
      C' ≤ ThS D C1 C2 N T T' δ x L → (D.R.rS : ℝ) * (C0 / ThS D C1 C2 N T T' δ x L) ^ D.R.f ≤ 1 →
      ∀ (HSv : D.what₂.Tau → Type) (ip : ∀ v, HSv v → HSv v → ℂ), (∀ v, PSDK (ip v)) →
      ∀ (n : Point D.host.E (D.R.rS + 1) → ℝ) (ι : Type) (c : ι → Point D.host.E (D.R.rS + 1) → ℂ)
        (V : ∀ v, Point D.host.E (D.R.rS + 1) → HSv v), RowsAx HSv ip (Kd.K (D.R.rS + 1)) n c V →
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (Wv : Point D.host.E (D.R.rS + 1) → H),
        (∀ p q, ⟪Wv p, Wv q⟫_ℂ = ((Real.sqrt (n q) : ℝ) : ℂ) * ((Real.sqrt (n p) : ℝ) : ℂ) * ∏ v, ip v (V v q) (V v p)) →
      ∀ (Wd : Type) [Fintype Wd] (len : Wd → ℕ)
        (Pat1 : Type) (pat1 : ℕ → D.host.E → Pat1) (pat3 : ℕ → ℕ → D.host.E → D.host.E → (D.what₂.Tau → Option Bool))
        (Φ : ℝ → Wd → Pt D.host.E → H)
        (tr : ℝ → ℕ → Wd → Finset (Pt D.host.E) → (Pt D.host.E → Pt D.host.E → ℂ) → D.host.E → ℂ)
        (w0 : Wd) (jn : ℝ),
        (∀ eps : ℝ, 0 < eps → ∀ i ∈ Icc 1 (D.R.rS + 1),
          LevelEst len K (taData D L Kd Lv) (Φ eps) (tr eps i) (pat1 i) (pat3 i) (prof1 D C1 C2 N T T' δ x K i)
            (prof3 D C1 C2 N T T' δ x K i) (bdB D C1 C2 N T T' δ x L C4 i) i) →
        (∀ w, len w ≤ 4 * K * (D.R.rS + 1) → Tendsto (fun eps => ‖Φ eps w []‖ ^ 2) (𝓝[>] 0) (𝓝 jn)) →
        len w0 = 0 →
        (∀ p, IsPt (D.R.rS + 1) p → ∀ᶠ eps in 𝓝[>] (0 : ℝ), Φ eps w0 p = Wv (ph (D.R.rS + 1) p)) →
        SRowForm HSv ip n c V ≤ ENNReal.ofReal
          ((1 + C * ((D.R.rS : ℝ) + 1) * (C0 / ThS D C1 C2 N T T' δ x L) ^ D.R.f) *
            (∏ i ∈ Icc 1 (D.R.rS + 1), (1 + Kd.e i)) * jn) := by
  obtain ⟨C0, C', C, hC01, h⟩ := rowSums_of_levelEst K hK C4 hC4
  refine ⟨C0, C', C, hC01, ?_⟩
  intro D C1 C2 N T T' δ x L Kd Lv hAx hOK hΘ hr HSv ip hip n ι c V hRows H _ _ _ Wv hW Wd _ len Pat1 pat1 pat3 Φ tr w0 jn
    hEst hE hw0 hcut
  refine sRowForm_le ip hip n c V Wv hW hRows.2 _ ?_
  refine h D C1 C2 N T T' δ x L Kd Lv hAx hOK hΘ hr H Wd len Pat1 pat1 pat3 Φ tr w0 jn ι c Wv hEst hE hw0 hcut hRows.1 ?_
  intro ρ
  refine (hRows.2 ρ).congr fun p => ?_
  rw [norm_places ip hip n V Wv hW p, mul_assoc]

end Formalism.MainNotions.InterlacingSignCuts

end

end PartATop
