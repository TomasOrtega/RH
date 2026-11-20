import Mathlib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DifferentialOperatorBracket
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsUnitaryWFrameToFrame
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory

open Formalism.FourierDecayAlt.P

open Matrix in
/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [mulVec, dotProduct]`. Rewrite using `[Finset.sum_eq_single i]`. Distinguish the cases in `hi : (i : ℕ) < r ∨ r + k < i`. Rewrite using `[hv i hi]`.

Simplify using the standard rewrite rules. Use `push_neg at hi`. Establish `h1 : ¬ (i : ℕ) < r` using `by omega`. Simplify using `only [_root_.Formalism.QuantumDeterminants.Hpk, h1, false_and, if_false, hi.1, hi.2, true_and, if_true]`. Apply the tactic sequence `split_ifs <;> simp`.

Introduce `j _ hj`. Distinguish the cases in `hjm : (j : ℕ) < r ∨ r + k < j`. Rewrite using `[hv j hjm]`. Simplify using the standard rewrite rules. Use `push_neg at hjm`.

Establish `hne : (i : ℕ) ≠ j` using `fun h => hj (Fin.ext h).symm`. Simplify using `only [_root_.Formalism.QuantumDeterminants.Hpk]`. Apply the tactic sequence `split_ifs with h1 h2 h3 <;> first | omega | exact absurd (congrArg Fin.val h3.2.2) hne | simp`. Simplify using the standard rewrite rules.
-/
private theorem Hpk_mulVec_of_inWb {k r : ℕ} {v : Fin (2 * r + k + 1) → ℂ} (hv : _root_.Formalism.QuantumDeterminants.inWb k r v) :
    _root_.Formalism.QuantumDeterminants.Hpk k r *ᵥ v = fun i : Fin (2 * r + k + 1) => if (i : ℕ) = r + k then -v i else v i := by
  funext i
  simp only [mulVec, dotProduct]
  rw [Finset.sum_eq_single i]
  · by_cases hi : (i : ℕ) < r ∨ r + k < i
    · rw [hv i hi]; simp
    · push_neg at hi
      have h1 : ¬ (i : ℕ) < r := by omega
      simp only [_root_.Formalism.QuantumDeterminants.Hpk, h1, false_and, if_false, hi.1, hi.2, true_and, if_true]
      split_ifs <;> simp
  · intro j _ hj
    by_cases hjm : (j : ℕ) < r ∨ r + k < j
    · rw [hv j hjm]; simp
    · push_neg at hjm
      have hne : (i : ℕ) ≠ j := fun h => hj (Fin.ext h).symm
      simp only [_root_.Formalism.QuantumDeterminants.Hpk]
      split_ifs with h1 h2 h3 <;> first | omega | exact absurd (congrArg Fin.val h3.2.2) hne | simp
  · simp

open Matrix in
/- English proof (translation)
Simplify using `[_root_.Formalism.QuantumDeterminants.herm, mulVec_smul, dotProduct_smul, smul_eq_mul]`.
-/
private theorem herm_smul_left_jet_harmonics {ι : Type} [Fintype ι] (H : Matrix ι ι ℂ) (c : ℂ) (v w : ι → ℂ) :
    _root_.Formalism.QuantumDeterminants.herm H (c • v) w = c * _root_.Formalism.QuantumDeterminants.herm H v w := by
  simp [_root_.Formalism.QuantumDeterminants.herm, mulVec_smul, dotProduct_smul, smul_eq_mul]

open Matrix in
/- English proof (translation)
Simplify using `[_root_.Formalism.QuantumDeterminants.herm, star_smul, smul_dotProduct, smul_eq_mul]`.
-/
private theorem herm_smul_right_jet_harmonics {ι : Type} [Fintype ι] (H : Matrix ι ι ℂ) (c : ℂ) (v w : ι → ℂ) :
    _root_.Formalism.QuantumDeterminants.herm H v (c • w) = star c * _root_.Formalism.QuantumDeterminants.herm H v w := by
  simp [_root_.Formalism.QuantumDeterminants.herm, star_smul, smul_dotProduct, smul_eq_mul]

open Matrix in
/- English proof (translation)
Use `set p : Fin (2 * r + (n + 1) + 1) := ⟨r, by omega⟩ with hp`. Use `set q : Fin (2 * r + (n + 1) + 1) := ⟨r + (n + 1), by omega⟩ with hq`. Establish `hpq : p ≠ q` using `by simp [hp, hq, Fin.ext_iff]`. Use `set v : Fin (2 * r + (n + 1) + 1) → ℂ := Pi.single p (star (z q)) + Pi.single q (star (z p)) with hvdef`. Establish `hv : _root_.Formalism.QuantumDeterminants.inWb (n + 1) r v`.

Introduce `i hi`. Establish `hip : i ≠ p` using `fun h => by rw [h] at hi; simp [hp] at hi`. Establish `hiq : i ≠ q` using `fun h => by rw [h] at hi; simp [hq] at hi`. Simplify using `[hvdef, Pi.single_apply, hip, hiq]`. Establish `hpval : (p : ℕ) ≠ r + (n + 1)` using `by simp [hp]`.

Establish `hqval : (q : ℕ) = r + (n + 1)` using `by simp [hq]`. Establish `hHv : _root_.Formalism.QuantumDeterminants.Hpk (n + 1) r *ᵥ v = Pi.single p (star (z q)) - Pi.single q (star (z p))`. Rewrite using `[Hpk_mulVec_of_inWb hv]`. Use function extensionality and compare the values at `i`. Distinguish the cases in `hip : i = p`.

Rewrite using `[hip, if_neg hpval, hvdef]`. Simplify using `[hpq, hpq.symm]`. Distinguish the cases in `hiq : i = q`. Rewrite using `[hiq, if_pos hqval, hvdef]`. Simplify using `[hpq, hpq.symm]`.

Establish `: (i : ℕ) ≠ r + (n + 1)` using `fun h => hiq (Fin.ext (h.trans hqval.symm))`. Rewrite using `[if_neg this, hvdef]`. Simplify using `[hip, hiq]`. Establish `hvz : _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk (n + 1) r) v z = 0`. Rewrite using `[_root_.Formalism.QuantumDeterminants.herm, hHv, dotProduct_sub, dotProduct_single, dotProduct_single]`.

Simplify using `[mul_comm]`. Establish `hvv : _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk (n + 1) r) v v = ((Complex.normSq (z q) - Complex.normSq (z p) : ℝ) : ℂ)`. Rewrite using `[_root_.Formalism.QuantumDeterminants.herm, hHv, dotProduct_sub, dotProduct_single, dotProduct_single]`. Simplify using `[hvdef, hpq, hpq.symm, Complex.normSq_eq_conj_mul_self]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hzz : Complex.normSq (z p) - Complex.normSq (z q) ≤ (_root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk (n + 1) r) z z).re`. Rewrite using `[_root_.Formalism.QuantumDeterminants.herm, Hpk_mulVec_of_inWb hz]`. Simplify using `only [dotProduct, Complex.re_sum]`. Establish `hf : ∀ i : Fin (2 * r + (n + 1) + 1), (star (z i) * (if (i : ℕ) = r + (n + 1) then -z i else z i)).re = if (i : ℕ) = r + (n + 1) then -Complex.normSq (z i) else Complex.normSq (z i)`. Introduce `i`.

Apply the tactic sequence `split_ifs <;> simp [Complex.normSq_apply, Complex.mul_re] <;> ring`. Simplify using `only [Pi.star_apply, hf]`. Rewrite using `[← Finset.add_sum_erase _ _ (Finset.mem_univ q), if_pos hqval]`. Establish `hpe : p ∈ Finset.univ.erase q` using `Finset.mem_erase.2 ⟨hpq, Finset.mem_univ _⟩`. Establish `h2` using `Finset.single_le_sum (f := fun i : Fin (2 * r + (n + 1) + 1) => if (i : ℕ) = r + (n + 1) then -Complex.normSq (z i) else Complex.normSq (z i)) (fun i hi => by`.

Establish `hiq : (i : ℕ) ≠ r + (n + 1)` using `fun h => Finset.ne_of_mem_erase hi (Fin.ext (h.trans hqval.symm))`. Simplify using `only [if_neg hiq]`. Conclude with `Complex.normSq_nonneg _) hpe`. Simplify using `only [if_neg hpval] at h2`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hT' : (_root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk (n + 1) r) z z).re < 0`. Use `hT` as an intermediate fact. Unfold `_root_.Formalism.QuantumDeterminants.Tz at this`. Combine the linear equalities and inequalities to obtain the conclusion. Use `set t := Complex.normSq (z q) - Complex.normSq (z p) with htdef`.

Establish `ht : 0 < t` using `by linarith`. Use `⟨((Real.sqrt t : ℂ))⁻¹ • v, fun i hi => by simp [hv i hi], ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[herm_smul_left_jet_harmonics, hvz, mul_zero]`. Rewrite using `[herm_smul_left_jet_harmonics, herm_smul_right_jet_harmonics, hvv]`. Establish `hs : Real.sqrt t ^ 2 = t` using `Real.sq_sqrt ht.le`.

Establish `hs0 : (Real.sqrt t : ℂ) ≠ 0` using `by exact_mod_cast (Real.sqrt_pos.2 ht).ne'`. Simplify using `only [star_inv₀, Complex.star_def, Complex.conj_ofReal]`. Clear the denominators using the available nonvanishing facts. Conclude with `hs.symm` after adjusting the coercions.
-/
private theorem exists_unit_orth_in_Wb {n r : ℕ} {z : Fin (2 * r + (n + 1) + 1) → ℂ} (hz : _root_.Formalism.QuantumDeterminants.inWb (n + 1) r z)
    (hT : 0 < _root_.Formalism.QuantumDeterminants.Tz (n + 1) r z) :
    ∃ e, _root_.Formalism.QuantumDeterminants.inWb (n + 1) r e ∧ _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk (n + 1) r) e z = 0 ∧
      _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk (n + 1) r) e e = 1 := by
  set p : Fin (2 * r + (n + 1) + 1) := ⟨r, by omega⟩ with hp
  set q : Fin (2 * r + (n + 1) + 1) := ⟨r + (n + 1), by omega⟩ with hq
  have hpq : p ≠ q := by simp [hp, hq, Fin.ext_iff]
  set v : Fin (2 * r + (n + 1) + 1) → ℂ := Pi.single p (star (z q)) + Pi.single q (star (z p)) with hvdef
  have hv : _root_.Formalism.QuantumDeterminants.inWb (n + 1) r v := by
    intro i hi
    have hip : i ≠ p := fun h => by rw [h] at hi; simp [hp] at hi
    have hiq : i ≠ q := fun h => by rw [h] at hi; simp [hq] at hi
    simp [hvdef, Pi.single_apply, hip, hiq]
  have hpval : (p : ℕ) ≠ r + (n + 1) := by simp [hp]
  have hqval : (q : ℕ) = r + (n + 1) := by simp [hq]
  have hHv : _root_.Formalism.QuantumDeterminants.Hpk (n + 1) r *ᵥ v = Pi.single p (star (z q)) - Pi.single q (star (z p)) := by
    rw [Hpk_mulVec_of_inWb hv]
    funext i
    by_cases hip : i = p
    · rw [hip, if_neg hpval, hvdef]
      simp [hpq, hpq.symm]
    · by_cases hiq : i = q
      · rw [hiq, if_pos hqval, hvdef]
        simp [hpq, hpq.symm]
      · have : (i : ℕ) ≠ r + (n + 1) := fun h => hiq (Fin.ext (h.trans hqval.symm))
        rw [if_neg this, hvdef]
        simp [hip, hiq]
  have hvz : _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk (n + 1) r) v z = 0 := by
    rw [_root_.Formalism.QuantumDeterminants.herm, hHv, dotProduct_sub, dotProduct_single, dotProduct_single]
    simp [mul_comm]
  have hvv : _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk (n + 1) r) v v =
      ((Complex.normSq (z q) - Complex.normSq (z p) : ℝ) : ℂ) := by
    rw [_root_.Formalism.QuantumDeterminants.herm, hHv, dotProduct_sub, dotProduct_single, dotProduct_single]
    simp [hvdef, hpq, hpq.symm, Complex.normSq_eq_conj_mul_self]
    ring
  have hzz : Complex.normSq (z p) - Complex.normSq (z q) ≤ (_root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk (n + 1) r) z z).re := by
    rw [_root_.Formalism.QuantumDeterminants.herm, Hpk_mulVec_of_inWb hz]
    simp only [dotProduct, Complex.re_sum]
    have hf : ∀ i : Fin (2 * r + (n + 1) + 1),
        (star (z i) * (if (i : ℕ) = r + (n + 1) then -z i else z i)).re =
          if (i : ℕ) = r + (n + 1) then -Complex.normSq (z i) else Complex.normSq (z i) := by
      intro i
      split_ifs <;> simp [Complex.normSq_apply, Complex.mul_re] <;> ring
    simp only [Pi.star_apply, hf]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ q), if_pos hqval]
    have hpe : p ∈ Finset.univ.erase q := Finset.mem_erase.2 ⟨hpq, Finset.mem_univ _⟩
    have h2 := Finset.single_le_sum (f := fun i : Fin (2 * r + (n + 1) + 1) =>
        if (i : ℕ) = r + (n + 1) then -Complex.normSq (z i) else Complex.normSq (z i))
      (fun i hi => by
        have hiq : (i : ℕ) ≠ r + (n + 1) := fun h =>
          Finset.ne_of_mem_erase hi (Fin.ext (h.trans hqval.symm))
        simp only [if_neg hiq]
        exact Complex.normSq_nonneg _) hpe
    simp only [if_neg hpval] at h2
    linarith
  have hT' : (_root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk (n + 1) r) z z).re < 0 := by
    have := hT; unfold _root_.Formalism.QuantumDeterminants.Tz at this; linarith
  set t := Complex.normSq (z q) - Complex.normSq (z p) with htdef
  have ht : 0 < t := by linarith
  refine ⟨((Real.sqrt t : ℂ))⁻¹ • v, fun i hi => by simp [hv i hi], ?_, ?_⟩
  · rw [herm_smul_left_jet_harmonics, hvz, mul_zero]
  · rw [herm_smul_left_jet_harmonics, herm_smul_right_jet_harmonics, hvv]
    have hs : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
    have hs0 : (Real.sqrt t : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 ht).ne'
    simp only [star_inv₀, Complex.star_def, Complex.conj_ofReal]
    field_simp
    exact_mod_cast hs.symm

open Matrix in
/- English proof (translation)
Use extensionality with `p q`. Simplify using `[_root_.GlobalTheory.FrameTrans.swapMat, Matrix.mul_apply, _root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.colM, _root_.Formalism.QuantumDeterminants.herm, _root_.Formalism.QuantumDeterminants.bvec, dotProduct, mulVec, Pi.single_apply, Finset.mul_sum]`.
-/
private theorem swapMat_eq_one_add_sub_mul {k r : ℕ} (H : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (B B' : Fin k → Fin (2 * r + k + 1) → ℂ) :
    _root_.GlobalTheory.FrameTrans.swapMat H B B' = 1 + (_root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.colM B' - _root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.colM B) * ((_root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.colM B)ᴴ * H) := by
  ext p q
  simp [_root_.GlobalTheory.FrameTrans.swapMat, Matrix.mul_apply, _root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.colM, _root_.Formalism.QuantumDeterminants.herm, _root_.Formalism.QuantumDeterminants.bvec, dotProduct, mulVec, Pi.single_apply, Finset.mul_sum]

open Matrix in
/- English proof (translation)
Rewrite using `[swapMat_eq_one_add_sub_mul, add_mulVec, one_mulVec, ← mulVec_mulVec]`. Use `congr 2`. Use function extensionality and compare the values at `c`. Simplify using `only [mulVec, dotProduct, _root_.Formalism.QuantumDeterminants.herm, Matrix.mul_apply, _root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.colM, conjTranspose_apply, Matrix.of_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]`. Conclude with `Finset.sum_comm`.
-/
private theorem swapMat_mulVec' {k r : ℕ} (H : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (B B' : Fin k → Fin (2 * r + k + 1) → ℂ) (v : Fin (2 * r + k + 1) → ℂ) :
    _root_.GlobalTheory.FrameTrans.swapMat H B B' *ᵥ v =
      v + (_root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.colM B' - _root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.colM B) *ᵥ fun c => _root_.Formalism.QuantumDeterminants.herm H v (B c) := by
  rw [swapMat_eq_one_add_sub_mul, add_mulVec, one_mulVec, ← mulVec_mulVec]
  congr 2
  funext c
  simp only [mulVec, dotProduct, _root_.Formalism.QuantumDeterminants.herm, Matrix.mul_apply, _root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.colM, conjTranspose_apply, Matrix.of_apply,
    Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

open Matrix in
/- English proof (translation)
Use extensionality with `p c`. Establish `e` using `congrFun (_root_.Formalism.FourierDecayAlt.P.HermitianFormSums.complete0 hz hzz hB (hB'.1 c) (hB'.2.2 c z (List.mem_singleton_self z))) p`. Rewrite using `[Matrix.mul_apply]`. Simplify using `only [_root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.gramM_apply]`. Simplify using `only [_root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.colM, Matrix.of_apply]`.

Use `conv_lhs => rw [e]`. Simplify using `[Finset.sum_apply, mul_comm]`.
-/
private theorem colM_eq_mul_gram_of_isFrameOf {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : _root_.Formalism.QuantumDeterminants.inWb k r z)
    (hzz : _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) z z ≠ 0) {B B' : Fin k → Fin (2 * r + k + 1) → ℂ}
    (hB : _root_.Formalism.FourierDecayAlt.Q.IsFrameOf k r [z] B) (hB' : _root_.Formalism.FourierDecayAlt.Q.IsFrameOf k r [z] B') :
    _root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.colM B' = _root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.colM B * ((_root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.colM B)ᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * _root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.colM B') := by
  ext p c
  have e := congrFun (_root_.Formalism.FourierDecayAlt.P.HermitianFormSums.complete0 hz hzz hB (hB'.1 c) (hB'.2.2 c z (List.mem_singleton_self z))) p
  rw [Matrix.mul_apply]
  simp only [_root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.gramM_apply]
  simp only [_root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.colM, Matrix.of_apply]
  conv_lhs => rw [e]
  simp [Finset.sum_apply, mul_comm]

open Matrix in
/- English proof (translation)
Establish `hfix : ∀ j, _root_.GlobalTheory.FrameTrans.swapMat (_root_.Formalism.QuantumDeterminants.Hpk k r) B B' *ᵥ _root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.cvec k r z j = _root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.cvec k r z j`. Introduce `j`. Rewrite using `[swapMat_mulVec']`. Establish `h0 : (fun c => _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) (_root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.cvec k r z j) (B c)) = 0` using `funext fun c => _root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.gram_VC hB c j`. Rewrite using `[h0, mulVec_zero, add_zero]`.

Use `⟨?_, fun a => ⟨hfix (Sum.inl a), hfix (Sum.inr (Sum.inl a))⟩, hfix (Sum.inr (Sum.inr ()))⟩` and prove the remaining obligations. Use `set H := _root_.Formalism.QuantumDeterminants.Hpk k r with hHdef`. Use `set V := _root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.colM B with hVdef`. Use `set V' := _root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.colM B' with hV'def`. Establish `hH : Hᴴ = H` using `_root_.Formalism.QuantumDeterminants.GBasic.Hpk_herm k r`.

Establish `gram : ∀ {C : Fin k → Fin (2 * r + k + 1) → ℂ}, _root_.Formalism.FourierDecayAlt.Q.IsFrameOf k r [z] C → (_root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.colM C)ᴴ * H * _root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.colM C = 1`. Introduce `C hC`. Use extensionality with `i j`. Rewrite using `[_root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.gramM_apply, hC.2.1 j i, Matrix.one_apply]`. Simplify using `[eq_comm]`.

Establish `hgramV : Vᴴ * H * V = 1` using `gram hB`. Establish `hgramV' : V'ᴴ * H * V' = 1` using `gram hB'`. Use `set M := Vᴴ * H * V' with hMdef`. Establish `hM : V' = V * M` using `colM_eq_mul_gram_of_isFrameOf hz hzz hB hB'`. Establish `hMM : Mᴴ * M = 1`.

Combine the equalities or inequalities in the displayed calculation. Establish `hG : ∀ X : Matrix (Fin k) (Fin (2 * r + k + 1)) ℂ, Vᴴ * (H * (V * X)) = X`. Introduce `X`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, hgramV, Matrix.one_mul]`. Establish `hQ : (M - 1) + (Mᴴ - 1) + (Mᴴ - 1) * (M - 1) = 0`.

Simplify using `only [sub_mul, mul_sub, hMM, Matrix.mul_one, Matrix.one_mul]`. Normalize the expressions using the abelian group laws. Use `show _ * H * _ = H`. Rewrite using `[swapMat_eq_one_add_sub_mul]`. Establish `hVV : V' - V = V * (M - 1)` using `by rw [Matrix.mul_sub, Matrix.mul_one, ← hM]`.

Rewrite using `[hVV]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [conjTranspose_add, conjTranspose_one, conjTranspose_mul, conjTranspose_conjTranspose, hH, conjTranspose_sub, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc, hG]`. Normalize the expressions using the abelian group laws. Use `_ = H := by rw [hQ]; simp`.
-/
private theorem swapMat_mem_UWset_of_isFrameOf {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : _root_.Formalism.QuantumDeterminants.inWb k r z)
    (hzz : _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) z z ≠ 0) {B B' : Fin k → Fin (2 * r + k + 1) → ℂ}
    (hB : _root_.Formalism.FourierDecayAlt.Q.IsFrameOf k r [z] B) (hB' : _root_.Formalism.FourierDecayAlt.Q.IsFrameOf k r [z] B') :
    _root_.GlobalTheory.FrameTrans.swapMat (_root_.Formalism.QuantumDeterminants.Hpk k r) B B' ∈ _root_.Formalism.QuantumDeterminants.UWset k r z := by
  have hfix : ∀ j, _root_.GlobalTheory.FrameTrans.swapMat (_root_.Formalism.QuantumDeterminants.Hpk k r) B B' *ᵥ _root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.cvec k r z j = _root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.cvec k r z j := by
    intro j
    rw [swapMat_mulVec']
    have h0 : (fun c => _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) (_root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.cvec k r z j) (B c)) = 0 := funext fun c => _root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.gram_VC hB c j
    rw [h0, mulVec_zero, add_zero]
  refine ⟨?_, fun a => ⟨hfix (Sum.inl a), hfix (Sum.inr (Sum.inl a))⟩, hfix (Sum.inr (Sum.inr ()))⟩
  set H := _root_.Formalism.QuantumDeterminants.Hpk k r with hHdef
  set V := _root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.colM B with hVdef
  set V' := _root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.colM B' with hV'def
  have hH : Hᴴ = H := _root_.Formalism.QuantumDeterminants.GBasic.Hpk_herm k r
  have gram : ∀ {C : Fin k → Fin (2 * r + k + 1) → ℂ}, _root_.Formalism.FourierDecayAlt.Q.IsFrameOf k r [z] C → (_root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.colM C)ᴴ * H * _root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.colM C = 1 := by
    intro C hC
    ext i j
    rw [_root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.gramM_apply, hC.2.1 j i, Matrix.one_apply]
    simp [eq_comm]
  have hgramV : Vᴴ * H * V = 1 := gram hB
  have hgramV' : V'ᴴ * H * V' = 1 := gram hB'
  set M := Vᴴ * H * V' with hMdef
  have hM : V' = V * M := colM_eq_mul_gram_of_isFrameOf hz hzz hB hB'
  have hMM : Mᴴ * M = 1 := by
    calc Mᴴ * M = Mᴴ * (Vᴴ * H * V) * M := by rw [hgramV, Matrix.mul_one]
      _ = (V * M)ᴴ * H * (V * M) := by simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [← hM, hgramV']
  have hG : ∀ X : Matrix (Fin k) (Fin (2 * r + k + 1)) ℂ, Vᴴ * (H * (V * X)) = X := by
    intro X; rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hgramV, Matrix.one_mul]
  have hQ : (M - 1) + (Mᴴ - 1) + (Mᴴ - 1) * (M - 1) = 0 := by
    simp only [sub_mul, mul_sub, hMM, Matrix.mul_one, Matrix.one_mul]; abel
  show _ * H * _ = H
  rw [swapMat_eq_one_add_sub_mul]
  have hVV : V' - V = V * (M - 1) := by rw [Matrix.mul_sub, Matrix.mul_one, ← hM]
  rw [hVV]
  calc (1 + V * (M - 1) * (Vᴴ * H))ᴴ * H * (1 + V * (M - 1) * (Vᴴ * H))
      = H + H * (V * (((M - 1) + (Mᴴ - 1) + (Mᴴ - 1) * (M - 1)) * (Vᴴ * H))) := by
        simp only [conjTranspose_add, conjTranspose_one, conjTranspose_mul, conjTranspose_conjTranspose, hH,
          conjTranspose_sub, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc, hG]
        abel
    _ = H := by rw [hQ]; simp

open Matrix in

/- English proof (translation)
Introduce `n r z hz hT`. Establish `hzz` using `_root_.Formalism.FourierDecayAlt.P.HermitianFormSums.hzz hT`. Establish `key : ∀ e, _root_.Formalism.QuantumDeterminants.inWb (n + 1) r e → _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk (n + 1) r) e z = 0 → _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk (n + 1) r) e e = 1 → ∃ B …`. Introduce `e he hez hee`. Take `⟨Bs, hBs⟩` from `_root_.Formalism.FourierDecayAlt.P.exists_frame_two n r z e hz hT he hez hee`.

Conclude with `⟨Fin.snoc Bs e, _root_.Formalism.FourierDecayAlt.P.FrameExtension.frame_snoc hBs he hez hee, by simp⟩`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Take `⟨e, he, hez, hee⟩` from `exists_unit_orth_in_Wb hz hT`. Take `⟨B', hB', -⟩` from `key e he hez hee`. Conclude with `⟨B', hB'⟩`.

Introduce `B hB w hw hwz`. Establish `hexp` using `_root_.Formalism.FourierDecayAlt.P.HermitianFormSums.complete0 hz hzz hB hw hwz`. Use `set S := ∑ a, Complex.normSq (_root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk (n + 1) r) w (B a)) with hS`. Establish `hww : _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk (n + 1) r) w w = (S : ℂ)` using `by conv_lhs => rw [hexp]`. Rewrite using `[_root_.Formalism.FourierDecayAlt.P.HermitianFormSums.herm_comb hB, hS]`.

Use `push_cast`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Conclude with `Complex.mul_conj _`. Establish `hS0 : 0 ≤ S` using `Finset.sum_nonneg fun a _ => Complex.normSq_nonneg _`. Establish `hre : (_root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk (n + 1) r) w w).re = S` using `by rw [hww, Complex.ofReal_re]`.

Establish `hone : _root_.GlobalTheory.FrameTrans.swapMat (_root_.Formalism.QuantumDeterminants.Hpk (n + 1) r) B B ∈ _root_.Formalism.QuantumDeterminants.UWset (n + 1) r z` using `swapMat_mem_UWset_of_isFrameOf hz hzz hB hB`. Distinguish the cases in `hw0 : w = 0`. Use `⟨0, 1, ?_, le_rfl, ?_, ?_⟩` and prove the remaining obligations. Rewrite `hone` using `[swapMat_eq_one_add_sub_mul, sub_self, Matrix.zero_mul, add_zero]`. Then use the resulting hypothesis. Rewrite using `[hre]`.

Substitute `hw0` using the available equality. Simplify using `[hS, _root_.Formalism.QuantumDeterminants.herm]`. Simplify using `[hw0]`. Establish `hSpos : 0 < S`. Use `lt_of_le_of_ne hS0 fun h0 => hw0 ?_` and prove the remaining obligations.

Rewrite using `[hexp]`. Use `Finset.sum_eq_zero fun a _ => ?_` and prove the remaining obligations. Use `(Finset.sum_eq_zero_iff_of_nonneg (fun a _ => Complex.normSq_nonneg _)).1 h0.symm a (Finset.mem_univ _)` as an intermediate fact. Rewrite using `[Complex.normSq_eq_zero.1 this, zero_smul]`. Use `set t := Real.sqrt S with htdef`.

Establish `ht0 : 0 < t` using `Real.sqrt_pos.2 hSpos`. Establish `htS : t ^ 2 = S` using `Real.sq_sqrt hS0`. Establish `htc : (t : ℂ) ≠ 0` using `by exact_mod_cast ht0.ne'`. Establish `he : _root_.Formalism.QuantumDeterminants.inWb (n + 1) r ((t : ℂ)⁻¹ • w)` using `fun i hi => by simp [hw i hi]`. Establish `hez : _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk (n + 1) r) ((t : ℂ)⁻¹ • w) z = 0`.

Rewrite using `[herm_smul_left_jet_harmonics, hwz, mul_zero]`. Establish `hee : _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk (n + 1) r) ((t : ℂ)⁻¹ • w) ((t : ℂ)⁻¹ • w) = 1`. Rewrite using `[herm_smul_left_jet_harmonics, herm_smul_right_jet_harmonics, hww, ← htS]`. Simplify using `only [star_inv₀, Complex.star_def, Complex.conj_ofReal]`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Take `⟨B', hB', hlast⟩` from `key _ he hez hee`. Use `⟨t, _root_.GlobalTheory.FrameTrans.swapMat (_root_.Formalism.QuantumDeterminants.Hpk (n + 1) r) B B', swapMat_mem_UWset_of_isFrameOf hz hzz hB hB', ht0.le, by rw [hre, htS], ?_⟩` and prove the remaining obligations. Establish `hsingle : (fun c => _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk (n + 1) r) (B (Fin.last n)) (B c)) = Pi.single (Fin.last n) 1`. Use function extensionality and compare the values at `c`.

Rewrite using `[hB.2.1]`. Simplify using `[Pi.single_apply, eq_comm]`. Rewrite using `[swapMat_mulVec', hsingle, Matrix.mulVec_single_one]`. Establish `hcol : (_root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.colM B' - _root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.colM B).col (Fin.last n) = B' (Fin.last n) - B (Fin.last n)`. Use function extensionality and compare the values at `p`.

Simplify using `[_root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.colM]`. Rewrite using `[hcol, add_sub_cancel, hlast, smul_smul, mul_inv_cancel₀ htc, one_smul]`.
-/
theorem _root_.GlobalTheory.frame_exists_and_vector_eq_smul_translate :
    ∀ (n r : ℕ) (z : (Fin (2 * r + (n + 1) + 1) → ℂ)), _root_.Formalism.QuantumDeterminants.inWb (n + 1) r z → 0 < _root_.Formalism.QuantumDeterminants.Tz (n + 1) r z →
      (∃ B : Fin (n + 1) → (Fin (2 * r + (n + 1) + 1) → ℂ), _root_.Formalism.FourierDecayAlt.Q.IsFrameOf (n + 1) r [z] B) ∧
      ∀ B : Fin (n + 1) → (Fin (2 * r + (n + 1) + 1) → ℂ), _root_.Formalism.FourierDecayAlt.Q.IsFrameOf (n + 1) r [z] B →
        ∀ w, _root_.Formalism.QuantumDeterminants.inWb (n + 1) r w → _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk (n + 1) r) w z = 0 →
          ∃ (t : ℝ), ∃ h ∈ _root_.Formalism.QuantumDeterminants.UWset (n + 1) r z, 0 ≤ t ∧ (_root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk (n + 1) r) w w).re = t ^ 2 ∧
            w = (t : ℂ) • (h *ᵥ B (Fin.last n)) := by
  intro n r z hz hT
  have hzz := _root_.Formalism.FourierDecayAlt.P.HermitianFormSums.hzz hT
  have key : ∀ e, _root_.Formalism.QuantumDeterminants.inWb (n + 1) r e → _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk (n + 1) r) e z = 0 →
      _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk (n + 1) r) e e = 1 →
        ∃ B' : Fin (n + 1) → (Fin (2 * r + (n + 1) + 1) → ℂ),
          _root_.Formalism.FourierDecayAlt.Q.IsFrameOf (n + 1) r [z] B' ∧ B' (Fin.last n) = e := by
    intro e he hez hee
    obtain ⟨Bs, hBs⟩ := _root_.Formalism.FourierDecayAlt.P.exists_frame_two n r z e hz hT he hez hee
    exact ⟨Fin.snoc Bs e, _root_.Formalism.FourierDecayAlt.P.FrameExtension.frame_snoc hBs he hez hee, by simp⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨e, he, hez, hee⟩ := exists_unit_orth_in_Wb hz hT
    obtain ⟨B', hB', -⟩ := key e he hez hee
    exact ⟨B', hB'⟩
  intro B hB w hw hwz
  have hexp := _root_.Formalism.FourierDecayAlt.P.HermitianFormSums.complete0 hz hzz hB hw hwz
  set S := ∑ a, Complex.normSq (_root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk (n + 1) r) w (B a)) with hS
  have hww : _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk (n + 1) r) w w = (S : ℂ) := by
    conv_lhs => rw [hexp]
    rw [_root_.Formalism.FourierDecayAlt.P.HermitianFormSums.herm_comb hB, hS]
    push_cast
    refine Finset.sum_congr rfl fun a _ => ?_
    exact Complex.mul_conj _
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun a _ => Complex.normSq_nonneg _
  have hre : (_root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk (n + 1) r) w w).re = S := by rw [hww, Complex.ofReal_re]
  have hone : _root_.GlobalTheory.FrameTrans.swapMat (_root_.Formalism.QuantumDeterminants.Hpk (n + 1) r) B B ∈ _root_.Formalism.QuantumDeterminants.UWset (n + 1) r z :=
    swapMat_mem_UWset_of_isFrameOf hz hzz hB hB
  by_cases hw0 : w = 0
  · refine ⟨0, 1, ?_, le_rfl, ?_, ?_⟩
    · rwa [swapMat_eq_one_add_sub_mul, sub_self, Matrix.zero_mul, add_zero] at hone
    · rw [hre]
      subst hw0
      simp [hS, _root_.Formalism.QuantumDeterminants.herm]
    · simp [hw0]
  have hSpos : 0 < S := by
    refine lt_of_le_of_ne hS0 fun h0 => hw0 ?_
    rw [hexp]
    refine Finset.sum_eq_zero fun a _ => ?_
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => Complex.normSq_nonneg _)).1 h0.symm a
      (Finset.mem_univ _)
    rw [Complex.normSq_eq_zero.1 this, zero_smul]
  set t := Real.sqrt S with htdef
  have ht0 : 0 < t := Real.sqrt_pos.2 hSpos
  have htS : t ^ 2 = S := Real.sq_sqrt hS0
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
  have he : _root_.Formalism.QuantumDeterminants.inWb (n + 1) r ((t : ℂ)⁻¹ • w) := fun i hi => by simp [hw i hi]
  have hez : _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk (n + 1) r) ((t : ℂ)⁻¹ • w) z = 0 := by
    rw [herm_smul_left_jet_harmonics, hwz, mul_zero]
  have hee : _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk (n + 1) r) ((t : ℂ)⁻¹ • w) ((t : ℂ)⁻¹ • w) = 1 := by
    rw [herm_smul_left_jet_harmonics, herm_smul_right_jet_harmonics, hww, ← htS]
    simp only [star_inv₀, Complex.star_def, Complex.conj_ofReal]
    push_cast
    field_simp
  obtain ⟨B', hB', hlast⟩ := key _ he hez hee
  refine ⟨t, _root_.GlobalTheory.FrameTrans.swapMat (_root_.Formalism.QuantumDeterminants.Hpk (n + 1) r) B B', swapMat_mem_UWset_of_isFrameOf hz hzz hB hB', ht0.le,
    by rw [hre, htS], ?_⟩
  have hsingle : (fun c => _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk (n + 1) r) (B (Fin.last n)) (B c)) = Pi.single (Fin.last n) 1 := by
    funext c
    rw [hB.2.1]
    simp [Pi.single_apply, eq_comm]
  rw [swapMat_mulVec', hsingle, Matrix.mulVec_single_one]
  have hcol : (_root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.colM B' - _root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.colM B).col (Fin.last n) = B' (Fin.last n) - B (Fin.last n) := by
    funext p
    simp [_root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.colM]
  rw [hcol, add_sub_cancel, hlast, smul_smul, mul_inv_cancel₀ htc, one_smul]

end GlobalTheory
