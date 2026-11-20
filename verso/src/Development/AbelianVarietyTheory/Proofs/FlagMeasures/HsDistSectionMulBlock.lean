import Mathlib
import Formalism.LocalRingCardinality.DataCD
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PerpendicularEmbedding
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousMatrixEntryAbsSum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CdScaleIsTrueScale
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousGaussSp

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot GlobalTheory.GaugeQuot GlobalTheory.Mem.Vol.Scale
open scoped ENNReal NNReal

namespace GlobalTheory.SectionHsCompare

variable {P Q P' Q' : ℕ}

section Frob
open scoped Matrix.Norms.Frobenius

/- English proof (translation)
Rewrite using `[Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity)]`. Simplify using `only [Real.rpow_two]`.
-/
theorem frob_sq (A : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :
    ‖A‖ ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity)]
  simp only [Real.rpow_two]

/- English proof (translation)
Establish `h : ∀ x, ∑ w, ‖Z x w‖ ^ 2 = ∑ o, ‖Z x (e o)‖ ^ 2` using `fun x => (e.sum_comp (fun w => ‖Z x w‖ ^ 2)).symm`. Rewrite using `[frob_sq, Finset.sum_congr rfl (fun x _ => h x), ← e.sum_comp (fun x => ∑ o, ‖Z x (e o)‖ ^ 2)]`. Simplify using `only [Fintype.sum_option, Finset.sum_add_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem frob_split (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q))
    (Z : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :
    ‖Z‖ ^ 2 = ‖Z (e none) (e none)‖ ^ 2 + ∑ b, ‖Z (e none) (e (some b))‖ ^ 2 +
      ∑ i, ‖Z (e (some i)) (e none)‖ ^ 2 + ∑ i, ∑ b, ‖Z (e (some i)) (e (some b))‖ ^ 2 := by
  have h : ∀ x, ∑ w, ‖Z x w‖ ^ 2 = ∑ o, ‖Z x (e o)‖ ^ 2 := fun x =>
    (e.sum_comp (fun w => ‖Z x w‖ ^ 2)).symm
  rw [frob_sq, Finset.sum_congr rfl (fun x _ => h x),
    ← e.sum_comp (fun x => ∑ o, ‖Z x (e o)‖ ^ 2)]
  simp only [Fintype.sum_option, Finset.sum_add_distrib]
  ring

/- English proof (translation)
Establish `h3 : 0 < 3 * t` using `by linarith`. Establish `hη0 : 0 ≤ η` using `by rw [hη]; exact div_nonneg (by linarith) h3.le`. Establish `key : η * (3 * t) = t - 1` using `by rw [hη]; field_simp`. Establish `hηt : η < 1 / 3` using `by nlinarith`. Prove the components needed by the constructor for the conclusion.

Establish `hW' : (1 - η) * R ≤ W` using `by linarith`. Establish `hsq : ((1 - η) * R) ^ 2 ≤ W ^ 2` using `pow_le_pow_left₀ (by nlinarith) hW' 2`. Establish `hge : 1 ≤ t * (1 - η) ^ 2` using `by nlinarith`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hsq (by linarith : (0 : ℝ) ≤ t), sq_nonneg R]`. Establish `hW' : W ≤ (1 + η) * R` using `by linarith`.

Establish `hsq : W ^ 2 ≤ ((1 + η) * R) ^ 2` using `pow_le_pow_left₀ hW hW' 2`. Establish `hle : (1 + η) ^ 2 ≤ t` using `by nlinarith`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right hle (sq_nonneg R)]`.
-/
theorem add_le_mul_pow_of_sq_le_of_le_mul {t η R W : ℝ} (ht : 1 < t) (hη : η = (t - 1) / (3 * t)) (hR : 0 ≤ R)
    (hW : 0 ≤ W) (h1 : W ≤ R + η * R) (h2 : R ≤ W + η * R) :
    R ^ 2 ≤ t * W ^ 2 ∧ W ^ 2 ≤ t * R ^ 2 := by
  have h3 : 0 < 3 * t := by linarith
  have hη0 : 0 ≤ η := by rw [hη]; exact div_nonneg (by linarith) h3.le
  have key : η * (3 * t) = t - 1 := by rw [hη]; field_simp
  have hηt : η < 1 / 3 := by nlinarith
  constructor
  ·
    have hW' : (1 - η) * R ≤ W := by linarith
    have hsq : ((1 - η) * R) ^ 2 ≤ W ^ 2 := pow_le_pow_left₀ (by nlinarith) hW' 2
    have hge : 1 ≤ t * (1 - η) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hsq (by linarith : (0 : ℝ) ≤ t), sq_nonneg R]
  ·
    have hW' : W ≤ (1 + η) * R := by linarith
    have hsq : W ^ 2 ≤ ((1 + η) * R) ^ 2 := pow_le_pow_left₀ hW hW' 2
    have hle : (1 + η) ^ 2 ≤ t := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hle (sq_nonneg R)]

/- English proof (translation)
Assume the negation of the conclusion as `hab`. Rewrite `hab` using `[not_le]`. Use the polynomial consequences of the given equalities and inequalities.
-/
private lemma le_of_sq_le_sq_of_nonneg {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  by_contra hab
  rw [not_le] at hab
  nlinarith

/- English proof (translation)
Introduce `P Q P' Q' e j hj t ht`. Use `set η : ℝ := (t - 1) / (3 * t) with hη`. Establish `hηpos : 0 < η` using `div_pos (by linarith) (by linarith)`. Establish `hη3 : η < 1 / 3`. Rewrite using `[hη, div_lt_iff₀ (by linarith)]; linarith`.

Use `set c : ℝ := η / 3 with hc`. Establish `hcpos : 0 < c` using `by positivity`. Establish `hc1 : c < 1` using `by linarith`. Use `⟨min 1 (c ^ 2), lt_min one_pos (by positivity), ?_⟩` and prove the remaining obligations. Introduce `y a hy hya hrow hblk g`.

Establish `hyc : ptSq e y < c ^ 2` using `lt_of_lt_of_le hy (min_le_right _ _)`. Establish `hy1 : ptSq e y < 1` using `lt_of_lt_of_le hy (min_le_left _ _)`. Take `⟨h00, h0b, ha0, hab⟩` from `hj g`. Establish `hcol : ∀ x, UpqT.mat a x (e none) = y x`. Introduce `x`.

Use `congrFun hya x` as an intermediate fact. Simplify `this` using `[act, baseVec, Matrix.mulVec, dotProduct, Pi.single_apply]`. Use `set S : ℝ := ∑ i, ‖y (e (some i))‖ ^ 2 with hS`. Establish `hS0 : 0 ≤ S` using `by positivity`. Establish `hpt : ptSq e y = ‖y (e none) - 1‖ ^ 2 + 2 * S` using `rfl`.

Establish `hSpt : S ≤ ptSq e y` using `by nlinarith [sq_nonneg ‖y (e none) - 1‖]`. Establish `hSc : S < c ^ 2` using `lt_of_le_of_lt hSpt hyc`. Establish `hS1 : S < 1` using `lt_of_le_of_lt hSpt hy1`. Establish `hn1 : 1 ≤ ‖1 + y (e none)‖`. Establish `h1 : ‖y (e none) - 1‖ < 1`.

Use polynomial arithmetic with `[norm_nonneg (y (e none) - 1), sq_nonneg ‖y (e none) - 1‖]`. Establish `h2 : (2 : ℂ) = (1 + y (e none)) - (y (e none) - 1)` using `by ring`. Establish `h3 : ‖(2 : ℂ)‖ ≤ ‖1 + y (e none)‖ + ‖y (e none) - 1‖`. Rewrite using `[h2]`. Conclude with `norm_sub_le _ _`.

Establish `h4 : ‖(2 : ℂ)‖ = 2` using `by simp`. Combine the linear equalities and inequalities to obtain the conclusion. Use `set M := UpqT.mat a with hM`. Use `set K := UpqT.mat (j g) - 1 with hK`. Use `set Ep : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ := Matrix.of fun x w => (e.symm x).elim 0 (fun _ => (e.symm w).elim 0 (fun _ => (M - 1) x w)) with hEp`.

Use `set Z0 := (M - 1) + K - Ep with hZ0`. Use `set Z := UpqT.mat (a * j g) - 1 with hZ`. Establish `hmul : UpqT.mat (a * j g) = M * UpqT.mat (j g)` using `rfl`. Establish `hZe : Z = (M - 1) + K + (M - 1) * K`. Rewrite using `[hZ, hmul, hK]`.

Use `noncomm_ring`. Establish `hdiff : Z - Z0 = Ep + (M - 1) * K`. Rewrite using `[hZe, hZ0]`. Normalize the expressions using the abelian group laws. Establish `hK2 : ‖K‖ ^ 2 = hsDist g`.

Rewrite using `[frob_split e K]`. Simplify using `[hK, Matrix.sub_apply, Matrix.one_apply, h00, h0b, ha0, hab, hsDist]`. Establish `hEp2 : ‖Ep‖ ^ 2 = ∑ i, ∑ b, ‖(M - 1) (e (some i)) (e (some b))‖ ^ 2`. Rewrite using `[frob_split e Ep]`. Simplify using `[hEp, Matrix.of_apply]`.

Establish `hEpS : ‖Ep‖ ^ 2 ≤ S ^ 2`. Rewrite using `[hEp2, sq, hS, Finset.sum_mul_sum]`. Use `Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun b _ => ?_` and prove the remaining obligations. Rewrite using `[hblk i b, div_pow, ← mul_pow]`. Establish `hp : 0 ≤ (‖y (e (some i))‖ * ‖y (e (some b))‖) ^ 2` using `sq_nonneg _`.

Combine the equalities or inequalities in the displayed calculation. Establish `hM2 : ‖M - 1‖ ^ 2 = ptSq e y + ‖Ep‖ ^ 2`. Rewrite using `[frob_split e (M - 1), hEp2, hpt]`. Simplify using `[Matrix.sub_apply, Matrix.one_apply, hcol, hrow]`. Rewrite using `[hS, Fintype.sum_sum_type]`.

Expand and normalize the polynomial expressions, which then agree. Establish `e00 : Z0 (e none) (e none) = y (e none) - 1`. Simplify using `[hZ0, hK, hEp, Matrix.of_apply, Matrix.sub_apply, Matrix.add_apply, hcol, h00]`. Establish `e0b : ∀ b, Z0 (e none) (e (some b)) = M (e none) (e (some b))`. Introduce `b`.

Simplify using `[hZ0, hK, hEp, Matrix.of_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply, h0b]`. Establish `ei0 : ∀ i, Z0 (e (some i)) (e none) = y (e (some i))`. Introduce `i`. Simplify using `[hZ0, hK, hEp, Matrix.of_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply, hcol, ha0]`. Establish `eib : ∀ i b, Z0 (e (some i)) (e (some b)) = (UpqT.mat g - 1) i b`.

Introduce `i b`. Simplify using `[hZ0, hK, hEp, Matrix.of_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply, hab]`. Establish `hZ02 : ‖Z0‖ ^ 2 = ptSq e y + hsDist g`. Rewrite using `[frob_split e Z0, e00]`. Simplify using `only [e0b, ei0, eib, hrow]`.

Rewrite using `[hpt, hS]`. Unfold `hsDist`. Expand and normalize the polynomial expressions, which then agree. Establish `hZ2 : ‖Z‖ ^ 2 = hsDist (a * j g)`. Rewrite using `[frob_sq]`.

Both sides reduce to the same expression. Establish `hR0 : 0 ≤ ‖Z0‖` using `norm_nonneg _`. Establish `hEpb : ‖Ep‖ ≤ c * ‖Z0‖`. Apply `le_of_sq_le_sq_of_nonneg (by positivity)` to reduce the goal to its premises. Rewrite using `[mul_pow, hZ02]`.

Establish `hg : 0 ≤ hsDist g` using `by rw [← hK2]; positivity`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_comm, mul_add]`. Conclude with `le_add_of_nonneg_right (mul_nonneg (sq_nonneg c) hg)`. Establish `hMb : ‖M - 1‖ ≤ 2 * c`.

Apply `le_of_sq_le_sq_of_nonneg (by positivity)` to reduce the goal to its premises. Rewrite using `[hM2]`. Establish `h1 : ‖Ep‖ ^ 2 ≤ c ^ 2`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : (2 * c) ^ 2 = 4 * c ^ 2` using `by ring`.

Rewrite using `[h2]`. Combine the linear relations using `[sq_nonneg c]`. Establish `hKb : ‖K‖ ≤ ‖Z0‖`. Apply `le_of_sq_le_sq_of_nonneg hR0` to reduce the goal to its premises. Rewrite using `[hK2, hZ02]`.

Establish `: 0 ≤ ptSq e y` using `by rw [hpt]; positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hdb : ‖Z - Z0‖ ≤ η * ‖Z0‖`. Rewrite using `[hdiff]`. Combine the equalities or inequalities in the displayed calculation.

Establish `h1 : ‖Z‖ ≤ ‖Z0‖ + η * ‖Z0‖`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : ‖Z0‖ ≤ ‖Z‖ + η * ‖Z0‖`. Combine the equalities or inequalities in the displayed calculation. Take `⟨hA, hB⟩` from `add_le_mul_pow_of_sq_le_of_le_mul ht hη hR0 (norm_nonneg _) h1 h2`.

Rewrite `hA`, `hB` using `[hZ02, hZ2]`. Conclude with `⟨hA, hB⟩`.
-/
theorem hsDist_section_mul_block : ∀ (P Q P' Q' : ℕ) (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (j : UpqT P' Q' → UpqT P Q), IsBlockEmb e j → ∀ t : ℝ, 1 < t → ∃ δ : ℝ, 0 < δ ∧ ∀ (y : Sp P Q) (a : UpqT P Q), ptSq e y < δ → act a (baseVec e) = y → (∀ b, ‖UpqT.mat a (e none) (e (some b))‖ = ‖y (e (some b))‖) → (∀ i b, ‖(UpqT.mat a - 1) (e (some i)) (e (some b))‖ = ‖y (e (some i))‖ * ‖y (e (some b))‖ / ‖1 + y (e none)‖) → ∀ g : UpqT P' Q', ptSq e y + hsDist g ≤ t * hsDist (a * j g) ∧ hsDist (a * j g) ≤ t * (ptSq e y + hsDist g) := by
  intro P Q P' Q' e j hj t ht
  set η : ℝ := (t - 1) / (3 * t) with hη
  have hηpos : 0 < η := div_pos (by linarith) (by linarith)
  have hη3 : η < 1 / 3 := by
    rw [hη, div_lt_iff₀ (by linarith)]; linarith
  set c : ℝ := η / 3 with hc
  have hcpos : 0 < c := by positivity
  have hc1 : c < 1 := by linarith
  refine ⟨min 1 (c ^ 2), lt_min one_pos (by positivity), ?_⟩
  intro y a hy hya hrow hblk g
  have hyc : ptSq e y < c ^ 2 := lt_of_lt_of_le hy (min_le_right _ _)
  have hy1 : ptSq e y < 1 := lt_of_lt_of_le hy (min_le_left _ _)
  obtain ⟨h00, h0b, ha0, hab⟩ := hj g

  have hcol : ∀ x, UpqT.mat a x (e none) = y x := by
    intro x
    have := congrFun hya x
    simpa [act, baseVec, Matrix.mulVec, dotProduct, Pi.single_apply] using this
  set S : ℝ := ∑ i, ‖y (e (some i))‖ ^ 2 with hS
  have hS0 : 0 ≤ S := by positivity
  have hpt : ptSq e y = ‖y (e none) - 1‖ ^ 2 + 2 * S := rfl
  have hSpt : S ≤ ptSq e y := by nlinarith [sq_nonneg ‖y (e none) - 1‖]
  have hSc : S < c ^ 2 := lt_of_le_of_lt hSpt hyc
  have hS1 : S < 1 := lt_of_le_of_lt hSpt hy1

  have hn1 : 1 ≤ ‖1 + y (e none)‖ := by
    have h1 : ‖y (e none) - 1‖ < 1 := by
      nlinarith [norm_nonneg (y (e none) - 1), sq_nonneg ‖y (e none) - 1‖]
    have h2 : (2 : ℂ) = (1 + y (e none)) - (y (e none) - 1) := by ring
    have h3 : ‖(2 : ℂ)‖ ≤ ‖1 + y (e none)‖ + ‖y (e none) - 1‖ := by
      rw [h2]; exact norm_sub_le _ _
    have h4 : ‖(2 : ℂ)‖ = 2 := by simp
    linarith

  set M := UpqT.mat a with hM
  set K := UpqT.mat (j g) - 1 with hK
  set Ep : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ := Matrix.of fun x w =>
    (e.symm x).elim 0 (fun _ => (e.symm w).elim 0 (fun _ => (M - 1) x w)) with hEp
  set Z0 := (M - 1) + K - Ep with hZ0
  set Z := UpqT.mat (a * j g) - 1 with hZ
  have hmul : UpqT.mat (a * j g) = M * UpqT.mat (j g) := rfl
  have hZe : Z = (M - 1) + K + (M - 1) * K := by
    rw [hZ, hmul, hK]; noncomm_ring
  have hdiff : Z - Z0 = Ep + (M - 1) * K := by
    rw [hZe, hZ0]; abel

  have hK2 : ‖K‖ ^ 2 = hsDist g := by
    rw [frob_split e K]
    simp [hK, Matrix.sub_apply, Matrix.one_apply, h00, h0b, ha0, hab, hsDist]
  have hEp2 : ‖Ep‖ ^ 2 = ∑ i, ∑ b, ‖(M - 1) (e (some i)) (e (some b))‖ ^ 2 := by
    rw [frob_split e Ep]
    simp [hEp, Matrix.of_apply]
  have hEpS : ‖Ep‖ ^ 2 ≤ S ^ 2 := by
    rw [hEp2, sq, hS, Finset.sum_mul_sum]
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun b _ => ?_
    rw [hblk i b, div_pow, ← mul_pow]
    have hp : 0 ≤ (‖y (e (some i))‖ * ‖y (e (some b))‖) ^ 2 := sq_nonneg _
    calc (‖y (e (some i))‖ * ‖y (e (some b))‖) ^ 2 / ‖1 + y (e none)‖ ^ 2
        ≤ (‖y (e (some i))‖ * ‖y (e (some b))‖) ^ 2 / 1 :=
          div_le_div_of_nonneg_left hp one_pos (by nlinarith)
      _ = (‖y (e (some i))‖ * ‖y (e (some b))‖) ^ 2 := div_one _
  have hM2 : ‖M - 1‖ ^ 2 = ptSq e y + ‖Ep‖ ^ 2 := by
    rw [frob_split e (M - 1), hEp2, hpt]
    simp [Matrix.sub_apply, Matrix.one_apply, hcol, hrow]
    rw [hS, Fintype.sum_sum_type]
    ring
  have e00 : Z0 (e none) (e none) = y (e none) - 1 := by
    simp [hZ0, hK, hEp, Matrix.of_apply, Matrix.sub_apply, Matrix.add_apply, hcol, h00]
  have e0b : ∀ b, Z0 (e none) (e (some b)) = M (e none) (e (some b)) := by
    intro b
    simp [hZ0, hK, hEp, Matrix.of_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply, h0b]
  have ei0 : ∀ i, Z0 (e (some i)) (e none) = y (e (some i)) := by
    intro i
    simp [hZ0, hK, hEp, Matrix.of_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply, hcol, ha0]
  have eib : ∀ i b, Z0 (e (some i)) (e (some b)) = (UpqT.mat g - 1) i b := by
    intro i b
    simp [hZ0, hK, hEp, Matrix.of_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply, hab]
  have hZ02 : ‖Z0‖ ^ 2 = ptSq e y + hsDist g := by
    rw [frob_split e Z0, e00]
    simp only [e0b, ei0, eib, hrow]
    rw [hpt, hS]
    unfold hsDist
    ring
  have hZ2 : ‖Z‖ ^ 2 = hsDist (a * j g) := by
    rw [frob_sq]; rfl

  have hR0 : 0 ≤ ‖Z0‖ := norm_nonneg _
  have hEpb : ‖Ep‖ ≤ c * ‖Z0‖ := by
    apply le_of_sq_le_sq_of_nonneg (by positivity)
    rw [mul_pow, hZ02]
    have hg : 0 ≤ hsDist g := by rw [← hK2]; positivity
    calc ‖Ep‖ ^ 2 ≤ S ^ 2 := hEpS
      _ = S * S := sq S
      _ ≤ S * c ^ 2 := mul_le_mul_of_nonneg_left hSc.le hS0
      _ ≤ ptSq e y * c ^ 2 := mul_le_mul_of_nonneg_right hSpt (sq_nonneg c)
      _ ≤ c ^ 2 * (ptSq e y + hsDist g) := by
        rw [mul_comm, mul_add]; exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg c) hg)
  have hMb : ‖M - 1‖ ≤ 2 * c := by
    apply le_of_sq_le_sq_of_nonneg (by positivity)
    rw [hM2]
    have h1 : ‖Ep‖ ^ 2 ≤ c ^ 2 :=
      calc ‖Ep‖ ^ 2 ≤ S ^ 2 := hEpS
        _ = S * S := sq S
        _ ≤ S * c ^ 2 := mul_le_mul_of_nonneg_left hSc.le hS0
        _ ≤ 1 * c ^ 2 := mul_le_mul_of_nonneg_right hS1.le (sq_nonneg c)
        _ = c ^ 2 := one_mul _
    have h2 : (2 * c) ^ 2 = 4 * c ^ 2 := by ring
    rw [h2]
    linarith [sq_nonneg c]
  have hKb : ‖K‖ ≤ ‖Z0‖ := by
    apply le_of_sq_le_sq_of_nonneg hR0
    rw [hK2, hZ02]
    have : 0 ≤ ptSq e y := by rw [hpt]; positivity
    linarith
  have hdb : ‖Z - Z0‖ ≤ η * ‖Z0‖ := by
    rw [hdiff]
    calc ‖Ep + (M - 1) * K‖ ≤ ‖Ep‖ + ‖(M - 1) * K‖ := norm_add_le _ _
      _ ≤ ‖Ep‖ + ‖M - 1‖ * ‖K‖ := by gcongr; exact Matrix.frobenius_norm_mul _ _
      _ ≤ c * ‖Z0‖ + 2 * c * ‖Z0‖ := by gcongr
      _ = η * ‖Z0‖ := by rw [hc]; ring
  have h1 : ‖Z‖ ≤ ‖Z0‖ + η * ‖Z0‖ := by
    calc ‖Z‖ = ‖Z0 + (Z - Z0)‖ := by rw [add_sub_cancel]
      _ ≤ ‖Z0‖ + ‖Z - Z0‖ := norm_add_le _ _
      _ ≤ ‖Z0‖ + η * ‖Z0‖ := by gcongr
  have h2 : ‖Z0‖ ≤ ‖Z‖ + η * ‖Z0‖ := by
    calc ‖Z0‖ = ‖Z - (Z - Z0)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖Z‖ + ‖Z - Z0‖ := norm_sub_le _ _
      _ ≤ ‖Z‖ + η * ‖Z0‖ := by gcongr
  obtain ⟨hA, hB⟩ := add_le_mul_pow_of_sq_le_of_le_mul ht hη hR0 (norm_nonneg _) h1 h2
  rw [hZ02, hZ2] at hA hB
  exact ⟨hA, hB⟩

end Frob

end GlobalTheory.SectionHsCompare
