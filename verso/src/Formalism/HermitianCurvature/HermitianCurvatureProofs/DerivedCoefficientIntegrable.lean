import Formalism.HermitianCurvature.StatementLE
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ShiftBound
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DegreeOfProdLinearLe
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeightedL2BoundedMul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Cauchy
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Markov

namespace Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE

/- English proof (translation)
Introduce `B X c M p N hN hdw hM hJ hP hNF hPol hCw hBF`. Conclude with `h3 B X c M hdw hM hJ hP (h2 h1 B X p N hN hdw hM hNF) hPol hCw hBF`.
-/
theorem lemmaEprimeFull_fromSteps (h1 : WeightedIntegrable) (h2 : EpCoefInt) (h3 : LemmaEprime) :
    LemmaEprimeFull := by
  intro B X c M p N hN hdw hM hJ hP hNF hPol hCw hBF
  exact h3 B X c M hdw hM hJ hP (h2 h1 B X p N hN hdw hM hNF) hPol hCw hBF

/- English proof (translation)
The claim follows from `A.stepClaimFromSteps_full hC hMV thetaForm thetaRange thetaSmooth thetaBound thetaLimit cutTheta leibniz A.termZero coefIntegrable adj A.eFinite csTerm A.shiftBound markovTerm A.termBound A.geomSum A.energyStep A.absorb A.uniformBound fatouStep domConv`.
-/
theorem stepClaim (hC : E.CauchyTheta) (hMV : E.MarkovVector) : StepClaim :=
  A.stepClaimFromSteps_full hC hMV thetaForm thetaRange thetaSmooth thetaBound thetaLimit cutTheta
    leibniz A.termZero coefIntegrable adj A.eFinite csTerm A.shiftBound markovTerm A.termBound
    A.geomSum A.energyStep A.absorb A.uniformBound fatouStep domConv

/- English proof (translation)
Introduce `N`. Proceed by induction on `N with`. Consider the case `zero`. Introduce `Y _`. Rewrite using `[List.ofFn_zero]`.

Conclude with `trivial`. Consider the case `succ N ih`. Introduce `Y hY`. Rewrite using `[List.ofFn_succ]`. Use `show Y 0 ∈ S.box (List.ofFn fun i => Y i.succ).length ∧ S.OnBoxes (List.ofFn fun i => Y i.succ)`.

Use `⟨?_, ih _ (fun i => ?_)⟩` and prove the remaining obligations. Use `hY 0 using 2` and compare the differences between its conclusion and the goal. Simplify using `only [List.length_ofFn, Fin.val_zero]`. Use linear arithmetic over natural numbers and integers. Use `hY i.succ using 2` and compare the differences between its conclusion and the goal.

Simplify using `only [Fin.val_succ]`. Use linear arithmetic over natural numbers and integers.
-/
private theorem onBoxes_ofFn_of_mem_box (S : Formalism.FourierDecayAlt.LE.Sys) : ∀ (N : ℕ) (Y : Fin N → ℝ),
    (∀ a : Fin N, Y a ∈ S.box (N - 1 - (a : ℕ))) → S.OnBoxes (List.ofFn Y) := by
  intro N
  induction N with
  | zero =>
    intro Y _
    rw [List.ofFn_zero]
    exact trivial
  | succ N ih =>
    intro Y hY
    rw [List.ofFn_succ]
    show Y 0 ∈ S.box (List.ofFn fun i => Y i.succ).length ∧ S.OnBoxes (List.ofFn fun i => Y i.succ)
    refine ⟨?_, ih _ (fun i => ?_)⟩
    · convert hY 0 using 2
      simp only [List.length_ofFn, Fin.val_zero]
      omega
    · convert hY i.succ using 2
      simp only [Fin.val_succ]
      omega

/- English proof (translation)
Introduce `N`. Proceed by induction on `N with`. Consider the case `zero`. Introduce `Y _ a`. Conclude with `a.elim0`.

Consider the case `succ N ih`. Introduce `Y hY a`. Rewrite `hY` using `[List.ofFn_succ]`. Establish `hY' : Y 0 ∈ S.box (List.ofFn fun i => Y i.succ).length ∧ S.OnBoxes (List.ofFn fun i => Y i.succ)` using `hY`. Proceed by induction on `a using Fin.cases with`.

Consider the case `zero`. Use `hY'.1 using 2` and compare the differences between its conclusion and the goal. Simplify using `only [List.length_ofFn, Fin.val_zero]`. Use linear arithmetic over natural numbers and integers. Consider the case `succ i`.

Use `ih _ hY'.2 i using 2` and compare the differences between its conclusion and the goal. Simplify using `only [Fin.val_succ]`. Use linear arithmetic over natural numbers and integers.
-/
private theorem mem_box_of_onBoxes_ofFn (S : Formalism.FourierDecayAlt.LE.Sys) : ∀ (N : ℕ) (Y : Fin N → ℝ),
    S.OnBoxes (List.ofFn Y) → ∀ a : Fin N, Y a ∈ S.box (N - 1 - (a : ℕ)) := by
  intro N
  induction N with
  | zero =>
    intro Y _ a
    exact a.elim0
  | succ N ih =>
    intro Y hY a
    rw [List.ofFn_succ] at hY
    have hY' : Y 0 ∈ S.box (List.ofFn fun i => Y i.succ).length ∧
        S.OnBoxes (List.ofFn fun i => Y i.succ) := hY
    induction a using Fin.cases with
    | zero =>
      convert hY'.1 using 2
      simp only [List.length_ofFn, Fin.val_zero]
      omega
    | succ i =>
      convert ih _ hY'.2 i using 2
      simp only [Fin.val_succ]
      omega

/- English proof (translation)
Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_empty, Finset.sum_empty, ← MvPolynomial.C_1, MvPolynomial.degreeOf_C]`. Introduce `a s ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.sum_insert ha]`. Conclude with `(MvPolynomial.degreeOf_mul_le _ _ _).trans (Nat.add_le_add_left ih _)`.
-/
private theorem degreeOf_prod_le_sum_degreeOf {σ ι : Type} (i : σ) (s : Finset ι) (f : ι → MvPolynomial σ ℝ) :
    MvPolynomial.degreeOf i (∏ j ∈ s, f j) ≤ ∑ j ∈ s, MvPolynomial.degreeOf i (f j) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.prod_empty, Finset.sum_empty, ← MvPolynomial.C_1, MvPolynomial.degreeOf_C]
  · intro a s ha ih
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (MvPolynomial.degreeOf_mul_le _ _ _).trans (Nat.add_le_add_left ih _)

/- English proof (translation)
Use `(MvPolynomial.degreeOf_mul_le _ _ _).trans ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.degreeOf_C, zero_add]`. Use `(degreeOf_prod_le_sum_degreeOf i _ _).trans ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_erase_add _ _ (Finset.mem_univ i)]`. Establish `h1 : ∑ a ∈ Finset.univ.erase i, MvPolynomial.degreeOf i (∏ s : Fin m, (MvPolynomial.X a + MvPolynomial.C (lam s))) = 0`.

Use `Finset.sum_eq_zero (fun a ha => ?_)` and prove the remaining obligations. Establish `hai : a ≠ i` using `Finset.ne_of_mem_erase ha`. Use `Nat.eq_zero_of_le_zero ((degreeOf_prod_le_sum_degreeOf i _ _).trans (le_of_eq (Finset.sum_eq_zero (fun s _ => ?_))))` and prove the remaining obligations. Use `Nat.eq_zero_of_le_zero ((MvPolynomial.degreeOf_add_le _ _ _).trans ?_)` and prove the remaining obligations. Rewrite using `[MvPolynomial.degreeOf_X, MvPolynomial.degreeOf_C, if_neg (Ne.symm hai)]`.

Simplify using the standard rewrite rules. Rewrite using `[h1, zero_add]`. Use `(degreeOf_prod_le_sum_degreeOf i _ _).trans ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `(MvPolynomial.degreeOf_add_le _ _ _).trans ?_` and prove the remaining obligations.

Rewrite using `[MvPolynomial.degreeOf_X, MvPolynomial.degreeOf_C, if_pos rfl]`. Use the proof step `simp)`. Use `_ = m := by simp`.
-/
private theorem degreeOf_C_mul_prod_X_add_C_le (N m : ℕ) (c : ℝ) (lam : Fin m → ℝ) (i : Fin N) :
    MvPolynomial.degreeOf i (MvPolynomial.C c *
      ∏ a : Fin N, ∏ s : Fin m, (MvPolynomial.X a + MvPolynomial.C (lam s))) ≤ m := by
  classical
  refine (MvPolynomial.degreeOf_mul_le _ _ _).trans ?_
  rw [MvPolynomial.degreeOf_C, zero_add]
  refine (degreeOf_prod_le_sum_degreeOf i _ _).trans ?_
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  have h1 : ∑ a ∈ Finset.univ.erase i,
      MvPolynomial.degreeOf i (∏ s : Fin m, (MvPolynomial.X a + MvPolynomial.C (lam s))) = 0 := by
    refine Finset.sum_eq_zero (fun a ha => ?_)
    have hai : a ≠ i := Finset.ne_of_mem_erase ha
    refine Nat.eq_zero_of_le_zero ((degreeOf_prod_le_sum_degreeOf i _ _).trans (le_of_eq (Finset.sum_eq_zero (fun s _ => ?_))))
    refine Nat.eq_zero_of_le_zero ((MvPolynomial.degreeOf_add_le _ _ _).trans ?_)
    rw [MvPolynomial.degreeOf_X, MvPolynomial.degreeOf_C, if_neg (Ne.symm hai)]
    simp
  rw [h1, zero_add]
  refine (degreeOf_prod_le_sum_degreeOf i _ _).trans ?_
  calc ∑ s : Fin m, MvPolynomial.degreeOf i (MvPolynomial.X i + MvPolynomial.C (lam s))
      ≤ ∑ _s : Fin m, 1 := Finset.sum_le_sum (fun s _ => by
        refine (MvPolynomial.degreeOf_add_le _ _ _).trans ?_
        rw [MvPolynomial.degreeOf_X, MvPolynomial.degreeOf_C, if_pos rfl]
        simp)
    _ = m := by simp

/- English proof (translation)
Introduce `k r N C₂ C₆ I hN hC₂ hC₆ hI`. Establish `hNr : (r:ℝ) + 1 ≤ N` using `by exact_mod_cast hN`. Establish `hr0 : (0:ℝ) ≤ r` using `Nat.cast_nonneg _`. Establish `hN0 : (0:ℝ) ≤ N` using `Nat.cast_nonneg _`. Establish `hk0 : (0:ℝ) ≤ k` using `Nat.cast_nonneg _`.

Establish `hQ0 : (0:ℝ) ≤ ((r:ℝ) + 1) ^ 2` using `by positivity`. Establish `hkNQ : (0:ℝ) ≤ (k:ℝ) * N * ((r:ℝ) + 1) ^ 2` using `by positivity`. Establish `hN2Q : (0:ℝ) ≤ (N:ℝ) ^ 2 * ((r:ℝ) + 1) ^ 2` using `by positivity`. Establish `h26 : C₂ ≤ C₆` using `by linarith`. Establish `hC6 : 0 ≤ C₆` using `by linarith`.

Establish `e1 : C₂ * ((k:ℝ) * N * ((r:ℝ) + 1) ^ 2) ≤ C₆ * ((k:ℝ) * N * ((r:ℝ) + 1) ^ 2)` using `mul_le_mul_of_nonneg_right h26 hkNQ`. Establish `e2 : (6 * C₂) * ((N:ℝ) ^ 2 * ((r:ℝ) + 1) ^ 2) ≤ C₆ * ((N:ℝ) ^ 2 * ((r:ℝ) + 1) ^ 2)` using `mul_le_mul_of_nonneg_right hC₆ hN2Q`. Establish `e3 : ((r:ℝ) + 1) * (N * ((r:ℝ) + 1) ^ 2) ≤ (N:ℝ) * (N * ((r:ℝ) + 1) ^ 2)` using `mul_le_mul_of_nonneg_right hNr (by positivity)`. Establish `e4 : C₂ * (((r:ℝ) + 1) * (N * ((r:ℝ) + 1) ^ 2)) ≤ C₂ * ((N:ℝ) * (N * ((r:ℝ) + 1) ^ 2))` using `mul_le_mul_of_nonneg_left e3 hC₂.le`. Establish `e5 : 0 ≤ C₂ * ((N:ℝ) * ((r:ℝ) + 1) ^ 2)` using `by positivity`.

Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Use the polynomial consequences of the given equalities and inequalities. Use `push_cast`. Use the polynomial consequences of the given equalities and inequalities. Use the polynomial consequences of the given equalities and inequalities.
-/
private theorem le_constants_proof : Formalism.FourierDecayAlt.LE.Constants := by
  intro k r N C₂ C₆ I hN hC₂ hC₆ hI
  have hNr : (r:ℝ) + 1 ≤ N := by exact_mod_cast hN
  have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg _
  have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg _
  have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg _
  have hQ0 : (0:ℝ) ≤ ((r:ℝ) + 1) ^ 2 := by positivity
  have hkNQ : (0:ℝ) ≤ (k:ℝ) * N * ((r:ℝ) + 1) ^ 2 := by positivity
  have hN2Q : (0:ℝ) ≤ (N:ℝ) ^ 2 * ((r:ℝ) + 1) ^ 2 := by positivity
  have h26 : C₂ ≤ C₆ := by linarith
  have hC6 : 0 ≤ C₆ := by linarith
  have e1 : C₂ * ((k:ℝ) * N * ((r:ℝ) + 1) ^ 2) ≤ C₆ * ((k:ℝ) * N * ((r:ℝ) + 1) ^ 2) :=
    mul_le_mul_of_nonneg_right h26 hkNQ
  have e2 : (6 * C₂) * ((N:ℝ) ^ 2 * ((r:ℝ) + 1) ^ 2) ≤ C₆ * ((N:ℝ) ^ 2 * ((r:ℝ) + 1) ^ 2) :=
    mul_le_mul_of_nonneg_right hC₆ hN2Q
  have e3 : ((r:ℝ) + 1) * (N * ((r:ℝ) + 1) ^ 2) ≤ (N:ℝ) * (N * ((r:ℝ) + 1) ^ 2) :=
    mul_le_mul_of_nonneg_right hNr (by positivity)
  have e4 : C₂ * (((r:ℝ) + 1) * (N * ((r:ℝ) + 1) ^ 2)) ≤ C₂ * ((N:ℝ) * (N * ((r:ℝ) + 1) ^ 2)) :=
    mul_le_mul_of_nonneg_left e3 hC₂.le
  have e5 : 0 ≤ C₂ * ((N:ℝ) * ((r:ℝ) + 1) ^ 2) := by positivity
  refine ⟨?_, ?_, ?_⟩
  · nlinarith
  · push_cast
    nlinarith
  · nlinarith

/- English proof (translation)
Introduce `n lam α β h`. Distinguish the cases in `hab : α ≤ β`. Use `⟨∏ s, (if -lam s < α then (1:ℝ) else -1), ?_, ?_⟩` and prove the remaining obligations. Use `Finset.prod_induction _ (fun x : ℝ => x = 1 ∨ x = -1) ?_ ?_ ?_` and prove the remaining obligations. Apply the tactic sequence `rintro a b (rfl | rfl) (rfl | rfl) <;> norm_num`.

Use `left`. Both sides reduce to the same expression. Apply the tactic sequence `intro s _ split_ifs <;> simp`. Introduce `Y hY`. Rewrite using `[Finset.abs_prod, ← Finset.prod_mul_distrib]`.

Use `Finset.prod_congr rfl (fun s _ => ?_)` and prove the remaining obligations. Establish `hs` using `h s`. Use `split_ifs with hlt`. Rewrite using `[abs_of_pos (by linarith [hY.1])]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hb : β < -lam s`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `hs ⟨not_lt.mp hlt, hc⟩`. Rewrite using `[abs_of_neg (by linarith [hY.2])]`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `⟨1, Or.inl rfl, fun Y hY => absurd (le_trans hY.1 hY.2) hab⟩`.
-/
private theorem le_constSign_proof : Formalism.FourierDecayAlt.LE.ConstSign := by
  intro n lam α β h
  classical
  by_cases hab : α ≤ β
  · refine ⟨∏ s, (if -lam s < α then (1:ℝ) else -1), ?_, ?_⟩
    · refine Finset.prod_induction _ (fun x : ℝ => x = 1 ∨ x = -1) ?_ ?_ ?_
      · rintro a b (rfl | rfl) (rfl | rfl) <;> norm_num
      · left; rfl
      · intro s _
        split_ifs <;> simp
    · intro Y hY
      rw [Finset.abs_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl (fun s _ => ?_)
      have hs := h s
      split_ifs with hlt
      · rw [abs_of_pos (by linarith [hY.1])]
        ring
      · have hb : β < -lam s := by
          by_contra hc
          push_neg at hc
          exact hs ⟨not_lt.mp hlt, hc⟩
        rw [abs_of_neg (by linarith [hY.2])]
        ring
  · exact ⟨1, Or.inl rfl, fun Y hY => absurd (le_trans hY.1 hY.2) hab⟩

/- English proof (translation)
Introduce `S hL hfit`. Establish `hL0 : 0 < S.L` using `by linarith`. Establish `hN0 : (0:ℝ) ≤ S.Ntot` using `Nat.cast_nonneg _`. Establish `hαβ : S.α ≤ S.β` using `by nlinarith [mul_nonneg hN0 hL0.le]`. Establish `hmid : ∀ a, a < S.Ntot → S.box a ⊆ Set.Icc (S.α + (S.β - S.α) / 3) (S.β - (S.β - S.α) / 3)`.

Introduce `a ha x hx`. Establish `ha1 : a + 1 ≤ S.Ntot` using `ha`. Establish `ha' : (a:ℝ) + 1 ≤ S.Ntot` using `by exact_mod_cast ha1`. Establish `ha0 : (0:ℝ) ≤ a` using `Nat.cast_nonneg _`. Take `⟨hx1, hx2⟩` from `hx`.

Establish `h1 : 0 ≤ 2 * (a:ℝ) * S.L` using `by positivity`. Establish `h2` using `mul_le_mul_of_nonneg_right ha' hL0.le`. Prove the components needed by the constructor for the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Use the polynomial consequences of the given equalities and inequalities.

Establish `hsep : ∀ a b, a < b → ∀ x ∈ S.box a, ∀ y ∈ S.box b, S.L ≤ y - x`. Introduce `a b hab x hx y hy`. Establish `hab1 : a + 1 ≤ b` using `hab`. Establish `hab' : (a:ℝ) + 1 ≤ b` using `by exact_mod_cast hab1`. Take `⟨hx1, hx2⟩` from `hx`.

Take `⟨hy1, hy2⟩` from `hy`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right hab' hL0.le]`. Use `⟨hmid, hsep, ?_⟩` and prove the remaining obligations. Establish `hmem : ∀ w : List ℝ, S.OnBoxes w → ∀ Z ∈ w, ∃ j, j < w.length ∧ Z ∈ S.box j`. Introduce `w`.

Proceed by induction on `w with`. Consider the case `nil`. Introduce `_ Z hZ`. Simplify using `at hZ`. Consider the case `cons Y w ih`.

Introduce `hOn Z hZ`. Establish `hOn' : Y ∈ S.box w.length ∧ S.OnBoxes w` using `hOn`. Break down `List.mem_cons.mp hZ with rfl | hZ'` into its components or cases. Conclude with `⟨w.length, by simp only [List.length_cons]; omega, hOn'.1⟩`. Take `⟨j, hj, hZj⟩` from `ih hOn'.2 Z hZ'`.

Conclude with `⟨j, by simp only [List.length_cons]; omega, hZj⟩`. Establish `hin : ∀ j, j < S.Ntot → ∀ x ∈ S.box j, x ∈ Set.Icc S.α S.β`. Introduce `j hj x hx`. Establish `hx'` using `hmid j hj hx`. Conclude with `⟨by linarith [hx'.1], by linarith [hx'.2]⟩`.

Introduce `w`. Proceed by induction on `w with`. Consider the case `nil`. Introduce `_ _`. Use `⟨fun x hx => ?_, List.Pairwise.nil⟩` and prove the remaining obligations.

Simplify using `[Formalism.FourierDecayAlt.LE.plus] at hx`. Consider the case `cons Y w ih`. Introduce `hOn hlen`. Establish `hOn' : Y ∈ S.box w.length ∧ S.OnBoxes w` using `hOn`. Establish `hlen' : w.length < S.Ntot`.

Simplify using `only [List.length_cons] at hlen`. Use linear arithmetic over natural numbers and integers. Take `⟨ih1, ih2⟩` from `ih hOn'.2 (by omega)`. Use `show (∀ x ∈ (true, Y) :: Formalism.FourierDecayAlt.LE.plus w, x.2 ∈ Set.Icc S.α S.β) ∧ ((true, Y) :: Formalism.FourierDecayAlt.LE.plus w).Pairwise fun x y => 2 < |x.2 - y.2|`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Introduce `x hx`. Break down `List.mem_cons.mp hx with rfl | hx'` into its components or cases. Conclude with `hin _ hlen' _ hOn'.1`. Conclude with `ih1 x hx'`. Use `List.Pairwise.cons ?_ ih2` and prove the remaining obligations.

Introduce `z hz`. Take `⟨Z, hZ, rfl⟩` from `List.mem_map.mp hz`. Take `⟨j, hj, hZj⟩` from `hmem w hOn'.2 Z hZ`. Establish `hd` using `hsep j w.length hj Z hZj Y hOn'.1`. Use `show 2 < |Y - Z|`.

Rewrite using `[abs_of_pos (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem le_boxesFit_proof : Formalism.FourierDecayAlt.LE.BoxesFit := by
  intro S hL hfit
  have hL0 : 0 < S.L := by linarith
  have hN0 : (0:ℝ) ≤ S.Ntot := Nat.cast_nonneg _
  have hαβ : S.α ≤ S.β := by nlinarith [mul_nonneg hN0 hL0.le]
  have hmid : ∀ a, a < S.Ntot →
      S.box a ⊆ Set.Icc (S.α + (S.β - S.α) / 3) (S.β - (S.β - S.α) / 3) := by
    intro a ha x hx
    have ha1 : a + 1 ≤ S.Ntot := ha
    have ha' : (a:ℝ) + 1 ≤ S.Ntot := by exact_mod_cast ha1
    have ha0 : (0:ℝ) ≤ a := Nat.cast_nonneg _
    obtain ⟨hx1, hx2⟩ := hx
    have h1 : 0 ≤ 2 * (a:ℝ) * S.L := by positivity
    have h2 := mul_le_mul_of_nonneg_right ha' hL0.le
    constructor
    · linarith
    · nlinarith
  have hsep : ∀ a b, a < b → ∀ x ∈ S.box a, ∀ y ∈ S.box b, S.L ≤ y - x := by
    intro a b hab x hx y hy
    have hab1 : a + 1 ≤ b := hab
    have hab' : (a:ℝ) + 1 ≤ b := by exact_mod_cast hab1
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hy
    nlinarith [mul_le_mul_of_nonneg_right hab' hL0.le]
  refine ⟨hmid, hsep, ?_⟩
  have hmem : ∀ w : List ℝ, S.OnBoxes w → ∀ Z ∈ w, ∃ j, j < w.length ∧ Z ∈ S.box j := by
    intro w
    induction w with
    | nil =>
      intro _ Z hZ
      simp at hZ
    | cons Y w ih =>
      intro hOn Z hZ
      have hOn' : Y ∈ S.box w.length ∧ S.OnBoxes w := hOn
      rcases List.mem_cons.mp hZ with rfl | hZ'
      · exact ⟨w.length, by simp only [List.length_cons]; omega, hOn'.1⟩
      · obtain ⟨j, hj, hZj⟩ := ih hOn'.2 Z hZ'
        exact ⟨j, by simp only [List.length_cons]; omega, hZj⟩
  have hin : ∀ j, j < S.Ntot → ∀ x ∈ S.box j, x ∈ Set.Icc S.α S.β := by
    intro j hj x hx
    have hx' := hmid j hj hx
    exact ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
  intro w
  induction w with
  | nil =>
    intro _ _
    refine ⟨fun x hx => ?_, List.Pairwise.nil⟩
    simp [Formalism.FourierDecayAlt.LE.plus] at hx
  | cons Y w ih =>
    intro hOn hlen
    have hOn' : Y ∈ S.box w.length ∧ S.OnBoxes w := hOn
    have hlen' : w.length < S.Ntot := by
      simp only [List.length_cons] at hlen
      omega
    obtain ⟨ih1, ih2⟩ := ih hOn'.2 (by omega)
    show (∀ x ∈ (true, Y) :: Formalism.FourierDecayAlt.LE.plus w, x.2 ∈ Set.Icc S.α S.β) ∧
      ((true, Y) :: Formalism.FourierDecayAlt.LE.plus w).Pairwise fun x y => 2 < |x.2 - y.2|
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hin _ hlen' _ hOn'.1
      · exact ih1 x hx'
    · refine List.Pairwise.cons ?_ ih2
      intro z hz
      obtain ⟨Z, hZ, rfl⟩ := List.mem_map.mp hz
      obtain ⟨j, hj, hZj⟩ := hmem w hOn'.2 Z hZ
      have hd := hsep j w.length hj Z hZj Y hOn'.1
      show 2 < |Y - Z|
      rw [abs_of_pos (by linarith)]
      linarith

/- English proof (translation)
Introduce `hStep hInd S σ CR Cd CP hσ hCR hCd hCP hL hbig hJL2 hImp`. Use `hInd S hJL2 ?_` and prove the remaining obligations. Introduce `w Y hOn hlen hint`. Establish `hOn' : Y ∈ S.box w.length ∧ S.OnBoxes w` using `hOn`. Establish `hY : Y ∈ (S.step w).J` using `by show Y ∈ Set.Icc (S.step w).a ((S.step w).a + (S.step w).L)`.

Rewrite using `[S.step_a, S.step_L]`. Conclude with `hOn'.1`. Establish `hst` using `hStep S.B (S.step w) S.c σ CR Cd CP hσ hCR hCd hCP (by rw [S.step_L]; exact hL) (by rw [S.step_r, S.step_L]; exact hbig) (hImp w hOn'.2 hlen) hint Y hY`. Establish `hfun : S.dens (Y :: w) = fun ω => Formalism.FourierDecayAlt.LE.sq S.B ((S.step w).d Y) ((S.step w).gX Y) ω`. Use function extensionality and compare the values at `(S.step_new w Y)`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hfun]`. Conclude with `hst.1`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[S.step_P]`.

Both sides reduce to the same expression.
-/
private theorem le_claimAll_proof : Formalism.FourierDecayAlt.LE.ClaimAll := by
  intro hStep hInd S σ CR Cd CP hσ hCR hCd hCP hL hbig hJL2 hImp
  refine hInd S hJL2 ?_
  intro w Y hOn hlen hint
  have hOn' : Y ∈ S.box w.length ∧ S.OnBoxes w := hOn
  have hY : Y ∈ (S.step w).J := by
    show Y ∈ Set.Icc (S.step w).a ((S.step w).a + (S.step w).L)
    rw [S.step_a, S.step_L]
    exact hOn'.1
  have hst := hStep S.B (S.step w) S.c σ CR Cd CP hσ hCR hCd hCP (by rw [S.step_L]; exact hL)
    (by rw [S.step_r, S.step_L]; exact hbig) (hImp w hOn'.2 hlen) hint Y hY
  have hfun : S.dens (Y :: w) = fun ω => Formalism.FourierDecayAlt.LE.sq S.B ((S.step w).d Y) ((S.step w).gX Y) ω :=
    funext (S.step_new w Y)
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact hst.1
  · calc ∫ ω, S.dens (Y :: w) ω ∂S.B.μ
        = ∫ ω, Formalism.FourierDecayAlt.LE.sq S.B ((S.step w).d Y) ((S.step w).gX Y) ω ∂S.B.μ := by rw [hfun]
      _ = |(S.step w).P Y| * (S.step w).A0 := hst.2
      _ = |S.P Y| * ∫ ω, S.dens w ω ∂S.B.μ := by
        rw [S.step_P]
        rfl

/- English proof (translation)
Introduce `S hJL2 hstep w`. Proceed by induction on `w with`. Consider the case `nil`. Introduce `_ _`. Use `⟨hJL2, ?_⟩` and prove the remaining obligations.

Simplify using `only [Formalism.FourierDecayAlt.LE.Sys.size, Formalism.FourierDecayAlt.LE.plus, List.map_nil, List.prod_nil, one_mul]`. Both sides reduce to the same expression. Consider the case `cons Y w ih`. Introduce `hOn hlen`. Establish `hOn' : Y ∈ S.box w.length ∧ S.OnBoxes w` using `hOn`.

Establish `hlen' : w.length < S.Ntot`. Simplify using `only [List.length_cons] at hlen`. Use linear arithmetic over natural numbers and integers. Take `⟨hi, he⟩` from `ih hOn'.2 hlen'.le`. Establish `h` using `hstep w Y hOn hlen' hi`.

Use `⟨h.1, ?_⟩` and prove the remaining obligations. Rewrite using `[h.2, he]`. Simplify using `only [Formalism.FourierDecayAlt.LE.Sys.size, Formalism.FourierDecayAlt.LE.plus, List.map_cons, List.prod_cons]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem le_claimInduction_proof : Formalism.FourierDecayAlt.LE.ClaimInduction := by
  intro S hJL2 hstep w
  induction w with
  | nil =>
    intro _ _
    refine ⟨hJL2, ?_⟩
    simp only [Formalism.FourierDecayAlt.LE.Sys.size, Formalism.FourierDecayAlt.LE.plus, List.map_nil, List.prod_nil, one_mul]
    rfl
  | cons Y w ih =>
    intro hOn hlen
    have hOn' : Y ∈ S.box w.length ∧ S.OnBoxes w := hOn
    have hlen' : w.length < S.Ntot := by
      simp only [List.length_cons] at hlen
      omega
    obtain ⟨hi, he⟩ := ih hOn'.2 hlen'.le
    have h := hstep w Y hOn hlen' hi
    refine ⟨h.1, ?_⟩
    rw [h.2, he]
    simp only [Formalism.FourierDecayAlt.LE.Sys.size, Formalism.FourierDecayAlt.LE.plus, List.map_cons, List.prod_cons]
    ring

/- English proof (translation)
Introduce `hConst hRed hGrid hSign hFit hAll hStep hInd hBL hLB hLA hLL2 hPL hCL2 hLeib hCut`. Introduce `CR Cd CP hCR hCd hCP C₂ hC₂ C₆ hC₆ S hN hL hI hRO hI1 hJL2 hThm hImp hFam`. Establish `hC₂64 : 64 ≤ C₂` using `le_trans (le_mul_of_one_le_right (by norm_num) (le_add_of_nonneg_right (by positivity))) hC₂`. Establish `hN1' : 1 ≤ S.Ntot` using `by omega`. Establish `hN1 : (1:ℝ) ≤ S.Ntot` using `by exact_mod_cast hN1'`.

Establish `hr0 : (0:ℝ) ≤ S.r` using `Nat.cast_nonneg _`. Establish `hQ : (1:ℝ) ≤ ((S.r:ℝ) + 1) ^ 2` using `by nlinarith`. Establish `hNQ : (1:ℝ) ≤ (S.Ntot:ℝ) * ((S.r:ℝ) + 1) ^ 2` using `by nlinarith`. Establish `hNQ0 : (0:ℝ) ≤ (S.Ntot:ℝ) * ((S.r:ℝ) + 1) ^ 2` using `by linarith`. Establish `hL64 : 64 ≤ S.L`.

Rewrite using `[hL]`. Use polynomial arithmetic with `[mul_le_mul hC₂64 hNQ (by norm_num) (by linarith)]`. Establish `hL2 : 2 < S.L` using `by linarith`. Establish `hL0 : 0 < S.L` using `by linarith`. Take `⟨-, -, h6⟩` from `hConst S.k S.r S.Ntot C₂ C₆ (S.β - S.α) hN (by linarith) hC₆ hI`.

Establish `hfit : 6 * (S.Ntot:ℝ) * S.L ≤ S.β - S.α`. Rewrite using `[hL]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hσ : (4:ℝ) ≤ 4 * (S.Ntot:ℝ)` using `by linarith`. Establish `hclaims` using `hAll hStep hInd S (4 * (S.Ntot:ℝ)) CR Cd CP hσ hCR hCd hCP hL0 (by rw [hL]; nlinarith [mul_le_mul_of_nonneg_right hC₂ hNQ0]) hJL2 hImp`.

Establish `hBox` using `hBL hLB hLA hLL2 hPL hCL2 hLeib hCut S hL0 hFam hThm hclaims`. Conclude with `hRed hGrid hSign hFit S hL2 hfit hRO hI1 hBox`.
-/
private theorem le_eFromConstituents_proof : Formalism.FourierDecayAlt.LE.LemmaEFromSteps := by
  intro hConst hRed hGrid hSign hFit hAll hStep hInd hBL hLB hLA hLL2 hPL hCL2 hLeib hCut
  intro CR Cd CP hCR hCd hCP C₂ hC₂ C₆ hC₆ S hN hL hI hRO hI1 hJL2 hThm hImp hFam
  have hC₂64 : 64 ≤ C₂ :=
    le_trans (le_mul_of_one_le_right (by norm_num) (le_add_of_nonneg_right (by positivity))) hC₂
  have hN1' : 1 ≤ S.Ntot := by omega
  have hN1 : (1:ℝ) ≤ S.Ntot := by exact_mod_cast hN1'
  have hr0 : (0:ℝ) ≤ S.r := Nat.cast_nonneg _
  have hQ : (1:ℝ) ≤ ((S.r:ℝ) + 1) ^ 2 := by nlinarith
  have hNQ : (1:ℝ) ≤ (S.Ntot:ℝ) * ((S.r:ℝ) + 1) ^ 2 := by nlinarith
  have hNQ0 : (0:ℝ) ≤ (S.Ntot:ℝ) * ((S.r:ℝ) + 1) ^ 2 := by linarith
  have hL64 : 64 ≤ S.L := by
    rw [hL]
    nlinarith [mul_le_mul hC₂64 hNQ (by norm_num) (by linarith)]
  have hL2 : 2 < S.L := by linarith
  have hL0 : 0 < S.L := by linarith
  obtain ⟨-, -, h6⟩ := hConst S.k S.r S.Ntot C₂ C₆ (S.β - S.α) hN (by linarith) hC₆ hI
  have hfit : 6 * (S.Ntot:ℝ) * S.L ≤ S.β - S.α := by
    rw [hL]
    linarith
  have hσ : (4:ℝ) ≤ 4 * (S.Ntot:ℝ) := by linarith
  have hclaims := hAll hStep hInd S (4 * (S.Ntot:ℝ)) CR Cd CP hσ hCR hCd hCP hL0
    (by rw [hL]; nlinarith [mul_le_mul_of_nonneg_right hC₂ hNQ0]) hJL2 hImp
  have hBox := hBL hLB hLA hLL2 hPL hCL2 hLeib hCut S hL0 hFam hThm hclaims
  exact hRed hGrid hSign hFit S hL2 hfit hRO hI1 hBox

/- English proof (translation)
Introduce `hGrid hSign hFit S hL hfit hRO hI1 hBox w hw hlen`. Take `⟨sg0, -, hsg⟩` from `hSign (S.k + 2 * S.r + 1) S.lam S.α S.β hRO`. Take `⟨hmid, -, hadm⟩` from `hFit S hL hfit`. Establish `hL0 : 0 < S.L` using `by linarith`. It suffices to establish `h : ∀ (N : ℕ) (sg : Fin N → Bool) (Y : Fin N → ℝ), S.admitted (List.ofFn fun a => (sg a, Y a)) → N ≤ S.Ntot → Filter.Tendsto (fun ε : ℝ => S.principalHermitianLattice ε (List.ofFn fun a => (sg a, Y a))) (nhdsWithin 0 (Set.Ioi 0)) (nhds (S.size (List.ofFn fun a => (sg a, Y a)) * S …`.

Establish `hwe : (List.ofFn fun a : Fin w.length => ((w.get a).1, (w.get a).2)) = w`. Simplify using `only [Prod.mk.eta]`. Conclude with `List.ofFn_get w`. Establish `h'` using `h w.length (fun a => (w.get a).1) (fun a => (w.get a).2) (by rw [hwe]; exact hw) hlen`. Rewrite `h'` using `[hwe]`.

Conclude with `h'`. Introduce `N sg Y hadmY hN`. Establish `hex : ∀ ε : ℝ, ∃ Q : MvPolynomial (Fin N) ℝ, (∀ a, Q.degreeOf a ≤ S.k + 2 * S.r + 1) ∧ (0 < ε → ∀ (sg' : Fin N → Bool) (Y' : Fin N → ℝ), S.admitted (List.ofFn fun a => (sg' a, Y' a)) → S.principalHermitianLattice ε (List.ofFn fun a => (sg' a, Y' a)) = MvPolynomial.eval Y' Q)`. Introduce `ε`. Distinguish the cases in `hε : 0 < ε`.

Take `⟨Q, hQ1, hQ2⟩` from `hI1 ε hε N hN`. Conclude with `⟨Q, hQ1, fun _ => hQ2⟩`. Conclude with `⟨0, fun a => by simp, fun h => absurd h hε⟩`. Use `choose Qf hQf using hex`. Use `set Q₀ : MvPolynomial (Fin N) ℝ := MvPolynomial.C (sg0 ^ N * S.jn) * ∏ a : Fin N, ∏ s : Fin (S.k + 2 * S.r + 1), (MvPolynomial.X a + MvPolynomial.C (S.lam s)) with hQ₀`.

Establish `hdeg0 : ∀ a, Q₀.degreeOf a ≤ S.k + 2 * S.r + 1` using `fun a => degreeOf_C_mul_prod_X_add_C_le _ _ _ _ a`. Establish `hval : ∀ Y' : Fin N → ℝ, (∀ a, Y' a ∈ Set.Icc S.α S.β) → ∀ sg' : Fin N → Bool, S.size (List.ofFn fun a => (sg' a, Y' a)) * S.jn = MvPolynomial.eval Y' Q₀`. Introduce `Y' hY' sg'`. Establish `habs : ∀ a, |S.P (Y' a)| = sg0 * ∏ s, (Y' a + S.lam s)` using `fun a => hsg (Y' a) (hY' a)`. Simplify using `only [Formalism.FourierDecayAlt.LE.Sys.size, List.map_ofFn, List.prod_ofFn, Function.comp_apply]`.

Rewrite using `[hQ₀]`. Simplify using `only [map_mul, map_prod, map_add, MvPolynomial.eval_C, MvPolynomial.eval_X]`. Simplify using `only [habs, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Expand and normalize the polynomial expressions, which then agree. Establish `hc : (0:ℝ) < ((S.k + 2 * S.r + 1 : ℕ) : ℝ) + 1` using `by positivity`.

Set `grid : Fin N → Finset ℝ` to `fun a => (Finset.range (S.k + 2 * S.r + 1 + 1)).image (fun i : ℕ => S.α + (S.β - S.α) / 3 + 2 * ((N - 1 - (a : ℕ) : ℕ) : ℝ) * S.L + (i : ℝ) * (S.L / (((S.k + 2 * S.r + 1 : ℕ) : ℝ) + 1)))`. Establish `hcard : ∀ a, (grid a).card = S.k + 2 * S.r + 1 + 1`. Introduce `a`. Rewrite using `[Finset.card_image_of_injective _ (fun i j hij => by`. Establish `hq : (0:ℝ) < S.L / (((S.k + 2 * S.r + 1 : ℕ) : ℝ) + 1)` using `div_pos hL0 hc`.

Establish `h2` using `add_left_cancel hij`. Conclude with `mul_right_cancel₀ hq.ne' h2)]` after adjusting the coercions. Conclude with `Finset.card_range _`. Establish `hconv : ∀ Y' : Fin N → ℝ, (∀ a, Y' a ∈ grid a) → Filter.Tendsto (fun t => MvPolynomial.eval Y' (Qf t)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (MvPolynomial.eval Y' Q₀))`. Introduce `Y' hY'`.

Establish `hbox : ∀ a : Fin N, Y' a ∈ S.box (N - 1 - (a : ℕ))`. Introduce `a`. Take `⟨i, hi, hiY⟩` from `Finset.mem_image.mp (hY' a)`. Rewrite using `[← hiY]`. Establish `hi' : (i:ℝ) ≤ ((S.k + 2 * S.r + 1 : ℕ) : ℝ)`.

Conclude with `(Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))` after adjusting the coercions. Establish `h0 : 0 ≤ (i:ℝ) * (S.L / (((S.k + 2 * S.r + 1 : ℕ) : ℝ) + 1))` using `mul_nonneg (Nat.cast_nonneg _) (div_nonneg hL0.le hc.le)`. Establish `h1 : (i:ℝ) * (S.L / (((S.k + 2 * S.r + 1 : ℕ) : ℝ) + 1)) ≤ S.L`. Rewrite using `[mul_div_assoc', div_le_iff₀ hc]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right hi' hL0.le]`.

Prove the components needed by the constructor for the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hOnY : S.OnBoxes (List.ofFn Y')` using `onBoxes_ofFn_of_mem_box S N Y' hbox`. Establish `hb` using `hBox (List.ofFn Y') hOnY (by rw [List.length_ofFn]; exact hN)`.

Establish `hplus : Formalism.FourierDecayAlt.LE.plus (List.ofFn Y') = List.ofFn fun a => (true, Y' a)`. Simplify using `only [Formalism.FourierDecayAlt.LE.plus, List.map_ofFn]`. Both sides reduce to the same expression. Establish `hIcc : ∀ a, Y' a ∈ Set.Icc S.α S.β` using `fun a => by`. Establish `ha` using `a.isLt`.

Establish `hm` using `hmid (N - 1 - (a : ℕ)) (by omega) (hbox a)`. Establish `hαβ : S.α ≤ S.β` using `by linarith [hm.1, hm.2]`. Conclude with `⟨by linarith [hm.1], by linarith [hm.2]⟩`. Rewrite `hb` using `[hplus, hval Y' hIcc (fun _ => true)]`. Use `hb.congr' ?_` and prove the remaining obligations.

Use `filter_upwards [self_mem_nhdsWithin] with ε hε`. Establish `hA` using `hadm (List.ofFn Y') hOnY (by rw [List.length_ofFn]; exact hN)`. Rewrite `hA` using `[hplus]`. Conclude with `(hQf ε).2 hε (fun _ => true) Y' hA`. Establish `hlim` using `hGrid N (S.k + 2 * S.r + 1) ℝ (nhdsWithin 0 (Set.Ioi 0)) Qf Q₀ grid (fun t a => (hQf t).1 a) hdeg0 hcard hconv Y`.

Take `⟨hA1, -⟩` from `id hadmY`. Establish `hIcc : ∀ a, Y a ∈ Set.Icc S.α S.β` using `fun a => hA1 (sg a, Y a) (by simp only [List.mem_ofFn]; exact ⟨a, rfl⟩)`. Rewrite using `[hval Y hIcc sg]`. Use `hlim.congr' ?_` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin] with ε hε`.

Conclude with `((hQf ε).2 hε sg Y hadmY).symm`.
-/
private theorem le_reduceToBoxes_proof : Formalism.FourierDecayAlt.LE.ReduceToBoxes := by
  intro hGrid hSign hFit S hL hfit hRO hI1 hBox w hw hlen
  classical
  obtain ⟨sg0, -, hsg⟩ := hSign (S.k + 2 * S.r + 1) S.lam S.α S.β hRO
  obtain ⟨hmid, -, hadm⟩ := hFit S hL hfit
  have hL0 : 0 < S.L := by linarith
  suffices h : ∀ (N : ℕ) (sg : Fin N → Bool) (Y : Fin N → ℝ),
      S.admitted (List.ofFn fun a => (sg a, Y a)) → N ≤ S.Ntot →
      Filter.Tendsto (fun ε : ℝ => S.principalHermitianLattice ε (List.ofFn fun a => (sg a, Y a))) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (S.size (List.ofFn fun a => (sg a, Y a)) * S.jn)) by
    have hwe : (List.ofFn fun a : Fin w.length => ((w.get a).1, (w.get a).2)) = w := by
      simp only [Prod.mk.eta]
      exact List.ofFn_get w
    have h' := h w.length (fun a => (w.get a).1) (fun a => (w.get a).2) (by rw [hwe]; exact hw) hlen
    rw [hwe] at h'
    exact h'
  intro N sg Y hadmY hN
  have hex : ∀ ε : ℝ, ∃ Q : MvPolynomial (Fin N) ℝ,
      (∀ a, Q.degreeOf a ≤ S.k + 2 * S.r + 1) ∧
      (0 < ε → ∀ (sg' : Fin N → Bool) (Y' : Fin N → ℝ), S.admitted (List.ofFn fun a => (sg' a, Y' a)) →
        S.principalHermitianLattice ε (List.ofFn fun a => (sg' a, Y' a)) = MvPolynomial.eval Y' Q) := by
    intro ε
    by_cases hε : 0 < ε
    · obtain ⟨Q, hQ1, hQ2⟩ := hI1 ε hε N hN
      exact ⟨Q, hQ1, fun _ => hQ2⟩
    · exact ⟨0, fun a => by simp, fun h => absurd h hε⟩
  choose Qf hQf using hex
  set Q₀ : MvPolynomial (Fin N) ℝ := MvPolynomial.C (sg0 ^ N * S.jn) *
    ∏ a : Fin N, ∏ s : Fin (S.k + 2 * S.r + 1), (MvPolynomial.X a + MvPolynomial.C (S.lam s)) with hQ₀
  have hdeg0 : ∀ a, Q₀.degreeOf a ≤ S.k + 2 * S.r + 1 := fun a => degreeOf_C_mul_prod_X_add_C_le _ _ _ _ a
  have hval : ∀ Y' : Fin N → ℝ, (∀ a, Y' a ∈ Set.Icc S.α S.β) → ∀ sg' : Fin N → Bool,
      S.size (List.ofFn fun a => (sg' a, Y' a)) * S.jn = MvPolynomial.eval Y' Q₀ := by
    intro Y' hY' sg'
    have habs : ∀ a, |S.P (Y' a)| = sg0 * ∏ s, (Y' a + S.lam s) := fun a => hsg (Y' a) (hY' a)
    simp only [Formalism.FourierDecayAlt.LE.Sys.size, List.map_ofFn, List.prod_ofFn, Function.comp_apply]
    rw [hQ₀]
    simp only [map_mul, map_prod, map_add, MvPolynomial.eval_C, MvPolynomial.eval_X]
    simp only [habs, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    ring
  have hc : (0:ℝ) < ((S.k + 2 * S.r + 1 : ℕ) : ℝ) + 1 := by positivity
  let grid : Fin N → Finset ℝ := fun a => (Finset.range (S.k + 2 * S.r + 1 + 1)).image
    (fun i : ℕ => S.α + (S.β - S.α) / 3 + 2 * ((N - 1 - (a : ℕ) : ℕ) : ℝ) * S.L +
      (i : ℝ) * (S.L / (((S.k + 2 * S.r + 1 : ℕ) : ℝ) + 1)))
  have hcard : ∀ a, (grid a).card = S.k + 2 * S.r + 1 + 1 := by
    intro a
    rw [Finset.card_image_of_injective _ (fun i j hij => by
      have hq : (0:ℝ) < S.L / (((S.k + 2 * S.r + 1 : ℕ) : ℝ) + 1) := div_pos hL0 hc
      have h2 := add_left_cancel hij
      exact_mod_cast mul_right_cancel₀ hq.ne' h2)]
    exact Finset.card_range _
  have hconv : ∀ Y' : Fin N → ℝ, (∀ a, Y' a ∈ grid a) →
      Filter.Tendsto (fun t => MvPolynomial.eval Y' (Qf t)) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (MvPolynomial.eval Y' Q₀)) := by
    intro Y' hY'
    have hbox : ∀ a : Fin N, Y' a ∈ S.box (N - 1 - (a : ℕ)) := by
      intro a
      obtain ⟨i, hi, hiY⟩ := Finset.mem_image.mp (hY' a)
      rw [← hiY]
      have hi' : (i:ℝ) ≤ ((S.k + 2 * S.r + 1 : ℕ) : ℝ) := by
        exact_mod_cast (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
      have h0 : 0 ≤ (i:ℝ) * (S.L / (((S.k + 2 * S.r + 1 : ℕ) : ℝ) + 1)) :=
        mul_nonneg (Nat.cast_nonneg _) (div_nonneg hL0.le hc.le)
      have h1 : (i:ℝ) * (S.L / (((S.k + 2 * S.r + 1 : ℕ) : ℝ) + 1)) ≤ S.L := by
        rw [mul_div_assoc', div_le_iff₀ hc]
        nlinarith [mul_le_mul_of_nonneg_right hi' hL0.le]
      constructor
      · linarith
      · linarith
    have hOnY : S.OnBoxes (List.ofFn Y') := onBoxes_ofFn_of_mem_box S N Y' hbox
    have hb := hBox (List.ofFn Y') hOnY (by rw [List.length_ofFn]; exact hN)
    have hplus : Formalism.FourierDecayAlt.LE.plus (List.ofFn Y') = List.ofFn fun a => (true, Y' a) := by
      simp only [Formalism.FourierDecayAlt.LE.plus, List.map_ofFn]
      rfl
    have hIcc : ∀ a, Y' a ∈ Set.Icc S.α S.β := fun a => by
      have ha := a.isLt
      have hm := hmid (N - 1 - (a : ℕ)) (by omega) (hbox a)
      have hαβ : S.α ≤ S.β := by linarith [hm.1, hm.2]
      exact ⟨by linarith [hm.1], by linarith [hm.2]⟩
    rw [hplus, hval Y' hIcc (fun _ => true)] at hb
    refine hb.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hA := hadm (List.ofFn Y') hOnY (by rw [List.length_ofFn]; exact hN)
    rw [hplus] at hA
    exact (hQf ε).2 hε (fun _ => true) Y' hA
  have hlim := hGrid N (S.k + 2 * S.r + 1) ℝ (nhdsWithin 0 (Set.Ioi 0)) Qf Q₀ grid
    (fun t a => (hQf t).1 a) hdeg0 hcard hconv Y
  obtain ⟨hA1, -⟩ := id hadmY
  have hIcc : ∀ a, Y a ∈ Set.Icc S.α S.β := fun a =>
    hA1 (sg a, Y a) (by simp only [List.mem_ofFn]; exact ⟨a, rfl⟩)
  rw [hval Y hIcc sg]
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact ((hQf ε).2 hε sg Y hadmY).symm

/- English proof (translation)
Introduce `hLB hLA hLL2 hPL hCL2 hLeib hCut S hL0 hFam hThm hClaim w hw hlen`. It suffices to establish `h : ∀ (N : ℕ) (Y : Fin N → ℝ), S.OnBoxes (List.ofFn Y) → N ≤ S.Ntot → Filter.Tendsto (fun ε : ℝ => S.principalHermitianLattice ε (Formalism.FourierDecayAlt.LE.plus (List.ofFn Y))) (nhdsWithin 0 (Set.Ioi 0)) (nhds (S.size (Formalism.FourierDecayAlt.LE.plus (List.ofFn Y)) * S.jn)) …`. Establish `h'` using `h w.length w.get (by rw [List.ofFn_get]; exact hw) hlen`. Rewrite `h'` using `[List.ofFn_get]`. Conclude with `h'`.

Introduce `N Y hOn hN`. Establish `hInt : ∀ Y' : Fin N → ℝ, (S.fam N).On Y' → MeasureTheory.Integrable (Formalism.FourierDecayAlt.LE.sq S.B ((S.fam N).dw Y') ((S.fam N).gw Y' (S.fam N).u)) S.B.μ`. Introduce `Y' hY'`. Establish `hOn' : S.OnBoxes (List.ofFn Y')` using `onBoxes_ofFn_of_mem_box S N Y' (fun a => by`. Establish `h` using `hY' a`.

Rewrite `h` using `[S.fam_J]`. Conclude with `h)`. Establish `hc` using `(hClaim (List.ofFn Y') hOn' (by rw [List.length_ofFn]; exact hN)).1`. Establish `hfun : S.dens (List.ofFn Y') = fun ω => Formalism.FourierDecayAlt.LE.sq S.B ((S.fam N).dw Y') ((S.fam N).gw Y' (S.fam N).u) ω`. Use function extensionality and compare the values at `(S.fam_dens N Y')`.

Rewrite `hc` using `[hfun]`. Conclude with `hc`. Establish `hJinf : ∀ a, ((S.fam N).J a).Infinite`. Introduce `a`. Rewrite using `[S.fam_J]`.

Conclude with `Set.Icc_infinite (by linarith)`. Establish `hOnF : ∀ a, Y a ∈ (S.fam N).J a`. Introduce `a`. Establish `h` using `mem_box_of_onBoxes_ofFn S N Y hOn a`. Rewrite using `[S.fam_J]`.

Conclude with `h`. Establish `hlim` using `hLB hLA hLL2 hPL hCL2 hLeib hCut S.B N (S.fam N) S.c hJinf (hFam N hN) hInt Y hOnF`. Establish `hval : S.size (Formalism.FourierDecayAlt.LE.plus (List.ofFn Y)) * S.jn = ∫ ω, Formalism.FourierDecayAlt.LE.sq S.B ((S.fam N).dw Y) ((S.fam N).gw Y (S.fam N).u) ω ∂S.B.μ`. Rewrite using `[← (hClaim (List.ofFn Y) hOn (by rw [List.length_ofFn]; exact hN)).2]`. Conclude with `congrArg (MeasureTheory.integral S.B.μ) (funext fun ω => S.fam_dens N Y ω)`.

Rewrite using `[hval]`. Use `hlim.congr' ?_` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin] with ε hε`. Conclude with `(hThm N Y hN hOn ε hε).symm`.
-/
private theorem le_boxLimitFromClaim_proof : Formalism.FourierDecayAlt.LE.BoxLimitFromClaim := by
  intro hLB hLA hLL2 hPL hCL2 hLeib hCut S hL0 hFam hThm hClaim w hw hlen
  suffices h : ∀ (N : ℕ) (Y : Fin N → ℝ), S.OnBoxes (List.ofFn Y) → N ≤ S.Ntot →
      Filter.Tendsto (fun ε : ℝ => S.principalHermitianLattice ε (Formalism.FourierDecayAlt.LE.plus (List.ofFn Y))) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (S.size (Formalism.FourierDecayAlt.LE.plus (List.ofFn Y)) * S.jn)) by
    have h' := h w.length w.get (by rw [List.ofFn_get]; exact hw) hlen
    rw [List.ofFn_get] at h'
    exact h'
  intro N Y hOn hN
  have hInt : ∀ Y' : Fin N → ℝ, (S.fam N).On Y' →
      MeasureTheory.Integrable
        (Formalism.FourierDecayAlt.LE.sq S.B ((S.fam N).dw Y') ((S.fam N).gw Y' (S.fam N).u)) S.B.μ := by
    intro Y' hY'
    have hOn' : S.OnBoxes (List.ofFn Y') := onBoxes_ofFn_of_mem_box S N Y' (fun a => by
      have h := hY' a
      rw [S.fam_J] at h
      exact h)
    have hc := (hClaim (List.ofFn Y') hOn' (by rw [List.length_ofFn]; exact hN)).1
    have hfun : S.dens (List.ofFn Y') =
        fun ω => Formalism.FourierDecayAlt.LE.sq S.B ((S.fam N).dw Y') ((S.fam N).gw Y' (S.fam N).u) ω :=
      funext (S.fam_dens N Y')
    rw [hfun] at hc
    exact hc
  have hJinf : ∀ a, ((S.fam N).J a).Infinite := by
    intro a
    rw [S.fam_J]
    exact Set.Icc_infinite (by linarith)
  have hOnF : ∀ a, Y a ∈ (S.fam N).J a := by
    intro a
    have h := mem_box_of_onBoxes_ofFn S N Y hOn a
    rw [S.fam_J]
    exact h
  have hlim := hLB hLA hLL2 hPL hCL2 hLeib hCut S.B N (S.fam N) S.c hJinf (hFam N hN) hInt Y hOnF
  have hval : S.size (Formalism.FourierDecayAlt.LE.plus (List.ofFn Y)) * S.jn =
      ∫ ω, Formalism.FourierDecayAlt.LE.sq S.B ((S.fam N).dw Y) ((S.fam N).gw Y (S.fam N).u) ω ∂S.B.μ := by
    rw [← (hClaim (List.ofFn Y) hOn (by rw [List.length_ofFn]; exact hN)).2]
    exact congrArg (MeasureTheory.integral S.B.μ) (funext fun ω => S.fam_dens N Y ω)
  rw [hval]
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (hThm N Y hN hOn ε hε).symm

/- English proof (translation)
The claim follows from `le_eFromConstituents_proof le_constants_proof le_reduceToBoxes_proof gridConvergence le_constSign_proof le_boxesFit_proof le_claimAll_proof (stepClaim hC hMV) le_claimInduction_proof le_boxLimitFromClaim_proof limitB limitA limit_L2 pairLimit coefficient_L2 leibniz cutBound`.
-/
theorem lemmaE (hC : E.CauchyTheta) (hMV : E.MarkovVector) : LemmaE :=
  le_eFromConstituents_proof le_constants_proof le_reduceToBoxes_proof gridConvergence le_constSign_proof le_boxesFit_proof
    le_claimAll_proof (stepClaim hC hMV) le_claimInduction_proof le_boxLimitFromClaim_proof limitB limitA limit_L2
    pairLimit coefficient_L2 leibniz cutBound

/- English proof (translation)
The claim follows from `lemmaE Formalism.FourierDecayAlt.P.cauchy_theta_identity Formalism.FourierDecayAlt.P.markov_inequality_vector`.
-/
theorem lemmaE_closed : LemmaE :=
  lemmaE Formalism.FourierDecayAlt.P.cauchy_theta_identity Formalism.FourierDecayAlt.P.markov_inequality_vector

/- English proof (translation)
The claim follows from `lemmaEprimeFull_fromSteps derived_energy_L2 epCoefInt lemmaEprime`.
-/
theorem lemmaEprimeFull_closed : LemmaEprimeFull :=
  lemmaEprimeFull_fromSteps derived_energy_L2 epCoefInt lemmaEprime

end Formalism.FourierDecayAlt.P.LEx2

/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.LEx2.coefficient_L2`.
-/
theorem Formalism.FourierDecayAlt.P.le_interpolation_coefficients_in_L2 : Formalism.FourierDecayAlt.LE.InterpolationCoefficientsInL2 :=
  Formalism.FourierDecayAlt.P.LEx2.coefficient_L2
/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.LEx2.limitA`.
-/
theorem Formalism.FourierDecayAlt.P.limit_A : Formalism.FourierDecayAlt.LE.LimitA :=
  Formalism.FourierDecayAlt.P.LEx2.limitA
/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.LEx2.limit_L2`.
-/
theorem Formalism.FourierDecayAlt.P.le_cutoff_limit_in_L2 : Formalism.FourierDecayAlt.LE.CutoffLimitInL2 :=
  Formalism.FourierDecayAlt.P.LEx2.limit_L2
/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.LEx2.pairLimit`.
-/
theorem Formalism.FourierDecayAlt.P.pair_limit : Formalism.FourierDecayAlt.LE.PairLimit :=
  Formalism.FourierDecayAlt.P.LEx2.pairLimit
/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.LEx2.limitB`.
-/
theorem Formalism.FourierDecayAlt.P.limit_B : Formalism.FourierDecayAlt.LE.LimitB :=
  Formalism.FourierDecayAlt.P.LEx2.limitB
/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.LEx2.gridConvergence`.
-/
theorem Formalism.FourierDecayAlt.P.grid_convergence : Formalism.FourierDecayAlt.LE.GridConvergence :=
  Formalism.FourierDecayAlt.P.LEx2.gridConvergence
/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.LEx2.le_constSign_proof`.
-/
theorem Formalism.FourierDecayAlt.P.constant_sign : Formalism.FourierDecayAlt.LE.ConstSign := Formalism.FourierDecayAlt.P.LEx2.le_constSign_proof
/- English proof (translation)
Introduce `n lam α β L Y s hαβ hroot hL hnL hs hY1 hY2 hYs1 hYs2`. Use `set D := (β - α) / 3 with hD`. Establish `hD0 : 0 < D` using `by rw [hD]; linarith`. Establish `hfac : ∀ t, D ≤ |Y + s + lam t|`. Introduce `t`.

Establish `ht` using `hroot t`. Distinguish the cases in `h : -lam t ≤ α`. Rewrite using `[abs_of_pos (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `push_neg at h`.

Establish `hb : β ≤ -lam t`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `ht ⟨h, hc⟩`. Rewrite using `[abs_of_neg (by linarith)]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hrat : ∀ t, |Y + lam t| ≤ (1 + L / D) * |Y + s + lam t|`. Introduce `t`. Establish `h1` using `abs_sub_abs_le_abs_sub (Y + lam t) (Y + s + lam t)`. Establish `h1' : (Y + lam t) - (Y + s + lam t) = -s` using `by ring`.

Rewrite `h1` using `[h1', abs_neg]`. Establish `h2 : L ≤ L / D * |Y + s + lam t|`. Rewrite using `[div_mul_eq_mul_div, le_div_iff₀ hD0]`. Conclude with `mul_le_mul_of_nonneg_left (hfac t) hL`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hprod : |∏ t, (Y + lam t)| ≤ (1 + L / D) ^ n * |∏ t, (Y + s + lam t)|`. Rewrite using `[Finset.abs_prod, Finset.abs_prod]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Establish `hx : 1 + L / D ≤ Real.exp (L / D)` using `by linarith [Real.add_one_le_exp (L / D)]`.

Establish `hexp : (1 + L / D) ^ n ≤ Real.exp 3`. Combine the equalities or inequalities in the displayed calculation. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Establish `he : (n:ℝ) * (L / D) = (n * L) / D` using `by ring`. Rewrite using `[he, div_le_iff₀ hD0]`.

Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation.
-/
theorem Formalism.FourierDecayAlt.P.ratio_middle_range : Formalism.FourierDecayAlt.LE.PRatioMiddle := by
  intro n lam α β L Y s hαβ hroot hL hnL hs hY1 hY2 hYs1 hYs2
  set D := (β - α) / 3 with hD
  have hD0 : 0 < D := by rw [hD]; linarith
  have hfac : ∀ t, D ≤ |Y + s + lam t| := by
    intro t
    have ht := hroot t
    by_cases h : -lam t ≤ α
    · rw [abs_of_pos (by linarith)]
      linarith
    · push_neg at h
      have hb : β ≤ -lam t := by
        by_contra hc
        push_neg at hc
        exact ht ⟨h, hc⟩
      rw [abs_of_neg (by linarith)]
      linarith
  have hrat : ∀ t, |Y + lam t| ≤ (1 + L / D) * |Y + s + lam t| := by
    intro t
    have h1 := abs_sub_abs_le_abs_sub (Y + lam t) (Y + s + lam t)
    have h1' : (Y + lam t) - (Y + s + lam t) = -s := by ring
    rw [h1', abs_neg] at h1
    have h2 : L ≤ L / D * |Y + s + lam t| := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hD0]
      exact mul_le_mul_of_nonneg_left (hfac t) hL
    nlinarith
  have hprod : |∏ t, (Y + lam t)| ≤ (1 + L / D) ^ n * |∏ t, (Y + s + lam t)| := by
    rw [Finset.abs_prod, Finset.abs_prod]
    calc ∏ t, |Y + lam t| ≤ ∏ t, ((1 + L / D) * |Y + s + lam t|) :=
          Finset.prod_le_prod (fun t _ => abs_nonneg _) (fun t _ => hrat t)
      _ = (1 + L / D) ^ n * ∏ t, |Y + s + lam t| := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hx : 1 + L / D ≤ Real.exp (L / D) := by linarith [Real.add_one_le_exp (L / D)]
  have hexp : (1 + L / D) ^ n ≤ Real.exp 3 := by
    calc (1 + L / D) ^ n ≤ (Real.exp (L / D)) ^ n := by gcongr <;> exact hx
      _ = Real.exp (n * (L / D)) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp 3 := by
          apply Real.exp_le_exp.mpr
          have he : (n:ℝ) * (L / D) = (n * L) / D := by ring
          rw [he, div_le_iff₀ hD0]
          linarith
  calc |∏ t, (Y + lam t)| ≤ (1 + L / D) ^ n * |∏ t, (Y + s + lam t)| := hprod
    _ ≤ Real.exp 3 * |∏ t, (Y + s + lam t)| := mul_le_mul_of_nonneg_right hexp (abs_nonneg _)
/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.LEx2.le_constants_proof`.
-/
theorem Formalism.FourierDecayAlt.P.constants_choice : Formalism.FourierDecayAlt.LE.Constants := Formalism.FourierDecayAlt.P.LEx2.le_constants_proof
/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.LEx2.le_boxesFit_proof`.
-/
theorem Formalism.FourierDecayAlt.P.boxes_fit : Formalism.FourierDecayAlt.LE.BoxesFit := Formalism.FourierDecayAlt.P.LEx2.le_boxesFit_proof
/- English proof (translation)
Introduce `hPR hFit S hL hfit hnL hRO w hlen`. Establish `hL0 : 0 < S.L` using `by linarith`. Establish `hN1 : (1:ℝ) ≤ S.Ntot`. Establish `: 1 ≤ S.Ntot` using `by omega`. Conclude with `this` after adjusting the coercions.

Establish `hαβ : S.α < S.β` using `by nlinarith`. Establish `hmid` using `(hFit S hL hfit).1 w.length hlen`. Establish `hJ : ∀ Y ∈ (S.step w).J, Y ∈ Set.Icc (S.α + (S.β - S.α) / 3) (S.β - (S.β - S.α) / 3)`. Introduce `Y hY`. Apply `hmid` to reduce the goal to its premises.

Establish `hY' : Y ∈ Set.Icc (S.step w).a ((S.step w).a + (S.step w).L)` using `hY`. Rewrite `hY'` using `[S.step_a, S.step_L]`. Conclude with `hY'`. Establish `hPfun : (S.step w).P = fun Y => ∏ s, (Y + S.lam s)` using `funext (S.step_P w)`. Use `⟨⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[hPfun]`. Conclude with `(continuous_finset_prod Finset.univ (fun s _ => continuous_id.add continuous_const)).continuousOn`. Introduce `Y hY`. Rewrite using `[S.step_P]`. Use `Finset.prod_ne_zero_iff.mpr (fun s _ => ?_)` and prove the remaining obligations.

Introduce `h0`. Establish `hYm` using `hJ Y hY`. Apply `hRO s` to reduce the goal to its premises. Apply the tactic sequence `refine ⟨?_, ?_⟩ <;> nlinarith [hYm.1, hYm.2]`. Introduce `Y s hY hYs`.

Establish `hYm` using `hJ Y hY`. Establish `hYsm` using `hJ (Y + s) hYs`. Establish `hY' : Y ∈ Set.Icc (S.step w).a ((S.step w).a + (S.step w).L)` using `hY`. Establish `hYs' : Y + s ∈ Set.Icc (S.step w).a ((S.step w).a + (S.step w).L)` using `hYs`. Rewrite `hY'`, `hYs'` using `[S.step_L]`.

Establish `key` using `hPR (S.k + 2 * S.r + 1) S.lam S.α S.β S.L (Y + s) (-s) hαβ (fun t ht => hRO t ⟨ht.1.le, ht.2.le⟩) hL0.le hnL (by rw [abs_neg]; exact abs_le.mpr ⟨by linarith [hY'.1, hY'.2, hYs'.1, hYs'.2], by linarith [hY'.1, hY'.2, hYs'.1, hYs'.2]⟩) hYsm.1 hYsm.2 (by linarith [hYm.1]) (by linari …`. Simplify using `only [add_neg_cancel_right] at key`. Rewrite using `[S.step_P, S.step_P]`. Conclude with `key`.
-/
theorem Formalism.FourierDecayAlt.P.imported_results_hold : Formalism.FourierDecayAlt.LE.PImportsHold := by
  intro hPR hFit S hL hfit hnL hRO w hlen
  have hL0 : 0 < S.L := by linarith
  have hN1 : (1:ℝ) ≤ S.Ntot := by
    have : 1 ≤ S.Ntot := by omega
    exact_mod_cast this
  have hαβ : S.α < S.β := by nlinarith
  have hmid := (hFit S hL hfit).1 w.length hlen
  have hJ : ∀ Y ∈ (S.step w).J,
      Y ∈ Set.Icc (S.α + (S.β - S.α) / 3) (S.β - (S.β - S.α) / 3) := by
    intro Y hY
    apply hmid
    have hY' : Y ∈ Set.Icc (S.step w).a ((S.step w).a + (S.step w).L) := hY
    rw [S.step_a, S.step_L] at hY'
    exact hY'
  have hPfun : (S.step w).P = fun Y => ∏ s, (Y + S.lam s) := funext (S.step_P w)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [hPfun]
    exact (continuous_finset_prod Finset.univ
      (fun s _ => continuous_id.add continuous_const)).continuousOn
  · intro Y hY
    rw [S.step_P]
    refine Finset.prod_ne_zero_iff.mpr (fun s _ => ?_)
    intro h0
    have hYm := hJ Y hY
    apply hRO s
    refine ⟨?_, ?_⟩ <;> nlinarith [hYm.1, hYm.2]
  · intro Y s hY hYs
    have hYm := hJ Y hY
    have hYsm := hJ (Y + s) hYs
    have hY' : Y ∈ Set.Icc (S.step w).a ((S.step w).a + (S.step w).L) := hY
    have hYs' : Y + s ∈ Set.Icc (S.step w).a ((S.step w).a + (S.step w).L) := hYs
    rw [S.step_L] at hY' hYs'
    have key := hPR (S.k + 2 * S.r + 1) S.lam S.α S.β S.L (Y + s) (-s) hαβ
      (fun t ht => hRO t ⟨ht.1.le, ht.2.le⟩) hL0.le hnL
      (by rw [abs_neg]; exact abs_le.mpr ⟨by linarith [hY'.1, hY'.2, hYs'.1, hYs'.2], by linarith [hY'.1, hY'.2, hYs'.1, hYs'.2]⟩)
      hYsm.1 hYsm.2 (by linarith [hYm.1]) (by linarith [hYm.2])
    simp only [add_neg_cancel_right] at key
    rw [S.step_P, S.step_P]
    exact key
/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.LEx2.le_reduceToBoxes_proof`.
-/
theorem Formalism.FourierDecayAlt.P.reduce_to_boxes : Formalism.FourierDecayAlt.LE.ReduceToBoxes := Formalism.FourierDecayAlt.P.LEx2.le_reduceToBoxes_proof
/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.LEx2.le_claimInduction_proof`.
-/
theorem Formalism.FourierDecayAlt.P.level_induction : Formalism.FourierDecayAlt.LE.ClaimInduction := Formalism.FourierDecayAlt.P.LEx2.le_claimInduction_proof
/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.LEx2.le_claimAll_proof`.
-/
theorem Formalism.FourierDecayAlt.P.induction_all_levels : Formalism.FourierDecayAlt.LE.ClaimAll := Formalism.FourierDecayAlt.P.LEx2.le_claimAll_proof
/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.LEx2.le_boxLimitFromClaim_proof`.
-/
theorem Formalism.FourierDecayAlt.P.box_limit_of_induction : Formalism.FourierDecayAlt.LE.BoxLimitFromClaim := Formalism.FourierDecayAlt.P.LEx2.le_boxLimitFromClaim_proof
/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.LEx2.lemmaE_closed`.
-/
theorem Formalism.FourierDecayAlt.P.le_E_proof : Formalism.FourierDecayAlt.LE.LemmaE := Formalism.FourierDecayAlt.P.LEx2.lemmaE_closed
/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.LEx2.le_eFromConstituents_proof`.
-/
theorem Formalism.FourierDecayAlt.P.lemma_E_of_parts : Formalism.FourierDecayAlt.LE.LemmaEFromSteps := Formalism.FourierDecayAlt.P.LEx2.le_eFromConstituents_proof
/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.LEx2.derived_energy_L2`.
-/
theorem Formalism.FourierDecayAlt.P.le_weightedIntegrable_proof : Formalism.FourierDecayAlt.LE.WeightedIntegrable :=
  Formalism.FourierDecayAlt.P.LEx2.derived_energy_L2
/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.LEx2.epCoefInt`.
-/
theorem Formalism.FourierDecayAlt.P.derived_coefficient_integrable : Formalism.FourierDecayAlt.LE.EpCoefInt :=
  Formalism.FourierDecayAlt.P.LEx2.epCoefInt
/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.LEx2.epStep5`.
-/
theorem Formalism.FourierDecayAlt.P.derived_energy_fifth_estimate : Formalism.FourierDecayAlt.LE.EpStep5 :=
  Formalism.FourierDecayAlt.P.LEx2.epStep5
/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.LEx2.epStep6`.
-/
theorem Formalism.FourierDecayAlt.P.derived_energy_sixth_estimate : Formalism.FourierDecayAlt.LE.EpStep6 :=
  Formalism.FourierDecayAlt.P.LEx2.epStep6
/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.LEx2.lemmaEprime`.
-/
theorem Formalism.FourierDecayAlt.P.lemma_E_derived : Formalism.FourierDecayAlt.LE.LemmaEprime :=
  Formalism.FourierDecayAlt.P.LEx2.lemmaEprime
/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.LEx2.lemmaEprimeFull_closed`.
-/
theorem Formalism.FourierDecayAlt.P.lemma_E_derived_full : Formalism.FourierDecayAlt.LE.LemmaEprimeFull :=
  Formalism.FourierDecayAlt.P.LEx2.lemmaEprimeFull_closed
/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.LEx2.lemmaEprimeFromSteps`.
-/
theorem Formalism.FourierDecayAlt.P.lemma_E_derived_of_parts : Formalism.FourierDecayAlt.LE.LemmaEprimeFromSteps :=
  Formalism.FourierDecayAlt.P.LEx2.lemmaEprimeFromSteps
/- English proof (translation)
Introduce `E W _ D S loc hN hRO hAdm hwt hgram hJ0 hEL`. Introduce `w hw`. Take `⟨hwW, hcnt⟩` from `Finset.mem_filter.mp hw`. Establish `hlim : ∀ v, Filter.Tendsto (fun ε : ℝ => (S v).principalHermitianLattice ε (loc w v)) (nhdsWithin 0 (Set.Ioi 0)) (nhds ((S v).size (loc w v) * (S v).jn))`. Introduce `v`.

Take `⟨hadm, hlen⟩` from `hAdm w hwW v`. Conclude with `hEL v (loc w v) hadm (by rw [hN v]; omega)`. Establish `hprod` using `tendsto_finset_prod Finset.univ (fun v _ => hlim v)`. Establish `hsize : ∀ v, (S v).size (loc w v) ≠ 0`. Introduce `v`.

Take `⟨⟨hin, -⟩, -⟩` from `hAdm w hwW v`. Introduce `h0`. Rewrite `h0` using `[Formalism.FourierDecayAlt.LE.Sys.size, List.prod_eq_zero_iff]`. Take `⟨x, hx, hx0⟩` from `List.mem_map.mp h0`. Establish `hP : (S v).P x.2 = 0` using `abs_eq_zero.mp hx0`.

Take `⟨s, -, hs⟩` from `Finset.prod_eq_zero_iff.mp hP`. Establish `hxin` using `hin x hx`. Conclude with `hRO v s (by rw [show -(S v).lam s = x.2 by linarith]; exact hxin)`. Establish `hjn : ∀ v, (S v).jn = (S v).jsq` using `fun v => congrArg (MeasureTheory.integral (S v).B.μ) (funext (hJ0 v))`. Establish `hlim2` using `hprod.div_const (D.wt w)`.

Establish `hval : (∏ v, (S v).size (loc w v) * (S v).jn) / D.wt w = ∏ v, (S v).jsq`. Rewrite using `[hwt w hwW, Finset.prod_mul_distrib, mul_div_right_comm, div_self (Finset.prod_ne_zero_iff.mpr (fun v _ => hsize v)), one_mul]`. Conclude with `Finset.prod_congr rfl (fun v _ => hjn v)`. Rewrite using `[← hval]`. Use `hlim2.congr' ?_` and prove the remaining obligations.

Use `filter_upwards [self_mem_nhdsWithin] with ε hε`. Use `show (∏ v, (S v).principalHermitianLattice ε (loc w v)) / D.wt w = (D.gram ε 0 w [] []).re / D.wt w`. Rewrite using `[hgram ε hε w hwW]`.
-/
theorem Formalism.FourierDecayAlt.P.energy_estimate_joint : Formalism.FourierDecayAlt.LE.EstEJoint := by
  intro E W _ D S loc hN hRO hAdm hwt hgram hJ0 hEL
  intro w hw
  obtain ⟨hwW, hcnt⟩ := Finset.mem_filter.mp hw
  have hlim : ∀ v, Filter.Tendsto (fun ε : ℝ => (S v).principalHermitianLattice ε (loc w v)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((S v).size (loc w v) * (S v).jn)) := by
    intro v
    obtain ⟨hadm, hlen⟩ := hAdm w hwW v
    exact hEL v (loc w v) hadm (by rw [hN v]; omega)
  have hprod := tendsto_finset_prod Finset.univ (fun v _ => hlim v)
  have hsize : ∀ v, (S v).size (loc w v) ≠ 0 := by
    intro v
    obtain ⟨⟨hin, -⟩, -⟩ := hAdm w hwW v
    intro h0
    rw [Formalism.FourierDecayAlt.LE.Sys.size, List.prod_eq_zero_iff] at h0
    obtain ⟨x, hx, hx0⟩ := List.mem_map.mp h0
    have hP : (S v).P x.2 = 0 := abs_eq_zero.mp hx0
    obtain ⟨s, -, hs⟩ := Finset.prod_eq_zero_iff.mp hP
    have hxin := hin x hx
    exact hRO v s (by rw [show -(S v).lam s = x.2 by linarith]; exact hxin)
  have hjn : ∀ v, (S v).jn = (S v).jsq := fun v =>
    congrArg (MeasureTheory.integral (S v).B.μ) (funext (hJ0 v))
  have hlim2 := hprod.div_const (D.wt w)
  have hval : (∏ v, (S v).size (loc w v) * (S v).jn) / D.wt w = ∏ v, (S v).jsq := by
    rw [hwt w hwW, Finset.prod_mul_distrib, mul_div_right_comm,
      div_self (Finset.prod_ne_zero_iff.mpr (fun v _ => hsize v)), one_mul]
    exact Finset.prod_congr rfl (fun v _ => hjn v)
  rw [← hval]
  refine hlim2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  show (∏ v, (S v).principalHermitianLattice ε (loc w v)) / D.wt w = (D.gram ε 0 w [] []).re / D.wt w
  rw [hgram ε hε w hwW]
