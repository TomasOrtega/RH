import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralFourierCoeffClassIndicatorLevelPoint
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmHostRootNegDiscriminantNeNegSelf
import Formalism.LocalRingCardinality.HostCls
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open GlobalTheory.CovInt IsDedekindDomain

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CovIntNum

section Size

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

/- English proof (translation)
Rewrite using `[Fin.sum_univ_add]`. Establish `h1 : ∀ i : Fin Dw.p, |((laOf Dw a n τ (Fin.castAdd Dw.q i) : ℤ) : ℝ)| = (a (τ.1, i) : ℝ) + ((n / 2 : ℕ) : ℝ)`. Introduce `i`. Establish `hi : ((Fin.castAdd Dw.q i : Fin (Dw.p + Dw.q)) : ℕ) < Dw.p` using `by simp`. Unfold `laOf GlobalTheory.AllWt.weightOf`.

Rewrite using `[if_pos hi, Fin.val_castAdd]`. Simplify using `only [Int.cast_add, Int.cast_natCast]`. Conclude with `abs_of_nonneg (by positivity)`. Establish `h2 : ∀ i : Fin Dw.q, |((laOf Dw a n τ (Fin.natAdd Dw.p i) : ℤ) : ℝ)| = (a (conjEmb τ.1, (Fin.rev i : ℕ)) : ℝ) + ((n / 2 : ℕ) : ℝ)`. Introduce `i`.

Establish `hi : ¬ ((Fin.natAdd Dw.p i : Fin (Dw.p + Dw.q)) : ℕ) < Dw.p` using `by simp`. Establish `hidx : Dw.q - 1 - (((Fin.natAdd Dw.p i : Fin (Dw.p + Dw.q)) : ℕ) - Dw.p) = (Fin.rev i : ℕ)`. Simplify using `only [Fin.val_natAdd, Fin.val_rev]`. Use linear arithmetic over natural numbers and integers. Unfold `laOf GlobalTheory.AllWt.weightOf`.

Rewrite using `[if_neg hi, hidx]`. Simplify using `only [Int.cast_sub, Int.cast_neg, Int.cast_natCast]`. Establish `h3 : (0 : ℝ) ≤ (a (conjEmb τ.1, (Fin.rev i : ℕ)) : ℝ)` using `Nat.cast_nonneg _`. Establish `h4 : (0 : ℝ) ≤ ((n / 2 : ℕ) : ℝ)` using `Nat.cast_nonneg _`. Rewrite using `[abs_of_nonpos (by linarith)]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [h1, h2, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Establish `hr : (∑ i : Fin Dw.q, (a (conjEmb τ.1, (Fin.rev i : ℕ)) : ℝ)) = ∑ i : Fin Dw.q, (a (conjEmb τ.1, i) : ℝ)` using `Fintype.sum_equiv Fin.revPerm _ _ (fun _ => rfl)`. Rewrite using `[hr]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_abs_laOf (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (τ : Psi H) :
    ∑ k, |((laOf Dw a n τ k : ℤ) : ℝ)| =
      ((∑ i : Fin Dw.p, (a (τ.1, i) : ℝ)) + ∑ i : Fin Dw.q, (a (conjEmb τ.1, i) : ℝ)) +
        ((Dw.p + Dw.q : ℕ) : ℝ) * ((n / 2 : ℕ) : ℝ) := by
  rw [Fin.sum_univ_add]
  have h1 : ∀ i : Fin Dw.p, |((laOf Dw a n τ (Fin.castAdd Dw.q i) : ℤ) : ℝ)| = (a (τ.1, i) : ℝ) + ((n / 2 : ℕ) : ℝ) := by
    intro i
    have hi : ((Fin.castAdd Dw.q i : Fin (Dw.p + Dw.q)) : ℕ) < Dw.p := by simp
    unfold laOf GlobalTheory.AllWt.weightOf
    rw [if_pos hi, Fin.val_castAdd]
    simp only [Int.cast_add, Int.cast_natCast]
    exact abs_of_nonneg (by positivity)
  have h2 : ∀ i : Fin Dw.q, |((laOf Dw a n τ (Fin.natAdd Dw.p i) : ℤ) : ℝ)| =
      (a (conjEmb τ.1, (Fin.rev i : ℕ)) : ℝ) + ((n / 2 : ℕ) : ℝ) := by
    intro i
    have hi : ¬ ((Fin.natAdd Dw.p i : Fin (Dw.p + Dw.q)) : ℕ) < Dw.p := by simp
    have hidx : Dw.q - 1 - (((Fin.natAdd Dw.p i : Fin (Dw.p + Dw.q)) : ℕ) - Dw.p) = (Fin.rev i : ℕ) := by
      simp only [Fin.val_natAdd, Fin.val_rev]; omega
    unfold laOf GlobalTheory.AllWt.weightOf
    rw [if_neg hi, hidx]
    simp only [Int.cast_sub, Int.cast_neg, Int.cast_natCast]
    have h3 : (0 : ℝ) ≤ (a (conjEmb τ.1, (Fin.rev i : ℕ)) : ℝ) := Nat.cast_nonneg _
    have h4 : (0 : ℝ) ≤ ((n / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [abs_of_nonpos (by linarith)]
    ring
  simp only [h1, h2, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hr : (∑ i : Fin Dw.q, (a (conjEmb τ.1, (Fin.rev i : ℕ)) : ℝ)) = ∑ i : Fin Dw.q, (a (conjEmb τ.1, i) : ℝ) :=
    Fintype.sum_equiv Fin.revPerm _ _ (fun _ => rfl)
  rw [hr]
  push_cast
  ring

/- English proof (translation)
Set `P : (E →+* ℂ) → Prop` to `fun τ => τ (H.rt : E) = H.rt0`. Establish `h` using `Fintype.sum_subtype_add_sum_subtype P (fun τ => ∑ i : Fin (Dw.mult τ), (a (τ, i) : ℝ))`. Use `beta_reduce at h`. Establish `e1 : (∑ τ : {τ // P τ}, ∑ i : Fin (Dw.mult τ.1), (a (τ.1, i) : ℝ)) = ∑ τ : {τ // P τ}, ∑ i : Fin Dw.p, (a (τ.1, i) : ℝ)`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations.

Rewrite using `[Fin.sum_univ_eq_sum_range (fun i => (a (τ.1, i) : ℝ)), Fin.sum_univ_eq_sum_range (fun i => (a (τ.1, i) : ℝ)), Datum.mult, if_pos τ.2]`. Set `e : {τ : E →+* ℂ // ¬ P τ} ≃ {τ // P τ}` to `{ toFun := fun τ => ⟨conjEmb τ.1, GlobalTheory.AllWt.conj_mem τ.2⟩ invFun := fun σ => ⟨conjEmb σ.1, GlobalTheory.AllWt.conj_not_mem (H := H) σ⟩ left_inv := fun τ => Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb _) right_inv := fun σ => Subtype.ext (GlobalTheory.AllWt.conjEmb_co …`. Establish `e2 : (∑ τ : {τ // ¬ P τ}, ∑ i : Fin (Dw.mult τ.1), (a (τ.1, i) : ℝ)) = ∑ σ : {τ // P τ}, ∑ i : Fin Dw.q, (a (conjEmb σ.1, i) : ℝ)`. Use `Fintype.sum_equiv e _ _ fun τ => ?_` and prove the remaining obligations. Use `show _ = ∑ i : Fin Dw.q, (a (conjEmb (conjEmb τ.1), i) : ℝ)`.

Rewrite using `[GlobalTheory.AllWt.conjEmb_conjEmb, Fin.sum_univ_eq_sum_range (fun i => (a (τ.1, i) : ℝ)), Fin.sum_univ_eq_sum_range (fun i => (a (τ.1, i) : ℝ)), Datum.mult, if_neg τ.2]`. Unfold `DF`. Use `push_cast`. Combine the equalities or inequalities in the displayed calculation. Apply the tactic sequence `convert congrArg₂ (· + ·) e1 e2 using 2 <;> first | rfl | exact Finset.sum_congr (congrArg _ (Subsingleton.elim _ _)) fun _ _ => rfl | congr 1`.

Use `_ = _ := by`. Rewrite using `[← Finset.sum_add_distrib]`.
-/
theorem DF_eq_sum (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) :
    (DF Dw a : ℝ) = ∑ τ : Psi H, ((∑ i : Fin Dw.p, (a (τ.1, i) : ℝ)) + ∑ i : Fin Dw.q, (a (conjEmb τ.1, i) : ℝ)) := by
  classical
  let P : (E →+* ℂ) → Prop := fun τ => τ (H.rt : E) = H.rt0
  have h := Fintype.sum_subtype_add_sum_subtype P (fun τ => ∑ i : Fin (Dw.mult τ), (a (τ, i) : ℝ))
  beta_reduce at h
  have e1 : (∑ τ : {τ // P τ}, ∑ i : Fin (Dw.mult τ.1), (a (τ.1, i) : ℝ)) =
      ∑ τ : {τ // P τ}, ∑ i : Fin Dw.p, (a (τ.1, i) : ℝ) := by
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Fin.sum_univ_eq_sum_range (fun i => (a (τ.1, i) : ℝ)), Fin.sum_univ_eq_sum_range (fun i => (a (τ.1, i) : ℝ)),
      Datum.mult, if_pos τ.2]
  let e : {τ : E →+* ℂ // ¬ P τ} ≃ {τ // P τ} :=
    { toFun := fun τ => ⟨conjEmb τ.1, GlobalTheory.AllWt.conj_mem τ.2⟩
      invFun := fun σ => ⟨conjEmb σ.1, GlobalTheory.AllWt.conj_not_mem (H := H) σ⟩
      left_inv := fun τ => Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb _)
      right_inv := fun σ => Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb _) }
  have e2 : (∑ τ : {τ // ¬ P τ}, ∑ i : Fin (Dw.mult τ.1), (a (τ.1, i) : ℝ)) =
      ∑ σ : {τ // P τ}, ∑ i : Fin Dw.q, (a (conjEmb σ.1, i) : ℝ) := by
    refine Fintype.sum_equiv e _ _ fun τ => ?_
    show _ = ∑ i : Fin Dw.q, (a (conjEmb (conjEmb τ.1), i) : ℝ)
    rw [GlobalTheory.AllWt.conjEmb_conjEmb, Fin.sum_univ_eq_sum_range (fun i => (a (τ.1, i) : ℝ)),
      Fin.sum_univ_eq_sum_range (fun i => (a (τ.1, i) : ℝ)), Datum.mult, if_neg τ.2]
  unfold DF
  push_cast
  calc (∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), (a (τ, i) : ℝ)) = _ := h.symm
    _ = (∑ τ : {τ // P τ}, ∑ i : Fin Dw.p, (a (τ.1, i) : ℝ)) +
          ∑ σ : {τ // P τ}, ∑ i : Fin Dw.q, (a (conjEmb σ.1, i) : ℝ) := by
        convert congrArg₂ (· + ·) e1 e2 using 2 <;> first | rfl | exact Finset.sum_congr (congrArg _ (Subsingleton.elim _ _)) fun _ _ => rfl | congr 1
    _ = _ := by
        rw [← Finset.sum_add_distrib]

/- English proof (translation)
Unfold `sizeK`. Simplify using `only [sum_abs_laOf, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Rewrite using `[DF_eq_sum, Finset.sum_add_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sizeK_eq (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    sizeK Dw a n = (DF Dw a : ℝ) + (Fintype.card (Psi H) : ℝ) * ((Dw.p + Dw.q : ℕ) : ℝ) * ((n / 2 : ℕ) : ℝ) := by
  unfold sizeK
  simp only [sum_abs_laOf, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [DF_eq_sum, Finset.sum_add_distrib]
  ring

end Size

end GlobalTheory.CovIntNum

namespace GlobalTheory.CovIntNum

/- English proof (translation)
Use `⟨67, by norm_num, ?_⟩` and prove the remaining obligations. Introduce `D T j Y e o Lb a n h`. Take `⟨-, -, -, -, -, -, hLb, hM, hsz, -, -, -, hn, -, -, -⟩` from `h`. Take `⟨hqp, hdp, hq8, hd16, -⟩` from `D.host.hyp`. Establish `hM3 : 3 ≤ Y.d.l₂.M` using `Y.d.l₂.three_le`.

Establish `hZ : (intZ D (T.Q.Dw j) Y.d.l₂ n a : ℝ) = (Y.d.l₂.M : ℝ) ^ (Module.finrank ℚ D.host.E / 2 * ((T.Q.Dw j).p + (T.Q.Dw j).q) * n + DF (T.Q.Dw j) a) * ((NumberField.discr D.host.E).natAbs : ℝ) ^ DF (T.Q.Dw j) a`. Rewrite using `[intZ_eq]`. Move the coercions through the operations in `[-Nat.cast_natAbs]`. Expand and normalize the polynomial expressions, which then agree. Establish `hD1 : (1 : ℝ) ≤ ((NumberField.discr D.host.E).natAbs : ℝ)`.

Conclude with `Nat.pos_of_ne_zero (Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero D.host.E))` after adjusting the coercions. Establish `hlD : Real.log ((NumberField.discr D.host.E).natAbs : ℝ) ≤ D.R.f * (7 * Lb)`. Establish `h1` using `log_discr_natAbs_le D.host.E`. Establish `h2 : (Module.finrank ℚ D.host.E : ℝ) = 2 * D.R.f` using `by exact_mod_cast D.host.finrank_E'`. Establish `h3 : (0 : ℝ) ≤ D.R.f` using `Nat.cast_nonneg _`.

Rewrite `h1` using `[h2]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hMpos : (0 : ℝ) < Y.d.l₂.M` using `by exact_mod_cast (by omega : 0 < Y.d.l₂.M)`. Establish `hq0 : (0 : ℝ) < D.host.q` using `by exact_mod_cast hqp.pos`. Establish `hd0 : (0 : ℝ) < D.host.d` using `by exact_mod_cast hdp.pos`.

Establish `hZpos : (0 : ℝ) < (intZ D (T.Q.Dw j) Y.d.l₂ n a : ℝ)` using `by rw [hZ]; positivity`. Use `⟨by exact_mod_cast hZpos, ?_⟩` and prove the remaining obligations. Establish `hlogZ : Real.log (intZ D (T.Q.Dw j) Y.d.l₂ n a : ℝ) = ((Module.finrank ℚ D.host.E / 2 * ((T.Q.Dw j).p + (T.Q.Dw j).q) * n + DF (T.Q.Dw j) a : ℕ) : ℝ) * Real.log Y.d.l₂.M + (DF (T.Q.Dw j) a : ℝ) * Real.log ((NumberField.discr D.host.E).natAbs : ℝ)`. Rewrite using `[hZ, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]`. Rewrite using `[hlogZ]`.

Establish `hSe` using `sizeK_eq (T.Q.Dw j) a n`. Establish `hcard : Fintype.card (Psi T.Q.H) = Module.finrank ℚ D.host.E / 2`. Rewrite using `[← Nat.card_eq_fintype_card]`. Conclude with `GlobalTheory.LamF.card_psiSet T.Q.H`. Rewrite `hSe` using `[hcard]`.

Establish `hlD0` using `Real.log_nonneg hD1`. Generalize the expression as in `Real.log ((NumberField.discr D.host.E).natAbs : ℝ) = lD at hlD hlD0 ⊢`. Take `⟨t, rfl⟩` from `hn`. Establish `ht : (t + t) / 2 = t` using `by omega`. Rewrite `hSe` using `[ht]`.

Generalize the expression as in `Module.finrank ℚ D.host.E / 2 = m at hSe ⊢`. Generalize the expression as in `sizeK (T.Q.Dw j) a (t + t) = S at hSe ⊢`. Generalize the expression as in `DF (T.Q.Dw j) a = dF at hSe ⊢`. Move the coercions through the operations in `at hSe ⊢`. Establish `hf : 1 ≤ D.R.f` using `by have : 0 < D.R.n := D.R.ord_pos; unfold Formalism.BasicNotions.Ranks.f; omega`.

Establish `hr : 1 ≤ D.R.r`. Use `D.R.two_le_m` as an intermediate fact. Use `D.R.m_add_three_le_k` as an intermediate fact. Unfold `Formalism.BasicNotions.Ranks.r`. Use linear arithmetic over natural numbers and integers.

Establish `hf1 : (1 : ℝ) ≤ D.R.f` using `by exact_mod_cast (by omega : 1 ≤ D.R.f)`. Establish `hr1 : (1 : ℝ) ≤ D.R.r` using `by exact_mod_cast hr`. Establish `hlM0 : 0 ≤ Real.log Y.d.l₂.M` using `Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Y.d.l₂.M))`. Establish `hdF0 : (0 : ℝ) ≤ dF` using `Nat.cast_nonneg _`. Establish `hB0 : (0 : ℝ) ≤ (m : ℝ) * (((T.Q.Dw j).p : ℝ) + (T.Q.Dw j).q) * t` using `by positivity`.

Establish `hS0 : 0 ≤ S` using `by rw [hSe]; positivity`. Establish `hX : (m : ℝ) * (((T.Q.Dw j).p : ℝ) + (T.Q.Dw j).q) * ((t : ℝ) + t) + dF ≤ 2 * S` using `by rw [hSe]; linarith`. Establish `hdFS : (dF : ℝ) ≤ S` using `by rw [hSe]; linarith`. Establish `h1 : ((m : ℝ) * (((T.Q.Dw j).p : ℝ) + (T.Q.Dw j).q) * ((t : ℝ) + t) + dF) * Real.log Y.d.l₂.M ≤ (2 * S) * (30 * Lb)` using `mul_le_mul hX hM hlM0 (by linarith)`. Establish `h2 : (dF : ℝ) * lD ≤ (D.R.f * S) * (7 * Lb)` using `(mul_le_mul hdFS hlD hlD0 hS0).trans (le_of_eq (by ring))`.

Establish `hLS : 0 ≤ Lb * S` using `mul_nonneg (by linarith) hS0`. Establish `hA : Lb * S ≤ D.R.f * (Lb * S)` using `le_mul_of_one_le_left hLS hf1`. Establish `h3 : (2 * S) * (30 * Lb) + (D.R.f * S) * (7 * Lb) ≤ 67 * ((D.R.f : ℝ) * Lb) * S` using `by linarith`. Establish `hx1 : (1 : ℝ) ≤ D.R.f * D.R.r * Lb` using `one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hf1 hr1) hLb`. Establish `h5 : (D.R.f : ℝ) * Lb ≤ D.R.f * D.R.r * Lb` using `mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by linarith) hr1) (by linarith)`.

Establish `h4 : (D.R.f : ℝ) * Lb ≤ ((D.R.f : ℝ) * D.R.r * Lb) ^ 2` using `h5.trans (le_self_pow₀ hx1 (by norm_num))`. Establish `h6 : 67 * ((D.R.f : ℝ) * Lb) * S ≤ 67 * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 * S` using `mul_le_mul_of_nonneg_right (by linarith) hS0`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem intZ_log_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o Lb : ℝ)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), GlobalTheory.CovGmin.Hyp D T j Y e o Lb a n →
    0 < intZ D (T.Q.Dw j) Y.d.l₂ n a ∧
    Real.log (intZ D (T.Q.Dw j) Y.d.l₂ n a) ≤ C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 * sizeK (T.Q.Dw j) a n := by
  refine ⟨67, by norm_num, ?_⟩
  intro D T j Y e o Lb a n h
  obtain ⟨-, -, -, -, -, -, hLb, hM, hsz, -, -, -, hn, -, -, -⟩ := h
  obtain ⟨hqp, hdp, hq8, hd16, -⟩ := D.host.hyp
  have hM3 : 3 ≤ Y.d.l₂.M := Y.d.l₂.three_le
  have hZ : (intZ D (T.Q.Dw j) Y.d.l₂ n a : ℝ) =
      (Y.d.l₂.M : ℝ) ^ (Module.finrank ℚ D.host.E / 2 * ((T.Q.Dw j).p + (T.Q.Dw j).q) * n + DF (T.Q.Dw j) a) *
        ((NumberField.discr D.host.E).natAbs : ℝ) ^ DF (T.Q.Dw j) a := by
    rw [intZ_eq]
    push_cast [-Nat.cast_natAbs]
    ring
  have hD1 : (1 : ℝ) ≤ ((NumberField.discr D.host.E).natAbs : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero D.host.E))
  have hlD : Real.log ((NumberField.discr D.host.E).natAbs : ℝ) ≤ D.R.f * (7 * Lb) := by
    have h1 := log_discr_natAbs_le D.host.E
    have h2 : (Module.finrank ℚ D.host.E : ℝ) = 2 * D.R.f := by exact_mod_cast D.host.finrank_E'
    have h3 : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
    rw [h2] at h1
    nlinarith
  have hMpos : (0 : ℝ) < Y.d.l₂.M := by exact_mod_cast (by omega : 0 < Y.d.l₂.M)
  have hq0 : (0 : ℝ) < D.host.q := by exact_mod_cast hqp.pos
  have hd0 : (0 : ℝ) < D.host.d := by exact_mod_cast hdp.pos
  have hZpos : (0 : ℝ) < (intZ D (T.Q.Dw j) Y.d.l₂ n a : ℝ) := by rw [hZ]; positivity
  refine ⟨by exact_mod_cast hZpos, ?_⟩
  have hlogZ : Real.log (intZ D (T.Q.Dw j) Y.d.l₂ n a : ℝ) =
      ((Module.finrank ℚ D.host.E / 2 * ((T.Q.Dw j).p + (T.Q.Dw j).q) * n + DF (T.Q.Dw j) a : ℕ) : ℝ) *
          Real.log Y.d.l₂.M +
        (DF (T.Q.Dw j) a : ℝ) * Real.log ((NumberField.discr D.host.E).natAbs : ℝ) := by
    rw [hZ, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  rw [hlogZ]

  have hSe := sizeK_eq (T.Q.Dw j) a n
  have hcard : Fintype.card (Psi T.Q.H) = Module.finrank ℚ D.host.E / 2 := by
    rw [← Nat.card_eq_fintype_card]; exact GlobalTheory.LamF.card_psiSet T.Q.H
  rw [hcard] at hSe
  have hlD0 := Real.log_nonneg hD1
  generalize Real.log ((NumberField.discr D.host.E).natAbs : ℝ) = lD at hlD hlD0 ⊢
  obtain ⟨t, rfl⟩ := hn
  have ht : (t + t) / 2 = t := by omega
  rw [ht] at hSe
  generalize Module.finrank ℚ D.host.E / 2 = m at hSe ⊢
  generalize sizeK (T.Q.Dw j) a (t + t) = S at hSe ⊢
  generalize DF (T.Q.Dw j) a = dF at hSe ⊢
  push_cast at hSe ⊢

  have hf : 1 ≤ D.R.f := by have : 0 < D.R.n := D.R.ord_pos; unfold Formalism.BasicNotions.Ranks.f; omega
  have hr : 1 ≤ D.R.r := by
    have := D.R.two_le_m; have := D.R.m_add_three_le_k; unfold Formalism.BasicNotions.Ranks.r; omega
  have hf1 : (1 : ℝ) ≤ D.R.f := by exact_mod_cast (by omega : 1 ≤ D.R.f)
  have hr1 : (1 : ℝ) ≤ D.R.r := by exact_mod_cast hr
  have hlM0 : 0 ≤ Real.log Y.d.l₂.M := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Y.d.l₂.M))
  have hdF0 : (0 : ℝ) ≤ dF := Nat.cast_nonneg _
  have hB0 : (0 : ℝ) ≤ (m : ℝ) * (((T.Q.Dw j).p : ℝ) + (T.Q.Dw j).q) * t := by positivity
  have hS0 : 0 ≤ S := by rw [hSe]; positivity
  have hX : (m : ℝ) * (((T.Q.Dw j).p : ℝ) + (T.Q.Dw j).q) * ((t : ℝ) + t) + dF ≤ 2 * S := by rw [hSe]; linarith
  have hdFS : (dF : ℝ) ≤ S := by rw [hSe]; linarith
  have h1 : ((m : ℝ) * (((T.Q.Dw j).p : ℝ) + (T.Q.Dw j).q) * ((t : ℝ) + t) + dF) * Real.log Y.d.l₂.M ≤
      (2 * S) * (30 * Lb) := mul_le_mul hX hM hlM0 (by linarith)
  have h2 : (dF : ℝ) * lD ≤ (D.R.f * S) * (7 * Lb) :=
    (mul_le_mul hdFS hlD hlD0 hS0).trans (le_of_eq (by ring))
  have hLS : 0 ≤ Lb * S := mul_nonneg (by linarith) hS0
  have hA : Lb * S ≤ D.R.f * (Lb * S) := le_mul_of_one_le_left hLS hf1
  have h3 : (2 * S) * (30 * Lb) + (D.R.f * S) * (7 * Lb) ≤ 67 * ((D.R.f : ℝ) * Lb) * S := by linarith
  have hx1 : (1 : ℝ) ≤ D.R.f * D.R.r * Lb :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hf1 hr1) hLb
  have h5 : (D.R.f : ℝ) * Lb ≤ D.R.f * D.R.r * Lb :=
    mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by linarith) hr1) (by linarith)
  have h4 : (D.R.f : ℝ) * Lb ≤ ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 := h5.trans (le_self_pow₀ hx1 (by norm_num))
  have h6 : 67 * ((D.R.f : ℝ) * Lb) * S ≤ 67 * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 * S :=
    mul_le_mul_of_nonneg_right (by linarith) hS0
  linarith

end GlobalTheory.CovIntNum
