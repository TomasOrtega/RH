import Formalism.HermitianCurvature.StatementQ
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CartanInvolutionConjTransposeMul

import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic

open Matrix Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.Q.TPresLie

open Formalism.REAL Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

/- English proof (translation)
The claim follows from `Matrix.inv_eq_right_inv (Hpk_sq k r)`.
-/
lemma hpk_inv : (Hpk k r)⁻¹ = Hpk k r := Matrix.inv_eq_right_inv (Hpk_sq k r)

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨Hpk k r, Hpk k r, Hpk_sq k r, Hpk_sq k r⟩, rfl⟩`.
-/
lemma hpk_unit : IsUnit (Hpk k r) := ⟨⟨Hpk k r, Hpk k r, Hpk_sq k r, Hpk_sq k r⟩, rfl⟩

/- English proof (translation)
Rewrite using `[← mul_assoc, Hpk_sq, one_mul]`.
-/
lemma hpk_hh (A : Mx k r) : Hpk k r * (Hpk k r * A) = A := by rw [← mul_assoc, Hpk_sq, one_mul]

/- English proof (translation)
Unfold `hpart1`. Rewrite using `[hpk_inv]`. Establish `hs : star (1 / 2 : ℂ) = 1 / 2` using `by simp`. Simplify using `only [conjTranspose_smul, conjTranspose_sub, conjTranspose_mul, conjTranspose_conjTranspose, Hpk_herm, hs, mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, mul_assoc, hpk_hh, Hpk_sq, mul_one]`. Rewrite using `[← smul_neg, neg_sub]`.
-/
lemma hpart1_skew (Z : Mx k r) :
    (hpart1 (Hpk k r) Z)ᴴ = -(Hpk k r * hpart1 (Hpk k r) Z * Hpk k r) := by
  unfold hpart1
  rw [hpk_inv]
  have hs : star (1 / 2 : ℂ) = 1 / 2 := by simp
  simp only [conjTranspose_smul, conjTranspose_sub, conjTranspose_mul, conjTranspose_conjTranspose, Hpk_herm, hs,
    mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, mul_assoc, hpk_hh, Hpk_sq, mul_one]
  rw [← smul_neg, neg_sub]

/- English proof (translation)
Unfold `hpart2`. Rewrite using `[hpk_inv]`. Establish `hs : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I))` using `by simp`. Simplify using `only [conjTranspose_smul, conjTranspose_add, conjTranspose_mul, conjTranspose_conjTranspose, Hpk_herm, hs, mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_assoc, hpk_hh, Hpk_sq, mul_one]`. Rewrite using `[neg_smul, add_comm Zᴴ]`.
-/
lemma hpart2_skew (Z : Mx k r) :
    (hpart2 (Hpk k r) Z)ᴴ = -(Hpk k r * hpart2 (Hpk k r) Z * Hpk k r) := by
  unfold hpart2
  rw [hpk_inv]
  have hs : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I)) := by simp
  simp only [conjTranspose_smul, conjTranspose_add, conjTranspose_mul, conjTranspose_conjTranspose, Hpk_herm, hs,
    mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_assoc, hpk_hh, Hpk_sq, mul_one]
  rw [neg_smul, add_comm Zᴴ]

/- English proof (translation)
Rewrite using `[conjTranspose_smul, hX]`. Simplify using `[Complex.star_def, Complex.conj_ofReal, mul_smul_comm, smul_mul_assoc]`.
-/
lemma skew_real (X : Mx k r) (hX : Xᴴ = -(Hpk k r * X * Hpk k r)) (t : ℝ) :
    ((t : ℂ) • X)ᴴ = -(Hpk k r * ((t : ℂ) • X) * Hpk k r) := by
  rw [conjTranspose_smul, hX]
  simp [Complex.star_def, Complex.conj_ofReal, mul_smul_comm, smul_mul_assoc]

/- English proof (translation)
Use `show (NormedSpace.exp Y)ᴴ * Hpk k r * NormedSpace.exp Y = Hpk k r`. Establish `e1 : Yᴴ = Hpk k r * (-Y) * (Hpk k r)⁻¹`. Rewrite using `[hY, hpk_inv, mul_neg, neg_mul]`. Rewrite using `[← Matrix.exp_conjTranspose, e1, Matrix.exp_conj _ _ hpk_unit, hpk_inv]`. Simplify using `only [mul_assoc, hpk_hh]`.

Rewrite using `[← Matrix.exp_add_of_commute _ _ (Commute.refl Y).neg_left, neg_add_cancel, NormedSpace.exp_zero, mul_one]`.
-/
lemma exp_mem_UH (Y : Mx k r) (hY : Yᴴ = -(Hpk k r * Y * Hpk k r)) :
    NormedSpace.exp Y ∈ UH (Hpk k r) := by
  show (NormedSpace.exp Y)ᴴ * Hpk k r * NormedSpace.exp Y = Hpk k r
  have e1 : Yᴴ = Hpk k r * (-Y) * (Hpk k r)⁻¹ := by
    rw [hY, hpk_inv, mul_neg, neg_mul]
  rw [← Matrix.exp_conjTranspose, e1, Matrix.exp_conj _ _ hpk_unit, hpk_inv]
  simp only [mul_assoc, hpk_hh]
  rw [← Matrix.exp_add_of_commute _ _ (Commute.refl Y).neg_left, neg_add_cancel, NormedSpace.exp_zero, mul_one]

/- English proof (translation)
Use `set P : Mx k r := Matrix.single c c 1 with hPdef`. Establish `hYP : Y * P = 0`. Use extensionality with `x y`. Simplify using `only [hPdef, Matrix.mul_apply, Matrix.single_apply, Matrix.zero_apply]`. Use `Finset.sum_eq_zero (fun j _ => ?_)` and prove the remaining obligations.

Use `split_ifs with h`. Rewrite using `[← h.1, hY, mul_one]`. Conclude with `mul_zero _`. Establish `hne : NormedSpace.exp Y ≠ 0`. Introduce `h0`.

Establish `hc : NormedSpace.exp (-Y) * NormedSpace.exp Y = 1`. Rewrite using `[← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl Y)), neg_add_cancel, NormedSpace.exp_zero]`. Rewrite `hc` using `[h0, Matrix.mul_zero]`. Use `congrFun (congrFun hc ⟨0, by omega⟩) ⟨0, by omega⟩` as an intermediate fact. Simplify using `at this`.

Establish `hsum : Summable (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • Y ^ n)`. Assume the negation of the conclusion as `hns`. Apply `hne` to reduce the goal to its premises. Rewrite using `[congrFun (NormedSpace.exp_eq_tsum ℂ) Y]`. Conclude with `tsum_eq_zero_of_not_summable hns`.

Establish `hhas : HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • Y ^ n) (NormedSpace.exp Y)`. Use `hsum.hasSum` as an intermediate fact. Rewrite `this` using `[← congrFun (NormedSpace.exp_eq_tsum ℂ) Y]`. Then use the resulting hypothesis. Establish `h1` using `hhas.mul_right P`. Establish `h2 : HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • Y ^ n * P) P`.

Use `hasSum_single (f := fun n : ℕ => ((n.factorial : ℂ)⁻¹) • Y ^ n * P) 0 (by` as an intermediate fact. Introduce `m hm`. Take `⟨m', rfl⟩` from `Nat.exists_eq_succ_of_ne_zero hm`. Rewrite using `[Matrix.smul_mul, pow_succ, Matrix.mul_assoc, hYP, Matrix.mul_zero, smul_zero])`. Simplify using `using this`.

Establish `hEP : NormedSpace.exp Y * P = P` using `h1.unique h2`. Establish `hPv : P *ᵥ bvec c = bvec c`. Use extensionality with `x`. Distinguish the cases in `h : x = c`. Substitute `h` using the available equality.

Simplify using `[hPdef, bvec, Matrix.mulVec, dotProduct, Matrix.single_apply, Pi.single_apply]`. Simplify using `[hPdef, bvec, Matrix.mulVec, dotProduct, Pi.single_apply, h, Ne.symm h]`. Rewrite using `[← hPv, Matrix.mulVec_mulVec, hEP]`.
-/
lemma exp_fix (Y : Mx k r) (c : Fin (2 * r + k + 1)) (hY : ∀ x, Y x c = 0) :
    NormedSpace.exp Y *ᵥ bvec c = bvec c := by
  set P : Mx k r := Matrix.single c c 1 with hPdef
  have hYP : Y * P = 0 := by
    ext x y
    simp only [hPdef, Matrix.mul_apply, Matrix.single_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    split_ifs with h
    · rw [← h.1, hY, mul_one]
    · exact mul_zero _
  have hne : NormedSpace.exp Y ≠ 0 := by
    intro h0
    have hc : NormedSpace.exp (-Y) * NormedSpace.exp Y = 1 := by
      rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl Y)), neg_add_cancel,
        NormedSpace.exp_zero]
    rw [h0, Matrix.mul_zero] at hc
    have := congrFun (congrFun hc ⟨0, by omega⟩) ⟨0, by omega⟩
    simp at this
  have hsum : Summable (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • Y ^ n) := by
    by_contra hns
    apply hne
    rw [congrFun (NormedSpace.exp_eq_tsum ℂ) Y]
    exact tsum_eq_zero_of_not_summable hns
  have hhas : HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • Y ^ n) (NormedSpace.exp Y) := by
    have := hsum.hasSum
    rwa [← congrFun (NormedSpace.exp_eq_tsum ℂ) Y] at this
  have h1 := hhas.mul_right P
  have h2 : HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • Y ^ n * P) P := by
    have := hasSum_single (f := fun n : ℕ => ((n.factorial : ℂ)⁻¹) • Y ^ n * P) 0 (by
      intro m hm
      obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
      rw [Matrix.smul_mul, pow_succ, Matrix.mul_assoc, hYP, Matrix.mul_zero, smul_zero])
    simpa using this
  have hEP : NormedSpace.exp Y * P = P := h1.unique h2
  have hPv : P *ᵥ bvec c = bvec c := by
    ext x
    by_cases h : x = c
    · subst h; simp [hPdef, bvec, Matrix.mulVec, dotProduct, Matrix.single_apply, Pi.single_apply]
    · simp [hPdef, bvec, Matrix.mulVec, dotProduct, Pi.single_apply, h, Ne.symm h]
  rw [← hPv, Matrix.mulVec_mulVec, hEP]

/- English proof (translation)
Simplify using `only [Glev, UH, Set.mem_setOf_eq] at hg hh ⊢`. Take `⟨hgU, hgF⟩` from `hg`. Take `⟨hhU, hhF⟩` from `hh`. Use `⟨?_, fun a ha => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[conjTranspose_mul, show hᴴ * gᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h by`.

Simplify using `only [mul_assoc], hgU, hhU]`. Rewrite using `[← Matrix.mulVec_mulVec, (hhF a ha).1, (hgF a ha).1]`. Rewrite using `[← Matrix.mulVec_mulVec, (hhF a ha).2, (hgF a ha).2]`.
-/
lemma glev_mul {i : Fin (r + 1)} {g h : Mx k r} (hg : g ∈ Glev k r i) (hh : h ∈ Glev k r i) :
    g * h ∈ Glev k r i := by
  simp only [Glev, UH, Set.mem_setOf_eq] at hg hh ⊢
  obtain ⟨hgU, hgF⟩ := hg
  obtain ⟨hhU, hhF⟩ := hh
  refine ⟨?_, fun a ha => ⟨?_, ?_⟩⟩
  · rw [conjTranspose_mul, show hᴴ * gᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h by
      simp only [mul_assoc], hgU, hhU]
  · rw [← Matrix.mulVec_mulVec, (hhF a ha).1, (hgF a ha).1]
  · rw [← Matrix.mulVec_mulVec, (hhF a ha).2, (hgF a ha).2]

/- English proof (translation)
Simplify using `only [Glev, Set.mem_setOf_eq]`. Use `⟨exp_mem_UH _ (skew_real X hX t), fun a ha => ⟨exp_fix _ _ fun x => ?_, exp_fix _ _ fun x => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[Matrix.smul_apply, (hc a ha x).1, smul_zero]`. Rewrite using `[Matrix.smul_apply, (hc a ha x).2, smul_zero]`.
-/
lemma exp_mem_glev (i : Fin (r + 1)) (X : Mx k r) (hX : Xᴴ = -(Hpk k r * X * Hpk k r))
    (hc : ∀ a : Fin r, a.val < i.val → ∀ x, X x (eI k r a) = 0 ∧ X x (esI k r a) = 0) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ Glev k r i := by
  simp only [Glev, Set.mem_setOf_eq]
  refine ⟨exp_mem_UH _ (skew_real X hX t), fun a ha => ⟨exp_fix _ _ fun x => ?_, exp_fix _ _ fun x => ?_⟩⟩
  · rw [Matrix.smul_apply, (hc a ha x).1, smul_zero]
  · rw [Matrix.smul_apply, (hc a ha x).2, smul_zero]

/- English proof (translation)
Establish `hp` using `p.isLt`. Establish `ha'` using `a.isLt`. Establish `hi` using `i.isLt`. Unfold `mdim at hp`. Simplify using `only [Hpk, posL, eI, esI, Fin.mk.injEq]`.

Apply the tactic sequence `constructor <;> split_ifs <;> first | rfl | (exfalso; omega)`.
-/
lemma hpk_zero (i : Fin (r + 1)) (p : Fin (mdim k r i)) (a : Fin r) (ha : a.val < i.val) :
    Hpk k r (posL k r i p) (eI k r a) = 0 ∧ Hpk k r (posL k r i p) (esI k r a) = 0 := by
  have hp := p.isLt
  have ha' := a.isLt
  have hi := i.isLt
  unfold mdim at hp
  simp only [Hpk, posL, eI, esI, Fin.mk.injEq]
  constructor <;> split_ifs <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Simplify using `[Matrix.single_apply, hcq, Ne.symm hcq]`. Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun l _ => ?_` and prove the remaining obligations. Distinguish the cases in `hl : l = posL k r i p`.

Rewrite using `[hl, hHc, mul_zero]`. Establish `h0 : (Hpk k r * (Matrix.single (posL k r i p) (posL k r i q) (1 : ℂ))ᴴ) x l = 0`. Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun m _ => ?_` and prove the remaining obligations. Simplify using `[Matrix.conjTranspose_apply, Matrix.single_apply, hl, Ne.symm hl]`.

Rewrite using `[h0, zero_mul]`.
-/
lemma unit_col (i : Fin (r + 1)) (p q : Fin (mdim k r i)) (c : Fin (2 * r + k + 1))
    (hcq : c ≠ posL k r i q) (hHc : Hpk k r (posL k r i p) c = 0) (x : Fin (2 * r + k + 1)) :
    (Matrix.single (posL k r i p) (posL k r i q) (1 : ℂ)) x c = 0 ∧
    (Hpk k r * (Matrix.single (posL k r i p) (posL k r i q) (1 : ℂ))ᴴ * Hpk k r) x c = 0 := by
  constructor
  · simp [Matrix.single_apply, hcq, Ne.symm hcq]
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : l = posL k r i p
    · rw [hl, hHc, mul_zero]
    · have h0 : (Hpk k r * (Matrix.single (posL k r i p) (posL k r i q) (1 : ℂ))ᴴ) x l = 0 := by
        rw [Matrix.mul_apply]
        refine Finset.sum_eq_zero fun m _ => ?_
        simp [Matrix.conjTranspose_apply, Matrix.single_apply, hl, Ne.symm hl]
      rw [h0, zero_mul]

/- English proof (translation)
Establish `hq` using `q.isLt`. Establish `ha'` using `a.isLt`. Unfold `mdim at hq`. Apply the tactic sequence `refine ⟨fun h => ?_, fun h => ?_⟩ <;>`. Establish `h2` using `congrArg Fin.val h`.

Simplify using `only [eI, esI, posL] at h2`. Use linear arithmetic over natural numbers and integers.
-/
lemma posL_ne (i : Fin (r + 1)) (q : Fin (mdim k r i)) (a : Fin r) (ha : a.val < i.val) :
    eI k r a ≠ posL k r i q ∧ esI k r a ≠ posL k r i q := by
  have hq := q.isLt
  have ha' := a.isLt
  unfold mdim at hq
  refine ⟨fun h => ?_, fun h => ?_⟩ <;>
  · have h2 := congrArg Fin.val h
    simp only [eI, esI, posL] at h2
    omega

/- English proof (translation)
Establish `key : ∀ a : Fin r, a.val < i.val → ∀ x c, (c = eI k r a ∨ c = esI k r a) → (Matrix.single (posL k r i p) (posL k r i q) (1 : ℂ)) x c = 0 ∧ (Hpk k r * (Matrix.single (posL k r i p) (posL k r i q) (1 : ℂ))ᴴ * Hpk k r) x c = 0`. Introduce `a ha x c hc`. Take `⟨n1, n2⟩` from `posL_ne i q a ha`. Take `⟨z1, z2⟩` from `hpk_zero i p a ha`. Break down `hc with rfl | rfl` into its components or cases.

Conclude with `unit_col i p q _ n1 z1 x`. Conclude with `unit_col i p q _ n2 z2 x`. Apply the tactic sequence `refine ⟨fun a ha x => ?_, fun a ha x => ?_⟩ <;>`. Take `⟨e1, e2⟩` from `key a ha x _ (Or.inl rfl)`. Take `⟨e3, e4⟩` from `key a ha x _ (Or.inr rfl)`.

Simplify using `only [hpart1, hpart2]`. Rewrite using `[hpk_inv]`. Apply the tactic sequence `refine ⟨?_, ?_⟩ <;>`. Use `first`. Consider the case `rw [Matrix.smul_apply, Matrix.sub_apply]`.

Consider the case `rw [Matrix.smul_apply, Matrix.add_apply]`. Simplify using `only [e1, e2, e3, e4, sub_zero, add_zero, smul_zero]`.
-/
lemma hpart_cols (i : Fin (r + 1)) (p q : Fin (mdim k r i)) :
    (∀ a : Fin r, a.val < i.val → ∀ x,
      hpart1 (Hpk k r) (Matrix.single (posL k r i p) (posL k r i q) 1) x (eI k r a) = 0 ∧
      hpart1 (Hpk k r) (Matrix.single (posL k r i p) (posL k r i q) 1) x (esI k r a) = 0) ∧
    (∀ a : Fin r, a.val < i.val → ∀ x,
      hpart2 (Hpk k r) (Matrix.single (posL k r i p) (posL k r i q) 1) x (eI k r a) = 0 ∧
      hpart2 (Hpk k r) (Matrix.single (posL k r i p) (posL k r i q) 1) x (esI k r a) = 0) := by
  have key : ∀ a : Fin r, a.val < i.val → ∀ x c, (c = eI k r a ∨ c = esI k r a) →
      (Matrix.single (posL k r i p) (posL k r i q) (1 : ℂ)) x c = 0 ∧
      (Hpk k r * (Matrix.single (posL k r i p) (posL k r i q) (1 : ℂ))ᴴ * Hpk k r) x c = 0 := by
    intro a ha x c hc
    obtain ⟨n1, n2⟩ := posL_ne i q a ha
    obtain ⟨z1, z2⟩ := hpk_zero i p a ha
    rcases hc with rfl | rfl
    · exact unit_col i p q _ n1 z1 x
    · exact unit_col i p q _ n2 z2 x
  refine ⟨fun a ha x => ?_, fun a ha x => ?_⟩ <;>
  · obtain ⟨e1, e2⟩ := key a ha x _ (Or.inl rfl)
    obtain ⟨e3, e4⟩ := key a ha x _ (Or.inr rfl)
    simp only [hpart1, hpart2]
    rw [hpk_inv]
    refine ⟨?_, ?_⟩ <;>
    · first
      | rw [Matrix.smul_apply, Matrix.sub_apply]
      | rw [Matrix.smul_apply, Matrix.add_apply]
      simp only [e1, e2, e3, e4, sub_zero, add_zero, smul_zero]

/- English proof (translation)
The claim follows from `exp_mem_glev i _ (hpart1_skew _) (hpart_cols i p q).1 t`.
-/
theorem exp_hpart1_mem (i : Fin (r + 1)) (p q : Fin (mdim k r i)) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • hpart1 (Hpk k r) (Matrix.single (posL k r i p) (posL k r i q) 1))
      ∈ Glev k r i := exp_mem_glev i _ (hpart1_skew _) (hpart_cols i p q).1 t

/- English proof (translation)
The claim follows from `exp_mem_glev i _ (hpart2_skew _) (hpart_cols i p q).2 t`.
-/
theorem exp_hpart2_mem (i : Fin (r + 1)) (p q : Fin (mdim k r i)) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • hpart2 (Hpk k r) (Matrix.single (posL k r i p) (posL k r i q) 1))
      ∈ Glev k r i := exp_mem_glev i _ (hpart2_skew _) (hpart_cols i p q).2 t

/- English proof (translation)
Establish `hγ` using `hasDerivAt_mul_exp_smul_zero g X`. Establish `hγ0 : g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g`. Simplify using `[NormedSpace.exp_zero]`. Establish `hFd : DifferentiableAt ℝ F g` using `(hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hg)`. Establish `hcomp : HasDerivAt (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X))) (fderiv ℝ F g (g * X)) 0` using `hFd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0.symm`.

Establish `hev : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[𝓝 0] (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X)))`. Establish `hmem : ∀ᶠ t : ℝ in 𝓝 0, g * NormedSpace.exp ((t : ℂ) • X) ∈ U` using `hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hU.mem_nhds hg)`. Use `filter_upwards [hmem] with t ht`. Conclude with `hfF _ ht (glev_mul hgG (hX t))`. Conclude with `hcomp.congr_of_eventuallyEq hev`.
-/
theorem hasDerivAt_ext {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (i : Fin (r + 1)) (X : Mx k r) (hX : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Glev k r i)
    (f F : Mx k r → E) (U : Set (Mx k r)) (g : Mx k r) (hU : IsOpen U) (hg : g ∈ U)
    (hgG : g ∈ Glev k r i) (hF : ContDiffOn ℝ ∞ F U)
    (hfF : ∀ x ∈ U, x ∈ Glev k r i → f x = F x) :
    HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) (fderiv ℝ F g (g * X)) 0 := by
  have hγ := hasDerivAt_mul_exp_smul_zero g X
  have hγ0 : g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g := by
    simp [NormedSpace.exp_zero]
  have hFd : DifferentiableAt ℝ F g :=
    (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hg)
  have hcomp : HasDerivAt (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X)))
      (fderiv ℝ F g (g * X)) 0 :=
    hFd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0.symm
  have hev : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[𝓝 0]
      (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X))) := by
    have hmem : ∀ᶠ t : ℝ in 𝓝 0, g * NormedSpace.exp ((t : ℂ) • X) ∈ U :=
      hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hU.mem_nhds hg)
    filter_upwards [hmem] with t ht
    exact hfF _ ht (glev_mul hgG (hX t))
  exact hcomp.congr_of_eventuallyEq hev

/- English proof (translation)
The claim follows from `(hasDerivAt_ext i X hX f F U g hU hg hgG hF hfF).deriv`.
-/
theorem rdV_ext {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (i : Fin (r + 1)) (X : Mx k r) (hX : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Glev k r i)
    (f F : Mx k r → E) (U : Set (Mx k r)) (g : Mx k r) (hU : IsOpen U) (hg : g ∈ U)
    (hgG : g ∈ Glev k r i) (hF : ContDiffOn ℝ ∞ F U)
    (hfF : ∀ x ∈ U, x ∈ Glev k r i → f x = F x) :
    RdV X f g = fderiv ℝ F g (g * X) := (hasDerivAt_ext i X hX f F U g hU hg hgG hF hfF).deriv

end Formalism.FourierDecayAlt.Q.TPresLie
