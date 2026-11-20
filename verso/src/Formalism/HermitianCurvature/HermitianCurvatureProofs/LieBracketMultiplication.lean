import Formalism.HermitianCurvature.FrameExists2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftDerivativeCurves
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameEntries

open Matrix Finset Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.QrD

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace LieBracketMultiplication

section Geometry

variable {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}

/- English proof (translation)
Take `⟨hg1, hg2, hg3⟩` from `hg`. Take `⟨hh1, hh2, hh3⟩` from `hh`. Use `⟨?_, fun a => ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Establish `e1 : gᴴ * Hpk k r * g = Hpk k r` using `hg1`. Establish `e2 : hᴴ * Hpk k r * h = Hpk k r` using `hh1`.

Use `show (g * h)ᴴ * Hpk k r * (g * h) = Hpk k r`. Rewrite using `[Matrix.conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Matrix.mulVec_mulVec, (hh2 a).1, (hg2 a).1]`. Rewrite using `[← Matrix.mulVec_mulVec, (hh2 a).2, (hg2 a).2]`.

Rewrite using `[← Matrix.mulVec_mulVec, hh3, hg3]`.
-/
theorem uw_mul {g h : Mx k r} (hg : g ∈ UWset k r z) (hh : h ∈ UWset k r z) : g * h ∈ UWset k r z := by
  obtain ⟨hg1, hg2, hg3⟩ := hg
  obtain ⟨hh1, hh2, hh3⟩ := hh
  refine ⟨?_, fun a => ⟨?_, ?_⟩, ?_⟩
  · have e1 : gᴴ * Hpk k r * g = Hpk k r := hg1
    have e2 : hᴴ * Hpk k r * h = Hpk k r := hh1
    show (g * h)ᴴ * Hpk k r * (g * h) = Hpk k r
    rw [Matrix.conjTranspose_mul]
    calc hᴴ * gᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h := by simp only [Matrix.mul_assoc]
      _ = Hpk k r := by rw [e1, e2]
  · rw [← Matrix.mulVec_mulVec, (hh2 a).1, (hg2 a).1]
  · rw [← Matrix.mulVec_mulVec, (hh2 a).2, (hg2 a).2]
  · rw [← Matrix.mulVec_mulVec, hh3, hg3]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Rewrite using `[pow_zero]`. Use `⟨?_, fun a => ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Use `show (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ᴴ * Hpk k r * 1 = Hpk k r`.

Simplify using the standard rewrite rules. Apply the tactic sequence `all_goals simp`. Consider the case `succ n ih`. Rewrite using `[pow_succ]`. Conclude with `uw_mul ih hg`.
-/
theorem uw_pow {g : Mx k r} (hg : g ∈ UWset k r z) (n : ℕ) : g ^ n ∈ UWset k r z := by
  induction n with
  | zero =>
    rw [pow_zero]
    refine ⟨?_, fun a => ⟨?_, ?_⟩, ?_⟩
    · show (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ᴴ * Hpk k r * 1 = Hpk k r
      simp
    all_goals simp
  | succ n ih =>
    rw [pow_succ]
    exact uw_mul ih hg

/- English proof (translation)
Use `FrameEntries.glev_inv (Qx8.uw_glev (Fin.last r) hh)` as an intermediate fact. Use `⟨this.1, fun a => this.2 a (by simp), ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem uw_inv {h : Mx k r} (hh : h ∈ UWset k r z) : h⁻¹ ∈ UWset k r z := by
  have := FrameEntries.glev_inv (Qx8.uw_glev (Fin.last r) hh)
  refine ⟨this.1, fun a => this.2 a (by simp), ?_⟩
  calc h⁻¹ *ᵥ z = h⁻¹ *ᵥ (h *ᵥ z) := by rw [hh.2.2]
    _ = z := by rw [Matrix.mulVec_mulVec, LeftDerivativeCurves.uh_inv_mul hh.1, Matrix.one_mulVec]

/- English proof (translation)
Unfold `InLieW inLieLev`. Use `⟨?_, by simp⟩` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem lie_zero : InLieW k r z (0 : Mx k r) := by
  unfold InLieW inLieLev
  refine ⟨?_, by simp⟩
  simp

/- English proof (translation)
Unfold `InLieW inLieLev at *`. Take `⟨⟨h1, h1'⟩, h2⟩` from `hX`. Take `⟨⟨h3, h3'⟩, h4⟩` from `hY`. Use `⟨⟨?_, fun a ha => ⟨?_, ?_⟩⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.conjTranspose_add, add_mul, mul_add]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.add_mulVec, (h1' a ha).1, (h3' a ha).1, add_zero]`. Rewrite using `[Matrix.add_mulVec, (h1' a ha).2, (h3' a ha).2, add_zero]`. Rewrite using `[Matrix.add_mulVec, h2, h4, add_zero]`.
-/
theorem lie_add {X Y : Mx k r} (hX : InLieW k r z X) (hY : InLieW k r z Y) : InLieW k r z (X + Y) := by
  unfold InLieW inLieLev at *
  obtain ⟨⟨h1, h1'⟩, h2⟩ := hX
  obtain ⟨⟨h3, h3'⟩, h4⟩ := hY
  refine ⟨⟨?_, fun a ha => ⟨?_, ?_⟩⟩, ?_⟩
  · rw [Matrix.conjTranspose_add, add_mul, mul_add]
    calc Xᴴ * Hpk k r + Yᴴ * Hpk k r + (Hpk k r * X + Hpk k r * Y)
        = (Xᴴ * Hpk k r + Hpk k r * X) + (Yᴴ * Hpk k r + Hpk k r * Y) := by abel
      _ = 0 := by rw [h1, h3, add_zero]
  · rw [Matrix.add_mulVec, (h1' a ha).1, (h3' a ha).1, add_zero]
  · rw [Matrix.add_mulVec, (h1' a ha).2, (h3' a ha).2, add_zero]
  · rw [Matrix.add_mulVec, h2, h4, add_zero]

/- English proof (translation)
Unfold `InLieW inLieLev at *`. Take `⟨⟨h1, h1'⟩, h2⟩` from `hX`. Establish `hs : star (s : ℂ) = (s : ℂ)` using `Complex.conj_ofReal s`. Use `⟨⟨?_, fun a ha => ⟨?_, ?_⟩⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.conjTranspose_smul, hs, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h1, smul_zero]`.

Use `first`. Consider the case `rw [Matrix.smul_mulVec, (h1' a ha).1, smul_zero]`. Consider the case `simp [(h1' a ha).1]`. Use `first`. Consider the case `rw [Matrix.smul_mulVec, (h1' a ha).2, smul_zero]`.

Consider the case `simp [(h1' a ha).2]`. Use `first`. Consider the case `rw [Matrix.smul_mulVec, h2, smul_zero]`. Consider the case `simp [h2]`.
-/
theorem lie_smul {X : Mx k r} (hX : InLieW k r z X) (s : ℝ) : InLieW k r z ((s : ℂ) • X) := by
  unfold InLieW inLieLev at *
  obtain ⟨⟨h1, h1'⟩, h2⟩ := hX
  have hs : star (s : ℂ) = (s : ℂ) := Complex.conj_ofReal s
  refine ⟨⟨?_, fun a ha => ⟨?_, ?_⟩⟩, ?_⟩
  · rw [Matrix.conjTranspose_smul, hs, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h1, smul_zero]
  · first
    | rw [Matrix.smul_mulVec, (h1' a ha).1, smul_zero]
    | simp [(h1' a ha).1]
  · first
    | rw [Matrix.smul_mulVec, (h1' a ha).2, smul_zero]
    | simp [(h1' a ha).2]
  · first
    | rw [Matrix.smul_mulVec, h2, smul_zero]
    | simp [h2]

/- English proof (translation)
Unfold `InLieW inLieLev at *`. Take `⟨⟨h1, h1'⟩, h2⟩` from `hX`. Take `⟨⟨h3, h3'⟩, h4⟩` from `hY`. Establish `eX : Xᴴ * Hpk k r = -(Hpk k r * X)` using `eq_neg_of_add_eq_zero_left h1`. Establish `eY : Yᴴ * Hpk k r = -(Hpk k r * Y)` using `eq_neg_of_add_eq_zero_left h3`.

Establish `t1 : Yᴴ * Xᴴ * Hpk k r = Hpk k r * Y * X`. Rewrite using `[mul_assoc, eX, mul_neg, ← mul_assoc, eY, neg_mul, neg_neg]`. Establish `t2 : Xᴴ * Yᴴ * Hpk k r = Hpk k r * X * Y`. Rewrite using `[mul_assoc, eY, mul_neg, ← mul_assoc, eX, neg_mul, neg_neg]`. Use `⟨⟨?_, fun a ha => ⟨?_, ?_⟩⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, sub_mul, t1, t2, mul_sub, ← mul_assoc, ← mul_assoc]`. Normalize the expressions using the abelian group laws. Rewrite using `[Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, (h1' a ha).1, (h3' a ha).1, Matrix.mulVec_zero, Matrix.mulVec_zero, sub_zero]`. Rewrite using `[Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, (h1' a ha).2, (h3' a ha).2, Matrix.mulVec_zero, Matrix.mulVec_zero, sub_zero]`. Rewrite using `[Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h2, h4, Matrix.mulVec_zero, Matrix.mulVec_zero, sub_zero]`.
-/
theorem lie_bracket {X Y : Mx k r} (hX : InLieW k r z X) (hY : InLieW k r z Y) :
    InLieW k r z (X * Y - Y * X) := by
  unfold InLieW inLieLev at *
  obtain ⟨⟨h1, h1'⟩, h2⟩ := hX
  obtain ⟨⟨h3, h3'⟩, h4⟩ := hY
  have eX : Xᴴ * Hpk k r = -(Hpk k r * X) := eq_neg_of_add_eq_zero_left h1
  have eY : Yᴴ * Hpk k r = -(Hpk k r * Y) := eq_neg_of_add_eq_zero_left h3
  have t1 : Yᴴ * Xᴴ * Hpk k r = Hpk k r * Y * X := by
    rw [mul_assoc, eX, mul_neg, ← mul_assoc, eY, neg_mul, neg_neg]
  have t2 : Xᴴ * Yᴴ * Hpk k r = Hpk k r * X * Y := by
    rw [mul_assoc, eY, mul_neg, ← mul_assoc, eX, neg_mul, neg_neg]
  refine ⟨⟨?_, fun a ha => ⟨?_, ?_⟩⟩, ?_⟩
  · rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, sub_mul, t1, t2,
      mul_sub, ← mul_assoc, ← mul_assoc]
    abel
  · rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, (h1' a ha).1, (h3' a ha).1,
      Matrix.mulVec_zero, Matrix.mulVec_zero, sub_zero]
  · rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, (h1' a ha).2, (h3' a ha).2,
      Matrix.mulVec_zero, Matrix.mulVec_zero, sub_zero]
  · rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h2, h4,
      Matrix.mulVec_zero, Matrix.mulVec_zero, sub_zero]

/- English proof (translation)
Establish `hi` using `uw_inv hh`. Establish `h1` using `LeftDerivativeCurves.lie_conj (Qx8.uw_glev (Fin.last r) hi) hX.1`. Rewrite `h1` using `[Matrix.nonsing_inv_nonsing_inv _ (WeylGroupFacts.isUnit_of_uh hh.1)]`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Rewrite using `[← Matrix.mulVec_mulVec, hi.2.2, ← Matrix.mulVec_mulVec, hX.2, Matrix.mulVec_zero]`.
-/
theorem lie_conj {X h : Mx k r} (hX : InLieW k r z X) (hh : h ∈ UWset k r z) : InLieW k r z (h * X * h⁻¹) := by
  have hi := uw_inv hh
  have h1 := LeftDerivativeCurves.lie_conj (Qx8.uw_glev (Fin.last r) hi) hX.1
  rw [Matrix.nonsing_inv_nonsing_inv _ (WeylGroupFacts.isUnit_of_uh hh.1)] at h1
  refine ⟨h1, ?_⟩
  rw [← Matrix.mulVec_mulVec, hi.2.2, ← Matrix.mulVec_mulVec, hX.2, Matrix.mulVec_zero]

/- English proof (translation)
Establish `e : (((-s : ℝ) : ℂ) • X) = -((s : ℂ) • X)`. Use `push_cast`. Rewrite using `[neg_smul]`. Rewrite using `[e, Matrix.exp_neg]`.
-/
theorem exp_inv (X : Mx k r) (s : ℝ) :
    (NormedSpace.exp ((s : ℂ) • X))⁻¹ = NormedSpace.exp (((-s : ℝ) : ℂ) • X) := by
  have e : (((-s : ℝ) : ℂ) • X) = -((s : ℂ) • X) := by
    push_cast
    rw [neg_smul]
  rw [e, Matrix.exp_neg]

end Geometry

section Rep

variable {k r : ℕ} {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (W →L[ℂ] W)}

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa using hπ.1`. Consider the case `succ n ih`. Rewrite using `[pow_succ, hπ.2 _ (uw_pow hg n) _ hg, ih, pow_succ]`. Apply the tactic sequence `try rfl`.
-/
theorem pi_pow (hπ : IsCRepOn (UWset k r z) π) {g : Mx k r} (hg : g ∈ UWset k r z) (n : ℕ) :
    π (g ^ n) = (π g) ^ n := by
  induction n with
  | zero => simpa using hπ.1
  | succ n ih =>
    rw [pow_succ, hπ.2 _ (uw_pow hg n) _ hg, ih, pow_succ]
    try rfl

/- English proof (translation)
Unfold `dOp`. Establish `h` using `deriv_comp_mul_left s (fun u : ℝ => π (NormedSpace.exp ((u : ℂ) • X))) 0`. Rewrite `h` using `[mul_zero]`. Rewrite using `[← h]`. Use `congr 1`.

Use function extensionality and compare the values at `t`. Use `congr 2`. Use `push_cast`. Rewrite using `[smul_smul, mul_comm (t : ℂ) (s : ℂ)]`.
-/
theorem dOp_smul (hπ : Qr.IsRepW k r z π) {X : Mx k r} (hX : InLieW k r z X) (s : ℝ) :
    dOp π ((s : ℂ) • X) = s • dOp π X := by
  unfold dOp
  have h := deriv_comp_mul_left s (fun u : ℝ => π (NormedSpace.exp ((u : ℂ) • X))) 0
  rw [mul_zero] at h
  rw [← h]
  congr 1
  funext t
  congr 2
  push_cast
  rw [smul_smul, mul_comm (t : ℂ) (s : ℂ)]

end Rep

end LieBracketMultiplication

/- English proof (translation)
Introduce `W _ _ _ k r z π hπ X hX h hh`. Establish `hi` using `LieBracketMultiplication.uw_inv hh`. Use `⟨hi, LieBracketMultiplication.lie_conj hX hh, ?_⟩` and prove the remaining obligations. Establish `hd` using `dOp_hasDeriv hπ.1 hπ.2 hX`. Set `L : (W →L[ℂ] W) →L[ℂ] (W →L[ℂ] W)` to `(ContinuousLinearMap.compL ℂ W W W (π h)).comp ((ContinuousLinearMap.compL ℂ W W W).flip (π h⁻¹))`.

Establish `h2` using `(L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd`. Establish `h3 : (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • (h * X * h⁻¹)))) = (L.restrictScalars ℝ) ∘ fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X))`. Use function extensionality and compare the values at `t`. Rewrite using `[Qx8.exp_conj_uh hh.1, Matrix.mul_assoc, hπ.1.2 _ hh _ (LieBracketMultiplication.uw_mul (exp_uw hX t) hi), hπ.1.2 _ (exp_uw hX t) _ hi]`. Both sides reduce to the same expression.

Unfold `dOp`. Rewrite using `[h3]`. Conclude with `h2.deriv`.
-/
theorem differential_operator_adjoint : Formalism.FourierDecayAlt.Qr.DOpAd := by
  intro W _ _ _ k r z π hπ X hX h hh
  have hi := LieBracketMultiplication.uw_inv hh
  refine ⟨hi, LieBracketMultiplication.lie_conj hX hh, ?_⟩
  have hd := dOp_hasDeriv hπ.1 hπ.2 hX
  let L : (W →L[ℂ] W) →L[ℂ] (W →L[ℂ] W) :=
    (ContinuousLinearMap.compL ℂ W W W (π h)).comp ((ContinuousLinearMap.compL ℂ W W W).flip (π h⁻¹))
  have h2 := (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
  have h3 : (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • (h * X * h⁻¹)))) =
      (L.restrictScalars ℝ) ∘ fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X)) := by
    funext t
    rw [Qx8.exp_conj_uh hh.1, Matrix.mul_assoc, hπ.1.2 _ hh _ (LieBracketMultiplication.uw_mul (exp_uw hX t) hi),
      hπ.1.2 _ (exp_uw hX t) _ hi]
    rfl
  unfold dOp
  rw [h3]
  exact h2.deriv

namespace LieBracketMultiplication

section Add

variable {k r : ℕ} {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (W →L[ℂ] W)}

/- English proof (translation)
Establish `: CompleteSpace W` using `FiniteDimensional.complete ℂ W`. Establish `hX'` using `lie_smul hX t`. Establish `hY'` using `lie_smul hY t`. Establish `h1` using `hM _ ((t : ℂ) • X) ((t : ℂ) • Y)`. Rewrite `h1` using `[← smul_add]`.

Establish `hmem : ∀ n : ℕ, (NormedSpace.exp ((((n : ℝ)⁻¹ : ℝ) : ℂ) • ((t : ℂ) • X)) * NormedSpace.exp ((((n : ℝ)⁻¹ : ℝ) : ℂ) • ((t : ℂ) • Y))) ^ n ∈ UWset k r z` using `fun n => uw_pow (uw_mul (exp_uw hX' _) (exp_uw hY' _)) n`. Establish `hlim` using `exp_uw (lie_add hX hY) t`. Establish `h2` using `(hπ.2 _ hlim).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨h1, Eventually.of_forall hmem⟩)`. Establish `h3` using `hT (W →L[ℂ] W) (t • dOp π X) (t • dOp π Y)`. Rewrite `h3` using `[← smul_add]`.

Use `tendsto_nhds_unique h2 (h3.congr fun n => ?_)` and prove the remaining obligations. Simplify using `only [Function.comp]`. Rewrite using `[pi_pow hπ.1 (uw_mul (exp_uw hX' _) (exp_uw hY' _)) n, hπ.1.2 _ (exp_uw hX' _) _ (exp_uw hY' _), hP W k r z π hπ _ hX', hP W k r z π hπ _ hY', dOp_smul hπ hX, dOp_smul hπ hY]`. Both sides reduce to the same expression.
-/
theorem pi_exp_add (hT : Qr.Trotter) (hM : Qr.TrotterMx) (hP : Qr.PiExp) (hπ : Qr.IsRepW k r z π) {X Y : Mx k r}
    (hX : InLieW k r z X) (hY : InLieW k r z Y) (t : ℝ) :
    π (NormedSpace.exp ((t : ℂ) • (X + Y))) = NormedSpace.exp (t • (dOp π X + dOp π Y)) := by
  have : CompleteSpace W := FiniteDimensional.complete ℂ W
  have hX' := lie_smul hX t
  have hY' := lie_smul hY t
  have h1 := hM _ ((t : ℂ) • X) ((t : ℂ) • Y)
  rw [← smul_add] at h1
  have hmem : ∀ n : ℕ, (NormedSpace.exp ((((n : ℝ)⁻¹ : ℝ) : ℂ) • ((t : ℂ) • X)) *
      NormedSpace.exp ((((n : ℝ)⁻¹ : ℝ) : ℂ) • ((t : ℂ) • Y))) ^ n ∈ UWset k r z :=
    fun n => uw_pow (uw_mul (exp_uw hX' _) (exp_uw hY' _)) n
  have hlim := exp_uw (lie_add hX hY) t
  have h2 := (hπ.2 _ hlim).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨h1, Eventually.of_forall hmem⟩)
  have h3 := hT (W →L[ℂ] W) (t • dOp π X) (t • dOp π Y)
  rw [← smul_add] at h3
  refine tendsto_nhds_unique h2 (h3.congr fun n => ?_)
  simp only [Function.comp]
  rw [pi_pow hπ.1 (uw_mul (exp_uw hX' _) (exp_uw hY' _)) n, hπ.1.2 _ (exp_uw hX' _) _ (exp_uw hY' _),
    hP W k r z π hπ _ hX', hP W k r z π hπ _ hY', dOp_smul hπ hX, dOp_smul hπ hY]
  rfl

end Add

end LieBracketMultiplication

/- English proof (translation)
Introduce `W _ _ _ k r z π hπ X Y hX hY`. Use `⟨?_, fun s => LieBracketMultiplication.dOp_smul hπ hX s⟩` and prove the remaining obligations. Establish `: CompleteSpace W` using `FiniteDimensional.complete ℂ W`. Establish `h` using `hasDerivAt_exp_smul_const (𝕂 := ℝ) (dOp π X + dOp π Y) (0 : ℝ)`. Rewrite `h` using `[zero_smul, NormedSpace.exp_zero, one_mul]`.

Establish `e : (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • (X + Y)))) = fun t : ℝ => NormedSpace.exp (t • (dOp π X + dOp π Y))`. Use function extensionality and compare the values at `(LieBracketMultiplication.pi_exp_add hT hM hP hπ hX hY)`. Use `show deriv (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • (X + Y)))) 0 = _`. Rewrite using `[e]`. Conclude with `h.deriv`.
-/
theorem qr_dOpLin_of (hT : Formalism.FourierDecayAlt.Qr.Trotter) (hM : Formalism.FourierDecayAlt.Qr.TrotterMx) (hP : Formalism.FourierDecayAlt.Qr.PiExp) :
    Formalism.FourierDecayAlt.Qr.DOpLin := by
  intro W _ _ _ k r z π hπ X Y hX hY
  refine ⟨?_, fun s => LieBracketMultiplication.dOp_smul hπ hX s⟩
  have : CompleteSpace W := FiniteDimensional.complete ℂ W
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) (dOp π X + dOp π Y) (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
  have e : (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • (X + Y)))) =
      fun t : ℝ => NormedSpace.exp (t • (dOp π X + dOp π Y)) :=
    funext (LieBracketMultiplication.pi_exp_add hT hM hP hπ hX hY)
  show deriv (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • (X + Y)))) 0 = _
  rw [e]
  exact h.deriv

namespace LieBracketMultiplication

section Bracket

variable {k r : ℕ}

/- English proof (translation)
Use `first`. Consider the case `exact (Complex.coe_smul s X).symm`. Consider the case `simp [Complex.coe_smul]`.
-/
theorem real_smul (s : ℝ) (X : Mx k r) : s • X = (s : ℂ) • X := by
  first
  | exact (Complex.coe_smul s X).symm
  | simp [Complex.coe_smul]

def lieSub (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Submodule ℝ (Mx k r) where
  carrier := {X | InLieW k r z X}
  add_mem' := fun hX hY => lie_add hX hY
  zero_mem' := lie_zero
  smul_mem' := fun s X hX => by
    show InLieW k r z (s • X)
    rw [real_smul]
    exact lie_smul hX s

def mulB (k r : ℕ) : Mx k r →L[ℝ] Mx k r →L[ℝ] Mx k r :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (Mx k r →ₗ[ℝ] Mx k r) ≃ₗ[ℝ] (Mx k r →L[ℝ] Mx k r)).toLinearMap ∘ₗ
      LinearMap.mul ℝ (Mx k r))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mulB_apply (X Y : Mx k r) : mulB k r X Y = X * Y := rfl

/- English proof (translation)
Establish `hu` using `LeftDerivativeCurves.lcurve_hasDeriv X Y`. Establish `hv` using `hasDerivAt_mul_exp_smul_zero (1 : Mx k r) (-X)`. Establish `h : HasDerivAt (fun s : ℝ => NormedSpace.exp ((s : ℂ) • X) * Y * ((1 : Mx k r) * NormedSpace.exp ((s : ℂ) • (-X)))) (NormedSpace.exp (((0 : ℝ) : ℂ) • X) * Y * ((1 : Mx k r) * -X) + X * Y * ((1 : Mx k r) * NormedSpace.exp (((0 : ℝ) : ℂ) • (-X)))) 0` using `(mulB k r).hasDerivAt_of_bilinear (fun _ => hu) (fun _ => hv)`. Simplify using `only [Matrix.one_mul, Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, Matrix.mul_one, Matrix.mul_neg] at h`. Rewrite `h` using `[neg_add_eq_sub]`.

Conclude with `h`.
-/
theorem conj_hasDeriv (X Y : Mx k r) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp ((s : ℂ) • X) * Y * NormedSpace.exp ((s : ℂ) • (-X)))
      (X * Y - Y * X) 0 := by
  have hu := LeftDerivativeCurves.lcurve_hasDeriv X Y
  have hv := hasDerivAt_mul_exp_smul_zero (1 : Mx k r) (-X)
  have h : HasDerivAt
      (fun s : ℝ => NormedSpace.exp ((s : ℂ) • X) * Y * ((1 : Mx k r) * NormedSpace.exp ((s : ℂ) • (-X))))
      (NormedSpace.exp (((0 : ℝ) : ℂ) • X) * Y * ((1 : Mx k r) * -X) +
        X * Y * ((1 : Mx k r) * NormedSpace.exp (((0 : ℝ) : ℂ) • (-X)))) 0 :=
    (mulB k r).hasDerivAt_of_bilinear (fun _ => hu) (fun _ => hv)
  simp only [Matrix.one_mul, Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, Matrix.mul_one,
    Matrix.mul_neg] at h
  rw [neg_add_eq_sub] at h
  exact h

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]

/- English proof (translation)
Establish `: CompleteSpace W` using `FiniteDimensional.complete ℂ W`. Establish `ha` using `hasDerivAt_exp_smul_const (𝕂 := ℝ) A (0 : ℝ)`. Establish `hb` using `hasDerivAt_exp_smul_const (𝕂 := ℝ) (-A) (0 : ℝ)`. Establish `h` using `(ha.mul_const B).mul hb`. Simplify using `only [zero_smul, NormedSpace.exp_zero, one_mul, mul_one, mul_neg] at h`.

Rewrite `h` using `[← sub_eq_add_neg]`. Conclude with `h`.
-/
theorem op_hasDeriv (A B : W →L[ℂ] W) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (s • A) * B * NormedSpace.exp (s • (-A))) (A * B - B * A) 0 := by
  have : CompleteSpace W := FiniteDimensional.complete ℂ W
  have ha := hasDerivAt_exp_smul_const (𝕂 := ℝ) A (0 : ℝ)
  have hb := hasDerivAt_exp_smul_const (𝕂 := ℝ) (-A) (0 : ℝ)
  have h := (ha.mul_const B).mul hb
  simp only [zero_smul, NormedSpace.exp_zero, one_mul, mul_one, mul_neg] at h
  rw [← sub_eq_add_neg] at h
  exact h

end Bracket

end LieBracketMultiplication

/- English proof (translation)
Introduce `W _ _ _ k r z π hπ X Y hX hY`. Establish `hbr` using `LieBracketMultiplication.lie_bracket hX hY`. Use `⟨hbr, ?_⟩` and prove the remaining obligations. Set `Λ₀ : LieBracketMultiplication.lieSub k r z →ₗ[ℝ] (W →L[ℂ] W)` to `{ toFun := fun U => dOp π U.1 map_add' := fun U V => (hL W k r z π hπ U.1 V.1 U.2 V.2).1 map_smul' := fun s U => by show dOp π (s • U.1) = s • dOp π U.1`. Rewrite using `[LieBracketMultiplication.real_smul]`.

Conclude with `(hL W k r z π hπ U.1 U.1 U.2 U.2).2 s }`. Take `⟨Λ, hΛ⟩` from `LinearMap.exists_extend Λ₀`. Establish `hΛ' : ∀ U : Mx k r, InLieW k r z U → Λ U = dOp π U` using `fun U hU => LinearMap.congr_fun hΛ (⟨U, hU⟩ : LieBracketMultiplication.lieSub k r z)`. Establish `h1` using `(LinearMap.toContinuousLinearMap Λ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (LieBracketMultiplication.conj_hasDeriv X Y)`. Establish `h2` using `LieBracketMultiplication.op_hasDeriv (dOp π X) (dOp π Y)`.

Establish `e : (LinearMap.toContinuousLinearMap Λ) ∘ (fun s : ℝ => NormedSpace.exp ((s : ℂ) • X) * Y * NormedSpace.exp ((s : ℂ) • (-X))) = fun s : ℝ => NormedSpace.exp (s • dOp π X) * dOp π Y * NormedSpace.exp (s • (-dOp π X))`. Use function extensionality and compare the values at `s`. Establish `e1 : (s : ℂ) • (-X) = ((-s : ℝ) : ℂ) • X`. Rewrite using `[Complex.ofReal_neg, neg_smul, smul_neg]`. Establish `e2 : s • (-dOp π X) = (-s) • dOp π X` using `by rw [neg_smul, smul_neg]`.

Establish `h3` using `hAd W k r z π hπ Y hY _ (exp_uw hX s)`. Use `show Λ (NormedSpace.exp ((s : ℂ) • X) * Y * NormedSpace.exp ((s : ℂ) • (-X))) = _`. Rewrite using `[e1, ← LieBracketMultiplication.exp_inv, hΛ' _ h3.2.1, h3.2.2, LieBracketMultiplication.exp_inv, hP W k r z π hπ X hX, hP W k r z π hπ X hX, e2, mul_assoc]`. Both sides reduce to the same expression. Rewrite `h1` using `[e]`.

Establish `h4` using `h1.unique h2`. Rewrite using `[← hΛ' _ hbr]`. Conclude with `h4`.
-/
theorem qr_dOpBracket_of (hP : Formalism.FourierDecayAlt.Qr.PiExp) (hL : Formalism.FourierDecayAlt.Qr.DOpLin) (hAd : Formalism.FourierDecayAlt.Qr.DOpAd) :
    Formalism.FourierDecayAlt.Qr.DOpBracket := by
  intro W _ _ _ k r z π hπ X Y hX hY
  have hbr := LieBracketMultiplication.lie_bracket hX hY
  refine ⟨hbr, ?_⟩
  let Λ₀ : LieBracketMultiplication.lieSub k r z →ₗ[ℝ] (W →L[ℂ] W) :=
    { toFun := fun U => dOp π U.1
      map_add' := fun U V => (hL W k r z π hπ U.1 V.1 U.2 V.2).1
      map_smul' := fun s U => by
        show dOp π (s • U.1) = s • dOp π U.1
        rw [LieBracketMultiplication.real_smul]
        exact (hL W k r z π hπ U.1 U.1 U.2 U.2).2 s }
  obtain ⟨Λ, hΛ⟩ := LinearMap.exists_extend Λ₀
  have hΛ' : ∀ U : Mx k r, InLieW k r z U → Λ U = dOp π U := fun U hU =>
    LinearMap.congr_fun hΛ (⟨U, hU⟩ : LieBracketMultiplication.lieSub k r z)
  have h1 := (LinearMap.toContinuousLinearMap Λ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (LieBracketMultiplication.conj_hasDeriv X Y)
  have h2 := LieBracketMultiplication.op_hasDeriv (dOp π X) (dOp π Y)
  have e : (LinearMap.toContinuousLinearMap Λ) ∘
      (fun s : ℝ => NormedSpace.exp ((s : ℂ) • X) * Y * NormedSpace.exp ((s : ℂ) • (-X))) =
      fun s : ℝ => NormedSpace.exp (s • dOp π X) * dOp π Y * NormedSpace.exp (s • (-dOp π X)) := by
    funext s
    have e1 : (s : ℂ) • (-X) = ((-s : ℝ) : ℂ) • X := by
      rw [Complex.ofReal_neg, neg_smul, smul_neg]
    have e2 : s • (-dOp π X) = (-s) • dOp π X := by rw [neg_smul, smul_neg]
    have h3 := hAd W k r z π hπ Y hY _ (exp_uw hX s)
    show Λ (NormedSpace.exp ((s : ℂ) • X) * Y * NormedSpace.exp ((s : ℂ) • (-X))) = _
    rw [e1, ← LieBracketMultiplication.exp_inv, hΛ' _ h3.2.1, h3.2.2, LieBracketMultiplication.exp_inv, hP W k r z π hπ X hX, hP W k r z π hπ X hX, e2,
      mul_assoc]
    rfl
  rw [e] at h1
  have h4 := h1.unique h2
  rw [← hΛ' _ hbr]
  exact h4

end Formalism.FourierDecayAlt.P
