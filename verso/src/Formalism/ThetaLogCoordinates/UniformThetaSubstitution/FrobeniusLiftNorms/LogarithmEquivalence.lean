import Mathlib
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.CyclicPowerClassOfExpEquiv
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.TopsChoicePartA
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.TopsChoicePartB
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.BallRing

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

open Formalism.DworkPowerSeriesWeights (Integral mvExp)

namespace LogarithmEquivalence

noncomputable def ballRing (K : Type) [NormedField K] [IsUltrametricDist K] : Subring K :=
  _root_.UpperTheory.Reformulated.B.ClosedUnitBallSubring.ballRing K

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_ballRing {K : Type} [NormedField K] [IsUltrametricDist K] {x : K} :
    x ∈ ballRing K ↔ ‖x‖ ≤ 1 := Iff.rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h' : ∀ n, MvPowerSeries.coeff n f ∈ ballRing K` using `h`. Set `f₀ : MvPowerSeries ι (ballRing K)` to `fun n => ⟨MvPowerSeries.coeff n f, h' n⟩`. Use `⟨f₀, ?_⟩` and prove the remaining obligations.

Use extensionality with `n`. Conclude with `(MvPowerSeries.coeff_map _ _ _).trans rfl`. Introduce and unpack `⟨f₀, rfl⟩ n`. Rewrite using `[MvPowerSeries.coeff_map]`. Conclude with `(MvPowerSeries.coeff n f₀).2`.
-/
theorem integral_iff_lift {K ι : Type} [NormedField K] [IsUltrametricDist K]
    {f : MvPowerSeries ι K} :
    Integral f ↔ ∃ f₀ : MvPowerSeries ι (ballRing K), MvPowerSeries.map (ballRing K).subtype f₀ = f := by
  constructor
  · intro h
    have h' : ∀ n, MvPowerSeries.coeff n f ∈ ballRing K := h
    let f₀ : MvPowerSeries ι (ballRing K) := fun n => ⟨MvPowerSeries.coeff n f, h' n⟩
    refine ⟨f₀, ?_⟩
    ext n
    exact (MvPowerSeries.coeff_map _ _ _).trans rfl
  · rintro ⟨f₀, rfl⟩ n
    rw [MvPowerSeries.coeff_map]
    exact (MvPowerSeries.coeff n f₀).2

/- English proof (translation)
Take `⟨f₀, rfl⟩` from `integral_iff_lift.1 hf`. Take `⟨g₀, rfl⟩` from `integral_iff_lift.1 hg`. Conclude with `integral_iff_lift.2 ⟨f₀ * g₀, map_mul _ _ _⟩`.
-/
theorem integral_mul' {K ι : Type} [NormedField K] [IsUltrametricDist K] {f g : MvPowerSeries ι K}
    (hf : Integral f) (hg : Integral g) : Integral (f * g) := by
  obtain ⟨f₀, rfl⟩ := integral_iff_lift.1 hf
  obtain ⟨g₀, rfl⟩ := integral_iff_lift.1 hg
  exact integral_iff_lift.2 ⟨f₀ * g₀, map_mul _ _ _⟩

/- English proof (translation)
The claim follows from `integral_iff_lift.2 ⟨1, map_one _⟩`.
-/
theorem integral_one' {K ι : Type} [NormedField K] [IsUltrametricDist K] :
    Integral (1 : MvPowerSeries ι K) :=
  integral_iff_lift.2 ⟨1, map_one _⟩

/- English proof (translation)
Rewrite `h` using `[MvPowerSeries.constantCoeff_map]`. Conclude with `Subtype.ext h`.
-/
theorem constantCoeff_lift {K ι : Type} [NormedField K] [IsUltrametricDist K]
    {f₀ : MvPowerSeries ι (ballRing K)} {c : ballRing K}
    (h : MvPowerSeries.constantCoeff (MvPowerSeries.map (ballRing K).subtype f₀) = c) :
    MvPowerSeries.constantCoeff f₀ = c := by
  rw [MvPowerSeries.constantCoeff_map] at h
  exact Subtype.ext h

/- English proof (translation)
Take `⟨f₀, rfl⟩` from `integral_iff_lift.1 hf`. Use `choose φ₀ hφ₀ using fun i => integral_iff_lift.1 (hφ i)`. Establish `hs : MvPowerSeries.HasSubst φ₀` using `MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => constantCoeff_lift (c := 0) (by rw [hφ₀ i, h0 i]; rfl)`. Use `integral_iff_lift.2 ⟨MvPowerSeries.subst φ₀ f₀, ?_⟩` and prove the remaining obligations. Rewrite using `[MvPowerSeries.map_subst hs]`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Conclude with `hφ₀ i`.
-/
theorem integral_subst' {K ι κ : Type} [Finite ι] [NormedField K] [IsUltrametricDist K]
    {f : MvPowerSeries ι K} {φ : ι → MvPowerSeries κ K}
    (h0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) (hφ : ∀ i, Integral (φ i))
    (hf : Integral f) : Integral (MvPowerSeries.subst φ f) := by
  obtain ⟨f₀, rfl⟩ := integral_iff_lift.1 hf
  choose φ₀ hφ₀ using fun i => integral_iff_lift.1 (hφ i)
  have hs : MvPowerSeries.HasSubst φ₀ := MvPowerSeries.hasSubst_of_constantCoeff_zero fun i =>
    constantCoeff_lift (c := 0) (by rw [hφ₀ i, h0 i]; rfl)
  refine integral_iff_lift.2 ⟨MvPowerSeries.subst φ₀ f₀, ?_⟩
  rw [MvPowerSeries.map_subst hs]
  congr 1
  funext i
  exact hφ₀ i

/- English proof (translation)
Take `⟨u₀, rfl⟩` from `integral_iff_lift.1 hu`. Establish `hc : MvPowerSeries.constantCoeff u₀ = 1` using `constantCoeff_lift (c := 1) (by rw [h1]; rfl)`. Establish `hU : IsUnit u₀` using `MvPowerSeries.isUnit_iff_constantCoeff.2 (by rw [hc]; exact isUnit_one)`. Take `⟨w, hw⟩` from `hU.exists_right_inv`. Establish `e : v = MvPowerSeries.map (ballRing K).subtype w`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e]`. Conclude with `integral_iff_lift.2 ⟨w, rfl⟩`.
-/
theorem integral_of_mul_eq_one {K ι : Type} [NormedField K] [IsUltrametricDist K]
    {u v : MvPowerSeries ι K} (hu : Integral u) (h1 : MvPowerSeries.constantCoeff u = 1)
    (huv : v * u = 1) : Integral v := by
  obtain ⟨u₀, rfl⟩ := integral_iff_lift.1 hu
  have hc : MvPowerSeries.constantCoeff u₀ = 1 := constantCoeff_lift (c := 1) (by rw [h1]; rfl)
  have hU : IsUnit u₀ := MvPowerSeries.isUnit_iff_constantCoeff.2 (by rw [hc]; exact isUnit_one)
  obtain ⟨w, hw⟩ := hU.exists_right_inv
  have e : v = MvPowerSeries.map (ballRing K).subtype w := by
    calc v = v * (MvPowerSeries.map (ballRing K).subtype u₀ *
          MvPowerSeries.map (ballRing K).subtype w) := by rw [← map_mul, hw, map_one, mul_one]
      _ = MvPowerSeries.map (ballRing K).subtype w := by rw [← mul_assoc, huv, one_mul]
  rw [e]
  exact integral_iff_lift.2 ⟨w, rfl⟩

/- English proof (translation)
Use extensionality with `n`. Rewrite using `[coeff_mvExp (map_zero _), Finset.sum_eq_single 0]`. Simplify using the standard rewrite rules. Introduce `k _ hk`. Rewrite using `[zero_pow hk, map_zero, mul_zero]`.

Introduce `h`. Conclude with `absurd (mem_range.2 (Nat.succ_pos _)) h`.
-/
theorem mvExp_zero' {K ι : Type} [NormedField K] [CharZero K] :
    mvExp (0 : MvPowerSeries ι K) = 1 := by
  ext n
  rw [coeff_mvExp (map_zero _), Finset.sum_eq_single 0]
  · simp
  · intro k _ hk
    rw [zero_pow hk, map_zero, mul_zero]
  · intro h
    exact absurd (mem_range.2 (Nat.succ_pos _)) h

/- English proof (translation)
Rewrite using `[← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_mvExp hf]`. Simplify using the standard rewrite rules.
-/
theorem constantCoeff_mvExp' {K ι : Type} [NormedField K] [CharZero K] {f : MvPowerSeries ι K}
    (hf : MvPowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (mvExp f) = 1 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_mvExp hf]
  simp

/- English proof (translation)
Unfold `mvExp`. Rewrite using `[PowerSeries.subst_def, PowerSeries.subst_def, MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero hf).const hs]`.
-/
theorem subst_mvExp' {K ι κ : Type} [NormedField K] [CharZero K] {a : ι → MvPowerSeries κ K}
    (hs : MvPowerSeries.HasSubst a) {f : MvPowerSeries ι K}
    (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.subst a (mvExp f) = mvExp (MvPowerSeries.subst a f) := by
  unfold mvExp
  rw [PowerSeries.subst_def, PowerSeries.subst_def,
    MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero hf).const hs]

/- English proof (translation)
Use `⟨by rw [map_add, ha.1, hb.1, add_zero], ?_⟩` and prove the remaining obligations. Rewrite using `[mvExp_add ha.1 hb.1]`. Conclude with `integral_mul' ha.2 hb.2`.
-/
theorem exp_integral_add {K ι : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]
    {a b : MvPowerSeries ι K}
    (ha : MvPowerSeries.constantCoeff a = 0 ∧ Integral (mvExp a))
    (hb : MvPowerSeries.constantCoeff b = 0 ∧ Integral (mvExp b)) :
    MvPowerSeries.constantCoeff (a + b) = 0 ∧ Integral (mvExp (a + b)) := by
  refine ⟨by rw [map_add, ha.1, hb.1, add_zero], ?_⟩
  rw [mvExp_add ha.1 hb.1]
  exact integral_mul' ha.2 hb.2

/- English proof (translation)
Introduce `K ι _ _ _`. Use `⟨?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `f`. Unfold `Simeq`. Rewrite using `[sub_self, mvExp_zero']`.

Conclude with `⟨map_zero _, integral_one'⟩`. Introduce `f g h`. Unfold `Simeq at h ⊢`. Establish `e : g - f = -(f - g)` using `by ring`. Establish `h0 : MvPowerSeries.constantCoeff (-(f - g)) = 0` using `by rw [map_neg, h.1, neg_zero]`.

Rewrite using `[e]`. Use `⟨h0, integral_of_mul_eq_one h.2 (constantCoeff_mvExp' h.1) ?_⟩` and prove the remaining obligations. Rewrite using `[← mvExp_add h0 h.1, neg_add_cancel, mvExp_zero']`. Introduce `f g h h1 h2`. Unfold `Simeq at h1 h2 ⊢`.

Establish `e : f - h = (f - g) + (g - h)` using `by ring`. Rewrite using `[e]`. Conclude with `exp_integral_add h1 h2`. Introduce `f g f' g' h1 h2`. Unfold `Simeq at h1 h2 ⊢`.

Establish `e : f + f' - (g + g') = (f - g) + (f' - g')` using `by ring`. Rewrite using `[e]`. Conclude with `exp_integral_add h1 h2`. Introduce `κ _ f g φ h0 hφ h`. Unfold `Simeq at h ⊢`.

Establish `hs : MvPowerSeries.HasSubst φ` using `MvPowerSeries.hasSubst_of_constantCoeff_zero h0`. Rewrite using `[← MvPowerSeries.subst_sub hs, ← subst_mvExp' hs h.1]`. Conclude with `⟨MvPowerSeries.constantCoeff_subst_eq_zero hs h0 h.1, integral_subst' h0 hφ h.2⟩`.
-/
theorem simeqRules : SimeqRules := by
  intro K ι _ _ _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro f
    unfold Simeq
    rw [sub_self, mvExp_zero']
    exact ⟨map_zero _, integral_one'⟩
  · intro f g h
    unfold Simeq at h ⊢
    have e : g - f = -(f - g) := by ring
    have h0 : MvPowerSeries.constantCoeff (-(f - g)) = 0 := by rw [map_neg, h.1, neg_zero]
    rw [e]
    refine ⟨h0, integral_of_mul_eq_one h.2 (constantCoeff_mvExp' h.1) ?_⟩
    rw [← mvExp_add h0 h.1, neg_add_cancel, mvExp_zero']
  · intro f g h h1 h2
    unfold Simeq at h1 h2 ⊢
    have e : f - h = (f - g) + (g - h) := by ring
    rw [e]
    exact exp_integral_add h1 h2
  · intro f g f' g' h1 h2
    unfold Simeq at h1 h2 ⊢
    have e : f + f' - (g + g') = (f - g) + (f' - g') := by ring
    rw [e]
    exact exp_integral_add h1 h2
  · intro κ _ f g φ h0 hφ h
    unfold Simeq at h ⊢
    have hs : MvPowerSeries.HasSubst φ := MvPowerSeries.hasSubst_of_constantCoeff_zero h0
    rw [← MvPowerSeries.subst_sub hs, ← subst_mvExp' hs h.1]
    exact ⟨MvPowerSeries.constantCoeff_subst_eq_zero hs h0 h.1, integral_subst' h0 hφ h.2⟩

/- English proof (translation)
Introduce `F L ι _ _ _ _ _ _ _ b σ τ`. Set `A : Matrix ι (L ≃ₐ[F] L) L` to `fun r ρ => ρ ((Algebra.traceForm F L).dualBasis (traceForm_nondegenerate F L) b r)`. Set `B : Matrix (L ≃ₐ[F] L) ι L` to `fun ρ r => ρ (b r)`. Establish `hAB : A * B = 1`. Use extensionality with `r s`.

Rewrite using `[Matrix.mul_apply]`. Establish `e : ∑ ρ : L ≃ₐ[F] L, A r ρ * B ρ s = algebraMap F L (Algebra.trace F L ((Algebra.traceForm F L).dualBasis (traceForm_nondegenerate F L) b r * b s))`. Rewrite using `[trace_eq_sum_automorphisms]`. Conclude with `Finset.sum_congr rfl fun ρ _ => (map_mul ρ _ _).symm`. Rewrite using `[e, ← Algebra.traceForm_apply, LinearMap.BilinForm.apply_dualBasis_left, Matrix.one_apply]`.

Distinguish the cases in `h : r = s`. Rewrite using `[if_pos h, if_pos h.symm, map_one]`. Rewrite using `[if_neg h, if_neg (Ne.symm h), map_zero]`. Establish `e : ι ≃ (L ≃ₐ[F] L)` using `Fintype.equivOfCardEq (by`. Rewrite using `[← Module.finrank_eq_card_basis b, ← IsGalois.card_aut_eq_finrank, Nat.card_eq_fintype_card])`.

Establish `hBA : B * A = 1` using `(Matrix.mul_eq_one_comm_of_equiv e).1 hAB`. Establish `key : ∑ r, σ ((Algebra.traceForm F L).dualBasis (traceForm_nondegenerate F L) b r) * τ (b r) = (1 : Matrix (L ≃ₐ[F] L) (L ≃ₐ[F] L) L) τ σ`. Rewrite using `[← hBA, Matrix.mul_apply]`. Conclude with `Finset.sum_congr rfl fun r _ => mul_comm _ _`. Rewrite using `[key]`.

Conclude with `⟨fun h => by rw [h, Matrix.one_apply_eq], fun h => Matrix.one_apply_ne (Ne.symm h)⟩`.
-/
theorem traceDual : TraceDual := by
  intro F L ι _ _ _ _ _ _ _ b σ τ
  classical
  let A : Matrix ι (L ≃ₐ[F] L) L := fun r ρ =>
    ρ ((Algebra.traceForm F L).dualBasis (traceForm_nondegenerate F L) b r)
  let B : Matrix (L ≃ₐ[F] L) ι L := fun ρ r => ρ (b r)
  have hAB : A * B = 1 := by
    ext r s
    rw [Matrix.mul_apply]
    have e : ∑ ρ : L ≃ₐ[F] L, A r ρ * B ρ s = algebraMap F L (Algebra.trace F L
        ((Algebra.traceForm F L).dualBasis (traceForm_nondegenerate F L) b r * b s)) := by
      rw [trace_eq_sum_automorphisms]
      exact Finset.sum_congr rfl fun ρ _ => (map_mul ρ _ _).symm
    rw [e, ← Algebra.traceForm_apply, LinearMap.BilinForm.apply_dualBasis_left, Matrix.one_apply]
    by_cases h : r = s
    · rw [if_pos h, if_pos h.symm, map_one]
    · rw [if_neg h, if_neg (Ne.symm h), map_zero]
  have e : ι ≃ (L ≃ₐ[F] L) := Fintype.equivOfCardEq (by
    rw [← Module.finrank_eq_card_basis b, ← IsGalois.card_aut_eq_finrank, Nat.card_eq_fintype_card])
  have hBA : B * A = 1 := (Matrix.mul_eq_one_comm_of_equiv e).1 hAB
  have key : ∑ r, σ ((Algebra.traceForm F L).dualBasis (traceForm_nondegenerate F L) b r) * τ (b r) =
      (1 : Matrix (L ≃ₐ[F] L) (L ≃ₐ[F] L) L) τ σ := by
    rw [← hBA, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun r _ => mul_comm _ _
  rw [key]
  exact ⟨fun h => by rw [h, Matrix.one_apply_eq], fun h => Matrix.one_apply_ne (Ne.symm h)⟩

/- English proof (translation)
The claim follows from `PowerSeries.map_subst ha f`.
-/
theorem ps_map_subst {R S : Type} [CommRing R] [CommRing S] (h : R →+* S) {a : PowerSeries R}
    (ha : PowerSeries.HasSubst a) (f : PowerSeries R) :
    PowerSeries.map h (PowerSeries.subst a f : PowerSeries R) =
      (PowerSeries.subst (PowerSeries.map h a) (PowerSeries.map h f) : PowerSeries S) :=
  PowerSeries.map_subst ha f

/- English proof (translation)
Establish `hsP` using `PowerSeries.HasSubst.of_constantCoeff_zero' hP`. Establish `hsμ` using `PowerSeries.HasSubst.of_constantCoeff_zero' hμ`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem right_inv_eq {R : Type} [CommRing R] {P μ Q : PowerSeries R}
    (hP : PowerSeries.constantCoeff P = 0) (hμ : PowerSeries.constantCoeff μ = 0)
    (hQ : (PowerSeries.subst P Q : PowerSeries R) = PowerSeries.X)
    (h : (PowerSeries.subst μ P : PowerSeries R) = PowerSeries.X) : μ = Q := by
  have hsP := PowerSeries.HasSubst.of_constantCoeff_zero' hP
  have hsμ := PowerSeries.HasSubst.of_constantCoeff_zero' hμ
  calc μ = PowerSeries.subst μ (PowerSeries.X : PowerSeries R) := (PowerSeries.subst_X hsμ).symm
    _ = PowerSeries.subst μ (PowerSeries.subst P Q : PowerSeries R) := by rw [hQ]
    _ = PowerSeries.subst (PowerSeries.subst μ P : PowerSeries R) Q :=
        PowerSeries.subst_comp_subst_apply hsP hsμ Q
    _ = PowerSeries.subst (PowerSeries.X : PowerSeries R) Q := by rw [h]
    _ = Q := PowerSeries.X_subst Q

/- English proof (translation)
Unfold `lamF`. Rewrite using `[PowerSeries.coeff_mk]`.
-/
theorem coeff_lamF {K : Type} [Field K] (p : ℕ) (ϖ : K) (n : ℕ) :
    PowerSeries.coeff n (lamF p ϖ) = ϖ ^ (n - 1) * PowerSeries.coeff n (lgF K p) := by
  unfold lamF
  rw [PowerSeries.coeff_mk]

/- English proof (translation)
Unfold `lgF`. Rewrite using `[PowerSeries.coeff_mk]`. Simplify using the standard rewrite rules.
-/
theorem coeff_zero_lgF (K : Type) [Field K] (p : ℕ) : PowerSeries.coeff 0 (lgF K p) = 0 := by
  unfold lgF
  rw [PowerSeries.coeff_mk]
  simp

/- English proof (translation)
Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_lamF, coeff_zero_lgF, mul_zero]`.
-/
theorem constantCoeff_lamF {K : Type} [Field K] (p : ℕ) (ϖ : K) :
    PowerSeries.constantCoeff (lamF p ϖ) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_lamF, coeff_zero_lgF, mul_zero]

/- English proof (translation)
Establish `h` using `coeff_lgF_pow K hp 0`. Rewrite `h` using `[pow_zero, pow_zero, inv_one]`. Rewrite using `[coeff_lamF, h]`. Simplify using the standard rewrite rules.
-/
theorem coeff_one_lamF {K : Type} [Field K] {p : ℕ} (hp : 2 ≤ p) (ϖ : K) :
    PowerSeries.coeff 1 (lamF p ϖ) = 1 := by
  have h := coeff_lgF_pow K hp 0
  rw [pow_zero, pow_zero, inv_one] at h
  rw [coeff_lamF, h]
  simp

/- English proof (translation)
Introduce `K _ p ϖ μ μ' hp _ h0 h0' h h'`. Establish `hc` using `constantCoeff_lamF p ϖ`. Establish `hu : IsUnit (PowerSeries.coeff 1 (lamF p ϖ))`. Rewrite using `[coeff_one_lamF hp]`. Conclude with `isUnit_one`.

Establish `hQ` using `PowerSeries.subst_substInvOfIsUnit_left (lamF p ϖ) hc hu`. Rewrite using `[right_inv_eq hc h0 hQ h, right_inv_eq hc h0' hQ h']`.
-/
theorem logRescaleUnique : LogRescaleUnique := by
  intro K _ p ϖ μ μ' hp _ h0 h0' h h'
  have hc := constantCoeff_lamF p ϖ
  have hu : IsUnit (PowerSeries.coeff 1 (lamF p ϖ)) := by
    rw [coeff_one_lamF hp]
    exact isUnit_one
  have hQ := PowerSeries.subst_substInvOfIsUnit_left (lamF p ϖ) hc hu
  rw [right_inv_eq hc h0 hQ h, right_inv_eq hc h0' hQ h']

/- English proof (translation)
Establish `e : (PowerSeries.C ϖ * PowerSeries.X : PowerSeries K) = ϖ • PowerSeries.X` using `(PowerSeries.smul_eq_C_mul _ _).symm`. Rewrite using `[e, ← PowerSeries.rescale_eq_subst]`. Use extensionality with `n`. Rewrite using `[PowerSeries.coeff_rescale, PowerSeries.coeff_C_mul, coeff_lamF]`. Break down `n with _ | n` into its components or cases.

Rewrite using `[coeff_zero_lgF]`. Simplify using the standard rewrite rules. Rewrite using `[Nat.add_sub_cancel]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem subst_lgF_scale {K : Type} [Field K] (p : ℕ) (ϖ : K) :
    (PowerSeries.subst (PowerSeries.C ϖ * PowerSeries.X : PowerSeries K) (lgF K p) : PowerSeries K) =
      PowerSeries.C ϖ * lamF p ϖ := by
  have e : (PowerSeries.C ϖ * PowerSeries.X : PowerSeries K) = ϖ • PowerSeries.X :=
    (PowerSeries.smul_eq_C_mul _ _).symm
  rw [e, ← PowerSeries.rescale_eq_subst]
  ext n
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_C_mul, coeff_lamF]
  rcases n with _ | n
  · rw [coeff_zero_lgF]
    simp
  · rw [Nat.add_sub_cancel]
    ring

/- English proof (translation)
Take `⟨r, rfl⟩ : ∃ r, q = r + 1` from `⟨q - 1, by omega⟩`. Rewrite using `[Nat.add_sub_cancel]`. Proceed by induction on `j with`. Consider the case `zero => exact ⟨0, by simp, le_refl _, fun h => by omega⟩`. Consider the case `succ j ih`.

Take `⟨g, h1, h2, _⟩` from `ih`. Use `⟨(r + 1) * g + 1, by rw [pow_succ, h1]; ring, by nlinarith, fun h => ?_⟩` and prove the remaining obligations. Establish `hg : 1 ≤ g` using `by omega`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem geom_sum_mul_pred {q : ℕ} (hq : 4 ≤ q) (j : ℕ) :
    ∃ g, q ^ j = (q - 1) * g + 1 ∧ j ≤ g ∧ (2 ≤ j → j + 1 ≤ g) := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  induction j with
  | zero => exact ⟨0, by simp, le_refl _, fun h => by omega⟩
  | succ j ih =>
    obtain ⟨g, h1, h2, _⟩ := ih
    refine ⟨(r + 1) * g + 1, by rw [pow_succ, h1]; ring, by nlinarith, fun h => ?_⟩
    have hg : 1 ≤ g := by omega
    nlinarith

/- English proof (translation)
Establish `hp2` using `hp.two_le`. Establish `hpR : (0 : ℝ) < (p : ℝ)⁻¹` using `inv_pos.2 (by exact_mod_cast hp.pos)`. Establish `hpK : (p : K) ≠ 0`. Introduce `h`. Rewrite `hn` using `[h, norm_zero]`.

Conclude with `absurd hn hpR.ne`. Establish `hq1 : p ^ 2 ≠ 1` using `by nlinarith`. Rewrite using `[map_sub, map_sub, PowerSeries.coeff_X, PowerSeries.coeff_X_pow, coeff_lamF]`. Distinguish the cases in `h : PowerSeries.coeff n (lgF K p) = 0`. Establish `h1 : n ≠ 1`.

Introduce and unpack `rfl`. Establish `h'` using `coeff_lgF_pow K hp2 0`. Rewrite `h'` using `[pow_zero, pow_zero, inv_one, h]`. Conclude with `zero_ne_one h'`. Establish `h2 : n ≠ p ^ 2`.

Introduce and unpack `rfl`. Establish `h'` using `coeff_lgF_pow K hp2 1`. Rewrite `h'` using `[pow_one, h]`. Conclude with `inv_ne_zero (pow_ne_zero 1 hpK) h'.symm`. Rewrite using `[h, if_neg h1, if_neg h2]`.

Simplify using the standard rewrite rules. Take `⟨j, rfl⟩` from `coeff_lgF_ne_zero h`. Rewrite using `[coeff_lgF_pow K hp2 j]`. Break down `j with _ | _ | j` into its components or cases. Rewrite using `[pow_zero, if_pos rfl, if_neg (Ne.symm hq1)]`.

Simplify using the standard rewrite rules. Rewrite using `[zero_add, pow_one, pow_one, hϖ, if_neg hq1, if_pos rfl, mul_inv_cancel₀ hpK]`. Simplify using the standard rewrite rules. Establish `h1 : (p ^ 2) ^ (j + 2) ≠ 1` using `fun h' => absurd (powq_inj hp2 (h'.trans (pow_zero _).symm)) (by omega)`. Establish `h2 : (p ^ 2) ^ (j + 2) ≠ p ^ 2` using `fun h' => absurd (powq_inj hp2 (h'.trans (pow_one _).symm)) (by omega)`.

Take `⟨g, hg, _, hj⟩` from `geom_sum_mul_pred (q := p ^ 2) (by nlinarith) (j + 2)`. Establish `hj'` using `hj (by omega)`. Take `⟨t, rfl⟩ : ∃ t, g = (j + 2) + (t + 1)` from `⟨g - (j + 2) - 1, by omega⟩`. Rewrite using `[if_neg h1, if_neg h2, sub_zero, sub_zero, hg, Nat.add_sub_cancel, pow_mul, hϖ, pow_add, mul_comm ((p : K) ^ (j + 2)), mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hpK), mul_one, norm_pow, hn, pow_succ]`. Conclude with `mul_le_of_le_one_left hpR.le (pow_le_one₀ hpR.le (inv_le_one_of_one_le₀ (by exact_mod_cast hp.one_le)))`.
-/
theorem norm_lamF_sub {K : Type} [NormedField K] [IsUltrametricDist K] {p : ℕ} {ϖ : K}
    (hp : p.Prime) (hn : ‖(p : K)‖ = (p : ℝ)⁻¹) (hϖ : ϖ ^ (p ^ 2 - 1) = (p : K)) (n : ℕ) :
    ‖PowerSeries.coeff n (lamF p ϖ - PowerSeries.X - PowerSeries.X ^ (p ^ 2))‖ ≤ (p : ℝ)⁻¹ := by
  have hp2 := hp.two_le
  have hpR : (0 : ℝ) < (p : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast hp.pos)
  have hpK : (p : K) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hn
    exact absurd hn hpR.ne
  have hq1 : p ^ 2 ≠ 1 := by nlinarith
  rw [map_sub, map_sub, PowerSeries.coeff_X, PowerSeries.coeff_X_pow, coeff_lamF]
  by_cases h : PowerSeries.coeff n (lgF K p) = 0
  · have h1 : n ≠ 1 := by
      rintro rfl
      have h' := coeff_lgF_pow K hp2 0
      rw [pow_zero, pow_zero, inv_one, h] at h'
      exact zero_ne_one h'
    have h2 : n ≠ p ^ 2 := by
      rintro rfl
      have h' := coeff_lgF_pow K hp2 1
      rw [pow_one, h] at h'
      exact inv_ne_zero (pow_ne_zero 1 hpK) h'.symm
    rw [h, if_neg h1, if_neg h2]
    simp
  · obtain ⟨j, rfl⟩ := coeff_lgF_ne_zero h
    rw [coeff_lgF_pow K hp2 j]
    rcases j with _ | _ | j
    · rw [pow_zero, if_pos rfl, if_neg (Ne.symm hq1)]
      simp
    · rw [zero_add, pow_one, pow_one, hϖ, if_neg hq1, if_pos rfl, mul_inv_cancel₀ hpK]
      simp
    · have h1 : (p ^ 2) ^ (j + 2) ≠ 1 := fun h' =>
        absurd (powq_inj hp2 (h'.trans (pow_zero _).symm)) (by omega)
      have h2 : (p ^ 2) ^ (j + 2) ≠ p ^ 2 := fun h' =>
        absurd (powq_inj hp2 (h'.trans (pow_one _).symm)) (by omega)
      obtain ⟨g, hg, _, hj⟩ := geom_sum_mul_pred (q := p ^ 2) (by nlinarith) (j + 2)
      have hj' := hj (by omega)
      obtain ⟨t, rfl⟩ : ∃ t, g = (j + 2) + (t + 1) := ⟨g - (j + 2) - 1, by omega⟩
      rw [if_neg h1, if_neg h2, sub_zero, sub_zero, hg, Nat.add_sub_cancel, pow_mul, hϖ, pow_add,
        mul_comm ((p : K) ^ (j + 2)), mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hpK), mul_one,
        norm_pow, hn, pow_succ]
      exact mul_le_of_le_one_left hpR.le (pow_le_one₀ hpR.le
        (inv_le_one_of_one_le₀ (by exact_mod_cast hp.one_le)))

def altR (R : Type) [CommRing R] (p : ℕ) : PowerSeries R :=
  PowerSeries.mk fun n => ∑ l ∈ range (n + 1), if n = (p ^ 2) ^ l then (-1 : R) ^ l else 0

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem altF_eq_altR (K : Type) [Field K] (p : ℕ) : altF K p = altR K p := rfl

/- English proof (translation)
Use extensionality with `n`. Unfold `altR`. Rewrite using `[PowerSeries.coeff_map, PowerSeries.coeff_mk, PowerSeries.coeff_mk, map_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Use `split_ifs`.

Rewrite using `[map_pow, map_neg, map_one]`. Rewrite using `[map_zero]`.
-/
theorem map_altR {R S : Type} [CommRing R] [CommRing S] (h : R →+* S) (p : ℕ) :
    PowerSeries.map h (altR R p) = altR S p := by
  ext n
  unfold altR
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, PowerSeries.coeff_mk, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs
  · rw [map_pow, map_neg, map_one]
  · rw [map_zero]

/- English proof (translation)
Unfold `altR`. Rewrite using `[PowerSeries.coeff_mk]`. Conclude with `sum_range_ite_unique _ (fun l' => (p ^ 2) ^ l = (p ^ 2) ^ l') _ l (lt_powq hp l) rfl fun l' h => (powq_inj hp h).symm`.
-/
theorem coeff_altR_pow (R : Type) [CommRing R] {p : ℕ} (hp : 2 ≤ p) (l : ℕ) :
    PowerSeries.coeff ((p ^ 2) ^ l) (altR R p) = (-1) ^ l := by
  unfold altR
  rw [PowerSeries.coeff_mk]
  exact sum_range_ite_unique _ (fun l' => (p ^ 2) ^ l = (p ^ 2) ^ l') _ l (lt_powq hp l) rfl
    fun l' h => (powq_inj hp h).symm

/- English proof (translation)
Unfold `altR`. Rewrite using `[PowerSeries.coeff_mk]`. Conclude with `Finset.sum_eq_zero fun l _ => if_neg (h l)`.
-/
theorem coeff_altR_of_not {R : Type} [CommRing R] {p n : ℕ} (h : ∀ l, n ≠ (p ^ 2) ^ l) :
    PowerSeries.coeff n (altR R p) = 0 := by
  unfold altR
  rw [PowerSeries.coeff_mk]
  exact Finset.sum_eq_zero fun l _ => if_neg (h l)

/- English proof (translation)
Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply]`. Conclude with `coeff_altR_of_not fun l => (pow_pos (pow_pos (by omega) 2) l).ne`.
-/
theorem constantCoeff_altR (R : Type) [CommRing R] {p : ℕ} (hp : 2 ≤ p) :
    PowerSeries.constantCoeff (altR R p) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact coeff_altR_of_not fun l => (pow_pos (pow_pos (by omega) 2) l).ne

/- English proof (translation)
Use extensionality with `n`. Rewrite using `[map_add, PowerSeries.coeff_expand, PowerSeries.coeff_X]`. Establish `hq1 : 1 < p ^ 2` using `by nlinarith`. Distinguish the cases in `h : ∃ l, n = (p ^ 2) ^ l`. Take `⟨l, rfl⟩` from `h`.

Break down `l with _ | l` into its components or cases. Rewrite using `[coeff_altR_pow R hp, pow_zero, pow_zero, if_pos rfl, if_neg (fun hd => absurd (Nat.le_of_dvd one_pos hd) (by omega)), add_zero]`. Establish `h1 : (p ^ 2) ^ (l + 1) ≠ 1` using `fun h' => absurd (powq_inj hp (h'.trans (pow_zero _).symm)) (by omega)`. Rewrite using `[coeff_altR_pow R hp, if_pos (Dvd.intro_left _ (pow_succ _ _).symm), if_neg h1, pow_succ (p ^ 2), Nat.mul_div_cancel _ (by omega), coeff_altR_pow R hp]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h' : ∀ l, n ≠ (p ^ 2) ^ l` using `fun l hl => h ⟨l, hl⟩`. Establish `h1 : n ≠ 1` using `by simpa using h' 0`. Rewrite using `[coeff_altR_of_not h', if_neg h1, zero_add]`. Use `split_ifs with hd`. Use `coeff_altR_of_not fun l hl => h' (l + 1) ?_` and prove the remaining obligations.

Rewrite using `[pow_succ, ← hl, Nat.div_mul_cancel hd]`. Both sides reduce to the same expression.
-/
theorem altR_add_expand (R : Type) [CommRing R] {p : ℕ} (hp : 2 ≤ p) (hq : p ^ 2 ≠ 0) :
    altR R p + PowerSeries.expand (p ^ 2) hq (altR R p) = PowerSeries.X := by
  ext n
  rw [map_add, PowerSeries.coeff_expand, PowerSeries.coeff_X]
  have hq1 : 1 < p ^ 2 := by nlinarith
  by_cases h : ∃ l, n = (p ^ 2) ^ l
  · obtain ⟨l, rfl⟩ := h
    rcases l with _ | l
    · rw [coeff_altR_pow R hp, pow_zero, pow_zero, if_pos rfl,
        if_neg (fun hd => absurd (Nat.le_of_dvd one_pos hd) (by omega)), add_zero]
    · have h1 : (p ^ 2) ^ (l + 1) ≠ 1 := fun h' =>
        absurd (powq_inj hp (h'.trans (pow_zero _).symm)) (by omega)
      rw [coeff_altR_pow R hp, if_pos (Dvd.intro_left _ (pow_succ _ _).symm), if_neg h1, pow_succ (p ^ 2),
        Nat.mul_div_cancel _ (by omega), coeff_altR_pow R hp]
      ring
  · have h' : ∀ l, n ≠ (p ^ 2) ^ l := fun l hl => h ⟨l, hl⟩
    have h1 : n ≠ 1 := by simpa using h' 0
    rw [coeff_altR_of_not h', if_neg h1, zero_add]
    split_ifs with hd
    · refine coeff_altR_of_not fun l hl => h' (l + 1) ?_
      rw [pow_succ, ← hl, Nat.div_mul_cancel hd]
    · rfl

/- English proof (translation)
Establish `: ExpChar R p` using `ExpChar.prime hp`. Establish `h` using `MvPowerSeries.map_iterateFrobenius_expand (σ := Unit) p hp.ne_zero (altR R p) 2`. Use `h.symm.trans ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `PowerSeries.map (iterateFrobenius R p 2) (PowerSeries.expand (p ^ 2) hq (altR R p)) = _`. Rewrite using `[PowerSeries.map_expand, map_altR]`.
-/
theorem altR_pow (R : Type) [CommRing R] {p : ℕ} (hp : p.Prime) [CharP R p] (hq : p ^ 2 ≠ 0) :
    altR R p ^ (p ^ 2) = PowerSeries.expand (p ^ 2) hq (altR R p) := by
  have : ExpChar R p := ExpChar.prime hp
  have h := MvPowerSeries.map_iterateFrobenius_expand (σ := Unit) p hp.ne_zero (altR R p) 2
  refine h.symm.trans ?_
  change PowerSeries.map (iterateFrobenius R p 2) (PowerSeries.expand (p ^ 2) hq (altR R p)) = _
  rw [PowerSeries.map_expand, map_altR]

/- English proof (translation)
Establish `hs` using `PowerSeries.HasSubst.of_constantCoeff_zero' (constantCoeff_altR R hp.two_le)`. Establish `hq : p ^ 2 ≠ 0` using `pow_ne_zero 2 hp.ne_zero`. Rewrite using `[PowerSeries.subst_add hs, PowerSeries.subst_pow hs, PowerSeries.subst_X hs, altR_pow R hp hq, altR_add_expand R hp.two_le hq]`.
-/
theorem subst_altR (R : Type) [CommRing R] {p : ℕ} (hp : p.Prime) [CharP R p] :
    (PowerSeries.subst (altR R p) (PowerSeries.X + PowerSeries.X ^ (p ^ 2) : PowerSeries R) :
      PowerSeries R) = PowerSeries.X := by
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero' (constantCoeff_altR R hp.two_le)
  have hq : p ^ 2 ≠ 0 := pow_ne_zero 2 hp.ne_zero
  rw [PowerSeries.subst_add hs, PowerSeries.subst_pow hs, PowerSeries.subst_X hs, altR_pow R hp hq,
    altR_add_expand R hp.two_le hq]

/- English proof (translation)
The claim follows from `map_natCast (ballRing K).subtype p`.
-/
theorem coe_natCast_ball {K : Type} [NormedField K] [IsUltrametricDist K] (p : ℕ) :
    (((p : ballRing K) : ballRing K) : K) = (p : K) := map_natCast (ballRing K).subtype p

/- English proof (translation)
Establish `hpR : (0 : ℝ) < (p : ℝ)⁻¹` using `inv_pos.2 (by exact_mod_cast hp.pos)`. Establish `hpK : (p : K) ≠ 0`. Introduce `h`. Rewrite `hn` using `[h, norm_zero]`. Conclude with `absurd hn hpR.ne`.

Rewrite using `[Ideal.mem_span_singleton']`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, rfl⟩`. Rewrite using `[Subring.coe_mul, coe_natCast_ball, norm_mul, hn]`. Conclude with `mul_le_of_le_one_left hpR.le a.2`.

Introduce `h`. Establish `ha : (x : K) / (p : K) ∈ ballRing K`. Rewrite using `[mem_ballRing, norm_div, hn, div_inv_eq_mul]`. Establish `hp0 : (0 : ℝ) < p` using `by exact_mod_cast hp.pos`. Combine the equalities or inequalities in the displayed calculation.

Use `⟨⟨_, ha⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite using `[Subring.coe_mul, coe_natCast_ball]`. Conclude with `div_mul_cancel₀ _ hpK`.
-/
theorem mem_span_p_iff {K : Type} [NormedField K] [IsUltrametricDist K] {p : ℕ} (hp : p.Prime)
    (hn : ‖(p : K)‖ = (p : ℝ)⁻¹) (x : ballRing K) :
    x ∈ Ideal.span {(p : ballRing K)} ↔ ‖(x : K)‖ ≤ (p : ℝ)⁻¹ := by
  have hpR : (0 : ℝ) < (p : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast hp.pos)
  have hpK : (p : K) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hn
    exact absurd hn hpR.ne
  rw [Ideal.mem_span_singleton']
  constructor
  · rintro ⟨a, rfl⟩
    rw [Subring.coe_mul, coe_natCast_ball, norm_mul, hn]
    exact mul_le_of_le_one_left hpR.le a.2
  · intro h
    have ha : (x : K) / (p : K) ∈ ballRing K := by
      rw [mem_ballRing, norm_div, hn, div_inv_eq_mul]
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
      calc ‖(x : K)‖ * p ≤ (p : ℝ)⁻¹ * p := mul_le_mul_of_nonneg_right h hp0.le
        _ = 1 := inv_mul_cancel₀ hp0.ne'
    refine ⟨⟨_, ha⟩, Subtype.ext ?_⟩
    rw [Subring.coe_mul, coe_natCast_ball]
    exact div_mul_cancel₀ _ hpK

/- English proof (translation)
Establish `hne : Ideal.span {(p : ballRing K)} ≠ ⊤`. Rewrite using `[Ideal.ne_top_iff_one, mem_span_p_iff hp hn]`. Rewrite using `[Subring.coe_one, norm_one, not_le]`. Conclude with `inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)`. Establish `: Nontrivial (ballRing K ⧸ Ideal.span {(p : ballRing K)})` using `Ideal.Quotient.nontrivial_iff.2 hne`.

Rewrite using `[CharP.charP_iff_prime_eq_zero hp, ← map_natCast (Ideal.Quotient.mk _) p, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `Ideal.subset_span rfl`.
-/
theorem charP_quot {K : Type} [NormedField K] [IsUltrametricDist K] {p : ℕ} (hp : p.Prime)
    (hn : ‖(p : K)‖ = (p : ℝ)⁻¹) : CharP (ballRing K ⧸ Ideal.span {(p : ballRing K)}) p := by
  have hne : Ideal.span {(p : ballRing K)} ≠ ⊤ := by
    rw [Ideal.ne_top_iff_one, mem_span_p_iff hp hn]
    rw [Subring.coe_one, norm_one, not_le]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have : Nontrivial (ballRing K ⧸ Ideal.span {(p : ballRing K)}) := Ideal.Quotient.nontrivial_iff.2 hne
  rw [CharP.charP_iff_prime_eq_zero hp, ← map_natCast (Ideal.Quotient.mk _) p,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span rfl

/- English proof (translation)
Rewrite using `[PowerSeries.ext_iff]`. Use `forall_congr' fun n => ?_` and prove the remaining obligations. Rewrite using `[PowerSeries.coeff_map, PowerSeries.coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem, mem_span_p_iff hp hn]`. Both sides reduce to the same expression.
-/
theorem map_mk_eq_zero_iff {K : Type} [NormedField K] [IsUltrametricDist K] {p : ℕ} (hp : p.Prime)
    (hn : ‖(p : K)‖ = (p : ℝ)⁻¹) (f : PowerSeries (ballRing K)) :
    PowerSeries.map (Ideal.Quotient.mk (Ideal.span {(p : ballRing K)})) f = 0 ↔
      ∀ n, ‖PowerSeries.coeff n (PowerSeries.map (ballRing K).subtype f)‖ ≤ (p : ℝ)⁻¹ := by
  rw [PowerSeries.ext_iff]
  refine forall_congr' fun n => ?_
  rw [PowerSeries.coeff_map, PowerSeries.coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem,
    mem_span_p_iff hp hn]
  rfl

/- English proof (translation)
Introduce `K _ _ p ϖ hp hn hϖ`. Establish `hp2` using `hp.two_le`. Establish `hsub` using `norm_lamF_sub hp hn hϖ`. Use `⟨subst_lgF_scale p ϖ, hsub, ?_⟩` and prove the remaining obligations. Establish `hp1 : (p : ℝ)⁻¹ ≤ 1` using `inv_le_one_of_one_le₀ (by exact_mod_cast hp.one_le)`.

Establish `hint : ∀ n, PowerSeries.coeff n (lamF p ϖ) ∈ ballRing K`. Introduce `n`. Establish `e : PowerSeries.coeff n (lamF p ϖ) = PowerSeries.coeff n (lamF p ϖ - PowerSeries.X - PowerSeries.X ^ (p ^ 2)) + ((if n = 1 then 1 else 0) + (if n = p ^ 2 then 1 else 0))`. Rewrite using `[map_sub, map_sub, PowerSeries.coeff_X, PowerSeries.coeff_X_pow]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Apply the tactic sequence `refine Subring.add_mem _ (mem_ballRing.2 ((hsub n).trans hp1)) (Subring.add_mem _ ?_ ?_) <;> split_ifs <;> first | exact Subring.one_mem _ | exact Subring.zero_mem _`. Set `l0 : PowerSeries (ballRing K)` to `PowerSeries.mk fun n => ⟨PowerSeries.coeff n (lamF p ϖ), hint n⟩`. Establish `hl0 : PowerSeries.map (ballRing K).subtype l0 = lamF p ϖ`. Use extensionality with `n`.

Rewrite using `[PowerSeries.coeff_map, PowerSeries.coeff_mk]`. Both sides reduce to the same expression. Establish `hc0 : PowerSeries.constantCoeff l0 = 0`. Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]`. Use `Subtype.ext ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `PowerSeries.coeff 0 (lamF p ϖ) = 0`. Rewrite using `[PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_lamF]`. Establish `hu0 : IsUnit (PowerSeries.coeff 1 l0)`. Establish `: PowerSeries.coeff 1 l0 = 1`. Rewrite using `[PowerSeries.coeff_mk]`.

Conclude with `Subtype.ext (coeff_one_lamF hp2 ϖ)`. Rewrite using `[this]`. Conclude with `isUnit_one`. Establish `hm0 : PowerSeries.constantCoeff (l0.substInvOfIsUnit hu0) = 0` using `PowerSeries.constantCoeff_substInvOfIsUnit l0 hu0`. Establish `hR` using `PowerSeries.subst_substInvOfIsUnit_right l0 hc0 hu0`.

Establish `hL` using `PowerSeries.subst_substInvOfIsUnit_left l0 hc0 hu0`. Establish `hsm` using `PowerSeries.HasSubst.of_constantCoeff_zero' hm0`. Establish `hsl` using `PowerSeries.HasSubst.of_constantCoeff_zero' hc0`. Use `⟨PowerSeries.map (ballRing K).subtype (l0.substInvOfIsUnit hu0), ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply, hm0, map_zero]`.

Introduce `n`. Rewrite using `[PowerSeries.coeff_map]`. Conclude with `(PowerSeries.coeff n (l0.substInvOfIsUnit hu0)).2`. Rewrite using `[← hl0, ← ps_map_subst _ hsm, hR, PowerSeries.map_X]`. Rewrite using `[← hl0, ← ps_map_subst _ hsl, hL, PowerSeries.map_X]`.

Use `charP_quot hp hn` as an intermediate fact. Establish `e1 : PowerSeries.map (Ideal.Quotient.mk (Ideal.span {(p : ballRing K)})) l0 = PowerSeries.X + PowerSeries.X ^ (p ^ 2)`. Establish `h` using `(map_mk_eq_zero_iff hp hn (l0 - PowerSeries.X - PowerSeries.X ^ (p ^ 2))).2 (by`. Rewrite using `[map_sub, map_sub, map_pow, PowerSeries.map_X, hl0]`. Conclude with `hsub)`.

Rewrite `h` using `[map_sub, map_sub, map_pow, PowerSeries.map_X]`. Take the linear combination `h`. Establish `hL'` using `congrArg (PowerSeries.map (Ideal.Quotient.mk (Ideal.span {(p : ballRing K)}))) hL`. Rewrite `hL'` using `[ps_map_subst _ hsl, PowerSeries.map_X, e1]`. Establish `key` using `right_inv_eq (by simp [hp.ne_zero]) (constantCoeff_altR _ hp2) hL' (subst_altR (ballRing K ⧸ Ideal.span {(p : ballRing K)}) hp)`.

Establish `h` using `(map_mk_eq_zero_iff hp hn (l0.substInvOfIsUnit hu0 - altR (ballRing K) p)).1 (by`. Rewrite using `[map_sub, map_altR, key, sub_self])`. Rewrite `h` using `[map_sub, map_altR]`. Conclude with `h`.
-/
theorem logRescale : LogRescale := by
  intro K _ _ p ϖ hp hn hϖ
  have hp2 := hp.two_le
  have hsub := norm_lamF_sub hp hn hϖ
  refine ⟨subst_lgF_scale p ϖ, hsub, ?_⟩
  have hp1 : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hp.one_le)

  have hint : ∀ n, PowerSeries.coeff n (lamF p ϖ) ∈ ballRing K := by
    intro n
    have e : PowerSeries.coeff n (lamF p ϖ) =
        PowerSeries.coeff n (lamF p ϖ - PowerSeries.X - PowerSeries.X ^ (p ^ 2)) +
          ((if n = 1 then 1 else 0) + (if n = p ^ 2 then 1 else 0)) := by
      rw [map_sub, map_sub, PowerSeries.coeff_X, PowerSeries.coeff_X_pow]
      ring
    rw [e]
    refine Subring.add_mem _ (mem_ballRing.2 ((hsub n).trans hp1)) (Subring.add_mem _ ?_ ?_) <;>
      split_ifs <;> first | exact Subring.one_mem _ | exact Subring.zero_mem _
  let l0 : PowerSeries (ballRing K) := PowerSeries.mk fun n => ⟨PowerSeries.coeff n (lamF p ϖ), hint n⟩
  have hl0 : PowerSeries.map (ballRing K).subtype l0 = lamF p ϖ := by
    ext n
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mk]
    rfl
  have hc0 : PowerSeries.constantCoeff l0 = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
    refine Subtype.ext ?_
    change PowerSeries.coeff 0 (lamF p ϖ) = 0
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_lamF]
  have hu0 : IsUnit (PowerSeries.coeff 1 l0) := by
    have : PowerSeries.coeff 1 l0 = 1 := by
      rw [PowerSeries.coeff_mk]
      exact Subtype.ext (coeff_one_lamF hp2 ϖ)
    rw [this]
    exact isUnit_one
  have hm0 : PowerSeries.constantCoeff (l0.substInvOfIsUnit hu0) = 0 :=
    PowerSeries.constantCoeff_substInvOfIsUnit l0 hu0
  have hR := PowerSeries.subst_substInvOfIsUnit_right l0 hc0 hu0
  have hL := PowerSeries.subst_substInvOfIsUnit_left l0 hc0 hu0
  have hsm := PowerSeries.HasSubst.of_constantCoeff_zero' hm0
  have hsl := PowerSeries.HasSubst.of_constantCoeff_zero' hc0
  refine ⟨PowerSeries.map (ballRing K).subtype (l0.substInvOfIsUnit hu0), ?_, ?_, ?_, ?_, ?_⟩
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hm0, map_zero]
  · intro n
    rw [PowerSeries.coeff_map]
    exact (PowerSeries.coeff n (l0.substInvOfIsUnit hu0)).2
  · rw [← hl0, ← ps_map_subst _ hsm, hR, PowerSeries.map_X]
  · rw [← hl0, ← ps_map_subst _ hsl, hL, PowerSeries.map_X]
  ·
    have := charP_quot hp hn
    have e1 : PowerSeries.map (Ideal.Quotient.mk (Ideal.span {(p : ballRing K)})) l0 =
        PowerSeries.X + PowerSeries.X ^ (p ^ 2) := by
      have h := (map_mk_eq_zero_iff hp hn (l0 - PowerSeries.X - PowerSeries.X ^ (p ^ 2))).2 (by
        rw [map_sub, map_sub, map_pow, PowerSeries.map_X, hl0]
        exact hsub)
      rw [map_sub, map_sub, map_pow, PowerSeries.map_X] at h
      linear_combination h
    have hL' := congrArg (PowerSeries.map (Ideal.Quotient.mk (Ideal.span {(p : ballRing K)}))) hL
    rw [ps_map_subst _ hsl, PowerSeries.map_X, e1] at hL'
    have key := right_inv_eq (by simp [hp.ne_zero]) (constantCoeff_altR _ hp2) hL'
      (subst_altR (ballRing K ⧸ Ideal.span {(p : ballRing K)}) hp)
    have h := (map_mk_eq_zero_iff hp hn (l0.substInvOfIsUnit hu0 - altR (ballRing K) p)).1 (by
      rw [map_sub, map_altR, key, sub_self])
    rw [map_sub, map_altR] at h
    exact h

end LogarithmEquivalence

/- English proof (translation)
The claim follows from `LogarithmEquivalence.simeqRules`.
-/
theorem equivalence_rules : SimeqRules := LogarithmEquivalence.simeqRules

/- English proof (translation)
The claim follows from `LogarithmEquivalence.logRescale`.
-/
theorem log_rescale_alt : LogRescale := LogarithmEquivalence.logRescale

/- English proof (translation)
The claim follows from `LogarithmEquivalence.logRescaleUnique`.
-/
theorem log_rescale_unique : LogRescaleUnique := LogarithmEquivalence.logRescaleUnique

/- English proof (translation)
The claim follows from `LogarithmEquivalence.traceDual`.
-/
theorem trace_duality : TraceDual := LogarithmEquivalence.traceDual

end Formalism.InvariantFactorPaths.G7
