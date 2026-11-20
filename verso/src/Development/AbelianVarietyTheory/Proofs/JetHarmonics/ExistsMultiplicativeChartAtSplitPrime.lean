import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFormalGroupAdd
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HeightOneOfSplit
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpBinomialPowerSubOneSeriesIntegralityCompositio
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsIsoGmOfMap

noncomputable section

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.SplitChart

open ChordLaw

section Algebra

variable {k : Type} [CommRing k] {σ : Type}

/- English proof (translation)
Establish `hab` using `hasSubst_two ha hb`. Establish `c0 : ∀ i, MvPowerSeries.constantCoeff (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) k) U) = 0` using `fun i => PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X i) _ hU`. Establish `h` using `congrArg (MvPowerSeries.subst ![a, b]) H`. Rewrite `h` using `[MvPowerSeries.subst_comp_subst_apply (hasSubst_two (c0 0) (c0 1)) hab, subst_psubst hab (by simp), MvPowerSeries.subst_add hab, MvPowerSeries.subst_X hab, MvPowerSeries.subst_X hab]`. Use `Eq.trans ?_ h` and prove the remaining obligations.

Use `congr 1`. Use function extensionality and compare the values at `i`. Use `fin_cases i`. Simplify using `[subst_psubst hab (MvPowerSeries.constantCoeff_X 0), MvPowerSeries.subst_X hab]`. Simplify using `[subst_psubst hab (MvPowerSeries.constantCoeff_X 1), MvPowerSeries.subst_X hab]`.
-/
theorem law_two {U : k⟦X⟧} (hU : constantCoeff U = 0) {F : MvPowerSeries (Fin 2) k}
    (H : MvPowerSeries.subst (![PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) U,
      PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k) U] : Fin 2 → MvPowerSeries (Fin 2) k) F =
      PowerSeries.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k) U)
    {a b : MvPowerSeries σ k} (ha : MvPowerSeries.constantCoeff a = 0) (hb : MvPowerSeries.constantCoeff b = 0) :
    MvPowerSeries.subst (![PowerSeries.subst a U, PowerSeries.subst b U] : Fin 2 → MvPowerSeries σ k) F =
      PowerSeries.subst (a + b) U := by
  have hab := hasSubst_two ha hb
  have c0 : ∀ i, MvPowerSeries.constantCoeff (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) k) U) = 0 :=
    fun i => PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X i) _ hU
  have h := congrArg (MvPowerSeries.subst ![a, b]) H
  rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_two (c0 0) (c0 1)) hab, subst_psubst hab (by simp),
    MvPowerSeries.subst_add hab, MvPowerSeries.subst_X hab, MvPowerSeries.subst_X hab] at h
  refine Eq.trans ?_ h
  congr 1
  funext i
  fin_cases i
  · simp [subst_psubst hab (MvPowerSeries.constantCoeff_X 0), MvPowerSeries.subst_X hab]
  · simp [subst_psubst hab (MvPowerSeries.constantCoeff_X 1), MvPowerSeries.subst_X hab]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp [JetMomFound.mulN]`. Consider the case `succ n ih`. Use `MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst_two ih constantCoeff_X) ?_ F.zero_constantCoeff` and prove the remaining obligations. Introduce `i`.

Use `fin_cases i`. Conclude with `ih`. Conclude with `constantCoeff_X`.
-/
theorem constantCoeff_mulN {R : Type} [CommRing R] (F : FormalGroup R) (n : ℕ) :
    constantCoeff (JetMomFound.mulN F n) = 0 := by
  induction n with
  | zero => simp [JetMomFound.mulN]
  | succ n ih =>
    refine MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst_two ih constantCoeff_X) ?_ F.zero_constantCoeff
    intro i
    fin_cases i
    · exact ih
    · exact constantCoeff_X

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Simplify using `only [JetMomFound.mulN, map_zero, Nat.cast_zero, zero_mul]`. Conclude with `(PowerSeries.subst_zero_of_constantCoeff_zero hU).symm`. Consider the case `succ n ih`.

Establish `h` using `law_two hU H (a := (C (n : k) * ℓ : k⟦X⟧)) (b := ℓ) (show constantCoeff (C (n : k) * ℓ) = 0 by rw [map_mul, hℓ, mul_zero]) hℓ`. Establish `e : (C ((n + 1 : ℕ) : k) * ℓ : k⟦X⟧) = C (n : k) * ℓ + ℓ`. Rewrite using `[Nat.cast_succ, map_add, map_one]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Use `Eq.trans ?_ h` and prove the remaining obligations. Rewrite using `[← ih, hUℓ]`. Use `(MvPowerSeries.map_subst (hasSubst_two (constantCoeff_mulN F n) constantCoeff_X) _).trans ?_` and prove the remaining obligations. Use `congr 1`. Use function extensionality and compare the values at `i`.

Use `fin_cases i`. Both sides reduce to the same expression. Conclude with `PowerSeries.map_X φ`.
-/
theorem map_mulN {R : Type} [CommRing R] (φ : R →+* k) (F : FormalGroup R) {U ℓ : k⟦X⟧}
    (hU : constantCoeff U = 0) (hℓ : constantCoeff ℓ = 0) (hUℓ : PowerSeries.subst ℓ U = (X : k⟦X⟧))
    (H : MvPowerSeries.subst (![PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) U,
      PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k) U] : Fin 2 → MvPowerSeries (Fin 2) k)
      (MvPowerSeries.map φ F.toPowerSeries) =
      PowerSeries.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k) U) (n : ℕ) :
    PowerSeries.map φ (JetMomFound.mulN F n) = PowerSeries.subst (C (n : k) * ℓ) U := by
  induction n with
  | zero =>
    simp only [JetMomFound.mulN, map_zero, Nat.cast_zero, zero_mul]
    exact (PowerSeries.subst_zero_of_constantCoeff_zero hU).symm
  | succ n ih =>
    have h := law_two hU H (a := (C (n : k) * ℓ : k⟦X⟧)) (b := ℓ)
      (show constantCoeff (C (n : k) * ℓ) = 0 by rw [map_mul, hℓ, mul_zero]) hℓ
    have e : (C ((n + 1 : ℕ) : k) * ℓ : k⟦X⟧) = C (n : k) * ℓ + ℓ := by
      rw [Nat.cast_succ, map_add, map_one]; ring
    rw [e]
    refine Eq.trans ?_ h
    rw [← ih, hUℓ]
    refine (MvPowerSeries.map_subst (hasSubst_two (constantCoeff_mulN F n) constantCoeff_X) _).trans ?_
    congr 1
    funext i
    fin_cases i
    · rfl
    · exact PowerSeries.map_X φ

/- English proof (translation)
Establish `HX : ∀ i, PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 2) k)` using `fun i => PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)`. Establish `HS : PowerSeries.HasSubst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k)` using `PowerSeries.HasSubst.of_constantCoeff_zero (by simp)`. Establish `h` using `congrArg (MvPowerSeries.pderiv k 1) H`. Simplify using `only [map_add, Derivation.leibniz, smul_eq_mul, GlobalTheory.FormalCalc.pderiv_powerSeries_subst (HX _), GlobalTheory.FormalCalc.pderiv_powerSeries_subst HS] at h`. Establish `p0 : MvPowerSeries.pderiv k 1 (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) = 0`.

Simplify using `[MvPowerSeries.pderiv_X_of_ne]`. Establish `p1 : MvPowerSeries.pderiv k 1 (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k) = 1` using `by simp`. Simplify using `only [p0, p1, zero_add, mul_one, mul_zero, add_zero] at h`. Establish `ha : MvPowerSeries.HasSubst (![(X : k⟦X⟧), 0] : Fin 2 → MvPowerSeries Unit k)` using `hasSubst_two constantCoeff_X (map_zero _)`. Establish `h2` using `congrArg (MvPowerSeries.subst (![(X : k⟦X⟧), 0] : Fin 2 → MvPowerSeries Unit k)) h`.

Rewrite `h2` using `[subst_psubst ha (by simp), MvPowerSeries.subst_add ha, MvPowerSeries.subst_add ha, MvPowerSeries.subst_mul ha, subst_psubst ha (MvPowerSeries.constantCoeff_X 0), subst_psubst ha (MvPowerSeries.constantCoeff_X 1), MvPowerSeries.subst_X ha, MvPowerSeries.subst_X ha]`. Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one, add_zero] at h2`. Establish `e : PowerSeries.subst (0 : MvPowerSeries Unit k) (derivative k g) = (C (coeff 1 g) : k⟦X⟧)`. Rewrite using `[PowerSeries.subst_zero_eq_C_constantCoeff, MvPowerSeries.map_C, ← coeff_zero_eq_constantCoeff_apply, coeff_derivative]`. Simplify using `[PowerSeries.C]`.

Rewrite `h2` using `[X_subst, X_subst, e]`. Rewrite using `[h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem deriv_of_mul {g : k⟦X⟧}
    (H : PowerSeries.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k) g =
      PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) g +
      PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k) g +
      PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) g *
      PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k) g) :
    derivative k g = C (coeff 1 g) * (1 + g) := by
  have HX : ∀ i, PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 2) k) := fun i =>
    PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)
  have HS : PowerSeries.HasSubst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  have h := congrArg (MvPowerSeries.pderiv k 1) H
  simp only [map_add, Derivation.leibniz, smul_eq_mul, GlobalTheory.FormalCalc.pderiv_powerSeries_subst (HX _),
    GlobalTheory.FormalCalc.pderiv_powerSeries_subst HS] at h
  have p0 : MvPowerSeries.pderiv k 1 (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) = 0 := by
    simp [MvPowerSeries.pderiv_X_of_ne]
  have p1 : MvPowerSeries.pderiv k 1 (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k) = 1 := by simp
  simp only [p0, p1, zero_add, mul_one, mul_zero, add_zero] at h
  have ha : MvPowerSeries.HasSubst (![(X : k⟦X⟧), 0] : Fin 2 → MvPowerSeries Unit k) :=
    hasSubst_two constantCoeff_X (map_zero _)
  have h2 := congrArg (MvPowerSeries.subst (![(X : k⟦X⟧), 0] : Fin 2 → MvPowerSeries Unit k)) h
  rw [subst_psubst ha (by simp), MvPowerSeries.subst_add ha, MvPowerSeries.subst_add ha,
    MvPowerSeries.subst_mul ha, subst_psubst ha (MvPowerSeries.constantCoeff_X 0),
    subst_psubst ha (MvPowerSeries.constantCoeff_X 1), MvPowerSeries.subst_X ha, MvPowerSeries.subst_X ha] at h2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, add_zero] at h2
  have e : PowerSeries.subst (0 : MvPowerSeries Unit k) (derivative k g) = (C (coeff 1 g) : k⟦X⟧) := by
    rw [PowerSeries.subst_zero_eq_C_constantCoeff, MvPowerSeries.map_C, ← coeff_zero_eq_constantCoeff_apply,
      coeff_derivative]
    simp [PowerSeries.C]
  rw [X_subst, X_subst, e] at h2
  rw [h2]
  ring

/- English proof (translation)
Establish `h0 : constantCoeff (C ω * L) = 0` using `by rw [map_mul, hL0, mul_zero]`. Establish `Hs` using `PowerSeries.HasSubst.of_constantCoeff_zero' h0`. Establish `hh0 : constantCoeff (PowerSeries.subst (C ω * L) g : k⟦X⟧) = 0` using `PowerSeries.constantCoeff_subst_eq_zero h0 _ hg`. Establish `hD : derivative k (PowerSeries.subst (C ω * L) g : k⟦X⟧) = C γ * (1 + PowerSeries.subst (C ω * L) g) * (C ω * derivative k L)`. Rewrite using `[PowerSeries.derivative_subst Hs, hd, PowerSeries.subst_mul Hs, PowerSeries.subst_add Hs, PowerSeries.subst_C, ← PowerSeries.coe_substAlgHom Hs, map_one, Derivation.leibniz, derivative_C]`.

Simplify using `only [smul_eq_mul, mul_zero, add_zero]`. Both sides reduce to the same expression. Generalize the expression as in `(PowerSeries.subst (C ω * L) g : k⟦X⟧) = h at hh0 hD`. Establish `hC : (C γ : k⟦X⟧) * C ω = 1` using `by rw [← map_mul, hγ, map_one]`. Use `set r := derivative k L with hr`.

Establish `hr'` using `congrArg (derivative k) hL`. Rewrite `hr'` using `[Derivation.leibniz, map_add, derivative_X, Derivation.map_one_eq_zero]`. Simplify using `only [smul_eq_mul] at hr'`. Establish `hr0 : constantCoeff r = 1` using `by simpa using congrArg constantCoeff hL`. Establish `key : (1 + h) * r = 1`.

Apply `derivative.ext` to reduce the goal to its premises. Rewrite using `[Derivation.leibniz, map_add, Derivation.map_one_eq_zero, hD]`. Simplify using `only [smul_eq_mul]`. Take the linear combination `(1 + h) * r * hr' - (1 + h) * derivative k r * hL + (1 + h) * r ^ 2 * hC`. Simplify using `[hh0, hr0]`.

Take the linear combination `(1 + X) * key - (1 + h) * hL`.
-/
theorem subst_log_eq_X [IsAddTorsionFree k] {g L : k⟦X⟧} {γ ω : k} (hγ : γ * ω = 1) (hg : constantCoeff g = 0)
    (hd : derivative k g = C γ * (1 + g)) (hL0 : constantCoeff L = 0) (hL : (1 + X) * derivative k L = 1) :
    PowerSeries.subst (C ω * L) g = (X : k⟦X⟧) := by
  have h0 : constantCoeff (C ω * L) = 0 := by rw [map_mul, hL0, mul_zero]
  have Hs := PowerSeries.HasSubst.of_constantCoeff_zero' h0
  have hh0 : constantCoeff (PowerSeries.subst (C ω * L) g : k⟦X⟧) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero h0 _ hg
  have hD : derivative k (PowerSeries.subst (C ω * L) g : k⟦X⟧) =
      C γ * (1 + PowerSeries.subst (C ω * L) g) * (C ω * derivative k L) := by
    rw [PowerSeries.derivative_subst Hs, hd, PowerSeries.subst_mul Hs, PowerSeries.subst_add Hs,
      PowerSeries.subst_C, ← PowerSeries.coe_substAlgHom Hs, map_one, Derivation.leibniz, derivative_C]
    simp only [smul_eq_mul, mul_zero, add_zero]
    rfl
  generalize (PowerSeries.subst (C ω * L) g : k⟦X⟧) = h at hh0 hD
  have hC : (C γ : k⟦X⟧) * C ω = 1 := by rw [← map_mul, hγ, map_one]
  set r := derivative k L with hr
  have hr' := congrArg (derivative k) hL
  rw [Derivation.leibniz, map_add, derivative_X, Derivation.map_one_eq_zero] at hr'
  simp only [smul_eq_mul] at hr'
  have hr0 : constantCoeff r = 1 := by simpa using congrArg constantCoeff hL
  have key : (1 + h) * r = 1 := by
    apply derivative.ext
    · rw [Derivation.leibniz, map_add, Derivation.map_one_eq_zero, hD]
      simp only [smul_eq_mul]
      linear_combination (1 + h) * r * hr' - (1 + h) * derivative k r * hL + (1 + h) * r ^ 2 * hC
    · simp [hh0, hr0]
  linear_combination (1 + X) * key - (1 + h) * hL

/- English proof (translation)
Take `⟨f0, f1, hf⟩` from `hf`. Establish `HX : ∀ i, PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 2) R)` using `fun i => PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)`. Establish `c0 : ∀ i, MvPowerSeries.constantCoeff (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) f) = 0` using `fun i => PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X i) _ f0`. Establish `cU : ∀ i, MvPowerSeries.constantCoeff (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) U) = 0` using `fun i => PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X i) _ hU`. Establish `ha` using `hasSubst_two (c0 0) (c0 1)`.

Establish `hb` using `hasSubst_two (cU 0) (cU 1)`. Rewrite `hf` using `[FormalGroup.𝔾ₘ_toPowerSeries, MvPowerSeries.subst_add ha, MvPowerSeries.subst_add ha, MvPowerSeries.subst_mul ha, MvPowerSeries.subst_X ha, MvPowerSeries.subst_X ha]`. Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one] at hf`. Establish `h1` using `congrArg (MvPowerSeries.map φ) hf`. Rewrite `h1` using `[map_add, map_add, map_mul, PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff), PowerSeries.map_subst (HX 0), PowerSeries.map_subst (HX 1), MvPowerSeries.map_X, MvPowerSeries.map_X]`.

Use `set f' := PowerSeries.map φ f with hf'`. Establish `f0' : constantCoeff f' = 0`. Rewrite using `[hf', ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, f0, map_zero]`. Establish `h2` using `congrArg (MvPowerSeries.subst (![PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) U, PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) U] : Fin 2 → MvPowerSeries (Fin 2) K)) h1`. Rewrite `h2` using `[subst_psubst hb (by rw [MvPowerSeries.constantCoeff_map, F.zero_constantCoeff, map_zero]), H, MvPowerSeries.subst_add hb, MvPowerSeries.subst_add hb, MvPowerSeries.subst_mul hb, subst_psubst hb (MvPowerSeries.constantCoeff_X 0), subst_psubst hb (MvPowerSeries.constantCoeff_X 1), …`.

Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one] at h2`. Rewrite `h2` using `[← psubst_psubst (by simp) hU, ← psubst_psubst (MvPowerSeries.constantCoeff_X 0) hU, ← psubst_psubst (MvPowerSeries.constantCoeff_X 1) hU]`. Establish `hd` using `deriv_of_mul h2`. Establish `g0 : constantCoeff (PowerSeries.subst U f' : K⟦X⟧) = 0` using `PowerSeries.constantCoeff_subst_eq_zero hU _ f0'`. Establish `hγ : coeff 1 (PowerSeries.subst U f' : K⟦X⟧) ≠ 0`.

Introduce `hz`. Establish `hg : (PowerSeries.subst U f' : K⟦X⟧) = 0`. Apply `derivative.ext` to reduce the goal to its premises. Rewrite using `[hd, hz]`. Simplify using the standard rewrite rules.

Rewrite using `[g0, map_zero]`. Establish `h3` using `psubst_psubst (σ := Unit) hℓ hU f'`. Rewrite `h3` using `[hg, hUℓ, X_subst, ← PowerSeries.coe_substAlgHom (PowerSeries.HasSubst.of_constantCoeff_zero' hℓ), map_zero]`. Establish `h4` using `f1.map φ`. Rewrite `h4` using `[← coeff_map, ← hf', ← h3, map_zero]`.

Conclude with `not_isUnit_zero h4`. Establish `h5` using `subst_log_eq_X (mul_inv_cancel₀ hγ) g0 hd hL0 hL`. Use `set ω := (coeff 1 (PowerSeries.subst U f' : K⟦X⟧))⁻¹`. Establish `h0 : constantCoeff (C ω * L) = 0` using `by rw [map_mul, hL0, mul_zero]`. Rewrite `h5` using `[psubst_psubst (σ := Unit) h0 hU]`.

Establish `u0 : constantCoeff (PowerSeries.subst (C ω * L) U : K⟦X⟧) = 0` using `PowerSeries.constantCoeff_subst_eq_zero h0 _ hU`. Use `⟨ω, f.substInvOfIsUnit f1, by rw [coeff_one_substInvOfIsUnit]; exact Units.isUnit _, ?_⟩` and prove the remaining obligations. Establish `h6` using `congrArg (MvPowerSeries.map φ) (subst_substInvOfIsUnit_left f f0 f1)`. Rewrite `h6` using `[PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' f0)]`. Establish `h7 : PowerSeries.subst f' (PowerSeries.map φ (f.substInvOfIsUnit f1)) = (X : K⟦X⟧)` using `h6.trans (PowerSeries.map_X φ)`.

Establish `h8` using `psubst_psubst (σ := Unit) u0 f0' (PowerSeries.map φ (f.substInvOfIsUnit f1))`. Rewrite `h8` using `[h7, h5, X_subst, PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero' u0)]`. Conclude with `h8`.
-/
theorem exists_scale {R K : Type} [CommRing R] [Field K] [CharZero K] (φ : R →+* K) (F : FormalGroup R)
    {U ℓ L : K⟦X⟧} (hU : constantCoeff U = 0) (hℓ : constantCoeff ℓ = 0)
    (hUℓ : PowerSeries.subst ℓ U = (X : K⟦X⟧))
    (H : MvPowerSeries.subst (![PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) U,
      PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) U] : Fin 2 → MvPowerSeries (Fin 2) K)
      (MvPowerSeries.map φ F.toPowerSeries) =
      PowerSeries.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) U)
    {f : R⟦X⟧} (hf : JetMomFound.IsIsoGm F f) (hL0 : constantCoeff L = 0) (hL : (1 + X) * derivative K L = 1) :
    ∃ (ω : K) (e : R⟦X⟧), IsUnit (coeff 1 e) ∧ PowerSeries.subst (C ω * L) U = PowerSeries.map φ e := by
  obtain ⟨f0, f1, hf⟩ := hf
  have HX : ∀ i, PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) := fun i =>
    PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)
  have c0 : ∀ i, MvPowerSeries.constantCoeff (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) f) = 0 :=
    fun i => PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X i) _ f0
  have cU : ∀ i, MvPowerSeries.constantCoeff (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) U) = 0 :=
    fun i => PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X i) _ hU
  have ha := hasSubst_two (c0 0) (c0 1)
  have hb := hasSubst_two (cU 0) (cU 1)
  rw [FormalGroup.𝔾ₘ_toPowerSeries, MvPowerSeries.subst_add ha, MvPowerSeries.subst_add ha,
    MvPowerSeries.subst_mul ha, MvPowerSeries.subst_X ha, MvPowerSeries.subst_X ha] at hf
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hf
  have h1 := congrArg (MvPowerSeries.map φ) hf
  rw [map_add, map_add, map_mul,
    PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff),
    PowerSeries.map_subst (HX 0), PowerSeries.map_subst (HX 1), MvPowerSeries.map_X, MvPowerSeries.map_X] at h1
  set f' := PowerSeries.map φ f with hf'
  have f0' : constantCoeff f' = 0 := by
    rw [hf', ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, f0, map_zero]
  have h2 := congrArg (MvPowerSeries.subst (![PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) U,
      PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) U] : Fin 2 → MvPowerSeries (Fin 2) K)) h1
  rw [subst_psubst hb (by rw [MvPowerSeries.constantCoeff_map, F.zero_constantCoeff, map_zero]), H,
    MvPowerSeries.subst_add hb, MvPowerSeries.subst_add hb, MvPowerSeries.subst_mul hb,
    subst_psubst hb (MvPowerSeries.constantCoeff_X 0), subst_psubst hb (MvPowerSeries.constantCoeff_X 1),
    MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb] at h2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h2
  rw [← psubst_psubst (by simp) hU, ← psubst_psubst (MvPowerSeries.constantCoeff_X 0) hU,
    ← psubst_psubst (MvPowerSeries.constantCoeff_X 1) hU] at h2
  have hd := deriv_of_mul h2
  have g0 : constantCoeff (PowerSeries.subst U f' : K⟦X⟧) = 0 := PowerSeries.constantCoeff_subst_eq_zero hU _ f0'
  have hγ : coeff 1 (PowerSeries.subst U f' : K⟦X⟧) ≠ 0 := by
    intro hz
    have hg : (PowerSeries.subst U f' : K⟦X⟧) = 0 := by
      apply derivative.ext
      · rw [hd, hz]; simp
      · rw [g0, map_zero]
    have h3 := psubst_psubst (σ := Unit) hℓ hU f'
    rw [hg, hUℓ, X_subst, ← PowerSeries.coe_substAlgHom (PowerSeries.HasSubst.of_constantCoeff_zero' hℓ),
      map_zero] at h3
    have h4 := f1.map φ
    rw [← coeff_map, ← hf', ← h3, map_zero] at h4
    exact not_isUnit_zero h4
  have h5 := subst_log_eq_X (mul_inv_cancel₀ hγ) g0 hd hL0 hL
  set ω := (coeff 1 (PowerSeries.subst U f' : K⟦X⟧))⁻¹
  have h0 : constantCoeff (C ω * L) = 0 := by rw [map_mul, hL0, mul_zero]
  rw [psubst_psubst (σ := Unit) h0 hU] at h5
  have u0 : constantCoeff (PowerSeries.subst (C ω * L) U : K⟦X⟧) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero h0 _ hU
  refine ⟨ω, f.substInvOfIsUnit f1, by rw [coeff_one_substInvOfIsUnit]; exact Units.isUnit _, ?_⟩
  have h6 := congrArg (MvPowerSeries.map φ) (subst_substInvOfIsUnit_left f f0 f1)
  rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' f0)] at h6
  have h7 : PowerSeries.subst f' (PowerSeries.map φ (f.substInvOfIsUnit f1)) = (X : K⟦X⟧) :=
    h6.trans (PowerSeries.map_X φ)
  have h8 := psubst_psubst (σ := Unit) u0 f0' (PowerSeries.map φ (f.substInvOfIsUnit f1))
  rw [h7, h5, X_subst, PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero' u0)] at h8
  exact h8

end Algebra

/- English proof (translation)
Introduce `d q _ M hd hd16 hsp hL hOk b₁ b₂ b₃ b₄ b₆`. Take `⟨F, hfin, H⟩` from `exists_formalGroup_add q M hOk b₁ b₂ b₃ b₄ b₆`. Take `⟨ℓ, hℓ, hUℓ, h1, h2⟩` from `height_one_of_split d q M F hd hd16 hsp hL hOk H`. Establish `hU : constantCoeff (PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u)) = 0`. Rewrite using `[← coeff_zero_eq_constantCoeff_apply, coeff_map, tay, coeff_mk]`.

Simplify using `[Mdl.u]`. Rewrite `h1`, `h2` using `[← map_mulN (algebraMap 𝓞_ℂ_[q] ℂ_[q]) F hU hℓ hUℓ H q]`. Take `⟨f, hf⟩` from `GlobalTheory.ConvSer.HeightOneInt.htOneIsGm q F hfin ⟨h1, h2⟩`. Establish `hL0 : constantCoeff (logS : ℂ_[q]⟦X⟧) = 0`. Rewrite using `[← coeff_zero_eq_constantCoeff_apply, logS, coeff_mk, if_pos rfl]`.

Take `⟨ω, e, he1, he⟩` from `exists_scale (algebraMap 𝓞_ℂ_[q] ℂ_[q]) F hU hℓ hUℓ H hf hL0 (MulSeries.mulS_laws q).2.2.2.2.1`. Establish `hO : ∀ x : 𝓞_ℂ_[q], ‖algebraMap 𝓞_ℂ_[q] ℂ_[q] x‖ ≤ 1` using `fun x => by`. Establish `hx` using `(Valuation.mem_valuationSubring_iff _ _).1 x.2`. Rewrite using `[PadicComplex.norm_eq_norm]`. Conclude with `Valued.toNormedField.norm_le_one_iff.2 hx`.

Use `⟨ω, hOk, by rw [map_mul, hL0, mul_zero], fun n => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hat, he, coeff_map]`. Conclude with `hO _`. Rewrite using `[hat, he, coeff_map]`. Take `⟨v, hv⟩` from `he1.exists_right_inv`.

Establish `h3` using `congrArg (fun x => ‖algebraMap 𝓞_ℂ_[q] ℂ_[q] x‖) hv`. Simplify using `only [map_mul, norm_mul, map_one, norm_one] at h3`. Establish `h4` using `hO (coeff 1 e)`. Establish `h5` using `hO v`. Use polynomial arithmetic with `[norm_nonneg (algebraMap 𝓞_ℂ_[q] ℂ_[q] (coeff 1 e)), norm_nonneg (algebraMap 𝓞_ℂ_[q] ℂ_[q] v)]`.
-/
theorem exists_mChart : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.Ok → IsAlgebraic ℚ M.W.a₁ → IsAlgebraic ℚ M.W.a₂ → IsAlgebraic ℚ M.W.a₃ → IsAlgebraic ℚ M.W.a₄ → IsAlgebraic ℚ M.W.a₆ → ∃ ω : ℂ_[q], M.MChart ω := by
  intro d q _ M hd hd16 hsp hL hOk b₁ b₂ b₃ b₄ b₆
  obtain ⟨F, hfin, H⟩ := exists_formalGroup_add q M hOk b₁ b₂ b₃ b₄ b₆
  obtain ⟨ℓ, hℓ, hUℓ, h1, h2⟩ := height_one_of_split d q M F hd hd16 hsp hL hOk H
  have hU : constantCoeff (PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u)) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, tay, coeff_mk]
    simp [Mdl.u]
  rw [← map_mulN (algebraMap 𝓞_ℂ_[q] ℂ_[q]) F hU hℓ hUℓ H q] at h1 h2
  obtain ⟨f, hf⟩ := GlobalTheory.ConvSer.HeightOneInt.htOneIsGm q F hfin ⟨h1, h2⟩
  have hL0 : constantCoeff (logS : ℂ_[q]⟦X⟧) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, logS, coeff_mk, if_pos rfl]
  obtain ⟨ω, e, he1, he⟩ := exists_scale (algebraMap 𝓞_ℂ_[q] ℂ_[q]) F hU hℓ hUℓ H hf hL0
    (MulSeries.mulS_laws q).2.2.2.2.1
  have hO : ∀ x : 𝓞_ℂ_[q], ‖algebraMap 𝓞_ℂ_[q] ℂ_[q] x‖ ≤ 1 := fun x => by
    have hx := (Valuation.mem_valuationSubring_iff _ _).1 x.2
    rw [PadicComplex.norm_eq_norm]
    exact Valued.toNormedField.norm_le_one_iff.2 hx
  refine ⟨ω, hOk, by rw [map_mul, hL0, mul_zero], fun n => ?_, ?_⟩
  · rw [hat, he, coeff_map]; exact hO _
  · rw [hat, he, coeff_map]
    obtain ⟨v, hv⟩ := he1.exists_right_inv
    have h3 := congrArg (fun x => ‖algebraMap 𝓞_ℂ_[q] ℂ_[q] x‖) hv
    simp only [map_mul, norm_mul, map_one, norm_one] at h3
    have h4 := hO (coeff 1 e)
    have h5 := hO v
    nlinarith [norm_nonneg (algebraMap 𝓞_ℂ_[q] ℂ_[q] (coeff 1 e)), norm_nonneg (algebraMap 𝓞_ℂ_[q] ℂ_[q] v)]

end GlobalTheory.MomOne.SplitChart
