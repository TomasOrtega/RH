import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ConstantCoeffSubst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetFactorDepthInChartIndependentClosedField
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.DetDepthBasis

open MvPowerSeries ReciprocityTheory.PGsh GlobalTheory.FGDepth

noncomputable section

variable {C : Type} [Field C]

def kerMat {i : ℕ} (g : Matrix (Fin i) (Fin i) C) (s t : Σ _ : Fin i, Fin i) : C :=
  if s.1 = t.1 then g t.2 s.2 else 0

def linP {i : ℕ} (g : Matrix (Fin i) (Fin i) C) (s : Σ _ : Fin i, Fin i) :
    MvPolynomial (Σ _ : Fin i, Fin i) C :=
  ∑ t, MvPolynomial.C (kerMat g s t) * MvPolynomial.X t

/- English proof (translation)
Unfold `linP`. Conclude with `MvPolynomial.IsHomogeneous.sum _ _ _ fun t _ => MvPolynomial.isHomogeneous_C_mul_X _ _`.
-/
theorem isHomogeneous_linP {i : ℕ} (g : Matrix (Fin i) (Fin i) C) (s : Σ _ : Fin i, Fin i) :
    (linP g s).IsHomogeneous 1 := by
  unfold linP
  exact MvPolynomial.IsHomogeneous.sum _ _ _ fun t _ => MvPolynomial.isHomogeneous_C_mul_X _ _

/- English proof (translation)
Rewrite using `[linP, ← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_sum]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_C, MvPolynomial.coe_X, smul_eq_C_mul]`.
-/
theorem coe_linP {i : ℕ} (g : Matrix (Fin i) (Fin i) C) (s : Σ _ : Fin i, Fin i) :
    ((linP g s : MvPolynomial (Σ _ : Fin i, Fin i) C) : MvPowerSeries (Σ _ : Fin i, Fin i) C) =
      ∑ t, kerMat g s t • (X t : MvPowerSeries (Σ _ : Fin i, Fin i) C) := by
  rw [linP, ← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_mul, MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coeToMvPowerSeries.ringHom_apply,
    MvPolynomial.coe_C, MvPolynomial.coe_X, smul_eq_C_mul]

/- English proof (translation)
The claim follows from `hasSubst_of_constantCoeff_zero fun s => by simp [coe_linP, map_sum]`.
-/
theorem hasSubst_linP {i : ℕ} (g : Matrix (Fin i) (Fin i) C) :
    HasSubst (fun s => (↑(linP g s) : MvPowerSeries (Σ _ : Fin i, Fin i) C)) :=
  hasSubst_of_constantCoeff_zero fun s => by simp [coe_linP, map_sum]

/- English proof (translation)
Establish `hc : (d.prod fun s n => ((linP g s : MvPolynomial _ C) : MvPowerSeries (Σ _ : Fin i, Fin i) C) ^ n) = ((d.prod fun s n => linP g s ^ n : MvPolynomial _ C) : MvPowerSeries _ C)`. Rewrite using `[← MvPolynomial.coeToMvPowerSeries.ringHom_apply, Finsupp.prod, Finsupp.prod, map_prod]`. Simplify using `[MvPolynomial.coeToMvPowerSeries.ringHom_apply]`. Rewrite using `[hc, MvPolynomial.coeff_coe]`. Establish `hh : (d.prod fun s n => linP g s ^ n : MvPolynomial _ C).IsHomogeneous d.degree`.

Use `MvPolynomial.IsHomogeneous.prod d.support (fun s => linP g s ^ d s) (fun s => 1 * d s) fun s _ => (isHomogeneous_linP g s).pow _` as an intermediate fact. Rewrite using `[Finsupp.prod]`. Use `this using 1` and compare the differences between its conclusion and the goal. Apply the tactic sequence `simp only [one_mul] first | rfl | simp [Finsupp.degree_apply]`. Conclude with `hh.coeff_eq_zero h`.
-/
theorem coeff_prod_linP {i : ℕ} (g : Matrix (Fin i) (Fin i) C) (d e : (Σ _ : Fin i, Fin i) →₀ ℕ)
    (h : e.degree ≠ d.degree) :
    coeff e (d.prod fun s n => ((linP g s : MvPolynomial _ C) : MvPowerSeries (Σ _ : Fin i, Fin i) C) ^ n) = 0 := by
  have hc : (d.prod fun s n => ((linP g s : MvPolynomial _ C) : MvPowerSeries (Σ _ : Fin i, Fin i) C) ^ n) =
      ((d.prod fun s n => linP g s ^ n : MvPolynomial _ C) : MvPowerSeries _ C) := by
    rw [← MvPolynomial.coeToMvPowerSeries.ringHom_apply, Finsupp.prod, Finsupp.prod, map_prod]
    simp [MvPolynomial.coeToMvPowerSeries.ringHom_apply]
  rw [hc, MvPolynomial.coeff_coe]
  have hh : (d.prod fun s n => linP g s ^ n : MvPolynomial _ C).IsHomogeneous d.degree := by
    have := MvPolynomial.IsHomogeneous.prod d.support (fun s => linP g s ^ d s) (fun s => 1 * d s)
      fun s _ => (isHomogeneous_linP g s).pow _
    rw [Finsupp.prod]
    convert this using 1
    · simp only [one_mul]
      first | rfl | simp [Finsupp.degree_apply]
  exact hh.coeff_eq_zero h

end

end GlobalTheory.DetDepthBasis

namespace GlobalTheory.DetDepthBasis

open MvPowerSeries ReciprocityTheory.PGsh GlobalTheory.FGDepth

noncomputable section

variable {C : Type} [Field C]

/- English proof (translation)
Unfold `derivAt0`. Use `Finset.sum_subset hS fun α _ hα => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.notMem_support_iff.1 hα]`. Simplify using the standard rewrite rules.
-/
theorem derivAt0_eq_sum {σ : Type} (P : MvPolynomial σ C) (h : MvPowerSeries σ C) (S : Finset (σ →₀ ℕ))
    (hS : P.support ⊆ S) : derivAt0 P h = ∑ α ∈ S, P.coeff α * mfact α * coeff α h := by
  unfold derivAt0
  refine Finset.sum_subset hS fun α _ hα => ?_
  rw [MvPolynomial.notMem_support_iff.1 hα]
  simp

/- English proof (translation)
Simplify using `only [derivAt0, GlobalTheory.PolyPairingAdjoint.pair, MvPolynomial.coeff_coe]`. Both sides reduce to the same expression.
-/
theorem derivAt0_coe_eq_pair {σ : Type} (P Q : MvPolynomial σ C) :
    derivAt0 P (Q : MvPowerSeries σ C) = GlobalTheory.PolyPairingAdjoint.pair P Q := by
  simp only [derivAt0, GlobalTheory.PolyPairingAdjoint.pair, MvPolynomial.coeff_coe]
  rfl

/- English proof (translation)
Rewrite using `[Finsupp.degree_apply]`. Distinguish the cases in `hs : s ∈ α.support`. Conclude with `Finset.single_le_sum (f := fun x => α x) (fun _ _ => Nat.zero_le _) hs`. Rewrite using `[Finsupp.notMem_support_iff.1 hs]`. Conclude with `Nat.zero_le _`.
-/
theorem apply_le_degree {σ : Type} (α : σ →₀ ℕ) (s : σ) : α s ≤ α.degree := by
  rw [Finsupp.degree_apply]
  by_cases hs : s ∈ α.support
  · exact Finset.single_le_sum (f := fun x => α x) (fun _ _ => Nat.zero_le _) hs
  · rw [Finsupp.notMem_support_iff.1 hs]
    exact Nat.zero_le _

/- English proof (translation)
Introduce `s`. Simplify using `using le_trans (apply_le_degree α s) h`.
-/
theorem le_const_of_degree_le {σ : Type} [Fintype σ] {α : σ →₀ ℕ} {N : ℕ} (h : α.degree ≤ N) :
    α ≤ Finsupp.equivFunOnFinite.symm (fun _ => N) := by
  intro s
  simpa using le_trans (apply_le_degree α s) h

/- English proof (translation)
Use `MvPolynomial.le_totalDegree h` as an intermediate fact. Rewrite using `[Finsupp.degree_apply]`. Conclude with `this`.
-/
theorem degree_le_totalDegree {σ : Type} {P : MvPolynomial σ C} {α : σ →₀ ℕ} (h : α ∈ P.support) :
    α.degree ≤ P.totalDegree := by
  have := MvPolynomial.le_totalDegree h
  rw [Finsupp.degree_apply]
  exact this

/- English proof (translation)
Use `set P' := GlobalTheory.PolyPairingAdjoint.subst (fun s t => kerMat g t s) P`. Use `set N := max P.totalDegree P'.totalDegree`. Use `set n : (Σ _ : Fin i, Fin i) →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun _ => N)`. Use `set Q := trunc' C n h`. Establish `hL` using `hasSubst_linP g`.

Establish `h1 : ∀ e : (Σ _ : Fin i, Fin i) →₀ ℕ, e.degree ≤ N → coeff e (subst (fun s => (↑(linP g s) : MvPowerSeries (Σ _ : Fin i, Fin i) C)) h) = coeff e (subst (fun s => (↑(linP g s) : MvPowerSeries (Σ _ : Fin i, Fin i) C)) (Q : MvPowerSeries _ C))`. Introduce `e he`. Rewrite using `[coeff_subst hL, coeff_subst hL]`. Use `finsum_congr fun d => ?_` and prove the remaining obligations. Distinguish the cases in `hd : e.degree = d.degree`.

Rewrite using `[MvPolynomial.coeff_coe, coeff_trunc', if_pos (le_const_of_degree_le (hd ▸ he))]`. Rewrite using `[coeff_prod_linP g d e hd, smul_zero, smul_zero]`. Establish `h2 : subst (fun s => (↑(linP g s) : MvPowerSeries (Σ _ : Fin i, Fin i) C)) (Q : MvPowerSeries _ C) = ((GlobalTheory.PolyPairingAdjoint.subst (kerMat g) Q : MvPolynomial _ C) : MvPowerSeries _ C)`. Rewrite using `[subst_coe]`. Use `congrArg (fun φ => φ Q) (MvPolynomial.comp_aeval (fun s => linP g s) (MvPolynomial.coeToMvPowerSeries.algHom (σ := Σ _ : Fin i, Fin i) (R := C) C))` as an intermediate fact.

Simplify using `only [AlgHom.comp_apply] at this`. Rewrite using `[GlobalTheory.PolyPairingAdjoint.subst]`. Conclude with `this.symm`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← h2]`.

Unfold `derivAt0`. Use `Finset.sum_congr rfl fun α hα => ?_` and prove the remaining obligations. Rewrite using `[h1 α (le_trans (degree_le_totalDegree hα) (le_max_left _ _))]`. Use `_ = GlobalTheory.PolyPairingAdjoint.pair P' Q := by`. Rewrite using `[derivAt0_coe_eq_pair, GlobalTheory.PolyPairingAdjoint.pair_subst]`.

Use `_ = derivAt0 P' h := by`. Rewrite using `[← derivAt0_coe_eq_pair]`. Unfold `derivAt0`. Use `Finset.sum_congr rfl fun α hα => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.coeff_coe, coeff_trunc', if_pos (le_const_of_degree_le (le_trans (degree_le_totalDegree hα) (le_max_right _ _)))]`.
-/
theorem derivAt0_subst_linP {i : ℕ} (g : Matrix (Fin i) (Fin i) C)
    (P : MvPolynomial (Σ _ : Fin i, Fin i) C) (h : MvPowerSeries (Σ _ : Fin i, Fin i) C) :
    derivAt0 P (subst (fun s => (↑(linP g s) : MvPowerSeries (Σ _ : Fin i, Fin i) C)) h) =
      derivAt0 (GlobalTheory.PolyPairingAdjoint.subst (fun s t => kerMat g t s) P) h := by
  classical
  set P' := GlobalTheory.PolyPairingAdjoint.subst (fun s t => kerMat g t s) P
  set N := max P.totalDegree P'.totalDegree
  set n : (Σ _ : Fin i, Fin i) →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun _ => N)
  set Q := trunc' C n h
  have hL := hasSubst_linP g

  have h1 : ∀ e : (Σ _ : Fin i, Fin i) →₀ ℕ, e.degree ≤ N →
      coeff e (subst (fun s => (↑(linP g s) : MvPowerSeries (Σ _ : Fin i, Fin i) C)) h) =
      coeff e (subst (fun s => (↑(linP g s) : MvPowerSeries (Σ _ : Fin i, Fin i) C)) (Q : MvPowerSeries _ C)) := by
    intro e he
    rw [coeff_subst hL, coeff_subst hL]
    refine finsum_congr fun d => ?_
    by_cases hd : e.degree = d.degree
    · rw [MvPolynomial.coeff_coe, coeff_trunc', if_pos (le_const_of_degree_le (hd ▸ he))]
    · rw [coeff_prod_linP g d e hd, smul_zero, smul_zero]
  have h2 : subst (fun s => (↑(linP g s) : MvPowerSeries (Σ _ : Fin i, Fin i) C)) (Q : MvPowerSeries _ C) =
      ((GlobalTheory.PolyPairingAdjoint.subst (kerMat g) Q : MvPolynomial _ C) : MvPowerSeries _ C) := by
    rw [subst_coe]
    have := congrArg (fun φ => φ Q) (MvPolynomial.comp_aeval (fun s => linP g s)
      (MvPolynomial.coeToMvPowerSeries.algHom (σ := Σ _ : Fin i, Fin i) (R := C) C))
    simp only [AlgHom.comp_apply] at this
    rw [GlobalTheory.PolyPairingAdjoint.subst]
    exact this.symm
  calc derivAt0 P (subst (fun s => (↑(linP g s) : MvPowerSeries (Σ _ : Fin i, Fin i) C)) h)
      = derivAt0 P ((GlobalTheory.PolyPairingAdjoint.subst (kerMat g) Q : MvPolynomial _ C) : MvPowerSeries _ C) := by
        rw [← h2]
        unfold derivAt0
        refine Finset.sum_congr rfl fun α hα => ?_
        rw [h1 α (le_trans (degree_le_totalDegree hα) (le_max_left _ _))]
    _ = GlobalTheory.PolyPairingAdjoint.pair P' Q := by
        rw [derivAt0_coe_eq_pair, GlobalTheory.PolyPairingAdjoint.pair_subst]
    _ = derivAt0 P' h := by
        rw [← derivAt0_coe_eq_pair]
        unfold derivAt0
        refine Finset.sum_congr rfl fun α hα => ?_
        rw [MvPolynomial.coeff_coe, coeff_trunc',
          if_pos (le_const_of_degree_le (le_trans (degree_le_totalDegree hα) (le_max_right _ _)))]

end

end GlobalTheory.DetDepthBasis

namespace GlobalTheory.DetDepthBasis

open MvPowerSeries ReciprocityTheory.PGsh GlobalTheory.FGDepth

noncomputable section

variable {C : Type} [Field C]

/- English proof (translation)
Rewrite using `[derivAt0_eq_sum _ h P.support (by rw [← MvPolynomial.smul_eq_C_mul]; exact MvPolynomial.support_smul), derivAt0, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun α _ => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.coeff_C_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem derivAt0_C_mul {σ : Type} (k : C) (P : MvPolynomial σ C) (h : MvPowerSeries σ C) :
    derivAt0 (MvPolynomial.C k * P) h = k * derivAt0 P h := by
  rw [derivAt0_eq_sum _ h P.support (by rw [← MvPolynomial.smul_eq_C_mul]; exact MvPolynomial.support_smul),
    derivAt0, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [MvPolynomial.coeff_C_mul]
  ring

/- English proof (translation)
Establish `hM : (GlobalTheory.PolyPairingAdjoint.subst (fun s t => kerMat g t s)).mapMatrix (Matrix.of fun a b : Fin i => (MvPolynomial.X ⟨b, a⟩ : MvPolynomial (Σ _ : Fin i, Fin i) C)) = (g.map MvPolynomial.C) * Matrix.of fun a b : Fin i => (MvPolynomial.X ⟨b, a⟩ : MvPolynomial _ C)`. Use extensionality with `a b`. Simplify using `only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply, GlobalTheory.PolyPairingAdjoint.subst_X, Fintype.sum_sigma, kerMat]`. Rewrite using `[Finset.sum_eq_single b]`. Simplify using the standard rewrite rules.

Introduce `b' _ hb'`. Simplify using `[hb']`. Simplify using the standard rewrite rules. Establish `hdet : (g.map MvPolynomial.C).det = (MvPolynomial.C g.det : MvPolynomial (Σ _ : Fin i, Fin i) C)` using `(RingHom.map_det _ _).symm`. Rewrite using `[detPow, map_pow, AlgHom.map_det, hM, Matrix.det_mul, hdet, mul_pow, map_pow]`.
-/
theorem subst_detPow {i : ℕ} (g : Matrix (Fin i) (Fin i) C) (c : ℕ) :
    GlobalTheory.PolyPairingAdjoint.subst (fun s t => kerMat g t s) (detPow C i c) =
      MvPolynomial.C (g.det ^ c) * detPow C i c := by
  classical
  have hM : (GlobalTheory.PolyPairingAdjoint.subst (fun s t => kerMat g t s)).mapMatrix
      (Matrix.of fun a b : Fin i => (MvPolynomial.X ⟨b, a⟩ : MvPolynomial (Σ _ : Fin i, Fin i) C)) =
      (g.map MvPolynomial.C) * Matrix.of fun a b : Fin i => (MvPolynomial.X ⟨b, a⟩ : MvPolynomial _ C) := by
    ext a b
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply,
      GlobalTheory.PolyPairingAdjoint.subst_X, Fintype.sum_sigma, kerMat]
    rw [Finset.sum_eq_single b]
    · simp
    · intro b' _ hb'
      simp [hb']
    · simp
  have hdet : (g.map MvPolynomial.C).det = (MvPolynomial.C g.det : MvPolynomial (Σ _ : Fin i, Fin i) C) :=
    (RingHom.map_det _ _).symm
  rw [detPow, map_pow, AlgHom.map_det, hM, Matrix.det_mul, hdet, mul_pow, map_pow]

/- English proof (translation)
Establish `inner : ∀ a : Fin i, (↑(linP g ⟨b, a⟩) : MvPowerSeries (Σ _ : Fin i, Fin i) C) = ∑ a2, g a2 a • (X ⟨b, a2⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)`. Introduce `a`. Rewrite using `[coe_linP, Fintype.sum_sigma, Finset.sum_eq_single b]`. Simplify using `[kerMat]`. Introduce `b' _ hb'`.

Simplify using `[kerMat, Ne.symm hb']`. Simplify using the standard rewrite rules. Rewrite using `[← coe_substAlgHom (hasSubst_linP g), map_sum]`. Simplify using `only [map_smul, coe_substAlgHom, subst_X (hasSubst_linP g), inner, Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun a2 _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_smul]`. Use `congr 1`. Simplify using `[Finset.sum_apply, mul_comm]`.
-/
theorem subst_linP_lin {i d : ℕ} (g : Matrix (Fin i) (Fin i) C) (u : Fin i → Fin d → C) (b : Fin i)
    (e : Fin d) :
    subst (fun s => (↑(linP g s) : MvPowerSeries (Σ _ : Fin i, Fin i) C))
      (∑ a, u a e • (X ⟨b, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)) =
    ∑ a, (fun a => ∑ a', g a a' • u a') a e • (X ⟨b, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C) := by
  classical
  have inner : ∀ a : Fin i, (↑(linP g ⟨b, a⟩) : MvPowerSeries (Σ _ : Fin i, Fin i) C) =
      ∑ a2, g a2 a • (X ⟨b, a2⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C) := by
    intro a
    rw [coe_linP, Fintype.sum_sigma, Finset.sum_eq_single b]
    · simp [kerMat]
    · intro b' _ hb'
      simp [kerMat, Ne.symm hb']
    · simp
  rw [← coe_substAlgHom (hasSubst_linP g), map_sum]
  simp only [map_smul, coe_substAlgHom, subst_X (hasSubst_linP g), inner, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a2 _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  simp [Finset.sum_apply, mul_comm]

/- English proof (translation)
Introduce `C _ _ v i d c G u g hg`. Unfold `detDepth depth`. Establish `hE : expAlong (fun _ : Fin i => G) (fun _ => fun a => ∑ a', g a a' • u a') = fun x => subst (fun s => (↑(linP g s) : MvPowerSeries (Σ _ : Fin i, Fin i) C)) (expAlong (fun _ : Fin i => G) (fun _ => u) x)`. Use function extensionality and compare the values at `x`. Simplify using `only [expAlong]`.

Rewrite using `[subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (GlobalTheory.DepthField.hasSubst_lin (fun _ : Fin i => u) x.1)) (hasSubst_linP g)]`. Use `congr 1`. Use function extensionality and compare the values at `e`. Conclude with `(subst_linP_lin g u x.1 e).symm`. Use `iInf_congr fun f => ?_` and prove the remaining obligations.

Rewrite using `[hE, ← subst_comp_subst_apply (GlobalTheory.DepthField.hasSubst_expAlong _ _) (hasSubst_linP g), derivAt0_subst_linP, subst_detPow, derivAt0_C_mul, v.map_mul, v.map_pow, hg, smul_zero, zero_add]`.
-/
theorem main : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (i d c : ℕ)
    (G : LogFGL v d) (u : Fin i → Fin d → C) (g : Matrix (Fin i) (Fin i) C), v g.det = 0 →
    detDepth G (fun a => ∑ a', g a a' • u a') c = detDepth G u c := by
  intro C _ _ v i d c G u g hg
  unfold detDepth depth
  have hE : expAlong (fun _ : Fin i => G) (fun _ => fun a => ∑ a', g a a' • u a') =
      fun x => subst (fun s => (↑(linP g s) : MvPowerSeries (Σ _ : Fin i, Fin i) C))
        (expAlong (fun _ : Fin i => G) (fun _ => u) x) := by
    funext x
    simp only [expAlong]
    rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero
      (GlobalTheory.DepthField.hasSubst_lin (fun _ : Fin i => u) x.1)) (hasSubst_linP g)]
    congr 1
    funext e
    exact (subst_linP_lin g u x.1 e).symm
  refine iInf_congr fun f => ?_
  rw [hE, ← subst_comp_subst_apply (GlobalTheory.DepthField.hasSubst_expAlong _ _) (hasSubst_linP g),
    derivAt0_subst_linP, subst_detPow, derivAt0_C_mul, v.map_mul, v.map_pow, hg, smul_zero, zero_add]

end

end GlobalTheory.DetDepthBasis
