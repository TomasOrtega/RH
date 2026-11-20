import Formalism.ThetaLogCoordinates.FockResolutionOnto.StatementD
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.RaisingKeepsEarlyLetters
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.Sl2RaisePowSuccLowerApplyEq
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.EArith
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.TypesLELeYcondC

namespace Formalism.InvariantFactorPaths.L4

open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset

section Comp
variable {k σ : Type} [Field k]

noncomputable def compL (k : Type) [Field k] {σ : Type} (Pr : (σ →₀ ℕ) → Prop) :
    MvPolynomial σ k →ₗ[k] MvPolynomial σ k where
  toFun := compP Pr
  map_add' x y := by
    classical
    ext m
    simp only [coeff_compP, coeff_add]
    split_ifs <;> simp
  map_smul' c x := by
    classical
    ext m
    simp only [coeff_compP, coeff_smul, RingHom.id_apply]
    split_ifs <;> simp

open Classical in
/- English proof (translation)
The claim follows from `coeff_compP Pr x m`.
-/
theorem coeff_compL (Pr : (σ →₀ ℕ) → Prop) (x : MvPolynomial σ k) (m : σ →₀ ℕ) :
    coeff m (compL k Pr x) = if Pr m then coeff m x else 0 := coeff_compP Pr x m

/- English proof (translation)
Rewrite using `[mem_restrictSupport_iff]`. Introduce `m hm`. Rewrite `hm` using `[Finset.mem_coe, mem_support_iff, coeff_compL]`. Use `split_ifs at hm with h`. Conclude with `h`.

Conclude with `absurd rfl hm`.
-/
theorem compL_mem (Pr : (σ →₀ ℕ) → Prop) (x : MvPolynomial σ k) :
    compL k Pr x ∈ restrictSupport k {m | Pr m} := by
  classical
  rw [mem_restrictSupport_iff]
  intro m hm
  rw [Finset.mem_coe, mem_support_iff, coeff_compL] at hm
  split_ifs at hm with h
  · exact h
  · exact absurd rfl hm

/- English proof (translation)
Rewrite `hx` using `[mem_restrictSupport_iff]`. Use extensionality with `m`. Rewrite using `[coeff_compL]`. Use `split_ifs with h`. Both sides reduce to the same expression.

Assume the negation of the conclusion as `hc`. Conclude with `h (hx (Finset.mem_coe.mpr (mem_support_iff.mpr (Ne.symm hc))))`.
-/
theorem compL_of_mem (Pr : (σ →₀ ℕ) → Prop) (x : MvPolynomial σ k) (hx : x ∈ restrictSupport k {m | Pr m}) :
    compL k Pr x = x := by
  classical
  rw [mem_restrictSupport_iff] at hx
  ext m
  rw [coeff_compL]
  split_ifs with h
  · rfl
  · by_contra hc
    exact h (hx (Finset.mem_coe.mpr (mem_support_iff.mpr (Ne.symm hc))))

/- English proof (translation)
Rewrite `hx` using `[mem_restrictSupport_iff]`. Use extensionality with `m`. Rewrite using `[coeff_compL, coeff_zero]`. Use `split_ifs with h`. Assume the negation of the conclusion as `hc`.

Conclude with `hx (Finset.mem_coe.mpr (mem_support_iff.mpr hc)) h`. Both sides reduce to the same expression.
-/
theorem compL_of_not (Pr : (σ →₀ ℕ) → Prop) (x : MvPolynomial σ k) (hx : x ∈ restrictSupport k {m | ¬ Pr m}) :
    compL k Pr x = 0 := by
  classical
  rw [mem_restrictSupport_iff] at hx
  ext m
  rw [coeff_compL, coeff_zero]
  split_ifs with h
  · by_contra hc
    exact hx (Finset.mem_coe.mpr (mem_support_iff.mpr hc)) h
  · rfl

/- English proof (translation)
Use extensionality with `m`. Rewrite using `[coeff_add, coeff_compL, coeff_compL]`. Apply the tactic sequence `by_cases h : Pr m <;> simp [h]`.
-/
theorem compL_add_not (Pr : (σ →₀ ℕ) → Prop) (x : MvPolynomial σ k) :
    compL k Pr x + compL k (fun m => ¬ Pr m) x = x := by
  classical
  ext m
  rw [coeff_add, coeff_compL, coeff_compL]
  by_cases h : Pr m <;> simp [h]

/- English proof (translation)
Use `conv_lhs => rw [← compL_add_not Pr' x]`. Rewrite using `[map_add, map_add, compL_of_mem Pr _ (h1 _ (compL_mem Pr' x)), compL_of_not Pr _ (h2 _ (compL_mem (fun m => ¬ Pr' m) x)), add_zero]`.
-/
theorem compL_intertwine (T : MvPolynomial σ k →ₗ[k] MvPolynomial σ k) (Pr Pr' : (σ →₀ ℕ) → Prop)
    (h1 : ∀ x ∈ restrictSupport k {m | Pr' m}, T x ∈ restrictSupport k {m | Pr m})
    (h2 : ∀ x ∈ restrictSupport k {m | ¬ Pr' m}, T x ∈ restrictSupport k {m | ¬ Pr m}) (x : MvPolynomial σ k) :
    compL k Pr (T x) = T (compL k Pr' x) := by
  conv_lhs => rw [← compL_add_not Pr' x]
  rw [map_add, map_add, compL_of_mem Pr _ (h1 _ (compL_mem Pr' x)),
    compL_of_not Pr _ (h2 _ (compL_mem (fun m => ¬ Pr' m) x)), add_zero]

/- English proof (translation)
Establish `h1 : pderiv u (X v * pderiv v z) = X v * pderiv u (pderiv v z)`. Rewrite using `[pderiv_mul, pderiv_X, Pi.single_eq_of_ne (Ne.symm huv)]`. Simplify using the standard rewrite rules. Establish `h2 : X u * (X v * pderiv u (pderiv v z)) = (cv * cu) • z`. Rewrite using `[← h1, hv, Derivation.map_smul, mul_smul_comm, hu, smul_smul]`.

Rewrite using `[pderiv_mul, pderiv_X, Pi.single_eq_same, one_mul, mul_add, hv, mul_left_comm, h2, ← add_smul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem XDXD (u v : σ) (huv : u ≠ v) (z : MvPolynomial σ k) (cu cv : k) (hu : X u * pderiv u z = cu • z)
    (hv : X v * pderiv v z = cv • z) : X v * pderiv u (X u * pderiv v z) = (cv * (cu + 1)) • z := by
  classical
  have h1 : pderiv u (X v * pderiv v z) = X v * pderiv u (pderiv v z) := by
    rw [pderiv_mul, pderiv_X, Pi.single_eq_of_ne (Ne.symm huv)]
    simp
  have h2 : X u * (X v * pderiv u (pderiv v z)) = (cv * cu) • z := by
    rw [← h1, hv, Derivation.map_smul, mul_smul_comm, hu, smul_smul]
  rw [pderiv_mul, pderiv_X, Pi.single_eq_same, one_mul, mul_add, hv, mul_left_comm, h2, ← add_smul]
  congr 1
  ring

end Comp

section WW
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}

def wp (K : ℕ) {r : ℕ} (m : Fin (K + 1) × Fin r →₀ ℕ) : Fin r → ℤ := fun a => (m (Fin.last K, a) : ℤ)

noncomputable def cw (p : ℕ) [Fact p.Prime] (K : ℕ) {r : ℕ} (γ : Fin r → ℤ) :
    MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] :=
  compL ℚ_[p] (fun m => wp K m = γ)

/- English proof (translation)
Use function extensionality and compare the values at `a`. Establish `h` using `last_ne_of_lt i hi`. Simplify using `[wp, Prod.ext_iff, Ne.symm h]`.
-/
theorem wp_early (i : Fin (K + 1)) (hi : (i : ℕ) < K) (c d : Fin r) (m : Fin (K + 1) × Fin r →₀ ℕ) :
    wp K (Finsupp.single (i, c) 1 + (m - Finsupp.single (i, d) 1)) = wp K m := by
  funext a
  have h := last_ne_of_lt i hi
  simp [wp, Prod.ext_iff, Ne.symm h]

/- English proof (translation)
Use function extensionality and compare the values at `a`. Simplify using `only [wp, shiftW]`. Rewrite using `[shift_apply m _ _ _ hm]`. Simplify using `[Prod.ext_iff]`.
-/
theorem wp_last (c d : Fin r) (m : Fin (K + 1) × Fin r →₀ ℕ) (hm : 1 ≤ m (Fin.last K, d)) :
    wp K (Finsupp.single (Fin.last K, c) 1 + (m - Finsupp.single (Fin.last K, d) 1)) = shiftW (wp K m) c d := by
  classical
  funext a
  simp only [wp, shiftW]
  rw [shift_apply m _ _ _ hm]
  simp [Prod.ext_iff]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl`. Use function extensionality and compare the values at `a`. Simplify using `only [shiftW]`. Expand and normalize the polynomial expressions, which then agree.

Introduce and unpack `rfl`. Use function extensionality and compare the values at `a`. Simplify using `only [shiftW]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem shiftW_iff (γ δ : Fin r → ℤ) (c d : Fin r) : shiftW δ c d = γ ↔ δ = shiftW γ d c := by
  constructor
  · rintro rfl; funext a; simp only [shiftW]; ring
  · rintro rfl; funext a; simp only [shiftW]; ring

/- English proof (translation)
Use function extensionality and compare the values at `a`. Simplify using `only [shiftW]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem shiftW_self (γ : Fin r → ℤ) (c : Fin r) : shiftW γ c c = γ := by
  funext a; simp only [shiftW]; ring

/- English proof (translation)
Use `compL_intertwine (glAct p LL K s t) _ _ ?_ ?_ x` and prove the remaining obligations. Use `glAct_keep LL K s t _ _ ?_ ?_` and prove the remaining obligations. Introduce `i hi _ m hm _`. Simplify using `only [Set.mem_ofPred_eq] at hm ⊢`. Rewrite using `[wp_early i hi]`.

Conclude with `hm`. Introduce `i hi _ m hm _`. Simplify using `only [Set.mem_ofPred_eq] at hm ⊢`. Rewrite using `[wp_early i hi]`. Conclude with `hm`.

Use `glAct_keep LL K s t _ _ ?_ ?_` and prove the remaining obligations. Introduce `i hi _ m hm _`. Simplify using `only [Set.mem_ofPred_eq] at hm ⊢`. Rewrite using `[wp_early i hi]`. Conclude with `hm`.

Introduce `i hi _ m hm _`. Simplify using `only [Set.mem_ofPred_eq] at hm ⊢`. Rewrite using `[wp_early i hi]`. Conclude with `hm`.
-/
theorem cw_glAct (LL : Letters (K + 1)) (γ : Fin r → ℤ) (s t : Fin r)
    (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    cw p K γ (glAct p LL K s t x) = glAct p LL K s t (cw p K γ x) := by
  refine compL_intertwine (glAct p LL K s t) _ _ ?_ ?_ x
  · refine glAct_keep LL K s t _ _ ?_ ?_
    · intro i hi _ m hm _
      simp only [Set.mem_ofPred_eq] at hm ⊢
      rw [wp_early i hi]; exact hm
    · intro i hi _ m hm _
      simp only [Set.mem_ofPred_eq] at hm ⊢
      rw [wp_early i hi]; exact hm
  · refine glAct_keep LL K s t _ _ ?_ ?_
    · intro i hi _ m hm _
      simp only [Set.mem_ofPred_eq] at hm ⊢
      rw [wp_early i hi]; exact hm
    · intro i hi _ m hm _
      simp only [Set.mem_ofPred_eq] at hm ⊢
      rw [wp_early i hi]; exact hm

/- English proof (translation)
Use `compL_intertwine ((LinearMap.mulLeft ℚ_[p] (X (Fin.last K, s))) ∘ₗ (pderiv (Fin.last K, t)).toLinearMap) _ _ ?_ ?_ x` and prove the remaining obligations. Use `XD_keep _ _ _ _ ?_` and prove the remaining obligations. Introduce `m hm hb`. Simplify using `only [Set.mem_ofPred_eq] at hm ⊢`. Rewrite using `[wp_last s t m hb, shiftW_iff]`.

Conclude with `hm`. Use `XD_keep _ _ _ _ ?_` and prove the remaining obligations. Introduce `m hm hb`. Simplify using `only [Set.mem_ofPred_eq] at hm ⊢`. Rewrite using `[wp_last s t m hb, shiftW_iff]`.

Conclude with `hm`.
-/
theorem cw_WD (γ : Fin r → ℤ) (s t : Fin r) (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    cw p K γ (X (Fin.last K, s) * pderiv (Fin.last K, t) x) =
      X (Fin.last K, s) * pderiv (Fin.last K, t) (cw p K (shiftW γ t s) x) := by
  refine compL_intertwine
    ((LinearMap.mulLeft ℚ_[p] (X (Fin.last K, s))) ∘ₗ (pderiv (Fin.last K, t)).toLinearMap) _ _ ?_ ?_ x
  · refine XD_keep _ _ _ _ ?_
    intro m hm hb
    simp only [Set.mem_ofPred_eq] at hm ⊢
    rw [wp_last s t m hb, shiftW_iff]; exact hm
  · refine XD_keep _ _ _ _ ?_
    intro m hm hb
    simp only [Set.mem_ofPred_eq] at hm ⊢
    rw [wp_last s t m hb, shiftW_iff]; exact hm

/- English proof (translation)
Use extensionality with `m`. Rewrite using `[coeff_X_mul_pderiv', coeff_smul, smul_eq_mul, cw, coeff_compL]`. Use `split_ifs with h`. Rewrite using `[← h]`. Simplify using `[wp, mul_comm]`.

Simplify using the standard rewrite rules.
-/
theorem WD_cw (γ : Fin r → ℤ) (a : Fin r) (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    X (Fin.last K, a) * pderiv (Fin.last K, a) (cw p K γ x) = ((γ a : ℤ) : ℚ_[p]) • cw p K γ x := by
  classical
  ext m
  rw [coeff_X_mul_pderiv', coeff_smul, smul_eq_mul, cw, coeff_compL]
  split_ifs with h
  · rw [← h]; simp [wp, mul_comm]
  · simp

def phiW {r : ℕ} (γ : Fin r → ℤ) : ℤ := ∑ c : Fin r, ((c : ℕ) : ℤ) * γ c

/- English proof (translation)
Simplify using `only [phiW, shiftW, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]`.
-/
theorem phiW_shift (γ : Fin r → ℤ) (c d : Fin r) : phiW (shiftW γ c d) = phiW γ + ((c : ℕ) : ℤ) - ((d : ℕ) : ℤ) := by
  simp only [phiW, shiftW, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

/- English proof (translation)
Take `⟨β, hβ, hmax⟩` from `Finset.exists_max_image (x.support.image (wp K)) phiW ((support_nonempty.mpr hx).image _)`. Take `⟨m, hm, rfl⟩` from `Finset.mem_image.mp hβ`. Use `⟨wp K m, ?_, ?_, m, hm, rfl⟩` and prove the remaining obligations. Introduce `h0`. Use `congrArg (coeff m) h0` as an intermediate fact.

Rewrite `this` using `[cw, coeff_compL, if_pos rfl, coeff_zero]`. Conclude with `(mem_support_iff.mp hm) this`. Introduce `γ hγ`. Use extensionality with `m'`. Rewrite using `[cw, coeff_compL, coeff_zero]`.

Use `split_ifs with h`. Assume the negation of the conclusion as `hc`. Use `hmax γ (Finset.mem_image.mpr ⟨m', mem_support_iff.mpr hc, h⟩)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Both sides reduce to the same expression.
-/
theorem exists_top (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hx : x ≠ 0) :
    ∃ β : Fin r → ℤ, cw p K β x ≠ 0 ∧ (∀ γ, phiW β < phiW γ → cw p K γ x = 0) ∧ ∃ m ∈ x.support, wp K m = β := by
  classical
  obtain ⟨β, hβ, hmax⟩ := Finset.exists_max_image (x.support.image (wp K)) phiW
    ((support_nonempty.mpr hx).image _)
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hβ
  refine ⟨wp K m, ?_, ?_, m, hm, rfl⟩
  · intro h0
    have := congrArg (coeff m) h0
    rw [cw, coeff_compL, if_pos rfl, coeff_zero] at this
    exact (mem_support_iff.mp hm) this
  · intro γ hγ
    ext m'
    rw [cw, coeff_compL, coeff_zero]
    split_ifs with h
    · by_contra hc
      have := hmax γ (Finset.mem_image.mpr ⟨m', mem_support_iff.mpr hc, h⟩)
      omega
    · rfl

end WW

section HW
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}

noncomputable def WS (p : ℕ) [Fact p.Prime] (K : ℕ) {r : ℕ} (γ : Fin r → ℤ) :
    Submodule ℚ_[p] (MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :=
  restrictSupport ℚ_[p] {m | wp K m = γ}

/- English proof (translation)
The claim follows from `compL_mem _ x`.
-/
theorem cw_mem (γ : Fin r → ℤ) (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) : cw p K γ x ∈ WS p K γ :=
  compL_mem _ x

/- English proof (translation)
Establish `h` using `WD_cw γ c z`. Rewrite `h` using `[show cw p K γ z = z from compL_of_mem _ z hz]`. Then use the resulting hypothesis.
-/
theorem WS_eig (γ : Fin r → ℤ) (z : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hz : z ∈ WS p K γ) (c : Fin r) :
    X (Fin.last K, c) * pderiv (Fin.last K, c) z = ((γ c : ℤ) : ℚ_[p]) • z := by
  have h := WD_cw γ c z
  rwa [show cw p K γ z = z from compL_of_mem _ z hz] at h

noncomputable def eW (p : ℕ) [Fact p.Prime] (K : ℕ) {r : ℕ} (s t : Fin r) :
    Module.End ℚ_[p] (MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :=
  (LinearMap.mulLeft ℚ_[p] (X (Fin.last K, s))) ∘ₗ (pderiv (Fin.last K, t)).toLinearMap

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem eW_apply (s t : Fin r) (z : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    eW p K s t z = X (Fin.last K, s) * pderiv (Fin.last K, t) z := rfl

/- English proof (translation)
Use `XD_keep _ _ _ _ ?_ z hz` and prove the remaining obligations. Introduce `m hm hb`. Simplify using `only [Set.mem_ofPred_eq] at hm ⊢`. Rewrite using `[wp_last s t m hb, hm]`.
-/
theorem eW_mem (γ : Fin r → ℤ) (s t : Fin r) (z : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hz : z ∈ WS p K γ) :
    eW p K s t z ∈ WS p K (shiftW γ s t) := by
  refine XD_keep _ _ _ _ ?_ z hz
  intro m hm hb
  simp only [Set.mem_ofPred_eq] at hm ⊢
  rw [wp_last s t m hb, hm]

/- English proof (translation)
Use `(FockB.ops_commute disj_last ?_ (glAct_mem LL K a b)).symm` and prove the remaining obligations. Unfold `eW`. Rewrite using `[← Module.End.mul_eq_comp]`. Conclude with `mul_mem (FockB.mulLeftX_mem (last_mem s)) (FockB.pderiv_mem (last_mem t))`.
-/
theorem eW_comm (LL : Letters (K + 1)) (s t a b : Fin r) :
    Commute (glAct p LL K a b : Module.End ℚ_[p] (MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p])) (eW p K s t) := by
  refine (FockB.ops_commute disj_last ?_ (glAct_mem LL K a b)).symm
  unfold eW
  rw [← Module.End.mul_eq_comp]
  exact mul_mem (FockB.mulLeftX_mem (last_mem s)) (FockB.pderiv_mem (last_mem t))

/- English proof (translation)
Introduce `h0`. Establish `hne : ((Fin.last K, a) : Fin (K + 1) × Fin r) ≠ (Fin.last K, a')` using `fun h => haa (Prod.mk.inj h).2`. Establish `h` using `XDXD _ _ hne z _ _ (WS_eig γ z hz a) (WS_eig γ z hz a')`. Rewrite `h0` using `[eW_apply]`. Rewrite `h` using `[h0, map_zero, mul_zero]`.

Break down `smul_eq_zero.mp h.symm with h3 | h3` into its components or cases. Establish `h4 : ((γ a' * (γ a + 1) : ℤ) : ℚ_[p]) = 0` using `by push_cast; exact h3`. Establish `h5` using `Int.cast_eq_zero.mp h4`. Apply the tactic sequence `rcases mul_eq_zero.mp h5 with h6 | h6 <;> omega`. Conclude with `hz0 h3`.
-/
theorem eW_ne (γ : Fin r → ℤ) (a a' : Fin r) (haa : a ≠ a') (z : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p])
    (hz : z ∈ WS p K γ) (hz0 : z ≠ 0) (h1 : 0 < γ a') (h2 : 0 ≤ γ a) : eW p K a a' z ≠ 0 := by
  intro h0
  have hne : ((Fin.last K, a) : Fin (K + 1) × Fin r) ≠ (Fin.last K, a') := fun h => haa (Prod.mk.inj h).2
  have h := XDXD _ _ hne z _ _ (WS_eig γ z hz a) (WS_eig γ z hz a')
  rw [eW_apply] at h0
  rw [h0, map_zero, mul_zero] at h
  rcases smul_eq_zero.mp h.symm with h3 | h3
  · have h4 : ((γ a' * (γ a + 1) : ℤ) : ℚ_[p]) = 0 := by push_cast; exact h3
    have h5 := Int.cast_eq_zero.mp h4
    rcases mul_eq_zero.mp h5 with h6 | h6 <;> omega
  · exact hz0 h3

/- English proof (translation)
Introduce `i`. Proceed by induction on `i with`. Consider the case `zero => intro γ z _ hz0 _ _`. Simplify using `using hz0`. Consider the case `succ i ih`.

Introduce `γ z hz hz0 h1 h2`. Rewrite using `[pow_succ, Module.End.mul_apply]`. Use `ih (shiftW γ a a') _ (eW_mem γ a a' z hz) (eW_ne γ a a' haa z hz hz0 (by push_cast at h1; omega) h2) ?_ ?_` and prove the remaining obligations. Simplify using `only [shiftW, if_neg haa, if_true]`. Move the coercions through the operations in `at h1`.

Use linear arithmetic over natural numbers and integers. Simplify using `only [shiftW, if_neg (Ne.symm haa), if_true]`. Use linear arithmetic over natural numbers and integers.
-/
theorem eW_pow_ne (a a' : Fin r) (haa : a ≠ a') : ∀ (i : ℕ) (γ : Fin r → ℤ)
    (z : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]), z ∈ WS p K γ → z ≠ 0 → (i : ℤ) ≤ γ a' → 0 ≤ γ a →
    ((eW p K a a') ^ i) z ≠ 0 := by
  intro i
  induction i with
  | zero => intro γ z _ hz0 _ _; simpa using hz0
  | succ i ih =>
    intro γ z hz hz0 h1 h2
    rw [pow_succ, Module.End.mul_apply]
    refine ih (shiftW γ a a') _ (eW_mem γ a a' z hz) (eW_ne γ a a' haa z hz hz0 (by push_cast at h1; omega) h2) ?_ ?_
    · simp only [shiftW, if_neg haa, if_true]
      push_cast at h1; omega
    · simp only [shiftW, if_neg (Ne.symm haa), if_true]
      omega

def shiftN {r : ℕ} (γ : Fin r → ℤ) (c d : Fin r) (i : ℤ) : Fin r → ℤ :=
  fun c' => γ c' + (if c = c' then i else 0) - (if d = c' then i else 0)

/- English proof (translation)
Use function extensionality and compare the values at `c'`. Simplify using `only [shiftN, shiftW]`. Apply the tactic sequence `split_ifs <;> ring`.
-/
theorem shiftN_succ (γ : Fin r → ℤ) (c d : Fin r) (i : ℤ) : shiftN (shiftW γ c d) c d i = shiftN γ c d (i + 1) := by
  funext c'
  simp only [shiftN, shiftW]
  split_ifs <;> ring

/- English proof (translation)
Use function extensionality and compare the values at `c'`. Simplify using `[shiftN]`.
-/
theorem shiftN_zero (γ : Fin r → ℤ) (c d : Fin r) : shiftN γ c d 0 = γ := by
  funext c'
  simp [shiftN]

/- English proof (translation)
Use function extensionality and compare the values at `c'`. Simplify using `only [shiftN]`. Apply the tactic sequence `split_ifs <;> ring`.
-/
theorem shiftN_back (γ : Fin r → ℤ) (c d : Fin r) (i j : ℤ) : shiftN (shiftN γ c d i) d c j = shiftN γ d c (j - i) := by
  funext c'
  simp only [shiftN]
  split_ifs <;> ring

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem shiftN_one (γ : Fin r → ℤ) (c d : Fin r) : shiftN γ c d 1 = shiftW γ c d := rfl

variable (LL : Letters (K + 1)) (hv : LL.vec (Fin.last K) = true) (Cs : Finset (Fin r)) (th : Fin r → ℤ)
  (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hx : x ∈ HWC p LL (K + 1) Cs th)

include hv hx in
/- English proof (translation)
Establish `hk` using `(Submodule.mem_inf.mp hx).2`. Simplify using `only [Submodule.mem_iInf, LinearMap.mem_ker] at hk`. Establish `h0` using `hk s t ⟨hs, ht, hst⟩`. Rewrite `h0` using `[glAct_succ LL hv]`. Establish `h1` using `congrArg (cw p K γ) h0`.

Rewrite `h1` using `[map_add, map_zero, cw_glAct, cw_WD]`. Conclude with `eq_neg_of_add_eq_zero_left h1`.
-/
theorem eJ_cw_lt (s t : Fin r) (hs : s ∈ Cs) (ht : t ∈ Cs) (hst : s < t) (γ : Fin r → ℤ) :
    glAct p LL K s t (cw p K γ x) = -(eW p K s t (cw p K (shiftW γ t s) x)) := by
  have hk := (Submodule.mem_inf.mp hx).2
  simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hk
  have h0 := hk s t ⟨hs, ht, hst⟩
  rw [glAct_succ LL hv] at h0
  have h1 := congrArg (cw p K γ) h0
  rw [map_add, map_zero, cw_glAct, cw_WD] at h1
  exact eq_neg_of_add_eq_zero_left h1

include hv hx in
/- English proof (translation)
Establish `h0` using `cartan_eigC LL (K + 1) Cs th x (Submodule.mem_inf.mp hx).1 s hs`. Rewrite `h0` using `[glAct_succ LL hv]`. Establish `h1` using `congrArg (cw p K γ) h0`. Rewrite `h1` using `[map_add, map_smul, cw_glAct, cw_WD, shiftW_self, WD_cw]`. Rewrite using `[Int.cast_sub, sub_smul, ← h1]`.

Normalize the expressions using the abelian group laws.
-/
theorem eJ_cw_diag (s : Fin r) (hs : s ∈ Cs) (γ : Fin r → ℤ) :
    glAct p LL K s s (cw p K γ x) = ((th s - γ s : ℤ) : ℚ_[p]) • cw p K γ x := by
  have h0 := cartan_eigC LL (K + 1) Cs th x (Submodule.mem_inf.mp hx).1 s hs
  rw [glAct_succ LL hv] at h0
  have h1 := congrArg (cw p K γ) h0
  rw [map_add, map_smul, cw_glAct, cw_WD, shiftW_self, WD_cw] at h1
  rw [Int.cast_sub, sub_smul, ← h1]
  abel

include hv hx in
/- English proof (translation)
Introduce `i`. Proceed by induction on `i with`. Consider the case `zero => intro γ`. Simplify using `[shiftN_zero]`. Consider the case `succ i ih`.

Introduce `γ`. Rewrite using `[pow_succ, Module.End.mul_apply, eJ_cw_lt LL hv Cs th x hx s t hs ht hst γ, map_neg, ← Module.End.mul_apply, ((eW_comm LL s t s t).pow_left i).eq, Module.End.mul_apply, ih, shiftN_succ, map_smul, ← Module.End.mul_apply, ← pow_succ', pow_succ (-1 : ℚ_[p]), mul_neg_one, neg_smul]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem eJ_pow_cw (s t : Fin r) (hs : s ∈ Cs) (ht : t ∈ Cs) (hst : s < t) : ∀ (i : ℕ) (γ : Fin r → ℤ),
    ((glAct p LL K s t : Module.End ℚ_[p] (MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p])) ^ i) (cw p K γ x) =
      ((-1 : ℚ_[p]) ^ i) • ((eW p K s t) ^ i) (cw p K (shiftN γ t s i) x) := by
  intro i
  induction i with
  | zero => intro γ; simp [shiftN_zero]
  | succ i ih =>
    intro γ
    rw [pow_succ, Module.End.mul_apply, eJ_cw_lt LL hv Cs th x hx s t hs ht hst γ, map_neg,
      ← Module.End.mul_apply, ((eW_comm LL s t s t).pow_left i).eq, Module.End.mul_apply, ih, shiftN_succ, map_smul,
      ← Module.End.mul_apply, ← pow_succ', pow_succ (-1 : ℚ_[p]), mul_neg_one, neg_smul]
    push_cast
    rfl

end HW

section Strip
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}

/- English proof (translation)
Use `set D := h.totalDegree with hD`. Set `Q : ℕ → Set (Fin N × Fin r →₀ ℕ)` to `fun k => {m | ∑ v, m v ≤ D ∧ (k : ℤ) - D ≤ wt LL j c m}`. Establish `h0 : h ∈ restrictSupport ℚ_[p] (Q 0)`. Rewrite using `[mem_restrictSupport_iff]`. Introduce `m hm`.

Establish `h1 : ∑ v, m v ≤ D`. Use `le_totalDegree (Finset.mem_coe.mp hm)` as an intermediate fact. Rewrite `this` using `[Finsupp.sum_fintype _ _ (fun _ => rfl)]`. Then use the resulting hypothesis. Use `⟨h1, ?_⟩` and prove the remaining obligations. Establish `h2` using `abs_le.mp (abs_wt_le LL j c m)`.

Establish `h3 : ((∑ v, m v : ℕ) : ℤ) ≤ D` using `by exact_mod_cast h1`. Move the coercions through the operations in `at h2 h3 ⊢`. Combine the linear relations using `[h2.1]`. Establish `hs : ∀ k, ∀ x ∈ restrictSupport ℚ_[p] (Q k), glAct p LL j c d x ∈ restrictSupport ℚ_[p] (Q (k + 1))`. Introduce `k`.

Use `glAct_keep LL j c d _ _ ?_ ?_` and prove the remaining obligations. Introduce `i hi hv m hm hb`. Use `⟨by rw [sum_shift m _ _ hb]; exact hm.1, ?_⟩` and prove the remaining obligations. Rewrite using `[(wt_shift LL j c d c i hi m).1 hv hb, if_pos rfl, if_neg (Ne.symm hcd)]`. Use `hm.2` as an intermediate fact.

Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `i hi hv m hm hb`. Use `⟨by rw [sum_shift m _ _ hb]; exact hm.1, ?_⟩` and prove the remaining obligations. Rewrite using `[(wt_shift LL j c d c i hi m).2 hv hb, if_pos rfl, if_neg (Ne.symm hcd)]`.

Use `hm.2` as an intermediate fact. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hk : ∀ k, ((glAct p LL j c d : Module.End ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p])) ^ k) h ∈ restrictSupport ℚ_[p] (Q k)`. Introduce `k`.

Proceed by induction on `k with`. Consider the case `zero => exact h0`. Consider the case `succ k ih`. Rewrite using `[pow_succ', Module.End.mul_apply]`. Conclude with `hs k _ ih`.

Use `⟨2 * D + 1, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Take `⟨m, hm⟩` from `support_nonempty.mpr hne`. Establish `h1` using `hk (2 * D + 1)`. Rewrite `h1` using `[mem_restrictSupport_iff]`.

Use `replace h1 := h1 (Finset.mem_coe.mpr hm)`. Establish `h2` using `abs_le.mp (abs_wt_le LL j c m)`. Establish `h3 : ((∑ v, m v : ℕ) : ℤ) ≤ D` using `by exact_mod_cast h1.1`. Establish `h4` using `h1.2`. Move the coercions through the operations in `at h2 h3 h4`.

Combine the linear relations using `[h2.2]`.
-/
theorem glAct_nil {N : ℕ} (LL : Letters N) (j : ℕ) (c d : Fin r) (hcd : c ≠ d)
    (h : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    ∃ n : ℕ, ((glAct p LL j c d : Module.End ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p])) ^ n) h = 0 := by
  classical
  set D := h.totalDegree with hD
  let Q : ℕ → Set (Fin N × Fin r →₀ ℕ) := fun k => {m | ∑ v, m v ≤ D ∧ (k : ℤ) - D ≤ wt LL j c m}
  have h0 : h ∈ restrictSupport ℚ_[p] (Q 0) := by
    rw [mem_restrictSupport_iff]
    intro m hm
    have h1 : ∑ v, m v ≤ D := by
      have := le_totalDegree (Finset.mem_coe.mp hm)
      rwa [Finsupp.sum_fintype _ _ (fun _ => rfl)] at this
    refine ⟨h1, ?_⟩
    have h2 := abs_le.mp (abs_wt_le LL j c m)
    have h3 : ((∑ v, m v : ℕ) : ℤ) ≤ D := by exact_mod_cast h1
    push_cast at h2 h3 ⊢
    linarith [h2.1]
  have hs : ∀ k, ∀ x ∈ restrictSupport ℚ_[p] (Q k), glAct p LL j c d x ∈ restrictSupport ℚ_[p] (Q (k + 1)) := by
    intro k
    refine glAct_keep LL j c d _ _ ?_ ?_
    · intro i hi hv m hm hb
      refine ⟨by rw [sum_shift m _ _ hb]; exact hm.1, ?_⟩
      rw [(wt_shift LL j c d c i hi m).1 hv hb, if_pos rfl, if_neg (Ne.symm hcd)]
      have := hm.2
      push_cast
      linarith
    · intro i hi hv m hm hb
      refine ⟨by rw [sum_shift m _ _ hb]; exact hm.1, ?_⟩
      rw [(wt_shift LL j c d c i hi m).2 hv hb, if_pos rfl, if_neg (Ne.symm hcd)]
      have := hm.2
      push_cast
      linarith
  have hk : ∀ k, ((glAct p LL j c d : Module.End ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p])) ^ k) h ∈
      restrictSupport ℚ_[p] (Q k) := by
    intro k
    induction k with
    | zero => exact h0
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact hs k _ ih
  refine ⟨2 * D + 1, ?_⟩
  by_contra hne
  obtain ⟨m, hm⟩ := support_nonempty.mpr hne
  have h1 := hk (2 * D + 1)
  rw [mem_restrictSupport_iff] at h1
  replace h1 := h1 (Finset.mem_coe.mpr hm)
  have h2 := abs_le.mp (abs_wt_le LL j c m)
  have h3 : ((∑ v, m v : ℕ) : ℤ) ≤ D := by exact_mod_cast h1.1
  have h4 := h1.2
  push_cast at h2 h3 h4
  linarith [h2.2]

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Establish `hne : a ≠ a'` using `ne_of_lt haa`. Take `⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = β a'` from `⟨(β a').toNat, Int.toNat_of_nonneg (hβ a')⟩`. Use `set u := cw p K (shiftN β a a' k) x with hu`. Establish `hpk` using `eJ_pow_cw LL hv Cs th x hx a a' ha ha' haa k (shiftN β a a' k)`.

Rewrite `hpk` using `[shiftN_back, sub_self, shiftN_zero]`. Establish `hu0 : u ≠ 0`. Introduce `h0`. Rewrite `hpk` using `[← hu, h0, map_zero]`. Break down `smul_eq_zero.mp hpk.symm with h1 | h1` into its components or cases.

Conclude with `absurd h1 (pow_ne_zero _ (by norm_num))`. Conclude with `eW_pow_ne a a' hne k β _ (cw_mem β x) hy (le_of_eq hk) (hβ a) h1`. Establish `hpk1` using `eJ_pow_cw LL hv Cs th x hx a a' ha ha' haa (k + 1) (shiftN β a a' k)`. Establish `e1 : shiftN (shiftN β a a' k) a' a ((k + 1 : ℕ) : ℤ) = shiftW β a' a`. Rewrite using `[shiftN_back, ← shiftN_one]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, htop (shiftW β a' a) (by`. Rewrite using `[phiW_shift]`.

Establish `: ((a : ℕ) : ℤ) < ((a' : ℕ) : ℤ)` using `by exact_mod_cast haa`. Use the proof step `omega), map_zero, smul_zero] at hpk1`. Establish `hd1` using `eJ_cw_diag LL hv Cs th x hx a ha (shiftN β a a' k)`. Establish `hd2` using `eJ_cw_diag LL hv Cs th x hx a' ha' (shiftN β a a' k)`. Establish `hh : (glAct p LL K a a - glAct p LL K a' a') u = (((th a - β a - k) - (th a' - β a' + k) : ℤ) : ℚ_[p]) • u`.

Rewrite using `[LinearMap.sub_apply, hu, hd1, hd2, ← sub_smul]`. Use `congr 1`. Simplify using `only [shiftN, if_neg hne, if_neg (Ne.symm hne), if_true]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Use `hu0 (sl2_injectivity_holds ℚ_[p] _ (glAct p LL K a a') (glAct p LL K a' a) (glAct p LL K a a - glAct p LL K a' a') ?_ ?_ ?_ u _ (k + 1) hh (glAct_nil LL K a' a (Ne.symm hne) u) (by push_cast; omega) hpk1)` and prove the remaining obligations. Introduce `z`. Establish `h1` using `glAct_comm LL K a a a a' z`. Establish `h2` using `glAct_comm LL K a' a' a a' z`. Rewrite `h1` using `[if_pos rfl, if_neg (Ne.symm hne)]`.

Rewrite `h2` using `[if_neg (Ne.symm hne), if_pos rfl]`. Simplify using `only [LinearMap.sub_apply, map_sub]`. Rewrite using `[two_smul]`. Take the linear combination `(exp := 1) h1 - h2`. Introduce `z`.

Establish `h1` using `glAct_comm LL K a a a' a z`. Establish `h2` using `glAct_comm LL K a' a' a' a z`. Rewrite `h1` using `[if_neg hne, if_pos rfl]`. Rewrite `h2` using `[if_pos rfl, if_neg hne]`. Simplify using `only [LinearMap.sub_apply, map_sub]`.

Rewrite using `[two_smul]`. Take the linear combination `(exp := 1) h1 - h2`. Introduce `z`. Establish `h1` using `glAct_comm LL K a a' a' a z`. Rewrite `h1` using `[if_pos rfl, if_pos rfl]`.

Rewrite using `[LinearMap.sub_apply]`. Conclude with `h1`.
-/
theorem strip_le (LL : Letters (K + 1)) (hv : LL.vec (Fin.last K) = true) (Cs : Finset (Fin r)) (th : Fin r → ℤ)
    (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hx : x ∈ HWC p LL (K + 1) Cs th) (β : Fin r → ℤ)
    (hy : cw p K β x ≠ 0) (htop : ∀ γ, phiW β < phiW γ → cw p K γ x = 0) (hβ : ∀ c, 0 ≤ β c)
    (a a' : Fin r) (ha : a ∈ Cs) (ha' : a' ∈ Cs) (haa : a < a') : th a' ≤ th a - β a := by
  by_contra hcon
  have hne : a ≠ a' := ne_of_lt haa
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = β a' := ⟨(β a').toNat, Int.toNat_of_nonneg (hβ a')⟩
  set u := cw p K (shiftN β a a' k) x with hu
  have hpk := eJ_pow_cw LL hv Cs th x hx a a' ha ha' haa k (shiftN β a a' k)
  rw [shiftN_back, sub_self, shiftN_zero] at hpk
  have hu0 : u ≠ 0 := by
    intro h0
    rw [← hu, h0, map_zero] at hpk
    rcases smul_eq_zero.mp hpk.symm with h1 | h1
    · exact absurd h1 (pow_ne_zero _ (by norm_num))
    · exact eW_pow_ne a a' hne k β _ (cw_mem β x) hy (le_of_eq hk) (hβ a) h1
  have hpk1 := eJ_pow_cw LL hv Cs th x hx a a' ha ha' haa (k + 1) (shiftN β a a' k)
  have e1 : shiftN (shiftN β a a' k) a' a ((k + 1 : ℕ) : ℤ) = shiftW β a' a := by
    rw [shiftN_back, ← shiftN_one]; congr 1; push_cast; ring
  rw [e1, htop (shiftW β a' a) (by
    rw [phiW_shift]
    have : ((a : ℕ) : ℤ) < ((a' : ℕ) : ℤ) := by exact_mod_cast haa
    omega), map_zero, smul_zero] at hpk1
  have hd1 := eJ_cw_diag LL hv Cs th x hx a ha (shiftN β a a' k)
  have hd2 := eJ_cw_diag LL hv Cs th x hx a' ha' (shiftN β a a' k)
  have hh : (glAct p LL K a a - glAct p LL K a' a') u =
      (((th a - β a - k) - (th a' - β a' + k) : ℤ) : ℚ_[p]) • u := by
    rw [LinearMap.sub_apply, hu, hd1, hd2, ← sub_smul]
    congr 1
    simp only [shiftN, if_neg hne, if_neg (Ne.symm hne), if_true]
    push_cast
    ring
  refine hu0 (sl2_injectivity_holds ℚ_[p] _ (glAct p LL K a a') (glAct p LL K a' a) (glAct p LL K a a - glAct p LL K a' a')
    ?_ ?_ ?_ u _ (k + 1) hh (glAct_nil LL K a' a (Ne.symm hne) u) (by push_cast; omega) hpk1)
  · intro z
    have h1 := glAct_comm LL K a a a a' z
    have h2 := glAct_comm LL K a' a' a a' z
    rw [if_pos rfl, if_neg (Ne.symm hne)] at h1
    rw [if_neg (Ne.symm hne), if_pos rfl] at h2
    simp only [LinearMap.sub_apply, map_sub]
    rw [two_smul]
    linear_combination (exp := 1) h1 - h2
  · intro z
    have h1 := glAct_comm LL K a a a' a z
    have h2 := glAct_comm LL K a' a' a' a z
    rw [if_neg hne, if_pos rfl] at h1
    rw [if_pos rfl, if_neg hne] at h2
    simp only [LinearMap.sub_apply, map_sub]
    rw [two_smul]
    linear_combination (exp := 1) h1 - h2
  · intro z
    have h1 := glAct_comm LL K a a' a' a z
    rw [if_pos rfl, if_pos rfl] at h1
    rw [LinearMap.sub_apply]
    exact h1

end Strip

section OmegaTop
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}

/- English proof (translation)
Rewrite `hx` using `[FreeOf, mem_restrictSupport_iff]`. Use extensionality with `m`. Rewrite using `[coeff_pderiv, coeff_zero]`. Establish `: coeff (m + Finsupp.single v 1) x = 0`. Assume the negation of the conclusion as `hc`.

Use `hx (Finset.mem_coe.mpr (mem_support_iff.mpr hc))` as an intermediate fact. Simplify using `at this`. Rewrite using `[this, zero_mul]`.
-/
theorem pderiv_free {σ : Type} (v : σ) (x : MvPolynomial σ ℚ_[p]) (hx : x ∈ FreeOf p v) : pderiv v x = 0 := by
  classical
  rw [FreeOf, mem_restrictSupport_iff] at hx
  ext m
  rw [coeff_pderiv, coeff_zero]
  have : coeff (m + Finsupp.single v 1) x = 0 := by
    by_contra hc
    have := hx (Finset.mem_coe.mpr (mem_support_iff.mpr hc))
    simp at this
  rw [this, zero_mul]

/- English proof (translation)
Use `ProjS.eulL_of_support _ _ _ ?_` and prove the remaining obligations. Introduce `m hm`. Rewrite `hm` using `[mem_support_iff, coeff_pderiv]`. Rewrite `hP` using `[Pol, mem_restrictSupport_iff]`. Establish `h1` using `hP (Finset.mem_coe.mpr (mem_support_iff.mpr (left_ne_zero_of_mul hm))) (Fin.last K)`.

Establish `h2 : (setLast LL (o + 1)).deg (Fin.last K) = o + 1` using `by simp [setLast]`. Rewrite `h1` using `[h2]`. Simplify using `only [Finsupp.add_apply, Finset.sum_add_distrib] at h1`. Establish `h3 : ∑ c : Fin r, (Finsupp.single ((Fin.last K, a) : Fin (K + 1) × Fin r) 1) (Fin.last K, c) = 1`. Simplify using `[Finsupp.single_apply, Prod.ext_iff]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem eul_pderiv (LL : Letters (K + 1)) (o : ℕ) (a : Fin r) (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p])
    (hP : x ∈ Pol p r (setLast LL (o + 1))) :
    ProjS.eulL (fun c : Fin r => (Fin.last K, c)) (pderiv (Fin.last K, a) x) =
      ((o : ℕ) : ℚ_[p]) • pderiv (Fin.last K, a) x := by
  classical
  refine ProjS.eulL_of_support _ _ _ ?_
  intro m hm
  rw [mem_support_iff, coeff_pderiv] at hm
  rw [Pol, mem_restrictSupport_iff] at hP
  have h1 := hP (Finset.mem_coe.mpr (mem_support_iff.mpr (left_ne_zero_of_mul hm))) (Fin.last K)
  have h2 : (setLast LL (o + 1)).deg (Fin.last K) = o + 1 := by simp [setLast]
  rw [h2] at h1
  simp only [Finsupp.add_apply, Finset.sum_add_distrib] at h1
  have h3 : ∑ c : Fin r, (Finsupp.single ((Fin.last K, a) : Fin (K + 1) × Fin r) 1) (Fin.last K, c) = 1 := by
    simp [Finsupp.single_apply, Prod.ext_iff]
  omega

/- English proof (translation)
Establish `hsum : ∑ a ∈ univ.erase ρ, X (Fin.last K, a) * pderiv (Fin.last K, a) x = ((o + 1 : ℕ) : ℚ_[p]) • x`. Establish `h1` using `(pol_iff_eul _ x).mp hP (Fin.last K)`. Establish `h2 : (setLast LL (o + 1)).deg (Fin.last K) = o + 1` using `by simp [setLast]`. Rewrite `h1` using `[h2, ProjS.eulL_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ ρ), pderiv_free _ x hF, mul_zero, zero_add]`. Conclude with `h1`.

Establish `hterm : ∀ a : Fin r, Uop p LL c (univ.erase ρ) a (dW p K a x) = (((c - o : ℤ)) : ℚ_[p]) • (X (Fin.last K, a) * pderiv (Fin.last K, a) x) - ∑ b ∈ univ.erase ρ, eW p K b a (glAct p LL K a b x)`. Introduce `a`. Rewrite using `[Uop_apply]`. Establish `e0 : dW p K a x = pderiv (Fin.last K, a) x` using `rfl`. Rewrite using `[e0, eul_pderiv LL o a x hP, ← sub_smul, mul_smul_comm]`.

Use `congr 1`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations.

Rewrite using `[eW_apply]`. Use `congr 1`. Conclude with `(FockB.ops_apply_comm disj_last (FockB.pderiv_mem (last_mem a)) (glAct_mem LL K a b) x).symm`. Unfold `Omega`. Rewrite using `[LinearMap.sum_apply]`.

Simplify using `only [LinearMap.comp_apply, hterm]`. Rewrite using `[Finset.sum_sub_distrib, ← Finset.smul_sum, hsum, smul_smul]`. Use `congr 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem omega_formula (LL : Letters (K + 1)) (ρ : Fin r) (c : ℤ) (o : ℕ)
    (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hP : x ∈ Pol p r (setLast LL (o + 1)))
    (hF : x ∈ FreeOf p (Fin.last K, ρ)) :
    Omega p LL c ρ x = (((c - o) * (o + 1) : ℤ) : ℚ_[p]) • x -
      ∑ a ∈ univ.erase ρ, ∑ b ∈ univ.erase ρ, eW p K b a (glAct p LL K a b x) := by
  have hsum : ∑ a ∈ univ.erase ρ, X (Fin.last K, a) * pderiv (Fin.last K, a) x = ((o + 1 : ℕ) : ℚ_[p]) • x := by
    have h1 := (pol_iff_eul _ x).mp hP (Fin.last K)
    have h2 : (setLast LL (o + 1)).deg (Fin.last K) = o + 1 := by simp [setLast]
    rw [h2, ProjS.eulL_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ ρ), pderiv_free _ x hF, mul_zero,
      zero_add] at h1
    exact h1
  have hterm : ∀ a : Fin r, Uop p LL c (univ.erase ρ) a (dW p K a x) =
      (((c - o : ℤ)) : ℚ_[p]) • (X (Fin.last K, a) * pderiv (Fin.last K, a) x) -
        ∑ b ∈ univ.erase ρ, eW p K b a (glAct p LL K a b x) := by
    intro a
    rw [Uop_apply]
    have e0 : dW p K a x = pderiv (Fin.last K, a) x := rfl
    rw [e0, eul_pderiv LL o a x hP, ← sub_smul, mul_smul_comm]
    congr 1
    · congr 1; push_cast; ring
    · refine Finset.sum_congr rfl fun b _ => ?_
      rw [eW_apply]
      congr 1
      exact (FockB.ops_apply_comm disj_last (FockB.pderiv_mem (last_mem a)) (glAct_mem LL K a b) x).symm
  unfold Omega
  rw [LinearMap.sum_apply]
  simp only [LinearMap.comp_apply, hterm]
  rw [Finset.sum_sub_distrib, ← Finset.smul_sum, hsum, smul_smul]
  congr 2
  push_cast
  ring

def Enum {r : ℕ} (ρ : Fin r) (c : ℤ) (o : ℕ) (th β : Fin r → ℤ) : ℤ :=
  (c - o) * (o + 1) - ∑ a ∈ univ.erase ρ, ∑ b ∈ univ.erase ρ,
    ((if a = b then β a * (th a - β a) else 0) - (if a < b then (β a + 1) * β b else 0))

/- English proof (translation)
Establish `hterm : ∀ a ∈ univ.erase ρ, ∀ b ∈ univ.erase ρ, cw p K β (eW p K b a (glAct p LL K a b x)) = ((((if a = b then β a * (th a - β a) else 0) - (if a < b then (β a + 1) * β b else 0) : ℤ)) : ℚ_[p]) • cw p K β x`. Introduce `a ha b hb`. Rewrite using `[eW_apply, cw_WD, cw_glAct]`. Break down `lt_trichotomy a b with hab | hab | hab` into its components or cases. Rewrite using `[eJ_cw_lt LL hv _ th x hx a b ha hb hab, if_neg (ne_of_lt hab), if_pos hab]`.

Establish `e1 : shiftW (shiftW β a b) b a = β` using `by funext c'; simp only [shiftW]; ring`. Establish `hne : ((Fin.last K, a) : Fin (K + 1) × Fin r) ≠ (Fin.last K, b)` using `fun h => (ne_of_lt hab) (Prod.mk.inj h).2`. Rewrite using `[e1, map_neg, mul_neg, eW_apply, XDXD _ _ hne _ _ _ (WS_eig β _ (cw_mem β x) a) (WS_eig β _ (cw_mem β x) b), ← neg_smul]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Substitute `hab` using the available equality. Rewrite using `[shiftW_self, eJ_cw_diag LL hv _ th x hx a ha, Derivation.map_smul, mul_smul_comm, WS_eig β _ (cw_mem β x) a, smul_smul, if_pos rfl, if_neg (lt_irrefl a)]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[htop (shiftW β a b) (by`. Rewrite using `[phiW_shift]`. Establish `: ((b : ℕ) : ℤ) < ((a : ℕ) : ℤ)` using `by exact_mod_cast hab`. Use the proof step `omega), map_zero, map_zero, mul_zero, if_neg (ne_of_gt hab), if_neg (not_lt_of_gt hab)]`.

Simplify using the standard rewrite rules. Rewrite using `[omega_formula LL ρ c o x hP hF, map_sub, map_smul, map_sum]`. Simplify using `only [map_sum]`. Rewrite using `[Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl (fun b hb => hterm a ha b hb))]`. Simplify using `only [← Finset.sum_smul]`.

Rewrite using `[← sub_smul]`. Use `congr 1`. Unfold `Enum`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem omega_top (LL : Letters (K + 1)) (hv : LL.vec (Fin.last K) = true) (ρ : Fin r) (c : ℤ) (o : ℕ)
    (th : Fin r → ℤ) (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hP : x ∈ Pol p r (setLast LL (o + 1)))
    (hF : x ∈ FreeOf p (Fin.last K, ρ)) (hx : x ∈ HWC p LL (K + 1) (univ.erase ρ) th) (β : Fin r → ℤ)
    (htop : ∀ γ, phiW β < phiW γ → cw p K γ x = 0) :
    cw p K β (Omega p LL c ρ x) = ((Enum ρ c o th β : ℤ) : ℚ_[p]) • cw p K β x := by
  have hterm : ∀ a ∈ univ.erase ρ, ∀ b ∈ univ.erase ρ, cw p K β (eW p K b a (glAct p LL K a b x)) =
      ((((if a = b then β a * (th a - β a) else 0) - (if a < b then (β a + 1) * β b else 0) : ℤ)) : ℚ_[p]) •
        cw p K β x := by
    intro a ha b hb
    rw [eW_apply, cw_WD, cw_glAct]
    rcases lt_trichotomy a b with hab | hab | hab
    · rw [eJ_cw_lt LL hv _ th x hx a b ha hb hab, if_neg (ne_of_lt hab), if_pos hab]
      have e1 : shiftW (shiftW β a b) b a = β := by funext c'; simp only [shiftW]; ring
      have hne : ((Fin.last K, a) : Fin (K + 1) × Fin r) ≠ (Fin.last K, b) :=
        fun h => (ne_of_lt hab) (Prod.mk.inj h).2
      rw [e1, map_neg, mul_neg, eW_apply,
        XDXD _ _ hne _ _ _ (WS_eig β _ (cw_mem β x) a) (WS_eig β _ (cw_mem β x) b), ← neg_smul]
      congr 1
      push_cast
      ring
    · subst hab
      rw [shiftW_self, eJ_cw_diag LL hv _ th x hx a ha, Derivation.map_smul, mul_smul_comm,
        WS_eig β _ (cw_mem β x) a, smul_smul, if_pos rfl, if_neg (lt_irrefl a)]
      congr 1
      push_cast
      ring
    · rw [htop (shiftW β a b) (by
        rw [phiW_shift]
        have : ((b : ℕ) : ℤ) < ((a : ℕ) : ℤ) := by exact_mod_cast hab
        omega), map_zero, map_zero, mul_zero, if_neg (ne_of_gt hab), if_neg (not_lt_of_gt hab)]
      simp
  rw [omega_formula LL ρ c o x hP hF, map_sub, map_smul, map_sum]
  simp only [map_sum]
  rw [Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl (fun b hb => hterm a ha b hb))]
  simp only [← Finset.sum_smul]
  rw [← sub_smul]
  congr 1
  unfold Enum
  push_cast
  rfl

end OmegaTop

section Arith

/- English proof (translation)
Establish `hr : r - 1 + 1 = r` using `by have := ρ.isLt; omega`. Establish `h1 : ∑ a : Fin r, G (a : ℕ) = ∑ i ∈ range r, G i` using `Fin.sum_univ_eq_sum_range G r`. Establish `h2 : ∑ i ∈ range r, G i = ∑ i ∈ range (r - 1), G i + G (r - 1)`. Rewrite using `[← Finset.sum_range_succ, hr]`. Rewrite `h1` using `[← Finset.add_sum_erase _ _ (Finset.mem_univ ρ), h2, hρ]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sum_erase_last {r : ℕ} (ρ : Fin r) (hρ : (ρ : ℕ) = r - 1) (G : ℕ → ℤ) :
    ∑ a ∈ univ.erase ρ, G (a : ℕ) = ∑ i ∈ range (r - 1), G i := by
  have hr : r - 1 + 1 = r := by have := ρ.isLt; omega
  have h1 : ∑ a : Fin r, G (a : ℕ) = ∑ i ∈ range r, G i := Fin.sum_univ_eq_sum_range G r
  have h2 : ∑ i ∈ range r, G i = ∑ i ∈ range (r - 1), G i + G (r - 1) := by
    rw [← Finset.sum_range_succ, hr]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ρ), h2, hρ] at h1
  linarith

/- English proof (translation)
Set `ka : ℕ → ℤ` to `fun i => if h : i < r then th ⟨i, h⟩ - β ⟨i, h⟩ else 0`. Set `bN : ℕ → ℕ` to `fun i => if h : i < r then (β ⟨i, h⟩).toNat else 0`. Establish `hka : ∀ a : Fin r, ka (a : ℕ) = th a - β a` using `fun a => by simp only [ka, dif_pos a.isLt, Fin.eta]`. Establish `hbN : ∀ a : Fin r, ((bN (a : ℕ) : ℕ) : ℤ) = β a` using `fun a => by`. Simplify using `only [bN, dif_pos a.isLt, Fin.eta]`.

Conclude with `Int.toNat_of_nonneg (hβ a)`. Establish `hmem : ∀ i, (h : i < r - 1) → (⟨i, by omega⟩ : Fin r) ∈ univ.erase ρ`. Introduce `i h`. Use `Finset.mem_erase.mpr ⟨fun he => ?_, Finset.mem_univ _⟩` and prove the remaining obligations. Use `congrArg Fin.val he` as an intermediate fact.

Simplify using `only at this`. Use linear arithmetic over natural numbers and integers. Establish `hS : ∑ a ∈ range (r - 1), ((bN a : ℕ) : ℤ) = o + 1`. Rewrite using `[← sum_erase_last ρ hρ (fun i => ((bN i : ℕ) : ℤ)), ← hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ ρ), hβρ, zero_add]`. Conclude with `Finset.sum_congr rfl fun a _ => hbN a`.

Establish `key` using `exponent_arithmetic_holds (r - 1) ka bN c ?_ ?_ ?_`. Rewrite `key` using `[hS]`. Establish `h1 : ∑ a ∈ range (r - 1), ((bN a : ℕ) : ℤ) * ka a = ∑ a ∈ univ.erase ρ, β a * (th a - β a)`. Rewrite using `[← sum_erase_last ρ hρ (fun i => ((bN i : ℕ) : ℤ) * ka i)]`. Conclude with `Finset.sum_congr rfl fun a _ => by rw [hbN, hka]`.

Establish `h2 : ∑ b ∈ range (r - 1), ∑ a ∈ range b, (((bN a : ℕ) : ℤ) + 1) * ((bN b : ℕ) : ℤ) = ∑ a ∈ univ.erase ρ, ∑ b ∈ univ.erase ρ, (if a < b then (β a + 1) * β b else 0)`. Rewrite using `[← sum_erase_last ρ hρ (fun j => ∑ a ∈ range j, (((bN a : ℕ) : ℤ) + 1) * ((bN j : ℕ) : ℤ)), Finset.sum_comm]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Establish `hb : (b : ℕ) ≤ r - 1` using `by have := b.isLt; omega`. Establish `e1 : ∑ a ∈ range (b : ℕ), (((bN a : ℕ) : ℤ) + 1) * ((bN (b : ℕ) : ℕ) : ℤ) = ∑ a ∈ range (r - 1), (if a < (b : ℕ) then (((bN a : ℕ) : ℤ) + 1) * ((bN (b : ℕ) : ℕ) : ℤ) else 0)`.

Rewrite using `[← Finset.sum_filter]`. Use `Finset.sum_congr ?_ fun _ _ => rfl` and prove the remaining obligations. Use extensionality with `i`. Simplify using `only [Finset.mem_range, Finset.mem_filter]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[e1, ← sum_erase_last ρ hρ (fun i => if i < (b : ℕ) then (((bN i : ℕ) : ℤ) + 1) * ((bN (b : ℕ) : ℕ) : ℤ) else 0)]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[hbN, hbN]`. Simplify using `only [Fin.lt_def]`. Rewrite `key` using `[h1, h2]`.

Unfold `Enum`. Simplify using `only [Finset.sum_sub_distrib]`. Establish `h3 : ∑ a ∈ univ.erase ρ, ∑ b ∈ univ.erase ρ, (if a = b then β a * (th a - β a) else 0) = ∑ a ∈ univ.erase ρ, β a * (th a - β a)`. Use `Finset.sum_congr rfl fun a ha => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_ite_eq, if_pos ha]`.

Rewrite using `[h3]`. Establish `e2 : (c - ((o : ℤ) + 1) + 1) * ((o : ℤ) + 1) = (c - o) * (o + 1)` using `by ring`. Rewrite `key` using `[e2]`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `i hi`.

Establish `h1` using `hstrip ⟨i, by omega⟩ (hmem i (by omega)) ⟨i + 1, by omega⟩ (hmem (i + 1) hi) (by simp only [Fin.lt_def]; omega)`. Establish `h2` using `hka ⟨i, by omega⟩`. Establish `h3` using `hka ⟨i + 1, by omega⟩`. Establish `h4` using `hbN ⟨i + 1, by omega⟩`. Simplify using `only at h2 h3 h4`.

Rewrite using `[h2, h3, h4]`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `_`. Establish `h2` using `hka 0`. Establish `h4` using `hbN 0`.

Rewrite `h2`, `h4` using `[Fin.val_zero]`. Rewrite using `[h2, h4]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `: ((1 : ℕ) : ℤ) ≤ ((∑ a ∈ range (r - 1), bN a : ℕ) : ℤ)`. Use `push_cast`.

Rewrite using `[hS]`. Use `Int.natCast_nonneg o` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `this` after adjusting the coercions.
-/
theorem enum_pos {r : ℕ} [NeZero r] (ρ : Fin r) (hr : 2 ≤ r) (hρ : (ρ : ℕ) = r - 1) (c : ℤ) (o : ℕ)
    (th β : Fin r → ℤ) (hβ : ∀ a, 0 ≤ β a) (hβρ : β ρ = 0) (hsum : ∑ a, β a = o + 1) (h0 : th 0 ≤ c)
    (hstrip : ∀ a ∈ univ.erase ρ, ∀ a' ∈ univ.erase ρ, a < a' → th a' ≤ th a - β a) : 0 < Enum ρ c o th β := by
  classical
  let ka : ℕ → ℤ := fun i => if h : i < r then th ⟨i, h⟩ - β ⟨i, h⟩ else 0
  let bN : ℕ → ℕ := fun i => if h : i < r then (β ⟨i, h⟩).toNat else 0
  have hka : ∀ a : Fin r, ka (a : ℕ) = th a - β a := fun a => by simp only [ka, dif_pos a.isLt, Fin.eta]
  have hbN : ∀ a : Fin r, ((bN (a : ℕ) : ℕ) : ℤ) = β a := fun a => by
    simp only [bN, dif_pos a.isLt, Fin.eta]; exact Int.toNat_of_nonneg (hβ a)
  have hmem : ∀ i, (h : i < r - 1) → (⟨i, by omega⟩ : Fin r) ∈ univ.erase ρ := by
    intro i h
    refine Finset.mem_erase.mpr ⟨fun he => ?_, Finset.mem_univ _⟩
    have := congrArg Fin.val he
    simp only at this
    omega
  have hS : ∑ a ∈ range (r - 1), ((bN a : ℕ) : ℤ) = o + 1 := by
    rw [← sum_erase_last ρ hρ (fun i => ((bN i : ℕ) : ℤ)), ← hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ ρ),
      hβρ, zero_add]
    exact Finset.sum_congr rfl fun a _ => hbN a
  have key := exponent_arithmetic_holds (r - 1) ka bN c ?_ ?_ ?_
  · rw [hS] at key
    have h1 : ∑ a ∈ range (r - 1), ((bN a : ℕ) : ℤ) * ka a = ∑ a ∈ univ.erase ρ, β a * (th a - β a) := by
      rw [← sum_erase_last ρ hρ (fun i => ((bN i : ℕ) : ℤ) * ka i)]
      exact Finset.sum_congr rfl fun a _ => by rw [hbN, hka]
    have h2 : ∑ b ∈ range (r - 1), ∑ a ∈ range b, (((bN a : ℕ) : ℤ) + 1) * ((bN b : ℕ) : ℤ) =
        ∑ a ∈ univ.erase ρ, ∑ b ∈ univ.erase ρ, (if a < b then (β a + 1) * β b else 0) := by
      rw [← sum_erase_last ρ hρ (fun j => ∑ a ∈ range j, (((bN a : ℕ) : ℤ) + 1) * ((bN j : ℕ) : ℤ)),
        Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      have hb : (b : ℕ) ≤ r - 1 := by have := b.isLt; omega
      have e1 : ∑ a ∈ range (b : ℕ), (((bN a : ℕ) : ℤ) + 1) * ((bN (b : ℕ) : ℕ) : ℤ) =
          ∑ a ∈ range (r - 1), (if a < (b : ℕ) then (((bN a : ℕ) : ℤ) + 1) * ((bN (b : ℕ) : ℕ) : ℤ) else 0) := by
        rw [← Finset.sum_filter]
        refine Finset.sum_congr ?_ fun _ _ => rfl
        ext i
        simp only [Finset.mem_range, Finset.mem_filter]
        omega
      rw [e1, ← sum_erase_last ρ hρ
        (fun i => if i < (b : ℕ) then (((bN i : ℕ) : ℤ) + 1) * ((bN (b : ℕ) : ℕ) : ℤ) else 0)]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hbN, hbN]
      simp only [Fin.lt_def]
    rw [h1, h2] at key
    unfold Enum
    simp only [Finset.sum_sub_distrib]
    have h3 : ∑ a ∈ univ.erase ρ, ∑ b ∈ univ.erase ρ, (if a = b then β a * (th a - β a) else 0) =
        ∑ a ∈ univ.erase ρ, β a * (th a - β a) := by
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [Finset.sum_ite_eq, if_pos ha]
    rw [h3]
    have e2 : (c - ((o : ℤ) + 1) + 1) * ((o : ℤ) + 1) = (c - o) * (o + 1) := by ring
    rw [e2] at key
    linarith
  · intro i hi
    have h1 := hstrip ⟨i, by omega⟩ (hmem i (by omega)) ⟨i + 1, by omega⟩ (hmem (i + 1) hi)
      (by simp only [Fin.lt_def]; omega)
    have h2 := hka ⟨i, by omega⟩
    have h3 := hka ⟨i + 1, by omega⟩
    have h4 := hbN ⟨i + 1, by omega⟩
    simp only at h2 h3 h4
    rw [h2, h3, h4]
    linarith
  · intro _
    have h2 := hka 0
    have h4 := hbN 0
    rw [Fin.val_zero] at h2 h4
    rw [h2, h4]
    linarith
  · have : ((1 : ℕ) : ℤ) ≤ ((∑ a ∈ range (r - 1), bN a : ℕ) : ℤ) := by
      push_cast
      rw [hS]
      have := Int.natCast_nonneg o
      linarith
    exact_mod_cast this

end Arith

section Final
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}

/- English proof (translation)
Establish `hterm : ∀ a : Fin r, glAct p LL (K + 1) s t (Uop p LL c (univ.erase ρ) a (dW p K a z)) = Uop p LL c (univ.erase ρ) a (dW p K a (glAct p LL (K + 1) s t z)) - (if s = a then Uop p LL c (univ.erase ρ) a (dW p K t z) else 0) + (if t = a then Uop p LL c (univ.erase ρ) s (dW p K a z) e …`. Introduce `a`. Establish `h1` using `raising_comm_holds p K r LL c (univ.erase ρ) a s t (dW p K a z) hv hs ht`. Establish `h2 : dW p K a (glAct p LL (K + 1) s t z) = glAct p LL (K + 1) s t (dW p K a z) + (if s = a then dW p K t z else 0)` using `pderiv_glAct LL hv s t a z`. Rewrite using `[h2, map_add, ← h1]`.

Apply the tactic sequence `split_ifs <;> simp`. Unfold `Omega`. Rewrite using `[LinearMap.sum_apply, LinearMap.sum_apply, map_sum]`. Simplify using `only [LinearMap.comp_apply, hterm]`. Rewrite using `[Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq, if_pos hs, if_pos ht]`.

Normalize the expressions using the abelian group laws.
-/
theorem omega_comm (LL : Letters (K + 1)) (hv : LL.vec (Fin.last K) = true) (ρ : Fin r) (c : ℤ) (s t : Fin r)
    (hs : s ∈ univ.erase ρ) (ht : t ∈ univ.erase ρ) (z : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    glAct p LL (K + 1) s t (Omega p LL c ρ z) = Omega p LL c ρ (glAct p LL (K + 1) s t z) := by
  classical
  have hterm : ∀ a : Fin r, glAct p LL (K + 1) s t (Uop p LL c (univ.erase ρ) a (dW p K a z)) =
      Uop p LL c (univ.erase ρ) a (dW p K a (glAct p LL (K + 1) s t z)) -
        (if s = a then Uop p LL c (univ.erase ρ) a (dW p K t z) else 0) +
        (if t = a then Uop p LL c (univ.erase ρ) s (dW p K a z) else 0) := by
    intro a
    have h1 := raising_comm_holds p K r LL c (univ.erase ρ) a s t (dW p K a z) hv hs ht
    have h2 : dW p K a (glAct p LL (K + 1) s t z) =
        glAct p LL (K + 1) s t (dW p K a z) + (if s = a then dW p K t z else 0) := pderiv_glAct LL hv s t a z
    rw [h2, map_add, ← h1]
    split_ifs <;> simp
  unfold Omega
  rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  simp only [LinearMap.comp_apply, hterm]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq, if_pos hs, if_pos ht]
  abel

/- English proof (translation)
Use `glAct_keep LL j s t _ _ ?_ ?_` and prove the remaining obligations. Introduce `i _ _ m hm _`. Simplify using `only [Set.mem_ofPred_eq] at hm ⊢`. Establish `: ((i, s) : Fin N × Fin r) ≠ v` using `fun h => hs (by rw [← h])`. Simplify using `[Finsupp.single_apply, this, hm]`.

Introduce `i _ _ m hm _`. Simplify using `only [Set.mem_ofPred_eq] at hm ⊢`. Establish `: ((i, t) : Fin N × Fin r) ≠ v` using `fun h => ht (by rw [← h])`. Simplify using `[Finsupp.single_apply, this, hm]`.
-/
theorem glAct_free {N : ℕ} (LL : Letters N) (j : ℕ) (s t : Fin r) (v : Fin N × Fin r) (hs : s ≠ v.2) (ht : t ≠ v.2) :
    ∀ z ∈ FreeOf p v, glAct p LL j s t z ∈ FreeOf p v := by
  refine glAct_keep LL j s t _ _ ?_ ?_
  · intro i _ _ m hm _
    simp only [Set.mem_ofPred_eq] at hm ⊢
    have : ((i, s) : Fin N × Fin r) ≠ v := fun h => hs (by rw [← h])
    simp [Finsupp.single_apply, this, hm]
  · intro i _ _ m hm _
    simp only [Set.mem_ofPred_eq] at hm ⊢
    have : ((i, t) : Fin N × Fin r) ≠ v := fun h => ht (by rw [← h])
    simp [Finsupp.single_apply, this, hm]

/- English proof (translation)
Establish `: TypesLE p LL j Cs M ≤ (TypesLE p LL j Cs M).comap (glAct p LL j s t)` using `iSup_le fun la => iSup_le fun hla => fun z hz => Submodule.mem_iSup_of_mem la (Submodule.mem_iSup_of_mem hla (isoC_glStableC LL j Cs la s hs t ht z hz))`. Conclude with `fun z hz => this hz`.
-/
theorem typesLE_glStable {N : ℕ} [NeZero r] (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (M : WithTop ℤ) (s t : Fin r)
    (hs : s ∈ Cs) (ht : t ∈ Cs) : ∀ z ∈ TypesLE p LL j Cs M, glAct p LL j s t z ∈ TypesLE p LL j Cs M := by
  have : TypesLE p LL j Cs M ≤ (TypesLE p LL j Cs M).comap (glAct p LL j s t) :=
    iSup_le fun la => iSup_le fun hla => fun z hz =>
      Submodule.mem_iSup_of_mem la (Submodule.mem_iSup_of_mem hla (isoC_glStableC LL j Cs la s hs t ht z hz))
  exact fun z hz => this hz

end Final

/- English proof (translation)
Introduce `p _ K r _ LL ρ c o hr hρ hv x hx hΩ`. Assume the negation of the conclusion as `hx0`. Establish `h0ρ : (0 : Fin r) ∈ univ.erase ρ`. Use `Finset.mem_erase.mpr ⟨fun he => ?_, Finset.mem_univ _⟩` and prove the remaining obligations. Use `congrArg Fin.val he` as an intermediate fact.

Rewrite `this` using `[Fin.val_zero]`. Use linear arithmetic over natural numbers and integers. Use `set S : Submodule ℚ_[p] (MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) := (Pol p r (setLast LL (o + 1)) ⊓ FreeOf p (Fin.last K, ρ) ⊓ TypesLE p LL (K + 1) (univ.erase ρ) ((c : ℤ) : WithTop ℤ)) ⊓ LinearMap.ker (Omega p LL c ρ) with hS`. Establish `hmem : ∀ z, z ∈ S ↔ ((z ∈ Pol p r (setLast LL (o + 1)) ∧ z ∈ FreeOf p (Fin.last K, ρ)) ∧ z ∈ TypesLE p LL (K + 1) (univ.erase ρ) ((c : ℤ) : WithTop ℤ)) ∧ Omega p LL c ρ z = 0`. Introduce `z`.

Simplify using `only [hS, Submodule.mem_inf, LinearMap.mem_ker]`. Establish `hstab : ∀ s ∈ univ.erase ρ, ∀ t ∈ univ.erase ρ, ∀ z ∈ S, glAct p (setLast LL (o + 1)) (K + 1) s t z ∈ S`. Introduce `s hs t ht z hz`. Rewrite `hz`, the goal using `[hmem]`. Take `⟨⟨⟨h1, h2⟩, h3⟩, h4⟩` from `hz`.

Use `⟨⟨⟨glAct_pol (setLast LL (o + 1)) (K + 1) s t z h1, ?_⟩, ?_⟩, ?_⟩` and prove the remaining obligations. Conclude with `glAct_free LL (K + 1) s t _ (Finset.ne_of_mem_erase hs) (Finset.ne_of_mem_erase ht) z h2`. Conclude with `typesLE_glStable LL (K + 1) _ _ s t hs ht z h3`. Rewrite using `[glAct_setLast, ← omega_comm LL hv ρ c s t hs ht z, h4, map_zero]`. Take `⟨h, hhS, hh0, th, hhw⟩` from `exists_hwC (setLast LL (o + 1)) (K + 1) (univ.erase ρ) S (fun z hz => ((hmem z).mp hz).1.1.1) hstab x (Submodule.mem_inf.mpr ⟨hx, LinearMap.mem_ker.mpr hΩ⟩) hx0`.

Rewrite `hhw` using `[hWC_setLast]`. Take `⟨⟨⟨hP, hF⟩, hT⟩, hO⟩` from `(hmem h).mp hhS`. Establish `hth0 : th 0 ≤ c`. Use `first_weight_le_of_support LL (K + 1) (univ.erase ρ) h0ρ ((c : ℤ) : WithTop ℤ) th h hh0 (ycondC_le_supp LL (K + 1) _ _ (typesLE_le_ycondC LL (K + 1) _ h0ρ _ hT)) (Submodule.mem_inf.mp hhw).1` as an intermediate fact. Conclude with `WithTop.coe_le_coe.mp this`.

Take `⟨β, hy, htop, m, hm, hmβ⟩` from `exists_top h hh0`. Establish `hβ : ∀ a, 0 ≤ β a` using `fun a => by rw [← hmβ]; exact Int.natCast_nonneg _`. Establish `hβρ : β ρ = 0`. Rewrite `hF` using `[FreeOf, mem_restrictSupport_iff]`. Use `hF (Finset.mem_coe.mpr hm)` as an intermediate fact.

Simplify using `only [Set.mem_ofPred_eq] at this`. Rewrite using `[← hmβ]`. Simplify using `only [wp, this]`. Both sides reduce to the same expression. Establish `hsum : ∑ a, β a = o + 1`.

Rewrite `hP` using `[Pol, mem_restrictSupport_iff]`. Establish `h1` using `hP (Finset.mem_coe.mpr hm) (Fin.last K)`. Establish `h2 : (setLast LL (o + 1)).deg (Fin.last K) = o + 1` using `by simp [setLast]`. Rewrite `h1` using `[h2]`. Rewrite using `[← hmβ]`.

Simplify using `only [wp]`. Conclude with `h1` after adjusting the coercions. Establish `hE` using `enum_pos ρ hr hρ c o th β hβ hβρ hsum hth0 (fun a ha a' ha' haa => strip_le LL hv _ th h hhw β hy htop hβ a a' ha ha' haa)`. Establish `h1` using `omega_top LL hv ρ c o th h hP hF hhw β htop`. Rewrite `h1` using `[hO, map_zero]`.

Break down `smul_eq_zero.mp h1.symm with h2 | h2` into its components or cases. Use `Int.cast_eq_zero.mp h2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Conclude with `hy h2`.
-/
theorem omega_injective_holds : OmegaInj := by
  intro p _ K r _ LL ρ c o hr hρ hv x hx hΩ
  by_contra hx0
  have h0ρ : (0 : Fin r) ∈ univ.erase ρ := by
    refine Finset.mem_erase.mpr ⟨fun he => ?_, Finset.mem_univ _⟩
    have := congrArg Fin.val he
    rw [Fin.val_zero] at this
    omega
  set S : Submodule ℚ_[p] (MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :=
    (Pol p r (setLast LL (o + 1)) ⊓ FreeOf p (Fin.last K, ρ) ⊓
      TypesLE p LL (K + 1) (univ.erase ρ) ((c : ℤ) : WithTop ℤ)) ⊓ LinearMap.ker (Omega p LL c ρ) with hS
  have hmem : ∀ z, z ∈ S ↔ ((z ∈ Pol p r (setLast LL (o + 1)) ∧ z ∈ FreeOf p (Fin.last K, ρ)) ∧
      z ∈ TypesLE p LL (K + 1) (univ.erase ρ) ((c : ℤ) : WithTop ℤ)) ∧ Omega p LL c ρ z = 0 := by
    intro z
    simp only [hS, Submodule.mem_inf, LinearMap.mem_ker]
  have hstab : ∀ s ∈ univ.erase ρ, ∀ t ∈ univ.erase ρ, ∀ z ∈ S, glAct p (setLast LL (o + 1)) (K + 1) s t z ∈ S := by
    intro s hs t ht z hz
    rw [hmem] at hz ⊢
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hz
    refine ⟨⟨⟨glAct_pol (setLast LL (o + 1)) (K + 1) s t z h1, ?_⟩, ?_⟩, ?_⟩
    · exact glAct_free LL (K + 1) s t _ (Finset.ne_of_mem_erase hs) (Finset.ne_of_mem_erase ht) z h2
    · exact typesLE_glStable LL (K + 1) _ _ s t hs ht z h3
    · rw [glAct_setLast, ← omega_comm LL hv ρ c s t hs ht z, h4, map_zero]
  obtain ⟨h, hhS, hh0, th, hhw⟩ := exists_hwC (setLast LL (o + 1)) (K + 1) (univ.erase ρ) S
    (fun z hz => ((hmem z).mp hz).1.1.1) hstab x (Submodule.mem_inf.mpr ⟨hx, LinearMap.mem_ker.mpr hΩ⟩) hx0
  rw [hWC_setLast] at hhw
  obtain ⟨⟨⟨hP, hF⟩, hT⟩, hO⟩ := (hmem h).mp hhS
  have hth0 : th 0 ≤ c := by
    have := first_weight_le_of_support LL (K + 1) (univ.erase ρ) h0ρ ((c : ℤ) : WithTop ℤ) th h hh0
      (ycondC_le_supp LL (K + 1) _ _ (typesLE_le_ycondC LL (K + 1) _ h0ρ _ hT)) (Submodule.mem_inf.mp hhw).1
    exact WithTop.coe_le_coe.mp this
  obtain ⟨β, hy, htop, m, hm, hmβ⟩ := exists_top h hh0
  have hβ : ∀ a, 0 ≤ β a := fun a => by rw [← hmβ]; exact Int.natCast_nonneg _
  have hβρ : β ρ = 0 := by
    rw [FreeOf, mem_restrictSupport_iff] at hF
    have := hF (Finset.mem_coe.mpr hm)
    simp only [Set.mem_ofPred_eq] at this
    rw [← hmβ]; simp only [wp, this]; rfl
  have hsum : ∑ a, β a = o + 1 := by
    rw [Pol, mem_restrictSupport_iff] at hP
    have h1 := hP (Finset.mem_coe.mpr hm) (Fin.last K)
    have h2 : (setLast LL (o + 1)).deg (Fin.last K) = o + 1 := by simp [setLast]
    rw [h2] at h1
    rw [← hmβ]
    simp only [wp]
    exact_mod_cast h1
  have hE := enum_pos ρ hr hρ c o th β hβ hβρ hsum hth0
    (fun a ha a' ha' haa => strip_le LL hv _ th h hhw β hy htop hβ a a' ha ha' haa)
  have h1 := omega_top LL hv ρ c o th h hP hF hhw β htop
  rw [hO, map_zero] at h1
  rcases smul_eq_zero.mp h1.symm with h2 | h2
  · have := Int.cast_eq_zero.mp h2
    omega
  · exact hy h2

end Formalism.InvariantFactorPaths.L4
