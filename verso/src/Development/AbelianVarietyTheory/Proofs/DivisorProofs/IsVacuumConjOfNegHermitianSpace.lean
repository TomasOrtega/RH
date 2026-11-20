import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.VacConj
variable {D : D7}
/- English proof (translation)
Distinguish the cases in `h : IsUnit A.det`. Conclude with `Matrix.inv_eq_left_inv (by rw [neg_mul_neg, Matrix.nonsing_inv_mul A h])`. Establish `h' : ¬ IsUnit (-A).det`. Rewrite using `[Matrix.det_neg]`. Introduce `hu`.

Conclude with `h (isUnit_of_mul_isUnit_right hu)`. Rewrite using `[Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.nonsing_inv_apply_not_isUnit _ h', neg_zero]`.
-/
theorem inv_neg' {n : ℕ} (A : Matrix (Fin n) (Fin n) D.host.E) : (-A)⁻¹ = -A⁻¹ := by
  by_cases h : IsUnit A.det
  · exact Matrix.inv_eq_left_inv (by rw [neg_mul_neg, Matrix.nonsing_inv_mul A h])
  · have h' : ¬ IsUnit (-A).det := by
      rw [Matrix.det_neg]
      intro hu
      exact h (isUnit_of_mul_isUnit_right hu)
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.nonsing_inv_apply_not_isUnit _ h', neg_zero]

/- English proof (translation)
Establish `h1 : ψ (-x) * ψ x = 1` using `by rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]`. Establish `h2 : star (ψ (-x)) * ψ (-x) = 1`. Rewrite using `[Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, h]`. Simplify using the standard rewrite rules. Combine the equalities or inequalities in the displayed calculation.
-/
theorem star_char' {R : Type} [CommRing R] (ψ : AddChar R ℂ) (h : ∀ x, ‖ψ x‖ = 1) (x : R) :
    star (ψ (-x)) = ψ x := by
  have h1 : ψ (-x) * ψ x = 1 := by rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  have h2 : star (ψ (-x)) * ψ (-x) = 1 := by
    rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, h]; simp
  calc star (ψ (-x)) = star (ψ (-x)) * (ψ (-x) * ψ x) := by rw [h1, mul_one]
    _ = ψ x := by rw [← mul_assoc, h2, one_mul]

/- English proof (translation)
Unfold `hO`. Rewrite using `[negSp_gram, inv_neg']`. Simplify using `only [Matrix.neg_apply, map_neg, neg_mul, Finset.sum_neg_distrib]`.
-/
theorem hO_neg (S T : HSp D) (x y : WO S T) : hO (negSp S) T x y = -hO S T x y := by
  unfold hO
  rw [negSp_gram, inv_neg']
  simp only [Matrix.neg_apply, map_neg, neg_mul, Finset.sum_neg_distrib]

/- English proof (translation)
Unfold `symplOH symplO`. Rewrite using `[hO_neg, mul_neg, map_neg, mul_neg]`.
-/
theorem symplOH_neg (S T : HSp D) (x y : WO S T) : symplOH (negSp S) T x y = -symplOH S T x y := by
  unfold symplOH symplO
  rw [hO_neg, mul_neg, map_neg, mul_neg]

/- English proof (translation)
Use function extensionality and compare the values at `w`. Simplify using `only [heisO, symplOH_neg, map_mul]`. Rewrite using `[← Complex.star_def, star_char' ψ hψ]`.
-/
theorem heisO_conj (ψ : AddChar (AF D.host.F) ℂ) (hψ : ∀ x, ‖ψ x‖ = 1) (S T : HSp D) (u : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T u (fun w => starRingEnd ℂ (f w)) = fun w => starRingEnd ℂ (heisO ψ (negSp S) T u f w) := by
  funext w
  simp only [heisO, symplOH_neg, map_mul]
  rw [← Complex.star_def, star_char' ψ hψ]

/- English proof (translation)
Establish `hL : IsLineAt θ τ z (lineAt θ τ z)` using `Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ m n τ z)`. Establish `hL0 : IsLineAt θ τ (-z) (lineAt θ τ (-z))` using `Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ m n τ (-z))`. Establish `hN : IsLineAt θ τ (-z) (-lineAt θ τ z)`. Use `⟨continuous_neg.comp hL.1, fun t => ?_, fun t τ' => ?_⟩` and prove the remaining obligations. Rewrite using `[AddMonoidHom.neg_apply, Matrix.map_neg _ (fun a => RingHom.map_neg (finPart D) a), hL.2.1 t, neg_zero]`.

Use `hL.2.2 t τ'` as an intermediate fact. Establish `e : compAt θ τ' ((-lineAt θ τ z) t) = -compAt θ τ' (lineAt θ τ z t)`. Unfold `compAt`. Rewrite using `[AddMonoidHom.neg_apply, Matrix.map_neg _ (fun a => by rw [RingHom.map_neg, RingHom.map_neg])]`. Rewrite using `[e, this]`.

Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[GlobalTheory.RealLineAt.lineAt_unique D θ hθ m n τ (-z) _ _ hL0 hN]`. Simplify using the standard rewrite rules.
-/
theorem lineAt_neg {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (τ : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ) (t : ℝ) :
    lineAt θ τ (-z) t = lineAt θ τ z (-t) := by
  have hL : IsLineAt θ τ z (lineAt θ τ z) := Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ m n τ z)
  have hL0 : IsLineAt θ τ (-z) (lineAt θ τ (-z)) :=
    Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ m n τ (-z))
  have hN : IsLineAt θ τ (-z) (-lineAt θ τ z) := by
    refine ⟨continuous_neg.comp hL.1, fun t => ?_, fun t τ' => ?_⟩
    · rw [AddMonoidHom.neg_apply, Matrix.map_neg _ (fun a => RingHom.map_neg (finPart D) a), hL.2.1 t, neg_zero]
    · have := hL.2.2 t τ'
      have e : compAt θ τ' ((-lineAt θ τ z) t) = -compAt θ τ' (lineAt θ τ z t) := by
        unfold compAt
        rw [AddMonoidHom.neg_apply, Matrix.map_neg _ (fun a => by rw [RingHom.map_neg, RingHom.map_neg])]
      rw [e, this]
      split_ifs <;> simp
  rw [GlobalTheory.RealLineAt.lineAt_unique D θ hθ m n τ (-z) _ _ hL0 hN]
  simp

/- English proof (translation)
Unfold `Formalism.IndefR.Datum.dRho`. Repeatedly rewrite using `[lineAt_neg hθ]`. Rewrite using `[deriv_comp_neg (f := fun t => hs (lineAt θ τ z t) f x), neg_zero]`.
-/
theorem dRho_neg {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ))
    (τ : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ) (f : Mx D m n → ℂ) (x : Mx D m n) :
    Formalism.IndefR.Datum.dRho hs θ τ (-z) f x = -Formalism.IndefR.Datum.dRho hs θ τ z f x := by
  unfold Formalism.IndefR.Datum.dRho
  simp_rw [lineAt_neg hθ]
  rw [deriv_comp_neg (f := fun t => hs (lineAt θ τ z t) f x), neg_zero]

/- English proof (translation)
Unfold `Formalism.IndefR.Datum.dRho`. Repeatedly rewrite using `[heisO_conj ψ hψ]`. Conclude with `deriv.star`.
-/
theorem dRho_conj (ψ : AddChar (AF D.host.F) ℂ) (hψ : ∀ x, ‖ψ x‖ = 1) (θ : InfFam D) (S T : HSp D) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (f : WO S T → ℂ) (x : WO S T) :
    Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z (fun w => starRingEnd ℂ (f w)) x =
      starRingEnd ℂ (Formalism.IndefR.Datum.dRho (heisO ψ (negSp S) T) θ τ z f x) := by
  unfold Formalism.IndefR.Datum.dRho
  simp_rw [heisO_conj ψ hψ]
  exact deriv.star

/- English proof (translation)
Unfold `cplxO`. Rewrite using `[Matrix.mul_neg, smul_neg]`.
-/
theorem cplxO_neg {m n : ℕ} (sS : Matrix (Fin n) (Fin n) ℂ) (sT : Matrix (Fin m) (Fin m) ℂ) (z : Matrix (Fin m) (Fin n) ℂ) :
    cplxO (-sS) sT z = -cplxO sS sT z := by
  unfold cplxO
  rw [Matrix.mul_neg, smul_neg]

/- English proof (translation)
Unfold `latO`. Rewrite using `[AddSubgroup.closure_le]`. Introduce and unpack `w ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩`. Rewrite using `[← neg_neg (Matrix.of _)]`. Use `neg_mem (AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, ?_⟩)` and prove the remaining obligations.

Use function extensionality and compare the values at `i j`. Simplify using `[negSp_gram, Finset.sum_neg_distrib, TensorProduct.tmul_neg]`.
-/
theorem latO_le (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) : latO S T LS LT P ≤ latO (negSp S) T LS LT P := by
  unfold latO
  rw [AddSubgroup.closure_le]
  rintro w ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
  rw [← neg_neg (Matrix.of _)]
  refine neg_mem (AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, ?_⟩)
  funext i j
  simp [negSp_gram, Finset.sum_neg_distrib, TensorProduct.tmul_neg]

end GlobalTheory.VacConj

namespace GlobalTheory.VacConj

/- English proof (translation)
Introduce and unpack `⟨hψ, hv⟩`. Establish `hn : ∀ x, ‖ψ x‖ = 1` using `hψ.1.2.1`. Establish `hθ : IsInfFam θ` using `hv.inf`. Use `⟨hψ, ⟨hθ, ⟨fun γ w => ?_, ?_, ?_, ?_⟩, ⟨fun u hu => ?_, fun e he u hu hh => ?_⟩, fun τ z => ?_, ?_⟩⟩` and prove the remaining obligations. Establish `h` using `hv.theta.quasi γ w show starRingEnd ℂ (f (ratW T S γ + w)) = _`.

Rewrite using `[show f (ratW T S γ + w) = _ from h, map_mul, symplOH_neg, ← Complex.star_def, star_char' ψ hn]`. Both sides reduce to the same expression. Take `⟨U, hU, hUf⟩` from `hv.theta.level`. Conclude with `⟨U, hU, fun u hu hu' => by rw [heisO_conj ψ hn, hUf u hu hu']⟩`. Conclude with `Complex.continuous_conj.comp hv.theta.cont`.

Introduce `k L hL hL' w`. Conclude with `(Complex.conjCLE.contDiff.comp (hv.theta.smooth k L hL hL' w) :)`. Rewrite using `[heisO_conj ψ hn, hv.lat.1 u (latO_le S T LS LT _ hu)]`. Rewrite using `[heisO_conj ψ hn, hv.lat.2 e he u (latO_le S T LS LT _ hu) hh]`. Use function extensionality and compare the values at `x`.

Establish `h` using `congrFun (hv.fock τ z) x`. Simplify using `only [annih, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h ⊢`. Rewrite `h` using `[cplxO_neg, dRho_neg hθ]`. Rewrite using `[dRho_conj ψ hn, dRho_conj ψ hn]`. Establish `h'` using `congrArg (starRingEnd ℂ) h`.

Simplify using `only [map_add, map_mul, map_neg, Complex.conj_I, map_zero] at h'`. Take the linear combination `h'`. Take `⟨h1, h2⟩` from `hv.norm`. Use `⟨h1, fun p hp => ?_⟩` and prove the remaining obligations. Use `h2 p hp` as an intermediate fact.

Unfold `nrm2 at this ⊢`. Simplify using `only [Complex.norm_conj]`. Conclude with `this`.
-/
theorem isVacO_conj_negSp {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (f : WO (negSp S) T → ℂ) :
    IsVacO ψ θ (negSp S) T (fun τ => -sS τ) sT LS LT f → IsVacO ψ θ S T sS sT LS LT (fun w => starRingEnd ℂ (f w)) := by
  rintro ⟨hψ, hv⟩
  have hn : ∀ x, ‖ψ x‖ = 1 := hψ.1.2.1
  have hθ : IsInfFam θ := hv.inf
  refine ⟨hψ, ⟨hθ, ⟨fun γ w => ?_, ?_, ?_, ?_⟩, ⟨fun u hu => ?_, fun e he u hu hh => ?_⟩, fun τ z => ?_, ?_⟩⟩
  · have h := hv.theta.quasi γ w
    show starRingEnd ℂ (f (ratW T S γ + w)) = _
    rw [show f (ratW T S γ + w) = _ from h, map_mul, symplOH_neg, ← Complex.star_def, star_char' ψ hn]
    rfl
  · obtain ⟨U, hU, hUf⟩ := hv.theta.level
    exact ⟨U, hU, fun u hu hu' => by rw [heisO_conj ψ hn, hUf u hu hu']⟩
  · exact Complex.continuous_conj.comp hv.theta.cont
  · intro k L hL hL' w
    exact (Complex.conjCLE.contDiff.comp (hv.theta.smooth k L hL hL' w) :)
  · rw [heisO_conj ψ hn, hv.lat.1 u (latO_le S T LS LT _ hu)]
  · rw [heisO_conj ψ hn, hv.lat.2 e he u (latO_le S T LS LT _ hu) hh]
  · funext x
    have h := congrFun (hv.fock τ z) x
    simp only [annih, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h ⊢
    rw [cplxO_neg, dRho_neg hθ] at h
    rw [dRho_conj ψ hn, dRho_conj ψ hn]
    have h' := congrArg (starRingEnd ℂ) h
    simp only [map_add, map_mul, map_neg, Complex.conj_I, map_zero] at h'
    linear_combination h'
  · obtain ⟨h1, h2⟩ := hv.norm
    refine ⟨h1, fun p hp => ?_⟩
    have := h2 p hp
    unfold nrm2 at this ⊢
    simp only [Complex.norm_conj]
    exact this

end GlobalTheory.VacConj
