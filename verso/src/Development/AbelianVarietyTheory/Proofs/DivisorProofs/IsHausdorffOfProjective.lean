import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNatura

set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

namespace GlobalTheory.CEval

/- English proof (translation)
Take `⟨s, hs⟩` from `Module.projective_def'.1 (inferInstance : Module.Projective O M)`. Establish `h0 : s y = 0`. Use extensionality with `i`. Use `eq_of_forall_dvd p fun m => ?_` and prove the remaining obligations. Take `⟨z, hz⟩` from `h m`.

Rewrite using `[hz, map_smul, Finsupp.smul_apply, smul_eq_mul, Finsupp.coe_zero, Pi.zero_apply, sub_zero]`. Conclude with `dvd_mul_right _ _`. Use `LinearMap.congr_fun hs y` as an intermediate fact. Rewrite `this` using `[LinearMap.comp_apply, h0, map_zero, LinearMap.id_apply]`. Conclude with `this.symm`.
-/
theorem eq_zero_of_projective {O M : Type} [CommRing O] [AddCommGroup M] [Module O M]
    [Module.Projective O M] (p : ℕ) [IsHausdorff (Ideal.span {(p : O)}) O] (y : M)
    (h : ∀ m : ℕ, ∃ z : M, y = ((p : O) ^ m) • z) : y = 0 := by
  obtain ⟨s, hs⟩ := Module.projective_def'.1 (inferInstance : Module.Projective O M)
  have h0 : s y = 0 := by
    ext i
    refine eq_of_forall_dvd p fun m => ?_
    obtain ⟨z, hz⟩ := h m
    rw [hz, map_smul, Finsupp.smul_apply, smul_eq_mul, Finsupp.coe_zero, Pi.zero_apply, sub_zero]
    exact dvd_mul_right _ _
  have := LinearMap.congr_fun hs y
  rw [LinearMap.comp_apply, h0, map_zero, LinearMap.id_apply] at this
  exact this.symm

/- English proof (translation)
Use `⟨fun y hy => eq_zero_of_projective (O := O) p y fun m => ?_⟩` and prove the remaining obligations. Use `dvd_of_smodEq p m (hy m)` as an intermediate fact. Rewrite `this` using `[sub_zero]`. Take `⟨z, hz⟩` from `this`. Use `⟨z, ?_⟩` and prove the remaining obligations.

Rewrite using `[hz, Algebra.smul_def, map_pow, map_natCast]`.
-/
theorem isHausdorff_of_projective {O A : Type} [CommRing O] [CommRing A] [Algebra O A]
    [Module.Projective O A] (p : ℕ) [IsHausdorff (Ideal.span {(p : O)}) O] :
    IsHausdorff (Ideal.span {(p : A)}) A := by
  refine ⟨fun y hy => eq_zero_of_projective (O := O) p y fun m => ?_⟩
  have := dvd_of_smodEq p m (hy m)
  rw [sub_zero] at this
  obtain ⟨z, hz⟩ := this
  refine ⟨z, ?_⟩
  rw [hz, Algebra.smul_def, map_pow, map_natCast]

/- English proof (translation)
Use `⟨fun i => by rw [AlgHom.comp_apply, h.1], fun m => ?_⟩` and prove the remaining obligations. Take `⟨N, hN⟩` from `h.2 m`. Use `⟨N, fun f hf => ?_⟩` and prove the remaining obligations. Use `map_dvd g (hN f hf)` as an intermediate fact. Rewrite `this` using `[map_pow, map_natCast]`. Then use the resulting hypothesis.
-/
theorem isEval_comp {σ R A A' : Type} [CommRing R] [CommRing A] [CommRing A'] [Algebra R A]
    [Algebra R A'] (p : ℕ) {x : σ → A} {E : MvPowerSeries σ R →ₐ[R] A} (h : IsEval p x E)
    (g : A →ₐ[R] A') : IsEval p (fun i => g (x i)) (g.comp E) := by
  refine ⟨fun i => by rw [AlgHom.comp_apply, h.1], fun m => ?_⟩
  obtain ⟨N, hN⟩ := h.2 m
  refine ⟨N, fun f hf => ?_⟩
  have := map_dvd g (hN f hf)
  rwa [map_pow, map_natCast] at this

/- English proof (translation)
Establish `hs : HasSubst u` using `hasSubst_of_constantCoeff_zero hu`. Rewrite using `[← coe_substAlgHom hs]`. Conclude with `ext_of_cont p ((E.comp (substAlgHom hs)).toRingHom) E'.toRingHom (fun c => by show E (substAlgHom hs (C c)) = E' (C c)`. Rewrite using `[c_eq_algebraMap, AlgHom.commutes, AlgHom.commutes, AlgHom.commutes])`. Use the proof step `(fun j => by show E (substAlgHom hs (X j)) = E' (X j)`.

Rewrite using `[substAlgHom_X, hE'.1])`. Use the proof step `(fun m => by`. Take `⟨N, hN⟩` from `hE.2 m`. Use `⟨N, fun f hf => ?_⟩` and prove the remaining obligations. Use `show (p : A) ^ m ∣ E (substAlgHom hs f)`.

Rewrite using `[coe_substAlgHom]`. Use `hN _ fun α hα => coeff_of_lt_order ?_` and prove the remaining obligations. Establish `h1 : (1 : ℕ∞) ≤ ⨅ j, (u j).order` using `le_iInf fun j => one_le_order_iff_constCoeff_eq_zero.2 (hu j)`. Establish `h2 : (N : ℕ∞) ≤ f.order` using `nat_le_order hf`. Combine the equalities or inequalities in the displayed calculation.

Use the proof step `hE'.2 f`.
-/
theorem eval_subst {σ τ R A : Type} [Fintype σ] [Fintype τ] [CommRing R] [CommRing A]
    [Algebra R A] (p : ℕ) [IsHausdorff (Ideal.span {(p : A)}) A] {x : σ → A}
    {E : MvPowerSeries σ R →ₐ[R] A} (hE : IsEval p x E) (u : τ → MvPowerSeries σ R)
    (E' : MvPowerSeries τ R →ₐ[R] A) (hu : ∀ j, constantCoeff (u j) = 0)
    (hE' : IsEval p (fun j => E (u j)) E') (f : MvPowerSeries τ R) : E (subst u f) = E' f := by
  have hs : HasSubst u := hasSubst_of_constantCoeff_zero hu
  rw [← coe_substAlgHom hs]
  exact ext_of_cont p ((E.comp (substAlgHom hs)).toRingHom) E'.toRingHom
    (fun c => by
      show E (substAlgHom hs (C c)) = E' (C c)
      rw [c_eq_algebraMap, AlgHom.commutes, AlgHom.commutes, AlgHom.commutes])
    (fun j => by
      show E (substAlgHom hs (X j)) = E' (X j)
      rw [substAlgHom_X, hE'.1])
    (fun m => by
      obtain ⟨N, hN⟩ := hE.2 m
      refine ⟨N, fun f hf => ?_⟩
      show (p : A) ^ m ∣ E (substAlgHom hs f)
      rw [coe_substAlgHom]
      refine hN _ fun α hα => coeff_of_lt_order ?_
      have h1 : (1 : ℕ∞) ≤ ⨅ j, (u j).order :=
        le_iInf fun j => one_le_order_iff_constCoeff_eq_zero.2 (hu j)
      have h2 : (N : ℕ∞) ≤ f.order := nat_le_order hf
      calc (α.degree : ℕ∞) < N := by exact_mod_cast hα
        _ = 1 * N := (one_mul _).symm
        _ ≤ (⨅ j, (u j).order) * f.order := mul_le_mul' h1 h2
        _ ≤ (subst u f).order := le_order_subst hs f)
    hE'.2 f

end GlobalTheory.CEval

namespace GlobalTheory.QLog.Chart

open GlobalTheory.CEval

variable {p : ℕ} {O : Type} [CommRing O] [IsHausdorff (Ideal.span {(p : O)}) O]
  {G : PDivGroup p O} {d : ℕ} (c : Chart G d)

omit c in
/- English proof (translation)
The claim follows from `isHausdorff_of_projective (O := O) p`.
-/
theorem isHausdorff₂ (G : PDivGroup p O) (n : ℕ) :
    IsHausdorff (Ideal.span {(p : G.A n ⊗[O] G.A n)}) (G.A n ⊗[O] G.A n) :=
  isHausdorff_of_projective (O := O) p

/- English proof (translation)
Use `haveI := isHausdorff₂ G n`. Establish `h` using `isEval_comp p (c.isEval n) (Bialgebra.comulAlgHom O (G.A n))`. Rewrite using `[eval_subst p (c.isEval₂ n) c.μ ((Bialgebra.comulAlgHom O (G.A n)).comp (c.ev n)) c.isLaw.const ?_ s]`. Both sides reduce to the same expression. Use `h using 2 with j` and compare the differences between its conclusion and the goal.

Rewrite using `[c.comul n j]`. Both sides reduce to the same expression.
-/
theorem ev₂_subst_μ (n : ℕ) (s : MvPowerSeries (Fin d) O) :
    c.ev₂ n (subst c.μ s) = Coalgebra.comul (R := O) (c.ev n s) := by
  haveI := isHausdorff₂ G n
  have h := isEval_comp p (c.isEval n) (Bialgebra.comulAlgHom O (G.A n))
  rw [eval_subst p (c.isEval₂ n) c.μ ((Bialgebra.comulAlgHom O (G.A n)).comp (c.ev n))
    c.isLaw.const ?_ s]
  · rfl
  convert h using 2 with j
  rw [c.comul n j]
  rfl

/- English proof (translation)
Use `haveI := isHausdorff₂ G n`. Establish `h` using `isEval_comp p (c.isEval n) (Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := G.A n) (B := G.A n))`. Rewrite using `[inL, eval_subst p (c.isEval₂ n) (fun i => X (Sum.inl i)) ((Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := G.A n) (B := G.A n)).comp (c.ev n)) (fun _ => constantCoeff_X _) ?_ s]`. Both sides reduce to the same expression. Conclude with `⟨fun j => (h.1 j).trans ((c.isEval₂ n).1 (Sum.inl j)).symm, h.2⟩`.
-/
theorem ev₂_inL (n : ℕ) (s : MvPowerSeries (Fin d) O) :
    c.ev₂ n (inL s) = c.ev n s ⊗ₜ[O] (1 : G.A n) := by
  haveI := isHausdorff₂ G n
  have h := isEval_comp p (c.isEval n) (Algebra.TensorProduct.includeLeft (R := O) (S := O)
    (A := G.A n) (B := G.A n))
  rw [inL, eval_subst p (c.isEval₂ n) (fun i => X (Sum.inl i))
    ((Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := G.A n) (B := G.A n)).comp (c.ev n))
    (fun _ => constantCoeff_X _) ?_ s]
  · rfl
  exact ⟨fun j => (h.1 j).trans ((c.isEval₂ n).1 (Sum.inl j)).symm, h.2⟩

/- English proof (translation)
Use `haveI := isHausdorff₂ G n`. Establish `h` using `isEval_comp p (c.isEval n) (Algebra.TensorProduct.includeRight (R := O) (A := G.A n) (B := G.A n))`. Rewrite using `[inR, eval_subst p (c.isEval₂ n) (fun i => X (Sum.inr i)) ((Algebra.TensorProduct.includeRight (R := O) (A := G.A n) (B := G.A n)).comp (c.ev n)) (fun _ => constantCoeff_X _) ?_ s]`. Both sides reduce to the same expression. Use `h using 2 with j` and compare the differences between its conclusion and the goal.

Rewrite using `[(c.isEval₂ n).1]`. Both sides reduce to the same expression.
-/
theorem ev₂_inR (n : ℕ) (s : MvPowerSeries (Fin d) O) :
    c.ev₂ n (inR s) = (1 : G.A n) ⊗ₜ[O] c.ev n s := by
  haveI := isHausdorff₂ G n
  have h := isEval_comp p (c.isEval n) (Algebra.TensorProduct.includeRight (R := O)
    (A := G.A n) (B := G.A n))
  rw [inR, eval_subst p (c.isEval₂ n) (fun i => X (Sum.inr i))
    ((Algebra.TensorProduct.includeRight (R := O) (A := G.A n) (B := G.A n)).comp (c.ev n))
    (fun _ => constantCoeff_X _) ?_ s]
  · rfl
  convert h using 2 with j
  rw [(c.isEval₂ n).1]
  rfl

end GlobalTheory.QLog.Chart

namespace GlobalTheory.QLog.Chart

/- English proof (translation)
Introduce `p _ C _ _ _ v O _ _ _ _ _ _ G d c n s`. Rewrite using `[cob1, map_sub, map_sub, c.ev₂_subst_μ, c.ev₂_inL, c.ev₂_inR]`. Normalize the expressions using the abelian group laws.
-/
theorem comul_ev : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (n : ℕ) (s : MvPowerSeries (Fin d) O), Coalgebra.comul (R := O) (c.ev n s) = c.ev n s ⊗ₜ[O] (1 : G.A n) + (1 : G.A n) ⊗ₜ[O] c.ev n s + c.ev₂ n (cob1 c.μ s) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ G d c n s
  rw [cob1, map_sub, map_sub, c.ev₂_subst_μ, c.ev₂_inL, c.ev₂_inR]
  abel

end GlobalTheory.QLog.Chart
