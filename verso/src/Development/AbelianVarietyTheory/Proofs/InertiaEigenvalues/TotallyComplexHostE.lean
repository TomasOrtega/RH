import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JumpDictCrysAtOfWeights
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Formalism.LocalToGlobal.UnitaryNorms.CharShare

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary

namespace GlobalTheory.BlockCharInf

open Formalism.L2.Host Formalism.FrobeniusOrbits

/- English proof (translation)
Take `⟨n, hn, h⟩` from `h`. Take `⟨n', hn', h'⟩` from `h'`. Use `⟨n + n', fun i => by simp [hn, hn', mul_add], fun k => ?_⟩` and prove the remaining obligations. Rewrite using `[HChar.inf_mul, Units.val_mul, h k, h' k, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations.

Establish `hne : φ i k ≠ 0` using `by simp`. Rewrite using `[Pi.add_apply, zpow_add₀ (div_ne_zero hne (by exact_mod_cast norm_ne_zero_iff.2 hne))]`.
-/
theorem hasInfQ_mul' {L I : Type} [Field L] [NumberField L] [Fintype I] {φ : I → L →+* ℂ} {χ χ' : HChar L}
    {a a' : I → ℚ} (h : χ.HasInfQ φ a) (h' : χ'.HasInfQ φ a') : (χ * χ').HasInfQ φ (a + a') := by
  obtain ⟨n, hn, h⟩ := h
  obtain ⟨n', hn', h'⟩ := h'
  refine ⟨n + n', fun i => by simp [hn, hn', mul_add], fun k => ?_⟩
  rw [HChar.inf_mul, Units.val_mul, h k, h' k, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hne : φ i k ≠ 0 := by simp
  rw [Pi.add_apply, zpow_add₀ (div_ne_zero hne (by exact_mod_cast norm_ne_zero_iff.2 hne))]

/- English proof (translation)
Take `⟨n, hn, h⟩` from `h`. Use `⟨-n, fun i => by simp [hn], fun k => ?_⟩` and prove the remaining obligations. Rewrite using `[HChar.inf_inv, Units.val_inv_eq_inv_val, h k, ← Finset.prod_inv_distrib]`. Simplify using the standard rewrite rules.
-/
theorem hasInfQ_inv' {L I : Type} [Field L] [NumberField L] [Fintype I] {φ : I → L →+* ℂ} {χ : HChar L}
    {a : I → ℚ} (h : χ.HasInfQ φ a) : (χ⁻¹).HasInfQ φ (-a) := by
  obtain ⟨n, hn, h⟩ := h
  refine ⟨-n, fun i => by simp [hn], fun k => ?_⟩
  rw [HChar.inf_inv, Units.val_inv_eq_inv_val, h k, ← Finset.prod_inv_distrib]
  simp

instance totallyComplexHostE {R : Ranks} (H : Formalism.BasicNotions.Host R) : IsTotallyComplex H.E := by
  haveI := H.isCMField_hostE
  infer_instance

/- English proof (translation)
Use `D.nd.j_range i` as an intermediate fact. Simplify using `only [liftIdx]`. Use linear arithmetic over natural numbers and integers.
-/
theorem liftIdx_succ (D : D7) (i : D.nd.Loc) : (liftIdx D i).1 + 1 = D.nd.j i := by
  have := D.nd.j_range i
  simp only [liftIdx]
  omega

/- English proof (translation)
Take `⟨n, hn, ho⟩` from `Tp.xi_fin μ`. Establish `h1 : (Tp.tup μ j).HasInfQ (embPsi D.host) (fun g => -eExp D j g)` using `(C.isMu0 j).inf.mul_triv (HChar.inf_eq_one_of_order hn ho)`. Establish `h2 : (C.eta⁻¹).HasInfQ (embPsi D.host) (-(fun _ => 1 / 2))` using `hasInfQ_inv' ⟨fun _ => 1, fun _ => by norm_num, C.isEta.inf⟩`. Use `hasInfQ_mul' h1 h2 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `g`.

Simplify using `only [Pi.add_apply, Pi.neg_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem block_hasInfQ (D : D7) (C : CharFrame D) (nch : NChoice D) (Tp : TupTied D C nch) (μ : D.what₂.Tup)
    (j : Fin D.R.m) :
    (Tp.tup μ j * C.eta⁻¹).HasInfQ (embPsi D.host) (fun g => -eExp D j g - 1 / 2) := by
  obtain ⟨n, hn, ho⟩ := Tp.xi_fin μ
  have h1 : (Tp.tup μ j).HasInfQ (embPsi D.host) (fun g => -eExp D j g) :=
    (C.isMu0 j).inf.mul_triv (HChar.inf_eq_one_of_order hn ho)
  have h2 : (C.eta⁻¹).HasInfQ (embPsi D.host) (-(fun _ => 1 / 2)) :=
    hasInfQ_inv' ⟨fun _ => 1, fun _ => by norm_num, C.isEta.inf⟩
  convert hasInfQ_mul' h1 h2 using 1
  funext g
  simp only [Pi.add_apply, Pi.neg_apply]
  ring

/- English proof (translation)
Introduce `D C nch Tp N i ρ`. Establish `he : (N.e1 (D.naut.tw (D.naut.muC i) D.naut.etaTinv)).1 = Tp.tup (D.nd.mu i) (liftIdx D i) * C.eta⁻¹`. Rewrite using `[N.tw, N.muC i (liftIdx D i) (liftIdx_succ D i), N.etaTinv]`. Establish `hI` using `block_hasInfQ D C nch Tp (D.nd.mu i) (liftIdx D i)`. Rewrite `hI` using `[← he]`.

Take `⟨h1, h2⟩` from `N.infG _ _ hI (D.eTau ρ)`. Establish `hval : eExp D (liftIdx D i) (D.eTau ρ) = (D.hc ρ).e (liftIdx D i)`. Simplify using `[eExp]`. Establish `hconj : embOver D ρ true = (starRingEnd ℂ).comp (embPsi D.host (D.eTau ρ))` using `RingHom.ext fun x => GlobalTheory.JumpDictionaryFoundation.embOver_true_apply D ρ x`. Prove the components needed by the constructor for the conclusion.

Establish `e0 : embOver D ρ false = embPsi D.host (D.eTau ρ)` using `rfl`. Rewrite using `[e0, h1, hval]`. Rewrite using `[hconj, h2, hval]`. Use `push_cast`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem main : ∀ (D : D7) (C : Formalism.L2.Host.CharFrame D) (nch : NChoice D) (Tp : Formalism.L2.Host.TupTied D C nch),
    Formalism.L2.Host.NCharTied D C nch Tp → BlockCharParam D := by
  intro D C nch Tp N i ρ
  have he : (N.e1 (D.naut.tw (D.naut.muC i) D.naut.etaTinv)).1 = Tp.tup (D.nd.mu i) (liftIdx D i) * C.eta⁻¹ := by
    rw [N.tw, N.muC i (liftIdx D i) (liftIdx_succ D i), N.etaTinv]
  have hI := block_hasInfQ D C nch Tp (D.nd.mu i) (liftIdx D i)
  rw [← he] at hI
  obtain ⟨h1, h2⟩ := N.infG _ _ hI (D.eTau ρ)
  have hval : eExp D (liftIdx D i) (D.eTau ρ) = (D.hc ρ).e (liftIdx D i) := by
    simp [eExp]
  have hconj : embOver D ρ true = (starRingEnd ℂ).comp (embPsi D.host (D.eTau ρ)) :=
    RingHom.ext fun x => GlobalTheory.JumpDictionaryFoundation.embOver_true_apply D ρ x
  constructor
  · have e0 : embOver D ρ false = embPsi D.host (D.eTau ρ) := rfl
    rw [e0, h1, hval]
  · rw [hconj, h2, hval]
    push_cast
    congr 1
    ring

end GlobalTheory.BlockCharInf

end
