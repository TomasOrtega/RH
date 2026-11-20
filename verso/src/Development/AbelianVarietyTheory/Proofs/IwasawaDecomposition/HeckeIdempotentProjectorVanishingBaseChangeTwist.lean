import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvRoots
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeInIsotypicSup
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HeightCounting.FormsStep

/- English proof (translation)
Establish `hpow : ∀ (n : ℕ) (y : S.WL j), Φ ((F ^ n) y) = (G ^ n) (Φ y)`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro y`. Both sides reduce to the same expression.

Consider the case `succ n ih => intro y`. Rewrite using `[pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hFG]`. Proceed by induction on `p using Polynomial.induction_on' generalizing x with`. Consider the case `add p q hp hq => rw [Polynomial.map_add, Polynomial.map_add, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, map_add, hp, hq]`. Consider the case `monomial n a`.

Rewrite using `[Polynomial.map_monomial, Polynomial.map_monomial, aeval_monomial, aeval_monomial, Module.End.mul_apply, Module.End.mul_apply, Module.algebraMap_end_apply, Module.algebraMap_end_apply, IntermediateField.algebraMap_apply, hc, hpow]`.
-/
theorem transfer_aeval (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw) (i : T.Tw) (j : ℕ) (b : Bool)
    (Φ : S.WL j →+ FmT D T S i j b)
    (hc : ∀ (c : ↥D.LL0) (x : S.WL j), Φ ((c : D.what₂.LL) • x) = readT D T i b c • Φ x)
    (F : Module.End D.what₂.LL (S.WL j)) (G : Module.End (FractionRing (T.O i)) (FmT D T S i j b))
    (hFG : ∀ x, Φ (F x) = G (Φ x)) (p : Polynomial ↥D.LL0) (x : S.WL j) :
    Φ (aeval F (p.map (algebraMap ↥D.LL0 D.what₂.LL)) x) = aeval G (p.map (readT D T i b)) (Φ x) := by
  have hpow : ∀ (n : ℕ) (y : S.WL j), Φ ((F ^ n) y) = (G ^ n) (Φ y) := by
    intro n
    induction n with
    | zero => intro y; rfl
    | succ n ih => intro y; rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hFG]
  induction p using Polynomial.induction_on' generalizing x with
  | add p q hp hq => rw [Polynomial.map_add, Polynomial.map_add, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply,
      map_add, hp, hq]
  | monomial n a =>
    rw [Polynomial.map_monomial, Polynomial.map_monomial, aeval_monomial, aeval_monomial, Module.End.mul_apply,
      Module.End.mul_apply, Module.algebraMap_end_apply, Module.algebraMap_end_apply, IntermediateField.algebraMap_apply,
      hc, hpow]

/- English proof (translation)
Use `haveI : Fintype (Formalism.IndefR.NX.U D.nd) := Fintype.ofFinite _`. Unfold `piLop piKop`. Rewrite using `[finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, LinearMap.sum_apply, LinearMap.sum_apply, map_sum]`. Use `Finset.sum_congr rfl fun u _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.smul_apply, LinearMap.smul_apply, hc, ha, LinearEquiv.coe_coe]`.
-/
theorem transfer_piLop (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw) (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool)
    (Φ : S.WL j →+ FmT D T S i j b)
    (hc : ∀ (c : ↥D.LL0) (x : S.WL j), Φ ((c : D.what₂.LL) • x) = readT D T i b c • Φ x)
    (ha : ∀ (g : G0g D.nd) (x : S.WL j), Φ (actL D S j g x) = actGT D T S In.rho In.chi i j b g (Φ x))
    (x : S.WL j) : Φ (piLop D S In.θ j x) = piKop D T S In i j b (Φ x) := by
  haveI : Fintype (Formalism.IndefR.NX.U D.nd) := Fintype.ofFinite _
  unfold piLop piKop
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply, hc, ha, LinearEquiv.coe_coe]

/- English proof (translation)
Introduce `D T S In i j b k P h1 h2 h0`. Take `⟨Φ, hc, hf, hw⟩` from `descend_exists D T S In i j b h1 h2`. Establish `ha` using `descend_actL D T S In i j b h1 h2 Φ hc hf`. Establish `he : ∀ x, Φ (eLop D S j x) = eGT D T S In.rho In.chi i j b (Φ x)` using `descend_eSum D T S In i j b Φ hc ha`. Establish `hpi` using `transfer_piLop D T S In i j b Φ hc ha`.

Establish `hr : ∀ w : ↥(WKr D S j), (hLr D S In j k P w : S.WL j) = In.hL j k P w`. Introduce `w`. Unfold `hLr`. Use `split_ifs with h`. Both sides reduce to the same expression.

Conclude with `absurd ⟨h1, h2⟩ h`. Establish `hh : ∀ x, Φ (In.hL j k P x) = hLT D T S In i j b k P (Φ x)` using `fun x => hf _ _ hr x`. Establish `hphi : ∀ x, Φ (phiLop D S In j k P x) = phiKop D T S In i j b k P (Φ x)` using `transfer_aeval D T S i j b Φ hc _ _ hh (evPol D S In j k P)`. Establish `key : ∀ w : ↥(WKr D S j), (phiKop D T S In i j b k P * eGT D T S In.rho In.chi i j b * piKop D T S In i j b) ((1 : KT D T i b) ⊗ₜ[S.Ks] w : KT D T i b ⊗[S.Ks] ↥(WKr D S j)) = 0`. Introduce `w`.

Rewrite using `[← hw, Module.End.mul_apply, Module.End.mul_apply, ← hpi, ← he, ← hphi]`. Establish `h3` using `LinearMap.congr_fun h0 (w : S.WL j)`. Rewrite `h3` using `[Module.End.mul_apply, Module.End.mul_apply]`. Rewrite using `[h3, LinearMap.zero_apply, map_zero]`. Use `set f := phiKop D T S In i j b k P * eGT D T S In.rho In.chi i j b * piKop D T S In i j b with hfdef`.

Use `LinearMap.ext fun y => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.zero_apply]`. Express the relevant statement in the definitionally equal form `KT D T i b ⊗[S.Ks] ↥(WKr D S j) at y`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => exact f.map_zero`.

Consider the case `tmul c w`. Establish `hcw : (c ⊗ₜ[S.Ks] w : KT D T i b ⊗[S.Ks] ↥(WKr D S j)) = (c : FractionRing (T.O i)) • ((1 : KT D T i b) ⊗ₜ[S.Ks] w : KT D T i b ⊗[S.Ks] ↥(WKr D S j))`. Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Rewrite using `[hcw]`. Conclude with `(f.map_smul (c : FractionRing (T.O i)) (show FmT D T S i j b from ((1 : KT D T i b) ⊗ₜ[S.Ks] w : KT D T i b ⊗[S.Ks] ↥(WKr D S j)))).trans (by rw [key]; exact smul_zero _)`.

Consider the case `add y z hy hz`. Conclude with `(f.map_add (show FmT D T S i j b from y) (show FmT D T S i j b from z)).trans (by rw [hy, hz, add_zero])`.
-/
theorem phiKop_eGT_piKop_eq_zero : ∀ (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw) (In : RatIn D S) (i : T.Tw) (j : ℕ)
    (b : Bool) (k : ℕ) (P : PlE D.host),
    1 ≤ j → j ≤ D.R.m → phiLop D S In j k P * eLop D S j * piLop D S In.θ j = 0 →
    phiKop D T S In i j b k P * eGT D T S In.rho In.chi i j b * piKop D T S In i j b = 0 := by
  intro D T S In i j b k P h1 h2 h0
  obtain ⟨Φ, hc, hf, hw⟩ := descend_exists D T S In i j b h1 h2
  have ha := descend_actL D T S In i j b h1 h2 Φ hc hf
  have he : ∀ x, Φ (eLop D S j x) = eGT D T S In.rho In.chi i j b (Φ x) := descend_eSum D T S In i j b Φ hc ha
  have hpi := transfer_piLop D T S In i j b Φ hc ha
  have hr : ∀ w : ↥(WKr D S j), (hLr D S In j k P w : S.WL j) = In.hL j k P w := by
    intro w
    unfold hLr
    split_ifs with h
    · rfl
    · exact absurd ⟨h1, h2⟩ h
  have hh : ∀ x, Φ (In.hL j k P x) = hLT D T S In i j b k P (Φ x) := fun x => hf _ _ hr x
  have hphi : ∀ x, Φ (phiLop D S In j k P x) = phiKop D T S In i j b k P (Φ x) :=
    transfer_aeval D T S i j b Φ hc _ _ hh (evPol D S In j k P)
  have key : ∀ w : ↥(WKr D S j),
      (phiKop D T S In i j b k P * eGT D T S In.rho In.chi i j b * piKop D T S In i j b)
        ((1 : KT D T i b) ⊗ₜ[S.Ks] w : KT D T i b ⊗[S.Ks] ↥(WKr D S j)) = 0 := by
    intro w
    rw [← hw, Module.End.mul_apply, Module.End.mul_apply, ← hpi, ← he, ← hphi]
    have h3 := LinearMap.congr_fun h0 (w : S.WL j)
    rw [Module.End.mul_apply, Module.End.mul_apply] at h3
    rw [h3, LinearMap.zero_apply, map_zero]
  set f := phiKop D T S In i j b k P * eGT D T S In.rho In.chi i j b * piKop D T S In i j b with hfdef
  refine LinearMap.ext fun y => ?_
  rw [LinearMap.zero_apply]
  change KT D T i b ⊗[S.Ks] ↥(WKr D S j) at y
  induction y using TensorProduct.induction_on with
  | zero => exact f.map_zero
  | tmul c w =>
    have hcw : (c ⊗ₜ[S.Ks] w : KT D T i b ⊗[S.Ks] ↥(WKr D S j)) =
        (c : FractionRing (T.O i)) • ((1 : KT D T i b) ⊗ₜ[S.Ks] w : KT D T i b ⊗[S.Ks] ↥(WKr D S j)) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hcw]
    exact (f.map_smul (c : FractionRing (T.O i))
      (show FmT D T S i j b from ((1 : KT D T i b) ⊗ₜ[S.Ks] w : KT D T i b ⊗[S.Ks] ↥(WKr D S j)))).trans
      (by rw [key]; exact smul_zero _)
  | add y z hy hz =>
    exact (f.map_add (show FmT D T S i j b from y) (show FmT D T S i j b from z)).trans (by rw [hy, hz, add_zero])

end GlobalTheory.HeightCounting.FormsStep
