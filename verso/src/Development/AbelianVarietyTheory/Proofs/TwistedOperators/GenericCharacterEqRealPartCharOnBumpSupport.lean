import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousReprSymm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorThetaFunctionalMixedSourceMode
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergThetaMixedModelTargetOfMixedModel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionMixedCoordinateBumpMulCoreStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTargetBumpMulCoreThetaExistsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionDeterminedByMixedCoordinatesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFinSupp

/- English proof (translation)
Apply `(GlobalTheory.AscFinInhab.coordH D m n).injective` to reduce the goal to its premises. Rewrite using `[GlobalTheory.AscFinInhab.coordH_apply, GlobalTheory.AscFinInhab.coordH_apply, (GlobalTheory.AscFinInhab.RCh_eq_zero_iff z).2 h1, (GlobalTheory.AscFinInhab.FCh_eq_zero_iff z).2 h2, map_zero, map_zero]`.
-/
theorem eq_zero_of_parts {D : D7} {m n : ℕ} (z : Mx D m n) (h1 : z.map (infPart D) = 0) (h2 : z.map (finPart D) = 0) : z = 0 := by
  apply (GlobalTheory.AscFinInhab.coordH D m n).injective
  rw [GlobalTheory.AscFinInhab.coordH_apply, GlobalTheory.AscFinInhab.coordH_apply, (GlobalTheory.AscFinInhab.RCh_eq_zero_iff z).2 h1,
    (GlobalTheory.AscFinInhab.FCh_eq_zero_iff z).2 h2, map_zero, map_zero]

/- English proof (translation)
Apply `eq_zero_of_parts` to reduce the goal to its premises. Use extensionality with `i j`. Establish `h0 : infPart D (a i j) = 0` using `congrFun (congrFun h i) j`. Simplify using `only [Matrix.map_apply, Matrix.smul_apply, Matrix.zero_apply, Algebra.smul_def, map_mul, h0, mul_zero]`. Use extensionality with `i j`.

Conclude with `GlobalTheory.ThetaClosed.finPart_eInf_smul (a i j)`.
-/
theorem smul_eInf_eq_zero {D : D7} {m n : ℕ} (a : Mx D m n) (h : a.map (infPart D) = 0) :
    GlobalTheory.FinTranslate.eInf D • a = 0 := by
  apply eq_zero_of_parts
  · ext i j
    have h0 : infPart D (a i j) = 0 := congrFun (congrFun h i) j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.zero_apply, Algebra.smul_def, map_mul, h0, mul_zero]
  · ext i j
    exact GlobalTheory.ThetaClosed.finPart_eInf_smul (a i j)

/- English proof (translation)
Apply `eq_zero_of_parts` to reduce the goal to its premises. Use extensionality with `i j`. Conclude with `GlobalTheory.ThetaClosed.infPart_one_sub_eInf_smul (r i j)`. Use extensionality with `i j`. Establish `h0 : finPart D (r i j) = 0` using `congrFun (congrFun h i) j`.

Simplify using `only [Matrix.map_apply, Matrix.smul_apply, Matrix.zero_apply, Algebra.smul_def, map_mul, h0, mul_zero]`.
-/
theorem smul_one_sub_eInf_eq_zero {D : D7} {m n : ℕ} (r : Mx D m n) (h : r.map (finPart D) = 0) :
    (1 - GlobalTheory.FinTranslate.eInf D) • r = 0 := by
  apply eq_zero_of_parts
  · ext i j
    exact GlobalTheory.ThetaClosed.infPart_one_sub_eInf_smul (r i j)
  · ext i j
    have h0 : finPart D (r i j) = 0 := congrFun (congrFun h i) j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.zero_apply, Algebra.smul_def, map_mul, h0, mul_zero]

/- English proof (translation)
Establish `hU : (u.1 : GL (Fin ρ) (AE D)) ∈ GlobalTheory.UniIndexPrime.uniSub ρ (AE D)` using `u.2`. Rewrite `hU` using `[GlobalTheory.UniIndexPrime.mem_uniSub]`. Take `⟨h1, h2⟩` from `hU`. Introduce `i j hij`. Break down `hij.lt_or_eq with h | h` into its components or cases.

Establish `e1 : (u.1.1 : Mx D ρ ρ) i j = 0` using `h1 i j h`. Establish `e2 : (1 : Mx D ρ ρ) i j = 0` using `Matrix.one_apply_ne (ne_of_gt h)`. Rewrite using `[Matrix.sub_apply, e1, e2, sub_zero]`. Substitute `h` using the available equality. Establish `e1 : (u.1.1 : Mx D ρ ρ) j j = 1` using `h2 j`.

Rewrite using `[Matrix.sub_apply, e1, Matrix.one_apply_eq, sub_self]`.
-/
theorem upper_of_UX {D : D7} {ρ : ℕ} (u : UX D ρ) : ∀ i j, j ≤ i → ((u.1.1 : Mx D ρ ρ) - 1) i j = 0 := by
  have hU : (u.1 : GL (Fin ρ) (AE D)) ∈ GlobalTheory.UniIndexPrime.uniSub ρ (AE D) := u.2
  rw [GlobalTheory.UniIndexPrime.mem_uniSub] at hU
  obtain ⟨h1, h2⟩ := hU
  intro i j hij
  rcases hij.lt_or_eq with h | h
  · have e1 : (u.1.1 : Mx D ρ ρ) i j = 0 := h1 i j h
    have e2 : (1 : Mx D ρ ρ) i j = 0 := Matrix.one_apply_ne (ne_of_gt h)
    rw [Matrix.sub_apply, e1, e2, sub_zero]
  · subst h
    have e1 : (u.1.1 : Mx D ρ ρ) j j = 1 := h2 j
    rw [Matrix.sub_apply, e1, Matrix.one_apply_eq, sub_self]

/- English proof (translation)
Establish `hea` using `smul_eInf_eq_zero a ha`. Establish `her` using `smul_one_sub_eInf_eq_zero r hr`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_smul, hxN, smul_add, her, zero_add, sub_smul, one_smul, hea, sub_zero]`. Rewrite using `[Matrix.mul_smul, hxN, smul_add, hea, add_zero]`.

Establish `h` using `her`. Rewrite `h` using `[sub_smul, one_smul, sub_eq_zero]`. Conclude with `h.symm`.
-/
theorem split_parts {D : D7} {m ρ : ℕ} (x : Mx D m ρ) (N : Mx D ρ ρ) (r a : Mx D m ρ) (hxN : x ⬝ N = r + a)
    (hr : r.map (finPart D) = 0) (ha : a.map (infPart D) = 0) :
    x ⬝ ((1 - GlobalTheory.FinTranslate.eInf D) • N) = a ∧ x ⬝ (GlobalTheory.FinTranslate.eInf D • N) = r := by
  have hea := smul_eInf_eq_zero a ha
  have her := smul_one_sub_eInf_eq_zero r hr
  refine ⟨?_, ?_⟩
  · rw [Matrix.mul_smul, hxN, smul_add, her, zero_add, sub_smul, one_smul, hea, sub_zero]
  · rw [Matrix.mul_smul, hxN, smul_add, hea, add_zero]
    have h := her
    rw [sub_smul, one_smul, sub_eq_zero] at h
    exact h.symm

/- English proof (translation)
Establish `hsplit : N = GlobalTheory.FinTranslate.eInf D • N + (1 - GlobalTheory.FinTranslate.eInf D) • N`. Rewrite using `[sub_smul, one_smul, add_sub_cancel]`. Use `show psiE ψ (upSum u.1.1) = _`. Rewrite using `[hN, GlobalTheory.AscFinInhab.upSum_add', GlobalTheory.AscFinInhab.upSum_one', zero_add, hsplit, GlobalTheory.AscFinInhab.upSum_add', psiE_add, h1, mul_one, ← hsplit]`.
-/
theorem main_part {D : D7} {ρ : ℕ} (ψ : AddChar (AF D.host.F) ℂ) (u : UX D ρ) (N : Mx D ρ ρ) (hN : (u.1.1 : Mx D ρ ρ) = 1 + N)
    (h1 : psiE ψ (upSum ((1 - GlobalTheory.FinTranslate.eInf D) • N)) = 1) :
    psiUni ψ u.1 = psiE ψ (upSum (GlobalTheory.FinTranslate.eInf D • N)) := by
  have hsplit : N = GlobalTheory.FinTranslate.eInf D • N + (1 - GlobalTheory.FinTranslate.eInf D) • N := by
    rw [sub_smul, one_smul, add_sub_cancel]
  show psiE ψ (upSum u.1.1) = _
  rw [hN, GlobalTheory.AscFinInhab.upSum_add', GlobalTheory.AscFinInhab.upSum_one', zero_add, hsplit,
    GlobalTheory.AscFinInhab.upSum_add', psiE_add, h1, mul_one, ← hsplit]

/- English proof (translation)
Introduce `D ψ V V₀ W W₀ ρ σ dV dW p x₀ L hL hp u r hr ha`. Establish `haInf : (rat x₀ ⬝ u.1.1 - (rat x₀ + r)).map (infPart D) = 0` using `(GlobalTheory.AscFinInhab.mxAt_true_iff _).1 (hp.a₁.fin _ ha)`. Establish `hxN : rat x₀ ⬝ ((u.1.1 : Mx D ρ ρ) - 1) = r + (rat x₀ ⬝ u.1.1 - (rat x₀ + r))`. Rewrite using `[Matrix.mul_sub, Matrix.mul_one]`. Normalize the expressions using the abelian group laws.

Take `⟨h1e, he⟩` from `split_parts _ _ _ _ hxN hr haInf`. Establish `hLr : rat L ⬝ r = GlobalTheory.FinTranslate.eInf D • ((u.1.1 : Mx D ρ ρ) - 1)`. Rewrite using `[← he, ← Matrix.mul_assoc, ← rat_mul, hL, rat_one, Matrix.one_mul]`. Establish `hfin : MxAt (fun _ => True) ((1 - GlobalTheory.FinTranslate.eInf D) • ((u.1.1 : Mx D ρ ρ) - 1))`. Rewrite using `[GlobalTheory.AscFinInhab.mxAt_true_iff]`.

Use extensionality with `i j`. Conclude with `GlobalTheory.ThetaClosed.infPart_one_sub_eInf_smul _`. Establish `hup' : ∀ i j, j ≤ i → ((1 - GlobalTheory.FinTranslate.eInf D) • ((u.1.1 : Mx D ρ ρ) - 1)) i j = 0`. Introduce `i j hij`. Rewrite using `[Matrix.smul_apply, upper_of_UX u i j hij, smul_zero]`.

Establish `hmem : Formalism.L2.Theta.mt W (1 : GA D W)⁻¹ ⬝ (rat x₀ ⬝ ((1 - GlobalTheory.FinTranslate.eInf D) • ((u.1.1 : Mx D ρ ρ) - 1))) ∈ p.A₁`. Rewrite using `[inv_one, GlobalTheory.AscFinInhab.mt_one_, Matrix.one_mul, h1e]`. Conclude with `ha`. Establish `hshift` using `(GlobalTheory.AscFin.cond_one hp (0 : Mx D V₀.rank σ)).shift _ hfin hup' hmem`. Rewrite using `[hLr]`.

Conclude with `main_part ψ u _ (by rw [add_sub_cancel]) hshift`.
-/
theorem charOnSupport : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (p : Pieces V₀ W W₀ ρ σ) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (L : Matrix (Fin ρ) (Fin W.rank) D.host.E), L * x₀ = 1 → p.Is dV dW (rat x₀) ψ → ∀ (u : UX D ρ) (r : Mx D W.rank ρ), r.map (finPart D) = 0 → rat x₀ ⬝ u.1.1 - (rat x₀ + r) ∈ p.A₁ → psiUni ψ u.1 = psiE ψ (upSum (rat L ⬝ r)) := by
  intro D ψ V V₀ W W₀ ρ σ dV dW p x₀ L hL hp u r hr ha
  have haInf : (rat x₀ ⬝ u.1.1 - (rat x₀ + r)).map (infPart D) = 0 :=
    (GlobalTheory.AscFinInhab.mxAt_true_iff _).1 (hp.a₁.fin _ ha)
  have hxN : rat x₀ ⬝ ((u.1.1 : Mx D ρ ρ) - 1) = r + (rat x₀ ⬝ u.1.1 - (rat x₀ + r)) := by
    rw [Matrix.mul_sub, Matrix.mul_one]; abel
  obtain ⟨h1e, he⟩ := split_parts _ _ _ _ hxN hr haInf
  have hLr : rat L ⬝ r = GlobalTheory.FinTranslate.eInf D • ((u.1.1 : Mx D ρ ρ) - 1) := by
    rw [← he, ← Matrix.mul_assoc, ← rat_mul, hL, rat_one, Matrix.one_mul]
  have hfin : MxAt (fun _ => True) ((1 - GlobalTheory.FinTranslate.eInf D) • ((u.1.1 : Mx D ρ ρ) - 1)) := by
    rw [GlobalTheory.AscFinInhab.mxAt_true_iff]
    ext i j
    exact GlobalTheory.ThetaClosed.infPart_one_sub_eInf_smul _
  have hup' : ∀ i j, j ≤ i → ((1 - GlobalTheory.FinTranslate.eInf D) • ((u.1.1 : Mx D ρ ρ) - 1)) i j = 0 := by
    intro i j hij
    rw [Matrix.smul_apply, upper_of_UX u i j hij, smul_zero]
  have hmem : Formalism.L2.Theta.mt W (1 : GA D W)⁻¹ ⬝ (rat x₀ ⬝ ((1 - GlobalTheory.FinTranslate.eInf D) • ((u.1.1 : Mx D ρ ρ) - 1))) ∈ p.A₁ := by
    rw [inv_one, GlobalTheory.AscFinInhab.mt_one_, Matrix.one_mul, h1e]; exact ha
  have hshift := (GlobalTheory.AscFin.cond_one hp (0 : Mx D V₀.rank σ)).shift _ hfin hup' hmem
  rw [hLr]
  exact main_part ψ u _ (by rw [add_sub_cancel]) hshift

end GlobalTheory.AscFinSupp

end
