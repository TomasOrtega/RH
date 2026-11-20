import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.StrongMultOneC

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

/- English proof (translation)
Introduce `E _ _`. Set `B : LinearMap.BilinForm ℝ (Cinf E)` to `(LinearMap.mul ℝ (Cinf E)).compr₂ (TG.tr E)`. Establish `hl : ∀ x : Cinf E, (∀ y, B x y = 0) → x = 0` using `fun x h => by`. Establish `h1 : ∑ w, 2 * (x w * starRingEnd ℂ (x w)).re = 0` using `h fun w => starRingEnd ℂ (x w)`. Simplify using `only [Complex.mul_conj, Complex.ofReal_re] at h1`.

Establish `b'` using `(Finset.sum_eq_zero_iff_of_nonneg fun w _ => mul_nonneg zero_le_two (Complex.normSq_nonneg (x w))).1 h1`. Conclude with `funext fun w => Complex.normSq_eq_zero.1 ((mul_eq_zero.1 (b' w (Finset.mem_univ _))).resolve_left two_ne_zero)`. Establish `hB : B.Nondegenerate` using `⟨hl, fun x h => hl x fun y => by`. Use `h y` as an intermediate fact. Express the relevant statement in the definitionally equal form `TG.tr E (_ * _) = 0 at this ⊢`.

Rewrite using `[mul_comm]⟩` and apply the resulting hypothesis. Set `b` to `Module.finBasis ℝ (Cinf E)`. Use `⟨_, b, B.dualBasis hB b, fun x y => ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [← b.sum_repr y]`. Rewrite using `[Finset.mul_sum, map_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.BilinForm.dualBasis_repr_apply, mul_smul_comm, map_smul, smul_eq_mul, mul_comm]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.V.Af.StrongMultiplicityOne.trDual :
    UpperTheory.V.Af.StrongMultiplicityOne.TrDual := by
  classical
  intro E _ _
  let B : LinearMap.BilinForm ℝ (Cinf E) := (LinearMap.mul ℝ (Cinf E)).compr₂ (TG.tr E)
  have hl : ∀ x : Cinf E, (∀ y, B x y = 0) → x = 0 := fun x h => by
    have h1 : ∑ w, 2 * (x w * starRingEnd ℂ (x w)).re = 0 := h fun w => starRingEnd ℂ (x w)
    simp only [Complex.mul_conj, Complex.ofReal_re] at h1
    have b' := (Finset.sum_eq_zero_iff_of_nonneg fun w _ => mul_nonneg zero_le_two (Complex.normSq_nonneg (x w))).1 h1
    exact funext fun w => Complex.normSq_eq_zero.1 ((mul_eq_zero.1 (b' w (Finset.mem_univ _))).resolve_left two_ne_zero)
  have hB : B.Nondegenerate := ⟨hl, fun x h => hl x fun y => by
    have := h y
    change TG.tr E (_ * _) = 0 at this ⊢
    rwa [mul_comm]⟩
  let b := Module.finBasis ℝ (Cinf E)
  refine ⟨_, b, B.dualBasis hB b, fun x y => ?_⟩
  conv_lhs => rw [← b.sum_repr y]
  rw [Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.BilinForm.dualBasis_repr_apply, mul_smul_comm, map_smul, smul_eq_mul, mul_comm]
  rfl
