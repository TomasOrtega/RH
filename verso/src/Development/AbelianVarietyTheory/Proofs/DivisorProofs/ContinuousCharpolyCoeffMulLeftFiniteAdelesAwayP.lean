import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.CharpolyCont

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C a => simp only [MvPolynomial.eval₂_C]`. Conclude with `continuous_const`. Consider the case `add P Q hP hQ => simp only [MvPolynomial.eval₂_add]`. Conclude with `hP.add hQ`.

Consider the case `mul_X P i hP => simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]`. Conclude with `hP.mul (hx i)`.
-/
theorem continuous_eval₂_of {X R : Type*} [TopologicalSpace X] [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] {σ : Type*} (f : ℤ →+* R) (P : MvPolynomial σ ℤ) (x : X → σ → R)
    (hx : ∀ i, Continuous fun t => x t i) : Continuous fun t => MvPolynomial.eval₂ f (x t) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp only [MvPolynomial.eval₂_C]; exact continuous_const
  | add P Q hP hQ => simp only [MvPolynomial.eval₂_add]; exact hP.add hQ
  | mul_X P i hP => simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]; exact hP.mul (hx i)

/- English proof (translation)
Set `b` to `Module.Free.chooseBasis R A`. Establish `e : ∀ a : A, (LinearMap.charpoly (LinearMap.mulLeft R a)).coeff k = MvPolynomial.eval₂Hom (Int.castRingHom R) (fun ij : Module.Free.ChooseBasisIndex R A × Module.Free.ChooseBasisIndex R A => LinearMap.toMatrix b b (LinearMap.mulLeft R a) ij.1 ij.2) ((Matrix.charpoly.univ ℤ (Modul …`. Introduce `a`. Rewrite using `[Matrix.charpoly.univ_coeff_eval₂Hom, ← LinearMap.charpoly_toMatrix _ b]`. Both sides reduce to the same expression.

Repeatedly rewrite using `[e]`. Use `continuous_eval₂_of _ _ _ fun ij => ?_` and prove the remaining obligations. Establish `h : ∀ a : A, LinearMap.toMatrix b b (LinearMap.mulLeft R a) ij.1 ij.2 = (b.coord ij.1).comp (LinearMap.mulRight R (b ij.2)) a`. Introduce `a`. Simplify using `[LinearMap.toMatrix_apply]`.

Repeatedly rewrite using `[h]`. Conclude with `IsModuleTopology.continuous_of_linearMap _`.
-/
theorem continuous_charpoly_coeff_mulLeft {R A : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [Ring A] [Algebra R A] [Module.Free R A] [Module.Finite R A] [TopologicalSpace A] [IsModuleTopology R A]
    (k : ℕ) : Continuous fun a : A => (LinearMap.charpoly (LinearMap.mulLeft R a)).coeff k := by
  let b := Module.Free.chooseBasis R A
  have e : ∀ a : A, (LinearMap.charpoly (LinearMap.mulLeft R a)).coeff k =
      MvPolynomial.eval₂Hom (Int.castRingHom R)
        (fun ij : Module.Free.ChooseBasisIndex R A × Module.Free.ChooseBasisIndex R A =>
          LinearMap.toMatrix b b (LinearMap.mulLeft R a) ij.1 ij.2)
        ((Matrix.charpoly.univ ℤ (Module.Free.ChooseBasisIndex R A)).coeff k) := by
    intro a
    rw [Matrix.charpoly.univ_coeff_eval₂Hom, ← LinearMap.charpoly_toMatrix _ b]
    rfl
  simp_rw [e]
  refine continuous_eval₂_of _ _ _ fun ij => ?_
  have h : ∀ a : A, LinearMap.toMatrix b b (LinearMap.mulLeft R a) ij.1 ij.2 =
      (b.coord ij.1).comp (LinearMap.mulRight R (b ij.2)) a := by
    intro a
    simp [LinearMap.toMatrix_apply]
  simp_rw [h]
  exact IsModuleTopology.continuous_of_linearMap _

end GlobalTheory.CharpolyCont

open GlobalTheory.CharpolyCont in
/- English proof (translation)
Introduce `p _ G k`. Use `letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) _`. Use `haveI : IsModuleTopology (AfP p) (AfP p ⊗[ℚ] G.C) := ⟨rfl⟩`. Conclude with `(continuous_charpoly_coeff_mulLeft (R := AfP p) (A := AfP p ⊗[ℚ] G.C) k).comp (Units.continuous_val.comp (continuous_fst.comp continuous_subtype_val))`.
-/
theorem GlobalTheory.charpoly_coeff_continuous_GAf : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (k : ℕ), Continuous fun g : G.GAf =>
    (LinearMap.charpoly (LinearMap.mulLeft (AfP p) (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) :
      AfP p ⊗[ℚ] G.C))).coeff k := by
  intro p _ G k
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) _
  haveI : IsModuleTopology (AfP p) (AfP p ⊗[ℚ] G.C) := ⟨rfl⟩
  exact (continuous_charpoly_coeff_mulLeft (R := AfP p) (A := AfP p ⊗[ℚ] G.C) k).comp
    (Units.continuous_val.comp (continuous_fst.comp continuous_subtype_val))
