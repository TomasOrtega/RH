import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordTensorDataFactorInclusionProjectionProps
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeatRatio.Square

variable {R : Type} [CommRing R] [IsDomain R]

/- English proof (translation)
Use `show (padd Q.P.A (𝟙 Q.P.A) (toUnit _ ≫ Q.c 0)).left = 𝟙 _`. Rewrite using `[GlobalTheory.Mum.degPre_c_zero, padd, comp_one, ← Hom.mul_def, _root_.mul_one]`. Both sides reduce to the same expression.
-/
theorem famφB_zero_one (Q : DegPre R) : Q.famφB 0 1 = 𝟙 _ := by
  show (padd Q.P.A (𝟙 Q.P.A) (toUnit _ ≫ Q.c 0)).left = 𝟙 _
  rw [GlobalTheory.Mum.degPre_c_zero, padd, comp_one, ← Hom.mul_def, _root_.mul_one]
  rfl

/- English proof (translation)
Use `show (toUnit Q.P.A ≫ Q.c 0).left = (toUnit Q.P.A ≫ η[Q.P.A]).left`. Rewrite using `[GlobalTheory.Mum.degPre_c_zero, comp_one, Hom.one_def]`.
-/
theorem famφB_zero_two (Q : DegPre R) : Q.famφB 0 2 = Q.famφB 0 3 := by
  show (toUnit Q.P.A ≫ Q.c 0).left = (toUnit Q.P.A ≫ η[Q.P.A]).left
  rw [GlobalTheory.Mum.degPre_c_zero, comp_one, Hom.one_def]

/- English proof (translation)
Introduce `U _ h`. Rewrite using `[Fintype.prod_sum_type]`. Simplify using `only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_four]`. Establish `e1` using `famφB_zero_one Q`. Establish `e2` using `famφB_zero_two Q`.

Establish `e0 : Q.famφB 0 0 = 𝟙 _` using `rfl`. Rewrite using `[e1, e2, e0]`. Simplify using `only [DegPre.famε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]`. Generalize the expression as in `h (𝟙 _) = a`. Generalize the expression as in `h (Q.famφB 0 3) = b`.

Use `push_cast`. Establish `hs : ∀ k : ℤ, a ^ (k - 1) * a ^ (1 : ℤ) = a ^ k` using `fun k => by rw [← zpow_add, sub_add_cancel]`. Rewrite using `[hs, hs, zpow_neg_one, zpow_one, inv_mul_cancel_right, inv_mul_cancel_right, ← zpow_add, two_mul]`.
-/
theorem formEq (Q : DegPre R) (N : ℕ) :
    FormEq (Sum.elim (Q.famφB 0) (Q.famφB 0)) (Sum.elim (DegPre.famε N) (DegPre.famε N))
      (Q.famφB 0) (DegPre.famε (2 * N)) := by
  intro U _ h
  rw [Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_four]
  have e1 := famφB_zero_one Q
  have e2 := famφB_zero_two Q
  have e0 : Q.famφB 0 0 = 𝟙 _ := rfl
  rw [e1, e2, e0]
  simp only [DegPre.famε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
  generalize h (𝟙 _) = a
  generalize h (Q.famφB 0 3) = b
  push_cast
  have hs : ∀ k : ℤ, a ^ (k - 1) * a ^ (1 : ℤ) = a ^ k := fun k => by rw [← zpow_add, sub_add_cancel]
  rw [hs, hs, zpow_neg_one, zpow_one, inv_mul_cancel_right, inv_mul_cancel_right, ← zpow_add, two_mul]

/- English proof (translation)
Take `⟨ρ, hρ⟩` from `exists_sec Q.P.isLB (formEq Q N) (H1.SectionArithmetic.mulSec σ σ')`. Take `⟨ρ', hρ'⟩` from `exists_sec Q.P.isLB (formEq Q N) (H1.SectionArithmetic.mulSec σ' σ')`. Use `⟨ρ, ρ', fun z hz J hJ => ?_⟩` and prove the remaining obligations. Take `⟨hu, he⟩` from `h z hz J hJ`. Rewrite using `[hρ _ _ z J hJ, hρ' _ _ z J hJ, H1.SectionArithmetic.sval_mulSec _ _ _ z hJ, H1.SectionArithmetic.sval_mulSec _ _ _ z hJ, he]`.

Conclude with `⟨hu.mul hu, by ring⟩`.
-/
theorem isRatio_two_mul (Q : DegPre R) (N : ℕ) (σ σ' : Q.SecB N 0) (U : Q.P.A.left.Opens)
    (f : Γ(Q.P.A.left, U)) (_hN : 1 ≤ N) (h : GlobalTheory.HeatRatio.IsRatio Q σ σ' U f) :
    ∃ ρ ρ' : Q.SecB (2 * N) 0, GlobalTheory.HeatRatio.IsRatio Q ρ ρ' U f := by
  obtain ⟨ρ, hρ⟩ := exists_sec Q.P.isLB (formEq Q N) (H1.SectionArithmetic.mulSec σ σ')
  obtain ⟨ρ', hρ'⟩ := exists_sec Q.P.isLB (formEq Q N) (H1.SectionArithmetic.mulSec σ' σ')
  refine ⟨ρ, ρ', fun z hz J hJ => ?_⟩
  obtain ⟨hu, he⟩ := h z hz J hJ
  rw [hρ _ _ z J hJ, hρ' _ _ z J hJ, H1.SectionArithmetic.sval_mulSec _ _ _ z hJ, H1.SectionArithmetic.sval_mulSec _ _ _ z hJ, he]
  exact ⟨hu.mul hu, by ring⟩

end GlobalTheory.HeatRatio.Square

/- English proof (translation)
Introduce `_ _ _ Q N σ σ' U f hN h` and use `GlobalTheory.HeatRatio.Square.isRatio_two_mul Q N σ σ' U f hN h`.
-/
theorem GlobalTheory.HeatRatio.isRatio_square : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (N : ℕ) (σ σ' : Q.SecB N 0) (U : Q.P.A.left.Opens) (f : Γ(Q.P.A.left, U)), 1 ≤ N → GlobalTheory.HeatRatio.IsRatio Q σ σ' U f → ∃ ρ ρ' : Q.SecB (2 * N) 0, GlobalTheory.HeatRatio.IsRatio Q ρ ρ' U f :=
  fun _ _ _ Q N σ σ' U f hN h => GlobalTheory.HeatRatio.Square.isRatio_two_mul Q N σ σ' U f hN h
