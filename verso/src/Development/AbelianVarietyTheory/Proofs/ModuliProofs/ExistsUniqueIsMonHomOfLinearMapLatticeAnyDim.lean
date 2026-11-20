import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsThetaSeriesApplyNeZeroOfLargeForm
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivOfLifting
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HermFormSwapOfIsHermitian
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsMonHomOfComplementary

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

open LatticeHom in

/- English proof (translation)
Introduce `hlaws _ _ hT P P' L L' u u' F hF`. Take `⟨rig, hrig⟩` from `P.8`. Take `⟨rig', hrig'⟩` from `P'.8`. Take `⟨v, Hm, χ, Ef, hAH, -, -, -, -, hth, -⟩` from `hT P rig hrig`. Take `⟨v', Hm', χ', Ef', hAH', -, -, -, -, hth', -⟩` from `hT P' rig' hrig'`.

Take `⟨T, hTu⟩` from `exists_linearEquiv_of_holUnif hlaws.6 P u v`. Take `⟨T', hTu'⟩` from `exists_linearEquiv_of_holUnif hlaws.6 P' u' v'`. Use `set F₀ : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P'.g → ℂ) := T'.toLinearMap ∘ₗ F ∘ₗ T.symm.toLinearMap`. Establish `hF₀T : ∀ z, F₀ (T z) = T' (F z)` using `fun z => by simp [F₀]`. Establish `hF₀ : ∀ l ∈ v.Λ, F₀ l ∈ v'.Λ`.

Introduce `l hl`. Establish `h1 : u.ex (T.symm l) = 1`. Rewrite using `[← hTu, T.apply_symm_apply]`. Conclude with `(v.5 l).2 hl`. Establish `h2 : u'.ex (F (T.symm l)) = 1` using `(u'.5 _).2 (hF _ ((u.5 _).1 h1))`.

Use `(v'.5 _).1 ?_` and prove the remaining obligations. Establish `h3 : F₀ l = T' (F (T.symm l))` using `by simp [F₀]`. Rewrite using `[h3, hTu']`. Conclude with `h2`. Take `⟨d, hd⟩` from `exists_complementary_theta ThetaLarge.exists_theta_apply_ne_zero v v' P.7 P'.7 hAH hAH' F₀ hF₀ 4`.

Take `⟨f, hf, hfF⟩` from `exists_isMonHom_of_complementary hlaws.3 P P' v v' (fun k θ hθ => ((hth k).2 θ hθ).exists) (fun k s => ((hth' k).1 s).exists) F₀ hF₀ d hd`. Establish `hfu : ∀ z, u'.ex (F z) = u.ex z ≫ f`. Introduce `z`. Rewrite using `[← hTu' (F z), ← hTu z, ← hfF, hF₀T]`. Use `⟨f, ⟨hf, hfu⟩, ?_⟩` and prove the remaining obligations.

Introduce and unpack `f' ⟨-, hf'⟩`. Use `P.5` as an intermediate fact. Establish `: Smooth P.A.hom` using `SmoothOfRelativeDimension.smooth P.g P.A.hom`. Establish `: IsReduced P.A.left` using `isReduced_of_smooth_complex P.A.left P.A.hom inferInstance`. Use `P'.3` as an intermediate fact.

Establish `: IsSeparated P'.A.hom` using `inferInstance`. Apply `ComplexPoints.over_hom_ext_of_complexPoints` to reduce the goal to its premises. Introduce `x`. Take `⟨z, rfl⟩` from `u.3 x`. Rewrite using `[← hf' z, hfu z]`.
-/
theorem existsUnique_isMonHom_of_map_lattice :
    Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (P P' : Out.PolAV (Sp ℂ)) (L : LB P.A.left) (L' : LB P'.A.left) (u : HolUnif P.A L P.g) (u' : HolUnif P'.A L' P'.g) (F : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P'.g → ℂ)), (∀ z ∈ u.Λ, F z ∈ u'.Λ) → ∃! f : P.A ⟶ P'.A, IsMonHom f ∧ ∀ z, u'.ex (F z) = u.ex z ≫ f := by
  intro hlaws _ _ hT P P' L L' u u' F hF
  obtain ⟨rig, hrig⟩ := P.8
  obtain ⟨rig', hrig'⟩ := P'.8
  obtain ⟨v, Hm, χ, Ef, hAH, -, -, -, -, hth, -⟩ := hT P rig hrig
  obtain ⟨v', Hm', χ', Ef', hAH', -, -, -, -, hth', -⟩ := hT P' rig' hrig'
  obtain ⟨T, hTu⟩ := exists_linearEquiv_of_holUnif hlaws.6 P u v
  obtain ⟨T', hTu'⟩ := exists_linearEquiv_of_holUnif hlaws.6 P' u' v'
  set F₀ : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P'.g → ℂ) :=
    T'.toLinearMap ∘ₗ F ∘ₗ T.symm.toLinearMap
  have hF₀T : ∀ z, F₀ (T z) = T' (F z) := fun z => by simp [F₀]
  have hF₀ : ∀ l ∈ v.Λ, F₀ l ∈ v'.Λ := by
    intro l hl
    have h1 : u.ex (T.symm l) = 1 := by
      rw [← hTu, T.apply_symm_apply]
      exact (v.5 l).2 hl
    have h2 : u'.ex (F (T.symm l)) = 1 := (u'.5 _).2 (hF _ ((u.5 _).1 h1))
    refine (v'.5 _).1 ?_
    have h3 : F₀ l = T' (F (T.symm l)) := by simp [F₀]
    rw [h3, hTu']
    exact h2
  obtain ⟨d, hd⟩ := exists_complementary_theta ThetaLarge.exists_theta_apply_ne_zero v v' P.7 P'.7
    hAH hAH' F₀ hF₀ 4
  obtain ⟨f, hf, hfF⟩ := exists_isMonHom_of_complementary hlaws.3 P P' v v'
    (fun k θ hθ => ((hth k).2 θ hθ).exists) (fun k s => ((hth' k).1 s).exists) F₀ hF₀ d hd
  have hfu : ∀ z, u'.ex (F z) = u.ex z ≫ f := by
    intro z
    rw [← hTu' (F z), ← hTu z, ← hfF, hF₀T]
  refine ⟨f, ⟨hf, hfu⟩, ?_⟩
  rintro f' ⟨-, hf'⟩
  have := P.5
  have : Smooth P.A.hom := SmoothOfRelativeDimension.smooth P.g P.A.hom
  have : IsReduced P.A.left := isReduced_of_smooth_complex P.A.left P.A.hom inferInstance
  have := P'.3
  have : IsSeparated P'.A.hom := inferInstance
  apply ComplexPoints.over_hom_ext_of_complexPoints
  intro x
  obtain ⟨z, rfl⟩ := u.3 x
  rw [← hf' z, hfu z]

end GlobalTheory
