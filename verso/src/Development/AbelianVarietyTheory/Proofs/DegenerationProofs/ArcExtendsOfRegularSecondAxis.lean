import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LawsChart
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AlgOverHomSurjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLocalRingSecondVariable
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFactorOfRangeSubset
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf
namespace GlobalTheory.SS.ArcInf

/- English proof (translation)
Establish `hs : PowerSeries.HasSubst (MvPowerSeries.X n : MvPowerSeries (Fin 2) k)` using `PowerSeries.HasSubst.of_constantCoeff_zero (by simp)`. Establish `hX : (MvPowerSeries.X n : MvPowerSeries (Fin 2) k) ≠ 0`. Introduce `h0`. Use `congrArg (MvPowerSeries.coeff (Finsupp.single n 1)) h0` as an intermediate fact. Simplify using `[MvPowerSeries.coeff_X] at this`.

Take `⟨σ, hσ⟩` from `exists_lift (k := k) ((IsScalarTower.toAlgHom k (MvPowerSeries (Fin 2) k) (FractionRing (MvPowerSeries (Fin 2) k))).comp (PowerSeries.substAlgHom (R := k) hs)) (by`. Rewrite using `[AlgHom.comp_apply, PowerSeries.substAlgHom_X, isUnit_iff_ne_zero, IsScalarTower.toAlgHom_apply]`. Conclude with `(map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hX)`. Use `⟨σ, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[hσ, AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, PowerSeries.coe_substAlgHom]`.
-/
theorem exists_lift_var (k : Type) [Field k] (n : Fin 2) :
    ∃ σ : FractionRing (PowerSeries k) →ₐ[k] FractionRing (MvPowerSeries (Fin 2) k),
      ∀ x : PowerSeries k, σ (algebraMap _ _ x) = algebraMap (MvPowerSeries (Fin 2) k) _
        (x.subst (MvPowerSeries.X n : MvPowerSeries (Fin 2) k)) := by
  have hs : PowerSeries.HasSubst (MvPowerSeries.X n : MvPowerSeries (Fin 2) k) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  have hX : (MvPowerSeries.X n : MvPowerSeries (Fin 2) k) ≠ 0 := by
    intro h0
    have := congrArg (MvPowerSeries.coeff (Finsupp.single n 1)) h0
    simp [MvPowerSeries.coeff_X] at this
  obtain ⟨σ, hσ⟩ := exists_lift (k := k)
    ((IsScalarTower.toAlgHom k (MvPowerSeries (Fin 2) k) (FractionRing (MvPowerSeries (Fin 2) k))).comp
      (PowerSeries.substAlgHom (R := k) hs)) (by
      rw [AlgHom.comp_apply, PowerSeries.substAlgHom_X, isUnit_iff_ne_zero, IsScalarTower.toAlgHom_apply]
      exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hX)
  refine ⟨σ, fun x => ?_⟩
  rw [hσ, AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, PowerSeries.coe_substAlgHom]

/- English proof (translation)
Introduce `k _ G _ A _ _ j ε r f hc a h d hd ht hreg`. Take `⟨σ₀, h0⟩` from `exists_lift_var k 0`. Take `⟨σ₁, h1⟩` from `exists_lift_var k 1`. Take `⟨L, hloc, hmem, hL0, hL1⟩` from `GlobalTheory.TwoVarValRing.exists_local_ring_second_variable k σ₀ σ₁ h0 h1`. Establish `hd' : algebraMap (MvPowerSeries (Fin 2) k) (FractionRing (MvPowerSeries (Fin 2) k)) d ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hd`.

Take `⟨χ, hχ, he⟩` from `ht (FractionRing (MvPowerSeries (Fin 2) k)) (IsScalarTower.toAlgHom k (MvPowerSeries (Fin 2) k) (FractionRing (MvPowerSeries (Fin 2) k))) σ₀ σ₁ hd' h0 h1`. Establish `hf : ∀ i, χ (f i) ∈ L`. Introduce `i`. Take `⟨u, v, hv, huv⟩` from `hreg i`. Use `hmem _ u v hv ?_` and prove the remaining obligations.

Establish `e1` using `hχ i`. Simplify using `only [IsScalarTower.toAlgHom_apply] at e1`. Establish `e2` using `congrArg (algebraMap (MvPowerSeries (Fin 2) k) (FractionRing (MvPowerSeries (Fin 2) k))) huv`. Rewrite `e2` using `[map_mul, map_mul, ← e1]`. Apply `mul_left_cancel₀ hd'` to reduce the goal to its premises.

Rewrite using `[← e2]`. Expand and normalize the polynomial expressions, which then agree. Establish `hall : ∀ x, χ x ∈ L`. Establish `: Algebra.adjoin k (Set.range f) ≤ L.comap χ` using `Algebra.adjoin_le (by rintro _ ⟨i, rfl⟩; exact hf i)`. Introduce `x`.

Conclude with `this (by rw [hc.2.2.1]; trivial)`. Use `GlobalTheory.SS.ArcInf.exists_extend_of_localSubring k G (PowerSeries k) (FractionRing (PowerSeries k)) (FractionRing (MvPowerSeries (Fin 2) k)) _ σ₁ L hloc (IsFractionRing.injective (PowerSeries k) (FractionRing (PowerSeries k))) hL1 a ((algOverHom (χ.codRestrict L hall) ≫ j) * …` and prove the remaining obligations. Rewrite using `[he, MonObj.comp_mul, ← Category.assoc, ← Category.assoc, ← algOverHom_comp, ← algOverHom_comp]`. Both sides reduce to the same expression.
-/
theorem extends_of_regular_second_axis :
    ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G] (A : Type) [CommRing A] [Algebra k A] (j : algOver k A ⟶ G) (ε : A →ₐ[k] k) (r : ℕ) (f : Fin r → A), IsChart G j ε f → ∀ (a : algOver k (FractionRing (PowerSeries k)) ⟶ G) (h : Fin r → MvPowerSeries (Fin 2) k) (d : MvPowerSeries (Fin 2) k), d ≠ 0 → TwoVar j f a h d → (∀ i, ∃ u v, ¬ MvPowerSeries.X 1 ∣ v ∧ h i * v = d * u) → ∃ b : algOver k (PowerSeries k) ⟶ G, algOverHom (IsScalarTower.toAlgHom k (PowerSeries k) (FractionRing (PowerSeries k))) ≫ b = a := by
  intro k _ G _ A _ _ j ε r f hc a h d hd ht hreg
  obtain ⟨σ₀, h0⟩ := exists_lift_var k 0
  obtain ⟨σ₁, h1⟩ := exists_lift_var k 1
  obtain ⟨L, hloc, hmem, hL0, hL1⟩ := GlobalTheory.TwoVarValRing.exists_local_ring_second_variable k σ₀ σ₁ h0 h1
  have hd' : algebraMap (MvPowerSeries (Fin 2) k) (FractionRing (MvPowerSeries (Fin 2) k)) d ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hd
  obtain ⟨χ, hχ, he⟩ := ht (FractionRing (MvPowerSeries (Fin 2) k))
    (IsScalarTower.toAlgHom k (MvPowerSeries (Fin 2) k) (FractionRing (MvPowerSeries (Fin 2) k))) σ₀ σ₁ hd' h0 h1
  have hf : ∀ i, χ (f i) ∈ L := by
    intro i
    obtain ⟨u, v, hv, huv⟩ := hreg i
    refine hmem _ u v hv ?_
    have e1 := hχ i
    simp only [IsScalarTower.toAlgHom_apply] at e1
    have e2 := congrArg (algebraMap (MvPowerSeries (Fin 2) k) (FractionRing (MvPowerSeries (Fin 2) k))) huv
    rw [map_mul, map_mul, ← e1] at e2
    apply mul_left_cancel₀ hd'
    rw [← e2]
    ring
  have hall : ∀ x, χ x ∈ L := by
    have : Algebra.adjoin k (Set.range f) ≤ L.comap χ :=
      Algebra.adjoin_le (by rintro _ ⟨i, rfl⟩; exact hf i)
    intro x
    exact this (by rw [hc.2.2.1]; trivial)
  refine GlobalTheory.SS.ArcInf.exists_extend_of_localSubring k G (PowerSeries k) (FractionRing (PowerSeries k)) (FractionRing (MvPowerSeries (Fin 2) k))
    _ σ₁ L hloc (IsFractionRing.injective (PowerSeries k) (FractionRing (PowerSeries k))) hL1 a
    ((algOverHom (χ.codRestrict L hall) ≫ j) * (algOverHom (σ₀.codRestrict L hL0) ≫ a)) ?_
  rw [he, MonObj.comp_mul, ← Category.assoc, ← Category.assoc, ← algOverHom_comp, ← algOverHom_comp]
  rfl

end GlobalTheory.SS.ArcInf
