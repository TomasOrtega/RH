import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLiftOfRangeSubset
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SquareOfCubical
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LocallyQuasiFiniteOfFiniteStabiliser
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsClosedStabiliser
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CubicalQuasiFinite

/- English proof (translation)
Take `⟨w, hw⟩` from `hw`. Use `replace hw := (isGen_iff w).1 hw`. Establish `e : translPt B x ≫ φ = snd _ B ≫ φ`. Establish `e₀ : translPt B x = snd _ B ≫ ((toUnit B ≫ x) * 𝟙 B)`. Rewrite using `[MonObj.comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique (snd _ B ≫ toUnit B) (fst _ B)]`.

Both sides reduce to the same expression. Rewrite using `[e₀, Category.assoc, hx]`. Establish `e' : (translPt B x).left ≫ φ.left = (snd _ B).left ≫ φ.left` using `congrArg CommaMorphism.left e`. Take `⟨c, hc, -⟩` from `exists_gen hH (φ' := fun k : Fin 2 => (![(translPt B x).left, (snd _ B).left] : Fin 2 → _) k ≫ φ.left) (ε' := ![1, -1]) (fun U _ f => (Fintype.prod_empty _).trans (by`. Simplify using `only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, e', zpow_one, zpow_neg, mul_inv_cancel])) (LB.oneGen H (Y := (𝟙_ (Over S) ⊗ B).left))`.

Use the proof step `(fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)`. Conclude with `exists_down hw hH hM c hc`.
-/
theorem triv_translDiff_of_fixes {S : Scheme.{0}} {B Z : Over S} [GrpObj B] (φ : B ⟶ Z) {M : LB B.left}
    {H : LB Z.left} (hM : M.IsLB) (hH : H.IsLB) (hw : LBIso M (H.pull φ.left)) (x : 𝟙_ (Over S) ⟶ B)
    (hx : ((toUnit B ≫ x) * 𝟙 B) ≫ φ = φ) : Triv (translDiff B M x) := by
  obtain ⟨w, hw⟩ := hw
  replace hw := (isGen_iff w).1 hw
  have e : translPt B x ≫ φ = snd _ B ≫ φ := by
    have e₀ : translPt B x = snd _ B ≫ ((toUnit B ≫ x) * 𝟙 B) := by
      rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc,
        toUnit_unique (snd _ B ≫ toUnit B) (fst _ B)]
      rfl
    rw [e₀, Category.assoc, hx]
  have e' : (translPt B x).left ≫ φ.left = (snd _ B).left ≫ φ.left := congrArg CommaMorphism.left e
  obtain ⟨c, hc, -⟩ := exists_gen hH
    (φ' := fun k : Fin 2 => (![(translPt B x).left, (snd _ B).left] : Fin 2 → _) k ≫ φ.left) (ε' := ![1, -1])
    (fun U _ f => (Fintype.prod_empty _).trans (by
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, e', zpow_one, zpow_neg,
        mul_inv_cancel])) (LB.oneGen H (Y := (𝟙_ (Over S) ⊗ B).left))
    (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans
      (_root_.mul_one _)).symm)
  exact exists_down hw hH hM c hc

/- English proof (translation)
Introduce `hcount K _ _ B _ _ hB L c r n hn hnK hnr hK Z _ _ φ H hH hw`. Take `⟨C, W, hW, hC, hCW⟩` from `GlobalTheory.Stabiliser.exists_closed_stabiliser K B hB Z φ`. Establish `hfin : Finite C`. Use `GlobalTheory.AbelianSubgroupFinite.finite_of_no_torsion hcount K B n hB hn hnK C W hW hCW fun x hx hxn => ?_` and prove the remaining obligations. Establish `h₁ : Triv (translDiff B L.L (x ^ r))` using `((GlobalTheory.Square.square_of_cubical _ B L c K (𝟙 _)).2 r x).1 (triv_translDiff_of_fixes φ (isLB_pw L.isLB r) hH hw x ((hC x).1 hx))`.

Establish `h₂ : x ^ r = 1` using `hK (x ^ r) (by`. Express the relevant statement in the definitionally equal form `(x ^ r) ^ n = 1`. Rewrite using `[← pow_mul, _root_.mul_comm, pow_mul, hxn, one_pow]) h₁`. Establish `h₃` using `pow_gcd_eq_one.2 ⟨hxn, h₂⟩`. Rewrite `h₃` using `[(Nat.Prime.coprime_iff_not_dvd hn).2 hnr, pow_one]`. Then use the resulting hypothesis.

Use `GlobalTheory.FiniteStabiliser.locallyQuasiFinite_of_finite_stabiliser K B hB Z φ ?_` and prove the remaining obligations. Establish `e : {x : 𝟙_ _ ⟶ B | ((toUnit B ≫ x) * 𝟙 B) ≫ φ = φ} = (C : Set _)` using `Set.ext fun x => (hC x).symm`. Rewrite using `[e]`. Conclude with `Set.toFinite _`.
-/
theorem locallyQuasiFinite_of_pow_iso_pull : (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) → ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ (L : RigLB B) (_ : CubicalStr B L) (r n : ℕ), n.Prime → (n : K) ≠ 0 → ¬ n ∣ r → (∀ x : baseOver _ ⟶ B, x ^ n = 1 → Triv (translDiff B L.L x) → x = 1) → ∀ (Z : Over (Spec (CommRingCat.of K))) [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] (φ : B ⟶ Z) (H : LB Z.left), H.IsLB → LBIso (pw L.L r) (H.pull φ.left) → LocallyQuasiFinite φ.left := by
  intro hcount K _ _ B _ _ hB L c r n hn hnK hnr hK Z _ _ φ H hH hw
  obtain ⟨C, W, hW, hC, hCW⟩ := GlobalTheory.Stabiliser.exists_closed_stabiliser K B hB Z φ
  have hfin : Finite C := by
    refine GlobalTheory.AbelianSubgroupFinite.finite_of_no_torsion hcount K B n hB hn hnK C W hW hCW fun x hx hxn => ?_
    have h₁ : Triv (translDiff B L.L (x ^ r)) :=
      ((GlobalTheory.Square.square_of_cubical _ B L c K (𝟙 _)).2 r x).1
        (triv_translDiff_of_fixes φ (isLB_pw L.isLB r) hH hw x ((hC x).1 hx))
    have h₂ : x ^ r = 1 := hK (x ^ r) (by
      change (x ^ r) ^ n = 1
      rw [← pow_mul, _root_.mul_comm, pow_mul, hxn, one_pow]) h₁
    have h₃ := pow_gcd_eq_one.2 ⟨hxn, h₂⟩
    rwa [(Nat.Prime.coprime_iff_not_dvd hn).2 hnr, pow_one] at h₃
  refine GlobalTheory.FiniteStabiliser.locallyQuasiFinite_of_finite_stabiliser K B hB Z φ ?_
  have e : {x : 𝟙_ _ ⟶ B | ((toUnit B ≫ x) * 𝟙 B) ≫ φ = φ} = (C : Set _) := Set.ext fun x => (hC x).symm
  rw [e]
  exact Set.toFinite _

end GlobalTheory.CubicalQuasiFinite
