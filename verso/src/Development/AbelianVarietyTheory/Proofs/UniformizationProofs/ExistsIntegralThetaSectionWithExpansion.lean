import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsProjectiveRep
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFourierJacobiExpansionOverFieldStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.ThetaIntegral

/- English proof (translation)
Use `(congrArg (gs r z _) (h _)).trans ?_` and prove the remaining obligations. Unfold `gs`. Use `split_ifs`. Conclude with `(congrArg _ (map_zero _)).trans (map_zero _)`. Both sides reduce to the same expression.
-/
theorem sval_eq_zero {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (h : ∀ j, s.f j = 0) (r : Z ⟶ Y) (z : Z) (J) : sval s r z J = 0 := by
  refine (congrArg (gs r z _) (h _)).trans ?_
  unfold gs
  split_ifs
  · exact (congrArg _ (map_zero _)).trans (map_zero _)
  · rfl

/- English proof (translation)
Take `⟨-, -, hr, -⟩` from `GlobalTheory.ThetaRep.exists_projective_rep h1 h2 S P F p 1 (by simp)`. Establish `: Nontrivial Γ((Over.mk p).left, ⊤)` using `(Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toEquiv.nontrivial`. Establish `: Nontrivial (SecM P.A P.L ((1 : ℕ) : ℤ) (Over.mk p))` using `Module.nontrivial_of_finrank_pos (R := Γ((Over.mk p).left, ⊤)) (by rw [hr]; simp)`. Conclude with `exists_ne 0`.
-/
theorem exists_sec_ne_zero (h1 : Laws) (h2 : Laws2) (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (F : Type)
    [Field F] [IsAlgClosed F] (p : Spec (CommRingCat.of F) ⟶ S) :
    ∃ v : SecM P.A P.L ((1 : ℕ) : ℤ) (Over.mk p), v ≠ 0 := by
  obtain ⟨-, -, hr, -⟩ := GlobalTheory.ThetaRep.exists_projective_rep h1 h2 S P F p 1 (by simp)
  have : Nontrivial Γ((Over.mk p).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  have : Nontrivial (SecM P.A P.L ((1 : ℕ) : ℤ) (Over.mk p)) :=
    Module.nontrivial_of_finrank_pos (R := Γ((Over.mk p).left, ⊤)) (by rw [hr]; simp)
  exact exists_ne 0

/- English proof (translation)
Introduce `h1 h2 V _ _ _ hV D A G _ _ U`. Take `⟨v, hv⟩` from `exists_sec_ne_zero h1 h2 _ A (Kbar V) (jFK (R := V) (Kbar V))`. Take `⟨s, n, c, σ, f, hE, hA, -⟩` from `GlobalTheory.T.exists_fourierJacobi_expansion_over_field h1 h2 V hV D A G U (Kbar V) 1 le_rfl (SecM.toSec A.A v)`. Assume the negation of the conclusion as `hn`. Establish `hz : ∀ i j, (σ i).f j = 0` using `fun i j => by`.

Assume the negation of the conclusion as `h`. Conclude with `hn ⟨σ i, f i, hE i, j, h⟩`. Use `hv (Subtype.ext (funext fun j => ?_))` and prove the remaining obligations. Use `sec_ext_val (L := A.L) (φ := fun _ : Fin 1 => (snd (TFK (R := V) (Kbar V)) A.A).left) (ε := fun _ => ((1 : ℕ) : ℤ)) A.isLB (s := SecM.toSec A.A v) (s' := SecM.toSec A.A 0) (fun z JA hJA => ?_) j` and prove the remaining obligations. Take `⟨JG, hJG⟩` from `exists_good_pt U.P.L.isLB z`.

Set `y` to `(snd (TFK (R := V) (Kbar V)) A.A).left ≫ U.gen.inv.left`. Set `T : Over (Spec (CommRingCat.of V))` to `Over.mk ((y ≫ pullback.fst G.hom (jK V)) ≫ G.hom)`. Set `x : T ⟶ G` to `Over.homMk (y ≫ pullback.fst G.hom (jK V)) rfl`. Establish `e` using `hA _ (𝟙 _) y (lift (toUnit T) x).left (by rw [Category.id_comp, Category.assoc, ← Over.comp_left, Iso.inv_hom_id, Over.id_left, Category.comp_id]) (congrArg (fun q => q.left) (lift_snd (toUnit T) x)) z JA JG hJA hJG`. Rewrite `e` using `[Finset.sum_eq_zero fun i _ => by rw [sval_eq_zero (σ i) (hz i), mul_zero], ← Units.val_pow_eq_pow_val, Units.mul_right_eq_zero]`.

Conclude with `e.trans (sval_eq_zero _ (fun _ => rfl) _ _ _).symm`.
-/
theorem exists_theta : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∃ θ f, U.Theta θ f) := by
  intro h1 h2 V _ _ _ hV D A G _ _ U
  obtain ⟨v, hv⟩ := exists_sec_ne_zero h1 h2 _ A (Kbar V) (jFK (R := V) (Kbar V))
  obtain ⟨s, n, c, σ, f, hE, hA, -⟩ := GlobalTheory.T.exists_fourierJacobi_expansion_over_field h1 h2 V hV D A G U (Kbar V) 1 le_rfl (SecM.toSec A.A v)
  by_contra hn
  have hz : ∀ i j, (σ i).f j = 0 := fun i j => by
    by_contra h
    exact hn ⟨σ i, f i, hE i, j, h⟩
  refine hv (Subtype.ext (funext fun j => ?_))
  refine sec_ext_val (L := A.L) (φ := fun _ : Fin 1 => (snd (TFK (R := V) (Kbar V)) A.A).left)
    (ε := fun _ => ((1 : ℕ) : ℤ)) A.isLB (s := SecM.toSec A.A v) (s' := SecM.toSec A.A 0) (fun z JA hJA => ?_) j
  obtain ⟨JG, hJG⟩ := exists_good_pt U.P.L.isLB z
  let y := (snd (TFK (R := V) (Kbar V)) A.A).left ≫ U.gen.inv.left
  let T : Over (Spec (CommRingCat.of V)) := Over.mk ((y ≫ pullback.fst G.hom (jK V)) ≫ G.hom)
  let x : T ⟶ G := Over.homMk (y ≫ pullback.fst G.hom (jK V)) rfl
  have e := hA _ (𝟙 _) y (lift (toUnit T) x).left
    (by rw [Category.id_comp, Category.assoc, ← Over.comp_left, Iso.inv_hom_id, Over.id_left, Category.comp_id])
    (congrArg (fun q => q.left) (lift_snd (toUnit T) x)) z JA JG hJA hJG
  rw [Finset.sum_eq_zero fun i _ => by rw [sval_eq_zero (σ i) (hz i), mul_zero], ← Units.val_pow_eq_pow_val,
    Units.mul_right_eq_zero] at e
  exact e.trans (sval_eq_zero _ (fun _ => rfl) _ _ _).symm

end GlobalTheory.ThetaIntegral
