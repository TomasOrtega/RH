import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifPowOf3
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsMatrixRingAct
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjMul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjointOfBoxProjectionsStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.MatrixRosati

/- English proof (translation)
Introduce `_ _` and use `(map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm`.
-/
theorem oneGen_isGen {X Y : Scheme.{0}} (L : LB X) : (LB.oneGen L (Y := Y)).IsGen := fun _ _ =>
  (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm

/- English proof (translation)
Introduce `s`. Use `⟨⊤, trivial, ?_⟩` and prove the remaining obligations. Set `W : (A ⊗ A).left.Opens` to `(A ⊗ A).hom ⁻¹ᵁ ⊤`. Set `T : Over S` to `Over.mk (W.ι ≫ (A ⊗ A).hom)`. Set `ρ : T ⟶ A ⊗ A` to `Over.homMk W.ι rfl`.

Take `⟨x, y, hxy⟩ : ∃ x y : T ⟶ A, (lift x y).left = W.ι` from `⟨ρ ≫ fst A A, ρ ≫ snd A A, congrArg (fun q => q.left) (lift_comp_fst_snd ρ)⟩`. Take `⟨u, hu, -⟩` from `exists_gen hL (φ' := fun i => W.ι ≫ rosatiφ A 1 1 i) (ε' := rosatiε) (fun V _ k => by`. Use `Eq.trans ?_ ((prod_ros 1 1 x y k).symm.trans (Finset.prod_congr rfl fun i _ => by rw [hxy]))` and prove the remaining obligations. Rewrite using `[MonObj.comp_one, MonObj.comp_one, _root_.one_mul, _root_.mul_one]`. Simplify using `[mul_comm, mul_left_comm])`.

Use the proof step `(LB.oneGen L (Y := W)) (oneGen_isGen _)`. Conclude with `⟨u, hu⟩`.
-/
theorem rosatiAdj_one {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left)
    (hL : L.IsLB) : RosatiAdj A L 1 1 := by
  intro s
  refine ⟨⊤, trivial, ?_⟩
  let W : (A ⊗ A).left.Opens := (A ⊗ A).hom ⁻¹ᵁ ⊤
  let T : Over S := Over.mk (W.ι ≫ (A ⊗ A).hom)
  let ρ : T ⟶ A ⊗ A := Over.homMk W.ι rfl
  obtain ⟨x, y, hxy⟩ : ∃ x y : T ⟶ A, (lift x y).left = W.ι :=
    ⟨ρ ≫ fst A A, ρ ≫ snd A A, congrArg (fun q => q.left) (lift_comp_fst_snd ρ)⟩
  obtain ⟨u, hu, -⟩ := exists_gen hL (φ' := fun i => W.ι ≫ rosatiφ A 1 1 i) (ε' := rosatiε)
    (fun V _ k => by
      refine Eq.trans ?_ ((prod_ros 1 1 x y k).symm.trans
        (Finset.prod_congr rfl fun i _ => by rw [hxy]))
      rw [MonObj.comp_one, MonObj.comp_one, _root_.one_mul, _root_.mul_one]
      simp [mul_comm, mul_left_comm])
    (LB.oneGen L (Y := W)) (oneGen_isGen _)
  exact ⟨u, hu⟩

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using rosatiAdj_one A L.L L.isLB`. Consider the case `insert i s hi ih`. Rewrite using `[Finset.prod_insert hi, Finset.prod_insert hi]`. Conclude with `GlobalTheory.rosatiAdj_mul S A L c _ _ _ _ (h i (Finset.mem_insert_self _ _)) (ih fun k hk => h k (Finset.mem_insert_of_mem hk))`.
-/
theorem rosatiAdj_prod {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A)
    (c : CubicalStr A L) {κ : Type} (s : Finset κ) (f g : κ → (A ⟶ A))
    (h : ∀ k ∈ s, RosatiAdj A L.L (f k) (g k)) :
    RosatiAdj A L.L (∏ k ∈ s, f k) (∏ k ∈ s, g k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using rosatiAdj_one A L.L L.isLB
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact GlobalTheory.rosatiAdj_mul S A L c _ _ _ _ (h i (Finset.mem_insert_self _ _))
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

/- English proof (translation)
Introduce `S P P' j p w hw L' hL' ⟨c⟩ O _ _ ιA`. Take `⟨ρ, hρ⟩` from `GlobalTheory.MatrixAction.exists_matrix_ringAct S P.A P'.A j p O ιA.toRingAct`. Establish `hs : ∀ (i l : Fin j) (a : O) (s : Fin j), ρ.act (Matrix.single i l a) ≫ p.pr s = if s = i then p.pr l ≫ ιA.act a else 1`. Introduce `i l a s`. Rewrite using `[hρ]`.

Use `split_ifs with h`. Substitute `h` using the available equality. Rewrite using `[Finset.prod_eq_single l]`. Rewrite using `[Matrix.single_apply_same]`. Introduce `t _ ht`.

Rewrite using `[Matrix.single_apply_of_col_ne _ _ ht.symm, GlobalTheory.MatrixAction.act_zero, MonObj.comp_one]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ l) h`. Use `Finset.prod_eq_one fun t _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.single_apply_of_row_ne (Ne.symm h), GlobalTheory.MatrixAction.act_zero, MonObj.comp_one]`.

Use `⟨⟨ρ, fun m => ?_⟩, hρ⟩` and prove the remaining obligations. Establish `e1 : m = ∑ k : Fin j × Fin j, Matrix.single k.1 k.2 (m k.1 k.2)`. Rewrite using `[Fintype.sum_prod_type]`. Conclude with `Matrix.matrix_eq_sum_single m`. Establish `e2 : star m = ∑ k : Fin j × Fin j, Matrix.single k.2 k.1 (star (m k.1 k.2))`.

Rewrite using `[Fintype.sum_prod_type_right]`. Conclude with `Matrix.matrix_eq_sum_single (star m)`. Rewrite using `[e2]`. Use `conv => enter [3, 2]`. Rewrite using `[e1]`.

Rewrite using `[GlobalTheory.MatrixAction.act_sum, GlobalTheory.MatrixAction.act_sum, ← hL']`. Use `rosatiAdj_prod P'.A L' c _ _ _ fun k _ => ?_` and prove the remaining obligations. Rewrite using `[hL']`. Conclude with `GlobalTheory.T.rosati_adjoint_of_box_projections S P.A P'.A j p P.L P'.L P.isLB P'.isLB w hw _ _ _ _ k.1 k.2 (hs _ _ _) (hs _ _ _) (ιA.rosati _)`.
-/
theorem exists_matrix_oAct : ∀ (S : Scheme.{0}) (P P' : PolAV S) (j : ℕ) (p : IsPowGrp P'.A P.A j) (w : LB.Iso P'.L (boxLB P.L p.pr)), w.IsGen → ∀ (L' : RigLB P'.A), L'.L = P'.L → Nonempty (CubicalStr P'.A L') → ∀ (O : Type) [Ring O] [StarRing O] (ιA : P.OAct O), ∃ ι' : P'.OAct (Matrix (Fin j) (Fin j) O), (∀ (m : (Matrix (Fin j) (Fin j) O)) (i : Fin j), ι'.act m ≫ p.pr i = ∏ l, p.pr l ≫ ιA.act (m i l)) := by
  intro S P P' j p w hw L' hL' ⟨c⟩ O _ _ ιA
  obtain ⟨ρ, hρ⟩ := GlobalTheory.MatrixAction.exists_matrix_ringAct S P.A P'.A j p O ιA.toRingAct
  have hs : ∀ (i l : Fin j) (a : O) (s : Fin j), ρ.act (Matrix.single i l a) ≫ p.pr s
      = if s = i then p.pr l ≫ ιA.act a else 1 := by
    intro i l a s
    rw [hρ]
    split_ifs with h
    · subst h
      rw [Finset.prod_eq_single l]
      · rw [Matrix.single_apply_same]
      · intro t _ ht
        rw [Matrix.single_apply_of_col_ne _ _ ht.symm, GlobalTheory.MatrixAction.act_zero, MonObj.comp_one]
      · intro h
        exact absurd (Finset.mem_univ l) h
    · refine Finset.prod_eq_one fun t _ => ?_
      rw [Matrix.single_apply_of_row_ne (Ne.symm h), GlobalTheory.MatrixAction.act_zero, MonObj.comp_one]
  refine ⟨⟨ρ, fun m => ?_⟩, hρ⟩
  have e1 : m = ∑ k : Fin j × Fin j, Matrix.single k.1 k.2 (m k.1 k.2) := by
    rw [Fintype.sum_prod_type]
    exact Matrix.matrix_eq_sum_single m
  have e2 : star m = ∑ k : Fin j × Fin j, Matrix.single k.2 k.1 (star (m k.1 k.2)) := by
    rw [Fintype.sum_prod_type_right]
    exact Matrix.matrix_eq_sum_single (star m)
  rw [e2]
  conv => enter [3, 2]; rw [e1]
  rw [GlobalTheory.MatrixAction.act_sum, GlobalTheory.MatrixAction.act_sum, ← hL']
  refine rosatiAdj_prod P'.A L' c _ _ _ fun k _ => ?_
  rw [hL']
  exact GlobalTheory.T.rosati_adjoint_of_box_projections S P.A P'.A j p P.L P'.L P.isLB P'.isLB w hw _ _ _ _ k.1 k.2
    (hs _ _ _) (hs _ _ _) (ιA.rosati _)

end GlobalTheory.MatrixRosati
