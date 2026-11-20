import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MulPullOfCubeOfSymm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UU

/- English proof (translation)
Take `⟨a, ha⟩` from `h`. Establish `mem : ∀ (x : X) (j k : L.ι), F x ∈ L.U j → x ∈ L.U k → x ∈ LB.wchart L ![F, 𝟙 X] ![j, k]` using `fun x j k hj hk => Set.mem_iInter.2 fun i => by fin_cases i`. Conclude with `hj`. Conclude with `hk`. Establish `le : ∀ p : (L.pull F).ι × L.ι, (L.pull F).U p.1 ⊓ L.U p.2 ≤ LB.wchart L ![F, 𝟙 X] ![p.1 PUnit.unit, p.2]` using `fun p x hx => mem x _ _ (mem_pull.1 hx.1) hx.2`.

Set `w : LB.Iso (pw L t) (L.pull F)` to `⟨fun p => res (le p) (a.s _)⟩`. Use `⟨w, (isGen_iff w).2 fun Y r y j j' k k' hj hj' hk hk' => ?_⟩` and prove the remaining obligations. Establish `e : ∀ j k, F (r y) ∈ L.U j → r y ∈ L.U k → gw w r y j k = gm r y (LB.wchart L ![F, 𝟙 X] ![j, k]) (a.s ![j, k])` using `fun j k hj hk => gm_res r y (le (fun _ => j, k)) ⟨mem_pull.2 hj, hk⟩ _`. Rewrite using `[e j k hj hk, e j' k' hj' hk', gen_trans ha r y (mem _ _ _ hj hk) (mem _ _ _ hj' hk'), trF, Fin.prod_univ_two]`. Use `congr 1`.

Use `show gm (r ≫ F) y _ (L.g j j') ^ (1 : ℤ) * gm (r ≫ 𝟙 X) y _ (L.g k k') ^ (-t) = gm (r ≫ F) y _ (L.g j j') * (gm r y (L.U k ⊓ L.U k') (L.g k k' ^ t))⁻¹`. Rewrite using `[zpow_one, Category.comp_id, map_zpow, zpow_neg]`.
-/
theorem lbIso_pw_pull_of_hasGen {X : Scheme.{0}} {L : LB X} (F : X ⟶ X) (t : ℤ)
    (h : MulPull.HasGen L (K := Fin 2) ![F, 𝟙 X] ![1, -t]) : LBIso (pw L t) (L.pull F) := by
  obtain ⟨a, ha⟩ := h
  have mem : ∀ (x : X) (j k : L.ι), F x ∈ L.U j → x ∈ L.U k → x ∈ LB.wchart L ![F, 𝟙 X] ![j, k] :=
    fun x j k hj hk => Set.mem_iInter.2 fun i => by
      fin_cases i
      · exact hj
      · exact hk
  have le : ∀ p : (L.pull F).ι × L.ι,
      (L.pull F).U p.1 ⊓ L.U p.2 ≤ LB.wchart L ![F, 𝟙 X] ![p.1 PUnit.unit, p.2] :=
    fun p x hx => mem x _ _ (mem_pull.1 hx.1) hx.2
  let w : LB.Iso (pw L t) (L.pull F) := ⟨fun p => res (le p) (a.s _)⟩
  refine ⟨w, (isGen_iff w).2 fun Y r y j j' k k' hj hj' hk hk' => ?_⟩
  have e : ∀ j k, F (r y) ∈ L.U j → r y ∈ L.U k →
      gw w r y j k = gm r y (LB.wchart L ![F, 𝟙 X] ![j, k]) (a.s ![j, k]) := fun j k hj hk =>
    gm_res r y (le (fun _ => j, k)) ⟨mem_pull.2 hj, hk⟩ _
  rw [e j k hj hk, e j' k' hj' hk', gen_trans ha r y (mem _ _ _ hj hk) (mem _ _ _ hj' hk'), trF, Fin.prod_univ_two]
  congr 1
  show gm (r ≫ F) y _ (L.g j j') ^ (1 : ℤ) * gm (r ≫ 𝟙 X) y _ (L.g k k') ^ (-t) =
    gm (r ≫ F) y _ (L.g j j') * (gm r y (L.U k ⊓ L.U k') (L.g k k' ^ t))⁻¹
  rw [zpow_one, Category.comp_id, map_zpow, zpow_neg]

/- English proof (translation)
Establish `hL` using `M.L.isLB`. Establish `hcube : MulPull.HasGen M.L.L (thφ B (x3 B)) thε` using `⟨M.c.t, M.c.isGen⟩`. Establish `hrig : MulPull.HasGen M.L.L (K` using `PUnit) (fun _ => eSec B) (fun _ => 1) := ⟨M.L.rig, M.L.rigGen⟩`. Establish `hsym : MulPull.HasGen M.L.L (K` using `Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1] := ⟨M.sym, M.sym_gen⟩`. Establish `h` using `MulPull.hasGen_pow hL hcube (𝟙 B) ((hrig.pull B.hom).of_formEq hL (fun U _ h => by`.

Simplify using `only [Finset.univ_unique, Finset.prod_singleton, Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, _root_.mul_one, one_left]`. Use the proof step `rfl))`. Use the proof step `(hsym.inv.of_formEq hL (fun U _ h => by`. Rewrite using `[Fin.prod_univ_two, Fin.prod_univ_two, Hom.inv_def, Category.id_comp, mul_comm]`. Use the proof step `rfl)) n`.

Use `lbIso_pw_pull_of_hasGen _ _ (h.inv.of_formEq hL fun U _ h => ?_)` and prove the remaining obligations. Rewrite using `[Fin.prod_univ_two, Fin.prod_univ_two, mul_comm]`. Both sides reduce to the same expression.
-/
theorem CP.lbIso_pw_pull_pow {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] (M : CP B) (n : ℕ) :
    LBIso (pw M.L.L ((n : ℤ) ^ 2)) (M.L.L.pull (𝟙 B ^ n).left) := by
  have hL := M.L.isLB
  have hcube : MulPull.HasGen M.L.L (thφ B (x3 B)) thε := ⟨M.c.t, M.c.isGen⟩
  have hrig : MulPull.HasGen M.L.L (K := PUnit) (fun _ => eSec B) (fun _ => 1) := ⟨M.L.rig, M.L.rigGen⟩
  have hsym : MulPull.HasGen M.L.L (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1] := ⟨M.sym, M.sym_gen⟩
  have h := MulPull.hasGen_pow hL hcube (𝟙 B) ((hrig.pull B.hom).of_formEq hL (fun U _ h => by
      simp only [Finset.univ_unique, Finset.prod_singleton, Fin.prod_univ_succ, Fin.prod_univ_zero,
        Matrix.cons_val_zero, _root_.mul_one, one_left]
      rfl))
    (hsym.inv.of_formEq hL (fun U _ h => by
      rw [Fin.prod_univ_two, Fin.prod_univ_two, Hom.inv_def, Category.id_comp, mul_comm]
      rfl)) n
  refine lbIso_pw_pull_of_hasGen _ _ (h.inv.of_formEq hL fun U _ h => ?_)
  rw [Fin.prod_univ_two, Fin.prod_univ_two, mul_comm]
  rfl

/- English proof (translation)
Introduce `_ _ _ _ _ _ M n` and use `M.lbIso_pw_pull_pow n`.
-/
theorem lbIso_pw_pull_pow_local : ∀ (A : Type) [CommRing A] [IsLocalRing A] (B : Over (Spec (CommRingCat.of A))) [GrpObj B] [IsCommMonObj B] (M : CP B) (n : ℕ), LBIso (pw M.L.L ((n : ℤ) ^ 2)) (M.L.L.pull (𝟙 B ^ n).left) :=
  fun _ _ _ _ _ _ M n => M.lbIso_pw_pull_pow n

end GlobalTheory.UU
end
