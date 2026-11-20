import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsPowGrpBaseChange

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Geo.Tor in

noncomputable def chartPullPullLinComb {X X' Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]
    (pr : K → (X' ⟶ X)) (ε : K → ℤ) (F : Y ⟶ X') (g : Z ⟶ X) (p : K → (Y ⟶ Z))
    (hc : ∀ k, p k ≫ g = F ≫ pr k) :
    ChartPull ((LB.LinComb L pr ε).pull F) (LB.LinComb (L.pull g) p ε) (𝟙 Y) :=
  have le : ∀ J : PUnit → K → L.ι, ((LB.LinComb L pr ε).pull F).U J ≤
      LB.wchart (L.pull g) p (fun k _ => J PUnit.unit k) := fun J y hy =>
    Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun _ => by
      have h1 : (F ≫ pr k) y ∈ L.U (J PUnit.unit k) :=
        Set.mem_iInter.1 (Set.mem_iInter.1 hy PUnit.unit) k
      rw [← hc k] at h1
      exact h1
  { idx := fun J k _ => J PUnit.unit k
    le := le
    g := fun y J J' hj hj' => by
      refine (gm_pull_g (LB.LinComb L pr ε) F (𝟙 Y) y J J' hj hj').trans ?_
      refine (gm_linComb L pr ε (𝟙 Y ≫ F) y _ _ (Set.mem_iInter.1 hj PUnit.unit)
        (Set.mem_iInter.1 hj' PUnit.unit)).trans
        (Eq.trans (Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k) ?_)
          (gm_linComb (L.pull g) p ε (𝟙 Y) y _ _ (le J hj) (le J' hj')).symm)
      refine Eq.trans ?_ (gm_pull_g L g (𝟙 Y ≫ p k) y _ _ (Set.mem_iInter.1 (le J hj) k)
        (Set.mem_iInter.1 (le J' hj') k)).symm
      rw [Category.assoc, Category.assoc, hc] }

/- English proof (translation)
Establish `ext : ∀ (a b : H ⊗ H ⟶ G'), (∀ i, a ≫ p.pr i = b ≫ p.pr i) → a = b` using `fun a b h => Fan.IsLimit.hom_ext p.lim a b h`. Establish `ext1 : ∀ (a b : 𝟙_ (Over S) ⟶ G'), (∀ i, a ≫ p.pr i = b ≫ p.pr i) → a = b` using `fun a b h => Fan.IsLimit.hom_ext p.lim a b h`. Prove the components needed by the constructor for the conclusion. Use `ext1 _ _ fun i => ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, (hf i).one_hom, (p.hom i).one_hom]`.

Use `ext _ _ fun i => ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, (hf i).mul_hom, Category.assoc, (p.hom i).mul_hom, ← Category.assoc (f ⊗ₘ f), tensorHom_comp_tensorHom]`.
-/
theorem isMonHom_of_isPowGrp {S : Scheme.{0}} {H G' G : Over S} [GrpObj H] [GrpObj G'] [GrpObj G]
    {j : ℕ} (p : IsPowGrp G' G j) (f : H ⟶ G') (hf : ∀ i, IsMonHom (f ≫ p.pr i)) : IsMonHom f := by
  have ext : ∀ (a b : H ⊗ H ⟶ G'), (∀ i, a ≫ p.pr i = b ≫ p.pr i) → a = b :=
    fun a b h => Fan.IsLimit.hom_ext p.lim a b h
  have ext1 : ∀ (a b : 𝟙_ (Over S) ⟶ G'), (∀ i, a ≫ p.pr i = b ≫ p.pr i) → a = b :=
    fun a b h => Fan.IsLimit.hom_ext p.lim a b h
  constructor
  · refine ext1 _ _ fun i => ?_
    rw [Category.assoc, (hf i).one_hom, (p.hom i).one_hom]
  · refine ext _ _ fun i => ?_
    rw [Category.assoc, (hf i).mul_hom, Category.assoc, (p.hom i).mul_hom, ← Category.assoc (f ⊗ₘ f),
      tensorHom_comp_tensorHom]

/- English proof (translation)
Set `u : H' ⟶ G'` to `Fan.IsLimit.lift p.lim fun i => q.pr i ≫ e.hom`. Set `v : G' ⟶ H'` to `Fan.IsLimit.lift q.lim fun i => p.pr i ≫ e.inv`. Establish `hu : ∀ i, u ≫ p.pr i = q.pr i ≫ e.hom` using `fun i => Fan.IsLimit.fac p.lim _ i`. Establish `hv : ∀ i, v ≫ q.pr i = p.pr i ≫ e.inv` using `fun i => Fan.IsLimit.fac q.lim _ i`. Establish `huv : u ≫ v = 𝟙 H'` using `Fan.IsLimit.hom_ext q.lim _ _ fun i => by`.

Express the relevant statement in the definitionally equal form `(u ≫ v) ≫ q.pr i = 𝟙 H' ≫ q.pr i`. Rewrite using `[Category.assoc, hv i, ← Category.assoc, hu i, Category.assoc, e.hom_inv_id, Category.comp_id, Category.id_comp]`. Establish `hvu : v ≫ u = 𝟙 G'` using `Fan.IsLimit.hom_ext p.lim _ _ fun i => by`. Express the relevant statement in the definitionally equal form `(v ≫ u) ≫ p.pr i = 𝟙 G' ≫ p.pr i`. Rewrite using `[Category.assoc, hu i, ← Category.assoc, hv i, Category.assoc, e.inv_hom_id, Category.comp_id, Category.id_comp]`.

Use `⟨⟨u, v, huv, hvu⟩, ?_, hu⟩` and prove the remaining obligations. Use `isMonHom_of_isPowGrp p _ fun i => ?_` and prove the remaining obligations. Establish `: IsMonHom (q.pr i)` using `q.hom i`. Express the relevant statement in the definitionally equal form `IsMonHom (u ≫ p.pr i)`. Rewrite using `[hu i]`.

Use `infer_instance`.
-/
theorem exists_iso_of_isPowGrp {S : Scheme.{0}} {H' H G' G : Over S} [GrpObj H'] [GrpObj H]
    [GrpObj G'] [GrpObj G] {j : ℕ} (q : IsPowGrp H' H j) (p : IsPowGrp G' G j) (e : H ≅ G)
    [IsMonHom e.hom] :
    ∃ e' : H' ≅ G', IsMonHom e'.hom ∧ ∀ i, e'.hom ≫ p.pr i = q.pr i ≫ e.hom := by
  let u : H' ⟶ G' := Fan.IsLimit.lift p.lim fun i => q.pr i ≫ e.hom
  let v : G' ⟶ H' := Fan.IsLimit.lift q.lim fun i => p.pr i ≫ e.inv
  have hu : ∀ i, u ≫ p.pr i = q.pr i ≫ e.hom := fun i => Fan.IsLimit.fac p.lim _ i
  have hv : ∀ i, v ≫ q.pr i = p.pr i ≫ e.inv := fun i => Fan.IsLimit.fac q.lim _ i
  have huv : u ≫ v = 𝟙 H' := Fan.IsLimit.hom_ext q.lim _ _ fun i => by
    change (u ≫ v) ≫ q.pr i = 𝟙 H' ≫ q.pr i
    rw [Category.assoc, hv i, ← Category.assoc, hu i, Category.assoc, e.hom_inv_id, Category.comp_id,
      Category.id_comp]
  have hvu : v ≫ u = 𝟙 G' := Fan.IsLimit.hom_ext p.lim _ _ fun i => by
    change (v ≫ u) ≫ p.pr i = 𝟙 G' ≫ p.pr i
    rw [Category.assoc, hu i, ← Category.assoc, hv i, Category.assoc, e.inv_hom_id, Category.comp_id,
      Category.id_comp]
  refine ⟨⟨u, v, huv, hvu⟩, ?_, hu⟩
  refine isMonHom_of_isPowGrp p _ fun i => ?_
  have : IsMonHom (q.pr i) := q.hom i
  change IsMonHom (u ≫ p.pr i)
  rw [hu i]
  infer_instance

open ReciprocityTheory.ChartRestriction.G.Geo.Tor in

/- English proof (translation)
Introduce `R _ _ I j D D' A A' G G' _ _ _ _ pD pA pG U`. Establish `: IsMonHom U.gen.hom` using `U.gen_hom`. Take `⟨p', hp'⟩` from `isPowGrp_baseChange _ _ (jK R) G' G j pG`. Take `⟨e', he', hc⟩` from `exists_iso_of_isPowGrp p' pA.toIsPowGrp U.gen`. Use `⟨e', he', fun i => by rw [hc i, hp' i], ?_⟩` and prove the remaining obligations.

Take `⟨w0, hw0⟩` from `U.ext`. Establish `pullCP : ∀ {X Y : Scheme.{0}} (L : LB X) (F : Y ⟶ X), ChartPull (L.pull F) L F` using `fun L F => { idx := fun J => J PUnit.unit le := fun J y hy => (mem_pull (L := L) (F := F) (x := y) (J := J)).1 hy g := fun y J J' hj hj' => (gm_pull_g L F (𝟙 _) y J J' hj hj').trans (by rw [Category.id_comp]) }`. Establish `hcA : ∀ k, (p'.pr k).left ≫ U.gen.hom.left = e'.hom.left ≫ (pA.pr k).left` using `fun k => by`. Simplify using `using (congrArg (fun m => m.left) (hc k)).symm`. Establish `hcG : ∀ k, (p'.pr k).left ≫ pullback.fst G.hom (jK R) = pullback.fst G'.hom (jK R) ≫ (pG.pr k).left` using `fun k => by`.

Rewrite using `[hp' k]`. Simplify using the standard rewrite rules. Conclude with `pullback.lift_fst _ _ _`. Establish `H34 : LBIso (LB.LinComb (A.L.pull U.gen.hom.left) (fun k => (p'.pr k).left) (fun _ => 1)) (LB.LinComb (U.LG.L.pull (pullback.fst G.hom (jK R))) (fun k => (p'.pr k).left) (fun _ => 1))` using `⟨LB.linCombIso w0 _ _, linCombIso_isGen w0 hw0 _ _⟩`. Establish `HB : LBIso ((boxLB A.L pA.pr).pull e'.hom.left) ((boxLB U.LG.L pG.pr).pull (pullback.fst G'.hom (jK R)))` using `LBIso.chartPull (chartPullPullLinComb A.L (fun k => (pA.pr k).left) (fun _ => 1) e'.hom.left U.gen.hom.left (fun k => (p'.pr k).left) hcA) (chartPullPullLinComb U.LG.L (fun k => (pG.pr k).left) (fun _ => 1) (pullback.fst G'.hom (jK R)) (pullback.fst G.hom (jK R)) (fun k => (p'.pr …`.

Establish `HA : LBIso (A'.L.pull e'.hom.left) ((boxLB A.L pA.pr).pull e'.hom.left)` using `LBIso.chartPull (pullCP A'.L e'.hom.left) (pullCP _ e'.hom.left) ⟨pA.w, pA.w_gen⟩`. Conclude with `LBIso.trans (pull_isLB A'.isLB _) (pull_isLB (linComb_isLB _ A.isLB _ _) _) (pull_isLB (linComb_isLB _ U.LG.isLB _ _) _) HA HB`.
-/
theorem exists_gen_pow : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (j : ℕ) (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre D.toPre j) (pA : IsPowPolAV A' A j) (pG : IsPowGrp G' G j) (U : UnifPre I D A G), ∃ gen' : (Over.pullback (jK R)).obj G' ≅ A'.A, IsMonHom gen'.hom ∧ (∀ i, gen'.hom ≫ pA.pr i = (Over.pullback (jK R)).map (pG.pr i) ≫ U.gen.hom) ∧ ∃ w : LB.Iso (A'.L.pull gen'.hom.left) ((boxLB U.LG.L pG.pr).pull (pullback.fst G'.hom (jK R))), w.IsGen := by
  intro R _ _ I j D D' A A' G G' _ _ _ _ pD pA pG U
  have : IsMonHom U.gen.hom := U.gen_hom
  obtain ⟨p', hp'⟩ := isPowGrp_baseChange _ _ (jK R) G' G j pG
  obtain ⟨e', he', hc⟩ := exists_iso_of_isPowGrp p' pA.toIsPowGrp U.gen
  refine ⟨e', he', fun i => by rw [hc i, hp' i], ?_⟩
  obtain ⟨w0, hw0⟩ := U.ext
  have pullCP : ∀ {X Y : Scheme.{0}} (L : LB X) (F : Y ⟶ X), ChartPull (L.pull F) L F := fun L F =>
    { idx := fun J => J PUnit.unit
      le := fun J y hy => (mem_pull (L := L) (F := F) (x := y) (J := J)).1 hy
      g := fun y J J' hj hj' => (gm_pull_g L F (𝟙 _) y J J' hj hj').trans (by rw [Category.id_comp]) }
  have hcA : ∀ k, (p'.pr k).left ≫ U.gen.hom.left = e'.hom.left ≫ (pA.pr k).left := fun k => by
    simpa using (congrArg (fun m => m.left) (hc k)).symm
  have hcG : ∀ k, (p'.pr k).left ≫ pullback.fst G.hom (jK R) =
      pullback.fst G'.hom (jK R) ≫ (pG.pr k).left := fun k => by
    rw [hp' k]
    simp
    exact pullback.lift_fst _ _ _
  have H34 : LBIso (LB.LinComb (A.L.pull U.gen.hom.left) (fun k => (p'.pr k).left) (fun _ => 1))
      (LB.LinComb (U.LG.L.pull (pullback.fst G.hom (jK R))) (fun k => (p'.pr k).left) (fun _ => 1)) :=
    ⟨LB.linCombIso w0 _ _, linCombIso_isGen w0 hw0 _ _⟩
  have HB : LBIso ((boxLB A.L pA.pr).pull e'.hom.left)
      ((boxLB U.LG.L pG.pr).pull (pullback.fst G'.hom (jK R))) :=
    LBIso.chartPull
      (chartPullPullLinComb A.L (fun k => (pA.pr k).left) (fun _ => 1) e'.hom.left U.gen.hom.left
        (fun k => (p'.pr k).left) hcA)
      (chartPullPullLinComb U.LG.L (fun k => (pG.pr k).left) (fun _ => 1) (pullback.fst G'.hom (jK R))
        (pullback.fst G.hom (jK R)) (fun k => (p'.pr k).left) hcG) H34
  have HA : LBIso (A'.L.pull e'.hom.left) ((boxLB A.L pA.pr).pull e'.hom.left) :=
    LBIso.chartPull (pullCP A'.L e'.hom.left) (pullCP _ e'.hom.left) ⟨pA.w, pA.w_gen⟩
  exact LBIso.trans (pull_isLB A'.isLB _) (pull_isLB (linComb_isLB _ A.isLB _ _) _)
    (pull_isLB (linComb_isLB _ U.LG.isLB _ _) _) HA HB

end GlobalTheory
