import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsDegenerationDataExtensionOverDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationOfFiniteExtTrans
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LiftThreeOverMapComp

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
namespace GlobalTheory.Mum.RigScale

/- English proof (translation)
Simplify using `only [LB.pull, LB.LinComb, LB.wchart]`. Simplify using `using hi`.
-/
private theorem mem_pull_lemma {X X' Y : Scheme.{0}} {L : LB X} {F : X' ⟶ X} (f : Y ⟶ X') (y : Y) (i : L.ι)
    (hi : F (f y) ∈ L.U i) : f y ∈ (L.pull F).U (fun _ => i) := by
  simp only [LB.pull, LB.LinComb, LB.wchart]
  simpa using hi

/- English proof (translation)
Simplify using `only [LB.pull, LB.LinComb, LB.wchart] at hi`. Simplify using `using hi`.
-/
private theorem mem_U_of_mem_pull_U {X X' Y : Scheme.{0}} {L : LB X} {F : X' ⟶ X} (f : Y ⟶ X') (y : Y) (i : L.ι)
    (hi : f y ∈ (L.pull F).U (fun _ => i)) : F (f y) ∈ L.U i := by
  simp only [LB.pull, LB.LinComb, LB.wchart] at hi
  simpa using hi

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Introduce `Y f y j j' k k' h1 h2 h3 h4`. Establish `m1` using `mem_pull_lemma f y j h1`. Establish `m2` using `mem_pull_lemma f y j' h2`. Establish `hy : f y ∈ ((L.pull F).div L').U (fun _ => j, k) ⊓ ((L.pull F).div L').U (fun _ => j', k')` using `⟨⟨m1, h3⟩, ⟨m2, h4⟩⟩`. Establish `e` using `congrArg (gm f y _) (hw (fun _ => j, k) (fun _ => j', k'))`.

Rewrite `e` using `[map_mul, gm_res _ _ _ hy, gm_res _ _ _ hy]`. Unfold `gw`. Use `e.trans ?_` and prove the remaining obligations. Use `congr 1`. Use `(map_mul (gm f y _) _ _).trans ?_` and prove the remaining obligations.

Use `congr 1`. Use `(gm_res f y _ hy _).trans ?_` and prove the remaining obligations. Simplify using `only [LB.pull, LB.LinComb, Finset.univ_unique, Finset.prod_singleton, zpow_one]`. Use `(gm_res f y _ (show f y ∈ (L.pull F).U (fun _ => j) ⊓ (L.pull F).U (fun _ => j') from ⟨m1, m2⟩) _).trans ?_` and prove the remaining obligations. Conclude with `gm_pull f F y (L.U j ⊓ L.U j') ⟨h1, h2⟩ _`.

Use `(map_inv (gm f y _) _).trans ?_` and prove the remaining obligations. Use `congr 1`. Conclude with `gm_res f y _ hy _`.
-/
private theorem pgen_of_isGen {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}
    (w : LB.Iso L' (L.pull F)) (hw : LB.Gen.IsGen w) : PGen w := by
  intro Y f y j j' k k' h1 h2 h3 h4
  have m1 := mem_pull_lemma f y j h1
  have m2 := mem_pull_lemma f y j' h2
  have hy : f y ∈ ((L.pull F).div L').U (fun _ => j, k) ⊓ ((L.pull F).div L').U (fun _ => j', k') :=
    ⟨⟨m1, h3⟩, ⟨m2, h4⟩⟩
  have e := congrArg (gm f y _) (hw (fun _ => j, k) (fun _ => j', k'))
  rw [map_mul, gm_res _ _ _ hy, gm_res _ _ _ hy] at e
  unfold gw
  refine e.trans ?_
  congr 1
  refine (map_mul (gm f y _) _ _).trans ?_
  congr 1
  · refine (gm_res f y _ hy _).trans ?_
    simp only [LB.pull, LB.LinComb, Finset.univ_unique, Finset.prod_singleton, zpow_one]
    refine (gm_res f y _ (show f y ∈ (L.pull F).U (fun _ => j) ⊓ (L.pull F).U (fun _ => j') from ⟨m1, m2⟩) _).trans ?_
    exact gm_pull f F y (L.U j ⊓ L.U j') ⟨h1, h2⟩ _
  · refine (map_inv (gm f y _) _).trans ?_
    congr 1
    exact gm_res f y _ hy _

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Introduce and unpack `⟨a, k⟩ ⟨a', k'⟩`. Apply `unit_ext` to reduce the goal to its premises. Introduce `x hx`. Establish `m1 : (𝟙 X') x ∈ (L.pull F).U (fun _ => a PUnit.unit)` using `hx.1.1`. Establish `m2 : (𝟙 X') x ∈ (L.pull F).U (fun _ => a' PUnit.unit)` using `hx.2.1`.

Establish `n1` using `mem_U_of_mem_pull_U (𝟙 X') x (a PUnit.unit) m1`. Establish `n2` using `mem_U_of_mem_pull_U (𝟙 X') x (a' PUnit.unit) m2`. Establish `h` using `hw X' (𝟙 X') x (a PUnit.unit) (a' PUnit.unit) k k' n1 n2 hx.1.2 hx.2.2`. Unfold `gw at h`. Rewrite using `[map_mul, gm_res, gm_res]`.

Use `h.trans ?_` and prove the remaining obligations. Use `symm`. Use `congr 1`. Use `(map_mul (gm (𝟙 X') x _) _ _).trans ?_` and prove the remaining obligations. Use `congr 1`.

Use `(gm_res (𝟙 X') x _ hx _).trans ?_` and prove the remaining obligations. Simplify using `only [LB.pull, LB.LinComb, Finset.univ_unique, Finset.prod_singleton, zpow_one]`. Use `(gm_res (𝟙 X') x _ (show (𝟙 X') x ∈ (L.pull F).U (fun _ => a PUnit.unit) ⊓ (L.pull F).U (fun _ => a' PUnit.unit) from ⟨m1, m2⟩) _).trans ?_` and prove the remaining obligations. Conclude with `gm_pull (𝟙 X') F x (L.U (a PUnit.unit) ⊓ L.U (a' PUnit.unit)) ⟨n1, n2⟩ _`. Use `(map_inv (gm (𝟙 X') x _) _).trans ?_` and prove the remaining obligations.

Use `congr 1`. Conclude with `gm_res (𝟙 X') x _ hx _`. Apply the tactic sequence `all_goals first | exact hx | skip`.
-/
private theorem isGen_of_pgen {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}
    (w : LB.Iso L' (L.pull F)) (hw : PGen w) : LB.Gen.IsGen w := by
  rintro ⟨a, k⟩ ⟨a', k'⟩
  apply unit_ext
  intro x hx
  have m1 : (𝟙 X') x ∈ (L.pull F).U (fun _ => a PUnit.unit) := hx.1.1
  have m2 : (𝟙 X') x ∈ (L.pull F).U (fun _ => a' PUnit.unit) := hx.2.1
  have n1 := mem_U_of_mem_pull_U (𝟙 X') x (a PUnit.unit) m1
  have n2 := mem_U_of_mem_pull_U (𝟙 X') x (a' PUnit.unit) m2
  have h := hw X' (𝟙 X') x (a PUnit.unit) (a' PUnit.unit) k k' n1 n2 hx.1.2 hx.2.2
  unfold gw at h
  rw [map_mul, gm_res, gm_res]
  · refine h.trans ?_
    symm
    congr 1
    refine (map_mul (gm (𝟙 X') x _) _ _).trans ?_
    congr 1
    · refine (gm_res (𝟙 X') x _ hx _).trans ?_
      simp only [LB.pull, LB.LinComb, Finset.univ_unique, Finset.prod_singleton, zpow_one]
      refine (gm_res (𝟙 X') x _ (show (𝟙 X') x ∈ (L.pull F).U (fun _ => a PUnit.unit) ⊓ (L.pull F).U (fun _ => a' PUnit.unit) from ⟨m1, m2⟩) _).trans ?_
      exact gm_pull (𝟙 X') F x (L.U (a PUnit.unit) ⊓ L.U (a' PUnit.unit)) ⟨n1, n2⟩ _
    · refine (map_inv (gm (𝟙 X') x _) _).trans ?_
      congr 1
      exact gm_res (𝟙 X') x _ hx _
  all_goals first | exact hx | skip

/- English proof (translation)
Introduce `R R' _ _ _ _ ρ D₂ D₃ Φ hΦ w₀ hw₀`. Establish `hσ : eSec D₃.P.A ≫ D₃.P.A.hom = 𝟙 _` using `Over.w (η[D₃.P.A])`. Take `⟨w, hw, hm⟩` from `GlobalTheory.UnifPreCompare.exists_rigidified (F := Φ) D₂.P.isLB D₃.P.isLB D₃.P.A.hom (eSec D₃.P.A) hσ w₀ (isGen_of_pgen w₀ hw₀) D₃.rig D₃.rig_gen D₂.rig D₂.rig_gen (spMap ρ) (GlobalTheory.PolBaseChange.eSec_comm hΦ)`. Conclude with `⟨w, pgen_of_isGen w hw, hm⟩`.
-/
theorem exists_rig_rescale : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R') (D₂ : DegPre R) (D₃ : DegPre R') (Φ : D₃.P.A.left ⟶ D₂.P.A.left), IsGrpPullback D₃.P.A D₂.P.A (spMap ρ) Φ → ∀ w₀ : LB.Iso D₃.P.L (D₂.P.L.pull Φ), PGen w₀ → ∃ w : LB.Iso D₃.P.L (D₂.P.L.pull Φ), PGen w ∧ PMaps w (K := PUnit) (fun _ => eSec D₃.P.A) (fun _ => eSec D₂.P.A) (fun _ => 1) D₃.rig D₂.rig (spMap ρ) := by
  intro R R' _ _ _ _ ρ D₂ D₃ Φ hΦ w₀ hw₀
  have hσ : eSec D₃.P.A ≫ D₃.P.A.hom = 𝟙 _ := Over.w (η[D₃.P.A])
  obtain ⟨w, hw, hm⟩ := GlobalTheory.UnifPreCompare.exists_rigidified (F := Φ) D₂.P.isLB D₃.P.isLB D₃.P.A.hom
    (eSec D₃.P.A) hσ w₀ (isGen_of_pgen w₀ hw₀) D₃.rig D₃.rig_gen D₂.rig D₂.rig_gen (spMap ρ)
    (GlobalTheory.PolBaseChange.eSec_comm hΦ)
  exact ⟨w, pgen_of_isGen w hw, hm⟩

end GlobalTheory.Mum.RigScale
