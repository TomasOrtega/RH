import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FlatDescentOfUnitsStatement
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.FnDesc

/- English proof (translation)
Introduce `P Q f hfl hlf hsu D hD t ht hinv`. Establish `hle : ∀ i : D.ι, f ⁻¹ᵁ D.U i ≤ (D.pull f).U (fun _ => i)` using `fun i x hx => mem_pull.2 hx`. Establish `hex : ∀ i : D.ι, ∃ s : Γ(Q, D.U i)ˣ, pullU f (D.U i) s = res (hle i) (t.s fun _ => i)`. Introduce `i`. Use `(GlobalTheory.T.flat_descent_of_units f hfl hlf hsu (D.U i)).2 _ ?_` and prove the remaining obligations.

Introduce `W b c hbc w hw`. Establish `hw' : f (c w) ∈ D.U i`. Establish `: f (b w) = f (c w)`. Use `congrArg (fun q : W ⟶ Q => q w) hbc` as an intermediate fact. Simplify using `using this`.

Conclude with `this ▸ hw`. Rewrite using `[gm_res b w (hle i) hw, gm_res c w (hle i) hw']`. Conclude with `hinv W b c hbc w i hw`. Use `choose s hs using hex`. Establish `key : ∀ (i : D.ι) (x : P) (hx : f x ∈ D.U i), gm (𝟙 P ≫ f) x (D.U i) (s i) = gm (𝟙 P) x ((D.pull f).U fun _ => i) (t.s fun _ => i)`.

Introduce `i x hx`. Rewrite using `[← gm_pull (𝟙 P) f x (D.U i) hx, hs i]`. Conclude with `gm_res (𝟙 P) x (hle i) hx _`. Use `⟨⟨s⟩, fun i j => ?_⟩` and prove the remaining obligations. Apply `(GlobalTheory.T.flat_descent_of_units f hfl hlf hsu (D.U i ⊓ D.U j)).1` to reduce the goal to its premises.

Apply `unit_ext` to reduce the goal to its premises. Introduce `x hx`. Establish `hi : f x ∈ D.U i` using `hx.1`. Establish `hj : f x ∈ D.U j` using `hx.2`. Establish `hij : f x ∈ D.U i ⊓ D.U j` using `hx`.

Establish `hm : x ∈ (D.pull f).U (fun _ => i) ⊓ (D.pull f).U (fun _ => j)` using `⟨mem_pull.2 hi, mem_pull.2 hj⟩`. Establish `e` using `congrArg (gm (𝟙 P) x _) (ht (fun _ => i) (fun _ => j))`. Rewrite `e` using `[map_mul, gm_res (𝟙 P) x _ hm, gm_res (𝟙 P) x _ hm]`. Establish `eg : gm (𝟙 P) x ((D.pull f).U (fun _ => i) ⊓ (D.pull f).U (fun _ => j)) ((D.pull f).g (fun _ => i) (fun _ => j)) = gm (𝟙 P ≫ f) x _ (D.g i j)` using `by show gm (𝟙 P) x _ (∏ _k : PUnit, (res _ (pullU f _ (D.g i j))) ^ (1 : ℤ)) = _`. Rewrite using `[Fintype.prod_unique, zpow_one]`.

Conclude with `(gm_res (𝟙 P) x _ hm _).trans (gm_pull (𝟙 P) f x (D.U i ⊓ D.U j) hij _)`. Rewrite `e` using `[eg, ← key i x hi, ← key j x hj]`. Rewrite using `[gm_pull (𝟙 P) f x _ hij, gm_pull (𝟙 P) f x _ hij, map_mul, gm_res (𝟙 P ≫ f) x _ hij, gm_res (𝟙 P ≫ f) x _ hij]`. Conclude with `e`.
-/
theorem triv_of_invariant_gen : ∀ {P Q : Scheme.{0}} (f : P ⟶ Q), Flat f → LocallyOfFinitePresentation f → Surjective f →
    ∀ (D : LB Q), D.IsLB → ∀ (t : LB.Gen (D.pull f)), t.IsGen →
      (∀ (W : Scheme.{0}) (a b : W ⟶ P), a ≫ f = b ≫ f → ∀ (w : W) (i : D.ι), f (a w) ∈ D.U i →
        gm a w ((D.pull f).U fun _ => i) (t.s fun _ => i) = gm b w ((D.pull f).U fun _ => i) (t.s fun _ => i)) →
      Triv D := by
  intro P Q f hfl hlf hsu D hD t ht hinv
  have hle : ∀ i : D.ι, f ⁻¹ᵁ D.U i ≤ (D.pull f).U (fun _ => i) := fun i x hx => mem_pull.2 hx
  have hex : ∀ i : D.ι, ∃ s : Γ(Q, D.U i)ˣ, pullU f (D.U i) s = res (hle i) (t.s fun _ => i) := by
    intro i
    refine (GlobalTheory.T.flat_descent_of_units f hfl hlf hsu (D.U i)).2 _ ?_
    intro W b c hbc w hw
    have hw' : f (c w) ∈ D.U i := by
      have : f (b w) = f (c w) := by
        have := congrArg (fun q : W ⟶ Q => q w) hbc
        simpa using this
      exact this ▸ hw
    rw [gm_res b w (hle i) hw, gm_res c w (hle i) hw']
    exact hinv W b c hbc w i hw
  choose s hs using hex
  have key : ∀ (i : D.ι) (x : P) (hx : f x ∈ D.U i),
      gm (𝟙 P ≫ f) x (D.U i) (s i) = gm (𝟙 P) x ((D.pull f).U fun _ => i) (t.s fun _ => i) := by
    intro i x hx
    rw [← gm_pull (𝟙 P) f x (D.U i) hx, hs i]
    exact gm_res (𝟙 P) x (hle i) hx _
  refine ⟨⟨s⟩, fun i j => ?_⟩
  apply (GlobalTheory.T.flat_descent_of_units f hfl hlf hsu (D.U i ⊓ D.U j)).1
  apply unit_ext
  intro x hx
  have hi : f x ∈ D.U i := hx.1
  have hj : f x ∈ D.U j := hx.2
  have hij : f x ∈ D.U i ⊓ D.U j := hx
  have hm : x ∈ (D.pull f).U (fun _ => i) ⊓ (D.pull f).U (fun _ => j) := ⟨mem_pull.2 hi, mem_pull.2 hj⟩
  have e := congrArg (gm (𝟙 P) x _) (ht (fun _ => i) (fun _ => j))
  rw [map_mul, gm_res (𝟙 P) x _ hm, gm_res (𝟙 P) x _ hm] at e
  have eg : gm (𝟙 P) x ((D.pull f).U (fun _ => i) ⊓ (D.pull f).U (fun _ => j)) ((D.pull f).g (fun _ => i) (fun _ => j)) =
      gm (𝟙 P ≫ f) x _ (D.g i j) := by
    show gm (𝟙 P) x _ (∏ _k : PUnit, (res _ (pullU f _ (D.g i j))) ^ (1 : ℤ)) = _
    rw [Fintype.prod_unique, zpow_one]
    exact (gm_res (𝟙 P) x _ hm _).trans (gm_pull (𝟙 P) f x (D.U i ⊓ D.U j) hij _)
  rw [eg, ← key i x hi, ← key j x hj] at e
  rw [gm_pull (𝟙 P) f x _ hij, gm_pull (𝟙 P) f x _ hij, map_mul,
    gm_res (𝟙 P ≫ f) x _ hij, gm_res (𝟙 P ≫ f) x _ hij]
  exact e

end GlobalTheory.CompanionTheory.FnDesc
