import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledBackGramMatricesIndependentOfFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellPointsExistsUniqueUnitriangularStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenFlagBundleCellAndCoordsRegularStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCell2

/- English proof (translation)
Use extensionality with `a`. Take `⟨x, rfl⟩` from `ε.symm.surjective a`. Apply the tactic sequence `rcases x with b | j <;> simp [pt, bsL_apply, fb]`.
-/
theorem pt_bsL_fb {n d : ℕ} {J : Type} (ε : Fin n ≃ Fin d ⊕ J) (w : V n) : pt ε (bsL ε w) (fb ε w) = w := by
  ext a
  obtain ⟨x, rfl⟩ := ε.symm.surjective a
  rcases x with b | j <;> simp [pt, bsL_apply, fb]

/- English proof (translation)
Introduce `F _ σ X Y ι _ m E E' φ f hf hR c A u hgen n ε`. Establish `hO` using `GlobalTheory.T.isOpen_flagBundleCell_and_coords_regular F X Y ι m E E' φ f hR A u`. Establish `hP` using `GlobalTheory.T.flag_cell_points_existsUnique_unitriangular F X Y ι m E E' φ f hR A u hgen`. Establish `hval : ∀ y : CxPts Y.str σ, InCell E E' φ f A u (under y) → ∀ j, ratVal (u j) y = (ratOf Y).val y.1 (u j)` using `fun y hy j => ratVal_eq_val_ratOf y (mem_O_ratOf.2 (hO.2 _ hy j))`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Set `W : Y.X.Opens` to `⟨{y | InCell E E' φ f A u y}, hO.1⟩`. Establish `e : cellSet E E' φ f hf c A u = ptsIn Y.str σ W ∩ ptMap σ f hf ⁻¹' c.e.source`. Use extensionality with `y`. Simplify using `only [cellSet, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, mem_ptsIn]`. Both sides reduce to the same expression.

Rewrite using `[e]`. Conclude with `(isOpen_ptsIn W).inter (c.e.open_source.preimage (Points.PtsOver.continuous_map f hf _))`. Introduce `y hy y' hy' h`. Establish `h1` using `congrArg (bsL ε) h`. Establish `h2` using `congrArg (fb ε) h`.

Simplify using `only [cellMap, bsL_pt, fb_pt] at h1 h2`. Establish `hx : ptMap σ f hf y = ptMap σ f hf y'` using `c.e.injOn hy.2 hy'.2 h1`. Establish `hA : A ∈ E.S ((ptMap σ f hf y).1 (IsLocalRing.closedPoint ℂ))` using `hy.1.1`. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `(hP ℂ (ptMap σ f hf y).1 hA (fun j => ratVal (u j) y)).unique ⟨rfl, hy.1, fun j => (hval y hy.1 j).symm⟩ ⟨congrArg Subtype.val hx.symm, hy'.1, fun j => (hval y' hy'.1 j).symm.trans (congrFun h2 j).symm⟩`.

Introduce `S hS hA`. Use extensionality with `w`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, ⟨hyS, -⟩, rfl⟩`. Conclude with `⟨ptMap σ f hf y, hyS, by simp only [cellMap, bsL_pt]⟩`.

Introduce and unpack `⟨x, hxS, hxw⟩`. Take `⟨p, ⟨hpf, hpc, hpv⟩, -⟩` from `hP ℂ x.1 (hA x hxS) (fb ε w)`. Establish `hps : p ≫ Y.str = spMap σ` using `by rw [← hf, ← Category.assoc, hpf, x.2]`. Set `y : CxPts Y.str σ` to `⟨p, hps⟩`. Establish `hyx : ptMap σ f hf y = x` using `Subtype.ext hpf`.

Use `⟨y, ⟨by rw [Set.mem_preimage, hyx]; exact hxS, hpc, by rw [hyx]; exact hS hxS⟩, ?_⟩` and prove the remaining obligations. Establish `hv : (fun j => ratVal (u j) y) = fb ε w` using `funext fun j => (hval y hpc j).trans (hpv j)`. Simplify using `only [cellMap, hyx, hxw, hv]`. Conclude with `pt_bsL_fb ε w`.
-/
theorem cellMap_image_eq : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ (c : AlgChart X.str σ X.dim) (A : Mat m X.Fn) (u : Cell m → Y.Fn), InCell E E' φ f A u (genericPoint Y.X) → ∀ (n : ℕ) (ε : Fin n ≃ Fin X.dim ⊕ Cell m), IsOpen (cellSet E E' φ f hf c A u) ∧ Set.InjOn (cellMap ε f hf c u) (cellSet E E' φ f hf c A u) ∧ ∀ T : Set (CxPts X.str σ), T ⊆ c.e.source → (∀ x ∈ T, A ∈ E.S (under x)) → cellMap ε f hf c u '' (ptMap σ f hf ⁻¹' T ∩ cellSet E E' φ f hf c A u) = bsL ε ⁻¹' (c.e '' T) := by
  intro F _ σ X Y ι _ m E E' φ f hf hR c A u hgen n ε
  have hO := GlobalTheory.T.isOpen_flagBundleCell_and_coords_regular F X Y ι m E E' φ f hR A u
  have hP := GlobalTheory.T.flag_cell_points_existsUnique_unitriangular F X Y ι m E E' φ f hR A u hgen
  have hval : ∀ y : CxPts Y.str σ, InCell E E' φ f A u (under y) → ∀ j,
      ratVal (u j) y = (ratOf Y).val y.1 (u j) :=
    fun y hy j => ratVal_eq_val_ratOf y (mem_O_ratOf.2 (hO.2 _ hy j))
  refine ⟨?_, ?_, ?_⟩
  · let W : Y.X.Opens := ⟨{y | InCell E E' φ f A u y}, hO.1⟩
    have e : cellSet E E' φ f hf c A u = ptsIn Y.str σ W ∩ ptMap σ f hf ⁻¹' c.e.source := by
      ext y
      simp only [cellSet, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, mem_ptsIn]
      rfl
    rw [e]
    exact (isOpen_ptsIn W).inter (c.e.open_source.preimage (Points.PtsOver.continuous_map f hf _))
  · intro y hy y' hy' h
    have h1 := congrArg (bsL ε) h
    have h2 := congrArg (fb ε) h
    simp only [cellMap, bsL_pt, fb_pt] at h1 h2
    have hx : ptMap σ f hf y = ptMap σ f hf y' := c.e.injOn hy.2 hy'.2 h1
    have hA : A ∈ E.S ((ptMap σ f hf y).1 (IsLocalRing.closedPoint ℂ)) := hy.1.1
    apply Subtype.ext
    exact (hP ℂ (ptMap σ f hf y).1 hA (fun j => ratVal (u j) y)).unique
      ⟨rfl, hy.1, fun j => (hval y hy.1 j).symm⟩
      ⟨congrArg Subtype.val hx.symm, hy'.1, fun j => (hval y' hy'.1 j).symm.trans (congrFun h2 j).symm⟩
  · intro S hS hA
    ext w
    constructor
    · rintro ⟨y, ⟨hyS, -⟩, rfl⟩
      exact ⟨ptMap σ f hf y, hyS, by simp only [cellMap, bsL_pt]⟩
    · rintro ⟨x, hxS, hxw⟩
      obtain ⟨p, ⟨hpf, hpc, hpv⟩, -⟩ := hP ℂ x.1 (hA x hxS) (fb ε w)
      have hps : p ≫ Y.str = spMap σ := by rw [← hf, ← Category.assoc, hpf, x.2]
      let y : CxPts Y.str σ := ⟨p, hps⟩
      have hyx : ptMap σ f hf y = x := Subtype.ext hpf
      refine ⟨y, ⟨by rw [Set.mem_preimage, hyx]; exact hxS, hpc, by rw [hyx]; exact hS hxS⟩, ?_⟩
      have hv : (fun j => ratVal (u j) y) = fb ε w := funext fun j => (hval y hpc j).trans (hpv j)
      simp only [cellMap, hyx, hxw, hv]
      exact pt_bsL_fb ε w

end GlobalTheory.FlagCell2
