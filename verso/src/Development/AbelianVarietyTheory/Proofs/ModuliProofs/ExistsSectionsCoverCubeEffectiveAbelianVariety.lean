import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SquareUnits
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSecValueIsUnit
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfAssociated

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.EffectiveCube

/- English proof (translation)
Establish `h' : y ∈ Out.nonzeroLocus (GlobalTheory.secPull s φ)`. Rewrite using `[GlobalTheory.nonzeroLocus_secPull]`. Conclude with `h`. Take `⟨k, hk⟩` from `TopologicalSpace.Opens.mem_iSup.1 h'`. Conclude with `⟨GlobalTheory.secPull s φ, fun J hJ => isUnit_sval _ (𝟙 Y) y hJ k hk⟩`.
-/
theorem unitAt_pull {X Y : Scheme.{0}} {N : LB X} (s : N.Sec) (φ : Y ⟶ X) (y : Y)
    (h : φ y ∈ Out.nonzeroLocus s) : UnitAt N (K := PUnit) (fun _ => φ) (fun _ => 1) y := by
  have h' : y ∈ Out.nonzeroLocus (GlobalTheory.secPull s φ) := by
    rw [GlobalTheory.nonzeroLocus_secPull]; exact h
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 h'
  exact ⟨GlobalTheory.secPull s φ, fun J hJ => isUnit_sval _ (𝟙 Y) y hJ k hk⟩

/- English proof (translation)
Take `⟨u, hu⟩` from `h`. Use `choose J hJ using fun χ : Y ⟶ X => exists_chart hN (χ y)`. Conclude with `⟨u, (mem_nonzeroLocus u y).2 ⟨_, Good.mem hJ φ (𝟙 Y), hu J hJ⟩⟩`.
-/
theorem exists_mem_of_unitAt {X Y : Scheme.{0}} {N : LB X} (hN : N.IsLB) {I : Type} [Fintype I]
    {φ : I → (Y ⟶ X)} {ε : I → ℤ} {y : Y} (h : UnitAt N φ ε y) :
    ∃ u : (LB.LinComb N φ ε).Sec, y ∈ Out.nonzeroLocus u := by
  obtain ⟨u, hu⟩ := h
  choose J hJ using fun χ : Y ⟶ X => exists_chart hN (χ y)
  exact ⟨u, (mem_nonzeroLocus u y).2 ⟨_, Good.mem hJ φ (𝟙 Y), hu J hJ⟩⟩

/- English proof (translation)
Establish `hall : (Set.univ : Set X) ⊆ ⋃ u : M.Sec, (Out.nonzeroLocus u : Set X)`. Introduce `y _`. Assume the negation of the conclusion as `hy`. Establish `ho : IsOpen (⋃ u : M.Sec, (Out.nonzeroLocus u : Set X))` using `isOpen_iUnion fun u => (Out.nonzeroLocus u).isOpen`. Take `⟨c, hc, hcl⟩` from `nonempty_inter_closedPoints (Z := (⋃ u : M.Sec, (Out.nonzeroLocus u : Set X))ᶜ) ⟨y, hy⟩ ho.isClosed_compl.isLocallyClosed`.

Take `⟨u, hu⟩` from `h c hcl`. Conclude with `hc (Set.mem_iUnion.2 ⟨u, hu⟩)`. Take `⟨T, hT⟩` from `isCompact_univ.elim_finite_subcover _ (fun u : M.Sec => (Out.nonzeroLocus u).isOpen) hall`. Use `⟨T.card, fun i => (T.equivFin.symm i).1, eq_top_iff.2 fun y _ => ?_⟩` and prove the remaining obligations. Take `⟨u, hu, hy⟩` from `Set.mem_iUnion₂.1 (hT (Set.mem_univ y))`.

Use `TopologicalSpace.Opens.mem_iSup.2 ⟨T.equivFin ⟨u, hu⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [Equiv.symm_apply_apply]`. Conclude with `hy`.
-/
theorem exists_fin_cover {X : Scheme.{0}} [CompactSpace X] [JacobsonSpace X] (M : LB X)
    (h : ∀ y : X, IsClosed {y} → ∃ u : M.Sec, y ∈ Out.nonzeroLocus u) :
    ∃ (r : ℕ) (u : Fin r → M.Sec), ⨆ i, Out.nonzeroLocus (u i) = ⊤ := by
  have hall : (Set.univ : Set X) ⊆ ⋃ u : M.Sec, (Out.nonzeroLocus u : Set X) := by
    intro y _
    by_contra hy
    have ho : IsOpen (⋃ u : M.Sec, (Out.nonzeroLocus u : Set X)) :=
      isOpen_iUnion fun u => (Out.nonzeroLocus u).isOpen
    obtain ⟨c, hc, hcl⟩ := nonempty_inter_closedPoints
      (Z := (⋃ u : M.Sec, (Out.nonzeroLocus u : Set X))ᶜ) ⟨y, hy⟩ ho.isClosed_compl.isLocallyClosed
    obtain ⟨u, hu⟩ := h c hcl
    exact hc (Set.mem_iUnion.2 ⟨u, hu⟩)
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover _ (fun u : M.Sec => (Out.nonzeroLocus u).isOpen) hall
  refine ⟨T.card, fun i => (T.equivFin.symm i).1, eq_top_iff.2 fun y _ => ?_⟩
  obtain ⟨u, hu, hy⟩ := Set.mem_iUnion₂.1 (hT (Set.mem_univ y))
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨T.equivFin ⟨u, hu⟩, ?_⟩
  simp only [Equiv.symm_apply_apply]
  exact hy

/- English proof (translation)
Introduce `hcube K _ _ P N s hN ⟨j, hj⟩`. Take `⟨t, ht⟩` from `hcube _ P N hN`. Use `P.isAb.smooth` as an intermediate fact. Use `P.isAb.proper` as an intermediate fact. Use `P.isAb.geomConnected` as an intermediate fact.

Use `geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres P.A.hom` as an intermediate fact. Establish `: IsIntegral P.A.left` using `GeometricallyIntegral.isIntegral_of_subsingleton P.A.hom`. Set `T : Over (Sp K)` to `Over.mk (𝟙 (Sp K))`. Establish `: IsIntegral (T ⊗ P.A).left` using `GeometricallyIntegral.geometrically_isIntegral (𝟙 (Sp K)) _ _ (IsPullback.of_hasPullback (𝟙 (Sp K)) P.A.hom).flip`. Establish `: JacobsonSpace P.A.left` using `LocallyOfFiniteType.jacobsonSpace P.A.hom`.

Establish `: CompactSpace P.A.left` using `QuasiCompact.compactSpace_of_compactSpace P.A.hom`. Set `π : P.A ⟶ T` to `Over.homMk P.A.hom (Category.comp_id _)`. Establish `hD : (((snd T P.A).left ⁻¹ᵁ Out.nonzeroLocus s : (T ⊗ P.A).left.Opens) : Set (T ⊗ P.A).left).Nonempty`. Choose the witnesses or unpack the hypotheses as in `⟨d, hd⟩ : ((P.A.left.basicOpen (s.f j) : P.A.left.Opens) : Set P.A.left).Nonempty := by`. Rewrite using `[Set.nonempty_iff_ne_empty]`.

Introduce `h`. Conclude with `hj ((basicOpen_eq_bot_iff _).1 (SetLike.coe_injective h))`. Use `⟨(lift π (𝟙 _)).left d, ?_⟩` and prove the remaining obligations. Use `show (snd T P.A).left ((lift π (𝟙 _)).left d) ∈ Out.nonzeroLocus s`. Rewrite using `[← Scheme.Hom.comp_apply, ← Over.comp_left, lift_snd]`.

Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨j, hd⟩`. Use `exists_fin_cover _ fun y hy => ?_` and prove the remaining obligations. Set `x : T ⟶ P.A` to `Over.homMk (pointOfClosedPoint P.A.hom y hy) (pointOfClosedPoint_comp P.A.hom y hy)`. Set `p : T.left` to `IsLocalRing.closedPoint K`. Establish `hx : x.left p = y` using `pointOfClosedPoint_apply P.A.hom y hy p`.

Establish `hxπ : x ≫ π = 𝟙 T` using `Over.OverMorphism.ext (pointOfClosedPoint_comp P.A.hom y hy)`. Establish `good : ∀ a : T ⟶ P.A, (Out.ptSecT P.A (a * x)).left p ∈ (snd T P.A).left ⁻¹ᵁ Out.nonzeroLocus s → UnitAt N (K` using `PUnit) (fun _ => ((π ≫ a) * 𝟙 P.A).left) (fun _ => 1) y := fun a ha => by`. Use `unitAt_pull s _ y ?_` and prove the remaining obligations. Establish `e : x ≫ ((π ≫ a) * 𝟙 P.A) = Out.ptSecT P.A (a * x) ≫ snd T P.A`. Simplify using `[Out.ptSecT, MonObj.comp_mul, reassoc_of% hxπ]`.

Rewrite using `[← hx, ← Scheme.Hom.comp_apply, ← Over.comp_left, e]`. Conclude with `ha`. Take `⟨a, ha, -⟩` from `NoBasePoint.exists_two_points (𝟙 (Sp K)) _ hD x x`. Take `⟨b, hb, hc⟩` from `NoBasePoint.exists_two_points (𝟙 (Sp K)) _ hD x (a⁻¹ * x)`. Rewrite `hc` using `[← _root_.mul_assoc]`.

Use `choose i hi using fun k : Fin 4 => exists_chart hN ((![a, b, b⁻¹ * a⁻¹, 1] k).left p)`. Take `⟨w, hw⟩` from `SepPoints.exists_gen_three hN t ht (π ≫ a) (π ≫ b) (π ≫ (b⁻¹ * a⁻¹)) (𝟙 P.A) 1 (by rw [pow_one, ← MonObj.comp_mul, ← MonObj.comp_mul]; simp) i (fun k z => by`. Establish `e : (![(π ≫ a).left, (π ≫ b).left, (π ≫ (b⁻¹ * a⁻¹)).left, (1 : P.A ⟶ P.A).left] k) = π.left ≫ (![a, b, b⁻¹ * a⁻¹, 1] k).left` using `by fin_cases k`. Both sides reduce to the same expression. Both sides reduce to the same expression.

Both sides reduce to the same expression. Conclude with `congrArg (fun q : P.A ⟶ P.A => q.left) (MonObj.comp_one π).symm`. Rewrite using `[e, Scheme.Hom.comp_apply, spec_pt_eq (k := K) (π.left z) p]`. Conclude with `hi k)`. Establish `hw' : UnitAt N _ _ y` using `⟨genSec w hw, fun J hJ => by`.

Rewrite using `[sval_genSec w hw _ y hJ]`. Conclude with `Units.isUnit _⟩`. Use `exists_mem_of_unitAt hN (UnitAt.congr hN (formEq_of_add fun U _ hh => ?_) (((hw'.mul (good a (ha p))).mul (good b (hb p))).mul (good _ (hc p))))` and prove the remaining obligations. Simplify using `[Fin.sum_univ_succ]`. Use `module`.
-/
theorem exists_sections_cube_cover :
    (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N : LB P.A.left) (s : N.Sec), N.IsLB → (∃ j, s.f j ≠ 0) → ∃ (r : ℕ) (u : Fin r → (lbPow N 3).Sec), ⨆ i, Out.nonzeroLocus (u i) = ⊤ := by
  intro hcube K _ _ P N s hN ⟨j, hj⟩
  obtain ⟨t, ht⟩ := hcube _ P N hN
  have := P.isAb.smooth
  have := P.isAb.proper
  have := P.isAb.geomConnected
  have := geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres P.A.hom
  have : IsIntegral P.A.left := GeometricallyIntegral.isIntegral_of_subsingleton P.A.hom
  let T : Over (Sp K) := Over.mk (𝟙 (Sp K))
  have : IsIntegral (T ⊗ P.A).left :=
    GeometricallyIntegral.geometrically_isIntegral (𝟙 (Sp K)) _ _ (IsPullback.of_hasPullback (𝟙 (Sp K)) P.A.hom).flip
  have : JacobsonSpace P.A.left := LocallyOfFiniteType.jacobsonSpace P.A.hom
  have : CompactSpace P.A.left := QuasiCompact.compactSpace_of_compactSpace P.A.hom
  let π : P.A ⟶ T := Over.homMk P.A.hom (Category.comp_id _)
  have hD : (((snd T P.A).left ⁻¹ᵁ Out.nonzeroLocus s : (T ⊗ P.A).left.Opens) : Set (T ⊗ P.A).left).Nonempty := by
    obtain ⟨d, hd⟩ : ((P.A.left.basicOpen (s.f j) : P.A.left.Opens) : Set P.A.left).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro h
      exact hj ((basicOpen_eq_bot_iff _).1 (SetLike.coe_injective h))
    refine ⟨(lift π (𝟙 _)).left d, ?_⟩
    show (snd T P.A).left ((lift π (𝟙 _)).left d) ∈ Out.nonzeroLocus s
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, lift_snd]
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, hd⟩
  refine exists_fin_cover _ fun y hy => ?_
  let x : T ⟶ P.A := Over.homMk (pointOfClosedPoint P.A.hom y hy) (pointOfClosedPoint_comp P.A.hom y hy)
  let p : T.left := IsLocalRing.closedPoint K
  have hx : x.left p = y := pointOfClosedPoint_apply P.A.hom y hy p
  have hxπ : x ≫ π = 𝟙 T := Over.OverMorphism.ext (pointOfClosedPoint_comp P.A.hom y hy)
  have good : ∀ a : T ⟶ P.A, (Out.ptSecT P.A (a * x)).left p ∈ (snd T P.A).left ⁻¹ᵁ Out.nonzeroLocus s →
      UnitAt N (K := PUnit) (fun _ => ((π ≫ a) * 𝟙 P.A).left) (fun _ => 1) y := fun a ha => by
    refine unitAt_pull s _ y ?_
    have e : x ≫ ((π ≫ a) * 𝟙 P.A) = Out.ptSecT P.A (a * x) ≫ snd T P.A := by
      simp [Out.ptSecT, MonObj.comp_mul, reassoc_of% hxπ]
    rw [← hx, ← Scheme.Hom.comp_apply, ← Over.comp_left, e]
    exact ha
  obtain ⟨a, ha, -⟩ := NoBasePoint.exists_two_points (𝟙 (Sp K)) _ hD x x
  obtain ⟨b, hb, hc⟩ := NoBasePoint.exists_two_points (𝟙 (Sp K)) _ hD x (a⁻¹ * x)
  rw [← _root_.mul_assoc] at hc
  choose i hi using fun k : Fin 4 => exists_chart hN ((![a, b, b⁻¹ * a⁻¹, 1] k).left p)
  obtain ⟨w, hw⟩ := SepPoints.exists_gen_three hN t ht (π ≫ a) (π ≫ b) (π ≫ (b⁻¹ * a⁻¹)) (𝟙 P.A) 1
    (by rw [pow_one, ← MonObj.comp_mul, ← MonObj.comp_mul]; simp) i (fun k z => by
      have e : (![(π ≫ a).left, (π ≫ b).left, (π ≫ (b⁻¹ * a⁻¹)).left, (1 : P.A ⟶ P.A).left] k) =
          π.left ≫ (![a, b, b⁻¹ * a⁻¹, 1] k).left := by
        fin_cases k
        · rfl
        · rfl
        · rfl
        · exact congrArg (fun q : P.A ⟶ P.A => q.left) (MonObj.comp_one π).symm
      rw [e, Scheme.Hom.comp_apply, spec_pt_eq (k := K) (π.left z) p]
      exact hi k)
  have hw' : UnitAt N _ _ y := ⟨genSec w hw, fun J hJ => by
    rw [sval_genSec w hw _ y hJ]; exact Units.isUnit _⟩
  refine exists_mem_of_unitAt hN (UnitAt.congr hN (formEq_of_add fun U _ hh => ?_)
    (((hw'.mul (good a (ha p))).mul (good b (hb p))).mul (good _ (hc p))))
  simp [Fin.sum_univ_succ]
  module

end GlobalTheory.EffectiveCube
