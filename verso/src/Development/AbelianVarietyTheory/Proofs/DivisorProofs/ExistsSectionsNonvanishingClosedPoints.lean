import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedBasePt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumLifts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootHeightLeAbelianHeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetric
import Development.AbelianVarietyTheory.Definitions.Divisors.DualRef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointHeightDualAndLinearCombStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightBoundedBelowOffZeroLocusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleSectionsAvoidClosedPoints
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts GlobalTheory.ShFam.Pad
open CategoryTheory AlgebraicGeometry GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.Cartier
open scoped Classical
set_option autoImplicit false

namespace GlobalTheory.RatSecClear

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.CechPic

/- English proof (translation)
Use `choose a ha using fun i => exists_unit_fnOf_eq (hu i)`. Use `⟨⟨fun i => (a i : Γ(Z, N.U i)), fun i j => GlobalTheory.Cartier.fn_ext fun h => ?_⟩, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul] erw [fnOf_resG, fnOf_resG]`. Rewrite using `[ha, ha, hr i j h]`. Take `⟨i, hi⟩` from `exists_chart hN x`.

Use `TopologicalSpace.Opens.mem_iSup.2 ⟨i, ?_⟩` and prove the remaining obligations. Use `show x ∈ Z.basicOpen (a i : Γ(Z, N.U i))`. Rewrite using `[Scheme.basicOpen_of_isUnit _ (a i).isUnit]`. Conclude with `hi`.
-/
theorem exists_sec_of_unit_ratSec {Z : Scheme.{0}} [IsIntegral Z] {N : LB Z} (hN : N.IsLB)
    {r : N.ι → Z.functionFieldˣ} (hr : IsRatSec N r) (hu : ∀ i, ∀ x ∈ N.U i, UnitAt x (r i)) :
    ∃ s : N.Sec, ∀ x, x ∈ nonzeroLocus s := by
  choose a ha using fun i => exists_unit_fnOf_eq (hu i)
  refine ⟨⟨fun i => (a i : Γ(Z, N.U i)), fun i j => GlobalTheory.Cartier.fn_ext fun h => ?_⟩, fun x => ?_⟩
  · rw [map_mul]
    erw [fnOf_resG, fnOf_resG]
    rw [ha, ha, hr i j h]
  · obtain ⟨i, hi⟩ := exists_chart hN x
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨i, ?_⟩
    show x ∈ Z.basicOpen (a i : Γ(Z, N.U i))
    rw [Scheme.basicOpen_of_isUnit _ (a i).isUnit]
    exact hi

/- English proof (translation)
Take `⟨N, ι, _, hι⟩` from `V.ar.isProjOver`. Use `isProper_str (𝓞 F) N` as an intermediate fact. Establish `: IsProper V.p` using `hι ▸ inferInstance`. Establish `: CompactSpace V.X` using `QuasiCompact.compactSpace_of_compactSpace V.p`. Establish `hB'` using `LB.isLB_pull hB V.j`.

Take `⟨a, ha, s, hs⟩` from `exists_extend (nonZeroDivisors (𝓞 F)) V.pb hB hB' ((isGen_iff (idIso _)).1 (idIso_isGen hB')) τ`. Use `⟨s, fun w => ?_⟩` and prove the remaining obligations. Take `⟨j, hj⟩` from `exists_chart hB (V.j w)`. Take `⟨k, hk⟩` from `exists_chart hB' w`. Use `(mem_nonzeroLocus_iff_isUnit s hj).2 ?_` and prove the remaining obligations.

Establish `u : IsUnit (gs V.j w _ (s.f j))`. Rewrite using `[hs w j k hj hk]`. Use `IsUnit.mul ?_ ((Units.isUnit _).mul ((mem_nonzeroLocus_iff_isUnit τ hk).1 (hτ w)))` and prove the remaining obligations. Rewrite using `[V.pb.w, cst_comp]`. Establish `h0 : algebraMap (𝓞 F) F a ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ha`.

Use `IsUnit.of_mul_eq_one (cst (V.π ≫ Y.str) w (algebraMap (𝓞 F) F a)⁻¹) ?_` and prove the remaining obligations. Rewrite using `[← H1.cst_mul, mul_inv_cancel₀ h0, H1.cst_one]`. Rewrite `u` using `[gs_stalkMap V.j w _ hj]`. Conclude with `isUnit_of_map_unit _ _ u`.
-/
theorem exists_sec_of_generic {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y)
    {B : LB V.X} (hB : B.IsLB) (τ : (B.pull V.j).Sec) (hτ : ∀ w, w ∈ nonzeroLocus τ) :
    ∃ s : B.Sec, ∀ w : V.G, V.j w ∈ nonzeroLocus s := by
  obtain ⟨N, ι, _, hι⟩ := V.ar.isProjOver
  have := isProper_str (𝓞 F) N
  have : IsProper V.p := hι ▸ inferInstance
  have : CompactSpace V.X := QuasiCompact.compactSpace_of_compactSpace V.p
  have hB' := LB.isLB_pull hB V.j
  obtain ⟨a, ha, s, hs⟩ := exists_extend (nonZeroDivisors (𝓞 F)) V.pb hB hB'
    ((isGen_iff (idIso _)).1 (idIso_isGen hB')) τ
  refine ⟨s, fun w => ?_⟩
  obtain ⟨j, hj⟩ := exists_chart hB (V.j w)
  obtain ⟨k, hk⟩ := exists_chart hB' w
  refine (mem_nonzeroLocus_iff_isUnit s hj).2 ?_
  have u : IsUnit (gs V.j w _ (s.f j)) := by
    rw [hs w j k hj hk]
    refine IsUnit.mul ?_ ((Units.isUnit _).mul ((mem_nonzeroLocus_iff_isUnit τ hk).1 (hτ w)))
    rw [V.pb.w, cst_comp]
    have h0 : algebraMap (𝓞 F) F a ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ha
    refine IsUnit.of_mul_eq_one (cst (V.π ≫ Y.str) w (algebraMap (𝓞 F) F a)⁻¹) ?_
    rw [← H1.cst_mul, mul_inv_cancel₀ h0, H1.cst_one]
  rw [gs_stalkMap V.j w _ hj] at u
  exact isUnit_of_map_unit _ _ u

/- English proof (translation)
Simplify using `[LB.pull, LB.LinComb, dual, map_inv]`. Conclude with `map_inv (res _) _`.
-/
theorem g_pull_dual {X Z : Scheme.{0}} (B : LB X) (f : Z ⟶ X) (i j : (B.pull f).ι) :
    ((dual B).pull f).g i j = ((B.pull f).g i j)⁻¹ := by
  simp [LB.pull, LB.LinComb, dual, map_inv]
  exact map_inv (res _) _

/- English proof (translation)
Introduce `i j h` and use `by have e := g_pull_dual B f i j erw [e, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_units_inv, hr i j h, mul_inv] rfl`.
-/
theorem isRatSec_dual_pull {X Z : Scheme.{0}} [IsIntegral Z] {B : LB X} {f : Z ⟶ X}
    {r : (B.pull f).ι → Z.functionFieldˣ} (hr : IsRatSec (B.pull f) r) :
    IsRatSec ((dual B).pull f) fun i => (r i)⁻¹ := fun i j h => by
  have e := g_pull_dual B f i j
  erw [e, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_units_inv, hr i j h, mul_inv]
  rfl

/- English proof (translation)
Introduce `F _ _ Y V L r hr hu`. Establish `hN` using `LB.isLB_pull L.isLB V.j`. Take `⟨τ, hτ⟩` from `exists_sec_of_unit_ratSec hN hr hu`. Take `⟨s, hs⟩` from `exists_sec_of_generic V L.isLB τ hτ`. Establish `hN'` using `LB.isLB_pull L.dual.isLB V.j`.

Establish `hu' : ∀ i, ∀ x ∈ (L.dual.B.pull V.j).U i, UnitAt x (((fun i => (r i)⁻¹) i : V.G.functionFieldˣ) : V.G.functionField)` using `fun i x hx => by`. Simplify using `only [Units.val_inv_eq_inv_val]`. Conclude with `(hu i x hx).inv`. Take `⟨τ', hτ'⟩` from `exists_sec_of_unit_ratSec hN' (isRatSec_dual_pull hr) hu'`. Take `⟨s', hs'⟩` from `exists_sec_of_generic V L.dual.isLB τ' hτ'`.

Conclude with `⟨s, s', fun w _ => ⟨hs w, hs' w⟩⟩`.
-/
theorem exists_secs_nonvanishing : ∀ {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y) (L : GlobalTheory.HermLB V.p) (r : (L.B.pull V.j).ι → V.G.functionFieldˣ), GlobalTheory.Cartier.IsRatSec (L.B.pull V.j) r → (∀ i, ∀ x ∈ (L.B.pull V.j).U i, UnitAt x (r i : V.G.functionField)) → ∃ (s : L.B.Sec) (s' : L.dual.B.Sec), ∀ w : V.G, IsClosed ({w} : Set V.G) → V.j w ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s ∧ V.j w ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s' := by
  intro F _ _ Y V L r hr hu
  have hN := LB.isLB_pull L.isLB V.j
  obtain ⟨τ, hτ⟩ := exists_sec_of_unit_ratSec hN hr hu
  obtain ⟨s, hs⟩ := exists_sec_of_generic V L.isLB τ hτ
  have hN' := LB.isLB_pull L.dual.isLB V.j
  have hu' : ∀ i, ∀ x ∈ (L.dual.B.pull V.j).U i,
      UnitAt x (((fun i => (r i)⁻¹) i : V.G.functionFieldˣ) : V.G.functionField) := fun i x hx => by
    simp only [Units.val_inv_eq_inv_val]
    exact (hu i x hx).inv
  obtain ⟨τ', hτ'⟩ := exists_sec_of_unit_ratSec hN' (isRatSec_dual_pull hr) hu'
  obtain ⟨s', hs'⟩ := exists_sec_of_generic V L.dual.isLB τ' hτ'
  exact ⟨s, s', fun w _ => ⟨hs w, hs' w⟩⟩

end GlobalTheory.RatSecClear
