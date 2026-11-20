import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisRaynaudTangentInvariantFields
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LieSurjLocal

/- English proof (translation)
Introduce `R _ _ G B _ _ _ _ q _ hsm u`. Establish `: Nontrivial (DualNumber R)` using `(TrivSqZeroExt.inl_injective (R := R) (M := R)).nontrivial`. Establish `: IsLocalRing (DualNumber R)` using `IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => by`. Rewrite using `[TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.isUnit_iff_isUnit_fst]`. Simplify using `using IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst`.

Set `π : CommRingCat.of (DualNumber R) ⟶ CommRingCat.of R` to `CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom`. Establish `hπ : Function.Surjective π` using `fun x => ⟨TrivSqZeroExt.inl x, rfl⟩`. Establish `hn : IsNilpotent (RingHom.ker π.hom)` using `⟨2, by`. Rewrite using `[pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]`. Introduce `x hx y hy`.

Establish `hx' : x.fst = 0` using `hx`. Establish `hy' : y.fst = 0` using `hy`. Rewrite using `[Ideal.mem_bot]`. Apply the tactic sequence `ext <;> simp [hx', hy']⟩`. Establish `hu : Spec.map π ≫ (tv u).left = η[B].left` using `GlobalTheory.RayBasis.isTangent_pt u`.

Establish `h0 : η[G].left ≫ q.left = Spec.map π ≫ (tv u).left` using `(congrArg (·.left) (IsMonHom.one_hom q)).trans hu.symm`. Take `⟨U, V, hU, hV, hVU, -, hxV⟩` from `GlobalTheory.exists_isAffineOpen_pair q.left (η[G].left (IsLocalRing.closedPoint R)) (O := ⊤) trivial`. Take `⟨x, hx, hq⟩` from `GlobalTheory.exists_lift_of_smooth_of_isAffineOpen q.left hU hV hVU π (tv u).left η[G].left h0 (GlobalTheory.range_subset_opens_of_isLocalRing _ (by`. Establish `: IsLocalHom π.hom` using `.of_surjective _ hπ`. Establish `e : q.left (η[G].left (IsLocalRing.closedPoint R)) = (tv u).left (Spec.map π (IsLocalRing.closedPoint R))` using `congr($h0 (IsLocalRing.closedPoint R))`.

Rewrite using `[← Spec_closedPoint (f := π), ← e]`. Conclude with `hVU hxV))`. Use the proof step `(GlobalTheory.range_subset_opens_of_isLocalRing _ hxV) (by`. Introduce `R' S _ _ _ _ _ _ p hp φ`. Establish `hs : Function.Surjective p` using `fun c => (hπ c).imp fun b hb => (hp b).trans hb`.

Establish `hk : IsNilpotent (RingHom.ker p.toRingHom)`. Use `hn using 1` and compare the differences between its conclusion and the goal. Conclude with `Ideal.ext fun b => Eq.congr_left (hp b)`. Conclude with `⟨Algebra.FormallySmooth.liftOfSurjective φ p hs hk, Algebra.FormallySmooth.comp_liftOfSurjective φ p hs hk⟩)`. Set `xo : overAt (𝟙 (Sp R)) (DualNumber R) ⟶ G` to `Over.homMk x (by rw [← Over.w q, reassoc_of% hq]; exact Over.w (tv u))`.

Establish `hz : smT (𝟙 (Sp R)) 0 xo = 1`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[smT_left, Hom.one_def, Over.comp_left, Over.toUnit_left]`. Use `show spMap _ ≫ x = (spMap (algebraMap R (DualNumber R)) ≫ 𝟙 _) ≫ _`. Rewrite using `[Category.comp_id, ← hx, ← Category.assoc]`.

Use `congr 1`. Simplify using `only [spMap, ← Spec.map_comp]`. Use `congr 1`. Apply `CommRingCat.hom_ext` to reduce the goal to its premises. Apply `RingHom.ext` to reduce the goal to its premises.

Introduce `r`. Apply the tactic sequence `ext <;> simp [π, epsMul, TrivSqZeroExt.algebraMap_eq_inl]`. Conclude with `⟨ReciprocityTheory.ChartRestriction.G.PullbackSections.mkT xo hz, Over.OverMorphism.ext hq⟩`.
-/
theorem map_surjective : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G B : Over (Sp R)) [GrpObj G] [GrpObj B] [IsCommMonObj G] [IsCommMonObj B] (q : G ⟶ B) [IsMonHom q], Smooth q.left → ∀ u : TanM (𝟙 (Sp R)) B, ∃ v : TanM (𝟙 (Sp R)) G, tv v ≫ q = tv u := by
  intro R _ _ G B _ _ _ _ q _ hsm u
  have : Nontrivial (DualNumber R) := (TrivSqZeroExt.inl_injective (R := R) (M := R)).nontrivial
  have : IsLocalRing (DualNumber R) := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.isUnit_iff_isUnit_fst]
    simpa using IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst
  let π : CommRingCat.of (DualNumber R) ⟶ CommRingCat.of R :=
    CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom
  have hπ : Function.Surjective π := fun x => ⟨TrivSqZeroExt.inl x, rfl⟩
  have hn : IsNilpotent (RingHom.ker π.hom) := ⟨2, by
    rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
    intro x hx y hy
    have hx' : x.fst = 0 := hx
    have hy' : y.fst = 0 := hy
    rw [Ideal.mem_bot]
    ext <;> simp [hx', hy']⟩
  have hu : Spec.map π ≫ (tv u).left = η[B].left := GlobalTheory.RayBasis.isTangent_pt u
  have h0 : η[G].left ≫ q.left = Spec.map π ≫ (tv u).left :=
    (congrArg (·.left) (IsMonHom.one_hom q)).trans hu.symm
  obtain ⟨U, V, hU, hV, hVU, -, hxV⟩ :=
    GlobalTheory.exists_isAffineOpen_pair q.left (η[G].left (IsLocalRing.closedPoint R)) (O := ⊤) trivial
  obtain ⟨x, hx, hq⟩ := GlobalTheory.exists_lift_of_smooth_of_isAffineOpen q.left hU hV hVU π
    (tv u).left η[G].left h0
    (GlobalTheory.range_subset_opens_of_isLocalRing _ (by
      have : IsLocalHom π.hom := .of_surjective _ hπ
      have e : q.left (η[G].left (IsLocalRing.closedPoint R)) =
        (tv u).left (Spec.map π (IsLocalRing.closedPoint R)) := congr($h0 (IsLocalRing.closedPoint R))
      rw [← Spec_closedPoint (f := π), ← e]
      exact hVU hxV))
    (GlobalTheory.range_subset_opens_of_isLocalRing _ hxV) (by
      intro R' S _ _ _ _ _ _ p hp φ
      have hs : Function.Surjective p := fun c => (hπ c).imp fun b hb => (hp b).trans hb
      have hk : IsNilpotent (RingHom.ker p.toRingHom) := by
        convert hn using 1
        exact Ideal.ext fun b => Eq.congr_left (hp b)
      exact ⟨Algebra.FormallySmooth.liftOfSurjective φ p hs hk,
        Algebra.FormallySmooth.comp_liftOfSurjective φ p hs hk⟩)
  let xo : overAt (𝟙 (Sp R)) (DualNumber R) ⟶ G :=
    Over.homMk x (by rw [← Over.w q, reassoc_of% hq]; exact Over.w (tv u))
  have hz : smT (𝟙 (Sp R)) 0 xo = 1 := by
    apply Over.OverMorphism.ext
    rw [smT_left, Hom.one_def, Over.comp_left, Over.toUnit_left]
    show spMap _ ≫ x = (spMap (algebraMap R (DualNumber R)) ≫ 𝟙 _) ≫ _
    rw [Category.comp_id, ← hx, ← Category.assoc]
    congr 1
    simp only [spMap, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    ext <;> simp [π, epsMul, TrivSqZeroExt.algebraMap_eq_inl]
  exact ⟨ReciprocityTheory.ChartRestriction.G.PullbackSections.mkT xo hz, Over.OverMorphism.ext hq⟩

end GlobalTheory.LieSurjLocal
