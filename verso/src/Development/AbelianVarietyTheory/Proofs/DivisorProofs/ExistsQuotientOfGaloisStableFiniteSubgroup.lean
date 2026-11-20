import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyDegreeEqCardKernelOfKilledByInvertible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorThroughIsogenyOfKillsKernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientAbelianVarietyByFiniteSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleSubgroupSchemeOfGaloisStablePoiStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.Quot

/- English proof (translation)
Set `Ω` to `AlgebraicClosure K`. Set `q : Sp Ω ⟶ Sp K` to `spMap (algebraMap K Ω)`. Establish `: Surjective q` using `⟨fun x => ⟨IsLocalRing.closedPoint Ω, Subsingleton.elim _ _⟩⟩`. Establish `: JacobsonSpace ↥(pullback H.hom q)` using `LocallyOfFiniteType.jacobsonSpace (pullback.snd H.hom q)`. Establish `hd : Dense (closedPoints ↥(pullback H.hom q))` using `dense_iff_closure_eq.2 closure_closedPoints`.

Establish `hD` using `(pullback.fst H.hom q).surjective.denseRange.dense_image (pullback.fst H.hom q).continuous hd`. Establish `hdom : IsDominant (equalizer.ι a.left b.left)`. Use `⟨hD.mono ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨w, hw₀, rfl⟩`. Establish `hw : IsClosed ({w} : Set ↥(pullback H.hom q))` using `hw₀`.

Set `y : Sp Ω ⟶ H.left` to `pointOfClosedPoint (pullback.snd H.hom q) w hw ≫ pullback.fst H.hom q`. Establish `hy : y ≫ H.hom = q`. Simplify using `only [y, Category.assoc, pullback.condition]`. Rewrite using `[← Category.assoc, pointOfClosedPoint_comp, Category.id_comp]`. Set `x : ptOver K Ω ⟶ H` to `Over.homMk y hy`.

Establish `hx : y ≫ a.left = y ≫ b.left` using `congrArg CommaMorphism.left (h x)`. Use `⟨equalizer.lift y hx (IsLocalRing.closedPoint Ω), ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(equalizer.lift y hx ≫ equalizer.ι a.left b.left) (IsLocalRing.closedPoint Ω) = _`. Rewrite using `[equalizer.lift_ι]`. Conclude with `congrArg (pullback.fst H.hom q) (pointOfClosedPoint_apply (pullback.snd H.hom q) w hw _)`.

Conclude with `Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated Z.hom ((Over.w a).trans (Over.w b).symm) (equalizer.ι _ _) (equalizer.condition _ _))`.
-/
theorem over_ext_of_pt_eq {K : Type} [Field K] {H Z : Over (Sp K)} [IsReduced H.left]
    [LocallyOfFiniteType H.hom] [IsSeparated Z.hom] (a b : H ⟶ Z)
    (h : ∀ y : ptOver K (AlgebraicClosure K) ⟶ H, y ≫ a = y ≫ b) : a = b := by
  let Ω := AlgebraicClosure K
  let q : Sp Ω ⟶ Sp K := spMap (algebraMap K Ω)
  have : Surjective q := ⟨fun x => ⟨IsLocalRing.closedPoint Ω, Subsingleton.elim _ _⟩⟩
  have : JacobsonSpace ↥(pullback H.hom q) :=
    LocallyOfFiniteType.jacobsonSpace (pullback.snd H.hom q)
  have hd : Dense (closedPoints ↥(pullback H.hom q)) := dense_iff_closure_eq.2 closure_closedPoints
  have hD := (pullback.fst H.hom q).surjective.denseRange.dense_image
    (pullback.fst H.hom q).continuous hd
  have hdom : IsDominant (equalizer.ι a.left b.left) := by
    refine ⟨hD.mono ?_⟩
    rintro _ ⟨w, hw₀, rfl⟩
    have hw : IsClosed ({w} : Set ↥(pullback H.hom q)) := hw₀
    let y : Sp Ω ⟶ H.left :=
      pointOfClosedPoint (pullback.snd H.hom q) w hw ≫ pullback.fst H.hom q
    have hy : y ≫ H.hom = q := by
      simp only [y, Category.assoc, pullback.condition]
      rw [← Category.assoc, pointOfClosedPoint_comp, Category.id_comp]
    let x : ptOver K Ω ⟶ H := Over.homMk y hy
    have hx : y ≫ a.left = y ≫ b.left := congrArg CommaMorphism.left (h x)
    refine ⟨equalizer.lift y hx (IsLocalRing.closedPoint Ω), ?_⟩
    change (equalizer.lift y hx ≫ equalizer.ι a.left b.left) (IsLocalRing.closedPoint Ω) = _
    rw [equalizer.lift_ι]
    exact congrArg (pullback.fst H.hom q) (pointOfClosedPoint_apply (pullback.snd H.hom q) w hw _)
  exact Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated Z.hom
    ((Over.w a).trans (Over.w b).symm) (equalizer.ι _ _) (equalizer.condition _ _))

end GlobalTheory.AV.Quot

namespace GlobalTheory.AV.AbVar

/- English proof (translation)
Introduce `K _ A G hfin hn hgal`. Take `⟨H, _, i, hi, hmono, hfinH, het, hG⟩` from `GlobalTheory.T.exists_finiteEtale_subgroupScheme_of_galoisStable_points K A G hfin hn hgal`. Take `⟨B, q, hq, hker⟩` from `GlobalTheory.T.exists_quotient_abelianVariety_by_finiteSubgroup K A H i hi hmono hfinH`. Establish `: IsReduced H.left` using `GlobalTheory.isReduced_of_smooth_of_isReduced H.hom`. Establish `hext : ∀ (Z : Over (Sp K)) [IsSeparated Z.hom] (a b : H ⟶ Z), (∀ y : A.Pt, y ∈ G → ∀ (y' : ptOver K (AlgebraicClosure K) ⟶ H), y' ≫ i = y → y' ≫ a = y' ≫ b) → a = b`.

Introduce `Z _ a b hab`. Conclude with `GlobalTheory.AV.Quot.over_ext_of_pt_eq a b fun y' => hab _ ((hG _).2 ⟨y', rfl⟩) y' rfl`. Establish `hkerG : (ptMap q).ker = G`. Use extensionality with `x`. Rewrite using `[MonoidHom.mem_ker, ptMap_apply, hker, hG]`.

Use `⟨B, q, hq, ?_, hkerG, ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.AV.DegSep.deg_eq_card_ker_of_killed K A B q (Nat.card G) hn hq, hkerG]`. Introduce `T x hx`. Take `⟨y, rfl⟩` from `(hker T x).1 hx`. Use `A.ab.proper` as an intermediate fact.

Establish `hpow : i ^ Nat.card G = 1`. Use `hext A.X _ _ ?_` and prove the remaining obligations. Introduce `z hz y' hy'`. Rewrite using `[MonObj.comp_pow, hy', MonObj.comp_one]`. Establish `h1` using `pow_card_eq_one' (G := G) (x := ⟨z, hz⟩)`.

Conclude with `congrArg Subtype.val h1`. Rewrite using `[← MonObj.comp_pow, hpow, MonObj.comp_one]`. Introduce `C f hf`. Use `GlobalTheory.AV.AbVar.exists_factor_of_isogeny K A B C q f hq ?_` and prove the remaining obligations. Introduce `T x hx`.

Take `⟨y, rfl⟩` from `(hker T x).1 hx`. Use `C.ab.proper` as an intermediate fact. Establish `hif : i ≫ f.hom = 1`. Use `hext C.X _ _ ?_` and prove the remaining obligations. Introduce `z hz y' hy'`.

Rewrite using `[← Category.assoc, hy', MonObj.comp_one]`. Conclude with `hf hz`. Rewrite using `[Category.assoc, hif, MonObj.comp_one]`.
-/
theorem exists_quot_of_galois_stable : ∀ (K : Type) [Field K] (A : AbVar K) (G : Subgroup A.Pt), Finite G →
    ((Nat.card G : ℕ) : K) ≠ 0 → (∀ (σ : Gal K) (x : A.Pt), x ∈ G → galPts A.X σ x ∈ G) →
    ∃ (B : AbVar K) (q : A ⟶ B), IsIsogeny q ∧ deg q = Nat.card G ∧ (ptMap q).ker = G ∧
      ∀ (C : AbVar K) (f : A ⟶ C), G ≤ (ptMap f).ker → ∃ g : B ⟶ C, q ≫ g = f := by
  intro K _ A G hfin hn hgal
  obtain ⟨H, _, i, hi, hmono, hfinH, het, hG⟩ := GlobalTheory.T.exists_finiteEtale_subgroupScheme_of_galoisStable_points K A G hfin hn hgal
  obtain ⟨B, q, hq, hker⟩ := GlobalTheory.T.exists_quotient_abelianVariety_by_finiteSubgroup K A H i hi hmono hfinH
  have : IsReduced H.left := GlobalTheory.isReduced_of_smooth_of_isReduced H.hom

  have hext : ∀ (Z : Over (Sp K)) [IsSeparated Z.hom] (a b : H ⟶ Z),
      (∀ y : A.Pt, y ∈ G → ∀ (y' : ptOver K (AlgebraicClosure K) ⟶ H), y' ≫ i = y → y' ≫ a = y' ≫ b) →
      a = b := by
    intro Z _ a b hab
    exact GlobalTheory.AV.Quot.over_ext_of_pt_eq a b fun y' => hab _ ((hG _).2 ⟨y', rfl⟩) y' rfl
  have hkerG : (ptMap q).ker = G := by
    ext x
    rw [MonoidHom.mem_ker, ptMap_apply, hker, hG]
  refine ⟨B, q, hq, ?_, hkerG, ?_⟩
  · rw [GlobalTheory.AV.DegSep.deg_eq_card_ker_of_killed K A B q (Nat.card G) hn hq, hkerG]
    intro T x hx
    obtain ⟨y, rfl⟩ := (hker T x).1 hx
    have := A.ab.proper
    have hpow : i ^ Nat.card G = 1 := by
      refine hext A.X _ _ ?_
      intro z hz y' hy'
      rw [MonObj.comp_pow, hy', MonObj.comp_one]
      have h1 := pow_card_eq_one' (G := G) (x := ⟨z, hz⟩)
      exact congrArg Subtype.val h1
    rw [← MonObj.comp_pow, hpow, MonObj.comp_one]
  · intro C f hf
    refine GlobalTheory.AV.AbVar.exists_factor_of_isogeny K A B C q f hq ?_
    intro T x hx
    obtain ⟨y, rfl⟩ := (hker T x).1 hx
    have := C.ab.proper
    have hif : i ≫ f.hom = 1 := by
      refine hext C.X _ _ ?_
      intro z hz y' hy'
      rw [← Category.assoc, hy', MonObj.comp_one]
      exact hf hz
    rw [Category.assoc, hif, MonObj.comp_one]

end GlobalTheory.AV.AbVar
