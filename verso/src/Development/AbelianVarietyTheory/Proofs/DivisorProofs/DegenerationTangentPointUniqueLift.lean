import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TanRel
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow

section General

variable {R : Type} [CommRing R] (I : Ideal R)

/- English proof (translation)
Use `show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _`. Rewrite using `[← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]`. Use `congrArg (fun q => Spec.map (CommRingCat.ofHom q)) (RingHom.ext fun r => ?_)` and prove the remaining obligations. Apply the tactic sequence `refine TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]`.
-/
theorem dualMap_mk_struct (e : ℕ) :
    spMap (algebraMap (R ⧸ I ^ (e + 1)) (DualNumber (R ⧸ I ^ (e + 1)))) ≫ thick R I e =
      spMap (dualMap (Ideal.Quotient.mk (I ^ (e + 1)))) ≫ (epsR R).hom := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  refine congrArg (fun q => Spec.map (CommRingCat.ofHom q)) (RingHom.ext fun r => ?_)
  refine TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

/- English proof (translation)
Establish `hs : Function.Surjective (dualMap (Ideal.Quotient.mk (I ^ (e + 1))))` using `fun x => by`. Take `⟨a, ha⟩` from `Ideal.Quotient.mk_surjective x.fst`. Take `⟨b, hb⟩` from `Ideal.Quotient.mk_surjective x.snd`. Apply the tactic sequence `refine ⟨TrivSqZeroExt.inl a + TrivSqZeroExt.inr b, TrivSqZeroExt.ext ?_ ?_⟩ <;> simp [dualMap, ha, hb]`. Establish `hk : RingHom.ker (dualMap (Ideal.Quotient.mk (I ^ (e + 1)))) ≤ RingHom.ker (Ideal.Quotient.mk ((I.map (algebraMap R (DualNumber R))) ^ (e + 1)))` using `fun x hx => by`.

Rewrite `hx` using `[RingHom.mem_ker]`. Establish `h1 : x.fst ∈ I ^ (e + 1)`. Use `congrArg TrivSqZeroExt.fst hx` as an intermediate fact. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem]`. Simplify `this` using `[dualMap]`.

Establish `h2 : x.snd ∈ I ^ (e + 1)`. Use `congrArg TrivSqZeroExt.snd hx` as an intermediate fact. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem]`. Simplify `this` using `[dualMap]`. Establish `ex : x = algebraMap R (DualNumber R) x.fst + algebraMap R (DualNumber R) x.snd * DualNumber.eps`.

Apply the tactic sequence `ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]`. Rewrite using `[Ideal.mk_ker, ← Ideal.map_pow, ex]`. Conclude with `add_mem (Ideal.mem_map_of_mem _ h1) (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ h2))`. Use `⟨spMap (RingHom.liftOfSurjective _ hs ⟨_, hk⟩), ?_⟩` and prove the remaining obligations. Use `show Spec.map _ ≫ Spec.map _ = Spec.map _`.

Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp, RingHom.liftOfSurjective_comp]`.
-/
theorem exists_factor_dualMap (e : ℕ) :
    ∃ l, l ≫ spMap (dualMap (Ideal.Quotient.mk (I ^ (e + 1)))) =
      adicLevelι (I.map (algebraMap R (DualNumber R))) (e + 1) := by
  have hs : Function.Surjective (dualMap (Ideal.Quotient.mk (I ^ (e + 1)))) := fun x => by
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective x.fst
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective x.snd
    refine ⟨TrivSqZeroExt.inl a + TrivSqZeroExt.inr b, TrivSqZeroExt.ext ?_ ?_⟩ <;> simp [dualMap, ha, hb]
  have hk : RingHom.ker (dualMap (Ideal.Quotient.mk (I ^ (e + 1)))) ≤
      RingHom.ker (Ideal.Quotient.mk ((I.map (algebraMap R (DualNumber R))) ^ (e + 1))) := fun x hx => by
    rw [RingHom.mem_ker] at hx
    have h1 : x.fst ∈ I ^ (e + 1) := by
      have := congrArg TrivSqZeroExt.fst hx
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simpa [dualMap] using this
    have h2 : x.snd ∈ I ^ (e + 1) := by
      have := congrArg TrivSqZeroExt.snd hx
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simpa [dualMap] using this
    have ex : x = algebraMap R (DualNumber R) x.fst + algebraMap R (DualNumber R) x.snd * DualNumber.eps := by
      ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
    rw [Ideal.mk_ker, ← Ideal.map_pow, ex]
    exact add_mem (Ideal.mem_map_of_mem _ h1) (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ h2))
  refine ⟨spMap (RingHom.liftOfSurjective _ hs ⟨_, hk⟩), ?_⟩
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, RingHom.liftOfSurjective_comp]

variable {I} [IsDomain R] {D : DegData R I} {A : PolAV (Sp (FractionRing R))}
  {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `(FormalPoint.isPointOf_iff_reduction U gm y).2 fun e => ?_` and prove the remaining obligations. Take `⟨ye, h1, h2⟩` from `h e`. Take `⟨l, hl⟩` from `exists_factor_dualMap I e`.

Establish `h3 : FormalPoint.HasCoords U e gm _ ye` using `h2`. Establish `h4` using `h3.comp l`. Establish `h5 : FormalPoint.reduction I y e = l ≫ ye`. Rewrite using `[← cancel_mono (fstG I e G).left, FormalPoint.reduction_fstG, Category.assoc, h1, ← hl]`. Conclude with `Category.assoc _ _ _`.

Rewrite using `[h5, ← hl]`. Conclude with `h4`. Introduce `h e`. Take `⟨ye, hy⟩` from `FormalPoint.exists_hasCoords U e gm _ _ (dualMap_mk_struct I e)`. Conclude with `⟨ye, h.comp_fstG_eq hy, hy⟩`.
-/
theorem tanRel_iff_isPointOf (y : epsR R ⟶ G) (gm : GtPt D.toPre (epsR R)) :
    TanRel U y gm ↔ FormalPoint.IsPointOf U gm y := by
  constructor
  · intro h
    refine (FormalPoint.isPointOf_iff_reduction U gm y).2 fun e => ?_
    obtain ⟨ye, h1, h2⟩ := h e
    obtain ⟨l, hl⟩ := exists_factor_dualMap I e
    have h3 : FormalPoint.HasCoords U e gm _ ye := h2
    have h4 := h3.comp l
    have h5 : FormalPoint.reduction I y e = l ≫ ye := by
      rw [← cancel_mono (fstG I e G).left, FormalPoint.reduction_fstG, Category.assoc, h1, ← hl]
      exact Category.assoc _ _ _
    rw [h5, ← hl]
    exact h4
  · intro h e
    obtain ⟨ye, hy⟩ := FormalPoint.exists_hasCoords U e gm _ _ (dualMap_mk_struct I e)
    exact ⟨ye, h.comp_fstG_eq hy, hy⟩

/- English proof (translation)
Take `⟨o, ho, hp⟩` from `hg`. Set `k : baseOver (Sp R) ⟶ epsR R` to `Over.homMk (redE R) (by show Spec.map _ ≫ Spec.map _ = 𝟙 _`. Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Establish `h3 : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R` using `RingHom.ext fun r => (TrivSqZeroExt.fstHom R R R).commutes r`. Rewrite using `[h3]`.

Conclude with `Spec.map_id _)`. Establish `h1 : k ≫ y = 1` using `(FormalPoint.existsUnique_isPointOf_unit U o).unique (h.pull k hp) (FormalPoint.isPointOf_one U ho)`. Use `(congrArg (·.left) h1).trans ?_` and prove the remaining obligations. Use `show (toUnit _ ≫ η[G]).left = _`. Simplify using the standard rewrite rules.
-/
theorem isTangent_of_isPointOf [IsLocalRing R] [IsAdicComplete I R] {y : epsR R ⟶ G} {gm : GtPt D.toPre (epsR R)}
    (hg : GtTan gm) (h : FormalPoint.IsPointOf U gm y) : IsTangent y := by
  obtain ⟨o, ho, hp⟩ := hg
  let k : baseOver (Sp R) ⟶ epsR R := Over.homMk (redE R) (by
    show Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have h3 : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R :=
      RingHom.ext fun r => (TrivSqZeroExt.fstHom R R R).commutes r
    rw [h3]
    exact Spec.map_id _)
  have h1 : k ≫ y = 1 := (FormalPoint.existsUnique_isPointOf_unit U o).unique (h.pull k hp)
    (FormalPoint.isPointOf_one U ho)
  refine (congrArg (·.left) h1).trans ?_
  show (toUnit _ ≫ η[G]).left = _
  simp

end General

/- English proof (translation)
Introduce `V _ _ _ _ hV D A G _ _ _ U gm hg`. Establish `: Module.Finite V (DualNumber V)` using `inferInstanceAs (Module.Finite V (V × V))`. Use `isAdicComplete_map_of_finite (IsLocalRing.maximalIdeal V) (DualNumber V)` as an intermediate fact. Establish `: Nontrivial (DualNumber V)` using `(TrivSqZeroExt.inl_injective (R := V) (M := V)).nontrivial`. Establish `: IsLocalRing (DualNumber V)` using `IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => by`.

Rewrite using `[TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.isUnit_iff_isUnit_fst]`. Simplify using `using IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst`. Take `⟨y, hy, hu⟩` from `FormalPoint.existsUnique_isPointOf U.toUnifPre gm`. Conclude with `⟨y, ⟨isTangent_of_isPointOf _ hg hy, (tanRel_iff_isPointOf _ _ _).2 hy⟩, fun y' h' => hu y' ((tanRel_iff_isPointOf _ _ _).1 h'.2)⟩`.
-/
theorem existsUnique_tangent_of_gtTan : AllV fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ gm : GtPt D.toPre (epsR V), GtTan gm → ∃! y : epsR V ⟶ G, IsTangent y ∧ TanRel U.toUnifPre y gm := by
  intro V _ _ _ _ hV D A G _ _ _ U gm hg
  have : Module.Finite V (DualNumber V) := inferInstanceAs (Module.Finite V (V × V))
  have := isAdicComplete_map_of_finite (IsLocalRing.maximalIdeal V) (DualNumber V)
  have : Nontrivial (DualNumber V) := (TrivSqZeroExt.inl_injective (R := V) (M := V)).nontrivial
  have : IsLocalRing (DualNumber V) := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.isUnit_iff_isUnit_fst]
    simpa using IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst
  obtain ⟨y, hy, hu⟩ := FormalPoint.existsUnique_isPointOf U.toUnifPre gm
  exact ⟨y, ⟨isTangent_of_isPointOf _ hg hy, (tanRel_iff_isPointOf _ _ _).2 hy⟩,
    fun y' h' => hu y' ((tanRel_iff_isPointOf _ _ _).1 h'.2)⟩

end GlobalTheory.MBLow

end
