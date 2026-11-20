import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRigidTranslatePrincipalPolarisationOrderTw
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueFieldMapFiniteOfQuasiFinite
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.TwoTorsionDescent

/- English proof (translation)
Introduce `K Ω _ _ _ ga A G _ α h x hx`. Use `set T : Over (Sp K) := Over.mk ((𝟙_ (Over (Sp Ω))).hom ≫ spMap ga) with hT`. Set `zo : T ⟶ A.A` to `pushHom h (𝟙_ (Over (Sp Ω))) x`. Establish `hzo : zo * zo = 1` using `by show pushHom h _ x * pushHom h _ x = 1`. Rewrite using `[← map_mul, hx, map_one]`.

Establish `hzl : zo.left = x.left ≫ α` using `rfl`. Establish `hmul : zo ≫ mulN A.A 2 = toUnit T ≫ η[A.A]`. Rewrite using `[GlobalTheory.GrpTangent.mulN_eq_pow, MonObj.comp_pow, Category.comp_id, sq, hzo]`. Both sides reduce to the same expression. Set `t : T ⟶ torsion A.A 2` to `pullback.lift zo (toUnit T) hmul`.

Establish `ht : t ≫ torsion.ι A.A 2 = zo` using `pullback.lift_fst _ _ _`. Establish `h2 : IsUnit ((2 : ℕ) : Γ(Sp K, ⊤))`. Establish `e : ((2 : ℕ) : Γ(Sp K, ⊤)) = (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (2 : K)`. Rewrite using `[map_ofNat]`. Both sides reduce to the same expression.

Rewrite using `[e]`. Conclude with `(IsUnit.mk0 (2 : K) two_ne_zero).map _`. Use `haveI := A.isAb`. Establish `hfin : IsFinite (torsion A.A 2).hom` using `(GlobalTheory.GrpTangent.finiteEtale_mulN_torsion A.A h2).2.1`. Use `set X := (torsion A.A 2).left`.

Use `set p := (torsion A.A 2).hom`. Set `tl : Sp Ω ⟶ X` to `t.left`. Set `w : X` to `tl (IsLocalRing.closedPoint Ω)`. Set `φ : X.residueField w ⟶ CommRingCat.of Ω` to `X.descResidueField (Scheme.stalkClosedPointTo tl)`. Establish `htl : Spec.map φ ≫ X.fromSpecResidueField w = tl` using `Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField Ω X tl`.

Set `s : Sp K` to `p w`. Use `haveI : s.asIdeal.IsPrime := s.isPrime`. Use `haveI : s.asIdeal.IsMaximal := by rw [Ideal.eq_bot_of_prime s.asIdeal]; exact Ideal.bot_isMaximal`. Set `c : K →+* (Sp K).residueField s` to `(Scheme.Spec.residueFieldIso (CommRingCat.of K) s).inv.hom.comp (algebraMap K s.asIdeal.ResidueField)`. Establish `hc : spMap c = (Sp K).fromSpecResidueField s`.

Rewrite using `[← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField, ← Spec.map_comp]`. Both sides reduce to the same expression. Establish `hcfin : c.Finite`. Use `RingHom.Finite.of_surjective _ ?_` and prove the remaining obligations. Use `(Scheme.Spec.residueFieldIso (CommRingCat.of K) s).commRingCatIsoToRingEquiv.symm.surjective.comp ?_` and prove the remaining obligations.

Establish `hq : Function.Surjective (Ideal.Quotient.mk s.asIdeal)` using `Ideal.Quotient.mk_surjective`. Establish `hb` using `Ideal.bijective_algebraMap_quotient_residueField s.asIdeal`. Establish `e : (algebraMap K s.asIdeal.ResidueField) = (algebraMap (K ⧸ s.asIdeal) s.asIdeal.ResidueField).comp (Ideal.Quotient.mk s.asIdeal)`. Use extensionality with `a`. Both sides reduce to the same expression.

Rewrite using `[e]`. Conclude with `hb.2.comp hq`. Set `io : K →+* X.residueField w` to `(p.residueFieldMap w).hom.comp c`. Establish `hio : io.Finite` using `(GlobalTheory.residueFieldMap_finite_of_locallyQuasiFinite p w).comp hcfin`. Establish `hsio : spMap io = X.fromSpecResidueField w ≫ p`.

Rewrite using `[← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← hc, ← Spec.map_comp]`. Both sides reduce to the same expression. Establish `hu : X.fromSpecResidueField w ≫ p = spMap io` using `hsio.symm`. Set `u : Over.mk (spMap io) ⟶ torsion A.A 2` to `Over.homMk (X.fromSpecResidueField w) hu`. Set `y : Over.mk (spMap io) ⟶ A.A` to `u ≫ torsion.ι A.A 2`.

Establish `hy : y * y = 1`. Establish `e1 : y * y = y ≫ mulN A.A 2`. Rewrite using `[GlobalTheory.GrpTangent.mulN_eq_pow, MonObj.comp_pow, Category.comp_id, sq]`. Establish `e2 : torsion.ι A.A 2 ≫ mulN A.A 2 = pullback.snd (mulN A.A 2) η[A.A] ≫ η[A.A]` using `pullback.condition`. Rewrite using `[e1, Category.assoc, e2]`.

Use `show (u ≫ pullback.snd (mulN A.A 2) η[A.A]) ≫ η[A.A] = toUnit _ ≫ η[A.A]`. Rewrite using `[toUnit_unique (u ≫ pullback.snd (mulN A.A 2) η[A.A]) (toUnit _)]`. Establish `hlo : Spec.map φ ≫ X.fromSpecResidueField w ≫ p = spMap ga`. Rewrite using `[← Category.assoc, htl]`. Conclude with `Over.w t`.

Use `⟨X.residueField w, inferInstance, io, φ.hom, y, hio, ?_, hy, ?_⟩` and prove the remaining obligations. Establish `e : spMap (φ.hom.comp io) = spMap ga`. Rewrite using `[← hlo, ← hsio]`. Use `show _ = Spec.map φ ≫ Spec.map (CommRingCat.ofHom io)`. Use `erw [← Spec.map_comp]`.

Both sides reduce to the same expression. Establish `e'` using `Spec.map_inj.mp e`. Conclude with `congrArg CommRingCat.Hom.hom e'`. Use `show Spec.map (CommRingCat.ofHom φ.hom) ≫ (X.fromSpecResidueField w ≫ (torsion.ι A.A 2).left) = x.left ≫ α`. Rewrite using `[CommRingCat.ofHom_hom, ← Category.assoc, htl, ← hzl, ← ht]`.

Both sides reduce to the same expression.
-/
theorem exists_finite_ext_of_sq_eq_one : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] (ga : K →+* Ω) (A : PolAV (Sp K)) (G : Over (Sp Ω)) [GrpObj G] (α : G.left ⟶ A.A.left), IsGrpPullback G A.A (spMap ga) α → ∀ x : 𝟙_ (Over (Sp Ω)) ⟶ G, x * x = 1 → ∃ (K' : Type) (_ : Field K') (io : K →+* K') (l : K' →+* Ω) (y : Over.mk (spMap io) ⟶ A.A), io.Finite ∧ l.comp io = ga ∧ y * y = 1 ∧ spMap l ≫ y.left = x.left ≫ α := by
  intro K Ω _ _ _ ga A G _ α h x hx

  set T : Over (Sp K) := Over.mk ((𝟙_ (Over (Sp Ω))).hom ≫ spMap ga) with hT
  let zo : T ⟶ A.A := pushHom h (𝟙_ (Over (Sp Ω))) x
  have hzo : zo * zo = 1 := by
    show pushHom h _ x * pushHom h _ x = 1
    rw [← map_mul, hx, map_one]
  have hzl : zo.left = x.left ≫ α := rfl
  have hmul : zo ≫ mulN A.A 2 = toUnit T ≫ η[A.A] := by
    rw [GlobalTheory.GrpTangent.mulN_eq_pow, MonObj.comp_pow, Category.comp_id, sq, hzo]
    rfl
  let t : T ⟶ torsion A.A 2 := pullback.lift zo (toUnit T) hmul
  have ht : t ≫ torsion.ι A.A 2 = zo := pullback.lift_fst _ _ _

  have h2 : IsUnit ((2 : ℕ) : Γ(Sp K, ⊤)) := by
    have e : ((2 : ℕ) : Γ(Sp K, ⊤)) = (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (2 : K) := by
      rw [map_ofNat]; rfl
    rw [e]
    exact (IsUnit.mk0 (2 : K) two_ne_zero).map _
  haveI := A.isAb
  have hfin : IsFinite (torsion A.A 2).hom := (GlobalTheory.GrpTangent.finiteEtale_mulN_torsion A.A h2).2.1
  set X := (torsion A.A 2).left
  set p := (torsion A.A 2).hom
  let tl : Sp Ω ⟶ X := t.left
  let w : X := tl (IsLocalRing.closedPoint Ω)
  let φ : X.residueField w ⟶ CommRingCat.of Ω := X.descResidueField (Scheme.stalkClosedPointTo tl)
  have htl : Spec.map φ ≫ X.fromSpecResidueField w = tl :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField Ω X tl

  let s : Sp K := p w
  haveI : s.asIdeal.IsPrime := s.isPrime
  haveI : s.asIdeal.IsMaximal := by rw [Ideal.eq_bot_of_prime s.asIdeal]; exact Ideal.bot_isMaximal
  let c : K →+* (Sp K).residueField s :=
    (Scheme.Spec.residueFieldIso (CommRingCat.of K) s).inv.hom.comp (algebraMap K s.asIdeal.ResidueField)
  have hc : spMap c = (Sp K).fromSpecResidueField s := by
    rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField, ← Spec.map_comp]
    rfl
  have hcfin : c.Finite := by
    refine RingHom.Finite.of_surjective _ ?_
    refine (Scheme.Spec.residueFieldIso (CommRingCat.of K) s).commRingCatIsoToRingEquiv.symm.surjective.comp ?_
    have hq : Function.Surjective (Ideal.Quotient.mk s.asIdeal) := Ideal.Quotient.mk_surjective
    have hb := Ideal.bijective_algebraMap_quotient_residueField s.asIdeal
    have e : (algebraMap K s.asIdeal.ResidueField) = (algebraMap (K ⧸ s.asIdeal) s.asIdeal.ResidueField).comp (Ideal.Quotient.mk s.asIdeal) := by
      ext a; rfl
    rw [e]
    exact hb.2.comp hq
  let io : K →+* X.residueField w := (p.residueFieldMap w).hom.comp c
  have hio : io.Finite := (GlobalTheory.residueFieldMap_finite_of_locallyQuasiFinite p w).comp hcfin
  have hsio : spMap io = X.fromSpecResidueField w ≫ p := by
    rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← hc, ← Spec.map_comp]
    rfl

  have hu : X.fromSpecResidueField w ≫ p = spMap io := hsio.symm
  let u : Over.mk (spMap io) ⟶ torsion A.A 2 := Over.homMk (X.fromSpecResidueField w) hu
  let y : Over.mk (spMap io) ⟶ A.A := u ≫ torsion.ι A.A 2
  have hy : y * y = 1 := by
    have e1 : y * y = y ≫ mulN A.A 2 := by
      rw [GlobalTheory.GrpTangent.mulN_eq_pow, MonObj.comp_pow, Category.comp_id, sq]
    have e2 : torsion.ι A.A 2 ≫ mulN A.A 2 = pullback.snd (mulN A.A 2) η[A.A] ≫ η[A.A] :=
      pullback.condition
    rw [e1, Category.assoc, e2]
    show (u ≫ pullback.snd (mulN A.A 2) η[A.A]) ≫ η[A.A] = toUnit _ ≫ η[A.A]
    rw [toUnit_unique (u ≫ pullback.snd (mulN A.A 2) η[A.A]) (toUnit _)]
  have hlo : Spec.map φ ≫ X.fromSpecResidueField w ≫ p = spMap ga := by
    rw [← Category.assoc, htl]
    exact Over.w t
  refine ⟨X.residueField w, inferInstance, io, φ.hom, y, hio, ?_, hy, ?_⟩
  · have e : spMap (φ.hom.comp io) = spMap ga := by
      rw [← hlo, ← hsio]
      show _ = Spec.map φ ≫ Spec.map (CommRingCat.ofHom io)
      erw [← Spec.map_comp]
      rfl
    have e' := Spec.map_inj.mp e
    exact congrArg CommRingCat.Hom.hom e'
  · show Spec.map (CommRingCat.ofHom φ.hom) ≫ (X.fromSpecResidueField w ≫ (torsion.ι A.A 2).left) = x.left ≫ α
    rw [CommRingCat.ofHom_hom, ← Category.assoc, htl, ← hzl, ← ht]
    rfl

end GlobalTheory.TwoTorsionDescent
