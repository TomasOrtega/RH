import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetric
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumLifts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeOfIsOpenImmersion
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm

namespace GlobalTheory.CoverDeg

/- English proof (translation)
Establish `hs : Function.Surjective (f.residueFieldMap x).hom`. Introduce `y`. Take `⟨s, rfl⟩` from `Scheme.residue_surjective X x y`. Take `⟨t, rfl⟩` from `SurjectiveOnStalks.stalkMap_surjective (f := f) x s`. Conclude with `⟨Y.residue (f x) t, rfl⟩`.

Use `letI : Algebra (Y.residueField (f x)) (X.residueField x) := (f.residueFieldMap x).hom.toAlgebra`. Establish `hb : Function.Bijective (algebraMap (Y.residueField (f x)) (X.residueField x))` using `⟨RingHom.injective (algebraMap (Y.residueField (f x)) (X.residueField x)), hs⟩`. Establish `e` using `(AlgEquiv.ofBijective (Algebra.ofId (Y.residueField (f x)) (X.residueField x)) hb).toLinearEquiv`. Unfold `Scheme.Hom.residueDegree`. Rewrite using `[← e.finrank_eq, Module.finrank_self]`.
-/
theorem residueDegree_eq_one_of_surjectiveOnStalks {X Y : Scheme} (f : X ⟶ Y) [SurjectiveOnStalks f]
    (x : X) : f.residueDegree x = 1 := by
  have hs : Function.Surjective (f.residueFieldMap x).hom := by
    intro y
    obtain ⟨s, rfl⟩ := Scheme.residue_surjective X x y
    obtain ⟨t, rfl⟩ := SurjectiveOnStalks.stalkMap_surjective (f := f) x s
    exact ⟨Y.residue (f x) t, rfl⟩
  letI : Algebra (Y.residueField (f x)) (X.residueField x) := (f.residueFieldMap x).hom.toAlgebra
  have hb : Function.Bijective (algebraMap (Y.residueField (f x)) (X.residueField x)) :=
    ⟨RingHom.injective (algebraMap (Y.residueField (f x)) (X.residueField x)), hs⟩
  have e := (AlgEquiv.ofBijective (Algebra.ofId (Y.residueField (f x)) (X.residueField x)) hb).toLinearEquiv
  unfold Scheme.Hom.residueDegree
  rw [← e.finrank_eq, Module.finrank_self]

end GlobalTheory.CoverDeg

namespace GlobalTheory.CoverDeg

/- English proof (translation)
Use `haveI := V.int`. Use `haveI := V.intG`. Set `η : Sp F` to `⟨⊥, Ideal.bot_prime⟩`. Establish `hη : ∀ w : Sp F, (spMap (algebraMap (𝓞 F) F) w).asIdeal = ⊥`. Introduce `w`.

Establish `hw : w.asIdeal = ⊥`. Break down `Ideal.eq_bot_or_top w.asIdeal with h | h` into its components or cases. Conclude with `h`. Conclude with `absurd h w.isPrime.ne_top`. Express the relevant statement in the definitionally equal form `Ideal.comap _ w.asIdeal = ⊥`.

Rewrite using `[hw, ← RingHom.ker_eq_comap_bot]`. Conclude with `(RingHom.injective_iff_ker_eq_bot _).mp (NumberField.RingOfIntegers.coe_injective)`. Establish `hw` using `V.pb.w`. Establish `hpj : ∀ z : V.G, (V.p (V.j z)).asIdeal = ⊥`. Introduce `z`.

Establish `: V.p (V.j z) = spMap (algebraMap (𝓞 F) F) ((V.π ≫ Y.str) z)`. Rewrite using `[← Scheme.Hom.comp_apply, hw, Scheme.Hom.comp_apply]`. Rewrite using `[this, hη]`. Establish `hpX : V.p (genericPoint V.X) = spMap (algebraMap (𝓞 F) F) η`. Apply `PrimeSpectrum.ext` to reduce the goal to its premises.

Rewrite using `[hη]`. Establish `hs : genericPoint V.X ⤳ V.j (genericPoint V.G)` using `genericPoint_specializes _`. Use `(PrimeSpectrum.le_iff_specializes _ _).mpr (hs.map V.p.continuous)` as an intermediate fact. Conclude with `le_bot_iff.mp ((hpj _) ▸ this)`. Choose the witnesses or unpack the hypotheses as in `⟨w, hw'⟩ : genericPoint V.X ∈ Set.range (Limits.pullback.fst V.p (spMap (algebraMap (𝓞 F) F))) := by`.

Rewrite using `[Scheme.Pullback.range_fst]`. Conclude with `⟨η, hpX.symm⟩`. Establish `hz : V.j (V.pb.isoPullback.inv w) = genericPoint V.X`. Establish `e : V.pb.isoPullback.inv ≫ V.j = Limits.pullback.fst V.p (spMap (algebraMap (𝓞 F) F))`. Rewrite using `[Iso.inv_comp_eq, V.pb.isoPullback_hom_fst]`.

Rewrite using `[← hw', ← e, Scheme.Hom.comp_apply]`. Establish `h1 : V.j (genericPoint V.G) ⤳ genericPoint V.X`. Rewrite using `[← hz]`. Conclude with `(genericPoint_specializes _).map V.j.continuous`. Conclude with `(h1.antisymm (genericPoint_specializes _)).eq`.
-/
theorem j_genericPoint {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y) :
    V.j (genericPoint V.G) = genericPoint V.X := by
  haveI := V.int
  haveI := V.intG

  let η : Sp F := ⟨⊥, Ideal.bot_prime⟩
  have hη : ∀ w : Sp F, (spMap (algebraMap (𝓞 F) F) w).asIdeal = ⊥ := by
    intro w
    have hw : w.asIdeal = ⊥ := by
      rcases Ideal.eq_bot_or_top w.asIdeal with h | h
      · exact h
      · exact absurd h w.isPrime.ne_top
    change Ideal.comap _ w.asIdeal = ⊥
    rw [hw, ← RingHom.ker_eq_comap_bot]
    exact (RingHom.injective_iff_ker_eq_bot _).mp (NumberField.RingOfIntegers.coe_injective)
  have hw := V.pb.w
  have hpj : ∀ z : V.G, (V.p (V.j z)).asIdeal = ⊥ := by
    intro z
    have : V.p (V.j z) = spMap (algebraMap (𝓞 F) F) ((V.π ≫ Y.str) z) := by
      rw [← Scheme.Hom.comp_apply, hw, Scheme.Hom.comp_apply]
    rw [this, hη]
  have hpX : V.p (genericPoint V.X) = spMap (algebraMap (𝓞 F) F) η := by
    apply PrimeSpectrum.ext
    rw [hη]
    have hs : genericPoint V.X ⤳ V.j (genericPoint V.G) := genericPoint_specializes _
    have := (PrimeSpectrum.le_iff_specializes _ _).mpr (hs.map V.p.continuous)
    exact le_bot_iff.mp ((hpj _) ▸ this)
  obtain ⟨w, hw'⟩ : genericPoint V.X ∈ Set.range (Limits.pullback.fst V.p (spMap (algebraMap (𝓞 F) F))) := by
    rw [Scheme.Pullback.range_fst]
    exact ⟨η, hpX.symm⟩
  have hz : V.j (V.pb.isoPullback.inv w) = genericPoint V.X := by
    have e : V.pb.isoPullback.inv ≫ V.j = Limits.pullback.fst V.p (spMap (algebraMap (𝓞 F) F)) := by
      rw [Iso.inv_comp_eq, V.pb.isoPullback_hom_fst]
    rw [← hw', ← e, Scheme.Hom.comp_apply]
  have h1 : V.j (genericPoint V.G) ⤳ genericPoint V.X := by
    rw [← hz]; exact (genericPoint_specializes _).map V.j.continuous
  exact (h1.antisymm (genericPoint_specializes _)).eq

end GlobalTheory.CoverDeg

namespace GlobalTheory.CoverDeg

/- English proof (translation)
Use `haveI := CoverHt.isPreimmersion_j V`. Conclude with `residueDegree_eq_one_of_surjectiveOnStalks V.j x`.
-/
theorem j_residueDegree {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y) (x : V.G) :
    V.j.residueDegree x = 1 := by
  haveI := CoverHt.isPreimmersion_j V
  exact residueDegree_eq_one_of_surjectiveOnStalks V.j x

/- English proof (translation)
Introduce `F _ _ Y V V' b _ g hjb hπ hg`. Establish `hpt : b (genericPoint V'.X) = genericPoint V.X`. Rewrite using `[← j_genericPoint V', ← Scheme.Hom.comp_apply, hjb, Scheme.Hom.comp_apply, hg, j_genericPoint V]`. Use `⟨hpt, ?_⟩` and prove the remaining obligations. Establish `h1` using `CurveDegreesCompare.residueDegree_comp V'.j b (genericPoint V'.G)`.

Establish `h2` using `CurveDegreesCompare.residueDegree_comp g V.j (genericPoint V'.G)`. Establish `h3` using `CurveDegreesCompare.residueDegree_comp g V.π (genericPoint V'.G)`. Rewrite `h1` using `[hjb, h2]`. Rewrite `h1` using `[j_residueDegree, j_residueDegree, mul_one, one_mul, j_genericPoint V']`. Unfold `Cover.deg`.

Rewrite using `[← hπ, h3, hg, h1, mul_comm]`.
-/
theorem map_genericPoint_and_deg : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y)
    (V' : Cover Y) (b : V'.X ⟶ V.X) (hb : b ≫ V.p = V'.p) (g : V'.G ⟶ V.G),
    V'.j ≫ b = g ≫ V.j → g ≫ V.π = V'.π → g (genericPoint V'.G) = genericPoint V.G →
    b (genericPoint V'.X) = genericPoint V.X ∧ b.residueDegree (genericPoint V'.X) * V.deg = V'.deg := by
  intro F _ _ Y V V' b _ g hjb hπ hg
  have hpt : b (genericPoint V'.X) = genericPoint V.X := by
    rw [← j_genericPoint V', ← Scheme.Hom.comp_apply, hjb, Scheme.Hom.comp_apply, hg, j_genericPoint V]
  refine ⟨hpt, ?_⟩
  have h1 := CurveDegreesCompare.residueDegree_comp V'.j b (genericPoint V'.G)
  have h2 := CurveDegreesCompare.residueDegree_comp g V.j (genericPoint V'.G)
  have h3 := CurveDegreesCompare.residueDegree_comp g V.π (genericPoint V'.G)
  rw [hjb, h2] at h1
  rw [j_residueDegree, j_residueDegree, mul_one, one_mul, j_genericPoint V'] at h1
  unfold Cover.deg
  rw [← hπ, h3, hg, h1, mul_comm]

end GlobalTheory.CoverDeg
