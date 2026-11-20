import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.MeasDefs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.RatVMemSpan
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension

noncomputable section

namespace PI.LevelKSplit.W.Meas

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.LevelKSplit
  PI.LevelKSplit.W.Glob
open scoped TensorProduct

/- English proof (translation)
The claim follows from `(Module.finBasis ℚ K).equivFun.injective.countable`.
-/
theorem countable_nf (K : Type) [Field K] [NumberField K] : Countable K :=
  (Module.finBasis ℚ K).equivFun.injective.countable

/- English proof (translation)
Introduce `F _ _`. Use `haveI : Countable F := countable_nf F`. Use `haveI : Countable (𝓞 F) := (IsFractionRing.injective (𝓞 F) F).countable`. Establish `hs : Function.Surjective (fun s : Finset (𝓞 F) => Ideal.span (s : Set (𝓞 F)))`. Introduce `I`.

Take `⟨s, hs⟩` from `IsNoetherian.noetherian I`. Conclude with `⟨s, hs⟩`. Use `haveI : Countable (Ideal (𝓞 F)) := hs.countable`. Establish `hinj : Function.Injective (fun P : HeightOneSpectrum (𝓞 F) => P.asIdeal)` using `fun P Q h => HeightOneSpectrum.ext h`. Conclude with `hinj.countable`.
-/
theorem places_countable : PlacesCountable := by
  intro F _ _
  haveI : Countable F := countable_nf F
  haveI : Countable (𝓞 F) := (IsFractionRing.injective (𝓞 F) F).countable
  have hs : Function.Surjective (fun s : Finset (𝓞 F) => Ideal.span (s : Set (𝓞 F))) := by
    intro I
    obtain ⟨s, hs⟩ := IsNoetherian.noetherian I
    exact ⟨s, hs⟩
  haveI : Countable (Ideal (𝓞 F)) := hs.countable
  have hinj : Function.Injective (fun P : HeightOneSpectrum (𝓞 F) => P.asIdeal) :=
    fun P Q h => HeightOneSpectrum.ext h
  exact hinj.countable

/- English proof (translation)
Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact hG y hy`. Consider the case `zero => rw [Matrix.mulVec_zero]`. Conclude with `Submodule.zero_mem _`.

Consider the case `add a b _ _ ha hb => rw [Matrix.mulVec_add]`. Conclude with `Submodule.add_mem _ ha hb`. Consider the case `smul c a _ ha => rw [Matrix.mulVec_smul]`. Conclude with `Submodule.smul_mem _ c ha`.
-/
private theorem mulVec_mem_span_of_mulVec_generators_mem {O B : Type} [CommRing O] [CommRing B] [Algebra O B] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) B) (G : Set (Fin n → B))
    (hG : ∀ y ∈ G, A.mulVec y ∈ Submodule.span O G) :
    ∀ x ∈ Submodule.span O G, A.mulVec x ∈ Submodule.span O G := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact hG y hy
  | zero => rw [Matrix.mulVec_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [Matrix.mulVec_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ c ha

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h y hy`. Establish `hyS : y ∈ Submodule.span O G` using `Submodule.subset_span hy`. Use `⟨(h y).1 hyS, ?_⟩` and prove the remaining obligations. Rewrite using `[h (C.mulVec y), hAC y]`.

Conclude with `hyS`. Introduce `h x`. Prove the components needed by the constructor for the conclusion. Conclude with `fun hx => mulVec_mem_span_of_mulVec_generators_mem A G (fun y hy => (h y hy).1) x hx`. Introduce `hx`.

Establish `hC` using `mulVec_mem_span_of_mulVec_generators_mem C G (fun y hy => (h y hy).2) _ hx`. Rewrite `hC` using `[hCA x]`. Then use the resulting hypothesis.
-/
theorem stab_iff {O B : Type} [CommRing O] [CommRing B] [Algebra O B] {n : ℕ}
    (A C : Matrix (Fin n) (Fin n) B) (hCA : ∀ x, C.mulVec (A.mulVec x) = x)
    (hAC : ∀ x, A.mulVec (C.mulVec x) = x) (G : Set (Fin n → B)) :
    (∀ x, x ∈ Submodule.span O G ↔ A.mulVec x ∈ Submodule.span O G) ↔
      ∀ y ∈ G, A.mulVec y ∈ Submodule.span O G ∧ C.mulVec y ∈ Submodule.span O G := by
  constructor
  · intro h y hy
    have hyS : y ∈ Submodule.span O G := Submodule.subset_span hy
    refine ⟨(h y).1 hyS, ?_⟩
    rw [h (C.mulVec y), hAC y]
    exact hyS
  · intro h x
    constructor
    · exact fun hx => mulVec_mem_span_of_mulVec_generators_mem A G (fun y hy => (h y hy).1) x hx
    · intro hx
      have hC := mulVec_mem_span_of_mulVec_generators_mem C G (fun y hy => (h y hy).2) _ hx
      rwa [hCA x] at hC

/- English proof (translation)
Rewrite using `[Matrix.mulVec_mulVec, map_inv, map_inv, Units.inv_mul, Matrix.one_mulVec]`.
-/
theorem compV_inv_mulVec {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (v : HeightOneSpectrum (𝓞 F))
    (g : HA (Af F) σ J) (x : Fin n → Fv F v ⊗[F] E) :
    Matrix.mulVec ((compV v (incAf σ J g⁻¹) : GL (Fin n) (Fv F v ⊗[F] E)) :
      Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))
      (Matrix.mulVec ((compV v (incAf σ J g) : GL (Fin n) (Fv F v ⊗[F] E)) :
        Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) x) = x := by
  rw [Matrix.mulVec_mulVec, map_inv, map_inv, Units.inv_mul, Matrix.one_mulVec]

/- English proof (translation)
Rewrite using `[Matrix.mulVec_mulVec, map_inv, map_inv, Units.mul_inv, Matrix.one_mulVec]`.
-/
theorem compV_mulVec_inv {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (v : HeightOneSpectrum (𝓞 F))
    (g : HA (Af F) σ J) (x : Fin n → Fv F v ⊗[F] E) :
    Matrix.mulVec ((compV v (incAf σ J g) : GL (Fin n) (Fv F v ⊗[F] E)) :
      Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))
      (Matrix.mulVec ((compV v (incAf σ J g⁻¹) : GL (Fin n) (Fv F v ⊗[F] E)) :
        Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) x) = x := by
  rw [Matrix.mulVec_mulVec, map_inv, map_inv, Units.mul_inv, Matrix.one_mulVec]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ _ M J _ Λ`. Use `haveI : Countable (HeightOneSpectrum (𝓞 F)) := places_countable F`. Use `haveI : Countable E := countable_nf E`. Unfold `Kf`. Rewrite using `[Subgroup.coe_iInf]`.

Use `MeasurableSet.iInter fun v => ?_` and prove the remaining obligations. Set `Mf : HA (Af F) σ J → Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)` to `fun g => ((compV v (incAf σ J g) : GL (Fin M) (Fv F v ⊗[F] E)) : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E))`. Set `G : Set (Fin M → Fv F v ⊗[F] E)` to `ratV (F := F) (Fv F v) '' Λ`. Establish `hG : G.Countable` using `(Set.to_countable Λ).image _`. Establish `hset : ((Subgroup.comap ((compV v).comp (incAf σ J)) (Kloc v Λ) : Subgroup (HA (Af F) σ J)) : Set (HA (Af F) σ J)) = ⋂ y ∈ G, ((fun g => (Mf g).mulVec y) ⁻¹' (latLoc (E` using `E) v Λ : Set _) ∩ (fun g => (Mf g⁻¹).mulVec y) ⁻¹' (latLoc (E := E) v Λ : Set _)) := by`.

Use extensionality with `g`. Simplify using `only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe]`. Express the relevant statement in the definitionally equal form `(∀ x, x ∈ latLoc (E := E) v Λ ↔ (Mf g).mulVec x ∈ latLoc (E := E) v Λ) ↔ _`. Conclude with `stab_iff (Mf g) (Mf g⁻¹) (compV_inv_mulVec v g) (compV_mulVec_inv v g) G`. Rewrite using `[hset]`.

Use `MeasurableSet.biInter hG fun y _ => ?_` and prove the remaining obligations. Use `letI : MeasurableSpace (Fin M → Fv F v ⊗[F] E) := borel _`. Use `haveI : BorelSpace (Fin M → Fv F v ⊗[F] E) := ⟨rfl⟩`. Establish `hc : Continuous (fun g => (Mf g).mulVec y)` using `(h2 F E σ M J v).matrix_mulVec continuous_const`. Use `MeasurableSet.inter (hc.measurable (h3 F E M v Λ)) ?_` and prove the remaining obligations.

Establish `hc' : Continuous (fun g => (Mf g⁻¹).mulVec y)` using `((h2 F E σ M J v).comp continuous_inv).matrix_mulVec continuous_const`. Conclude with `hc'.measurable (h3 F E M v Λ)`.
-/
theorem measKf_of (h2 : ContPlace) (h3 : LatBorel) : MeasKfAll := by
  intro F E _ _ _ _ _ σ _ M J _ Λ
  haveI : Countable (HeightOneSpectrum (𝓞 F)) := places_countable F
  haveI : Countable E := countable_nf E
  unfold Kf
  rw [Subgroup.coe_iInf]
  refine MeasurableSet.iInter fun v => ?_
  let Mf : HA (Af F) σ J → Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E) := fun g =>
    ((compV v (incAf σ J g) : GL (Fin M) (Fv F v ⊗[F] E)) : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E))
  let G : Set (Fin M → Fv F v ⊗[F] E) := ratV (F := F) (Fv F v) '' Λ
  have hG : G.Countable := (Set.to_countable Λ).image _
  have hset : ((Subgroup.comap ((compV v).comp (incAf σ J)) (Kloc v Λ) : Subgroup (HA (Af F) σ J)) :
      Set (HA (Af F) σ J)) = ⋂ y ∈ G, ((fun g => (Mf g).mulVec y) ⁻¹' (latLoc (E := E) v Λ : Set _) ∩
        (fun g => (Mf g⁻¹).mulVec y) ⁻¹' (latLoc (E := E) v Λ : Set _)) := by
    ext g
    simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe]
    change (∀ x, x ∈ latLoc (E := E) v Λ ↔ (Mf g).mulVec x ∈ latLoc (E := E) v Λ) ↔ _
    exact stab_iff (Mf g) (Mf g⁻¹) (compV_inv_mulVec v g) (compV_mulVec_inv v g) G
  rw [hset]
  refine MeasurableSet.biInter hG fun y _ => ?_
  letI : MeasurableSpace (Fin M → Fv F v ⊗[F] E) := borel _
  haveI : BorelSpace (Fin M → Fv F v ⊗[F] E) := ⟨rfl⟩
  have hc : Continuous (fun g => (Mf g).mulVec y) :=
    (h2 F E σ M J v).matrix_mulVec continuous_const
  refine MeasurableSet.inter (hc.measurable (h3 F E M v Λ)) ?_
  have hc' : Continuous (fun g => (Mf g⁻¹).mulVec y) :=
    ((h2 F E σ M J v).comp continuous_inv).matrix_mulVec continuous_const
  exact hc'.measurable (h3 F E M v Λ)

end PI.LevelKSplit.W.Meas
