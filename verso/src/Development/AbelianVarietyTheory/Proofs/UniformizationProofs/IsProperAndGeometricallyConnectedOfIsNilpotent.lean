import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.NilProper

/- English proof (translation)
Set `m` to `pullback.map (j ≫ f) (j ≫ f) f f j j (𝟙 S) (by simp) (by simp)`. Establish `hm : UniversallyClosed m` using `MorphismProperty.pullbackMap (P := @UniversallyClosed) ‹_› ‹_› rfl rfl`. Establish `hcomm : pullback.diagonal (j ≫ f) ≫ m = j ≫ pullback.diagonal f`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, pullback.lift_fst, pullback.diagonal_fst_assoc]`.

Simplify using the standard rewrite rules. Rewrite using `[Category.assoc, pullback.lift_snd, pullback.diagonal_snd_assoc]`. Simplify using the standard rewrite rules. Establish `key : m '' Set.range (pullback.diagonal (j ≫ f)) = Set.range (pullback.diagonal f)`. Use extensionality with `z`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨x, rfl⟩, rfl⟩`. Conclude with `⟨j x, by rw [← Scheme.Hom.comp_apply, ← hcomm, Scheme.Hom.comp_apply]⟩`. Introduce and unpack `⟨y, rfl⟩`. Take `⟨x, rfl⟩` from `j.surjective y`.

Conclude with `⟨_, ⟨x, rfl⟩, by rw [← Scheme.Hom.comp_apply, hcomm, Scheme.Hom.comp_apply]⟩`. Use `⟨IsClosedImmersion.of_isPreimmersion _ ?_⟩` and prove the remaining obligations. Rewrite using `[← key]`. Conclude with `m.isClosedMap _ (pullback.diagonal (j ≫ f)).isClosedEmbedding.isClosed_range`.
-/
theorem isSeparated_of_comp_surjective {X Y S : Scheme.{0}} (j : X ⟶ Y) (f : Y ⟶ S)
    [Surjective j] [UniversallyClosed j] [IsSeparated (j ≫ f)] : IsSeparated f := by
  let m := pullback.map (j ≫ f) (j ≫ f) f f j j (𝟙 S) (by simp) (by simp)
  have hm : UniversallyClosed m :=
    MorphismProperty.pullbackMap (P := @UniversallyClosed) ‹_› ‹_› rfl rfl
  have hcomm : pullback.diagonal (j ≫ f) ≫ m = j ≫ pullback.diagonal f := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.diagonal_fst_assoc]
      simp
    · rw [Category.assoc, pullback.lift_snd, pullback.diagonal_snd_assoc]
      simp
  have key : m '' Set.range (pullback.diagonal (j ≫ f)) = Set.range (pullback.diagonal f) := by
    ext z
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨j x, by rw [← Scheme.Hom.comp_apply, ← hcomm, Scheme.Hom.comp_apply]⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨x, rfl⟩ := j.surjective y
      exact ⟨_, ⟨x, rfl⟩, by rw [← Scheme.Hom.comp_apply, hcomm, Scheme.Hom.comp_apply]⟩
  refine ⟨IsClosedImmersion.of_isPreimmersion _ ?_⟩
  rw [← key]
  exact m.isClosedMap _ (pullback.diagonal (j ≫ f)).isClosedEmbedding.isClosed_range

/- English proof (translation)
Take `⟨n, hn⟩` from `hJ`. Establish `hle : J ≤ nilradical A` using `fun x hx ↦ by`. Rewrite using `[mem_nilradical]`. Use `⟨n, ?_⟩` and prove the remaining obligations. Use `Ideal.pow_mem_pow hx n` as an intermediate fact.

Rewrite `this` using `[hn, Ideal.zero_eq_bot, Ideal.mem_bot]`. Then use the resulting hypothesis. Conclude with `⟨(PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical hle).2⟩`.
-/
theorem surjective_specMap_mk (A : Type) [CommRing A] (J : Ideal A) (hJ : IsNilpotent J) :
    Surjective (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) := by
  obtain ⟨n, hn⟩ := hJ
  have hle : J ≤ nilradical A := fun x hx ↦ by
    rw [mem_nilradical]
    refine ⟨n, ?_⟩
    have := Ideal.pow_mem_pow hx n
    rwa [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at this
  exact ⟨(PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical hle).2⟩

/- English proof (translation)
Introduce `A _ J hJ Y _`. Establish `hsq : Surjective (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))` using `surjective_specMap_mk A J hJ`. Establish `hci : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))` using `IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective`. Use `⟨fun hP ↦ ?_, fun hG ↦ ?_⟩` and prove the remaining obligations. Establish `hcomp : IsProper (pullback.fst Y.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) ≫ Y.hom)`.

Rewrite using `[pullback.condition]`. Use `infer_instance`. Establish `: IsSeparated Y.hom` using `isSeparated_of_comp_surjective (pullback.fst Y.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) Y.hom`. Establish `: UniversallyClosed Y.hom` using `UniversallyClosed.of_comp_surjective (pullback.fst Y.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) Y.hom`. Conclude with `{ toIsSeparated := ‹_›, toUniversallyClosed := ‹_›, toLocallyOfFiniteType := ‹_› }`.

Rewrite `hG`, the goal using `[geometricallyConnected_iff]`. Introduce `K _ y Z fst snd h`. Take `⟨φ, rfl⟩` from `Spec.map_surjective y`. Establish `hker : ∀ x ∈ J, φ.hom x = 0`. Take `⟨n, hn⟩` from `hJ`.

Introduce `x hx`. Establish `hx' : x ^ n = 0`. Use `Ideal.pow_mem_pow hx n` as an intermediate fact. Rewrite `this` using `[hn, Ideal.zero_eq_bot, Ideal.mem_bot]`. Then use the resulting hypothesis. Conclude with `(IsNilpotent.map ⟨n, hx'⟩ φ.hom).eq_zero`.

Set `ψ` to `Ideal.Quotient.lift J φ.hom hker`. Establish `hφ : φ = CommRingCat.ofHom (Ideal.Quotient.mk J) ≫ CommRingCat.ofHom ψ`. Use extensionality with `x`. Simplify using `[ψ]`. Rewrite `h` using `[hφ, Spec.map_comp]`.

Set `p : Z ⟶ pullback Y.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))` to `pullback.lift fst (snd ≫ Spec.map (CommRingCat.ofHom ψ)) (by rw [h.w, Category.assoc])`. Apply `hG (Spec.map (CommRingCat.ofHom ψ)) p snd` to reduce the goal to its premises. Establish `e : p ≫ pullback.fst Y.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) = fst` using `pullback.lift_fst _ _ _`. Use `IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)` and prove the remaining obligations. Rewrite using `[e]`.

Conclude with `h`.
-/
theorem isProper_and_geometricallyConnected_of_isNilpotent :
    ∀ (A : Type) [CommRing A] (J : Ideal A), IsNilpotent J → ∀ (Y : Over (Spec (CommRingCat.of A))) [LocallyOfFiniteType Y.hom], (IsProper (pullback.snd Y.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) → IsProper Y.hom) ∧ (GeometricallyConnected (pullback.snd Y.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) → GeometricallyConnected Y.hom) := by
  intro A _ J hJ Y _
  have hsq : Surjective (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
    surjective_specMap_mk A J hJ
  have hci : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  refine ⟨fun hP ↦ ?_, fun hG ↦ ?_⟩
  · have hcomp : IsProper (pullback.fst Y.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))
        ≫ Y.hom) := by
      rw [pullback.condition]
      infer_instance
    have : IsSeparated Y.hom :=
      isSeparated_of_comp_surjective (pullback.fst Y.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) Y.hom
    have : UniversallyClosed Y.hom :=
      UniversallyClosed.of_comp_surjective (pullback.fst Y.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) Y.hom
    exact { toIsSeparated := ‹_›, toUniversallyClosed := ‹_›, toLocallyOfFiniteType := ‹_› }
  · rw [geometricallyConnected_iff] at hG ⊢
    intro K _ y Z fst snd h
    obtain ⟨φ, rfl⟩ := Spec.map_surjective y
    have hker : ∀ x ∈ J, φ.hom x = 0 := by
      obtain ⟨n, hn⟩ := hJ
      intro x hx
      have hx' : x ^ n = 0 := by
        have := Ideal.pow_mem_pow hx n
        rwa [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at this
      exact (IsNilpotent.map ⟨n, hx'⟩ φ.hom).eq_zero
    let ψ := Ideal.Quotient.lift J φ.hom hker
    have hφ : φ = CommRingCat.ofHom (Ideal.Quotient.mk J) ≫ CommRingCat.ofHom ψ := by
      ext x
      simp [ψ]
    rw [hφ, Spec.map_comp] at h
    let p : Z ⟶ pullback Y.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
      pullback.lift fst (snd ≫ Spec.map (CommRingCat.ofHom ψ)) (by rw [h.w, Category.assoc])
    apply hG (Spec.map (CommRingCat.ofHom ψ)) p snd
    have e : p ≫ pullback.fst Y.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) = fst :=
      pullback.lift_fst _ _ _
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
    rw [e]
    exact h

end GlobalTheory.NilProper
