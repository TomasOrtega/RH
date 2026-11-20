import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSectionOfIsIsoRestrict
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

namespace GlobalTheory.IntFlat

/- English proof (translation)
Introduce `X _ s x hx`. Use `HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat) (Q := RingHom.Flat)` as an intermediate fact. Use `IsZariskiLocalAtSource.of_openCover (P := @Flat) X.affineOpenCover.openCover fun i => ?_` and prove the remaining obligations. Set `R` to `X.affineOpenCover.X i`. Set `j : Spec R ⟶ X` to `X.affineOpenCover.f i`.

Establish `: IsOpenImmersion j` using `X.affineOpenCover.map_prop i`. Express the relevant statement in the definitionally equal form `Flat (j ≫ s)`. Break down `isEmpty_or_nonempty (Spec R) with h | h` into its components or cases. Use `infer_instance`. Establish `: IsIntegral (Spec R)` using `isIntegral_of_isOpenImmersion j`.

Establish `: IsDomain R` using `(affine_isIntegral_iff R).1 this`. Take `⟨φ, hφ⟩` from `Spec.map_surjective (j ≫ s)`. Set `p0 : PrimeSpectrum R` to `⟨⊥, Ideal.bot_prime⟩`. Establish `hg : genericPoint X ∈ Set.range j` using `(genericPoint_specializes (j (Classical.arbitrary (Spec R)))).mem_open j.isOpenEmbedding.isOpen_range ⟨_, rfl⟩`. Take `⟨q, hq⟩` from `hg`.

Establish `h1 : p0 ⤳ q` using `(PrimeSpectrum.le_iff_specializes _ _).1 bot_le`. Establish `h2 : j p0 ⤳ x` using `hq ▸ (h1.map j.continuous) |>.trans (genericPoint_specializes x)`. Establish `h3 : (j ≫ s) p0 ⤳ s x` using `h2.map s.continuous`. Establish `h4 : ((j ≫ s) p0).asIdeal ≤ ⊥` using `hx ▸ (PrimeSpectrum.le_iff_specializes _ _).2 h3`. Rewrite `h4` using `[← hφ]`.

Establish `hinj : Function.Injective φ.hom`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `n hn`. Establish `: n ∈ ((Spec.map φ) p0).asIdeal` using `by show n ∈ Ideal.comap φ.hom ⊥`. Simplify using `[hn]`.

Simplify using `using h4 this`. Establish `e : φ.hom = algebraMap ℤ R` using `RingHom.ext_int _ _`. Establish `: CharZero R` using `charZero_of_injective_algebraMap (e ▸ hinj)`. Rewrite using `[← hφ, HasRingHomProperty.Spec_iff (P := @Flat)]`. Rewrite using `[e, RingHom.flat_algebraMap_iff]`.

Use `infer_instance`.
-/
theorem flat_of_generic_zero : ∀ {X : Scheme.{0}} [IsIntegral X] (s : X ⟶ Spec (CommRingCat.of ℤ)) (x : X), (s x).asIdeal = ⊥ → Flat s := by
  intro X _ s x hx
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat) (Q := RingHom.Flat)
  refine IsZariskiLocalAtSource.of_openCover (P := @Flat) X.affineOpenCover.openCover fun i => ?_
  let R := X.affineOpenCover.X i
  let j : Spec R ⟶ X := X.affineOpenCover.f i
  have : IsOpenImmersion j := X.affineOpenCover.map_prop i
  change Flat (j ≫ s)
  rcases isEmpty_or_nonempty (Spec R) with h | h
  · infer_instance
  have : IsIntegral (Spec R) := isIntegral_of_isOpenImmersion j
  have : IsDomain R := (affine_isIntegral_iff R).1 this
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (j ≫ s)
  let p0 : PrimeSpectrum R := ⟨⊥, Ideal.bot_prime⟩
  have hg : genericPoint X ∈ Set.range j :=
    (genericPoint_specializes (j (Classical.arbitrary (Spec R)))).mem_open
      j.isOpenEmbedding.isOpen_range ⟨_, rfl⟩
  obtain ⟨q, hq⟩ := hg
  have h1 : p0 ⤳ q := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
  have h2 : j p0 ⤳ x := hq ▸ (h1.map j.continuous) |>.trans (genericPoint_specializes x)
  have h3 : (j ≫ s) p0 ⤳ s x := h2.map s.continuous
  have h4 : ((j ≫ s) p0).asIdeal ≤ ⊥ := hx ▸ (PrimeSpectrum.le_iff_specializes _ _).2 h3
  rw [← hφ] at h4
  have hinj : Function.Injective φ.hom := by
    rw [injective_iff_map_eq_zero]
    intro n hn
    have : n ∈ ((Spec.map φ) p0).asIdeal := by
      show n ∈ Ideal.comap φ.hom ⊥
      simp [hn]
    simpa using h4 this
  have e : φ.hom = algebraMap ℤ R := RingHom.ext_int _ _
  have : CharZero R := charZero_of_injective_algebraMap (e ▸ hinj)
  rw [← hφ, HasRingHomProperty.Spec_iff (P := @Flat)]
  rw [e, RingHom.flat_algebraMap_iff]
  infer_instance

end GlobalTheory.IntFlat
