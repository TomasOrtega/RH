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
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Introduce a local definition for the expression. Introduce a local definition for the expression.

Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify to obtain the desired conclusion from the available facts.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
