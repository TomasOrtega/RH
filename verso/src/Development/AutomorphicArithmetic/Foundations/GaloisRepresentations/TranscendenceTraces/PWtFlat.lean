import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
Introduce `hC hS hB hO Z S p _ _ _`. Use `hC p (mult p) fun A W hW => ?_` and prove the remaining obligations. Establish `: IsFinite A.r` using `A.finite`. Establish `: Flat A.r` using `MorphismProperty.of_isPullback A.pb ‹_›`. Establish `: LocallyOfFinitePresentation A.r` using `MorphismProperty.of_isPullback A.pb ‹_›`.

Set `O : A.V.Opens` to `⟨W, hW.isOpen⟩`. Establish `: IsClosedImmersion O.ι` using `IsClosedImmersion.of_isPreimmersion O.ι (by rw [O.range_ι]; exact hW.isClosed)`. Establish `hm : mult (O.ι ≫ A.r) = (mult A.r).comap O.ι` using `hO O.ι A.r`. Establish `hm' : mult A.r = (mult p).comap A.v` using `hB A.v A.r p A.u A.pb`. Use `⟨fun u => (((O.ι ≫ A.r).finrank u : ℕ) : ℤ), ?_, ?_⟩` and prove the remaining obligations.

Conclude with `(Scheme.Hom.isLocallyConstant_finrank (O.ι ≫ A.r)).comp _`. Introduce `Ω _ _ x`. Establish `h1` using `hS (O.ι ≫ A.r) Ω x`. Use `h1.symm.trans ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `∑ᶠ z ∈ fib (O.ι ≫ A.r) x, mult (O.ι ≫ A.r) Ω z = _`.

Use `finsum_mem_eq_of_bijOn (fun z => z ≫ O.ι) ⟨?_, ?_, ?_⟩ ?_` and prove the remaining obligations. Introduce `z hz`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(z ≫ O.ι) ≫ A.r = x`. Rewrite using `[Category.assoc]`.

Conclude with `hz`. Express the relevant statement in the definitionally equal form `pt (z ≫ O.ι) ∈ W`. Rewrite using `[pt_comp]`. Conclude with `(pt z).2`. Introduce `z _ z' _ e`.

Conclude with `(cancel_mono O.ι).1 e`. Introduce and unpack `z ⟨hz, hzW⟩`. Establish `hr : Set.range z ⊆ Set.range O.ι`. Rewrite using `[O.range_ι]`. Introduce and unpack `_ ⟨t, rfl⟩`.

Rewrite using `[pt_eq]`. Conclude with `hzW`. Use `⟨IsOpenImmersion.lift O.ι z hr, ?_, IsOpenImmersion.lift_fac _ _ _⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ ≫ O.ι ≫ A.r = x`. Rewrite using `[← Category.assoc, IsOpenImmersion.lift_fac]`.

Conclude with `hz`. Introduce `z _`. Rewrite using `[hm, hm']`. Simplify using `[Wt.comap]`.
-/
theorem UpperTheory.Gal.TranscendenceTraces.wtFlat_of :
    WtClopen → MultSum → MultBC → MultOpen → WtFlat := by
  intro hC hS hB hO Z S p _ _ _
  refine hC p (mult p) fun A W hW => ?_
  have : IsFinite A.r := A.finite
  have : Flat A.r := MorphismProperty.of_isPullback A.pb ‹_›
  have : LocallyOfFinitePresentation A.r := MorphismProperty.of_isPullback A.pb ‹_›
  let O : A.V.Opens := ⟨W, hW.isOpen⟩
  have : IsClosedImmersion O.ι :=
    IsClosedImmersion.of_isPreimmersion O.ι (by rw [O.range_ι]; exact hW.isClosed)
  have hm : mult (O.ι ≫ A.r) = (mult A.r).comap O.ι := hO O.ι A.r
  have hm' : mult A.r = (mult p).comap A.v := hB A.v A.r p A.u A.pb
  refine ⟨fun u => (((O.ι ≫ A.r).finrank u : ℕ) : ℤ), ?_, ?_⟩
  · exact (Scheme.Hom.isLocallyConstant_finrank (O.ι ≫ A.r)).comp _
  · intro Ω _ _ x
    have h1 := hS (O.ι ≫ A.r) Ω x
    refine h1.symm.trans ?_
    change ∑ᶠ z ∈ fib (O.ι ≫ A.r) x, mult (O.ι ≫ A.r) Ω z = _
    refine finsum_mem_eq_of_bijOn (fun z => z ≫ O.ι) ⟨?_, ?_, ?_⟩ ?_
    · intro z hz
      refine ⟨?_, ?_⟩
      · change (z ≫ O.ι) ≫ A.r = x
        rw [Category.assoc]; exact hz
      · change pt (z ≫ O.ι) ∈ W
        rw [pt_comp]; exact (pt z).2
    · intro z _ z' _ e
      exact (cancel_mono O.ι).1 e
    · rintro z ⟨hz, hzW⟩
      have hr : Set.range z ⊆ Set.range O.ι := by
        rw [O.range_ι]
        rintro _ ⟨t, rfl⟩
        rw [pt_eq]; exact hzW
      refine ⟨IsOpenImmersion.lift O.ι z hr, ?_, IsOpenImmersion.lift_fac _ _ _⟩
      change _ ≫ O.ι ≫ A.r = x
      rw [← Category.assoc, IsOpenImmersion.lift_fac]; exact hz
    · intro z _
      rw [hm, hm']
      simp [Wt.comap]
