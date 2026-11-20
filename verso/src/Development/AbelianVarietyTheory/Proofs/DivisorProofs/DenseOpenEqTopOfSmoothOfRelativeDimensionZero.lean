import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory

/- English proof (translation)
Introduce `k _ Y p hp U hU`. Establish `he : Etale p` using `(Etale.iff_smoothOfRelativeDimension_zero p).2 hp`. Establish `hq : LocallyQuasiFinite p`. Use `⟨fun {V} hV {W} hW e ↦ ?_⟩` and prove the remaining obligations. Establish `h` using `p.etale_appLE hV hW e`.

Use `letI := (p.appLE V W e).hom.toAlgebra`. Establish `: Algebra.Etale Γ(Sp k, V) Γ(Y, W)` using `h`. Conclude with `(inferInstance : Algebra.QuasiFinite Γ(Sp k, V) Γ(Y, W))`. Establish `hsub : Subsingleton (Sp k)` using `inferInstanceAs (Subsingleton (PrimeSpectrum k))`. Establish `hopen : ∀ y : Y, IsOpen ({y} : Set Y)`.

Introduce `y`. Establish `hd : _root_.IsDiscrete (p ⁻¹' {p y})` using `p.isDiscrete_preimage_singleton (p y)`. Establish `huniv : p ⁻¹' {p y} = Set.univ`. Use extensionality with `z`. Simplify using `[Subsingleton.elim (p z) (p y)]`.

Rewrite `hd` using `[huniv]`. Establish `: DiscreteTopology Y`. Establish `h2` using `hd.to_subtype`. Conclude with `(Homeomorph.Set.univ Y).symm.isEmbedding.discreteTopology`. Conclude with `isOpen_discrete _`.

Use `eq_top_iff.2 fun y _ ↦ ?_` and prove the remaining obligations. Take `⟨z, hz1, hz2⟩` from `hU.inter_open_nonempty {y} (hopen y) ⟨y, rfl⟩`. Rewrite `hz1` using `[Set.mem_singleton_iff]`. Substitute `hz1` using the available equality. Conclude with `hz2`.
-/
theorem dense_open_eq_top_of_smoothOfRelativeDimension_zero : ∀ (k : Type) [Field k] (Y : Scheme.{0}) (p : Y ⟶ Sp k), SmoothOfRelativeDimension 0 p → ∀ (U : Y.Opens), Dense (U : Set Y) → U = ⊤ := by
  intro k _ Y p hp U hU
  have he : Etale p := (Etale.iff_smoothOfRelativeDimension_zero p).2 hp
  have hq : LocallyQuasiFinite p := by
    refine ⟨fun {V} hV {W} hW e ↦ ?_⟩
    have h := p.etale_appLE hV hW e
    letI := (p.appLE V W e).hom.toAlgebra
    have : Algebra.Etale Γ(Sp k, V) Γ(Y, W) := h
    exact (inferInstance : Algebra.QuasiFinite Γ(Sp k, V) Γ(Y, W))
  have hsub : Subsingleton (Sp k) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  have hopen : ∀ y : Y, IsOpen ({y} : Set Y) := by
    intro y
    have hd : _root_.IsDiscrete (p ⁻¹' {p y}) := p.isDiscrete_preimage_singleton (p y)
    have huniv : p ⁻¹' {p y} = Set.univ := by
      ext z; simp [Subsingleton.elim (p z) (p y)]
    rw [huniv] at hd
    have : DiscreteTopology Y := by
      have h2 := hd.to_subtype
      exact (Homeomorph.Set.univ Y).symm.isEmbedding.discreteTopology
    exact isOpen_discrete _
  refine eq_top_iff.2 fun y _ ↦ ?_
  obtain ⟨z, hz1, hz2⟩ := hU.inter_open_nonempty {y} (hopen y) ⟨y, rfl⟩
  rw [Set.mem_singleton_iff] at hz1
  subst hz1
  exact hz2

end GlobalTheory
