import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsTailMore
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocReg

/- English proof (translation)
Establish `hU : IsAffineOpen U.1` using `U.2`. Use `set p := hU.primeIdealOf ⟨y, hy⟩ with hp`. Establish `hpy : hU.fromSpec p = y` using `hU.fromSpec_primeIdealOf ⟨y, hy⟩`. Establish `hle : mm ≤ p.asIdeal`. Introduce `f hf`.

Assume the negation of the conclusion as `hfp`. Apply `h f hf` to reduce the goal to its premises. Establish `h1 : p ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen f`. Rewrite using `[hU.fromSpec_preimage_basicOpen]`. Conclude with `hfp`.

Rewrite using `[← hpy]`. Conclude with `h1`. Establish `heq : mm = p.asIdeal` using `hm.eq_of_le p.isPrime.ne_top hle`. Establish `hcl : IsClosed ({p} : Set (PrimeSpectrum Γ(X, U.1)))` using `(PrimeSpectrum.isClosed_singleton_iff_isMaximal p).2 (heq ▸ hm)`. Establish `he` using `hU.fromSpec.isOpenEmbedding`.

Establish `hlc` using `IsLocallyClosed.image (f := hU.fromSpec) (s := {p}) hcl.isLocallyClosed he.isInducing he.isOpen_range.isLocallyClosed`. Establish `e : hU.fromSpec '' {p} = {y}` using `Set.image_singleton.trans (congrArg _ hpy)`. Conclude with `isClosed_singleton_of_isLocallyClosed_singleton (e ▸ hlc)`.
-/
theorem isClosed_singleton_of_maximal {X : Scheme.{0}} [JacobsonSpace X] (U : X.affineOpens)
    (mm : Ideal Γ(X, U.1)) (hm : mm.IsMaximal) (y : X) (hy : y ∈ U.1)
    (h : ∀ f ∈ mm, y ∉ X.basicOpen f) : IsClosed ({y} : Set X) := by
  have hU : IsAffineOpen U.1 := U.2
  set p := hU.primeIdealOf ⟨y, hy⟩ with hp
  have hpy : hU.fromSpec p = y := hU.fromSpec_primeIdealOf ⟨y, hy⟩
  have hle : mm ≤ p.asIdeal := by
    intro f hf
    by_contra hfp
    apply h f hf
    have h1 : p ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen f := by
      rw [hU.fromSpec_preimage_basicOpen]; exact hfp
    rw [← hpy]; exact h1
  have heq : mm = p.asIdeal := hm.eq_of_le p.isPrime.ne_top hle
  have hcl : IsClosed ({p} : Set (PrimeSpectrum Γ(X, U.1))) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal p).2 (heq ▸ hm)
  have he := hU.fromSpec.isOpenEmbedding
  have hlc := IsLocallyClosed.image (f := hU.fromSpec) (s := {p}) hcl.isLocallyClosed he.isInducing
    he.isOpen_range.isLocallyClosed
  have e : hU.fromSpec '' {p} = {y} := Set.image_singleton.trans (congrArg _ hpy)
  exact isClosed_singleton_of_isLocallyClosed_singleton (e ▸ hlc)

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c Y U mm hm x hx h`. Establish `: LocallyOfFiniteType Y.s`. Take `⟨N, i, hi, hs⟩` from `Y.proj`. Use `isProper_str c.F N` as an intermediate fact. Rewrite using `[← hs]`.

Use `infer_instance`. Establish `: JacobsonSpace (Sp c.F)` using `inferInstanceAs (JacobsonSpace (PrimeSpectrum c.F))`. Establish `: JacobsonSpace Y.X` using `LocallyOfFiniteType.jacobsonSpace Y.s`. Establish `hc` using `isClosed_singleton_of_maximal U mm hm _ hx h`. Establish `hiso : IsIso (genι Y)` using `isIso_fst Y`.

Establish `hinj : Function.Injective (genι Y)` using `(genι Y).isOpenEmbedding.injective`. Use `hc.preimage (genι Y).continuous` as an intermediate fact. Rewrite `this` using `[← Set.image_singleton, Set.preimage_image_eq _ hinj]`. Then use the resulting hypothesis.
-/
theorem isClosed_singleton_gen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (U : Y.X.affineOpens) (mm : Ideal Γ(Y.X, U.1)), mm.IsMaximal → ∀ x : gen Y, genι Y x ∈ U.1 → (∀ f ∈ mm, genι Y x ∉ Y.X.basicOpen f) → IsClosed ({x} : Set (gen Y)) := by
  intro E _ _ _ H Dw l Xo c Y U mm hm x hx h
  have : LocallyOfFiniteType Y.s := by
    obtain ⟨N, i, hi, hs⟩ := Y.proj
    have := isProper_str c.F N
    rw [← hs]; infer_instance
  have : JacobsonSpace (Sp c.F) := inferInstanceAs (JacobsonSpace (PrimeSpectrum c.F))
  have : JacobsonSpace Y.X := LocallyOfFiniteType.jacobsonSpace Y.s
  have hc := isClosed_singleton_of_maximal U mm hm _ hx h
  have hiso : IsIso (genι Y) := isIso_fst Y
  have hinj : Function.Injective (genι Y) := (genι Y).isOpenEmbedding.injective
  have := hc.preimage (genι Y).continuous
  rwa [← Set.image_singleton, Set.preimage_image_eq _ hinj] at this

end GlobalTheory.LocReg
