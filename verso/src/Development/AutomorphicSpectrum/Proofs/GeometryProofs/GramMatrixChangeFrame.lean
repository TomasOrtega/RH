import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ContDiffUncentre
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeHermitianFormExistsStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgeMetric

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c Y S Ω _ _ K _ J _ y 𝔐 z r b Γ Γ' hP h1 h2`. Take `⟨v, hv, hΓ⟩` from `h1`. Take `⟨v', hv', hΓ'⟩` from `h2`. Establish `hgen : GlobalTheory.CompanionTheory.Ar.IsCptGen 𝔐.ξ` using `𝔐.tie.gen`. Establish `hvv : v = v'` using `funext fun i => GlobalTheory.CompanionTheory.Ar.LieModel.ValAt.unique hgen (hv i) (hv' i)`.

Substitute `hvv` using the available equality. Take `⟨V, _, _, ⟨M'⟩⟩` from `GlobalTheory.CompanionTheory.Ar.lieModel_exists 𝔐.X 𝔐.t.G ℂ z`. Take `⟨h, hh, -⟩` from `GlobalTheory.T.hodge_hermitian_form_exists E H 𝔐.X 𝔐.t z V M' hP`. Establish `hpre : ∀ i, ∃ e, M'.pt e = v i`. Introduce `i`.

Establish `hT : GlobalTheory.CompanionTheory.Ar.IsTanAt 𝔐.t.G z (v i)`. Take `⟨-, hT, -⟩` from `hΓ i i`. Conclude with `hT`. Conclude with `M'.onto (v i) hT`. Use extensionality with `p q`.

Take `⟨e, he⟩` from `hpre p`. Take `⟨f, hf⟩` from `hpre q`. Establish `k1` using `(hh e f (Γ p q)).1 (by rw [he, hf]; exact hΓ p q)`. Establish `k2` using `(hh e f (Γ' p q)).1 (by rw [he, hf]; exact hΓ' p q)`. Rewrite using `[k1, k2]`.
-/
theorem gramAt_unique_of_polarisedAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (r : ℕ) (b : Fin r → 𝔐.Li) (Γ Γ' : Matrix (Fin r) (Fin r) ℂ), HodgeMetric.PolarisedAt 𝔐.t z → 𝔐.M.GramAt 𝔐.t.PP.L z b Γ → 𝔐.M.GramAt 𝔐.t.PP.L z b Γ' → Γ = Γ' := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K _ J _ y 𝔐 z r b Γ Γ' hP h1 h2
  obtain ⟨v, hv, hΓ⟩ := h1
  obtain ⟨v', hv', hΓ'⟩ := h2
  have hgen : GlobalTheory.CompanionTheory.Ar.IsCptGen 𝔐.ξ := 𝔐.tie.gen
  have hvv : v = v' := funext fun i => GlobalTheory.CompanionTheory.Ar.LieModel.ValAt.unique hgen (hv i) (hv' i)
  subst hvv
  obtain ⟨V, _, _, ⟨M'⟩⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists 𝔐.X 𝔐.t.G ℂ z
  obtain ⟨h, hh, -⟩ := GlobalTheory.T.hodge_hermitian_form_exists E H 𝔐.X 𝔐.t z V M' hP
  have hpre : ∀ i, ∃ e, M'.pt e = v i := by
    intro i
    have hT : GlobalTheory.CompanionTheory.Ar.IsTanAt 𝔐.t.G z (v i) := by
      obtain ⟨-, hT, -⟩ := hΓ i i
      exact hT
    exact M'.onto (v i) hT
  ext p q
  obtain ⟨e, he⟩ := hpre p
  obtain ⟨f, hf⟩ := hpre q
  have k1 := (hh e f (Γ p q)).1 (by rw [he, hf]; exact hΓ p q)
  have k2 := (hh e f (Γ' p q)).1 (by rw [he, hf]; exact hΓ' p q)
  rw [k1, k2]

end GlobalTheory.CompanionTheory.Ar.HodgeMetric
