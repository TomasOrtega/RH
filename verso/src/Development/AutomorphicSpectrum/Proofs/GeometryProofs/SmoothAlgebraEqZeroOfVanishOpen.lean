import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenPtSpecializesOfSpecializes
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueSection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.UnLocal
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitAtDivOfIsGenAt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsNeZeroIsStandardSmoothOfRelativeDimension

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
open ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.PullbackSections
open GlobalTheory.CompanionTheory.Ar.Flat.GagaC

namespace GlobalTheory.CompanionTheory.Ar.Flat.GagaC

/- English proof (translation)
Take `⟨b₀, hb₀⟩` from `hne`. Take `⟨ε, hε, hball⟩` from `Metric.isOpen_iff.1 hO b₀ hb₀`. Use `MvPolynomial.funext_set (fun i => Metric.ball (b₀ i) ε) (fun i => infinite_of_mem_nhds (b₀ i) (Metric.ball_mem_nhds _ hε)) fun x hx => ?_` and prove the remaining obligations. Rewrite using `[map_zero]`. Conclude with `h x (hball (by rw [ball_pi _ hε]; exact hx))`.
-/
theorem mvPolynomial_eq_zero_of_eval_eq_zero_on_open {D : ℕ} {O : Set (Fin D → ℂ)}
    (hO : IsOpen O) (hne : O.Nonempty) (p : MvPolynomial (Fin D) ℂ)
    (h : ∀ b ∈ O, MvPolynomial.eval b p = 0) : p = 0 := by
  obtain ⟨b₀, hb₀⟩ := hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO b₀ hb₀
  refine MvPolynomial.funext_set (fun i => Metric.ball (b₀ i) ε)
    (fun i => infinite_of_mem_nhds (b₀ i) (Metric.ball_mem_nhds _ hε)) fun x hx => ?_
  rw [map_zero]
  exact h x (hball (by rw [ball_pi _ hε]; exact hx))

/- English proof (translation)
Introduce `A _ _ _ D _ O Ψ f a hO hne hΨ ha`. Assume the negation of the conclusion as `ha0`. Establish `key : ∀ b ∈ O, ∀ p : MvPolynomial (Fin D) ℂ, Ψ b (MvPolynomial.aeval f p) = MvPolynomial.eval b p`. Introduce `b hb p`. Set `φ : A →ₐ[ℂ] ℂ` to `{ Ψ b with commutes' := fun r => DFunLike.congr_fun (hΨ b hb).1 r }`.

Establish `h1 : φ.comp (MvPolynomial.aeval f) = MvPolynomial.aeval b`. Use extensionality with `i`. Simplify `(hΨ b hb).2 i` using `[φ]`. Establish `h2` using `DFunLike.congr_fun h1 p`. Conclude with `h2.trans (DFunLike.congr_fun (MvPolynomial.coe_aeval_eq_eval b) p)`.

Establish `hind : AlgebraicIndependent ℂ f`. Rewrite using `[algebraicIndependent_iff]`. Introduce `p hp`. Use `mvPolynomial_eq_zero_of_eval_eq_zero_on_open hO hne p fun b hb => ?_` and prove the remaining obligations. Rewrite using `[← key b hb p, hp, map_zero]`.

Take `⟨e, he⟩` from `Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial D ℂ A`. Establish `htr : Algebra.trdeg ℂ A = D` using `GlobalTheory.AffinePoints.trdeg_eq_of_etale e he`. Establish `hbasis : IsTranscendenceBasis ℂ f` using `hind.isTranscendenceBasis_of_trdeg_le_of_finite (by simp [htr])`. Use `haveI := hbasis.isAlgebraic`. Take `⟨r, hr, c, hc⟩` from `(Algebra.IsAlgebraic.isAlgebraic (R := Algebra.adjoin ℂ (Set.range f)) a).exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero ha0)`.

Establish `hmem : (r : A) ∈ (MvPolynomial.aeval f : MvPolynomial (Fin D) ℂ →ₐ[ℂ] A).range`. Rewrite using `[← Algebra.adjoin_range_eq_range_aeval]`. Conclude with `r.2`. Take `⟨p, hp⟩` from `hmem`. Establish `hp' : MvPolynomial.aeval f p = (r : A)` using `hp`.

Establish `hp0 : p = 0`. Use `mvPolynomial_eq_zero_of_eval_eq_zero_on_open hO hne p fun b hb => ?_` and prove the remaining obligations. Establish `hrc : (r : A) = a * c` using `hc`. Rewrite using `[← key b hb p, hp', hrc, map_mul, ha b hb, zero_mul]`. Apply `hr` to reduce the goal to its premises.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← hp', hp0, map_zero]`. Both sides reduce to the same expression.
-/
theorem eq_zero_of_forall_points_eq_zero :
    ∀ (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] (D : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension D ℂ A] (O : Set (Fin D → ℂ)) (Ψ : (Fin D → ℂ) → (A →+* ℂ)) (f : Fin D → A) (a : A), IsOpen O → O.Nonempty → (∀ b ∈ O, (Ψ b).comp (algebraMap ℂ A) = RingHom.id ℂ ∧ ∀ i, Ψ b (f i) = b i) → (∀ b ∈ O, Ψ b a = 0) → a = 0 := by
  intro A _ _ _ D _ O Ψ f a hO hne hΨ ha
  by_contra ha0
  have key : ∀ b ∈ O, ∀ p : MvPolynomial (Fin D) ℂ,
      Ψ b (MvPolynomial.aeval f p) = MvPolynomial.eval b p := by
    intro b hb p
    let φ : A →ₐ[ℂ] ℂ :=
      { Ψ b with commutes' := fun r => DFunLike.congr_fun (hΨ b hb).1 r }
    have h1 : φ.comp (MvPolynomial.aeval f) = MvPolynomial.aeval b := by
      ext i
      simpa [φ] using (hΨ b hb).2 i
    have h2 := DFunLike.congr_fun h1 p
    exact h2.trans (DFunLike.congr_fun (MvPolynomial.coe_aeval_eq_eval b) p)
  have hind : AlgebraicIndependent ℂ f := by
    rw [algebraicIndependent_iff]
    intro p hp
    refine mvPolynomial_eq_zero_of_eval_eq_zero_on_open hO hne p fun b hb => ?_
    rw [← key b hb p, hp, map_zero]
  obtain ⟨e, he⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial D ℂ A
  have htr : Algebra.trdeg ℂ A = D := GlobalTheory.AffinePoints.trdeg_eq_of_etale e he
  have hbasis : IsTranscendenceBasis ℂ f :=
    hind.isTranscendenceBasis_of_trdeg_le_of_finite (by simp [htr])
  haveI := hbasis.isAlgebraic
  obtain ⟨r, hr, c, hc⟩ := (Algebra.IsAlgebraic.isAlgebraic
    (R := Algebra.adjoin ℂ (Set.range f)) a).exists_nonzero_dvd
      (mem_nonZeroDivisors_of_ne_zero ha0)
  have hmem : (r : A) ∈ (MvPolynomial.aeval f : MvPolynomial (Fin D) ℂ →ₐ[ℂ] A).range := by
    rw [← Algebra.adjoin_range_eq_range_aeval]
    exact r.2
  obtain ⟨p, hp⟩ := hmem
  have hp' : MvPolynomial.aeval f p = (r : A) := hp
  have hp0 : p = 0 := by
    refine mvPolynomial_eq_zero_of_eval_eq_zero_on_open hO hne p fun b hb => ?_
    have hrc : (r : A) = a * c := hc
    rw [← key b hb p, hp', hrc, map_mul, ha b hb, zero_mul]
  apply hr
  apply Subtype.ext
  rw [← hp', hp0, map_zero]
  rfl

end GlobalTheory.CompanionTheory.Ar.Flat.GagaC
