import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ThreeLeLevel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsUnitIffUnitAt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsIffCentresStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FibreLatticeLinearEquivStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspCorrespondenceBoundStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CuspWeightInvariantUnderIsometryStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp MeasureTheory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.WeightSheet

/- English proof (translation)
Establish `hs : ∀ q : Σ k, J k, torusSmul a w q = a q.1 * w q` using `fun q => rfl`. Use `⟨fun k => ?_, fun k c hc => ?_⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `h.1 k`. Use `⟨c, ?_⟩` and prove the remaining obligations. Rewrite using `[hs]`.

Conclude with `(isUnit_iff_ne_zero.2 (ha k)).mul hc`. Establish `hc' : IsUnit (w ⟨k, c⟩)`. Rewrite `hc` using `[hs]`. Conclude with `isUnit_of_mul_isUnit_right hc`. Take `⟨hy, hv⟩` from `h.2 k c hc'`.

Use `⟨hy, fun i => ?_⟩` and prove the remaining obligations. Take `⟨r, hr, he⟩` from `hv i`. Use `⟨r, hr, ?_⟩` and prove the remaining obligations. Rewrite using `[hs, hs]`. Use `show a k * w ⟨k, i⟩ = r * (a k * w ⟨k, c⟩)`.

Rewrite using `[he]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem coordsAt_torusSmul {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) {K : Type} [Fintype K]
    {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω} {z : Spec (CommRingCat.of ℂ) ⟶ X} {w : (Σ k, J k) → ℂ}
    (h : CoordsAt ξ y z w) {a : K → ℂ} (ha : ∀ k, a k ≠ 0) : CoordsAt ξ y z (torusSmul a w) := by
  have hs : ∀ q : Σ k, J k, torusSmul a w q = a q.1 * w q := fun q => rfl
  refine ⟨fun k => ?_, fun k c hc => ?_⟩
  · obtain ⟨c, hc⟩ := h.1 k
    refine ⟨c, ?_⟩
    rw [hs]
    exact (isUnit_iff_ne_zero.2 (ha k)).mul hc
  · have hc' : IsUnit (w ⟨k, c⟩) := by
      rw [hs] at hc
      exact isUnit_of_mul_isUnit_right hc
    obtain ⟨hy, hv⟩ := h.2 k c hc'
    refine ⟨hy, fun i => ?_⟩
    obtain ⟨r, hr, he⟩ := hv i
    refine ⟨r, hr, ?_⟩
    rw [hs, hs]
    show a k * w ⟨k, i⟩ = r * (a k * w ⟨k, c⟩)
    rw [he]
    ring

/- English proof (translation)
Take `⟨φ, hφ, -⟩` from `ValHom.exists_valAt_hom X Ω ξ R z h hξ`. Take `⟨_, e₁⟩` from `(hφ a r).1 h₁`. Take `⟨_, e₂⟩` from `(hφ a r').1 h₂`. Conclude with `e₁.symm.trans e₂`.
-/
theorem valAt_eq {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} (hξ : IsCptGen ξ)
    {R : Type} [CommRing R] [IsLocalRing R] {z : Spec (CommRingCat.of R) ⟶ X} (h : genPt ξ ⤳ centre z) {a : Ω} {r r' : R}
    (h₁ : ValAt ξ z a r) (h₂ : ValAt ξ z a r') : r = r' := by
  obtain ⟨φ, hφ, -⟩ := ValHom.exists_valAt_hom X Ω ξ R z h hξ
  obtain ⟨_, e₁⟩ := (hφ a r).1 h₁
  obtain ⟨_, e₂⟩ := (hφ a r').1 h₂
  exact e₁.symm.trans e₂

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {Xo : ∀ l : Tor.Level H, Moduli D l}
  {l : Tor.Level H} {c : Coeff l} {Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)} {II : IntersectionSystem} {K : Type}
  [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : CMType H → Type}
  [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] {Dc : ComponentData II (CMType H) K J Ω W} {Hd : HodgeData Dc}
  {S₀ : Finset ℕ}

/- English proof (translation)
Take `⟨σ₀, h0, -, -, -, -, hcm⟩` from `GlobalTheory.T.cusp_correspondence_bound E H D l (Xo l) c Y S₀ Ω K J Dc.y Or.𝔐 ℂ z`. Establish `hs : ∀ τ, σ τ = σ₀ (Or.sm τ)` using `fun τ => RingHom.ext fun a => valAt_eq Or.𝔐.tie.gen (Or.𝔐.all _) (hL τ a) (h0 (Or.sm τ) a)`. Take `⟨h1, h2, -⟩` from `hcm (RingHom.id ℂ)`. Establish `he : σ = fun τ => σ₀ (Or.sm τ)` using `funext hs`. Break down `Or.side with ⟨-, h, -⟩ | ⟨-, h, -⟩` into its components or cases.

Rewrite using `[he, h]`. Conclude with `h2`. Rewrite using `[he, h]`. Conclude with `h1`.
-/
theorem isCMFam_of_labVal (Or : CptOrigin Y S₀ Dc Hd) {z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X}
    {σ : CMType H → (𝓞 E →+* ℂ)} (hL : Or.𝔐.LabVal z Or.sm σ) : IsCMFam σ := by
  obtain ⟨σ₀, h0, -, -, -, -, hcm⟩ := GlobalTheory.T.cusp_correspondence_bound E H D l (Xo l) c Y S₀ Ω K J Dc.y Or.𝔐 ℂ z
  have hs : ∀ τ, σ τ = σ₀ (Or.sm τ) := fun τ => RingHom.ext fun a =>
    valAt_eq Or.𝔐.tie.gen (Or.𝔐.all _) (hL τ a) (h0 (Or.sm τ) a)
  obtain ⟨h1, h2, -⟩ := hcm (RingHom.id ℂ)
  have he : σ = fun τ => σ₀ (Or.sm τ) := funext hs
  rcases Or.side with ⟨-, h, -⟩ | ⟨-, h, -⟩
  · rw [he, h]
    exact h2
  · rw [he, h]
    exact h1

/- English proof (translation)
Take `⟨g', Λ', i₁, i₂, R', σ', hF', hL', he⟩` from `hU z w hw hz`. Establish `hσ : σ' = σ` using `funext fun τ => RingHom.ext fun a => valAt_eq Or.𝔐.tie.gen (Or.𝔐.all _) (hL' τ a) (hL τ a)`. Substitute `hσ` using the available equality. Take `⟨φ, h1, h2, h3, -⟩` from `GlobalTheory.T.fibre_lattice_linear_equiv E H Or.𝔐.X Or.𝔐.t z g' g Λ' Λ R' R Empty _ _ _ hF' hF`. Rewrite using `[he]`.

Apply the tactic sequence `exact (GlobalTheory.T.cusp_weight_invariant_under_isometry E g' Λ' (CMType H) R' σ' g Λ R φ (isCMFam_of_labVal Or hL) h1 h2 h3).1.symm`.
-/
theorem eq_cuspW_of_fibre (Or : CptOrigin Y S₀ Dc Hd) {U : ((Σ k, J k) → ℂ) → ℝ} (hU : Or.𝔐.IsCuspWeight Or.sm U)
    {z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X} {w : (Σ k, J k) → ℂ} (hw : CoordsAt Or.𝔐.ξ Dc.y z w) (hz : Or.𝔐.Interior z)
    {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ) {σ : CMType H → (𝓞 E →+* ℂ)}
    (hF : FibreLat Or.𝔐.t z R) (hL : Or.𝔐.LabVal z Or.sm σ) : U w = R.cuspW σ := by
  obtain ⟨g', Λ', i₁, i₂, R', σ', hF', hL', he⟩ := hU z w hw hz
  have hσ : σ' = σ := funext fun τ => RingHom.ext fun a =>
    valAt_eq Or.𝔐.tie.gen (Or.𝔐.all _) (hL' τ a) (hL τ a)
  subst hσ
  obtain ⟨φ, h1, h2, h3, -⟩ := GlobalTheory.T.fibre_lattice_linear_equiv E H Or.𝔐.X Or.𝔐.t z g' g Λ' Λ R' R Empty _ _ _ hF' hF
  rw [he]
  exact (GlobalTheory.T.cusp_weight_invariant_under_isometry E g' Λ' (CMType H) R' σ' g Λ R φ (isCMFam_of_labVal Or hL) h1 h2 h3).1.symm

/- English proof (translation)
Introduce `E _ _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or Q U hU`. Use `⟨fun w hw w' hw' => ?_, fun m t ht => ?_⟩` and prove the remaining obligations. Take `⟨z, -, hz⟩` from `(GlobalTheory.T.complex_points_iff_centres Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y Or.𝔐.tie w).1 hw.1`. Establish `hI : Or.𝔐.Interior z`. Assume the negation of the conclusion as `hn`.

Conclude with `hw.2 ((Or.bd z w hz).2 hn)`. Take `⟨u, hu, a, ha, rfl⟩` from `hw'`. Rewrite using `[show u = w from hu]`. Take `⟨g, Λ, i₁, i₂, R, σ, hF, hL, he⟩` from `hU z w hz hI`. Rewrite using `[he]`.

Conclude with `eq_cuspW_of_fibre Or hU (coordsAt_torusSmul Or.𝔐.ξ hz ha) hI R hF hL`. Take `⟨z, hz, hI, hF, hL⟩` from `Q.fibre m t ht`. Conclude with `eq_cuspW_of_fibre Or hU hz hI _ hF hL`.
-/
theorem cuspWeight_torus_and_sheets : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (Q : Pieces Or) (U : ((Σ k, J k) → ℂ) → ℝ), Or.𝔐.IsCuspWeight Or.sm U → (∀ w ∈ Dc.Xo, ∀ w' ∈ torusSat {w}, U w' = U w) ∧ ∀ m, ∀ t ∈ Q.V m, U (Q.γ m t) = ((Q.F (Q.pc m)).R t).cuspW (Q.F (Q.pc m)).σ := by
  intro E _ _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or Q U hU
  refine ⟨fun w hw w' hw' => ?_, fun m t ht => ?_⟩
  · obtain ⟨z, -, hz⟩ := (GlobalTheory.T.complex_points_iff_centres Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y Or.𝔐.tie w).1 hw.1
    have hI : Or.𝔐.Interior z := by
      by_contra hn
      exact hw.2 ((Or.bd z w hz).2 hn)
    obtain ⟨u, hu, a, ha, rfl⟩ := hw'
    rw [show u = w from hu]
    obtain ⟨g, Λ, i₁, i₂, R, σ, hF, hL, he⟩ := hU z w hz hI
    rw [he]
    exact eq_cuspW_of_fibre Or hU (coordsAt_torusSmul Or.𝔐.ξ hz ha) hI R hF hL
  · obtain ⟨z, hz, hI, hF, hL⟩ := Q.fibre m t ht
    exact eq_cuspW_of_fibre Or hU hz hI _ hF hL

end GlobalTheory.CompanionTheory.Ar.Cusp.WeightSheet

end
