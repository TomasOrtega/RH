import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExponentialFamilyPeriods
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeGram
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat

/- English proof (translation)
Establish `hcont : Continuous (fun b : Fin n → ℂ => (b, x))` using `continuous_id.prodMk continuous_const`. Establish `hUo : IsOpen ((fun b : Fin n → ℂ => (b, x)) ⁻¹' W)` using `hW.preimage hcont`. Establish `hΦd : DifferentiableOn ℂ (fun b => Φ (b, x)) ((fun b : Fin n → ℂ => (b, x)) ⁻¹' W)`. Rewrite using `[differentiableOn_pi]`. Introduce `j`.

Conclude with `(hΦ j).comp (differentiable_id.prodMk (differentiable_const x)).differentiableOn (fun b hb => hb)`. Establish `hFd : DifferentiableOn ℂ (fun b => (b, Φ (b, x))) ((fun b : Fin n → ℂ => (b, x)) ⁻¹' W)` using `differentiableOn_id.prodMk hΦd`. Establish `hb₀ : b₀ ∈ (fun b : Fin n → ℂ => (b, x)) ⁻¹' W` using `hmem`. Establish `hFc : ContinuousAt (fun b => (b, Φ (b, x))) b₀` using `(hFd.differentiableAt (hUo.mem_nhds hb₀)).continuousAt`. Establish `hU' : ∀ᶠ b in 𝓝 b₀, b ∈ (fun b : Fin n → ℂ => (b, x)) ⁻¹' W` using `hUo.mem_nhds hb₀`.

Establish `hev : ∀ᶠ b in 𝓝 b₀, b ∈ (fun b : Fin n → ℂ => (b, x)) ⁻¹' W ∧ AnalyticAt ℂ L (b, Φ (b, x)) ∧ Q (b, Φ (b, x))` using `hU'.and (Filter.Tendsto.eventually hFc (hL.eventually_analyticAt.and hQ))`. Take `⟨ε, hε, hball⟩` from `Metric.eventually_nhds_iff_ball.mp hev`. Use `⟨ε, hε, fun b hb => ?_, fun b hb => ⟨(hball b hb).1, (hball b hb).2.2⟩⟩` and prove the remaining obligations. Conclude with `((hball b hb).2.1.differentiableAt.comp b (hFd.differentiableAt (hUo.mem_nhds (hball b hb).1))).differentiableWithinAt`.
-/
theorem spread_slice {n g N : ℕ} {W : Set ((Fin n → ℂ) × (Fin g → ℂ))} (hW : IsOpen W)
    {Φ : (Fin n → ℂ) × (Fin g → ℂ) → (Fin N → ℂ)} (hΦ : ∀ j, DifferentiableOn ℂ (fun bz => Φ bz j) W)
    {b₀ : Fin n → ℂ} {x : Fin g → ℂ} (hmem : (b₀, x) ∈ W)
    {L : (Fin n → ℂ) × (Fin N → ℂ) → (Fin g → ℂ)} (hL : AnalyticAt ℂ L (b₀, Φ (b₀, x)))
    {Q : (Fin n → ℂ) × (Fin N → ℂ) → Prop} (hQ : ∀ᶠ p in 𝓝 (b₀, Φ (b₀, x)), Q p) :
    ∃ ε : ℝ, 0 < ε ∧ DifferentiableOn ℂ (fun b => L (b, Φ (b, x))) (ball b₀ ε) ∧
      ∀ b ∈ ball b₀ ε, (b, x) ∈ W ∧ Q (b, Φ (b, x)) := by
  have hcont : Continuous (fun b : Fin n → ℂ => (b, x)) := continuous_id.prodMk continuous_const
  have hUo : IsOpen ((fun b : Fin n → ℂ => (b, x)) ⁻¹' W) := hW.preimage hcont
  have hΦd : DifferentiableOn ℂ (fun b => Φ (b, x)) ((fun b : Fin n → ℂ => (b, x)) ⁻¹' W) := by
    rw [differentiableOn_pi]
    intro j
    exact (hΦ j).comp (differentiable_id.prodMk (differentiable_const x)).differentiableOn
      (fun b hb => hb)
  have hFd : DifferentiableOn ℂ (fun b => (b, Φ (b, x))) ((fun b : Fin n → ℂ => (b, x)) ⁻¹' W) :=
    differentiableOn_id.prodMk hΦd
  have hb₀ : b₀ ∈ (fun b : Fin n → ℂ => (b, x)) ⁻¹' W := hmem
  have hFc : ContinuousAt (fun b => (b, Φ (b, x))) b₀ :=
    (hFd.differentiableAt (hUo.mem_nhds hb₀)).continuousAt
  have hU' : ∀ᶠ b in 𝓝 b₀, b ∈ (fun b : Fin n → ℂ => (b, x)) ⁻¹' W := hUo.mem_nhds hb₀
  have hev : ∀ᶠ b in 𝓝 b₀, b ∈ (fun b : Fin n → ℂ => (b, x)) ⁻¹' W ∧
      AnalyticAt ℂ L (b, Φ (b, x)) ∧ Q (b, Φ (b, x)) :=
    hU'.and (Filter.Tendsto.eventually hFc (hL.eventually_analyticAt.and hQ))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  refine ⟨ε, hε, fun b hb => ?_, fun b hb => ⟨(hball b hb).1, (hball b hb).2.2⟩⟩
  exact ((hball b hb).2.1.differentiableAt.comp b
    (hFd.differentiableAt (hUo.mem_nhds (hball b hb).1))).differentiableWithinAt

/- English proof (translation)
Introduce `R _ G _ _ g n M B ψ e _ b₀ hb₀ x hx`. Establish `hx1 : e.ex b₀ x = 1` using `hx`. Establish `h01 : e.ex b₀ 0 = 1`. Establish `h` using `e.add b₀ hb₀ 0 0`. Rewrite `h` using `[add_zero]`.

Conclude with `mul_right_cancel (h.symm.trans (_root_.one_mul _).symm)`. Establish `hx0 : e.ex b₀ x = e.ex b₀ 0` using `hx1.trans h01.symm`. Take `⟨V, N, f, L, hV, hLan, hinv, huniq⟩` from `e.log b₀ hb₀`. Set `W : Set ((Fin n → ℂ) × (Fin g → ℂ))` to `{bz | bz ∈ B ×ˢ Set.univ ∧ ⊤ ≤ (TopologicalSpace.Opens.map (Over.Hom.left (e.ex bz.1 bz.2)).base).obj V}`. Establish `hWo : IsOpen W` using `(e.hol V 0).1`.

Set `Φ : (Fin n → ℂ) × (Fin g → ℂ) → (Fin N → ℂ)` to `fun bz j => valAt' (Over.Hom.left (e.ex bz.1 bz.2)) V (f j)`. Establish `hΦ : ∀ j, DifferentiableOn ℂ (fun bz => Φ bz j) W` using `fun j => (e.hol V (f j)).2`. Establish `hmemW : (b₀, x) ∈ W`. Use `⟨⟨hb₀, Set.mem_univ _⟩, ?_⟩` and prove the remaining obligations. Use `show ⊤ ≤ (TopologicalSpace.Opens.map (Over.Hom.left (e.ex b₀ x)).base).obj V`.

Rewrite using `[hx0]`. Conclude with `hV`. Establish `hΦx : Φ (b₀, x) = fun j => valAt' (Over.Hom.left (e.ex b₀ 0)) V (f j)` using `by show (fun j => valAt' (Over.Hom.left (e.ex b₀ x)) V (f j)) = _`. Rewrite using `[hx0]`. Establish `hL' : AnalyticAt ℂ L (b₀, Φ (b₀, x))`.

Rewrite using `[hΦx]`. Conclude with `hLan`. Set `Q : (Fin n → ℂ) × (Fin N → ℂ) → Prop` to `fun p => ∀ y : Over.mk (spMap (ψ p.1)) ⟶ G, ⊤ ≤ (TopologicalSpace.Opens.map (Over.Hom.left y).base).obj V → (∀ j, valAt' (Over.Hom.left y) V (f j) = p.2 j) → y = e.ex p.1 (L p)`. Establish `hQ : ∀ᶠ p in 𝓝 (b₀, Φ (b₀, x)), Q p`. Rewrite using `[hΦx]`.

Conclude with `huniq`. Take `⟨ε, hε, hdiff, hprop⟩` from `spread_slice hWo hΦ hmemW hL' hQ`. Establish `hWmem : ∀ b ∈ ball b₀ ε, b ∈ B ∧ ⊤ ≤ (TopologicalSpace.Opens.map (Over.Hom.left (e.ex b x)).base).obj V`. Introduce `b hb`. Take `⟨⟨hbB, -⟩, hcov⟩` from `(hprop b hb).1`.

Conclude with `⟨hbB, hcov⟩`. Use `⟨ε, fun b => x - L (b, Φ (b, x)), hε, fun b hb => (hWmem b hb).1, (differentiableOn_const x).sub hdiff, ?_, ?_⟩` and prove the remaining obligations. Use `show x - L (b₀, Φ (b₀, x)) = x`. Establish `h0 : L (b₀, fun j => valAt' (Over.Hom.left (e.ex b₀ 0)) V (f j)) = 0` using `hinv.self_of_nhds`. Rewrite using `[hΦx, h0, sub_zero]`.

Introduce `b hb`. Take `⟨hbB, hcov⟩` from `hWmem b hb`. Establish `hyx : e.ex b x = e.ex b (L (b, Φ (b, x)))` using `(hprop b hb).2 (e.ex b x) hcov (fun j => rfl)`. Use `show e.ex b (x - L (b, Φ (b, x))) = 1`. Establish `hadd` using `e.add b hbB (x - L (b, Φ (b, x))) (L (b, Φ (b, x)))`.

Rewrite `hadd` using `[sub_add_cancel, hyx]`. Conclude with `mul_right_cancel (hadd.symm.trans (_root_.one_mul _).symm)`.
-/
theorem per_spreads : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (g n : ℕ) (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : FamExp G M B ψ), IsOpen B → ∀ b₀ ∈ B, ∀ x ∈ e.per b₀, ∃ (ε : ℝ) (s : (Fin n → ℂ) → (Fin g → ℂ)), 0 < ε ∧ ball b₀ ε ⊆ B ∧ DifferentiableOn ℂ s (ball b₀ ε) ∧ s b₀ = x ∧ ∀ b ∈ ball b₀ ε, s b ∈ e.per b := by
  intro R _ G _ _ g n M B ψ e _ b₀ hb₀ x hx
  have hx1 : e.ex b₀ x = 1 := hx
  have h01 : e.ex b₀ 0 = 1 := by
    have h := e.add b₀ hb₀ 0 0
    rw [add_zero] at h
    exact mul_right_cancel (h.symm.trans (_root_.one_mul _).symm)
  have hx0 : e.ex b₀ x = e.ex b₀ 0 := hx1.trans h01.symm
  obtain ⟨V, N, f, L, hV, hLan, hinv, huniq⟩ := e.log b₀ hb₀
  let W : Set ((Fin n → ℂ) × (Fin g → ℂ)) := {bz | bz ∈ B ×ˢ Set.univ ∧
    ⊤ ≤ (TopologicalSpace.Opens.map (Over.Hom.left (e.ex bz.1 bz.2)).base).obj V}
  have hWo : IsOpen W := (e.hol V 0).1
  let Φ : (Fin n → ℂ) × (Fin g → ℂ) → (Fin N → ℂ) :=
    fun bz j => valAt' (Over.Hom.left (e.ex bz.1 bz.2)) V (f j)
  have hΦ : ∀ j, DifferentiableOn ℂ (fun bz => Φ bz j) W := fun j => (e.hol V (f j)).2
  have hmemW : (b₀, x) ∈ W := by
    refine ⟨⟨hb₀, Set.mem_univ _⟩, ?_⟩
    show ⊤ ≤ (TopologicalSpace.Opens.map (Over.Hom.left (e.ex b₀ x)).base).obj V
    rw [hx0]
    exact hV
  have hΦx : Φ (b₀, x) = fun j => valAt' (Over.Hom.left (e.ex b₀ 0)) V (f j) := by
    show (fun j => valAt' (Over.Hom.left (e.ex b₀ x)) V (f j)) = _
    rw [hx0]
  have hL' : AnalyticAt ℂ L (b₀, Φ (b₀, x)) := by
    rw [hΦx]
    exact hLan
  let Q : (Fin n → ℂ) × (Fin N → ℂ) → Prop := fun p =>
    ∀ y : Over.mk (spMap (ψ p.1)) ⟶ G,
      ⊤ ≤ (TopologicalSpace.Opens.map (Over.Hom.left y).base).obj V →
        (∀ j, valAt' (Over.Hom.left y) V (f j) = p.2 j) → y = e.ex p.1 (L p)
  have hQ : ∀ᶠ p in 𝓝 (b₀, Φ (b₀, x)), Q p := by
    rw [hΦx]
    exact huniq
  obtain ⟨ε, hε, hdiff, hprop⟩ := spread_slice hWo hΦ hmemW hL' hQ
  have hWmem : ∀ b ∈ ball b₀ ε, b ∈ B ∧
      ⊤ ≤ (TopologicalSpace.Opens.map (Over.Hom.left (e.ex b x)).base).obj V := by
    intro b hb
    obtain ⟨⟨hbB, -⟩, hcov⟩ := (hprop b hb).1
    exact ⟨hbB, hcov⟩
  refine ⟨ε, fun b => x - L (b, Φ (b, x)), hε, fun b hb => (hWmem b hb).1,
    (differentiableOn_const x).sub hdiff, ?_, ?_⟩
  · show x - L (b₀, Φ (b₀, x)) = x
    have h0 : L (b₀, fun j => valAt' (Over.Hom.left (e.ex b₀ 0)) V (f j)) = 0 :=
      hinv.self_of_nhds
    rw [hΦx, h0, sub_zero]
  · intro b hb
    obtain ⟨hbB, hcov⟩ := hWmem b hb
    have hyx : e.ex b x = e.ex b (L (b, Φ (b, x))) :=
      (hprop b hb).2 (e.ex b x) hcov (fun j => rfl)
    show e.ex b (x - L (b, Φ (b, x))) = 1
    have hadd := e.add b hbB (x - L (b, Φ (b, x))) (L (b, Φ (b, x)))
    rw [sub_add_cancel, hyx] at hadd
    exact mul_right_cancel (hadd.symm.trans (_root_.one_mul _).symm)

end GlobalTheory.CompanionTheory.Ar.Flat
