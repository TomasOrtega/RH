import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsBaseChart
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan

/- English proof (translation)
Use `haveI : CompleteSpace E := FiniteDimensional.complete ℂ E`. Take `⟨g, hg⟩` from `LinearMap.exists_leftInverse_of_injective _ hk`. Set `L : F →L[ℂ] E` to `LinearMap.toContinuousLinearMap g`. Establish `hLf : ∀ x, L (fderiv ℂ f u x) = x` using `fun x => by`. Use `LinearMap.congr_fun hg x` as an intermediate fact.

Simplify `this` using `[L]`. Set `h : E → E` to `fun v => L (f v)`. Establish `hh : AnalyticAt ℂ h u` using `(L.analyticAt (f u)).comp hf`. Establish `hd : fderiv ℂ h u = ((ContinuousLinearEquiv.refl ℂ E : E ≃L[ℂ] E) : E →L[ℂ] E)`. Establish `h1 : HasFDerivAt h (L.comp (fderiv ℂ f u)) u` using `L.hasFDerivAt.comp u hf.differentiableAt.hasFDerivAt`.

Rewrite using `[h1.fderiv]`. Use extensionality with `x`. Simplify using `[hLf]`. Establish `hs : HasStrictFDerivAt h ((ContinuousLinearEquiv.refl ℂ E : E ≃L[ℂ] E) : E →L[ℂ] E) u`. Use `hh.hasStrictFDerivAt` as an intermediate fact.

Rewrite `this` using `[hd]`. Then use the resulting hypothesis. Establish `hsrc : u ∈ (hs.toOpenPartialHomeomorph h).source` using `hs.mem_toOpenPartialHomeomorph_source`. Establish `hcoe : ((hs.toOpenPartialHomeomorph h : OpenPartialHomeomorph E E) : E → E) = h` using `hs.toOpenPartialHomeomorph_coe`. Establish `han : AnalyticAt ℂ (hs.toOpenPartialHomeomorph h).symm (h u)`. Use `(hs.toOpenPartialHomeomorph h).analyticAt_symm' (i := ContinuousLinearEquiv.refl ℂ E) hsrc (by rw [hcoe]; exact hh) (by rw [hcoe]; exact hd)` as an intermediate fact.

Rewrite `this` using `[hcoe]`. Then use the resulting hypothesis. Use `⟨fun y => (hs.toOpenPartialHomeomorph h).symm (L y), ?_, ?_⟩` and prove the remaining obligations. Conclude with `AnalyticAt.comp (f := fun y => L y) (g := (hs.toOpenPartialHomeomorph h).symm) han (L.analyticAt (f u))`. Use `filter_upwards [(hs.toOpenPartialHomeomorph h).open_source.mem_nhds hsrc] with v hv`. Use `(hs.toOpenPartialHomeomorph h).left_inv hv` as an intermediate fact.

Rewrite `this` using `[hcoe]`. Then use the resulting hypothesis.
-/
theorem exists_analyticAt_leftInverse {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F] {f : E → F} {u : E} (hf : AnalyticAt ℂ f u)
    (hk : (fderiv ℂ f u : E →ₗ[ℂ] F).ker = ⊥) :
    ∃ Λ : F → E, AnalyticAt ℂ Λ (f u) ∧ ∀ᶠ v in 𝓝 u, Λ (f v) = v := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℂ E
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hk
  let L : F →L[ℂ] E := LinearMap.toContinuousLinearMap g
  have hLf : ∀ x, L (fderiv ℂ f u x) = x := fun x => by
    have := LinearMap.congr_fun hg x
    simpa [L] using this
  let h : E → E := fun v => L (f v)
  have hh : AnalyticAt ℂ h u := (L.analyticAt (f u)).comp hf
  have hd : fderiv ℂ h u = ((ContinuousLinearEquiv.refl ℂ E : E ≃L[ℂ] E) : E →L[ℂ] E) := by
    have h1 : HasFDerivAt h (L.comp (fderiv ℂ f u)) u := L.hasFDerivAt.comp u hf.differentiableAt.hasFDerivAt
    rw [h1.fderiv]
    ext x
    simp [hLf]
  have hs : HasStrictFDerivAt h ((ContinuousLinearEquiv.refl ℂ E : E ≃L[ℂ] E) : E →L[ℂ] E) u := by
    have := hh.hasStrictFDerivAt
    rwa [hd] at this
  have hsrc : u ∈ (hs.toOpenPartialHomeomorph h).source := hs.mem_toOpenPartialHomeomorph_source
  have hcoe : ((hs.toOpenPartialHomeomorph h : OpenPartialHomeomorph E E) : E → E) = h :=
    hs.toOpenPartialHomeomorph_coe
  have han : AnalyticAt ℂ (hs.toOpenPartialHomeomorph h).symm (h u) := by
    have := (hs.toOpenPartialHomeomorph h).analyticAt_symm' (i := ContinuousLinearEquiv.refl ℂ E) hsrc
      (by rw [hcoe]; exact hh) (by rw [hcoe]; exact hd)
    rwa [hcoe] at this
  refine ⟨fun y => (hs.toOpenPartialHomeomorph h).symm (L y), ?_, ?_⟩
  · exact AnalyticAt.comp (f := fun y => L y) (g := (hs.toOpenPartialHomeomorph h).symm) han (L.analyticAt (f u))
  · filter_upwards [(hs.toOpenPartialHomeomorph h).open_source.mem_nhds hsrc] with v hv
    have := (hs.toOpenPartialHomeomorph h).left_inv hv
    rwa [hcoe] at this

section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Take `⟨c, hc, rfl⟩` from `h`. Use function extensionality and compare the values at `q`. Simplify using `only [affCoord]`. Conclude with `mul_div_mul_left _ _ (hc q.1)`.
-/
theorem affCoord_congr_sameOrbit (p : (k : K) → ι k) {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    affCoord p z = affCoord p z' := by
  obtain ⟨c, hc, rfl⟩ := h
  funext q
  simp only [affCoord]
  exact mul_div_mul_left _ _ (hc q.1)

/- English proof (translation)
Rewrite using `[analyticAt_pi_iff]`. Introduce `q`. Conclude with `(C.holo q w hw).div (C.holo ⟨q.1, p q.1⟩ w hw) (hp q.1)`.
-/
theorem OrbitChart.analyticAt_affCoord {P : Ideal (MRing ι)} {e : ℕ} (C : OrbitChart P e) {w : Fin e → ℂ}
    (hw : w ∈ C.D) (p : (k : K) → ι k) (hp : ∀ k, C.φ w ⟨k, p k⟩ ≠ 0) :
    AnalyticAt ℂ (fun w' => affCoord p (C.φ w')) w := by
  rw [analyticAt_pi_iff]
  intro q
  exact (C.holo q w hw).div (C.holo ⟨q.1, p q.1⟩ w hw) (hp q.1)

end

/- English proof (translation)
Introduce and unpack `w₀ ⟨hw₀, hO₀⟩`. Take `⟨O', hO'o, hO'⟩` from `C₂.O_open`. Establish `hcont : ContinuousAt C₁.φ w₀` using `continuousAt_pi.2 fun q => (C₁.holo q w₀ hw₀).continuousAt`. Establish `hS : ∀ᶠ w in 𝓝 w₀, w ∈ C₁.D ∧ C₁.φ w ∈ C₂.O`. Establish `h1 : ∀ᶠ w in 𝓝 w₀, w ∈ C₁.D` using `C₁.isOpen_D.mem_nhds hw₀`.

Establish `h2 : ∀ᶠ w in 𝓝 w₀, C₁.φ w ∈ O'` using `hcont (hO'o.mem_nhds (by rw [hO'] at hO₀; exact hO₀.1))`. Use `filter_upwards [h1, h2] with w a b`. Conclude with `⟨a, by rw [hO']; exact ⟨b, C₁.mem w a⟩⟩`. Establish `hTc : ContinuousAt (fun w => C₂.ρ (C₁.φ w)) w₀`. Establish `h1 : Tendsto C₁.φ (𝓝 w₀) (𝓝[C₂.O] (C₁.φ w₀))` using `tendsto_nhdsWithin_iff.2 ⟨hcont, hS.mono fun _ h => h.2⟩`.

Conclude with `(C₂.ρ_cont _ hO₀).tendsto.comp h1`. Use `choose p hp using (C₁.mem w₀ hw₀).1`. Establish `hu₀ : C₂.ρ (C₁.φ w₀) ∈ C₂.D` using `C₂.ρ_mem _ hO₀`. Establish `horb` using `C₂.φ_ρ _ hO₀`. Establish `hne : ∀ k, C₂.φ (C₂.ρ (C₁.φ w₀)) ⟨k, p k⟩ ≠ 0`.

Take `⟨c, hc, hz⟩` from `horb`. Introduce `k`. Rewrite using `[hz]`. Conclude with `mul_ne_zero (hc k) (hp k)`. Establish `hA₂` using `C₂.analyticAt_affCoord hu₀ p hne`.

Establish `hA₁` using `C₁.analyticAt_affCoord hw₀ p hp`. Take `⟨Λ, hΛ, hΛl⟩` from `exists_analyticAt_leftInverse hA₂ (C₂.immersion _ hu₀ p hne)`. Establish `hval : affCoord p (C₂.φ (C₂.ρ (C₁.φ w₀))) = affCoord p (C₁.φ w₀)` using `affCoord_congr_sameOrbit p horb`. Establish `hΛ' : AnalyticAt ℂ Λ (affCoord p (C₁.φ w₀))`. Use `hΛ` as an intermediate fact.

Simplify using `only [hval] at this`. Conclude with `this`. Establish `hcomp : AnalyticAt ℂ (fun w => Λ (affCoord p (C₁.φ w))) w₀` using `AnalyticAt.comp (f := fun w => affCoord p (C₁.φ w)) (g := Λ) hΛ' hA₁`. Use `hcomp.congr ?_` and prove the remaining obligations. Use `filter_upwards [hS, hTc.eventually hΛl] with w hw hl`.

Rewrite using `[← hl, affCoord_congr_sameOrbit p (C₂.φ_ρ _ hw.2)]`.
-/
theorem OrbitChart.analyticOnNhd_transition (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (e : ℕ) (C₁ C₂ : OrbitChart P e) :
    AnalyticOnNhd ℂ (fun w => C₂.ρ (C₁.φ w)) {w | w ∈ C₁.D ∧ C₁.φ w ∈ C₂.O} := by
  rintro w₀ ⟨hw₀, hO₀⟩
  obtain ⟨O', hO'o, hO'⟩ := C₂.O_open
  have hcont : ContinuousAt C₁.φ w₀ := continuousAt_pi.2 fun q => (C₁.holo q w₀ hw₀).continuousAt
  have hS : ∀ᶠ w in 𝓝 w₀, w ∈ C₁.D ∧ C₁.φ w ∈ C₂.O := by
    have h1 : ∀ᶠ w in 𝓝 w₀, w ∈ C₁.D := C₁.isOpen_D.mem_nhds hw₀
    have h2 : ∀ᶠ w in 𝓝 w₀, C₁.φ w ∈ O' :=
      hcont (hO'o.mem_nhds (by rw [hO'] at hO₀; exact hO₀.1))
    filter_upwards [h1, h2] with w a b
    exact ⟨a, by rw [hO']; exact ⟨b, C₁.mem w a⟩⟩
  have hTc : ContinuousAt (fun w => C₂.ρ (C₁.φ w)) w₀ := by
    have h1 : Tendsto C₁.φ (𝓝 w₀) (𝓝[C₂.O] (C₁.φ w₀)) :=
      tendsto_nhdsWithin_iff.2 ⟨hcont, hS.mono fun _ h => h.2⟩
    exact (C₂.ρ_cont _ hO₀).tendsto.comp h1
  choose p hp using (C₁.mem w₀ hw₀).1
  have hu₀ : C₂.ρ (C₁.φ w₀) ∈ C₂.D := C₂.ρ_mem _ hO₀
  have horb := C₂.φ_ρ _ hO₀
  have hne : ∀ k, C₂.φ (C₂.ρ (C₁.φ w₀)) ⟨k, p k⟩ ≠ 0 := by
    obtain ⟨c, hc, hz⟩ := horb
    intro k
    rw [hz]
    exact mul_ne_zero (hc k) (hp k)
  have hA₂ := C₂.analyticAt_affCoord hu₀ p hne
  have hA₁ := C₁.analyticAt_affCoord hw₀ p hp
  obtain ⟨Λ, hΛ, hΛl⟩ := exists_analyticAt_leftInverse hA₂ (C₂.immersion _ hu₀ p hne)
  have hval : affCoord p (C₂.φ (C₂.ρ (C₁.φ w₀))) = affCoord p (C₁.φ w₀) := affCoord_congr_sameOrbit p horb
  have hΛ' : AnalyticAt ℂ Λ (affCoord p (C₁.φ w₀)) := by
    have := hΛ
    simp only [hval] at this
    exact this
  have hcomp : AnalyticAt ℂ (fun w => Λ (affCoord p (C₁.φ w))) w₀ :=
    AnalyticAt.comp (f := fun w => affCoord p (C₁.φ w)) (g := Λ) hΛ' hA₁
  refine hcomp.congr ?_
  filter_upwards [hS, hTc.eventually hΛl] with w hw hl
  rw [← hl, affCoord_congr_sameOrbit p (C₂.φ_ρ _ hw.2)]

end GlobalTheory.CompanionTheory.Ar.PB.WMan
