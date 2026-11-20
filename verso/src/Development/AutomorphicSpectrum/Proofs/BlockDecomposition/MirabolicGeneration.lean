import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold

noncomputable section

open MeasureTheory PositivityTheory.RgEis PositivityTheory.RgEis.MG

namespace GlobalTheory.CompanionTheory.EisMir

/- English proof (translation)
Establish `hint : Integrable (fun κ : K => (1 : ℂ) • ρ κ) μ`. Simplify using `only [one_smul]`. Conclude with `hρ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)`. Simplify using `only [avg]`. Rewrite using `[ContinuousLinearMap.integral_apply hint]`.

Simplify using `[hw]`.
-/
theorem avg_one_apply {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [FiniteDimensional ℂ W] {K : Subgroup G} [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsProbabilityMeasure μ] (ρ : K →* (W →L[ℂ] W)) (hρ : Continuous ρ) (w : W)
    (hw : ∀ r : K, ρ r w = w) : avg μ ρ (fun _ => (1 : ℂ)) w = w := by
  have hint : Integrable (fun κ : K => (1 : ℂ) • ρ κ) μ := by
    simp only [one_smul]
    exact hρ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp only [avg]
  rw [ContinuousLinearMap.integral_apply hint]
  simp [hw]

/- English proof (translation)
Use `⟨?_, fun g => ⟨g, Subgroup.mem_top g, 1, K.one_mem, (mul_one g).symm⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [Subgroup.coe_top]`. Conclude with `isClosed_univ`. Conclude with `⟨fun _ _ _ _ => by simp, fun _ _ => by simp, fun _ _ _ => by simp, continuous_const.continuousOn⟩`.
-/
theorem isPar_top {G : Type} [Group G] [TopologicalSpace G] (Γ K : Subgroup G) :
    IsPar Γ K ⊤ (1 : G → ℂ) := by
  refine ⟨?_, fun g => ⟨g, Subgroup.mem_top g, 1, K.one_mem, (mul_one g).symm⟩, ?_⟩
  · simp only [Subgroup.coe_top]
    exact isClosed_univ
  · exact ⟨fun _ _ _ _ => by simp, fun _ _ => by simp, fun _ _ _ => by simp,
      continuous_const.continuousOn⟩

/- English proof (translation)
Unfold `sec`. Rewrite using `[dif_pos ⟨1, Subgroup.mem_top _⟩]`. Simplify using `[hw]`.
-/
theorem sec_top_apply {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W]
    [NormedSpace ℂ W] (K : Subgroup G) (ρ : K →* (W →L[ℂ] W)) (g : G) (w : W)
    (hw : ∀ r : K, ρ r w = w) : sec K ⊤ (1 : G → ℂ) ρ g w = w := by
  unfold sec
  rw [dif_pos ⟨1, Subgroup.mem_top _⟩]
  simp [hw]

/- English proof (translation)
Introduce `_hSec hSph hMem hInv hSide hTK hCore G _ _ _ _ _ W _ _ _ K ρ hK hρ k _ _ ι _ _ π Γ i₀ i₁ ω d c η η' l hSC hMD`. Use `haveI := hSC`. Use `haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK`. Use `letI : MeasurableSpace K := borel K`. Use `haveI : BorelSpace K := ⟨rfl⟩`.

Set `μ : Measure K` to `Measure.haarMeasure ⊤`. Establish `hHaar : μ.IsHaarMeasure` using `Measure.isHaarMeasure_haarMeasure _`. Establish `hProb : IsProbabilityMeasure μ` using `⟨by`. Establish `h` using `Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts K))`. Simplify using `using h⟩`.

Use `haveI := hProb`. Establish `hN1 : (1 : ℝ) < Fintype.card ι`. Establish `h2` using `hMD.two`. Conclude with `(show 1 < Fintype.card ι by omega)` after adjusting the coercions. Take `⟨hS0, -, -, -⟩` from `hSide G K hK k ι π Γ i₀ i₁ ω d c η η' l hMD`.

Take `⟨V, hV, hJV⟩` from `hInv G W K ρ hK hρ μ hHaar hProb Γ _ c hMD.par`. Take `⟨Ψ, Ψ₁, φ, hΨ, hΨ₁, hφc, hφ1, hφL, hφN, hzt, hz, hω1⟩` from `hTK G K hK k ι π Γ _ i₀ ω d c η hS0 V hV`. Take `⟨J, hJ⟩` from `hJV φ hφc hφ1 hφL hφN`. Take `⟨R, D, Op, H, hW, ⟨dd, hdd, hD, hddN⟩, -, hH⟩` from `hCore G W K ρ hK hρ μ hHaar hProb k ι π Γ i₀ i₁ ω d c η η' l hMD Ψ Ψ₁ φ _ J hΨ hΨ₁ hzt hz le_rfl hJ`. Use `⟨⟨R, D, Op, H, hW⟩, fun hω hc => ?_⟩` and prove the remaining obligations.

Substitute `hω` using the available equality. Substitute `hc` using the available equality. Establish `hinv : ∀ w ∈ secSp K ⊤ (1 : G → ℂ) ρ, ∀ r : K, ρ r w = w` using `fun w hw r => by`. Simplify using `using hw r (Subgroup.mem_top _)`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Take `⟨Ψs, Ψ₁s, hΨs, hΨ₁s, hΨ0, hsph, hnz⟩` from `hSph k ι i₀`. Establish `hzt' : ∀ s (κ : K), zt π d i₀ Ψs 1 s κ = tate Ψ₁s 1 s * (fun _ => (1 : ℂ)) κ`. Introduce `s κ`. Simplify using `only [mul_one]`. Unfold `zt tate lineZeta`.

Use `congr 1`. Use function extensionality and compare the values at `t`. Conclude with `hsph t ⟨kap π d κ, hS0.piK κ κ.2⟩`. Establish `hnz' : ∃ z : ℂ, (Fintype.card ι : ℝ) < z.re ∧ tate Ψ₁s 1 z ≠ 0` using `⟨(((Fintype.card ι : ℝ) + 1 : ℝ) : ℂ), by simp, hnz _ (by linarith)⟩`. Establish `hle : secSp K ⊤ (1 : G → ℂ) ρ ≤ secSp K ((stab _ {i₀}).comap π) 1 ρ` using `fun w hw r _ => hw r (Subgroup.mem_top _)`.

Establish `havg : ∀ w : secSp K ⊤ (1 : G → ℂ) ρ, avg μ ρ (fun _ => (1 : ℂ)) ((secSp K ⊤ (1 : G → ℂ) ρ).subtypeL w) = w` using `fun w => by`. Simplify using `using avg_one_apply μ ρ hρ (w : W) (hinv w w.2)`. Take `⟨R', D', Op', H', hW', -, ⟨O', hO', hOp'⟩, hH'⟩` from `hCore G W K ρ hK hρ μ hHaar hProb k ι π Γ i₀ i₁ 1 d 1 η η' l hMD Ψs Ψ₁s (fun _ => 1) (secSp K ⊤ (1 : G → ℂ) ρ) (secSp K ⊤ (1 : G → ℂ) ρ).subtypeL hΨs hΨ₁s hzt' hnz' hle havg`. Take `⟨⟨a, ha, hH0⟩, -⟩` from `hH' rfl`. Use `⟨R', D', Op', H', hW', ⟨a, ha, fun g w => ?_⟩, O', hO', hOp'⟩` and prove the remaining obligations.

Rewrite using `[hH0, hΨ0, mul_one, havg w, sec_top_apply K ρ g (w : W) (hinv w w.2)]`. Take `⟨-, b, hb⟩` from `hH rfl`. Establish `hmem : ∀ v, avg μ ρ (fun _ => (1 : ℂ)) v ∈ secSp K ⊤ (1 : G → ℂ) ρ` using `hMem G W K ρ hK hρ μ hHaar hProb Γ ⊤ 1 (isPar_top Γ K) (fun _ => 1) continuous_const (fun _ _ _ => by simp)`. Set `T : secSp K ((stab _ {i₀}).comap π) 1 ρ →L[ℂ] secSp K ⊤ (1 : G → ℂ) ρ` to `b • ((avg μ ρ (fun _ => (1 : ℂ))).comp J).codRestrict _ (fun w => hmem (J w))`. Use `⟨R, D, Op, H, hW, ⟨dd, hdd, hddN (hω1 rfl _ hN1), hD⟩, T, fun g w => ?_⟩` and prove the remaining obligations.

Rewrite using `[hb g w, sec_top_apply K ρ g _ (hinv _ (T w).2), mul_smul]`. Both sides reduce to the same expression.
-/
theorem mirGen_of_core : SecLaw → TestSph → AvgMem → AvgInv → SideOf → TestK → Core → MirGen := by
  intro _hSec hSph hMem hInv hSide hTK hCore G _ _ _ _ _ W _ _ _ K ρ hK hρ k _ _ ι _ _ π Γ i₀ i₁ ω d c η η' l hSC hMD
  haveI := hSC
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  letI : MeasurableSpace K := borel K
  haveI : BorelSpace K := ⟨rfl⟩
  let μ : Measure K := Measure.haarMeasure ⊤
  have hHaar : μ.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _
  have hProb : IsProbabilityMeasure μ := ⟨by
    have h := Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts K))
    simpa using h⟩
  haveI := hProb
  have hN1 : (1 : ℝ) < Fintype.card ι := by
    have h2 := hMD.two
    exact_mod_cast (show 1 < Fintype.card ι by omega)
  obtain ⟨hS0, -, -, -⟩ := hSide G K hK k ι π Γ i₀ i₁ ω d c η η' l hMD
  obtain ⟨V, hV, hJV⟩ := hInv G W K ρ hK hρ μ hHaar hProb Γ _ c hMD.par
  obtain ⟨Ψ, Ψ₁, φ, hΨ, hΨ₁, hφc, hφ1, hφL, hφN, hzt, hz, hω1⟩ :=
    hTK G K hK k ι π Γ _ i₀ ω d c η hS0 V hV
  obtain ⟨J, hJ⟩ := hJV φ hφc hφ1 hφL hφN
  obtain ⟨R, D, Op, H, hW, ⟨dd, hdd, hD, hddN⟩, -, hH⟩ :=
    hCore G W K ρ hK hρ μ hHaar hProb k ι π Γ i₀ i₁ ω d c η η' l hMD Ψ Ψ₁ φ _ J hΨ hΨ₁ hzt hz le_rfl hJ
  refine ⟨⟨R, D, Op, H, hW⟩, fun hω hc => ?_⟩
  subst hω
  subst hc
  have hinv : ∀ w ∈ secSp K ⊤ (1 : G → ℂ) ρ, ∀ r : K, ρ r w = w := fun w hw r => by
    simpa using hw r (Subgroup.mem_top _)
  refine ⟨?_, ?_⟩
  · obtain ⟨Ψs, Ψ₁s, hΨs, hΨ₁s, hΨ0, hsph, hnz⟩ := hSph k ι i₀
    have hzt' : ∀ s (κ : K), zt π d i₀ Ψs 1 s κ = tate Ψ₁s 1 s * (fun _ => (1 : ℂ)) κ := by
      intro s κ
      simp only [mul_one]
      unfold zt tate lineZeta
      congr 1
      funext t
      exact hsph t ⟨kap π d κ, hS0.piK κ κ.2⟩
    have hnz' : ∃ z : ℂ, (Fintype.card ι : ℝ) < z.re ∧ tate Ψ₁s 1 z ≠ 0 :=
      ⟨(((Fintype.card ι : ℝ) + 1 : ℝ) : ℂ), by simp, hnz _ (by linarith)⟩
    have hle : secSp K ⊤ (1 : G → ℂ) ρ ≤ secSp K ((stab _ {i₀}).comap π) 1 ρ :=
      fun w hw r _ => hw r (Subgroup.mem_top _)
    have havg : ∀ w : secSp K ⊤ (1 : G → ℂ) ρ,
        avg μ ρ (fun _ => (1 : ℂ)) ((secSp K ⊤ (1 : G → ℂ) ρ).subtypeL w) = w := fun w => by
      simpa using avg_one_apply μ ρ hρ (w : W) (hinv w w.2)
    obtain ⟨R', D', Op', H', hW', -, ⟨O', hO', hOp'⟩, hH'⟩ :=
      hCore G W K ρ hK hρ μ hHaar hProb k ι π Γ i₀ i₁ 1 d 1 η η' l hMD Ψs Ψ₁s (fun _ => 1)
        (secSp K ⊤ (1 : G → ℂ) ρ) (secSp K ⊤ (1 : G → ℂ) ρ).subtypeL hΨs hΨ₁s hzt' hnz' hle havg
    obtain ⟨⟨a, ha, hH0⟩, -⟩ := hH' rfl
    refine ⟨R', D', Op', H', hW', ⟨a, ha, fun g w => ?_⟩, O', hO', hOp'⟩
    rw [hH0, hΨ0, mul_one, havg w, sec_top_apply K ρ g (w : W) (hinv w w.2)]
  · obtain ⟨-, b, hb⟩ := hH rfl
    have hmem : ∀ v, avg μ ρ (fun _ => (1 : ℂ)) v ∈ secSp K ⊤ (1 : G → ℂ) ρ :=
      hMem G W K ρ hK hρ μ hHaar hProb Γ ⊤ 1 (isPar_top Γ K) (fun _ => 1) continuous_const
        (fun _ _ _ => by simp)
    let T : secSp K ((stab _ {i₀}).comap π) 1 ρ →L[ℂ] secSp K ⊤ (1 : G → ℂ) ρ :=
      b • ((avg μ ρ (fun _ => (1 : ℂ))).comp J).codRestrict _ (fun w => hmem (J w))
    refine ⟨R, D, Op, H, hW, ⟨dd, hdd, hddN (hω1 rfl _ hN1), hD⟩, T, fun g w => ?_⟩
    rw [hb g w, sec_top_apply K ρ g _ (hinv _ (T w).2), mul_smul]
    rfl

end GlobalTheory.CompanionTheory.EisMir
