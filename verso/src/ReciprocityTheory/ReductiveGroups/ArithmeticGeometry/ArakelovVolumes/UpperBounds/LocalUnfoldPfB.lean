import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldPfA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfB
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.LUB

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal ContDiff

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
  {x1' : Frame X.Ψ r} (b1 : Frame X.Ψ r) (D : ExtFPf.LUData X x1')

/- English proof (translation)
Conclude with `(OntoB.cd_cpt X x).differentiable (by simp)`.
-/
theorem cpt_diff (x : Frame X.Ψ r) : Differentiable ℂ (cpt X x) := by
  exact (OntoB.cd_cpt X x).differentiable (by simp)

def Uc : Set (V (nd X)) := (cpt X (rmul x1' b1)) ⁻¹' ExtFPf.cell D

/- English proof (translation)
Establish `hcell : IsOpen (ExtFPf.cell D)` using `(FourierCoefficientDomain.isOpen_dom (X := X)).inter (D.hΔ.continuous.isOpen_preimage _ isOpen_compl_singleton)`. Conclude with `(cpt_diff X _).continuous.isOpen_preimage _ hcell`.
-/
theorem isOpen_Uc : IsOpen (Uc X b1 D) := by
  have hcell : IsOpen (ExtFPf.cell D) :=
    (FourierCoefficientDomain.isOpen_dom (X := X)).inter (D.hΔ.continuous.isOpen_preimage _ isOpen_compl_singleton)
  exact (cpt_diff X _).continuous.isOpen_preimage _ hcell

/- English proof (translation)
Conclude with `D.hz.comp (cpt_diff X _).differentiableOn fun z hz => hz`.
-/
theorem Φ_diffOn : DifferentiableOn ℂ (Φ X b1 D) (Uc X b1 D) := by
  exact D.hz.comp (cpt_diff X _).differentiableOn fun z hz => hz

/- English proof (translation)
Use `contDiffOn_piLp' 2 fun i => ?_` and prove the remaining obligations. Establish `hi : DifferentiableOn ℂ (fun x => (EuclideanSpace.proj (𝕜` using `ℂ) (ι := Fin (nd X)) i) (Φ X b1 D x)) (Uc X b1 D) := (EuclideanSpace.proj (𝕜 := ℂ) (ι := Fin (nd X)) i).differentiable.comp_differentiableOn (Φ_diffOn X b1 D)`. Conclude with `ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn (nd X) _ _ (isOpen_Uc X b1 D) hi`.
-/
theorem Φ_cdOn : ContDiffOn ℂ ∞ (Φ X b1 D) (Uc X b1 D) := by
  refine contDiffOn_piLp' 2 fun i => ?_
  have hi : DifferentiableOn ℂ (fun x => (EuclideanSpace.proj (𝕜 := ℂ) (ι := Fin (nd X)) i) (Φ X b1 D x))
      (Uc X b1 D) :=
    (EuclideanSpace.proj (𝕜 := ℂ) (ι := Fin (nd X)) i).differentiable.comp_differentiableOn (Φ_diffOn X b1 D)
  exact ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn (nd X) _ _ (isOpen_Uc X b1 D) hi

/- English proof (translation)
Establish `hcd : ContDiffOn ℝ ∞ (Φ X b1 D) (Uc X b1 D)` using `(Φ_cdOn X b1 D).restrict_scalars ℝ`. Establish `hfd : ContinuousOn (fun z => fderiv ℝ (Φ X b1 D) z) (Uc X b1 D)` using `hcd.continuousOn_fderiv_of_isOpen (isOpen_Uc X b1 D) (by simp)`. Establish `hdet : ContinuousOn (fun z => (fderiv ℝ (Φ X b1 D) z).det) (Uc X b1 D)` using `ContinuousLinearMap.continuous_det.comp_continuousOn hfd`. Take `⟨C, hC⟩` from `(isCompact_closedBall (0 : V (nd X)) ρ0).exists_bound_of_continuousOn (hdet.mono hsub)`. Conclude with `⟨C, fun z hz => by simpa [Real.norm_eq_abs] using hC z hz⟩`.
-/
theorem jac_bound {ρ0 : ℝ} (hsub : Metric.closedBall (0 : V (nd X)) ρ0 ⊆ Uc X b1 D) :
    ∃ Kj : ℝ, ∀ z ∈ Metric.closedBall (0 : V (nd X)) ρ0, |(fderiv ℝ (Φ X b1 D) z).det| ≤ Kj := by
  have hcd : ContDiffOn ℝ ∞ (Φ X b1 D) (Uc X b1 D) := (Φ_cdOn X b1 D).restrict_scalars ℝ
  have hfd : ContinuousOn (fun z => fderiv ℝ (Φ X b1 D) z) (Uc X b1 D) :=
    hcd.continuousOn_fderiv_of_isOpen (isOpen_Uc X b1 D) (by simp)
  have hdet : ContinuousOn (fun z => (fderiv ℝ (Φ X b1 D) z).det) (Uc X b1 D) :=
    ContinuousLinearMap.continuous_det.comp_continuousOn hfd
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : V (nd X)) ρ0).exists_bound_of_continuousOn (hdet.mono hsub)
  exact ⟨C, fun z hz => by simpa [Real.norm_eq_abs] using hC z hz⟩

/- English proof (translation)
Establish `hΦc : ContinuousOn (Φ X b1 D) (Uc X b1 D)` using `(Φ_diffOn X b1 D).continuousOn`. Establish `hmaps : Set.MapsTo (Φ X b1 D) (Uc X b1 D) (OmF X x1')` using `fun z hz => (split X b1 D hz).1`. Establish `hc : ContinuousOn (fun z => densF X x1' (Φ X b1 D z)) (Uc X b1 D)` using `(OntoB.densF_continuousOn (X := X) (x0 := x1')).comp hΦc hmaps`. Take `⟨C, hC⟩` from `(isCompact_closedBall (0 : V (nd X)) ρ0).exists_bound_of_continuousOn (hc.mono hsub)`. Conclude with `⟨C, fun z hz => (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hC z hz)⟩`.
-/
theorem dens_bound {ρ0 : ℝ} (hsub : Metric.closedBall (0 : V (nd X)) ρ0 ⊆ Uc X b1 D) :
    ∃ Kd : ℝ, ∀ z ∈ Metric.closedBall (0 : V (nd X)) ρ0, densF X x1' (Φ X b1 D z) ≤ Kd := by
  have hΦc : ContinuousOn (Φ X b1 D) (Uc X b1 D) := (Φ_diffOn X b1 D).continuousOn
  have hmaps : Set.MapsTo (Φ X b1 D) (Uc X b1 D) (OmF X x1') := fun z hz => (split X b1 D hz).1
  have hc : ContinuousOn (fun z => densF X x1' (Φ X b1 D z)) (Uc X b1 D) :=
    (OntoB.densF_continuousOn (X := X) (x0 := x1')).comp hΦc hmaps
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : V (nd X)) ρ0).exists_bound_of_continuousOn (hc.mono hsub)
  exact ⟨C, fun z hz => (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hC z hz)⟩

def Tset (x1 : Frame X.Ψ r) (ρ : ℝ) : Set (Frame X.Ψ r) :=
  (fun p : V (nd X) × Frame X.Ψ r => rmul (cpt X x1 p.1) p.2) '' (Metric.ball 0 ρ ×ˢ Bor X.Ψ r)

/- English proof (translation)
Establish `hTmem : ∀ {y c : Frame X.Ψ r}, c ∈ Bor X.Ψ r → (rmul y c ∈ Tset X (rmul x1' b1) ρ ↔ y ∈ Tset X (rmul x1' b1) ρ)` using `fun hc => KU.rmul_mem_S X (x0 := rmul x1' b1) (FF := Metric.ball 0 ρ) hc`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨z, b⟩, ⟨hz, hb⟩, rfl⟩`. Establish `hs` using `split X b1 D (hsub hz)`.

Use `show rmul (cpt X (rmul x1' b1) z) b ∈ _`. Rewrite using `[KU.rmul_mem_S X hb, hs.2.2]`. Conclude with `⟨(Φ X b1 D z, β X b1 D z), ⟨⟨z, hz, rfl⟩, hs.2.1⟩, rfl⟩`. Introduce and unpack `⟨⟨w, b⟩, ⟨⟨z, hz, rfl⟩, hb⟩, rfl⟩`. Establish `hs` using `split X b1 D (hsub hz)`.

Use `show rmul (cpt X x1' (Φ X b1 D z)) b ∈ Tset X (rmul x1' b1) ρ`. Rewrite using `[hTmem hb, ← MI.rmul_invF X (y := cpt X x1' (Φ X b1 D z)) hs.2.1, ← hs.2.2, hTmem (MI.invF_mem' X hs.2.1)]`. Conclude with `⟨(z, ExtFPf.oneF X), ⟨hz, ExtFPf.oneF_mem X⟩, ExtFPf.rmul_oneF X _⟩`.
-/
theorem Tset_eq {ρ : ℝ} (hsub : Metric.ball (0 : V (nd X)) ρ ⊆ Uc X b1 D) :
    Tset X (rmul x1' b1) ρ = KU.Sset X x1' (Φ X b1 D '' Metric.ball 0 ρ) := by
  have hTmem : ∀ {y c : Frame X.Ψ r}, c ∈ Bor X.Ψ r →
      (rmul y c ∈ Tset X (rmul x1' b1) ρ ↔ y ∈ Tset X (rmul x1' b1) ρ) := fun hc =>
    KU.rmul_mem_S X (x0 := rmul x1' b1) (FF := Metric.ball 0 ρ) hc
  ext y
  constructor
  · rintro ⟨⟨z, b⟩, ⟨hz, hb⟩, rfl⟩
    have hs := split X b1 D (hsub hz)
    show rmul (cpt X (rmul x1' b1) z) b ∈ _
    rw [KU.rmul_mem_S X hb, hs.2.2]
    exact ⟨(Φ X b1 D z, β X b1 D z), ⟨⟨z, hz, rfl⟩, hs.2.1⟩, rfl⟩
  · rintro ⟨⟨w, b⟩, ⟨⟨z, hz, rfl⟩, hb⟩, rfl⟩
    have hs := split X b1 D (hsub hz)
    show rmul (cpt X x1' (Φ X b1 D z)) b ∈ Tset X (rmul x1' b1) ρ
    rw [hTmem hb, ← MI.rmul_invF X (y := cpt X x1' (Φ X b1 D z)) hs.2.1, ← hs.2.2,
      hTmem (MI.invF_mem' X hs.2.1)]
    exact ⟨(z, ExtFPf.oneF X), ⟨hz, ExtFPf.oneF_mem X⟩, ExtFPf.rmul_oneF X _⟩

/- English proof (translation)
Conclude with `measurableSet_ball.image_of_continuousOn_injOn ((Φ_diffOn X b1 D).continuousOn.mono hsub) ((Φ_injOn X b1 D hx1).mono hsub)`.
-/
theorem meas_image {ρ : ℝ} (hsub : Metric.ball (0 : V (nd X)) ρ ⊆ Uc X b1 D) (hx1 : rmul x1' b1 ∈ X.dom) :
    MeasurableSet (Φ X b1 D '' Metric.ball 0 ρ) := by
  exact measurableSet_ball.image_of_continuousOn_injOn ((Φ_diffOn X b1 D).continuousOn.mono hsub)
    ((Φ_injOn X b1 D hx1).mono hsub)

/- English proof (translation)
Rewrite using `[Tset_eq X b1 D hsub]`. Conclude with `KU.meas_S X ho' (meas_image X b1 D hsub hx1)`.
-/
theorem meas_Tset (ho' : IsOrth X x1') {ρ : ℝ} (hsub : Metric.ball (0 : V (nd X)) ρ ⊆ Uc X b1 D)
    (hx1 : rmul x1' b1 ∈ X.dom) : MeasurableSet (Tset X (rmul x1' b1) ρ) := by
  rw [Tset_eq X b1 D hsub]
  exact KU.meas_S X ho' (meas_image X b1 D hsub hx1)

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.LUB
