import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Adapted
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryEmbeddingStabilizer
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralRealUnitaryHaarEqProdUpqHaar

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PackGlob

open GlobalTheory.PackLoc

variable {D : D7}

/- English proof (translation)
Establish `hth : θ = Formalism.IndefR.Eqv.thetaC D` using `(GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).1 θ _ hθ (Formalism.IndefR.Eqv.isInfFam_thetaC D)`. Set `e` to `GlobalTheory.HaarReal.eqv M₀`. Set `eM : GinfC Y ≃ᵐ (∀ τ, Formalism.REAL.UJ (M₀.ε τ))` to `e.toHomeomorph.toMeasurableEquiv`. Establish `hc : ∀ (g : GinfC Y) τ, GlobalTheory.SepPer.cmp θ τ (g : GA D Y) = ptY M₀ τ (eM g τ)`. Introduce `g τ`.

Rewrite using `[hth]`. Conclude with `(GlobalTheory.HaarReal.ofFr_eqv M₀ g τ).symm`. Set `μP : Measure (∀ τ, Formalism.REAL.UJ (M₀.ε τ))` to `Measure.pi fun τ => Formalism.REAL.muG (M₀.ε τ)`. Establish `hmapE : m.map e = Measure.haarScalarFactor (m.map e) μP • μP` using `Measure.isMulLeftInvariant_eq_smul_of_regular (Measure.map (⇑e) m) μP`. Establish `hmapM : m.map eM = Measure.haarScalarFactor (m.map e) μP • μP` using `hmapE`.

Use `⟨(Measure.haarScalarFactor (m.map e) μP : ℝ), by exact_mod_cast Measure.haarScalarFactor_pos_of_isHaarMeasure _ _, ?_⟩` and prove the remaining obligations. Introduce `𝕜 _ F`. Establish `hP : ∀ g : GinfC Y, (∏ τ, F τ (GlobalTheory.SepPer.cmp θ τ (g : GA D Y))) = (fun x : (∀ τ, Formalism.REAL.UJ (M₀.ε τ)) => ∏ τ, F τ (ptY M₀ τ (x τ))) (eM g)` using `fun g => Finset.prod_congr rfl fun τ _ => congrArg (F τ) (hc g τ)`. Use `⟨fun hF => ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : Integrable (fun x : (∀ τ, Formalism.REAL.UJ (M₀.ε τ)) => ∏ τ, F τ (ptY M₀ τ (x τ))) μP` using `Integrable.fintype_prod_dep (f := fun τ u => F τ (ptY M₀ τ u)) hF`.

Establish `h2 : Integrable (fun x : (∀ τ, Formalism.REAL.UJ (M₀.ε τ)) => ∏ τ, F τ (ptY M₀ τ (x τ))) (m.map eM)`. Rewrite using `[hmapM]`. Conclude with `h1.smul_measure_nnreal`. Conclude with `(integrable_congr (ae_of_all _ hP)).2 ((integrable_map_equiv eM (fun x : (∀ τ, Formalism.REAL.UJ (M₀.ε τ)) => ∏ τ, F τ (ptY M₀ τ (x τ)))).1 h2)`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hmapM, integral_smul_nnreal_measure]`. Use `_ = _ := by`. Rewrite using `[integral_fintype_prod_eq_prod (f := fun τ u => F τ (ptY M₀ τ u)), NNReal.smul_def]`.
-/
theorem haar_prod {Y : HSp D} {S' : D.what₂.Tau → SPar} (M₀ : DSModel Y S') {θ : InfFam D} (hθ : IsInfFam θ)
    (m : Measure (GinfC Y)) (hm : m.IsHaarMeasure) : ∃ κ : ℝ, 0 < κ ∧ ∀ (𝕜 : Type) [RCLike 𝕜]
      (F : D.what₂.Tau → Matrix (Fin Y.rank) (Fin Y.rank) ℂ → 𝕜),
      ((∀ τ, Integrable (fun u => F τ (ptY M₀ τ u)) (Formalism.REAL.muG (M₀.ε τ))) →
        Integrable (fun h : GinfC Y => ∏ τ, F τ (GlobalTheory.SepPer.cmp θ τ (h : GA D Y))) m) ∧
      ∫ h : GinfC Y, ∏ τ, F τ (GlobalTheory.SepPer.cmp θ τ (h : GA D Y)) ∂m =
        κ • ∏ τ, ∫ u, F τ (ptY M₀ τ u) ∂(Formalism.REAL.muG (M₀.ε τ)) := by
  classical
  have hth : θ = Formalism.IndefR.Eqv.thetaC D := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).1 θ _ hθ (Formalism.IndefR.Eqv.isInfFam_thetaC D)
  let e := GlobalTheory.HaarReal.eqv M₀
  let eM : GinfC Y ≃ᵐ (∀ τ, Formalism.REAL.UJ (M₀.ε τ)) := e.toHomeomorph.toMeasurableEquiv
  have hc : ∀ (g : GinfC Y) τ, GlobalTheory.SepPer.cmp θ τ (g : GA D Y) = ptY M₀ τ (eM g τ) := by
    intro g τ
    rw [hth]
    exact (GlobalTheory.HaarReal.ofFr_eqv M₀ g τ).symm
  let μP : Measure (∀ τ, Formalism.REAL.UJ (M₀.ε τ)) := Measure.pi fun τ => Formalism.REAL.muG (M₀.ε τ)
  have hmapE : m.map e = Measure.haarScalarFactor (m.map e) μP • μP := Measure.isMulLeftInvariant_eq_smul_of_regular (Measure.map (⇑e) m) μP
  have hmapM : m.map eM = Measure.haarScalarFactor (m.map e) μP • μP := hmapE
  refine ⟨(Measure.haarScalarFactor (m.map e) μP : ℝ), by exact_mod_cast Measure.haarScalarFactor_pos_of_isHaarMeasure _ _, ?_⟩
  intro 𝕜 _ F
  have hP : ∀ g : GinfC Y, (∏ τ, F τ (GlobalTheory.SepPer.cmp θ τ (g : GA D Y))) =
      (fun x : (∀ τ, Formalism.REAL.UJ (M₀.ε τ)) => ∏ τ, F τ (ptY M₀ τ (x τ))) (eM g) := fun g =>
    Finset.prod_congr rfl fun τ _ => congrArg (F τ) (hc g τ)
  refine ⟨fun hF => ?_, ?_⟩
  · have h1 : Integrable (fun x : (∀ τ, Formalism.REAL.UJ (M₀.ε τ)) => ∏ τ, F τ (ptY M₀ τ (x τ))) μP :=
      Integrable.fintype_prod_dep (f := fun τ u => F τ (ptY M₀ τ u)) hF
    have h2 : Integrable (fun x : (∀ τ, Formalism.REAL.UJ (M₀.ε τ)) => ∏ τ, F τ (ptY M₀ τ (x τ))) (m.map eM) := by
      rw [hmapM]
      exact h1.smul_measure_nnreal
    exact (integrable_congr (ae_of_all _ hP)).2 ((integrable_map_equiv eM (fun x : (∀ τ, Formalism.REAL.UJ (M₀.ε τ)) => ∏ τ, F τ (ptY M₀ τ (x τ)))).1 h2)
  · calc ∫ g : GinfC Y, ∏ τ, F τ (GlobalTheory.SepPer.cmp θ τ (g : GA D Y)) ∂m
        = ∫ g : GinfC Y, (fun x : (∀ τ, Formalism.REAL.UJ (M₀.ε τ)) => ∏ τ, F τ (ptY M₀ τ (x τ))) (eM g) ∂m :=
          integral_congr_ae (ae_of_all _ hP)
      _ = ∫ x, ∏ τ, F τ (ptY M₀ τ (x τ)) ∂(m.map eM) := (integral_map_equiv eM (fun x : (∀ τ, Formalism.REAL.UJ (M₀.ε τ)) => ∏ τ, F τ (ptY M₀ τ (x τ)))).symm
      _ = (Measure.haarScalarFactor (m.map e) μP) • ∫ x, ∏ τ, F τ (ptY M₀ τ (x τ)) ∂μP := by
          rw [hmapM, integral_smul_nnreal_measure]
      _ = _ := by
          rw [integral_fintype_prod_eq_prod (f := fun τ u => F τ (ptY M₀ τ u)), NNReal.smul_def]

/- English proof (translation)
Unfold `GlobalTheory.SepPer.cmp infMat`. Rewrite using `[Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.HA_mat_mul, Units.val_mul]`. Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, Matrix.mul_apply, map_sum, map_mul]`.
-/
theorem cmp_mul (θ : InfFam D) {V : HSp D} (τ : D.what₂.Tau) (g h : GA D V) :
    GlobalTheory.SepPer.cmp θ τ (g * h) = GlobalTheory.SepPer.cmp θ τ g * GlobalTheory.SepPer.cmp θ τ h := by
  unfold GlobalTheory.SepPer.cmp infMat
  rw [Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.HA_mat_mul, Units.val_mul]
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, map_sum, map_mul]

/- English proof (translation)
Unfold `GlobalTheory.SepPer.cmp infMat`. Rewrite using `[Matrix.map_map]`. Both sides reduce to the same expression.
-/
private theorem cmp_eq_map (θ : InfFam D) {V : HSp D} (τ : D.what₂.Tau) (x : GA D V) :
    GlobalTheory.SepPer.cmp θ τ x = (matHom V x).1.map
      ((θ τ).comp (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom) := by
  unfold GlobalTheory.SepPer.cmp infMat
  rw [Matrix.map_map]
  rfl

/- English proof (translation)
Establish `hRP` using `(GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ Y`. Establish `hU : GlobalTheory.SepPer.cmp θ τ h ∈ Formalism.QuantumDeterminants.UH (gramAt D Y τ)` using `GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ Y h τ`. Establish `hex : ∃ x, IsAtTau θ Y τ (GlobalTheory.SepPer.cmp θ τ h) x` using `((GlobalTheory.PointAtPlaceHom.atTau_laws D θ hθ Y τ).1 _ hU).exists`. Establish `hk : IsAtTau θ Y τ (GlobalTheory.SepPer.cmp θ τ h) (atTau θ Y τ (GlobalTheory.SepPer.cmp θ τ h))`. Unfold `atTau`.

Rewrite using `[dif_pos hex]`. Conclude with `hex.choose_spec`. Use `set k := atTau θ Y τ (GlobalTheory.SepPer.cmp θ τ h) with hkdef`. Establish `h1 : GlobalTheory.SepPer.cmp θ τ (1 : GA D Y) = 1` using `hRP.2.2.2.2.1 1 (one_mem _) τ`. Establish `hkc : GlobalTheory.SepPer.cmp θ τ k = GlobalTheory.SepPer.cmp θ τ h` using `hk.2.1`.

Establish `hk1 : GlobalTheory.SepPer.cmp θ τ (h * k⁻¹) = 1`. Combine the equalities or inequalities in the displayed calculation. Establish `hA : GlobalTheory.SepPer.cmp θ τ (stabilizerEmbedding d (h * k⁻¹)) = 1`. Rewrite `hk1`, the goal using `[cmp_eq_map]`. Conclude with `(GlobalTheory.UnitaryEmbeddingGroup.map_eq_one_iff d _ (h * k⁻¹)).1 hk1`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul, inv_mul_cancel_right]`. Use `_ = GlobalTheory.SepPer.cmp θ τ (stabilizerEmbedding d (h * k⁻¹)) * GlobalTheory.SepPer.cmp θ τ (stabilizerEmbedding d k) := cmp_mul θ τ _ _`. Use `_ = GlobalTheory.SepPer.cmp θ τ (stabilizerEmbedding d k) := by rw [hA, one_mul]`. Use `_ = embAt θ d τ (GlobalTheory.SepPer.cmp θ τ h) := rfl`.
-/
theorem component_of_auxiliary_embedding {θ : InfFam D} (hθ : IsInfFam θ) {Y V : HSp D} (d : HermitianOrthogonalExtensionData Y V 1 1) (τ : D.what₂.Tau) (h : GA D Y) :
    GlobalTheory.SepPer.cmp θ τ (stabilizerEmbedding d h) = embAt θ d τ (GlobalTheory.SepPer.cmp θ τ h) := by
  have hRP := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ Y
  have hU : GlobalTheory.SepPer.cmp θ τ h ∈ Formalism.QuantumDeterminants.UH (gramAt D Y τ) :=
    GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ Y h τ
  have hex : ∃ x, IsAtTau θ Y τ (GlobalTheory.SepPer.cmp θ τ h) x :=
    ((GlobalTheory.PointAtPlaceHom.atTau_laws D θ hθ Y τ).1 _ hU).exists
  have hk : IsAtTau θ Y τ (GlobalTheory.SepPer.cmp θ τ h) (atTau θ Y τ (GlobalTheory.SepPer.cmp θ τ h)) := by
    unfold atTau
    rw [dif_pos hex]
    exact hex.choose_spec
  set k := atTau θ Y τ (GlobalTheory.SepPer.cmp θ τ h) with hkdef
  have h1 : GlobalTheory.SepPer.cmp θ τ (1 : GA D Y) = 1 := hRP.2.2.2.2.1 1 (one_mem _) τ
  have hkc : GlobalTheory.SepPer.cmp θ τ k = GlobalTheory.SepPer.cmp θ τ h := hk.2.1
  have hk1 : GlobalTheory.SepPer.cmp θ τ (h * k⁻¹) = 1 := by
    calc GlobalTheory.SepPer.cmp θ τ (h * k⁻¹) = GlobalTheory.SepPer.cmp θ τ h * GlobalTheory.SepPer.cmp θ τ k⁻¹ := cmp_mul θ τ h k⁻¹
      _ = GlobalTheory.SepPer.cmp θ τ k * GlobalTheory.SepPer.cmp θ τ k⁻¹ := by rw [hkc]
      _ = GlobalTheory.SepPer.cmp θ τ (k * k⁻¹) := (cmp_mul θ τ k k⁻¹).symm
      _ = 1 := by rw [mul_inv_cancel, h1]
  have hA : GlobalTheory.SepPer.cmp θ τ (stabilizerEmbedding d (h * k⁻¹)) = 1 := by
    rw [cmp_eq_map] at hk1 ⊢
    exact (GlobalTheory.UnitaryEmbeddingGroup.map_eq_one_iff d _ (h * k⁻¹)).1 hk1
  calc GlobalTheory.SepPer.cmp θ τ (stabilizerEmbedding d h) = GlobalTheory.SepPer.cmp θ τ (stabilizerEmbedding d (h * k⁻¹) * stabilizerEmbedding d k) := by
        rw [← GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul, inv_mul_cancel_right]
    _ = GlobalTheory.SepPer.cmp θ τ (stabilizerEmbedding d (h * k⁻¹)) * GlobalTheory.SepPer.cmp θ τ (stabilizerEmbedding d k) := cmp_mul θ τ _ _
    _ = GlobalTheory.SepPer.cmp θ τ (stabilizerEmbedding d k) := by rw [hA, one_mul]
    _ = embAt θ d τ (GlobalTheory.SepPer.cmp θ τ h) := rfl

/- English proof (translation)
Unfold `oneP atTau`. Use `split_ifs with hx`. Conclude with `hx.choose_spec.2.2 τ' hne`. Unfold `GlobalTheory.SepPer.cmp infMat`. Rewrite using `[Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.HA_mat_one, Units.val_one]`.

Use extensionality with `i j`. Simplify using `[Matrix.one_apply]`.
-/
theorem cmp_oneP_eq_one_of_ne (θ : InfFam D) {Y : HSp D} {τ τ' : D.what₂.Tau} (hne : τ' ≠ τ) (X : Matrix (Fin Y.rank) (Fin Y.rank) ℂ)
    (s : ℝ) : GlobalTheory.SepPer.cmp θ τ' (oneP θ Y τ X s) = 1 := by
  unfold oneP atTau
  split_ifs with hx
  · exact hx.choose_spec.2.2 τ' hne
  · unfold GlobalTheory.SepPer.cmp infMat
    rw [Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.HA_mat_one, Units.val_one]
    ext i j
    simp [Matrix.one_apply]

/- English proof (translation)
Take `⟨x, hx, hxc⟩` from `((GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ V).2.1 g hg`. Conclude with `⟨x, hx, hxc⟩`.
-/
theorem exists_real {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} (g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hg : ∀ τ, g τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) : ∃ x ∈ GinfC V, ∀ τ, GlobalTheory.SepPer.cmp θ τ x = g τ := by
  obtain ⟨x, hx, hxc⟩ := ((GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ V).2.1 g hg
  exact ⟨x, hx, hxc⟩

/- English proof (translation)
Unfold `eu`. Check the signs of the components of the expression.
-/
theorem eu_nonneg {n : ℕ} (y : Fin n → ℂ) : 0 ≤ eu y := by
  unfold eu
  positivity

/- English proof (translation)
Establish `ha : ∏ σ, a σ = a τ * ∏ σ ∈ ({τ}ᶜ : Finset ι), b σ`. Rewrite using `[Fintype.prod_eq_mul_prod_compl τ]`. Use `congr 1`. Use `Finset.prod_congr rfl fun σ hσ => h σ ?_` and prove the remaining obligations. Simplify using `using hσ`.

Establish `hb : ∏ σ, b σ = b τ * ∏ σ ∈ ({τ}ᶜ : Finset ι), b σ` using `Fintype.prod_eq_mul_prod_compl τ _`. Establish `hr : (∏ σ, if σ = τ then ‖a σ - b σ‖ else ‖b σ‖) = ‖a τ - b τ‖ * ∏ σ ∈ ({τ}ᶜ : Finset ι), ‖b σ‖`. Rewrite using `[Fintype.prod_eq_mul_prod_compl τ, if_pos rfl]`. Use `congr 1`. Use `Finset.prod_congr rfl fun σ hσ => ?_` and prove the remaining obligations.

Rewrite using `[if_neg (by simpa using hσ)]`. Rewrite using `[ha, hb, hr, ← sub_mul, norm_mul, norm_prod]`.
-/
theorem norm_prod_sub {ι : Type} [Fintype ι] [DecidableEq ι] (a b : ι → ℂ) (τ : ι) (h : ∀ σ, σ ≠ τ → a σ = b σ) :
    ‖∏ σ, a σ - ∏ σ, b σ‖ = ∏ σ, if σ = τ then ‖a σ - b σ‖ else ‖b σ‖ := by
  have ha : ∏ σ, a σ = a τ * ∏ σ ∈ ({τ}ᶜ : Finset ι), b σ := by
    rw [Fintype.prod_eq_mul_prod_compl τ]
    congr 1
    refine Finset.prod_congr rfl fun σ hσ => h σ ?_
    simpa using hσ
  have hb : ∏ σ, b σ = b τ * ∏ σ ∈ ({τ}ᶜ : Finset ι), b σ := Fintype.prod_eq_mul_prod_compl τ _
  have hr : (∏ σ, if σ = τ then ‖a σ - b σ‖ else ‖b σ‖) = ‖a τ - b τ‖ * ∏ σ ∈ ({τ}ᶜ : Finset ι), ‖b σ‖ := by
    rw [Fintype.prod_eq_mul_prod_compl τ, if_pos rfl]
    congr 1
    refine Finset.prod_congr rfl fun σ hσ => ?_
    rw [if_neg (by simpa using hσ)]
  rw [ha, hb, hr, ← sub_mul, norm_mul, norm_prod]

/- English proof (translation)
Introduce `D θ hθ Y V d S S' M₀ M q εA A εB B v₀ g₀ w c hL`. Take `⟨x₀, hx₀, hx₀c⟩` from `exists_real hθ g₀ fun τ => (hL τ).real`. Set `p : Pack M₀ M` to `⟨⟨εA, A, fun τ => (hL τ).unitA, fun τ => (hL τ).gramA⟩, ⟨εB, B, fun τ => (hL τ).unitB, fun τ => (hL τ).gramB⟩, v₀, x₀, fun τ => ⟨w τ, (hL τ).sm⟩⟩`. Establish `hpv : ∀ τ, p.v θ τ = M.rep τ (g₀ τ) (v₀ τ)` using `fun τ => by show M.rep τ (GlobalTheory.SepPer.cmp θ τ x₀) (v₀ τ) = _`. Rewrite using `[hx₀c τ]`.

Establish `hco : ∀ (g : GA D V) (h : GA D Y), coefR θ M (p.v θ) (p.v θ) (g * stabilizerEmbedding d h) = ∏ τ, mco M τ (g₀ τ) (v₀ τ) (GlobalTheory.SepPer.cmp θ τ g * embAt θ d τ (GlobalTheory.SepPer.cmp θ τ h))`. Introduce `g h`. Unfold `GlobalTheory.SepPer.coefR`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[hpv τ, cmp_mul, component_of_auxiliary_embedding hθ]`.

Both sides reduce to the same expression. Establish `hco1 : ∀ h : GA D Y, coefR θ M (p.v θ) (p.v θ) (stabilizerEmbedding d h) = ∏ τ, mco M τ (g₀ τ) (v₀ τ) (embAt θ d τ (GlobalTheory.SepPer.cmp θ τ h))`. Introduce `h`. Unfold `GlobalTheory.SepPer.coefR`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations.

Rewrite using `[hpv τ, component_of_auxiliary_embedding hθ]`. Both sides reduce to the same expression. Use `⟨p, ?_⟩` and prove the remaining obligations. Unfold `GlobalTheory.SepPer.Pack.Is`. Use `⟨⟨fun τ y a => (hL τ).adapted y a, hx₀, fun τ => ⟨(hL τ).kfin, (hL τ).dec⟩, fun τ => (hL τ).ne⟩, ?_⟩` and prove the remaining obligations.

Introduce `m hm`. Take `⟨κ, hκ, hK⟩` from `haar_prod M₀ hθ m hm`. Use `⟨(κ : ℂ) * ∏ τ, c τ, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `mul_ne_zero (by exact_mod_cast hκ.ne') (Finset.prod_ne_zero_iff.2 fun τ _ => (hL τ).cne)`. Introduce `b`.

Establish `e1 : ∀ h : GinfC Y, coefR θ M (p.v θ) (p.v θ) (stabilizerEmbedding d (h : GA D Y)) * coefR θ M₀ b (fun τ => (p.w τ : M₀.H τ)) (h : GA D Y) = ∏ τ, (fun τ X => mco M τ (g₀ τ) (v₀ τ) (embAt θ d τ X) * ⟪b τ, M₀.rep τ X (w τ)⟫_ℂ) τ (GlobalTheory.SepPer.cmp θ τ (h : GA D Y))`. Introduce `h`. Rewrite using `[hco1]`. Unfold `GlobalTheory.SepPer.coefR`. Rewrite using `[← Finset.prod_mul_distrib]`.

Use `(integral_congr_ae (ae_of_all _ e1)).trans ?_` and prove the remaining obligations. Rewrite using `[(hK ℂ (fun τ X => mco M τ (g₀ τ) (v₀ τ) (embAt θ d τ X) * ⟪b τ, M₀.rep τ X (w τ)⟫_ℂ)).2]`. Rewrite using `[show (∏ τ, ∫ u, (fun τ X => mco M τ (g₀ τ) (v₀ τ) (embAt θ d τ X) * ⟪b τ, M₀.rep τ X (w τ)⟫_ℂ) τ (ptY M₀ τ u) ∂(Formalism.REAL.muG (M₀.ε τ))) = ∏ τ, (c τ * ⟪b τ, w τ⟫_ℂ) from Finset.prod_congr rfl fun τ _ => (hL τ).act (b τ)]`. Use `show (κ : ℝ) • ∏ τ, (c τ * ⟪b τ, w τ⟫_ℂ) = ((κ : ℂ) * ∏ τ, c τ) * ∏ τ, ⟪b τ, w τ⟫_ℂ`. Rewrite using `[Finset.prod_mul_distrib, Complex.real_smul]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `g`. Establish `hgU : ∀ τ, GlobalTheory.SepPer.cmp θ τ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)` using `fun τ => GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V g τ`. Establish `e2 : ∀ h : GinfC Y, coefR θ M (p.v θ) (p.v θ) (g * stabilizerEmbedding d (h : GA D Y)) = ∏ τ, (fun τ X => mco M τ (g₀ τ) (v₀ τ) (GlobalTheory.SepPer.cmp θ τ g * embAt θ d τ X)) τ (GlobalTheory.SepPer.cmp θ τ (h : GA D Y))` using `fun h => hco g h`. Establish `e3 : ∀ h : GinfC Y, ‖coefR θ M (p.v θ) (p.v θ) (g * stabilizerEmbedding d (h : GA D Y))‖ = ∏ τ, (fun τ X => ‖mco M τ (g₀ τ) (v₀ τ) (GlobalTheory.SepPer.cmp θ τ g * embAt θ d τ X)‖) τ (GlobalTheory.SepPer.cmp θ τ (h : GA D Y))`.

Introduce `h`. Rewrite using `[hco g h, norm_prod]`. Use `⟨(integrable_congr (ae_of_all _ e2)).2 ((hK ℂ (fun τ X => mco M τ (g₀ τ) (v₀ τ) (GlobalTheory.SepPer.cmp θ τ g * embAt θ d τ X))).1 fun τ => ((hL τ).far _ (hgU τ)).1), ?_⟩` and prove the remaining obligations. Establish `hN : ∀ τ, nrm θ p.B g⁻¹ τ (zv d) = eu (B τ *ᵥ (GlobalTheory.SepPer.cmp θ τ g *ᵥ fun i => tauE D τ (zv d i)))`. Introduce `τ`.

Unfold `nrm`. Rewrite using `[inv_inv]`. Establish `hI : (∫ h : GinfC Y, ‖coefR θ M (p.v θ) (p.v θ) (g * stabilizerEmbedding d (h : GA D Y))‖ ∂m) = κ * ∏ τ, ∫ u, ‖mco M τ (g₀ τ) (v₀ τ) (GlobalTheory.SepPer.cmp θ τ g * embAt θ d τ (ptY M₀ τ u))‖ ∂(Formalism.REAL.muG (M₀.ε τ))` using `(integral_congr_ae (ae_of_all _ e3)).trans ((hK ℝ (fun τ X => ‖mco M τ (g₀ τ) (v₀ τ) (GlobalTheory.SepPer.cmp θ τ g * embAt θ d τ X)‖)).2.trans (smul_eq_mul _ _))`. Rewrite using `[hI, Finset.prod_congr rfl fun τ _ => hN τ, ← Finset.prod_pow, mul_assoc, ← Finset.prod_mul_distrib]`. Establish `hle : ∏ τ, ((∫ u, ‖mco M τ (g₀ τ) (v₀ τ) (GlobalTheory.SepPer.cmp θ τ g * embAt θ d τ (ptY M₀ τ u))‖ ∂(Formalism.REAL.muG (M₀.ε τ))) * eu (B τ *ᵥ (GlobalTheory.SepPer.cmp θ τ g *ᵥ fun i => tauE D τ (zv d i))) ^ (2 * V.rank + 5)) ≤ ∏ τ, (Real.exp q * ‖c τ‖)` using `Finset.prod_le_prod (fun τ _ => mul_nonneg (integral_nonneg fun _ => norm_nonneg _) (pow_nonneg (eu_nonneg _) _)) fun τ _ => ((hL τ).far _ (hgU τ)).2`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul, norm_mul, Complex.norm_real, norm_prod, Real.norm_eq_abs, abs_of_pos hκ]`. Expand and normalize the polynomial expressions, which then agree. Introduce `τ X hX s`. Establish `hcomp : ∀ (σ : D.what₂.Tau) (h : GA D Y), GlobalTheory.SepPer.cmp θ σ (oneP θ Y τ X s * h) = (if σ = τ then GlobalTheory.SepPer.cmp θ τ (oneP θ Y τ X s) else 1) * GlobalTheory.SepPer.cmp θ σ h`.

Introduce `σ h`. Rewrite using `[cmp_mul]`. Use `split_ifs with hσ`. Rewrite using `[hσ]`. Rewrite using `[cmp_oneP_eq_one_of_ne θ hσ X s]`.

Establish `e4 : ∀ h : GinfC Y, ‖coefR θ M (p.v θ) (p.v θ) (stabilizerEmbedding d (oneP θ Y τ X s * (h : GA D Y))) - coefR θ M (p.v θ) (p.v θ) (stabilizerEmbedding d (h : GA D Y))‖ = ∏ σ, (fun σ Z => if σ = τ then ‖mco M σ (g₀ σ) (v₀ σ) (embAt θ d σ (GlobalTheory.SepPer.cmp θ τ (oneP θ Y τ X …`. Introduce `h`. Rewrite using `[hco1, hco1, norm_prod_sub _ _ τ]`. Use `Finset.prod_congr rfl fun σ _ => ?_` and prove the remaining obligations. Distinguish the cases in `hσ : σ = τ`.

Substitute `hσ` using the available equality. Simplify using `only [↓reduceIte, hcomp]`. Simplify using `only [hσ, ↓reduceIte]`. Introduce `σ hσ`. Rewrite using `[hcomp, if_neg hσ, one_mul]`.

Establish `hb : ∀ σ, (∫ u, (fun σ Z => if σ = τ then ‖mco M σ (g₀ σ) (v₀ σ) (embAt θ d σ (GlobalTheory.SepPer.cmp θ τ (oneP θ Y τ X s) * Z)) - mco M σ (g₀ σ) (v₀ σ) (embAt θ d σ Z)‖ else ‖mco M σ (g₀ σ) (v₀ σ) (embAt θ d σ Z)‖) σ (ptY M₀ σ u) ∂(Formalism.REAL.muG (M₀.ε σ))) ≤ Real.exp q * ‖ …`. Introduce `σ`. Distinguish the cases in `hσ : σ = τ`. Substitute `hσ` using the available equality. Simplify using `only [↓reduceIte]`.

Simplify `((hL σ).lip X hX s).2` using `only [mul_assoc]`. Simplify using `only [hσ, ↓reduceIte, mul_one]`. Establish `h1U : (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) ∈ Formalism.QuantumDeterminants.UH (gramAt D V σ)` using `by show (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᴴ * gramAt D V σ * 1 = gramAt D V σ`. Simplify using the standard rewrite rules. Establish `hf` using `((hL σ).far 1 h1U).2`.

Establish `hz : eu (B σ *ᵥ ((1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) *ᵥ fun i => tauE D σ (zv d i))) = 1`. Establish `ha` using `(hL σ).adapted 0 1`. Rewrite `ha` using `[Matrix.mulVec_zero, Matrix.mulVec_zero, zero_add, one_smul, eu_zero, norm_one]`. Rewrite using `[Matrix.one_mulVec]`. Conclude with `(pow_eq_one_iff_of_nonneg (eu_nonneg _) two_ne_zero).1 (by simpa using ha)`.

Rewrite `hf` using `[hz, one_pow, mul_one]`. Simplify `hf` using `only [one_mul]`. Establish `hI : (∫ h : GinfC Y, ‖coefR θ M (p.v θ) (p.v θ) (stabilizerEmbedding d (oneP θ Y τ X s * (h : GA D Y))) - coefR θ M (p.v θ) (p.v θ) (stabilizerEmbedding d (h : GA D Y))‖ ∂m) = κ * ∏ σ, ∫ u, (fun σ Z => if σ = τ then ‖mco M σ (g₀ σ) (v₀ σ) (embAt θ d σ (GlobalTheory.SepPer.cmp θ τ …` using `(integral_congr_ae (ae_of_all _ e4)).trans ((hK ℝ (fun σ Z => if σ = τ then ‖mco M σ (g₀ σ) (v₀ σ) (embAt θ d σ (GlobalTheory.SepPer.cmp θ τ (oneP θ Y τ X s) * Z)) - mco M σ (g₀ σ) (v₀ σ) (embAt θ d σ Z)‖ else ‖mco M σ (g₀ σ) (v₀ σ) (embAt θ d σ Z)‖)).2.trans (smul_eq_mul _ _))`. Rewrite using `[hI]`. Apply the tactic sequence `have hle := Finset.prod_le_prod (s := Finset.univ) (fun σ _ => integral_nonneg fun u => by show (0 : ℝ) ≤ (if σ = τ then _ else _) split_ifs <;> exact norm_nonneg _) fun σ _ => hb σ`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_ite_eq', if_pos (Finset.mem_univ τ), Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul, norm_mul, Complex.norm_real, norm_prod, Real.norm_eq_abs, abs_of_pos hκ]`. Use `show _ = Real.exp (Fintype.card D.what₂.Tau * q) * (κ * ∏ σ, ‖c σ‖) * |s| * hsn (A τ * X * (A τ)⁻¹)`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pack_of_loc : ∀ {D : D7} (θ : InfFam D), IsInfFam θ → ∀ {Y V : HSp D} (d : HermitianOrthogonalExtensionData Y V 1 1) {S S' : D.what₂.Tau → SPar}
    (M₀ : DSModel Y S') (M : DSModel V S) (q : ℝ) (εA : D.what₂.Tau → Fin Y.rank → Bool)
    (A : D.what₂.Tau → Matrix (Fin Y.rank) (Fin Y.rank) ℂ) (εB : D.what₂.Tau → Fin V.rank → Bool)
    (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (v₀ : ∀ τ, M.H τ)
    (g₀ : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (w : ∀ τ, M₀.H τ) (c : D.what₂.Tau → ℂ),
    (∀ τ, GlobalTheory.PackLoc.LocOK θ d M₀ M τ q (εA τ) (A τ) (εB τ) (B τ) (v₀ τ) (g₀ τ) (w τ) (c τ)) →
      ∃ p : Pack M₀ M, p.Is θ d (Fintype.card D.what₂.Tau * q) := by
  intro D θ hθ Y V d S S' M₀ M q εA A εB B v₀ g₀ w c hL
  classical
  obtain ⟨x₀, hx₀, hx₀c⟩ := exists_real hθ g₀ fun τ => (hL τ).real
  let p : Pack M₀ M := ⟨⟨εA, A, fun τ => (hL τ).unitA, fun τ => (hL τ).gramA⟩,
    ⟨εB, B, fun τ => (hL τ).unitB, fun τ => (hL τ).gramB⟩, v₀, x₀, fun τ => ⟨w τ, (hL τ).sm⟩⟩
  have hpv : ∀ τ, p.v θ τ = M.rep τ (g₀ τ) (v₀ τ) := fun τ => by
    show M.rep τ (GlobalTheory.SepPer.cmp θ τ x₀) (v₀ τ) = _
    rw [hx₀c τ]
  have hco : ∀ (g : GA D V) (h : GA D Y), coefR θ M (p.v θ) (p.v θ) (g * stabilizerEmbedding d h) =
      ∏ τ, mco M τ (g₀ τ) (v₀ τ) (GlobalTheory.SepPer.cmp θ τ g * embAt θ d τ (GlobalTheory.SepPer.cmp θ τ h)) := by
    intro g h
    unfold GlobalTheory.SepPer.coefR
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [hpv τ, cmp_mul, component_of_auxiliary_embedding hθ]
    rfl
  have hco1 : ∀ h : GA D Y, coefR θ M (p.v θ) (p.v θ) (stabilizerEmbedding d h) =
      ∏ τ, mco M τ (g₀ τ) (v₀ τ) (embAt θ d τ (GlobalTheory.SepPer.cmp θ τ h)) := by
    intro h
    unfold GlobalTheory.SepPer.coefR
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [hpv τ, component_of_auxiliary_embedding hθ]
    rfl
  refine ⟨p, ?_⟩
  unfold GlobalTheory.SepPer.Pack.Is
  refine ⟨⟨fun τ y a => (hL τ).adapted y a, hx₀, fun τ => ⟨(hL τ).kfin, (hL τ).dec⟩, fun τ => (hL τ).ne⟩, ?_⟩
  intro m hm
  obtain ⟨κ, hκ, hK⟩ := haar_prod M₀ hθ m hm
  refine ⟨(κ : ℂ) * ∏ τ, c τ, ?_, ?_, ?_, ?_⟩
  · exact mul_ne_zero (by exact_mod_cast hκ.ne') (Finset.prod_ne_zero_iff.2 fun τ _ => (hL τ).cne)
  · intro b
    have e1 : ∀ h : GinfC Y, coefR θ M (p.v θ) (p.v θ) (stabilizerEmbedding d (h : GA D Y)) *
        coefR θ M₀ b (fun τ => (p.w τ : M₀.H τ)) (h : GA D Y) =
        ∏ τ, (fun τ X => mco M τ (g₀ τ) (v₀ τ) (embAt θ d τ X) * ⟪b τ, M₀.rep τ X (w τ)⟫_ℂ) τ
          (GlobalTheory.SepPer.cmp θ τ (h : GA D Y)) := by
      intro h
      rw [hco1]
      unfold GlobalTheory.SepPer.coefR
      rw [← Finset.prod_mul_distrib]
    refine (integral_congr_ae (ae_of_all _ e1)).trans ?_
    rw [(hK ℂ (fun τ X => mco M τ (g₀ τ) (v₀ τ) (embAt θ d τ X) * ⟪b τ, M₀.rep τ X (w τ)⟫_ℂ)).2]
    rw [show (∏ τ, ∫ u, (fun τ X => mco M τ (g₀ τ) (v₀ τ) (embAt θ d τ X) * ⟪b τ, M₀.rep τ X (w τ)⟫_ℂ) τ
        (ptY M₀ τ u) ∂(Formalism.REAL.muG (M₀.ε τ))) = ∏ τ, (c τ * ⟪b τ, w τ⟫_ℂ) from
      Finset.prod_congr rfl fun τ _ => (hL τ).act (b τ)]
    show (κ : ℝ) • ∏ τ, (c τ * ⟪b τ, w τ⟫_ℂ) = ((κ : ℂ) * ∏ τ, c τ) * ∏ τ, ⟪b τ, w τ⟫_ℂ
    rw [Finset.prod_mul_distrib, Complex.real_smul]
    ring
  · intro g
    have hgU : ∀ τ, GlobalTheory.SepPer.cmp θ τ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := fun τ =>
      GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V g τ
    have e2 : ∀ h : GinfC Y, coefR θ M (p.v θ) (p.v θ) (g * stabilizerEmbedding d (h : GA D Y)) =
        ∏ τ, (fun τ X => mco M τ (g₀ τ) (v₀ τ) (GlobalTheory.SepPer.cmp θ τ g * embAt θ d τ X)) τ
          (GlobalTheory.SepPer.cmp θ τ (h : GA D Y)) := fun h => hco g h
    have e3 : ∀ h : GinfC Y, ‖coefR θ M (p.v θ) (p.v θ) (g * stabilizerEmbedding d (h : GA D Y))‖ =
        ∏ τ, (fun τ X => ‖mco M τ (g₀ τ) (v₀ τ) (GlobalTheory.SepPer.cmp θ τ g * embAt θ d τ X)‖) τ
          (GlobalTheory.SepPer.cmp θ τ (h : GA D Y)) := by
      intro h
      rw [hco g h, norm_prod]
    refine ⟨(integrable_congr (ae_of_all _ e2)).2
      ((hK ℂ (fun τ X => mco M τ (g₀ τ) (v₀ τ) (GlobalTheory.SepPer.cmp θ τ g * embAt θ d τ X))).1
        fun τ => ((hL τ).far _ (hgU τ)).1), ?_⟩
    have hN : ∀ τ, nrm θ p.B g⁻¹ τ (zv d) =
        eu (B τ *ᵥ (GlobalTheory.SepPer.cmp θ τ g *ᵥ fun i => tauE D τ (zv d i))) := by
      intro τ
      unfold nrm
      rw [inv_inv]
    have hI : (∫ h : GinfC Y, ‖coefR θ M (p.v θ) (p.v θ) (g * stabilizerEmbedding d (h : GA D Y))‖ ∂m) =
        κ * ∏ τ, ∫ u, ‖mco M τ (g₀ τ) (v₀ τ) (GlobalTheory.SepPer.cmp θ τ g * embAt θ d τ (ptY M₀ τ u))‖
          ∂(Formalism.REAL.muG (M₀.ε τ)) :=
      (integral_congr_ae (ae_of_all _ e3)).trans
        ((hK ℝ (fun τ X => ‖mco M τ (g₀ τ) (v₀ τ) (GlobalTheory.SepPer.cmp θ τ g * embAt θ d τ X)‖)).2.trans
          (smul_eq_mul _ _))
    rw [hI, Finset.prod_congr rfl fun τ _ => hN τ, ← Finset.prod_pow, mul_assoc, ← Finset.prod_mul_distrib]
    have hle : ∏ τ, ((∫ u, ‖mco M τ (g₀ τ) (v₀ τ) (GlobalTheory.SepPer.cmp θ τ g * embAt θ d τ (ptY M₀ τ u))‖
          ∂(Formalism.REAL.muG (M₀.ε τ))) *
        eu (B τ *ᵥ (GlobalTheory.SepPer.cmp θ τ g *ᵥ fun i => tauE D τ (zv d i))) ^ (2 * V.rank + 5)) ≤
        ∏ τ, (Real.exp q * ‖c τ‖) :=
      Finset.prod_le_prod (fun τ _ => mul_nonneg (integral_nonneg fun _ => norm_nonneg _)
        (pow_nonneg (eu_nonneg _) _)) fun τ _ => ((hL τ).far _ (hgU τ)).2
    calc _ ≤ κ * ∏ τ, (Real.exp q * ‖c τ‖) := mul_le_mul_of_nonneg_left hle hκ.le
      _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul, norm_mul,
          Complex.norm_real, norm_prod, Real.norm_eq_abs, abs_of_pos hκ]
        ring
  · intro τ X hX s
    have hcomp : ∀ (σ : D.what₂.Tau) (h : GA D Y), GlobalTheory.SepPer.cmp θ σ (oneP θ Y τ X s * h) =
        (if σ = τ then GlobalTheory.SepPer.cmp θ τ (oneP θ Y τ X s) else 1) * GlobalTheory.SepPer.cmp θ σ h := by
      intro σ h
      rw [cmp_mul]
      split_ifs with hσ
      · rw [hσ]
      · rw [cmp_oneP_eq_one_of_ne θ hσ X s]
    have e4 : ∀ h : GinfC Y, ‖coefR θ M (p.v θ) (p.v θ) (stabilizerEmbedding d (oneP θ Y τ X s * (h : GA D Y))) -
        coefR θ M (p.v θ) (p.v θ) (stabilizerEmbedding d (h : GA D Y))‖ =
        ∏ σ, (fun σ Z => if σ = τ then
            ‖mco M σ (g₀ σ) (v₀ σ) (embAt θ d σ (GlobalTheory.SepPer.cmp θ τ (oneP θ Y τ X s) * Z)) -
              mco M σ (g₀ σ) (v₀ σ) (embAt θ d σ Z)‖
          else ‖mco M σ (g₀ σ) (v₀ σ) (embAt θ d σ Z)‖) σ (GlobalTheory.SepPer.cmp θ σ (h : GA D Y)) := by
      intro h
      rw [hco1, hco1, norm_prod_sub _ _ τ]
      · refine Finset.prod_congr rfl fun σ _ => ?_
        by_cases hσ : σ = τ
        · subst hσ
          simp only [↓reduceIte, hcomp]
        · simp only [hσ, ↓reduceIte]
      · intro σ hσ
        rw [hcomp, if_neg hσ, one_mul]
    have hb : ∀ σ, (∫ u, (fun σ Z => if σ = τ then
            ‖mco M σ (g₀ σ) (v₀ σ) (embAt θ d σ (GlobalTheory.SepPer.cmp θ τ (oneP θ Y τ X s) * Z)) -
              mco M σ (g₀ σ) (v₀ σ) (embAt θ d σ Z)‖
          else ‖mco M σ (g₀ σ) (v₀ σ) (embAt θ d σ Z)‖) σ (ptY M₀ σ u) ∂(Formalism.REAL.muG (M₀.ε σ))) ≤
        Real.exp q * ‖c σ‖ * (if σ = τ then |s| * hsn (A τ * X * (A τ)⁻¹) else 1) := by
      intro σ
      by_cases hσ : σ = τ
      · subst hσ
        simp only [↓reduceIte]
        simpa only [mul_assoc] using ((hL σ).lip X hX s).2
      · simp only [hσ, ↓reduceIte, mul_one]
        have h1U : (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) ∈ Formalism.QuantumDeterminants.UH (gramAt D V σ) := by
          show (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᴴ * gramAt D V σ * 1 = gramAt D V σ
          simp
        have hf := ((hL σ).far 1 h1U).2
        have hz : eu (B σ *ᵥ ((1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) *ᵥ fun i => tauE D σ (zv d i))) = 1 := by
          have ha := (hL σ).adapted 0 1
          rw [Matrix.mulVec_zero, Matrix.mulVec_zero, zero_add, one_smul, eu_zero, norm_one] at ha
          rw [Matrix.one_mulVec]
          exact (pow_eq_one_iff_of_nonneg (eu_nonneg _) two_ne_zero).1 (by simpa using ha)
        rw [hz, one_pow, mul_one] at hf
        simpa only [one_mul] using hf
    have hI : (∫ h : GinfC Y, ‖coefR θ M (p.v θ) (p.v θ) (stabilizerEmbedding d (oneP θ Y τ X s * (h : GA D Y))) -
        coefR θ M (p.v θ) (p.v θ) (stabilizerEmbedding d (h : GA D Y))‖ ∂m) =
        κ * ∏ σ, ∫ u, (fun σ Z => if σ = τ then
            ‖mco M σ (g₀ σ) (v₀ σ) (embAt θ d σ (GlobalTheory.SepPer.cmp θ τ (oneP θ Y τ X s) * Z)) -
              mco M σ (g₀ σ) (v₀ σ) (embAt θ d σ Z)‖
          else ‖mco M σ (g₀ σ) (v₀ σ) (embAt θ d σ Z)‖) σ (ptY M₀ σ u) ∂(Formalism.REAL.muG (M₀.ε σ)) :=
      (integral_congr_ae (ae_of_all _ e4)).trans ((hK ℝ (fun σ Z => if σ = τ then
            ‖mco M σ (g₀ σ) (v₀ σ) (embAt θ d σ (GlobalTheory.SepPer.cmp θ τ (oneP θ Y τ X s) * Z)) -
              mco M σ (g₀ σ) (v₀ σ) (embAt θ d σ Z)‖
          else ‖mco M σ (g₀ σ) (v₀ σ) (embAt θ d σ Z)‖)).2.trans (smul_eq_mul _ _))
    rw [hI]
    have hle := Finset.prod_le_prod (s := Finset.univ) (fun σ _ => integral_nonneg fun u => by
      show (0 : ℝ) ≤ (if σ = τ then _ else _)
      split_ifs <;> exact norm_nonneg _) fun σ _ => hb σ
    calc _ ≤ κ * ∏ σ, (Real.exp q * ‖c σ‖ * (if σ = τ then |s| * hsn (A τ * X * (A τ)⁻¹) else 1)) :=
          mul_le_mul_of_nonneg_left hle hκ.le
      _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_ite_eq', if_pos (Finset.mem_univ τ), Finset.prod_mul_distrib,
          Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul, norm_mul, Complex.norm_real, norm_prod,
          Real.norm_eq_abs, abs_of_pos hκ]
        show _ = Real.exp (Fintype.card D.what₂.Tau * q) * (κ * ∏ σ, ‖c σ‖) * |s| * hsn (A τ * X * (A τ)⁻¹)
        ring

end GlobalTheory.PackGlob

end
