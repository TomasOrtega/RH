import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.DifferentiableOfChar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DatumFock

open GlobalTheory.SplitScalar

/- English proof (translation)
Set `p : Submodule ℂ (ℝ → ℂ)` to `{ carrier := {g | DifferentiableAt ℝ g 0} add_mem' := fun ha hb => ha.add hb zero_mem' := differentiableAt_const _ smul_mem' := fun c _ hg => hg.const_smul c }`. Set `d : p →ₗ[ℂ] ℂ` to `{ toFun := fun g => deriv g.1 0 map_add' := fun g h => deriv_add g.2 h.2 map_smul' := fun c g => deriv_const_smul c g.2 }`. Take `⟨l, hl⟩` from `LinearMap.exists_extend d`. Conclude with `⟨l, fun g hg => LinearMap.congr_fun hl ⟨g, hg⟩⟩`.
-/
theorem exists_derivForm : ∃ l : (ℝ → ℂ) →ₗ[ℂ] ℂ, ∀ g, DifferentiableAt ℝ g 0 → l g = deriv g 0 := by
  let p : Submodule ℂ (ℝ → ℂ) :=
    { carrier := {g | DifferentiableAt ℝ g 0}
      add_mem' := fun ha hb => ha.add hb
      zero_mem' := differentiableAt_const _
      smul_mem' := fun c _ hg => hg.const_smul c }
  let d : p →ₗ[ℂ] ℂ :=
    { toFun := fun g => deriv g.1 0
      map_add' := fun g h => deriv_add g.2 h.2
      map_smul' := fun c g => deriv_const_smul c g.2 }
  obtain ⟨l, hl⟩ := LinearMap.exists_extend d
  exact ⟨l, fun g hg => LinearMap.congr_fun hl ⟨g, hg⟩⟩

variable {D : D7}

def alongLine (l : (ℝ → ℂ) →ₗ[ℂ] ℂ) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (L : ℝ → WO S T) :
    (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) where
  toFun g := fun x => l fun t => heisO ψ S T (L t) g x
  map_add' g g' := by
    funext x
    rw [Pi.add_apply, ← map_add]
    congr 1
    funext t
    exact congrFun ((heisL ψ S T (L t)).map_add g g') x
  map_smul' c g := by
    funext x
    rw [RingHom.id_apply, Pi.smul_apply, ← map_smul]
    congr 1
    funext t
    exact congrFun ((heisL ψ S T (L t)).map_smul c g) x

/- English proof (translation)
Use function extensionality and compare the values at `x`. Establish `hc : ∀ t, heisO ψ S T (L t) (heisO ψ S T u g) = heisO ψ S T u (heisO ψ S T (L t) g)`. Introduce `t`. Rewrite using `[GlobalTheory.SplitScalar.heisO_comm, GlobalTheory.SplitScalar.symplO_real_fin S T (hL t) hu, AddChar.map_zero_eq_one, one_smul]`. Establish `key : ∀ h : WO S T → ℂ, heisO ψ S T u h x = ψ (symplOH S T x u) * h (x + u)` using `fun _ => rfl`.

Simplify using `only [alongLine, LinearMap.coe_mk, AddHom.coe_mk, hc, key]`. Conclude with `l.map_smul (ψ (symplOH S T x u)) (fun t => heisO ψ S T (L t) g (x + u))`.
-/
theorem alongLine_heisO (l : (ℝ → ℂ) →ₗ[ℂ] ℂ) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {L : ℝ → WO S T}
    (hL : ∀ t, (L t).map (finPart D) = 0) {u : WO S T} (hu : u.map (infPart D) = 0) (g : WO S T → ℂ) :
    alongLine l ψ S T L (heisO ψ S T u g) = heisO ψ S T u (alongLine l ψ S T L g) := by
  funext x
  have hc : ∀ t, heisO ψ S T (L t) (heisO ψ S T u g) = heisO ψ S T u (heisO ψ S T (L t) g) := by
    intro t
    rw [GlobalTheory.SplitScalar.heisO_comm, GlobalTheory.SplitScalar.symplO_real_fin S T (hL t) hu, AddChar.map_zero_eq_one,
      one_smul]
  have key : ∀ h : WO S T → ℂ, heisO ψ S T u h x = ψ (symplOH S T x u) * h (x + u) := fun _ => rfl
  simp only [alongLine, LinearMap.coe_mk, AddHom.coe_mk, hc, key]
  exact l.map_smul (ψ (symplOH S T x u)) (fun t => heisO ψ S T (L t) g (x + u))

/- English proof (translation)
Use `set F : ℝ → ℂ := fun u => ∫ x in (0:ℝ)..u, φ x with hFdef`. Establish `hF : ∀ b, HasDerivAt F (φ b) b` using `fun b => (hφ.integral_hasStrictDerivAt 0 b).hasDerivAt`. Choose the witnesses or unpack the hypotheses as in `⟨δ, hδ⟩ : ∃ δ, F δ ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Establish `hz : F = fun _ => (0:ℂ)` using `funext fun δ => by`.

Assume the negation of the conclusion as `h`. Conclude with `hcon ⟨δ, h⟩`. Establish `h1` using `hF 0`. Rewrite `h1` using `[hz, h0]`. Conclude with `one_ne_zero (h1.unique (hasDerivAt_const (0:ℝ) (0:ℂ)))`.

Establish `key : ∀ t, φ t = (F (δ + t) - F t) * (F δ)⁻¹`. Introduce `t`. Establish `h1 : ∫ x in (0:ℝ)..δ, φ (x + t) = F (δ + t) - F t`. Rewrite using `[intervalIntegral.integral_comp_add_right, zero_add, hFdef]`. Conclude with `(intervalIntegral.integral_interval_sub_left (hφ.intervalIntegrable _ _) (hφ.intervalIntegrable _ _)).symm`.

Establish `h2 : ∫ x in (0:ℝ)..δ, φ (x + t) = F δ * φ t`. Repeatedly rewrite using `[hmul]`. Conclude with `intervalIntegral.integral_mul_const _ _`. Rewrite using `[← h1, h2, mul_comm (F δ) (φ t), mul_assoc, mul_inv_cancel₀ hδ, mul_one]`. Introduce `t`.

Establish `hd : DifferentiableAt ℝ (fun t => (F (δ + t) - F t) * (F δ)⁻¹) t` using `((((hF (δ + t)).differentiableAt).comp t (differentiableAt_id.const_add δ)).sub (hF t).differentiableAt).mul_const _`. Conclude with `hd.congr_of_eventuallyEq (Filter.Eventually.of_forall key)`.
-/
private lemma differentiable_of_continuous_additive_char {φ : ℝ → ℂ} (hφ : Continuous φ) (h0 : φ 0 = 1)
    (hmul : ∀ s t, φ (s + t) = φ s * φ t) : Differentiable ℝ φ := by
  set F : ℝ → ℂ := fun u => ∫ x in (0:ℝ)..u, φ x with hFdef
  have hF : ∀ b, HasDerivAt F (φ b) b := fun b => (hφ.integral_hasStrictDerivAt 0 b).hasDerivAt
  obtain ⟨δ, hδ⟩ : ∃ δ, F δ ≠ 0 := by
    by_contra hcon
    have hz : F = fun _ => (0:ℂ) := funext fun δ => by
      by_contra h
      exact hcon ⟨δ, h⟩
    have h1 := hF 0
    rw [hz, h0] at h1
    exact one_ne_zero (h1.unique (hasDerivAt_const (0:ℝ) (0:ℂ)))
  have key : ∀ t, φ t = (F (δ + t) - F t) * (F δ)⁻¹ := by
    intro t
    have h1 : ∫ x in (0:ℝ)..δ, φ (x + t) = F (δ + t) - F t := by
      rw [intervalIntegral.integral_comp_add_right, zero_add, hFdef]
      exact (intervalIntegral.integral_interval_sub_left (hφ.intervalIntegrable _ _)
        (hφ.intervalIntegrable _ _)).symm
    have h2 : ∫ x in (0:ℝ)..δ, φ (x + t) = F δ * φ t := by
      simp_rw [hmul]
      exact intervalIntegral.integral_mul_const _ _
    rw [← h1, h2, mul_comm (F δ) (φ t), mul_assoc, mul_inv_cancel₀ hδ, mul_one]
  intro t
  have hd : DifferentiableAt ℝ (fun t => (F (δ + t) - F t) * (F δ)⁻¹) t :=
    ((((hF (δ + t)).differentiableAt).comp t (differentiableAt_id.const_add δ)).sub
      (hF t).differentiableAt).mul_const _
  exact hd.congr_of_eventuallyEq (Filter.Eventually.of_forall key)

/- English proof (translation)
Take `⟨l, hl⟩` from `exists_derivForm`. Establish `hex` using `GlobalTheory.RealLineAt.lineAt_exists D`. Unfold `LineAtExists at hex`. Establish `hspec : ∀ w : Matrix (Fin T.rank) (Fin S.rank) ℂ, IsLineAt θ τ w (lineAt θ τ w)`. Introduce `w`.

Take `⟨L, hL⟩` from `hex θ hθ T.rank S.rank τ w`. Conclude with `Classical.epsilon_spec ⟨L, hL⟩`. Establish `hfin : ∀ (w : Matrix (Fin T.rank) (Fin S.rank) ℂ) (t : ℝ), (lineAt θ τ w t).map (finPart D) = 0`. Introduce `w t`. Establish `h` using `hspec w`.

Unfold `IsLineAt at h`. Conclude with `h.2.1 t`. Establish `hcont : ∀ w : Matrix (Fin T.rank) (Fin S.rank) ℂ, Continuous (lineAt θ τ w)`. Introduce `w`. Establish `h` using `hspec w`.

Unfold `IsLineAt at h`. Conclude with `h.1`. Establish `hdiff : ∀ g, IsThetaFunO ψ S T g → ∀ (w : Matrix (Fin T.rank) (Fin S.rank) ℂ) (x : WO S T), DifferentiableAt ℝ (fun t => heisO ψ S T (lineAt θ τ w t) g x) 0`. Introduce `g hg w x`. Take `⟨-, -, -, hsm⟩` from `hg`.

Establish `hgL : DifferentiableAt ℝ (fun t => g (x + lineAt θ τ w t)) 0`. Set `L1 : (Fin 1 → ℝ) →+ WO S T` to `(lineAt θ τ w).comp (Pi.evalAddMonoidHom (fun _ : Fin 1 => ℝ) 0)`. Establish `h1` using `hsm 1 L1 ((hcont w).comp (continuous_apply 0)) (fun t => hfin w (t 0)) x`. Establish `h2 : (fun t : ℝ => g (x + lineAt θ τ w t)) = (fun t : Fin 1 → ℝ => g (x + L1 t)) ∘ (fun t : ℝ => fun _ : Fin 1 => t)` using `rfl`. Rewrite using `[h2]`.

Conclude with `((h1.differentiable (by simp)) _).comp _ (differentiableAt_pi.2 fun _ => differentiableAt_id)`. Establish `hφ : Differentiable ℝ (fun t => ψ (symplOH S T x (lineAt θ τ w t)))`. Apply `differentiable_of_continuous_additive_char` to reduce the goal to its premises. Establish `hc : (fun t => symplOH S T x (lineAt θ τ w t)) = fun t => algebraMap D.host.F (AF D.host.F) (1 / 2) * symplO S T x (lineAt θ τ w t)` using `rfl`. Conclude with `hψ.comp (hc ▸ continuous_const.mul (GlobalTheory.SplitScalar.continuous_symplO S T continuous_const (hcont w)))`.

Rewrite using `[map_zero] show ψ (algebraMap D.host.F (AF D.host.F) (1 / 2) * symplO S T x 0) = 1`. Rewrite using `[GlobalTheory.SplitScalar.symplO_zero_right, mul_zero, AddChar.map_zero_eq_one]`. Introduce `s t`. Rewrite using `[map_add, GlobalTheory.SplitScalar.symplOH_add_right, AddChar.map_add_eq_mul]`. Conclude with `(hφ 0).mul hgL`.

Use `⟨alongLine l ψ S T (lineAt θ τ z) + Complex.I • alongLine l ψ S T (lineAt θ τ (J z)), ?_, ?_⟩` and prove the remaining obligations. Introduce `u hu g`. Simplify using `only [LinearMap.add_apply, LinearMap.smul_apply]`. Rewrite using `[alongLine_heisO l ψ S T (hfin z) hu, alongLine_heisO l ψ S T (hfin (J z)) hu]`. Use function extensionality and compare the values at `x`.

Unfold `heisO`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Introduce `g hg`. Use function extensionality and compare the values at `x`.

Unfold `annih Datum.dRho`. Simplify using `only [LinearMap.add_apply, LinearMap.smul_apply, Pi.add_apply, Pi.smul_apply, alongLine, LinearMap.coe_mk, AddHom.coe_mk]`. Rewrite using `[hl _ (hdiff g hg z x), hl _ (hdiff g hg (J z) x)]`.
-/
theorem exists_annihLin {ψ : AddChar (AF D.host.F) ℂ} (hψ : Continuous ψ) {θ : InfFam D} (hθ : IsInfFam θ)
    (S T : HSp D) (τ : D.what₂.Tau)
    (J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    ∃ A : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ),
      (∀ u : WO S T, u.map (infPart D) = 0 → ∀ g, A (heisO ψ S T u g) = heisO ψ S T u (A g)) ∧
      ∀ g, IsThetaFunO ψ S T g → A g = annih (heisO ψ S T) θ τ J z g := by
  obtain ⟨l, hl⟩ := exists_derivForm
  have hex := GlobalTheory.RealLineAt.lineAt_exists D
  unfold LineAtExists at hex
  have hspec : ∀ w : Matrix (Fin T.rank) (Fin S.rank) ℂ, IsLineAt θ τ w (lineAt θ τ w) := by
    intro w
    obtain ⟨L, hL⟩ := hex θ hθ T.rank S.rank τ w
    exact Classical.epsilon_spec ⟨L, hL⟩
  have hfin : ∀ (w : Matrix (Fin T.rank) (Fin S.rank) ℂ) (t : ℝ), (lineAt θ τ w t).map (finPart D) = 0 := by
    intro w t
    have h := hspec w
    unfold IsLineAt at h
    exact h.2.1 t
  have hcont : ∀ w : Matrix (Fin T.rank) (Fin S.rank) ℂ, Continuous (lineAt θ τ w) := by
    intro w
    have h := hspec w
    unfold IsLineAt at h
    exact h.1
  have hdiff : ∀ g, IsThetaFunO ψ S T g → ∀ (w : Matrix (Fin T.rank) (Fin S.rank) ℂ) (x : WO S T),
      DifferentiableAt ℝ (fun t => heisO ψ S T (lineAt θ τ w t) g x) 0 := by
    intro g hg w x
    obtain ⟨-, -, -, hsm⟩ := hg
    have hgL : DifferentiableAt ℝ (fun t => g (x + lineAt θ τ w t)) 0 := by
      let L1 : (Fin 1 → ℝ) →+ WO S T := (lineAt θ τ w).comp (Pi.evalAddMonoidHom (fun _ : Fin 1 => ℝ) 0)
      have h1 := hsm 1 L1 ((hcont w).comp (continuous_apply 0)) (fun t => hfin w (t 0)) x
      have h2 : (fun t : ℝ => g (x + lineAt θ τ w t)) =
          (fun t : Fin 1 → ℝ => g (x + L1 t)) ∘ (fun t : ℝ => fun _ : Fin 1 => t) := rfl
      rw [h2]
      exact ((h1.differentiable (by simp)) _).comp _ (differentiableAt_pi.2 fun _ => differentiableAt_id)
    have hφ : Differentiable ℝ (fun t => ψ (symplOH S T x (lineAt θ τ w t))) := by
      apply differentiable_of_continuous_additive_char
      · have hc : (fun t => symplOH S T x (lineAt θ τ w t)) =
            fun t => algebraMap D.host.F (AF D.host.F) (1 / 2) * symplO S T x (lineAt θ τ w t) := rfl
        exact hψ.comp (hc ▸ continuous_const.mul (GlobalTheory.SplitScalar.continuous_symplO S T continuous_const (hcont w)))
      · rw [map_zero]
        show ψ (algebraMap D.host.F (AF D.host.F) (1 / 2) * symplO S T x 0) = 1
        rw [GlobalTheory.SplitScalar.symplO_zero_right, mul_zero, AddChar.map_zero_eq_one]
      · intro s t
        rw [map_add, GlobalTheory.SplitScalar.symplOH_add_right, AddChar.map_add_eq_mul]
    exact (hφ 0).mul hgL
  refine ⟨alongLine l ψ S T (lineAt θ τ z) + Complex.I • alongLine l ψ S T (lineAt θ τ (J z)), ?_, ?_⟩
  · intro u hu g
    simp only [LinearMap.add_apply, LinearMap.smul_apply]
    rw [alongLine_heisO l ψ S T (hfin z) hu, alongLine_heisO l ψ S T (hfin (J z)) hu]
    funext x
    unfold heisO
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · intro g hg
    funext x
    unfold annih Datum.dRho
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Pi.add_apply, Pi.smul_apply, alongLine,
      LinearMap.coe_mk, AddHom.coe_mk]
    rw [hl _ (hdiff g hg z x), hl _ (hdiff g hg (J z) x)]

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.map_apply, Matrix.zero_apply, ← hu i j, map_mul, he, zero_mul]`.
-/
theorem infPart_of_isHalf {S T : HSp D} {e : AE D} (he : infPart D e = 0) {u : WO S T} (hu : IsHalf e u) :
    u.map (infPart D) = 0 := by
  ext i j
  rw [Matrix.map_apply, Matrix.zero_apply, ← hu i j, map_mul, he, zero_mul]

/- English proof (translation)
Unfold `IsThetaAt AllSome at h`. Take `⟨⟨Tm, hTm⟩, hU⟩` from `h`. Unfold `IsFockVacAt at hv ⊢`. Introduce `z`. Take `⟨A, hA, hAθ⟩` from `exists_annihLin hψ hθ S T τ J z`.

Establish `hadd : ∀ (w : WO S T) (g g' : WO S T → ℂ), heisO ψ S T w (g + g') = heisO ψ S T w g + heisO ψ S T w g'` using `fun _ _ _ => funext fun _ => mul_add _ _ _`. Establish `hTm' : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c f₀ (Tm + A ∘ₗ Tm)`. Take `⟨htr, hmod, hvac⟩` from `hTm`. Use `⟨fun Φ' hΦ x hx => ?_, fun Φ' hΦ y hy => ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [LinearMap.add_apply, LinearMap.comp_apply]`.

Rewrite using `[htr Φ' hΦ x hx, hA x (infPart_of_isHalf he hx), hadd]`. Simplify using `only [LinearMap.add_apply, LinearMap.comp_apply]`. Rewrite using `[hmod Φ' hΦ y hy, hA y (infPart_of_isHalf he' hy), hadd]`. Simplify using `only [LinearMap.add_apply, LinearMap.comp_apply]`. Rewrite using `[hvac, hAθ f₀ h₀, hv z, add_zero]`.

Establish `e1 : f = Tm Φ` using `hU Tm hTm`. Establish `e2 : f = (Tm + A ∘ₗ Tm) Φ` using `hU _ hTm'`. Rewrite `e2` using `[LinearMap.add_apply, LinearMap.comp_apply, ← e1]`. Rewrite using `[← hAθ f hf]`. Simplify using `using e2`.
-/
theorem isFockVacAt_of_isThetaAt {ψ : AddChar (AF D.host.F) ℂ} (hψ : Continuous ψ) {θ : InfFam D} (hθ : IsInfFam θ)
    {S T : HSp D} {e : AE D} (he : infPart D e = 0) (he' : infPart D (cA D e) = 0) {Λ : AddSubgroup (WO S T)} {c : ℂ}
    {f₀ Φ f : WO S T → ℂ} (h : IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Φ f)
    (h₀ : IsThetaFunO ψ S T f₀) (hf : IsThetaFunO ψ S T f) {τ : D.what₂.Tau}
    {J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ}
    (hv : IsFockVacAt (heisO ψ S T) θ τ J f₀) : IsFockVacAt (heisO ψ S T) θ τ J f := by
  unfold IsThetaAt AllSome at h
  obtain ⟨⟨Tm, hTm⟩, hU⟩ := h
  unfold IsFockVacAt at hv ⊢
  intro z
  obtain ⟨A, hA, hAθ⟩ := exists_annihLin hψ hθ S T τ J z
  have hadd : ∀ (w : WO S T) (g g' : WO S T → ℂ),
      heisO ψ S T w (g + g') = heisO ψ S T w g + heisO ψ S T w g' :=
    fun _ _ _ => funext fun _ => mul_add _ _ _
  have hTm' : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c f₀ (Tm + A ∘ₗ Tm) := by
    obtain ⟨htr, hmod, hvac⟩ := hTm
    refine ⟨fun Φ' hΦ x hx => ?_, fun Φ' hΦ y hy => ?_, ?_⟩
    · simp only [LinearMap.add_apply, LinearMap.comp_apply]
      rw [htr Φ' hΦ x hx, hA x (infPart_of_isHalf he hx), hadd]
    · simp only [LinearMap.add_apply, LinearMap.comp_apply]
      rw [hmod Φ' hΦ y hy, hA y (infPart_of_isHalf he' hy), hadd]
    · simp only [LinearMap.add_apply, LinearMap.comp_apply]
      rw [hvac, hAθ f₀ h₀, hv z, add_zero]
  have e1 : f = Tm Φ := hU Tm hTm
  have e2 : f = (Tm + A ∘ₗ Tm) Φ := hU _ hTm'
  rw [LinearMap.add_apply, LinearMap.comp_apply, ← e1] at e2
  rw [← hAθ f hf]
  simpa using e2

/- English proof (translation)
Introduce `D ψ θ S T sS sT ΛS ΛT βS βT Pg Q ξ f₀ f h hf τ`. Take `⟨hv, e, he, ht⟩` from `h`. Unfold `IsVacO IsStdChar at hv`. Take `⟨hs, ⟨hθ, h₀, -, hfock, -⟩⟩` from `hv`. Establish `hψ : Continuous ψ`.

Establish `h1` using `hs.1`. Unfold `IsCharAF at h1`. Conclude with `h1.1`. Establish `ho : GlobalTheory.PlaceModelSum.IsOrthSum e` using `GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he`. Conclude with `isFockVacAt_of_isThetaAt hψ hθ ho.conj.infPart_eq ho.conj.conj.infPart_eq ht h₀ hf (hfock τ)`.
-/
theorem isFockVacAt_thPVec : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) βS βT Pg Q ξ (f₀ f : WO S T → ℂ), IsThPVecOf ψ θ S T sS sT ΛS ΛT βS βT Pg Q ξ f₀ f → IsThetaFunO ψ S T f → ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f := by
  intro D ψ θ S T sS sT ΛS ΛT βS βT Pg Q ξ f₀ f h hf τ
  obtain ⟨hv, e, he, ht⟩ := h
  unfold IsVacO IsStdChar at hv
  obtain ⟨hs, ⟨hθ, h₀, -, hfock, -⟩⟩ := hv
  have hψ : Continuous ψ := by
    have h1 := hs.1
    unfold IsCharAF at h1
    exact h1.1
  have ho : GlobalTheory.PlaceModelSum.IsOrthSum e := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he
  exact isFockVacAt_of_isThetaAt hψ hθ ho.conj.infPart_eq ho.conj.conj.infPart_eq ht h₀ hf (hfock τ)

end GlobalTheory.DatumFock

end
