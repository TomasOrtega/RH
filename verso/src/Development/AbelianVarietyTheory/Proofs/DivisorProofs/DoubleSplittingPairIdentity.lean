import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksSubOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryCommutingHeisenbergActsFibrewiseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicAddCharNontrivialFinitePlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzRestrictFinitePlaceMemSchwartzBruhStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMemOfMemStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.DblScal.LocAt

/- English proof (translation)
Use `Prod.ext ?_ ?_` and prove the remaining obligations. Conclude with `zero_mul _`. Express the relevant statement in the definitionally equal form `GlobalTheory.AdelicU.singleFin v 1 * b.2 = GlobalTheory.AdelicU.singleFin v (evFin F v b)`. Apply `GlobalTheory.AdelicU.af_ext` to reduce the goal to its premises. Introduce `w`.

Rewrite using `[map_mul]`. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Rewrite using `[GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self, one_mul]`. Both sides reduce to the same expression.

Rewrite using `[GlobalTheory.AdelicU.evalV_singleFin_ne hw, GlobalTheory.AdelicU.evalV_singleFin_ne hw, zero_mul]`.
-/
theorem liftV_one_mul' {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (b : AF F) :
    GlobalTheory.LatVac.liftV v 1 * b = GlobalTheory.LatVac.liftV v (evFin F v b) := by
  refine Prod.ext ?_ ?_
  · exact zero_mul _
  · change GlobalTheory.AdelicU.singleFin v 1 * b.2 = GlobalTheory.AdelicU.singleFin v (evFin F v b)
    apply GlobalTheory.AdelicU.af_ext
    intro w
    rw [map_mul]
    by_cases hw : w = v
    · subst hw
      rw [GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self, one_mul]
      rfl
    · rw [GlobalTheory.AdelicU.evalV_singleFin_ne hw, GlobalTheory.AdelicU.evalV_singleFin_ne hw, zero_mul]

/- English proof (translation)
Use function extensionality and compare the values at `y`. Simplify using `[GlobalTheory.WeilM.schr]`.
-/
theorem schr_trans' {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) {κ : Type} [Fintype κ]
    (w : κ → AF F) (Φ : (κ → AF F) → ℂ) : GlobalTheory.WeilM.schr ψ (w, 0) Φ = fun y => Φ (y + w) := by
  funext y
  simp [GlobalTheory.WeilM.schr]

/- English proof (translation)
Establish `hfib` using `GlobalTheory.T.isometry_commuting_heisenberg_acts_fibrewise v ψ T hstd (GlobalTheory.T.standardAdelicAddChar_nontrivial_finitePlace ψ hstd) hkeep hunit hcomm`. Establish `htr : ∀ u : AF F, evFin F v u = 0 → ∀ p : κ → AF F, ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, T (fun y => Φ (y + u • p)) = fun y => T Φ (y + u • p)`. Introduce `u hu p Φ hΦ`. Establish `h` using `hcomm u hu p 0 Φ hΦ`. Rewrite `h` using `[smul_zero, schr_trans', schr_trans']`.

Conclude with `h`. Take `⟨R, hR0, hR⟩` from `GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction κ v`. Use `⟨(R 0)⁻¹ • fun t => T (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ R) (fun i => GlobalTheory.LatVac.liftV v (t i)), ?_, ?_⟩` and prove the remaining obligations. Conclude with `(GlobalTheory.WeilM.SB _).smul_mem (R 0)⁻¹ (GlobalTheory.T.adelicSchwartz_restrict_finitePlace_mem_schwartzBruhat v _ (hkeep _ (hR φ hφ).2))`. Introduce `r hr`.

Use function extensionality and compare the values at `y`. Use `set u : AF F := 1 - GlobalTheory.LatVac.liftV v 1 with hudef`. Establish `hu : evFin F v u = 0` using `by simp [hudef, GlobalTheory.LatVac.evFin_liftV]`. Use `set p : κ → AF F := fun i => GlobalTheory.LatVac.liftV v (evFin F v (y i)) with hpdef`. Establish `hyp : y + u • (-y) = p`.

Use function extensionality and compare the values at `i`. Simplify using `only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, hudef, hpdef]`. Rewrite using `[← liftV_one_mul']`. Expand and normalize the polynomial expressions, which then agree. Establish `hpat : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) p`.

Introduce `u' hu'`. Use function extensionality and compare the values at `i`. Conclude with `GlobalTheory.LatVac.at_liftV v _ u' hu'`. Use `set Φ₀ := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ R with hΦ₀`. Use `set Φ₁ := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ r with hΦ₁`.

Use `set Φ₂ : (κ → AF F) → ℂ := (r y / R 0) • (fun w => Φ₀ (w + u • (-y))) with hΦ₂`. Establish `hm₀ : Φ₀ ∈ GlobalTheory.WeilM.schA F _` using `(hR φ hφ).2`. Establish `hm₂ : Φ₂ ∈ GlobalTheory.WeilM.schA F _` using `Submodule.smul_mem _ _ (GlobalTheory.T.adelicSchwartzSpace_translate_mem_of_mem _ _ hm₀)`. Establish `hfz : ∀ z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z → (Φ₁ - Φ₂) (y + z) = 0`. Introduce `z hz`.

Establish `e1 : r (y + z) = r y` using `hr.1 y z hz`. Establish `e2 : y + z + u • (-y) = p + z` using `by rw [← hyp]; abel`. Establish `hpz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) (p + z)` using `fun u' hu' => by`. Rewrite using `[smul_add, hpat u' hu', hz u' hu', add_zero]`. Establish `e3 : R (p + z) = R 0` using `by simpa using (hR φ hφ).1 0 (p + z) hpz`.

Establish `e4 : (fun i => evFin F v ((y + z + u • (-y)) i)) = fun i => evFin F v ((y + z) i)`. Use function extensionality and compare the values at `i`. Simplify using `[hu]`. Simplify using `only [Pi.sub_apply, hΦ₂, hΦ₁, hΦ₀, Pi.smul_apply, smul_eq_mul, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens]`. Rewrite using `[e4, e2, e3, e1]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `h0` using `hfib (Φ₁ - Φ₂) (sub_mem hr.2 hm₂) y hfz`. Rewrite `h0` using `[map_sub, Pi.sub_apply, sub_eq_zero]`. Establish `h2 : T Φ₂ y = (r y / R 0) * T Φ₀ p`.

Rewrite using `[hΦ₂, map_smul, htr u hu (-y) Φ₀ hm₀, Pi.smul_apply, smul_eq_mul, hyp]`. Rewrite using `[h0, h2]`. Simplify using `only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, hpdef, Pi.smul_apply, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts.
-/
theorem acts_of_comm {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (ψ : AddChar (AF F) ℂ) (hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (T : Module.End ℂ ((κ → AF F) → ℂ))
    (hkeep : ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, T Φ ∈ GlobalTheory.WeilM.schA F κ)
    (hunit : ∀ μ : @MeasureTheory.Measure (κ → AF F) (borel _),
      @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∫⁻ y, ‖T Φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖Φ y‖ₑ ^ 2 ∂μ)
    (hcomm : ∀ u : AF F, evFin F v u = 0 → ∀ p q : κ → AF F, ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
      T (GlobalTheory.WeilM.schr ψ (u • p, u • q) Φ) = GlobalTheory.WeilM.schr ψ (u • p, u • q) (T Φ))
    (φ : (κ → Fv F v) → ℂ) (hφ : φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v)) :
    ∃ φ₁ ∈ GlobalTheory.WeilM.SB (κ → Fv F v), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) T φ φ₁ := by
  have hfib := GlobalTheory.T.isometry_commuting_heisenberg_acts_fibrewise v ψ T hstd (GlobalTheory.T.standardAdelicAddChar_nontrivial_finitePlace ψ hstd) hkeep hunit hcomm
  have htr : ∀ u : AF F, evFin F v u = 0 → ∀ p : κ → AF F,
      ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, T (fun y => Φ (y + u • p)) = fun y => T Φ (y + u • p) := by
    intro u hu p Φ hΦ
    have h := hcomm u hu p 0 Φ hΦ
    rw [smul_zero, schr_trans', schr_trans'] at h
    exact h
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction κ v
  refine ⟨(R 0)⁻¹ • fun t => T (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ R) (fun i => GlobalTheory.LatVac.liftV v (t i)), ?_, ?_⟩
  · exact (GlobalTheory.WeilM.SB _).smul_mem (R 0)⁻¹ (GlobalTheory.T.adelicSchwartz_restrict_finitePlace_mem_schwartzBruhat v _ (hkeep _ (hR φ hφ).2))
  · intro r hr
    funext y
    set u : AF F := 1 - GlobalTheory.LatVac.liftV v 1 with hudef
    have hu : evFin F v u = 0 := by simp [hudef, GlobalTheory.LatVac.evFin_liftV]
    set p : κ → AF F := fun i => GlobalTheory.LatVac.liftV v (evFin F v (y i)) with hpdef
    have hyp : y + u • (-y) = p := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, hudef, hpdef]
      rw [← liftV_one_mul']
      ring
    have hpat : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) p := by
      intro u' hu'
      funext i
      exact GlobalTheory.LatVac.at_liftV v _ u' hu'
    set Φ₀ := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ R with hΦ₀
    set Φ₁ := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ r with hΦ₁
    set Φ₂ : (κ → AF F) → ℂ := (r y / R 0) • (fun w => Φ₀ (w + u • (-y))) with hΦ₂
    have hm₀ : Φ₀ ∈ GlobalTheory.WeilM.schA F _ := (hR φ hφ).2
    have hm₂ : Φ₂ ∈ GlobalTheory.WeilM.schA F _ := Submodule.smul_mem _ _ (GlobalTheory.T.adelicSchwartzSpace_translate_mem_of_mem _ _ hm₀)
    have hfz : ∀ z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z → (Φ₁ - Φ₂) (y + z) = 0 := by
      intro z hz
      have e1 : r (y + z) = r y := hr.1 y z hz
      have e2 : y + z + u • (-y) = p + z := by rw [← hyp]; abel
      have hpz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) (p + z) := fun u' hu' => by
        rw [smul_add, hpat u' hu', hz u' hu', add_zero]
      have e3 : R (p + z) = R 0 := by simpa using (hR φ hφ).1 0 (p + z) hpz
      have e4 : (fun i => evFin F v ((y + z + u • (-y)) i)) = fun i => evFin F v ((y + z) i) := by
        funext i
        simp [hu]
      simp only [Pi.sub_apply, hΦ₂, hΦ₁, hΦ₀, Pi.smul_apply, smul_eq_mul, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens]
      rw [e4, e2, e3, e1]
      field_simp
      ring
    have h0 := hfib (Φ₁ - Φ₂) (sub_mem hr.2 hm₂) y hfz
    rw [map_sub, Pi.sub_apply, sub_eq_zero] at h0
    have h2 : T Φ₂ y = (r y / R 0) * T Φ₀ p := by
      rw [hΦ₂, map_smul, htr u hu (-y) Φ₀ hm₀, Pi.smul_apply, smul_eq_mul, hyp]
    rw [h0, h2]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, hpdef, Pi.smul_apply, smul_eq_mul]
    field_simp

end GlobalTheory.DblScal.LocAt

namespace GlobalTheory.DblScal.LocAt

/- English proof (translation)
Introduce `_ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP dd omd hS v g hg φ hφ`. Use `acts_of_comm v B.ψ hP.base.std (omd g) (fun Φ hΦ => hS.pres g Φ hΦ) (fun μ hμ Φ hΦ => hS.unit μ hμ g Φ hΦ) ?_ φ hφ` and prove the remaining obligations. Introduce `u hu p q Φ hΦ`. Use `set w := dd.e.symm (p, q) with hw`. Establish `he : dd.e (u • w) = (u • p, u • q)`.

Rewrite using `[LinearEquiv.map_smul, hw, LinearEquiv.apply_symm_apply, Prod.smul_mk]`. Set `G : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)` to `((g : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix _ _ _)`. Establish `h2 : u • (G - 1) = 0` using `hg u hu`. Establish `e2 : (u • w) * G.transpose = u • w`. Establish `: (u • w) * G.transpose - u • w = w * (u • (G - 1)).transpose`.

Rewrite using `[Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_sub, Matrix.transpose_one, Matrix.mul_sub, Matrix.mul_one, smul_sub]`. Rewrite `this` using `[h2, Matrix.transpose_zero, Matrix.mul_zero, sub_eq_zero]`. Conclude with `this`. Establish `hact : actB (cA σ) g (u • w) = u • w` using `e2`. Establish `h3` using `hS.impl g (u • w) Φ hΦ`.

Simplify using `only [GlobalTheory.WeilM.Darboux.rho, he, hact] at h3`. Conclude with `h3`.
-/
theorem locOps : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (dd : GlobalTheory.DblScal.DblCo σ X W) (omd : GlobalTheory.DblScal.DblRep σ (n := n) W),
      IsUSplitting (adeleClass F) B.ψ dd (actB (cA σ)) omd → ∀ v : Pl F, GlobalTheory.DblScal.LocOps omd v := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP dd omd hS v g hg φ hφ
  refine acts_of_comm v B.ψ hP.base.std (omd g) (fun Φ hΦ => hS.pres g Φ hΦ)
    (fun μ hμ Φ hΦ => hS.unit μ hμ g Φ hΦ) ?_ φ hφ
  intro u hu p q Φ hΦ
  set w := dd.e.symm (p, q) with hw
  have he : dd.e (u • w) = (u • p, u • q) := by
    rw [LinearEquiv.map_smul, hw, LinearEquiv.apply_symm_apply, Prod.smul_mk]
  let G : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E) := ((g : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix _ _ _)
  have h2 : u • (G - 1) = 0 := hg u hu
  have e2 : (u • w) * G.transpose = u • w := by
    have : (u • w) * G.transpose - u • w = w * (u • (G - 1)).transpose := by
      rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_sub, Matrix.transpose_one,
        Matrix.mul_sub, Matrix.mul_one, smul_sub]
    rw [h2, Matrix.transpose_zero, Matrix.mul_zero, sub_eq_zero] at this
    exact this
  have hact : actB (cA σ) g (u • w) = u • w := e2
  have h3 := hS.impl g (u • w) Φ hΦ
  simp only [GlobalTheory.WeilM.Darboux.rho, he, hact] at h3
  exact h3

end GlobalTheory.DblScal.LocAt
