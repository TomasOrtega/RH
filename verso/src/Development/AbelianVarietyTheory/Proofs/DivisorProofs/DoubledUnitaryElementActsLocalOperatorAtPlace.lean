import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryCommutingHeisenbergActsFibrewiseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicAddCharNontrivialFinitePlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzRestrictFinitePlaceMemSchwartzBruhStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMemOfMemStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.DblActs

/- English proof (translation)
Use function extensionality and compare the values at `y`. Simplify using `[GlobalTheory.WeilM.schr]`.
-/
theorem schr_trans' {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) {κ : Type} [Fintype κ]
    (w : κ → AF F) (Φ : (κ → AF F) → ℂ) : GlobalTheory.WeilM.schr ψ (w, 0) Φ = fun y => Φ (y + w) := by
  funext y
  simp [GlobalTheory.WeilM.schr]

/- English proof (translation)
Use `Prod.ext ?_ ?_` and prove the remaining obligations. Conclude with `zero_mul _`. Express the relevant statement in the definitionally equal form `GlobalTheory.AdelicU.singleFin v 1 * b.2 = GlobalTheory.AdelicU.singleFin v (evFin F v b)`. Apply `GlobalTheory.AdelicU.af_ext` to reduce the goal to its premises. Introduce `w`.

Rewrite using `[map_mul]`. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Rewrite using `[GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self, one_mul]`. Both sides reduce to the same expression.

Rewrite using `[GlobalTheory.AdelicU.evalV_singleFin_ne hw, GlobalTheory.AdelicU.evalV_singleFin_ne hw, zero_mul]`.
-/
theorem liftV_one_mul' {F : Type} [Field F] [NumberField F] (v : Pl F) (b : AF F) :
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
Establish `hfib` using `GlobalTheory.T.isometry_commuting_heisenberg_acts_fibrewise v ψ T hψ (GlobalTheory.T.standardAdelicAddChar_nontrivial_finitePlace ψ hψ) hkeep hunit hcomm`. Establish `htr : ∀ u : AF F, evFin F v u = 0 → ∀ p : κ → AF F, ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, T (fun y => Φ (y + u • p)) = fun y => T Φ (y + u • p)`. Introduce `u hu p Φ hΦ`. Establish `h` using `hcomm u hu p 0 Φ hΦ`. Rewrite `h` using `[smul_zero, schr_trans', schr_trans']`.

Conclude with `h`. Take `⟨R, hR0, hR⟩` from `GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction κ v`. Use `⟨(R 0)⁻¹ • fun t => T (tens (evFin F v) φ R) (fun i => GlobalTheory.LatVac.liftV v (t i)), ?_, ?_⟩` and prove the remaining obligations. Conclude with `(GlobalTheory.WeilM.SB _).smul_mem (R 0)⁻¹ (GlobalTheory.T.adelicSchwartz_restrict_finitePlace_mem_schwartzBruhat v _ (hkeep _ (hR φ hφ).2))`. Introduce `r hr`.

Use function extensionality and compare the values at `y`. Use `set u : AF F := 1 - GlobalTheory.LatVac.liftV v 1 with hudef`. Establish `hu : evFin F v u = 0` using `by simp [hudef, GlobalTheory.LatVac.evFin_liftV]`. Use `set p : κ → AF F := fun i => GlobalTheory.LatVac.liftV v (evFin F v (y i)) with hpdef`. Establish `hyp : y + u • (-y) = p`.

Use function extensionality and compare the values at `i`. Simplify using `only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, hudef, hpdef]`. Rewrite using `[← liftV_one_mul']`. Expand and normalize the polynomial expressions, which then agree. Establish `hpat : At (evFin F v) p`.

Introduce `u' hu'`. Use function extensionality and compare the values at `i`. Conclude with `GlobalTheory.LatVac.at_liftV v _ u' hu'`. Use `set Φ₀ := tens (evFin F v) φ R with hΦ₀`. Use `set Φ₁ := tens (evFin F v) φ r with hΦ₁`.

Use `set Φ₂ : (κ → AF F) → ℂ := (r y / R 0) • (fun w => Φ₀ (w + u • (-y))) with hΦ₂`. Establish `hm₀ : Φ₀ ∈ GlobalTheory.WeilM.schA F _` using `(hR φ hφ).2`. Establish `hm₂ : Φ₂ ∈ GlobalTheory.WeilM.schA F _` using `Submodule.smul_mem _ _ (GlobalTheory.T.adelicSchwartzSpace_translate_mem_of_mem _ _ hm₀)`. Establish `hfz : ∀ z, At (evFin F v) z → (Φ₁ - Φ₂) (y + z) = 0`. Introduce `z hz`.

Establish `e1 : r (y + z) = r y` using `hr.1 y z hz`. Establish `e2 : y + z + u • (-y) = p + z` using `by rw [← hyp]; abel`. Establish `hpz : At (evFin F v) (p + z)` using `fun u' hu' => by`. Rewrite using `[smul_add, hpat u' hu', hz u' hu', add_zero]`. Establish `e3 : R (p + z) = R 0` using `by simpa using (hR φ hφ).1 0 (p + z) hpz`.

Establish `e4 : (fun i => evFin F v ((y + z + u • (-y)) i)) = fun i => evFin F v ((y + z) i)`. Use function extensionality and compare the values at `i`. Simplify using `[hu]`. Simplify using `only [Pi.sub_apply, hΦ₂, hΦ₁, hΦ₀, Pi.smul_apply, smul_eq_mul, tens]`. Rewrite using `[e4, e2, e3, e1]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `h0` using `hfib (Φ₁ - Φ₂) (sub_mem hr.2 hm₂) y hfz`. Rewrite `h0` using `[map_sub, Pi.sub_apply, sub_eq_zero]`. Establish `h2 : T Φ₂ y = (r y / R 0) * T Φ₀ p`.

Rewrite using `[hΦ₂, map_smul, htr u hu (-y) Φ₀ hm₀, Pi.smul_apply, smul_eq_mul, hyp]`. Rewrite using `[h0, h2]`. Simplify using `only [tens, hpdef, Pi.smul_apply, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts.
-/
theorem acts_of_comm {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : Pl F)
    (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (T : Module.End ℂ ((κ → AF F) → ℂ))
    (hkeep : ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, T Φ ∈ GlobalTheory.WeilM.schA F κ)
    (hunit : ∀ μ : @MeasureTheory.Measure (κ → AF F) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∫⁻ y, ‖T Φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖Φ y‖ₑ ^ 2 ∂μ)
    (hcomm : ∀ u : AF F, evFin F v u = 0 → ∀ p q : κ → AF F, ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
      T (GlobalTheory.WeilM.schr ψ (u • p, u • q) Φ) = GlobalTheory.WeilM.schr ψ (u • p, u • q) (T Φ))
    (φ : (κ → Fv F v) → ℂ) (hφ : φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v)) :
    ∃ φ₁ ∈ GlobalTheory.WeilM.SB (κ → Fv F v), Acts (evFin F v) T φ φ₁ := by
  have hfib := GlobalTheory.T.isometry_commuting_heisenberg_acts_fibrewise v ψ T hψ (GlobalTheory.T.standardAdelicAddChar_nontrivial_finitePlace ψ hψ) hkeep hunit hcomm
  have htr : ∀ u : AF F, evFin F v u = 0 → ∀ p : κ → AF F,
      ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, T (fun y => Φ (y + u • p)) = fun y => T Φ (y + u • p) := by
    intro u hu p Φ hΦ
    have h := hcomm u hu p 0 Φ hΦ
    rw [smul_zero, schr_trans', schr_trans'] at h
    exact h
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction κ v
  refine ⟨(R 0)⁻¹ • fun t => T (tens (evFin F v) φ R) (fun i => GlobalTheory.LatVac.liftV v (t i)), ?_, ?_⟩
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
    have hpat : At (evFin F v) p := by
      intro u' hu'
      funext i
      exact GlobalTheory.LatVac.at_liftV v _ u' hu'
    set Φ₀ := tens (evFin F v) φ R with hΦ₀
    set Φ₁ := tens (evFin F v) φ r with hΦ₁
    set Φ₂ : (κ → AF F) → ℂ := (r y / R 0) • (fun w => Φ₀ (w + u • (-y))) with hΦ₂
    have hm₀ : Φ₀ ∈ GlobalTheory.WeilM.schA F _ := (hR φ hφ).2
    have hm₂ : Φ₂ ∈ GlobalTheory.WeilM.schA F _ := Submodule.smul_mem _ _ (GlobalTheory.T.adelicSchwartzSpace_translate_mem_of_mem _ _ hm₀)
    have hfz : ∀ z, At (evFin F v) z → (Φ₁ - Φ₂) (y + z) = 0 := by
      intro z hz
      have e1 : r (y + z) = r y := hr.1 y z hz
      have e2 : y + z + u • (-y) = p + z := by rw [← hyp]; abel
      have hpz : At (evFin F v) (p + z) := fun u' hu' => by
        rw [smul_add, hpat u' hu', hz u' hu', add_zero]
      have e3 : R (p + z) = R 0 := by simpa using (hR φ hφ).1 0 (p + z) hpz
      have e4 : (fun i => evFin F v ((y + z + u • (-y)) i)) = fun i => evFin F v ((y + z) i) := by
        funext i
        simp [hu]
      simp only [Pi.sub_apply, hΦ₂, hΦ₁, hΦ₀, Pi.smul_apply, smul_eq_mul, tens]
      rw [e4, e2, e3, e1]
      field_simp
      ring
    have h0 := hfib (Φ₁ - Φ₂) (sub_mem hr.2 hm₂) y hfz
    rw [map_sub, Pi.sub_apply, sub_eq_zero] at h0
    have h2 : T Φ₂ y = (r y / R 0) * T Φ₀ p := by
      rw [hΦ₂, map_smul, htr u hu (-y) Φ₀ hm₀, Pi.smul_apply, smul_eq_mul, hyp]
    rw [h0, h2]
    simp only [tens, hpdef, Pi.smul_apply, smul_eq_mul]
    field_simp

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B a a' G hB dd omd hS v p hp φ hφ`. Use `acts_of_comm v B.ψ hB.std (omd p) (fun Φ hΦ => hS.pres p Φ hΦ) (fun μ hμ Φ hΦ => hS.unit μ hμ p Φ hΦ) ?_ φ hφ` and prove the remaining obligations. Introduce `u hu x y Φ hΦ`. Use `set w := dd.e.symm (x, y) with hw`. Establish `he : dd.e (u • w) = (u • x, u • y)`.

Rewrite using `[LinearEquiv.map_smul, hw, LinearEquiv.apply_symm_apply, Prod.smul_mk]`. Establish `h2` using `hp u hu`. Establish `e2 : actB (cA σ) p (u • w) = u • w`. Simplify using `only [actB]`. Use `set P : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E) := ((p : GL (Fin a' ⊕ Fin a') (AE F E)) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) with hP`.

Use `set c : AE F E := algebraMap (AF F) (AE F E) u with hc`. Establish `hs1 : u • w = c • w` using `(algebraMap_smul (AE F E) u w).symm`. Establish `hs2 : u • (P - 1) = c • (P - 1)` using `(algebraMap_smul (AE F E) u (P - 1)).symm`. Establish `h2' : c • (P - 1) = 0` using `hs2 ▸ h2`. Establish `: (c • w) * Pᵀ - c • w = w * (c • (P - 1))ᵀ`.

Rewrite using `[Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_sub, Matrix.transpose_one, Matrix.mul_sub, Matrix.mul_one, smul_sub]`. Rewrite `this` using `[h2']`. Simplify using `only [Matrix.transpose_zero, Matrix.mul_zero, sub_eq_zero] at this`. Rewrite using `[hs1]`. Conclude with `this`.

Establish `h3` using `hS.impl p (u • w) Φ hΦ`. Simplify using `only [Darboux.rho, he, e2] at h3`. Conclude with `h3`.
-/
theorem dbl_acts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a'), B.IsGood σ →
    ∀ (dd : Darboux (symp (cA σ) (-1) (incM F G.W.J) (dbl (incM F G.V'.J))) ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a'))))
      (omd : UG (cA σ) (dbl (incM F G.V'.J)) →* Module.End ℂ (((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → AF F) → ℂ)),
      IsUSplitting (adeleClass F) B.ψ dd (actB (cA σ)) omd →
    ∀ (v : Pl F) (p : UG (cA σ) (dbl (incM F G.V'.J))),
      At (evFin F v) (((p : GL (Fin a' ⊕ Fin a') (AE F E)) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) - 1) →
    ∀ φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v), ∃ φ₁ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v),
      Acts (evFin F v) (omd p) φ φ₁ := by
  intro F E _ _ _ _ _ σ B a a' G hB dd omd hS v p hp φ hφ
  refine acts_of_comm v B.ψ hB.std (omd p) (fun Φ hΦ => hS.pres p Φ hΦ)
    (fun μ hμ Φ hΦ => hS.unit μ hμ p Φ hΦ) ?_ φ hφ
  intro u hu x y Φ hΦ
  set w := dd.e.symm (x, y) with hw
  have he : dd.e (u • w) = (u • x, u • y) := by
    rw [LinearEquiv.map_smul, hw, LinearEquiv.apply_symm_apply, Prod.smul_mk]
  have h2 := hp u hu
  have e2 : actB (cA σ) p (u • w) = u • w := by
    simp only [actB]
    set P : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E) :=
      ((p : GL (Fin a' ⊕ Fin a') (AE F E)) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) with hP
    set c : AE F E := algebraMap (AF F) (AE F E) u with hc
    have hs1 : u • w = c • w := (algebraMap_smul (AE F E) u w).symm
    have hs2 : u • (P - 1) = c • (P - 1) := (algebraMap_smul (AE F E) u (P - 1)).symm
    have h2' : c • (P - 1) = 0 := hs2 ▸ h2
    have : (c • w) * Pᵀ - c • w = w * (c • (P - 1))ᵀ := by
      rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_sub, Matrix.transpose_one,
        Matrix.mul_sub, Matrix.mul_one, smul_sub]
    rw [h2'] at this
    simp only [Matrix.transpose_zero, Matrix.mul_zero, sub_eq_zero] at this
    rw [hs1]
    exact this
  have h3 := hS.impl p (u • w) Φ hΦ
  simp only [Darboux.rho, he, e2] at h3
  exact h3

end GlobalTheory.DblActs

end
