import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSubAug
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.Published
open scoped TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open scoped Matrix

namespace GlobalTheory.LocalOpsW

/- English proof (translation)
Establish `hW` using `GlobalTheory.WeilM.IsUWeilPair.isUSplitting hWeil`. Use `set w := M.co.e.symm (p, q) with hw`. Establish `he : M.co.e (u • w) = (u • p, u • q)`. Rewrite using `[LinearEquiv.map_smul, hw, LinearEquiv.apply_symm_apply, Prod.smul_mk]`. Establish `h1 : u • (mat x.1 - 1) = 0` using `hx1 u hu`.

Establish `h2 : u • (mat x.2 - 1) = 0` using `hx2 u hu`. Establish `e1 : mat x.1 * (u • w) = u • w`. Establish `: mat x.1 * (u • w) - u • w = (u • (mat x.1 - 1)) * w`. Rewrite using `[Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_smul, smul_sub]`. Rewrite `this` using `[h1, Matrix.zero_mul, sub_eq_zero]`.

Conclude with `this`. Establish `e2 : (u • w) * (mat x.2)ᵀ = u • w`. Establish `: (u • w) * (mat x.2)ᵀ - u • w = w * (u • (mat x.2 - 1))ᵀ`. Rewrite using `[Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_sub, Matrix.transpose_one, Matrix.mul_sub, Matrix.mul_one, smul_sub]`. Rewrite `this` using `[h2, Matrix.transpose_zero, Matrix.mul_zero, sub_eq_zero]`.

Conclude with `this`. Establish `hact : GlobalTheory.WeilM.actAB (cA σ) x (u • w) = u • w`. Simplify using `only [GlobalTheory.WeilM.actAB]`. Use `e1` as an intermediate fact. Simplify using `only [mat] at this e2`.

Rewrite using `[this, e2]`. Establish `h3` using `hW.impl x (u • w) Φ hΦ`. Simplify using `only [GlobalTheory.WeilM.Darboux.rho, he, hact] at h3`. Conclude with `h3`.
-/
theorem comm_off {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {ψ : AddChar (AF F) ℂ} {χX χW : Chr F E}
    {om : Rep σ X W} (hWeil : M.IsWeil ψ χX χW om) (v : Pl F) (x : UA σ X.J × UA σ W.J)
    (hx1 : x.1 ∈ UAt σ X (evFin F v)) (hx2 : x.2 ∈ UAt σ W (evFin F v))
    (u : AF F) (hu : evFin F v u = 0) (p q : Fin n × Fin d → AF F) (Φ : (Fin n × Fin d → AF F) → ℂ)
    (hΦ : Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d)) :
    om x (GlobalTheory.WeilM.schr ψ (u • p, u • q) Φ) = GlobalTheory.WeilM.schr ψ (u • p, u • q) (om x Φ) := by
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hWeil
  set w := M.co.e.symm (p, q) with hw
  have he : M.co.e (u • w) = (u • p, u • q) := by
    rw [LinearEquiv.map_smul, hw, LinearEquiv.apply_symm_apply, Prod.smul_mk]
  have h1 : u • (mat x.1 - 1) = 0 := hx1 u hu
  have h2 : u • (mat x.2 - 1) = 0 := hx2 u hu
  have e1 : mat x.1 * (u • w) = u • w := by
    have : mat x.1 * (u • w) - u • w = (u • (mat x.1 - 1)) * w := by
      rw [Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_smul, smul_sub]
    rw [h1, Matrix.zero_mul, sub_eq_zero] at this
    exact this
  have e2 : (u • w) * (mat x.2)ᵀ = u • w := by
    have : (u • w) * (mat x.2)ᵀ - u • w = w * (u • (mat x.2 - 1))ᵀ := by
      rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_sub, Matrix.transpose_one,
        Matrix.mul_sub, Matrix.mul_one, smul_sub]
    rw [h2, Matrix.transpose_zero, Matrix.mul_zero, sub_eq_zero] at this
    exact this
  have hact : GlobalTheory.WeilM.actAB (cA σ) x (u • w) = u • w := by
    simp only [GlobalTheory.WeilM.actAB]
    have := e1
    simp only [mat] at this e2
    rw [this, e2]
  have h3 := hW.impl x (u • w) Φ hΦ
  simp only [GlobalTheory.WeilM.Darboux.rho, he, hact] at h3
  exact h3

/- English proof (translation)
Establish `hW` using `GlobalTheory.WeilM.IsUWeilPair.isUSplitting hWeil`. Use `set T := om x with hTdef`. Establish `hkeep : ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), T Φ ∈ GlobalTheory.WeilM.schA F _` using `fun Φ hΦ => hW.pres x Φ hΦ`. Establish `hcomm` using `comm_off hWeil v x hx1 hx2`. Establish `hfib` using `GlobalTheory.T.isometry_commuting_heisenberg_acts_fibrewise v ψ T hstd (GlobalTheory.T.standardAdelicAddChar_nontrivial_finitePlace ψ hstd) hkeep (fun μ hμ Φ hΦ => hW.unit μ hμ x Φ hΦ) hcomm`.

Establish `htr : ∀ u : AF F, evFin F v u = 0 → ∀ p : Fin n × Fin d → AF F, ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), T (fun y => Φ (y + u • p)) = fun y => T Φ (y + u • p)`. Introduce `u hu p Φ hΦ`. Establish `h` using `hcomm u hu p 0 Φ hΦ`. Rewrite `h` using `[smul_zero, GlobalTheory.ThK.LocalOps.schr_trans, GlobalTheory.ThK.LocalOps.schr_trans]`. Conclude with `h`.

Take `⟨R, hR0, hR⟩` from `GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction (Fin n × Fin d) v`. Use `⟨(R 0)⁻¹ • fun t => T (tens (evFin F v) φ R) (fun i => GlobalTheory.LatVac.liftV v (t i)), ?_, ?_⟩` and prove the remaining obligations. Conclude with `(GlobalTheory.WeilM.SB _).smul_mem (R 0)⁻¹ (GlobalTheory.T.adelicSchwartz_restrict_finitePlace_mem_schwartzBruhat v _ (hkeep _ (hR φ hφ).2))`. Introduce `r hr`. Use function extensionality and compare the values at `y`.

Use `set u : AF F := 1 - GlobalTheory.LatVac.liftV v 1 with hudef`. Establish `hu : evFin F v u = 0` using `by simp [hudef, GlobalTheory.LatVac.evFin_liftV]`. Use `set p : Fin n × Fin d → AF F := fun i => GlobalTheory.LatVac.liftV v (evFin F v (y i)) with hpdef`. Establish `hyp : y + u • (-y) = p`. Use function extensionality and compare the values at `i`.

Simplify using `only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, hudef, hpdef]`. Rewrite using `[← GlobalTheory.ThK.LocalOps.liftV_one_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hpat : At (evFin F v) p`. Introduce `u' hu'`.

Use function extensionality and compare the values at `i`. Conclude with `GlobalTheory.LatVac.at_liftV v _ u' hu'`. Use `set Φ₀ := tens (evFin F v) φ R with hΦ₀`. Use `set Φ₁ := tens (evFin F v) φ r with hΦ₁`. Use `set Φ₂ : (Fin n × Fin d → AF F) → ℂ := (r y / R 0) • (fun w => Φ₀ (w + u • (-y))) with hΦ₂`.

Establish `hm₀ : Φ₀ ∈ GlobalTheory.WeilM.schA F _` using `(hR φ hφ).2`. Establish `hm₂ : Φ₂ ∈ GlobalTheory.WeilM.schA F _` using `Submodule.smul_mem _ _ (GlobalTheory.T.adelicSchwartzSpace_translate_mem_of_mem _ _ hm₀)`. Establish `hfz : ∀ z, At (evFin F v) z → (Φ₁ - Φ₂) (y + z) = 0`. Introduce `z hz`. Establish `e1 : r (y + z) = r y` using `hr.1 y z hz`.

Establish `e2 : y + z + u • (-y) = p + z` using `by rw [← hyp]; abel`. Establish `hpz : At (evFin F v) (p + z)` using `fun u' hu' => by`. Rewrite using `[smul_add, hpat u' hu', hz u' hu', add_zero]`. Establish `e3 : R (p + z) = R 0` using `by simpa using (hR φ hφ).1 0 (p + z) hpz`. Establish `e4 : (fun i => evFin F v ((y + z + u • (-y)) i)) = fun i => evFin F v ((y + z) i)`.

Use function extensionality and compare the values at `i`. Simplify using `[hu]`. Simplify using `only [Pi.sub_apply, hΦ₂, hΦ₁, hΦ₀, Pi.smul_apply, smul_eq_mul, tens]`. Rewrite using `[e4, e2, e3, e1]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Establish `h0` using `hfib (Φ₁ - Φ₂) (sub_mem hr.2 hm₂) y hfz`. Rewrite `h0` using `[map_sub, Pi.sub_apply, sub_eq_zero]`. Establish `h2 : T Φ₂ y = (r y / R 0) * T Φ₀ p`. Rewrite using `[hΦ₂, map_smul, htr u hu (-y) Φ₀ hm₀, Pi.smul_apply, smul_eq_mul, hyp]`.

Rewrite using `[h0, h2]`. Simplify using `only [tens, hpdef, Pi.smul_apply, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts.
-/
theorem acts_exists {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {ψ : AddChar (AF F) ℂ} {χX χW : Chr F E}
    {om : Rep σ X W} (hstd : IsStd ψ) (hWeil : M.IsWeil ψ χX χW om) (v : Pl F) (x : UA σ X.J × UA σ W.J)
    (hx1 : x.1 ∈ UAt σ X (evFin F v)) (hx2 : x.2 ∈ UAt σ W (evFin F v))
    (φ : (Fin n × Fin d → Fv F v) → ℂ) (hφ : φ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) :
    ∃ φ₁ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v), Acts (evFin F v) (om x) φ φ₁ := by
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hWeil
  set T := om x with hTdef
  have hkeep : ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), T Φ ∈ GlobalTheory.WeilM.schA F _ :=
    fun Φ hΦ => hW.pres x Φ hΦ
  have hcomm := comm_off hWeil v x hx1 hx2
  have hfib := GlobalTheory.T.isometry_commuting_heisenberg_acts_fibrewise v ψ T hstd (GlobalTheory.T.standardAdelicAddChar_nontrivial_finitePlace ψ hstd) hkeep
    (fun μ hμ Φ hΦ => hW.unit μ hμ x Φ hΦ) hcomm
  have htr : ∀ u : AF F, evFin F v u = 0 → ∀ p : Fin n × Fin d → AF F,
      ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), T (fun y => Φ (y + u • p)) = fun y => T Φ (y + u • p) := by
    intro u hu p Φ hΦ
    have h := hcomm u hu p 0 Φ hΦ
    rw [smul_zero, GlobalTheory.ThK.LocalOps.schr_trans, GlobalTheory.ThK.LocalOps.schr_trans] at h
    exact h
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction (Fin n × Fin d) v
  refine ⟨(R 0)⁻¹ • fun t => T (tens (evFin F v) φ R) (fun i => GlobalTheory.LatVac.liftV v (t i)), ?_, ?_⟩
  · exact (GlobalTheory.WeilM.SB _).smul_mem (R 0)⁻¹ (GlobalTheory.T.adelicSchwartz_restrict_finitePlace_mem_schwartzBruhat v _ (hkeep _ (hR φ hφ).2))
  · intro r hr
    funext y
    set u : AF F := 1 - GlobalTheory.LatVac.liftV v 1 with hudef
    have hu : evFin F v u = 0 := by simp [hudef, GlobalTheory.LatVac.evFin_liftV]
    set p : Fin n × Fin d → AF F := fun i => GlobalTheory.LatVac.liftV v (evFin F v (y i)) with hpdef
    have hyp : y + u • (-y) = p := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, hudef, hpdef]
      rw [← GlobalTheory.ThK.LocalOps.liftV_one_mul]
      ring
    have hpat : At (evFin F v) p := by
      intro u' hu'
      funext i
      exact GlobalTheory.LatVac.at_liftV v _ u' hu'
    set Φ₀ := tens (evFin F v) φ R with hΦ₀
    set Φ₁ := tens (evFin F v) φ r with hΦ₁
    set Φ₂ : (Fin n × Fin d → AF F) → ℂ := (r y / R 0) • (fun w => Φ₀ (w + u • (-y))) with hΦ₂
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
Introduce `_hP F E _ _ _ _ _ σ _hCM n d X W M ψ χX χW om hstd _ _ _ _ _ _ _ _ hWeil v`. Establish `hex : ∀ g ∈ UAt σ X (evFin F v), ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∃ φ₁ ∈ SB (Fin n × Fin d → Fv F v), Acts (evFin F v) (om (g, h)) φ φ₁` using `fun g hg h hh φ hφ => acts_exists hstd hWeil v (g, h) hg hh φ hφ`. Use `⟨fun g hg h hh φ hφ => ?_, fun g hg h hh φ hφ φ' hφ' φ₁ φ₁' h1 h1' => ?_⟩` and prove the remaining obligations. Take `⟨φ₁, h1, h2⟩` from `hex g hg h hh φ hφ`. Conclude with `⟨φ₁, ⟨h1, h2⟩, fun φ₂ hφ₂ => GlobalTheory.ThK.LocalOps.acts_unique v _ hφ hφ₂.2 h2⟩`.

Use `GlobalTheory.ThK.LocalOps.acts_lin v (om (g, h)) (hex g hg h hh) hφ hφ' h1 h1' 1 1` as an intermediate fact. Simplify `this` using `only [one_smul]`.
-/
theorem ops : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ v : Pl F,
        (∀ g ∈ UAt σ X (evFin F v), ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
          ∃! φ₁, φ₁ ∈ SB (Fin n × Fin d → Fv F v) ∧ Acts (evFin F v) (om (g, h)) φ φ₁) ∧
        ∀ g ∈ UAt σ X (evFin F v), ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
          ∀ φ' ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ φ₁', Acts (evFin F v) (om (g, h)) φ φ₁ →
          Acts (evFin F v) (om (g, h)) φ' φ₁' → Acts (evFin F v) (om (g, h)) (φ + φ') (φ₁ + φ₁') := by
  intro _hP F E _ _ _ _ _ σ _hCM n d X W M ψ χX χW om hstd _ _ _ _ _ _ _ _ hWeil v
  have hex : ∀ g ∈ UAt σ X (evFin F v), ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      ∃ φ₁ ∈ SB (Fin n × Fin d → Fv F v), Acts (evFin F v) (om (g, h)) φ φ₁ :=
    fun g hg h hh φ hφ => acts_exists hstd hWeil v (g, h) hg hh φ hφ
  refine ⟨fun g hg h hh φ hφ => ?_, fun g hg h hh φ hφ φ' hφ' φ₁ φ₁' h1 h1' => ?_⟩
  · obtain ⟨φ₁, h1, h2⟩ := hex g hg h hh φ hφ
    exact ⟨φ₁, ⟨h1, h2⟩, fun φ₂ hφ₂ => GlobalTheory.ThK.LocalOps.acts_unique v _ hφ hφ₂.2 h2⟩
  · have := GlobalTheory.ThK.LocalOps.acts_lin v (om (g, h)) (hex g hg h hh) hφ hφ' h1 h1' 1 1
    simpa only [one_smul] using this

end GlobalTheory.LocalOpsW

end
