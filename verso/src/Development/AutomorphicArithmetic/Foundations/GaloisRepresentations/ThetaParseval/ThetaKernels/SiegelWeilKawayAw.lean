import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AwayActions.AwayActOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopCore
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopAway
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopPlumb
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.AdDecompK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKawayAwStep
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopStepW
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopRel

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.KAway
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace Step
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F)
/- English proof (translation)
Introduce `X Z hZ hf`. Simplify using `only [Pi.smul_apply, hΨ X Z hZ hf]`.
-/
theorem away_smul_k {Ψ : d.MF} (hΨ : d.IsAwayW w Ψ) (c : ℂ) : d.IsAwayW w (c • Ψ) := by
  intro X Z hZ hf
  simp only [Pi.smul_apply, hΨ X Z hZ hf]
/- English proof (translation)
Introduce `_ _ _ _` and use `rfl`.
-/
theorem away_zero_k : d.IsAwayW w (0 : d.MF) := fun _ _ _ _ => rfl
/- English proof (translation)
Introduce `u X`. Take `⟨Z, hZ1, hZ2, hZ3⟩` from `R.loc_surj w X u`. Use `congrFun h (X + Z)` as an intermediate fact. Simplify using `only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, hZ3, hΨ X Z hZ1 hZ2, hΨ' X Z hZ1 hZ2] at this`. Conclude with `this`.
-/
theorem tens_key_k {f g : d.LF} {Ψ Ψ' : d.MF} (hΨ : d.IsAwayW w Ψ) (hΨ' : d.IsAwayW w Ψ')
    (h : R.tens w f Ψ = R.tens w g Ψ') : ∀ u X, f u * Ψ X = g u * Ψ' X := by
  intro u X
  obtain ⟨Z, hZ1, hZ2, hZ3⟩ := R.loc_surj w X u
  have := congrFun h (X + Z)
  simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, hZ3, hΨ X Z hZ1 hZ2, hΨ' X Z hZ1 hZ2] at this
  exact this
/- English proof (translation)
Establish `hsch` using `d.om_sch`. Establish `hc` using `R.step_comp w hsch (R.step_comp w hsch h₁ h') h₂`. Establish `h0` using `R.step_comp w hsch h₁ h₂`. Use `⟨fun Ψ => if h : ∃ X₀, Ψ X₀ ≠ 0 ∧ B₁ (B₂ Ψ) X₀ ≠ 0 then (Ψ h.choose / B₁ (B₂ Ψ) h.choose) • B₁ (B' (B₂ Ψ)) else 0, fun f hf => hf, fun Ψ hΨ => ⟨?_, fun f hf Φ hΦ hTΦ => ?_⟩⟩` and prove the remaining obligations. Simplify using `only split_ifs with h`.

Conclude with `_root_.PositivityTheory.SiegelWeilFormula.KAway.Step.away_smul_k w (hc.2 Ψ hΨ).1 _`. Conclude with `_root_.PositivityTheory.SiegelWeilFormula.KAway.Step.away_zero_k w`. Establish `e` using `(hc.2 Ψ hΨ).2 f hf Φ hΦ hTΦ`. Establish `e0` using `(h0.2 Ψ hΨ).2 f hf Φ hΦ hTΦ`. Rewrite `e0` using `[h1, map_one, Module.End.one_apply, hTΦ]`.

Establish `key : ∀ u X, f u * Ψ X = A₁ (A₂ f) u * B₁ (B₂ Ψ) X` using `_root_.PositivityTheory.SiegelWeilFormula.KAway.Step.tens_key_k R w hΨ (h0.2 Ψ hΨ).1 e0`. Distinguish the cases in `hz : (∀ u, f u = 0) ∨ ∀ X, Ψ X = 0`. Establish `hΦ0 : Φ = 0` using `d.T_inj hT Φ hΦ (by`. Rewrite using `[hTΦ]`. Use function extensionality and compare the values at `X`.

Apply the tactic sequence `rcases hz with hz | hz <;> simp [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, hz])`. Substitute `hΦ0` using the available equality. Rewrite using `[map_zero, d.T_zero]`. Use function extensionality and compare the values at `X`. Break down `hz with hz | hz` into its components or cases.

Simplify using `[_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, hz]`. Establish `hn : ¬ ∃ X₀, Ψ X₀ ≠ 0 ∧ B₁ (B₂ Ψ) X₀ ≠ 0` using `fun ⟨X₀, h, _⟩ => h (hz X₀)`. Simplify using `[_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, dif_neg hn]`. Use `push_neg at hz`. Take `⟨⟨u₀, hu₀⟩, ⟨X₁, hX₁⟩⟩` from `hz`.

Establish `hex : ∃ X₀, Ψ X₀ ≠ 0 ∧ B₁ (B₂ Ψ) X₀ ≠ 0`. Use `⟨X₁, hX₁, fun h0' => ?_⟩` and prove the remaining obligations. Use `key u₀ X₁` as an intermediate fact. Rewrite `this` using `[h0', mul_zero]`. Conclude with `mul_ne_zero hu₀ hX₁ this`.

Establish `hB0` using `hex.choose_spec.2`. Establish `hA : ∀ u, A₁ (A₂ f) u = f u * (Ψ hex.choose / B₁ (B₂ Ψ) hex.choose)`. Introduce `u`. Use `key u hex.choose` as an intermediate fact. Rewrite using `[mul_div_assoc', eq_div_iff hB0]`.

Take the linear combination `-this`. Rewrite using `[e]`. Use function extensionality and compare the values at `X`. Simplify using `only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, Function.comp_apply, id_eq, dif_pos hex, Pi.smul_apply, smul_eq_mul, hA]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem away_conj_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) {x₁ x₂ x' : d.G} {A₁ A₂ : d.LF → d.LF} {B₁ B₂ B' : d.MF → d.MF}
    (h₁ : R.StepOK w x₁ A₁ B₁) (h₂ : R.StepOK w x₂ A₂ B₂) (h' : R.StepOK w x' id B') (h1 : x₁ * x₂ = 1) :
    ∃ B, R.StepOK w (x₁ * x' * x₂) id B := by
  have hsch := d.om_sch
  have hc := R.step_comp w hsch (R.step_comp w hsch h₁ h') h₂
  have h0 := R.step_comp w hsch h₁ h₂
  refine ⟨fun Ψ => if h : ∃ X₀, Ψ X₀ ≠ 0 ∧ B₁ (B₂ Ψ) X₀ ≠ 0 then
      (Ψ h.choose / B₁ (B₂ Ψ) h.choose) • B₁ (B' (B₂ Ψ)) else 0,
    fun f hf => hf, fun Ψ hΨ => ⟨?_, fun f hf Φ hΦ hTΦ => ?_⟩⟩
  · dsimp only
    split_ifs with h
    · exact _root_.PositivityTheory.SiegelWeilFormula.KAway.Step.away_smul_k w (hc.2 Ψ hΨ).1 _
    · exact _root_.PositivityTheory.SiegelWeilFormula.KAway.Step.away_zero_k w
  · have e := (hc.2 Ψ hΨ).2 f hf Φ hΦ hTΦ
    have e0 := (h0.2 Ψ hΨ).2 f hf Φ hΦ hTΦ
    rw [h1, map_one, Module.End.one_apply, hTΦ] at e0
    have key : ∀ u X, f u * Ψ X = A₁ (A₂ f) u * B₁ (B₂ Ψ) X := _root_.PositivityTheory.SiegelWeilFormula.KAway.Step.tens_key_k R w hΨ (h0.2 Ψ hΨ).1 e0
    by_cases hz : (∀ u, f u = 0) ∨ ∀ X, Ψ X = 0
    · have hΦ0 : Φ = 0 := d.T_inj hT Φ hΦ (by
        rw [hTΦ]
        funext X
        rcases hz with hz | hz <;> simp [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, hz])
      subst hΦ0
      rw [map_zero, d.T_zero]
      funext X
      rcases hz with hz | hz
      · simp [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, hz]
      · have hn : ¬ ∃ X₀, Ψ X₀ ≠ 0 ∧ B₁ (B₂ Ψ) X₀ ≠ 0 := fun ⟨X₀, h, _⟩ => h (hz X₀)
        simp [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, dif_neg hn]
    · push_neg at hz
      obtain ⟨⟨u₀, hu₀⟩, ⟨X₁, hX₁⟩⟩ := hz
      have hex : ∃ X₀, Ψ X₀ ≠ 0 ∧ B₁ (B₂ Ψ) X₀ ≠ 0 := by
        refine ⟨X₁, hX₁, fun h0' => ?_⟩
        have := key u₀ X₁
        rw [h0', mul_zero] at this
        exact mul_ne_zero hu₀ hX₁ this
      have hB0 := hex.choose_spec.2
      have hA : ∀ u, A₁ (A₂ f) u = f u * (Ψ hex.choose / B₁ (B₂ Ψ) hex.choose) := by
        intro u
        have := key u hex.choose
        rw [mul_div_assoc', eq_div_iff hB0]
        linear_combination -this
      rw [e]
      funext X
      simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, Function.comp_apply, id_eq, dif_pos hex, Pi.smul_apply, smul_eq_mul, hA]
      ring
end Step
/- English proof (translation)
Introduce `hT hA hD F E _ _ _ _ _ σ d R w x hx`. Establish `hsch` using `d.om_sch`. Take `⟨-, ⟨ε, w₀, hw₀, -⟩, -⟩` from `hA F E σ d`. Establish `he : eW w • inFrame d.b x = eW w • (1 : Matrix _ _ (AE F E))` using `(_root_.PositivityTheory.SiegelWeilFormula.KAway.eW_smul_eq_iff_k d w _ _).2 (by rw [hx, _root_.PositivityTheory.SiegelWeilFormula.KAway.cw_one_k])`. Take `⟨x₁, x₂, x₃, x₄, t, c, b, a, a', hxe, h1, h2, h3, h4, ht, hc, hb, -, ha'⟩` from `hD F E σ d ε w₀ hw₀ (eW w) (eW_mul_self w) x he`.

Take `⟨C, s, BW, -, hW⟩` from `R.stepW w hT hA ε w₀ hw₀`. Establish `hW3` using `R.step_comp w hsch (R.step_comp w hsch hW hW) hW`. Establish `h4' : w₀ * (w₀ * w₀ * w₀) = 1`. Simplify `_root_.PositivityTheory.SiegelWeilFormula.RD_k.w_four hw₀` using `only [mul_assoc]`. Take `⟨BC, hC⟩` from `_root_.PositivityTheory.SiegelWeilFormula.KAway.Step.away_conj_k R w hT hW hW3 (_root_.PositivityTheory.SiegelWeilFormula.KAway.Step.stepN_k R w hT x₂ c h2 hc) h4'`.

Establish `hinv : w₀⁻¹ = w₀ * w₀ * w₀` using `(eq_inv_of_mul_eq_one_left (_root_.PositivityTheory.SiegelWeilFormula.RD_k.w_four hw₀)).symm`. Establish `hall` using `R.step_comp w hsch (R.step_comp w hsch (R.step_comp w hsch (_root_.PositivityTheory.SiegelWeilFormula.KAway.Step.stepN_k R w hT x₁ t h1 ht) hC) (_root_.PositivityTheory.SiegelWeilFormula.KAway.Step.stepM_k R w hT x₃ a a' h3 ha')) (_root_.PositivityTheory.SiegelWeilFormula.KAway.S …`. Rewrite using `[hxe, hinv]`. Conclude with `⟨_, fun Ψ hΨ => ⟨(hall.2 Ψ hΨ).1, fun f hf Φ hΦ hTΦ => (hall.2 Ψ hΨ).2 f hf Φ hΦ hTΦ⟩⟩`.
-/
theorem awayAct_of_k : _root_.PositivityTheory.SiegelWeilFormula.TAll_k → _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties → _root_.PositivityTheory.SiegelWeilFormula.AdDecomp_k → _root_.PositivityTheory.SiegelWeilFormula.AwayAct_k := by
  intro hT hA hD F E _ _ _ _ _ σ d R w x hx
  have hsch := d.om_sch
  obtain ⟨-, ⟨ε, w₀, hw₀, -⟩, -⟩ := hA F E σ d
  have he : eW w • inFrame d.b x = eW w • (1 : Matrix _ _ (AE F E)) :=
    (_root_.PositivityTheory.SiegelWeilFormula.KAway.eW_smul_eq_iff_k d w _ _).2 (by rw [hx, _root_.PositivityTheory.SiegelWeilFormula.KAway.cw_one_k])
  obtain ⟨x₁, x₂, x₃, x₄, t, c, b, a, a', hxe, h1, h2, h3, h4, ht, hc, hb, -, ha'⟩ :=
    hD F E σ d ε w₀ hw₀ (eW w) (eW_mul_self w) x he
  obtain ⟨C, s, BW, -, hW⟩ := R.stepW w hT hA ε w₀ hw₀
  have hW3 := R.step_comp w hsch (R.step_comp w hsch hW hW) hW
  have h4' : w₀ * (w₀ * w₀ * w₀) = 1 := by
    simpa only [mul_assoc] using _root_.PositivityTheory.SiegelWeilFormula.RD_k.w_four hw₀
  obtain ⟨BC, hC⟩ := _root_.PositivityTheory.SiegelWeilFormula.KAway.Step.away_conj_k R w hT hW hW3 (_root_.PositivityTheory.SiegelWeilFormula.KAway.Step.stepN_k R w hT x₂ c h2 hc) h4'
  have hinv : w₀⁻¹ = w₀ * w₀ * w₀ := (eq_inv_of_mul_eq_one_left (_root_.PositivityTheory.SiegelWeilFormula.RD_k.w_four hw₀)).symm
  have hall := R.step_comp w hsch (R.step_comp w hsch (R.step_comp w hsch (_root_.PositivityTheory.SiegelWeilFormula.KAway.Step.stepN_k R w hT x₁ t h1 ht) hC)
    (_root_.PositivityTheory.SiegelWeilFormula.KAway.Step.stepM_k R w hT x₃ a a' h3 ha')) (_root_.PositivityTheory.SiegelWeilFormula.KAway.Step.stepN_k R w hT x₄ b h4 hb)
  rw [hxe, hinv]
  exact ⟨_, fun Ψ hΨ => ⟨(hall.2 Ψ hΨ).1, fun f hf Φ hΦ hTΦ => (hall.2 Ψ hΨ).2 f hf Φ hΦ hTΦ⟩⟩
end PositivityTheory.SiegelWeilFormula.KAway
end
end
