import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.LocalOperatorLongWeylIntegral
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopAway
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopCore
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopPlumb
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopRel
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopLocForm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopLocNbar
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopRelPf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopStepNM
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopLocJJA
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopStepWN

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace RD
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {w : InfinitePlace F}
  {L : GR d.n → ((Fin d.m → Fin d.n → ℂ) → ℂ) → (Fin d.m → Fin d.n → ℂ) → ℂ}
/- English proof (translation)
Establish `hsch` using `d.om_sch`. Establish `h4` using `R.step_comp w hsch (R.step_comp w hsch (R.step_comp w hsch hW' hW') hW') hW'`. Rewrite `h4` using `[_root_.PositivityTheory.SiegelWeilFormula.RD_k.w_four hw₀]`. Take `⟨Ψ, hΨ⟩` from `hG F E σ d R w`. Choose the witnesses or unpack the hypotheses as in `⟨X₀, hX₀⟩ : ∃ X₀, Ψ X₀ ≠ 0 := by`.

Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Conclude with `hΨ.2.1 (funext hc)`. Establish `hB4 : d.IsAwayW w (B (B (B (B Ψ))))` using `(h4.2 Ψ hΨ.1).1`. Establish `key : ∀ f : d.LF, IsSw f → ∀ X, f (R.loc w X) * Ψ X = locFT C s (locFT C s (locFT C s (locFT C s f))) (R.loc w X) * B (B (B (B Ψ))) X`.

Introduce `f hf X`. Take `⟨Φ, hΦ, hT'⟩` from `R.exists_adm hT hΨ hf`. Establish `e` using `(h4.2 Ψ hΨ.1).2 f hf Φ hΦ hT'`. Rewrite `e` using `[map_one, Module.End.one_apply, hT']`. Conclude with `congrFun e X`.

Establish `key0 : ∀ f : d.LF, IsSw f → ∀ u, f u * Ψ X₀ = locFT C s (locFT C s (locFT C s (locFT C s f))) u * B (B (B (B Ψ))) X₀`. Introduce `f hf u`. Take `⟨Z, hZ1, hZ2, hZ3⟩` from `R.loc_surj w X₀ u`. Use `key f hf (X₀ + Z)` as an intermediate fact. Rewrite `this` using `[hZ3, hΨ.1 X₀ Z hZ1 hZ2, hB4 X₀ Z hZ1 hZ2]`. Then use the resulting hypothesis.

Distinguish the cases in `hb : B (B (B (B Ψ))) X₀ = 0`. Establish `hz : ∀ f : d.LF, IsSw f → f = 0`. Introduce `f hf`. Use function extensionality and compare the values at `u`. Use `key0 f hf u` as an intermediate fact.

Rewrite `this` using `[hb, mul_zero]`. Conclude with `(mul_eq_zero.mp this).resolve_right hX₀`. Use `⟨1, one_ne_zero, fun f hf => ?_, fun y c hc hy f hf => ?_, fun y c hc hy f hf => ?_⟩` and prove the remaining obligations. Rewrite using `[hz f hf]`. Simplify using `[locFT_zero]`.

Rewrite using `[hz f hf, R.locOp_zero hT hG hL y]`. Simplify using `[locFT_zero, chirp_zero]`. Rewrite using `[hz f hf, R.locOp_zero hT hG hL y]`. Simplify using `[locFT_zero, chirp_zero]`. Use `set κ := Ψ X₀ / B (B (B (B Ψ))) X₀ with hκ`.

Establish `hκ0 : κ ≠ 0` using `div_ne_zero hX₀ hb`. Establish `h4f : ∀ f : d.LF, IsSw f → locFT C s (locFT C s (locFT C s (locFT C s f))) = κ • f`. Introduce `f hf`. Use function extensionality and compare the values at `u`. Use `key0 f hf u` as an intermediate fact.

Simplify using `only [Pi.smul_apply, smul_eq_mul, hκ]`. Clear the denominators using the available nonvanishing facts. Take the linear combination `-this`. Establish `hmain : ∀ (y : GR d.n) (c : Matrix (Fin d.n) (Fin d.n) ℂ), cᴴ = c → mR y = nbLoc c → ∀ f, IsSw f → IsSw (chirp ((R.sg w : ℤ) : ℂ) ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c) (locFT C s f)) ∧ L y f = κ⁻¹ • locFT C s (locFT C s (locFT C s (chirp ((R.sg w : ℤ) : ℂ) ((((ε : ℤ) : ℂ) * R.ζ⁻¹ …`. Introduce `y c hc hy f hf`.

Take `⟨y', hy', hrel⟩` from `R.oppositeUnipotent_weylConj w hw₀ y c hc hy`. Establish `hx : ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c)ᴴ = (((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c`. Establish `hs : star (((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) = ((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹`. Break down `R.hζ with ⟨-, hz⟩ | ⟨-, hz⟩` into its components or cases. Rewrite using `[hz]`.

Simplify using the standard rewrite rules. Rewrite using `[hz]`. Simplify using `[Complex.inv_I]`. Rewrite using `[Matrix.conjTranspose_smul, hc, hs]`. Establish `hN : R.StepOK w (R.ι w y') (chirp ((R.sg w : ℤ) : ℂ) ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c)) id` using `R.stepN w hT y' _ hx hy'`.

Use `⟨hN.1 _ (hW'.1 f hf), ?_⟩` and prove the remaining obligations. Distinguish the cases in `hf0 : ∀ u, f u = 0`. Establish `: f = 0` using `funext hf0`. Rewrite using `[this, R.locOp_zero hT hG hL y]`. Simplify using `[locFT_zero, chirp_zero]`.

Use `push Not at hf0`. Take `⟨u₀, hu₀⟩` from `hf0`. Establish `hBΨ : ∀ X, B (B (B (B Ψ))) X = κ⁻¹ * Ψ X`. Introduce `X`. Take `⟨Z, hZ1, hZ2, hZ3⟩` from `R.loc_surj w X u₀`.

Use `key f hf (X + Z)` as an intermediate fact. Rewrite `this` using `[hZ3, hΨ.1 X Z hZ1 hZ2, hB4 X Z hZ1 hZ2, h4f f hf]`. Simplify using `only [Pi.smul_apply, smul_eq_mul] at this`. Rewrite using `[eq_inv_mul_iff_mul_eq₀ hκ0]`. Apply `mul_left_cancel₀ hu₀` to reduce the goal to its premises.

Take the linear combination `-this`. Establish `hc3` using `R.step_comp w hsch (R.step_comp w hsch (R.step_comp w hsch (R.step_comp w hsch hW' hW') hW') hN) hW'`. Take `⟨Φ, hΦ, hT'⟩` from `R.exists_adm hT hΨ hf`. Establish `e` using `(hc3.2 Ψ hΨ.1).2 f hf Φ hΦ hT'`. Establish `e1` using `(hL y f hf).2 Ψ hΨ.1 Φ hΦ hT'`.

Rewrite `e1` using `[hrel]`. Apply `R.tens_cancel hΨ.1 hΨ.2.1` to reduce the goal to its premises. Rewrite using `[← e1, e]`. Use function extensionality and compare the values at `X`. Simplify using `only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, Function.comp_apply, id, Pi.smul_apply, smul_eq_mul, hBΨ]`.

Expand and normalize the polynomial expressions, which then agree. Use `⟨κ, hκ0, h4f, fun y c hc hy f hf => (hmain y c hc hy f hf).2, fun y c hc hy f hf => ?_⟩` and prove the remaining obligations. Take `⟨hsw, heq⟩` from `hmain y c hc hy f hf`. Rewrite using `[heq, locFT_smul, h4f _ hsw, smul_smul, inv_mul_cancel₀ hκ0, one_smul]`.
-/
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.locOp_nbar_of (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hG : _root_.PositivityTheory.SiegelWeilFormula.GoodAwayEx_k) (hL : R.IsLocOp w L) {ε : ℤˣ} {w₀ : d.G} (hw₀ : d.IsW ε w₀)
    {C s : ℂ} {B : d.MF → d.MF} (hW' : R.StepOK w w₀ (locFT C s) B) :
    ∃ κ : ℂ, κ ≠ 0 ∧
      (∀ f : d.LF, IsSw f → locFT C s (locFT C s (locFT C s (locFT C s f))) = κ • f) ∧
      (∀ (y : GR d.n) (c : Matrix (Fin d.n) (Fin d.n) ℂ), cᴴ = c → mR y = nbLoc c → ∀ f, IsSw f →
        L y f = κ⁻¹ • locFT C s (locFT C s (locFT C s
          (chirp ((R.sg w : ℤ) : ℂ) ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c) (locFT C s f))))) ∧
      ∀ (y : GR d.n) (c : Matrix (Fin d.n) (Fin d.n) ℂ), cᴴ = c → mR y = nbLoc c → ∀ f, IsSw f →
        locFT C s (L y f) = chirp ((R.sg w : ℤ) : ℂ) ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c) (locFT C s f) := by
  have hsch := d.om_sch
  have h4 := R.step_comp w hsch (R.step_comp w hsch (R.step_comp w hsch hW' hW') hW') hW'
  rw [_root_.PositivityTheory.SiegelWeilFormula.RD_k.w_four hw₀] at h4
  obtain ⟨Ψ, hΨ⟩ := hG F E σ d R w
  obtain ⟨X₀, hX₀⟩ : ∃ X₀, Ψ X₀ ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hΨ.2.1 (funext hc)
  have hB4 : d.IsAwayW w (B (B (B (B Ψ)))) := (h4.2 Ψ hΨ.1).1
  have key : ∀ f : d.LF, IsSw f → ∀ X, f (R.loc w X) * Ψ X =
      locFT C s (locFT C s (locFT C s (locFT C s f))) (R.loc w X) * B (B (B (B Ψ))) X := by
    intro f hf X
    obtain ⟨Φ, hΦ, hT'⟩ := R.exists_adm hT hΨ hf
    have e := (h4.2 Ψ hΨ.1).2 f hf Φ hΦ hT'
    rw [map_one, Module.End.one_apply, hT'] at e
    exact congrFun e X
  have key0 : ∀ f : d.LF, IsSw f → ∀ u, f u * Ψ X₀ =
      locFT C s (locFT C s (locFT C s (locFT C s f))) u * B (B (B (B Ψ))) X₀ := by
    intro f hf u
    obtain ⟨Z, hZ1, hZ2, hZ3⟩ := R.loc_surj w X₀ u
    have := key f hf (X₀ + Z)
    rwa [hZ3, hΨ.1 X₀ Z hZ1 hZ2, hB4 X₀ Z hZ1 hZ2] at this
  by_cases hb : B (B (B (B Ψ))) X₀ = 0
  · have hz : ∀ f : d.LF, IsSw f → f = 0 := by
      intro f hf
      funext u
      have := key0 f hf u
      rw [hb, mul_zero] at this
      exact (mul_eq_zero.mp this).resolve_right hX₀
    refine ⟨1, one_ne_zero, fun f hf => ?_, fun y c hc hy f hf => ?_, fun y c hc hy f hf => ?_⟩
    · rw [hz f hf]
      simp [locFT_zero]
    · rw [hz f hf, R.locOp_zero hT hG hL y]
      simp [locFT_zero, chirp_zero]
    · rw [hz f hf, R.locOp_zero hT hG hL y]
      simp [locFT_zero, chirp_zero]
  · set κ := Ψ X₀ / B (B (B (B Ψ))) X₀ with hκ
    have hκ0 : κ ≠ 0 := div_ne_zero hX₀ hb
    have h4f : ∀ f : d.LF, IsSw f → locFT C s (locFT C s (locFT C s (locFT C s f))) = κ • f := by
      intro f hf
      funext u
      have := key0 f hf u
      simp only [Pi.smul_apply, smul_eq_mul, hκ]
      field_simp
      linear_combination -this
    have hmain : ∀ (y : GR d.n) (c : Matrix (Fin d.n) (Fin d.n) ℂ), cᴴ = c → mR y = nbLoc c → ∀ f, IsSw f →
        IsSw (chirp ((R.sg w : ℤ) : ℂ) ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c) (locFT C s f)) ∧
        L y f = κ⁻¹ • locFT C s (locFT C s (locFT C s
          (chirp ((R.sg w : ℤ) : ℂ) ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c) (locFT C s f)))) := by
      intro y c hc hy f hf
      obtain ⟨y', hy', hrel⟩ := R.oppositeUnipotent_weylConj w hw₀ y c hc hy
      have hx : ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c)ᴴ = (((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c := by
        have hs : star (((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) = ((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹ := by
          rcases R.hζ with ⟨-, hz⟩ | ⟨-, hz⟩
          · rw [hz]; simp
          · rw [hz]; simp [Complex.inv_I]
        rw [Matrix.conjTranspose_smul, hc, hs]
      have hN : R.StepOK w (R.ι w y') (chirp ((R.sg w : ℤ) : ℂ) ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c)) id :=
        R.stepN w hT y' _ hx hy'
      refine ⟨hN.1 _ (hW'.1 f hf), ?_⟩
      by_cases hf0 : ∀ u, f u = 0
      · have : f = 0 := funext hf0
        rw [this, R.locOp_zero hT hG hL y]
        simp [locFT_zero, chirp_zero]
      push Not at hf0
      obtain ⟨u₀, hu₀⟩ := hf0
      have hBΨ : ∀ X, B (B (B (B Ψ))) X = κ⁻¹ * Ψ X := by
        intro X
        obtain ⟨Z, hZ1, hZ2, hZ3⟩ := R.loc_surj w X u₀
        have := key f hf (X + Z)
        rw [hZ3, hΨ.1 X Z hZ1 hZ2, hB4 X Z hZ1 hZ2, h4f f hf] at this
        simp only [Pi.smul_apply, smul_eq_mul] at this
        rw [eq_inv_mul_iff_mul_eq₀ hκ0]
        apply mul_left_cancel₀ hu₀
        linear_combination -this
      have hc3 := R.step_comp w hsch (R.step_comp w hsch (R.step_comp w hsch (R.step_comp w hsch hW' hW') hW') hN) hW'
      obtain ⟨Φ, hΦ, hT'⟩ := R.exists_adm hT hΨ hf
      have e := (hc3.2 Ψ hΨ.1).2 f hf Φ hΦ hT'
      have e1 := (hL y f hf).2 Ψ hΨ.1 Φ hΦ hT'
      rw [hrel] at e1
      apply R.tens_cancel hΨ.1 hΨ.2.1
      rw [← e1, e]
      funext X
      simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, Function.comp_apply, id, Pi.smul_apply, smul_eq_mul, hBΨ]
      ring
    refine ⟨κ, hκ0, h4f, fun y c hc hy f hf => (hmain y c hc hy f hf).2,
      fun y c hc hy f hf => ?_⟩
    obtain ⟨hsw, heq⟩ := hmain y c hc hy f hf
    rw [heq, locFT_smul, h4f _ hsw, smul_smul, inv_mul_cancel₀ hκ0, one_smul]
/- English proof (translation)
Take `⟨-, ⟨ε, w₀, hw₀, -⟩, -⟩` from `hA F E σ d`. Establish `hεR : ε = R.ε` using `R.isW_eps w hw₀`. Take `⟨C₀, B, hC₀, hW⟩` from `R.stepW_exp w hT hA ε w₀ hw₀`. Use `set s : ℂ := -2 * ((ε : ℤ) : ℂ) * ((R.sg w : ℤ) : ℂ) / R.ζ with hs_def`. Establish `hW' : R.StepOK w w₀ (locFT C₀ s) B` using `hW`.

Take `⟨κ, hκ, -, hnb, -⟩` from `R.locOp_nbar_of hT hG hL hw₀ hW'`. Establish `hk : ((R.sg w : ℤ) : ℝ) ≠ 0` using `Int.cast_ne_zero.mpr (Units.ne_zero _)`. Establish `hζn : ‖R.ζ‖ = 1`. Apply the tactic sequence `rcases R.hζ with ⟨-, hz⟩ | ⟨-, hz⟩ <;> rw [hz] <;> simp`. Establish `hunit : ∀ u : ℤˣ, ‖((u : ℤ) : ℂ)‖ = 1` using `fun u => by`.

Apply the tactic sequence `rcases Int.units_eq_one_or u with h | h <;> rw [h] <;> simp`. Establish `hsn : ‖s‖ = 2 * |((R.sg w : ℤ) : ℝ)|`. Establish `h1 : |((R.sg w : ℤ) : ℝ)| = 1`. Apply the tactic sequence `rcases Int.units_eq_one_or (R.sg w) with h | h <;> rw [h] <;> simp`. Rewrite using `[h1, hs_def, norm_div, norm_mul, norm_mul, hunit, hunit, hζn]`.

Evaluate the numerical expressions. Take `⟨c, hc, hfres⟩` from `GlobalTheory.T.fourier_transform_matrix_space_involution d.m d.n C₀ s ((R.sg w : ℤ) : ℝ) hC₀ hk hsn`. Use `⟨κ⁻¹ * c, mul_ne_zero (inv_ne_zero hκ) hc, fun y hy f hf => ?_⟩` and prove the remaining obligations. Take `⟨y₁, y₂, h1, h2, rfl⟩` from `jj_split y hy`. Establish `hb1 : (1 : Matrix (Fin d.n) (Fin d.n) ℂ)ᴴ = 1` using `Matrix.conjTranspose_one`.

Establish `hbm : (-1 : Matrix (Fin d.n) (Fin d.n) ℂ)ᴴ = -1` using `by rw [Matrix.conjTranspose_neg, Matrix.conjTranspose_one]`. Establish `hf1 : IsSw (L y₁ f)` using `(hL y₁ f hf).1`. Establish `hf2 : IsSw (L y₂ (L y₁ f))` using `(hL y₂ _ hf1).1`. Rewrite using `[R.locOp_mul hT hG hL (y₁ * y₂) y₁ f hf, R.locOp_mul hT hG hL y₁ y₂ _ hf1, R.locOp_nU hT hG hL y₁ 1 hb1 h1 _ hf2, hnb y₂ (-1) hbm h2 _ hf1, R.locOp_nU hT hG hL y₁ 1 hb1 h1 f hf]`. Establish `hx : (((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • (-1 : Matrix (Fin d.n) (Fin d.n) ℂ) = 1`.

Rewrite using `[hεR]`. Apply the tactic sequence `rcases R.hζ with ⟨he, hz⟩ | ⟨he, hz⟩ <;> rw [he, hz] <;> simp [Complex.inv_I]`. Rewrite using `[hx]`. Take `⟨φ, hφ⟩` from `hf`. Establish `hch : ∀ g : d.LF, chirp ((R.sg w : ℤ) : ℂ) (1 : Matrix (Fin d.n) (Fin d.n) ℂ) g = fun u => Complex.exp (2 * Real.pi * Complex.I * (((R.sg w : ℤ) : ℝ) : ℂ) * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of u)) * g u` using `fun g => by`.

Use function extensionality and compare the values at `u`. Simplify using `[chirp]`. Establish `hin : (fun u => Complex.exp (2 * Real.pi * Complex.I * ((R.sg w : ℤ) : ℂ) * Matrix.trace ((1 : Matrix (Fin d.n) (Fin d.n) ℂ) * ((Matrix.of u)ᴴ * Matrix.of u))) * f u) = chirp ((R.sg w : ℤ) : ℂ) 1 f` using `rfl`. Establish `h0 : Complex.exp (2 * Real.pi * Complex.I * ((R.sg w : ℤ) : ℂ) * Matrix.trace ((1 : Matrix (Fin d.n) (Fin d.n) ℂ) * ((Matrix.of (0 : Fin d.m → Fin d.n → ℂ))ᴴ * Matrix.of (0 : Fin d.m → Fin d.n → ℂ)))) = 1`. Simplify using the standard rewrite rules.

Simplify using `only [hin]`. Rewrite using `[h0, one_mul, Pi.smul_apply, smul_eq_mul, hch, hch, ← hφ]`. Use `hfres φ` as an intermediate fact. Simplify using `only [locFT] at this ⊢`. Rewrite using `[this, hφ]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.localOperator_longWeyl_integral (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hG : _root_.PositivityTheory.SiegelWeilFormula.GoodAwayEx_k) (hL : R.IsLocOp w L) :
    ∃ C : ℂ, C ≠ 0 ∧ ∀ y : GR d.n, mR y = JJ d.n → ∀ f, IsSw f → L y f 0 = C * ∫ v, f v := by
  obtain ⟨-, ⟨ε, w₀, hw₀, -⟩, -⟩ := hA F E σ d
  have hεR : ε = R.ε := R.isW_eps w hw₀
  obtain ⟨C₀, B, hC₀, hW⟩ := R.stepW_exp w hT hA ε w₀ hw₀
  set s : ℂ := -2 * ((ε : ℤ) : ℂ) * ((R.sg w : ℤ) : ℂ) / R.ζ with hs_def
  have hW' : R.StepOK w w₀ (locFT C₀ s) B := hW
  obtain ⟨κ, hκ, -, hnb, -⟩ := R.locOp_nbar_of hT hG hL hw₀ hW'
  have hk : ((R.sg w : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr (Units.ne_zero _)
  have hζn : ‖R.ζ‖ = 1 := by
    rcases R.hζ with ⟨-, hz⟩ | ⟨-, hz⟩ <;> rw [hz] <;> simp
  have hunit : ∀ u : ℤˣ, ‖((u : ℤ) : ℂ)‖ = 1 := fun u => by
    rcases Int.units_eq_one_or u with h | h <;> rw [h] <;> simp
  have hsn : ‖s‖ = 2 * |((R.sg w : ℤ) : ℝ)| := by
    have h1 : |((R.sg w : ℤ) : ℝ)| = 1 := by
      rcases Int.units_eq_one_or (R.sg w) with h | h <;> rw [h] <;> simp
    rw [h1, hs_def, norm_div, norm_mul, norm_mul, hunit, hunit, hζn]
    norm_num
  obtain ⟨c, hc, hfres⟩ := GlobalTheory.T.fourier_transform_matrix_space_involution d.m d.n C₀ s ((R.sg w : ℤ) : ℝ) hC₀ hk hsn
  refine ⟨κ⁻¹ * c, mul_ne_zero (inv_ne_zero hκ) hc, fun y hy f hf => ?_⟩
  obtain ⟨y₁, y₂, h1, h2, rfl⟩ := jj_split y hy
  have hb1 : (1 : Matrix (Fin d.n) (Fin d.n) ℂ)ᴴ = 1 := Matrix.conjTranspose_one
  have hbm : (-1 : Matrix (Fin d.n) (Fin d.n) ℂ)ᴴ = -1 := by rw [Matrix.conjTranspose_neg, Matrix.conjTranspose_one]
  have hf1 : IsSw (L y₁ f) := (hL y₁ f hf).1
  have hf2 : IsSw (L y₂ (L y₁ f)) := (hL y₂ _ hf1).1
  rw [R.locOp_mul hT hG hL (y₁ * y₂) y₁ f hf, R.locOp_mul hT hG hL y₁ y₂ _ hf1,
    R.locOp_nU hT hG hL y₁ 1 hb1 h1 _ hf2, hnb y₂ (-1) hbm h2 _ hf1, R.locOp_nU hT hG hL y₁ 1 hb1 h1 f hf]
  have hx : (((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • (-1 : Matrix (Fin d.n) (Fin d.n) ℂ) = 1 := by
    rw [hεR]
    rcases R.hζ with ⟨he, hz⟩ | ⟨he, hz⟩ <;> rw [he, hz] <;> simp [Complex.inv_I]
  rw [hx]
  obtain ⟨φ, hφ⟩ := hf
  have hch : ∀ g : d.LF, chirp ((R.sg w : ℤ) : ℂ) (1 : Matrix (Fin d.n) (Fin d.n) ℂ) g =
      fun u => Complex.exp (2 * Real.pi * Complex.I * (((R.sg w : ℤ) : ℝ) : ℂ) *
        Matrix.trace ((Matrix.of u)ᴴ * Matrix.of u)) * g u := fun g => by
    funext u
    simp [chirp]
  have hin : (fun u => Complex.exp (2 * Real.pi * Complex.I * ((R.sg w : ℤ) : ℂ) *
      Matrix.trace ((1 : Matrix (Fin d.n) (Fin d.n) ℂ) * ((Matrix.of u)ᴴ * Matrix.of u))) * f u) =
      chirp ((R.sg w : ℤ) : ℂ) 1 f := rfl
  have h0 : Complex.exp (2 * Real.pi * Complex.I * ((R.sg w : ℤ) : ℂ) *
      Matrix.trace ((1 : Matrix (Fin d.n) (Fin d.n) ℂ) *
        ((Matrix.of (0 : Fin d.m → Fin d.n → ℂ))ᴴ * Matrix.of (0 : Fin d.m → Fin d.n → ℂ)))) = 1 := by
    simp
  simp only [hin]
  rw [h0, one_mul, Pi.smul_apply, smul_eq_mul, hch, hch, ← hφ]
  have := hfres φ
  simp only [locFT] at this ⊢
  rw [this, hφ]
  ring
end RD
end PositivityTheory.SiegelWeilFormula
end
end
