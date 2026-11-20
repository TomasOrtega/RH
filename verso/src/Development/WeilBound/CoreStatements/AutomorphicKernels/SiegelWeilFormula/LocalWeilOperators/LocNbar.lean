import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.LocForm
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.StepW
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.NbarConj
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.OppositeUnipotentWeylConj
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.StepWN
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.LocJJA

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula

def locFT {m n : ℕ} (C s : ℂ) (g : (Fin m → Fin n → ℂ) → ℂ) : (Fin m → Fin n → ℂ) → ℂ :=
  fun u => C * ∫ v : Fin m → Fin n → ℂ,
    Complex.exp (2 * Real.pi * Complex.I * ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * g v

def chirp {m n : ℕ} (k : ℂ) (x : Matrix (Fin n) (Fin n) ℂ) (g : (Fin m → Fin n → ℂ) → ℂ) :
    (Fin m → Fin n → ℂ) → ℂ :=
  fun u => Complex.exp (2 * Real.pi * Complex.I * k * Matrix.trace (x * ((Matrix.of u)ᴴ * Matrix.of u))) * g u

/- English proof (translation)
Use function extensionality and compare the values at `u`. Simplify using `[locFT]`.
-/
theorem locFT_zero {m n : ℕ} (C s : ℂ) : locFT (m := m) (n := n) C s 0 = 0 := by
  funext u
  simp [locFT]

/- English proof (translation)
Use function extensionality and compare the values at `u`. Simplify using `[chirp]`.
-/
theorem chirp_zero {m n : ℕ} (k : ℂ) (x : Matrix (Fin n) (Fin n) ℂ) : chirp (m := m) k x 0 = 0 := by
  funext u
  simp [chirp]

/- English proof (translation)
Use function extensionality and compare the values at `u`. Simplify using `only [locFT, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[show (fun v : Fin m → Fin n → ℂ => Complex.exp (2 * Real.pi * Complex.I * ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * (a * g v)) = fun v => a * (Complex.exp (2 * Real.pi * Complex.I * ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * g v) from`. Use function extensionality and compare the values at `fun v => by ring, integral_const_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem locFT_smul {m n : ℕ} (C s a : ℂ) (g : (Fin m → Fin n → ℂ) → ℂ) :
    locFT C s (a • g) = a • locFT C s g := by
  funext u
  simp only [locFT, Pi.smul_apply, smul_eq_mul]
  rw [show (fun v : Fin m → Fin n → ℂ => Complex.exp (2 * Real.pi * Complex.I *
      ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * (a * g v)) = fun v => a * (Complex.exp
      (2 * Real.pi * Complex.I * ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * g v) from
    funext fun v => by ring, integral_const_mul]
  ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

namespace RD

variable {d : SD σ} (R : RD d) {w : InfinitePlace F}
  {L : GR d.n → ((Fin d.m → Fin d.n → ℂ) → ℂ) → (Fin d.m → Fin d.n → ℂ) → ℂ}

/- English proof (translation)
Take `⟨Ψ, hΨ⟩` from `hG F E σ d R w`. Establish `h0 : IsSw (0 : d.LF)` using `⟨0, by ext; simp⟩`. Take `⟨Φ, hΦ, hT'⟩` from `R.exists_adm hT hΨ h0`. Establish `hΦ0 : Φ = 0` using `d.T_inj hT Φ hΦ (by rw [hT']; funext X; simp [RD.tens])`. Establish `e` using `(hL y 0 h0).2 Ψ hΨ.1 Φ hΦ hT'`.

Rewrite `e` using `[hΦ0, map_zero, d.T_zero]`. Apply `R.tens_cancel hΨ.1 hΨ.2.1` to reduce the goal to its premises. Rewrite using `[← e]`. Use function extensionality and compare the values at `X`. Simplify using `[RD.tens]`.
-/
theorem locOp_zero (hT : TAll) (hG : GoodAwayEx) (hL : R.IsLocOp w L) (y : GR d.n) : L y 0 = 0 := by
  obtain ⟨Ψ, hΨ⟩ := hG F E σ d R w
  have h0 : IsSw (0 : d.LF) := ⟨0, by ext; simp⟩
  obtain ⟨Φ, hΦ, hT'⟩ := R.exists_adm hT hΨ h0
  have hΦ0 : Φ = 0 := d.T_inj hT Φ hΦ (by rw [hT']; funext X; simp [RD.tens])
  have e := (hL y 0 h0).2 Ψ hΨ.1 Φ hΦ hT'
  rw [hΦ0, map_zero, d.T_zero] at e
  apply R.tens_cancel hΨ.1 hΨ.2.1
  rw [← e]
  funext X
  simp [RD.tens]

/- English proof (translation)
Take `⟨-, ⟨ε, w₀, hw₀, -⟩, -⟩` from `hA F E σ d`. Take `⟨C, B, -, hW⟩` from `R.stepW_exp w hT hA ε w₀ hw₀`. Use `set s : ℂ := -2 * ((ε : ℤ) : ℂ) * ((R.sg w : ℤ) : ℂ) / R.ζ with hs_def`. Establish `hW' : R.StepOK w w₀ (locFT C s) B` using `hW`. Establish `hζn : ‖R.ζ‖ = 1`.

Apply the tactic sequence `rcases R.hζ with ⟨-, hz⟩ | ⟨-, hz⟩ <;> rw [hz] <;> simp`. Establish `hunit : ∀ u : ℤˣ, ‖((u : ℤ) : ℂ)‖ = 1` using `fun u => by`. Apply the tactic sequence `rcases Int.units_eq_one_or u with h | h <;> rw [h] <;> simp`. Establish `hsn : ‖s‖ = 2`. Rewrite using `[hs_def, norm_div, norm_mul, norm_mul, hunit, hunit, hζn]`.

Evaluate the numerical expressions. Establish `hs : s ≠ 0`. Introduce `h0`. Rewrite `hsn` using `[h0, norm_zero]`. Evaluate the numerical expressions using `at hsn`.

Establish `hη : ((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹ = -1`. Rewrite using `[R.isW_eps w hw₀]`. Break down `R.hζ with ⟨he, hz⟩ | ⟨he, hz⟩` into its components or cases. Rewrite using `[he, hz]`. Simplify using the standard rewrite rules.

Rewrite using `[he, hz]`. Simplify using `[Complex.inv_I]`. Establish `hsch` using `d.om_sch`. Establish `h4` using `R.step_comp w hsch (R.step_comp w hsch (R.step_comp w hsch hW' hW') hW') hW'`. Rewrite `h4` using `[RD.w_four hw₀]`.

Take `⟨Ψ, hΨ⟩` from `hG F E σ d R w`. Choose the witnesses or unpack the hypotheses as in `⟨X₀, hX₀⟩ : ∃ X₀, Ψ X₀ ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Conclude with `hΨ.2.1 (funext hc)`.

Establish `hB4 : d.IsAwayW w (B (B (B (B Ψ))))` using `(h4.2 Ψ hΨ.1).1`. Establish `key : ∀ f : d.LF, IsSw f → ∀ X, f (R.loc w X) * Ψ X = locFT C s (locFT C s (locFT C s (locFT C s f))) (R.loc w X) * B (B (B (B Ψ))) X`. Introduce `f hf X`. Take `⟨Φ, hΦ, hT'⟩` from `R.exists_adm hT hΨ hf`. Establish `e` using `(h4.2 Ψ hΨ.1).2 f hf Φ hΦ hT'`.

Rewrite `e` using `[map_one, Module.End.one_apply, hT']`. Conclude with `congrFun e X`. Establish `key0 : ∀ f : d.LF, IsSw f → ∀ u, f u * Ψ X₀ = locFT C s (locFT C s (locFT C s (locFT C s f))) u * B (B (B (B Ψ))) X₀`. Introduce `f hf u`. Take `⟨Z, hZ1, hZ2, hZ3⟩` from `R.loc_surj w X₀ u`.

Use `key f hf (X₀ + Z)` as an intermediate fact. Rewrite `this` using `[hZ3, hΨ.1 X₀ Z hZ1 hZ2, hB4 X₀ Z hZ1 hZ2]`. Then use the resulting hypothesis. Distinguish the cases in `hb : B (B (B (B Ψ))) X₀ = 0`. Establish `hz : ∀ f : d.LF, IsSw f → f = 0`. Introduce `f hf`.

Use function extensionality and compare the values at `u`. Use `key0 f hf u` as an intermediate fact. Rewrite `this` using `[hb, mul_zero]`. Conclude with `(mul_eq_zero.mp this).resolve_right hX₀`. Use `⟨C, s, 1, ε, hs, one_ne_zero, fun f hf => ?_, fun y c hc hy f hf => ?_, fun y c hc hy f hf => ?_, hsn, hη⟩` and prove the remaining obligations.

Rewrite using `[hz f hf]`. Simplify using `[locFT_zero]`. Rewrite using `[hz f hf, R.locOp_zero hT hG hL y]`. Simplify using `[locFT_zero, chirp_zero]`. Rewrite using `[hz f hf, R.locOp_zero hT hG hL y]`.

Simplify using `[locFT_zero, chirp_zero]`. Use `set κ := Ψ X₀ / B (B (B (B Ψ))) X₀ with hκ`. Establish `hκ0 : κ ≠ 0` using `div_ne_zero hX₀ hb`. Establish `h4f : ∀ f : d.LF, IsSw f → locFT C s (locFT C s (locFT C s (locFT C s f))) = κ • f`. Introduce `f hf`.

Use function extensionality and compare the values at `u`. Use `key0 f hf u` as an intermediate fact. Simplify using `only [Pi.smul_apply, smul_eq_mul, hκ]`. Clear the denominators using the available nonvanishing facts. Take the linear combination `-this`.

Establish `hmain : ∀ (y : GR d.n) (c : Matrix (Fin d.n) (Fin d.n) ℂ), cᴴ = c → mR y = nbLoc c → ∀ f, IsSw f → IsSw (chirp ((R.sg w : ℤ) : ℂ) ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c) (locFT C s f)) ∧ L y f = κ⁻¹ • locFT C s (locFT C s (locFT C s (chirp ((R.sg w : ℤ) : ℂ) ((((ε : ℤ) : ℂ) * R.ζ⁻¹ …`. Introduce `y c hc hy f hf`. Take `⟨y', hy', hrel⟩` from `R.oppositeUnipotent_weylConj w hw₀ y c hc hy`. Establish `hx : ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c)ᴴ = (((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c`. Establish `hs : star (((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) = ((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹`.

Break down `R.hζ with ⟨-, hz⟩ | ⟨-, hz⟩` into its components or cases. Rewrite using `[hz]`. Simplify using the standard rewrite rules. Rewrite using `[hz]`. Simplify using `[Complex.inv_I]`.

Rewrite using `[Matrix.conjTranspose_smul, hc, hs]`. Establish `hN : R.StepOK w (R.ι w y') (chirp ((R.sg w : ℤ) : ℂ) ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c)) id` using `R.stepN w hT y' _ hx hy'`. Use `⟨hN.1 _ (hW'.1 f hf), ?_⟩` and prove the remaining obligations. Distinguish the cases in `hf0 : ∀ u, f u = 0`. Establish `: f = 0` using `funext hf0`.

Rewrite using `[this, R.locOp_zero hT hG hL y]`. Simplify using `[locFT_zero, chirp_zero]`. Use `push Not at hf0`. Take `⟨u₀, hu₀⟩` from `hf0`. Establish `hBΨ : ∀ X, B (B (B (B Ψ))) X = κ⁻¹ * Ψ X`.

Introduce `X`. Take `⟨Z, hZ1, hZ2, hZ3⟩` from `R.loc_surj w X u₀`. Use `key f hf (X + Z)` as an intermediate fact. Rewrite `this` using `[hZ3, hΨ.1 X Z hZ1 hZ2, hB4 X Z hZ1 hZ2, h4f f hf]`. Simplify using `only [Pi.smul_apply, smul_eq_mul] at this`.

Rewrite using `[eq_inv_mul_iff_mul_eq₀ hκ0]`. Apply `mul_left_cancel₀ hu₀` to reduce the goal to its premises. Take the linear combination `-this`. Establish `hc3` using `R.step_comp w hsch (R.step_comp w hsch (R.step_comp w hsch (R.step_comp w hsch hW' hW') hW') hN) hW'`. Take `⟨Φ, hΦ, hT'⟩` from `R.exists_adm hT hΨ hf`.

Establish `e` using `(hc3.2 Ψ hΨ.1).2 f hf Φ hΦ hT'`. Establish `e1` using `(hL y f hf).2 Ψ hΨ.1 Φ hΦ hT'`. Rewrite `e1` using `[hrel]`. Apply `R.tens_cancel hΨ.1 hΨ.2.1` to reduce the goal to its premises. Rewrite using `[← e1, e]`.

Use function extensionality and compare the values at `X`. Simplify using `only [RD.tens, Function.comp_apply, id, Pi.smul_apply, smul_eq_mul, hBΨ]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨C, s, κ, ε, hs, hκ0, h4f, fun y c hc hy f hf => (hmain y c hc hy f hf).2, fun y c hc hy f hf => ?_, hsn, hη⟩` and prove the remaining obligations. Take `⟨hsw, heq⟩` from `hmain y c hc hy f hf`.

Rewrite using `[heq, locFT_smul, h4f _ hsw, smul_smul, inv_mul_cancel₀ hκ0, one_smul]`.
-/
theorem locOp_nbar (hT : TAll) (hA : AuxiliaryPrimeFunction) (hG : GoodAwayEx) (hL : R.IsLocOp w L) :
    ∃ (C s κ : ℂ) (ε : ℤˣ), s ≠ 0 ∧ κ ≠ 0 ∧
      (∀ f : d.LF, IsSw f → locFT C s (locFT C s (locFT C s (locFT C s f))) = κ • f) ∧
      (∀ (y : GR d.n) (c : Matrix (Fin d.n) (Fin d.n) ℂ), cᴴ = c → mR y = nbLoc c → ∀ f, IsSw f →
        L y f = κ⁻¹ • locFT C s (locFT C s (locFT C s
          (chirp ((R.sg w : ℤ) : ℂ) ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c) (locFT C s f))))) ∧
      (∀ (y : GR d.n) (c : Matrix (Fin d.n) (Fin d.n) ℂ), cᴴ = c → mR y = nbLoc c → ∀ f, IsSw f →
        locFT C s (L y f) = chirp ((R.sg w : ℤ) : ℂ) ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c) (locFT C s f)) ∧
      ‖s‖ = 2 ∧ ((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹ = -1 := by
  obtain ⟨-, ⟨ε, w₀, hw₀, -⟩, -⟩ := hA F E σ d
  obtain ⟨C, B, -, hW⟩ := R.stepW_exp w hT hA ε w₀ hw₀
  set s : ℂ := -2 * ((ε : ℤ) : ℂ) * ((R.sg w : ℤ) : ℂ) / R.ζ with hs_def
  have hW' : R.StepOK w w₀ (locFT C s) B := hW
  have hζn : ‖R.ζ‖ = 1 := by
    rcases R.hζ with ⟨-, hz⟩ | ⟨-, hz⟩ <;> rw [hz] <;> simp
  have hunit : ∀ u : ℤˣ, ‖((u : ℤ) : ℂ)‖ = 1 := fun u => by
    rcases Int.units_eq_one_or u with h | h <;> rw [h] <;> simp
  have hsn : ‖s‖ = 2 := by
    rw [hs_def, norm_div, norm_mul, norm_mul, hunit, hunit, hζn]
    norm_num
  have hs : s ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hsn
    norm_num at hsn
  have hη : ((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹ = -1 := by
    rw [R.isW_eps w hw₀]
    rcases R.hζ with ⟨he, hz⟩ | ⟨he, hz⟩
    · rw [he, hz]; simp
    · rw [he, hz]; simp [Complex.inv_I]
  have hsch := d.om_sch
  have h4 := R.step_comp w hsch (R.step_comp w hsch (R.step_comp w hsch hW' hW') hW') hW'
  rw [RD.w_four hw₀] at h4
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
    refine ⟨C, s, 1, ε, hs, one_ne_zero, fun f hf => ?_, fun y c hc hy f hf => ?_, fun y c hc hy f hf => ?_, hsn, hη⟩
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
      simp only [RD.tens, Function.comp_apply, id, Pi.smul_apply, smul_eq_mul, hBΨ]
      ring
    refine ⟨C, s, κ, ε, hs, hκ0, h4f, fun y c hc hy f hf => (hmain y c hc hy f hf).2,
      fun y c hc hy f hf => ?_, hsn, hη⟩
    obtain ⟨hsw, heq⟩ := hmain y c hc hy f hf
    rw [heq, locFT_smul, h4f _ hsw, smul_smul, inv_mul_cancel₀ hκ0, one_smul]

end RD

end PositivityTheory.SiegelWeilFormula

end
