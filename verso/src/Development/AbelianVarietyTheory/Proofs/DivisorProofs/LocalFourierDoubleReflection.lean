import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualFor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsSelfDualOfHasConductor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.WeylFour.LocInv

variable {F : Type} [Field F] [NumberField F]

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

local instance borelFvLoc (v : Pl F) : BorelSpace (Fv F v) := ⟨rfl⟩

open GlobalTheory.SplitWeil

/- English proof (translation)
Establish `hb : ∀ y : Fv F v, ‖χ y‖ ≤ 1`. Introduce `y`. Choose the witnesses or unpack the hypotheses as in `⟨s, hs⟩ : ∃ s : (Fv F v)ˣ, y ∈ cball s := by`. Distinguish the cases in `hy : y = 0`. Conclude with `⟨1, by simp [hy, cball]⟩`.

Conclude with `⟨Units.mk0 y hy, by simp [cball]⟩`. Take `⟨M, hM⟩` from `(isCompact_cball s).exists_bound_of_continuousOn hχ.continuousOn`. Establish `hn : ∀ n : ℕ, ‖χ y‖ ^ n ≤ M`. Introduce `n`. Establish `hmem : n • y ∈ cball s`.

Proceed by induction on `n with`. Consider the case `zero => simp [cball]`. Consider the case `succ n ih => rw [succ_nsmul]`. Conclude with `add_mem_cball ih hs`. Rewrite using `[← norm_pow, ← AddChar.map_nsmul_eq_pow]`.

Conclude with `hM _ hmem`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Take `⟨n, hn'⟩` from `pow_unbounded_of_one_lt M h`. Conclude with `absurd (hn n) (not_le.mpr hn')`.

Establish `h1` using `hb x`. Establish `h2` using `hb (-x)`. Establish `h3 : χ x * χ (-x) = 1`. Rewrite using `[← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]`. Establish `h4 : ‖χ x‖ * ‖χ (-x)‖ = 1` using `by rw [← norm_mul, h3, norm_one]`.

Use `le_antisymm h1 ?_` and prove the remaining obligations. Use polynomial arithmetic with `[norm_nonneg (χ x), norm_nonneg (χ (-x))]`.
-/
theorem norm_addChar_eq_one {v : Pl F} (χ : AddChar (Fv F v) ℂ) (hχ : Continuous χ) (x : Fv F v) :
    ‖χ x‖ = 1 := by
  have hb : ∀ y : Fv F v, ‖χ y‖ ≤ 1 := by
    intro y
    obtain ⟨s, hs⟩ : ∃ s : (Fv F v)ˣ, y ∈ cball s := by
      by_cases hy : y = 0
      · exact ⟨1, by simp [hy, cball]⟩
      · exact ⟨Units.mk0 y hy, by simp [cball]⟩
    obtain ⟨M, hM⟩ := (isCompact_cball s).exists_bound_of_continuousOn hχ.continuousOn
    have hn : ∀ n : ℕ, ‖χ y‖ ^ n ≤ M := by
      intro n
      have hmem : n • y ∈ cball s := by
        induction n with
        | zero => simp [cball]
        | succ n ih => rw [succ_nsmul]; exact add_mem_cball ih hs
      rw [← norm_pow, ← AddChar.map_nsmul_eq_pow]
      exact hM _ hmem
    by_contra h
    push_neg at h
    obtain ⟨n, hn'⟩ := pow_unbounded_of_one_lt M h
    exact absurd (hn n) (not_le.mpr hn')
  have h1 := hb x
  have h2 := hb (-x)
  have h3 : χ x * χ (-x) = 1 := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have h4 : ‖χ x‖ * ‖χ (-x)‖ = 1 := by rw [← norm_mul, h3, norm_one]
  refine le_antisymm h1 ?_
  nlinarith [norm_nonneg (χ x), norm_nonneg (χ (-x))]

def toCirc {v : Pl F} (χ : AddChar (Fv F v) ℂ) (h : ∀ x, ‖χ x‖ = 1) : AddChar (Fv F v) Circle where
  toFun x := ⟨χ x, by simpa [Submonoid.unitSphere, mem_sphere_zero_iff_norm] using h x⟩
  map_zero_eq_one' := by
    apply Circle.ext
    simp
  map_add_eq_mul' a b := by
    apply Circle.ext
    exact χ.map_add_eq_mul a b

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_toCirc {v : Pl F} (χ : AddChar (Fv F v) ℂ) (h : ∀ x, ‖χ x‖ = 1) (x : Fv F v) :
    ((toCirc χ h x : Circle) : ℂ) = χ x := rfl

/- English proof (translation)
Establish `hj : Continuous (GlobalTheory.LatVac.liftV (F` using `F) v) := by`. Express the relevant statement in the definitionally equal form `Continuous fun a => ((0 : Ainf F), GlobalTheory.AdelicU.singleFin v a)`. Conclude with `continuous_const.prodMk (GlobalTheory.AdelicU.continuous_singleFin v)`. Conclude with `hψ.comp hj`.
-/
theorem continuous_psiAt' (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) (v : Pl F) :
    Continuous (GlobalTheory.LatVac.psiAt ψ v) := by
  have hj : Continuous (GlobalTheory.LatVac.liftV (F := F) v) := by
    change Continuous fun a => ((0 : Ainf F), GlobalTheory.AdelicU.singleFin v a)
    exact continuous_const.prodMk (GlobalTheory.AdelicU.continuous_singleFin v)
  exact hψ.comp hj

/- English proof (translation)
Establish `hc` using `continuous_psiAt' ψ hψ.1 v`. Establish `hn : ∀ x, ‖GlobalTheory.LatVac.psiAt ψ v x‖ = 1` using `norm_addChar_eq_one _ hc`. Establish `hcc : Continuous (toCirc _ hn)` using `Continuous.subtype_mk hc _`. Establish `hne1 : toCirc _ hn ≠ 1`. Take `⟨x, hx⟩` from `hne`.

Introduce `h1`. Apply `hx` to reduce the goal to its premises. Use `congrArg (fun χ : AddChar (Fv F v) Circle => ((χ x : Circle) : ℂ)) h1` as an intermediate fact. Simplify `this` using `[coe_toCirc, GlobalTheory.LatVac.psiAt_apply]`. Take `⟨c, hcond⟩` from `exists_hasConductor_of_continuous _ hcc hne1`.

Take `⟨ν, hν⟩` from `exists_isSelfDual_of_hasConductor hcond`. Establish `hex : ∃ ν, IsSelfDualFor (GlobalTheory.LatVac.psiAt ψ v) ν` using `⟨ν, hν.1, fun f hf => hν.2 f hf⟩`. Use `⟨hn, c, hcond, ?_⟩` and prove the remaining obligations. Establish `hm : measV ψ v = hex.choose`. Unfold `measV`.

Rewrite using `[dif_pos hex]`. Rewrite using `[hm]`. Conclude with `⟨hex.choose_spec.1, fun f hf => hex.choose_spec.2 f hf⟩`.
-/
theorem measV_selfDual (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (v : Pl F) (hne : ∃ x, psiLoc ψ v x ≠ 1) :
    ∃ (h : ∀ x, ‖GlobalTheory.LatVac.psiAt ψ v x‖ = 1) (c : (Fv F v)ˣ),
      HasConductor (toCirc _ h) c ∧ IsSelfDual (toCirc _ h) (measV ψ v) := by
  have hc := continuous_psiAt' ψ hψ.1 v
  have hn : ∀ x, ‖GlobalTheory.LatVac.psiAt ψ v x‖ = 1 := norm_addChar_eq_one _ hc
  have hcc : Continuous (toCirc _ hn) := Continuous.subtype_mk hc _
  have hne1 : toCirc _ hn ≠ 1 := by
    obtain ⟨x, hx⟩ := hne
    intro h1
    apply hx
    have := congrArg (fun χ : AddChar (Fv F v) Circle => ((χ x : Circle) : ℂ)) h1
    simpa [coe_toCirc, GlobalTheory.LatVac.psiAt_apply] using this
  obtain ⟨c, hcond⟩ := exists_hasConductor_of_continuous _ hcc hne1
  obtain ⟨ν, hν⟩ := exists_isSelfDual_of_hasConductor hcond
  have hex : ∃ ν, IsSelfDualFor (GlobalTheory.LatVac.psiAt ψ v) ν := ⟨ν, hν.1, fun f hf => hν.2 f hf⟩
  refine ⟨hn, c, hcond, ?_⟩
  have hm : measV ψ v = hex.choose := by
    unfold measV
    rw [dif_pos hex]
  rw [hm]
  exact ⟨hex.choose_spec.1, fun f hf => hex.choose_spec.2 f hf⟩

end GlobalTheory.WeylFour.LocInv

namespace GlobalTheory.WeylFour.LocInv

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Introduce `F _ _ ψ hψ v hne κ _ φ hφ`. Use `haveI : BorelSpace (Fv F v) := ⟨rfl⟩`. Take `⟨hn, c, hcond, hself⟩` from `measV_selfDual ψ hψ v hne`. Use `haveI := hself.1`. Use `haveI := GlobalTheory.SplitWeil.secondCountable (Fv F v)`.

Use `haveI := GlobalTheory.SplitWeil.t2Space (Fv F v)`. Use function extensionality and compare the values at `z`. Establish `hinner : ∀ y, fourV ψ v φ y * GlobalTheory.LatVac.psiAt ψ v (y ⬝ᵥ z) = ∫ x, φ (x - z) * ((toCirc _ hn (x ⬝ᵥ y) : Circle) : ℂ) ∂(Measure.pi fun _ : κ => measV ψ v)`. Introduce `y`. Unfold `fourV`.

Rewrite using `[← integral_mul_const]`. Establish `h1 : ∀ x : κ → Fv F v, φ x * GlobalTheory.LatVac.psiAt ψ v (x ⬝ᵥ y) * GlobalTheory.LatVac.psiAt ψ v (y ⬝ᵥ z) = φ x * GlobalTheory.LatVac.psiAt ψ v ((x + z) ⬝ᵥ y)`. Introduce `x`. Rewrite using `[add_dotProduct, AddChar.map_add_eq_mul, dotProduct_comm z y, mul_assoc]`. Simplify using `only [h1]`.

Rewrite using `[← integral_sub_right_eq_self (μ := Measure.pi fun _ : κ => measV ψ v) (fun x => φ x * GlobalTheory.LatVac.psiAt ψ v ((x + z) ⬝ᵥ y)) z]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Simplify using `only [sub_add_cancel, coe_toCirc]`. Establish `hg : (fun x : κ → Fv F v => φ (x - z)) ∈ GlobalTheory.SplitWeil.SB (κ → Fv F v)` using `⟨hφ.1.comp_continuous (continuous_id.sub continuous_const), hφ.2.comp_homeomorph (Homeomorph.subRight z)⟩`. Establish `h2` using `(GlobalTheory.SplitWeil.FourierPi.fourier_pi_of_conductor hcond hself hg).2`.

Use `show ∫ y, fourV ψ v φ y * GlobalTheory.LatVac.psiAt ψ v (y ⬝ᵥ z) ∂(Measure.pi fun _ : κ => measV ψ v) = φ (-z)`. Simplify using `only [hinner]`. Rewrite using `[h2, zero_sub]`.
-/
theorem fourV_fourV : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ v : Pl F,
    (∃ x, psiLoc ψ v x ≠ 1) →
    ∀ (κ : Type) [Fintype κ], ∀ φ ∈ SB (κ → Fv F v), fourV ψ v (fourV ψ v φ) = fun x => φ (-x) := by
  intro F _ _ ψ hψ v hne κ _ φ hφ
  classical
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨hn, c, hcond, hself⟩ := measV_selfDual ψ hψ v hne
  haveI := hself.1
  haveI := GlobalTheory.SplitWeil.secondCountable (Fv F v)
  haveI := GlobalTheory.SplitWeil.t2Space (Fv F v)
  funext z
  have hinner : ∀ y, fourV ψ v φ y * GlobalTheory.LatVac.psiAt ψ v (y ⬝ᵥ z) =
      ∫ x, φ (x - z) * ((toCirc _ hn (x ⬝ᵥ y) : Circle) : ℂ) ∂(Measure.pi fun _ : κ => measV ψ v) := by
    intro y
    unfold fourV
    rw [← integral_mul_const]
    have h1 : ∀ x : κ → Fv F v, φ x * GlobalTheory.LatVac.psiAt ψ v (x ⬝ᵥ y) * GlobalTheory.LatVac.psiAt ψ v (y ⬝ᵥ z) =
        φ x * GlobalTheory.LatVac.psiAt ψ v ((x + z) ⬝ᵥ y) := by
      intro x
      rw [add_dotProduct, AddChar.map_add_eq_mul, dotProduct_comm z y, mul_assoc]
    simp only [h1]
    rw [← integral_sub_right_eq_self (μ := Measure.pi fun _ : κ => measV ψ v)
      (fun x => φ x * GlobalTheory.LatVac.psiAt ψ v ((x + z) ⬝ᵥ y)) z]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [sub_add_cancel, coe_toCirc]
  have hg : (fun x : κ → Fv F v => φ (x - z)) ∈ GlobalTheory.SplitWeil.SB (κ → Fv F v) :=
    ⟨hφ.1.comp_continuous (continuous_id.sub continuous_const),
      hφ.2.comp_homeomorph (Homeomorph.subRight z)⟩
  have h2 := (GlobalTheory.SplitWeil.FourierPi.fourier_pi_of_conductor hcond hself hg).2
  show ∫ y, fourV ψ v φ y * GlobalTheory.LatVac.psiAt ψ v (y ⬝ᵥ z) ∂(Measure.pi fun _ : κ => measV ψ v) = φ (-z)
  simp only [hinner]
  rw [h2, zero_sub]

end GlobalTheory.WeylFour.LocInv
