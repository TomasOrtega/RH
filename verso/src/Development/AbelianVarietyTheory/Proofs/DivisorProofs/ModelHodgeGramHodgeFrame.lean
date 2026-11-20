import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeFrameGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelHodgeGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelHodgeGramPosDefQuotientStatement
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
open Matrix
open scoped ComplexOrder
open GlobalTheory.HodgeLocGeo

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HodgeLocGeo

open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram
open scoped ContDiff

/- English proof (translation)
Use `set e := Fintype.equivFin ι`. Set `P : (Fin (Fintype.card ι) → ℂ) →L[ℂ] (ι → ℂ)` to `ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (e i)`. Set `Q : (ι → ℂ) →L[ℂ] (Fin (Fintype.card ι) → ℂ)` to `ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (e.symm j)`. Establish `hPQ : ∀ y, P (Q y) = y` using `fun y => by ext i; simp [P, Q]`. Establish `hU' : IsOpen (P ⁻¹' U)` using `hU.preimage P.continuous`.

Establish `hg : DifferentiableOn ℂ (f ∘ P) (P ⁻¹' U)` using `hf.comp P.differentiableOn (fun y hy => hy)`. Establish `ha` using `ReciprocityTheory.AnForm.Osgood.osgood _ _ _ hU' hg (Q x) (by simpa [Set.mem_preimage, hPQ] using hx)`. Establish `h2 : AnalyticAt ℂ ((f ∘ P) ∘ Q) x` using `ha.comp (Q.analyticAt x)`. Establish `heq : (f ∘ P) ∘ Q = f` using `funext fun y => by simp [hPQ]`. Rewrite `h2` using `[heq]`.

Conclude with `h2.contDiffAt`.
-/
theorem contDiffAt_of_differentiableOn_pi {ι : Type} [Fintype ι] {U : Set (ι → ℂ)} (hU : IsOpen U)
    {f : (ι → ℂ) → ℂ} (hf : DifferentiableOn ℂ f U) {x : ι → ℂ} (hx : x ∈ U) : ContDiffAt ℂ ∞ f x := by
  classical
  set e := Fintype.equivFin ι
  let P : (Fin (Fintype.card ι) → ℂ) →L[ℂ] (ι → ℂ) :=
    ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (e i)
  let Q : (ι → ℂ) →L[ℂ] (Fin (Fintype.card ι) → ℂ) :=
    ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (e.symm j)
  have hPQ : ∀ y, P (Q y) = y := fun y => by ext i; simp [P, Q]
  have hU' : IsOpen (P ⁻¹' U) := hU.preimage P.continuous
  have hg : DifferentiableOn ℂ (f ∘ P) (P ⁻¹' U) := hf.comp P.differentiableOn (fun y hy => hy)
  have ha := ReciprocityTheory.AnForm.Osgood.osgood _ _ _ hU' hg (Q x) (by simpa [Set.mem_preimage, hPQ] using hx)
  have h2 : AnalyticAt ℂ ((f ∘ P) ∘ Q) x := ha.comp (Q.analyticAt x)
  have heq : (f ∘ P) ∘ Q = f := funext fun y => by simp [hPQ]
  rw [heq] at h2
  exact h2.contDiffAt

/- English proof (translation)
Use `set A : (ι → ℂ) → Matrix (Fin q ⊕ Fin p) (Fin q ⊕ Fin p) ℂ := fun x => modelFrame (Z x) with hAdef`. Establish `hZd : ∀ x ∈ U, ∀ a b, DifferentiableAt ℂ (fun y => Z y a b) x` using `fun x hx a b => (hZ a b).differentiableAt (hU.mem_nhds hx)`. Establish `hA : ∀ x ∈ U, MContDiffAt ∞ A x` using `fun x hx a b => by`. Establish `hz : ∀ c d, ContDiffAt ℝ ∞ (fun y => Z y c d) x` using `fun c d => by`. Establish `h2 : ContDiffAt ℂ ∞ (fun y => Z y c d) x` using `contDiffAt_of_differentiableOn_pi hU (hZ c d) hx`.

Conclude with `h2.restrict_scalars ℝ`. Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b`. Simplify using `only [hAdef, modelFrame, fromBlocks_apply₁₁]`. Conclude with `contDiffAt_const`. Simplify using `only [hAdef, modelFrame, fromBlocks_apply₁₂]`.

Conclude with `contDiffAt_const`. Simplify using `only [hAdef, modelFrame, fromBlocks_apply₂₁]`. Conclude with `hz a b`. Simplify using `only [hAdef, modelFrame, fromBlocks_apply₂₂]`. Conclude with `contDiffAt_const`.

Establish `hAu : ∀ x, IsUnit (A x).det` using `fun x => by`. Simplify using `[hAdef, modelFrame, det_fromBlocks_zero₁₂]`. Establish `hJ : IsUnit (fromBlocks (-1) 0 0 1 : Matrix (Fin q ⊕ Fin p) (Fin q ⊕ Fin p) ℂ).det`. Simplify using `[det_fromBlocks_zero₁₂, det_neg]`. Establish `hA0 : ∀ x ∈ U, ∀ η, mdbar A x η = 0` using `fun x hx η => by`.

Use extensionality with `(a | a) (b | b)`. Simplify using `[hAdef, modelFrame]`. Simplify using `[hAdef, modelFrame]`. Express the relevant statement in the definitionally equal form `dbar (fun y => Z y a b) x η = 0`. Rewrite using `[dbar_eq_zero (hZd x hx a b)]`.

Both sides reduce to the same expression. Simplify using `[hAdef, modelFrame]`. Establish `hblk` using `fun x hx => GlobalTheory.T.model_hodge_gram_pos_def_quotient (Z x) (hpos x hx)`. Use `⟨.of_mContDiffAt hU (fun x hx => ((hA x hx).transpose.mul (mContDiffAt_const _)).mul (hA x hx).conjTranspose.transpose) (fun x _ => ?_) (fun x _ => ?_), fun x hx v w => ?_, fun x hx => ?_, fun x hx => ?_⟩` and prove the remaining obligations. Establish `e1 : ∀ M : Matrix (Fin q ⊕ Fin p) (Fin q ⊕ Fin p) ℂ, Mᴴᵀᴴ = Mᵀ` using `fun M => by ext; simp`.

Establish `e2 : ∀ M : Matrix (Fin q ⊕ Fin p) (Fin q ⊕ Fin p) ℂ, Mᵀᴴ = Mᴴᵀ` using `fun M => by ext; simp`. Simplify using `[IsHermitian, modelHodgeGram, conjTranspose_mul, Matrix.mul_assoc, fromBlocks_conjTranspose, e1, e2]`. Simplify using `only [modelHodgeGram, det_mul, det_transpose, det_conjTranspose]`. Conclude with `((hAu x).mul hJ).mul (hAu x).star`. Use `curv_changeFrame (H := fun _ => fromBlocks (-1) 0 0 1) (mContDiffAt_const _) hJ ((hA x hx).of_le (by norm_cast)) (hAu x) (Filter.eventually_of_mem (hU.mem_nhds hx) hA0) v w` as an intermediate fact.

Conclude with `this.trans (by simp)`. Rewrite using `[(hblk x hx).2.2.2]`. Conclude with `(hblk x hx).2.1`. Rewrite using `[(hblk x hx).2.2.1]`. Conclude with `(hblk x hx).1.inv`.
-/
theorem isHodgeFrame_model {ι : Type} [Fintype ι] {p q : ℕ} (U : Set (ι → ℂ))
    (Z : (ι → ℂ) → Matrix (Fin p) (Fin q) ℂ) (hU : IsOpen U)
    (hZ : ∀ a b, DifferentiableOn ℂ (fun x => Z x a b) U)
    (hpos : ∀ x ∈ U, (1 - (Z x)ᴴ * Z x).PosDef) :
    IsHodgeFrame U (fun x => modelHodgeGram (Z x)) := by
  set A : (ι → ℂ) → Matrix (Fin q ⊕ Fin p) (Fin q ⊕ Fin p) ℂ := fun x => modelFrame (Z x) with hAdef
  have hZd : ∀ x ∈ U, ∀ a b, DifferentiableAt ℂ (fun y => Z y a b) x := fun x hx a b =>
    (hZ a b).differentiableAt (hU.mem_nhds hx)
  have hA : ∀ x ∈ U, MContDiffAt ∞ A x := fun x hx a b => by
    have hz : ∀ c d, ContDiffAt ℝ ∞ (fun y => Z y c d) x := fun c d => by
      have h2 : ContDiffAt ℂ ∞ (fun y => Z y c d) x := contDiffAt_of_differentiableOn_pi hU (hZ c d) hx
      exact h2.restrict_scalars ℝ
    rcases a with a | a <;> rcases b with b | b
    · simp only [hAdef, modelFrame, fromBlocks_apply₁₁]; exact contDiffAt_const
    · simp only [hAdef, modelFrame, fromBlocks_apply₁₂]; exact contDiffAt_const
    · simp only [hAdef, modelFrame, fromBlocks_apply₂₁]; exact hz a b
    · simp only [hAdef, modelFrame, fromBlocks_apply₂₂]; exact contDiffAt_const
  have hAu : ∀ x, IsUnit (A x).det := fun x => by
    simp [hAdef, modelFrame, det_fromBlocks_zero₁₂]
  have hJ : IsUnit (fromBlocks (-1) 0 0 1 : Matrix (Fin q ⊕ Fin p) (Fin q ⊕ Fin p) ℂ).det := by
    simp [det_fromBlocks_zero₁₂, det_neg]
  have hA0 : ∀ x ∈ U, ∀ η, mdbar A x η = 0 := fun x hx η => by
    ext (a | a) (b | b)
    · simp [hAdef, modelFrame]
    · simp [hAdef, modelFrame]
    · change dbar (fun y => Z y a b) x η = 0
      rw [dbar_eq_zero (hZd x hx a b)]; rfl
    · simp [hAdef, modelFrame]
  have hblk := fun x hx => GlobalTheory.T.model_hodge_gram_pos_def_quotient (Z x) (hpos x hx)
  refine ⟨.of_mContDiffAt hU
    (fun x hx => ((hA x hx).transpose.mul (mContDiffAt_const _)).mul (hA x hx).conjTranspose.transpose)
    (fun x _ => ?_) (fun x _ => ?_), fun x hx v w => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · have e1 : ∀ M : Matrix (Fin q ⊕ Fin p) (Fin q ⊕ Fin p) ℂ, Mᴴᵀᴴ = Mᵀ := fun M => by ext; simp
    have e2 : ∀ M : Matrix (Fin q ⊕ Fin p) (Fin q ⊕ Fin p) ℂ, Mᵀᴴ = Mᴴᵀ := fun M => by ext; simp
    simp [IsHermitian, modelHodgeGram, conjTranspose_mul, Matrix.mul_assoc, fromBlocks_conjTranspose, e1, e2]
  · simp only [modelHodgeGram, det_mul, det_transpose, det_conjTranspose]
    exact ((hAu x).mul hJ).mul (hAu x).star
  · have := curv_changeFrame (H := fun _ => fromBlocks (-1) 0 0 1) (mContDiffAt_const _) hJ
      ((hA x hx).of_le (by norm_cast)) (hAu x)
      (Filter.eventually_of_mem (hU.mem_nhds hx) hA0) v w
    exact this.trans (by simp)
  · rw [(hblk x hx).2.2.2]; exact (hblk x hx).2.1
  · rw [(hblk x hx).2.2.1]; exact (hblk x hx).1.inv

end GlobalTheory.HodgeLocGeo
