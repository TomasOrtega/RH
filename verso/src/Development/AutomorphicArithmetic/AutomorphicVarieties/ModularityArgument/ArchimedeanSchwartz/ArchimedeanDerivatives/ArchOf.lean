import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.HodgeTateFromSandwich
import GroundTheory.AutomorphicForms.GL2.GJStandardLBump

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.GJStandardL GroundTheory.Automorphic.GodementJacquet
open GroundTheory.Automorphic.GLnLocal
open scoped SchwartzMap Classical

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

/- English proof (translation)
Introduce `hS hF hT hB K _ _ _ n hn ψ m hm fi hfi hne μ _`. Take `⟨hsurj, hpe, habs, e, c, c', he, hc, hc', hΦ⟩` from `hB K n μ`. Take `⟨k, hk, hS⟩` from `hS K n`. Take `⟨κ, hκ, hF⟩` from `hF K n e he`. Establish `hcont : ContinuousOn (chart ψ.1 1) (invSet K n)` using `fun x hx => (contDiffAt_chart ψ.2 1 hx).continuousAt.continuousWithinAt`.

Establish `hval : ∀ y, fi (archComp K n (infGL K n y)) = chart ψ.1 1 (toL y.val)`. Introduce `y`. Rewrite using `[hfi, hpe, chart_val, one_mul]`. Establish `hne' : ∃ x ∈ invSet K n, chart ψ.1 1 x ≠ 0`. Take `⟨x, hx⟩` from `hne`.

Take `⟨y, rfl⟩` from `hsurj x`. Conclude with `⟨_, val_mem_invSet y, by rwa [← hval]⟩`. Take `⟨Φ, hΦt, hdiff, s₀, hs₀⟩` from `hT K n _ hcont hne'`. Take `⟨hDt, hsh⟩` from `hS ψ m hm Φ hΦt`. Take `⟨φ, hφ, hφF⟩` from `hΦ Φ hΦt`.

Take `⟨φ', hφ', hφF'⟩` from `hΦ _ hDt`. Use `⟨φ, φ', k, κ, hk, hκ, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `h : archZeta μ φ fi = fun s => c * (fun s : ℂ => ∫ x, Φ x * chart ψ.1 1 x * ((UpperTheory.V.Z.Inf.nrm x : ℝ) : ℂ) ^ s) (s + ((n : ℂ) - 1) / 2 - n)` using `funext fun s => hφ fi _ hcont hval s`. Rewrite using `[h]`. Conclude with `(hdiff.comp ((differentiable_id.add_const _).sub_const _)).const_mul c`.

Introduce `h0`. Establish `h` using `hφ fi _ hcont hval (s₀ + n - ((n : ℂ) - 1) / 2)`. Rewrite `h` using `[h0, show s₀ + n - ((n : ℂ) - 1) / 2 + ((n : ℂ) - 1) / 2 - n = s₀ by ring]`. Conclude with `mul_ne_zero hc hs₀ h.symm`. Introduce `s`.

Rewrite using `[hφ' fi _ hcont hval, hφ fi _ hcont hval, hsh 1 s]`. Expand and normalize the polynomial expressions, which then agree. Introduce `g s`. Unfold `archZeta`. Rewrite using `[← integral_const_mul]`.

Use `integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Take `⟨y, rfl⟩` from `hsurj x`. Establish `hp : ((archAbsDet (archComp K n (infGL K n y)) : ℝ) : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.2 (archAbsDet_pos _).ne'`. Simplify using `only [archIntegrand, archDetPow]`. Rewrite using `[hφF, hφF', hF Φ hΦt, show s + 1 + ((n : ℂ) - 1) / 2 = (s + ((n : ℂ) - 1) / 2) + 1 by ring, Complex.cpow_add _ 1 hp, Complex.cpow_one, habs]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.V.Z.Inf.archOf :
    UpperTheory.V.Z.Inf.ArchOf := by
  intro hS hF hT hB K _ _ _ n hn ψ m hm fi hfi hne μ _
  obtain ⟨hsurj, hpe, habs, e, c, c', he, hc, hc', hΦ⟩ := hB K n μ
  obtain ⟨k, hk, hS⟩ := hS K n
  obtain ⟨κ, hκ, hF⟩ := hF K n e he
  have hcont : ContinuousOn (chart ψ.1 1) (invSet K n) := fun x hx =>
    (contDiffAt_chart ψ.2 1 hx).continuousAt.continuousWithinAt
  have hval : ∀ y, fi (archComp K n (infGL K n y)) = chart ψ.1 1 (toL y.val) := by
    intro y
    rw [hfi, hpe, chart_val, one_mul]
  have hne' : ∃ x ∈ invSet K n, chart ψ.1 1 x ≠ 0 := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨y, rfl⟩ := hsurj x
    exact ⟨_, val_mem_invSet y, by rwa [← hval]⟩
  obtain ⟨Φ, hΦt, hdiff, s₀, hs₀⟩ := hT K n _ hcont hne'
  obtain ⟨hDt, hsh⟩ := hS ψ m hm Φ hΦt
  obtain ⟨φ, hφ, hφF⟩ := hΦ Φ hΦt
  obtain ⟨φ', hφ', hφF'⟩ := hΦ _ hDt
  refine ⟨φ, φ', k, κ, hk, hκ, ?_, ?_, ?_, ?_⟩
  · have h : archZeta μ φ fi = fun s => c * (fun s : ℂ => ∫ x, Φ x * chart ψ.1 1 x * ((UpperTheory.V.Z.Inf.nrm x : ℝ) : ℂ) ^ s)
        (s + ((n : ℂ) - 1) / 2 - n) := funext fun s => hφ fi _ hcont hval s
    rw [h]
    exact (hdiff.comp ((differentiable_id.add_const _).sub_const _)).const_mul c
  · intro h0
    have h := hφ fi _ hcont hval (s₀ + n - ((n : ℂ) - 1) / 2)
    rw [h0, show s₀ + n - ((n : ℂ) - 1) / 2 + ((n : ℂ) - 1) / 2 - n = s₀ by ring] at h
    exact mul_ne_zero hc hs₀ h.symm
  · intro s
    rw [hφ' fi _ hcont hval, hφ fi _ hcont hval, hsh 1 s]
    ring
  · intro g s
    unfold archZeta
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    obtain ⟨y, rfl⟩ := hsurj x
    have hp : ((archAbsDet (archComp K n (infGL K n y)) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (archAbsDet_pos _).ne'
    simp only [archIntegrand, archDetPow]
    rw [hφF, hφF', hF Φ hΦt, show s + 1 + ((n : ℂ) - 1) / 2 = (s + ((n : ℂ) - 1) / 2) + 1 by ring,
      Complex.cpow_add _ 1 hp, Complex.cpow_one, habs]
    ring
