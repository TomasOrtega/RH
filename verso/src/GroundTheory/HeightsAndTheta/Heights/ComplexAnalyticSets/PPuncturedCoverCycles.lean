import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPuncturedCoverCycles
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFibreSectionsCovering
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteCoverPuncturedPolydisc
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Filter Topology Matrix

noncomputable section

/- English proof (translation)
Rewrite using `[differentiable_pi]`. Introduce `i`. Distinguish the cases in `hi : i = 0`. Substitute `hi` using the available equality. Simplify using `only [Function.update_self]`.

Use `fun_prop`. Simplify using `only [Function.update_of_ne hi] fun_prop`.
-/
private theorem differentiable_update_pow (e k : ℕ) :
    Differentiable ℂ (fun s : Fin (e + 1) → ℂ => Function.update s 0 (s 0 ^ k)) := by
  rw [differentiable_pi]
  intro i
  by_cases hi : i = 0
  · subst hi
    simp only [Function.update_self]
    fun_prop
  · simp only [Function.update_of_ne hi]
    fun_prop

/- English proof (translation)
Introduce `n e N A c r X hr hc0 hXP hfib hsec`. Establish `hX : Set.MapsTo (fun x => A *ᵥ x) X (Metric.ball c r ∩ {t | t 0 ≠ 0})` using `fun x hx => hXP x hx`. Establish `hcov` using `hCov n e N A _ X hX (fun y hy => hfib y hy.1 hy.2) hsec`. Establish `hfib' : ∀ z, (hX.restrict ⁻¹' {z}).encard = N`. Introduce `z`.

Establish `himg : Subtype.val '' (hX.restrict ⁻¹' {z}) = {x | x ∈ X ∧ A *ᵥ x = z}`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x', hx', rfl⟩`. Conclude with `⟨x'.2, congrArg Subtype.val hx'⟩`.

Introduce and unpack `⟨hx, hxz⟩`. Conclude with `⟨⟨x, hx⟩, Subtype.ext hxz, rfl⟩`. Rewrite using `[← Subtype.val_injective.encard_image, himg]`. Conclude with `hfib z z.2.1 z.2.2`. Take `⟨m, ord, δ, ψ, hδ0, hδ1, hsum, hord, hcont, hA, hinj, hdisj, hcover⟩` from `hCyc e N c r X hX.restrict hr hc0 hcov hfib'`.

Set `Ψ : Fin m → (Fin (e + 1) → ℂ) → Fin n → ℂ` to `fun b t => if h : t ∈ Metric.ball c δ ∩ {t | t 0 ≠ 0} then (ψ b ⟨t, h⟩ : Fin n → ℂ) else 0`. Establish `hΨ : ∀ b t (h : t ∈ Metric.ball c δ ∩ {t | t 0 ≠ 0}), Ψ b t = ψ b ⟨t, h⟩` using `fun b t h => dif_pos h`. Establish `hAΨ : ∀ b t (h : t ∈ Metric.ball c δ ∩ {t | t 0 ≠ 0}), A *ᵥ Ψ b t = Function.update t 0 (t 0 ^ ord b)`. Introduce `b t h`. Rewrite using `[hΨ b t h]`.

Conclude with `hA b ⟨t, h⟩`. Establish `hopen : IsOpen (Metric.ball c δ ∩ {t : Fin (e + 1) → ℂ | t 0 ≠ 0})` using `Metric.isOpen_ball.inter (isOpen_ne_fun (continuous_apply 0) continuous_const)`. Use `⟨m, ord, Ψ, δ, hδ0, hδ1, hsum, hord, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `b t ht`. Establish `hcontΨ : ContinuousOn (Ψ b) (Metric.ball c δ ∩ {t | t 0 ≠ 0})`.

Rewrite using `[continuousOn_iff_continuous_domRestrict]`. Establish `: (Metric.ball c δ ∩ {t | t 0 ≠ 0}).domRestrict (Ψ b) = fun s => (ψ b s : Fin n → ℂ)`. Use function extensionality and compare the values at `fun s => hΨ b s.1 s.2`. Rewrite using `[this]`. Conclude with `continuous_subtype_val.comp (hcont b)`.

Take `⟨O, V', g, hO, hAO, hV', hxV', hg, -, hAg, hXV'⟩` from `hsec _ (ψ b ⟨t, ht⟩).2`. Establish `hqt : Function.update t 0 (t 0 ^ ord b) ∈ O`. Rewrite using `[← hAΨ b t ht, hΨ b t ht]`. Conclude with `hAO`. Establish `h1 : ∀ᶠ s in 𝓝 t, s ∈ Metric.ball c δ ∩ {t | t 0 ≠ 0}` using `hopen.mem_nhds ht`.

Establish `h2 : ∀ᶠ s in 𝓝 t, Ψ b s ∈ V'` using `(hcontΨ.continuousAt (hopen.mem_nhds ht)).preimage_mem_nhds (hV'.mem_nhds (by rw [hΨ b t ht]; exact hxV'))`. Establish `heq : Ψ b =ᶠ[𝓝 t] fun s => g (Function.update s 0 (s 0 ^ ord b))` using `by filter_upwards [h1, h2] with s hs hsV`. Establish `hmem : Ψ b s ∈ X ∩ V'` using `⟨by rw [hΨ b s hs]; exact (ψ b ⟨s, hs⟩).2, hsV⟩`. Rewrite `hmem` using `[hXV']`. Take `⟨o, ho, hgo⟩` from `hmem`.

Establish `hAo : A *ᵥ Ψ b s = o` using `by rw [← hgo, hAg o ho]`. Rewrite using `[← hgo, ← hAo, hAΨ b s hs]`. Establish `hdiff : DifferentiableAt ℂ (fun s => g (Function.update s 0 (s 0 ^ ord b))) t` using `(hg.differentiableAt (hO.mem_nhds hqt)).comp t (differentiable_update_pow e (ord b) t)`. Conclude with `(heq.differentiableAt_iff.mpr hdiff).differentiableWithinAt`. Introduce `b t ht`.

Rewrite using `[hΨ b t ht]`. Conclude with `⟨(ψ b ⟨t, ht⟩).2, hA b ⟨t, ht⟩⟩`. Introduce `b t ht t' ht' h`. Rewrite `h` using `[hΨ b t ht, hΨ b t' ht']`. Conclude with `congrArg Subtype.val (hinj b (Subtype.ext h))`.

Introduce `b b' hbb t ht t' ht' h`. Rewrite `h` using `[hΨ b t ht, hΨ b' t' ht']`. Conclude with `hdisj b b' hbb _ _ (Subtype.ext h)`. Introduce `x hx hdist`. Take `⟨b, t, hbt⟩` from `hcover ⟨x, hx⟩ hdist`.

Use `⟨b, t.1, t.2, ?_⟩` and prove the remaining obligations. Rewrite using `[hΨ b t.1 t.2]`. Conclude with `congrArg Subtype.val hbt`.
-/
theorem PuncturedCoverCycles.proof (hCov : FibreSectionsCovering.Statement)
    (hCyc : FiniteCoverPuncturedPolydisc.Statement) : PuncturedCoverCycles.Statement := by
  intro n e N A c r X hr hc0 hXP hfib hsec
  have hX : Set.MapsTo (fun x => A *ᵥ x) X (Metric.ball c r ∩ {t | t 0 ≠ 0}) :=
    fun x hx => hXP x hx
  have hcov := hCov n e N A _ X hX (fun y hy => hfib y hy.1 hy.2) hsec
  have hfib' : ∀ z, (hX.restrict ⁻¹' {z}).encard = N := by
    intro z
    have himg : Subtype.val '' (hX.restrict ⁻¹' {z}) = {x | x ∈ X ∧ A *ᵥ x = z} := by
      ext x
      constructor
      · rintro ⟨x', hx', rfl⟩
        exact ⟨x'.2, congrArg Subtype.val hx'⟩
      · rintro ⟨hx, hxz⟩
        exact ⟨⟨x, hx⟩, Subtype.ext hxz, rfl⟩
    rw [← Subtype.val_injective.encard_image, himg]
    exact hfib z z.2.1 z.2.2
  obtain ⟨m, ord, δ, ψ, hδ0, hδ1, hsum, hord, hcont, hA, hinj, hdisj, hcover⟩ :=
    hCyc e N c r X hX.restrict hr hc0 hcov hfib'
  classical
  let Ψ : Fin m → (Fin (e + 1) → ℂ) → Fin n → ℂ := fun b t =>
    if h : t ∈ Metric.ball c δ ∩ {t | t 0 ≠ 0} then (ψ b ⟨t, h⟩ : Fin n → ℂ) else 0
  have hΨ : ∀ b t (h : t ∈ Metric.ball c δ ∩ {t | t 0 ≠ 0}), Ψ b t = ψ b ⟨t, h⟩ :=
    fun b t h => dif_pos h
  have hAΨ : ∀ b t (h : t ∈ Metric.ball c δ ∩ {t | t 0 ≠ 0}),
      A *ᵥ Ψ b t = Function.update t 0 (t 0 ^ ord b) := by
    intro b t h
    rw [hΨ b t h]
    exact hA b ⟨t, h⟩
  have hopen : IsOpen (Metric.ball c δ ∩ {t : Fin (e + 1) → ℂ | t 0 ≠ 0}) :=
    Metric.isOpen_ball.inter (isOpen_ne_fun (continuous_apply 0) continuous_const)
  refine ⟨m, ord, Ψ, δ, hδ0, hδ1, hsum, hord, ?_, ?_, ?_, ?_, ?_⟩
  · intro b t ht
    have hcontΨ : ContinuousOn (Ψ b) (Metric.ball c δ ∩ {t | t 0 ≠ 0}) := by
      rw [continuousOn_iff_continuous_domRestrict]
      have : (Metric.ball c δ ∩ {t | t 0 ≠ 0}).domRestrict (Ψ b) = fun s => (ψ b s : Fin n → ℂ) :=
        funext fun s => hΨ b s.1 s.2
      rw [this]
      exact continuous_subtype_val.comp (hcont b)
    obtain ⟨O, V', g, hO, hAO, hV', hxV', hg, -, hAg, hXV'⟩ := hsec _ (ψ b ⟨t, ht⟩).2
    have hqt : Function.update t 0 (t 0 ^ ord b) ∈ O := by
      rw [← hAΨ b t ht, hΨ b t ht]
      exact hAO
    have h1 : ∀ᶠ s in 𝓝 t, s ∈ Metric.ball c δ ∩ {t | t 0 ≠ 0} := hopen.mem_nhds ht
    have h2 : ∀ᶠ s in 𝓝 t, Ψ b s ∈ V' :=
      (hcontΨ.continuousAt (hopen.mem_nhds ht)).preimage_mem_nhds
        (hV'.mem_nhds (by rw [hΨ b t ht]; exact hxV'))
    have heq : Ψ b =ᶠ[𝓝 t] fun s => g (Function.update s 0 (s 0 ^ ord b)) := by
      filter_upwards [h1, h2] with s hs hsV
      have hmem : Ψ b s ∈ X ∩ V' := ⟨by rw [hΨ b s hs]; exact (ψ b ⟨s, hs⟩).2, hsV⟩
      rw [hXV'] at hmem
      obtain ⟨o, ho, hgo⟩ := hmem
      have hAo : A *ᵥ Ψ b s = o := by rw [← hgo, hAg o ho]
      rw [← hgo, ← hAo, hAΨ b s hs]
    have hdiff : DifferentiableAt ℂ (fun s => g (Function.update s 0 (s 0 ^ ord b))) t :=
      (hg.differentiableAt (hO.mem_nhds hqt)).comp t (differentiable_update_pow e (ord b) t)
    exact (heq.differentiableAt_iff.mpr hdiff).differentiableWithinAt
  · intro b t ht
    rw [hΨ b t ht]
    exact ⟨(ψ b ⟨t, ht⟩).2, hA b ⟨t, ht⟩⟩
  · intro b t ht t' ht' h
    rw [hΨ b t ht, hΨ b t' ht'] at h
    exact congrArg Subtype.val (hinj b (Subtype.ext h))
  · intro b b' hbb t ht t' ht' h
    rw [hΨ b t ht, hΨ b' t' ht'] at h
    exact hdisj b b' hbb _ _ (Subtype.ext h)
  · intro x hx hdist
    obtain ⟨b, t, hbt⟩ := hcover ⟨x, hx⟩ hdist
    refine ⟨b, t.1, t.2, ?_⟩
    rw [hΨ b t.1 t.2]
    exact congrArg Subtype.val hbt

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
