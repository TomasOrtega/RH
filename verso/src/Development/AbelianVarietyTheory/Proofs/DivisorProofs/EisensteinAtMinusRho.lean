import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinConstantTermSettingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyUniformModerateGrowth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRhoOfCore
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinConstantTermSettingAltBis

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n J r X Y L a h hS`. Take `⟨hcm, hun, hJ, hn, hW, hA, hI⟩` from `hS`. Take `⟨Eis, c, p1, p2, p3, p4, p5⟩` from `hK.eisensteinIsotropicLine F E σ hcm hun n J hJ r X Y hW (col0 X) (col0 Y)`. Use `rfl rfl L a hA h hI.1 hI.2`. Establish `hP : EisensteinHyp σ J (col0 X) (col0 Y) h Eis c` using `⟨p1, p2, p3, p4, p5⟩`.

Establish `hS : HidaSetting σ J X Y L a h` using `⟨hcm, hun, hJ, hn, hW, hA, hI⟩`. Take `⟨mid, hmid, hct⟩` from `GlobalTheory.T.eisenstein_constant_term_setting hK.eisensteinIsotropicLine F E σ n J r X Y L a h Eis c hS hP`. Take `⟨u, U₀, U₁, Hol, C, N, ⟨hU₀, hu, hu0, hcu⟩, hU₁, hHol, hHd, hHb, hHρ⟩` from `GlobalTheory.T.eisenstein_constant_term_setting_alt hK.eisensteinResidueLine F E σ n J r X Y L a h Eis c hS hP mid hmid hct`. Use `set ρ : ℂ := ((n : ℂ) - 1) / 2 with hρ`. Establish `hpos : 0 < ‖u ρ‖` using `norm_pos_iff.2 hu0`.

Establish `hev : ∀ᶠ s in 𝓝 (-ρ), (s ≠ -ρ → c s * c (-s) = 1 ∧ ∀ g, Eis s g = c s * Eis (-s) g) ∧ -s ∈ U₀ ∧ -s ∈ U₁ ∧ ‖u ρ‖ / 2 < ‖u (-s)‖`. Establish `t : Tendsto (fun s : ℂ => -s) (𝓝 (-ρ)) (𝓝 ρ)` using `by simpa using (continuous_neg.tendsto (-ρ))`. Establish `hucont : ContinuousAt u ρ` using `(hu.differentiableAt hU₀).continuousAt`. Use `((eventually_nhdsWithin_iff.1 (p5 (-ρ))).mono fun s hs hne => hs hne).and ((t.eventually hU₀).and ((t.eventually hU₁).and ?_))` and prove the remaining obligations. Establish `: Tendsto (fun s : ℂ => ‖u (-s)‖) (𝓝 (-ρ)) (𝓝 ‖u ρ‖)` using `(continuous_norm.tendsto _).comp (hucont.tendsto.comp t)`.

Conclude with `this.eventually_const_lt (by linarith)`. Take `⟨V, hV, hVs⟩` from `hev.exists_mem`. Set `Eis' : ℂ → GAd σ J → ℂ` to `fun s g => if s = -ρ then 1 else Eis s g`. Establish `hform : ∀ s ∈ V, ∀ g, Eis' s g = Hol (-s) g / u (-s)`. Introduce `s hs g`.

Take `⟨h1, h2, h3, h4⟩` from `hVs s hs`. Distinguish the cases in `e : s = -ρ`. Substitute `e` using the available equality. Simplify using `[Eis', hHρ, div_self hu0]`. Establish `hne : -s ≠ ρ` using `fun h' => e (by rw [← h', neg_neg])`.

Establish `hu' : u (-s) ≠ 0` using `fun h0 => by rw [h0, norm_zero] at h4; linarith`. Establish `hd : -s - ρ ≠ 0` using `sub_ne_zero.2 hne`. Take `⟨hc1, hc2⟩` from `h1 e`. Establish `hc' : c s * (u (-s) / (-s - ρ)) = 1` using `by rw [← hcu (-s) h2 hne]; exact hc1`. Simplify using `only [Eis', if_neg e]`.

Rewrite using `[hc2 g, hHol (-s) h3 hne g]`. Clear denominators, using `at hc' ⊢` for the nonvanishing conditions. Take the linear combination `Eis (-s) g * hc'`. Establish `hneg : ∃ U ∈ 𝓝 (-ρ), ∃ (C : ℝ) (N : ℕ), ∀ g, DifferentiableOn ℂ (Eis' · g) U ∧ (∀ s ∈ U, ‖Eis' s g‖ ≤ C * (height σ J g : ℝ) ^ N) ∧ Eis' (-ρ) g = 1`. Use `⟨V, hV, 2 * C / ‖u ρ‖, N, fun g => ⟨?_, ?_, by simp [Eis']⟩⟩` and prove the remaining obligations.

Establish `hd : DifferentiableOn ℂ (fun s => Hol (-s) g / u (-s)) V`. Use `DifferentiableOn.div ((hHd g).comp differentiable_neg.differentiableOn fun s hs => (hVs s hs).2.2.1) (hu.comp differentiable_neg.differentiableOn fun s hs => (hVs s hs).2.1) fun s hs => ?_` and prove the remaining obligations. Use `(hVs s hs).2.2.2` as an intermediate fact. Introduce `h0`. Rewrite `this` using `[h0, norm_zero]`.

Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `hd.congr fun s hs => hform s hs g`. Introduce `s hs`. Rewrite using `[hform s hs g, norm_div]`. Establish `h1` using `hHb (-s) (hVs s hs).2.2.1 g`.

Establish `h2` using `(hVs s hs).2.2.2`. Establish `h0 : 0 ≤ C * (height σ J g : ℝ) ^ N` using `(norm_nonneg _).trans h1`. Combine the equalities or inequalities in the displayed calculation. Use `⟨Eis', ?_, ?_, hneg⟩` and prove the remaining obligations. Introduce `T hT s hs g`.

Establish `hne : s ≠ -ρ`. Introduce and unpack `rfl`. Establish `e : (-ρ).re = -(((n : ℝ) - 1) / 2)` using `by simp [hρ]`. Establish `hn' : (4 : ℝ) ≤ n` using `by exact_mod_cast hn`. Rewrite `hs` using `[e]`.

Combine the linear equalities and inequalities to obtain the conclusion. Simplify `p1 T hT s hs g` using `[Eis', hne]`. Introduce `s₀`. Distinguish the cases in `h0 : s₀ = -ρ`. Substitute `h0` using the available equality.

Take `⟨V', hV', C', N', hall⟩` from `hneg`. Conclude with `⟨0, V', Eis', C', N', hV', fun s _ _ g => by simp, fun g => (hall g).1, fun s hs g => (hall g).2.1 s hs⟩`. Take `⟨k, U, H, hU, hH, hsm, hhol⟩` from `p4 s₀`. Take `⟨V', hV', C', N', hb⟩` from `GlobalTheory.WeakHolFamily.locally_uniform_moderate_growth F E σ n J H s₀ U hU hsm hhol`. Use `⟨k, U ∩ V' ∩ {-ρ}ᶜ, H, C', N', Filter.inter_mem (Filter.inter_mem hU hV') (isOpen_compl_singleton.mem_nhds h0), fun s hs hs0 g => ?_, fun g => ?_, fun s hs g => hb s hs.1.2 g⟩` and prove the remaining obligations.

Establish `e : s ≠ -ρ` using `hs.2`. Simplify using `only [Eis', if_neg e]`. Conclude with `hH s hs.1.1 hs0 g`. Conclude with `(hhol _ (GlobalTheory.EisLine.isModerateForm_proj σ J g)).mono fun s hs => hs.1.1`.
-/
theorem GlobalTheory.EisRes.eisCore_of_kazhdanPatterson (hK : GlobalTheory.ThK.KP) : EisCore := by
  intro F E _ _ _ _ _ σ n J r X Y L a h hS
  obtain ⟨hcm, hun, hJ, hn, hW, hA, hI⟩ := hS
  obtain ⟨Eis, c, p1, p2, p3, p4, p5⟩ := hK.eisensteinIsotropicLine F E σ hcm hun n J hJ r X Y hW (col0 X) (col0 Y)
    rfl rfl L a hA h hI.1 hI.2
  have hP : EisensteinHyp σ J (col0 X) (col0 Y) h Eis c := ⟨p1, p2, p3, p4, p5⟩
  have hS : HidaSetting σ J X Y L a h := ⟨hcm, hun, hJ, hn, hW, hA, hI⟩
  obtain ⟨mid, hmid, hct⟩ := GlobalTheory.T.eisenstein_constant_term_setting hK.eisensteinIsotropicLine F E σ n J r X Y L a h Eis c hS hP
  obtain ⟨u, U₀, U₁, Hol, C, N, ⟨hU₀, hu, hu0, hcu⟩, hU₁, hHol, hHd, hHb, hHρ⟩ :=
    GlobalTheory.T.eisenstein_constant_term_setting_alt hK.eisensteinResidueLine F E σ n J r X Y L a h Eis c hS hP mid hmid hct
  set ρ : ℂ := ((n : ℂ) - 1) / 2 with hρ
  have hpos : 0 < ‖u ρ‖ := norm_pos_iff.2 hu0
  have hev : ∀ᶠ s in 𝓝 (-ρ), (s ≠ -ρ → c s * c (-s) = 1 ∧ ∀ g, Eis s g = c s * Eis (-s) g) ∧ -s ∈ U₀ ∧ -s ∈ U₁ ∧
      ‖u ρ‖ / 2 < ‖u (-s)‖ := by
    have t : Tendsto (fun s : ℂ => -s) (𝓝 (-ρ)) (𝓝 ρ) := by simpa using (continuous_neg.tendsto (-ρ))
    have hucont : ContinuousAt u ρ := (hu.differentiableAt hU₀).continuousAt
    refine ((eventually_nhdsWithin_iff.1 (p5 (-ρ))).mono fun s hs hne => hs hne).and
      ((t.eventually hU₀).and ((t.eventually hU₁).and ?_))
    have : Tendsto (fun s : ℂ => ‖u (-s)‖) (𝓝 (-ρ)) (𝓝 ‖u ρ‖) :=
      (continuous_norm.tendsto _).comp (hucont.tendsto.comp t)
    exact this.eventually_const_lt (by linarith)
  obtain ⟨V, hV, hVs⟩ := hev.exists_mem
  let Eis' : ℂ → GAd σ J → ℂ := fun s g => if s = -ρ then 1 else Eis s g
  have hform : ∀ s ∈ V, ∀ g, Eis' s g = Hol (-s) g / u (-s) := by
    intro s hs g
    obtain ⟨h1, h2, h3, h4⟩ := hVs s hs
    by_cases e : s = -ρ
    · subst e
      simp [Eis', hHρ, div_self hu0]
    · have hne : -s ≠ ρ := fun h' => e (by rw [← h', neg_neg])
      have hu' : u (-s) ≠ 0 := fun h0 => by rw [h0, norm_zero] at h4; linarith
      have hd : -s - ρ ≠ 0 := sub_ne_zero.2 hne
      obtain ⟨hc1, hc2⟩ := h1 e
      have hc' : c s * (u (-s) / (-s - ρ)) = 1 := by rw [← hcu (-s) h2 hne]; exact hc1
      simp only [Eis', if_neg e]
      rw [hc2 g, hHol (-s) h3 hne g]
      field_simp at hc' ⊢
      linear_combination Eis (-s) g * hc'
  have hneg : ∃ U ∈ 𝓝 (-ρ), ∃ (C : ℝ) (N : ℕ), ∀ g, DifferentiableOn ℂ (Eis' · g) U ∧
      (∀ s ∈ U, ‖Eis' s g‖ ≤ C * (height σ J g : ℝ) ^ N) ∧ Eis' (-ρ) g = 1 := by
    refine ⟨V, hV, 2 * C / ‖u ρ‖, N, fun g => ⟨?_, ?_, by simp [Eis']⟩⟩
    · have hd : DifferentiableOn ℂ (fun s => Hol (-s) g / u (-s)) V := by
        refine DifferentiableOn.div ((hHd g).comp differentiable_neg.differentiableOn fun s hs => (hVs s hs).2.2.1)
          (hu.comp differentiable_neg.differentiableOn fun s hs => (hVs s hs).2.1) fun s hs => ?_
        have := (hVs s hs).2.2.2
        intro h0; rw [h0, norm_zero] at this; linarith
      exact hd.congr fun s hs => hform s hs g
    · intro s hs
      rw [hform s hs g, norm_div]
      have h1 := hHb (-s) (hVs s hs).2.2.1 g
      have h2 := (hVs s hs).2.2.2
      have h0 : 0 ≤ C * (height σ J g : ℝ) ^ N := (norm_nonneg _).trans h1
      calc ‖Hol (-s) g‖ / ‖u (-s)‖ ≤ C * (height σ J g : ℝ) ^ N / (‖u ρ‖ / 2) :=
            div_le_div₀ h0 h1 (by linarith) h2.le
        _ = 2 * C / ‖u ρ‖ * (height σ J g : ℝ) ^ N := by field_simp
  refine ⟨Eis', ?_, ?_, hneg⟩
  · intro T hT s hs g
    have hne : s ≠ -ρ := by
      rintro rfl
      have e : (-ρ).re = -(((n : ℝ) - 1) / 2) := by simp [hρ]
      have hn' : (4 : ℝ) ≤ n := by exact_mod_cast hn
      rw [e] at hs
      linarith
    simpa [Eis', hne] using p1 T hT s hs g
  · intro s₀
    by_cases h0 : s₀ = -ρ
    · subst h0
      obtain ⟨V', hV', C', N', hall⟩ := hneg
      exact ⟨0, V', Eis', C', N', hV', fun s _ _ g => by simp, fun g => (hall g).1, fun s hs g => (hall g).2.1 s hs⟩
    · obtain ⟨k, U, H, hU, hH, hsm, hhol⟩ := p4 s₀
      obtain ⟨V', hV', C', N', hb⟩ := GlobalTheory.WeakHolFamily.locally_uniform_moderate_growth F E σ n J H s₀ U hU hsm hhol
      refine ⟨k, U ∩ V' ∩ {-ρ}ᶜ, H, C', N', Filter.inter_mem (Filter.inter_mem hU hV')
        (isOpen_compl_singleton.mem_nhds h0), fun s hs hs0 g => ?_, fun g => ?_, fun s hs g => hb s hs.1.2 g⟩
      · have e : s ≠ -ρ := hs.2
        simp only [Eis', if_neg e]
        exact hH s hs.1.1 hs0 g
      · exact (hhol _ (GlobalTheory.EisLine.isModerateForm_proj σ J g)).mono fun s hs => hs.1.1

/- English proof (translation)
Introduce `hK` and use `GlobalTheory.EisReduce.eisAtMinusRho_of_core (GlobalTheory.EisRes.eisCore_of_kazhdanPatterson hK)`.
-/
theorem GlobalTheory.ConeSmall.eisAtMinusRho : GlobalTheory.ThK.KP → GlobalTheory.ConeSmall.EisAtMinusRho := fun hK =>
  GlobalTheory.EisReduce.eisAtMinusRho_of_core (GlobalTheory.EisRes.eisCore_of_kazhdanPatterson hK)

end
