import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel

namespace Ad3.SchwartzSpaceL2

/- English proof (translation)
Introduce `F _ _ _ _ _ _ ψ hψ μ₁ μ₂ h₁ h₂`. Use `⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hun F ψ hψ μ₁ μ₂ h₁ h₂⟩` and prove the remaining obligations. Take `⟨φ, hφ, h⟩` from `hne F ψ hψ μ₁ μ₂ h₁ h₂`. Conclude with `⟨_, Submodule.subset_span ⟨φ, hφ, rfl⟩, h⟩`. Introduce `W hW h`.

Proceed by induction on `hW using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨φ, hφ, rfl⟩` from `hx`. Take `⟨hm, he⟩` from `htr F ψ hψ μ₁ μ₂ h₁ h₂ φ hφ h`. Establish `: (fun g => W2 ψ μ₁ μ₂ φ (g * h)) = (((μ₂ (GeneralLinearGroup.det h) : ℂˣ) : ℂ) * mp (GeneralLinearGroup.det h) (1 / 2)) • W2 ψ μ₁ μ₂ (rt φ h)`.

Use function extensionality and compare the values at `g`. Rewrite using `[he g]`. Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hm, rfl⟩)`.

Consider the case `zero => exact Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy => exact Submodule.add_mem _ hx hy`. Consider the case `smul a x _ hx => exact Submodule.smul_mem _ a hx`. Introduce `W hW x g`. Proceed by induction on `hW using Submodule.span_induction with`.

Consider the case `mem w hw`. Take `⟨φ, hφ, rfl⟩` from `hw`. Conclude with `hpsi F ψ hψ μ₁ μ₂ h₁ h₂ φ hφ x g`. Consider the case `zero => simp`. Consider the case `add u v _ _ hu hv => simp only [Pi.add_apply, hu, hv]`.

Expand and normalize the polynomial expressions, which then agree. Consider the case `smul a u _ hu => simp only [Pi.smul_apply, smul_eq_mul, hu]`. Expand and normalize the polynomial expressions, which then agree. Introduce `W hW a g`. Proceed by induction on `hW using Submodule.span_induction with`.

Consider the case `mem w hw`. Take `⟨φ, hφ, rfl⟩` from `hw`. Conclude with `hcen F ψ hψ μ₁ μ₂ h₁ h₂ φ hφ a g`. Consider the case `zero => simp`. Consider the case `add u v _ _ hu hv => simp only [Pi.add_apply, hu, hv]`.

Expand and normalize the polynomial expressions, which then agree. Consider the case `smul b u _ hu => simp only [Pi.smul_apply, smul_eq_mul, hu]`. Expand and normalize the polynomial expressions, which then agree. Introduce `W hW`. Proceed by induction on `hW using Submodule.span_induction with`.

Consider the case `mem w hw`. Take `⟨φ, hφ, rfl⟩` from `hw`. Conclude with `hsm F ψ hψ μ₁ μ₂ h₁ h₂ φ hφ`. Consider the case `zero => exact ⟨⊤, fun _ _ _ => rfl⟩`. Consider the case `add u v _ _ hu hv`.

Take `⟨U, hU⟩` from `hu`. Take `⟨V, hV⟩` from `hv`. Use `⟨U ⊓ V, fun g w hw => ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.add_apply, hU g w hw.1, hV g w hw.2]`. Consider the case `smul b u _ hu`.

Take `⟨U, hU⟩` from `hu`. Conclude with `⟨U, fun g w hw => by simp only [Pi.smul_apply, hU g w hw]⟩`. Introduce `W hW ε hε`. Proceed by induction on `hW using Submodule.span_induction with`. Consider the case `mem w hw`.

Take `⟨φ, hφ, rfl⟩` from `hw`. Conclude with `hbd F ψ hψ μ₁ μ₂ h₁ h₂ φ hφ ε hε`. Consider the case `zero => exact ⟨0, 0, fun a k _ => ⟨by simp, fun h => absurd rfl h⟩⟩`. Consider the case `add u v _ _ hu hv`. Take `⟨C₁, B₁, hu⟩` from `hu`.

Take `⟨C₂, B₂, hv⟩` from `hv`. Use `⟨C₁ + C₂, max B₁ B₂, fun a k hk => ⟨?_, fun hne => ?_⟩⟩` and prove the remaining obligations. Establish `h1` using `(hu a k hk).1`. Establish `h2` using `(hv a k hk).1`. Combine the equalities or inequalities in the displayed calculation.

Distinguish the cases in `hu0 : u (dg2 a 1 * k) = 0`. Establish `: v (dg2 a 1 * k) ≠ 0`. Introduce `h0`. Apply `hne` to reduce the goal to its premises. Simplify using `[hu0, h0]`.

Conclude with `le_max_of_le_right ((hv a k hk).2 this)`. Conclude with `le_max_of_le_left ((hu a k hk).2 hu0)`. Consider the case `smul b u _ hu`. Take `⟨C, B, hu⟩` from `hu`. Use `⟨‖b‖ * C, B, fun a k hk => ⟨?_, fun hne => ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_left (hu a k hk).1 (norm_nonneg _)`. Use `(hu a k hk).2 fun h0 => hne ?_` and prove the remaining obligations. Simplify using `[h0]`. Introduce `W hW c hc s hs0 hs1`.

It suffices to establish `H : Integrable (fun a : Fˣ => W (dg2 a 1 * w0) * (((μ₁ a * μ₂ a * c a)⁻¹ : ℂˣ) : ℂ) * mp a (1 / 2 - s)) (multHaar F) ∧ Integrable (fun a : Fˣ => W (dg2 a 1) * ((c a : ℂˣ) : ℂ) * mp a (s - 1 / 2)) (multHaar F) ∧ ∫ a, W (dg2 a 1 * w0) * (((μ₁ a * μ₂ a * c a)⁻¹ : ℂˣ) : ℂ) * mp a (1 …`. Proceed by induction on `hW using Submodule.span_induction with`. Consider the case `mem w hw`. Take `⟨φ, hφ, rfl⟩` from `hw`. Conclude with `hfe F ψ hψ μ₁ μ₂ h₁ h₂ φ hφ c hc s hs0 hs1`.

Consider the case `zero => simp`. Consider the case `add u v _ _ hu hv`. Take `⟨hu1, hu2, hu3⟩` from `hu`. Take `⟨hv1, hv2, hv3⟩` from `hv`. Simplify using `only [Pi.add_apply, add_mul]`.

Use `⟨hu1.add hv1, hu2.add hv2, ?_⟩` and prove the remaining obligations. Rewrite using `[integral_add hu1 hv1, integral_add hu2 hv2, hu3, hv3]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `smul b u _ hu`. Take `⟨hu1, hu2, hu3⟩` from `hu`.

Simplify using `only [Pi.smul_apply, smul_eq_mul, mul_assoc]`. Simplify using `only [← mul_assoc] at hu1 hu2 hu3 ⊢`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Simplify `hu1.const_mul b` using `only [mul_assoc]`. Simplify `hu2.const_mul b` using `only [mul_assoc]`.

Simplify using `only [mul_assoc]`. Rewrite using `[integral_const_mul, integral_const_mul]`. Simplify using `only [← mul_assoc] at hu3 ⊢`. Rewrite using `[hu3]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem top (hpsi : SPsi) (hcen : SCen) (htr : STrans) (hsm : SSmooth) (hbd : SBound) (hne : SNe)
    (hun : SUnr) (hfe : FeGen) : Loc2 := by
  intro F _ _ _ _ _ _ ψ hψ μ₁ μ₂ h₁ h₂
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hun F ψ hψ μ₁ μ₂ h₁ h₂⟩
  · obtain ⟨φ, hφ, h⟩ := hne F ψ hψ μ₁ μ₂ h₁ h₂
    exact ⟨_, Submodule.subset_span ⟨φ, hφ, rfl⟩, h⟩
  · intro W hW h
    induction hW using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨φ, hφ, rfl⟩ := hx
      obtain ⟨hm, he⟩ := htr F ψ hψ μ₁ μ₂ h₁ h₂ φ hφ h
      have : (fun g => W2 ψ μ₁ μ₂ φ (g * h)) =
          (((μ₂ (GeneralLinearGroup.det h) : ℂˣ) : ℂ) * mp (GeneralLinearGroup.det h) (1 / 2)) •
            W2 ψ μ₁ μ₂ (rt φ h) := by
        funext g; rw [he g]; rfl
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hm, rfl⟩)
    | zero => exact Submodule.zero_mem _
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | smul a x _ hx => exact Submodule.smul_mem _ a hx
  · intro W hW x g
    induction hW using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨φ, hφ, rfl⟩ := hw
      exact hpsi F ψ hψ μ₁ μ₂ h₁ h₂ φ hφ x g
    | zero => simp
    | add u v _ _ hu hv => simp only [Pi.add_apply, hu, hv]; ring
    | smul a u _ hu => simp only [Pi.smul_apply, smul_eq_mul, hu]; ring
  · intro W hW a g
    induction hW using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨φ, hφ, rfl⟩ := hw
      exact hcen F ψ hψ μ₁ μ₂ h₁ h₂ φ hφ a g
    | zero => simp
    | add u v _ _ hu hv => simp only [Pi.add_apply, hu, hv]; ring
    | smul b u _ hu => simp only [Pi.smul_apply, smul_eq_mul, hu]; ring
  · intro W hW
    induction hW using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨φ, hφ, rfl⟩ := hw
      exact hsm F ψ hψ μ₁ μ₂ h₁ h₂ φ hφ
    | zero => exact ⟨⊤, fun _ _ _ => rfl⟩
    | add u v _ _ hu hv =>
      obtain ⟨U, hU⟩ := hu
      obtain ⟨V, hV⟩ := hv
      refine ⟨U ⊓ V, fun g w hw => ?_⟩
      simp only [Pi.add_apply, hU g w hw.1, hV g w hw.2]
    | smul b u _ hu =>
      obtain ⟨U, hU⟩ := hu
      exact ⟨U, fun g w hw => by simp only [Pi.smul_apply, hU g w hw]⟩
  · intro W hW ε hε
    induction hW using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨φ, hφ, rfl⟩ := hw
      exact hbd F ψ hψ μ₁ μ₂ h₁ h₂ φ hφ ε hε
    | zero => exact ⟨0, 0, fun a k _ => ⟨by simp, fun h => absurd rfl h⟩⟩
    | add u v _ _ hu hv =>
      obtain ⟨C₁, B₁, hu⟩ := hu
      obtain ⟨C₂, B₂, hv⟩ := hv
      refine ⟨C₁ + C₂, max B₁ B₂, fun a k hk => ⟨?_, fun hne => ?_⟩⟩
      · have h1 := (hu a k hk).1
        have h2 := (hv a k hk).1
        calc ‖(u + v) (dg2 a 1 * k)‖ ≤ ‖u (dg2 a 1 * k)‖ + ‖v (dg2 a 1 * k)‖ := norm_add_le _ _
          _ ≤ _ := by rw [add_mul]; exact add_le_add h1 h2
      · by_cases hu0 : u (dg2 a 1 * k) = 0
        · have : v (dg2 a 1 * k) ≠ 0 := by
            intro h0; apply hne; simp [hu0, h0]
          exact le_max_of_le_right ((hv a k hk).2 this)
        · exact le_max_of_le_left ((hu a k hk).2 hu0)
    | smul b u _ hu =>
      obtain ⟨C, B, hu⟩ := hu
      refine ⟨‖b‖ * C, B, fun a k hk => ⟨?_, fun hne => ?_⟩⟩
      · rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
        exact mul_le_mul_of_nonneg_left (hu a k hk).1 (norm_nonneg _)
      · refine (hu a k hk).2 fun h0 => hne ?_
        simp [h0]
  · intro W hW c hc s hs0 hs1
    suffices H : Integrable (fun a : Fˣ => W (dg2 a 1 * w0) * (((μ₁ a * μ₂ a * c a)⁻¹ : ℂˣ) : ℂ) *
          mp a (1 / 2 - s)) (multHaar F) ∧
        Integrable (fun a : Fˣ => W (dg2 a 1) * ((c a : ℂˣ) : ℂ) * mp a (s - 1 / 2)) (multHaar F) ∧
        ∫ a, W (dg2 a 1 * w0) * (((μ₁ a * μ₂ a * c a)⁻¹ : ℂˣ) : ℂ) * mp a (1 / 2 - s) ∂multHaar F =
          gam ψ (μ₁ * c) s * gam ψ (μ₂ * c) s *
            ∫ a, W (dg2 a 1) * ((c a : ℂˣ) : ℂ) * mp a (s - 1 / 2) ∂multHaar F from H.2.2
    induction hW using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨φ, hφ, rfl⟩ := hw
      exact hfe F ψ hψ μ₁ μ₂ h₁ h₂ φ hφ c hc s hs0 hs1
    | zero => simp
    | add u v _ _ hu hv =>
      obtain ⟨hu1, hu2, hu3⟩ := hu
      obtain ⟨hv1, hv2, hv3⟩ := hv
      simp only [Pi.add_apply, add_mul]
      refine ⟨hu1.add hv1, hu2.add hv2, ?_⟩
      rw [integral_add hu1 hv1, integral_add hu2 hv2, hu3, hv3]
      ring
    | smul b u _ hu =>
      obtain ⟨hu1, hu2, hu3⟩ := hu
      simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
      simp only [← mul_assoc] at hu1 hu2 hu3 ⊢
      refine ⟨?_, ?_, ?_⟩
      · simpa only [mul_assoc] using hu1.const_mul b
      · simpa only [mul_assoc] using hu2.const_mul b
      · simp only [mul_assoc]
        rw [integral_const_mul, integral_const_mul]
        simp only [← mul_assoc] at hu3 ⊢
        rw [hu3]
        ring

/- English proof (translation)
The claim follows from `top hpsi hcen htr hsm hbd hne hun (hfe hdz hwd hpu hli htr hta)`.
-/
theorem top' (hpsi : SPsi) (hcen : SCen) (htr : STrans) (hsm : SSmooth) (hbd : SBound) (hne : SNe)
    (hun : SUnr) (hdz : SDZ) (hwd : SWd) (hpu : SPure) (hli : SLin) (hta : STate) (hfe : SFe) : Loc2 :=
  top hpsi hcen htr hsm hbd hne hun (hfe hdz hwd hpu hli htr hta)

end Ad3.SchwartzSpaceL2
