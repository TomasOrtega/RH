import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.GoodHeightExists
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.ExplicitFormulaFromGluing

noncomputable section

namespace PI.EF

open Complex Filter Topology Set DirichletCharacter

/- English proof (translation)
Rewrite using `[rect, Complex.mem_reProdIm]`. Simplify using `only [Set.mem_Icc]`.
-/
lemma mem_rect_iff {x₀ x₁ y₀ y₁ : ℝ} {s : ℂ} :
    s ∈ rect x₀ x₁ y₀ y₁ ↔ (x₀ ≤ s.re ∧ s.re ≤ x₁) ∧ (y₀ ≤ s.im ∧ s.im ≤ y₁) := by
  rw [rect, Complex.mem_reProdIm]
  simp only [Set.mem_Icc]

/- English proof (translation)
Establish `hre : ∀ a b : ℝ, ((a : ℂ) + b * I).re = a` using `fun a b => by simp`. Establish `him : ∀ a b : ℝ, ((a : ℂ) + b * I).im = b` using `fun a b => by simp`. Establish `hxI` using `Set.uIcc_of_le hx`. Establish `hyI` using `Set.uIcc_of_le hy`. Establish `e1 : ∀ y : ℝ, y₀ ≤ y → y ≤ y₁ → (y = y₀ ∨ y = y₁) → (∫ x : ℝ in x₀..x₁, f (x + y * I)) = ∫ x : ℝ in x₀..x₁, g (x + y * I)`.

Introduce `y hy0 hy1 hyy`. Use `intervalIntegral.integral_congr fun x hxm => ?_` and prove the remaining obligations. Rewrite `hxm` using `[hxI]`. Apply `h` to reduce the goal to its premises. Rewrite using `[mem_rect_iff, hre, him]`.

Conclude with `⟨hxm, hy0, hy1⟩`. Rewrite using `[hre, him]`. Break down `hyy with e | e` into its components or cases. Conclude with `Or.inr (Or.inr (Or.inl e))`. Conclude with `Or.inr (Or.inr (Or.inr e))`.

Establish `e2 : ∀ x : ℝ, x₀ ≤ x → x ≤ x₁ → (x = x₀ ∨ x = x₁) → (∫ y : ℝ in y₀..y₁, f (x + y * I)) = ∫ y : ℝ in y₀..y₁, g (x + y * I)`. Introduce `x hx0 hx1 hxx`. Use `intervalIntegral.integral_congr fun y hym => ?_` and prove the remaining obligations. Rewrite `hym` using `[hyI]`. Apply `h` to reduce the goal to its premises.

Rewrite using `[mem_rect_iff, hre, him]`. Conclude with `⟨⟨hx0, hx1⟩, hym⟩`. Rewrite using `[hre, him]`. Break down `hxx with e | e` into its components or cases. Conclude with `Or.inl e`.

Conclude with `Or.inr (Or.inl e)`. Unfold `rectInt`. Rewrite using `[e1 y₀ le_rfl hy (Or.inl rfl), e1 y₁ hy le_rfl (Or.inr rfl), e2 x₁ hx le_rfl (Or.inr rfl), e2 x₀ le_rfl hx (Or.inl rfl)]`.
-/
lemma rectInt_congr_sides {f g : ℂ → ℂ} {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁)
    (h : ∀ s ∈ rect x₀ x₁ y₀ y₁, (s.re = x₀ ∨ s.re = x₁ ∨ s.im = y₀ ∨ s.im = y₁) → f s = g s) :
    rectInt f x₀ x₁ y₀ y₁ = rectInt g x₀ x₁ y₀ y₁ := by
  have hre : ∀ a b : ℝ, ((a : ℂ) + b * I).re = a := fun a b => by simp
  have him : ∀ a b : ℝ, ((a : ℂ) + b * I).im = b := fun a b => by simp
  have hxI := Set.uIcc_of_le hx
  have hyI := Set.uIcc_of_le hy
  have e1 : ∀ y : ℝ, y₀ ≤ y → y ≤ y₁ → (y = y₀ ∨ y = y₁) →
      (∫ x : ℝ in x₀..x₁, f (x + y * I)) = ∫ x : ℝ in x₀..x₁, g (x + y * I) := by
    intro y hy0 hy1 hyy
    refine intervalIntegral.integral_congr fun x hxm => ?_
    rw [hxI] at hxm
    apply h
    · rw [mem_rect_iff, hre, him]
      exact ⟨hxm, hy0, hy1⟩
    · rw [hre, him]
      rcases hyy with e | e
      · exact Or.inr (Or.inr (Or.inl e))
      · exact Or.inr (Or.inr (Or.inr e))
  have e2 : ∀ x : ℝ, x₀ ≤ x → x ≤ x₁ → (x = x₀ ∨ x = x₁) →
      (∫ y : ℝ in y₀..y₁, f (x + y * I)) = ∫ y : ℝ in y₀..y₁, g (x + y * I) := by
    intro x hx0 hx1 hxx
    refine intervalIntegral.integral_congr fun y hym => ?_
    rw [hyI] at hym
    apply h
    · rw [mem_rect_iff, hre, him]
      exact ⟨⟨hx0, hx1⟩, hym⟩
    · rw [hre, him]
      rcases hxx with e | e
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
  unfold rectInt
  rw [e1 y₀ le_rfl hy (Or.inl rfl), e1 y₁ hy le_rfl (Or.inr rfl), e2 x₁ hx le_rfl (Or.inr rfl),
    e2 x₀ le_rfl hx (Or.inl rfl)]

/- English proof (translation)
Introduce `hR hZ hF N _ χ hχ u T' H hu hT hno hreg`. Establish `hlog : 0 < Real.log u` using `Real.log_pos (by linarith)`. Establish `hc : 1 < cLine u`. Unfold `cLine`. Use `one_div_pos.2 hlog` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hfin` using `hF N χ hχ T'`. Use `set S := hfin.toFinset with hS`. Establish `hmemS : ∀ ρ, ρ ∈ S ↔ ρ ∈ ZerosBelow χ T'` using `fun ρ => hfin.mem_toFinset`. Establish `h1S : (1 : ℂ) ∉ S`.

Rewrite using `[hmemS]`. Introduce `h`. Use `h.2.1` as an intermediate fact. Simplify using `at this`. Use `set Z := insert (1 : ℂ) S with hZdef`.

Use `set wt : ℂ → ℂ := fun ρ => if ρ = 1 then -del1 χ else (mult χ ρ : ℂ) with hwt`. Establish `hfs : ∀ g : ℂ → ℂ, (∑ᶠ ρ ∈ ZerosBelow χ T', g ρ) = ∑ ρ ∈ S, g ρ` using `fun g => finsum_mem_eq_finite_toFinset_sum g hfin`. Establish `hsumZ : ∀ F : ℂ → ℂ → ℂ, ∑ ρ ∈ Z, F (wt ρ) ρ = F (-del1 χ) 1 + ∑ ρ ∈ S, F (mult χ ρ) ρ`. Introduce `F`. Rewrite using `[hZdef, Finset.sum_insert h1S]`.

Use `congr 1`. Simplify using `[hwt]`. Use `Finset.sum_congr rfl fun ρ hρ => ?_` and prove the remaining obligations. Establish `: ρ ≠ 1` using `fun e => h1S (e ▸ hρ)`. Simplify using `[hwt, this]`.

Establish `hbd : rectInt (fun s => logDeriv (DirichletCharacter.LFunction χ) s * ((u : ℂ) ^ s / s)) (-1 / 2) (cLine u) (-T') T' = rectInt (fun s => (H s + (∑ ρ ∈ Z, wt ρ / (s - ρ)) + eps0 χ / s) * ((u : ℂ) ^ s / s)) (-1 / 2) (cLine u) (-T') T'`. Apply `rectInt_congr_sides (by linarith) (by linarith)` to reduce the goal to its premises. Introduce `s hs hside`. Establish `hs'` using `mem_rect_iff.1 hs`. Establish `hs1 : s ≠ 1`.

Introduce `e`. Establish `r1 : s.re = 1` using `by rw [e]; simp`. Establish `i1 : s.im = 0` using `by rw [e]; simp`. Apply the tactic sequence `rcases hside with e' | e' | e' | e' <;> linarith`. Establish `hL : DirichletCharacter.LFunction χ s ≠ 0`.

Introduce `h0`. Break down `hZ N χ hχ s (by linarith [hs'.1.1]) hs1 h0 with h | ⟨h, -⟩ | ⟨h, -⟩` into its components or cases. Break down `hside with e | e | e | e` into its components or cases. Combine the linear relations using `[h.1]`. Combine the linear relations using `[h.2]`.

Conclude with `hno s h.1 h.2 h0 (by rw [e, abs_neg, abs_of_pos (by linarith)])`. Conclude with `hno s h.1 h.2 h0 (by rw [e, abs_of_pos (by linarith)])`. Establish `r1 : s.re = 0` using `by rw [h]; simp`. Establish `i1 : s.im = 0` using `by rw [h]; simp`. Apply the tactic sequence `rcases hside with e' | e' | e' | e' <;> linarith`.

Establish `r1 : s.re = -1` using `by rw [h]; simp`. Establish `i1 : s.im = 0` using `by rw [h]; simp`. Apply the tactic sequence `rcases hside with e' | e' | e' | e' <;> linarith`. Rewrite using `[hreg.2 s hs hL hs1, hfs]`. Use `hsumZ (fun w ρ => w / (s - ρ))` as an intermediate fact.

Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hbd, hR (-1 / 2) (cLine u) (-T') T' H Z wt (eps0 χ) u (by linarith) (by norm_num) (by linarith) (by linarith) (by linarith) hreg.1 ?_]`. Use `hsumZ (fun w ρ => w * (((u : ℂ) ^ ρ - 1) / ρ))` as an intermediate fact. Rewrite using `[this, zsum, hfs, hfs, Complex.cpow_one]`.

Establish `e : ∑ ρ ∈ S, (mult χ ρ : ℂ) * (((u : ℂ) ^ ρ - 1) / ρ) = ∑ ρ ∈ S, (mult χ ρ : ℂ) * ((u : ℂ) ^ ρ / ρ) - ∑ ρ ∈ S, (mult χ ρ : ℂ) / ρ`. Rewrite using `[← Finset.sum_sub_distrib]`. Conclude with `Finset.sum_congr rfl fun ρ _ => by ring`. Rewrite using `[e]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `ρ hρ`. Rewrite `hρ` using `[hZdef, Finset.mem_insert]`. Break down `hρ with e | hρ` into its components or cases. Substitute `e` using the available equality. Simplify using `only [Complex.one_re, Complex.one_im]`.

Conclude with `⟨one_ne_zero, by norm_num, hc, by linarith, by linarith⟩`. Take `⟨h0, h1, him, -⟩` from `(hmemS ρ).1 hρ`. Rewrite `him` using `[abs_lt]`. Use `⟨fun e => by rw [e] at h0; simp at h0, by linarith, by linarith, him.1, him.2⟩` and prove the remaining obligations.
-/
theorem glueContour : GlueContour := by
  intro hR hZ hF N _ χ hχ u T' H hu hT hno hreg
  have hlog : 0 < Real.log u := Real.log_pos (by linarith)
  have hc : 1 < cLine u := by
    unfold cLine
    have := one_div_pos.2 hlog
    linarith
  have hfin := hF N χ hχ T'
  set S := hfin.toFinset with hS
  have hmemS : ∀ ρ, ρ ∈ S ↔ ρ ∈ ZerosBelow χ T' := fun ρ => hfin.mem_toFinset
  have h1S : (1 : ℂ) ∉ S := by
    rw [hmemS]
    intro h
    have := h.2.1
    simp at this
  set Z := insert (1 : ℂ) S with hZdef
  set wt : ℂ → ℂ := fun ρ => if ρ = 1 then -del1 χ else (mult χ ρ : ℂ) with hwt
  have hfs : ∀ g : ℂ → ℂ, (∑ᶠ ρ ∈ ZerosBelow χ T', g ρ) = ∑ ρ ∈ S, g ρ := fun g =>
    finsum_mem_eq_finite_toFinset_sum g hfin

  have hsumZ : ∀ F : ℂ → ℂ → ℂ, ∑ ρ ∈ Z, F (wt ρ) ρ = F (-del1 χ) 1 + ∑ ρ ∈ S, F (mult χ ρ) ρ := by
    intro F
    rw [hZdef, Finset.sum_insert h1S]
    congr 1
    · simp [hwt]
    · refine Finset.sum_congr rfl fun ρ hρ => ?_
      have : ρ ≠ 1 := fun e => h1S (e ▸ hρ)
      simp [hwt, this]

  have hbd : rectInt (fun s => logDeriv (DirichletCharacter.LFunction χ) s * ((u : ℂ) ^ s / s))
        (-1 / 2) (cLine u) (-T') T' =
      rectInt (fun s => (H s + (∑ ρ ∈ Z, wt ρ / (s - ρ)) + eps0 χ / s) * ((u : ℂ) ^ s / s))
        (-1 / 2) (cLine u) (-T') T' := by
    apply rectInt_congr_sides (by linarith) (by linarith)
    intro s hs hside
    have hs' := mem_rect_iff.1 hs
    have hs1 : s ≠ 1 := by
      intro e
      have r1 : s.re = 1 := by rw [e]; simp
      have i1 : s.im = 0 := by rw [e]; simp
      rcases hside with e' | e' | e' | e' <;> linarith
    have hL : DirichletCharacter.LFunction χ s ≠ 0 := by
      intro h0
      rcases hZ N χ hχ s (by linarith [hs'.1.1]) hs1 h0 with h | ⟨h, -⟩ | ⟨h, -⟩
      · rcases hside with e | e | e | e
        · linarith [h.1]
        · linarith [h.2]
        · exact hno s h.1 h.2 h0 (by rw [e, abs_neg, abs_of_pos (by linarith)])
        · exact hno s h.1 h.2 h0 (by rw [e, abs_of_pos (by linarith)])
      · have r1 : s.re = 0 := by rw [h]; simp
        have i1 : s.im = 0 := by rw [h]; simp
        rcases hside with e' | e' | e' | e' <;> linarith
      · have r1 : s.re = -1 := by rw [h]; simp
        have i1 : s.im = 0 := by rw [h]; simp
        rcases hside with e' | e' | e' | e' <;> linarith
    rw [hreg.2 s hs hL hs1, hfs]
    have := hsumZ (fun w ρ => w / (s - ρ))
    rw [this]
    ring
  rw [hbd, hR (-1 / 2) (cLine u) (-T') T' H Z wt (eps0 χ) u (by linarith) (by norm_num) (by linarith)
    (by linarith) (by linarith) hreg.1 ?_]
  · have := hsumZ (fun w ρ => w * (((u : ℂ) ^ ρ - 1) / ρ))
    rw [this, zsum, hfs, hfs, Complex.cpow_one]
    have e : ∑ ρ ∈ S, (mult χ ρ : ℂ) * (((u : ℂ) ^ ρ - 1) / ρ) =
        ∑ ρ ∈ S, (mult χ ρ : ℂ) * ((u : ℂ) ^ ρ / ρ) - ∑ ρ ∈ S, (mult χ ρ : ℂ) / ρ := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun ρ _ => by ring
    rw [e]
    ring
  · intro ρ hρ
    rw [hZdef, Finset.mem_insert] at hρ
    rcases hρ with e | hρ
    · subst e
      simp only [Complex.one_re, Complex.one_im]
      exact ⟨one_ne_zero, by norm_num, hc, by linarith, by linarith⟩
    · obtain ⟨h0, h1, him, -⟩ := (hmemS ρ).1 hρ
      rw [abs_lt] at him
      refine ⟨fun e => by rw [e] at h0; simp at h0, by linarith, by linarith, him.1, him.2⟩

end PI.EF
