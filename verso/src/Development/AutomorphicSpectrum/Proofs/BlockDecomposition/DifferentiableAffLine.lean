import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire

noncomputable section

open Filter Topology PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.RgEisGal

def aff (α β γ : ℝ) (l : ℂ × ℂ) : ℂ := (α : ℂ) * l.1 + (β : ℂ) * l.2 + (γ : ℂ)

def affR (α β γ : ℝ) (x : ℝ × ℝ) : ℝ := α * x.1 + β * x.2 + γ

def chg (α₁ β₁ γ₁ α₂ β₂ γ₂ : ℝ) (l : ℂ × ℂ) : ℂ × ℂ := (aff α₁ β₁ γ₁ l, aff α₂ β₂ γ₂ l)

def chgR (α₁ β₁ γ₁ α₂ β₂ γ₂ : ℝ) (x : ℝ × ℝ) : ℝ × ℝ := (affR α₁ β₁ γ₁ x, affR α₂ β₂ γ₂ x)

/- English proof (translation)
Simplify using `[aff, affR]`.
-/
lemma aff_re (α β γ : ℝ) (l : ℂ × ℂ) : (aff α β γ l).re = affR α β γ (l.1.re, l.2.re) := by
  simp [aff, affR]

/- English proof (translation)
Simplify using `only [aff, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma aff_line (α β γ : ℝ) (p v : ℂ × ℂ) (τ : ℂ) :
    aff α β γ (p + τ • v) = aff α β γ p + τ * ((α : ℂ) * v.1 + (β : ℂ) * v.2) := by
  simp only [aff, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/- English proof (translation)
Unfold `aff`. Use `fun_prop`.
-/
lemma continuous_aff (α β γ : ℝ) : Continuous (aff α β γ) := by
  unfold aff; fun_prop

/- English proof (translation)
Unfold `affR`. Use `fun_prop`.
-/
lemma continuous_affR (α β γ : ℝ) : Continuous (affR α β γ) := by
  unfold affR; fun_prop

/- English proof (translation)
The claim follows from `(continuous_aff _ _ _).prodMk (continuous_aff _ _ _)`.
-/
lemma continuous_chg (α₁ β₁ γ₁ α₂ β₂ γ₂ : ℝ) : Continuous (chg α₁ β₁ γ₁ α₂ β₂ γ₂) :=
  (continuous_aff _ _ _).prodMk (continuous_aff _ _ _)

/- English proof (translation)
The claim follows from `(continuous_affR _ _ _).prodMk (continuous_affR _ _ _)`.
-/
lemma continuous_chgR (α₁ β₁ γ₁ α₂ β₂ γ₂ : ℝ) : Continuous (chgR α₁ β₁ γ₁ α₂ β₂ γ₂) :=
  (continuous_affR _ _ _).prodMk (continuous_affR _ _ _)

/- English proof (translation)
Simplify using `only [aff_line]`. Use `fun_prop`.
-/
lemma differentiable_aff_line (α β γ : ℝ) (p v : ℂ × ℂ) :
    Differentiable ℂ fun τ : ℂ => aff α β γ (p + τ • v) := by
  simp only [aff_line]
  fun_prop

/- English proof (translation)
Simplify using `only [tube, Set.mem_setOf_eq, Set.mem_preimage, chg, chgR, aff_re]`.
-/
lemma mem_tube_chg {Ω : Set (ℝ × ℝ)} {α₁ β₁ γ₁ α₂ β₂ γ₂ : ℝ} {l : ℂ × ℂ} :
    l ∈ tube (chgR α₁ β₁ γ₁ α₂ β₂ γ₂ ⁻¹' Ω) ↔ chg α₁ β₁ γ₁ α₂ β₂ γ₂ l ∈ tube Ω := by
  simp only [tube, Set.mem_setOf_eq, Set.mem_preimage, chg, chgR, aff_re]

/- English proof (translation)
Simplify using `only [chg, aff_line]`. Both sides reduce to the same expression.
-/
lemma chg_line (α₁ β₁ γ₁ α₂ β₂ γ₂ : ℝ) (p v : ℂ × ℂ) (τ : ℂ) :
    chg α₁ β₁ γ₁ α₂ β₂ γ₂ (p + τ • v) = chg α₁ β₁ γ₁ α₂ β₂ γ₂ p +
      τ • ((α₁ : ℂ) * v.1 + (β₁ : ℂ) * v.2, (α₂ : ℂ) * v.1 + (β₂ : ℂ) * v.2) := by
  simp only [chg, aff_line]
  rfl

section Good

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

/- English proof (translation)
Introduce `p v`. Establish `h` using `hF (chg α₁ β₁ γ₁ α₂ β₂ γ₂ p) ((α₁ : ℂ) * v.1 + (β₁ : ℂ) * v.2, (α₂ : ℂ) * v.1 + (β₂ : ℂ) * v.2)`. Simplify using `only [mem_tube_chg, chg_line]`. Conclude with `h`.
-/
lemma lineHol_chg {F : ℂ × ℂ → X} {Ω : Set (ℝ × ℝ)} (hF : LineHol F (tube Ω))
    (α₁ β₁ γ₁ α₂ β₂ γ₂ : ℝ) :
    LineHol (fun l => F (chg α₁ β₁ γ₁ α₂ β₂ γ₂ l)) (tube (chgR α₁ β₁ γ₁ α₂ β₂ γ₂ ⁻¹' Ω)) := by
  intro p v
  have h := hF (chg α₁ β₁ γ₁ α₂ β₂ γ₂ p)
    ((α₁ : ℂ) * v.1 + (β₁ : ℂ) * v.2, (α₂ : ℂ) * v.1 + (β₂ : ℂ) * v.2)
  simp only [mem_tube_chg, chg_line]
  exact h

/- English proof (translation)
Use `⟨fun g => lineHol_chg (hF.hol g) _ _ _ _ _ _, ?_, ?_⟩` and prove the remaining obligations. Establish `hc : Continuous fun y : (ℂ × ℂ) × T => (chg α₁ β₁ γ₁ α₂ β₂ γ₂ y.1, y.2)` using `((continuous_chg _ _ _ _ _ _).comp continuous_fst).prodMk continuous_snd`. Use `hF.cont.comp hc.continuousOn ?_` and prove the remaining obligations. Introduce and unpack `⟨l, g⟩ ⟨hl, -⟩`. Conclude with `⟨mem_tube_chg.1 hl, Set.mem_univ _⟩`.

Introduce `C hC hCc g`. Take `⟨U, hU, M, hM⟩` from `hF.bdd (chgR α₁ β₁ γ₁ α₂ β₂ γ₂ '' C) (by rintro _ ⟨x, hx, rfl⟩; exact hC hx) (hCc.image (continuous_chgR _ _ _ _ _ _)) g`. Use `⟨U, hU, M, fun l hl g' hg' => hM _ ?_ g' hg'⟩` and prove the remaining obligations. Establish `: (l.1.re, l.2.re) ∈ C` using `hl`. Use `⟨_, this, ?_⟩` and prove the remaining obligations.

Simplify using `only [chg, chgR, aff_re]`.
-/
theorem TubeGood_chg {T : Type} [TopologicalSpace T] {F : ℂ × ℂ → T → X} {Ω : Set (ℝ × ℝ)}
    (hF : TubeGood F Ω) (α₁ β₁ γ₁ α₂ β₂ γ₂ : ℝ) :
    TubeGood (fun l g => F (chg α₁ β₁ γ₁ α₂ β₂ γ₂ l) g) (chgR α₁ β₁ γ₁ α₂ β₂ γ₂ ⁻¹' Ω) := by
  refine ⟨fun g => lineHol_chg (hF.hol g) _ _ _ _ _ _, ?_, ?_⟩
  · have hc : Continuous fun y : (ℂ × ℂ) × T => (chg α₁ β₁ γ₁ α₂ β₂ γ₂ y.1, y.2) :=
      ((continuous_chg _ _ _ _ _ _).comp continuous_fst).prodMk continuous_snd
    refine hF.cont.comp hc.continuousOn ?_
    rintro ⟨l, g⟩ ⟨hl, -⟩
    exact ⟨mem_tube_chg.1 hl, Set.mem_univ _⟩
  · intro C hC hCc g
    obtain ⟨U, hU, M, hM⟩ := hF.bdd (chgR α₁ β₁ γ₁ α₂ β₂ γ₂ '' C)
      (by rintro _ ⟨x, hx, rfl⟩; exact hC hx) (hCc.image (continuous_chgR _ _ _ _ _ _)) g
    refine ⟨U, hU, M, fun l hl g' hg' => hM _ ?_ g' hg'⟩
    have : (l.1.re, l.2.re) ∈ C := hl
    refine ⟨_, this, ?_⟩
    simp only [chg, chgR, aff_re]

/- English proof (translation)
Establish `ht : tube Ω' ⊆ tube Ω` using `fun l hl => h hl`. Use `⟨fun g p v => ?_, hF.cont.mono (Set.prod_mono ht subset_rfl), fun C hC => hF.bdd C (hC.trans h)⟩` and prove the remaining obligations. Conclude with `(hF.hol g p v).mono fun τ hτ => ht hτ`.
-/
lemma TubeGood_mono {T : Type} [TopologicalSpace T] {F : ℂ × ℂ → T → X} {Ω Ω' : Set (ℝ × ℝ)}
    (hF : TubeGood F Ω) (h : Ω' ⊆ Ω) : TubeGood F Ω' := by
  have ht : tube Ω' ⊆ tube Ω := fun l hl => h hl
  refine ⟨fun g p v => ?_, hF.cont.mono (Set.prod_mono ht subset_rfl),
    fun C hC => hF.bdd C (hC.trans h)⟩
  exact (hF.hol g p v).mono fun τ hτ => ht hτ

structure Fac (A : ℂ × ℂ → X) (Ω : Set (ℝ × ℝ)) : Prop where
  hol : LineHol A (tube Ω)
  cont : ContinuousOn A (tube Ω)
  bdd : ∀ C ⊆ Ω, IsCompact C → ∃ M : ℝ, ∀ l ∈ tube C, ‖A l‖ ≤ M

/- English proof (translation)
Take `⟨x, hx, hx'⟩` from `hC.exists_isMinOn hne hf.continuousOn`. Take `⟨y, hy, hy'⟩` from `hC.exists_isMaxOn hne hf.continuousOn`. Conclude with `⟨x, hx, y, hy, fun u hu => ⟨hx' hu, hy' hu⟩⟩`.
-/
lemma exists_bounds {C : Set (ℝ × ℝ)} (hC : IsCompact C) (hne : C.Nonempty) (f : ℝ × ℝ → ℝ)
    (hf : Continuous f) : ∃ x ∈ C, ∃ y ∈ C, ∀ u ∈ C, f x ≤ f u ∧ f u ≤ f y := by
  obtain ⟨x, hx, hx'⟩ := hC.exists_isMinOn hne hf.continuousOn
  obtain ⟨y, hy, hy'⟩ := hC.exists_isMaxOn hne hf.continuousOn
  exact ⟨x, hx, y, hy, fun u hu => ⟨hx' hu, hy' hu⟩⟩

/- English proof (translation)
Establish `hre : ∀ l ∈ tube Ω, (aff α β γ l).re < a` using `fun l hl => by`. Rewrite using `[aff_re]`. Conclude with `h _ hl`. Use `⟨fun p v => ?_, ?_, fun C hC hCc => ?_⟩` and prove the remaining obligations. Use `hf.1.comp (differentiable_aff_line α β γ p v).differentiableOn ?_` and prove the remaining obligations.

Introduce `τ hτ`. Conclude with `hre _ hτ`. Conclude with `hf.1.continuousOn.comp (continuous_aff _ _ _).continuousOn fun l hl => hre l hl`. Break down `C.eq_empty_or_nonempty with rfl | hne` into its components or cases. Conclude with `⟨0, fun l hl => hl.elim⟩`.

Take `⟨x, -, y, hy, hxy⟩` from `exists_bounds hCc hne _ (continuous_affR α β γ)`. Take `⟨M, hM⟩` from `hf.2 (affR α β γ x) (affR α β γ y) (h y (hC hy))`. Use `⟨M, fun l hl => hM _ ?_ ?_⟩` and prove the remaining obligations. Rewrite using `[aff_re]`. Conclude with `(hxy _ hl).1`.

Rewrite using `[aff_re]`. Conclude with `(hxy _ hl).2`.
-/
theorem Fac_left {f : ℂ → X} {a : ℝ} (hf : LeftGood f a) (α β γ : ℝ) {Ω : Set (ℝ × ℝ)}
    (h : ∀ x ∈ Ω, affR α β γ x < a) : Fac (fun l => f (aff α β γ l)) Ω := by
  have hre : ∀ l ∈ tube Ω, (aff α β γ l).re < a := fun l hl => by
    rw [aff_re]; exact h _ hl
  refine ⟨fun p v => ?_, ?_, fun C hC hCc => ?_⟩
  · refine hf.1.comp (differentiable_aff_line α β γ p v).differentiableOn ?_
    intro τ hτ
    exact hre _ hτ
  · exact hf.1.continuousOn.comp (continuous_aff _ _ _).continuousOn fun l hl => hre l hl
  · rcases C.eq_empty_or_nonempty with rfl | hne
    · exact ⟨0, fun l hl => hl.elim⟩
    · obtain ⟨x, -, y, hy, hxy⟩ := exists_bounds hCc hne _ (continuous_affR α β γ)
      obtain ⟨M, hM⟩ := hf.2 (affR α β γ x) (affR α β γ y) (h y (hC hy))
      refine ⟨M, fun l hl => hM _ ?_ ?_⟩
      · rw [aff_re]; exact (hxy _ hl).1
      · rw [aff_re]; exact (hxy _ hl).2

/- English proof (translation)
Use `⟨fun p v => ?_, ?_, fun C _ hCc => ?_⟩` and prove the remaining obligations. Conclude with `(hf.1.comp (differentiable_aff_line α β γ p v)).differentiableOn`. Conclude with `(hf.1.continuous.comp (continuous_aff _ _ _)).continuousOn`. Break down `C.eq_empty_or_nonempty with rfl | hne` into its components or cases. Conclude with `⟨0, fun l hl => hl.elim⟩`.

Take `⟨x, -, y, -, hxy⟩` from `exists_bounds hCc hne _ (continuous_affR α β γ)`. Take `⟨M, hM⟩` from `hf.2 (affR α β γ x) (affR α β γ y)`. Use `⟨M, fun l hl => hM _ ?_ ?_⟩` and prove the remaining obligations. Rewrite using `[aff_re]`. Conclude with `(hxy _ hl).1`.

Rewrite using `[aff_re]`. Conclude with `(hxy _ hl).2`.
-/
theorem Fac_strip {f : ℂ → X} (hf : StripEntire f) (α β γ : ℝ) (Ω : Set (ℝ × ℝ)) :
    Fac (fun l => f (aff α β γ l)) Ω := by
  refine ⟨fun p v => ?_, ?_, fun C _ hCc => ?_⟩
  · exact (hf.1.comp (differentiable_aff_line α β γ p v)).differentiableOn
  · exact (hf.1.continuous.comp (continuous_aff _ _ _)).continuousOn
  · rcases C.eq_empty_or_nonempty with rfl | hne
    · exact ⟨0, fun l hl => hl.elim⟩
    · obtain ⟨x, -, y, -, hxy⟩ := exists_bounds hCc hne _ (continuous_affR α β γ)
      obtain ⟨M, hM⟩ := hf.2 (affR α β γ x) (affR α β γ y)
      refine ⟨M, fun l hl => hM _ ?_ ?_⟩
      · rw [aff_re]; exact (hxy _ hl).1
      · rw [aff_re]; exact (hxy _ hl).2

/- English proof (translation)
Establish `ht : tube Ω' ⊆ tube Ω` using `fun l hl => h hl`. Conclude with `⟨fun p v => (hA.hol p v).mono fun τ hτ => ht hτ, hA.cont.mono ht, fun C hC => hA.bdd C (hC.trans h)⟩`.
-/
lemma Fac_mono {A : ℂ × ℂ → X} {Ω Ω' : Set (ℝ × ℝ)} (hA : Fac A Ω) (h : Ω' ⊆ Ω) : Fac A Ω' := by
  have ht : tube Ω' ⊆ tube Ω := fun l hl => h hl
  exact ⟨fun p v => (hA.hol p v).mono fun τ hτ => ht hτ, hA.cont.mono ht,
    fun C hC => hA.bdd C (hC.trans h)⟩

/- English proof (translation)
Use `⟨fun p v => (hf.hol p v).smul (hA.hol p v), hf.cont.smul hA.cont, fun C hC hCc => ?_⟩` and prove the remaining obligations. Take `⟨M₁, h₁⟩` from `hf.bdd C hC hCc`. Take `⟨M₂, h₂⟩` from `hA.bdd C hC hCc`. Use `⟨|M₁| * |M₂|, fun l hl => ?_⟩` and prove the remaining obligations. Rewrite using `[norm_smul]`.

Conclude with `mul_le_mul ((h₁ l hl).trans (le_abs_self _)) ((h₂ l hl).trans (le_abs_self _)) (norm_nonneg _) (abs_nonneg _)`.
-/
theorem Fac_smul {f : ℂ × ℂ → ℂ} {A : ℂ × ℂ → X} {Ω : Set (ℝ × ℝ)} (hf : Fac f Ω) (hA : Fac A Ω) :
    Fac (fun l => f l • A l) Ω := by
  refine ⟨fun p v => (hf.hol p v).smul (hA.hol p v), hf.cont.smul hA.cont, fun C hC hCc => ?_⟩
  obtain ⟨M₁, h₁⟩ := hf.bdd C hC hCc
  obtain ⟨M₂, h₂⟩ := hA.bdd C hC hCc
  refine ⟨|M₁| * |M₂|, fun l hl => ?_⟩
  rw [norm_smul]
  exact mul_le_mul ((h₁ l hl).trans (le_abs_self _)) ((h₂ l hl).trans (le_abs_self _))
    (norm_nonneg _) (abs_nonneg _)

/- English proof (translation)
The claim follows from `Fac_smul hf hf'`.
-/
theorem Fac_mul {f f' : ℂ × ℂ → ℂ} {Ω : Set (ℝ × ℝ)} (hf : Fac f Ω) (hf' : Fac f' Ω) :
    Fac (fun l => f l * f' l) Ω :=
  Fac_smul hf hf'

/- English proof (translation)
Use `⟨fun g p v => (hf.hol p v).smul (hF.hol g p v), ?_, fun C hC hCc g => ?_⟩` and prove the remaining obligations. Use `ContinuousOn.smul (hf.cont.comp continuousOn_fst ?_) hF.cont` and prove the remaining obligations. Introduce and unpack `⟨l, g⟩ ⟨hl, -⟩`. Conclude with `hl`. Take `⟨M₁, h₁⟩` from `hf.bdd C hC hCc`.

Take `⟨U, hU, M₂, h₂⟩` from `hF.bdd C hC hCc g`. Use `⟨U, hU, |M₁| * |M₂|, fun l hl g' hg' => ?_⟩` and prove the remaining obligations. Rewrite using `[norm_smul]`. Conclude with `mul_le_mul ((h₁ l hl).trans (le_abs_self _)) ((h₂ l hl g' hg').trans (le_abs_self _)) (norm_nonneg _) (abs_nonneg _)`.
-/
theorem TubeGood_smul {T : Type} [TopologicalSpace T] {F : ℂ × ℂ → T → X} {Ω : Set (ℝ × ℝ)}
    {f : ℂ × ℂ → ℂ} (hf : Fac f Ω) (hF : TubeGood F Ω) :
    TubeGood (fun l g => f l • F l g) Ω := by
  refine ⟨fun g p v => (hf.hol p v).smul (hF.hol g p v), ?_, fun C hC hCc g => ?_⟩
  · refine ContinuousOn.smul (hf.cont.comp continuousOn_fst ?_) hF.cont
    rintro ⟨l, g⟩ ⟨hl, -⟩
    exact hl
  · obtain ⟨M₁, h₁⟩ := hf.bdd C hC hCc
    obtain ⟨U, hU, M₂, h₂⟩ := hF.bdd C hC hCc g
    refine ⟨U, hU, |M₁| * |M₂|, fun l hl g' hg' => ?_⟩
    rw [norm_smul]
    exact mul_le_mul ((h₁ l hl).trans (le_abs_self _)) ((h₂ l hl g' hg').trans (le_abs_self _))
      (norm_nonneg _) (abs_nonneg _)

end Good

section Comp

variable {E₁ E₂ E₃ : Type} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [NormedAddCommGroup E₂]
  [NormedSpace ℂ E₂] [NormedAddCommGroup E₃] [NormedSpace ℂ E₃]

/- English proof (translation)
Use `⟨fun p v => (hA.hol p v).clm_comp (hB.hol p v), hA.cont.clm_comp hB.cont, fun C hC hCc => ?_⟩` and prove the remaining obligations. Take `⟨M₁, h₁⟩` from `hA.bdd C hC hCc`. Take `⟨M₂, h₂⟩` from `hB.bdd C hC hCc`. Use `⟨|M₁| * |M₂|, fun l hl => (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_⟩` and prove the remaining obligations. Conclude with `mul_le_mul ((h₁ l hl).trans (le_abs_self _)) ((h₂ l hl).trans (le_abs_self _)) (norm_nonneg _) (abs_nonneg _)`.
-/
theorem Fac_comp {A : ℂ × ℂ → E₂ →L[ℂ] E₃} {B : ℂ × ℂ → E₁ →L[ℂ] E₂} {Ω : Set (ℝ × ℝ)}
    (hA : Fac A Ω) (hB : Fac B Ω) : Fac (fun l => (A l).comp (B l)) Ω := by
  refine ⟨fun p v => (hA.hol p v).clm_comp (hB.hol p v), hA.cont.clm_comp hB.cont,
    fun C hC hCc => ?_⟩
  obtain ⟨M₁, h₁⟩ := hA.bdd C hC hCc
  obtain ⟨M₂, h₂⟩ := hB.bdd C hC hCc
  refine ⟨|M₁| * |M₂|, fun l hl => (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_⟩
  exact mul_le_mul ((h₁ l hl).trans (le_abs_self _)) ((h₂ l hl).trans (le_abs_self _))
    (norm_nonneg _) (abs_nonneg _)

/- English proof (translation)
Use `⟨fun g p v => (hF.hol g p v).clm_comp (hA.hol p v), ?_, fun C hC hCc g => ?_⟩` and prove the remaining obligations. Use `ContinuousOn.clm_comp hF.cont (hA.cont.comp continuousOn_fst ?_)` and prove the remaining obligations. Introduce and unpack `⟨l, g⟩ ⟨hl, -⟩`. Conclude with `hl`. Take `⟨U, hU, M₁, h₁⟩` from `hF.bdd C hC hCc g`.

Take `⟨M₂, h₂⟩` from `hA.bdd C hC hCc`. Use `⟨U, hU, |M₁| * |M₂|, fun l hl g' hg' => (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_⟩` and prove the remaining obligations. Conclude with `mul_le_mul ((h₁ l hl g' hg').trans (le_abs_self _)) ((h₂ l hl).trans (le_abs_self _)) (norm_nonneg _) (abs_nonneg _)`.
-/
theorem TubeGood_comp {T : Type} [TopologicalSpace T] {F : ℂ × ℂ → T → E₂ →L[ℂ] E₃}
    {A : ℂ × ℂ → E₁ →L[ℂ] E₂} {Ω : Set (ℝ × ℝ)} (hF : TubeGood F Ω) (hA : Fac A Ω) :
    TubeGood (fun l g => (F l g).comp (A l)) Ω := by
  refine ⟨fun g p v => (hF.hol g p v).clm_comp (hA.hol p v), ?_, fun C hC hCc g => ?_⟩
  · refine ContinuousOn.clm_comp hF.cont (hA.cont.comp continuousOn_fst ?_)
    rintro ⟨l, g⟩ ⟨hl, -⟩
    exact hl
  · obtain ⟨U, hU, M₁, h₁⟩ := hF.bdd C hC hCc g
    obtain ⟨M₂, h₂⟩ := hA.bdd C hC hCc
    refine ⟨U, hU, |M₁| * |M₂|, fun l hl g' hg' =>
      (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_⟩
    exact mul_le_mul ((h₁ l hl g' hg').trans (le_abs_self _)) ((h₂ l hl).trans (le_abs_self _))
      (norm_nonneg _) (abs_nonneg _)

end Comp

end GlobalTheory.CompanionTheory.RgEisGal
