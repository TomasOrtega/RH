import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyAbs
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.SchurTensRep

noncomputable section

open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.S.Pv.SchurTens

open Formalism.L2.SG.Pf.EnergyAbs

section Gen

variable {K : Type*} [MeasurableSpace K] {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]

def SP (m : Measure K) (σs : K → (Hs →L[ℂ] Hs)) (D : ℝ) (a b a' b' : Hs) : Prop :=
  Integrable (fun x => ⟪b, σs x a⟫_ℂ * conj ⟪b', σs x a'⟫_ℂ) m ∧
    ∫ x, ⟪b, σs x a⟫_ℂ * conj ⟪b', σs x a'⟫_ℂ ∂m = ⟪a', a⟫_ℂ * ⟪b, b'⟫_ℂ / (D : ℂ)

variable {m : Measure K} {σs : K → (Hs →L[ℂ] Hs)} {D : ℝ}

/- English proof (translation)
Conclude with `hf.mono (Complex.continuous_conj.comp_aestronglyMeasurable hf.aestronglyMeasurable) (ae_of_all _ fun x => by simp)`.
-/
theorem integrable_conj' {f : K → ℂ} (hf : Integrable f m) : Integrable (fun x => conj (f x)) m := by
  exact hf.mono (Complex.continuous_conj.comp_aestronglyMeasurable hf.aestronglyMeasurable)
    (ae_of_all _ fun x => by simp)

/- English proof (translation)
Unfold `SP at h ⊢`. Establish `e : (fun x => ⟪b', σs x a'⟫_ℂ * conj ⟪b, σs x a⟫_ℂ) = fun x => conj (⟪b, σs x a⟫_ℂ * conj ⟪b', σs x a'⟫_ℂ)`. Use function extensionality and compare the values at `x`. Rewrite using `[map_mul, Complex.conj_conj]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Use `⟨integrable_conj' h.1, ?_⟩` and prove the remaining obligations. Rewrite using `[integral_conj, h.2]`. Rewrite using `[map_div₀, map_mul, Complex.conj_ofReal, inner_conj_symm, inner_conj_symm]`.
-/
theorem SP_swap {a b a' b' : Hs} (h : SP m σs D a b a' b') : SP m σs D a' b' a b := by
  unfold SP at h ⊢
  have e : (fun x => ⟪b', σs x a'⟫_ℂ * conj ⟪b, σs x a⟫_ℂ) =
      fun x => conj (⟪b, σs x a⟫_ℂ * conj ⟪b', σs x a'⟫_ℂ) := by
    funext x
    rw [map_mul, Complex.conj_conj]
    ring
  rw [e]
  refine ⟨integrable_conj' h.1, ?_⟩
  rw [integral_conj, h.2]
  rw [map_div₀, map_mul, Complex.conj_ofReal, inner_conj_symm, inner_conj_symm]

/- English proof (translation)
Unfold `SP`. Simplify using the standard rewrite rules.
-/
theorem SP_zero_a (b a' b' : Hs) : SP m σs D 0 b a' b' := by
  unfold SP
  simp

/- English proof (translation)
Unfold `SP at h₁ h₂ ⊢`. Establish `e : (fun x => ⟪b, σs x (a₁ + a₂)⟫_ℂ * conj ⟪b', σs x a'⟫_ℂ) = fun x => ⟪b, σs x a₁⟫_ℂ * conj ⟪b', σs x a'⟫_ℂ + ⟪b, σs x a₂⟫_ℂ * conj ⟪b', σs x a'⟫_ℂ`. Use function extensionality and compare the values at `x`. Rewrite using `[map_add, inner_add_right, add_mul]`. Rewrite using `[e]`.

Use `⟨h₁.1.add h₂.1, ?_⟩` and prove the remaining obligations. Rewrite using `[integral_add h₁.1 h₂.1, h₁.2, h₂.2, inner_add_right]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem SP_add_a {a₁ a₂ b a' b' : Hs} (h₁ : SP m σs D a₁ b a' b') (h₂ : SP m σs D a₂ b a' b') :
    SP m σs D (a₁ + a₂) b a' b' := by
  unfold SP at h₁ h₂ ⊢
  have e : (fun x => ⟪b, σs x (a₁ + a₂)⟫_ℂ * conj ⟪b', σs x a'⟫_ℂ) =
      fun x => ⟪b, σs x a₁⟫_ℂ * conj ⟪b', σs x a'⟫_ℂ + ⟪b, σs x a₂⟫_ℂ * conj ⟪b', σs x a'⟫_ℂ := by
    funext x
    rw [map_add, inner_add_right, add_mul]
  rw [e]
  refine ⟨h₁.1.add h₂.1, ?_⟩
  rw [integral_add h₁.1 h₂.1, h₁.2, h₂.2, inner_add_right]
  ring

/- English proof (translation)
Unfold `SP at h ⊢`. Establish `e : (fun x => ⟪b, σs x (c • a)⟫_ℂ * conj ⟪b', σs x a'⟫_ℂ) = fun x => c * (⟪b, σs x a⟫_ℂ * conj ⟪b', σs x a'⟫_ℂ)`. Use function extensionality and compare the values at `x`. Rewrite using `[map_smul, inner_smul_right, mul_assoc]`. Rewrite using `[e]`.

Use `⟨h.1.const_mul c, ?_⟩` and prove the remaining obligations. Rewrite using `[integral_const_mul]`. Rewrite using `[h.2, inner_smul_right]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem SP_smul_a (c : ℂ) {a b a' b' : Hs} (h : SP m σs D a b a' b') : SP m σs D (c • a) b a' b' := by
  unfold SP at h ⊢
  have e : (fun x => ⟪b, σs x (c • a)⟫_ℂ * conj ⟪b', σs x a'⟫_ℂ) =
      fun x => c * (⟪b, σs x a⟫_ℂ * conj ⟪b', σs x a'⟫_ℂ) := by
    funext x
    rw [map_smul, inner_smul_right, mul_assoc]
  rw [e]
  refine ⟨h.1.const_mul c, ?_⟩
  rw [integral_const_mul]
  rw [h.2, inner_smul_right]
  ring

/- English proof (translation)
Unfold `SP`. Simplify using the standard rewrite rules.
-/
theorem SP_zero_b (a a' b' : Hs) : SP m σs D a 0 a' b' := by
  unfold SP
  simp

/- English proof (translation)
Unfold `SP at h₁ h₂ ⊢`. Establish `e : (fun x => ⟪b₁ + b₂, σs x a⟫_ℂ * conj ⟪b', σs x a'⟫_ℂ) = fun x => ⟪b₁, σs x a⟫_ℂ * conj ⟪b', σs x a'⟫_ℂ + ⟪b₂, σs x a⟫_ℂ * conj ⟪b', σs x a'⟫_ℂ`. Use function extensionality and compare the values at `x`. Rewrite using `[inner_add_left, add_mul]`. Rewrite using `[e]`.

Use `⟨h₁.1.add h₂.1, ?_⟩` and prove the remaining obligations. Rewrite using `[integral_add h₁.1 h₂.1, h₁.2, h₂.2, inner_add_left]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem SP_add_b {a b₁ b₂ a' b' : Hs} (h₁ : SP m σs D a b₁ a' b') (h₂ : SP m σs D a b₂ a' b') :
    SP m σs D a (b₁ + b₂) a' b' := by
  unfold SP at h₁ h₂ ⊢
  have e : (fun x => ⟪b₁ + b₂, σs x a⟫_ℂ * conj ⟪b', σs x a'⟫_ℂ) =
      fun x => ⟪b₁, σs x a⟫_ℂ * conj ⟪b', σs x a'⟫_ℂ + ⟪b₂, σs x a⟫_ℂ * conj ⟪b', σs x a'⟫_ℂ := by
    funext x
    rw [inner_add_left, add_mul]
  rw [e]
  refine ⟨h₁.1.add h₂.1, ?_⟩
  rw [integral_add h₁.1 h₂.1, h₁.2, h₂.2, inner_add_left]
  ring

/- English proof (translation)
Unfold `SP at h ⊢`. Establish `e : (fun x => ⟪c • b, σs x a⟫_ℂ * conj ⟪b', σs x a'⟫_ℂ) = fun x => conj c * (⟪b, σs x a⟫_ℂ * conj ⟪b', σs x a'⟫_ℂ)`. Use function extensionality and compare the values at `x`. Rewrite using `[inner_smul_left, mul_assoc]`. Rewrite using `[e]`.

Use `⟨h.1.const_mul _, ?_⟩` and prove the remaining obligations. Rewrite using `[integral_const_mul]`. Rewrite using `[h.2, inner_smul_left]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem SP_smul_b (c : ℂ) {a b a' b' : Hs} (h : SP m σs D a b a' b') : SP m σs D a (c • b) a' b' := by
  unfold SP at h ⊢
  have e : (fun x => ⟪c • b, σs x a⟫_ℂ * conj ⟪b', σs x a'⟫_ℂ) =
      fun x => conj c * (⟪b, σs x a⟫_ℂ * conj ⟪b', σs x a'⟫_ℂ) := by
    funext x
    rw [inner_smul_left, mul_assoc]
  rw [e]
  refine ⟨h.1.const_mul _, ?_⟩
  rw [integral_const_mul]
  rw [h.2, inner_smul_left]
  ring

/- English proof (translation)
Introduce `a ha`. Set `S : Submodule ℂ Hs` to `{ carrier := {x | P x} add_mem' := fun {x y} hx hy => hadd x y hx hy zero_mem' := h0 smul_mem' := fun c {x} hx => hsmul c x hx }`. Establish `hle : Submodule.span ℂ E ≤ S` using `Submodule.span_le.mpr fun x hx => hE x hx`. Conclude with `hle ha`.
-/
private theorem mem_span_of_closed_lemma {P : Hs → Prop} (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (hsmul : ∀ (c : ℂ) x, P x → P (c • x)) {E : Set Hs} (hE : ∀ a ∈ E, P a) :
    ∀ a ∈ Submodule.span ℂ E, P a := by
  intro a ha
  let S : Submodule ℂ Hs :=
    { carrier := {x | P x}
      add_mem' := fun {x y} hx hy => hadd x y hx hy
      zero_mem' := h0
      smul_mem' := fun c {x} hx => hsmul c x hx }
  have hle : Submodule.span ℂ E ≤ S := Submodule.span_le.mpr fun x hx => hE x hx
  exact hle ha

/- English proof (translation)
Establish `s1 : ∀ a ∈ Submodule.span ℂ E, ∀ b ∈ E, ∀ a' ∈ E, ∀ b' ∈ E, SP m σs D a b a' b'` using `mem_span_of_closed_lemma (P := fun a => ∀ b ∈ E, ∀ a' ∈ E, ∀ b' ∈ E, SP m σs D a b a' b') (fun b _ a' _ b' _ => SP_zero_a b a' b') (fun x y hx hy b hb a' ha' b' hb' => SP_add_a (hx b hb a' ha' b' hb') (hy b hb a' ha' b' hb')) (fun c x hx b hb a' ha' b' hb' => SP_smul_a c (hx b hb …`. Establish `s2 : ∀ a ∈ Submodule.span ℂ E, ∀ b ∈ Submodule.span ℂ E, ∀ a' ∈ E, ∀ b' ∈ E, SP m σs D a b a' b'`. Introduce `a ha`. Conclude with `mem_span_of_closed_lemma (P := fun b => ∀ a' ∈ E, ∀ b' ∈ E, SP m σs D a b a' b') (fun a' _ b' _ => SP_zero_b a a' b') (fun x y hx hy a' ha' b' hb' => SP_add_b (hx a' ha' b' hb') (hy a' ha' b' hb')) (fun c x hx a' ha' b' hb' => SP_smul_b c (hx a' ha' b' hb')) (fun b hb => s1 a ha …`. Establish `s3 : ∀ a' ∈ Submodule.span ℂ E, ∀ b' ∈ E, ∀ a ∈ Submodule.span ℂ E, ∀ b ∈ Submodule.span ℂ E, SP m σs D a' b' a b` using `mem_span_of_closed_lemma (P := fun a' => ∀ b' ∈ E, ∀ a ∈ Submodule.span ℂ E, ∀ b ∈ Submodule.span ℂ E, SP m σs D a' b' a b) (fun b' _ a _ b _ => SP_zero_a b' a b) (fun x y hx hy b' hb' a ha b hb => SP_add_a (hx b' hb' a ha b hb) (hy b' hb' a ha b hb)) (fun c x hx b' hb' a ha b hb …`.

Establish `s4 : ∀ a' ∈ Submodule.span ℂ E, ∀ b' ∈ Submodule.span ℂ E, ∀ a ∈ Submodule.span ℂ E, ∀ b ∈ Submodule.span ℂ E, SP m σs D a' b' a b`. Introduce `a' ha'`. Conclude with `mem_span_of_closed_lemma (P := fun b' => ∀ a ∈ Submodule.span ℂ E, ∀ b ∈ Submodule.span ℂ E, SP m σs D a' b' a b) (fun a _ b _ => SP_zero_b a' a b) (fun x y hx hy a ha b hb => SP_add_b (hx a ha b hb) (hy a ha b hb)) (fun c x hx a ha b hb => SP_smul_b c (hx a ha b hb)) (fun b' hb' …`. Introduce `a ha b hb a' ha' b' hb'`. Conclude with `SP_swap (s4 a' ha' b' hb' a ha b hb)`.
-/
theorem SP_span {E : Set Hs} (h : ∀ a ∈ E, ∀ b ∈ E, ∀ a' ∈ E, ∀ b' ∈ E, SP m σs D a b a' b') :
    ∀ a ∈ Submodule.span ℂ E, ∀ b ∈ Submodule.span ℂ E, ∀ a' ∈ Submodule.span ℂ E,
      ∀ b' ∈ Submodule.span ℂ E, SP m σs D a b a' b' := by
  have s1 : ∀ a ∈ Submodule.span ℂ E, ∀ b ∈ E, ∀ a' ∈ E, ∀ b' ∈ E, SP m σs D a b a' b' :=
    mem_span_of_closed_lemma (P := fun a => ∀ b ∈ E, ∀ a' ∈ E, ∀ b' ∈ E, SP m σs D a b a' b')
      (fun b _ a' _ b' _ => SP_zero_a b a' b')
      (fun x y hx hy b hb a' ha' b' hb' => SP_add_a (hx b hb a' ha' b' hb') (hy b hb a' ha' b' hb'))
      (fun c x hx b hb a' ha' b' hb' => SP_smul_a c (hx b hb a' ha' b' hb'))
      (fun a ha => h a ha)
  have s2 : ∀ a ∈ Submodule.span ℂ E, ∀ b ∈ Submodule.span ℂ E, ∀ a' ∈ E, ∀ b' ∈ E,
      SP m σs D a b a' b' := by
    intro a ha
    exact mem_span_of_closed_lemma (P := fun b => ∀ a' ∈ E, ∀ b' ∈ E, SP m σs D a b a' b')
      (fun a' _ b' _ => SP_zero_b a a' b')
      (fun x y hx hy a' ha' b' hb' => SP_add_b (hx a' ha' b' hb') (hy a' ha' b' hb'))
      (fun c x hx a' ha' b' hb' => SP_smul_b c (hx a' ha' b' hb'))
      (fun b hb => s1 a ha b hb)
  have s3 : ∀ a' ∈ Submodule.span ℂ E, ∀ b' ∈ E, ∀ a ∈ Submodule.span ℂ E, ∀ b ∈ Submodule.span ℂ E,
      SP m σs D a' b' a b :=
    mem_span_of_closed_lemma
      (P := fun a' => ∀ b' ∈ E, ∀ a ∈ Submodule.span ℂ E, ∀ b ∈ Submodule.span ℂ E, SP m σs D a' b' a b)
      (fun b' _ a _ b _ => SP_zero_a b' a b)
      (fun x y hx hy b' hb' a ha b hb => SP_add_a (hx b' hb' a ha b hb) (hy b' hb' a ha b hb))
      (fun c x hx b' hb' a ha b hb => SP_smul_a c (hx b' hb' a ha b hb))
      (fun a' ha' b' hb' a ha b hb => SP_swap (s2 a ha b hb a' ha' b' hb'))
  have s4 : ∀ a' ∈ Submodule.span ℂ E, ∀ b' ∈ Submodule.span ℂ E, ∀ a ∈ Submodule.span ℂ E,
      ∀ b ∈ Submodule.span ℂ E, SP m σs D a' b' a b := by
    intro a' ha'
    exact mem_span_of_closed_lemma
      (P := fun b' => ∀ a ∈ Submodule.span ℂ E, ∀ b ∈ Submodule.span ℂ E, SP m σs D a' b' a b)
      (fun a _ b _ => SP_zero_b a' a b)
      (fun x y hx hy a ha b hb => SP_add_b (hx a ha b hb) (hy a ha b hb))
      (fun c x hx a ha b hb => SP_smul_b c (hx a ha b hb))
      (fun b' hb' => s3 a' ha' b' hb')
  intro a ha b hb a' ha' b' hb'
  exact SP_swap (s4 a' ha' b' hb' a ha b hb)

end Gen

section Pure

variable {ι : Type} [Fintype ι] {G : ι → Type} [∀ v, Group (G v)] [∀ v, TopologicalSpace (G v)]
  [∀ v, MeasurableSpace (G v)] {H : ι → Type} [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
  {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
  {σ : ∀ v, G v → (H v →L[ℂ] H v)} {σs : (∀ v, G v) → (Hs →L[ℂ] Hs)} {tens : (∀ v, H v) → Hs}

/- English proof (translation)
Establish `hf : (fun x => ⟪tens β, σs x (tens α)⟫_ℂ * conj ⟪tens β', σs x (tens α')⟫_ℂ) = fun x => ∏ v, (⟪β v, σ v (x v) (α v)⟫_ℂ * conj ⟪β' v, σ v (x v) (α' v)⟫_ℂ)`. Use function extensionality and compare the values at `x`. Rewrite using `[h.2.1, h.2.1, h.1, h.1, map_prod, ← Finset.prod_mul_distrib]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hf]`.

Conclude with `Integrable.fintype_prod_dep fun v => ((hS v).2 (α v) (β v) (α' v) (β' v)).1`. Rewrite using `[hf, integral_fintype_prod_eq_prod (fun v y => ⟪β v, σ v y (α v)⟫_ℂ * conj ⟪β' v, σ v y (α' v)⟫_ℂ)]`. Simplify using `only [fun v => ((hS v).2 (α v) (β v) (α' v) (β' v)).2]`. Rewrite using `[h.1, h.1, Finset.prod_div_distrib, Finset.prod_mul_distrib, Complex.ofReal_prod]`.
-/
theorem SP_pure (μ : ∀ v, Measure (G v)) [∀ v, SigmaFinite (μ v)] (d : ι → ℝ)
    (hS : ∀ v, IsSchur (μ v) (σ v) (d v)) (h : IsTensAbs σ σs tens) (α β α' β' : ∀ v, H v) :
    SP (Measure.pi μ) σs (∏ v, d v) (tens α) (tens β) (tens α') (tens β') := by
  have hf : (fun x => ⟪tens β, σs x (tens α)⟫_ℂ * conj ⟪tens β', σs x (tens α')⟫_ℂ) =
      fun x => ∏ v, (⟪β v, σ v (x v) (α v)⟫_ℂ * conj ⟪β' v, σ v (x v) (α' v)⟫_ℂ) := by
    funext x
    rw [h.2.1, h.2.1, h.1, h.1, map_prod, ← Finset.prod_mul_distrib]
  refine ⟨?_, ?_⟩
  · rw [hf]
    exact Integrable.fintype_prod_dep fun v => ((hS v).2 (α v) (β v) (α' v) (β' v)).1
  · rw [hf, integral_fintype_prod_eq_prod (fun v y => ⟪β v, σ v y (α v)⟫_ℂ * conj ⟪β' v, σ v y (α' v)⟫_ℂ)]
    simp only [fun v => ((hS v).2 (α v) (β v) (α' v) (β' v)).2]
    rw [h.1, h.1, Finset.prod_div_distrib, Finset.prod_mul_distrib, Complex.ofReal_prod]

end Pure

end Formalism.L2.S.Pv.SchurTens
