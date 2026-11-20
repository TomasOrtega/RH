import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsLieDataCircle

open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology

namespace GlobalTheory.SmoothForms

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Establish `hB1 : B ≤ B ^ 4` using `le_self_pow₀ (by linarith) (by norm_num)`. Choose the witnesses or unpack the hypotheses as in `⟨x, ⟨hx1, hx2, hx3⟩, hx0⟩ : ∃ x ∈ {x | x ∈ Λ ∧ x ∈ W ∧ ν x ≤ B}, x ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Conclude with `hW (le_bot_iff.1 (hsp.trans (Submodule.span_eq_bot.2 hc).le))`.

Choose the witnesses or unpack the hypotheses as in `⟨y, ⟨hy1, hy2, hy3⟩, hxy⟩ : ∃ y ∈ {x | x ∈ Λ ∧ x ∈ W ∧ ν x ≤ B}, h x y ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Use `hx0 (hnd x hx2 fun z hz => ?_)` and prove the remaining obligations. Establish `: Submodule.span E {x | x ∈ Λ ∧ x ∈ W ∧ ν x ≤ B} ≤ LinearMap.ker (h x)` using `Submodule.span_le.2 fun z hz => hc z hz`.

Conclude with `this (hsp hz)`. Distinguish the cases in `hxx : h x x = 0`. Use `swap`. Conclude with `⟨x, hx1, hx2, hxx, hx3.trans hB1⟩`. Distinguish the cases in `hyy : h y y = 0`.

Use `swap`. Conclude with `⟨y, hy1, hy2, hyy, hy3.trans hB1⟩`. Use `⟨x + h x y • y, Λ.add_mem hx1 (H.stable _ (H.int x hx1 y hy1) y hy1), W.add_mem hx2 (W.smul_mem _ hy2), ?_, ?_⟩` and prove the remaining obligations. Establish `: h (x + h x y • y) (x + h x y • y) = 2 * (h x y * star (h x y))`. Simplify using `only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, hxx, hyy, H.symm x y, smul_eq_mul, RingHom.id_apply, starRingEnd_apply]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `mul_ne_zero two_ne_zero (mul_ne_zero hxy (star_ne_zero.2 hxy))`. Establish `h0 : (0 : ℝ) ≤ B` using `by linarith`. Establish `h1 : house (h x y) ≤ B * B` using `(H.form_le x y).trans (mul_le_mul hx3 hy3 (H.nonneg _) h0)`.

Establish `h2 : ν (h x y • y) ≤ B * B * B` using `(H.smul_le _ _).trans (mul_le_mul h1 hy3 (H.nonneg _) (by positivity))`. Establish `h3 : B ≤ B ^ 3` using `le_self_pow₀ (by linarith) (by norm_num)`. Establish `h4 : 2 * B ^ 3 ≤ B * B ^ 3` using `mul_le_mul_of_nonneg_right hB (by positivity)`. Use `H.add_le x (h x y • y)` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem exists_small_anisotropic_mem {V : Type} [AddCommGroup V] [Module E V] {h : V →ₗ[E] V →ₗ⋆[E] E}
    {Λ : Submodule ℤ V} {N : ℤ} {ν : V → ℝ} {B₀ : ℝ} (H : Sized h Λ N ν B₀) {B : ℝ} (hB : 2 ≤ B)
    {W : Submodule E V} (hW : W ≠ ⊥) (hnd : ∀ y ∈ W, (∀ x ∈ W, h y x = 0) → y = 0)
    (hsp : W ≤ Submodule.span E {x | x ∈ Λ ∧ x ∈ W ∧ ν x ≤ B}) :
    ∃ v, v ∈ Λ ∧ v ∈ W ∧ h v v ≠ 0 ∧ ν v ≤ B ^ 4 := by
  have hB1 : B ≤ B ^ 4 := le_self_pow₀ (by linarith) (by norm_num)
  obtain ⟨x, ⟨hx1, hx2, hx3⟩, hx0⟩ : ∃ x ∈ {x | x ∈ Λ ∧ x ∈ W ∧ ν x ≤ B}, x ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hW (le_bot_iff.1 (hsp.trans (Submodule.span_eq_bot.2 hc).le))
  obtain ⟨y, ⟨hy1, hy2, hy3⟩, hxy⟩ : ∃ y ∈ {x | x ∈ Λ ∧ x ∈ W ∧ ν x ≤ B}, h x y ≠ 0 := by
    by_contra hc
    push Not at hc
    refine hx0 (hnd x hx2 fun z hz => ?_)
    have : Submodule.span E {x | x ∈ Λ ∧ x ∈ W ∧ ν x ≤ B} ≤ LinearMap.ker (h x) :=
      Submodule.span_le.2 fun z hz => hc z hz
    exact this (hsp hz)
  by_cases hxx : h x x = 0
  swap
  · exact ⟨x, hx1, hx2, hxx, hx3.trans hB1⟩
  by_cases hyy : h y y = 0
  swap
  · exact ⟨y, hy1, hy2, hyy, hy3.trans hB1⟩
  refine ⟨x + h x y • y, Λ.add_mem hx1 (H.stable _ (H.int x hx1 y hy1) y hy1),
    W.add_mem hx2 (W.smul_mem _ hy2), ?_, ?_⟩
  · have : h (x + h x y • y) (x + h x y • y) = 2 * (h x y * star (h x y)) := by
      simp only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, hxx, hyy, H.symm x y,
        smul_eq_mul, RingHom.id_apply, starRingEnd_apply]
      ring
    rw [this]
    exact mul_ne_zero two_ne_zero (mul_ne_zero hxy (star_ne_zero.2 hxy))
  · have h0 : (0 : ℝ) ≤ B := by linarith
    have h1 : house (h x y) ≤ B * B := (H.form_le x y).trans (mul_le_mul hx3 hy3 (H.nonneg _) h0)
    have h2 : ν (h x y • y) ≤ B * B * B :=
      (H.smul_le _ _).trans (mul_le_mul h1 hy3 (H.nonneg _) (by positivity))
    have h3 : B ≤ B ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
    have h4 : 2 * B ^ 3 ≤ B * B ^ 3 := mul_le_mul_of_nonneg_right hB (by positivity)
    have := H.add_le x (h x y • y)
    nlinarith

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => exact ⟨0, fun V _ _ _ h Λ N ν B₀ H B hB W hn hnd hsp => ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩⟩`. Consider the case `succ n ih`. Take `⟨k, ih⟩` from `ih`. Use `⟨10 * k + 4, fun V _ _ _ h Λ N ν B₀ H B hB W hn hnd hsp => ?_⟩` and prove the remaining obligations.

Establish `hW : W ≠ ⊥`. Introduce and unpack `rfl`. Simplify using `at hn`. Establish `h0 : (0 : ℝ) ≤ B` using `by linarith`. Establish `hB1 : (1 : ℝ) ≤ B` using `by linarith`.

Take `⟨v, hv1, hv2, hv3, hv4⟩` from `exists_small_anisotropic_mem H hB hW hnd hsp`. Set `g : W →ₗ[E] E` to `(h.flip v).domRestrict W`. Set `W' : Submodule E V` to `(LinearMap.ker g).map W.subtype`. Establish `hmem : ∀ x, x ∈ W' ↔ x ∈ W ∧ h x v = 0` using `fun x => by`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `⟨y.2, hy⟩`. Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨⟨x, h1⟩, h2, rfl⟩`. Establish `hrank : Module.finrank E W' = n`.

Establish `h1` using `g.finrank_range_add_finrank_ker`. Establish `h2 : LinearMap.range g = ⊤`. Rewrite using `[eq_top_iff]`. Introduce `c _`. Use `⟨(c / h v v) • ⟨v, hv2⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_smul]`. Express the relevant statement in the definitionally equal form `(c / h v v) * h v v = c`. Clear the denominators using the available nonvanishing facts. Rewrite `h1` using `[h2, hn, finrank_top, Module.finrank_self]`. Rewrite using `[Submodule.finrank_map_subtype_eq]`.

Use linear arithmetic over natural numbers and integers. Set `P : V →ₗ[E] V` to `h v v • LinearMap.id - (h.flip v).smulRight v`. Establish `hP : ∀ x, P x = h v v • x + (-h x v) • v` using `fun x => by`. Simplify using `[P, sub_eq_add_neg]`. Establish `hPW : ∀ x ∈ W, P x ∈ W'` using `fun x hx => by`.

Rewrite using `[hmem, hP]`. Use `⟨W.add_mem (W.smul_mem _ hx) (W.smul_mem _ hv2), ?_⟩` and prove the remaining obligations. Simplify using `only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hnd' : ∀ y ∈ W', (∀ x ∈ W', h y x = 0) → y = 0` using `fun y hy hy0 => by`.

Take `⟨hy1, hy2⟩` from `(hmem y).1 hy`. Use `hnd y hy1 fun x hx => ?_` and prove the remaining obligations. Establish `h1` using `hy0 _ (hPW x hx)`. Rewrite `h1` using `[hP]`. Simplify using `only [map_add, map_smulₛₗ, hy2, smul_eq_mul, mul_zero, add_zero, starRingEnd_apply] at h1`.

Conclude with `(mul_eq_zero.1 h1).resolve_left (star_ne_zero.2 hv3)`. Establish `hsp' : W' ≤ Submodule.span E {x | x ∈ Λ ∧ x ∈ W' ∧ ν x ≤ B ^ 10}`. Establish `h1 : Submodule.span E {x | x ∈ Λ ∧ x ∈ W ∧ ν x ≤ B} ≤ (Submodule.span E {x | x ∈ Λ ∧ x ∈ W' ∧ ν x ≤ B ^ 10}).comap P`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `x ⟨hx1, hx2, hx3⟩`.

Use `Submodule.subset_span ⟨?_, hPW x hx2, ?_⟩` and prove the remaining obligations. Rewrite using `[hP]`. Conclude with `Λ.add_mem (H.stable _ (H.int v hv1 v hv1) x hx1) (H.stable _ (H.int x hx1 v hv1).neg v hv1)`. Rewrite using `[hP]`. Establish `a1 : house (h v v) ≤ B ^ 4 * B ^ 4` using `(H.form_le v v).trans (mul_le_mul hv4 hv4 (H.nonneg _) (by positivity))`.

Establish `a2 : house (-h x v) ≤ B * B ^ 4`. Establish `: house (-h x v) = house (h x v)` using `by simp [house]`. Rewrite using `[this]`. Conclude with `(H.form_le x v).trans (mul_le_mul hx3 hv4 (H.nonneg _) h0)`. Establish `a3 : ν (h v v • x) ≤ B ^ 4 * B ^ 4 * B` using `(H.smul_le _ _).trans (mul_le_mul a1 hx3 (H.nonneg _) (by positivity))`.

Establish `a4 : ν ((-h x v) • v) ≤ B * B ^ 4 * B ^ 4` using `(H.smul_le _ _).trans (mul_le_mul a2 hv4 (H.nonneg _) (by positivity))`. Establish `a5 : 2 * B ^ 9 ≤ B * B ^ 9` using `mul_le_mul_of_nonneg_right hB (by positivity)`. Combine the equalities or inequalities in the displayed calculation. Introduce `x hx`. Take `⟨hx1, hx2⟩` from `(hmem x).1 hx`.

Establish `h2 : P x ∈ Submodule.span E {x | x ∈ Λ ∧ x ∈ W' ∧ ν x ≤ B ^ 10}` using `h1 (hsp hx1)`. Rewrite `h2` using `[hP, hx2, neg_zero, zero_smul, add_zero]`. Conclude with `(Submodule.smul_mem_iff _ hv3).1 h2`. Take `⟨w, hw1, hw2, hw3⟩` from `ih V h Λ N ν B₀ H (B ^ 10) (hB.trans (le_self_pow₀ hB1 (by norm_num))) W' hrank hnd' hsp'`. Establish `hwv : ∀ i, h (w i) v = 0` using `fun i => ((hmem _).1 (hw1 i).2).2`.

Use `⟨Fin.cons v w, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i`. Use `Fin.cases ⟨hv1, hv2⟩ (fun i => ?_) i` and prove the remaining obligations. Conclude with `⟨(hw1 i).1, ((hmem _).1 (hw1 i).2).1⟩`. Introduce `i j`.

Apply the tactic sequence `refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j`. Introduce `hij`. Conclude with `absurd rfl hij`. Introduce `_`. Simplify using `only [Fin.cons_zero, Fin.cons_succ]`.

Rewrite using `[H.symm, hwv, star_zero]`. Introduce `_`. Simplify using `using hwv i`. Introduce `hij`. Simplify using `using hw2 i j fun e => hij (by rw [e])`.

Introduce `i`. Use `Fin.cases ⟨hv3, hv4.trans (pow_le_pow_right₀ hB1 (by omega))⟩ (fun i => ?_) i` and prove the remaining obligations. Use `⟨(hw3 i).1, (hw3 i).2.trans ?_⟩` and prove the remaining obligations. Rewrite using `[← pow_mul]`. Conclude with `pow_le_pow_right₀ hB1 (by omega)`.
-/
theorem exists_small_frame_mem (n : ℕ) : ∃ k : ℕ, ∀ (V : Type) [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (Λ : Submodule ℤ V) (N : ℤ) (ν : V → ℝ) (B₀ : ℝ), Sized h Λ N ν B₀ →
    ∀ B : ℝ, 2 ≤ B → ∀ W : Submodule E V, Module.finrank E W = n → (∀ y ∈ W, (∀ x ∈ W, h y x = 0) → y = 0) →
    W ≤ Submodule.span E {x | x ∈ Λ ∧ x ∈ W ∧ ν x ≤ B} →
    ∃ v : Fin n → V, (∀ i, v i ∈ Λ ∧ v i ∈ W) ∧ (∀ i j, i ≠ j → h (v i) (v j) = 0) ∧
      ∀ i, h (v i) (v i) ≠ 0 ∧ ν (v i) ≤ B ^ k := by
  induction n with
  | zero => exact ⟨0, fun V _ _ _ h Λ N ν B₀ H B hB W hn hnd hsp =>
      ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩⟩
  | succ n ih =>
    obtain ⟨k, ih⟩ := ih
    refine ⟨10 * k + 4, fun V _ _ _ h Λ N ν B₀ H B hB W hn hnd hsp => ?_⟩
    have hW : W ≠ ⊥ := by
      rintro rfl
      simp at hn
    have h0 : (0 : ℝ) ≤ B := by linarith
    have hB1 : (1 : ℝ) ≤ B := by linarith
    obtain ⟨v, hv1, hv2, hv3, hv4⟩ := exists_small_anisotropic_mem H hB hW hnd hsp
    let g : W →ₗ[E] E := (h.flip v).domRestrict W
    let W' : Submodule E V := (LinearMap.ker g).map W.subtype
    have hmem : ∀ x, x ∈ W' ↔ x ∈ W ∧ h x v = 0 := fun x => by
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.2, hy⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨x, h1⟩, h2, rfl⟩
    have hrank : Module.finrank E W' = n := by
      have h1 := g.finrank_range_add_finrank_ker
      have h2 : LinearMap.range g = ⊤ := by
        rw [eq_top_iff]
        intro c _
        refine ⟨(c / h v v) • ⟨v, hv2⟩, ?_⟩
        rw [map_smul]
        change (c / h v v) * h v v = c
        field_simp
      rw [h2, hn, finrank_top, Module.finrank_self] at h1
      rw [Submodule.finrank_map_subtype_eq]
      omega
    let P : V →ₗ[E] V := h v v • LinearMap.id - (h.flip v).smulRight v
    have hP : ∀ x, P x = h v v • x + (-h x v) • v := fun x => by
      simp [P, sub_eq_add_neg]
    have hPW : ∀ x ∈ W, P x ∈ W' := fun x hx => by
      rw [hmem, hP]
      refine ⟨W.add_mem (W.smul_mem _ hx) (W.smul_mem _ hv2), ?_⟩
      simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
      ring
    have hnd' : ∀ y ∈ W', (∀ x ∈ W', h y x = 0) → y = 0 := fun y hy hy0 => by
      obtain ⟨hy1, hy2⟩ := (hmem y).1 hy
      refine hnd y hy1 fun x hx => ?_
      have h1 := hy0 _ (hPW x hx)
      rw [hP] at h1
      simp only [map_add, map_smulₛₗ, hy2, smul_eq_mul, mul_zero, add_zero, starRingEnd_apply] at h1
      exact (mul_eq_zero.1 h1).resolve_left (star_ne_zero.2 hv3)
    have hsp' : W' ≤ Submodule.span E {x | x ∈ Λ ∧ x ∈ W' ∧ ν x ≤ B ^ 10} := by
      have h1 : Submodule.span E {x | x ∈ Λ ∧ x ∈ W ∧ ν x ≤ B} ≤
          (Submodule.span E {x | x ∈ Λ ∧ x ∈ W' ∧ ν x ≤ B ^ 10}).comap P := by
        refine Submodule.span_le.2 ?_
        rintro x ⟨hx1, hx2, hx3⟩
        refine Submodule.subset_span ⟨?_, hPW x hx2, ?_⟩
        · rw [hP]
          exact Λ.add_mem (H.stable _ (H.int v hv1 v hv1) x hx1) (H.stable _ (H.int x hx1 v hv1).neg v hv1)
        · rw [hP]
          have a1 : house (h v v) ≤ B ^ 4 * B ^ 4 :=
            (H.form_le v v).trans (mul_le_mul hv4 hv4 (H.nonneg _) (by positivity))
          have a2 : house (-h x v) ≤ B * B ^ 4 := by
            have : house (-h x v) = house (h x v) := by simp [house]
            rw [this]
            exact (H.form_le x v).trans (mul_le_mul hx3 hv4 (H.nonneg _) h0)
          have a3 : ν (h v v • x) ≤ B ^ 4 * B ^ 4 * B :=
            (H.smul_le _ _).trans (mul_le_mul a1 hx3 (H.nonneg _) (by positivity))
          have a4 : ν ((-h x v) • v) ≤ B * B ^ 4 * B ^ 4 :=
            (H.smul_le _ _).trans (mul_le_mul a2 hv4 (H.nonneg _) (by positivity))
          have a5 : 2 * B ^ 9 ≤ B * B ^ 9 := mul_le_mul_of_nonneg_right hB (by positivity)
          calc _ ≤ _ := H.add_le _ _
            _ ≤ _ := add_le_add a3 a4
            _ = 2 * B ^ 9 := by ring
            _ ≤ B * B ^ 9 := a5
            _ = B ^ 10 := by ring
      intro x hx
      obtain ⟨hx1, hx2⟩ := (hmem x).1 hx
      have h2 : P x ∈ Submodule.span E {x | x ∈ Λ ∧ x ∈ W' ∧ ν x ≤ B ^ 10} := h1 (hsp hx1)
      rw [hP, hx2, neg_zero, zero_smul, add_zero] at h2
      exact (Submodule.smul_mem_iff _ hv3).1 h2
    obtain ⟨w, hw1, hw2, hw3⟩ := ih V h Λ N ν B₀ H (B ^ 10)
      (hB.trans (le_self_pow₀ hB1 (by norm_num))) W' hrank hnd' hsp'
    have hwv : ∀ i, h (w i) v = 0 := fun i => ((hmem _).1 (hw1 i).2).2
    refine ⟨Fin.cons v w, ?_, ?_, ?_⟩
    · intro i
      refine Fin.cases ⟨hv1, hv2⟩ (fun i => ?_) i
      exact ⟨(hw1 i).1, ((hmem _).1 (hw1 i).2).1⟩
    · intro i j
      refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
      · intro hij; exact absurd rfl hij
      · intro _
        simp only [Fin.cons_zero, Fin.cons_succ]
        rw [H.symm, hwv, star_zero]
      · intro _
        simpa using hwv i
      · intro hij
        simpa using hw2 i j fun e => hij (by rw [e])
    · intro i
      refine Fin.cases ⟨hv3, hv4.trans (pow_le_pow_right₀ hB1 (by omega))⟩ (fun i => ?_) i
      refine ⟨(hw3 i).1, (hw3 i).2.trans ?_⟩
      rw [← pow_mul]
      exact pow_le_pow_right₀ hB1 (by omega)

/- English proof (translation)
Introduce `E _ _ _ n`. Take `⟨k, hk⟩` from `exists_small_frame_mem (E := E) n`. Use `⟨k, fun V _ _ _ h Λ N ν B hn H => ?_⟩` and prove the remaining obligations. Take `⟨v, h1, h2, h3⟩` from `hk V h Λ N ν B H B H.two_le ⊤ (by rw [finrank_top, hn]) (fun y _ hy => H.nondeg y fun x => hy x trivial) (by simp [H.span])`. Conclude with `⟨v, fun i => (h1 i).1, h2, h3⟩`.
-/
theorem frameSmall : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], FrameSmall E := by
  intro E _ _ _ n
  obtain ⟨k, hk⟩ := exists_small_frame_mem (E := E) n
  refine ⟨k, fun V _ _ _ h Λ N ν B hn H => ?_⟩
  obtain ⟨v, h1, h2, h3⟩ := hk V h Λ N ν B H B H.two_le ⊤ (by rw [finrank_top, hn])
    (fun y _ hy => H.nondeg y fun x => hy x trivial) (by simp [H.span])
  exact ⟨v, fun i => (h1 i).1, h2, h3⟩

end GlobalTheory.SmoothForms
