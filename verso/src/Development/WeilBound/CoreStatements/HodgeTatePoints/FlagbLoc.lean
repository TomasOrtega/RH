import Mathlib
import Development.WeilBound.CoreStatements.HodgeTatePoints.FlagbAlg

noncomputable section

namespace PositivityTheory.HtPt.Flagb

open AlgebraicGeometry CategoryTheory NumberField GlobalTheory.CompanionTheory.Ar

variable {Ω L : Type} [Field Ω] [AddCommGroup L] [Module Ω L]

/- English proof (translation)
Establish `h1 : b i ∈ flagStep Ω b₀ (i + 1)`. Rewrite using `[← hF]; exact Submodule.subset_span ⟨i, by simp, rfl⟩`. Establish `h2 : b₀ '' {k | (k : ℕ) < i + 1} = insert (b₀ i) (b₀ '' {k | (k : ℕ) < i})`. Rewrite using `[← Set.image_insert_eq]`. Use `congr 1`.

Use extensionality with `k`. Simplify using `only [Set.mem_setOf_eq, Set.mem_insert_iff, Fin.ext_iff]`. Use linear arithmetic over natural numbers and integers. Unfold `flagStep at h1`. Rewrite `h1` using `[h2, Submodule.mem_span_insert]`.

Take `⟨a, z, hz, h⟩` from `h1`. Conclude with `⟨a, by rw [h, add_sub_cancel_left]; exact hz⟩`.
-/
theorem exists_lead {r : ℕ} (b₀ b : Fin r → L) (hF : ∀ i, flagStep Ω b i = flagStep Ω b₀ i) (i : Fin r) :
    ∃ τ : Ω, b i - τ • b₀ i ∈ flagStep Ω b₀ i := by
  have h1 : b i ∈ flagStep Ω b₀ (i + 1) := by
    rw [← hF]; exact Submodule.subset_span ⟨i, by simp, rfl⟩
  have h2 : b₀ '' {k | (k : ℕ) < i + 1} = insert (b₀ i) (b₀ '' {k | (k : ℕ) < i}) := by
    rw [← Set.image_insert_eq]
    congr 1
    ext k
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Fin.ext_iff]
    omega
  unfold flagStep at h1
  rw [h2, Submodule.mem_span_insert] at h1
  obtain ⟨a, z, hz, h⟩ := h1
  exact ⟨a, by rw [h, add_sub_cancel_left]; exact hz⟩

/- English proof (translation)
Take `⟨u, rfl⟩` from `Submodule.mem_span_singleton.1 h`. Distinguish the cases in `hc : c = 0`. Simplify using `[hc]`. Use `show (u : Ω) * c / c ∈ R`. Rewrite using `[mul_div_cancel_right₀ _ hc]`.

Conclude with `u.2`.
-/
theorem div_mem_of_span (R : Subring Ω) {a c : Ω} (h : a ∈ Submodule.span R {c}) : a / c ∈ R := by
  obtain ⟨u, rfl⟩ := Submodule.mem_span_singleton.1 h
  by_cases hc : c = 0
  · simp [hc]
  · show (u : Ω) * c / c ∈ R
    rw [mul_div_cancel_right₀ _ hc]; exact u.2

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Use `div_mem_of_span _ ?_` and prove the remaining obligations. Rewrite using `[← hc]`. Conclude with `Submodule.subset_span ⟨fun _ => τ, fun _ => h, by simp⟩`. Use `div_mem_of_span _ ?_` and prove the remaining obligations.

Establish `: Lat.tens (fun _ : Unit => Λ) (fun _ => ε) q ≤ Submodule.span (regAt ξ q) {τ ^ ε}`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨s, hs, rfl⟩`. Use `replace hs : ∀ i, Λ.IsGenAt q (s i) := hs`. Establish `h1 : s () / τ ∈ regAt ξ q` using `div_mem_of_span _ (by`.

Rewrite using `[← h.2, (hs ()).2]`. Conclude with `Submodule.mem_span_singleton_self _)`. Establish `h2 : τ / s () ∈ regAt ξ q` using `div_mem_of_span _ (by`. Rewrite using `[← (hs ()).2, h.2]`. Conclude with `Submodule.mem_span_singleton_self _)`.

Establish `h3` using `h.1`. Establish `h4` using `(hs ()).1`. Break down `hε with rfl | rfl` into its components or cases. Use `Submodule.mem_span_singleton.2 ⟨⟨_, h1⟩, ?_⟩ show s () / τ * τ ^ (1 : ℤ) = _` and prove the remaining obligations. Simplify using `[h3]`.

Use `Submodule.mem_span_singleton.2 ⟨⟨_, h2⟩, ?_⟩ show τ / s () * τ ^ (-1 : ℤ) = _` and prove the remaining obligations. Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts. Conclude with `this (hc ▸ Submodule.mem_span_singleton_self _)`.
-/
theorem tens_gen {X : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X} (Λ : Lat ξ Ω) (q : Cpt ξ) (ε : ℤ)
    (hε : ε = 1 ∨ ε = -1) (τ c : Ω) (h : Λ.IsGenAt q τ)
    (hc : Lat.tens (fun _ : Unit => Λ) (fun _ => ε) q = Submodule.span (regAt ξ q) {c}) :
    τ ^ ε / c ∈ regAt ξ q ∧ c / τ ^ ε ∈ regAt ξ q := by
  constructor
  · refine div_mem_of_span _ ?_
    rw [← hc]
    exact Submodule.subset_span ⟨fun _ => τ, fun _ => h, by simp⟩
  · refine div_mem_of_span _ ?_
    have : Lat.tens (fun _ : Unit => Λ) (fun _ => ε) q ≤ Submodule.span (regAt ξ q) {τ ^ ε} := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨s, hs, rfl⟩
      replace hs : ∀ i, Λ.IsGenAt q (s i) := hs
      have h1 : s () / τ ∈ regAt ξ q := div_mem_of_span _ (by
        rw [← h.2, (hs ()).2]; exact Submodule.mem_span_singleton_self _)
      have h2 : τ / s () ∈ regAt ξ q := div_mem_of_span _ (by
        rw [← (hs ()).2, h.2]; exact Submodule.mem_span_singleton_self _)
      have h3 := h.1
      have h4 := (hs ()).1
      rcases hε with rfl | rfl
      · refine Submodule.mem_span_singleton.2 ⟨⟨_, h1⟩, ?_⟩
        show s () / τ * τ ^ (1 : ℤ) = _
        simp [h3]
      · refine Submodule.mem_span_singleton.2 ⟨⟨_, h2⟩, ?_⟩
        show τ / s () * τ ^ (-1 : ℤ) = _
        simp
        field_simp
    exact this (hc ▸ Submodule.mem_span_singleton_self _)

/- English proof (translation)
Set `B : Module.Basis (Fin r) Ω (Module.Dual Ω V)` to `Module.Basis.mk hf hs.ge`. Establish `hB : ∀ j, B j = f j` using `fun j => Module.Basis.mk_apply _ _ j`. Establish `h1 : ∀ j, B.repr u j ∈ R`. Introduce `j`. Establish `h2 : ∀ w : Module.Dual Ω V, w ((Module.evalEquiv Ω V).symm (B.coord j)) = B.repr w j` using `fun w => by`.

Rewrite using `[Module.apply_evalEquiv_symm_apply]`. Both sides reduce to the same expression. Rewrite using `[← h2]`. Use `hu _ fun i => ?_` and prove the remaining obligations. Rewrite using `[h2, ← hB, B.repr_self, Finsupp.single_apply]`.

Use `split_ifs`. Conclude with `R.one_mem`. Conclude with `R.zero_mem`. Rewrite using `[← B.sum_repr u]`. Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations.

Conclude with `Submodule.smul_mem (Submodule.span R (Set.range f)) (⟨_, h1 j⟩ : R) (Submodule.subset_span ⟨j, (hB j).symm⟩)`.
-/
theorem mem_span_of_dual {V : Type} [AddCommGroup V] [Module Ω V] [FiniteDimensional Ω V] (R : Subring Ω) {r : ℕ}
    (f : Fin r → Module.Dual Ω V) (hf : LinearIndependent Ω f) (hs : Submodule.span Ω (Set.range f) = ⊤)
    (u : Module.Dual Ω V) (hu : ∀ e : V, (∀ j, f j e ∈ R) → u e ∈ R) : u ∈ Submodule.span R (Set.range f) := by
  classical
  let B : Module.Basis (Fin r) Ω (Module.Dual Ω V) := Module.Basis.mk hf hs.ge
  have hB : ∀ j, B j = f j := fun j => Module.Basis.mk_apply _ _ j
  have h1 : ∀ j, B.repr u j ∈ R := by
    intro j
    have h2 : ∀ w : Module.Dual Ω V, w ((Module.evalEquiv Ω V).symm (B.coord j)) = B.repr w j := fun w => by
      rw [Module.apply_evalEquiv_symm_apply]; rfl
    rw [← h2]
    refine hu _ fun i => ?_
    rw [h2, ← hB, B.repr_self, Finsupp.single_apply]
    split_ifs
    · exact R.one_mem
    · exact R.zero_mem
  rw [← B.sum_repr u]
  refine Submodule.sum_mem _ fun j _ => ?_
  exact Submodule.smul_mem (Submodule.span R (Set.range f)) (⟨_, h1 j⟩ : R) (Submodule.subset_span ⟨j, (hB j).symm⟩)

/- English proof (translation)
Proceed by induction on `he using Submodule.span_induction with`. Consider the case `mem x hx => exact h x hx`. Consider the case `zero => rw [map_zero]`. Conclude with `R.zero_mem`. Consider the case `add x y _ _ hx hy => rw [map_add]`.

Conclude with `add_mem hx hy`. Consider the case `smul c x _ hx`. Establish `: w (c • x) = (c : Ω) * w x` using `map_smul w (c : Ω) x`. Rewrite using `[this]`. Conclude with `mul_mem c.2 hx`.
-/
theorem apply_mem_of_span (R : Subring Ω) (w : Module.Dual Ω L) (s : Set L) (h : ∀ x ∈ s, w x ∈ R) (e : L)
    (he : e ∈ Submodule.span R s) : w e ∈ R := by
  induction he using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => rw [map_zero]; exact R.zero_mem
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx =>
    have : w (c • x) = (c : Ω) * w x := map_smul w (c : Ω) x
    rw [this]; exact mul_mem c.2 hx

/- English proof (translation)
Take `⟨y, hy, hi⟩` from `(show IsAlgebraic ℤ x from (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic x)).exists_integral_multiple`. Take `⟨z, hz⟩ : ∃ z : 𝓞 E, algebraMap (𝓞 E) E z = y * x` from `⟨⟨y • x, hi⟩, by rw [← zsmul_eq_mul]; rfl⟩`. Establish `hN` using `Ideal.absNorm_mem (differentIdeal ℤ (𝓞 E))`. Establish `hN0 : Ideal.absNorm (differentIdeal ℤ (𝓞 E)) ≠ 0` using `fun h => differentIdeal_ne_bot (A := ℤ) (B := 𝓞 E) (Ideal.absNorm_eq_zero_iff.1 h)`. Use `⟨Ideal.absNorm (differentIdeal ℤ (𝓞 E)) * y.natAbs ^ 2, mul_ne_zero hN0 (pow_ne_zero _ (by simpa using hy)), _, Ideal.mul_mem_right ((y : 𝓞 E) * z) _ hN, ?_⟩` and prove the remaining obligations.

Establish `: ((y.natAbs ^ 2 : ℕ) : E) = (y : E) * y`. Rewrite using `[← Int.cast_natCast, Nat.cast_pow, Int.natAbs_sq, Int.cast_pow, sq]`. Rewrite using `[Nat.cast_mul, this]`. Simplify using `only [RingOfIntegers.coe_eq_algebraMap, map_mul, map_natCast, map_intCast]`. Rewrite using `[hz]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_nat_diff {E : Type} [Field E] [NumberField E] (x : E) :
    ∃ n : ℕ, n ≠ 0 ∧ ∃ δ ∈ differentIdeal ℤ (𝓞 E), (δ : E) = n * x := by
  obtain ⟨y, hy, hi⟩ := (show IsAlgebraic ℤ x from
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic x)).exists_integral_multiple
  obtain ⟨z, hz⟩ : ∃ z : 𝓞 E, algebraMap (𝓞 E) E z = y * x := ⟨⟨y • x, hi⟩, by rw [← zsmul_eq_mul]; rfl⟩
  have hN := Ideal.absNorm_mem (differentIdeal ℤ (𝓞 E))
  have hN0 : Ideal.absNorm (differentIdeal ℤ (𝓞 E)) ≠ 0 := fun h =>
    differentIdeal_ne_bot (A := ℤ) (B := 𝓞 E) (Ideal.absNorm_eq_zero_iff.1 h)
  refine ⟨Ideal.absNorm (differentIdeal ℤ (𝓞 E)) * y.natAbs ^ 2, mul_ne_zero hN0 (pow_ne_zero _ (by simpa using hy)),
    _, Ideal.mul_mem_right ((y : 𝓞 E) * z) _ hN, ?_⟩
  have : ((y.natAbs ^ 2 : ℕ) : E) = (y : E) * y := by
    rw [← Int.cast_natCast, Nat.cast_pow, Int.natAbs_sq, Int.cast_pow, sq]
  rw [Nat.cast_mul, this]
  simp only [RingOfIntegers.coe_eq_algebraMap, map_mul, map_natCast, map_intCast]
  rw [hz]; ring

end PositivityTheory.HtPt.Flagb
