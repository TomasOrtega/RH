import Mathlib
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 TensorProduct

namespace GlobalTheory.SplitComp

variable (L : Type) [Field L] [NumberField L] [IsCMField L]

/- English proof (translation)
Establish `h` using `IsCMField.complexConj_ne_one L`. Choose the witnesses or unpack the hypotheses as in `⟨x, hx⟩ : ∃ x : L, IsCMField.complexConj L x ≠ x := by`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Conclude with `h (AlgEquiv.ext hc)`.

Use `⟨x - IsCMField.complexConj L x, sub_ne_zero.mpr hx.symm, ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, IsCMField.complexConj_apply_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_imag : ∃ θ : L, θ ≠ 0 ∧ IsCMField.complexConj L θ = -θ := by
  have h := IsCMField.complexConj_ne_one L
  obtain ⟨x, hx⟩ : ∃ x : L, IsCMField.complexConj L x ≠ x := by
    by_contra hc
    push Not at hc
    exact h (AlgEquiv.ext hc)
  refine ⟨x - IsCMField.complexConj L x, sub_ne_zero.mpr hx.symm, ?_⟩
  rw [map_sub, IsCMField.complexConj_apply_apply]; ring

/- English proof (translation)
Establish `h2 : IsCMField.complexConj L (2 : L) = 2` using `map_ofNat _ 2`. Establish `ha : (x + IsCMField.complexConj L x) / 2 ∈ maximalRealSubfield L`. Rewrite using `[← IsCMField.complexConj_eq_self_iff, map_div₀, map_add, IsCMField.complexConj_apply_apply, h2]`. Expand and normalize the polynomial expressions, which then agree. Establish `hb : (x - IsCMField.complexConj L x) / (2 * θ) ∈ maximalRealSubfield L`.

Rewrite using `[← IsCMField.complexConj_eq_self_iff, map_div₀, map_sub, map_mul, IsCMField.complexConj_apply_apply, h2, hθ]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Use `⟨⟨_, ha⟩, ⟨_, hb⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `x = (x + IsCMField.complexConj L x) / 2 * 1 + (x - IsCMField.complexConj L x) / (2 * θ) * θ`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_real_add (θ : L) (h0 : θ ≠ 0) (hθ : IsCMField.complexConj L θ = -θ) (x : L) :
    ∃ a b : maximalRealSubfield L, x = a • (1 : L) + b • θ := by
  have h2 : IsCMField.complexConj L (2 : L) = 2 := map_ofNat _ 2
  have ha : (x + IsCMField.complexConj L x) / 2 ∈ maximalRealSubfield L := by
    rw [← IsCMField.complexConj_eq_self_iff, map_div₀, map_add, IsCMField.complexConj_apply_apply, h2]
    ring
  have hb : (x - IsCMField.complexConj L x) / (2 * θ) ∈ maximalRealSubfield L := by
    rw [← IsCMField.complexConj_eq_self_iff, map_div₀, map_sub, map_mul,
      IsCMField.complexConj_apply_apply, h2, hθ]
    field_simp
    ring
  refine ⟨⟨_, ha⟩, ⟨_, hb⟩, ?_⟩
  change x = (x + IsCMField.complexConj L x) / 2 * 1 + (x - IsCMField.complexConj L x) / (2 * θ) * θ
  field_simp
  ring

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, 0, by simp⟩`. Consider the case `tmul x c`. Take `⟨a, b, rfl⟩` from `exists_real_add L θ h0 hθ x`. Conclude with `⟨a • c, b • c, by rw [add_tmul, smul_tmul, smul_tmul]⟩`.

Consider the case `add x y hx hy`. Take `⟨a, b, rfl⟩` from `hx`. Take `⟨a', b', rfl⟩` from `hy`. Conclude with `⟨a + a', b + b', by rw [tmul_add, tmul_add]; abel⟩`.
-/
theorem exists_tmul_add (θ : L) (h0 : θ ≠ 0) (hθ : IsCMField.complexConj L θ = -θ) (z : AL L) :
    ∃ a b : AFplus L, z = (1 : L) ⊗ₜ[maximalRealSubfield L] a + θ ⊗ₜ[maximalRealSubfield L] b := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul x c =>
    obtain ⟨a, b, rfl⟩ := exists_real_add L θ h0 hθ x
    exact ⟨a • c, b • c, by rw [add_tmul, smul_tmul, smul_tmul]⟩
  | add x y hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨a', b', rfl⟩ := hy
    exact ⟨a + a', b + b', by rw [tmul_add, tmul_add]; abel⟩

/- English proof (translation)
Introduce `L _ _ _ s z h1 h2`. Take `⟨θ, h0, hθ⟩` from `exists_imag L`. Take `⟨a, b, rfl⟩` from `exists_tmul_add L θ h0 hθ z`. Establish `e1 : evalAt L s.v a + s.i θ * evalAt L s.v b = 0`. Simplify `h1` using `[SplitPlace.proj]`.

Establish `e2 : evalAt L s.v a - s.i θ * evalAt L s.v b = 0`. Simplify `h2` using `[SplitPlace.proj, conjAL, hθ, neg_tmul, sub_eq_add_neg]`. Establish `hi : s.i θ ≠ 0` using `(map_ne_zero s.i).mpr h0`. Establish `: CharZero (s.v.adicCompletion (maximalRealSubfield L))` using `algebraRat.charZero _`. Establish `ha : evalAt L s.v a = 0` using `by linear_combination (e1 + e2) / 2`.

Establish `hb : evalAt L s.v b = 0`. Rewrite `e1` using `[ha, zero_add]`. Conclude with `(mul_eq_zero.mp e1).resolve_left hi`. Simplify using `[compAt, ha, hb]`.
-/
theorem compAt_eq_zero : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (z : AL L),
    s.proj z = 0 → s.proj (conjAL L z) = 0 → compAt L s.v z = 0 := by
  intro L _ _ _ s z h1 h2
  obtain ⟨θ, h0, hθ⟩ := exists_imag L
  obtain ⟨a, b, rfl⟩ := exists_tmul_add L θ h0 hθ z
  have e1 : evalAt L s.v a + s.i θ * evalAt L s.v b = 0 := by
    simpa [SplitPlace.proj] using h1
  have e2 : evalAt L s.v a - s.i θ * evalAt L s.v b = 0 := by
    simpa [SplitPlace.proj, conjAL, hθ, neg_tmul, sub_eq_add_neg] using h2
  have hi : s.i θ ≠ 0 := (map_ne_zero s.i).mpr h0
  have : CharZero (s.v.adicCompletion (maximalRealSubfield L)) :=
    algebraRat.charZero _
  have ha : evalAt L s.v a = 0 := by linear_combination (e1 + e2) / 2
  have hb : evalAt L s.v b = 0 := by
    rw [ha, zero_add] at e1
    exact (mul_eq_zero.mp e1).resolve_left hi
  simp [compAt, ha, hb]

end GlobalTheory.SplitComp
