import Mathlib
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwGXi
open NumberField TensorProduct

namespace PositivityTheory.UnitarySelfGeneration

/- English proof (translation)
Set `T : Z ⊗[ℤ] B →ₗ[Z] Module.Dual Z (Z ⊗[ℤ] B)` to `(LinearMap.mul Z (Z ⊗[ℤ] B)).compr₂ L`. Use `show Function.Bijective T`. Set `b` to `Module.Free.chooseBasis ℤ B`. Set `bZ` to `Algebra.TensorProduct.basis Z b`. Establish `hs : Function.Surjective T`.

Introduce `f`. Use `choose m β hu hm using fun i => h (b.coord i)`. Use `⟨∑ i, (f (bZ i) * ↑(hu i).unit⁻¹) ⊗ₜ β i, bZ.ext fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[map_sum, LinearMap.sum_apply]`. Establish `h1 : ∀ i, T ((f (bZ i) * ↑(hu i).unit⁻¹) ⊗ₜ β i) (bZ j) = if j = i then f (bZ i) else 0`.

Introduce `i`. Establish `h2 : bZ j = 1 ⊗ₜ b j` using `Algebra.TensorProduct.basis_apply _ _`. Use `show L (_ * bZ j) = _`. Rewrite using `[h2, Algebra.TensorProduct.tmul_mul_tmul, hL, ← hm, mul_one, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]`. Use `split_ifs`.

Rewrite using `[mul_one, mul_assoc, IsUnit.val_inv_mul, mul_one]`. Simplify using the standard rewrite rules. Simplify using `[h1]`. Use `⟨?_, hs⟩` and prove the remaining obligations. Use `OrzechProperty.injective_of_surjective_endomorphism (bZ.toDualEquiv.symm.toLinearMap.comp T) (bZ.toDualEquiv.symm.surjective.comp hs)` as an intermediate fact.

Conclude with `Function.Injective.of_comp this`.
-/
theorem trace_form_mulLeft_bijective (B Z : Type) [CommRing B] [Module.Finite ℤ B] [Module.Free ℤ B] [CommRing Z]
    (l : B →ₗ[ℤ] ℤ) (h : ∀ f : B →ₗ[ℤ] ℤ, ∃ (m : ℤ) (b : B), IsUnit (m : Z) ∧ ∀ a, m * f a = l (b * a))
    (L : Z ⊗[ℤ] B →ₗ[Z] Z) (hL : ∀ z a, L (z ⊗ₜ a) = z * l a) :
    Function.Bijective (fun r : Z ⊗[ℤ] B => L.comp (LinearMap.mulLeft Z r)) := by
  classical
  let T : Z ⊗[ℤ] B →ₗ[Z] Module.Dual Z (Z ⊗[ℤ] B) := (LinearMap.mul Z (Z ⊗[ℤ] B)).compr₂ L
  show Function.Bijective T
  let b := Module.Free.chooseBasis ℤ B
  let bZ := Algebra.TensorProduct.basis Z b
  have hs : Function.Surjective T := by
    intro f
    choose m β hu hm using fun i => h (b.coord i)
    refine ⟨∑ i, (f (bZ i) * ↑(hu i).unit⁻¹) ⊗ₜ β i, bZ.ext fun j => ?_⟩
    rw [map_sum, LinearMap.sum_apply]
    have h1 : ∀ i, T ((f (bZ i) * ↑(hu i).unit⁻¹) ⊗ₜ β i) (bZ j) = if j = i then f (bZ i) else 0 := by
      intro i
      have h2 : bZ j = 1 ⊗ₜ b j := Algebra.TensorProduct.basis_apply _ _
      show L (_ * bZ j) = _
      rw [h2, Algebra.TensorProduct.tmul_mul_tmul, hL, ← hm, mul_one, Module.Basis.coord_apply,
        Module.Basis.repr_self, Finsupp.single_apply]
      split_ifs
      · rw [mul_one, mul_assoc, IsUnit.val_inv_mul, mul_one]
      · simp
    simp [h1]
  refine ⟨?_, hs⟩
  have := OrzechProperty.injective_of_surjective_endomorphism (bZ.toDualEquiv.symm.toLinearMap.comp T)
    (bZ.toDualEquiv.symm.surjective.comp hs)
  exact Function.Injective.of_comp this

/- English proof (translation)
Introduce `E _ _ _ bar hbar hun p hp`. Take `⟨ξ, h1, h2, h3⟩` from `tw_g_xi E bar hbar hun p hp.out`. Use `choose l0 hl0 using h2`. Set `l : 𝓞 E →ₗ[ℤ] ℤ` to `(AddMonoidHom.mk' l0 fun a b => by`. Apply `Int.cast_injective (α := ℚ)` to reduce the goal to its premises.

Use `push_cast`. Rewrite using `[← hl0, ← hl0, ← hl0, ← map_add, ← mul_add]`. Use the proof step `rfl).toIntLinearMap`. Establish `hl : ∀ a, (l a : ℚ) = Algebra.trace ℚ E (ξ * a)` using `fun a => (hl0 a).symm`. Set `L : ℤ_[p] ⊗[ℤ] 𝓞 E →ₗ[ℤ_[p]] ℤ_[p]` to `(TensorProduct.AlgebraTensorModule.rid ℤ ℤ_[p] ℤ_[p]).toLinearMap.comp (l.baseChange ℤ_[p])`.

Establish `hL : ∀ z a, L (z ⊗ₜ a) = z * l a`. Introduce `z a`. Simplify using `[L, mul_comm]`. Establish `htr : ∀ x : E, Algebra.trace ℚ E (IsCMField.complexConj E x) = Algebra.trace ℚ E x` using `fun x => Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) x`. Establish `hlb : ∀ a, l (bar a) = -l a`.

Introduce `a`. Apply `Int.cast_injective (α := ℚ)` to reduce the goal to its premises. Use `push_cast`. Rewrite using `[hl, hl, ← htr, map_mul, h1, hbar, IsCMField.complexConj_apply_apply, neg_mul, map_neg]`. Use `⟨L, fun r => ?_, trace_form_mulLeft_bijective _ _ l (fun f => ?_) L hL⟩` and prove the remaining obligations.

Proceed by induction on `r using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul z a`. Rewrite using `[Algebra.TensorProduct.map_tmul, hL, hL]`. Use `show z * (l (bar a) : ℤ_[p]) = _`.

Rewrite using `[hlb]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Consider the case `add x y hx hy => rw [map_add, map_add, map_add, hx, hy, neg_add]`. Take `⟨m, b, hm, hb⟩` from `h3 f`.

Use `⟨m, b, ?_, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[PadicInt.isUnit_iff]`. Conclude with `le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun h => hm ((PadicInt.norm_int_lt_one_iff_dvd m).1 h))`. Apply `Int.cast_injective (α := ℚ)` to reduce the goal to its premises. Rewrite using `[hb, hl, mul_assoc]`.

Both sides reduce to the same expression.
-/
theorem tw_g_lam : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (bar : 𝓞 E ≃+* 𝓞 E), (∀ a : 𝓞 E, ((bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) → Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) → ∀ (p : ℕ) [Fact p.Prime], ∃ lam : (ℤ_[p] ⊗[ℤ] 𝓞 E) →ₗ[ℤ_[p]] ℤ_[p], (∀ r, lam (Algebra.TensorProduct.map (AlgHom.id ℤ_[p] ℤ_[p]) bar.toRingHom.toIntAlgHom r) = -lam r) ∧ Function.Bijective (fun r : ℤ_[p] ⊗[ℤ] 𝓞 E => lam.comp (LinearMap.mulLeft ℤ_[p] r)) := by
  intro E _ _ _ bar hbar hun p hp
  obtain ⟨ξ, h1, h2, h3⟩ := tw_g_xi E bar hbar hun p hp.out
  choose l0 hl0 using h2
  let l : 𝓞 E →ₗ[ℤ] ℤ := (AddMonoidHom.mk' l0 fun a b => by
    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [← hl0, ← hl0, ← hl0, ← map_add, ← mul_add]
    rfl).toIntLinearMap
  have hl : ∀ a, (l a : ℚ) = Algebra.trace ℚ E (ξ * a) := fun a => (hl0 a).symm
  let L : ℤ_[p] ⊗[ℤ] 𝓞 E →ₗ[ℤ_[p]] ℤ_[p] :=
    (TensorProduct.AlgebraTensorModule.rid ℤ ℤ_[p] ℤ_[p]).toLinearMap.comp (l.baseChange ℤ_[p])
  have hL : ∀ z a, L (z ⊗ₜ a) = z * l a := by
    intro z a
    simp [L, mul_comm]
  have htr : ∀ x : E, Algebra.trace ℚ E (IsCMField.complexConj E x) = Algebra.trace ℚ E x := fun x =>
    Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) x
  have hlb : ∀ a, l (bar a) = -l a := by
    intro a
    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [hl, hl, ← htr, map_mul, h1, hbar, IsCMField.complexConj_apply_apply, neg_mul, map_neg]
  refine ⟨L, fun r => ?_, trace_form_mulLeft_bijective _ _ l (fun f => ?_) L hL⟩
  · induction r using TensorProduct.induction_on with
    | zero => simp
    | tmul z a =>
      rw [Algebra.TensorProduct.map_tmul, hL, hL]
      show z * (l (bar a) : ℤ_[p]) = _
      rw [hlb]
      push_cast
      ring
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, neg_add]
  · obtain ⟨m, b, hm, hb⟩ := h3 f
    refine ⟨m, b, ?_, fun a => ?_⟩
    · rw [PadicInt.isUnit_iff]
      exact le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun h => hm ((PadicInt.norm_int_lt_one_iff_dvd m).1 h))
    · apply Int.cast_injective (α := ℚ)
      rw [hb, hl, mul_assoc]
      rfl

end PositivityTheory.UnitarySelfGeneration
