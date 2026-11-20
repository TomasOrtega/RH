import Mathlib
open scoped TensorProduct

namespace GlobalTheory

/- English proof (translation)
Set `f : NumberField.RingOfIntegers F →ₐ[ℤ] B` to `((algebraMap F B).comp (algebraMap (NumberField.RingOfIntegers F) F)).toIntAlgHom`. Set `g : OB →ₐ[ℤ] B` to `OB.subtype.toIntAlgHom`. Establish `hc : ∀ a b, Commute (f a) (g b)` using `fun a b => Algebra.commutes _ _`. Set `L` to `Algebra.TensorProduct.lift f g hc`. Establish `hL : ∀ a b, L (a ⊗ₜ b) = f a * g b` using `fun a b => Algebra.TensorProduct.lift_tmul f g hc a b`.

Take `⟨s, hs⟩` from `(Module.Finite.fg_top : (⊤ : Submodule ℤ (NumberField.RingOfIntegers F)).FG)`. Use `choose m hm0 hm using fun a : NumberField.RingOfIntegers F => hsat (f a)`. Set `N : ℕ` to `∏ a ∈ s, m a`. Establish `hN0 : 0 < N` using `Finset.prod_pos fun a _ => hm0 a`. Establish `hnat : ∀ (k : ℕ) (y : B), y ∈ OB → (k : B) * y ∈ OB` using `fun k y hy => OB.mul_mem (natCast_mem OB k) hy`.

Set `P : Submodule ℤ (NumberField.RingOfIntegers F)` to `{ carrier := {a | (N : B) * f a ∈ OB} add_mem' := by`. Introduce `a b ha hb`. Simplify using `only [Set.mem_setOf_eq, map_add, mul_add] at *`. Conclude with `OB.add_mem ha hb`. Use the proof step `zero_mem' := by simp`.

Use the proof step `smul_mem' := by`. Introduce `n a ha`. Simplify using `only [Set.mem_setOf_eq, map_zsmul, mul_smul_comm] at *`. Conclude with `OB.zsmul_mem ha n }`. Establish `hsP : (s : Set (NumberField.RingOfIntegers F)) ⊆ SetLike.coe P`.

Introduce `a ha`. Take `⟨k, hk⟩` from `Finset.dvd_prod_of_mem m ha`. Use `show (N : B) * f a ∈ OB`. Establish `: (N : B) = (k : B) * (m a : B)`. Rewrite using `[show N = m a * k from hk, Nat.cast_mul, (Nat.cast_commute _ _).eq]`.

Rewrite using `[this, mul_assoc]`. Conclude with `hnat k _ (hm a)`. Establish `hP : ∀ a, (N : B) * f a ∈ OB`. Introduce `a`. Establish `: a ∈ Submodule.span ℤ (s : Set _)` using `by rw [hs]; trivial`.

Conclude with `(Submodule.span_le.mpr hsP) this`. Use `⟨L.toRingHom.range, ?_, ?_, ?_, N, hN0, ?_⟩` and prove the remaining obligations. Introduce `b hb`. Use `⟨1 ⊗ₜ ⟨b, hb⟩, ?_⟩` and prove the remaining obligations. Use `show L _ = b`.

Rewrite using `[hL]`. Simplify using `[f, g]`. Introduce `a`. Use `⟨a ⊗ₜ 1, ?_⟩` and prove the remaining obligations. Use `show L _ = _`.

Rewrite using `[hL]`. Simplify using `[f, g]`. Use `haveI : Module.Finite ℤ OB := hfin haveI : Module.Finite ℤ (NumberField.RingOfIntegers F ⊗[ℤ] OB) := Module.Finite.tensorProduct _ _ _`. Conclude with `Module.Finite.of_surjective (L.toRingHom.rangeRestrict.toIntAlgHom.toLinearMap) (RingHom.rangeRestrict_surjective _)`. Introduce and unpack `x ⟨t, rfl⟩ show (N : B) * L t ∈ OB`.

Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b`. Rewrite using `[hL, ← mul_assoc]`. Conclude with `OB.mul_mem (hP a) b.2`.

Consider the case `add t u ht hu`. Rewrite using `[map_add, mul_add]`. Conclude with `OB.add_mem ht hu`.
-/
theorem exists_order_integers_mul_finite_index (F B : Type) [Field F] [NumberField F] [Ring B]
    [Algebra F B] [Algebra ℚ B] [IsScalarTower ℚ F B] (OB : Subring B) (hfin : Module.Finite ℤ OB)
    (hsat : ∀ b : B, ∃ m : ℕ, 0 < m ∧ (m : B) * b ∈ OB) :
    ∃ Λ : Subring B, OB ≤ Λ ∧ (∀ a : NumberField.RingOfIntegers F, algebraMap F B (a : F) ∈ Λ) ∧
      Module.Finite ℤ Λ ∧ ∃ N : ℕ, 0 < N ∧ ∀ x ∈ Λ, (N : B) * x ∈ OB := by
  classical
  let f : NumberField.RingOfIntegers F →ₐ[ℤ] B :=
    ((algebraMap F B).comp (algebraMap (NumberField.RingOfIntegers F) F)).toIntAlgHom
  let g : OB →ₐ[ℤ] B := OB.subtype.toIntAlgHom
  have hc : ∀ a b, Commute (f a) (g b) := fun a b => Algebra.commutes _ _
  let L := Algebra.TensorProduct.lift f g hc
  have hL : ∀ a b, L (a ⊗ₜ b) = f a * g b := fun a b => Algebra.TensorProduct.lift_tmul f g hc a b

  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ (NumberField.RingOfIntegers F)).FG)
  choose m hm0 hm using fun a : NumberField.RingOfIntegers F => hsat (f a)
  let N : ℕ := ∏ a ∈ s, m a
  have hN0 : 0 < N := Finset.prod_pos fun a _ => hm0 a
  have hnat : ∀ (k : ℕ) (y : B), y ∈ OB → (k : B) * y ∈ OB := fun k y hy =>
    OB.mul_mem (natCast_mem OB k) hy
  let P : Submodule ℤ (NumberField.RingOfIntegers F) :=
    { carrier := {a | (N : B) * f a ∈ OB}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, map_add, mul_add] at *
        exact OB.add_mem ha hb
      zero_mem' := by simp
      smul_mem' := by
        intro n a ha
        simp only [Set.mem_setOf_eq, map_zsmul, mul_smul_comm] at *
        exact OB.zsmul_mem ha n }
  have hsP : (s : Set (NumberField.RingOfIntegers F)) ⊆ SetLike.coe P := by
    intro a ha
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem m ha
    show (N : B) * f a ∈ OB
    have : (N : B) = (k : B) * (m a : B) := by
      rw [show N = m a * k from hk, Nat.cast_mul, (Nat.cast_commute _ _).eq]
    rw [this, mul_assoc]
    exact hnat k _ (hm a)
  have hP : ∀ a, (N : B) * f a ∈ OB := by
    intro a
    have : a ∈ Submodule.span ℤ (s : Set _) := by rw [hs]; trivial
    exact (Submodule.span_le.mpr hsP) this
  refine ⟨L.toRingHom.range, ?_, ?_, ?_, N, hN0, ?_⟩
  · intro b hb
    refine ⟨1 ⊗ₜ ⟨b, hb⟩, ?_⟩
    show L _ = b
    rw [hL]; simp [f, g]
  · intro a
    refine ⟨a ⊗ₜ 1, ?_⟩
    show L _ = _
    rw [hL]; simp [f, g]
  · haveI : Module.Finite ℤ OB := hfin
    haveI : Module.Finite ℤ (NumberField.RingOfIntegers F ⊗[ℤ] OB) := Module.Finite.tensorProduct _ _ _
    exact Module.Finite.of_surjective (L.toRingHom.rangeRestrict.toIntAlgHom.toLinearMap)
      (RingHom.rangeRestrict_surjective _)
  · rintro x ⟨t, rfl⟩
    show (N : B) * L t ∈ OB
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      rw [hL, ← mul_assoc]
      exact OB.mul_mem (hP a) b.2
    | add t u ht hu =>
      rw [map_add, mul_add]
      exact OB.add_mem ht hu

end GlobalTheory
