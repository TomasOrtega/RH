import Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.CompactFixesLattice

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Set `β : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → E` to `fun j => algebraMap (𝓞 E) E (NumberField.RingOfIntegers.basis E j)`. Establish `hspanQ : Submodule.span ℚ (Set.range β) = ⊤`. Establish `h` using `(NumberField.integralBasis E).span_eq`. Establish `hr : Set.range (NumberField.integralBasis E) = Set.range β`. Use extensionality with `x`.

Simplify using `[β, NumberField.integralBasis_apply]`. Rewrite `h` using `[hr]`. Conclude with `h`. Establish `hspan : Submodule.span F (Set.range β) = ⊤`. Rewrite using `[eq_top_iff]`.

Introduce `x _`. Establish `hx : x ∈ Submodule.span ℚ (Set.range β)` using `by rw [hspanQ]; exact Submodule.mem_top`. Conclude with `Submodule.span_le_restrictScalars ℚ F _ hx`. Take `⟨B, hBsub, hBspan, hBli⟩` from `exists_linearIndependent F (Set.range β)`. Establish `hBfin : B.Finite` using `(Set.finite_range β).subset hBsub`.

Use `haveI := hBfin.fintype`. Set `e` to `Fintype.equivFin B`. Set `b0 : Module.Basis B F E` to `Module.Basis.mk hBli (by rw [Subtype.range_coe, hBspan, hspan])`. Set `b : Module.Basis (Fin (Fintype.card B)) F E` to `b0.reindex e`. Take `⟨D, hD⟩` from `IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 F)) ((Finset.univ : Finset (Module.Free.ChooseBasisIndex ℤ (𝓞 E) × Fin (Fintype.card B))).image fun p => b.repr (β p.1) p.2)`.

Use `⟨Fintype.card B, b, (D : 𝓞 F), nonZeroDivisors.ne_zero D.2, ?_, ?_⟩` and prove the remaining obligations. Introduce `i`. Establish `hbi : b i = ((e.symm i : B) : E)` using `by simp [b, b0]`. Take `⟨j, hj⟩` from `hBsub (e.symm i).2`. Rewrite using `[hbi, ← hj]`.

Conclude with `RingHom.mem_range.mpr ⟨_, rfl⟩`. Introduce `x hx i`. Take `⟨y, rfl⟩` from `RingHom.mem_range.mp hx`. Establish `key : ∀ j, ((D : 𝓞 F) : F) * b.repr (β j) i ∈ (algebraMap (𝓞 F) F).range`. Introduce `j`.

Take `⟨z, hz⟩` from `hD (b.repr (β j) i) (Finset.mem_image.mpr ⟨(j, i), Finset.mem_univ _, rfl⟩)`. Use `RingHom.mem_range.mpr ⟨z, ?_⟩` and prove the remaining obligations. Rewrite using `[hz, Algebra.smul_def]`. Establish `hxe : algebraMap (𝓞 E) E y = ∑ j, ((NumberField.RingOfIntegers.basis E).repr y j) • β j` using `by conv_lhs => rw [← (NumberField.RingOfIntegers.basis E).sum_repr y]`. Rewrite using `[map_sum]`.

Simplify using `[β, map_zsmul]`. Rewrite using `[hxe]`. Simplify using `only [map_sum, map_zsmul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply, Finset.mul_sum, mul_smul_comm]`. Conclude with `Subring.sum_mem _ fun j _ => Subring.zsmul_mem _ (key j) _`.
-/
theorem exists_basis (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) F E) (D : 𝓞 F), D ≠ 0 ∧ (∀ i, b i ∈ intOE E) ∧
      ∀ e ∈ intOE E, ∀ i, (D : F) * b.repr e i ∈ (algebraMap (𝓞 F) F).range := by
  classical
  let β : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → E := fun j =>
    algebraMap (𝓞 E) E (NumberField.RingOfIntegers.basis E j)
  have hspanQ : Submodule.span ℚ (Set.range β) = ⊤ := by
    have h := (NumberField.integralBasis E).span_eq
    have hr : Set.range (NumberField.integralBasis E) = Set.range β := by
      ext x
      simp [β, NumberField.integralBasis_apply]
    rw [hr] at h
    exact h
  have hspan : Submodule.span F (Set.range β) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ Submodule.span ℚ (Set.range β) := by rw [hspanQ]; exact Submodule.mem_top
    exact Submodule.span_le_restrictScalars ℚ F _ hx
  obtain ⟨B, hBsub, hBspan, hBli⟩ := exists_linearIndependent F (Set.range β)
  have hBfin : B.Finite := (Set.finite_range β).subset hBsub
  haveI := hBfin.fintype
  let e := Fintype.equivFin B
  let b0 : Module.Basis B F E := Module.Basis.mk hBli (by rw [Subtype.range_coe, hBspan, hspan])
  let b : Module.Basis (Fin (Fintype.card B)) F E := b0.reindex e
  obtain ⟨D, hD⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 F))
    ((Finset.univ : Finset (Module.Free.ChooseBasisIndex ℤ (𝓞 E) × Fin (Fintype.card B))).image
      fun p => b.repr (β p.1) p.2)
  refine ⟨Fintype.card B, b, (D : 𝓞 F), nonZeroDivisors.ne_zero D.2, ?_, ?_⟩
  · intro i
    have hbi : b i = ((e.symm i : B) : E) := by simp [b, b0]
    obtain ⟨j, hj⟩ := hBsub (e.symm i).2
    rw [hbi, ← hj]
    exact RingHom.mem_range.mpr ⟨_, rfl⟩
  · intro x hx i
    obtain ⟨y, rfl⟩ := RingHom.mem_range.mp hx
    have key : ∀ j, ((D : 𝓞 F) : F) * b.repr (β j) i ∈ (algebraMap (𝓞 F) F).range := by
      intro j
      obtain ⟨z, hz⟩ := hD (b.repr (β j) i) (Finset.mem_image.mpr ⟨(j, i), Finset.mem_univ _, rfl⟩)
      refine RingHom.mem_range.mpr ⟨z, ?_⟩
      rw [hz, Algebra.smul_def]
    have hxe : algebraMap (𝓞 E) E y = ∑ j, ((NumberField.RingOfIntegers.basis E).repr y j) • β j := by
      conv_lhs => rw [← (NumberField.RingOfIntegers.basis E).sum_repr y]
      rw [map_sum]
      simp [β, map_zsmul]
    rw [hxe]
    simp only [map_sum, map_zsmul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.coe_smul,
      Pi.smul_apply, Finset.mul_sum, mul_smul_comm]
    exact Subring.sum_mem _ fun j _ => Subring.zsmul_mem _ (key j) _

end Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory

end
