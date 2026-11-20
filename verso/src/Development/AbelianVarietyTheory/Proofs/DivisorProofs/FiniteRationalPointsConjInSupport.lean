import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPtHomApply
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TraceBlocks
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

/- English proof (translation)
Introduce `G H _ _ ι hι K' F hF hT x hfin`. Establish `key : ∀ g : G, F ((g : G ⧸ K').out) = F g`. Introduce `g`. Take `⟨k, hk⟩` from `QuotientGroup.mk_out_eq_mul K' g`. Rewrite using `[hk]`.

Conclude with `hF _ k.2 g`. Establish `hL : (ι ⁻¹' ((ι.range ⊓ K'.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G)).Finite` using `(Set.finite_coe_iff.mp hfin).preimage hι.injOn`. Use `Set.Finite.of_finite_fibers (fun h : H => ((x⁻¹ * ι h * x : G) : G ⧸ K')) (hT.subset ?_) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨h, hh, rfl⟩`. Simplify using `only [Set.mem_setOf_eq] at hh ⊢`.

Rewrite using `[key]` and apply the resulting hypothesis. Introduce and unpack `_ ⟨h0, -, rfl⟩`. Use `(hL.image (fun k => h0 * k)).subset ?_` and prove the remaining obligations. Introduce and unpack `h ⟨-, hh⟩`. Use `⟨h0⁻¹ * h, ?_, by simp⟩` and prove the remaining obligations.

Simplify using `only [Set.mem_preimage, Set.mem_singleton_iff] at hh`. Establish `hk : (x⁻¹ * ι h0 * x)⁻¹ * (x⁻¹ * ι h * x) ∈ K'` using `QuotientGroup.eq.mp hh.symm`. Establish `hk' : x⁻¹ * ι (h0⁻¹ * h) * x ∈ K'`. Use `hk using 1` and compare the differences between its conclusion and the goal. Simplify using `[map_mul, map_inv, mul_assoc]`.

Simplify using `only [Set.mem_preimage, SetLike.mem_coe, Subgroup.mem_inf, MonoidHom.mem_range, exists_apply_eq_apply, true_and, Subgroup.mem_map]`. Use `⟨_, hk', ?_⟩` and prove the remaining obligations. Simplify using `[MulAut.conj_apply, mul_assoc]`.
-/
theorem finite_support_conj_points : ∀ (G H : Type) [Group G] [Group H] (ι : H →* G), Function.Injective ι → ∀ (K' : Subgroup G) (F : G → ℂ), (∀ k ∈ K', ∀ x, F (x * k) = F x) → {q : G ⧸ K' | F q.out ≠ 0}.Finite → ∀ x : G, Finite (ι.range ⊓ K'.map (MulAut.conj x).toMonoidHom : Subgroup G) → {h : H | F (x⁻¹ * ι h * x) ≠ 0}.Finite := by
  intro G H _ _ ι hι K' F hF hT x hfin
  have key : ∀ g : G, F ((g : G ⧸ K').out) = F g := by
    intro g
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K' g
    rw [hk]; exact hF _ k.2 g
  have hL : (ι ⁻¹' ((ι.range ⊓ K'.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G)).Finite :=
    (Set.finite_coe_iff.mp hfin).preimage hι.injOn
  refine Set.Finite.of_finite_fibers (fun h : H => ((x⁻¹ * ι h * x : G) : G ⧸ K')) (hT.subset ?_) ?_
  · rintro _ ⟨h, hh, rfl⟩
    simp only [Set.mem_setOf_eq] at hh ⊢
    rwa [key]
  · rintro _ ⟨h0, -, rfl⟩
    refine (hL.image (fun k => h0 * k)).subset ?_
    rintro h ⟨-, hh⟩
    refine ⟨h0⁻¹ * h, ?_, by simp⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hh
    have hk : (x⁻¹ * ι h0 * x)⁻¹ * (x⁻¹ * ι h * x) ∈ K' := QuotientGroup.eq.mp hh.symm
    have hk' : x⁻¹ * ι (h0⁻¹ * h) * x ∈ K' := by
      convert hk using 1
      simp [map_mul, map_inv, mul_assoc]
    simp only [Set.mem_preimage, SetLike.mem_coe, Subgroup.mem_inf, MonoidHom.mem_range,
      exists_apply_eq_apply, true_and, Subgroup.mem_map]
    refine ⟨_, hk', ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

end GlobalTheory
