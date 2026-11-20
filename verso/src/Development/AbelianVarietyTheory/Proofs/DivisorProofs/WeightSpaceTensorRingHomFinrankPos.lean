import Mathlib
open scoped TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce `k _ _ C _ _ _ χ`. Set `φ : k ⊗[ℤ] C →ₐ[k] k` to `Algebra.TensorProduct.lift (Algebra.ofId k k) χ.toIntAlgHom (fun _ _ => Commute.all _ _)`. Establish `hφs : Function.Surjective φ` using `fun a => ⟨algebraMap k (k ⊗[ℤ] C) a, by rw [φ.commutes]; rfl⟩`. Set `m : Ideal (k ⊗[ℤ] C)` to `RingHom.ker φ`. Establish `hm : m.IsMaximal` using `RingHom.ker_isMaximal_of_surjective φ hφs`.

Use `haveI : IsArtinianRing (k ⊗[ℤ] C) := IsArtinianRing.of_finite k (k ⊗[ℤ] C)`. Take `⟨N, hN⟩` from `IsArtinian.monotone_stabilizes (⟨fun j => OrderDual.toDual (m ^ j), fun a b h => Ideal.pow_le_pow_right h⟩ : ℕ →o (Ideal (k ⊗[ℤ] C))ᵒᵈ)`. Establish `hst : ∀ j, N ≤ j → m ^ N = m ^ j` using `fun j hj => hN j hj`. Establish `hJJ : IsIdempotentElem (m ^ (N + 1))` using `by show m ^ (N + 1) * m ^ (N + 1) = m ^ (N + 1)`. Rewrite using `[← pow_add, ← hst (N + 1 + (N + 1)) (by omega), hst (N + 1) (by omega)]`.

Take `⟨e, he, hJe⟩` from `(Ideal.isIdempotentElem_iff_of_fg _ (IsNoetherian.noetherian (m ^ (N + 1)))).mp hJJ`. Establish `hJe' : m ^ (N + 1) = Ideal.span {e}` using `hJe`. Establish `hv : (1 - e : k ⊗[ℤ] C) ≠ 0`. Introduce `h`. Establish `h1 : e = 1` using `(sub_eq_zero.mp h).symm`.

Establish `: m ^ (N + 1) = ⊤` using `by rw [hJe', h1, Ideal.span_singleton_one]`. Conclude with `hm.ne_top (top_le_iff.mp (this ▸ Ideal.pow_le_self (by omega)))`. Establish `key : ∀ x ∈ m, x ^ (N + 1) * (1 - e) = 0`. Introduce `x hx`. Establish `hx' : x ^ (N + 1) ∈ Ideal.span {e}` using `hJe' ▸ Ideal.pow_mem_pow hx (N + 1)`.

Take `⟨a, ha⟩` from `Ideal.mem_span_singleton'.mp hx'`. Rewrite using `[← ha, mul_assoc, mul_sub, mul_one, he.eq, sub_self, mul_zero]`. Use `lt_of_lt_of_le Nat.zero_lt_one (Submodule.one_le_finrank_iff.2 ?_)` and prove the remaining obligations. Rewrite using `[Submodule.ne_bot_iff]`. Use `⟨1 - e, ?_, hv⟩` and prove the remaining obligations.

Rewrite using `[Submodule.mem_iInf]`. Introduce `c`. Rewrite using `[Module.End.mem_maxGenEigenspace]`. Use `⟨N + 1, ?_⟩` and prove the remaining obligations. Set `x : k ⊗[ℤ] C` to `(1 : k) ⊗ₜ c - algebraMap k (k ⊗[ℤ] C) (χ c)`.

Establish `hxm : x ∈ m`. Simplify using `[m, x, φ, RingHom.mem_ker]`. Establish `hf : (((Algebra.lmul k (k ⊗[ℤ] C)).toRingHom.comp (Algebra.TensorProduct.includeRight : C →ₐ[ℤ] k ⊗[ℤ] C).toRingHom) c) - χ c • (1 : Module.End k (k ⊗[ℤ] C)) = Algebra.lmul k (k ⊗[ℤ] C) x`. Use extensionality with `y`. Simplify using `[x, sub_mul, Algebra.smul_def]`.

Rewrite using `[hf, ← map_pow]`. Simplify using `using key x hxm`.
-/
theorem weightSpace_tensor_ringHom_pos : ∀ (k : Type) [Field k] [IsAlgClosed k] (C : Type) [CommRing C] [Module.Free ℤ C] [Module.Finite ℤ C] (χ : C →+* k), 0 < Module.finrank k ↥(⨅ c : C, (((Algebra.lmul k (k ⊗[ℤ] C)).toRingHom.comp (Algebra.TensorProduct.includeRight : C →ₐ[ℤ] k ⊗[ℤ] C).toRingHom) c).maxGenEigenspace (χ c)) := by
  intro k _ _ C _ _ _ χ
  let φ : k ⊗[ℤ] C →ₐ[k] k :=
    Algebra.TensorProduct.lift (Algebra.ofId k k) χ.toIntAlgHom (fun _ _ => Commute.all _ _)
  have hφs : Function.Surjective φ := fun a => ⟨algebraMap k (k ⊗[ℤ] C) a, by rw [φ.commutes]; rfl⟩
  let m : Ideal (k ⊗[ℤ] C) := RingHom.ker φ
  have hm : m.IsMaximal := RingHom.ker_isMaximal_of_surjective φ hφs
  haveI : IsArtinianRing (k ⊗[ℤ] C) := IsArtinianRing.of_finite k (k ⊗[ℤ] C)
  obtain ⟨N, hN⟩ := IsArtinian.monotone_stabilizes
    (⟨fun j => OrderDual.toDual (m ^ j), fun a b h => Ideal.pow_le_pow_right h⟩ :
      ℕ →o (Ideal (k ⊗[ℤ] C))ᵒᵈ)
  have hst : ∀ j, N ≤ j → m ^ N = m ^ j := fun j hj => hN j hj
  have hJJ : IsIdempotentElem (m ^ (N + 1)) := by
    show m ^ (N + 1) * m ^ (N + 1) = m ^ (N + 1)
    rw [← pow_add, ← hst (N + 1 + (N + 1)) (by omega), hst (N + 1) (by omega)]
  obtain ⟨e, he, hJe⟩ :=
    (Ideal.isIdempotentElem_iff_of_fg _ (IsNoetherian.noetherian (m ^ (N + 1)))).mp hJJ
  have hJe' : m ^ (N + 1) = Ideal.span {e} := hJe
  have hv : (1 - e : k ⊗[ℤ] C) ≠ 0 := by
    intro h
    have h1 : e = 1 := (sub_eq_zero.mp h).symm
    have : m ^ (N + 1) = ⊤ := by rw [hJe', h1, Ideal.span_singleton_one]
    exact hm.ne_top (top_le_iff.mp (this ▸ Ideal.pow_le_self (by omega)))
  have key : ∀ x ∈ m, x ^ (N + 1) * (1 - e) = 0 := by
    intro x hx
    have hx' : x ^ (N + 1) ∈ Ideal.span {e} := hJe' ▸ Ideal.pow_mem_pow hx (N + 1)
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hx'
    rw [← ha, mul_assoc, mul_sub, mul_one, he.eq, sub_self, mul_zero]
  refine lt_of_lt_of_le Nat.zero_lt_one (Submodule.one_le_finrank_iff.2 ?_)
  rw [Submodule.ne_bot_iff]
  refine ⟨1 - e, ?_, hv⟩
  rw [Submodule.mem_iInf]
  intro c
  rw [Module.End.mem_maxGenEigenspace]
  refine ⟨N + 1, ?_⟩
  let x : k ⊗[ℤ] C := (1 : k) ⊗ₜ c - algebraMap k (k ⊗[ℤ] C) (χ c)
  have hxm : x ∈ m := by
    simp [m, x, φ, RingHom.mem_ker]
  have hf : (((Algebra.lmul k (k ⊗[ℤ] C)).toRingHom.comp
      (Algebra.TensorProduct.includeRight : C →ₐ[ℤ] k ⊗[ℤ] C).toRingHom) c) - χ c • (1 : Module.End k (k ⊗[ℤ] C))
      = Algebra.lmul k (k ⊗[ℤ] C) x := by
    ext y
    simp [x, sub_mul, Algebra.smul_def]
  rw [hf, ← map_pow]
  simpa using key x hxm

end GlobalTheory
