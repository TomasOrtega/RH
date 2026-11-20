import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BinQuadRepresentsUnitOfFiniteReduced
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
open IsDedekindDomain

namespace GlobalTheory

/- English proof (translation)
Use `set J : Ideal A := (⊥ : Ideal A).jacobson with hJ`. Establish `hm : ∀ m ∈ IsLocalRing.maximalIdeal O, algebraMap O A m ∈ J`. Introduce `m hm`. Rewrite using `[hJ, Ideal.jacobson, Ideal.mem_sInf]`. Introduce and unpack `M ⟨-, hM⟩`.

Establish `: (M.comap (algebraMap O A)).IsMaximal` using `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M`. Establish `h` using `IsLocalRing.eq_maximalIdeal this`. Establish `: m ∈ M.comap (algebraMap O A)` using `h ▸ hm`. Conclude with `this`. Establish `hfin : Module.Finite O (A ⧸ J)` using `Module.Finite.of_surjective (Ideal.Quotient.mkₐ O J).toLinearMap Ideal.Quotient.mk_surjective`.

Take `⟨n, s, hs⟩` from `Module.Finite.exists_fin (R := O) (M := A ⧸ J)`. Establish `hsurj : Function.Surjective (IsLocalRing.residue O)` using `Ideal.Quotient.mk_surjective`. Set `f : (Fin n → IsLocalRing.ResidueField O) → A ⧸ J` to `fun y ↦ ∑ i, Function.surjInv hsurj (y i) • s i`. Establish `: Function.Surjective f`. Introduce `q`.

Establish `hq : q ∈ Submodule.span O (Set.range s)` using `hs ▸ Submodule.mem_top`. Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun O).1 hq`. Use `⟨fun i ↦ IsLocalRing.residue O (c i), ?_⟩` and prove the remaining obligations. Simplify using `only [f]`. Use `Finset.sum_congr rfl fun i _ ↦ ?_` and prove the remaining obligations.

Establish `hd : Function.surjInv hsurj (IsLocalRing.residue O (c i)) - c i ∈ IsLocalRing.maximalIdeal O`. Rewrite using `[← IsLocalRing.residue_eq_zero_iff, map_sub, Function.surjInv_eq hsurj, sub_self]`. Rewrite using `[← sub_eq_zero, ← sub_smul, Algebra.smul_def]`. Establish `h0 : algebraMap O (A ⧸ J) (Function.surjInv hsurj (IsLocalRing.residue O (c i)) - c i) = 0`. Rewrite using `[IsScalarTower.algebraMap_apply O A (A ⧸ J), Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `hm _ hd`. Rewrite using `[h0, zero_mul]`. Conclude with `Finite.of_surjective f this`.
-/
theorem finite_quotient_jacobson_of_finite_residueField (O : Type) [CommRing O] [IsLocalRing O]
    [Finite (IsLocalRing.ResidueField O)] (A : Type) [CommRing A] [Algebra O A]
    [Module.Finite O A] : Finite (A ⧸ (⊥ : Ideal A).jacobson) := by
  set J : Ideal A := (⊥ : Ideal A).jacobson with hJ

  have hm : ∀ m ∈ IsLocalRing.maximalIdeal O, algebraMap O A m ∈ J := by
    intro m hm
    rw [hJ, Ideal.jacobson, Ideal.mem_sInf]
    rintro M ⟨-, hM⟩
    have : (M.comap (algebraMap O A)).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M
    have h := IsLocalRing.eq_maximalIdeal this
    have : m ∈ M.comap (algebraMap O A) := h ▸ hm
    exact this
  have hfin : Module.Finite O (A ⧸ J) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ O J).toLinearMap Ideal.Quotient.mk_surjective
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := O) (M := A ⧸ J)
  have hsurj : Function.Surjective (IsLocalRing.residue O) := Ideal.Quotient.mk_surjective
  let f : (Fin n → IsLocalRing.ResidueField O) → A ⧸ J :=
    fun y ↦ ∑ i, Function.surjInv hsurj (y i) • s i
  have : Function.Surjective f := by
    intro q
    have hq : q ∈ Submodule.span O (Set.range s) := hs ▸ Submodule.mem_top
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 hq
    refine ⟨fun i ↦ IsLocalRing.residue O (c i), ?_⟩
    simp only [f]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hd : Function.surjInv hsurj (IsLocalRing.residue O (c i)) - c i ∈
        IsLocalRing.maximalIdeal O := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, Function.surjInv_eq hsurj, sub_self]
    rw [← sub_eq_zero, ← sub_smul, Algebra.smul_def]
    have h0 : algebraMap O (A ⧸ J) (Function.surjInv hsurj (IsLocalRing.residue O (c i)) - c i)
        = 0 := by
      rw [IsScalarTower.algebraMap_apply O A (A ⧸ J), Ideal.Quotient.algebraMap_eq,
        Ideal.Quotient.eq_zero_iff_mem]
      exact hm _ hd
    rw [h0, zero_mul]
  exact Finite.of_surjective f this

/- English proof (translation)
Introduce `O _ _ _ A _ _ _ τ hτ θ hθ a ha hτa`. Use `set J : Ideal A := (⊥ : Ideal A).jacobson with hJ`. Establish `: Finite (A ⧸ J)` using `finite_quotient_jacobson_of_finite_residueField O A`. Establish `: IsReduced (A ⧸ J)`. Use `⟨fun x ⟨k, hk⟩ ↦ ?_⟩` and prove the remaining obligations.

Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Rewrite `hk` using `[← map_pow, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.isRadical_jacobson ⊥ ⟨k, hk⟩)`. Establish `hτJ : J ≤ J.comap τ`. Introduce `x hx`.

Rewrite `*` using `[Ideal.mem_comap, hJ, Ideal.mem_jacobson_bot]`. Introduce `b`. Establish `h` using `(hx (τ b)).map τ`. Simplify `h` using `[hτ]`. Set `τ' : A ⧸ J →+* A ⧸ J` to `Ideal.quotientMap J τ hτJ`.

Establish `hτ' : ∀ x, τ' (Ideal.Quotient.mk J x) = Ideal.Quotient.mk J (τ x)` using `fun x ↦ Ideal.quotientMap_mk`. Establish `hinv : ∀ x, τ' (τ' x) = x`. Introduce `x`. Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Rewrite using `[hτ', hτ', hτ]`.

Take `⟨c, hc⟩` from `norm_surj_of_finite_reduced_involution (A ⧸ J) τ' hinv (Ideal.Quotient.mk J θ) (by rw [hτ', ← map_sub]; exact hθ.map _) (Ideal.Quotient.mk J a) (ha.map _) (by rw [hτ', hτa])`. Take `⟨t, rfl⟩` from `Ideal.Quotient.mk_surjective c`. Use `⟨t, isUnit_of_isUnit_mk_of_le_jacobson le_rfl ?_, ?_⟩` and prove the remaining obligations. Establish `: IsUnit (τ' (Ideal.Quotient.mk J t) * Ideal.Quotient.mk J t)` using `hc ▸ ha.map _`. Conclude with `isUnit_of_mul_isUnit_right this`.

Rewrite using `[← Ideal.Quotient.eq, map_mul, ← hτ', mul_comm, hc]`.
-/
theorem exists_isUnit_mul_sub_mem_jacobson_of_finite_residueField :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [Finite (IsLocalRing.ResidueField O)] (A : Type)
      [CommRing A] [Algebra O A] [Module.Finite O A] (τ : A →+* A), (∀ a, τ (τ a) = a) →
      ∀ θ : A, IsUnit (θ - τ θ) → ∀ a : A, IsUnit a → τ a = a →
      ∃ t : A, IsUnit t ∧ t * τ t - a ∈ (⊥ : Ideal A).jacobson := by
  intro O _ _ _ A _ _ _ τ hτ θ hθ a ha hτa
  set J : Ideal A := (⊥ : Ideal A).jacobson with hJ
  have : Finite (A ⧸ J) := finite_quotient_jacobson_of_finite_residueField O A
  have : IsReduced (A ⧸ J) := by
    refine ⟨fun x ⟨k, hk⟩ ↦ ?_⟩
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem] at hk
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.isRadical_jacobson ⊥ ⟨k, hk⟩)
  have hτJ : J ≤ J.comap τ := by
    intro x hx
    rw [Ideal.mem_comap, hJ, Ideal.mem_jacobson_bot] at *
    intro b
    have h := (hx (τ b)).map τ
    simpa [hτ] using h
  let τ' : A ⧸ J →+* A ⧸ J := Ideal.quotientMap J τ hτJ
  have hτ' : ∀ x, τ' (Ideal.Quotient.mk J x) = Ideal.Quotient.mk J (τ x) := fun x ↦
    Ideal.quotientMap_mk
  have hinv : ∀ x, τ' (τ' x) = x := by
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hτ', hτ', hτ]
  obtain ⟨c, hc⟩ := norm_surj_of_finite_reduced_involution (A ⧸ J) τ' hinv
    (Ideal.Quotient.mk J θ) (by rw [hτ', ← map_sub]; exact hθ.map _)
    (Ideal.Quotient.mk J a) (ha.map _) (by rw [hτ', hτa])
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective c
  refine ⟨t, isUnit_of_isUnit_mk_of_le_jacobson le_rfl ?_, ?_⟩
  · have : IsUnit (τ' (Ideal.Quotient.mk J t) * Ideal.Quotient.mk J t) := hc ▸ ha.map _
    exact isUnit_of_mul_isUnit_right this
  · rw [← Ideal.Quotient.eq, map_mul, ← hτ', mul_comm, hc]

end GlobalTheory
