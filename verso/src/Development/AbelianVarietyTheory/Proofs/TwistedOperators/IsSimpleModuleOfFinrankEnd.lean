import Mathlib
import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharOfIsPrimitiveRoot
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldOfRepresentation
open GlobalTheory.GLq Polynomial
open scoped Classical

namespace GlobalTheory.AbsIrrDescent

/- English proof (translation)
Establish `hE : Nontrivial (Module.End R M)` using `Module.nontrivial_of_finrank_eq_succ h`. Establish `hM : Nontrivial M`. Assume the negation of the conclusion as `hM`. Rewrite `hM` using `[not_nontrivial_iff_subsingleton]`. Conclude with `not_subsingleton (Module.End R M) inferInstance`.

Establish `: Nontrivial (Submodule R M)` using `(Submodule.nontrivial_iff R).2 hM`. Use `{ eq_bot_or_eq_top := fun U => ?_ }` and prove the remaining obligations. Take `⟨U', hU⟩` from `exists_isCompl U`. Take `⟨c, hc⟩` from `(finrank_eq_one_iff_of_nonzero' (1 : Module.End R M) one_ne_zero).1 h (U.subtype ∘ₗ U.projectionOnto U' hU)`. Distinguish the cases in `h0 : c = 0`.

Use `left`. Rewrite using `[Submodule.eq_bot_iff]`. Introduce `x hx`. Use `LinearMap.congr_fun hc x` as an intermediate fact. Rewrite `this` using `[h0, zero_smul]`.

Establish `h2 : (U.subtype ∘ₗ U.projectionOnto U' hU) x = x`. Simplify using `using congrArg Subtype.val (Submodule.projectionOnto_apply_left hU ⟨x, hx⟩)`. Rewrite using `[← h2, ← this]`. Both sides reduce to the same expression. Use `right`.

Rewrite using `[Submodule.eq_top_iff']`. Introduce `x`. Use `LinearMap.congr_fun hc (c⁻¹ • x)` as an intermediate fact. Establish `h2 : (c • (1 : Module.End R M)) (c⁻¹ • x) = x`. Simplify using `[smul_smul, h0]`.

Rewrite using `[← h2, this]`. Conclude with `Subtype.property _`.
-/
theorem isSimpleModule_of_finrank_end {k R M : Type} [Field k] [Ring R] [Algebra k R] [AddCommGroup M] [Module R M]
    [Module k M] [IsScalarTower k R M] [SMulCommClass R k M] [IsSemisimpleModule R M]
    (h : Module.finrank k (Module.End R M) = 1) : IsSimpleModule R M := by
  have hE : Nontrivial (Module.End R M) := Module.nontrivial_of_finrank_eq_succ h
  have hM : Nontrivial M := by
    by_contra hM
    rw [not_nontrivial_iff_subsingleton] at hM
    exact not_subsingleton (Module.End R M) inferInstance
  have : Nontrivial (Submodule R M) := (Submodule.nontrivial_iff R).2 hM
  refine { eq_bot_or_eq_top := fun U => ?_ }
  obtain ⟨U', hU⟩ := exists_isCompl U
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : Module.End R M) one_ne_zero).1 h
    (U.subtype ∘ₗ U.projectionOnto U' hU)
  by_cases h0 : c = 0
  · left
    rw [Submodule.eq_bot_iff]
    intro x hx
    have := LinearMap.congr_fun hc x
    rw [h0, zero_smul] at this
    have h2 : (U.subtype ∘ₗ U.projectionOnto U' hU) x = x := by
      simpa using congrArg Subtype.val (Submodule.projectionOnto_apply_left hU ⟨x, hx⟩)
    rw [← h2, ← this]; rfl
  · right
    rw [Submodule.eq_top_iff']
    intro x
    have := LinearMap.congr_fun hc (c⁻¹ • x)
    have h2 : (c • (1 : Module.End R M)) (c⁻¹ • x) = x := by
      simp [smul_smul, h0]
    rw [← h2, this]
    exact Subtype.property _

/- English proof (translation)
Establish `hc : (Nat.card G : k) ≠ 0` using `Nat.cast_ne_zero.2 Nat.card_pos.ne'`. Use `invertibleOfNonzero hc` as an intermediate fact. Establish `: NeZero (Nat.card G : k)` using `⟨hc⟩`. Establish `h` using `Representation.card_inv_mul_sum_char_mul_char_eq_finrank ρ ρ`. Rewrite `h` using `[hn, inv_mul_cancel₀ hc, eq_comm, Nat.cast_eq_one]`.

Rewrite using `[Representation.irreducible_iff_isSimpleModule_asModule]`. Use `isSimpleModule_of_finrank_end (k := k) ?_` and prove the remaining obligations. Rewrite using `[← h]`. Conclude with `(Representation.IntertwiningMap.equivAlgEnd (ρ := ρ)).toLinearEquiv.finrank_eq.symm`.
-/
theorem isIrreducible_of_norm_one {k G V : Type} [Field k] [CharZero k] [Group G] [Fintype G] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] (ρ : Representation k G V)
    (hn : ∑ g, ρ.character g * ρ.character g⁻¹ = (Nat.card G : k)) : ρ.IsIrreducible := by
  have hc : (Nat.card G : k) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have := invertibleOfNonzero hc
  have : NeZero (Nat.card G : k) := ⟨hc⟩
  have h := Representation.card_inv_mul_sum_char_mul_char_eq_finrank ρ ρ
  rw [hn, inv_mul_cancel₀ hc, eq_comm, Nat.cast_eq_one] at h
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  refine isSimpleModule_of_finrank_end (k := k) ?_
  rw [← h]
  exact (Representation.IntertwiningMap.equivAlgEnd (ρ := ρ)).toLinearEquiv.finrank_eq.symm

/- English proof (translation)
Introduce `K _ σ G _ _ χ h`. Take `⟨V, hV, hχ⟩` from `h`. Use `haveI : CharZero K := σ.charZero`. Use `letI : Algebra K ℂ := σ.toAlgebra`. Set `τ : AlgebraicClosure K →ₐ[K] ℂ` to `IsAlgClosed.lift`.

Use `letI : Algebra (AlgebraicClosure K) ℂ := τ.toRingHom.toAlgebra`. Establish `hτ : ∀ x : K, algebraMap (AlgebraicClosure K) ℂ (algebraMap K (AlgebraicClosure K) x) = σ x` using `fun x => τ.commutes x`. Establish `hinj : Function.Injective (algebraMap (AlgebraicClosure K) ℂ)` using `RingHom.injective _`. Establish `hm : Nat.card G ≠ 0` using `Nat.card_pos.ne'`. Use `haveI : NeZero (Nat.card G) := ⟨hm⟩`.

Use `haveI : NeZero (Nat.card G : AlgebraicClosure K) := ⟨Nat.cast_ne_zero.2 hm⟩`. Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) (Nat.card G)`. Establish `hch : GlobalTheory.BI.IsChar ℂ ℂ (fun t => σ (χ t))`. Establish `h` using `(GlobalTheory.BI.isChar_and_isIrrChar_of_rep ℂ ℂ G V V.ρ).1`. Establish `e : (fun t => σ (χ t)) = fun g => algebraMap ℂ ℂ (Representation.character V.ρ g)`.

Use function extensionality and compare the values at `g`. Conclude with `(hχ g).symm`. Rewrite using `[e]`. Conclude with `h`. Take `⟨n, ρ, hρ⟩` from `GlobalTheory.BI.isChar_of_isPrimitiveRoot (AlgebraicClosure K) ℂ (Nat.card G) ζ hm hζ G (fun g => pow_card_eq_one') _ hch`.

Establish `hρ' : ∀ t, ρ.character t = algebraMap K (AlgebraicClosure K) (χ t)` using `fun t => hinj (by rw [hτ]; exact (hρ t).symm)`. Use `⟨n, ρ, isIrreducible_of_norm_one ρ (hinj ?_), hρ'⟩` and prove the remaining obligations. Establish `hn` using `(FDRep.simple_iff_char_is_norm_one V).1 hV`. Rewrite using `[map_natCast, ← hn, map_sum]`. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations.

Rewrite using `[map_mul, hρ', hρ', hτ, hτ, hχ, hχ]`.
-/
theorem isAbsIrrChar_of_isIrr : ∀ (K : Type) [Field K] (σ : K →+* ℂ) (G : Type) [Group G] [Fintype G] (χ : G → K), IsIrr (fun t => σ (χ t)) → Formalism.L2.DIV.IsAbsIrrChar χ := by
  intro K _ σ G _ _ χ h
  obtain ⟨V, hV, hχ⟩ := h
  haveI : CharZero K := σ.charZero
  letI : Algebra K ℂ := σ.toAlgebra
  let τ : AlgebraicClosure K →ₐ[K] ℂ := IsAlgClosed.lift
  letI : Algebra (AlgebraicClosure K) ℂ := τ.toRingHom.toAlgebra
  have hτ : ∀ x : K, algebraMap (AlgebraicClosure K) ℂ (algebraMap K (AlgebraicClosure K) x) = σ x :=
    fun x => τ.commutes x
  have hinj : Function.Injective (algebraMap (AlgebraicClosure K) ℂ) := RingHom.injective _
  have hm : Nat.card G ≠ 0 := Nat.card_pos.ne'
  haveI : NeZero (Nat.card G) := ⟨hm⟩
  haveI : NeZero (Nat.card G : AlgebraicClosure K) := ⟨Nat.cast_ne_zero.2 hm⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) (Nat.card G)
  have hch : GlobalTheory.BI.IsChar ℂ ℂ (fun t => σ (χ t)) := by
    have h := (GlobalTheory.BI.isChar_and_isIrrChar_of_rep ℂ ℂ G V V.ρ).1
    have e : (fun t => σ (χ t)) = fun g => algebraMap ℂ ℂ (Representation.character V.ρ g) := by
      funext g
      exact (hχ g).symm
    rw [e]
    exact h
  obtain ⟨n, ρ, hρ⟩ := GlobalTheory.BI.isChar_of_isPrimitiveRoot (AlgebraicClosure K) ℂ (Nat.card G) ζ hm hζ G
    (fun g => pow_card_eq_one') _ hch
  have hρ' : ∀ t, ρ.character t = algebraMap K (AlgebraicClosure K) (χ t) := fun t =>
    hinj (by rw [hτ]; exact (hρ t).symm)
  refine ⟨n, ρ, isIrreducible_of_norm_one ρ (hinj ?_), hρ'⟩
  have hn := (FDRep.simple_iff_char_is_norm_one V).1 hV
  rw [map_natCast, ← hn, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [map_mul, hρ', hρ', hτ, hτ, hχ, hχ]

end GlobalTheory.AbsIrrDescent
