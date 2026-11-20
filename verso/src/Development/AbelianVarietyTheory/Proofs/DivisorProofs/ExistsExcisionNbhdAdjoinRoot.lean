import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdSelf
open GlobalTheory.EtC Polynomial

namespace GlobalTheory.EtC

/- English proof (translation)
Introduce `A _ h q hq ε r hε hr`. Break down `Nat.eq_zero_or_pos q with hq0 | hq0` into its components or cases. Substitute `hq0` using the available equality. Establish `: Subsingleton A`. Simplify using `only [Nat.cast_zero, isUnit_zero_iff] at hq`.

Conclude with `subsingleton_of_zero_eq_one hq`. Conclude with `⟨A, inferInstance, inferInstance, isExcisionNbhd_self A h, 1, Subsingleton.elim _ _⟩`. Take `⟨m, rfl⟩ : ∃ m, q = m + 1` from `⟨q - 1, by omega⟩`. Use `set qi : A := ↑hq.unit⁻¹`. Use `set ei : A := ↑hε.unit⁻¹`.

Establish `hq1 : ((m + 1 : ℕ) : A) * qi = 1` using `hq.mul_val_inv`. Establish `he1 : ε * ei = 1` using `hε.mul_val_inv`. Set `g : A[X]` to `∑ i ∈ Finset.range (m + 1), X ^ i * C r ^ (m + 1 - 1 - i)`. Set `P : StandardEtalePair A` to `{ f := X ^ (m + 1) - C ε monic_f := monic_X_pow_sub_C ε (by omega) g := g cond := ⟨C (qi * ei) * X, - C ei, 0, by`. Establish `a1 : C ((m + 1 : ℕ) : A) * C qi = 1` using `by rw [← C_mul, hq1, C_1]`.

Establish `a2 : C ε * C ei = 1` using `by rw [← C_mul, he1, C_1]`. Simplify using `only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, pow_zero, C_mul, Nat.add_sub_cancel]`. Take the linear combination `(X ^ (m + 1) * C ei) * a1 + a2⟩ }`. Set `I : Ideal A` to `Ideal.span {h}`. Establish `hmap : P.HasMap (Ideal.Quotient.mk I r)`.

Prove the components needed by the constructor for the conclusion. Use `show aeval _ (X ^ (m + 1) - C ε) = 0`. Rewrite using `[map_sub, map_pow, aeval_X, aeval_C, Ideal.Quotient.algebraMap_eq, ← map_pow, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]`. Simplify using `using I.neg_mem hr`. Use `show IsUnit (aeval _ g)`.

Simplify using `only [g, map_sum, map_mul, map_pow, aeval_X, aeval_C, Ideal.Quotient.algebraMap_eq]`. Rewrite using `[geom_sum₂_self]`. Use `IsUnit.mul ?_ (IsUnit.pow _ ?_)` and prove the remaining obligations. Simplify using `using hq.map (Ideal.Quotient.mk I)`. Rewrite using `[← isUnit_pow_iff (n := m + 1) (by omega), ← map_pow]`.

Establish `: Ideal.Quotient.mk I (r ^ (m + 1)) = Ideal.Quotient.mk I ε`. Rewrite using `[Ideal.Quotient.eq]`. Simplify using `using I.neg_mem hr`. Rewrite using `[this]`. Conclude with `hε.map _`.

Set `φ : P.Ring →ₐ[A] A ⧸ I` to `P.lift _ hmap`. Set `J : Ideal P.Ring` to `Ideal.span {algebraMap A P.Ring h}`. Establish `hgu : IsUnit (aeval P.X g)` using `P.hasMap_X.2`. Establish `e2 : P.X ^ (m + 1) = algebraMap A P.Ring ε`. Establish `: aeval P.X (X ^ (m + 1) - C ε) = 0` using `P.hasMap_X.1`.

Simplify `this` using `[sub_eq_zero]`. Establish `hX : P.X - algebraMap A P.Ring r ∈ J`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.mp hr`. Establish `key : (P.X - algebraMap A P.Ring r) * aeval P.X g = algebraMap A P.Ring c * algebraMap A P.Ring h`. Establish `e1 : aeval P.X g * (P.X - algebraMap A P.Ring r) = P.X ^ (m + 1) - (algebraMap A P.Ring r) ^ (m + 1)`.

Simplify using `only [g, map_sum, map_mul, map_pow, aeval_X, aeval_C]`. Conclude with `geom_sum₂_mul _ _ _`. Rewrite using `[mul_comm, e1, e2, ← map_pow, ← map_sub, ← hc, map_mul]`. Rewrite using `[Ideal.mem_span_singleton']`. Use `⟨algebraMap A P.Ring c * ↑hgu.unit⁻¹, ?_⟩` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Set `ψ : A ⧸ I →ₐ[A] P.Ring ⧸ J` to `Ideal.Quotient.liftₐ I (Algebra.ofId A (P.Ring ⧸ J)) (by`. Introduce `a ha`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.mp ha`. Rewrite using `[Algebra.ofId_apply, IsScalarTower.algebraMap_apply A P.Ring (P.Ring ⧸ J), Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem, map_mul]`.

Conclude with `J.mul_mem_left _ (Ideal.mem_span_singleton_self _))`. Establish `hψ : ∀ a : A, ψ (Ideal.Quotient.mk I a) = Ideal.Quotient.mk J (algebraMap A P.Ring a)`. Introduce `a`. Use `first`. Consider the case `rfl`.

Consider the case `simp [ψ, Ideal.Quotient.liftₐ_apply, IsScalarTower.algebraMap_apply A P.Ring (P.Ring ⧸ J)]`. Establish `hcomp : ψ.comp φ = Ideal.Quotient.mkₐ A J`. Apply `P.hom_ext` to reduce the goal to its premises. Simplify using `only [AlgHom.comp_apply, φ, StandardEtalePair.lift_X, Ideal.Quotient.mkₐ_eq_mk]`. Use `show ψ (Ideal.Quotient.mk I r) = _`.

Rewrite using `[hψ, Ideal.Quotient.eq]`. Use `first`. Consider the case `exact hX`. Consider the case `(have := J.neg_mem hX; rwa [neg_sub] at this)`. Use `⟨P.Ring, inferInstance, inferInstance, ⟨inferInstance, ?_, ?_⟩, P.X, e2.symm⟩` and prove the remaining obligations.

Introduce `a'`. Take `⟨a, ha⟩` from `Ideal.Quotient.mk_surjective (φ a')`. Use `⟨a, ?_⟩` and prove the remaining obligations. Establish `h1` using `congrArg (fun F => F a') hcomp`. Simplify using `only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, ← ha] at h1`.

Rewrite `h1` using `[hψ]`. Conclude with `Ideal.Quotient.eq.mp h1.symm`. Introduce `a ha`. Take `⟨y, hy⟩` from `Ideal.mem_span_singleton'.mp ha`. Establish `h1` using `congrArg φ hy`.

Establish `hh0 : Ideal.Quotient.mk I h = 0` using `Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)`. Simplify using `only [map_mul, AlgHom.commutes, Ideal.Quotient.algebraMap_eq] at h1`. Rewrite `h1` using `[hh0, mul_zero]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.mp h1.symm`.
-/
theorem exists_excisionNbhd_adjoin_root : ∀ (A : Type) [CommRing A] (h : A) (q : ℕ), IsUnit (q : A) →
    ∀ ε r : A, IsUnit ε → ε - r ^ q ∈ Ideal.span {h} → ∃ (A' : Type) (_ : CommRing A') (_ : Algebra A A'),
      IsExcisionNbhd A A' h ∧ ∃ x : A', algebraMap A A' ε = x ^ q := by
  intro A _ h q hq ε r hε hr
  rcases Nat.eq_zero_or_pos q with hq0 | hq0
  · subst hq0
    have : Subsingleton A := by
      simp only [Nat.cast_zero, isUnit_zero_iff] at hq
      exact subsingleton_of_zero_eq_one hq
    exact ⟨A, inferInstance, inferInstance, isExcisionNbhd_self A h, 1, Subsingleton.elim _ _⟩
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  set qi : A := ↑hq.unit⁻¹
  set ei : A := ↑hε.unit⁻¹
  have hq1 : ((m + 1 : ℕ) : A) * qi = 1 := hq.mul_val_inv
  have he1 : ε * ei = 1 := hε.mul_val_inv
  let g : A[X] := ∑ i ∈ Finset.range (m + 1), X ^ i * C r ^ (m + 1 - 1 - i)
  let P : StandardEtalePair A :=
    { f := X ^ (m + 1) - C ε
      monic_f := monic_X_pow_sub_C ε (by omega)
      g := g
      cond := ⟨C (qi * ei) * X, - C ei, 0, by
        have a1 : C ((m + 1 : ℕ) : A) * C qi = 1 := by rw [← C_mul, hq1, C_1]
        have a2 : C ε * C ei = 1 := by rw [← C_mul, he1, C_1]
        simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, pow_zero, C_mul,
          Nat.add_sub_cancel]
        linear_combination (X ^ (m + 1) * C ei) * a1 + a2⟩ }
  let I : Ideal A := Ideal.span {h}
  have hmap : P.HasMap (Ideal.Quotient.mk I r) := by
    constructor
    · show aeval _ (X ^ (m + 1) - C ε) = 0
      rw [map_sub, map_pow, aeval_X, aeval_C, Ideal.Quotient.algebraMap_eq, ← map_pow, ← map_sub,
        Ideal.Quotient.eq_zero_iff_mem]
      simpa using I.neg_mem hr
    · show IsUnit (aeval _ g)
      simp only [g, map_sum, map_mul, map_pow, aeval_X, aeval_C, Ideal.Quotient.algebraMap_eq]
      rw [geom_sum₂_self]
      refine IsUnit.mul ?_ (IsUnit.pow _ ?_)
      · simpa using hq.map (Ideal.Quotient.mk I)
      · rw [← isUnit_pow_iff (n := m + 1) (by omega), ← map_pow]
        have : Ideal.Quotient.mk I (r ^ (m + 1)) = Ideal.Quotient.mk I ε := by
          rw [Ideal.Quotient.eq]; simpa using I.neg_mem hr
        rw [this]; exact hε.map _
  let φ : P.Ring →ₐ[A] A ⧸ I := P.lift _ hmap
  let J : Ideal P.Ring := Ideal.span {algebraMap A P.Ring h}
  have hgu : IsUnit (aeval P.X g) := P.hasMap_X.2
  have e2 : P.X ^ (m + 1) = algebraMap A P.Ring ε := by
    have : aeval P.X (X ^ (m + 1) - C ε) = 0 := P.hasMap_X.1
    simpa [sub_eq_zero] using this
  have hX : P.X - algebraMap A P.Ring r ∈ J := by
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hr
    have key : (P.X - algebraMap A P.Ring r) * aeval P.X g =
        algebraMap A P.Ring c * algebraMap A P.Ring h := by
      have e1 : aeval P.X g * (P.X - algebraMap A P.Ring r) =
          P.X ^ (m + 1) - (algebraMap A P.Ring r) ^ (m + 1) := by
        simp only [g, map_sum, map_mul, map_pow, aeval_X, aeval_C]
        exact geom_sum₂_mul _ _ _
      rw [mul_comm, e1, e2, ← map_pow, ← map_sub, ← hc, map_mul]
    rw [Ideal.mem_span_singleton']
    refine ⟨algebraMap A P.Ring c * ↑hgu.unit⁻¹, ?_⟩
    calc _ = (P.X - algebraMap A P.Ring r) * aeval P.X g * ↑hgu.unit⁻¹ := by rw [key]; ring
      _ = _ := by rw [mul_assoc, hgu.mul_val_inv, mul_one]
  let ψ : A ⧸ I →ₐ[A] P.Ring ⧸ J := Ideal.Quotient.liftₐ I (Algebra.ofId A (P.Ring ⧸ J)) (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [Algebra.ofId_apply, IsScalarTower.algebraMap_apply A P.Ring (P.Ring ⧸ J),
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem, map_mul]
    exact J.mul_mem_left _ (Ideal.mem_span_singleton_self _))
  have hψ : ∀ a : A, ψ (Ideal.Quotient.mk I a) = Ideal.Quotient.mk J (algebraMap A P.Ring a) := by
    intro a
    first
      | rfl
      | simp [ψ, Ideal.Quotient.liftₐ_apply, IsScalarTower.algebraMap_apply A P.Ring (P.Ring ⧸ J)]
  have hcomp : ψ.comp φ = Ideal.Quotient.mkₐ A J := by
    apply P.hom_ext
    simp only [AlgHom.comp_apply, φ, StandardEtalePair.lift_X, Ideal.Quotient.mkₐ_eq_mk]
    show ψ (Ideal.Quotient.mk I r) = _
    rw [hψ, Ideal.Quotient.eq]
    first
      | exact hX
      | (have := J.neg_mem hX; rwa [neg_sub] at this)
  refine ⟨P.Ring, inferInstance, inferInstance, ⟨inferInstance, ?_, ?_⟩, P.X, e2.symm⟩
  · intro a'
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (φ a')
    refine ⟨a, ?_⟩
    have h1 := congrArg (fun F => F a') hcomp
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, ← ha] at h1
    rw [hψ] at h1
    exact Ideal.Quotient.eq.mp h1.symm
  · intro a ha
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp ha
    have h1 := congrArg φ hy
    have hh0 : Ideal.Quotient.mk I h = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
    simp only [map_mul, AlgHom.commutes, Ideal.Quotient.algebraMap_eq] at h1
    rw [hh0, mul_zero] at h1
    exact Ideal.Quotient.eq_zero_iff_mem.mp h1.symm

end GlobalTheory.EtC
