import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData

open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical

noncomputable section

namespace GlobalTheory.CondAway

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Use `haveI : Finite (OF E ⧸ q.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ q.ne_bot`. Use `haveI := q.isMaximal`. Use `letI : Field (OF E ⧸ q.asIdeal) := Ideal.Quotient.field _`. Use `letI : Fintype (OF E ⧸ q.asIdeal) := Fintype.ofFinite _`. Take `⟨n, hp, hcard⟩` from `FiniteField.card (OF E ⧸ q.asIdeal) (ringChar (OF E ⧸ q.asIdeal))`.

Use `set p := ringChar (OF E ⧸ q.asIdeal)`. Establish `hN : Ideal.absNorm q.asIdeal = p ^ (n : ℕ)`. Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card, hcard]`. Establish `hpl : p ≠ l`. Introduce `h`.

Apply `hq` to reduce the goal to its premises. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← h]`. Conclude with `ringChar.Nat.cast_ringChar`. Assume the negation of the conclusion as `hu`. Establish `hmem : ((p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O`.

Establish `: ((p : ℕ) : O) ^ (n : ℕ) ∈ IsLocalRing.maximalIdeal O`. Rewrite using `[← Nat.cast_pow, ← hN]`. Conclude with `(IsLocalRing.mem_maximalIdeal _).2 hu`. Conclude with `(IsLocalRing.maximalIdeal.isMaximal O).isPrime.mem_of_pow_mem _ this`. Establish `hcop : IsCoprime (p : ℤ) (l : ℤ)` using `Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hl).2 hpl)`.

Take `⟨u, v, huv⟩` from `hcop`. Establish `h1 : (1 : O) ∈ IsLocalRing.maximalIdeal O`. Use `congrArg (Int.cast : ℤ → O) huv` as an intermediate fact. Move the coercions through the operations in `at this`. Rewrite using `[← this]`.

Conclude with `Ideal.add_mem _ (Ideal.mul_mem_left _ _ hmem) (Ideal.mul_mem_left _ _ hlO)`. Conclude with `(IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h1)`.
-/
theorem isUnit_absNorm_of_not_mem (q : HeightOneSpectrum (OF E)) (l : ℕ) (hl : l.Prime)
    (hq : (l : OF E) ∉ q.asIdeal) (O : Type) [CommRing O] [IsLocalRing O]
    (hlO : (l : O) ∈ IsLocalRing.maximalIdeal O) : IsUnit ((Ideal.absNorm q.asIdeal : ℕ) : O) := by
  haveI : Finite (OF E ⧸ q.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ q.ne_bot
  haveI := q.isMaximal
  letI : Field (OF E ⧸ q.asIdeal) := Ideal.Quotient.field _
  letI : Fintype (OF E ⧸ q.asIdeal) := Fintype.ofFinite _
  obtain ⟨n, hp, hcard⟩ := FiniteField.card (OF E ⧸ q.asIdeal) (ringChar (OF E ⧸ q.asIdeal))
  set p := ringChar (OF E ⧸ q.asIdeal)
  have hN : Ideal.absNorm q.asIdeal = p ^ (n : ℕ) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card, hcard]
  have hpl : p ≠ l := by
    intro h
    apply hq
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← h]
    exact ringChar.Nat.cast_ringChar
  by_contra hu
  have hmem : ((p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O := by
    have : ((p : ℕ) : O) ^ (n : ℕ) ∈ IsLocalRing.maximalIdeal O := by
      rw [← Nat.cast_pow, ← hN]; exact (IsLocalRing.mem_maximalIdeal _).2 hu
    exact (IsLocalRing.maximalIdeal.isMaximal O).isPrime.mem_of_pow_mem _ this
  have hcop : IsCoprime (p : ℤ) (l : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hl).2 hpl)
  obtain ⟨u, v, huv⟩ := hcop
  have h1 : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
    have := congrArg (Int.cast : ℤ → O) huv
    push_cast at this
    rw [← this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hmem) (Ideal.mul_mem_left _ _ hlO)
  exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h1)

/- English proof (translation)
Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a x`. Rewrite using `[LinearMap.rTensor_tmul]`. Use `show σ (g a) * algebraMap O K x = σ s * (σ a * algebraMap O K x)`.

Rewrite using `[hg, map_mul, mul_assoc]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy, map_add, mul_add]`.
-/
theorem coordAt_rTensor (O : Type) [CommRing O] {K : Type} [Field K] [Algebra O K] {c c' : Ideal (OF E)} (s : E)
    (g : orderC c →ₗ[ℤ] orderC c') (hg : ∀ x, (g x : E) = s * x) (σ : E →+* K) (t : orderC c ⊗[ℤ] O) :
    coordAt O c' σ (g.rTensor O t) = σ s * coordAt O c σ t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [LinearMap.rTensor_tmul]
    show σ (g a) * algebraMap O K x = σ s * (σ a * algebraMap O K x)
    rw [hg, map_mul, mul_assoc]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, mul_add]

/- English proof (translation)
Introduce `E _ _ _ 𝔣 Q l hl hQ O _ _ _ _ K _ _ _ hlO D`. Establish `hle : condQ 𝔣 Q ≤ 𝔣` using `Ideal.mul_le_inf.trans inf_le_left`. Prove the components needed by the constructor for the conclusion. Introduce `h σ`. Take `⟨t, ht⟩` from `h σ`.

Set `g : orderC (condQ 𝔣 Q) →ₗ[ℤ] orderC 𝔣` to `AddMonoidHom.toIntLinearMap { toFun := fun x => ⟨(1 : E) * x, by rw [one_mul]; exact orderC_mono hle x.2⟩, map_zero' := Subtype.ext (by simp), map_add' := fun x y => Subtype.ext (by simp [mul_add]) }`. Use `⟨g.rTensor O t, fun σ' => ?_⟩` and prove the remaining obligations. Rewrite using `[coordAt_rTensor O (1 : E) g (fun x => rfl), map_one, one_mul, ht]`. Introduce `h σ`. Take `⟨t, ht⟩` from `h σ`.

Use `set m : ℕ := ∏ q ∈ Q, Ideal.absNorm q.asIdeal with hm`. Establish `hmI : (m : OF E) ∈ ∏ q ∈ Q, q.asIdeal`. Rewrite using `[hm, Nat.cast_prod]`. Conclude with `Ideal.prod_mem_prod fun q _ => Ideal.absNorm_mem q.asIdeal`. Establish `hmul : ∀ x ∈ orderC 𝔣, (m : E) * x ∈ orderC (condQ 𝔣 Q)`.

Introduce `x hx`. Take `⟨a, b, hb, rfl⟩` from `mem_orderC.1 hx`. Use `mem_orderC.2 ⟨m * a, b * algebraMap (OF E) (𝓞 E) m, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[condQ, Ideal.map_mul]`. Conclude with `Ideal.mul_mem_mul hb (Ideal.mem_map_of_mem _ hmI)`.

Simplify using `only [map_mul, map_natCast]`. Expand and normalize the polynomial expressions, which then agree. Set `g : orderC 𝔣 →ₗ[ℤ] orderC (condQ 𝔣 Q)` to `AddMonoidHom.toIntLinearMap { toFun := fun x => ⟨(m : E) * x, hmul x x.2⟩, map_zero' := Subtype.ext (by simp), map_add' := fun x y => Subtype.ext (by simp [mul_add]) }`. Establish `hu : IsUnit (m : O)`. Rewrite using `[hm, Nat.cast_prod]`.

Conclude with `Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one (fun q hq => isUnit_absNorm_of_not_mem q l hl (hQ q hq) O hlO)`. Take `⟨u, hu'⟩` from `hu.exists_left_inv`. Use `⟨g.rTensor O t * (1 ⊗ₜ u), fun σ' => ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, coordAt_rTensor O (m : E) g (fun x => rfl), ht]`. Establish `h1 : coordAt O (condQ 𝔣 Q) σ' (1 ⊗ₜ u) = algebraMap O K u` using `by show σ' ((1 : orderC (condQ 𝔣 Q)) : E) * algebraMap O K u = _`.

Simplify using the standard rewrite rules. Establish `h2 : algebraMap O K u * (m : K) = 1`. Rewrite using `[← map_natCast (algebraMap O K), ← map_mul, hu', map_one]`. Rewrite using `[h1, map_natCast]`. Use `split_ifs`.

Take the linear combination `(algebraMap O K D) * h2`. Simplify using the standard rewrite rules.
-/
theorem clearsIdem_condQ_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (𝔣 : Ideal (OF E))
    (Q : Finset (HeightOneSpectrum (OF E))) (l : ℕ), l.Prime → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K]
    [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → ∀ D : O,
    ClearsIdem K (condQ 𝔣 Q) D ↔ ClearsIdem K 𝔣 D := by
  intro E _ _ _ 𝔣 Q l hl hQ O _ _ _ _ K _ _ _ hlO D
  have hle : condQ 𝔣 Q ≤ 𝔣 := Ideal.mul_le_inf.trans inf_le_left
  constructor
  · intro h σ
    obtain ⟨t, ht⟩ := h σ
    let g : orderC (condQ 𝔣 Q) →ₗ[ℤ] orderC 𝔣 := AddMonoidHom.toIntLinearMap
      { toFun := fun x => ⟨(1 : E) * x, by rw [one_mul]; exact orderC_mono hle x.2⟩,
        map_zero' := Subtype.ext (by simp), map_add' := fun x y => Subtype.ext (by simp [mul_add]) }
    refine ⟨g.rTensor O t, fun σ' => ?_⟩
    rw [coordAt_rTensor O (1 : E) g (fun x => rfl), map_one, one_mul, ht]
  · intro h σ
    obtain ⟨t, ht⟩ := h σ
    set m : ℕ := ∏ q ∈ Q, Ideal.absNorm q.asIdeal with hm
    have hmI : (m : OF E) ∈ ∏ q ∈ Q, q.asIdeal := by
      rw [hm, Nat.cast_prod]
      exact Ideal.prod_mem_prod fun q _ => Ideal.absNorm_mem q.asIdeal
    have hmul : ∀ x ∈ orderC 𝔣, (m : E) * x ∈ orderC (condQ 𝔣 Q) := by
      intro x hx
      obtain ⟨a, b, hb, rfl⟩ := mem_orderC.1 hx
      refine mem_orderC.2 ⟨m * a, b * algebraMap (OF E) (𝓞 E) m, ?_, ?_⟩
      · rw [condQ, Ideal.map_mul]
        exact Ideal.mul_mem_mul hb (Ideal.mem_map_of_mem _ hmI)
      · simp only [map_mul, map_natCast]
        ring
    let g : orderC 𝔣 →ₗ[ℤ] orderC (condQ 𝔣 Q) := AddMonoidHom.toIntLinearMap
      { toFun := fun x => ⟨(m : E) * x, hmul x x.2⟩,
        map_zero' := Subtype.ext (by simp), map_add' := fun x y => Subtype.ext (by simp [mul_add]) }
    have hu : IsUnit (m : O) := by
      rw [hm, Nat.cast_prod]
      exact Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one
        (fun q hq => isUnit_absNorm_of_not_mem q l hl (hQ q hq) O hlO)
    obtain ⟨u, hu'⟩ := hu.exists_left_inv
    refine ⟨g.rTensor O t * (1 ⊗ₜ u), fun σ' => ?_⟩
    rw [map_mul, coordAt_rTensor O (m : E) g (fun x => rfl), ht]
    have h1 : coordAt O (condQ 𝔣 Q) σ' (1 ⊗ₜ u) = algebraMap O K u := by
      show σ' ((1 : orderC (condQ 𝔣 Q)) : E) * algebraMap O K u = _
      simp
    have h2 : algebraMap O K u * (m : K) = 1 := by
      rw [← map_natCast (algebraMap O K), ← map_mul, hu', map_one]
    rw [h1, map_natCast]
    split_ifs
    · linear_combination (algebraMap O K D) * h2
    · simp

end GlobalTheory.CondAway
