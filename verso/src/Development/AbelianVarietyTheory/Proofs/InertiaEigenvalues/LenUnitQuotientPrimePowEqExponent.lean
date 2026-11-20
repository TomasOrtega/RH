import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory.LenUnitPow

variable (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]

variable (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] in

/- English proof (translation)
Introduce `h`. Establish `hker : (RingHom.ker (algebraMap ℤ_[l] O)).IsMaximal`. Use `Ideal.IsPrime.isMaximal (RingHom.ker_isPrime _) ?_` and prove the remaining obligations. Introduce `hbot`. Establish `hl : ((l : ℤ_[l])) ∈ RingHom.ker (algebraMap ℤ_[l] O)`.

Rewrite using `[RingHom.mem_ker, map_natCast]`. Conclude with `h`. Rewrite `hl` using `[hbot, Ideal.mem_bot]`. Conclude with `(Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) hl`. Establish `hbot : (⊥ : Ideal O).IsMaximal`.

Use `Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := ℤ_[l]) _ ?_` and prove the remaining obligations. Rewrite using `[← RingHom.ker_eq_comap_bot]` and apply the resulting hypothesis. Conclude with `IsDiscreteValuationRing.not_a_field O (IsLocalRing.eq_maximalIdeal hbot).symm`.
-/
theorem _root_.GlobalTheory.LenUnitPow.natCast_ne_zero : (l : O) ≠ 0 := by
  intro h
  have hker : (RingHom.ker (algebraMap ℤ_[l] O)).IsMaximal := by
    refine Ideal.IsPrime.isMaximal (RingHom.ker_isPrime _) ?_
    intro hbot
    have hl : ((l : ℤ_[l])) ∈ RingHom.ker (algebraMap ℤ_[l] O) := by
      rw [RingHom.mem_ker, map_natCast]; exact h
    rw [hbot, Ideal.mem_bot] at hl
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) hl
  have hbot : (⊥ : Ideal O).IsMaximal := by
    refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := ℤ_[l]) _ ?_
    rwa [← RingHom.ker_eq_comap_bot]
  exact IsDiscreteValuationRing.not_a_field O (IsLocalRing.eq_maximalIdeal hbot).symm

variable (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] in

/- English proof (translation)
Introduce `h`. Establish `hm : (Ideal.comap (algebraMap ℤ_[l] O) (IsLocalRing.maximalIdeal O)).IsMaximal` using `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _`. Establish `hl : (l : ℤ_[l]) ∈ Ideal.comap (algebraMap ℤ_[l] O) (IsLocalRing.maximalIdeal O)`. Rewrite using `[IsLocalRing.eq_maximalIdeal hm, PadicInt.maximalIdeal_eq_span_p]`. Conclude with `Ideal.subset_span rfl`.

Rewrite `hl` using `[Ideal.mem_comap, map_natCast, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Conclude with `hl h`.
-/
theorem _root_.GlobalTheory.LenUnitPow.natCast_not_isUnit : ¬ IsUnit (l : O) := by
  intro h
  have hm : (Ideal.comap (algebraMap ℤ_[l] O) (IsLocalRing.maximalIdeal O)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _
  have hl : (l : ℤ_[l]) ∈ Ideal.comap (algebraMap ℤ_[l] O) (IsLocalRing.maximalIdeal O) := by
    rw [IsLocalRing.eq_maximalIdeal hm, PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.subset_span rfl
  rw [Ideal.mem_comap, map_natCast, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hl
  exact hl h

/- English proof (translation)
Establish `h0` using `natCast_ne_zero l (O := O)`. Establish `h1` using `natCast_not_isUnit l (O := O)`. Unfold `lenUnit`. Express the relevant statement in the definitionally equal form `((Ring.ord O ((w : O) * (l : O) ^ m)).toNat : ℚ) / ((Ring.ord O (l : O)).toNat : ℚ) = m`. Rewrite using `[Ring.ord_mul_of_isUnit_left w.isUnit, Ring.ord_pow (mem_nonZeroDivisors_of_ne_zero h0), Ring.ord_eq_addVal]`.

Establish `htop : IsDiscreteValuationRing.addVal O (l : O) ≠ ⊤`. Rewrite using `[Ne, IsDiscreteValuationRing.addVal_eq_top_iff]` and apply the resulting hypothesis. Establish `hz : IsDiscreteValuationRing.addVal O (l : O) ≠ 0`. Rewrite using `[Ne, IsDiscreteValuationRing.addVal_eq_zero_iff]` and apply the resulting hypothesis. Take `⟨e, he⟩` from `ENat.ne_top_iff_exists.mp htop`.

Rewrite `hz`, the goal using `[← he]`. Establish `he0 : (e : ℚ) ≠ 0` using `by exact_mod_cast hz`. Rewrite using `[nsmul_eq_mul, ← Nat.cast_mul, ENat.toNat_coe, ENat.toNat_coe, Nat.cast_mul]`. Conclude with `mul_div_cancel_right₀ _ he0`.
-/
theorem lenUnit_quot_unit_mul_pow (w : Oˣ) (m : ℕ) :
    lenUnit (O := O) l (O ⧸ Ideal.span {(w : O) * (l : O) ^ m}) = (m : ℚ) := by
  have h0 := natCast_ne_zero l (O := O)
  have h1 := natCast_not_isUnit l (O := O)
  unfold lenUnit
  change ((Ring.ord O ((w : O) * (l : O) ^ m)).toNat : ℚ) / ((Ring.ord O (l : O)).toNat : ℚ) = m
  rw [Ring.ord_mul_of_isUnit_left w.isUnit, Ring.ord_pow (mem_nonZeroDivisors_of_ne_zero h0),
    Ring.ord_eq_addVal]
  have htop : IsDiscreteValuationRing.addVal O (l : O) ≠ ⊤ := by
    rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
  have hz : IsDiscreteValuationRing.addVal O (l : O) ≠ 0 := by
    rwa [Ne, IsDiscreteValuationRing.addVal_eq_zero_iff]
  obtain ⟨e, he⟩ := ENat.ne_top_iff_exists.mp htop
  rw [← he] at hz ⊢
  have he0 : (e : ℚ) ≠ 0 := by exact_mod_cast hz
  rw [nsmul_eq_mul, ← Nat.cast_mul, ENat.toNat_coe, ENat.toNat_coe, Nat.cast_mul]
  exact mul_div_cancel_right₀ _ he0

/- English proof (translation)
Introduce `l _ _ _ _ _ _ _ w m` and use `lenUnit_quot_unit_mul_pow l w m`.
-/
theorem main : ∀ (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (w : Oˣ) (m : ℕ),
    lenUnit (O := O) l (O ⧸ Ideal.span {(w : O) * (l : O) ^ m}) = (m : ℚ) :=
  fun l _ _ _ _ _ _ _ w m => lenUnit_quot_unit_mul_pow l w m

end GlobalTheory.LenUnitPow
