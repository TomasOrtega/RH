import Formalism.LocalToGlobal.UnitaryNorms.MemFIffReal
import Formalism.LocalToGlobal.UnitaryNorms.PowValCast
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostRam

noncomputable section

open NumberField IntermediateField

namespace Formalism.L2.Host

open Formalism.BasicNotions Formalism.FrobeniusOrbits

/- English proof (translation)
Establish `hz : IsPrimitiveRoot (κ (Cond.z M)) M` using `(Cond.z_spec M).map_of_injective κ.toRingHom.injective`. Rewrite using `[AlgHom.fieldRange_eq_map, ← Cond.top_adjoin M, adjoin_map, Set.image_singleton, cycQ_eq hz]`.
-/
theorem range_cyc (M : ℕ) [NeZero M] (κ : CyclotomicField M ℚ →ₐ[ℚ] Qb) : κ.fieldRange = cycQ M := by
  have hz : IsPrimitiveRoot (κ (Cond.z M)) M := (Cond.z_spec M).map_of_injective κ.toRingHom.injective
  rw [AlgHom.fieldRange_eq_map, ← Cond.top_adjoin M, adjoin_map, Set.image_singleton, cycQ_eq hz]

/- English proof (translation)
Establish `hco : (u : ZMod N).val.Coprime N` using `ZMod.val_coe_unit_coprime u`. Take `⟨σ, hσ⟩` from `Cond.aut N (u : ZMod N).val hco`. Set `κ : CyclotomicField N ℚ →ₐ[ℚ] Qb` to `IsAlgClosed.lift`. Set `_ : Algebra (CyclotomicField N ℚ) Qb` to `κ.toRingHom.toAlgebra`. Establish `: IsScalarTower ℚ (CyclotomicField N ℚ) Qb` using `IsScalarTower.of_algebraMap_eq fun x => (κ.commutes x).symm`.

Establish `: IsGalois ℚ (CyclotomicField N ℚ)` using `IsCyclotomicExtension.isGalois {N} ℚ (CyclotomicField N ℚ)`. Establish `: IsAlgClosure ℚ Qb` using `⟨inferInstance, AlgebraicClosure.isAlgebraic ℚ⟩`. Establish `: Normal ℚ Qb` using `IsAlgClosure.normal ℚ Qb`. Use `⟨σ.liftNormal Qb, fun z hz => ?_⟩` and prove the remaining obligations. Establish `hzr : z ∈ κ.fieldRange` using `by rw [range_cyc N κ]; exact subset_adjoin ℚ _ hz`.

Take `⟨w, rfl⟩` from `hzr`. Establish `hw : w ^ N = 1` using `κ.toRingHom.injective (by show κ (w ^ N) = κ 1`. Rewrite using `[map_pow, map_one]`. Conclude with `hz)`. Establish `h` using `AlgEquiv.liftNormal_commutes σ Qb w`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_cyc_act (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) :
    ∃ s : Qb ≃ₐ[ℚ] Qb, ∀ z ∈ mus N, s z = z ^ (u : ZMod N).val := by
  have hco : (u : ZMod N).val.Coprime N := ZMod.val_coe_unit_coprime u
  obtain ⟨σ, hσ⟩ := Cond.aut N (u : ZMod N).val hco
  let κ : CyclotomicField N ℚ →ₐ[ℚ] Qb := IsAlgClosed.lift
  let _ : Algebra (CyclotomicField N ℚ) Qb := κ.toRingHom.toAlgebra
  have : IsScalarTower ℚ (CyclotomicField N ℚ) Qb := IsScalarTower.of_algebraMap_eq fun x => (κ.commutes x).symm
  have : IsGalois ℚ (CyclotomicField N ℚ) := IsCyclotomicExtension.isGalois {N} ℚ (CyclotomicField N ℚ)
  have : IsAlgClosure ℚ Qb := ⟨inferInstance, AlgebraicClosure.isAlgebraic ℚ⟩
  have : Normal ℚ Qb := IsAlgClosure.normal ℚ Qb
  refine ⟨σ.liftNormal Qb, fun z hz => ?_⟩
  have hzr : z ∈ κ.fieldRange := by rw [range_cyc N κ]; exact subset_adjoin ℚ _ hz
  obtain ⟨w, rfl⟩ := hzr
  have hw : w ^ N = 1 := κ.toRingHom.injective (by
    show κ (w ^ N) = κ 1
    rw [map_pow, map_one]; exact hz)
  have h := AlgEquiv.liftNormal_commutes σ Qb w
  calc σ.liftNormal Qb (κ w) = κ (σ w) := h
    _ = κ w ^ (u : ZMod N).val := by rw [hσ w hw, map_pow]

/- English proof (translation)
Use `⟨H.EQ_le_cycQ, fun M hM hle => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hnd`. Establish `hN` using `H.condN_ne_zero`. Take `⟨c, hc⟩` from `Nat.gcd_dvd_left H.condN M`. Establish `hc1 : c ≠ 1`.

Introduce and unpack `rfl`. Rewrite `hc` using `[mul_one]`. Conclude with `hnd (hc ▸ Nat.gcd_dvd_right _ _)`. Take `⟨l, hl, c', rfl⟩` from `Nat.exists_prime_and_dvd hc1`. Establish `hdiv : H.condN / l = Nat.gcd H.condN M * c'` using `Nat.div_eq_of_eq_mul_right hl.pos (hc.trans (by ring))`.

Take `⟨u, hu, hne⟩` from `H.exact_all hP hE l hl ⟨Nat.gcd H.condN M * c', hc.trans (by ring)⟩`. Take `⟨k, hk1, hk2⟩` from `Nat.chineseRemainder' (hu.of_dvd (hdiv ▸ dvd_mul_right _ _))`. Establish `: NeZero (H.condN * M)` using `⟨mul_ne_zero hN hM.ne'⟩`. Establish `hk : Nat.Coprime k (H.condN * M)` using `Nat.Coprime.mul_right (by rw [Nat.Coprime, hk1.gcd_eq]; exact ZMod.val_coe_unit_coprime u) (by rw [Nat.Coprime, hk2.gcd_eq]; exact Nat.gcd_one_left _)`. Take `⟨w, hw⟩` from `Formalism.HC.exists_unit_val hk`.

Take `⟨s, hs⟩` from `exists_cyc_act (H.condN * M) w`. Establish `hs1 : ∀ z ∈ mus H.condN, s z = z ^ (u : ZMod H.condN).val` using `fun z hz => by`. Rewrite using `[hs z (mus_mono (dvd_mul_right _ _) hz), pow_eq_pow_mod _ (show z ^ H.condN = 1 from hz), (hw.of_dvd (dvd_mul_right _ _)).trans hk1, ← pow_eq_pow_mod _ (show z ^ H.condN = 1 from hz)]`. Establish `hs2 : ∀ z ∈ mus M, s z = z` using `fun z hz => by`. Rewrite using `[hs z (mus_mono (dvd_mul_left _ _) hz), pow_eq_pow_mod _ (show z ^ M = 1 from hz), (hw.of_dvd (dvd_mul_left _ _)).trans hk2, ← pow_eq_pow_mod _ (show z ^ M = 1 from hz), pow_one]`.

Establish `hs3 : cycQ M ≤ fixedField (Subgroup.zpowers s)`. Rewrite using `[cycQ, adjoin_le_iff]`. Introduce `z hz`. Use `(mem_fixedField_iff _ _).2 fun t ht => ?_` and prove the remaining obligations. Conclude with `(Subgroup.zpowers_le.2 (show s ∈ MulAction.stabilizer (Qb ≃ₐ[ℚ] Qb) z from hs2 z hz) ht : _)`.

Take `⟨j⟩` from `H.nonempty_emb`. Apply `hne` to reduce the goal to its premises. Rewrite using `[← H.gal.symm.map_eq_one_iff]`. Use extensionality with `x`. Apply `j.toRingHom.injective` to reduce the goal to its premises.

Establish `h1` using `(mem_fixedField_iff _ _).1 (hs3 (hle (H.mem_EQ j x))) s (Subgroup.mem_zpowers s)`. Conclude with `(H.artin_apply s u hs1 j x).symm.trans h1`.
-/
theorem condEQ_of {φ : Formalism.HC.Frame} (H : Formalism.HC.HostAx φ) (hP : H.PsQ) (hE : H.Exact) : H.CondEQ := by
  refine ⟨H.EQ_le_cycQ, fun M hM hle => ?_⟩
  by_contra hnd
  have hN := H.condN_ne_zero
  obtain ⟨c, hc⟩ := Nat.gcd_dvd_left H.condN M
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [mul_one] at hc
    exact hnd (hc ▸ Nat.gcd_dvd_right _ _)
  obtain ⟨l, hl, c', rfl⟩ := Nat.exists_prime_and_dvd hc1
  have hdiv : H.condN / l = Nat.gcd H.condN M * c' :=
    Nat.div_eq_of_eq_mul_right hl.pos (hc.trans (by ring))
  obtain ⟨u, hu, hne⟩ := H.exact_all hP hE l hl ⟨Nat.gcd H.condN M * c', hc.trans (by ring)⟩
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder' (hu.of_dvd (hdiv ▸ dvd_mul_right _ _))
  have : NeZero (H.condN * M) := ⟨mul_ne_zero hN hM.ne'⟩
  have hk : Nat.Coprime k (H.condN * M) :=
    Nat.Coprime.mul_right (by rw [Nat.Coprime, hk1.gcd_eq]; exact ZMod.val_coe_unit_coprime u)
      (by rw [Nat.Coprime, hk2.gcd_eq]; exact Nat.gcd_one_left _)
  obtain ⟨w, hw⟩ := Formalism.HC.exists_unit_val hk
  obtain ⟨s, hs⟩ := exists_cyc_act (H.condN * M) w
  have hs1 : ∀ z ∈ mus H.condN, s z = z ^ (u : ZMod H.condN).val := fun z hz => by
    rw [hs z (mus_mono (dvd_mul_right _ _) hz), pow_eq_pow_mod _ (show z ^ H.condN = 1 from hz),
      (hw.of_dvd (dvd_mul_right _ _)).trans hk1, ← pow_eq_pow_mod _ (show z ^ H.condN = 1 from hz)]
  have hs2 : ∀ z ∈ mus M, s z = z := fun z hz => by
    rw [hs z (mus_mono (dvd_mul_left _ _) hz), pow_eq_pow_mod _ (show z ^ M = 1 from hz),
      (hw.of_dvd (dvd_mul_left _ _)).trans hk2, ← pow_eq_pow_mod _ (show z ^ M = 1 from hz), pow_one]
  have hs3 : cycQ M ≤ fixedField (Subgroup.zpowers s) := by
    rw [cycQ, adjoin_le_iff]
    intro z hz
    refine (mem_fixedField_iff _ _).2 fun t ht => ?_
    exact (Subgroup.zpowers_le.2 (show s ∈ MulAction.stabilizer (Qb ≃ₐ[ℚ] Qb) z from hs2 z hz) ht : _)
  obtain ⟨j⟩ := H.nonempty_emb
  apply hne
  rw [← H.gal.symm.map_eq_one_iff]
  ext x
  apply j.toRingHom.injective
  have h1 := (mem_fixedField_iff _ _).1 (hs3 (hle (H.mem_EQ j x))) s (Subgroup.mem_zpowers s)
  exact (H.artin_apply s u hs1 j x).symm.trans h1

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

/- English proof (translation)
The claim follows from `condEQ_of H.toHostAx H.flPS H.QS_exact`.
-/
theorem condEQ : H.CondEQ := condEQ_of H.toHostAx H.flPS H.QS_exact

end Formalism.L2.Host
