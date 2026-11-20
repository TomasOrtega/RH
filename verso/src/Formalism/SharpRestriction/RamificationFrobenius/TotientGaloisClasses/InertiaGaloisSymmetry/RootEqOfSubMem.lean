import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.CycLift

open NumberField IntermediateField Ideal
open scoped Pointwise

noncomputable section

namespace Formalism.HC.Der

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition

/- English proof (translation)
Establish `hm0 : m ≠ 0`. Introduce and unpack `rfl`. Conclude with `hm (by simp)`. Establish `hgeom` using `geom_sum₂_mul x y m`. Rewrite `hgeom` using `[hx, hy, sub_self]`.

Break down `mul_eq_zero.1 hgeom with hG | hG` into its components or cases. It suffices to derive a contradiction. Establish `hq : Ideal.Quotient.mk P x = Ideal.Quotient.mk P y` using `Ideal.Quotient.eq.2 hxy`. Establish `h1` using `congrArg (Ideal.Quotient.mk P) hG`. Rewrite `h1` using `[map_sum, map_zero]`.

Simplify using `only [map_mul, map_pow, hq] at h1`. Establish `h2 : ∀ i ∈ Finset.range m, (Ideal.Quotient.mk P y) ^ i * (Ideal.Quotient.mk P y) ^ (m - 1 - i) = (Ideal.Quotient.mk P y) ^ (m - 1)`. Introduce `i hi`. Rewrite using `[← pow_add]`. Use `congr 1`.

Rewrite `hi` using `[Finset.mem_range]`. Use linear arithmetic over natural numbers and integers. Rewrite `h1` using `[Finset.sum_congr rfl h2, Finset.sum_const, Finset.card_range, nsmul_eq_mul]`. Break down `mul_eq_zero.1 h1 with h3 | h3` into its components or cases. Apply `hm` to reduce the goal to its premises.

Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_natCast]`. Conclude with `h3`. Establish `h4 : (Ideal.Quotient.mk P y) ^ m = 1` using `by rw [← map_pow, hy, map_one]`. Establish `h5 : (Ideal.Quotient.mk P y) ^ m = 0`. Rewrite using `[show m = m - 1 + 1 by omega, pow_succ, h3, zero_mul]`.

Rewrite `h5` using `[h4]`. Conclude with `one_ne_zero h5`. Conclude with `sub_eq_zero.1 hG`.
-/
theorem root_eq_of_sub_mem {S : Type*} [CommRing S] [IsDomain S] (P : Ideal S) [hP : P.IsPrime] {m : ℕ}
    (hm : (m : S) ∉ P) {x y : S} (hx : x ^ m = 1) (hy : y ^ m = 1) (hxy : x - y ∈ P) : x = y := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (by simp)
  have hgeom := geom_sum₂_mul x y m
  rw [hx, hy, sub_self] at hgeom
  rcases mul_eq_zero.1 hgeom with hG | hG
  · exfalso
    have hq : Ideal.Quotient.mk P x = Ideal.Quotient.mk P y := Ideal.Quotient.eq.2 hxy
    have h1 := congrArg (Ideal.Quotient.mk P) hG
    rw [map_sum, map_zero] at h1
    simp only [map_mul, map_pow, hq] at h1
    have h2 : ∀ i ∈ Finset.range m, (Ideal.Quotient.mk P y) ^ i * (Ideal.Quotient.mk P y) ^ (m - 1 - i) =
        (Ideal.Quotient.mk P y) ^ (m - 1) := by
      intro i hi
      rw [← pow_add]
      congr 1
      rw [Finset.mem_range] at hi
      omega
    rw [Finset.sum_congr rfl h2, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
    rcases mul_eq_zero.1 h1 with h3 | h3
    · apply hm
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
      exact h3
    · have h4 : (Ideal.Quotient.mk P y) ^ m = 1 := by rw [← map_pow, hy, map_one]
      have h5 : (Ideal.Quotient.mk P y) ^ m = 0 := by
        rw [show m = m - 1 + 1 by omega, pow_succ, h3, zero_mul]
      rw [h4] at h5
      exact one_ne_zero h5
  · exact sub_eq_zero.1 hG

/- English proof (translation)
Rewrite using `[show ((ZMod.unitsMap h u : (ZMod M)ˣ) : ZMod M) = ((u : ZMod N).val : ZMod M) from ZMod.cast_eq_val _, ZMod.natCast_eq_natCast_iff]`.
-/
theorem val_modEq_iff {M N : ℕ} [NeZero N] (h : M ∣ N) (u : (ZMod N)ˣ) (x : ℕ) :
    (u : ZMod N).val ≡ x [MOD M] ↔ ((ZMod.unitsMap h u : (ZMod M)ˣ) : ZMod M) = (x : ZMod M) := by
  rw [show ((ZMod.unitsMap h u : (ZMod M)ˣ) : ZMod M) = ((u : ZMod N).val : ZMod M) from
    ZMod.cast_eq_val _, ZMod.natCast_eq_natCast_iff]

/- English proof (translation)
Rewrite using `[val_modEq_iff h u 1, Nat.cast_one, Units.val_eq_one]`.
-/
theorem val_modEq_one_iff {M N : ℕ} [NeZero N] (h : M ∣ N) (u : (ZMod N)ˣ) :
    (u : ZMod N).val ≡ 1 [MOD M] ↔ ZMod.unitsMap h u = 1 := by
  rw [val_modEq_iff h u 1, Nat.cast_one, Units.val_eq_one]

/- English proof (translation)
Take `⟨u, hu⟩` from `ZMod.unitsMap_surjective h (ZMod.unitOfCoprime x hx)`. Conclude with `⟨u, (val_modEq_iff h u x).2 (by rw [hu, ZMod.coe_unitOfCoprime])⟩`.
-/
theorem exists_unit_modEq {M N : ℕ} [NeZero N] (h : M ∣ N) (x : ℕ) (hx : x.Coprime M) :
    ∃ u : (ZMod N)ˣ, (u : ZMod N).val ≡ x [MOD M] := by
  obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective h (ZMod.unitOfCoprime x hx)
  exact ⟨u, (val_modEq_iff h u x).2 (by rw [hu, ZMod.coe_unitOfCoprime])⟩

section Cyc

variable (N : ℕ) [NeZero N]

def zO : 𝓞 (Cond.Cyc N) := (Cond.z_spec N).toInteger

/- English proof (translation)
Conclude with `(Cond.z_spec N).toInteger_isPrimitiveRoot`.
-/
theorem zO_prim : IsPrimitiveRoot (zO N) N := by
  exact (Cond.z_spec N).toInteger_isPrimitiveRoot

/- English proof (translation)
Apply `RingOfIntegers.ext` to reduce the goal to its premises. Use `show (tauN N u) ((zO N : 𝓞 (Cond.Cyc N)) : Cond.Cyc N) = (((zO N) ^ (u : ZMod N).val : 𝓞 (Cond.Cyc N)) : Cond.Cyc N)`. Use `push_cast`. Conclude with `tauN_root N u _ (Cond.z_spec N).pow_eq_one`.
-/
theorem tauN_zO (u : (ZMod N)ˣ) : tauN N u • zO N = zO N ^ (u : ZMod N).val := by
  apply RingOfIntegers.ext
  show (tauN N u) ((zO N : 𝓞 (Cond.Cyc N)) : Cond.Cyc N) =
    (((zO N) ^ (u : ZMod N).val : 𝓞 (Cond.Cyc N)) : Cond.Cyc N)
  push_cast
  exact tauN_root N u _ (Cond.z_spec N).pow_eq_one

/- English proof (translation)
Establish `hx : x ∈ Algebra.adjoin ℤ {zO N}`. Rewrite using `[show Algebra.adjoin ℤ {zO N} = ⊤ from IsCyclotomicExtension.Rat.adjoin_singleton_eq_top (Cond.z_spec N)]`. Conclude with `Algebra.mem_top`. Use `Algebra.adjoin_induction (p := fun x _ => f x = g x) (fun y hy => ?_) (fun r => ?_) (fun y z _ _ h1 h2 => ?_) (fun y z _ _ h1 h2 => ?_) hx` and prove the remaining obligations. Rewrite using `[Set.mem_singleton_iff.1 hy]`.

Conclude with `h`. Simplify using `only [algebraMap_int_eq, eq_intCast, map_intCast]`. Rewrite using `[map_add, map_add, h1, h2]`. Rewrite using `[map_mul, map_mul, h1, h2]`.
-/
theorem ringHom_ext_zO {R : Type*} [CommRing R] (f g : 𝓞 (Cond.Cyc N) →+* R) (h : f (zO N) = g (zO N))
    (x : 𝓞 (Cond.Cyc N)) : f x = g x := by
  have hx : x ∈ Algebra.adjoin ℤ {zO N} := by
    rw [show Algebra.adjoin ℤ {zO N} = ⊤ from IsCyclotomicExtension.Rat.adjoin_singleton_eq_top (Cond.z_spec N)]
    exact Algebra.mem_top
  refine Algebra.adjoin_induction (p := fun x _ => f x = g x) (fun y hy => ?_) (fun r => ?_)
    (fun y z _ _ h1 h2 => ?_) (fun y z _ _ h1 h2 => ?_) hx
  · rw [Set.mem_singleton_iff.1 hy]
    exact h
  · simp only [algebraMap_int_eq, eq_intCast, map_intCast]
  · rw [map_add, map_add, h1, h2]
  · rw [map_mul, map_mul, h1, h2]

variable (l : ℕ) [Fact l.Prime] (Q : Ideal (𝓞 (Cond.Cyc N))) [Q.IsPrime] [Q.LiesOver (span {(l : ℤ)})]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `x`. Establish `hu : Q.under ℤ = span {(l : ℤ)}` using `(Ideal.LiesOver.over (P := Q) (p := span {(l : ℤ)})).symm`. Rewrite using `[← map_natCast (Ideal.Quotient.mk Q), Ideal.Quotient.eq_zero_iff_mem, show ((x : ℕ) : 𝓞 (Cond.Cyc N)) = algebraMap ℤ (𝓞 (Cond.Cyc N)) (x : ℤ) by simp, ← Ideal.mem_comap]`. Express the relevant statement in the definitionally equal form `(x : ℤ) ∈ Q.under ℤ ↔ _`.

Rewrite using `[hu, Ideal.mem_span_singleton, Int.natCast_dvd_natCast]`.
-/
theorem charP_quot : CharP (𝓞 (Cond.Cyc N) ⧸ Q) l := by
  constructor
  intro x
  have hu : Q.under ℤ = span {(l : ℤ)} := (Ideal.LiesOver.over (P := Q) (p := span {(l : ℤ)})).symm
  rw [← map_natCast (Ideal.Quotient.mk Q), Ideal.Quotient.eq_zero_iff_mem,
    show ((x : ℕ) : 𝓞 (Cond.Cyc N)) = algebraMap ℤ (𝓞 (Cond.Cyc N)) (x : ℤ) by simp, ← Ideal.mem_comap]
  change (x : ℤ) ∈ Q.under ℤ ↔ _
  rw [hu, Ideal.mem_span_singleton, Int.natCast_dvd_natCast]

/- English proof (translation)
Use `haveI := charP_quot N l Q`. Establish `hl : l.Prime` using `Fact.out`. Establish `hN0 : N ≠ 0` using `NeZero.ne N`. Establish `hnN : ordProj[l] N * ordCompl[l] N = N` using `Nat.ordProj_mul_ordCompl_eq_self N l`. Establish `hN'0 : 0 < ordCompl[l] N` using `Nat.ordCompl_pos l hN0`.

Establish `hζ` using `zO_prim N`. Establish `key1 : ∀ c, Ideal.Quotient.mk Q (zO N ^ (ordCompl[l] N * c)) = 1`. Introduce `c`. Establish `h1 : (Ideal.Quotient.mk Q (zO N ^ (ordCompl[l] N * c)) - 1) ^ (ordProj[l] N) = 0`. Rewrite using `[sub_pow_char_pow, ← map_pow, ← pow_mul, one_pow, show ordCompl[l] N * c * l ^ N.factorization l = N * c by`.

Rewrite using `[mul_right_comm, mul_comm (ordCompl[l] N), hnN],`. Use the proof step `pow_mul, hζ.pow_eq_one, one_pow, map_one, sub_self]`. Conclude with `sub_eq_zero.1 ((pow_eq_zero_iff (pow_ne_zero _ hl.ne_zero)).1 h1)`. Rewrite using `[← Ideal.Quotient.eq]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Establish `h1 : (zO N ^ (ordProj[l] N)) ^ a = (zO N ^ (ordProj[l] N)) ^ b`. Apply `root_eq_of_sub_mem Q (m := ordCompl[l] N)` to reduce the goal to its premises. Introduce `hmem`. Establish `h2 : ((ordCompl[l] N : ℕ) : 𝓞 (Cond.Cyc N) ⧸ Q) = 0`.

Rewrite using `[← map_natCast (Ideal.Quotient.mk Q), Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hmem`. Rewrite `h2` using `[CharP.cast_eq_zero_iff _ l]`. Conclude with `Nat.not_dvd_ordCompl hl hN0 h2`. Establish `ex : ordProj[l] N * (a * ordCompl[l] N) = N * a`.

Rewrite using `[mul_left_comm, hnN, mul_comm]`. Rewrite using `[← pow_mul, ← pow_mul, ex, pow_mul, hζ.pow_eq_one, one_pow]`. Establish `ex : ordProj[l] N * (b * ordCompl[l] N) = N * b`. Rewrite using `[mul_left_comm, hnN, mul_comm]`. Rewrite using `[← pow_mul, ← pow_mul, ex, pow_mul, hζ.pow_eq_one, one_pow]`.

Rewrite using `[← Ideal.Quotient.eq]`. Establish `e1 : (zO N ^ (ordProj[l] N)) ^ a = (zO N ^ a) ^ (ordProj[l] N)`. Rewrite using `[← pow_mul, ← pow_mul, mul_comm]`. Establish `e2 : (zO N ^ (ordProj[l] N)) ^ b = (zO N ^ b) ^ (ordProj[l] N)`. Rewrite using `[← pow_mul, ← pow_mul, mul_comm]`.

Rewrite using `[e1, e2, map_pow (Ideal.Quotient.mk Q) (zO N ^ a), map_pow (Ideal.Quotient.mk Q) (zO N ^ b), h]`. Establish `hprim : IsPrimitiveRoot (zO N ^ (ordProj[l] N)) (ordCompl[l] N)` using `hζ.pow_of_dvd (pow_ne_zero _ hl.ne_zero) (Nat.ordProj_dvd N l)`. Establish `e : ∀ c, (zO N ^ (ordProj[l] N)) ^ c = (zO N ^ (ordProj[l] N)) ^ (c % ordCompl[l] N)` using `fun c => by conv_lhs => rw [← Nat.mod_add_div c (ordCompl[l] N), pow_add, pow_mul, hprim.pow_eq_one, one_pow, mul_one]`. Rewrite `h1` using `[e a, e b]`. Conclude with `hprim.pow_inj (Nat.mod_lt _ hN'0) (Nat.mod_lt _ hN'0) h1`.

Introduce `h`. Break down `le_total b a with hab | hab` into its components or cases. Take `⟨c, hc⟩ : ordCompl[l] N ∣ a - b` from `(Nat.modEq_iff_dvd' hab).1 h.symm`. Establish `hac : a = b + ordCompl[l] N * c` using `by omega`. Rewrite using `[hac, pow_add, map_mul, key1, mul_one]`.

Take `⟨c, hc⟩ : ordCompl[l] N ∣ b - a` from `(Nat.modEq_iff_dvd' hab).1 h`. Establish `hbc : b = a + ordCompl[l] N * c` using `by omega`. Rewrite using `[hbc, pow_add, map_mul, key1, mul_one]`.
-/
theorem zO_sub_mem_iff (a b : ℕ) : zO N ^ a - zO N ^ b ∈ Q ↔ a ≡ b [MOD ordCompl[l] N] := by
  haveI := charP_quot N l Q
  have hl : l.Prime := Fact.out
  have hN0 : N ≠ 0 := NeZero.ne N
  have hnN : ordProj[l] N * ordCompl[l] N = N := Nat.ordProj_mul_ordCompl_eq_self N l
  have hN'0 : 0 < ordCompl[l] N := Nat.ordCompl_pos l hN0
  have hζ := zO_prim N
  have key1 : ∀ c, Ideal.Quotient.mk Q (zO N ^ (ordCompl[l] N * c)) = 1 := by
    intro c
    have h1 : (Ideal.Quotient.mk Q (zO N ^ (ordCompl[l] N * c)) - 1) ^ (ordProj[l] N) = 0 := by
      rw [sub_pow_char_pow, ← map_pow, ← pow_mul, one_pow,
        show ordCompl[l] N * c * l ^ N.factorization l = N * c by
          rw [mul_right_comm, mul_comm (ordCompl[l] N), hnN],
        pow_mul, hζ.pow_eq_one, one_pow, map_one, sub_self]
    exact sub_eq_zero.1 ((pow_eq_zero_iff (pow_ne_zero _ hl.ne_zero)).1 h1)
  rw [← Ideal.Quotient.eq]
  constructor
  · intro h
    have h1 : (zO N ^ (ordProj[l] N)) ^ a = (zO N ^ (ordProj[l] N)) ^ b := by
      apply root_eq_of_sub_mem Q (m := ordCompl[l] N)
      · intro hmem
        have h2 : ((ordCompl[l] N : ℕ) : 𝓞 (Cond.Cyc N) ⧸ Q) = 0 := by
          rw [← map_natCast (Ideal.Quotient.mk Q), Ideal.Quotient.eq_zero_iff_mem]
          exact hmem
        rw [CharP.cast_eq_zero_iff _ l] at h2
        exact Nat.not_dvd_ordCompl hl hN0 h2
      · have ex : ordProj[l] N * (a * ordCompl[l] N) = N * a := by
          rw [mul_left_comm, hnN, mul_comm]
        rw [← pow_mul, ← pow_mul, ex, pow_mul, hζ.pow_eq_one, one_pow]
      · have ex : ordProj[l] N * (b * ordCompl[l] N) = N * b := by
          rw [mul_left_comm, hnN, mul_comm]
        rw [← pow_mul, ← pow_mul, ex, pow_mul, hζ.pow_eq_one, one_pow]
      · rw [← Ideal.Quotient.eq]
        have e1 : (zO N ^ (ordProj[l] N)) ^ a = (zO N ^ a) ^ (ordProj[l] N) := by
          rw [← pow_mul, ← pow_mul, mul_comm]
        have e2 : (zO N ^ (ordProj[l] N)) ^ b = (zO N ^ b) ^ (ordProj[l] N) := by
          rw [← pow_mul, ← pow_mul, mul_comm]
        rw [e1, e2, map_pow (Ideal.Quotient.mk Q) (zO N ^ a), map_pow (Ideal.Quotient.mk Q) (zO N ^ b), h]
    have hprim : IsPrimitiveRoot (zO N ^ (ordProj[l] N)) (ordCompl[l] N) :=
      hζ.pow_of_dvd (pow_ne_zero _ hl.ne_zero) (Nat.ordProj_dvd N l)
    have e : ∀ c, (zO N ^ (ordProj[l] N)) ^ c = (zO N ^ (ordProj[l] N)) ^ (c % ordCompl[l] N) := fun c => by
      conv_lhs => rw [← Nat.mod_add_div c (ordCompl[l] N), pow_add, pow_mul, hprim.pow_eq_one, one_pow, mul_one]
    rw [e a, e b] at h1
    exact hprim.pow_inj (Nat.mod_lt _ hN'0) (Nat.mod_lt _ hN'0) h1
  · intro h
    rcases le_total b a with hab | hab
    · obtain ⟨c, hc⟩ : ordCompl[l] N ∣ a - b := (Nat.modEq_iff_dvd' hab).1 h.symm
      have hac : a = b + ordCompl[l] N * c := by omega
      rw [hac, pow_add, map_mul, key1, mul_one]
    · obtain ⟨c, hc⟩ : ordCompl[l] N ∣ b - a := (Nat.modEq_iff_dvd' hab).1 h
      have hbc : b = a + ordCompl[l] N * c := by omega
      rw [hbc, pow_add, map_mul, key1, mul_one]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h1 : zO N ^ (u : ZMod N).val - zO N ^ 1 ∈ Q`. Rewrite using `[pow_one, ← tauN_zO]`. Conclude with `h _`.

Conclude with `(zO_sub_mem_iff N l Q _ 1).1 h1`. Introduce `hu y`. Establish `hfg` using `ringHom_ext_zO N ((Ideal.Quotient.mk Q).comp (MulSemiringAction.toRingHom _ _ (tauN N u))) (Ideal.Quotient.mk Q) ?_ y`. Simplify using `only [RingHom.comp_apply, MulSemiringAction.toRingHom_apply] at hfg`. Conclude with `Ideal.Quotient.eq.1 hfg`.

Simplify using `only [RingHom.comp_apply, MulSemiringAction.toRingHom_apply]`. Rewrite using `[tauN_zO]`. Establish `h1` using `(zO_sub_mem_iff N l Q _ 1).2 hu`. Rewrite `h1` using `[pow_one]`. Conclude with `Ideal.Quotient.eq.2 h1`.
-/
theorem tauN_inertia_iff (u : (ZMod N)ˣ) :
    (∀ y : 𝓞 (Cond.Cyc N), tauN N u • y - y ∈ Q) ↔ (u : ZMod N).val ≡ 1 [MOD ordCompl[l] N] := by
  constructor
  · intro h
    have h1 : zO N ^ (u : ZMod N).val - zO N ^ 1 ∈ Q := by
      rw [pow_one, ← tauN_zO]
      exact h _
    exact (zO_sub_mem_iff N l Q _ 1).1 h1
  · intro hu y
    have hfg := ringHom_ext_zO N ((Ideal.Quotient.mk Q).comp (MulSemiringAction.toRingHom _ _ (tauN N u)))
      (Ideal.Quotient.mk Q) ?_ y
    · simp only [RingHom.comp_apply, MulSemiringAction.toRingHom_apply] at hfg
      exact Ideal.Quotient.eq.1 hfg
    · simp only [RingHom.comp_apply, MulSemiringAction.toRingHom_apply]
      rw [tauN_zO]
      have h1 := (zO_sub_mem_iff N l Q _ 1).2 hu
      rw [pow_one] at h1
      exact Ideal.Quotient.eq.2 h1

/- English proof (translation)
Use `haveI := charP_quot N l Q`. Establish `hcard : Nat.card (ℤ ⧸ Q.under ℤ) = l`. Rewrite using `[← Ideal.LiesOver.over (P := Q) (p := span {(l : ℤ)}), Nat.card_congr (Int.quotientSpanNatEquivZMod l).toEquiv, Nat.card_zmod]`. Unfold `IsArithFrobAt`. Introduce `y`.

Rewrite using `[hcard]`. Simplify using `only [MulSemiringAction.toAlgHom_apply]`. Establish `hfg` using `ringHom_ext_zO N ((Ideal.Quotient.mk Q).comp (MulSemiringAction.toRingHom _ _ (tauN N u))) ((frobenius (𝓞 (Cond.Cyc N) ⧸ Q) l).comp (Ideal.Quotient.mk Q)) ?_ y`. Simplify using `only [RingHom.comp_apply, MulSemiringAction.toRingHom_apply, frobenius_def, ← map_pow] at hfg`. Conclude with `Ideal.Quotient.eq.1 hfg`.

Simplify using `only [RingHom.comp_apply, MulSemiringAction.toRingHom_apply, frobenius_def, ← map_pow]`. Rewrite using `[tauN_zO]`. Conclude with `Ideal.Quotient.eq.2 ((zO_sub_mem_iff N l Q _ l).2 hu)`.
-/
theorem tauN_frob (u : (ZMod N)ˣ) (hu : (u : ZMod N).val ≡ l [MOD ordCompl[l] N]) : IsArithFrobAt ℤ (tauN N u) Q := by
  haveI := charP_quot N l Q
  have hcard : Nat.card (ℤ ⧸ Q.under ℤ) = l := by
    rw [← Ideal.LiesOver.over (P := Q) (p := span {(l : ℤ)}),
      Nat.card_congr (Int.quotientSpanNatEquivZMod l).toEquiv, Nat.card_zmod]
  unfold IsArithFrobAt
  intro y
  rw [hcard]
  simp only [MulSemiringAction.toAlgHom_apply]
  have hfg := ringHom_ext_zO N ((Ideal.Quotient.mk Q).comp (MulSemiringAction.toRingHom _ _ (tauN N u)))
    ((frobenius (𝓞 (Cond.Cyc N) ⧸ Q) l).comp (Ideal.Quotient.mk Q)) ?_ y
  · simp only [RingHom.comp_apply, MulSemiringAction.toRingHom_apply, frobenius_def, ← map_pow] at hfg
    exact Ideal.Quotient.eq.1 hfg
  · simp only [RingHom.comp_apply, MulSemiringAction.toRingHom_apply, frobenius_def, ← map_pow]
    rw [tauN_zO]
    exact Ideal.Quotient.eq.2 ((zO_sub_mem_iff N l Q _ l).2 hu)

end Cyc

variable {φ : Frame} (H : HostRaw φ)

/- English proof (translation)
Introduce `l _ P _ _ σ`. Use `cyc_isGalois H.condN` as an intermediate fact. Take `⟨Q, _, _, h1, -⟩` from `exists_over (emb H) l P`. Rewrite using `[h1]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨τ, h2, h3⟩`. Take `⟨u, rfl⟩` from `(tauN H.condN).surjective τ`. Conclude with `⟨u, (tauN_inertia_iff _ l Q u).mp h3, (gal_eq_art_iff H σ u).mpr h2⟩`. Introduce and unpack `⟨u, h2, h3⟩`. Conclude with `⟨_, (gal_eq_art_iff H σ u).mp h3, (tauN_inertia_iff _ l Q u).mpr h2⟩`.
-/
theorem inertia : ∀ (l : ℕ) [Fact l.Prime] (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})]
    (σ : H.E ≃ₐ[ℚ] H.E), (∀ x : 𝓞 H.E, σ • x - x ∈ P) ↔
      ∃ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ 1 [MOD ordCompl[l] H.condN] ∧ H.gal σ = H.art u := by
  intro l _ P _ _ σ
  have := cyc_isGalois H.condN
  obtain ⟨Q, _, _, h1, -⟩ := exists_over (emb H) l P
  rw [h1]
  constructor
  · rintro ⟨τ, h2, h3⟩
    obtain ⟨u, rfl⟩ := (tauN H.condN).surjective τ
    exact ⟨u, (tauN_inertia_iff _ l Q u).mp h3, (gal_eq_art_iff H σ u).mpr h2⟩
  · rintro ⟨u, h2, h3⟩
    exact ⟨_, (gal_eq_art_iff H σ u).mp h3, (tauN_inertia_iff _ l Q u).mpr h2⟩

/- English proof (translation)
Use `letI : Algebra (𝓞 H.E) (𝓞 (Cond.Cyc H.condN)) := (RingOfIntegers.mapRingHom (emb H).toRingHom).toAlgebra`. Use `haveI : Algebra.IsIntegral (𝓞 H.E) (𝓞 (Cond.Cyc H.condN)) := ⟨fun y => (RingOfIntegers.isIntegral y).tower_top⟩`. Establish `hinj : Function.Injective (RingOfIntegers.mapRingHom (emb H).toRingHom)`. Introduce `x y hxy`. Apply `RingOfIntegers.ext` to reduce the goal to its premises.

Establish `h1` using `congrArg (fun z : 𝓞 (Cond.Cyc H.condN) => (z : Cond.Cyc H.condN)) hxy`. Conclude with `(emb H).toRingHom.injective h1`. Take `⟨Q, -, hQp, hQ⟩` from `Ideal.exists_ideal_over_prime_of_isIntegral P (⊥ : Ideal (𝓞 (Cond.Cyc H.condN))) (by`. Introduce `x hx`. Rewrite `hx` using `[Ideal.mem_comap, Ideal.mem_bot]`.

Establish `hx0 : x = 0` using `hinj (hx.trans (map_zero _).symm)`. Rewrite using `[hx0]`. Conclude with `P.zero_mem)`. Use `⟨Q, hQp, ⟨?_⟩, hQ⟩` and prove the remaining obligations. Establish `hP : span {(l : ℤ)} = P.under ℤ` using `Ideal.LiesOver.over`.

Rewrite using `[hP, ← hQ]`. Use `show Ideal.comap (algebraMap ℤ (𝓞 H.E)) (Ideal.comap (algebraMap (𝓞 H.E) (𝓞 (Cond.Cyc H.condN))) Q) = Ideal.comap (algebraMap ℤ (𝓞 (Cond.Cyc H.condN))) Q`. Rewrite using `[Ideal.comap_comap]`. Use `congr 1`. Conclude with `RingHom.ext_int _ _`.
-/
private lemma lift_lemma' (l : ℕ) [Fact l.Prime] (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})] :
    ∃ Q : Ideal (𝓞 (Cond.Cyc H.condN)), Q.IsPrime ∧ Q.LiesOver (span {(l : ℤ)}) ∧
      Q.comap (RingOfIntegers.mapRingHom (emb H).toRingHom) = P := by
  classical
  letI : Algebra (𝓞 H.E) (𝓞 (Cond.Cyc H.condN)) := (RingOfIntegers.mapRingHom (emb H).toRingHom).toAlgebra
  haveI : Algebra.IsIntegral (𝓞 H.E) (𝓞 (Cond.Cyc H.condN)) :=
    ⟨fun y => (RingOfIntegers.isIntegral y).tower_top⟩
  have hinj : Function.Injective (RingOfIntegers.mapRingHom (emb H).toRingHom) := by
    intro x y hxy
    apply RingOfIntegers.ext
    have h1 := congrArg (fun z : 𝓞 (Cond.Cyc H.condN) => (z : Cond.Cyc H.condN)) hxy
    exact (emb H).toRingHom.injective h1
  obtain ⟨Q, -, hQp, hQ⟩ := Ideal.exists_ideal_over_prime_of_isIntegral P (⊥ : Ideal (𝓞 (Cond.Cyc H.condN))) (by
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_bot] at hx
    have hx0 : x = 0 := hinj (hx.trans (map_zero _).symm)
    rw [hx0]
    exact P.zero_mem)
  refine ⟨Q, hQp, ⟨?_⟩, hQ⟩
  have hP : span {(l : ℤ)} = P.under ℤ := Ideal.LiesOver.over
  rw [hP, ← hQ]
  show Ideal.comap (algebraMap ℤ (𝓞 H.E)) (Ideal.comap (algebraMap (𝓞 H.E) (𝓞 (Cond.Cyc H.condN))) Q) =
    Ideal.comap (algebraMap ℤ (𝓞 (Cond.Cyc H.condN))) Q
  rw [Ideal.comap_comap]
  congr 1
  exact RingHom.ext_int _ _

/- English proof (translation)
Take `⟨Q, hQp, hQl, hQ⟩` from `lift_lemma' H l P`. Use `haveI := hQp`. Use `haveI := hQl`. Establish `hτ` using `tauN_frob H.condN l Q u hu`. Establish `hact : ∀ x : 𝓞 H.E, RingOfIntegers.mapRingHom (emb H).toRingHom (σ • x) = tauN H.condN u • RingOfIntegers.mapRingHom (emb H).toRingHom x`.

Introduce `x`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Conclude with `(gal_eq_art_iff H σ u).1 h x`. Establish `hcard : Nat.card (ℤ ⧸ P.under ℤ) = Nat.card (ℤ ⧸ Q.under ℤ)`. Rewrite using `[← Ideal.LiesOver.over (P := P) (p := span {(l : ℤ)}), ← Ideal.LiesOver.over (P := Q) (p := span {(l : ℤ)})]`.

Unfold `IsArithFrobAt at hτ ⊢`. Introduce `x`. Rewrite using `[hcard, ← hQ, Ideal.mem_comap]`. Simplify using `only [MulSemiringAction.toAlgHom_apply] at hτ ⊢`. Rewrite using `[map_sub, map_pow, hact]`.

Conclude with `hτ _`.
-/
theorem frob_of_modEq (l : ℕ) [Fact l.Prime] (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})]
    (σ : H.E ≃ₐ[ℚ] H.E) (u : (ZMod H.condN)ˣ) (hu : (u : ZMod H.condN).val ≡ l [MOD ordCompl[l] H.condN])
    (h : H.gal σ = H.art u) : IsArithFrobAt ℤ σ P := by
  obtain ⟨Q, hQp, hQl, hQ⟩ := lift_lemma' H l P
  haveI := hQp
  haveI := hQl
  have hτ := tauN_frob H.condN l Q u hu
  have hact : ∀ x : 𝓞 H.E, RingOfIntegers.mapRingHom (emb H).toRingHom (σ • x) =
      tauN H.condN u • RingOfIntegers.mapRingHom (emb H).toRingHom x := by
    intro x
    apply RingOfIntegers.ext
    exact (gal_eq_art_iff H σ u).1 h x
  have hcard : Nat.card (ℤ ⧸ P.under ℤ) = Nat.card (ℤ ⧸ Q.under ℤ) := by
    rw [← Ideal.LiesOver.over (P := P) (p := span {(l : ℤ)}), ← Ideal.LiesOver.over (P := Q) (p := span {(l : ℤ)})]
  unfold IsArithFrobAt at hτ ⊢
  intro x
  rw [hcard, ← hQ, Ideal.mem_comap]
  simp only [MulSemiringAction.toAlgHom_apply] at hτ ⊢
  rw [map_sub, map_pow, hact]
  exact hτ _

/- English proof (translation)
Establish `hl : l.Prime` using `Fact.out`. Establish `hcop : l.Coprime (ordCompl[l] H.condN)` using `Nat.coprime_ordCompl hl (NeZero.ne _)`. Take `⟨w, hw⟩` from `exists_unit_modEq (Nat.ordCompl_dvd H.condN l) l hcop`. Conclude with `⟨H.gal.symm (H.art w), w, frob_of_modEq H l P _ w hw (by simp), hw, by simp⟩`.
-/
theorem exists_frob (l : ℕ) [Fact l.Prime] (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})] :
    ∃ (F : H.E ≃ₐ[ℚ] H.E) (w : (ZMod H.condN)ˣ), IsArithFrobAt ℤ F P ∧
      (w : ZMod H.condN).val ≡ l [MOD ordCompl[l] H.condN] ∧ H.gal F = H.art w := by
  have hl : l.Prime := Fact.out
  have hcop : l.Coprime (ordCompl[l] H.condN) := Nat.coprime_ordCompl hl (NeZero.ne _)
  obtain ⟨w, hw⟩ := exists_unit_modEq (Nat.ordCompl_dvd H.condN l) l hcop
  exact ⟨H.gal.symm (H.art w), w, frob_of_modEq H l P _ w hw (by simp), hw, by simp⟩

/- English proof (translation)
Introduce `l _ P _ _ σ`. Use `⟨fun hσ => ?_, fun ⟨u, h1, h2⟩ => frob_of_modEq H l P σ u h1 h2⟩` and prove the remaining obligations. Take `⟨F, w, hF, hw, hFw⟩` from `exists_frob H l P`. Establish `hM` using `Nat.ordCompl_dvd H.condN l`. Rewrite `hσ` using `[frob_iff_inertia P F σ hF, inertia H l P, map_mul, map_inv, hFw]`.

Take `⟨u, hu, h1⟩` from `hσ`. Use `⟨u * w, ?_, by rw [map_mul, ← h1, inv_mul_cancel_right]⟩` and prove the remaining obligations. Rewrite `hu` using `[val_modEq_one_iff hM]`. Rewrite `hw`, the goal using `[val_modEq_iff hM]`. Rewrite using `[map_mul, hu, one_mul, hw]`.
-/
theorem frob_any : ∀ (l : ℕ) [Fact l.Prime] (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})]
    (σ : H.E ≃ₐ[ℚ] H.E), IsArithFrobAt ℤ σ P ↔
      ∃ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ l [MOD ordCompl[l] H.condN] ∧ H.gal σ = H.art u := by
  intro l _ P _ _ σ
  refine ⟨fun hσ => ?_, fun ⟨u, h1, h2⟩ => frob_of_modEq H l P σ u h1 h2⟩
  obtain ⟨F, w, hF, hw, hFw⟩ := exists_frob H l P
  have hM := Nat.ordCompl_dvd H.condN l
  rw [frob_iff_inertia P F σ hF, inertia H l P, map_mul, map_inv, hFw] at hσ
  obtain ⟨u, hu, h1⟩ := hσ
  refine ⟨u * w, ?_, by rw [map_mul, ← h1, inv_mul_cancel_right]⟩
  rw [val_modEq_one_iff hM] at hu
  rw [val_modEq_iff hM] at hw ⊢
  rw [map_mul, hu, one_mul, hw]

/- English proof (translation)
Introduce `l _ P _ _ σ`. Take `⟨F, w, hF, hw, hFw⟩` from `exists_frob H l P`. Establish `hM` using `Nat.ordCompl_dvd H.condN l`. Rewrite `hw` using `[val_modEq_iff hM]`. Prove the components needed by the constructor for the conclusion.

Introduce `hσ`. Take `⟨k, ρ, hρ, rfl⟩` from `Decomp.stab_eq_inertia_mul l P F σ hF hσ`. Take `⟨u, hu, h1⟩` from `(inertia H l P ρ).mp hρ`. Use `⟨u * w ^ k, k, ?_, by rw [map_mul, map_mul, map_pow, map_pow, h1, hFw]⟩` and prove the remaining obligations. Rewrite `hu` using `[val_modEq_one_iff hM]`.

Rewrite using `[val_modEq_iff hM, map_mul, hu, one_mul, map_pow, Units.val_pow_eq_pow_val, hw, Nat.cast_pow]`. Introduce and unpack `⟨u, k, hu, h1⟩`. Establish `h2 : ∀ x : 𝓞 H.E, (σ * (F ^ k)⁻¹) • x - x ∈ P`. Rewrite using `[inertia H l P]`. Use `⟨u * (w ^ k)⁻¹, ?_, by rw [map_mul, map_mul, map_inv, map_inv, map_pow, map_pow, h1, hFw]⟩` and prove the remaining obligations.

Rewrite `hu` using `[val_modEq_iff hM]`. Establish `h3 : ZMod.unitsMap hM u = ZMod.unitsMap hM (w ^ k)` using `Units.ext (by rw [hu, map_pow, Units.val_pow_eq_pow_val, hw, Nat.cast_pow])`. Rewrite using `[val_modEq_one_iff hM, map_mul, map_inv, h3, mul_inv_cancel]`. Establish `h4` using `Subgroup.mul_mem _ (Decomp.mem_stab_of _ P (smul_mem_of_inertia _ P h2)) (Subgroup.pow_mem _ hF.mem_stabilizer k)`. Rewrite `h4` using `[inv_mul_cancel_right]`. Then use the resulting hypothesis.
-/
theorem decomp : ∀ (l : ℕ) [Fact l.Prime] (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})]
    (σ : H.E ≃ₐ[ℚ] H.E), σ ∈ MulAction.stabilizer _ P ↔
      ∃ (u : (ZMod H.condN)ˣ) (k : ℕ), (u : ZMod H.condN).val ≡ l ^ k [MOD ordCompl[l] H.condN] ∧ H.gal σ = H.art u := by
  intro l _ P _ _ σ
  obtain ⟨F, w, hF, hw, hFw⟩ := exists_frob H l P
  have hM := Nat.ordCompl_dvd H.condN l
  rw [val_modEq_iff hM] at hw
  constructor
  · intro hσ
    obtain ⟨k, ρ, hρ, rfl⟩ := Decomp.stab_eq_inertia_mul l P F σ hF hσ
    obtain ⟨u, hu, h1⟩ := (inertia H l P ρ).mp hρ
    refine ⟨u * w ^ k, k, ?_, by rw [map_mul, map_mul, map_pow, map_pow, h1, hFw]⟩
    rw [val_modEq_one_iff hM] at hu
    rw [val_modEq_iff hM, map_mul, hu, one_mul, map_pow, Units.val_pow_eq_pow_val, hw, Nat.cast_pow]
  · rintro ⟨u, k, hu, h1⟩
    have h2 : ∀ x : 𝓞 H.E, (σ * (F ^ k)⁻¹) • x - x ∈ P := by
      rw [inertia H l P]
      refine ⟨u * (w ^ k)⁻¹, ?_, by rw [map_mul, map_mul, map_inv, map_inv, map_pow, map_pow, h1, hFw]⟩
      rw [val_modEq_iff hM] at hu
      have h3 : ZMod.unitsMap hM u = ZMod.unitsMap hM (w ^ k) :=
        Units.ext (by rw [hu, map_pow, Units.val_pow_eq_pow_val, hw, Nat.cast_pow])
      rw [val_modEq_one_iff hM, map_mul, map_inv, h3, mul_inv_cancel]
    have h4 := Subgroup.mul_mem _ (Decomp.mem_stab_of _ P (smul_mem_of_inertia _ P h2))
      (Subgroup.pow_mem _ hF.mem_stabilizer k)
    rwa [inv_mul_cancel_right] at h4

end Formalism.HC.Der

end
