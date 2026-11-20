import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl ValuativeRel NumberField

namespace GlobalTheory.QpChar

open IsLocalRing

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {T : ℕ} [hT : Fact T.Prime]

/- English proof (translation)
Rewrite using `[← map_natCast (IsLocalRing.residue 𝒪[k]), IsLocalRing.residue_eq_zero_iff]`. Conclude with `(IsLocalRing.mem_maximalIdeal _).mpr hirr.not_isUnit`.
-/
theorem natCast_residue_eq_zero (hirr : Irreducible (T : 𝒪[k])) :
    ((T : ℕ) : ResidueField 𝒪[k]) = 0 := by
  rw [← map_natCast (IsLocalRing.residue 𝒪[k]), IsLocalRing.residue_eq_zero_iff]
  exact (IsLocalRing.mem_maximalIdeal _).mpr hirr.not_isUnit

/- English proof (translation)
The claim follows from `(CharP.charP_iff_prime_eq_zero hT.out).mpr (natCast_residue_eq_zero hirr)`.
-/
theorem charP_residueField_of_irreducible (hirr : Irreducible (T : 𝒪[k])) : CharP (ResidueField 𝒪[k]) T :=
  (CharP.charP_iff_prime_eq_zero hT.out).mpr (natCast_residue_eq_zero hirr)

/- English proof (translation)
The claim follows from `hirr.maximalIdeal_eq`.
-/
theorem maximalIdeal_eq (hirr : Irreducible (T : 𝒪[k])) :
    maximalIdeal 𝒪[k] = Ideal.span {(T : 𝒪[k])} :=
  hirr.maximalIdeal_eq

/- English proof (translation)
Use `haveI := charP_residueField_of_irreducible hirr`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h1 : (a : 𝒪[k]) ∈ maximalIdeal 𝒪[k]`. Rewrite using `[maximalIdeal_eq hirr, Ideal.mem_span_singleton]`.

Conclude with `h`. Establish `h2 : ((a : ℤ) : ResidueField 𝒪[k]) = 0`. Rewrite using `[← map_intCast (IsLocalRing.residue 𝒪[k]), IsLocalRing.residue_eq_zero_iff]`. Conclude with `h1`. Conclude with `(CharP.intCast_eq_zero_iff (ResidueField 𝒪[k]) T a).mp h2`.

Introduce and unpack `⟨c, rfl⟩`. Conclude with `⟨(c : 𝒪[k]), by push_cast; ring⟩`.
-/
theorem dvd_of_residue (hirr : Irreducible (T : 𝒪[k])) (a : ℤ) :
    (T : 𝒪[k]) ∣ (a : 𝒪[k]) ↔ (T : ℤ) ∣ a := by
  haveI := charP_residueField_of_irreducible hirr
  constructor
  · intro h
    have h1 : (a : 𝒪[k]) ∈ maximalIdeal 𝒪[k] := by
      rw [maximalIdeal_eq hirr, Ideal.mem_span_singleton]
      exact h
    have h2 : ((a : ℤ) : ResidueField 𝒪[k]) = 0 := by
      rw [← map_intCast (IsLocalRing.residue 𝒪[k]), IsLocalRing.residue_eq_zero_iff]
      exact h1
    exact (CharP.intCast_eq_zero_iff (ResidueField 𝒪[k]) T a).mp h2
  · rintro ⟨c, rfl⟩
    exact ⟨(c : 𝒪[k]), by push_cast; ring⟩

/- English proof (translation)
Proceed by induction on `n generalizing a with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Take `⟨b, rfl⟩` from `(ih a).mp (dvd_trans (pow_dvd_pow _ n.le_succ) h)`. Establish `hT0 : (T : 𝒪[k]) ^ n ≠ 0` using `pow_ne_zero _ hirr.ne_zero`. Establish `h' : (T : 𝒪[k]) ∣ (b : 𝒪[k])`. Rewrite `h` using `[pow_succ]`. Move the coercions through the operations in `at h`.

Conclude with `(mul_dvd_mul_iff_left hT0).mp h`. Rewrite using `[pow_succ]`. Conclude with `mul_dvd_mul_left _ ((dvd_of_residue hirr b).mp h')`. Introduce and unpack `⟨c, rfl⟩`. Conclude with `⟨(c : 𝒪[k]), by push_cast; ring⟩`.
-/
theorem pow_dvd_intCast_iff (hirr : Irreducible (T : 𝒪[k])) (n : ℕ) (a : ℤ) :
    (T : 𝒪[k]) ^ n ∣ (a : 𝒪[k]) ↔ (T : ℤ) ^ n ∣ a := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    constructor
    · intro h
      obtain ⟨b, rfl⟩ := (ih a).mp (dvd_trans (pow_dvd_pow _ n.le_succ) h)
      have hT0 : (T : 𝒪[k]) ^ n ≠ 0 := pow_ne_zero _ hirr.ne_zero
      have h' : (T : 𝒪[k]) ∣ (b : 𝒪[k]) := by
        rw [pow_succ] at h
        push_cast at h
        exact (mul_dvd_mul_iff_left hT0).mp h
      rw [pow_succ]
      exact mul_dvd_mul_left _ ((dvd_of_residue hirr b).mp h')
    · rintro ⟨c, rfl⟩
      exact ⟨(c : 𝒪[k]), by push_cast; ring⟩

/- English proof (translation)
Use `haveI := charP_residueField_of_irreducible hirr`. Use `haveI : NeZero T := ⟨hT.out.ne_zero⟩`. Establish `hbij : Function.Bijective (ZMod.castHom (dvd_refl T) (ResidueField 𝒪[k]))` using `(ZMod.castHom_injective _).bijective_of_nat_card_le (by rw [hcard, Nat.card_zmod])`. Take `⟨q, hq⟩` from `hbij.2 (IsLocalRing.residue 𝒪[k] y)`. Take `⟨b, rfl⟩` from `ZMod.intCast_surjective q`.

Use `⟨b, ?_⟩` and prove the remaining obligations. Rewrite `hq` using `[map_intCast, ← map_intCast (IsLocalRing.residue 𝒪[k])]`. Establish `h0 : IsLocalRing.residue 𝒪[k] (y - b) = 0` using `by rw [map_sub, ← hq, sub_self]`. Rewrite `h0` using `[IsLocalRing.residue_eq_zero_iff, maximalIdeal_eq hirr, Ideal.mem_span_singleton]`. Conclude with `h0`.
-/
theorem exists_residue_intCast (hcard : Nat.card (ResidueField 𝒪[k]) = T)
    (hirr : Irreducible (T : 𝒪[k])) (y : 𝒪[k]) : ∃ b : ℤ, (T : 𝒪[k]) ∣ y - b := by
  haveI := charP_residueField_of_irreducible hirr
  haveI : NeZero T := ⟨hT.out.ne_zero⟩
  have hbij : Function.Bijective (ZMod.castHom (dvd_refl T) (ResidueField 𝒪[k])) :=
    (ZMod.castHom_injective _).bijective_of_nat_card_le (by rw [hcard, Nat.card_zmod])
  obtain ⟨q, hq⟩ := hbij.2 (IsLocalRing.residue 𝒪[k] y)
  obtain ⟨b, rfl⟩ := ZMod.intCast_surjective q
  refine ⟨b, ?_⟩
  rw [map_intCast, ← map_intCast (IsLocalRing.residue 𝒪[k])] at hq
  have h0 : IsLocalRing.residue 𝒪[k] (y - b) = 0 := by rw [map_sub, ← hq, sub_self]
  rw [IsLocalRing.residue_eq_zero_iff, maximalIdeal_eq hirr, Ideal.mem_span_singleton] at h0
  exact h0

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `succ n ih`. Take `⟨a, y, hy⟩` from `ih`. Take `⟨b, z, hz⟩` from `exists_residue_intCast hcard hirr y`.

Use `⟨a + (T : ℤ) ^ n * b, z, ?_⟩` and prove the remaining obligations. Use `push_cast`. Rewrite using `[pow_succ, mul_assoc, ← hz, mul_sub, ← hy]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_intCast_sub (hcard : Nat.card (ResidueField 𝒪[k]) = T)
    (hirr : Irreducible (T : 𝒪[k])) (n : ℕ) (x : 𝒪[k]) : ∃ a : ℤ, (T : 𝒪[k]) ^ n ∣ x - a := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨a, y, hy⟩ := ih
    obtain ⟨b, z, hz⟩ := exists_residue_intCast hcard hirr y
    refine ⟨a + (T : ℤ) ^ n * b, z, ?_⟩
    push_cast
    rw [pow_succ, mul_assoc, ← hz, mul_sub, ← hy]
    ring

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `m`. Establish `h` using `pow_dvd_intCast_iff hirr n (m : ℤ)`. Rewrite `h` using `[Int.cast_natCast]`. Rewrite using `[← map_natCast (Ideal.Quotient.mk (Ideal.span {(T : 𝒪[k]) ^ n})), Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, h, ← Int.natCast_pow, Int.natCast_dvd_natCast]`.
-/
theorem charP_quot (hirr : Irreducible (T : 𝒪[k])) (n : ℕ) :
    CharP (𝒪[k] ⧸ Ideal.span {(T : 𝒪[k]) ^ n}) (T ^ n) := by
  constructor
  intro m
  have h := pow_dvd_intCast_iff hirr n (m : ℤ)
  rw [Int.cast_natCast] at h
  rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(T : 𝒪[k]) ^ n})), Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton, h, ← Int.natCast_pow, Int.natCast_dvd_natCast]

end GlobalTheory.QpChar

namespace GlobalTheory.QpChar

open IsLocalRing

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {T : ℕ} [hT : Fact T.Prime]

noncomputable def quotEquiv (hcard : Nat.card (ResidueField 𝒪[k]) = T)
    (hirr : Irreducible (T : 𝒪[k])) (n : ℕ) :
    ZMod (T ^ n) ≃+* 𝒪[k] ⧸ Ideal.span {(T : 𝒪[k]) ^ n} :=
  letI := charP_quot hirr n
  RingEquiv.ofBijective (ZMod.castHom (dvd_refl _) _) ⟨ZMod.castHom_injective _, by
    intro q
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨a, ha⟩ := exists_intCast_sub hcard hirr n x
    refine ⟨a, ?_⟩
    rw [map_intCast, ← map_intCast (Ideal.Quotient.mk (Ideal.span {(T : 𝒪[k]) ^ n})), Ideal.Quotient.eq,
      Ideal.mem_span_singleton]
    exact (dvd_sub_comm).mp ha⟩

/- English proof (translation)
Simplify using `only [map_intCast]`.
-/
theorem quotEquiv_intCast (hcard : Nat.card (ResidueField 𝒪[k]) = T)
    (hirr : Irreducible (T : 𝒪[k])) (n : ℕ) (a : ℤ) :
    quotEquiv hcard hirr n (a : ZMod (T ^ n)) = Ideal.Quotient.mk _ (a : 𝒪[k]) := by
  simp only [map_intCast]

noncomputable def red (hcard : Nat.card (ResidueField 𝒪[k]) = T)
    (hirr : Irreducible (T : 𝒪[k])) (n : ℕ) : 𝒪[k] →+* ZMod (T ^ n) :=
  (quotEquiv hcard hirr n).symm.toRingHom.comp (Ideal.Quotient.mk _)

/- English proof (translation)
Establish `h1 : Ideal.Quotient.mk (Ideal.span {(T : 𝒪[k]) ^ n}) x = quotEquiv hcard hirr n (a : ZMod (T ^ n))`. Rewrite using `[quotEquiv_intCast, Ideal.Quotient.eq, Ideal.mem_span_singleton]`. Conclude with `h`. Use `show (quotEquiv hcard hirr n).symm (Ideal.Quotient.mk _ x) = _`. Rewrite using `[h1, RingEquiv.symm_apply_apply]`.
-/
theorem red_eq (hcard : Nat.card (ResidueField 𝒪[k]) = T)
    (hirr : Irreducible (T : 𝒪[k])) (n : ℕ) (x : 𝒪[k]) (a : ℤ) (h : (T : 𝒪[k]) ^ n ∣ x - a) :
    red hcard hirr n x = a := by
  have h1 : Ideal.Quotient.mk (Ideal.span {(T : 𝒪[k]) ^ n}) x = quotEquiv hcard hirr n (a : ZMod (T ^ n)) := by
    rw [quotEquiv_intCast, Ideal.Quotient.eq, Ideal.mem_span_singleton]
    exact h
  show (quotEquiv hcard hirr n).symm (Ideal.Quotient.mk _ x) = _
  rw [h1, RingEquiv.symm_apply_apply]

/- English proof (translation)
Use `RingHom.ext fun x => ?_` and prove the remaining obligations. Take `⟨a, ha⟩` from `exists_intCast_sub hcard hirr k2 x`. Rewrite using `[RingHom.comp_apply, red_eq hcard hirr k2 x a ha, map_intCast, red_eq hcard hirr k1 x a (dvd_trans (pow_dvd_pow _ hk) ha)]`.
-/
theorem red_compat (hcard : Nat.card (ResidueField 𝒪[k]) = T)
    (hirr : Irreducible (T : 𝒪[k])) (k1 k2 : ℕ) (hk : k1 ≤ k2) :
    (ZMod.castHom (pow_dvd_pow T hk) (ZMod (T ^ k1))).comp (red hcard hirr k2) = red hcard hirr k1 := by
  refine RingHom.ext fun x => ?_
  obtain ⟨a, ha⟩ := exists_intCast_sub hcard hirr k2 x
  rw [RingHom.comp_apply, red_eq hcard hirr k2 x a ha, map_intCast,
    red_eq hcard hirr k1 x a (dvd_trans (pow_dvd_pow _ hk) ha)]

end GlobalTheory.QpChar

namespace GlobalTheory.QpChar

open IsLocalRing

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {T : ℕ} [hT : Fact T.Prime]

/- English proof (translation)
Rewrite using `[← PadicInt.ker_toZModPow, RingHom.mem_ker, map_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_pow]`.
-/
theorem padic_intCast_mem_span_iff (m : ℕ) (c : ℤ) :
    (c : ℤ_[T]) ∈ Ideal.span {(T : ℤ_[T]) ^ m} ↔ (T : ℤ) ^ m ∣ c := by
  rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd,
    Nat.cast_pow]

/- English proof (translation)
Use `letI := IsTopologicalAddGroup.rightUniformSpace k`. Use `haveI := isUniformAddGroup_of_addCommGroup (G := k)`. Use `infer_instance`.
-/
theorem isAdicComplete_integer : IsAdicComplete (maximalIdeal 𝒪[k]) 𝒪[k] := by
  letI := IsTopologicalAddGroup.rightUniformSpace k
  haveI := isUniformAddGroup_of_addCommGroup (G := k)
  infer_instance

noncomputable def toPadic (hcard : Nat.card (ResidueField 𝒪[k]) = T)
    (hirr : Irreducible (T : 𝒪[k])) : 𝒪[k] →+* ℤ_[T] :=
  PadicInt.lift (red_compat hcard hirr)

/- English proof (translation)
Unfold `toPadic`. Rewrite using `[← RingHom.comp_apply, PadicInt.lift_spec]`.
-/
theorem toZModPow_toPadic (hcard : Nat.card (ResidueField 𝒪[k]) = T)
    (hirr : Irreducible (T : 𝒪[k])) (n : ℕ) (x : 𝒪[k]) :
    PadicInt.toZModPow n (toPadic hcard hirr x) = red hcard hirr n x := by
  unfold toPadic
  rw [← RingHom.comp_apply, PadicInt.lift_spec]

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Establish `hdiv : ∀ n : ℕ, (T : 𝒪[k]) ^ n ∣ x`. Introduce `n`. Take `⟨a, ha⟩` from `exists_intCast_sub hcard hirr n x`.

Establish `h1` using `toZModPow_toPadic hcard hirr n x`. Rewrite `h1` using `[hx, map_zero, red_eq hcard hirr n x a ha, eq_comm, ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_pow, ← pow_dvd_intCast_iff hirr]`. Establish `h2` using `dvd_add ha h1`. Simplify using `using h2`. Assume the negation of the conclusion as `hne`.

Take `⟨n, u, hu⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hirr`. Take `⟨c, hc⟩` from `hdiv (n + 1)`. Establish `hT0 : (T : 𝒪[k]) ^ n ≠ 0` using `pow_ne_zero _ hirr.ne_zero`. Establish `hu' : (u : 𝒪[k]) = T * c`. Apply `mul_right_cancel₀ hT0` to reduce the goal to its premises.

Rewrite using `[← hu, hc]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `hirr.not_isUnit (isUnit_of_dvd_unit ⟨c, hu'⟩ u.isUnit)`.
-/
theorem toPadic_injective (hcard : Nat.card (ResidueField 𝒪[k]) = T)
    (hirr : Irreducible (T : 𝒪[k])) : Function.Injective (toPadic hcard hirr) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hdiv : ∀ n : ℕ, (T : 𝒪[k]) ^ n ∣ x := by
    intro n
    obtain ⟨a, ha⟩ := exists_intCast_sub hcard hirr n x
    have h1 := toZModPow_toPadic hcard hirr n x
    rw [hx, map_zero, red_eq hcard hirr n x a ha, eq_comm, ZMod.intCast_zmod_eq_zero_iff_dvd,
      Nat.cast_pow, ← pow_dvd_intCast_iff hirr] at h1
    have h2 := dvd_add ha h1
    simpa using h2
  by_contra hne
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hirr
  obtain ⟨c, hc⟩ := hdiv (n + 1)
  have hT0 : (T : 𝒪[k]) ^ n ≠ 0 := pow_ne_zero _ hirr.ne_zero
  have hu' : (u : 𝒪[k]) = T * c := by
    apply mul_right_cancel₀ hT0
    rw [← hu, hc]
    ring
  exact hirr.not_isUnit (isUnit_of_dvd_unit ⟨c, hu'⟩ u.isUnit)

/- English proof (translation)
Introduce `z`. Use `haveI := isAdicComplete_integer (k := k)`. Establish `hI : ∀ m : ℕ, ((maximalIdeal 𝒪[k]) ^ m • ⊤ : Submodule 𝒪[k] 𝒪[k]) = Ideal.span {(T : 𝒪[k]) ^ m}`. Introduce `m`. Rewrite using `[Ideal.smul_eq_mul, Ideal.mul_top, maximalIdeal_eq hirr, Ideal.span_singleton_pow]`.

Establish `key : ∀ m n : ℕ, m ≤ n → (T : 𝒪[k]) ^ m ∣ ((PadicInt.appr z n : ℕ) : 𝒪[k]) - ((PadicInt.appr z m : ℕ) : 𝒪[k])`. Introduce `m n hmn`. Establish `h1 : (((PadicInt.appr z n : ℤ) - (PadicInt.appr z m : ℤ) : ℤ) : ℤ_[T]) ∈ Ideal.span {(T : ℤ_[T]) ^ m}`. Establish `e1` using `Ideal.mem_span_singleton.mp (PadicInt.appr_spec m z)`. Establish `e2` using `Ideal.mem_span_singleton.mp (PadicInt.appr_spec n z)`.

Rewrite using `[Ideal.mem_span_singleton]`. Establish `h3` using `dvd_sub e1 (dvd_trans (pow_dvd_pow _ hmn) e2)`. Establish `h4 : (((PadicInt.appr z n : ℤ) - (PadicInt.appr z m : ℤ) : ℤ) : ℤ_[T]) = (z - (PadicInt.appr z m : ℤ_[T])) - (z - (PadicInt.appr z n : ℤ_[T]))`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h4]`. Conclude with `h3`. Establish `h2` using `(pow_dvd_intCast_iff hirr m _).mpr ((padic_intCast_mem_span_iff m _).mp h1)`. Move the coercions through the operations in `at h2`. Conclude with `h2`.

Take `⟨L, hL⟩` from `IsPrecomplete.prec (I := maximalIdeal 𝒪[k]) inferInstance (f := fun n => ((PadicInt.appr z n : ℕ) : 𝒪[k])) (fun {m n} hmn => by`. Rewrite using `[SModEq.sub_mem, hI, Ideal.mem_span_singleton, dvd_sub_comm]`. Conclude with `key m n hmn)`. Use `⟨L, PadicInt.ext_of_toZModPow.mp fun n => ?_⟩` and prove the remaining obligations. Establish `hLn : (T : 𝒪[k]) ^ n ∣ L - (((PadicInt.appr z n : ℕ) : ℤ) : 𝒪[k])`.

Establish `h5` using `hL n`. Rewrite `h5` using `[SModEq.sub_mem, hI, Ideal.mem_span_singleton]`. Rewrite using `[Int.cast_natCast, dvd_sub_comm]`. Conclude with `h5`. Establish `hz : z - (PadicInt.appr z n : ℤ_[T]) ∈ RingHom.ker (PadicInt.toZModPow n : ℤ_[T] →+* ZMod (T ^ n))`.

Rewrite using `[PadicInt.ker_toZModPow]`. Conclude with `PadicInt.appr_spec n z`. Rewrite `hz` using `[RingHom.mem_ker, map_sub, sub_eq_zero]`. Rewrite using `[toZModPow_toPadic, red_eq hcard hirr n L _ hLn, hz, map_natCast, Int.cast_natCast]`.
-/
theorem toPadic_surjective (hcard : Nat.card (ResidueField 𝒪[k]) = T)
    (hirr : Irreducible (T : 𝒪[k])) : Function.Surjective (toPadic hcard hirr) := by
  intro z
  haveI := isAdicComplete_integer (k := k)
  have hI : ∀ m : ℕ, ((maximalIdeal 𝒪[k]) ^ m • ⊤ : Submodule 𝒪[k] 𝒪[k]) = Ideal.span {(T : 𝒪[k]) ^ m} := by
    intro m
    rw [Ideal.smul_eq_mul, Ideal.mul_top, maximalIdeal_eq hirr, Ideal.span_singleton_pow]
  have key : ∀ m n : ℕ, m ≤ n →
      (T : 𝒪[k]) ^ m ∣ ((PadicInt.appr z n : ℕ) : 𝒪[k]) - ((PadicInt.appr z m : ℕ) : 𝒪[k]) := by
    intro m n hmn
    have h1 : (((PadicInt.appr z n : ℤ) - (PadicInt.appr z m : ℤ) : ℤ) : ℤ_[T]) ∈
        Ideal.span {(T : ℤ_[T]) ^ m} := by
      have e1 := Ideal.mem_span_singleton.mp (PadicInt.appr_spec m z)
      have e2 := Ideal.mem_span_singleton.mp (PadicInt.appr_spec n z)
      rw [Ideal.mem_span_singleton]
      have h3 := dvd_sub e1 (dvd_trans (pow_dvd_pow _ hmn) e2)
      have h4 : (((PadicInt.appr z n : ℤ) - (PadicInt.appr z m : ℤ) : ℤ) : ℤ_[T]) =
          (z - (PadicInt.appr z m : ℤ_[T])) - (z - (PadicInt.appr z n : ℤ_[T])) := by
        push_cast
        ring
      rw [h4]
      exact h3
    have h2 := (pow_dvd_intCast_iff hirr m _).mpr ((padic_intCast_mem_span_iff m _).mp h1)
    push_cast at h2
    exact h2
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := maximalIdeal 𝒪[k]) inferInstance
    (f := fun n => ((PadicInt.appr z n : ℕ) : 𝒪[k])) (fun {m n} hmn => by
      rw [SModEq.sub_mem, hI, Ideal.mem_span_singleton, dvd_sub_comm]
      exact key m n hmn)
  refine ⟨L, PadicInt.ext_of_toZModPow.mp fun n => ?_⟩
  have hLn : (T : 𝒪[k]) ^ n ∣ L - (((PadicInt.appr z n : ℕ) : ℤ) : 𝒪[k]) := by
    have h5 := hL n
    rw [SModEq.sub_mem, hI, Ideal.mem_span_singleton] at h5
    rw [Int.cast_natCast, dvd_sub_comm]
    exact h5
  have hz : z - (PadicInt.appr z n : ℤ_[T]) ∈
      RingHom.ker (PadicInt.toZModPow n : ℤ_[T] →+* ZMod (T ^ n)) := by
    rw [PadicInt.ker_toZModPow]
    exact PadicInt.appr_spec n z
  rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hz
  rw [toZModPow_toPadic, red_eq hcard hirr n L _ hLn, hz, map_natCast, Int.cast_natCast]

end GlobalTheory.QpChar

namespace GlobalTheory.QpChar

open IsLocalRing Filter Topology

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {T : ℕ} [hT : Fact T.Prime]

noncomputable def intEquiv (hcard : Nat.card (ResidueField 𝒪[k]) = T)
    (hirr : Irreducible (T : 𝒪[k])) : 𝒪[k] ≃+* ℤ_[T] :=
  RingEquiv.ofBijective (toPadic hcard hirr) ⟨toPadic_injective hcard hirr, toPadic_surjective hcard hirr⟩

/- English proof (translation)
Establish `h` using `(Valuation.Integer.not_isUnit_iff_valuation_lt_one (v := valuation k)).mp hirr.not_isUnit`. Establish `hc : ((T : 𝒪[k]) : k) = (T : k)` using `by simp`. Rewrite `h` using `[hc]`. Then use the resulting hypothesis.
-/
theorem valuation_T_lt_one (hirr : Irreducible (T : 𝒪[k])) : valuation k (T : k) < 1 := by
  have h := (Valuation.Integer.not_isUnit_iff_valuation_lt_one (v := valuation k)).mp hirr.not_isUnit
  have hc : ((T : 𝒪[k]) : k) = (T : k) := by simp
  rwa [hc] at h

/- English proof (translation)
Rewrite using `[ne_eq, map_eq_zero]`. Introduce `h`. Conclude with `hirr.ne_zero (Subtype.ext (by simpa using h))`.
-/
theorem valuation_T_ne_zero (hirr : Irreducible (T : 𝒪[k])) : valuation k (T : k) ≠ 0 := by
  rw [ne_eq, map_eq_zero]
  intro h
  exact hirr.ne_zero (Subtype.ext (by simpa using h))

/- English proof (translation)
Rewrite using `[(Valuation.integer.integers (valuation k)).dvd_iff_le]`. Simplify using `only [map_pow, map_natCast]`. Both sides reduce to the same expression.
-/
theorem valuation_le_T_pow_iff (hirr : Irreducible (T : 𝒪[k])) (o : 𝒪[k]) (n : ℕ) :
    valuation k (o : k) ≤ valuation k (T : k) ^ n ↔ (T : 𝒪[k]) ^ n ∣ o := by
  rw [(Valuation.integer.integers (valuation k)).dvd_iff_le]
  simp only [map_pow, map_natCast]
  rfl

/- English proof (translation)
Use `haveI : MulArchimedean (ValueGroupWithZero k) := ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance`. Take `⟨n, hn⟩` from `exists_pow_lt₀ (valuation_T_lt_one hirr) (Units.mk0 γ hγ)`. Conclude with `⟨n, hn⟩`.
-/
theorem exists_T_pow_lt (hirr : Irreducible (T : 𝒪[k])) (γ : ValueGroupWithZero k) (hγ : γ ≠ 0) :
    ∃ n : ℕ, valuation k (T : k) ^ n < γ := by
  haveI : MulArchimedean (ValueGroupWithZero k) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨n, hn⟩ := exists_pow_lt₀ (valuation_T_lt_one hirr) (Units.mk0 γ hγ)
  exact ⟨n, hn⟩

end GlobalTheory.QpChar

namespace GlobalTheory.QpChar

open IsLocalRing Filter Topology

/- English proof (translation)
Introduce `k _ _ _ _ _ _ T hT hcard hirr`. Establish `hTpos : (0 : ℝ) < T` using `by exact_mod_cast hT.out.pos`. Establish `hT0 : (T : ℚ_[T]) ≠ 0` using `by exact_mod_cast hT.out.ne_zero`. Set `e : ℤ_[T] ≃+* 𝒪[k]` to `(intEquiv hcard hirr).symm`. Set `φ : ℚ_[T] ≃+* k` to `IsFractionRing.ringEquivOfRingEquiv e`.

Establish `hφ : ∀ z : ℤ_[T], φ (z : ℚ_[T]) = ((e z : 𝒪[k]) : k)` using `fun z => IsFractionRing.ringEquivOfRingEquiv_algebraMap e z`. Establish `hmem : ∀ x : ℚ_[T], φ x ∈ 𝒪[k] ↔ ‖x‖ ≤ 1`. Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`.

Establish `h1 : φ ((e.symm ⟨φ x, hx⟩ : ℤ_[T]) : ℚ_[T]) = φ x`. Rewrite using `[hφ, RingEquiv.apply_symm_apply]`. Rewrite using `[← φ.injective h1]`. Conclude with `PadicInt.norm_le_one _`. Introduce `hx`.

Establish `h1 : φ x = ((e ⟨x, hx⟩ : 𝒪[k]) : k)` using `hφ ⟨x, hx⟩`. Rewrite using `[h1]`. Conclude with `(e ⟨x, hx⟩).2`. Establish `hcont : Continuous φ`. Apply `continuous_of_continuousAt_zero (φ : ℚ_[T] →+* k)` to reduce the goal to its premises.

Rewrite using `[ContinuousAt, map_zero, (IsValuativeTopology.hasBasis_nhds_zero' k).tendsto_right_iff]`. Introduce `γ hγ`. Take `⟨n, hn⟩` from `exists_T_pow_lt hirr γ hγ`. Establish `hball : Metric.closedBall (0 : ℚ_[T]) ((T : ℝ) ^ (-(n : ℤ))) ∈ 𝓝 (0 : ℚ_[T])` using `Metric.closedBall_mem_nhds _ (zpow_pos hTpos _)`. Use `filter_upwards [hball] with x hx`.

Rewrite `hx` using `[Metric.mem_closedBall, dist_zero_right]`. Establish `hy : ‖x / (T : ℚ_[T]) ^ n‖ ≤ 1`. Rewrite using `[norm_div, Padic.norm_p_pow, div_le_one (zpow_pos hTpos _)]`. Conclude with `hx`. Establish `hyO` using `(hmem _).mpr hy`.

Establish `hx' : x = (T : ℚ_[T]) ^ n * (x / (T : ℚ_[T]) ^ n)`. Clear the denominators using the available nonvanishing facts. Use `show valuation k (φ x) < γ`. Rewrite using `[hx', map_mul, map_pow, map_natCast, map_mul, map_pow]`. Establish `hle : valuation k (T : k) ^ n * valuation k (φ (x / (T : ℚ_[T]) ^ n)) ≤ valuation k (T : k) ^ n * 1` using `mul_le_mul_right ((Valuation.mem_integer_iff _ _).mp hyO) _`.

Rewrite `hle` using `[mul_one]`. Conclude with `lt_of_le_of_lt hle hn`. Establish `hsymm : Continuous φ.symm`. Apply `continuous_of_continuousAt_zero (φ.symm : k →+* ℚ_[T])` to reduce the goal to its premises. Rewrite using `[ContinuousAt, map_zero, Metric.nhds_basis_closedBall.tendsto_right_iff]`.

Introduce `ε hε`. Establish `hTinv : ((T : ℝ))⁻¹ < 1` using `inv_lt_one_of_one_lt₀ (by exact_mod_cast hT.out.one_lt)`. Take `⟨n, hn⟩` from `exists_pow_lt_of_lt_one hε hTinv`. Establish `hγ : valuation k (T : k) ^ n ≠ 0` using `pow_ne_zero _ (valuation_T_ne_zero hirr)`. Use `filter_upwards [(IsValuativeTopology.hasBasis_nhds_zero' k).mem_of_mem hγ] with y hy`.

Establish `hy1 : valuation k y < valuation k (T : k) ^ n` using `hy`. Establish `hyO : valuation k y ≤ 1` using `hy1.le.trans (pow_le_one₀ zero_le' (valuation_T_lt_one hirr).le)`. Take `⟨w, hw⟩` from `(valuation_le_T_pow_iff hirr ⟨y, hyO⟩ n).mp hy1.le`. Establish `hy' : y = (T : k) ^ n * (w : k)`. Establish `h6` using `congrArg (fun t : 𝒪[k] => (t : k)) hw`.

Simplify using `using h6`. Establish `hw1 : ‖φ.symm (w : k)‖ ≤ 1` using `(hmem _).mp (by rw [RingEquiv.apply_symm_apply]; exact w.2)`. Rewrite using `[Metric.mem_closedBall, dist_zero_right, hy', map_mul, map_pow, map_natCast, norm_mul, Padic.norm_p_pow]`. Establish `h7 : (T : ℝ) ^ (-(n : ℤ)) = ((T : ℝ)⁻¹) ^ n`. Rewrite using `[zpow_neg, zpow_natCast, inv_pow]`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `⟨φ, hcont, hsymm, hmem⟩`.
-/
theorem exists_ringEquiv_padic : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [IsTopologicalRing k] [CharZero k] (T : ℕ) [Fact T.Prime], Nat.card (IsLocalRing.ResidueField 𝒪[k]) = T → Irreducible (T : 𝒪[k]) → ∃ φ : ℚ_[T] ≃+* k, Continuous φ ∧ Continuous φ.symm ∧ ∀ x : ℚ_[T], φ x ∈ 𝒪[k] ↔ ‖x‖ ≤ 1 := by
  intro k _ _ _ _ _ _ T hT hcard hirr
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT.out.pos
  have hT0 : (T : ℚ_[T]) ≠ 0 := by exact_mod_cast hT.out.ne_zero
  let e : ℤ_[T] ≃+* 𝒪[k] := (intEquiv hcard hirr).symm
  let φ : ℚ_[T] ≃+* k := IsFractionRing.ringEquivOfRingEquiv e
  have hφ : ∀ z : ℤ_[T], φ (z : ℚ_[T]) = ((e z : 𝒪[k]) : k) := fun z =>
    IsFractionRing.ringEquivOfRingEquiv_algebraMap e z
  have hmem : ∀ x : ℚ_[T], φ x ∈ 𝒪[k] ↔ ‖x‖ ≤ 1 := by
    intro x
    constructor
    · intro hx
      have h1 : φ ((e.symm ⟨φ x, hx⟩ : ℤ_[T]) : ℚ_[T]) = φ x := by
        rw [hφ, RingEquiv.apply_symm_apply]
      rw [← φ.injective h1]
      exact PadicInt.norm_le_one _
    · intro hx
      have h1 : φ x = ((e ⟨x, hx⟩ : 𝒪[k]) : k) := hφ ⟨x, hx⟩
      rw [h1]
      exact (e ⟨x, hx⟩).2
  have hcont : Continuous φ := by
    apply continuous_of_continuousAt_zero (φ : ℚ_[T] →+* k)
    rw [ContinuousAt, map_zero, (IsValuativeTopology.hasBasis_nhds_zero' k).tendsto_right_iff]
    intro γ hγ
    obtain ⟨n, hn⟩ := exists_T_pow_lt hirr γ hγ
    have hball : Metric.closedBall (0 : ℚ_[T]) ((T : ℝ) ^ (-(n : ℤ))) ∈ 𝓝 (0 : ℚ_[T]) :=
      Metric.closedBall_mem_nhds _ (zpow_pos hTpos _)
    filter_upwards [hball] with x hx
    rw [Metric.mem_closedBall, dist_zero_right] at hx
    have hy : ‖x / (T : ℚ_[T]) ^ n‖ ≤ 1 := by
      rw [norm_div, Padic.norm_p_pow, div_le_one (zpow_pos hTpos _)]
      exact hx
    have hyO := (hmem _).mpr hy
    have hx' : x = (T : ℚ_[T]) ^ n * (x / (T : ℚ_[T]) ^ n) := by
      field_simp
    show valuation k (φ x) < γ
    rw [hx', map_mul, map_pow, map_natCast, map_mul, map_pow]
    have hle : valuation k (T : k) ^ n * valuation k (φ (x / (T : ℚ_[T]) ^ n)) ≤
        valuation k (T : k) ^ n * 1 :=
      mul_le_mul_right ((Valuation.mem_integer_iff _ _).mp hyO) _
    rw [mul_one] at hle
    exact lt_of_le_of_lt hle hn
  have hsymm : Continuous φ.symm := by
    apply continuous_of_continuousAt_zero (φ.symm : k →+* ℚ_[T])
    rw [ContinuousAt, map_zero, Metric.nhds_basis_closedBall.tendsto_right_iff]
    intro ε hε
    have hTinv : ((T : ℝ))⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hT.out.one_lt)
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hTinv
    have hγ : valuation k (T : k) ^ n ≠ 0 := pow_ne_zero _ (valuation_T_ne_zero hirr)
    filter_upwards [(IsValuativeTopology.hasBasis_nhds_zero' k).mem_of_mem hγ] with y hy
    have hy1 : valuation k y < valuation k (T : k) ^ n := hy
    have hyO : valuation k y ≤ 1 :=
      hy1.le.trans (pow_le_one₀ zero_le' (valuation_T_lt_one hirr).le)
    obtain ⟨w, hw⟩ := (valuation_le_T_pow_iff hirr ⟨y, hyO⟩ n).mp hy1.le
    have hy' : y = (T : k) ^ n * (w : k) := by
      have h6 := congrArg (fun t : 𝒪[k] => (t : k)) hw
      simpa using h6
    have hw1 : ‖φ.symm (w : k)‖ ≤ 1 := (hmem _).mp (by rw [RingEquiv.apply_symm_apply]; exact w.2)
    rw [Metric.mem_closedBall, dist_zero_right, hy', map_mul, map_pow, map_natCast, norm_mul,
      Padic.norm_p_pow]
    have h7 : (T : ℝ) ^ (-(n : ℤ)) = ((T : ℝ)⁻¹) ^ n := by
      rw [zpow_neg, zpow_natCast, inv_pow]
    calc (T : ℝ) ^ (-(n : ℤ)) * ‖φ.symm (w : k)‖ ≤ (T : ℝ) ^ (-(n : ℤ)) * 1 :=
          mul_le_mul_of_nonneg_left hw1 (zpow_pos hTpos _).le
      _ = ((T : ℝ)⁻¹) ^ n := by rw [mul_one, h7]
      _ ≤ ε := hn.le
  exact ⟨φ, hcont, hsymm, hmem⟩

end GlobalTheory.QpChar
