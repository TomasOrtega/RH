import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.CoprimeTwoPow
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Orbits
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.OrbitSg
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.OrderOfSignGroupDvdTwo
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.CardExtendedGaloisGroup
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.ThickOrbit

noncomputable section

namespace Formalism.HC.Frame

open Formalism.FrobeniusOrbits

variable (φ : Frame)

/- English proof (translation)
Use `show Nat.card (Fin φ.ord) = φ.ord`. Rewrite using `[Nat.card_eq_fintype_card, Fintype.card_fin]`.
-/
private theorem natCard_A_eq_ord : Nat.card φ.A = φ.ord := by
  show Nat.card (Fin φ.ord) = φ.ord
  rw [Nat.card_eq_fintype_card, Fintype.card_fin]

/- English proof (translation)
Rewrite using `[Nat.card_congr (Multiplicative.ofAdd (α := φ.A)).symm]`. Conclude with `natCard_A_eq_ord φ`.
-/
theorem natCard_MA : Nat.card φ.MA = φ.ord := by
  rw [Nat.card_congr (Multiplicative.ofAdd (α := φ.A)).symm]
  exact natCard_A_eq_ord φ

/- English proof (translation)
Rewrite using `[← Nat.card_eq_fintype_card, φ.natCard_MA]`.
-/
theorem card_MA : Fintype.card φ.MA = φ.ord := by
  rw [← Nat.card_eq_fintype_card, φ.natCard_MA]

/- English proof (translation)
Use `first`. Consider the case `(rw [Nat.card_eq_fintype_card]; rfl)`. Consider the case `(rw [Nat.card_eq_fintype_card]; decide)`. Consider the case `simp`.
-/
private theorem natCard_int_units_eq_two : Nat.card ℤˣ = 2 := by
  first
  | (rw [Nat.card_eq_fintype_card]; rfl)
  | (rw [Nat.card_eq_fintype_card]; decide)
  | simp

/- English proof (translation)
Establish `h3 : Nat.card φ.GG = Nat.card ℤˣ * Nat.card ℤˣ * Nat.card φ.MA`. Rewrite using `[Nat.card_prod, Nat.card_prod]`. Rewrite `h3` using `[natCard_int_units_eq_two, φ.natCard_MA]`. Use linear arithmetic over natural numbers and integers.
-/
private theorem natCard_GG_eq_four_mul_ord : Nat.card φ.GG = 4 * φ.ord := by
  have h3 : Nat.card φ.GG = Nat.card ℤˣ * Nat.card ℤˣ * Nat.card φ.MA := by
    rw [Nat.card_prod, Nat.card_prod]
  rw [natCard_int_units_eq_two, φ.natCard_MA] at h3
  omega

/- English proof (translation)
Rewrite using `[← Nat.card_eq_fintype_card, natCard_GG_eq_four_mul_ord]`.
-/
theorem card_GG [Fintype φ.GG] : Fintype.card φ.GG = 4 * φ.ord := by
  rw [← Nat.card_eq_fintype_card, natCard_GG_eq_four_mul_ord]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem chD_apply (g : φ.GG) : φ.chD g = g.1.2 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem chQ_apply (g : φ.GG) : φ.chQ g = g.1.1 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem chC_apply (g : φ.GG) : ((φ.chC g : ℂˣ) : ℂ) = (((g.1.2 : ℤˣ) : ℤ) : ℂ) := rfl

/- English proof (translation)
Establish `hs : Function.Surjective φ.chD` using `fun u => ⟨((1, u), 1), rfl⟩`. Use `show φ.chD.ker.index = 2`. Rewrite using `[Subgroup.index_ker, MonoidHom.range_eq_top.2 hs, Subgroup.card_top, natCard_int_units_eq_two]`.
-/
theorem index_Psi : φ.Psi.index = 2 := by
  have hs : Function.Surjective φ.chD := fun u => ⟨((1, u), 1), rfl⟩
  show φ.chD.ker.index = 2
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hs, Subgroup.card_top, natCard_int_units_eq_two]

/- English proof (translation)
Establish `h` using `φ.Psi.card_mul_index`. Rewrite `h` using `[φ.index_Psi, natCard_GG_eq_four_mul_ord]`. Use linear arithmetic over natural numbers and integers.
-/
theorem natCard_Psi : Nat.card φ.Psi = 2 * φ.ord := by
  have h := φ.Psi.card_mul_index
  rw [φ.index_Psi, natCard_GG_eq_four_mul_ord] at h
  omega

/- English proof (translation)
Introduce `h`. Establish `h'` using `congrArg (fun u : ℤˣ => (u : ℤ)) h`. Evaluate the numerical expressions using `at h'`.
-/
private theorem int_units_neg_one_ne_one : (-1 : ℤˣ) ≠ 1 := by
  intro h
  have h' := congrArg (fun u : ℤˣ => (u : ℤ)) h
  norm_num at h'

/- English proof (translation)
Rewrite using `[mem_Psi_iff]`. Conclude with `int_units_neg_one_ne_one`.
-/
theorem cc_notMem_Psi : φ.cc ∉ φ.Psi := by
  rw [mem_Psi_iff]
  exact int_units_neg_one_ne_one

/- English proof (translation)
Rewrite using `[mem_Psi_iff]`. Conclude with `int_units_neg_one_ne_one`.
-/
theorem iod_notMem_Psi : φ.iod ∉ φ.Psi := by
  rw [mem_Psi_iff]
  exact int_units_neg_one_ne_one

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sg_mem_Psi : φ.sg ∈ φ.Psi := rfl

/- English proof (translation)
Use `show ((c0, 1) : φ.GG) * (c0, 1) = 1`. Simplify using `[c0]`.
-/
theorem cc_mul_cc : φ.cc * φ.cc = 1 := by
  show ((c0, 1) : φ.GG) * (c0, 1) = 1
  simp [c0]

/- English proof (translation)
Introduce `h`. Conclude with `φ.cc_notMem_Psi (h ▸ φ.Psi.one_mem)`.
-/
theorem cc_ne_one : φ.cc ≠ 1 := by
  intro h
  exact φ.cc_notMem_Psi (h ▸ φ.Psi.one_mem)

/- English proof (translation)
Use `show (((-1, 1), 1) : φ.GG) * ((-1, 1), 1) = 1`. Simplify using the standard rewrite rules.
-/
theorem sg_mul_sg : φ.sg * φ.sg = 1 := by
  show (((-1, 1), 1) : φ.GG) * ((-1, 1), 1) = 1
  simp

/- English proof (translation)
Introduce `h`. Conclude with `int_units_neg_one_ne_one (congrArg (fun g : φ.GG => g.1.1) h)`.
-/
theorem sg_ne_one : φ.sg ≠ 1 := by
  intro h
  exact int_units_neg_one_ne_one (congrArg (fun g : φ.GG => g.1.1) h)

/- English proof (translation)
Introduce `h`. Conclude with `int_units_neg_one_ne_one (congrArg (fun g : φ.GG => g.1.2) h)`.
-/
theorem iod_ne_one : φ.iod ≠ 1 := by
  intro h
  exact int_units_neg_one_ne_one (congrArg (fun g : φ.GG => g.1.2) h)

/- English proof (translation)
Use `show ((c0, 1) : φ.GG) * ((1, -1), 1) = ((-1, 1), 1)`. Simplify using `[c0]`.
-/
theorem cc_mul_iod : φ.cc * φ.iod = φ.sg := by
  show ((c0, 1) : φ.GG) * ((1, -1), 1) = ((-1, 1), 1)
  simp [c0]

/- English proof (translation)
Conclude with `orderOf_eq_prime (by rw [pow_two]; exact φ.cc_mul_cc) φ.cc_ne_one`.
-/
theorem orderOf_cc : orderOf φ.cc = 2 := by
  exact orderOf_eq_prime (by rw [pow_two]; exact φ.cc_mul_cc) φ.cc_ne_one

/- English proof (translation)
Assemble the required witnesses or components as `⟨by rw [natCard_GG_eq_four_mul_ord], φ.index_Psi, φ.cc_notMem_Psi, φ.sg_mem_Psi, φ.orderOf_cc⟩`.
-/
theorem hostGroup : Nat.card φ.GG = 4 * φ.ord ∧ φ.Psi.index = 2 ∧ φ.cc ∉ φ.Psi ∧ φ.sg ∈ φ.Psi ∧
    orderOf φ.cc = 2 := ⟨by rw [natCard_GG_eq_four_mul_ord], φ.index_Psi, φ.cc_notMem_Psi, φ.sg_mem_Psi, φ.orderOf_cc⟩

/- English proof (translation)
Introduce `_ _ h` and use `Multiplicative.ofAdd.injective h`.
-/
theorem iota_injective : Function.Injective φ.iota := fun _ _ h => Multiplicative.ofAdd.injective h

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem iotaInv_mul (a b : φ.MA) : φ.iotaInv (a * b) = φ.iotaInv a + φ.iotaInv b := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem iotaInv_one : φ.iotaInv 1 = 0 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem iotaInv_inv (a : φ.MA) : φ.iotaInv a⁻¹ = -φ.iotaInv a := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem iotaInv_pow (a : φ.MA) (i : ℕ) : φ.iotaInv (a ^ i) = i • φ.iotaInv a := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem iota_neg (t : φ.A) : φ.iota (-t) = (φ.iota t)⁻¹ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem iota_nsmul (i : ℕ) (t : φ.A) : φ.iota (i • t) = φ.iota t ^ i := rfl

/- English proof (translation)
The claim follows from `toAdd_eq_zero`.
-/
theorem iotaInv_eq_zero_iff (a : φ.MA) : φ.iotaInv a = 0 ↔ a = 1 := toAdd_eq_zero

/- English proof (translation)
The claim follows from `orderOf_ofAdd_eq_addOrderOf t`.
-/
theorem orderOf_iota (t : φ.A) : orderOf (φ.iota t) = addOrderOf t := orderOf_ofAdd_eq_addOrderOf t

/- English proof (translation)
The claim follows from `(orderOf_ofAdd_eq_addOrderOf (Multiplicative.toAdd a)).symm`.
-/
theorem addOrderOf_iotaInv (a : φ.MA) : addOrderOf (φ.iotaInv a) = orderOf a := (orderOf_ofAdd_eq_addOrderOf (Multiplicative.toAdd a)).symm

/- English proof (translation)
Introduce `_ _ h` and use `φ.iota_injective (congrArg Prod.snd h)`.
-/
theorem tau1_injective : Function.Injective φ.tau1 := fun _ _ h => φ.iota_injective (congrArg Prod.snd h)

/- English proof (translation)
Introduce `_ _ h` and use `φ.iota_injective (congrArg Prod.snd h)`.
-/
theorem doubling_injective : Function.Injective φ.tau2 := fun _ _ h => φ.iota_injective (congrArg Prod.snd h)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem tau1_mem_Psi (t : φ.A) : φ.tau1 t ∈ φ.Psi := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem doubling_mem_character_set (t : φ.A) : φ.tau2 t ∈ φ.Psi := rfl

/- English proof (translation)
Introduce `h`. Conclude with `int_units_neg_one_ne_one (congrArg (fun g : φ.GG => g.1.1) h).symm`.
-/
theorem ramifiedTau1_ne_ramifiedTau2 (t t' : φ.A) : φ.tau1 t ≠ φ.tau2 t' := by
  intro h
  exact int_units_neg_one_ne_one (congrArg (fun g : φ.GG => g.1.1) h).symm

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hg`. Rewrite `hg` using `[mem_Psi_iff]`. Take `⟨⟨q, d⟩, a⟩` from `g`. Simplify using `only at hg`.

Substitute `hg` using the available equality. Break down `Int.units_eq_one_or q with rfl | rfl` into its components or cases. Conclude with `Or.inl ⟨φ.iotaInv a, rfl⟩`. Conclude with `Or.inr ⟨φ.iotaInv a, rfl⟩`. Introduce and unpack `(⟨t, rfl⟩ | ⟨t, rfl⟩)`.

Conclude with `φ.tau1_mem_Psi t`. Conclude with `φ.doubling_mem_character_set t`.
-/
theorem mem_Psi_iff_tau (g : φ.GG) : g ∈ φ.Psi ↔ (∃ t, g = φ.tau1 t) ∨ (∃ t, g = φ.tau2 t) := by
  constructor
  · intro hg
    rw [mem_Psi_iff] at hg
    obtain ⟨⟨q, d⟩, a⟩ := g
    simp only at hg
    subst hg
    rcases Int.units_eq_one_or q with rfl | rfl
    · exact Or.inl ⟨φ.iotaInv a, rfl⟩
    · exact Or.inr ⟨φ.iotaInv a, rfl⟩
  · rintro (⟨t, rfl⟩ | ⟨t, rfl⟩)
    · exact φ.tau1_mem_Psi t
    · exact φ.doubling_mem_character_set t

/- English proof (translation)
Unfold `Formalism.HC.Frame.placeOf`. Use `split_ifs with h`. Conclude with `(mem_Psi_iff g).2 h`. Rewrite using `[mem_Psi_iff]`. Break down `Int.units_eq_one_or g.1.2 with h' | h'` into its components or cases.

Conclude with `absurd h' h`. Use `show (-1 : ℤˣ) * g.1.2 = 1`. Rewrite using `[h']`. Simplify using the standard rewrite rules.
-/
theorem placeOf_mem_Psi (g : φ.GG) : placeOf g ∈ φ.Psi := by
  unfold Formalism.HC.Frame.placeOf
  split_ifs with h
  · exact (mem_Psi_iff g).2 h
  · rw [mem_Psi_iff]
    rcases Int.units_eq_one_or g.1.2 with h' | h'
    · exact absurd h' h
    · show (-1 : ℤˣ) * g.1.2 = 1
      rw [h']
      simp

/- English proof (translation)
Unfold `Formalism.HC.Frame.placeOf`. Conclude with `if_pos ((mem_Psi_iff g).1 hg)`.
-/
theorem placeOf_of_mem {g : φ.GG} (hg : g ∈ φ.Psi) : placeOf g = g := by
  unfold Formalism.HC.Frame.placeOf
  exact if_pos ((mem_Psi_iff g).1 hg)

/- English proof (translation)
Unfold `Formalism.HC.Frame.placeOf`. Conclude with `if_neg (fun h => hg ((mem_Psi_iff g).2 h))`.
-/
theorem placeOf_of_notMem {g : φ.GG} (hg : g ∉ φ.Psi) : placeOf g = φ.cc * g := by
  unfold Formalism.HC.Frame.placeOf
  exact if_neg (fun h => hg ((mem_Psi_iff g).2 h))

/- English proof (translation)
Unfold `Formalism.HC.Frame.placeOf`. Use `split_ifs`. Both sides reduce to the same expression. Conclude with `one_mul g.2`.
-/
theorem placeOf_snd (g : φ.GG) : (placeOf g).2 = g.2 := by
  unfold Formalism.HC.Frame.placeOf
  split_ifs
  · rfl
  · exact one_mul g.2

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem hH_apply (a : φ.MA) : φ.hH a = (φ.h (φ.iotaInv a)).toMul := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem hH_iota (t : φ.A) : φ.hH (φ.iota t) = (φ.h t).toMul := rfl

/- English proof (translation)
Introduce `y`. Take `⟨t, ht⟩` from `φ.projection_surjective_field (Additive.ofMul y)`. Conclude with `⟨φ.iota t, congrArg Additive.toMul ht⟩`.
-/
theorem hH_surj : Function.Surjective φ.hH := by
  intro y
  obtain ⟨t, ht⟩ := φ.projection_surjective_field (Additive.ofMul y)
  exact ⟨φ.iota t, congrArg Additive.toMul ht⟩

/- English proof (translation)
Rewrite using `[← natCard_A_eq_ord]`. Conclude with `Nat.card_pos`.
-/
private theorem ord_pos' : 0 < φ.ord := by
  rw [← natCard_A_eq_ord]
  exact Nat.card_pos

/- English proof (translation)
Use `Subgroup.card_dvd_of_surjective φ.hH φ.hH_surj` as an intermediate fact. Rewrite `this` using `[Formalism.FrobeniusOrbits.Group.card_H, φ.natCard_MA]`. Then use the resulting hypothesis.
-/
theorem two_pow_dvd_ord : 2 ^ φ.e ∣ φ.ord := by
  have := Subgroup.card_dvd_of_surjective φ.hH φ.hH_surj
  rwa [Formalism.FrobeniusOrbits.Group.card_H, φ.natCard_MA] at this

/- English proof (translation)
The claim follows from `Nat.le_of_dvd (ord_pos' φ) φ.two_pow_dvd_ord`.
-/
theorem two_pow_le_ord : 2 ^ φ.e ≤ φ.ord := Nat.le_of_dvd (ord_pos' φ) φ.two_pow_dvd_ord

/- English proof (translation)
Rewrite using `[← natCard_A_eq_ord]`. Conclude with `addOrderOf_dvd_natCard t`.
-/
theorem addOrderOf_dvd_ord (t : φ.A) : addOrderOf t ∣ φ.ord := by
  rw [← natCard_A_eq_ord]
  exact addOrderOf_dvd_natCard t

/- English proof (translation)
Rewrite using `[← φ.natCard_MA]`. Conclude with `orderOf_dvd_natCard a`.
-/
theorem orderOf_dvd_ord (a : φ.MA) : orderOf a ∣ φ.ord := by
  rw [← φ.natCard_MA]
  exact orderOf_dvd_natCard a

/- English proof (translation)
The claim follows from `addOrderOf_dvd_iff_nsmul_eq_zero.1 (φ.addOrderOf_dvd_ord t)`.
-/
theorem ord_nsmul (t : φ.A) : φ.ord • t = 0 := addOrderOf_dvd_iff_nsmul_eq_zero.1 (φ.addOrderOf_dvd_ord t)

/- English proof (translation)
The claim follows from `addOrderOf_pos φ.a0`.
-/
theorem n0_pos : 0 < φ.n0 := addOrderOf_pos φ.a0

/- English proof (translation)
The claim follows from `φ.addOrderOf_dvd_ord φ.a0`.
-/
theorem cyclic_order_dvd_exponent : φ.n0 ∣ φ.ord := φ.addOrderOf_dvd_ord φ.a0

/- English proof (translation)
The claim follows from `(Nat.div_mul_cancel φ.cyclic_order_dvd_exponent).symm`.
-/
theorem exponent_eq_index_mul_cyclic_order : φ.ord = φ.o * φ.n0 := (Nat.div_mul_cancel φ.cyclic_order_dvd_exponent).symm

/- English proof (translation)
The claim follows from `Nat.div_pos (Nat.le_of_dvd (ord_pos' φ) φ.cyclic_order_dvd_exponent) φ.n0_pos`.
-/
theorem o_pos : 0 < φ.o := Nat.div_pos (Nat.le_of_dvd (ord_pos' φ) φ.cyclic_order_dvd_exponent) φ.n0_pos

/- English proof (translation)
The claim follows from `Nat.card_zmultiples φ.a0`.
-/
theorem natCard_cyclic_subgroup : Nat.card φ.A0 = φ.n0 := Nat.card_zmultiples φ.a0

/- English proof (translation)
Establish `h` using `φ.A0.card_mul_index`. Rewrite `h` using `[φ.natCard_cyclic_subgroup, natCard_A_eq_ord, φ.exponent_eq_index_mul_cyclic_order]`. Conclude with `Nat.eq_of_mul_eq_mul_left φ.n0_pos (h.trans (mul_comm _ _))`.
-/
theorem index_A0_eq_o : φ.A0.index = φ.o := by
  have h := φ.A0.card_mul_index
  rw [φ.natCard_cyclic_subgroup, natCard_A_eq_ord, φ.exponent_eq_index_mul_cyclic_order] at h
  exact Nat.eq_of_mul_eq_mul_left φ.n0_pos (h.trans (mul_comm _ _))

/- English proof (translation)
Take `⟨k, rfl⟩` from `AddSubgroup.mem_zmultiples_iff.1 ht`. Conclude with `φ.zsmul_generator_eq_zero_of_projection k h0`.
-/
theorem eq_zero_of_mem_cyclic_of_projection {t : φ.A} (ht : t ∈ φ.A0) (h0 : φ.h t = 0) : t = 0 := by
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 ht
  exact φ.zsmul_generator_eq_zero_of_projection k h0

/- English proof (translation)
Introduce `x hx y hy hxy`. Conclude with `sub_eq_zero.1 (φ.eq_zero_of_mem_cyclic_of_projection (φ.A0.sub_mem hx hy) (by rw [map_sub, hxy, sub_self]))`.
-/
theorem injOn_projection_cyclic_subgroup : Set.InjOn φ.h φ.A0 := by
  intro x hx y hy hxy
  exact sub_eq_zero.1 (φ.eq_zero_of_mem_cyclic_of_projection (φ.A0.sub_mem hx hy) (by rw [map_sub, hxy, sub_self]))

/- English proof (translation)
The claim follows from `addOrderOf_map_dvd φ.h t`.
-/
theorem addOrderOf_h_dvd (t : φ.A) : addOrderOf (φ.h t) ∣ addOrderOf t := addOrderOf_map_dvd φ.h t

/- English proof (translation)
The claim follows from `orderOf_map_dvd φ.hH a`.
-/
theorem orderOf_hH_dvd (a : φ.MA) : orderOf (φ.hH a) ∣ orderOf a := orderOf_map_dvd φ.hH a

/- English proof (translation)
Rewrite using `[φ.hH_iota]`. Conclude with `(addOrderOf_ofMul_eq_orderOf _).symm`.
-/
theorem orderOf_hH_iota (t : φ.A) : orderOf (φ.hH (φ.iota t)) = addOrderOf (φ.h t) := by
  rw [φ.hH_iota]
  exact (addOrderOf_ofMul_eq_orderOf _).symm

/- English proof (translation)
Apply `Nat.dvd_antisymm (φ.addOrderOf_h_dvd t)` to reduce the goal to its premises. Apply `addOrderOf_dvd_of_nsmul_eq_zero` to reduce the goal to its premises. Apply `φ.eq_zero_of_mem_cyclic_of_projection (φ.A0.nsmul_mem ht _)` to reduce the goal to its premises. Rewrite using `[map_nsmul, addOrderOf_nsmul_eq_zero]`.
-/
theorem addOrderOf_projection_of_mem_cyclic {t : φ.A} (ht : t ∈ φ.A0) : addOrderOf (φ.h t) = addOrderOf t := by
  apply Nat.dvd_antisymm (φ.addOrderOf_h_dvd t)
  apply addOrderOf_dvd_of_nsmul_eq_zero
  apply φ.eq_zero_of_mem_cyclic_of_projection (φ.A0.nsmul_mem ht _)
  rw [map_nsmul, addOrderOf_nsmul_eq_zero]

/- English proof (translation)
Rewrite using `[← Formalism.FrobeniusOrbits.Group.card_H φ.e]`. Conclude with `orderOf_dvd_natCard x`.
-/
theorem orderOf_H_dvd (x : HGrp φ.e) : orderOf x ∣ 2 ^ φ.e := by
  rw [← Formalism.FrobeniusOrbits.Group.card_H φ.e]
  exact orderOf_dvd_natCard x

/- English proof (translation)
Rewrite using `[← φ.orderOf_hH_iota]`. Conclude with `φ.orderOf_H_dvd _`.
-/
theorem addOrderOf_h_dvd_two_pow (t : φ.A) : addOrderOf (φ.h t) ∣ 2 ^ φ.e := by
  rw [← φ.orderOf_hH_iota]
  exact φ.orderOf_H_dvd _

/- English proof (translation)
Use `show addOrderOf φ.a0 ∣ 2 ^ φ.e`. Rewrite using `[← φ.addOrderOf_projection_of_mem_cyclic (AddSubgroup.mem_zmultiples φ.a0)]`. Conclude with `φ.addOrderOf_h_dvd_two_pow _`.
-/
theorem cyclic_order_dvd_two_pow : φ.n0 ∣ 2 ^ φ.e := by
  show addOrderOf φ.a0 ∣ 2 ^ φ.e
  rw [← φ.addOrderOf_projection_of_mem_cyclic (AddSubgroup.mem_zmultiples φ.a0)]
  exact φ.addOrderOf_h_dvd_two_pow _

/- English proof (translation)
The claim follows from `Nat.le_of_dvd (by positivity) φ.cyclic_order_dvd_two_pow`.
-/
theorem cyclic_order_le_two_pow : φ.n0 ≤ 2 ^ φ.e := Nat.le_of_dvd (by positivity) φ.cyclic_order_dvd_two_pow

/- English proof (translation)
The claim follows from `Nat.le_of_dvd (ord_pos' φ) φ.cyclic_order_dvd_exponent`.
-/
theorem cyclic_order_le_exponent : φ.n0 ≤ φ.ord := Nat.le_of_dvd (ord_pos' φ) φ.cyclic_order_dvd_exponent

/- English proof (translation)
Rewrite using `[φ.exponent_eq_index_mul_cyclic_order]`. Conclude with `Nat.mul_le_mul_left _ φ.cyclic_order_le_two_pow`.
-/
theorem ord_le_o_mul_two_pow : φ.ord ≤ φ.o * 2 ^ φ.e := by
  rw [φ.exponent_eq_index_mul_cyclic_order]
  exact Nat.mul_le_mul_left _ φ.cyclic_order_le_two_pow

/- English proof (translation)
The claim follows from `(Nat.dvd_prime_pow Nat.prime_two).1 φ.cyclic_order_dvd_two_pow`.
-/
theorem exists_cyclic_order_eq_two_pow : ∃ j ≤ φ.e, φ.n0 = 2 ^ j := (Nat.dvd_prime_pow Nat.prime_two).1 φ.cyclic_order_dvd_two_pow

/- English proof (translation)
Rewrite using `[← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.mk_nsmul, ← φ.index_A0_eq_o, AddSubgroup.index_eq_card]`. Conclude with `card_nsmul_eq_zero'`.
-/
private theorem o_smul_mem_A0 (t : φ.A) : φ.o • t ∈ φ.A0 := by
  rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.mk_nsmul, ← φ.index_A0_eq_o,
    AddSubgroup.index_eq_card]
  exact card_nsmul_eq_zero'

/- English proof (translation)
Apply `φ.eq_zero_of_mem_cyclic_of_projection (o_smul_mem_A0 φ t)` to reduce the goal to its premises. Rewrite using `[map_nsmul, ht, nsmul_zero]`.
-/
theorem o_nsmul_of_h_eq_zero {t : φ.A} (ht : φ.h t = 0) : φ.o • t = 0 := by
  apply φ.eq_zero_of_mem_cyclic_of_projection (o_smul_mem_A0 φ t)
  rw [map_nsmul, ht, nsmul_zero]

/- English proof (translation)
The claim follows from `o_smul_mem_A0 φ t`.
-/
theorem index_nsmul_mem_cyclic_subgroup (t : φ.A) : φ.o • t ∈ φ.A0 := o_smul_mem_A0 φ t

/- English proof (translation)
Apply `addOrderOf_dvd_of_nsmul_eq_zero` to reduce the goal to its premises. Rewrite using `[← smul_smul]`. Conclude with `φ.o_nsmul_of_h_eq_zero (by rw [map_nsmul, addOrderOf_nsmul_eq_zero])`.
-/
theorem addOrderOf_dvd_o_mul (t : φ.A) : addOrderOf t ∣ φ.o * addOrderOf (φ.h t) := by
  apply addOrderOf_dvd_of_nsmul_eq_zero
  rw [← smul_smul]
  exact φ.o_nsmul_of_h_eq_zero (by rw [map_nsmul, addOrderOf_nsmul_eq_zero])

/- English proof (translation)
The claim follows from `zero_nsmul φ.a0`.
-/
theorem dig_zero : φ.dig 0 = 0 := zero_nsmul φ.a0

/- English proof (translation)
The claim follows from `add_nsmul φ.a0 s s'`.
-/
theorem dig_add (s s' : ℕ) : φ.dig (s + s') = φ.dig s + φ.dig s' := add_nsmul φ.a0 s s'

/- English proof (translation)
The claim follows from `φ.A0.nsmul_mem (AddSubgroup.mem_zmultiples φ.a0) s`.
-/
theorem digit_mem_cyclic_subgroup (s : ℕ) : φ.dig s ∈ φ.A0 := φ.A0.nsmul_mem (AddSubgroup.mem_zmultiples φ.a0) s

/- English proof (translation)
The claim follows from `nsmul_eq_nsmul_iff_modEq`.
-/
theorem dig_eq_dig_iff (s s' : ℕ) : φ.dig s = φ.dig s' ↔ s ≡ s' [MOD φ.n0] := nsmul_eq_nsmul_iff_modEq

/- English proof (translation)
Introduce `s hs s' hs' h`. Establish `h1` using `(φ.dig_eq_dig_iff s s').1 h`. Unfold `Nat.ModEq at h1`. Rewrite `h1` using `[Nat.mod_eq_of_lt (Set.mem_Iio.1 hs), Nat.mod_eq_of_lt (Set.mem_Iio.1 hs')]`. Then use the resulting hypothesis.
-/
theorem dig_injOn : Set.InjOn φ.dig (Set.Iio φ.n0) := by
  intro s hs s' hs' h
  have h1 := (φ.dig_eq_dig_iff s s').1 h
  unfold Nat.ModEq at h1
  rwa [Nat.mod_eq_of_lt (Set.mem_Iio.1 hs), Nat.mod_eq_of_lt (Set.mem_Iio.1 hs')] at h1

/- English proof (translation)
The claim follows from `φ.dig_injOn (Set.mem_Iio.2 hs) (Set.mem_Iio.2 hs') h`.
-/
theorem dig_inj {s s' : ℕ} (hs : s < φ.n0) (hs' : s' < φ.n0) (h : φ.dig s = φ.dig s') : s = s' := φ.dig_injOn (Set.mem_Iio.2 hs) (Set.mem_Iio.2 hs') h

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `ht`. Take `⟨k, rfl⟩` from `AddSubgroup.mem_zmultiples_iff.1 ht`. Establish `hn : (0 : ℤ) < φ.n0` using `by exact_mod_cast φ.n0_pos`. Take `⟨r, hr⟩ : ∃ r : ℕ, (r : ℤ) = k % φ.n0` from `⟨(k % φ.n0).toNat, Int.toNat_of_nonneg (Int.emod_nonneg _ hn.ne')⟩`.

Use `⟨r, ?_, ?_⟩` and prove the remaining obligations. Establish `h1` using `Int.emod_lt_of_pos k hn`. Rewrite `h1` using `[← hr]`. Conclude with `h1` after adjusting the coercions. Use `show k • φ.a0 = r • φ.a0`.

Rewrite using `[← natCast_zsmul, hr]`. Conclude with `(mod_addOrderOf_zsmul φ.a0 k).symm`. Introduce and unpack `⟨s, -, rfl⟩`. Conclude with `φ.digit_mem_cyclic_subgroup s`.
-/
theorem mem_cusp_forms_iff_automorphic_compact (t : φ.A) : t ∈ φ.A0 ↔ ∃ s < φ.n0, t = φ.dig s := by
  constructor
  · intro ht
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 ht
    have hn : (0 : ℤ) < φ.n0 := by exact_mod_cast φ.n0_pos
    obtain ⟨r, hr⟩ : ∃ r : ℕ, (r : ℤ) = k % φ.n0 :=
      ⟨(k % φ.n0).toNat, Int.toNat_of_nonneg (Int.emod_nonneg _ hn.ne')⟩
    refine ⟨r, ?_, ?_⟩
    · have h1 := Int.emod_lt_of_pos k hn
      rw [← hr] at h1
      exact_mod_cast h1
    · show k • φ.a0 = r • φ.a0
      rw [← natCast_zsmul, hr]
      exact (mod_addOrderOf_zsmul φ.a0 k).symm
  · rintro ⟨s, -, rfl⟩
    exact φ.digit_mem_cyclic_subgroup s

/- English proof (translation)
The claim follows from `addOrderOf_dvd_iff_zsmul_eq_zero.symm`.
-/
theorem zsmul_generator_eq_zero_iff (k : ℤ) : k • φ.a0 = 0 ↔ (φ.n0 : ℤ) ∣ k := addOrderOf_dvd_iff_zsmul_eq_zero.symm

/- English proof (translation)
The claim follows from `Prod.ext (by rw [Prod.pow_fst]; exact Int.units_sq _) (by rw [Prod.pow_snd]; exact Int.units_sq _)`.
-/
theorem fst_sq (g : φ.GG) : g.1 ^ 2 = 1 := Prod.ext (by rw [Prod.pow_fst]; exact Int.units_sq _) (by rw [Prod.pow_snd]; exact Int.units_sq _)

/- English proof (translation)
The claim follows from `Prod.ext (by rw [Prod.pow_fst]; exact Int.units_sq _) (by rw [Prod.pow_snd]; exact Int.units_sq _)`.
-/
private theorem sign_group_sq_eq_one_var (x : G0) : x ^ 2 = 1 :=
  Prod.ext (by rw [Prod.pow_fst]; exact Int.units_sq _) (by rw [Prod.pow_snd]; exact Int.units_sq _)

/- English proof (translation)
Break down `Nat.even_or_odd i with ⟨k, rfl⟩ | ⟨k, rfl⟩` into its components or cases. Rewrite using `[if_pos ⟨k, rfl⟩, ← two_mul, pow_mul, sign_group_sq_eq_one_var, one_pow]`. Rewrite using `[if_neg (Nat.not_even_iff_odd.2 ⟨k, rfl⟩), pow_succ, pow_mul, sign_group_sq_eq_one_var, one_pow, one_mul]`.
-/
private theorem G0_pow_eq_ite_even (x : G0) (i : ℕ) : x ^ i = if Even i then 1 else x := by
  rcases Nat.even_or_odd i with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [if_pos ⟨k, rfl⟩, ← two_mul, pow_mul, sign_group_sq_eq_one_var, one_pow]
  · rw [if_neg (Nat.not_even_iff_odd.2 ⟨k, rfl⟩), pow_succ, pow_mul, sign_group_sq_eq_one_var, one_pow, one_mul]

/- English proof (translation)
Establish `h2 : x ^ (2 : ℤ) = 1` using `by rw [zpow_two, ← pow_two, sign_group_sq_eq_one_var]`. Break down `Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩` into its components or cases. Rewrite using `[if_pos ⟨m, rfl⟩, ← two_mul, zpow_mul, h2, one_zpow]`. Rewrite using `[if_neg (Int.not_even_iff_odd.2 ⟨m, rfl⟩), zpow_add_one, zpow_mul, h2, one_zpow, one_mul]`.
-/
private theorem G0_zpow_eq_ite_even (x : G0) (k : ℤ) : x ^ k = if Even k then 1 else x := by
  have h2 : x ^ (2 : ℤ) = 1 := by rw [zpow_two, ← pow_two, sign_group_sq_eq_one_var]
  rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · rw [if_pos ⟨m, rfl⟩, ← two_mul, zpow_mul, h2, one_zpow]
  · rw [if_neg (Int.not_even_iff_odd.2 ⟨m, rfl⟩), zpow_add_one, zpow_mul, h2, one_zpow, one_mul]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨k, hk⟩` from `Subgroup.mem_zpowers_iff.1 h`. Establish `h1 : g.1 ^ k = c0` using `congrArg Prod.fst hk`. Establish `h2 : g.2 ^ k = 1` using `congrArg Prod.snd hk`.

Rewrite `h1` using `[G0_zpow_eq_ite_even]`. Use `split_ifs at h1 with hk2`. Conclude with `(int_units_neg_one_ne_one (congrArg Prod.fst h1).symm).elim`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Establish `hd` using `orderOf_dvd_iff_zpow_eq_one.2 h2`.

Break down `Nat.even_or_odd (orderOf g.2) with he | ho` into its components or cases. Establish `h2d : (2 : ℤ) ∣ (orderOf g.2 : ℤ)` using `by exact_mod_cast even_iff_two_dvd.1 he`. Conclude with `absurd (even_iff_two_dvd.2 (dvd_trans h2d hd)) hk2`. Conclude with `ho`. Introduce and unpack `⟨hc, ho⟩`.

Use `Subgroup.mem_zpowers_iff.2 ⟨(orderOf g.2 : ℤ), ?_⟩` and prove the remaining obligations. Rewrite using `[zpow_natCast]`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use `show g.1 ^ orderOf g.2 = c0`. Rewrite using `[hc, G0_pow_eq_ite_even, if_neg (Nat.not_even_iff_odd.2 ho)]`.

Use `show g.2 ^ orderOf g.2 = 1`. Conclude with `pow_orderOf_eq_one g.2`.
-/
theorem cc_mem_zpowers_iff (g : φ.GG) : φ.cc ∈ Subgroup.zpowers g ↔ g.1 = c0 ∧ Odd (orderOf g.2) := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
    have h1 : g.1 ^ k = c0 := congrArg Prod.fst hk
    have h2 : g.2 ^ k = 1 := congrArg Prod.snd hk
    rw [G0_zpow_eq_ite_even] at h1
    split_ifs at h1 with hk2
    · exact (int_units_neg_one_ne_one (congrArg Prod.fst h1).symm).elim
    · refine ⟨h1, ?_⟩
      have hd := orderOf_dvd_iff_zpow_eq_one.2 h2
      rcases Nat.even_or_odd (orderOf g.2) with he | ho
      · have h2d : (2 : ℤ) ∣ (orderOf g.2 : ℤ) := by exact_mod_cast even_iff_two_dvd.1 he
        exact absurd (even_iff_two_dvd.2 (dvd_trans h2d hd)) hk2
      · exact ho
  · rintro ⟨hc, ho⟩
    refine Subgroup.mem_zpowers_iff.2 ⟨(orderOf g.2 : ℤ), ?_⟩
    rw [zpow_natCast]
    refine Prod.ext ?_ ?_
    · show g.1 ^ orderOf g.2 = c0
      rw [hc, G0_pow_eq_ite_even, if_neg (Nat.not_even_iff_odd.2 ho)]
    · show g.2 ^ orderOf g.2 = 1
      exact pow_orderOf_eq_one g.2

variable {φ} in
/- English proof (translation)
Take `⟨j, hj⟩` from `h2`. Establish `hd : orderOf a ∣ 2 ^ j`. Rewrite using `[← hj]`. Conclude with `φ.orderOf_dvd_ord a`. Take `⟨i, -, hi⟩` from `(Nat.dvd_prime_pow Nat.prime_two).1 hd`.

Conclude with `⟨i, hi⟩`.
-/
theorem TwoGroup.orderOf_eq (h2 : φ.TwoGroup) (a : φ.MA) : ∃ i : ℕ, orderOf a = 2 ^ i := by
  obtain ⟨j, hj⟩ := h2
  have hd : orderOf a ∣ 2 ^ j := by
    rw [← hj]
    exact φ.orderOf_dvd_ord a
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
  exact ⟨i, hi⟩

variable {φ} in
/- English proof (translation)
Take `⟨j, hj⟩` from `h2`. Establish `hd : addOrderOf t ∣ 2 ^ j`. Rewrite using `[← hj]`. Conclude with `φ.addOrderOf_dvd_ord t`. Take `⟨i, -, hi⟩` from `(Nat.dvd_prime_pow Nat.prime_two).1 hd`.

Conclude with `⟨i, hi⟩`.
-/
theorem TwoGroup.addOrderOf_eq (h2 : φ.TwoGroup) (t : φ.A) : ∃ i : ℕ, addOrderOf t = 2 ^ i := by
  obtain ⟨j, hj⟩ := h2
  have hd : addOrderOf t ∣ 2 ^ j := by
    rw [← hj]
    exact φ.addOrderOf_dvd_ord t
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
  exact ⟨i, hi⟩

variable {φ} in
/- English proof (translation)
Take `⟨i, hi⟩` from `h2.orderOf_eq a`. Rewrite using `[hi]`. Use `Nat.even_pow.2 ⟨even_two, ?_⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Conclude with `ha (orderOf_eq_one_iff.1 (by rw [hi, pow_zero]))`.
-/
theorem TwoGroup.even_orderOf (h2 : φ.TwoGroup) {a : φ.MA} (ha : a ≠ 1) : Even (orderOf a) := by
  obtain ⟨i, hi⟩ := h2.orderOf_eq a
  rw [hi]
  refine Nat.even_pow.2 ⟨even_two, ?_⟩
  rintro rfl
  exact ha (orderOf_eq_one_iff.1 (by rw [hi, pow_zero]))

variable {φ} in
/- English proof (translation)
Take `⟨i, hi⟩` from `h2.orderOf_eq a`. Rewrite using `[← orderOf_dvd_iff_pow_eq_one, hi, Nat.pow_dvd_pow_iff_le_right (by norm_num), Nat.pow_le_pow_iff_right (by norm_num)]`.
-/
theorem TwoGroup.orderOf_le_iff (h2 : φ.TwoGroup) (a : φ.MA) (j : ℕ) : orderOf a ≤ 2 ^ j ↔ a ^ (2 ^ j) = 1 := by
  obtain ⟨i, hi⟩ := h2.orderOf_eq a
  rw [← orderOf_dvd_iff_pow_eq_one, hi, Nat.pow_dvd_pow_iff_le_right (by norm_num),
    Nat.pow_le_pow_iff_right (by norm_num)]

variable {φ} in
/- English proof (translation)
Take `⟨j, hj⟩` from `h2`. Establish `hd : orderOf g ∣ 2 ^ (j + 2)`. Use `orderOf_dvd_natCard g using 1` and compare the differences between its conclusion and the goal. Rewrite using `[natCard_GG_eq_four_mul_ord, hj]`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨i, -, hi⟩` from `(Nat.dvd_prime_pow Nat.prime_two).1 hd`. Conclude with `⟨i, hi⟩`.
-/
theorem TwoGroup.orderOf_GG (h2 : φ.TwoGroup) (g : φ.GG) : ∃ i : ℕ, orderOf g = 2 ^ i := by
  obtain ⟨j, hj⟩ := h2
  have hd : orderOf g ∣ 2 ^ (j + 2) := by
    convert orderOf_dvd_natCard g using 1
    rw [natCard_GG_eq_four_mul_ord, hj]
    ring
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
  exact ⟨i, hi⟩

variable {φ} in

/- English proof (translation)
Rewrite using `[φ.cc_mem_zpowers_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hc, ho⟩`. Take `⟨i, hi⟩` from `h2.orderOf_eq g.2`. Establish `h1 : orderOf g.2 = 1`.

Rewrite `ho`, the goal using `[hi]`. Break down `i with _ | i` into its components or cases. Both sides reduce to the same expression. Conclude with `absurd ho (Nat.not_odd_iff_even.2 (Nat.even_pow.2 ⟨even_two, Nat.succ_ne_zero _⟩))`. Conclude with `Prod.ext hc (orderOf_eq_one_iff.1 h1)`.

Introduce and unpack `rfl`. Conclude with `⟨rfl, by show Odd (orderOf (1 : φ.MA)); rw [orderOf_one]; exact odd_one⟩`.
-/
theorem TwoGroup.cc_mem_zpowers_iff (h2 : φ.TwoGroup) (g : φ.GG) : φ.cc ∈ Subgroup.zpowers g ↔ g = φ.cc := by
  rw [φ.cc_mem_zpowers_iff]
  constructor
  · rintro ⟨hc, ho⟩
    obtain ⟨i, hi⟩ := h2.orderOf_eq g.2
    have h1 : orderOf g.2 = 1 := by
      rw [hi] at ho ⊢
      rcases i with _ | i
      · rfl
      · exact absurd ho (Nat.not_odd_iff_even.2 (Nat.even_pow.2 ⟨even_two, Nat.succ_ne_zero _⟩))
    exact Prod.ext hc (orderOf_eq_one_iff.1 h1)
  · rintro rfl
    exact ⟨rfl, by show Odd (orderOf (1 : φ.MA)); rw [orderOf_one]; exact odd_one⟩

/- English proof (translation)
Establish `h1` using `φ.orderOf_hH_dvd a`. Take `⟨i, -, hi⟩` from `(Nat.dvd_prime_pow Nat.prime_two).1 (φ.orderOf_H_dvd (φ.hH a))`. Break down `i with _ | i` into its components or cases. Conclude with `absurd (orderOf_eq_one_iff.1 (by simpa using hi)) ha`. Conclude with `even_iff_two_dvd.2 (dvd_trans (by rw [hi, pow_succ]; exact dvd_mul_left 2 _) h1)`.
-/
theorem even_orderOf_of_hH_ne_one {a : φ.MA} (ha : φ.hH a ≠ 1) : Even (orderOf a) := by
  have h1 := φ.orderOf_hH_dvd a
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (φ.orderOf_H_dvd (φ.hH a))
  rcases i with _ | i
  · exact absurd (orderOf_eq_one_iff.1 (by simpa using hi)) ha
  · exact even_iff_two_dvd.2 (dvd_trans (by rw [hi, pow_succ]; exact dvd_mul_left 2 _) h1)

/- English proof (translation)
Establish `h1 : orderOf (φ.hH a) ≤ 2 ^ j` using `le_trans (Nat.le_of_dvd (orderOf_pos a) (φ.orderOf_hH_dvd a)) hj`. Rewrite `h1` using `[ha]`. Conclude with `((Formalism.FrobeniusOrbits.hostOrders φ.e).1 j l u hu).1 h1`.
-/
theorem hostOrders_of_le (a : φ.MA) (j : ℕ) (l : ℤ) (u : (ZMod (2 ^ (φ.e + 2)))ˣ)
    (hu : (u : ZMod (2 ^ (φ.e + 2))) = (l : ZMod _)) (ha : φ.hH a = hcl φ.e u) (hj : orderOf a ≤ 2 ^ j) :
    (l : ZMod (2 ^ (φ.e + 2 - j))) = 1 ∨ (l : ZMod (2 ^ (φ.e + 2 - j))) = -1 := by
  have h1 : orderOf (φ.hH a) ≤ 2 ^ j :=
    le_trans (Nat.le_of_dvd (orderOf_pos a) (φ.orderOf_hH_dvd a)) hj
  rw [ha] at h1
  exact ((Formalism.FrobeniusOrbits.hostOrders φ.e).1 j l u hu).1 h1

/- English proof (translation)
Rewrite using `[ha]`. Conclude with `(Formalism.FrobeniusOrbits.hostOrders φ.e).1 j l u hu`.
-/
theorem hostOrders_hH (a : φ.MA) (j : ℕ) (l : ℤ) (u : (ZMod (2 ^ (φ.e + 2)))ˣ)
    (hu : (u : ZMod (2 ^ (φ.e + 2))) = (l : ZMod _)) (ha : φ.hH a = hcl φ.e u) :
    orderOf (φ.hH a) ≤ 2 ^ j ↔
      ((l : ZMod (2 ^ (φ.e + 2 - j))) = 1 ∨ (l : ZMod (2 ^ (φ.e + 2 - j))) = -1) := by
  rw [ha]
  exact (Formalism.FrobeniusOrbits.hostOrders φ.e).1 j l u hu

/- English proof (translation)
Establish `h1 : orderOf g.1 ∣ 2` using `orderOf_dvd_of_pow_eq_one (φ.fst_sq g)`. Establish `hp : orderOf g = Nat.lcm (orderOf g.1) (orderOf g.2)` using `Prod.orderOf g`. Establish `hA : orderOf g.2 ∣ orderOf g` using `by rw [hp]; exact Nat.dvd_lcm_right _ _`. Use `⟨hA, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hp]`.

Conclude with `Nat.lcm_dvd (dvd_trans h1 (dvd_mul_right 2 _)) (dvd_mul_left _ 2)`. Introduce `j l u hu ha hj`. Conclude with `φ.hostOrders_of_le g.2 j l u hu ha (le_trans (Nat.le_of_dvd (orderOf_pos g) hA) hj)`.
-/
theorem hostOrdersFrob (g : φ.GG) :
    orderOf g.2 ∣ orderOf g ∧ orderOf g ∣ 2 * orderOf g.2 ∧
    ∀ (j : ℕ) (l : ℤ) (u : (ZMod (2 ^ (φ.e + 2)))ˣ), ((u : ZMod (2 ^ (φ.e + 2))) = (l : ZMod _)) →
      φ.hH g.2 = hcl φ.e u → orderOf g ≤ 2 ^ j →
      ((l : ZMod (2 ^ (φ.e + 2 - j))) = 1 ∨ (l : ZMod (2 ^ (φ.e + 2 - j))) = -1) := by
  have h1 : orderOf g.1 ∣ 2 := orderOf_dvd_of_pow_eq_one (φ.fst_sq g)
  have hp : orderOf g = Nat.lcm (orderOf g.1) (orderOf g.2) := Prod.orderOf g
  have hA : orderOf g.2 ∣ orderOf g := by rw [hp]; exact Nat.dvd_lcm_right _ _
  refine ⟨hA, ?_, ?_⟩
  · rw [hp]
    exact Nat.lcm_dvd (dvd_trans h1 (dvd_mul_right 2 _)) (dvd_mul_left _ 2)
  · intro j l u hu ha hj
    exact φ.hostOrders_of_le g.2 j l u hu ha (le_trans (Nat.le_of_dvd (orderOf_pos g) hA) hj)

/- English proof (translation)
Rewrite using `[mem_Psi_iff, mem_Psi_iff]`. Use `show (-1 : ℤˣ) * g.1.2 = 1 ↔ ¬ g.1.2 = 1`. Apply the tactic sequence `rcases Int.units_eq_one_or g.1.2 with h | h <;> rw [h] <;> simp [int_units_neg_one_ne_one]`.
-/
private theorem cc_mul_mem_Psi_iff_not_mem (g : φ.GG) : φ.cc * g ∈ φ.Psi ↔ g ∉ φ.Psi := by
  rw [mem_Psi_iff, mem_Psi_iff]
  show (-1 : ℤˣ) * g.1.2 = 1 ↔ ¬ g.1.2 = 1
  rcases Int.units_eq_one_or g.1.2 with h | h <;> rw [h] <;> simp [int_units_neg_one_ne_one]

/- English proof (translation)
Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `g hg`. Conclude with `φ.Psi.mul_mem ((cc_mul_mem_Psi_iff_not_mem φ g).2 hg) hτ`. Introduce `g _ g' _ h`. Conclude with `mul_left_cancel (mul_right_cancel h)`.

Introduce `y hy`. Use `⟨φ.cc * y * τ⁻¹, ?_, ?_⟩` and prove the remaining obligations. Use `show φ.cc * y * τ⁻¹ ∉ φ.Psi`. Introduce `hm`. Establish `: φ.cc * y ∈ φ.Psi` using `by simpa using φ.Psi.mul_mem hm hτ`.

Conclude with `(cc_mul_mem_Psi_iff_not_mem φ y).1 this hy`. Use `show φ.cc * (φ.cc * y * τ⁻¹) * τ = y`. Rewrite using `[← mul_assoc, ← mul_assoc, φ.cc_mul_cc, one_mul, inv_mul_cancel_right]`.
-/
theorem hostPartner (τ : φ.GG) (hτ : τ ∈ φ.Psi) :
    Set.BijOn (fun g : φ.GG => φ.cc * g * τ) {g | g ∉ φ.Psi} (φ.Psi : Set φ.GG) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    exact φ.Psi.mul_mem ((cc_mul_mem_Psi_iff_not_mem φ g).2 hg) hτ
  · intro g _ g' _ h
    exact mul_left_cancel (mul_right_cancel h)
  · intro y hy
    refine ⟨φ.cc * y * τ⁻¹, ?_, ?_⟩
    · show φ.cc * y * τ⁻¹ ∉ φ.Psi
      intro hm
      have : φ.cc * y ∈ φ.Psi := by simpa using φ.Psi.mul_mem hm hτ
      exact (cc_mul_mem_Psi_iff_not_mem φ y).1 this hy
    · show φ.cc * (φ.cc * y * τ⁻¹) * τ = y
      rw [← mul_assoc, ← mul_assoc, φ.cc_mul_cc, one_mul, inv_mul_cancel_right]

def twHom (χ : φ.GG →* ℂˣ) : φ.GG →* ℂ :=
  (Units.coeHom ℂ).comp φ.chC * Misc2.conjHom χ

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use extensionality with `g`. Establish `hg : ((φ.chC g : ℂˣ) : ℂ) * starRingEnd ℂ ((χ g : ℂˣ) : ℂ) = 1` using `congrArg (fun f : φ.GG →* ℂ => f g) h`. Establish `hc : ((φ.chC g : ℂˣ) : ℂ) * ((φ.chC g : ℂˣ) : ℂ) = 1`.

Rewrite using `[φ.chC_apply]`. Apply the tactic sequence `rcases Int.units_eq_one_or g.1.2 with h1 | h1 <;> rw [h1] <;> norm_num`. Establish `hr : starRingEnd ℂ ((φ.chC g : ℂˣ) : ℂ) = ((φ.chC g : ℂˣ) : ℂ)`. Rewrite using `[φ.chC_apply]`. Conclude with `map_intCast _ _`.

Establish `h2 : starRingEnd ℂ ((χ g : ℂˣ) : ℂ) = ((φ.chC g : ℂˣ) : ℂ)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hc, one_mul]`. Use `_ = ((φ.chC g : ℂˣ) : ℂ) := by rw [mul_assoc, hg, mul_one]`. Establish `h3` using `congrArg (starRingEnd ℂ) h2`.

Rewrite `h3` using `[Complex.conj_conj, hr]`. Use `first`. Consider the case `exact h3`. Consider the case `exact Units.ext h3`. Introduce and unpack `rfl`.

Use extensionality with `g`. Use `show ((φ.chC g : ℂˣ) : ℂ) * starRingEnd ℂ ((φ.chC g : ℂˣ) : ℂ) = 1`. Rewrite using `[φ.chC_apply]`. Apply the tactic sequence `rcases Int.units_eq_one_or g.1.2 with h1 | h1 <;> rw [h1] <;> norm_num`.
-/
theorem twHom_eq_one_iff (χ : φ.GG →* ℂˣ) : φ.twHom χ = 1 ↔ χ = φ.chC := by
  constructor
  · intro h
    ext g
    have hg : ((φ.chC g : ℂˣ) : ℂ) * starRingEnd ℂ ((χ g : ℂˣ) : ℂ) = 1 :=
      congrArg (fun f : φ.GG →* ℂ => f g) h
    have hc : ((φ.chC g : ℂˣ) : ℂ) * ((φ.chC g : ℂˣ) : ℂ) = 1 := by
      rw [φ.chC_apply]
      rcases Int.units_eq_one_or g.1.2 with h1 | h1 <;> rw [h1] <;> norm_num
    have hr : starRingEnd ℂ ((φ.chC g : ℂˣ) : ℂ) = ((φ.chC g : ℂˣ) : ℂ) := by
      rw [φ.chC_apply]
      exact map_intCast _ _
    have h2 : starRingEnd ℂ ((χ g : ℂˣ) : ℂ) = ((φ.chC g : ℂˣ) : ℂ) := by
      calc _ = ((φ.chC g : ℂˣ) : ℂ) * ((φ.chC g : ℂˣ) : ℂ) * starRingEnd ℂ ((χ g : ℂˣ) : ℂ) := by
            rw [hc, one_mul]
        _ = ((φ.chC g : ℂˣ) : ℂ) := by rw [mul_assoc, hg, mul_one]
    have h3 := congrArg (starRingEnd ℂ) h2
    rw [Complex.conj_conj, hr] at h3
    first
    | exact h3
    | exact Units.ext h3
  · rintro rfl
    ext g
    show ((φ.chC g : ℂˣ) : ℂ) * starRingEnd ℂ ((φ.chC g : ℂˣ) : ℂ) = 1
    rw [φ.chC_apply]
    rcases Int.units_eq_one_or g.1.2 with h1 | h1 <;> rw [h1] <;> norm_num

/- English proof (translation)
Introduce `h`. Establish `h1 : ((φ.chC φ.iod : ℂˣ) : ℂ) = 1` using `by simp [h]`. Rewrite `h1` using `[φ.chC_apply]`. Evaluate the numerical expressions using `[iod] at h1`.
-/
theorem chC_ne_one : φ.chC ≠ 1 := by
  intro h
  have h1 : ((φ.chC φ.iod : ℂˣ) : ℂ) = 1 := by simp [h]
  rw [φ.chC_apply] at h1
  norm_num [iod] at h1

open Classical in

/- English proof (translation)
Use `⟨fun χ => ?_, fun g => ?_⟩` and prove the remaining obligations. Set `f : φ.GG →* ℂ` to `Formalism.FrobeniusOrbits.Misc2.conjHom χ`. Establish `hfg : ∀ g, f g = starRingEnd ℂ ((χ g : ℂˣ) : ℂ)` using `fun g => rfl`. Establish `hT1 : (∑ g ∈ Finset.univ.filter (fun g : φ.GG => g ∈ φ.Psi), f g) + (∑ g ∈ Finset.univ.filter (fun g : φ.GG => g ∉ φ.Psi), f g) = ∑ g, f g` using `Finset.sum_filter_add_sum_filter_not _ _ _`. Establish `hT2 : (∑ g ∈ Finset.univ.filter (fun g : φ.GG => g ∈ φ.Psi), f g) - (∑ g ∈ Finset.univ.filter (fun g : φ.GG => g ∉ φ.Psi), f g) = ∑ g, φ.twHom χ g`.

Rewrite using `[← Finset.sum_filter_add_sum_filter_not Finset.univ (fun g : φ.GG => g ∈ φ.Psi) (φ.twHom χ), sub_eq_add_neg, ← Finset.sum_neg_distrib]`. Use `congr 1`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `g hg`. Rewrite `hg` using `[Finset.mem_filter]`.

Use `show f g = ((φ.chC g : ℂˣ) : ℂ) * f g`. Rewrite using `[φ.chC_apply, (mem_Psi_iff g).1 hg.2]`. Simplify using the standard rewrite rules. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `g hg`.

Rewrite `hg` using `[Finset.mem_filter]`. Use `show -f g = ((φ.chC g : ℂˣ) : ℂ) * f g`. Rewrite using `[φ.chC_apply, (Int.units_eq_one_or _).resolve_left (fun h => hg.2 ((mem_Psi_iff g).2 h))]`. Simplify using the standard rewrite rules. Establish `hf1 : f = 1 ↔ χ = 1`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Use extensionality with `g`. Establish `h1 : starRingEnd ℂ ((χ g : ℂˣ) : ℂ) = 1` using `by rw [← hfg, h, MonoidHom.one_apply]`. Establish `h2` using `congrArg (starRingEnd ℂ) h1`.

Rewrite `h2` using `[Complex.conj_conj, map_one]`. Use `first`. Consider the case `exact h2`. Consider the case `exact Units.ext h2`. Introduce `h`.

Use extensionality with `g`. Rewrite using `[hfg, h]`. Simplify using the standard rewrite rules. Establish `hS1 : (∑ g, f g) = if χ = 1 then (4 * φ.ord : ℂ) else 0`. Rewrite using `[sum_hom_units]`.

Distinguish the cases in `h : χ = 1`. Rewrite using `[if_pos (hf1.2 h), if_pos h, φ.card_GG]`. Evaluate the numerical expressions. Rewrite using `[if_neg (fun h' => h (hf1.1 h')), if_neg h, Nat.cast_zero]`. Establish `hS2 : (∑ g, φ.twHom χ g) = if χ = φ.chC then (4 * φ.ord : ℂ) else 0`.

Rewrite using `[sum_hom_units]`. Distinguish the cases in `h : χ = φ.chC`. Rewrite using `[if_pos ((φ.twHom_eq_one_iff χ).2 h), if_pos h, φ.card_GG]`. Evaluate the numerical expressions. Rewrite using `[if_neg (fun h' => h ((φ.twHom_eq_one_iff χ).1 h')), if_neg h, Nat.cast_zero]`.

Use `show (∑ g ∈ Finset.univ.filter (fun g : φ.GG => g ∉ φ.Psi), f g) = _`. Rewrite `hT1` using `[hS1]`. Rewrite `hT2` using `[hS2]`. Distinguish the cases in `h1 : χ = 1`. Establish `h2 : χ ≠ φ.chC` using `fun h => φ.chC_ne_one (h.symm.trans h1)`.

Rewrite `hT1`, the goal using `[if_pos h1]`. Rewrite `hT2` using `[if_neg h2]`. Take the linear combination `(hT1 - hT2) / 2`. Rewrite `hT1`, the goal using `[if_neg h1]`. Distinguish the cases in `h2 : χ = φ.chC`.

Rewrite `hT2`, the goal using `[if_pos h2]`. Take the linear combination `(hT1 - hT2) / 2`. Rewrite `hT2`, the goal using `[if_neg h2]`. Take the linear combination `(hT1 - hT2) / 2`. Take `⟨⟨q, d⟩, a⟩` from `g show 4 * (if ((q, d) : G0) = ((1 : ℤˣ), (-1 : ℤˣ)) then (1 : ℤ) else 0) = (1 - ((d : ℤˣ) : ℤ)) * (1 + ((q : ℤˣ) : ℤ))`.

Apply the tactic sequence `rcases Int.units_eq_one_or q with rfl | rfl <;> rcases Int.units_eq_one_or d with rfl | rfl <;>`. Evaluate the numerical expressions using `[int_units_neg_one_ne_one, int_units_neg_one_ne_one.symm]`.
-/
theorem hostCharSum :
    (∀ χ : φ.GG →* ℂˣ,
      (∑ g ∈ Finset.univ.filter (fun g : φ.GG => g ∉ φ.Psi), starRingEnd ℂ ((χ g : ℂˣ) : ℂ)) =
        if χ = 1 then (2 * φ.ord : ℂ) else if χ = φ.chC then -(2 * φ.ord : ℂ) else 0) ∧
    ∀ g : φ.GG,
      4 * (if g.1 = ((1 : ℤˣ), (-1 : ℤˣ)) then (1 : ℤ) else 0) =
        (1 - ((φ.chD g : ℤˣ) : ℤ)) * (1 + ((φ.chQ g : ℤˣ) : ℤ)) := by
  refine ⟨fun χ => ?_, fun g => ?_⟩
  · let f : φ.GG →* ℂ := Formalism.FrobeniusOrbits.Misc2.conjHom χ
    have hfg : ∀ g, f g = starRingEnd ℂ ((χ g : ℂˣ) : ℂ) := fun g => rfl
    have hT1 : (∑ g ∈ Finset.univ.filter (fun g : φ.GG => g ∈ φ.Psi), f g) +
        (∑ g ∈ Finset.univ.filter (fun g : φ.GG => g ∉ φ.Psi), f g) = ∑ g, f g :=
      Finset.sum_filter_add_sum_filter_not _ _ _
    have hT2 : (∑ g ∈ Finset.univ.filter (fun g : φ.GG => g ∈ φ.Psi), f g) -
        (∑ g ∈ Finset.univ.filter (fun g : φ.GG => g ∉ φ.Psi), f g) = ∑ g, φ.twHom χ g := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun g : φ.GG => g ∈ φ.Psi)
        (φ.twHom χ), sub_eq_add_neg, ← Finset.sum_neg_distrib]
      congr 1
      · apply Finset.sum_congr rfl
        intro g hg
        rw [Finset.mem_filter] at hg
        show f g = ((φ.chC g : ℂˣ) : ℂ) * f g
        rw [φ.chC_apply, (mem_Psi_iff g).1 hg.2]
        simp
      · apply Finset.sum_congr rfl
        intro g hg
        rw [Finset.mem_filter] at hg
        show -f g = ((φ.chC g : ℂˣ) : ℂ) * f g
        rw [φ.chC_apply, (Int.units_eq_one_or _).resolve_left (fun h => hg.2 ((mem_Psi_iff g).2 h))]
        simp
    have hf1 : f = 1 ↔ χ = 1 := by
      constructor
      · intro h
        ext g
        have h1 : starRingEnd ℂ ((χ g : ℂˣ) : ℂ) = 1 := by rw [← hfg, h, MonoidHom.one_apply]
        have h2 := congrArg (starRingEnd ℂ) h1
        rw [Complex.conj_conj, map_one] at h2
        first
        | exact h2
        | exact Units.ext h2
      · intro h
        ext g
        rw [hfg, h]
        simp
    have hS1 : (∑ g, f g) = if χ = 1 then (4 * φ.ord : ℂ) else 0 := by
      rw [sum_hom_units]
      by_cases h : χ = 1
      · rw [if_pos (hf1.2 h), if_pos h, φ.card_GG]
        norm_num
      · rw [if_neg (fun h' => h (hf1.1 h')), if_neg h, Nat.cast_zero]
    have hS2 : (∑ g, φ.twHom χ g) = if χ = φ.chC then (4 * φ.ord : ℂ) else 0 := by
      rw [sum_hom_units]
      by_cases h : χ = φ.chC
      · rw [if_pos ((φ.twHom_eq_one_iff χ).2 h), if_pos h, φ.card_GG]
        norm_num
      · rw [if_neg (fun h' => h ((φ.twHom_eq_one_iff χ).1 h')), if_neg h, Nat.cast_zero]
    show (∑ g ∈ Finset.univ.filter (fun g : φ.GG => g ∉ φ.Psi), f g) = _
    rw [hS1] at hT1
    rw [hS2] at hT2
    by_cases h1 : χ = 1
    · have h2 : χ ≠ φ.chC := fun h => φ.chC_ne_one (h.symm.trans h1)
      rw [if_pos h1] at hT1 ⊢
      rw [if_neg h2] at hT2
      linear_combination (hT1 - hT2) / 2
    · rw [if_neg h1] at hT1 ⊢
      by_cases h2 : χ = φ.chC
      · rw [if_pos h2] at hT2 ⊢
        linear_combination (hT1 - hT2) / 2
      · rw [if_neg h2] at hT2 ⊢
        linear_combination (hT1 - hT2) / 2
  · obtain ⟨⟨q, d⟩, a⟩ := g
    show 4 * (if ((q, d) : G0) = ((1 : ℤˣ), (-1 : ℤˣ)) then (1 : ℤ) else 0) =
      (1 - ((d : ℤˣ) : ℤ)) * (1 + ((q : ℤˣ) : ℤ))
    rcases Int.units_eq_one_or q with rfl | rfl <;> rcases Int.units_eq_one_or d with rfl | rfl <;>
      norm_num [int_units_neg_one_ne_one, int_units_neg_one_ne_one.symm]

/- English proof (translation)
Rewrite `hg`, `hτ` using `[mem_Psi_iff]`. Rewrite using `[mem_Psi_iff]`. Establish `hg' : g.1.2 = -1` using `(Int.units_eq_one_or _).resolve_left hg`. Use `show g.1.2 ^ i * τ.1.2 = 1 ↔ Even i`. Rewrite using `[hg', hτ, mul_one]`.

Conclude with `neg_one_pow_eq_one_iff_even int_units_neg_one_ne_one`.
-/
theorem pow_mul_mem_Psi_iff {g : φ.GG} (hg : g ∉ φ.Psi) {τ : φ.GG} (hτ : τ ∈ φ.Psi) (i : ℕ) :
    g ^ i * τ ∈ φ.Psi ↔ Even i := by
  rw [mem_Psi_iff] at hg hτ
  rw [mem_Psi_iff]
  have hg' : g.1.2 = -1 := (Int.units_eq_one_or _).resolve_left hg
  show g.1.2 ^ i * τ.1.2 = 1 ↔ Even i
  rw [hg', hτ, mul_one]
  exact neg_one_pow_eq_one_iff_even int_units_neg_one_ne_one

/- English proof (translation)
Establish `hc0 : orderOf (c0 : G0) = 2` using `orderOf_eq_prime (sign_group_sq_eq_one_var _) (fun h => int_units_neg_one_ne_one (congrArg Prod.fst h))`. Rewrite using `[Prod.orderOf, hc, hc0]`.
-/
theorem orderOf_of_fst_eq_conjugation {g : φ.GG} (hc : g.1 = c0) : orderOf g = Nat.lcm 2 (orderOf g.2) := by
  have hc0 : orderOf (c0 : G0) = 2 :=
    orderOf_eq_prime (sign_group_sq_eq_one_var _) (fun h => int_units_neg_one_ne_one (congrArg Prod.fst h))
  rw [Prod.orderOf, hc, hc0]

/- English proof (translation)
Rewrite using `[mem_Psi_iff]`. Apply the tactic sequence `rcases hg with h | h <;> rw [h] <;> exact int_units_neg_one_ne_one`.
-/
private theorem not_mem_Psi_of_fst_eq_c0_or (g : φ.GG) (hg : g.1 = c0 ∨ g.1 = ((1 : ℤˣ), (-1 : ℤˣ))) :
    g ∉ φ.Psi := by
  rw [mem_Psi_iff]
  rcases hg with h | h <;> rw [h] <;> exact int_units_neg_one_ne_one

/- English proof (translation)
Establish `hg'` using `not_mem_Psi_of_fst_eq_c0_or φ g hg`. Use `⟨fun τ hτ i => φ.pow_mul_mem_Psi_iff hg' hτ i, fun hc he => ?_⟩` and prove the remaining obligations. Rewrite using `[φ.orderOf_of_fst_eq_conjugation hc]`. Conclude with `Nat.dvd_antisymm (Nat.lcm_dvd (even_iff_two_dvd.1 he) (dvd_refl _)) (Nat.dvd_lcm_right _ _)`.
-/
theorem hostOrbits' (g : φ.GG) (hg : g.1 = c0 ∨ g.1 = ((1 : ℤˣ), (-1 : ℤˣ))) :
    (∀ τ ∈ φ.Psi, ∀ i : ℕ, g ^ i * τ ∈ φ.Psi ↔ Even i) ∧
    (g.1 = c0 → Even (orderOf g.2) → orderOf g = orderOf g.2) := by
  have hg' := not_mem_Psi_of_fst_eq_c0_or φ g hg
  refine ⟨fun τ hτ i => φ.pow_mul_mem_Psi_iff hg' hτ i, fun hc he => ?_⟩
  rw [φ.orderOf_of_fst_eq_conjugation hc]
  exact Nat.dvd_antisymm (Nat.lcm_dvd (even_iff_two_dvd.1 he) (dvd_refl _)) (Nat.dvd_lcm_right _ _)

/- English proof (translation)
Establish `hg'` using `not_mem_Psi_of_fst_eq_c0_or φ g hg`. Use `⟨fun τ hτ i => φ.pow_mul_mem_Psi_iff hg' hτ i, fun hc h1 => ?_⟩` and prove the remaining obligations. Establish `he` using `h2.even_orderOf h1`. Conclude with `⟨he, (φ.hostOrbits' g hg).2 hc he⟩`.
-/
theorem hostOrbits (h2 : φ.TwoGroup) (g : φ.GG) (hg : g.1 = c0 ∨ g.1 = ((1 : ℤˣ), (-1 : ℤˣ))) :
    (∀ τ ∈ φ.Psi, ∀ i : ℕ, g ^ i * τ ∈ φ.Psi ↔ Even i) ∧
    (g.1 = c0 → g.2 ≠ 1 → Even (orderOf g.2) ∧ orderOf g = orderOf g.2) := by
  have hg' := not_mem_Psi_of_fst_eq_c0_or φ g hg
  refine ⟨fun τ hτ i => φ.pow_mul_mem_Psi_iff hg' hτ i, fun hc h1 => ?_⟩
  have he := h2.even_orderOf h1
  exact ⟨he, (φ.hostOrbits' g hg).2 hc he⟩

/- English proof (translation)
Establish `hg'` using `not_mem_Psi_of_fst_eq_c0_or φ g hg`. Use `⟨(φ.placeOf_snd _).trans rfl, fun hc => ?_, fun hs => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hi : Even i`. Rewrite using `[φ.placeOf_of_mem ((φ.pow_mul_mem_Psi_iff hg' hτ i).2 hi)] show g.1 ^ i * τ.1 = τ.1`. Rewrite using `[hc, G0_pow_eq_ite_even, if_pos hi, one_mul]`.

Rewrite using `[φ.placeOf_of_notMem (fun h => hi ((φ.pow_mul_mem_Psi_iff hg' hτ i).1 h))] show c0 * (g.1 ^ i * τ.1) = τ.1`. Rewrite using `[hc, G0_pow_eq_ite_even, if_neg hi, ← mul_assoc, ← pow_two, sign_group_sq_eq_one_var, one_mul]`. Distinguish the cases in `hi : Even i`. Rewrite using `[φ.placeOf_of_mem ((φ.pow_mul_mem_Psi_iff hg' hτ i).2 hi), if_pos hi] show g.1 ^ i * τ.1 = 1 * τ.1`. Rewrite using `[hs, G0_pow_eq_ite_even, if_pos hi]`.

Rewrite using `[φ.placeOf_of_notMem (fun h => hi ((φ.pow_mul_mem_Psi_iff hg' hτ i).1 h)), if_neg hi] show c0 * (g.1 ^ i * τ.1) = φ.sg.1 * τ.1`. Rewrite using `[hs, G0_pow_eq_ite_even, if_neg hi, ← mul_assoc]`. Use `congr 1`.
-/
theorem hostOrbitsPlaces (g : φ.GG) (hg : g.1 = c0 ∨ g.1 = ((1 : ℤˣ), (-1 : ℤˣ))) (τ : φ.GG) (hτ : τ ∈ φ.Psi)
    (i : ℕ) :
    (placeOf (g ^ i * τ)).2 = g.2 ^ i * τ.2 ∧
    (g.1 = c0 → (placeOf (g ^ i * τ)).1 = τ.1) ∧
    (g.1 = ((1 : ℤˣ), (-1 : ℤˣ)) →
      (placeOf (g ^ i * τ)).1 = (if Even i then 1 else φ.sg.1) * τ.1) := by
  have hg' := not_mem_Psi_of_fst_eq_c0_or φ g hg
  refine ⟨(φ.placeOf_snd _).trans rfl, fun hc => ?_, fun hs => ?_⟩
  · by_cases hi : Even i
    · rw [φ.placeOf_of_mem ((φ.pow_mul_mem_Psi_iff hg' hτ i).2 hi)]
      show g.1 ^ i * τ.1 = τ.1
      rw [hc, G0_pow_eq_ite_even, if_pos hi, one_mul]
    · rw [φ.placeOf_of_notMem (fun h => hi ((φ.pow_mul_mem_Psi_iff hg' hτ i).1 h))]
      show c0 * (g.1 ^ i * τ.1) = τ.1
      rw [hc, G0_pow_eq_ite_even, if_neg hi, ← mul_assoc, ← pow_two, sign_group_sq_eq_one_var, one_mul]
  · by_cases hi : Even i
    · rw [φ.placeOf_of_mem ((φ.pow_mul_mem_Psi_iff hg' hτ i).2 hi), if_pos hi]
      show g.1 ^ i * τ.1 = 1 * τ.1
      rw [hs, G0_pow_eq_ite_even, if_pos hi]
    · rw [φ.placeOf_of_notMem (fun h => hi ((φ.pow_mul_mem_Psi_iff hg' hτ i).1 h)), if_neg hi]
      show c0 * (g.1 ^ i * τ.1) = φ.sg.1 * τ.1
      rw [hs, G0_pow_eq_ite_even, if_neg hi, ← mul_assoc]
      congr 1

/- English proof (translation)
Establish `h : Nat.card (Submonoid.powers x) = orderOf x` using `Nat.card_submonoidPowers`. Rewrite using `[← h, ← Submonoid.coe_powers]`. Conclude with `(Nat.card_coe_set_eq _).symm`.
-/
private theorem ncard_range_pow_eq_orderOf {M : Type*} [Group M] (x : M) :
    (Set.range fun i : ℕ => x ^ i).ncard = orderOf x := by
  have h : Nat.card (Submonoid.powers x) = orderOf x := Nat.card_submonoidPowers
  rw [← h, ← Submonoid.coe_powers]
  exact (Nat.card_coe_set_eq _).symm

/- English proof (translation)
The claim follows from `orderOf_eq_prime (Int.units_sq _) int_units_neg_one_ne_one`.
-/
private theorem orderOf_int_units_neg_one_eq_two : orderOf (-1 : ℤˣ) = 2 :=
  orderOf_eq_prime (Int.units_sq _) int_units_neg_one_ne_one

/- English proof (translation)
Establish `hfun : (fun i : ℕ => placeOf (g ^ i * τ)) = (fun y : φ.MA => ((τ.1, y * τ.2) : φ.GG)) ∘ (fun i : ℕ => g.2 ^ i)`. Use function extensionality and compare the values at `i`. Take `⟨h1, h2, -⟩` from `φ.hostOrbitsPlaces g (Or.inl h0) τ hτ i`. Conclude with `Prod.ext (h2 h0) h1`. Rewrite using `[hfun, Set.range_comp, Set.ncard_image_of_injective _ (fun y y' h => mul_right_cancel (congrArg Prod.snd h)), ncard_range_pow_eq_orderOf]`.
-/
theorem hostOrbitCount (g : φ.GG) (h0 : g.1 = c0) (τ : φ.GG) (hτ : τ ∈ φ.Psi) :
    (Set.range fun i : ℕ => placeOf (g ^ i * τ)).ncard = orderOf g.2 := by
  have hfun : (fun i : ℕ => placeOf (g ^ i * τ)) =
      (fun y : φ.MA => ((τ.1, y * τ.2) : φ.GG)) ∘ (fun i : ℕ => g.2 ^ i) := by
    funext i
    obtain ⟨h1, h2, -⟩ := φ.hostOrbitsPlaces g (Or.inl h0) τ hτ i
    exact Prod.ext (h2 h0) h1
  rw [hfun, Set.range_comp, Set.ncard_image_of_injective _
    (fun y y' h => mul_right_cancel (congrArg Prod.snd h)), ncard_range_pow_eq_orderOf]

def orbEmb (τ : φ.GG) (x : ℤˣ × φ.MA) : φ.GG :=
  ((if x.1 = 1 then 1 else φ.sg.1) * τ.1, x.2 * τ.2)

/- English proof (translation)
Introduce and unpack `⟨s, a⟩ ⟨s', a'⟩ h`. Establish `h1 : (if s = 1 then (1 : G0) else φ.sg.1) * τ.1 = (if s' = 1 then 1 else φ.sg.1) * τ.1` using `congrArg Prod.fst h`. Establish `h2 : a * τ.2 = a' * τ.2` using `congrArg Prod.snd h`. Establish `h1'` using `mul_right_cancel h1`. Use `Prod.ext ?_ (mul_right_cancel h2)` and prove the remaining obligations.

Establish `hsg : (φ.sg.1 : G0) ≠ 1` using `fun h' => int_units_neg_one_ne_one (congrArg Prod.fst h')`. Apply the tactic sequence `rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or s' with rfl | rfl`. Both sides reduce to the same expression. Rewrite `h1'` using `[if_pos rfl, if_neg int_units_neg_one_ne_one]`. Conclude with `absurd h1'.symm hsg`.

Rewrite `h1'` using `[if_neg int_units_neg_one_ne_one, if_pos rfl]`. Conclude with `absurd h1' hsg`. Both sides reduce to the same expression.
-/
theorem orbEmb_injective (τ : φ.GG) : Function.Injective (φ.orbEmb τ) := by
  rintro ⟨s, a⟩ ⟨s', a'⟩ h
  have h1 : (if s = 1 then (1 : G0) else φ.sg.1) * τ.1 = (if s' = 1 then 1 else φ.sg.1) * τ.1 :=
    congrArg Prod.fst h
  have h2 : a * τ.2 = a' * τ.2 := congrArg Prod.snd h
  have h1' := mul_right_cancel h1
  refine Prod.ext ?_ (mul_right_cancel h2)
  have hsg : (φ.sg.1 : G0) ≠ 1 := fun h' => int_units_neg_one_ne_one (congrArg Prod.fst h')
  rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or s' with rfl | rfl
  · rfl
  · rw [if_pos rfl, if_neg int_units_neg_one_ne_one] at h1'
    exact absurd h1'.symm hsg
  · rw [if_neg int_units_neg_one_ne_one, if_pos rfl] at h1'
    exact absurd h1' hsg
  · rfl

/- English proof (translation)
Establish `hsq : orderOf g.1 = 2`. Rewrite using `[h0]`. Conclude with `orderOf_eq_prime (sign_group_sq_eq_one_var _) (fun h => int_units_neg_one_ne_one (congrArg Prod.snd h))`. Establish `hord : orderOf g = Nat.lcm 2 (orderOf g.2)` using `by rw [Prod.orderOf, hsq]`. Use `⟨hord, ?_⟩` and prove the remaining obligations.

Establish `hfun : (fun i : ℕ => placeOf (g ^ i * τ)) = φ.orbEmb τ ∘ (fun i : ℕ => (((-1 : ℤˣ), g.2) : ℤˣ × φ.MA) ^ i)`. Use function extensionality and compare the values at `i`. Take `⟨h1, -, h3⟩` from `φ.hostOrbitsPlaces g (Or.inr h0) τ hτ i`. Use `Prod.ext ?_ h1` and prove the remaining obligations. Rewrite using `[h3 h0]`.

Use `show _ = (if ((-1 : ℤˣ) ^ i) = 1 then 1 else φ.sg.1) * τ.1`. Distinguish the cases in `hi : Even i`. Rewrite using `[if_pos hi, if_pos ((neg_one_pow_eq_one_iff_even int_units_neg_one_ne_one).2 hi)]`. Rewrite using `[if_neg hi, if_neg (fun h => hi ((neg_one_pow_eq_one_iff_even int_units_neg_one_ne_one).1 h))]`. Rewrite using `[hfun, Set.range_comp, Set.ncard_image_of_injective _ (φ.orbEmb_injective τ), ncard_range_pow_eq_orderOf, hord, Prod.orderOf]`.

Conclude with `congrArg (fun n => Nat.lcm n (orderOf g.2)) orderOf_int_units_neg_one_eq_two`.
-/
theorem hostOrbitCountSg (g : φ.GG) (h0 : g.1 = ((1 : ℤˣ), (-1 : ℤˣ))) (τ : φ.GG) (hτ : τ ∈ φ.Psi) :
    orderOf g = Nat.lcm 2 (orderOf g.2) ∧
    (Set.range fun i : ℕ => placeOf (g ^ i * τ)).ncard = orderOf g := by
  have hsq : orderOf g.1 = 2 := by
    rw [h0]
    exact orderOf_eq_prime (sign_group_sq_eq_one_var _) (fun h => int_units_neg_one_ne_one (congrArg Prod.snd h))
  have hord : orderOf g = Nat.lcm 2 (orderOf g.2) := by rw [Prod.orderOf, hsq]
  refine ⟨hord, ?_⟩
  have hfun : (fun i : ℕ => placeOf (g ^ i * τ)) =
      φ.orbEmb τ ∘ (fun i : ℕ => (((-1 : ℤˣ), g.2) : ℤˣ × φ.MA) ^ i) := by
    funext i
    obtain ⟨h1, -, h3⟩ := φ.hostOrbitsPlaces g (Or.inr h0) τ hτ i
    refine Prod.ext ?_ h1
    rw [h3 h0]
    show _ = (if ((-1 : ℤˣ) ^ i) = 1 then 1 else φ.sg.1) * τ.1
    by_cases hi : Even i
    · rw [if_pos hi, if_pos ((neg_one_pow_eq_one_iff_even int_units_neg_one_ne_one).2 hi)]
    · rw [if_neg hi, if_neg (fun h => hi ((neg_one_pow_eq_one_iff_even int_units_neg_one_ne_one).1 h))]
  rw [hfun, Set.range_comp, Set.ncard_image_of_injective _ (φ.orbEmb_injective τ),
    ncard_range_pow_eq_orderOf, hord, Prod.orderOf]
  exact congrArg (fun n => Nat.lcm n (orderOf g.2)) orderOf_int_units_neg_one_eq_two

def InTranslate (T : Finset ℕ) (u₀ x : φ.A) : Prop := ∃ s ∈ T, x = φ.dig s + u₀

/- English proof (translation)
The claim follows from `(natCast_zsmul φ.a0 s).symm`.
-/
theorem dig_eq_zsmul (s : ℕ) : φ.dig s = (s : ℤ) • φ.a0 := (natCast_zsmul φ.a0 s).symm

/- English proof (translation)
Rewrite using `[sub_zsmul, sub_zsmul, ← φ.dig_eq_zsmul, ← φ.dig_eq_zsmul, eq_sub_of_add_eq hq.symm, eq_sub_of_add_eq hp.symm]`. Normalize the expressions using the abelian group laws.
-/
private theorem sub_smul_eq_sub_smul_a0_of_dig_eq (t u₀ x : φ.A) (p q : ℤ) (sp sq : ℕ)
    (hp : t + p • x = φ.dig sp + u₀) (hq : t + q • x = φ.dig sq + u₀) :
    (q - p) • x = ((sq : ℤ) - sp) • φ.a0 := by
  rw [sub_zsmul, sub_zsmul, ← φ.dig_eq_zsmul, ← φ.dig_eq_zsmul, eq_sub_of_add_eq hq.symm,
    eq_sub_of_add_eq hp.symm]
  abel

/- English proof (translation)
Take `⟨s1, hs1, h1⟩` from `hxa`. Take `⟨s2, hs2, h2⟩` from `hxb`. Take `⟨s3, hs3, h3⟩` from `hxc`. Rewrite `ha`, `hc` using `[Finset.mem_Ico]`. Establish `small : ∀ k : ℤ, 0 < k → k < L → k • x ≠ 0`.

Introduce `k hk hkL hk0`. Use `Int.le_of_dvd hk (addOrderOf_dvd_iff_zsmul_eq_zero.2 hk0)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `e12` using `sub_smul_eq_sub_smul_a0_of_dig_eq φ t u₀ x a b s1 s2 h1 h2`. Establish `e13` using `sub_smul_eq_sub_smul_a0_of_dig_eq φ t u₀ x a c s1 s3 h1 h3`.

Establish `e23` using `sub_smul_eq_sub_smul_a0_of_dig_eq φ t u₀ x b c s2 s3 h2 h3`. Distinguish the cases in `h12 : s1 = s2`. Substitute `h12` using the available equality. Conclude with `small (b - a) (by omega) (by omega) (by rw [e12, sub_self, zero_zsmul])`. Distinguish the cases in `h13 : s1 = s3`.

Substitute `h13` using the available equality. Conclude with `small (c - a) (by omega) (by omega) (by rw [e13, sub_self, zero_zsmul])`. Distinguish the cases in `h23 : s2 = s3`. Substitute `h23` using the available equality. Conclude with `small (c - b) (by omega) (by omega) (by rw [e23, sub_self, zero_zsmul])`.

Apply `hR s1 hs1 s2 hs2 s3 hs3 h12 h13 h23 (b - a) (c - a) (abs_pos.2 (by omega)) (abs_le.2 ⟨by omega, by omega⟩) (abs_pos.2 (by omega)) (abs_le.2 ⟨by omega, by omega⟩) (by omega)` to reduce the goal to its premises. Establish `hD : ((c - a) * ((s2 : ℤ) - s1) - (b - a) * ((s3 : ℤ) - s1)) • φ.a0 = 0`. Rewrite using `[sub_zsmul, ← smul_smul, ← smul_smul, ← e12, ← e13, smul_smul, smul_smul, mul_comm (c - a)]`. Normalize the expressions using the abelian group laws. Rewrite `hD` using `[φ.zsmul_generator_eq_zero_iff]`.

Establish `t1 : 4 * (L : ℤ) * s1 < φ.n0` using `by exact_mod_cast hT s1 hs1`. Establish `t2 : 4 * (L : ℤ) * s2 < φ.n0` using `by exact_mod_cast hT s2 hs2`. Establish `t3 : 4 * (L : ℤ) * s3 < φ.n0` using `by exact_mod_cast hT s3 hs3`. Establish `hcaL : c - a ≤ L` using `by omega`. Establish `hbaL : b - a ≤ L` using `by omega`.

Establish `hs1' : (0 : ℤ) ≤ s1` using `by positivity`. Establish `hs2' : (0 : ℤ) ≤ s2` using `by positivity`. Establish `hs3' : (0 : ℤ) ≤ s3` using `by positivity`. Establish `pA2 : (c - a) * (s2 : ℤ) ≤ L * s2` using `mul_le_mul_of_nonneg_right hcaL hs2'`. Establish `pA1 : (c - a) * (s1 : ℤ) ≤ L * s1` using `mul_le_mul_of_nonneg_right hcaL hs1'`.

Establish `pB3 : (b - a) * (s3 : ℤ) ≤ L * s3` using `mul_le_mul_of_nonneg_right hbaL hs3'`. Establish `pB1 : (b - a) * (s1 : ℤ) ≤ L * s1` using `mul_le_mul_of_nonneg_right hbaL hs1'`. Establish `qA2 : 0 ≤ (c - a) * (s2 : ℤ)` using `mul_nonneg (by omega) hs2'`. Establish `qA1 : 0 ≤ (c - a) * (s1 : ℤ)` using `mul_nonneg (by omega) hs1'`. Establish `qB3 : 0 ≤ (b - a) * (s3 : ℤ)` using `mul_nonneg (by omega) hs3'`.

Establish `qB1 : 0 ≤ (b - a) * (s1 : ℤ)` using `mul_nonneg (by omega) hs1'`. Establish `hz` using `Int.eq_zero_of_abs_lt_dvd hD (abs_lt.2 ⟨by linarith, by linarith⟩)`. Take the linear combination `hz`.
-/
theorem thick_key {L : ℕ} (T : Finset ℕ) (hT : ∀ s ∈ T, 4 * L * s < φ.n0) (hR : NoRel T L)
    (u₀ t x : φ.A) (hord : 4 * L < addOrderOf x) (i₀ a b c : ℤ)
    (ha : a ∈ Finset.Ico i₀ (i₀ + L)) (hc : c ∈ Finset.Ico i₀ (i₀ + L)) (hab : a < b)
    (hbc : b < c) (hxa : φ.InTranslate T u₀ (t + a • x)) (hxb : φ.InTranslate T u₀ (t + b • x))
    (hxc : φ.InTranslate T u₀ (t + c • x)) : False := by
  obtain ⟨s1, hs1, h1⟩ := hxa
  obtain ⟨s2, hs2, h2⟩ := hxb
  obtain ⟨s3, hs3, h3⟩ := hxc
  rw [Finset.mem_Ico] at ha hc
  have small : ∀ k : ℤ, 0 < k → k < L → k • x ≠ 0 := by
    intro k hk hkL hk0
    have := Int.le_of_dvd hk (addOrderOf_dvd_iff_zsmul_eq_zero.2 hk0)
    omega
  have e12 := sub_smul_eq_sub_smul_a0_of_dig_eq φ t u₀ x a b s1 s2 h1 h2
  have e13 := sub_smul_eq_sub_smul_a0_of_dig_eq φ t u₀ x a c s1 s3 h1 h3
  have e23 := sub_smul_eq_sub_smul_a0_of_dig_eq φ t u₀ x b c s2 s3 h2 h3
  by_cases h12 : s1 = s2
  · subst h12
    exact small (b - a) (by omega) (by omega) (by rw [e12, sub_self, zero_zsmul])
  by_cases h13 : s1 = s3
  · subst h13
    exact small (c - a) (by omega) (by omega) (by rw [e13, sub_self, zero_zsmul])
  by_cases h23 : s2 = s3
  · subst h23
    exact small (c - b) (by omega) (by omega) (by rw [e23, sub_self, zero_zsmul])
  apply hR s1 hs1 s2 hs2 s3 hs3 h12 h13 h23 (b - a) (c - a) (abs_pos.2 (by omega))
    (abs_le.2 ⟨by omega, by omega⟩) (abs_pos.2 (by omega)) (abs_le.2 ⟨by omega, by omega⟩) (by omega)
  have hD : ((c - a) * ((s2 : ℤ) - s1) - (b - a) * ((s3 : ℤ) - s1)) • φ.a0 = 0 := by
    rw [sub_zsmul, ← smul_smul, ← smul_smul, ← e12, ← e13, smul_smul, smul_smul,
      mul_comm (c - a)]
    abel
  rw [φ.zsmul_generator_eq_zero_iff] at hD
  have t1 : 4 * (L : ℤ) * s1 < φ.n0 := by exact_mod_cast hT s1 hs1
  have t2 : 4 * (L : ℤ) * s2 < φ.n0 := by exact_mod_cast hT s2 hs2
  have t3 : 4 * (L : ℤ) * s3 < φ.n0 := by exact_mod_cast hT s3 hs3
  have hcaL : c - a ≤ L := by omega
  have hbaL : b - a ≤ L := by omega
  have hs1' : (0 : ℤ) ≤ s1 := by positivity
  have hs2' : (0 : ℤ) ≤ s2 := by positivity
  have hs3' : (0 : ℤ) ≤ s3 := by positivity
  have pA2 : (c - a) * (s2 : ℤ) ≤ L * s2 := mul_le_mul_of_nonneg_right hcaL hs2'
  have pA1 : (c - a) * (s1 : ℤ) ≤ L * s1 := mul_le_mul_of_nonneg_right hcaL hs1'
  have pB3 : (b - a) * (s3 : ℤ) ≤ L * s3 := mul_le_mul_of_nonneg_right hbaL hs3'
  have pB1 : (b - a) * (s1 : ℤ) ≤ L * s1 := mul_le_mul_of_nonneg_right hbaL hs1'
  have qA2 : 0 ≤ (c - a) * (s2 : ℤ) := mul_nonneg (by omega) hs2'
  have qA1 : 0 ≤ (c - a) * (s1 : ℤ) := mul_nonneg (by omega) hs1'
  have qB3 : 0 ≤ (b - a) * (s3 : ℤ) := mul_nonneg (by omega) hs3'
  have qB1 : 0 ≤ (b - a) * (s1 : ℤ) := mul_nonneg (by omega) hs1'
  have hz := Int.eq_zero_of_abs_lt_dvd hD (abs_lt.2 ⟨by linarith, by linarith⟩)
  linear_combination hz

open Classical in

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Take `⟨p, hp, q, hq, r, hr, hpq, hpr, hqr⟩` from `Finset.two_lt_card.1 hcon`. Rewrite `hp`, `hq`, `hr` using `[Finset.mem_filter]`. Establish `K : ∀ a b c : ℤ, a ∈ Finset.Ico i₀ (i₀ + L) → b ∈ Finset.Ico i₀ (i₀ + L) → c ∈ Finset.Ico i₀ (i₀ + L) → a < b → b < c → φ.InTranslate T u₀ (t + a • x) → φ.InTranslate T u₀ (t + b • x) → φ.InTranslate T u₀ (t + c • x) → False` using `fun a b c ha _ hc hab hbc hxa hxb hxc => φ.thick_key T hT hR u₀ t x hord i₀ a b c ha hc hab hbc hxa hxb hxc`.

Apply the tactic sequence `rcases lt_or_gt_of_ne hpq with h1 | h1 <;> rcases lt_or_gt_of_ne hpr with h2 | h2 <;>`. Apply the tactic sequence `rcases lt_or_gt_of_ne hqr with h3 | h3 <;>`. Use `first`. Consider the case `omega`. Consider the case `exact K p q r hp.1 hq.1 hr.1 (by omega) (by omega) hp.2 hq.2 hr.2`.

Consider the case `exact K p r q hp.1 hr.1 hq.1 (by omega) (by omega) hp.2 hr.2 hq.2`. Consider the case `exact K q p r hq.1 hp.1 hr.1 (by omega) (by omega) hq.2 hp.2 hr.2`. Consider the case `exact K q r p hq.1 hr.1 hp.1 (by omega) (by omega) hq.2 hr.2 hp.2`. Consider the case `exact K r p q hr.1 hp.1 hq.1 (by omega) (by omega) hr.2 hp.2 hq.2`. Consider the case `exact K r q p hr.1 hq.1 hp.1 (by omega) (by omega) hr.2 hq.2 hp.2`.
-/
theorem thick_part_one {L : ℕ} (T : Finset ℕ) (hT : ∀ s ∈ T, 4 * L * s < φ.n0) (hR : NoRel T L)
    (u₀ t x : φ.A) (hord : 4 * L < addOrderOf x) (i₀ : ℤ) :
    ((Finset.Ico i₀ (i₀ + L)).filter (fun i : ℤ => φ.InTranslate T u₀ (t + i • x))).card ≤ 2 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨p, hp, q, hq, r, hr, hpq, hpr, hqr⟩ := Finset.two_lt_card.1 hcon
  rw [Finset.mem_filter] at hp hq hr
  have K : ∀ a b c : ℤ, a ∈ Finset.Ico i₀ (i₀ + L) → b ∈ Finset.Ico i₀ (i₀ + L) →
      c ∈ Finset.Ico i₀ (i₀ + L) → a < b → b < c → φ.InTranslate T u₀ (t + a • x) →
      φ.InTranslate T u₀ (t + b • x) → φ.InTranslate T u₀ (t + c • x) → False :=
    fun a b c ha _ hc hab hbc hxa hxb hxc =>
      φ.thick_key T hT hR u₀ t x hord i₀ a b c ha hc hab hbc hxa hxb hxc
  rcases lt_or_gt_of_ne hpq with h1 | h1 <;> rcases lt_or_gt_of_ne hpr with h2 | h2 <;>
    rcases lt_or_gt_of_ne hqr with h3 | h3 <;>
    first
    | omega
    | exact K p q r hp.1 hq.1 hr.1 (by omega) (by omega) hp.2 hq.2 hr.2
    | exact K p r q hp.1 hr.1 hq.1 (by omega) (by omega) hp.2 hr.2 hq.2
    | exact K q p r hq.1 hp.1 hr.1 (by omega) (by omega) hq.2 hp.2 hr.2
    | exact K q r p hq.1 hr.1 hp.1 (by omega) (by omega) hq.2 hr.2 hp.2
    | exact K r p q hr.1 hp.1 hq.1 (by omega) (by omega) hr.2 hp.2 hq.2
    | exact K r q p hr.1 hq.1 hp.1 (by omega) (by omega) hr.2 hq.2 hp.2

/- English proof (translation)
Rewrite using `[Set.ncard_le_one (Set.toFinite _)]`. Introduce and unpack `y1 ⟨⟨i, rfl⟩, s1, hs1, h1⟩ y2 ⟨⟨j, rfl⟩, s2, hs2, h2⟩`. Establish `e : (j - i) • x = ((s2 : ℤ) - s1) • φ.a0` using `sub_smul_eq_sub_smul_a0_of_dig_eq φ t u₀ x i j s1 s2 h1 h2`. Establish `hm0 : 0 < addOrderOf (φ.h x)` using `addOrderOf_pos _`. Establish `hz : ((addOrderOf (φ.h x) : ℤ) • (((s2 : ℤ) - s1) • φ.a0)) = 0`.

Apply `φ.eq_zero_of_mem_cyclic_of_projection` to reduce the goal to its premises. Conclude with `φ.A0.zsmul_mem (φ.A0.zsmul_mem (AddSubgroup.mem_zmultiples φ.a0) _) _`. Rewrite using `[← e, map_zsmul, map_zsmul, smul_comm, natCast_zsmul, addOrderOf_nsmul_eq_zero, smul_zero]`. Rewrite `hz` using `[smul_smul, φ.zsmul_generator_eq_zero_iff]`. Establish `t1 : 4 * (L : ℤ) * s1 < φ.n0` using `by exact_mod_cast hT s1 hs1`.

Establish `t2 : 4 * (L : ℤ) * s2 < φ.n0` using `by exact_mod_cast hT s2 hs2`. Establish `hmL : (addOrderOf (φ.h x) : ℤ) ≤ 4 * L` using `by exact_mod_cast hord`. Establish `hm0' : (0 : ℤ) < addOrderOf (φ.h x)` using `by exact_mod_cast hm0`. Establish `p1 : (addOrderOf (φ.h x) : ℤ) * s2 ≤ 4 * L * s2` using `mul_le_mul_of_nonneg_right hmL (by positivity)`. Establish `p2 : (addOrderOf (φ.h x) : ℤ) * s1 ≤ 4 * L * s1` using `mul_le_mul_of_nonneg_right hmL (by positivity)`.

Establish `p3 : 0 ≤ (addOrderOf (φ.h x) : ℤ) * s1` using `by positivity`. Establish `p4 : 0 ≤ (addOrderOf (φ.h x) : ℤ) * s2` using `by positivity`. Establish `hz'` using `Int.eq_zero_of_abs_lt_dvd hz (abs_lt.2 ⟨by linarith, by linarith⟩)`. Establish `hs : s1 = s2`. Break down `mul_eq_zero.1 hz' with h | h` into its components or cases.

Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers. Rewrite using `[h1, h2, hs]`.
-/
theorem thick_part_two {L : ℕ} (T : Finset ℕ) (hT : ∀ s ∈ T, 4 * L * s < φ.n0)
    (u₀ t x : φ.A) (hord : addOrderOf (φ.h x) ≤ 4 * L) :
    {y : φ.A | (∃ i : ℤ, y = t + i • x) ∧ φ.InTranslate T u₀ y}.ncard ≤ 1 := by
  rw [Set.ncard_le_one (Set.toFinite _)]
  rintro y1 ⟨⟨i, rfl⟩, s1, hs1, h1⟩ y2 ⟨⟨j, rfl⟩, s2, hs2, h2⟩
  have e : (j - i) • x = ((s2 : ℤ) - s1) • φ.a0 := sub_smul_eq_sub_smul_a0_of_dig_eq φ t u₀ x i j s1 s2 h1 h2
  have hm0 : 0 < addOrderOf (φ.h x) := addOrderOf_pos _
  have hz : ((addOrderOf (φ.h x) : ℤ) • (((s2 : ℤ) - s1) • φ.a0)) = 0 := by
    apply φ.eq_zero_of_mem_cyclic_of_projection
    · exact φ.A0.zsmul_mem (φ.A0.zsmul_mem (AddSubgroup.mem_zmultiples φ.a0) _) _
    · rw [← e, map_zsmul, map_zsmul, smul_comm, natCast_zsmul, addOrderOf_nsmul_eq_zero, smul_zero]
  rw [smul_smul, φ.zsmul_generator_eq_zero_iff] at hz
  have t1 : 4 * (L : ℤ) * s1 < φ.n0 := by exact_mod_cast hT s1 hs1
  have t2 : 4 * (L : ℤ) * s2 < φ.n0 := by exact_mod_cast hT s2 hs2
  have hmL : (addOrderOf (φ.h x) : ℤ) ≤ 4 * L := by exact_mod_cast hord
  have hm0' : (0 : ℤ) < addOrderOf (φ.h x) := by exact_mod_cast hm0
  have p1 : (addOrderOf (φ.h x) : ℤ) * s2 ≤ 4 * L * s2 :=
    mul_le_mul_of_nonneg_right hmL (by positivity)
  have p2 : (addOrderOf (φ.h x) : ℤ) * s1 ≤ 4 * L * s1 :=
    mul_le_mul_of_nonneg_right hmL (by positivity)
  have p3 : 0 ≤ (addOrderOf (φ.h x) : ℤ) * s1 := by positivity
  have p4 : 0 ≤ (addOrderOf (φ.h x) : ℤ) * s2 := by positivity
  have hz' := Int.eq_zero_of_abs_lt_dvd hz (abs_lt.2 ⟨by linarith, by linarith⟩)
  have hs : s1 = s2 := by
    rcases mul_eq_zero.1 hz' with h | h
    · omega
    · omega
  rw [h1, h2, hs]

open Classical in

/- English proof (translation)
Use `⟨fun h i₀ => φ.thick_part_one T hT hR u₀ t x h i₀, fun h => φ.thick_part_two T hT u₀ t x ?_⟩` and prove the remaining obligations. Conclude with `le_trans (Nat.le_of_dvd (addOrderOf_pos x) (φ.addOrderOf_h_dvd x)) h`.
-/
theorem hostThickOrbit {L : ℕ} (T : Finset ℕ) (hT : ∀ s ∈ T, 4 * L * s < φ.n0) (hR : NoRel T L)
    (u₀ t x : φ.A) :
    (4 * L < addOrderOf x → ∀ i₀ : ℤ,
      ((Finset.Ico i₀ (i₀ + L)).filter (fun i : ℤ => φ.InTranslate T u₀ (t + i • x))).card ≤ 2) ∧
    (addOrderOf x ≤ 4 * L →
      {y : φ.A | (∃ i : ℤ, y = t + i • x) ∧ φ.InTranslate T u₀ y}.ncard ≤ 1) := by
  refine ⟨fun h i₀ => φ.thick_part_one T hT hR u₀ t x h i₀, fun h => φ.thick_part_two T hT u₀ t x ?_⟩
  exact le_trans (Nat.le_of_dvd (addOrderOf_pos x) (φ.addOrderOf_h_dvd x)) h

open Classical in

/- English proof (translation)
Use `⟨fun h i₀ => φ.thick_part_one T hT hR u₀ t x ?_ i₀, fun h => φ.thick_part_two T hT u₀ t x h⟩` and prove the remaining obligations. Conclude with `lt_of_lt_of_le h (Nat.le_of_dvd (addOrderOf_pos x) (φ.addOrderOf_h_dvd x))`.
-/
theorem hostThickOrbitH {L : ℕ} (T : Finset ℕ) (hT : ∀ s ∈ T, 4 * L * s < φ.n0) (hR : NoRel T L)
    (u₀ t x : φ.A) :
    (4 * L < addOrderOf (φ.h x) → ∀ i₀ : ℤ,
      ((Finset.Ico i₀ (i₀ + L)).filter (fun i : ℤ => φ.InTranslate T u₀ (t + i • x))).card ≤ 2) ∧
    (addOrderOf (φ.h x) ≤ 4 * L →
      {y : φ.A | (∃ i : ℤ, y = t + i • x) ∧ φ.InTranslate T u₀ y}.ncard ≤ 1) := by
  refine ⟨fun h i₀ => φ.thick_part_one T hT hR u₀ t x ?_ i₀, fun h => φ.thick_part_two T hT u₀ t x h⟩
  exact lt_of_lt_of_le h (Nat.le_of_dvd (addOrderOf_pos x) (φ.addOrderOf_h_dvd x))

end Formalism.HC.Frame

end
