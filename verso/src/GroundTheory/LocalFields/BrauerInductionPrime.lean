import Mathlib
import GroundTheory.LocalFields.BrauerInductionLocal

noncomputable section

namespace GroundTheory.LocalField

open Module Representation

open scoped Classical

universe u

variable {G : Type u} [Group G]

section MulSubgroup

def mulSubgroup (C P : Subgroup G) (hcomm : ∀ c ∈ C, ∀ y ∈ P, c * y = y * c) : Subgroup G where
  carrier := {h | ∃ c ∈ C, ∃ y ∈ P, h = c * y}
  one_mem' := ⟨1, C.one_mem, 1, P.one_mem, (mul_one 1).symm⟩
  mul_mem' := by
    rintro _ _ ⟨c, hc, y, hy, rfl⟩ ⟨c', hc', y', hy', rfl⟩
    refine ⟨c * c', C.mul_mem hc hc', y * y', P.mul_mem hy hy', ?_⟩
    rw [show c * y * (c' * y') = c * (y * c') * y' by group, ← hcomm c' hc' y hy]
    group
  inv_mem' := by
    rintro _ ⟨c, hc, y, hy, rfl⟩
    refine ⟨c⁻¹, C.inv_mem hc, y⁻¹, P.inv_mem hy, ?_⟩
    rw [mul_inv_rev]
    exact (hcomm c⁻¹ (C.inv_mem hc) y⁻¹ (P.inv_mem hy)).symm

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_mulSubgroup {C P : Subgroup G} {hcomm : ∀ c ∈ C, ∀ y ∈ P, c * y = y * c} {h : G} :
    h ∈ mulSubgroup C P hcomm ↔ ∃ c ∈ C, ∃ y ∈ P, h = c * y := Iff.rfl

/- English proof (translation)
The claim follows from `fun c hc ↦ ⟨c, hc, 1, P.one_mem, (mul_one c).symm⟩`.
-/
theorem left_le_mulSubgroup {C P : Subgroup G} (hcomm : ∀ c ∈ C, ∀ y ∈ P, c * y = y * c) :
    C ≤ mulSubgroup C P hcomm := fun c hc ↦ ⟨c, hc, 1, P.one_mem, (mul_one c).symm⟩

/- English proof (translation)
The claim follows from `fun y hy ↦ ⟨1, C.one_mem, y, hy, (one_mul y).symm⟩`.
-/
theorem right_le_mulSubgroup {C P : Subgroup G} (hcomm : ∀ c ∈ C, ∀ y ∈ P, c * y = y * c) :
    P ≤ mulSubgroup C P hcomm := fun y hy ↦ ⟨1, C.one_mem, y, hy, (one_mul y).symm⟩

end MulSubgroup

variable [Fintype G] (p : ℕ) [hp : Fact p.Prime] (x : G)

def sylowCent : Subgroup G :=
  ((Classical.arbitrary (Sylow p (Subgroup.centralizer {x}))) : Subgroup (Subgroup.centralizer {x})).map
    (Subgroup.centralizer {x}).subtype

variable {p x}

omit [Fintype G] hp in
/- English proof (translation)
Establish `: y ∈ Subgroup.centralizer {x}` using `Subgroup.map_subtype_le _ hy`. Conclude with `Subgroup.mem_centralizer_singleton_iff.mp this`.
-/
theorem commute_of_mem_sylowCent {y : G} (hy : y ∈ sylowCent p x) : y * x = x * y := by
  have : y ∈ Subgroup.centralizer {x} := Subgroup.map_subtype_le _ hy
  exact Subgroup.mem_centralizer_singleton_iff.mp this

omit [Fintype G] hp in
variable (p x) in
/- English proof (translation)
The claim follows from `(Classical.arbitrary (Sylow p (Subgroup.centralizer {x}))).isPGroup'.map _`.
-/
theorem isPGroup_sylowCent : IsPGroup p (sylowCent p x) :=
  (Classical.arbitrary (Sylow p (Subgroup.centralizer {x}))).isPGroup'.map _

variable (p x) in

/- English proof (translation)
Use `set P0 := Classical.arbitrary (Sylow p (Subgroup.centralizer {x}))`. Use `⟨(P0 : Subgroup (Subgroup.centralizer {x})).index, ?_, P0.not_dvd_index⟩` and prove the remaining obligations. Rewrite using `[sylowCent, Subgroup.card_map_of_injective (Subgroup.subtype_injective _), Subgroup.card_mul_index]`.
-/
theorem exists_card_centralizer_eq :
    ∃ m : ℕ, Nat.card (Subgroup.centralizer {x}) = Nat.card (sylowCent p x) * m ∧ ¬ p ∣ m := by
  set P0 := Classical.arbitrary (Sylow p (Subgroup.centralizer {x}))
  refine ⟨(P0 : Subgroup (Subgroup.centralizer {x})).index, ?_, P0.not_dvd_index⟩
  rw [sylowCent, Subgroup.card_map_of_injective (Subgroup.subtype_injective _), Subgroup.card_mul_index]

omit [Fintype G] hp in
/- English proof (translation)
Introduce `c hc y hy`. Take `⟨i, rfl⟩` from `Subgroup.mem_zpowers_iff.mp hc`. Conclude with `((Commute.symm (commute_of_mem_sylowCent hy)).zpow_left i).eq`.
-/
theorem commute_zpowers_sylowCent :
    ∀ c ∈ Subgroup.zpowers x, ∀ y ∈ sylowCent p x, c * y = y * c := by
  intro c hc y hy
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  exact ((Commute.symm (commute_of_mem_sylowCent hy)).zpow_left i).eq

variable (p x) in

def elemSub : Subgroup G := mulSubgroup (Subgroup.zpowers x) (sylowCent p x) commute_zpowers_sylowCent

omit [Fintype G] hp in
/- English proof (translation)
The claim follows from `left_le_mulSubgroup _ (Subgroup.mem_zpowers x)`.
-/
theorem mem_elemSub_self : x ∈ elemSub p x :=
  left_le_mulSubgroup _ (Subgroup.mem_zpowers x)

omit [Fintype G] hp in
/- English proof (translation)
The claim follows from `right_le_mulSubgroup _`.
-/
theorem sylowCent_le_elemSub : sylowCent p x ≤ elemSub p x := right_le_mulSubgroup _

omit [Fintype G] hp in
/- English proof (translation)
Assemble the required witnesses or components as `⟨Subgroup.zpowers x, sylowCent p x, left_le_mulSubgroup _, right_le_mulSubgroup _, inferInstance, by rwa [Nat.card_zpowers], isPGroup_sylowCent p x, commute_zpowers_sylowCent, fun _ hh ↦ hh⟩`.
-/
theorem isElementaryAt_elemSub (hx : (orderOf x).Coprime p) : IsElementaryAt p (elemSub p x) :=
  ⟨Subgroup.zpowers x, sylowCent p x, left_le_mulSubgroup _, right_le_mulSubgroup _, inferInstance,
    by rwa [Nat.card_zpowers], isPGroup_sylowCent p x, commute_zpowers_sylowCent,
    fun _ hh ↦ hh⟩

variable (p x) in

abbrev sylowCentIn : Subgroup (elemSub p x) := (sylowCent p x).subgroupOf (elemSub p x)

instance normal_sylowCentIn : (sylowCentIn p x).Normal := by
  constructor
  intro n hn g
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨c, hc, y, hy, hg⟩ := mem_mulSubgroup.mp g.2
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hg]
  have hw : y * n * y⁻¹ ∈ sylowCent p x :=
    (sylowCent p x).mul_mem ((sylowCent p x).mul_mem hy hn) ((sylowCent p x).inv_mem hy)
  rw [show c * y * (n : G) * (c * y)⁻¹ = c * (y * n * y⁻¹) * c⁻¹ by group,
    commute_zpowers_sylowCent c hc _ hw, mul_inv_cancel_right]
  exact hw

omit [Fintype G] hp in
/- English proof (translation)
Take `⟨a, rfl⟩` from `QuotientGroup.mk_surjective a`. Take `⟨b, rfl⟩` from `QuotientGroup.mk_surjective b`. Rewrite using `[← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]`. Take `⟨c1, hc1, y1, hy1, ha⟩` from `mem_mulSubgroup.mp a.2`. Take `⟨c2, hc2, y2, hy2, hb⟩` from `mem_mulSubgroup.mp b.2`.

Establish `hcc : c1 * c2 = c2 * c1`. Take `⟨i, rfl⟩` from `Subgroup.mem_zpowers_iff.mp hc1`. Take `⟨j, rfl⟩` from `Subgroup.mem_zpowers_iff.mp hc2`. Rewrite using `[← zpow_add, ← zpow_add, add_comm]`. Establish `hab : ((a * b : elemSub p x) : G) = (c1 * c2) * (y1 * y2)`.

Simplify using `only [Subgroup.coe_mul, ha, hb]`. Rewrite using `[show c1 * y1 * (c2 * y2) = c1 * (y1 * c2) * y2 by group, ← commute_zpowers_sylowCent c2 hc2 y1 hy1]`. Use `group`. Establish `hba : ((b * a : elemSub p x) : G) = (c1 * c2) * (y2 * y1)`. Simplify using `only [Subgroup.coe_mul, ha, hb]`.

Rewrite using `[show c2 * y2 * (c1 * y1) = c2 * (y2 * c1) * y1 by group, ← commute_zpowers_sylowCent c1 hc1 y2 hy2, hcc]`. Use `group`. Simplify using `only [Subgroup.coe_mul, Subgroup.coe_inv] at hab hba ⊢`. Rewrite using `[hab, hba, show (c1 * c2 * (y1 * y2))⁻¹ * (c1 * c2 * (y2 * y1)) = (y1 * y2)⁻¹ * (y2 * y1) by group]`. Conclude with `(sylowCent p x).mul_mem ((sylowCent p x).inv_mem ((sylowCent p x).mul_mem hy1 hy2)) ((sylowCent p x).mul_mem hy2 hy1)`.
-/
theorem quotient_mul_comm (a b : elemSub p x ⧸ sylowCentIn p x) : a * b = b * a := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  obtain ⟨c1, hc1, y1, hy1, ha⟩ := mem_mulSubgroup.mp a.2
  obtain ⟨c2, hc2, y2, hy2, hb⟩ := mem_mulSubgroup.mp b.2
  have hcc : c1 * c2 = c2 * c1 := by
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc1
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc2
    rw [← zpow_add, ← zpow_add, add_comm]
  have hab : ((a * b : elemSub p x) : G) = (c1 * c2) * (y1 * y2) := by
    simp only [Subgroup.coe_mul, ha, hb]
    rw [show c1 * y1 * (c2 * y2) = c1 * (y1 * c2) * y2 by group,
      ← commute_zpowers_sylowCent c2 hc2 y1 hy1]
    group
  have hba : ((b * a : elemSub p x) : G) = (c1 * c2) * (y2 * y1) := by
    simp only [Subgroup.coe_mul, ha, hb]
    rw [show c2 * y2 * (c1 * y1) = c2 * (y2 * c1) * y1 by group,
      ← commute_zpowers_sylowCent c1 hc1 y2 hy2, hcc]
    group
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hab hba ⊢
  rw [hab, hba, show (c1 * c2 * (y1 * y2))⁻¹ * (c1 * c2 * (y2 * y1)) = (y1 * y2)⁻¹ * (y2 * y1) by group]
  exact (sylowCent p x).mul_mem ((sylowCent p x).inv_mem ((sylowCent p x).mul_mem hy1 hy2))
    ((sylowCent p x).mul_mem hy2 hy1)

section Theta

variable (p x) in

def xIn : elemSub p x := ⟨x, mem_elemSub_self⟩

variable (p x) in

def theta (h : elemSub p x) : ℂ :=
  if (h : elemSub p x ⧸ sylowCentIn p x) = (xIn p x : elemSub p x ⧸ sylowCentIn p x) then
    (Nat.card (elemSub p x ⧸ sylowCentIn p x) : ℂ) else 0

omit [Fintype G] hp in
/- English proof (translation)
Rewrite using `[QuotientGroup.eq, Subgroup.mem_subgroupOf, ← (sylowCent p x).inv_mem_iff]`. Simplify using `[xIn]`.
-/
theorem mk_eq_mk_xIn_iff (h : elemSub p x) :
    (h : elemSub p x ⧸ sylowCentIn p x) = (xIn p x : elemSub p x ⧸ sylowCentIn p x) ↔
      x⁻¹ * (h : G) ∈ sylowCent p x := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, ← (sylowCent p x).inv_mem_iff]
  simp [xIn]

omit hp in

/- English proof (translation)
Use `set H := elemSub p x`. Use `set P := sylowCent p x`. Use `set Q := H ⧸ sylowCentIn p x`. Establish `hinner : ∀ z : G, ∑ h : H, (if (H.subtype h) = z then theta p x h else 0) = if x⁻¹ * z ∈ P then (Nat.card Q : ℂ) else 0`. Introduce `z`.

Distinguish the cases in `hz : z ∈ H`. Rewrite using `[Finset.sum_eq_single ⟨z, hz⟩]`. Rewrite using `[show H.subtype ⟨z, hz⟩ = z from rfl, if_pos rfl, theta]`. Establish `hiff` using `mk_eq_mk_xIn_iff (p := p) (x := x) ⟨z, hz⟩`. Distinguish the cases in `hc : x⁻¹ * z ∈ P`.

Rewrite using `[if_pos (hiff.mpr hc), if_pos hc]`. Rewrite using `[if_neg (fun h ↦ hc (hiff.mp h)), if_neg hc]`. Introduce `h _ hne`. Rewrite using `[if_neg]`. Introduce `h'`.

Conclude with `hne (Subtype.ext h')`. Introduce `h'`. Conclude with `absurd (Finset.mem_univ _) h'`. Rewrite using `[Finset.sum_eq_zero, if_neg]`. Introduce `hP`.

Apply `hz` to reduce the goal to its premises. Use `H.mul_mem (mem_elemSub_self (p := p)) (sylowCent_le_elemSub hP)` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel_left]`. Then use the resulting hypothesis. Introduce `h _`. Rewrite using `[if_neg]`.

Introduce `h'`. Conclude with `hz (h' ▸ h.2)`. Establish `hcard : (Nat.card H : ℂ) = Nat.card Q * Nat.card P`. Rewrite using `[Subgroup.card_eq_card_quotient_mul_card_subgroup (sylowCentIn p x), Nat.card_congr (Subgroup.subgroupOfEquivOfLe sylowCent_le_elemSub).toEquiv]`. Use `push_cast`.

Both sides reduce to the same expression. Establish `hQ : (Nat.card Q : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr Nat.card_pos.ne'`. Establish `hP : (Nat.card P : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr Nat.card_pos.ne'`. Rewrite using `[indFun_apply, Finset.sum_congr rfl fun t _ ↦ hinner _, hcard, ← mul_assoc, mul_inv, mul_comm (Nat.card Q : ℂ)⁻¹, ← mul_assoc, mul_inv_cancel₀ hP, one_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun t _ ↦ ?_` and prove the remaining obligations.

Use `split_ifs`. Conclude with `inv_mul_cancel₀ hQ`. Simplify using the standard rewrite rules.
-/
theorem card_mul_indFun_theta (g : G) :
    (Nat.card (sylowCent p x) : ℂ) * indFun (elemSub p x).subtype (theta p x) g =
      ∑ t : G, if x⁻¹ * (t⁻¹ * g * t) ∈ sylowCent p x then 1 else 0 := by
  set H := elemSub p x
  set P := sylowCent p x
  set Q := H ⧸ sylowCentIn p x
  have hinner : ∀ z : G, ∑ h : H, (if (H.subtype h) = z then theta p x h else 0) =
      if x⁻¹ * z ∈ P then (Nat.card Q : ℂ) else 0 := by
    intro z
    by_cases hz : z ∈ H
    · rw [Finset.sum_eq_single ⟨z, hz⟩]
      · rw [show H.subtype ⟨z, hz⟩ = z from rfl, if_pos rfl, theta]
        have hiff := mk_eq_mk_xIn_iff (p := p) (x := x) ⟨z, hz⟩
        by_cases hc : x⁻¹ * z ∈ P
        · rw [if_pos (hiff.mpr hc), if_pos hc]
        · rw [if_neg (fun h ↦ hc (hiff.mp h)), if_neg hc]
      · intro h _ hne
        rw [if_neg]
        intro h'
        exact hne (Subtype.ext h')
      · intro h'
        exact absurd (Finset.mem_univ _) h'
    · rw [Finset.sum_eq_zero, if_neg]
      · intro hP
        apply hz
        have := H.mul_mem (mem_elemSub_self (p := p)) (sylowCent_le_elemSub hP)
        rwa [mul_inv_cancel_left] at this
      · intro h _
        rw [if_neg]
        intro h'
        exact hz (h' ▸ h.2)
  have hcard : (Nat.card H : ℂ) = Nat.card Q * Nat.card P := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (sylowCentIn p x),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe sylowCent_le_elemSub).toEquiv]
    push_cast
    rfl
  have hQ : (Nat.card Q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hP : (Nat.card P : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [indFun_apply, Finset.sum_congr rfl fun t _ ↦ hinner _, hcard, ← mul_assoc, mul_inv,
    mul_comm (Nat.card Q : ℂ)⁻¹, ← mul_assoc, mul_inv_cancel₀ hP, one_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  split_ifs
  · exact inv_mul_cancel₀ hQ
  · simp

omit [Fintype G] in

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hw`. Establish `hxw : x * (x⁻¹ * z) = (x⁻¹ * z) * x` using `(commute_of_mem_sylowCent hw).symm`. Establish `hxz : Commute x z`. Establish `h1 : Commute x (x⁻¹ * z)` using `hxw`.

Use `(Commute.refl x).mul_right h1` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel_left]`. Then use the resulting hypothesis. Establish `hcomm : Commute x⁻¹ z` using `hxz.inv_left`. Take `⟨j, hj⟩` from `(IsPGroup.iff_orderOf.mp (isPGroup_sylowCent p x)) ⟨_, hw⟩`. Rewrite `hj` using `[Subgroup.orderOf_mk]`.

Establish `hdvd` using `hcomm.orderOf_mul_dvd_lcm`. Rewrite `hdvd` using `[orderOf_inv, hj]`. Establish `hcop : (Nat.lcm (orderOf x) (orderOf z)).Coprime p` using `Nat.Coprime.coprime_dvd_left (Nat.lcm_dvd_mul _ _) (Nat.Coprime.mul_left hx hz)`. Establish `hj0 : j = 0`. Assume the negation of the conclusion as `hj0`.

Establish `: p ∣ Nat.lcm (orderOf x) (orderOf z)` using `(dvd_pow_self p hj0).trans hdvd`. Conclude with `hp.out.one_lt.ne' ((Nat.coprime_comm.mp hcop).eq_one_of_dvd this)`. Rewrite `hj` using `[hj0, pow_zero, orderOf_eq_one_iff]`. Combine the equalities or inequalities in the displayed calculation. Introduce `h`.

Rewrite using `[h, inv_mul_cancel]`. Conclude with `(sylowCent p x).one_mem`.
-/
theorem mem_sylowCent_iff (hx : (orderOf x).Coprime p) {z : G} (hz : (orderOf z).Coprime p) :
    x⁻¹ * z ∈ sylowCent p x ↔ z = x := by
  constructor
  · intro hw
    have hxw : x * (x⁻¹ * z) = (x⁻¹ * z) * x := (commute_of_mem_sylowCent hw).symm
    have hxz : Commute x z := by
      have h1 : Commute x (x⁻¹ * z) := hxw
      have := (Commute.refl x).mul_right h1
      rwa [mul_inv_cancel_left] at this
    have hcomm : Commute x⁻¹ z := hxz.inv_left
    obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp (isPGroup_sylowCent p x)) ⟨_, hw⟩
    rw [Subgroup.orderOf_mk] at hj
    have hdvd := hcomm.orderOf_mul_dvd_lcm
    rw [orderOf_inv, hj] at hdvd
    have hcop : (Nat.lcm (orderOf x) (orderOf z)).Coprime p :=
      Nat.Coprime.coprime_dvd_left (Nat.lcm_dvd_mul _ _) (Nat.Coprime.mul_left hx hz)
    have hj0 : j = 0 := by
      by_contra hj0
      have : p ∣ Nat.lcm (orderOf x) (orderOf z) :=
        (dvd_pow_self p hj0).trans hdvd
      exact hp.out.one_lt.ne' ((Nat.coprime_comm.mp hcop).eq_one_of_dvd this)
    rw [hj0, pow_zero, orderOf_eq_one_iff] at hj
    calc z = x * (x⁻¹ * z) := by group
      _ = x := by rw [hj, mul_one]
  · intro h
    rw [h, inv_mul_cancel]
    exact (sylowCent p x).one_mem

end Theta

section ThetaSpan

variable {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (Nat.card G))
  (hmono : ∀ K : Subgroup G, IsElementaryAt p K → ∀ χ : K → ℂ, IsIrrCharacter χ →
    ∃ (L : Subgroup K) (μ : L →* ℂˣ), χ = indLin L μ)

omit hp in
include hζ hmono in

/- English proof (translation)
Use `set H := elemSub p x`. Use `set Q := H ⧸ sylowCentIn p x`. Use `set xb : Q := (xIn p x : Q)`. Use `set δ : Q → ℂ := fun q ↦ if q = xb then (Nat.card Q : ℂ) else 0`. Establish `hδ : IsClassFun δ`.

Introduce `g h`. Simplify using `only [δ]`. Rewrite using `[quotient_mul_comm h g, mul_inv_cancel_right]`. Establish `hN : (Nat.card Q : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr Nat.card_pos.ne'`. Establish `hcoef : ∀ ψ : Q → ℂ, charInner Q δ ψ = ψ xb⁻¹`.

Introduce `ψ`. Rewrite using `[charInner_apply]`. Simplify using `only [δ, ite_mul, zero_mul]`. Rewrite using `[Finset.sum_ite_eq', if_pos (Finset.mem_univ _), ← mul_assoc, inv_mul_cancel₀ hN, one_mul]`. Establish `htheta : theta p x = δ ∘ QuotientGroup.mk' (sylowCentIn p x)` using `rfl`.

Rewrite using `[htheta, eq_sum_irrChars_of_isClassFun hδ]`. Establish `hcomp : (∑ ψ ∈ irrChars Q, charInner Q δ ψ • ψ) ∘ QuotientGroup.mk' (sylowCentIn p x) = ∑ ψ ∈ irrChars Q, charInner Q δ ψ • (ψ ∘ QuotientGroup.mk' (sylowCentIn p x))`. Use function extensionality and compare the values at `h`. Simplify using `[Finset.sum_apply]`. Rewrite using `[hcomp, map_sum]`.

Use `Submodule.sum_mem _ fun ψ hψ ↦ ?_` and prove the remaining obligations. Rewrite using `[map_smul, hcoef]`. Establish `hψc` using `(mem_irrChars.mp hψ).isCharacter`. Use `smul_mem_spanA ?_ (indFun_mem_spanZ (fun K L hK hLK ↦ hK.mono hLK) hmono (isElementaryAt_elemSub hx) (hψc.comp _))` and prove the remaining obligations. Establish `: NeZero (Nat.card G)` using `⟨Nat.card_pos.ne'⟩`.

Use `hψc.apply_mem_adjoin _ hζ ?_` and prove the remaining obligations. Rewrite using `[orderOf_inv]`. Use `(orderOf_map_dvd (QuotientGroup.mk' (sylowCentIn p x)) (xIn p x)).trans ?_` and prove the remaining obligations. Rewrite using `[xIn, Subgroup.orderOf_mk]`. Conclude with `orderOf_dvd_natCard x`.
-/
theorem indFun_theta_mem_spanA (hx : (orderOf x).Coprime p) :
    indFun (elemSub p x).subtype (theta p x) ∈ spanA (G := G) (IsElementaryAt p) ζ := by
  set H := elemSub p x
  set Q := H ⧸ sylowCentIn p x
  set xb : Q := (xIn p x : Q)
  set δ : Q → ℂ := fun q ↦ if q = xb then (Nat.card Q : ℂ) else 0
  have hδ : IsClassFun δ := by
    intro g h
    simp only [δ]
    rw [quotient_mul_comm h g, mul_inv_cancel_right]
  have hN : (Nat.card Q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hcoef : ∀ ψ : Q → ℂ, charInner Q δ ψ = ψ xb⁻¹ := by
    intro ψ
    rw [charInner_apply]
    simp only [δ, ite_mul, zero_mul]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _), ← mul_assoc, inv_mul_cancel₀ hN, one_mul]
  have htheta : theta p x = δ ∘ QuotientGroup.mk' (sylowCentIn p x) := rfl
  rw [htheta, eq_sum_irrChars_of_isClassFun hδ]
  have hcomp : (∑ ψ ∈ irrChars Q, charInner Q δ ψ • ψ) ∘ QuotientGroup.mk' (sylowCentIn p x) =
      ∑ ψ ∈ irrChars Q, charInner Q δ ψ • (ψ ∘ QuotientGroup.mk' (sylowCentIn p x)) := by
    funext h
    simp [Finset.sum_apply]
  rw [hcomp, map_sum]
  refine Submodule.sum_mem _ fun ψ hψ ↦ ?_
  rw [map_smul, hcoef]
  have hψc := (mem_irrChars.mp hψ).isCharacter
  refine smul_mem_spanA ?_ (indFun_mem_spanZ (fun K L hK hLK ↦ hK.mono hLK) hmono
    (isElementaryAt_elemSub hx) (hψc.comp _))
  have : NeZero (Nat.card G) := ⟨Nat.card_pos.ne'⟩
  refine hψc.apply_mem_adjoin _ hζ ?_
  rw [orderOf_inv]
  refine (orderOf_map_dvd (QuotientGroup.mk' (sylowCentIn p x)) (xIn p x)).trans ?_
  rw [xIn, Subgroup.orderOf_mk]
  exact orderOf_dvd_natCard x

omit hp in
include hζ hmono in

/- English proof (translation)
Establish `hA` using `apply_mem_adjoin_of_mem_spanA hζ (indFun_theta_mem_spanA hζ hmono hx) g`. Establish `hcount` using `card_mul_indFun_theta (p := p) (x := x) g`. Take `⟨z, hz, -⟩` from `exists_int_of_mul_eq_int (hζ.isIntegral Nat.card_pos) hA (d := Nat.card (sylowCent p x)) (k := ∑ t : G, if x⁻¹ * (t⁻¹ * g * t) ∈ sylowCent p x then 1 else 0) (Int.natCast_ne_zero.mpr Nat.card_pos.ne') (by push_cast; exact hcount)`. Conclude with `⟨z, hz⟩`.
-/
theorem exists_int_indFun_theta (hx : (orderOf x).Coprime p) (g : G) :
    ∃ k : ℤ, indFun (elemSub p x).subtype (theta p x) g = k := by
  have hA := apply_mem_adjoin_of_mem_spanA hζ (indFun_theta_mem_spanA hζ hmono hx) g
  have hcount := card_mul_indFun_theta (p := p) (x := x) g
  obtain ⟨z, hz, -⟩ := exists_int_of_mul_eq_int (hζ.isIntegral Nat.card_pos) hA
    (d := Nat.card (sylowCent p x)) (k := ∑ t : G, if x⁻¹ * (t⁻¹ * g * t) ∈ sylowCent p x then 1 else 0)
    (Int.natCast_ne_zero.mpr Nat.card_pos.ne') (by push_cast; exact hcount)
  exact ⟨z, hz⟩

end ThetaSpan

section Count

/- English proof (translation)
Rewrite using `[card_mul_indFun_theta]`. Use `Finset.sum_congr rfl fun t _ ↦ ?_` and prove the remaining obligations. Establish `ht : (orderOf (t⁻¹ * g * t)).Coprime p`. Establish `: t⁻¹ * g * t = (MulAut.conj t⁻¹) g` using `by simp`. Rewrite using `[this, MulEquiv.orderOf_eq]`.

Conclude with `hg`. Distinguish the cases in `h : t⁻¹ * g * t = x`. Rewrite using `[if_pos h, if_pos ((mem_sylowCent_iff hx ht).mpr h)]`. Rewrite using `[if_neg h, if_neg fun h' ↦ h ((mem_sylowCent_iff hx ht).mp h')]`.
-/
theorem card_mul_indFun_theta_of_coprime (hx : (orderOf x).Coprime p) {g : G}
    (hg : (orderOf g).Coprime p) :
    (Nat.card (sylowCent p x) : ℂ) * indFun (elemSub p x).subtype (theta p x) g =
      ∑ t : G, if t⁻¹ * g * t = x then 1 else 0 := by
  rw [card_mul_indFun_theta]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  have ht : (orderOf (t⁻¹ * g * t)).Coprime p := by
    have : t⁻¹ * g * t = (MulAut.conj t⁻¹) g := by simp
    rw [this, MulEquiv.orderOf_eq]
    exact hg
  by_cases h : t⁻¹ * g * t = x
  · rw [if_pos h, if_pos ((mem_sylowCent_iff hx ht).mpr h)]
  · rw [if_neg h, if_neg fun h' ↦ h ((mem_sylowCent_iff hx ht).mp h')]

omit [Fintype G] hp in
/- English proof (translation)
Take `⟨u, hu⟩` from `isConj_iff.mp hc`. Rewrite using `[← hu]`. Rewrite using `[Fintype.sum_equiv (Equiv.mulLeft u⁻¹) _ (fun t ↦ if t ∈ Subgroup.centralizer {x} then (1 : ℂ) else 0) (fun t ↦ ?_)]`. Rewrite using `[Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]`. Simplify using `only [Equiv.coe_mulLeft, Subgroup.mem_centralizer_singleton_iff]`.

Use `congr 1`. Apply `propext` to reduce the goal to its premises. Prove the components needed by the constructor for the conclusion. Introduce `h`. Combine the equalities or inequalities in the displayed calculation.

Introduce `h`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem sum_conj_eq_card_centralizer [Fintype G] {g : G} (hc : IsConj x g) :
    (∑ t : G, if t⁻¹ * g * t = x then (1 : ℂ) else 0) = Nat.card (Subgroup.centralizer {x}) := by
  obtain ⟨u, hu⟩ := isConj_iff.mp hc
  rw [← hu]
  rw [Fintype.sum_equiv (Equiv.mulLeft u⁻¹) _ (fun t ↦ if t ∈ Subgroup.centralizer {x} then (1 : ℂ) else 0)
    (fun t ↦ ?_)]
  · rw [Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]
  · simp only [Equiv.coe_mulLeft, Subgroup.mem_centralizer_singleton_iff]
    congr 1
    apply propext
    constructor
    · intro h
      calc u⁻¹ * t * x = u⁻¹ * (t * (t⁻¹ * (u * x * u⁻¹) * t)) := by rw [h]; group
        _ = x * (u⁻¹ * t) := by group
    · intro h
      calc t⁻¹ * (u * x * u⁻¹) * t = t⁻¹ * u * (x * (u⁻¹ * t)) := by group
        _ = t⁻¹ * u * (u⁻¹ * t * x) := by rw [h]
        _ = x := by group

omit [Fintype G] hp in
/- English proof (translation)
Use `Finset.sum_eq_zero fun t _ ↦ if_neg fun h ↦ hc ?_` and prove the remaining obligations. Rewrite using `[isConj_iff]`. Conclude with `⟨t, by rw [← h]; group⟩`.
-/
theorem sum_conj_eq_zero [Fintype G] {g : G} (hc : ¬ IsConj x g) :
    (∑ t : G, if t⁻¹ * g * t = x then (1 : ℂ) else 0) = 0 := by
  refine Finset.sum_eq_zero fun t _ ↦ if_neg fun h ↦ hc ?_
  rw [isConj_iff]
  exact ⟨t, by rw [← h]; group⟩

end Count

section Main

def classRep (c : ConjClasses G) : G := Classical.choose c.exists_rep

omit [Fintype G] hp in
/- English proof (translation)
The claim follows from `Classical.choose_spec c.exists_rep`.
-/
theorem mk_classRep (c : ConjClasses G) : ConjClasses.mk (classRep c) = c :=
  Classical.choose_spec c.exists_rep

variable (p) in

def brauerFun : G → ℂ := ∑ c : ConjClasses G,
  if (orderOf (classRep c)).Coprime p then
    indFun (elemSub p (classRep c)).subtype (theta p (classRep c)) else 0

variable {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (Nat.card G))
  (hmono : ∀ K : Subgroup G, IsElementaryAt p K → ∀ χ : K → ℂ, IsIrrCharacter χ →
    ∃ (L : Subgroup K) (μ : L →* ℂˣ), χ = indLin L μ)
include hζ hmono

omit hp in
/- English proof (translation)
Use `Submodule.sum_mem _ fun c _ ↦ ?_` and prove the remaining obligations. Use `split_ifs with h`. Conclude with `indFun_theta_mem_spanA hζ hmono h`. Conclude with `Submodule.zero_mem _`.
-/
theorem brauerFun_mem_spanA : brauerFun p ∈ spanA (G := G) (IsElementaryAt p) ζ := by
  refine Submodule.sum_mem _ fun c _ ↦ ?_
  split_ifs with h
  · exact indFun_theta_mem_spanA hζ hmono h
  · exact Submodule.zero_mem _

omit hp in
/- English proof (translation)
Establish `h : ∀ c : ConjClasses G, ∃ k : ℤ, (if (orderOf (classRep c)).Coprime p then indFun (elemSub p (classRep c)).subtype (theta p (classRep c)) else 0) g = k`. Introduce `c`. Use `split_ifs with h`. Conclude with `exists_int_indFun_theta hζ hmono h g`. Conclude with `⟨0, by simp⟩`.

Use `choose k hk using h`. Use `⟨∑ c, k c, ?_⟩` and prove the remaining obligations. Rewrite using `[brauerFun, Finset.sum_apply]`. Use `push_cast`. Conclude with `Finset.sum_congr rfl fun c _ ↦ hk c`.
-/
theorem exists_int_brauerFun (g : G) : ∃ k : ℤ, brauerFun p g = k := by
  have h : ∀ c : ConjClasses G, ∃ k : ℤ, (if (orderOf (classRep c)).Coprime p then
      indFun (elemSub p (classRep c)).subtype (theta p (classRep c)) else 0) g = k := by
    intro c
    split_ifs with h
    · exact exists_int_indFun_theta hζ hmono h g
    · exact ⟨0, by simp⟩
  choose k hk using h
  refine ⟨∑ c, k c, ?_⟩
  rw [brauerFun, Finset.sum_apply]
  push_cast
  exact Finset.sum_congr rfl fun c _ ↦ hk c

omit hζ hmono in

/- English proof (translation)
Use `set c0 := ConjClasses.mk y`. Use `set x := classRep c0`. Establish `hxy : IsConj x y` using `ConjClasses.mk_eq_mk_iff_isConj.mp (mk_classRep c0)`. Establish `hx : (orderOf x).Coprime p`. Take `⟨u, hu⟩` from `isConj_iff.mp hxy`.

Rewrite using `[show x = (MulAut.conj u⁻¹) y by rw [MulAut.conj_apply, ← hu]; group, MulEquiv.orderOf_eq]`. Conclude with `hy`. Take `⟨m, hm, hpm⟩` from `exists_card_centralizer_eq p x`. Use `⟨m, ?_, hpm⟩` and prove the remaining obligations. Rewrite using `[brauerFun, Finset.sum_apply, Finset.sum_eq_single c0]`.

Rewrite using `[if_pos hx]`. Establish `h` using `card_mul_indFun_theta_of_coprime hx hy`. Rewrite `h` using `[sum_conj_eq_card_centralizer hxy, hm]`. Establish `hP : (Nat.card (sylowCent p x) : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr Nat.card_pos.ne'`. Move the coercions through the operations in `at h`.

Conclude with `mul_left_cancel₀ hP h`. Introduce `c _ hc split_ifs with hxc`. Establish `h` using `card_mul_indFun_theta_of_coprime hxc hy`. Establish `hnc : ¬ IsConj (classRep c) y`. Introduce `hcj`.

Apply `hc` to reduce the goal to its premises. Rewrite using `[← mk_classRep c]`. Conclude with `ConjClasses.mk_eq_mk_iff_isConj.mpr hcj`. Rewrite `h` using `[sum_conj_eq_zero hnc]`. Establish `hP : (Nat.card (sylowCent p (classRep c)) : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr Nat.card_pos.ne'`.

Conclude with `(mul_eq_zero.mp h).resolve_left hP`. Simplify using the standard rewrite rules. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem brauerFun_of_coprime {y : G} (hy : (orderOf y).Coprime p) :
    ∃ m : ℕ, brauerFun p y = m ∧ ¬ p ∣ m := by
  set c0 := ConjClasses.mk y
  set x := classRep c0
  have hxy : IsConj x y := ConjClasses.mk_eq_mk_iff_isConj.mp (mk_classRep c0)
  have hx : (orderOf x).Coprime p := by
    obtain ⟨u, hu⟩ := isConj_iff.mp hxy
    rw [show x = (MulAut.conj u⁻¹) y by rw [MulAut.conj_apply, ← hu]; group, MulEquiv.orderOf_eq]
    exact hy
  obtain ⟨m, hm, hpm⟩ := exists_card_centralizer_eq p x
  refine ⟨m, ?_, hpm⟩
  rw [brauerFun, Finset.sum_apply, Finset.sum_eq_single c0]
  · rw [if_pos hx]
    have h := card_mul_indFun_theta_of_coprime hx hy
    rw [sum_conj_eq_card_centralizer hxy, hm] at h
    have hP : (Nat.card (sylowCent p x) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    push_cast at h
    exact mul_left_cancel₀ hP h
  · intro c _ hc
    split_ifs with hxc
    · have h := card_mul_indFun_theta_of_coprime hxc hy
      have hnc : ¬ IsConj (classRep c) y := by
        intro hcj
        apply hc
        rw [← mk_classRep c]
        exact ConjClasses.mk_eq_mk_iff_isConj.mpr hcj
      rw [sum_conj_eq_zero hnc] at h
      have hP : (Nat.card (sylowCent p (classRep c)) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
      exact (mul_eq_zero.mp h).resolve_left hP
    · simp
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Take `⟨a, b, hab, ha, hb⟩` from `exists_zpow_mul_zpow_eq hp.out s`. Take `⟨k, hk⟩` from `exists_int_brauerFun hζ hmono s`. Take `⟨m, hm, hpm⟩` from `brauerFun_of_coprime ha`. Use `⟨k, hk, fun hdiv ↦ hpm ?_⟩` and prove the remaining obligations. Establish `hcong` using `int_modEq_of_mem_spanA hζ hp.out hab hb (brauerFun_mem_spanA hζ hmono) hk (v := (m : ℤ)) (by rw [hm]; push_cast; rfl)`.

Rewrite `hcong` using `[(ZMod.intCast_zmod_eq_zero_iff_dvd k p).mpr hdiv]`. Establish `h0` using `(ZMod.intCast_zmod_eq_zero_iff_dvd (m : ℤ) p).mp hcong.symm`. Conclude with `Int.natCast_dvd_natCast.mp h0`.
-/
theorem not_dvd_brauerFun (s : G) : ∃ k : ℤ, brauerFun p s = k ∧ ¬ (p : ℤ) ∣ k := by
  obtain ⟨a, b, hab, ha, hb⟩ := exists_zpow_mul_zpow_eq hp.out s
  obtain ⟨k, hk⟩ := exists_int_brauerFun hζ hmono s
  obtain ⟨m, hm, hpm⟩ := brauerFun_of_coprime ha
  refine ⟨k, hk, fun hdiv ↦ hpm ?_⟩
  have hcong := int_modEq_of_mem_spanA hζ hp.out hab hb (brauerFun_mem_spanA hζ hmono) hk
    (v := (m : ℤ)) (by rw [hm]; push_cast; rfl)
  rw [(ZMod.intCast_zmod_eq_zero_iff_dvd k p).mpr hdiv] at hcong
  have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd (m : ℤ) p).mp hcong.symm
  exact Int.natCast_dvd_natCast.mp h0

/- English proof (translation)
Establish `hE : ∀ K L : Subgroup G, IsElementaryAt p K → L ≤ K → IsElementaryAt p L` using `fun K L hK hLK ↦ hK.mono hLK`. Establish `hcyc : ∀ s : G, IsElementaryAt p (Subgroup.zpowers s)` using `fun s ↦ isElementaryAt_zpowers hp.out s`. Use `set n := Nat.card G`. Use `set e := n.factorization p`. Use `set q := p ^ e`.

Use `set m := n / q`. Establish `hn : q * m = n` using `Nat.ordProj_mul_ordCompl_eq_self n p`. Use `set M := Nat.totient q`. Establish `hq0 : 0 < q` using `pow_pos hp.out.pos e`. Establish `hM : M ≠ 0` using `(Nat.totient_pos.mpr hq0).ne'`.

Establish `: NeZero q` using `⟨hq0.ne'⟩`. Use `set f : G → ℂ := brauerFun p`. Establish `hfA : f ∈ spanA (G` using `G) (IsElementaryAt p) ζ := brauerFun_mem_spanA hζ hmono`. Establish `hval : ∀ s, ∃ j : ℤ, (f ^ M - 1) s = (q : ℂ) * j`. Introduce `s`.

Take `⟨k, hk, hpk⟩` from `not_dvd_brauerFun hζ hmono s`. Establish `hcop : Nat.Coprime k.natAbs q` using `Nat.Coprime.pow_right e ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr fun h ↦ hpk (Int.natCast_dvd.mpr h)).symm`. Establish `hunit : IsUnit (k : ZMod q)`. Break down `Int.natAbs_eq k with h | h` into its components or cases. Rewrite using `[h, Int.cast_natCast]`.

Conclude with `(ZMod.isUnit_iff_coprime _ _).mpr hcop`. Rewrite using `[h, Int.cast_neg, Int.cast_natCast]`. Conclude with `((ZMod.isUnit_iff_coprime _ _).mpr hcop).neg`. Establish `hpow : ((k ^ M - 1 : ℤ) : ZMod q) = 0`. Establish `h2 : (k : ZMod q) ^ M = 1`.

Use `congrArg Units.val (ZMod.pow_totient hunit.unit)` as an intermediate fact. Rewrite `this` using `[Units.val_pow_eq_pow_val, IsUnit.unit_spec, Units.val_one]`. Then use the resulting hypothesis. Use `push_cast`. Rewrite using `[h2, sub_self]`. Take `⟨j, hj⟩` from `(ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp hpow`.

Use `⟨j, ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.sub_apply, Pi.pow_apply, Pi.one_apply]`. Rewrite using `[show f s = (k : ℂ) from hk, show ((k : ℂ) ^ M - 1) = ((k ^ M - 1 : ℤ) : ℂ) by push_cast; ring, hj]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hcl : IsClassFun f` using `isClassFun_of_mem_spanA hfA`. Establish `hF1 : ((m : ℤ) • (f ^ M - 1)) ∈ spanA (G` using `G) (IsElementaryAt p) ζ := by`. Apply `mem_spanA_of_dvd hE hmono hcyc hζ` to reduce the goal to its premises. Introduce `g h`. Simplify using `[hcl g h]`.

Introduce `g`. Take `⟨j, hj⟩` from `hval g`. Use `⟨j, ?_⟩` and prove the remaining obligations. Establish `hn' : (Nat.card G : ℂ) = q * m` using `by exact_mod_cast hn.symm`. Rewrite using `[Pi.smul_apply, hj, zsmul_eq_mul, hn']`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hfM` using `pow_mem_spanA hE hmono hfA hM`. Establish `h1 : ((m : ℤ) • (1 : G → ℂ)) = (m : ℤ) • f ^ M - (m : ℤ) • (f ^ M - 1)`. Rewrite using `[smul_sub]`.

Normalize the expressions using the abelian group laws. Establish `hA1 : ((m : ℤ) • (1 : G → ℂ)) ∈ spanA (G` using `G) (IsElementaryAt p) ζ := by`. Rewrite using `[h1]`. Conclude with `Submodule.sub_mem _ (Submodule.smul_mem _ _ hfM) hF1`. Use `⟨m, Nat.not_dvd_ordCompl hp.out Nat.card_pos.ne', ?_⟩` and prove the remaining obligations.

Apply `mem_spanZ_of_mem_spanA (hζ.isIntegral Nat.card_pos) hA1` to reduce the goal to its premises. Introduce `ψ hψ`. Take `⟨j, hj⟩` from `isCharacter_one.exists_nat_charInner (mem_irrChars.mp hψ).isCharacter`. Use `⟨m * j, ?_⟩` and prove the remaining obligations. Rewrite using `[map_zsmul, LinearMap.smul_apply, hj, zsmul_eq_mul]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_smul_one_mem_spanZ :
    ∃ m : ℕ, ¬ p ∣ m ∧ ((m : ℤ) • (1 : G → ℂ)) ∈ spanZ (IsElementaryAt p) := by
  have hE : ∀ K L : Subgroup G, IsElementaryAt p K → L ≤ K → IsElementaryAt p L :=
    fun K L hK hLK ↦ hK.mono hLK
  have hcyc : ∀ s : G, IsElementaryAt p (Subgroup.zpowers s) := fun s ↦ isElementaryAt_zpowers hp.out s
  set n := Nat.card G
  set e := n.factorization p
  set q := p ^ e
  set m := n / q
  have hn : q * m = n := Nat.ordProj_mul_ordCompl_eq_self n p
  set M := Nat.totient q
  have hq0 : 0 < q := pow_pos hp.out.pos e
  have hM : M ≠ 0 := (Nat.totient_pos.mpr hq0).ne'
  have : NeZero q := ⟨hq0.ne'⟩
  set f : G → ℂ := brauerFun p
  have hfA : f ∈ spanA (G := G) (IsElementaryAt p) ζ := brauerFun_mem_spanA hζ hmono
  have hval : ∀ s, ∃ j : ℤ, (f ^ M - 1) s = (q : ℂ) * j := by
    intro s
    obtain ⟨k, hk, hpk⟩ := not_dvd_brauerFun hζ hmono s
    have hcop : Nat.Coprime k.natAbs q := Nat.Coprime.pow_right e
      ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr fun h ↦ hpk (Int.natCast_dvd.mpr h)).symm
    have hunit : IsUnit (k : ZMod q) := by
      rcases Int.natAbs_eq k with h | h
      · rw [h, Int.cast_natCast]
        exact (ZMod.isUnit_iff_coprime _ _).mpr hcop
      · rw [h, Int.cast_neg, Int.cast_natCast]
        exact ((ZMod.isUnit_iff_coprime _ _).mpr hcop).neg
    have hpow : ((k ^ M - 1 : ℤ) : ZMod q) = 0 := by
      have h2 : (k : ZMod q) ^ M = 1 := by
        have := congrArg Units.val (ZMod.pow_totient hunit.unit)
        rwa [Units.val_pow_eq_pow_val, IsUnit.unit_spec, Units.val_one] at this
      push_cast
      rw [h2, sub_self]
    obtain ⟨j, hj⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp hpow
    refine ⟨j, ?_⟩
    simp only [Pi.sub_apply, Pi.pow_apply, Pi.one_apply]
    rw [show f s = (k : ℂ) from hk, show ((k : ℂ) ^ M - 1) = ((k ^ M - 1 : ℤ) : ℂ) by push_cast; ring, hj]
    push_cast
    ring
  have hcl : IsClassFun f := isClassFun_of_mem_spanA hfA
  have hF1 : ((m : ℤ) • (f ^ M - 1)) ∈ spanA (G := G) (IsElementaryAt p) ζ := by
    apply mem_spanA_of_dvd hE hmono hcyc hζ
    · intro g h
      simp [hcl g h]
    · intro g
      obtain ⟨j, hj⟩ := hval g
      refine ⟨j, ?_⟩
      have hn' : (Nat.card G : ℂ) = q * m := by exact_mod_cast hn.symm
      rw [Pi.smul_apply, hj, zsmul_eq_mul, hn']
      push_cast
      ring
  have hfM := pow_mem_spanA hE hmono hfA hM
  have h1 : ((m : ℤ) • (1 : G → ℂ)) = (m : ℤ) • f ^ M - (m : ℤ) • (f ^ M - 1) := by
    rw [smul_sub]
    abel
  have hA1 : ((m : ℤ) • (1 : G → ℂ)) ∈ spanA (G := G) (IsElementaryAt p) ζ := by
    rw [h1]
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hfM) hF1
  refine ⟨m, Nat.not_dvd_ordCompl hp.out Nat.card_pos.ne', ?_⟩
  apply mem_spanZ_of_mem_spanA (hζ.isIntegral Nat.card_pos) hA1
  intro ψ hψ
  obtain ⟨j, hj⟩ := isCharacter_one.exists_nat_charInner (mem_irrChars.mp hψ).isCharacter
  refine ⟨m * j, ?_⟩
  rw [map_zsmul, LinearMap.smul_apply, hj, zsmul_eq_mul]
  push_cast
  ring

end Main

end GroundTheory.LocalField
