import Mathlib

noncomputable section

namespace GroundTheory.LocalField

variable {G : Type*} [Group G]

def IsElementaryAt (p : ℕ) (H : Subgroup G) : Prop :=
  ∃ C P : Subgroup G, C ≤ H ∧ P ≤ H ∧ IsCyclic C ∧ (Nat.card C).Coprime p ∧ IsPGroup p P ∧
    (∀ c ∈ C, ∀ y ∈ P, c * y = y * c) ∧ ∀ h ∈ H, ∃ c ∈ C, ∃ y ∈ P, h = c * y

def IsElementary (H : Subgroup G) : Prop := ∃ p : ℕ, p.Prime ∧ IsElementaryAt p H

variable [Finite G] {p : ℕ}

/- English proof (translation)
Use `set o := orderOf s`. Establish `ho : o ≠ 0` using `(orderOf_pos s).ne'`. Use `set k := o.factorization p`. Use `set r := o / p ^ k`. Establish `hor : p ^ k * r = o` using `Nat.ordProj_mul_ordCompl_eq_self o p`.

Establish `hr : r.Coprime p` using `(Nat.coprime_ordCompl hp ho).symm`. Establish `hcop : IsCoprime ((p ^ k : ℕ) : ℤ) (r : ℤ)` using `Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.pow_left k hr.symm)`. Take `⟨u, v, huv⟩` from `hcop`. Establish `hso : s ^ (o : ℤ) = 1` using `by rw [zpow_natCast, pow_orderOf_eq_one]`. Use `⟨u * (p ^ k : ℕ), v * r, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← zpow_add, huv, zpow_one]`. Establish `h1 : (s ^ (u * (p ^ k : ℕ) : ℤ)) ^ r = 1`. Rewrite using `[← zpow_natCast, ← zpow_mul, show u * ((p ^ k : ℕ) : ℤ) * (r : ℤ) = u * (o : ℤ) by`. Rewrite using `[← hor]`. Use `push_cast`.

Use the proof step `ring, zpow_mul', hso, one_zpow]`. Conclude with `Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one h1) hr`. Rewrite using `[← zpow_natCast, ← zpow_mul, show v * (r : ℤ) * ((p ^ k : ℕ) : ℤ) = v * (o : ℤ) by`. Rewrite using `[← hor]`. Use `push_cast`.

Use the proof step `ring, zpow_mul', hso, one_zpow]`.
-/
theorem exists_zpow_mul_zpow_eq (hp : p.Prime) (s : G) :
    ∃ a b : ℤ, s ^ a * s ^ b = s ∧ (orderOf (s ^ a)).Coprime p ∧
      (s ^ b) ^ (p ^ (orderOf s).factorization p) = 1 := by
  set o := orderOf s
  have ho : o ≠ 0 := (orderOf_pos s).ne'
  set k := o.factorization p
  set r := o / p ^ k
  have hor : p ^ k * r = o := Nat.ordProj_mul_ordCompl_eq_self o p
  have hr : r.Coprime p := (Nat.coprime_ordCompl hp ho).symm
  have hcop : IsCoprime ((p ^ k : ℕ) : ℤ) (r : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.pow_left k hr.symm)
  obtain ⟨u, v, huv⟩ := hcop
  have hso : s ^ (o : ℤ) = 1 := by rw [zpow_natCast, pow_orderOf_eq_one]
  refine ⟨u * (p ^ k : ℕ), v * r, ?_, ?_, ?_⟩
  · rw [← zpow_add, huv, zpow_one]
  · have h1 : (s ^ (u * (p ^ k : ℕ) : ℤ)) ^ r = 1 := by
      rw [← zpow_natCast, ← zpow_mul, show u * ((p ^ k : ℕ) : ℤ) * (r : ℤ) = u * (o : ℤ) by
        rw [← hor]; push_cast; ring, zpow_mul', hso, one_zpow]
    exact Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one h1) hr
  · rw [← zpow_natCast, ← zpow_mul, show v * (r : ℤ) * ((p ^ k : ℕ) : ℤ) = v * (o : ℤ) by
      rw [← hor]; push_cast; ring, zpow_mul', hso, one_zpow]

/- English proof (translation)
Take `⟨a, b, hab, ha, hb⟩` from `exists_zpow_mul_zpow_eq hp s`. Use `⟨Subgroup.zpowers (s ^ a), Subgroup.zpowers (s ^ b), ?_, ?_, inferInstance, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Subgroup.zpowers_le]`. Conclude with `Subgroup.zpow_mem_zpowers s a`. Rewrite using `[Subgroup.zpowers_le]`.

Conclude with `Subgroup.zpow_mem_zpowers s b`. Rewrite using `[Nat.card_zpowers]` and apply the resulting hypothesis. Introduce `g`. Take `⟨m, hm⟩` from `Subgroup.mem_zpowers_iff.mp g.2`. Use `⟨(orderOf s).factorization p, ?_⟩` and prove the remaining obligations.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [Subgroup.coe_pow, OneMemClass.coe_one]`. Rewrite using `[← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb, one_zpow]`. Introduce `c hc y hy`. Take `⟨i, rfl⟩` from `Subgroup.mem_zpowers_iff.mp hc`.

Take `⟨j, rfl⟩` from `Subgroup.mem_zpowers_iff.mp hy`. Rewrite using `[← zpow_mul, ← zpow_mul, ← zpow_add, ← zpow_add, add_comm]`. Introduce `h hh`. Take `⟨m, rfl⟩` from `Subgroup.mem_zpowers_iff.mp hh`. Use `⟨(s ^ a) ^ m, Subgroup.zpow_mem_zpowers _ m, (s ^ b) ^ m, Subgroup.zpow_mem_zpowers _ m, ?_⟩` and prove the remaining obligations.

Establish `hab' : s ^ (a + b) = s` using `by rw [zpow_add, hab]`. Rewrite using `[← zpow_mul, ← zpow_mul, ← zpow_add, ← add_mul, zpow_mul, hab']`.
-/
theorem isElementaryAt_zpowers (hp : p.Prime) (s : G) : IsElementaryAt p (Subgroup.zpowers s) := by
  obtain ⟨a, b, hab, ha, hb⟩ := exists_zpow_mul_zpow_eq hp s
  refine ⟨Subgroup.zpowers (s ^ a), Subgroup.zpowers (s ^ b), ?_, ?_, inferInstance, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.zpowers_le]
    exact Subgroup.zpow_mem_zpowers s a
  · rw [Subgroup.zpowers_le]
    exact Subgroup.zpow_mem_zpowers s b
  · rwa [Nat.card_zpowers]
  · intro g
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp g.2
    refine ⟨(orderOf s).factorization p, ?_⟩
    apply Subtype.ext
    simp only [Subgroup.coe_pow, OneMemClass.coe_one]
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb, one_zpow]
  · intro c hc y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← zpow_mul, ← zpow_mul, ← zpow_add, ← zpow_add, add_comm]
  · intro h hh
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    refine ⟨(s ^ a) ^ m, Subgroup.zpow_mem_zpowers _ m, (s ^ b) ^ m, Subgroup.zpow_mem_zpowers _ m, ?_⟩
    have hab' : s ^ (a + b) = s := by rw [zpow_add, hab]
    rw [← zpow_mul, ← zpow_mul, ← zpow_add, ← add_mul, zpow_mul, hab']

omit [Finite G] in

/- English proof (translation)
Take `⟨C, P, hCH, hPH, hC, hCp, hP, hcomm, hdec⟩` from `hH`. Use `⟨L ⊓ C, L ⊓ P, inf_le_left, inf_le_left, Subgroup.isCyclic_of_le inf_le_right, ?_, hP.to_le inf_le_right, fun c hc y hy ↦ hcomm c hc.2 y hy.2, ?_⟩` and prove the remaining obligations. Conclude with `Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le inf_le_right) hCp`. Introduce `l hl`. Take `⟨c, hc, y, hy, rfl⟩` from `hdec l (hLH hl)`.

Take `⟨j, hj⟩` from `hP ⟨y, hy⟩`. Establish `hyj : y ^ p ^ j = 1`. Use `congrArg Subtype.val hj` as an intermediate fact. Simplify using `using this`. Establish `hoc : orderOf c ∣ Nat.card C`.

Rewrite using `[← Subgroup.orderOf_mk c hc]`. Conclude with `orderOf_dvd_natCard _`. Establish `hcop : (orderOf c).Coprime (p ^ j)` using `Nat.Coprime.pow_right j (Nat.Coprime.coprime_dvd_left hoc hCp)`. Take `⟨u, v, huv⟩` from `Nat.isCoprime_iff_coprime.mpr hcop`. Establish `hcy : Commute c y` using `hcomm c hc y hy`.

Establish `hpow : (c * y) ^ (v * ((p ^ j : ℕ) : ℤ)) = c`. Rewrite using `[hcy.mul_zpow, zpow_mul' y, zpow_natCast y, hyj, one_zpow, mul_one, show v * ((p ^ j : ℕ) : ℤ) = 1 - u * (orderOf c : ℤ) by rw [← huv]; ring, zpow_sub, zpow_one, zpow_mul', zpow_natCast c, pow_orderOf_eq_one, one_zpow, inv_one, mul_one]`. Establish `hcL : c ∈ L` using `hpow ▸ L.zpow_mem hl _`. Establish `hyL : y ∈ L`. Use `L.mul_mem (L.inv_mem hcL) hl` as an intermediate fact.

Rewrite `this` using `[inv_mul_cancel_left]`. Then use the resulting hypothesis. Conclude with `⟨c, ⟨hcL, hc⟩, y, ⟨hyL, hy⟩, rfl⟩`.
-/
theorem IsElementaryAt.mono {H L : Subgroup G} (hH : IsElementaryAt p H) (hLH : L ≤ H) :
    IsElementaryAt p L := by
  obtain ⟨C, P, hCH, hPH, hC, hCp, hP, hcomm, hdec⟩ := hH
  refine ⟨L ⊓ C, L ⊓ P, inf_le_left, inf_le_left, Subgroup.isCyclic_of_le inf_le_right, ?_,
    hP.to_le inf_le_right, fun c hc y hy ↦ hcomm c hc.2 y hy.2, ?_⟩
  · exact Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le inf_le_right) hCp
  · intro l hl
    obtain ⟨c, hc, y, hy, rfl⟩ := hdec l (hLH hl)
    obtain ⟨j, hj⟩ := hP ⟨y, hy⟩
    have hyj : y ^ p ^ j = 1 := by
      have := congrArg Subtype.val hj
      simpa using this
    have hoc : orderOf c ∣ Nat.card C := by
      rw [← Subgroup.orderOf_mk c hc]
      exact orderOf_dvd_natCard _
    have hcop : (orderOf c).Coprime (p ^ j) :=
      Nat.Coprime.pow_right j (Nat.Coprime.coprime_dvd_left hoc hCp)
    obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop
    have hcy : Commute c y := hcomm c hc y hy
    have hpow : (c * y) ^ (v * ((p ^ j : ℕ) : ℤ)) = c := by
      rw [hcy.mul_zpow, zpow_mul' y, zpow_natCast y, hyj, one_zpow, mul_one,
        show v * ((p ^ j : ℕ) : ℤ) = 1 - u * (orderOf c : ℤ) by rw [← huv]; ring, zpow_sub, zpow_one,
        zpow_mul', zpow_natCast c, pow_orderOf_eq_one, one_zpow, inv_one, mul_one]
    have hcL : c ∈ L := hpow ▸ L.zpow_mem hl _
    have hyL : y ∈ L := by
      have := L.mul_mem (L.inv_mem hcL) hl
      rwa [inv_mul_cancel_left] at this
    exact ⟨c, ⟨hcL, hc⟩, y, ⟨hyL, hy⟩, rfl⟩

/- English proof (translation)
Take `⟨C, P, hCH, hPH, hC, hCp, hP, hcomm, hdec⟩` from `hH`. Establish `: Fact p.Prime` using `⟨hp⟩`. Set `C' : Subgroup H` to `C.subgroupOf H`. Establish `hCcomm : ∀ c ∈ C, ∀ c' ∈ C, c * c' = c' * c`. Introduce `c hc c' hc'`.

Use `hC.commGroup.mul_comm ⟨c, hc⟩ ⟨c', hc'⟩` as an intermediate fact. Conclude with `congrArg Subtype.val this`. Establish `hcent : C' ≤ Subgroup.center H`. Introduce `c hc`. Rewrite using `[Subgroup.mem_center_iff]`.

Introduce `h`. Take `⟨c0, hc0, y0, hy0, hh⟩` from `hdec h h.2`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [Subgroup.coe_mul]`. Rewrite using `[hh]`.

Establish `hc' : (c : G) ∈ C` using `hc`. Establish `key : (c : G) * (c0 * y0) = (c0 * y0) * c`. Rewrite using `[← mul_assoc, hCcomm c hc' c0 hc0, mul_assoc, hcomm c hc' y0 hy0, mul_assoc]`. Use `first`. Consider the case `exact key`.

Consider the case `exact key.symm`. Establish `hnorm : C'.Normal` using `⟨fun n hn g ↦ by`. Use `Subgroup.mem_center_iff.mp (hcent hn) g` as an intermediate fact. Rewrite using `[this, mul_inv_cancel_right]`. Conclude with `hn⟩`.

Establish `hQ : IsPGroup p (H ⧸ C')`. Introduce `q`. Take `⟨h, rfl⟩` from `QuotientGroup.mk_surjective q`. Take `⟨c0, hc0, y0, hy0, hh⟩` from `hdec h h.2`. Take `⟨j, hj⟩` from `hP ⟨y0, hy0⟩`.

Use `⟨j, ?_⟩` and prove the remaining obligations. Establish `hyj : y0 ^ p ^ j = 1` using `by simpa using congrArg Subtype.val hj`. Establish `hmk : (QuotientGroup.mk h : H ⧸ C') = QuotientGroup.mk ⟨y0, hPH hy0⟩`. Rewrite using `[QuotientGroup.eq]`. Express the relevant statement in the definitionally equal form `((h⁻¹ * ⟨y0, hPH hy0⟩ : H) : G) ∈ C`.

Simplify using `only [Subgroup.coe_mul, Subgroup.coe_inv]`. Rewrite using `[hh, mul_inv_rev, mul_assoc, hcomm _ (C.inv_mem hc0) y0 hy0, inv_mul_cancel_left]`. Conclude with `C.inv_mem hc0`. Rewrite using `[hmk, ← QuotientGroup.mk_pow]`. Establish `: (⟨y0, hPH hy0⟩ : H) ^ p ^ j = 1` using `Subtype.ext (by simpa using hyj)`.

Rewrite using `[this, QuotientGroup.mk_one]`. Establish `hnil : Group.IsNilpotent (H ⧸ C')` using `hQ.isNilpotent`. Conclude with `Subgroup.isNilpotent_of_ker_le_center (QuotientGroup.mk' C') (by rw [QuotientGroup.ker_mk']; exact hcent)`.
-/
theorem IsElementaryAt.isNilpotent (hp : p.Prime) {H : Subgroup G} (hH : IsElementaryAt p H) :
    Group.IsNilpotent H := by
  obtain ⟨C, P, hCH, hPH, hC, hCp, hP, hcomm, hdec⟩ := hH
  have : Fact p.Prime := ⟨hp⟩
  let C' : Subgroup H := C.subgroupOf H
  have hCcomm : ∀ c ∈ C, ∀ c' ∈ C, c * c' = c' * c := by
    intro c hc c' hc'
    have := hC.commGroup.mul_comm ⟨c, hc⟩ ⟨c', hc'⟩
    exact congrArg Subtype.val this
  have hcent : C' ≤ Subgroup.center H := by
    intro c hc
    rw [Subgroup.mem_center_iff]
    intro h
    obtain ⟨c0, hc0, y0, hy0, hh⟩ := hdec h h.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [hh]
    have hc' : (c : G) ∈ C := hc
    have key : (c : G) * (c0 * y0) = (c0 * y0) * c := by
      rw [← mul_assoc, hCcomm c hc' c0 hc0, mul_assoc, hcomm c hc' y0 hy0, mul_assoc]
    first
    | exact key
    | exact key.symm
  have hnorm : C'.Normal := ⟨fun n hn g ↦ by
    have := Subgroup.mem_center_iff.mp (hcent hn) g
    rw [this, mul_inv_cancel_right]
    exact hn⟩
  have hQ : IsPGroup p (H ⧸ C') := by
    intro q
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨c0, hc0, y0, hy0, hh⟩ := hdec h h.2
    obtain ⟨j, hj⟩ := hP ⟨y0, hy0⟩
    refine ⟨j, ?_⟩
    have hyj : y0 ^ p ^ j = 1 := by simpa using congrArg Subtype.val hj
    have hmk : (QuotientGroup.mk h : H ⧸ C') = QuotientGroup.mk ⟨y0, hPH hy0⟩ := by
      rw [QuotientGroup.eq]
      change ((h⁻¹ * ⟨y0, hPH hy0⟩ : H) : G) ∈ C
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hh, mul_inv_rev, mul_assoc, hcomm _ (C.inv_mem hc0) y0 hy0, inv_mul_cancel_left]
      exact C.inv_mem hc0
    rw [hmk, ← QuotientGroup.mk_pow]
    have : (⟨y0, hPH hy0⟩ : H) ^ p ^ j = 1 := Subtype.ext (by simpa using hyj)
    rw [this, QuotientGroup.mk_one]
  have hnil : Group.IsNilpotent (H ⧸ C') := hQ.isNilpotent
  exact Subgroup.isNilpotent_of_ker_le_center (QuotientGroup.mk' C')
    (by rw [QuotientGroup.ker_mk']; exact hcent)

end GroundTheory.LocalField
