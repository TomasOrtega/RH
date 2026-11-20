import Mathlib
import GroundTheory.LocalFields.UnitsBasic
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsRootOfAdicComplete

namespace GroundTheory.LocalField

open ValuativeRel IsLocalRing Polynomial
open scoped WithZero

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/- English proof (translation)
Set `` to `IsTopologicalAddGroup.rightUniformSpace K`. Use `isUniformAddGroup_of_addCommGroup (G := K)` as an intermediate fact. Use `infer_instance`.
-/
theorem isAdicComplete_integer : IsAdicComplete 𝓂[K] 𝒪[K] := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  infer_instance

variable {K}

/- English proof (translation)
Establish `h1 : IsUnit (1 + (η⁻¹ : 𝒪[K]ˣ) * x)`. Simplify using `using isUnit_one_sub_self_of_mem_nonunits (-(((η⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) * x)) ((IsLocalRing.mem_maximalIdeal _).mp (neg_mem (Ideal.mul_mem_left _ _ hx)))`. Establish `: (η : 𝒪[K]) + x = η * (1 + (η⁻¹ : 𝒪[K]ˣ) * x)`. Rewrite using `[mul_add, mul_one, ← mul_assoc, Units.mul_inv, one_mul]`. Rewrite using `[this]`.

Conclude with `η.isUnit.mul h1`.
-/
theorem isUnit_unit_add {η : 𝒪[K]ˣ} {x : 𝒪[K]} (hx : x ∈ 𝓂[K]) : IsUnit ((η : 𝒪[K]) + x) := by
  have h1 : IsUnit (1 + (η⁻¹ : 𝒪[K]ˣ) * x) := by
    simpa using isUnit_one_sub_self_of_mem_nonunits (-(((η⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) * x))
      ((IsLocalRing.mem_maximalIdeal _).mp (neg_mem (Ideal.mul_mem_left _ _ hx)))
  have : (η : 𝒪[K]) + x = η * (1 + (η⁻¹ : 𝒪[K]ˣ) * x) := by
    rw [mul_add, mul_one, ← mul_assoc, Units.mul_inv, one_mul]
  rw [this]
  exact η.isUnit.mul h1

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.AdicCompleteRootExistence.exists_root_of_dvd hϖ f a k ε hd hf`.
-/
theorem exists_root_of_dvd {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) (f : 𝒪[K][X]) (a : 𝒪[K]) (k : ℕ)
    (ε : 𝒪[K]ˣ) (hd : f.derivative.eval a = ϖ ^ k * ε) (hf : ϖ ^ (2 * k + 1) ∣ f.eval a) :
    ∃ b, f.eval b = 0 ∧ ϖ ^ (k + 1) ∣ b - a :=
  _root_.UpperTheory.Reformulated.B.AdicCompleteRootExistence.exists_root_of_dvd hϖ f a k ε hd hf

/- English proof (translation)
Establish `hres : residue 𝒪[K] (u : 𝒪[K]) = 1`. Use `(residue_eq_zero_iff _).mpr (by have := mem_unitFiltration.mp hu; rwa [pow_one] at this)` as an intermediate fact. Rewrite `this` using `[map_sub, map_one, sub_eq_zero]`. Then use the resulting hypothesis. Establish `hgeom` using `geom_sum_mul (u : 𝒪[K]) m`. Rewrite `hgeom` using `[← Units.val_pow_eq_pow_val, h, Units.val_one, sub_self]`.

Establish `hS : IsUnit (∑ i ∈ Finset.range m, (u : 𝒪[K]) ^ i)`. Rewrite using `[← residue_ne_zero_iff_isUnit]`. Simplify `hm` using `[map_sum, hres]`. Use `(hS.mul_right_eq_zero).mp hgeom` as an intermediate fact. Use `ext`.

Simplify `this` using `[sub_eq_zero]`.
-/
theorem eq_one_of_pow_eq_one {m : ℕ} (hm : (m : 𝓀[K]) ≠ 0) {u : 𝒪[K]ˣ}
    (hu : u ∈ unitFiltration K 1) (h : u ^ m = 1) : u = 1 := by
  have hres : residue 𝒪[K] (u : 𝒪[K]) = 1 := by
    have := (residue_eq_zero_iff _).mpr (by have := mem_unitFiltration.mp hu; rwa [pow_one] at this)
    rwa [map_sub, map_one, sub_eq_zero] at this
  have hgeom := geom_sum_mul (u : 𝒪[K]) m
  rw [← Units.val_pow_eq_pow_val, h, Units.val_one, sub_self] at hgeom
  have hS : IsUnit (∑ i ∈ Finset.range m, (u : 𝒪[K]) ^ i) := by
    rw [← residue_ne_zero_iff_isUnit]
    simpa [map_sum, hres] using hm
  have := (hS.mul_right_eq_zero).mp hgeom
  ext
  simpa [sub_eq_zero] using this

section Teichmuller

variable (K)

/- English proof (translation)
The claim follows from `Finite.one_lt_card`.
-/
theorem one_lt_card_residueField : 1 < Nat.card 𝓀[K] := Finite.one_lt_card

/- English proof (translation)
Establish `: Fintype 𝓀[K]` using `Fintype.ofFinite _`. Establish `hq : ((Nat.card 𝓀[K] : ℕ) : 𝓀[K]) = 0`. Rewrite using `[Nat.card_eq_fintype_card]`. Conclude with `FiniteField.cast_card_eq_zero _`. Rewrite using `[Nat.cast_sub (one_lt_card_residueField K).le, hq, Nat.cast_one, zero_sub]`.

Conclude with `neg_ne_zero.mpr one_ne_zero`.
-/
theorem natCast_card_residueField_sub_one_ne_zero : ((Nat.card 𝓀[K] - 1 : ℕ) : 𝓀[K]) ≠ 0 := by
  have : Fintype 𝓀[K] := Fintype.ofFinite _
  have hq : ((Nat.card 𝓀[K] : ℕ) : 𝓀[K]) = 0 := by
    rw [Nat.card_eq_fintype_card]; exact FiniteField.cast_card_eq_zero _
  rw [Nat.cast_sub (one_lt_card_residueField K).le, hq, Nat.cast_one, zero_sub]
  exact neg_ne_zero.mpr one_ne_zero

variable {K}

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible 𝒪[K]`. Use `set n := Nat.card 𝓀[K] - 1 with hn`. Establish `hn0 : n ≠ 0` using `by have := one_lt_card_residueField K; omega`. Take `⟨a, ha⟩` from `residue_surjective (ζ : 𝓀[K])`. Establish `hζ : ζ ^ n = 1`.

Rewrite using `[hn, ← Nat.card_units]`. Conclude with `pow_card_eq_one'`. Use `set f : 𝒪[K][X] := X ^ n - 1`. Establish `hfa : f.eval a ∈ 𝓂[K]`. Rewrite using `[← residue_eq_zero_iff]`.

Simplify using `[f, ha, ← Units.val_pow_eq_pow_val, hζ]`. Establish `hd : IsUnit (f.derivative.eval a)`. Rewrite using `[← residue_ne_zero_iff_isUnit]`. Simplify using `only [f, derivative_sub, derivative_X_pow, derivative_one, sub_zero, eval_mul, eval_pow, eval_X, eval_natCast, map_mul, map_natCast, map_pow, ha]`. Conclude with `mul_ne_zero (natCast_card_residueField_sub_one_ne_zero K) (pow_ne_zero _ ζ.ne_zero)`.

Take `⟨b, hb, hba⟩` from `exists_root_of_dvd hϖ f a 0 hd.unit (by simp) (by simpa using (mem_maximalIdeal_iff_dvd hϖ).mp hfa)`. Establish `hbn : b ^ n = 1` using `by simpa [f, sub_eq_zero] using hb`. Establish `hbu : IsUnit b` using `(isUnit_pow_iff hn0).mp (hbn ▸ isUnit_one)`. Use `⟨hbu.unit, ?_, ?_⟩` and prove the remaining obligations. Use `ext`.

Simplify using `[hbn]`. Use `ext`. Rewrite using `[coe_unitsToResidue, IsUnit.unit_spec, ← ha, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff, mem_maximalIdeal_iff_dvd hϖ]`. Simplify using `using hba`.
-/
theorem exists_teichmuller_lift (ζ : 𝓀[K]ˣ) :
    ∃ u : 𝒪[K]ˣ, u ^ (Nat.card 𝓀[K] - 1) = 1 ∧ unitsToResidue K u = ζ := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  set n := Nat.card 𝓀[K] - 1 with hn
  have hn0 : n ≠ 0 := by have := one_lt_card_residueField K; omega
  obtain ⟨a, ha⟩ := residue_surjective (ζ : 𝓀[K])
  have hζ : ζ ^ n = 1 := by
    rw [hn, ← Nat.card_units]; exact pow_card_eq_one'
  set f : 𝒪[K][X] := X ^ n - 1
  have hfa : f.eval a ∈ 𝓂[K] := by
    rw [← residue_eq_zero_iff]
    simp [f, ha, ← Units.val_pow_eq_pow_val, hζ]
  have hd : IsUnit (f.derivative.eval a) := by
    rw [← residue_ne_zero_iff_isUnit]
    simp only [f, derivative_sub, derivative_X_pow, derivative_one, sub_zero, eval_mul,
      eval_pow, eval_X, eval_natCast, map_mul, map_natCast, map_pow, ha]
    exact mul_ne_zero (natCast_card_residueField_sub_one_ne_zero K) (pow_ne_zero _ ζ.ne_zero)
  obtain ⟨b, hb, hba⟩ := exists_root_of_dvd hϖ f a 0 hd.unit (by simp)
    (by simpa using (mem_maximalIdeal_iff_dvd hϖ).mp hfa)
  have hbn : b ^ n = 1 := by simpa [f, sub_eq_zero] using hb
  have hbu : IsUnit b := (isUnit_pow_iff hn0).mp (hbn ▸ isUnit_one)
  refine ⟨hbu.unit, ?_, ?_⟩
  · ext; simp [hbn]
  · ext
    rw [coe_unitsToResidue, IsUnit.unit_spec, ← ha, ← sub_eq_zero, ← map_sub,
      residue_eq_zero_iff, mem_maximalIdeal_iff_dvd hϖ]
    simpa using hba

/- English proof (translation)
Establish `hmem : u * w⁻¹ ∈ unitFiltration K 1`. Rewrite using `[← ker_unitsToResidue, MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]`. Use `eq_one_of_pow_eq_one (natCast_card_residueField_sub_one_ne_zero K) hmem (by rw [mul_pow, inv_pow, hu, hw, inv_one, mul_one])` as an intermediate fact. Rewrite `this` using `[mul_inv_eq_one]`. Then use the resulting hypothesis.
-/
theorem eq_of_pow_card_sub_one {u w : 𝒪[K]ˣ} (hu : u ^ (Nat.card 𝓀[K] - 1) = 1)
    (hw : w ^ (Nat.card 𝓀[K] - 1) = 1) (h : unitsToResidue K u = unitsToResidue K w) :
    u = w := by
  have hmem : u * w⁻¹ ∈ unitFiltration K 1 := by
    rw [← ker_unitsToResidue, MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]
  have := eq_one_of_pow_eq_one (natCast_card_residueField_sub_one_ne_zero K) hmem
    (by rw [mul_pow, inv_pow, hu, hw, inv_one, mul_one])
  rwa [mul_inv_eq_one] at this

variable (K)

noncomputable def teichmuller : 𝓀[K]ˣ →* 𝒪[K]ˣ where
  toFun ζ := (exists_teichmuller_lift ζ).choose
  map_one' := eq_of_pow_card_sub_one (exists_teichmuller_lift 1).choose_spec.1 (one_pow _)
    (by rw [(exists_teichmuller_lift 1).choose_spec.2, map_one])
  map_mul' ζ η := eq_of_pow_card_sub_one (exists_teichmuller_lift (ζ * η)).choose_spec.1
    (by rw [mul_pow, (exists_teichmuller_lift ζ).choose_spec.1,
      (exists_teichmuller_lift η).choose_spec.1, one_mul])
    (by rw [(exists_teichmuller_lift (ζ * η)).choose_spec.2, map_mul,
      (exists_teichmuller_lift ζ).choose_spec.2, (exists_teichmuller_lift η).choose_spec.2])

variable {K}

@[simp]
/- English proof (translation)
The claim follows from `(exists_teichmuller_lift ζ).choose_spec.2`.
-/
theorem unitsToResidue_teichmuller (ζ : 𝓀[K]ˣ) : unitsToResidue K (teichmuller K ζ) = ζ :=
  (exists_teichmuller_lift ζ).choose_spec.2

/- English proof (translation)
The claim follows from `(exists_teichmuller_lift ζ).choose_spec.1`.
-/
theorem teichmuller_pow_card_sub_one (ζ : 𝓀[K]ˣ) :
    teichmuller K ζ ^ (Nat.card 𝓀[K] - 1) = 1 :=
  (exists_teichmuller_lift ζ).choose_spec.1

/- English proof (translation)
Rewrite using `[← ker_unitsToResidue, MonoidHom.mem_ker, map_mul, map_inv, unitsToResidue_teichmuller, mul_inv_cancel]`.
-/
theorem unitsMulInvTeichmuller_mem (u : 𝒪[K]ˣ) :
    u * (teichmuller K (unitsToResidue K u))⁻¹ ∈ unitFiltration K 1 := by
  rw [← ker_unitsToResidue, MonoidHom.mem_ker, map_mul, map_inv, unitsToResidue_teichmuller,
    mul_inv_cancel]

variable (K)

noncomputable def unitsEquivResidueProd : 𝒪[K]ˣ ≃* 𝓀[K]ˣ × unitFiltration K 1 where
  toFun u := (unitsToResidue K u, ⟨_, unitsMulInvTeichmuller_mem u⟩)
  invFun p := teichmuller K p.1 * p.2
  left_inv u := by simp
  right_inv p := by
    obtain ⟨ζ, v, hv⟩ := p
    have hv' : unitsToResidue K v = 1 := by rwa [← MonoidHom.mem_ker, ker_unitsToResidue]
    ext
    · simp [hv']
    · simp [hv']
  map_mul' u w := by
    ext
    · simp
    · simp only [map_mul, mul_inv_rev, Prod.snd_mul, Subgroup.coe_mul]
      simp only [mul_comm, mul_left_comm, mul_assoc]

@[simp]
/- English proof (translation)
The claim follows from `rfl @[simp]`.
-/
theorem unitsEquivResidueProd_fst (u : 𝒪[K]ˣ) :
    (unitsEquivResidueProd K u).1 = unitsToResidue K u := rfl

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem unitsEquivResidueProd_symm_apply (ζ : 𝓀[K]ˣ) (v : unitFiltration K 1) :
    (unitsEquivResidueProd K).symm (ζ, v) = teichmuller K ζ * v := rfl

end Teichmuller

section Powers

/- English proof (translation)
Use `set f : 𝒪[K][X] := X ^ m - C (w : 𝒪[K])`. Take `⟨b, hb, -⟩` from `exists_root_of_dvd hϖ f 1 k ε (by`. Simplify using `only [f, derivative_sub, derivative_C, sub_zero, derivative_X_pow, eval_mul, eval_C, eval_pow, eval_X, one_pow, mul_one]`. Conclude with `hmk)`. Use the proof step `(by`.

Use `(mem_maximalIdeal_pow_iff hϖ).mp (mem_unitFiltration.mp hw)` as an intermediate fact. Establish `e : f.eval 1 = -((w : 𝒪[K]) - 1)` using `by simp [f]`. Rewrite using `[e, dvd_neg]`. Conclude with `this)`. Establish `hbm : b ^ m = w` using `by simpa [f, sub_eq_zero] using hb`.

Establish `hbu : IsUnit b` using `(isUnit_pow_iff hm).mp (hbm ▸ w.isUnit)`. Conclude with `⟨hbu.unit, by ext; simp [hbm]⟩`.
-/
theorem exists_pow_eq_of_mem {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) {m k : ℕ} (hm : m ≠ 0)
    {ε : 𝒪[K]ˣ} (hmk : (m : 𝒪[K]) = ϖ ^ k * ε) {w : 𝒪[K]ˣ}
    (hw : w ∈ unitFiltration K (2 * k + 1)) : ∃ x : 𝒪[K]ˣ, x ^ m = w := by
  set f : 𝒪[K][X] := X ^ m - C (w : 𝒪[K])
  obtain ⟨b, hb, -⟩ := exists_root_of_dvd hϖ f 1 k ε
    (by
      simp only [f, derivative_sub, derivative_C, sub_zero, derivative_X_pow, eval_mul,
        eval_C, eval_pow, eval_X, one_pow, mul_one]
      exact hmk)
    (by
      have := (mem_maximalIdeal_pow_iff hϖ).mp (mem_unitFiltration.mp hw)
      have e : f.eval 1 = -((w : 𝒪[K]) - 1) := by simp [f]
      rw [e, dvd_neg]
      exact this)
  have hbm : b ^ m = w := by simpa [f, sub_eq_zero] using hb
  have hbu : IsUnit b := (isUnit_pow_iff hm).mp (hbm ▸ w.isUnit)
  exact ⟨hbu.unit, by ext; simp [hbm]⟩

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible 𝒪[K]`. Establish `hm' : (m : 𝒪[K]) ≠ 0` using `fun h ↦ hm (by have := congrArg Subtype.val h; simpa using this)`. Establish `hm0 : m ≠ 0` using `by rintro rfl; simp at hm`. Take `⟨k, ε, hk⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hm' hϖ`. Use `⟨2 * k + 1, fun w hw ↦ ?_⟩` and prove the remaining obligations.

Take `⟨x, hx⟩` from `exists_pow_eq_of_mem hϖ hm0 (ε := ε) (by rw [hk, mul_comm]) hw`. Conclude with `⟨x, hx⟩`.
-/
theorem exists_unitFiltration_le_range_pow {m : ℕ} (hm : (m : K) ≠ 0) :
    ∃ N, unitFiltration K N ≤ (powMonoidHom m : 𝒪[K]ˣ →* 𝒪[K]ˣ).range := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hm' : (m : 𝒪[K]) ≠ 0 := fun h ↦ hm (by have := congrArg Subtype.val h; simpa using this)
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  obtain ⟨k, ε, hk⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hm' hϖ
  refine ⟨2 * k + 1, fun w hw ↦ ?_⟩
  obtain ⟨x, hx⟩ := exists_pow_eq_of_mem hϖ hm0 (ε := ε) (by rw [hk, mul_comm]) hw
  exact ⟨x, hx⟩

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible 𝒪[K]`. Establish `hu : IsUnit (m : 𝒪[K])`. Rewrite using `[← residue_ne_zero_iff_isUnit, map_natCast]`. Conclude with `hm`. Establish `hm0 : m ≠ 0` using `by rintro rfl; simp at hm`.

Introduce `w hw`. Take `⟨x, hx⟩` from `exists_pow_eq_of_mem hϖ hm0 (k := 0) (ε := hu.unit) (by simp) (by simpa using hw)`. Conclude with `⟨x, hx⟩`.
-/
theorem unitFiltration_one_le_range_pow {m : ℕ} (hm : (m : 𝓀[K]) ≠ 0) :
    unitFiltration K 1 ≤ (powMonoidHom m : 𝒪[K]ˣ →* 𝒪[K]ˣ).range := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hu : IsUnit (m : 𝒪[K]) := by
    rw [← residue_ne_zero_iff_isUnit, map_natCast]; exact hm
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  intro w hw
  obtain ⟨x, hx⟩ := exists_pow_eq_of_mem hϖ hm0 (k := 0) (ε := hu.unit) (by simp)
    (by simpa using hw)
  exact ⟨x, hx⟩

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible 𝒪[K]`. Take `⟨N, hN⟩` from `exists_unitFiltration_le_range_pow hm`. Establish `hm0 : m ≠ 0` using `by rintro rfl; simp at hm`. Use `set H := (powMonoidHom m : Kˣ →* Kˣ).range`. Use `set ψ : 𝒪[K]ˣ →* Kˣ ⧸ H := (QuotientGroup.mk' H).comp (unitsIncl K)`.

Establish `hle : unitFiltration K N ≤ ψ.ker`. Introduce `w hw`. Take `⟨x, rfl⟩` from `hN hw`. Rewrite using `[MonoidHom.mem_ker]`. Simplify using `only [ψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]`.

Conclude with `⟨unitsIncl K x, by simp⟩`. Use `set ψ' := QuotientGroup.lift _ ψ hle`. Use `set π := uniformizerUnit hϖ`. Set `g : Fin m × (𝒪[K]ˣ ⧸ unitFiltration K N) → Kˣ ⧸ H` to `fun p ↦ (QuotientGroup.mk π : Kˣ ⧸ H) ^ (p.1 : ℕ) * ψ' p.2`. Use `Finite.of_surjective g ?_` and prove the remaining obligations.

Introduce `y`. Take `⟨x, rfl⟩` from `QuotientGroup.mk_surjective y`. Use `set p := unitsEquivIntProd hϖ x`. Establish `hx : x = unitsOfIntProd hϖ p`. Rewrite using `[← unitsEquivIntProd_symm_apply, MulEquiv.symm_apply_apply]`.

Use `set n := Multiplicative.toAdd p.1`. Establish `hmpos : (0 : ℤ) < m` using `by exact_mod_cast Nat.pos_of_ne_zero hm0`. Use `set r := n % (m : ℤ)`. Use `set q := n / (m : ℤ)`. Establish `hr0 : 0 ≤ r` using `Int.emod_nonneg _ hmpos.ne'`.

Establish `hrm : r < m` using `Int.emod_lt_of_pos _ hmpos`. Establish `hnrq : n = r + m * q` using `by have := Int.mul_ediv_add_emod n m; linarith`. Use `⟨(⟨r.toNat, by omega⟩, QuotientGroup.mk p.2), ?_⟩` and prove the remaining obligations. Establish `hπ : π ^ n = π ^ r.toNat * (π ^ q) ^ m`. Rewrite using `[← zpow_natCast, ← zpow_natCast (π ^ q) m, ← zpow_mul, ← zpow_add, Int.toNat_of_nonneg hr0, hnrq, mul_comm]`.

Establish `hxπ : x = π ^ n * unitsIncl K p.2`. Rewrite using `[hx]`. Both sides reduce to the same expression. Simplify using `only [g, ψ', QuotientGroup.lift_mk, ψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply]`. Rewrite using `[hxπ, hπ, ← QuotientGroup.mk_pow, ← QuotientGroup.mk_mul, QuotientGroup.eq]`.

Use `⟨π ^ q, ?_⟩` and prove the remaining obligations. Rewrite using `[powMonoidHom_apply, mul_right_comm (π ^ r.toNat), inv_mul_cancel_left]`.
-/
theorem finite_quotient_range_pow {m : ℕ} (hm : (m : K) ≠ 0) :
    Finite (Kˣ ⧸ (powMonoidHom m : Kˣ →* Kˣ).range) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  obtain ⟨N, hN⟩ := exists_unitFiltration_le_range_pow hm
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  set H := (powMonoidHom m : Kˣ →* Kˣ).range
  set ψ : 𝒪[K]ˣ →* Kˣ ⧸ H := (QuotientGroup.mk' H).comp (unitsIncl K)
  have hle : unitFiltration K N ≤ ψ.ker := by
    intro w hw
    obtain ⟨x, rfl⟩ := hN hw
    rw [MonoidHom.mem_ker]
    simp only [ψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ⟨unitsIncl K x, by simp⟩
  set ψ' := QuotientGroup.lift _ ψ hle
  set π := uniformizerUnit hϖ
  let g : Fin m × (𝒪[K]ˣ ⧸ unitFiltration K N) → Kˣ ⧸ H :=
    fun p ↦ (QuotientGroup.mk π : Kˣ ⧸ H) ^ (p.1 : ℕ) * ψ' p.2
  refine Finite.of_surjective g ?_
  intro y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  set p := unitsEquivIntProd hϖ x
  have hx : x = unitsOfIntProd hϖ p := by
    rw [← unitsEquivIntProd_symm_apply, MulEquiv.symm_apply_apply]
  set n := Multiplicative.toAdd p.1
  have hmpos : (0 : ℤ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm0
  set r := n % (m : ℤ)
  set q := n / (m : ℤ)
  have hr0 : 0 ≤ r := Int.emod_nonneg _ hmpos.ne'
  have hrm : r < m := Int.emod_lt_of_pos _ hmpos
  have hnrq : n = r + m * q := by have := Int.mul_ediv_add_emod n m; linarith
  refine ⟨(⟨r.toNat, by omega⟩, QuotientGroup.mk p.2), ?_⟩
  have hπ : π ^ n = π ^ r.toNat * (π ^ q) ^ m := by
    rw [← zpow_natCast, ← zpow_natCast (π ^ q) m, ← zpow_mul, ← zpow_add, Int.toNat_of_nonneg hr0,
      hnrq, mul_comm]
  have hxπ : x = π ^ n * unitsIncl K p.2 := by
    rw [hx]
    rfl
  simp only [g, ψ', QuotientGroup.lift_mk, ψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
  rw [hxπ, hπ, ← QuotientGroup.mk_pow, ← QuotientGroup.mk_mul, QuotientGroup.eq]
  refine ⟨π ^ q, ?_⟩
  rw [powMonoidHom_apply, mul_right_comm (π ^ r.toNat), inv_mul_cancel_left]

/- English proof (translation)
The claim follows from `finite_quotient_range_pow (Nat.cast_ne_zero.mpr hm)`.
-/
theorem finite_quotient_range_pow_of_charZero [CharZero K] {m : ℕ} (hm : m ≠ 0) :
    Finite (Kˣ ⧸ (powMonoidHom m : Kˣ →* Kˣ).range) :=
  finite_quotient_range_pow (Nat.cast_ne_zero.mpr hm)

end Powers

end GroundTheory.LocalField
