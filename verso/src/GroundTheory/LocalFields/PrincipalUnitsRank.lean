import Mathlib
import GroundTheory.LocalFields.PadicLogLinear
import GroundTheory.LocalFields.Integers

namespace GroundTheory.LocalField

open ValuativeRel IsLocalRing Topology Filter
open scoped WithZero

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

namespace PadicRank

variable (p : ℕ) [hp : Fact p.Prime]

/- English proof (translation)
Rewrite using `[Valuation.mem_integer_iff, ← map_one (valuation ℚ_[p]), ← Valuation.vle_iff_le, Valuation.Compatible.vle_iff_le (v := Padic.mulValuation), GroundTheory.LocalField.Padic.mulValuation_le_iff_norm_le, norm_one]`.
-/
theorem mem_integer_padic_iff (x : ℚ_[p]) : x ∈ 𝒪[ℚ_[p]] ↔ ‖x‖ ≤ 1 := by
  rw [Valuation.mem_integer_iff, ← map_one (valuation ℚ_[p]), ← Valuation.vle_iff_le,
    Valuation.Compatible.vle_iff_le (v := Padic.mulValuation),
    GroundTheory.LocalField.Padic.mulValuation_le_iff_norm_le, norm_one]

noncomputable def padicIntEquivInteger : ℤ_[p] ≃+* 𝒪[ℚ_[p]] where
  toFun x := ⟨x, (mem_integer_padic_iff p x).mpr x.2⟩
  invFun y := ⟨y, (mem_integer_padic_iff p y).mp y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

variable [CharP 𝓀[K] p] [CharZero K]

variable (K) in

noncomputable def padicIntHom : ℤ_[p] →+* K :=
  (CharZero.padicHom K p).comp PadicInt.Coe.ringHom

/- English proof (translation)
The claim follows from `CharZero.valuation_padicHom_padicInt_le_one K p a`.
-/
theorem padicIntHom_mem (a : ℤ_[p]) : padicIntHom K p a ∈ 𝒪[K] :=
  CharZero.valuation_padicHom_padicInt_le_one K p a

variable (K) in

noncomputable def padicIntHomInteger : ℤ_[p] →+* 𝒪[K] :=
  (padicIntHom K p).codRestrict 𝒪[K] (padicIntHom_mem p)

variable (K) in

noncomputable abbrev algebraK : Algebra ℤ_[p] K := (padicIntHom K p).toAlgebra

variable (K) in

noncomputable abbrev algebraInteger : Algebra ℤ_[p] 𝒪[K] := (padicIntHomInteger K p).toAlgebra

attribute [local instance] algebraK algebraInteger

/- English proof (translation)
Set `` to `(CharZero.padicHom K p).toAlgebra`. Establish `: ValuativeExtension ℚ_[p] K` using `⟨CharZero.padicHom_vle_iff K p⟩`. Establish `: FiniteDimensional ℚ_[p] K` using `CharZero.finiteDimensional_padicHom K p`. Establish `hfin : Module.Finite 𝒪[ℚ_[p]] 𝒪[K]` using `finite_integer ℚ_[p] K`. Establish `hrank` using `finrank_integer ℚ_[p] K`.

Establish `he : (algebraMap ℤ_[p] 𝒪[K]).comp ((padicIntEquivInteger p).symm : 𝒪[ℚ_[p]] →+* ℤ_[p]) = (RingEquiv.refl 𝒪[K] : 𝒪[K] →+* 𝒪[K]).comp (algebraMap 𝒪[ℚ_[p]] 𝒪[K])`. Use extensionality with `x`. Both sides reduce to the same expression. Use `⟨Module.Finite.of_equiv_equiv (padicIntEquivInteger p).symm (RingEquiv.refl _) he, ?_⟩` and prove the remaining obligations. Rewrite using `[← hrank]`.

Use `rank_eq_of_equiv_equiv (R := ℤ_[p]) (R' := 𝒪[ℚ_[p]]) (M := 𝒪[K]) (M₁ := 𝒪[K]) (padicIntEquivInteger p) (AddEquiv.refl _) (padicIntEquivInteger p).bijective (fun r m ↦ rfl)` as an intermediate fact. Conclude with `congrArg Cardinal.toNat this`.
-/
theorem finite_and_finrank_integer :
    Module.Finite ℤ_[p] 𝒪[K] ∧ Module.finrank ℤ_[p] 𝒪[K] =
      (letI := (CharZero.padicHom K p).toAlgebra; Module.finrank ℚ_[p] K) := by
  let := (CharZero.padicHom K p).toAlgebra
  have : ValuativeExtension ℚ_[p] K := ⟨CharZero.padicHom_vle_iff K p⟩
  have : FiniteDimensional ℚ_[p] K := CharZero.finiteDimensional_padicHom K p
  have hfin : Module.Finite 𝒪[ℚ_[p]] 𝒪[K] := finite_integer ℚ_[p] K
  have hrank := finrank_integer ℚ_[p] K
  have he : (algebraMap ℤ_[p] 𝒪[K]).comp ((padicIntEquivInteger p).symm : 𝒪[ℚ_[p]] →+* ℤ_[p]) =
      (RingEquiv.refl 𝒪[K] : 𝒪[K] →+* 𝒪[K]).comp (algebraMap 𝒪[ℚ_[p]] 𝒪[K]) := by
    ext x
    rfl
  refine ⟨Module.Finite.of_equiv_equiv (padicIntEquivInteger p).symm (RingEquiv.refl _) he, ?_⟩
  rw [← hrank]
  have := rank_eq_of_equiv_equiv (R := ℤ_[p]) (R' := 𝒪[ℚ_[p]]) (M := 𝒪[K]) (M₁ := 𝒪[K])
    (padicIntEquivInteger p) (AddEquiv.refl _) (padicIntEquivInteger p).bijective
    (fun r m ↦ rfl)
  exact congrArg Cardinal.toNat this

/- English proof (translation)
The claim follows from `padicHom_padicInt_mem_valBall_zero p a`.
-/
theorem padicIntHom_mem_valBall_zero (a : ℤ_[p]) : padicIntHom K p a ∈ valBall K 0 :=
  padicHom_padicInt_mem_valBall_zero p a

variable (K) in

noncomputable def valBallSubmodule (m : ℤ) : Submodule ℤ_[p] K where
  carrier := valBall K m
  add_mem' := add_mem
  zero_mem' := zero_mem _
  smul_mem' a x hx := by
    rw [Algebra.smul_def]
    have h := mul_mem_valBall (padicIntHom_mem_valBall_zero p a) hx
    rw [zero_add] at h
    exact h

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_valBallSubmodule {m : ℤ} {x : K} : x ∈ valBallSubmodule K p m ↔ x ∈ valBall K m :=
  Iff.rfl

variable (K) in

noncomputable def valBallSubmoduleZeroEquiv : valBallSubmodule K p 0 ≃ₗ[ℤ_[p]] 𝒪[K] where
  toFun x := ⟨x, mem_integer_of_mem_valBall le_rfl x.2⟩
  invFun y := ⟨y, by
    rw [mem_valBallSubmodule, mem_valBall, neg_zero, WithZero.exp_zero,
      normalizedValuation_le_one_iff]; exact y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (K) in

noncomputable def valBallSubmoduleEquiv (m : ℤ) :
    valBallSubmodule K p 0 ≃ₗ[ℤ_[p]] valBallSubmodule K p m :=
  have hy := exists_normalizedValuation_eq K (-m)
  let y := hy.choose
  have hy0 : y ≠ 0 := by
    intro h
    have := hy.choose_spec
    rw [show hy.choose = y from rfl, h, map_zero] at this
    exact WithZero.exp_ne_zero this.symm
  { toFun x := ⟨y * x, (mem_valBallSubmodule p).mpr (by
      have := mul_mem_valBall (show y ∈ valBall K m by
        rw [mem_valBall, show y = hy.choose from rfl, hy.choose_spec]) x.2
      simpa using this)⟩
    invFun x := ⟨y⁻¹ * x, (mem_valBallSubmodule p).mpr (by
      have := mul_mem_valBall (show y⁻¹ ∈ valBall K (-m) by
        rw [mem_valBall, map_inv₀, show y = hy.choose from rfl, hy.choose_spec,
          ← WithZero.exp_neg]) x.2
      simpa using this)⟩
    left_inv x := by ext; simp [hy0]
    right_inv x := by ext; simp [hy0]
    map_add' x x' := by ext; simp [mul_add]
    map_smul' a x := by
      ext
      simp only [SetLike.val_smul, Algebra.smul_def, RingHom.id_apply]
      ring }

/- English proof (translation)
Take `⟨h1, h2⟩` from `finite_and_finrank_integer (K := K) p`. Establish `e` using `(valBallSubmoduleEquiv K p m).symm.trans (valBallSubmoduleZeroEquiv K p)`. Conclude with `⟨Module.Finite.equiv e.symm, e.finrank_eq.trans h2⟩`.
-/
theorem finite_and_finrank_valBallSubmodule (m : ℤ) :
    Module.Finite ℤ_[p] (valBallSubmodule K p m) ∧ Module.finrank ℤ_[p] (valBallSubmodule K p m) =
      (letI := (CharZero.padicHom K p).toAlgebra; Module.finrank ℚ_[p] K) := by
  obtain ⟨h1, h2⟩ := finite_and_finrank_integer (K := K) p
  have e := (valBallSubmoduleEquiv K p m).symm.trans (valBallSubmoduleZeroEquiv K p)
  exact ⟨Module.Finite.equiv e.symm, e.finrank_eq.trans h2⟩

/- English proof (translation)
Take `⟨h1, h2⟩` from `finite_and_finrank_valBallSubmodule (K := K) p m`. Rewrite using `[← h2]`. Conclude with `(Cardinal.cast_toNat_of_lt_aleph0 (Module.rank_lt_aleph0 _ _)).symm`.
-/
theorem rank_valBallSubmodule (m : ℤ) :
    Module.rank ℤ_[p] (valBallSubmodule K p m) =
      (letI := (CharZero.padicHom K p).toAlgebra; Module.finrank ℚ_[p] K) := by
  obtain ⟨h1, h2⟩ := finite_and_finrank_valBallSubmodule (K := K) p m
  rw [← h2]
  exact (Cardinal.cast_toNat_of_lt_aleph0 (Module.rank_lt_aleph0 _ _)).symm

variable (K) in

noncomputable def padicLogLinear : Additive (unitFiltrationUnits K 1) →ₗ[ℤ_[p]] K where
  toFun := padicLog K
  map_add' := map_add _
  map_smul' a u := by
    rw [padicLog_smul p a u, RingHom.id_apply, Algebra.smul_def]
    rfl

omit [CharZero K] in
/- English proof (translation)
Rewrite using `[principalFiltration_zero]`. Discharge the goal by the elementary cases of `trivial`.
-/
theorem mem_principalFiltration_zero (u : Additive (unitFiltrationUnits K 1)) :
    u ∈ principalFiltration K 0 := by
  rw [principalFiltration_zero]; trivial

/- English proof (translation)
Use `nsmul_prime_pow_mem_principalFiltration p (mem_principalFiltration_zero u) (absRamificationIndex K)` as an intermediate fact. Rewrite `this` using `[zero_add]`. Conclude with `padicLog_mem_valBall_of_mem p le_rfl this` after adjusting the coercions.
-/
theorem padicLog_nsmul_mem (u : Additive (unitFiltrationUnits K 1)) :
    padicLog K (p ^ absRamificationIndex K • u) ∈ valBall K (absRamificationIndex K + 1) := by
  have := nsmul_prime_pow_mem_principalFiltration p (mem_principalFiltration_zero u)
    (absRamificationIndex K)
  rw [zero_add] at this
  exact_mod_cast padicLog_mem_valBall_of_mem p le_rfl this

include p in

/- English proof (translation)
Use `set e := absRamificationIndex K`. Establish `h` using `padicLog_nsmul_mem p u`. Rewrite `h` using `[map_nsmul, nsmul_eq_mul]`. Establish `hp0 : ((p ^ e : ℕ) : K) ≠ 0` using `Nat.cast_ne_zero.mpr (pow_ne_zero _ hp.out.ne_zero)`. Establish `hinv : (((p ^ e : ℕ) : K))⁻¹ ∈ valBall K (-(e * e : ℤ))`.

Rewrite using `[mem_valBall, map_inv₀, Nat.cast_pow, map_pow, normalizedValuation_natCast_prime p, ← WithZero.exp_nsmul, ← WithZero.exp_neg]`. Simplify using the standard rewrite rules. Conclude with `le_rfl`. Use `mul_mem_valBall hinv h` as an intermediate fact. Move the coercions through the operations in `at this hp0`.

Rewrite `this` using `[← mul_assoc, inv_mul_cancel₀ hp0, one_mul]`. Use `this using 2` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.
-/
theorem padicLog_mem_valBall_bound (u : Additive (unitFiltrationUnits K 1)) :
    padicLog K u ∈ valBall K (absRamificationIndex K + 1 -
      absRamificationIndex K * absRamificationIndex K) := by
  set e := absRamificationIndex K
  have h := padicLog_nsmul_mem p u
  rw [map_nsmul, nsmul_eq_mul] at h
  have hp0 : ((p ^ e : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (pow_ne_zero _ hp.out.ne_zero)
  have hinv : (((p ^ e : ℕ) : K))⁻¹ ∈ valBall K (-(e * e : ℤ)) := by
    rw [mem_valBall, map_inv₀, Nat.cast_pow, map_pow, normalizedValuation_natCast_prime p,
      ← WithZero.exp_nsmul, ← WithZero.exp_neg]
    simp
    exact le_rfl
  have := mul_mem_valBall hinv h
  push_cast at this hp0
  rw [← mul_assoc, inv_mul_cancel₀ hp0, one_mul] at this
  convert this using 2
  ring

/- English proof (translation)
Introduce and unpack `_ ⟨u, rfl⟩`. Conclude with `padicLog_mem_valBall_bound p u`.
-/
theorem range_padicLogLinear_le : LinearMap.range (padicLogLinear K p) ≤
    valBallSubmodule K p (absRamificationIndex K + 1 -
      absRamificationIndex K * absRamificationIndex K) := by
  rintro _ ⟨u, rfl⟩
  exact padicLog_mem_valBall_bound p u

omit [CharP 𝓀[K] p] [CharZero K] in
/- English proof (translation)
Establish `hp2 : (2 : ℤ) ≤ p` using `by exact_mod_cast hp.out.two_le`. Use `push_cast`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem lt_sub_one_mul_succ : (absRamificationIndex K : ℤ) <
    (p - 1 : ℤ) * ((absRamificationIndex K + 1 : ℕ) : ℤ) := by
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.out.two_le
  push_cast
  nlinarith

/- English proof (translation)
Introduce `y hy`. Use `set n := absRamificationIndex K + 1`. Establish `hn` using `lt_sub_one_mul_succ (K := K) p`. Use `set w := (logValBallEquiv p n hn).symm ⟨y, hy⟩`. Establish `h1 : 1 ≤ n` using `by omega`.

Use `⟨Additive.ofMul ⟨((Additive.toMul w : unitFiltrationUnits K n) : Kˣ), unitFiltrationUnits_antitone h1 (Additive.toMul w).2⟩, ?_⟩` and prove the remaining obligations. Use `congrArg Subtype.val ((logValBallEquiv p n hn).apply_symm_apply ⟨y, hy⟩)` as an intermediate fact. Conclude with `this`.
-/
theorem valBallSubmodule_le_range : valBallSubmodule K p ((absRamificationIndex K + 1 : ℕ) : ℤ) ≤
    LinearMap.range (padicLogLinear K p) := by
  intro y hy
  set n := absRamificationIndex K + 1
  have hn := lt_sub_one_mul_succ (K := K) p
  set w := (logValBallEquiv p n hn).symm ⟨y, hy⟩
  have h1 : 1 ≤ n := by omega
  refine ⟨Additive.ofMul ⟨((Additive.toMul w : unitFiltrationUnits K n) : Kˣ),
    unitFiltrationUnits_antitone h1 (Additive.toMul w).2⟩, ?_⟩
  have := congrArg Subtype.val ((logValBallEquiv p n hn).apply_symm_apply ⟨y, hy⟩)
  exact this

/- English proof (translation)
Use `set e := absRamificationIndex K`. Establish `hw` using `nsmul_prime_pow_mem_principalFiltration p (mem_principalFiltration_zero u) e`. Rewrite `hw` using `[zero_add, mem_principalFiltration]`. Establish `hlog : logSeries ((((Additive.toMul (p ^ e • u) : unitFiltrationUnits K 1) : Kˣ) : K) - 1) = 0`. Rewrite using `[← padicLog_apply, map_nsmul, hu, smul_zero]`.

Use `eq_zero_of_logSeries_eq_zero p (by exact_mod_cast lt_sub_one_mul_succ (K := K) p) hw hlog` as an intermediate fact. Apply `Additive.toMul.injective` to reduce the goal to its premises. Use `ext`. Simplify `this` using `[sub_eq_zero]`.
-/
theorem nsmul_eq_zero_of_padicLog_eq_zero {u : Additive (unitFiltrationUnits K 1)}
    (hu : padicLog K u = 0) : p ^ absRamificationIndex K • u = 0 := by
  set e := absRamificationIndex K
  have hw := nsmul_prime_pow_mem_principalFiltration p (mem_principalFiltration_zero u) e
  rw [zero_add, mem_principalFiltration] at hw
  have hlog : logSeries ((((Additive.toMul (p ^ e • u) : unitFiltrationUnits K 1) : Kˣ) : K) - 1)
      = 0 := by
    rw [← padicLog_apply, map_nsmul, hu, smul_zero]
  have := eq_zero_of_logSeries_eq_zero p (by exact_mod_cast lt_sub_one_mul_succ (K := K) p) hw hlog
  apply Additive.toMul.injective
  ext
  simpa [sub_eq_zero] using this

/- English proof (translation)
Use `set e := absRamificationIndex K`. Set `f : LinearMap.ker (padicLogLinear K p) → rootsOfUnity (p ^ e) K` to `fun u ↦ ⟨((Additive.toMul (u : Additive (unitFiltrationUnits K 1)) : unitFiltrationUnits K 1) : Kˣ), by`. Establish `h` using `nsmul_eq_zero_of_padicLog_eq_zero p (LinearMap.mem_ker.mp u.2)`. Use `congrArg (fun v : Additive (unitFiltrationUnits K 1) ↦ ((Additive.toMul v : unitFiltrationUnits K 1) : Kˣ)) h` as an intermediate fact. Simplify `this⟩` using `[mem_rootsOfUnity]`.

Use `Finite.of_injective f fun u v huv ↦ ?_` and prove the remaining obligations. Use `congrArg (fun z : rootsOfUnity (p ^ e) K ↦ (z : Kˣ)) huv` as an intermediate fact. Conclude with `Subtype.ext (Additive.toMul.injective (Subtype.ext this))`.
-/
theorem finite_ker_padicLog : Finite (LinearMap.ker (padicLogLinear K p)) := by
  set e := absRamificationIndex K
  let f : LinearMap.ker (padicLogLinear K p) → rootsOfUnity (p ^ e) K := fun u ↦
    ⟨((Additive.toMul (u : Additive (unitFiltrationUnits K 1)) : unitFiltrationUnits K 1) : Kˣ), by
      have h := nsmul_eq_zero_of_padicLog_eq_zero p (LinearMap.mem_ker.mp u.2)
      have := congrArg (fun v : Additive (unitFiltrationUnits K 1) ↦
        ((Additive.toMul v : unitFiltrationUnits K 1) : Kˣ)) h
      simpa [mem_rootsOfUnity] using this⟩
  refine Finite.of_injective f fun u v huv ↦ ?_
  have := congrArg (fun z : rootsOfUnity (p ^ e) K ↦ (z : Kˣ)) huv
  exact Subtype.ext (Additive.toMul.injective (Subtype.ext this))

/- English proof (translation)
Use `finite_ker_padicLog (K := K) p` as an intermediate fact. Establish `hfin : (LinearMap.ker (padicLogLinear K p) : Set (Additive (unitFiltrationUnits K 1))).Finite` using `Set.toFinite _`. Use `⟨hfin.toFinset, ?_⟩` and prove the remaining obligations. Rewrite using `[Set.Finite.coe_toFinset, Submodule.span_eq]`.
-/
theorem fg_ker_padicLogLinear : (LinearMap.ker (padicLogLinear K p)).FG := by
  have := finite_ker_padicLog (K := K) p
  have hfin : (LinearMap.ker (padicLogLinear K p) : Set (Additive (unitFiltrationUnits K 1))).Finite :=
    Set.toFinite _
  refine ⟨hfin.toFinset, ?_⟩
  rw [Set.Finite.coe_toFinset, Submodule.span_eq]

/- English proof (translation)
Use `set c : ℤ := absRamificationIndex K + 1 - absRamificationIndex K * absRamificationIndex K`. Establish `: Module.Finite ℤ_[p] (valBallSubmodule K p c)` using `(finite_and_finrank_valBallSubmodule (K := K) p c).1`. Establish `: IsNoetherian ℤ_[p] (valBallSubmodule K p c)` using `inferInstance`. Establish `: IsNoetherian ℤ_[p] (LinearMap.range (padicLogLinear K p))` using `isNoetherian_of_le (range_padicLogLinear_le p)`. Conclude with `(Submodule.fg_top _).mp (IsNoetherian.noetherian ⊤)`.
-/
theorem fg_range_padicLogLinear : (LinearMap.range (padicLogLinear K p)).FG := by
  set c : ℤ := absRamificationIndex K + 1 - absRamificationIndex K * absRamificationIndex K
  have : Module.Finite ℤ_[p] (valBallSubmodule K p c) :=
    (finite_and_finrank_valBallSubmodule (K := K) p c).1
  have : IsNoetherian ℤ_[p] (valBallSubmodule K p c) := inferInstance
  have : IsNoetherian ℤ_[p] (LinearMap.range (padicLogLinear K p)) :=
    isNoetherian_of_le (range_padicLogLinear_le p)
  exact (Submodule.fg_top _).mp (IsNoetherian.noetherian ⊤)

end PadicRank

section Rank

open PadicRank

attribute [local instance] algebraK algebraInteger

/- English proof (translation)
Use `⟨?_⟩` and prove the remaining obligations. Establish `h` using `Submodule.fg_of_fg_map_of_fg_inf_ker (padicLogLinear K p) (s := ⊤) (by rw [Submodule.map_top]; exact fg_range_padicLogLinear p) (by rw [top_inf_eq]; exact fg_ker_padicLogLinear p)`. Conclude with `h`.
-/
theorem finite_principalUnits (p : ℕ) [Fact p.Prime] [CharP 𝓀[K] p] [CharZero K] :
    Module.Finite ℤ_[p] (Additive (unitFiltrationUnits K 1)) := by
  refine ⟨?_⟩
  have h := Submodule.fg_of_fg_map_of_fg_inf_ker (padicLogLinear K p)
    (s := ⊤) (by rw [Submodule.map_top]; exact fg_range_padicLogLinear p)
    (by rw [top_inf_eq]; exact fg_ker_padicLogLinear p)
  exact h

/- English proof (translation)
Use `set d := (letI := (CharZero.padicHom K p).toAlgebra; Module.finrank ℚ_[p] K)`. Establish `hker : Module.rank ℤ_[p] (LinearMap.ker (padicLogLinear K p)) = 0`. Use `(rank_eq_zero_iff (R := ℤ_[p]) (M := LinearMap.ker (padicLogLinear K p))).mpr fun x ↦ ?_` and prove the remaining obligations. Use `⟨((p ^ absRamificationIndex K : ℕ) : ℤ_[p]), ?_, ?_⟩` and prove the remaining obligations. Conclude with `pow_ne_zero _ (Fact.out : p.Prime).ne_zero` after adjusting the coercions.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[Submodule.coe_smul, natCast_smul, Submodule.coe_zero]`. Conclude with `nsmul_eq_zero_of_padicLog_eq_zero p (LinearMap.mem_ker.mp x.2)`. Establish `hrange : Module.rank ℤ_[p] (LinearMap.range (padicLogLinear K p)) = d`. Use `le_antisymm ?_ ?_` and prove the remaining obligations.

Rewrite using `[← rank_valBallSubmodule (K := K) p (absRamificationIndex K + 1 - absRamificationIndex K * absRamificationIndex K)]`. Conclude with `Submodule.rank_mono (range_padicLogLinear_le p)`. Rewrite using `[← rank_valBallSubmodule (K := K) p ((absRamificationIndex K + 1 : ℕ) : ℤ)]`. Conclude with `Submodule.rank_mono (valBallSubmodule_le_range p)`. Establish `h` using `(padicLogLinear K p).rank_range_add_rank_ker`.

Rewrite `h` using `[hker, hrange, add_zero]`. Rewrite using `[Module.finrank, ← h]`. Simplify using the standard rewrite rules.
-/
theorem finrank_principalUnits (p : ℕ) [Fact p.Prime] [CharP 𝓀[K] p] [CharZero K] :
    Module.finrank ℤ_[p] (Additive (unitFiltrationUnits K 1)) =
      (letI := (CharZero.padicHom K p).toAlgebra; Module.finrank ℚ_[p] K) := by
  set d := (letI := (CharZero.padicHom K p).toAlgebra; Module.finrank ℚ_[p] K)
  have hker : Module.rank ℤ_[p] (LinearMap.ker (padicLogLinear K p)) = 0 := by
    refine (rank_eq_zero_iff (R := ℤ_[p]) (M := LinearMap.ker (padicLogLinear K p))).mpr
      fun x ↦ ?_
    refine ⟨((p ^ absRamificationIndex K : ℕ) : ℤ_[p]), ?_, ?_⟩
    · exact_mod_cast pow_ne_zero _ (Fact.out : p.Prime).ne_zero
    · apply Subtype.ext
      rw [Submodule.coe_smul, natCast_smul, Submodule.coe_zero]
      exact nsmul_eq_zero_of_padicLog_eq_zero p (LinearMap.mem_ker.mp x.2)
  have hrange : Module.rank ℤ_[p] (LinearMap.range (padicLogLinear K p)) = d := by
    refine le_antisymm ?_ ?_
    · rw [← rank_valBallSubmodule (K := K) p (absRamificationIndex K + 1 -
        absRamificationIndex K * absRamificationIndex K)]
      exact Submodule.rank_mono (range_padicLogLinear_le p)
    · rw [← rank_valBallSubmodule (K := K) p ((absRamificationIndex K + 1 : ℕ) : ℤ)]
      exact Submodule.rank_mono (valBallSubmodule_le_range p)
  have h := (padicLogLinear K p).rank_range_add_rank_ker
  rw [hker, hrange, add_zero] at h
  rw [Module.finrank, ← h]
  simp

end Rank

end GroundTheory.LocalField
