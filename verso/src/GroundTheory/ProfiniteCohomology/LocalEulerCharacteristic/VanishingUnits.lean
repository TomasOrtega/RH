import Mathlib
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.UnitsPower
import GroundTheory.LocalFields.UnitsBasic
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open GroundTheory.LocalField ValuativeRel IsLocalRing

section Group

variable {G : Type*} [CommGroup G]

/- English proof (translation)
Establish `hPn : P.Normal` using `Subgroup.normal_of_isMulCommutative P`. Establish `hq : ∀ a b : G, a * b⁻¹ ∈ P → (a : G ⧸ P) = b` using `fun a b h => by`. Rewrite using `[QuotientGroup.eq]`. Use `P.inv_mem h` as an intermediate fact. Rewrite `this` using `[mul_inv_rev, inv_inv, mul_comm]`. Then use the resulting hypothesis.

Use `set c := s x * x⁻¹ with hc`. Establish `hOs : ∀ e ∈ O, s e ∈ O` using `fun e he => by`. Use `O.mul_mem (hO e) he` as an intermediate fact. Rewrite `this` using `[inv_mul_cancel_right]`. Then use the resulting hypothesis. Establish `hcO : ∀ j : ℕ, s^[j] c ∈ O` using `fun j => by`.

Proceed by induction on `j with`. Consider the case `zero => exact hO x`. Consider the case `succ j ih => rw [Function.iterate_succ_apply']`. Conclude with `hOs _ ih`. Establish `hcj : ∀ j : ℕ, ((s^[j] c : G) : G ⧸ P) = c` using `fun j => by`.

Proceed by induction on `j with`. Consider the case `zero => rfl`. Consider the case `succ j ih => rw [Function.iterate_succ_apply', hq _ _ (hOP _ (hcO j)), ih]`. Establish `hsx : s x = x * c` using `by rw [hc, mul_comm (s x), mul_inv_cancel_left]`. Establish `hxj : ∀ j : ℕ, ((s^[j] x : G) : G ⧸ P) = (x : G ⧸ P) * (c : G ⧸ P) ^ j` using `fun j => by`.

Proceed by induction on `j with`. Consider the case `zero => simp`. Consider the case `succ j ih`. Rewrite using `[Function.iterate_succ_apply, hsx, iterate_map_mul, QuotientGroup.mk_mul, ih, hcj, pow_succ, mul_assoc]`. Establish `h1 : (c : G ⧸ P) ^ m = 1`.

Establish `h` using `hxj m`. Rewrite `h` using `[hsm]`. Conclude with `mul_left_cancel (h.symm.trans (mul_one _).symm)`. Establish `h2 : (c : G ⧸ P) ^ l = 1`. Rewrite using `[← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]`.

Conclude with `hPl c`. Establish `h3 : (c : G ⧸ P) = 1`. Establish `h` using `(pow_gcd_eq_one (a := (c : G ⧸ P))).2 ⟨h1, h2⟩`. Rewrite `h` using `[Nat.Coprime.gcd_eq_one hm, pow_one]`. Then use the resulting hypothesis. Conclude with `(QuotientGroup.eq_one_iff c).1 h3`.
-/
theorem mul_inv_mem_of_iterate_eq {l m : ℕ} (P O : Subgroup G) (s : G →* G)
    (hPl : ∀ y : G, y ^ l ∈ P) (hO : ∀ x : G, s x * x⁻¹ ∈ O)
    (hOP : ∀ e ∈ O, s e * e⁻¹ ∈ P) (hm : m.Coprime l) (hsm : ∀ x : G, s^[m] x = x) (x : G) :
    s x * x⁻¹ ∈ P := by
  have hPn : P.Normal := Subgroup.normal_of_isMulCommutative P
  have hq : ∀ a b : G, a * b⁻¹ ∈ P → (a : G ⧸ P) = b := fun a b h => by
    rw [QuotientGroup.eq]
    have := P.inv_mem h
    rwa [mul_inv_rev, inv_inv, mul_comm] at this
  set c := s x * x⁻¹ with hc
  have hOs : ∀ e ∈ O, s e ∈ O := fun e he => by
    have := O.mul_mem (hO e) he
    rwa [inv_mul_cancel_right] at this
  have hcO : ∀ j : ℕ, s^[j] c ∈ O := fun j => by
    induction j with
    | zero => exact hO x
    | succ j ih => rw [Function.iterate_succ_apply']; exact hOs _ ih
  have hcj : ∀ j : ℕ, ((s^[j] c : G) : G ⧸ P) = c := fun j => by
    induction j with
    | zero => rfl
    | succ j ih => rw [Function.iterate_succ_apply', hq _ _ (hOP _ (hcO j)), ih]
  have hsx : s x = x * c := by rw [hc, mul_comm (s x), mul_inv_cancel_left]
  have hxj : ∀ j : ℕ, ((s^[j] x : G) : G ⧸ P) = (x : G ⧸ P) * (c : G ⧸ P) ^ j := fun j => by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Function.iterate_succ_apply, hsx, iterate_map_mul, QuotientGroup.mk_mul, ih,
        hcj, pow_succ, mul_assoc]
  have h1 : (c : G ⧸ P) ^ m = 1 := by
    have h := hxj m
    rw [hsm] at h
    exact mul_left_cancel (h.symm.trans (mul_one _).symm)
  have h2 : (c : G ⧸ P) ^ l = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hPl c
  have h3 : (c : G ⧸ P) = 1 := by
    have h := (pow_gcd_eq_one (a := (c : G ⧸ P))).2 ⟨h1, h2⟩
    rwa [Nat.Coprime.gcd_eq_one hm, pow_one] at h
  exact (QuotientGroup.eq_one_iff c).1 h3

end Group

section LocalField

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/- English proof (translation)
Use `set s : Fˣ →* Fˣ := Units.map (σ : F →* F) with hs_def`. Establish `hs : ∀ x : Fˣ, ((s x : Fˣ) : F) = σ x` using `fun x => rfl`. Set `P : Subgroup Fˣ` to `(powMonoidHom l : Fˣ →* Fˣ).range`. Set `O : Subgroup Fˣ` to `{ carrier := {x | valuation F (x : F) = 1} one_mem' := by simp mul_mem' := fun {a b} ha hb => by`. Simplify using `only [Set.mem_ofPred_eq, Units.val_mul, map_mul] at ha hb ⊢`.

Rewrite using `[ha, hb, mul_one]`. Use the proof step `inv_mem' := fun {a} ha => by`. Simplify using `only [Set.mem_ofPred_eq, Units.val_inv_eq_inv_val, map_inv₀] at ha ⊢`. Rewrite using `[ha, inv_one] }`. Establish `hmemO : ∀ x : Fˣ, x ∈ O ↔ valuation F (x : F) = 1` using `fun x => Iff.rfl`.

Establish `hv0 : ∀ x : Fˣ, valuation F (x : F) ≠ 0` using `fun x => (valuation F).ne_zero_iff.2 x.ne_zero`. Establish `hO : ∀ x : Fˣ, s x * x⁻¹ ∈ O` using `fun x => by`. Rewrite using `[hmemO, Units.val_mul, hs, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hval, mul_inv_cancel₀ (hv0 x)]`. Establish `hOP : ∀ e ∈ O, s e * e⁻¹ ∈ P` using `fun e he => by`. Rewrite `he` using `[hmemO]`.

Use `set t := s e * e⁻¹ with ht`. Establish `htv : valuation F (t : F) = 1` using `(hmemO t).1 (hO e)`. Establish `ht1 : valuation F ((t : F) - 1) < 1`. Establish `e1 : (t : F) - 1 = (σ e - e) * (e : F)⁻¹`. Rewrite using `[ht, Units.val_mul, hs, Units.val_inv_eq_inv_val, sub_mul, mul_inv_cancel₀ e.ne_zero]`.

Rewrite using `[e1, map_mul, map_inv₀, he, inv_one, mul_one]`. Conclude with `hin _ he.le`. Establish `hnt : normalizedValuation F (t : F) = 1`. Rewrite using `[← map_one (normalizedValuation F), normalizedValuation_eq_iff, map_one]`. Conclude with `htv`.

Take `⟨t', ht'⟩` from `mem_range_unitsIncl_iff.2 hnt`. Establish `ht'F : ((t' : 𝒪[F]) : F) = t` using `by rw [← coe_unitsIncl, ht']`. Establish `hmem : t' ∈ unitFiltration F 1`. Rewrite using `[mem_unitFiltration, pow_one, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Introduce `hu`.

Establish `h1` using `valuation_unit hu.unit`. Rewrite `h1` using `[IsUnit.unit_spec]`. Establish `h2 : (((t' : 𝒪[F]) - 1 : 𝒪[F]) : F) = (t : F) - 1`. Use `push_cast`. Rewrite using `[ht'F]`.

Rewrite `h1` using `[h2]`. Conclude with `(lt_irrefl _ (h1 ▸ ht1))`. Take `⟨z, -, hz⟩` from `exists_pow_eq_of_mem_unitFiltration_one hl hmem`. Use `⟨unitsIncl F z, ?_⟩` and prove the remaining obligations. Rewrite using `[powMonoidHom_apply, ← map_pow, hz, ht']`.

Establish `hiter : ∀ (j : ℕ) (x : Fˣ), ((s^[j] x : Fˣ) : F) = σ^[j] (x : F)` using `fun j => by`. Proceed by induction on `j with`. Consider the case `zero => intro x`. Both sides reduce to the same expression. Consider the case `succ j ih`.

Introduce `x`. Rewrite using `[Function.iterate_succ_apply', Function.iterate_succ_apply', hs, ih]`. Establish `hsm : ∀ x : Fˣ, s^[m] x = x` using `fun x => Units.ext (by rw [hiter, hσm])`. Take `⟨y, hy⟩` from `mul_inv_mem_of_iterate_eq P O s (fun y => ⟨y, rfl⟩) hO hOP hm hsm u`. Use `⟨y, ?_⟩` and prove the remaining obligations.

Rewrite `hy` using `[powMonoidHom_apply]`. Rewrite using `[hy, mul_comm (s u), mul_inv_cancel_left]`.
-/
theorem exists_map_units_eq_mul_pow {l m : ℕ} (hl : (l : 𝓀[F]) ≠ 0) (σ : F ≃+* F)
    (hval : ∀ x : F, valuation F (σ x) = valuation F x)
    (hin : ∀ x : F, valuation F x ≤ 1 → valuation F (σ x - x) < 1)
    (hm : m.Coprime l) (hσm : ∀ x : F, σ^[m] x = x) (u : Fˣ) :
    ∃ y : Fˣ, Units.map (σ : F →* F) u = u * y ^ l := by
  set s : Fˣ →* Fˣ := Units.map (σ : F →* F) with hs_def
  have hs : ∀ x : Fˣ, ((s x : Fˣ) : F) = σ x := fun x => rfl
  let P : Subgroup Fˣ := (powMonoidHom l : Fˣ →* Fˣ).range
  let O : Subgroup Fˣ :=
    { carrier := {x | valuation F (x : F) = 1}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, Units.val_mul, map_mul] at ha hb ⊢
        rw [ha, hb, mul_one]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq, Units.val_inv_eq_inv_val, map_inv₀] at ha ⊢
        rw [ha, inv_one] }
  have hmemO : ∀ x : Fˣ, x ∈ O ↔ valuation F (x : F) = 1 := fun x => Iff.rfl
  have hv0 : ∀ x : Fˣ, valuation F (x : F) ≠ 0 := fun x => (valuation F).ne_zero_iff.2 x.ne_zero
  have hO : ∀ x : Fˣ, s x * x⁻¹ ∈ O := fun x => by
    rw [hmemO, Units.val_mul, hs, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hval,
      mul_inv_cancel₀ (hv0 x)]
  have hOP : ∀ e ∈ O, s e * e⁻¹ ∈ P := fun e he => by
    rw [hmemO] at he
    set t := s e * e⁻¹ with ht
    have htv : valuation F (t : F) = 1 := (hmemO t).1 (hO e)
    have ht1 : valuation F ((t : F) - 1) < 1 := by
      have e1 : (t : F) - 1 = (σ e - e) * (e : F)⁻¹ := by
        rw [ht, Units.val_mul, hs, Units.val_inv_eq_inv_val, sub_mul,
          mul_inv_cancel₀ e.ne_zero]
      rw [e1, map_mul, map_inv₀, he, inv_one, mul_one]
      exact hin _ he.le
    have hnt : normalizedValuation F (t : F) = 1 := by
      rw [← map_one (normalizedValuation F), normalizedValuation_eq_iff, map_one]
      exact htv
    obtain ⟨t', ht'⟩ := mem_range_unitsIncl_iff.2 hnt
    have ht'F : ((t' : 𝒪[F]) : F) = t := by rw [← coe_unitsIncl, ht']
    have hmem : t' ∈ unitFiltration F 1 := by
      rw [mem_unitFiltration, pow_one, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have h1 := valuation_unit hu.unit
      rw [IsUnit.unit_spec] at h1
      have h2 : (((t' : 𝒪[F]) - 1 : 𝒪[F]) : F) = (t : F) - 1 := by
        push_cast
        rw [ht'F]
      rw [h2] at h1
      exact (lt_irrefl _ (h1 ▸ ht1))
    obtain ⟨z, -, hz⟩ := exists_pow_eq_of_mem_unitFiltration_one hl hmem
    refine ⟨unitsIncl F z, ?_⟩
    rw [powMonoidHom_apply, ← map_pow, hz, ht']
  have hiter : ∀ (j : ℕ) (x : Fˣ), ((s^[j] x : Fˣ) : F) = σ^[j] (x : F) := fun j => by
    induction j with
    | zero => intro x; rfl
    | succ j ih =>
      intro x
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hs, ih]
  have hsm : ∀ x : Fˣ, s^[m] x = x := fun x => Units.ext (by rw [hiter, hσm])
  obtain ⟨y, hy⟩ := mul_inv_mem_of_iterate_eq P O s (fun y => ⟨y, rfl⟩) hO hOP hm hsm u
  refine ⟨y, ?_⟩
  rw [powMonoidHom_apply] at hy
  rw [hy, mul_comm (s u), mul_inv_cancel_left]

end LocalField

end GroundTheory.ProfCoh
