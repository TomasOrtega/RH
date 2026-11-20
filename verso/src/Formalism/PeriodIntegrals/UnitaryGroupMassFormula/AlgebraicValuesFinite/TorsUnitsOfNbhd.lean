import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.EvFLocalIdeleSelf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.NormEqOneOfForallZpow
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.PowCardSubOneMem

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

namespace PI.AlgValsFin.W

def ufinSub (L : Type) [Field L] [NumberField L] : Subgroup (Ideles L) where
  carrier := UFin L
  one_mem' := ⟨rfl, fun v => by
    show Valued.v (1 : v.adicCompletion L) = 1
    exact map_one _⟩
  mul_mem' := fun {a b} ha hb => ⟨by
    change (a : AdeleRing (𝓞 L) L).1 * (b : AdeleRing (𝓞 L) L).1 = 1
    rw [ha.1, hb.1, mul_one],
    fun v => by rw [comp_mul, map_mul, ha.2 v, hb.2 v, mul_one]⟩
  inv_mem' := fun {a} ha => by
    refine ⟨?_, fun v => ?_⟩
    · have e : (a : AdeleRing (𝓞 L) L).1 * (a⁻¹ : Ideles L).val.1 = 1 := by
        change ((a * a⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).1 = 1
        rw [mul_inv_cancel]; rfl
      rw [ha.1, one_mul] at e
      exact e
    · have e := congrArg Valued.v (comp_mul_inv L a v)
      rw [map_mul, ha.2 v, one_mul, map_one] at e
      exact e

variable {L : Type} [Field L] [NumberField L]

/- English proof (translation)
Use `choose N hNpos hN using fun v : HeightOneSpectrum (𝓞 L) => exists_pow_close v n`. Use `⟨∏ v ∈ S, N v, Finset.prod_pos fun v _ => hNpos v, fun y hy v hv => ?_⟩` and prove the remaining obligations. Take `⟨r, hr⟩ : N v ∣ ∏ w ∈ S, N w` from `Finset.dvd_prod_of_mem N hv`. Establish `hcomp : ((y ^ (∏ w ∈ S, N w) : Ideles L) : AdeleRing (𝓞 L) L).2 v = ((y : AdeleRing (𝓞 L) L).2 v) ^ (∏ w ∈ S, N w)`. Rewrite using `[← evF_val, ← evF_val, map_pow, Units.val_pow_eq_pow_val]`.

Rewrite using `[hcomp, hr, pow_mul]`. Establish `hy1 : Valued.v ((y : AdeleRing (𝓞 L) L).2 v) = 1` using `hy.2 v`. Establish `hx1 : Valued.v (((y : AdeleRing (𝓞 L) L).2 v) ^ N v) ≤ 1`. Rewrite using `[map_pow, hy1, one_pow]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem pow_close (S : Finset (HeightOneSpectrum (𝓞 L))) (n : ℕ) :
    ∃ M : ℕ, 0 < M ∧ ∀ y ∈ UFin L, ∀ v ∈ S,
      Valued.v (((y ^ M : Ideles L) : AdeleRing (𝓞 L) L).2 v - 1) ≤ WithZero.exp (-(n : ℤ)) := by
  choose N hNpos hN using fun v : HeightOneSpectrum (𝓞 L) => exists_pow_close v n
  refine ⟨∏ v ∈ S, N v, Finset.prod_pos fun v _ => hNpos v, fun y hy v hv => ?_⟩
  obtain ⟨r, hr⟩ : N v ∣ ∏ w ∈ S, N w := Finset.dvd_prod_of_mem N hv
  have hcomp : ((y ^ (∏ w ∈ S, N w) : Ideles L) : AdeleRing (𝓞 L) L).2 v =
      ((y : AdeleRing (𝓞 L) L).2 v) ^ (∏ w ∈ S, N w) := by
    rw [← evF_val, ← evF_val, map_pow, Units.val_pow_eq_pow_val]
  rw [hcomp, hr, pow_mul]
  have hy1 : Valued.v ((y : AdeleRing (𝓞 L) L).2 v) = 1 := hy.2 v
  have hx1 : Valued.v (((y : AdeleRing (𝓞 L) L).2 v) ^ N v) ≤ 1 := by
    rw [map_pow, hy1, one_pow]
  calc Valued.v ((((y : AdeleRing (𝓞 L) L).2 v) ^ N v) ^ r - 1)
      = Valued.v ((((y : AdeleRing (𝓞 L) L).2 v) ^ N v) ^ r - 1 ^ r) := by rw [one_pow]
    _ ≤ Valued.v (((y : AdeleRing (𝓞 L) L).2 v) ^ N v - 1) :=
        val_pow_sub_le v hx1 (by rw [map_one]) r
    _ ≤ WithZero.exp (-(n : ℤ)) := hN v _ hy1

/- English proof (translation)
Introduce `χ`. Use `set W : Set (Ideles L) := χ.1 ⁻¹' {u : ℂˣ | ‖(u : ℂ) - 1‖ < 1} with hW`. Establish `hWo : IsOpen W`. Use `IsOpen.preimage χ.2.1 ?_` and prove the remaining obligations. Conclude with `isOpen_lt (continuous_norm.comp (Units.continuous_val.sub continuous_const)) continuous_const`.

Establish `hW1 : (1 : Ideles L) ∈ W`. Simplify using `[hW]`. Take `⟨S, n, hSn⟩` from `hnb W hWo hW1`. Take `⟨M, hM, hclose⟩` from `pow_close (L := L) S n`. Use `⟨M, hM, fun x hx => ?_⟩` and prove the remaining obligations.

Establish `hmem : ∀ k : ℤ, (x ^ k) ^ M ∈ W`. Introduce `k`. Establish `hk : x ^ k ∈ UFin L` using `(ufinSub L).zpow_mem hx k`. Establish `hkM : (x ^ k) ^ M ∈ UFin L` using `(ufinSub L).pow_mem hk M`. Conclude with `hSn _ hkM (fun v hv => hclose _ hk v hv)`.

Establish `hz : ((χ.1 (x ^ M) : ℂˣ) : ℂ) = 1`. Apply `eq_one_of_forall_zpow` to reduce the goal to its premises. Introduce `k`. Establish `e : ((χ.1 (x ^ M) : ℂˣ) : ℂ) ^ k = ((χ.1 ((x ^ k) ^ M) : ℂˣ) : ℂ)`. Rewrite using `[← Units.val_zpow_eq_zpow_val, ← map_zpow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]`.

Rewrite using `[e]`. Conclude with `hmem k`. Rewrite using `[← map_pow]`. Conclude with `Units.ext hz`.
-/
theorem torsUnits_of_nbhd (L : Type) [Field L] [NumberField L]
    (hnb : ∀ W : Set (Ideles L), IsOpen W → (1 : Ideles L) ∈ W →
      ∃ (S : Finset (HeightOneSpectrum (𝓞 L))) (n : ℕ), ∀ x ∈ UFin L,
        (∀ v ∈ S, Valued.v ((x : AdeleRing (𝓞 L) L).2 v - 1) ≤ WithZero.exp (-(n : ℤ))) → x ∈ W) :
    TorsUnits L := by
  intro χ
  set W : Set (Ideles L) := χ.1 ⁻¹' {u : ℂˣ | ‖(u : ℂ) - 1‖ < 1} with hW
  have hWo : IsOpen W := by
    refine IsOpen.preimage χ.2.1 ?_
    exact isOpen_lt (continuous_norm.comp (Units.continuous_val.sub continuous_const)) continuous_const
  have hW1 : (1 : Ideles L) ∈ W := by
    simp [hW]
  obtain ⟨S, n, hSn⟩ := hnb W hWo hW1
  obtain ⟨M, hM, hclose⟩ := pow_close (L := L) S n
  refine ⟨M, hM, fun x hx => ?_⟩
  have hmem : ∀ k : ℤ, (x ^ k) ^ M ∈ W := by
    intro k
    have hk : x ^ k ∈ UFin L := (ufinSub L).zpow_mem hx k
    have hkM : (x ^ k) ^ M ∈ UFin L := (ufinSub L).pow_mem hk M
    exact hSn _ hkM (fun v hv => hclose _ hk v hv)
  have hz : ((χ.1 (x ^ M) : ℂˣ) : ℂ) = 1 := by
    apply eq_one_of_forall_zpow
    intro k
    have e : ((χ.1 (x ^ M) : ℂˣ) : ℂ) ^ k = ((χ.1 ((x ^ k) ^ M) : ℂˣ) : ℂ) := by
      rw [← Units.val_zpow_eq_zpow_val, ← map_zpow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul,
        ← zpow_mul, mul_comm]
    rw [e]
    exact hmem k
  rw [← map_pow]
  exact Units.ext hz

end PI.AlgValsFin.W
