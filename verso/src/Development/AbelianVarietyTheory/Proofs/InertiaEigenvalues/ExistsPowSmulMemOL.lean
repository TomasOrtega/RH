import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar

namespace GlobalTheory.IntegerRingPowers

open Formalism.BasicNotions

/- English proof (translation)
Use `haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2`. Establish `hint : IsIntegral ℚ_[l] a` using `IsIntegral.of_finite ℚ_[l] a`. Take `⟨⟨m, hm⟩, hmi⟩` from `IsIntegral.exists_multiple_integral_of_isLocalization (nonZeroDivisors ℤ_[l]) a hint`. Establish `hm0 : m ≠ 0` using `nonZeroDivisors.ne_zero hm`. Use `⟨m.valuation, ?_⟩` and prove the remaining obligations.

Rewrite using `[Loc.OL, mem_integralClosure_iff]`. Establish `hmi' : IsIntegral ℤ_[l] (m • a)` using `hmi`. Establish `e` using `PadicInt.unitCoeff_spec hm0`. Use `set u := PadicInt.unitCoeff hm0`. Establish `key : (l : ↥LL.1) ^ m.valuation * a = ((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) • (m • a)` using `by conv_rhs => rw [e]`.

Rewrite using `[smul_smul, ← mul_assoc, Units.inv_mul, one_mul, Algebra.smul_def, map_pow, map_natCast]`. Rewrite using `[key]`. Conclude with `IsIntegral.smul _ hmi'`.
-/
theorem exists_pow_smul_mem_OL {l : ℕ} [Fact (Nat.Prime l)] (LL : Loc.FinExt l) (a : ↥LL.1) :
    ∃ n : ℕ, (l : ↥LL.1) ^ n * a ∈ Loc.OL LL := by
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have hint : IsIntegral ℚ_[l] a := IsIntegral.of_finite ℚ_[l] a
  obtain ⟨⟨m, hm⟩, hmi⟩ :=
    IsIntegral.exists_multiple_integral_of_isLocalization (nonZeroDivisors ℤ_[l]) a hint
  have hm0 : m ≠ 0 := nonZeroDivisors.ne_zero hm
  refine ⟨m.valuation, ?_⟩
  rw [Loc.OL, mem_integralClosure_iff]
  have hmi' : IsIntegral ℤ_[l] (m • a) := hmi
  have e := PadicInt.unitCoeff_spec hm0
  set u := PadicInt.unitCoeff hm0
  have key : (l : ↥LL.1) ^ m.valuation * a = ((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) • (m • a) := by
    conv_rhs => rw [e]
    rw [smul_smul, ← mul_assoc, Units.inv_mul, one_mul, Algebra.smul_def, map_pow, map_natCast]
  rw [key]
  exact IsIntegral.smul _ hmi'

/- English proof (translation)
Establish `h` using `T.L.T.smul_mem (⟨c, hc⟩ : ↥(Loc.OL LL)) hw`. Establish `e` using `T.towO.smul_assoc (⟨c, hc⟩ : ↥(Loc.OL LL)) (1 : ↥LL.1) w`. Establish `e2 : ((⟨c, hc⟩ : ↥(Loc.OL LL)) • (1 : ↥LL.1)) = c`. Rewrite using `[Algebra.smul_def, mul_one]`. Both sides reduce to the same expression.

Rewrite `e` using `[e2, one_smul]`. Rewrite using `[e]`. Conclude with `h`.
-/
theorem smul_mem_of_mem_OL {l : ℕ} [Fact (Nat.Prime l)] {K LL : Loc.FinExt l}
    (T : LocLat ↥(Loc.GK K) ℚ_[l] ↥LL.1 ↥(Loc.OL LL)) {c : ↥LL.1} (hc : c ∈ Loc.OL LL)
    {w : T.V} (hw : w ∈ T.L.T) : c • w ∈ T.L.T := by
  have h := T.L.T.smul_mem (⟨c, hc⟩ : ↥(Loc.OL LL)) hw
  have e := T.towO.smul_assoc (⟨c, hc⟩ : ↥(Loc.OL LL)) (1 : ↥LL.1) w
  have e2 : ((⟨c, hc⟩ : ↥(Loc.OL LL)) • (1 : ↥LL.1)) = c := by
    rw [Algebra.smul_def, mul_one]; rfl
  rw [e2, one_smul] at e
  rw [e]; exact h

/- English proof (translation)
The claim follows from `(Loc.OL LL).pow_mem ((Loc.OL LL).natCast_mem l) k`.
-/
theorem natCast_pow_mem_OL {l : ℕ} [Fact (Nat.Prime l)] (LL : Loc.FinExt l) (k : ℕ) :
    (l : ↥LL.1) ^ k ∈ Loc.OL LL :=
  (Loc.OL LL).pow_mem ((Loc.OL LL).natCast_mem l) k

/- English proof (translation)
Rewrite using `[pow_add, mul_smul, mul_smul]`. Use `congr 1`. Rewrite using `[← mul_smul, ← mul_smul, mul_comm]`.
-/
theorem pow_smul_smul_eq {l : ℕ} [Fact (Nat.Prime l)] {K LL : Loc.FinExt l}
    (T : LocLat ↥(Loc.GK K) ℚ_[l] ↥LL.1 ↥(Loc.OL LL)) (a : ↥LL.1) (x : T.V) (k n : ℕ) :
    (l : ↥LL.1) ^ (k + n) • a • x = ((l : ↥LL.1) ^ k * a) • ((l : ↥LL.1) ^ n • x) := by
  rw [pow_add, mul_smul, mul_smul]
  congr 1
  rw [← mul_smul, ← mul_smul, mul_comm]

/- English proof (translation)
Introduce `l _ K LL T v`. Establish `hv : v ∈ Submodule.span ↥LL.1 (T.L.T : Set T.V)`. Rewrite using `[T.L.span]`. Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hv using Submodule.span_induction with`.

Consider the case `mem x hx => exact ⟨0, by rw [pow_zero, one_smul]; exact hx⟩`. Consider the case `zero => exact ⟨0, by rw [smul_zero]; exact T.L.T.zero_mem⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨n, hn⟩` from `hx`. Take `⟨k, hk⟩` from `hy`.

Use `⟨n + k, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`. Use `T.L.T.add_mem ?_ ?_` and prove the remaining obligations. Rewrite using `[add_comm, pow_add, mul_smul]`. Conclude with `smul_mem_of_mem_OL T (natCast_pow_mem_OL LL k) hn`.

Rewrite using `[pow_add, mul_smul]`. Conclude with `smul_mem_of_mem_OL T (natCast_pow_mem_OL LL n) hk`. Consider the case `smul a x _ hx`. Take `⟨n, hn⟩` from `hx`. Take `⟨k, hk⟩` from `exists_pow_smul_mem_OL LL a`.

Use `⟨k + n, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_smul_smul_eq T a x k n]`. Conclude with `smul_mem_of_mem_OL T hk hn`.
-/
theorem main : ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] (K LL : Formalism.BasicNotions.Loc.FinExt l)
    (T : Formalism.BasicNotions.LocLat ↥(Formalism.BasicNotions.Loc.GK K) ℚ_[l]
      ↥(↑LL : IntermediateField ℚ_[l] (Formalism.BasicNotions.Loc.Om l)) ↥(Formalism.BasicNotions.Loc.OL LL))
    (v : Formalism.BasicNotions.LocLat.V T),
    ∃ (n : ℕ), (↑l : ↥(↑LL : IntermediateField ℚ_[l] (Formalism.BasicNotions.Loc.Om l))) ^ n • v ∈
      Formalism.WeaklyAdmissibleFiltrations.Lattice.T (Formalism.BasicNotions.LocLat.L T) := by
  intro l _ K LL T v
  have hv : v ∈ Submodule.span ↥LL.1 (T.L.T : Set T.V) := by
    rw [T.L.span]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨0, by rw [pow_zero, one_smul]; exact hx⟩
  | zero => exact ⟨0, by rw [smul_zero]; exact T.L.T.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨k, hk⟩ := hy
    refine ⟨n + k, ?_⟩
    rw [smul_add]
    refine T.L.T.add_mem ?_ ?_
    · rw [add_comm, pow_add, mul_smul]
      exact smul_mem_of_mem_OL T (natCast_pow_mem_OL LL k) hn
    · rw [pow_add, mul_smul]
      exact smul_mem_of_mem_OL T (natCast_pow_mem_OL LL n) hk
  | smul a x _ hx =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨k, hk⟩ := exists_pow_smul_mem_OL LL a
    refine ⟨k + n, ?_⟩
    rw [pow_smul_smul_eq T a x k n]
    exact smul_mem_of_mem_OL T hk hn

end GlobalTheory.IntegerRingPowers
