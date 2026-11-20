import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory.IntegralPowerScalar

/- English proof (translation)
Use `haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2`. Establish `h1 : IsAlgebraic ℚ_[l] c` using `IsAlgebraic.of_finite ℚ_[l] c`. Establish `h2 : IsAlgebraic ℤ_[l] c` using `(IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] ↥LL.1).2 h1`. Take `⟨y, hy, hint⟩` from `h2.exists_integral_multiple`. Use `⟨y.valuation, ?_⟩` and prove the remaining obligations.

Establish `hs` using `PadicInt.unitCoeff_spec hy`. Establish `hm : y • c ∈ OL LL` using `hint`. Establish `hm2` using `(OL LL).smul_mem hm (((PadicInt.unitCoeff hy)⁻¹ : ℤ_[l]ˣ) : ℤ_[l])`. Establish `he : (((PadicInt.unitCoeff hy)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) * y = (l : ℤ_[l]) ^ y.valuation`. Conclude with `(Units.inv_mul_eq_iff_eq_mul _).2 hs`.

Rewrite `hm2` using `[smul_smul, he, Algebra.smul_def, map_pow, map_natCast]`. Conclude with `hm2`.
-/
theorem exists_pow_mul_integral {l : ℕ} [Fact (Nat.Prime l)] (LL : FinExt l) (c : ↥LL.1) :
    ∃ n : ℕ, (l : ↥LL.1) ^ n * c ∈ OL LL := by
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have h1 : IsAlgebraic ℚ_[l] c := IsAlgebraic.of_finite ℚ_[l] c
  have h2 : IsAlgebraic ℤ_[l] c := (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] ↥LL.1).2 h1
  obtain ⟨y, hy, hint⟩ := h2.exists_integral_multiple
  refine ⟨y.valuation, ?_⟩
  have hs := PadicInt.unitCoeff_spec hy
  have hm : y • c ∈ OL LL := hint
  have hm2 := (OL LL).smul_mem hm (((PadicInt.unitCoeff hy)⁻¹ : ℤ_[l]ˣ) : ℤ_[l])
  have he : (((PadicInt.unitCoeff hy)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) * y = (l : ℤ_[l]) ^ y.valuation := by
    exact (Units.inv_mul_eq_iff_eq_mul _).2 hs
  rw [smul_smul, he, Algebra.smul_def, map_pow, map_natCast] at hm2
  exact hm2

/- English proof (translation)
Establish `h` using `T.L.T.smul_mem (⟨c, hc⟩ : ↥(OL LL)) hx`. Rewrite `h` using `[← algebraMap_smul ↥LL.1 (⟨c, hc⟩ : ↥(OL LL)) x]`. Conclude with `h`.
-/
theorem smul_mem_of_mem {l : ℕ} [Fact (Nat.Prime l)] {LL : FinExt l} (T : GlobalTheory.BKGal.QLat LL)
    {c : ↥LL.1} (hc : c ∈ OL LL) {x : T.V} (hx : x ∈ T.L.T) : c • x ∈ T.L.T := by
  have h := T.L.T.smul_mem (⟨c, hc⟩ : ↥(OL LL)) hx
  rw [← algebraMap_smul ↥LL.1 (⟨c, hc⟩ : ↥(OL LL)) x] at h
  exact h

/- English proof (translation)
Establish `hl : ∀ k : ℕ, (l : ↥LL.1) ^ k ∈ OL LL` using `fun k => pow_mem (natCast_mem (OL LL) l) k`. Establish `hv : v ∈ Submodule.span ↥LL.1 (T.L.T : Set T.V)`. Rewrite using `[T.L.span]`. Conclude with `Submodule.mem_top`. Proceed by induction on `hv using Submodule.span_induction with`.

Consider the case `mem x hx => exact ⟨0, by rw [pow_zero, one_smul]; exact hx⟩`. Consider the case `zero => exact ⟨0, by rw [smul_zero]; exact T.L.T.zero_mem⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨m, hm⟩` from `hx`. Take `⟨n, hn⟩` from `hy`.

Use `⟨m + n, ?_⟩` and prove the remaining obligations. Establish `h1` using `smul_mem_of_mem T (hl n) hm`. Establish `h2` using `smul_mem_of_mem T (hl m) hn`. Rewrite `h1` using `[smul_smul, ← pow_add, Nat.add_comm]`. Rewrite `h2` using `[smul_smul, ← pow_add]`.

Rewrite using `[smul_add]`. Conclude with `T.L.T.add_mem h1 h2`. Consider the case `smul c x _ hx`. Take `⟨m, hm⟩` from `hx`. Take `⟨n, hn⟩` from `exists_pow_mul_integral LL c`.

Use `⟨n + m, ?_⟩` and prove the remaining obligations. Establish `h` using `smul_mem_of_mem T hn hm`. Establish `e : (l : ↥LL.1) ^ (n + m) * c = (l : ↥LL.1) ^ n * c * (l : ↥LL.1) ^ m` using `by ring`. Establish `e2 : (l : ↥LL.1) ^ (n + m) • c • x = ((l : ↥LL.1) ^ n * c) • (l : ↥LL.1) ^ m • x` using `(smul_smul _ _ x).trans ((congrArg (fun a : ↥LL.1 => a • x) e).trans (smul_smul _ _ x).symm)`. Conclude with `Eq.mpr (congrArg (fun w : T.V => w ∈ T.L.T) e2) h`.
-/
theorem exists_pow_smul_mem {l : ℕ} [inst : Fact (Nat.Prime l)] {LL : FinExt l}
    (T : GlobalTheory.BKGal.QLat LL) (v : T.V) : ∃ n : ℕ, (l : ↥LL.1) ^ n • v ∈ T.L.T := by
  have hl : ∀ k : ℕ, (l : ↥LL.1) ^ k ∈ OL LL := fun k => pow_mem (natCast_mem (OL LL) l) k
  have hv : v ∈ Submodule.span ↥LL.1 (T.L.T : Set T.V) := by
    rw [T.L.span]; exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨0, by rw [pow_zero, one_smul]; exact hx⟩
  | zero => exact ⟨0, by rw [smul_zero]; exact T.L.T.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, hm⟩ := hx
    obtain ⟨n, hn⟩ := hy
    refine ⟨m + n, ?_⟩
    have h1 := smul_mem_of_mem T (hl n) hm
    have h2 := smul_mem_of_mem T (hl m) hn
    rw [smul_smul, ← pow_add, Nat.add_comm] at h1
    rw [smul_smul, ← pow_add] at h2
    rw [smul_add]
    exact T.L.T.add_mem h1 h2
  | smul c x _ hx =>
    obtain ⟨m, hm⟩ := hx
    obtain ⟨n, hn⟩ := exists_pow_mul_integral LL c
    refine ⟨n + m, ?_⟩
    have h := smul_mem_of_mem T hn hm
    have e : (l : ↥LL.1) ^ (n + m) * c = (l : ↥LL.1) ^ n * c * (l : ↥LL.1) ^ m := by ring
    have e2 : (l : ↥LL.1) ^ (n + m) • c • x = ((l : ↥LL.1) ^ n * c) • (l : ↥LL.1) ^ m • x :=
      (smul_smul _ _ x).trans ((congrArg (fun a : ↥LL.1 => a • x) e).trans (smul_smul _ _ x).symm)
    exact Eq.mpr (congrArg (fun w : T.V => w ∈ T.L.T) e2) h

end GlobalTheory.IntegralPowerScalar
