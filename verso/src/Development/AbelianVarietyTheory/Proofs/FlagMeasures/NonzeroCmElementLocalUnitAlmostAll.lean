import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.UnitAlmostAll

variable {D : D7}

/- English proof (translation)
Establish `: Algebra.IsAlgebraic ℤ ℚ` using `IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)`. Establish `: Algebra.IsAlgebraic ℤ D.host.E` using `Algebra.IsAlgebraic.trans ℤ ℚ D.host.E`. Take `⟨y, hy0, hy⟩` from `(Algebra.IsAlgebraic.isAlgebraic (R := ℤ) x).exists_integral_multiple`. Use `⟨y.natAbs * y.natAbs, by simpa using hy0, ?_⟩` and prove the remaining obligations. Establish `hsq : ((y.natAbs * y.natAbs : ℕ) : ℤ) = y * y`.

Rewrite using `[Nat.cast_mul]`. Conclude with `Int.natAbs_mul_self' y`. Establish `e : ((y.natAbs * y.natAbs : ℕ) : D.host.E) * x = (y : D.host.E) * (y • x)`. Rewrite using `[zsmul_eq_mul, ← mul_assoc]`. Establish `hc : ((y.natAbs * y.natAbs : ℕ) : D.host.E) = (((y.natAbs * y.natAbs : ℕ) : ℤ) : D.host.E)` using `(Int.cast_natCast _).symm`.

Rewrite using `[hc, hsq, Int.cast_mul]`. Rewrite using `[e]`. Establish `hyi : IsIntegral ℤ (y : D.host.E)`. Simplify using `using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ D.host.E y))`. Conclude with `hyi.mul hy`.
-/
theorem exists_nat_mul_integral (x : D.host.E) : ∃ n : ℕ, n ≠ 0 ∧ IsIntegral ℤ ((n : D.host.E) * x) := by
  have : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  have : Algebra.IsAlgebraic ℤ D.host.E := Algebra.IsAlgebraic.trans ℤ ℚ D.host.E
  obtain ⟨y, hy0, hy⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) x).exists_integral_multiple

  refine ⟨y.natAbs * y.natAbs, by simpa using hy0, ?_⟩
  have hsq : ((y.natAbs * y.natAbs : ℕ) : ℤ) = y * y := by
    rw [Nat.cast_mul]
    exact Int.natAbs_mul_self' y
  have e : ((y.natAbs * y.natAbs : ℕ) : D.host.E) * x = (y : D.host.E) * (y • x) := by
    rw [zsmul_eq_mul, ← mul_assoc]
    have hc : ((y.natAbs * y.natAbs : ℕ) : D.host.E) = (((y.natAbs * y.natAbs : ℕ) : ℤ) : D.host.E) :=
      (Int.cast_natCast _).symm
    rw [hc, hsq, Int.cast_mul]
  rw [e]
  have hyi : IsIntegral ℤ (y : D.host.E) := by
    simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ D.host.E y))
  exact hyi.mul hy

/- English proof (translation)
Rewrite using `[Formalism.L2.SG.Pf.LocFacts.lf_hO Z p, (D.s.atP p).O_def]`. Establish `: CharZero (D.s.atP p).Fp` using `(D.s.atP p).char0`. Establish `hn0 : n ≠ 0`. Introduce and unpack `rfl`. Conclude with `hn (by simp)`.

Establish `hcn : (D.s.atP p).ιF (n : D.host.F) = (n : (D.s.atP p).Fp)` using `map_natCast _ n`. Establish `hc0 : (n : (D.s.atP p).Fp) ≠ 0` using `by exact_mod_cast hn0`. Establish `hv : p.valuation D.host.F (n : D.host.F) = 1`. Use `(IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem (v := p) (K := D.host.F) (r := (n : 𝓞 D.host.F))).mpr hn` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis.

Establish `hle : (1 : (D.s.atP p).Fp) ≤ᵥ (n : (D.s.atP p).Fp)`. Use `((D.s.atP p).val 1 (n : D.host.F)).mpr (by rw [hv, map_one])` as an intermediate fact. Rewrite `this` using `[map_one, hcn]`. Then use the resulting hypothesis. Establish `hinv : (n : (D.s.atP p).Fp)⁻¹ ∈ (ValuativeRel.valuation (D.s.atP p).Fp).integer`. Rewrite using `[Valuation.mem_integer_iff, map_inv₀]`.

Establish `h1` using `(Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation (D.s.atP p).Fp) 1 (n : (D.s.atP p).Fp)).mp hle`. Rewrite `h1` using `[map_one]`. Conclude with `inv_le_one_of_one_le₀ h1`. Establish `hx : (D.s.atP p).ιE x = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (n : (D.s.atP p).Fp)⁻¹ * (D.s.atP p).ιE ((n : D.host.E) * x)`. Establish `hE : (n : D.host.E) = algebraMap D.host.F D.host.E (n : D.host.F)` using `(map_natCast _ n).symm`.

Rewrite using `[map_mul, hE, (D.s.atP p).compat, hcn, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_mul]`. Rewrite using `[hx]`. Use `IsIntegral.mul ?_ ?_` and prove the remaining obligations. Conclude with `isIntegral_algebraMap (R := (ValuativeRel.valuation (D.s.atP p).Fp).integer) (x := ⟨(n : (D.s.atP p).Fp)⁻¹, hinv⟩)`. Conclude with `(hint.map (D.s.atP p).ιE.toIntAlgHom).tower_top`.
-/
theorem iota_mem_O (Z : LocDat D) (p : PlF D) (x : D.host.E) (n : ℕ)
    (hint : IsIntegral ℤ ((n : D.host.E) * x)) (hn : ¬ ((n : 𝓞 D.host.F) ∈ p.asIdeal)) :
    (D.s.atP p).ιE x ∈ (Z.M p).L.O := by
  rw [Formalism.L2.SG.Pf.LocFacts.lf_hO Z p, (D.s.atP p).O_def]
  have : CharZero (D.s.atP p).Fp := (D.s.atP p).char0
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn (by simp)
  have hcn : (D.s.atP p).ιF (n : D.host.F) = (n : (D.s.atP p).Fp) := map_natCast _ n
  have hc0 : (n : (D.s.atP p).Fp) ≠ 0 := by exact_mod_cast hn0

  have hv : p.valuation D.host.F (n : D.host.F) = 1 := by
    have := (IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem
      (v := p) (K := D.host.F) (r := (n : 𝓞 D.host.F))).mpr hn
    rwa [map_natCast] at this
  have hle : (1 : (D.s.atP p).Fp) ≤ᵥ (n : (D.s.atP p).Fp) := by
    have := ((D.s.atP p).val 1 (n : D.host.F)).mpr (by rw [hv, map_one])
    rwa [map_one, hcn] at this
  have hinv : (n : (D.s.atP p).Fp)⁻¹ ∈ (ValuativeRel.valuation (D.s.atP p).Fp).integer := by
    rw [Valuation.mem_integer_iff, map_inv₀]
    have h1 := (Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation (D.s.atP p).Fp) 1
      (n : (D.s.atP p).Fp)).mp hle
    rw [map_one] at h1
    exact inv_le_one_of_one_le₀ h1
  have hx : (D.s.atP p).ιE x = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (n : (D.s.atP p).Fp)⁻¹ *
      (D.s.atP p).ιE ((n : D.host.E) * x) := by
    have hE : (n : D.host.E) = algebraMap D.host.F D.host.E (n : D.host.F) := (map_natCast _ n).symm
    rw [map_mul, hE, (D.s.atP p).compat, hcn, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_mul]
  rw [hx]
  refine IsIntegral.mul ?_ ?_
  · exact isIntegral_algebraMap (R := (ValuativeRel.valuation (D.s.atP p).Fp).integer) (x := ⟨(n : (D.s.atP p).Fp)⁻¹, hinv⟩)
  · exact (hint.map (D.s.atP p).ιE.toIntAlgHom).tower_top

/- English proof (translation)
Introduce `D Z x hx`. Take `⟨n, hn0, hn⟩` from `exists_nat_mul_integral x`. Take `⟨m, hm0, hm⟩` from `exists_nat_mul_integral x⁻¹`. Establish `hI : Ideal.span {((n * m : ℕ) : 𝓞 D.host.F)} ≠ 0`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`.

Conclude with `Nat.mul_ne_zero hn0 hm0` after adjusting the coercions. Use `(Ideal.finite_factors hI).subset ?_` and prove the remaining obligations. Introduce `p hp`. Simplify using `only [Set.mem_ofPred_eq] at hp ⊢`. Rewrite using `[Ideal.dvd_span_singleton]`.

Assume the negation of the conclusion as `hnm`. Apply `hp` to reduce the goal to its premises. Establish `hn' : ¬ ((n : 𝓞 D.host.F) ∈ p.asIdeal)` using `fun h => hnm (by`. Use `push_cast`. Conclude with `Ideal.mul_mem_right _ _ h)`.

Establish `hm' : ¬ ((m : 𝓞 D.host.F) ∈ p.asIdeal)` using `fun h => hnm (by`. Use `push_cast`. Conclude with `Ideal.mul_mem_left _ _ h)`. Use `⟨iota_mem_O Z p x n hn hn', (D.s.atP p).ιE x⁻¹, iota_mem_O Z p x⁻¹ m hm hm', ?_⟩` and prove the remaining obligations. Rewrite using `[← map_mul, mul_inv_cancel₀ hx, map_one]`.
-/
theorem unit_almost_all : ∀ (D : D7) (Z : LocDat D) (x : D.host.E), x ≠ 0 →
    {p : PlF D | ¬ Formalism.MainNotions.S.LocNG.IsUnitO (Z.M p) ((D.s.atP p).ιE x)}.Finite := by
  intro D Z x hx
  obtain ⟨n, hn0, hn⟩ := exists_nat_mul_integral x
  obtain ⟨m, hm0, hm⟩ := exists_nat_mul_integral x⁻¹

  have hI : Ideal.span {((n * m : ℕ) : 𝓞 D.host.F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast Nat.mul_ne_zero hn0 hm0
  refine (Ideal.finite_factors hI).subset ?_
  intro p hp
  simp only [Set.mem_ofPred_eq] at hp ⊢
  rw [Ideal.dvd_span_singleton]
  by_contra hnm
  apply hp
  have hn' : ¬ ((n : 𝓞 D.host.F) ∈ p.asIdeal) := fun h => hnm (by
    push_cast
    exact Ideal.mul_mem_right _ _ h)
  have hm' : ¬ ((m : 𝓞 D.host.F) ∈ p.asIdeal) := fun h => hnm (by
    push_cast
    exact Ideal.mul_mem_left _ _ h)
  refine ⟨iota_mem_O Z p x n hn hn', (D.s.atP p).ιE x⁻¹, iota_mem_O Z p x⁻¹ m hm hm', ?_⟩
  rw [← map_mul, mul_inv_cancel₀ hx, map_one]

end GlobalTheory.UnitAlmostAll
