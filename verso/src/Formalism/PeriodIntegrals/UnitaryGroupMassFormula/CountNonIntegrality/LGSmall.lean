import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.LGDefs

noncomputable section

namespace PI.CntNotIntW

open NumberField IsDedekindDomain Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical ValuativeRel

/- English proof (translation)
Use `first`. Consider the case `exact one_ne_zero`. Consider the case `exact FractionalIdeal.one_ne_zero`.
-/
theorem oneFI_ne_zero (D : Formalism.BasicNotions.D7) :
    (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.F)) D.host.F) ≠ 0 := by
  first
  | exact one_ne_zero
  | exact FractionalIdeal.one_ne_zero

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `Fp _ _ _ _ x y hy`. Distinguish the cases in `hx : valuation Fp x = 0`. Conclude with `⟨0, by simp [hx]⟩`. Take `⟨n, hn⟩` from `exists_pow_lt₀ hy (Units.mk0 (valuation Fp x)⁻¹ (inv_ne_zero hx))`. Establish `hn' : valuation Fp y ^ n < (valuation Fp x)⁻¹` using `by rwa [Units.val_mk0] at hn`.

Use `⟨n, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_pow]`. Establish `hpos : 0 < valuation Fp x` using `zero_lt_iff.2 hx`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem small_powers_bound : PowSmall := by
  intro Fp _ _ _ _ x y hy
  by_cases hx : valuation Fp x = 0
  · exact ⟨0, by simp [hx]⟩
  · obtain ⟨n, hn⟩ := exists_pow_lt₀ hy (Units.mk0 (valuation Fp x)⁻¹ (inv_ne_zero hx))
    have hn' : valuation Fp y ^ n < (valuation Fp x)⁻¹ := by rwa [Units.val_mk0] at hn
    refine ⟨n, ?_⟩
    rw [map_mul, map_pow]
    have hpos : 0 < valuation Fp x := zero_lt_iff.2 hx
    calc valuation Fp y ^ n * valuation Fp x < (valuation Fp x)⁻¹ * valuation Fp x :=
          mul_lt_mul_of_pos_right hn' hpos
      _ = 1 := inv_mul_cancel₀ hx

/- English proof (translation)
Introduce `d hd`. Establish `h1` using `coeIdeal_differentIdeal (A := ℤ) (K := ℚ) (B := 𝓞 D.host.F) (L := D.host.F)`. Establish `hdmem : algebraMap (𝓞 D.host.F) D.host.F d ∈ (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.F)) D.host.F))⁻¹`. Rewrite using `[← h1]`. Conclude with `(FractionalIdeal.mem_coeIdeal _).mpr ⟨d, hd, rfl⟩`.

Establish `htmem : t ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.F)) D.host.F)`. Rewrite using `[FractionalIdeal.mem_dual (oneFI_ne_zero D)]`. Introduce `a ha`. Take `⟨a', rfl⟩` from `(FractionalIdeal.mem_one_iff _).mp ha`. Take `⟨n, hn⟩` from `ht a'`.

Use `⟨n, ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.traceForm_apply]`. Simplify using `using hn.symm`. Establish `hne : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.F)) D.host.F) ≠ 0` using `FractionalIdeal.dual_ne_zero ℤ ℚ (oneFI_ne_zero D)`. Establish `hprod` using `FractionalIdeal.mul_mem_mul htmem hdmem`.

Rewrite `hprod` using `[mul_inv_cancel₀ hne]`. Take `⟨y, hy⟩` from `(FractionalIdeal.mem_one_iff _).mp hprod`. Rewrite using `[← hy]`. Use `first`. Consider the case `exact RingOfIntegers.isIntegral_coe y`.

Consider the case `exact y.2`.
-/
theorem dual_mul_different_integral (D : Formalism.BasicNotions.D7) (t : D.host.F)
    (ht : ∀ a : 𝓞 D.host.F, ∃ n : ℤ, Algebra.trace ℚ D.host.F (t * a) = n) :
    ∀ d ∈ differentIdeal ℤ (𝓞 D.host.F), IsIntegral ℤ (t * algebraMap (𝓞 D.host.F) D.host.F d) := by
  intro d hd
  have h1 := coeIdeal_differentIdeal (A := ℤ) (K := ℚ) (B := 𝓞 D.host.F) (L := D.host.F)
  have hdmem : algebraMap (𝓞 D.host.F) D.host.F d ∈
      (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.F)) D.host.F))⁻¹ := by
    rw [← h1]
    exact (FractionalIdeal.mem_coeIdeal _).mpr ⟨d, hd, rfl⟩
  have htmem : t ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.F)) D.host.F) := by
    rw [FractionalIdeal.mem_dual (oneFI_ne_zero D)]
    intro a ha
    obtain ⟨a', rfl⟩ := (FractionalIdeal.mem_one_iff _).mp ha
    obtain ⟨n, hn⟩ := ht a'
    refine ⟨n, ?_⟩
    rw [Algebra.traceForm_apply]
    simpa using hn.symm
  have hne : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.F)) D.host.F) ≠ 0 :=
    FractionalIdeal.dual_ne_zero ℤ ℚ (oneFI_ne_zero D)
  have hprod := FractionalIdeal.mul_mem_mul htmem hdmem
  rw [mul_inv_cancel₀ hne] at hprod
  obtain ⟨y, hy⟩ := (FractionalIdeal.mem_one_iff _).mp hprod
  rw [← hy]
  first
  | exact RingOfIntegers.isIntegral_coe y
  | exact y.2

/- English proof (translation)
Use `first`. Consider the case `exact differentIdeal_ne_bot`. Consider the case `exact differentIdeal_ne_bot (K := ℚ) (L := D.host.F)`.
-/
theorem differentF_ne_bot (D : Formalism.BasicNotions.D7) : differentIdeal ℤ (𝓞 D.host.F) ≠ ⊥ := by
  first
  | exact differentIdeal_ne_bot
  | exact differentIdeal_ne_bot (K := ℚ) (L := D.host.F)

/- English proof (translation)
Introduce `D t ht m`. Establish `hinj : Function.Injective (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))` using `by first`. Consider the case `exact FaithfulSMul.algebraMap_injective _ _`. Consider the case `exact NoZeroSMulDivisors.algebraMap_injective _ _`. Consider the case `exact (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)).injective`.

Establish `hne : ddS D ≠ 0`. Unfold `ddS`. Rewrite using `[Ne, FractionalIdeal.coeIdeal_eq_zero, Ideal.map_eq_bot_iff_of_injective hinj]`. Conclude with `differentF_ne_bot D`. Establish `key : ∀ z ∈ Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F)), (t : D.host.E) * algebraMap (𝓞 D.host.E) D.host.E z ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)`.

Introduce `z hz`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨d, hd, rfl⟩` from `hx`. Establish `hint` using `(dual_mul_different_integral D t ht d hd).map (algebraMap D.host.F D.host.E).toIntAlgHom`.

Rewrite using `[FractionalIdeal.mem_one_iff]`. Use `⟨⟨_, hint⟩, ?_⟩` and prove the remaining obligations. Use `first`. Consider the case `rfl`. Consider the case `(simp [map_mul]; done)`.

Consider the case `(simp only [RingHom.toIntAlgHom_apply, map_mul]; rfl)`. Consider the case `zero`. Conclude with `(FractionalIdeal.mem_one_iff _).mpr ⟨0, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨w₁, hw₁⟩` from `(FractionalIdeal.mem_one_iff _).mp hx`.

Take `⟨w₂, hw₂⟩` from `(FractionalIdeal.mem_one_iff _).mp hy`. Conclude with `(FractionalIdeal.mem_one_iff _).mpr ⟨w₁ + w₂, by rw [map_add, hw₁, hw₂, map_add, mul_add]⟩`. Consider the case `smul a x _ hx`. Rewrite using `[smul_eq_mul, map_mul, mul_left_comm]`. Take `⟨w, hw⟩` from `(FractionalIdeal.mem_one_iff _).mp hx`.

Conclude with `(FractionalIdeal.mem_one_iff _).mpr ⟨a * w, by rw [map_mul, hw]⟩`. Establish `h1 : (t : D.host.E) ∈ (ddS D)⁻¹`. Rewrite using `[FractionalIdeal.mem_inv_iff hne]`. Introduce `y hy`. Unfold `ddS at hy`.

Take `⟨z, hz, rfl⟩` from `(FractionalIdeal.mem_coeIdeal _).mp hy`. Conclude with `key z hz`. Rewrite using `[zpow_neg, zpow_natCast, ← inv_pow]`. Proceed by induction on `m with`. Consider the case `zero`.

Rewrite using `[pow_zero, pow_zero]`. Use `first`. Consider the case `exact FractionalIdeal.one_mem_one _`. Consider the case `exact FractionalIdeal.one_mem_one`. Consider the case `succ n ih`.

Rewrite using `[pow_succ, pow_succ]`. Conclude with `FractionalIdeal.mul_mem_mul ih h1`.
-/
theorem dual_lattice_powers : DualPow := by
  intro D t ht m
  have hinj : Function.Injective (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) := by
    first
    | exact FaithfulSMul.algebraMap_injective _ _
    | exact NoZeroSMulDivisors.algebraMap_injective _ _
    | exact (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)).injective
  have hne : ddS D ≠ 0 := by
    unfold ddS
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero, Ideal.map_eq_bot_iff_of_injective hinj]
    exact differentF_ne_bot D
  have key : ∀ z ∈ Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F)),
      (t : D.host.E) * algebraMap (𝓞 D.host.E) D.host.E z ∈
        (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨d, hd, rfl⟩ := hx
      have hint := (dual_mul_different_integral D t ht d hd).map
        (algebraMap D.host.F D.host.E).toIntAlgHom
      rw [FractionalIdeal.mem_one_iff]
      refine ⟨⟨_, hint⟩, ?_⟩
      first
      | rfl
      | (simp [map_mul]; done)
      | (simp only [RingHom.toIntAlgHom_apply, map_mul]; rfl)
    | zero =>
      exact (FractionalIdeal.mem_one_iff _).mpr ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨w₁, hw₁⟩ := (FractionalIdeal.mem_one_iff _).mp hx
      obtain ⟨w₂, hw₂⟩ := (FractionalIdeal.mem_one_iff _).mp hy
      exact (FractionalIdeal.mem_one_iff _).mpr ⟨w₁ + w₂, by rw [map_add, hw₁, hw₂, map_add, mul_add]⟩
    | smul a x _ hx =>
      rw [smul_eq_mul, map_mul, mul_left_comm]
      obtain ⟨w, hw⟩ := (FractionalIdeal.mem_one_iff _).mp hx
      exact (FractionalIdeal.mem_one_iff _).mpr ⟨a * w, by rw [map_mul, hw]⟩
  have h1 : (t : D.host.E) ∈ (ddS D)⁻¹ := by
    rw [FractionalIdeal.mem_inv_iff hne]
    intro y hy
    unfold ddS at hy
    obtain ⟨z, hz, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hy
    exact key z hz
  rw [zpow_neg, zpow_natCast, ← inv_pow]
  induction m with
  | zero =>
    rw [pow_zero, pow_zero]
    first
    | exact FractionalIdeal.one_mem_one _
    | exact FractionalIdeal.one_mem_one
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact FractionalIdeal.mul_mem_mul ih h1

end PI.CntNotIntW
