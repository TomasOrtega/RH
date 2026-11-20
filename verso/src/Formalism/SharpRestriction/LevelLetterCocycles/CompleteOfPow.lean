import Formalism.SharpRestriction.LevelLetterCocycles.RingConditionOfDeltaInvariants
import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf

noncomputable section

namespace Formalism.MainNotions.CrystallineLiftingInputs.OL

open Formalism.BasicNotions Formalism.BasicNotions.Loc IsLocalRing

/- English proof (translation)
Set `: WithIdeal R` to `⟨J⟩`. Establish `hJ : IsAdic J` using `rfl`. Establish `hJn : IsAdic (J ^ n)` using `is_ideal_adic_pow hJ hn`. Rewrite using `[hJ.isAdicComplete_iff]`. Conclude with `hJn.isAdicComplete_iff.mp h`.
-/
theorem complete_of_pow {R : Type*} [CommRing R] (J : Ideal R) {n : ℕ} (hn : 0 < n)
    (h : IsAdicComplete (J ^ n) R) : IsAdicComplete J R := by
  let : WithIdeal R := ⟨J⟩
  have hJ : IsAdic J := rfl
  have hJn : IsAdic (J ^ n) := is_ideal_adic_pow hJ hn
  rw [hJ.isAdicComplete_iff]
  exact hJn.isAdicComplete_iff.mp h

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Introduce `h`. Establish `h2` using `congrArg (fun x : ↥(OL LL) => (x : ↥LL.1)) h`. Simplify using `only [ZeroMemClass.coe_zero, SubringClass.coe_natCast] at h2`. Conclude with `(Fact.out : l.Prime).ne_zero (by exact_mod_cast h2)`.
-/
theorem l_ne_zero (LL : FinExt l) : ((l : ℕ) : ↥(OL LL)) ≠ 0 := by
  intro h
  have h2 := congrArg (fun x : ↥(OL LL) => (x : ↥LL.1)) h
  simp only [ZeroMemClass.coe_zero, SubringClass.coe_natCast] at h2
  exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast h2)

/- English proof (translation)
Introduce `hu`. Establish `h0` using `Formalism.MainNotions.LiftingTheory.zl_v_unit P LL hu.unit`. Establish `h1` using `Formalism.MainNotions.LiftingTheory.zl_v_pow P LL 1`. Rewrite `h0` using `[IsUnit.unit_spec, map_natCast]`. Rewrite `h1` using `[pow_one, h0]`.

Conclude with `absurd h1 (by simp)`.
-/
theorem l_not_unit (P : LocPrime l) (LL : FinExt l) : ¬ IsUnit ((l : ℕ) : ↥(OL LL)) := by
  intro hu
  have h0 := Formalism.MainNotions.LiftingTheory.zl_v_unit P LL hu.unit
  have h1 := Formalism.MainNotions.LiftingTheory.zl_v_pow P LL 1
  rw [IsUnit.unit_spec, map_natCast] at h0
  rw [pow_one, h0] at h1
  exact absurd h1 (by simp)

/- English proof (translation)
Set `` to `Formalism.MainNotions.LiftingTheory.lkd_local P LL`. Conclude with `(mem_maximalIdeal _).2 (mem_nonunits_iff.2 (l_not_unit P LL))`.
-/
theorem l_mem_max (P : LocPrime l) (LL : FinExt l) :
    letI := Formalism.MainNotions.LiftingTheory.lkd_local P LL
    ((l : ℕ) : ↥(OL LL)) ∈ maximalIdeal ↥(OL LL) := by
  let := Formalism.MainNotions.LiftingTheory.lkd_local P LL
  exact (mem_maximalIdeal _).2 (mem_nonunits_iff.2 (l_not_unit P LL))

/- English proof (translation)
Use `letI := Formalism.MainNotions.LiftingTheory.lkd_local P LL`. Establish `hfd : FiniteDimensional ℚ_[l] ↥LL.1` using `LL.2`. Establish `hded : IsDedekindDomain ↥(OL LL)` using `IsIntegralClosure.isDedekindDomain ℤ_[l] ℚ_[l] ↥LL.1 ↥(integralClosure ℤ_[l] ↥LL.1)`. Establish `hnf : ¬ IsField ↥(OL LL)` using `fun hf => by`. Establish `hm` using `l_mem_max P LL`.

Rewrite `hm` using `[isField_iff_maximalIdeal_eq.mp hf, Ideal.mem_bot]`. Conclude with `l_ne_zero LL hm`. Conclude with `((IsDiscreteValuationRing.TFAE _ hnf).out 0 2).mpr hded`.
-/
theorem OL_dvr (P : LocPrime l) (LL : FinExt l) : IsDiscreteValuationRing ↥(OL LL) := by
  letI := Formalism.MainNotions.LiftingTheory.lkd_local P LL
  have hfd : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have hded : IsDedekindDomain ↥(OL LL) :=
    IsIntegralClosure.isDedekindDomain ℤ_[l] ℚ_[l] ↥LL.1 ↥(integralClosure ℤ_[l] ↥LL.1)
  have hnf : ¬ IsField ↥(OL LL) := fun hf => by
    have hm := l_mem_max P LL
    rw [isField_iff_maximalIdeal_eq.mp hf, Ideal.mem_bot] at hm
    exact l_ne_zero LL hm
  exact ((IsDiscreteValuationRing.TFAE _ hnf).out 0 2).mpr hded

/- English proof (translation)
Use `letI := Formalism.MainNotions.LiftingTheory.lkd_local P LL`. Use `OL_dvr P LL` as an intermediate fact. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible ↥(OL LL)`. Establish `hl0 : Ideal.span {((l : ℕ) : ↥(OL LL))} ≠ ⊥`. Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`.

Conclude with `l_ne_zero LL`. Take `⟨e, he⟩` from `IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hl0 hϖ`. Establish `hC` using `Formalism.MainNotions.WachCoordinates.Br.complete_OL LL`. Rewrite `hC` using `[he, ← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq]`. Use `complete_of_pow _ (n := e) (Nat.pos_of_ne_zero ?_) hC` and prove the remaining obligations.

Introduce and unpack `rfl`. Rewrite `hC` using `[pow_zero, Ideal.one_eq_top]`. Conclude with `not_subsingleton _ hC.subsingleton`.
-/
theorem OL_complete_max (P : LocPrime l) (LL : FinExt l) :
    letI := Formalism.MainNotions.LiftingTheory.lkd_local P LL
    IsAdicComplete (maximalIdeal ↥(OL LL)) ↥(OL LL) := by
  letI := Formalism.MainNotions.LiftingTheory.lkd_local P LL
  have := OL_dvr P LL
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥(OL LL)
  have hl0 : Ideal.span {((l : ℕ) : ↥(OL LL))} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact l_ne_zero LL
  obtain ⟨e, he⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hl0 hϖ
  have hC := Formalism.MainNotions.WachCoordinates.Br.complete_OL LL
  rw [he, ← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq] at hC
  refine complete_of_pow _ (n := e) (Nat.pos_of_ne_zero ?_) hC
  rintro rfl
  rw [pow_zero, Ideal.one_eq_top] at hC
  exact not_subsingleton _ hC.subsingleton

end Formalism.MainNotions.CrystallineLiftingInputs.OL
