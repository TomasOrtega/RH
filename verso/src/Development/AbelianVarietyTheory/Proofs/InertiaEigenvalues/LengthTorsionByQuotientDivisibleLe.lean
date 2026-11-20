import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory

/- English proof (translation)
Establish `hLfin : Module.length O (O ⧸ Ideal.span {a}) ≠ ⊤`. Rewrite using `[Module.length_ne_top_iff]`. Conclude with `isFiniteLength_quotient_span_singleton O (mem_nonZeroDivisors_of_ne_zero ha)`. Set `φ : Submodule.torsionBy O Z a →ₗ[O] Submodule.torsionBy O Q a` to `LinearMap.codRestrict (Submodule.torsionBy O Q a) (π ∘ₗ (Submodule.torsionBy O Z a).subtype) (fun z => by`. Rewrite using `[Submodule.mem_torsionBy_iff, LinearMap.comp_apply, Submodule.subtype_apply, ← map_smul, (Submodule.mem_torsionBy_iff _ _).mp z.2, map_zero])`.

Establish `hφ : Function.Surjective φ`. Introduce and unpack `⟨q, hq⟩`. Take `⟨z, rfl⟩` from `hs q`. Establish `h1 : π (a • z) = 0`. Rewrite using `[map_smul]`.

Conclude with `(Submodule.mem_torsionBy_iff _ _).mp hq`. Take `⟨y, hy0, hy⟩` from `hdiv a ha (a • z) h1`. Use `⟨⟨z - y, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.mem_torsionBy_iff, smul_sub, hy, sub_self]`. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `[φ, hy0]`. Establish `hexact` using `Module.length_eq_add_of_exact (LinearMap.ker φ).subtype φ (Submodule.subtype_injective _) hφ (LinearMap.exact_subtype_ker_map φ)`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Establish `hdvd_unit : ∀ c : O, ¬ ϖ ∣ c → IsUnit c`. Introduce `c hc`.

Assume the negation of the conclusion as `hnu`. Apply `hc` to reduce the goal to its premises. Establish `hmem` using `(IsLocalRing.mem_maximalIdeal c).mpr hnu`. Rewrite `hmem` using `[(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.mem_span_singleton]`. Conclude with `hmem`.

Take `⟨x, hx0, hxK, b, hb0, hbx⟩` from `htor`. Take `⟨m, u, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ`. Establish `hxm : ϖ ^ m • x = 0`. Rewrite `hbx` using `[mul_smul, ← Units.smul_def, smul_eq_zero_iff_eq]`. Conclude with `hbx`.

Establish `hex : ∃ j, ϖ ^ j • x = 0` using `⟨m, hxm⟩`. Establish `hj : ϖ ^ Nat.find hex • x = 0` using `Nat.find_spec hex`. Establish `hj0 : Nat.find hex ≠ 0`. Introduce `h`. Rewrite `hj` using `[h, pow_zero, one_smul]`.

Conclude with `hx0 hj`. Take `⟨i, hi⟩` from `Nat.exists_eq_succ_of_ne_zero hj0`. Establish `he0 : ϖ ^ i • x ≠ 0` using `Nat.find_min hex (by omega)`. Establish `hϖe : ϖ • (ϖ ^ i • x) = 0`. Rewrite `hj` using `[hi]`.

Rewrite using `[smul_smul, ← pow_succ']`. Conclude with `hj`. Establish `heK : π (ϖ ^ i • x) = 0` using `by rw [map_smul, hxK, smul_zero]`. Establish `hunit_e : ∀ w : O, IsUnit w → w • (ϖ ^ i • x) ≠ 0`. Introduce `w hw h`.

Conclude with `he0 ((hw.smul_eq_zero).mp h)`. Take `⟨n, v, hav⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ`. Establish `hadvd : ∀ c : O, a ∣ c ↔ ϖ ^ n ∣ c`. Introduce `c`. Rewrite using `[hav, Units.mul_left_dvd]`.

Choose the witnesses or unpack the hypotheses as in `⟨y₀, hy₀K, hy₀⟩ : ∃ y₀ : Z, π y₀ = 0 ∧ ∀ c : O, c • y₀ = 0 ↔ a ∣ c := by`. Consider the cases of `n with`. Consider the case `zero`. Use `⟨0, map_zero π, fun c => ?_⟩` and prove the remaining obligations. Rewrite using `[hadvd, pow_zero]`.

Simplify using the standard rewrite rules. Consider the case `succ n'`. Take `⟨y, hyK, hy⟩` from `hdiv (ϖ ^ n') (pow_ne_zero _ hϖ.ne_zero) _ heK`. Use `⟨y, hyK, fun c => ?_⟩` and prove the remaining obligations. Rewrite using `[hadvd]`.

Prove the components needed by the constructor for the conclusion. Introduce `hc`. Distinguish the cases in `hc0 : c = 0`. Rewrite using `[hc0]`. Conclude with `dvd_zero _`.

Take `⟨r, w, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc0 hϖ`. Distinguish the cases in `hr : n' + 1 ≤ r`. Conclude with `Dvd.dvd.mul_left (pow_dvd_pow ϖ hr) _`. It suffices to derive a contradiction. Take `⟨d, hd⟩ : ∃ d, n' = r + d` from `⟨n' - r, by omega⟩`.

Apply `hunit_e (w : O) w.isUnit` to reduce the goal to its premises. Establish `hmul : (w : O) * ϖ ^ n' = ϖ ^ d * ((w : O) * ϖ ^ r)` using `by rw [hd, pow_add]; ring`. Rewrite using `[← hy, smul_smul, hmul, mul_smul, hc, smul_zero]`. Introduce and unpack `⟨d, rfl⟩`. Establish `hmul : ϖ ^ (n' + 1) * d = d * ϖ * ϖ ^ n'` using `by ring`.

Rewrite using `[hmul, mul_smul, hy, mul_smul, hϖe, smul_zero]`. Establish `hy₀T : y₀ ∈ Submodule.torsionBy O Z a` using `(Submodule.mem_torsionBy_iff _ _).mpr ((hy₀ a).mpr dvd_rfl)`. Establish `hy₀ker : (⟨y₀, hy₀T⟩ : Submodule.torsionBy O Z a) ∈ LinearMap.ker φ`. Rewrite using `[LinearMap.mem_ker]`. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `[φ, hy₀K]`. Set `f : O →ₗ[O] LinearMap.ker φ` to `LinearMap.toSpanSingleton O _ ⟨⟨y₀, hy₀T⟩, hy₀ker⟩`. Establish `hker : Ideal.span {a} = LinearMap.ker f`. Use extensionality with `c`. Rewrite using `[LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, Ideal.mem_span_singleton, ← hy₀ c]`.

Simplify using `[Subtype.ext_iff]`. Establish `hK : Module.length O (O ⧸ Ideal.span {a}) ≤ Module.length O (LinearMap.ker φ)`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : Module.length O ↥(Submodule.torsionBy O Q a) + Module.length O (O ⧸ Ideal.span {a}) ≤ (k : ℕ∞) * Module.length O (O ⧸ Ideal.span {a}) + Module.length O (O ⧸ Ideal.span {a})`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `(ENat.add_le_add_iff_right hLfin).mp h2`.
-/
theorem length_torsionBy_quotient_divisible_le (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (Z Q : Type) [AddCommGroup Z] [Module O Z] [AddCommGroup Q]
    [Module O Q] (π : Z →ₗ[O] Q) (hs : Function.Surjective π)
    (hdiv : ∀ b : O, b ≠ 0 → ∀ x, π x = 0 → ∃ y, π y = 0 ∧ b • y = x)
    (htor : ∃ x, x ≠ 0 ∧ π x = 0 ∧ ∃ b : O, b ≠ 0 ∧ b • x = 0) (a : O) (ha : a ≠ 0) (k : ℕ)
    (hle : Module.length O ↥(Submodule.torsionBy O Z a) ≤
      ((k + 1 : ℕ) : ℕ∞) * Module.length O (O ⧸ Ideal.span {a})) :
    Module.length O ↥(Submodule.torsionBy O Q a) ≤
      (k : ℕ∞) * Module.length O (O ⧸ Ideal.span {a}) := by
  classical

  have hLfin : Module.length O (O ⧸ Ideal.span {a}) ≠ ⊤ := by
    rw [Module.length_ne_top_iff]
    exact isFiniteLength_quotient_span_singleton O (mem_nonZeroDivisors_of_ne_zero ha)

  let φ : Submodule.torsionBy O Z a →ₗ[O] Submodule.torsionBy O Q a :=
    LinearMap.codRestrict (Submodule.torsionBy O Q a) (π ∘ₗ (Submodule.torsionBy O Z a).subtype)
      (fun z => by
        rw [Submodule.mem_torsionBy_iff, LinearMap.comp_apply, Submodule.subtype_apply,
          ← map_smul, (Submodule.mem_torsionBy_iff _ _).mp z.2, map_zero])

  have hφ : Function.Surjective φ := by
    rintro ⟨q, hq⟩
    obtain ⟨z, rfl⟩ := hs q
    have h1 : π (a • z) = 0 := by
      rw [map_smul]; exact (Submodule.mem_torsionBy_iff _ _).mp hq
    obtain ⟨y, hy0, hy⟩ := hdiv a ha (a • z) h1
    refine ⟨⟨z - y, ?_⟩, ?_⟩
    · rw [Submodule.mem_torsionBy_iff, smul_sub, hy, sub_self]
    · apply Subtype.ext
      simp [φ, hy0]
  have hexact := Module.length_eq_add_of_exact (LinearMap.ker φ).subtype φ
    (Submodule.subtype_injective _) hφ (LinearMap.exact_subtype_ker_map φ)

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hdvd_unit : ∀ c : O, ¬ ϖ ∣ c → IsUnit c := by
    intro c hc
    by_contra hnu
    apply hc
    have hmem := (IsLocalRing.mem_maximalIdeal c).mpr hnu
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ,
      Ideal.mem_span_singleton] at hmem
    exact hmem
  obtain ⟨x, hx0, hxK, b, hb0, hbx⟩ := htor
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  have hxm : ϖ ^ m • x = 0 := by
    rw [mul_smul, ← Units.smul_def, smul_eq_zero_iff_eq] at hbx
    exact hbx
  have hex : ∃ j, ϖ ^ j • x = 0 := ⟨m, hxm⟩
  have hj : ϖ ^ Nat.find hex • x = 0 := Nat.find_spec hex
  have hj0 : Nat.find hex ≠ 0 := by
    intro h
    rw [h, pow_zero, one_smul] at hj
    exact hx0 hj
  obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero hj0
  have he0 : ϖ ^ i • x ≠ 0 := Nat.find_min hex (by omega)
  have hϖe : ϖ • (ϖ ^ i • x) = 0 := by
    rw [hi] at hj
    rw [smul_smul, ← pow_succ']; exact hj
  have heK : π (ϖ ^ i • x) = 0 := by rw [map_smul, hxK, smul_zero]
  have hunit_e : ∀ w : O, IsUnit w → w • (ϖ ^ i • x) ≠ 0 := by
    intro w hw h
    exact he0 ((hw.smul_eq_zero).mp h)
  obtain ⟨n, v, hav⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  have hadvd : ∀ c : O, a ∣ c ↔ ϖ ^ n ∣ c := by
    intro c; rw [hav, Units.mul_left_dvd]
  obtain ⟨y₀, hy₀K, hy₀⟩ : ∃ y₀ : Z, π y₀ = 0 ∧ ∀ c : O, c • y₀ = 0 ↔ a ∣ c := by
    cases n with
    | zero =>
      refine ⟨0, map_zero π, fun c => ?_⟩
      rw [hadvd, pow_zero]
      simp
    | succ n' =>
      obtain ⟨y, hyK, hy⟩ := hdiv (ϖ ^ n') (pow_ne_zero _ hϖ.ne_zero) _ heK
      refine ⟨y, hyK, fun c => ?_⟩
      rw [hadvd]
      constructor
      · intro hc
        by_cases hc0 : c = 0
        · rw [hc0]; exact dvd_zero _
        obtain ⟨r, w, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc0 hϖ
        by_cases hr : n' + 1 ≤ r
        · exact Dvd.dvd.mul_left (pow_dvd_pow ϖ hr) _
        · exfalso
          obtain ⟨d, hd⟩ : ∃ d, n' = r + d := ⟨n' - r, by omega⟩
          apply hunit_e (w : O) w.isUnit
          have hmul : (w : O) * ϖ ^ n' = ϖ ^ d * ((w : O) * ϖ ^ r) := by rw [hd, pow_add]; ring
          rw [← hy, smul_smul, hmul, mul_smul, hc, smul_zero]
      · rintro ⟨d, rfl⟩
        have hmul : ϖ ^ (n' + 1) * d = d * ϖ * ϖ ^ n' := by ring
        rw [hmul, mul_smul, hy, mul_smul, hϖe, smul_zero]
  have hy₀T : y₀ ∈ Submodule.torsionBy O Z a :=
    (Submodule.mem_torsionBy_iff _ _).mpr ((hy₀ a).mpr dvd_rfl)
  have hy₀ker : (⟨y₀, hy₀T⟩ : Submodule.torsionBy O Z a) ∈ LinearMap.ker φ := by
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    simp [φ, hy₀K]
  let f : O →ₗ[O] LinearMap.ker φ := LinearMap.toSpanSingleton O _ ⟨⟨y₀, hy₀T⟩, hy₀ker⟩
  have hker : Ideal.span {a} = LinearMap.ker f := by
    ext c
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, Ideal.mem_span_singleton, ← hy₀ c]
    simp [Subtype.ext_iff]
  have hK : Module.length O (O ⧸ Ideal.span {a}) ≤ Module.length O (LinearMap.ker φ) := by
    calc Module.length O (O ⧸ Ideal.span {a})
        = Module.length O (O ⧸ LinearMap.ker f) :=
          (Submodule.quotEquivOfEq _ _ hker).length_eq
      _ = Module.length O (LinearMap.range f) := f.quotKerEquivRange.length_eq
      _ ≤ Module.length O (LinearMap.ker φ) :=
          Module.length_le_of_injective (LinearMap.range f).subtype (Submodule.subtype_injective _)
  have h2 : Module.length O ↥(Submodule.torsionBy O Q a) + Module.length O (O ⧸ Ideal.span {a}) ≤
      (k : ℕ∞) * Module.length O (O ⧸ Ideal.span {a}) + Module.length O (O ⧸ Ideal.span {a}) := by
    calc _ ≤ Module.length O ↥(Submodule.torsionBy O Q a) + Module.length O (LinearMap.ker φ) := by
            gcongr
      _ = Module.length O ↥(Submodule.torsionBy O Z a) := by rw [hexact, add_comm]
      _ ≤ _ := hle
      _ = _ := by push_cast; ring
  exact (ENat.add_le_add_iff_right hLfin).mp h2

end GlobalTheory
