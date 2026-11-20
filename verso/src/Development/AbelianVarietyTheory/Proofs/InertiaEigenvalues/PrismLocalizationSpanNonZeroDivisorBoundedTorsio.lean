import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

/- English proof (translation)
Establish `hfg : I.FG` using `Module.Finite.iff_fg.1 inferInstance`. Take `⟨S, hS⟩` from `hfg`. Set `k : A → ℕ` to `fun x => if hx : x ∈ I then (h x hx).choose else 0`. Establish `hk : ∀ x ∈ I, f ^ k x * (c * x) = 0` using `fun x hx => by`. Simplify using `only [k, dif_pos hx]`.

Conclude with `(h x hx).choose_spec`. Use `⟨S.sup k, ?_⟩` and prove the remaining obligations. Establish `hle : I ≤ LinearMap.ker (LinearMap.mulLeft A (f ^ S.sup k * c))`. Rewrite using `[← hS, Submodule.span_le]`. Introduce `x hx`.

Establish `hxI : x ∈ I` using `hS ▸ Submodule.subset_span hx`. Establish `hkx : k x ≤ S.sup k` using `Finset.le_sup (f := k) hx`. Rewrite using `[SetLike.mem_coe, LinearMap.mem_ker, LinearMap.mulLeft_apply]`. Take `⟨j, hj⟩` from `Nat.exists_eq_add_of_le hkx`. Rewrite using `[hj, pow_add]`.

Take the linear combination `(f ^ j) * hk x hxI`. Apply `eq_of_smul_eq_smul (α := ↥I)` to reduce the goal to its premises. Introduce `y`. Use `hle y.2` as an intermediate fact. Rewrite `this` using `[LinearMap.mem_ker, LinearMap.mulLeft_apply]`.

Use `ext`. Simplify using `[this]`.
-/
theorem pow_mul_eq_zero_of_invertible {A : Type} [CommRing A] (I : Ideal A) (hI : Module.Invertible A ↥I)
    (f c : A) (h : ∀ x ∈ I, ∃ k : ℕ, f ^ k * (c * x) = 0) : ∃ K : ℕ, f ^ K * c = 0 := by
  classical
  have hfg : I.FG := Module.Finite.iff_fg.1 inferInstance
  obtain ⟨S, hS⟩ := hfg
  let k : A → ℕ := fun x => if hx : x ∈ I then (h x hx).choose else 0
  have hk : ∀ x ∈ I, f ^ k x * (c * x) = 0 := fun x hx => by
    simp only [k, dif_pos hx]; exact (h x hx).choose_spec
  refine ⟨S.sup k, ?_⟩
  have hle : I ≤ LinearMap.ker (LinearMap.mulLeft A (f ^ S.sup k * c)) := by
    rw [← hS, Submodule.span_le]
    intro x hx
    have hxI : x ∈ I := hS ▸ Submodule.subset_span hx
    have hkx : k x ≤ S.sup k := Finset.le_sup (f := k) hx
    rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.mulLeft_apply]
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hkx
    rw [hj, pow_add]
    linear_combination (f ^ j) * hk x hxI
  apply eq_of_smul_eq_smul (α := ↥I)
  intro y
  have := hle y.2
  rw [LinearMap.mem_ker, LinearMap.mulLeft_apply] at this
  ext
  simp [this]

/- English proof (translation)
Use `set φ := algebraMap B.A (Localization M) with hφ`. Establish `hu : IsUnit (φ f)` using `IsLocalization.map_units (Localization M) (⟨f, hf⟩ : M)`. Establish `h1 : B.I.map φ = Ideal.span {φ d}`. Use `le_antisymm ?_ ?_` and prove the remaining obligations. Rewrite using `[Ideal.map_le_iff_le_comap]`.

Introduce `x hx`. Take `⟨k, hk⟩` from `hG.2 x hx`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.1 hk`. Rewrite using `[Ideal.mem_comap, ← Ideal.unit_mul_mem_iff_mem _ (hu.pow k), ← map_pow, ← map_mul, ← hc, map_mul]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)`.

Rewrite using `[Ideal.span_le, Set.singleton_subset_iff]`. Conclude with `Ideal.mem_map_of_mem _ hG.1`. Use `⟨h1, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_nonZeroDivisors_iff_right]`. Introduce `x hx`.

Take `⟨⟨a, s⟩, rfl⟩` from `IsLocalization.mk'_surjective M x`. Rewrite `hx` using `[mul_comm, hφ, IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_zero_iff]`. Take `⟨t, ht⟩` from `hx`. Take `⟨K, hK⟩` from `pow_mul_eq_zero_of_invertible B.I B.inv f ((t : B.A) * a) (fun x hx => by`. Take `⟨k, hk⟩` from `hG.2 x hx`.

Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.1 hk`. Conclude with `⟨k, by linear_combination c * ht - (t : B.A) * a * hc⟩)`. Rewrite using `[IsLocalization.mk'_eq_zero_iff]`. Conclude with `⟨⟨f ^ K * t, M.mul_mem (M.pow_mem hf K) t.2⟩, by simp only; linear_combination hK⟩`. Take `⟨n, hn⟩` from `B.bdd`.

Use `⟨n, fun x m hx => ?_⟩` and prove the remaining obligations. Rewrite `hx`, the goal using `[← h1]`. Take `⟨⟨a, s⟩, rfl⟩` from `IsLocalization.mk'_surjective M x`. Establish `e : ∀ j : ℕ, (l : Localization M) ^ j * IsLocalization.mk' (Localization M) a s = IsLocalization.mk' (Localization M) ((l : B.A) ^ j * a) s` using `fun j => by`. Rewrite using `[← IsLocalization.mul_mk'_eq_mk'_of_mul, map_pow, map_natCast]`.

Rewrite `hx`, the goal using `[e, IsLocalization.mk'_mem_map_algebraMap_iff]`. Take `⟨s', hs', hI⟩` from `hx`. Use `⟨s', hs', ?_⟩` and prove the remaining obligations. Establish `h0 : (l : B.A ⧸ B.I) ^ m * Ideal.Quotient.mk B.I (s' * a) = 0`. Rewrite using `[← map_natCast (Ideal.Quotient.mk B.I), ← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]`.

Use `hI using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Establish `h2` using `hn _ ⟨m, h0⟩`. Rewrite `h2` using `[← map_natCast (Ideal.Quotient.mk B.I), ← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]`. Use `h2 using 1` and compare the differences between its conclusion and the goal.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem locAway_span_nzd_bdd (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B : Obj l R) (f d : B.A)
    (hG : GenAway B f d) (M : Submonoid B.A) (hf : f ∈ M) :
    B.I.map (algebraMap B.A (Localization M)) = Ideal.span {algebraMap B.A (Localization M) d} ∧
    algebraMap B.A (Localization M) d ∈ nonZeroDivisors (Localization M) ∧
    ∃ N : ℕ, ∀ (x : Localization M) (m : ℕ), (l : Localization M) ^ m * x ∈
      Ideal.span {algebraMap B.A (Localization M) d} →
      (l : Localization M) ^ N * x ∈ Ideal.span {algebraMap B.A (Localization M) d} := by
  set φ := algebraMap B.A (Localization M) with hφ
  have hu : IsUnit (φ f) := IsLocalization.map_units (Localization M) (⟨f, hf⟩ : M)
  have h1 : B.I.map φ = Ideal.span {φ d} := by
    refine le_antisymm ?_ ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      obtain ⟨k, hk⟩ := hG.2 x hx
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hk
      rw [Ideal.mem_comap, ← Ideal.unit_mul_mem_iff_mem _ (hu.pow k), ← map_pow, ← map_mul, ← hc, map_mul]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.mem_map_of_mem _ hG.1
  refine ⟨h1, ?_, ?_⟩
  · rw [mem_nonZeroDivisors_iff_right]
    intro x hx
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective M x
    rw [mul_comm, hφ, IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_zero_iff] at hx
    obtain ⟨t, ht⟩ := hx
    obtain ⟨K, hK⟩ := pow_mul_eq_zero_of_invertible B.I B.inv f ((t : B.A) * a) (fun x hx => by
      obtain ⟨k, hk⟩ := hG.2 x hx
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hk
      exact ⟨k, by linear_combination c * ht - (t : B.A) * a * hc⟩)
    rw [IsLocalization.mk'_eq_zero_iff]
    exact ⟨⟨f ^ K * t, M.mul_mem (M.pow_mem hf K) t.2⟩, by simp only; linear_combination hK⟩
  · obtain ⟨n, hn⟩ := B.bdd
    refine ⟨n, fun x m hx => ?_⟩
    rw [← h1] at hx ⊢
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective M x
    have e : ∀ j : ℕ, (l : Localization M) ^ j * IsLocalization.mk' (Localization M) a s =
        IsLocalization.mk' (Localization M) ((l : B.A) ^ j * a) s := fun j => by
      rw [← IsLocalization.mul_mk'_eq_mk'_of_mul, map_pow, map_natCast]
    rw [e, IsLocalization.mk'_mem_map_algebraMap_iff] at hx ⊢
    obtain ⟨s', hs', hI⟩ := hx
    refine ⟨s', hs', ?_⟩
    have h0 : (l : B.A ⧸ B.I) ^ m * Ideal.Quotient.mk B.I (s' * a) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk B.I), ← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      convert hI using 1; ring
    have h2 := hn _ ⟨m, h0⟩
    rw [← map_natCast (Ideal.Quotient.mk B.I), ← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at h2
    convert h2 using 1; ring

end GlobalTheory.BSP
