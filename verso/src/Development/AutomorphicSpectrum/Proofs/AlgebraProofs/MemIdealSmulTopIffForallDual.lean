import Mathlib

open MeasureTheory NumberField Matrix Filter Topology
open scoped Pointwise ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Cmp

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx φ`. Establish `hle : 𝔟 • (⊤ : Submodule O L) ≤ Submodule.comap φ 𝔟`. Rewrite using `[Submodule.smul_le]`. Introduce `r hr n _`.

Rewrite using `[Submodule.mem_comap, map_smul, smul_eq_mul]`. Conclude with `Ideal.mul_mem_right _ _ hr`. Conclude with `hle hx`. Introduce `h`. Take `⟨s, hs⟩` from `Module.Projective.out (R := O) (P := L)`.

Rewrite using `[← hs x, Finsupp.linearCombination_apply, Finsupp.sum]`. Use `sum_mem fun y _ => ?_` and prove the remaining obligations. Establish `hy : (s x) y ∈ 𝔟`. Simplify using `using h ((Finsupp.lapply y).comp s)`. Conclude with `Submodule.smul_mem_smul hy Submodule.mem_top`.
-/
theorem mem_ideal_smul_top_iff_forall_dual {O : Type*} [CommRing O] {L : Type*} [AddCommGroup L]
    [Module O L] [Module.Finite O L] [Module.Projective O L] (𝔟 : Ideal O) (x : L) :
    x ∈ 𝔟 • (⊤ : Submodule O L) ↔ ∀ φ : L →ₗ[O] O, φ x ∈ 𝔟 := by
  constructor
  · intro hx φ
    have hle : 𝔟 • (⊤ : Submodule O L) ≤ Submodule.comap φ 𝔟 := by
      rw [Submodule.smul_le]
      intro r hr n _
      rw [Submodule.mem_comap, map_smul, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ hr
    exact hle hx
  · intro h
    obtain ⟨s, hs⟩ := Module.Projective.out (R := O) (P := L)
    rw [← hs x, Finsupp.linearCombination_apply, Finsupp.sum]
    refine sum_mem fun y _ => ?_
    have hy : (s x) y ∈ 𝔟 := by
      simpa using h ((Finsupp.lapply y).comp s)
    exact Submodule.smul_mem_smul hy Submodule.mem_top

/- English proof (translation)
Establish `h0 : 𝔪 ≠ 0` using `by rwa [Ne, Ideal.zero_eq_bot]`. Establish `hle : 𝔪 * Ideal.span {c} ≤ 𝔪 * 𝔞`. Rewrite using `[Ideal.mul_le]`. Introduce `r hr s hs`. Take `⟨t, rfl⟩` from `Ideal.mem_span_singleton.mp hs`.

Rewrite using `[← mul_assoc]`. Conclude with `Ideal.mul_mem_right _ _ (h r hr)`. Establish `hd : 𝔪 * 𝔞 ∣ 𝔪 * Ideal.span {c}` using `Ideal.dvd_iff_le.mpr hle`. Rewrite `hd` using `[mul_dvd_mul_iff_left h0]`. Conclude with `(Ideal.dvd_iff_le.mp hd) (Ideal.mem_span_singleton_self c)`.
-/
theorem mem_of_forall_mul_mem_ideal_mul {O : Type*} [CommRing O] [IsDedekindDomain O]
    {𝔪 𝔞 : Ideal O} (h𝔪 : 𝔪 ≠ ⊥) {c : O} (h : ∀ m ∈ 𝔪, m * c ∈ 𝔪 * 𝔞) : c ∈ 𝔞 := by
  have h0 : 𝔪 ≠ 0 := by rwa [Ne, Ideal.zero_eq_bot]
  have hle : 𝔪 * Ideal.span {c} ≤ 𝔪 * 𝔞 := by
    rw [Ideal.mul_le]
    intro r hr s hs
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton.mp hs
    rw [← mul_assoc]
    exact Ideal.mul_mem_right _ _ (h r hr)
  have hd : 𝔪 * 𝔞 ∣ 𝔪 * Ideal.span {c} := Ideal.dvd_iff_le.mpr hle
  rw [mul_dvd_mul_iff_left h0] at hd
  exact (Ideal.dvd_iff_le.mp hd) (Ideal.mem_span_singleton_self c)

/- English proof (translation)
Introduce `O _ _ L _ _ _ _ 𝔪 𝔞 T h𝔪`. Prove the components needed by the constructor for the conclusion. Introduce `hT x`. Rewrite using `[mem_ideal_smul_top_iff_forall_dual]`. Introduce `φ`.

Use `mem_of_forall_mul_mem_ideal_mul h𝔪 fun m hm => ?_` and prove the remaining obligations. Establish `hmx : m • x ∈ 𝔪 • (⊤ : Submodule O L)` using `Submodule.smul_mem_smul hm Submodule.mem_top`. Establish `key` using `(mem_ideal_smul_top_iff_forall_dual (𝔪 * 𝔞) (T (m • x))).mp (hT _ hmx) φ`. Rewrite `key` using `[map_smul, map_smul, smul_eq_mul]`. Then use the resulting hypothesis. Introduce `hT x hx`.

Establish `hle : 𝔪 • (⊤ : Submodule O L) ≤ Submodule.comap T ((𝔪 * 𝔞) • (⊤ : Submodule O L))`. Rewrite using `[Submodule.smul_le]`. Introduce `r hr n _`. Rewrite using `[Submodule.mem_comap, map_smul, mem_ideal_smul_top_iff_forall_dual]`. Introduce `φ`.

Rewrite using `[map_smul, smul_eq_mul]`. Conclude with `Ideal.mul_mem_mul hr ((mem_ideal_smul_top_iff_forall_dual 𝔞 (T n)).mp (hT n) φ)`. Conclude with `hle hx`.
-/
theorem map_ideal_smul_top_iff_cancel : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] (L : Type) [AddCommGroup L] [Module O L] [Module.Finite O L] [Module.Projective O L] (𝔪 𝔞 : Ideal O) (T : L →ₗ[O] L), 𝔪 ≠ ⊥ → ((∀ x ∈ 𝔪 • (⊤ : Submodule O L), T x ∈ (𝔪 * 𝔞) • (⊤ : Submodule O L)) ↔ ∀ x, T x ∈ 𝔞 • (⊤ : Submodule O L)) := by
  intro O _ _ L _ _ _ _ 𝔪 𝔞 T h𝔪
  constructor
  · intro hT x
    rw [mem_ideal_smul_top_iff_forall_dual]
    intro φ
    refine mem_of_forall_mul_mem_ideal_mul h𝔪 fun m hm => ?_
    have hmx : m • x ∈ 𝔪 • (⊤ : Submodule O L) := Submodule.smul_mem_smul hm Submodule.mem_top
    have key := (mem_ideal_smul_top_iff_forall_dual (𝔪 * 𝔞) (T (m • x))).mp (hT _ hmx) φ
    rwa [map_smul, map_smul, smul_eq_mul] at key
  · intro hT x hx
    have hle : 𝔪 • (⊤ : Submodule O L) ≤ Submodule.comap T ((𝔪 * 𝔞) • (⊤ : Submodule O L)) := by
      rw [Submodule.smul_le]
      intro r hr n _
      rw [Submodule.mem_comap, map_smul, mem_ideal_smul_top_iff_forall_dual]
      intro φ
      rw [map_smul, smul_eq_mul]
      exact Ideal.mul_mem_mul hr ((mem_ideal_smul_top_iff_forall_dual 𝔞 (T n)).mp (hT n) φ)
    exact hle hx

end GlobalTheory.CompanionTheory.Ar.Cmp
