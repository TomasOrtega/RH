import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocOf

open NumberField

namespace GlobalTheory.SpanInfDenominators

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hy⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact Λ.zero_mem⟩`. Consider the case `add y z _ _ hy hz`. Take `⟨c, hc, hcy⟩` from `hy`.

Take `⟨c', hc', hcz⟩` from `hz`. Use `⟨c * c', mul_ne_zero hc hc', ?_⟩` and prove the remaining obligations. Establish `e1 : (c * c') • y = c' • (c • y)` using `by rw [mul_comm, mul_smul]`. Establish `e2 : (c * c') • z = c • (c' • z)` using `by rw [mul_smul]`. Rewrite using `[smul_add, e1, e2]`.

Conclude with `Λ.add_mem (Λ.smul_mem _ hcy) (Λ.smul_mem _ hcz)`. Consider the case `smul a y _ hy`. Take `⟨c, hc, hcy⟩` from `hy`. Take `⟨⟨n, d⟩, hnd⟩` from `IsLocalization.surj (nonZeroDivisors (𝓞 E)) a`. Establish `hd : (d : 𝓞 E) ≠ 0` using `nonZeroDivisors.ne_zero d.2`.

Use `⟨(d : 𝓞 E) * c, mul_ne_zero hd hc, ?_⟩` and prove the remaining obligations. Establish `key : ((d : 𝓞 E) * c) • (a • y) = n • (c • y)`. Rewrite using `[← algebraMap_smul E ((d : 𝓞 E) * c) (a • y), ← algebraMap_smul E n (c • y), ← algebraMap_smul E c y, smul_smul, smul_smul, map_mul]`. Use `congr 1`. Rewrite using `[← hnd]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key]`. Conclude with `Λ.smul_mem n hcy`.
-/
theorem exists_smul_mem {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module E V]
    [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] (Λ : Submodule (𝓞 E) V) (x : V)
    (hx : x ∈ Submodule.span E (Λ : Set V)) : ∃ c : 𝓞 E, c ≠ 0 ∧ c • x ∈ Λ := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hy⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact Λ.zero_mem⟩
  | add y z _ _ hy hz =>
    obtain ⟨c, hc, hcy⟩ := hy
    obtain ⟨c', hc', hcz⟩ := hz
    refine ⟨c * c', mul_ne_zero hc hc', ?_⟩
    have e1 : (c * c') • y = c' • (c • y) := by rw [mul_comm, mul_smul]
    have e2 : (c * c') • z = c • (c' • z) := by rw [mul_smul]
    rw [smul_add, e1, e2]
    exact Λ.add_mem (Λ.smul_mem _ hcy) (Λ.smul_mem _ hcz)
  | smul a y _ hy =>
    obtain ⟨c, hc, hcy⟩ := hy
    obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 E)) a
    have hd : (d : 𝓞 E) ≠ 0 := nonZeroDivisors.ne_zero d.2
    refine ⟨(d : 𝓞 E) * c, mul_ne_zero hd hc, ?_⟩
    have key : ((d : 𝓞 E) * c) • (a • y) = n • (c • y) := by
      rw [← algebraMap_smul E ((d : 𝓞 E) * c) (a • y), ← algebraMap_smul E n (c • y),
        ← algebraMap_smul E c y, smul_smul, smul_smul, map_mul]
      congr 1
      rw [← hnd]
      ring
    rw [key]
    exact Λ.smul_mem n hcy

/- English proof (translation)
Introduce `x hx`. Establish `hxs : x ∈ Submodule.span E (Λ : Set S.V)`. Rewrite using `[hΛ.span_eq_top]`. Discharge the goal by the elementary cases of `trivial`. Take `⟨c, hc, hcx⟩` from `exists_smul_mem Λ x hxs`.

Establish `hcU : c • x ∈ U`. Rewrite using `[← algebraMap_smul E c x]`. Conclude with `U.smul_mem _ hx`. Establish `hmem : c • x ∈ Λ ⊓ Formalism.MainNotions.S.Lat.toO S U` using `Submodule.mem_inf.2 ⟨hcx, hcU⟩`. Establish `hc' : algebraMap (𝓞 E) E c ≠ 0`.

Rewrite using `[ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 E) E)]` and apply the resulting hypothesis. Establish `hx' : x = (algebraMap (𝓞 E) E c)⁻¹ • (c • x)`. Rewrite using `[← algebraMap_smul E c x, smul_smul, inv_mul_cancel₀ hc', one_smul]`. Rewrite using `[hx']`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span hmem)`.
-/
theorem le_spanE_inf_toO {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E}
    (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.IsLattice E Λ) (U : Submodule E S.V) :
    U ≤ Formalism.MainNotions.S.Lat.spanE S (Λ ⊓ Formalism.MainNotions.S.Lat.toO S U) := by
  intro x hx
  have hxs : x ∈ Submodule.span E (Λ : Set S.V) := by
    rw [hΛ.span_eq_top]
    trivial
  obtain ⟨c, hc, hcx⟩ := exists_smul_mem Λ x hxs
  have hcU : c • x ∈ U := by
    rw [← algebraMap_smul E c x]
    exact U.smul_mem _ hx
  have hmem : c • x ∈ Λ ⊓ Formalism.MainNotions.S.Lat.toO S U := Submodule.mem_inf.2 ⟨hcx, hcU⟩
  have hc' : algebraMap (𝓞 E) E c ≠ 0 := by
    rwa [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 E) E)]
  have hx' : x = (algebraMap (𝓞 E) E c)⁻¹ • (c • x) := by
    rw [← algebraMap_smul E c x, smul_smul, inv_mul_cancel₀ hc', one_smul]
  rw [hx']
  exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

end GlobalTheory.SpanInfDenominators
