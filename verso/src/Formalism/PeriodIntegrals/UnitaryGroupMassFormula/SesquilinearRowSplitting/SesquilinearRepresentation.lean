import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.CoordStep

open NumberField Module

namespace PI.SRW

/- English proof (translation)
Introduce `E V _ _ _ _ _ _ _ _ h hnd Λ hΛ ℓ`. Establish `hsurj : Function.Surjective h`. Rewrite using `[← LinearMap.range_eq_top]`. Establish `hco : (LinearMap.range h).dualCoannihilator = ⊥`. Rewrite using `[eq_bot_iff]`.

Introduce `y hy`. Rewrite `hy` using `[Submodule.mem_dualCoannihilator]`. Rewrite using `[Submodule.mem_bot]`. Conclude with `hnd.2 y (fun x => hy (h x) ⟨x, rfl⟩)`. Rewrite using `[← Subspace.dualCoannihilator_dualAnnihilator_eq (W := LinearMap.range h), hco, Submodule.dualAnnihilator_bot]`.

Take `⟨s, hsΛ, hspan, hli⟩` from `exists_linearIndependent E (Λ : Set V)`. Establish `hs_top : Submodule.span E s = ⊤` using `hspan.trans hΛ.span_eq_top`. Set `b : Basis s E V` to `Basis.mk hli (le_of_eq (by rw [Subtype.range_coe, hs_top]))`. Set `φ : V →ₗ[E] E` to `b.constr E (fun i => ℓ ⟨i.1, hsΛ i.2⟩)`. Establish `hφb : ∀ v (hv : v ∈ s), φ v = ℓ ⟨v, hsΛ hv⟩`.

Introduce `v hv`. Establish `hb : b ⟨v, hv⟩ = v` using `Basis.mk_apply _ _ _`. Establish `e` using `b.constr_basis E (fun i : s => ℓ ⟨i.1, hsΛ i.2⟩) ⟨v, hv⟩`. Rewrite `e` using `[hb]`. Conclude with `e`.

Establish `hind : ∀ y ∈ Submodule.span (𝓞 E) (s : Set V), ∃ hy : y ∈ Λ, ℓ ⟨y, hy⟩ = φ y`. Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem v hv => exact ⟨hsΛ hv, (hφb v hv).symm⟩`. Consider the case `zero => exact ⟨zero_mem _, (map_zero ℓ).trans (map_zero φ).symm⟩`.

Consider the case `add u v _ _ hu hv`. Take `⟨hu', eu⟩` from `hu`. Take `⟨hv', ev⟩` from `hv`. Use `⟨add_mem hu' hv', ?_⟩` and prove the remaining obligations. Establish `e : (⟨u + v, add_mem hu' hv'⟩ : Λ) = ⟨u, hu'⟩ + ⟨v, hv'⟩` using `rfl`.

Rewrite using `[e, map_add, map_add, eu, ev]`. Consider the case `smul a u _ hu`. Take `⟨hu', eu⟩` from `hu`. Use `⟨Λ.smul_mem a hu', ?_⟩` and prove the remaining obligations. Establish `e : (⟨a • u, Λ.smul_mem a hu'⟩ : Λ) = a • ⟨u, hu'⟩` using `rfl`.

Rewrite using `[e, map_smul, eu, ← algebraMap_smul E a u, map_smul, Algebra.smul_def, smul_eq_mul]`. Establish `key : ∀ x : Λ, φ x = ℓ x`. Introduce `x`. Establish `hxE : (x : V) ∈ Submodule.span E s`. Rewrite using `[hs_top]`.

Conclude with `Submodule.mem_top`. Take `⟨y, hy, z, hxy⟩` from `(IsLocalization.mem_span_iff (nonZeroDivisors (𝓞 E))).mp hxE`. Establish `hzx : (z : 𝓞 E) • (x : V) = y`. Rewrite using `[hxy, ← algebraMap_smul E (z : 𝓞 E), smul_smul, IsLocalization.mk'_spec', map_one, one_smul]`. Take `⟨hyΛ, hℓφ⟩` from `hind y hy`.

Establish `h1 : ℓ ((z : 𝓞 E) • x) = algebraMap (𝓞 E) E z * ℓ x`. Rewrite using `[map_smul, Algebra.smul_def]`. Establish `h2 : φ ((z : 𝓞 E) • (x : V)) = algebraMap (𝓞 E) E z * φ x`. Rewrite using `[← algebraMap_smul E (z : 𝓞 E) (x : V), map_smul, smul_eq_mul]`. Establish `hzΛ : ((z : 𝓞 E) • x : Λ) = ⟨y, hyΛ⟩`.

Use `ext`. Conclude with `hzx`. Establish `hne : algebraMap (𝓞 E) E z ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors z.2`. Apply `mul_left_cancel₀ hne` to reduce the goal to its premises. Rewrite using `[← h1, ← h2, hzΛ, hzx, hℓφ]`.

Take `⟨w, hw⟩` from `hsurj φ`. Conclude with `⟨w, fun x => by rw [hw, key]⟩`.
-/
theorem sesquilinearRepresentation : RepStep := by
  intro E V _ _ _ _ _ _ _ _ h hnd Λ hΛ ℓ

  have hsurj : Function.Surjective h := by
    rw [← LinearMap.range_eq_top]
    have hco : (LinearMap.range h).dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      rw [Submodule.mem_dualCoannihilator] at hy
      rw [Submodule.mem_bot]
      exact hnd.2 y (fun x => hy (h x) ⟨x, rfl⟩)
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := LinearMap.range h), hco,
      Submodule.dualAnnihilator_bot]

  obtain ⟨s, hsΛ, hspan, hli⟩ := exists_linearIndependent E (Λ : Set V)
  have hs_top : Submodule.span E s = ⊤ := hspan.trans hΛ.span_eq_top
  let b : Basis s E V := Basis.mk hli (le_of_eq (by rw [Subtype.range_coe, hs_top]))
  let φ : V →ₗ[E] E := b.constr E (fun i => ℓ ⟨i.1, hsΛ i.2⟩)
  have hφb : ∀ v (hv : v ∈ s), φ v = ℓ ⟨v, hsΛ hv⟩ := by
    intro v hv
    have hb : b ⟨v, hv⟩ = v := Basis.mk_apply _ _ _
    have e := b.constr_basis E (fun i : s => ℓ ⟨i.1, hsΛ i.2⟩) ⟨v, hv⟩
    rw [hb] at e
    exact e

  have hind : ∀ y ∈ Submodule.span (𝓞 E) (s : Set V), ∃ hy : y ∈ Λ, ℓ ⟨y, hy⟩ = φ y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem v hv => exact ⟨hsΛ hv, (hφb v hv).symm⟩
    | zero => exact ⟨zero_mem _, (map_zero ℓ).trans (map_zero φ).symm⟩
    | add u v _ _ hu hv =>
      obtain ⟨hu', eu⟩ := hu
      obtain ⟨hv', ev⟩ := hv
      refine ⟨add_mem hu' hv', ?_⟩
      have e : (⟨u + v, add_mem hu' hv'⟩ : Λ) = ⟨u, hu'⟩ + ⟨v, hv'⟩ := rfl
      rw [e, map_add, map_add, eu, ev]
    | smul a u _ hu =>
      obtain ⟨hu', eu⟩ := hu
      refine ⟨Λ.smul_mem a hu', ?_⟩
      have e : (⟨a • u, Λ.smul_mem a hu'⟩ : Λ) = a • ⟨u, hu'⟩ := rfl
      rw [e, map_smul, eu, ← algebraMap_smul E a u, map_smul, Algebra.smul_def, smul_eq_mul]

  have key : ∀ x : Λ, φ x = ℓ x := by
    intro x
    have hxE : (x : V) ∈ Submodule.span E s := by
      rw [hs_top]
      exact Submodule.mem_top
    obtain ⟨y, hy, z, hxy⟩ := (IsLocalization.mem_span_iff (nonZeroDivisors (𝓞 E))).mp hxE
    have hzx : (z : 𝓞 E) • (x : V) = y := by
      rw [hxy, ← algebraMap_smul E (z : 𝓞 E), smul_smul, IsLocalization.mk'_spec', map_one,
        one_smul]
    obtain ⟨hyΛ, hℓφ⟩ := hind y hy
    have h1 : ℓ ((z : 𝓞 E) • x) = algebraMap (𝓞 E) E z * ℓ x := by
      rw [map_smul, Algebra.smul_def]
    have h2 : φ ((z : 𝓞 E) • (x : V)) = algebraMap (𝓞 E) E z * φ x := by
      rw [← algebraMap_smul E (z : 𝓞 E) (x : V), map_smul, smul_eq_mul]
    have hzΛ : ((z : 𝓞 E) • x : Λ) = ⟨y, hyΛ⟩ := by
      ext
      exact hzx
    have hne : algebraMap (𝓞 E) E z ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors z.2
    apply mul_left_cancel₀ hne
    rw [← h1, ← h2, hzΛ, hzx, hℓφ]
  obtain ⟨w, hw⟩ := hsurj φ
  exact ⟨w, fun x => by rw [hw, key]⟩

end PI.SRW
