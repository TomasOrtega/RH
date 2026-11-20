import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.OrdBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.EigSum
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.EigUnitInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.EigNilInt

open UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite TensorProduct

/- English proof (translation)
Establish `hm : ∀ x ∈ LinearMap.range e, U x ∈ LinearMap.range e` using `fun x hx => h.bij.mapsTo hx`. Establish `hb : Function.Bijective (U.restrict hm)`. Prove the components needed by the constructor for the conclusion. Introduce `x y hxy`. Conclude with `Subtype.ext (h.bij.injOn x.2 y.2 (congrArg Subtype.val hxy))`.

Introduce `y`. Take `⟨x, hx, hxy⟩` from `h.bij.surjOn y.2`. Conclude with `⟨⟨x, hx⟩, Subtype.ext hxy⟩`. Set `E` to `LinearEquiv.ofBijective _ hb`. Set `V : Module.End R M` to `(LinearMap.range e).subtype ∘ₗ E.symm.toLinearMap ∘ₗ e.rangeRestrict`.

Establish `hc : ∀ x, U (e x) = e (U x)` using `fun x => LinearMap.congr_fun h.comm.eq x`. Establish `hV : ∀ z, e z = z → V (U z) = z`. Introduce `z hz`. Establish `: e.rangeRestrict (U z) = E ⟨z, z, hz⟩` using `Subtype.ext (by show e (U z) = U z`. Rewrite using `[← hc, hz])`.

Simplify using `only [V, LinearMap.comp_apply, this]`. Simplify using the standard rewrite rules. Use `⟨V, LinearMap.ext fun x => ?_⟩` and prove the remaining obligations. Conclude with `hV (e x) (LinearMap.congr_fun h.idem.eq x)`.
-/
private theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigOrdInt_inv
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] {I : Ideal R}
    {U e : Module.End R M} (h : IsOrdProj I U e) : ∃ V : Module.End R M, V * U * e = e := by
  have hm : ∀ x ∈ LinearMap.range e, U x ∈ LinearMap.range e := fun x hx => h.bij.mapsTo hx
  have hb : Function.Bijective (U.restrict hm) := by
    constructor
    · intro x y hxy
      exact Subtype.ext (h.bij.injOn x.2 y.2 (congrArg Subtype.val hxy))
    · intro y
      obtain ⟨x, hx, hxy⟩ := h.bij.surjOn y.2
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  let E := LinearEquiv.ofBijective _ hb
  let V : Module.End R M := (LinearMap.range e).subtype ∘ₗ E.symm.toLinearMap ∘ₗ e.rangeRestrict
  have hc : ∀ x, U (e x) = e (U x) := fun x => LinearMap.congr_fun h.comm.eq x
  have hV : ∀ z, e z = z → V (U z) = z := by
    intro z hz
    have : e.rangeRestrict (U z) = E ⟨z, z, hz⟩ := Subtype.ext (by
      show e (U z) = U z
      rw [← hc, hz])
    simp only [V, LinearMap.comp_apply, this]
    simp
  refine ⟨V, LinearMap.ext fun x => ?_⟩
  exact hV (e x) (LinearMap.congr_fun h.idem.eq x)

/- English proof (translation)
Introduce `O K _ _ _ _ _ M _ _ _ U e h`. Use `UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigSum (U.baseChange K) (e.baseChange K) _ ?_ ?_ ?_ ?_` and prove the remaining obligations. Use `show _ * _ = _`. Rewrite using `[← LinearMap.baseChange_mul, h.idem.eq]`. Use `show _ * _ = _ * _`.

Rewrite using `[← LinearMap.baseChange_mul, ← LinearMap.baseChange_mul, h.comm.eq]`. Introduce `μ y hy he hU`. Take `⟨V, hV⟩` from `UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigOrdInt_inv h`. Conclude with `UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigUnitInt U V e hV μ y hy he hU`. Introduce and unpack `μ y hy he hU ⟨h0, -, hi⟩`.

Take `⟨n, hn⟩` from `h.nil 1`. Establish `hp : ∀ k : ℕ, (U ^ k).baseChange K y = μ ^ k • y`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => rw [pow_zero, pow_zero, LinearMap.baseChange_one, one_smul, Module.End.one_apply]`.

Consider the case `succ k ih`. Rewrite using `[pow_succ, LinearMap.baseChange_mul, Module.End.mul_apply, hU, map_smul, ih, smul_smul, pow_succ']`. Use `UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigNilInt (U ^ n * (1 - e)) ?_ (μ ^ n) y hy ?_ (pow_ne_zero n h0) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, rfl⟩`. Use `hn x` as an intermediate fact.

Rewrite `this` using `[pow_one]`. Conclude with `this`. Rewrite using `[LinearMap.baseChange_mul, Module.End.mul_apply, LinearMap.baseChange_sub, LinearMap.baseChange_one, LinearMap.sub_apply, he, sub_zero, Module.End.one_apply, hp]`. Rewrite using `[← inv_pow]`. Conclude with `hi.pow n`.
-/
theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigOrdInt :
    ∀ {O K : Type*} [CommRing O] [Field K] [Algebra O K] [IsLocalRing O] [IsAlgClosed K] {M : Type*} [AddCommGroup M] [Module O M] [Module.Finite O M] {U e : Module.End O M}, IsOrdProj (IsLocalRing.maximalIdeal O) U e → LinearMap.range (e.baseChange K) = ⨆ μ ∈ {μ : K | μ ≠ 0 ∧ IsIntegral O μ ∧ IsIntegral O μ⁻¹}, Module.End.maxGenEigenspace (U.baseChange K) μ := by
  intro O K _ _ _ _ _ M _ _ _ U e h
  refine UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigSum (U.baseChange K) (e.baseChange K) _ ?_ ?_ ?_ ?_
  · show _ * _ = _
    rw [← LinearMap.baseChange_mul, h.idem.eq]
  · show _ * _ = _ * _
    rw [← LinearMap.baseChange_mul, ← LinearMap.baseChange_mul, h.comm.eq]
  · intro μ y hy he hU
    obtain ⟨V, hV⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigOrdInt_inv h
    exact UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigUnitInt U V e hV μ y hy he hU
  · rintro μ y hy he hU ⟨h0, -, hi⟩
    obtain ⟨n, hn⟩ := h.nil 1
    have hp : ∀ k : ℕ, (U ^ k).baseChange K y = μ ^ k • y := by
      intro k
      induction k with
      | zero => rw [pow_zero, pow_zero, LinearMap.baseChange_one, one_smul, Module.End.one_apply]
      | succ k ih =>
        rw [pow_succ, LinearMap.baseChange_mul, Module.End.mul_apply, hU, map_smul, ih, smul_smul,
          pow_succ']
    refine UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigNilInt (U ^ n * (1 - e)) ?_ (μ ^ n) y hy ?_ (pow_ne_zero n h0) ?_
    · rintro _ ⟨x, rfl⟩
      have := hn x
      rw [pow_one] at this
      exact this
    · rw [LinearMap.baseChange_mul, Module.End.mul_apply, LinearMap.baseChange_sub,
        LinearMap.baseChange_one, LinearMap.sub_apply, he, sub_zero, Module.End.one_apply, hp]
    · rw [← inv_pow]
      exact hi.pow n
