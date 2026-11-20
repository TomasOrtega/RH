import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensVSecSt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop

noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct

/- English proof (translation)
Set `ι : (Fin a → K) →ₗ[K] (Fin M → K)` to `Fintype.linearCombination K Z`. Establish `hinj : Function.Injective ι`. Introduce `x y hxy`. Establish `h0 : ∑ i, (x - y) i • Z i = 0`. Use `congrArg (fun v => v) hxy` as an intermediate fact.

Simplify using `only [ι, Fintype.linearCombination_apply] at this`. Simplify using `only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, this, sub_self]`. Use function extensionality and compare the values at `i`. Conclude with `sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hZ _ h0 i)`. Take `⟨q, hq⟩` from `exists_isCompl (LinearMap.range ι)`.

Set `e` to `LinearEquiv.ofInjective ι hinj`. Set `p : (Fin M → K) →ₗ[K] (Fin a → K)` to `e.symm.toLinearMap ∘ₗ (LinearMap.range ι).projectionOnto q hq`. Establish `hp : ∀ x, p (ι x) = x`. Introduce `x`. Establish `e1 : ι x = ((e x : LinearMap.range ι) : Fin M → K)` using `rfl`.

Simplify using `only [p, LinearMap.comp_apply, LinearEquiv.coe_coe]`. Rewrite using `[e1, Submodule.projectionOnto_apply_left, LinearEquiv.symm_apply_apply]`. Use `⟨fun k i' => p (Pi.single k 1) i', fun i i' => ?_⟩` and prove the remaining obligations. Establish `hZi : Z i = ∑ k, Z i k • (Pi.single k (1 : K) : Fin M → K)`. Use function extensionality and compare the values at `j`.

Simplify using `[Finset.sum_apply, Pi.single_apply]`. Establish `hι : ι (Pi.single i 1) = Z i`. Simplify using `[ι, Fintype.linearCombination_apply_single]`. Establish `e1 : ∑ k, Z i k * p (Pi.single k 1) i' = p (Z i) i'` using `by conv_rhs => rw [hZi]`. Simplify using `only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`.

Rewrite using `[e1, ← hι, hp, Pi.single_apply]`. Distinguish the cases in `h : i = i'`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h, Ne.symm h]`.
-/
theorem exists_leftInv_of_linIndep {K : Type} [CommRing K] [IsSemisimpleRing K] {a M : ℕ}
    (Z : Fin a → Fin M → K) (hZ : LinearIndependent K Z) :
    ∃ q : Fin M → Fin a → K, ∀ i i', ∑ k, Z i k * q k i' = if i = i' then 1 else 0 := by
  classical
  let ι : (Fin a → K) →ₗ[K] (Fin M → K) := Fintype.linearCombination K Z
  have hinj : Function.Injective ι := by
    intro x y hxy
    have h0 : ∑ i, (x - y) i • Z i = 0 := by
      have := congrArg (fun v => v) hxy
      simp only [ι, Fintype.linearCombination_apply] at this
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, this, sub_self]
    funext i
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hZ _ h0 i)
  obtain ⟨q, hq⟩ := exists_isCompl (LinearMap.range ι)
  let e := LinearEquiv.ofInjective ι hinj
  let p : (Fin M → K) →ₗ[K] (Fin a → K) :=
    e.symm.toLinearMap ∘ₗ (LinearMap.range ι).projectionOnto q hq
  have hp : ∀ x, p (ι x) = x := by
    intro x
    have e1 : ι x = ((e x : LinearMap.range ι) : Fin M → K) := rfl
    simp only [p, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [e1, Submodule.projectionOnto_apply_left, LinearEquiv.symm_apply_apply]
  refine ⟨fun k i' => p (Pi.single k 1) i', fun i i' => ?_⟩
  have hZi : Z i = ∑ k, Z i k • (Pi.single k (1 : K) : Fin M → K) := by
    funext j; simp [Finset.sum_apply, Pi.single_apply]
  have hι : ι (Pi.single i 1) = Z i := by
    simp [ι, Fintype.linearCombination_apply_single]
  have e1 : ∑ k, Z i k * p (Pi.single k 1) i' = p (Z i) i' := by
    conv_rhs => rw [hZi]
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [e1, ← hι, hp, Pi.single_apply]
  by_cases h : i = i'
  · subst h; simp
  · simp [h, Ne.symm h]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ M J hJ hdet R _ _ hss a x hx`. Use `hss` as an intermediate fact. Set `s` to `sigR R σ`. Set `Z : Fin a → Fin M → R ⊗[F] E` to `fun i => Matrix.vecMul (fun l => s (x i l)) (JR (F := F) R J)`. Establish `hZh : ∀ i y, hR R σ J (x i) y = ∑ k, Z i k * y k`.

Introduce `i y`. Simplify using `only [hR, Formalism.UG.hform, Z, Matrix.vecMul, dotProduct, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Establish `hJu : IsUnit (JR (F` using `F) R J).det := by`. Establish `e` using `RingHom.map_det (inclR (F := F) (E := E) R) J`.

Rewrite `e` using `[RingHom.mapMatrix_apply]`. Use `show IsUnit (J.map (inclR R)).det`. Rewrite using `[← e]`. Conclude with `(isUnit_iff_ne_zero.2 hdet).map _`. Establish `hZ : LinearIndependent (R ⊗[F] E) Z`.

Use `Fintype.linearIndependent_iff.2 fun g hg i => ?_` and prove the remaining obligations. Set `v : Fin M → R ⊗[F] E` to `fun l => ∑ i, g i * s (x i l)`. Establish `hv0 : Matrix.vecMul v (JR (F` using `F) R J) = 0 := by`. Use function extensionality and compare the values at `j`. Use `congrFun hg j` as an intermediate fact.

Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Z, Matrix.vecMul, dotProduct, Finset.mul_sum, Pi.zero_apply] at this`. Simplify using `only [Matrix.vecMul, dotProduct, v, Finset.sum_mul, Pi.zero_apply]`. Rewrite using `[Finset.sum_comm]`. Rewrite using `[← this]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring`.

Establish `hv : v = 0`. Use `congrArg (fun u => Matrix.vecMul u (JR (F := F) R J)⁻¹) hv0` as an intermediate fact. Simplify using `only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hJu, Matrix.vecMul_one, Matrix.zero_vecMul] at this`. Conclude with `this`. Establish `hX0 : ∑ i, s (g i) • x i = 0`.

Use function extensionality and compare the values at `l`. Use `congrArg s (congrFun hv l)` as an intermediate fact. Simplify using `only [v, map_sum, map_mul, s, sigR_invol R σ hσ, Pi.zero_apply, map_zero] at this`. Simplify `this` using `[Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Use `Fintype.linearIndependent_iff.1 hx _ hX0 i` as an intermediate fact.

Establish `e2` using `congrArg s this`. Simplify using `only [s, sigR_invol R σ hσ, map_zero] at e2`. Conclude with `e2`. Take `⟨q, hq⟩` from `exists_leftInv_of_linIndep Z hZ`. Use `⟨q, fun S hS => ?_⟩` and prove the remaining obligations.

Establish `hh : algebraMap F (R ⊗[F] E) (1 / 2) + algebraMap F (R ⊗[F] E) (1 / 2) = 1`. Rewrite using `[← map_add, show (1 / 2 : F) + 1 / 2 = 1 by norm_num, map_one]`. Establish `hsh : sigR R σ (algebraMap F (R ⊗[F] E) (1 / 2)) = algebraMap F (R ⊗[F] E) (1 / 2)` using `(Algebra.TensorProduct.map (AlgHom.id F R) σ).commutes _`. Establish `h1 : ∀ i j, hR R σ J (x i) (fun k => ∑ i', (algebraMap F (R ⊗[F] E) (1 / 2) * S i' j) * q k i') = algebraMap F (R ⊗[F] E) (1 / 2) * S i j`. Introduce `i j`.

Rewrite using `[hZh]`. Simplify using `only [Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Establish `e3 : ∀ i', ∑ k, Z i k * (algebraMap F (R ⊗[F] E) (1 / 2) * S i' j * q k i') = algebraMap F (R ⊗[F] E) (1 / 2) * S i' j * (if i = i' then 1 else 0)` using `fun i' => by`. Rewrite using `[← hq i i', Finset.mul_sum]`.

Conclude with `Finset.sum_congr rfl fun k _ => by ring`. Simplify using `only [e3, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Establish `h2 : ∀ i j, hR R σ J (fun k => ∑ i', (algebraMap F (R ⊗[F] E) (1 / 2) * S i' i) * q k i') (x j) = algebraMap F (R ⊗[F] E) (1 / 2) * S i j`. Introduce `i j`. Rewrite using `[← hR_herm R σ hσ J hJ (x j), h1 j i, map_mul, hsh, hS i j]`.

Use function extensionality and compare the values at `i j`. Use `show hR R σ J (x i) (fun k => ∑ i', (algebraMap F (R ⊗[F] E) (1 / 2) * S i' j) * q k i') + hR R σ J (fun k => ∑ i', (algebraMap F (R ⊗[F] E) (1 / 2) * S i' i) * q k i') (x j) = S i j`. Rewrite using `[h1, h2, ← add_mul, hh, one_mul]`.
-/
theorem secGram_holds : SecGram := by
  intro F E _ _ _ _ _ σ hσ M J hJ hdet R _ _ hss a x hx
  have := hss
  let s := sigR R σ
  let Z : Fin a → Fin M → R ⊗[F] E := fun i => Matrix.vecMul (fun l => s (x i l)) (JR (F := F) R J)
  have hZh : ∀ i y, hR R σ J (x i) y = ∑ k, Z i k * y k := by
    intro i y
    simp only [hR, Formalism.UG.hform, Z, Matrix.vecMul, dotProduct, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hJu : IsUnit (JR (F := F) R J).det := by
    have e := RingHom.map_det (inclR (F := F) (E := E) R) J
    rw [RingHom.mapMatrix_apply] at e
    show IsUnit (J.map (inclR R)).det
    rw [← e]
    exact (isUnit_iff_ne_zero.2 hdet).map _
  have hZ : LinearIndependent (R ⊗[F] E) Z := by
    refine Fintype.linearIndependent_iff.2 fun g hg i => ?_
    let v : Fin M → R ⊗[F] E := fun l => ∑ i, g i * s (x i l)
    have hv0 : Matrix.vecMul v (JR (F := F) R J) = 0 := by
      funext j
      have := congrFun hg j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Z, Matrix.vecMul, dotProduct,
        Finset.mul_sum, Pi.zero_apply] at this
      simp only [Matrix.vecMul, dotProduct, v, Finset.sum_mul, Pi.zero_apply]
      rw [Finset.sum_comm]
      rw [← this]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
    have hv : v = 0 := by
      have := congrArg (fun u => Matrix.vecMul u (JR (F := F) R J)⁻¹) hv0
      simp only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hJu, Matrix.vecMul_one,
        Matrix.zero_vecMul] at this
      exact this
    have hX0 : ∑ i, s (g i) • x i = 0 := by
      funext l
      have := congrArg s (congrFun hv l)
      simp only [v, map_sum, map_mul, s, sigR_invol R σ hσ, Pi.zero_apply, map_zero] at this
      simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
    have := Fintype.linearIndependent_iff.1 hx _ hX0 i
    have e2 := congrArg s this
    simp only [s, sigR_invol R σ hσ, map_zero] at e2
    exact e2
  obtain ⟨q, hq⟩ := exists_leftInv_of_linIndep Z hZ
  refine ⟨q, fun S hS => ?_⟩
  have hh : algebraMap F (R ⊗[F] E) (1 / 2) + algebraMap F (R ⊗[F] E) (1 / 2) = 1 := by
    rw [← map_add, show (1 / 2 : F) + 1 / 2 = 1 by norm_num, map_one]
  have hsh : sigR R σ (algebraMap F (R ⊗[F] E) (1 / 2)) = algebraMap F (R ⊗[F] E) (1 / 2) :=
    (Algebra.TensorProduct.map (AlgHom.id F R) σ).commutes _
  have h1 : ∀ i j, hR R σ J (x i)
      (fun k => ∑ i', (algebraMap F (R ⊗[F] E) (1 / 2) * S i' j) * q k i') =
        algebraMap F (R ⊗[F] E) (1 / 2) * S i j := by
    intro i j
    rw [hZh]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    have e3 : ∀ i', ∑ k, Z i k * (algebraMap F (R ⊗[F] E) (1 / 2) * S i' j * q k i') =
        algebraMap F (R ⊗[F] E) (1 / 2) * S i' j * (if i = i' then 1 else 0) := fun i' => by
      rw [← hq i i', Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    simp only [e3, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have h2 : ∀ i j, hR R σ J
      (fun k => ∑ i', (algebraMap F (R ⊗[F] E) (1 / 2) * S i' i) * q k i') (x j) =
        algebraMap F (R ⊗[F] E) (1 / 2) * S i j := by
    intro i j
    rw [← hR_herm R σ hσ J hJ (x j), h1 j i, map_mul, hsh, hS i j]
  funext i j
  show hR R σ J (x i) (fun k => ∑ i', (algebraMap F (R ⊗[F] E) (1 / 2) * S i' j) * q k i') +
    hR R σ J (fun k => ∑ i', (algebraMap F (R ⊗[F] E) (1 / 2) * S i' i) * q k i') (x j) = S i j
  rw [h1, h2, ← add_mul, hh, one_mul]

end PI.VolStabS
