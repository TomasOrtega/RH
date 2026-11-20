import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensInfCo

noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW Topology
open scoped TensorProduct
open PI.AdicCompletionValuation

def SemisimpleTens : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → IsSemisimpleRing (Ainf F ⊗[F] E)

/- English proof (translation)
Set `ι : (Fin a → K) →ₗ[K] (Fin M → K)` to `Fintype.linearCombination K Z`. Establish `hinj : Function.Injective ι`. Introduce `x y hxy`. Establish `h0 : ∑ i, (x - y) i • Z i = 0`. Use `congrArg (fun v => v) hxy` as an intermediate fact.

Simplify using `only [ι, Fintype.linearCombination_apply] at this`. Simplify using `only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, this, sub_self]`. Use function extensionality and compare the values at `i`. Conclude with `sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hZ _ h0 i)`. Take `⟨q, hq⟩` from `exists_isCompl (LinearMap.range ι)`.

Set `e` to `LinearEquiv.ofInjective ι hinj`. Set `p : (Fin M → K) →ₗ[K] (Fin a → K)` to `e.symm.toLinearMap ∘ₗ (LinearMap.range ι).projectionOnto q hq`. Establish `hp : ∀ x, p (ι x) = x`. Introduce `x`. Establish `e1 : ι x = ((e x : LinearMap.range ι) : Fin M → K)` using `rfl`.

Simplify using `only [p, LinearMap.comp_apply, LinearEquiv.coe_coe]`. Rewrite using `[e1, Submodule.projectionOnto_apply_left, LinearEquiv.symm_apply_apply]`. Use `⟨fun k => ∑ i', c i' * p (Pi.single k 1) i', fun i => ?_⟩` and prove the remaining obligations. Establish `hZi : Z i = ∑ k, Z i k • (Pi.single k (1 : K) : Fin M → K)`. Use function extensionality and compare the values at `j`.

Simplify using `[Finset.sum_apply, Pi.single_apply]`. Establish `hι : ι (Pi.single i 1) = Z i`. Simplify using `[ι, Fintype.linearCombination_apply_single]`. Establish `e1 : ∑ k, Z i k * ∑ i', c i' * p (Pi.single k 1) i' = ∑ i', c i' * (p (Z i)) i'` using `by conv_rhs => rw [hZi]`. Simplify using `only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`.

Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i' _ => by ring`. Rewrite using `[e1, ← hι, hp]`. Simplify using `[Pi.single_apply]`.
-/
theorem exists_dual_of_linIndep {K : Type} [CommRing K] [IsSemisimpleRing K] {a M : ℕ}
    (Z : Fin a → Fin M → K) (hZ : LinearIndependent K Z) (c : Fin a → K) :
    ∃ w : Fin M → K, ∀ i, ∑ k, Z i k * w k = c i := by
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
  refine ⟨fun k => ∑ i', c i' * p (Pi.single k 1) i', fun i => ?_⟩
  have hZi : Z i = ∑ k, Z i k • (Pi.single k (1 : K) : Fin M → K) := by
    funext j; simp [Finset.sum_apply, Pi.single_apply]
  have hι : ι (Pi.single i 1) = Z i := by
    simp [ι, Fintype.linearCombination_apply_single]
  have e1 : ∑ k, Z i k * ∑ i', c i' * p (Pi.single k 1) i' =
      ∑ i', c i' * (p (Z i)) i' := by
    conv_rhs => rw [hZi]
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i' _ => by ring
  rw [e1, ← hι, hp]
  simp [Pi.single_apply]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM M J hJ ha hc a hA1 hA2 X0 hT0 hdet X hX S`. Use `h F E σ hCM` as an intermediate fact. Establish `hσ : ∀ x, σ (σ x) = x` using `sigma_invol σ hCM.2.2.2`. Set `s` to `sigR (Ainf F) σ`. Set `Z : Fin a → Fin M → Ainf F ⊗[F] E` to `fun i => Matrix.vecMul (fun l => s (X i l)) (JR (F := F) (Ainf F) J)`.

Establish `hZh : ∀ i y, hR (Ainf F) σ J (X i) y = ∑ k, Z i k * y k`. Introduce `i y`. Simplify using `only [hR, Formalism.UG.hform, Z, Matrix.vecMul, dotProduct, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Establish `hJu : IsUnit (JR (F` using `F) (Ainf F) J).det := by`.

Establish `e` using `RingHom.map_det (inclR (F := F) (E := E) (Ainf F)) J`. Rewrite `e` using `[RingHom.mapMatrix_apply]`. Use `show IsUnit (J.map (inclR (Ainf F))).det`. Rewrite using `[← e]`. Conclude with `(isUnit_iff_ne_zero.2 hJ.2).map _`.

Establish `hZ : LinearIndependent (Ainf F ⊗[F] E) Z`. Use `Fintype.linearIndependent_iff.2 fun g hg i => ?_` and prove the remaining obligations. Set `v : Fin M → Ainf F ⊗[F] E` to `fun l => ∑ i, g i * s (X i l)`. Establish `hv0 : Matrix.vecMul v (JR (F` using `F) (Ainf F) J) = 0 := by`. Use function extensionality and compare the values at `j`.

Use `congrFun hg j` as an intermediate fact. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Z, Matrix.vecMul, dotProduct, Finset.mul_sum, Pi.zero_apply] at this`. Simplify using `only [Matrix.vecMul, dotProduct, v, Finset.sum_mul, Pi.zero_apply]`. Rewrite using `[Finset.sum_comm]`. Rewrite using `[← this]`.

Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring`. Establish `hv : v = 0`. Use `congrArg (fun u => Matrix.vecMul u (JR (F := F) (Ainf F) J)⁻¹) hv0` as an intermediate fact. Simplify using `only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hJu, Matrix.vecMul_one, Matrix.zero_vecMul] at this`. Conclude with `this`.

Establish `hX0 : ∑ i, s (g i) • X i = 0`. Use function extensionality and compare the values at `l`. Use `congrArg s (congrFun hv l)` as an intermediate fact. Simplify using `only [v, map_sum, map_mul, s, sigR_invol (Ainf F) σ hσ, Pi.zero_apply, map_zero] at this`. Simplify `this` using `[Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`.

Use `Fintype.linearIndependent_iff.1 hX _ hX0 i` as an intermediate fact. Establish `e2` using `congrArg s this`. Simplify using `only [s, sigR_invol (Ainf F) σ hσ, map_zero] at e2`. Conclude with `e2`. Set `half : Ainf F ⊗[F] E` to `algebraMap F (Ainf F ⊗[F] E) (1/2)`.

Establish `hh : half + half = 1`. Simplify using `only [half, ← map_add]`. Evaluate the numerical expressions. Apply the tactic sequence `first | rfl | exact Algebra.TensorProduct.one_def.symm`. Establish `hsh : s half = half` using `(Algebra.TensorProduct.map (AlgHom.id F (Ainf F)) σ).commutes _`.

Establish `hw : ∀ j, ∃ w : Fin M → Ainf F ⊗[F] E, ∀ i, ∑ k, Z i k * w k = half * (S : Matrix (Fin a) (Fin a) (Ainf F ⊗[F] E)) i j` using `fun j => exists_dual_of_linIndep Z hZ _`. Use `choose Y hY using hw`. Use `⟨Y, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i j`. Establish `h1 : hR (Ainf F) σ J (X i) (Y j) = half * (S : Matrix _ _ _) i j` using `by rw [hZh]; exact hY j i`.

Establish `h2 : hR (Ainf F) σ J (Y i) (X j) = half * (S : Matrix _ _ _) i j`. Rewrite using `[← hR_herm (Ainf F) σ hσ J hJ.1 (X j) (Y i), hZh, hY i j]`. Simplify using `only [map_mul]`. Rewrite using `[show sigR (Ainf F) σ half = half from hsh, S.2 i j]`. Use `show hR (Ainf F) σ J (X i) (Y j) + hR (Ainf F) σ J (Y i) (X j) = _`.

Rewrite using `[h1, h2, ← add_mul, hh, one_mul]`.
-/
theorem freeSurj_of (h : SemisimpleTens) : FreeSurj := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a hA1 hA2 X0 hT0 hdet X hX S
  have := h F E σ hCM
  have hσ : ∀ x, σ (σ x) = x := sigma_invol σ hCM.2.2.2
  let s := sigR (Ainf F) σ
  let Z : Fin a → Fin M → Ainf F ⊗[F] E := fun i => Matrix.vecMul (fun l => s (X i l)) (JR (F := F) (Ainf F) J)
  have hZh : ∀ i y, hR (Ainf F) σ J (X i) y = ∑ k, Z i k * y k := by
    intro i y
    simp only [hR, Formalism.UG.hform, Z, Matrix.vecMul, dotProduct, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hJu : IsUnit (JR (F := F) (Ainf F) J).det := by
    have e := RingHom.map_det (inclR (F := F) (E := E) (Ainf F)) J
    rw [RingHom.mapMatrix_apply] at e
    show IsUnit (J.map (inclR (Ainf F))).det
    rw [← e]
    exact (isUnit_iff_ne_zero.2 hJ.2).map _
  have hZ : LinearIndependent (Ainf F ⊗[F] E) Z := by
    refine Fintype.linearIndependent_iff.2 fun g hg i => ?_
    let v : Fin M → Ainf F ⊗[F] E := fun l => ∑ i, g i * s (X i l)
    have hv0 : Matrix.vecMul v (JR (F := F) (Ainf F) J) = 0 := by
      funext j
      have := congrFun hg j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Z, Matrix.vecMul, dotProduct,
        Finset.mul_sum, Pi.zero_apply] at this
      simp only [Matrix.vecMul, dotProduct, v, Finset.sum_mul, Pi.zero_apply]
      rw [Finset.sum_comm]
      rw [← this]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
    have hv : v = 0 := by
      have := congrArg (fun u => Matrix.vecMul u (JR (F := F) (Ainf F) J)⁻¹) hv0
      simp only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hJu, Matrix.vecMul_one,
        Matrix.zero_vecMul] at this
      exact this
    have hX0 : ∑ i, s (g i) • X i = 0 := by
      funext l
      have := congrArg s (congrFun hv l)
      simp only [v, map_sum, map_mul, s, sigR_invol (Ainf F) σ hσ, Pi.zero_apply, map_zero] at this
      simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
    have := Fintype.linearIndependent_iff.1 hX _ hX0 i
    have e2 := congrArg s this
    simp only [s, sigR_invol (Ainf F) σ hσ, map_zero] at e2
    exact e2
  let half : Ainf F ⊗[F] E := algebraMap F (Ainf F ⊗[F] E) (1/2)
  have hh : half + half = 1 := by
    simp only [half, ← map_add]; norm_num
    first | rfl | exact Algebra.TensorProduct.one_def.symm
  have hsh : s half = half := (Algebra.TensorProduct.map (AlgHom.id F (Ainf F)) σ).commutes _
  have hw : ∀ j, ∃ w : Fin M → Ainf F ⊗[F] E, ∀ i, ∑ k, Z i k * w k =
      half * (S : Matrix (Fin a) (Fin a) (Ainf F ⊗[F] E)) i j :=
    fun j => exists_dual_of_linIndep Z hZ _
  choose Y hY using hw
  refine ⟨Y, ?_⟩
  funext i j
  have h1 : hR (Ainf F) σ J (X i) (Y j) = half * (S : Matrix _ _ _) i j := by rw [hZh]; exact hY j i
  have h2 : hR (Ainf F) σ J (Y i) (X j) = half * (S : Matrix _ _ _) i j := by
    rw [← hR_herm (Ainf F) σ hσ J hJ.1 (X j) (Y i), hZh, hY i j]
    simp only [map_mul]
    rw [show sigR (Ainf F) σ half = half from hsh, S.2 i j]
  show hR (Ainf F) σ J (X i) (Y j) + hR (Ainf F) σ J (Y i) (X j) = _
  rw [h1, h2, ← add_mul, hh, one_mul]

/- English proof (translation)
The claim follows from `densInf_of_tens h2 (freeSurj_of h3)`.
-/
theorem densInf_of_ss (h2 : TensR) (h3 : SemisimpleTens) : DensInf :=
  densInf_of_tens h2 (freeSurj_of h3)

end PI.VolStabS
