import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsGenericFormsKer
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

/- English proof (translation)
Introduce `F L _ _ _ ι _ e r hre u hu b c h j`. Use `set V : Submodule F (ι → F) := Submodule.span F (Set.range b) with hV`. Use `set B := Module.finBasis F V`. Use `set r' := Module.finrank F V`. Establish `hr' : r' ≤ e` using `(finrank_range_le_card b).trans (by simpa using hre)`.

Set `v : Fin r' → ι → F` to `fun l => (B l : ι → F)`. Establish `hbm : ∀ m, b m ∈ V` using `fun m => Submodule.subset_span ⟨m, rfl⟩`. Set `c' : Fin r' → L` to `fun l => ∑ m, c m * algebraMap F L (B.repr ⟨b m, hbm m⟩ l)`. Establish `hw : ∀ j, ∑ m, c m * algebraMap F L (b m j) = ∑ l, c' l * algebraMap F L (v l j)`. Introduce `j`.

Establish `hexp : ∀ m, b m j = ∑ l, B.repr ⟨b m, hbm m⟩ l * v l j`. Introduce `m`. Use `congrFun (congrArg Subtype.val (B.sum_repr ⟨b m, hbm m⟩)) j` as an intermediate fact. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this`. Conclude with `this.symm`.

Simplify using `only [hexp, map_sum, map_mul, Finset.mul_sum, c', Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => by ring` and prove the remaining obligations. Set `M : Matrix (Fin r') (Fin r') L` to `fun i l => ∑ j, u (Fin.castLE hr' i, j) * algebraMap F L (v l j)`. Establish `hMc : M.mulVec c' = 0`.

Use function extensionality and compare the values at `i`. Establish `hi` using `h (Fin.castLE hr' i)`. Simplify using `only [hw] at hi`. Simplify using `only [Matrix.mulVec, dotProduct, M, Pi.zero_apply, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm, ← hi]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun l _ => by ring`. Set `P : Matrix (Fin r') (Fin r') (MvPolynomial (Fin e × ι) F)` to `fun i l => ∑ j, X (Fin.castLE hr' i, j) * C (v l j)`. Establish `hPM : (aeval u : MvPolynomial (Fin e × ι) F →ₐ[F] L).toRingHom.mapMatrix P = M`.

Use extensionality with `i l`. Express the relevant statement in the definitionally equal form `aeval u (∑ j, X (Fin.castLE hr' i, j) * C (v l j)) = M i l`. Simplify using `only [map_sum, map_mul, aeval_X, aeval_C, M]`. Take `⟨g, hg⟩` from `LinearMap.exists_leftInverse_of_injective V.subtype V.ker_subtype`. Set `A₀ : Fin r' → ι → F` to `fun l j => B.repr (g (Pi.single j 1)) l`.

Establish `hA₀ : ∀ i l, ∑ j, A₀ i j * v l j = if i = l then 1 else 0`. Introduce `i l`. Establish `hvl : (∑ j, v l j • (Pi.single j (1 : F) : ι → F)) = V.subtype (B l)`. Use function extensionality and compare the values at `k`. Simplify using `[v, Finset.sum_apply, Pi.single_apply]`.

Use `congrArg (fun x => B.repr (g x) i) hvl` as an intermediate fact. Simplify using `only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul] at this`. Rewrite `this` using `[← LinearMap.comp_apply, hg, LinearMap.id_apply, Module.Basis.repr_self_apply]`. Establish `hil : (if i = l then (1 : F) else 0) = if l = i then 1 else 0`. Distinguish the cases in `hh : i = l`.

Simplify using `[hh]`. Simplify using `[hh, Ne.symm hh]`. Rewrite using `[hil, ← this]`. Simplify using `only [A₀]`. Conclude with `Finset.sum_congr rfl fun j _ => mul_comm _ _`.

Set `x : Fin e × ι → F` to `fun p => if hp : p.1.val < r' then A₀ ⟨p.1.val, hp⟩ p.2 else 0`. Establish `hPx : (eval x).mapMatrix P = 1`. Use extensionality with `i l`. Express the relevant statement in the definitionally equal form `eval x (∑ j, X (Fin.castLE hr' i, j) * C (v l j)) = (1 : Matrix (Fin r') (Fin r') F) i l`. Simplify using `only [map_sum, map_mul, eval_X, eval_C, Matrix.one_apply]`.

Rewrite using `[← hA₀]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `[x, Fin.castLE]`. Establish `hPdet : P.det ≠ 0`. Introduce `h0`.

Use `congrArg (eval x) h0` as an intermediate fact. Rewrite `this` using `[RingHom.map_det, hPx, Matrix.det_one, map_zero]`. Conclude with `one_ne_zero this`. Establish `hMdet : M.det ≠ 0`. Rewrite using `[← hPM, ← RingHom.map_det]`.

Establish `hinj : Function.Injective (aeval u : MvPolynomial (Fin e × ι) F →ₐ[F] L)` using `algebraicIndependent_iff_injective_aeval.1 hu`. Conclude with `(map_ne_zero_iff _ hinj).2 hPdet`. Establish `hc' : c' = 0` using `Matrix.eq_zero_of_mulVec_eq_zero hMdet hMc`. Rewrite using `[hw]`. Simplify using `[hc']`.
-/
theorem GenericFormsKer.proof : GenericFormsKer.Statement := by
  intro F L _ _ _ ι _ e r hre u hu b c h j
  classical

  set V : Submodule F (ι → F) := Submodule.span F (Set.range b) with hV
  set B := Module.finBasis F V
  set r' := Module.finrank F V
  have hr' : r' ≤ e := (finrank_range_le_card b).trans (by simpa using hre)
  let v : Fin r' → ι → F := fun l => (B l : ι → F)
  have hbm : ∀ m, b m ∈ V := fun m => Submodule.subset_span ⟨m, rfl⟩

  let c' : Fin r' → L := fun l => ∑ m, c m * algebraMap F L (B.repr ⟨b m, hbm m⟩ l)
  have hw : ∀ j, ∑ m, c m * algebraMap F L (b m j) = ∑ l, c' l * algebraMap F L (v l j) := by
    intro j
    have hexp : ∀ m, b m j = ∑ l, B.repr ⟨b m, hbm m⟩ l * v l j := by
      intro m
      have := congrFun (congrArg Subtype.val (B.sum_repr ⟨b m, hbm m⟩)) j
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul] at this
      exact this.symm
    simp only [hexp, map_sum, map_mul, Finset.mul_sum, c', Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => by ring

  let M : Matrix (Fin r') (Fin r') L :=
    fun i l => ∑ j, u (Fin.castLE hr' i, j) * algebraMap F L (v l j)
  have hMc : M.mulVec c' = 0 := by
    funext i
    have hi := h (Fin.castLE hr' i)
    simp only [hw] at hi
    simp only [Matrix.mulVec, dotProduct, M, Pi.zero_apply, Finset.sum_mul]
    rw [Finset.sum_comm, ← hi]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring

  let P : Matrix (Fin r') (Fin r') (MvPolynomial (Fin e × ι) F) :=
    fun i l => ∑ j, X (Fin.castLE hr' i, j) * C (v l j)
  have hPM : (aeval u : MvPolynomial (Fin e × ι) F →ₐ[F] L).toRingHom.mapMatrix P = M := by
    ext i l
    change aeval u (∑ j, X (Fin.castLE hr' i, j) * C (v l j)) = M i l
    simp only [map_sum, map_mul, aeval_X, aeval_C, M]

  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective V.subtype V.ker_subtype
  let A₀ : Fin r' → ι → F := fun l j => B.repr (g (Pi.single j 1)) l
  have hA₀ : ∀ i l, ∑ j, A₀ i j * v l j = if i = l then 1 else 0 := by
    intro i l
    have hvl : (∑ j, v l j • (Pi.single j (1 : F) : ι → F)) = V.subtype (B l) := by
      funext k
      simp [v, Finset.sum_apply, Pi.single_apply]
    have := congrArg (fun x => B.repr (g x) i) hvl
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul,
      Pi.smul_apply, smul_eq_mul] at this
    rw [← LinearMap.comp_apply, hg, LinearMap.id_apply, Module.Basis.repr_self_apply] at this
    have hil : (if i = l then (1 : F) else 0) = if l = i then 1 else 0 := by
      by_cases hh : i = l
      · simp [hh]
      · simp [hh, Ne.symm hh]
    rw [hil, ← this]
    simp only [A₀]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _

  let x : Fin e × ι → F := fun p => if hp : p.1.val < r' then A₀ ⟨p.1.val, hp⟩ p.2 else 0
  have hPx : (eval x).mapMatrix P = 1 := by
    ext i l
    change eval x (∑ j, X (Fin.castLE hr' i, j) * C (v l j)) = (1 : Matrix (Fin r') (Fin r') F) i l
    simp only [map_sum, map_mul, eval_X, eval_C, Matrix.one_apply]
    rw [← hA₀]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [x, Fin.castLE]
  have hPdet : P.det ≠ 0 := by
    intro h0
    have := congrArg (eval x) h0
    rw [RingHom.map_det, hPx, Matrix.det_one, map_zero] at this
    exact one_ne_zero this
  have hMdet : M.det ≠ 0 := by
    rw [← hPM, ← RingHom.map_det]
    have hinj : Function.Injective (aeval u : MvPolynomial (Fin e × ι) F →ₐ[F] L) :=
      algebraicIndependent_iff_injective_aeval.1 hu
    exact (map_ne_zero_iff _ hinj).2 hPdet
  have hc' : c' = 0 := Matrix.eq_zero_of_mulVec_eq_zero hMdet hMc
  rw [hw]
  simp [hc']

end

end GroundTheory.Heights₂.Heights.Vertical
