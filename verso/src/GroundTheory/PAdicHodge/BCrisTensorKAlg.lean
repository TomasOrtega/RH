import Mathlib
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Polynomial TensorProduct

section Lifts

variable {R E : Type*} [Field R] [Field E]

/- English proof (translation)
Establish `hPm0 : P.map i ≠ 0` using `Polynomial.map_ne_zero hP0`. Establish `hQs : Q.Splits` using `(hP.map i).of_dvd hPm0 hdvd`. Use `hQs.mem_lift_of_roots_mem_range hQ i fun a ha => ?_` and prove the remaining obligations. Establish `ha' : a ∈ (P.map i).roots` using `Multiset.mem_of_le (roots.le_of_dvd hPm0 hdvd) ha`. Conclude with `hP.mem_range_of_isRoot hP0 (isRoot_of_mem_roots ha')`.
-/
theorem mem_lifts_of_dvd_map_of_splits (i : R →+* E) {P : R[X]} (hP : P.Splits) (hP0 : P ≠ 0)
    {Q : E[X]} (hQ : Q.Monic) (hdvd : Q ∣ P.map i) : Q ∈ lifts i := by
  have hPm0 : P.map i ≠ 0 := Polynomial.map_ne_zero hP0
  have hQs : Q.Splits := (hP.map i).of_dvd hPm0 hdvd
  refine hQs.mem_lift_of_roots_mem_range hQ i fun a ha => ?_
  have ha' : a ∈ (P.map i).roots := Multiset.mem_of_le (roots.le_of_dvd hPm0 hdvd) ha
  exact hP.mem_range_of_isRoot hP0 (isRoot_of_mem_roots ha')

end Lifts

section Disjoint

variable {K₀ C E : Type*} [Field K₀] [Field C] [Field E] [Algebra K₀ C] [Algebra K₀ E]
  (j : C →ₐ[K₀] E) (F : IntermediateField K₀ E) (M N : IntermediateField K₀ C)
  (L : Type*) [Field L] [Algebra K₀ L] [Algebra L C] [IsScalarTower K₀ L C]

/- English proof (translation)
Use `set α : C := algebraMap L C pb.gen with hα`. Use `set x : E := j α with hx`. Use `set n := pb.dim`. Use `set P := minpoly K₀ pb.gen`. Set `f : L →ₐ[K₀] E` to `j.comp (IsScalarTower.toAlgHom K₀ L C)`.

Establish `hfx : f pb.gen = x` using `rfl`. Establish `hxint : IsIntegral F x`. Establish `h1 : IsIntegral K₀ x` using `hfx ▸ (pb.isIntegral_gen).map f`. Conclude with `h1.tower_top`. Use `set m := minpoly F x`.

Establish `hm0 : m ≠ 0` using `minpoly.ne_zero hxint`. Establish `hP0 : P ≠ 0` using `minpoly.ne_zero pb.isIntegral_gen`. Establish `hPx : aeval x P = 0`. Rewrite using `[← hfx, Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]`. Establish `hdvdF : m ∣ P.map (algebraMap K₀ F)` using `minpoly.dvd F x (by rw [Polynomial.aeval_map_algebraMap]; exact hPx)`.

Set `i : N →+* E` to `j.toRingHom.comp (algebraMap N C)`. Establish `hi : i.comp (algebraMap K₀ N) = algebraMap K₀ E`. Use extensionality with `a`. Simplify using `only [i, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]`. Rewrite using `[← IsScalarTower.algebraMap_apply, AlgHom.commutes]`.

Establish `hFE : (algebraMap F E).comp (algebraMap K₀ F) = algebraMap K₀ E` using `(IsScalarTower.algebraMap_eq K₀ F E).symm`. Establish `hdvdE : m.map (algebraMap F E) ∣ (P.map (algebraMap K₀ N)).map i`. Rewrite using `[Polynomial.map_map, hi, ← hFE, ← Polynomial.map_map]`. Conclude with `Polynomial.map_dvd _ hdvdF`. Establish `hlift` using `mem_lifts_of_dvd_map_of_splits i hN (Polynomial.map_ne_zero hP0) ((minpoly.monic hxint).map _) hdvdE`.

Take `⟨D, hD⟩` from `(Polynomial.mem_lifts _).1 hlift`. Establish `hiinj : Function.Injective i` using `i.injective`. Establish `hDdeg : D.natDegree = m.natDegree`. Rewrite using `[← natDegree_map_eq_of_injective hiinj, hD, natDegree_map_eq_of_injective (algebraMap F E).injective]`. Establish `hcoeff : ∀ k, ((D.coeff k : N) : C) ∈ M ⊓ N`.

Introduce `k`. Use `⟨hM _ ?_, (D.coeff k).2⟩` and prove the remaining obligations. Establish `e : j ((D.coeff k : N) : C) = (D.map i).coeff k`. Rewrite using `[coeff_map]`. Both sides reduce to the same expression.

Rewrite using `[e, hD, coeff_map]`. Conclude with `(m.coeff k).2`. Establish `hDα : (D.map (algebraMap N C)).eval α = 0`. Establish `h0 : j.toRingHom ((D.map (algebraMap N C)).eval α) = 0`. Rewrite using `[Polynomial.eval_map, Polynomial.hom_eval₂]`.

Express the relevant statement in the definitionally equal form `D.eval₂ i x = 0`. Rewrite using `[← Polynomial.eval_map, hD, Polynomial.eval_map, ← Polynomial.aeval_def, minpoly.aeval]`. Conclude with `(map_eq_zero_iff _ j.toRingHom.injective).1 h0`. Assume the negation of the conclusion as `hlt`. Rewrite `hlt` using `[not_le]`.

Establish `hDlt : (D.map (algebraMap N C)).natDegree < n`. Rewrite using `[natDegree_map_eq_of_injective (algebraMap N C).injective, hDdeg]`. Conclude with `hlt`. Establish `hsum` using `hDα`. Rewrite `hsum` using `[Polynomial.eval_eq_sum_range' hDlt, ← Fin.sum_univ_eq_sum_range (fun k => (D.map (algebraMap N C)).coeff k * α ^ k) n]`.

Establish `li` using `hdisj.linearIndependent_right' pb.basis.linearIndependent`. Establish `hzero` using `Fintype.linearIndependent_iff.1 li (fun k => ⟨((D.coeff k : N) : C), hcoeff k⟩) (by`. Rewrite using `[← hsum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Function.comp_apply, PowerBasis.coe_basis, map_pow, Algebra.smul_def, coeff_map]`.

Use the proof step `rfl)`. Establish `hD0 : D = 0`. Use `Polynomial.ext fun k => ?_` and prove the remaining obligations. Rewrite using `[Polynomial.coeff_zero]`. Distinguish the cases in `hk : k < n`.

Establish `h1` using `congrArg Subtype.val (hzero ⟨k, hk⟩)`. Simplify using `using h1`. Conclude with `coeff_eq_zero_of_natDegree_lt (p := D) (n := k) (by rw [hDdeg]; omega)`. Apply `hm0` to reduce the goal to its premises. Establish `h2` using `hD`.

Rewrite `h2` using `[hD0, Polynomial.map_zero]`. Conclude with `(Polynomial.map_eq_zero_iff (algebraMap F E).injective).1 h2.symm`.
-/
theorem le_natDegree_minpoly_of_linearDisjoint (pb : PowerBasis K₀ L)
    (hM : ∀ y : C, j y ∈ F → y ∈ M)
    (hN : ((minpoly K₀ pb.gen).map (algebraMap K₀ N)).Splits)
    (hdisj : (M ⊓ N).LinearDisjoint L) :
    pb.dim ≤ (minpoly F (j (algebraMap L C pb.gen))).natDegree := by
  set α : C := algebraMap L C pb.gen with hα
  set x : E := j α with hx
  set n := pb.dim
  set P := minpoly K₀ pb.gen
  let f : L →ₐ[K₀] E := j.comp (IsScalarTower.toAlgHom K₀ L C)
  have hfx : f pb.gen = x := rfl
  have hxint : IsIntegral F x := by
    have h1 : IsIntegral K₀ x := hfx ▸ (pb.isIntegral_gen).map f
    exact h1.tower_top
  set m := minpoly F x
  have hm0 : m ≠ 0 := minpoly.ne_zero hxint
  have hP0 : P ≠ 0 := minpoly.ne_zero pb.isIntegral_gen

  have hPx : aeval x P = 0 := by
    rw [← hfx, Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  have hdvdF : m ∣ P.map (algebraMap K₀ F) :=
    minpoly.dvd F x (by rw [Polynomial.aeval_map_algebraMap]; exact hPx)
  let i : N →+* E := j.toRingHom.comp (algebraMap N C)
  have hi : i.comp (algebraMap K₀ N) = algebraMap K₀ E := by
    ext a
    simp only [i, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [← IsScalarTower.algebraMap_apply, AlgHom.commutes]
  have hFE : (algebraMap F E).comp (algebraMap K₀ F) = algebraMap K₀ E :=
    (IsScalarTower.algebraMap_eq K₀ F E).symm
  have hdvdE : m.map (algebraMap F E) ∣ (P.map (algebraMap K₀ N)).map i := by
    rw [Polynomial.map_map, hi, ← hFE, ← Polynomial.map_map]
    exact Polynomial.map_dvd _ hdvdF
  have hlift := mem_lifts_of_dvd_map_of_splits i hN (Polynomial.map_ne_zero hP0)
    ((minpoly.monic hxint).map _) hdvdE
  obtain ⟨D, hD⟩ := (Polynomial.mem_lifts _).1 hlift
  have hiinj : Function.Injective i := i.injective
  have hDdeg : D.natDegree = m.natDegree := by
    rw [← natDegree_map_eq_of_injective hiinj, hD,
      natDegree_map_eq_of_injective (algebraMap F E).injective]

  have hcoeff : ∀ k, ((D.coeff k : N) : C) ∈ M ⊓ N := by
    intro k
    refine ⟨hM _ ?_, (D.coeff k).2⟩
    have e : j ((D.coeff k : N) : C) = (D.map i).coeff k := by
      rw [coeff_map]; rfl
    rw [e, hD, coeff_map]
    exact (m.coeff k).2

  have hDα : (D.map (algebraMap N C)).eval α = 0 := by
    have h0 : j.toRingHom ((D.map (algebraMap N C)).eval α) = 0 := by
      rw [Polynomial.eval_map, Polynomial.hom_eval₂]
      change D.eval₂ i x = 0
      rw [← Polynomial.eval_map, hD, Polynomial.eval_map, ← Polynomial.aeval_def, minpoly.aeval]
    exact (map_eq_zero_iff _ j.toRingHom.injective).1 h0
  by_contra hlt
  rw [not_le] at hlt
  have hDlt : (D.map (algebraMap N C)).natDegree < n := by
    rw [natDegree_map_eq_of_injective (algebraMap N C).injective, hDdeg]
    exact hlt
  have hsum := hDα
  rw [Polynomial.eval_eq_sum_range' hDlt,
    ← Fin.sum_univ_eq_sum_range (fun k => (D.map (algebraMap N C)).coeff k * α ^ k) n] at hsum
  have li := hdisj.linearIndependent_right' pb.basis.linearIndependent
  have hzero := Fintype.linearIndependent_iff.1 li (fun k => ⟨((D.coeff k : N) : C), hcoeff k⟩) (by
    rw [← hsum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Function.comp_apply, PowerBasis.coe_basis, map_pow, Algebra.smul_def, coeff_map]
    rfl)
  have hD0 : D = 0 := by
    refine Polynomial.ext fun k => ?_
    rw [Polynomial.coeff_zero]
    by_cases hk : k < n
    · have h1 := congrArg Subtype.val (hzero ⟨k, hk⟩)
      simpa using h1
    · exact coeff_eq_zero_of_natDegree_lt (p := D) (n := k) (by rw [hDdeg]; omega)
  apply hm0
  have h2 := hD
  rw [hD0, Polynomial.map_zero] at h2
  exact (Polynomial.map_eq_zero_iff (algebraMap F E).injective).1 h2.symm

/- English proof (translation)
Set `pb` to `Field.powerBasisOfFiniteOfSeparable K₀ L`. Use `set x : E := j (algebraMap L C pb.gen) with hx`. Establish `hle` using `le_natDegree_minpoly_of_linearDisjoint j F M N L pb hM (hN pb.gen) hdisj`. Establish `li : LinearIndependent F (fun k : Fin pb.dim => x ^ (k : ℕ))` using `(linearIndependent_pow x).comp (Fin.castLE hle) (Fin.castLE_injective hle)`. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `z hz`. Take `⟨c, rfl⟩` from `TensorProduct.eq_repr_basis_left pb.basis z`. Establish `hc : c = 0`. Use extensionality with `k`. Establish `h3` using `Fintype.linearIndependent_iff.1 li (fun k => c k) (by`.

Rewrite `hz` using `[map_finsuppSum, Finsupp.sum_fintype _ _ (by simp)]`. Rewrite using `[← hz]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.TensorProduct.lift_tmul, PowerBasis.coe_basis, Algebra.smul_def, mul_comm]`. Simplify using `[x, map_pow])`.

Simplify using `using h3 k`. Rewrite using `[hc, Finsupp.sum_zero_index]`.
-/
theorem injective_lift_of_linearDisjoint [FiniteDimensional K₀ L] [Algebra.IsSeparable K₀ L]
    (hM : ∀ y : C, j y ∈ F → y ∈ M)
    (hN : ∀ x : L, ((minpoly K₀ x).map (algebraMap K₀ N)).Splits)
    (hdisj : (M ⊓ N).LinearDisjoint L) :
    Function.Injective (Algebra.TensorProduct.lift (j.comp (IsScalarTower.toAlgHom K₀ L C)) F.val
      fun _ _ => Commute.all _ _) := by
  let pb := Field.powerBasisOfFiniteOfSeparable K₀ L
  set x : E := j (algebraMap L C pb.gen) with hx
  have hle := le_natDegree_minpoly_of_linearDisjoint j F M N L pb hM (hN pb.gen) hdisj
  have li : LinearIndependent F (fun k : Fin pb.dim => x ^ (k : ℕ)) :=
    (linearIndependent_pow x).comp (Fin.castLE hle) (Fin.castLE_injective hle)
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨c, rfl⟩ := TensorProduct.eq_repr_basis_left pb.basis z
  have hc : c = 0 := by
    ext k
    have h3 := Fintype.linearIndependent_iff.1 li (fun k => c k) (by
      rw [map_finsuppSum, Finsupp.sum_fintype _ _ (by simp)] at hz
      rw [← hz]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Algebra.TensorProduct.lift_tmul, PowerBasis.coe_basis, Algebra.smul_def, mul_comm]
      simp [x, map_pow])
    simpa using h3 k
  rw [hc, Finsupp.sum_zero_index]

/- English proof (translation)
Set `g' : B →ₐ[K₀] F` to `{ toFun := fun b => ⟨g b, hgF b⟩ map_one' := Subtype.ext (map_one g) map_mul' := fun a b => Subtype.ext (map_mul g a b) map_zero' := Subtype.ext (map_zero g) map_add' := fun a b => Subtype.ext (map_add g a b) commutes' := fun r => Subtype.ext (g.commutes r) }`. Establish `hg' : Function.Injective g'` using `fun a b h => hg (congrArg Subtype.val h)`. Establish `hflat : Function.Injective (g'.toLinearMap.lTensor L)` using `Module.Flat.lTensor_preserves_injective_linearMap _ hg'`. Establish `heq : ∀ z, Algebra.TensorProduct.lift (j.comp (IsScalarTower.toAlgHom K₀ L C)) F.val (fun _ _ => Commute.all _ _) (g'.toLinearMap.lTensor L z) = Algebra.TensorProduct.lift (j.comp (IsScalarTower.toAlgHom K₀ L C)) g (fun _ _ => Commute.all _ _) z`. Introduce `z`.

Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => simp [g']`. Consider the case `add a b ha hb => rw [map_add, map_add, ha, hb, map_add]`. Introduce `z₁ z₂ h`.

Apply `hflat` to reduce the goal to its premises. Apply `injective_lift_of_linearDisjoint j F M N L hM hN hdisj` to reduce the goal to its premises. Rewrite using `[heq, heq, h]`.
-/
theorem injective_lift_of_forall_mem [FiniteDimensional K₀ L] [Algebra.IsSeparable K₀ L]
    (hM : ∀ y : C, j y ∈ F → y ∈ M)
    (hN : ∀ x : L, ((minpoly K₀ x).map (algebraMap K₀ N)).Splits)
    (hdisj : (M ⊓ N).LinearDisjoint L) {B : Type*} [CommRing B] [Algebra K₀ B] (g : B →ₐ[K₀] E)
    (hg : Function.Injective g) (hgF : ∀ b, g b ∈ F) :
    Function.Injective (Algebra.TensorProduct.lift (j.comp (IsScalarTower.toAlgHom K₀ L C)) g
      fun _ _ => Commute.all _ _) := by
  let g' : B →ₐ[K₀] F :=
    { toFun := fun b => ⟨g b, hgF b⟩
      map_one' := Subtype.ext (map_one g)
      map_mul' := fun a b => Subtype.ext (map_mul g a b)
      map_zero' := Subtype.ext (map_zero g)
      map_add' := fun a b => Subtype.ext (map_add g a b)
      commutes' := fun r => Subtype.ext (g.commutes r) }
  have hg' : Function.Injective g' := fun a b h => hg (congrArg Subtype.val h)
  have hflat : Function.Injective (g'.toLinearMap.lTensor L) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ hg'
  have heq : ∀ z, Algebra.TensorProduct.lift (j.comp (IsScalarTower.toAlgHom K₀ L C)) F.val
      (fun _ _ => Commute.all _ _) (g'.toLinearMap.lTensor L z) =
      Algebra.TensorProduct.lift (j.comp (IsScalarTower.toAlgHom K₀ L C)) g
      (fun _ _ => Commute.all _ _) z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [g']
    | add a b ha hb => rw [map_add, map_add, ha, hb, map_add]
  intro z₁ z₂ h
  apply hflat
  apply injective_lift_of_linearDisjoint j F M N L hM hN hdisj
  rw [heq, heq, h]

end Disjoint

end GroundTheory.PAdicHodge
