import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsAlgebraicElementOfAlgebraicVectorSubspace
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology Polynomial

/- English proof (translation)
Set `b : Basis (Fin P.natDegree) R (AdjoinRoot P)` to `(AdjoinRoot.powerBasis' hP).basis`. Establish `hb : ∀ i : Fin P.natDegree, b i = AdjoinRoot.root P ^ (i : ℕ)` using `fun i => (AdjoinRoot.powerBasis' hP).basis_eq_pow i`. Establish `hr : IsUnit (AdjoinRoot.root P)`. Establish `h1 : AdjoinRoot.mk P (X * divX P + C (P.coeff 0)) = 0`. Rewrite using `[X_mul_divX_add]`.

Conclude with `AdjoinRoot.mk_self`. Rewrite `h1` using `[map_add, map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C]`. Establish `h2 : IsUnit (AdjoinRoot.root P * AdjoinRoot.mk P (divX P))`. Rewrite using `[eq_neg_of_add_eq_zero_left h1]`. Conclude with `(h0.map (AdjoinRoot.of P)).neg`.

Conclude with `isUnit_of_mul_isUnit_left h2`. Use `⟨(Algebra.leftMulMatrix b (AdjoinRoot.root P)).transpose, ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.det_transpose, ← Matrix.isUnit_iff_isUnit_det]`. Conclude with `hr.map _`. Rewrite using `[← AdjoinRoot.mk_eq_mk]`.

Establish `h` using `b.sum_repr (AdjoinRoot.root P * b i)`. Simplify using `only [map_sum, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, Matrix.transpose_apply, Algebra.leftMulMatrix_eq_repr_mul]`. Rewrite using `[pow_succ', ← hb, ← h]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[h, Algebra.smul_def, hb j]`.

Both sides reduce to the same expression.
-/
private theorem companion {R : Type} [CommRing R] (P : R[X]) (hP : P.Monic) (h0 : IsUnit (P.coeff 0)) :
    ∃ M : Matrix (Fin P.natDegree) (Fin P.natDegree) R, IsUnit M.det ∧
      ∀ i : Fin P.natDegree, P ∣ X ^ ((i : ℕ) + 1) - ∑ j : Fin P.natDegree, C (M i j) * X ^ (j : ℕ) := by
  classical
  let b : Basis (Fin P.natDegree) R (AdjoinRoot P) := (AdjoinRoot.powerBasis' hP).basis
  have hb : ∀ i : Fin P.natDegree, b i = AdjoinRoot.root P ^ (i : ℕ) := fun i =>
    (AdjoinRoot.powerBasis' hP).basis_eq_pow i
  have hr : IsUnit (AdjoinRoot.root P) := by
    have h1 : AdjoinRoot.mk P (X * divX P + C (P.coeff 0)) = 0 := by
      rw [X_mul_divX_add]; exact AdjoinRoot.mk_self
    rw [map_add, map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at h1
    have h2 : IsUnit (AdjoinRoot.root P * AdjoinRoot.mk P (divX P)) := by
      rw [eq_neg_of_add_eq_zero_left h1]
      exact (h0.map (AdjoinRoot.of P)).neg
    exact isUnit_of_mul_isUnit_left h2
  refine ⟨(Algebra.leftMulMatrix b (AdjoinRoot.root P)).transpose, ?_, fun i => ?_⟩
  · rw [Matrix.det_transpose, ← Matrix.isUnit_iff_isUnit_det]
    exact hr.map _
  · rw [← AdjoinRoot.mk_eq_mk]
    have h := b.sum_repr (AdjoinRoot.root P * b i)
    simp only [map_sum, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, Matrix.transpose_apply,
      Algebra.leftMulMatrix_eq_repr_mul]
    rw [pow_succ', ← hb, ← h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [h, Algebra.smul_def, hb j]
    rfl

/- English proof (translation)
Introduce `l _ P hP h0 x hx hF g hg`. Break down `Nat.eq_zero_or_pos P.natDegree with hd | hd` into its components or cases. Rewrite `hx` using `[hP.natDegree_eq_zero.1 hd, Polynomial.map_one, map_one, Module.End.one_apply]`. Rewrite using `[hx, map_zero]`. Take `⟨M, hM, hdiv⟩` from `companion P hP h0`.

Take `⟨N, N', hNN, -, hN', hφ, hI⟩` from `UpperTheory.exists_algebraic_element_of_algebraicVectorSubspace M hM`. Set `V : Fin P.natDegree → Bcr l` to `fun i => ((PP l).φB)^[i] x`. Establish `hpow : ∀ k : ℕ, (((PP l).φB.toLinearMap : Module.End ℚ_[l] (Bcr l)) ^ k) x = ((PP l).φB)^[k] x` using `fun k => by rw [Module.End.pow_apply]; rfl`. Establish `hV : ∀ i, (PP l).φB (V i) = ((M.map (fun z => algebraMap ℚ_[l] (Bcr l) (z : ℚ_[l]))).mulVec V) i` using `fun i => by`. Take `⟨Q, hQ⟩` from `hdiv i`.

Establish `h1` using `congrArg (fun p : ℤ_[l][X] => aeval ((PP l).φB.toLinearMap : Module.End ℚ_[l] (Bcr l)) (p.map (algebraMap ℤ_[l] ℚ_[l])) x) hQ`. Rewrite `h1` using `[mul_comm P Q, Polynomial.map_mul, map_mul, Module.End.mul_apply, hx, map_zero]`. Simplify using `only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_sum, Polynomial.map_mul, map_X, map_C, map_sub, map_sum, map_mul, map_pow, aeval_X, aeval_C, LinearMap.sub_apply, LinearMap.sum_apply, Module.End.mul_apply, hpow, Module.algebraMap_end_apply] at h1`. Rewrite `h1` using `[Function.iterate_succ_apply', sub_eq_zero]`. Use `h1.trans (Finset.sum_congr rfl fun j _ => ?_)` and prove the remaining obligations.

Rewrite using `[Algebra.smul_def]`. Both sides reduce to the same expression. Establish `hN'N : N' * N = 1` using `mul_eq_one_comm.1 hNN`. Set `Y : Fin P.natDegree → Bcr l` to `N'.mulVec V`. Establish `hVY : N.mulVec Y = V`.

Simplify using `only [Y, Matrix.mulVec_mulVec, hNN, Matrix.one_mulVec]`. Establish `hφY : ∀ i, (PP l).φB (Y i) = Y i` using `fun i => by`. Establish `h1 : (PP l).φB (Y i) = ((N'.map (PP l).φB).mulVec ((PP l).φB ∘ V)) i` using `RingHom.map_mulVec ((PP l).φB : Bcr l →+* Bcr l) N' V i`. Establish `h2 : (PP l).φB ∘ V = (M.map (fun z => algebraMap ℚ_[l] (Bcr l) (z : ℚ_[l]))).mulVec V`. Use function extensionality and compare the values at `hV`.

Establish `h3 : N'.map (PP l).φB * N.map (PP l).φB = 1`. Use `congrArg ((PP l).φB : Bcr l →+* Bcr l).mapMatrix hN'N` as an intermediate fact. Rewrite `this` using `[map_mul, map_one]`. Conclude with `this`. Rewrite using `[h1, h2, ← hVY, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, ← hφ, h3, Matrix.one_mulVec]`.

Establish `hYF : ∀ i, (PP l).ιB (Y i) ∈ ((PP l).PD (botExt l)).Fil 0` using `fun i => by`. Establish `h1 : Y i = ∑ j, N' i j * V j` using `rfl`. Rewrite using `[h1, map_sum]`. Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`.

Simplify using `using ((PP l).PD (botExt l)).Fil_mul 0 0 _ _ (hN' i j) (hF j)`. Establish `hgY : (PP l).actQ g ∘ Y = Y` using `funext fun i => by`. Take `⟨c, hc⟩` from `((PP l).PD (botExt l)).fund (Y i) (by rw [(PP l).PD_φ]; exact hφY i) (by rw [(PP l).PD_ι]; exact hYF i)`. Express the relevant statement in the definitionally equal form `(PP l).actQ g (Y i) = Y i`. Rewrite using `[← hc, AlgEquiv.commutes]`.

Establish `h1 : (PP l).actQ g (N.mulVec Y ⟨0, hd⟩) = ((N.map ((PP l).actQ g)).mulVec ((PP l).actQ g ∘ Y)) ⟨0, hd⟩` using `RingHom.map_mulVec (((PP l).actQ g : Bcr l ≃ₐ[ℚ_[l]] Bcr l) : Bcr l →+* Bcr l) N Y _`. Rewrite `h1` using `[hI g hg, hgY, hVY]`. Conclude with `h1`.
-/
theorem UpperTheory.inertia_fixes_of_frobenius_annihilated_mem_fil_zero :
    ∀ {l : ℕ} [Fact l.Prime] (P : ℤ_[l][X]), P.Monic → IsUnit (P.coeff 0) → ∀ x : Bcr l, aeval ((PP l).φB.toLinearMap : Module.End ℚ_[l] (Bcr l)) (P.map (algebraMap ℤ_[l] ℚ_[l])) x = 0 → (∀ i : ℕ, (PP l).ιB (((PP l).φB)^[i] x) ∈ ((PP l).PD (botExt l)).Fil 0) → ∀ g ∈ Iq l, (PP l).actQ g x = x := by
  intro l _ P hP h0 x hx hF g hg
  classical
  rcases Nat.eq_zero_or_pos P.natDegree with hd | hd
  · rw [hP.natDegree_eq_zero.1 hd, Polynomial.map_one, map_one, Module.End.one_apply] at hx
    rw [hx, map_zero]
  obtain ⟨M, hM, hdiv⟩ := companion P hP h0
  obtain ⟨N, N', hNN, -, hN', hφ, hI⟩ := UpperTheory.exists_algebraic_element_of_algebraicVectorSubspace M hM
  let V : Fin P.natDegree → Bcr l := fun i => ((PP l).φB)^[i] x
  have hpow : ∀ k : ℕ, (((PP l).φB.toLinearMap : Module.End ℚ_[l] (Bcr l)) ^ k) x = ((PP l).φB)^[k] x :=
    fun k => by rw [Module.End.pow_apply]; rfl
  have hV : ∀ i, (PP l).φB (V i) =
      ((M.map (fun z => algebraMap ℚ_[l] (Bcr l) (z : ℚ_[l]))).mulVec V) i := fun i => by
    obtain ⟨Q, hQ⟩ := hdiv i
    have h1 := congrArg (fun p : ℤ_[l][X] => aeval ((PP l).φB.toLinearMap : Module.End ℚ_[l] (Bcr l))
      (p.map (algebraMap ℤ_[l] ℚ_[l])) x) hQ
    rw [mul_comm P Q, Polynomial.map_mul, map_mul, Module.End.mul_apply, hx, map_zero] at h1
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_sum, Polynomial.map_mul, map_X, map_C,
      map_sub, map_sum, map_mul, map_pow, aeval_X, aeval_C, LinearMap.sub_apply, LinearMap.sum_apply,
      Module.End.mul_apply, hpow, Module.algebraMap_end_apply] at h1
    rw [Function.iterate_succ_apply', sub_eq_zero] at h1
    refine h1.trans (Finset.sum_congr rfl fun j _ => ?_)
    rw [Algebra.smul_def]
    rfl
  have hN'N : N' * N = 1 := mul_eq_one_comm.1 hNN
  let Y : Fin P.natDegree → Bcr l := N'.mulVec V
  have hVY : N.mulVec Y = V := by
    simp only [Y, Matrix.mulVec_mulVec, hNN, Matrix.one_mulVec]
  have hφY : ∀ i, (PP l).φB (Y i) = Y i := fun i => by
    have h1 : (PP l).φB (Y i) = ((N'.map (PP l).φB).mulVec ((PP l).φB ∘ V)) i :=
      RingHom.map_mulVec ((PP l).φB : Bcr l →+* Bcr l) N' V i
    have h2 : (PP l).φB ∘ V = (M.map (fun z => algebraMap ℚ_[l] (Bcr l) (z : ℚ_[l]))).mulVec V :=
      funext hV
    have h3 : N'.map (PP l).φB * N.map (PP l).φB = 1 := by
      have := congrArg ((PP l).φB : Bcr l →+* Bcr l).mapMatrix hN'N
      rw [map_mul, map_one] at this
      exact this
    rw [h1, h2, ← hVY, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, ← hφ, h3,
      Matrix.one_mulVec]
  have hYF : ∀ i, (PP l).ιB (Y i) ∈ ((PP l).PD (botExt l)).Fil 0 := fun i => by
    have h1 : Y i = ∑ j, N' i j * V j := rfl
    rw [h1, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [map_mul]
    simpa using ((PP l).PD (botExt l)).Fil_mul 0 0 _ _ (hN' i j) (hF j)
  have hgY : (PP l).actQ g ∘ Y = Y := funext fun i => by
    obtain ⟨c, hc⟩ := ((PP l).PD (botExt l)).fund (Y i) (by rw [(PP l).PD_φ]; exact hφY i)
      (by rw [(PP l).PD_ι]; exact hYF i)
    change (PP l).actQ g (Y i) = Y i
    rw [← hc, AlgEquiv.commutes]
  have h1 : (PP l).actQ g (N.mulVec Y ⟨0, hd⟩) =
      ((N.map ((PP l).actQ g)).mulVec ((PP l).actQ g ∘ Y)) ⟨0, hd⟩ :=
    RingHom.map_mulVec (((PP l).actQ g : Bcr l ≃ₐ[ℚ_[l]] Bcr l) : Bcr l →+* Bcr l) N Y _
  rw [hI g hg, hgY, hVY] at h1
  exact h1
