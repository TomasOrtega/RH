import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.NormAlmostAll
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.NmPoly
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.SeparableOfMap
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.NmCent

open Matrix Polynomial NumberField IsDedekindDomain
open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.D

/- English proof (translation)
Unfold `cp`. Rewrite using `[← Matrix.charpoly_map]`. Both sides reduce to the same expression.
-/
private theorem cp_map {S R : Type} [CommRing S] [CommRing R] {n : ℕ} (j : S →+* R) (g : GL (Fin n) S) :
    cp (Matrix.GeneralLinearGroup.map j g) = (cp g).map j := by
  unfold cp
  rw [← Matrix.charpoly_map]
  rfl

/- English proof (translation)
Unfold `cp`. Rewrite using `[Units.val_mul, Matrix.charpoly_mul_comm, ← Units.val_mul, ← mul_assoc, mul_inv_cancel, one_mul]`.
-/
private theorem cp_conj {R : Type} [CommRing R] {n : ℕ} (x g : GL (Fin n) R) :
    cp (x⁻¹ * g * x) = cp g := by
  unfold cp
  rw [Units.val_mul, Matrix.charpoly_mul_comm, ← Units.val_mul, ← mul_assoc, mul_inv_cancel, one_mul]

section
variable {O S k R : Type} [CommRing O] [CommRing S] [Algebra O S] [CommRing k] [CommRing R] [Algebra k R] {n : ℕ}

/- English proof (translation)
Use extensionality with `a b`. Conclude with `h _`.
-/
private theorem map_sg (j : S →+* R) (s : S ≃ₐ[O] S) (σ : R ≃ₐ[k] R) (h : ∀ x, j (s x) = σ (j x))
    (g : GL (Fin n) S) :
    Matrix.GeneralLinearGroup.map j (sg s g) = sg σ (Matrix.GeneralLinearGroup.map j g) := by
  ext a b
  exact h _

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => intro x`. Both sides reduce to the same expression. Consider the case `succ m ih => intro x`. Rewrite using `[pow_succ, pow_succ, AlgEquiv.mul_apply, AlgEquiv.mul_apply, ih, h]`.
-/
private theorem pow_comp (j : S →+* R) (s : S ≃ₐ[O] S) (σ : R ≃ₐ[k] R) (h : ∀ x, j (s x) = σ (j x))
    (m : ℕ) : ∀ x, j ((s ^ m) x) = (σ ^ m) (j x) := by
  induction m with
  | zero => intro x; rfl
  | succ m ih => intro x; rw [pow_succ, pow_succ, AlgEquiv.mul_apply, AlgEquiv.mul_apply, ih, h]

/- English proof (translation)
Unfold `nm`. Rewrite using `[map_list_prod, List.map_map]`. Use `congr 1`. Use `List.map_congr_left fun m _ => ?_` and prove the remaining obligations. Conclude with `map_sg j (s ^ m) (σ ^ m) (pow_comp j s σ h m) g`.
-/
private theorem map_nm (j : S →+* R) (s : S ≃ₐ[O] S) (σ : R ≃ₐ[k] R) (h : ∀ x, j (s x) = σ (j x))
    (q : ℕ) (g : GL (Fin n) S) :
    Matrix.GeneralLinearGroup.map j (nm s q g) = nm σ q (Matrix.GeneralLinearGroup.map j g) := by
  unfold nm
  rw [map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun m _ => ?_
  exact map_sg j (s ^ m) (σ ^ m) (pow_comp j s σ h m) g

/- English proof (translation)
Use extensionality with `a b`. Conclude with `h _`.
-/
private theorem map_up (i : O →+* k) (j : S →+* R) (h : ∀ x, j (algebraMap O S x) = algebraMap k R (i x))
    (g : GL (Fin n) O) :
    Matrix.GeneralLinearGroup.map j (up S g) = up R (Matrix.GeneralLinearGroup.map i g) := by
  ext a b
  exact h _

end

end UpperTheory.ConvolutionTheory.D

/- English proof (translation)
Introduce `O S k R _ _ _ _ _ _ _ i j s σ q hs hσ hj hjs hji n a a' γ hγ ha x hx`. Establish `h1 : cp (nm s q a') = cp (nm s q a)`. Apply `Polynomial.map_injective j hj` to reduce the goal to its premises. Rewrite using `[← cp_map, ← cp_map, map_nm j s σ hjs, map_nm j s σ hjs, ← hx, (nmPoly k R σ q hσ n _).2, cp_conj]`. Establish `h2 : (cp (nm s q a)).Separable`.

Rewrite using `[ha, up, cp_map]`. Conclude with `hγ.map`. Take `⟨u, hu⟩` from `nmInj O S s q hs n a a' h2 h1`. Establish `h3 : (cp (Matrix.GeneralLinearGroup.map i γ)).Separable`. Rewrite using `[cp_map]`.

Conclude with `hγ.map`. Establish `h4 : nm σ q (Matrix.GeneralLinearGroup.map j a) = up R (Matrix.GeneralLinearGroup.map i γ)`. Rewrite using `[← map_nm j s σ hjs, ha, map_up i j hji]`. Establish `h5 : sgConj σ (x * (Matrix.GeneralLinearGroup.map j u)⁻¹) (Matrix.GeneralLinearGroup.map j a) = Matrix.GeneralLinearGroup.map j a`. Rewrite `hx` using `[hu, sgConj, sgConj, map_mul, map_mul, map_inv, map_sg j s σ hjs]`.

Rewrite using `[sgConj, map_mul, map_inv]`. Combine the equalities or inequalities in the displayed calculation. Take `⟨t, ht, hxt⟩` from `(nmCent k R σ q hσ n _ _ h3 h4 _).1 h5`. Conclude with `⟨t, u, ht, by rw [← hxt]; group⟩`.
-/
theorem UpperTheory.ConvolutionTheory.D.nmInt :
    UpperTheory.ConvolutionTheory.D.NmInt := by
  intro O S k R _ _ _ _ _ _ _ i j s σ q hs hσ hj hjs hji n a a' γ hγ ha x hx
  have h1 : cp (nm s q a') = cp (nm s q a) := by
    apply Polynomial.map_injective j hj
    rw [← cp_map, ← cp_map, map_nm j s σ hjs, map_nm j s σ hjs, ← hx,
      (nmPoly k R σ q hσ n _).2, cp_conj]
  have h2 : (cp (nm s q a)).Separable := by
    rw [ha, up, cp_map]
    exact hγ.map
  obtain ⟨u, hu⟩ := nmInj O S s q hs n a a' h2 h1
  have h3 : (cp (Matrix.GeneralLinearGroup.map i γ)).Separable := by
    rw [cp_map]
    exact hγ.map
  have h4 : nm σ q (Matrix.GeneralLinearGroup.map j a) = up R (Matrix.GeneralLinearGroup.map i γ) := by
    rw [← map_nm j s σ hjs, ha, map_up i j hji]
  have h5 : sgConj σ (x * (Matrix.GeneralLinearGroup.map j u)⁻¹) (Matrix.GeneralLinearGroup.map j a) =
      Matrix.GeneralLinearGroup.map j a := by
    rw [hu, sgConj, sgConj, map_mul, map_mul, map_inv, map_sg j s σ hjs] at hx
    rw [sgConj, map_mul, map_inv]
    calc _ = Matrix.GeneralLinearGroup.map j u * (x⁻¹ * Matrix.GeneralLinearGroup.map j a * sg σ x) *
          (sg σ (Matrix.GeneralLinearGroup.map j u))⁻¹ := by group
      _ = _ := by rw [hx]; group
  obtain ⟨t, ht, hxt⟩ := (nmCent k R σ q hσ n _ _ h3 h4 _).1 h5
  exact ⟨t, u, ht, by rw [← hxt]; group⟩
