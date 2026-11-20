import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AtVecMulVecRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLagrangianSetArchimedean
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianSetAdditiveSubgroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviMapPreservesRationalPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviElementSkewCm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleAdaptedLagrangianEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HTensVmvLeft
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ArchSch GlobalTheory.ArchSchB GlobalTheory.ArchSchA

noncomputable section

namespace GlobalTheory.ArchSchA.Coiso

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Establish `key` using `(GlobalTheory.LeviRatHerm.decomp hX.lat hH).1`. Use `choose a t u hsu using fun j : Fin n => key (Pi.single j 1)`. Establish `hI : (1 : Matrix (Fin n) (Fin n) E) = Matrix.vecMulVec H.x a + H.ι * (Matrix.of u)ᵀ + Matrix.vecMulVec H.y t`. Use extensionality with `l j`. Use `congrFun (hsu j) l` as an intermediate fact.

Simplify using `only [Pi.single_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct] at this`. Simplify using `only [Matrix.one_apply, Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply]`. Rewrite using `[this, mul_comm (a j), mul_comm (t j)]`. Establish `h0 : ∀ c : AF F, evI F c = 0 → ∀ i j, c • w i j = 0` using `fun c hc i j => by`. Simplify using `using congrFun (congrFun (hw c hc) i) j`.

Establish `hAt : ∀ v : Fin n → AE F E, At (evI F) (v ᵥ* w)`. Introduce `v c hc`. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.smul_apply, Matrix.vecMul, dotProduct, Finset.smul_sum, ← mul_smul_comm, h0 c hc, mul_zero, Finset.sum_const_zero, Pi.zero_apply]`. Use `⟨incV F a ᵥ* w, incV F t ᵥ* w, incM F (Matrix.of u)ᵀ * w, hAt _, hAt _, ?_, ?_⟩` and prove the remaining obligations.

Introduce `c hc`. Use extensionality with `i k`. Simplify using `only [Matrix.smul_apply, Matrix.mul_apply, Finset.smul_sum, ← mul_smul_comm, h0 c hc, mul_zero, Finset.sum_const_zero, Matrix.zero_apply]`. Establish `hI'` using `congrArg (incM F) hI`. Establish `e1 : incM F (1 : Matrix (Fin n) (Fin n) E) = 1` using `Matrix.map_one _ (map_zero _) (map_one _)`.

Establish `e2 : incM F (Matrix.vecMulVec H.x a + H.ι * (Matrix.of u)ᵀ + Matrix.vecMulVec H.y t) = Matrix.vecMulVec (incV F H.x) (incV F a) + incM F H.ι * incM F (Matrix.of u)ᵀ + Matrix.vecMulVec (incV F H.y) (incV F t)`. Use extensionality with `i j`. Simplify using `[incM, incV, Matrix.vecMulVec_apply, Matrix.mul_apply, map_sum, map_add, map_mul]`. Rewrite `hI'` using `[e1, e2]`. Use `conv_lhs => rw [← Matrix.one_mul w, hI']`.

Establish `hv : ∀ p q : Fin n → AE F E, Matrix.vecMulVec p q * w = Matrix.vecMulVec p (q ᵥ* w)`. Introduce `p q`. Use extensionality with `i l`. Simplify using `[Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.vecMul, dotProduct, Finset.mul_sum, mul_assoc]`. Rewrite using `[Matrix.add_mul, Matrix.add_mul, hv, hv, Matrix.mul_assoc]`.
-/
theorem decompose_left (B : Base F E) {n d n₁ r s i₀ i₁ : ℕ} {X : Spc F E n} {X₁ : Spc F E n₁} {H : Plane E n n₁}
    (hX : X.IsHerm σ B r s) (hH : H.IsAdapted σ B X X₁ i₀ i₁) (w : Matrix (Fin n) (Fin d) (AE F E)) (hw : At (evI F) w) :
    ∃ (α β : Fin d → AE F E) (C : Matrix (Fin n₁) (Fin d) (AE F E)), At (evI F) α ∧ At (evI F) β ∧ At (evI F) C ∧
      w = Matrix.vecMulVec (incV F H.x) α + incM F H.ι * C + Matrix.vecMulVec (incV F H.y) β := by
  have key := (GlobalTheory.LeviRatHerm.decomp hX.lat hH).1
  choose a t u hsu using fun j : Fin n => key (Pi.single j 1)
  have hI : (1 : Matrix (Fin n) (Fin n) E) =
      Matrix.vecMulVec H.x a + H.ι * (Matrix.of u)ᵀ + Matrix.vecMulVec H.y t := by
    ext l j
    have := congrFun (hsu j) l
    simp only [Pi.single_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct] at this
    simp only [Matrix.one_apply, Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.of_apply,
      Matrix.transpose_apply]
    rw [this, mul_comm (a j), mul_comm (t j)]
  have h0 : ∀ c : AF F, evI F c = 0 → ∀ i j, c • w i j = 0 := fun c hc i j => by
    simpa using congrFun (congrFun (hw c hc) i) j
  have hAt : ∀ v : Fin n → AE F E, At (evI F) (v ᵥ* w) := by
    intro v c hc; funext i
    simp only [Pi.smul_apply, Matrix.vecMul, dotProduct, Finset.smul_sum, ← mul_smul_comm, h0 c hc, mul_zero,
      Finset.sum_const_zero, Pi.zero_apply]
  refine ⟨incV F a ᵥ* w, incV F t ᵥ* w, incM F (Matrix.of u)ᵀ * w, hAt _, hAt _, ?_, ?_⟩
  · intro c hc; ext i k
    simp only [Matrix.smul_apply, Matrix.mul_apply, Finset.smul_sum, ← mul_smul_comm, h0 c hc, mul_zero,
      Finset.sum_const_zero, Matrix.zero_apply]
  · have hI' := congrArg (incM F) hI
    have e1 : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
    have e2 : incM F (Matrix.vecMulVec H.x a + H.ι * (Matrix.of u)ᵀ + Matrix.vecMulVec H.y t) =
        Matrix.vecMulVec (incV F H.x) (incV F a) + incM F H.ι * incM F (Matrix.of u)ᵀ +
          Matrix.vecMulVec (incV F H.y) (incV F t) := by
      ext i j
      simp [incM, incV, Matrix.vecMulVec_apply, Matrix.mul_apply, map_sum, map_add, map_mul]
    rw [e1, e2] at hI'
    conv_lhs => rw [← Matrix.one_mul w, hI']
    have hv : ∀ p q : Fin n → AE F E, Matrix.vecMulVec p q * w = Matrix.vecMulVec p (q ᵥ* w) := by
      intro p q; ext i l
      simp [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.vecMul, dotProduct, Finset.mul_sum, mul_assoc]
    rw [Matrix.add_mul, Matrix.add_mul, hv, hv, Matrix.mul_assoc]

/- English proof (translation)
Establish `hdet : IsUnit (incM F J).det`. Establish `h : (incM F J).det = inclR (F` using `F) (AF F) J.det := by`. Rewrite using `[RingHom.map_det]`. Both sides reduce to the same expression. Rewrite using `[h]`.

Conclude with `(isUnit_iff_ne_zero.2 hJ).map _`. Establish `hv : b ᵥ* incM F J = 0`. Use function extensionality and compare the values at `k`. Apply `GlobalTheory.ArchSch.trAE_nondeg _ (GlobalTheory.ArchTraceNondeg.at_vecMul hb _ k)` to reduce the goal to its premises. Introduce `t ht`.

Establish `h` using `hc (Pi.single k (GlobalTheory.ArchTraceNondeg.cAinv σ t)) (GlobalTheory.ArchTraceNondeg.at_single k (GlobalTheory.ArchTraceNondeg.at_cAinv σ ht))`. Rewrite `h` using `[Matrix.dotProduct_mulVec]`. Establish `hw : (fun j => cA σ ((Pi.single k (GlobalTheory.ArchTraceNondeg.cAinv σ t) : Fin n → AE F E) j)) = Pi.single k t`. Use function extensionality and compare the values at `j`. Distinguish the cases in `hj : j = k`.

Substitute `hj` using the available equality. Simplify using `[GlobalTheory.ArchTraceNondeg.cA_cAinv]`. Simplify using `[Pi.single_apply, hj]`. Rewrite `h` using `[hw, dotProduct_single]`. Conclude with `h`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem eq_zero_of_trace_gram (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (hJ : J.det ≠ 0)
    (b : Fin n → AE F E) (hb : At (evI F) b)
    (hc : ∀ c : Fin n → AE F E, At (evI F) c → Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
      (evI F (Algebra.trace (AF F) (AE F E) (b ⬝ᵥ (incM F J *ᵥ fun k => cA σ (c k))))) = 0) : b = 0 := by
  have hdet : IsUnit (incM F J).det := by
    have h : (incM F J).det = inclR (F := F) (AF F) J.det := by
      rw [RingHom.map_det]; rfl
    rw [h]
    exact (isUnit_iff_ne_zero.2 hJ).map _
  have hv : b ᵥ* incM F J = 0 := by
    funext k
    apply GlobalTheory.ArchSch.trAE_nondeg _ (GlobalTheory.ArchTraceNondeg.at_vecMul hb _ k)
    intro t ht
    have h := hc (Pi.single k (GlobalTheory.ArchTraceNondeg.cAinv σ t))
      (GlobalTheory.ArchTraceNondeg.at_single k (GlobalTheory.ArchTraceNondeg.at_cAinv σ ht))
    rw [Matrix.dotProduct_mulVec] at h
    have hw : (fun j => cA σ ((Pi.single k (GlobalTheory.ArchTraceNondeg.cAinv σ t) : Fin n → AE F E) j)) = Pi.single k t := by
      funext j
      by_cases hj : j = k
      · subst hj; simp [GlobalTheory.ArchTraceNondeg.cA_cAinv]
      · simp [Pi.single_apply, hj]
    rw [hw, dotProduct_single] at h
    exact h
  calc b = b ᵥ* (incM F J * (incM F J)⁻¹) := by rw [Matrix.mul_nonsing_inv _ hdet, Matrix.vecMul_one]
    _ = (b ᵥ* incM F J) ᵥ* (incM F J)⁻¹ := (Matrix.vecMul_vecMul _ _ _).symm
    _ = 0 := by rw [hv, Matrix.zero_vecMul]

/- English proof (translation)
Rewrite using `[Finset.sum_mul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.vecMulVec_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem vmv_sum {A α β : Type} [CommRing A] [Fintype α] [Fintype β] (u : α → A) (v : β → A) (P : α → A) (Q : β → A) :
    ∑ i, ∑ j, Matrix.vecMulVec u v i j * P i * Q j = (∑ i, u i * P i) * ∑ j, v j * Q j := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.vecMulVec_apply]; ring

/- English proof (translation)
Simplify using `only [Matrix.mul_apply, Finset.sum_mul]`. Rewrite using `[OrthPlane.sum_three_comm]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem prod_sum {A α β γ : Type} [CommRing A] [Fintype α] [Fintype β] [Fintype γ] (M : Matrix α γ A) (C : Matrix γ β A)
    (P : α → A) (Q : β → A) :
    ∑ i, ∑ j, (M * C) i j * P i * Q j = ∑ m, (∑ i, M i m * P i) * ∑ j, C m j * Q j := by
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [OrthPlane.sum_three_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Use `set P : Fin n → AE F E := fun i => ∑ k, incM F X.J i k * cA σ (incV F H.x k) with hPdef`. Establish `hform : ∀ u : Fin n → E, ∑ i, inclR (F` using `F) (AF F) (u i) * P i = inclR (F := F) (AF F) (form σ X.J u H.x) := by`. Introduce `u`. Simplify using `only [hPdef, form, dotProduct, Matrix.mulVec, incM, incV, Matrix.map_apply, OrthPlane.cA_inclR, map_sum, map_mul, Finset.mul_sum]`. Establish `hcol : ∀ m, H.ι *ᵥ Pi.single m 1 = fun j => H.ι j m`.

Introduce `m`. Use extensionality with `j`. Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply]`. Unfold `symp`. Rewrite using `[TensForm.hTens_add_left, TensForm.hTens_add_left, TensForm.hTens_vmv_right, TensForm.hTens_vmv_right, TensForm.hTens_vmv_right, vmv_sum, vmv_sum, prod_sum]`.

Establish `h1 : ∑ i, incV F H.x i * P i = 0`. Simplify using `only [incV]`. Rewrite using `[hform, hA.xx, map_zero]`. Establish `h2 : ∀ m, ∑ i, incM F H.ι i m * P i = 0`. Introduce `m`.

Use `hform (fun i => H.ι i m)` as an intermediate fact. Simplify using `only [incM, Matrix.map_apply]`. Rewrite using `[this, ← hcol, (hA.orth _).1, map_zero]`. Establish `h3 : ∑ i, incV F H.y i * P i = 1`. Simplify using `only [incV]`.

Rewrite using `[hform, Iso.form_herm hinv hX.herm, hA.xy, map_one, map_one]`. Simplify using `only [hPdef] at h1 h2 h3 ⊢`. Simplify using `only [h1, h2, h3, zero_mul, Finset.sum_const_zero, zero_add, one_mul, neg_mul, map_neg, dotProduct, Matrix.mulVec]`.
-/
theorem symplectic_form_adapted_coordinates (hinv : ∀ t, σ (σ t) = t) (B : Base F E) {n d n₁ r s i₀ i₁ : ℕ} {X : Spc F E n} {X₁ : Spc F E n₁}
    {H : Plane E n n₁} (JW : Matrix (Fin d) (Fin d) E) (hX : X.IsHerm σ B r s) (hA : H.IsAdapted σ B X X₁ i₀ i₁)
    (α β a : Fin d → AE F E) (C : Matrix (Fin n₁) (Fin d) (AE F E)) :
    symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F JW)
      (Matrix.vecMulVec (incV F H.x) α + incM F H.ι * C + Matrix.vecMulVec (incV F H.y) β) (Matrix.vecMulVec (incV F H.x) a) =
    -Algebra.trace (AF F) (AE F E) (β ⬝ᵥ (incM F JW *ᵥ fun k => cA σ (a k))) := by
  set P : Fin n → AE F E := fun i => ∑ k, incM F X.J i k * cA σ (incV F H.x k) with hPdef
  have hform : ∀ u : Fin n → E, ∑ i, inclR (F := F) (AF F) (u i) * P i = inclR (F := F) (AF F) (form σ X.J u H.x) := by
    intro u
    simp only [hPdef, form, dotProduct, Matrix.mulVec, incM, incV, Matrix.map_apply, OrthPlane.cA_inclR, map_sum, map_mul,
      Finset.mul_sum]
  have hcol : ∀ m, H.ι *ᵥ Pi.single m 1 = fun j => H.ι j m := by
    intro m; ext j; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  unfold symp
  rw [TensForm.hTens_add_left, TensForm.hTens_add_left, TensForm.hTens_vmv_right, TensForm.hTens_vmv_right,
    TensForm.hTens_vmv_right, vmv_sum, vmv_sum, prod_sum]
  have h1 : ∑ i, incV F H.x i * P i = 0 := by
    simp only [incV]; rw [hform, hA.xx, map_zero]
  have h2 : ∀ m, ∑ i, incM F H.ι i m * P i = 0 := by
    intro m
    have := hform (fun i => H.ι i m)
    simp only [incM, Matrix.map_apply]
    rw [this, ← hcol, (hA.orth _).1, map_zero]
  have h3 : ∑ i, incV F H.y i * P i = 1 := by
    simp only [incV]; rw [hform, Iso.form_herm hinv hX.herm, hA.xy, map_one, map_one]
  simp only [hPdef] at h1 h2 h3 ⊢
  simp only [h1, h2, h3, zero_mul, Finset.sum_const_zero, zero_add, one_mul, neg_mul, map_neg, dotProduct, Matrix.mulVec]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Finset.mul_sum, Matrix.transpose_apply]`. Conclude with `Finset.sum_congr rfl fun _ _ => by ring`.
-/
theorem vmv_mul_transpose {m k l : ℕ} (x : Fin m → AE F E) (c : Fin k → AE F E) (P : Matrix (Fin l) (Fin k) (AE F E)) :
    Matrix.vecMulVec x c * Pᵀ = Matrix.vecMulVec x (P *ᵥ c) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Finset.mul_sum, Matrix.transpose_apply]
  exact Finset.sum_congr rfl fun _ _ => by ring

/- English proof (translation)
Use `show InfiniteAdeleRing.ringEquiv_mixedSpace F (-a.1) = -InfiniteAdeleRing.ringEquiv_mixedSpace F a.1`. Conclude with `map_neg _ _`.
-/
theorem evI_neg (a : AF F) : evI F (-a) = -evI F a := by
  show InfiniteAdeleRing.ringEquiv_mixedSpace F (-a.1) = -InfiniteAdeleRing.ringEquiv_mixedSpace F a.1
  exact map_neg _ _

end GlobalTheory.ArchSchA.Coiso

namespace GlobalTheory.ArchSchA

open GlobalTheory.ArchSchA.Coiso GlobalTheory.ArchSchB.Iso in

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ X W X₁ W₁ M M₁ H H' hB hX hW hH hH' v hv`. Establish `hω` using `fun w w' => GlobalTheory.ArchSch.trace_evI_darboux M.co w w'`. Establish `hω₁` using `fun z z' => GlobalTheory.ArchSch.trace_evI_darboux M₁.co z z'`. Establish `hinv : ∀ t, σ (σ t) = t` using `fun t => by`. Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`.

Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[hB.cm.2.2.2, hB.cm.2.2.2, star_star]`. Take `⟨w, hwA, hw1, hw2⟩` from `GlobalTheory.ArchSch.exists_darboux_lift M.co v.1 v.2`. Establish `key : ∀ w', (arch F (M.co.e w').1, arch F (M.co.e w').2) ∈ lagSetA M M₁ H H' → Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (symp (R` using `AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) w w')) = 0 := by`. Introduce `w' hl`.

Use `hv _ hl` as an intermediate fact. Rewrite using `[hω, hw1, hw2]`. Conclude with `sub_eq_zero.mpr this`. Take `⟨a, b, Z, ha, hb, hZ, rfl⟩` from `GlobalTheory.ThK.DecW.decompose B W W₁ H' r' s' i₀ i₁ hW hH' w hwA`. Establish `hb0 : b = 0`.

Use `GlobalTheory.ArchTraceNondeg.eq_zero_of_trace_orth B X r s GlobalTheory.ArchSch.trAE_nondeg hX b hb fun c hc => ?_` and prove the remaining obligations. Use `key _ (mem_lagSetA_y M M₁ H H' hc)` as an intermediate fact. Rewrite `this` using `[lagL_dar_add_left M.co, lagL_dar_add_left M.co, GlobalTheory.LagIsotropic.symp_vecMulVec_x_eq_zero B W W₁ H' i₀ i₁ X.J hH', (GlobalTheory.ArchSch.OrthPlane.symp_tens_orth B W W₁ H' r' s' i₀ i₁ X.J hB hW hH' c Z).1, GlobalTheory.ArchSch.symp_dual_iso B W W₁ H' r' s' i₀ i₁ X.J hW …`. Then use the resulting hypothesis. Substitute `hb0` using the available equality. Rewrite `key`, `hw1`, `hw2` using `[zero_vecMulVec', add_zero]`.

Establish `e1 : incM F (1 : Matrix (Fin n) (Fin n) E) = 1` using `Matrix.map_one _ (map_zero _) (map_one _)`. Establish `key₁ : ∀ z' : Matrix (Fin n) (Fin d₁) (AE F E), (arch F (M.co.e (z' * (incM F H'.ι)ᵀ)).1, arch F (M.co.e (z' * (incM F H'.ι)ᵀ)).2) ∈ lagSetA M M₁ H H' → Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (symp (R` using `AF F) (cA σ) (-1) (incM F X.J) (incM F W₁.J) Z z')) = 0 := by`. Introduce `z' hl`. Use `key (incM F (1 : Matrix (Fin n) (Fin n) E) * z' * (incM F H'.ι)ᵀ) (by rwa [e1, Matrix.one_mul])` as an intermediate fact. Rewrite `this` using `[lagL_dar_add_left M.co, (GlobalTheory.ArchSch.OrthPlane.symp_tens_orth B W W₁ H' r' s' i₀ i₁ X.J hB hW hH' a z').2.1, GlobalTheory.SympRestrict.symp_embed_eq B W W₁ H' i₀ i₁ X.J hH', zero_add]`. Then use the resulting hypothesis.

Take `⟨α, β, C, hα, hβ, hC, rfl⟩` from `decompose_left B hX hH Z hZ`. Establish `hβ0 : β = 0`. Use `eq_zero_of_trace_gram σ W₁.J (GlobalTheory.LeviAdapted.isUnit_det_low hinv hW hH').ne_zero β hβ fun c hc => ?_` and prove the remaining obligations. Establish `h` using `key₁ (Matrix.vecMulVec (incV F H.x) c) (by rw [vmv_mul_transpose]; exact mem_lagSetA_c M M₁ H H' hc)`. Rewrite `h` using `[symplectic_form_adapted_coordinates hinv B W₁.J hX hH, evI_neg, map_neg, neg_eq_zero]`. Then use the resulting hypothesis.

Substitute `hβ0` using the available equality. Rewrite `key₁`, `hw1`, `hw2` using `[vecMulVec_zero', add_zero]`. Establish `hflipX : ∀ u v, form σ X.J u v = 0 → form σ X.J v u = 0` using `fun u v h => by`. Rewrite using `[form_herm hinv hX.herm, h, map_zero]`. Establish `h0 : ∀ {p q : Type}, incM F (0 : Matrix p q E) = 0` using `fun {p q} => by ext; simp [incM]`.

Establish `hXI : (incM F (Matrix.replicateCol Unit H.x))ᵀ * incM F X.J * (incM F H.ι).map (cA σ) = 0`. Rewrite using `[incM_gram, gram_xι hH hflipX, h0]`. Establish `hGX : (incM F H.ι)ᵀ * incM F X.J * (incM F H.ι).map (cA σ) = incM F X₁.J`. Rewrite using `[incM_gram, hH.gram]`. Establish `hG1 : (1 : Matrix (Fin d₁) (Fin d₁) (AE F E))ᵀ * incM F W₁.J * (1 : Matrix (Fin d₁) (Fin d₁) (AE F E)).map (cA σ) = incM F W₁.J`.

Rewrite using `[Matrix.transpose_one, Matrix.one_mul, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]`. Establish `hA : Matrix.vecMulVec (incV F H.x) α = incM F (Matrix.replicateCol Unit H.x) * Matrix.replicateRow Unit α * (1 : Matrix (Fin d₁) (Fin d₁) (AE F E))ᵀ`. Rewrite using `[Matrix.transpose_one, Matrix.mul_one, Matrix.vecMulVec_eq Unit]`. Use `congr 1`. Establish `hι : ∀ z : Matrix (Fin n₁) (Fin d₁) (AE F E), incM F H.ι * z = incM F H.ι * z * (1 : Matrix (Fin d₁) (Fin d₁) (AE F E))ᵀ` using `fun z => by`.

Rewrite using `[Matrix.transpose_one, Matrix.mul_one]`. Establish `hpair : ∀ z' : Matrix (Fin n₁) (Fin d₁) (AE F E), symp (R` using `AF F) (cA σ) (-1) (incM F X.J) (incM F W₁.J) (Matrix.vecMulVec (incV F H.x) α + incM F H.ι * C) (incM F H.ι * z') = symp (R := AF F) (cA σ) (-1) (incM F X₁.J) (incM F W₁.J) C z' := by`. Introduce `z'`. Establish `e₁` using `symp_change_zero_left (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W₁.J) _ (1 : Matrix (Fin d₁) (Fin d₁) (AE F E)) _ (1 : Matrix (Fin d₁) (Fin d₁) (AE F E)) (Matrix.replicateRow Unit α) z' hXI`. Establish `e₂` using `symp_change_eq (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W₁.J) _ _ _ _ C z' hGX hG1`.

Rewrite `e₁` using `[← hA, ← hι]`. Rewrite `e₂` using `[← hι, ← hι]`. Rewrite using `[← e₂]`. Unfold `symp at e₁ ⊢`. Rewrite using `[TensForm.hTens_add_left, mul_add, map_add, e₁, zero_add]`.

Establish `hp : arch F (M₁.co.e C).1 = 0`. Use function extensionality and compare the values at `i`. Use `GlobalTheory.mixedSpace_traceForm_nondegenerate F _ fun η => ?_` and prove the remaining obligations. Take `⟨z', hz'A, hz'1, hz'2⟩` from `GlobalTheory.ArchSch.exists_darboux_lift M₁.co 0 (Pi.single i η)`. Use `key₁ _ (mem_lagrangian_set_archimedean M M₁ H H' hz'A hz'1)` as an intermediate fact.

Rewrite `this` using `[hpair, hω₁, hz'1, hz'2]`. Simplify `this` using `[mixedTracePairing_apply, Pi.single_apply]`. Rewrite `hw1`, `hw2` using `[e1, Matrix.one_mul, Matrix.add_mul, vmv_mul_transpose, ← add_assoc]`. Conclude with `⟨a, α, C, ha, hα, hC, hp, Prod.ext hw1.symm hw2.symm⟩`.
-/
theorem lagSetA_coisotropic : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E) {n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} (M : Model σ X W) (M₁ : Model σ X₁ W₁) (H : Plane E n n₁) (H' : Plane E d d₁),
    B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ v, (∀ l ∈ lagSetA M M₁ H H', trP F _ v.1 l.2 = trP F _ l.1 v.2) → v ∈ lagSetA M M₁ H H' := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ X W X₁ W₁ M M₁ H H' hB hX hW hH hH' v hv
  have hω := fun w w' => GlobalTheory.ArchSch.trace_evI_darboux M.co w w'
  have hω₁ := fun z z' => GlobalTheory.ArchSch.trace_evI_darboux M₁.co z z'
  have hinv : ∀ t, σ (σ t) = t := fun t => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star]
  obtain ⟨w, hwA, hw1, hw2⟩ := GlobalTheory.ArchSch.exists_darboux_lift M.co v.1 v.2
  have key : ∀ w', (arch F (M.co.e w').1, arch F (M.co.e w').2) ∈ lagSetA M M₁ H H' →
      Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
        (evI F (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) w w')) = 0 := by
    intro w' hl
    have := hv _ hl
    rw [hω, hw1, hw2]
    exact sub_eq_zero.mpr this
  obtain ⟨a, b, Z, ha, hb, hZ, rfl⟩ := GlobalTheory.ThK.DecW.decompose B W W₁ H' r' s' i₀ i₁ hW hH' w hwA
  have hb0 : b = 0 := by
    refine GlobalTheory.ArchTraceNondeg.eq_zero_of_trace_orth B X r s GlobalTheory.ArchSch.trAE_nondeg hX b hb fun c hc => ?_
    have := key _ (mem_lagSetA_y M M₁ H H' hc)
    rwa [lagL_dar_add_left M.co, lagL_dar_add_left M.co, GlobalTheory.LagIsotropic.symp_vecMulVec_x_eq_zero B W W₁ H' i₀ i₁ X.J hH',
      (GlobalTheory.ArchSch.OrthPlane.symp_tens_orth B W W₁ H' r' s' i₀ i₁ X.J hB hW hH' c Z).1,
      GlobalTheory.ArchSch.symp_dual_iso B W W₁ H' r' s' i₀ i₁ X.J hW hH', zero_add, zero_add] at this
  subst hb0
  rw [zero_vecMulVec', add_zero] at key hw1 hw2
  have e1 : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)

  have key₁ : ∀ z' : Matrix (Fin n) (Fin d₁) (AE F E),
      (arch F (M.co.e (z' * (incM F H'.ι)ᵀ)).1, arch F (M.co.e (z' * (incM F H'.ι)ᵀ)).2) ∈ lagSetA M M₁ H H' →
      Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
        (evI F (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W₁.J) Z z')) = 0 := by
    intro z' hl
    have := key (incM F (1 : Matrix (Fin n) (Fin n) E) * z' * (incM F H'.ι)ᵀ) (by rwa [e1, Matrix.one_mul])
    rwa [lagL_dar_add_left M.co, (GlobalTheory.ArchSch.OrthPlane.symp_tens_orth B W W₁ H' r' s' i₀ i₁ X.J hB hW hH' a z').2.1,
      GlobalTheory.SympRestrict.symp_embed_eq B W W₁ H' i₀ i₁ X.J hH', zero_add] at this
  obtain ⟨α, β, C, hα, hβ, hC, rfl⟩ := decompose_left B hX hH Z hZ
  have hβ0 : β = 0 := by
    refine eq_zero_of_trace_gram σ W₁.J (GlobalTheory.LeviAdapted.isUnit_det_low hinv hW hH').ne_zero β hβ fun c hc => ?_
    have h := key₁ (Matrix.vecMulVec (incV F H.x) c) (by rw [vmv_mul_transpose]; exact mem_lagSetA_c M M₁ H H' hc)
    rwa [symplectic_form_adapted_coordinates hinv B W₁.J hX hH, evI_neg, map_neg, neg_eq_zero] at h
  subst hβ0
  rw [vecMulVec_zero', add_zero] at key₁ hw1 hw2
  have hflipX : ∀ u v, form σ X.J u v = 0 → form σ X.J v u = 0 := fun u v h => by
    rw [form_herm hinv hX.herm, h, map_zero]
  have h0 : ∀ {p q : Type}, incM F (0 : Matrix p q E) = 0 := fun {p q} => by ext; simp [incM]
  have hXI : (incM F (Matrix.replicateCol Unit H.x))ᵀ * incM F X.J * (incM F H.ι).map (cA σ) = 0 := by
    rw [incM_gram, gram_xι hH hflipX, h0]
  have hGX : (incM F H.ι)ᵀ * incM F X.J * (incM F H.ι).map (cA σ) = incM F X₁.J := by
    rw [incM_gram, hH.gram]
  have hG1 : (1 : Matrix (Fin d₁) (Fin d₁) (AE F E))ᵀ * incM F W₁.J * (1 : Matrix (Fin d₁) (Fin d₁) (AE F E)).map (cA σ) =
      incM F W₁.J := by
    rw [Matrix.transpose_one, Matrix.one_mul, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
  have hA : Matrix.vecMulVec (incV F H.x) α =
      incM F (Matrix.replicateCol Unit H.x) * Matrix.replicateRow Unit α * (1 : Matrix (Fin d₁) (Fin d₁) (AE F E))ᵀ := by
    rw [Matrix.transpose_one, Matrix.mul_one, Matrix.vecMulVec_eq Unit]
    congr 1
  have hι : ∀ z : Matrix (Fin n₁) (Fin d₁) (AE F E),
      incM F H.ι * z = incM F H.ι * z * (1 : Matrix (Fin d₁) (Fin d₁) (AE F E))ᵀ := fun z => by
    rw [Matrix.transpose_one, Matrix.mul_one]
  have hpair : ∀ z' : Matrix (Fin n₁) (Fin d₁) (AE F E),
      symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W₁.J) (Matrix.vecMulVec (incV F H.x) α + incM F H.ι * C)
        (incM F H.ι * z') = symp (R := AF F) (cA σ) (-1) (incM F X₁.J) (incM F W₁.J) C z' := by
    intro z'
    have e₁ := symp_change_zero_left (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W₁.J) _ (1 : Matrix (Fin d₁) (Fin d₁) (AE F E)) _
      (1 : Matrix (Fin d₁) (Fin d₁) (AE F E)) (Matrix.replicateRow Unit α) z' hXI
    have e₂ := symp_change_eq (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W₁.J) _ _ _ _ C z' hGX hG1
    rw [← hA, ← hι] at e₁
    rw [← hι, ← hι] at e₂
    rw [← e₂]
    unfold symp at e₁ ⊢
    rw [TensForm.hTens_add_left, mul_add, map_add, e₁, zero_add]
  have hp : arch F (M₁.co.e C).1 = 0 := by
    funext i
    refine GlobalTheory.mixedSpace_traceForm_nondegenerate F _ fun η => ?_
    obtain ⟨z', hz'A, hz'1, hz'2⟩ := GlobalTheory.ArchSch.exists_darboux_lift M₁.co 0 (Pi.single i η)
    have := key₁ _ (mem_lagrangian_set_archimedean M M₁ H H' hz'A hz'1)
    rw [hpair, hω₁, hz'1, hz'2] at this
    simpa [mixedTracePairing_apply, Pi.single_apply] using this
  rw [e1, Matrix.one_mul, Matrix.add_mul, vmv_mul_transpose, ← add_assoc] at hw1 hw2
  exact ⟨a, α, C, ha, hα, hC, hp, Prod.ext hw1.symm hw2.symm⟩

end GlobalTheory.ArchSchA
