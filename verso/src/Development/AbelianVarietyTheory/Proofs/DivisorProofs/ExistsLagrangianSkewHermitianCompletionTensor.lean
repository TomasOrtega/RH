import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweDualityGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ComplementaryThetaInert
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.SkewLagr

open Matrix

/- English proof (translation)
Establish `h : fromBlocks (0 : Matrix (Fin m) (Fin m) L) (1 : Matrix (Fin m) (Fin m) L) 1 0 = (fromBlocks 1 1 0 1 * fromBlocks 1 0 (-1) 1 * fromBlocks 1 1 0 1 * fromBlocks (-1) 0 0 1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L)`. Simplify using `[fromBlocks_multiply]`. Rewrite using `[h, det_mul, det_mul, det_mul, det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂, det_fromBlocks_zero₂₁]`. Simplify using `[det_neg]`.
-/
theorem det_hyp {L : Type*} [CommRing L] (m : ℕ) :
    (fromBlocks (0 : Matrix (Fin m) (Fin m) L) (1 : Matrix (Fin m) (Fin m) L) 1 0).det = (-1) ^ m := by
  have h : fromBlocks (0 : Matrix (Fin m) (Fin m) L) (1 : Matrix (Fin m) (Fin m) L) 1 0 =
      (fromBlocks 1 1 0 1 * fromBlocks 1 0 (-1) 1 * fromBlocks 1 1 0 1 * fromBlocks (-1) 0 0 1 :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) := by
    simp [fromBlocks_multiply]
  rw [h, det_mul, det_mul, det_mul, det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂, det_fromBlocks_zero₂₁]
  simp [det_neg]

/- English proof (translation)
Use `haveI : CharZero (v.adicCompletion F) := charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective`. Take `⟨x, hx⟩` from `hx`. Set `σ : L ≃ₐ[v.adicCompletion F] L` to `AlgEquiv.ofAlgHom c c (AlgHom.ext hc) (AlgHom.ext hc)`. Establish `hσc : ∀ y, σ y = c y` using `fun _ => rfl`. Establish `h2 : (2 : L) ≠ 0`.

Rewrite using `[← map_ofNat (algebraMap (v.adicCompletion F) L) 2]`. Conclude with `(map_ne_zero _).2 two_ne_zero`. Establish `hσ : σ ≠ 1`. Introduce `h`. Establish `h1 : c δ = δ` using `by rw [← hσc, h]; rfl`.

Apply `hδ` to reduce the goal to its premises. Establish `: (2 : L) * δ = 0` using `by linear_combination hcδ - h1`. Conclude with `(mul_eq_zero.1 this).resolve_left h2`. Set `e : Fin m ⊕ Fin m ≃ Fin (m + m)` to `finSumFinEquiv`. Set `Hyp : Matrix (Fin (m + m)) (Fin (m + m)) L` to `(fromBlocks 0 1 1 0 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L).submatrix e.symm e.symm`.

Set `H : Matrix (Fin (m + m)) (Fin (m + m)) L` to `δ • J`. Establish `hH : ∀ a b, σ (H a b) = H b a`. Introduce `a b`. Simplify using `only [H, Matrix.smul_apply, smul_eq_mul, hσc, map_mul, hcδ, hJ]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hHyp : ∀ a b, σ (Hyp a b) = Hyp b a`. Introduce `a b`. Simplify using `only [Hyp, submatrix_apply]`. Apply the tactic sequence `rcases e.symm a with i | i <;> rcases e.symm b with j | j <;>`. Apply the tactic sequence `by_cases hij : i = j <;> simp [fromBlocks, one_apply, hij, eq_comm]`.

Establish `hdH : H.det = δ ^ (m + m) * J.det` using `by simp [H, det_smul]`. Establish `hdHyp : Hyp.det = (-1) ^ m` using `by simp [Hyp, det_submatrix_equiv_self, det_hyp]`. Establish `hs : ((-1 : L) ^ m) ^ 2 = 1` using `by rw [← pow_mul, mul_comm, pow_mul]; simp`. Take `⟨P, hP, hPeq⟩` from `(GlobalTheory.HermLocal.congr_iff_adicCompletion F v L σ hσ hH hHyp (by rw [hdH]; exact mul_ne_zero (pow_ne_zero _ hδ) hd) (by rw [hdHyp]; simp)).2 ⟨δ ^ m * x, by`. Rewrite using `[hdH, hdHyp, div_eq_iff (by simp), hx, hσc, map_mul, map_pow, hcδ, neg_pow]`.

Take the linear combination `(-(δ ^ (m + m) * x * c x)) * hs⟩`. Establish `hQ : ∀ a b, δ * (Pᵀ * J * P.map c) a b = Hyp a b`. Introduce `a b`. Rewrite using `[hPeq]`. Simplify using `only [H, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]`.

Both sides reduce to the same expression. Establish `hiso : ∀ (f : Fin m → Fin m ⊕ Fin m), (∀ a b, Hyp (e (f a)) (e (f b)) = 0) → (P.submatrix id (fun j => e (f j)))ᵀ * J * (P.submatrix id (fun j => e (f j))).map c = 0`. Introduce `f hf`. Use extensionality with `a b`. Establish `h1 : ((P.submatrix id (fun j => e (f j)))ᵀ * J * (P.submatrix id (fun j => e (f j))).map c) a b = (Pᵀ * J * P.map c) (e (f a)) (e (f b))` using `rfl`.

Rewrite using `[h1, Matrix.zero_apply]`. Establish `h3` using `hQ (e (f a)) (e (f b))`. Rewrite `h3` using `[hf]`. Conclude with `(mul_eq_zero.1 h3).resolve_left hδ`. Establish `hPu : IsUnit P.det` using `isUnit_iff_ne_zero.2 hP`.

Establish `hcols : fromCols (P.submatrix id (fun j => e (Sum.inl j))) (P.submatrix id (fun j => e (Sum.inr j))) = P.submatrix id e`. Apply the tactic sequence `ext i (j | j) <;> rfl`. Use `⟨P.submatrix id (fun j => e (Sum.inl j)), hiso Sum.inl (fun a b => by simp [Hyp]), P.submatrix id (fun j => e (Sum.inr j)), P⁻¹.submatrix e id, hiso Sum.inr (fun a b => by simp [Hyp]), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hcols, submatrix_mul_equiv, mul_nonsing_inv P hPu, submatrix_id_id]`. Rewrite using `[hcols, show (P⁻¹.submatrix e id) = P⁻¹.submatrix e (Equiv.refl _) from rfl, show P.submatrix id e = P.submatrix (Equiv.refl _) e from rfl, submatrix_mul_equiv, nonsing_inv_mul P hPu, submatrix_one_equiv]`.
-/
theorem exists_isLagr_of_local (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    {L : Type} [Field L] [Algebra (v.adicCompletion F) L]
    [Algebra.IsQuadraticExtension (v.adicCompletion F) L]
    (c : L →ₐ[v.adicCompletion F] L) (hc : ∀ x, c (c x) = x) {δ : L} (hδ : δ ≠ 0) (hcδ : c δ = -δ)
    (m : ℕ) (J : Matrix (Fin (m + m)) (Fin (m + m)) L) (hJ : ∀ i j, c (J j i) = -J i j)
    (hd : J.det ≠ 0) (hx : ∃ x, J.det = x * c x) :
    ∃ Cy : Matrix (Fin (m + m)) (Fin m) L, GlobalTheory.WeilM.IsLagr c J Cy := by
  classical
  haveI : CharZero (v.adicCompletion F) :=
    charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
  obtain ⟨x, hx⟩ := hx
  let σ : L ≃ₐ[v.adicCompletion F] L := AlgEquiv.ofAlgHom c c (AlgHom.ext hc) (AlgHom.ext hc)
  have hσc : ∀ y, σ y = c y := fun _ => rfl
  have h2 : (2 : L) ≠ 0 := by
    rw [← map_ofNat (algebraMap (v.adicCompletion F) L) 2]
    exact (map_ne_zero _).2 two_ne_zero
  have hσ : σ ≠ 1 := by
    intro h
    have h1 : c δ = δ := by rw [← hσc, h]; rfl
    apply hδ
    have : (2 : L) * δ = 0 := by linear_combination hcδ - h1
    exact (mul_eq_zero.1 this).resolve_left h2
  let e : Fin m ⊕ Fin m ≃ Fin (m + m) := finSumFinEquiv
  let Hyp : Matrix (Fin (m + m)) (Fin (m + m)) L :=
    (fromBlocks 0 1 1 0 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L).submatrix e.symm e.symm
  let H : Matrix (Fin (m + m)) (Fin (m + m)) L := δ • J
  have hH : ∀ a b, σ (H a b) = H b a := by
    intro a b
    simp only [H, Matrix.smul_apply, smul_eq_mul, hσc, map_mul, hcδ, hJ]
    ring
  have hHyp : ∀ a b, σ (Hyp a b) = Hyp b a := by
    intro a b
    simp only [Hyp, submatrix_apply]
    rcases e.symm a with i | i <;> rcases e.symm b with j | j <;>
      by_cases hij : i = j <;> simp [fromBlocks, one_apply, hij, eq_comm]
  have hdH : H.det = δ ^ (m + m) * J.det := by simp [H, det_smul]
  have hdHyp : Hyp.det = (-1) ^ m := by simp [Hyp, det_submatrix_equiv_self, det_hyp]
  have hs : ((-1 : L) ^ m) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  obtain ⟨P, hP, hPeq⟩ := (GlobalTheory.HermLocal.congr_iff_adicCompletion F v L σ hσ hH hHyp
    (by rw [hdH]; exact mul_ne_zero (pow_ne_zero _ hδ) hd) (by rw [hdHyp]; simp)).2 ⟨δ ^ m * x, by
      rw [hdH, hdHyp, div_eq_iff (by simp), hx, hσc, map_mul, map_pow, hcδ, neg_pow]
      linear_combination (-(δ ^ (m + m) * x * c x)) * hs⟩
  have hQ : ∀ a b, δ * (Pᵀ * J * P.map c) a b = Hyp a b := by
    intro a b
    rw [hPeq]
    simp only [H, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
    rfl
  have hiso : ∀ (f : Fin m → Fin m ⊕ Fin m), (∀ a b, Hyp (e (f a)) (e (f b)) = 0) →
      (P.submatrix id (fun j => e (f j)))ᵀ * J * (P.submatrix id (fun j => e (f j))).map c = 0 := by
    intro f hf
    ext a b
    have h1 : ((P.submatrix id (fun j => e (f j)))ᵀ * J * (P.submatrix id (fun j => e (f j))).map c) a b =
        (Pᵀ * J * P.map c) (e (f a)) (e (f b)) := rfl
    rw [h1, Matrix.zero_apply]
    have h3 := hQ (e (f a)) (e (f b))
    rw [hf] at h3
    exact (mul_eq_zero.1 h3).resolve_left hδ
  have hPu : IsUnit P.det := isUnit_iff_ne_zero.2 hP
  have hcols : fromCols (P.submatrix id (fun j => e (Sum.inl j))) (P.submatrix id (fun j => e (Sum.inr j))) =
      P.submatrix id e := by
    ext i (j | j) <;> rfl
  refine ⟨P.submatrix id (fun j => e (Sum.inl j)), hiso Sum.inl (fun a b => by simp [Hyp]),
    P.submatrix id (fun j => e (Sum.inr j)), P⁻¹.submatrix e id, hiso Sum.inr (fun a b => by simp [Hyp]), ?_, ?_⟩
  · rw [hcols, submatrix_mul_equiv, mul_nonsing_inv P hPu, submatrix_id_id]
  · rw [hcols, show (P⁻¹.submatrix e id) = P⁻¹.submatrix e (Equiv.refl _) from rfl,
      show P.submatrix id e = P.submatrix (Equiv.refl _) e from rfl, submatrix_mul_equiv,
      nonsing_inv_mul P hPu, submatrix_one_equiv]

end GlobalTheory.SkewLagr

namespace GlobalTheory.SkewLagr

open Matrix

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hcm v hF n J hn hJ hd hx`. Take `⟨m, rfl⟩` from `hn`. Rewrite using `[show (m + m) / 2 = m by omega]`. Use `letI : Field (Fv F v ⊗[F] E) := hF.toField`. Use `haveI : Algebra.IsQuadraticExtension (Fv F v) (Fv F v ⊗[F] E) := { finrank_eq_two' := by rw [Module.finrank_baseChange]; exact hcm.2.2.1 }`.

Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Establish `hσσ : ∀ y, σ (σ y) = y` using `fun y => τ.injective (by rw [hcm.2.2.2, hcm.2.2.2, star_star])`. Choose the witnesses or unpack the hypotheses as in `⟨t, ht⟩ : ∃ t, σ t ≠ t := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Establish `hw` using `hcm.2.1.isComplex (NumberField.InfinitePlace.mk τ)`. Rewrite `hw` using `[NumberField.InfinitePlace.isComplex_mk_iff, NumberField.ComplexEmbedding.isReal_iff]`. Apply `hw` to reduce the goal to its premises. Use extensionality with `y`. Establish `hy` using `hcm.2.2.2 τ y`.

Rewrite `hy` using `[h]`. Simplify using `only [NumberField.ComplexEmbedding.conjugate_coe_eq]`. Rewrite using `[starRingEnd_apply]`. Conclude with `hy.symm`. Use `set c := Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ with hcdef`.

Establish `hct : ∀ y : E, c ((1 : Fv F v) ⊗ₜ[F] y) = (1 : Fv F v) ⊗ₜ[F] σ y` using `fun y => by`. Simplify using `[c, Algebra.TensorProduct.map_tmul]`. Establish `hc : ∀ z, c (c z) = z`. Introduce `z`. Proceed by induction on `z using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul a b => simp [c, Algebra.TensorProduct.map_tmul, hσσ]`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Establish `hinj : Function.Injective (inclR (Fv F v) : E →+* Fv F v ⊗[F] E)` using `RingHom.injective _`. Establish `hincl : ∀ y : E, inclR (Fv F v) y = (1 : Fv F v) ⊗ₜ[F] y` using `fun _ => rfl`.

Establish `hδ : (1 : Fv F v) ⊗ₜ[F] (t - σ t) ≠ 0`. Rewrite using `[← hincl]`. Conclude with `(map_ne_zero_iff _ hinj).2 (sub_ne_zero.2 (Ne.symm ht))`. Establish `hcδ : c ((1 : Fv F v) ⊗ₜ[F] (t - σ t)) = -((1 : Fv F v) ⊗ₜ[F] (t - σ t))`. Rewrite using `[hct, map_sub, hσσ, ← TensorProduct.tmul_neg, neg_sub]`.

Establish `hdet : (JR (Fv F v) J).det = (1 : Fv F v) ⊗ₜ[F] J.det`. Rewrite using `[← hincl, RingHom.map_det]`. Both sides reduce to the same expression. Use `exists_isLagr_of_local F v c hc hδ hcδ m (JR (Fv F v) J) (fun i j => ?_) ?_ ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `c (inclR (Fv F v) (J j i)) = -inclR (Fv F v) (J i j)`.

Rewrite using `[hincl, hincl, hct, hJ, TensorProduct.tmul_neg]`. Rewrite using `[hdet, ← hincl]`. Conclude with `(map_ne_zero_iff _ hinj).2 hd`. Rewrite using `[hdet]`. Conclude with `hx`.
-/
theorem exists_isLagr_tensor : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (v : Pl F), IsField (Fv F v ⊗[F] E) →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), Even n → (∀ i j, σ (J j i) = -J i j) → J.det ≠ 0 →
    (∃ x : Fv F v ⊗[F] E, (1 : Fv F v) ⊗ₜ[F] J.det = x * Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ x) →
    ∃ Cy : Matrix (Fin n) (Fin (n / 2)) (Fv F v ⊗[F] E),
      IsLagr (Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ) (JR (Fv F v) J) Cy := by
  intro F E _ _ _ _ _ σ hcm v hF n J hn hJ hd hx
  obtain ⟨m, rfl⟩ := hn
  rw [show (m + m) / 2 = m by omega]
  letI : Field (Fv F v ⊗[F] E) := hF.toField
  haveI : Algebra.IsQuadraticExtension (Fv F v) (Fv F v ⊗[F] E) :=
    { finrank_eq_two' := by rw [Module.finrank_baseChange]; exact hcm.2.2.1 }
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hσσ : ∀ y, σ (σ y) = y := fun y => τ.injective (by rw [hcm.2.2.2, hcm.2.2.2, star_star])
  obtain ⟨t, ht⟩ : ∃ t, σ t ≠ t := by
    by_contra h
    push_neg at h
    have hw := hcm.2.1.isComplex (NumberField.InfinitePlace.mk τ)
    rw [NumberField.InfinitePlace.isComplex_mk_iff, NumberField.ComplexEmbedding.isReal_iff] at hw
    apply hw
    ext y
    have hy := hcm.2.2.2 τ y
    rw [h] at hy
    simp only [NumberField.ComplexEmbedding.conjugate_coe_eq]
    rw [starRingEnd_apply]
    exact hy.symm
  set c := Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ with hcdef
  have hct : ∀ y : E, c ((1 : Fv F v) ⊗ₜ[F] y) = (1 : Fv F v) ⊗ₜ[F] σ y := fun y => by
    simp [c, Algebra.TensorProduct.map_tmul]
  have hc : ∀ z, c (c z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [c, Algebra.TensorProduct.map_tmul, hσσ]
    | add a b ha hb => simp only [map_add, ha, hb]
  have hinj : Function.Injective (inclR (Fv F v) : E →+* Fv F v ⊗[F] E) := RingHom.injective _
  have hincl : ∀ y : E, inclR (Fv F v) y = (1 : Fv F v) ⊗ₜ[F] y := fun _ => rfl
  have hδ : (1 : Fv F v) ⊗ₜ[F] (t - σ t) ≠ 0 := by
    rw [← hincl]
    exact (map_ne_zero_iff _ hinj).2 (sub_ne_zero.2 (Ne.symm ht))
  have hcδ : c ((1 : Fv F v) ⊗ₜ[F] (t - σ t)) = -((1 : Fv F v) ⊗ₜ[F] (t - σ t)) := by
    rw [hct, map_sub, hσσ, ← TensorProduct.tmul_neg, neg_sub]
  have hdet : (JR (Fv F v) J).det = (1 : Fv F v) ⊗ₜ[F] J.det := by
    rw [← hincl, RingHom.map_det]
    rfl
  refine exists_isLagr_of_local F v c hc hδ hcδ m (JR (Fv F v) J) (fun i j => ?_) ?_ ?_
  · change c (inclR (Fv F v) (J j i)) = -inclR (Fv F v) (J i j)
    rw [hincl, hincl, hct, hJ, TensorProduct.tmul_neg]
  · rw [hdet, ← hincl]
    exact (map_ne_zero_iff _ hinj).2 hd
  · rw [hdet]
    exact hx

end GlobalTheory.SkewLagr
