import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StFrameJacobianGeneric
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StConormalGenerationGeneric
import GroundTheory.HeightsAndTheta.Heights.Intersections.JacMinorC
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

open MvPolynomial
open scoped Matrix

/- English proof (translation)
Introduce `h`. Take `⟨v, hv, hvM⟩` from `Matrix.exists_vecMul_eq_zero_iff.mpr h`. Apply `hv` to reduce the goal to its premises. Establish `hsum : ∑ j, v j • b j = 0`. Use extensionality with `l`.

Use `congrFun hvM l` as an intermediate fact. Simplify `this` using `[Matrix.vecMul, dotProduct, mul_comm]`. Establish `hli` using `Fintype.linearIndependent_iff.mp b.toBasis.linearIndependent v (by simpa using hsum)`. Use function extensionality and compare the values at `j`. Conclude with `hli j`.
-/
theorem frame_matrix_det_ne_zero {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) :
    (Matrix.of fun j l : Fin n => b j l).det ≠ 0 := by
  intro h
  obtain ⟨v, hv, hvM⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h
  apply hv
  have hsum : ∑ j, v j • b j = 0 := by
    ext l
    have := congrFun hvM l
    simpa [Matrix.vecMul, dotProduct, mul_comm] using this
  have hli := Fintype.linearIndependent_iff.mp b.toBasis.linearIndependent v (by simpa using hsum)
  funext j
  exact hli j

/- English proof (translation)
Introduce `n d J hJ hd b`. Use `hJ` as an intermediate fact. Use `set K := FractionRing (MvPolynomial (Fin n) ℂ ⧸ J)`. Set `π : MvPolynomial (Fin n) ℂ →+* K` to `(algebraMap (MvPolynomial (Fin n) ℂ ⧸ J) K).comp (Ideal.Quotient.mk J)`. Establish `hπ : ∀ f, π f = 0 ↔ f ∈ J`.

Introduce `f`. Simplify using `only [π, RingHom.comp_apply]`. Rewrite using `[IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]`. Establish `hdn : d ≤ n`. Establish `h1` using `ringKrullDim_quotient_le J`.

Rewrite `h1` using `[hd, MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add, Nat.card_eq_fintype_card, Fintype.card_fin]`. Conclude with `h1` after adjusting the coercions. Take `⟨t, G, hG⟩` from `Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian J)`. Use `set r := Fintype.card (Fin n) - d with hr`. Take `⟨a, c, hac⟩` from `IndefiniteRowSideFullHecke.Inter.exists_jacobian_minor_not_mem_charZero J G hG d hd`.

Establish `hrn : r = n - d` using `by rw [hr, Fintype.card_fin]`. Establish `hGJ : ∀ i, G i ∈ J` using `fun i => hG ▸ Ideal.subset_span ⟨i, rfl⟩`. Set `V : Matrix (Fin r) (Fin n) K` to `Matrix.of fun i l => π (pderiv l (G (a i)))`. Set `N : Matrix (Fin n) (Fin n) K` to `Matrix.of fun l j => π (C (b j l))`. Set `W : Matrix (Fin r) (Fin n) K` to `Matrix.of fun i j => π (frameDeriv b j (G (a i)))`.

Establish `hW : W = V * N`. Use extensionality with `i j`. Simplify using `[W, V, N, frameDeriv, Matrix.mul_apply, map_sum, mul_comm]`. Establish `hVc : (V.submatrix id c).det ≠ 0`. Establish `: V.submatrix id c = π.mapMatrix (Matrix.of fun i j => pderiv (c j) (G (a i)))`.

Use extensionality with `i j`. Both sides reduce to the same expression. Rewrite using `[this, ← RingHom.map_det]`. Conclude with `fun h => hac ((hπ _).mp h)`. Establish `hN : N.det ≠ 0`.

Establish `: N = π.mapMatrix ((C : ℂ →+* MvPolynomial (Fin n) ℂ).mapMatrix (Matrix.of fun j l : Fin n => b j l)ᵀ)`. Use extensionality with `l j`. Both sides reduce to the same expression. Rewrite using `[this, ← RingHom.map_det, ← RingHom.map_det, Matrix.det_transpose]`. Introduce `h`.

Rewrite `h` using `[hπ]`. Establish `hu : IsUnit (C (Matrix.of fun j l : Fin n => b j l).det : MvPolynomial (Fin n) ℂ)` using `(isUnit_iff_ne_zero.mpr (frame_matrix_det_ne_zero b)).map C`. Conclude with `hJ.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)`. Establish `hVinj : ∀ x : Fin r → K, x ᵥ* V = 0 → x = 0`. Introduce `x hx`.

Apply `Matrix.eq_zero_of_vecMul_eq_zero hVc` to reduce the goal to its premises. Use extensionality with `j`. Simplify `congrFun hx (c j)` using `[Matrix.vecMul, dotProduct]`. Establish `hWinj : ∀ x : Fin r → K, Wᵀ *ᵥ x = 0 → x = 0`. Introduce `x hx`.

Rewrite `hx` using `[Matrix.mulVec_transpose, hW, ← Matrix.vecMul_vecMul]`. Conclude with `hVinj x (Matrix.eq_zero_of_vecMul_eq_zero hN hx)`. Take `⟨col, hcol⟩` from `ReciprocityTheory.AnForm.R.gs_exists_rows_det_ne_zero Wᵀ hWinj`. Establish `hcol' : (W.submatrix id col).det ≠ 0`. Rewrite using `[← Matrix.det_transpose, Matrix.transpose_submatrix]` and apply the resulting hypothesis.

Establish `hinj : Function.Injective col`. Introduce `i i' h`. Assume the negation of the conclusion as `hne`. Apply `hcol` to reduce the goal to its premises. Apply `Matrix.det_zero_of_row_eq hne` to reduce the goal to its premises.

Use function extensionality and compare the values at `k`. Simplify using `[h]`. Set `I₀ : Finset (Fin n)` to `(Finset.univ.image col)ᶜ`. Establish `hmem : ∀ j, j ∈ Set.range col ↔ j ∉ I₀`. Introduce `j`.

Simplify using `[I₀]`. Set `e : Fin r ≃ {j // j ∉ I₀}` to `(Equiv.ofInjective col hinj).trans (Equiv.subtypeEquivRight hmem)`. Establish `he : ∀ i, (e i : Fin n) = col i` using `fun i => rfl`. Set `f : {j // j ∉ I₀} → MvPolynomial (Fin n) ℂ` to `fun k => G (a (e.symm k))`. Establish `hli : LinearIndependent K (fun i => genericGradient J (G (a i)))`.

Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `x hx`. Establish `: x ᵥ* V = 0`. Rewrite using `[Matrix.vecMul_eq_sum]`. Conclude with `hx`.

Simplify using `using congrFun (hVinj x this)`. Establish `hspan : Submodule.span K (Set.range (genericGradient J ∘ f)) = Submodule.span K (genericGradient J '' (J : Set _))`. Establish `hrange : Set.range (genericGradient J ∘ f) = Set.range (fun i => genericGradient J (G (a i)))`. Use extensionality with `v`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨k, rfl⟩`. Conclude with `⟨e.symm k, rfl⟩`. Introduce and unpack `⟨i, rfl⟩`. Conclude with `⟨e i, by simp [f]⟩`. Rewrite using `[hrange]`.

Apply `Submodule.eq_of_le_of_finrank_le` to reduce the goal to its premises. Apply `Submodule.span_mono` to reduce the goal to its premises. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `⟨G (a i), hGJ _, rfl⟩`. Rewrite using `[finrank_span_eq_card hli, Fintype.card_fin]`.

Conclude with `(hR n d J hd).trans (by simp)`. Take `⟨s, hsJ, hs⟩` from `hC n J {j // j ∉ I₀} f (fun k => hGJ _) hspan`. Use `⟨I₀, f, s, ?_, fun k => hGJ _, hsJ, ?_, hs⟩` and prove the remaining obligations. Rewrite using `[Finset.card_compl, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin, Fintype.card_fin]`. Use linear arithmetic over natural numbers and integers.

Introduce `hdet`. Rewrite `hdet` using `[← hπ, frameJacobianDet, RingHom.map_det, ← Matrix.det_submatrix_equiv_self e]`. Apply `hcol'` to reduce the goal to its premises. Use `hdet using 2` and compare the differences between its conclusion and the goal. Use extensionality with `i i'`.

Simplify using `[f, W, he]`.
-/
theorem FrameJacobianGeneric.proof (hR : JacobianRankGeneric.Statement)
    (hC : ConormalGenerationGeneric.Statement) : FrameJacobianGeneric.Statement := by
  classical
  intro n d J hJ hd b
  have := hJ
  set K := FractionRing (MvPolynomial (Fin n) ℂ ⧸ J)
  let π : MvPolynomial (Fin n) ℂ →+* K :=
    (algebraMap (MvPolynomial (Fin n) ℂ ⧸ J) K).comp (Ideal.Quotient.mk J)
  have hπ : ∀ f, π f = 0 ↔ f ∈ J := by
    intro f
    simp only [π, RingHom.comp_apply]
    rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
  have hdn : d ≤ n := by
    have h1 := ringKrullDim_quotient_le J
    rw [hd, MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,
      Nat.card_eq_fintype_card, Fintype.card_fin] at h1
    exact_mod_cast h1
  obtain ⟨t, G, hG⟩ := Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian J)
  set r := Fintype.card (Fin n) - d with hr
  obtain ⟨a, c, hac⟩ := IndefiniteRowSideFullHecke.Inter.exists_jacobian_minor_not_mem_charZero J G hG d hd
  have hrn : r = n - d := by rw [hr, Fintype.card_fin]
  have hGJ : ∀ i, G i ∈ J := fun i => hG ▸ Ideal.subset_span ⟨i, rfl⟩
  let V : Matrix (Fin r) (Fin n) K := Matrix.of fun i l => π (pderiv l (G (a i)))
  let N : Matrix (Fin n) (Fin n) K := Matrix.of fun l j => π (C (b j l))
  let W : Matrix (Fin r) (Fin n) K := Matrix.of fun i j => π (frameDeriv b j (G (a i)))
  have hW : W = V * N := by
    ext i j
    simp [W, V, N, frameDeriv, Matrix.mul_apply, map_sum, mul_comm]
  have hVc : (V.submatrix id c).det ≠ 0 := by
    have : V.submatrix id c = π.mapMatrix (Matrix.of fun i j => pderiv (c j) (G (a i))) := by
      ext i j
      rfl
    rw [this, ← RingHom.map_det]
    exact fun h => hac ((hπ _).mp h)
  have hN : N.det ≠ 0 := by
    have : N = π.mapMatrix ((C : ℂ →+* MvPolynomial (Fin n) ℂ).mapMatrix
        (Matrix.of fun j l : Fin n => b j l)ᵀ) := by
      ext l j
      rfl
    rw [this, ← RingHom.map_det, ← RingHom.map_det, Matrix.det_transpose]
    intro h
    rw [hπ] at h
    have hu : IsUnit (C (Matrix.of fun j l : Fin n => b j l).det : MvPolynomial (Fin n) ℂ) :=
      (isUnit_iff_ne_zero.mpr (frame_matrix_det_ne_zero b)).map C
    exact hJ.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)
  have hVinj : ∀ x : Fin r → K, x ᵥ* V = 0 → x = 0 := by
    intro x hx
    apply Matrix.eq_zero_of_vecMul_eq_zero hVc
    ext j
    simpa [Matrix.vecMul, dotProduct] using congrFun hx (c j)
  have hWinj : ∀ x : Fin r → K, Wᵀ *ᵥ x = 0 → x = 0 := by
    intro x hx
    rw [Matrix.mulVec_transpose, hW, ← Matrix.vecMul_vecMul] at hx
    exact hVinj x (Matrix.eq_zero_of_vecMul_eq_zero hN hx)
  obtain ⟨col, hcol⟩ := ReciprocityTheory.AnForm.R.gs_exists_rows_det_ne_zero Wᵀ hWinj
  have hcol' : (W.submatrix id col).det ≠ 0 := by
    rwa [← Matrix.det_transpose, Matrix.transpose_submatrix]
  have hinj : Function.Injective col := by
    intro i i' h
    by_contra hne
    apply hcol
    apply Matrix.det_zero_of_row_eq hne
    funext k
    simp [h]
  let I₀ : Finset (Fin n) := (Finset.univ.image col)ᶜ
  have hmem : ∀ j, j ∈ Set.range col ↔ j ∉ I₀ := by
    intro j
    simp [I₀]
  let e : Fin r ≃ {j // j ∉ I₀} :=
    (Equiv.ofInjective col hinj).trans (Equiv.subtypeEquivRight hmem)
  have he : ∀ i, (e i : Fin n) = col i := fun i => rfl
  let f : {j // j ∉ I₀} → MvPolynomial (Fin n) ℂ := fun k => G (a (e.symm k))
  have hli : LinearIndependent K (fun i => genericGradient J (G (a i))) := by
    rw [Fintype.linearIndependent_iff]
    intro x hx
    have : x ᵥ* V = 0 := by
      rw [Matrix.vecMul_eq_sum]
      exact hx
    simpa using congrFun (hVinj x this)
  have hspan : Submodule.span K (Set.range (genericGradient J ∘ f)) =
      Submodule.span K (genericGradient J '' (J : Set _)) := by
    have hrange : Set.range (genericGradient J ∘ f) =
        Set.range (fun i => genericGradient J (G (a i))) := by
      ext v
      constructor
      · rintro ⟨k, rfl⟩
        exact ⟨e.symm k, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨e i, by simp [f]⟩
    rw [hrange]
    apply Submodule.eq_of_le_of_finrank_le
    · apply Submodule.span_mono
      rintro _ ⟨i, rfl⟩
      exact ⟨G (a i), hGJ _, rfl⟩
    · rw [finrank_span_eq_card hli, Fintype.card_fin]
      exact (hR n d J hd).trans (by simp)
  obtain ⟨s, hsJ, hs⟩ := hC n J {j // j ∉ I₀} f (fun k => hGJ _) hspan
  refine ⟨I₀, f, s, ?_, fun k => hGJ _, hsJ, ?_, hs⟩
  · rw [Finset.card_compl, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin,
      Fintype.card_fin]
    omega
  · intro hdet
    rw [← hπ, frameJacobianDet, RingHom.map_det, ← Matrix.det_submatrix_equiv_self e] at hdet
    apply hcol'
    convert hdet using 2
    ext i i'
    simp [f, W, he]

end

end GroundTheory.Heights₂.Heights
