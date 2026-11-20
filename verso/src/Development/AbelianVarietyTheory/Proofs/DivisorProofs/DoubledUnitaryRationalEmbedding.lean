import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegFamOfContinuousAt
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling GlobalTheory.ThK.DblKer
noncomputable section

namespace GlobalTheory.DoublingRat

/- English proof (translation)
Establish `h : (fun i => σ ((A *ᵥ y) i)) = A.map σ *ᵥ fun i => σ (y i)`. Use function extensionality and compare the values at `i`. Simplify using `[Matrix.mulVec, dotProduct, map_sum]`. Unfold `form`. Rewrite using `[h, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x, Matrix.vecMul_transpose]`.
-/
theorem form_mulVec {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J A : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    form σ J (A *ᵥ x) (A *ᵥ y) = form σ (Aᵀ * J * A.map σ) x y := by
  have h : (fun i => σ ((A *ᵥ y) i)) = A.map σ *ᵥ fun i => σ (y i) := by
    funext i
    simp [Matrix.mulVec, dotProduct, map_sum]
  unfold form
  rw [h, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x,
    Matrix.vecMul_transpose]

/- English proof (translation)
Use `set e : Fin n ⊕ Fin n ≃ Fin (n + n) := finSumFinEquiv with he`. Use `set M := h.1.submatrix e e with hM`. Use `set A := M.toBlocks₁₁ + M.toBlocks₁₂ with hA`. Use `set B := M.toBlocks₂₁ + M.toBlocks₂₂ with hB`. Establish `h1 : Mᵀ * Matrix.fromBlocks J 0 0 (-J) * M.map σ = Matrix.fromBlocks J 0 0 (-J)`.

Rewrite using `[← submatrix_blkMat e, show Mᵀ = h.1ᵀ.submatrix e e from rfl, show M.map σ = (h.1.map σ).submatrix e e from rfl, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]`. Conclude with `congrArg (fun X => X.submatrix e e) hh`. Rewrite `h1` using `[← Matrix.fromBlocks_toBlocks M]`. Simplify using `only [Matrix.fromBlocks_map, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_neg, Matrix.neg_mul, Matrix.fromBlocks_inj] at h1`. Take `⟨h11, h12, h21, h22⟩` from `h1`.

Establish `hAB : Aᵀ * J * A.map σ = Bᵀ * J * B.map σ`. Rewrite using `[hA, hB, Matrix.map_add _ (map_add σ), Matrix.map_add _ (map_add σ), Matrix.transpose_add, Matrix.transpose_add, ← sub_eq_zero]`. Simplify using `only [Matrix.add_mul, Matrix.mul_add]`. Use `Eq.trans ?_ ((congrArg₂ (· + ·) (congrArg₂ (· + ·) h11 h12) (congrArg₂ (· + ·) h21 h22)).trans (by simp))` and prove the remaining obligations. Normalize the expressions using the abelian group laws.

Establish `hf : ∀ x, form σ J (A *ᵥ x) (A *ᵥ x) = form σ J (B *ᵥ x) (B *ᵥ x)` using `fun x => by`. Rewrite using `[form_mulVec, form_mulVec, hAB]`. Establish `hd : ∀ x, h.1 *ᵥ pairVec e x x = pairVec e (A *ᵥ x) (B *ᵥ x)` using `fun x => by`. Rewrite using `[mulVec_pairVec, hA, hB, Matrix.add_mulVec, Matrix.add_mulVec]`. Establish `h0 : ∀ x, A *ᵥ x = 0 → B *ᵥ x = 0 → x = 0` using `fun x ha hb => by`.

Establish `h2 : h.1 *ᵥ pairVec e x x = h.1 *ᵥ 0`. Rewrite using `[hd, ha, hb, Matrix.mulVec_zero]`. Apply the tactic sequence `funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp`. Establish `h3` using `Matrix.mulVec_injective_iff_isUnit.2 h.isUnit h2`. Use function extensionality and compare the values at `i`.

Simplify using `using congrFun h3 (e (.inl i))`. Establish `hz : form σ J 0 0 = 0` using `by simp [form]`. Establish `hAu : IsUnit A` using `Matrix.mulVec_injective_iff_isUnit.1 fun x y hxy => by`. Establish `ha : A *ᵥ (x - y) = 0` using `by rw [Matrix.mulVec_sub]; exact sub_eq_zero.2 hxy`. Conclude with `sub_eq_zero.1 (h0 _ ha (han _ (by rw [← hf, ha, hz])))`.

Establish `hBu : IsUnit B` using `Matrix.mulVec_injective_iff_isUnit.1 fun x y hxy => by`. Establish `hb : B *ᵥ (x - y) = 0` using `by rw [Matrix.mulVec_sub]; exact sub_eq_zero.2 hxy`. Conclude with `sub_eq_zero.1 (h0 _ (han _ (by rw [hf, hb, hz])) hb)`. Take `⟨a, ha⟩` from `hAu`. Take `⟨b, hb⟩` from `hBu`.

Use `⟨a * b⁻¹, ?_, keepsDiag_of_mulVec fun w hw => ?_⟩` and prove the remaining obligations. Establish `hbb : B * (b⁻¹).1 = 1` using `by rw [← hb]; exact b.mul_inv`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Units.val_mul, ha, Matrix.transpose_mul, Matrix.map_mul]`. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = (B * (b⁻¹).1)ᵀ * J * (B * (b⁻¹).1).map σ := by`. Rewrite using `[hAB, Matrix.transpose_mul, Matrix.map_mul]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = J := by rw [hbb, Matrix.map_one _ (map_zero σ) (map_one σ)]; simp`. Take `⟨x, rfl⟩` from `(mem_diagSub e).1 hw`.

Rewrite using `[← Matrix.mulVec_mulVec, hd, blkMat_mulVec, pairVec_mem_diagSub, Matrix.one_mulVec, Matrix.mulVec_mulVec, ← hb, ← Units.val_mul, inv_mul_cancel_right, ha]`.
-/
theorem exists_isometry_keepsDiag {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (han : ∀ x : Fin n → E, form σ J x x = 0 → x = 0)
    (h : GL (Fin (n + n)) E)
    (hh : h.1ᵀ * dblGram finSumFinEquiv J * h.1.map σ = dblGram finSumFinEquiv J) :
    ∃ D : GL (Fin n) E, D.1ᵀ * J * D.1.map σ = J ∧ KeepsDiag finSumFinEquiv (blkMat finSumFinEquiv 1 D.1 * h.1) := by
  set e : Fin n ⊕ Fin n ≃ Fin (n + n) := finSumFinEquiv with he
  set M := h.1.submatrix e e with hM
  set A := M.toBlocks₁₁ + M.toBlocks₁₂ with hA
  set B := M.toBlocks₂₁ + M.toBlocks₂₂ with hB
  have h1 : Mᵀ * Matrix.fromBlocks J 0 0 (-J) * M.map σ = Matrix.fromBlocks J 0 0 (-J) := by
    rw [← submatrix_blkMat e, show Mᵀ = h.1ᵀ.submatrix e e from rfl,
      show M.map σ = (h.1.map σ).submatrix e e from rfl, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
    exact congrArg (fun X => X.submatrix e e) hh
  rw [← Matrix.fromBlocks_toBlocks M] at h1
  simp only [Matrix.fromBlocks_map, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.mul_zero,
    add_zero, zero_add, Matrix.mul_neg, Matrix.neg_mul, Matrix.fromBlocks_inj] at h1
  obtain ⟨h11, h12, h21, h22⟩ := h1
  have hAB : Aᵀ * J * A.map σ = Bᵀ * J * B.map σ := by
    rw [hA, hB, Matrix.map_add _ (map_add σ), Matrix.map_add _ (map_add σ), Matrix.transpose_add,
      Matrix.transpose_add, ← sub_eq_zero]
    simp only [Matrix.add_mul, Matrix.mul_add]
    refine Eq.trans ?_ ((congrArg₂ (· + ·) (congrArg₂ (· + ·) h11 h12) (congrArg₂ (· + ·) h21 h22)).trans
      (by simp))
    abel
  have hf : ∀ x, form σ J (A *ᵥ x) (A *ᵥ x) = form σ J (B *ᵥ x) (B *ᵥ x) := fun x => by
    rw [form_mulVec, form_mulVec, hAB]
  have hd : ∀ x, h.1 *ᵥ pairVec e x x = pairVec e (A *ᵥ x) (B *ᵥ x) := fun x => by
    rw [mulVec_pairVec, hA, hB, Matrix.add_mulVec, Matrix.add_mulVec]
  have h0 : ∀ x, A *ᵥ x = 0 → B *ᵥ x = 0 → x = 0 := fun x ha hb => by
    have h2 : h.1 *ᵥ pairVec e x x = h.1 *ᵥ 0 := by
      rw [hd, ha, hb, Matrix.mulVec_zero]
      funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
    have h3 := Matrix.mulVec_injective_iff_isUnit.2 h.isUnit h2
    funext i
    simpa using congrFun h3 (e (.inl i))
  have hz : form σ J 0 0 = 0 := by simp [form]
  have hAu : IsUnit A := Matrix.mulVec_injective_iff_isUnit.1 fun x y hxy => by
    have ha : A *ᵥ (x - y) = 0 := by rw [Matrix.mulVec_sub]; exact sub_eq_zero.2 hxy
    exact sub_eq_zero.1 (h0 _ ha (han _ (by rw [← hf, ha, hz])))
  have hBu : IsUnit B := Matrix.mulVec_injective_iff_isUnit.1 fun x y hxy => by
    have hb : B *ᵥ (x - y) = 0 := by rw [Matrix.mulVec_sub]; exact sub_eq_zero.2 hxy
    exact sub_eq_zero.1 (h0 _ (han _ (by rw [hf, hb, hz])) hb)
  obtain ⟨a, ha⟩ := hAu
  obtain ⟨b, hb⟩ := hBu
  refine ⟨a * b⁻¹, ?_, keepsDiag_of_mulVec fun w hw => ?_⟩
  · have hbb : B * (b⁻¹).1 = 1 := by rw [← hb]; exact b.mul_inv
    calc _ = (b⁻¹).1ᵀ * (Aᵀ * J * A.map σ) * (b⁻¹).1.map σ := by
          rw [Units.val_mul, ha, Matrix.transpose_mul, Matrix.map_mul]
          simp only [Matrix.mul_assoc]
      _ = (B * (b⁻¹).1)ᵀ * J * (B * (b⁻¹).1).map σ := by
          rw [hAB, Matrix.transpose_mul, Matrix.map_mul]
          simp only [Matrix.mul_assoc]
      _ = J := by rw [hbb, Matrix.map_one _ (map_zero σ) (map_one σ)]; simp
  · obtain ⟨x, rfl⟩ := (mem_diagSub e).1 hw
    rw [← Matrix.mulVec_mulVec, hd, blkMat_mulVec, pairVec_mem_diagSub, Matrix.one_mulVec, Matrix.mulVec_mulVec,
      ← hb, ← Units.val_mul, inv_mul_cancel_right, ha]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n J J₂ han hJ i hi r hr`. Establish `hinj : Function.Injective (inclR (F` using `F) (E := E) (AF F)) := Algebra.TensorProduct.includeRight_injective (NumberField.AdeleRing.algebraMap_injective (𝓞 F) F)`. Establish `hc : ∀ {k : ℕ} (X : Matrix (Fin k) (Fin k) E), (X.map (inclR (F` using `F) (AF F))).map (cA σ) = (X.map σ).map (inclR (F := F) (AF F)) := fun X => by`. Use extensionality with `a b`. Simplify using `[cA, inclR]`.

Establish `hU : ∀ {k : ℕ} (Q X : Matrix (Fin k) (Fin k) E), (X.map (inclR (F` using `F) (AF F)))ᵀ * incM F Q * (X.map (inclR (F := F) (AF F))).map (cA σ) = incM F (Xᵀ * Q * X.map σ) := fun Q X => by`. Rewrite using `[hc, incM, incM, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]`. Prove the components needed by the constructor for the conclusion. Introduce `δ δ' h`. Take `⟨q, hq⟩` from `GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.1 h`.

Establish `h1 : ((q : ratU σ J₂) : UA σ J₂) = i ((1, (δ' : UA σ J)) * (1, (δ : UA σ J))⁻¹)`. Rewrite using `[map_mul, map_inv, ← hr, ← hr, ← hq]`. Simplify using the standard rewrite rules. Establish `h2` using `mem_siegelOf.1 (Subgroup.mem_subgroupOf.1 q.2)`. Rewrite `h2` using `[h1]`.

Express the relevant statement in the definitionally equal form `KeepsDiag finSumFinEquiv (mat (i (1 * 1⁻¹, (δ' : UA σ J) * (δ : UA σ J)⁻¹))) at h2`. Rewrite `h2` using `[hi, keepsDiag_blkMat]`. Establish `h3 : (δ' : UA σ J) * (δ : UA σ J)⁻¹ = 1`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises.

Establish `h4 : mat ((δ' : UA σ J) * (δ : UA σ J)⁻¹) = mat (1 : UA σ J)` using `by simpa using h2`. Conclude with `h4`. Conclude with `Subtype.ext (mul_inv_eq_one.1 h3).symm`. Introduce `c`. Take `⟨γ, rfl⟩` from `Quotient.exists_rep c`.

Take `⟨h, hh⟩` from `MonoidHom.mem_range.1 (Subgroup.mem_subgroupOf.1 (γ⁻¹).2)`. Establish `hm : mat ((γ⁻¹ : ratU σ J₂) : UA σ J₂) = h.1.map (inclR (F` using `F) (AF F)) := by show ((γ⁻¹ : ratU σ J₂) : UA σ J₂).1.val = _`. Rewrite using `[← hh]`. Both sides reduce to the same expression. Establish `hu : h.1ᵀ * J₂ * h.1.map σ = J₂`.

Establish `h1 : (mat ((γ⁻¹ : ratU σ J₂) : UA σ J₂))ᵀ * incM F J₂ * (mat ((γ⁻¹ : ratU σ J₂) : UA σ J₂)).map (cA σ) = incM F J₂` using `((γ⁻¹ : ratU σ J₂) : UA σ J₂).2`. Rewrite `h1` using `[hm, hU]`. Conclude with `Matrix.map_injective hinj h1`. Take `⟨D, hD, hK⟩` from `exists_isometry_keepsDiag σ J han h (by rw [← hJ]; exact hu)`. Establish `hDU : Matrix.GeneralLinearGroup.map (inclR (F` using `F) (AF F)) D ∈ UG (cA σ) (incM F J) := by`.

Express the relevant statement in the definitionally equal form `(D.1.map (inclR (F := F) (AF F)))ᵀ * incM F J * (D.1.map (inclR (F := F) (AF F))).map (cA σ) = _`. Rewrite using `[hU, hD]`. Set `δ : ratU σ J` to `⟨⟨_, hDU⟩, Subgroup.mem_subgroupOf.2 ⟨D, rfl⟩⟩`. Use `⟨δ, Eq.symm (GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.2 ⟨⟨r δ * γ⁻¹, ?_⟩, by simp⟩)⟩` and prove the remaining obligations. Use `Subgroup.mem_subgroupOf.2 (mem_siegelOf.2 ?_)` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `KeepsDiag finSumFinEquiv (mat (r δ : UA σ J₂) * mat ((γ⁻¹ : ratU σ J₂) : UA σ J₂))`. Establish `h2` using `KeepsDiag.map _ hK (inclR (F := F) (AF F))`. Rewrite `h2` using `[Matrix.map_mul, blkMat_map _ _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _)]`. Rewrite using `[hr, hi, hm]`. Conclude with `h2`.
-/
theorem bijective_open_orbit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E), (∀ x : Fin n → E, form σ J x x = 0 → x = 0) →
    J₂ = dblGram finSumFinEquiv J → ∀ i : UA σ J × UA σ J →* UA σ J₂, (∀ h h', mat (i (h, h')) = blkMat finSumFinEquiv (mat h) (mat h')) →
    ∀ r : ratU σ J → ratU σ J₂, (∀ δ, (r δ : UA σ J₂) = i (1, δ)) →
    Function.Bijective fun δ => GlobalTheory.AutomorphicL2Unitary.mk ((siegelOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype).subgroupOf (ratU σ J₂)) (r δ) := by
  intro F E _ _ _ _ _ σ n J J₂ han hJ i hi r hr
  have hinj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
    Algebra.TensorProduct.includeRight_injective (NumberField.AdeleRing.algebraMap_injective (𝓞 F) F)
  have hc : ∀ {k : ℕ} (X : Matrix (Fin k) (Fin k) E),
      (X.map (inclR (F := F) (AF F))).map (cA σ) = (X.map σ).map (inclR (F := F) (AF F)) := fun X => by
    ext a b
    simp [cA, inclR]
  have hU : ∀ {k : ℕ} (Q X : Matrix (Fin k) (Fin k) E),
      (X.map (inclR (F := F) (AF F)))ᵀ * incM F Q * (X.map (inclR (F := F) (AF F))).map (cA σ) =
        incM F (Xᵀ * Q * X.map σ) := fun Q X => by
    rw [hc, incM, incM, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  constructor
  · intro δ δ' h
    obtain ⟨q, hq⟩ := GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.1 h
    have h1 : ((q : ratU σ J₂) : UA σ J₂) = i ((1, (δ' : UA σ J)) * (1, (δ : UA σ J))⁻¹) := by
      rw [map_mul, map_inv, ← hr, ← hr, ← hq]
      simp
    have h2 := mem_siegelOf.1 (Subgroup.mem_subgroupOf.1 q.2)
    rw [h1] at h2
    change KeepsDiag finSumFinEquiv (mat (i (1 * 1⁻¹, (δ' : UA σ J) * (δ : UA σ J)⁻¹))) at h2
    rw [hi, keepsDiag_blkMat] at h2
    have h3 : (δ' : UA σ J) * (δ : UA σ J)⁻¹ = 1 := by
      apply Subtype.ext
      apply Units.ext
      have h4 : mat ((δ' : UA σ J) * (δ : UA σ J)⁻¹) = mat (1 : UA σ J) := by simpa using h2
      exact h4
    exact Subtype.ext (mul_inv_eq_one.1 h3).symm
  · intro c
    obtain ⟨γ, rfl⟩ := Quotient.exists_rep c
    obtain ⟨h, hh⟩ := MonoidHom.mem_range.1 (Subgroup.mem_subgroupOf.1 (γ⁻¹).2)
    have hm : mat ((γ⁻¹ : ratU σ J₂) : UA σ J₂) = h.1.map (inclR (F := F) (AF F)) := by
      show ((γ⁻¹ : ratU σ J₂) : UA σ J₂).1.val = _
      rw [← hh]; rfl
    have hu : h.1ᵀ * J₂ * h.1.map σ = J₂ := by
      have h1 : (mat ((γ⁻¹ : ratU σ J₂) : UA σ J₂))ᵀ * incM F J₂ * (mat ((γ⁻¹ : ratU σ J₂) : UA σ J₂)).map (cA σ) =
        incM F J₂ := ((γ⁻¹ : ratU σ J₂) : UA σ J₂).2
      rw [hm, hU] at h1
      exact Matrix.map_injective hinj h1
    obtain ⟨D, hD, hK⟩ := exists_isometry_keepsDiag σ J han h (by rw [← hJ]; exact hu)
    have hDU : Matrix.GeneralLinearGroup.map (inclR (F := F) (AF F)) D ∈ UG (cA σ) (incM F J) := by
      change (D.1.map (inclR (F := F) (AF F)))ᵀ * incM F J * (D.1.map (inclR (F := F) (AF F))).map (cA σ) = _
      rw [hU, hD]
    let δ : ratU σ J := ⟨⟨_, hDU⟩, Subgroup.mem_subgroupOf.2 ⟨D, rfl⟩⟩
    refine ⟨δ, Eq.symm (GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.2 ⟨⟨r δ * γ⁻¹, ?_⟩, by simp⟩)⟩
    refine Subgroup.mem_subgroupOf.2 (mem_siegelOf.2 ?_)
    change KeepsDiag finSumFinEquiv (mat (r δ : UA σ J₂) * mat ((γ⁻¹ : ratU σ J₂) : UA σ J₂))
    have h2 := KeepsDiag.map _ hK (inclR (F := F) (AF F))
    rw [Matrix.map_mul, blkMat_map _ _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _)] at h2
    rw [hr, hi, hm]
    exact h2

end GlobalTheory.DoublingRat

end
