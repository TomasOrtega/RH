import Mathlib
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SignatureConjugationInvariant
import Formalism.LocalRingCardinality.DataSpaces

noncomputable section

namespace PI.CntNotPosW

open Matrix

variable {E : Type} [Field E] [NumberField E] [StarRing E]

/- English proof (translation)
Establish `hx` using `S.frame.sum_repr x`. Establish `hy` using `S.frame.sum_repr y`. Use `conv_lhs => rw [← hx, ← hy]`. Simplify using `only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, Finset.mul_sum, Formalism.BasicNotions.HSpace.gram]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[RingHom.id_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hT_expand' (S : Formalism.BasicNotions.HSpace E) (x y : S.V) :
    S.hT x y = ∑ a, ∑ b, star (S.frame.repr x a) * S.gram a b * S.frame.repr y b := by
  have hx := S.frame.sum_repr x
  have hy := S.frame.sum_repr y
  conv_lhs => rw [← hx, ← hy]
  simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, Finset.mul_sum, Formalism.BasicNotions.HSpace.gram]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [RingHom.id_apply]
  ring

/- English proof (translation)
Rewrite using `[hT_expand', map_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, hτ, Matrix.map_apply, starRingEnd_apply]`.
-/
theorem hT_map (S : Formalism.BasicNotions.HSpace E) (τ : E →+* ℂ) (hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a))
    (x y : S.V) :
    τ (S.hT x y) = ∑ a, ∑ b, star (τ (S.frame.repr x a)) * (S.gram.map τ) a b * τ (S.frame.repr y b) := by
  rw [hT_expand', map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_mul, map_mul, hτ, Matrix.map_apply, starRingEnd_apply]

/- English proof (translation)
Take `⟨e, P, hP⟩` from `hS`. Establish `hQQi : (P : Matrix (Fin p' ⊕ Fin q') (Fin p' ⊕ Fin q') ℂ) * ((P⁻¹ : GL (Fin p' ⊕ Fin q') ℂ) : Matrix (Fin p' ⊕ Fin q') (Fin p' ⊕ Fin q') ℂ) = 1` using `Units.mul_inv P`. Establish `hcT : Formalism.UG.cT (starRingEnd ℂ) (P : Matrix (Fin p' ⊕ Fin q') (Fin p' ⊕ Fin q') ℂ) = (P : Matrix (Fin p' ⊕ Fin q') (Fin p' ⊕ Fin q') ℂ)ᴴ`. Use extensionality with `i j`. Simplify using `[Formalism.UG.cT, Matrix.conjTranspose_apply]`.

Rewrite `hP` using `[hcT]`. Take `⟨col, hcol⟩ : ∃ col : S.V → Matrix (Fin p' ⊕ Fin q') (Fin 1) ℂ, ∀ x s, col x s 0 = τ (S.frame.repr x (e.symm s))` from `⟨fun x => Matrix.of fun s _ => τ (S.frame.repr x (e.symm s)), fun _ _ => rfl⟩`. Establish `key : ∀ x y : S.V, τ (S.hT x y) = ((col x)ᴴ * (S.gram.map τ).reindex e e * col y) 0 0`. Introduce `x y`. Rewrite using `[hT_map S τ hτ x y]`.

Simplify using `only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.reindex_apply, Matrix.submatrix_apply, hcol, Finset.sum_mul]`. Use `conv_lhs => rw [← e.symm.sum_comp]`. Use `conv_lhs => enter [2, s]`. Rewrite using `[← e.symm.sum_comp]`. Rewrite using `[Finset.sum_comm]`.

Take `⟨V, hV⟩ : ∃ V : S.V → Matrix (Fin p' ⊕ Fin q') (Fin 1) ℂ, ∀ x, col x = (P : Matrix (Fin p' ⊕ Fin q') (Fin p' ⊕ Fin q') ℂ) * V x` from `⟨fun x => ((P⁻¹ : GL (Fin p' ⊕ Fin q') ℂ) : Matrix (Fin p' ⊕ Fin q') (Fin p' ⊕ Fin q') ℂ) * col x, fun x => by rw [← Matrix.mul_assoc, hQQi, Matrix.one_mul]⟩`. Establish `form2 : ∀ x y : S.V, τ (S.hT x y) = ((V x)ᴴ * Formalism.UG.Jpq p' q' * V y) 0 0`. Introduce `x y`. Rewrite using `[key, hV x, hV y, Matrix.conjTranspose_mul, ← hP]`. Simplify using `only [Matrix.mul_assoc]`.

Establish `hG : ∀ i j, ((V (w i))ᴴ * Formalism.UG.Jpq p' q' * V (w j)) 0 0 = if i = j then (d i : ℂ) else 0`. Introduce `i j`. Rewrite using `[← form2]`. Use `split_ifs with h`. Substitute `h` using the available equality.

Conclude with `hdiag i`. Rewrite using `[hoff i j h, map_zero]`. Set `f : ι → Fin q' → ℂ` to `fun i b => V (w i) (Sum.inr b) 0`. Establish `hli : LinearIndependent ℂ f`. Rewrite using `[Fintype.linearIndependent_iff]`.

Introduce `g hg`. Take `⟨z, hz⟩ : ∃ z : Matrix (Fin p' ⊕ Fin q') (Fin 1) ℂ, z = ∑ i, g i • V (w i)` from `⟨_, rfl⟩`. Establish `hz0 : ∀ b, z (Sum.inr b) 0 = 0`. Introduce `b`. Establish `h1` using `congrFun hg b`.

Rewrite using `[hz]`. Simplify `h1` using `[Matrix.sum_apply, f]`. Establish `hG1 : (zᴴ * Formalism.UG.Jpq p' q' * z) 0 0 = ∑ i, (star (g i) * g i) * (d i : ℂ)`. Rewrite using `[hz]`. Simplify using `only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, hG, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `hG2 : (zᴴ * Formalism.UG.Jpq p' q' * z) 0 0 = ∑ a : Fin p', star (z (Sum.inl a) 0) * z (Sum.inl a) 0`. Simplify using `[Matrix.mul_apply, Fintype.sum_sum_type, Formalism.UG.Jpq, hz0, Matrix.one_apply, Matrix.conjTranspose_apply]`. Establish `hreal : ∑ i, Complex.normSq (g i) * d i = ∑ a : Fin p', Complex.normSq (z (Sum.inl a) 0)`.

Establish `h` using `hG1.symm.trans hG2`. Simplify using `only [Complex.star_def, ← Complex.normSq_eq_conj_mul_self] at h`. Conclude with `h` after adjusting the coercions. Establish `hle : ∀ i ∈ Finset.univ, Complex.normSq (g i) * d i ≤ 0` using `fun i _ => mul_nonpos_of_nonneg_of_nonpos (Complex.normSq_nonneg _) (hneg i).le`. Establish `hsum0 : ∑ i, Complex.normSq (g i) * d i = 0` using `le_antisymm (Finset.sum_nonpos hle) (hreal ▸ Finset.sum_nonneg fun a _ => Complex.normSq_nonneg _)`.

Introduce `i`. Establish `h0` using `(Finset.sum_eq_zero_iff_of_nonpos hle).1 hsum0 i (Finset.mem_univ _)`. Break down `mul_eq_zero.1 h0 with h | h` into its components or cases. Conclude with `Complex.normSq_eq_zero.1 h`. Conclude with `absurd h (hneg i).ne`.

Establish `hc` using `hli.fintype_card_le_finrank`. Simplify using `using hc`.
-/
theorem card_le_of_negFamily (S : Formalism.BasicNotions.HSpace E) (τ : E →+* ℂ)
    (hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a)) {p' q' : ℕ}
    (hS : Formalism.UG.HasSignature (S.gram.map τ) p' q')
    {ι : Type} [Fintype ι] [DecidableEq ι] (w : ι → S.V) (d : ι → ℝ)
    (hoff : ∀ i j, i ≠ j → S.hT (w i) (w j) = 0)
    (hdiag : ∀ i, τ (S.hT (w i) (w i)) = (d i : ℂ)) (hneg : ∀ i, d i < 0) :
    Fintype.card ι ≤ q' := by
  classical
  obtain ⟨e, P, hP⟩ := hS
  have hQQi : (P : Matrix (Fin p' ⊕ Fin q') (Fin p' ⊕ Fin q') ℂ) *
      ((P⁻¹ : GL (Fin p' ⊕ Fin q') ℂ) : Matrix (Fin p' ⊕ Fin q') (Fin p' ⊕ Fin q') ℂ) = 1 :=
    Units.mul_inv P
  have hcT : Formalism.UG.cT (starRingEnd ℂ) (P : Matrix (Fin p' ⊕ Fin q') (Fin p' ⊕ Fin q') ℂ) =
      (P : Matrix (Fin p' ⊕ Fin q') (Fin p' ⊕ Fin q') ℂ)ᴴ := by
    ext i j
    simp [Formalism.UG.cT, Matrix.conjTranspose_apply]
  rw [hcT] at hP
  obtain ⟨col, hcol⟩ : ∃ col : S.V → Matrix (Fin p' ⊕ Fin q') (Fin 1) ℂ,
      ∀ x s, col x s 0 = τ (S.frame.repr x (e.symm s)) :=
    ⟨fun x => Matrix.of fun s _ => τ (S.frame.repr x (e.symm s)), fun _ _ => rfl⟩
  have key : ∀ x y : S.V,
      τ (S.hT x y) = ((col x)ᴴ * (S.gram.map τ).reindex e e * col y) 0 0 := by
    intro x y
    rw [hT_map S τ hτ x y]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.reindex_apply,
      Matrix.submatrix_apply, hcol, Finset.sum_mul]
    conv_lhs => rw [← e.symm.sum_comp]
    conv_lhs => enter [2, s]; rw [← e.symm.sum_comp]
    rw [Finset.sum_comm]
  obtain ⟨V, hV⟩ : ∃ V : S.V → Matrix (Fin p' ⊕ Fin q') (Fin 1) ℂ,
      ∀ x, col x = (P : Matrix (Fin p' ⊕ Fin q') (Fin p' ⊕ Fin q') ℂ) * V x :=
    ⟨fun x => ((P⁻¹ : GL (Fin p' ⊕ Fin q') ℂ) : Matrix (Fin p' ⊕ Fin q') (Fin p' ⊕ Fin q') ℂ) * col x,
      fun x => by rw [← Matrix.mul_assoc, hQQi, Matrix.one_mul]⟩
  have form2 : ∀ x y : S.V, τ (S.hT x y) = ((V x)ᴴ * Formalism.UG.Jpq p' q' * V y) 0 0 := by
    intro x y
    rw [key, hV x, hV y, Matrix.conjTranspose_mul, ← hP]
    simp only [Matrix.mul_assoc]
  have hG : ∀ i j, ((V (w i))ᴴ * Formalism.UG.Jpq p' q' * V (w j)) 0 0 = if i = j then (d i : ℂ) else 0 := by
    intro i j
    rw [← form2]
    split_ifs with h
    · subst h
      exact hdiag i
    · rw [hoff i j h, map_zero]
  let f : ι → Fin q' → ℂ := fun i b => V (w i) (Sum.inr b) 0
  have hli : LinearIndependent ℂ f := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    obtain ⟨z, hz⟩ : ∃ z : Matrix (Fin p' ⊕ Fin q') (Fin 1) ℂ, z = ∑ i, g i • V (w i) := ⟨_, rfl⟩
    have hz0 : ∀ b, z (Sum.inr b) 0 = 0 := by
      intro b
      have h1 := congrFun hg b
      rw [hz]
      simpa [Matrix.sum_apply, f] using h1
    have hG1 : (zᴴ * Formalism.UG.Jpq p' q' * z) 0 0 = ∑ i, (star (g i) * g i) * (d i : ℂ) := by
      rw [hz]
      simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, Matrix.sum_mul, Matrix.mul_sum,
        Matrix.smul_mul, Matrix.mul_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, hG,
        mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    have hG2 : (zᴴ * Formalism.UG.Jpq p' q' * z) 0 0 =
        ∑ a : Fin p', star (z (Sum.inl a) 0) * z (Sum.inl a) 0 := by
      simp [Matrix.mul_apply, Fintype.sum_sum_type, Formalism.UG.Jpq, hz0, Matrix.one_apply,
        Matrix.conjTranspose_apply]
    have hreal : ∑ i, Complex.normSq (g i) * d i = ∑ a : Fin p', Complex.normSq (z (Sum.inl a) 0) := by
      have h := hG1.symm.trans hG2
      simp only [Complex.star_def, ← Complex.normSq_eq_conj_mul_self] at h
      exact_mod_cast h
    have hle : ∀ i ∈ Finset.univ, Complex.normSq (g i) * d i ≤ 0 := fun i _ =>
      mul_nonpos_of_nonneg_of_nonpos (Complex.normSq_nonneg _) (hneg i).le
    have hsum0 : ∑ i, Complex.normSq (g i) * d i = 0 :=
      le_antisymm (Finset.sum_nonpos hle)
        (hreal ▸ Finset.sum_nonneg fun a _ => Complex.normSq_nonneg _)
    intro i
    have h0 := (Finset.sum_eq_zero_iff_of_nonpos hle).1 hsum0 i (Finset.mem_univ _)
    rcases mul_eq_zero.1 h0 with h | h
    · exact Complex.normSq_eq_zero.1 h
    · exact absurd h (hneg i).ne
  have hc := hli.fintype_card_le_finrank
  simpa using hc

end PI.CntNotPosW
