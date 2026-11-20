import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergMatrixPreservesForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCentralUnipotentTranslate

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.HermAnisConstTerm

open GlobalTheory.UnipMass

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Establish `hσ` using `cm_conj_conj h`. Take `⟨_, hc, _, hconj⟩` from `h`. Take `⟨w⟩ : Nonempty (InfinitePlace E)` from `inferInstance`. Establish `hw : w.IsComplex` using `hc.isComplex w`. Rewrite `hw` using `[InfinitePlace.isComplex_iff]`.

Establish `: ∃ x, star (w.embedding x) ≠ w.embedding x`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Conclude with `hw (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => by`. Rewrite using `[ComplexEmbedding.conjugate_coe_eq]`.

Conclude with `hne x))`. Take `⟨x, hx⟩` from `this`. Use `⟨x - σ x, fun h0 => hx ?_, by rw [map_sub, hσ, neg_sub]⟩` and prove the remaining obligations. Establish `: σ x = x` using `(sub_eq_zero.1 h0).symm`. Rewrite using `[← hconj, this]`.
-/
theorem exists_anti {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : ∃ δ : E, δ ≠ 0 ∧ σ δ = -δ := by
  have hσ := cm_conj_conj h
  obtain ⟨_, hc, _, hconj⟩ := h
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  have hw : w.IsComplex := hc.isComplex w
  rw [InfinitePlace.isComplex_iff] at hw
  have : ∃ x, star (w.embedding x) ≠ w.embedding x := by
    by_contra hne
    push_neg at hne
    exact hw (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => by
      rw [ComplexEmbedding.conjugate_coe_eq]; exact hne x))
  obtain ⟨x, hx⟩ := this
  refine ⟨x - σ x, fun h0 => hx ?_, by rw [map_sub, hσ, neg_sub]⟩
  have : σ x = x := (sub_eq_zero.1 h0).symm
  rw [← hconj, this]

/- English proof (translation)
Simplify using `only [hA, dotProduct, Matrix.mulVec, map_sum, map_mul, Unitary.cA_invol σ hσ, incM, Matrix.map_apply, Unitary.cA_inclR, hJ, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hA_swap_herm (σ : E →ₐ[F] E) (hσ : ∀ a, σ (σ a) = a) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (v w : Fin n → AE F E) :
    hA σ J w v = cA σ (hA σ J v w) := by
  simp only [hA, dotProduct, Matrix.mulVec, map_sum, map_mul, Unitary.cA_invol σ hσ, incM, Matrix.map_apply,
    Unitary.cA_inclR, hJ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

variable {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

/- English proof (translation)
Rewrite using `[nmat_mulVec, hA_zero_right, zero_smul, sub_zero, zero_add, smul_smul]`.
-/
theorem unipotent_transvection_mulVec (x : Fin n → AE F E) (c : AE F E) (v : Fin n → AE F E) :
    nmat σ J x 0 c *ᵥ v = v - (hA σ J v x * c) • x := by
  rw [nmat_mulVec, hA_zero_right, zero_smul, sub_zero, zero_add, smul_smul]

/- English proof (translation)
Use `Matrix.ext_of_mulVec_single fun i => ?_` and prove the remaining obligations. Rewrite using `[← Matrix.mulVec_mulVec, unipotent_transvection_mulVec, unipotent_transvection_mulVec, unipotent_transvection_mulVec, Unitary.hA_sub_left, Unitary.hA_smul_left, hxx, mul_zero, sub_zero, sub_sub, ← add_smul]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem unipotent_transvection_mul (x : Fin n → AE F E) (hxx : hA σ J x x = 0) (c c' : AE F E) :
    nmat σ J x 0 c * nmat σ J x 0 c' = nmat σ J x 0 (c + c') := by
  refine Matrix.ext_of_mulVec_single fun i => ?_
  rw [← Matrix.mulVec_mulVec, unipotent_transvection_mulVec, unipotent_transvection_mulVec, unipotent_transvection_mulVec, Unitary.hA_sub_left, Unitary.hA_smul_left,
    hxx, mul_zero, sub_zero, sub_sub, ← add_smul]
  congr 2
  ring

/- English proof (translation)
Establish `key : ∀ v w : Fin n → AE F E, hA σ J (nmat σ J x 0 c *ᵥ v) (nmat σ J x 0 c *ᵥ w) = hA σ J v w`. Introduce `v w`. Rewrite using `[unipotent_transvection_mulVec, unipotent_transvection_mulVec]`. Establish `hxw : hA σ J x w = cA σ (hA σ J w x)` using `hA_swap_herm σ hσ J hJ _ _`. Simplify using `only [Unitary.hA_sub_left, Unitary.hA_sub_right, Unitary.hA_smul_left, Unitary.hA_smul_right, hxx, hxw, map_mul]`.

Take the linear combination `(-(hA σ J v x * cA σ (hA σ J w x))) * hc`. Use extensionality with `i j`. Rewrite using `[Unitary.entry_eq, key, ← Unitary.entry_J hσ]`.
-/
theorem unipotent_transvection_unitary (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j) (x : Fin n → AE F E)
    (hxx : hA σ J x x = 0) (c : AE F E) (hc : cA σ c = -c) :
    (nmat σ J x 0 c)ᵀ * incM F J * (nmat σ J x 0 c).map (cA σ) = incM F J := by
  have key : ∀ v w : Fin n → AE F E, hA σ J (nmat σ J x 0 c *ᵥ v) (nmat σ J x 0 c *ᵥ w) = hA σ J v w := by
    intro v w
    rw [unipotent_transvection_mulVec, unipotent_transvection_mulVec]
    have hxw : hA σ J x w = cA σ (hA σ J w x) := hA_swap_herm σ hσ J hJ _ _
    simp only [Unitary.hA_sub_left, Unitary.hA_sub_right, Unitary.hA_smul_left, Unitary.hA_smul_right, hxx, hxw,
      map_mul]
    linear_combination (-(hA σ J v x * cA σ (hA σ J w x))) * hc
  ext i j
  rw [Unitary.entry_eq, key, ← Unitary.entry_J hσ]

def cz (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j) (x : Fin n → AE F E) (hxx : hA σ J x x = 0)
    (c : AE F E) (hc : cA σ c = -c) : UA σ J :=
  ⟨⟨nmat σ J x 0 c, nmat σ J x 0 (-c), by rw [unipotent_transvection_mul x hxx, add_neg_cancel, nmat_zero],
    by rw [unipotent_transvection_mul x hxx, neg_add_cancel, nmat_zero]⟩, unipotent_transvection_unitary hσ hJ x hxx c hc⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mat_cz (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j) (x : Fin n → AE F E)
    (hxx : hA σ J x x = 0) (c : AE F E) (hc : cA σ c = -c) : mat (cz hσ hJ x hxx c hc) = nmat σ J x 0 c := rfl

/- English proof (translation)
Establish `hxxA : hA σ X.J (incV F H.x) (incV F H.x) = 0` using `by rw [hA_incV, hxx, map_zero]`. Establish `hc' : cA σ (-c) = -(-c)` using `by rw [map_neg, hc]`. Use `set z := cz hσ hJ (incV F H.x) hxxA (-c) hc' with hz`. Establish `hmz : ∀ v, mat z *ᵥ v = v - (hA σ X.J v (incV F H.x) * -c) • incV F H.x` using `fun v => by`. Rewrite using `[hz, mat_cz, unipotent_transvection_mulVec]`.

Establish `hzU : z ∈ unip σ X H`. Use `Subgroup.subset_closure ⟨?_, fun w' => ⟨-(hA σ X.J (incM F H.ι *ᵥ w') (incV F H.x) * -c), ?_⟩⟩` and prove the remaining obligations. Rewrite using `[hmz, hxxA, zero_mul, zero_smul, sub_zero]`. Rewrite using `[hmz, sub_eq_add_neg, neg_smul]`. Use `⟨z, hzU, fun u hu => ?_, ?_⟩` and prove the remaining obligations.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Use `show mat z * mat u = mat u * mat z`. Use `Matrix.ext_of_mulVec_single fun i => ?_` and prove the remaining obligations. Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hmz, hmz, Matrix.mulVec_sub, Matrix.mulVec_smul, CentralShift.unip_fix u hu]`.

Establish `e : hA σ X.J (mat u *ᵥ Pi.single i 1) (incV F H.x) = hA σ X.J (Pi.single i 1) (incV F H.x)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e]`. Establish `hxy' : hA σ X.J (incV F H.x) (incV F H.y) = 1` using `by rw [hA_incV, hxy, map_one]`. Establish `hyx : hA σ X.J (incV F H.y) (incV F H.x) = 1`.

Rewrite using `[hA_swap_herm σ hσ X.J hJ, hxy', map_one]`. Establish `hs : hA σ X.J (incV F H.y - c • incV F H.x) (incV F H.x) = 1`. Rewrite using `[Unitary.hA_sub_left, Unitary.hA_smul_left, hxxA, mul_zero, sub_zero, hyx]`. Establish `hzy : mat z *ᵥ (incV F H.y - c • incV F H.x) = incV F H.y`. Rewrite using `[hmz, hs, one_mul, neg_smul, sub_neg_eq_add, sub_add_cancel]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mulVec_mulVec, CentralShift.mat_inv_mul', Matrix.one_mulVec]`.
-/
theorem exists_central_shift_herm (hσ : ∀ a, σ (σ a) = a) {X : Spc F E n} (hJ : ∀ i j, σ (X.J j i) = X.J i j)
    {d₂ : ℕ} (H : Plane E n d₂) (hxx : form σ X.J H.x H.x = 0) (hxy : form σ X.J H.x H.y = 1)
    (c : AE F E) (hc : cA σ c = -c) :
    ∃ z : UA σ X.J, z ∈ unip σ X H ∧ (∀ u ∈ unip σ X H, z * u = u * z) ∧
      mat z⁻¹ *ᵥ incV F H.y = incV F H.y - c • incV F H.x := by
  have hxxA : hA σ X.J (incV F H.x) (incV F H.x) = 0 := by rw [hA_incV, hxx, map_zero]
  have hc' : cA σ (-c) = -(-c) := by rw [map_neg, hc]
  set z := cz hσ hJ (incV F H.x) hxxA (-c) hc' with hz
  have hmz : ∀ v, mat z *ᵥ v = v - (hA σ X.J v (incV F H.x) * -c) • incV F H.x := fun v => by
    rw [hz, mat_cz, unipotent_transvection_mulVec]
  have hzU : z ∈ unip σ X H := by
    refine Subgroup.subset_closure ⟨?_, fun w' => ⟨-(hA σ X.J (incM F H.ι *ᵥ w') (incV F H.x) * -c), ?_⟩⟩
    · rw [hmz, hxxA, zero_mul, zero_smul, sub_zero]
    · rw [hmz, sub_eq_add_neg, neg_smul]
  refine ⟨z, hzU, fun u hu => ?_, ?_⟩
  · apply Subtype.ext
    apply Units.ext
    show mat z * mat u = mat u * mat z
    refine Matrix.ext_of_mulVec_single fun i => ?_
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hmz, hmz, Matrix.mulVec_sub, Matrix.mulVec_smul,
      CentralShift.unip_fix u hu]
    have e : hA σ X.J (mat u *ᵥ Pi.single i 1) (incV F H.x) = hA σ X.J (Pi.single i 1) (incV F H.x) :=
      calc hA σ X.J (mat u *ᵥ Pi.single i 1) (incV F H.x)
          = hA σ X.J (mat u *ᵥ Pi.single i 1) (mat u *ᵥ incV F H.x) := by rw [CentralShift.unip_fix u hu]
        _ = _ := CentralShift.hA_mat σ u _ _
    rw [e]
  · have hxy' : hA σ X.J (incV F H.x) (incV F H.y) = 1 := by rw [hA_incV, hxy, map_one]
    have hyx : hA σ X.J (incV F H.y) (incV F H.x) = 1 := by
      rw [hA_swap_herm σ hσ X.J hJ, hxy', map_one]
    have hs : hA σ X.J (incV F H.y - c • incV F H.x) (incV F H.x) = 1 := by
      rw [Unitary.hA_sub_left, Unitary.hA_smul_left, hxxA, mul_zero, sub_zero, hyx]
    have hzy : mat z *ᵥ (incV F H.y - c • incV F H.x) = incV F H.y := by
      rw [hmz, hs, one_mul, neg_smul, sub_neg_eq_add, sub_add_cancel]
    calc mat z⁻¹ *ᵥ incV F H.y
        = mat z⁻¹ *ᵥ (mat z *ᵥ (incV F H.y - c • incV F H.x)) := by rw [hzy]
      _ = incV F H.y - c • incV F H.x := by
        rw [Matrix.mulVec_mulVec, CentralShift.mat_inv_mul', Matrix.one_mulVec]

end GlobalTheory.HermAnisConstTerm
