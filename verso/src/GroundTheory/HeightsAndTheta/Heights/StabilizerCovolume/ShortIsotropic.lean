import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.Objects
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix

section Herm

variable {Em : Type} [Field Em] [NumberField Em] [IsCMField Em] {Ψ : Type} [Fintype Ψ] {N j : ℕ}

def HermDatum.IsWittPoint (A : HermDatum Em Ψ N j) (P : Ψ → Matrix (Fin N) (Fin N) ℂ) : Prop :=
  ∀ τ, (P τ)ᴴ * A.H.map (A.emb τ) * P τ = signMat N j

def HermDatum.hodgeNormSq (A : HermDatum Em Ψ N j) (P : Ψ → Matrix (Fin N) (Fin N) ℂ) (v : Fin N → Em) : ℝ :=
  ∑ τ, 2 * ‖A.emb τ A.ξ‖ * ∑ c, ‖((P τ)⁻¹ *ᵥ fun a => A.emb τ (v a)) c‖ ^ 2

def HermDatum.hodgeNorm (A : HermDatum Em Ψ N j) (P : Ψ → Matrix (Fin N) (Fin N) ℂ) (v : Fin N → Em) : ℝ :=
  Real.sqrt (A.hodgeNormSq P v)

def HermDatum.shortSpan (A : HermDatum Em Ψ N j) (P : Ψ → Matrix (Fin N) (Fin N) ℂ) (r : ℝ) :
    Submodule (𝓞 Em) (Fin N → Em) :=
  Submodule.span (𝓞 Em) {v | v ∈ A.L ∧ A.hodgeNorm P v < r}

variable (Em) in

def IntegralBasisBound (vr : ℝ) : Prop :=
  ∃ (κ : Type) (_ : Fintype κ) (a : κ → 𝓞 Em), Fintype.card κ = Module.finrank ℚ Em ∧
    LinearIndependent ℚ (fun i => (a i : Em)) ∧ ∀ i (σ : Em →+* ℂ), ‖σ (a i)‖ ≤ vr

end Herm

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)] {Em : Type} [Field Em] [NumberField Em] [IsCMField Em]

def ShortIsotropic.Statement (D : FullerData II Ψ K ι Ω E Em) : Prop :=
  ∀ z ∈ mcPts (mCoordIdeal D.y) \ D.Bd, ∀ vr : ℝ, IntegralBasisBound Em vr →
    D.herm.IsIso (D.herm.shortSpan (D.per z) (Real.sqrt vr)⁻¹)

namespace ShortIsotropic

section Herm

variable {Em : Type} [Field Em] [NumberField Em] [IsCMField Em] {Ψ : Type} [Fintype Ψ] {N j : ℕ}

/- English proof (translation)
Simplify using `[hermForm]`.
-/
theorem hermForm_zero_left (H : Matrix (Fin N) (Fin N) Em) (y : Fin N → Em) : hermForm Em H 0 y = 0 := by
  simp [hermForm]

/- English proof (translation)
Simplify using `[hermForm]`.
-/
theorem hermForm_zero_right (H : Matrix (Fin N) (Fin N) Em) (x : Fin N → Em) : hermForm Em H x 0 = 0 := by
  simp [hermForm]

/- English proof (translation)
Simplify using `only [hermForm, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]`.
-/
theorem hermForm_add_left (H : Matrix (Fin N) (Fin N) Em) (x x' y : Fin N → Em) :
    hermForm Em H (x + x') y = hermForm Em H x y + hermForm Em H x' y := by
  simp only [hermForm, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [hermForm, Pi.add_apply, mul_add, Finset.sum_add_distrib]`.
-/
theorem hermForm_add_right (H : Matrix (Fin N) (Fin N) Em) (x y y' : Fin N → Em) :
    hermForm Em H x (y + y') = hermForm Em H x y + hermForm Em H x y' := by
  simp only [hermForm, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [hermForm, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`.
-/
theorem hermForm_smul_left (H : Matrix (Fin N) (Fin N) Em) (c : Em) (x y : Fin N → Em) :
    hermForm Em H (c • x) y = IsCMField.complexConj Em c * hermForm Em H x y := by
  simp only [hermForm, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/- English proof (translation)
Simplify using `only [hermForm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`.
-/
theorem hermForm_smul_right (H : Matrix (Fin N) (Fin N) Em) (c : Em) (x y : Fin N → Em) :
    hermForm Em H x (c • y) = c * hermForm Em H x y := by
  simp only [hermForm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

omit [NumberField Em] [IsCMField Em] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem oSmul_eq (c : 𝓞 Em) (x : Fin N → Em) : c • x = (c : Em) • x := rfl

/- English proof (translation)
Simplify using `only [hermForm, map_sum, map_mul, IsCMField.complexEmbedding_complexConj, dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply, Finset.mul_sum, mul_assoc, starRingEnd_apply]`.
-/
theorem emb_hermForm (σ : Em →+* ℂ) (H : Matrix (Fin N) (Fin N) Em) (x y : Fin N → Em) :
    σ (hermForm Em H x y) = star (fun a => σ (x a)) ⬝ᵥ (H.map σ *ᵥ fun b => σ (y b)) := by
  simp only [hermForm, map_sum, map_mul, IsCMField.complexEmbedding_complexConj, dotProduct, Matrix.mulVec,
    Matrix.map_apply, Pi.star_apply, Finset.mul_sum, mul_assoc, starRingEnd_apply]

/- English proof (translation)
Rewrite using `[signMat, Matrix.det_diagonal]`. Apply the tactic sequence `exact Finset.prod_ne_zero_iff.mpr fun a _ => by split_ifs <;> norm_num`.
-/
theorem det_signMat_ne_zero (N j : ℕ) : (signMat N j).det ≠ 0 := by
  rw [signMat, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr fun a _ => by split_ifs <;> norm_num

/- English proof (translation)
Rewrite using `[isUnit_iff_ne_zero]`. Introduce `h0`. Establish `h` using `congrArg Matrix.det hW`. Rewrite `h` using `[Matrix.det_mul, h0, mul_zero]`. Conclude with `det_signMat_ne_zero N j h.symm`.
-/
theorem isUnit_det_of_witt {M P : Matrix (Fin N) (Fin N) ℂ} (hW : Pᴴ * M * P = signMat N j) : IsUnit P.det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  have h := congrArg Matrix.det hW
  rw [Matrix.det_mul, h0, mul_zero] at h
  exact det_signMat_ne_zero N j h.symm

/- English proof (translation)
Establish `hu` using `isUnit_det_of_witt hW`. Establish `hx : x = P *ᵥ (P⁻¹ *ᵥ x)`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]`. Establish `hy : y = P *ᵥ (P⁻¹ *ᵥ y)`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]`.

Generalize the expression as in `P⁻¹ *ᵥ x = a at hx ⊢`. Generalize the expression as in `P⁻¹ *ᵥ y = b at hy ⊢`. Substitute `hx hy` using the available equality. Rewrite using `[Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hW]`.
-/
theorem form_witt {M P : Matrix (Fin N) (Fin N) ℂ} (hW : Pᴴ * M * P = signMat N j) (x y : Fin N → ℂ) :
    star x ⬝ᵥ (M *ᵥ y) = star (P⁻¹ *ᵥ x) ⬝ᵥ (signMat N j *ᵥ (P⁻¹ *ᵥ y)) := by
  have hu := isUnit_det_of_witt hW
  have hx : x = P *ᵥ (P⁻¹ *ᵥ x) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  have hy : y = P *ᵥ (P⁻¹ *ᵥ y) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  generalize P⁻¹ *ᵥ x = a at hx ⊢
  generalize P⁻¹ *ᵥ y = b at hy ⊢
  subst hx hy
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hW]

/- English proof (translation)
Establish `h1 : ‖star a ⬝ᵥ (signMat N j *ᵥ b)‖ ≤ ∑ c, ‖a c‖ * ‖b c‖`. Simplify using `only [signMat, dotProduct, Matrix.mulVec_diagonal]`. Use `(norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun c _ => ?_))` and prove the remaining obligations. Simplify using `only [Pi.star_apply, norm_mul, norm_star]`. Apply the tactic sequence `split_ifs <;> simp`.

Conclude with `h1.trans (Real.sum_mul_le_sqrt_mul_sqrt _ _ _)`.
-/
theorem norm_sign_form_le (a b : Fin N → ℂ) :
    ‖star a ⬝ᵥ (signMat N j *ᵥ b)‖ ≤ Real.sqrt (∑ c, ‖a c‖ ^ 2) * Real.sqrt (∑ c, ‖b c‖ ^ 2) := by
  have h1 : ‖star a ⬝ᵥ (signMat N j *ᵥ b)‖ ≤ ∑ c, ‖a c‖ * ‖b c‖ := by
    simp only [signMat, dotProduct, Matrix.mulVec_diagonal]
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun c _ => ?_))
    simp only [Pi.star_apply, norm_mul, norm_star]
    split_ifs <;> simp
  exact h1.trans (Real.sum_mul_le_sqrt_mul_sqrt _ _ _)

/- English proof (translation)
Set `e : Ψ × Bool → (Em →+* ℂ)` to `fun p => if p.2 then (starRingEnd ℂ).comp (A.emb p.1) else A.emb p.1`. Establish `cc : ∀ σ : Em →+* ℂ, (starRingEnd ℂ).comp ((starRingEnd ℂ).comp σ) = σ`. Introduce `σ`. Use extensionality with `x`. Simplify using the standard rewrite rules.

Establish `key : ∀ τ τ', A.emb τ ≠ (starRingEnd ℂ).comp (A.emb τ')`. Introduce `τ τ' h`. Use `(A.cmType (A.emb τ)).1 ⟨τ, rfl⟩ ⟨τ', ?_⟩` and prove the remaining obligations. Rewrite using `[h, cc]`. Establish `he : Function.Bijective e`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨τ, b⟩ ⟨τ', b'⟩ h`. Apply the tactic sequence `cases b <;> cases b' <;> simp only [e, Bool.false_eq_true, if_true, if_false] at h`. Rewrite using `[A.emb_inj h]`. Conclude with `absurd h (key _ _)`.

Conclude with `absurd h.symm (key _ _)`. Establish `h'` using `congrArg (fun f : Em →+* ℂ => (starRingEnd ℂ).comp f) h`. Simplify using `only [cc] at h'`. Rewrite using `[A.emb_inj h']`. Introduce `σ`.

Distinguish the cases in `hσ : ∃ τ, A.emb τ = σ`. Take `⟨τ, rfl⟩` from `hσ`. Conclude with `⟨(τ, false), rfl⟩`. Take `⟨τ, hτ⟩` from `not_not.mp (mt (A.cmType σ).2 hσ)`. Use `⟨(τ, true), ?_⟩` and prove the remaining obligations.

Simplify using `only [e, if_true]`. Rewrite using `[hτ, cc]`. Rewrite using `[← he.sum_comp, Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[Fintype.sum_bool]`.

Simplify using `only [e, if_true, Bool.false_eq_true, if_false, add_comm]`.
-/
theorem sum_embeddings (A : HermDatum Em Ψ N j) (g : (Em →+* ℂ) → ℝ) :
    ∑ σ : Em →+* ℂ, g σ = ∑ τ, (g (A.emb τ) + g ((starRingEnd ℂ).comp (A.emb τ))) := by
  let e : Ψ × Bool → (Em →+* ℂ) := fun p => if p.2 then (starRingEnd ℂ).comp (A.emb p.1) else A.emb p.1
  have cc : ∀ σ : Em →+* ℂ, (starRingEnd ℂ).comp ((starRingEnd ℂ).comp σ) = σ := by
    intro σ; ext x; simp
  have key : ∀ τ τ', A.emb τ ≠ (starRingEnd ℂ).comp (A.emb τ') := by
    intro τ τ' h
    refine (A.cmType (A.emb τ)).1 ⟨τ, rfl⟩ ⟨τ', ?_⟩
    rw [h, cc]
  have he : Function.Bijective e := by
    constructor
    · rintro ⟨τ, b⟩ ⟨τ', b'⟩ h
      cases b <;> cases b' <;> simp only [e, Bool.false_eq_true, if_true, if_false] at h
      · rw [A.emb_inj h]
      · exact absurd h (key _ _)
      · exact absurd h.symm (key _ _)
      · have h' := congrArg (fun f : Em →+* ℂ => (starRingEnd ℂ).comp f) h
        simp only [cc] at h'
        rw [A.emb_inj h']
    · intro σ
      by_cases hσ : ∃ τ, A.emb τ = σ
      · obtain ⟨τ, rfl⟩ := hσ
        exact ⟨(τ, false), rfl⟩
      · obtain ⟨τ, hτ⟩ := not_not.mp (mt (A.cmType σ).2 hσ)
        refine ⟨(τ, true), ?_⟩
        simp only [e, if_true]
        rw [hτ, cc]
  rw [← he.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Fintype.sum_bool]
  simp only [e, if_true, Bool.false_eq_true, if_false, add_comm]

/- English proof (translation)
The claim follows from `|((Algebra.trace ℚ Em x : ℚ) : ℝ)| ≤ ∑ τ, 2 * ‖A.emb τ x‖ := by have htr : ((Algebra.trace ℚ Em x : ℚ) : ℂ) = ∑ σ : Em →+* ℂ, σ x := by have h := trace_eq_sum_embeddings (K := ℚ) (L := Em) (E := ℂ) (x := x) rw [eq_ratCast (algebraMap ℚ ℂ)] at h rw [h] exact (Fintype.sum_equiv (Ri …`.
-/
theorem abs_trace_le (A : HermDatum Em Ψ N j) (x : Em) :
    |((Algebra.trace ℚ Em x : ℚ) : ℝ)| ≤ ∑ τ, 2 * ‖A.emb τ x‖ := by
  have htr : ((Algebra.trace ℚ Em x : ℚ) : ℂ) = ∑ σ : Em →+* ℂ, σ x := by
    have h := trace_eq_sum_embeddings (K := ℚ) (L := Em) (E := ℂ) (x := x)
    rw [eq_ratCast (algebraMap ℚ ℂ)] at h
    rw [h]
    exact (Fintype.sum_equiv (RingHom.equivRatAlgHom Em ℂ) _ _ (fun _ => rfl)).symm
  have habs : |((Algebra.trace ℚ Em x : ℚ) : ℝ)| = ‖((Algebra.trace ℚ Em x : ℚ) : ℂ)‖ := by
    rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
  rw [habs, htr]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  rw [sum_embeddings A (fun σ => ‖σ x‖)]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp [two_mul]

/- English proof (translation)
The claim follows from `|((trForm Em A.ξ A.H x y : ℚ) : ℝ)| ≤ A.hodgeNorm P x * A.hodgeNorm P y := by set nx : Ψ → ℝ := fun τ => Real.sqrt (∑ c, ‖((P τ)⁻¹ *ᵥ fun a => A.emb τ (x a)) c‖ ^ 2) with hnx set ny : Ψ → ℝ := fun τ => Real.sqrt (∑ c, ‖((P τ)⁻¹ *ᵥ fun a => A.emb τ (y a)) c‖ ^ 2) with hny set s : …`.
-/
theorem abs_trForm_le (A : HermDatum Em Ψ N j) {P : Ψ → Matrix (Fin N) (Fin N) ℂ} (hP : A.IsWittPoint P)
    (x y : Fin N → Em) :
    |((trForm Em A.ξ A.H x y : ℚ) : ℝ)| ≤ A.hodgeNorm P x * A.hodgeNorm P y := by
  set nx : Ψ → ℝ := fun τ => Real.sqrt (∑ c, ‖((P τ)⁻¹ *ᵥ fun a => A.emb τ (x a)) c‖ ^ 2) with hnx
  set ny : Ψ → ℝ := fun τ => Real.sqrt (∑ c, ‖((P τ)⁻¹ *ᵥ fun a => A.emb τ (y a)) c‖ ^ 2) with hny
  set s : Ψ → ℝ := fun τ => Real.sqrt (2 * ‖A.emb τ A.ξ‖) with hs
  have hτ : ∀ τ, ‖A.emb τ (A.ξ * hermForm Em A.H x y)‖ ≤ ‖A.emb τ A.ξ‖ * (nx τ * ny τ) := by
    intro τ
    rw [map_mul, norm_mul, emb_hermForm, form_witt (hP τ)]
    exact mul_le_mul_of_nonneg_left (norm_sign_form_le _ _) (norm_nonneg _)
  have hw : ∀ τ, 2 * (‖A.emb τ A.ξ‖ * (nx τ * ny τ)) = (s τ * nx τ) * (s τ * ny τ) := by
    intro τ
    have h := Real.mul_self_sqrt (by positivity : (0 : ℝ) ≤ 2 * ‖A.emb τ A.ξ‖)
    calc 2 * (‖A.emb τ A.ξ‖ * (nx τ * ny τ))
        = (Real.sqrt (2 * ‖A.emb τ A.ξ‖) * Real.sqrt (2 * ‖A.emb τ A.ξ‖)) * (nx τ * ny τ) := by rw [h]; ring
      _ = (s τ * nx τ) * (s τ * ny τ) := by simp only [hs]; ring
  have hsq : ∀ u : Fin N → Em, ∑ τ, (s τ * Real.sqrt (∑ c, ‖((P τ)⁻¹ *ᵥ fun a => A.emb τ (u a)) c‖ ^ 2)) ^ 2 =
      A.hodgeNormSq P u := by
    intro u
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  calc |((trForm Em A.ξ A.H x y : ℚ) : ℝ)| ≤ ∑ τ, 2 * ‖A.emb τ (A.ξ * hermForm Em A.H x y)‖ := abs_trace_le A _
    _ ≤ ∑ τ, 2 * (‖A.emb τ A.ξ‖ * (nx τ * ny τ)) :=
        Finset.sum_le_sum fun τ _ => mul_le_mul_of_nonneg_left (hτ τ) (by norm_num)
    _ = ∑ τ, (s τ * nx τ) * (s τ * ny τ) := Finset.sum_congr rfl fun τ _ => hw τ
    _ ≤ Real.sqrt (∑ τ, (s τ * nx τ) ^ 2) * Real.sqrt (∑ τ, (s τ * ny τ) ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = A.hodgeNorm P x * A.hodgeNorm P y := by rw [hsq x, hsq y]; rfl

/- English proof (translation)
Establish `h0 : 0 ≤ vr` using `(norm_nonneg _).trans (hc (Classical.choice inferInstance))`. Establish `hsq : A.hodgeNormSq P (c • x) ≤ vr ^ 2 * A.hodgeNormSq P x`. Unfold `HermDatum.hodgeNormSq`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_le_sum fun τ _ => ?_` and prove the remaining obligations.

Establish `hv : ((P τ)⁻¹ *ᵥ fun a => A.emb τ ((c • x) a)) = A.emb τ c • ((P τ)⁻¹ *ᵥ fun a => A.emb τ (x a))`. Rewrite using `[← Matrix.mulVec_smul]`. Use `congr 1`. Use extensionality with `a`. Simplify using `[smul_eq_mul]`.

Establish `hS : ∑ c', ‖(A.emb τ c • ((P τ)⁻¹ *ᵥ fun a => A.emb τ (x a))) c'‖ ^ 2 = ‖A.emb τ c‖ ^ 2 * ∑ c', ‖((P τ)⁻¹ *ᵥ fun a => A.emb τ (x a)) c'‖ ^ 2`. Rewrite using `[Finset.mul_sum]`. Simplify using `[mul_pow]`. Rewrite using `[hv, hS]`. Establish `ht : ‖A.emb τ c‖ ^ 2 ≤ vr ^ 2` using `pow_le_pow_left₀ (norm_nonneg _) (hc _) 2`.

Combine the equalities or inequalities in the displayed calculation. Unfold `HermDatum.hodgeNorm`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem hodgeNorm_smul_le (A : HermDatum Em Ψ N j) (P : Ψ → Matrix (Fin N) (Fin N) ℂ) {vr : ℝ} (c : Em)
    (hc : ∀ σ : Em →+* ℂ, ‖σ c‖ ≤ vr) (x : Fin N → Em) :
    A.hodgeNorm P (c • x) ≤ vr * A.hodgeNorm P x := by
  have h0 : 0 ≤ vr := (norm_nonneg _).trans (hc (Classical.choice inferInstance))
  have hsq : A.hodgeNormSq P (c • x) ≤ vr ^ 2 * A.hodgeNormSq P x := by
    unfold HermDatum.hodgeNormSq
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun τ _ => ?_
    have hv : ((P τ)⁻¹ *ᵥ fun a => A.emb τ ((c • x) a)) =
        A.emb τ c • ((P τ)⁻¹ *ᵥ fun a => A.emb τ (x a)) := by
      rw [← Matrix.mulVec_smul]
      congr 1
      ext a
      simp [smul_eq_mul]
    have hS : ∑ c', ‖(A.emb τ c • ((P τ)⁻¹ *ᵥ fun a => A.emb τ (x a))) c'‖ ^ 2 =
        ‖A.emb τ c‖ ^ 2 * ∑ c', ‖((P τ)⁻¹ *ᵥ fun a => A.emb τ (x a)) c'‖ ^ 2 := by
      rw [Finset.mul_sum]
      simp [mul_pow]
    rw [hv, hS]
    have ht : ‖A.emb τ c‖ ^ 2 ≤ vr ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hc _) 2
    calc 2 * ‖A.emb τ A.ξ‖ * (‖A.emb τ c‖ ^ 2 * ∑ c', ‖((P τ)⁻¹ *ᵥ fun a => A.emb τ (x a)) c'‖ ^ 2)
        = ‖A.emb τ c‖ ^ 2 * (2 * ‖A.emb τ A.ξ‖ * ∑ c', ‖((P τ)⁻¹ *ᵥ fun a => A.emb τ (x a)) c'‖ ^ 2) := by ring
      _ ≤ vr ^ 2 * (2 * ‖A.emb τ A.ξ‖ * ∑ c', ‖((P τ)⁻¹ *ᵥ fun a => A.emb τ (x a)) c'‖ ^ 2) :=
        mul_le_mul_of_nonneg_right ht (by positivity)
  unfold HermDatum.hodgeNorm
  calc Real.sqrt (A.hodgeNormSq P (c • x)) ≤ Real.sqrt (vr ^ 2 * A.hodgeNormSq P x) := Real.sqrt_le_sqrt hsq
    _ = vr * Real.sqrt (A.hodgeNormSq P x) := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq h0]

/- English proof (translation)
Take `⟨κ, _, a, hcard, hli, hbd⟩` from `hvr`. Establish `hvr0 : 0 < vr`. Establish `h1 : 0 < (Real.sqrt vr)⁻¹` using `lt_of_le_of_lt (Real.sqrt_nonneg _) hvs`. Conclude with `Real.sqrt_pos.mp (inv_pos.mp h1)`. Establish `step : ∀ i, trForm Em A.ξ A.H ((a i : Em) • v) w = 0`.

Introduce `i`. Establish `hmem : (a i : Em) • v ∈ A.L` using `A.L.smul_mem (a i) hv`. Take `⟨m, hm⟩` from `(A.selfDual _).1 hmem w hw`. Establish `hlt : |((trForm Em A.ξ A.H ((a i : Em) • v) w : ℚ) : ℝ)| < 1`. Use `lt_of_le_of_lt (abs_trForm_le A hP _ _) ?_` and prove the remaining obligations.

Establish `hnv` using `Real.sqrt_nonneg (A.hodgeNormSq P v)`. Establish `hnw` using `Real.sqrt_nonneg (A.hodgeNormSq P w)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_assoc, ← mul_inv, Real.mul_self_sqrt hvr0.le, mul_inv_cancel₀ hvr0.ne']`. Rewrite `hlt` using `[hm, Rat.cast_intCast]`.

Establish `hm0 : m = 0` using `Int.abs_lt_one_iff.mp (by exact_mod_cast hlt)`. Rewrite using `[hm, hm0, Int.cast_zero]`. Use `set t := hermForm Em A.H v w`. Set `conjQ : Em →ₗ[ℚ] Em` to `((IsCMField.complexConj Em : Em →+* Em).toRatAlgHom).toLinearMap`. Set `φ : Em →ₗ[ℚ] ℚ` to `(Algebra.trace ℚ Em).comp ((LinearMap.mulRight ℚ (A.ξ * t)).comp conjQ)`.

Establish `hφ : ∀ b : Em, φ b = trForm Em A.ξ A.H (b • v) w`. Introduce `b`. Simplify using `only [φ, conjQ, LinearMap.comp_apply, LinearMap.mulRight_apply, AlgHom.toLinearMap_apply, RingHom.toRatAlgHom_apply, trForm, hermForm_smul_left, t]`. Use `congr 1`. Simplify using `only [RingHom.coe_coe]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hspan` using `hli.span_eq_top_of_card_eq_finrank' hcard`. Establish `hφ0 : φ = 0` using `LinearMap.ext_on_range hspan fun i => by rw [hφ, LinearMap.zero_apply]; exact step i`. Assume the negation of the conclusion as `ht`. Establish `hξt : A.ξ * t ≠ 0` using `mul_ne_zero A.ξ_ne ht`.

Establish `h1` using `LinearMap.congr_fun hφ0 (IsCMField.complexConj Em (A.ξ * t)⁻¹)`. Simplify using `only [φ, conjQ, LinearMap.comp_apply, LinearMap.mulRight_apply, AlgHom.toLinearMap_apply, RingHom.toRatAlgHom_apply, LinearMap.zero_apply, RingHom.coe_coe, IsCMField.complexConj_apply_apply, inv_mul_cancel₀ hξt] at h1`. Rewrite `h1` using `[show (1 : Em) = algebraMap ℚ Em 1 from (map_one _).symm, Algebra.trace_algebraMap]`. Simplify using `only [nsmul_eq_mul, mul_one, Nat.cast_eq_zero] at h1`. Conclude with `(Module.finrank_pos (R := ℚ) (M := Em)).ne' h1`.
-/
theorem hermForm_eq_zero_of_short (A : HermDatum Em Ψ N j) {P : Ψ → Matrix (Fin N) (Fin N) ℂ}
    (hP : A.IsWittPoint P) {vr : ℝ} (hvr : IntegralBasisBound Em vr) {v w : Fin N → Em} (hv : v ∈ A.L)
    (hw : w ∈ A.L) (hvs : A.hodgeNorm P v < (Real.sqrt vr)⁻¹) (hws : A.hodgeNorm P w < (Real.sqrt vr)⁻¹) :
    hermForm Em A.H v w = 0 := by
  obtain ⟨κ, _, a, hcard, hli, hbd⟩ := hvr
  have hvr0 : 0 < vr := by
    have h1 : 0 < (Real.sqrt vr)⁻¹ := lt_of_le_of_lt (Real.sqrt_nonneg _) hvs
    exact Real.sqrt_pos.mp (inv_pos.mp h1)
  have step : ∀ i, trForm Em A.ξ A.H ((a i : Em) • v) w = 0 := by
    intro i
    have hmem : (a i : Em) • v ∈ A.L := A.L.smul_mem (a i) hv
    obtain ⟨m, hm⟩ := (A.selfDual _).1 hmem w hw
    have hlt : |((trForm Em A.ξ A.H ((a i : Em) • v) w : ℚ) : ℝ)| < 1 := by
      refine lt_of_le_of_lt (abs_trForm_le A hP _ _) ?_
      have hnv := Real.sqrt_nonneg (A.hodgeNormSq P v)
      have hnw := Real.sqrt_nonneg (A.hodgeNormSq P w)
      calc A.hodgeNorm P ((a i : Em) • v) * A.hodgeNorm P w ≤ vr * A.hodgeNorm P v * A.hodgeNorm P w :=
            mul_le_mul_of_nonneg_right (hodgeNorm_smul_le A P _ (hbd i) v) hnw
        _ < vr * (Real.sqrt vr)⁻¹ * (Real.sqrt vr)⁻¹ :=
            mul_lt_mul'' (mul_lt_mul_of_pos_left hvs hvr0) hws (by positivity) hnw
        _ = 1 := by
            rw [mul_assoc, ← mul_inv, Real.mul_self_sqrt hvr0.le, mul_inv_cancel₀ hvr0.ne']
    rw [hm, Rat.cast_intCast] at hlt
    have hm0 : m = 0 := Int.abs_lt_one_iff.mp (by exact_mod_cast hlt)
    rw [hm, hm0, Int.cast_zero]
  set t := hermForm Em A.H v w
  let conjQ : Em →ₗ[ℚ] Em := ((IsCMField.complexConj Em : Em →+* Em).toRatAlgHom).toLinearMap
  let φ : Em →ₗ[ℚ] ℚ := (Algebra.trace ℚ Em).comp ((LinearMap.mulRight ℚ (A.ξ * t)).comp conjQ)
  have hφ : ∀ b : Em, φ b = trForm Em A.ξ A.H (b • v) w := by
    intro b
    simp only [φ, conjQ, LinearMap.comp_apply, LinearMap.mulRight_apply, AlgHom.toLinearMap_apply,
      RingHom.toRatAlgHom_apply, trForm, hermForm_smul_left, t]
    congr 1
    simp only [RingHom.coe_coe]
    ring
  have hspan := hli.span_eq_top_of_card_eq_finrank' hcard
  have hφ0 : φ = 0 := LinearMap.ext_on_range hspan fun i => by rw [hφ, LinearMap.zero_apply]; exact step i
  by_contra ht
  have hξt : A.ξ * t ≠ 0 := mul_ne_zero A.ξ_ne ht
  have h1 := LinearMap.congr_fun hφ0 (IsCMField.complexConj Em (A.ξ * t)⁻¹)
  simp only [φ, conjQ, LinearMap.comp_apply, LinearMap.mulRight_apply, AlgHom.toLinearMap_apply,
    RingHom.toRatAlgHom_apply, LinearMap.zero_apply, RingHom.coe_coe, IsCMField.complexConj_apply_apply,
    inv_mul_cancel₀ hξt] at h1
  rw [show (1 : Em) = algebraMap ℚ Em 1 from (map_one _).symm, Algebra.trace_algebraMap] at h1
  simp only [nsmul_eq_mul, mul_one, Nat.cast_eq_zero] at h1
  exact (Module.finrank_pos (R := ℚ) (M := Em)).ne' h1

/- English proof (translation)
Establish `right : ∀ v ∈ {v | v ∈ A.L ∧ A.hodgeNorm P v < (Real.sqrt vr)⁻¹}, ∀ y ∈ A.shortSpan P (Real.sqrt vr)⁻¹, hermForm Em A.H v y = 0`. Introduce `v hv y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem w hw => exact hermForm_eq_zero_of_short A hP hvr hv.1 hw.1 hv.2 hw.2`. Consider the case `zero => exact hermForm_zero_right _ _`.

Consider the case `add y y' _ _ h h' => rw [hermForm_add_right, h, h', add_zero]`. Consider the case `smul c y _ h => rw [oSmul_eq, hermForm_smul_right, h, mul_zero]`. Introduce `x hx y hy`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem v hv => exact right v hv y hy`.

Consider the case `zero => exact hermForm_zero_left _ _`. Consider the case `add x x' _ _ h h' => rw [hermForm_add_left, h, h', add_zero]`. Consider the case `smul c x _ h => rw [oSmul_eq, hermForm_smul_left, h, mul_zero]`.
-/
theorem isIso_shortSpan (A : HermDatum Em Ψ N j) {P : Ψ → Matrix (Fin N) (Fin N) ℂ} (hP : A.IsWittPoint P)
    {vr : ℝ} (hvr : IntegralBasisBound Em vr) : A.IsIso (A.shortSpan P (Real.sqrt vr)⁻¹) := by
  have right : ∀ v ∈ {v | v ∈ A.L ∧ A.hodgeNorm P v < (Real.sqrt vr)⁻¹},
      ∀ y ∈ A.shortSpan P (Real.sqrt vr)⁻¹, hermForm Em A.H v y = 0 := by
    intro v hv y hy
    induction hy using Submodule.span_induction with
    | mem w hw => exact hermForm_eq_zero_of_short A hP hvr hv.1 hw.1 hv.2 hw.2
    | zero => exact hermForm_zero_right _ _
    | add y y' _ _ h h' => rw [hermForm_add_right, h, h', add_zero]
    | smul c y _ h => rw [oSmul_eq, hermForm_smul_right, h, mul_zero]
  intro x hx y hy
  induction hx using Submodule.span_induction with
  | mem v hv => exact right v hv y hy
  | zero => exact hermForm_zero_left _ _
  | add x x' _ _ h h' => rw [hermForm_add_left, h, h', add_zero]
  | smul c x _ h => rw [oSmul_eq, hermForm_smul_left, h, mul_zero]

end Herm

/- English proof (translation)
Introduce `z hz _ hvr` and use `isIso_shortSpan D.herm (fun τ => D.per_witt z hz τ) hvr`.
-/
theorem proof (D : FullerData II Ψ K ι Ω E Em) : ShortIsotropic.Statement D :=
  fun z hz _ hvr => isIso_shortSpan D.herm (fun τ => D.per_witt z hz τ) hvr

end ShortIsotropic

namespace ShortIsotropic

/- English proof (translation)
Introduce `_` and use `Gauss.gauss_signature`.
-/
theorem gauss_isWittPoint : Gauss.gaussDatum.IsWittPoint (fun _ => 1) := fun _ => Gauss.gauss_signature

/- English proof (translation)
Use `⟨Fin 2, inferInstance, ![1, ⟨Gauss.ζ, Gauss.ζ_isIntegral⟩], by rw [Fintype.card_fin, Gauss.finrank_Em], ?_, ?_⟩` and prove the remaining obligations. Establish `he : (fun i => ((![1, ⟨Gauss.ζ, Gauss.ζ_isIntegral⟩] : Fin 2 → 𝓞 Gauss.Em) i : Gauss.Em)) = ![1, Gauss.ζ]`. Apply the tactic sequence `ext i; fin_cases i <;> rfl`. Rewrite using `[he, LinearIndependent.pair_iff]`. Introduce `s t hst`.

Simplify using `only [Algebra.smul_def, eq_ratCast, mul_one] at hst`. Establish `h2` using `congrArg (Algebra.trace ℚ Gauss.Em) hst`. Rewrite `h2` using `[Gauss.trace_rep, map_zero]`. Establish `hs : s = 0` using `by linarith`. Use `⟨hs, ?_⟩` and prove the remaining obligations.

Rewrite `hst` using `[hs, Rat.cast_zero, zero_add]`. Use `(mul_eq_zero.mp hst).resolve_right (Gauss.hζ.ne_zero (by norm_num))` as an intermediate fact. Conclude with `this` after adjusting the coercions. Introduce `i σ fin_cases i`. Simplify using the standard rewrite rules.

Use `show ‖σ Gauss.ζ‖ ≤ 1`. Apply the tactic sequence `rcases Gauss.emb_ζ σ with h | h <;> simp [h]`.
-/
theorem gauss_integralBasisBound : IntegralBasisBound Gauss.Em 1 := by
  refine ⟨Fin 2, inferInstance, ![1, ⟨Gauss.ζ, Gauss.ζ_isIntegral⟩],
    by rw [Fintype.card_fin, Gauss.finrank_Em], ?_, ?_⟩
  · have he : (fun i => ((![1, ⟨Gauss.ζ, Gauss.ζ_isIntegral⟩] : Fin 2 → 𝓞 Gauss.Em) i : Gauss.Em)) =
        ![1, Gauss.ζ] := by
      ext i; fin_cases i <;> rfl
    rw [he, LinearIndependent.pair_iff]
    intro s t hst
    simp only [Algebra.smul_def, eq_ratCast, mul_one] at hst
    have h2 := congrArg (Algebra.trace ℚ Gauss.Em) hst
    rw [Gauss.trace_rep, map_zero] at h2
    have hs : s = 0 := by linarith
    refine ⟨hs, ?_⟩
    rw [hs, Rat.cast_zero, zero_add] at hst
    have := (mul_eq_zero.mp hst).resolve_right (Gauss.hζ.ne_zero (by norm_num))
    exact_mod_cast this
  · intro i σ
    fin_cases i
    · simp
    · show ‖σ Gauss.ζ‖ ≤ 1
      rcases Gauss.emb_ζ σ with h | h <;> simp [h]

/- English proof (translation)
Use `⟨⟨fun _ => ⟨0, one_ne_zero⟩, fun f hf => ?_⟩, fun h => h⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `f ∈ mCoordIdeal Line.yLine at hf`. Rewrite `hf` using `[Line.mCoordIdeal_yLine, Ideal.mem_bot]`. Simplify using `[hf]`.
-/
theorem lineFuller_point : (fun _ => (1 : ℂ)) ∈
    mcPts (mCoordIdeal LineFuller.lineFullerZero.y) \ LineFuller.lineFullerZero.Bd := by
  refine ⟨⟨fun _ => ⟨0, one_ne_zero⟩, fun f hf => ?_⟩, fun h => h⟩
  change f ∈ mCoordIdeal Line.yLine at hf
  rw [Line.mCoordIdeal_yLine, Ideal.mem_bot] at hf
  simp [hf]

/- English proof (translation)
The claim follows from `proof _ _ lineFuller_point 1 gauss_integralBasisBound`.
-/
theorem lineFuller_instance :
    LineFuller.lineFullerZero.herm.IsIso (LineFuller.lineFullerZero.herm.shortSpan
      (LineFuller.lineFullerZero.per (fun _ => 1)) (Real.sqrt 1)⁻¹) :=
  proof _ _ lineFuller_point 1 gauss_integralBasisBound

end ShortIsotropic

end GroundTheory.Heights₂.Heights.NineStatements
