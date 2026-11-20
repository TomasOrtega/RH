import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsConjLinearIsometryCompactUnitaryTypeWeylMoStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalizedFockFormPureTensorPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsConjLinearOfGramEqStatement

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

namespace GlobalTheory.TenTypes

/- English proof (translation)
Rewrite using `[Formalism.L2.DIV.fockL_apply, Formalism.L2.DIV.fockS_eq_sum g f (f.support ∪ g.support) Finset.subset_union_right]`. Unfold `Formalism.REAL.fockF`. Rewrite using `[Finset.sum_subset Finset.subset_union_left ?_]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Simplify using `only [Formalism.L2.DIV.mfact]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `m _ hm`. Rewrite `hm` using `[MvPolynomial.mem_support_iff, not_not]`. Simplify using `[hm]`.
-/
theorem fockF_eq_fockL {σ : Type} (f g : MvPolynomial σ ℂ) : Formalism.REAL.fockF f g = Formalism.L2.DIV.fockL g f := by
  classical
  rw [Formalism.L2.DIV.fockL_apply,
    Formalism.L2.DIV.fockS_eq_sum g f (f.support ∪ g.support) Finset.subset_union_right]
  unfold Formalism.REAL.fockF
  rw [Finset.sum_subset Finset.subset_union_left ?_]
  · refine Finset.sum_congr rfl fun m _ => ?_
    simp only [Formalism.L2.DIV.mfact]
    ring
  · intro m _ hm
    rw [MvPolynomial.mem_support_iff, not_not] at hm
    simp [hm]

/- English proof (translation)
Rewrite using `[fockF_eq_fockL g f, Formalism.L2.DIV.fockL_apply]`. Unfold `Formalism.REAL.fockF Formalism.L2.DIV.fockS`. Rewrite using `[star_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Simplify using `only [Formalism.L2.DIV.mfact, star_mul', star_star, star_natCast]`.
-/
private theorem star_fockF_comm {σ : Type} (f g : MvPolynomial σ ℂ) :
    star (Formalism.REAL.fockF f g) = Formalism.REAL.fockF g f := by
  rw [fockF_eq_fockL g f, Formalism.L2.DIV.fockL_apply]
  unfold Formalism.REAL.fockF Formalism.L2.DIV.fockS
  rw [star_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [Formalism.L2.DIV.mfact, star_mul', star_star, star_natCast]

/- English proof (translation)
Unfold `nfAll`. Rewrite using `[fockF_eq_fockL (p + p') q, map_add, ← fockF_eq_fockL p q, ← fockF_eq_fockL p' q, add_div]`.
-/
theorem nfAll_add_left {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (p p' q : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    nfAll lam (p + p') q = nfAll lam p q + nfAll lam p' q := by
  unfold nfAll
  rw [fockF_eq_fockL (p + p') q, map_add, ← fockF_eq_fockL p q, ← fockF_eq_fockL p' q, add_div]

/- English proof (translation)
Unfold `nfAll`. Rewrite using `[fockF_eq_fockL (c • p) q, map_smul, ← fockF_eq_fockL p q, smul_eq_mul, mul_div_assoc]`.
-/
theorem nfAll_smul_left {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (c : ℂ) (p q : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    nfAll lam (c • p) q = c * nfAll lam p q := by
  unfold nfAll
  rw [fockF_eq_fockL (c • p) q, map_smul, ← fockF_eq_fockL p q, smul_eq_mul, mul_div_assoc]

/- English proof (translation)
Unfold `nfAll`. Rewrite using `[← starRingEnd_apply, map_div₀, map_prod]`. Simplify using `only [starRingEnd_apply, star_fockF_comm]`.
-/
theorem nfAll_symm {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (p q : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    nfAll lam q p = star (nfAll lam p q) := by
  unfold nfAll
  rw [← starRingEnd_apply, map_div₀, map_prod]
  simp only [starRingEnd_apply, star_fockF_comm]

/- English proof (translation)
Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a => simp [Formalism.GradedWeylDivisibility.rowAct]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p v hp`. Establish `hX : MvPolynomial.eval (fun w : Fin n × Fin n => x w.1 w.2) (Formalism.GradedWeylDivisibility.rowAct ℂ g (MvPolynomial.X v)) = (g * x) v.1 v.2`.

Simplify using `[Formalism.GradedWeylDivisibility.rowAct, Matrix.mul_apply]`. Simplify using `only [map_mul, hp, hX, MvPolynomial.eval_X]`.
-/
theorem eval_rowAct {n : ℕ} (g x : Matrix (Fin n) (Fin n) ℂ) (p : MvPolynomial (Fin n × Fin n) ℂ) :
    MvPolynomial.eval (fun v : Fin n × Fin n => x v.1 v.2) (Formalism.GradedWeylDivisibility.rowAct ℂ g p) =
      MvPolynomial.eval (fun v : Fin n × Fin n => (g * x) v.1 v.2) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [Formalism.GradedWeylDivisibility.rowAct]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    have hX : MvPolynomial.eval (fun w : Fin n × Fin n => x w.1 w.2)
        (Formalism.GradedWeylDivisibility.rowAct ℂ g (MvPolynomial.X v)) = (g * x) v.1 v.2 := by
      simp [Formalism.GradedWeylDivisibility.rowAct, Matrix.mul_apply]
    simp only [map_mul, hp, hX, MvPolynomial.eval_X]

/- English proof (translation)
Establish `hmm : mᴴ * m = 1`. Use `Matrix.mem_unitaryGroup_iff'.mp hm` as an intermediate fact. Rewrite `this` using `[Matrix.star_eq_conjTranspose]`. Then use the resulting hypothesis. Establish `hdet : m.det ≠ 0`. Use `congrArg Matrix.det hmm` as an intermediate fact.

Rewrite `this` using `[Matrix.det_mul, Matrix.det_one]`. Conclude with `right_ne_zero_of_mul_eq_one this`. Establish `key : o⁻¹ * a = m * (o⁻¹ * b)`. Rewrite using `[hab]`. Simplify using `only [Matrix.mul_assoc]`.

Rewrite using `[← Matrix.mul_assoc o⁻¹ o, Matrix.nonsing_inv_mul o ho, Matrix.one_mul]`. Rewrite using `[key, Matrix.det_mul, MvPolynomial.smul_eq_C_mul, MvPolynomial.eval_mul, MvPolynomial.eval_C, eval_rowAct mᴴ (m * (o⁻¹ * b)) p, ← Matrix.mul_assoc mᴴ m, hmm, Matrix.one_mul, mul_zpow, _root_.zpow_neg]`. Establish `e : m.det ^ s * (m.det ^ s)⁻¹ = 1` using `mul_inv_cancel₀ (zpow_ne_zero s hdet)`. Take the linear combination `((o⁻¹ * b).det ^ s * MvPolynomial.eval (fun v : Fin n × Fin n => (o⁻¹ * b) v.1 v.2) p) * e`.
-/
theorem factor_eq {n : ℕ} (m o a b : Matrix (Fin n) (Fin n) ℂ) (hm : m ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (ho : IsUnit o.det) (s : ℤ) (p : MvPolynomial (Fin n × Fin n) ℂ) (hab : a = o * m * o⁻¹ * b) :
    (o⁻¹ * a).det ^ s * MvPolynomial.eval (fun v : Fin n × Fin n => (o⁻¹ * a) v.1 v.2)
        ((m.det ^ (-s)) • Formalism.GradedWeylDivisibility.rowAct ℂ mᴴ p) =
      (o⁻¹ * b).det ^ s * MvPolynomial.eval (fun v : Fin n × Fin n => (o⁻¹ * b) v.1 v.2) p := by
  have hmm : mᴴ * m = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.mp hm
    rwa [Matrix.star_eq_conjTranspose] at this
  have hdet : m.det ≠ 0 := by
    have := congrArg Matrix.det hmm
    rw [Matrix.det_mul, Matrix.det_one] at this
    exact right_ne_zero_of_mul_eq_one this
  have key : o⁻¹ * a = m * (o⁻¹ * b) := by
    rw [hab]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc o⁻¹ o, Matrix.nonsing_inv_mul o ho, Matrix.one_mul]
  rw [key, Matrix.det_mul, MvPolynomial.smul_eq_C_mul, MvPolynomial.eval_mul, MvPolynomial.eval_C,
    eval_rowAct mᴴ (m * (o⁻¹ * b)) p, ← Matrix.mul_assoc mᴴ m, hmm, Matrix.one_mul, mul_zpow, _root_.zpow_neg]
  have e : m.det ^ s * (m.det ^ s)⁻¹ = 1 := mul_inv_cancel₀ (zpow_ne_zero s hdet)
  linear_combination
    ((o⁻¹ * b).det ^ s * MvPolynomial.eval (fun v : Fin n × Fin n => (o⁻¹ * b) v.1 v.2) p) * e

/- English proof (translation)
Introduce `ι _ k n h lam u hu Vl _ _ πl hπ W _ _ tens htens hspan`. Establish `hj` using `fun τ => GlobalTheory.T.exists_conjLinear_isometry_compact_unitary_type_weyl_module k n h (lam τ) (u τ) (hu τ) (Vl τ) (πl τ) (hπ τ)`. Use `choose j hjmem hjonto hjnorm hjeq using hj`. Take `⟨hten, hdef, hfn⟩` from `GlobalTheory.T.normalizedFockForm_pureTensor_properties ι n lam`. Take `⟨Jp, hJa, hJn⟩` from `GlobalTheory.T.exists_conjLinear_of_gram_eq' W (MvPolynomial (ι × Fin n × Fin n) ℂ) (nfAll lam) (∀ τ, Vl τ) tens (fun x => ten fun τ => j τ (x τ)) (nfAll_add_left lam) (nfAll_smul_left lam) (nfAll_symm lam) hdef hspan (fun x x' => by show nfAll lam (ten fun τ => j τ (x' τ)) (ten …`.

Rewrite using `[hten, htens]`. Conclude with `Finset.prod_congr rfl fun τ _ => hjnorm τ (x τ) (x' τ))`. Establish `hall : ∀ ξ : W, ξ ∈ Submodule.span ℂ (Set.range tens)` using `fun ξ => by`. Rewrite using `[hspan]`. Conclude with `Submodule.mem_top`.

Use `⟨Jp, ?_, ?_, hJn, ?_⟩` and prove the remaining obligations. Establish `hle : Submodule.span ℂ (Set.range tens) ≤ (CSpan lam).comap Jp`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨x, rfl⟩`. Use `show Jp (tens x) ∈ CSpan lam`.

Rewrite using `[hJa x]`. Conclude with `Submodule.subset_span ⟨fun τ => j τ (x τ), fun τ => hjmem τ (x τ), rfl⟩`. Introduce `ξ`. Conclude with `hle (hall ξ)`. Introduce `p hp`.

Unfold `CSpan at hp`. Proceed by induction on `hp using Submodule.span_induction with`. Consider the case `mem p hp`. Take `⟨f, hf, rfl⟩` from `hp`. Use `choose x hx using fun τ => hjonto τ (f τ) (hf τ)`.

Use `⟨tens x, ?_⟩` and prove the remaining obligations. Rewrite using `[hJa x]`. Use `show (ten fun τ => j τ (x τ)) = ten f`. Use `congr 1`. Use function extensionality and compare the values at `τ`.

Conclude with `hx τ`. Consider the case `zero => exact ⟨0, map_zero Jp⟩`. Consider the case `add p q _ _ hp hq`. Take `⟨ξ, rfl⟩` from `hp`. Take `⟨η, rfl⟩` from `hq`.

Conclude with `⟨ξ + η, map_add Jp ξ η⟩`. Consider the case `smul c p _ hp`. Take `⟨ξ, rfl⟩` from `hp`. Use `⟨(starRingEnd ℂ c) • ξ, ?_⟩` and prove the remaining obligations. Rewrite using `[map_smulₛₗ, starRingEnd_self_apply]`.

Introduce `m hm A hA G o ho ξ y y' hy`. Proceed by induction on `hall ξ using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨x, rfl⟩` from `hz`. Rewrite using `[hA x, hJa, hJa, hfn, hfn]`.

Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[hjeq τ (m τ) (hm τ) (x τ)]`. Conclude with `factor_eq (m τ) (o τ) (y.1 τ) (y'.1 τ) (hm τ) (ho τ) (shiftOf lam τ) (j τ (x τ)) (hy τ)`. Consider the case `zero => simp`. Consider the case `add z w _ _ hz hw => simp only [map_add, Pi.add_apply, hz, hw]`.

Consider the case `smul c z _ hz => simp only [map_smul, map_smulₛₗ, Pi.smul_apply, smul_eq_mul, hz]`.
-/
theorem tensor_dict : ∀ (ι : Type) [Fintype ι] (k n : ℕ) (h : k = n) (lam : ι → DomWeight n) (u : ι → Fin k → ℝ), (∀ τ (i : Fin k), u τ i = ((lam τ).w (Fin.cast h i) : ℝ) + ((rhoVec k i : ℚ) : ℝ)) → ∀ (Vl : ι → Type) [∀ τ, NormedAddCommGroup (Vl τ)] [∀ τ, InnerProductSpace ℂ (Vl τ)] (πl : ∀ τ, Matrix (Fin k) (Fin k) ℂ → (Vl τ →L[ℂ] Vl τ)), (∀ τ, IsHCTypeU k (u τ) (πl τ)) → ∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (tens : (∀ τ, Vl τ) → W), (∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ τ, ⟪x τ, y τ⟫_ℂ) → Submodule.span ℂ (Set.range tens) = ⊤ → ∃ Jp : W →ₗ⋆[ℂ] MvPolynomial (ι × Fin n × Fin n) ℂ, (∀ ξ, Jp ξ ∈ CSpan lam) ∧ (∀ p ∈ CSpan lam, ∃ ξ, Jp ξ = p) ∧ (∀ ξ η, nfAll lam (Jp η) (Jp ξ) = ⟪η, ξ⟫_ℂ) ∧ ∀ (m : ι → Matrix (Fin n) (Fin n) ℂ), (∀ τ, m τ ∈ Matrix.unitaryGroup (Fin n) ℂ) → ∀ A : W →L[ℂ] W, (∀ x, A (tens x) = tens (fun τ => πl τ ((m τ).submatrix (Fin.cast h) (Fin.cast h)) (x τ))) → ∀ (G o : ι → Matrix (Fin n) (Fin n) ℂ), (∀ τ, IsUnit (o τ).det) → ∀ (ξ : W) (y y' : Frames G), IsTr (fun τ => o τ * m τ * (o τ)⁻¹) y' y → fnOf G (shiftOf lam) (fun τ => (o τ)⁻¹) (Jp (A ξ)) y = fnOf G (shiftOf lam) (fun τ => (o τ)⁻¹) (Jp ξ) y' := by
  intro ι _ k n h lam u hu Vl _ _ πl hπ W _ _ tens htens hspan
  have hj := fun τ => GlobalTheory.T.exists_conjLinear_isometry_compact_unitary_type_weyl_module k n h (lam τ) (u τ) (hu τ) (Vl τ) (πl τ) (hπ τ)
  choose j hjmem hjonto hjnorm hjeq using hj
  obtain ⟨hten, hdef, hfn⟩ := GlobalTheory.T.normalizedFockForm_pureTensor_properties ι n lam
  obtain ⟨Jp, hJa, hJn⟩ := GlobalTheory.T.exists_conjLinear_of_gram_eq' W (MvPolynomial (ι × Fin n × Fin n) ℂ) (nfAll lam)
    (∀ τ, Vl τ) tens (fun x => ten fun τ => j τ (x τ)) (nfAll_add_left lam) (nfAll_smul_left lam)
    (nfAll_symm lam) hdef hspan (fun x x' => by
      show nfAll lam (ten fun τ => j τ (x' τ)) (ten fun τ => j τ (x τ)) = _
      rw [hten, htens]
      exact Finset.prod_congr rfl fun τ _ => hjnorm τ (x τ) (x' τ))
  have hall : ∀ ξ : W, ξ ∈ Submodule.span ℂ (Set.range tens) := fun ξ => by
    rw [hspan]; exact Submodule.mem_top
  refine ⟨Jp, ?_, ?_, hJn, ?_⟩
  · have hle : Submodule.span ℂ (Set.range tens) ≤ (CSpan lam).comap Jp := by
      rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      show Jp (tens x) ∈ CSpan lam
      rw [hJa x]
      exact Submodule.subset_span ⟨fun τ => j τ (x τ), fun τ => hjmem τ (x τ), rfl⟩
    intro ξ
    exact hle (hall ξ)
  · intro p hp
    unfold CSpan at hp
    induction hp using Submodule.span_induction with
    | mem p hp =>
      obtain ⟨f, hf, rfl⟩ := hp
      choose x hx using fun τ => hjonto τ (f τ) (hf τ)
      refine ⟨tens x, ?_⟩
      rw [hJa x]
      show (ten fun τ => j τ (x τ)) = ten f
      congr 1
      funext τ
      exact hx τ
    | zero => exact ⟨0, map_zero Jp⟩
    | add p q _ _ hp hq =>
      obtain ⟨ξ, rfl⟩ := hp
      obtain ⟨η, rfl⟩ := hq
      exact ⟨ξ + η, map_add Jp ξ η⟩
    | smul c p _ hp =>
      obtain ⟨ξ, rfl⟩ := hp
      refine ⟨(starRingEnd ℂ c) • ξ, ?_⟩
      rw [map_smulₛₗ, starRingEnd_self_apply]
  · intro m hm A hA G o ho ξ y y' hy
    induction hall ξ using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, rfl⟩ := hz
      rw [hA x, hJa, hJa, hfn, hfn]
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [hjeq τ (m τ) (hm τ) (x τ)]
      exact factor_eq (m τ) (o τ) (y.1 τ) (y'.1 τ) (hm τ) (ho τ) (shiftOf lam τ) (j τ (x τ)) (hy τ)
    | zero => simp
    | add z w _ _ hz hw => simp only [map_add, Pi.add_apply, hz, hw]
    | smul c z _ hz => simp only [map_smul, map_smulₛₗ, Pi.smul_apply, smul_eq_mul, hz]

end GlobalTheory.TenTypes
