import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.WittIso

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E}

/- English proof (translation)
Simplify using `[form, add_dotProduct]`.
-/
theorem form_add_left (x x' y : Fin n → E) : form σ J (x + x') y = form σ J x y + form σ J x' y := by
  simp [form, add_dotProduct]

/- English proof (translation)
Simplify using `[form, smul_dotProduct]`.
-/
theorem form_smul_left (c : E) (x y : Fin n → E) : form σ J (c • x) y = c * form σ J x y := by
  simp [form, smul_dotProduct]

/- English proof (translation)
Establish `: (fun i => σ ((y + y') i)) = (fun i => σ (y i)) + fun i => σ (y' i)` using `by ext i; simp`. Simplify using `only [form, this, Matrix.mulVec_add, dotProduct_add]`.
-/
theorem form_add_right (x y y' : Fin n → E) : form σ J x (y + y') = form σ J x y + form σ J x y' := by
  have : (fun i => σ ((y + y') i)) = (fun i => σ (y i)) + fun i => σ (y' i) := by ext i; simp
  simp only [form, this, Matrix.mulVec_add, dotProduct_add]

/- English proof (translation)
Establish `: (fun i => σ ((c • y) i)) = σ c • fun i => σ (y i)` using `by ext i; simp`. Simplify using `only [form, this, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]`.
-/
theorem form_smul_right (c : E) (x y : Fin n → E) : form σ J x (c • y) = σ c * form σ J x y := by
  have : (fun i => σ ((c • y) i)) = σ c • fun i => σ (y i) := by ext i; simp
  simp only [form, this, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

/- English proof (translation)
Simplify using `only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← hJ j i]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem form_symm (hσ : ∀ z, σ (σ z) = z) (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin n → E) :
    form σ J y x = σ (form σ J x y) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← hJ j i]; ring

/- English proof (translation)
Establish `: (fun i => σ ((g *ᵥ y) i)) = g.map σ *ᵥ fun i => σ (y i)`. Use extensionality with `i`. Conclude with `RingHom.map_mulVec σ.toRingHom g y i`. Simplify using `only [form, this, Matrix.mulVec_mulVec]`. Rewrite using `[Matrix.mul_assoc]`.

Use `conv_rhs => rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]`.
-/
theorem form_mulVec (g : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    form σ J (g *ᵥ x) (g *ᵥ y) = form σ (gᵀ * J * g.map σ) x y := by
  have : (fun i => σ ((g *ᵥ y) i)) = g.map σ *ᵥ fun i => σ (y i) := by
    ext i; exact RingHom.map_mulVec σ.toRingHom g y i
  simp only [form, this, Matrix.mulVec_mulVec]
  rw [Matrix.mul_assoc]
  conv_rhs => rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

end GlobalTheory.WittIso

namespace GlobalTheory.WittIso

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E}

/- English proof (translation)
Establish `: (fun k => σ ((Pi.single j (1 : E) : Fin n → E) k)) = Pi.single j 1`. Apply the tactic sequence `ext k; by_cases h : k = j <;> simp [h]`. Simplify using `[form, this]`.
-/
theorem form_single (i j : Fin n) : form σ J (Pi.single i 1) (Pi.single j 1) = J i j := by
  have : (fun k => σ ((Pi.single j (1 : E) : Fin n → E) k)) = Pi.single j 1 := by
    ext k; by_cases h : k = j <;> simp [h]
  simp [form, this]

/- English proof (translation)
Use extensionality with `i j`. Use `h (Pi.single i 1) (Pi.single j 1)` as an intermediate fact. Rewrite `this` using `[form_mulVec, form_single, form_single]`. Then use the resulting hypothesis.
-/
theorem unitary_of_form (g : Matrix (Fin n) (Fin n) E) (h : ∀ x y, form σ J (g *ᵥ x) (g *ᵥ y) = form σ J x y) :
    gᵀ * J * g.map σ = J := by
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  rwa [form_mulVec, form_single, form_single] at this

/- English proof (translation)
Use `set c := form σ J a b with hcdef`. Establish `hc' : σ c ≠ 0` using `(map_ne_zero σ).2 hab`. Establish `hba : form σ J b a = σ c` using `form_symm hσ hJ a b`. Use `set la : Fin n → E := J *ᵥ fun i => σ (a i)`. Use `set lb : Fin n → E := J *ᵥ fun i => σ (b i)`.

Use `set g : Matrix (Fin n) (Fin n) E := 1 + Matrix.vecMulVec a (c⁻¹ • (la - lb)) + Matrix.vecMulVec b (c⁻¹ • lb - (σ c)⁻¹ • la) with hgdef`. Establish `hg : ∀ z, g *ᵥ z = z + (c⁻¹ * (form σ J z a - form σ J z b)) • a + (c⁻¹ * form σ J z b - (σ c)⁻¹ * form σ J z a) • b`. Introduce `z`. Rewrite using `[hgdef, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec, Matrix.vecMulVec_mulVec]`. Use extensionality with `i`.

Simplify using `[form, la, lb, dotProduct_comm _ z, dotProduct_sub, dotProduct_smul, sub_dotProduct, smul_dotProduct]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨g, unitary_of_form g fun z z' => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hg, hg]`. Simplify using `only [form_add_left, form_add_right, form_smul_left, form_smul_right, ha, hb, hba, form_symm hσ hJ z' a, form_symm hσ hJ z' b, map_mul, map_sub, map_inv₀, hσ]`.

Rewrite using `[← hcdef]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hg, ha, ← hcdef]`. Establish `h1 : c⁻¹ * (0 - c) = -1` using `by rw [zero_sub, mul_neg, inv_mul_cancel₀ hab]`.

Establish `h2 : c⁻¹ * c - (σ c)⁻¹ * 0 = 1` using `by rw [mul_zero, sub_zero, inv_mul_cancel₀ hab]`. Rewrite using `[h1, h2]`. Simplify using the standard rewrite rules.
-/
theorem exists_swap (hσ : ∀ z, σ (σ z) = z) (hJ : ∀ i j, σ (J j i) = J i j) {a b : Fin n → E}
    (ha : form σ J a a = 0) (hb : form σ J b b = 0) (hab : form σ J a b ≠ 0) :
    ∃ g : Matrix (Fin n) (Fin n) E, gᵀ * J * g.map σ = J ∧ g *ᵥ a = b := by
  set c := form σ J a b with hcdef
  have hc' : σ c ≠ 0 := (map_ne_zero σ).2 hab
  have hba : form σ J b a = σ c := form_symm hσ hJ a b
  set la : Fin n → E := J *ᵥ fun i => σ (a i)
  set lb : Fin n → E := J *ᵥ fun i => σ (b i)
  set g : Matrix (Fin n) (Fin n) E :=
    1 + Matrix.vecMulVec a (c⁻¹ • (la - lb)) + Matrix.vecMulVec b (c⁻¹ • lb - (σ c)⁻¹ • la) with hgdef
  have hg : ∀ z, g *ᵥ z = z + (c⁻¹ * (form σ J z a - form σ J z b)) • a +
      (c⁻¹ * form σ J z b - (σ c)⁻¹ * form σ J z a) • b := by
    intro z
    rw [hgdef, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec, Matrix.vecMulVec_mulVec]
    ext i
    simp [form, la, lb, dotProduct_comm _ z, dotProduct_sub, dotProduct_smul, sub_dotProduct, smul_dotProduct]
    ring
  refine ⟨g, unitary_of_form g fun z z' => ?_, ?_⟩
  · rw [hg, hg]
    simp only [form_add_left, form_add_right, form_smul_left, form_smul_right, ha, hb, hba,
      form_symm hσ hJ z' a, form_symm hσ hJ z' b, map_mul, map_sub, map_inv₀, hσ]
    rw [← hcdef]
    field_simp
    ring
  · rw [hg, ha, ← hcdef]
    have h1 : c⁻¹ * (0 - c) = -1 := by rw [zero_sub, mul_neg, inv_mul_cancel₀ hab]
    have h2 : c⁻¹ * c - (σ c)⁻¹ * 0 = 1 := by rw [mul_zero, sub_zero, inv_mul_cancel₀ hab]
    rw [h1, h2]
    simp

end GlobalTheory.WittIso

namespace GlobalTheory.WittIso

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E}

/- English proof (translation)
Establish `hm : (g₂ * g₁).map σ = g₂.map σ * g₁.map σ` using `Matrix.map_mul (f := (σ : E →+* E))`. Rewrite using `[Matrix.transpose_mul, hm]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = J := by rw [h₂, h₁]`.
-/
theorem unitary_mul {g₁ g₂ : Matrix (Fin n) (Fin n) E} (h₁ : g₁ᵀ * J * g₁.map σ = J) (h₂ : g₂ᵀ * J * g₂.map σ = J) :
    (g₂ * g₁)ᵀ * J * (g₂ * g₁).map σ = J := by
  have hm : (g₂ * g₁).map σ = g₂.map σ * g₁.map σ := Matrix.map_mul (f := (σ : E →+* E))
  rw [Matrix.transpose_mul, hm]
  calc g₁ᵀ * g₂ᵀ * J * (g₂.map σ * g₁.map σ) = g₁ᵀ * (g₂ᵀ * J * g₂.map σ) * g₁.map σ := by
        simp only [Matrix.mul_assoc]
    _ = J := by rw [h₂, h₁]

/- English proof (translation)
Introduce `h0`. Establish `hm : (g.map σ).det = σ g.det` using `(RingHom.map_det (σ : E →+* E) g).symm`. Use `congrArg Matrix.det h` as an intermediate fact. Rewrite `this` using `[Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hm, h0]`. Simplify using `at this`.

Conclude with `hJ this.symm`.
-/
theorem det_ne_zero_of_unitary {g : Matrix (Fin n) (Fin n) E} (h : gᵀ * J * g.map σ = J) (hJ : J.det ≠ 0) : g.det ≠ 0 := by
  intro h0
  have hm : (g.map σ).det = σ g.det := (RingHom.map_det (σ : E →+* E) g).symm
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hm, h0] at this
  simp at this
  exact hJ this.symm

/- English proof (translation)
Establish `hsv : (fun i => σ (v i)) ≠ 0`. Introduce `h0`. Apply `hv` to reduce the goal to its premises. Use extensionality with `i`. Use `congrFun h0 i` as an intermediate fact.

Simplify using `using this`. Establish `hJv : J *ᵥ (fun i => σ (v i)) ≠ 0`. Introduce `h0`. Conclude with `hJ (Matrix.exists_mulVec_eq_zero_iff.1 ⟨_, hsv, h0⟩)`. Take `⟨i, hi⟩` from `Function.ne_iff.1 hJv`.

Conclude with `⟨Pi.single i 1, by simpa [form] using hi⟩`.
-/
theorem nondeg_of_det (hJ : J.det ≠ 0) {v : Fin n → E} (hv : v ≠ 0) : ∃ p, form σ J p v ≠ 0 := by
  have hsv : (fun i => σ (v i)) ≠ 0 := by
    intro h0; apply hv; ext i
    have := congrFun h0 i
    simpa using this
  have hJv : J *ᵥ (fun i => σ (v i)) ≠ 0 := by
    intro h0; exact hJ (Matrix.exists_mulVec_eq_zero_iff.1 ⟨_, hsv, h0⟩)
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hJv
  exact ⟨Pi.single i 1, by simpa [form] using hi⟩

/- English proof (translation)
Distinguish the cases in `h : form σ J x x₀ = 0`. Take `⟨p₁, hp₁⟩` from `nondeg_of_det (σ := σ) hdet hx₀`. Take `⟨p₂, hp₂⟩` from `nondeg_of_det (σ := σ) hdet hx`. Establish `: ∃ p, form σ J p x₀ ≠ 0 ∧ form σ J p x ≠ 0`. Distinguish the cases in `h1 : form σ J p₁ x = 0`.

Distinguish the cases in `h2 : form σ J p₂ x₀ = 0`. Conclude with `⟨p₁ + p₂, by simpa [form_add_left, h2] using hp₁, by simpa [form_add_left, h1] using hp₂⟩`. Conclude with `⟨p₂, h2, hp₂⟩`. Conclude with `⟨p₁, hp₁, h1⟩`. Take `⟨p, hpx₀, hpx⟩` from `this`.

Establish `hm : σ (form σ J p x₀) ≠ 0` using `(map_ne_zero σ).2 hpx₀`. Establish `hQ : σ (form σ J p p) = form σ J p p` using `(form_symm hσ hJ p p).symm`. Establish `hx₀x : form σ J x₀ x = 0` using `by rw [form_symm hσ hJ x x₀, h, map_zero]`. Use `set t : E := -form σ J p p / (2 * σ (form σ J p x₀)) with htdef`. Establish `hwx₀ : form σ J (p + t • x₀) x₀ = form σ J p x₀`.

Simplify using `[form_add_left, form_smul_left, hx₀x₀]`. Establish `hwx : form σ J (p + t • x₀) x = form σ J p x`. Simplify using `[form_add_left, form_smul_left, hx₀x]`. Establish `hww : form σ J (p + t • x₀) (p + t • x₀) = 0`. Simplify using `only [form_add_left, form_add_right, form_smul_left, form_smul_right, hx₀x₀, form_symm hσ hJ p x₀]`.

Establish `ht : σ t = -form σ J p p / (2 * form σ J p x₀)`. Rewrite using `[htdef, map_div₀, map_neg, map_mul, hQ, hσ, map_ofNat]`. Rewrite using `[ht, htdef]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Establish `hxw : form σ J x (p + t • x₀) ≠ 0`. Rewrite using `[form_symm hσ hJ, hwx]`. Conclude with `(map_ne_zero σ).2 hpx`. Take `⟨g₁, hg₁, hg₁x⟩` from `exists_swap hσ hJ hxx hww hxw`. Take `⟨g₂, hg₂, hg₂w⟩` from `exists_swap hσ hJ hww hx₀x₀ (by rw [hwx₀]; exact hpx₀)`.

Conclude with `⟨g₂ * g₁, unitary_mul hg₁ hg₂, by rw [← Matrix.mulVec_mulVec, hg₁x, hg₂w]⟩`. Conclude with `exists_swap hσ hJ hxx hx₀x₀ h`.
-/
theorem exists_unitary_isotropic (hσ : ∀ z, σ (σ z) = z) (hJ : ∀ i j, σ (J j i) = J i j) (hdet : J.det ≠ 0)
    {x x₀ : Fin n → E} (hx : x ≠ 0) (hx₀ : x₀ ≠ 0) (hxx : form σ J x x = 0) (hx₀x₀ : form σ J x₀ x₀ = 0) :
    ∃ g : Matrix (Fin n) (Fin n) E, gᵀ * J * g.map σ = J ∧ g *ᵥ x = x₀ := by
  by_cases h : form σ J x x₀ = 0
  · obtain ⟨p₁, hp₁⟩ := nondeg_of_det (σ := σ) hdet hx₀
    obtain ⟨p₂, hp₂⟩ := nondeg_of_det (σ := σ) hdet hx
    have : ∃ p, form σ J p x₀ ≠ 0 ∧ form σ J p x ≠ 0 := by
      by_cases h1 : form σ J p₁ x = 0
      · by_cases h2 : form σ J p₂ x₀ = 0
        · exact ⟨p₁ + p₂, by simpa [form_add_left, h2] using hp₁, by simpa [form_add_left, h1] using hp₂⟩
        · exact ⟨p₂, h2, hp₂⟩
      · exact ⟨p₁, hp₁, h1⟩
    obtain ⟨p, hpx₀, hpx⟩ := this
    have hm : σ (form σ J p x₀) ≠ 0 := (map_ne_zero σ).2 hpx₀
    have hQ : σ (form σ J p p) = form σ J p p := (form_symm hσ hJ p p).symm
    have hx₀x : form σ J x₀ x = 0 := by rw [form_symm hσ hJ x x₀, h, map_zero]
    set t : E := -form σ J p p / (2 * σ (form σ J p x₀)) with htdef
    have hwx₀ : form σ J (p + t • x₀) x₀ = form σ J p x₀ := by
      simp [form_add_left, form_smul_left, hx₀x₀]
    have hwx : form σ J (p + t • x₀) x = form σ J p x := by
      simp [form_add_left, form_smul_left, hx₀x]
    have hww : form σ J (p + t • x₀) (p + t • x₀) = 0 := by
      simp only [form_add_left, form_add_right, form_smul_left, form_smul_right, hx₀x₀, form_symm hσ hJ p x₀]
      have ht : σ t = -form σ J p p / (2 * form σ J p x₀) := by
        rw [htdef, map_div₀, map_neg, map_mul, hQ, hσ, map_ofNat]
      rw [ht, htdef]
      field_simp
      ring
    have hxw : form σ J x (p + t • x₀) ≠ 0 := by
      rw [form_symm hσ hJ, hwx]; exact (map_ne_zero σ).2 hpx
    obtain ⟨g₁, hg₁, hg₁x⟩ := exists_swap hσ hJ hxx hww hxw
    obtain ⟨g₂, hg₂, hg₂w⟩ := exists_swap hσ hJ hww hx₀x₀ (by rw [hwx₀]; exact hpx₀)
    exact ⟨g₂ * g₁, unitary_mul hg₁ hg₂, by rw [← Matrix.mulVec_mulVec, hg₁x, hg₂w]⟩
  · exact exists_swap hσ hJ hxx hx₀x₀ h

end GlobalTheory.WittIso

namespace GlobalTheory.WittIso

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E}

/- English proof (translation)
Take `⟨hrs, A, hA⟩` from `h`. Establish `hU : IsUnit (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1 : Matrix (Fin s) (Fin s) ℂ))`. Rewrite using `[Matrix.isUnit_iff_isUnit_det, Matrix.det_fromBlocks_zero₂₁]`. Simplify using `[Matrix.det_neg]`. Establish `hD` using `Matrix.rank_of_isUnit _ hU`.

Establish `hle : r + s ≤ M.rank`. Establish `h1` using `(Matrix.rank_mul_le_left (Aᵀ * M) (A.map star)).trans (Matrix.rank_mul_le_right Aᵀ M)`. Rewrite `h1` using `[hA, hD]`. Simplify using `using h1`. Introduce `h0`.

Take `⟨v, hv, hMv⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 h0`. Establish `hk : LinearMap.ker M.mulVecLin ≠ ⊥`. Introduce `hb`. Establish `hvk : v ∈ LinearMap.ker M.mulVecLin` using `by simpa using hMv`. Rewrite `hvk` using `[hb]`.

Conclude with `hv (by simpa using hvk)`. Establish `hpos : 0 < Module.finrank ℂ (LinearMap.ker M.mulVecLin)`. Rewrite using `[Nat.pos_iff_ne_zero]`. Introduce `hz`. Conclude with `hk (Submodule.finrank_eq_zero.1 hz)`.

Establish `hrn` using `LinearMap.finrank_range_add_finrank_ker M.mulVecLin`. Establish `hrk : M.rank = Module.finrank ℂ (LinearMap.range M.mulVecLin)` using `rfl`. Simplify using `only [Module.finrank_fin_fun] at hrn`. Use linear arithmetic over natural numbers and integers.
-/
theorem det_ne_zero_of_hasSig {r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  have hU : IsUnit (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1 : Matrix (Fin s) (Fin s) ℂ)) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fromBlocks_zero₂₁]
    simp [Matrix.det_neg]
  have hD := Matrix.rank_of_isUnit _ hU
  have hle : r + s ≤ M.rank := by
    have h1 := (Matrix.rank_mul_le_left (Aᵀ * M) (A.map star)).trans (Matrix.rank_mul_le_right Aᵀ M)
    rw [hA, hD] at h1
    simpa using h1
  intro h0
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have hk : LinearMap.ker M.mulVecLin ≠ ⊥ := by
    intro hb
    have hvk : v ∈ LinearMap.ker M.mulVecLin := by simpa using hMv
    rw [hb] at hvk
    exact hv (by simpa using hvk)
  have hpos : 0 < Module.finrank ℂ (LinearMap.ker M.mulVecLin) := by
    rw [Nat.pos_iff_ne_zero]; intro hz
    exact hk (Submodule.finrank_eq_zero.1 hz)
  have hrn := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  have hrk : M.rank = Module.finrank ℂ (LinearMap.range M.mulVecLin) := rfl
  simp only [Module.finrank_fin_fun] at hrn
  omega

/- English proof (translation)
Set `τ : E →+* ℂ` to `(IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom`. Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[hcm.2.2.2 τ, hcm.2.2.2 τ, star_star]`.
-/
theorem invol_of_cm (hcm : IsCMExt F E σ) (z : E) : σ (σ z) = z := by
  let τ : E →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom
  apply τ.injective
  rw [hcm.2.2.2 τ, hcm.2.2.2 τ, star_star]

/- English proof (translation)
Simplify using `[cA, inclR]`.
-/
theorem inclR_conj (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [cA, inclR]

/- English proof (translation)
Establish `hc : (fun e => cA σ e) ∘ (inclR (F` using `F) (AF F)) = (inclR (F := F) (AF F)) ∘ σ := by`. Use function extensionality and compare the values at `e`. Conclude with `inclR_conj e`. Use `show ((g.map (inclR (F := F) (AF F))))ᵀ * incM F J * (g.map (inclR (F := F) (AF F))).map (cA σ) = incM F J`. Rewrite using `[Matrix.map_map, hc, ← Matrix.map_map, incM, ← Matrix.transpose_map]`.

Rewrite using `[← Matrix.map_mul (f := inclR (F := F) (AF F)), ← Matrix.map_mul (f := inclR (F := F) (AF F)), hg]`.
-/
theorem map_mem_UA {g : Matrix (Fin n) (Fin n) E} (hg : gᵀ * J * g.map σ = J) (hd : g.det ≠ 0) :
    Matrix.GeneralLinearGroup.map (inclR (F := F) (AF F)) (Matrix.GeneralLinearGroup.mkOfDetNeZero g hd) ∈
      UG (cA σ) (incM F J) := by
  have hc : (fun e => cA σ e) ∘ (inclR (F := F) (AF F)) = (inclR (F := F) (AF F)) ∘ σ := by
    funext e; exact inclR_conj e
  show ((g.map (inclR (F := F) (AF F))))ᵀ * incM F J * (g.map (inclR (F := F) (AF F))).map (cA σ) = incM F J
  rw [Matrix.map_map, hc, ← Matrix.map_map, incM, ← Matrix.transpose_map]
  rw [← Matrix.map_mul (f := inclR (F := F) (AF F)), ← Matrix.map_mul (f := inclR (F := F) (AF F)), hg]

end GlobalTheory.WittIso

namespace GlobalTheory.WittIso

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B b a' G G₁ H H' hcfg X om om' htr`. Establish `hσ` using `invol_of_cm htr.base.cm`. Establish `hV` using `htr.geo.hV`. Take `⟨w⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Establish `hdet : G.V.J.det ≠ 0`.

Establish `h1` using `det_ne_zero_of_hasSig (hV.sig w)`. Introduce `h0`. Apply `h1` to reduce the goal to its premises. Establish `h2` using `RingHom.map_det (B.emb w).1 G.V.J`. Rewrite `h2` using `[h0, map_zero]`.

Conclude with `h2.symm`. Establish `hH` using `hcfg.hH`. Establish `hx₀ : H.x ≠ 0`. Introduce `h0`. Establish `h1` using `hH.xy`.

Rewrite `h1` using `[h0]`. Simplify using `[form] at h1`. Use `choose g hg hgx using fun x : {x : Fin (b + 2) → E // x ≠ 0 ∧ form σ G.V.J x x = 0} => exists_unitary_isotropic hσ hV.herm hdet x.2.1 hx₀ x.2.2 hH.xx`. Use `⟨fun x => ⟨_, map_mem_UA (F := F) (hg x) (det_ne_zero_of_unitary (hg x) hdet)⟩, fun x => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Conclude with `Subgroup.mem_subgroupOf.2 ⟨_, rfl⟩`.

Use extensionality with `k show ((g x).map (inclR (F := F) (AF F)) *ᵥ fun i => inclR (F := F) (AF F) (x.1 i)) k = inclR (F := F) (AF F) (H.x k)`. Rewrite using `[← hgx x]`. Conclude with `(RingHom.map_mulVec (inclR (F := F) (AF F)) (g x) x.1 k).symm`.
-/
theorem exists_rational_to_x₀ : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∃ γ : {x : Fin (b + 2) → E // x ≠ 0 ∧ form σ G.V.J x x = 0} → UA σ G.V.J,
      ∀ x, γ x ∈ ratU σ G.V.J ∧ mat (γ x) *ᵥ incV F x.1 = incV F H.x := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hcfg X om om' htr
  have hσ := invol_of_cm htr.base.cm
  have hV := htr.geo.hV
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hdet : G.V.J.det ≠ 0 := by
    have h1 := det_ne_zero_of_hasSig (hV.sig w)
    intro h0
    apply h1
    have h2 := RingHom.map_det (B.emb w).1 G.V.J
    rw [h0, map_zero] at h2
    exact h2.symm
  have hH := hcfg.hH
  have hx₀ : H.x ≠ 0 := by
    intro h0
    have h1 := hH.xy
    rw [h0] at h1
    simp [form] at h1
  choose g hg hgx using fun x : {x : Fin (b + 2) → E // x ≠ 0 ∧ form σ G.V.J x x = 0} =>
    exists_unitary_isotropic hσ hV.herm hdet x.2.1 hx₀ x.2.2 hH.xx
  refine ⟨fun x => ⟨_, map_mem_UA (F := F) (hg x) (det_ne_zero_of_unitary (hg x) hdet)⟩, fun x => ⟨?_, ?_⟩⟩
  · exact Subgroup.mem_subgroupOf.2 ⟨_, rfl⟩
  · ext k
    show ((g x).map (inclR (F := F) (AF F)) *ᵥ fun i => inclR (F := F) (AF F) (x.1 i)) k = inclR (F := F) (AF F) (H.x k)
    rw [← hgx x]
    exact (RingHom.map_mulVec (inclR (F := F) (AF F)) (g x) x.1 k).symm

end GlobalTheory.WittIso
