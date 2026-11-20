import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLevi

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.LeviAdapted

open Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Simplify using `only [form, dotProduct, mulVec, map_sum, map_mul, hσ, hJ, Finset.mul_sum, Finset.sum_neg_distrib, neg_mul, mul_neg, neg_neg]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem form_swap (hσ : ∀ x, σ (σ x) = x) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : ∀ i j, σ (J j i) = -J i j)
    (a b : Fin n → E) : form σ J a b = -σ (form σ J b a) := by
  simp only [form, dotProduct, mulVec, map_sum, map_mul, hσ, hJ, Finset.mul_sum, Finset.sum_neg_distrib, neg_mul, mul_neg, neg_neg]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

/- English proof (translation)
Simplify using `[form, add_dotProduct]`.
-/
theorem form_add_left {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a a' b : Fin n → E) :
    form σ J (a + a') b = form σ J a b + form σ J a' b := by simp [form, add_dotProduct]

/- English proof (translation)
Simplify using `[form, smul_dotProduct]`.
-/
theorem form_smul_left {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (s : E) (a b : Fin n → E) :
    form σ J (s • a) b = s * form σ J a b := by simp [form, smul_dotProduct]

/- English proof (translation)
Set `φ : ((E × (Fin d₁ → E)) × E) →ₗ[E] (Fin d → E)` to `LinearMap.coprod (LinearMap.coprod (LinearMap.toSpanSingleton E _ H'.x) (Matrix.mulVecLin H'.ι)) (LinearMap.toSpanSingleton E _ H'.y)`. Establish `hφ : ∀ p, φ p = p.1.1 • H'.x + H'.ι *ᵥ p.1.2 + p.2 • H'.y` using `fun p => by`. Simplify using `[φ, LinearMap.coprod_apply]`. Establish `hsurj : Function.Surjective φ`. Rewrite using `[← LinearMap.range_eq_top, eq_top_iff, ← hW.lat.span_eq_top, Submodule.span_le]`.

Introduce `z hz`. Take `⟨a, b, u, -, -, -, rfl⟩` from `hA.split z hz`. Conclude with `⟨((a, u), b), hφ _⟩`. Establish `hrk : Module.finrank E ((E × (Fin d₁ → E)) × E) = Module.finrank E (Fin d → E)`. Simplify using `[Module.finrank_prod, hA.rank]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hinj : Function.Injective φ` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrk).2 hsurj`. Use `⟨fun v => ?_, fun u hu => ?_⟩` and prove the remaining obligations. Take `⟨p, rfl⟩` from `hsurj v`. Conclude with `⟨p.1.1, p.2, p.1.2, hφ p⟩`.

Establish `: φ ((0, u), 0) = φ 0` using `by rw [hφ, map_zero]; simp [hu]`. Use `hinj this` as an intermediate fact. Simplify using `using congrArg (fun p => p.1.2) this`.
-/
theorem decomp {B : Base F E} {d d₁ r s : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} (hW : W.IsSkew σ B r s)
    {H' : Plane E d d₁} {i₀ i₁ : ℕ} (hA : H'.IsAdapted σ B W W₁ i₀ i₁) :
    (∀ v : Fin d → E, ∃ (a b : E) (u : Fin d₁ → E), v = a • H'.x + H'.ι *ᵥ u + b • H'.y) ∧
    ∀ u : Fin d₁ → E, H'.ι *ᵥ u = 0 → u = 0 := by
  let φ : ((E × (Fin d₁ → E)) × E) →ₗ[E] (Fin d → E) :=
    LinearMap.coprod (LinearMap.coprod (LinearMap.toSpanSingleton E _ H'.x) (Matrix.mulVecLin H'.ι))
      (LinearMap.toSpanSingleton E _ H'.y)
  have hφ : ∀ p, φ p = p.1.1 • H'.x + H'.ι *ᵥ p.1.2 + p.2 • H'.y := fun p => by
    simp [φ, LinearMap.coprod_apply]
  have hsurj : Function.Surjective φ := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hW.lat.span_eq_top, Submodule.span_le]
    intro z hz
    obtain ⟨a, b, u, -, -, -, rfl⟩ := hA.split z hz
    exact ⟨((a, u), b), hφ _⟩
  have hrk : Module.finrank E ((E × (Fin d₁ → E)) × E) = Module.finrank E (Fin d → E) := by
    simp [Module.finrank_prod, hA.rank]; ring
  have hinj : Function.Injective φ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrk).2 hsurj
  refine ⟨fun v => ?_, fun u hu => ?_⟩
  · obtain ⟨p, rfl⟩ := hsurj v
    exact ⟨p.1.1, p.2, p.1.2, hφ p⟩
  · have : φ ((0, u), 0) = φ 0 := by rw [hφ, map_zero]; simp [hu]
    have := hinj this
    simpa using congrArg (fun p => p.1.2) this

/- English proof (translation)
Take `⟨w⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Establish `h` using `GlobalTheory.LeviUnitary.det_ne_zero_of_hasSig (hW.sig w)`. Rewrite `h` using `[det_smul]`. Establish `h'` using `right_ne_zero_of_mul h`. Introduce `h0`.

Apply `h'` to reduce the goal to its premises. Use `RingHom.map_det (B.emb w).1 W.J` as an intermediate fact. Rewrite `this` using `[h0, map_zero]`. Conclude with `this.symm`.
-/
theorem det_ne_zero {B : Base F E} {d r s : ℕ} {W : Spc F E d} (hW : W.IsSkew σ B r s) : W.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have h := GlobalTheory.LeviUnitary.det_ne_zero_of_hasSig (hW.sig w)
  rw [det_smul] at h
  have h' := right_ne_zero_of_mul h
  intro h0
  apply h'
  have := RingHom.map_det (B.emb w).1 W.J
  rw [h0, map_zero] at this
  exact this.symm

/- English proof (translation)
Take `⟨hdec, hinj⟩` from `decomp hW hA`. Rewrite using `[isUnit_iff_ne_zero]`. Introduce `h0`. Take `⟨w, hw0, hw⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 h0`. Apply `hw0` to reduce the goal to its premises.

Use `set w' : Fin d₁ → E := fun j => σ (w j) with hw'`. Use `set z : Fin d → E := H'.ι *ᵥ w' with hz`. Establish `hσz : (fun i => σ (z i)) = H'.ι.map σ *ᵥ w`. Use function extensionality and compare the values at `i`. Simplify using `[hz, hw', mulVec, dotProduct, map_sum, map_mul, hσ]`.

Establish `hι : ∀ u, form σ W.J (H'.ι *ᵥ u) z = 0`. Introduce `u`. Establish `e : form σ W.J (H'.ι *ᵥ u) z = u ⬝ᵥ (W₁.J *ᵥ w)`. Rewrite using `[form, hσz, ← hA.gram, ← mulVec_mulVec, ← mulVec_mulVec, mulVec_transpose, dotProduct_comm, dotProduct_mulVec, dotProduct_comm]`. Rewrite using `[e, hw, dotProduct_zero]`.

Establish `hx : form σ W.J H'.x z = 0`. Rewrite using `[form_swap hσ hW.skew, (hA.orth w').1, map_zero, neg_zero]`. Establish `hy : form σ W.J H'.y z = 0`. Rewrite using `[form_swap hσ hW.skew, (hA.orth w').2, map_zero, neg_zero]`. Establish `hall : ∀ v, form σ W.J v z = 0`.

Introduce `v`. Take `⟨a, b, u, rfl⟩` from `hdec v`. Rewrite using `[form_add_left, form_add_left, form_smul_left, form_smul_left, hx, hy, hι]`. Simplify using the standard rewrite rules. Establish `hJz : W.J *ᵥ (fun i => σ (z i)) = 0`.

Use function extensionality and compare the values at `i`. Use `hall (Pi.single i 1)` as an intermediate fact. Rewrite `this` using `[form, single_one_dotProduct]`. Conclude with `this`. Establish `hσz0` using `Matrix.eq_zero_of_mulVec_eq_zero (det_ne_zero hW) hJz`.

Establish `hz0 : z = 0`. Use function extensionality and compare the values at `i`. Use `congrArg σ (congrFun hσz0 i)` as an intermediate fact. Simplify `this` using `[hσ]`. Use `hinj w' hz0` as an intermediate fact.

Use function extensionality and compare the values at `j`. Use `congrArg σ (congrFun this j)` as an intermediate fact. Simplify `this` using `[hw', hσ]`.
-/
theorem isUnit_det_low (hσ : ∀ x, σ (σ x) = x) {B : Base F E} {d d₁ r s : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁}
    (hW : W.IsSkew σ B r s) {H' : Plane E d d₁} {i₀ i₁ : ℕ} (hA : H'.IsAdapted σ B W W₁ i₀ i₁) : IsUnit W₁.J.det := by
  obtain ⟨hdec, hinj⟩ := decomp hW hA
  rw [isUnit_iff_ne_zero]
  intro h0
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  apply hw0
  set w' : Fin d₁ → E := fun j => σ (w j) with hw'
  set z : Fin d → E := H'.ι *ᵥ w' with hz
  have hσz : (fun i => σ (z i)) = H'.ι.map σ *ᵥ w := by
    funext i
    simp [hz, hw', mulVec, dotProduct, map_sum, map_mul, hσ]
  have hι : ∀ u, form σ W.J (H'.ι *ᵥ u) z = 0 := by
    intro u
    have e : form σ W.J (H'.ι *ᵥ u) z = u ⬝ᵥ (W₁.J *ᵥ w) := by
      rw [form, hσz, ← hA.gram, ← mulVec_mulVec, ← mulVec_mulVec, mulVec_transpose, dotProduct_comm,
        dotProduct_mulVec, dotProduct_comm]
    rw [e, hw, dotProduct_zero]
  have hx : form σ W.J H'.x z = 0 := by
    rw [form_swap hσ hW.skew, (hA.orth w').1, map_zero, neg_zero]
  have hy : form σ W.J H'.y z = 0 := by
    rw [form_swap hσ hW.skew, (hA.orth w').2, map_zero, neg_zero]
  have hall : ∀ v, form σ W.J v z = 0 := by
    intro v
    obtain ⟨a, b, u, rfl⟩ := hdec v
    rw [form_add_left, form_add_left, form_smul_left, form_smul_left, hx, hy, hι]
    simp
  have hJz : W.J *ᵥ (fun i => σ (z i)) = 0 := by
    funext i
    have := hall (Pi.single i 1)
    rw [form, single_one_dotProduct] at this
    exact this
  have hσz0 := Matrix.eq_zero_of_mulVec_eq_zero (det_ne_zero hW) hJz
  have hz0 : z = 0 := by
    funext i
    have := congrArg σ (congrFun hσz0 i)
    simpa [hσ] using this
  have := hinj w' hz0
  funext j
  have := congrArg σ (congrFun this j)
  simpa [hw', hσ] using this

/- English proof (translation)
Establish `hσ` using `GlobalTheory.LeviTorus.sigma_invol hcm`. Establish `hdet` using `isUnit_det_low hσ hW hA`. Establish `mm : ∀ {k l : ℕ} (A : Matrix (Fin k) (Fin l) E), (A.map σ).map σ = A` using `fun A => by`. Use extensionality with `i j`. Conclude with `hσ _`.

Establish `mul : ∀ {k l p : ℕ} (A : Matrix (Fin k) (Fin l) E) (A' : Matrix (Fin l) (Fin p) E), (A * A').map σ = A.map σ * A'.map σ` using `fun A A' => Matrix.map_mul (f := σ.toRingHom)`. Establish `sk : W.J.map σ = -W.Jᵀ` using `by ext i j; exact hW.skew j i`. Establish `sk₁ : W₁.J.map σ = -W₁.Jᵀ`. Rewrite using `[← hA.gram, mul, mul, mm, sk, transpose_mul, transpose_mul, transpose_transpose]`. Simplify using `[Matrix.mul_assoc, Matrix.transpose_map]`.

Use `set P : Matrix (Fin d₁) (Fin d) E := W₁.J⁻¹ * (H'.ιᵀ * W.J) with hP`. Establish `h2 : H'.ιᵀ * W.J = W₁.J * P` using `by rw [hP, Matrix.mul_nonsing_inv_cancel_left _ _ hdet]`. Establish `hz : ∀ z : Fin d → E, (∀ u, form σ W.J (H'.ι *ᵥ u) z = 0) → P.map σ *ᵥ z = 0`. Introduce `z hz`. Establish `e1 : (H'.ιᵀ * W.J) *ᵥ (fun i => σ (z i)) = 0`.

Use function extensionality and compare the values at `j`. Use `hz (Pi.single j 1)` as an intermediate fact. Rewrite `this` using `[form, mulVec_single_one]`. Rewrite using `[← mulVec_mulVec]`. Conclude with `this`.

Establish `e2 : P *ᵥ (fun i => σ (z i)) = 0` using `by rw [hP, ← mulVec_mulVec, e1, mulVec_zero]`. Use function extensionality and compare the values at `j`. Use `congrArg σ (congrFun e2 j)` as an intermediate fact. Simplify `this` using `[mulVec, dotProduct, map_sum, map_mul, hσ]`. Use `⟨P.map σ, ?_, ?_, by rw [mm, h2], hz _ fun u => (hA.orth u).1, hz _ fun u => (hA.orth u).2⟩` and prove the remaining obligations.

Establish `: P * H'.ι.map σ = 1` using `by rw [hP, Matrix.mul_assoc, hA.gram, Matrix.nonsing_inv_mul _ hdet]`. Rewrite using `[← mm H'.ι, ← mul, this]`. Conclude with `Matrix.map_one _ (map_zero σ) (map_one σ)`. Use `congrArg (fun A => (Matrix.map A σ)ᵀ) h2` as an intermediate fact. Simplify using `only [mul, sk, sk₁, transpose_mul, transpose_neg, transpose_transpose, Matrix.neg_mul, Matrix.mul_neg, neg_inj] at this`.

Conclude with `this`.
-/
theorem exists_proj (hcm : IsCMExt F E σ) {B : Base F E} {d d₁ r s : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁}
    (hW : W.IsSkew σ B r s) {H' : Plane E d d₁} {i₀ i₁ : ℕ} (hA : H'.IsAdapted σ B W W₁ i₀ i₁) :
    ∃ π : Matrix (Fin d₁) (Fin d) E, π * H'.ι = 1 ∧ W.J * H'.ι.map σ = πᵀ * W₁.J ∧ H'.ιᵀ * W.J = W₁.J * π.map σ ∧
      π *ᵥ H'.x = 0 ∧ π *ᵥ H'.y = 0 := by
  have hσ := GlobalTheory.LeviTorus.sigma_invol hcm
  have hdet := isUnit_det_low hσ hW hA
  have mm : ∀ {k l : ℕ} (A : Matrix (Fin k) (Fin l) E), (A.map σ).map σ = A := fun A => by
    ext i j; exact hσ _
  have mul : ∀ {k l p : ℕ} (A : Matrix (Fin k) (Fin l) E) (A' : Matrix (Fin l) (Fin p) E),
      (A * A').map σ = A.map σ * A'.map σ := fun A A' => Matrix.map_mul (f := σ.toRingHom)
  have sk : W.J.map σ = -W.Jᵀ := by ext i j; exact hW.skew j i
  have sk₁ : W₁.J.map σ = -W₁.Jᵀ := by
    rw [← hA.gram, mul, mul, mm, sk, transpose_mul, transpose_mul, transpose_transpose]
    simp [Matrix.mul_assoc, Matrix.transpose_map]
  set P : Matrix (Fin d₁) (Fin d) E := W₁.J⁻¹ * (H'.ιᵀ * W.J) with hP
  have h2 : H'.ιᵀ * W.J = W₁.J * P := by rw [hP, Matrix.mul_nonsing_inv_cancel_left _ _ hdet]
  have hz : ∀ z : Fin d → E, (∀ u, form σ W.J (H'.ι *ᵥ u) z = 0) → P.map σ *ᵥ z = 0 := by
    intro z hz
    have e1 : (H'.ιᵀ * W.J) *ᵥ (fun i => σ (z i)) = 0 := by
      funext j
      have := hz (Pi.single j 1)
      rw [form, mulVec_single_one] at this
      rw [← mulVec_mulVec]
      exact this
    have e2 : P *ᵥ (fun i => σ (z i)) = 0 := by rw [hP, ← mulVec_mulVec, e1, mulVec_zero]
    funext j
    have := congrArg σ (congrFun e2 j)
    simpa [mulVec, dotProduct, map_sum, map_mul, hσ] using this
  refine ⟨P.map σ, ?_, ?_, by rw [mm, h2], hz _ fun u => (hA.orth u).1, hz _ fun u => (hA.orth u).2⟩
  · have : P * H'.ι.map σ = 1 := by rw [hP, Matrix.mul_assoc, hA.gram, Matrix.nonsing_inv_mul _ hdet]
    rw [← mm H'.ι, ← mul, this]
    exact Matrix.map_one _ (map_zero σ) (map_one σ)
  · have := congrArg (fun A => (Matrix.map A σ)ᵀ) h2
    simp only [mul, sk, sk₁, transpose_mul, transpose_neg, transpose_transpose, Matrix.neg_mul, Matrix.mul_neg,
      neg_inj] at this
    exact this

end GlobalTheory.LeviAdapted

namespace GlobalTheory.ThK

open Matrix GlobalTheory.LeviUnitary

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B d d₁ W W₁ H' i₀ i₁ r s hcm hW hA h₁`. Take `⟨π, p1, p2, p3, p4, p5⟩` from `GlobalTheory.LeviAdapted.exists_proj hcm hW hA`. Establish `q1 : incM F π * incM F H'.ι = 1`. Rewrite using `[← incM_mul, p1]`. Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`.

Establish `q2 : incM F W.J * (incM F H'.ι).map (cA σ).toRingHom = (incM F π)ᵀ * incM F W₁.J`. Rewrite using `[incM_conj, ← incM_mul, p2, incM_mul]`. Both sides reduce to the same expression. Establish `q3 : (incM F H'.ι)ᵀ * incM F W.J = incM F W₁.J * (incM F π).map (cA σ).toRingHom`. Rewrite using `[incM_conj, ← incM_mul, ← p3, incM_mul]`.

Both sides reduce to the same expression. Establish `hfix : ∀ z, π *ᵥ z = 0 → (1 + incM F H'.ι * (mat h₁ - 1) * incM F π) *ᵥ incV F z = incV F z`. Introduce `z hz`. Establish `h0 : incV F (0 : Fin d₁ → E) = 0` using `by funext i; exact map_zero _`. Rewrite using `[add_mulVec, one_mulVec, ← mulVec_mulVec, incM_mulVec, hz, h0, mulVec_zero, add_zero]`.

Use `⟨⟨⟨1 + incM F H'.ι * (mat h₁ - 1) * incM F π, 1 + incM F H'.ι * ((h₁.1⁻¹).1 - 1) * incM F π, ?_, ?_⟩, ?_⟩, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[ext_mul q1, mat, Units.mul_inv]`. Simplify using the standard rewrite rules. Rewrite using `[ext_mul q1, mat, Units.inv_mul]`. Simplify using the standard rewrite rules.

Conclude with `ext_unitary (cA σ).toRingHom q1 q2 q3 h₁.2`. Rewrite using `[Units.val_one, one_smul]`. Conclude with `hfix _ p4`. Rewrite using `[inv_one, Units.val_one, map_one, one_smul]`. Conclude with `hfix _ p5`.

Use `show (1 + incM F H'.ι * (mat h₁ - 1) * incM F π) * incM F H'.ι = _`. Rewrite using `[Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, q1, Matrix.mul_one, Matrix.mul_sub, Matrix.mul_one, add_sub_cancel]`.
-/
theorem exists_isLevi_one_of_adapted : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ r s : ℕ),
    IsCMExt F E σ → W.IsSkew σ B r s → H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ h₁ : UA σ W₁.J, ∃ m : UA σ W.J, IsLevi (W₁ := W₁) H' 1 h₁ m := by
  intro F E _ _ _ _ _ σ B d d₁ W W₁ H' i₀ i₁ r s hcm hW hA h₁
  obtain ⟨π, p1, p2, p3, p4, p5⟩ := GlobalTheory.LeviAdapted.exists_proj hcm hW hA
  have q1 : incM F π * incM F H'.ι = 1 := by
    rw [← incM_mul, p1]; exact Matrix.map_one _ (map_zero _) (map_one _)
  have q2 : incM F W.J * (incM F H'.ι).map (cA σ).toRingHom = (incM F π)ᵀ * incM F W₁.J := by
    rw [incM_conj, ← incM_mul, p2, incM_mul]; rfl
  have q3 : (incM F H'.ι)ᵀ * incM F W.J = incM F W₁.J * (incM F π).map (cA σ).toRingHom := by
    rw [incM_conj, ← incM_mul, ← p3, incM_mul]; rfl
  have hfix : ∀ z, π *ᵥ z = 0 → (1 + incM F H'.ι * (mat h₁ - 1) * incM F π) *ᵥ incV F z = incV F z := by
    intro z hz
    have h0 : incV F (0 : Fin d₁ → E) = 0 := by funext i; exact map_zero _
    rw [add_mulVec, one_mulVec, ← mulVec_mulVec, incM_mulVec, hz, h0, mulVec_zero, add_zero]
  refine ⟨⟨⟨1 + incM F H'.ι * (mat h₁ - 1) * incM F π, 1 + incM F H'.ι * ((h₁.1⁻¹).1 - 1) * incM F π, ?_, ?_⟩, ?_⟩,
    ?_, ?_, ?_⟩
  · rw [ext_mul q1, mat, Units.mul_inv]; simp
  · rw [ext_mul q1, mat, Units.inv_mul]; simp
  · exact ext_unitary (cA σ).toRingHom q1 q2 q3 h₁.2
  · rw [Units.val_one, one_smul]; exact hfix _ p4
  · rw [inv_one, Units.val_one, map_one, one_smul]; exact hfix _ p5
  · show (1 + incM F H'.ι * (mat h₁ - 1) * incM F π) * incM F H'.ι = _
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, q1, Matrix.mul_one, Matrix.mul_sub, Matrix.mul_one, add_sub_cancel]

end GlobalTheory.ThK

end
