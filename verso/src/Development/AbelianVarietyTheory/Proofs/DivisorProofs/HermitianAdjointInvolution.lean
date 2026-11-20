import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Idem3

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipHaar

noncomputable section

namespace GlobalTheory.UnipHaar

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Simplify using `only [incM]`. Conclude with `Matrix.map_mul`.
-/
theorem incM_mul' {n : ℕ} (A B : Matrix (Fin n) (Fin n) E) : incM F (A * B) = incM F A * incM F B := by
  simp only [incM]; exact Matrix.map_mul

/- English proof (translation)
Simplify using `only [incM]`. Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`.
-/
theorem incM_one' {n : ℕ} : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := by
  simp only [incM]; exact Matrix.map_one _ (map_zero _) (map_one _)

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[incM]`.
-/
theorem incM_neg' {n : ℕ} (A : Matrix (Fin n) (Fin n) E) : incM F (-A) = -incM F A := by
  ext i j; simp [incM]

/- English proof (translation)
Simplify using `only [incM]`. Conclude with `(Matrix.transpose_map).symm`.
-/
theorem incM_transpose' {n : ℕ} (A : Matrix (Fin n) (Fin n) E) : incM F Aᵀ = (incM F A)ᵀ := by
  simp only [incM]; exact (Matrix.transpose_map).symm

/- English proof (translation)
Simplify using `[cA, inclR]`.
-/
theorem cA_inclR (σ : E →ₐ[F] E) (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [cA, inclR]

/- English proof (translation)
Proceed by induction on `a using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul r e => simp [cA, hσ]`. Consider the case `add a b ha hb => rw [map_add, map_add, ha, hb]`.
-/
theorem cA_cA (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (a : AE F E) : cA σ (cA σ a) = a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [cA, hσ]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[incM, cA_inclR]`.
-/
theorem incM_map_cA (σ : E →ₐ[F] E) {n : ℕ} (A : Matrix (Fin n) (Fin n) E) :
    (incM F A).map (cA σ) = incM F (A.map σ) := by
  ext i j; simp [incM, cA_inclR]

/- English proof (translation)
Use `haveI := IsModuleTopology.isTopologicalRing (AF F) (AE F E)`. Conclude with `IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap`.
-/
theorem continuous_cA (σ : E →ₐ[F] E) : Continuous (cA σ) := by
  haveI := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
  exact IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap

end GlobalTheory.UnipHaar

namespace GlobalTheory.UnipHaar

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n J hσ hskew hdet`. Use `haveI := IsModuleTopology.isTopologicalRing (AF F) (AE F E)`. Use `set K := J.map σ with hKdef`. Establish `hK : K = -Jᵀ` using `by ext i j; simp [K, hskew j i]`. Establish `hKdet : K.det ≠ 0`.

Rewrite using `[hK, Matrix.det_neg, Matrix.det_transpose]`. Conclude with `mul_ne_zero (pow_ne_zero _ (by norm_num)) hdet`. Establish `hKu : IsUnit K.det` using `isUnit_iff_ne_zero.mpr hKdet`. Establish `hKK : K⁻¹ * K = 1` using `Matrix.nonsing_inv_mul K hKu`. Establish `hKK' : K * K⁻¹ = 1` using `Matrix.mul_nonsing_inv K hKu`.

Establish `hKσ : K.map σ = J` using `by ext i j; simp [K, hσ]`. Establish `hCinv : (incM F K)⁻¹ = incM F K⁻¹`. Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises. Rewrite using `[← incM_mul', hKK, incM_one']`. Establish `hCC : incM F K⁻¹ * incM F K = 1` using `by rw [← incM_mul', hKK, incM_one']`.

Establish `hCC' : incM F K * incM F K⁻¹ = 1` using `by rw [← incM_mul', hKK', incM_one']`. Establish `hadj : ∀ X, adj σ J X = incM F K⁻¹ * (X.map (cA σ))ᵀ * incM F K` using `fun X => by show (incM F K)⁻¹ * _ * _ = _`. Rewrite using `[hCinv]`. Use `set cR : AE F E →+* AE F E := (cA σ).toRingHom`. Establish `hc : ⇑(cA σ) = ⇑cR` using `rfl`.

Establish `hcc : ∀ X : Matrix (Fin n) (Fin n) (AE F E), (X.map (cA σ)).map (cA σ) = X` using `fun X => by`. Use extensionality with `i j`. Simplify using `[cA_cA σ hσ]`. Use `⟨?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `: ⇑(adj σ J) = fun X => incM F K⁻¹ * (X.map (cA σ))ᵀ * incM F K` using `funext hadj`.

Rewrite using `[this]`. Conclude with `(continuous_const.matrix_mul (continuous_id.matrix_map (continuous_cA σ)).matrix_transpose).matrix_mul continuous_const`. Introduce `X Y`. Rewrite using `[hadj, hadj, hadj, hc, Matrix.map_mul, Matrix.transpose_mul]`. Simplify using `only [Matrix.mul_assoc]`.

Rewrite using `[← Matrix.mul_assoc (incM F K) (incM F K⁻¹), hCC', Matrix.one_mul]`. Introduce `X set L := K⁻¹.map σ with hLdef`. Establish `hs : ⇑σ = ⇑(σ.toRingHom)` using `rfl`. Establish `hLJ : L * J = 1`. Rewrite using `[← hKσ, hLdef, hs, ← Matrix.map_mul, hKK, Matrix.map_one _ (map_zero _) (map_one _)]`.

Establish `hJt : Jᵀ = -K` using `by rw [hK, neg_neg]`. Establish `hKL : (-Lᵀ) * K = 1`. Rewrite using `[mul_eq_one_comm]`. Establish `: Jᵀ * Lᵀ = 1` using `by rw [← Matrix.transpose_mul, hLJ, Matrix.transpose_one]`. Rewrite `this` using `[hJt]`.

Rewrite using `[Matrix.mul_neg, ← Matrix.neg_mul, this]`. Establish `h1 : incM F K⁻¹ * incM F Jᵀ = -1`. Rewrite using `[← incM_mul', hJt, Matrix.mul_neg, hKK, incM_neg', incM_one']`. Establish `h2 : incM F Lᵀ * incM F K = -1`. Rewrite using `[← incM_mul', ← neg_neg (Lᵀ * K), ← Matrix.neg_mul, hKL, incM_neg', incM_one']`.

Rewrite using `[hadj (adj σ J X), hadj X, hc, Matrix.map_mul, Matrix.map_mul, ← hc, incM_map_cA, incM_map_cA, hKσ, Matrix.transpose_map, hcc, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← incM_transpose', ← incM_transpose']`. Rewrite using `[← hLdef, show ∀ A B C D : Matrix (Fin n) (Fin n) (AE F E), A * (B * (X * C)) * D = (A * B) * X * (C * D) from fun A B C D => by simp only [Matrix.mul_assoc], h1, h2]`. Simplify using the standard rewrite rules. Introduce and unpack `X ⟨A, rfl⟩`. Use `⟨K⁻¹ * (A.map σ)ᵀ * K, ?_⟩` and prove the remaining obligations.

Rewrite using `[hadj]`. Use `show incM F _ = _`. Rewrite using `[RingHom.mapMatrix_apply]`. Express the relevant statement in the definitionally equal form `_ = incM F K⁻¹ * ((incM F A).map (cA σ))ᵀ * incM F K`. Rewrite using `[incM_map_cA, incM_mul', incM_mul', incM_transpose']`.

Introduce `X`. Establish `e1 : adj σ J X * X = incM F K⁻¹ * ((X.map (cA σ))ᵀ * incM F K * X)`. Rewrite using `[hadj]`. Simplify using `only [Matrix.mul_assoc]`. Establish `e2 : incM F K⁻¹ * ((X.map (cA σ))ᵀ * incM F K * X) = 1 ↔ (X.map (cA σ))ᵀ * incM F K * X = incM F K`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Matrix.mul_assoc, hCC', Matrix.one_mul]`. Use `_ = incM F K := by rw [h, Matrix.mul_one]`.

Introduce `h`. Rewrite using `[h, hCC]`. Establish `e3 : ((X.map (cA σ))ᵀ * incM F K * X).map (cA σ) = Xᵀ * incM F J * X.map (cA σ)`. Rewrite using `[hc, Matrix.map_mul, Matrix.map_mul, ← hc, Matrix.transpose_map, hcc, incM_map_cA, hKσ]`. Establish `e4 : (incM F K).map (cA σ) = incM F J` using `by rw [incM_map_cA, hKσ]`.

Rewrite using `[e1, e2, ← e3, ← e4]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[h]`. Introduce `h`.

Use `congrArg (fun M : Matrix (Fin n) (Fin n) (AE F E) => M.map (cA σ)) h` as an intermediate fact. Simplify `this` using `only [hcc]`.
-/
theorem adj_props : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), (∀ x, σ (σ x) = x) → (∀ i j, σ (J j i) = -J i j) → J.det ≠ 0 → Continuous (adj σ J) ∧ (∀ X Y, adj σ J (X * Y) = adj σ J Y * adj σ J X) ∧ (∀ X, adj σ J (adj σ J X) = X) ∧ (∀ X ∈ ((inclR (F := F) (E := E) (AF F)).mapMatrix (m := Fin n)).range, adj σ J X ∈ ((inclR (F := F) (E := E) (AF F)).mapMatrix (m := Fin n)).range) ∧ ∀ X, adj σ J X * X = 1 ↔ Xᵀ * incM F J * X.map (cA σ) = incM F J := by
  intro F E _ _ _ _ _ σ n J hσ hskew hdet
  haveI := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
  set K := J.map σ with hKdef
  have hK : K = -Jᵀ := by ext i j; simp [K, hskew j i]
  have hKdet : K.det ≠ 0 := by
    rw [hK, Matrix.det_neg, Matrix.det_transpose]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hdet
  have hKu : IsUnit K.det := isUnit_iff_ne_zero.mpr hKdet
  have hKK : K⁻¹ * K = 1 := Matrix.nonsing_inv_mul K hKu
  have hKK' : K * K⁻¹ = 1 := Matrix.mul_nonsing_inv K hKu
  have hKσ : K.map σ = J := by ext i j; simp [K, hσ]
  have hCinv : (incM F K)⁻¹ = incM F K⁻¹ := by
    apply Matrix.inv_eq_left_inv
    rw [← incM_mul', hKK, incM_one']
  have hCC : incM F K⁻¹ * incM F K = 1 := by rw [← incM_mul', hKK, incM_one']
  have hCC' : incM F K * incM F K⁻¹ = 1 := by rw [← incM_mul', hKK', incM_one']
  have hadj : ∀ X, adj σ J X = incM F K⁻¹ * (X.map (cA σ))ᵀ * incM F K := fun X => by
    show (incM F K)⁻¹ * _ * _ = _
    rw [hCinv]
  set cR : AE F E →+* AE F E := (cA σ).toRingHom
  have hc : ⇑(cA σ) = ⇑cR := rfl
  have hcc : ∀ X : Matrix (Fin n) (Fin n) (AE F E), (X.map (cA σ)).map (cA σ) = X := fun X => by
    ext i j; simp [cA_cA σ hσ]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have : ⇑(adj σ J) = fun X => incM F K⁻¹ * (X.map (cA σ))ᵀ * incM F K := funext hadj
    rw [this]
    exact (continuous_const.matrix_mul
      (continuous_id.matrix_map (continuous_cA σ)).matrix_transpose).matrix_mul continuous_const
  · intro X Y
    rw [hadj, hadj, hadj, hc, Matrix.map_mul, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (incM F K) (incM F K⁻¹), hCC', Matrix.one_mul]
  · intro X
    set L := K⁻¹.map σ with hLdef
    have hs : ⇑σ = ⇑(σ.toRingHom) := rfl
    have hLJ : L * J = 1 := by
      rw [← hKσ, hLdef, hs, ← Matrix.map_mul, hKK, Matrix.map_one _ (map_zero _) (map_one _)]
    have hJt : Jᵀ = -K := by rw [hK, neg_neg]
    have hKL : (-Lᵀ) * K = 1 := by
      rw [mul_eq_one_comm]
      have : Jᵀ * Lᵀ = 1 := by rw [← Matrix.transpose_mul, hLJ, Matrix.transpose_one]
      rw [hJt] at this
      rw [Matrix.mul_neg, ← Matrix.neg_mul, this]
    have h1 : incM F K⁻¹ * incM F Jᵀ = -1 := by
      rw [← incM_mul', hJt, Matrix.mul_neg, hKK, incM_neg', incM_one']
    have h2 : incM F Lᵀ * incM F K = -1 := by
      rw [← incM_mul', ← neg_neg (Lᵀ * K), ← Matrix.neg_mul, hKL, incM_neg', incM_one']
    rw [hadj (adj σ J X), hadj X, hc, Matrix.map_mul, Matrix.map_mul, ← hc, incM_map_cA, incM_map_cA, hKσ,
      Matrix.transpose_map, hcc, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      ← incM_transpose', ← incM_transpose']
    rw [← hLdef, show ∀ A B C D : Matrix (Fin n) (Fin n) (AE F E), A * (B * (X * C)) * D = (A * B) * X * (C * D)
      from fun A B C D => by simp only [Matrix.mul_assoc], h1, h2]
    simp
  · rintro X ⟨A, rfl⟩
    refine ⟨K⁻¹ * (A.map σ)ᵀ * K, ?_⟩
    rw [hadj]
    show incM F _ = _
    rw [RingHom.mapMatrix_apply]
    change _ = incM F K⁻¹ * ((incM F A).map (cA σ))ᵀ * incM F K
    rw [incM_map_cA, incM_mul', incM_mul', incM_transpose']
  · intro X
    have e1 : adj σ J X * X = incM F K⁻¹ * ((X.map (cA σ))ᵀ * incM F K * X) := by
      rw [hadj]; simp only [Matrix.mul_assoc]
    have e2 : incM F K⁻¹ * ((X.map (cA σ))ᵀ * incM F K * X) = 1 ↔ (X.map (cA σ))ᵀ * incM F K * X = incM F K := by
      constructor
      · intro h
        calc (X.map (cA σ))ᵀ * incM F K * X
            = incM F K * (incM F K⁻¹ * ((X.map (cA σ))ᵀ * incM F K * X)) := by
              rw [← Matrix.mul_assoc, hCC', Matrix.one_mul]
          _ = incM F K := by rw [h, Matrix.mul_one]
      · intro h; rw [h, hCC]
    have e3 : ((X.map (cA σ))ᵀ * incM F K * X).map (cA σ) = Xᵀ * incM F J * X.map (cA σ) := by
      rw [hc, Matrix.map_mul, Matrix.map_mul, ← hc, Matrix.transpose_map, hcc, incM_map_cA, hKσ]
    have e4 : (incM F K).map (cA σ) = incM F J := by rw [incM_map_cA, hKσ]
    rw [e1, e2, ← e3, ← e4]
    constructor
    · intro h; rw [h]
    · intro h
      have := congrArg (fun M : Matrix (Fin n) (Fin n) (AE F E) => M.map (cA σ)) h
      simpa only [hcc] using this

end GlobalTheory.UnipHaar

end
