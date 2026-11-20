import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvIInfScaleMul
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

namespace GlobalTheory.SiegelSet.PerpBasis

/- English proof (translation)
Use `set K := LinearMap.ker G.mulVecLin with hK`. Set `b` to `Module.finBasis E K`. Set `Z : Matrix (Fin n) (Fin (Module.finrank E K)) E` to `Matrix.of fun i j => (b j : Fin n → E) i`. Establish `hZv : ∀ a, Z *ᵥ a = ((∑ j, a j • b j : K) : Fin n → E)`. Introduce `a`.

Use extensionality with `i`. Simplify using `[Z, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]`. Establish `hGZv : ∀ a, G *ᵥ (Z *ᵥ a) = 0`. Introduce `a`. Rewrite using `[hZv]`.

Conclude with `(∑ j, a j • b j : K).2`. Establish `hGZ : G * Z = 0`. Use extensionality with `i j`. Use `congrFun (hGZv (Pi.single j 1)) i` as an intermediate fact. Rewrite `this` using `[Matrix.mulVec_mulVec]`.

Simplify using `using this`. Establish `hsurj : LinearMap.range G.mulVecLin = ⊤`. Rewrite using `[LinearMap.range_eq_top]`. Introduce `v`. Use `⟨(B * (G * B)) *ᵥ v, ?_⟩` and prove the remaining obligations.

Simplify using `only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]`. Rewrite using `[← Matrix.mul_assoc, h, Matrix.one_mulVec]`. Establish `hdim : Module.finrank E K + Fintype.card ι = n`. Use `LinearMap.finrank_range_add_finrank_ker G.mulVecLin` as an intermediate fact. Rewrite `this` using `[hsurj]`.

Simplify using `only [finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at this`. Rewrite using `[hK]`. Use linear arithmetic over natural numbers and integers. Establish `hinj : Function.Injective (Matrix.toLin' (Matrix.fromCols Z B))`. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `v hv`. Rewrite `hv` using `[Matrix.toLin'_apply, Matrix.fromCols_mulVec]`. Establish `h1 : (G * B) *ᵥ (v ∘ Sum.inr) = 0`. Use `congrArg (G *ᵥ ·) hv` as an intermediate fact. Simplify using `only [Matrix.mulVec_add, hGZv, zero_add, Matrix.mulVec_zero] at this`.

Rewrite using `[← Matrix.mulVec_mulVec]`. Conclude with `this`. Establish `h2 : v ∘ Sum.inr = 0`. Use `congrArg ((G * B) *ᵥ ·) h1` as an intermediate fact. Simplify using `only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at this`.

Rewrite `this` using `[h, Matrix.one_mulVec]`. Then use the resulting hypothesis. Rewrite `hv` using `[h2, Matrix.mulVec_zero, add_zero, hZv]`. Establish `h3 : (∑ j, (v ∘ Sum.inl) j • b j : K) = 0` using `Subtype.ext hv`. Establish `h4` using `Fintype.linearIndependent_iff.1 b.linearIndependent _ h3`. Use extensionality with `x`.

Break down `x with x | x` into its components or cases. Conclude with `h4 x`. Conclude with `congrFun h2 x`. Set `e` to `LinearMap.linearEquivOfInjective _ hinj (by simp [hdim])`. Establish `he : (e : (Fin (Module.finrank E K) ⊕ ι → E) →ₗ[E] (Fin n → E)) = Matrix.toLin' (Matrix.fromCols Z B)` using `by ext1 x; rfl`.

Establish `he' : LinearMap.toMatrix' (e : (Fin (Module.finrank E K) ⊕ ι → E) →ₗ[E] (Fin n → E)) = Matrix.fromCols Z B` using `by rw [he, LinearMap.toMatrix'_toLin']`. Use `⟨_, Z, LinearMap.toMatrix' (e.symm : (Fin n → E) →ₗ[E] (Fin (Module.finrank E K) ⊕ ι → E)), hdim, ?_, ?_, hGZ⟩` and prove the remaining obligations. Rewrite using `[← he', ← LinearMap.toMatrix'_comp]`. Simplify using the standard rewrite rules. Rewrite using `[← he', ← LinearMap.toMatrix'_comp]`.

Simplify using the standard rewrite rules.
-/
theorem exists_ker_basis {E : Type} [Field E] {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι (Fin n) E) (B : Matrix (Fin n) ι E) (h : G * B * (G * B) = 1) :
    ∃ (n₀ : ℕ) (Z : Matrix (Fin n) (Fin n₀) E) (Q : Matrix (Fin n₀ ⊕ ι) (Fin n) E),
      n₀ + Fintype.card ι = n ∧ Q * Matrix.fromCols Z B = 1 ∧ Matrix.fromCols Z B * Q = 1 ∧ G * Z = 0 := by
  set K := LinearMap.ker G.mulVecLin with hK
  let b := Module.finBasis E K
  let Z : Matrix (Fin n) (Fin (Module.finrank E K)) E := Matrix.of fun i j => (b j : Fin n → E) i
  have hZv : ∀ a, Z *ᵥ a = ((∑ j, a j • b j : K) : Fin n → E) := by
    intro a
    ext i
    simp [Z, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hGZv : ∀ a, G *ᵥ (Z *ᵥ a) = 0 := by
    intro a
    rw [hZv]
    exact (∑ j, a j • b j : K).2
  have hGZ : G * Z = 0 := by
    ext i j
    have := congrFun (hGZv (Pi.single j 1)) i
    rw [Matrix.mulVec_mulVec] at this
    simpa using this
  have hsurj : LinearMap.range G.mulVecLin = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro v
    refine ⟨(B * (G * B)) *ᵥ v, ?_⟩
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
    rw [← Matrix.mul_assoc, h, Matrix.one_mulVec]
  have hdim : Module.finrank E K + Fintype.card ι = n := by
    have := LinearMap.finrank_range_add_finrank_ker G.mulVecLin
    rw [hsurj] at this
    simp only [finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at this
    rw [hK]
    omega
  have hinj : Function.Injective (Matrix.toLin' (Matrix.fromCols Z B)) := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    rw [Matrix.toLin'_apply, Matrix.fromCols_mulVec] at hv
    have h1 : (G * B) *ᵥ (v ∘ Sum.inr) = 0 := by
      have := congrArg (G *ᵥ ·) hv
      simp only [Matrix.mulVec_add, hGZv, zero_add, Matrix.mulVec_zero] at this
      rw [← Matrix.mulVec_mulVec]; exact this
    have h2 : v ∘ Sum.inr = 0 := by
      have := congrArg ((G * B) *ᵥ ·) h1
      simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at this
      rwa [h, Matrix.one_mulVec] at this
    rw [h2, Matrix.mulVec_zero, add_zero, hZv] at hv
    have h3 : (∑ j, (v ∘ Sum.inl) j • b j : K) = 0 := Subtype.ext hv
    have h4 := Fintype.linearIndependent_iff.1 b.linearIndependent _ h3
    ext x
    rcases x with x | x
    · exact h4 x
    · exact congrFun h2 x
  let e := LinearMap.linearEquivOfInjective _ hinj (by simp [hdim])
  have he : (e : (Fin (Module.finrank E K) ⊕ ι → E) →ₗ[E] (Fin n → E)) =
      Matrix.toLin' (Matrix.fromCols Z B) := by
    ext1 x; rfl
  have he' : LinearMap.toMatrix' (e : (Fin (Module.finrank E K) ⊕ ι → E) →ₗ[E] (Fin n → E)) =
      Matrix.fromCols Z B := by rw [he, LinearMap.toMatrix'_toLin']
  refine ⟨_, Z, LinearMap.toMatrix' (e.symm : (Fin n → E) →ₗ[E] (Fin (Module.finrank E K) ⊕ ι → E)),
    hdim, ?_, ?_, hGZ⟩
  · rw [← he', ← LinearMap.toMatrix'_comp]; simp
  · rw [← he', ← LinearMap.toMatrix'_comp]; simp

section
variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Formalism.UG.cT, Matrix.mul_apply, hσ]`.
-/
theorem gram_eq_map (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {a b : Type}
    (A : Matrix (Fin n) a E) (B : Matrix (Fin n) b E) :
    Aᵀ * J * B.map σ = (Formalism.UG.cT (σ : E →+* E) A * ((1 : E) • J.map σ) * B).map σ := by
  ext i j
  simp [Formalism.UG.cT, Matrix.mul_apply, hσ]

/- English proof (translation)
Establish `: J.map σ = Jᵀ` using `by ext i j; simp [hJ]`. Rewrite using `[this]`. Simplify using `only [Formalism.UG.cT, one_smul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]`. Both sides reduce to the same expression.
-/
theorem gram_eq_transpose {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (hJ : ∀ i j, σ (J j i) = J i j)
    {a b : Type} (A : Matrix (Fin n) a E) (B : Matrix (Fin n) b E) :
    Aᵀ * J * B.map σ = (Formalism.UG.cT (σ : E →+* E) B * ((1 : E) • J.map σ) * A)ᵀ := by
  have : J.map σ = Jᵀ := by ext i j; simp [hJ]
  rw [this]
  simp only [Formalism.UG.cT, one_smul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.mul_assoc]
  rfl

end

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hcm n J hJ hdet r₀ X Y hW`. Establish `hσ : ∀ x, σ (σ x) = x` using `GlobalTheory.SiegelSet.sigma_sigma hcm`. Establish `gxx : Xᵀ * J * X.map σ = 0` using `by rw [gram_eq_transpose σ J hJ, hW.xx]; simp`. Establish `gyy : Yᵀ * J * Y.map σ = 0` using `by rw [gram_eq_transpose σ J hJ, hW.yy]; simp`. Establish `gyx : Yᵀ * J * X.map σ = 1` using `by rw [gram_eq_transpose σ J hJ, hW.xy]; simp`.

Establish `gxy : Xᵀ * J * Y.map σ = 1`. Rewrite using `[gram_eq_map σ hσ J, hW.xy]`. Conclude with `Matrix.map_one _ (map_zero σ) (map_one σ)`. Establish `hyx : Formalism.UG.cT (σ : E →+* E) Y * ((1 : E) • J.map σ) * X = 1`. Use `gram_eq_transpose σ J hJ X Y` as an intermediate fact.

Rewrite `this` using `[gxy]`. Rewrite using `[← Matrix.transpose_transpose (_ * X), ← this, Matrix.transpose_one]`. Establish `hGB : Matrix.fromRows (Formalism.UG.cT (σ : E →+* E) X * ((1 : E) • J.map σ)) (Formalism.UG.cT (σ : E →+* E) Y * ((1 : E) • J.map σ)) * Matrix.fromCols X Y = Matrix.fromBlocks 0 1 1 0`. Rewrite using `[Matrix.fromRows_mul_fromCols, hW.xx, hW.yy, hW.xy, hyx]`. Take `⟨n₀, Z, Q, hn, hQP, hPQ, hGZ⟩` from `exists_ker_basis (Matrix.fromRows (Formalism.UG.cT (σ : E →+* E) X * ((1 : E) • J.map σ)) (Formalism.UG.cT (σ : E →+* E) Y * ((1 : E) • J.map σ))) (Matrix.fromCols X Y) (by rw [hGB, Matrix.fromBlocks_multiply]; simp)`.

Rewrite `hGZ` using `[Matrix.fromRows_mul]`. Establish `hXZ : Formalism.UG.cT (σ : E →+* E) X * ((1 : E) • J.map σ) * Z = 0`. Use extensionality with `i j`. Conclude with `congrFun (congrFun hGZ (Sum.inl i)) j`. Establish `hYZ : Formalism.UG.cT (σ : E →+* E) Y * ((1 : E) • J.map σ) * Z = 0`.

Use extensionality with `i j`. Conclude with `congrFun (congrFun hGZ (Sum.inr i)) j`. Establish `gzx : Zᵀ * J * X.map σ = 0` using `by rw [gram_eq_transpose σ J hJ, hXZ]; simp`. Establish `gzy : Zᵀ * J * Y.map σ = 0` using `by rw [gram_eq_transpose σ J hJ, hYZ]; simp`. Establish `gxz : Xᵀ * J * Z.map σ = 0`.

Rewrite using `[gram_eq_map σ hσ J, hXZ]`. Conclude with `Matrix.map_zero _ (map_zero σ)`. Establish `gyz : Yᵀ * J * Z.map σ = 0`. Rewrite using `[gram_eq_map σ hσ J, hYZ]`. Conclude with `Matrix.map_zero _ (map_zero σ)`.

Establish `hgram : (Matrix.fromCols Z (Matrix.fromCols X Y))ᵀ * J * (Matrix.fromCols Z (Matrix.fromCols X Y)).map σ = Matrix.fromBlocks (Zᵀ * J * Z.map σ) 0 0 (Matrix.fromBlocks 0 1 1 0)`. Simplify using `only [Matrix.transpose_fromCols, Matrix.fromCols_map]`. Rewrite using `[Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols, Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols, Matrix.mul_fromCols, Matrix.fromRows_mul, gxx, gyy, gyx, gxy, gzx, gzy, gxz, gyz]`. Simplify using the standard rewrite rules. Use `⟨n₀, Z, Q, by simpa using hn, hQP, hPQ, hgram, ?_, ?_, hXZ, hYZ⟩` and prove the remaining obligations.

Use `set P := Matrix.fromCols Z (Matrix.fromCols X Y) with hP`. Establish `hJu : IsUnit J.det` using `hdet.isUnit`. Establish `h1 : P.map σ * Q.map σ = 1`. Rewrite using `[← Matrix.map_mul, hPQ]`. Conclude with `Matrix.map_one _ (map_zero σ) (map_one σ)`.

Establish `h2 : Pᵀ * Qᵀ = 1` using `by rw [← Matrix.transpose_mul, hQP, Matrix.transpose_one]`. Establish `h3 : (Pᵀ * J * P.map σ) * (Q.map σ * J⁻¹ * Qᵀ) = 1`. Combine the equalities or inequalities in the displayed calculation. Establish `h4` using `congrArg Matrix.det h3`. Rewrite `h4` using `[Matrix.det_mul, hgram, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one]`.

Introduce `h0`. Rewrite `h4` using `[h0]`. Simplify using `at h4`. Introduce `i j`. Establish `h1` using `congrFun (congrFun (gram_eq_map σ hσ J Z Z) j) i`.

Establish `h2` using `congrFun (congrFun (gram_eq_transpose σ J hJ Z Z) i) j`. Rewrite using `[h1, h2, Matrix.map_apply, hσ, Matrix.transpose_apply]`.
-/
theorem exists_perp_basis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), (∀ i j, σ (J j i) = J i j) → J.det ≠ 0 →
    ∀ (r₀ : ℕ) (Xf Yf : Matrix (Fin n) (Fin r₀) E), GlobalTheory.SiegelSet.IsWittFrame σ ((1 : E) • J.map σ) Xf Yf →
    ∃ (n₀ : ℕ) (Z₀ : Matrix (Fin n) (Fin n₀) E) (Q : Matrix (Fin n₀ ⊕ (Fin r₀ ⊕ Fin r₀)) (Fin n) E),
      n₀ + (r₀ + r₀) = n ∧
      Q * Matrix.fromCols Z₀ (Matrix.fromCols Xf Yf) = 1 ∧ Matrix.fromCols Z₀ (Matrix.fromCols Xf Yf) * Q = 1 ∧
      (Matrix.fromCols Z₀ (Matrix.fromCols Xf Yf))ᵀ * J * (Matrix.fromCols Z₀ (Matrix.fromCols Xf Yf)).map σ =
        Matrix.fromBlocks (Z₀ᵀ * J * Z₀.map σ) 0 0 (Matrix.fromBlocks 0 1 1 0) ∧
      (Z₀ᵀ * J * Z₀.map σ).det ≠ 0 ∧ (∀ i j, σ ((Z₀ᵀ * J * Z₀.map σ) j i) = (Z₀ᵀ * J * Z₀.map σ) i j) ∧
      Formalism.UG.cT (σ : E →+* E) Xf * ((1 : E) • J.map σ) * Z₀ = 0 ∧ Formalism.UG.cT (σ : E →+* E) Yf * ((1 : E) • J.map σ) * Z₀ = 0 := by
  intro F E _ _ _ _ _ σ hcm n J hJ hdet r₀ X Y hW
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.SiegelSet.sigma_sigma hcm
  have gxx : Xᵀ * J * X.map σ = 0 := by rw [gram_eq_transpose σ J hJ, hW.xx]; simp
  have gyy : Yᵀ * J * Y.map σ = 0 := by rw [gram_eq_transpose σ J hJ, hW.yy]; simp
  have gyx : Yᵀ * J * X.map σ = 1 := by rw [gram_eq_transpose σ J hJ, hW.xy]; simp
  have gxy : Xᵀ * J * Y.map σ = 1 := by
    rw [gram_eq_map σ hσ J, hW.xy]; exact Matrix.map_one _ (map_zero σ) (map_one σ)
  have hyx : Formalism.UG.cT (σ : E →+* E) Y * ((1 : E) • J.map σ) * X = 1 := by
    have := gram_eq_transpose σ J hJ X Y
    rw [gxy] at this
    rw [← Matrix.transpose_transpose (_ * X), ← this, Matrix.transpose_one]
  have hGB : Matrix.fromRows (Formalism.UG.cT (σ : E →+* E) X * ((1 : E) • J.map σ))
      (Formalism.UG.cT (σ : E →+* E) Y * ((1 : E) • J.map σ)) * Matrix.fromCols X Y =
      Matrix.fromBlocks 0 1 1 0 := by
    rw [Matrix.fromRows_mul_fromCols, hW.xx, hW.yy, hW.xy, hyx]
  obtain ⟨n₀, Z, Q, hn, hQP, hPQ, hGZ⟩ := exists_ker_basis
    (Matrix.fromRows (Formalism.UG.cT (σ : E →+* E) X * ((1 : E) • J.map σ))
      (Formalism.UG.cT (σ : E →+* E) Y * ((1 : E) • J.map σ))) (Matrix.fromCols X Y)
    (by rw [hGB, Matrix.fromBlocks_multiply]; simp)
  rw [Matrix.fromRows_mul] at hGZ
  have hXZ : Formalism.UG.cT (σ : E →+* E) X * ((1 : E) • J.map σ) * Z = 0 := by
    ext i j; exact congrFun (congrFun hGZ (Sum.inl i)) j
  have hYZ : Formalism.UG.cT (σ : E →+* E) Y * ((1 : E) • J.map σ) * Z = 0 := by
    ext i j; exact congrFun (congrFun hGZ (Sum.inr i)) j
  have gzx : Zᵀ * J * X.map σ = 0 := by rw [gram_eq_transpose σ J hJ, hXZ]; simp
  have gzy : Zᵀ * J * Y.map σ = 0 := by rw [gram_eq_transpose σ J hJ, hYZ]; simp
  have gxz : Xᵀ * J * Z.map σ = 0 := by
    rw [gram_eq_map σ hσ J, hXZ]; exact Matrix.map_zero _ (map_zero σ)
  have gyz : Yᵀ * J * Z.map σ = 0 := by
    rw [gram_eq_map σ hσ J, hYZ]; exact Matrix.map_zero _ (map_zero σ)
  have hgram : (Matrix.fromCols Z (Matrix.fromCols X Y))ᵀ * J *
      (Matrix.fromCols Z (Matrix.fromCols X Y)).map σ =
      Matrix.fromBlocks (Zᵀ * J * Z.map σ) 0 0 (Matrix.fromBlocks 0 1 1 0) := by
    simp only [Matrix.transpose_fromCols, Matrix.fromCols_map]
    rw [Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols, Matrix.fromRows_mul,
      Matrix.fromRows_mul_fromCols, Matrix.mul_fromCols, Matrix.fromRows_mul,
      gxx, gyy, gyx, gxy, gzx, gzy, gxz, gyz]
    simp
  refine ⟨n₀, Z, Q, by simpa using hn, hQP, hPQ, hgram, ?_, ?_, hXZ, hYZ⟩
  · set P := Matrix.fromCols Z (Matrix.fromCols X Y) with hP
    have hJu : IsUnit J.det := hdet.isUnit
    have h1 : P.map σ * Q.map σ = 1 := by
      rw [← Matrix.map_mul, hPQ]; exact Matrix.map_one _ (map_zero σ) (map_one σ)
    have h2 : Pᵀ * Qᵀ = 1 := by rw [← Matrix.transpose_mul, hQP, Matrix.transpose_one]
    have h3 : (Pᵀ * J * P.map σ) * (Q.map σ * J⁻¹ * Qᵀ) = 1 := by
      calc _ = Pᵀ * (J * ((P.map σ * Q.map σ) * J⁻¹)) * Qᵀ := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [h1, Matrix.one_mul, Matrix.mul_nonsing_inv _ hJu, Matrix.mul_one, h2]
    have h4 := congrArg Matrix.det h3
    rw [Matrix.det_mul, hgram, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one] at h4
    intro h0
    rw [h0] at h4
    simp at h4
  · intro i j
    have h1 := congrFun (congrFun (gram_eq_map σ hσ J Z Z) j) i
    have h2 := congrFun (congrFun (gram_eq_transpose σ J hJ Z Z) i) j
    rw [h1, h2, Matrix.map_apply, hσ, Matrix.transpose_apply]

end GlobalTheory.SiegelSet.PerpBasis
