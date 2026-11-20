import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.DenseC
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.RDIota
import Development.WeilBound.ThetaLifts.TowerModels.PlaneIso

noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Krd.DM

open PositivityTheory.SiegelWeilFormula.Krd.DC

variable {n : ℕ}

def QR (R : Type) [Ring R] (n : ℕ) (ε : ℤˣ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R :=
  Matrix.fromBlocks 0 1 (((ε : ℤ) : R) • 1) 0

/- English proof (translation)
Rewrite using `[← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]`.
-/
theorem eps_sq (ε : ℤˣ) (R : Type) [Ring R] : ((ε : ℤ) : R) * ((ε : ℤ) : R) = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]

/- English proof (translation)
Simplify using `only [QR, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.transpose_zero, Matrix.transpose_one, Matrix.transpose_smul]`. Simplify using `[smul_smul, eps_sq]`.
-/
theorem orthogonal_form_mul_transpose (R : Type) [CommRing R] (ε : ℤˣ) : QR R n ε * (QR R n ε)ᵀ = 1 := by
  simp only [QR, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.transpose_zero, Matrix.transpose_one,
    Matrix.transpose_smul]
  simp [smul_smul, eps_sq]

/- English proof (translation)
Introduce `h0`. Use `congrArg Matrix.det (orthogonal_form_mul_transpose (n := n) K ε)` as an intermediate fact. Rewrite `this` using `[Matrix.det_mul, h0, zero_mul, Matrix.det_one]`. Conclude with `zero_ne_one this`.
-/
theorem QR_det_ne (K : Type) [Field K] (ε : ℤˣ) : (QR K n ε).det ≠ 0 := by
  intro h0
  have := congrArg Matrix.det (orthogonal_form_mul_transpose (n := n) K ε)
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j <;> rcases eq_or_ne i j with rfl | hij <;> simp [QR, Matrix.one_apply, *]`.
-/
theorem QR_map {K L : Type} [Field K] [Field L] (f : K →+* L) (ε : ℤˣ) : (QR K n ε).map f = QR L n ε := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> rcases eq_or_ne i j with rfl | hij <;> simp [QR, Matrix.one_apply, *]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Qc_eq (ε : ℤˣ) : Qc n ε = QR ℂ n ε := rfl

/- English proof (translation)
Establish `e : ∀ A : M2 n, (hᴴ * A * h)ᵀ = hᵀ * Aᵀ * h.map star` using `fun A => by`. Rewrite using `[Matrix.transpose_mul, Matrix.transpose_mul, ← Matrix.mul_assoc]`. Use `congr 1`. Unfold `InU`. Prove the components needed by the constructor for the conclusion.

Introduce `hh`. Use `congrArg Matrix.transpose hh` as an intermediate fact. Rewrite `this` using `[e, Matrix.transpose_transpose]`. Then use the resulting hypothesis. Introduce `hh`. Apply `Matrix.transpose_injective` to reduce the goal to its premises.

Rewrite using `[e, Matrix.transpose_transpose, hh]`.
-/
theorem inU_iff (ε : ℤˣ) (h : M2 n) : InU (Qc n ε)ᵀ h ↔ hᵀ * Qc n ε * h.map star = Qc n ε := by
  have e : ∀ A : M2 n, (hᴴ * A * h)ᵀ = hᵀ * Aᵀ * h.map star := fun A => by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, ← Matrix.mul_assoc]
    congr 1
  unfold InU
  constructor
  · intro hh
    have := congrArg Matrix.transpose hh
    rwa [e, Matrix.transpose_transpose] at this
  · intro hh
    apply Matrix.transpose_injective
    rw [e, Matrix.transpose_transpose, hh]

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j <;> rcases eq_or_ne i j with rfl | hij <;>`. Apply the tactic sequence `simp [Qc, Matrix.conjTranspose_apply, Matrix.one_apply, ← mul_assoc, eps_sq, *] <;>`. Conclude with `fun h => absurd h.symm hij`.
-/
theorem J_herm (ε : ℤˣ) : ((Qc n ε)ᵀ)ᴴ = ((ε : ℤ) : ℂ) • (Qc n ε)ᵀ := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> rcases eq_or_ne i j with rfl | hij <;>
    simp [Qc, Matrix.conjTranspose_apply, Matrix.one_apply, ← mul_assoc, eps_sq, *] <;>
    exact fun h => absurd h.symm hij

/- English proof (translation)
Rewrite using `[show ((ε : ℤ) : ℂ) • (1 : M2 n) = Matrix.fromBlocks (((ε : ℤ) : ℂ) • 1) 0 0 (((ε : ℤ) : ℂ) • 1) by`. Rewrite using `[← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, smul_zero]]`. Simplify using `[Qc, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]`.
-/
theorem J_sq (ε : ℤˣ) : (Qc n ε)ᵀ * (Qc n ε)ᵀ = ((ε : ℤ) : ℂ) • 1 := by
  rw [show ((ε : ℤ) : ℂ) • (1 : M2 n) = Matrix.fromBlocks (((ε : ℤ) : ℂ) • 1) 0 0 (((ε : ℤ) : ℂ) • 1) by
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, smul_zero]]
  simp [Qc, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]

/- English proof (translation)
Introduce `h`. Use `eps_sq ε ℂ` as an intermediate fact. Rewrite `this` using `[h, zero_mul]`. Conclude with `zero_ne_one this`.
-/
theorem eps_ne (ε : ℤˣ) : ((ε : ℤ) : ℂ) ≠ 0 := by
  intro h; have := eps_sq ε ℂ; rw [h, zero_mul] at this; exact zero_ne_one this

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem eps_star (ε : ℤˣ) : star ((ε : ℤ) : ℂ) = ((ε : ℤ) : ℂ) := by simp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def ratS (τ : E →+* ℂ) : Set (M2 n) := Set.range fun X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E => X.map τ

/- English proof (translation)
Use `show DenseRange fun X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E => X.map τ`. Conclude with `DenseRange.piMap fun _ => DenseRange.piMap fun _ => PositivityTheory.ThKG.Tow.Pln.denseRange_emb h τ`.
-/
theorem dense_ratS (h : IsCMExt F E σ) (τ : E →+* ℂ) : Dense (ratS (n := n) τ) := by
  show DenseRange fun X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E => X.map τ
  exact DenseRange.piMap fun _ => DenseRange.piMap fun _ => PositivityTheory.ThKG.Tow.Pln.denseRange_emb h τ

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.transpose_apply]`. Conclude with `(h.2.2.2 τ (X j i)).symm`.
-/
theorem map_conjT (h : IsCMExt F E σ) (τ : E →+* ℂ) (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E) :
    (X.map τ)ᴴ = (X.map σ)ᵀ.map τ := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.transpose_apply]
  exact (h.2.2.2 τ (X j i)).symm

/- English proof (translation)
Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
theorem map_smul_τ (τ : E →+* ℂ) (c : E) (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E) :
    (c • M).map τ = τ c • M.map τ := by
  ext i j
  simp

/- English proof (translation)
Rewrite using `[Matrix.transpose_map, QR_map]`. Both sides reduce to the same expression.
-/
theorem QT_map (τ : E →+* ℂ) (ε : ℤˣ) : (QR E n ε)ᵀ.map τ = (Qc n ε)ᵀ := by
  rw [Matrix.transpose_map, QR_map]
  rfl

/- English proof (translation)
Introduce and unpack `_ ⟨X, rfl⟩`. Use `⟨X - ((ε : ℤ) : E)⁻¹ • ((QR E n ε)ᵀ * (X.map σ)ᵀ * (QR E n ε)ᵀ), ?_⟩` and prove the remaining obligations. Use `show (X - ((ε : ℤ) : E)⁻¹ • ((QR E n ε)ᵀ * (X.map σ)ᵀ * (QR E n ε)ᵀ)).map τ = X.map τ - ((ε : ℤ) : ℂ)⁻¹ • ((Qc n ε)ᵀ * (X.map τ)ᴴ * (Qc n ε)ᵀ)`. Rewrite using `[map_conjT h τ X, Matrix.map_sub _ (map_sub τ), map_smul_τ, Matrix.map_mul, Matrix.map_mul, QT_map, map_inv₀, map_intCast]`.
-/
theorem proj_ratS (h : IsCMExt F E σ) (τ : E →+* ℂ) (ε : ℤˣ) :
    ∀ X ∈ ratS (n := n) τ, proj (Qc n ε)ᵀ ((ε : ℤ) : ℂ) X ∈ ratS τ := by
  rintro _ ⟨X, rfl⟩
  refine ⟨X - ((ε : ℤ) : E)⁻¹ • ((QR E n ε)ᵀ * (X.map σ)ᵀ * (QR E n ε)ᵀ), ?_⟩
  show (X - ((ε : ℤ) : E)⁻¹ • ((QR E n ε)ᵀ * (X.map σ)ᵀ * (QR E n ε)ᵀ)).map τ = X.map τ - ((ε : ℤ) : ℂ)⁻¹ • ((Qc n ε)ᵀ * (X.map τ)ᴴ * (Qc n ε)ᵀ)
  rw [map_conjT h τ X, Matrix.map_sub _ (map_sub τ), map_smul_τ, Matrix.map_mul, Matrix.map_mul, QT_map, map_inv₀, map_intCast]

/- English proof (translation)
Establish `e : (M.map τ).det = τ M.det` using `(RingHom.map_det τ M).symm`. Establish `h0 : M.det ≠ 0` using `fun h0 => by rw [e, h0, map_zero] at hM; exact not_isUnit_zero hM`. Establish `hu : IsUnit M.det` using `isUnit_iff_ne_zero.2 h0`. Use `symm`. Use `Matrix.inv_eq_left_inv ?_` and prove the remaining obligations.

Rewrite using `[← Matrix.map_mul, Matrix.nonsing_inv_mul _ hu, Matrix.map_one _ (map_zero τ) (map_one τ)]`.
-/
theorem map_inv_of (τ : E →+* ℂ) (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E) (hM : IsUnit (M.map τ).det) :
    (M⁻¹).map τ = (M.map τ)⁻¹ := by
  have e : (M.map τ).det = τ M.det := (RingHom.map_det τ M).symm
  have h0 : M.det ≠ 0 := fun h0 => by rw [e, h0, map_zero] at hM; exact not_isUnit_zero hM
  have hu : IsUnit M.det := isUnit_iff_ne_zero.2 h0
  symm
  refine Matrix.inv_eq_left_inv ?_
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hu, Matrix.map_one _ (map_zero τ) (map_one τ)]

/- English proof (translation)
Introduce and unpack `_ ⟨X, rfl⟩ hu`. Simplify using `only at hu`. Establish `e1 : (1 - X).map τ = 1 - X.map τ` using `by rw [Matrix.map_sub _ (map_sub τ), Matrix.map_one _ (map_zero τ) (map_one τ)]`. Establish `e2 : (1 + X).map τ = 1 + X.map τ` using `by rw [Matrix.map_add _ (map_add τ), Matrix.map_one _ (map_zero τ) (map_one τ)]`. Use `⟨(1 + X) * (1 - X)⁻¹, ?_⟩` and prove the remaining obligations.

Use `show ((1 + X) * (1 - X)⁻¹).map τ = (1 + X.map τ) * (1 - X.map τ)⁻¹`. Rewrite using `[Matrix.map_mul, e2, map_inv_of τ _ (e1 ▸ hu), e1]`.
-/
theorem cay_ratS (τ : E →+* ℂ) : ∀ X ∈ ratS (n := n) τ, IsUnit (1 - X).det → cay X ∈ ratS τ := by
  rintro _ ⟨X, rfl⟩ hu
  simp only at hu
  have e1 : (1 - X).map τ = 1 - X.map τ := by rw [Matrix.map_sub _ (map_sub τ), Matrix.map_one _ (map_zero τ) (map_one τ)]
  have e2 : (1 + X).map τ = 1 + X.map τ := by rw [Matrix.map_add _ (map_add τ), Matrix.map_one _ (map_zero τ) (map_one τ)]
  refine ⟨(1 + X) * (1 - X)⁻¹, ?_⟩
  show ((1 + X) * (1 - X)⁻¹).map τ = (1 + X.map τ) * (1 - X.map τ)⁻¹
  rw [Matrix.map_mul, e2, map_inv_of τ _ (e1 ▸ hu), e1]

/- English proof (translation)
Rewrite `hX` using `[inU_iff]`. Establish `e : (X.map σ).map τ = (X.map τ).map star` using `by ext i j; exact h.2.2.2 τ (X i j)`. Apply `Matrix.map_injective τ.injective` to reduce the goal to its premises. Use `show (Xᵀ * QR E n ε * X.map σ).map τ = (QR E n ε).map τ`. Rewrite using `[Matrix.map_mul, Matrix.map_mul, e, Matrix.transpose_map, QR_map]`.

Conclude with `hX`.
-/
theorem rat_unitary (h : IsCMExt F E σ) (τ : E →+* ℂ) (ε : ℤˣ) (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E)
    (hX : InU (Qc n ε)ᵀ (X.map τ)) : Xᵀ * QR E n ε * X.map σ = QR E n ε := by
  rw [inU_iff] at hX
  have e : (X.map σ).map τ = (X.map τ).map star := by ext i j; exact h.2.2.2 τ (X i j)
  apply Matrix.map_injective τ.injective
  show (Xᵀ * QR E n ε * X.map σ).map τ = (QR E n ε).map τ
  rw [Matrix.map_mul, Matrix.map_mul, e, Matrix.transpose_map, QR_map]
  exact hX

/- English proof (translation)
Take `⟨h', hV', ⟨X, rfl⟩, hU⟩` from `densG (J_herm ε) (eps_sq ε ℂ) (J_sq ε) (eps_ne ε) (eps_star ε) (dense_ratS h τ) (proj_ratS h τ ε) (cay_ratS τ) hV h0V h0U`. Conclude with `⟨X, hV', hU⟩`.
-/
theorem dense_pts (h : IsCMExt F E σ) (τ : E →+* ℂ) (ε : ℤˣ) {V : Set (M2 n)} (hV : IsOpen V) {h0 : M2 n}
    (h0V : h0 ∈ V) (h0U : InU (Qc n ε)ᵀ h0) :
    ∃ X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E, X.map τ ∈ V ∧ InU (Qc n ε)ᵀ (X.map τ) := by
  obtain ⟨h', hV', ⟨X, rfl⟩, hU⟩ := densG (J_herm ε) (eps_sq ε ℂ) (J_sq ε) (eps_ne ε) (eps_star ε) (dense_ratS h τ)
    (proj_ratS h τ ε) (cay_ratS τ) hV h0V h0U
  exact ⟨X, hV', hU⟩

end PositivityTheory.SiegelWeilFormula.Krd.DM

end
