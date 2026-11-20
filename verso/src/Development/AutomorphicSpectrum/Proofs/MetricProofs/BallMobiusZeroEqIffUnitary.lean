import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Stab

variable {j j' : ℕ}

/- English proof (translation)
Unfold `IsSgU sgI at h`. Rewrite `h` using `[fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]`. Take `⟨h1, h2, -, h4⟩` from `fromBlocks_inj.1 h`. Simplify using `only [Matrix.mul_one, Matrix.mul_zero, Matrix.mul_neg, add_zero, zero_add] at h1 h2 h4`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Simplify `h1` using `[sub_eq_add_neg]`. Simplify `h2` using `[sub_eq_add_neg]`. Simplify `h4` using `[sub_eq_add_neg]`.
-/
theorem sg_fb {a : Matrix (Fin j) (Fin j) ℂ} {b : Matrix (Fin j) (Fin j') ℂ}
    {c : Matrix (Fin j') (Fin j) ℂ} {d : Matrix (Fin j') (Fin j') ℂ}
    (h : IsSgU (fromBlocks a b c d)) :
    aᴴ * a - cᴴ * c = 1 ∧ aᴴ * b - cᴴ * d = 0 ∧ bᴴ * b - dᴴ * d = -1 := by
  unfold IsSgU sgI at h
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply] at h
  obtain ⟨h1, h2, -, h4⟩ := fromBlocks_inj.1 h
  simp only [Matrix.mul_one, Matrix.mul_zero, Matrix.mul_neg, add_zero, zero_add] at h1 h2 h4
  refine ⟨?_, ?_, ?_⟩
  · simpa [sub_eq_add_neg] using h1
  · simpa [sub_eq_add_neg] using h2
  · simpa [sub_eq_add_neg] using h4

/- English proof (translation)
Establish `e : aᴴ * a = 1 + cᴴ * c` using `by rw [← h]; abel`. Establish `pd : (aᴴ * a).PosDef`. Rewrite using `[e]`. Conclude with `Matrix.PosDef.one.add_posSemidef (Matrix.posSemidef_conjTranspose_mul_self c)`. Establish `hu : IsUnit (aᴴ * a).det` using `(Matrix.isUnit_iff_isUnit_det _).1 pd.isUnit`.

Rewrite `hu` using `[Matrix.det_mul]`. Conclude with `isUnit_of_mul_isUnit_right hu`.
-/
theorem unit_of_rel {a : Matrix (Fin j) (Fin j) ℂ} {c : Matrix (Fin j') (Fin j) ℂ}
    (h : aᴴ * a - cᴴ * c = 1) : IsUnit a.det := by
  have e : aᴴ * a = 1 + cᴴ * c := by rw [← h]; abel
  have pd : (aᴴ * a).PosDef := by
    rw [e]
    exact Matrix.PosDef.one.add_posSemidef (Matrix.posSemidef_conjTranspose_mul_self c)
  have hu : IsUnit (aᴴ * a).det := (Matrix.isUnit_iff_isUnit_det _).1 pd.isUnit
  rw [Matrix.det_mul] at hu
  exact isUnit_of_mul_isUnit_right hu

/- English proof (translation)
Unfold `sgI`. Rewrite using `[fromBlocks_multiply]`. Simplify using the standard rewrite rules.
-/
theorem sgI_mul_self : sgI j j' * sgI j j' = 1 := by
  unfold sgI
  rw [fromBlocks_multiply]
  simp

/- English proof (translation)
Unfold `IsSgU at *`. Rewrite using `[conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = sgI j j' := by rw [hu, hv]`.
-/
theorem IsSgU.mul {u v : Matrix (Sg j j') (Sg j j') ℂ} (hu : IsSgU u) (hv : IsSgU v) : IsSgU (u * v) := by
  unfold IsSgU at *
  rw [conjTranspose_mul]
  calc vᴴ * uᴴ * sgI j j' * (u * v) = vᴴ * (uᴴ * sgI j j' * u) * v := by
        simp only [Matrix.mul_assoc]
    _ = sgI j j' := by rw [hu, hv]

/- English proof (translation)
Establish `: (sgI j j' * uᴴ * sgI j j') * u = 1`. Establish `e : sgI j j' * uᴴ * sgI j j' * u = sgI j j' * (uᴴ * sgI j j' * u)`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[e, show uᴴ * sgI j j' * u = sgI j j' from hu, sgI_mul_self]`. Conclude with `Matrix.isUnit_det_of_left_inverse this`.
-/
theorem IsSgU.det_unit {u : Matrix (Sg j j') (Sg j j') ℂ} (hu : IsSgU u) : IsUnit u.det := by
  have : (sgI j j' * uᴴ * sgI j j') * u = 1 := by
    have e : sgI j j' * uᴴ * sgI j j' * u = sgI j j' * (uᴴ * sgI j j' * u) := by
      simp only [Matrix.mul_assoc]
    rw [e, show uᴴ * sgI j j' * u = sgI j j' from hu, sgI_mul_self]
  exact Matrix.isUnit_det_of_left_inverse this

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `sg_fb h`. Rewrite using `[fromBlocks_conjTranspose, fromBlocks_multiply, ← fromBlocks_one]`. Prove the components needed by the constructor for the conclusion. Introduce `e`. Take `⟨e1, -, -, -⟩` from `fromBlocks_inj.1 e`.

Establish `hz : (2 : ℂ) • (rᴴ * r) = 0`. Establish `: rᴴ * r + rᴴ * r = 0`. Use `sub_eq_zero.2 (e1.trans h1.symm)` as an intermediate fact. Rewrite using `[← this]`. Normalize the expressions using the abelian group laws.

Rewrite using `[two_smul]`. Conclude with `this`. Establish `hz' : rᴴ * r = 0` using `(smul_eq_zero.1 hz).resolve_left two_ne_zero`. Conclude with `conjTranspose_mul_self_eq_zero.1 hz'`. Introduce and unpack `rfl`.

Simplify using `only [conjTranspose_zero, Matrix.zero_mul, sub_zero, add_zero] at h1 h2 h3 ⊢`. Establish `hp : p * pᴴ = 1` using `mul_eq_one_comm.1 h1`. Establish `hb : b = 0`. Establish `: p * (pᴴ * b) = b` using `by rw [← Matrix.mul_assoc, hp, Matrix.one_mul]`. Rewrite using `[← this, h2, Matrix.mul_zero]`.

Substitute `hb` using the available equality. Simplify using `only [conjTranspose_zero, Matrix.zero_mul, zero_sub, neg_inj] at h3`. Simplify using `[h1, h3]`.
-/
theorem unitary_iff_fb {p : Matrix (Fin j) (Fin j) ℂ} {b : Matrix (Fin j) (Fin j') ℂ}
    {r : Matrix (Fin j') (Fin j) ℂ} {s : Matrix (Fin j') (Fin j') ℂ}
    (h : IsSgU (fromBlocks p b r s)) :
    (fromBlocks p b r s)ᴴ * fromBlocks p b r s = 1 ↔ r = 0 := by
  obtain ⟨h1, h2, h3⟩ := sg_fb h
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, ← fromBlocks_one]
  constructor
  · intro e
    obtain ⟨e1, -, -, -⟩ := fromBlocks_inj.1 e
    have hz : (2 : ℂ) • (rᴴ * r) = 0 := by
      have : rᴴ * r + rᴴ * r = 0 := by
        have := sub_eq_zero.2 (e1.trans h1.symm)
        rw [← this]; abel
      rw [two_smul]; exact this
    have hz' : rᴴ * r = 0 := (smul_eq_zero.1 hz).resolve_left two_ne_zero
    exact conjTranspose_mul_self_eq_zero.1 hz'
  · rintro rfl
    simp only [conjTranspose_zero, Matrix.zero_mul, sub_zero, add_zero] at h1 h2 h3 ⊢
    have hp : p * pᴴ = 1 := mul_eq_one_comm.1 h1
    have hb : b = 0 := by
      have : p * (pᴴ * b) = b := by rw [← Matrix.mul_assoc, hp, Matrix.one_mul]
      rw [← this, h2, Matrix.mul_zero]
    subst hb
    simp only [conjTranspose_zero, Matrix.zero_mul, zero_sub, neg_inj] at h3
    simp [h1, h3]

/- English proof (translation)
Establish `ha : IsUnit a.det` using `unit_of_rel (sg_fb hu).1`. Establish `hp : IsUnit p.det` using `unit_of_rel (sg_fb hv).1`. Establish `hw : IsUnit (a * p + b * r).det`. Use `IsSgU.mul hu hv` as an intermediate fact. Rewrite `this` using `[fromBlocks_multiply]`.

Conclude with `unit_of_rel (sg_fb this).1`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h' : c * a⁻¹ * (a * p + b * r) = c * p + d * r`. Rewrite using `[h, Matrix.nonsing_inv_mul_cancel_right _ _ hw]`.

Establish `hs : (d - c * a⁻¹ * b) * r = 0`. Establish `e1 : c * a⁻¹ * (a * p + b * r) = c * p + c * a⁻¹ * b * r`. Rewrite using `[Matrix.mul_add, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_right _ _ ha, Matrix.mul_assoc (c * a⁻¹) b r]`. Rewrite `h'` using `[e1]`. Establish `: c * a⁻¹ * b * r = d * r` using `add_left_cancel h'`.

Rewrite using `[Matrix.sub_mul, this, sub_self]`. Establish `hS : IsUnit (d - c * a⁻¹ * b).det`. Establish `hd` using `IsSgU.det_unit hu`. Use `letI := Matrix.invertibleOfIsUnitDet a ha`. Rewrite `hd` using `[Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv]`.

Conclude with `isUnit_of_mul_isUnit_right hd`. Establish `: (d - c * a⁻¹ * b)⁻¹ * ((d - c * a⁻¹ * b) * r) = r` using `Matrix.nonsing_inv_mul_cancel_left _ _ hS`. Rewrite using `[← this, hs, Matrix.mul_zero]`. Introduce and unpack `rfl`. Simplify using `only [Matrix.mul_zero, add_zero]`.

Rewrite using `[Matrix.mul_inv_rev, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ hp]`.
-/
theorem single_fb {a p : Matrix (Fin j) (Fin j) ℂ} {b e : Matrix (Fin j) (Fin j') ℂ}
    {c r : Matrix (Fin j') (Fin j) ℂ} {d s : Matrix (Fin j') (Fin j') ℂ}
    (hu : IsSgU (fromBlocks a b c d)) (hv : IsSgU (fromBlocks p e r s)) :
    c * a⁻¹ = (c * p + d * r) * (a * p + b * r)⁻¹ ↔ r = 0 := by
  have ha : IsUnit a.det := unit_of_rel (sg_fb hu).1
  have hp : IsUnit p.det := unit_of_rel (sg_fb hv).1
  have hw : IsUnit (a * p + b * r).det := by
    have := IsSgU.mul hu hv
    rw [fromBlocks_multiply] at this
    exact unit_of_rel (sg_fb this).1
  constructor
  · intro h
    have h' : c * a⁻¹ * (a * p + b * r) = c * p + d * r := by
      rw [h, Matrix.nonsing_inv_mul_cancel_right _ _ hw]
    have hs : (d - c * a⁻¹ * b) * r = 0 := by
      have e1 : c * a⁻¹ * (a * p + b * r) = c * p + c * a⁻¹ * b * r := by
        rw [Matrix.mul_add, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_right _ _ ha, Matrix.mul_assoc (c * a⁻¹) b r]
      rw [e1] at h'
      have : c * a⁻¹ * b * r = d * r := add_left_cancel h'
      rw [Matrix.sub_mul, this, sub_self]
    have hS : IsUnit (d - c * a⁻¹ * b).det := by
      have hd := IsSgU.det_unit hu
      letI := Matrix.invertibleOfIsUnitDet a ha
      rw [Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv] at hd
      exact isUnit_of_mul_isUnit_right hd
    have : (d - c * a⁻¹ * b)⁻¹ * ((d - c * a⁻¹ * b) * r) = r :=
      Matrix.nonsing_inv_mul_cancel_left _ _ hS
    rw [← this, hs, Matrix.mul_zero]
  · rintro rfl
    simp only [Matrix.mul_zero, add_zero]
    rw [Matrix.mul_inv_rev, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ hp]

/- English proof (translation)
Take `⟨a, b, c, d, rfl⟩ : ∃ a b c d, u = fromBlocks a b c d` from `⟨_, _, _, _, (fromBlocks_toBlocks u).symm⟩`. Take `⟨p, e, r, s, rfl⟩ : ∃ a b c d, v = fromBlocks a b c d` from `⟨_, _, _, _, (fromBlocks_toBlocks v).symm⟩`. Rewrite using `[unitary_iff_fb hv, ← single_fb hu hv, fromBlocks_multiply]`. Simplify using `only [toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₁₁]`.
-/
theorem single {u v : Matrix (Sg j j') (Sg j j') ℂ} (hu : IsSgU u) (hv : IsSgU v) :
    u.toBlocks₂₁ * u.toBlocks₁₁⁻¹ = (u * v).toBlocks₂₁ * (u * v).toBlocks₁₁⁻¹ ↔ vᴴ * v = 1 := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d, u = fromBlocks a b c d :=
    ⟨_, _, _, _, (fromBlocks_toBlocks u).symm⟩
  obtain ⟨p, e, r, s, rfl⟩ : ∃ a b c d, v = fromBlocks a b c d :=
    ⟨_, _, _, _, (fromBlocks_toBlocks v).symm⟩
  rw [unitary_iff_fb hv, ← single_fb hu hv, fromBlocks_multiply]
  simp only [toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₁₁]

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Use extensionality with `i' i`. Use `congrFun h (q (τ, i, i'))` as an intermediate fact. Simplify `this` using `[ballPt]`.
-/
theorem ballPt_inj {Ψ : Type} {n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n)
    {W W' : Ψ → Matrix (Fin j') (Fin j) ℂ} (h : ballPt q W = ballPt q W') : W = W' := by
  funext τ
  ext i' i
  have := congrFun h (q (τ, i, i'))
  simpa [ballPt] using this

/- English proof (translation)
Establish `hb : ∀ τ, (ballMat q (0 : Fin n → ℂ) τ)ᵀ = 0`. Introduce `τ`. Use extensionality with `a b`. Simplify using `[ballMat]`. Unfold `moebBall`.

Use `congr 1`. Use function extensionality and compare the values at `τ`. Rewrite using `[hb τ]`. Simplify using `[moebW]`.
-/
theorem moebBall_zero {Ψ : Type} [Fintype Ψ] {n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n)
    (w : Ψ → Matrix (Sg j j') (Sg j j') ℂ) :
    moebBall q w 0 = ballPt q fun τ => (w τ).toBlocks₂₁ * (w τ).toBlocks₁₁⁻¹ := by
  have hb : ∀ τ, (ballMat q (0 : Fin n → ℂ) τ)ᵀ = 0 := by
    intro τ
    ext a b
    simp [ballMat]
  unfold moebBall
  congr 1
  funext τ
  rw [hb τ]
  simp [moebW]

/- English proof (translation)
Introduce `Ψ _ j j' n q u v hu hv`. Rewrite using `[moebBall_zero, moebBall_zero]`. Prove the components needed by the constructor for the conclusion. Introduce `h τ`. Conclude with `(single (hu τ) (hv τ)).1 (congrFun (ballPt_inj q h) τ)`.

Introduce `h`. Use `congr 1`. Use function extensionality and compare the values at `τ`. Conclude with `(single (hu τ) (hv τ)).2 (h τ)`.
-/
theorem moebBall_zero_iff : ∀ (Ψ : Type) [Fintype Ψ] (j j' n : ℕ) (q : Ψ × Fin j × Fin j' ≃ Fin n) (u v : Ψ → Matrix (Sg j j') (Sg j j') ℂ), (∀ τ, IsSgU (u τ)) → (∀ τ, IsSgU (v τ)) → (moebBall q u 0 = moebBall q (fun τ => u τ * v τ) 0 ↔ ∀ τ, (v τ)ᴴ * v τ = 1) := by
  intro Ψ _ j j' n q u v hu hv
  rw [moebBall_zero, moebBall_zero]
  constructor
  · intro h τ
    exact (single (hu τ) (hv τ)).1 (congrFun (ballPt_inj q h) τ)
  · intro h
    congr 1
    funext τ
    exact (single (hu τ) (hv τ)).2 (h τ)

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Stab
