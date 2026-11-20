import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.ApartOfNotMem
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open GlobalTheory.SplitPts (conjE)
open GroundTheory.Global.AdeleBaseChange (finiteAdeleMap)
open scoped TensorProduct

namespace UpperTheory.Gal.W2.Seed

/- English proof (translation)
Use extensionality with `i k`. Establish `h : algebraMap R (R ⊗[ℚ] Matrix (Fin n) (Fin n) E) r = r ⊗ₜ[ℚ] (1 : Matrix (Fin n) (Fin n) E)` using `rfl`. Rewrite using `[h, hμ r 1 i k]`. Distinguish the cases in `hik : i = k`. Substitute `hik` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Matrix.one_apply, hik]`.
-/
private theorem mu_algebraMap {R E : Type} [CommRing R] [Algebra ℚ R] [Field E] [NumberField E] {n : ℕ}
    (μ : R ⊗[ℚ] Matrix (Fin n) (Fin n) E ≃+* Matrix (Fin n) (Fin n) (R ⊗[ℚ] E)) (hμ : IsMu μ) (r : R) :
    μ (algebraMap R (R ⊗[ℚ] Matrix (Fin n) (Fin n) E) r) =
      (r ⊗ₜ[ℚ] (1 : E)) • (1 : Matrix (Fin n) (Fin n) (R ⊗[ℚ] E)) := by
  ext i k
  have h : algebraMap R (R ⊗[ℚ] Matrix (Fin n) (Fin n) E) r = r ⊗ₜ[ℚ] (1 : Matrix (Fin n) (Fin n) E) := rfl
  rw [h, hμ r 1 i k]
  by_cases hik : i = k
  · subst hik; simp
  · simp [Matrix.one_apply, hik]

/- English proof (translation)
Use `set b : Matrix (Fin n) (Fin n) K := ((a⁻¹).val.map σ)ᵀ with hb`. Establish `h1 : (a.val.map σ)ᵀ * b = 1`. Rewrite using `[hb, ← Matrix.transpose_mul, ← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one]`. Establish `h1' : b * (a.val.map σ)ᵀ = 1`. Rewrite using `[hb, ← Matrix.transpose_mul, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one]`.

Establish `hD : D = b * (a⁻¹).val`. Combine the equalities or inequalities in the displayed calculation. Establish `e : ((a * g * a⁻¹).val.map σ)ᵀ = b * (g.val.map σ)ᵀ * (a.val.map σ)ᵀ`. Simplify using `only [Units.val_mul, Matrix.map_mul, Matrix.transpose_mul, hb, Matrix.mul_assoc]`. Rewrite using `[e]`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Units.val_mul, Matrix.mul_assoc]`. Use `_ = b * ((g.val.map σ)ᵀ * g.val) * (a⁻¹).val := by`. Rewrite using `[ha, Matrix.mul_one]`. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = c • D := by`. Rewrite using `[hg, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, ← hD]`.
-/
private theorem conj_form {K : Type} [CommRing K] (σ : K →+* K) {n : ℕ} (D : Matrix (Fin n) (Fin n) K)
    (a g : GL (Fin n) K) (c : K) (ha : (a.val.map σ)ᵀ * D * a.val = 1)
    (hg : (g.val.map σ)ᵀ * g.val = c • (1 : Matrix (Fin n) (Fin n) K)) :
    ((a * g * a⁻¹).val.map σ)ᵀ * D * (a * g * a⁻¹).val = c • D := by
  set b : Matrix (Fin n) (Fin n) K := ((a⁻¹).val.map σ)ᵀ with hb
  have h1 : (a.val.map σ)ᵀ * b = 1 := by
    rw [hb, ← Matrix.transpose_mul, ← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one]
  have h1' : b * (a.val.map σ)ᵀ = 1 := by
    rw [hb, ← Matrix.transpose_mul, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one]
  have hD : D = b * (a⁻¹).val := by
    calc D = (b * (a.val.map σ)ᵀ) * D * (a.val * (a⁻¹).val) := by rw [h1', Units.mul_inv]; simp
      _ = b * ((a.val.map σ)ᵀ * D * a.val) * (a⁻¹).val := by simp only [Matrix.mul_assoc]
      _ = b * (a⁻¹).val := by rw [ha, Matrix.mul_one]
  have e : ((a * g * a⁻¹).val.map σ)ᵀ = b * (g.val.map σ)ᵀ * (a.val.map σ)ᵀ := by
    simp only [Units.val_mul, Matrix.map_mul, Matrix.transpose_mul, hb, Matrix.mul_assoc]
  rw [e]
  calc b * (g.val.map σ)ᵀ * (a.val.map σ)ᵀ * D * (a * g * a⁻¹).val
      = b * (g.val.map σ)ᵀ * ((a.val.map σ)ᵀ * D * a.val) * g.val * (a⁻¹).val := by
        simp only [Units.val_mul, Matrix.mul_assoc]
    _ = b * ((g.val.map σ)ᵀ * g.val) * (a⁻¹).val := by
        rw [ha, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = c • D := by
        rw [hg, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, ← hD]

/- English proof (translation)
Use `set x' := (starT (hermStar (A.H n) (A.det_ne n)) R (u : R ⊗[ℚ] Matrix (Fin n) (Fin n) E)).unop with hx'`. Establish `h1` using `hst R E A n μ hμ u`. Establish `hne : ∀ i, ((A.dg n i : 𝓞 E) : E) ≠ 0` using `fun i => by`. Use `A.c_ne` as an intermediate fact. Apply the tactic sequence `unfold Arith.dg; split_ifs <;> simp [this]`.

Establish `hDi : Matrix.diagonal (fun i => (1 : R) ⊗ₜ[ℚ] ((A.dg n i : E))⁻¹) * Matrix.diagonal (fun i => (1 : R) ⊗ₜ[ℚ] (A.dg n i : E)) = 1`. Rewrite using `[Matrix.diagonal_mul_diagonal]`. Simplify using `only [Algebra.TensorProduct.tmul_mul_tmul, mul_one]`. Establish `: ∀ i, ((A.dg n i : E))⁻¹ * (A.dg n i : E) = 1` using `fun i => inv_mul_cancel₀ (hne i)`. Simplify using `only [this]`.

Conclude with `Matrix.diagonal_one`. Establish `h2 : Matrix.diagonal (fun i => (1 : R) ⊗ₜ[ℚ] (A.dg n i : E)) * (μ x' * μ u) = Matrix.diagonal (fun i => (1 : R) ⊗ₜ[ℚ] (A.dg n i : E)) * ((s ⊗ₜ[ℚ] (1 : E)) • 1)`. Rewrite using `[← Matrix.mul_assoc, h1, h, Matrix.mul_smul, Matrix.mul_one]`. Establish `h3 : μ x' * μ u = (s ⊗ₜ[ℚ] (1 : E)) • (1 : Matrix (Fin n) (Fin n) (R ⊗[ℚ] E))`. Use `congrArg (fun M => Matrix.diagonal (fun i => (1 : R) ⊗ₜ[ℚ] ((A.dg n i : E))⁻¹) * M) h2` as an intermediate fact.

Simplify `this` using `only [← Matrix.mul_assoc, hDi, Matrix.one_mul]`. Establish `h4 : x' * (u : R ⊗[ℚ] Matrix (Fin n) (Fin n) E) = algebraMap R _ s` using `μ.injective (by rw [map_mul, h3, mu_algebraMap μ hμ])`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mul_assoc, Units.mul_inv, mul_one]`. Use `_ = algebraMap R _ s := by`.

Rewrite using `[h4, ← Algebra.commutes, mul_assoc, Units.mul_inv, mul_one]`.
-/
private theorem key {R E : Type} [CommRing R] [Algebra ℚ R] [Field E] [NumberField E] [IsCMField E]
    (hst : MuStar) (A : Arith E) {n : ℕ}
    (μ : R ⊗[ℚ] Matrix (Fin n) (Fin n) E ≃+* Matrix (Fin n) (Fin n) (R ⊗[ℚ] E)) (hμ : IsMu μ)
    (u : (R ⊗[ℚ] Matrix (Fin n) (Fin n) E)ˣ) (s : R)
    (h : ((μ u).map (conjT E R))ᵀ * Matrix.diagonal (fun i => (1 : R) ⊗ₜ[ℚ] (A.dg n i : E)) * μ u =
      (s ⊗ₜ[ℚ] (1 : E)) • Matrix.diagonal (fun i => (1 : R) ⊗ₜ[ℚ] (A.dg n i : E))) :
    (u : R ⊗[ℚ] Matrix (Fin n) (Fin n) E) * (starT (hermStar (A.H n) (A.det_ne n)) R u).unop =
      algebraMap R _ s := by
  set x' := (starT (hermStar (A.H n) (A.det_ne n)) R (u : R ⊗[ℚ] Matrix (Fin n) (Fin n) E)).unop with hx'
  have h1 := hst R E A n μ hμ u
  have hne : ∀ i, ((A.dg n i : 𝓞 E) : E) ≠ 0 := fun i => by
    have := A.c_ne
    unfold Arith.dg; split_ifs <;> simp [this]
  have hDi : Matrix.diagonal (fun i => (1 : R) ⊗ₜ[ℚ] ((A.dg n i : E))⁻¹) *
      Matrix.diagonal (fun i => (1 : R) ⊗ₜ[ℚ] (A.dg n i : E)) = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    have : ∀ i, ((A.dg n i : E))⁻¹ * (A.dg n i : E) = 1 := fun i => inv_mul_cancel₀ (hne i)
    simp only [this]
    exact Matrix.diagonal_one
  have h2 : Matrix.diagonal (fun i => (1 : R) ⊗ₜ[ℚ] (A.dg n i : E)) * (μ x' * μ u) =
      Matrix.diagonal (fun i => (1 : R) ⊗ₜ[ℚ] (A.dg n i : E)) * ((s ⊗ₜ[ℚ] (1 : E)) • 1) := by
    rw [← Matrix.mul_assoc, h1, h, Matrix.mul_smul, Matrix.mul_one]
  have h3 : μ x' * μ u = (s ⊗ₜ[ℚ] (1 : E)) • (1 : Matrix (Fin n) (Fin n) (R ⊗[ℚ] E)) := by
    have := congrArg (fun M => Matrix.diagonal (fun i => (1 : R) ⊗ₜ[ℚ] ((A.dg n i : E))⁻¹) * M) h2
    simpa only [← Matrix.mul_assoc, hDi, Matrix.one_mul] using this
  have h4 : x' * (u : R ⊗[ℚ] Matrix (Fin n) (Fin n) E) = algebraMap R _ s :=
    μ.injective (by rw [map_mul, h3, mu_algebraMap μ hμ])
  calc (u : R ⊗[ℚ] Matrix (Fin n) (Fin n) E) * x'
      = u * (x' * u) * (↑u⁻¹ : R ⊗[ℚ] Matrix (Fin n) (Fin n) E) := by
        simp only [mul_assoc, Units.mul_inv, mul_one]
    _ = algebraMap R _ s := by
        rw [h4, ← Algebra.commutes, mul_assoc, Units.mul_inv, mul_one]

/- English proof (translation)
Introduce `hst E _ _ _ A n p _ S T μ hμ a ha`. Set `m : GUf E n →* (AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E)` to `{ toFun := fun g => μ.symm ((a * mat g * a⁻¹).val.map T.Φ) map_one' := by`. Simplify using `only [map_one, mul_one, mul_inv_cancel, Units.val_one]`. Rewrite using `[Matrix.map_one _ (map_zero _) (map_one _), map_one]`. Use the proof step `map_mul' := fun g h => by`.

Rewrite using `[← map_mul, ← Matrix.map_mul]`. Use `congr 2`. Simplify using `only [map_mul, Units.val_mul, Matrix.mul_assoc, Units.inv_mul_cancel_left] }`. Establish `hm : ∀ g, μ (m g) = (a * mat g * a⁻¹).val.map T.Φ` using `fun g => μ.apply_symm_apply _`. Set `f₁ : GUf E n →* (AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E)ˣ` to `m.toHomUnits`.

Set `f₂ : GUf E n →* (AfP p)ˣ` to `(Units.map (T.ρ : AfQ →* AfP p)).comp sim`. Establish `mem : ∀ g, (f₁.prod f₂) g ∈ UPts (hermStar (A.H n) (A.det_ne n)) (AfP p)`. Introduce `g`. Use `show ((f₁ g : (AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E)ˣ) : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E) * (starT (hermStar (A.H n) (A.det_ne n)) (AfP p) ((f₁ g : (AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E)ˣ) : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E)).unop = algebraMap (AfP p) _ (T.ρ (sim g : AfQˣ))`. Apply `key hst A μ hμ` to reduce the goal to its premises.

Establish `hf : μ ((f₁ g : (AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E)ˣ) : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E) = (a * mat g * a⁻¹).val.map T.Φ` using `hm g`. Rewrite using `[hf]`. Establish `h0` using `conj_form (conjFin (conjE E)) (Matrix.diagonal (fun i => algebraMap E (Af E) (A.dg n i : E))) a (mat g) (finiteAdeleMap ℚ E (sim g : AfQˣ)) ha.1 g.2`. Establish `h1` using `congrArg (fun M => M.map T.Φ) h0`. Establish `e1 : ((((a * mat g * a⁻¹).val.map (conjFin (conjE E)))ᵀ).map T.Φ) = (((a * mat g * a⁻¹).val.map T.Φ).map (conjT E (AfP p)))ᵀ`.

Use extensionality with `i k`. Conclude with `T.Φ_conj _`. Establish `e2 : (Matrix.diagonal (fun i => algebraMap E (Af E) (A.dg n i : E))).map T.Φ = Matrix.diagonal (fun i => (1 : AfP p) ⊗ₜ[ℚ] (A.dg n i : E))`. Rewrite using `[Matrix.diagonal_map (map_zero _)]`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Conclude with `T.Φ_E _`. Establish `e3 : (finiteAdeleMap ℚ E (sim g : AfQˣ) • Matrix.diagonal (fun i => algebraMap E (Af E) (A.dg n i : E))).map T.Φ = (T.ρ (sim g : AfQˣ) ⊗ₜ[ℚ] (1 : E)) • Matrix.diagonal (fun i => (1 : AfP p) ⊗ₜ[ℚ] (A.dg n i : E))`. Rewrite using `[← e2]`. Use extensionality with `i k`.

Simplify using `only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, T.Φ_Q]`. Simplify using `only [Matrix.map_mul] at h1`. Rewrite `h1` using `[e1, e2, e3]`. Conclude with `h1`. Use `⟨MonoidHom.codRestrict (f₁.prod f₂) (UPts S.G.star (AfP p)) mem, ?_, ?_⟩` and prove the remaining obligations.

Introduce `g`. Conclude with `hm g`. Introduce `g`. Both sides reduce to the same expression.
-/
theorem pJEx :
    MuStar → JEx := by
  intro hst E _ _ _ A n p _ S T μ hμ a ha
  let m : GUf E n →* (AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E) :=
    { toFun := fun g => μ.symm ((a * mat g * a⁻¹).val.map T.Φ)
      map_one' := by
        simp only [map_one, mul_one, mul_inv_cancel, Units.val_one]
        rw [Matrix.map_one _ (map_zero _) (map_one _), map_one]
      map_mul' := fun g h => by
        rw [← map_mul, ← Matrix.map_mul]
        congr 2
        simp only [map_mul, Units.val_mul, Matrix.mul_assoc, Units.inv_mul_cancel_left] }
  have hm : ∀ g, μ (m g) = (a * mat g * a⁻¹).val.map T.Φ := fun g => μ.apply_symm_apply _
  let f₁ : GUf E n →* (AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E)ˣ := m.toHomUnits
  let f₂ : GUf E n →* (AfP p)ˣ := (Units.map (T.ρ : AfQ →* AfP p)).comp sim
  have mem : ∀ g, (f₁.prod f₂) g ∈ UPts (hermStar (A.H n) (A.det_ne n)) (AfP p) := by
    intro g
    show ((f₁ g : (AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E)ˣ) : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E) *
        (starT (hermStar (A.H n) (A.det_ne n)) (AfP p)
          ((f₁ g : (AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E)ˣ) : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E)).unop =
      algebraMap (AfP p) _ (T.ρ (sim g : AfQˣ))
    apply key hst A μ hμ
    have hf : μ ((f₁ g : (AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E)ˣ) : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E) =
      (a * mat g * a⁻¹).val.map T.Φ := hm g
    rw [hf]
    have h0 := conj_form (conjFin (conjE E)) (Matrix.diagonal (fun i => algebraMap E (Af E) (A.dg n i : E))) a (mat g)
      (finiteAdeleMap ℚ E (sim g : AfQˣ)) ha.1 g.2
    have h1 := congrArg (fun M => M.map T.Φ) h0
    have e1 : ((((a * mat g * a⁻¹).val.map (conjFin (conjE E)))ᵀ).map T.Φ) =
        (((a * mat g * a⁻¹).val.map T.Φ).map (conjT E (AfP p)))ᵀ := by
      ext i k
      exact T.Φ_conj _
    have e2 : (Matrix.diagonal (fun i => algebraMap E (Af E) (A.dg n i : E))).map T.Φ =
        Matrix.diagonal (fun i => (1 : AfP p) ⊗ₜ[ℚ] (A.dg n i : E)) := by
      rw [Matrix.diagonal_map (map_zero _)]
      congr 1
      funext i
      exact T.Φ_E _
    have e3 : (finiteAdeleMap ℚ E (sim g : AfQˣ) •
        Matrix.diagonal (fun i => algebraMap E (Af E) (A.dg n i : E))).map T.Φ =
        (T.ρ (sim g : AfQˣ) ⊗ₜ[ℚ] (1 : E)) • Matrix.diagonal (fun i => (1 : AfP p) ⊗ₜ[ℚ] (A.dg n i : E)) := by
      rw [← e2]
      ext i k
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, T.Φ_Q]
    simp only [Matrix.map_mul] at h1
    rw [e1, e2, e3] at h1
    exact h1
  refine ⟨MonoidHom.codRestrict (f₁.prod f₂) (UPts S.G.star (AfP p)) mem, ?_, ?_⟩
  · intro g
    exact hm g
  · intro g
    rfl

end UpperTheory.Gal.W2.Seed
