import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulEqOfRangeLe
import GroundTheory.AutomorphicForms.AnisotropicHeight
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.TorusCh

/- English proof (translation)
Establish `h1 : ((p.map (conjE E))ᵀ * D * p) *ᵥ b = (p.map (conjE E))ᵀ *ᵥ (D *ᵥ (p *ᵥ b))`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mul_assoc]`. Rewrite using `[h1, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[RingHom.map_mulVec]`.
-/
theorem pair_range_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
    (D p : Matrix (Fin n) (Fin n) E) (a b : Fin n → E) :
    ∑ i, conjE E ((p *ᵥ a) i) * (D *ᵥ (p *ᵥ b)) i =
      (conjE E ∘ a) ⬝ᵥ (((p.map (conjE E))ᵀ * D * p) *ᵥ b) := by
  have h1 : ((p.map (conjE E))ᵀ * D * p) *ᵥ b = (p.map (conjE E))ᵀ *ᵥ (D *ᵥ (p *ᵥ b)) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mul_assoc]
  rw [h1, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RingHom.map_mulVec]

/- English proof (translation)
Establish `hd1 : d.val * (d⁻¹ : GL (Fin n) E).val = 1` using `Units.mul_inv d`. Establish `hd2 : (d⁻¹ : GL (Fin n) E).val * d.val = 1` using `Units.inv_mul d`. Establish `hsg : sg d π * π = d.val * ((π.map (conjE E))ᵀ * (d⁻¹ : GL (Fin n) E).val * π)`. Simplify using `only [sg, mul_assoc]`. Establish `hM : sg d π * π = 0 ↔ (π.map (conjE E))ᵀ * (d⁻¹ : GL (Fin n) E).val * π = 0`.

Rewrite using `[hsg]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h2` using `congrArg (fun X => (d⁻¹ : GL (Fin n) E).val * X) h`. Simplify `h2` using `[← mul_assoc, hd2]`.

Introduce `h`. Rewrite using `[h, mul_zero]`. Rewrite using `[hM]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Use extensionality with `i j`. Establish `hv : π *ᵥ Pi.single j 1 ∈ perpD (conjE E) d (LinearMap.range (Matrix.toLin' π))` using `h ⟨Pi.single j 1, by rw [Matrix.toLin'_apply]⟩`. Take `⟨y, hy, hyv⟩` from `hv`. Establish `hy' : ∀ x ∈ LinearMap.range (Matrix.toLin' π), ∑ k, conjE E (x k) * y k = 0` using `hy`. Establish `hyd : y = (d⁻¹ : GL (Fin n) E).val *ᵥ (π *ᵥ Pi.single j 1)`.

Rewrite using `[← hyv, Matrix.toLin'_apply, Matrix.mulVec_mulVec, hd2, Matrix.one_mulVec]`. Establish `h3` using `hy' (π *ᵥ Pi.single i 1) ⟨Pi.single i 1, by rw [Matrix.toLin'_apply]⟩`. Rewrite `h3` using `[hyd, pair_range_eq]`. Establish `hc : (conjE E ∘ (Pi.single i 1 : Fin n → E)) = Pi.single i 1`. Use function extensionality and compare the values at `k`.

Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, hk]`. Rewrite `h3` using `[hc, single_one_dotProduct, Matrix.mulVec_single_one]`.

Simplify using `using h3`. Introduce and unpack `h _ ⟨b, rfl⟩`. Use `⟨(d⁻¹ : GL (Fin n) E).val *ᵥ (π *ᵥ b), ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨a, rfl⟩`. Simplify using `only [Matrix.toLin'_apply]`.

Rewrite using `[pair_range_eq, h, Matrix.zero_mulVec, dotProduct_zero]`. Rewrite using `[Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec, hd1, Matrix.one_mulVec]`.
-/
theorem iso_range_iff_sg_mul (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (d : GL (Fin n) E) (π : Matrix (Fin n) (Fin n) E) :
    LinearMap.range (Matrix.toLin' π) ≤ perpD (conjE E) d (LinearMap.range (Matrix.toLin' π)) ↔
      sg d π * π = 0 := by
  have hd1 : d.val * (d⁻¹ : GL (Fin n) E).val = 1 := Units.mul_inv d
  have hd2 : (d⁻¹ : GL (Fin n) E).val * d.val = 1 := Units.inv_mul d
  have hsg : sg d π * π = d.val * ((π.map (conjE E))ᵀ * (d⁻¹ : GL (Fin n) E).val * π) := by
    simp only [sg, mul_assoc]
  have hM : sg d π * π = 0 ↔ (π.map (conjE E))ᵀ * (d⁻¹ : GL (Fin n) E).val * π = 0 := by
    rw [hsg]
    constructor
    · intro h
      have h2 := congrArg (fun X => (d⁻¹ : GL (Fin n) E).val * X) h
      simpa [← mul_assoc, hd2] using h2
    · intro h
      rw [h, mul_zero]
  rw [hM]
  constructor
  · intro h
    ext i j
    have hv : π *ᵥ Pi.single j 1 ∈ perpD (conjE E) d (LinearMap.range (Matrix.toLin' π)) :=
      h ⟨Pi.single j 1, by rw [Matrix.toLin'_apply]⟩
    obtain ⟨y, hy, hyv⟩ := hv
    have hy' : ∀ x ∈ LinearMap.range (Matrix.toLin' π), ∑ k, conjE E (x k) * y k = 0 := hy
    have hyd : y = (d⁻¹ : GL (Fin n) E).val *ᵥ (π *ᵥ Pi.single j 1) := by
      rw [← hyv, Matrix.toLin'_apply, Matrix.mulVec_mulVec, hd2, Matrix.one_mulVec]
    have h3 := hy' (π *ᵥ Pi.single i 1) ⟨Pi.single i 1, by rw [Matrix.toLin'_apply]⟩
    rw [hyd, pair_range_eq] at h3
    have hc : (conjE E ∘ (Pi.single i 1 : Fin n → E)) = Pi.single i 1 := by
      funext k
      by_cases hk : k = i
      · subst hk; simp
      · simp [Pi.single_apply, hk]
    rw [hc, single_one_dotProduct, Matrix.mulVec_single_one] at h3
    simpa using h3
  · rintro h _ ⟨b, rfl⟩
    refine ⟨(d⁻¹ : GL (Fin n) E).val *ᵥ (π *ᵥ b), ?_, ?_⟩
    · rintro _ ⟨a, rfl⟩
      simp only [Matrix.toLin'_apply]
      rw [pair_range_eq, h, Matrix.zero_mulVec, dotProduct_zero]
    · rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec, hd1, Matrix.one_mulVec]

end GlobalTheory.CompanionTheory.TorusCh
