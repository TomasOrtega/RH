import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PrimeProj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CharConj

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.LKTrip GlobalTheory.LKDef GlobalTheory.LKMid Formalism.BasicNotions
open UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

namespace UpperTheory.Gal.Int.Geo.Pl

/- English proof (translation)
Introduce `E _ _ _ n l d hn hd x hx U hU w₀ hw₀ hT Up hUp hu`. Take `⟨e, J, θ, χ, hJo, hJc, htf, -, -, hcusp, hφ⟩` from `hT`. Set `π : AutSub E n` to `⟨U, hU⟩`. Take `⟨W, hW⟩` from `(h1 E n hn π).1`. Set `m : InfinitePlace E → ℕ` to `fun v => ∑ i, ((W v).w i).natAbs`.

Establish `hm : ∀ v i, 0 ≤ (W v).w i + m v` using `fun v i => by`. Establish `: ((W v).w i).natAbs ≤ m v` using `Finset.single_le_sum (f := fun i => ((W v).w i).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)`. Use linear arithmetic over natural numbers and integers. Take `⟨S, Kw, Φ, κ, a1, a2, a3, a4, a5, a6, a7, a8⟩` from `h0 E n hn d x hd hx π W hW (∑ v, ((∑ i, (W v).w i) + n * m v)) Up hUp w₀ hw₀ hu J (χ.comp θ) hJo hJc hφ`. Conclude with `⟨⟨π, rfl, W, hW, m, hm, _, rfl, J, χ.comp θ, hcusp, htf, S, Kw, Φ, κ, hw₀, a1, a2, a3, a4, a5, a6, a7, a8⟩⟩`.
-/
theorem vecEx_of (h0 : SeedGU) (h1 : WtAt) : VecEx := by
  intro E _ _ _ n l d hn hd x hx U hU w₀ hw₀ hT Up hUp hu
  obtain ⟨e, J, θ, χ, hJo, hJc, htf, -, -, hcusp, hφ⟩ := hT
  let π : AutSub E n := ⟨U, hU⟩
  obtain ⟨W, hW⟩ := (h1 E n hn π).1
  let m : InfinitePlace E → ℕ := fun v => ∑ i, ((W v).w i).natAbs
  have hm : ∀ v i, 0 ≤ (W v).w i + m v := fun v i => by
    have : ((W v).w i).natAbs ≤ m v := Finset.single_le_sum (f := fun i => ((W v).w i).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  obtain ⟨S, Kw, Φ, κ, a1, a2, a3, a4, a5, a6, a7, a8⟩ := h0 E n hn d x hd hx π W hW (∑ v, ((∑ i, (W v).w i) + n * m v)) Up hUp w₀ hw₀ hu
    J (χ.comp θ) hJo hJc hφ
  exact ⟨⟨π, rfl, W, hW, m, hm, _, rfl, J, χ.comp θ, hcusp, htf, S, Kw, Φ, κ, hw₀, a1, a2, a3, a4, a5, a6, a7, a8⟩⟩

/- English proof (translation)
Introduce `E _ _ _ A n p _ S x U w₀ Up V thQ hth B y hdeg hsep`. Set `y₀ : GL (Fin n) E × ℚˣ` to `y.1`. Set `β : GL (Fin n) E` to `B.β`. Establish `hc : ∀ z : E, S.L.e.symm z = z` using `fun z => S.L.e.symm_apply_eq.2 (S.L_e z).symm`. Establish `hmin : minpoly E y₀.1.val = y₀.1.val.charpoly`.

Use `Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic (Matrix.isIntegral _)) (Matrix.charpoly_monic _) (Matrix.minpoly_dvd_charpoly _) ?_ |>.symm` and prove the remaining obligations. Rewrite using `[Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]`. Conclude with `hdeg.ge`. Set `Hc : Matrix (Fin n) (Fin n) E` to `(A.H n).map (IsCMField.complexConj E : E →+* E)`. Establish `hu : IsUnit Hc.det`.

Rewrite using `[show Hc.det = _ from ((IsCMField.complexConj E : E →+* E).map_det _).symm]`. Conclude with `((map_ne_zero _).2 (A.det_ne n)).isUnit`. Establish `hy : y₀.1.val * β.val * (Hc⁻¹ * (y₀.1.val.map (IsCMField.complexConj E : E →+* E))ᵀ * Hc) = algebraMap ℚ _ (y₀.2 : ℚ) * β.val` using `y.2.1`. Establish `hrel : (y₀.1.val.map (IsCMField.complexConj E))ᵀ * ((Matrix.isUnit_iff_isUnit_det _).2 hu).unit.val * β⁻¹.val * y₀.1.val = ((y₀.2 : ℚ) : E) • (((Matrix.isUnit_iff_isUnit_det _).2 hu).unit.val * β⁻¹.val)`. Rewrite using `[IsUnit.unit_spec]`.

Establish `e1 : (y₀.1.val.map (IsCMField.complexConj E))ᵀ * Hc = ((y₀.2 : ℚ) : E) • (Hc * β⁻¹.val * y₀.1⁻¹.val * β.val)`. Establish `h2` using `congrArg (fun M => Hc * β⁻¹.val * y₀.1⁻¹.val * M) hy`. Simplify using `only [Matrix.mul_assoc, Units.inv_mul_cancel_left, Matrix.mul_nonsing_inv_cancel_left _ _ hu] at h2`. Rewrite `h2` using `[← Algebra.smul_def, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul]`. Simplify using `only [Matrix.mul_assoc]`.

Rewrite using `[Rat.cast_smul_eq_qsmul]`. Conclude with `h2`. Rewrite using `[e1]`. Simplify using `only [smul_mul_assoc, Matrix.mul_assoc, Units.mul_inv_cancel_left, Units.inv_mul, Matrix.mul_one]`. Establish `hsep' : y₀.1.val.charpoly.Separable` using `hmin ▸ hsep`.

Establish `key` using `h0 E n V.W V.m V.pos y₀.1 (((Matrix.isUnit_iff_isUnit_det _).2 hu).unit * β⁻¹) (thQ y₀).1 y₀.2 (by rw [Units.val_mul, ← Matrix.mul_assoc]; exact hrel) hsep' (hth y₀).1`. Establish `e2 : thQ y₀ = ((thQ y₀).1, y₀.2⁻¹)` using `Prod.ext rfl (hth y₀).2`. Establish `e3 : LocalSmoothExtension.endPol S.L (minpoly E y₀.1.val) = LocalSmoothExtension.invPol y₀.1.val.charpoly`. Unfold `LocalSmoothExtension.endPol`. Rewrite using `[hmin]`.

Use `congrArg LocalSmoothExtension.invPol (Polynomial.ext fun i => ?_)` and prove the remaining obligations. Conclude with `(Polynomial.coeff_map _ _).trans (hc _)`. Rewrite `key` using `[← V.jz_eq, ← e2, ← e3]`. Conclude with `key`.
-/
theorem wtOf_of (h0 : WtCore) : WtOf := by
  intro E _ _ _ A n p _ S x U w₀ Up V thQ hth B y hdeg hsep
  let y₀ : GL (Fin n) E × ℚˣ := y.1
  let β : GL (Fin n) E := B.β
  have hc : ∀ z : E, S.L.e.symm z = z := fun z => S.L.e.symm_apply_eq.2 (S.L_e z).symm
  have hmin : minpoly E y₀.1.val = y₀.1.val.charpoly := by
    refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic (Matrix.isIntegral _)) (Matrix.charpoly_monic _)
      (Matrix.minpoly_dvd_charpoly _) ?_ |>.symm
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
    exact hdeg.ge
  let Hc : Matrix (Fin n) (Fin n) E := (A.H n).map (IsCMField.complexConj E : E →+* E)
  have hu : IsUnit Hc.det := by
    rw [show Hc.det = _ from ((IsCMField.complexConj E : E →+* E).map_det _).symm]
    exact ((map_ne_zero _).2 (A.det_ne n)).isUnit
  have hy : y₀.1.val * β.val * (Hc⁻¹ * (y₀.1.val.map (IsCMField.complexConj E : E →+* E))ᵀ * Hc) = algebraMap ℚ _ (y₀.2 : ℚ) * β.val := y.2.1
  have hrel : (y₀.1.val.map (IsCMField.complexConj E))ᵀ * ((Matrix.isUnit_iff_isUnit_det _).2 hu).unit.val * β⁻¹.val * y₀.1.val =
      ((y₀.2 : ℚ) : E) • (((Matrix.isUnit_iff_isUnit_det _).2 hu).unit.val * β⁻¹.val) := by
    rw [IsUnit.unit_spec]
    have e1 : (y₀.1.val.map (IsCMField.complexConj E))ᵀ * Hc = ((y₀.2 : ℚ) : E) • (Hc * β⁻¹.val * y₀.1⁻¹.val * β.val) := by
      have h2 := congrArg (fun M => Hc * β⁻¹.val * y₀.1⁻¹.val * M) hy
      simp only [Matrix.mul_assoc, Units.inv_mul_cancel_left, Matrix.mul_nonsing_inv_cancel_left _ _ hu] at h2
      rw [← Algebra.smul_def, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul] at h2
      simp only [Matrix.mul_assoc]
      rw [Rat.cast_smul_eq_qsmul]
      exact h2
    rw [e1]
    simp only [smul_mul_assoc, Matrix.mul_assoc, Units.mul_inv_cancel_left, Units.inv_mul, Matrix.mul_one]
  have hsep' : y₀.1.val.charpoly.Separable := hmin ▸ hsep
  have key := h0 E n V.W V.m V.pos y₀.1 (((Matrix.isUnit_iff_isUnit_det _).2 hu).unit * β⁻¹) (thQ y₀).1 y₀.2
    (by rw [Units.val_mul, ← Matrix.mul_assoc]; exact hrel) hsep' (hth y₀).1
  have e2 : thQ y₀ = ((thQ y₀).1, y₀.2⁻¹) := Prod.ext rfl (hth y₀).2
  have e3 : LocalSmoothExtension.endPol S.L (minpoly E y₀.1.val) = LocalSmoothExtension.invPol y₀.1.val.charpoly := by
    unfold LocalSmoothExtension.endPol
    rw [hmin]
    refine congrArg LocalSmoothExtension.invPol (Polynomial.ext fun i => ?_)
    exact (Polynomial.coeff_map _ _).trans (hc _)
  rw [← V.jz_eq, ← e2, ← e3] at key
  exact key

/- English proof (translation)
Introduce `E _ _ _ A n p _ S x U w₀ Up V d hd hx hG`. Take `⟨a1, a2⟩` from `h0 E n d x hd hx V.W V.m V.pos`. Use `⟨a1, fun τ => ?_⟩` and prove the remaining obligations. Take `⟨σ, hσ⟩` from `h1 E τ A.τ₀`. Use `⟨σ, hσ, fun lam hl j hj => ?_⟩` and prove the remaining obligations.

Take `⟨k, -, rfl⟩` from `Finset.mem_image.1 hj`. Establish `e : lam = V.W.at τ` using `(h2 E n S.facts.pos V.π).2 V.W V.hW τ lam (by rw [V.hV]; exact hl)`. Substitute `e` using the available equality. Rewrite using `[V.jz_eq]`. Use `a2 τ A.τ₀ σ hσ _ (fun φ => ?_) k` and prove the remaining obligations.

Establish `e1 : (starRingEnd ℂ) (A.τ₀ (A.ω : E)) = σ ((starRingEnd ℂ) (τ (A.ω : E)))`. Rewrite using `[← IsCMField.complexEmbedding_complexConj, ← IsCMField.complexEmbedding_complexConj, hσ]`. Establish `e2 : (σ (φ (A.ω : E)) = (starRingEnd ℂ) (A.τ₀ (A.ω : E))) ↔ φ x = -τ x`. Rewrite using `[e1, σ.injective.eq_iff]`. Conclude with `h3 E d x A.ω hd hx hG.1 hG.2 τ φ`.

Conclude with `if_congr e2 rfl rfl`.
-/
theorem expOf_of (h0 : ExpCore) (h1 : AutEx) (h2 : WtAt) (h3 : EpsIff) : ExpOf := by
  intro E _ _ _ A n p _ S x U w₀ Up V d hd hx hG
  obtain ⟨a1, a2⟩ := h0 E n d x hd hx V.W V.m V.pos
  refine ⟨a1, fun τ => ?_⟩
  obtain ⟨σ, hσ⟩ := h1 E τ A.τ₀
  refine ⟨σ, hσ, fun lam hl j hj => ?_⟩
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hj
  have e : lam = V.W.at τ := (h2 E n S.facts.pos V.π).2 V.W V.hW τ lam (by rw [V.hV]; exact hl)
  subst e
  rw [V.jz_eq]
  refine a2 τ A.τ₀ σ hσ _ (fun φ => ?_) k
  have e1 : (starRingEnd ℂ) (A.τ₀ (A.ω : E)) = σ ((starRingEnd ℂ) (τ (A.ω : E))) := by
    rw [← IsCMField.complexEmbedding_complexConj, ← IsCMField.complexEmbedding_complexConj, hσ]
  have e2 : (σ (φ (A.ω : E)) = (starRingEnd ℂ) (A.τ₀ (A.ω : E))) ↔ φ x = -τ x := by
    rw [e1, σ.injective.eq_iff]
    exact h3 E d x A.ω hd hx hG.1 hG.2 τ φ
  exact if_congr e2 rfl rfl

end UpperTheory.Gal.Int.Geo.Pl

end
