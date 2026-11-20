import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WHyp
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open scoped NNReal ENNReal Pointwise

noncomputable section

namespace GlobalTheory.JR.Hyp

/- English proof (translation)
Use `haveI : LocallyCompactSpace F := Unram.lcF (E := E)`. Use `haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F`. Use `haveI : SecondCountableTopology A.K := by`. Set `e : A.K ≃ₗ[F] (Fin (Module.finrank F A.K) → F)` to `(Module.finBasis F A.K).equivFun`. Establish `h1 : Continuous e` using `IsModuleTopology.continuous_of_linearMap e.toLinearMap`.

Establish `h2 : Continuous e.symm` using `IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap`. Set `h : A.K ≃ₜ (Fin (Module.finrank F A.K) → F)` to `⟨e.toEquiv, h1, h2⟩`. Conclude with `h.isEmbedding.secondCountableTopology`. Establish `hme : MeasurableEmbedding (fun b : A.K => s • b)` using `(Homeomorph.smul s).measurableEmbedding`. Establish `hmap : Measure.map (fun b : A.K => s • b) ν = ((distribHaarChar A.K s : ℝ≥0∞))⁻¹ • ν`.

Use extensionality with `S hS`. Rewrite using `[hme.map_apply, Measure.smul_apply, smul_eq_mul]`. Establish `h1` using `distribHaarChar_mul ν s⁻¹ S`. Rewrite using `[Set.preimage_smul, ← h1, map_inv, ENNReal.coe_inv (distribHaarChar_pos).ne']`. Establish `hint : ∫ b, g ((s : A.K) * b) ∂ν = ∫ b, g b ∂(Measure.map (fun b : A.K => s • b) ν)`.

Rewrite using `[hme.integral_map]`. Both sides reduce to the same expression. Establish `habs : A.absK (s : A.K) = (distribHaarChar A.K s : ℝ)`. Unfold `Et.absK`. Rewrite using `[dif_pos s.isUnit]`.

Use `congr 2`. Use `ext`. Both sides reduce to the same expression. Rewrite using `[hint, hmap, integral_smul_measure, habs]`. Simplify using `[Complex.real_smul]`.
-/
theorem integral_comp_unit_mul {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ν : Measure A.K) [ν.IsAddHaarMeasure]
    (s : A.Kˣ) (g : A.K → ℂ) :
    ∫ b, g ((s : A.K) * b) ∂ν = ((A.absK (s : A.K) : ℂ))⁻¹ * ∫ b, g b ∂ν := by
  haveI : LocallyCompactSpace F := Unram.lcF (E := E)
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : SecondCountableTopology A.K := by
    let e : A.K ≃ₗ[F] (Fin (Module.finrank F A.K) → F) := (Module.finBasis F A.K).equivFun
    have h1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
    have h2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
    let h : A.K ≃ₜ (Fin (Module.finrank F A.K) → F) := ⟨e.toEquiv, h1, h2⟩
    exact h.isEmbedding.secondCountableTopology
  have hme : MeasurableEmbedding (fun b : A.K => s • b) := (Homeomorph.smul s).measurableEmbedding
  have hmap : Measure.map (fun b : A.K => s • b) ν = ((distribHaarChar A.K s : ℝ≥0∞))⁻¹ • ν := by
    ext S hS
    rw [hme.map_apply, Measure.smul_apply, smul_eq_mul]
    have h1 := distribHaarChar_mul ν s⁻¹ S
    rw [Set.preimage_smul, ← h1, map_inv, ENNReal.coe_inv (distribHaarChar_pos).ne']
  have hint : ∫ b, g ((s : A.K) * b) ∂ν = ∫ b, g b ∂(Measure.map (fun b : A.K => s • b) ν) := by
    rw [hme.integral_map]; rfl
  have habs : A.absK (s : A.K) = (distribHaarChar A.K s : ℝ) := by
    unfold Et.absK
    rw [dif_pos s.isUnit]
    congr 2
    ext; rfl
  rw [hint, hmap, integral_smul_measure, habs]
  simp [Complex.real_smul]

/- English proof (translation)
Introduce `F E _ _ _ _ _ A ν hν ψ x s Φ`. Use function extensionality and compare the values at `p`. Take `⟨a, u⟩` from `p`. Establish `hs0 : A.absK (s : A.K) ≠ 0`. Unfold `Et.absK`.

Rewrite using `[dif_pos s.isUnit]`. Conclude with `(distribHaarChar_pos).ne'` after adjusting the coercions. Establish `key` using `integral_comp_unit_mul A ν s (fun b' => Φ (a * (s : A.K), b') * A.psiK ψ (x * b' * (u * ((s⁻¹ : A.Kˣ) : A.K))))`. Simplify using `only [pt, rg, mS, fourB, kx]`. Simplify using `only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const, mul_zero, add_zero, zero_add]`.

Rewrite `key` using `[eq_inv_mul_iff_mul_eq₀ (by exact_mod_cast hs0)]`. Rewrite using `[← key, ← integral_const_mul]`. Use `integral_congr_ae (Eventually.of_forall fun b => ?_)` and prove the remaining obligations. Establish `e1 : x * ((s : A.K) * b) * (u * ((s⁻¹ : A.Kˣ) : A.K)) = x * b * u`. Rewrite using `[show x * ((s : A.K) * b) * (u * ((s⁻¹ : A.Kˣ) : A.K)) = x * b * u * ((s : A.K) * ((s⁻¹ : A.Kˣ) : A.K)) by ring, Units.mul_inv, mul_one]`.

Simplify using `only [e1, mul_comm a (s : A.K)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pt_scale_eq_rg_mS : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ν : Measure A.K), ν.IsAddHaarMeasure → ∀ (ψ : AddChar F ℂ) (x : A.K) (s : A.Kˣ) (Φ : A.K × A.K → ℂ), Hyp.pt A ν ψ x (fun p => (A.absK (s : A.K) : ℂ) * Φ ((s : A.K) * p.1, (s : A.K) * p.2)) = Hyp.rg A (mS s) (Hyp.pt A ν ψ x Φ) := by
  intro F E _ _ _ _ _ A ν hν ψ x s Φ
  funext p
  obtain ⟨a, u⟩ := p
  have hs0 : A.absK (s : A.K) ≠ 0 := by
    unfold Et.absK
    rw [dif_pos s.isUnit]
    exact_mod_cast (distribHaarChar_pos).ne'
  have key := integral_comp_unit_mul A ν s
    (fun b' => Φ (a * (s : A.K), b') * A.psiK ψ (x * b' * (u * ((s⁻¹ : A.Kˣ) : A.K))))
  simp only [pt, rg, mS, fourB, kx]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const, mul_zero, add_zero, zero_add]
  rw [eq_inv_mul_iff_mul_eq₀ (by exact_mod_cast hs0)] at key
  rw [← key, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun b => ?_)
  have e1 : x * ((s : A.K) * b) * (u * ((s⁻¹ : A.Kˣ) : A.K)) = x * b * u := by
    rw [show x * ((s : A.K) * b) * (u * ((s⁻¹ : A.Kˣ) : A.K)) = x * b * u * ((s : A.K) * ((s⁻¹ : A.Kˣ) : A.K)) by ring,
      Units.mul_inv, mul_one]
  simp only [e1, mul_comm a (s : A.K)]
  ring

end GlobalTheory.JR.Hyp
