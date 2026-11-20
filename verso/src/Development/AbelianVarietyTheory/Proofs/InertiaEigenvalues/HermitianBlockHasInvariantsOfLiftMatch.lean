import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FullToGlIsSelfAdjoint
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisBorderedMatrixNormalFormInvariantsStatement

open GlobalTheory.JR Matrix

noncomputable section

namespace GlobalTheory.JR.Step

section MapLemmas
variable {r : ℕ} {k k' : Type} [CommRing k] [CommRing k'] (φ : k →+* k')

/- English proof (translation)
Simplify using `only [mom, glMap]`. Rewrite using `[RingHom.map_dotProduct, ← Matrix.map_pow]`. Use `congr 1`. Use extensionality with `j`. Simplify using `[RingHom.map_mulVec]`.

Both sides reduce to the same expression.
-/
theorem mom_glMap (Y : Gl r k) (i : ℕ) : mom (glMap φ Y) i = φ (mom Y i) := by
  simp only [mom, glMap]
  rw [RingHom.map_dotProduct, ← Matrix.map_pow]
  congr 1
  ext j
  simp [RingHom.map_mulVec]
  rfl

/- English proof (translation)
Use `Prod.ext ?_ (Prod.ext ?_ ?_)` and prove the remaining obligations. Use extensionality with `i`. Simplify using `[inv, Inv.map, glMap, Matrix.charpoly_map]`. Use extensionality with `i`. Simplify using `only [inv, Inv.map]`.

Conclude with `mom_glMap φ Y i`. Both sides reduce to the same expression.
-/
theorem inv_glMap (Y : Gl r k) : inv (glMap φ Y) = (inv Y).map φ := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · ext i
    simp [inv, Inv.map, glMap, Matrix.charpoly_map]
  · ext i
    simp only [inv, Inv.map]
    exact mom_glMap φ Y i
  · rfl

/- English proof (translation)
Use `Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))` and prove the remaining obligations. Use extensionality with `i j`. Simplify using `only [sec, glMap, companion, Inv.map, Matrix.map_apply, Matrix.of_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Use extensionality with `i`.

Simplify using `only [sec, glMap]`. Apply the tactic sequence `split_ifs <;> simp`. Both sides reduce to the same expression. Both sides reduce to the same expression.
-/
theorem sec_map (a : Inv r k) : sec (a.map φ) = glMap φ (sec a) := by
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · ext i j
    simp only [sec, glMap, companion, Inv.map, Matrix.map_apply, Matrix.of_apply]
    split_ifs <;> simp
  · ext i
    simp only [sec, glMap]
    split_ifs <;> simp
  · rfl
  · rfl

/- English proof (translation)
Establish `: hankel (a.map φ) = (hankel a).map φ`. Use extensionality with `i j`. Simplify using `only [hankel, Matrix.of_apply, Matrix.map_apply, sec_map, mom_glMap]`. Rewrite using `[Delta, Delta, this, RingHom.map_det]`. Both sides reduce to the same expression.
-/
theorem Delta_map (a : Inv r k) : Delta (a.map φ) = φ (Delta a) := by
  have : hankel (a.map φ) = (hankel a).map φ := by
    ext i j
    simp only [hankel, Matrix.of_apply, Matrix.map_apply, sec_map, mom_glMap]
  rw [Delta, Delta, this, RingHom.map_det]
  rfl

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [full, glMap, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.map_apply]`. Apply the tactic sequence `rcases (finSumFinEquiv.symm i) with a | a <;> rcases (finSumFinEquiv.symm j) with b | b <;> simp`.
-/
theorem full_glMap (Y : Gl r k) : full (glMap φ Y) = (full Y).map φ := by
  ext i j
  simp only [full, glMap, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.map_apply]
  rcases (finSumFinEquiv.symm i) with a | a <;> rcases (finSumFinEquiv.symm j) with b | b <;> simp

end MapLemmas

section Blocks
variable {r : ℕ} {k : Type} [CommRing k]

/- English proof (translation)
Use `Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))` and prove the remaining obligations. Use extensionality with `i j`. Simplify using `[blocks, full, finSumFinEquiv_symm_apply_castSucc]`. Use extensionality with `i`. Simplify using `[blocks, full, finSumFinEquiv_symm_apply_castSucc, finSumFinEquiv_symm_last]`.

Use extensionality with `i`. Simplify using `[blocks, full, finSumFinEquiv_symm_apply_castSucc, finSumFinEquiv_symm_last]`. Simplify using `[blocks, full, finSumFinEquiv_symm_last]`.
-/
theorem blocks_full (Y : Gl r k) : blocks (full Y) = Y := by
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · ext i j
    simp [blocks, full, finSumFinEquiv_symm_apply_castSucc]
  · ext i
    simp [blocks, full, finSumFinEquiv_symm_apply_castSucc, finSumFinEquiv_symm_last]
  · ext i
    simp [blocks, full, finSumFinEquiv_symm_apply_castSucc, finSumFinEquiv_symm_last]
  · simp [blocks, full, finSumFinEquiv_symm_last]

/- English proof (translation)
The claim follows from `Function.LeftInverse.injective blocks_full`.
-/
theorem full_injective : Function.Injective (full : Gl r k → _) :=
  Function.LeftInverse.injective blocks_full

/- English proof (translation)
Simplify using `only [full, embHom, act, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]`. Use `congr 1`. Use `congr 1`. Simplify using the standard rewrite rules. Use extensionality with `i j`.

Simplify using `[Matrix.mul_apply, Matrix.mulVec, dotProduct]`. Use extensionality with `i j`. Simplify using `[Matrix.mul_apply, Matrix.vecMul, dotProduct]`. Use extensionality with `i j`. Simplify using `[Matrix.mul_apply]`.
-/
theorem full_act (g : GL (Fin r) k) (Y : Gl r k) :
    full (act g Y) = embHom r k g * full Y * embHom r k ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) := by
  simp only [full, embHom, act, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.reindex_apply,
    Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  congr 1
  congr 1
  · simp
  · ext i j; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  · ext i j; simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]
  · ext i j; simp [Matrix.mul_apply]

/- English proof (translation)
Simplify using `[embHom, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]`.
-/
theorem det_embHom (h : Matrix (Fin r) (Fin r) k) : (embHom r k h).det = h.det := by
  simp [embHom, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

end Blocks

/- English proof (translation)
Introduce `F E _ _ _ _ _ r Z X μ l ν hν hμ hΔ hX`. Establish `hφ : Function.Injective (algebraMap F E)` using `(algebraMap F E).injective`. Establish `hμ' : algebraMap F E μ ≠ 0` using `fun h => hμ (hφ (h.trans (map_zero _).symm))`. Establish `hsν : star ν ≠ 0`. Introduce `h`.

Apply `hμ'` to reduce the goal to its premises. Rewrite using `[← hν, h, mul_zero]`. Establish `hinv : inv (liftH X ν l).toGl = inv (glMap (algebraMap F E) (lift Z μ l))`. Rewrite using `[inv_glMap]`. Conclude with `hX`.

Establish `hD : Delta (inv (glMap (algebraMap F E) (lift Z μ l))) ≠ 0`. Rewrite using `[inv_glMap, Delta_map]`. Conclude with `fun h => hΔ (hφ (h.trans (map_zero _).symm))`. Take `⟨g, ⟨hg, -⟩, -⟩` from `(GlobalTheory.T.jacquetRallis_borderedMatrix_normalForm_invariants E (r + 1)).2.2.2.2 _ _ hD hinv`. Use `set G : Matrix (Fin (r + 1)) (Fin (r + 1)) E := (g : Matrix (Fin (r + 1)) (Fin (r + 1)) E) with hG`.

Use `set Gi : Matrix (Fin (r + 1)) (Fin (r + 1)) E := ((g⁻¹ : GL (Fin (r + 1)) E) : Matrix (Fin (r + 1)) (Fin (r + 1)) E) with hGi`. Establish `hGiG : Gi * G = 1` using `by rw [hG, hGi, Units.inv_mul]`. Establish `h1 : G * full (glMap (algebraMap F E) Z) * Gi = full X.toGl`. Rewrite using `[full_glMap]`. Conclude with `congrArg Prod.fst hg`.

Establish `h2 : G *ᵥ (fun i => algebraMap F E ((μ • eL r F) i)) = ν • eL r E` using `congrArg (fun Y => Y.2.1) hg`. Establish `h3 : (fun i => algebraMap F E (eL r F i)) ᵥ* Gi = star (ν • eL r E)` using `congrArg (fun Y => Y.2.2.1) hg`. Establish `hv1 : (fun i => algebraMap F E ((μ • eL r F) i)) = algebraMap F E μ • eL r E`. Apply the tactic sequence `ext i; simp only [eL, Pi.smul_apply, Pi.single_apply, smul_eq_mul]; split_ifs <;> simp`. Establish `hv2 : (fun i => algebraMap F E (eL r F i)) = eL r E`.

Apply the tactic sequence `ext i; simp only [eL, Pi.single_apply]; split_ifs <;> simp`. Establish `hv3 : star (ν • eL r E) = star ν • eL r E`. Apply the tactic sequence `ext i; simp only [eL, Pi.star_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]; split_ifs <;> simp`. Rewrite `h2` using `[hv1]`. Rewrite `h3` using `[hv2, hv3]`.

Establish `hcol : ∀ i, G i (Fin.last r) * algebraMap F E μ = ν * eL r E i`. Introduce `i`. Use `congrFun h2 i` as an intermediate fact. Rewrite `this` using `[Matrix.mulVec_smul, eL, Matrix.mulVec_single_one]`. Simplify using `only [Pi.smul_apply, smul_eq_mul, Matrix.transpose_apply] at this`.

Rewrite using `[mul_comm]`. Conclude with `this`. Establish `hrow : eL r E ᵥ* G = (star ν)⁻¹ • eL r E`. Establish `hs : star ν • (eL r E ᵥ* G) = eL r E`. Rewrite using `[← Matrix.smul_vecMul, ← h3, Matrix.vecMul_vecMul, hGiG, Matrix.vecMul_one]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[smul_smul, inv_mul_cancel₀ hsν, one_smul]`. Use `_ = (star ν)⁻¹ • eL r E := by rw [hs]`. Establish `eLL : G (Fin.last r) (Fin.last r) = (star ν)⁻¹`. Use `congrFun hrow (Fin.last r)` as an intermediate fact.

Simplify `this` using `[eL, Matrix.single_one_vecMul]`. Establish `eLc : ∀ b : Fin r, G (Fin.last r) (Fin.castSucc b) = 0`. Introduce `b`. Use `congrFun hrow (Fin.castSucc b)` as an intermediate fact. Simplify `this` using `[eL, Matrix.single_one_vecMul, Fin.castSucc_ne_last]`.

Establish `ecL : ∀ a : Fin r, G (Fin.castSucc a) (Fin.last r) = 0`. Introduce `a`. Use `hcol (Fin.castSucc a)` as an intermediate fact. Simplify using `only [eL, Pi.single_apply, Fin.castSucc_ne_last, if_false, mul_zero] at this`. Conclude with `(mul_eq_zero.mp this).resolve_right hμ'`.

Use `set H : Matrix (Fin (r + 1)) (Fin (r + 1)) E := star ν • G with hH`. Use `set h' : Matrix (Fin r) (Fin r) E := H.submatrix Fin.castSucc Fin.castSucc with hh'`. Establish `hHemb : H = embHom r E h'`. Use extensionality with `i j`. Apply the tactic sequence `refine Fin.lastCases ?_ (fun a => ?_) i <;> refine Fin.lastCases ?_ (fun b => ?_) j`.

Apply the tactic sequence `all_goals simp [embHom, H, h', finSumFinEquiv_symm_apply_castSucc, finSumFinEquiv_symm_last, eLL, eLc, ecL, hsν]`. Establish `hdetG : G.det ≠ 0` using `((Matrix.isUnit_iff_isUnit_det G).mp g.isUnit).ne_zero`. Establish `hdet : h'.det ≠ 0`. Rewrite using `[← det_embHom, ← hHemb, hH, Matrix.det_smul]`. Conclude with `mul_ne_zero (pow_ne_zero _ hsν) hdetG`.

Use `set u : GL (Fin r) E := Matrix.GeneralLinearGroup.mkOfDetNeZero h' hdet with hu_def`. Establish `hu : (u : Matrix (Fin r) (Fin r) E) = h'` using `rfl`. Establish `hGM : G * full (glMap (algebraMap F E) Z) = full X.toGl * G`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hGiG, Matrix.mul_one]`.

Use `_ = (G * full (glMap (algebraMap F E) Z) * Gi) * G := by`. Rewrite using `[Matrix.mul_assoc (G * full (glMap (algebraMap F E) Z))]`. Use `_ = full X.toGl * G := by rw [h1]`. Establish `hHM : H * full (glMap (algebraMap F E) Z) = full X.toGl * H`. Rewrite using `[hH, Matrix.smul_mul, Matrix.mul_smul, hGM]`.

Establish `key : full (act u (glMap (algebraMap F E) Z)) = full X.toGl`. Rewrite using `[full_act, hu, ← hHemb, hHM, hHemb, Matrix.mul_assoc, ← map_mul (embHom r E), ← hu, Units.mul_inv, map_one, Matrix.mul_one]`. Establish `hXeq : X.toGl = act u (glMap (algebraMap F E) Z)` using `(full_injective key).symm`. Unfold `HasInv`. Rewrite using `[hXeq, (GlobalTheory.T.jacquetRallis_borderedMatrix_normalForm_invariants E r).1, inv_glMap]`.
-/
theorem hasInv_of_lift : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (Z : Gl r F) (X : Hn r F E) (μ l : F) (ν : E),
    ν * star ν = algebraMap F E μ → μ ≠ 0 → Delta (inv (GlobalTheory.JR.Step.lift Z μ l)) ≠ 0 →
    HasInv (GlobalTheory.JR.Step.liftH X ν l) (inv (GlobalTheory.JR.Step.lift Z μ l)) → HasInv X (inv Z) := by
  intro F E _ _ _ _ _ r Z X μ l ν hν hμ hΔ hX
  have hφ : Function.Injective (algebraMap F E) := (algebraMap F E).injective
  have hμ' : algebraMap F E μ ≠ 0 := fun h => hμ (hφ (h.trans (map_zero _).symm))
  have hsν : star ν ≠ 0 := by
    intro h; apply hμ'; rw [← hν, h, mul_zero]
  have hinv : inv (liftH X ν l).toGl = inv (glMap (algebraMap F E) (lift Z μ l)) := by
    rw [inv_glMap]; exact hX
  have hD : Delta (inv (glMap (algebraMap F E) (lift Z μ l))) ≠ 0 := by
    rw [inv_glMap, Delta_map]
    exact fun h => hΔ (hφ (h.trans (map_zero _).symm))
  obtain ⟨g, ⟨hg, -⟩, -⟩ := (GlobalTheory.T.jacquetRallis_borderedMatrix_normalForm_invariants E (r + 1)).2.2.2.2 _ _ hD hinv
  set G : Matrix (Fin (r + 1)) (Fin (r + 1)) E := (g : Matrix (Fin (r + 1)) (Fin (r + 1)) E) with hG
  set Gi : Matrix (Fin (r + 1)) (Fin (r + 1)) E := ((g⁻¹ : GL (Fin (r + 1)) E) : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    with hGi
  have hGiG : Gi * G = 1 := by rw [hG, hGi, Units.inv_mul]
  have h1 : G * full (glMap (algebraMap F E) Z) * Gi = full X.toGl := by
    rw [full_glMap]; exact congrArg Prod.fst hg
  have h2 : G *ᵥ (fun i => algebraMap F E ((μ • eL r F) i)) = ν • eL r E := congrArg (fun Y => Y.2.1) hg
  have h3 : (fun i => algebraMap F E (eL r F i)) ᵥ* Gi = star (ν • eL r E) := congrArg (fun Y => Y.2.2.1) hg
  have hv1 : (fun i => algebraMap F E ((μ • eL r F) i)) = algebraMap F E μ • eL r E := by
    ext i; simp only [eL, Pi.smul_apply, Pi.single_apply, smul_eq_mul]; split_ifs <;> simp
  have hv2 : (fun i => algebraMap F E (eL r F i)) = eL r E := by
    ext i; simp only [eL, Pi.single_apply]; split_ifs <;> simp
  have hv3 : star (ν • eL r E) = star ν • eL r E := by
    ext i; simp only [eL, Pi.star_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]; split_ifs <;> simp
  rw [hv1] at h2
  rw [hv2, hv3] at h3
  have hcol : ∀ i, G i (Fin.last r) * algebraMap F E μ = ν * eL r E i := by
    intro i
    have := congrFun h2 i
    rw [Matrix.mulVec_smul, eL, Matrix.mulVec_single_one] at this
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.transpose_apply] at this
    rw [mul_comm]
    exact this
  have hrow : eL r E ᵥ* G = (star ν)⁻¹ • eL r E := by
    have hs : star ν • (eL r E ᵥ* G) = eL r E := by
      rw [← Matrix.smul_vecMul, ← h3, Matrix.vecMul_vecMul, hGiG, Matrix.vecMul_one]
    calc eL r E ᵥ* G = (star ν)⁻¹ • (star ν • (eL r E ᵥ* G)) := by
          rw [smul_smul, inv_mul_cancel₀ hsν, one_smul]
      _ = (star ν)⁻¹ • eL r E := by rw [hs]
  have eLL : G (Fin.last r) (Fin.last r) = (star ν)⁻¹ := by
    have := congrFun hrow (Fin.last r)
    simpa [eL, Matrix.single_one_vecMul] using this
  have eLc : ∀ b : Fin r, G (Fin.last r) (Fin.castSucc b) = 0 := by
    intro b
    have := congrFun hrow (Fin.castSucc b)
    simpa [eL, Matrix.single_one_vecMul, Fin.castSucc_ne_last] using this
  have ecL : ∀ a : Fin r, G (Fin.castSucc a) (Fin.last r) = 0 := by
    intro a
    have := hcol (Fin.castSucc a)
    simp only [eL, Pi.single_apply, Fin.castSucc_ne_last, if_false, mul_zero] at this
    exact (mul_eq_zero.mp this).resolve_right hμ'
  set H : Matrix (Fin (r + 1)) (Fin (r + 1)) E := star ν • G with hH
  set h' : Matrix (Fin r) (Fin r) E := H.submatrix Fin.castSucc Fin.castSucc with hh'
  have hHemb : H = embHom r E h' := by
    ext i j
    refine Fin.lastCases ?_ (fun a => ?_) i <;> refine Fin.lastCases ?_ (fun b => ?_) j
    all_goals simp [embHom, H, h', finSumFinEquiv_symm_apply_castSucc, finSumFinEquiv_symm_last, eLL, eLc, ecL, hsν]
  have hdetG : G.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det G).mp g.isUnit).ne_zero
  have hdet : h'.det ≠ 0 := by
    rw [← det_embHom, ← hHemb, hH, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hsν) hdetG
  set u : GL (Fin r) E := Matrix.GeneralLinearGroup.mkOfDetNeZero h' hdet with hu_def
  have hu : (u : Matrix (Fin r) (Fin r) E) = h' := rfl
  have hGM : G * full (glMap (algebraMap F E) Z) = full X.toGl * G := by
    calc G * full (glMap (algebraMap F E) Z) = G * full (glMap (algebraMap F E) Z) * (Gi * G) := by
          rw [hGiG, Matrix.mul_one]
      _ = (G * full (glMap (algebraMap F E) Z) * Gi) * G := by
          rw [Matrix.mul_assoc (G * full (glMap (algebraMap F E) Z))]
      _ = full X.toGl * G := by rw [h1]
  have hHM : H * full (glMap (algebraMap F E) Z) = full X.toGl * H := by
    rw [hH, Matrix.smul_mul, Matrix.mul_smul, hGM]
  have key : full (act u (glMap (algebraMap F E) Z)) = full X.toGl := by
    rw [full_act, hu, ← hHemb, hHM, hHemb, Matrix.mul_assoc, ← map_mul (embHom r E), ← hu, Units.mul_inv,
      map_one, Matrix.mul_one]
  have hXeq : X.toGl = act u (glMap (algebraMap F E) Z) := (full_injective key).symm
  unfold HasInv
  rw [hXeq, (GlobalTheory.T.jacquetRallis_borderedMatrix_normalForm_invariants E r).1, inv_glMap]

end GlobalTheory.JR.Step
