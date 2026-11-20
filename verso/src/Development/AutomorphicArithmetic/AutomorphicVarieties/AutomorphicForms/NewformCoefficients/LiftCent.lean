import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CuspCritAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Decomp
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.IntOfIntegers
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.DvdOfOhat
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.NslMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.NslInv

open NumberField Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af.Nf Matrix
open scoped MatrixGroups

/- English proof (translation)
Establish `h : ∀ x, TR.pInf ℚ (TR.sInf ℚ x) = x` using `fun x => (TR.infEq ℚ).symm_apply_apply x`. Establish `h2 : ∀ x, TR.pInf ℚ (sFin ℚ x) = 0` using `fun x => map_zero (TR.infEq ℚ).symm`. Establish `h3 : ∀ x, pFin ℚ (TR.sInf ℚ x) = 0` using `fun x => rfl`. Establish `h4 : ∀ x, pFin ℚ (sFin ℚ x) = x` using `fun x => rfl`. Use `Units.ext (TR.ad_ext ?_ ?_)` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `TR.pInf ℚ ((1 - TR.sInf ℚ 1 + TR.sInf ℚ (TR.pInf ℚ x.val)) * (1 - sFin ℚ 1 + sFin ℚ (pFin ℚ x.val))) = _`. Simplify using `[h, h2]`. Express the relevant statement in the definitionally equal form `pFin ℚ ((1 - TR.sInf ℚ 1 + TR.sInf ℚ (TR.pInf ℚ x.val)) * (1 - sFin ℚ 1 + sFin ℚ (pFin ℚ x.val))) = _`. Simplify using `[h3, h4]`.
-/
private theorem idele_split (x : Ideles ℚ) :
    TR.infId ℚ (Units.map (TR.pInf ℚ).toMonoidHom x) * finId ℚ (Units.map (pFin ℚ).toMonoidHom x) = x := by
  have h : ∀ x, TR.pInf ℚ (TR.sInf ℚ x) = x := fun x => (TR.infEq ℚ).symm_apply_apply x
  have h2 : ∀ x, TR.pInf ℚ (sFin ℚ x) = 0 := fun x => map_zero (TR.infEq ℚ).symm
  have h3 : ∀ x, pFin ℚ (TR.sInf ℚ x) = 0 := fun x => rfl
  have h4 : ∀ x, pFin ℚ (sFin ℚ x) = x := fun x => rfl
  refine Units.ext (TR.ad_ext ?_ ?_)
  · change TR.pInf ℚ ((1 - TR.sInf ℚ 1 + TR.sInf ℚ (TR.pInf ℚ x.val)) * (1 - sFin ℚ 1 + sFin ℚ (pFin ℚ x.val))) = _
    simp [h, h2]
  · change pFin ℚ ((1 - TR.sInf ℚ 1 + TR.sInf ℚ (TR.pInf ℚ x.val)) * (1 - sFin ℚ 1 + sFin ℚ (pFin ℚ x.val))) = _
    simp [h3, h4]

/- English proof (translation)
Use extensionality with `i j`. Express the relevant statement in the definitionally equal form `(1 : Matrix (Fin 2) (Fin 2) S) i j - s ((1 : Matrix (Fin 2) (Fin 2) R) i j) + s (Matrix.scalar (Fin 2) u.val i j) = Matrix.scalar (Fin 2) (1 - s 1 + s u.val) i j`. Apply the tactic sequence `by_cases e : i = j <;> simp [Matrix.one_apply, e]`.
-/
private theorem corner_sc {R S : Type} [CommRing R] [CommRing S] (s : R →ₙ+* S) (u : Rˣ) :
    cornerGL 2 s (GeneralLinearGroup.scalar (Fin 2) u) = GeneralLinearGroup.scalar (Fin 2) (Units.map (corner s) u) := by
  ext i j
  change (1 : Matrix (Fin 2) (Fin 2) S) i j - s ((1 : Matrix (Fin 2) (Fin 2) R) i j) + s (Matrix.scalar (Fin 2) u.val i j) =
    Matrix.scalar (Fin 2) (1 - s 1 + s u.val) i j
  by_cases e : i = j <;> simp [Matrix.one_apply, e]

/- English proof (translation)
Take `⟨r, u, -, hu, e⟩` from `ratAd.1 (Units.map (pFin ℚ).toMonoidHom z)`. Use `set w : Ideles ℚ := (Units.map (algebraMap ℚ (Ad ℚ)).toMonoidHom r)⁻¹ * z with hw`. Establish `hz : z = Units.map (algebraMap ℚ (Ad ℚ)).toMonoidHom r * w` using `by rw [hw, mul_inv_cancel_left]`. Establish `e1 : Units.map (pFin ℚ).toMonoidHom w = u`. Rewrite using `[hw, map_mul, map_inv, e]`.

Conclude with `inv_mul_cancel_left _ _`. Establish `h0` using `TR.unit_ne_zero (Units.map (TR.pInf ℚ).toMonoidHom w) Rat.infinitePlace`. Break down `lt_or_gt_of_ne h0 with h | h` into its components or cases. Use `⟨-r, Units.map (TR.pInf ℚ).toMonoidHom (-w), Units.map (pFin ℚ).toMonoidHom (-w), fun v => ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Subsingleton.elim v Rat.infinitePlace]`.

Express the relevant statement in the definitionally equal form `0 < TR.pInf ℚ (-w.val) Rat.infinitePlace`. Rewrite using `[map_neg]`. Conclude with `neg_pos.2 h`. Establish `: Units.map (pFin ℚ).toMonoidHom (-w) = -u`. Rewrite using `[← e1]`.

Conclude with `Units.ext (map_neg (pFin ℚ) w.val)`. Rewrite using `[this]`. Conclude with `⟨neg_mem hu.1, neg_mem hu.2⟩`. Rewrite using `[idele_split]`. Use `hz.trans (Units.ext ?_)` and prove the remaining obligations.

Simplify using the standard rewrite rules. Use `⟨r, Units.map (TR.pInf ℚ).toMonoidHom w, Units.map (pFin ℚ).toMonoidHom w, fun v => ?_, e1 ▸ hu, ?_⟩` and prove the remaining obligations. Rewrite using `[Subsingleton.elim v Rat.infinitePlace]`. Conclude with `h`. Rewrite using `[idele_split]`.

Conclude with `hz`.
-/
private theorem idele_dec (z : Ideles ℚ) : ∃ (r : ℚˣ) (t : (TR.Rinf ℚ)ˣ) (u : (Af ℚ)ˣ), (∀ v, 0 < t.val v) ∧ IsZU u ∧
    z = Units.map (algebraMap ℚ (Ad ℚ)).toMonoidHom r * (TR.infId ℚ t * finId ℚ u) := by
  obtain ⟨r, u, -, hu, e⟩ := ratAd.1 (Units.map (pFin ℚ).toMonoidHom z)
  set w : Ideles ℚ := (Units.map (algebraMap ℚ (Ad ℚ)).toMonoidHom r)⁻¹ * z with hw
  have hz : z = Units.map (algebraMap ℚ (Ad ℚ)).toMonoidHom r * w := by rw [hw, mul_inv_cancel_left]
  have e1 : Units.map (pFin ℚ).toMonoidHom w = u := by
    rw [hw, map_mul, map_inv, e]
    exact inv_mul_cancel_left _ _
  have h0 := TR.unit_ne_zero (Units.map (TR.pInf ℚ).toMonoidHom w) Rat.infinitePlace
  rcases lt_or_gt_of_ne h0 with h | h
  · refine ⟨-r, Units.map (TR.pInf ℚ).toMonoidHom (-w), Units.map (pFin ℚ).toMonoidHom (-w), fun v => ?_, ?_, ?_⟩
    · rw [Subsingleton.elim v Rat.infinitePlace]
      change 0 < TR.pInf ℚ (-w.val) Rat.infinitePlace
      rw [map_neg]
      exact neg_pos.2 h
    · have : Units.map (pFin ℚ).toMonoidHom (-w) = -u := by
        rw [← e1]
        exact Units.ext (map_neg (pFin ℚ) w.val)
      rw [this]
      exact ⟨neg_mem hu.1, neg_mem hu.2⟩
    · rw [idele_split]
      refine hz.trans (Units.ext ?_)
      simp
  · refine ⟨r, Units.map (TR.pInf ℚ).toMonoidHom w, Units.map (pFin ℚ).toMonoidHom w, fun v => ?_, e1 ▸ hu, ?_⟩
    · rw [Subsingleton.elim v Rat.infinitePlace]
      exact h
    · rw [idele_split]
      exact hz

/- English proof (translation)
Introduce `k M hM χ ω hω f hf φ hφ z g`. Take `⟨r, t, u, ht, hu, rfl⟩` from `idele_dec z`. Take `⟨γ, h, κ, hκ, rfl⟩` from `decomp M hM g`. Take `⟨δ, β, hδ, hβ, hK, hd⟩` from `(ratK M hM).2 u hu`. Establish `h1 : ω.1 (Units.map (algebraMap ℚ (Ad ℚ)).toMonoidHom r) = 1` using `ω.2.2 r`.

Establish `h2` using `hω.unit u hu _ hd`. Establish `s1 : GeneralLinearGroup.scalar (Fin 2) (Units.map (algebraMap ℚ (Ad ℚ)).toMonoidHom r) = ratGL ℚ 2 (GeneralLinearGroup.scalar (Fin 2) r)`. Use extensionality with `i j`. Apply the tactic sequence `by_cases e : i = j <;> simp [ratGL, Matrix.diagonal_apply, e, Matrix.algebraMap_matrix_apply]`. Use `set T : GL (Fin 2) ℝ := GeneralLinearGroup.map ev (GeneralLinearGroup.scalar (Fin 2) t) with hT`.

Establish `s2 : GeneralLinearGroup.scalar (Fin 2) (TR.infId ℚ t) = upR T`. Rewrite using `[hT, upR_ev]`. Conclude with `(corner_sc _ t).symm`. Establish `s3 : GeneralLinearGroup.scalar (Fin 2) (finId ℚ u) = finGL ℚ 2 (GeneralLinearGroup.scalar (Fin 2) u)` using `(corner_sc _ u).symm`. Establish `e : GeneralLinearGroup.scalar (Fin 2) (Units.map (algebraMap ℚ (Ad ℚ)).toMonoidHom r * (TR.infId ℚ t * finId ℚ u)) * (ratGL ℚ 2 γ * (upR h * finGL ℚ 2 κ)) = ratGL ℚ 2 (GeneralLinearGroup.scalar (Fin 2) r * γ * β) * (upR ((toR β)⁻¹ * (T * h)) * finGL ℚ 2 ((toF β)⁻¹ * GeneralLinear …`.

Establish `c : ∀ (x : GL (Fin 2) ℝ) (y : GL (Fin 2) (Af ℚ)) (w : GA ℚ 2), finGL ℚ 2 y * (upR x * w) = upR x * (finGL ℚ 2 y * w)` using `fun x y w => by rw [← mul_assoc, ← upR_comm, mul_assoc]`. Rewrite using `[map_mul, mul_assoc, ← mul_assoc _ (ratGL ℚ 2 γ), GeneralLinearGroup.scalar_commute (TR.infId ℚ t * finId ℚ u) (ratGL ℚ 2 γ), map_mul, s1, s2, s3, map_mul (ratGL ℚ 2), map_mul (ratGL ℚ 2), ratGL_eq β]`. Simplify using `only [mul_assoc, c]`. Simplify using `only [mul_assoc, map_mul, map_inv, mul_inv_cancel_left]`. Establish `hβ' : (toR β).val = δ.1.map (Int.cast : ℤ → ℝ)`.

Use extensionality with `i j`. Use `congrFun (congrFun hβ i) j` as an intermediate fact. Express the relevant statement in the definitionally equal form `(Rat.castHom ℝ) (β.val i j) = _`. Rewrite using `[this]`. Simplify using the standard rewrite rules.

Establish `e2 : ((toR β)⁻¹ * (T * h)).val = t.val Rat.infinitePlace • ((toR β)⁻¹ * h).val`. Establish `: T.val = t.val Rat.infinitePlace • (1 : Matrix (Fin 2) (Fin 2) ℝ)`. Use extensionality with `i j`. Apply the tactic sequence `by_cases e : i = j <;> simp [hT, ev, Matrix.diagonal_apply, e]`. Simplify using `only [Units.val_mul, this, Matrix.smul_mul, Matrix.mul_smul, one_mul]`.

Establish `e3` using `((nslInv k M f ((toR β)⁻¹ * h).val ((toR β)⁻¹ * h).det_ne_zero).2 χ hf δ hδ)`. Rewrite `e3` using `[← hβ', ← Units.val_mul, mul_inv_cancel_left]`. Rewrite using `[e, hφ _ _ _ (mul_mem hK hκ), hφ _ _ _ hκ, e2, (nslMul k f).2.2.1 _ _ (ht _), e3, map_mul, map_mul, h1, hω.pos t ht, one_mul, one_mul, Pi.smul_apply, smul_eq_mul, ← mul_assoc, h2, one_mul]`.
-/
theorem UpperTheory.V.Af.Nf.liftCent :
    UpperTheory.V.Af.Nf.LiftCent := by
  intro k M hM χ ω hω f hf φ hφ z g
  obtain ⟨r, t, u, ht, hu, rfl⟩ := idele_dec z
  obtain ⟨γ, h, κ, hκ, rfl⟩ := decomp M hM g
  obtain ⟨δ, β, hδ, hβ, hK, hd⟩ := (ratK M hM).2 u hu
  have h1 : ω.1 (Units.map (algebraMap ℚ (Ad ℚ)).toMonoidHom r) = 1 := ω.2.2 r
  have h2 := hω.unit u hu _ hd
  have s1 : GeneralLinearGroup.scalar (Fin 2) (Units.map (algebraMap ℚ (Ad ℚ)).toMonoidHom r) =
      ratGL ℚ 2 (GeneralLinearGroup.scalar (Fin 2) r) := by
    ext i j
    by_cases e : i = j <;> simp [ratGL, Matrix.diagonal_apply, e, Matrix.algebraMap_matrix_apply]
  set T : GL (Fin 2) ℝ := GeneralLinearGroup.map ev (GeneralLinearGroup.scalar (Fin 2) t) with hT
  have s2 : GeneralLinearGroup.scalar (Fin 2) (TR.infId ℚ t) = upR T := by
    rw [hT, upR_ev]
    exact (corner_sc _ t).symm
  have s3 : GeneralLinearGroup.scalar (Fin 2) (finId ℚ u) = finGL ℚ 2 (GeneralLinearGroup.scalar (Fin 2) u) :=
    (corner_sc _ u).symm
  have e : GeneralLinearGroup.scalar (Fin 2) (Units.map (algebraMap ℚ (Ad ℚ)).toMonoidHom r * (TR.infId ℚ t * finId ℚ u)) *
      (ratGL ℚ 2 γ * (upR h * finGL ℚ 2 κ)) = ratGL ℚ 2 (GeneralLinearGroup.scalar (Fin 2) r * γ * β) *
        (upR ((toR β)⁻¹ * (T * h)) * finGL ℚ 2 ((toF β)⁻¹ * GeneralLinearGroup.scalar (Fin 2) u * κ)) := by
    have c : ∀ (x : GL (Fin 2) ℝ) (y : GL (Fin 2) (Af ℚ)) (w : GA ℚ 2), finGL ℚ 2 y * (upR x * w) = upR x * (finGL ℚ 2 y * w) :=
      fun x y w => by rw [← mul_assoc, ← upR_comm, mul_assoc]
    rw [map_mul, mul_assoc, ← mul_assoc _ (ratGL ℚ 2 γ),
      GeneralLinearGroup.scalar_commute (TR.infId ℚ t * finId ℚ u) (ratGL ℚ 2 γ), map_mul, s1, s2, s3,
      map_mul (ratGL ℚ 2), map_mul (ratGL ℚ 2), ratGL_eq β]
    simp only [mul_assoc, c]
    simp only [mul_assoc, map_mul, map_inv, mul_inv_cancel_left]
  have hβ' : (toR β).val = δ.1.map (Int.cast : ℤ → ℝ) := by
    ext i j
    have := congrFun (congrFun hβ i) j
    change (Rat.castHom ℝ) (β.val i j) = _
    rw [this]
    simp
  have e2 : ((toR β)⁻¹ * (T * h)).val = t.val Rat.infinitePlace • ((toR β)⁻¹ * h).val := by
    have : T.val = t.val Rat.infinitePlace • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
      ext i j
      by_cases e : i = j <;> simp [hT, ev, Matrix.diagonal_apply, e]
    simp only [Units.val_mul, this, Matrix.smul_mul, Matrix.mul_smul, one_mul]
  have e3 := ((nslInv k M f ((toR β)⁻¹ * h).val ((toR β)⁻¹ * h).det_ne_zero).2 χ hf δ hδ)
  rw [← hβ', ← Units.val_mul, mul_inv_cancel_left] at e3
  rw [e, hφ _ _ _ (mul_mem hK hκ), hφ _ _ _ hκ, e2, (nslMul k f).2.2.1 _ _ (ht _), e3, map_mul, map_mul, h1, hω.pos t ht,
    one_mul, one_mul, Pi.smul_apply, smul_eq_mul, ← mul_assoc, h2, one_mul]
