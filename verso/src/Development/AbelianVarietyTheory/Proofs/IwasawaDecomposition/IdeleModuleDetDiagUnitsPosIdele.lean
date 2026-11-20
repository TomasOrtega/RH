import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup
  GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

namespace GlobalTheory.CuspBoundSiegel

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

omit [IsTotallyComplex E] in
/- English proof (translation)
Unfold `posIdele`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[← map_mul]`. Use `congr 1`.

Conclude with `Subtype.ext (mul_pow ρ σ _)`.
-/
theorem posIdele_mul (ρ σ : ℝ) (hρ : 0 < ρ) (hσ : 0 < σ) :
    posIdele (K := E) (ρ * σ) (mul_pos hρ hσ) = posIdele ρ hρ * posIdele σ hσ := by
  unfold posIdele
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [← map_mul]
  congr 1
  exact Subtype.ext (mul_pow ρ σ _)

/- English proof (translation)
Use `Units.ext (ad_ext ?_ ?_)` and prove the remaining obligations. Establish `h : ∀ x, pInf E (sInf E x) = x` using `fun x => (infEq E).symm_apply_apply x`. Express the relevant statement in the definitionally equal form `_ = pInf E (1 - sInf E 1 + sInf E _)`. Simplify using `only [map_add, map_sub, map_one, h, sub_self, zero_add]`. Use function extensionality and compare the values at `w`.

Establish `hc` using `IsTotallyComplex.isComplex w`. Establish `hw : ¬ w.IsReal` using `InfinitePlace.not_isReal_iff_isComplex.2 hc`. Use `show (InfinitePlace.Completion.ringEquivComplexOfIsComplex hc) (((posIdele _ _ : IdeleGroup E) : AdeleRing (𝓞 E) E).1 w) = _`. Rewrite using `[← coe_infiniteProj, infiniteProj_posIdele]`. Use `show (InfinitePlace.Completion.ringEquivComplexOfIsComplex hc) (posRealElem w _) = _`.

Unfold `posRealElem`. Rewrite using `[dif_neg hw, RingEquiv.apply_symm_apply]`. Simplify using `[InfinitePlace.mult, hw, Real.sqrt_sq (Real.exp_pos u).le, expU, Complex.ofReal_exp]`. Express the relevant statement in the definitionally equal form `((posIdele _ _ : IdeleGroup E) : AdeleRing (𝓞 E) E).2 = (1 : Af E) - 0 + 0`. Rewrite using `[sub_zero, add_zero]`.

Conclude with `IsDedekindDomain.FiniteAdeleRing.ext _ fun v => by rw [posIdele_finite]; rfl`.
-/
theorem posIdele_exp (u : ℝ) :
    posIdele (K := E) (Real.exp u) (Real.exp_pos u) = infId E (expU fun _ : InfinitePlace E => (u : ℂ)) := by
  refine Units.ext (ad_ext ?_ ?_)
  · have h : ∀ x, pInf E (sInf E x) = x := fun x => (infEq E).symm_apply_apply x
    change _ = pInf E (1 - sInf E 1 + sInf E _)
    simp only [map_add, map_sub, map_one, h, sub_self, zero_add]
    funext w
    have hc := IsTotallyComplex.isComplex w
    have hw : ¬ w.IsReal := InfinitePlace.not_isReal_iff_isComplex.2 hc
    show (InfinitePlace.Completion.ringEquivComplexOfIsComplex hc) (((posIdele _ _ : IdeleGroup E) : AdeleRing (𝓞 E) E).1 w) = _
    rw [← coe_infiniteProj, infiniteProj_posIdele]
    show (InfinitePlace.Completion.ringEquivComplexOfIsComplex hc) (posRealElem w _) = _
    unfold posRealElem
    rw [dif_neg hw, RingEquiv.apply_symm_apply]
    simp [InfinitePlace.mult, hw, Real.sqrt_sq (Real.exp_pos u).le, expU, Complex.ofReal_exp]
  · change ((posIdele _ _ : IdeleGroup E) : AdeleRing (𝓞 E) E).2 = (1 : Af E) - 0 + 0
    rw [sub_zero, add_zero]
    exact IsDedekindDomain.FiniteAdeleRing.ext _ fun v => by rw [posIdele_finite]; rfl

omit [IsTotallyComplex E] in
/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem posIdele_congr {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (h : x = y) :
    posIdele (K := E) x hx = posIdele y hy := by subst h; rfl

/- English proof (translation)
Rewrite using `[splitCentre_eq_scalar, ← posIdele_exp, posIdele_congr hx (Real.exp_pos _) (Real.exp_log hx).symm]`. Use `Units.ext ?_` and prove the remaining obligations. Rewrite using `[coe_diagUnits]`. Both sides reduce to the same expression.
-/
theorem diagUnits_posIdele (a : ℕ) {x : ℝ} (hx : 0 < x) :
    diagUnits a (fun _ : Fin a => posIdele (K := E) x hx) = splitCentre E a (Real.log x) := by
  rw [splitCentre_eq_scalar, ← posIdele_exp, posIdele_congr hx (Real.exp_pos _) (Real.exp_log hx).symm]
  refine Units.ext ?_
  rw [coe_diagUnits]
  rfl

omit [IsTotallyComplex E] in

/- English proof (translation)
Unfold `posIdele`. Conclude with `continuous_finsetProd _ fun w _ => (continuous_moduleSection w).comp (Continuous.subtype_mk ((continuous_subtype_val).pow _) _)`.
-/
theorem continuous_posIdele_pos :
    Continuous fun r : {r : ℝ // 0 < r} => (posIdele (K := E) r.1 r.2 : IdeleGroup E) := by
  unfold posIdele
  exact continuous_finsetProd _ fun w _ => (continuous_moduleSection w).comp
    (Continuous.subtype_mk ((continuous_subtype_val).pow _) _)

omit [IsTotallyComplex E] in

/- English proof (translation)
Establish `hdet : Matrix.GeneralLinearGroup.det (diagUnits a (fun _ : Fin a => posIdele (K` using `E) x hx)) = posIdele x hx ^ a := by`. Use `Units.ext ?_` and prove the remaining obligations. Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply, coe_diagUnits, det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Units.val_pow_eq_pow_val]`. Rewrite using `[hdet, map_pow, Positive.val_pow, ideleModule_posIdele, ← pow_mul, mul_comm]`.
-/
theorem ideleModule_det_diagUnits_posIdele (a : ℕ) {x : ℝ} (hx : 0 < x) :
    (IdeleGroup.ideleModule E (Matrix.GeneralLinearGroup.det
      (diagUnits a (fun _ : Fin a => posIdele (K := E) x hx))) : ℝ) = x ^ (a * Module.finrank ℚ E) := by
  have hdet : Matrix.GeneralLinearGroup.det (diagUnits a (fun _ : Fin a => posIdele (K := E) x hx)) =
      posIdele x hx ^ a := by
    refine Units.ext ?_
    rw [Matrix.GeneralLinearGroup.val_det_apply, coe_diagUnits, det_diagonal, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, Units.val_pow_eq_pow_val]
  rw [hdet, map_pow, Positive.val_pow, ideleModule_posIdele, ← pow_mul, mul_comm]

/- English proof (translation)
Introduce `E _ _ _ a φ hφ hA`. Break down `Nat.eq_zero_or_pos a with rfl | ha` into its components or cases. Use `⟨‖φ.1 1‖, fun g => ?_⟩` and prove the remaining obligations. Establish `: g = 1` using `Units.ext (Subsingleton.elim _ _)`. Rewrite using `[this]`.

Take `⟨ω, hω, hωB, t, ht, hsieg⟩` from `exists_siegelSet (K := E) a`. Use `set d : ℕ := Module.finrank ℚ E with hd`. Establish `hd0 : 0 < d` using `Module.finrank_pos`. Establish `had : a * d ≠ 0` using `(Nat.mul_pos ha hd0).ne'`. Use `set m : AdelicGLn.AdelicGL E a → ℝ := fun b => (IdeleGroup.ideleModule E (Matrix.GeneralLinearGroup.det b) : ℝ) with hm`.

Establish `hmpos : ∀ b, 0 < m b` using `fun b => (IdeleGroup.ideleModule E _).2`. Use `set s : AdelicGLn.AdelicGL E a → ℝ := fun b => m b ^ (((a * d : ℕ) : ℝ)⁻¹) with hs`. Establish `hspos : ∀ b, 0 < s b` using `fun b => Real.rpow_pos_of_pos (hmpos b) _`. Establish `hspow : ∀ b, s b ^ (a * d) = m b` using `fun b => Real.rpow_inv_natCast_pow (hmpos b).le had`. Use `set f : AdelicGLn.AdelicGL E a → AdelicGLn.AdelicGL E a := fun b => b * (diagUnits a (fun _ : Fin a => posIdele (K := E) (s b) (hspos b)))⁻¹ with hf`.

Establish `hmc : Continuous m` using `continuous_subtype_val.comp (continuous_ideleModule.comp (AdelicGLn.continuous_det E a))`. Establish `hsc : Continuous fun b => (⟨s b, hspos b⟩ : {r : ℝ // 0 < r})` using `Continuous.subtype_mk (hmc.rpow_const fun b => Or.inl (hmpos b).ne') _`. Establish `hfc : Continuous f` using `continuous_id.mul ((continuous_diagUnits a).comp (continuous_pi fun _ => continuous_posIdele_pos.comp hsc)).inv`. Establish `hω'c : IsCompact (f '' ω)` using `hω.image hfc`. Establish `hω'B : f '' ω ⊆ (adelicBorel (K` using `E) (n := a) : Set (AdelicGLn.AdelicGL E a)) := by`.

Introduce and unpack `_ ⟨b, hb, rfl⟩`. Conclude with `mul_mem (hωB hb) (inv_mem (diagUnits_mem_adelicBorel a _))`. Establish `hω'1 : ∀ b ∈ f '' ω, (IdeleGroup.ideleModule E (Matrix.GeneralLinearGroup.det b) : ℝ) = 1`. Introduce and unpack `_ ⟨b, -, rfl⟩`. Establish `e : IdeleGroup.ideleModule E (Matrix.GeneralLinearGroup.det (diagUnits a (fun _ : Fin a => posIdele (K` using `E) (s b) (hspos b)))) = IdeleGroup.ideleModule E (Matrix.GeneralLinearGroup.det b) := Subtype.ext (by rw [ideleModule_det_diagUnits_posIdele, hspow])`.

Simplify using `only [hf, map_mul, map_inv, e, mul_inv_cancel]`. Both sides reduce to the same expression. Take `⟨C, hC⟩` from `h E a φ hφ (f '' ω) hω'c hω'B hω'1 t ht 0`. Use `⟨C, fun g => ?_⟩` and prove the remaining obligations. Take `⟨γ, b, hb, _, ⟨r, hr, hrat, rfl⟩, k, hk, e⟩` from `hsieg g`.

Establish `hprod : 0 < ∏ i, r i` using `Finset.prod_pos fun i _ => hr i`. Use `set ρ := (∏ i, r i) ^ ((a : ℝ)⁻¹) with hρ`. Establish `hρpos : 0 < ρ` using `Real.rpow_pos_of_pos hprod _`. Establish `hρa : ρ ^ a = ∏ i, r i` using `Real.rpow_inv_natCast_pow hprod.le ha.ne'`. Use `set r' : Fin a → ℝ := fun i => r i / ρ with hr'`.

Establish `hr'pos : ∀ i, 0 < r' i` using `fun i => div_pos (hr i) hρpos`. Establish `hD : diagUnits a (fun i => posIdele (K` using `E) (r i) (hr i)) = diagUnits a (fun _ : Fin a => posIdele (K := E) ρ hρpos) * diagUnits a (fun i => posIdele (K := E) (r' i) (hr'pos i)) := by`. Rewrite using `[← map_mul]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Rewrite using `[Pi.mul_apply, ← posIdele_mul]`. Conclude with `posIdele_congr _ _ (by simp only [hr']; field_simp)`. Use `set D' := diagUnits a (fun i => posIdele (K := E) (r' i) (hr'pos i)) with hD'`. Establish `key : ratGL E a γ * g = splitCentre E a (Real.log (s b) + Real.log ρ) * (f b * D' * k)`. Express the relevant statement in the definitionally equal form `AdelicGLn.diagonal E a γ * g = _`.

Rewrite using `[e, hD, diagUnits_posIdele a hρpos, splitCentre_add]`. Simplify using `only [hf, diagUnits_posIdele a (hspos b)]`. Use `symm`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [hr']`. Rewrite using `[← mul_div_assoc]`. Conclude with `div_le_div_of_nonneg_right (hrat i j hij) hρpos.le) (by`. Simplify using `only [hr']`. Rewrite using `[Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hρa, div_self hprod.ne']) k hk`.

Use `_ = C := by simp`.
-/
theorem cuspFormsBounded_of_rapidDecay (h : GlobalTheory.Published.CuspRapidDecaySiegelGL) : GlobalTheory.Published.CuspFormsBoundedGL := by
  intro E _ _ _ a φ hφ hA
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · refine ⟨‖φ.1 1‖, fun g => ?_⟩
    have : g = 1 := Units.ext (Subsingleton.elim _ _)
    rw [this]
  obtain ⟨ω, hω, hωB, t, ht, hsieg⟩ := exists_siegelSet (K := E) a
  set d : ℕ := Module.finrank ℚ E with hd
  have hd0 : 0 < d := Module.finrank_pos
  have had : a * d ≠ 0 := (Nat.mul_pos ha hd0).ne'
  set m : AdelicGLn.AdelicGL E a → ℝ :=
    fun b => (IdeleGroup.ideleModule E (Matrix.GeneralLinearGroup.det b) : ℝ) with hm
  have hmpos : ∀ b, 0 < m b := fun b => (IdeleGroup.ideleModule E _).2
  set s : AdelicGLn.AdelicGL E a → ℝ := fun b => m b ^ (((a * d : ℕ) : ℝ)⁻¹) with hs
  have hspos : ∀ b, 0 < s b := fun b => Real.rpow_pos_of_pos (hmpos b) _
  have hspow : ∀ b, s b ^ (a * d) = m b := fun b => Real.rpow_inv_natCast_pow (hmpos b).le had
  set f : AdelicGLn.AdelicGL E a → AdelicGLn.AdelicGL E a :=
    fun b => b * (diagUnits a (fun _ : Fin a => posIdele (K := E) (s b) (hspos b)))⁻¹ with hf
  have hmc : Continuous m :=
    continuous_subtype_val.comp (continuous_ideleModule.comp (AdelicGLn.continuous_det E a))
  have hsc : Continuous fun b => (⟨s b, hspos b⟩ : {r : ℝ // 0 < r}) :=
    Continuous.subtype_mk (hmc.rpow_const fun b => Or.inl (hmpos b).ne') _
  have hfc : Continuous f := continuous_id.mul ((continuous_diagUnits a).comp
    (continuous_pi fun _ => continuous_posIdele_pos.comp hsc)).inv
  have hω'c : IsCompact (f '' ω) := hω.image hfc
  have hω'B : f '' ω ⊆ (adelicBorel (K := E) (n := a) : Set (AdelicGLn.AdelicGL E a)) := by
    rintro _ ⟨b, hb, rfl⟩
    exact mul_mem (hωB hb) (inv_mem (diagUnits_mem_adelicBorel a _))
  have hω'1 : ∀ b ∈ f '' ω, (IdeleGroup.ideleModule E (Matrix.GeneralLinearGroup.det b) : ℝ) = 1 := by
    rintro _ ⟨b, -, rfl⟩
    have e : IdeleGroup.ideleModule E (Matrix.GeneralLinearGroup.det
        (diagUnits a (fun _ : Fin a => posIdele (K := E) (s b) (hspos b)))) =
        IdeleGroup.ideleModule E (Matrix.GeneralLinearGroup.det b) :=
      Subtype.ext (by rw [ideleModule_det_diagUnits_posIdele, hspow])
    simp only [hf, map_mul, map_inv, e, mul_inv_cancel]
    rfl
  obtain ⟨C, hC⟩ := h E a φ hφ (f '' ω) hω'c hω'B hω'1 t ht 0
  refine ⟨C, fun g => ?_⟩
  obtain ⟨γ, b, hb, _, ⟨r, hr, hrat, rfl⟩, k, hk, e⟩ := hsieg g
  have hprod : 0 < ∏ i, r i := Finset.prod_pos fun i _ => hr i
  set ρ := (∏ i, r i) ^ ((a : ℝ)⁻¹) with hρ
  have hρpos : 0 < ρ := Real.rpow_pos_of_pos hprod _
  have hρa : ρ ^ a = ∏ i, r i := Real.rpow_inv_natCast_pow hprod.le ha.ne'
  set r' : Fin a → ℝ := fun i => r i / ρ with hr'
  have hr'pos : ∀ i, 0 < r' i := fun i => div_pos (hr i) hρpos
  have hD : diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) =
      diagUnits a (fun _ : Fin a => posIdele (K := E) ρ hρpos) *
        diagUnits a (fun i => posIdele (K := E) (r' i) (hr'pos i)) := by
    rw [← map_mul]
    congr 1
    funext i
    rw [Pi.mul_apply, ← posIdele_mul]
    exact posIdele_congr _ _ (by simp only [hr']; field_simp)
  set D' := diagUnits a (fun i => posIdele (K := E) (r' i) (hr'pos i)) with hD'
  have key : ratGL E a γ * g = splitCentre E a (Real.log (s b) + Real.log ρ) * (f b * D' * k) := by
    change AdelicGLn.diagonal E a γ * g = _
    rw [e, hD, diagUnits_posIdele a hρpos, splitCentre_add]
    simp only [hf, diagUnits_posIdele a (hspos b)]
    symm
    calc splitCentre E a (Real.log (s b)) * splitCentre E a (Real.log ρ) *
          (b * (splitCentre E a (Real.log (s b)))⁻¹ * D' * k)
        = splitCentre E a (Real.log (s b)) * (splitCentre E a (Real.log ρ) *
            (b * (splitCentre E a (Real.log (s b)))⁻¹)) * D' * k := by group
      _ = splitCentre E a (Real.log (s b)) * ((b * (splitCentre E a (Real.log (s b)))⁻¹) *
            splitCentre E a (Real.log ρ)) * D' * k := by rw [splitCentre_comm (Real.log ρ)]
      _ = (splitCentre E a (Real.log (s b)) * b) * (splitCentre E a (Real.log (s b)))⁻¹ *
            splitCentre E a (Real.log ρ) * D' * k := by group
      _ = (b * splitCentre E a (Real.log (s b))) * (splitCentre E a (Real.log (s b)))⁻¹ *
            splitCentre E a (Real.log ρ) * D' * k := by rw [splitCentre_comm (Real.log (s b)) b]
      _ = b * (splitCentre E a (Real.log ρ) * D') * k := by group
  calc ‖φ.1 g‖ = ‖φ.1 (ratGL E a γ * g)‖ := by rw [hφ.1.left]
    _ = ‖φ.1 (f b * D' * k)‖ := by rw [key, hA]
    _ ≤ C * ∏ i, r' i ^ (0 : Fin a → ℝ) i := hC (f b) ⟨b, hb, rfl⟩ r' hr'pos (fun i j hij => by
          simp only [hr']
          rw [← mul_div_assoc]
          exact div_le_div_of_nonneg_right (hrat i j hij) hρpos.le) (by
          simp only [hr']
          rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hρa,
            div_self hprod.ne']) k hk
    _ = C := by simp

end GlobalTheory.CuspBoundSiegel

end
