import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.ThStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.HeightBoundOfQuasiHeightLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.GeometricSideQuadraticFormIdentity
open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.Reduction

/- English proof (translation)
Establish `c2 : Continuous (infEq E).symm`. Use `continuous_pi fun w => ?_` and prove the remaining obligations. Conclude with `(InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp (continuous_apply w)`. Conclude with `c2.comp continuous_fst`.
-/
private theorem cont_pInf {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] : Continuous (pInf E) := by
  have c2 : Continuous (infEq E).symm := by
    refine continuous_pi fun w => ?_
    exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)
  exact c2.comp continuous_fst

/- English proof (translation)
Use function extensionality and compare the values at `w`. Establish `hw : ¬ w.IsReal` using `InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)`. Establish `h : ((posIdele s hs : GroundTheory.Global.IdeleGroup E) : AdeleRing (𝓞 E) E).1 w = (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).symm (s : ℂ)`. Rewrite using `[← GroundTheory.Global.IdeleGroup.coe_infiniteProj, infiniteProj_posIdele]`. Express the relevant statement in the definitionally equal form `GroundTheory.Global.posRealElem w _ = _`.

Unfold `GroundTheory.Global.posRealElem`. Rewrite using `[dif_neg hw]`. Simplify using `[InfinitePlace.mult, hw, Real.sqrt_sq hs.le]`. Express the relevant statement in the definitionally equal form `(InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)) (((posIdele s hs : GroundTheory.Global.IdeleGroup E) : AdeleRing (𝓞 E) E).1 w) = _`. Rewrite using `[h, RingEquiv.apply_symm_apply]`.
-/
private theorem pInf_pos {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (s : ℝ) (hs : 0 < s) :
    pInf E ((posIdele (K := E) s hs : GroundTheory.Global.IdeleGroup E) : Ad E) = fun _ => (s : ℂ) := by
  funext w
  have hw : ¬ w.IsReal := InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)
  have h : ((posIdele s hs : GroundTheory.Global.IdeleGroup E) : AdeleRing (𝓞 E) E).1 w =
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).symm (s : ℂ) := by
    rw [← GroundTheory.Global.IdeleGroup.coe_infiniteProj, infiniteProj_posIdele]
    change GroundTheory.Global.posRealElem w _ = _
    unfold GroundTheory.Global.posRealElem
    rw [dif_neg hw]
    simp [InfinitePlace.mult, hw, Real.sqrt_sq hs.le]
  change (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w))
    (((posIdele s hs : GroundTheory.Global.IdeleGroup E) : AdeleRing (𝓞 E) E).1 w) = _
  rw [h, RingEquiv.apply_symm_apply]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `((posIdele s hs : GroundTheory.Global.IdeleGroup E) : AdeleRing (𝓞 E) E).2 = (1 : Af E)`. Conclude with `IsDedekindDomain.FiniteAdeleRing.ext _ fun v => by rw [posIdele_finite]; rfl`.
-/
private theorem pFin_pos {E : Type} [Field E] [NumberField E] (s : ℝ) (hs : 0 < s) :
    pFin E ((posIdele (K := E) s hs : GroundTheory.Global.IdeleGroup E) : Ad E) = 1 := by
  change ((posIdele s hs : GroundTheory.Global.IdeleGroup E) : AdeleRing (𝓞 E) E).2 = (1 : Af E)
  exact IsDedekindDomain.FiniteAdeleRing.ext _ fun v => by rw [posIdele_finite]; rfl

/- English proof (translation)
Establish `h1 : g⁻¹ * γ⁻¹ = k⁻¹ * d⁻¹ * b⁻¹`. Rewrite using `[← _root_.mul_inv_rev, h]`. Simplify using `[mul_assoc]`. Establish `h2 : ((g⁻¹).val *ᵥ fun i => (γ⁻¹).val i i₀) = (k⁻¹ * d⁻¹).val *ᵥ fun i => (b⁻¹).val i i₀`. Use function extensionality and compare the values at `i`.

Use `congrArg (fun x : GL (Fin a) R => x.val i i₀) h1` as an intermediate fact. Simplify `this` using `only [Units.val_mul, Matrix.mul_apply, Matrix.mulVec, dotProduct]`. Establish `h3 : u i₀ • (fun i => (b⁻¹).val i i₀) = d.val *ᵥ fun i => (b⁻¹).val i i₀`. Use function extensionality and compare the values at `i`. Rewrite using `[hd, Matrix.mulVec_diagonal]`.

Distinguish the cases in `hi : i = i₀`. Substitute `hi` using the available equality. Both sides reduce to the same expression. Simplify using `only [Pi.smul_apply, hb i hi, smul_zero, mul_zero]`. Rewrite using `[h2, ← Matrix.mulVec_smul, h3, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel_right]`.

Both sides reduce to the same expression.
-/
private theorem col_eq {R : Type} [CommRing R] {a : ℕ} (i₀ : Fin a) (g γ b d k : GL (Fin a) R) (u : Fin a → R)
    (hd : d.val = Matrix.diagonal u) (hb : ∀ i, i ≠ i₀ → (b⁻¹).val i i₀ = 0) (h : γ * g = b * d * k) :
    u i₀ • ((g⁻¹).val *ᵥ fun i => (γ⁻¹).val i i₀) = fun i => (k⁻¹ * b⁻¹).val i i₀ := by
  have h1 : g⁻¹ * γ⁻¹ = k⁻¹ * d⁻¹ * b⁻¹ := by
    rw [← _root_.mul_inv_rev, h]; simp [mul_assoc]
  have h2 : ((g⁻¹).val *ᵥ fun i => (γ⁻¹).val i i₀) = (k⁻¹ * d⁻¹).val *ᵥ fun i => (b⁻¹).val i i₀ := by
    funext i
    have := congrArg (fun x : GL (Fin a) R => x.val i i₀) h1
    simpa only [Units.val_mul, Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  have h3 : u i₀ • (fun i => (b⁻¹).val i i₀) = d.val *ᵥ fun i => (b⁻¹).val i i₀ := by
    funext i
    rw [hd, Matrix.mulVec_diagonal]
    by_cases hi : i = i₀
    · subst hi; rfl
    · simp only [Pi.smul_apply, hb i hi, smul_zero, mul_zero]
  rw [h2, ← Matrix.mulVec_smul, h3, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel_right]
  rfl

/- English proof (translation)
Introduce `E _ _ _ a ha`. Take `⟨Ω, C, N, hΩ, hB, hS⟩` from `UpperTheory.height_bound_of_quasiHeight_le E a`. Take `⟨-, -, -, hsm, -, -⟩` from `UpperTheory.geometric_side_quadraticForm_identity E a`. Set `i₀ : Fin a` to `⟨0, ha⟩`. Establish `hK : IsCompact (maxCompact (K` using `E) (n := a) : Set (GA E a)) := isCompact_maxCompact`.

Set `f : GA E a × GA E a → Fin a → Ad E` to `fun p i => (p.1⁻¹ * p.2⁻¹).val i i₀`. Establish `hf : Continuous f` using `continuous_pi fun i => (Units.continuous_val.comp (continuous_fst.inv.mul continuous_snd.inv)).matrix_elem i i₀`. Establish `hc` using `hK.prod hΩ`. Establish `hF : Continuous fun p i => pFin E (f p i)` using `continuous_pi fun i => continuous_snd.comp ((continuous_apply i).comp hf)`. Establish `hI : Continuous fun p => qf (fun i => pInf E (f p i))`.

Unfold `qf`. Use `continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun w _ => ?_` and prove the remaining obligations. Conclude with `(((continuous_apply w).comp (cont_pInf.comp ((continuous_apply i).comp hf))).norm).pow 2`. Take `⟨M, hM⟩` from `hc.bddAbove_image hI.continuousOn`. Use `⟨_, |C| * M ^ N, N, hc.image hF, fun g => ?_⟩` and prove the remaining obligations.

Take `⟨γ, b, k, ρ, hρ, hb, hk, he, hh⟩` from `hS g`. Establish `hh0` using `(hh i₀).2 rfl`. Establish `hcol` using `col_eq i₀ (g.1 : GA E a) (ratGL E a γ) b _ k (fun i => ((posIdele (K := E) (ρ i) (hρ i) : GroundTheory.Global.IdeleGroup E) : Ad E)) (coe_diagUnits _ _) (fun i hi => mem_adelicBorel.1 (inv_mem (hB b hb)) (Fin.lt_def.2 (Nat.pos_of_ne_zero fun h => hi (Fin.ext h)))) he`. Establish `hγ : (fun i => ((ratGL E a γ)⁻¹).val i i₀) = fun i => algebraMap E (Ad E) ((γ⁻¹).val i i₀)`. Rewrite using `[← map_inv]`.

Both sides reduce to the same expression. Rewrite `hcol` using `[hγ]`. Use `⟨fun i => (γ⁻¹).val i i₀, fun h0 => ?_, ⟨(k, b), ⟨hk, hb⟩, ?_⟩, ?_⟩` and prove the remaining obligations. Establish `h1 : (γ * γ⁻¹).val i₀ i₀ = 0`. Rewrite using `[Units.val_mul, Matrix.mul_apply]`.

Conclude with `Finset.sum_eq_zero fun j _ => by rw [congrFun h0 j]; simp`. Simplify using `at h1`. Use function extensionality and compare the values at `i`. Establish `h1` using `congrArg (pFin E) (congrFun hcol i)`. Rewrite `h1` using `[Pi.smul_apply, smul_eq_mul, map_mul, pFin_pos, one_mul, RingHom.map_mulVec]`.

Conclude with `h1.symm`. Establish `h1 : (fun i => pInf E (f (k, b) i)) = ρ i₀ • ((GeneralLinearGroup.map (pInf E) (g.1⁻¹ : GA E a)).val *ᵥ vInf fun i => (γ⁻¹).val i i₀)`. Use function extensionality and compare the values at `i`. Establish `h1` using `congrArg (pInf E) (congrFun hcol i)`. Rewrite `h1` using `[Pi.smul_apply, smul_eq_mul, map_mul, pInf_pos, RingHom.map_mulVec]`.

Use `h1.symm.trans ?_` and prove the remaining obligations. Use function extensionality and compare the values at `w`. Rewrite using `[Pi.smul_apply, Pi.smul_apply, Complex.real_smul]`. Both sides reduce to the same expression. Establish `h2 : qf (fun i => pInf E (f (k, b) i)) ≤ M` using `hM ⟨(k, b), ⟨hk, hb⟩, rfl⟩`.

Rewrite `h2` using `[h1, hsm]`. Use `set q := qf ((GeneralLinearGroup.map (pInf E) (g.1⁻¹ : GA E a)).val *ᵥ vInf fun i => (γ⁻¹).val i i₀) with hq`. Establish `hq0 : 0 ≤ q` using `qf_nonneg _`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem UpperTheory.positivity_at_all_places :
    SiegelCol := by
  intro E _ _ _ a ha
  obtain ⟨Ω, C, N, hΩ, hB, hS⟩ := UpperTheory.height_bound_of_quasiHeight_le E a
  obtain ⟨-, -, -, hsm, -, -⟩ := UpperTheory.geometric_side_quadraticForm_identity E a
  let i₀ : Fin a := ⟨0, ha⟩
  have hK : IsCompact (maxCompact (K := E) (n := a) : Set (GA E a)) := isCompact_maxCompact
  let f : GA E a × GA E a → Fin a → Ad E := fun p i => (p.1⁻¹ * p.2⁻¹).val i i₀
  have hf : Continuous f := continuous_pi fun i =>
    (Units.continuous_val.comp (continuous_fst.inv.mul continuous_snd.inv)).matrix_elem i i₀
  have hc := hK.prod hΩ
  have hF : Continuous fun p i => pFin E (f p i) := continuous_pi fun i =>
    continuous_snd.comp ((continuous_apply i).comp hf)
  have hI : Continuous fun p => qf (fun i => pInf E (f p i)) := by
    unfold qf
    refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun w _ => ?_
    exact (((continuous_apply w).comp (cont_pInf.comp ((continuous_apply i).comp hf))).norm).pow 2
  obtain ⟨M, hM⟩ := hc.bddAbove_image hI.continuousOn
  refine ⟨_, |C| * M ^ N, N, hc.image hF, fun g => ?_⟩
  obtain ⟨γ, b, k, ρ, hρ, hb, hk, he, hh⟩ := hS g
  have hh0 := (hh i₀).2 rfl
  have hcol := col_eq i₀ (g.1 : GA E a) (ratGL E a γ) b _ k
    (fun i => ((posIdele (K := E) (ρ i) (hρ i) : GroundTheory.Global.IdeleGroup E) : Ad E)) (coe_diagUnits _ _)
    (fun i hi => mem_adelicBorel.1 (inv_mem (hB b hb)) (Fin.lt_def.2 (Nat.pos_of_ne_zero fun h => hi (Fin.ext h)))) he
  have hγ : (fun i => ((ratGL E a γ)⁻¹).val i i₀) = fun i => algebraMap E (Ad E) ((γ⁻¹).val i i₀) := by
    rw [← map_inv]; rfl
  rw [hγ] at hcol
  refine ⟨fun i => (γ⁻¹).val i i₀, fun h0 => ?_, ⟨(k, b), ⟨hk, hb⟩, ?_⟩, ?_⟩
  · have h1 : (γ * γ⁻¹).val i₀ i₀ = 0 := by
      rw [Units.val_mul, Matrix.mul_apply]
      exact Finset.sum_eq_zero fun j _ => by rw [congrFun h0 j]; simp
    simp at h1
  · funext i
    have h1 := congrArg (pFin E) (congrFun hcol i)
    rw [Pi.smul_apply, smul_eq_mul, map_mul, pFin_pos, one_mul, RingHom.map_mulVec] at h1
    exact h1.symm
  · have h1 : (fun i => pInf E (f (k, b) i)) =
        ρ i₀ • ((GeneralLinearGroup.map (pInf E) (g.1⁻¹ : GA E a)).val *ᵥ vInf fun i => (γ⁻¹).val i i₀) := by
      funext i
      have h1 := congrArg (pInf E) (congrFun hcol i)
      rw [Pi.smul_apply, smul_eq_mul, map_mul, pInf_pos, RingHom.map_mulVec] at h1
      refine h1.symm.trans ?_
      funext w
      rw [Pi.smul_apply, Pi.smul_apply, Complex.real_smul]
      rfl
    have h2 : qf (fun i => pInf E (f (k, b) i)) ≤ M := hM ⟨(k, b), ⟨hk, hb⟩, rfl⟩
    rw [h1, hsm] at h2
    set q := qf ((GeneralLinearGroup.map (pInf E) (g.1⁻¹ : GA E a)).val *ᵥ vInf fun i => (γ⁻¹).val i i₀) with hq
    have hq0 : 0 ≤ q := qf_nonneg _
    calc _ ≤ C * ρ i₀ ^ (2 * N) * q ^ N := mul_le_mul_of_nonneg_right hh0 (pow_nonneg hq0 N)
      _ = C * (ρ i₀ ^ 2 * q) ^ N := by rw [mul_pow, ← pow_mul, mul_assoc]
      _ ≤ |C| * M ^ N := mul_le_mul (le_abs_self C) (pow_le_pow_left₀ (by positivity) h2 N) (by positivity) (abs_nonneg C)
