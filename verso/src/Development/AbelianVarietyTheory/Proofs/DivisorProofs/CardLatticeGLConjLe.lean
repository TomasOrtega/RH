import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SetIntegralNormRmulLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousIntegralInvMulOfLocallyIntegrable
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLieSmoothingMemSlowlyIncreasing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalGLBoundedSizeCompactFinitePolynomialCounStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsSplitCentreExponentLeOfConjMemCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousGLAdelicProjectionsInclusionsStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory

namespace GlobalTheory

/- English proof (translation)
Introduce `E _ _ _ a`. Break down `Nat.eq_zero_or_pos a with rfl | ha` into its components or cases. Use `⟨0, fun W _ => ⟨1, zero_le_one, fun y => ?_⟩⟩` and prove the remaining obligations. Establish `hs : ∀ s : Set (GlobalTheory.UnitaryBC.latticeGL E 0), s.Subsingleton` using `fun s x _ z _ => Subtype.ext (Units.ext (Matrix.ext fun i => Fin.elim0 i))`. Use `⟨(hs _).finite, ?_⟩` and prove the remaining obligations.

Rewrite using `[pow_zero, mul_one]`. Conclude with `(Set.ncard_le_one_iff (hs _).finite).2 fun h1 h2 => hs _ h1 h2` after adjusting the coercions. Take `⟨m, hm⟩` from `GlobalTheory.T.rationalGL_boundedSize_compactFinite_polynomialCount E a`. Use `⟨m, fun W hW => ?_⟩` and prove the remaining obligations. Take `⟨n₀, hn₀⟩` from `GlobalTheory.T.abs_splitCentre_exponent_le_of_conj_mem_compact E a ha W hW`.

Take `⟨hInf, hFin, -, -⟩` from `GlobalTheory.T.continuous_GL_adelic_projections_inclusions E a`. Use `set e : GA E a := GlobalTheory.UnitaryBC.splitCentre E a 1 with he`. Use `set W' : Set (GA E a) := ⋃ n ∈ Finset.Icc (-(n₀ : ℤ)) n₀, (fun g => g * (e ^ n)⁻¹) '' W with hW'`. Establish `hW'c : IsCompact W'` using `(Finset.Icc (-(n₀ : ℤ)) n₀).isCompact_biUnion fun n _ => hW.image (continuous_mul_right _)`. Use `set Kf : Set (GL (Fin a) (Af E)) := (fun g : GA E a => Matrix.GeneralLinearGroup.map (pFin E) g) '' W' with hKf`.

Establish `hKfc : IsCompact Kf` using `hW'c.image hFin`. Establish `hv : Continuous fun g : GA E a => ((Matrix.GeneralLinearGroup.map (pInf E) g : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E))` using `Units.continuous_val.comp hInf`. Establish `ht : Continuous (toL : Matrix (Fin a) (Fin a) (Cinf E) → Lie E a)` using `continuous_id`. Establish `hcn : Continuous fun g : GA E a => ‖toL (Matrix.GeneralLinearGroup.map (pInf E) g).val‖` using `continuous_norm.comp (ht.comp hv)`. Take `⟨B₀, hB₀⟩` from `hW'c.exists_bound_of_continuousOn hcn.continuousOn`.

Use `set B : ℝ := max 0 B₀ with hB`. Establish `hB0 : 0 ≤ B` using `le_max_left _ _`. Establish `hBb : ∀ w ∈ W', ‖toL (Matrix.GeneralLinearGroup.map (pInf E) w).val‖ ≤ B` using `fun w hw => (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hB₀ w hw).trans (le_max_right _ _))`. Take `⟨C₁, hC₁0, hC₁⟩` from `hm Kf hKfc`. Use `set N : ℝ := ((Set.Icc (-(n₀ : ℤ)) n₀).ncard : ℝ) with hN`.

Use `set c : ℝ := 1 + (a : ℝ) ^ 2 * B with hc`. Establish `hc1 : 1 ≤ c`. Establish `: 0 ≤ (a : ℝ) ^ 2 * B` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨C₁ * c ^ m * N, by positivity, fun y => ?_⟩` and prove the remaining obligations.

Use `set T : ℝ := c * height y ^ 2 with hT`. Establish `hh` using `one_le_height y`. Establish `hT1 : 1 ≤ T` using `one_le_mul_of_one_le_of_one_le hc1 (one_le_pow₀ hh)`. Take `⟨hfin, hcard⟩` from `hC₁ T hT1`. Use `set S := {δ : GL (Fin a) E | ‖toL (Matrix.GeneralLinearGroup.map (pInf E) (ratGL E a δ)).val‖ ≤ T ∧ Matrix.GeneralLinearGroup.map (pFin E) (ratGL E a δ) ∈ Kf} with hS`.

Set `f : GL (Fin a) E × ℤ → GlobalTheory.UnitaryBC.latticeGL E a` to `fun p => ⟨ratGL E a p.1 * e ^ p.2, GlobalTheory.CuspRep.CuspidalL2GL.mem_latticeGL_iff.2 ⟨p.1, p.2, rfl⟩⟩`. Establish `hsub : {γ : GlobalTheory.UnitaryBC.latticeGL E a | (infGL E a y)⁻¹ * (γ : GA E a) * infGL E a y ∈ W} ⊆ f '' (S ×ˢ Set.Icc (-(n₀ : ℤ)) n₀)`. Introduce and unpack `⟨γ, hγ⟩ hγW`. Take `⟨δ, n, rfl⟩` from `GlobalTheory.CuspRep.CuspidalL2GL.mem_latticeGL_iff.1 hγ`. Express the relevant statement in the definitionally equal form `(infGL E a y)⁻¹ * (ratGL E a δ * e ^ n) * infGL E a y ∈ W at hγW`.

Establish `hn : |n| ≤ n₀` using `hn₀ δ n _ hγW`. Establish `hn' : n ∈ Set.Icc (-(n₀ : ℤ)) n₀` using `abs_le.1 hn`. Use `set w := (infGL E a y)⁻¹ * ratGL E a δ * infGL E a y with hw`. Establish `hcomm : Commute (e ^ n) (infGL E a y)` using `(Commute.zpow_left (GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm 1 (infGL E a y)) n)`. Establish `hwW : w ∈ W'`.

Use `Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_Icc.2 hn')) ⟨_, hγW, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(infGL E a y)⁻¹ * (ratGL E a δ * e ^ n) * infGL E a y * (e ^ n)⁻¹ = w`. Simplify using `only [mul_assoc]`. Rewrite using `[← mul_assoc (e ^ n) (infGL E a y), hcomm.eq, mul_inv_cancel_right]`. Apply the tactic sequence `all_goals simp only [hw, mul_assoc]`.

Establish `hδ : ratGL E a δ = infGL E a y * w * (infGL E a y)⁻¹` using `by rw [hw]; group`. Use `⟨(δ, n), ⟨⟨?_, ?_⟩, hn'⟩, rfl⟩` and prove the remaining obligations. Establish `e1 : Matrix.GeneralLinearGroup.map (pInf E) (ratGL E a δ) = y * Matrix.GeneralLinearGroup.map (pInf E) w * y⁻¹`. Rewrite using `[hδ, map_mul, map_mul, map_inv, pInf_infGL]`. Rewrite using `[e1, Units.val_mul, Units.val_mul]`.

Establish `hw'` using `hBb w hwW`. Establish `p1` using `GlobalTheory.AutGrowth.norm_toL_mul_le (y.val * (Matrix.GeneralLinearGroup.map (pInf E) w).val) (y⁻¹).val`. Establish `p2` using `GlobalTheory.AutGrowth.norm_toL_mul_le y.val (Matrix.GeneralLinearGroup.map (pInf E) w).val`. Establish `hy1 : ‖toL y.val‖ ≤ height y`. Unfold `height`.

Combine the linear relations using `[norm_nonneg (toL (y⁻¹).val)]`. Establish `hy2 : ‖toL (y⁻¹).val‖ ≤ height y`. Unfold `height`. Combine the linear relations using `[norm_nonneg (toL y.val)]`. Establish `n1` using `norm_nonneg (toL y.val)`.

Establish `n2` using `norm_nonneg (toL (y⁻¹).val)`. Establish `n3` using `norm_nonneg (toL (Matrix.GeneralLinearGroup.map (pInf E) w).val)`. Establish `ha0 : (0 : ℝ) ≤ a` using `Nat.cast_nonneg a`. Establish `q1 : ‖toL (y.val * (Matrix.GeneralLinearGroup.map (pInf E) w).val)‖ ≤ a * (height y * B)` using `p2.trans (mul_le_mul_of_nonneg_left (mul_le_mul hy1 hw' n3 (by linarith)) ha0)`. Establish `q2 : ‖toL (y.val * (Matrix.GeneralLinearGroup.map (pInf E) w).val * (y⁻¹).val)‖ ≤ a * ((a * (height y * B)) * height y)` using `p1.trans (mul_le_mul_of_nonneg_left (mul_le_mul q1 hy2 n2 (by positivity)) ha0)`.

Use `q2.trans ?_` and prove the remaining obligations. Rewrite using `[hT, hc]`. Establish `: 0 ≤ height y ^ 2` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Establish `e2 : Matrix.GeneralLinearGroup.map (pFin E) (ratGL E a δ) = Matrix.GeneralLinearGroup.map (pFin E) w`.

Rewrite using `[hδ, map_mul, map_mul, map_inv, pFin_infGL, inv_one, one_mul, mul_one]`. Rewrite using `[e2]`. Conclude with `⟨w, hwW, rfl⟩`. Establish `hfin2 : (f '' (S ×ˢ Set.Icc (-(n₀ : ℤ)) n₀)).Finite` using `(hfin.prod (Set.finite_Icc _ _)).image f`. Use `⟨hfin2.subset hsub, ?_⟩` and prove the remaining obligations.

Establish `k1` using `Set.ncard_le_ncard hsub hfin2`. Establish `k2` using `Set.ncard_image_le (f := f) (hfin.prod (Set.finite_Icc (-(n₀ : ℤ)) n₀))`. Rewrite `k2` using `[Set.ncard_prod]`. Establish `k3 : (({γ : GlobalTheory.UnitaryBC.latticeGL E a | (infGL E a y)⁻¹ * (γ : GA E a) * infGL E a y ∈ W}.ncard : ℕ) : ℝ) ≤ (S.ncard : ℝ) * N` using `by rw [hN]; exact_mod_cast k1.trans k2`. Use `k3.trans ?_` and prove the remaining obligations.

Establish `hN0 : 0 ≤ N` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem card_latticeGL_conj_le : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), ∃ A : ℕ,
    ∀ W : Set (GA E a), IsCompact W → ∃ C : ℝ, 0 ≤ C ∧ ∀ y : GL (Fin a) (Cinf E),
      {γ : GlobalTheory.UnitaryBC.latticeGL E a | (infGL E a y)⁻¹ * (γ : GA E a) * infGL E a y ∈ W}.Finite ∧
      ({γ : GlobalTheory.UnitaryBC.latticeGL E a | (infGL E a y)⁻¹ * (γ : GA E a) * infGL E a y ∈ W}.ncard : ℝ) ≤
        C * height y ^ (2 * A) := by
  intro E _ _ _ a
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · refine ⟨0, fun W _ => ⟨1, zero_le_one, fun y => ?_⟩⟩
    have hs : ∀ s : Set (GlobalTheory.UnitaryBC.latticeGL E 0), s.Subsingleton := fun s x _ z _ =>
      Subtype.ext (Units.ext (Matrix.ext fun i => Fin.elim0 i))
    refine ⟨(hs _).finite, ?_⟩
    rw [pow_zero, mul_one]
    exact_mod_cast (Set.ncard_le_one_iff (hs _).finite).2 fun h1 h2 => hs _ h1 h2
  obtain ⟨m, hm⟩ := GlobalTheory.T.rationalGL_boundedSize_compactFinite_polynomialCount E a
  refine ⟨m, fun W hW => ?_⟩
  obtain ⟨n₀, hn₀⟩ := GlobalTheory.T.abs_splitCentre_exponent_le_of_conj_mem_compact E a ha W hW
  obtain ⟨hInf, hFin, -, -⟩ := GlobalTheory.T.continuous_GL_adelic_projections_inclusions E a
  set e : GA E a := GlobalTheory.UnitaryBC.splitCentre E a 1 with he
  set W' : Set (GA E a) := ⋃ n ∈ Finset.Icc (-(n₀ : ℤ)) n₀, (fun g => g * (e ^ n)⁻¹) '' W with hW'
  have hW'c : IsCompact W' := (Finset.Icc (-(n₀ : ℤ)) n₀).isCompact_biUnion fun n _ =>
    hW.image (continuous_mul_right _)
  set Kf : Set (GL (Fin a) (Af E)) := (fun g : GA E a => Matrix.GeneralLinearGroup.map (pFin E) g) '' W' with hKf
  have hKfc : IsCompact Kf := hW'c.image hFin
  have hv : Continuous fun g : GA E a =>
      ((Matrix.GeneralLinearGroup.map (pInf E) g : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) :=
    Units.continuous_val.comp hInf
  have ht : Continuous (toL : Matrix (Fin a) (Fin a) (Cinf E) → Lie E a) := continuous_id
  have hcn : Continuous fun g : GA E a => ‖toL (Matrix.GeneralLinearGroup.map (pInf E) g).val‖ :=
    continuous_norm.comp (ht.comp hv)
  obtain ⟨B₀, hB₀⟩ := hW'c.exists_bound_of_continuousOn hcn.continuousOn
  set B : ℝ := max 0 B₀ with hB
  have hB0 : 0 ≤ B := le_max_left _ _
  have hBb : ∀ w ∈ W', ‖toL (Matrix.GeneralLinearGroup.map (pInf E) w).val‖ ≤ B := fun w hw =>
    (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hB₀ w hw).trans (le_max_right _ _))
  obtain ⟨C₁, hC₁0, hC₁⟩ := hm Kf hKfc
  set N : ℝ := ((Set.Icc (-(n₀ : ℤ)) n₀).ncard : ℝ) with hN
  set c : ℝ := 1 + (a : ℝ) ^ 2 * B with hc
  have hc1 : 1 ≤ c := by
    have : 0 ≤ (a : ℝ) ^ 2 * B := by positivity
    linarith
  refine ⟨C₁ * c ^ m * N, by positivity, fun y => ?_⟩
  set T : ℝ := c * height y ^ 2 with hT
  have hh := one_le_height y
  have hT1 : 1 ≤ T := one_le_mul_of_one_le_of_one_le hc1 (one_le_pow₀ hh)
  obtain ⟨hfin, hcard⟩ := hC₁ T hT1
  set S := {δ : GL (Fin a) E | ‖toL (Matrix.GeneralLinearGroup.map (pInf E) (ratGL E a δ)).val‖ ≤ T ∧
    Matrix.GeneralLinearGroup.map (pFin E) (ratGL E a δ) ∈ Kf} with hS
  let f : GL (Fin a) E × ℤ → GlobalTheory.UnitaryBC.latticeGL E a := fun p =>
    ⟨ratGL E a p.1 * e ^ p.2, GlobalTheory.CuspRep.CuspidalL2GL.mem_latticeGL_iff.2 ⟨p.1, p.2, rfl⟩⟩
  have hsub : {γ : GlobalTheory.UnitaryBC.latticeGL E a | (infGL E a y)⁻¹ * (γ : GA E a) * infGL E a y ∈ W} ⊆
      f '' (S ×ˢ Set.Icc (-(n₀ : ℤ)) n₀) := by
    rintro ⟨γ, hγ⟩ hγW
    obtain ⟨δ, n, rfl⟩ := GlobalTheory.CuspRep.CuspidalL2GL.mem_latticeGL_iff.1 hγ
    change (infGL E a y)⁻¹ * (ratGL E a δ * e ^ n) * infGL E a y ∈ W at hγW
    have hn : |n| ≤ n₀ := hn₀ δ n _ hγW
    have hn' : n ∈ Set.Icc (-(n₀ : ℤ)) n₀ := abs_le.1 hn
    set w := (infGL E a y)⁻¹ * ratGL E a δ * infGL E a y with hw
    have hcomm : Commute (e ^ n) (infGL E a y) :=
      (Commute.zpow_left (GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm 1 (infGL E a y)) n)
    have hwW : w ∈ W' := by
      refine Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_Icc.2 hn')) ⟨_, hγW, ?_⟩
      change (infGL E a y)⁻¹ * (ratGL E a δ * e ^ n) * infGL E a y * (e ^ n)⁻¹ = w
      simp only [mul_assoc]
      rw [← mul_assoc (e ^ n) (infGL E a y), hcomm.eq, mul_inv_cancel_right]
      all_goals simp only [hw, mul_assoc]
    have hδ : ratGL E a δ = infGL E a y * w * (infGL E a y)⁻¹ := by rw [hw]; group
    refine ⟨(δ, n), ⟨⟨?_, ?_⟩, hn'⟩, rfl⟩
    · have e1 : Matrix.GeneralLinearGroup.map (pInf E) (ratGL E a δ) =
          y * Matrix.GeneralLinearGroup.map (pInf E) w * y⁻¹ := by
        rw [hδ, map_mul, map_mul, map_inv, pInf_infGL]
      rw [e1, Units.val_mul, Units.val_mul]
      have hw' := hBb w hwW
      have p1 := GlobalTheory.AutGrowth.norm_toL_mul_le (y.val * (Matrix.GeneralLinearGroup.map (pInf E) w).val) (y⁻¹).val
      have p2 := GlobalTheory.AutGrowth.norm_toL_mul_le y.val (Matrix.GeneralLinearGroup.map (pInf E) w).val
      have hy1 : ‖toL y.val‖ ≤ height y := by
        unfold height; linarith [norm_nonneg (toL (y⁻¹).val)]
      have hy2 : ‖toL (y⁻¹).val‖ ≤ height y := by
        unfold height; linarith [norm_nonneg (toL y.val)]
      have n1 := norm_nonneg (toL y.val)
      have n2 := norm_nonneg (toL (y⁻¹).val)
      have n3 := norm_nonneg (toL (Matrix.GeneralLinearGroup.map (pInf E) w).val)
      have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
      have q1 : ‖toL (y.val * (Matrix.GeneralLinearGroup.map (pInf E) w).val)‖ ≤ a * (height y * B) :=
        p2.trans (mul_le_mul_of_nonneg_left (mul_le_mul hy1 hw' n3 (by linarith)) ha0)
      have q2 : ‖toL (y.val * (Matrix.GeneralLinearGroup.map (pInf E) w).val * (y⁻¹).val)‖ ≤
          a * ((a * (height y * B)) * height y) :=
        p1.trans (mul_le_mul_of_nonneg_left (mul_le_mul q1 hy2 n2 (by positivity)) ha0)
      refine q2.trans ?_
      rw [hT, hc]
      have : 0 ≤ height y ^ 2 := by positivity
      nlinarith
    · have e2 : Matrix.GeneralLinearGroup.map (pFin E) (ratGL E a δ) =
          Matrix.GeneralLinearGroup.map (pFin E) w := by
        rw [hδ, map_mul, map_mul, map_inv, pFin_infGL, inv_one, one_mul, mul_one]
      rw [e2]
      exact ⟨w, hwW, rfl⟩
  have hfin2 : (f '' (S ×ˢ Set.Icc (-(n₀ : ℤ)) n₀)).Finite := (hfin.prod (Set.finite_Icc _ _)).image f
  refine ⟨hfin2.subset hsub, ?_⟩
  have k1 := Set.ncard_le_ncard hsub hfin2
  have k2 := Set.ncard_image_le (f := f) (hfin.prod (Set.finite_Icc (-(n₀ : ℤ)) n₀))
  rw [Set.ncard_prod] at k2
  have k3 : (({γ : GlobalTheory.UnitaryBC.latticeGL E a | (infGL E a y)⁻¹ * (γ : GA E a) * infGL E a y ∈ W}.ncard : ℕ) : ℝ) ≤
      (S.ncard : ℝ) * N := by rw [hN]; exact_mod_cast k1.trans k2
  refine k3.trans ?_
  have hN0 : 0 ≤ N := by positivity
  calc (S.ncard : ℝ) * N ≤ C₁ * T ^ m * N := mul_le_mul_of_nonneg_right hcard hN0
    _ = C₁ * c ^ m * N * height y ^ (2 * m) := by rw [hT, mul_pow, ← pow_mul, mul_comm 2 m]; ring

end GlobalTheory
