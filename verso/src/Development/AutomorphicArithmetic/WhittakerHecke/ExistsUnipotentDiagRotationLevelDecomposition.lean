import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.FacDefs
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem kgl_of {v : H.P ℚ} (y : GL (Fin 2) (H.Kv v)) (h1 : ∀ i j, y.val i j ∈ Formalism.UG.Ov ℚ v)
    (h2 : ∀ i j, (y⁻¹).val i j ∈ Formalism.UG.Ov ℚ v) : y ∈ GlobalTheory.LFun.KGL v 2 := by
  rw [GlobalTheory.LFun.KGL, Formalism.UG.GLint, MonoidHom.mem_range]
  let M : Matrix (Fin 2) (Fin 2) (Formalism.UG.Ov ℚ v) := Matrix.of fun i j => ⟨_, h1 i j⟩
  let N : Matrix (Fin 2) (Fin 2) (Formalism.UG.Ov ℚ v) := Matrix.of fun i j => ⟨_, h2 i j⟩
  have hM : M.map (Formalism.UG.Ov ℚ v).subtype = y.val := by ext i j; rfl
  have hN : N.map (Formalism.UG.Ov ℚ v).subtype = (y⁻¹).val := by ext i j; rfl
  have inj : Function.Injective (fun A : Matrix (Fin 2) (Fin 2) (Formalism.UG.Ov ℚ v) => A.map (Formalism.UG.Ov ℚ v).subtype) :=
    Matrix.map_injective Subtype.val_injective
  refine ⟨⟨M, N, inj ?_, inj ?_⟩, Units.ext ?_⟩
  · simp only
    rw [Matrix.map_mul, hM, hN, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  · simp only
    rw [Matrix.map_mul, hM, hN, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  · exact hM

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.
-/
private theorem cp_rot (v : H.P ℚ) (t : ℝ) : Matrix.GeneralLinearGroup.map (H.cp v) (rot t) = 1 := by
  have h : Matrix.GeneralLinearGroup.map (pFin ℚ) (rot t) = 1 := TR.pFin_infGL _
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h2 := congrArg (fun x : GL (Fin 2) (Af ℚ) => pLoc ℚ v (x.val i j)) h
  change H.cp v ((rot t).val i j) = _ at h2
  change H.cp v ((rot t).val i j) = _
  rw [h2]
  fin_cases i <;> fin_cases j <;> simp

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition.

Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem lev_of (N : ℕ) (t : ℝ) (k : G1 ℚ)
    (hr : Matrix.GeneralLinearGroup.map (TR.pInf ℚ) (gl k) = Matrix.GeneralLinearGroup.map (TR.pInf ℚ) (rot t))
    (hi : ∀ v i j, Valued.v (H.cp v (k i j)) ≤ 1)
    (hd : ∀ v i j, Dv N v (k i j - (1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j)) : Lev N ((rot t)⁻¹ * gl k) := by
  have e : ∀ v, Matrix.GeneralLinearGroup.map (H.cp v) ((rot t)⁻¹ * gl k) = Matrix.GeneralLinearGroup.map (H.cp v) (gl k) := by
    intro v
    rw [map_mul, map_inv, cp_rot, inv_one, one_mul]
  refine ⟨fun i j => ?_, fun v => ⟨?_, fun i j => ?_⟩⟩
  · have h : Matrix.GeneralLinearGroup.map (TR.pInf ℚ) ((rot t)⁻¹ * gl k) = Matrix.GeneralLinearGroup.map (TR.pInf ℚ) 1 := by
      rw [map_mul, map_inv, hr, inv_mul_cancel, map_one]
    exact (TR.infEq ℚ).symm.injective (congrArg (fun x : GL (Fin 2) (TR.Rinf ℚ) => x.val i j) h)
  · unfold H.KAt
    rw [e]
    refine kgl_of _ (fun i j => hi v i j) fun i j => ?_
    rw [← map_inv, ← map_inv]
    change Valued.v (H.cp v ((k⁻¹ : G1 ℚ) i j)) ≤ 1
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
    fin_cases i <;> fin_cases j <;> simp [hi]
  · have h := congrArg (fun x : GL (Fin 2) (H.Kv v) => x.val i j) (e v)
    change H.cp v (((rot t)⁻¹ * gl k).val i j) = H.cp v (k i j) at h
    have h2 := hd v i j
    unfold Dv at h2 ⊢
    rw [map_sub] at h2 ⊢
    rw [h]; exact h2

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
private theorem pinf_re (x : A ℚ) : TR.pInf ℚ x = fun _ => re x := by
  funext w
  rw [Subsingleton.elim w Rat.infinitePlace]; rfl

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Prove the components needed by the constructor for the conclusion.

Take a linear combination of the given relations to obtain the conclusion. Take a linear combination of the given relations to obtain the conclusion.
-/
private theorem real_rot (k : G1 ℚ) (hk : InfOrth k) (t : ℝ) (hs : re (k 1 0) = Real.sin t) (hc : re (k 1 1) = Real.cos t) :
    re (k 0 0) = Real.cos t ∧ re (k 0 1) = -Real.sin t := by
  let φ : A ℚ →+* ℝ := (Pi.evalRingHom (fun _ : InfinitePlace ℚ => ℝ) Rat.infinitePlace).comp (TR.pInf ℚ)
  have hφ : ∀ x, re x = φ x := fun _ => rfl
  have h1 : φ ((k.1 * k.1ᵀ) 0 1) = φ ((1 : Matrix (Fin 2) (Fin 2) (A ℚ)) 0 1) :=
    congrArg (fun x => (TR.infEq ℚ).symm x Rat.infinitePlace) (hk 0 1)
  have h2 := congrArg φ k.det_coe
  rw [Matrix.det_fin_two] at h2
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, map_add, map_mul, map_sub, map_one,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide), map_zero] at h1 h2
  simp only [hφ] at hs hc ⊢
  rw [hs, hc] at h1 h2
  have h3 := Real.sin_sq_add_cos_sq t
  constructor
  · linear_combination (Real.sin t) * h1 + (Real.cos t) * h2 - φ (k 0 0) * h3
  · linear_combination (Real.cos t) * h1 - (Real.sin t) * h2 - φ (k 0 1) * h3

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.

A detailed English derivation is pending.
-/
private theorem rot_of (k : G1 ℚ) (t : ℝ) (h0 : re (k 0 0) = Real.cos t) (h1 : re (k 0 1) = -Real.sin t)
    (hs : re (k 1 0) = Real.sin t) (hc : re (k 1 1) = Real.cos t) :
    Matrix.GeneralLinearGroup.map (TR.pInf ℚ) (gl k) = Matrix.GeneralLinearGroup.map (TR.pInf ℚ) (rot t) := by
  rw [rot, TR.pInf_infGL]
  refine Units.ext (Matrix.ext fun i j => ?_)
  change TR.pInf ℚ (k i j) = _
  rw [pinf_re]
  fin_cases i <;> fin_cases j
  · exact congrArg (fun x _ => x) h0
  · exact congrArg (fun x _ => x) h1
  · exact congrArg (fun x _ => x) hs
  · exact congrArg (fun x _ => x) hc

/- English proof (translation)
Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Rewrite the hypotheses and the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Simplify to obtain the desired conclusion from the available facts.

Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the hypotheses and the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts. Simplify to obtain the desired conclusion from the available facts.

A detailed English derivation is pending.
-/
private theorem loc {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] (w : Valuation K Γ) (a b c d n : K)
    (ha : w a ≤ 1) (hb : w b ≤ 1) (hc : w c ≤ w n) (hd : w d ≤ 1) (hn : w n ≤ 1) (h : a * d - b * c = 1) :
    ∃ z z' β : K, z * z' = 1 ∧ w z = 1 ∧ w z' = 1 ∧ w β ≤ 1 ∧ w (z' * (a - β * c) - 1) ≤ w n ∧
      w (z' * (b - β * d)) ≤ w n ∧ w (z * c) ≤ w n ∧ w (z * d - 1) ≤ w n := by
  rcases hn.lt_or_eq with hn' | hn'
  · have hbc : w (b * c) ≤ w n := by
      rw [map_mul]; exact (mul_le_of_le_one_left' hb).trans hc
    have had : w a * w d = 1 := by
      rw [← map_mul, show a * d = 1 + b * c by linear_combination h]
      exact w.map_one_add_of_lt (hbc.trans_lt hn')
    have ha1 : w a = 1 := le_antisymm ha (had ▸ mul_le_of_le_one_right' hd)
    have hd1 : w d = 1 := by rwa [ha1, one_mul] at had
    have a0 : a ≠ 0 := by rintro rfl; simp at ha1
    have d0 : d ≠ 0 := by rintro rfl; simp at hd1
    refine ⟨a, a⁻¹, b / d, mul_inv_cancel₀ a0, ha1, by simp [ha1], by simpa [hd1] using hb, ?_, ?_, ?_, ?_⟩
    · rw [show a⁻¹ * (a - b / d * c) - 1 = -(b * c) / (a * d) by field_simp; ring]
      simpa [ha1, hd1] using hbc
    · rw [div_mul_cancel₀ _ d0]; simp
    · simpa [ha1] using hc
    · rw [show a * d - 1 = b * c by linear_combination h]; exact hbc
  · rw [hn'] at hc ⊢
    refine ⟨1, 1, 0, one_mul _, map_one _, map_one _, by simp, ?_, by simpa using hb, by simpa using hc, ?_⟩
    · simpa using w.map_sub_le ha (map_one w).le
    · simpa using w.map_sub_le hd (map_one w).le

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Introduce a local definition for the expression. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Introduce a local definition for the expression. Introduce a local definition for the expression. Rewrite the conclusion using the stated equalities. Take a linear combination of the given relations to obtain the conclusion.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Apply the first step, then apply the next step to every resulting obligation. Simplify to obtain the desired conclusion from the available facts.

Simplify to obtain the desired conclusion from the available facts. Simplify to obtain the desired conclusion from the available facts. Simplify to obtain the desired conclusion from the available facts. Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts.

Simplify to obtain the desired conclusion from the available facts. Simplify to obtain the desired conclusion from the available facts. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Apply the first step, then apply the next step to every resulting obligation. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Reduce the conclusion to the remaining proof obligations.

Express the relevant assertion in an equivalent form by its definition. Apply the first step, then apply the next step to every resulting obligation. Take a linear combination of the given relations to obtain the conclusion. Take a linear combination of the given relations to obtain the conclusion. Take a linear combination of the given relations to obtain the conclusion.

Take a linear combination of the given relations to obtain the conclusion. A detailed English derivation is pending.
-/
theorem UpperTheory.exists_unipotent_diag_rotation_level_decomposition :
    ∀ (N : ℕ), 0 < N → ∀ k ∈ KK ℚ, k ∈ SS N → ∀ t : ℝ, re (k 1 0) = Real.sin t → re (k 1 1) = Real.cos t →
        ∃ (b : A ℚ) (ζ : (A ℚ)ˣ) (κ : GL (Fin 2) (A ℚ)), ζ ∈ UU ∧ Lev N κ ∧ gl k = gl (nU b) * gl (mD ζ) * rot t * κ := by
  intro N _ k hk hS t hs hc
  obtain ⟨h0, h1⟩ := real_rot k hk.1 t hs hc
  have hdet := k.det_coe
  rw [Matrix.det_fin_two] at hdet
  have hint : ∀ v i j, Valued.v (H.cp v (k i j)) ≤ 1 := fun v i j => hk.2 v i j
  have hN : ∀ v : H.P ℚ, Valued.v (N : H.Kv v) ≤ 1 := fun v => natCast_mem (v.adicCompletionIntegers ℚ) N
  choose z z' β hzz hz hz' hβ e00 e01 e10 e11 using fun v : H.P ℚ =>
    loc (Valued.v (R := H.Kv v)) (H.cp v (k 0 0)) (H.cp v (k 0 1)) (H.cp v (k 1 0)) (H.cp v (k 1 1)) (N : H.Kv v)
      (hint v 0 0) (hint v 0 1) (hS v) (hint v 1 1) (hN v)
      (by rw [← map_mul, ← map_mul, ← map_sub, hdet, map_one])
  let Z : A ℚ := ((1, ⟨z, Eventually.of_forall fun v => (hz v).le⟩) : InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ)
  let Z' : A ℚ := ((1, ⟨z', Eventually.of_forall fun v => (hz' v).le⟩) : InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ)
  let B : A ℚ := ((0, ⟨β, Eventually.of_forall fun v => hβ v⟩) : InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ)
  have hZ : ∀ v, H.cp v Z = z v := fun _ => rfl
  have hZ' : ∀ v, H.cp v Z' = z' v := fun _ => rfl
  have hB : ∀ v, H.cp v B = β v := fun _ => rfl
  have hZZ : Z * Z' = 1 := Prod.ext (mul_one _) (FiniteAdeleRing.ext _ fun v => hzz v)
  have rZ : TR.pInf ℚ Z = 1 := map_one (TR.infEq ℚ).symm
  have rZ' : TR.pInf ℚ Z' = 1 := map_one (TR.infEq ℚ).symm
  have rB : TR.pInf ℚ B = 0 := map_zero (TR.infEq ℚ).symm
  let ζ : (A ℚ)ˣ := ⟨Z, Z', hZZ, (mul_comm _ _).trans hZZ⟩
  let k' : G1 ℚ := ⟨!![Z' * (k 0 0 - B * k 1 0), Z' * (k 0 1 - B * k 1 1); Z * k 1 0, Z * k 1 1], by
    rw [Matrix.det_fin_two_of]
    linear_combination (k 0 0 * k 1 1 - k 0 1 * k 1 0) * hZZ + hdet⟩
  have hd : ∀ v i j, Dv N v (k' i j - (1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j) := by
    intro v i j
    unfold Dv
    fin_cases i <;> fin_cases j
    · simpa [k', hZ, hZ', hB] using e00 v
    · simpa [k', hZ, hZ', hB] using e01 v
    · simpa [k', hZ, hZ', hB] using e10 v
    · simpa [k', hZ, hZ', hB] using e11 v
  refine ⟨B, ζ, (rot t)⁻¹ * gl k', ⟨rfl, fun v => hz v⟩, lev_of N t k' (rot_of k' t ?_ ?_ ?_ ?_) (fun v i j => ?_) hd, ?_⟩
  · simpa [k', re, rZ, rZ', rB] using h0
  · simpa [k', re, rZ, rZ', rB] using h1
  · simpa [k', re, rZ, rZ', rB] using hs
  · simpa [k', re, rZ, rZ', rB] using hc
  · have h := (hd v i j).trans (hN v)
    rw [← sub_add_cancel (k' i j) ((1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j), map_add]
    refine Valuation.map_add_le _ h ?_
    fin_cases i <;> fin_cases j <;> simp
  · rw [mul_assoc, mul_inv_cancel_left, ← map_mul, ← map_mul]
    congr 1
    refine Subtype.ext (Matrix.ext fun i j => ?_)
    change _ = (!![1, B; 0, 1] * !![Z, 0; 0, Z'] *
      !![Z' * (k 0 0 - B * k 1 0), Z' * (k 0 1 - B * k 1 1); Z * k 1 0, Z * k 1 1] : Matrix (Fin 2) (Fin 2) (A ℚ)) i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination (-k 0 0) * hZZ
    · linear_combination (-k 0 1) * hZZ
    · linear_combination (-k 1 0) * hZZ
    · linear_combination (-k 1 1) * hZZ
