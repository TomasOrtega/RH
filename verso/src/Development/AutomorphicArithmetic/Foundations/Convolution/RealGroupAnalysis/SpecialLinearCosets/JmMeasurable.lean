import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.GoodU
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.CompCoordMem
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

section SlopeTestRemainingChoices

variable {F : Type} [Field F] [NumberField F] {v : P F}

private noncomputable def Jm (c : Fin 2 → Kv v) : Fin 2 → Kv v := ![-c 1, c 0]

/- English proof (translation)
Apply the tactic sequence `funext i; fin_cases i <;> simp [Jm]`.
-/
private lemma Jm_Jm (c : Fin 2 → Kv v) : Jm (Jm c) = -c := by
  funext i; fin_cases i <;> simp [Jm]

/- English proof (translation)
Use `measurable_pi_iff.mpr fun i => ?_` and prove the remaining obligations. Use `fin_cases i`. Establish `h : Measurable fun c : Fin 2 → Kv v => -c 1` using `measurable_neg.comp (measurable_pi_apply (1 : Fin 2))`. Simplify `h` using `[Jm]`. Simplify `measurable_pi_apply (0 : Fin 2)` using `[Jm]`.
-/
private lemma Jm_measurable : Measurable (Jm (v := v)) := by
  refine measurable_pi_iff.mpr fun i => ?_
  fin_cases i
  · have h : Measurable fun c : Fin 2 → Kv v => -c 1 := measurable_neg.comp (measurable_pi_apply (1 : Fin 2))
    simpa [Jm] using h
  · simpa [Jm] using measurable_pi_apply (0 : Fin 2)

private noncomputable def JmE : (Fin 2 → Kv v) ≃ᵐ (Fin 2 → Kv v) where
  toFun := Jm
  invFun := fun c => -Jm c
  left_inv := fun c => by
    show -Jm (Jm c) = c
    rw [Jm_Jm, neg_neg]
  right_inv := fun c => by
    show Jm (-Jm c) = c
    funext i; fin_cases i <;> simp [Jm]
  measurable_toFun := Jm_measurable
  measurable_invFun := measurable_neg.comp Jm_measurable

/- English proof (translation)
Establish `hs` using `measurePreserving_piCongrLeft (α := fun _ : Fin 2 => Kv v) (fun _ => GroundTheory.LocalField.selfDualMeasure (localAdelicChar F v)) (Equiv.swap (0 : Fin 2) 1)`. Establish `hn` using `measurePreserving_pi (fun _ : Fin 2 => GroundTheory.LocalField.selfDualMeasure (localAdelicChar F v)) (fun _ : Fin 2 => GroundTheory.LocalField.selfDualMeasure (localAdelicChar F v)) (f := fun (i : Fin 2) (x : Kv v) => if i = 0 then -x else x) (by`. Introduce `i`. Use `fin_cases i`. Simplify using `using Measure.measurePreserving_neg _`.

Use `MeasurePreserving.id (GroundTheory.LocalField.selfDualMeasure (localAdelicChar F v)) using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x`. Use the proof step `simp)`. Establish `h` using `hn.comp hs`. Establish `hf : Jm (v` using `v) = (fun (a : Fin 2 → Kv v) (i : Fin 2) => if i = 0 then -a i else a i) ∘ (MeasurableEquiv.piCongrLeft (fun _ : Fin 2 => Kv v) (Equiv.swap (0 : Fin 2) 1)) := by`.

Use function extensionality and compare the values at `c i`. Apply the tactic sequence `fin_cases i <;> simp [Jm, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply]`. Rewrite using `[hf]`. Conclude with `h`.
-/
private lemma Jm_mp : MeasurePreserving (Jm (v := v)) (μ2 v) (μ2 v) := by
  have hs := measurePreserving_piCongrLeft (α := fun _ : Fin 2 => Kv v)
    (fun _ => GroundTheory.LocalField.selfDualMeasure (localAdelicChar F v)) (Equiv.swap (0 : Fin 2) 1)
  have hn := measurePreserving_pi (fun _ : Fin 2 => GroundTheory.LocalField.selfDualMeasure (localAdelicChar F v))
    (fun _ : Fin 2 => GroundTheory.LocalField.selfDualMeasure (localAdelicChar F v))
    (f := fun (i : Fin 2) (x : Kv v) => if i = 0 then -x else x) (by
      intro i
      fin_cases i
      · simpa using Measure.measurePreserving_neg _
      · convert MeasurePreserving.id (GroundTheory.LocalField.selfDualMeasure (localAdelicChar F v)) using 1
        funext x
        simp)
  have h := hn.comp hs
  have hf : Jm (v := v) = (fun (a : Fin 2 → Kv v) (i : Fin 2) => if i = 0 then -a i else a i) ∘
      (MeasurableEquiv.piCongrLeft (fun _ : Fin 2 => Kv v) (Equiv.swap (0 : Fin 2) 1)) := by
    funext c i
    fin_cases i <;> simp [Jm, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply]
  rw [hf]
  exact h

/- English proof (translation)
Apply the tactic sequence `funext i; fin_cases i <;> simp [cols]`.
-/
private lemma cols_col (c c' : Fin 2 → Kv v) : (fun i => cols c c' i 1) = c' := by
  funext i; fin_cases i <;> simp [cols]

/- English proof (translation)
Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;> simp [sw, cols]`.
-/
private lemma sw_cols (p q : Fin 2 → Kv v) : sw (cols p q) = cols q p := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [sw, cols]

/- English proof (translation)
Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;> simp [sw]`.
-/
private lemma sw_sw (m : M2 v) : sw (sw m) = m := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [sw]

/- English proof (translation)
Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;> simp [cols]`.
-/
private lemma eq_cols (m : M2 v) : m = cols (fun i => m i 0) (fun i => m i 1) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cols]

/- English proof (translation)
Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [sw] <;> fun_prop`.
-/
private lemma sw_continuous : Continuous (sw (v := v)) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [sw] <;> fun_prop

private noncomputable def swH : M2 v ≃ₜ M2 v where
  toFun := sw
  invFun := sw
  left_inv := sw_sw
  right_inv := sw_sw
  continuous_toFun := sw_continuous
  continuous_invFun := sw_continuous

/- English proof (translation)
Assemble the required witnesses or components as `⟨ha.1.comp_continuous sw_continuous, ha.2.comp_homeomorph swH⟩`.
-/
private lemma comp_sw_mem {a : M2 v → ℂ} (ha : a ∈ SB (M2 v)) : (fun X => a (sw X)) ∈ SB (M2 v) :=
  ⟨ha.1.comp_continuous sw_continuous, ha.2.comp_homeomorph swH⟩

/- English proof (translation)
Establish `hc : Continuous fun c' : Fin 2 → Kv v => cols c c'`. Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [cols] <;> fun_prop`. Establish `hr : Continuous fun X : M2 v => (fun i => X i 1 : Fin 2 → Kv v)`. Use `continuous_pi fun i => ?_` and prove the remaining obligations.

Conclude with `(continuous_id.matrix_elem i 1)`. Establish `he : IsClosedEmbedding fun c' : Fin 2 → Kv v => cols c c'` using `Function.LeftInverse.isClosedEmbedding (f := fun X : M2 v => (fun i => X i 1 : Fin 2 → Kv v)) (fun c' => cols_col c c') hr hc`. Conclude with `⟨ha.1.comp_continuous hc, ha.2.comp_isClosedEmbedding he⟩`.
-/
private lemma slice_mem {a : M2 v → ℂ} (ha : a ∈ SB (M2 v)) (c : Fin 2 → Kv v) :
    (fun c' => a (cols c c')) ∈ localSchwartzBruhatPi (Kv v) (ι := Fin 2) := by
  have hc : Continuous fun c' : Fin 2 → Kv v => cols c c' := by
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [cols] <;> fun_prop
  have hr : Continuous fun X : M2 v => (fun i => X i 1 : Fin 2 → Kv v) := by
    refine continuous_pi fun i => ?_
    exact (continuous_id.matrix_elem i 1)
  have he : IsClosedEmbedding fun c' : Fin 2 → Kv v => cols c c' :=
    Function.LeftInverse.isClosedEmbedding (f := fun X : M2 v => (fun i => X i 1 : Fin 2 → Kv v))
      (fun c' => cols_col c c') hr hc
  exact ⟨ha.1.comp_continuous hc, ha.2.comp_isClosedEmbedding he⟩

/- English proof (translation)
Simplify using `only [Pt, localFourierPi, cols_col]`. Unfold `μ2`. Use `integral_congr_ae (Eventually.of_forall fun c' => ?_)` and prove the remaining obligations. Establish `h : c₁ 0 * c' 1 - c₁ 1 * c' 0 = ∑ i, c' i * Jm c₁ i`. Simplify using `[Jm, Fin.sum_univ_two]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [ψl]`. Rewrite using `[← h]`. Simplify using `[cols]`.
-/
private lemma Pt_cols (a : M2 v → ℂ) (c₁ c : Fin 2 → Kv v) :
    Pt a (cols c₁ c) = localFourierPi (localAdelicChar F v) (fun c' => a (cols c c')) (Jm c₁) := by
  simp only [Pt, localFourierPi, cols_col]
  unfold μ2
  refine integral_congr_ae (Eventually.of_forall fun c' => ?_)
  have h : c₁ 0 * c' 1 - c₁ 1 * c' 0 = ∑ i, c' i * Jm c₁ i := by
    simp [Jm, Fin.sum_univ_two]; ring
  simp only [ψl]
  rw [← h]
  simp [cols]

/- English proof (translation)
Establish `h` using `(Jm_mp (v := v)).integral_comp (JmE (v := v)).measurableEmbedding (fun y => G y * ((localAdelicChar F v (∑ i, y i * (-q) i) : Circle) : ℂ))`. Express the relevant statement in the definitionally equal form `∫ x, G (Jm x) * ((localAdelicChar F v (∑ i, x i * Jm q i) : Circle) : ℂ) ∂(μ2 v) = ∫ y, G y * ((localAdelicChar F v (∑ i, y i * (-q) i) : Circle) : ℂ) ∂(μ2 v)`. Rewrite using `[← h]`. Use `integral_congr_ae (Eventually.of_forall fun c => ?_)` and prove the remaining obligations. Establish `: ∑ i, c i * Jm q i = ∑ i, Jm c i * (-q) i`.

Simplify using `[Jm, Fin.sum_univ_two]`. Simplify using `only [this]`.
-/
private lemma fourier_rot (G : (Fin 2 → Kv v) → ℂ) (q : Fin 2 → Kv v) :
    localFourierPi (localAdelicChar F v) (fun c => G (Jm c)) (Jm q) =
      localFourierPi (localAdelicChar F v) G (-q) := by
  have h := (Jm_mp (v := v)).integral_comp (JmE (v := v)).measurableEmbedding
    (fun y => G y * ((localAdelicChar F v (∑ i, y i * (-q) i) : Circle) : ℂ))
  change ∫ x, G (Jm x) * ((localAdelicChar F v (∑ i, x i * Jm q i) : Circle) : ℂ) ∂(μ2 v) =
    ∫ y, G y * ((localAdelicChar F v (∑ i, y i * (-q) i) : Circle) : ℂ) ∂(μ2 v)
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun c => ?_)
  have : ∑ i, c i * Jm q i = ∑ i, Jm c i * (-q) i := by
    simp [Jm, Fin.sum_univ_two]
  simp only [this]

/- English proof (translation)
Establish `hc` using `continuous_localAdelicChar (K := F) v`. Establish `hn : localAdelicChar F v ≠ 1` using `localAdelicChar_ne_one v`. Establish `hb` using `slice_mem ha p`. Establish `hG` using `localFourierPi_mem hc hn hb`. Rewrite using `[Pt_cols]`.

Establish `h1 : (fun c' => Pt a (sw (cols p c'))) = fun c' => localFourierPi (localAdelicChar F v) (fun c'' => a (cols p c'')) (Jm c')`. Use function extensionality and compare the values at `c'`. Rewrite using `[sw_cols, Pt_cols]`. Rewrite using `[h1, fourier_rot, localFourierPi_localFourierPi hc hn hb]`. Simplify using the standard rewrite rules.
-/
private lemma part1 {a : M2 v → ℂ} (ha : a ∈ SB (M2 v)) (p q : Fin 2 → Kv v) :
    Pt (fun X => Pt a (sw X)) (cols q p) = a (cols p q) := by
  have hc := continuous_localAdelicChar (K := F) v
  have hn : localAdelicChar F v ≠ 1 := localAdelicChar_ne_one v
  have hb := slice_mem ha p
  have hG := localFourierPi_mem hc hn hb
  rw [Pt_cols]
  have h1 : (fun c' => Pt a (sw (cols p c'))) =
      fun c' => localFourierPi (localAdelicChar F v) (fun c'' => a (cols p c'')) (Jm c') := by
    funext c'
    rw [sw_cols, Pt_cols]
  rw [h1, fourier_rot, localFourierPi_localFourierPi hc hn hb]
  simp

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `F _ _ v a ha`. Establish `h1 : ∀ b ∈ SB (M2 v), ∀ m, Pt (fun X => Pt b (sw X)) (sw m) = b m`. Introduce `b hb m`. Rewrite using `[eq_cols m, sw_cols]`. Conclude with `part1 hb _ _`.

Use `⟨h1 a ha, ?_⟩` and prove the remaining obligations. Take `⟨T, hT⟩` from `UpperTheory.ConvolutionTheory.R2.I.ptMem F v`. Establish `hb` using `comp_sw_mem ha`. Establish `hTb : Pt (fun X => a (sw X)) ∈ SB (M2 v)`. Use `(T ⟨_, hb⟩).2` as an intermediate fact.

Rewrite `this` using `[hT]`. Then use the resulting hypothesis. Use `⟨fun X => Pt (fun Y => a (sw Y)) (sw X), comp_sw_mem hTb, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `m`. Use `h1 _ hb (sw m)` as an intermediate fact. Rewrite `this` using `[sw_sw]`.

Simplify `this` using `[sw_sw]`.
-/
theorem UpperTheory.ConvolutionTheory.R2.I.ptInv :
    ∀ (F : Type) [Field F] [NumberField F] (v : P F), ∀ a ∈ SB (M2 v), (∀ m, Pt (fun X => Pt a (sw X)) (sw m) = a m) ∧ ∃ a' ∈ SB (M2 v), Pt a' = a := by
  intro F _ _ v a ha
  have h1 : ∀ b ∈ SB (M2 v), ∀ m, Pt (fun X => Pt b (sw X)) (sw m) = b m := by
    intro b hb m
    rw [eq_cols m, sw_cols]
    exact part1 hb _ _
  refine ⟨h1 a ha, ?_⟩
  obtain ⟨T, hT⟩ := UpperTheory.ConvolutionTheory.R2.I.ptMem F v
  have hb := comp_sw_mem ha
  have hTb : Pt (fun X => a (sw X)) ∈ SB (M2 v) := by
    have := (T ⟨_, hb⟩).2
    rwa [hT] at this
  refine ⟨fun X => Pt (fun Y => a (sw Y)) (sw X), comp_sw_mem hTb, ?_⟩
  funext m
  have := h1 _ hb (sw m)
  rw [sw_sw] at this
  simpa [sw_sw] using this
