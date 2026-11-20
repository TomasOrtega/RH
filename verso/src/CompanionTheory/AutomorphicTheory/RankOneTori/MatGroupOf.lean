import CompanionTheory.AutomorphicTheory.RankOneTori.RpowNegLe
import Formalism.SharpRestriction.CuspSpanNormBounds.BigCellDensity
import Formalism.SharpRestriction.CuspSpanNormBounds.SpanMemOfImage
import Formalism.FormalDegreeBessel.FinalG
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.RStabInv

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.Pv.AmpDDPf Formalism.MainNotions.S.Pv.AmpDDPf.CC Formalism.FourierDecayAlt
open scoped ENNReal

noncomputable section

namespace Formalism.MainStatements.RankOne

variable {k r : ℕ}

def Cell (L : LocBessel k r) (a : ℝ) (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR : Measure (Mt k r)) (ν : Measure (PairSp k r)) : Prop :=
  γ ∈ UH (Hpk k r) ∧ IsRelStab L γ ∧ IsHaarOn (RStab k r γ) μR ∧ IsOrbQuot L γ μR ν ∧
    MeasurePreserving (P.B7.invM (k := k) (r := r)) μR μR ∧
    ∃ b : ℝ, 0 ≤ b ∧ ThreeDimData.AG k r + 1 < a - b ∧ Integrable (Pv.AmpDD.pairMaj γ b) ν

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.closed, h.one_mem, h.mul_mem, fun a ha => ⟨h.inv_mem a ha, Matrix.mul_nonsing_inv a (h.unit a ha)⟩⟩`.
-/
theorem matGroup_of {U : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)} (h : B2.IsClosedSubgroup U) : PI.IsMatGroup U :=
  ⟨h.closed, h.one_mem, h.mul_mem, fun a ha => ⟨h.inv_mem a ha, Matrix.mul_nonsing_inv a (h.unit a ha)⟩⟩

def lr (a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (x : Mt k r) : Mt k r := fun i j => (a * Matrix.of x * b) i j

/- English proof (translation)
Use `show Continuous fun x : Mt k r => (a * (Matrix.of x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) * b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)`. Conclude with `(continuous_const.matrix_mul PI.WUN.continuous_of).matrix_mul continuous_const`.
-/
theorem lr_cont (a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Continuous (lr (k := k) (r := r) a b) := by
  show Continuous fun x : Mt k r => (a * (Matrix.of x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) * b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
  exact (continuous_const.matrix_mul PI.WUN.continuous_of).matrix_mul continuous_const

/- English proof (translation)
Use function extensionality and compare the values at `i j`. Use `show (γ * (γ⁻¹ * Matrix.of x * γ) * γ⁻¹) i j = x i j`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hγ, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hγ, Matrix.mul_one]`. Both sides reduce to the same expression.
-/
theorem lr_lr {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hγ : IsUnit γ.det) (x : Mt k r) : lr γ γ⁻¹ (lr γ⁻¹ γ x) = x := by
  funext i j
  show (γ * (γ⁻¹ * Matrix.of x * γ) * γ⁻¹) i j = x i j
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hγ, Matrix.one_mul, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ hγ, Matrix.mul_one]
  rfl

/- English proof (translation)
Use function extensionality and compare the values at `i j`. Use `show (γ⁻¹ * (γ * Matrix.of x * γ⁻¹) * γ) i j = x i j`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hγ, Matrix.one_mul, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hγ, Matrix.mul_one]`. Both sides reduce to the same expression.
-/
theorem lr_lr' {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hγ : IsUnit γ.det) (x : Mt k r) : lr γ⁻¹ γ (lr γ γ⁻¹ x) = x := by
  funext i j
  show (γ⁻¹ * (γ * Matrix.of x * γ⁻¹) * γ) i j = x i j
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hγ, Matrix.one_mul, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ hγ, Matrix.mul_one]
  rfl

/- English proof (translation)
Establish `hu` using `uh_isUnit hγ`. Establish `hRg : B2.IsClosedSubgroup (RStab k r γ)` using `P.Dx2.OrbJ.closedR (k := k) (r := r) hu`. Set `e : Mt k r ≃ᵐ Mt k r` to `{ toFun := lr γ⁻¹ γ, invFun := lr γ γ⁻¹, left_inv := lr_lr hu, right_inv := lr_lr' hu measurable_toFun := (lr_cont _ _).measurable, measurable_invFun := (lr_cont _ _).measurable }`. Use `set S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) := {y | γ * y * γ⁻¹ ∈ RStab k r γ} with hS`. Establish `c1 : ∀ y : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, γ⁻¹ * (γ * y * γ⁻¹) * γ = y` using `fun y => lr_lr' hu y`.

Establish `c2 : ∀ y : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, γ * (γ⁻¹ * y * γ) * γ⁻¹ = y` using `fun y => lr_lr hu y`. Establish `hSG : S ⊆ UH (Hpk k r)` using `fun y hy => by`. Establish `: γ⁻¹ * (γ * y * γ⁻¹) * γ ∈ Nset k r` using `hy.2`. Rewrite `this` using `[c1]`. Conclude with `this.1`.

Establish `cm : ∀ a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, γ * (a * b) * γ⁻¹ = (γ * a * γ⁻¹) * (γ * b * γ⁻¹)` using `fun a b => by`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc γ⁻¹ γ, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]`. Establish `hSm : PI.IsMatGroup S`. Use `⟨hRg.closed.preimage (lr_cont γ γ⁻¹), ?_, fun a ha b hb => ?_, fun a ha => ⟨?_, ?_⟩⟩` and prove the remaining obligations.

Use `show γ * 1 * γ⁻¹ ∈ RStab k r γ`. Rewrite using `[Matrix.mul_one, Matrix.mul_nonsing_inv _ hu]`. Conclude with `hRg.one_mem`. Use `show γ * (a * b) * γ⁻¹ ∈ RStab k r γ`. Rewrite using `[cm]`.

Conclude with `hRg.mul_mem _ ha _ hb`. Use `show γ * a⁻¹ * γ⁻¹ ∈ RStab k r γ`. Use `hRg.inv_mem _ ha` as an intermediate fact. Rewrite `this` using `[Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hu, ← Matrix.mul_assoc]`. Then use the resulting hypothesis. Conclude with `Matrix.mul_nonsing_inv a (uh_isUnit (hSG ha))`.

Establish `: SigmaFinite μR` using `hR.1`. Establish `hH : PI.IsHaarOnM S (μR.map e)`. Use `⟨e.sigmaFinite_map, fun h0 => hR.2.1 (e.measurableEmbedding.map_injective (by simpa using h0)), ?_, fun s hs => ?_⟩` and prove the remaining obligations. Rewrite using `[e.map_apply]`. Use `measure_mono_null (t := {x | Matrix.of x ∉ RStab k r γ}) (fun x hx hxR => hx ?_) hR.2.2.1` and prove the remaining obligations.

Use `show γ * (γ⁻¹ * Matrix.of x * γ) * γ⁻¹ ∈ RStab k r γ`. Rewrite using `[c2]`. Conclude with `hxR`. Establish `hm : ∀ t : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, Measurable (lmulM (k` using `k) (r := r) t) := Formalism.MainNotions.FrameBoundFromBesselTorus.measurable_lmulM`. Establish `e1 : (lmulM (k` using `k) (r := r) s) ∘ e = e ∘ lmulM (γ * s * γ⁻¹) := by`.

Use function extensionality and compare the values at `x`. Use `show (s * (γ⁻¹ * Matrix.of x * γ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) = γ⁻¹ * (γ * s * γ⁻¹ * Matrix.of x) * γ`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc γ⁻¹ γ, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]`. Use `show (μR.map e).map (lmulM s) = μR.map e`.

Rewrite using `[Measure.map_map (hm s) e.measurable, e1, ← Measure.map_map e.measurable (hm _), hR.2.2.2 _ hs]`. Conclude with `Formalism.L2.SG.Pf.QuotMeasExists.quotM_exists (matGroup_of (P.unitary_group_closed k r)) hSm hSG hG hH`.
-/
theorem quot_exists {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hγ : γ ∈ UH (Hpk k r)) {μG μR : Measure (Mt k r)} (hG : IsHaarOn (UH (Hpk k r)) μG)
    (hR : IsHaarOn (RStab k r γ) μR) :
    ∃ νR, PI.BesselPeriodGGP.IsQuotMeas μG (μR.map (fun x => fun i j => (γ⁻¹ * Matrix.of x * γ) i j)) νR := by
  have hu := uh_isUnit hγ
  have hRg : B2.IsClosedSubgroup (RStab k r γ) := P.Dx2.OrbJ.closedR (k := k) (r := r) hu
  let e : Mt k r ≃ᵐ Mt k r :=
    { toFun := lr γ⁻¹ γ, invFun := lr γ γ⁻¹, left_inv := lr_lr hu, right_inv := lr_lr' hu
      measurable_toFun := (lr_cont _ _).measurable, measurable_invFun := (lr_cont _ _).measurable }
  set S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) := {y | γ * y * γ⁻¹ ∈ RStab k r γ} with hS
  have c1 : ∀ y : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, γ⁻¹ * (γ * y * γ⁻¹) * γ = y := fun y => lr_lr' hu y
  have c2 : ∀ y : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, γ * (γ⁻¹ * y * γ) * γ⁻¹ = y := fun y => lr_lr hu y
  have hSG : S ⊆ UH (Hpk k r) := fun y hy => by
    have : γ⁻¹ * (γ * y * γ⁻¹) * γ ∈ Nset k r := hy.2
    rw [c1] at this
    exact this.1
  have cm : ∀ a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, γ * (a * b) * γ⁻¹ = (γ * a * γ⁻¹) * (γ * b * γ⁻¹) := fun a b => by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc γ⁻¹ γ, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
  have hSm : PI.IsMatGroup S := by
    refine ⟨hRg.closed.preimage (lr_cont γ γ⁻¹), ?_, fun a ha b hb => ?_, fun a ha => ⟨?_, ?_⟩⟩
    · show γ * 1 * γ⁻¹ ∈ RStab k r γ
      rw [Matrix.mul_one, Matrix.mul_nonsing_inv _ hu]; exact hRg.one_mem
    · show γ * (a * b) * γ⁻¹ ∈ RStab k r γ
      rw [cm]; exact hRg.mul_mem _ ha _ hb
    · show γ * a⁻¹ * γ⁻¹ ∈ RStab k r γ
      have := hRg.inv_mem _ ha
      rwa [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hu, ← Matrix.mul_assoc] at this
    · exact Matrix.mul_nonsing_inv a (uh_isUnit (hSG ha))
  have : SigmaFinite μR := hR.1
  have hH : PI.IsHaarOnM S (μR.map e) := by
    refine ⟨e.sigmaFinite_map, fun h0 => hR.2.1 (e.measurableEmbedding.map_injective (by simpa using h0)), ?_,
      fun s hs => ?_⟩
    · rw [e.map_apply]
      refine measure_mono_null (t := {x | Matrix.of x ∉ RStab k r γ}) (fun x hx hxR => hx ?_) hR.2.2.1
      show γ * (γ⁻¹ * Matrix.of x * γ) * γ⁻¹ ∈ RStab k r γ
      rw [c2]; exact hxR
    · have hm : ∀ t : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, Measurable (lmulM (k := k) (r := r) t) := Formalism.MainNotions.FrameBoundFromBesselTorus.measurable_lmulM
      have e1 : (lmulM (k := k) (r := r) s) ∘ e = e ∘ lmulM (γ * s * γ⁻¹) := by
        funext x
        show (s * (γ⁻¹ * Matrix.of x * γ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) = γ⁻¹ * (γ * s * γ⁻¹ * Matrix.of x) * γ
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc γ⁻¹ γ, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
      show (μR.map e).map (lmulM s) = μR.map e
      rw [Measure.map_map (hm s) e.measurable, e1, ← Measure.map_map e.measurable (hm _), hR.2.2.2 _ hs]
  exact Formalism.L2.SG.Pf.QuotMeasExists.quotM_exists (matGroup_of (P.unitary_group_closed k r)) hSm hSG hG hH

def oneM (k r : ℕ) : Mt k r := fun i j => (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j

/- English proof (translation)
Establish `hR : RStab k r (bigCell k r c μ) = {1}` using `Lem.orbRStabBig k r c μ hc hμ`. Establish `hγ` using `bigCellMem k r c μ hc hμ`. Establish `hu` using `uh_isUnit hγ`. Establish `hAS : 0 ≤ ThreeDimData.AS k r`. Establish `hd : 0 ≤ ThreeDimData.dN k r`.

Unfold `ThreeDimData.dN`. Establish `h0 : (0 : ℝ) ≤ r` using `Nat.cast_nonneg r`. Establish `h1 : (0 : ℝ) ≤ k` using `Nat.cast_nonneg k`. Use the polynomial consequences of the given equalities and inequalities. Conclude with `mul_nonneg (Nat.cast_nonneg _) hd`.

Establish `hAG : 0 ≤ ThreeDimData.AG k r` using `by unfold ThreeDimData.AG; positivity`. Use `⟨hγ, fun a ha => ?_, ⟨inferInstance, ?_, ?_, fun s hs => ?_⟩, fun f hf => ?_, ⟨P.B7.measurable_invM, ?_⟩, 10 * ((r : ℝ) + 1) ^ 2 * (ThreeDimData.AS k r + ThreeDimData.AG k r) + 1, by positivity, ?_, big_int hk L h0 h1 c μ hc hμ ?_⟩` and prove the remaining obligations. Rewrite `ha` using `[hR]`. Take `rfl : a = 1` from `ha`. Rewrite using `[Matrix.mul_one, Matrix.nonsing_inv_mul _ hu, Formalism.MainNotions.BigCellDensity.psi_one _ _ L.hz.1, Formalism.MainNotions.BigCellDensity.psi_one _ _ L.hz'.1]`.

Conclude with `NeZero.ne _`. Rewrite using `[Measure.dirac_apply, Set.indicator_of_notMem]`. Rewrite using `[hR]`. Conclude with `fun h => h rfl`. Rewrite `hs` using `[hR]`.

Take `rfl : s = 1` from `hs`. Rewrite using `[Measure.map_dirac' (Formalism.MainNotions.FrameBoundFromBesselTorus.measurable_lmulM _)]`. Use `congr 1`. Conclude with `Matrix.one_mul (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)`. Use `lintegral_congr fun x => ?_` and prove the remaining obligations.

Rewrite using `[lintegral_dirac]`. Use `congr 1`. Establish `e1 : (Matrix.of (oneM k r) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) = 1` using `rfl`. Simplify using `only [stabAct, e1, Matrix.mul_one, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]`. Both sides reduce to the same expression.

Rewrite using `[Measure.map_dirac' P.B7.measurable_invM]`. Use `congr 1`. Conclude with `inv_one (G := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)`. Unfold `Pv.AmpDD.GapCell at hC`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `: 0 ≤ 10 * ((r : ℝ) + 1) ^ 2 * ThreeDimData.AS k r` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem cell_big (hk : 1 ≤ k) (L : LocBessel k r) (h0 : L.κN ≠ 0) (h1 : L.κN ≠ ⊤) {h : ℝ} (hC : Pv.AmpDD.GapCell k r h)
    (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hc : ∀ a, c a ≠ 0) (hμ : μᴴ * Hb k * μ = Hb k) :
    Cell L (ThreeDimData.aOf r h - 1) (bigCell k r c μ) (Measure.dirac (oneM k r)) (pairMeas L) := by
  have hR : RStab k r (bigCell k r c μ) = {1} := Lem.orbRStabBig k r c μ hc hμ
  have hγ := bigCellMem k r c μ hc hμ
  have hu := uh_isUnit hγ
  have hAS : 0 ≤ ThreeDimData.AS k r := by
    have hd : 0 ≤ ThreeDimData.dN k r := by
      unfold ThreeDimData.dN
      have h0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      have h1 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      nlinarith
    exact mul_nonneg (Nat.cast_nonneg _) hd
  have hAG : 0 ≤ ThreeDimData.AG k r := by unfold ThreeDimData.AG; positivity
  refine ⟨hγ, fun a ha => ?_, ⟨inferInstance, ?_, ?_, fun s hs => ?_⟩, fun f hf => ?_,
    ⟨P.B7.measurable_invM, ?_⟩, 10 * ((r : ℝ) + 1) ^ 2 * (ThreeDimData.AS k r + ThreeDimData.AG k r) + 1, by positivity, ?_,
    big_int hk L h0 h1 c μ hc hμ ?_⟩
  · rw [hR] at ha
    obtain rfl : a = 1 := ha
    rw [Matrix.mul_one, Matrix.nonsing_inv_mul _ hu, Formalism.MainNotions.BigCellDensity.psi_one _ _ L.hz.1,
      Formalism.MainNotions.BigCellDensity.psi_one _ _ L.hz'.1]
  · exact NeZero.ne _
  · rw [Measure.dirac_apply, Set.indicator_of_notMem]
    rw [hR]
    exact fun h => h rfl
  · rw [hR] at hs
    obtain rfl : s = 1 := hs
    rw [Measure.map_dirac' (Formalism.MainNotions.FrameBoundFromBesselTorus.measurable_lmulM _)]
    congr 1
    exact Matrix.one_mul (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
  · refine lintegral_congr fun x => ?_
    rw [lintegral_dirac]
    congr 1
    have e1 : (Matrix.of (oneM k r) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) = 1 := rfl
    simp only [stabAct, e1, Matrix.mul_one, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
    rfl
  · rw [Measure.map_dirac' P.B7.measurable_invM]
    congr 1
    exact inv_one (G := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
  · unfold Pv.AmpDD.GapCell at hC
    linarith
  · have : 0 ≤ 10 * ((r : ℝ) + 1) ^ 2 * ThreeDimData.AS k r := by positivity
    linarith

/- English proof (translation)
Take `⟨k0, rfl⟩ : ∃ k0, k = k0 + 1` from `⟨k - 1, by omega⟩`. Establish `hn : 0 < ‖L.c‖` using `norm_pos_iff.2 hc`. Use `set t : ℝ≥0∞ := ENNReal.ofReal ((2 / ‖L.c‖) ^ (rootPat γ).card) with ht`. Establish `ht0 : t ≠ 0` using `(ENNReal.ofReal_pos.2 (by positivity)).ne'`. Establish `ht1 : t ≠ ⊤` using `ENNReal.ofReal_ne_top`.

Establish `hroot' : IsRootMeas { L with c` using `cStd } γ g (t • μR) := by`. Use `⟨by rw [Measure.smul_apply, hroot.1, smul_zero], ?_⟩` and prove the remaining obligations. Use `show (t • μR).map (rootCoords (k0 + 1) r L.z γ) = ENNReal.ofReal ((‖cStd‖ / (2 * Real.pi)) ^ (rootPat γ).card) • volume`. Rewrite using `[Measure.map_smul, hroot.2, smul_smul, ht, ← ENNReal.ofReal_mul (by positivity), ← mul_pow, Formalism.MainNotions.BigCellDensity.ucStd]`. Use `congr 3`.

Clear the denominators using the available nonvanishing facts. Establish `h1` using `(Formalism.MainNotions.BigCellDensity.rootHaar_gen { L with c := cStd } γ g (t • μR) rfl hrep hroot').1`. Establish `h2` using `Formalism.MainNotions.BigCellDensity.isHaarOn_smul h1 (ENNReal.inv_ne_zero.2 ht1) (ENNReal.inv_ne_top.2 ht0)`. Rewrite `h2` using `[smul_smul, ENNReal.inv_mul_cancel ht0 ht1, one_smul]`. Conclude with `⟨P.B5.haar_sigmaFinite h2, h2.ne_zero, h2.conc, h2.left⟩`.
-/
theorem root_haar (hk : 1 ≤ k) (L : LocBessel k r) (hc : L.c ≠ 0) {γ : Point ℂ (r + 1)} {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    {μR : Measure (Mt k r)} (hrep : IsPtRep L γ g) (hroot : IsRootMeas L γ g μR) : IsHaarOn (RStab k r g) μR := by
  obtain ⟨k0, rfl⟩ : ∃ k0, k = k0 + 1 := ⟨k - 1, by omega⟩
  have hn : 0 < ‖L.c‖ := norm_pos_iff.2 hc
  set t : ℝ≥0∞ := ENNReal.ofReal ((2 / ‖L.c‖) ^ (rootPat γ).card) with ht
  have ht0 : t ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have ht1 : t ≠ ⊤ := ENNReal.ofReal_ne_top
  have hroot' : IsRootMeas { L with c := cStd } γ g (t • μR) := by
    refine ⟨by rw [Measure.smul_apply, hroot.1, smul_zero], ?_⟩
    show (t • μR).map (rootCoords (k0 + 1) r L.z γ) =
      ENNReal.ofReal ((‖cStd‖ / (2 * Real.pi)) ^ (rootPat γ).card) • volume
    rw [Measure.map_smul, hroot.2, smul_smul, ht, ← ENNReal.ofReal_mul (by positivity), ← mul_pow,
      Formalism.MainNotions.BigCellDensity.ucStd]
    congr 3
    field_simp
  have h1 := (Formalism.MainNotions.BigCellDensity.rootHaar_gen { L with c := cStd } γ g (t • μR) rfl hrep hroot').1
  have h2 := Formalism.MainNotions.BigCellDensity.isHaarOn_smul h1 (ENNReal.inv_ne_zero.2 ht1) (ENNReal.inv_ne_top.2 ht0)
  rw [smul_smul, ENNReal.inv_mul_cancel ht0 ht1, one_smul] at h2
  exact ⟨P.B5.haar_sigmaFinite h2, h2.ne_zero, h2.conc, h2.left⟩

/- English proof (translation)
Establish `hR` using `root_haar hO.1 L hc hrep hroot`. Establish `hmono : C2.IsMonomial (Formalism.QuantumDeterminants.Zhat k r L.z L.z' g)` using `⟨Formalism.MainNotions.BigCellDensity.wPt γ, Formalism.MainNotions.BigCellDensity.dPt γ, Formalism.MainNotions.BigCellDensity.dPt_ne γ, by`. Rewrite using `[hrep.2, ← Formalism.MainNotions.BigCellDensity.ptMatN_swap, Formalism.MainNotions.BigCellDensity.ptMatN_mono]⟩`. Establish `hpos : 0 < Gf k r L.z L.z' g`. Use `lt_of_le_of_ne (gNonneg k r L.z L.z' L.hz.1 L.hz'.1 L.hz.2 L.hz'.2 g hrep.1) fun h0 => hG ?_` and prove the remaining obligations.

Rewrite using `[← Formalism.MainNotions.BigCellDensity.gTie k r L.z L.z' γ g hrep.1 hrep.2, ← h0]`. Take `⟨μG, hμG⟩` from `P.unitary_group_haar_exists k r`. Establish `hGsk : IsHaarOn (UH (Hpk k r)) μG` using `⟨P.B5.haar_sigmaFinite hμG, hμG.ne_zero, hμG.conc, hμG.left⟩`. Take `⟨νR, hν⟩` from `quot_exists hrep.1 hGsk hR`. Conclude with `⟨hrep.1, hrel, hR, hq, ⟨P.B7.measurable_invM, rStabInv_of_k k r hO.1 L g μR hrep.1 hmono hR⟩, Pv.AmpDDPf.cell_convergence k r L h μG g μR νR ν h1 hO hC ⟨hrep.1, hpos, hmono, hrel, hR, hq, hν⟩ hmono⟩`.
-/
theorem cell_small (L : LocBessel k r) (hc : L.c ≠ 0) (h1 : L.κN ≠ ⊤) {h : ℝ} (hO : ThreeDimData.GapOK k r h)
    (hC : Pv.AmpDD.GapCell k r h) {γ : Point ℂ (r + 1)} {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} {μR : Measure (Mt k r)} {ν : Measure (PairSp k r)}
    (hG : ThB.Gpt (Tz k r L.z) (Tz k r L.z') γ ≠ 0) (hrep : IsPtRep L γ g) (hrel : IsRelStab L g)
    (hroot : IsRootMeas L γ g μR) (hq : IsOrbQuot L g μR ν) : Cell L (ThreeDimData.aOf r h - 1) g μR ν := by
  have hR := root_haar hO.1 L hc hrep hroot
  have hmono : C2.IsMonomial (Formalism.QuantumDeterminants.Zhat k r L.z L.z' g) :=
    ⟨Formalism.MainNotions.BigCellDensity.wPt γ, Formalism.MainNotions.BigCellDensity.dPt γ, Formalism.MainNotions.BigCellDensity.dPt_ne γ, by
      rw [hrep.2, ← Formalism.MainNotions.BigCellDensity.ptMatN_swap, Formalism.MainNotions.BigCellDensity.ptMatN_mono]⟩
  have hpos : 0 < Gf k r L.z L.z' g := by
    refine lt_of_le_of_ne (gNonneg k r L.z L.z' L.hz.1 L.hz'.1 L.hz.2 L.hz'.2 g hrep.1) fun h0 => hG ?_
    rw [← Formalism.MainNotions.BigCellDensity.gTie k r L.z L.z' γ g hrep.1 hrep.2, ← h0]
  obtain ⟨μG, hμG⟩ := P.unitary_group_haar_exists k r
  have hGsk : IsHaarOn (UH (Hpk k r)) μG := ⟨P.B5.haar_sigmaFinite hμG, hμG.ne_zero, hμG.conc, hμG.left⟩
  obtain ⟨νR, hν⟩ := quot_exists hrep.1 hGsk hR
  exact ⟨hrep.1, hrel, hR, hq, ⟨P.B7.measurable_invM, rStabInv_of_k k r hO.1 L g μR hrep.1 hmono hR⟩,
    Pv.AmpDDPf.cell_convergence k r L h μG g μR νR ν h1 hO hC ⟨hrep.1, hpos, hmono, hrel, hR, hq, hν⟩ hmono⟩

end Formalism.MainStatements.RankOne
