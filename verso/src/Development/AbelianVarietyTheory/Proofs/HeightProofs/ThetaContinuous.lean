import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsSplitIdemIff
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MeanSquareAddFundamentalDomainOfCocompact
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsIsAddHaarMeasureIsAddFundamentalDomainPrei
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SymplecticValTauCompat
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAlgebraMapOfSigRFixed
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ExistsJunkLiftNotVanishing
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ContinuousOfHeisenbergLevelAndSmooth
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SmoothIffRealCoordinatesAndRealLines
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsIsArchimedeanAdeleChartOfRealChart
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsRealChartInfiniteAdelesCmType

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct ContDiff

namespace GlobalTheory.WeilTieCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

/- English proof (translation)
Use extensionality with `k l`. Rewrite using `[Matrix.matrix_eq_sum_single x]`. Simplify using `only [map_sum, Matrix.map_apply, Matrix.sum_apply, Matrix.zero_apply]`. Use `Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Establish `e : Matrix.single i j (x i j) = x i j • Matrix.single i j (1 : AE D)`.

Rewrite using `[Matrix.smul_single, smul_eq_mul, mul_one]`. Establish `h0 : φ (x i j) = 0` using `congrFun (congrFun hx i) j`. Rewrite using `[e, hκ, Matrix.smul_apply, smul_eq_mul, map_mul, h0, zero_mul]`.
-/
theorem map_zero_change {A B V W : HSp D} (κ : WA A B →+ WA V W) (hκ : ∀ (c : AE D) x, κ (c • x) = c • κ x)
    {R : Type} [CommRing R] (φ : AE D →+* R) (x : WA A B) (hx : x.map φ = 0) : (κ x).map φ = 0 := by
  classical
  ext k l
  rw [Matrix.matrix_eq_sum_single x]
  simp only [map_sum, Matrix.map_apply, Matrix.sum_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  have e : Matrix.single i j (x i j) = x i j • Matrix.single i j (1 : AE D) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  have h0 : φ (x i j) = 0 := congrFun (congrFun hx i) j
  rw [e, hκ, Matrix.smul_apply, smul_eq_mul, map_mul, h0, zero_mul]

/- English proof (translation)
Use `⟨fun h => ?_, map_zero_change κ.toAddMonoidHom hκ.2.2.2.2.1 φ x⟩` and prove the remaining obligations. Rewrite using `[← κ.symm_apply_apply x]`. Use `map_zero_change κ.symm.toAddMonoidHom (fun c y => κ.injective ?_) φ _ h` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `κ (κ.symm _) = κ (c • κ.symm y)`. Rewrite using `[hκ.2.2.2.2.1, κ.apply_symm_apply, κ.apply_symm_apply]`.
-/
theorem IsChange.map_zero_iff {A B V W : HSp D} {κ : WA A B ≃+ WA V W} {σ} (hκ : IsChange κ σ)
    {R : Type} [CommRing R] (φ : AE D →+* R) (x : WA A B) : (κ x).map φ = 0 ↔ x.map φ = 0 := by
  refine ⟨fun h => ?_, map_zero_change κ.toAddMonoidHom hκ.2.2.2.2.1 φ x⟩
  rw [← κ.symm_apply_apply x]
  refine map_zero_change κ.symm.toAddMonoidHom (fun c y => κ.injective ?_) φ _ h
  change κ (κ.symm _) = κ (c • κ.symm y)
  rw [hκ.2.2.2.2.1, κ.apply_symm_apply, κ.apply_symm_apply]

/- English proof (translation)
Set `R` to `Fin A.rank → Fin B.rank → (InfinitePlace D.host.F → ℝ) × (InfinitePlace D.host.F → ℝ)`. Set `P : R →+ WA A B` to `AddMonoidHom.mk' (fun p => Matrix.of fun i j => HeisenbergWeilMatrices.realPt D (p i j)) fun p q => Matrix.ext fun i j => (DualPairCompare.realPtHom D).map_add _ _`. Establish `hP : Continuous P` using `continuous_pi fun i => continuous_pi fun j => (DualPairCompare.continuous_realPt D).comp ((continuous_apply j).comp (continuous_apply i))`. Prove the components needed by the constructor for the conclusion. Introduce `h w`.

Set `e : R ≃L[ℝ] (Fin (Module.finrank ℝ R) → ℝ)` to `ContinuousLinearEquiv.ofFinrankEq (by simp)`. Use `(h _ (κ.toAddMonoidHom.comp (P.comp e.symm.toLinearMap.toAddMonoidHom)) (hκ.1.comp (hP.comp e.symm.continuous)) (fun t => (hκ.map_zero_iff _ _).2 (Matrix.ext fun i j => DualPairCompare.finPart_realPt D _)) (κ w)).comp e.contDiff` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `p`. Express the relevant statement in the definitionally equal form `f (κ (w + P p)) = f (κ w + κ (P (e.symm (e p))))`.

Rewrite using `[e.symm_apply_apply, map_add]`. Introduce `h k L hL h0 w`. Take `⟨co, hc, -, h2⟩` from `DualPairCompare.exists_co D`. Set `q : (Fin k → ℝ) →+ R` to `AddMonoidHom.mk' (fun t i j => co (κ.symm (L t) i j)) fun s t => by`. Use function extensionality and compare the values at `i j`.

Rewrite using `[map_add, map_add, Matrix.add_apply, map_add]`. Both sides reduce to the same expression. Establish `hq : Continuous q` using `continuous_pi fun i => continuous_pi fun j => hc.comp ((continuous_apply j).comp ((continuous_apply i).comp (hκ.2.1.comp hL)))`. Use `(h (κ.symm w)).comp (q.toRealLinearMap hq).contDiff` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `t`. Establish `z : (κ.symm (L t)).map (finPart D) = 0`. Rewrite using `[← hκ.map_zero_iff, κ.apply_symm_apply]`. Conclude with `h0 t`. Establish `e : P (q t) = κ.symm (L t)` using `Matrix.ext fun i j => h2 _ (congrFun (congrFun z i) j)`.

Express the relevant statement in the definitionally equal form `_ = f (κ (κ.symm w + P (q t)))`. Rewrite using `[e, map_add, κ.apply_symm_apply, κ.apply_symm_apply]`.
-/
theorem smooth_iff {A B V W : HSp D} {κ : WA A B ≃+ WA V W} {σ} (hκ : IsChange κ σ) (f : WA V W → ℂ) :
    (∀ (k : ℕ) (L : (Fin k → ℝ) →+ WA V W), Continuous L → (∀ t, (L t).map (finPart D) = 0) →
      ∀ w, ContDiff ℝ ∞ fun t => f (w + L t)) ↔
    ∀ w : WA A B, ContDiff ℝ ∞
      fun p : Fin A.rank → Fin B.rank → (InfinitePlace D.host.F → ℝ) × (InfinitePlace D.host.F → ℝ) =>
        (f ∘ κ) (w + Matrix.of fun i j => HeisenbergWeilMatrices.realPt D (p i j)) := by
  let R := Fin A.rank → Fin B.rank → (InfinitePlace D.host.F → ℝ) × (InfinitePlace D.host.F → ℝ)
  let P : R →+ WA A B := AddMonoidHom.mk' (fun p => Matrix.of fun i j => HeisenbergWeilMatrices.realPt D (p i j)) fun p q =>
    Matrix.ext fun i j => (DualPairCompare.realPtHom D).map_add _ _
  have hP : Continuous P := continuous_pi fun i => continuous_pi fun j =>
    (DualPairCompare.continuous_realPt D).comp ((continuous_apply j).comp (continuous_apply i))
  constructor
  · intro h w
    let e : R ≃L[ℝ] (Fin (Module.finrank ℝ R) → ℝ) := ContinuousLinearEquiv.ofFinrankEq (by simp)
    have := (h _ (κ.toAddMonoidHom.comp (P.comp e.symm.toLinearMap.toAddMonoidHom))
      (hκ.1.comp (hP.comp e.symm.continuous)) (fun t => (hκ.map_zero_iff _ _).2 (Matrix.ext fun i j =>
        DualPairCompare.finPart_realPt D _)) (κ w)).comp e.contDiff
    convert this using 1
    funext p
    change f (κ (w + P p)) = f (κ w + κ (P (e.symm (e p))))
    rw [e.symm_apply_apply, map_add]
  · intro h k L hL h0 w
    obtain ⟨co, hc, -, h2⟩ := DualPairCompare.exists_co D
    let q : (Fin k → ℝ) →+ R := AddMonoidHom.mk' (fun t i j => co (κ.symm (L t) i j)) fun s t => by
      funext i j
      rw [map_add, map_add, Matrix.add_apply, map_add]
      rfl
    have hq : Continuous q := continuous_pi fun i => continuous_pi fun j =>
      hc.comp ((continuous_apply j).comp ((continuous_apply i).comp (hκ.2.1.comp hL)))
    have := (h (κ.symm w)).comp (q.toRealLinearMap hq).contDiff
    convert this using 1
    funext t
    have z : (κ.symm (L t)).map (finPart D) = 0 := by
      rw [← hκ.map_zero_iff, κ.apply_symm_apply]; exact h0 t
    have e : P (q t) = κ.symm (L t) := Matrix.ext fun i j => h2 _ (congrFun (congrFun z i) j)
    change _ = f (κ (κ.symm w + P (q t)))
    rw [e, map_add, κ.apply_symm_apply, κ.apply_symm_apply]

/- English proof (translation)
Establish `sk : ∀ x y, -symplH V W (κ x) (κ y) = HeisenbergWeilMatrices.hsymp y x` using `fun x y => by`. Rewrite using `[← hκ.2.2.1]`. Unfold `symplH`. Rewrite using `[DualPairCheck.sympl_skew V W (κ x), mul_neg]`. Establish `lv : ∀ u, Heisenberg₂ ψ V W (κ u) f = f ↔ HeisenbergWeilMatrices.rho ψ u (f ∘ κ) = f ∘ κ` using `fun u => by`.

Rewrite using `[← heis_change hκ]`. Conclude with `(κ.surjective.injective_comp_right.eq_iff).symm`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, ⟨U, hU, h2⟩, -, h4⟩`. Use `⟨fun γ hγ w => ?_, (smooth_iff hκ f).1 h4, U.comap κ.toAddMonoidHom, hU.preimage hκ.1, fun u hu h0 => (lv u).1 (h2 _ hu ((hκ.map_zero_iff _ _).2 h0))⟩` and prove the remaining obligations.

Take `⟨δ, hδ⟩` from `(hκ.2.2.2.1 γ).2 hγ`. Use `h1 δ (κ w)` as an intermediate fact. Rewrite `this` using `[show ratW V W δ = κ γ from hδ, sk, ← map_add]`. Conclude with `this`. Introduce and unpack `⟨h1, h2, U, hU, h3⟩`.

Establish `l : ∃ U : AddSubgroup (WA V W), IsOpen (U : Set (WA V W)) ∧ ∀ u ∈ U, u.map (infPart D) = 0 → Heisenberg₂ ψ V W u f = f`. Use `⟨U.comap κ.symm.toAddMonoidHom, hU.preimage hκ.2.1, fun u hu h0 => ?_⟩` and prove the remaining obligations. Take `⟨u, rfl⟩` from `κ.surjective u`. Conclude with `(lv u).2 (h3 u (κ.symm_apply_apply u ▸ hu) ((hκ.map_zero_iff _ _).1 h0))`. Establish `s` using `(smooth_iff hκ f).2 h2`.

Take `⟨θ, hθ⟩` from `DualPairCompare.exists_infFam D`. Take `⟨ρ, r1, r2, r3⟩` from `FockCompare.exists_real_chart D θ hθ (DualPairCompare.plF_bijective D)`. Take `⟨s', hs'⟩` from `FockCompare.RealChart.exists_chart D θ hθ ρ r1 r2 r3`. Use `⟨fun δ w => ?_, l, FockCompare.ThetaCont.continuous_of_level_of_smooth D θ s' hs' ψ hψ V W f l (((FockCompare.smooth_iff_sm_and_real_lines D θ s' hs' V W).1 f).1 s), s⟩` and prove the remaining obligations. Take `⟨γ, hγ⟩` from `κ.surjective (ratW V W δ)`.

Take `⟨w, rfl⟩` from `κ.surjective w`. Rewrite using `[← hγ, sk, ← map_add]`. Conclude with `h1 γ ((hκ.2.2.2.1 γ).1 ⟨δ, hγ.symm⟩) w`.
-/
theorem theta_iff {A B V W : HSp D} {κ : WA A B ≃+ WA V W} {σ} (hκ : IsChange κ σ) {ψ : AddChar (AF D.host.F) ℂ}
    (hψ : Continuous ψ) (f : WA V W → ℂ) : IsThetaFun ψ V W f ↔ HeisenbergWeilMatrices.IsTheta ψ (f ∘ κ) := by
  have sk : ∀ x y, -symplH V W (κ x) (κ y) = HeisenbergWeilMatrices.hsymp y x := fun x y => by
    rw [← hκ.2.2.1]
    unfold symplH
    rw [DualPairCheck.sympl_skew V W (κ x), mul_neg]
  have lv : ∀ u, Heisenberg₂ ψ V W (κ u) f = f ↔ HeisenbergWeilMatrices.rho ψ u (f ∘ κ) = f ∘ κ := fun u => by
    rw [← heis_change hκ]
    exact (κ.surjective.injective_comp_right.eq_iff).symm
  constructor
  · rintro ⟨h1, ⟨U, hU, h2⟩, -, h4⟩
    refine ⟨fun γ hγ w => ?_, (smooth_iff hκ f).1 h4, U.comap κ.toAddMonoidHom, hU.preimage hκ.1, fun u hu h0 =>
      (lv u).1 (h2 _ hu ((hκ.map_zero_iff _ _).2 h0))⟩
    obtain ⟨δ, hδ⟩ := (hκ.2.2.2.1 γ).2 hγ
    have := h1 δ (κ w)
    rw [show ratW V W δ = κ γ from hδ, sk, ← map_add] at this
    exact this
  · rintro ⟨h1, h2, U, hU, h3⟩
    have l : ∃ U : AddSubgroup (WA V W), IsOpen (U : Set (WA V W)) ∧
        ∀ u ∈ U, u.map (infPart D) = 0 → Heisenberg₂ ψ V W u f = f := by
      refine ⟨U.comap κ.symm.toAddMonoidHom, hU.preimage hκ.2.1, fun u hu h0 => ?_⟩
      obtain ⟨u, rfl⟩ := κ.surjective u
      exact (lv u).2 (h3 u (κ.symm_apply_apply u ▸ hu) ((hκ.map_zero_iff _ _).1 h0))
    have s := (smooth_iff hκ f).2 h2
    obtain ⟨θ, hθ⟩ := DualPairCompare.exists_infFam D
    obtain ⟨ρ, r1, r2, r3⟩ := FockCompare.exists_real_chart D θ hθ (DualPairCompare.plF_bijective D)
    obtain ⟨s', hs'⟩ := FockCompare.RealChart.exists_chart D θ hθ ρ r1 r2 r3
    refine ⟨fun δ w => ?_, l, FockCompare.ThetaCont.continuous_of_level_of_smooth D θ s' hs' ψ hψ V W f l
      (((FockCompare.smooth_iff_sm_and_real_lines D θ s' hs' V W).1 f).1 s), s⟩
    obtain ⟨γ, hγ⟩ := κ.surjective (ratW V W δ)
    obtain ⟨w, rfl⟩ := κ.surjective w
    rw [← hγ, sk, ← map_add]
    exact h1 γ ((hκ.2.2.2.1 γ).1 ⟨δ, hγ.symm⟩) w

/- English proof (translation)
Use `and_congr_right fun _ => ⟨fun h x => ?_, fun h => ⟨DualPairCompare.exists_infFam D, fun θ hθ x => ?_⟩⟩` and prove the remaining obligations. Take `⟨θ, hθ⟩` from `h.1`. Rewrite using `[h.2 θ hθ x, DualPairCompare.sum_infFam θ hθ]`. Both sides reduce to the same expression. Rewrite using `[h x, DualPairCompare.sum_infFam θ hθ]`.

Both sides reduce to the same expression.
-/
theorem stdChar_iff (ψ : AddChar (AF D.host.F) ℂ) : IsStdChar D ψ (-1) ↔ HeisenbergWeilMatrices.IsStdChar D (-1) ψ := by
  refine and_congr_right fun _ => ⟨fun h x => ?_, fun h => ⟨DualPairCompare.exists_infFam D, fun θ hθ x => ?_⟩⟩
  · obtain ⟨θ, hθ⟩ := h.1
    rw [h.2 θ hθ x, DualPairCompare.sum_infFam θ hθ]
    rfl
  · rw [h x, DualPairCompare.sum_infFam θ hθ]
    rfl

/- English proof (translation)
Establish `hκ` using `isChange_kap hr`. Establish `h : IsThetaFun ψ A B ((f : WA A B → ℂ) ∘ (kap A B).symm)`. Rewrite using `[theta_iff hκ hψ]`. Establish `: ((f : WA A B → ℂ) ∘ (kap A B).symm) ∘ kap A B = f` using `by funext x; simp`. Rewrite using `[this]`.

Conclude with `f.2`. Use `h.cont.comp hκ.1` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x`. Simplify using the standard rewrite rules.
-/
theorem theta_continuous {A B : HSp D} {ψ : AddChar (AF D.host.F) ℂ} (hψ : Continuous ψ) (hr : A.rank ≤ B.rank)
    (f : HeisenbergWeilMatrices.Theta ψ A B) : Continuous (f : WA A B → ℂ) := by
  have hκ := isChange_kap hr
  have h : IsThetaFun ψ A B ((f : WA A B → ℂ) ∘ (kap A B).symm) := by
    rw [theta_iff hκ hψ]
    have : ((f : WA A B → ℂ) ∘ (kap A B).symm) ∘ kap A B = f := by funext x; simp
    rw [this]; exact f.2
  have := h.cont.comp hκ.1
  convert this using 1
  funext x; simp

def SameNorm (V W : HSp D) (f f' : WA V W → ℂ) : Prop :=
  ∀ (μ : Measure (WA V W)) (𝓕 : Set (WA V W)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL V W) 𝓕 μ →
    ∫ w in 𝓕, ‖f' w‖ ^ 2 ∂μ = ∫ w in 𝓕, ‖f w‖ ^ 2 ∂μ

/- English proof (translation)
Establish `: BorelSpace (WA A B)` using `⟨rfl⟩`. Establish `: BorelSpace (WA V W)` using `⟨rfl⟩`. Use `(GlobalTheory.AdelicMatrixLattice.lattice D A B).1` as an intermediate fact. Use `(GlobalTheory.AdelicMatrixLattice.lattice D V W).1` as an intermediate fact. Prove the components needed by the constructor for the conclusion.

Introduce `h μ 𝓕 hμ hF`. Take `⟨ν, h1, h2, h3⟩` from `GlobalTheory.exists_isAddHaarMeasure_isAddFundamentalDomain_preimage _ _ κ.symm hκ.2.1 hκ.1 (ratL V W) (ratL A B) (fun x => ((hκ.2.2.2.1 (κ.symm x)).symm.trans (by rw [κ.apply_symm_apply]))) μ 𝓕 hμ hF`. Rewrite using `[← h3 fun w => ‖(f' ∘ κ) w‖ ^ 2, ← h3 fun w => ‖(f ∘ κ) w‖ ^ 2]`. Simplify using `using h ν _ h1 h2`. Introduce `h μ 𝓕 hμ hF`.

Take `⟨ν, h1, h2, h3⟩` from `GlobalTheory.exists_isAddHaarMeasure_isAddFundamentalDomain_preimage _ _ κ hκ.1 hκ.2.1 (ratL A B) (ratL V W) hκ.2.2.2.1 μ 𝓕 hμ hF`. Rewrite using `[← h3 fun w => ‖f' w‖ ^ 2, ← h3 fun w => ‖f w‖ ^ 2]`. Conclude with `h ν _ h1 h2`.
-/
theorem sameNorm_change {A B V W : HSp D} {κ : WA A B ≃+ WA V W} {σ} (hκ : IsChange κ σ) (f f' : WA V W → ℂ) :
    SameNorm V W f f' ↔ SameNorm A B (f ∘ κ) (f' ∘ κ) := by
  have : BorelSpace (WA A B) := ⟨rfl⟩
  have : BorelSpace (WA V W) := ⟨rfl⟩
  have := (GlobalTheory.AdelicMatrixLattice.lattice D A B).1
  have := (GlobalTheory.AdelicMatrixLattice.lattice D V W).1
  constructor
  · intro h μ 𝓕 hμ hF
    obtain ⟨ν, h1, h2, h3⟩ := GlobalTheory.exists_isAddHaarMeasure_isAddFundamentalDomain_preimage _ _ κ.symm hκ.2.1 hκ.1 (ratL V W) (ratL A B)
      (fun x => ((hκ.2.2.2.1 (κ.symm x)).symm.trans (by rw [κ.apply_symm_apply]))) μ 𝓕 hμ hF
    rw [← h3 fun w => ‖(f' ∘ κ) w‖ ^ 2, ← h3 fun w => ‖(f ∘ κ) w‖ ^ 2]
    simpa using h ν _ h1 h2
  · intro h μ 𝓕 hμ hF
    obtain ⟨ν, h1, h2, h3⟩ := GlobalTheory.exists_isAddHaarMeasure_isAddFundamentalDomain_preimage _ _ κ hκ.1 hκ.2.1 (ratL A B) (ratL V W) hκ.2.2.2.1 μ 𝓕 hμ hF
    rw [← h3 fun w => ‖f' w‖ ^ 2, ← h3 fun w => ‖f w‖ ^ 2]
    exact h ν _ h1 h2

/- English proof (translation)
Establish `: BorelSpace (WA A B)` using `⟨rfl⟩`. Take `⟨_, _, _, _, _, K, hK, hc⟩` from `GlobalTheory.AdelicMatrixLattice.lattice D A B`. Take `⟨μ, 𝓕, h⟩` from `(GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact _ (ratL A B) K hK hc).1`. Conclude with `⟨(μ, 𝓕), h⟩`.
-/
theorem exists_probPair (A B : HSp D) : ∃ m : Measure (WA A B) × Set (WA A B), HeisenbergWeilMatrices.IsProbPair A B m.1 m.2 := by
  have : BorelSpace (WA A B) := ⟨rfl⟩
  obtain ⟨_, _, _, _, _, K, hK, hc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D A B
  obtain ⟨μ, 𝓕, h⟩ := (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact _ (ratL A B) K hK hc).1
  exact ⟨(μ, 𝓕), h⟩

/- English proof (translation)
Establish `: BorelSpace (WA A B)` using `⟨rfl⟩`. Take `⟨_, _, _, _, _, K, hK, hc⟩` from `GlobalTheory.AdelicMatrixLattice.lattice D A B`. Establish `key` using `fun f : HeisenbergWeilMatrices.Theta ψ A B => (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact _ (ratL A B) K hK hc).2 f (theta_continuous hψ.1 hr f) fun γ hγ w => by rw [f.2.law γ hγ w, norm_mul, hψ.2.1, one_mul]`. Take `⟨N, hN⟩` from `key f`. Take `⟨N', hN'⟩` from `key f'`.

Take `⟨m, hm⟩` from `exists_probPair A B`. Establish `e : ∀ (g : WA A B → ℂ) (M : NNReal), (∀ (μ : Measure (WA A B)) (𝓕 : Set (WA A B)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL A B) 𝓕 μ → μ 𝓕 ≠ 0 ∧ μ 𝓕 ≠ ⊤ ∧ ∫⁻ w in 𝓕, ‖g w‖ₑ ^ 2 ∂μ = μ 𝓕 * M ∧ ∫ w in 𝓕, ‖g w‖ ^ 2 ∂μ = (μ 𝓕).toReal * M) → HeisenbergWeilMatrices.IsNormSq g …` using `fun g M h => ⟨⟨m, hm⟩, fun a ha => (h a.1 a.2 ha.1 ha.2.1).2.2.1.trans (by rw [ha.2.2, one_mul])⟩`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h1` using `h m.1 m.2 hm.1 hm.2.1`.

Rewrite `h1` using `[(hN _ _ hm.1 hm.2.1).2.2.2, (hN' _ _ hm.1 hm.2.1).2.2.2, hm.2.2]`. Establish `h2 : N' = N` using `by simpa using h1`. Conclude with `⟨N, ENNReal.coe_ne_top, e _ _ hN, h2 ▸ e _ _ hN'⟩`. Introduce and unpack `⟨M, -, h1, h2⟩ μ 𝓕 hμ hF`. Establish `h3 : (N' : ENNReal) = N` using `(((e _ _ hN').2 m hm).symm.trans (h2.2 m hm)).trans ((h1.2 m hm).symm.trans ((e _ _ hN).2 m hm))`.

Rewrite using `[(hN _ _ hμ hF).2.2.2, (hN' _ _ hμ hF).2.2.2, ENNReal.coe_inj.1 h3]`.
-/
theorem sameNorm_iff {A B : HSp D} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (hr : A.rank ≤ B.rank)
    (f f' : HeisenbergWeilMatrices.Theta ψ A B) :
    SameNorm A B f f' ↔ ∃ N, N ≠ ⊤ ∧ HeisenbergWeilMatrices.IsNormSq (f : WA A B → ℂ) N ∧ HeisenbergWeilMatrices.IsNormSq (f' : WA A B → ℂ) N := by
  have : BorelSpace (WA A B) := ⟨rfl⟩
  obtain ⟨_, _, _, _, _, K, hK, hc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D A B
  have key := fun f : HeisenbergWeilMatrices.Theta ψ A B => (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact _ (ratL A B) K hK hc).2 f (theta_continuous hψ.1 hr f)
    fun γ hγ w => by rw [f.2.law γ hγ w, norm_mul, hψ.2.1, one_mul]
  obtain ⟨N, hN⟩ := key f
  obtain ⟨N', hN'⟩ := key f'
  obtain ⟨m, hm⟩ := exists_probPair A B
  have e : ∀ (g : WA A B → ℂ) (M : NNReal), (∀ (μ : Measure (WA A B)) (𝓕 : Set (WA A B)), μ.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratL A B) 𝓕 μ → μ 𝓕 ≠ 0 ∧ μ 𝓕 ≠ ⊤ ∧ ∫⁻ w in 𝓕, ‖g w‖ₑ ^ 2 ∂μ = μ 𝓕 * M ∧
        ∫ w in 𝓕, ‖g w‖ ^ 2 ∂μ = (μ 𝓕).toReal * M) → HeisenbergWeilMatrices.IsNormSq g M := fun g M h =>
    ⟨⟨m, hm⟩, fun a ha => (h a.1 a.2 ha.1 ha.2.1).2.2.1.trans (by rw [ha.2.2, one_mul])⟩
  constructor
  · intro h
    have h1 := h m.1 m.2 hm.1 hm.2.1
    rw [(hN _ _ hm.1 hm.2.1).2.2.2, (hN' _ _ hm.1 hm.2.1).2.2.2, hm.2.2] at h1
    have h2 : N' = N := by simpa using h1
    exact ⟨N, ENNReal.coe_ne_top, e _ _ hN, h2 ▸ e _ _ hN'⟩
  · rintro ⟨M, -, h1, h2⟩ μ 𝓕 hμ hF
    have h3 : (N' : ENNReal) = N :=
      (((e _ _ hN').2 m hm).symm.trans (h2.2 m hm)).trans ((h1.2 m hm).symm.trans ((e _ _ hN).2 m hm))
    rw [(hN _ _ hμ hF).2.2.2, (hN' _ _ hμ hF).2.2.2, ENNReal.coe_inj.1 h3]

/- English proof (translation)
The claim follows from `Algebra.TensorProduct.includeLeft_injective (S := D.host.F) (algebraMap D.host.F D.host.E).injective`.
-/
theorem alg_inj (D : D7) : Function.Injective (algebraMap (AF D.host.F) (AE D)) :=
  Algebra.TensorProduct.includeLeft_injective (S := D.host.F) (algebraMap D.host.F D.host.E).injective

/- English proof (translation)
Establish `h1 : e * e = e` using `he.idem`. Establish `h2 : e * cA D e = 0` using `he.orth`. Establish `h3 : e + cA D e = HeisenbergWeilMatrices.idemFin D v` using `he.sum`. Establish `k : HeisenbergWeilMatrices.trA D (e * u) * HeisenbergWeilMatrices.trA D (e * ↑u⁻¹) = pairA D.host.F 0 (singleV D.host.F v 1)`. Apply `alg_inj D` to reduce the goal to its premises.

Establish `hu : cA D u * cA D ↑u⁻¹ = 1` using `by rw [← map_mul, u.mul_inv, map_one]`. Establish `hc : cA D e * cA D e = cA D e` using `by rw [← map_mul, h1]`. Rewrite using `[map_mul]`. Use `Eq.trans ?_ h3` and prove the remaining obligations. Use `erw [GlobalTheory.FockCompare.SymplVal.trace_AE D, GlobalTheory.FockCompare.SymplVal.trace_AE D]`.

Rewrite using `[map_mul, map_mul]`. Take the linear combination `(e * e) * u.mul_inv + h1 + (cA D e * cA D e) * hu + hc + (u * cA D ↑u⁻¹ + cA D u * ↑u⁻¹) * h2`. Introduce `h0`. Use `congrArg (fun a => evalV D.host.F v (sndA D.host.F a)) k` as an intermediate fact. Simplify using `only [map_mul] at this`.

Express the relevant statement in the definitionally equal form `HeisenbergWeilMatrices.wComp D v e u * _ = _ at this`. Rewrite `this` using `[h0, zero_mul]`. Conclude with `zero_ne_one (this.trans (RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 D.host.F) => w.adicCompletionIntegers D.host.F) v 1))`.
-/
theorem wComp_ne {v} {e : AE D} (he : HeisenbergWeilMatrices.IsSplitIdem D v e) (u : (AE D)ˣ) : HeisenbergWeilMatrices.wComp D v e u ≠ 0 := by
  classical
  have h1 : e * e = e := he.idem
  have h2 : e * cA D e = 0 := he.orth
  have h3 : e + cA D e = HeisenbergWeilMatrices.idemFin D v := he.sum
  have k : HeisenbergWeilMatrices.trA D (e * u) * HeisenbergWeilMatrices.trA D (e * ↑u⁻¹) = pairA D.host.F 0 (singleV D.host.F v 1) := by
    apply alg_inj D
    have hu : cA D u * cA D ↑u⁻¹ = 1 := by rw [← map_mul, u.mul_inv, map_one]
    have hc : cA D e * cA D e = cA D e := by rw [← map_mul, h1]
    rw [map_mul]
    refine Eq.trans ?_ h3
    erw [GlobalTheory.FockCompare.SymplVal.trace_AE D, GlobalTheory.FockCompare.SymplVal.trace_AE D]
    rw [map_mul, map_mul]
    linear_combination (e * e) * u.mul_inv + h1 + (cA D e * cA D e) * hu + hc +
      (u * cA D ↑u⁻¹ + cA D u * ↑u⁻¹) * h2
  intro h0
  have := congrArg (fun a => evalV D.host.F v (sndA D.host.F a)) k
  simp only [map_mul] at this
  change HeisenbergWeilMatrices.wComp D v e u * _ = _ at this
  rw [h0, zero_mul] at this
  exact zero_ne_one (this.trans
    (RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 D.host.F) => w.adicCompletionIntegers D.host.F) v 1))

/- English proof (translation)
Establish `k : ∀ u : (AE D)ˣ, 0 < HeisenbergWeilMatrices.absV D v (HeisenbergWeilMatrices.wComp D v e u)` using `fun u => NNReal.coe_pos.2 (WithZeroMulInt.toNNReal_pos _ ((Valuation.ne_zero_iff _).2 (wComp_ne he u)))`. Conclude with `mul_pos (Real.rpow_pos_of_pos (k _) _) (Real.rpow_pos_of_pos (k _) _)`.
-/
theorem splitMod_pos {v} {e : AE D} (he : HeisenbergWeilMatrices.IsSplitIdem D v e) (A B : HSp D) (p : GA D A × GA D B) :
    0 < HeisenbergWeilMatrices.splitMod A B v e p := by
  have k : ∀ u : (AE D)ˣ, 0 < HeisenbergWeilMatrices.absV D v (HeisenbergWeilMatrices.wComp D v e u) := fun u =>
    NNReal.coe_pos.2 (WithZeroMulInt.toNNReal_pos _ ((Valuation.ne_zero_iff _).2 (wComp_ne he u)))
  exact mul_pos (Real.rpow_pos_of_pos (k _) _) (Real.rpow_pos_of_pos (k _) _)

section Clauses

variable {A B V W : HSp D} {κ : WA A B ≃+ WA V W} {σ : GA D V × GA D W → GA D A × GA D B}
  {ψ : AddChar (AF D.host.F) ℂ} {S : Type} [AddCommGroup S] [Module ℂ S]
  {ev : S →ₗ[ℂ] (WA V W → ℂ)} {E : S ≃ₗ[ℂ] HeisenbergWeilMatrices.Theta ψ A B}

/- English proof (translation)
Rewrite using `[← hE, ← hE, ← heis_change hκ]`. Conclude with `(κ.surjective.injective_comp_right.eq_iff).symm`.
-/
theorem heis_iff (hκ : IsChange κ σ) (hE : ∀ Φ, ev Φ ∘ κ = E Φ) (u : WA A B) (Φ Φ' : S) :
    ev Φ' = Heisenberg₂ ψ V W (κ u) (ev Φ) ↔ (E Φ' : WA A B → ℂ) = HeisenbergWeilMatrices.rho ψ u (E Φ) := by
  rw [← hE, ← hE, ← heis_change hκ]
  exact (κ.surjective.injective_comp_right.eq_iff).symm

/- English proof (translation)
Unfold `HeisenbergWeilMatrices.Implements`. Rewrite using `[κ.surjective.forall]`. Use `forall_congr' fun u => ?_` and prove the remaining obligations. Rewrite using `[E.surjective.forall]`. Use `forall_congr' fun Φ => ?_` and prove the remaining obligations.

Rewrite using `[E.surjective.forall]`. Use `forall_congr' fun Φ' => ?_` and prove the remaining obligations. Rewrite using `[hκ.2.2.2.2.2, heis_iff hκ hE, heis_iff hκ hE, hM, hM]`.
-/
theorem impl_iff (hκ : IsChange κ σ) (hE : ∀ Φ, ev Φ ∘ κ = E Φ) {M : Module.End ℂ S}
    {N : Module.End ℂ (HeisenbergWeilMatrices.Theta ψ A B)} (hM : ∀ Φ, E (M Φ) = N (E Φ)) (g : GA D V) (h : GA D W) :
    (∀ w₀ Φ Φ', ev Φ' = Heisenberg₂ ψ V W w₀ (ev Φ) → ev (M Φ') = Heisenberg₂ ψ V W (actHom V W g h w₀) (ev (M Φ))) ↔
      HeisenbergWeilMatrices.Implements N (σ (g, h)) := by
  unfold HeisenbergWeilMatrices.Implements
  rw [κ.surjective.forall]
  refine forall_congr' fun u => ?_
  rw [E.surjective.forall]
  refine forall_congr' fun Φ => ?_
  rw [E.surjective.forall]
  refine forall_congr' fun Φ' => ?_
  rw [hκ.2.2.2.2.2, heis_iff hκ hE, heis_iff hκ hE, hM, hM]

/- English proof (translation)
Rewrite using `[sameNorm_change hκ, hE, hE, sameNorm_iff hψ hr]`.
-/
theorem unit_iff (hκ : IsChange κ σ) (hE : ∀ Φ, ev Φ ∘ κ = E Φ) (hψ : IsCharAF D.host.F ψ) (hr : A.rank ≤ B.rank)
    (Φ Φ' : S) : SameNorm V W (ev Φ) (ev Φ') ↔
      ∃ N, N ≠ ⊤ ∧ HeisenbergWeilMatrices.IsNormSq (E Φ : WA A B → ℂ) N ∧ HeisenbergWeilMatrices.IsNormSq (E Φ' : WA A B → ℂ) N := by
  rw [sameNorm_change hκ, hE, hE, sameNorm_iff hψ hr]

/- English proof (translation)
Establish `key : ∀ l : HeisenbergWeilMatrices.Theta ψ A B →ₗ[ℂ] ℂ, (∀ u : WA V W, (∀ i j, cA D e * u i j = u i j) → ∀ Φ Φ', ev Φ' = Heisenberg₂ ψ V W u (ev Φ) → l (E Φ') = l (E Φ)) ↔ ∀ y ∈ HeisenbergWeilMatrices.lagr A B (HeisenbergWeilMatrices.cj D e), ∀ f f' : HeisenbergWeilMatrices.Theta …`. Introduce `l`. Rewrite using `[κ.surjective.forall]`. Use `forall_congr' fun u => imp_congr ?_ ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ ↔ cA D e • u = u`.

Rewrite using `[← κ.injective.eq_iff, hκ.2.2.2.2.1, ← Matrix.ext_iff]`. Both sides reduce to the same expression. Rewrite using `[E.surjective.forall]`. Use `forall_congr' fun Φ => ?_` and prove the remaining obligations. Rewrite using `[E.surjective.forall]`.

Use `forall_congr' fun Φ' => ?_` and prove the remaining obligations. Rewrite using `[heis_iff hκ hE]`. Prove the components needed by the constructor for the conclusion. Introduce `h l hl f`. Take `⟨Φ, rfl⟩` from `E.surjective f`.

Rewrite using `[← hM]`. Conclude with `h (l ∘ₗ E.toLinearMap) ((key l).2 hl) Φ`. Introduce `h ℓ hℓ Φ`. Use `h (ℓ ∘ₗ E.symm.toLinearMap) ((key _).1 fun u hu Φ Φ' hh => by simpa using hℓ u hu Φ Φ' hh) (E Φ)` as an intermediate fact. Rewrite `this` using `[← hM]`.

Simplify `this` using `only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]`.
-/
theorem actsBy_iff (hκ : IsChange κ σ) (hE : ∀ Φ, ev Φ ∘ κ = E Φ) {M : Module.End ℂ S}
    {N : Module.End ℂ (HeisenbergWeilMatrices.Theta ψ A B)} (hM : ∀ Φ, E (M Φ) = N (E Φ)) (e : AE D) (c : ℂ) :
    (∀ ℓ : S →ₗ[ℂ] ℂ, (∀ u : WA V W, (∀ i j, cA D e * u i j = u i j) → ∀ Φ Φ', ev Φ' = Heisenberg₂ ψ V W u (ev Φ) → ℓ Φ' = ℓ Φ) →
      ∀ Φ, ℓ (M Φ) = c * ℓ Φ) ↔ HeisenbergWeilMatrices.ActsBy e N c := by
  have key : ∀ l : HeisenbergWeilMatrices.Theta ψ A B →ₗ[ℂ] ℂ,
      (∀ u : WA V W, (∀ i j, cA D e * u i j = u i j) → ∀ Φ Φ', ev Φ' = Heisenberg₂ ψ V W u (ev Φ) → l (E Φ') = l (E Φ)) ↔
      ∀ y ∈ HeisenbergWeilMatrices.lagr A B (HeisenbergWeilMatrices.cj D e), ∀ f f' : HeisenbergWeilMatrices.Theta ψ A B,
        (f' : WA A B → ℂ) = HeisenbergWeilMatrices.rho ψ y f → l f' = l f := by
    intro l
    rw [κ.surjective.forall]
    refine forall_congr' fun u => imp_congr ?_ ?_
    · change _ ↔ cA D e • u = u
      rw [← κ.injective.eq_iff, hκ.2.2.2.2.1, ← Matrix.ext_iff]
      rfl
    · rw [E.surjective.forall]
      refine forall_congr' fun Φ => ?_
      rw [E.surjective.forall]
      refine forall_congr' fun Φ' => ?_
      rw [heis_iff hκ hE]
  constructor
  · intro h l hl f
    obtain ⟨Φ, rfl⟩ := E.surjective f
    rw [← hM]
    exact h (l ∘ₗ E.toLinearMap) ((key l).2 hl) Φ
  · intro h ℓ hℓ Φ
    have := h (ℓ ∘ₗ E.symm.toLinearMap) ((key _).1 fun u hu Φ Φ' hh => by simpa using hℓ u hu Φ Φ' hh) (E Φ)
    rw [← hM] at this
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using this

/- English proof (translation)
Rewrite using `[← hE, Function.comp, map_zero]`.
-/
theorem ev_zero (hE : ∀ Φ, ev Φ ∘ κ = E Φ) (Φ : S) : ev Φ 0 = (E Φ : WA A B → ℂ) 0 := by
  rw [← hE, Function.comp, map_zero]

end Clauses

end GlobalTheory.WeilTieCompare

end
