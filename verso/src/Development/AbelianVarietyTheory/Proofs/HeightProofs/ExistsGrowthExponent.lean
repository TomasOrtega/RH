import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddHsConjLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CasselmanWallachExtensionBanachTarget
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsKFinDRep
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KFiniteLeOfGKStableDiscreteSeriesModel
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HasDerivAtMap
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.PointAtPlaceHom GlobalTheory.Mem.AutSpace GlobalTheory.TypeSum GlobalTheory.TypeSum.GrowthAtPlace Formalism.REAL

namespace GlobalTheory.TypeSum.GKCoef

/- English proof (translation)
Introduce `D θ V τ hθ hHC H _ _ σ lam ε P T hDS hP hPG hT x`. Use `haveI : CompleteSpace H := hDS.1`. Establish `hstd : Std ε σ` using `std_of_isDS hHC hDS`. Take `⟨Th, hTh⟩` from `LinearMap.exists_extend T`. Establish `eTh : ∀ v (hv : v ∈ GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ), Th v = T ⟨v, hv⟩` using `fun v hv => LinearMap.congr_fun hTh ⟨v, hv⟩`.

Establish `hkf : ∀ v, IsKFin ε σ v → v ∈ GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ` using `fun v hv => mem_kFin_iff.2 hv`. Establish `hDw : ∀ l : List (Mx V.rank), (∀ X ∈ l, X ∈ lieSet ε) → ∀ v, IsKFin ε σ v → IsKFin ε σ (Dw σ l v)`. Introduce `l hl v hv`. Proceed by induction on `l with`. Consider the case `nil => exact hv`.

Consider the case `cons X l ih`. Conclude with `isKFin_dRep _ ε H σ hstd _ (ih fun Y hY => hl Y (List.mem_cons_of_mem _ hY)) X (hl X List.mem_cons_self)`. Take `⟨u, hu, hu0⟩` from `hstd.2.2.2.2`. Take `⟨N, F, hF0, hFd, hFg⟩` from `umg_atTau D θ hθ V τ (T ⟨u, hkf u hu⟩) (hT.aut _) ε P hP hPG x`. Establish `hFeq : ∀ l : List (Mx V.rank), (∀ X ∈ l, X ∈ lieSet ε) → ∀ y ∈ UJset ε, F l y = Th (Dw σ l u) (x * atTau θ V τ (P⁻¹ * y * P))`.

Introduce `l hl`. Proceed by induction on `l with`. Consider the case `nil => intro y hy`. Rewrite using `[hF0 y hy]`. Conclude with `(congrFun (eTh u (hkf u hu)) _).symm`.

Consider the case `cons X l ih`. Introduce `y hy`. Establish `hl' : ∀ Y ∈ l, Y ∈ lieSet ε` using `fun Y hY => hl Y (List.mem_cons_of_mem _ hY)`. Establish `hX` using `hl X List.mem_cons_self`. Establish `k1` using `hDw l hl' u hu`.

Establish `k2` using `hDw (X :: l) hl u hu`. Establish `d1` using `hFd l hl' X hX y hy`. Establish `d2` using `hasDerivAt_map hθ hP hPG hT ⟨Dw σ l u, hkf _ k1⟩ ⟨Dw σ (X :: l) u, hkf _ k2⟩ hX (hstd.2.2.1 _ k1) rfl x hy`. Establish `d1' : HasDerivAt (fun t : ℝ => T ⟨Dw σ l u, hkf _ k1⟩ (x * atTau θ V τ (P⁻¹ * (y * NormedSpace.exp (t • X)) * P))) (F (X :: l) y) 0`. Use `d1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)` and prove the remaining obligations.

Use `show _ = F l _`. Rewrite using `[ih hl' _ (mul_mem_UJ hy (exp_mem_UJ hX t)), eTh _ (hkf _ k1)]`. Rewrite using `[d1'.unique d2, eTh _ (hkf _ k2)]`. Take `⟨Pr, hPr⟩ : ∃ Pr : H → Prop, ∀ w, Pr w ↔ ∀ l : List (Mx V.rank), (∀ X ∈ l, X ∈ lieSet ε) → ∃ C : ℝ, ∀ y ∈ UJset ε, ‖Th (Dw σ l w) (x * atTau θ V τ (P⁻¹ * y * P))‖ ≤ C * (1 + hs y) ^ N` from `⟨_, fun _ => Iff.rfl⟩`. Establish `hSm : ∀ w, IsKFin ε σ w → Sm ε σ w` using `hstd.2.2.1`.

Choose the witnesses or unpack the hypotheses as in `⟨W, hW⟩ : ∃ W : Submodule ℂ H, ∀ w, w ∈ W ↔ IsKFin ε σ w ∧ Pr w := by`. Use `⟨{ carrier := {w | IsKFin ε σ w ∧ Pr w}, add_mem' := ?_, zero_mem' := ?_, smul_mem' := ?_ }, fun _ => Iff.rfl⟩` and prove the remaining obligations. Introduce and unpack `a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩`. Use `⟨mem_kfin.1 ((kfin ε σ).add_mem (mem_kfin.2 ha1) (mem_kfin.2 hb1)), (hPr _).2 fun l hl => ?_⟩` and prove the remaining obligations. Take `⟨C1, h1⟩` from `(hPr a).1 ha2 l hl`.

Take `⟨C2, h2⟩` from `(hPr b).1 hb2 l hl`. Use `⟨C1 + C2, fun y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[Dw_add hstd.1 hl (hSm _ ha1) (hSm _ hb1), map_add, Pi.add_apply, add_mul]`. Conclude with `(norm_add_le _ _).trans (add_le_add (h1 y hy) (h2 y hy))`. Establish `h0 : IsKFin ε σ (0 : H)` using `mem_kfin.1 (kfin ε σ).zero_mem`.

Use `⟨h0, (hPr _).2 fun l hl => ⟨0, fun y hy => ?_⟩⟩` and prove the remaining obligations. Establish `e` using `Dw_smul hstd.1 hl (0 : ℂ) (hSm _ h0)`. Rewrite `e` using `[zero_smul, zero_smul]`. Rewrite using `[e, map_zero]`. Simplify using the standard rewrite rules.

Introduce and unpack `c a ⟨ha1, ha2⟩`. Use `⟨mem_kfin.1 ((kfin ε σ).smul_mem c (mem_kfin.2 ha1)), (hPr _).2 fun l hl => ?_⟩` and prove the remaining obligations. Take `⟨C, h1⟩` from `(hPr a).1 ha2 l hl`. Use `⟨‖c‖ * C, fun y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[Dw_smul hstd.1 hl c (hSm _ ha1), map_smul, Pi.smul_apply, smul_eq_mul, norm_mul]`.

Conclude with `(mul_le_mul_of_nonneg_left (h1 y hy) (norm_nonneg c)).trans_eq (by ring)`. Establish `hWk : ∀ w ∈ W, IsKFin ε σ w` using `fun w hw => ((hW w).1 hw).1`. Establish `hWX : ∀ X, inG ε X → ∀ w ∈ W, dRep σ X w ∈ W`. Introduce `X hXg w hw`. Take `⟨hw1, hw2⟩` from `(hW w).1 hw`.

Establish `hXl : X ∈ lieSet ε` using `hXg`. Use `(hW _).2 ⟨isKFin_dRep _ ε H σ hstd w hw1 X hXl, (hPr _).2 fun l hl => ?_⟩` and prove the remaining obligations. Take `⟨C, hC⟩` from `(hPr w).1 hw2 (l ++ [X]) (by`. Introduce `Y hY`. Break down `List.mem_append.1 hY with h | h` into its components or cases.

Conclude with `hl Y h`. Rewrite `h` using `[List.mem_singleton]`. Rewrite using `[h]`. Conclude with `hXl)`. Use `⟨C, fun y hy => ?_⟩` and prove the remaining obligations.

Establish `e : Dw σ l (dRep σ X w) = Dw σ (l ++ [X]) w` using `by rw [Dw_append]; rfl`. Rewrite using `[e]`. Conclude with `hC y hy`. Establish `hWK : ∀ k ∈ Kset ε, ∀ w ∈ W, σ k w ∈ W`. Introduce `k hk w hw`.

Take `⟨hw1, hw2⟩` from `(hW w).1 hw`. Establish `hkU` using `K_le_UJ hk`. Use `(hW _).2 ⟨isKFin_translate hw1 hk, (hPr _).2 fun l hl => ?_⟩` and prove the remaining obligations. Establish `hl' : ∀ X ∈ l.map (fun X => k⁻¹ * X * k), X ∈ lieSet ε`. Introduce `X hX`.

Take `⟨Y, hY, rfl⟩` from `List.mem_map.1 hX`. Conclude with `conj_mem_lie (isUnit_Jm ε) hkU (hl Y hY)`. Take `⟨C, hC⟩` from `(hPr w).1 hw2 _ hl'`. Establish `hv'` using `hDw _ hl' w hw1`. Use `⟨|C| * (1 + hs k) ^ N, fun y hy => ?_⟩` and prove the remaining obligations.

Rewrite using `[Dw_translate hstd.1 hkU (hSm _ hw1) hl, eTh _ (hkf _ (isKFin_translate hv' hk)), map_K hθ hP hPG hT hk ⟨_, hkf _ hv'⟩ _ rfl x hy, ← eTh _ (hkf _ hv')]`. Use `(hC (y * k) (mul_mem_UJ hy hkU)).trans ?_` and prove the remaining obligations. Establish `hp : (1 + hs (y * k)) ^ N ≤ (1 + hs y) ^ N * (1 + hs k) ^ N`. Rewrite using `[← mul_pow]`. Conclude with `pow_le_pow_left₀ (by linarith [hs_nonneg (y * k)]) (one_add_hs_mul_le y k) N`.

Combine the equalities or inequalities in the displayed calculation. Establish `huW : u ∈ W` using `(hW u).2 ⟨hu, (hPr u).2 fun l hl => by`. Take `⟨C, hC⟩` from `hFg l hl`. Conclude with `⟨C, fun y hy => by rw [← hFeq l hl y hy]; exact hC y hy⟩⟩`. Establish `hW0 : W ≠ ⊥` using `fun hb => hu0 ((Submodule.mem_bot ℂ).1 (hb ▸ huW))`.

Establish `hd` using `GlobalTheory.HCModIrred.dense_of_stable hHC hstd.1 hstd.2.1 hWk hWX hWK hW0`. Use `⟨N, fun w => ?_⟩` and prove the remaining obligations. Establish `hmem` using `GlobalTheory.HCModIrred.mem_of_dense hstd hd hWk hWK (mem_kFin_iff.1 w.2)`. Take `⟨C, hC⟩` from `(hPr _).1 ((hW _).1 hmem).2 [] (by simp)`. Use `⟨C, fun y hy => ?_⟩` and prove the remaining obligations.

Use `hC y hy` as an intermediate fact. Rewrite `this` using `[show Dw σ [] (w : H) = w from rfl, eTh _ w.2]`. Then use the resulting hypothesis.
-/
theorem exists_growth_exponent : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (τ : D.what₂.Tau), IsInfFam (D := D) θ → GlobalTheory.Published.HarishChandraModules →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (σ : Matrix (Fin V.rank) (Fin V.rank) ℂ → (H →L[ℂ] H)) (lam : Fin V.rank → ℝ) (ε : Fin V.rank → Bool)
      (P : Matrix (Fin V.rank) (Fin V.rank) ℂ) (T : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ →ₗ[ℂ] (GA D V → ℂ)),
    IsDS ε lam σ → IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = gramAt D V τ →
    GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.IsGKMap θ V τ ε σ P T → ∀ x : GA D V, ∃ N : ℕ, ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ, ∃ C : ℝ,
      ∀ y ∈ UJset ε, ‖T w (x * atTau θ V τ (P⁻¹ * y * P))‖ ≤ C * (1 + Formalism.REAL.hs y) ^ N := by
  intro D θ V τ hθ hHC H _ _ σ lam ε P T hDS hP hPG hT x
  haveI : CompleteSpace H := hDS.1
  have hstd : Std ε σ := std_of_isDS hHC hDS
  obtain ⟨Th, hTh⟩ := LinearMap.exists_extend T
  have eTh : ∀ v (hv : v ∈ GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ), Th v = T ⟨v, hv⟩ := fun v hv => LinearMap.congr_fun hTh ⟨v, hv⟩
  have hkf : ∀ v, IsKFin ε σ v → v ∈ GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ := fun v hv => mem_kFin_iff.2 hv
  have hDw : ∀ l : List (Mx V.rank), (∀ X ∈ l, X ∈ lieSet ε) → ∀ v, IsKFin ε σ v → IsKFin ε σ (Dw σ l v) := by
    intro l hl v hv
    induction l with
    | nil => exact hv
    | cons X l ih =>
      exact isKFin_dRep _ ε H σ hstd _ (ih fun Y hY => hl Y (List.mem_cons_of_mem _ hY)) X (hl X List.mem_cons_self)
  obtain ⟨u, hu, hu0⟩ := hstd.2.2.2.2
  obtain ⟨N, F, hF0, hFd, hFg⟩ := umg_atTau D θ hθ V τ (T ⟨u, hkf u hu⟩) (hT.aut _) ε P hP hPG x
  have hFeq : ∀ l : List (Mx V.rank), (∀ X ∈ l, X ∈ lieSet ε) → ∀ y ∈ UJset ε,
      F l y = Th (Dw σ l u) (x * atTau θ V τ (P⁻¹ * y * P)) := by
    intro l hl
    induction l with
    | nil => intro y hy; rw [hF0 y hy]; exact (congrFun (eTh u (hkf u hu)) _).symm
    | cons X l ih =>
      intro y hy
      have hl' : ∀ Y ∈ l, Y ∈ lieSet ε := fun Y hY => hl Y (List.mem_cons_of_mem _ hY)
      have hX := hl X List.mem_cons_self
      have k1 := hDw l hl' u hu
      have k2 := hDw (X :: l) hl u hu
      have d1 := hFd l hl' X hX y hy
      have d2 := hasDerivAt_map hθ hP hPG hT ⟨Dw σ l u, hkf _ k1⟩ ⟨Dw σ (X :: l) u, hkf _ k2⟩ hX
        (hstd.2.2.1 _ k1) rfl x hy
      have d1' : HasDerivAt (fun t : ℝ => T ⟨Dw σ l u, hkf _ k1⟩
          (x * atTau θ V τ (P⁻¹ * (y * NormedSpace.exp (t • X)) * P))) (F (X :: l) y) 0 := by
        refine d1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
        show _ = F l _
        rw [ih hl' _ (mul_mem_UJ hy (exp_mem_UJ hX t)), eTh _ (hkf _ k1)]
      rw [d1'.unique d2, eTh _ (hkf _ k2)]
  obtain ⟨Pr, hPr⟩ : ∃ Pr : H → Prop, ∀ w, Pr w ↔ ∀ l : List (Mx V.rank), (∀ X ∈ l, X ∈ lieSet ε) →
      ∃ C : ℝ, ∀ y ∈ UJset ε, ‖Th (Dw σ l w) (x * atTau θ V τ (P⁻¹ * y * P))‖ ≤ C * (1 + hs y) ^ N :=
    ⟨_, fun _ => Iff.rfl⟩
  have hSm : ∀ w, IsKFin ε σ w → Sm ε σ w := hstd.2.2.1
  obtain ⟨W, hW⟩ : ∃ W : Submodule ℂ H, ∀ w, w ∈ W ↔ IsKFin ε σ w ∧ Pr w := by
    refine ⟨{ carrier := {w | IsKFin ε σ w ∧ Pr w}, add_mem' := ?_, zero_mem' := ?_, smul_mem' := ?_ },
      fun _ => Iff.rfl⟩
    · rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
      refine ⟨mem_kfin.1 ((kfin ε σ).add_mem (mem_kfin.2 ha1) (mem_kfin.2 hb1)), (hPr _).2 fun l hl => ?_⟩
      obtain ⟨C1, h1⟩ := (hPr a).1 ha2 l hl
      obtain ⟨C2, h2⟩ := (hPr b).1 hb2 l hl
      refine ⟨C1 + C2, fun y hy => ?_⟩
      rw [Dw_add hstd.1 hl (hSm _ ha1) (hSm _ hb1), map_add, Pi.add_apply, add_mul]
      exact (norm_add_le _ _).trans (add_le_add (h1 y hy) (h2 y hy))
    · have h0 : IsKFin ε σ (0 : H) := mem_kfin.1 (kfin ε σ).zero_mem
      refine ⟨h0, (hPr _).2 fun l hl => ⟨0, fun y hy => ?_⟩⟩
      have e := Dw_smul hstd.1 hl (0 : ℂ) (hSm _ h0)
      rw [zero_smul, zero_smul] at e
      rw [e, map_zero]
      simp
    · rintro c a ⟨ha1, ha2⟩
      refine ⟨mem_kfin.1 ((kfin ε σ).smul_mem c (mem_kfin.2 ha1)), (hPr _).2 fun l hl => ?_⟩
      obtain ⟨C, h1⟩ := (hPr a).1 ha2 l hl
      refine ⟨‖c‖ * C, fun y hy => ?_⟩
      rw [Dw_smul hstd.1 hl c (hSm _ ha1), map_smul, Pi.smul_apply, smul_eq_mul, norm_mul]
      exact (mul_le_mul_of_nonneg_left (h1 y hy) (norm_nonneg c)).trans_eq (by ring)
  have hWk : ∀ w ∈ W, IsKFin ε σ w := fun w hw => ((hW w).1 hw).1
  have hWX : ∀ X, inG ε X → ∀ w ∈ W, dRep σ X w ∈ W := by
    intro X hXg w hw
    obtain ⟨hw1, hw2⟩ := (hW w).1 hw
    have hXl : X ∈ lieSet ε := hXg
    refine (hW _).2 ⟨isKFin_dRep _ ε H σ hstd w hw1 X hXl, (hPr _).2 fun l hl => ?_⟩
    obtain ⟨C, hC⟩ := (hPr w).1 hw2 (l ++ [X]) (by
      intro Y hY
      rcases List.mem_append.1 hY with h | h
      · exact hl Y h
      · rw [List.mem_singleton] at h; rw [h]; exact hXl)
    refine ⟨C, fun y hy => ?_⟩
    have e : Dw σ l (dRep σ X w) = Dw σ (l ++ [X]) w := by rw [Dw_append]; rfl
    rw [e]
    exact hC y hy
  have hWK : ∀ k ∈ Kset ε, ∀ w ∈ W, σ k w ∈ W := by
    intro k hk w hw
    obtain ⟨hw1, hw2⟩ := (hW w).1 hw
    have hkU := K_le_UJ hk
    refine (hW _).2 ⟨isKFin_translate hw1 hk, (hPr _).2 fun l hl => ?_⟩
    have hl' : ∀ X ∈ l.map (fun X => k⁻¹ * X * k), X ∈ lieSet ε := by
      intro X hX
      obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
      exact conj_mem_lie (isUnit_Jm ε) hkU (hl Y hY)
    obtain ⟨C, hC⟩ := (hPr w).1 hw2 _ hl'
    have hv' := hDw _ hl' w hw1
    refine ⟨|C| * (1 + hs k) ^ N, fun y hy => ?_⟩
    rw [Dw_translate hstd.1 hkU (hSm _ hw1) hl, eTh _ (hkf _ (isKFin_translate hv' hk)),
      map_K hθ hP hPG hT hk ⟨_, hkf _ hv'⟩ _ rfl x hy, ← eTh _ (hkf _ hv')]
    refine (hC (y * k) (mul_mem_UJ hy hkU)).trans ?_
    have hp : (1 + hs (y * k)) ^ N ≤ (1 + hs y) ^ N * (1 + hs k) ^ N := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by linarith [hs_nonneg (y * k)]) (one_add_hs_mul_le y k) N
    calc C * (1 + hs (y * k)) ^ N ≤ |C| * (1 + hs (y * k)) ^ N :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg (by linarith [hs_nonneg (y * k)]) _)
      _ ≤ |C| * ((1 + hs y) ^ N * (1 + hs k) ^ N) := mul_le_mul_of_nonneg_left hp (abs_nonneg C)
      _ = |C| * (1 + hs k) ^ N * (1 + hs y) ^ N := by ring
  have huW : u ∈ W := (hW u).2 ⟨hu, (hPr u).2 fun l hl => by
    obtain ⟨C, hC⟩ := hFg l hl
    exact ⟨C, fun y hy => by rw [← hFeq l hl y hy]; exact hC y hy⟩⟩
  have hW0 : W ≠ ⊥ := fun hb => hu0 ((Submodule.mem_bot ℂ).1 (hb ▸ huW))
  have hd := GlobalTheory.HCModIrred.dense_of_stable hHC hstd.1 hstd.2.1 hWk hWX hWK hW0
  refine ⟨N, fun w => ?_⟩
  have hmem := GlobalTheory.HCModIrred.mem_of_dense hstd hd hWk hWK (mem_kFin_iff.1 w.2)
  obtain ⟨C, hC⟩ := (hPr _).1 ((hW _).1 hmem).2 [] (by simp)
  refine ⟨C, fun y hy => ?_⟩
  have := hC y hy
  rwa [show Dw σ [] (w : H) = w from rfl, eTh _ w.2] at this

end GlobalTheory.TypeSum.GKCoef

end
