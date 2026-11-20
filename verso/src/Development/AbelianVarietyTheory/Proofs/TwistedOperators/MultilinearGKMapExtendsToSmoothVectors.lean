import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.KTypeExtension
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemKFinOfMemLowT
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSmoothCuspFormFrechetModerateGrowthRepStatement
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SobolevFormEqZeroOnSmoothOfKFiniteDiscreteSeriesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsKFinDRep
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SobBdSeminorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMultilinearSlotwiseExtensionOfEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BilinearBoundOfDenseSecondSlotStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemClosureOfForallDualVanishStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSmoothVectorsDiscreteSeriesModelIffStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SobolevContinuousModelRepOfSobolevBoundStatement
open Classical Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FactorExtension

open GlobalTheory.SmoothGlob

variable {E : Type} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E] [T2Space E]

/- English proof (translation)
Rewrite using `[Seminorm.coe_smul]`. Conclude with `hq.const_smul c`.
-/
theorem smul_seminorm_cont {q : Seminorm ℂ E} (hq : Continuous q) (c : NNReal) : Continuous (c • q) := by
  rw [Seminorm.coe_smul]
  exact hq.const_smul c

/- English proof (translation)
Take `⟨S, C, hS, hb⟩` from `hL i`. Take `⟨q, hq, hqb⟩` from `hN S hS`. Use `⟨Real.toNNReal |C| • q, smul_seminorm_cont hq _, fun w hw => ?_⟩` and prove the remaining obligations. Rewrite using `[Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (abs_nonneg C)]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem bound_via {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {p : ℕ → Seminorm ℂ E} {N L : H →ₗ[ℂ] E}
    (hN : ∀ S : List (List (Matrix (Fin n) (Fin n) ℂ)), (∀ l ∈ S, ∀ X ∈ l, X ∈ lieSet ε) →
      ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ w, SmoothVec (lieSet ε) σ w → sobNorm σ S w ≤ q (N w))
    (hL : L ∈ sobBd ε σ p) (i : ℕ) :
    ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ w, SmoothVec (lieSet ε) σ w → p i (L w) ≤ q (N w) := by
  obtain ⟨S, C, hS, hb⟩ := hL i
  obtain ⟨q, hq, hqb⟩ := hN S hS
  refine ⟨Real.toNNReal |C| • q, smul_seminorm_cont hq _, fun w hw => ?_⟩
  rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (abs_nonneg C)]
  calc p i (L w) ≤ C * sobNorm σ S w := hb w hw
    _ ≤ |C| * sobNorm σ S w := mul_le_mul_of_nonneg_right (le_abs_self C) (sobNorm_nonneg σ S w)
    _ ≤ |C| * q (N w) := mul_le_mul_of_nonneg_left (hqb w hw) (abs_nonneg C)

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

/- English proof (translation)
Establish `hq : Continuous ((normSeminorm ℂ ℂ).comp (f : E →ₗ[ℂ] ℂ))` using `continuous_norm.comp f.continuous`. Take `⟨Sl, C, hS, hb⟩` from `sobBd_seminorm hp hL _ hq`. Establish `hsc` using `GlobalTheory.T.sobolevContinuous_modelRep_of_sobolevBound M τ ((f : E →ₗ[ℂ] ℂ) ∘ₗ L) Sl C hS (fun w hw => by simpa using hb w hw)`. Conclude with `GlobalTheory.T.sobolevForm_eq_zero_on_smooth_of_kFinite_discreteSeries hHC D V S M τ _ hsc h0`.
-/
theorem form_zero (hHC : GlobalTheory.Published.HarishChandraModules) (M : DSModel V S) (τ : D.what₂.Tau) {p : ℕ → Seminorm ℂ E}
    (hp : WithSeminorms p) {L : M.H τ →ₗ[ℂ] E} (hL : L ∈ sobBd (M.ε τ) (M.σ τ) p) (f : E →L[ℂ] ℂ)
    (h0 : ∀ a ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, f (L a) = 0) : ∀ w ∈ M.sm τ, f (L w) = 0 := by
  have hq : Continuous ((normSeminorm ℂ ℂ).comp (f : E →ₗ[ℂ] ℂ)) := continuous_norm.comp f.continuous
  obtain ⟨Sl, C, hS, hb⟩ := sobBd_seminorm hp hL _ hq
  have hsc := GlobalTheory.T.sobolevContinuous_modelRep_of_sobolevBound M τ ((f : E →ₗ[ℂ] ℂ) ∘ₗ L) Sl C hS (fun w hw => by simpa using hb w hw)
  exact GlobalTheory.T.sobolevForm_eq_zero_on_smooth_of_kFinite_discreteSeries hHC D V S M τ _ hsc h0

/- English proof (translation)
Introduce `w hw`. Establish `h` using `GlobalTheory.T.mem_closure_of_forall_clm_vanish hp ⊥ (L w) fun f _ => form_zero hHC M τ hp hL f (fun a ha => by rw [h0 a ha, map_zero]) w hw`. Rewrite `h` using `[Submodule.bot_coe, closure_singleton]`. Conclude with `h`.
-/
theorem uniq (hHC : GlobalTheory.Published.HarishChandraModules) (M : DSModel V S) (τ : D.what₂.Tau) {p : ℕ → Seminorm ℂ E}
    (hp : WithSeminorms p) {L : M.H τ →ₗ[ℂ] E} (hL : L ∈ sobBd (M.ε τ) (M.σ τ) p)
    (h0 : ∀ a ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, L a = 0) : ∀ w ∈ M.sm τ, L w = 0 := by
  intro w hw
  have h := GlobalTheory.T.mem_closure_of_forall_clm_vanish hp ⊥ (L w) fun f _ => form_zero hHC M τ hp hL f (fun a ha => by rw [h0 a ha, map_zero]) w hw
  rw [Submodule.bot_coe, closure_singleton] at h
  exact h

end GlobalTheory.FactorExtension

namespace GlobalTheory.FactorExtension

open GlobalTheory.SmoothGlob

/- English proof (translation)
Introduce `hHC hCW D V S M E _ _ _ _ _ _ p π dπ hπ hcomm T₀ hK hL`. Use `haveI hc : ∀ τ, CompleteSpace (M.H τ) := fun τ => (M.ds τ).1`. Establish `hsm : ∀ τ w, w ∈ M.sm τ ↔ SmoothVec (lieSet (M.ε τ)) (M.σ τ) w` using `fun τ w => GlobalTheory.T.mem_smoothVectors_discreteSeriesModel_iff M τ w`. Establish `hstd : ∀ τ, GlobalTheory.TypeSum.Std (M.ε τ) (M.σ τ)` using `fun τ => GlobalTheory.TypeSum.std_of_isDS hHC (M.ds τ)`. Establish `hAB : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ ≤ M.sm τ` using `fun τ v hv => (hsm τ v).2 ((hstd τ).2.2.1 v hv)`.

Establish `hPex : ∀ τ, ∃ P : M.H τ →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, ∀ x : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, P x = x`. Introduce `τ`. Take `⟨P, hP⟩` from `LinearMap.exists_leftInverse_of_injective (GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ).subtype (Submodule.ker_subtype _)`. Conclude with `⟨P, fun x => LinearMap.congr_fun hP x⟩`. Use `choose P hP using hPex`.

Establish `hP' : ∀ τ (x : M.H τ) (hx : x ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ), P τ x = ⟨x, hx⟩` using `fun τ x hx => hP τ ⟨x, hx⟩`. Set `T₀' : MultilinearMap ℂ (fun τ => M.H τ) E` to `T₀.compLinearMap P`. Set `Rk : ∀ τ, Set ((M.H τ → M.H τ) × (E →ₗ[ℂ] E))` to `fun τ => {r | (∃ k ∈ Formalism.REAL.Kset (M.ε τ), r = (⇑(M.σ τ k), (π τ k : E →ₗ[ℂ] E))) ∨ ∃ X ∈ lieSet (M.ε τ), r = (dRep (M.σ τ) X, (dπ τ X : E →ₗ[ℂ] E))}`. Set `Rg : ∀ τ, Set ((M.H τ → M.H τ) × (E →ₗ[ℂ] E))` to `fun τ => {r | ∃ g ∈ Formalism.MainNotions.S.UJset (M.ε τ), r = (⇑(M.σ τ g), (π τ g : E →ₗ[ℂ] E))}`. Establish `hRk : ∀ τ, ∀ r ∈ Rk τ, ∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, r.1 x ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ`.

Introduce and unpack `τ r (⟨k, hk, rfl⟩ | ⟨X, hX, rfl⟩) x hx`. Take `⟨A, hA, ha, hs⟩` from `hx`. Conclude with `⟨A, hA, hs k hk x ha, hs⟩`. Conclude with `GlobalTheory.TypeSum.isKFin_dRep _ _ _ (M.σ τ) (hstd τ) x hx X hX`. Establish `hRg : ∀ τ, ∀ r ∈ Rg τ, ∀ x ∈ M.sm τ, r.1 x ∈ M.sm τ`.

Introduce and unpack `τ r ⟨g, hg, rfl⟩ x hx`. Rewrite `hx`, the goal using `[GlobalTheory.SmVec.sm_eq]`. Conclude with `GlobalTheory.SmVec.sigma_mem (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1 hx hg`. Set `C : ∀ τ, Submodule ℂ (M.H τ →ₗ[ℂ] E)` to `fun τ => sobBd (M.ε τ) (M.σ τ) p`. Establish `hC : ∀ τ, ∀ L ∈ C τ, ∀ L' : M.H τ →ₗ[ℂ] E, (∀ x ∈ M.sm τ, L' x = L x) → L' ∈ C τ` using `fun τ L hL L' h => sobBd_congr hL fun w hw => h w ((hsm τ w).2 hw)`.

Establish `hcw : ∀ τ (L : M.H τ →ₗ[ℂ] E), (∀ r ∈ Rk τ, ∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, L (r.1 x) = r.2 (L x)) → ∃ T : M.H τ →ₗ[ℂ] E, (∀ v, Formalism.MainNotions.S.IsKFin (M.ε τ) (M.σ τ) v → T v = L v) ∧ IsSmoothGMap (M.ε τ) (M.σ τ) p (π τ) T ∧ IsClosed …`. Introduce `τ L hLk`. Establish `hGK : IsGKMap (M.ε τ) (M.σ τ) (π τ) (dπ τ) L` using `⟨fun k hk v hv => hLk _ (Or.inl ⟨k, hk, rfl⟩) v hv, fun X hX v hv => hLk _ (Or.inr ⟨X, hX, rfl⟩) v hv⟩`. Take `⟨T, hT1, hT2, -, hT4, hT5⟩` from `hCW V.rank (M.ε τ) (M.H τ) (M.σ τ) (M.ds τ).2.2.1 (M.ds τ).2.2.2.1 E p (π τ) (dπ τ) (hπ τ) L hGK`. Conclude with `⟨T, hT1, hT2, hT4, hT5⟩`.

Establish `hext : ∀ τ (L : M.H τ →ₗ[ℂ] E), (∀ r ∈ Rk τ, ∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, L (r.1 x) = r.2 (L x)) → ∃ L' ∈ C τ, (∀ r ∈ Rg τ, ∀ x ∈ M.sm τ, L' (r.1 x) = r.2 (L' x)) ∧ ∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, L' …`. Introduce `τ L hLk`. Take `⟨T, hT1, ⟨hT2, hT3⟩, -⟩` from `hcw τ L hLk`. Use `⟨T, hT3, ?_, fun x hx => hT1 x hx⟩` and prove the remaining obligations. Introduce and unpack `r ⟨g, hg, rfl⟩ x hx`.

Conclude with `hT2 g hg x ((hsm τ x).1 hx)`. Establish `huniq : ∀ τ, ∀ L ∈ C τ, (∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, L x = 0) → ∀ x ∈ M.sm τ, L x = 0` using `fun τ L hL h0 => uniq hHC M τ (hπ τ).withSeminorms hL h0`. Establish `hpostC : ∀ τ τ', τ ≠ τ' → ∀ r ∈ Rk τ ∪ Rg τ, ∀ L ∈ C τ', r.2 ∘ₗ L ∈ C τ'`. Introduce and unpack `τ τ' - r ((⟨k, -, rfl⟩ | ⟨X, -, rfl⟩) | ⟨g, -, rfl⟩) L hL`. Conclude with `sobBd_comp (hπ τ').withSeminorms hL (π τ k)`.

Conclude with `sobBd_comp (hπ τ').withSeminorms hL (dπ τ X)`. Conclude with `sobBd_comp (hπ τ').withSeminorms hL (π τ g)`. Establish `hcomm' : ∀ τ τ', τ ≠ τ' → ∀ r ∈ Rk τ ∪ Rg τ, ∀ r' ∈ Rg τ', r.2 ∘ₗ r'.2 = r'.2 ∘ₗ r.2`. Introduce and unpack `τ τ' hne r ((⟨k, hk, rfl⟩ | ⟨X, hX, rfl⟩) | ⟨g, hg, rfl⟩) r' ⟨g', hg', rfl⟩`. Establish `h` using `hcomm τ τ' hne k (GlobalTheory.TypeSum.K_le_UJ hk) g' hg'`.

Use extensionality with `x`. Conclude with `congrArg (fun f : E →L[ℂ] E => f x) h`. Establish `h` using `dRep_comm (hπ τ) hX (π τ' g') fun t => hcomm τ' τ hne.symm g' hg' _ (GlobalTheory.TypeSum.exp_mem_UJ hX t)`. Use extensionality with `x`. Conclude with `(congrArg (fun f : E →L[ℂ] E => f x) h).symm`.

Establish `h` using `hcomm τ τ' hne g hg g' hg'`. Use extensionality with `x`. Conclude with `congrArg (fun f : E →L[ℂ] E => f x) h`. Establish `h0 : ∀ τ (u : ∀ τ, M.H τ), (∀ τ', τ' ≠ τ → u τ' ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ') → ∀ r ∈ Rk τ, ∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, T₀' (Function.update u τ (r.1 x)) = r.2 (T₀' (Function.update u τ x))`. Introduce `τ u _ r hr x hx`.

Establish `e : ∀ y : M.H τ, T₀' (Function.update u τ y) = T₀ (Function.update (fun τ' => P τ' (u τ')) τ (P τ y))` using `fun y => by show T₀ (fun τ' => P τ' (Function.update u τ y τ')) = _`. Use `congr 1`. Use function extensionality and compare the values at `τ'`. Conclude with `Function.apply_update (fun τ => P τ) u τ y τ'`. Establish `hr'` using `hRk τ r hr x hx`.

Rewrite using `[e, e]`. Break down `hr with ⟨k, hk, rfl⟩ | ⟨X, hX, rfl⟩` into its components or cases. Establish `h` using `hK τ k hk (Function.update (fun τ' => P τ' (u τ')) τ (P τ x)) (P τ (M.σ τ k x)) (by rw [Function.update_self, hP' τ _ hx, hP' τ _ hr'])`. Rewrite `h` using `[Function.update_idem]`. Conclude with `h`.

Establish `h` using `hL τ X hX (Function.update (fun τ' => P τ' (u τ')) τ (P τ x)) (P τ (dRep (M.σ τ) X x)) (by rw [Function.update_self, hP' τ _ hx, hP' τ _ hr'])`. Rewrite `h` using `[Function.update_idem]`. Conclude with `h`. Distinguish the cases in `hz : ∀ u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M, T₀ u = 0`. Use `⟨0, fun v u _ => (hz u).symm, fun τ g _ v w _ => by simp, fun τ i v => ⟨[], 0, by simp, fun w => by simp⟩⟩` and prove the remaining obligations.

Use `push_neg at hz`. Take `⟨u₀, hu₀⟩` from `hz`. Establish `hNZ : ∀ τ, ∃ N : M.H τ →ₗ[ℂ] E, N ∈ C τ ∧ IsClosed (N '' {w | SmoothVec (lieSet (M.ε τ)) (M.σ τ) w}) ∧ ∀ Sl : List (List (Matrix (Fin V.rank) (Fin V.rank) ℂ)), (∀ l ∈ Sl, ∀ X ∈ l, X ∈ lieSet (M.ε τ)) → ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ w, SmoothVec (lieSet (M.ε τ)) (M.σ τ) w → …`. Introduce `τ`. Set `u : ∀ τ, M.H τ` to `fun τ => (u₀ τ : M.H τ)`.

Establish `hLk : ∀ r ∈ Rk τ, ∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, T₀'.toLinearMap u τ (r.1 x) = r.2 (T₀'.toLinearMap u τ x)` using `fun r hr x hx => by`. Simplify using `only [MultilinearMap.toLinearMap_apply]`. Conclude with `h0 τ u (fun τ' _ => (u₀ τ').2) r hr x hx`. Take `⟨T, hT1, ⟨-, hT3⟩, hT4, hT5⟩` from `hcw τ _ hLk`. Use `⟨T, hT3, hT4, hT5 ⟨u τ, (u₀ τ).2, ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[MultilinearMap.toLinearMap_apply, Function.update_eq_self]`. Use `show T₀ (fun τ' => P τ' (u₀ τ' : M.H τ')) ≠ 0`. Establish `: (fun τ' => P τ' (u₀ τ' : M.H τ')) = u₀` using `funext fun τ' => hP τ' (u₀ τ')`. Rewrite using `[this]`. Conclude with `hu₀`.

Establish `hbs : ∀ τ τ', τ ≠ τ' → ∀ F : M.H τ →ₗ[ℂ] M.H τ' →ₗ[ℂ] E, (∀ w ∈ M.sm τ, F w ∈ C τ') → (∀ a ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ', F.flip a ∈ C τ) → ∀ b ∈ M.sm τ', F.flip b ∈ C τ`. Introduce `τ τ' _ F hF1 hF2 b hb`. Take `⟨N₁, hN₁C, hN₁cl, hN₁iso⟩` from `hNZ τ`. Take `⟨N₂, hN₂C, -, hN₂iso⟩` from `hNZ τ'`. Establish `hp` using `(hπ τ).withSeminorms`.

Set `j₁ : M.sm τ →ₗ[ℂ] E` to `N₁ ∘ₗ (M.sm τ).subtype`. Set `j₂ : M.sm τ' →ₗ[ℂ] E` to `N₂ ∘ₗ (M.sm τ').subtype`. Establish `hinj : Function.Injective j₁`. Use `(injective_iff_map_eq_zero j₁).2 fun x hx => ?_` and prove the remaining obligations. Take `⟨q, -, hq⟩` from `hN₁iso [[]] (by simp)`.

Establish `h1` using `hq x ((hsm τ x).1 x.2)`. Establish `h2 : j₁ x = N₁ x` using `rfl`. Rewrite `h1` using `[← h2, hx, map_zero]`. Establish `h3 : sobNorm (M.σ τ) [[]] (x : M.H τ) = ‖(x : M.H τ)‖` using `by simp [sobNorm]`. Rewrite `h1` using `[h3]`.

Conclude with `Subtype.ext (norm_le_zero_iff.1 h1)`. Establish `hcl : IsClosed (Set.range j₁)`. Establish `e : Set.range j₁ = N₁ '' {w | SmoothVec (lieSet (M.ε τ)) (M.σ τ) w}`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨x, rfl⟩`. Conclude with `⟨x, (hsm τ x).1 x.2, rfl⟩`. Introduce and unpack `⟨w, hw, rfl⟩`. Conclude with `⟨⟨w, (hsm τ w).2 hw⟩, rfl⟩`. Rewrite using `[e]`.

Conclude with `hN₁cl`. Set `D₂ : Submodule ℂ (M.sm τ')` to `(GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ').comap (M.sm τ').subtype`. Establish `hD : ∀ x, j₂ x ∈ closure (j₂ '' (D₂ : Set (M.sm τ')))`. Introduce `x`. Establish `h` using `GlobalTheory.T.mem_closure_of_forall_clm_vanish (hπ τ').withSeminorms (D₂.map j₂) (j₂ x) fun f hf => form_zero hHC M τ' (hπ τ').withSeminorms hN₂C f (fun a ha => hf _ ⟨⟨a, hAB τ' ha⟩, ha, rfl⟩) x x.2`.

Rewrite `h` using `[Submodule.map_coe]`. Then use the resulting hypothesis. Set `F' : M.sm τ →ₗ[ℂ] M.sm τ' →ₗ[ℂ] E` to `F.compl₁₂ (M.sm τ).subtype (M.sm τ').subtype`. Establish `h₂ : ∀ w i, ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ b, p i (F' w b) ≤ q (j₂ b)`. Introduce `w i`. Take `⟨q, hq, hb⟩` from `bound_via hN₂iso (hF1 w w.2) i`.

Conclude with `⟨q, hq, fun b => hb b ((hsm τ' b).1 b.2)⟩`. Establish `h₁ : ∀ a ∈ D₂, ∀ i, ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ w, p i (F' w a) ≤ q (j₁ w)`. Introduce `a ha i`. Take `⟨q, hq, hb⟩` from `bound_via hN₁iso (hF2 a ha) i`. Conclude with `⟨q, hq, fun w => hb w ((hsm τ w).1 w.2)⟩`.

Introduce `i`. Take `⟨q, hq, hb'⟩` from `GlobalTheory.T.exists_seminorm_bound_of_dense_second_slot hp j₁ j₂ hinj hcl D₂ hD F' h₂ h₁ ⟨b, hb⟩ i`. Take `⟨Sl, C', hS, hb''⟩` from `sobBd_seminorm hp hN₁C q hq`. Conclude with `⟨Sl, C', hS, fun w hw => (hb' ⟨w, (hsm τ w).2 hw⟩).trans (hb'' w hw)⟩`. Take `⟨Tab, hT1, hT2⟩` from `GlobalTheory.T.exists_multilinear_positionwise_extension_of_equivariant (H := fun τ => M.H τ) (fun τ => GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) (fun τ => M.sm τ) hAB Rk Rg hRk hRg C hC hext huniq hpostC hcomm' hbs T₀' h0`.

Establish `hupd : ∀ (v : M.Vec) τ (w : M.sm τ), (fun τ' => ((Function.update v τ w τ' : M.sm τ') : M.H τ')) = Function.update (fun τ' => (v τ' : M.H τ')) τ (w : M.H τ)` using `fun v τ w => funext fun τ' => Function.apply_update (fun τ => ((M.sm τ).subtype : M.sm τ → M.H τ)) v τ w τ'`. Use `⟨Tab.compLinearMap fun τ => (M.sm τ).subtype, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `v u hvu show Tab (fun τ => (v τ : M.H τ)) = T₀ u`. Establish `e : (fun τ => (v τ : M.H τ)) = fun τ => (u τ : M.H τ)` using `funext hvu`. Rewrite using `[e, hT1 _ fun τ => (u τ).2]`.

Use `show T₀ (fun τ => P τ (u τ : M.H τ)) = T₀ u`. Use `congr 1`. Use function extensionality and compare the values at `τ`. Conclude with `hP τ (u τ)`. Introduce `τ g hg v w hw show Tab (fun τ' => ((Function.update v τ w τ' : M.sm τ') : M.H τ')) = π τ g (Tab fun τ' => (v τ' : M.H τ'))`.

Rewrite using `[hupd, hw]`. Establish `h` using `(hT2 τ (fun τ' => (v τ' : M.H τ')) fun τ' _ => (v τ').2).2 _ ⟨g, hg, rfl⟩ (v τ) (v τ).2`. Rewrite `h` using `[Function.update_eq_self]`. Conclude with `h`. Introduce `τ i v`.

Take `⟨Sl, C', hS, hb⟩` from `(hT2 τ (fun τ' => (v τ' : M.H τ')) fun τ' _ => (v τ').2).1 i`. Use `⟨Sl, C', hS, fun w => ?_⟩` and prove the remaining obligations. Establish `h` using `hb w ((hsm τ w).1 w.2)`. Rewrite `h` using `[MultilinearMap.toLinearMap_apply]`. Use `show p i (Tab (fun τ' => ((Function.update v τ w τ' : M.sm τ') : M.H τ'))) ≤ _`.

Rewrite using `[hupd]`. Conclude with `h`.
-/
theorem extend_positions : GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (E : Type) [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E] [T2Space E] (p : ℕ → Seminorm ℂ E) (π dπ : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ → (E →L[ℂ] E)), (∀ τ, GlobalTheory.SmoothGlob.IsSmoothModRep (M.ε τ) p (π τ) (dπ τ)) → (∀ τ τ', τ ≠ τ' → ∀ g ∈ Formalism.MainNotions.S.UJset (M.ε τ), ∀ g' ∈ Formalism.MainNotions.S.UJset (M.ε τ'), (π τ g).comp (π τ' g') = (π τ' g').comp (π τ g)) → ∀ T₀ : MultilinearMap ℂ (fun τ : D.what₂.Tau => GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) E, (∀ τ, ∀ k ∈ Formalism.REAL.Kset (M.ε τ), ∀ (u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M) (w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ), (w : M.H τ) = M.σ τ k (u τ) → T₀ (Function.update u τ w) = π τ k (T₀ u)) → (∀ τ, ∀ X ∈ GlobalTheory.SmoothGlob.lieSet (M.ε τ), ∀ (u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M) (w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ), (w : M.H τ) = dRep (M.σ τ) X (u τ) → T₀ (Function.update u τ w) = dπ τ X (T₀ u)) → ∃ T : MultilinearMap ℂ (fun τ : D.what₂.Tau => M.sm τ) E, (∀ (v : M.Vec) (u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M), (∀ τ, (v τ : M.H τ) = u τ) → T v = T₀ u) ∧ (∀ τ, ∀ g ∈ Formalism.MainNotions.S.UJset (M.ε τ), ∀ (v : M.Vec) (w : M.sm τ), (w : M.H τ) = M.σ τ g (v τ) → T (Function.update v τ w) = π τ g (T v)) ∧ ∀ τ (i : ℕ) (v : M.Vec), ∃ (L : List (List (Matrix (Fin V.rank) (Fin V.rank) ℂ))) (C : ℝ), (∀ l ∈ L, ∀ X ∈ l, X ∈ GlobalTheory.SmoothGlob.lieSet (M.ε τ)) ∧ ∀ w : M.sm τ, p i (T (Function.update v τ w)) ≤ C * GlobalTheory.SmoothGlob.sobNorm (M.σ τ) L w := by
  intro hHC hCW D V S M E _ _ _ _ _ _ p π dπ hπ hcomm T₀ hK hL
  haveI hc : ∀ τ, CompleteSpace (M.H τ) := fun τ => (M.ds τ).1
  have hsm : ∀ τ w, w ∈ M.sm τ ↔ SmoothVec (lieSet (M.ε τ)) (M.σ τ) w := fun τ w => GlobalTheory.T.mem_smoothVectors_discreteSeriesModel_iff M τ w
  have hstd : ∀ τ, GlobalTheory.TypeSum.Std (M.ε τ) (M.σ τ) := fun τ => GlobalTheory.TypeSum.std_of_isDS hHC (M.ds τ)
  have hAB : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ ≤ M.sm τ := fun τ v hv => (hsm τ v).2 ((hstd τ).2.2.1 v hv)
  have hPex : ∀ τ, ∃ P : M.H τ →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, ∀ x : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, P x = x := by
    intro τ
    obtain ⟨P, hP⟩ := LinearMap.exists_leftInverse_of_injective (GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ).subtype
      (Submodule.ker_subtype _)
    exact ⟨P, fun x => LinearMap.congr_fun hP x⟩
  choose P hP using hPex
  have hP' : ∀ τ (x : M.H τ) (hx : x ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ), P τ x = ⟨x, hx⟩ := fun τ x hx => hP τ ⟨x, hx⟩
  let T₀' : MultilinearMap ℂ (fun τ => M.H τ) E := T₀.compLinearMap P
  let Rk : ∀ τ, Set ((M.H τ → M.H τ) × (E →ₗ[ℂ] E)) := fun τ =>
    {r | (∃ k ∈ Formalism.REAL.Kset (M.ε τ), r = (⇑(M.σ τ k), (π τ k : E →ₗ[ℂ] E))) ∨
      ∃ X ∈ lieSet (M.ε τ), r = (dRep (M.σ τ) X, (dπ τ X : E →ₗ[ℂ] E))}
  let Rg : ∀ τ, Set ((M.H τ → M.H τ) × (E →ₗ[ℂ] E)) := fun τ =>
    {r | ∃ g ∈ Formalism.MainNotions.S.UJset (M.ε τ), r = (⇑(M.σ τ g), (π τ g : E →ₗ[ℂ] E))}
  have hRk : ∀ τ, ∀ r ∈ Rk τ, ∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, r.1 x ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ := by
    rintro τ r (⟨k, hk, rfl⟩ | ⟨X, hX, rfl⟩) x hx
    · obtain ⟨A, hA, ha, hs⟩ := hx
      exact ⟨A, hA, hs k hk x ha, hs⟩
    · exact GlobalTheory.TypeSum.isKFin_dRep _ _ _ (M.σ τ) (hstd τ) x hx X hX
  have hRg : ∀ τ, ∀ r ∈ Rg τ, ∀ x ∈ M.sm τ, r.1 x ∈ M.sm τ := by
    rintro τ r ⟨g, hg, rfl⟩ x hx
    rw [GlobalTheory.SmVec.sm_eq] at hx ⊢
    exact GlobalTheory.SmVec.sigma_mem (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1 hx hg
  let C : ∀ τ, Submodule ℂ (M.H τ →ₗ[ℂ] E) := fun τ => sobBd (M.ε τ) (M.σ τ) p
  have hC : ∀ τ, ∀ L ∈ C τ, ∀ L' : M.H τ →ₗ[ℂ] E, (∀ x ∈ M.sm τ, L' x = L x) → L' ∈ C τ :=
    fun τ L hL L' h => sobBd_congr hL fun w hw => h w ((hsm τ w).2 hw)

  have hcw : ∀ τ (L : M.H τ →ₗ[ℂ] E), (∀ r ∈ Rk τ, ∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, L (r.1 x) = r.2 (L x)) →
      ∃ T : M.H τ →ₗ[ℂ] E, (∀ v, Formalism.MainNotions.S.IsKFin (M.ε τ) (M.σ τ) v → T v = L v) ∧
        IsSmoothGMap (M.ε τ) (M.σ τ) p (π τ) T ∧ IsClosed (T '' {w | SmoothVec (lieSet (M.ε τ)) (M.σ τ) w}) ∧
        ((∃ v, Formalism.MainNotions.S.IsKFin (M.ε τ) (M.σ τ) v ∧ L v ≠ 0) →
          ∀ Sl : List (List (Matrix (Fin V.rank) (Fin V.rank) ℂ)), (∀ l ∈ Sl, ∀ X ∈ l, X ∈ lieSet (M.ε τ)) →
            ∃ q : Seminorm ℂ E, Continuous q ∧
              ∀ w, SmoothVec (lieSet (M.ε τ)) (M.σ τ) w → sobNorm (M.σ τ) Sl w ≤ q (T w)) := by
    intro τ L hLk
    have hGK : IsGKMap (M.ε τ) (M.σ τ) (π τ) (dπ τ) L :=
      ⟨fun k hk v hv => hLk _ (Or.inl ⟨k, hk, rfl⟩) v hv, fun X hX v hv => hLk _ (Or.inr ⟨X, hX, rfl⟩) v hv⟩
    obtain ⟨T, hT1, hT2, -, hT4, hT5⟩ := hCW V.rank (M.ε τ) (M.H τ) (M.σ τ) (M.ds τ).2.2.1 (M.ds τ).2.2.2.1 E p
      (π τ) (dπ τ) (hπ τ) L hGK
    exact ⟨T, hT1, hT2, hT4, hT5⟩
  have hext : ∀ τ (L : M.H τ →ₗ[ℂ] E), (∀ r ∈ Rk τ, ∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, L (r.1 x) = r.2 (L x)) →
      ∃ L' ∈ C τ, (∀ r ∈ Rg τ, ∀ x ∈ M.sm τ, L' (r.1 x) = r.2 (L' x)) ∧
        ∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, L' x = L x := by
    intro τ L hLk
    obtain ⟨T, hT1, ⟨hT2, hT3⟩, -⟩ := hcw τ L hLk
    refine ⟨T, hT3, ?_, fun x hx => hT1 x hx⟩
    rintro r ⟨g, hg, rfl⟩ x hx
    exact hT2 g hg x ((hsm τ x).1 hx)
  have huniq : ∀ τ, ∀ L ∈ C τ, (∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, L x = 0) → ∀ x ∈ M.sm τ, L x = 0 :=
    fun τ L hL h0 => uniq hHC M τ (hπ τ).withSeminorms hL h0
  have hpostC : ∀ τ τ', τ ≠ τ' → ∀ r ∈ Rk τ ∪ Rg τ, ∀ L ∈ C τ', r.2 ∘ₗ L ∈ C τ' := by
    rintro τ τ' - r ((⟨k, -, rfl⟩ | ⟨X, -, rfl⟩) | ⟨g, -, rfl⟩) L hL
    · exact sobBd_comp (hπ τ').withSeminorms hL (π τ k)
    · exact sobBd_comp (hπ τ').withSeminorms hL (dπ τ X)
    · exact sobBd_comp (hπ τ').withSeminorms hL (π τ g)
  have hcomm' : ∀ τ τ', τ ≠ τ' → ∀ r ∈ Rk τ ∪ Rg τ, ∀ r' ∈ Rg τ', r.2 ∘ₗ r'.2 = r'.2 ∘ₗ r.2 := by
    rintro τ τ' hne r ((⟨k, hk, rfl⟩ | ⟨X, hX, rfl⟩) | ⟨g, hg, rfl⟩) r' ⟨g', hg', rfl⟩
    · have h := hcomm τ τ' hne k (GlobalTheory.TypeSum.K_le_UJ hk) g' hg'
      ext x
      exact congrArg (fun f : E →L[ℂ] E => f x) h
    · have h := dRep_comm (hπ τ) hX (π τ' g') fun t =>
        hcomm τ' τ hne.symm g' hg' _ (GlobalTheory.TypeSum.exp_mem_UJ hX t)
      ext x
      exact (congrArg (fun f : E →L[ℂ] E => f x) h).symm
    · have h := hcomm τ τ' hne g hg g' hg'
      ext x
      exact congrArg (fun f : E →L[ℂ] E => f x) h
  have h0 : ∀ τ (u : ∀ τ, M.H τ), (∀ τ', τ' ≠ τ → u τ' ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ') → ∀ r ∈ Rk τ,
      ∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ,
      T₀' (Function.update u τ (r.1 x)) = r.2 (T₀' (Function.update u τ x)) := by
    intro τ u _ r hr x hx
    have e : ∀ y : M.H τ, T₀' (Function.update u τ y) = T₀ (Function.update (fun τ' => P τ' (u τ')) τ (P τ y)) :=
      fun y => by
        show T₀ (fun τ' => P τ' (Function.update u τ y τ')) = _
        congr 1
        funext τ'
        exact Function.apply_update (fun τ => P τ) u τ y τ'
    have hr' := hRk τ r hr x hx
    rw [e, e]
    rcases hr with ⟨k, hk, rfl⟩ | ⟨X, hX, rfl⟩
    · have h := hK τ k hk (Function.update (fun τ' => P τ' (u τ')) τ (P τ x)) (P τ (M.σ τ k x))
        (by rw [Function.update_self, hP' τ _ hx, hP' τ _ hr'])
      rw [Function.update_idem] at h
      exact h
    · have h := hL τ X hX (Function.update (fun τ' => P τ' (u τ')) τ (P τ x)) (P τ (dRep (M.σ τ) X x))
        (by rw [Function.update_self, hP' τ _ hx, hP' τ _ hr'])
      rw [Function.update_idem] at h
      exact h
  by_cases hz : ∀ u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M, T₀ u = 0
  · refine ⟨0, fun v u _ => (hz u).symm, fun τ g _ v w _ => by simp, fun τ i v => ⟨[], 0, by simp, fun w => by simp⟩⟩
  push_neg at hz
  obtain ⟨u₀, hu₀⟩ := hz

  have hNZ : ∀ τ, ∃ N : M.H τ →ₗ[ℂ] E, N ∈ C τ ∧ IsClosed (N '' {w | SmoothVec (lieSet (M.ε τ)) (M.σ τ) w}) ∧
      ∀ Sl : List (List (Matrix (Fin V.rank) (Fin V.rank) ℂ)), (∀ l ∈ Sl, ∀ X ∈ l, X ∈ lieSet (M.ε τ)) →
        ∃ q : Seminorm ℂ E, Continuous q ∧
          ∀ w, SmoothVec (lieSet (M.ε τ)) (M.σ τ) w → sobNorm (M.σ τ) Sl w ≤ q (N w) := by
    intro τ
    let u : ∀ τ, M.H τ := fun τ => (u₀ τ : M.H τ)
    have hLk : ∀ r ∈ Rk τ, ∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, T₀'.toLinearMap u τ (r.1 x) = r.2 (T₀'.toLinearMap u τ x) :=
      fun r hr x hx => by
        simp only [MultilinearMap.toLinearMap_apply]
        exact h0 τ u (fun τ' _ => (u₀ τ').2) r hr x hx
    obtain ⟨T, hT1, ⟨-, hT3⟩, hT4, hT5⟩ := hcw τ _ hLk
    refine ⟨T, hT3, hT4, hT5 ⟨u τ, (u₀ τ).2, ?_⟩⟩
    rw [MultilinearMap.toLinearMap_apply, Function.update_eq_self]
    show T₀ (fun τ' => P τ' (u₀ τ' : M.H τ')) ≠ 0
    have : (fun τ' => P τ' (u₀ τ' : M.H τ')) = u₀ := funext fun τ' => hP τ' (u₀ τ')
    rw [this]
    exact hu₀
  have hbs : ∀ τ τ', τ ≠ τ' → ∀ F : M.H τ →ₗ[ℂ] M.H τ' →ₗ[ℂ] E, (∀ w ∈ M.sm τ, F w ∈ C τ') →
      (∀ a ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ', F.flip a ∈ C τ) → ∀ b ∈ M.sm τ', F.flip b ∈ C τ := by
    intro τ τ' _ F hF1 hF2 b hb
    obtain ⟨N₁, hN₁C, hN₁cl, hN₁iso⟩ := hNZ τ
    obtain ⟨N₂, hN₂C, -, hN₂iso⟩ := hNZ τ'
    have hp := (hπ τ).withSeminorms
    let j₁ : M.sm τ →ₗ[ℂ] E := N₁ ∘ₗ (M.sm τ).subtype
    let j₂ : M.sm τ' →ₗ[ℂ] E := N₂ ∘ₗ (M.sm τ').subtype
    have hinj : Function.Injective j₁ := by
      refine (injective_iff_map_eq_zero j₁).2 fun x hx => ?_
      obtain ⟨q, -, hq⟩ := hN₁iso [[]] (by simp)
      have h1 := hq x ((hsm τ x).1 x.2)
      have h2 : j₁ x = N₁ x := rfl
      rw [← h2, hx, map_zero] at h1
      have h3 : sobNorm (M.σ τ) [[]] (x : M.H τ) = ‖(x : M.H τ)‖ := by simp [sobNorm]
      rw [h3] at h1
      exact Subtype.ext (norm_le_zero_iff.1 h1)
    have hcl : IsClosed (Set.range j₁) := by
      have e : Set.range j₁ = N₁ '' {w | SmoothVec (lieSet (M.ε τ)) (M.σ τ) w} := by
        ext y
        constructor
        · rintro ⟨x, rfl⟩
          exact ⟨x, (hsm τ x).1 x.2, rfl⟩
        · rintro ⟨w, hw, rfl⟩
          exact ⟨⟨w, (hsm τ w).2 hw⟩, rfl⟩
      rw [e]
      exact hN₁cl
    let D₂ : Submodule ℂ (M.sm τ') := (GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ').comap (M.sm τ').subtype
    have hD : ∀ x, j₂ x ∈ closure (j₂ '' (D₂ : Set (M.sm τ'))) := by
      intro x
      have h := GlobalTheory.T.mem_closure_of_forall_clm_vanish (hπ τ').withSeminorms (D₂.map j₂) (j₂ x) fun f hf =>
        form_zero hHC M τ' (hπ τ').withSeminorms hN₂C f (fun a ha => hf _ ⟨⟨a, hAB τ' ha⟩, ha, rfl⟩) x x.2
      rwa [Submodule.map_coe] at h
    let F' : M.sm τ →ₗ[ℂ] M.sm τ' →ₗ[ℂ] E := F.compl₁₂ (M.sm τ).subtype (M.sm τ').subtype
    have h₂ : ∀ w i, ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ b, p i (F' w b) ≤ q (j₂ b) := by
      intro w i
      obtain ⟨q, hq, hb⟩ := bound_via hN₂iso (hF1 w w.2) i
      exact ⟨q, hq, fun b => hb b ((hsm τ' b).1 b.2)⟩
    have h₁ : ∀ a ∈ D₂, ∀ i, ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ w, p i (F' w a) ≤ q (j₁ w) := by
      intro a ha i
      obtain ⟨q, hq, hb⟩ := bound_via hN₁iso (hF2 a ha) i
      exact ⟨q, hq, fun w => hb w ((hsm τ w).1 w.2)⟩
    intro i
    obtain ⟨q, hq, hb'⟩ := GlobalTheory.T.exists_seminorm_bound_of_dense_second_slot hp j₁ j₂ hinj hcl D₂ hD F' h₂ h₁ ⟨b, hb⟩ i
    obtain ⟨Sl, C', hS, hb''⟩ := sobBd_seminorm hp hN₁C q hq
    exact ⟨Sl, C', hS, fun w hw => (hb' ⟨w, (hsm τ w).2 hw⟩).trans (hb'' w hw)⟩
  obtain ⟨Tab, hT1, hT2⟩ := GlobalTheory.T.exists_multilinear_positionwise_extension_of_equivariant (H := fun τ => M.H τ) (fun τ => GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ)
    (fun τ => M.sm τ) hAB Rk Rg hRk hRg C hC hext huniq hpostC hcomm' hbs T₀' h0
  have hupd : ∀ (v : M.Vec) τ (w : M.sm τ),
      (fun τ' => ((Function.update v τ w τ' : M.sm τ') : M.H τ')) =
        Function.update (fun τ' => (v τ' : M.H τ')) τ (w : M.H τ) :=
    fun v τ w => funext fun τ' => Function.apply_update (fun τ => ((M.sm τ).subtype : M.sm τ → M.H τ)) v τ w τ'
  refine ⟨Tab.compLinearMap fun τ => (M.sm τ).subtype, ?_, ?_, ?_⟩
  · intro v u hvu
    show Tab (fun τ => (v τ : M.H τ)) = T₀ u
    have e : (fun τ => (v τ : M.H τ)) = fun τ => (u τ : M.H τ) := funext hvu
    rw [e, hT1 _ fun τ => (u τ).2]
    show T₀ (fun τ => P τ (u τ : M.H τ)) = T₀ u
    congr 1
    funext τ
    exact hP τ (u τ)
  · intro τ g hg v w hw
    show Tab (fun τ' => ((Function.update v τ w τ' : M.sm τ') : M.H τ')) = π τ g (Tab fun τ' => (v τ' : M.H τ'))
    rw [hupd, hw]
    have h := (hT2 τ (fun τ' => (v τ' : M.H τ')) fun τ' _ => (v τ').2).2 _ ⟨g, hg, rfl⟩ (v τ) (v τ).2
    rw [Function.update_eq_self] at h
    exact h
  · intro τ i v
    obtain ⟨Sl, C', hS, hb⟩ := (hT2 τ (fun τ' => (v τ' : M.H τ')) fun τ' _ => (v τ').2).1 i
    refine ⟨Sl, C', hS, fun w => ?_⟩
    have h := hb w ((hsm τ w).1 w.2)
    rw [MultilinearMap.toLinearMap_apply] at h
    show p i (Tab (fun τ' => ((Function.update v τ w τ' : M.sm τ') : M.H τ'))) ≤ _
    rw [hupd]
    exact h

end GlobalTheory.FactorExtension
