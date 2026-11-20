import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerGoodModelsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdaptedPlaneFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdaptedBasisHermitianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordinatesGoodModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedBasisHermitianUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRestrictionExtendByZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendByZeroMemSchAStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendByZeroSchwartzBruhatMapStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.EvTwoNeB

/- English proof (translation)
Introduce `g`. Set `eq : κ₁ ⊕ {k // k ∉ Set.range j} ≃ κ` to `(Equiv.sumCongr (Equiv.ofInjective j hj) (Equiv.refl _)).trans (Equiv.sumCompl (· ∈ Set.range j))`. Set `b : ContDiffBump (0 : {k // k ∉ Set.range j} → mixedEmbedding.mixedSpace F)` to `⟨1, 2, one_pos, one_lt_two⟩`. Establish `hs : HasCompactSupport (fun x => ((b x : ℝ) : ℂ))` using `b.hasCompactSupport.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)`. Establish `hc : ContDiff ℝ (⊤ : ℕ∞) (fun x => ((b x : ℝ) : ℂ))` using `Complex.ofRealCLM.contDiff.comp b.contDiff`.

Take `⟨f₀, hf₀⟩` from `GlobalTheory.SchwartzBox.exists_schwartz_box g (hs.toSchwartzMap hc)`. Use `⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : κ => mixedEmbedding.mixedSpace F) eq).symm f₀, ?_⟩` and prove the remaining obligations. Use extensionality with `y`. Rewrite using `[hR, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply]`. Establish `h2 : b 0 = 1` using `b.one_of_mem_closedBall (by simp [b])`.

Establish `e1 : ∀ x : κ → mixedEmbedding.mixedSpace F, (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : κ => mixedEmbedding.mixedSpace F) eq).symm x = x ∘ eq`. Introduce `x`. Both sides reduce to the same expression. Rewrite using `[e1, hf₀]`. Establish `e2 : ((Function.extend j y 0 : κ → mixedEmbedding.mixedSpace F) ∘ eq) ∘ Sum.inl = y`.

Use function extensionality and compare the values at `i`. Simplify using `[eq, hj.extend_apply]`. Establish `e3 : ((Function.extend j y 0 : κ → mixedEmbedding.mixedSpace F) ∘ eq) ∘ Sum.inr = 0`. Use function extensionality and compare the values at `k`. Simplify using `only [Function.comp_apply, eq, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr, Equiv.refl_apply, Equiv.sumCompl_apply_inr, Pi.zero_apply]`.

Conclude with `Function.extend_apply' _ _ _ (fun ⟨a, ha⟩ => k.2 ⟨a, ha⟩)`. Rewrite using `[e2, e3]`. Simplify using `[h2]`.
-/
theorem restr_surjective {F : Type} [Field F] [NumberField F] {κ₁ κ : Type} [Fintype κ₁] [Fintype κ] {j : κ₁ → κ}
    (hj : Function.Injective j) (R : SInf F κ →L[ℂ] SInf F κ₁) (hR : ∀ f y, R f y = f (Function.extend j y 0)) :
    Function.Surjective R := by
  classical
  intro g
  let eq : κ₁ ⊕ {k // k ∉ Set.range j} ≃ κ :=
    (Equiv.sumCongr (Equiv.ofInjective j hj) (Equiv.refl _)).trans (Equiv.sumCompl (· ∈ Set.range j))
  let b : ContDiffBump (0 : {k // k ∉ Set.range j} → mixedEmbedding.mixedSpace F) := ⟨1, 2, one_pos, one_lt_two⟩
  have hs : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) :=
    b.hasCompactSupport.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun x => ((b x : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp b.contDiff
  obtain ⟨f₀, hf₀⟩ := GlobalTheory.SchwartzBox.exists_schwartz_box g (hs.toSchwartzMap hc)
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : κ => mixedEmbedding.mixedSpace F) eq).symm f₀, ?_⟩
  ext y
  rw [hR, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply]
  have h2 : b 0 = 1 := b.one_of_mem_closedBall (by simp [b])
  have e1 : ∀ x : κ → mixedEmbedding.mixedSpace F,
      (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : κ => mixedEmbedding.mixedSpace F) eq).symm x = x ∘ eq := by
    intro x; rfl
  rw [e1, hf₀]
  have e2 : ((Function.extend j y 0 : κ → mixedEmbedding.mixedSpace F) ∘ eq) ∘ Sum.inl = y := by
    funext i
    simp [eq, hj.extend_apply]
  have e3 : ((Function.extend j y 0 : κ → mixedEmbedding.mixedSpace F) ∘ eq) ∘ Sum.inr = 0 := by
    funext k
    simp only [Function.comp_apply, eq, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr, Equiv.refl_apply,
      Equiv.sumCompl_apply_inr, Pi.zero_apply]
    exact Function.extend_apply' _ _ _ (fun ⟨a, ha⟩ => k.2 ⟨a, ha⟩)
  rw [e2, e3]
  simp [h2]

end GlobalTheory.ThK.EvTwoNeB

namespace GlobalTheory.ThK.EvTwoNeB

/- English proof (translation)
Use function extensionality and compare the values at `k`. Distinguish the cases in `h : ∃ a, j a = k`. Take `⟨a, rfl⟩` from `h`. Simplify using `[hj.extend_apply]`. Simplify using `[Function.extend_apply' _ _ _ h, hg]`.
-/
theorem extend_map {α β M N : Type} {j : α → β} (hj : Function.Injective j) [Zero M] [Zero N] (g : M → N) (hg : g 0 = 0)
    (y : α → M) : (fun k => g (Function.extend j y 0 k)) = Function.extend j (fun i => g (y i)) 0 := by
  funext k
  by_cases h : ∃ a, j a = k
  · obtain ⟨a, rfl⟩ := h
    simp [hj.extend_apply]
  · simp [Function.extend_apply' _ _ _ h, hg]

/- English proof (translation)
Use function extensionality and compare the values at `k`. Distinguish the cases in `h : ∃ x, j x = k`. Take `⟨x, rfl⟩` from `h`. Simplify using `[hj.extend_apply]`. Simplify using `[Function.extend_apply' _ _ _ h]`.
-/
theorem extend_add {α β M : Type} {j : α → β} (hj : Function.Injective j) [AddZeroClass M] (a b : α → M) :
    Function.extend j (a + b) 0 = Function.extend j a 0 + Function.extend j b 0 := by
  funext k
  by_cases h : ∃ x, j x = k
  · obtain ⟨x, rfl⟩ := h
    simp [hj.extend_apply]
  · simp [Function.extend_apply' _ _ _ h]

/- English proof (translation)
Rewrite using `[← Finset.sum_subset (Finset.subset_univ (Finset.univ.map ⟨j, hj⟩)) (fun k _ hk => by`. Rewrite using `[Function.extend_apply' (f := j) f (0 : β → R) k (fun ⟨a, ha⟩ => hk (Finset.mem_map.2 ⟨a, Finset.mem_univ _, ha⟩))]`. Use the proof step `rfl),`. Use the proof step `Finset.sum_map]`. Conclude with `Finset.sum_congr rfl fun i _ => hj.extend_apply _ _ _`.
-/
theorem sum_extend {α β R : Type} [Fintype α] [Fintype β] {j : α → β} (hj : Function.Injective j) [AddCommMonoid R]
    (f : α → R) : ∑ k, Function.extend j f 0 k = ∑ i, f i := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map ⟨j, hj⟩)) (fun k _ hk => by
      rw [Function.extend_apply' (f := j) f (0 : β → R) k (fun ⟨a, ha⟩ => hk (Finset.mem_map.2 ⟨a, Finset.mem_univ _, ha⟩))]; rfl),
    Finset.sum_map]
  exact Finset.sum_congr rfl fun i _ => hj.extend_apply _ _ _

/- English proof (translation)
Establish `: (fun k => Function.extend j a 0 k * Function.extend j b 0 k) = Function.extend j (fun i => a i * b i) 0`. Use function extensionality and compare the values at `k`. Distinguish the cases in `h : ∃ x, j x = k`. Take `⟨x, rfl⟩` from `h`. Simplify using `[hj.extend_apply]`.

Simplify using `[Function.extend_apply' _ _ _ h]`. Simplify using `only [dotProduct]`. Rewrite using `[show (∑ k, Function.extend j a 0 k * Function.extend j b 0 k) = ∑ k, Function.extend j (fun i => a i * b i) 0 k from Finset.sum_congr rfl fun k _ => congrFun this k, sum_extend hj]`.
-/
theorem extend_dot {α β R : Type} [Fintype α] [Fintype β] {j : α → β} (hj : Function.Injective j) [CommRing R]
    (a b : α → R) : Function.extend j a 0 ⬝ᵥ Function.extend j b 0 = a ⬝ᵥ b := by
  have : (fun k => Function.extend j a 0 k * Function.extend j b 0 k) = Function.extend j (fun i => a i * b i) 0 := by
    funext k
    by_cases h : ∃ x, j x = k
    · obtain ⟨x, rfl⟩ := h
      simp [hj.extend_apply]
    · simp [Function.extend_apply' _ _ _ h]
  simp only [dotProduct]
  rw [show (∑ k, Function.extend j a 0 k * Function.extend j b 0 k) = ∑ k, Function.extend j (fun i => a i * b i) 0 k from
    Finset.sum_congr rfl fun k _ => congrFun this k, sum_extend hj]

/- English proof (translation)
Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : ∃ x, j x = k`. Take `⟨x, rfl⟩` from `h`. Simplify using `[hq]`. Simplify using `[Function.extend_apply' _ _ _ h]`.
-/
theorem extend_dot_zero {α β R : Type} [Fintype α] [Fintype β] {j : α → β} [CommRing R] (y : α → R) (q : β → R)
    (hq : ∀ k, q (j k) = 0) : Function.extend j y 0 ⬝ᵥ q = 0 := by
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases h : ∃ x, j x = k
  · obtain ⟨x, rfl⟩ := h
    simp [hq]
  · simp [Function.extend_apply' _ _ _ h]

/- English proof (translation)
Use function extensionality and compare the values at `y`. Establish `key : (∀ i, Function.extend j y 0 i ∈ v.adicCompletionIntegers F) ↔ ∀ i, y i ∈ v.adicCompletionIntegers F`. Prove the components needed by the constructor for the conclusion. Introduce `h i`. Simplify `h (j i)` using `[hj.extend_apply]`.

Introduce `h k`. Distinguish the cases in `hk : ∃ a, j a = k`. Take `⟨a, rfl⟩` from `hk`. Simplify `h a` using `[hj.extend_apply]`. Simplify using `[Function.extend_apply' _ _ _ hk]`.

Distinguish the cases in `hy : ∀ i, y i ∈ v.adicCompletionIntegers F`. Rewrite using `[Set.indicator_of_mem (show y ∈ {x : κ₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from hy), Set.indicator_of_mem (show Function.extend j y 0 ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from key.2 hy)]`. Both sides reduce to the same expression. Rewrite using `[Set.indicator_of_notMem (show y ∉ {x : κ₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from hy), Set.indicator_of_notMem (show Function.extend j y 0 ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from fun h => hy (key.1 h))]`.
-/
theorem std_extend {F : Type} [Field F] [NumberField F] {κ₁ κ : Type} {j : κ₁ → κ} (hj : Function.Injective j) (v : Pl F) :
    (fun y : κ₁ → Fv F v => Set.indicator {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} (1 : (κ → Fv F v) → ℂ)
      (Function.extend j y 0)) = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} (1 : (κ₁ → Fv F v) → ℂ) := by
  funext y
  have key : (∀ i, Function.extend j y 0 i ∈ v.adicCompletionIntegers F) ↔ ∀ i, y i ∈ v.adicCompletionIntegers F := by
    constructor
    · intro h i
      simpa [hj.extend_apply] using h (j i)
    · intro h k
      by_cases hk : ∃ a, j a = k
      · obtain ⟨a, rfl⟩ := hk
        simpa [hj.extend_apply] using h a
      · simp [Function.extend_apply' _ _ _ hk]
  by_cases hy : ∀ i, y i ∈ v.adicCompletionIntegers F
  · rw [Set.indicator_of_mem (show y ∈ {x : κ₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from hy),
      Set.indicator_of_mem (show Function.extend j y 0 ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from key.2 hy)]
    rfl
  · rw [Set.indicator_of_notMem (show y ∉ {x : κ₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from hy),
      Set.indicator_of_notMem (show Function.extend j y 0 ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from
        fun h => hy (key.1 h))]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d n₁ X W X₁ M Mb r s r' s' r₁ s₁ H j₀ j₁ hB hX hW hM hX₁ hMb hH`. Take `⟨j, co, hj, hrat, hι, hx, hy⟩` from `GlobalTheory.T.exists_adapted_basis_hermitian F E σ B n d X W r s r' s' hB hX hW n₁ X₁ H j₀ j₁ Mb r₁ s₁ hX₁ hH hMb`. Take `⟨e₁, ei₁, ev₁, hsurj, hmaps, hheis, hSB, hvac, hstd, hpure⟩` from `GlobalTheory.T.darboux_coordinates_good_model F E σ B n d X W M r s r' s' hB hX hW hM co hrat`. Establish `hres` using `fun v => GlobalTheory.T.adapted_basis_hermitian_unique F E σ B n d X W r s r' s' hB hX hW n₁ X₁ H j₀ j₁ Mb r₁ s₁ hX₁ hH hMb j co hj hι hx hy v _ (hvac v)`. Use `choose c hc0 hc using hres`.

Establish `hc1 : ∀ᶠ v in cofinite, c v = 1` using `by filter_upwards [hstd, hMb.std] with v h1 h2`. Establish `h'` using `hc v`. Rewrite `h'` using `[h1, h2, std_extend hj v]`. Establish `h` using `congrFun h' 0`. Establish `hm : (0 : Fin n₁ × Fin d → Fv F v) ∈ {x : Fin n₁ × Fin d → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F}` using `fun i => zero_mem _`.

Rewrite `h` using `[Pi.smul_apply, Set.indicator_of_mem hm, smul_eq_mul]`. Simplify using `using h.symm`. Take `⟨R, hR⟩` from `GlobalTheory.T.exists_restriction_extend_by_zero F j hj`. Set `ev : ∀ v : Pl F, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n₁ × Fin d → Fv F v) → ℂ` to `fun v => (c v)⁻¹ • (LinearMap.funLeft ℂ ℂ (fun y : Fin n₁ × Fin d → Fv F v => Function.extend j y 0) ∘ₗ ev₁ v)`. Establish `hev : ∀ v, ev v (M.vac v) = Mb.vac v`.

Introduce `v`. Use `show (c v)⁻¹ • (LinearMap.funLeft ℂ ℂ (fun y : Fin n₁ × Fin d → Fv F v => Function.extend j y 0) (ev₁ v (M.vac v))) = _`. Rewrite using `[show LinearMap.funLeft ℂ ℂ (fun y : Fin n₁ × Fin d → Fv F v => Function.extend j y 0) (ev₁ v (M.vac v)) = c v • Mb.vac v from hc v, smul_smul, inv_mul_cancel₀ (hc0 v), one_smul]`. Establish `pureEq : ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) → ((∏ᶠ v, c v)⁻¹ • (LinearMap.funLeft ℂ ℂ (fun y : Fin n₁ × Fin d → AF F => Function.extend j y 0) ∘ₗ e₁)) (pure f φ) = pure ((R.comp ei₁) f) fun v => ev v (φ v)`. Introduce `f φ hφ hφv`.

Use function extensionality and compare the values at `y`. Rewrite using `[LinearMap.smul_apply, LinearMap.comp_apply, hpure f φ hφ hφv]`. Simplify using `only [ev, LinearMap.funLeft_apply, Function.comp_apply, Pi.smul_apply, smul_eq_mul, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, ContinuousLinearMap.comp_apply, hR, LinearMap.smul_apply, LinearMap.comp_apply]`. Establish `hI : (fun i => evI F (Function.extend j y 0 i)) = Function.extend j (fun i => evI F (y i)) 0` using `extend_map hj (evI F) (by unfold evI; exact map_zero _) y`. Establish `hF : ∀ v : Pl F, (fun i => evFin F v (Function.extend j y 0 i)) = Function.extend j (fun i => evFin F v (y i)) 0` using `fun v => extend_map hj _ (map_zero _) y`.

Simplify using `only [hI, hF]`. Establish `hfin1 : (Function.mulSupport fun v : Pl F => (c v)⁻¹).Finite`. Use `(Filter.eventually_cofinite.1 hc1).subset fun v hv h => hv ?_` and prove the remaining obligations. Simplify using `[h]`. Establish `hfin2 : (Function.mulSupport fun v : Pl F => ev₁ v (φ v) (Function.extend j (fun i => evFin F v (y i)) 0)).Finite`.

Use `GlobalTheory.PureFactor.mulSupport_finite (κ := Fin n₁ × Fin d) (fun v x => ev₁ v (φ v) (Function.extend j x 0)) (by filter_upwards [hφv, hstd] with v h1 h2` as an intermediate fact. Rewrite using `[h1, h2]`. Conclude with `std_extend hj v) y`. Conclude with `this`. Rewrite using `[finprod_mul_distrib hfin1 hfin2, finprod_inv_distrib]`.

Expand and normalize the polynomial expressions, which then agree. Use `⟨(∏ᶠ v, c v)⁻¹ • (LinearMap.funLeft ℂ ℂ (fun y : Fin n₁ × Fin d → AF F => Function.extend j y 0) ∘ₗ e₁), R.comp ei₁, ev, ⟨?_, ?_, ?_, ?_⟩, (restr_surjective hj R hR).comp hsurj, hev, ?_⟩` and prove the remaining obligations. Introduce `Φ hΦ`. Conclude with `Submodule.smul_mem _ _ (GlobalTheory.T.extend_by_zero_mem_schA F j hj _ (hmaps Φ hΦ))`. Introduce `z Φ hΦ`.

Establish `h1 : incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ = incM F H.ι * z`. Rewrite using `[show incM F (1 : Matrix (Fin d) (Fin d) E) = 1 from Matrix.map_one _ (map_zero _) (map_one _)]`. Simplify using the standard rewrite rules. Rewrite using `[h1]`. Use function extensionality and compare the values at `y`.

Simplify using `only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.funLeft_apply, Function.comp_apply, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[hheis _ Φ hΦ]`. Simplify using `only [Darboux.rho, schr, hι, extend_dot hj, ← extend_add hj, Pi.smul_apply, smul_eq_mul, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.funLeft_apply, Function.comp_apply]`. Expand and normalize the polynomial expressions, which then agree. Introduce `u hu Φ hΦ`.

Take `⟨z, rfl⟩` from `hu`. Use function extensionality and compare the values at `y`. Simplify using `only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.funLeft_apply, Function.comp_apply, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[hheis _ Φ hΦ]`. Take `⟨h1, h2⟩` from `hx z`.

Simplify using `only [Darboux.rho, schr, h1, extend_dot_zero _ _ h2, zero_dotProduct, mul_zero, add_zero, AddChar.map_zero_eq_one, one_mul]`. Use `⟨R.comp ei₁, ev, ?_, fun v => ⟨hev v, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `h`. Choose the witnesses or unpack the hypotheses as in `⟨g, hg⟩ : ∃ g : SInf F (Fin n₁ × Fin d), g ≠ 0 := by`. Choose the witnesses or unpack the hypotheses as in `⟨b, hb0⟩ : ∃ b : SInf F (Fin n₁ × Fin d), b 0 ≠ 0 := by`.

Set `bb : ContDiffBump (0 : Fin n₁ × Fin d → mixedEmbedding.mixedSpace F)` to `⟨1, 2, one_pos, one_lt_two⟩`. Establish `hs : HasCompactSupport (fun x => ((bb x : ℝ) : ℂ))` using `bb.hasCompactSupport.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)`. Establish `hcd : ContDiff ℝ (⊤ : ℕ∞) (fun x => ((bb x : ℝ) : ℂ))` using `Complex.ofRealCLM.contDiff.comp bb.contDiff`. Use `⟨hs.toSchwartzMap hcd, ?_⟩` and prove the remaining obligations. Establish `h2 : bb 0 = 1` using `bb.one_of_mem_closedBall (by simp [bb])`.

Simplify using `[h2]`. Conclude with `⟨b, fun h0 => hb0 (by rw [h0]; rfl)⟩`. Take `⟨f, hf⟩` from `(restr_surjective hj R hR).comp hsurj g`. Apply `hg` to reduce the goal to its premises. Rewrite using `[← hf]`.

Conclude with `congrArg (fun T : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d) => T f) h`. Use `show (SB _).map ((c v)⁻¹ • (LinearMap.funLeft ℂ ℂ (fun y : Fin n₁ × Fin d → Fv F v => Function.extend j y 0) ∘ₗ ev₁ v)) = SB _`. Rewrite using `[Submodule.map_smul _ _ _ (inv_ne_zero (hc0 v)), Submodule.map_comp, hSB v, GlobalTheory.T.extend_by_zero_schwartzBruhat_map F j hj v]`. Conclude with `pureEq`. Conclude with `pureEq`.
-/
theorem exists_isEv_onto : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E)
    {n d n₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} (M : Model σ X W) (Mb : Model σ X₁ W) {r s r' s' r₁ s₁ : ℕ}
    (H : Plane E n n₁) {j₀ j₁ : ℕ}, B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ →
    X₁.IsHerm σ B r₁ s₁ → Mb.IsGood B.ψ → H.IsAdapted σ B X X₁ j₀ j₁ →
    ∃ (S : Fn F n d →ₗ[ℂ] Fn F n₁ d) (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d))
      (ev : ∀ v : Pl F, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n₁ × Fin d → Fv F v) → ℂ),
      IsEv B M Mb H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} S ∧ Function.Surjective ei ∧
      (∀ v, ev v (M.vac v) = Mb.vac v) ∧
      ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) → S (pure f φ) = pure (ei f) fun v => ev v (φ v) := by
  intro F E _ _ _ _ _ σ B n d n₁ X W X₁ M Mb r s r' s' r₁ s₁ H j₀ j₁ hB hX hW hM hX₁ hMb hH
  classical
  obtain ⟨j, co, hj, hrat, hι, hx, hy⟩ :=
    GlobalTheory.T.exists_adapted_basis_hermitian F E σ B n d X W r s r' s' hB hX hW n₁ X₁ H j₀ j₁ Mb r₁ s₁ hX₁ hH hMb
  obtain ⟨e₁, ei₁, ev₁, hsurj, hmaps, hheis, hSB, hvac, hstd, hpure⟩ :=
    GlobalTheory.T.darboux_coordinates_good_model F E σ B n d X W M r s r' s' hB hX hW hM co hrat
  have hres := fun v => GlobalTheory.T.adapted_basis_hermitian_unique F E σ B n d X W r s r' s' hB hX hW n₁ X₁ H j₀ j₁ Mb r₁ s₁ hX₁ hH
    hMb j co hj hι hx hy v _ (hvac v)
  choose c hc0 hc using hres
  have hc1 : ∀ᶠ v in cofinite, c v = 1 := by
    filter_upwards [hstd, hMb.std] with v h1 h2
    have h' := hc v
    rw [h1, h2, std_extend hj v] at h'
    have h := congrFun h' 0
    have hm : (0 : Fin n₁ × Fin d → Fv F v) ∈ {x : Fin n₁ × Fin d → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} :=
      fun i => zero_mem _
    rw [Pi.smul_apply, Set.indicator_of_mem hm, smul_eq_mul] at h
    simpa using h.symm
  obtain ⟨R, hR⟩ := GlobalTheory.T.exists_restriction_extend_by_zero F j hj
  let ev : ∀ v : Pl F, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n₁ × Fin d → Fv F v) → ℂ := fun v => (c v)⁻¹ •
      (LinearMap.funLeft ℂ ℂ (fun y : Fin n₁ × Fin d → Fv F v => Function.extend j y 0) ∘ₗ ev₁ v)
  have hev : ∀ v, ev v (M.vac v) = Mb.vac v := by
    intro v
    show (c v)⁻¹ • (LinearMap.funLeft ℂ ℂ (fun y : Fin n₁ × Fin d → Fv F v => Function.extend j y 0) (ev₁ v (M.vac v))) = _
    rw [show LinearMap.funLeft ℂ ℂ (fun y : Fin n₁ × Fin d → Fv F v => Function.extend j y 0) (ev₁ v (M.vac v)) =
      c v • Mb.vac v from hc v, smul_smul, inv_mul_cancel₀ (hc0 v), one_smul]
  have pureEq : ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) →
      ((∏ᶠ v, c v)⁻¹ • (LinearMap.funLeft ℂ ℂ (fun y : Fin n₁ × Fin d → AF F => Function.extend j y 0) ∘ₗ e₁)) (pure f φ) =
        pure ((R.comp ei₁) f) fun v => ev v (φ v) := by
    intro f φ hφ hφv
    funext y
    rw [LinearMap.smul_apply, LinearMap.comp_apply, hpure f φ hφ hφv]
    simp only [ev, LinearMap.funLeft_apply, Function.comp_apply, Pi.smul_apply, smul_eq_mul, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure,
      ContinuousLinearMap.comp_apply, hR, LinearMap.smul_apply, LinearMap.comp_apply]
    have hI : (fun i => evI F (Function.extend j y 0 i)) = Function.extend j (fun i => evI F (y i)) 0 :=
      extend_map hj (evI F) (by unfold evI; exact map_zero _) y
    have hF : ∀ v : Pl F, (fun i => evFin F v (Function.extend j y 0 i)) =
        Function.extend j (fun i => evFin F v (y i)) 0 := fun v => extend_map hj _ (map_zero _) y
    simp only [hI, hF]
    have hfin1 : (Function.mulSupport fun v : Pl F => (c v)⁻¹).Finite := by
      refine (Filter.eventually_cofinite.1 hc1).subset fun v hv h => hv ?_
      simp [h]
    have hfin2 : (Function.mulSupport fun v : Pl F =>
        ev₁ v (φ v) (Function.extend j (fun i => evFin F v (y i)) 0)).Finite := by
      have := GlobalTheory.PureFactor.mulSupport_finite (κ := Fin n₁ × Fin d)
        (fun v x => ev₁ v (φ v) (Function.extend j x 0)) (by
          filter_upwards [hφv, hstd] with v h1 h2
          rw [h1, h2]
          exact std_extend hj v) y
      exact this
    rw [finprod_mul_distrib hfin1 hfin2, finprod_inv_distrib]
    ring
  refine ⟨(∏ᶠ v, c v)⁻¹ • (LinearMap.funLeft ℂ ℂ (fun y : Fin n₁ × Fin d → AF F => Function.extend j y 0) ∘ₗ e₁),
    R.comp ei₁, ev, ⟨?_, ?_, ?_, ?_⟩, (restr_surjective hj R hR).comp hsurj, hev, ?_⟩
  · intro Φ hΦ
    exact Submodule.smul_mem _ _ (GlobalTheory.T.extend_by_zero_mem_schA F j hj _ (hmaps Φ hΦ))
  · intro z Φ hΦ
    have h1 : incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ = incM F H.ι * z := by
      rw [show incM F (1 : Matrix (Fin d) (Fin d) E) = 1 from Matrix.map_one _ (map_zero _) (map_one _)]
      simp
    rw [h1]
    funext y
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.funLeft_apply, Function.comp_apply, Pi.smul_apply,
      smul_eq_mul]
    rw [hheis _ Φ hΦ]
    simp only [Darboux.rho, schr, hι, extend_dot hj, ← extend_add hj, Pi.smul_apply, smul_eq_mul,
      LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.funLeft_apply, Function.comp_apply]
    ring
  · intro u hu Φ hΦ
    obtain ⟨z, rfl⟩ := hu
    funext y
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.funLeft_apply, Function.comp_apply, Pi.smul_apply,
      smul_eq_mul]
    rw [hheis _ Φ hΦ]
    obtain ⟨h1, h2⟩ := hx z
    simp only [Darboux.rho, schr, h1, extend_dot_zero _ _ h2, zero_dotProduct, mul_zero, add_zero,
      AddChar.map_zero_eq_one, one_mul]
  · refine ⟨R.comp ei₁, ev, ?_, fun v => ⟨hev v, ?_⟩, ?_⟩
    · intro h
      obtain ⟨g, hg⟩ : ∃ g : SInf F (Fin n₁ × Fin d), g ≠ 0 := by
        obtain ⟨b, hb0⟩ : ∃ b : SInf F (Fin n₁ × Fin d), b 0 ≠ 0 := by
          let bb : ContDiffBump (0 : Fin n₁ × Fin d → mixedEmbedding.mixedSpace F) := ⟨1, 2, one_pos, one_lt_two⟩
          have hs : HasCompactSupport (fun x => ((bb x : ℝ) : ℂ)) :=
            bb.hasCompactSupport.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
          have hcd : ContDiff ℝ (⊤ : ℕ∞) (fun x => ((bb x : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp bb.contDiff
          refine ⟨hs.toSchwartzMap hcd, ?_⟩
          have h2 : bb 0 = 1 := bb.one_of_mem_closedBall (by simp [bb])
          simp [h2]
        exact ⟨b, fun h0 => hb0 (by rw [h0]; rfl)⟩
      obtain ⟨f, hf⟩ := (restr_surjective hj R hR).comp hsurj g
      apply hg
      rw [← hf]
      exact congrArg (fun T : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d) => T f) h
    · show (SB _).map ((c v)⁻¹ • (LinearMap.funLeft ℂ ℂ (fun y : Fin n₁ × Fin d → Fv F v => Function.extend j y 0) ∘ₗ ev₁ v)) = SB _
      rw [Submodule.map_smul _ _ _ (inv_ne_zero (hc0 v)), Submodule.map_comp, hSB v, GlobalTheory.T.extend_by_zero_schwartzBruhat_map F j hj v]
    · exact pureEq
  · exact pureEq
end GlobalTheory.ThK.EvTwoNeB

namespace GlobalTheory.ThK.EvTwoNeB

/- English proof (translation)
Introduce `hP F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ M χX χW om r s r' s' hPr H H' j₀ j₁ i₀ i₁ Mb omb r₁ s₁ M₁ hH hH' hPb hM₁ e₁ e₂ he₁ he₂`. Take `⟨S, ei, ev, hS, hsurj, hev, hl⟩` from `exists_isEv_onto B M Mb H hPr.base hPr.herm hPr.skew hPr.good hPb.herm hPb.good hH`. Take `⟨k, hk⟩` from `GlobalTheory.T.hermitian_adapted_plane_factor hP F E σ B n d X W M χX χW om r s r' s' hPr n₁ X₁ H j₀ j₁ Mb omb r₁ s₁ hH hPb e₁ he₁ S hS.maps hS.Heisenberg₂ hS.inv (GlobalTheory.T.eigen_intertwiner_good_models F E σ B n d n₁ d X W X₁ W M Mb H.ι 1 _ S hPr.good hPb.good hS)`. Take `⟨ei₂, ev₂, hei₂, hv₂, hl₂⟩` from `he₂.loc`. Choose the witnesses or unpack the hypotheses as in `⟨g, hg⟩ : ∃ g, ei₂ g ≠ 0 := by`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hei₂ (ContinuousLinearMap.ext h)`. Take `⟨f, rfl⟩` from `hsurj g`. Establish `hvacM : ∀ v, M.vac v ∈ SB _` using `fun v => (hPr.good.vac v).1`.

Use `⟨pure f M.vac, GlobalTheory.TensUniq.pure_mem_schA f M.vac hvacM hPr.good.std, fun h0 => ?_⟩` and prove the remaining obligations. Establish `h1 : S (pure f M.vac) = pure (ei f) Mb.vac`. Rewrite using `[hl f M.vac hvacM (Filter.Eventually.of_forall fun _ => rfl)]`. Conclude with `congrArg _ (funext hev)`. Establish `h2 : e₂ (S (pure f M.vac)) = pure (ei₂ (ei f)) M₁.vac`.

Rewrite using `[h1, hl₂ (ei f) Mb.vac (fun v => (hPb.good.vac v).1) (Filter.Eventually.of_forall fun _ => rfl)]`. Conclude with `congrArg _ (funext fun v => (hv₂ v).1)`. Establish `h3 : e₂ (S (pure f M.vac)) = 0`. Rewrite using `[hk _ (GlobalTheory.TensUniq.pure_mem_schA f M.vac hvacM hPr.good.std), map_smul, h0, smul_zero]`. Conclude with `GlobalTheory.ThK.EvNeZero.pure_ne_zero (ei₂ (ei f)) hg M₁.vac (fun v => (hM₁.vac v).2.1) hM₁.std (h2.symm.trans h3)`.
-/
theorem comp_ne_zero : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (H : Plane E n n₁) (H' : Plane E d d₁) (j₀ j₁ i₀ i₁ : ℕ) (Mb : Model σ X₁ W) (omb : Rep σ X₁ W) (r₁ s₁ : ℕ)
    (M₁ : Model σ X₁ W₁), H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B Mb χX χW omb r₁ s₁ r' s' → M₁.IsGood B.ψ →
    ∀ e₁ e₂, IsEv B M Mb H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e₁ → IsEv B Mb M₁ 1 H'.ι (iso0 n₁ H') e₂ →
    ∃ Φ ∈ schA F (Fin n × Fin d), e₂ (e₁ Φ) ≠ 0 := by
  intro hP F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ M χX χW om r s r' s' hPr H H' j₀ j₁ i₀ i₁ Mb omb r₁ s₁ M₁ hH hH' hPb hM₁
    e₁ e₂ he₁ he₂
  obtain ⟨S, ei, ev, hS, hsurj, hev, hl⟩ :=
    exists_isEv_onto B M Mb H hPr.base hPr.herm hPr.skew hPr.good hPb.herm hPb.good hH
  obtain ⟨k, hk⟩ := GlobalTheory.T.hermitian_adapted_plane_factor hP F E σ B n d X W M χX χW om r s r' s' hPr n₁ X₁ H j₀ j₁ Mb omb r₁ s₁ hH hPb e₁ he₁ S
    hS.maps hS.Heisenberg₂ hS.inv
    (GlobalTheory.T.eigen_intertwiner_good_models F E σ B n d n₁ d X W X₁ W M Mb H.ι 1 _ S hPr.good hPb.good hS)
  obtain ⟨ei₂, ev₂, hei₂, hv₂, hl₂⟩ := he₂.loc
  obtain ⟨g, hg⟩ : ∃ g, ei₂ g ≠ 0 := by
    by_contra h
    push_neg at h
    exact hei₂ (ContinuousLinearMap.ext h)
  obtain ⟨f, rfl⟩ := hsurj g
  have hvacM : ∀ v, M.vac v ∈ SB _ := fun v => (hPr.good.vac v).1
  refine ⟨pure f M.vac, GlobalTheory.TensUniq.pure_mem_schA f M.vac hvacM hPr.good.std, fun h0 => ?_⟩
  have h1 : S (pure f M.vac) = pure (ei f) Mb.vac := by
    rw [hl f M.vac hvacM (Filter.Eventually.of_forall fun _ => rfl)]
    exact congrArg _ (funext hev)
  have h2 : e₂ (S (pure f M.vac)) = pure (ei₂ (ei f)) M₁.vac := by
    rw [h1, hl₂ (ei f) Mb.vac (fun v => (hPb.good.vac v).1) (Filter.Eventually.of_forall fun _ => rfl)]
    exact congrArg _ (funext fun v => (hv₂ v).1)
  have h3 : e₂ (S (pure f M.vac)) = 0 := by
    rw [hk _ (GlobalTheory.TensUniq.pure_mem_schA f M.vac hvacM hPr.good.std), map_smul, h0, smul_zero]
  exact GlobalTheory.ThK.EvNeZero.pure_ne_zero (ei₂ (ei f)) hg M₁.vac (fun v => (hM₁.vac v).2.1) hM₁.std (h2.symm.trans h3)

end GlobalTheory.ThK.EvTwoNeB
