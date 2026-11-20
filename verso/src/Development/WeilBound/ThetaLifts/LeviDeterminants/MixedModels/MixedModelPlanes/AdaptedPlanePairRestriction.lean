import Mathlib
import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixedModelPlanes.Imports
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixedModelPlanes.ExistsAdaptedBasisHermitian
import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixedModelPlanes.DarbouxCoordinatesGoodModel
import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixedModelPlanes.AdaptedBasisHermitianUnique
import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixedModelPlanes.ExistsRestrictionExtendByZero
import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixedModelPlanes.ExtendByZeroMemSchA
import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixedModelPlanes.ExtendByZeroSchwartzBruhatMap

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThKMixXEx

/- English proof (translation)
Use function extensionality and compare the values at `k`. Distinguish the cases in `h : ∃ a, j a = k`. Take `⟨a, rfl⟩` from `h`. Simplify using `[hj.extend_apply]`. Simplify using `[Function.extend_apply' _ _ _ h, hg]`.
-/
theorem extend_map_m {α β M N : Type} {j : α → β} (hj : Function.Injective j) [Zero M] [Zero N] (g : M → N) (hg : g 0 = 0)
    (y : α → M) : (fun k => g (Function.extend j y 0 k)) = Function.extend j (fun i => g (y i)) 0 := by
  funext k
  by_cases h : ∃ a, j a = k
  · obtain ⟨a, rfl⟩ := h
    simp [hj.extend_apply]
  · simp [Function.extend_apply' _ _ _ h, hg]

/- English proof (translation)
Use function extensionality and compare the values at `k`. Distinguish the cases in `h : ∃ a, j a = k`. Take `⟨a, rfl⟩` from `h`. Simplify using `[hj.extend_apply]`. Simplify using `[Function.extend_apply' _ _ _ h]`.
-/
theorem extend_zero'_m {α β M : Type} {j : α → β} (hj : Function.Injective j) [Zero M] :
    Function.extend j (0 : α → M) 0 = 0 := by
  funext k
  by_cases h : ∃ a, j a = k
  · obtain ⟨a, rfl⟩ := h
    simp [hj.extend_apply]
  · simp [Function.extend_apply' _ _ _ h]

/- English proof (translation)
Use function extensionality and compare the values at `k`. Distinguish the cases in `h : ∃ x, j x = k`. Take `⟨x, rfl⟩` from `h`. Simplify using `[hj.extend_apply]`. Simplify using `[Function.extend_apply' _ _ _ h]`.
-/
theorem extend_add_m {α β M : Type} {j : α → β} (hj : Function.Injective j) [AddZeroClass M] (a b : α → M) :
    Function.extend j (a + b) 0 = Function.extend j a 0 + Function.extend j b 0 := by
  funext k
  by_cases h : ∃ x, j x = k
  · obtain ⟨x, rfl⟩ := h
    simp [hj.extend_apply]
  · simp [Function.extend_apply' _ _ _ h]

/- English proof (translation)
Rewrite using `[← Finset.sum_subset (Finset.subset_univ (Finset.univ.map ⟨j, hj⟩)) (fun k _ hk => by`. Rewrite using `[Function.extend_apply' (f := j) f (0 : β → R) k (fun ⟨a, ha⟩ => hk (Finset.mem_map.2 ⟨a, Finset.mem_univ _, ha⟩))]`. Use the proof step `rfl),`. Use the proof step `Finset.sum_map]`. Conclude with `Finset.sum_congr rfl fun i _ => hj.extend_apply _ _ _`.
-/
theorem sum_extend_m {α β R : Type} [Fintype α] [Fintype β] {j : α → β} (hj : Function.Injective j) [AddCommMonoid R]
    (f : α → R) : ∑ k, Function.extend j f 0 k = ∑ i, f i := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map ⟨j, hj⟩)) (fun k _ hk => by
      rw [Function.extend_apply' (f := j) f (0 : β → R) k (fun ⟨a, ha⟩ => hk (Finset.mem_map.2 ⟨a, Finset.mem_univ _, ha⟩))]; rfl),
    Finset.sum_map]
  exact Finset.sum_congr rfl fun i _ => hj.extend_apply _ _ _

/- English proof (translation)
Establish `: (fun k => Function.extend j a 0 k * Function.extend j b 0 k) = Function.extend j (fun i => a i * b i) 0`. Use function extensionality and compare the values at `k`. Distinguish the cases in `h : ∃ x, j x = k`. Take `⟨x, rfl⟩` from `h`. Simplify using `[hj.extend_apply]`.

Simplify using `[Function.extend_apply' _ _ _ h]`. Simplify using `only [dotProduct]`. Rewrite using `[show (∑ k, Function.extend j a 0 k * Function.extend j b 0 k) = ∑ k, Function.extend j (fun i => a i * b i) 0 k from Finset.sum_congr rfl fun k _ => congrFun this k, sum_extend_m hj]`.
-/
theorem extend_dot_m {α β R : Type} [Fintype α] [Fintype β] {j : α → β} (hj : Function.Injective j) [CommRing R]
    (a b : α → R) : Function.extend j a 0 ⬝ᵥ Function.extend j b 0 = a ⬝ᵥ b := by
  have : (fun k => Function.extend j a 0 k * Function.extend j b 0 k) = Function.extend j (fun i => a i * b i) 0 := by
    funext k
    by_cases h : ∃ x, j x = k
    · obtain ⟨x, rfl⟩ := h
      simp [hj.extend_apply]
    · simp [Function.extend_apply' _ _ _ h]
  simp only [dotProduct]
  rw [show (∑ k, Function.extend j a 0 k * Function.extend j b 0 k) = ∑ k, Function.extend j (fun i => a i * b i) 0 k from
    Finset.sum_congr rfl fun k _ => congrFun this k, sum_extend_m hj]

/- English proof (translation)
Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : ∃ x, j x = k`. Take `⟨x, rfl⟩` from `h`. Simplify using `[hq]`. Simplify using `[Function.extend_apply' _ _ _ h]`.
-/
theorem extend_dot_zero_m {α β R : Type} [Fintype α] [Fintype β] {j : α → β} [CommRing R] (y : α → R) (q : β → R)
    (hq : ∀ k, q (j k) = 0) : Function.extend j y 0 ⬝ᵥ q = 0 := by
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases h : ∃ x, j x = k
  · obtain ⟨x, rfl⟩ := h
    simp [hq]
  · simp [Function.extend_apply' _ _ _ h]

end GlobalTheory.ThKMixXEx

namespace GlobalTheory.ThKMixXEx

/- English proof (translation)
Use function extensionality and compare the values at `y`. Establish `key : (∀ i, Function.extend j y 0 i ∈ v.adicCompletionIntegers F) ↔ ∀ i, y i ∈ v.adicCompletionIntegers F`. Prove the components needed by the constructor for the conclusion. Introduce `h i`. Simplify `h (j i)` using `[hj.extend_apply]`.

Introduce `h k`. Distinguish the cases in `hk : ∃ a, j a = k`. Take `⟨a, rfl⟩` from `hk`. Simplify `h a` using `[hj.extend_apply]`. Simplify using `[Function.extend_apply' _ _ _ hk]`.

Distinguish the cases in `hy : ∀ i, y i ∈ v.adicCompletionIntegers F`. Rewrite using `[Set.indicator_of_mem (show y ∈ {x : κ₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from hy), Set.indicator_of_mem (show Function.extend j y 0 ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from key.2 hy)]`. Both sides reduce to the same expression. Rewrite using `[Set.indicator_of_notMem (show y ∉ {x : κ₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from hy), Set.indicator_of_notMem (show Function.extend j y 0 ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from fun h => hy (key.1 h))]`.
-/
theorem std_extend_m {F : Type} [Field F] [NumberField F] {κ₁ κ : Type} {j : κ₁ → κ} (hj : Function.Injective j) (v : Pl F) :
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
Introduce `F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁`. Take `⟨j, co, hj, hrat, hι, hx, hy⟩` from `PositivityTheory.Mix.T.exists_adapted_basis_hermitian F E σ B n d X W r s r' s' hP.base hP.herm hP.skew n₁ X₁ H j₀ j₁ M₁ r₁ s₁ hP₁.herm hH hP₁.good`. Take `⟨e₁, ei₁, ev₁, hsurj, hmaps, hheis, hSB, hvac, hstd, hpure⟩` from `PositivityTheory.Mix.T.darboux_coordinates_good_model F E σ B n d X W M r s r' s' hP.base hP.herm hP.skew hP.good co hrat`. Establish `hres` using `fun v => PositivityTheory.Mix.T.adapted_basis_hermitian_unique F E σ B n d X W r s r' s' hP.base hP.herm hP.skew n₁ X₁ H j₀ j₁ M₁ r₁ s₁ hP₁.herm hH hP₁.good j co hj hι hx hy v _ (hvac v)`. Use `choose c hc0 hc using hres`.

Establish `hc1 : ∀ᶠ v in cofinite, c v = 1` using `by filter_upwards [hstd, hP₁.good.std] with v h1 h2`. Establish `h'` using `hc v`. Rewrite `h'` using `[h1, h2, std_extend_m hj v]`. Establish `h` using `congrFun h' 0`. Establish `hm : (0 : Fin n₁ × Fin d → Fv F v) ∈ {x : Fin n₁ × Fin d → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F}` using `fun i => zero_mem _`.

Rewrite `h` using `[Pi.smul_apply, Set.indicator_of_mem hm, smul_eq_mul]`. Simplify using `using h.symm`. Take `⟨R, hR⟩` from `PositivityTheory.Mix.T.exists_restriction_extend_by_zero F j hj`. Use `⟨(∏ᶠ v, c v)⁻¹ • (LinearMap.funLeft ℂ ℂ (fun y : Fin n₁ × Fin d → AF F => Function.extend j y 0) ∘ₗ e₁), ⟨?_, ?_, ?_, ?_⟩⟩` and prove the remaining obligations. Introduce `Φ hΦ`.

Conclude with `Submodule.smul_mem _ _ (PositivityTheory.Mix.T.extend_by_zero_mem_schA F j hj _ (hmaps Φ hΦ))`. Introduce `z Φ hΦ`. Establish `h1 : incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ = incM F H.ι * z`. Rewrite using `[show incM F (1 : Matrix (Fin d) (Fin d) E) = 1 from Matrix.map_one _ (map_zero _) (map_one _)]`. Simplify using the standard rewrite rules.

Rewrite using `[h1]`. Use function extensionality and compare the values at `y`. Simplify using `only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.funLeft_apply, Function.comp_apply, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[hheis _ Φ hΦ]`. Simplify using `only [Darboux.rho, schr, hι, extend_dot_m hj, ← extend_add_m hj, Pi.smul_apply, smul_eq_mul, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.funLeft_apply, Function.comp_apply]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `u hu Φ hΦ`. Take `⟨z, rfl⟩` from `hu`. Use function extensionality and compare the values at `y`. Simplify using `only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.funLeft_apply, Function.comp_apply, Pi.smul_apply, smul_eq_mul]`.

Rewrite using `[hheis _ Φ hΦ]`. Take `⟨h1, h2⟩` from `hx z`. Simplify using `only [Darboux.rho, schr, h1, extend_dot_zero_m _ _ h2, zero_dotProduct, mul_zero, add_zero, AddChar.map_zero_eq_one, one_mul]`. Choose the witnesses or unpack the hypotheses as in `⟨b, hb0⟩ : ∃ b : SInf F (Fin n × Fin d), b 0 ≠ 0 := by`. Set `bb : ContDiffBump (0 : Fin n × Fin d → mixedEmbedding.mixedSpace F)` to `⟨1, 2, one_pos, one_lt_two⟩`.

Establish `hs : HasCompactSupport (fun x => ((bb x : ℝ) : ℂ))` using `bb.hasCompactSupport.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)`. Establish `hcd : ContDiff ℝ (⊤ : ℕ∞) (fun x => ((bb x : ℝ) : ℂ))` using `Complex.ofRealCLM.contDiff.comp bb.contDiff`. Use `⟨hs.toSchwartzMap hcd, ?_⟩` and prove the remaining obligations. Establish `h2 : bb 0 = 1` using `bb.one_of_mem_closedBall (by simp [bb])`. Simplify using `[h2]`.

Take `⟨f₀, hf₀⟩` from `hsurj b`. Use `⟨R.comp ei₁, fun v => (c v)⁻¹ • (LinearMap.funLeft ℂ ℂ (fun y : Fin n₁ × Fin d → Fv F v => Function.extend j y 0) ∘ₗ ev₁ v), ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `h`. Use `congrArg (fun T : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d) => T f₀ 0) h` as an intermediate fact. Simplify using `only [ContinuousLinearMap.comp_apply, hR, hf₀, extend_zero'_m hj, ContinuousLinearMap.zero_apply, SchwartzMap.zero_apply] at this`.

Conclude with `hb0 this`. Introduce `v`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.smul_apply, LinearMap.comp_apply]`. Rewrite using `[show LinearMap.funLeft ℂ ℂ (fun y : Fin n₁ × Fin d → Fv F v => Function.extend j y 0) (ev₁ v (M.vac v)) = c v • M₁.vac v from hc v, smul_smul, inv_mul_cancel₀ (hc0 v), one_smul]`.

Rewrite using `[Submodule.map_smul _ _ _ (inv_ne_zero (hc0 v)), Submodule.map_comp, hSB v, PositivityTheory.Mix.T.extend_by_zero_schwartzBruhat_map F j hj v]`. Introduce `f φ hφ hφv`. Use function extensionality and compare the values at `y`. Rewrite using `[LinearMap.smul_apply, LinearMap.comp_apply, hpure f φ hφ hφv]`. Simplify using `only [LinearMap.funLeft_apply, Function.comp_apply, Pi.smul_apply, smul_eq_mul, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, ContinuousLinearMap.comp_apply, hR, LinearMap.smul_apply, LinearMap.comp_apply]`.

Establish `hI : (fun i => evI F (Function.extend j y 0 i)) = Function.extend j (fun i => evI F (y i)) 0` using `extend_map_m hj (evI F) (by unfold evI; exact map_zero _) y`. Establish `hF : ∀ v : Pl F, (fun i => evFin F v (Function.extend j y 0 i)) = Function.extend j (fun i => evFin F v (y i)) 0` using `fun v => extend_map_m hj _ (map_zero _) y`. Simplify using `only [hI, hF]`. Establish `hfin1 : (Function.mulSupport fun v : Pl F => (c v)⁻¹).Finite`. Use `(Filter.eventually_cofinite.1 hc1).subset fun v hv h => hv ?_` and prove the remaining obligations.

Simplify using `[h]`. Establish `hfin2 : (Function.mulSupport fun v : Pl F => ev₁ v (φ v) (Function.extend j (fun i => evFin F v (y i)) 0)).Finite`. Use `GlobalTheory.PureFactor.mulSupport_finite (κ := Fin n₁ × Fin d) (fun v x => ev₁ v (φ v) (Function.extend j x 0)) (by filter_upwards [hφv, hstd] with v h1 h2` as an intermediate fact. Rewrite using `[h1, h2]`. Conclude with `std_extend_m hj v) y`.

Conclude with `this`. Rewrite using `[finprod_mul_distrib hfin1 hfin2, finprod_inv_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_isEv_mixedX_m : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∃ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁
  classical
  obtain ⟨j, co, hj, hrat, hι, hx, hy⟩ :=
    PositivityTheory.Mix.T.exists_adapted_basis_hermitian F E σ B n d X W r s r' s' hP.base hP.herm hP.skew n₁ X₁ H j₀ j₁ M₁ r₁ s₁ hP₁.herm hH hP₁.good
  obtain ⟨e₁, ei₁, ev₁, hsurj, hmaps, hheis, hSB, hvac, hstd, hpure⟩ :=
    PositivityTheory.Mix.T.darboux_coordinates_good_model F E σ B n d X W M r s r' s' hP.base hP.herm hP.skew hP.good co hrat
  have hres := fun v => PositivityTheory.Mix.T.adapted_basis_hermitian_unique F E σ B n d X W r s r' s' hP.base hP.herm hP.skew n₁ X₁ H j₀ j₁ M₁ r₁ s₁ hP₁.herm hH
    hP₁.good j co hj hι hx hy v _ (hvac v)
  choose c hc0 hc using hres
  have hc1 : ∀ᶠ v in cofinite, c v = 1 := by
    filter_upwards [hstd, hP₁.good.std] with v h1 h2
    have h' := hc v
    rw [h1, h2, std_extend_m hj v] at h'
    have h := congrFun h' 0
    have hm : (0 : Fin n₁ × Fin d → Fv F v) ∈ {x : Fin n₁ × Fin d → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} :=
      fun i => zero_mem _
    rw [Pi.smul_apply, Set.indicator_of_mem hm, smul_eq_mul] at h
    simpa using h.symm
  obtain ⟨R, hR⟩ := PositivityTheory.Mix.T.exists_restriction_extend_by_zero F j hj
  refine ⟨(∏ᶠ v, c v)⁻¹ • (LinearMap.funLeft ℂ ℂ (fun y : Fin n₁ × Fin d → AF F => Function.extend j y 0) ∘ₗ e₁),
    ⟨?_, ?_, ?_, ?_⟩⟩
  · intro Φ hΦ
    exact Submodule.smul_mem _ _ (PositivityTheory.Mix.T.extend_by_zero_mem_schA F j hj _ (hmaps Φ hΦ))
  · intro z Φ hΦ
    have h1 : incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ = incM F H.ι * z := by
      rw [show incM F (1 : Matrix (Fin d) (Fin d) E) = 1 from Matrix.map_one _ (map_zero _) (map_one _)]
      simp
    rw [h1]
    funext y
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.funLeft_apply, Function.comp_apply, Pi.smul_apply,
      smul_eq_mul]
    rw [hheis _ Φ hΦ]
    simp only [Darboux.rho, schr, hι, extend_dot_m hj, ← extend_add_m hj, Pi.smul_apply, smul_eq_mul,
      LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.funLeft_apply, Function.comp_apply]
    ring
  · intro u hu Φ hΦ
    obtain ⟨z, rfl⟩ := hu
    funext y
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.funLeft_apply, Function.comp_apply, Pi.smul_apply,
      smul_eq_mul]
    rw [hheis _ Φ hΦ]
    obtain ⟨h1, h2⟩ := hx z
    simp only [Darboux.rho, schr, h1, extend_dot_zero_m _ _ h2, zero_dotProduct, mul_zero, add_zero,
      AddChar.map_zero_eq_one, one_mul]
  · obtain ⟨b, hb0⟩ : ∃ b : SInf F (Fin n × Fin d), b 0 ≠ 0 := by
      let bb : ContDiffBump (0 : Fin n × Fin d → mixedEmbedding.mixedSpace F) := ⟨1, 2, one_pos, one_lt_two⟩
      have hs : HasCompactSupport (fun x => ((bb x : ℝ) : ℂ)) :=
        bb.hasCompactSupport.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
      have hcd : ContDiff ℝ (⊤ : ℕ∞) (fun x => ((bb x : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp bb.contDiff
      refine ⟨hs.toSchwartzMap hcd, ?_⟩
      have h2 : bb 0 = 1 := bb.one_of_mem_closedBall (by simp [bb])
      simp [h2]
    obtain ⟨f₀, hf₀⟩ := hsurj b
    refine ⟨R.comp ei₁, fun v => (c v)⁻¹ •
      (LinearMap.funLeft ℂ ℂ (fun y : Fin n₁ × Fin d → Fv F v => Function.extend j y 0) ∘ₗ ev₁ v), ?_, ?_, ?_⟩
    · intro h
      have := congrArg (fun T : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d) => T f₀ 0) h
      simp only [ContinuousLinearMap.comp_apply, hR, hf₀, extend_zero'_m hj, ContinuousLinearMap.zero_apply,
        SchwartzMap.zero_apply] at this
      exact hb0 this
    · intro v
      refine ⟨?_, ?_⟩
      · rw [LinearMap.smul_apply, LinearMap.comp_apply]
        rw [show LinearMap.funLeft ℂ ℂ (fun y : Fin n₁ × Fin d → Fv F v => Function.extend j y 0) (ev₁ v (M.vac v)) =
          c v • M₁.vac v from hc v, smul_smul, inv_mul_cancel₀ (hc0 v), one_smul]
      · rw [Submodule.map_smul _ _ _ (inv_ne_zero (hc0 v)), Submodule.map_comp, hSB v, PositivityTheory.Mix.T.extend_by_zero_schwartzBruhat_map F j hj v]
    · intro f φ hφ hφv
      funext y
      rw [LinearMap.smul_apply, LinearMap.comp_apply, hpure f φ hφ hφv]
      simp only [LinearMap.funLeft_apply, Function.comp_apply, Pi.smul_apply, smul_eq_mul, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure,
        ContinuousLinearMap.comp_apply, hR, LinearMap.smul_apply, LinearMap.comp_apply]
      have hI : (fun i => evI F (Function.extend j y 0 i)) = Function.extend j (fun i => evI F (y i)) 0 :=
        extend_map_m hj (evI F) (by unfold evI; exact map_zero _) y
      have hF : ∀ v : Pl F, (fun i => evFin F v (Function.extend j y 0 i)) =
          Function.extend j (fun i => evFin F v (y i)) 0 := fun v => extend_map_m hj _ (map_zero _) y
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
            exact std_extend_m hj v) y
        exact this
      rw [finprod_mul_distrib hfin1 hfin2, finprod_inv_distrib]
      ring

end GlobalTheory.ThKMixXEx
