import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IntegralFiniteAdeleCompactClosedMultiples

noncomputable section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.RealLift

section Laws

open scoped Classical

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

variable (F κ) in

def intPts : Set (κ → Af F) :=
  Set.univ.pi fun _ => {a : Af F | ∀ v, a v ∈ v.adicCompletionIntegers F}

/- English proof (translation)
Use `haveI := GlobalTheory.IntegralFinAdele.t2Space_finiteAdeleRing' F`. Establish `hO : IsOpen {a : Af F | ∀ v, a v ∈ v.adicCompletionIntegers F}` using `RestrictedProduct.isOpen_forall_mem fun v => Valued.isOpen_valuationSubring _`. Establish `hC : IsCompact {a : Af F | ∀ v, a v ∈ v.adicCompletionIntegers F}` using `(GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties F).1`. Establish `hU : IsOpen (intPts F κ)` using `isOpen_set_pi Set.finite_univ fun _ _ => hO`. Establish `hK : IsCompact (intPts F κ)` using `isCompact_univ_pi fun _ => hC`.

Use `⟨?_, HasCompactSupport.intro' hK hK.isClosed fun x hx => Set.indicator_of_notMem hx _⟩` and prove the remaining obligations. Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `x`. Distinguish the cases in `hx : x ∈ intPts F κ`. Use `filter_upwards [hU.mem_nhds hx] with y hy`.

Simplify using `[Set.indicator_of_mem hy, Set.indicator_of_mem hx]`. Use `filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hx] with y hy`. Simplify using `[Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]`.
-/
theorem indicator_intPts_mem_SB : (intPts F κ).indicator (1 : (κ → Af F) → ℂ) ∈ SB (κ → Af F) := by
  haveI := GlobalTheory.IntegralFinAdele.t2Space_finiteAdeleRing' F
  have hO : IsOpen {a : Af F | ∀ v, a v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_mem fun v => Valued.isOpen_valuationSubring _
  have hC : IsCompact {a : Af F | ∀ v, a v ∈ v.adicCompletionIntegers F} :=
    (GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties F).1
  have hU : IsOpen (intPts F κ) := isOpen_set_pi Set.finite_univ fun _ _ => hO
  have hK : IsCompact (intPts F κ) := isCompact_univ_pi fun _ => hC
  refine ⟨?_, HasCompactSupport.intro' hK hK.isClosed fun x hx => Set.indicator_of_notMem hx _⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ intPts F κ
  · filter_upwards [hU.mem_nhds hx] with y hy
    simp [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
  · filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hx] with y hy
    simp [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

/- English proof (translation)
Introduce `_ _ v` and use `zero_mem _`.
-/
theorem zero_mem_intPts : (0 : κ → Af F) ∈ intPts F κ := fun _ _ v => zero_mem _

def ptAt (a : κ → mixedEmbedding.mixedSpace F) (y : κ → Af F) : κ → AF F :=
  fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (a i), y i)

/- English proof (translation)
Simplify using `[pureA, ptAt]`.
-/
theorem pureA_ptAt (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → Af F) → ℂ) (a : κ → mixedEmbedding.mixedSpace F)
    (y : κ → Af F) : pureA F f g (ptAt a y) = f a * g y := by
  simp [pureA, ptAt]

/- English proof (translation)
Establish `h` using `congrFun (hz ((0, 1) : AF F) (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F))) i`. Establish `h2 : (1 : Af F) * (z i).2 = 0` using `congrArg Prod.snd h`. Rewrite `h2` using `[one_mul]`. Then use the resulting hypothesis.
-/
theorem fin_eq_zero_of_at {z : κ → AF F} (hz : At (evI F) z) (i : κ) : (z i).2 = 0 := by
  have h := congrFun (hz ((0, 1) : AF F) (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F))) i
  have h2 : (1 : Af F) * (z i).2 = 0 := congrArg Prod.snd h
  rwa [one_mul] at h2

/- English proof (translation)
Introduce `u hu`. Establish `hu1 : u.1 = 0` using `(InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)`. Use function extensionality and compare the values at `i`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `u.1 * (z i).1 = 0`.

Rewrite using `[hu1, zero_mul]`. Express the relevant statement in the definitionally equal form `u.2 * (z i).2 = 0`. Rewrite using `[hz i, mul_zero]`.
-/
theorem at_of_fin_eq_zero {z : κ → AF F} (hz : ∀ i, (z i).2 = 0) : At (evI F) z := by
  intro u hu
  have hu1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
  funext i
  refine Prod.ext ?_ ?_
  · change u.1 * (z i).1 = 0
    rw [hu1, zero_mul]
  · change u.2 * (z i).2 = 0
    rw [hz i, mul_zero]

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [tens, pureA, evI]`. Use `congr 1`. Establish `h` using `hr (fun i => ((0 : Ainf F), (x i).2)) (fun i => ((x i).1, (0 : Af F))) (at_of_fin_eq_zero fun i => rfl)`. Rewrite using `[← h]`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Conclude with `Prod.ext (zero_add _).symm (add_zero _).symm`.
-/
theorem tens_eq_pureA (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) {r : (κ → AF F) → ℂ}
    (hr : ∀ x z, At (evI F) z → r (x + z) = r x) :
    tens (evI F) f r = pureA F f (fun y => r (fun i => ((0 : Ainf F), y i))) := by
  funext x
  simp only [tens, pureA, evI]
  congr 1
  have h := hr (fun i => ((0 : Ainf F), (x i).2)) (fun i => ((x i).1, (0 : Af F)))
    (at_of_fin_eq_zero fun i => rfl)
  rw [← h]
  congr 1
  funext i
  exact Prod.ext (zero_add _).symm (add_zero _).symm

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨a, ha⟩ : ∃ a, f a ≠ 0 := by`. Assume the negation of the conclusion as `h0`. Use `push_neg at h0`. Conclude with `hf (SchwartzMap.ext h0)`. Set `L : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → Af F) → ℂ)` to `LinearMap.funLeft ℂ ℂ (ptAt a)`.

Establish `hle : schA F κ ≤ (SB (κ → Af F)).comap L`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨f', g', hg', rfl⟩`. Express the relevant statement in the definitionally equal form `(fun y => pureA F f' g' (ptAt a y)) ∈ SB (κ → Af F)`. Repeatedly rewrite using `[pureA_ptAt]`.

Conclude with `(SB (κ → Af F)).smul_mem (f' a) hg'`. Establish `h1 : L (pureA F f g) ∈ SB (κ → Af F)` using `hle h`. Establish `h2 : L (pureA F f g) = f a • g`. Use function extensionality and compare the values at `y`. Express the relevant statement in the definitionally equal form `pureA F f g (ptAt a y) = _`.

Rewrite using `[pureA_ptAt]`. Both sides reduce to the same expression. Rewrite `h1` using `[h2]`. Establish `h3` using `(SB (κ → Af F)).smul_mem (f a)⁻¹ h1`. Rewrite `h3` using `[smul_smul, inv_mul_cancel₀ ha, one_smul]`. Then use the resulting hypothesis.
-/
theorem mem_SB_of_pureA_mem {f : SInf F κ} (hf : f ≠ 0) {g : (κ → Af F) → ℂ} (h : pureA F f g ∈ schA F κ) :
    g ∈ SB (κ → Af F) := by
  obtain ⟨a, ha⟩ : ∃ a, f a ≠ 0 := by
    by_contra h0
    push_neg at h0
    exact hf (SchwartzMap.ext h0)
  let L : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → Af F) → ℂ) := LinearMap.funLeft ℂ ℂ (ptAt a)
  have hle : schA F κ ≤ (SB (κ → Af F)).comap L := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f', g', hg', rfl⟩
    change (fun y => pureA F f' g' (ptAt a y)) ∈ SB (κ → Af F)
    simp_rw [pureA_ptAt]
    exact (SB (κ → Af F)).smul_mem (f' a) hg'
  have h1 : L (pureA F f g) ∈ SB (κ → Af F) := hle h
  have h2 : L (pureA F f g) = f a • g := by
    funext y
    change pureA F f g (ptAt a y) = _
    rw [pureA_ptAt]
    rfl
  rw [h2] at h1
  have h3 := (SB (κ → Af F)).smul_mem (f a)⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ ha, one_smul] at h3

/- English proof (translation)
Introduce `g _`. Use `⟨g (fun i => (x i).2) • ((BoundedContinuousFunction.evalCLM ℂ (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1)).comp (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)), fun f => ?_⟩` and prove the remaining obligations. Simplify using `[pureA, mul_comm]`.
-/
theorem eval_mem_adm (x : κ → AF F) :
    (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g (fun i => (x i).2) • ((BoundedContinuousFunction.evalCLM ℂ
    (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1)).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)), fun f => ?_⟩
  simp [pureA, mul_comm]

end Laws

section Main

open scoped Classical

/- English proof (translation)
Introduce `F _ _ κ _ f f₁ f₂`. Use `set g₀ : (κ → Af F) → ℂ := (intPts F κ).indicator 1 with hg₀def`. Establish `hg₀ : g₀ ∈ SB (κ → Af F)` using `indicator_intPts_mem_SB`. Establish `hg₀0 : g₀ 0 = 1` using `by rw [hg₀def, Set.indicator_of_mem zero_mem_intPts]; rfl`. Use `set r₀ : (κ → AF F) → ℂ := fun x => g₀ (fun i => (x i).2) with hr₀def`.

Establish `hr₀inv : ∀ x z, At (evI F) z → r₀ (x + z) = r₀ x`. Introduce `x z hz`. Express the relevant statement in the definitionally equal form `g₀ (fun i => (x i + z i).2) = g₀ (fun i => (x i).2)`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Express the relevant statement in the definitionally equal form `(x i).2 + (z i).2 = (x i).2`. Rewrite using `[fin_eq_zero_of_at hz, add_zero]`. Establish `htens₀ : ∀ φ : (κ → mixedEmbedding.mixedSpace F) → ℂ, tens (evI F) φ r₀ = pureA F φ g₀` using `fun φ => rfl`. Establish `hrest₀ : Rest (evI F) (⇑f) r₀` using `⟨hr₀inv, by rw [htens₀]; exact Submodule.subset_span ⟨f, g₀, hg₀, rfl⟩⟩`. Establish `hext : ∀ h₁ h₂ : SInf F κ, (∀ a, pureA F h₁ g₀ (ptAt a 0) = pureA F h₂ g₀ (ptAt a 0)) → h₁ = h₂`.

Introduce `h₁ h₂ h`. Use extensionality with `a`. Simplify `h a` using `[pureA_ptAt, hg₀0]`. Establish `hzero : ∀ g : (κ → Af F) → ℂ, pureA F ⇑(0 : SInf F κ) g = 0`. Introduce `g`.

Use function extensionality and compare the values at `x`. Simplify using `[pureA]`. Establish `hzeroT : ∀ r : (κ → AF F) → ℂ, tens (evI F) ⇑(0 : SInf F κ) r = 0`. Introduce `r`. Use function extensionality and compare the values at `x`.

Simplify using `[tens]`. Use `⟨?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `T hT0 hSD r hr x`. Distinguish the cases in `hf : f = 0`. Substitute `hf` using the available equality.

Establish `hf₁ : f₁ = 0` using `hext _ _ fun a => by`. Establish `h` using `hSD g₀ hg₀ _ (eval_mem_adm (ptAt a 0))`. Simplify using `only [LinearMap.proj_apply, hzero, hT0] at h`. Rewrite using `[hzero]`. Conclude with `(h.unique (hasDerivAt_const 0 (0 : ℂ)))`.

Substitute `hf₁` using the available equality. Rewrite using `[hzeroT]`. Simplify using `only [hT0, Pi.zero_apply]`. Conclude with `hasDerivAt_const 0 (0 : ℂ)`. Establish `hg : (fun y => r (fun i => ((0 : Ainf F), y i))) ∈ SB (κ → Af F)` using `mem_SB_of_pureA_mem hf (tens_eq_pureA (⇑f) hr.1 ▸ hr.2)`.

Establish `h` using `hSD _ hg _ (eval_mem_adm x)`. Rewrite using `[tens_eq_pureA (⇑f) hr.1, tens_eq_pureA (⇑f₁) hr.1]`. Conclude with `h`. Introduce `T hT0 hSA r hr`. Distinguish the cases in `hf : f = 0`.

Substitute `hf` using the available equality. Establish `hf₁ : f₁ = 0` using `hext _ _ fun a => by`. Establish `h` using `hSA g₀ hg₀`. Rewrite `h` using `[hzero, hT0]`. Rewrite using `[← h, hzero]`.

Substitute `hf₁` using the available equality. Rewrite using `[hzeroT, hT0]`. Establish `hg : (fun y => r (fun i => ((0 : Ainf F), y i))) ∈ SB (κ → Af F)` using `mem_SB_of_pureA_mem hf (tens_eq_pureA (⇑f) hr.1 ▸ hr.2)`. Rewrite using `[tens_eq_pureA (⇑f) hr.1, tens_eq_pureA (⇑f₁) hr.1]`. Conclude with `hSA _ hg`.

Introduce `T h₁ h₂`. Use `hext _ _ fun a => ?_` and prove the remaining obligations. Establish `e₁` using `h₁ r₀ hrest₀ (ptAt a 0)`. Establish `e₂` using `h₂ r₀ hrest₀ (ptAt a 0)`. Rewrite `e₁`, `e₂` using `[htens₀]`.

Conclude with `e₁.unique e₂`. Introduce `T h₁ h₂`. Use `hext _ _ fun a => ?_` and prove the remaining obligations. Establish `e` using `(h₁ r₀ hrest₀).symm.trans (h₂ r₀ hrest₀)`. Rewrite `e` using `[htens₀, htens₀]`.

Conclude with `congrFun e (ptAt a 0)`. Introduce `T h₁ h₂`. Use `hext _ _ fun a => ?_` and prove the remaining obligations. Establish `e₁` using `h₁ g₀ hg₀ _ (eval_mem_adm (ptAt a 0))`. Establish `e₂` using `h₂ g₀ hg₀ _ (eval_mem_adm (ptAt a 0))`.

Conclude with `e₁.unique e₂`.
-/
theorem actsLaws : ActsLaws := by
  intro F _ _ κ _ f f₁ f₂
  set g₀ : (κ → Af F) → ℂ := (intPts F κ).indicator 1 with hg₀def
  have hg₀ : g₀ ∈ SB (κ → Af F) := indicator_intPts_mem_SB
  have hg₀0 : g₀ 0 = 1 := by rw [hg₀def, Set.indicator_of_mem zero_mem_intPts]; rfl

  set r₀ : (κ → AF F) → ℂ := fun x => g₀ (fun i => (x i).2) with hr₀def
  have hr₀inv : ∀ x z, At (evI F) z → r₀ (x + z) = r₀ x := by
    intro x z hz
    change g₀ (fun i => (x i + z i).2) = g₀ (fun i => (x i).2)
    congr 1
    funext i
    change (x i).2 + (z i).2 = (x i).2
    rw [fin_eq_zero_of_at hz, add_zero]
  have htens₀ : ∀ φ : (κ → mixedEmbedding.mixedSpace F) → ℂ, tens (evI F) φ r₀ = pureA F φ g₀ := fun φ => rfl
  have hrest₀ : Rest (evI F) (⇑f) r₀ := ⟨hr₀inv, by rw [htens₀]; exact Submodule.subset_span ⟨f, g₀, hg₀, rfl⟩⟩

  have hext : ∀ h₁ h₂ : SInf F κ, (∀ a, pureA F h₁ g₀ (ptAt a 0) = pureA F h₂ g₀ (ptAt a 0)) → h₁ = h₂ := by
    intro h₁ h₂ h
    ext a
    simpa [pureA_ptAt, hg₀0] using h a

  have hzero : ∀ g : (κ → Af F) → ℂ, pureA F ⇑(0 : SInf F κ) g = 0 := by
    intro g; funext x; simp [pureA]
  have hzeroT : ∀ r : (κ → AF F) → ℂ, tens (evI F) ⇑(0 : SInf F κ) r = 0 := by
    intro r; funext x; simp [tens]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro T hT0 hSD r hr x
    by_cases hf : f = 0
    · subst hf
      have hf₁ : f₁ = 0 := hext _ _ fun a => by
        have h := hSD g₀ hg₀ _ (eval_mem_adm (ptAt a 0))
        simp only [LinearMap.proj_apply, hzero, hT0] at h
        rw [hzero]
        exact (h.unique (hasDerivAt_const 0 (0 : ℂ)))
      subst hf₁
      rw [hzeroT]
      simp only [hT0, Pi.zero_apply]
      exact hasDerivAt_const 0 (0 : ℂ)
    · have hg : (fun y => r (fun i => ((0 : Ainf F), y i))) ∈ SB (κ → Af F) :=
        mem_SB_of_pureA_mem hf (tens_eq_pureA (⇑f) hr.1 ▸ hr.2)
      have h := hSD _ hg _ (eval_mem_adm x)
      rw [tens_eq_pureA (⇑f) hr.1, tens_eq_pureA (⇑f₁) hr.1]
      exact h
  · intro T hT0 hSA r hr
    by_cases hf : f = 0
    · subst hf
      have hf₁ : f₁ = 0 := hext _ _ fun a => by
        have h := hSA g₀ hg₀
        rw [hzero, hT0] at h
        rw [← h, hzero]
      subst hf₁
      rw [hzeroT, hT0]
    · have hg : (fun y => r (fun i => ((0 : Ainf F), y i))) ∈ SB (κ → Af F) :=
        mem_SB_of_pureA_mem hf (tens_eq_pureA (⇑f) hr.1 ▸ hr.2)
      rw [tens_eq_pureA (⇑f) hr.1, tens_eq_pureA (⇑f₁) hr.1]
      exact hSA _ hg
  · intro T h₁ h₂
    refine hext _ _ fun a => ?_
    have e₁ := h₁ r₀ hrest₀ (ptAt a 0)
    have e₂ := h₂ r₀ hrest₀ (ptAt a 0)
    rw [htens₀] at e₁ e₂
    exact e₁.unique e₂
  · intro T h₁ h₂
    refine hext _ _ fun a => ?_
    have e := (h₁ r₀ hrest₀).symm.trans (h₂ r₀ hrest₀)
    rw [htens₀, htens₀] at e
    exact congrFun e (ptAt a 0)
  · intro T h₁ h₂
    refine hext _ _ fun a => ?_
    have e₁ := h₁ g₀ hg₀ _ (eval_mem_adm (ptAt a 0))
    have e₂ := h₂ g₀ hg₀ _ (eval_mem_adm (ptAt a 0))
    exact e₁.unique e₂

end Main

end GlobalTheory.RealLift
