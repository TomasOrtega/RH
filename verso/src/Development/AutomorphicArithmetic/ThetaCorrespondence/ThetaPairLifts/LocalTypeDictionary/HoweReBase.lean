import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.ReBase
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaKernelLocalOperatorAction

section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
noncomputable section
namespace UpperTheory.Lit.HoweDuality
open GlobalTheory GlobalTheory.ReBase GlobalTheory.FinUniq
/- English proof (translation)
Introduce `hK F E _ _ _ _ _ σ B a a' G X om om' R Rf hM V V' W Rf₃ h₃ v`. Establish `hT` using `hM.triple`. Establish `hf` using `hM.fin`. Establish `hP` using `GlobalTheory.ThK.Inhab.pairV hT`. Establish `hP'` using `GlobalTheory.ThK.Inhab.pairV' hT`.

Establish `hAE` using `_root_.GlobalTheory.ThK.LocalOps.theta_kernel_local_operators_act hK`. Establish `h1V : (1 : UA σ G.V.J) ∈ UAt σ G.V (evFin F v)` using `fun u _ => by show u • ((1 : UA σ G.V.J).1.1 - 1) = 0`. Rewrite using `[show (1 : UA σ G.V.J).1.1 = 1 from rfl, sub_self, smul_zero]`. Establish `h1V' : (1 : UA σ G.V'.J) ∈ UAt σ G.V' (evFin F v)` using `fun u _ => by show u • ((1 : UA σ G.V'.J).1.1 - 1) = 0`. Rewrite using `[show (1 : UA σ G.V'.J).1.1 = 1 from rfl, sub_self, smul_zero]`.

Establish `exV : ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁` using `fun h hh φ hφ => by`. Take `⟨φ₁, ⟨h1, h2⟩, -⟩` from `(hAE F E σ B _ _ _ _ _ _ _ om _ _ _ _ hP v).1 1 h1V h hh φ hφ`. Conclude with `⟨φ₁, h1, h2⟩`. Establish `exV' : ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∃ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (1, h)) φ φ₁` using `fun h hh φ hφ => by`. Take `⟨φ₁, ⟨h1, h2⟩, -⟩` from `(hAE F E σ B _ _ _ _ _ _ _ om' _ _ _ _ hP' v).1 1 h1V' h hh φ hφ`.

Conclude with `⟨φ₁, h1, h2⟩`. Establish `props : ∀ Q : FinMaps F a a', (SB (Fin a' × Fin (a + a') → Fv F v)).map (Q.p' v) = ⊤ → (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ' ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁' ∈ SB (Fin a' × Fin (a + a') …`. Introduce `Q onto' eqv irr`. Use `⟨fun h hh φ hφ φ₁ hφ₁ hact e => ?_, fun h hh φ hφ φ₁ hφ₁ hact e => ?_, fun N hN => irr N ?_⟩` and prove the remaining obligations. Rewrite using `[eqv h hh φ hφ 0 (zero_mem _) φ₁ hφ₁ 0 (zero_mem _) hact (acts_zero_zero v _) (by rw [e, map_zero]), map_zero]`.

Rewrite using `[← eqv h hh 0 (zero_mem _) φ hφ 0 (zero_mem _) φ₁ hφ₁ (acts_zero_zero v _) hact (by rw [e, map_zero]), map_zero]`. Introduce `h hh φ hφ φ₁ hφ₁ hact hmem`. Choose the witnesses or unpack the hypotheses as in `⟨φ', hφ', e⟩ : ∃ φ' ∈ SB (Fin a' × Fin (a + a') → Fv F v), Q.p' v φ' = Q.p v φ := by`. Establish `: Q.p v φ ∈ (SB (Fin a' × Fin (a + a') → Fv F v)).map (Q.p' v)` using `by rw [onto']; trivial`. Conclude with `this`.

Take `⟨φ₁', hφ₁', hact'⟩` from `exV' h hh φ' hφ'`. Rewrite using `[eqv h hh φ hφ φ' hφ' φ₁ hφ₁ φ₁' hφ₁' hact hact' e.symm]`. Conclude with `hN h hh φ' hφ' φ₁' hφ₁' hact' (e ▸ hmem)`. Take `⟨sV, sV', iV'⟩` from `props Rf (hf.onto' v) (hf.equiv v) (hf.irred v)`. Take `⟨tV, tV', jV'⟩` from `props Rf₃ (h₃.onto' v) (h₃.equiv v) (h₃.irred v)`.

Use `haveI := hf.nontriv v`. Use `haveI := h₃.nontriv v`. Establish `mV` using `ker_maximal om v (Rf.p v) (hf.onto v) (hf.inv v) sV (hf.irred v)`. Establish `mV₃` using `ker_maximal (Y := G.V) (Z := G.W) om v (Rf₃.p v) (h₃.onto v) (h₃.inv v) tV (h₃.irred v)`. Establish `mV'` using `ker_maximal om' v (Rf.p' v) (hf.onto' v) (hf.inv' v) sV' iV'`.

Establish `mV₃'` using `ker_maximal (Y := G.V') (Z := G.W) om' v (Rf₃.p' v) (h₃.onto' v) (h₃.inv' v) tV' jV'`. Establish `howe` using `PositivityTheory.Sph.maxFinT_of sphTri F E σ B a a' G X om om' hT v trivial`. Establish `eV` using `howe.1 _ _ mV mV₃`. Establish `eV'` using `howe.2 _ _ mV' mV₃'`. Take `⟨ψ, hψ⟩` from `equiv_of_ker_eq' (Rf.p v) (Rf₃.p v) (hf.onto v) (h₃.onto v) eV`.

Take `⟨ψ', hψ'⟩` from `equiv_of_ker_eq' (Rf.p' v) (Rf₃.p' v) (hf.onto' v) (h₃.onto' v) eV'`. Use `set T : Module.End ℂ (Rf.Pi v) := ψ.symm.toLinearMap ∘ₗ ψ'.toLinearMap with hTdef`. Establish `hTapp : ∀ x, T x = ψ.symm (ψ' x)` using `fun x => rfl`. Establish `comm : ∀ h ∈ UAt σ G.W (evFin F v), ∀ χ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ χ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, h)) χ χ₁ → ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁ → Rf …`. Introduce `h hh χ hχ χ₁ hχ₁ hc φ hφ φ₁ hφ₁ ha e`.

Choose the witnesses or unpack the hypotheses as in `⟨χ', hχ', e1⟩ : ∃ χ' ∈ SB (Fin a' × Fin (a + a') → Fv F v), Rf.p' v χ' = Rf.p v χ := by`. Establish `: Rf.p v χ ∈ (SB (Fin a' × Fin (a + a') → Fv F v)).map (Rf.p' v)` using `by rw [hf.onto' v]; trivial`. Conclude with `this`. Take `⟨χ₁', hχ₁', hc'⟩` from `exV' h hh χ' hχ'`. Establish `e2 : Rf.p v χ₁ = Rf.p' v χ₁'` using `hf.equiv v h hh χ hχ χ' hχ' χ₁ hχ₁ χ₁' hχ₁' hc hc' e1.symm`.

Establish `e3 : Rf₃.p v φ = Rf₃.p' v χ'`. Rewrite using `[hψ φ hφ, e, hTapp, ← e1, LinearEquiv.apply_symm_apply, ← hψ' χ' hχ']`. Establish `e4 : Rf₃.p v φ₁ = Rf₃.p' v χ₁'` using `h₃.equiv v h hh φ hφ χ' hχ' φ₁ hφ₁ χ₁' hχ₁' ha hc' e3`. Rewrite using `[hTapp, e2, ← hψ' χ₁' hχ₁', ← e4, hψ φ₁ hφ₁, LinearEquiv.symm_apply_apply]`. Establish `hrank : Module.rank ℂ (Rf.Pi v) ≤ Cardinal.aleph0` using `by haveI := sc_Fv v`.

Establish `sp : Function.Surjective ((Rf.p v).comp (SB (Fin a × Fin (a + a') → Fv F v)).subtype)` using `fun y => by`. Establish `: y ∈ (SB (Fin a × Fin (a + a') → Fv F v)).map (Rf.p v)` using `by rw [hf.onto v]; trivial`. Take `⟨x, hx, rfl⟩` from `this`. Conclude with `⟨⟨x, hx⟩, rfl⟩`. Conclude with `(LinearMap.rank_le_of_surjective _ sp).trans (rank_SB_le _)`.

Establish `hker : ∀ c : ℂ, ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁ → Rf.p v φ ∈ LinearMap.ker (T - c • 1) → Rf.p v φ₁ ∈ LinearMap.ker (T - c • 1)`. Introduce `c h hh φ hφ φ₁ hφ₁ hact hmem`. Rewrite `hmem`, the goal using `[LinearMap.mem_ker]`. Simplify using `only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at hmem ⊢`. Establish `hsc` using `GlobalTheory.ThK.LocalOps.acts_lin v (om (1, h)) (exV h hh) hφ hφ hact hact c 0`.

Rewrite `hsc` using `[zero_smul, zero_smul, add_zero, add_zero]`. Establish `e : Rf.p v (c • φ) = T (Rf.p v φ)` using `by rw [map_smul, hmem]`. Use `comm h hh φ hφ φ₁ hφ₁ hact (c • φ) ((SB (Fin a × Fin (a + a') → Fv F v)).smul_mem c hφ) (c • φ₁) ((SB (Fin a × Fin (a + a') → Fv F v)).smul_mem c hφ₁) hsc e` as an intermediate fact. Rewrite using `[← this, map_smul]`. Establish `hran : ∀ c : ℂ, ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁ → Rf.p v φ ∈ LinearMap.range (T - c • 1) → Rf.p v φ₁ ∈ LinearMap.range (T - c • 1)`.

Introduce `c h hh φ hφ φ₁ hφ₁ hact hmem`. Take `⟨y, hy⟩` from `hmem`. Choose the witnesses or unpack the hypotheses as in `⟨χ, hχ, rfl⟩ : ∃ χ ∈ SB (Fin a × Fin (a + a') → Fv F v), Rf.p v χ = y := by`. Establish `: y ∈ (SB (Fin a × Fin (a + a') → Fv F v)).map (Rf.p v)` using `by rw [hf.onto v]; trivial`. Conclude with `this`.

Take `⟨χ₁, hχ₁, hc⟩` from `exV h hh χ hχ`. Establish `hsum` using `GlobalTheory.ThK.LocalOps.acts_lin v (om (1, h)) (exV h hh) hφ hχ hact hc 1 c`. Rewrite `hsum` using `[one_smul, one_smul]`. Simplify using `only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at hy`. Establish `e : Rf.p v (φ + c • χ) = T (Rf.p v χ)`.

Rewrite using `[map_add, map_smul, ← hy]`. Normalize the expressions using the abelian group laws. Use `comm h hh χ hχ χ₁ hχ₁ hc (φ + c • χ) (add_mem hφ ((SB (Fin a × Fin (a + a') → Fv F v)).smul_mem c hχ)) (φ₁ + c • χ₁) (add_mem hφ₁ ((SB (Fin a × Fin (a + a') → Fv F v)).smul_mem c hχ₁)) hsum e` as an intermediate fact. Use `⟨Rf.p v χ₁, ?_⟩` and prove the remaining obligations. Simplify using `only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]`.

Rewrite using `[← this, map_add, map_smul]`. Normalize the expressions using the abelian group laws. Take `⟨l, hl⟩` from `scalar_of_irred (fun N => ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁ → Rf.p v φ ∈ N → Rf.p v φ₁ ∈ N) hrank (hf.irred v) T hker hran`. Establish `hTl : ∀ x, ψ' x = l • ψ x` using `fun x => by`. Use `congrArg (fun f : Module.End ℂ (Rf.Pi v) => f x) hl` as an intermediate fact.

Simplify using `only [hTapp, LinearMap.smul_apply, Module.End.one_apply] at this`. Rewrite using `[← map_smul, ← this, LinearEquiv.apply_symm_apply]`. Establish `hl0 : l ≠ 0`. Introduce and unpack `rfl`. Take `⟨x, hx⟩` from `exists_ne (0 : Rf.Pi v)`.

Use `hTl x` as an intermediate fact. Rewrite `this` using `[zero_smul, LinearEquiv.map_eq_zero_iff]`. Conclude with `hx this`. Use `⟨ψ, l, hl0, hψ, fun φ hφ => by rw [hψ' φ hφ, hTl], fun hv => ?_⟩` and prove the remaining obligations. Take `⟨s1, s2⟩` from `hf.sph v hv`.

Take `⟨s3, -⟩` from `h₃.sph v hv`. Establish `hvac` using `(hT.geo.hM.vac v).1`. Establish `hvac'` using `(hT.geo.hM'.vac v).1`. Express the relevant statement in the definitionally equal form `Rf₃.p v (G.M.vac v) = Rf₃.p' v (G.M'.vac v) at s3`. Establish `e1 : Rf₃.p' v (G.M'.vac v) = l • Rf₃.p v (G.M.vac v)`.

Rewrite using `[hψ' _ hvac', hTl, ← s1, ← hψ _ hvac]`. Establish `hne : Rf₃.p v (G.M.vac v) ≠ 0`. Rewrite using `[hψ _ hvac]`. Conclude with `(LinearEquiv.map_ne_zero_iff ψ).2 s2`. Rewrite `e1` using `[← s3]`.

Establish `: (l - 1) • Rf₃.p v (G.M.vac v) = 0` using `by rw [sub_smul, one_smul, ← e1, sub_self]`. Break down `smul_eq_zero.1 this with h | h` into its components or cases. Conclude with `sub_eq_zero.1 h`. Conclude with `absurd h hne`.
-/
theorem exists_local_iso_scalar_of_reG : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf →
    ∀ (V : Spc F E a) (V' : Spc F E a') (W : Spc F E (a + a')) (Rf₃ : FinMaps F a a'), IsFinMaps B (reG G V V' W) X om om' Rf₃ →
    ∀ v : Pl F, ∃ (ψ : Rf.Pi v ≃ₗ[ℂ] Rf₃.Pi v) (l : ℂ), l ≠ 0 ∧ (∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), Rf₃.p v φ = ψ (Rf.p v φ)) ∧
      (∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Rf₃.p' v φ = l • ψ (Rf.p' v φ)) ∧ (v ∉ X.T → l = 1) := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' R Rf hM V V' W Rf₃ h₃ v
  have hT := hM.triple
  have hf := hM.fin
  have hP := GlobalTheory.ThK.Inhab.pairV hT
  have hP' := GlobalTheory.ThK.Inhab.pairV' hT
  have hAE := _root_.GlobalTheory.ThK.LocalOps.theta_kernel_local_operators_act hK
  have h1V : (1 : UA σ G.V.J) ∈ UAt σ G.V (evFin F v) := fun u _ => by
    show u • ((1 : UA σ G.V.J).1.1 - 1) = 0
    rw [show (1 : UA σ G.V.J).1.1 = 1 from rfl, sub_self, smul_zero]
  have h1V' : (1 : UA σ G.V'.J) ∈ UAt σ G.V' (evFin F v) := fun u _ => by
    show u • ((1 : UA σ G.V'.J).1.1 - 1) = 0
    rw [show (1 : UA σ G.V'.J).1.1 = 1 from rfl, sub_self, smul_zero]
  have exV : ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁ := fun h hh φ hφ => by
    obtain ⟨φ₁, ⟨h1, h2⟩, -⟩ := (hAE F E σ B _ _ _ _ _ _ _ om _ _ _ _ hP v).1 1 h1V h hh φ hφ
    exact ⟨φ₁, h1, h2⟩
  have exV' : ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      ∃ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (1, h)) φ φ₁ := fun h hh φ hφ => by
    obtain ⟨φ₁, ⟨h1, h2⟩, -⟩ := (hAE F E σ B _ _ _ _ _ _ _ om' _ _ _ _ hP' v).1 1 h1V' h hh φ hφ
    exact ⟨φ₁, h1, h2⟩
  have props : ∀ Q : FinMaps F a a',
      (SB (Fin a' × Fin (a + a') → Fv F v)).map (Q.p' v) = ⊤ →
      (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ' ∈ SB (Fin a' × Fin (a + a') → Fv F v),
        ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁' ∈ SB (Fin a' × Fin (a + a') → Fv F v),
        Acts (evFin F v) (om (1, h)) φ φ₁ → Acts (evFin F v) (om' (1, h)) φ' φ₁' → Q.p v φ = Q.p' v φ' →
          Q.p v φ₁ = Q.p' v φ₁') →
      (∀ N : Submodule ℂ (Q.Pi v), (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
        Acts (evFin F v) (om (1, h)) φ φ₁ → Q.p v φ ∈ N → Q.p v φ₁ ∈ N) → N = ⊥ ∨ N = ⊤) →
      (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
        Acts (evFin F v) (om (1, h)) φ φ₁ → Q.p v φ = 0 → Q.p v φ₁ = 0) ∧
      (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
        Acts (evFin F v) (om' (1, h)) φ φ₁ → Q.p' v φ = 0 → Q.p' v φ₁ = 0) ∧
      (∀ N : Submodule ℂ (Q.Pi v), (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
        Acts (evFin F v) (om' (1, h)) φ φ₁ → Q.p' v φ ∈ N → Q.p' v φ₁ ∈ N) → N = ⊥ ∨ N = ⊤) := by
    intro Q onto' eqv irr
    refine ⟨fun h hh φ hφ φ₁ hφ₁ hact e => ?_, fun h hh φ hφ φ₁ hφ₁ hact e => ?_, fun N hN => irr N ?_⟩
    · rw [eqv h hh φ hφ 0 (zero_mem _) φ₁ hφ₁ 0 (zero_mem _) hact (acts_zero_zero v _) (by rw [e, map_zero]), map_zero]
    · rw [← eqv h hh 0 (zero_mem _) φ hφ 0 (zero_mem _) φ₁ hφ₁ (acts_zero_zero v _) hact (by rw [e, map_zero]), map_zero]
    · intro h hh φ hφ φ₁ hφ₁ hact hmem
      obtain ⟨φ', hφ', e⟩ : ∃ φ' ∈ SB (Fin a' × Fin (a + a') → Fv F v), Q.p' v φ' = Q.p v φ := by
        have : Q.p v φ ∈ (SB (Fin a' × Fin (a + a') → Fv F v)).map (Q.p' v) := by rw [onto']; trivial
        exact this
      obtain ⟨φ₁', hφ₁', hact'⟩ := exV' h hh φ' hφ'
      rw [eqv h hh φ hφ φ' hφ' φ₁ hφ₁ φ₁' hφ₁' hact hact' e.symm]
      exact hN h hh φ' hφ' φ₁' hφ₁' hact' (e ▸ hmem)
  obtain ⟨sV, sV', iV'⟩ := props Rf (hf.onto' v) (hf.equiv v) (hf.irred v)
  obtain ⟨tV, tV', jV'⟩ := props Rf₃ (h₃.onto' v) (h₃.equiv v) (h₃.irred v)
  haveI := hf.nontriv v
  haveI := h₃.nontriv v
  have mV := ker_maximal om v (Rf.p v) (hf.onto v) (hf.inv v) sV (hf.irred v)
  have mV₃ := ker_maximal (Y := G.V) (Z := G.W) om v (Rf₃.p v) (h₃.onto v) (h₃.inv v) tV (h₃.irred v)
  have mV' := ker_maximal om' v (Rf.p' v) (hf.onto' v) (hf.inv' v) sV' iV'
  have mV₃' := ker_maximal (Y := G.V') (Z := G.W) om' v (Rf₃.p' v) (h₃.onto' v) (h₃.inv' v) tV' jV'
  have howe := PositivityTheory.Sph.maxFinT_of sphTri F E σ B a a' G X om om' hT v trivial
  have eV := howe.1 _ _ mV mV₃
  have eV' := howe.2 _ _ mV' mV₃'
  obtain ⟨ψ, hψ⟩ := equiv_of_ker_eq' (Rf.p v) (Rf₃.p v) (hf.onto v) (h₃.onto v) eV
  obtain ⟨ψ', hψ'⟩ := equiv_of_ker_eq' (Rf.p' v) (Rf₃.p' v) (hf.onto' v) (h₃.onto' v) eV'
  set T : Module.End ℂ (Rf.Pi v) := ψ.symm.toLinearMap ∘ₗ ψ'.toLinearMap with hTdef
  have hTapp : ∀ x, T x = ψ.symm (ψ' x) := fun x => rfl
  have comm : ∀ h ∈ UAt σ G.W (evFin F v), ∀ χ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ χ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (1, h)) χ χ₁ → ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₁ → Rf.p v φ = T (Rf.p v χ) → Rf.p v φ₁ = T (Rf.p v χ₁) := by
    intro h hh χ hχ χ₁ hχ₁ hc φ hφ φ₁ hφ₁ ha e
    obtain ⟨χ', hχ', e1⟩ : ∃ χ' ∈ SB (Fin a' × Fin (a + a') → Fv F v), Rf.p' v χ' = Rf.p v χ := by
      have : Rf.p v χ ∈ (SB (Fin a' × Fin (a + a') → Fv F v)).map (Rf.p' v) := by rw [hf.onto' v]; trivial
      exact this
    obtain ⟨χ₁', hχ₁', hc'⟩ := exV' h hh χ' hχ'
    have e2 : Rf.p v χ₁ = Rf.p' v χ₁' := hf.equiv v h hh χ hχ χ' hχ' χ₁ hχ₁ χ₁' hχ₁' hc hc' e1.symm
    have e3 : Rf₃.p v φ = Rf₃.p' v χ' := by
      rw [hψ φ hφ, e, hTapp, ← e1, LinearEquiv.apply_symm_apply, ← hψ' χ' hχ']
    have e4 : Rf₃.p v φ₁ = Rf₃.p' v χ₁' := h₃.equiv v h hh φ hφ χ' hχ' φ₁ hφ₁ χ₁' hχ₁' ha hc' e3
    rw [hTapp, e2, ← hψ' χ₁' hχ₁', ← e4, hψ φ₁ hφ₁, LinearEquiv.symm_apply_apply]
  have hrank : Module.rank ℂ (Rf.Pi v) ≤ Cardinal.aleph0 := by
    haveI := sc_Fv v
    have sp : Function.Surjective ((Rf.p v).comp (SB (Fin a × Fin (a + a') → Fv F v)).subtype) := fun y => by
      have : y ∈ (SB (Fin a × Fin (a + a') → Fv F v)).map (Rf.p v) := by rw [hf.onto v]; trivial
      obtain ⟨x, hx, rfl⟩ := this
      exact ⟨⟨x, hx⟩, rfl⟩
    exact (LinearMap.rank_le_of_surjective _ sp).trans (rank_SB_le _)
  have hker : ∀ c : ℂ, ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₁ → Rf.p v φ ∈ LinearMap.ker (T - c • 1) →
        Rf.p v φ₁ ∈ LinearMap.ker (T - c • 1) := by
    intro c h hh φ hφ φ₁ hφ₁ hact hmem
    rw [LinearMap.mem_ker] at hmem ⊢
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at hmem ⊢
    have hsc := GlobalTheory.ThK.LocalOps.acts_lin v (om (1, h)) (exV h hh) hφ hφ hact hact c 0
    rw [zero_smul, zero_smul, add_zero, add_zero] at hsc
    have e : Rf.p v (c • φ) = T (Rf.p v φ) := by rw [map_smul, hmem]
    have := comm h hh φ hφ φ₁ hφ₁ hact (c • φ) ((SB (Fin a × Fin (a + a') → Fv F v)).smul_mem c hφ) (c • φ₁)
      ((SB (Fin a × Fin (a + a') → Fv F v)).smul_mem c hφ₁) hsc e
    rw [← this, map_smul]
  have hran : ∀ c : ℂ, ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₁ → Rf.p v φ ∈ LinearMap.range (T - c • 1) →
        Rf.p v φ₁ ∈ LinearMap.range (T - c • 1) := by
    intro c h hh φ hφ φ₁ hφ₁ hact hmem
    obtain ⟨y, hy⟩ := hmem
    obtain ⟨χ, hχ, rfl⟩ : ∃ χ ∈ SB (Fin a × Fin (a + a') → Fv F v), Rf.p v χ = y := by
      have : y ∈ (SB (Fin a × Fin (a + a') → Fv F v)).map (Rf.p v) := by rw [hf.onto v]; trivial
      exact this
    obtain ⟨χ₁, hχ₁, hc⟩ := exV h hh χ hχ
    have hsum := GlobalTheory.ThK.LocalOps.acts_lin v (om (1, h)) (exV h hh) hφ hχ hact hc 1 c
    rw [one_smul, one_smul] at hsum
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at hy
    have e : Rf.p v (φ + c • χ) = T (Rf.p v χ) := by
      rw [map_add, map_smul, ← hy]; abel
    have := comm h hh χ hχ χ₁ hχ₁ hc (φ + c • χ) (add_mem hφ ((SB (Fin a × Fin (a + a') → Fv F v)).smul_mem c hχ)) (φ₁ + c • χ₁)
      (add_mem hφ₁ ((SB (Fin a × Fin (a + a') → Fv F v)).smul_mem c hχ₁)) hsum e
    refine ⟨Rf.p v χ₁, ?_⟩
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    rw [← this, map_add, map_smul]; abel
  obtain ⟨l, hl⟩ := scalar_of_irred (fun N => ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁ → Rf.p v φ ∈ N → Rf.p v φ₁ ∈ N)
    hrank (hf.irred v) T hker hran
  have hTl : ∀ x, ψ' x = l • ψ x := fun x => by
    have := congrArg (fun f : Module.End ℂ (Rf.Pi v) => f x) hl
    simp only [hTapp, LinearMap.smul_apply, Module.End.one_apply] at this
    rw [← map_smul, ← this, LinearEquiv.apply_symm_apply]
  have hl0 : l ≠ 0 := by
    rintro rfl
    obtain ⟨x, hx⟩ := exists_ne (0 : Rf.Pi v)
    have := hTl x
    rw [zero_smul, LinearEquiv.map_eq_zero_iff] at this
    exact hx this
  refine ⟨ψ, l, hl0, hψ, fun φ hφ => by rw [hψ' φ hφ, hTl], fun hv => ?_⟩
  obtain ⟨s1, s2⟩ := hf.sph v hv
  obtain ⟨s3, -⟩ := h₃.sph v hv
  have hvac := (hT.geo.hM.vac v).1
  have hvac' := (hT.geo.hM'.vac v).1
  change Rf₃.p v (G.M.vac v) = Rf₃.p' v (G.M'.vac v) at s3
  have e1 : Rf₃.p' v (G.M'.vac v) = l • Rf₃.p v (G.M.vac v) := by
    rw [hψ' _ hvac', hTl, ← s1, ← hψ _ hvac]
  have hne : Rf₃.p v (G.M.vac v) ≠ 0 := by
    rw [hψ _ hvac]; exact (LinearEquiv.map_ne_zero_iff ψ).2 s2
  rw [← s3] at e1
  have : (l - 1) • Rf₃.p v (G.M.vac v) = 0 := by rw [sub_smul, one_smul, ← e1, sub_self]
  rcases smul_eq_zero.1 this with h | h
  · exact sub_eq_zero.1 h
  · exact absurd h hne
end UpperTheory.Lit.HoweDuality
end
end
