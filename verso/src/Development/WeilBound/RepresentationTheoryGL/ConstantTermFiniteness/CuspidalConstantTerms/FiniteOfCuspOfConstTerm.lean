import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstTermEqZeroOfFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IteratedDerivOneP
import Development.WeilBound.RepresentationTheoryGL.ConstantTermFiniteness.CuspidalConstantTerms.FormsSubsetFormsOnEmpty

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCF.Rg

open GlobalTheory.Published GlobalTheory.Published.AutFin

section Sub

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}
  {U : Subgroup (GA D V)} {ε : D.what₂.Tau → Fin V.rank → Bool}
  {fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {W : D.what₂.Tau → Type}
  [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] {ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ)}
  {c : D.what₂.Tau → ℕ → ℂ}

/- English proof (translation)
Take `⟨f1, f2, f3, f4⟩` from `hf`. Take `⟨g1, g2, g3, g4⟩` from `hg`. Use `⟨GlobalTheory.MultMem.isAutFunSm_add f1 g1, fun u hu hu' x => ?_, fun τ x => ?_, fun τ k => ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.add_apply, f2 u hu hu' x, g2 u hu hu' x]`. Conclude with `(GlobalTheory.Published.AutFin.coeffSpan (ρ τ)).add_mem (f3 τ x) (g3 τ x)`.

Rewrite using `[(GlobalTheory.Mem.AutSpace.linOnSm_gelf (θ := θ) (V := V) τ k).add f f1.smooth g g1.smooth, f4, g4, smul_add]`.
-/
theorem forms_add {f g : GA D V → ℂ} (hf : f ∈ forms θ V U ε fr ρ c) (hg : g ∈ forms θ V U ε fr ρ c) :
    f + g ∈ forms θ V U ε fr ρ c := by
  obtain ⟨f1, f2, f3, f4⟩ := hf
  obtain ⟨g1, g2, g3, g4⟩ := hg
  refine ⟨GlobalTheory.MultMem.isAutFunSm_add f1 g1, fun u hu hu' x => ?_, fun τ x => ?_, fun τ k => ?_⟩
  · simp only [Pi.add_apply, f2 u hu hu' x, g2 u hu hu' x]
  · exact (GlobalTheory.Published.AutFin.coeffSpan (ρ τ)).add_mem (f3 τ x) (g3 τ x)
  · rw [(GlobalTheory.Mem.AutSpace.linOnSm_gelf (θ := θ) (V := V) τ k).add f f1.smooth g g1.smooth, f4, g4, smul_add]

/- English proof (translation)
Take `⟨f1, f2, f3, f4⟩` from `hf`. Use `⟨GlobalTheory.MultMem.isAutFunSm_smul a f1, fun u hu hu' x => ?_, fun τ x => ?_, fun τ k => ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, f2 u hu hu' x]`. Conclude with `(GlobalTheory.Published.AutFin.coeffSpan (ρ τ)).smul_mem a (f3 τ x)`. Rewrite using `[(GlobalTheory.Mem.AutSpace.linOnSm_gelf (θ := θ) (V := V) τ k).smul, f4, smul_comm]`.
-/
theorem forms_smul (a : ℂ) {f : GA D V → ℂ} (hf : f ∈ forms θ V U ε fr ρ c) :
    a • f ∈ forms θ V U ε fr ρ c := by
  obtain ⟨f1, f2, f3, f4⟩ := hf
  refine ⟨GlobalTheory.MultMem.isAutFunSm_smul a f1, fun u hu hu' x => ?_, fun τ x => ?_, fun τ k => ?_⟩
  · simp only [Pi.smul_apply, f2 u hu hu' x]
  · exact (GlobalTheory.Published.AutFin.coeffSpan (ρ τ)).smul_mem a (f3 τ x)
  · rw [(GlobalTheory.Mem.AutSpace.linOnSm_gelf (θ := θ) (V := V) τ k).smul, f4, smul_comm]

/- English proof (translation)
Use `⟨GlobalTheory.Mem.AutSpace.isAutFunSm_zero θ V, fun _ _ _ _ => rfl, fun τ x => (GlobalTheory.Published.AutFin.coeffSpan (ρ τ)).zero_mem, fun τ k => ?_⟩` and prove the remaining obligations. Use `(GlobalTheory.Mem.AutSpace.linOnSm_gelf (θ := θ) (V := V) τ k).smul 0 0` as an intermediate fact. Simplify using `using this`.
-/
theorem forms_zero : (0 : GA D V → ℂ) ∈ forms θ V U ε fr ρ c := by
  refine ⟨GlobalTheory.Mem.AutSpace.isAutFunSm_zero θ V, fun _ _ _ _ => rfl, fun τ x => (GlobalTheory.Published.AutFin.coeffSpan (ρ τ)).zero_mem, fun τ k => ?_⟩
  have := (GlobalTheory.Mem.AutSpace.linOnSm_gelf (θ := θ) (V := V) τ k).smul 0 0
  simpa using this

/- English proof (translation)
Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem x h => exact h`. Consider the case `zero => exact forms_zero`. Consider the case `add x y _ _ hx hy => exact forms_add hx hy`. Consider the case `smul a x _ hx => exact forms_smul a hx`.
-/
theorem mem_forms_of_mem_span {f : GA D V → ℂ} (hf : f ∈ Submodule.span ℂ (forms θ V U ε fr ρ c)) :
    f ∈ forms θ V U ε fr ρ c := by
  induction hf using Submodule.span_induction with
  | mem x h => exact h
  | zero => exact forms_zero
  | add x y _ _ hx hy => exact forms_add hx hy
  | smul a x _ hx => exact forms_smul a hx

end Sub

/- English proof (translation)
Use `set S := Submodule.span ℂ (forms θ V U ε fr ρ c) with hS`. Establish `hmem : ∀ f : S, f.1 ∈ forms θ V U ε fr ρ c` using `fun f => mem_forms_of_mem_span f.2`. Set `hex : ℕ → Prop` to `fun r => ∃ C : Matrix (Fin V.rank) (Fin r) D.host.E, IsIsoFrame V C`. Set `Tm : ∀ r, hex r → (S →ₗ[ℂ] (GA D V → ℂ))` to `fun r h => { toFun := fun f => GlobalTheory.Cusp.constTerm (GlobalTheory.Cusp.frameFlag h.choose_spec) f.1 map_add' := fun a b => funext fun x => (GlobalTheory.Cusp.cocompact_single _).constTermOn_add (hmem a).1.left (hmem a).1.cont (hmem b).1.left (hmem b).1.cont x map_smul' := …`. Set `R : Fin (V.rank + 1) → Submodule ℂ (GA D V → ℂ)` to `fun i => if h : hex i.val then Submodule.span ℂ (GlobalTheory.Cusp.constTerm (GlobalTheory.Cusp.frameFlag h.choose_spec) '' forms θ V U ε fr ρ c) else ⊥`.

Establish `hRfin : ∀ i, FiniteDimensional ℂ (R i)` using `fun i => by`. Distinguish the cases in `h : hex i.val`. Establish `e : R i = Submodule.span ℂ (GlobalTheory.Cusp.constTerm (GlobalTheory.Cusp.frameFlag h.choose_spec) '' forms θ V U ε fr ρ c)` using `dif_pos h`. Rewrite using `[e]`. Conclude with `hct _ _ h.choose_spec`.

Establish `e : R i = ⊥` using `dif_neg h`. Rewrite using `[e]`. Use `infer_instance`. Set `T : ∀ i : Fin (V.rank + 1), S →ₗ[ℂ] R i` to `fun i => if h : hex i.val then (Tm i.val h).codRestrict (R i) (fun f => by`. Simplify using `only [R, dif_pos h]`.

Conclude with `Submodule.subset_span ⟨f.1, hmem f, rfl⟩)`. Use `else 0`. Set `Ψ : S →ₗ[ℂ] (∀ i, R i)` to `LinearMap.pi T`. Establish `hker : ∀ f : S, Ψ f = 0 → IsCuspFun V f.1`. Introduce `f hf`.

Establish `hl : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) f.1` using `(hmem f).1.left`. Use `(GlobalTheory.Cusp.isCuspFun_iff hl).2 fun Y hY => ?_` and prove the remaining obligations. Take `⟨r, C, hC, rfl⟩` from `(GlobalTheory.AutFunCompare.isIsotropic_iff V Y).1 hY`. Establish `hr : r ≤ V.rank`. Use `hC.2.1.fintype_card_le_finrank` as an intermediate fact.

Simplify using `using this`. Establish `hx : hex r` using `⟨C, hC⟩`. Establish `h0 : GlobalTheory.Cusp.constTerm (GlobalTheory.Cusp.frameFlag hx.choose_spec) f.1 = 0`. Use `congrFun hf ⟨r, Nat.lt_succ_of_le hr⟩` as an intermediate fact. Establish `h2` using `congrArg Subtype.val this`.

Simplify `h2` using `[Ψ, T, hx, Tm]`. Conclude with `GlobalTheory.CompanionTheory.ConstTermConj.constTerm_eq_zero_of_frame D V r _ C hx.choose_spec hC f.1 hl h0`. Use `haveI := hcusp`. Use `haveI : FiniteDimensional ℂ (LinearMap.ker Ψ) := by`. Set `ι : LinearMap.ker Ψ →ₗ[ℂ] Submodule.span ℂ {φ | φ ∈ forms θ V U ε fr ρ c ∧ IsCuspFun V φ}` to `{ toFun := fun f => ⟨f.1.1, Submodule.subset_span ⟨hmem f.1, hker f.1 f.2⟩⟩ map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`.

Conclude with `FiniteDimensional.of_injective ι fun a b h => Subtype.ext (Subtype.ext (congrArg (fun z => z.1) h))`. Use `haveI : FiniteDimensional ℂ (LinearMap.range Ψ) := inferInstance`. Use `haveI : FiniteDimensional ℂ (S ⧸ LinearMap.ker Ψ) := Module.Finite.equiv Ψ.quotKerEquivRange.symm`. Conclude with `Module.Finite.of_submodule_quotient (LinearMap.ker Ψ)`.
-/
theorem finite_of_cusp_of_constTerm {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (V : HSp D) (U : Subgroup (GA D V)) (ε : D.what₂.Tau → Fin V.rank → Bool)
    (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (W : D.what₂.Tau → Type)
    [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ))
    (c : D.what₂.Tau → ℕ → ℂ)
    (hcusp : FiniteDimensional ℂ (Submodule.span ℂ {φ | φ ∈ forms θ V U ε fr ρ c ∧ IsCuspFun V φ}))
    (hct : ∀ (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (hC : IsIsoFrame V C),
      FiniteDimensional ℂ (Submodule.span ℂ
        (GlobalTheory.Cusp.constTerm (GlobalTheory.Cusp.frameFlag hC) '' forms θ V U ε fr ρ c))) :
    FiniteDimensional ℂ (Submodule.span ℂ (forms θ V U ε fr ρ c)) := by
  classical
  set S := Submodule.span ℂ (forms θ V U ε fr ρ c) with hS
  have hmem : ∀ f : S, f.1 ∈ forms θ V U ε fr ρ c := fun f => mem_forms_of_mem_span f.2

  let hex : ℕ → Prop := fun r => ∃ C : Matrix (Fin V.rank) (Fin r) D.host.E, IsIsoFrame V C
  let Tm : ∀ r, hex r → (S →ₗ[ℂ] (GA D V → ℂ)) := fun r h =>
    { toFun := fun f => GlobalTheory.Cusp.constTerm (GlobalTheory.Cusp.frameFlag h.choose_spec) f.1
      map_add' := fun a b => funext fun x =>
        (GlobalTheory.Cusp.cocompact_single _).constTermOn_add (hmem a).1.left (hmem a).1.cont (hmem b).1.left (hmem b).1.cont x
      map_smul' := fun a f => funext fun x => GlobalTheory.Cusp.constTermOn_smul a f.1 x }
  let R : Fin (V.rank + 1) → Submodule ℂ (GA D V → ℂ) := fun i =>
    if h : hex i.val then Submodule.span ℂ (GlobalTheory.Cusp.constTerm (GlobalTheory.Cusp.frameFlag h.choose_spec) '' forms θ V U ε fr ρ c) else ⊥
  have hRfin : ∀ i, FiniteDimensional ℂ (R i) := fun i => by
    by_cases h : hex i.val
    · have e : R i = Submodule.span ℂ (GlobalTheory.Cusp.constTerm (GlobalTheory.Cusp.frameFlag h.choose_spec) '' forms θ V U ε fr ρ c) :=
        dif_pos h
      rw [e]; exact hct _ _ h.choose_spec
    · have e : R i = ⊥ := dif_neg h
      rw [e]; infer_instance
  let T : ∀ i : Fin (V.rank + 1), S →ₗ[ℂ] R i := fun i =>
    if h : hex i.val then
      (Tm i.val h).codRestrict (R i) (fun f => by
        simp only [R, dif_pos h]
        exact Submodule.subset_span ⟨f.1, hmem f, rfl⟩)
    else 0
  let Ψ : S →ₗ[ℂ] (∀ i, R i) := LinearMap.pi T
  have hker : ∀ f : S, Ψ f = 0 → IsCuspFun V f.1 := by
    intro f hf
    have hl : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) f.1 := (hmem f).1.left
    refine (GlobalTheory.Cusp.isCuspFun_iff hl).2 fun Y hY => ?_
    obtain ⟨r, C, hC, rfl⟩ := (GlobalTheory.AutFunCompare.isIsotropic_iff V Y).1 hY
    have hr : r ≤ V.rank := by
      have := hC.2.1.fintype_card_le_finrank
      simpa using this
    have hx : hex r := ⟨C, hC⟩
    have h0 : GlobalTheory.Cusp.constTerm (GlobalTheory.Cusp.frameFlag hx.choose_spec) f.1 = 0 := by
      have := congrFun hf ⟨r, Nat.lt_succ_of_le hr⟩
      have h2 := congrArg Subtype.val this
      simpa [Ψ, T, hx, Tm] using h2
    exact GlobalTheory.CompanionTheory.ConstTermConj.constTerm_eq_zero_of_frame D V r _ C hx.choose_spec hC f.1 hl h0
  haveI := hcusp
  haveI : FiniteDimensional ℂ (LinearMap.ker Ψ) := by
    let ι : LinearMap.ker Ψ →ₗ[ℂ] Submodule.span ℂ {φ | φ ∈ forms θ V U ε fr ρ c ∧ IsCuspFun V φ} :=
      { toFun := fun f => ⟨f.1.1, Submodule.subset_span ⟨hmem f.1, hker f.1 f.2⟩⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact FiniteDimensional.of_injective ι fun a b h =>
      Subtype.ext (Subtype.ext (congrArg (fun z => z.1) h))
  haveI : FiniteDimensional ℂ (LinearMap.range Ψ) := inferInstance
  haveI : FiniteDimensional ℂ (S ⧸ LinearMap.ker Ψ) := Module.Finite.equiv Ψ.quotKerEquivRange.symm
  exact Module.Finite.of_submodule_quotient (LinearMap.ker Ψ)

end GlobalTheory.CompanionTheory.Hypotheses₂.HCF.Rg

namespace GlobalTheory.CompanionTheory.Hypotheses₂

open GlobalTheory.Published.AutFin in

/- English proof (translation)
Introduce `D θ hθ V U hU ε fr hfr W _ _ _ ρ hρ c`. Conclude with `HCF.Rg.finite_of_cusp_of_constTerm θ V U ε fr W ρ c (GlobalTheory.CompanionTheory.HCCusp.cuspFinite D θ hθ V U hU ε fr hfr W ρ hρ c) (ConstFin.Rg.finite_constTerm D θ hθ V U hU ε fr hfr W ρ hρ c)`.
-/
theorem _root_.PositivityTheory.RgHf.harishChandraFinite : GlobalTheory.Published.HarishChandraFinite := by
  intro D θ hθ V U hU ε fr hfr W _ _ _ ρ hρ c
  exact HCF.Rg.finite_of_cusp_of_constTerm θ V U ε fr W ρ c (GlobalTheory.CompanionTheory.HCCusp.cuspFinite D θ hθ V U hU ε fr hfr W ρ hρ c)
    (ConstFin.Rg.finite_constTerm D θ hθ V U hU ε fr hfr W ρ hρ c)

end GlobalTheory.CompanionTheory.Hypotheses₂

end
