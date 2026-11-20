import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnitFormC
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.ROrdAway
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SatWDCharPolChars

noncomputable section

namespace UpperTheory.V.Z.Sym.Unl.UnlinkedPrincipalSeriesHeckeRoots

section Rep

/- English proof (translation)
Establish `htop : isotypicComponent R M S = ⊤` using `top_le_iff.1 (h ▸ iSup_le fun f => by`. Break down `f.injective_or_eq_zero with hi | rfl` into its components or cases. Conclude with `le_sSup ⟨(LinearEquiv.ofInjective _ hi).symm⟩`. Use the proof step `simp)`. Use `haveI : IsSemisimpleModule R M := IsSemisimpleModule.congr (M := isotypicComponent R M S) (LinearEquiv.ofTop _ htop).symm`.

Establish `hiso` using `IsIsotypicOfType.of_isotypicComponent_eq_top htop`. Choose the witnesses or unpack the hypotheses as in `⟨m, hm, hxm⟩ : ∃ m : Submodule R M, IsCoatom m ∧ x ∉ m := by`. Assume the negation of the conclusion as `hn`. Use `push Not at hn`. Use `hx ((Submodule.mem_bot R).1 ?_)` and prove the remaining obligations.

Rewrite using `[← IsSemisimpleModule.jacobson_eq_bot R M]`. Conclude with `Submodule.mem_sInf.2 hn`. Take `⟨W, hc⟩` from `exists_isCompl m`. Use `haveI : IsSimpleModule R W := isSimpleModule_iff_isAtom.2 (hc.isCoatom_iff_isAtom.1 hm)`. Take `⟨e⟩` from `hiso W`.

Use `⟨e.toLinearMap ∘ₗ W.projectionOnto m hc.symm, fun h0 => hxm ?_⟩` and prove the remaining obligations. Simplify using `using h0`.
-/
private theorem mod_retr {R S M : Type} [Ring R] [AddCommGroup S] [Module R S] [AddCommGroup M] [Module R M]
    [IsSimpleModule R S] (h : ⨆ f : S →ₗ[R] M, LinearMap.range f = ⊤) (x : M) (hx : x ≠ 0) :
    ∃ T : M →ₗ[R] S, T x ≠ 0 := by
  have htop : isotypicComponent R M S = ⊤ := top_le_iff.1 (h ▸ iSup_le fun f => by
    rcases f.injective_or_eq_zero with hi | rfl
    · exact le_sSup ⟨(LinearEquiv.ofInjective _ hi).symm⟩
    · simp)
  haveI : IsSemisimpleModule R M :=
    IsSemisimpleModule.congr (M := isotypicComponent R M S) (LinearEquiv.ofTop _ htop).symm
  have hiso := IsIsotypicOfType.of_isotypicComponent_eq_top htop
  obtain ⟨m, hm, hxm⟩ : ∃ m : Submodule R M, IsCoatom m ∧ x ∉ m := by
    by_contra hn
    push Not at hn
    refine hx ((Submodule.mem_bot R).1 ?_)
    rw [← IsSemisimpleModule.jacobson_eq_bot R M]
    exact Submodule.mem_sInf.2 hn
  obtain ⟨W, hc⟩ := exists_isCompl m
  haveI : IsSimpleModule R W := isSimpleModule_iff_isAtom.2 (hc.isCoatom_iff_isAtom.1 hm)
  obtain ⟨e⟩ := hiso W
  refine ⟨e.toLinearMap ∘ₗ W.projectionOnto m hc.symm, fun h0 => hxm ?_⟩
  simpa using h0

variable {Γ X V : Type} [Group Γ] [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Establish `key` using `mod_retr (R := MonoidAlgebra ℂ Γ) (S := σ.asModule) (M := τ.asModule) (by`. Use `top_le_iff.1 fun y _ => ?_` and prove the remaining obligations. Establish `hy : τ.asModuleEquiv y ∈ (⊤ : Submodule ℂ V)` using `trivial`. Rewrite `hy` using `[← h]`. Rewrite using `[← τ.asModuleEquiv.symm_apply_apply y]`.

Use `Submodule.iSup_induction _ (motive := fun z => τ.asModuleEquiv.symm z ∈ _) hy ?_ ?_ ?_` and prove the remaining obligations. Introduce and unpack `f _ ⟨v, rfl⟩`. Conclude with `Submodule.mem_iSup_of_mem (Representation.IntertwiningMap.equivLinearMapAsModule σ τ ⟨f.1, fun g => LinearMap.ext (f.2 g)⟩) ⟨v, rfl⟩`. Simplify using the standard rewrite rules. Introduce `a b ha hb`.

Rewrite using `[map_add]`. Conclude with `add_mem ha hb)`. Take `⟨T, h2⟩` from `key x hx`. Set `T'` to `(Representation.IntertwiningMap.equivLinearMapAsModule τ σ).symm T`. Conclude with `⟨T'.toLinearMap, fun g v => LinearMap.congr_fun (T'.2 g) v, h2⟩`.
-/
private theorem rep_retr (σ : Representation ℂ Γ X) (hσ : σ.IsIrreducible) (τ : Representation ℂ Γ V)
    (h : ⨆ f : {f : X →ₗ[ℂ] V // ∀ g v, f (σ g v) = τ g (f v)}, LinearMap.range f.1 = ⊤) (x : V) (hx : x ≠ 0) :
    ∃ T : V →ₗ[ℂ] X, (∀ g v, T (τ g v) = σ g (T v)) ∧ T x ≠ 0 := by
  have key := mod_retr (R := MonoidAlgebra ℂ Γ) (S := σ.asModule) (M := τ.asModule) (by
      refine top_le_iff.1 fun y _ => ?_
      have hy : τ.asModuleEquiv y ∈ (⊤ : Submodule ℂ V) := trivial
      rw [← h] at hy
      rw [← τ.asModuleEquiv.symm_apply_apply y]
      refine Submodule.iSup_induction _ (motive := fun z => τ.asModuleEquiv.symm z ∈ _) hy ?_ ?_ ?_
      · rintro f _ ⟨v, rfl⟩
        exact Submodule.mem_iSup_of_mem (Representation.IntertwiningMap.equivLinearMapAsModule σ τ
          ⟨f.1, fun g => LinearMap.ext (f.2 g)⟩) ⟨v, rfl⟩
      · simp
      · intro a b ha hb
        rw [map_add]
        exact add_mem ha hb)
  obtain ⟨T, h2⟩ := key x hx
  let T' := (Representation.IntertwiningMap.equivLinearMapAsModule τ σ).symm T
  exact ⟨T'.toLinearMap, fun g v => LinearMap.congr_fun (T'.2 g) v, h2⟩

/- English proof (translation)
Introduce `h` and use `hx (by have : τ g⁻¹ (τ g x) = x := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] rw [← this, h, LinearMap.zero_apply, map_zero])`.
-/
private theorem ne_zero_rep (τ : Representation ℂ Γ V) {x : V} (hx : x ≠ 0) (g : Γ) : τ g ≠ 0 := fun h => hx (by
  have : τ g⁻¹ (τ g x) = x := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [← this, h, LinearMap.zero_apply, map_zero])

/- English proof (translation)
Establish `hx0 : x ≠ 0` using `fun e => hx (by rw [e, map_zero])`. Break down `finite_or_infinite (MulAction.orbit K (a : Γ ⧸ K)) with hf | hf` into its components or cases. Use `haveI := Fintype.ofFinite (MulAction.orbit K (a : Γ ⧸ K))`. Simplify using `only [Hi.dc, finsum_eq_sum_of_fintype, LinearMap.sum_apply, map_sum, hT]`. Rewrite using `[Hi.dc, Hi.dc, finsum_of_infinite_support, finsum_of_infinite_support]`.

Simplify using the standard rewrite rules. Rewrite using `[Function.support_eq_univ fun _ => ne_zero_rep σ hx _]`. Conclude with `Set.infinite_univ`. Rewrite using `[Function.support_eq_univ fun _ => ne_zero_rep τ hx0 _]`. Conclude with `Set.infinite_univ`.
-/
private theorem map_dc (σ : Representation ℂ Γ X) (τ : Representation ℂ Γ V) (T : V →ₗ[ℂ] X)
    (hT : ∀ g v, T (τ g v) = σ g (T v)) {x : V} (hx : T x ≠ 0) (K : Subgroup Γ) (a : Γ) :
    T (Hi.dc τ K K a x) = Hi.dc σ K K a (T x) := by
  have hx0 : x ≠ 0 := fun e => hx (by rw [e, map_zero])
  rcases finite_or_infinite (MulAction.orbit K (a : Γ ⧸ K)) with hf | hf
  · haveI := Fintype.ofFinite (MulAction.orbit K (a : Γ ⧸ K))
    simp only [Hi.dc, finsum_eq_sum_of_fintype, LinearMap.sum_apply, map_sum, hT]
  · rw [Hi.dc, Hi.dc, finsum_of_infinite_support, finsum_of_infinite_support]
    · simp
    · rw [Function.support_eq_univ fun _ => ne_zero_rep σ hx _]
      exact Set.infinite_univ
    · rw [Function.support_eq_univ fun _ => ne_zero_rep τ hx0 _]
      exact Set.infinite_univ

end Rep

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial ValuativeRel
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.SmGL UpperTheory.V.Af UpperTheory.V.Sd

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Use `set δ : (Fin 2 → kˣ) →* ℂˣ := (deltaHalf k fun _ : Fin 2 => Unit).comp (leviTorus k (Fin 2)).toMonoidHom with hδ`. Set `χ : (Fin 2 → kˣ) →* ℂˣ` to `torusChar ![μ₁, μ₂] * δ⁻¹`. Establish `hU : GlobalTheory.PRep.twKer π (unipB k (Fin 2)) 1 ≤ LinearMap.ker L`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨u, v, rfl⟩`.

Take `⟨u1, u2⟩` from `(mem_unipB k).1 u.2`. Establish `e : (u : GL (Fin 2) k) = Matrix.GeneralLinearGroup.scalar (Fin 2) 1 * aff (1 / 1) (u.1.val 0 1)`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [aff, u2, u1 1 0]`. Use `H 1 1 (u.1.val 0 1) v` as an intermediate fact.

Rewrite `this` using `[← e]`. Simplify using `[this]`. Set `l : GlobalTheory.PRep.Jacquet π (unipB k (Fin 2)) →ₗ[ℂ] ℂ` to `Submodule.liftQ _ L hU`. Choose the witnesses or unpack the hypotheses as in `⟨v, hv⟩ : ∃ v, L v ≠ 0 := by`. Assume the negation of the conclusion as `hn`.

Use `push Not at hn`. Conclude with `hL (LinearMap.ext hn)`. Establish `hle : ∀ t x, l (jacB π t x) = (χ t : ℂ) * l x` using `fun t x => by`. Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Establish `e : diagT k (Fin 2) t = Matrix.GeneralLinearGroup.scalar (Fin 2) (t 1) * aff (t 0 / t 1) 0`.

Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [aff, val_diagT, Matrix.GeneralLinearGroup.scalar, mul_div_cancel₀]`. Rewrite using `[UnramFixed.jacB_apply, jacBU_mk, map_smul, e]`. Express the relevant statement in the definitionally equal form `_ * L _ = _ * L y`. Rewrite using `[H, ← mul_assoc, ← Units.val_mul, mul_comm _ (μ₁ _ * _)]`.

Simplify using `[χ, torusChar_apply, hδ]`. Establish `hs : IsSmoothChar χ`. Use `Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset ((isSmooth_jacB hπ (Submodule.Quotient.mk v)).mem_nhds (by simp)) ?_)` and prove the remaining obligations. Introduce `g hg`. Establish `hg' : jacB π g (Submodule.Quotient.mk v) = Submodule.Quotient.mk v` using `hg`.

Establish `h` using `hle g (Submodule.Quotient.mk v)`. Rewrite `h` using `[hg']`. Conclude with `Units.ext (mul_right_cancel₀ (show l (Submodule.Quotient.mk v) ≠ 0 from hv) (h.symm.trans (one_mul _).symm))`. Establish `htc : torusChar (fun i => χ.comp (MonoidHom.mulSingle (fun _ => kˣ) i)) = χ` using `MonoidHom.ext fun t => by`. Rewrite using `[torusChar_apply]`.

Use `conv_rhs => rw [← Finset.univ_prod_mulSingle t, map_prod]`. Both sides reduce to the same expression. Use `⟨fun i => χ.comp (MonoidHom.mulSingle (fun _ => kˣ) i), fun i => hs.comp _ (continuous_mulSingle (A := fun _ => kˣ) i), ?_, fun x => ?_⟩` and prove the remaining obligations. Establish `key` using `GlobalTheory.SatakeExists.isSubquotient_of_eigenform hπ hi χ l (fun e => hv (LinearMap.congr_fun e (Submodule.Quotient.mk v))) hle`. Rewrite `key` using `[← htc]`.

Conclude with `key`. Establish `hd : ∀ (t : Fin 2 → kˣ) i, Matrix.GeneralLinearGroup.det (leviTorus k (Fin 2) t i) = t i` using `fun t => congrFun ((leviTorus k (Fin 2)).left_inv t)`. Establish `e0 : modExp (fun _ : Fin 2 => Unit) 0 = 1` using `by decide`. Establish `e1 : modExp (fun _ : Fin 2 => Unit) 1 = -1` using `by decide`. Establish `h1 : δ (Pi.mulSingle 0 x) = absPow k (1 / 2) x`.

Rewrite using `[hδ, MonoidHom.comp_apply]`. Express the relevant statement in the definitionally equal form `deltaHalf k (fun _ : Fin 2 => Unit) (leviTorus k (Fin 2) (Pi.mulSingle 0 x)) = _`. Rewrite using `[deltaHalf_apply, Fin.prod_univ_two, hd, hd, e0, e1]`. Simplify using the standard rewrite rules. Express the relevant statement in the definitionally equal form `torusChar ![μ₁, μ₂] (Pi.mulSingle 0 x) * (δ (Pi.mulSingle 0 x))⁻¹ = _`.

Rewrite using `[h1]`. Simplify using `[torusChar_apply]`.
-/
private theorem exists_ps {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin 2) k) V} (hπ : GlobalTheory.PRep.IsSmooth π)
    (hi : π.IsIrreducible) (μ₁ μ₂ : kˣ →* ℂˣ) (L : V →ₗ[ℂ] ℂ) (hL : L ≠ 0)
    (H : ∀ (a d : kˣ) (x : k) v, L (π (Matrix.GeneralLinearGroup.scalar (Fin 2) d * aff (a / d) x) v) =
      ((μ₁ a * μ₂ d : ℂˣ) : ℂ) * L v) :
    ∃ ψ : Fin 2 → kˣ →* ℂˣ, (∀ i, IsSmoothChar (ψ i)) ∧ IsSubquotient π (prinSeries ψ) ∧
      ∀ x : kˣ, ψ 0 x = μ₁ x * (absPow k (1 / 2) x)⁻¹ := by
  set δ : (Fin 2 → kˣ) →* ℂˣ := (deltaHalf k fun _ : Fin 2 => Unit).comp (leviTorus k (Fin 2)).toMonoidHom with hδ
  let χ : (Fin 2 → kˣ) →* ℂˣ := torusChar ![μ₁, μ₂] * δ⁻¹
  have hU : GlobalTheory.PRep.twKer π (unipB k (Fin 2)) 1 ≤ LinearMap.ker L := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, v, rfl⟩
    obtain ⟨u1, u2⟩ := (mem_unipB k).1 u.2
    have e : (u : GL (Fin 2) k) = Matrix.GeneralLinearGroup.scalar (Fin 2) 1 * aff (1 / 1) (u.1.val 0 1) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [aff, u2, u1 1 0]
    have := H 1 1 (u.1.val 0 1) v
    rw [← e] at this
    simp [this]
  let l : GlobalTheory.PRep.Jacquet π (unipB k (Fin 2)) →ₗ[ℂ] ℂ := Submodule.liftQ _ L hU
  obtain ⟨v, hv⟩ : ∃ v, L v ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hL (LinearMap.ext hn)
  have hle : ∀ t x, l (jacB π t x) = (χ t : ℂ) * l x := fun t x => by
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have e : diagT k (Fin 2) t = Matrix.GeneralLinearGroup.scalar (Fin 2) (t 1) * aff (t 0 / t 1) 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [aff, val_diagT, Matrix.GeneralLinearGroup.scalar, mul_div_cancel₀]
    rw [UnramFixed.jacB_apply, jacBU_mk, map_smul, e]
    change _ * L _ = _ * L y
    rw [H, ← mul_assoc, ← Units.val_mul, mul_comm _ (μ₁ _ * _)]
    simp [χ, torusChar_apply, hδ]
  have hs : IsSmoothChar χ := by
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset
      ((isSmooth_jacB hπ (Submodule.Quotient.mk v)).mem_nhds (by simp)) ?_)
    intro g hg
    have hg' : jacB π g (Submodule.Quotient.mk v) = Submodule.Quotient.mk v := hg
    have h := hle g (Submodule.Quotient.mk v)
    rw [hg'] at h
    exact Units.ext (mul_right_cancel₀ (show l (Submodule.Quotient.mk v) ≠ 0 from hv) (h.symm.trans (one_mul _).symm))
  have htc : torusChar (fun i => χ.comp (MonoidHom.mulSingle (fun _ => kˣ) i)) = χ :=
    MonoidHom.ext fun t => by
      rw [torusChar_apply]
      conv_rhs => rw [← Finset.univ_prod_mulSingle t, map_prod]
      rfl
  refine ⟨fun i => χ.comp (MonoidHom.mulSingle (fun _ => kˣ) i),
    fun i => hs.comp _ (continuous_mulSingle (A := fun _ => kˣ) i), ?_, fun x => ?_⟩
  · have key := GlobalTheory.SatakeExists.isSubquotient_of_eigenform hπ hi χ l
      (fun e => hv (LinearMap.congr_fun e (Submodule.Quotient.mk v))) hle
    rw [← htc] at key
    exact key
  · have hd : ∀ (t : Fin 2 → kˣ) i, Matrix.GeneralLinearGroup.det (leviTorus k (Fin 2) t i) = t i := fun t =>
      congrFun ((leviTorus k (Fin 2)).left_inv t)
    have e0 : modExp (fun _ : Fin 2 => Unit) 0 = 1 := by decide
    have e1 : modExp (fun _ : Fin 2 => Unit) 1 = -1 := by decide
    have h1 : δ (Pi.mulSingle 0 x) = absPow k (1 / 2) x := by
      rw [hδ, MonoidHom.comp_apply]
      change deltaHalf k (fun _ : Fin 2 => Unit) (leviTorus k (Fin 2) (Pi.mulSingle 0 x)) = _
      rw [deltaHalf_apply, Fin.prod_univ_two, hd, hd, e0, e1]
      simp
    change torusChar ![μ₁, μ₂] (Pi.mulSingle 0 x) * (δ (Pi.mulSingle 0 x))⁻¹ = _
    rw [h1]
    simp [torusChar_apply]

section Gal

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} {h : IsPlaceOver A w}

/- English proof (translation)
Take `⟨n, a, rfl⟩` from `x.exists_rep`. Rewrite using `[WD.lpTw_mk, WD.charPol_mk]`. Rewrite `hz` using `[WD.charPol_mk]`. Establish `h1` using `Module.End.hasEigenvalue_iff_isRoot_charpoly _ _ |>.2 hz`. Take `⟨v, hv⟩` from `h1.exists_hasEigenvector`.

Use `(Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).1 (Module.End.hasEigenvalue_of_hasEigenvector (x := v) ⟨?_, hv.2⟩)` and prove the remaining obligations. Rewrite using `[Module.End.mem_eigenspace_iff, WDRep.tw_ρ, LinearMap.smul_apply, hv.apply_eq_smul, smul_smul]`.
-/
private theorem root_lpTw (x : WD h) (s : ℝ) (g : Weil h) {z : ℂ} (hz : (x.charPol g).IsRoot z) :
    ((x.lpTw s).charPol g).IsRoot ((((normV w : ℕ) : ℂ) ^ (s : ℂ)) ^ deg g * z) := by
  obtain ⟨n, a, rfl⟩ := x.exists_rep
  rw [WD.lpTw_mk, WD.charPol_mk]
  rw [WD.charPol_mk] at hz
  have h1 := Module.End.hasEigenvalue_iff_isRoot_charpoly _ _ |>.2 hz
  obtain ⟨v, hv⟩ := h1.exists_hasEigenvector
  refine (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).1
    (Module.End.hasEigenvalue_of_hasEigenvector (x := v) ⟨?_, hv.2⟩)
  rw [Module.End.mem_eigenspace_iff, WDRep.tw_ρ, LinearMap.smul_apply, hv.apply_eq_smul, smul_smul]

end Gal

end UpperTheory.V.Z.Sym.Unl.UnlinkedPrincipalSeriesHeckeRoots

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial ValuativeRel
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.SmGL UpperTheory.V.Af
open UpperTheory.V.Sd UpperTheory.V.Z.Sym.Unl.UnlinkedPrincipalSeriesHeckeRoots

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Introduce `PH F Ω _ _ _ _ _ _ l _ ι ξ s c m a π r H w hl n lam hn hl0 hU A h t ht`. Establish `P` using `PH.toClassicalTheorems`. Take `⟨χ, hχ⟩` from `H.pol`. Take `⟨-, wt, HT, -, -, hall⟩` from `UpperTheory.GalN.V.exRN (exR PH) F Ω l ι 2 one_le_two π χ H.reg hχ`. Establish `hG` using `hall r H.cont H.att`.

Take `⟨⟨σ, hσ⟩, hiso⟩` from `locCompR P F 2 π w`. Take `⟨v, hv, hf, hUv⟩` from `hU`. Take `⟨T, hT, hTv⟩` from `rep_retr σ.ρ σ.irred (π.locRep w) (hiso σ hσ).2 v hv`. Take `⟨μ₁, μ₂, L, hL, hμ, hlam, hlaw⟩` from `jacqOfU P F w σ n (Units.mk0 lam hl0) hn ⟨T v, hTv, fun u hu => by rw [← hT, hf u hu], by`. Rewrite using `[Uop, ← map_dc σ.ρ (π.locRep w) T hT hTv, ← Uop, hUv, map_smul, Units.val_mk0]⟩`.

Take `⟨ψ, hψ, hs, hψ0⟩` from `exists_ps σ.smooth σ.irred μ₁ μ₂ L hL hlaw`. Take `⟨rc, hrc⟩` from `P.exists_rec h`. Set `g : Weil h` to `(⟨t, mem_Weil_of_isFrob h ht⟩ : Weil h)⁻¹`. Establish `hdeg : deg g = -1`. Rewrite using `[deg_inv, deg_eq_one_iff.2 ht]`.

Establish `hcont : Continuous fun g => ((r g : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l))` using `Units.continuous_val.comp H.cont`. Establish `e1` using `charPol_wdOf (h := h) hl ι hcont g`. Rewrite `e1` using `[(hG.away w hl A h rc hrc σ hσ).pol, rec_algNorm hrc]`. Take `⟨b, hb, ε, -, hLw⟩` from `id hrc`. Establish `h1` using `UpperTheory.V.AlgebraTools.jqRec F Ω A w h b hb ε rc hLw 2 ⟨σ.V, σ.ρ, σ.smooth, σ.irred⟩ ψ hψ hs g`.

Establish `hz : ((rc (IrrGL.of σ.ρ σ.smooth σ.irred)).charPol g).IsRoot ((ψ 0 (b g) : ℂˣ) : ℂ)`. Use `(?_ : (rc (cls ⟨σ.V, σ.ρ, σ.smooth, σ.irred⟩)).charPol g |>.IsRoot _)` and prove the remaining obligations. Rewrite using `[h1, Fin.prod_univ_two]`. Simplify using the standard rewrite rules. Establish `h2` using `root_lpTw _ ((1 - ((2 : ℕ) : ℝ)) / 2) g hz`.

Rewrite `h2` using `[e1]`. Establish `key : (((normV w : ℕ) : ℂ) ^ ((((1 - ((2 : ℕ) : ℝ)) / 2 : ℝ)) : ℂ)) ^ deg g * ((ψ 0 (b g) : ℂˣ) : ℂ) = lam`. Establish `hy : ord (w.adicCompletion F) (b g) = 1` using `by rw [hb.ord_eq, hdeg, neg_neg]`. Establish `hv0 : Valued.v ((b g : (w.adicCompletion F)ˣ) : w.adicCompletion F) ≠ 0` using `(Valuation.ne_zero_iff _).2 (Units.ne_zero _)`. Establish `hv1 : Valued.v ((b g : (w.adicCompletion F)ˣ) : w.adicCompletion F) = WithZero.exp (-1 : ℤ)`.

Rewrite `hy` using `[SphCompletion.ord_completion]`. Rewrite using `[← WithZero.exp_log hv0]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers. Establish `hu : IsUnitAt w (b g * (atFin w (unif w))⁻¹)`.

Establish `h2` using `unif_spec w`. Unfold `IsUnitAt IsUnifAt at *`. Rewrite using `[Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hv1, h2]`. Conclude with `mul_inv_cancel₀ (by simp)`. Establish `hμy : μ₁ (b g) = μ₁ (atFin w (unif w))`.

Conclude with `mul_inv_eq_one.1 (by rw [← map_inv, ← map_mul]; exact hμ _ hu)`. Establish `hA` using `GlobalTheory.SatChar.absPow_art hb (1 / 2 : ℝ) g`. Establish `hq : ((normV w : ℕ) : ℂ) ≠ 0`. Use `GlobalTheory.WeilDeligne.one_lt_normV w` as an intermediate fact. Conclude with `(zero_lt_one.trans this).ne'` after adjusting the coercions.

Establish `hQ2 : ((normV w : ℕ) : ℂ) ^ (((1 / 2 : ℝ)) : ℂ) * ((normV w : ℕ) : ℂ) ^ (((1 / 2 : ℝ)) : ℂ) = ((normV w : ℕ) : ℂ)`. Rewrite using `[← Complex.cpow_add _ _ hq]`. Evaluate the numerical expressions. Establish `hs' : ((((1 - ((2 : ℕ) : ℝ)) / 2 : ℝ)) : ℂ) = -(((1 / 2 : ℝ)) : ℂ)`. Use `push_cast`.

Evaluate the numerical expressions. Establish `hc : ((1 / 2 : ℂ)) = (((1 / 2 : ℝ)) : ℂ)`. Use `push_cast`. Both sides reduce to the same expression. Rewrite `hA` using `[hdeg]`.

Rewrite using `[hψ0, Units.val_mul, Units.val_inv_eq_inv_val, hc, hA, hμy, hs', hdeg, Complex.cpow_neg]`. Establish `hl'` using `hlam`. Rewrite `hl'` using `[Units.val_mk0]`. Generalize the expression as in `((normV w : ℕ) : ℂ) ^ (((1 / 2 : ℝ)) : ℂ) = Q at hQ2 ⊢`. Rewrite using `[← hl', ← hQ2]`.

Simplify using `only [zpow_neg, zpow_one, inv_inv]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h2` using `[key]`. Use `⟨ι.symm lam, ?_, by simp⟩` and prove the remaining obligations. Establish `h3 : ι.toRingHom (ι.symm lam) = lam` using `ι.apply_symm_apply lam`.

Rewrite `h2` using `[← h3]`. Conclude with `(Polynomial.isRoot_map_iff ι.injective).1 h2`.
-/
theorem UpperTheory.V.Z.Sym.Unl.tieU :
    UpperTheory.V.Af.HypothesesH → UpperTheory.V.Z.Sym.Unl.TieU := by
  intro PH F Ω _ _ _ _ _ _ l _ ι ξ s c m a π r H w hl n lam hn hl0 hU A h t ht
  have P := PH.toClassicalTheorems
  obtain ⟨χ, hχ⟩ := H.pol
  obtain ⟨-, wt, HT, -, -, hall⟩ := UpperTheory.GalN.V.exRN (exR PH) F Ω l ι 2 one_le_two π χ H.reg hχ
  have hG := hall r H.cont H.att
  obtain ⟨⟨σ, hσ⟩, hiso⟩ := locCompR P F 2 π w
  obtain ⟨v, hv, hf, hUv⟩ := hU
  obtain ⟨T, hT, hTv⟩ := rep_retr σ.ρ σ.irred (π.locRep w) (hiso σ hσ).2 v hv
  obtain ⟨μ₁, μ₂, L, hL, hμ, hlam, hlaw⟩ := jacqOfU P F w σ n (Units.mk0 lam hl0) hn
    ⟨T v, hTv, fun u hu => by rw [← hT, hf u hu], by
      rw [Uop, ← map_dc σ.ρ (π.locRep w) T hT hTv, ← Uop, hUv, map_smul, Units.val_mk0]⟩
  obtain ⟨ψ, hψ, hs, hψ0⟩ := exists_ps σ.smooth σ.irred μ₁ μ₂ L hL hlaw
  obtain ⟨rc, hrc⟩ := P.exists_rec h
  let g : Weil h := (⟨t, mem_Weil_of_isFrob h ht⟩ : Weil h)⁻¹
  have hdeg : deg g = -1 := by
    rw [deg_inv, deg_eq_one_iff.2 ht]
  have hcont : Continuous fun g => ((r g : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) :=
    Units.continuous_val.comp H.cont
  have e1 := charPol_wdOf (h := h) hl ι hcont g
  rw [(hG.away w hl A h rc hrc σ hσ).pol, rec_algNorm hrc] at e1
  obtain ⟨b, hb, ε, -, hLw⟩ := id hrc
  have h1 := UpperTheory.V.AlgebraTools.jqRec F Ω A w h b hb ε rc hLw 2 ⟨σ.V, σ.ρ, σ.smooth, σ.irred⟩ ψ hψ hs g
  have hz : ((rc (IrrGL.of σ.ρ σ.smooth σ.irred)).charPol g).IsRoot ((ψ 0 (b g) : ℂˣ) : ℂ) := by
    refine (?_ : (rc (cls ⟨σ.V, σ.ρ, σ.smooth, σ.irred⟩)).charPol g |>.IsRoot _)
    rw [h1, Fin.prod_univ_two]
    simp
  have h2 := root_lpTw _ ((1 - ((2 : ℕ) : ℝ)) / 2) g hz
  rw [e1] at h2
  have key : (((normV w : ℕ) : ℂ) ^ ((((1 - ((2 : ℕ) : ℝ)) / 2 : ℝ)) : ℂ)) ^ deg g * ((ψ 0 (b g) : ℂˣ) : ℂ) = lam := by
    have hy : ord (w.adicCompletion F) (b g) = 1 := by rw [hb.ord_eq, hdeg, neg_neg]
    have hv0 : Valued.v ((b g : (w.adicCompletion F)ˣ) : w.adicCompletion F) ≠ 0 :=
      (Valuation.ne_zero_iff _).2 (Units.ne_zero _)
    have hv1 : Valued.v ((b g : (w.adicCompletion F)ˣ) : w.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
      rw [SphCompletion.ord_completion] at hy
      rw [← WithZero.exp_log hv0]
      congr 1
      omega
    have hu : IsUnitAt w (b g * (atFin w (unif w))⁻¹) := by
      have h2 := unif_spec w
      unfold IsUnitAt IsUnifAt at *
      rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hv1, h2]
      exact mul_inv_cancel₀ (by simp)
    have hμy : μ₁ (b g) = μ₁ (atFin w (unif w)) := by
      exact mul_inv_eq_one.1 (by rw [← map_inv, ← map_mul]; exact hμ _ hu)
    have hA := GlobalTheory.SatChar.absPow_art hb (1 / 2 : ℝ) g
    have hq : ((normV w : ℕ) : ℂ) ≠ 0 := by
      have := GlobalTheory.WeilDeligne.one_lt_normV w
      exact_mod_cast (zero_lt_one.trans this).ne'
    have hQ2 : ((normV w : ℕ) : ℂ) ^ (((1 / 2 : ℝ)) : ℂ) * ((normV w : ℕ) : ℂ) ^ (((1 / 2 : ℝ)) : ℂ) = ((normV w : ℕ) : ℂ) := by
      rw [← Complex.cpow_add _ _ hq]
      norm_num
    have hs' : ((((1 - ((2 : ℕ) : ℝ)) / 2 : ℝ)) : ℂ) = -(((1 / 2 : ℝ)) : ℂ) := by
      push_cast
      norm_num
    have hc : ((1 / 2 : ℂ)) = (((1 / 2 : ℝ)) : ℂ) := by
      push_cast
      rfl
    rw [hdeg] at hA
    rw [hψ0, Units.val_mul, Units.val_inv_eq_inv_val, hc, hA, hμy, hs', hdeg, Complex.cpow_neg]
    have hl' := hlam
    rw [Units.val_mk0] at hl'
    generalize ((normV w : ℕ) : ℂ) ^ (((1 / 2 : ℝ)) : ℂ) = Q at hQ2 ⊢
    rw [← hl', ← hQ2]
    simp only [zpow_neg, zpow_one, inv_inv]
    ring
  rw [key] at h2
  refine ⟨ι.symm lam, ?_, by simp⟩
  have h3 : ι.toRingHom (ι.symm lam) = lam := ι.apply_symm_apply lam
  rw [← h3] at h2
  exact (Polynomial.isRoot_map_iff ι.injective).1 h2
