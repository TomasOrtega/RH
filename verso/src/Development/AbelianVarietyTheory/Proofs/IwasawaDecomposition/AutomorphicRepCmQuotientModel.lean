import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfOfNodupAlg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SubrepTopToSubmodule
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.AutModel

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
  {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

def compE (e : W ≃ₗ[ℂ] W') : (GAf L n → W) ≃ₗ[ℂ] (GAf L n → W') :=
  LinearEquiv.piCongrRight fun _ => e

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem compE_apply (e : W ≃ₗ[ℂ] W') (f : GAf L n → W) (g : GAf L n) :
    compE (L := L) (n := n) e f g = e (f g) := rfl

/- English proof (translation)
The claim follows from `LinearEquiv.ext fun _ => rfl`.
-/
theorem compE_symm (e : W ≃ₗ[ℂ] W') : compE (L := L) (n := n) e.symm = (compE e).symm :=
  LinearEquiv.ext fun _ => rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem rt_compE (e : W ≃ₗ[ℂ] W') (h : GAf L n) (f : GAf L n → W) :
    NG.rt L n h (compE e f) = compE e (NG.rt L n h f) := rfl

def conjRep (e : W ≃ₗ[ℂ] W') (ρ : Representation ℂ (GQ L n) W) : Representation ℂ (GQ L n) W' where
  toFun γ := e.toLinearMap ∘ₗ ρ γ ∘ₗ e.symm.toLinearMap
  map_one' := by ext x; simp
  map_mul' a b := by ext x; simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem conjRep_apply (e : W ≃ₗ[ℂ] W') (ρ : Representation ℂ (GQ L n) W) (γ : GQ L n) (x : W') :
    conjRep e ρ γ x = e (ρ γ (e.symm x)) := rfl

/- English proof (translation)
Simplify using `[conjRep_apply]`.
-/
theorem conjRep_inter (e : W ≃ₗ[ℂ] W') (ρ : Representation ℂ (GQ L n) W) (γ : GQ L n) (x : W) :
    e (ρ γ x) = conjRep e ρ γ (e x) := by simp [conjRep_apply]

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨f, hf, rfl⟩`. Take `⟨h1, N, hN, h2⟩` from `hS.le hf`. Use `⟨fun γ g => ?_, N, hN, fun κ hκ g => ?_⟩` and prove the remaining obligations. Simplify using `[h1 γ g, he]`.

Simplify using `[h2 κ hκ g]`. Introduce and unpack `h _ ⟨f, hf, rfl⟩`. Conclude with `⟨NG.rt L n h f, hS.stable h f hf, rfl⟩`.
-/
theorem isSubrep_map (e : W ≃ₗ[ℂ] W') {ρ : Representation ℂ (GQ L n) W} {ρ' : Representation ℂ (GQ L n) W'}
    (he : ∀ γ x, e (ρ γ x) = ρ' γ (e x)) {S : Submodule ℂ (GAf L n → W)} (hS : NG.IsSubrep ρ S) :
    NG.IsSubrep ρ' (S.map (compE (L := L) (n := n) e : (GAf L n → W) →ₗ[ℂ] (GAf L n → W'))) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨f, hf, rfl⟩
    obtain ⟨h1, N, hN, h2⟩ := hS.le hf
    refine ⟨fun γ g => ?_, N, hN, fun κ hκ g => ?_⟩
    · simp [h1 γ g, he]
    · simp [h2 κ hκ g]
  · rintro h _ ⟨f, hf, rfl⟩
    exact ⟨NG.rt L n h f, hS.stable h f hf, rfl⟩

/- English proof (translation)
Establish `he' : ∀ γ y, e.symm (ρ' γ y) = ρ γ (e.symm y)` using `fun γ y => by`. Apply `e.injective` to reduce the goal to its premises. Rewrite using `[he]`. Simplify using the standard rewrite rules. Take `⟨hsub, hne, hmin⟩` from `hS`.

Use `⟨isSubrep_map e he hsub, ?_, fun S' hS' hle => ?_⟩` and prove the remaining obligations. Introduce `h0`. Apply `hne` to reduce the goal to its premises. Use `congrArg (Submodule.comap (compE (L := L) (n := n) e : (GAf L n → W) →ₗ[ℂ] (GAf L n → W'))) h0` as an intermediate fact. Rewrite `this` using `[Submodule.comap_map_eq_of_injective (compE (L := L) (n := n) e).injective, Submodule.comap_bot, LinearMap.ker_eq_bot.mpr (compE (L := L) (n := n) e).injective]`. Then use the resulting hypothesis.

Use `set T := S'.comap (compE (L := L) (n := n) e : (GAf L n → W) →ₗ[ℂ] (GAf L n → W')) with hT`. Establish `hTm : T = S'.map (compE (L` using `L) (n := n) e.symm : (GAf L n → W') →ₗ[ℂ] (GAf L n → W)) := by`. Rewrite using `[compE_symm, Submodule.map_equiv_eq_comap_symm, LinearEquiv.symm_symm]`. Establish `hTs : NG.IsSubrep ρ T` using `hTm ▸ isSubrep_map e.symm he' hS'`. Establish `hTle : T ≤ S`.

Use `Submodule.comap_mono (f := (compE (L := L) (n := n) e : (GAf L n → W) →ₗ[ℂ] (GAf L n → W'))) hle` as an intermediate fact. Rewrite `this` using `[Submodule.comap_map_eq_of_injective (compE (L := L) (n := n) e).injective]`. Then use the resulting hypothesis. Establish `hS'eq : S' = T.map (compE (L` using `L) (n := n) e : (GAf L n → W) →ₗ[ℂ] (GAf L n → W')) := by`. Rewrite using `[hT, Submodule.map_comap_eq_of_surjective (compE (L := L) (n := n) e).surjective]`. Break down `hmin T hTs hTle with h | h` into its components or cases.

Use `left`. Rewrite using `[hS'eq, h, Submodule.map_bot]`. Use `right`. Rewrite using `[hS'eq, h]`.
-/
theorem isIrrRep_map (e : W ≃ₗ[ℂ] W') {ρ : Representation ℂ (GQ L n) W} {ρ' : Representation ℂ (GQ L n) W'}
    (he : ∀ γ x, e (ρ γ x) = ρ' γ (e x)) {S : Submodule ℂ (GAf L n → W)} (hS : NG.IsIrrRep ρ S) :
    NG.IsIrrRep ρ' (S.map (compE (L := L) (n := n) e : (GAf L n → W) →ₗ[ℂ] (GAf L n → W'))) := by
  have he' : ∀ γ y, e.symm (ρ' γ y) = ρ γ (e.symm y) := fun γ y => by
    apply e.injective; rw [he]; simp
  obtain ⟨hsub, hne, hmin⟩ := hS
  refine ⟨isSubrep_map e he hsub, ?_, fun S' hS' hle => ?_⟩
  · intro h0
    apply hne
    have := congrArg (Submodule.comap (compE (L := L) (n := n) e : (GAf L n → W) →ₗ[ℂ] (GAf L n → W'))) h0
    rwa [Submodule.comap_map_eq_of_injective (compE (L := L) (n := n) e).injective, Submodule.comap_bot,
      LinearMap.ker_eq_bot.mpr (compE (L := L) (n := n) e).injective] at this
  · set T := S'.comap (compE (L := L) (n := n) e : (GAf L n → W) →ₗ[ℂ] (GAf L n → W')) with hT
    have hTm : T = S'.map (compE (L := L) (n := n) e.symm : (GAf L n → W') →ₗ[ℂ] (GAf L n → W)) := by
      rw [compE_symm, Submodule.map_equiv_eq_comap_symm, LinearEquiv.symm_symm]
    have hTs : NG.IsSubrep ρ T := hTm ▸ isSubrep_map e.symm he' hS'
    have hTle : T ≤ S := by
      have := Submodule.comap_mono (f := (compE (L := L) (n := n) e : (GAf L n → W) →ₗ[ℂ] (GAf L n → W'))) hle
      rwa [Submodule.comap_map_eq_of_injective (compE (L := L) (n := n) e).injective] at this
    have hS'eq : S' = T.map (compE (L := L) (n := n) e : (GAf L n → W) →ₗ[ℂ] (GAf L n → W')) := by
      rw [hT, Submodule.map_comap_eq_of_surjective (compE (L := L) (n := n) e).surjective]
    rcases hmin T hTs hTle with h | h
    · left; rw [hS'eq, h, Submodule.map_bot]
    · right; rw [hS'eq, h]

/- English proof (translation)
Use `⟨(compE e).submoduleMap S, fun h f f' hf => ?_⟩` and prove the remaining obligations. Simplify using `only [LinearEquiv.submoduleMap_apply]`. Rewrite using `[hf, rt_compE]`.
-/
theorem isoRep_map (e : W ≃ₗ[ℂ] W') (S : Submodule ℂ (GAf L n → W)) :
    NG.IsoRep S (S.map (compE (L := L) (n := n) e : (GAf L n → W) →ₗ[ℂ] (GAf L n → W'))) := by
  refine ⟨(compE e).submoduleMap S, fun h f f' hf => ?_⟩
  simp only [LinearEquiv.submoduleMap_apply]
  rw [hf, rt_compE]

omit [Field L] [NumberField L] [IsCMField L] in
/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.SubrepTopBot.main`. Consider the case `exact _root_.GlobalTheory.SubrepTopBot.main`. Consider the case `(apply _root_.GlobalTheory.SubrepTopBot.main <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.SubrepTopBot.main <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.SubrepTopBot.main <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.SubrepTopBot.main ..)`.
-/
theorem irr_iff {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) :
    ρ.IsIrreducible ↔ Nontrivial V ∧
      ∀ U : Submodule ℂ V, (∀ g : G, ∀ v ∈ U, ρ g v ∈ U) → U = ⊥ ∨ U = ⊤ := by
  first
  | exact @_root_.GlobalTheory.SubrepTopBot.main
  | exact _root_.GlobalTheory.SubrepTopBot.main
  | (apply _root_.GlobalTheory.SubrepTopBot.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SubrepTopBot.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SubrepTopBot.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SubrepTopBot.main ..)

/- English proof (translation)
Rewrite `h`, the goal using `[irr_iff]`. Take `⟨hW, hmin⟩` from `h`. Use `⟨e.symm.surjective.nontrivial, fun U' hU' => ?_⟩` and prove the remaining obligations. Establish `hU : ∀ γ, ∀ x ∈ U'.comap (e : W →ₗ[ℂ] W'), ρ γ x ∈ U'.comap (e : W →ₗ[ℂ] W')`. Introduce `γ x hx`.

Simplify using `only [Submodule.mem_comap, LinearEquiv.coe_coe] at hx ⊢`. Rewrite using `[conjRep_inter]`. Conclude with `hU' γ _ hx`. Establish `hback : U' = (U'.comap (e : W →ₗ[ℂ] W')).map (e : W →ₗ[ℂ] W')` using `(Submodule.map_comap_eq_of_surjective e.surjective U').symm`. Break down `hmin _ hU with h0 | h0` into its components or cases.

Use `left`. Rewrite using `[hback, h0, Submodule.map_bot]`. Use `right`. Rewrite using `[hback, h0, Submodule.map_top, LinearMap.range_eq_top.mpr e.surjective]`.
-/
theorem irr_conj (e : W ≃ₗ[ℂ] W') {ρ : Representation ℂ (GQ L n) W} (h : ρ.IsIrreducible) :
    (conjRep e ρ).IsIrreducible := by
  rw [irr_iff] at h ⊢
  obtain ⟨hW, hmin⟩ := h
  refine ⟨e.symm.surjective.nontrivial, fun U' hU' => ?_⟩
  have hU : ∀ γ, ∀ x ∈ U'.comap (e : W →ₗ[ℂ] W'), ρ γ x ∈ U'.comap (e : W →ₗ[ℂ] W') := by
    intro γ x hx
    simp only [Submodule.mem_comap, LinearEquiv.coe_coe] at hx ⊢
    rw [conjRep_inter]; exact hU' γ _ hx
  have hback : U' = (U'.comap (e : W →ₗ[ℂ] W')).map (e : W →ₗ[ℂ] W') :=
    (Submodule.map_comap_eq_of_surjective e.surjective U').symm
  rcases hmin _ hU with h0 | h0
  · left; rw [hback, h0, Submodule.map_bot]
  · right; rw [hback, h0, Submodule.map_top, LinearMap.range_eq_top.mpr e.surjective]

/- English proof (translation)
Take `⟨-, ι, hι, hd, b, P, hP⟩` from `h`. Use `⟨inferInstance, ι, hι, hd, b.map e, P, fun γ γ₀ hγ => ?_⟩` and prove the remaining obligations. Rewrite using `[← hP γ γ₀ hγ]`. Use extensionality with `i j`. Simplify using `[LinearMap.toMatrix_apply, conjRep_apply]`.
-/
theorem alg_conj (e : W ≃ₗ[ℂ] W') {ρ : Representation ℂ (GQ L n) W} (h : IsAlgWeight L n ρ)
    [FiniteDimensional ℂ W'] : IsAlgWeight L n (conjRep e ρ) := by
  obtain ⟨-, ι, hι, hd, b, P, hP⟩ := h
  refine ⟨inferInstance, ι, hι, hd, b.map e, P, fun γ γ₀ hγ => ?_⟩
  rw [← hP γ γ₀ hγ]
  ext i j
  simp [LinearMap.toMatrix_apply, conjRep_apply]

/- English proof (translation)
Use `haveI : FiniteDimensional ℂ π.W := π.alg.1`. Set `e : π.W ≃ₗ[ℂ] (Fin (Module.finrank ℂ π.W) → ℂ)` to `(Module.finBasis ℂ π.W).equivFun`. Set `m : GlobalTheory.AutQuot.AutRepM L n` to `{ d := Module.finrank ℂ π.W ρ := conjRep e π.ρ alg := alg_conj e π.alg irr := irr_conj e π.irr S := π.S.map (compE (L := L) (n := n) e : (GAf L n → π.W) →ₗ[ℂ] (GAf L n → _)) irrS := isIrrRep_map e (conjRep_inter e π.ρ) π.irrS }`. Conclude with `⟨m, ⟨e, conjRep_inter e π.ρ⟩, isoRep_map e π.S⟩`.
-/
theorem exists_autRepM (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.AutRep L n) :
    ∃ m : GlobalTheory.AutQuot.AutRepM L n, π.Iso m.toAutRep := by
  haveI : FiniteDimensional ℂ π.W := π.alg.1
  let e : π.W ≃ₗ[ℂ] (Fin (Module.finrank ℂ π.W) → ℂ) := (Module.finBasis ℂ π.W).equivFun
  let m : GlobalTheory.AutQuot.AutRepM L n :=
    { d := Module.finrank ℂ π.W
      ρ := conjRep e π.ρ
      alg := alg_conj e π.alg
      irr := irr_conj e π.irr
      S := π.S.map (compE (L := L) (n := n) e : (GAf L n → π.W) →ₗ[ℂ] (GAf L n → _))
      irrS := isIrrRep_map e (conjRep_inter e π.ρ) π.irrS }
  exact ⟨m, ⟨e, conjRep_inter e π.ρ⟩, isoRep_map e π.S⟩

end GlobalTheory.AutModel

end
