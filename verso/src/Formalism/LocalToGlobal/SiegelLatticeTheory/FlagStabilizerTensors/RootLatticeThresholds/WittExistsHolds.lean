import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TermTieOf
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.TermTiesEmptyOfLargeIndex
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WittExtensionTheorem

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting

namespace Formalism.L2.SG.Pf.WittFlags

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Flag

variable {D : D7} {T : D.host.E}

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨a, rfl⟩` from `hy`. Conclude with `F.z_orth a`. Consider the case `zero => simp`.

Consider the case `add y w _ _ hy hw => simp [hy, hw]`. Consider the case `smul c y _ hy => simp [hy]`.
-/
theorem flag_span_orth (F : FlagG (VS D) D.R.rS T) {x : (VS D).V}
    (hx : x ∈ Submodule.span D.host.E (Set.range F.e)) : (VS D).hT x F.z = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    exact F.z_orth a
  | zero => simp
  | add y w _ _ hy hw => simp [hy, hw]
  | smul c y _ hy => simp [hy]

/- English proof (translation)
Unfold `FlagG.fvec`. Rewrite using `[linearIndependent_finSnoc]`. Use `⟨F.e_indep, fun hz => hT ?_⟩` and prove the remaining obligations. Establish `h1` using `flag_span_orth F hz`. Rewrite `h1` using `[F.z_norm]`.

Conclude with `neg_eq_zero.1 h1`.
-/
theorem flag_fvec_indep (hT : T ≠ 0) (F : FlagG (VS D) D.R.rS T) : LinearIndependent D.host.E F.fvec := by
  unfold FlagG.fvec
  rw [linearIndependent_finSnoc]
  refine ⟨F.e_indep, fun hz => hT ?_⟩
  have h1 := flag_span_orth F hz
  rw [F.z_norm] at h1
  exact neg_eq_zero.1 h1

/- English proof (translation)
Substitute `hTT` using the available equality. Establish `hze : ∀ (G : FlagG (VS D) D.R.rS T) (a : Fin D.R.rS), (VS D).hT G.z (G.e a) = 0`. Introduce `G a`. Rewrite using `[← (VS D).herm.eq (G.e a) G.z, G.z_orth a, map_zero]`. Proceed by induction on `i using Fin.lastCases with`.

Consider the case `last`. Proceed by induction on `j using Fin.lastCases with`. Consider the case `last => simp only [FlagG.fvec, Fin.snoc_last, F.z_norm, F'.z_norm]`. Consider the case `cast b => simp only [FlagG.fvec, Fin.snoc_last, Fin.snoc_castSucc, hze]`. Consider the case `cast a`.

Proceed by induction on `j using Fin.lastCases with`. Consider the case `last => simp only [FlagG.fvec, Fin.snoc_last, Fin.snoc_castSucc, F.z_orth, F'.z_orth]`. Consider the case `cast b => simp only [FlagG.fvec, Fin.snoc_castSucc, F.e_iso, F'.e_iso]`.
-/
theorem flag_gram {T' : D.host.E} (hTT : T = T') (F : FlagG (VS D) D.R.rS T) (F' : FlagG (VS D) D.R.rS T')
    (i j : Fin (D.R.rS + 1)) :
    (VS D).hT (F.fvec i) (F.fvec j) = (VS D).hT (F'.fvec i) (F'.fvec j) := by
  subst hTT
  have hze : ∀ (G : FlagG (VS D) D.R.rS T) (a : Fin D.R.rS), (VS D).hT G.z (G.e a) = 0 := by
    intro G a
    rw [← (VS D).herm.eq (G.e a) G.z, G.z_orth a, map_zero]
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp only [FlagG.fvec, Fin.snoc_last, F.z_norm, F'.z_norm]
    | cast b => simp only [FlagG.fvec, Fin.snoc_last, Fin.snoc_castSucc, hze]
  | cast a =>
    induction j using Fin.lastCases with
    | last => simp only [FlagG.fvec, Fin.snoc_last, Fin.snoc_castSucc, F.z_orth, F'.z_orth]
    | cast b => simp only [FlagG.fvec, Fin.snoc_castSucc, F.e_iso, F'.e_iso]

/- English proof (translation)
Establish `hind` using `flag_fvec_indep hT F`. Establish `hind'` using `flag_fvec_indep (hTT ▸ hT) F'`. Use `set U := Submodule.span D.host.E (Set.range F.fvec) with hU`. Set `b : Module.Basis (Fin (D.R.rS + 1)) D.host.E U` to `Module.Basis.span hind`. Set `f : U →ₗ[D.host.E] (VS D).V` to `Finsupp.linearCombination D.host.E F'.fvec ∘ₗ (b.repr : U →ₗ[D.host.E] (Fin (D.R.rS + 1) →₀ D.host.E))`.

Establish `hfb : ∀ i, f (b i) = F'.fvec i`. Introduce `i`. Simplify using `[f, Module.Basis.repr_self, Finsupp.linearCombination_single]`. Establish `hbv : ∀ i, ((b i : U) : (VS D).V) = F.fvec i`. Introduce `i`.

Conclude with `congrArg Subtype.val (Module.Basis.span_apply hind i)`. Establish `hinj : Function.Injective f`. Establish `h2 : Function.Injective (Finsupp.linearCombination D.host.E F'.fvec)` using `hind'`. Conclude with `h2.comp b.repr.injective`. Establish `hB : ((VS D).hT.comp f).compl₂ f = ((VS D).hT.comp U.subtype).compl₂ U.subtype`.

Use `LinearMap.ext_basis b b fun i j => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.compl₂_apply, LinearMap.comp_apply, hfb, Submodule.subtype_apply, hbv]`. Conclude with `(flag_gram hTT F F' i j).symm`. Establish `hiso : ∀ x y : U, (VS D).hT (f x) (f y) = (VS D).hT x y`. Introduce `x y`.

Establish `h` using `congrArg (fun B => B x y) hB`. Simplify `h` using `only [LinearMap.compl₂_apply, LinearMap.comp_apply, Submodule.subtype_apply]`. Take `⟨g, hg, hgf⟩` from `_root_.witt_extension_theorem D.host.E (VS D).V (VS D).hT (fun x y => (VS D).herm.eq x y) (fun x hx => (VS D).nondeg.1 x hx) U f hinj hiso`. Establish `hgi : ∀ i, g (F.fvec i) = F'.fvec i`. Introduce `i`.

Establish `h` using `hgf (b i)`. Rewrite `h` using `[hbv, hfb]`. Conclude with `h`. Use `⟨g, hg, fun a => ?_, ?_⟩` and prove the remaining obligations. Establish `h` using `hgi (Fin.castSucc a)`.

Simplify `h` using `only [FlagG.fvec, Fin.snoc_castSucc]`. Establish `h` using `hgi (Fin.last _)`. Simplify `h` using `only [FlagG.fvec, Fin.snoc_last]`.
-/
theorem flag_witt {T' : D.host.E} (hT : T ≠ 0) (hTT : T = T') (F : FlagG (VS D) D.R.rS T)
    (F' : FlagG (VS D) D.R.rS T') :
    ∃ δ : (VS D).V ≃ₗ[D.host.E] (VS D).V, δ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧ (∀ a, δ (F.e a) = F'.e a) ∧
      δ F.z = F'.z := by
  have hind := flag_fvec_indep hT F
  have hind' := flag_fvec_indep (hTT ▸ hT) F'
  set U := Submodule.span D.host.E (Set.range F.fvec) with hU
  let b : Module.Basis (Fin (D.R.rS + 1)) D.host.E U := Module.Basis.span hind
  let f : U →ₗ[D.host.E] (VS D).V :=
    Finsupp.linearCombination D.host.E F'.fvec ∘ₗ (b.repr : U →ₗ[D.host.E] (Fin (D.R.rS + 1) →₀ D.host.E))
  have hfb : ∀ i, f (b i) = F'.fvec i := by
    intro i
    simp [f, Module.Basis.repr_self, Finsupp.linearCombination_single]
  have hbv : ∀ i, ((b i : U) : (VS D).V) = F.fvec i := by
    intro i
    exact congrArg Subtype.val (Module.Basis.span_apply hind i)
  have hinj : Function.Injective f := by
    have h2 : Function.Injective (Finsupp.linearCombination D.host.E F'.fvec) := hind'
    exact h2.comp b.repr.injective
  have hB : ((VS D).hT.comp f).compl₂ f = ((VS D).hT.comp U.subtype).compl₂ U.subtype := by
    refine LinearMap.ext_basis b b fun i j => ?_
    simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, hfb, Submodule.subtype_apply, hbv]
    exact (flag_gram hTT F F' i j).symm
  have hiso : ∀ x y : U, (VS D).hT (f x) (f y) = (VS D).hT x y := by
    intro x y
    have h := congrArg (fun B => B x y) hB
    simpa only [LinearMap.compl₂_apply, LinearMap.comp_apply, Submodule.subtype_apply] using h
  obtain ⟨g, hg, hgf⟩ := _root_.witt_extension_theorem D.host.E (VS D).V (VS D).hT
    (fun x y => (VS D).herm.eq x y) (fun x hx => (VS D).nondeg.1 x hx) U f hinj hiso
  have hgi : ∀ i, g (F.fvec i) = F'.fvec i := by
    intro i
    have h := hgf (b i)
    rw [hbv, hfb] at h
    exact h
  refine ⟨g, hg, fun a => ?_, ?_⟩
  · have h := hgi (Fin.castSucc a)
    simpa only [FlagG.fvec, Fin.snoc_castSucc] using h
  · have h := hgi (Fin.last _)
    simpa only [FlagG.fvec, Fin.snoc_last] using h

end Flag

/- English proof (translation)
Establish `hT : ∀ u : D.what₂.Word, (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0` using `fun u => Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero`. Use `choose δ hδ he hz using fun u => flag_witt (hT u) rfl (X.Fu u) (Formalism.MainNotions.S.Inh.tie_flag0 D u)`. Use `⟨{ δ := δ, isom := hδ, e_eq := fun u a => ?_, z_eq := fun u => ?_ }⟩` and prove the remaining obligations. Establish `h` using `he u a`. Rewrite `h` using `[X.Fu_e u]`.

Conclude with `h`. Establish `h` using `hz u`. Rewrite `h` using `[X.flagZVector u]`. Conclude with `h`.
-/
theorem WittExists_holds (D : D7) (X : HidaSetting D) : Formalism.L2.SG.TermTieOf.WittExists X := by
  have hT : ∀ u : D.what₂.Word, (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 := fun u =>
    Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero
  choose δ hδ he hz using fun u => flag_witt (hT u) rfl (X.Fu u) (Formalism.MainNotions.S.Inh.tie_flag0 D u)
  refine ⟨{ δ := δ, isom := hδ, e_eq := fun u a => ?_, z_eq := fun u => ?_ }⟩
  · have h := he u a
    rw [X.Fu_e u] at h
    exact h
  · have h := hz u
    rw [X.flagZVector u] at h
    exact h

end Formalism.L2.SG.Pf.WittFlags
