import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.AllHolds

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

/- English proof (translation)
Introduce `l _ B hl n i Z Y p q s _ _ W r c hc J _ σ hσ hsp x`. Take `⟨hsc, hiso⟩` from `hsp`. Establish `hT` using `UpperTheory.Gal.TranscendenceTraces.adic.2.2.2.2.2.2.2.2.2`. Set `e` to `Fintype.equivFin J`. Establish `hiso' : IsIso (Sigma.desc fun k : Fin (Fintype.card J) => pullback.lift (σ (e.symm k)) (𝟙 W) (by rw [hsc, Category.id_comp]))`.

Establish `hEq : (Sigma.desc fun k : Fin (Fintype.card J) => pullback.lift (σ (e.symm k)) (𝟙 W) (by rw [hsc, Category.id_comp])) = (Sigma.reindex e.symm (fun _ : J => W)).hom ≫ Sigma.desc fun j => pullback.lift (σ j) (𝟙 W) (by rw [hsc, Category.id_comp])`. Use `Sigma.hom_ext _ _ (fun k => ?_)` and prove the remaining obligations. Rewrite using `[Sigma.ι_desc]`. Establish `h4` using `Sigma.ι_reindex_hom_assoc (ε := e.symm) (f := fun _ : J => W) (b := k) (h := Sigma.desc fun j => pullback.lift (σ j) (𝟙 W) (by rw [hsc, Category.id_comp]))`. Rewrite `h4` using `[Sigma.ι_desc]`.

Conclude with `h4.symm`. Rewrite using `[hEq]`. Use `infer_instance`. Establish `hlZ : IsUnit ((l : Γ(Z, ⊤)))`. Simplify using `using hl.map (Scheme.Hom.appTop p).hom`.

Establish `h1` using `hT l n i s hlZ W c (Fintype.card J) (fun k => σ (e.symm k)) (fun k => hsc _) hiso'`. Establish `h2 : ∀ y : HQ l (sch.obj Y) n i, pullHQ l (sch.map c) n i (TranscendenceTraces.trHQ l s (TranscendenceTraces.Wt.const Y 1) n i y) = ∑ j, pullHQ l (sch.map (σ j)) n i y`. Introduce `y`. Establish `h3` using `LinearMap.congr_fun h1 y`. Rewrite `h3` using `[LinearMap.comp_apply, LinearMap.sum_apply]`.

Rewrite using `[h3]`. Conclude with `Equiv.sum_comp e.symm (fun j => pullHQ l (sch.map (σ j)) n i y)`. Conclude with `h2 x`.
-/
theorem UpperTheory.Gal.G3.pEtTr :
    EtTr := by
  intro l _ B hl n i Z Y p q s _ _ W r c hc J _ σ hσ hsp x
  obtain ⟨hsc, hiso⟩ := hsp
  have hT := UpperTheory.Gal.TranscendenceTraces.adic.2.2.2.2.2.2.2.2.2
  let e := Fintype.equivFin J
  have hiso' : IsIso (Sigma.desc fun k : Fin (Fintype.card J) =>
      pullback.lift (σ (e.symm k)) (𝟙 W) (by rw [hsc, Category.id_comp])) := by
    have hEq : (Sigma.desc fun k : Fin (Fintype.card J) =>
        pullback.lift (σ (e.symm k)) (𝟙 W) (by rw [hsc, Category.id_comp])) =
        (Sigma.reindex e.symm (fun _ : J => W)).hom ≫
          Sigma.desc fun j => pullback.lift (σ j) (𝟙 W) (by rw [hsc, Category.id_comp]) := by
      refine Sigma.hom_ext _ _ (fun k => ?_)
      rw [Sigma.ι_desc]
      have h4 := Sigma.ι_reindex_hom_assoc (ε := e.symm) (f := fun _ : J => W) (b := k)
        (h := Sigma.desc fun j => pullback.lift (σ j) (𝟙 W) (by rw [hsc, Category.id_comp]))
      rw [Sigma.ι_desc] at h4
      exact h4.symm
    rw [hEq]
    infer_instance
  have hlZ : IsUnit ((l : Γ(Z, ⊤))) := by
    simpa using hl.map (Scheme.Hom.appTop p).hom
  have h1 := hT l n i s hlZ W c (Fintype.card J) (fun k => σ (e.symm k)) (fun k => hsc _) hiso'
  have h2 : ∀ y : HQ l (sch.obj Y) n i, pullHQ l (sch.map c) n i
      (TranscendenceTraces.trHQ l s (TranscendenceTraces.Wt.const Y 1) n i y) = ∑ j, pullHQ l (sch.map (σ j)) n i y := by
    intro y
    have h3 := LinearMap.congr_fun h1 y
    rw [LinearMap.comp_apply, LinearMap.sum_apply] at h3
    rw [h3]
    exact Equiv.sum_comp e.symm (fun j => pullHQ l (sch.map (σ j)) n i y)
  exact h2 x
