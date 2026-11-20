import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RecT
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleSecondFactorOfIrreducibleProductStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSatakeGLOfHasSatakeParametersPrincipalSeriesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGenericOfIsLocComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsSpehProductStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

namespace GlobalTheory.FormDict.RecTLaws

section Core

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {rc : IrrGL (w.adicCompletion E) → WD h}

/- English proof (translation)
Take `⟨a, ha, ε, -, L⟩` from `H`. Introduce `c`. Proceed by induction on `c with`. Consider the case `zero`. Introduce `n d hd σ σ' e`.

Take `rfl : n = 0` from `by simpa using hd.symm`. Take `⟨e⟩` from `e`. Take `⟨φ⟩` from `GlobalTheory.LocGL.SupportRing.nonempty_equiv_unit (k := w.adicCompletion E) (stdBlocks d hd) fun i => (σ i).ρ`. Establish `h1` using `L.det 0 1 isSmoothChar_one`. Simplify using `only [List.range_zero, List.map_nil] at h1`.

Rewrite using `[List.ofFn_zero]`. Use `((L.eq_iff (ParLaws.toRep σ') (IrrRep.det (Fin 0) 1 isSmoothChar_one)).2 ⟨e.trans φ⟩).trans ?_` and prove the remaining obligations. Conclude with `h1`. Consider the case `succ s ih`. Introduce `n d hd σ σ' e`.

Take `rfl : n = d 0 + ∑ i : Fin s, d i.succ` from `hd.symm.trans (Fin.sum_univ_succ d)`. Take `⟨e⟩` from `e`. Take `⟨E₁⟩` from `MultiIrr.nonempty_prod₂_equiv_multiProd_succ (k := w.adicCompletion E) d hd fun i => (σ i).ρ`. Establish `hs : IsSmooth (multiProd (stdBlocks (fun i : Fin s => d i.succ) rfl) fun i : Fin s => (σ i.succ).ρ)` using `isSmooth_parInd _ _`. Establish `hi` using `GlobalTheory.T.isIrreducible_second_factor_of_irreducible_product _ _ _ _ _ _ (σ 0).ρ _ σ'.ρ (σ 0).smooth (σ 0).irred hs σ'.irred ⟨e.trans E₁.symm⟩`.

Set `σ'' : SmIrr (GL (Fin (∑ i : Fin s, d i.succ)) (w.adicCompletion E))` to `⟨_, _, hs, hi⟩`. Establish `h1` using `L.prod (d 0) _ (ParLaws.toRep (σ 0)) (ParLaws.toRep σ'') (ParLaws.toRep σ') ⟨e.trans E₁.symm⟩`. Establish `h2` using `ih (d := fun i : Fin s => d i.succ) rfl (fun i => σ i.succ) σ'' ⟨.refl _⟩`. Rewrite using `[List.ofFn_succ]`. Conclude with `h1.trans (congrArg _ h2)`.
-/
theorem locProd_eq (H : IsRec h rc) : ∀ {c n : ℕ} {d : Fin c → ℕ} (hd : ∑ i, d i = n)
    (σ : ∀ i, SmIrr (GL (Fin (d i)) (w.adicCompletion E))) (σ' : SmIrr (GL (Fin n) (w.adicCompletion E))),
    Nonempty (σ'.ρ.Equiv (GlobalTheory.UnitaryBC.locProd hd w σ)) →
      rc (cls (ParLaws.toRep σ')) = sumList (List.ofFn fun i => rc (cls (ParLaws.toRep (σ i)))) := by
  obtain ⟨a, ha, ε, -, L⟩ := H
  intro c
  induction c with
  | zero =>
    intro n d hd σ σ' e
    obtain rfl : n = 0 := by simpa using hd.symm
    obtain ⟨e⟩ := e
    obtain ⟨φ⟩ := GlobalTheory.LocGL.SupportRing.nonempty_equiv_unit (k := w.adicCompletion E) (stdBlocks d hd) fun i => (σ i).ρ
    have h1 := L.det 0 1 isSmoothChar_one
    simp only [List.range_zero, List.map_nil] at h1
    rw [List.ofFn_zero]
    refine ((L.eq_iff (ParLaws.toRep σ') (IrrRep.det (Fin 0) 1 isSmoothChar_one)).2 ⟨e.trans φ⟩).trans ?_
    exact h1
  | succ s ih =>
    intro n d hd σ σ' e
    obtain rfl : n = d 0 + ∑ i : Fin s, d i.succ := hd.symm.trans (Fin.sum_univ_succ d)
    obtain ⟨e⟩ := e
    obtain ⟨E₁⟩ := MultiIrr.nonempty_prod₂_equiv_multiProd_succ (k := w.adicCompletion E) d hd fun i => (σ i).ρ
    have hs : IsSmooth (multiProd (stdBlocks (fun i : Fin s => d i.succ) rfl) fun i : Fin s => (σ i.succ).ρ) :=
      isSmooth_parInd _ _
    have hi := GlobalTheory.T.isIrreducible_second_factor_of_irreducible_product _ _ _ _ _ _ (σ 0).ρ _ σ'.ρ (σ 0).smooth (σ 0).irred hs σ'.irred ⟨e.trans E₁.symm⟩
    let σ'' : SmIrr (GL (Fin (∑ i : Fin s, d i.succ)) (w.adicCompletion E)) := ⟨_, _, hs, hi⟩
    have h1 := L.prod (d 0) _ (ParLaws.toRep (σ 0)) (ParLaws.toRep σ'') (ParLaws.toRep σ') ⟨e.trans E₁.symm⟩
    have h2 := ih (d := fun i : Fin s => d i.succ) rfl (fun i => σ i.succ) σ'' ⟨.refl _⟩
    rw [List.ofFn_succ]
    exact h1.trans (congrArg _ h2)

/- English proof (translation)
Establish `hsph : IsSpherical (ParLaws.toRep σ).ρ`. Use `hS.1` as an intermediate fact. Unfold `IsSpherical IsSphericalFor`. Rewrite using `[GlobalTheory.SmGL.SphCompletion.KO_completion w n]`. Conclude with `this`.

Establish `hu : (rc (cls (ParLaws.toRep σ))).unr` using `(ParLaws.unr_iff H _).2 hsph`. Take `⟨α, hα⟩` from `ParLaws.exists_hasSatake_of_unr H hu`. Establish `e : S = Finset.univ.val.map α` using `hS.unique (GlobalTheory.T.hasSatakeGL_of_hasSatakeParameters_principalSeries E w n _ σ.ρ α hα)`. Use `⟨hu, ?_⟩` and prove the remaining obligations. Rewrite using `[ParLaws.rec_eq_diag H hα, WD.frobEig_diag, e, Multiset.map_map]`.

Both sides reduce to the same expression.
-/
theorem hasSatGL_rec (H : IsRec h rc) {n : ℕ} (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (S : Multiset ℂˣ)
    (hS : GlobalTheory.LFun.HasSatGL w σ.ρ S) :
    (rc (cls (ParLaws.toRep σ))).unr ∧
      (rc (cls (ParLaws.toRep σ))).frobEig = S.map fun z => ((z⁻¹ : ℂˣ) : ℂ) := by
  have hsph : IsSpherical (ParLaws.toRep σ).ρ := by
    have := hS.1
    unfold IsSpherical IsSphericalFor
    rw [GlobalTheory.SmGL.SphCompletion.KO_completion w n]
    exact this
  have hu : (rc (cls (ParLaws.toRep σ))).unr := (ParLaws.unr_iff H _).2 hsph
  obtain ⟨α, hα⟩ := ParLaws.exists_hasSatake_of_unr H hu
  have e : S = Finset.univ.val.map α := hS.unique (GlobalTheory.T.hasSatakeGL_of_hasSatakeParameters_principalSeries E w n _ σ.ρ α hα)
  refine ⟨hu, ?_⟩
  rw [ParLaws.rec_eq_diag H hα, WD.frobEig_diag, e, Multiset.map_map]
  rfl

end Core

section Record

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}
  (T : GlobalTheory.RowTie.WDTie N A) (hL : GlobalTheory.Published.LocalLanglandsGL)

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil => exact T.zero w`. Consider the case `cons x L ih`. Express the relevant statement in the definitionally equal form `T.e w (A.lpSum x (lpSumList L)) = (T.e w x).lpSum (sumList (L.map (T.e w)))`. Rewrite using `[T.sum, ih]`.
-/
theorem e_lpSumList (w : PlE H) (L : List (A.LP w)) : T.e w (lpSumList L) = sumList (L.map (T.e w)) := by
  induction L with
  | nil => exact T.zero w
  | cons x L ih =>
    change T.e w (A.lpSum x (lpSumList L)) = (T.e w x).lpSum (sumList (L.map (T.e w)))
    rw [T.sum, ih]

/- English proof (translation)
The claim follows from `(T.e w).apply_symm_apply _`.
-/
theorem e_recT (w : PlE H) {n : ℕ} (σ : LocIrr w n) :
    T.e w (recT T hL w n σ) = ParLaws.locRec hL (N.plOm.2 w) (cls (ParLaws.toRep σ)) :=
  (T.e w).apply_symm_apply _

/- English proof (translation)
Introduce `w c n d hd σ σ' e`. Apply `(T.e w).injective` to reduce the goal to its premises. Rewrite using `[e_recT, e_lpSumList, locProd_eq (ParLaws.isRec_locRec hL (N.plOm.2 w)) hd σ σ' e, List.map_ofFn]`. Use `congr 2`. Use function extensionality and compare the values at `i`.

Conclude with `(e_recT T hL w (σ i)).symm`.
-/
theorem recProd_recT : RecProd (recT T hL) := by
  intro w c n d hd σ σ' e
  apply (T.e w).injective
  rw [e_recT, e_lpSumList, locProd_eq (ParLaws.isRec_locRec hL (N.plOm.2 w)) hd σ σ' e, List.map_ofFn]
  congr 2
  funext i
  exact (e_recT T hL w (σ i)).symm

/- English proof (translation)
Introduce `w n σ S hS`. Take `⟨h1, h2⟩` from `hasSatGL_rec (ParLaws.isRec_locRec hL (N.plOm.2 w)) σ S hS`. Establish `hu : A.unr (recT T hL w n σ)` using `(T.unr w _).2 (by rw [e_recT]; exact h1)`. Conclude with `⟨hu, (T.frobEig w _ hu).trans (by rw [e_recT]; exact h2)⟩`.
-/
theorem recSatake_recT : RecSatake (recT T hL) := by
  intro w n σ S hS
  obtain ⟨h1, h2⟩ := hasSatGL_rec (ParLaws.isRec_locRec hL (N.plOm.2 w)) σ S hS
  have hu : A.unr (recT T hL w n σ) := (T.unr w _).2 (by rw [e_recT]; exact h1)
  exact ⟨hu, (T.frobEig w _ hu).trans (by rw [e_recT]; exact h2)⟩

/- English proof (translation)
Introduce `w a d n hd P σ σ' hP hu hq`. Establish `hg : IsGeneric σ.ρ` using `GlobalTheory.CuspRep.Generic.isGeneric_of_isLocComp H.E a P w σ hP`. Apply `(T.e w).injective` to reduce the goal to its premises. Rewrite using `[e_recT, e_lpSumList, GlobalTheory.T.local_langlands_speh_product _ _ _ w _ _ (ParLaws.isRec_locRec hL (N.plOm.2 w)) hTZ hSC a d n hd σ σ' hu hg hq, List.map_map]`. Use `congr 1`.

Use `List.map_congr_left fun k _ => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply, T.tw, e_recT]`.
-/
theorem recSpeh_recT (hTZ : GlobalTheory.Published.GenericUnitaryDualGL) (hSC : GlobalTheory.Published.StandardCosocleGL) :
    RecSpeh (recT T hL) := by
  intro w a d n hd P σ σ' hP hu hq
  have hg : IsGeneric σ.ρ := GlobalTheory.CuspRep.Generic.isGeneric_of_isLocComp H.E a P w σ hP
  apply (T.e w).injective
  rw [e_recT, e_lpSumList, GlobalTheory.T.local_langlands_speh_product _ _ _ w _ _ (ParLaws.isRec_locRec hL (N.plOm.2 w)) hTZ hSC a d n hd σ σ'
    hu hg hq, List.map_map]
  congr 1
  refine List.map_congr_left fun k _ => ?_
  simp only [Function.comp_apply, T.tw, e_recT]

end Record

/- English proof (translation)
Introduce `hTZ hSC hL _ _ _ _ _ T` and use `⟨recProd_recT T hL, recSpeh_recT T hL hTZ hSC, recSatake_recT T hL⟩`.
-/
theorem recLaws_recT : GlobalTheory.Published.GenericUnitaryDualGL → GlobalTheory.Published.StandardCosocleGL →
    ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)
      (A : NAut N) (T : GlobalTheory.RowTie.WDTie N A), RecProd (recT T hL) ∧ RecSpeh (recT T hL) ∧ RecSatake (recT T hL) :=
  fun hTZ hSC hL _ _ _ _ _ T => ⟨recProd_recT T hL, recSpeh_recT T hL hTZ hSC, recSatake_recT T hL⟩

end GlobalTheory.FormDict.RecTLaws
