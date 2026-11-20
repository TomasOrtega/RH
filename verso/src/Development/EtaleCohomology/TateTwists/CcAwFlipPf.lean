import Development.EtaleCohomology.TateTwists.CcCupFlipPf
import Development.EtaleCohomology.TateTwists.CupflipHomotopyPf
import Development.EtaleCohomology.TateTwists.EtaleFreeModuleCohomologyHomOfComponents
import Development.EtaleCohomology.TateTwists.EtaleCochainComplexBasicPropertiesOfComponents
import Development.EtaleCohomology.TateTwists.EtaleEvaluationMapConstructionOfComponents

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

/- English proof (translation)
Introduce `R _ E I n α β hab`. Use `Cochain.ext _ _ fun p q hpq => ?_` and prove the remaining obligations. Break down `le_or_gt p 0 with hp | hp` into its components or cases. Take `⟨N, rfl⟩ : ∃ N : ℕ, p = -(N : ℤ)` from `⟨p.natAbs, by omega⟩`. Establish `key : (chainsXIso R E N).inv ≫ α.v _ q hpq = (chainsXIso R E N).inv ≫ β.v _ q hpq`.

Use `(LateralTheory.Fin.EtaleFreeSheafUniversalProperty.intersectionNumber_baseChange R _ _).2.1 _ _ fun U x => ?_` and prove the remaining obligations. Conclude with `hab N q hpq U x`. Simplify using `using congrArg (fun f => (chainsXIso R E N).hom ≫ f) key`. Use `(LateralTheory.Fin.EtaleSimplicialChainsFreeDescription.intersectionNumber_baseChange R).1 E` as an intermediate fact. Establish `hz : IsZero (((chains R).obj E).X p)` using `CochainComplex.isZero_of_isStrictlyLE _ 0 p hp`.

Conclude with `hz.eq_of_src _ _`.
-/
theorem LateralTheory.EtaleFoundations.cupflip_ev_ext_pf : LateralTheory.EtaleFoundations.cupflip_ev_ext := by
  intro R _ E I n α β hab
  refine Cochain.ext _ _ fun p q hpq => ?_
  rcases le_or_gt p 0 with hp | hp
  · obtain ⟨N, rfl⟩ : ∃ N : ℕ, p = -(N : ℤ) := ⟨p.natAbs, by omega⟩
    have key : (chainsXIso R E N).inv ≫ α.v _ q hpq = (chainsXIso R E N).inv ≫ β.v _ q hpq := by
      refine (LateralTheory.Fin.EtaleFreeSheafUniversalProperty.intersectionNumber_baseChange R _ _).2.1 _ _ fun U x => ?_
      exact hab N q hpq U x
    simpa using congrArg (fun f => (chainsXIso R E N).hom ≫ f) key
  · have := (LateralTheory.Fin.EtaleSimplicialChainsFreeDescription.intersectionNumber_baseChange R).1 E
    have hz : IsZero (((chains R).obj E).X p) := CochainComplex.isZero_of_isStrictlyLE _ 0 p hp
    exact hz.eq_of_src _ _

namespace LateralTheory.EtaleFoundations

/- English proof (translation)
Establish `h3` using `(LateralTheory.Fin.EtaleFreeSheafUniversalProperty.intersectionNumber_baseChange R (E.obj (op (SimplexCategory.mk p))) (I.X s)).2.2.1 V U g x`. Unfold `ev`. Rewrite using `[show Sx.res g x = (E.obj (op (SimplexCategory.mk p))).map g.op x from rfl, ← h3]`. Use `congrArg (fun f => (ModuleCat.Hom.hom f) (freeGen R (E.obj (op (SimplexCategory.mk p))) U x)) (((chainsXIso R E p).inv ≫ α.v _ _ h).hom.naturality g.op)` as an intermediate fact. Simplify using `using this.symm`.
-/
theorem ev_res' {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E p U) :
    Sec.res g (ev α p s h U x) = ev α p s h V (x.res g) := by
  have h3 := (LateralTheory.Fin.EtaleFreeSheafUniversalProperty.intersectionNumber_baseChange R (E.obj (op (SimplexCategory.mk p))) (I.X s)).2.2.1 V U g x
  unfold ev
  rw [show Sx.res g x = (E.obj (op (SimplexCategory.mk p))).map g.op x from rfl, ← h3]
  have := congrArg (fun f => (ModuleCat.Hom.hom f) (freeGen R (E.obj (op (SimplexCategory.mk p))) U x))
    (((chainsXIso R E p).inv ≫ α.v _ _ h).hom.naturality g.op)
  simpa using this.symm

/- English proof (translation)
Unfold `Sx.along Sx.res`. Conclude with `(NatTrans.naturality_apply (E.map θ.op) g.op x).symm`.
-/
theorem along_res' {E : Spc} {p N : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E N U)
    (θ : SimplexCategory.mk p ⟶ SimplexCategory.mk N) : (x.along θ).res g = (x.res g).along θ := by
  unfold Sx.along Sx.res
  exact (NatTrans.naturality_apply (E.map θ.op) g.op x).symm

/- English proof (translation)
Introduce `h _ R _ I J K μ E n m k hk α β`. Take `⟨η, hη⟩` from `LateralTheory.Fin.EtaleCochainExistsOfNaturalEvaluation.intersectionNumber_baseChange R (E := E) (I := K) (n := k - 1) (fun N s _ U x => phi μ hk α β x s (h N)) (by`. Introduce `N s hs V U g x`. Simplify using `only [phi, Finsupp.sum, Sec.res, map_sum, map_zsmul]`. Use `Finset.sum_congr rfl fun z _ => ?_` and prove the remaining obligations.

Use `congr 1`. Unfold `phiT`. Use `split_ifs with hw`. Rewrite using `[map_zsmul]`. Use `μ.nat g _ _ _ (by omega : -(z.1 : ℤ) + n + (-(z.2.1 : ℤ) + m) = s) (ev α z.1 _ rfl U (x.along z.2.2.1)) (ev β z.2.1 _ rfl U (x.along z.2.2.2))` as an intermediate fact.

Simplify using `only [Sec.res] at this`. Establish `ea` using `ev_res' α _ _ rfl g (x.along z.2.2.1)`. Establish `eb` using `ev_res' β _ _ rfl g (x.along z.2.2.2)`. Rewrite `ea`, `eb` using `[along_res']`. Simplify using `only [Sec.res] at ea eb`.

Rewrite using `[this, ea, eb]`. Use the proof step `simp)`. Conclude with `⟨η, fun N s hs U x => hη N s hs U x⟩`.
-/
theorem cupflip_eta_mk_pf : cupflip_eta_mk := by
  intro h _ R _ I J K μ E n m k hk α β
  obtain ⟨η, hη⟩ := LateralTheory.Fin.EtaleCochainExistsOfNaturalEvaluation.intersectionNumber_baseChange R (E := E) (I := K) (n := k - 1)
    (fun N s _ U x => phi μ hk α β x s (h N)) (by
      intro N s hs V U g x
      simp only [phi, Finsupp.sum, Sec.res, map_sum, map_zsmul]
      refine Finset.sum_congr rfl fun z _ => ?_
      congr 1
      unfold phiT
      split_ifs with hw
      · rw [map_zsmul]
        have := μ.nat g _ _ _ (by omega : -(z.1 : ℤ) + n + (-(z.2.1 : ℤ) + m) = s)
          (ev α z.1 _ rfl U (x.along z.2.2.1)) (ev β z.2.1 _ rfl U (x.along z.2.2.2))
        simp only [Sec.res] at this
        have ea := ev_res' α _ _ rfl g (x.along z.2.2.1)
        have eb := ev_res' β _ _ rfl g (x.along z.2.2.2)
        rw [along_res'] at ea eb
        simp only [Sec.res] at ea eb
        rw [this, ea, eb]
      · simp)
  exact ⟨η, fun N s hs U x => hη N s hs U x⟩

end LateralTheory.EtaleFoundations

/- English proof (translation)
The claim follows from `LateralTheory.EtaleFoundations.cupflip_aw_flip_of hst (LateralTheory.EtaleFoundations.cupflip_homotopy_of LateralTheory.EtaleFoundations.cupflip_ev_ext_pf LateralTheory.EtaleFoundations.cupflip_eta_mk_pf hdl)`.
-/
theorem LateralTheory.EtaleFoundations.cc_aw_flip_of (hst : LateralTheory.EtaleFoundations.cupflip_steen) (hdl : LateralTheory.EtaleFoundations.cupflip_eta_delta) :
    LateralTheory.EtaleFoundations.cc_aw_flip :=
  LateralTheory.EtaleFoundations.cupflip_aw_flip_of hst (LateralTheory.EtaleFoundations.cupflip_homotopy_of LateralTheory.EtaleFoundations.cupflip_ev_ext_pf
    LateralTheory.EtaleFoundations.cupflip_eta_mk_pf hdl)
