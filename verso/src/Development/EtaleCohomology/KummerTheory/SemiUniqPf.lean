import Development.EtaleCohomology.KummerTheory.BockCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory.SemiUniqPf

/- English proof (translation)
Take `⟨a, rfl⟩` from `x.mk_surjective`. Rewrite using `[cpost_mk, cpost_mk, ← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]`. Use `⟨a.1.comp (Cochain.ofHomotopy ho) (by omega), ?_⟩` and prove the remaining obligations. Rewrite using `[δ_comp _ _ _ (n + 1) 0 n (by omega) (by omega) (by omega), δ_ofHomotopy, Cocycle.δ_eq_zero]`. Use extensionality with `p q hpq`.

Simplify using `[zcomp, Cochain.comp_sub]`.
-/
theorem cpush_homotopy {R : Type} [CommRing R] (K : Cx R) {I J : Cx R} {f g : I ⟶ J} (ho : Homotopy f g) (n : ℤ)
    (x : CohomologyClass K I n) : cpush K f n x = cpush K g n x := by
  obtain ⟨a, rfl⟩ := x.mk_surjective
  rw [cpost_mk, cpost_mk, ← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨a.1.comp (Cochain.ofHomotopy ho) (by omega), ?_⟩
  rw [δ_comp _ _ _ (n + 1) 0 n (by omega) (by omega) (by omega), δ_ofHomotopy, Cocycle.δ_eq_zero]
  ext p q hpq
  simp [zcomp, Cochain.comp_sub]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem secMap_comp {R : Type} [CommRing R] {F G M : Shv R} (f : F ⟶ G) (g : G ⟶ M) {U : Scheme.{0}} (a : Sec F U) :
    Sec.map (f ≫ g) a = Sec.map g (Sec.map f a) := rfl

/- English proof (translation)
Set `e : ∀ (U : Scheme.{0}) (s : ℤ), Sec (I.X s) U ≃+ Sec (T.X s) U` to `fun U s => AddEquiv.ofBijective (σ.app U s) (hσ U s)`. Establish `he : ∀ U s a, e U s a = σ.app U s a` using `fun _ _ _ => rfl`. Establish `hu : ∀ s, ∃ φ : T.X s ⟶ J.X s, ∀ (U : Scheme.{0}) (b : Sec (T.X s) U), Sec.map φ b = κ.app U s ((e U s).symm b)`. Introduce `s`. Use `hZ _ _ (fun U => (κ.app U s).comp (e U s).symm.toAddMonoidHom) ?_` and prove the remaining obligations.

Introduce `V U g b`. Take `⟨a, rfl⟩` from `(e U s).surjective b`. Simplify using `only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, AddEquiv.symm_apply_apply]`. Rewrite using `[κ.nat]`. Use `congr 1`.

Apply `(e V s).injective` to reduce the goal to its premises. Rewrite using `[AddEquiv.apply_symm_apply, he, he, σ.nat]`. Use `choose φ hφ using hu`. Use `⟨{ f := φ, comm' := ?_ }, ?_⟩` and prove the remaining obligations. Introduce `s t _`.

Use `(hME ℤ (φ s ≫ J.d s t)).2.2.2 (T.d s t ≫ φ t) ?_` and prove the remaining obligations. Introduce `U b`. Take `⟨a, rfl⟩` from `(e U s).surjective b`. Rewrite using `[secMap_comp, secMap_comp, hφ, AddEquiv.symm_apply_apply, κ.comm, he, σ.comm, hφ, ← he, AddEquiv.symm_apply_apply]`. Introduce `U s a show κ.app U s a = Sec.map (φ s) (σ.app U s a)`.

Rewrite using `[hφ, ← he, AddEquiv.symm_apply_apply]`.
-/
theorem factor (hZ : LateralTheory.KummerTheory.BockCut.ZHom) (hME : LateralTheory.EtaleFoundations.EtaleSheafMonoEpiSectionCriteria) {S : Type} [CommRing S]
    {I : Cx S} {T J : Cx ℤ} (σ : SemiMap I T) (hσ : ∀ (U : Scheme.{0}) (s : ℤ), Function.Bijective (σ.app U s))
    (κ : SemiMap I J) : ∃ u : T ⟶ J, ∀ (U : Scheme.{0}) (s : ℤ) (a : Sec (I.X s) U),
      κ.app U s a = Sec.map (u.f s) (σ.app U s a) := by
  let e : ∀ (U : Scheme.{0}) (s : ℤ), Sec (I.X s) U ≃+ Sec (T.X s) U :=
    fun U s => AddEquiv.ofBijective (σ.app U s) (hσ U s)
  have he : ∀ U s a, e U s a = σ.app U s a := fun _ _ _ => rfl
  have hu : ∀ s, ∃ φ : T.X s ⟶ J.X s, ∀ (U : Scheme.{0}) (b : Sec (T.X s) U),
      Sec.map φ b = κ.app U s ((e U s).symm b) := by
    intro s
    refine hZ _ _ (fun U => (κ.app U s).comp (e U s).symm.toAddMonoidHom) ?_
    intro V U g b
    obtain ⟨a, rfl⟩ := (e U s).surjective b
    simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, AddEquiv.symm_apply_apply]
    rw [κ.nat]
    congr 1
    apply (e V s).injective
    rw [AddEquiv.apply_symm_apply, he, he, σ.nat]
  choose φ hφ using hu
  refine ⟨{ f := φ, comm' := ?_ }, ?_⟩
  · intro s t _
    refine (hME ℤ (φ s ≫ J.d s t)).2.2.2 (T.d s t ≫ φ t) ?_
    intro U b
    obtain ⟨a, rfl⟩ := (e U s).surjective b
    rw [secMap_comp, secMap_comp, hφ, AddEquiv.symm_apply_apply, κ.comm, he, σ.comm, hφ, ← he,
      AddEquiv.symm_apply_apply]
  · intro U s a
    show κ.app U s a = Sec.map (φ s) (σ.app U s a)
    rw [hφ, ← he, AddEquiv.symm_apply_apply]

/- English proof (translation)
Introduce `S _ F G ρ ρ' hρ E n x`. Take `⟨T, σ, ε, hε, hσ, hσε⟩` from `hRR ℤ S (Int.castRingHom S) F`. Take `⟨u, hu⟩` from `factor hZ hME σ hσ ρ`. Take `⟨u', hu'⟩` from `factor hZ hME σ hσ ρ'`. Take `⟨hK, -, hGE, -⟩` from `hRB ℤ G`.

Establish `heq : ε ≫ u = ε ≫ u'`. Apply `HomologicalComplex.from_single_hom_ext` to reduce the goal to its premises. Use `(hME ℤ _).2.2.2 _ ?_` and prove the remaining obligations. Introduce `U b`. Set `ι` to `HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ((restr (Int.castRingHom S)).obj F)`.

Establish `hb : b = Sec.map (sglι _) (Sec.map ι.hom b)`. Rewrite using `[← secMap_comp]`. Conclude with `(congrArg (fun f => Sec.map f b) ι.hom_inv_id).symm`. Establish `h1` using `hσε U (Sec.map ι.hom b)`. Simplify using `only at h1`.

Rewrite using `[hb]`. Express the relevant statement in the definitionally equal form `Sec.map (u.f 0) (Sec.map (ε.f 0) (Sec.map (sglι _) (Sec.map ι.hom b))) = Sec.map (u'.f 0) (Sec.map (ε.f 0) (Sec.map (sglι _) (Sec.map ι.hom b)))`. Rewrite using `[h1, ← hu, ← hu']`. Conclude with `hρ U _`. Take `⟨ho⟩` from `(hEH ℤ _ T (res ℤ G) ε).2 u u' heq`.

Rewrite using `[(hOC S ℤ σ ρ u hu).1 E n x, (hOC S ℤ σ ρ' u' hu').1 E n x]`. Conclude with `cpush_homotopy _ ho n _`.
-/
theorem SemiUniq_of (hRR : LateralTheory.KummerTheory.BockCut.RestrRes) (hZ : LateralTheory.KummerTheory.BockCut.ZHom)
    (hOC : LateralTheory.EtaleFoundations.EtaleCochainSemilinearMapCompCompatible) (hEH : LateralTheory.EtaleFoundations.EtaleKInjectiveHomExtendsAlongQuasiIso)
    (hRB : LateralTheory.EtaleFoundations.EtaleInjectiveResolutionBasicProperties) (hME : LateralTheory.EtaleFoundations.EtaleSheafMonoEpiSectionCriteria) :
    LateralTheory.KummerTheory.BockCut.SemiUniq := by
  intro S _ F G ρ ρ' hρ E n x
  obtain ⟨T, σ, ε, hε, hσ, hσε⟩ := hRR ℤ S (Int.castRingHom S) F
  obtain ⟨u, hu⟩ := factor hZ hME σ hσ ρ
  obtain ⟨u', hu'⟩ := factor hZ hME σ hσ ρ'
  obtain ⟨hK, -, hGE, -⟩ := hRB ℤ G
  have heq : ε ≫ u = ε ≫ u' := by
    apply HomologicalComplex.from_single_hom_ext
    refine (hME ℤ _).2.2.2 _ ?_
    intro U b
    let ι := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ((restr (Int.castRingHom S)).obj F)
    have hb : b = Sec.map (sglι _) (Sec.map ι.hom b) := by
      rw [← secMap_comp]; exact (congrArg (fun f => Sec.map f b) ι.hom_inv_id).symm
    have h1 := hσε U (Sec.map ι.hom b)
    dsimp only at h1
    rw [hb]
    change Sec.map (u.f 0) (Sec.map (ε.f 0) (Sec.map (sglι _) (Sec.map ι.hom b))) =
      Sec.map (u'.f 0) (Sec.map (ε.f 0) (Sec.map (sglι _) (Sec.map ι.hom b)))
    rw [h1, ← hu, ← hu']
    exact hρ U _
  obtain ⟨ho⟩ := (hEH ℤ _ T (res ℤ G) ε).2 u u' heq
  rw [(hOC S ℤ σ ρ u hu).1 E n x, (hOC S ℤ σ ρ' u' hu').1 E n x]
  exact cpush_homotopy _ ho n _

end LateralTheory.KummerTheory.SemiUniqPf
