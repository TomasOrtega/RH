import Development.EtaleCohomology.KummerTheory.BockCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory.SemiUniqPf

/- English proof (translation)
Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules.
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
Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify by unfolding definitions. Rewrite the conclusion using the stated equalities.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
