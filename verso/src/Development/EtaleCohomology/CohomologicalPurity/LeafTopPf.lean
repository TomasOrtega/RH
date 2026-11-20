import Development.EtaleCohomology.CohomologicalPurity.LeafFlqPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Cl.Flq

/- English proof (translation)
Use `show (F.obj.map f.op).hom ((F.obj.map g.op).hom a) = (F.obj.map (f ≫ g).op).hom a`. Rewrite using `[op_comp, Functor.map_comp]`. Both sides reduce to the same expression.
-/
theorem etale_sheaf_sections_restrict_restrict_eq_restrict_comp {R : Type} [CommRing R] {F : Shv R} {Y Z W : Scheme.{0}} (f : Y ⟶ Z) (g : Z ⟶ W) (a : Sec F W) :
    Sec.res f (Sec.res g a) = Sec.res (f ≫ g) a := by
  show (F.obj.map f.op).hom ((F.obj.map g.op).hom a) = (F.obj.map (f ≫ g).op).hom a
  rw [op_comp, Functor.map_comp]; rfl

/- English proof (translation)
Use `show (F.obj.map f.op).hom 0 = 0`. Conclude with `map_zero _`.
-/
theorem etale_sheaf_sections_restriction_of_zero_eq_zero {R : Type} [CommRing R] {F : Shv R} {Y Z : Scheme.{0}} (f : Y ⟶ Z) :
    Sec.res f (0 : Sec F Z) = 0 := by
  show (F.obj.map f.op).hom 0 = 0
  exact map_zero _

/- English proof (translation)
Use `show (φ.hom.app (op Y)).hom ((F.obj.map f.op).hom a) = (G.obj.map f.op).hom ((φ.hom.app (op Z)).hom a)`. Establish `h` using `φ.hom.naturality f.op`. Conclude with `congrArg (fun ψ => ψ.hom a) h`.
-/
theorem etale_sheaf_sections_map_restrict_comm {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {Y Z : Scheme.{0}} (f : Y ⟶ Z) (a : Sec F Z) :
    Sec.map φ (Sec.res f a) = Sec.res f (Sec.map φ a) := by
  show (φ.hom.app (op Y)).hom ((F.obj.map f.op).hom a) = (G.obj.map f.op).hom ((φ.hom.app (op Z)).hom a)
  have h := φ.hom.naturality f.op
  exact congrArg (fun ψ => ψ.hom a) h

/- English proof (translation)
Introduce `R _ K X U n c' hc'`. Take `⟨h1, h2⟩` from `(mem_Zc c').1 hc'`. Use `⟨Sec.res X.topIso.inv c', (mem_Zc _).2 ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Establish `: IsIso (⊤ : X.Opens).ι` using `by rw [← Scheme.topIso_hom]; infer_instance`. Establish `e : U.ι ≫ X.topIso.inv = inv ((⊤ : X.Opens).ι ∣_ U) ≫ ((⊤ : X.Opens).ι ⁻¹ᵁ U).ι`.

Rewrite using `[← cancel_mono X.topIso.hom, Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc, Scheme.topIso_hom, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]`. Rewrite using `[etale_sheaf_sections_restrict_restrict_eq_restrict_comp, e, ← etale_sheaf_sections_restrict_restrict_eq_restrict_comp, h1, etale_sheaf_sections_restriction_of_zero_eq_zero]`. Rewrite using `[etale_sheaf_sections_map_restrict_comm, h2, etale_sheaf_sections_restriction_of_zero_eq_zero]`. Introduce `V`. Rewrite using `[etale_sheaf_sections_restrict_restrict_eq_restrict_comp]`.

Use `congr 1`. Rewrite using `[← cancel_mono X.topIso.hom, Category.assoc, Iso.inv_hom_id, Category.comp_id, Scheme.topIso_hom, Scheme.homOfLE_ι]`.
-/
theorem LeafTop_of : LeafTop := by
  intro R _ K X U n c' hc'
  obtain ⟨h1, h2⟩ := (mem_Zc c').1 hc'
  refine ⟨Sec.res X.topIso.inv c', (mem_Zc _).2 ⟨?_, ?_⟩, ?_⟩
  · have : IsIso (⊤ : X.Opens).ι := by rw [← Scheme.topIso_hom]; infer_instance
    have e : U.ι ≫ X.topIso.inv = inv ((⊤ : X.Opens).ι ∣_ U) ≫ ((⊤ : X.Opens).ι ⁻¹ᵁ U).ι := by
      rw [← cancel_mono X.topIso.hom, Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
        Scheme.topIso_hom, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
    rw [etale_sheaf_sections_restrict_restrict_eq_restrict_comp, e, ← etale_sheaf_sections_restrict_restrict_eq_restrict_comp, h1, etale_sheaf_sections_restriction_of_zero_eq_zero]
  · rw [etale_sheaf_sections_map_restrict_comm, h2, etale_sheaf_sections_restriction_of_zero_eq_zero]
  · intro V
    rw [etale_sheaf_sections_restrict_restrict_eq_restrict_comp]
    congr 1
    rw [← cancel_mono X.topIso.hom, Category.assoc, Iso.inv_hom_id, Category.comp_id, Scheme.topIso_hom,
      Scheme.homOfLE_ι]

end LateralTheory.CohomologicalPurity.Cl.Flq
