import Development.EtaleCohomology.TateTwists.TPairAssocPf

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

/- English proof (translation)
Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem pa_sec_res_map {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U)
    (x : Sec F U) : Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  have := congrArg (fun f => (ModuleCat.Hom.hom f) x) (φ.hom.naturality g.op)
  simpa using this.symm

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pa_sec_map_comp {R : Type} [CommRing R] {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}}
    (x : Sec F U) : Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Fix the arbitrary inputs or assume the hypotheses. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem t_pa_precomp_of : t_pa_precomp := by
  intro R _ I I' J K u μ
  refine ⟨⟨fun U s t w h => (μ.mul U s t w h).comp ((u.f s).hom.app (op U)).hom, ?_, ?_⟩, ?_⟩
  · intro V U g s t w h a b
    simp only [LinearMap.comp_apply]
    exact (μ.nat g s t w h _ b).trans (by rw [pa_sec_res_map])
  · intro U s t w h a b
    simp only [LinearMap.comp_apply]
    rw [μ.leibniz]
    congr 2
    rw [← pa_sec_map_comp, u.comm]; rfl
  · intro U s t w h a b
    rfl

end LateralTheory.EtaleFoundations
