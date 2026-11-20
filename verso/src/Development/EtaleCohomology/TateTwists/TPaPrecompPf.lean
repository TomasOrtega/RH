import Development.EtaleCohomology.TateTwists.TPairAssocPf

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

/- English proof (translation)
Use `congrArg (fun f => (ModuleCat.Hom.hom f) x) (φ.hom.naturality g.op)` as an intermediate fact. Simplify using `using this.symm`.
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
Introduce `R _ I I' J K u μ`. Use `⟨⟨fun U s t w h => (μ.mul U s t w h).comp ((u.f s).hom.app (op U)).hom, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `V U g s t w h a b`. Simplify using `only [LinearMap.comp_apply]`. Conclude with `(μ.nat g s t w h _ b).trans (by rw [pa_sec_res_map])`.

Introduce `U s t w h a b`. Simplify using `only [LinearMap.comp_apply]`. Rewrite using `[μ.leibniz]`. Use `congr 2`. Rewrite using `[← pa_sec_map_comp, u.comm]`.

Both sides reduce to the same expression. Introduce `U s t w h a b`. Both sides reduce to the same expression.
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
