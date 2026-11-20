import Mathlib

namespace GlobalTheory

/- English proof (translation)
Take `⟨n, f, g, -, -, hfg⟩` from `Module.Finite.exists_comp_eq_id_of_projective A M`. Establish `hg : g x = 0`. Use function extensionality and compare the values at `i`. Establish `hmem : g x i ∈ nilradical A`. Rewrite using `[nilradical_eq_sInf, Ideal.mem_sInf]`.

Introduce `(p : Ideal A) (hp : p.IsPrime)`. Establish `h` using `hx p ((Algebra.linearMap A p.ResidueField) ∘ₗ (LinearMap.proj i) ∘ₗ g)`. Simplify using `only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj, Function.eval, Algebra.linearMap_apply] at h`. Establish `h' : g x i ∈ RingHom.ker (algebraMap A p.ResidueField)` using `h`. Rewrite `h'` using `[Ideal.ker_algebraMap_residueField]`. Then use the resulting hypothesis.

Conclude with `(mem_nilradical.mp hmem).eq_zero`. Use `congrArg (fun y => f y) hg` as an intermediate fact. Simplify `this` using `[← LinearMap.comp_apply, hfg]`.
-/
theorem eq_zero_of_forall_residueField_functional (A M : Type) [CommRing A] [IsReduced A]
    [AddCommGroup M] [Module A M] [Module.Finite A M] [Module.Projective A M] (x : M)
    (hx : ∀ (p : Ideal A) [p.IsPrime] (l : M →ₗ[A] p.ResidueField), l x = 0) : x = 0 := by
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective A M
  have hg : g x = 0 := by
    funext i
    have hmem : g x i ∈ nilradical A := by
      rw [nilradical_eq_sInf, Ideal.mem_sInf]
      intro (p : Ideal A) (hp : p.IsPrime)
      have h := hx p ((Algebra.linearMap A p.ResidueField) ∘ₗ (LinearMap.proj i) ∘ₗ g)
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj,
        Function.eval, Algebra.linearMap_apply] at h
      have h' : g x i ∈ RingHom.ker (algebraMap A p.ResidueField) := h
      rwa [Ideal.ker_algebraMap_residueField] at h'
    exact (mem_nilradical.mp hmem).eq_zero
  have := congrArg (fun y => f y) hg
  simpa [← LinearMap.comp_apply, hfg] using this

end GlobalTheory
