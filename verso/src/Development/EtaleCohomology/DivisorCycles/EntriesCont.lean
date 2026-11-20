import Development.EtaleCohomology.DivisorCycles.CycleCount

open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb.DegAll₂
open LateralTheory.DivDb

/- English proof (translation)
The claim follows from `continuous_pi fun p => (hφ.matrix_elem p.1 p.2)`.
-/
theorem entries_cont {Γ K : Type} [TopologicalSpace Γ] [TopologicalSpace K] {N : ℕ}
    {φ : Γ → Mat K N} (hφ : Continuous φ) :
    Continuous (fun g => fun p : Fin N × Fin N => φ g p.1 p.2) :=
  continuous_pi fun p => (hφ.matrix_elem p.1 p.2)

/- English proof (translation)
Use `((MvPolynomial.continuous_eval f).comp (entries_cont hφ)).congr ?_` and prove the remaining obligations. Introduce `g`. Rewrite using `[MvPolynomial.aeval_eq_eval₂Hom, Algebra.algebraMap_self]`. Both sides reduce to the same expression.
-/
theorem poly_cont {Γ K : Type} [TopologicalSpace Γ] [Field K] [TopologicalSpace K]
    [IsTopologicalRing K] {N : ℕ} {φ : Γ → Mat K N} (hφ : Continuous φ) (f : MP K N) :
    Continuous (fun g => MvPolynomial.aeval (fun p : Fin N × Fin N => φ g p.1 p.2) f) := by
  refine ((MvPolynomial.continuous_eval f).comp (entries_cont hφ)).congr ?_
  intro g
  rw [MvPolynomial.aeval_eq_eval₂Hom, Algebra.algebraMap_self]
  rfl

end LateralTheory.DivDb.DegAll₂

namespace LateralTheory.DivDb

/- English proof (translation)
Introduce `Γ K _ _ _ _ _ _ N n ρ hρ S hS hSd g`. Take `⟨𝓕, h𝓕⟩` from `hP K N n`. Rewrite using `[h𝓕 K]`. Introduce `f hf`. Establish `key` using `Continuous.ext_on hS (DegAll₂.poly_cont hρ f) continuous_const (fun s hs => ((h𝓕 K _).1 (hSd s hs)) f hf)`.

Conclude with `congrFun key g`.
-/
theorem DegAll_of (hP : DegPoly) : DegAll := by
  intro Γ K _ _ _ _ _ _ N n ρ hρ S hS hSd g
  obtain ⟨𝓕, h𝓕⟩ := hP K N n
  rw [h𝓕 K]
  intro f hf
  have key := Continuous.ext_on hS (DegAll₂.poly_cont hρ f) continuous_const
    (fun s hs => ((h𝓕 K _).1 (hSd s hs)) f hf)
  exact congrFun key g

end LateralTheory.DivDb
