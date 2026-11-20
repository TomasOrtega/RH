import Development.AbelianVarietyTheory.Definitions.Divisors.MaxWeightGL1EqOne
open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKLoc

namespace GlobalTheory.LKLoc

/- English proof (translation)
Introduce `x hx`. Establish `hx' : ((x : PadicAlgCl p)) ∈ Obar p` using `hx`. Use `show ((frobR p K r x : Kn p K r) : PadicAlgCl p) ∈ Obar p`. Establish `h : ((frobR p K r x : Kn p K r) : PadicAlgCl p) = frobK p K (x : PadicAlgCl p)` using `rfl`. Rewrite using `[h, mem_Obar_iff, norm_map_GK]`.

Conclude with `mem_Obar_iff.1 hx'`.
-/
theorem frobR_mem_intR (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ) :
    ∀ x ∈ intR p K r, frobR p K r x ∈ intR p K r := by
  intro x hx
  have hx' : ((x : PadicAlgCl p)) ∈ Obar p := hx
  show ((frobR p K r x : Kn p K r) : PadicAlgCl p) ∈ Obar p
  have h : ((frobR p K r x : Kn p K r) : PadicAlgCl p) = frobK p K (x : PadicAlgCl p) := rfl
  rw [h, mem_Obar_iff, norm_map_GK]
  exact mem_Obar_iff.1 hx'

end GlobalTheory.LKLoc
