import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory

/- English proof (translation)
Introduce `U S`. Prove the components needed by the constructor for the conclusion. Introduce `hS u`. Take `⟨𝒰, hle⟩` from `(Scheme.mem_grothendieckTopology_iff (P := @Etale)).1 hS`. Take `⟨i, v, hv⟩` from `((Scheme.presieve₀_mem_precoverage_iff _).1 𝒰.mem₀).1 u`.

Conclude with `⟨𝒰.X i, 𝒰.f i, v, 𝒰.map_prop i, hv, hle _ _ (Presieve.ofArrows.mk i)⟩`. Introduce `h choose V j v hj hv hS using h`. Use `(Scheme.mem_grothendieckTopology_iff (P := @Etale)).2 ⟨Scheme.Cover.mkOfCovers U V j (fun u => ⟨u, v u, hv u⟩) hj, ?_⟩` and prove the remaining obligations. Introduce `W f hf`. Take `⟨u⟩` from `hf`.

Conclude with `hS u`.
-/
theorem etale_mem_iff_points : ∀ (U : Scheme.{0}) (S : Sieve U), S ∈ Scheme.etaleTopology.{0} U ↔
    ∀ u : U, ∃ (V : Scheme.{0}) (j : V ⟶ U) (v : V), Etale j ∧ j v = u ∧ S.arrows j := by
  intro U S
  constructor
  · intro hS u
    obtain ⟨𝒰, hle⟩ := (Scheme.mem_grothendieckTopology_iff (P := @Etale)).1 hS
    obtain ⟨i, v, hv⟩ := ((Scheme.presieve₀_mem_precoverage_iff _).1 𝒰.mem₀).1 u
    exact ⟨𝒰.X i, 𝒰.f i, v, 𝒰.map_prop i, hv, hle _ _ (Presieve.ofArrows.mk i)⟩
  · intro h
    choose V j v hj hv hS using h
    refine (Scheme.mem_grothendieckTopology_iff (P := @Etale)).2
      ⟨Scheme.Cover.mkOfCovers U V j (fun u => ⟨u, v u, hv u⟩) hj, ?_⟩
    intro W f hf
    obtain ⟨u⟩ := hf
    exact hS u

end GlobalTheory
