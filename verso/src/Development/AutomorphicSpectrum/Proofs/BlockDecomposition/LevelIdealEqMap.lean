import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatC

/- English proof (translation)
Establish `key : IB (fk l k) (xi0 l) = (I (fk l k) (xi0 l) l M).map (ι (fk l k) (xi0 l) l M)`. Apply `le_antisymm` to reduce the goal to its premises. Use `Ideal.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨⟩`. Establish `hm : ofW (fk l k) (xi0 l) l M (xi0 l) ∈ I (fk l k) (xi0 l) l M` using `by show ι (fk l k) (xi0 l) l M (ofW (fk l k) (xi0 l) l M (xi0 l)) ∈ IB (fk l k) (xi0 l)`.

Rewrite using `[ι_ofW]`. Conclude with `Ideal.subset_span rfl`. Use `Ideal.mem_map_of_mem (ι (fk l k) (xi0 l) l M) hm` as an intermediate fact. Rewrite `this` using `[ι_ofW]`. Then use the resulting hypothesis. Conclude with `Ideal.map_comap_le`.

Conclude with `key`.
-/
theorem lev_IB_eq_map {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ}
    (h : LevHyp l K M) (k : ℕ) : (lev h k).IB = (lev h k).I.map (lev h k).ι := by
  have key : IB (fk l k) (xi0 l) = (I (fk l k) (xi0 l) l M).map (ι (fk l k) (xi0 l) l M) := by
    apply le_antisymm
    · refine Ideal.span_le.2 ?_
      rintro _ ⟨⟩
      have hm : ofW (fk l k) (xi0 l) l M (xi0 l) ∈ I (fk l k) (xi0 l) l M := by
        show ι (fk l k) (xi0 l) l M (ofW (fk l k) (xi0 l) l M (xi0 l)) ∈ IB (fk l k) (xi0 l)
        rw [ι_ofW]
        exact Ideal.subset_span rfl
      have := Ideal.mem_map_of_mem (ι (fk l k) (xi0 l) l M) hm
      rwa [ι_ofW] at this
    · exact Ideal.map_comap_le
  exact key

end GlobalTheory.CompanionTheory.LatC
