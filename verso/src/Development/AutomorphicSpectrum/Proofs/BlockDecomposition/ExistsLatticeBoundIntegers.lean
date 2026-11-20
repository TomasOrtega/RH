import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegerMemLatticeSubBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFinsetGenerators
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PadicIntMemSub

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatCOK

/- English proof (translation)
Introduce `l _ K _`. Take `⟨s, hs⟩` from `GlobalTheory.CompanionTheory.LocalIntegers.exists_finset_generators l K`. Use `choose c hc using GlobalTheory.T.integer_mem_lattice_sub_bound l K`. Use `⟨2 * s.sup c, fun k a => ?_⟩` and prove the remaining obligations. Take `⟨d, hd⟩` from `hs a`.

Establish `h1 : Lat.kP l K a = ∑ i ∈ s, algClToBdR l (algebraMap ℚ_[l] (PadicAlgCl l) (d i : ℚ_[l])) * Lat.kP l K i`. Establish `h2 : Lat.kP l K a = algClToBdR l (((a : K) : PadicAlgCl l))` using `rfl`. Rewrite using `[h2, hd, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, map_mul]`.

Both sides reduce to the same expression. Rewrite using `[h1, map_sum]`. Use `Subring.sum_mem _ fun i hi => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `Subring.mul_mem _ (GlobalTheory.CompanionTheory.LatCZp.padicInt_mem_sub l _ k (d i)) (hc i _ k (Nat.mul_le_mul_left 2 (Finset.le_sup hi)))`.
-/
theorem exists_uniform_mem_sub : ∀ (l : ℕ) [Fact l.Prime]
    (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K],
    ∃ M : ℕ, ∀ (k : ℕ) (a : OK l K),
      Lat.pk l k (Lat.kP l K a) ∈ Lat.sub (Lat.fk l k) (xi0 l) l M := by
  intro l _ K _
  classical
  obtain ⟨s, hs⟩ := GlobalTheory.CompanionTheory.LocalIntegers.exists_finset_generators l K
  choose c hc using GlobalTheory.T.integer_mem_lattice_sub_bound l K
  refine ⟨2 * s.sup c, fun k a => ?_⟩
  obtain ⟨d, hd⟩ := hs a
  have h1 : Lat.kP l K a = ∑ i ∈ s, algClToBdR l (algebraMap ℚ_[l] (PadicAlgCl l) (d i : ℚ_[l])) *
      Lat.kP l K i := by
    have h2 : Lat.kP l K a = algClToBdR l (((a : K) : PadicAlgCl l)) := rfl
    rw [h2, hd, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, map_mul]
    rfl
  rw [h1, map_sum]
  refine Subring.sum_mem _ fun i hi => ?_
  rw [map_mul]
  exact Subring.mul_mem _ (GlobalTheory.CompanionTheory.LatCZp.padicInt_mem_sub l _ k (d i))
    (hc i _ k (Nat.mul_le_mul_left 2 (Finset.le_sup hi)))

end GlobalTheory.CompanionTheory.LatCOK
