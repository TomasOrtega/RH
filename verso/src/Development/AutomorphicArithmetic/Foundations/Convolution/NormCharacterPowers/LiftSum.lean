import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.SumSatUnit
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.JacquetShalikaRigidity
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlobalArtinReciprocityHolds
import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele

open UpperTheory.ConvolutionTheory.R

/- English proof (translation)
Introduce `K M _ _ _ _ _ _ _ _ _ ι _ κ _ n m π P h`. Establish `h'` using `Filter.eventually_all.2 h`. Use `h'.mono fun w hw f hf => ?_` and prove the remaining obligations. Use `choose B hB C hC e using fun i => hw i f hf`. Use `⟨∑ i, B i, ⟨B, hB, rfl⟩, fun a => C a.1 a.2, fun a => hC a.1 a.2, ?_⟩` and prove the remaining obligations.

Rewrite using `[Fintype.sum_sigma]`. Establish `: (∑ i, B i).map (· ^ f) = ∑ i, (B i).map (· ^ f)` using `map_sum (Multiset.mapAddMonoidHom (· ^ f)) B Finset.univ`. Rewrite using `[this]`. Conclude with `Finset.sum_congr rfl fun i _ => e i`.
-/
theorem UpperTheory.ConvolutionTheory.R.liftSum :
    LiftSum := by
  intro K M _ _ _ _ _ _ _ _ _ ι _ κ _ n m π P h
  have h' := Filter.eventually_all.2 h
  refine h'.mono fun w hw f hf => ?_
  choose B hB C hC e using fun i => hw i f hf
  refine ⟨∑ i, B i, ⟨B, hB, rfl⟩, fun a => C a.1 a.2, fun a => hC a.1 a.2, ?_⟩
  rw [Fintype.sum_sigma]
  have : (∑ i, B i).map (· ^ f) = ∑ i, (B i).map (· ^ f) :=
    map_sum (Multiset.mapAddMonoidHom (· ^ f)) B Finset.univ
  rw [this]
  exact Finset.sum_congr rfl fun i _ => e i
