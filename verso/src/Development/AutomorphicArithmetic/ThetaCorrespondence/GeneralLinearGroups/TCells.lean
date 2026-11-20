import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.CasselmanSuffTemp
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSubquotientCompMulSingle
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiExteriorTensorSmoothIrreducibleIsIrreducibleStatement

open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Introduce `hGL hBZ k _ _ _ _ h N δ hd x hx hne`. Take `⟨hJ, hC⟩` from `hGL k`. Use `haveI hfin : Fintype (SizeMatrix (fun i : Fin h => Fin (δ i).1) (fun j : Fin 2 => Fin (x j).1)) := by haveI : Finite (SizeMatrix (fun i : Fin h => Fin (δ i).1) (fun j : Fin 2 => Fin (x j).1)) := by`. Use `Finite.of_injective (β := (i : Fin h) → Fin 2 → Fin ((δ i).1 + 1)) (fun b i j => ⟨b.1 i j, Nat.lt_succ_of_le ?_⟩) ?_` and prove the remaining obligations. Establish `hrow` using `b.2.1 i`.

Simplify using `only [Fintype.card_fin] at hrow`. Rewrite using `[← hrow]`. Conclude with `Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)`. Introduce `b b' hbb`. Apply `Subtype.ext` to reduce the goal to its premises.

Use function extensionality and compare the values at `i j`. Use `congrFun (congrFun hbb i) j` as an intermediate fact. Simplify using `using this`. Conclude with `Fintype.ofFinite _`. Set `f : (b : SizeMatrix (fun i : Fin h => Fin (δ i).1) (fun j : Fin 2 => Fin (x j).1)) → (i : Fin h) → (j : Fin 2) × Fin (b.1 i j) ≃ Fin (δ i).1` to `fun b i => stdBlocks (fun j => b.1 i j) (by simpa using b.2.1 i)`.

Set `g : (b : SizeMatrix (fun i : Fin h => Fin (δ i).1) (fun j : Fin 2 => Fin (x j).1)) → (j : Fin 2) → (i : Fin h) × Fin (b.1 i j) ≃ Fin (x j).1` to `fun b j => stdBlocks (fun i => b.1 i j) (by simpa using b.2.2 j)`. Establish `hτirr : (piTensor fun j => (x j).rep).IsIrreducible` using `GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible hBZ k (Fin 2) (fun j => Fin (x j).1) (fun j => (x j).snd.rep)`. Establish `hsm : IsSmooth (piTensor fun i => (δ i).rep)` using `isSmooth_piTensor (fun i => (δ i).snd.rep.smooth)`. Establish `hne' : jhMult (piTensor fun j => (x j).rep) (jac (stdBlocks (fun j => (x j).1) hx) (parInd (stdBlocks (fun i => (δ i).1) hd) (piTensor fun i => (δ i).rep))) ≠ 0` using `hne`. Rewrite `hne'` using `[JacquetOfInducedFiltration.jhMult_eq hJ (stdBlocks _ hd) (stdBlocks _ hx) hsm f g hτirr]`.

Take `⟨b, -, hb⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hne'`. Take `⟨T, -, hT⟩` from `hC (Fin h) (Fin 2) (fun i => Fin (δ i).1) (fun j => Fin (x j).1) (fun i j => Fin (b.1 i j)) (f b) (g b) _ (fun i => (δ i).rep) (fun i => (δ i).snd.rep.smooth) (fun i => hasFiniteLength_of_isIrreducible (δ i).snd.rep.irr)`. Establish `hT'` using `hT ⟨_, piTensor fun j => (x j).rep, isSmooth_piTensor (fun j => (x j).snd.rep.smooth), hτirr⟩`. Rewrite `hb` using `[hT']`. Take `⟨s, -, hs⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hb`.

Establish `hs1` using `left_ne_zero_of_mul hs`. Establish `hs2` using `right_ne_zero_of_mul hs`. Rewrite `hs1` using `[Finset.prod_ne_zero_iff]`. Use `⟨fun i j => ⟨b.1 i j, s i j⟩, fun i => by simpa using b.2.1 i, fun j => by simpa using b.2.2 j, fun i => ?_, fun j => ?_⟩` and prove the remaining obligations. Conclude with `hs1 i (Finset.mem_univ i)`.

Rewrite `hs2`, the goal using `[jhMult_ne_zero_iff]`. Establish `h1` using `SupportUnique.isSubquotient_comp hs2 (MonoidHom.mulSingle (fun j : Fin 2 => GL (Fin (x j).1) k) j)`. Establish `h2` using `GlobalTheory.CompanionTheory.Hypotheses₂.TD.isSubquotient_comp_mulSingle (fun j => (x j).rep) (fun j => (x j).snd.rep.irr) j`. Conclude with `SupportUnique.isSubquotient_factor _ j (x j).snd.rep.irr (h2.trans h1)`.
-/
theorem UpperTheory.Lit.Cas.cells :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (h N : ℕ) (δ : Fin h → IrrGL k) (hd : ∑ i, (δ i).1 = N) (x : Fin 2 → IrrGL k) (hx : ∑ j, (x j).1 = N), jm x hx (prodIrr δ hd) ≠ 0 → ∃ (y : Fin h → Fin 2 → IrrGL k) (hr : ∀ i, ∑ j, (y i j).1 = (δ i).1) (hc : ∀ j, ∑ i, (y i j).1 = (x j).1), (∀ i, jm (y i) (hr i) (δ i).rep ≠ 0) ∧ ∀ j, jhMult (x j).rep (prodIrr (fun i => y i j) (hc j)) ≠ 0 := by
  intro hGL hBZ k _ _ _ _ h N δ hd x hx hne
  classical
  obtain ⟨hJ, hC⟩ := hGL k
  haveI hfin : Fintype (SizeMatrix (fun i : Fin h => Fin (δ i).1) (fun j : Fin 2 => Fin (x j).1)) := by
    haveI : Finite (SizeMatrix (fun i : Fin h => Fin (δ i).1) (fun j : Fin 2 => Fin (x j).1)) := by
      refine Finite.of_injective (β := (i : Fin h) → Fin 2 → Fin ((δ i).1 + 1))
        (fun b i j => ⟨b.1 i j, Nat.lt_succ_of_le ?_⟩) ?_
      · have hrow := b.2.1 i
        simp only [Fintype.card_fin] at hrow
        rw [← hrow]
        exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      · intro b b' hbb
        apply Subtype.ext
        funext i j
        have := congrFun (congrFun hbb i) j
        simpa using this
    exact Fintype.ofFinite _
  let f : (b : SizeMatrix (fun i : Fin h => Fin (δ i).1) (fun j : Fin 2 => Fin (x j).1)) →
      (i : Fin h) → (j : Fin 2) × Fin (b.1 i j) ≃ Fin (δ i).1 := fun b i =>
    stdBlocks (fun j => b.1 i j) (by simpa using b.2.1 i)
  let g : (b : SizeMatrix (fun i : Fin h => Fin (δ i).1) (fun j : Fin 2 => Fin (x j).1)) →
      (j : Fin 2) → (i : Fin h) × Fin (b.1 i j) ≃ Fin (x j).1 := fun b j =>
    stdBlocks (fun i => b.1 i j) (by simpa using b.2.2 j)
  have hτirr : (piTensor fun j => (x j).rep).IsIrreducible :=
    GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible hBZ k (Fin 2) (fun j => Fin (x j).1) (fun j => (x j).snd.rep)
  have hsm : IsSmooth (piTensor fun i => (δ i).rep) := isSmooth_piTensor (fun i => (δ i).snd.rep.smooth)
  have hne' : jhMult (piTensor fun j => (x j).rep) (jac (stdBlocks (fun j => (x j).1) hx)
      (parInd (stdBlocks (fun i => (δ i).1) hd) (piTensor fun i => (δ i).rep))) ≠ 0 := hne
  rw [JacquetOfInducedFiltration.jhMult_eq hJ (stdBlocks _ hd) (stdBlocks _ hx) hsm f g hτirr] at hne'
  obtain ⟨b, -, hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne'
  obtain ⟨T, -, hT⟩ := hC (Fin h) (Fin 2) (fun i => Fin (δ i).1) (fun j => Fin (x j).1)
    (fun i j => Fin (b.1 i j)) (f b) (g b) _ (fun i => (δ i).rep) (fun i => (δ i).snd.rep.smooth)
    (fun i => hasFiniteLength_of_isIrreducible (δ i).snd.rep.irr)
  have hT' := hT ⟨_, piTensor fun j => (x j).rep, isSmooth_piTensor (fun j => (x j).snd.rep.smooth), hτirr⟩
  rw [hT'] at hb
  obtain ⟨s, -, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero hb
  have hs1 := left_ne_zero_of_mul hs
  have hs2 := right_ne_zero_of_mul hs
  rw [Finset.prod_ne_zero_iff] at hs1
  refine ⟨fun i j => ⟨b.1 i j, s i j⟩, fun i => by simpa using b.2.1 i, fun j => by simpa using b.2.2 j,
    fun i => ?_, fun j => ?_⟩
  · exact hs1 i (Finset.mem_univ i)
  · rw [jhMult_ne_zero_iff] at hs2 ⊢
    have h1 := SupportUnique.isSubquotient_comp hs2
      (MonoidHom.mulSingle (fun j : Fin 2 => GL (Fin (x j).1) k) j)
    have h2 := GlobalTheory.CompanionTheory.Hypotheses₂.TD.isSubquotient_comp_mulSingle (fun j => (x j).rep)
      (fun j => (x j).snd.rep.irr) j
    exact SupportUnique.isSubquotient_factor _ j (x j).snd.rep.irr (h2.trans h1)
