import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsBisLast
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsTerAlt
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsBisFurther
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinPlainPolyPairNum
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

namespace FlagPairValueIndependence

/- English proof (translation)
Unfold `IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum`. Use `Finset.sum_congr rfl fun μ hμ => ?_` and prove the remaining obligations. Establish `hm : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList deg₁ μ = IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList deg₂ μ`. Unfold `IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList`. Use `congr 1`.

Use function extensionality and compare the values at `s`. Distinguish the cases in `hs : μ s = 0`. Simplify using `[hs]`. Rewrite using `[h s ((mem_vars_iff_mem_support s).mpr ⟨μ, hμ, Finsupp.mem_support_iff.mpr hs⟩)]`. Conclude with `congrArg (fun l : List (K → ℤ) => P.coeff μ * if h : l.length = n then I W n (fun j => l.get (Fin.cast h.symm j)) else 0) hm`.
-/
theorem polyNum_congr {F : Type*} [Field F] {K : Type} [Fintype K] {κ : K → Type} [∀ k, Fintype (κ k)]
    (I : ReciprocityTheory.ChartRestriction.G.AI.I1.IFamily F κ) (W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F κ)) (n : ℕ)
    {m : ℕ} {deg₁ deg₂ : Fin m → K → ℤ} (P : MvPolynomial (Fin m) ℤ)
    (h : ∀ s ∈ P.vars, deg₁ s = deg₂ s) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum I W n deg₁ P = IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum I W n deg₂ P := by
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have hm : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList deg₁ μ = IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList deg₂ μ := by
    unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList
    congr 1
    funext s
    by_cases hs : μ s = 0
    · simp [hs]
    · rw [h s ((mem_vars_iff_mem_support s).mpr ⟨μ, hμ, Finsupp.mem_support_iff.mpr hs⟩)]
  exact congrArg (fun l : List (K → ℤ) => P.coeff μ * if h : l.length = n then
    I W n (fun j => l.get (Fin.cast h.symm j)) else 0) hm

/- English proof (translation)
Introduce `hs`. Take `⟨μ, hμ, hsμ⟩` from `(mem_vars_iff_mem_support _).mp hs`. Establish `he : Function.Injective (finSumFinEquiv.symm : Fin ((N + r) + (N + r)) → Fin (N + r) ⊕ Fin (N + r))` using `finSumFinEquiv.symm.injective`. Establish `h1 : Finsupp.mapDomain finSumFinEquiv.symm μ ∈ (rename finSumFinEquiv.symm (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff (Fin.castAdd r i) (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q))).support`. Rewrite using `[support_rename_of_injective he]`.

Conclude with `Finset.mem_image_of_mem _ hμ`. Establish `h2 : finSumFinEquiv.symm (Fin.natAdd (N + r) (Fin.natAdd N j)) ∈ (rename finSumFinEquiv.symm (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff (Fin.castAdd r i) (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q))).vars`. Use `(mem_vars_iff_mem_support _).mpr ⟨_, h1, ?_⟩` and prove the remaining obligations. Rewrite using `[Finsupp.mem_support_iff, Finsupp.mapDomain_apply he]`. Conclude with `Finsupp.mem_support_iff.mp hsμ`.

Rewrite `h2` using `[finSumFinEquiv_symm_apply_natAdd, plainPolynomialPairNumber.rename_divDiff_castAdd_mul]`. Break down `Finset.mem_union.mp (vars_mul _ _ h2) with h3 | h3` into its components or cases. Take `⟨t, -, ht⟩` from `Finset.mem_image.mp (vars_rename _ _ h3)`. Break down `t with t | t` into its components or cases. Conclude with `Sum.inl_ne_inr ht`.

Simplify using `only [Sum.map_inr, Sum.inr.injEq] at ht`. Use `congrArg Fin.val ht` as an intermediate fact. Simplify using `only [Fin.val_castAdd, Fin.val_natAdd] at this`. Use linear arithmetic over natural numbers and integers. Take `⟨t, -, ht⟩` from `Finset.mem_image.mp (vars_rename _ _ h3)`.

Conclude with `Sum.inl_ne_inr ht`.
-/
theorem not_mem_vars_divDiff_castAdd {N r : ℕ} (i : Fin N) (j : Fin r) (G : MvPolynomial (Fin N) ℤ)
    (Q : MvPolynomial (Fin r) ℤ) :
    Fin.natAdd (N + r) (Fin.natAdd N j) ∉ (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff (Fin.castAdd r i)
      (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q)).vars := by
  classical
  intro hs
  obtain ⟨μ, hμ, hsμ⟩ := (mem_vars_iff_mem_support _).mp hs
  have he : Function.Injective
      (finSumFinEquiv.symm : Fin ((N + r) + (N + r)) → Fin (N + r) ⊕ Fin (N + r)) :=
    finSumFinEquiv.symm.injective
  have h1 : Finsupp.mapDomain finSumFinEquiv.symm μ ∈ (rename finSumFinEquiv.symm
      (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff (Fin.castAdd r i)
        (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q))).support := by
    rw [support_rename_of_injective he]
    exact Finset.mem_image_of_mem _ hμ
  have h2 : finSumFinEquiv.symm (Fin.natAdd (N + r) (Fin.natAdd N j)) ∈ (rename finSumFinEquiv.symm
      (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff (Fin.castAdd r i)
        (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q))).vars := by
    refine (mem_vars_iff_mem_support _).mpr ⟨_, h1, ?_⟩
    rw [Finsupp.mem_support_iff, Finsupp.mapDomain_apply he]
    exact Finsupp.mem_support_iff.mp hsμ
  rw [finSumFinEquiv_symm_apply_natAdd, plainPolynomialPairNumber.rename_divDiff_castAdd_mul] at h2
  rcases Finset.mem_union.mp (vars_mul _ _ h2) with h3 | h3
  · obtain ⟨t, -, ht⟩ := Finset.mem_image.mp (vars_rename _ _ h3)
    rcases t with t | t
    · exact Sum.inl_ne_inr ht
    · simp only [Sum.map_inr, Sum.inr.injEq] at ht
      have := congrArg Fin.val ht
      simp only [Fin.val_castAdd, Fin.val_natAdd] at this
      omega
  · obtain ⟨t, -, ht⟩ := Finset.mem_image.mp (vars_rename _ _ h3)
    exact Sum.inl_ne_inr ht

/- English proof (translation)
Introduce `O _ _ _ Ω _ _ K _ ι _ x d N V _ _ E E' hM hS φ₁ φ₂ I hI G hG r y y' f g hv c Q hc hGc hQ`. Establish `hz : ∀ J : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver (IsLocalRing.ResidueField O) ι) → ℤ, IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O J 0 = 0` using `fun J => Finsupp.sum_zero_index`. Establish `h0 : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) 1 1 = 0` using `sub_self _`. Establish `split : ∀ φ : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagPair O x E E', IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O I (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) d (Fin.append φ.deg y) (Fin.append φ.deg' y') (Fin.append φ.f f) (Fin.append φ.g g) …`. Introduce `φ`.

Unfold `IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum`. Rewrite using `[Fin.sum_univ_add, Fin.sum_univ_add]`. Simplify using `only [Fin.append_left, Fin.append_right, h0, hz, Finset.sum_const_zero, add_zero]`. Use `congrArg (· + _) (Finset.sum_congr rfl fun i _ => ?_)` and prove the remaining obligations. Use `congrArg (fun J => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O J _) (funext fun W => ?_)` and prove the remaining obligations.

Use `polyNum_congr I W d _ fun s hs => ?_` and prove the remaining obligations. Proceed by induction on `s using Fin.addCases with`. Consider the case `left a => simp only [Fin.append_left]`. Consider the case `right b`. Proceed by induction on `b using Fin.addCases with`.

Consider the case `left a => simp only [Fin.append_right, Fin.append_left]`. Consider the case `right j => exact absurd hs (not_mem_vars_divDiff_castAdd i j G Q)`. Rewrite using `[split φ₁, split φ₂, hPlain O Ω K ι x d N V E E' hM hS φ₁ φ₂ I hI G hG r y c Q hc hGc hQ]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun l _ => hFur O Ω K ι x d N V E E' hM hS φ₁ φ₂ I hI G hG r y y' f g hv c Q hc hGc hQ l`.
-/
theorem proof (hPlain : FlagPlainValueIndependence.Statement)
    (hFur : flagFurtherTerm_independent.Statement) : FlagPairValueIndependence.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ x d N V _ _ E E' hM hS φ₁ φ₂ I hI G hG r y y' f g hv c Q hc hGc hQ
  classical
  have hz : ∀ J : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver (IsLocalRing.ResidueField O) ι) → ℤ,
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O J 0 = 0 := fun J => Finsupp.sum_zero_index
  have h0 : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) 1 1 = 0 :=
    sub_self _
  have split : ∀ φ : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagPair O x E E',
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O I (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) d
                                (Fin.append φ.deg y) (Fin.append φ.deg' y') (Fin.append φ.f f) (Fin.append φ.g g)
                                (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q) =
        IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O I (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) d
                                  (Fin.append φ.deg y) (Fin.append φ.deg' y) (Fin.append φ.f fun _ => 1)
                                  (Fin.append φ.g fun _ => 1) (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q) +
          ∑ l : Fin r, IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O
            (fun W => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum I W d
              (Fin.append (Fin.append φ.deg y) (Fin.append φ.deg' y'))
              (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff (Fin.natAdd N l)
                (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q)))
            (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) (f l) (g l)) := by
    intro φ
    unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum
    rw [Fin.sum_univ_add, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, h0, hz, Finset.sum_const_zero, add_zero]
    refine congrArg (· + _) (Finset.sum_congr rfl fun i _ => ?_)
    refine congrArg (fun J => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O J _) (funext fun W => ?_)
    refine polyNum_congr I W d _ fun s hs => ?_
    induction s using Fin.addCases with
    | left a => simp only [Fin.append_left]
    | right b =>
      induction b using Fin.addCases with
      | left a => simp only [Fin.append_right, Fin.append_left]
      | right j => exact absurd hs (not_mem_vars_divDiff_castAdd i j G Q)
  rw [split φ₁, split φ₂, hPlain O Ω K ι x d N V E E' hM hS φ₁ φ₂ I hI G hG r y c Q hc hGc hQ]
  congr 1
  exact Finset.sum_congr rfl fun l _ =>
    hFur O Ω K ι x d N V E E' hM hS φ₁ φ₂ I hI G hG r y y' f g hv c Q hc hGc hQ l

end FlagPairValueIndependence

end GroundTheory.Heights₂.Heights.NumbersDVR
