import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.LinEmbedSt
import GroundTheory.HeightsAndTheta.Heights.Intersections.LinEmbedAlg
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 LinEmbed

/- English proof (translation)
Introduce `F _ K K' _ _ ι ι' _ _ e A hA I I' hI hI' V d L hV`. Proceed by induction on `d generalizing V with`. Consider the case `zero`. Establish `hV'` using `isProjVarF_comap hA hV`. Establish `hi : IsChart V fun k => (hV.1.2.2 k).choose` using `fun k => (hV.1.2.2 k).choose_spec`.

Establish `hi' : IsChart (V.comap (blockLinSubst e A).toRingHom) fun k' => (hV'.1.2.2 k').choose` using `fun k' => (hV'.1.2.2 k').choose_spec`. Rewrite using `[hI'.1 _ _ _ hV' hi', hI.1 V L _ hV hi, ptDeg_comap hA hV hi hi']`. Consider the case `succ n ih`. Take `⟨L0, a, rfl⟩ : ∃ (L0 : Fin n → K → ℤ) (a : K → ℤ), L = Fin.snoc (α` from `fun _ => K → ℤ) L0 a := ⟨Fin.init L, L (Fin.last n), (Fin.snoc_init_self L).symm⟩`. Establish `hL : (fun j => Fin.snoc (α` using `fun _ => K → ℤ) L0 a j ∘ e) = Fin.snoc (α := fun _ => K' → ℤ) (fun j => L0 j ∘ e) (a ∘ e) := by`.

Use function extensionality and compare the values at `j`. Use `Fin.lastCases ?_ (fun j => ?_) j` and prove the remaining obligations. Simplify using `only [Fin.snoc_last]`. Simplify using `only [Fin.snoc_castSucc]`. Establish `hV'` using `isProjVarF_comap hA hV`.

Use `set i' : ∀ k', ι' k' := fun k' => (hV'.1.2.2 k').choose`. Establish `hi' : IsChart (V.comap (blockLinSubst e A).toRingHom) i'` using `fun k' => (hV'.1.2.2 k').choose_spec`. Establish `hf'` using `isMultiHomog_coordProd (F := F) i' (fun k' => (a (e k')).toNat)`. Establish `hg'` using `isMultiHomog_coordProd (F := F) i' (fun k' => (-a (e k')).toNat)`. Establish `hf'V` using `coordProd_not_mem hV'.1.1 i' hi' (fun k' => (a (e k')).toNat)`.

Establish `hg'V` using `coordProd_not_mem hV'.1.1 i' hi' (fun k' => (-a (e k')).toNat)`. Establish `hsec' : IsRatSection (V.comap (blockLinSubst e A).toRingHom) (a ∘ e) _ _` using `⟨_, _, hf', hg', hf'V, hg'V, fun k' => Int.toNat_sub_toNat_neg _⟩`. Establish `hφf` using `isMultiHomog_blockLinSubst (A := A) hf'`. Establish `hφg` using `isMultiHomog_blockLinSubst (A := A) hg'`. Establish `hsec : IsRatSection V a (blockLinSubst e A (∏ k', (X ⟨k', i' k'⟩ : MRingOver F ι') ^ (a (e k')).toNat)) (blockLinSubst e A (∏ k', (X ⟨k', i' k'⟩ : MRingOver F ι') ^ (-a (e k')).toNat))` using `⟨_, _, hφf, hφg, hf'V, hg'V, fun k => by`.

Simplify using `only [Function.comp_apply, Equiv.apply_symm_apply]`. Conclude with `Int.toNat_sub_toNat_neg _⟩`. Rewrite using `[hL, hI'.2 _ n _ _ _ _ hV' hsec', hI.2 V n L0 a _ _ hV hsec, ratDiv_comap hA, cycEval_mapDomain]`. Use `cycEval_congr fun W hW => ?_` and prove the remaining obligations. Establish `hmem : W ∈ divSupp V (blockLinSubst e A (∏ k', (X ⟨k', i' k'⟩ : MRingOver F ι') ^ (a (e k')).toNat)) ∨ W ∈ divSupp V (blockLinSubst e A (∏ k', (X ⟨k', i' k'⟩ : MRingOver F ι') ^ (-a (e k')).toNat))`.

Assume the negation of the conclusion as `h`. Use `push Not at h`. Apply `hW` to reduce the goal to its premises. Simplify using `only [ratDiv, Finsupp.coe_sub, Pi.sub_apply, Finsupp.mapRange_apply, DivisorCycleSwap.divCycle_apply_of_not_mem h.1, DivisorCycleSwap.divCycle_apply_of_not_mem h.2, Nat.cast_zero, sub_zero]`. Establish `hWn : IsProjVarF W n` using `hmem.elim (isProjVarF_of_mem_divSupp hV hφf hf'V) (isProjVarF_of_mem_divSupp hV hφg hg'V)`.

Conclude with `ih W L0 hWn`.
-/
theorem LinEmbed.proof : LinEmbed.Statement := by
  intro F _ K K' _ _ ι ι' _ _ e A hA I I' hI hI' V d L hV
  induction d generalizing V with
  | zero =>
    have hV' := isProjVarF_comap hA hV
    have hi : IsChart V fun k => (hV.1.2.2 k).choose := fun k => (hV.1.2.2 k).choose_spec
    have hi' : IsChart (V.comap (blockLinSubst e A).toRingHom) fun k' => (hV'.1.2.2 k').choose :=
      fun k' => (hV'.1.2.2 k').choose_spec
    rw [hI'.1 _ _ _ hV' hi', hI.1 V L _ hV hi, ptDeg_comap hA hV hi hi']
  | succ n ih =>
    obtain ⟨L0, a, rfl⟩ : ∃ (L0 : Fin n → K → ℤ) (a : K → ℤ),
        L = Fin.snoc (α := fun _ => K → ℤ) L0 a :=
      ⟨Fin.init L, L (Fin.last n), (Fin.snoc_init_self L).symm⟩
    have hL : (fun j => Fin.snoc (α := fun _ => K → ℤ) L0 a j ∘ e) =
        Fin.snoc (α := fun _ => K' → ℤ) (fun j => L0 j ∘ e) (a ∘ e) := by
      funext j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simp only [Fin.snoc_last]
      · simp only [Fin.snoc_castSucc]
    have hV' := isProjVarF_comap hA hV
    set i' : ∀ k', ι' k' := fun k' => (hV'.1.2.2 k').choose
    have hi' : IsChart (V.comap (blockLinSubst e A).toRingHom) i' := fun k' => (hV'.1.2.2 k').choose_spec
    have hf' := isMultiHomog_coordProd (F := F) i' (fun k' => (a (e k')).toNat)
    have hg' := isMultiHomog_coordProd (F := F) i' (fun k' => (-a (e k')).toNat)
    have hf'V := coordProd_not_mem hV'.1.1 i' hi' (fun k' => (a (e k')).toNat)
    have hg'V := coordProd_not_mem hV'.1.1 i' hi' (fun k' => (-a (e k')).toNat)
    have hsec' : IsRatSection (V.comap (blockLinSubst e A).toRingHom) (a ∘ e) _ _ :=
      ⟨_, _, hf', hg', hf'V, hg'V, fun k' => Int.toNat_sub_toNat_neg _⟩
    have hφf := isMultiHomog_blockLinSubst (A := A) hf'
    have hφg := isMultiHomog_blockLinSubst (A := A) hg'
    have hsec : IsRatSection V a (blockLinSubst e A (∏ k', (X ⟨k', i' k'⟩ : MRingOver F ι') ^ (a (e k')).toNat))
        (blockLinSubst e A (∏ k', (X ⟨k', i' k'⟩ : MRingOver F ι') ^ (-a (e k')).toNat)) :=
      ⟨_, _, hφf, hφg, hf'V, hg'V, fun k => by
        simp only [Function.comp_apply, Equiv.apply_symm_apply]
        exact Int.toNat_sub_toNat_neg _⟩
    rw [hL, hI'.2 _ n _ _ _ _ hV' hsec', hI.2 V n L0 a _ _ hV hsec, ratDiv_comap hA,
      cycEval_mapDomain]
    refine cycEval_congr fun W hW => ?_
    have hmem : W ∈ divSupp V (blockLinSubst e A (∏ k', (X ⟨k', i' k'⟩ : MRingOver F ι') ^ (a (e k')).toNat)) ∨
        W ∈ divSupp V (blockLinSubst e A (∏ k', (X ⟨k', i' k'⟩ : MRingOver F ι') ^ (-a (e k')).toNat)) := by
      by_contra h
      push Not at h
      apply hW
      simp only [ratDiv, Finsupp.coe_sub, Pi.sub_apply, Finsupp.mapRange_apply,
        DivisorCycleSwap.divCycle_apply_of_not_mem h.1, DivisorCycleSwap.divCycle_apply_of_not_mem h.2, Nat.cast_zero, sub_zero]
    have hWn : IsProjVarF W n :=
      hmem.elim (isProjVarF_of_mem_divSupp hV hφf hf'V) (isProjVarF_of_mem_divSupp hV hφg hg'V)
    exact ih W L0 hWn

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
