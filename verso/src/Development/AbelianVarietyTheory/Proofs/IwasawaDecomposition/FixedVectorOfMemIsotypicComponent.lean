import Mathlib
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
open Formalism.L2 Formalism.AUTREP ReciprocityTheory.Aut NumberField

namespace GlobalTheory.IsoFix

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

/- English proof (translation)
Take `⟨T, hT⟩` from `hiso`. Establish `hTf0 : T (T.symm ⟨x, hx⟩) = ⟨x, hx⟩` using `T.apply_symm_apply _`. Use `⟨(T.symm ⟨x, hx⟩ : S), (T.symm ⟨x, hx⟩).2, ?_, ?_⟩` and prove the remaining obligations. Introduce `h`. Establish `h1 : T.symm ⟨x, hx⟩ = 0` using `Subtype.ext h`.

Establish `h2 : (⟨x, hx⟩ : S') = 0` using `by rw [← hTf0, h1, map_zero]`. Conclude with `hx0 (congrArg Subtype.val h2)`. Introduce `κ hκ`. Establish `hmem : NG.rt L n κ ((T.symm ⟨x, hx⟩ : S) : GAf L n → W) ∈ S` using `hS.stable κ _ (T.symm ⟨x, hx⟩).2`. Establish `key` using `hT κ (T.symm ⟨x, hx⟩) ⟨_, hmem⟩ rfl`.

Rewrite `key` using `[hTf0]`. Establish `h3 : T ⟨_, hmem⟩ = T (T.symm ⟨x, hx⟩)`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[key, hTf0]`. Conclude with `hfix κ hκ`.

Conclude with `congrArg Subtype.val (T.injective h3)`.
-/
theorem fixed_transport {ρ : Representation ℂ (GQ L n) W} {S S' : Submodule ℂ (GAf L n → W)} (K : Set (GAf L n))
    (hS : NG.IsSubrep ρ S) (hiso : NG.IsoRep S S') {x : GAf L n → W} (hx : x ∈ S') (hx0 : x ≠ 0)
    (hfix : ∀ κ ∈ K, NG.rt L n κ x = x) :
    ∃ f' ∈ S, f' ≠ 0 ∧ ∀ κ ∈ K, NG.rt L n κ f' = f' := by
  obtain ⟨T, hT⟩ := hiso
  have hTf0 : T (T.symm ⟨x, hx⟩) = ⟨x, hx⟩ := T.apply_symm_apply _
  refine ⟨(T.symm ⟨x, hx⟩ : S), (T.symm ⟨x, hx⟩).2, ?_, ?_⟩
  · intro h
    have h1 : T.symm ⟨x, hx⟩ = 0 := Subtype.ext h
    have h2 : (⟨x, hx⟩ : S') = 0 := by rw [← hTf0, h1, map_zero]
    exact hx0 (congrArg Subtype.val h2)
  · intro κ hκ
    have hmem : NG.rt L n κ ((T.symm ⟨x, hx⟩ : S) : GAf L n → W) ∈ S := hS.stable κ _ (T.symm ⟨x, hx⟩).2
    have key := hT κ (T.symm ⟨x, hx⟩) ⟨_, hmem⟩ rfl
    rw [hTf0] at key
    have h3 : T ⟨_, hmem⟩ = T (T.symm ⟨x, hx⟩) := by
      apply Subtype.ext
      rw [key, hTf0]
      exact hfix κ hκ
    exact congrArg Subtype.val (T.injective h3)

/- English proof (translation)
Establish `hle : (⨆ i ∈ s, i) ≤ (⨆ i ∈ s, i).comap (NG.rt L n h)`. Use `iSup₂_le fun i hi => ?_` and prove the remaining obligations. Introduce `f hf`. Conclude with `(le_iSup₂ (f := fun i (_ : i ∈ s) => i) i hi) (hs i hi h f hf)`. Conclude with `fun f hf => hle hf`.
-/
theorem iSup_finset_stable (s : Finset (Submodule ℂ (GAf L n → W)))
    (hs : ∀ i ∈ s, ∀ h, ∀ f ∈ i, NG.rt L n h f ∈ i) (h : GAf L n) :
    ∀ f ∈ (⨆ i ∈ s, i), NG.rt L n h f ∈ (⨆ i ∈ s, i) := by
  have hle : (⨆ i ∈ s, i) ≤ (⨆ i ∈ s, i).comap (NG.rt L n h) := by
    refine iSup₂_le fun i hi => ?_
    intro f hf
    exact (le_iSup₂ (f := fun i (_ : i ∈ s) => i) i hi) (hs i hi h f hf)
  exact fun f hf => hle hf

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Introduce `_ f hf hf0 _`. Simplify using `at hf`. Conclude with `absurd hf hf0`.

Consider the case `insert a s ha ih`. Introduce `hsub f hf hf0 hfix`. Establish `haF : NG.IsIrrRep ρ a ∧ NG.IsoRep S a` using `hsub (Finset.mem_insert_self a s)`. Establish `hsF : (↑s : Set _) ⊆ {S' | NG.IsIrrRep ρ S' ∧ NG.IsoRep S S'}` using `fun x hx => hsub (Finset.mem_insert_of_mem hx)`. Rewrite `hf` using `[Finset.iSup_insert]`.

Establish `hMst : ∀ h, ∀ g ∈ (⨆ i ∈ s, i), NG.rt L n h g ∈ (⨆ i ∈ s, i)` using `iSup_finset_stable s (fun i hi => (hsF hi).1.1.stable)`. Establish `hsubrep : NG.IsSubrep ρ (a ⊓ ⨆ i ∈ s, i)` using `⟨inf_le_left.trans haF.1.1.le, fun h g hg => ⟨haF.1.1.stable h g hg.1, hMst h g hg.2⟩⟩`. Break down `haF.1.2.2 _ hsubrep inf_le_left with h0 | htop` into its components or cases. Take `⟨y, hy, z, hz, rfl⟩` from `Submodule.mem_sup.1 hf`. Establish `hyfix : ∀ κ ∈ K, NG.rt L n κ y = y`.

Introduce `κ hκ`. Establish `e` using `hfix κ hκ`. Rewrite `e` using `[map_add]`. Establish `hd : NG.rt L n κ y - y ∈ a ⊓ ⨆ i ∈ s, i`. Use `⟨Submodule.sub_mem _ (haF.1.1.stable κ y hy) hy, ?_⟩` and prove the remaining obligations.

Establish `h4 : NG.rt L n κ y - y = z - NG.rt L n κ z`. Rewrite using `[sub_eq_sub_iff_add_eq_add, e]`. Conclude with `add_comm _ _`. Rewrite using `[h4]`. Conclude with `Submodule.sub_mem _ hz (hMst κ z hz)`.

Rewrite `hd` using `[h0, Submodule.mem_bot, sub_eq_zero]`. Conclude with `hd`. Distinguish the cases in `hy0 : y = 0`. Substitute `hy0` using the available equality. Simplify using `only [zero_add] at hf0 hfix`.

Conclude with `ih hsF z hz hf0 hfix`. Conclude with `fixed_transport K hS.1 haF.2 hy hy0 hyfix`. Establish `hle : a ≤ ⨆ i ∈ s, i` using `inf_eq_left.1 htop`. Conclude with `ih hsF f ((sup_le hle le_rfl) hf) hf0 hfix`.
-/
theorem fixed_of_mem_finset_sum (ρ : Representation ℂ (GQ L n) W) (S : Submodule ℂ (GAf L n → W))
    (K : Set (GAf L n)) (hS : NG.IsIrrRep ρ S) (s : Finset (Submodule ℂ (GAf L n → W))) :
    (↑s ⊆ {S' | NG.IsIrrRep ρ S' ∧ NG.IsoRep S S'}) → ∀ f ∈ (⨆ i ∈ s, i), f ≠ 0 →
      (∀ κ ∈ K, NG.rt L n κ f = f) → ∃ f' ∈ S, f' ≠ 0 ∧ ∀ κ ∈ K, NG.rt L n κ f' = f' := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro _ f hf hf0 _
    simp at hf
    exact absurd hf hf0
  | insert a s ha ih =>
    intro hsub f hf hf0 hfix
    have haF : NG.IsIrrRep ρ a ∧ NG.IsoRep S a := hsub (Finset.mem_insert_self a s)
    have hsF : (↑s : Set _) ⊆ {S' | NG.IsIrrRep ρ S' ∧ NG.IsoRep S S'} :=
      fun x hx => hsub (Finset.mem_insert_of_mem hx)
    rw [Finset.iSup_insert] at hf
    have hMst : ∀ h, ∀ g ∈ (⨆ i ∈ s, i), NG.rt L n h g ∈ (⨆ i ∈ s, i) :=
      iSup_finset_stable s (fun i hi => (hsF hi).1.1.stable)
    have hsubrep : NG.IsSubrep ρ (a ⊓ ⨆ i ∈ s, i) :=
      ⟨inf_le_left.trans haF.1.1.le, fun h g hg => ⟨haF.1.1.stable h g hg.1, hMst h g hg.2⟩⟩
    rcases haF.1.2.2 _ hsubrep inf_le_left with h0 | htop
    · obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hf
      have hyfix : ∀ κ ∈ K, NG.rt L n κ y = y := by
        intro κ hκ
        have e := hfix κ hκ
        rw [map_add] at e
        have hd : NG.rt L n κ y - y ∈ a ⊓ ⨆ i ∈ s, i := by
          refine ⟨Submodule.sub_mem _ (haF.1.1.stable κ y hy) hy, ?_⟩
          have h4 : NG.rt L n κ y - y = z - NG.rt L n κ z := by
            rw [sub_eq_sub_iff_add_eq_add, e]
            exact add_comm _ _
          rw [h4]
          exact Submodule.sub_mem _ hz (hMst κ z hz)
        rw [h0, Submodule.mem_bot, sub_eq_zero] at hd
        exact hd
      by_cases hy0 : y = 0
      · subst hy0
        simp only [zero_add] at hf0 hfix
        exact ih hsF z hz hf0 hfix
      · exact fixed_transport K hS.1 haF.2 hy hy0 hyfix
    · have hle : a ≤ ⨆ i ∈ s, i := inf_eq_left.1 htop
      exact ih hsF f ((sup_le hle le_rfl) hf) hf0 hfix

/- English proof (translation)
Introduce `L _ _ _ n W _ _ ρ S K hS f hf hf0 hfix`. Take `⟨s, hs, hfs⟩` from `Submodule.mem_sSup_iff_exists_finset.1 hf`. Conclude with `fixed_of_mem_finset_sum ρ S K hS s hs f hfs hf0 hfix`.
-/
theorem fixed_of_isoTyp : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W]
    [Module ℂ W] (ρ : Representation ℂ (GQ L n) W) (S : Submodule ℂ (GAf L n → W)) (K : Set (GAf L n)),
    NG.IsIrrRep ρ S → ∀ f ∈ NG.isoTyp ρ S, f ≠ 0 → (∀ κ ∈ K, NG.rt L n κ f = f) →
      ∃ f' ∈ S, f' ≠ 0 ∧ ∀ κ ∈ K, NG.rt L n κ f' = f' := by
  intro L _ _ _ n W _ _ ρ S K hS f hf hf0 hfix
  obtain ⟨s, hs, hfs⟩ := Submodule.mem_sSup_iff_exists_finset.1 hf
  exact fixed_of_mem_finset_sum ρ S K hS s hs f hfs hf0 hfix

end GlobalTheory.IsoFix
