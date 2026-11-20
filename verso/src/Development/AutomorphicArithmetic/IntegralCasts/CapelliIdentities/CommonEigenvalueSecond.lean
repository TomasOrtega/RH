import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CommonEigenvalue

/- English proof (translation)
Introduce `ι M _ _ _ f hc n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `W hn hW hinv`. Distinguish the cases in `h : ∀ i, ∃ c : ℂ, ∀ x ∈ W, f i x = c • x`.

Take `⟨v, hv, hv0⟩` from `(Submodule.ne_bot_iff W).1 hW`. Conclude with `⟨v, hv, hv0, fun i => (h i).imp fun c hc' => hc' v hv⟩`. Take `⟨i, hi⟩` from `not_forall.1 h haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.2 hW`. Take `⟨c, hce⟩` from `Module.End.exists_eigenvalue ((f i).restrict (p := W) (q := W) (hinv i) : Module.End ℂ W)`. Take `⟨w, hw⟩` from `hce.exists_hasEigenvector`.

Establish `hw1 : f i (w : M) = c • (w : M)` using `congrArg Subtype.val hw.apply_eq_smul`. Establish `hw0 : (w : M) ≠ 0` using `fun e => hw.2 (Subtype.ext e)`. Establish `hlt : W ⊓ (f i).eigenspace c < W`. Use `lt_of_le_of_ne inf_le_left fun e => hi ⟨c, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite `hx` using `[← e]`.

Conclude with `Module.End.mem_eigenspace_iff.1 hx.2`. Establish `hne : W ⊓ (f i).eigenspace c ≠ ⊥` using `(Submodule.ne_bot_iff _).2 ⟨w, ⟨w.2, Module.End.mem_eigenspace_iff.2 hw1⟩, hw0⟩`. Take `⟨v, hv, hv0, hall⟩` from `ih _ (hn ▸ Submodule.finrank_lt_finrank_of_lt hlt) (W ⊓ (f i).eigenspace c) rfl hne (fun j x hx => by`. Use `⟨hinv j x hx.1, Module.End.mem_eigenspace_iff.2 ?_⟩` and prove the remaining obligations. Establish `h1 : f i x = c • x` using `Module.End.mem_eigenspace_iff.1 hx.2`.

Establish `h2 : f i (f j x) = f j (f i x)` using `LinearMap.congr_fun (hc i j).eq x`. Rewrite using `[h2, h1, map_smul])`. Conclude with `⟨v, hv.1, hv0, hall⟩`.
-/
theorem UpperTheory.Reformulated.B.ComplexCommonEigenvectorOfFinrankEq.common_eig :
    ∀ {ι M : Type} [inst : AddCommGroup M]
    [inst_1 : _root_.Module ℂ M] [FiniteDimensional ℂ M] (f : ι → Module.End ℂ M),
    (∀ (i j : ι), Commute (f i) (f j)) →
      ∀ (n : ℕ) (W : Submodule ℂ M),
        Module.finrank ℂ ↥W = n →
          W ≠ ⊥ →
            (∀ (i : ι), ∀ x ∈ W, (f i : M → M) x ∈ W) →
              ∃ v ∈ W, v ≠ (0 : M) ∧ ∀ (i : ι), ∃ (c : ℂ), (f i : M → M) v = c • v := by
  intro ι M _ _ _ f hc n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro W hn hW hinv
  by_cases h : ∀ i, ∃ c : ℂ, ∀ x ∈ W, f i x = c • x
  · obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff W).1 hW
    exact ⟨v, hv, hv0, fun i => (h i).imp fun c hc' => hc' v hv⟩
  · obtain ⟨i, hi⟩ := not_forall.1 h
    haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.2 hW
    obtain ⟨c, hce⟩ := Module.End.exists_eigenvalue
      ((f i).restrict (p := W) (q := W) (hinv i) : Module.End ℂ W)
    obtain ⟨w, hw⟩ := hce.exists_hasEigenvector
    have hw1 : f i (w : M) = c • (w : M) := congrArg Subtype.val hw.apply_eq_smul
    have hw0 : (w : M) ≠ 0 := fun e => hw.2 (Subtype.ext e)
    have hlt : W ⊓ (f i).eigenspace c < W := by
      refine lt_of_le_of_ne inf_le_left fun e => hi ⟨c, fun x hx => ?_⟩
      rw [← e] at hx
      exact Module.End.mem_eigenspace_iff.1 hx.2
    have hne : W ⊓ (f i).eigenspace c ≠ ⊥ :=
      (Submodule.ne_bot_iff _).2 ⟨w, ⟨w.2, Module.End.mem_eigenspace_iff.2 hw1⟩, hw0⟩
    obtain ⟨v, hv, hv0, hall⟩ := ih _ (hn ▸ Submodule.finrank_lt_finrank_of_lt hlt)
      (W ⊓ (f i).eigenspace c) rfl hne (fun j x hx => by
        refine ⟨hinv j x hx.1, Module.End.mem_eigenspace_iff.2 ?_⟩
        have h1 : f i x = c • x := Module.End.mem_eigenspace_iff.1 hx.2
        have h2 : f i (f j x) = f j (f i x) := LinearMap.congr_fun (hc i j).eq x
        rw [h2, h1, map_smul])
    exact ⟨v, hv.1, hv0, hall⟩
