import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CommonEigenvalue

/- English proof (translation)
Introduce `K M _ _ _ _ _ J T hT d`. Proceed by induction on `d using Nat.strong_induction_on with`. Consider the case `_ d ih`. Introduce `U hd hU hinv`. Distinguish the cases in `h : ∀ j, ∃ c : K, ∀ x ∈ U, T j x = c • x`.

Take `⟨v, hv, hv0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hU`. Use `⟨v, hv, hv0, fun j => ?_⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `h j`. Conclude with `⟨c, hc v hv⟩`. Rewrite `h` using `[not_forall]`.

Take `⟨i, hi⟩` from `h`. Use `haveI : Nontrivial U := Submodule.nontrivial_iff_ne_bot.mpr hU`. Take `⟨c, hc⟩` from `Module.End.exists_eigenvalue ((T i).restrict (hinv i) : Module.End K U)`. Take `⟨w, hw⟩` from `hc.exists_hasEigenvector`. Establish `hw1 : T i (w : M) = c • (w : M)`.

Establish `h1` using `congrArg Subtype.val hw.apply_eq_smul`. Simplify `h1` using `[LinearMap.restrict_apply]`. Establish `hw0 : (w : M) ≠ 0` using `fun h0 => hw.2 (Subtype.ext h0)`. Establish `hlt : U ⊓ (T i).eigenspace c < U`. Use `lt_of_le_of_ne inf_le_left fun heq => hi ⟨c, fun x hx => ?_⟩` and prove the remaining obligations.

Rewrite `hx` using `[← heq]`. Conclude with `Module.End.mem_eigenspace_iff.mp hx.2`. Establish `hne : U ⊓ (T i).eigenspace c ≠ ⊥`. Introduce `h0`. Establish `hm : (w : M) ∈ U ⊓ (T i).eigenspace c` using `⟨w.2, Module.End.mem_eigenspace_iff.mpr hw1⟩`.

Rewrite `hm` using `[h0]`. Conclude with `hw0 ((Submodule.mem_bot K).mp hm)`. Establish `hst : ∀ j, ∀ x ∈ U ⊓ (T i).eigenspace c, T j x ∈ U ⊓ (T i).eigenspace c`. Introduce `j x hx`. Use `⟨hinv j x hx.1, Module.End.mem_eigenspace_iff.mpr ?_⟩` and prove the remaining obligations.

Establish `h2 : T i x = c • x` using `Module.End.mem_eigenspace_iff.mp hx.2`. Establish `h3` using `LinearMap.congr_fun (hT i j) x`. Simplify using `only [Module.End.mul_apply] at h3`. Rewrite using `[h3, h2, map_smul]`. Take `⟨v, hv, hv0, hvj⟩` from `ih _ (hd ▸ Submodule.finrank_lt_finrank_of_lt hlt) _ rfl hne hst`.

Conclude with `⟨v, hv.1, hv0, hvj⟩`.
-/
theorem UpperTheory.Reformulated.B.SimultaneousEigenvectorInvariantSubspace.simEig :
    ∀ {K M : Type} [inst : Field K] [IsAlgClosed K] [inst_2 : AddCommGroup M]
    [inst_3 : _root_.Module K M] [FiniteDimensional K M] {J : Type} (T : J → Module.End K M),
    (∀ (i j : J), T i * T j = T j * T i) →
      ∀ (d : ℕ) (U : Submodule K M),
        Module.finrank K ↥U = d →
          U ≠ ⊥ →
            (∀ (j : J), ∀ x ∈ U, (T j : M → M) x ∈ U) →
              ∃ v ∈ U, v ≠ (0 : M) ∧ ∀ (j : J), ∃ (c : K), (T j : M → M) v = c • v := by
  intro K M _ _ _ _ _ J T hT d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro U hd hU hinv
    by_cases h : ∀ j, ∃ c : K, ∀ x ∈ U, T j x = c • x
    · obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
      refine ⟨v, hv, hv0, fun j => ?_⟩
      obtain ⟨c, hc⟩ := h j
      exact ⟨c, hc v hv⟩
    · rw [not_forall] at h
      obtain ⟨i, hi⟩ := h
      haveI : Nontrivial U := Submodule.nontrivial_iff_ne_bot.mpr hU
      obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue ((T i).restrict (hinv i) : Module.End K U)
      obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
      have hw1 : T i (w : M) = c • (w : M) := by
        have h1 := congrArg Subtype.val hw.apply_eq_smul
        simpa [LinearMap.restrict_apply] using h1
      have hw0 : (w : M) ≠ 0 := fun h0 => hw.2 (Subtype.ext h0)
      have hlt : U ⊓ (T i).eigenspace c < U := by
        refine lt_of_le_of_ne inf_le_left fun heq => hi ⟨c, fun x hx => ?_⟩
        rw [← heq] at hx
        exact Module.End.mem_eigenspace_iff.mp hx.2
      have hne : U ⊓ (T i).eigenspace c ≠ ⊥ := by
        intro h0
        have hm : (w : M) ∈ U ⊓ (T i).eigenspace c :=
          ⟨w.2, Module.End.mem_eigenspace_iff.mpr hw1⟩
        rw [h0] at hm
        exact hw0 ((Submodule.mem_bot K).mp hm)
      have hst : ∀ j, ∀ x ∈ U ⊓ (T i).eigenspace c, T j x ∈ U ⊓ (T i).eigenspace c := by
        intro j x hx
        refine ⟨hinv j x hx.1, Module.End.mem_eigenspace_iff.mpr ?_⟩
        have h2 : T i x = c • x := Module.End.mem_eigenspace_iff.mp hx.2
        have h3 := LinearMap.congr_fun (hT i j) x
        simp only [Module.End.mul_apply] at h3
        rw [h3, h2, map_smul]
      obtain ⟨v, hv, hv0, hvj⟩ :=
        ih _ (hd ▸ Submodule.finrank_lt_finrank_of_lt hlt) _ rfl hne hst
      exact ⟨v, hv.1, hv0, hvj⟩
