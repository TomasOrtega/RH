import Mathlib

namespace GlobalTheory.CommonEigenvectorExistenceInertiaEigenvalues

open Module

/- English proof (translation)
Introduce `d`. Proceed by induction on `d using Nat.strong_induction_on with`. Consider the case `_ d ih`. Introduce `W hd hW hinv`. Distinguish the cases in `hs : ∀ i, ∃ c : k, ∀ w ∈ W, f i w = c • w`.

Take `⟨x, hx, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hW`. Conclude with `⟨x, hx, hx0, fun i => let ⟨c, hc⟩ := hs i; ⟨c, hc x hx⟩⟩`. Use `push_neg at hs`. Take `⟨i, hi⟩` from `hs`. Set `g : Module.End k W` to `(f i).restrict (fun w hw => hinv i w hw)`.

Use `haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW`. Take `⟨c, hc'⟩` from `Module.End.exists_eigenvalue g`. Take `⟨v, hv⟩` from `hc'.exists_hasEigenvector`. Establish `hgv : g v = c • v` using `hv.apply_eq_smul`. Establish `hv0 : v ≠ 0` using `hv.2`.

Use `set W' : Submodule k V := W ⊓ Module.End.eigenspace (f i) c with hW'`. Establish `hvW' : (v : V) ∈ W'`. Use `⟨v.2, ?_⟩` and prove the remaining obligations. Rewrite using `[SetLike.mem_coe, Module.End.mem_eigenspace_iff]`. Use `congrArg Subtype.val hgv` as an intermediate fact.

Simplify `this` using `[g]`. Establish `hW'ne : W' ≠ ⊥`. Introduce `h`. Rewrite `hvW'` using `[h, Submodule.mem_bot]`. Conclude with `hv0 (Subtype.ext hvW')`.

Establish `hlt : W' < W`. Use `lt_of_le_of_ne inf_le_left ?_` and prove the remaining obligations. Introduce `h`. Take `⟨w, hw, hne⟩` from `hi c`. Establish `: w ∈ W'` using `h ▸ hw`.

Conclude with `hne ((Module.End.mem_eigenspace_iff).mp this.2)`. Establish `hdlt : Module.finrank k W' < d` using `hd ▸ Submodule.finrank_lt_finrank_of_lt hlt`. Establish `hinv' : ∀ j, ∀ w ∈ W', (f j : V → V) w ∈ W'`. Introduce `j w hw`. Use `⟨hinv j w hw.1, ?_⟩` and prove the remaining obligations.

Rewrite using `[SetLike.mem_coe, Module.End.mem_eigenspace_iff]`. Establish `h1 : f i w = c • w` using `(Module.End.mem_eigenspace_iff).mp hw.2`. Establish `h2` using `congrArg (fun F : Module.End k V => F w) (hcomm i j)`. Simplify using `only [Module.End.mul_apply] at h2`. Rewrite using `[h2, h1, map_smul]`.

Take `⟨x, hx, hx0, hxe⟩` from `ih _ hdlt W' rfl hW'ne hinv'`. Conclude with `⟨x, hx.1, hx0, hxe⟩`.
-/
theorem exists_common_eigenvector {k ι V : Type} [Field k] [IsAlgClosed k] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] (f : ι → Module.End k V)
    (hcomm : ∀ i j, f i * f j = f j * f i) :
    ∀ (d : ℕ) (W : Submodule k V), Module.finrank k W = d → W ≠ ⊥ →
      (∀ i, ∀ w ∈ W, (f i : V → V) w ∈ W) →
        ∃ x ∈ W, x ≠ (0 : V) ∧ ∀ i, ∃ c : k, (f i : V → V) x = c • x := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro W hd hW hinv
  by_cases hs : ∀ i, ∃ c : k, ∀ w ∈ W, f i w = c • w
  · obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
    exact ⟨x, hx, hx0, fun i => let ⟨c, hc⟩ := hs i; ⟨c, hc x hx⟩⟩
  · push_neg at hs
    obtain ⟨i, hi⟩ := hs
    let g : Module.End k W := (f i).restrict (fun w hw => hinv i w hw)
    haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
    obtain ⟨c, hc'⟩ := Module.End.exists_eigenvalue g
    obtain ⟨v, hv⟩ := hc'.exists_hasEigenvector
    have hgv : g v = c • v := hv.apply_eq_smul
    have hv0 : v ≠ 0 := hv.2
    set W' : Submodule k V := W ⊓ Module.End.eigenspace (f i) c with hW'
    have hvW' : (v : V) ∈ W' := by
      refine ⟨v.2, ?_⟩
      rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff]
      have := congrArg Subtype.val hgv
      simpa [g] using this
    have hW'ne : W' ≠ ⊥ := by
      intro h
      rw [h, Submodule.mem_bot] at hvW'
      exact hv0 (Subtype.ext hvW')
    have hlt : W' < W := by
      refine lt_of_le_of_ne inf_le_left ?_
      intro h
      obtain ⟨w, hw, hne⟩ := hi c
      have : w ∈ W' := h ▸ hw
      exact hne ((Module.End.mem_eigenspace_iff).mp this.2)
    have hdlt : Module.finrank k W' < d := hd ▸ Submodule.finrank_lt_finrank_of_lt hlt
    have hinv' : ∀ j, ∀ w ∈ W', (f j : V → V) w ∈ W' := by
      intro j w hw
      refine ⟨hinv j w hw.1, ?_⟩
      rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff]
      have h1 : f i w = c • w := (Module.End.mem_eigenspace_iff).mp hw.2
      have h2 := congrArg (fun F : Module.End k V => F w) (hcomm i j)
      simp only [Module.End.mul_apply] at h2
      rw [h2, h1, map_smul]
    obtain ⟨x, hx, hx0, hxe⟩ := ih _ hdlt W' rfl hW'ne hinv'
    exact ⟨x, hx.1, hx0, hxe⟩

/- English proof (translation)
Introduce `f hc` and use `exists_common_eigenvector f hc`.
-/
theorem target : ∀ {k ι V : Type} [inst : Field k] [IsAlgClosed k] [inst_2 : AddCommGroup V] [inst_3 : Module k V] [FiniteDimensional k V] (f : ι → Module.End k V), (∀ (i j : ι), f i * f j = f j * f i) → ∀ (d : ℕ) (W : Submodule k V), Module.finrank k ↥W = d → W ≠ ⊥ → (∀ (i : ι), ∀ w ∈ W, (f i : V → V) w ∈ W) → ∃ x ∈ W, x ≠ (0 : V) ∧ ∀ (i : ι), ∃ (c : k), (f i : V → V) x = c • x :=
  fun f hc => exists_common_eigenvector f hc

end GlobalTheory.CommonEigenvectorExistenceInertiaEigenvalues
