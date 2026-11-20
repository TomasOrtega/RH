import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

noncomputable section

namespace GlobalTheory.HoweR

/- English proof (translation)
Introduce `T _ _ V _ _ R S a C v hgen N hN hC hv`. Establish `key : ∀ s : Finset T, ∀ f : ∀ w, V w, (∀ w, w ∉ s → f w = v w) → PiTensorProduct.tprod ℂ f ∈ N`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`.

Introduce `f hf`. Establish `: f = v` using `funext fun w => hf w (Finset.notMem_empty w)`. Rewrite using `[this]`. Conclude with `hv`. Consider the case `insert w s hws ih`.

Introduce `f hf`. Set `K : Submodule ℂ (V w)` to `Submodule.comap ((PiTensorProduct.tprod ℂ (s := V)).toLinearMap f w) N`. Establish `hmem : ∀ x, x ∈ K ↔ PiTensorProduct.tprod ℂ (Function.update f w x) ∈ N`. Introduce `x`. Simplify using `[K, MultilinearMap.toLinearMap_apply]`.

Establish `hstab : ∀ Z, ∀ y ∈ K, a w Z y ∈ K`. Introduce `Z y hy`. Rewrite `hy`, the goal using `[hmem]`. Establish `h1` using `hN w Z _ hy`. Rewrite `h1` using `[actAt_apply, atPl, PiTensorProduct.map_tprod]`.

Use `h1 using 2` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Distinguish the cases in `h : i = w`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[Function.update_of_ne h]`. Establish `hvK : v w ∈ K`. Rewrite using `[hmem]`. Apply `ih` to reduce the goal to its premises. Introduce `u hu`.

Distinguish the cases in `h : u = w`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[Function.update_of_ne h]`. Conclude with `hf u (by simp [h, hu])`.

Establish `hCK : C w ≤ K`. Introduce `c hc`. Rewrite using `[hmem]`. Apply `hC` to reduce the goal to its premises. Apply `Submodule.subset_span` to reduce the goal to its premises.

Conclude with `⟨Function.update f w c, ⟨w, by simpa using hc⟩, rfl⟩`. Establish `hgK : genSub (a w) {v w} ≤ K`. Apply `sInf_le` to reduce the goal to its premises. Use `⟨?_, hstab⟩` and prove the remaining obligations. Simplify using `using hvK`.

Establish `htop : K = ⊤`. Rewrite using `[eq_top_iff, ← hgen w]`. Conclude with `sup_le hgK hCK`. Establish `: f w ∈ K` using `by rw [htop]; trivial`. Rewrite `this` using `[hmem, Function.update_eq_self]`.

Conclude with `this`. Establish `hall : ∀ f : ∀ w, V w, PiTensorProduct.tprod ℂ f ∈ N` using `fun f => key Finset.univ f (fun w hw => absurd (Finset.mem_univ w) hw)`. Rewrite using `[eq_top_iff, ← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]`. Introduce and unpack `_ ⟨f, rfl⟩`. Conclude with `hall f`.
-/
theorem tprod_cyclic_top : ∀ (T : Type) [Fintype T] [DecidableEq T] (V : T → Type) [∀ w, AddCommGroup (V w)] [∀ w, Module ℂ (V w)], ∀ (R S : T → ℕ) (a : ∀ w, Mat (R w) (S w) →ₗ[ℂ] Module.End ℂ (V w)) (C : ∀ w, Submodule ℂ (V w)) (v : ∀ w, V w), (∀ w, genSub (a w) {v w} ⊔ C w = ⊤) → ∀ N : Submodule ℂ (PiTensorProduct ℂ V), (∀ w, Stab (actAt w (a w)) N) → tensAny C ≤ N → PiTensorProduct.tprod ℂ v ∈ N → N = ⊤ := by
  intro T _ _ V _ _ R S a C v hgen N hN hC hv
  have key : ∀ s : Finset T, ∀ f : ∀ w, V w, (∀ w, w ∉ s → f w = v w) → PiTensorProduct.tprod ℂ f ∈ N := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro f hf
      have : f = v := funext fun w => hf w (Finset.notMem_empty w)
      rw [this]; exact hv
    | insert w s hws ih =>
      intro f hf
      let K : Submodule ℂ (V w) :=
        Submodule.comap ((PiTensorProduct.tprod ℂ (s := V)).toLinearMap f w) N
      have hmem : ∀ x, x ∈ K ↔ PiTensorProduct.tprod ℂ (Function.update f w x) ∈ N := by
        intro x; simp [K, MultilinearMap.toLinearMap_apply]
      have hstab : ∀ Z, ∀ y ∈ K, a w Z y ∈ K := by
        intro Z y hy
        rw [hmem] at hy ⊢
        have h1 := hN w Z _ hy
        rw [actAt_apply, atPl, PiTensorProduct.map_tprod] at h1
        convert h1 using 2
        funext i
        by_cases h : i = w
        · subst h; simp
        · simp [Function.update_of_ne h]
      have hvK : v w ∈ K := by
        rw [hmem]
        apply ih
        intro u hu
        by_cases h : u = w
        · subst h; simp
        · rw [Function.update_of_ne h]
          exact hf u (by simp [h, hu])
      have hCK : C w ≤ K := by
        intro c hc
        rw [hmem]
        apply hC
        apply Submodule.subset_span
        exact ⟨Function.update f w c, ⟨w, by simpa using hc⟩, rfl⟩
      have hgK : genSub (a w) {v w} ≤ K := by
        apply sInf_le
        refine ⟨?_, hstab⟩
        simpa using hvK
      have htop : K = ⊤ := by
        rw [eq_top_iff, ← hgen w]
        exact sup_le hgK hCK
      have : f w ∈ K := by rw [htop]; trivial
      rw [hmem, Function.update_eq_self] at this
      exact this
  have hall : ∀ f : ∀ w, V w, PiTensorProduct.tprod ℂ f ∈ N :=
    fun f => key Finset.univ f (fun w hw => absurd (Finset.mem_univ w) hw)
  rw [eq_top_iff, ← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
  rintro _ ⟨f, rfl⟩
  exact hall f

end GlobalTheory.HoweR
