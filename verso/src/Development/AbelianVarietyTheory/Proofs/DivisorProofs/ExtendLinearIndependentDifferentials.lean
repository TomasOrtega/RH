import Mathlib
open scoped TensorProduct Polynomial

namespace GlobalTheory

/- English proof (translation)
Introduce `R B K _ _ _ _ _ _ d ι x hd hx`. Use `set g : B → K ⊗[B] Ω[B⁄R] := fun b => (1 : K) ⊗ₜ[B] KaehlerDifferential.D R B b with hg`. Establish `hspan : Submodule.span K (Set.range g) = ⊤`. Rewrite using `[eq_top_iff]`. Introduce and unpack `z -`.

Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => exact zero_mem _`. Consider the case `tmul k ω`. Establish `h1 : (1 : K) ⊗ₜ[B] ω ∈ Submodule.span K (Set.range g)`. Establish `hω : ω ∈ Submodule.span B (Set.range (KaehlerDifferential.D R B))`.

Rewrite using `[KaehlerDifferential.span_range_derivation]`. Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hω using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨b, rfl⟩` from `hy`.

Conclude with `Submodule.subset_span ⟨b, rfl⟩`. Consider the case `zero => simp`. Consider the case `add y z _ _ hy hz => rw [TensorProduct.tmul_add]`. Conclude with `add_mem hy hz`. Consider the case `smul c y _ hy`.

Rewrite using `[TensorProduct.tmul_smul, ← algebraMap_smul K c]`. Conclude with `Submodule.smul_mem _ _ hy`. Establish `: k ⊗ₜ[B] ω = k • ((1 : K) ⊗ₜ[B] ω)`. Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Rewrite using `[this]`.

Conclude with `Submodule.smul_mem _ _ h1`. Consider the case `add a b ha hb => exact add_mem ha hb`. Establish `hxinj : Function.Injective x` using `fun i j h => hx.injective (by simp [h])`. Establish `hs : LinearIndepOn K g (Set.range x)` using `(linearIndepOn_range_iff hxinj g).2 hx`. Take `⟨b, -, hsb, htb, hli⟩` from `exists_linearIndepOn_extension hs (Set.subset_univ _)`.

Establish `hspanb : ⊤ ≤ Submodule.span K (Set.range (fun y : b => g y))`. Rewrite using `[← hspan, Submodule.span_le]`. Introduce and unpack `_ ⟨c, rfl⟩`. Use `htb ⟨c, Set.mem_univ _, rfl⟩` as an intermediate fact. Rewrite `this` using `[Set.image_eq_range]`. Then use the resulting hypothesis.

Set `bas` to `Module.Basis.mk hli hspanb`. Use `haveI : Finite b := Module.Finite.finite_basis bas`. Establish `hcard : Nat.card b = d`. Rewrite using `[← hd, Module.finrank_eq_nat_card_basis bas]`. Set `eq : b ≃ Fin d` to `Finite.equivFinOfCardEq hcard`.

Use `⟨fun a => (eq.symm a).1, ⟨fun i => eq ⟨x i, hsb ⟨i, rfl⟩⟩, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `i j h`. Use `eq.injective h` as an intermediate fact. Conclude with `hxinj (congrArg Subtype.val this)`. Introduce `i show ((eq.symm (eq ⟨x i, hsb ⟨i, rfl⟩⟩)) : B) = x i`.

Rewrite using `[Equiv.symm_apply_apply]`. Conclude with `hli.comp eq.symm eq.symm.injective`.
-/
theorem kaehler_baseChange_independent_extend :
    ∀ (R B K : Type) [CommRing R] [CommRing B] [Field K] [Algebra R B] [Algebra B K]
      [Algebra.FiniteType R B] (d : ℕ) (ι : Type) (x : ι → B),
      Module.finrank K (K ⊗[B] Ω[B⁄R]) = d →
      LinearIndependent K (fun i => (1 : K) ⊗ₜ[B] KaehlerDifferential.D R B (x i)) →
      ∃ (t : Fin d → B) (e : ι ↪ Fin d), (∀ i, t (e i) = x i) ∧
        LinearIndependent K (fun a => (1 : K) ⊗ₜ[B] KaehlerDifferential.D R B (t a)) := by
  intro R B K _ _ _ _ _ _ d ι x hd hx
  set g : B → K ⊗[B] Ω[B⁄R] := fun b => (1 : K) ⊗ₜ[B] KaehlerDifferential.D R B b with hg
  have hspan : Submodule.span K (Set.range g) = ⊤ := by
    rw [eq_top_iff]
    rintro z -
    induction z using TensorProduct.induction_on with
    | zero => exact zero_mem _
    | tmul k ω =>
      have h1 : (1 : K) ⊗ₜ[B] ω ∈ Submodule.span K (Set.range g) := by
        have hω : ω ∈ Submodule.span B (Set.range (KaehlerDifferential.D R B)) := by
          rw [KaehlerDifferential.span_range_derivation]; trivial
        induction hω using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨b, rfl⟩ := hy
          exact Submodule.subset_span ⟨b, rfl⟩
        | zero => simp
        | add y z _ _ hy hz => rw [TensorProduct.tmul_add]; exact add_mem hy hz
        | smul c y _ hy =>
          rw [TensorProduct.tmul_smul, ← algebraMap_smul K c]
          exact Submodule.smul_mem _ _ hy
      have : k ⊗ₜ[B] ω = k • ((1 : K) ⊗ₜ[B] ω) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this]
      exact Submodule.smul_mem _ _ h1
    | add a b ha hb => exact add_mem ha hb
  have hxinj : Function.Injective x := fun i j h => hx.injective (by simp [h])
  have hs : LinearIndepOn K g (Set.range x) := (linearIndepOn_range_iff hxinj g).2 hx
  obtain ⟨b, -, hsb, htb, hli⟩ := exists_linearIndepOn_extension hs (Set.subset_univ _)
  have hspanb : ⊤ ≤ Submodule.span K (Set.range (fun y : b => g y)) := by
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨c, rfl⟩
    have := htb ⟨c, Set.mem_univ _, rfl⟩
    rwa [Set.image_eq_range] at this
  let bas := Module.Basis.mk hli hspanb
  haveI : Finite b := Module.Finite.finite_basis bas
  have hcard : Nat.card b = d := by
    rw [← hd, Module.finrank_eq_nat_card_basis bas]
  let eq : b ≃ Fin d := Finite.equivFinOfCardEq hcard
  refine ⟨fun a => (eq.symm a).1, ⟨fun i => eq ⟨x i, hsb ⟨i, rfl⟩⟩, ?_⟩, ?_, ?_⟩
  · intro i j h
    have := eq.injective h
    exact hxinj (congrArg Subtype.val this)
  · intro i
    show ((eq.symm (eq ⟨x i, hsb ⟨i, rfl⟩⟩)) : B) = x i
    rw [Equiv.symm_apply_apply]
  · exact hli.comp eq.symm eq.symm.injective

end GlobalTheory
