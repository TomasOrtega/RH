import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.TopNilDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.GrLocal
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoEvLow

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

/- English proof (translation)
Rewrite using `[← Finset.univ_prod_mulSingle g]`. Use `Submonoid.prod_mem _ fun s _ => ?_` and prove the remaining obligations. Establish `hs : Pi.mulSingle s (g s) = (Pi.mulSingle s (Multiplicative.ofAdd (1 : ZMod (n s))) : ∀ s, Multiplicative (ZMod (n s))) ^ (Multiplicative.toAdd (g s)).val`. Rewrite using `[← Pi.mulSingle_pow, ← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]`. Both sides reduce to the same expression.

Rewrite using `[hs]`. Conclude with `Submonoid.pow_mem _ (h s) _`.
-/
private theorem grEx_gen {σ : Type} [Fintype σ] [DecidableEq σ] (n : σ → ℕ) [∀ s, NeZero (n s)]
    (S : Submonoid (∀ s, Multiplicative (ZMod (n s))))
    (h : ∀ s : σ, (Pi.mulSingle s (Multiplicative.ofAdd (1 : ZMod (n s))) : ∀ s, Multiplicative (ZMod (n s))) ∈ S)
    (g : ∀ s, Multiplicative (ZMod (n s))) : g ∈ S := by
  rw [← Finset.univ_prod_mulSingle g]
  refine Submonoid.prod_mem _ fun s _ => ?_
  have hs : Pi.mulSingle s (g s) =
      (Pi.mulSingle s (Multiplicative.ofAdd (1 : ZMod (n s))) : ∀ s, Multiplicative (ZMod (n s))) ^
        (Multiplicative.toAdd (g s)).val := by
    rw [← Pi.mulSingle_pow, ← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
    rfl
  rw [hs]
  exact Submonoid.pow_mem _ (h s) _

/- English proof (translation)
Introduce `Λ _ _ _ _ l hl hlm σ _ _ e`. Use `haveI : Fact l.Prime := ⟨hl⟩`. Use `haveI hNZ : ∀ s, NeZero (l ^ e s) := fun s => ⟨pow_ne_zero _ hl.ne_zero⟩`. Establish `hpg : IsPGroup l (∀ s, Multiplicative (ZMod (l ^ e s)))`. Apply `IsPGroup.of_card (n := ∑ s, e s)` to reduce the goal to its premises.

Rewrite using `[Nat.card_pi, ← Finset.prod_pow_eq_pow_sum]`. Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]`. Take `⟨hloc, hmax, -, -⟩` from `UpperTheory.V.CF.grLocal l Λ (∀ s, Multiplicative (ZMod (l ^ e s))) hlm hpg`. Use `haveI := hloc`.

Use `haveI hCOΛ : UpperTheory.V.Alg.IsCO Λ Λ := inferInstance`. Use `haveI hCO : UpperTheory.V.Alg.IsCO Λ (MonoidAlgebra Λ (∀ s, Multiplicative (ZMod (l ^ e s)))) := by`. Apply `UpperTheory.V.Alg.co_finite Λ Λ` to reduce the goal to its premises. Introduce `x`. Use `⟨UpperTheory.V.CF.aug Λ _ x, ?_⟩` and prove the remaining obligations.

Rewrite using `[hmax, Ideal.mem_comap, map_sub, AlgHom.commutes]`. Simplify using the standard rewrite rules. Use `set gen : σ → MonoidAlgebra Λ (∀ s, Multiplicative (ZMod (l ^ e s))) := fun s => MonoidAlgebra.of Λ (∀ s, Multiplicative (ZMod (l ^ e s))) (Pi.mulSingle s (Multiplicative.ofAdd (1 : ZMod (l ^ e s)))) with hgen`. Establish `haug_of : ∀ g, UpperTheory.V.CF.aug Λ (∀ s, Multiplicative (ZMod (l ^ e s))) (MonoidAlgebra.of Λ _ g) = 1`. Introduce `g`.

Simplify using `[UpperTheory.V.CF.aug]`. Establish `hamem : ∀ s, gen s - 1 ∈ IsLocalRing.maximalIdeal (MonoidAlgebra Λ (∀ s, Multiplicative (ZMod (l ^ e s))))`. Introduce `s`. Rewrite using `[hmax, Ideal.mem_comap, map_sub, map_one, hgen, haug_of, sub_self]`. Conclude with `Ideal.zero_mem _`.

Take `⟨φ, ⟨hφC, hφX⟩, -⟩` from `UpperTheory.V.Alg.co_ev Λ Λ (MonoidAlgebra Λ (∀ s, Multiplicative (ZMod (l ^ e s)))) σ (Algebra.ofId Λ _) (fun s => gen s - 1) hamem`. Establish `hφ1 : ∀ s, φ (1 + MvPowerSeries.X s) = gen s`. Introduce `s`. Rewrite using `[map_add, map_one, hφX]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hofrange : ∀ g, MonoidAlgebra.of Λ _ g ∈ φ.range`. Introduce `g`. Set `S : Submonoid (∀ s, Multiplicative (ZMod (l ^ e s)))` to `{ carrier := {g | MonoidAlgebra.of Λ _ g ∈ φ.range} mul_mem' := by`. Introduce `a b ha hb`. Simplify using `only [Set.mem_setOf_eq, map_mul] at *`.

Conclude with `Subalgebra.mul_mem _ ha hb`. Use the proof step `one_mem' := by`. Simplify using `only [Set.mem_setOf_eq, map_one]`. Conclude with `Subalgebra.one_mem _ }`. Conclude with `grEx_gen (fun s => l ^ e s) S (fun s => ⟨1 + MvPowerSeries.X s, hφ1 s⟩) g`.

Establish `hsurj : Function.Surjective φ`. Introduce `y`. It suffices to establish `y ∈ φ.range by simpa using this`. Proceed by induction on `y using MonoidAlgebra.induction_on with`. Consider the case `of g => exact hofrange g`.

Consider the case `add f g hf hg => exact Subalgebra.add_mem _ hf hg`. Consider the case `smul r f hf => exact Subalgebra.smul_mem _ hf r`. Use `⟨φ, hφ1, hsurj, hloc, ?_⟩` and prove the remaining obligations. Establish `hker` using `(UpperTheory.V.CF.augKer Λ (∀ s, Multiplicative (ZMod (l ^ e s)))).1`. Express the relevant statement in the definitionally equal form `_ = RingHom.ker (UpperTheory.V.CF.aug Λ _)`.

Rewrite using `[hker, Ideal.map_span, ← Set.range_comp]`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨s, rfl⟩`. Apply `Ideal.subset_span` to reduce the goal to its premises.

Conclude with `⟨Pi.mulSingle s (Multiplicative.ofAdd (1 : ZMod (l ^ e s))), (hφX s).symm⟩`. Rewrite using `[UpperTheory.V.CF.augIdeal, Ideal.span_le]`. Introduce and unpack `_ ⟨g, rfl⟩`. Use `set J := Ideal.span (Set.range (⇑φ ∘ MvPowerSeries.X))`. Set `S : Submonoid (∀ s, Multiplicative (ZMod (l ^ e s)))` to `{ carrier := {g | MonoidAlgebra.of Λ _ g - 1 ∈ J} mul_mem' := by`.

Introduce `a b ha hb`. Simplify using `only [Set.mem_setOf_eq, map_mul] at *`. Establish `: MonoidAlgebra.of Λ _ a * MonoidAlgebra.of Λ _ b - 1 = (MonoidAlgebra.of Λ _ a - 1) * MonoidAlgebra.of Λ _ b + (MonoidAlgebra.of Λ _ b - 1)` using `by ring`. Rewrite using `[this]`. Conclude with `J.add_mem (J.mul_mem_right _ ha) hb`.

Use the proof step `one_mem' := by`. Simplify using `only [Set.mem_setOf_eq, map_one, sub_self]`. Conclude with `J.zero_mem }`. Use `grEx_gen (fun s => l ^ e s) S (fun s => ?_) g` and prove the remaining obligations. Use `show gen s - 1 ∈ J`.

Rewrite using `[← hφX]`. Conclude with `Ideal.subset_span ⟨s, rfl⟩`.
-/
theorem UpperTheory.V.AlgebraTools.exists_groupRing_surj :
    ∀ (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (IsLocalRing.maximalIdeal Λ) Λ] (l : ℕ), l.Prime → (l : Λ) ∈ IsLocalRing.maximalIdeal Λ → ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (e : σ → ℕ),
      ∃ φ : MvPowerSeries σ Λ →ₐ[Λ] MonoidAlgebra Λ (∀ s, Multiplicative (ZMod (l ^ e s))), (∀ s : σ, φ (1 + MvPowerSeries.X s) = MonoidAlgebra.of Λ (∀ s, Multiplicative (ZMod (l ^ e s))) (Pi.mulSingle s (Multiplicative.ofAdd (1 : ZMod (l ^ e s))))) ∧ Function.Surjective φ ∧
        IsLocalRing (MonoidAlgebra Λ (∀ s, Multiplicative (ZMod (l ^ e s)))) ∧
        (Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ Λ))).map φ =
          RingHom.ker (MonoidAlgebra.lift Λ Λ (∀ s, Multiplicative (ZMod (l ^ e s))) 1) := by
  intro Λ _ _ _ _ l hl hlm σ _ _ e
  haveI : Fact l.Prime := ⟨hl⟩
  haveI hNZ : ∀ s, NeZero (l ^ e s) := fun s => ⟨pow_ne_zero _ hl.ne_zero⟩
  have hpg : IsPGroup l (∀ s, Multiplicative (ZMod (l ^ e s))) := by
    apply IsPGroup.of_card (n := ∑ s, e s)
    rw [Nat.card_pi, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  obtain ⟨hloc, hmax, -, -⟩ := UpperTheory.V.CF.grLocal l Λ (∀ s, Multiplicative (ZMod (l ^ e s))) hlm hpg
  haveI := hloc
  haveI hCOΛ : UpperTheory.V.Alg.IsCO Λ Λ := inferInstance
  haveI hCO : UpperTheory.V.Alg.IsCO Λ (MonoidAlgebra Λ (∀ s, Multiplicative (ZMod (l ^ e s)))) := by
    apply UpperTheory.V.Alg.co_finite Λ Λ
    intro x
    refine ⟨UpperTheory.V.CF.aug Λ _ x, ?_⟩
    rw [hmax, Ideal.mem_comap, map_sub, AlgHom.commutes]
    simp
  set gen : σ → MonoidAlgebra Λ (∀ s, Multiplicative (ZMod (l ^ e s))) := fun s =>
    MonoidAlgebra.of Λ (∀ s, Multiplicative (ZMod (l ^ e s)))
      (Pi.mulSingle s (Multiplicative.ofAdd (1 : ZMod (l ^ e s)))) with hgen
  have haug_of : ∀ g, UpperTheory.V.CF.aug Λ (∀ s, Multiplicative (ZMod (l ^ e s)))
      (MonoidAlgebra.of Λ _ g) = 1 := by
    intro g
    simp [UpperTheory.V.CF.aug]
  have hamem : ∀ s, gen s - 1 ∈ IsLocalRing.maximalIdeal (MonoidAlgebra Λ (∀ s, Multiplicative (ZMod (l ^ e s)))) := by
    intro s
    rw [hmax, Ideal.mem_comap, map_sub, map_one, hgen, haug_of, sub_self]
    exact Ideal.zero_mem _
  obtain ⟨φ, ⟨hφC, hφX⟩, -⟩ := UpperTheory.V.Alg.co_ev Λ Λ
    (MonoidAlgebra Λ (∀ s, Multiplicative (ZMod (l ^ e s)))) σ
    (Algebra.ofId Λ _) (fun s => gen s - 1) hamem
  have hφ1 : ∀ s, φ (1 + MvPowerSeries.X s) = gen s := by
    intro s
    rw [map_add, map_one, hφX]
    ring
  have hofrange : ∀ g, MonoidAlgebra.of Λ _ g ∈ φ.range := by
    intro g
    let S : Submonoid (∀ s, Multiplicative (ZMod (l ^ e s))) :=
      { carrier := {g | MonoidAlgebra.of Λ _ g ∈ φ.range}
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_setOf_eq, map_mul] at *
          exact Subalgebra.mul_mem _ ha hb
        one_mem' := by
          simp only [Set.mem_setOf_eq, map_one]
          exact Subalgebra.one_mem _ }
    exact grEx_gen (fun s => l ^ e s) S (fun s => ⟨1 + MvPowerSeries.X s, hφ1 s⟩) g
  have hsurj : Function.Surjective φ := by
    intro y
    suffices y ∈ φ.range by simpa using this
    induction y using MonoidAlgebra.induction_on with
    | of g => exact hofrange g
    | add f g hf hg => exact Subalgebra.add_mem _ hf hg
    | smul r f hf => exact Subalgebra.smul_mem _ hf r
  refine ⟨φ, hφ1, hsurj, hloc, ?_⟩
  have hker := (UpperTheory.V.CF.augKer Λ (∀ s, Multiplicative (ZMod (l ^ e s)))).1
  change _ = RingHom.ker (UpperTheory.V.CF.aug Λ _)
  rw [hker, Ideal.map_span, ← Set.range_comp]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨s, rfl⟩
    apply Ideal.subset_span
    exact ⟨Pi.mulSingle s (Multiplicative.ofAdd (1 : ZMod (l ^ e s))), (hφX s).symm⟩
  · rw [UpperTheory.V.CF.augIdeal, Ideal.span_le]
    rintro _ ⟨g, rfl⟩
    set J := Ideal.span (Set.range (⇑φ ∘ MvPowerSeries.X))
    let S : Submonoid (∀ s, Multiplicative (ZMod (l ^ e s))) :=
      { carrier := {g | MonoidAlgebra.of Λ _ g - 1 ∈ J}
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_setOf_eq, map_mul] at *
          have : MonoidAlgebra.of Λ _ a * MonoidAlgebra.of Λ _ b - 1 =
              (MonoidAlgebra.of Λ _ a - 1) * MonoidAlgebra.of Λ _ b + (MonoidAlgebra.of Λ _ b - 1) := by ring
          rw [this]
          exact J.add_mem (J.mul_mem_right _ ha) hb
        one_mem' := by
          simp only [Set.mem_setOf_eq, map_one, sub_self]
          exact J.zero_mem }
    refine grEx_gen (fun s => l ^ e s) S (fun s => ?_) g
    show gen s - 1 ∈ J
    rw [← hφX]
    exact Ideal.subset_span ⟨s, rfl⟩
