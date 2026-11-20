import Mathlib

namespace GlobalTheory

open PowerSeries

/- English proof (translation)
Use `set p : Submodule (PowerSeries O) M := Ideal.span {(PowerSeries.X : PowerSeries O)} • (⊤ : Submodule (PowerSeries O) M) with hp`. Establish `memp : ∀ m : M, m ∈ p ↔ ∃ y : M, m = (PowerSeries.X : PowerSeries O) • y`. Introduce `m`. Rewrite using `[hp, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, -, hy⟩`. Conclude with `⟨y, hy.symm⟩`. Introduce and unpack `⟨y, hy⟩`. Conclude with `⟨y, Submodule.mem_top, hy.symm⟩`. Establish `hsmul : ∀ (c : O) (m : M), c • m = (PowerSeries.C c : PowerSeries O) • m`.

Introduce `c m`. Rewrite using `[← IsScalarTower.algebraMap_smul (PowerSeries O) c m, PowerSeries.algebraMap_apply]`. Simplify using the standard rewrite rules. Establish `hdec : ∀ r : PowerSeries O, ∃ s : PowerSeries O, r = PowerSeries.C (PowerSeries.constantCoeff r) + PowerSeries.X * s`. Introduce `r`.

Choose the witnesses or unpack the hypotheses as in `⟨s, hs⟩ : (PowerSeries.X : PowerSeries O) ∣ r - PowerSeries.C (PowerSeries.constantCoeff r) := by`. Rewrite using `[PowerSeries.X_dvd_iff]`. Simplify using the standard rewrite rules. Conclude with `⟨s, by rw [← hs]; ring⟩`. Establish `hN : ∀ (r : PowerSeries O) (y : M ⧸ p), r • y = (PowerSeries.constantCoeff r) • y`.

Introduce `r y`. Take `⟨m, rfl⟩` from `Submodule.Quotient.mk_surjective p y`. Take `⟨s, hs⟩` from `hdec r`. Rewrite using `[← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, memp]`. Establish `e1 : r • m = (PowerSeries.C (PowerSeries.constantCoeff r) : PowerSeries O) • m + (PowerSeries.X : PowerSeries O) • (s • m)` using `by conv_lhs => rw [hs]`.

Rewrite using `[add_smul, mul_smul]`. Use `⟨s • m, ?_⟩` and prove the remaining obligations. Rewrite using `[e1, hsmul]`. Normalize the expressions using the abelian group laws. Establish `hfin : Module.Finite O (M ⧸ p)`.

Take `⟨T, hT'⟩` from `Module.finite_def.mp (inferInstance : Module.Finite (PowerSeries O) (M ⧸ p))`. Use `⟨⟨T, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[eq_top_iff]`. Introduce and unpack `y -`. Establish `hy : y ∈ Submodule.span (PowerSeries O) (T : Set (M ⧸ p))`.

Rewrite using `[hT']`. Conclude with `Submodule.mem_top`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx => exact Submodule.subset_span hx`. Consider the case `zero => exact zero_mem _`.

Consider the case `add x y _ _ hx hy => exact add_mem hx hy`. Consider the case `smul r x _ hx`. Rewrite using `[hN]`. Conclude with `Submodule.smul_mem _ _ hx`. Establish `htf : Module.IsTorsionFree O (M ⧸ p)`.

Use `Module.IsTorsionFree.of_smul_eq_zero fun c y hcy => ?_` and prove the remaining obligations. Take `⟨m, rfl⟩` from `Submodule.Quotient.mk_surjective p y`. Distinguish the cases in `hc : c = 0`. Conclude with `Or.inl hc`. Use `right`.

Rewrite `hcy` using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, memp, hsmul c m]`. Rewrite using `[Submodule.Quotient.mk_eq_zero, memp]`. Conclude with `hT c m hc hcy`. Set `b` to `Module.Free.chooseBasis O (M ⧸ p)`. Use `choose e he using fun i => Submodule.Quotient.mk_surjective p (b i)`.

Establish `hspan : (⊤ : Submodule (PowerSeries O) M) ≤ Submodule.span (PowerSeries O) (Set.range e)`. Use `Submodule.le_of_le_smul_of_le_jacobson_bot (I := Ideal.span {PowerSeries.X}) (Module.finite_def.mp inferInstance) ?_ ?_` and prove the remaining obligations. Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ rfl`. Express the relevant statement in the definitionally equal form `PowerSeries.X ∈ Ideal.jacobson (⊥ : Ideal (PowerSeries O))`.

Rewrite using `[Ideal.mem_jacobson_bot]`. Introduce `y`. Rewrite using `[PowerSeries.isUnit_iff_constantCoeff]`. Simplify using the standard rewrite rules. Introduce `m _ set c := b.repr (Submodule.Quotient.mk m)`.

Establish `h2 : m - ∑ i, c i • e i ∈ p`. Rewrite using `[← Submodule.Quotient.eq, ← Submodule.mkQ_apply p (∑ i, c i • e i), map_sum]`. Simplify using `only [Submodule.mkQ_apply, Submodule.Quotient.mk_smul, he]`. Conclude with `(b.sum_repr _).symm`. Rewrite using `[Submodule.mem_sup]`.

Use `⟨∑ i, c i • e i, ?_, m - ∑ i, c i • e i, h2, by abel⟩` and prove the remaining obligations. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hsmul]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Establish `hli : LinearIndependent (PowerSeries O) e`.

Rewrite using `[Fintype.linearIndependent_iff]`. Establish `key : ∀ k : ℕ, ∀ g : Module.Free.ChooseBasisIndex O (M ⧸ p) → PowerSeries O, ∑ i, g i • e i = 0 → ∀ i, (PowerSeries.X : PowerSeries O) ^ k ∣ g i`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`.

Introduce `g _ i`. Simplify using the standard rewrite rules. Consider the case `succ k ih`. Introduce `g hg i`. Use `choose s hs using fun j => hdec (g j)`.

Establish `hc : ∀ j, PowerSeries.constantCoeff (g j) = 0`. Establish `h0 : ∑ j, (PowerSeries.constantCoeff (g j)) • b j = 0`. Establish `h1` using `congrArg p.mkQ hg`. Simplify using `only [map_sum, map_smul, Submodule.mkQ_apply, he, hN, map_zero] at h1`. Conclude with `h1`.

Conclude with `(Fintype.linearIndependent_iff.mp b.linearIndependent) _ h0`. Establish `hgX : ∀ j, g j = PowerSeries.X * s j`. Introduce `j`. Rewrite using `[hs j, hc j]`. Simplify using the standard rewrite rules.

Establish `hg' : (PowerSeries.X : PowerSeries O) • ∑ j, s j • e j = 0`. Rewrite using `[Finset.smul_sum, ← hg]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hgX j, mul_smul]`. Take `⟨t, ht⟩` from `ih s (hX _ hg') i`.

Conclude with `⟨t, by rw [hgX i, ht]; ring⟩`. Introduce `g hg i`. Use extensionality with `n`. Establish `h` using `PowerSeries.X_pow_dvd_iff.mp (key (n + 1) g hg i) n (Nat.lt_succ_self n)`. Simplify using `using h`.

Conclude with `Module.Free.of_basis (Module.Basis.mk hli hspan)`.
-/
theorem free_of_X_regular_quotient_torsionFree_scalarTower (O M : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [AddCommGroup M] [Module (PowerSeries O) M]
    [Module.Finite (PowerSeries O) M] [Module O M] [IsScalarTower O (PowerSeries O) M]
    (hX : ∀ x : M, (PowerSeries.X : PowerSeries O) • x = 0 → x = 0)
    (hT : ∀ (c : O) (x : M), c ≠ 0 →
      (∃ y : M, (PowerSeries.C c : PowerSeries O) • x = (PowerSeries.X : PowerSeries O) • y) →
      ∃ y : M, x = (PowerSeries.X : PowerSeries O) • y) :
    Module.Free (PowerSeries O) M := by
  classical
  set p : Submodule (PowerSeries O) M :=
    Ideal.span {(PowerSeries.X : PowerSeries O)} • (⊤ : Submodule (PowerSeries O) M) with hp
  have memp : ∀ m : M, m ∈ p ↔ ∃ y : M, m = (PowerSeries.X : PowerSeries O) • y := by
    intro m
    rw [hp, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨y, -, hy⟩
      exact ⟨y, hy.symm⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, Submodule.mem_top, hy.symm⟩
  have hsmul : ∀ (c : O) (m : M), c • m = (PowerSeries.C c : PowerSeries O) • m := by
    intro c m
    rw [← IsScalarTower.algebraMap_smul (PowerSeries O) c m, PowerSeries.algebraMap_apply]
    simp

  have hdec : ∀ r : PowerSeries O, ∃ s : PowerSeries O,
      r = PowerSeries.C (PowerSeries.constantCoeff r) + PowerSeries.X * s := by
    intro r
    obtain ⟨s, hs⟩ : (PowerSeries.X : PowerSeries O) ∣
        r - PowerSeries.C (PowerSeries.constantCoeff r) := by
      rw [PowerSeries.X_dvd_iff]
      simp
    exact ⟨s, by rw [← hs]; ring⟩

  have hN : ∀ (r : PowerSeries O) (y : M ⧸ p), r • y = (PowerSeries.constantCoeff r) • y := by
    intro r y
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective p y
    obtain ⟨s, hs⟩ := hdec r
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, memp]
    have e1 : r • m = (PowerSeries.C (PowerSeries.constantCoeff r) : PowerSeries O) • m
        + (PowerSeries.X : PowerSeries O) • (s • m) := by
      conv_lhs => rw [hs]
      rw [add_smul, mul_smul]
    refine ⟨s • m, ?_⟩
    rw [e1, hsmul]
    abel
  have hfin : Module.Finite O (M ⧸ p) := by
    obtain ⟨T, hT'⟩ := Module.finite_def.mp
      (inferInstance : Module.Finite (PowerSeries O) (M ⧸ p))
    refine ⟨⟨T, ?_⟩⟩
    rw [eq_top_iff]
    rintro y -
    have hy : y ∈ Submodule.span (PowerSeries O) (T : Set (M ⧸ p)) := by
      rw [hT']
      exact Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span hx
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul r x _ hx =>
      rw [hN]
      exact Submodule.smul_mem _ _ hx
  have htf : Module.IsTorsionFree O (M ⧸ p) := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun c y hcy => ?_
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective p y
    by_cases hc : c = 0
    · exact Or.inl hc
    · right
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, memp, hsmul c m] at hcy
      rw [Submodule.Quotient.mk_eq_zero, memp]
      exact hT c m hc hcy
  let b := Module.Free.chooseBasis O (M ⧸ p)
  choose e he using fun i => Submodule.Quotient.mk_surjective p (b i)
  have hspan : (⊤ : Submodule (PowerSeries O) M) ≤ Submodule.span (PowerSeries O) (Set.range e) := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := Ideal.span {PowerSeries.X})
      (Module.finite_def.mp inferInstance) ?_ ?_
    · rw [Ideal.span_le]
      rintro _ rfl
      change PowerSeries.X ∈ Ideal.jacobson (⊥ : Ideal (PowerSeries O))
      rw [Ideal.mem_jacobson_bot]
      intro y
      rw [PowerSeries.isUnit_iff_constantCoeff]
      simp
    · intro m _
      set c := b.repr (Submodule.Quotient.mk m)
      have h2 : m - ∑ i, c i • e i ∈ p := by
        rw [← Submodule.Quotient.eq, ← Submodule.mkQ_apply p (∑ i, c i • e i), map_sum]
        simp only [Submodule.mkQ_apply, Submodule.Quotient.mk_smul, he]
        exact (b.sum_repr _).symm
      rw [Submodule.mem_sup]
      refine ⟨∑ i, c i • e i, ?_, m - ∑ i, c i • e i, h2, by abel⟩
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [hsmul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hli : LinearIndependent (PowerSeries O) e := by
    rw [Fintype.linearIndependent_iff]

    have key : ∀ k : ℕ, ∀ g : Module.Free.ChooseBasisIndex O (M ⧸ p) → PowerSeries O,
        ∑ i, g i • e i = 0 → ∀ i, (PowerSeries.X : PowerSeries O) ^ k ∣ g i := by
      intro k
      induction k with
      | zero =>
        intro g _ i
        simp
      | succ k ih =>
        intro g hg i
        choose s hs using fun j => hdec (g j)
        have hc : ∀ j, PowerSeries.constantCoeff (g j) = 0 := by
          have h0 : ∑ j, (PowerSeries.constantCoeff (g j)) • b j = 0 := by
            have h1 := congrArg p.mkQ hg
            simp only [map_sum, map_smul, Submodule.mkQ_apply, he, hN, map_zero] at h1
            exact h1
          exact (Fintype.linearIndependent_iff.mp b.linearIndependent) _ h0
        have hgX : ∀ j, g j = PowerSeries.X * s j := by
          intro j
          rw [hs j, hc j]
          simp
        have hg' : (PowerSeries.X : PowerSeries O) • ∑ j, s j • e j = 0 := by
          rw [Finset.smul_sum, ← hg]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hgX j, mul_smul]
        obtain ⟨t, ht⟩ := ih s (hX _ hg') i
        exact ⟨t, by rw [hgX i, ht]; ring⟩
    intro g hg i
    ext n
    have h := PowerSeries.X_pow_dvd_iff.mp (key (n + 1) g hg i) n (Nat.lt_succ_self n)
    simpa using h
  exact Module.Free.of_basis (Module.Basis.mk hli hspan)

/- English proof (translation)
Set `_ : Module O M` to `Module.compHom M (algebraMap O (PowerSeries O))`. Establish `: IsScalarTower O (PowerSeries O) M` using `IsScalarTower.of_algebraMap_smul fun _ _ => rfl`. Conclude with `free_of_X_regular_quotient_torsionFree_scalarTower O M hX hT`.
-/
theorem free_of_X_regular_of_quotient_torsionFree (O M : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [AddCommGroup M] [Module (PowerSeries O) M]
    [Module.Finite (PowerSeries O) M]
    (hX : ∀ x : M, (PowerSeries.X : PowerSeries O) • x = 0 → x = 0)
    (hT : ∀ (c : O) (x : M), c ≠ 0 →
      (∃ y : M, (PowerSeries.C c : PowerSeries O) • x = (PowerSeries.X : PowerSeries O) • y) →
      ∃ y : M, x = (PowerSeries.X : PowerSeries O) • y) :
    Module.Free (PowerSeries O) M := by
  let _ : Module O M := Module.compHom M (algebraMap O (PowerSeries O))
  have : IsScalarTower O (PowerSeries O) M :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact free_of_X_regular_quotient_torsionFree_scalarTower O M hX hT

end GlobalTheory
