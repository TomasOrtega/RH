import Formalism.WachLatticeTwists.LatticeDualFibres.StatDualFibreLattice

universe u

open Formalism.NG (KO)

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.LOC

section SlopeTestRemainingChoices

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/- English proof (translation)
Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := O) k`. Establish `hb0 : b ≠ 0` using `nonZeroDivisors.ne_zero hb`. Take `⟨n, w, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ`. Use `⟨n, a * ((w⁻¹ : Oˣ) : O), ?_⟩` and prove the remaining obligations. Establish `hne : algebraMap O (FractionRing O) ((w : O) * ϖ ^ n) ≠ 0`.

Simplify using `using (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).mpr hb0`. Rewrite using `[Algebra.smul_def, ← mul_div_assoc, div_eq_iff hne, ← map_mul, ← map_mul]`. Use `congr 1`. Establish `: ((w⁻¹ : Oˣ) : O) * (w : O) = 1` using `by simp`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_pow_smul_integral {ϖ : O} (hϖ : Irreducible ϖ) (k : FractionRing O) :
    ∃ (n : ℕ) (a : O), (ϖ ^ n) • k = algebraMap O (FractionRing O) a := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) k
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨n, w, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  refine ⟨n, a * ((w⁻¹ : Oˣ) : O), ?_⟩
  have hne : algebraMap O (FractionRing O) ((w : O) * ϖ ^ n) ≠ 0 := by
    simpa using (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).mpr hb0
  rw [Algebra.smul_def, ← mul_div_assoc, div_eq_iff hne, ← map_mul, ← map_mul]
  congr 1
  have : ((w⁻¹ : Oˣ) : O) * (w : O) = 1 := by simp
  calc ϖ ^ n * a = ϖ ^ n * a * (((w⁻¹ : Oˣ) : O) * (w : O)) := by rw [this, mul_one]
    _ = a * ((w⁻¹ : Oˣ) : O) * ((w : O) * ϖ ^ n) := by ring

/- English proof (translation)
Establish `hx : x ∈ Submodule.span (FractionRing O) (T : Set V)` using `by rw [hT]; trivial`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨0, by simpa using hx⟩`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add x y _ _ ihx ihy`.

Take `⟨n, hn⟩` from `ihx`. Take `⟨m, hm⟩` from `ihy`. Use `⟨n + m, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`. Use `T.add_mem ?_ ?_` and prove the remaining obligations.

Rewrite using `[pow_add, mul_comm, mul_smul]`. Conclude with `T.smul_mem _ hn`. Rewrite using `[pow_add, mul_smul]`. Conclude with `T.smul_mem _ hm`. Consider the case `smul k x _ ih`.

Take `⟨n, hn⟩` from `ih`. Take `⟨m, a, ha⟩` from `exists_pow_smul_integral hϖ k`. Use `⟨m + n, ?_⟩` and prove the remaining obligations. Establish `: (ϖ ^ (m + n)) • k • x = a • (ϖ ^ n) • x`. Rewrite using `[pow_add, mul_comm, mul_smul, ← smul_assoc (ϖ ^ m) k x, ha, algebraMap_smul, smul_comm]`.

Rewrite using `[this]`. Conclude with `T.smul_mem _ hn`.
-/
theorem exists_pow_smul_mem {V : Type u} [AddCommGroup V] [Module O V] [Module (FractionRing O) V]
    [IsScalarTower O (FractionRing O) V] {T : Submodule O V}
    (hT : Submodule.span (FractionRing O) (T : Set V) = ⊤) {ϖ : O} (hϖ : Irreducible ϖ) (x : V) :
    ∃ n : ℕ, (ϖ ^ n) • x ∈ T := by
  have hx : x ∈ Submodule.span (FractionRing O) (T : Set V) := by rw [hT]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨0, by simpa using hx⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨n, hn⟩ := ihx
    obtain ⟨m, hm⟩ := ihy
    refine ⟨n + m, ?_⟩
    rw [smul_add]
    refine T.add_mem ?_ ?_
    · rw [pow_add, mul_comm, mul_smul]; exact T.smul_mem _ hn
    · rw [pow_add, mul_smul]; exact T.smul_mem _ hm
  | smul k x _ ih =>
    obtain ⟨n, hn⟩ := ih
    obtain ⟨m, a, ha⟩ := exists_pow_smul_integral hϖ k
    refine ⟨m + n, ?_⟩
    have : (ϖ ^ (m + n)) • k • x = a • (ϖ ^ n) • x := by
      rw [pow_add, mul_comm, mul_smul, ← smul_assoc (ϖ ^ m) k x, ha, algebraMap_smul,
        smul_comm]
    rw [this]; exact T.smul_mem _ hn

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `O V _ _ _ _ _ _ _ T hT`. Establish `hfin : Module.Finite O T` using `Module.Finite.iff_fg.mpr hT.1`. Establish `htfV : Module.IsTorsionFree O V` using `Module.IsTorsionFree.trans (R := FractionRing O)`. Establish `htf : Module.IsTorsionFree O T` using `inferInstance`. Establish `hfree : Module.Free O T` using `inferInstance`.

Set `b` to `Module.finBasis O T`. Set `v : Fin (Module.finrank O T) → V` to `fun i => (b i : V)`. Establish `hliO : LinearIndependent O v` using `b.linearIndependent.map' T.subtype (Submodule.ker_subtype T)`. Establish `hli : LinearIndependent (FractionRing O) v` using `(LinearIndependent.iff_fractionRing O (FractionRing O)).mp hliO`. Establish `hTv : ∀ t : T, (t : V) = ∑ i, b.repr t i • v i`.

Introduce `t`. Establish `h` using `congrArg T.subtype (b.sum_repr t)`. Rewrite `h` using `[map_sum]`. Simplify `h.symm` using `[v]`. Establish `hsp : ⊤ ≤ Submodule.span (FractionRing O) (Set.range v)`.

Rewrite using `[← hT.2, Submodule.span_le]`. Introduce `t ht`. Establish `h : t = ∑ i, b.repr ⟨t, ht⟩ i • v i` using `hTv ⟨t, ht⟩`. Rewrite using `[h]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[← algebraMap_smul (FractionRing O)]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Set `B : Module.Basis (Fin (Module.finrank O T)) (FractionRing O) V` to `Module.Basis.mk hli hsp`. Establish `hB : ∀ i, B i = v i` using `fun i => Module.Basis.mk_apply hli hsp i`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Module.finrank_eq_card_basis B, Fintype.card_fin]`. Set `f : V →ₗ[O] (Fin (Module.finrank O T) → KO O)` to `LinearMap.pi fun i => (toKO O) ∘ₗ ((B.coord i).restrictScalars O)`. Establish `hker : LinearMap.ker f = T`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `x hx`.

Establish `hx' : ∀ i, B.repr x i ∈ (1 : Submodule O (FractionRing O))`. Introduce `i`. Use `congrFun (LinearMap.mem_ker.mp hx) i` as an intermediate fact. Conclude with `(Submodule.Quotient.mk_eq_zero _).mp this`. Rewrite using `[← B.sum_repr x]`.

Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Take `⟨a, ha⟩` from `Submodule.mem_one.mp (hx' i)`. Rewrite using `[← ha, algebraMap_smul, hB]`. Conclude with `T.smul_mem _ (b i).2`. Introduce `x hx`.

Rewrite using `[LinearMap.mem_ker]`. Use function extensionality and compare the values at `i`. Establish `hrep : B.repr x i = algebraMap O (FractionRing O) (b.repr ⟨x, hx⟩ i)`. Establish `h1 : x = ∑ j, algebraMap O (FractionRing O) (b.repr ⟨x, hx⟩ j) • B j`. Establish `h : x = ∑ i, b.repr ⟨x, hx⟩ i • v i` using `hTv ⟨x, hx⟩`.

Simplify `h` using `[hB]`. Establish `h2` using `DFunLike.congr_fun (congrArg B.repr h1) i`. Rewrite `h2` using `[B.repr_sum_self]`. Conclude with `h2`. Express the relevant statement in the definitionally equal form `toKO O (B.repr x i) = 0`.

Rewrite using `[hrep]`. Conclude with `(Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_one.mpr ⟨_, rfl⟩)`. Use `⟨T.liftQ f hker.ge, ?_⟩` and prove the remaining obligations. Rewrite using `[← LinearMap.ker_eq_bot, Submodule.ker_liftQ, hker, Submodule.mkQ_map_self]`.
-/
theorem quotEmbeds : StatQuotEmbeds.{u} := by
  intro O V _ _ _ _ _ _ _ T hT
  have hfin : Module.Finite O T := Module.Finite.iff_fg.mpr hT.1
  have htfV : Module.IsTorsionFree O V := Module.IsTorsionFree.trans (R := FractionRing O)
  have htf : Module.IsTorsionFree O T := inferInstance
  have hfree : Module.Free O T := inferInstance
  let b := Module.finBasis O T
  let v : Fin (Module.finrank O T) → V := fun i => (b i : V)
  have hliO : LinearIndependent O v :=
    b.linearIndependent.map' T.subtype (Submodule.ker_subtype T)
  have hli : LinearIndependent (FractionRing O) v :=
    (LinearIndependent.iff_fractionRing O (FractionRing O)).mp hliO
  have hTv : ∀ t : T, (t : V) = ∑ i, b.repr t i • v i := by
    intro t
    have h := congrArg T.subtype (b.sum_repr t)
    rw [map_sum] at h
    simpa [v] using h.symm
  have hsp : ⊤ ≤ Submodule.span (FractionRing O) (Set.range v) := by
    rw [← hT.2, Submodule.span_le]
    intro t ht
    have h : t = ∑ i, b.repr ⟨t, ht⟩ i • v i := hTv ⟨t, ht⟩
    rw [h]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← algebraMap_smul (FractionRing O)]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let B : Module.Basis (Fin (Module.finrank O T)) (FractionRing O) V := Module.Basis.mk hli hsp
  have hB : ∀ i, B i = v i := fun i => Module.Basis.mk_apply hli hsp i
  refine ⟨?_, ?_⟩
  · rw [Module.finrank_eq_card_basis B, Fintype.card_fin]
  · let f : V →ₗ[O] (Fin (Module.finrank O T) → KO O) :=
      LinearMap.pi fun i => (toKO O) ∘ₗ ((B.coord i).restrictScalars O)
    have hker : LinearMap.ker f = T := by
      apply le_antisymm
      · intro x hx
        have hx' : ∀ i, B.repr x i ∈ (1 : Submodule O (FractionRing O)) := by
          intro i
          have := congrFun (LinearMap.mem_ker.mp hx) i
          exact (Submodule.Quotient.mk_eq_zero _).mp this
        rw [← B.sum_repr x]
        refine Submodule.sum_mem _ fun i _ => ?_
        obtain ⟨a, ha⟩ := Submodule.mem_one.mp (hx' i)
        rw [← ha, algebraMap_smul, hB]
        exact T.smul_mem _ (b i).2
      · intro x hx
        rw [LinearMap.mem_ker]
        funext i
        have hrep : B.repr x i = algebraMap O (FractionRing O) (b.repr ⟨x, hx⟩ i) := by
          have h1 : x = ∑ j, algebraMap O (FractionRing O) (b.repr ⟨x, hx⟩ j) • B j := by
            have h : x = ∑ i, b.repr ⟨x, hx⟩ i • v i := hTv ⟨x, hx⟩
            simpa [hB] using h
          have h2 := DFunLike.congr_fun (congrArg B.repr h1) i
          rw [B.repr_sum_self] at h2
          exact h2
        change toKO O (B.repr x i) = 0
        rw [hrep]
        exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_one.mpr ⟨_, rfl⟩)
    refine ⟨T.liftQ f hker.ge, ?_⟩
    rw [← LinearMap.ker_eq_bot, Submodule.ker_liftQ, hker, Submodule.mkQ_map_self]

end Formalism.RepresentationBoundsCohomology.LOC
