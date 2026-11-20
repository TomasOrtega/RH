import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

/- English proof (translation)
Establish `h0 : ∀ x : R, x ∈ (I ^ 2 • ⊤ : Submodule R R) → x = 0`. Introduce `x hx`. Rewrite `hx` using `[Ideal.smul_eq_mul, Ideal.mul_top, h]`. Conclude with `(Submodule.mem_bot R).mp hx`. Use `{ haus' := ?_, prec' := ?_ }` and prove the remaining obligations.

Introduce `x hx`. Establish `hx2` using `hx 2`. Rewrite `hx2` using `[SModEq.sub_mem, sub_zero]`. Conclude with `h0 x hx2`. Introduce `f hf`.

Use `⟨f 2, fun n => ?_⟩` and prove the remaining obligations. Break down `le_or_gt 2 n with hn | hn` into its components or cases. Establish `hfn` using `hf hn`. Rewrite `hfn` using `[SModEq.sub_mem]`. Establish `e : f 2 = f n` using `sub_eq_zero.mp (h0 _ hfn)`.

Rewrite using `[SModEq.sub_mem, e, sub_self]`. Conclude with `Submodule.zero_mem _`. Conclude with `hf hn.le`.
-/
private theorem complete_of_sq {R : Type} [CommRing R] (I : Ideal R) (h : I ^ 2 = ⊥) :
    IsAdicComplete I R := by
  have h0 : ∀ x : R, x ∈ (I ^ 2 • ⊤ : Submodule R R) → x = 0 := by
    intro x hx
    rw [Ideal.smul_eq_mul, Ideal.mul_top, h] at hx
    exact (Submodule.mem_bot R).mp hx
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    have hx2 := hx 2
    rw [SModEq.sub_mem, sub_zero] at hx2
    exact h0 x hx2
  · intro f hf
    refine ⟨f 2, fun n => ?_⟩
    rcases le_or_gt 2 n with hn | hn
    · have hfn := hf hn
      rw [SModEq.sub_mem] at hfn
      have e : f 2 = f n := sub_eq_zero.mp (h0 _ hfn)
      rw [SModEq.sub_mem, e, sub_self]
      exact Submodule.zero_mem _
    · exact hf hn.le

/- English proof (translation)
Introduce `O _ _`. Prove the components needed by the constructor for the conclusion. Use `IsCO.mk ?_ ?_ ?_` and prove the remaining obligations. Apply `complete_of_sq` to reduce the goal to its premises. Rewrite using `[maximalIdeal_eq_bot, pow_two, Ideal.bot_mul]`.

Use `show IsLocalHom (residue O) infer_instance`. Introduce `x`. Take `⟨a, ha⟩` from `Ideal.Quotient.mk_surjective x`. Use `⟨a, ?_⟩` and prove the remaining obligations. Establish `h : x - algebraMap O (ResidueField O) a = 0` using `sub_eq_zero.mpr ha.symm`.

Rewrite using `[h]`. Conclude with `zero_mem _`. Establish `hm : ∀ x : DualNumber (ResidueField O), x ∈ maximalIdeal _ ↔ x.fst = 0`. Introduce `x`. Rewrite using `[mem_maximalIdeal, mem_nonunits_iff, TrivSqZeroExt.isUnit_iff_isUnit_fst, isUnit_iff_ne_zero, not_not]`.

Establish `hfst : ∀ a : O, (algebraMap O (DualNumber (ResidueField O)) a).fst = algebraMap O (ResidueField O) a` using `fun a => (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).commutes a`. Use `IsCO.mk ?_ ?_ ?_` and prove the remaining obligations. Apply `complete_of_sq` to reduce the goal to its premises. Rewrite using `[pow_two]`. Use `le_bot_iff.mp (Ideal.mul_le.mpr fun r hr s hs => ?_)` and prove the remaining obligations.

Rewrite `hr`, `hs` using `[hm]`. Apply the tactic sequence `refine Ideal.mem_bot.mpr (TrivSqZeroExt.ext ?_ ?_) <;> simp [hr, hs]`. Use `⟨fun a ha => ?_⟩` and prove the remaining obligations. Establish `h1` using `ha.map (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O))`. Rewrite `h1` using `[(TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).commutes]`.

Conclude with `isUnit_of_map_unit (residue O) a h1`. Introduce `x`. Take `⟨a, ha⟩` from `Ideal.Quotient.mk_surjective x.fst`. Use `⟨a, ?_⟩` and prove the remaining obligations. Rewrite using `[hm, TrivSqZeroExt.fst_sub, hfst]`.

Conclude with `sub_eq_zero.mpr ha.symm`.
-/
theorem UpperTheory.V.Alg.co_res :
    ∀ (O : Type) [CommRing O] [IsLocalRing O], IsCO O (ResidueField O) ∧ IsCO O (DualNumber (ResidueField O)) := by
  intro O _ _
  constructor
  · refine IsCO.mk ?_ ?_ ?_
    · apply complete_of_sq
      rw [maximalIdeal_eq_bot, pow_two, Ideal.bot_mul]
    · show IsLocalHom (residue O)
      infer_instance
    · intro x
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective x
      refine ⟨a, ?_⟩
      have h : x - algebraMap O (ResidueField O) a = 0 := sub_eq_zero.mpr ha.symm
      rw [h]
      exact zero_mem _
  · have hm : ∀ x : DualNumber (ResidueField O), x ∈ maximalIdeal _ ↔ x.fst = 0 := by
      intro x
      rw [mem_maximalIdeal, mem_nonunits_iff, TrivSqZeroExt.isUnit_iff_isUnit_fst, isUnit_iff_ne_zero,
        not_not]
    have hfst : ∀ a : O, (algebraMap O (DualNumber (ResidueField O)) a).fst =
        algebraMap O (ResidueField O) a :=
      fun a => (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).commutes a
    refine IsCO.mk ?_ ?_ ?_
    · apply complete_of_sq
      rw [pow_two]
      refine le_bot_iff.mp (Ideal.mul_le.mpr fun r hr s hs => ?_)
      rw [hm] at hr hs
      refine Ideal.mem_bot.mpr (TrivSqZeroExt.ext ?_ ?_) <;> simp [hr, hs]
    · refine ⟨fun a ha => ?_⟩
      have h1 := ha.map (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O))
      rw [(TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).commutes] at h1
      exact isUnit_of_map_unit (residue O) a h1
    · intro x
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective x.fst
      refine ⟨a, ?_⟩
      rw [hm, TrivSqZeroExt.fst_sub, hfst]
      exact sub_eq_zero.mpr ha.symm
