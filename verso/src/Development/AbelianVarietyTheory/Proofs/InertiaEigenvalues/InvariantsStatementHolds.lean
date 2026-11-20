import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.InvariantsGenerators
import Formalism.SharpRestriction.LevelLetterCocycles.InvariantsIsoOfGenerators
import Formalism.SharpRestriction.LevelLetterCocycles.ZlWCbInjective
import Formalism.SharpRestriction.LevelLetterCocycles.NormLtOneIffToZMod

noncomputable section

namespace GlobalTheory.FixedByDense

section
open Formalism.MainNotions Formalism.MainNotions.InvariantsGenerators Formalism.MainNotions.InvariantsGenerators.InvariantsFromGenerators
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.tableLineDegreeTwo Formalism.MainNotions.LocalSituation TensorProduct

def PGen (S : Sit) : Set S.G :=
  {g | S.W.resΓ g ∈ Subgroup.closure (insert S.W.gamK (S.W.DelF : Set S.W.Gam))}

/- English proof (translation)
Introduce `T t hK hΔ h1 g`. Establish `hact : ∀ g : S.G, T.actT g t = t ↔ T.ρ g (t : T.V) = t` using `fun g => ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩`. Set `St : Subgroup S.G` to `{ carrier := {g | T.ρ g (t : T.V) = t} mul_mem' := fun {a b} ha hb => by`. Simplify using `only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *`. Rewrite using `[hb, ha]`.

Use the proof step `one_mem' := by simp`. Use the proof step `inv_mem' := fun {a} ha => by`. Express the relevant statement in the definitionally equal form `T.ρ a (t : T.V) = t at ha`. Express the relevant statement in the definitionally equal form `T.ρ a⁻¹ (t : T.V) = t`. Combine the equalities or inequalities in the displayed calculation.

Establish `hmem : ∀ g, g ∈ St ↔ T.ρ g (t : T.V) = t` using `fun g => Iff.rfl`. Establish `hmap : Subgroup.closure (insert S.W.gamK (S.W.DelF : Set S.W.Gam)) ≤ St.map S.W.resΓ`. Rewrite using `[Subgroup.closure_le]`. Introduce and unpack `x (rfl | hx)`. Take `⟨g, hg⟩` from `S.W.resΓ_onto S.W.gamK`.

Conclude with `⟨g, (hmem g).2 ((hact g).1 (hK g hg)), hg⟩`. Take `⟨g, hg⟩` from `S.W.resΓ_onto x`. Conclude with `⟨g, (hmem g).2 ((hact g).1 (hΔ g (hg ▸ hx))), hg⟩`. Establish `hP : PGen S ⊆ (St : Set S.G)`. Introduce `g hg`.

Take `⟨h, hh, he⟩` from `hmap hg`. Establish `hk : h⁻¹ * g ∈ St` using `(hmem _).2 ((hact _).1 (h1 _ (by rw [map_mul, map_inv, he, inv_mul_cancel])))`. Use `St.mul_mem hh hk` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel_left]`. Then use the resulting hypothesis. Establish `hcl : IsClosed (St : Set S.G)` using `isClosed_eq (T.cont (t : T.V)) continuous_const`.

Establish `hall : (Set.univ : Set S.G) ⊆ St`. Rewrite using `[← hd.closure_eq]`. Conclude with `closure_minimal hP hcl`. Conclude with `(hact g).2 (hall (Set.mem_univ g))`.
-/
theorem genFix_of_dense (S : Sit) (hT2 : ∀ T : LocLat S.G S.Qp S.LL S.O, T2Space T.V)
    (hd : Dense (PGen S)) : GenFix S := by
  intro T t hK hΔ h1 g
  have hact : ∀ g : S.G, T.actT g t = t ↔ T.ρ g (t : T.V) = t := fun g =>
    ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  let St : Subgroup S.G :=
    { carrier := {g | T.ρ g (t : T.V) = t}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
        rw [hb, ha]
      one_mem' := by simp
      inv_mem' := fun {a} ha => by
        change T.ρ a (t : T.V) = t at ha
        change T.ρ a⁻¹ (t : T.V) = t
        calc T.ρ a⁻¹ (t : T.V) = T.ρ a⁻¹ (T.ρ a (t : T.V)) := by rw [ha]
          _ = t := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hmem : ∀ g, g ∈ St ↔ T.ρ g (t : T.V) = t := fun g => Iff.rfl
  have hmap : Subgroup.closure (insert S.W.gamK (S.W.DelF : Set S.W.Gam)) ≤ St.map S.W.resΓ := by
    rw [Subgroup.closure_le]
    rintro x (rfl | hx)
    · obtain ⟨g, hg⟩ := S.W.resΓ_onto S.W.gamK
      exact ⟨g, (hmem g).2 ((hact g).1 (hK g hg)), hg⟩
    · obtain ⟨g, hg⟩ := S.W.resΓ_onto x
      exact ⟨g, (hmem g).2 ((hact g).1 (hΔ g (hg ▸ hx))), hg⟩
  have hP : PGen S ⊆ (St : Set S.G) := by
    intro g hg
    obtain ⟨h, hh, he⟩ := hmap hg
    have hk : h⁻¹ * g ∈ St := (hmem _).2 ((hact _).1 (h1 _ (by rw [map_mul, map_inv, he, inv_mul_cancel])))
    have := St.mul_mem hh hk
    rwa [mul_inv_cancel_left] at this
  have hcl : IsClosed (St : Set S.G) := isClosed_eq (T.cont (t : T.V)) continuous_const
  have hall : (Set.univ : Set S.G) ⊆ St := by
    rw [← hd.closure_eq]
    exact closure_minimal hP hcl
  exact (hact g).2 (hall (Set.mem_univ g))

variable {l : ℕ} [Fact l.Prime]

local instance contMulLL (LL : FinExt l) : ContinuousMul ↥LL.1 :=
  ⟨continuous_induced_rng.2 ((continuous_subtype_val.comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd))⟩

local instance contAddLL (LL : FinExt l) : ContinuousAdd ↥LL.1 :=
  ⟨continuous_induced_rng.2 ((continuous_subtype_val.comp continuous_fst).add
    (continuous_subtype_val.comp continuous_snd))⟩

/- English proof (translation)
Set `b` to `Module.finBasis ↥LL.1 T.V`. Establish `hc : Continuous b.equivFun` using `IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap`. Conclude with `T2Space.of_injective_continuous b.equivFun.injective hc`.
-/
theorem t2Space_locLat_V' {G : Type} [Group G] [TopologicalSpace G] (LL : FinExt l)
    (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) : T2Space T.V := by
  let b := Module.finBasis ↥LL.1 T.V
  have hc : Continuous b.equivFun := IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap
  exact T2Space.of_injective_continuous b.equivFun.injective hc

/- English proof (translation)
The claim follows from `t2Space_locLat_V' (G := ↥(GK K)) LL T`.
-/
theorem t2Space_lattice_V_of_good_situation (LT : LocTheory) (HW : HWOf LT) (AI : LocAinf l (LT l)) (K : FinExt l) (s : ℕ)
    (LL : FinExt l) (h : Good K s LL) (T : LocLat (sit LT HW l AI K s LL h).G (sit LT HW l AI K s LL h).Qp
      (sit LT HW l AI K s LL h).LL (sit LT HW l AI K s LL h).O) : T2Space T.V :=
  t2Space_locLat_V' (G := ↥(GK K)) LL T

end

section
open Formalism.MainNotions Formalism.MainNotions.InvariantsGenerators Formalism.MainNotions.InvariantsGenerators.InvariantsFromGenerators
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.tableLineDegreeTwo Formalism.MainNotions.LocalSituation Topology Filter

variable {l : ℕ} [hl : Fact l.Prime]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih => rw [← add_assoc, pow_succ', pow_mul, P.ζQ_succ, ih]`.
-/
theorem zetaQ_pow (P : LocPrime l) (j k : ℕ) : P.ζQ (j + k) ^ (l ^ k) = P.ζQ j := by
  induction k with
  | zero => simp
  | succ k ih => rw [← add_assoc, pow_succ', pow_mul, P.ζQ_succ, ih]

/- English proof (translation)
Take `⟨k, rfl⟩ : ∃ k, m = k + 1` from `⟨m - 1, by omega⟩`. Apply `orderOf_eq_prime_pow` to reduce the goal to its premises. Use `zetaQ_pow P 1 k` as an intermediate fact. Rewrite `this` using `[add_comm]`. Rewrite using `[this]`.

Conclude with `P.ζQ_one`. Use `zetaQ_pow P 0 (k + 1)` as an intermediate fact. Rewrite `this` using `[zero_add]`. Rewrite using `[this, P.ζQ_zero]`.
-/
theorem zetaQ_order (P : LocPrime l) (m : ℕ) (hm : 1 ≤ m) : orderOf (P.ζQ m) = l ^ m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  apply orderOf_eq_prime_pow
  · have := zetaQ_pow P 1 k
    rw [add_comm] at this
    rw [this]; exact P.ζQ_one
  · have := zetaQ_pow P 0 (k + 1)
    rw [zero_add] at this
    rw [this, P.ζQ_zero]

/- English proof (translation)
Use `zetaQ_pow P 0 m` as an intermediate fact. Rewrite `this` using `[zero_add, P.ζQ_zero]`. Then use the resulting hypothesis.
-/
theorem zetaQ_root (P : LocPrime l) (m : ℕ) : P.ζQ m ^ (l ^ m) = 1 := by
  have := zetaQ_pow P 0 m
  rwa [zero_add, P.ζQ_zero] at this

/- English proof (translation)
Take `⟨a, ha, hha⟩` from `P.χQ_cyc h m (P.ζQ m) (zetaQ_root P m)`. Establish `h1 : P.ζQ m ^ a = P.ζQ m` using `by rw [← hha, hζ]`. Establish `hord` using `zetaQ_order P m hm`. Establish `hz0 : P.ζQ m ≠ 0`. Introduce `h0`.

Use `zetaQ_root P m` as an intermediate fact. Rewrite `this` using `[h0, zero_pow (pow_ne_zero _ hl.out.ne_zero)]`. Conclude with `zero_ne_one this`. Establish `hdvd : ((l : ℤ) ^ m) ∣ (1 - (a : ℤ))`. Break down `Nat.eq_zero_or_pos a with ha0 | hapos` into its components or cases.

It suffices to derive a contradiction. Rewrite `h1` using `[ha0, pow_zero]`. Establish `: orderOf (P.ζQ m) = 1` using `by rw [← h1, orderOf_one]`. Rewrite `this` using `[hord]`. Use `Nat.one_lt_pow (by omega : m ≠ 0) hl.out.one_lt` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `h2 : P.ζQ m ^ (a - 1) = 1`. Apply `mul_right_cancel₀ hz0` to reduce the goal to its premises. Rewrite using `[← pow_succ, Nat.sub_add_cancel hapos, h1, one_mul]`. Establish `hd : l ^ m ∣ a - 1` using `hord ▸ orderOf_dvd_of_pow_eq_one h2`.

Establish `h3 : ((l : ℤ) ^ m) ∣ ((a - 1 : ℕ) : ℤ)` using `by exact_mod_cast Int.natCast_dvd_natCast.2 hd`. Rewrite `h3` using `[Nat.cast_sub hapos, Nat.cast_one]`. Rewrite using `[← neg_sub]`. Conclude with `(dvd_neg).2 h3`. Establish `h2 : ‖(((1 - (a : ℤ)) : ℤ) : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(m : ℤ))` using `(Padic.norm_int_le_pow_iff_dvd _ _).2 hdvd`.

Establish `h3 : (P.χQ h : ℚ_[l]) - 1 = ((P.χQ h : ℚ_[l]) - a) + -(((1 - (a : ℤ)) : ℤ) : ℚ_[l])` using `by push_cast; ring`. Rewrite using `[h3]`. Use `(Padic.nonarchimedean _ _).trans (max_le ha ?_)` and prove the remaining obligations. Rewrite using `[norm_neg]` and apply the resulting hypothesis.
-/
theorem chiQ_fix (P : LocPrime l) (h : GQ l) (m : ℕ) (hm : 1 ≤ m) (hζ : h (P.ζQ m) = P.ζQ m) :
    ‖(P.χQ h : ℚ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
  obtain ⟨a, ha, hha⟩ := P.χQ_cyc h m (P.ζQ m) (zetaQ_root P m)
  have h1 : P.ζQ m ^ a = P.ζQ m := by rw [← hha, hζ]
  have hord := zetaQ_order P m hm
  have hz0 : P.ζQ m ≠ 0 := by
    intro h0
    have := zetaQ_root P m
    rw [h0, zero_pow (pow_ne_zero _ hl.out.ne_zero)] at this
    exact zero_ne_one this
  have hdvd : ((l : ℤ) ^ m) ∣ (1 - (a : ℤ)) := by
    rcases Nat.eq_zero_or_pos a with ha0 | hapos
    · exfalso
      rw [ha0, pow_zero] at h1
      have : orderOf (P.ζQ m) = 1 := by rw [← h1, orderOf_one]
      rw [hord] at this
      have := Nat.one_lt_pow (by omega : m ≠ 0) hl.out.one_lt
      omega
    · have h2 : P.ζQ m ^ (a - 1) = 1 := by
        apply mul_right_cancel₀ hz0
        rw [← pow_succ, Nat.sub_add_cancel hapos, h1, one_mul]
      have hd : l ^ m ∣ a - 1 := hord ▸ orderOf_dvd_of_pow_eq_one h2
      have h3 : ((l : ℤ) ^ m) ∣ ((a - 1 : ℕ) : ℤ) := by exact_mod_cast Int.natCast_dvd_natCast.2 hd
      rw [Nat.cast_sub hapos, Nat.cast_one] at h3
      rw [← neg_sub]
      exact (dvd_neg).2 h3
  have h2 : ‖(((1 - (a : ℤ)) : ℤ) : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(m : ℤ)) :=
    (Padic.norm_int_le_pow_iff_dvd _ _).2 hdvd
  have h3 : (P.χQ h : ℚ_[l]) - 1 = ((P.χQ h : ℚ_[l]) - a) + -(((1 - (a : ℤ)) : ℤ) : ℚ_[l]) := by
    push_cast; ring
  rw [h3]
  refine (Padic.nonarchimedean _ _).trans (max_le ha ?_)
  rwa [norm_neg]

/- English proof (translation)
Take `⟨a, ha, hha⟩` from `P.χQ_cyc h 1 (P.ζQ 1) (by simpa using zetaQ_root P 1)`. Establish `hna : ¬ (l : ℤ) ∣ (a : ℤ)`. Introduce `hd`. Establish `h1 : P.ζQ 1 ^ a = 1`. Rewrite using `[← orderOf_dvd_iff_pow_eq_one, zetaQ_order P 1 le_rfl, pow_one]`.

Conclude with `hd` after adjusting the coercions. Rewrite `h1` using `[← hha]`. Conclude with `P.ζQ_one (h.injective (h1.trans (map_one h).symm))`. Establish `hA : ‖((a : ℤ) : ℚ_[l])‖ = 1`. Establish `: ‖((a : ℤ) : ℤ_[l])‖ = 1` using `le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun hlt => hna ((PadicInt.norm_int_lt_one_iff_dvd _).1 hlt))`.

Rewrite `this` using `[PadicInt.norm_def, PadicInt.coe_intCast]`. Conclude with `this`. Establish `hlt : ‖(P.χQ h : ℚ_[l]) - a‖ < ‖((a : ℤ) : ℚ_[l])‖`. Rewrite using `[hA]`. Use `lt_of_le_of_lt ha ?_` and prove the remaining obligations.

Rewrite using `[Nat.cast_one, zpow_neg_one]`. Conclude with `inv_lt_one_of_one_lt₀ (by exact_mod_cast hl.out.one_lt)`. Establish `h3 : (P.χQ h : ℚ_[l]) = ((a : ℤ) : ℚ_[l]) + ((P.χQ h : ℚ_[l]) - a)` using `by push_cast; ring`. Rewrite using `[h3, Padic.add_eq_max_of_ne (ne_of_gt hlt), max_eq_left hlt.le, hA]`.
-/
theorem chiQ_norm (P : LocPrime l) (h : GQ l) : ‖(P.χQ h : ℚ_[l])‖ = 1 := by
  obtain ⟨a, ha, hha⟩ := P.χQ_cyc h 1 (P.ζQ 1) (by simpa using zetaQ_root P 1)
  have hna : ¬ (l : ℤ) ∣ (a : ℤ) := by
    intro hd
    have h1 : P.ζQ 1 ^ a = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, zetaQ_order P 1 le_rfl, pow_one]
      exact_mod_cast hd
    rw [← hha] at h1
    exact P.ζQ_one (h.injective (h1.trans (map_one h).symm))
  have hA : ‖((a : ℤ) : ℚ_[l])‖ = 1 := by
    have : ‖((a : ℤ) : ℤ_[l])‖ = 1 :=
      le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun hlt => hna ((PadicInt.norm_int_lt_one_iff_dvd _).1 hlt))
    rw [PadicInt.norm_def, PadicInt.coe_intCast] at this
    exact this
  have hlt : ‖(P.χQ h : ℚ_[l]) - a‖ < ‖((a : ℤ) : ℚ_[l])‖ := by
    rw [hA]
    refine lt_of_le_of_lt ha ?_
    rw [Nat.cast_one, zpow_neg_one]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hl.out.one_lt)
  have h3 : (P.χQ h : ℚ_[l]) = ((a : ℤ) : ℚ_[l]) + ((P.χQ h : ℚ_[l]) - a) := by push_cast; ring
  rw [h3, Padic.add_eq_max_of_ne (ne_of_gt hlt), max_eq_left hlt.le, hA]

/- English proof (translation)
Rewrite using `[continuous_iff_continuousAt]`. Introduce `g`. Rewrite using `[ContinuousAt, Metric.tendsto_nhds]`. Introduce `ε hε`. Establish `hl1 : (l : ℝ)⁻¹ < 1` using `inv_lt_one_of_one_lt₀ (by exact_mod_cast hl.out.one_lt)`.

Take `⟨m, hm⟩` from `exists_pow_lt_of_lt_one hε hl1`. Set `E : IntermediateField ℚ_[l] (Om l)` to `IntermediateField.adjoin ℚ_[l] {P.ζQ (m + 1)}`. Use `haveI : FiniteDimensional ℚ_[l] E := IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)`. Establish `hU : IsOpen (E.fixingSubgroup : Set (GQ l))` using `E.fixingSubgroup_isOpen`. Establish `hopen : IsOpen {h : GQ l | g⁻¹ * h ∈ E.fixingSubgroup}` using `hU.preimage (continuous_mul_left g⁻¹)`.

Use `filter_upwards [hopen.mem_nhds (by simp)] with h hh`. Rewrite using `[dist_eq_norm]`. Establish `hfix : (g⁻¹ * h) (P.ζQ (m + 1)) = P.ζQ (m + 1)` using `(mem_fixingSubgroup_iff _).1 hh (P.ζQ (m + 1)) (IntermediateField.subset_adjoin _ _ rfl)`. Establish `h1` using `chiQ_fix P (g⁻¹ * h) (m + 1) (by omega) hfix`. Establish `hmul : (P.χQ h : ℚ_[l]) = P.χQ g * P.χQ (g⁻¹ * h)`.

Rewrite using `[← Units.val_mul, ← map_mul, mul_inv_cancel_left]`. Establish `hle : (l : ℝ) ^ (-((m + 1 : ℕ) : ℤ)) ≤ (l : ℝ)⁻¹ ^ m`. Rewrite using `[zpow_neg, zpow_natCast, ← inv_pow]`. Conclude with `pow_le_pow_of_le_one (by positivity) hl1.le (by omega)`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hmul, ← norm_mul, mul_sub, mul_one]`. Use `_ ≤ 1 * (l : ℝ) ^ (-((m + 1 : ℕ) : ℤ)) := by rw [chiQ_norm]; exact mul_le_mul_of_nonneg_left h1 zero_le_one`. Use `_ < ε := by rw [one_mul]; exact lt_of_le_of_lt hle hm`.
-/
theorem chiQ_cont (P : LocPrime l) : Continuous (fun h : GQ l => (P.χQ h : ℚ_[l])) := by
  rw [continuous_iff_continuousAt]
  intro g
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  have hl1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hl.out.one_lt)
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε hl1
  let E : IntermediateField ℚ_[l] (Om l) := IntermediateField.adjoin ℚ_[l] {P.ζQ (m + 1)}
  haveI : FiniteDimensional ℚ_[l] E :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)
  have hU : IsOpen (E.fixingSubgroup : Set (GQ l)) := E.fixingSubgroup_isOpen
  have hopen : IsOpen {h : GQ l | g⁻¹ * h ∈ E.fixingSubgroup} := hU.preimage (continuous_mul_left g⁻¹)
  filter_upwards [hopen.mem_nhds (by simp)] with h hh
  rw [dist_eq_norm]
  have hfix : (g⁻¹ * h) (P.ζQ (m + 1)) = P.ζQ (m + 1) :=
    (mem_fixingSubgroup_iff _).1 hh (P.ζQ (m + 1)) (IntermediateField.subset_adjoin _ _ rfl)
  have h1 := chiQ_fix P (g⁻¹ * h) (m + 1) (by omega) hfix
  have hmul : (P.χQ h : ℚ_[l]) = P.χQ g * P.χQ (g⁻¹ * h) := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel_left]
  have hle : (l : ℝ) ^ (-((m + 1 : ℕ) : ℤ)) ≤ (l : ℝ)⁻¹ ^ m := by
    rw [zpow_neg, zpow_natCast, ← inv_pow]
    exact pow_le_pow_of_le_one (by positivity) hl1.le (by omega)
  calc ‖(P.χQ h : ℚ_[l]) - P.χQ g‖ = ‖(P.χQ g : ℚ_[l])‖ * ‖(P.χQ (g⁻¹ * h) : ℚ_[l]) - 1‖ := by
        rw [hmul, ← norm_mul, mul_sub, mul_one]
    _ ≤ 1 * (l : ℝ) ^ (-((m + 1 : ℕ) : ℤ)) := by rw [chiQ_norm]; exact mul_le_mul_of_nonneg_left h1 zero_le_one
    _ < ε := by rw [one_mul]; exact lt_of_le_of_lt hle hm

/- English proof (translation)
Establish `hint : ∀ z : ℚ_[l], 0 ≤ P.v LL (algebraMap ℚ_[l] ↥LL.1 z) → ‖z‖ ≤ 1`. Introduce `z hz`. Establish `hO` using `(P.v_O LL _).1 hz`. Establish `hI : IsIntegral ℤ_[l] (algebraMap ℚ_[l] ↥LL.1 z)` using `hO`. Establish `hI' : IsIntegral ℤ_[l] z` using `(isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ_[l] ℚ_[l] ↥LL.1) (algebraMap ℚ_[l] ↥LL.1).injective).1 hI`.

Take `⟨y, rfl⟩` from `IsIntegrallyClosed.isIntegral_iff.1 hI'`. Rewrite using `[PadicInt.algebraMap_apply]`. Conclude with `PadicInt.norm_le_one y`. Establish `hx0 : x ≠ 0`. Introduce and unpack `rfl`.

Rewrite `hv` using `[map_zero, AddValuation.map_zero]`. Conclude with `WithTop.top_ne_one hv`. Establish `hl0 : (l : ℚ_[l]) ≠ 0` using `by exact_mod_cast hl.out.ne_zero`. Use `set y := x / l with hy`. Establish `hy0 : y ≠ 0` using `div_ne_zero hx0 hl0`.

Establish `hvl : P.v LL (algebraMap ℚ_[l] ↥LL.1 (l : ℚ_[l])) = 1` using `by rw [map_natCast]; exact P.v_l LL`. Establish `hxy : x = y * l` using `by rw [hy, div_mul_cancel₀ _ hl0]`. Establish `hvy : P.v LL (algebraMap ℚ_[l] ↥LL.1 y) = 0`. Rewrite `hv` using `[hxy, map_mul, AddValuation.map_mul, hvl]`. Establish `h2 : P.v LL (algebraMap ℚ_[l] ↥LL.1 y) + 1 = 0 + 1` using `by rw [hv, zero_add]`.

Conclude with `WithTop.add_right_cancel WithTop.one_ne_top h2`. Establish `hvy' : P.v LL (algebraMap ℚ_[l] ↥LL.1 y⁻¹) = 0`. Establish `h1 : algebraMap ℚ_[l] ↥LL.1 y * algebraMap ℚ_[l] ↥LL.1 y⁻¹ = 1`. Rewrite using `[← map_mul, mul_inv_cancel₀ hy0, map_one]`. Use `congrArg (P.v LL) h1` as an intermediate fact.

Rewrite `this` using `[AddValuation.map_mul, AddValuation.map_one, hvy, zero_add]`. Then use the resulting hypothesis. Establish `hy1` using `hint y (by rw [hvy])`. Establish `hy2` using `hint y⁻¹ (by rw [hvy'])`. Establish `hyn : ‖y‖ = 1`. Rewrite `hy2` using `[norm_inv]`.

Establish `hpos : 0 < ‖y‖` using `norm_pos_iff.2 hy0`. Conclude with `le_antisymm hy1 (by rwa [inv_le_one₀ hpos] at hy2)`. Rewrite using `[hxy, norm_mul, hyn, one_mul, Padic.norm_p]`.
-/
theorem norm_of_v_one (P : LocPrime l) (LL : FinExt l) (x : ℚ_[l])
    (hv : P.v LL (algebraMap ℚ_[l] ↥LL.1 x) = 1) : ‖x‖ = (l : ℝ)⁻¹ := by
  have hint : ∀ z : ℚ_[l], 0 ≤ P.v LL (algebraMap ℚ_[l] ↥LL.1 z) → ‖z‖ ≤ 1 := by
    intro z hz
    have hO := (P.v_O LL _).1 hz
    have hI : IsIntegral ℤ_[l] (algebraMap ℚ_[l] ↥LL.1 z) := hO
    have hI' : IsIntegral ℤ_[l] z :=
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ_[l] ℚ_[l] ↥LL.1) (algebraMap ℚ_[l] ↥LL.1).injective).1 hI
    obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hI'
    rw [PadicInt.algebraMap_apply]
    exact PadicInt.norm_le_one y
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero, AddValuation.map_zero] at hv
    exact WithTop.top_ne_one hv
  have hl0 : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast hl.out.ne_zero
  set y := x / l with hy
  have hy0 : y ≠ 0 := div_ne_zero hx0 hl0
  have hvl : P.v LL (algebraMap ℚ_[l] ↥LL.1 (l : ℚ_[l])) = 1 := by rw [map_natCast]; exact P.v_l LL
  have hxy : x = y * l := by rw [hy, div_mul_cancel₀ _ hl0]
  have hvy : P.v LL (algebraMap ℚ_[l] ↥LL.1 y) = 0 := by
    rw [hxy, map_mul, AddValuation.map_mul, hvl] at hv
    have h2 : P.v LL (algebraMap ℚ_[l] ↥LL.1 y) + 1 = 0 + 1 := by rw [hv, zero_add]
    exact WithTop.add_right_cancel WithTop.one_ne_top h2
  have hvy' : P.v LL (algebraMap ℚ_[l] ↥LL.1 y⁻¹) = 0 := by
    have h1 : algebraMap ℚ_[l] ↥LL.1 y * algebraMap ℚ_[l] ↥LL.1 y⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hy0, map_one]
    have := congrArg (P.v LL) h1
    rwa [AddValuation.map_mul, AddValuation.map_one, hvy, zero_add] at this
  have hy1 := hint y (by rw [hvy])
  have hy2 := hint y⁻¹ (by rw [hvy'])
  have hyn : ‖y‖ = 1 := by
    rw [norm_inv] at hy2
    have hpos : 0 < ‖y‖ := norm_pos_iff.2 hy0
    exact le_antisymm hy1 (by rwa [inv_le_one₀ hpos] at hy2)
  rw [hxy, norm_mul, hyn, one_mul, Padic.norm_p]

/- English proof (translation)
Set `W` to `(HW l).W K 1 LL h`. Set `P` to `LT l`. Set `χ' : ↥(GK K) → ℚ_[l]` to `fun g => (P.χQ (g : GQ l) : ℚ_[l])`. Establish `hlink : ∀ g : ↥(GK K), algebraMap ↥(OL LL) ↥LL.1 ((W.χΓ (W.resΓ g) : ↥(OL LL))) = algebraMap ℚ_[l] ↥LL.1 (χ' g)` using `fun g => by`. Rewrite using `[W.χΓ_res g, P.PD_χ K g]`.

Establish `hres : ∀ g g' : ↥(GK K), χ' g = χ' g' → W.resΓ g = W.resΓ g'`. Introduce `g g' he`. Apply `W.χΓ_inj` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Apply `Subtype.val_injective` to reduce the goal to its premises.

Use `(hlink g).trans ((congrArg _ he).trans (hlink g').symm)` as an intermediate fact. Conclude with `this`. Establish `hχ1 : χ' 1 = 1` using `by simp [χ']`. Establish `hχmul : ∀ a b, χ' (a * b) = χ' a * χ' b` using `fun a b => by`. Simplify using `only [χ', Subgroup.coe_mul, map_mul, Units.val_mul]`.

Establish `hχpow : ∀ a (k : ℕ), χ' (a ^ k) = χ' a ^ k` using `fun a k => by`. Simplify using `only [χ', SubgroupClass.coe_pow, map_pow, Units.val_pow_eq_pow_val]`. Establish `hs : W.s = 1` using `(HW l).W_s K 1 LL h`. Establish `hp2 : ((LT l).PD K).p ≠ 2` using `by rw [P.PD_p K]; exact hl2`. Establish `hgK : W.gamK = W.gam` using `W.gamK_eq_one hs hp2`.

Take `⟨g₁, hg₁⟩` from `W.resΓ_onto W.gam`. Establish `hv : P.v LL (algebraMap ℚ_[l] ↥LL.1 (χ' g₁ - 1)) = 1`. Use `W.gam_gen` as an intermediate fact. Rewrite `this` using `[hs, ← hg₁, hlink g₁]`. Rewrite using `[map_sub, map_one]`.

Simplify using `using this`. Establish `hu : ‖χ' g₁ - 1‖ = (l : ℝ)⁻¹` using `norm_of_v_one P LL _ hv`. Use `haveI : CompactSpace ↥(GK K) := isCompact_iff_compactSpace.1 (InfiniteGalois.fixingSubgroup_isClosed K.1).isCompact`. Establish `hχc : Continuous χ'` using `(chiQ_cont P).comp continuous_subtype_val`. Set `Pg : Subgroup ↥(GK K)` to `(Subgroup.closure (insert W.gamK (W.DelF : Set W.Gam))).comap W.resΓ`.

Establish `hPg : (Pg : Set ↥(GK K)) = PGen (sit LT HW l AI K 1 LL h)` using `rfl`. Set `Q` to `Pg.topologicalClosure`. Establish `hQc : IsClosed (Q : Set ↥(GK K))` using `Pg.isClosed_topologicalClosure`. Establish `hPQ : Pg ≤ Q` using `Pg.le_topologicalClosure`. Establish `hg1 : g₁ ∈ Pg`.

Express the relevant statement in the definitionally equal form `W.resΓ g₁ ∈ Subgroup.closure (insert W.gamK (W.DelF : Set W.Gam))`. Rewrite using `[hg₁, ← hgK]`. Conclude with `Subgroup.subset_closure (Set.mem_insert W.gamK (W.DelF : Set W.Gam))`. Establish `hun : ‖χ' g₁‖ ≤ 1` using `(chiQ_norm P _).le`. Set `uZ : ℤ_[l]` to `⟨χ' g₁, hun⟩`.

Establish `huZ : ‖uZ - 1‖ = (l : ℝ)⁻¹` using `by rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_one]; exact hu`. Establish `happrox : ∀ y : ℤ_[l], ‖y - 1‖ < 1 → ∃ q ∈ Q, χ' q = y`. Introduce `y hy`. Use `choose k hk using fun N => Cyc.pow_approx hl2 uZ huZ y hy N`. Set `x : ℕ → ↥(GK K)` to `fun N => g₁ ^ (k N)`.

Establish `hF : Filter.map x atTop ≤ 𝓟 (Q : Set ↥(GK K))` using `Filter.le_principal_iff.2 (Filter.mem_map.2 (Filter.univ_mem' fun N => hPQ (Pg.pow_mem hg1 _)))`. Take `⟨q, hq, hcl⟩` from `hQc.isCompact.exists_clusterPt hF`. Use `⟨q, hq, ?_⟩` and prove the remaining obligations. Establish `htend : Tendsto χ' (Filter.map x atTop) (𝓝 (y : ℚ_[l]))`. Rewrite using `[tendsto_map'_iff, Metric.tendsto_atTop]`.

Introduce `ε hε`. Establish `hl1 : (l : ℝ)⁻¹ < 1` using `inv_lt_one_of_one_lt₀ (by exact_mod_cast hl.out.one_lt)`. Take `⟨N₀, hN₀⟩` from `exists_pow_lt_of_lt_one hε hl1`. Use `⟨N₀, fun N hN => ?_⟩` and prove the remaining obligations. Rewrite using `[dist_eq_norm]`.

Establish `hx : χ' (x N) = ((uZ ^ k N : ℤ_[l]) : ℚ_[l])`. Rewrite using `[hχpow, PadicInt.coe_pow]`. Rewrite using `[Function.comp_apply, hx, ← PadicInt.coe_sub, ← PadicInt.norm_def]`. Use `lt_of_le_of_lt (hk N) (lt_of_le_of_lt ?_ hN₀)` and prove the remaining obligations. Rewrite using `[zpow_neg, zpow_natCast, ← inv_pow]`.

Conclude with `pow_le_pow_of_le_one (by positivity) hl1.le (by omega)`. Establish `h2` using `hcl.map hχc.continuousAt htend`. Conclude with `eq_of_nhds_neBot h2`. Express the relevant statement in the definitionally equal form `Dense (Pg : Set ↥(GK K))`. Rewrite using `[dense_iff_closure_eq, Set.eq_univ_iff_forall]`.

Introduce `g`. Rewrite using `[← Subgroup.topologicalClosure_coe]`. Establish `hcn : ‖χ' g‖ = 1` using `chiQ_norm P _`. Set `cZ : ℤ_[l]` to `⟨χ' g, hcn.le⟩`. Take `⟨ω, hω, hωc⟩` from `Cyc.teich cZ hcn`.

Establish `hc0 : χ' g ≠ 0` using `by intro h0; rw [h0, norm_zero] at hcn; exact zero_ne_one hcn`. Establish `hωn : ‖(ω : ℚ_[l])‖ = 1`. Establish `: (ω : ℚ_[l]) = χ' g + ((ω : ℚ_[l]) - χ' g)` using `by ring`. Establish `hlt : ‖(ω : ℚ_[l]) - χ' g‖ < ‖χ' g‖` using `by rw [hcn]; exact hωc`. Rewrite using `[this, Padic.add_eq_max_of_ne (ne_of_gt hlt), max_eq_left hlt.le, hcn]`.

Set `yQ : ℚ_[l]` to `(ω : ℚ_[l]) / χ' g`. Establish `hyn : ‖yQ‖ ≤ 1` using `by simp only [yQ, norm_div, hωn, hcn, div_one, le_refl]`. Set `yZ : ℤ_[l]` to `⟨yQ, hyn⟩`. Establish `hy1 : ‖yZ - 1‖ < 1`. Rewrite using `[PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_one]`.

Use `show ‖(ω : ℚ_[l]) / χ' g - 1‖ < 1`. Rewrite using `[div_sub_one hc0, norm_div, hcn, div_one]`. Conclude with `hωc`. Take `⟨q, hq, hqy⟩` from `happrox yZ hy1`. Establish `hgqχ : χ' (g * q) = ω`.

Rewrite using `[hχmul, hqy]`. Use `show χ' g * ((ω : ℚ_[l]) / χ' g) = ω`. Clear the denominators using the available nonvanishing facts. Establish `hgq : g * q ∈ Pg`. Express the relevant statement in the definitionally equal form `W.resΓ (g * q) ∈ Subgroup.closure (insert W.gamK (W.DelF : Set W.Gam))`.

Establish `hpow : W.resΓ (g * q) ^ (l - 1) = 1`. Rewrite using `[← map_pow, ← map_one W.resΓ]`. Apply `hres` to reduce the goal to its premises. Rewrite using `[hχpow, hgqχ, hχ1, ← PadicInt.coe_pow, hω, PadicInt.coe_one]`. Establish `hmem : W.resΓ (g * q) ∈ W.DelF` using `(W.DelF_def _).2 ⟨l - 1, by have := hl.out.two_le; omega, hpow⟩`.

Conclude with `Subgroup.subset_closure (Set.mem_insert_of_mem _ hmem)`. Use `Q.mul_mem (hPQ hgq) (Q.inv_mem hq)` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel_right]`. Then use the resulting hypothesis.
-/
theorem dense_PGen (LT : LocTheory) (HW : HWOf LT) (AI : LocAinf l (LT l)) (K LL : FinExt l)
    (hl2 : l ≠ 2) (h : Good K 1 LL) : Dense (PGen (sit LT HW l AI K 1 LL h)) := by
  let W := (HW l).W K 1 LL h
  let P := LT l
  let χ' : ↥(GK K) → ℚ_[l] := fun g => (P.χQ (g : GQ l) : ℚ_[l])
  have hlink : ∀ g : ↥(GK K), algebraMap ↥(OL LL) ↥LL.1 ((W.χΓ (W.resΓ g) : ↥(OL LL))) =
      algebraMap ℚ_[l] ↥LL.1 (χ' g) := fun g => by
    rw [W.χΓ_res g, P.PD_χ K g]
  have hres : ∀ g g' : ↥(GK K), χ' g = χ' g' → W.resΓ g = W.resΓ g' := by
    intro g g' he
    apply W.χΓ_inj
    apply Units.ext
    apply Subtype.val_injective
    have := (hlink g).trans ((congrArg _ he).trans (hlink g').symm)
    exact this
  have hχ1 : χ' 1 = 1 := by simp [χ']
  have hχmul : ∀ a b, χ' (a * b) = χ' a * χ' b := fun a b => by
    simp only [χ', Subgroup.coe_mul, map_mul, Units.val_mul]
  have hχpow : ∀ a (k : ℕ), χ' (a ^ k) = χ' a ^ k := fun a k => by
    simp only [χ', SubgroupClass.coe_pow, map_pow, Units.val_pow_eq_pow_val]
  have hs : W.s = 1 := (HW l).W_s K 1 LL h
  have hp2 : ((LT l).PD K).p ≠ 2 := by rw [P.PD_p K]; exact hl2
  have hgK : W.gamK = W.gam := W.gamK_eq_one hs hp2
  obtain ⟨g₁, hg₁⟩ := W.resΓ_onto W.gam
  have hv : P.v LL (algebraMap ℚ_[l] ↥LL.1 (χ' g₁ - 1)) = 1 := by
    have := W.gam_gen
    rw [hs, ← hg₁, hlink g₁] at this
    rw [map_sub, map_one]
    simpa using this
  have hu : ‖χ' g₁ - 1‖ = (l : ℝ)⁻¹ := norm_of_v_one P LL _ hv
  haveI : CompactSpace ↥(GK K) :=
    isCompact_iff_compactSpace.1 (InfiniteGalois.fixingSubgroup_isClosed K.1).isCompact
  have hχc : Continuous χ' := (chiQ_cont P).comp continuous_subtype_val
  let Pg : Subgroup ↥(GK K) := (Subgroup.closure (insert W.gamK (W.DelF : Set W.Gam))).comap W.resΓ
  have hPg : (Pg : Set ↥(GK K)) = PGen (sit LT HW l AI K 1 LL h) := rfl
  let Q := Pg.topologicalClosure
  have hQc : IsClosed (Q : Set ↥(GK K)) := Pg.isClosed_topologicalClosure
  have hPQ : Pg ≤ Q := Pg.le_topologicalClosure
  have hg1 : g₁ ∈ Pg := by
    change W.resΓ g₁ ∈ Subgroup.closure (insert W.gamK (W.DelF : Set W.Gam))
    rw [hg₁, ← hgK]
    exact Subgroup.subset_closure (Set.mem_insert W.gamK (W.DelF : Set W.Gam))
  have hun : ‖χ' g₁‖ ≤ 1 := (chiQ_norm P _).le
  let uZ : ℤ_[l] := ⟨χ' g₁, hun⟩
  have huZ : ‖uZ - 1‖ = (l : ℝ)⁻¹ := by rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_one]; exact hu
  have happrox : ∀ y : ℤ_[l], ‖y - 1‖ < 1 → ∃ q ∈ Q, χ' q = y := by
    intro y hy
    choose k hk using fun N => Cyc.pow_approx hl2 uZ huZ y hy N
    let x : ℕ → ↥(GK K) := fun N => g₁ ^ (k N)
    have hF : Filter.map x atTop ≤ 𝓟 (Q : Set ↥(GK K)) :=
      Filter.le_principal_iff.2 (Filter.mem_map.2 (Filter.univ_mem' fun N => hPQ (Pg.pow_mem hg1 _)))
    obtain ⟨q, hq, hcl⟩ := hQc.isCompact.exists_clusterPt hF
    refine ⟨q, hq, ?_⟩
    have htend : Tendsto χ' (Filter.map x atTop) (𝓝 (y : ℚ_[l])) := by
      rw [tendsto_map'_iff, Metric.tendsto_atTop]
      intro ε hε
      have hl1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hl.out.one_lt)
      obtain ⟨N₀, hN₀⟩ := exists_pow_lt_of_lt_one hε hl1
      refine ⟨N₀, fun N hN => ?_⟩
      rw [dist_eq_norm]
      have hx : χ' (x N) = ((uZ ^ k N : ℤ_[l]) : ℚ_[l]) := by
        rw [hχpow, PadicInt.coe_pow]
      rw [Function.comp_apply, hx, ← PadicInt.coe_sub, ← PadicInt.norm_def]
      refine lt_of_le_of_lt (hk N) (lt_of_le_of_lt ?_ hN₀)
      rw [zpow_neg, zpow_natCast, ← inv_pow]
      exact pow_le_pow_of_le_one (by positivity) hl1.le (by omega)
    have h2 := hcl.map hχc.continuousAt htend
    exact eq_of_nhds_neBot h2
  change Dense (Pg : Set ↥(GK K))
  rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro g
  rw [← Subgroup.topologicalClosure_coe]
  have hcn : ‖χ' g‖ = 1 := chiQ_norm P _
  let cZ : ℤ_[l] := ⟨χ' g, hcn.le⟩
  obtain ⟨ω, hω, hωc⟩ := Cyc.teich cZ hcn
  have hc0 : χ' g ≠ 0 := by intro h0; rw [h0, norm_zero] at hcn; exact zero_ne_one hcn
  have hωn : ‖(ω : ℚ_[l])‖ = 1 := by
    have : (ω : ℚ_[l]) = χ' g + ((ω : ℚ_[l]) - χ' g) := by ring
    have hlt : ‖(ω : ℚ_[l]) - χ' g‖ < ‖χ' g‖ := by rw [hcn]; exact hωc
    rw [this, Padic.add_eq_max_of_ne (ne_of_gt hlt), max_eq_left hlt.le, hcn]
  let yQ : ℚ_[l] := (ω : ℚ_[l]) / χ' g
  have hyn : ‖yQ‖ ≤ 1 := by simp only [yQ, norm_div, hωn, hcn, div_one, le_refl]
  let yZ : ℤ_[l] := ⟨yQ, hyn⟩
  have hy1 : ‖yZ - 1‖ < 1 := by
    rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_one]
    show ‖(ω : ℚ_[l]) / χ' g - 1‖ < 1
    rw [div_sub_one hc0, norm_div, hcn, div_one]
    exact hωc
  obtain ⟨q, hq, hqy⟩ := happrox yZ hy1
  have hgqχ : χ' (g * q) = ω := by
    rw [hχmul, hqy]
    show χ' g * ((ω : ℚ_[l]) / χ' g) = ω
    field_simp
  have hgq : g * q ∈ Pg := by
    change W.resΓ (g * q) ∈ Subgroup.closure (insert W.gamK (W.DelF : Set W.Gam))
    have hpow : W.resΓ (g * q) ^ (l - 1) = 1 := by
      rw [← map_pow, ← map_one W.resΓ]
      apply hres
      rw [hχpow, hgqχ, hχ1, ← PadicInt.coe_pow, hω, PadicInt.coe_one]
    have hmem : W.resΓ (g * q) ∈ W.DelF :=
      (W.DelF_def _).2 ⟨l - 1, by have := hl.out.two_le; omega, hpow⟩
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ hmem)
  have := Q.mul_mem (hPQ hgq) (Q.inv_mem hq)
  rwa [mul_inv_cancel_right] at this

/- English proof (translation)
The claim follows from `genFix_of_dense _ (t2Space_lattice_V_of_good_situation LT HW AI K 1 LL h) (dense_PGen LT HW AI K LL hl2 h)`.
-/
theorem genFix_sit (LT : LocTheory) (HW : HWOf LT) (AI : LocAinf l (LT l)) (K LL : FinExt l)
    (hl2 : l ≠ 2) (h : Good K 1 LL) : GenFix (sit LT HW l AI K 1 LL h) :=
  genFix_of_dense _ (t2Space_lattice_V_of_good_situation LT HW AI K 1 LL h) (dense_PGen LT HW AI K LL hl2 h)

end

end GlobalTheory.FixedByDense

namespace GlobalTheory
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

/- English proof (translation)
Introduce `D HW F` and use `Formalism.MainNotions.InvariantsGenerators.InvariantsFromGenerators.invariants_iso_of_generators D HW F (fun l _ K LL hA => Formalism.MainNotions.InvariantsGenerators.InvariantsFromGenerators.oneInj_sit D.loc HW (D.locA l) K 1 LL hA.2.2) (fun l _ K LL hA => FixedByDense.genFix_si …`.
-/
theorem invariants_of_field_of_norms : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Formalism.MainNotions.InvariantsGenerators.H0InvariantsTheorem D HW F :=
  fun D HW F => Formalism.MainNotions.InvariantsGenerators.InvariantsFromGenerators.invariants_iso_of_generators D HW F
    (fun l _ K LL hA => Formalism.MainNotions.InvariantsGenerators.InvariantsFromGenerators.oneInj_sit D.loc HW (D.locA l) K 1 LL hA.2.2)
    (fun l _ K LL hA => FixedByDense.genFix_sit D.loc HW (D.locA l) K LL hA.2.1 hA.2.2)

end GlobalTheory
