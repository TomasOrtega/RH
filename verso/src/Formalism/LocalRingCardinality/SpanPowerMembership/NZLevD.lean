import Formalism.LocalRingCardinality.SpanPowerMembership.NZLevC

open MvPolynomial

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.G.Model

section Rename₂

variable {R σ τ M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]

/- English proof (translation)
Rewrite using `[f.as_sum, map_sum]`. Apply `IsWeightedHomogeneous.sum` to reduce the goal to its premises. Introduce `d hd`. Rewrite using `[rename_monomial]`. Apply `isWeightedHomogeneous_monomial` to reduce the goal to its premises.

Rewrite using `[← hf (mem_support_iff.1 hd), Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum_mapDomain_index (by simp) (by intros; rw [add_smul])]`. Simplify using `only [Finsupp.sum, map_sum, map_nsmul, hL]`.
-/
theorem isWH_rename (g : σ → τ) (w1 : σ → M) (w2 : τ → N) (L : M →+ N) (hL : ∀ x, w2 (g x) = L (w1 x))
    (f : MvPolynomial σ R) (μ : M) (hf : IsWeightedHomogeneous w1 f μ) :
    IsWeightedHomogeneous w2 (rename g f) (L μ) := by
  classical
  rw [f.as_sum, map_sum]
  apply IsWeightedHomogeneous.sum
  intro d hd
  rw [rename_monomial]
  apply isWeightedHomogeneous_monomial
  rw [← hf (mem_support_iff.1 hd), Finsupp.weight_apply, Finsupp.weight_apply,
    Finsupp.sum_mapDomain_index (by simp) (by intros; rw [add_smul])]
  simp only [Finsupp.sum, map_sum, map_nsmul, hL]

/- English proof (translation)
The claim follows from `IsWeightedHomogeneous.prod s φ n h`.
-/
theorem isWH_prod {ι : Type*} (s : Finset ι) (w : σ → M) (φ : ι → MvPolynomial σ R) (n : ι → M)
    (h : ∀ i ∈ s, IsWeightedHomogeneous w (φ i) (n i)) :
    IsWeightedHomogeneous w (∏ i ∈ s, φ i) (∑ i ∈ s, n i) := IsWeightedHomogeneous.prod s φ n h

end Rename₂

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  [CharZero Kf] (P : Places p O Kf)

def om (x : Σ v : Fin P.nV, Fin (P.n' v) × (Fin (P.m + 1) × Fin (P.m + 1))) : Fin P.nV × Fin (P.m + 1) → ℕ :=
  fun y => if y = (x.1, x.2.2.1) then 1 else 0

def atV (v : Fin P.nV) : (Fin (P.m + 1) → ℕ) →+ (Fin P.nV × Fin (P.m + 1) → ℕ) where
  toFun μ := fun y => if y.1 = v then μ y.2 else 0
  map_zero' := by funext y; simp
  map_add' a b := by funext y; by_cases h : y.1 = v <;> simp [h]

/- English proof (translation)
Simplify using `only [blockEmb, Places.vEmb]`. Rewrite using `[rename_rename]`. Use `isWH_rename _ (rowW (P.m + 1) (P.m + 1)) (om P) (atV P v) ?_ f μ hf` and prove the remaining obligations. Introduce `x`. Use function extensionality and compare the values at `y`.

Take `⟨y1, y2⟩` from `y`. Simplify using `only [om, atV, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Function.comp_apply, rowW, Pi.single_apply, Prod.mk.injEq]`. Distinguish the cases in `h1 : y1 = v`. Substitute `h1` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[h1]`.
-/
theorem emb_isWH (v : Fin P.nV) (s : Fin (P.n' v)) (f : MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) Kf)
    (μ : Fin (P.m + 1) → ℕ) (hf : IsWeightedHomogeneous (rowW (P.m + 1) (P.m + 1)) f μ) :
    IsWeightedHomogeneous (om P) (P.vEmb v (blockEmb Kf s f)) (atV P v μ) := by
  simp only [blockEmb, Places.vEmb]
  rw [rename_rename]
  refine isWH_rename _ (rowW (P.m + 1) (P.m + 1)) (om P) (atV P v) ?_ f μ hf
  intro x
  funext y
  obtain ⟨y1, y2⟩ := y
  simp only [om, atV, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Function.comp_apply, rowW, Pi.single_apply,
    Prod.mk.injEq]
  by_cases h1 : y1 = v
  · subst h1
    simp
  · simp [h1]

def wtOf (μ : ∀ v, Fin (P.n' v) → Fin (P.m + 1) → ℕ) : Fin P.nV × Fin (P.m + 1) → ℕ :=
  ∑ v, ∑ s, atV P v (μ v s)

/- English proof (translation)
Simplify using `only [prodF, wtOf]`. Apply `isWH_prod` to reduce the goal to its premises. Introduce `v _`. Rewrite using `[map_prod]`. Apply `isWH_prod` to reduce the goal to its premises.

Introduce `s _`. Conclude with `emb_isWH P v s (F v s) (μ v s) (h v s)`.
-/
theorem prodF_isWH (F : ∀ v, Fin (P.n' v) → MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) Kf)
    (μ : ∀ v, Fin (P.n' v) → Fin (P.m + 1) → ℕ)
    (h : ∀ v s, IsWeightedHomogeneous (rowW (P.m + 1) (P.m + 1)) (F v s) (μ v s)) :
    IsWeightedHomogeneous (om P) (prodF P F) (wtOf P μ) := by
  simp only [prodF, wtOf]
  apply isWH_prod
  intro v _
  rw [map_prod]
  apply isWH_prod
  intro s _
  exact emb_isWH P v s (F v s) (μ v s) (h v s)

/- English proof (translation)
Simplify using `only [wtOf, Finset.sum_apply, atV, AddMonoidHom.coe_mk, ZeroHom.coe_mk]`. Rewrite using `[Finset.sum_eq_single v]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[Ne.symm hb]`.

Simplify using the standard rewrite rules.
-/
theorem wtOf_apply (μ : ∀ v, Fin (P.n' v) → Fin (P.m + 1) → ℕ) (v : Fin P.nV) (a : Fin (P.m + 1)) :
    wtOf P μ (v, a) = ∑ s, μ v s a := by
  simp only [wtOf, Finset.sum_apply, atV, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [Finset.sum_eq_single v]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

/- English proof (translation)
Establish `hpart : ∀ s c, (∑ a : Fin k with a.val < c, μ s a) = ∑ a : Fin k with a.val < c, ν s a`. Introduce `s c`. Establish `htot : ∑ s, (∑ a : Fin k with a.val < c, μ s a) = ∑ s, ∑ a : Fin k with a.val < c, ν s a`. Rewrite using `[Finset.sum_comm]`. Use `conv_rhs => rw [Finset.sum_comm]`.

Conclude with `Finset.sum_congr rfl fun a _ => hsum a`. Conclude with `(Finset.sum_eq_sum_iff_of_le (fun s _ => hdom s c)).1 htot s (Finset.mem_univ s)`. Use function extensionality and compare the values at `s a`. Establish `hs : (Finset.univ.filter fun b : Fin k => b.val < a.val + 1) = insert a (Finset.univ.filter fun b : Fin k => b.val < a.val)`. Use extensionality with `b`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]`. Use linear arithmetic over natural numbers and integers. Establish `hsplit : ∀ f : Fin k → ℕ, (∑ b : Fin k with b.val < a.val + 1, f b) = (∑ b : Fin k with b.val < a.val, f b) + f a`. Introduce `f`. Rewrite using `[hs, Finset.sum_insert (by simp), add_comm]`.

Establish `h1` using `hpart s (a.val + 1)`. Rewrite `h1` using `[hsplit (μ s), hsplit (ν s), hpart s a.val]`. Conclude with `Nat.add_left_cancel h1`.
-/
theorem eq_of_dom {S : Type*} [Fintype S] {k : ℕ} (μ ν : S → Fin k → ℕ)
    (hdom : ∀ s (c : ℕ), (∑ a : Fin k with a.val < c, μ s a) ≤ ∑ a : Fin k with a.val < c, ν s a)
    (hsum : ∀ a, ∑ s, μ s a = ∑ s, ν s a) : μ = ν := by
  have hpart : ∀ s c, (∑ a : Fin k with a.val < c, μ s a) = ∑ a : Fin k with a.val < c, ν s a := by
    intro s c
    have htot : ∑ s, (∑ a : Fin k with a.val < c, μ s a) = ∑ s, ∑ a : Fin k with a.val < c, ν s a := by
      rw [Finset.sum_comm]
      conv_rhs => rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun a _ => hsum a
    exact (Finset.sum_eq_sum_iff_of_le (fun s _ => hdom s c)).1 htot s (Finset.mem_univ s)
  funext s a
  have hs : (Finset.univ.filter fun b : Fin k => b.val < a.val + 1) =
      insert a (Finset.univ.filter fun b : Fin k => b.val < a.val) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  have hsplit : ∀ f : Fin k → ℕ,
      (∑ b : Fin k with b.val < a.val + 1, f b) = (∑ b : Fin k with b.val < a.val, f b) + f a := by
    intro f
    rw [hs, Finset.sum_insert (by simp), add_comm]
  have h1 := hpart s (a.val + 1)
  rw [hsplit (μ s), hsplit (ν s), hpart s a.val] at h1
  exact Nat.add_left_cancel h1

instance : Infinite Kf := Infinite.of_injective (Nat.cast : ℕ → Kf) Nat.cast_injective

/- English proof (translation)
Unfold `bV`. Use `generalize_proofs hh`. Introduce `h0`. Establish `h1` using `(hh.choose_spec.2 i).2.1`. Rewrite `h1` using `[h0, MonomialOrder.leadingCoeff_zero]`.

Conclude with `zero_ne_one h1`.
-/
theorem bV_ne (v : Fin P.nV) (s : Fin (P.n' v)) (i : IdxV P v s) : bV P v s i ≠ 0 := by
  unfold bV
  generalize_proofs hh
  intro h0
  have h1 := (hh.choose_spec.2 i).2.1
  rw [h0, MonomialOrder.leadingCoeff_zero] at h1
  exact zero_ne_one h1

/- English proof (translation)
Take `⟨_, _, hb⟩` from `Formalism.MainNotions.G.LatticeSystems.lb_basis Kf (P.m + 1) (P.m + 1) (nuV P v s)`. Conclude with `hb i c`.
-/
theorem bV_dom (v : Fin P.nV) (s : Fin (P.n' v)) (i : IdxV P v s) (c : ℕ) :
    (∑ a : Fin (P.m + 1) with a.val < c, rowWt i.1 a) ≤ ∑ a : Fin (P.m + 1) with a.val < c, nuV P v s a := by
  obtain ⟨_, _, hb⟩ := Formalism.MainNotions.G.LatticeSystems.lb_basis Kf (P.m + 1) (P.m + 1) (nuV P v s)
  exact hb i c

/- English proof (translation)
Establish `hanti : Antitone (nuV P v s)`. Unfold `nuV`. Conclude with `Formalism.MainNotions.G.LatticeSystems.kp_nuOf_antitone _ (Formalism.MainNotions.G.LatticeSystems.kp_lamAt_antitone _ (P.dom v) s)`. Unfold `bV`. Use `generalize_proofs hh`.

Take `⟨⟨_, hspan, hhom⟩, _⟩` from `hh.choose_spec`. Establish `hmem : hh.choose i ∈ dualWeyl Kf (P.m + 1) (P.m + 1) (nuV P v s)`. Rewrite using `[← hspan]`. Conclude with `Submodule.subset_span ⟨i, rfl⟩`. Establish `hwt : IsWeightedHomogeneous (rowW (P.m + 1) (P.m + 1)) (hh.choose i) (rowNu (r` using `P.m + 1) (nuV P v s)) := by`.

Establish `e : rowNu (r` using `P.m + 1) (nuV P v s) = nuV P v s := by`. Use function extensionality and compare the values at `a`. Simplify using `[rowNu, a.isLt]`. Establish `h2 : IsWeightedHomogeneous (rowW (P.m + 1) (P.m + 1)) (hh.choose i) (rowWt i.1)` using `hhom i`. Rewrite `h2` using `[h]`.

Rewrite using `[e]`. Conclude with `h2`. Conclude with `⟨_, Formalism.L2.G.Model.sw_line Kf le_rfl (nuV P v s) hanti _ hmem hwt⟩`.
-/
theorem bV_top (v : Fin P.nV) (s : Fin (P.n' v)) (i : IdxV P v s) (h : rowWt i.1 = nuV P v s) :
    ∃ c : Kf, bV P v s i = c • hw Kf le_rfl (nuV P v s) := by
  have hanti : Antitone (nuV P v s) := by
    unfold nuV
    exact Formalism.MainNotions.G.LatticeSystems.kp_nuOf_antitone _ (Formalism.MainNotions.G.LatticeSystems.kp_lamAt_antitone _ (P.dom v) s)
  unfold bV
  generalize_proofs hh
  obtain ⟨⟨_, hspan, hhom⟩, _⟩ := hh.choose_spec
  have hmem : hh.choose i ∈ dualWeyl Kf (P.m + 1) (P.m + 1) (nuV P v s) := by
    rw [← hspan]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hwt : IsWeightedHomogeneous (rowW (P.m + 1) (P.m + 1)) (hh.choose i)
      (rowNu (r := P.m + 1) (nuV P v s)) := by
    have e : rowNu (r := P.m + 1) (nuV P v s) = nuV P v s := by
      funext a
      simp [rowNu, a.isLt]
    have h2 : IsWeightedHomogeneous (rowW (P.m + 1) (P.m + 1)) (hh.choose i) (rowWt i.1) := hhom i
    rw [h] at h2
    rw [e]
    exact h2
  exact ⟨_, Formalism.L2.G.Model.sw_line Kf le_rfl (nuV P v s) hanti _ hmem hwt⟩

/- English proof (translation)
Simplify using `only [prodF, smul_eq_C_mul, map_mul, Finset.prod_mul_distrib, map_prod]`. Simplify using `[Places.vEmb, blockEmb, rename_C, ← map_prod]`.
-/
theorem prodF_smul (c : ∀ v, Fin (P.n' v) → Kf) (F : ∀ v, Fin (P.n' v) → MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) Kf) :
    prodF P (fun v s => c v s • F v s) = (∏ v, ∏ s, c v s) • prodF P F := by
  simp only [prodF, smul_eq_C_mul, map_mul, Finset.prod_mul_distrib, map_prod]
  simp [Places.vEmb, blockEmb, rename_C, ← map_prod]

abbrev LamTot : Fin P.nV × Fin (P.m + 1) → ℕ := wtOf P (nuV P)

/- English proof (translation)
Establish `hBI : ∀ I, BI P I = prodF P (fun v s => bV P v s (I v s))` using `fun I => rfl`. Establish `hEV : EV P = prodF P (fun v s => hw Kf le_rfl (nuV P v s))` using `rfl`. Establish `hwtI : ∀ I, IsWeightedHomogeneous (om P) (BI P I) (wtOf P (fun v s => rowWt (I v s).1))`. Introduce `I`. Rewrite using `[hBI]`.

Apply `prodF_isWH` to reduce the goal to its premises. Introduce `v s`. Use `show IsWeightedHomogeneous _ (bV P v s (I v s)) (rowWt (I v s).1)`. Unfold `bV`. Use `generalize_proofs hh`.

Conclude with `hh.choose_spec.1.2.2 (I v s)`. Establish `htop : ∀ I, wtOf P (fun v s => rowWt (I v s).1) = LamTot P → BI P I ∈ Submodule.span Kf {EV P}`. Introduce `I hI`. Establish `hall : ∀ v s, rowWt (I v s).1 = nuV P v s`. Introduce `v`.

Establish `hv` using `eq_of_dom (fun s => rowWt (I v s).1) (fun s => nuV P v s) (fun s c => bV_dom P v s (I v s) c) (by`. Introduce `a`. Establish `h1` using `congrFun hI (v, a)`. Simplify using `only [LamTot, wtOf_apply] at h1`. Conclude with `h1)`.

Conclude with `fun s => congrFun hv s`. Establish `hc : ∀ v s, ∃ c : Kf, bV P v s (I v s) = c • hw Kf le_rfl (nuV P v s)` using `fun v s => bV_top P v s (I v s) (hall v s)`. Use `choose c hc using hc`. Establish `hF : (fun v s => bV P v s (I v s)) = (fun v s => c v s • hw Kf le_rfl (nuV P v s))`. Use function extensionality and compare the values at `v s`.

Conclude with `hc v s`. Rewrite using `[hBI, hF, prodF_smul, ← hEV]`. Conclude with `Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)`. Take `⟨f, hf⟩` from `Finsupp.mem_span_range_iff_exists_finsupp.1 he`. Establish `hcomp : weightedHomogeneousComponent (om P) (LamTot P) e = e`.

Rewrite using `[weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).2 hwt), if_pos rfl]`. Establish `hmem : e ∈ Submodule.span Kf {EV P}`. Rewrite using `[← hcomp, ← hf, Finsupp.sum, map_sum]`. Use `Submodule.sum_mem _ fun I _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul]`.

Use `Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Distinguish the cases in `hI : wtOf P (fun v s => rowWt (I v s).1) = LamTot P`. Establish `h3` using `hwtI I`. Rewrite `h3` using `[hI]`. Rewrite using `[weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).2 h3), if_pos rfl]`.

Conclude with `htop I hI`. Rewrite using `[weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).2 (hwtI I)), if_neg (Ne.symm hI)]`. Conclude with `Submodule.zero_mem _`. Take `⟨c, hc⟩` from `Submodule.mem_span_singleton.1 hmem`. Conclude with `⟨c, hc.symm⟩`.
-/
theorem mem_line (e : P.Xsp) (he : e ∈ Submodule.span Kf (Set.range (BI P)))
    (hwt : IsWeightedHomogeneous (om P) e (LamTot P)) : ∃ c : Kf, e = c • EV P := by
  classical
  have hBI : ∀ I, BI P I = prodF P (fun v s => bV P v s (I v s)) := fun I => rfl
  have hEV : EV P = prodF P (fun v s => hw Kf le_rfl (nuV P v s)) := rfl
  have hwtI : ∀ I, IsWeightedHomogeneous (om P) (BI P I) (wtOf P (fun v s => rowWt (I v s).1)) := by
    intro I
    rw [hBI]
    apply prodF_isWH
    intro v s
    show IsWeightedHomogeneous _ (bV P v s (I v s)) (rowWt (I v s).1)
    unfold bV
    generalize_proofs hh
    exact hh.choose_spec.1.2.2 (I v s)
  have htop : ∀ I, wtOf P (fun v s => rowWt (I v s).1) = LamTot P →
      BI P I ∈ Submodule.span Kf {EV P} := by
    intro I hI
    have hall : ∀ v s, rowWt (I v s).1 = nuV P v s := by
      intro v
      have hv := eq_of_dom (fun s => rowWt (I v s).1) (fun s => nuV P v s)
        (fun s c => bV_dom P v s (I v s) c) (by
          intro a
          have h1 := congrFun hI (v, a)
          simp only [LamTot, wtOf_apply] at h1
          exact h1)
      exact fun s => congrFun hv s
    have hc : ∀ v s, ∃ c : Kf, bV P v s (I v s) = c • hw Kf le_rfl (nuV P v s) :=
      fun v s => bV_top P v s (I v s) (hall v s)
    choose c hc using hc
    have hF : (fun v s => bV P v s (I v s)) = (fun v s => c v s • hw Kf le_rfl (nuV P v s)) := by
      funext v s
      exact hc v s
    rw [hBI, hF, prodF_smul, ← hEV]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  obtain ⟨f, hf⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 he
  have hcomp : weightedHomogeneousComponent (om P) (LamTot P) e = e := by
    rw [weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).2 hwt), if_pos rfl]
  have hmem : e ∈ Submodule.span Kf {EV P} := by
    rw [← hcomp, ← hf, Finsupp.sum, map_sum]
    refine Submodule.sum_mem _ fun I _ => ?_
    rw [map_smul]
    refine Submodule.smul_mem _ _ ?_
    by_cases hI : wtOf P (fun v s => rowWt (I v s).1) = LamTot P
    · have h3 := hwtI I
      rw [hI] at h3
      rw [weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).2 h3), if_pos rfl]
      exact htop I hI
    · rw [weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).2 (hwtI I)), if_neg (Ne.symm hI)]
      exact Submodule.zero_mem _
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
  exact ⟨c, hc.symm⟩

end Formalism.BasicNotions.Examples₂.NZ
