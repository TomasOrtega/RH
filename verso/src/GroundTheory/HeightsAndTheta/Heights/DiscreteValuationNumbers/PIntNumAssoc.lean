import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp`. Consider the case `cons a l ih => simp [ih, Finset.sum_add_distrib]`.
-/
theorem IntNumAssoc.list_sum_finset_sum {α β : Type*} (l : List α) (s : Finset β)
    (f : α → β → ℤ) :
    (l.map fun a => ∑ b ∈ s, f a b).sum = ∑ b ∈ s, (l.map fun a => f a b).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, Finset.sum_add_distrib]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp`. Consider the case `cons a l ih => by_cases h : P a <;> simp [h, ih]`.
-/
theorem IntNumAssoc.list_sum_ite_enat {α : Type*} (l : List α) (P : α → Prop) [DecidablePred P] :
    (l.map fun a => if P a then (1 : ℕ∞) else 0).sum =
      ((l.map fun a => if P a then (1 : ℕ) else 0).sum : ℕ) := by
  induction l with
  | nil => simp
  | cons a l ih => by_cases h : P a <;> simp [h, ih]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp`. Consider the case `cons a l ih => by_cases h : P a <;> simp [h, ih, add_mul]`.
-/
theorem IntNumAssoc.list_sum_ite_mul {α : Type*} (l : List α) (P : α → Prop) [DecidablePred P]
    (c : ℤ) :
    (l.map fun a => if P a then c else 0).sum =
      ((l.map fun a => if P a then (1 : ℕ) else 0).sum : ℤ) * c := by
  induction l with
  | nil => simp
  | cons a l ih => by_cases h : P a <;> simp [h, ih, add_mul]

/- English proof (translation)
Introduce `F _ K _ _ ι _ n J hJ hdim bs`. Take `⟨l, hl, hhilb, hmult⟩` from `h1 F K ι J hJ`. Establish `hdimp : ∀ p ∈ l, ringKrullDim (MRing ι F ⧸ p.1) < ((n + 1 + Fintype.card K : ℕ) : WithBot ℕ∞)` using `fun p hp => lt_of_le_of_lt (ringKrullDim_le_of_surjective (Ideal.Quotient.factor (hl p hp).2.2) (Ideal.Quotient.factor_surjective (hl p hp).2.2)) hdim`. Establish `hdeg : ∀ p ∈ l, DegLT (hilbFn p.1) (n + 1)` using `fun p hp => h6 F K ι (n + 1) p.1 (hl p hp).1 (hl p hp).2.1 (hdimp p hp)`. Rewrite using `[h2 F K ι n J l hdeg hhilb bs]`.

Establish `hfin` using `Ideal.finite_minimalPrimes_of_isNoetherianRing (MRing ι F) J`. Establish `hp : ∀ p ∈ l, intNum F p.1 bs = ∑ W ∈ hfin.toFinset, if p.1 = W then (if IsRelevant W then intNum F W bs else 0) else 0`. Introduce `p hpl`. Rewrite using `[Finset.sum_ite_eq]`. Distinguish the cases in `hz : intNum F p.1 bs = 0`.

Rewrite using `[hz]`. Simplify using the standard rewrite rules. Use `(hl p hpl).1` as an intermediate fact. Establish `hrel : IsRelevant p.1`. Assume the negation of the conclusion as `hr`.

Conclude with `hz (h4 F K ι n p.1 (hl p hpl).1 (hl p hpl).2.1 (Or.inl hr) bs)`. Establish `hbig : ¬ ringKrullDim (MRing ι F ⧸ p.1) < ((n + Fintype.card K : ℕ) : WithBot ℕ∞)` using `fun hs => hz (h4 F K ι n p.1 (hl p hpl).1 (hl p hpl).2.1 (Or.inr hs) bs)`. Establish `hJ' : ringKrullDim (MRing ι F ⧸ J) < ((n + Fintype.card K + 1 : ℕ) : WithBot ℕ∞)`. Establish `e : n + Fintype.card K + 1 = n + 1 + Fintype.card K` using `by omega`. Rewrite using `[e]`.

Conclude with `hdim`. Establish `hmin` using `h5 _ J p.1 (n + Fintype.card K) (hl p hpl).2.2 hJ' hbig`. Rewrite using `[if_pos (hfin.mem_toFinset.mpr hmin), if_pos hrel]`. Establish `hl2 : (l.map fun p => intNum F p.1 bs) = l.map fun p => ∑ W ∈ hfin.toFinset, if p.1 = W then (if IsRelevant W then intNum F W bs else 0) else 0` using `List.map_congr_left hp`. Rewrite using `[hl2, IntNumAssoc.list_sum_finset_sum]`.

Establish `hsupp : Function.support (fun W => idealCycle J W * intNum F W bs) ⊆ (hfin.toFinset : Set (Ideal (MRing ι F)))`. Introduce `W hW`. Rewrite using `[Finset.mem_coe, Set.Finite.mem_toFinset]`. Assume the negation of the conclusion as `hn`. Apply `Function.mem_support.mp hW` to reduce the goal to its premises.

Unfold `idealCycle`. Rewrite using `[dif_neg (fun h => hn h.1), zero_mul]`. Unfold `cycEval`. Rewrite using `[finsum_eq_finsetSum_of_support_subset _ hsupp]`. Use `Finset.sum_congr rfl fun W hW => ?_` and prove the remaining obligations.

Establish `hWm : W ∈ J.minimalPrimes` using `hfin.mem_toFinset.mp hW`. Establish `: W.IsPrime` using `hWm.1.1`. Rewrite using `[IntNumAssoc.list_sum_ite_mul]`. Unfold `idealCycle`. Distinguish the cases in `hr : IsRelevant W`.

Rewrite using `[dif_pos ⟨hWm, hr⟩, if_pos hr]`. Establish `hcount : multAt J W = (l.map fun p => if p.1 = W then (1 : ℕ∞) else 0).sum`. Rewrite using `[hmult W]`. Use `congr 1`. Apply `List.map_congr_left` to reduce the goal to its premises.

Introduce `p hpl`. Use `(hl p hpl).1` as an intermediate fact. Conclude with `h3 F K ι J p.1 W (hl p hpl).2.2 hWm`. Rewrite using `[hcount, IntNumAssoc.list_sum_ite_enat, ENat.toNat_natCast]`. Rewrite using `[dif_neg (fun h => hr h.2), if_neg hr]`.

Simplify using the standard rewrite rules.
-/
theorem IntNumAssoc.proof (h1 : PrimeFiltration.Statement.{u})
    (h2 : IntNumOfFiltration.Statement.{u}) (h3 : MultAtPrimeAtMinimal.Statement.{u})
    (h4 : IntNumVanish.Statement.{u}) (h5 : TopDimMinimal.Statement.{u})
    (h6 : HilbDegBound.Statement.{u}) : IntNumAssoc.Statement.{u} := by
  classical
  intro F _ K _ _ ι _ n J hJ hdim bs
  obtain ⟨l, hl, hhilb, hmult⟩ := h1 F K ι J hJ
  have hdimp : ∀ p ∈ l, ringKrullDim (MRing ι F ⧸ p.1) <
      ((n + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) := fun p hp =>
    lt_of_le_of_lt (ringKrullDim_le_of_surjective (Ideal.Quotient.factor (hl p hp).2.2)
      (Ideal.Quotient.factor_surjective (hl p hp).2.2)) hdim
  have hdeg : ∀ p ∈ l, DegLT (hilbFn p.1) (n + 1) := fun p hp =>
    h6 F K ι (n + 1) p.1 (hl p hp).1 (hl p hp).2.1 (hdimp p hp)
  rw [h2 F K ι n J l hdeg hhilb bs]
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing (MRing ι F) J
  have hp : ∀ p ∈ l, intNum F p.1 bs =
      ∑ W ∈ hfin.toFinset, if p.1 = W then (if IsRelevant W then intNum F W bs else 0) else 0 := by
    intro p hpl
    rw [Finset.sum_ite_eq]
    by_cases hz : intNum F p.1 bs = 0
    · rw [hz]
      simp
    · have := (hl p hpl).1
      have hrel : IsRelevant p.1 := by
        by_contra hr
        exact hz (h4 F K ι n p.1 (hl p hpl).1 (hl p hpl).2.1 (Or.inl hr) bs)
      have hbig : ¬ ringKrullDim (MRing ι F ⧸ p.1) <
          ((n + Fintype.card K : ℕ) : WithBot ℕ∞) := fun hs =>
        hz (h4 F K ι n p.1 (hl p hpl).1 (hl p hpl).2.1 (Or.inr hs) bs)
      have hJ' : ringKrullDim (MRing ι F ⧸ J) <
          ((n + Fintype.card K + 1 : ℕ) : WithBot ℕ∞) := by
        have e : n + Fintype.card K + 1 = n + 1 + Fintype.card K := by omega
        rw [e]
        exact hdim
      have hmin := h5 _ J p.1 (n + Fintype.card K) (hl p hpl).2.2 hJ' hbig
      rw [if_pos (hfin.mem_toFinset.mpr hmin), if_pos hrel]
  have hl2 : (l.map fun p => intNum F p.1 bs) = l.map fun p =>
      ∑ W ∈ hfin.toFinset, if p.1 = W then (if IsRelevant W then intNum F W bs else 0) else 0 :=
    List.map_congr_left hp
  rw [hl2, IntNumAssoc.list_sum_finset_sum]
  have hsupp : Function.support (fun W => idealCycle J W * intNum F W bs) ⊆
      (hfin.toFinset : Set (Ideal (MRing ι F))) := by
    intro W hW
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    by_contra hn
    apply Function.mem_support.mp hW
    unfold idealCycle
    rw [dif_neg (fun h => hn h.1), zero_mul]
  unfold cycEval
  rw [finsum_eq_finsetSum_of_support_subset _ hsupp]
  refine Finset.sum_congr rfl fun W hW => ?_
  have hWm : W ∈ J.minimalPrimes := hfin.mem_toFinset.mp hW
  have : W.IsPrime := hWm.1.1
  rw [IntNumAssoc.list_sum_ite_mul]
  unfold idealCycle
  by_cases hr : IsRelevant W
  · rw [dif_pos ⟨hWm, hr⟩, if_pos hr]
    have hcount : multAt J W = (l.map fun p => if p.1 = W then (1 : ℕ∞) else 0).sum := by
      rw [hmult W]
      congr 1
      apply List.map_congr_left
      intro p hpl
      have := (hl p hpl).1
      exact h3 F K ι J p.1 W (hl p hpl).2.2 hWm
    rw [hcount, IntNumAssoc.list_sum_ite_enat, ENat.toNat_natCast]
  · rw [dif_neg (fun h => hr h.2), if_neg hr]
    simp

end GroundTheory.Heights₂.Heights.NumbersDVR
