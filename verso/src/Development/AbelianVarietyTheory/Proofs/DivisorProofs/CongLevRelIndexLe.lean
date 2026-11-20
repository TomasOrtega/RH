import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecEq
import Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.AdeleIntA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleMod
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.CongIdx

variable {D : D7}

/- English proof (translation)
The claim follows from `Subring.subset_closure (Or.inl ⟨⟨(a : D.host.E), ⟨a, rfl⟩⟩, rfl⟩)`.
-/
theorem inc_int_mem (a : 𝓞 D.host.E) : inc D (a : D.host.E) ∈ OhE D :=
  Subring.subset_closure (Or.inl ⟨⟨(a : D.host.E), ⟨a, rfl⟩⟩, rfl⟩)

/- English proof (translation)
Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨b, hb, s, hs, rfl⟩` from `hy`. Conclude with `AddSubgroup.subset_closure ⟨b, hb, s * t, mul_mem hs ht, by ring⟩`. Consider the case `zero => rw [mul_zero]`.

Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [mul_add]`. Conclude with `add_mem hx hy`. Consider the case `neg x _ hx => rw [mul_neg]`. Conclude with `neg_mem hx`.
-/
theorem mul_mem_hatId {𝔪 : Ideal (𝓞 D.host.E)} {t y : AE D} (ht : t ∈ OhE D) (hy : y ∈ hatId D 𝔪) :
    t * y ∈ hatId D 𝔪 := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨b, hb, s * t, mul_mem hs ht, by ring⟩
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg]; exact neg_mem hx

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.AdeleTensorModule.main`. Consider the case `exact _root_.GlobalTheory.AdeleTensorModule.main`. Consider the case `(apply _root_.GlobalTheory.AdeleTensorModule.main <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.AdeleTensorModule.main <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.AdeleTensorModule.main <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.AdeleTensorModule.main ..)`.
-/
theorem ohE_approx (N : ℕ) (hN : 1 ≤ N) (x : AE D) (hx : x ∈ OhE D) :
    ∃ a ∈ Formalism.UG.intOE D.host.E, ∃ z ∈ OhE D, x = inc D a + (N : AE D) * z := by
  first
  | exact @_root_.GlobalTheory.AdeleTensorModule.main
  | exact _root_.GlobalTheory.AdeleTensorModule.main
  | (apply _root_.GlobalTheory.AdeleTensorModule.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.AdeleTensorModule.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AdeleTensorModule.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AdeleTensorModule.main ..)

/- English proof (translation)
Establish `hN : 1 ≤ Ideal.absNorm 𝔪` using `Nat.one_le_iff_ne_zero.2 (Ideal.absNorm_eq_zero_iff.not.2 h𝔪)`. Take `⟨a0, ⟨a, rfl⟩, z, hz, e⟩` from `ohE_approx _ hN x hx`. Use `⟨a, ?_⟩` and prove the remaining obligations. Establish `e2 : x - inc D (algebraMap (𝓞 D.host.E) D.host.E a) = (Ideal.absNorm 𝔪 : AE D) * z`. Rewrite using `[e]`.

Expand and normalize the polynomial expressions, which then agree. Establish `e3 : inc D (((Ideal.absNorm 𝔪 : ℕ) : 𝓞 D.host.E) : D.host.E) = (Ideal.absNorm 𝔪 : AE D)`. Simplify using the standard rewrite rules. Rewrite using `[show ((a : D.host.E)) = algebraMap (𝓞 D.host.E) D.host.E a from rfl, e2, ← e3]`. Conclude with `AddSubgroup.subset_closure ⟨_, Ideal.absNorm_mem 𝔪, z, hz, rfl⟩`.
-/
theorem exists_rep {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) {x : AE D} (hx : x ∈ OhE D) :
    ∃ a : 𝓞 D.host.E, x - inc D (a : D.host.E) ∈ hatId D 𝔪 := by
  have hN : 1 ≤ Ideal.absNorm 𝔪 := Nat.one_le_iff_ne_zero.2 (Ideal.absNorm_eq_zero_iff.not.2 h𝔪)
  obtain ⟨a0, ⟨a, rfl⟩, z, hz, e⟩ := ohE_approx _ hN x hx
  refine ⟨a, ?_⟩
  have e2 : x - inc D (algebraMap (𝓞 D.host.E) D.host.E a) = (Ideal.absNorm 𝔪 : AE D) * z := by
    rw [e]; ring
  have e3 : inc D (((Ideal.absNorm 𝔪 : ℕ) : 𝓞 D.host.E) : D.host.E) = (Ideal.absNorm 𝔪 : AE D) := by
    simp
  rw [show ((a : D.host.E)) = algebraMap (𝓞 D.host.E) D.host.E a from rfl, e2, ← e3]
  exact AddSubgroup.subset_closure ⟨_, Ideal.absNorm_mem 𝔪, z, hz, rfl⟩

/- English proof (translation)
Use `Subgroup.subset_closure ⟨mul_mem (inv_mem hk) hk', fun i j => ?_⟩` and prove the remaining obligations. Establish `hi` using `(mem_intG k).1 hk`. Establish `e : (((k⁻¹ * k' : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) - 1 = (((k : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) * (((k' : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) - ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N …`. Rewrite using `[Matrix.mul_sub, ← Units.val_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]`. Both sides reduce to the same expression.

Rewrite using `[e, Matrix.mul_apply]`. Conclude with `sum_mem fun l _ => mul_mem_hatId (hi i l).2 (h l j)`.
-/
theorem inv_mul_mem {𝔪 : Ideal (𝓞 D.host.E)} {N : ℕ} {k k' : GA D N} (hk : k ∈ intG D N) (hk' : k' ∈ intG D N)
    (h : ∀ i j, ((k' : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j -
      ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j ∈ hatId D 𝔪) :
    k⁻¹ * k' ∈ congLev D 𝔪 N := by
  refine Subgroup.subset_closure ⟨mul_mem (inv_mem hk) hk', fun i j => ?_⟩
  have hi := (mem_intG k).1 hk
  have e : (((k⁻¹ * k' : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) - 1 =
      (((k : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) *
        (((k' : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) -
          ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))) := by
    rw [Matrix.mul_sub, ← Units.val_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    rfl
  rw [e, Matrix.mul_apply]
  exact sum_mem fun l _ => mul_mem_hatId (hi i l).2 (h l j)

end GlobalTheory.CongIdx

open GlobalTheory.CongIdx in

/- English proof (translation)
Introduce `D 𝔪 h𝔪 N`. Establish `hrep : ∀ x : AE D, ∃ a : 𝓞 D.host.E, x ∈ OhE D → x - inc D (a : D.host.E) ∈ hatId D 𝔪` using `fun x => by`. Distinguish the cases in `hx : x ∈ OhE D`. Take `⟨a, ha⟩` from `exists_rep h𝔪 hx`. Conclude with `⟨a, fun _ => ha⟩`.

Conclude with `⟨0, fun h => absurd h hx⟩`. Use `choose r hr using hrep`. Set `f : intG D N → (Fin N → Fin N → 𝓞 D.host.E ⧸ 𝔪)` to `fun k i j => Ideal.Quotient.mk 𝔪 (r ((((k : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j))`. Set `g : intG D N ⧸ (congLev D 𝔪 N).subgroupOf (intG D N) → (Fin N → Fin N → 𝓞 D.host.E ⧸ 𝔪)` to `fun q => f q.out`. Establish `hg : Function.Injective g`.

Introduce `q1 q2 h`. Rewrite using `[← QuotientGroup.out_eq' q1, ← QuotientGroup.out_eq' q2, QuotientGroup.eq, Subgroup.mem_subgroupOf]`. Establish `hk` using `(q1.out).2`. Establish `hk'` using `(q2.out).2`. Use `(show ((q1.out⁻¹ * q2.out : intG D N) : GA D N) = (q1.out : GA D N)⁻¹ * q2.out from rfl) ▸ inv_mul_mem hk hk' fun i j => ?_` and prove the remaining obligations.

Establish `h1` using `hr _ ((mem_intG _).1 hk i j).1`. Establish `h2` using `hr _ ((mem_intG _).1 hk' i j).1`. Establish `h3 : r ((((q2.out : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j) - r ((((q1.out : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j) ∈ 𝔪` using `Ideal.Quotient.eq.1 (congr_fun (congr_fun h i) j).symm`. Establish `h4 : inc D (((r ((((q2.out : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j) - r ((((q1.out : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j) : 𝓞 D.host.E) : D.host.E)) * 1 ∈ hatId D 𝔪` using `AddSubgroup.subset_closure ⟨_, h3, 1, one_mem _, rfl⟩`. Establish `h5` using `add_mem (sub_mem h2 h1) h4`.

Use `h5 using 1` and compare the differences between its conclusion and the goal. Use `push_cast`. Simplify using `only [map_sub, mul_one]`. Expand and normalize the polynomial expressions, which then agree. Establish `hfin : Ideal.absNorm 𝔪 ≠ 0` using `Ideal.absNorm_eq_zero_iff.not.2 h𝔪`.

Establish `hcard : Nat.card (𝓞 D.host.E ⧸ 𝔪) = Ideal.absNorm 𝔪`. Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Use `haveI : Finite (𝓞 D.host.E ⧸ 𝔪) := Nat.finite_of_card_ne_zero (hcard ▸ hfin)`. Use `haveI : Finite (intG D N ⧸ (congLev D 𝔪 N).subgroupOf (intG D N)) := Finite.of_injective g hg`. Establish `hle` using `Nat.card_le_card_of_injective g hg`.

Rewrite `hle` using `[Nat.card_fun, Nat.card_fun, hcard, Nat.card_fin, ← pow_mul]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `Subgroup.index_ne_zero_of_finite`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem GlobalTheory.congLev_relIndex_le : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ N : ℕ,
    (congLev D 𝔪 N).relIndex (intG D N) ≠ 0 ∧ (congLev D 𝔪 N).relIndex (intG D N) ≤ Ideal.absNorm 𝔪 ^ (N ^ 2) := by
  intro D 𝔪 h𝔪 N
  classical
  have hrep : ∀ x : AE D, ∃ a : 𝓞 D.host.E, x ∈ OhE D → x - inc D (a : D.host.E) ∈ hatId D 𝔪 := fun x => by
    by_cases hx : x ∈ OhE D
    · obtain ⟨a, ha⟩ := exists_rep h𝔪 hx
      exact ⟨a, fun _ => ha⟩
    · exact ⟨0, fun h => absurd h hx⟩
  choose r hr using hrep
  let f : intG D N → (Fin N → Fin N → 𝓞 D.host.E ⧸ 𝔪) := fun k i j =>
    Ideal.Quotient.mk 𝔪 (r ((((k : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j))
  let g : intG D N ⧸ (congLev D 𝔪 N).subgroupOf (intG D N) → (Fin N → Fin N → 𝓞 D.host.E ⧸ 𝔪) :=
    fun q => f q.out
  have hg : Function.Injective g := by
    intro q1 q2 h
    rw [← QuotientGroup.out_eq' q1, ← QuotientGroup.out_eq' q2, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have hk := (q1.out).2
    have hk' := (q2.out).2
    refine (show ((q1.out⁻¹ * q2.out : intG D N) : GA D N) = (q1.out : GA D N)⁻¹ * q2.out from rfl) ▸
      inv_mul_mem hk hk' fun i j => ?_
    have h1 := hr _ ((mem_intG _).1 hk i j).1
    have h2 := hr _ ((mem_intG _).1 hk' i j).1
    have h3 : r ((((q2.out : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j) -
        r ((((q1.out : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j) ∈ 𝔪 :=
      Ideal.Quotient.eq.1 (congr_fun (congr_fun h i) j).symm
    have h4 : inc D (((r ((((q2.out : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j) -
        r ((((q1.out : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j) : 𝓞 D.host.E) : D.host.E)) * 1 ∈
        hatId D 𝔪 := AddSubgroup.subset_closure ⟨_, h3, 1, one_mem _, rfl⟩
    have h5 := add_mem (sub_mem h2 h1) h4
    convert h5 using 1
    push_cast
    simp only [map_sub, mul_one]
    ring
  have hfin : Ideal.absNorm 𝔪 ≠ 0 := Ideal.absNorm_eq_zero_iff.not.2 h𝔪
  have hcard : Nat.card (𝓞 D.host.E ⧸ 𝔪) = Ideal.absNorm 𝔪 := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 D.host.E ⧸ 𝔪) := Nat.finite_of_card_ne_zero (hcard ▸ hfin)
  haveI : Finite (intG D N ⧸ (congLev D 𝔪 N).subgroupOf (intG D N)) := Finite.of_injective g hg
  have hle := Nat.card_le_card_of_injective g hg
  rw [Nat.card_fun, Nat.card_fun, hcard, Nat.card_fin, ← pow_mul] at hle
  refine ⟨?_, ?_⟩
  · exact Subgroup.index_ne_zero_of_finite
  · calc (congLev D 𝔪 N).relIndex (intG D N) = Nat.card (intG D N ⧸ (congLev D 𝔪 N).subgroupOf (intG D N)) := rfl
      _ ≤ _ := hle
      _ = _ := by rw [sq]
