import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.DifferentialBoundedSupport

open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit KStab)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.RgExhStableChains

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def chainsIn (lev : Fin n → ℕ) (d : ℕ) (S : Submodule ℂ V) : Submodule ℂ (Cn n V) where
  carrier := {x | SuppIn (inU lev) x ∧ Deg d x ∧ ∀ A, x A ∈ S}
  add_mem' := by
    rintro x y ⟨hx1, hx2, hx3⟩ ⟨hy1, hy2, hy3⟩
    have key : ∀ A, (x + y) A ≠ 0 → x A ≠ 0 ∨ y A ≠ 0 := fun A h => by
      by_contra hc
      push Not at hc
      exact h (by simp [hc.1, hc.2])
    refine ⟨fun A h => ?_, fun A h => ?_, fun A => S.add_mem (hx3 A) (hy3 A)⟩
    · rcases key A h with h' | h'
      · exact hx1 A h'
      · exact hy1 A h'
    · rcases key A h with h' | h'
      · exact hx2 A h'
      · exact hy2 A h'
  zero_mem' := ⟨fun A h => absurd rfl h, fun A h => absurd rfl h, fun A => S.zero_mem⟩
  smul_mem' := by
    rintro c x ⟨hx1, hx2, hx3⟩
    have key : ∀ A, (c • x) A ≠ 0 → x A ≠ 0 := fun A h h0 => h (by simp [h0])
    exact ⟨fun A h => hx1 A (key A h), fun A h => hx2 A (key A h), fun A => S.smul_mem c (hx3 A)⟩

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_chainsIn {lev : Fin n → ℕ} {d : ℕ} {S : Submodule ℂ V} {x : Cn n V} :
    x ∈ chainsIn lev d S ↔ SuppIn (inU lev) x ∧ Deg d x ∧ ∀ A, x A ∈ S := Iff.rfl

/- English proof (translation)
Set `L : chainsIn lev d S →ₗ[ℂ] (Finset (Pos n) → S)` to `LinearMap.pi fun A => LinearMap.codRestrict S ((LinearMap.proj A).comp (chainsIn lev d S).subtype) fun x => x.2.2.2 A`. Use `Module.Finite.of_injective L fun x y h => Subtype.ext (funext fun A => ?_)` and prove the remaining obligations. Conclude with `congrArg Subtype.val (congrFun h A)`.
-/
theorem finiteDimensional_chainsIn (lev : Fin n → ℕ) (d : ℕ) (S : Submodule ℂ V) [FiniteDimensional ℂ S] :
    FiniteDimensional ℂ (chainsIn lev d S) := by
  let L : chainsIn lev d S →ₗ[ℂ] (Finset (Pos n) → S) :=
    LinearMap.pi fun A => LinearMap.codRestrict S ((LinearMap.proj A).comp (chainsIn lev d S).subtype)
      fun x => x.2.2.2 A
  refine Module.Finite.of_injective L fun x y h => Subtype.ext (funext fun A => ?_)
  exact congrArg Subtype.val (congrFun h A)

/- English proof (translation)
Simplify using `[lF, adL, LinearMap.add_apply, LinearMap.sum_apply, Finset.sum_apply, Module.End.mul_apply]`.
-/
theorem lF_apply (E : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) (x : Cn n V) (A : Finset (Pos n)) :
    lF E p q x A = E p q (x A) + ∑ i : Pos n, ∑ k : Pos n, adC p q i k • cre k (ann i x) A := by
  simp [lF, adL, LinearMap.add_apply, LinearMap.sum_apply, Finset.sum_apply, Module.End.mul_apply]

/- English proof (translation)
Rewrite using `[CompanionTheory.D.LK.Car.cre_apply]`. Use `split_ifs`. Use `S.smul_mem _ ?_` and prove the remaining obligations. Rewrite using `[CompanionTheory.D.LK.Car.ann_apply]`. Use `split_ifs`.

Conclude with `S.zero_mem`. Conclude with `S.smul_mem _ (hx _)`. Conclude with `S.zero_mem`.
-/
theorem cre_ann_mem {S : Submodule ℂ V} {x : Cn n V} (hx : ∀ A, x A ∈ S) (i k : Pos n) (A : Finset (Pos n)) :
    cre k (ann i x) A ∈ S := by
  rw [CompanionTheory.D.LK.Car.cre_apply]
  split_ifs
  · refine S.smul_mem _ ?_
    rw [CompanionTheory.D.LK.Car.ann_apply]
    split_ifs
    · exact S.zero_mem
    · exact S.smul_mem _ (hx _)
  · exact S.zero_mem

/- English proof (translation)
Distinguish the cases in `c1 : q = i.1.1 ∧ k.1 = (p, i.1.2)`. Use `show lev k.1.1 < lev k.1.2`. Rewrite using `[c1.2]`. Use `show lev p < lev i.1.2`. Rewrite using `[hpq, c1.1]`.

Conclude with `hi`. Distinguish the cases in `c2 : i.1.2 = p ∧ k.1 = (i.1.1, q)`. Use `show lev k.1.1 < lev k.1.2`. Rewrite using `[c2.2]`. Use `show lev i.1.1 < lev q`.

Rewrite using `[← hpq, ← c2.1]`. Conclude with `hi`. Conclude with `absurd (by simp [adC, c1, c2]) h`.
-/
theorem inU_of_adC {lev : Fin n → ℕ} {p q : Fin n} (hpq : lev p = lev q) {i k : Pos n}
    (h : adC p q i k ≠ 0) (hi : inU lev i) : inU lev k := by
  by_cases c1 : q = i.1.1 ∧ k.1 = (p, i.1.2)
  · show lev k.1.1 < lev k.1.2
    rw [c1.2]
    show lev p < lev i.1.2
    rw [hpq, c1.1]
    exact hi
  by_cases c2 : i.1.2 = p ∧ k.1 = (i.1.1, q)
  · show lev k.1.1 < lev k.1.2
    rw [c2.2]
    show lev i.1.1 < lev q
    rw [← hpq, ← c2.1]
    exact hi
  · exact absurd (by simp [adC, c1, c2]) h

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Apply `h` to reduce the goal to its premises. Rewrite using `[lF_apply, hc.1, map_zero, zero_add]`. Use `Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations.

Distinguish the cases in `h0 : adC p q i k = 0`. Rewrite using `[h0, zero_smul]`. Rewrite using `[hc.2 i k h0, smul_zero]`.
-/
theorem lF_ne {E : Fin n → Fin n → Module.End ℂ V} {p q : Fin n} {x : Cn n V} {A : Finset (Pos n)}
    (h : lF E p q x A ≠ 0) : x A ≠ 0 ∨ ∃ i k, adC p q i k ≠ 0 ∧ cre k (ann i x) A ≠ 0 := by
  by_contra hc
  push Not at hc
  apply h
  rw [lF_apply, hc.1, map_zero, zero_add]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun k _ => ?_
  by_cases h0 : adC p q i k = 0
  · rw [h0, zero_smul]
  · rw [hc.2 i k h0, smul_zero]

/- English proof (translation)
Take `⟨hk, h1⟩` from `CompanionTheory.D.LK.cre_ne h`. Take `⟨h2, h3⟩` from `CompanionTheory.D.LK.ann_ne h1`. Establish `hs` using `hx _ h3`. Establish `hi : inU lev i` using `hs i (mem_insert_self _ _)`. Use `⟨fun j hj => ?_, ?_⟩` and prove the remaining obligations.

Distinguish the cases in `e : j = k`. Conclude with `e ▸ inU_of_adC hpq h0 hi`. Conclude with `hs j (mem_insert_of_mem (mem_erase.2 ⟨e, hj⟩))`. Establish `e1` using `hd _ h3`. Rewrite `e1` using `[card_insert_of_notMem h2]`.

Establish `e2` using `card_erase_add_one hk`. Use linear arithmetic over natural numbers and integers.
-/
theorem term_supp {lev : Fin n → ℕ} {d : ℕ} {p q : Fin n} (hpq : lev p = lev q) {x : Cn n V}
    (hx : SuppIn (inU lev) x) (hd : Deg d x) {A : Finset (Pos n)} {i k : Pos n} (h0 : adC p q i k ≠ 0)
    (h : cre k (ann i x) A ≠ 0) : (∀ j ∈ A, inU lev j) ∧ A.card = d := by
  obtain ⟨hk, h1⟩ := CompanionTheory.D.LK.cre_ne h
  obtain ⟨h2, h3⟩ := CompanionTheory.D.LK.ann_ne h1
  have hs := hx _ h3
  have hi : inU lev i := hs i (mem_insert_self _ _)
  refine ⟨fun j hj => ?_, ?_⟩
  · by_cases e : j = k
    · exact e ▸ inU_of_adC hpq h0 hi
    · exact hs j (mem_insert_of_mem (mem_erase.2 ⟨e, hj⟩))
  · have e1 := hd _ h3
    rw [card_insert_of_notMem h2] at e1
    have e2 := card_erase_add_one hk
    omega

/- English proof (translation)
Take `⟨hx1, hx2, hx3⟩` from `hx`. Use `⟨fun A h => ?_, fun A h => ?_, fun A => ?_⟩` and prove the remaining obligations. Break down `lF_ne h with h' | ⟨i, k, h0, h'⟩` into its components or cases. Conclude with `hx1 A h'`. Conclude with `(term_supp hpq hx1 hx2 h0 h').1`.

Break down `lF_ne h with h' | ⟨i, k, h0, h'⟩` into its components or cases. Conclude with `hx2 A h'`. Conclude with `(term_supp hpq hx1 hx2 h0 h').2`. Rewrite using `[lF_apply]`. Conclude with `S.add_mem (hS p q hε _ (hx3 A)) (S.sum_mem fun i _ => S.sum_mem fun k _ => S.smul_mem _ (cre_ann_mem hx3 i k A))`.
-/
theorem lF_mem_chainsIn {ε : Fin n → Bool} {lev : Fin n → ℕ} {d : ℕ} {E : Fin n → Fin n → Module.End ℂ V}
    {S : Submodule ℂ V} (hS : KStab ε E S) {p q : Fin n} (hε : ε p = ε q) (hpq : lev p = lev q) {x : Cn n V}
    (hx : x ∈ chainsIn lev d S) : lF E p q x ∈ chainsIn lev d S := by
  obtain ⟨hx1, hx2, hx3⟩ := hx
  refine ⟨fun A h => ?_, fun A h => ?_, fun A => ?_⟩
  · rcases lF_ne h with h' | ⟨i, k, h0, h'⟩
    · exact hx1 A h'
    · exact (term_supp hpq hx1 hx2 h0 h').1
  · rcases lF_ne h with h' | ⟨i, k, h0, h'⟩
    · exact hx2 A h'
    · exact (term_supp hpq hx1 hx2 h0 h').2
  · rw [lF_apply]
    exact S.add_mem (hS p q hε _ (hx3 A)) (S.sum_mem fun i _ => S.sum_mem fun k _ =>
      S.smul_mem _ (cre_ann_mem hx3 i k A))

/- English proof (translation)
Introduce `n ε lev V _ _ E d y hF hy hd`. Use `choose Sf hfd hSt hmem using hF`. Set `S : Submodule ℂ V` to `⨆ A, Sf (y A)`. Use `haveI : ∀ A, FiniteDimensional ℂ (Sf (y A)) := fun A => hfd _`. Use `haveI : FiniteDimensional ℂ S := Submodule.finiteDimensional_iSup _`.

Establish `hSs : KStab ε E S` using `fun a b h v hv => (iSup_le fun A z hz => Submodule.mem_iSup_of_mem A (hSt _ a b h z hz) : S ≤ S.comap (E a b)) hv`. Use `⟨chainsIn lev d S, finiteDimensional_chainsIn lev d S, ⟨hy, hd, fun A => Submodule.mem_iSup_of_mem A (hmem _)⟩, fun x hx => ⟨hx.1, hx.2.1⟩, fun p q hε hpq x hx => lF_mem_chainsIn hSs hε hpq hx⟩` and prove the remaining obligations.
-/
theorem exists_stable : ∀ (n : ℕ) (ε : Fin n → Bool) (lev : Fin n → ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (d : ℕ) (y : Cn n V), LocFin ε E → SuppIn (inU lev) y → Deg d y →
    ∃ T : Submodule ℂ (Cn n V), FiniteDimensional ℂ T ∧ y ∈ T ∧ (∀ x ∈ T, SuppIn (inU lev) x ∧ Deg d x) ∧
      ∀ p q : Fin n, ε p = ε q → lev p = lev q → ∀ x ∈ T, lF E p q x ∈ T := by
  intro n ε lev V _ _ E d y hF hy hd
  choose Sf hfd hSt hmem using hF
  let S : Submodule ℂ V := ⨆ A, Sf (y A)
  haveI : ∀ A, FiniteDimensional ℂ (Sf (y A)) := fun A => hfd _
  haveI : FiniteDimensional ℂ S := Submodule.finiteDimensional_iSup _
  have hSs : KStab ε E S := fun a b h v hv =>
    (iSup_le fun A z hz => Submodule.mem_iSup_of_mem A (hSt _ a b h z hz) : S ≤ S.comap (E a b)) hv
  refine ⟨chainsIn lev d S, finiteDimensional_chainsIn lev d S,
    ⟨hy, hd, fun A => Submodule.mem_iSup_of_mem A (hmem _)⟩, fun x hx => ⟨hx.1, hx.2.1⟩,
    fun p q hε hpq x hx => lF_mem_chainsIn hSs hε hpq hx⟩

end GlobalTheory.CompanionTheory.RgExhStableChains
