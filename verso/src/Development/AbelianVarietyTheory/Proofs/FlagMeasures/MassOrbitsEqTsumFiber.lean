import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvVolMulPosLeConj
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

/- English proof (translation)
Establish `e : ∀ S : Set X, (S.encard : ℝ≥0∞) = ∑' x, S.indicator (fun _ => (1 : ℝ≥0∞)) x`. Introduce `S`. Rewrite using `[← ENNReal.tsum_set_one, tsum_subtype S (fun _ => (1 : ℝ≥0∞))]`. Simplify using `only [e]`. Rewrite using `[ENNReal.tsum_comm]`.

Use `tsum_congr fun x => ?_` and prove the remaining obligations. Rewrite using `[tsum_eq_single (q x)]`. Simplify using `[Set.indicator]`. Introduce `z hz`. Establish `: ¬ q x = z` using `fun h => hz h.symm`.

Simplify using `[Set.indicator, this]`.
-/
theorem encard_eq_tsum_fiber {X Z : Type*} (q : X → Z) (Q : X → Prop) :
    (({x | Q x} : Set X).encard : ℝ≥0∞)
      = ∑' z : Z, (({x | q x = z ∧ Q x} : Set X).encard : ℝ≥0∞) := by
  have e : ∀ S : Set X, (S.encard : ℝ≥0∞) = ∑' x, S.indicator (fun _ => (1 : ℝ≥0∞)) x := by
    intro S
    rw [← ENNReal.tsum_set_one, tsum_subtype S (fun _ => (1 : ℝ≥0∞))]
  simp only [e]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun x => ?_
  rw [tsum_eq_single (q x)]
  · simp [Set.indicator]
  · intro z hz
    have : ¬ q x = z := fun h => hz h.symm
    simp [Set.indicator, this]

/- English proof (translation)
Establish `h1 : ({z | (Quotient.mk'' z : MulAction.orbitRel.Quotient H X) = Quotient.mk'' x ∧ P z ∧ π z = π x} : Set X) = MulAction.orbit (↥(H ⊓ MulAction.stabilizer G (π x))) x`. Use extensionality with `z`. Simplify using `only [Set.mem_setOf_eq, Quotient.eq'', MulAction.orbitRel_apply]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨h, rfl⟩, -, hz⟩`.

Establish `h2` using `(hP h h.2 x hx).2`. Conclude with `⟨⟨h, h.2, h2.symm.trans hz⟩, rfl⟩`. Introduce and unpack `⟨⟨h, hh, hs⟩, rfl⟩`. Establish `h2` using `hP h hh x hx`. Conclude with `⟨⟨⟨h, hh⟩, rfl⟩, h2.1, h2.2.trans hs⟩`.

Establish `h2 : (H ⊓ MulAction.stabilizer G x).relIndex (H ⊓ MulAction.stabilizer G (π x)) = (MulAction.orbit (↥(H ⊓ MulAction.stabilizer G (π x))) x).ncard`. Rewrite using `[← MulAction.index_stabilizer, Subgroup.relIndex]`. Use `congr 1`. Use extensionality with `⟨h, hh, hs⟩`. Simplify using `only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]`.

Conclude with `⟨fun a => a.2, fun a => ⟨hh, a⟩⟩`. Rewrite using `[h1, h2]`. Rewrite `hfin` using `[h2]`. Conclude with `(Set.finite_of_ncard_ne_zero hfin).cast_ncard_eq.symm`.
-/
theorem encard_orbit_fiber {G X Y : Type*} [Group G] [MulAction G X] [MulAction G Y]
    (H : Subgroup G) (P : X → Prop) (π : X → Y)
    (hP : ∀ h ∈ H, ∀ x, P x → P (h • x) ∧ π (h • x) = h • π x) (x : X) (hx : P x)
    (hfin : (H ⊓ MulAction.stabilizer G x).relIndex (H ⊓ MulAction.stabilizer G (π x)) ≠ 0) :
    ({z | (Quotient.mk'' z : MulAction.orbitRel.Quotient H X) = Quotient.mk'' x ∧
        P z ∧ π z = π x} : Set X).encard
      = (H ⊓ MulAction.stabilizer G x).relIndex (H ⊓ MulAction.stabilizer G (π x)) := by
  have h1 : ({z | (Quotient.mk'' z : MulAction.orbitRel.Quotient H X) = Quotient.mk'' x ∧
        P z ∧ π z = π x} : Set X)
      = MulAction.orbit (↥(H ⊓ MulAction.stabilizer G (π x))) x := by
    ext z
    simp only [Set.mem_setOf_eq, Quotient.eq'', MulAction.orbitRel_apply]
    constructor
    · rintro ⟨⟨h, rfl⟩, -, hz⟩
      have h2 := (hP h h.2 x hx).2
      exact ⟨⟨h, h.2, h2.symm.trans hz⟩, rfl⟩
    · rintro ⟨⟨h, hh, hs⟩, rfl⟩
      have h2 := hP h hh x hx
      exact ⟨⟨⟨h, hh⟩, rfl⟩, h2.1, h2.2.trans hs⟩
  have h2 : (H ⊓ MulAction.stabilizer G x).relIndex (H ⊓ MulAction.stabilizer G (π x))
      = (MulAction.orbit (↥(H ⊓ MulAction.stabilizer G (π x))) x).ncard := by
    rw [← MulAction.index_stabilizer, Subgroup.relIndex]
    congr 1
    ext ⟨h, hh, hs⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
    exact ⟨fun a => a.2, fun a => ⟨hh, a⟩⟩
  rw [h1, h2]
  rw [h2] at hfin
  exact (Set.finite_of_ncard_ne_zero hfin).cast_ncard_eq.symm

/- English proof (translation)
Introduce `G X Y _ _ _ H K0 P π _ hP hc`. Establish `hP' : ∀ h ∈ H, ∀ x, P x → P (h • x) ∧ π (h • x) = h • π x` using `fun h hh x hx => ⟨(hP h hh x hx).1, (hP h hh x hx).2.1⟩`. Simplify using `only [fun c : MulAction.orbitRel.Quotient H Y => encard_eq_tsum_fiber (fun z : X => (Quotient.mk'' z : MulAction.orbitRel.Quotient H X)) (fun x => P x ∧ π x = c.out), ← ENNReal.tsum_mul_left]`. Rewrite using `[ENNReal.tsum_comm]`. Use `tsum_congr fun o => ?_` and prove the remaining obligations.

Establish `hmem : ∀ z : X, (Quotient.mk'' z : MulAction.orbitRel.Quotient H X) = o → ∃ h ∈ H, h • z = o.out`. Introduce `z hz`. Establish `: (Quotient.mk'' o.out : MulAction.orbitRel.Quotient H X) = Quotient.mk'' z`. Rewrite using `[hz]`. Conclude with `Quotient.out_eq' o`.

Rewrite `this` using `[Quotient.eq'', MulAction.orbitRel_apply]`. Take `⟨h, hh⟩` from `this`. Conclude with `⟨h, h.2, hh⟩`. Use `split_ifs with ho`. Use `set c0 : MulAction.orbitRel.Quotient H Y := Quotient.mk'' (π o.out) with hc0`.

Rewrite using `[tsum_eq_single c0]`. Establish `: (Quotient.mk'' c0.out : MulAction.orbitRel.Quotient H Y) = Quotient.mk'' (π o.out)` using `Quotient.out_eq' c0`. Rewrite `this` using `[Quotient.eq'', MulAction.orbitRel_apply]`. Take `⟨⟨h, hh⟩, hy⟩` from `this`. Establish `hy' : h • π o.out = c0.out` using `hy`.

Take `⟨p1, p2, p3⟩` from `hP h hh _ ho`. Establish `ho' : o = Quotient.mk'' (h • o.out)` using `by conv_lhs => rw [← Quotient.out_eq' o]`. Use `symm`. Rewrite using `[Quotient.eq'', MulAction.orbitRel_apply]`. Conclude with `⟨⟨h, hh⟩, rfl⟩`.

Rewrite using `[← p3, ← hy', ← p2]`. Generalize the expression as in `h • o.out = x at p1 ho'`. Take `⟨a1, a2, a3, a4⟩` from `hc x p1`. Establish `hle : H ⊓ MulAction.stabilizer G x ≤ H ⊓ MulAction.stabilizer G (π x)`. Introduce and unpack `g ⟨g1, g2⟩`.

Use `⟨g1, ?_⟩` and prove the remaining obligations. Establish `g3 : g • x = x` using `g2`. Use `(hP' g g1 x p1).2` as an intermediate fact. Rewrite `this` using `[g3]`. Conclude with `this.symm`.

Take `⟨-, -, b, -⟩` from `invVol_mul_pos_le_conj K0 _ _ a3 a4 a1 a2`. Rewrite using `[ho', encard_orbit_fiber H P π hP' x p1 (Subgroup.relIndex_ne_zero_trans a2 a3), b hle, ENNReal.ofReal_mul' (Nat.cast_nonneg _)]`. Simplify using the standard rewrite rules. Introduce `c hne`. Establish `: ({x | (Quotient.mk'' x : MulAction.orbitRel.Quotient H X) = o ∧ P x ∧ π x = c.out} : Set X) = ∅`.

Use extensionality with `z`. Simplify using `only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]`. Introduce and unpack `⟨h1, h2, h3⟩`. Take `⟨h, hh, e⟩` from `hmem z h1`. Apply `hne` to reduce the goal to its premises.

Rewrite using `[hc0, ← e, (hP' h hh z h2).2, h3]`. Use `conv_lhs => rw [← Quotient.out_eq' c]`. Use `symm`. Rewrite using `[Quotient.eq'', MulAction.orbitRel_apply]`. Conclude with `⟨⟨h, hh⟩, rfl⟩`.

Rewrite using `[this]`. Simplify using the standard rewrite rules. Use `symm`. Use `ENNReal.tsum_eq_zero.2 fun c => ?_` and prove the remaining obligations. Establish `: ({x | (Quotient.mk'' x : MulAction.orbitRel.Quotient H X) = o ∧ P x ∧ π x = c.out} : Set X) = ∅`.

Use extensionality with `z`. Simplify using `only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]`. Introduce and unpack `⟨h1, h2, -⟩`. Take `⟨h, hh, e⟩` from `hmem z h1`. Conclude with `ho (e ▸ (hP' h hh z h2).1)`.

Rewrite using `[this]`. Simplify using the standard rewrite rules.
-/
theorem mass_orbits_eq_tsum_fiber : ∀ {G X Y : Type} [Group G] [MulAction G X] [MulAction G Y] (H K0 : Subgroup G) (P : X → Prop) (π : X → Y), K0 ≤ H → (∀ h ∈ H, ∀ x, P x → P (h • x) ∧ π (h • x) = h • π x ∧ invVol K0 (H ⊓ MulAction.stabilizer G (h • x)) = invVol K0 (H ⊓ MulAction.stabilizer G x)) → (∀ x, P x → K0.relIndex (H ⊓ MulAction.stabilizer G x) ≠ 0 ∧ (H ⊓ MulAction.stabilizer G x).relIndex K0 ≠ 0 ∧ K0.relIndex (H ⊓ MulAction.stabilizer G (π x)) ≠ 0 ∧ (H ⊓ MulAction.stabilizer G (π x)).relIndex K0 ≠ 0) → (∑' o : MulAction.orbitRel.Quotient H X, if P o.out then ENNReal.ofReal (invVol K0 (H ⊓ MulAction.stabilizer G o.out)) else 0) = ∑' c : MulAction.orbitRel.Quotient H Y, ENNReal.ofReal (invVol K0 (H ⊓ MulAction.stabilizer G c.out)) * (({x | P x ∧ π x = c.out} : Set X).encard : ℝ≥0∞) := by
  intro G X Y _ _ _ H K0 P π _ hP hc
  have hP' : ∀ h ∈ H, ∀ x, P x → P (h • x) ∧ π (h • x) = h • π x :=
    fun h hh x hx => ⟨(hP h hh x hx).1, (hP h hh x hx).2.1⟩
  simp only [fun c : MulAction.orbitRel.Quotient H Y =>
    encard_eq_tsum_fiber (fun z : X => (Quotient.mk'' z : MulAction.orbitRel.Quotient H X))
      (fun x => P x ∧ π x = c.out), ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun o => ?_
  have hmem : ∀ z : X, (Quotient.mk'' z : MulAction.orbitRel.Quotient H X) = o →
      ∃ h ∈ H, h • z = o.out := by
    intro z hz
    have : (Quotient.mk'' o.out : MulAction.orbitRel.Quotient H X) = Quotient.mk'' z := by
      rw [hz]; exact Quotient.out_eq' o
    rw [Quotient.eq'', MulAction.orbitRel_apply] at this
    obtain ⟨h, hh⟩ := this
    exact ⟨h, h.2, hh⟩
  split_ifs with ho
  · set c0 : MulAction.orbitRel.Quotient H Y := Quotient.mk'' (π o.out) with hc0
    rw [tsum_eq_single c0]
    · have : (Quotient.mk'' c0.out : MulAction.orbitRel.Quotient H Y) = Quotient.mk'' (π o.out) :=
        Quotient.out_eq' c0
      rw [Quotient.eq'', MulAction.orbitRel_apply] at this
      obtain ⟨⟨h, hh⟩, hy⟩ := this
      have hy' : h • π o.out = c0.out := hy
      obtain ⟨p1, p2, p3⟩ := hP h hh _ ho
      have ho' : o = Quotient.mk'' (h • o.out) := by
        conv_lhs => rw [← Quotient.out_eq' o]
        symm
        rw [Quotient.eq'', MulAction.orbitRel_apply]
        exact ⟨⟨h, hh⟩, rfl⟩
      rw [← p3, ← hy', ← p2]
      generalize h • o.out = x at p1 ho'
      obtain ⟨a1, a2, a3, a4⟩ := hc x p1
      have hle : H ⊓ MulAction.stabilizer G x ≤ H ⊓ MulAction.stabilizer G (π x) := by
        rintro g ⟨g1, g2⟩
        refine ⟨g1, ?_⟩
        have g3 : g • x = x := g2
        have := (hP' g g1 x p1).2
        rw [g3] at this
        exact this.symm
      obtain ⟨-, -, b, -⟩ := invVol_mul_pos_le_conj K0 _ _ a3 a4 a1 a2
      rw [ho', encard_orbit_fiber H P π hP' x p1 (Subgroup.relIndex_ne_zero_trans a2 a3), b hle,
        ENNReal.ofReal_mul' (Nat.cast_nonneg _)]
      simp
    · intro c hne
      have : ({x | (Quotient.mk'' x : MulAction.orbitRel.Quotient H X) = o ∧ P x ∧ π x = c.out} :
          Set X) = ∅ := by
        ext z
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨h1, h2, h3⟩
        obtain ⟨h, hh, e⟩ := hmem z h1
        apply hne
        rw [hc0, ← e, (hP' h hh z h2).2, h3]
        conv_lhs => rw [← Quotient.out_eq' c]
        symm
        rw [Quotient.eq'', MulAction.orbitRel_apply]
        exact ⟨⟨h, hh⟩, rfl⟩
      rw [this]; simp
  · symm
    refine ENNReal.tsum_eq_zero.2 fun c => ?_
    have : ({x | (Quotient.mk'' x : MulAction.orbitRel.Quotient H X) = o ∧ P x ∧ π x = c.out} :
        Set X) = ∅ := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨h1, h2, -⟩
      obtain ⟨h, hh, e⟩ := hmem z h1
      exact ho (e ▸ (hP' h hh z h2).1)
    rw [this]; simp

end GlobalTheory.HL
