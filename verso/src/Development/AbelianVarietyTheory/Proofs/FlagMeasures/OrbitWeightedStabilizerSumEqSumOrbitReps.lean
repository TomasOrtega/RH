import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass

open NumberField Matrix in
open scoped ENNReal Classical in

/- English proof (translation)
Introduce `G α _ _ X N hX hN s hs huniq`. Establish `hX' : ∀ (g : G), ∀ x ∈ X, g • x ∈ X` using `hX`. Unfold `_root_.GlobalTheory.Mass.orbSum`. Establish `hout : ∀ x : α, ∃ g : G, g • x = (Quotient.mk (MulAction.orbitRel G α) x).out` using `fun x => MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp (Quotient.exact (Quotient.out_eq (Quotient.mk (MulAction.orbitRel G α) x))))`. Establish `hterm : ∀ x : α, ((ENat.card (MulAction.stabilizer G (Quotient.mk (MulAction.orbitRel G α) x).out) : ℕ∞) : ℝ≥0∞)⁻¹ * N (Quotient.mk (MulAction.orbitRel G α) x).out = ((ENat.card (MulAction.stabilizer G x) : ℕ∞) : ℝ≥0∞)⁻¹ * N x`.

Introduce `x`. Take `⟨g, hg⟩` from `hout x`. Rewrite using `[← hg, hN, ENat.card_congr (MulAction.stabilizerEquivStabilizer (rfl : g • x = g • x)).toEquiv.symm]`. Set `e : {x // x ∈ s} → {q : MulAction.orbitRel.Quotient G α // q.out ∈ X}` to `fun x => ⟨Quotient.mk _ x.1, by obtain ⟨g, hg⟩ := hout x.1; rw [← hg]; exact hX' g _ (hs _ x.2)⟩`. Establish `he_inj : Function.Injective e`.

Introduce and unpack `⟨x, hx⟩ ⟨y, hy⟩ hxy`. Establish `hq : Quotient.mk (MulAction.orbitRel G α) x = Quotient.mk _ y` using `congrArg Subtype.val hxy`. Take `⟨g, hg⟩` from `MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp (Quotient.exact hq))`. Take `⟨z, -, hz⟩` from `huniq x (hs x hx)`. Establish `h1` using `hz x ⟨hx, 1, one_smul G x⟩`.

Establish `h2` using `hz y ⟨hy, g, hg⟩`. Conclude with `Subtype.ext (h1.trans h2.symm)`. Establish `he_surj : Function.Surjective e`. Introduce and unpack `⟨q, hq⟩`. Take `⟨y, ⟨hy, g, hg⟩, -⟩` from `huniq q.out hq`.

Use `⟨⟨y, hy⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Use `show Quotient.mk _ y = q`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← (Equiv.ofBijective e ⟨he_inj, he_surj⟩).tsum_eq, tsum_fintype, ← Finset.sum_coe_sort s]`. Conclude with `Finset.sum_congr rfl fun x _ => hterm x.1`.
-/
theorem _root_.GlobalTheory.Mass.orbSum_eq_sum_reps : ∀ (G α : Type) [Group G] [MulAction G α]
    (X : Set α) (N : α → ℝ≥0∞), _root_.GlobalTheory.Mass.Stable G X → (∀ (g : G) x, N (g • x) = N x) →
    ∀ s : Finset α, (∀ x ∈ s, x ∈ X) → (∀ x ∈ X, ∃! y, y ∈ s ∧ ∃ g : G, g • y = x) →
    _root_.GlobalTheory.Mass.orbSum G X N =
      ∑ x ∈ s, ((ENat.card (MulAction.stabilizer G x) : ℕ∞) : ℝ≥0∞)⁻¹ * N x := by
  intro G α _ _ X N hX hN s hs huniq
  have hX' : ∀ (g : G), ∀ x ∈ X, g • x ∈ X := hX
  unfold _root_.GlobalTheory.Mass.orbSum
  have hout : ∀ x : α, ∃ g : G, g • x = (Quotient.mk (MulAction.orbitRel G α) x).out := fun x =>
    MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp
      (Quotient.exact (Quotient.out_eq (Quotient.mk (MulAction.orbitRel G α) x))))
  have hterm : ∀ x : α,
      ((ENat.card (MulAction.stabilizer G (Quotient.mk (MulAction.orbitRel G α) x).out) : ℕ∞) :
          ℝ≥0∞)⁻¹ * N (Quotient.mk (MulAction.orbitRel G α) x).out
        = ((ENat.card (MulAction.stabilizer G x) : ℕ∞) : ℝ≥0∞)⁻¹ * N x := by
    intro x
    obtain ⟨g, hg⟩ := hout x
    rw [← hg, hN,
      ENat.card_congr (MulAction.stabilizerEquivStabilizer (rfl : g • x = g • x)).toEquiv.symm]
  let e : {x // x ∈ s} → {q : MulAction.orbitRel.Quotient G α // q.out ∈ X} := fun x =>
    ⟨Quotient.mk _ x.1, by obtain ⟨g, hg⟩ := hout x.1; rw [← hg]; exact hX' g _ (hs _ x.2)⟩
  have he_inj : Function.Injective e := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    have hq : Quotient.mk (MulAction.orbitRel G α) x = Quotient.mk _ y := congrArg Subtype.val hxy
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp (Quotient.exact hq))
    obtain ⟨z, -, hz⟩ := huniq x (hs x hx)
    have h1 := hz x ⟨hx, 1, one_smul G x⟩
    have h2 := hz y ⟨hy, g, hg⟩
    exact Subtype.ext (h1.trans h2.symm)
  have he_surj : Function.Surjective e := by
    rintro ⟨q, hq⟩
    obtain ⟨y, ⟨hy, g, hg⟩, -⟩ := huniq q.out hq
    refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
    show Quotient.mk _ y = q
    calc Quotient.mk (MulAction.orbitRel G α) y = Quotient.mk _ q.out :=
          Quotient.sound (MulAction.orbitRel_apply.mpr
            (MulAction.mem_orbit_iff.mpr ⟨g⁻¹, inv_smul_eq_iff.mpr hg.symm⟩))
      _ = q := Quotient.out_eq q
  rw [← (Equiv.ofBijective e ⟨he_inj, he_surj⟩).tsum_eq, tsum_fintype, ← Finset.sum_coe_sort s]
  exact Finset.sum_congr rfl fun x _ => hterm x.1

end GlobalTheory.Mass
