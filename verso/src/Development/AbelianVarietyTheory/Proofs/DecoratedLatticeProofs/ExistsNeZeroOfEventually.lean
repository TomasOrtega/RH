import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
open ValuativeRel GlobalTheory.SplitWeil Matrix

noncomputable section
namespace GlobalTheory.SBUnif

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Set `S : AddSubgroup k` to `(𝒪[k].toAddSubgroup).comap (AddMonoidHom.mulLeft c⁻¹)`. Set `H : AddSubgroup 𝒪[k]` to `S.comap (𝒪[k].subtype.toAddMonoidHom)`. Establish `hS : IsOpen (S : Set k)` using `(Valuation.isOpen_integer (v := valuation k)).preimage (continuous_const.mul continuous_id)`. Establish `hH : IsOpen (H : Set 𝒪[k])` using `hS.preimage continuous_subtype_val`. Set `H' : OpenAddSubgroup 𝒪[k]` to `⟨H, hH⟩`.

Establish `: Finite (𝒪[k] ⧸ H)` using `AddSubgroup.instFiniteQuotientOfSeparatelyContinuousAddOfCompactSpace H'`. Establish `hne : H.index ≠ 0` using `AddSubgroup.index_ne_zero_of_finite`. Use `⟨H.index, Nat.pos_of_ne_zero hne, ?_⟩` and prove the remaining obligations. Establish `hm` using `H.nsmul_index_mem (1 : 𝒪[k])`. Simplify `hm` using `[H, S]`.
-/
theorem exists_nat_mem_mul_integer (c : k) (hc : c ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ c⁻¹ * (n : k) ∈ 𝒪[k] := by
  let S : AddSubgroup k := (𝒪[k].toAddSubgroup).comap (AddMonoidHom.mulLeft c⁻¹)
  let H : AddSubgroup 𝒪[k] := S.comap (𝒪[k].subtype.toAddMonoidHom)
  have hS : IsOpen (S : Set k) :=
    (Valuation.isOpen_integer (v := valuation k)).preimage (continuous_const.mul continuous_id)
  have hH : IsOpen (H : Set 𝒪[k]) := hS.preimage continuous_subtype_val
  let H' : OpenAddSubgroup 𝒪[k] := ⟨H, hH⟩
  have : Finite (𝒪[k] ⧸ H) := AddSubgroup.instFiniteQuotientOfSeparatelyContinuousAddOfCompactSpace H'
  have hne : H.index ≠ 0 := AddSubgroup.index_ne_zero_of_finite
  refine ⟨H.index, Nat.pos_of_ne_zero hne, ?_⟩
  have hm := H.nsmul_index_mem (1 : 𝒪[k])
  simpa [H, S] using hm

/- English proof (translation)
Take `⟨γ, hγ⟩` from `(IsValuativeTopology.mem_nhds_zero_iff _).1 h`. Take `⟨a, ha⟩` from `ValuativeRel.valuation_surjective (γ : ValueGroupWithZero k)`. Take `⟨w, hw0, hw1⟩` from `Valuation.IsNontrivial.exists_lt_one (v := valuation k)`. Establish `ha0 : a ≠ 0`. Introduce and unpack `rfl`.

Simplify using `only [map_zero] at ha`. Conclude with `γ.ne_zero ha.symm`. Use `⟨a * w, mul_ne_zero ha0 hw0, hγ ?_⟩` and prove the remaining obligations. Use `show valuation k (a * w) < γ`. Rewrite using `[map_mul, ha]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_ne_zero_of_eventually {P : k → Prop} (h : ∀ᶠ s in nhds (0 : k), P s) :
    ∃ c : k, c ≠ 0 ∧ P c := by
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff _).1 h
  obtain ⟨a, ha⟩ := ValuativeRel.valuation_surjective (γ : ValueGroupWithZero k)
  obtain ⟨w, hw0, hw1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp only [map_zero] at ha
    exact γ.ne_zero ha.symm
  refine ⟨a * w, mul_ne_zero ha0 hw0, hγ ?_⟩
  show valuation k (a * w) < γ
  rw [map_mul, ha]
  calc (γ : ValueGroupWithZero k) * valuation k w < γ * 1 :=
        mul_lt_mul_of_pos_left hw1 (zero_lt_iff.mpr γ.ne_zero)
    _ = γ := mul_one _

end GlobalTheory.SBUnif

namespace GlobalTheory.SBUnif

/- English proof (translation)
Introduce `k _ _ _ _ _ Y Y' _ _ Φ hΦ`. Take `⟨hlc, hcs⟩` from `hΦ`. Use `set O : Set (Matrix Y Y' k) := {u | ∀ r q, u r q ∈ 𝒪[k]} with hOdef`. Establish `hOpi : O = Set.univ.pi (fun _ : Y => Set.univ.pi (fun _ : Y' => (𝒪[k] : Set k)))`. Use extensionality with `u`.

Prove the components needed by the constructor for the conclusion. Introduce `h r _ q _`. Conclude with `h r q`. Introduce `h r q`. Conclude with `h r (Set.mem_univ _) q (Set.mem_univ _)`.

Establish `hOc : IsCompact O`. Rewrite using `[hOpi]`. Conclude with `isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => (isCompact_iff_compactSpace (s := (𝒪[k] : Set k))).mpr (inferInstanceAs (CompactSpace 𝒪[k]))))`. Establish `hOo : IsOpen O`. Rewrite using `[hOpi]`.

Conclude with `isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_set_pi Set.finite_univ (fun _ _ => Valuation.isOpen_integer (v := valuation k)))`. Establish `hK : IsCompact (tsupport Φ)` using `hcs`. Establish `h1 : ∀ᶠ s in nhds (0 : k), ∀ p ∈ tsupport Φ ×ˢ O, Φ (p.1 + s • p.2) = Φ p.1`. Apply `(hK.prod hOc).eventually_forall_of_forall_eventually` to reduce the goal to its premises. Introduce `p _`.

Establish `hc : Continuous (fun z : k × (Matrix Y Y' k × Matrix Y Y' k) => z.2.1 + z.1 • z.2.2)` using `by fun_prop`. Establish `e1` using `(hlc.comp_continuous hc).eventually_eq (0, p)`. Establish `e2` using `(hlc.comp_continuous (continuous_fst.comp continuous_snd)).eventually_eq ((0 : k), p)`. Use `filter_upwards [e1, e2] with z hz1 hz2`. Simplify using `only [Function.comp_apply, zero_smul, add_zero] at hz1 hz2`.

Rewrite using `[hz1, hz2]`. Establish `h2 : ∀ᶠ s in nhds (0 : k), ∀ t ∈ tsupport Φ, s • t ∈ O`. Apply `hK.eventually_forall_of_forall_eventually` to reduce the goal to its premises. Introduce `t _`. Establish `hc : Continuous (fun z : k × Matrix Y Y' k => z.1 • z.2)` using `by fun_prop`.

Establish `h0 : (fun z : k × Matrix Y Y' k => z.1 • z.2) ((0 : k), t) ∈ O`. Simplify using `only [zero_smul]`. Introduce `r q`. Simplify using the standard rewrite rules. Conclude with `hc.continuousAt.preimage_mem_nhds (hOo.mem_nhds h0)`.

Take `⟨c, hc0, hc1, hc2⟩` from `exists_ne_zero_of_eventually (h1.and h2)`. Take `⟨n, hn, hy⟩` from `exists_nat_mem_mul_integer c hc0`. Use `set y := c⁻¹ * (n : k) with hydef`. Establish `hn' : (n : k) = c * y`. Rewrite using `[hydef, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]`.

Establish `hsmul : ∀ u : Matrix Y Y' k, n • u = c • (y • u)`. Introduce `u`. Rewrite using `[smul_smul, ← hn', Nat.cast_smul_eq_nsmul]`. Establish `hyO : ∀ u ∈ O, y • u ∈ O` using `fun u hu r q => by`. Simplify using `only [Matrix.smul_apply, smul_eq_mul]`.

Conclude with `mul_mem hy (hu r q)`. Use `⟨n, hn, ?_, ?_⟩` and prove the remaining obligations. Introduce `u hu t`. Rewrite using `[hsmul]`. Establish `hu' : y • u ∈ O` using `hyO u hu`.

Distinguish the cases in `ht : t ∈ tsupport Φ`. Conclude with `hc1 (t, y • u) ⟨ht, hu'⟩`. Distinguish the cases in `ht' : t + c • (y • u) ∈ tsupport Φ`. Establish `hneg : -(y • u) ∈ O` using `fun r q => by`. Simplify using `only [Matrix.neg_apply]`.

Conclude with `neg_mem (hu' r q)`. Use `hc1 (t + c • (y • u), -(y • u)) ⟨ht', hneg⟩` as an intermediate fact. Simplify using `only [smul_neg, add_neg_cancel_right] at this`. Conclude with `this.symm`. Rewrite using `[image_eq_zero_of_notMem_tsupport ht', image_eq_zero_of_notMem_tsupport ht]`.

Introduce `t ht r q`. Establish `htK : t ∈ tsupport Φ` using `subset_tsupport _ ht`. Rewrite using `[hsmul, smul_comm]`. Conclude with `hyO _ (hc2 t htK) r q`.
-/
theorem sb_lattice_bounds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (Y Y' : Type) [Fintype Y] [Fintype Y'] (Φ : Matrix Y Y' k → ℂ), Φ ∈ SB (Matrix Y Y' k) → ∃ n : ℕ, 0 < n ∧ (∀ u : Matrix Y Y' k, (∀ r q, u r q ∈ 𝒪[k]) → ∀ t, Φ (t + n • u) = Φ t) ∧ ∀ t, Φ t ≠ 0 → ∀ r q, (n • t) r q ∈ 𝒪[k] := by
  intro k _ _ _ _ _ Y Y' _ _ Φ hΦ
  obtain ⟨hlc, hcs⟩ := hΦ
  set O : Set (Matrix Y Y' k) := {u | ∀ r q, u r q ∈ 𝒪[k]} with hOdef
  have hOpi : O = Set.univ.pi (fun _ : Y => Set.univ.pi (fun _ : Y' => (𝒪[k] : Set k))) := by
    ext u
    constructor
    · intro h r _ q _
      exact h r q
    · intro h r q
      exact h r (Set.mem_univ _) q (Set.mem_univ _)
  have hOc : IsCompact O := by
    rw [hOpi]
    exact isCompact_univ_pi (fun _ => isCompact_univ_pi
      (fun _ => (isCompact_iff_compactSpace (s := (𝒪[k] : Set k))).mpr
        (inferInstanceAs (CompactSpace 𝒪[k]))))
  have hOo : IsOpen O := by
    rw [hOpi]
    exact isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_set_pi Set.finite_univ
      (fun _ _ => Valuation.isOpen_integer (v := valuation k)))
  have hK : IsCompact (tsupport Φ) := hcs
  have h1 : ∀ᶠ s in nhds (0 : k), ∀ p ∈ tsupport Φ ×ˢ O, Φ (p.1 + s • p.2) = Φ p.1 := by
    apply (hK.prod hOc).eventually_forall_of_forall_eventually
    intro p _
    have hc : Continuous (fun z : k × (Matrix Y Y' k × Matrix Y Y' k) => z.2.1 + z.1 • z.2.2) := by
      fun_prop
    have e1 := (hlc.comp_continuous hc).eventually_eq (0, p)
    have e2 := (hlc.comp_continuous (continuous_fst.comp continuous_snd)).eventually_eq
      ((0 : k), p)
    filter_upwards [e1, e2] with z hz1 hz2
    simp only [Function.comp_apply, zero_smul, add_zero] at hz1 hz2
    rw [hz1, hz2]
  have h2 : ∀ᶠ s in nhds (0 : k), ∀ t ∈ tsupport Φ, s • t ∈ O := by
    apply hK.eventually_forall_of_forall_eventually
    intro t _
    have hc : Continuous (fun z : k × Matrix Y Y' k => z.1 • z.2) := by fun_prop
    have h0 : (fun z : k × Matrix Y Y' k => z.1 • z.2) ((0 : k), t) ∈ O := by
      simp only [zero_smul]
      intro r q
      simp
    exact hc.continuousAt.preimage_mem_nhds (hOo.mem_nhds h0)
  obtain ⟨c, hc0, hc1, hc2⟩ := exists_ne_zero_of_eventually (h1.and h2)
  obtain ⟨n, hn, hy⟩ := exists_nat_mem_mul_integer c hc0
  set y := c⁻¹ * (n : k) with hydef
  have hn' : (n : k) = c * y := by
    rw [hydef, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
  have hsmul : ∀ u : Matrix Y Y' k, n • u = c • (y • u) := by
    intro u
    rw [smul_smul, ← hn', Nat.cast_smul_eq_nsmul]
  have hyO : ∀ u ∈ O, y • u ∈ O := fun u hu r q => by
    simp only [Matrix.smul_apply, smul_eq_mul]
    exact mul_mem hy (hu r q)
  refine ⟨n, hn, ?_, ?_⟩
  · intro u hu t
    rw [hsmul]
    have hu' : y • u ∈ O := hyO u hu
    by_cases ht : t ∈ tsupport Φ
    · exact hc1 (t, y • u) ⟨ht, hu'⟩
    by_cases ht' : t + c • (y • u) ∈ tsupport Φ
    · have hneg : -(y • u) ∈ O := fun r q => by
        simp only [Matrix.neg_apply]
        exact neg_mem (hu' r q)
      have := hc1 (t + c • (y • u), -(y • u)) ⟨ht', hneg⟩
      simp only [smul_neg, add_neg_cancel_right] at this
      exact this.symm
    · rw [image_eq_zero_of_notMem_tsupport ht', image_eq_zero_of_notMem_tsupport ht]
  · intro t ht r q
    have htK : t ∈ tsupport Φ := subset_tsupport _ ht
    rw [hsmul, smul_comm]
    exact hyO _ (hc2 t htK) r q

end GlobalTheory.SBUnif
