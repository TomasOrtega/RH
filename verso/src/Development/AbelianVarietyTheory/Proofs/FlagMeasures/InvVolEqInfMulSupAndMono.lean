import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvVolMulPosLeConj
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.IndexProd

/- English proof (translation)
Use `symm`. Use `Nat.card_congr (Equiv.ofBijective (Subgroup.quotientSubgroupOfEmbeddingOfLE D hNE) ⟨(Subgroup.quotientSubgroupOfEmbeddingOfLE D hNE).injective, ?_⟩)` and prove the remaining obligations. Introduce `q`. Proceed by induction on `q using QuotientGroup.induction_on with`. Consider the case `H e`.

Take `⟨n, hn, d, hd, hnd⟩` from `h e e.2`. Use `⟨QuotientGroup.mk ⟨n, hn⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Subgroup.quotientSubgroupOfEmbeddingOfLE_apply_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf]`. Simplify `hd` using `[← hnd]`.
-/
theorem relIndex_eq_of_forall_mul {G : Type*} [Group G] {D N E : Subgroup G} (hNE : N ≤ E)
    (h : ∀ e ∈ E, ∃ n ∈ N, ∃ d ∈ D, n * d = e) : D.relIndex E = D.relIndex N := by
  symm
  refine Nat.card_congr (Equiv.ofBijective (Subgroup.quotientSubgroupOfEmbeddingOfLE D hNE)
    ⟨(Subgroup.quotientSubgroupOfEmbeddingOfLE D hNE).injective, ?_⟩)
  intro q
  induction q using QuotientGroup.induction_on with
  | H e =>
    obtain ⟨n, hn, d, hd, hnd⟩ := h e e.2
    refine ⟨QuotientGroup.mk ⟨n, hn⟩, ?_⟩
    rw [Subgroup.quotientSubgroupOfEmbeddingOfLE_apply_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa [← hnd] using hd

/- English proof (translation)
Establish `hle : A ≤ Subgroup.normalizer M`. Introduce `s hs`. Rewrite using `[Subgroup.mem_normalizer_iff]`. Introduce `t`. Use `⟨h s hs t, fun ht => ?_⟩` and prove the remaining obligations.

Use `h s⁻¹ (A.inv_mem hs) _ ht` as an intermediate fact. Simplify `this` using `[mul_assoc]`. Establish `hx' : x ∈ ((A ⊔ M : Subgroup G) : Set G)` using `hx`. Rewrite `hx'` using `[Subgroup.coe_mul_of_left_le_normalizer_right A M hle]`. Take `⟨a, ha, m, hm, e⟩` from `hx'`.

Conclude with `⟨a, ha, m, hm, e⟩`.
-/
theorem exists_mul_of_mem_sup {G : Type*} [Group G] {A M : Subgroup G}
    (h : ∀ s ∈ A, ∀ t ∈ M, s * t * s⁻¹ ∈ M) {x : G} (hx : x ∈ A ⊔ M) :
    ∃ a ∈ A, ∃ m ∈ M, a * m = x := by
  have hle : A ≤ Subgroup.normalizer M := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro t
    refine ⟨h s hs t, fun ht => ?_⟩
    have := h s⁻¹ (A.inv_mem hs) _ ht
    simpa [mul_assoc] using this
  have hx' : x ∈ ((A ⊔ M : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right A M hle] at hx'
  obtain ⟨a, ha, m, hm, e⟩ := hx'
  exact ⟨a, ha, m, hm, e⟩

/- English proof (translation)
Establish `h1 : (D ⊔ M).relIndex (A ⊔ M) = (D ⊔ M).relIndex A` using `relIndex_eq_of_forall_mul le_sup_left fun e he => by`. Take `⟨a, ha, m, hm, e⟩` from `exists_mul_of_mem_sup h he`. Conclude with `⟨a, ha, m, (le_sup_right : M ≤ D ⊔ M) hm, e⟩`. Establish `h2 : D.relIndex ((D ⊔ M) ⊓ A) = D.relIndex (A ⊓ M)` using `relIndex_eq_of_forall_mul (le_inf (inf_le_right.trans le_sup_right) inf_le_left) fun e he => by`. Take `⟨d, hd, m, hm, e'⟩` from `exists_mul_of_mem_sup (fun s hs => h s (hDA hs)) he.1`.

Use `⟨d * m * d⁻¹, ⟨?_, h d (hDA hd) m hm⟩, d, hd, by rw [← e']; simp⟩` and prove the remaining obligations. Rewrite using `[e']`. Conclude with `A.mul_mem he.2 (A.inv_mem (hDA hd))`. Establish `h3 : (D ⊓ M).relIndex (A ⊓ M) = D.relIndex (A ⊓ M)`. Rewrite using `[← Subgroup.inf_relIndex_right D, ← Subgroup.inf_relIndex_right (D ⊓ M)]`.

Use `congr 1`. Rewrite using `[inf_comm A M, ← inf_assoc, ← inf_assoc, inf_assoc D M M, inf_idem]`. Rewrite using `[h1, h3, ← h2, Subgroup.relIndex_inf_mul_relIndex, inf_eq_left.2 le_sup_left]`.
-/
theorem relIndex_eq_inf_mul_sup {G : Type*} [Group G] {D A M : Subgroup G} (hDA : D ≤ A)
    (h : ∀ s ∈ A, ∀ t ∈ M, s * t * s⁻¹ ∈ M) :
    D.relIndex A = (D ⊓ M).relIndex (A ⊓ M) * (D ⊔ M).relIndex (A ⊔ M) := by
  have h1 : (D ⊔ M).relIndex (A ⊔ M) = (D ⊔ M).relIndex A :=
    relIndex_eq_of_forall_mul le_sup_left fun e he => by
      obtain ⟨a, ha, m, hm, e⟩ := exists_mul_of_mem_sup h he
      exact ⟨a, ha, m, (le_sup_right : M ≤ D ⊔ M) hm, e⟩
  have h2 : D.relIndex ((D ⊔ M) ⊓ A) = D.relIndex (A ⊓ M) :=
    relIndex_eq_of_forall_mul (le_inf (inf_le_right.trans le_sup_right) inf_le_left)
      fun e he => by
        obtain ⟨d, hd, m, hm, e'⟩ := exists_mul_of_mem_sup (fun s hs => h s (hDA hs)) he.1
        refine ⟨d * m * d⁻¹, ⟨?_, h d (hDA hd) m hm⟩, d, hd, by rw [← e']; simp⟩
        rw [e']
        exact A.mul_mem he.2 (A.inv_mem (hDA hd))
  have h3 : (D ⊓ M).relIndex (A ⊓ M) = D.relIndex (A ⊓ M) := by
    rw [← Subgroup.inf_relIndex_right D, ← Subgroup.inf_relIndex_right (D ⊓ M)]
    congr 1
    rw [inf_comm A M, ← inf_assoc, ← inf_assoc, inf_assoc D M M, inf_idem]
  rw [h1, h3, ← h2, Subgroup.relIndex_inf_mul_relIndex, inf_eq_left.2 le_sup_left]

/- English proof (translation)
Introduce `G _ R M A B _ hA hB hn hAB hBA`. Prove the components needed by the constructor for the conclusion. Establish `eA` using `relIndex_eq_inf_mul_sup (D := A ⊓ B) (M := M) inf_le_left (fun s hs => hn s (hA hs))`. Establish `eB` using `relIndex_eq_inf_mul_sup (D := A ⊓ B) (M := M) inf_le_right (fun s hs => hn s (hB hs))`. Establish `dA : (A ⊓ B).relIndex A ≠ 0` using `by rwa [Subgroup.inf_relIndex_left]`.

Establish `dA'` using `dA`. Rewrite `dA'` using `[eA, mul_ne_zero_iff]`. Rewrite using `[GlobalTheory.HL.invVol_eq_div_of_le inf_le_left inf_le_right dA, GlobalTheory.HL.invVol_eq_div_of_le (inf_le_inf_right M inf_le_left) (inf_le_inf_right M inf_le_right) dA'.1, GlobalTheory.HL.invVol_eq_div_of_le (sup_le_sup_right inf_le_left M) (sup_le_sup_right inf_le_right M) d …`. Use `push_cast`. Rewrite using `[div_mul_div_comm]`.

Introduce `B' hB' h1 h2`. Establish `dA : (A ⊓ B').relIndex A ≠ 0` using `by rwa [Subgroup.inf_relIndex_left]`. Establish `dB : (A ⊓ B').relIndex B ≠ 0` using `Subgroup.relIndex_inf_ne_zero hAB (Subgroup.relIndex_ne_zero_trans h1 hAB)`. Establish `dB' : (A ⊓ B').relIndex B' ≠ 0` using `by rwa [Subgroup.inf_relIndex_right]`. Establish `hle : GlobalTheory.HL.invVol A B ≤ GlobalTheory.HL.invVol A B'`.

Rewrite using `[GlobalTheory.HL.invVol_eq_div_of_le inf_le_left (inf_le_right.trans hB') dA, GlobalTheory.HL.invVol_eq_div_of_le inf_le_left inf_le_right dA]`. Use `div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by exact_mod_cast Nat.pos_of_ne_zero dB') ?_` and prove the remaining obligations. Conclude with `Subgroup.relIndex_le_of_le_right hB' dB` after adjusting the coercions. Use `⟨hle, hle.trans ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.HL.invVol]`.

Conclude with `div_le_self (Nat.cast_nonneg _) (by exact_mod_cast Nat.pos_of_ne_zero h2)`.
-/
theorem invVol_eq_inf_mul_sup_and_mono : ∀ (G : Type) [Group G] (R M A B : Subgroup G), M ≤ R → A ≤ R → B ≤ R → (∀ s ∈ R, ∀ t ∈ M, s * t * s⁻¹ ∈ M) → A.relIndex B ≠ 0 → B.relIndex A ≠ 0 → GlobalTheory.HL.invVol A B = GlobalTheory.HL.invVol (A ⊓ M) (B ⊓ M) * GlobalTheory.HL.invVol (A ⊔ M) (B ⊔ M) ∧ ∀ B' ≤ B, B'.relIndex A ≠ 0 → A.relIndex B' ≠ 0 → GlobalTheory.HL.invVol A B ≤ GlobalTheory.HL.invVol A B' ∧ GlobalTheory.HL.invVol A B ≤ (B'.relIndex A : ℝ) := by
  intro G _ R M A B _ hA hB hn hAB hBA
  constructor
  · have eA := relIndex_eq_inf_mul_sup (D := A ⊓ B) (M := M) inf_le_left
      (fun s hs => hn s (hA hs))
    have eB := relIndex_eq_inf_mul_sup (D := A ⊓ B) (M := M) inf_le_right
      (fun s hs => hn s (hB hs))
    have dA : (A ⊓ B).relIndex A ≠ 0 := by rwa [Subgroup.inf_relIndex_left]
    have dA' := dA
    rw [eA, mul_ne_zero_iff] at dA'
    rw [GlobalTheory.HL.invVol_eq_div_of_le inf_le_left inf_le_right dA,
      GlobalTheory.HL.invVol_eq_div_of_le (inf_le_inf_right M inf_le_left)
        (inf_le_inf_right M inf_le_right) dA'.1,
      GlobalTheory.HL.invVol_eq_div_of_le (sup_le_sup_right inf_le_left M)
        (sup_le_sup_right inf_le_right M) dA'.2, eA, eB]
    push_cast
    rw [div_mul_div_comm]
  · intro B' hB' h1 h2
    have dA : (A ⊓ B').relIndex A ≠ 0 := by rwa [Subgroup.inf_relIndex_left]
    have dB : (A ⊓ B').relIndex B ≠ 0 :=
      Subgroup.relIndex_inf_ne_zero hAB (Subgroup.relIndex_ne_zero_trans h1 hAB)
    have dB' : (A ⊓ B').relIndex B' ≠ 0 := by rwa [Subgroup.inf_relIndex_right]
    have hle : GlobalTheory.HL.invVol A B ≤ GlobalTheory.HL.invVol A B' := by
      rw [GlobalTheory.HL.invVol_eq_div_of_le inf_le_left (inf_le_right.trans hB') dA,
        GlobalTheory.HL.invVol_eq_div_of_le inf_le_left inf_le_right dA]
      refine div_le_div_of_nonneg_left (Nat.cast_nonneg _)
        (by exact_mod_cast Nat.pos_of_ne_zero dB') ?_
      exact_mod_cast Subgroup.relIndex_le_of_le_right hB' dB
    refine ⟨hle, hle.trans ?_⟩
    rw [GlobalTheory.HL.invVol]
    exact div_le_self (Nat.cast_nonneg _) (by exact_mod_cast Nat.pos_of_ne_zero h2)

end GlobalTheory.IndexProd
