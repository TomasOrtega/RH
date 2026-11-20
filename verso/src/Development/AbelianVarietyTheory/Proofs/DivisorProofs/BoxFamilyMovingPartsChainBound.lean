import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLineBundleIsNefShiftOfNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFubiniStudyOfTotallyOrderedRatFnFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudyBundleIsNefOfNonnegWeightsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankLeFubiniStudyBoxFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudySubfamilyLeShiftFubiniStudyFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithKleimanHeightNefOfIsNefStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithSelfIntersectionMonoOfIsNefStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun j => h.1 (ι j), fun x j l => h.2 x (ι j) (ι l)⟩`.
-/
theorem Total.comp {X : Scheme.{0}} [IsIntegral X] {J J' : Type} {f : J → X.functionField} (h : Total f)
    (ι : J' → J) : Total (f ∘ ι) :=
  ⟨fun j => h.1 (ι j), fun x j l => h.2 x (ι j) (ι l)⟩

/- English proof (translation)
Establish `hnef` using `GlobalTheory.T.fubiniStudy_bundle_isNef_of_nonneg_weights hC k X p D hX M J f w hM hw`. Establish `hht` using `(GlobalTheory.T.arithKleiman_heightNef_of_isNef hC hA hS k X p D hX M hnef).2`. Take `⟨h, hh, rfl⟩` from `hμ`. Conclude with `hht h hh _`.
-/
theorem selfInter_nonneg_of_isFS (hC : GlobalTheory.Published.ArCalc) (hA : AmpleHS) (hS : SemiPull) {k : Type} [CommRing k]
    {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ} (hX : IsArithVar p D) {M : HermLB p} {J : Type} [Fintype J]
    {f : J → X.functionField} {w : J → ℝ} (hM : IsFS M f w) (hw : ∀ j, 0 ≤ w j) {μ : ℝ} (hμ : M.IsSelfInter μ) :
    0 ≤ μ := by
  have hnef := GlobalTheory.T.fubiniStudy_bundle_isNef_of_nonneg_weights hC k X p D hX M J f w hM hw
  have hht := (GlobalTheory.T.arithKleiman_heightNef_of_isNef hC hA hS k X p D hX M hnef).2
  obtain ⟨h, hh, rfl⟩ := hμ
  exact hht h hh _

/- English proof (translation)
Introduce `N`. Proceed by induction on `N with`. Consider the case `zero`. Introduce `J _ e n M μ _ hn _ hM hμ`. Establish `h0 : ∀ j, n j = 0` using `fun j => Nat.le_zero.1 (hn j)`.

Simplify using `only [h0, Nat.cast_zero, Finset.sum_const_zero, mul_zero]`. Conclude with `selfInter_nonneg_of_isFS hC hA hS hX hM (fun c => by simp [h0]) hμ`. Consider the case `succ N ih`. Introduce `J _ e n M μ he hn ht hM hμ`. Establish `hw0 : ∀ c : J × Finset (Fin D), 0 ≤ (n c.1 : ℝ) * Δ` using `fun c => by positivity`.

Distinguish the cases in `hJ : ∀ j, n j = 0`. Simplify using `only [hJ, Nat.cast_zero, Finset.sum_const_zero, mul_zero]`. Conclude with `selfInter_nonneg_of_isFS hC hA hS hX hM hw0 hμ`. Use `push_neg at hJ`. Take `⟨j₀, hj₀⟩` from `hJ`.

Set `J'` to `{j // 1 ≤ n j}`. Set `e' : J' → X.functionField` to `fun j => e j.1`. Set `n' : J' → ℕ` to `fun j => n j.1 - 1`. Set `ι : J' × Finset (Fin D) → J × Finset (Fin D)` to `fun c => (c.1.1, c.2)`. Establish `hι : Function.Injective ι`.

Introduce and unpack `⟨⟨a, ha⟩, s⟩ ⟨⟨b, hb⟩, t⟩ h`. Simplify using `only [ι, Prod.mk.injEq] at h`. Take `⟨rfl, rfl⟩` from `h`. Both sides reduce to the same expression. Establish `hbox : boxFam e' x = boxFam e x ∘ ι` using `rfl`.

Use `haveI : Nonempty (J' × Finset (Fin D)) := ⟨(⟨j₀, Nat.one_le_iff_ne_zero.2 hj₀⟩, ∅)⟩`. Establish `ht' : Total (boxFam e' x)` using `hbox ▸ ht.comp ι`. Take `⟨M', hM'⟩` from `GlobalTheory.T.exists_fubiniStudy_of_totallyOrdered_ratFnFamily k X p (J' × Finset (Fin D)) (boxFam e' x) (fun c => (n' c.1 : ℝ) * Δ) ht'`. Take `⟨h', hh'⟩` from `(hC.arExists k X p D hX).1 M'`. Establish `hμ' : M'.IsSelfInter (h' (genericPoint X))` using `⟨h', hh', rfl⟩`.

Establish `he' : LinearIndependent ℤ e'` using `he.comp _ Subtype.val_injective`. Establish `hn' : ∀ j, n' j ≤ N` using `fun j => by`. Use `hn j.1` as an intermediate fact. Simplify using `only [n']`. Use linear arithmetic over natural numbers and integers.

Establish `IH` using `ih J' e' n' M' _ he' hn' ht' hM' hμ'`. Establish `hw0' : ∀ c : J' × Finset (Fin D), 0 ≤ (n' c.1 : ℝ) * Δ` using `fun c => by positivity`. Establish `hstep : ∀ c : J' × Finset (Fin D), (n' c.1 : ℝ) * Δ + Δ ≤ (n (ι c).1 : ℝ) * Δ` using `fun c => by`. Establish `h1` using `c.1.2`. Simplify using `only [n', ι]`.

Rewrite using `[Nat.cast_sub h1]`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hle : Le (M'.shift (fun _ => Δ) fun _ => rfl) M` using `GlobalTheory.T.fubiniStudy_subfamily_le_shift_fubiniStudy_family k X p M M' (J × Finset (Fin D)) (J' × Finset (Fin D)) (boxFam e x) (fun c => (n c.1 : ℝ) * Δ) (fun c => (n' c.1 : ℝ) * Δ) ι Δ hι hM (hbox ▸ hM') hstep`. Establish `hnefM` using `GlobalTheory.T.fubiniStudy_bundle_isNef_of_nonneg_weights hC k X p D hX M _ _ _ hM hw0`.

Establish `hnefM'` using `GlobalTheory.T.fubiniStudy_bundle_isNef_of_nonneg_weights hC k X p D hX M' _ _ _ hM' hw0'`. Establish `hnefS` using `GlobalTheory.NefShift.isNef_shift_nonneg k X p D hX M' Δ hΔ.le hnefM'`. Establish `hsh` using `hC.arShift k X p D hX M' _ Δ hμ'`. Establish `hmono` using `GlobalTheory.T.arithSelfIntersection_mono_of_isNef hC hA hS k X p D hX M _ μ _ hnefM hnefS hle hμ hsh`. Establish `hrk` using `GlobalTheory.T.rank_le_fubiniStudy_boxFamily hC hA k X p D hX M' J' e' x (fun c => (n' c.1 : ℝ) * Δ) he' hx hw0' hM'`.

Establish `hsum : ∑ j, (n j : ℝ) = ∑ j : J', (n' j : ℝ) + Fintype.card J'`. Rewrite using `[← Fintype.sum_subtype_add_sum_subtype (fun j => 1 ≤ n j) (fun j => (n j : ℝ))]`. Establish `h2 : ∑ j : {j // ¬ 1 ≤ n j}, (n j.1 : ℝ) = 0` using `Finset.sum_eq_zero fun j _ => by`. Use `j.2` as an intermediate fact. Establish `: n j.1 = 0` using `by omega`.

Simplify using `[this]`. Rewrite using `[h2, add_zero]`. Establish `h3 : ∀ j : J', (n j.1 : ℝ) = (n' j : ℝ) + 1` using `fun j => by`. Simplify using `only [n']`. Rewrite using `[Nat.cast_sub j.2]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [h3, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]`. Both sides reduce to the same expression. Establish `hf : ((D + 1).factorial : ℝ) = ((D : ℝ) + 1) * D.factorial`. Rewrite using `[Nat.factorial_succ]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hcard : ((D + 1).factorial : ℝ) * Δ * Fintype.card J' ≤ ((D : ℝ) + 1) * Δ * gdeg M' D`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hf]`.

Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ ((D : ℝ) + 1) * Δ * gdeg M' D := mul_le_mul_of_nonneg_left hrk (by positivity)`. Rewrite using `[hsum, mul_add]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem levels_le_selfInter (hC : GlobalTheory.Published.ArCalc) (hA : AmpleHS) (hS : SemiPull) (k : Type) [CommRing k]
    (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsArithVar p D) (x : Fin D → X.functionField) (Δ : ℝ)
    (hx : AlgebraicIndependent ℤ x) (hΔ : 0 < Δ) :
    ∀ (N : ℕ) (J : Type) [Fintype J] (e : J → X.functionField) (n : J → ℕ) (M : HermLB p) (μ : ℝ),
      LinearIndependent ℤ e → (∀ j, n j ≤ N) → Total (boxFam e x) → IsFS M (boxFam e x) (fun c => n c.1 * Δ) →
      M.IsSelfInter μ → ((D + 1).factorial : ℝ) * Δ * ∑ j, (n j : ℝ) ≤ μ := by
  intro N
  induction N with
  | zero =>
    intro J _ e n M μ _ hn _ hM hμ
    have h0 : ∀ j, n j = 0 := fun j => Nat.le_zero.1 (hn j)
    simp only [h0, Nat.cast_zero, Finset.sum_const_zero, mul_zero]
    exact selfInter_nonneg_of_isFS hC hA hS hX hM (fun c => by simp [h0]) hμ
  | succ N ih =>
    intro J _ e n M μ he hn ht hM hμ
    classical
    have hw0 : ∀ c : J × Finset (Fin D), 0 ≤ (n c.1 : ℝ) * Δ := fun c => by positivity
    by_cases hJ : ∀ j, n j = 0
    · simp only [hJ, Nat.cast_zero, Finset.sum_const_zero, mul_zero]
      exact selfInter_nonneg_of_isFS hC hA hS hX hM hw0 hμ
    push_neg at hJ
    obtain ⟨j₀, hj₀⟩ := hJ
    let J' := {j // 1 ≤ n j}
    let e' : J' → X.functionField := fun j => e j.1
    let n' : J' → ℕ := fun j => n j.1 - 1
    let ι : J' × Finset (Fin D) → J × Finset (Fin D) := fun c => (c.1.1, c.2)
    have hι : Function.Injective ι := by
      rintro ⟨⟨a, ha⟩, s⟩ ⟨⟨b, hb⟩, t⟩ h
      simp only [ι, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    have hbox : boxFam e' x = boxFam e x ∘ ι := rfl
    haveI : Nonempty (J' × Finset (Fin D)) := ⟨(⟨j₀, Nat.one_le_iff_ne_zero.2 hj₀⟩, ∅)⟩
    have ht' : Total (boxFam e' x) := hbox ▸ ht.comp ι
    obtain ⟨M', hM'⟩ := GlobalTheory.T.exists_fubiniStudy_of_totallyOrdered_ratFnFamily k X p (J' × Finset (Fin D)) (boxFam e' x) (fun c => (n' c.1 : ℝ) * Δ) ht'
    obtain ⟨h', hh'⟩ := (hC.arExists k X p D hX).1 M'
    have hμ' : M'.IsSelfInter (h' (genericPoint X)) := ⟨h', hh', rfl⟩
    have he' : LinearIndependent ℤ e' := he.comp _ Subtype.val_injective
    have hn' : ∀ j, n' j ≤ N := fun j => by
      have := hn j.1
      simp only [n']
      omega
    have IH := ih J' e' n' M' _ he' hn' ht' hM' hμ'
    have hw0' : ∀ c : J' × Finset (Fin D), 0 ≤ (n' c.1 : ℝ) * Δ := fun c => by positivity
    have hstep : ∀ c : J' × Finset (Fin D), (n' c.1 : ℝ) * Δ + Δ ≤ (n (ι c).1 : ℝ) * Δ := fun c => by
      have h1 := c.1.2
      simp only [n', ι]
      rw [Nat.cast_sub h1]
      push_cast
      linarith
    have hle : Le (M'.shift (fun _ => Δ) fun _ => rfl) M :=
      GlobalTheory.T.fubiniStudy_subfamily_le_shift_fubiniStudy_family k X p M M' (J × Finset (Fin D)) (J' × Finset (Fin D)) (boxFam e x) (fun c => (n c.1 : ℝ) * Δ)
        (fun c => (n' c.1 : ℝ) * Δ) ι Δ hι hM (hbox ▸ hM') hstep
    have hnefM := GlobalTheory.T.fubiniStudy_bundle_isNef_of_nonneg_weights hC k X p D hX M _ _ _ hM hw0
    have hnefM' := GlobalTheory.T.fubiniStudy_bundle_isNef_of_nonneg_weights hC k X p D hX M' _ _ _ hM' hw0'
    have hnefS := GlobalTheory.NefShift.isNef_shift_nonneg k X p D hX M' Δ hΔ.le hnefM'
    have hsh := hC.arShift k X p D hX M' _ Δ hμ'
    have hmono := GlobalTheory.T.arithSelfIntersection_mono_of_isNef hC hA hS k X p D hX M _ μ _ hnefM hnefS hle hμ hsh
    have hrk := GlobalTheory.T.rank_le_fubiniStudy_boxFamily hC hA k X p D hX M' J' e' x (fun c => (n' c.1 : ℝ) * Δ) he' hx hw0' hM'
    have hsum : ∑ j, (n j : ℝ) = ∑ j : J', (n' j : ℝ) + Fintype.card J' := by
      rw [← Fintype.sum_subtype_add_sum_subtype (fun j => 1 ≤ n j) (fun j => (n j : ℝ))]
      have h2 : ∑ j : {j // ¬ 1 ≤ n j}, (n j.1 : ℝ) = 0 :=
        Finset.sum_eq_zero fun j _ => by
          have := j.2
          have : n j.1 = 0 := by omega
          simp [this]
      rw [h2, add_zero]
      have h3 : ∀ j : J', (n j.1 : ℝ) = (n' j : ℝ) + 1 := fun j => by
        simp only [n']
        rw [Nat.cast_sub j.2]
        ring
      simp only [h3, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      rfl
    have hf : ((D + 1).factorial : ℝ) = ((D : ℝ) + 1) * D.factorial := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    have hcard : ((D + 1).factorial : ℝ) * Δ * Fintype.card J' ≤ ((D : ℝ) + 1) * Δ * gdeg M' D := by
      calc ((D + 1).factorial : ℝ) * Δ * Fintype.card J' = ((D : ℝ) + 1) * Δ * (D.factorial * Fintype.card J') := by
            rw [hf]; ring
        _ ≤ ((D : ℝ) + 1) * Δ * gdeg M' D := mul_le_mul_of_nonneg_left hrk (by positivity)
    rw [hsum, mul_add]
    linarith

/- English proof (translation)
Introduce `hC hA hS k _ X _ p D hX x Δ hx hΔ N J _ e n M μ he hn ht hM hμ`. Establish `key` using `levels_le_selfInter hC hA hS k X p D hX x Δ hx hΔ N J e n M μ he hn ht hM hμ`. Establish `hw0 : ∀ c : J × Finset (Fin D), 0 ≤ (n c.1 : ℝ) * Δ` using `fun c => by positivity`. Establish `hrk` using `GlobalTheory.T.rank_le_fubiniStudy_boxFamily hC hA k X p D hX M J e x (fun c => (n c.1 : ℝ) * Δ) he hx hw0 hM`. Establish `hf : ((D + 1).factorial : ℝ) = ((D : ℝ) + 1) * D.factorial`.

Rewrite using `[Nat.factorial_succ]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hcard : ((D + 1).factorial : ℝ) * Δ * Fintype.card J ≤ ((D : ℝ) + 1) * Δ * gdeg M D`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hf]`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ ((D : ℝ) + 1) * Δ * gdeg M D := mul_le_mul_of_nonneg_left hrk (by positivity)`. Establish `hsum : ((∑ j, (n j + 1) : ℕ) : ℝ) = ∑ j, (n j : ℝ) + Fintype.card J`. Use `push_cast`.

Rewrite using `[Finset.sum_add_distrib]`. Simplify using the standard rewrite rules. Rewrite using `[hsum, mul_add]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem chain_moving_parts : GlobalTheory.Published.ArCalc → AmpleHS → SemiPull → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (x : Fin D → X.functionField) (Δ : ℝ), AlgebraicIndependent ℤ x → 0 < Δ → ∀ (N : ℕ) (J : Type) [Fintype J] (e : J → X.functionField) (n : J → ℕ) (M : HermLB p) (μ : ℝ), LinearIndependent ℤ e → (∀ j, n j ≤ N) → Total (boxFam e x) → IsFS M (boxFam e x) (fun c => n c.1 * Δ) → M.IsSelfInter μ → ((D + 1).factorial : ℝ) * Δ * ((∑ j, (n j + 1) : ℕ) : ℝ) ≤ μ + ((D : ℝ) + 1) * Δ * gdeg M D := by
  intro hC hA hS k _ X _ p D hX x Δ hx hΔ N J _ e n M μ he hn ht hM hμ
  have key := levels_le_selfInter hC hA hS k X p D hX x Δ hx hΔ N J e n M μ he hn ht hM hμ
  have hw0 : ∀ c : J × Finset (Fin D), 0 ≤ (n c.1 : ℝ) * Δ := fun c => by positivity
  have hrk := GlobalTheory.T.rank_le_fubiniStudy_boxFamily hC hA k X p D hX M J e x (fun c => (n c.1 : ℝ) * Δ) he hx hw0 hM
  have hf : ((D + 1).factorial : ℝ) = ((D : ℝ) + 1) * D.factorial := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hcard : ((D + 1).factorial : ℝ) * Δ * Fintype.card J ≤ ((D : ℝ) + 1) * Δ * gdeg M D := by
    calc ((D + 1).factorial : ℝ) * Δ * Fintype.card J = ((D : ℝ) + 1) * Δ * (D.factorial * Fintype.card J) := by
          rw [hf]; ring
      _ ≤ ((D : ℝ) + 1) * Δ * gdeg M D := mul_le_mul_of_nonneg_left hrk (by positivity)
  have hsum : ((∑ j, (n j + 1) : ℕ) : ℝ) = ∑ j, (n j : ℝ) + Fintype.card J := by
    push_cast
    rw [Finset.sum_add_distrib]
    simp
  rw [hsum, mul_add]
  linarith

end GlobalTheory.HSNef
