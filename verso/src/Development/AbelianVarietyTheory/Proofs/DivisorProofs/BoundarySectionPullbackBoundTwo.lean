import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticLogResolution
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSNCAtlasOfIsEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncComponentHolomorphicAtlasStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncAtlasRankDropPotentialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundaryPotentialSectionAtlasStatement

namespace GlobalTheory.ResDivBound

open MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions GlobalTheory.LogResInt
open scoped ENNReal

/- English proof (translation)
Introduce `d X _ _ _ A m α Λ σ c hset L s hL hs hs1 n Y _ _ _ B hB μ hμ r W e hsnc hRD w K hw hpsh hbd`. Use `choose Bk hBk hBkA using GlobalTheory.T.snc_component_holomorphic_atlas n Y B X μ (m + 1) r (Fin.cons L Λ) (Fin.cons s σ) W e hsnc`. Use `⟨Bk, hBk, ?_⟩` and prove the remaining obligations. Establish `key : ∀ k, ∃ c : ℝ, ∀ (R : ℕ) (T : Fin n → LocPot Y), (∀ i, T i = (α + LocPot.ofFun (w R)).pullback μ hμ.1 ∨ T i = α.pullback μ hμ.1) → 1 ≤ e 0 k → -c ≤ mInt (Bk k) (fun i => (T i).pullback Subtype.val continuous_subtype_val) (fun y => w R (μ y.1))`. Introduce `k`.

Distinguish the cases in `hk : ∃ i : Fin m, 1 ≤ e i.succ k`. Use `⟨0, fun R T hT he0 => ?_⟩ classical` and prove the remaining obligations. Set `Φ : Fin n → LocPot X` to `fun i => if T i = α.pullback μ hμ.1 then α else α + LocPot.ofFun (w R)`. Establish `hα : IsPotential A α` using `hset.1`. Establish `hΦ : ∀ i, IsPotential A (Φ i)`.

Introduce `i`. Distinguish the cases in `h : T i = α.pullback μ hμ.1`. Simplify using `only [Φ, if_pos h]`. Conclude with `hα`. Simplify using `only [Φ, if_neg h]`.

Conclude with `isPotentialAdd A _ _ hα (isPotential_ofFun A (w R) (hw R))`. Establish `hTΦ : (fun i => (T i).pullback (Subtype.val : W k → Y) continuous_subtype_val) = fun i => ((Φ i).pullback μ hμ.1).pullback (Subtype.val : W k → Y) continuous_subtype_val`. Use function extensionality and compare the values at `i`. Distinguish the cases in `h : T i = α.pullback μ hμ.1`. Simplify using `only [Φ, if_pos h, h]`.

Simplify using `only [Φ, if_neg h]`. Rewrite using `[(hT i).resolve_right h]`. Rewrite using `[hTΦ, GlobalTheory.T.snc_atlas_rank_drop_potential d n X Y A B μ hμ (m + 1) r (Fin.cons L Λ) (Fin.cons s σ) W e k (Bk k) (hBk k) (hBkA k) (hRD k he0 hk) Φ hΦ (fun y => w R (μ y.1))]`. Simplify using the standard rewrite rules. Use `push_neg at hk`.

Establish `hk' : ∀ i : Fin m, e i.succ k = 0` using `fun i => by have := hk i; omega`. Distinguish the cases in `he0 : 1 ≤ e 0 k`. Take `⟨c, hc⟩` from `GlobalTheory.T.boundary_potential_section_atlas d X A m α Λ σ c hset L s hL hs hs1 n Y B hB μ hμ r W e hsnc w K hw hpsh hbd k (Bk k) (hBk k) (hBkA k) he0 hk'`. Conclude with `⟨c, fun R T hT _ => hc R T hT⟩`. Conclude with `⟨0, fun R T hT h => absurd h he0⟩`.

Use `choose c hc using key`. Use `⟨∑ k, |c k|, fun R T hT k he0 => ?_⟩` and prove the remaining obligations. Establish `h1` using `hc k R T hT he0`. Establish `h2 : c k ≤ ∑ k, |c k|` using `(le_abs_self _).trans (Finset.single_le_sum (fun i _ => abs_nonneg (c i)) (Finset.mem_univ k))`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem divisor_terms_bounded : ∀ (d : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas d X) (m : ℕ) (α : LocPot X) (Λ : Fin m → LocPot X) (σ : Fin m → X → X → ℂ) (c : ℝ),
    IsBoundarySetting A α Λ σ c →
    ∀ (L : LocPot X) (s : X → X → ℂ), IsPotential A L → IsSection A L s → (∀ y, normSec L s y ≤ 1) →
    ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] (B : FinHolAtlas (n + 1) Y),
    IsProjective B → ∀ (μ : Y → X) (hμ : HoloMap B A μ) (r : ℕ) (W : Fin r → Set Y)
    (e : Fin (m + 1) → Fin r → ℕ),
    IsJointSNC B μ (Fin.cons L Λ) (Fin.cons s σ) W e →
    (∀ k, 1 ≤ e 0 k → (∃ i : Fin m, 1 ≤ e i.succ k) → RankDropAlong A μ B (W k)) →
    ∀ (w : ℕ → X → ℝ) (K : ℝ), (∀ R, A.Smooth (w R)) → (∀ R, IsPsh A (α + LocPot.ofFun (w R))) →
    (∀ R x, x ∉ boundary σ →
        -(K * (1 + ∑ i, Real.log (rFun (Λ i) (σ i) x))) ≤ w R x ∧ w R x ≤ 0) →
    ∃ Bk : ∀ k, FinHolAtlas n (W k), (∀ k, HoloMap (Bk k) B Subtype.val) ∧ ∃ C : ℝ,
      ∀ (R : ℕ) (T : Fin n → LocPot Y), (∀ k, T k = (α + LocPot.ofFun (w R)).pullback μ hμ.1 ∨ T k = α.pullback μ hμ.1) → ∀ k, 1 ≤ e 0 k →
        -C ≤ mInt (Bk k) (fun i => (T i).pullback Subtype.val continuous_subtype_val) (fun y => w R (μ y.1)) := by
  intro d X _ _ _ A m α Λ σ c hset L s hL hs hs1 n Y _ _ _ B hB μ hμ r W e hsnc hRD w K hw hpsh hbd
  choose Bk hBk hBkA using GlobalTheory.T.snc_component_holomorphic_atlas n Y B X μ (m + 1) r (Fin.cons L Λ) (Fin.cons s σ) W e hsnc
  refine ⟨Bk, hBk, ?_⟩
  have key : ∀ k, ∃ c : ℝ, ∀ (R : ℕ) (T : Fin n → LocPot Y),
      (∀ i, T i = (α + LocPot.ofFun (w R)).pullback μ hμ.1 ∨ T i = α.pullback μ hμ.1) → 1 ≤ e 0 k →
        -c ≤ mInt (Bk k) (fun i => (T i).pullback Subtype.val continuous_subtype_val)
          (fun y => w R (μ y.1)) := by
    intro k
    by_cases hk : ∃ i : Fin m, 1 ≤ e i.succ k
    · refine ⟨0, fun R T hT he0 => ?_⟩
      classical
      let Φ : Fin n → LocPot X := fun i =>
        if T i = α.pullback μ hμ.1 then α else α + LocPot.ofFun (w R)
      have hα : IsPotential A α := hset.1
      have hΦ : ∀ i, IsPotential A (Φ i) := by
        intro i
        by_cases h : T i = α.pullback μ hμ.1
        · simp only [Φ, if_pos h]; exact hα
        · simp only [Φ, if_neg h]
          exact isPotentialAdd A _ _ hα (isPotential_ofFun A (w R) (hw R))
      have hTΦ : (fun i => (T i).pullback (Subtype.val : W k → Y) continuous_subtype_val) =
          fun i => ((Φ i).pullback μ hμ.1).pullback (Subtype.val : W k → Y) continuous_subtype_val := by
        funext i
        by_cases h : T i = α.pullback μ hμ.1
        · simp only [Φ, if_pos h, h]
        · simp only [Φ, if_neg h]
          rw [(hT i).resolve_right h]
      rw [hTΦ, GlobalTheory.T.snc_atlas_rank_drop_potential d n X Y A B μ hμ (m + 1) r (Fin.cons L Λ) (Fin.cons s σ) W e k (Bk k) (hBk k)
        (hBkA k) (hRD k he0 hk) Φ hΦ (fun y => w R (μ y.1))]
      simp
    · push_neg at hk
      have hk' : ∀ i : Fin m, e i.succ k = 0 := fun i => by have := hk i; omega
      by_cases he0 : 1 ≤ e 0 k
      · obtain ⟨c, hc⟩ := GlobalTheory.T.boundary_potential_section_atlas d X A m α Λ σ c hset L s hL hs hs1 n Y B hB μ hμ r W e hsnc w K hw hpsh
          hbd k (Bk k) (hBk k) (hBkA k) he0 hk'
        exact ⟨c, fun R T hT _ => hc R T hT⟩
      · exact ⟨0, fun R T hT h => absurd h he0⟩
  choose c hc using key
  refine ⟨∑ k, |c k|, fun R T hT k he0 => ?_⟩
  have h1 := hc k R T hT he0
  have h2 : c k ≤ ∑ k, |c k| := (le_abs_self _).trans
    (Finset.single_le_sum (fun i _ => abs_nonneg (c i)) (Finset.mem_univ k))
  linarith

end GlobalTheory.ResDivBound
