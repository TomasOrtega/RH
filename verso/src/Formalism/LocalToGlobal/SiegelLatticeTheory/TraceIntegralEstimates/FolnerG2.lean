import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.FolnerS2

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal Pointwise

namespace Formalism.L2.S.Pv.FolnerG

open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.SW PI.QuotSetU.UnitaryGroupMassFormula.ModW PI.QuotSetU.UnitaryGroupMassFormula.ModW.MG
  Formalism.L2.S.Pv.FolnerAbs Formalism.L2.SG.Pf.EnergyAbs Formalism.L2.S.Pv.FolnerS

variable {k r : ℕ} {ι : Type} [Fintype ι] (z : ι → Fin (2 * r + k + 1) → ℂ)

def SP : Set (ι → GH k r) := {s | ∀ v, s v ∈ Sg k r (z v)}

def CP : Set (ι → GH k r) := {s | ∀ v, s v ∈ Cg k r (z v)}

def fP (s : ι → GH k r) : ℝ := ∑ v, fG k r (z v) (s v)

variable {z}

/- English proof (translation)
Unfold `fG`. Use `Real.sInf_nonneg ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨c, -, rfl⟩`. Unfold `nrm`. Check the signs of the components of the expression.
-/
theorem fG_nonneg (z0 : Fin (2 * r + k + 1) → ℂ) (g : GH k r) : 0 ≤ fG k r z0 g := by
  unfold fG
  refine Real.sInf_nonneg ?_
  rintro _ ⟨c, -, rfl⟩
  unfold nrm; positivity

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cjB_pi (b s : ι → GH k r) (v : ι) : cjB b s v = cjB (b v) (s v) := rfl

/- English proof (translation)
Establish `hCc : IsCompact (CP z)`. Establish `: CP z = Set.pi Set.univ (fun v => Cg k r (z v))` using `by ext s; simp [CP, Set.mem_pi]`. Rewrite using `[this]`. Conclude with `isCompact_univ_pi fun v => isCompact_Cg (hz v) (hT v)`. Use `isFolner_of_contract hμ (CP z) (fP z) ?_ ?_ ?_ (fun _ => aT k r) ?_ ?_` and prove the remaining obligations.

Conclude with `continuous_finsetSum _ fun v _ => (continuous_fG (hz v) (hT v)).comp (continuous_apply v)`. Introduce `c hc x`. Unfold `fP`. Conclude with `Finset.sum_congr rfl fun v _ => fG_mul_left (hc v) (x v)`. Introduce `ρ`.

Establish `hsub : {x | fP z x ≤ ρ} ∩ SP z ⊆ Set.pi Set.univ (fun v => {y | fG k r (z v) y ≤ ρ} ∩ Sg k r (z v))`. Introduce and unpack `s ⟨hs, hsS⟩ v -`. Use `⟨?_, hsS v⟩` and prove the remaining obligations. Use `show fG k r (z v) (s v) ≤ ρ`. Use `le_trans ?_ hs` and prove the remaining obligations.

Conclude with `Finset.single_le_sum (f := fun w => fG k r (z w) (s w)) (fun w _ => fG_nonneg _ _) (Finset.mem_univ v)`. Use `(isCompact_univ_pi fun v => isCompact_sublevel (hz v) (hT v) ρ).of_isClosed_subset ?_ hsub` and prove the remaining obligations. Use `(isClosed_le (continuous_finsetSum _ fun v _ => (continuous_fG (hz v) (hT v)).comp (continuous_apply v)) continuous_const).inter ?_` and prove the remaining obligations. Establish `: SP z = ⋂ v, (fun s : ι → GH k r => s v) ⁻¹' Sg k r (z v)` using `by ext s; simp [SP]`. Rewrite using `[this]`.

Conclude with `isClosed_iInter fun v => (isClosed_Sg (hz v) (hT v)).preimage (continuous_apply v)`. Introduce `s show (∀ v, s v ∈ Sg k r (z v)) ↔ ∀ v, cjB (fun _ => aT k r) s v ∈ Sg k r (z v)`. Conclude with `forall_congr' fun v => by rw [cjB_pi]; exact aT_iff (z v) (s v)`. Introduce `K hK hKS U hU hCU`. Take `⟨V, hV, hCV⟩` from `compact_open_separated_mul_right hCc hU hCU`.

Rewrite `hV` using `[nhds_pi, Filter.mem_pi']`. Take `⟨I, t, ht, hIt⟩` from `hV`. Establish `hev : ∀ v, ∀ᶠ m : ℕ in atTop, ∀ x ∈ (fun s : ι → GH k r => s v) '' K, cjB (aT k r ^ m) x ∈ Cg k r (z v) * t v` using `fun v => contractV (hz v) (hT v) _ (hK.image (continuous_apply v)) (by rintro _ ⟨s, hs, rfl⟩; exact hKS hs v) (t v) (ht v)`. Use `filter_upwards [Filter.eventually_all.2 hev] with m hm x hx`. Establish `hx' : ∀ v, cjB (aT k r ^ m) (x v) ∈ Cg k r (z v) * t v` using `fun v => hm v (x v) ⟨x, hx, rfl⟩`.

Use `choose c hc w hw hcw using hx'`. Use `hCV ⟨c, hc, w, hIt (fun v _ => hw v), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `v`. Use `show c v * w v = cjB ((fun _ => aT k r) ^ m) x v`. Rewrite using `[cjB_pi, Pi.pow_apply]`.

Conclude with `hcw v`.
-/
theorem isFolner_pi (hz : ∀ v, inWb k r (z v)) (hT : ∀ v, 0 < Tz k r (z v)) (μS : Measure (ι → GH k r))
    (hμ : IsHaarSub (SP z) μS) : IsFolner (SP z) μS := by
  have hCc : IsCompact (CP z) := by
    have : CP z = Set.pi Set.univ (fun v => Cg k r (z v)) := by ext s; simp [CP, Set.mem_pi]
    rw [this]; exact isCompact_univ_pi fun v => isCompact_Cg (hz v) (hT v)
  refine isFolner_of_contract hμ (CP z) (fP z) ?_ ?_ ?_ (fun _ => aT k r) ?_ ?_
  · exact continuous_finsetSum _ fun v _ => (continuous_fG (hz v) (hT v)).comp (continuous_apply v)
  · intro c hc x
    unfold fP
    exact Finset.sum_congr rfl fun v _ => fG_mul_left (hc v) (x v)
  · intro ρ
    have hsub : {x | fP z x ≤ ρ} ∩ SP z ⊆ Set.pi Set.univ (fun v => {y | fG k r (z v) y ≤ ρ} ∩ Sg k r (z v)) := by
      rintro s ⟨hs, hsS⟩ v -
      refine ⟨?_, hsS v⟩
      show fG k r (z v) (s v) ≤ ρ
      refine le_trans ?_ hs
      exact Finset.single_le_sum (f := fun w => fG k r (z w) (s w)) (fun w _ => fG_nonneg _ _) (Finset.mem_univ v)
    refine (isCompact_univ_pi fun v => isCompact_sublevel (hz v) (hT v) ρ).of_isClosed_subset ?_ hsub
    refine (isClosed_le (continuous_finsetSum _ fun v _ => (continuous_fG (hz v) (hT v)).comp (continuous_apply v))
      continuous_const).inter ?_
    have : SP z = ⋂ v, (fun s : ι → GH k r => s v) ⁻¹' Sg k r (z v) := by ext s; simp [SP]
    rw [this]
    exact isClosed_iInter fun v => (isClosed_Sg (hz v) (hT v)).preimage (continuous_apply v)
  · intro s
    show (∀ v, s v ∈ Sg k r (z v)) ↔ ∀ v, cjB (fun _ => aT k r) s v ∈ Sg k r (z v)
    exact forall_congr' fun v => by rw [cjB_pi]; exact aT_iff (z v) (s v)
  · intro K hK hKS U hU hCU
    obtain ⟨V, hV, hCV⟩ := compact_open_separated_mul_right hCc hU hCU
    rw [nhds_pi, Filter.mem_pi'] at hV
    obtain ⟨I, t, ht, hIt⟩ := hV
    have hev : ∀ v, ∀ᶠ m : ℕ in atTop, ∀ x ∈ (fun s : ι → GH k r => s v) '' K,
        cjB (aT k r ^ m) x ∈ Cg k r (z v) * t v := fun v =>
      contractV (hz v) (hT v) _ (hK.image (continuous_apply v)) (by rintro _ ⟨s, hs, rfl⟩; exact hKS hs v) (t v) (ht v)
    filter_upwards [Filter.eventually_all.2 hev] with m hm x hx
    have hx' : ∀ v, cjB (aT k r ^ m) (x v) ∈ Cg k r (z v) * t v := fun v => hm v (x v) ⟨x, hx, rfl⟩
    choose c hc w hw hcw using hx'
    refine hCV ⟨c, hc, w, hIt (fun v _ => hw v), ?_⟩
    funext v
    show c v * w v = cjB ((fun _ => aT k r) ^ m) x v
    rw [cjB_pi, Pi.pow_apply]
    exact hcw v

end Formalism.L2.S.Pv.FolnerG
