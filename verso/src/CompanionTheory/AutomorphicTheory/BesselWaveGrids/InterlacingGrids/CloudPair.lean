import Mathlib
import CompanionTheory.AutomorphicTheory.BesselWaveGrids.InterlacingGrids.PairOKOfInterlace

namespace GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid

open Finset

/- English proof (translation)
Establish `hm : 0 < max d 1` using `lt_of_lt_of_le one_pos (le_max_right _ _)`. Establish `hmD : max d 1 ≤ D` using `max_le hD1 hD2`. Establish `h1 : 1 + c ≤ (1 + c) / max d 1 * D`. Rewrite using `[div_mul_eq_mul_div, le_div_iff₀ hm]`. Conclude with `mul_le_mul_of_nonneg_left hmD (by linarith)`.

Establish `h2 : (1 + (1 + c) / max d 1) * D = D + (1 + c) / max d 1 * D` using `by ring`. Rewrite using `[h2]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem cloud_pair_factor (a d c D : ℝ) (hc : 0 ≤ c) (ha : a ≤ d + 1 + c) (hD1 : d ≤ D)
    (hD2 : 1 ≤ D) : a ≤ (1 + (1 + c) / max d 1) * D := by
  have hm : 0 < max d 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hmD : max d 1 ≤ D := max_le hD1 hD2
  have h1 : 1 + c ≤ (1 + c) / max d 1 * D := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hm]
    exact mul_le_mul_of_nonneg_left hmD (by linarith)
  have h2 : (1 + (1 + c) / max d 1) * D = D + (1 + c) / max d 1 * D := by ring
  rw [h2]
  linarith

/- English proof (translation)
Set `φ : ℕ → ℕ` to `fun s => if 0 < Y + lam s then s else s + 1`. Establish `hF1 : ∀ s, 1 ≤ (1 + (1 + c) / max |Y + lam s| 1)` using `fun s => by`. Establish `: 0 ≤ (1 + c) / max |Y + lam s| 1` using `div_nonneg (by linarith) (le_trans zero_le_one (le_max_right _ _))`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hA0 : ∀ s, 0 ≤ |Y + ε + lam s| + c` using `fun s => by positivity`.

Establish `hD0 : ∀ i, 0 ≤ |Y + 1 / 2 + v i|` using `fun i => abs_nonneg _`. Apply the tactic sequence `have hε1 : |ε| ≤ 1 := by rcases hε with h | h <;> simp [h]`. Establish `hmaps : ∀ s ∈ ((Icc 1 (k - 1)).erase e), φ s ∈ Icc 1 k`. Introduce `s hs`. Rewrite `hs` using `[Finset.mem_erase, Finset.mem_Icc]`.

Rewrite using `[Finset.mem_Icc]`. Distinguish the cases in `hpos : 0 < Y + lam s`. Simplify using `only [φ, hpos, if_true]`. Use linear arithmetic over natural numbers and integers. Simplify using `only [φ, hpos, if_false]`.

Use linear arithmetic over natural numbers and integers. Establish `hkey : ∀ s ∈ ((Icc 1 (k - 1)).erase e), |Y + ε + lam s| + c ≤ (1 + (1 + c) / max |Y + lam s| 1) * |Y + 1 / 2 + v (φ s)|`. Introduce `s hs`. Establish `hs'` using `hs`. Rewrite `hs'` using `[Finset.mem_erase, Finset.mem_Icc]`.

Take `⟨hne, h1, h2⟩` from `hs'`. Establish `hPs` using `hp s h1 h2 hne`. Establish `hmem` using `hmaps s hs`. Rewrite `hmem` using `[Finset.mem_Icc]`. Apply `cloud_pair_factor _ _ _ _ hc` to reduce the goal to its premises.

Establish `h3 : |Y + ε + lam s| ≤ |Y + lam s| + |ε|`. Establish `h4 : Y + ε + lam s = (Y + lam s) + ε` using `by ring`. Rewrite using `[h4]`. Conclude with `abs_add_le _ _`. Combine the linear equalities and inequalities to obtain the conclusion.

Distinguish the cases in `hpos : 0 < Y + lam s`. Simplify using `only [φ, hpos, if_true]`. Establish `hv` using `hPs.1 (by linarith)`. Rewrite using `[abs_of_pos hpos]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [φ, hpos, if_false]`. Establish `hv` using `hPs.2 (by linarith)`. Rewrite using `[abs_of_nonpos (not_lt.1 hpos)]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `hden _ hmem.1 hmem.2`.

Establish `hinj : ∀ s ∈ ((Icc 1 (k - 1)).erase e), ∀ t ∈ ((Icc 1 (k - 1)).erase e), φ s = φ t → s = t`. Introduce `s hs t ht hst`. Rewrite `hs`, `ht` using `[Finset.mem_erase, Finset.mem_Icc]`. Apply the tactic sequence `by_cases h1 : 0 < Y + lam s <;> by_cases h2 : 0 < Y + lam t`. Simplify `hst` using `[φ, h1, h2]`.

Simplify using `only [φ, h1, h2, if_true, if_false] at hst`. It suffices to derive a contradiction. Establish `hg` using `hgap t ht.2.1 (by omega)`. Substitute `hst` using the available equality. Combine the linear relations using `[not_lt.1 h2]`.

Simplify using `only [φ, h1, h2, if_true, if_false] at hst`. It suffices to derive a contradiction. Establish `hg` using `hgap s hs.2.1 (by omega)`. Substitute `hst` using the available equality. Combine the linear relations using `[not_lt.1 h1]`.

Simplify using `only [φ, h1, h2, if_false] at hst`. Use linear arithmetic over natural numbers and integers. Establish `hFnn : ∀ s, 0 ≤ (1 + (1 + c) / max |Y + lam s| 1)` using `fun s => le_trans zero_le_one (hF1 s)`. Establish `hprodA : ∏ s ∈ ((Icc 1 (k - 1)).erase e), (|Y + ε + lam s| + c) ≤ (∏ s ∈ ((Icc 1 (k - 1)).erase e), (1 + (1 + c) / max |Y + lam s| 1)) * ∏ i ∈ Icc 1 k, |Y + 1 / 2 + v i|`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Finset.prod_image hinj]`. Use `_ ≤ (∏ s ∈ ((Icc 1 (k - 1)).erase e), (1 + (1 + c) / max |Y + lam s| 1)) * ∏ i ∈ Icc 1 k, |Y + 1 / 2 + v i| := by`. Apply `mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun s _ => hFnn s)` to reduce the goal to its premises. Establish `hsub : ((Icc 1 (k - 1)).erase e).image φ ⊆ Icc 1 k` using `fun i hi => by`. Take `⟨s, hs, rfl⟩` from `Finset.mem_image.1 hi`.

Conclude with `hmaps s hs`. Rewrite using `[← Finset.prod_sdiff hsub]`. Establish `h1 : 1 ≤ ∏ i ∈ Icc 1 k \ ((Icc 1 (k - 1)).erase e).image φ, |Y + 1 / 2 + v i|`. Establish `h5` using `Finset.prod_le_prod (s := Icc 1 k \ ((Icc 1 (k - 1)).erase e).image φ) (f := fun _ => (1 : ℝ)) (g := fun i => |Y + 1 / 2 + v i|) (fun _ _ => zero_le_one) (fun i hi => by`. Establish `hi'` using `(Finset.mem_Icc.1 (Finset.mem_sdiff.1 hi).1)`.

Conclude with `hden i hi'.1 hi'.2)`. Simplify using `using h5`. Establish `h0 : 0 ≤ ∏ i ∈ ((Icc 1 (k - 1)).erase e).image φ, |Y + 1 / 2 + v i|` using `Finset.prod_nonneg fun i _ => hD0 i`. Use the polynomial consequences of the given equalities and inequalities. Establish `hFS : ∏ s ∈ ((Icc 1 (k - 1)).erase e), (1 + (1 + c) / max |Y + lam s| 1) ≤ ∏ s ∈ (Icc 1 (k - 1)), (1 + (1 + c) / max |Y + lam s| 1)`.

Distinguish the cases in `he : e ∈ (Icc 1 (k - 1))`. Rewrite using `[← Finset.mul_prod_erase _ _ he]`. Establish `h0 : 0 ≤ ∏ s ∈ ((Icc 1 (k - 1)).erase e), (1 + (1 + c) / max |Y + lam s| 1)` using `Finset.prod_nonneg fun s _ => hFnn s`. Use polynomial arithmetic with `[hF1 e]`. Rewrite using `[Finset.erase_eq_of_notMem he]`.

Establish `hDnn : 0 ≤ ∏ i ∈ Icc 1 k, |Y + 1 / 2 + v i|` using `Finset.prod_nonneg fun i _ => hD0 i`. Establish `hFSnn : 0 ≤ ∏ s ∈ ((Icc 1 (k - 1)).erase e), (1 + (1 + c) / max |Y + lam s| 1)` using `Finset.prod_nonneg fun s _ => hFnn s`. Establish `hb1 : 1 ≤ b` using `by linarith`. Distinguish the cases in `he : e ∈ (Icc 1 (k - 1))`. Rewrite using `[← Finset.mul_prod_erase _ _ he]`.

Establish `hAe : |Y + ε + lam e| + c ≤ 3 * b`. Rewrite `he` using `[Finset.mem_Icc]`. Establish `hl` using `hlam e he.1 he.2`. Establish `h6 : |Y + ε + lam e| ≤ |Y| + |ε| + |lam e|` using `abs_add_three Y ε (lam e)`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hAnn : 0 ≤ ∏ s ∈ ((Icc 1 (k - 1)).erase e), (|Y + ε + lam s| + c)` using `Finset.prod_nonneg fun s _ => hA0 s`. Combine the equalities or inequalities in the displayed calculation. Combine the linear relations using `[mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hFS hDnn) (show (0 : ℝ) ≤ 3 * b by linarith)]`. Rewrite `hprodA` using `[Finset.erase_eq_of_notMem he]`. Establish `hX : 0 ≤ (∏ s ∈ (Icc 1 (k - 1)), (1 + (1 + c) / max |Y + lam s| 1)) * ∏ i ∈ Icc 1 k, |Y + 1 / 2 + v i|` using `mul_nonneg (Finset.prod_nonneg fun s _ => hFnn s) hDnn`.

Combine the linear relations using `[mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 3 * b by linarith) hX]`.
-/
theorem cloud_pair_le (k : ℕ) (lam v : ℕ → ℝ) (e : ℕ) (c g b Y ε : ℝ) (hk : 2 ≤ k) (hc : 0 ≤ c) (hg : 1 + c ≤ g)
    (hε : ε = 0 ∨ ε = 1) (hcb : c + 1 ≤ b) (hY : |Y| ≤ b)
    (hlam : ∀ s, 1 ≤ s → s ≤ k - 1 → |lam s| ≤ b)
    (hgap : ∀ s, 1 ≤ s → s + 1 ≤ k - 1 → lam (s + 1) + g ≤ lam s)
    (hp : PairOK k lam v e (-Y)) (hden : ∀ i, 1 ≤ i → i ≤ k → 1 ≤ |Y + 1 / 2 + v i|) :
    ∏ s ∈ Icc 1 (k - 1), (|Y + ε + lam s| + c) ≤
      3 * b * (∏ s ∈ Icc 1 (k - 1), (1 + (1 + c) / max |Y + lam s| 1)) *
        ∏ i ∈ Icc 1 k, |Y + 1 / 2 + v i| := by
  let φ : ℕ → ℕ := fun s => if 0 < Y + lam s then s else s + 1
  have hF1 : ∀ s, 1 ≤ (1 + (1 + c) / max |Y + lam s| 1) := fun s => by
    have : 0 ≤ (1 + c) / max |Y + lam s| 1 :=
      div_nonneg (by linarith) (le_trans zero_le_one (le_max_right _ _))
    linarith
  have hA0 : ∀ s, 0 ≤ |Y + ε + lam s| + c := fun s => by positivity
  have hD0 : ∀ i, 0 ≤ |Y + 1 / 2 + v i| := fun i => abs_nonneg _
  have hε1 : |ε| ≤ 1 := by rcases hε with h | h <;> simp [h]
  have hmaps : ∀ s ∈ ((Icc 1 (k - 1)).erase e), φ s ∈ Icc 1 k := by
    intro s hs
    rw [Finset.mem_erase, Finset.mem_Icc] at hs
    rw [Finset.mem_Icc]
    by_cases hpos : 0 < Y + lam s
    · simp only [φ, hpos, if_true]
      omega
    · simp only [φ, hpos, if_false]
      omega
  have hkey : ∀ s ∈ ((Icc 1 (k - 1)).erase e),
      |Y + ε + lam s| + c ≤ (1 + (1 + c) / max |Y + lam s| 1) * |Y + 1 / 2 + v (φ s)| := by
    intro s hs
    have hs' := hs
    rw [Finset.mem_erase, Finset.mem_Icc] at hs'
    obtain ⟨hne, h1, h2⟩ := hs'
    have hPs := hp s h1 h2 hne
    have hmem := hmaps s hs
    rw [Finset.mem_Icc] at hmem
    apply cloud_pair_factor _ _ _ _ hc
    · have h3 : |Y + ε + lam s| ≤ |Y + lam s| + |ε| := by
        have h4 : Y + ε + lam s = (Y + lam s) + ε := by ring
        rw [h4]
        exact abs_add_le _ _
      linarith
    · by_cases hpos : 0 < Y + lam s
      · simp only [φ, hpos, if_true]
        have hv := hPs.1 (by linarith)
        rw [abs_of_pos hpos]
        calc Y + lam s ≤ Y + 1 / 2 + v s := by linarith
          _ ≤ |Y + 1 / 2 + v s| := le_abs_self _
      · simp only [φ, hpos, if_false]
        have hv := hPs.2 (by linarith)
        rw [abs_of_nonpos (not_lt.1 hpos)]
        calc -(Y + lam s) ≤ -(Y + 1 / 2 + v (s + 1)) := by linarith
          _ ≤ |Y + 1 / 2 + v (s + 1)| := neg_le_abs _
    · exact hden _ hmem.1 hmem.2
  have hinj : ∀ s ∈ ((Icc 1 (k - 1)).erase e), ∀ t ∈ ((Icc 1 (k - 1)).erase e), φ s = φ t → s = t := by
    intro s hs t ht hst
    rw [Finset.mem_erase, Finset.mem_Icc] at hs ht
    by_cases h1 : 0 < Y + lam s <;> by_cases h2 : 0 < Y + lam t
    · simpa [φ, h1, h2] using hst
    · simp only [φ, h1, h2, if_true, if_false] at hst
      exfalso
      have hg := hgap t ht.2.1 (by omega)
      subst hst
      linarith [not_lt.1 h2]
    · simp only [φ, h1, h2, if_true, if_false] at hst
      exfalso
      have hg := hgap s hs.2.1 (by omega)
      subst hst
      linarith [not_lt.1 h1]
    · simp only [φ, h1, h2, if_false] at hst
      omega
  have hFnn : ∀ s, 0 ≤ (1 + (1 + c) / max |Y + lam s| 1) := fun s => le_trans zero_le_one (hF1 s)
  have hprodA : ∏ s ∈ ((Icc 1 (k - 1)).erase e), (|Y + ε + lam s| + c) ≤
      (∏ s ∈ ((Icc 1 (k - 1)).erase e), (1 + (1 + c) / max |Y + lam s| 1)) * ∏ i ∈ Icc 1 k, |Y + 1 / 2 + v i| := by
    calc ∏ s ∈ ((Icc 1 (k - 1)).erase e), (|Y + ε + lam s| + c)
        ≤ ∏ s ∈ ((Icc 1 (k - 1)).erase e), ((1 + (1 + c) / max |Y + lam s| 1) * |Y + 1 / 2 + v (φ s)|) :=
          Finset.prod_le_prod (fun s _ => hA0 s) hkey
      _ = (∏ s ∈ ((Icc 1 (k - 1)).erase e), (1 + (1 + c) / max |Y + lam s| 1)) * ∏ s ∈ ((Icc 1 (k - 1)).erase e), |Y + 1 / 2 + v (φ s)| :=
          Finset.prod_mul_distrib
      _ = (∏ s ∈ ((Icc 1 (k - 1)).erase e), (1 + (1 + c) / max |Y + lam s| 1)) * ∏ i ∈ ((Icc 1 (k - 1)).erase e).image φ, |Y + 1 / 2 + v i| := by
          rw [Finset.prod_image hinj]
      _ ≤ (∏ s ∈ ((Icc 1 (k - 1)).erase e), (1 + (1 + c) / max |Y + lam s| 1)) * ∏ i ∈ Icc 1 k, |Y + 1 / 2 + v i| := by
          apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun s _ => hFnn s)
          have hsub : ((Icc 1 (k - 1)).erase e).image φ ⊆ Icc 1 k := fun i hi => by
            obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hi
            exact hmaps s hs
          rw [← Finset.prod_sdiff hsub]
          have h1 : 1 ≤ ∏ i ∈ Icc 1 k \ ((Icc 1 (k - 1)).erase e).image φ, |Y + 1 / 2 + v i| := by
            have h5 := Finset.prod_le_prod (s := Icc 1 k \ ((Icc 1 (k - 1)).erase e).image φ) (f := fun _ => (1 : ℝ))
              (g := fun i => |Y + 1 / 2 + v i|) (fun _ _ => zero_le_one) (fun i hi => by
                have hi' := (Finset.mem_Icc.1 (Finset.mem_sdiff.1 hi).1)
                exact hden i hi'.1 hi'.2)
            simpa using h5
          have h0 : 0 ≤ ∏ i ∈ ((Icc 1 (k - 1)).erase e).image φ, |Y + 1 / 2 + v i| := Finset.prod_nonneg fun i _ => hD0 i
          nlinarith
  have hFS : ∏ s ∈ ((Icc 1 (k - 1)).erase e), (1 + (1 + c) / max |Y + lam s| 1) ≤ ∏ s ∈ (Icc 1 (k - 1)), (1 + (1 + c) / max |Y + lam s| 1) := by
    by_cases he : e ∈ (Icc 1 (k - 1))
    · rw [← Finset.mul_prod_erase _ _ he]
      have h0 : 0 ≤ ∏ s ∈ ((Icc 1 (k - 1)).erase e), (1 + (1 + c) / max |Y + lam s| 1) := Finset.prod_nonneg fun s _ => hFnn s
      nlinarith [hF1 e]
    · rw [Finset.erase_eq_of_notMem he]
  have hDnn : 0 ≤ ∏ i ∈ Icc 1 k, |Y + 1 / 2 + v i| := Finset.prod_nonneg fun i _ => hD0 i
  have hFSnn : 0 ≤ ∏ s ∈ ((Icc 1 (k - 1)).erase e), (1 + (1 + c) / max |Y + lam s| 1) := Finset.prod_nonneg fun s _ => hFnn s
  have hb1 : 1 ≤ b := by linarith
  by_cases he : e ∈ (Icc 1 (k - 1))
  · rw [← Finset.mul_prod_erase _ _ he]
    have hAe : |Y + ε + lam e| + c ≤ 3 * b := by
      rw [Finset.mem_Icc] at he
      have hl := hlam e he.1 he.2
      have h6 : |Y + ε + lam e| ≤ |Y| + |ε| + |lam e| := abs_add_three Y ε (lam e)
      linarith
    have hAnn : 0 ≤ ∏ s ∈ ((Icc 1 (k - 1)).erase e), (|Y + ε + lam s| + c) := Finset.prod_nonneg fun s _ => hA0 s
    calc (|Y + ε + lam e| + c) * ∏ s ∈ ((Icc 1 (k - 1)).erase e), (|Y + ε + lam s| + c)
        ≤ 3 * b * ((∏ s ∈ ((Icc 1 (k - 1)).erase e), (1 + (1 + c) / max |Y + lam s| 1)) * ∏ i ∈ Icc 1 k, |Y + 1 / 2 + v i|) :=
          mul_le_mul hAe hprodA hAnn (by linarith)
      _ ≤ 3 * b * (∏ s ∈ (Icc 1 (k - 1)), (1 + (1 + c) / max |Y + lam s| 1)) * ∏ i ∈ Icc 1 k, |Y + 1 / 2 + v i| := by
          linarith [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hFS hDnn)
            (show (0 : ℝ) ≤ 3 * b by linarith)]
  · rw [Finset.erase_eq_of_notMem he] at hprodA
    have hX : 0 ≤ (∏ s ∈ (Icc 1 (k - 1)), (1 + (1 + c) / max |Y + lam s| 1)) * ∏ i ∈ Icc 1 k, |Y + 1 / 2 + v i| :=
      mul_nonneg (Finset.prod_nonneg fun s _ => hFnn s) hDnn
    linarith [mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 3 * b by linarith) hX]

end GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
