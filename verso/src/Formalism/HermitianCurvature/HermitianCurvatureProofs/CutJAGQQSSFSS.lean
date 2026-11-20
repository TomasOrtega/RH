import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGQQSSFCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormalFormOrderZeroOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CoordinateCommuteRaisingConstant
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCRadSpSmooth

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.GQ

noncomputable section

section gen

variable {P : M.Par} {A : Type} [Ring A] [Algebra ℂ A]

def pj (κ : (M.Ty P → ℂ) →ₐ[ℂ] A) (ρ : M.Ty P) : A := κ fun σ => if σ = ρ then 1 else 0

variable (κ : (M.Ty P → ℂ) →ₐ[ℂ] A) (S : ℕ → A)

/- English proof (translation)
Unfold `pj`. Rewrite using `[← map_mul, ← map_smul]`. Use `congr 1`. Use function extensionality and compare the values at `σ`. Distinguish the cases in `hσ : σ = ρ`.

Substitute `hσ` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hσ]`.
-/
theorem kap_pj (h : M.Ty P → ℂ) (ρ : M.Ty P) : κ h * pj κ ρ = h ρ • pj κ ρ := by
  unfold pj
  rw [← map_mul, ← map_smul]
  congr 1
  funext σ
  by_cases hσ : σ = ρ
  · subst hσ; simp
  · simp [hσ]

/- English proof (translation)
Unfold `pj`. Rewrite using `[← map_mul, ← map_smul]`. Use `congr 1`. Use function extensionality and compare the values at `σ`. Distinguish the cases in `hσ : σ = ρ`.

Substitute `hσ` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hσ]`.
-/
theorem pj_kap (h : M.Ty P → ℂ) (ρ : M.Ty P) : pj κ ρ * κ h = h ρ • pj κ ρ := by
  unfold pj
  rw [← map_mul, ← map_smul]
  congr 1
  funext σ
  by_cases hσ : σ = ρ
  · subst hσ; simp
  · simp [hσ]

/- English proof (translation)
Unfold `pj`. Rewrite using `[← map_mul, ← map_zero κ]`. Use `congr 1`. Use function extensionality and compare the values at `τ`. Distinguish the cases in `h1 : τ = ρ`.

Substitute `h1` using the available equality. Simplify using `[h]`. Simplify using `[h1]`.
-/
theorem pj_mul_ne {ρ σ : M.Ty P} (h : ρ ≠ σ) : pj κ ρ * pj κ σ = 0 := by
  unfold pj
  rw [← map_mul, ← map_zero κ]
  congr 1
  funext τ
  by_cases h1 : τ = ρ
  · subst h1; simp [h]
  · simp [h1]

/- English proof (translation)
Unfold `pj`. Rewrite using `[← map_sum, ← map_one κ]`. Use `congr 1`. Use function extensionality and compare the values at `σ`. Simplify using `[Finset.sum_apply]`.
-/
theorem sum_pj : ∑ ρ, pj κ ρ = 1 := by
  unfold pj
  rw [← map_sum, ← map_one κ]
  congr 1
  funext σ
  simp [Finset.sum_apply]

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_mul, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun ρ' _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`.
-/
theorem decomp' (a : A) : a = ∑ ρ', ∑ ρ, pj κ ρ' * a * pj κ ρ := by
  calc a = 1 * a * 1 := by rw [one_mul, mul_one]
    _ = (∑ ρ', pj κ ρ') * a * (∑ ρ, pj κ ρ) := by rw [sum_pj κ]
    _ = ∑ ρ', ∑ ρ, pj κ ρ' * a * pj κ ρ := by
      rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun ρ' _ => ?_
      rw [Finset.mul_sum]

def Rai : Prop := ∀ l (f g : M.Ty P → ℂ), (∀ ρ ρ', M.Up P l ρ ρ' → g ρ' = f ρ) → κ g * S l = S l * κ f

def RaiS : Prop := ∀ l (f g : M.Ty P → ℂ), (∀ ρ ρ', M.Up P l ρ ρ' → g ρ' = f ρ) → S l * κ g = κ f * S l

/- English proof (translation)
Introduce `σ τ hU`. Distinguish the cases in `h : τ = ρ'`. Substitute `h` using the available equality. Simplify using `[hU]`. Establish `h2 : ¬ M.Up P l σ ρ'`.

Introduce `h2`. Apply `h` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Conclude with `Fin.ext ((hU i).trans (h2 i).symm)`. Simplify using `[h, h2]`.
-/
theorem rai_ind {l : ℕ} {ρ' : M.Ty P} :
    ∀ σ τ, M.Up P l σ τ → (fun τ : M.Ty P => if τ = ρ' then (1 : ℂ) else 0) τ =
      (fun σ : M.Ty P => if M.Up P l σ ρ' then (1 : ℂ) else 0) σ := by
  intro σ τ hU
  by_cases h : τ = ρ'
  · subst h; simp [hU]
  · have h2 : ¬ M.Up P l σ ρ' := by
      intro h2
      apply h
      funext i
      exact Fin.ext ((hU i).trans (h2 i).symm)
    simp [h, h2]

/- English proof (translation)
Establish `h1 : pj κ ρ' * S l = S l * κ (fun σ : M.Ty P => if M.Up P l σ ρ' then (1 : ℂ) else 0)` using `hR l (fun σ => if M.Up P l σ ρ' then 1 else 0) (fun τ => if τ = ρ' then 1 else 0) rai_ind`. Rewrite using `[h1, mul_assoc, kap_pj]`. Simplify using `[h]`.
-/
theorem blk_zero (hR : Rai κ S) {l : ℕ} {ρ ρ' : M.Ty P} (h : ¬ M.Up P l ρ ρ') : pj κ ρ' * S l * pj κ ρ = 0 := by
  have h1 : pj κ ρ' * S l = S l * κ (fun σ : M.Ty P => if M.Up P l σ ρ' then (1 : ℂ) else 0) :=
    hR l (fun σ => if M.Up P l σ ρ' then 1 else 0) (fun τ => if τ = ρ' then 1 else 0) rai_ind
  rw [h1, mul_assoc, kap_pj]
  simp [h]

/- English proof (translation)
Establish `h1 : S l * pj κ ρ' = κ (fun σ : M.Ty P => if M.Up P l σ ρ' then (1 : ℂ) else 0) * S l` using `hR l (fun σ => if M.Up P l σ ρ' then 1 else 0) (fun τ => if τ = ρ' then 1 else 0) rai_ind`. Rewrite using `[mul_assoc, h1, ← mul_assoc, pj_kap]`. Simplify using `[h]`.
-/
theorem blk_zeroS (hR : RaiS κ S) {l : ℕ} {ρ ρ' : M.Ty P} (h : ¬ M.Up P l ρ ρ') : pj κ ρ * S l * pj κ ρ' = 0 := by
  have h1 : S l * pj κ ρ' = κ (fun σ : M.Ty P => if M.Up P l σ ρ' then (1 : ℂ) else 0) * S l :=
    hR l (fun σ => if M.Up P l σ ρ' then 1 else 0) (fun τ => if τ = ρ' then 1 else 0) rai_ind
  rw [mul_assoc, h1, ← mul_assoc, pj_kap]
  simp [h]

/- English proof (translation)
Rewrite `hl` using `[Finset.mem_Icc]`. Take `⟨i, hi⟩ : ∃ i : Fin (P.k - 1), (i : ℕ) + 1 = l` from `⟨⟨l - 1, by omega⟩, show l - 1 + 1 = l by omega⟩`. Establish `h1` using `hU i`. Rewrite `h1` using `[if_pos hi]`. Use `⟨fun h => ?_, fun j hj h2 => ?_⟩` and prove the remaining obligations.

Substitute `h` using the available equality. Use linear arithmetic over natural numbers and integers. Establish `h3` using `h2 i`. Rewrite `h3` using `[if_neg (by omega)]`. Use linear arithmetic over natural numbers and integers.
-/
private theorem ne_and_unique_index_of_up {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) {ρ ρ' : M.Ty P}
    (hU : M.Up P l ρ ρ') : ρ ≠ ρ' ∧ ∀ j, j ≠ l → ¬ M.Up P j ρ ρ' := by
  rw [Finset.mem_Icc] at hl
  obtain ⟨i, hi⟩ : ∃ i : Fin (P.k - 1), (i : ℕ) + 1 = l := ⟨⟨l - 1, by omega⟩, show l - 1 + 1 = l by omega⟩
  have h1 := hU i
  rw [if_pos hi] at h1
  refine ⟨fun h => ?_, fun j hj h2 => ?_⟩
  · subst h
    omega
  · have h3 := h2 i
    rw [if_neg (by omega)] at h3
    omega

/- English proof (translation)
Take `⟨hne, hoth⟩` from `ne_and_unique_index_of_up hl hU`. Establish `hc : pj κ ρ' * B = B * pj κ ρ'` using `(hB _).eq`. Establish `hB0 : pj κ ρ' * B * pj κ ρ = 0`. Rewrite using `[hc, mul_assoc, pj_mul_ne κ (Ne.symm hne), mul_zero]`. Establish `hterm : ∀ j, pj κ ρ' * (S j * κ (fun π => M.xEx P {j} π Y)) * pj κ ρ = M.xEx P {j} ρ Y • (pj κ ρ' * S j * pj κ ρ)`.

Introduce `j`. Rewrite using `[← mul_assoc, mul_assoc _ (κ _), kap_pj, mul_smul_comm]`. Rewrite using `[mul_add, add_mul, hB0, zero_add, Finset.mul_sum, Finset.sum_mul, Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_eq_single l]`. Introduce `j _ hjl`. Rewrite using `[blk_zero κ S hR (hoth j hjl), smul_zero]`.

Introduce `h`. Conclude with `absurd hl h`.
-/
theorem projected_block_lower_sum (hR : Rai κ S) {B : A} (hB : ∀ f, Commute (κ f) B) {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1))
    {ρ ρ' : M.Ty P} (hU : M.Up P l ρ ρ') (Y : ℂ) :
    pj κ ρ' * (B + ∑ j ∈ Finset.Icc 1 (P.k - 1), S j * κ (fun π => M.xEx P {j} π Y)) * pj κ ρ =
      M.xEx P {l} ρ Y • (pj κ ρ' * S l * pj κ ρ) := by
  obtain ⟨hne, hoth⟩ := ne_and_unique_index_of_up hl hU
  have hc : pj κ ρ' * B = B * pj κ ρ' := (hB _).eq
  have hB0 : pj κ ρ' * B * pj κ ρ = 0 := by
    rw [hc, mul_assoc, pj_mul_ne κ (Ne.symm hne), mul_zero]
  have hterm : ∀ j, pj κ ρ' * (S j * κ (fun π => M.xEx P {j} π Y)) * pj κ ρ =
      M.xEx P {j} ρ Y • (pj κ ρ' * S j * pj κ ρ) := by
    intro j
    rw [← mul_assoc, mul_assoc _ (κ _), kap_pj, mul_smul_comm]
  rw [mul_add, add_mul, hB0, zero_add, Finset.mul_sum, Finset.sum_mul,
    Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_eq_single l]
  · intro j _ hjl
    rw [blk_zero κ S hR (hoth j hjl), smul_zero]
  · intro h
    exact absurd hl h

/- English proof (translation)
Take `⟨hne, hoth⟩` from `ne_and_unique_index_of_up hl hU`. Establish `hc : pj κ ρ * B = B * pj κ ρ` using `(hB _).eq`. Establish `hB0 : pj κ ρ * B * pj κ ρ' = 0`. Rewrite using `[hc, mul_assoc, pj_mul_ne κ hne, mul_zero]`. Establish `hterm : ∀ j, pj κ ρ * (κ (fun π => M.xEx P {j} π Y) * S j) * pj κ ρ' = M.xEx P {j} ρ Y • (pj κ ρ * S j * pj κ ρ')`.

Introduce `j`. Rewrite using `[← mul_assoc, pj_kap, smul_mul_assoc, smul_mul_assoc]`. Rewrite using `[mul_add, add_mul, hB0, zero_add, Finset.mul_sum, Finset.sum_mul, Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_eq_single l]`. Introduce `j _ hjl`. Rewrite using `[blk_zeroS κ S hR (hoth j hjl), smul_zero]`.

Introduce `h`. Conclude with `absurd hl h`.
-/
theorem projected_block_upper_sum (hR : RaiS κ S) {B : A} (hB : ∀ f, Commute (κ f) B) {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1))
    {ρ ρ' : M.Ty P} (hU : M.Up P l ρ ρ') (Y : ℂ) :
    pj κ ρ * (B + ∑ j ∈ Finset.Icc 1 (P.k - 1), κ (fun π => M.xEx P {j} π Y) * S j) * pj κ ρ' =
      M.xEx P {l} ρ Y • (pj κ ρ * S l * pj κ ρ') := by
  obtain ⟨hne, hoth⟩ := ne_and_unique_index_of_up hl hU
  have hc : pj κ ρ * B = B * pj κ ρ := (hB _).eq
  have hB0 : pj κ ρ * B * pj κ ρ' = 0 := by
    rw [hc, mul_assoc, pj_mul_ne κ hne, mul_zero]
  have hterm : ∀ j, pj κ ρ * (κ (fun π => M.xEx P {j} π Y) * S j) * pj κ ρ' =
      M.xEx P {j} ρ Y • (pj κ ρ * S j * pj κ ρ') := by
    intro j
    rw [← mul_assoc, pj_kap, smul_mul_assoc, smul_mul_assoc]
  rw [mul_add, add_mul, hB0, zero_add, Finset.mul_sum, Finset.sum_mul,
    Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_eq_single l]
  · intro j _ hjl
    rw [blk_zeroS κ S hR (hoth j hjl), smul_zero]
  · intro h
    exact absurd hl h

def yl (l : ℕ) (ρ : M.Ty P) : ℝ := -M.rho P ρ l

/- English proof (translation)
Establish `hg` using `hP.gap m (Finset.mem_Icc.mpr ⟨h1, h2⟩)`. Establish `h3 : ((ρ ⟨m - 1, by omega⟩ : Fin _) : ℕ) ≤ P.wid m`. Establish `h4` using `(ρ ⟨m - 1, by omega⟩).isLt`. Establish `e : m - 1 + 1 = m` using `by omega`. Simplify using `only [Fin.val_mk, e] at h4`.

Use linear arithmetic over natural numbers and integers. Establish `hw : (((ρ ⟨m - 1, by omega⟩ : Fin _) : ℕ) : ℝ) ≤ P.hi m - P.lo m`. Combine the equalities or inequalities in the displayed calculation. Establish `h0 : (0 : ℝ) ≤ (((ρ ⟨m - 1, by omega⟩ : Fin _) : ℕ) : ℝ)` using `Nat.cast_nonneg _`. Unfold `M.rho`.

Rewrite using `[dif_pos ⟨h1, h2⟩]`. Apply the tactic sequence `constructor <;> linarith`.
-/
private theorem lo_le_rho_and_rho_le_hi (hP : P.OK) {m : ℕ} (h1 : 1 ≤ m) (h2 : m ≤ P.k - 1) (ρ : M.Ty P) :
    P.lo m ≤ M.rho P ρ m ∧ M.rho P ρ m ≤ P.hi m := by
  have hg := hP.gap m (Finset.mem_Icc.mpr ⟨h1, h2⟩)
  have h3 : ((ρ ⟨m - 1, by omega⟩ : Fin _) : ℕ) ≤ P.wid m := by
    have h4 := (ρ ⟨m - 1, by omega⟩).isLt
    have e : m - 1 + 1 = m := by omega
    simp only [Fin.val_mk, e] at h4
    omega
  have hw : (((ρ ⟨m - 1, by omega⟩ : Fin _) : ℕ) : ℝ) ≤ P.hi m - P.lo m := by
    calc (((ρ ⟨m - 1, by omega⟩ : Fin _) : ℕ) : ℝ) ≤ (P.wid m : ℝ) := by exact_mod_cast h3
      _ ≤ P.hi m - P.lo m := Nat.floor_le (by linarith)
  have h0 : (0 : ℝ) ≤ (((ρ ⟨m - 1, by omega⟩ : Fin _) : ℕ) : ℝ) := Nat.cast_nonneg _
  unfold M.rho
  rw [dif_pos ⟨h1, h2⟩]
  constructor <;> linarith

/- English proof (translation)
Unfold `M.Par.hi M.Par.lo`. Establish `h1` using `min_le_left (P.u (m + 1)) (P.u' (m + 1))`. Establish `h2` using `le_max_left (P.u (m + 1)) (P.u' (m + 1))`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem hi_succ_lt_lo (m : ℕ) : P.hi (m + 1) < P.lo m := by
  unfold M.Par.hi M.Par.lo
  have h1 := min_le_left (P.u (m + 1)) (P.u' (m + 1))
  have h2 := le_max_left (P.u (m + 1)) (P.u' (m + 1))
  linarith

/- English proof (translation)
Proceed by induction on `b, hab using Nat.le_induction with`. Consider the case `base => exact le_refl _`. Consider the case `succ n hn ih`. Establish `hg` using `hP.gap n (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)`. Establish `h1` using `hi_succ_lt_lo (P := P) n`.

Establish `h2` using `ih (by omega)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem hi_le_hi_of_le (hP : P.OK) {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ P.k - 1) :
    P.hi b ≤ P.hi a := by
  induction b, hab using Nat.le_induction with
  | base => exact le_refl _
  | succ n hn ih =>
    have hg := hP.gap n (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    have h1 := hi_succ_lt_lo (P := P) n
    have h2 := ih (by omega)
    linarith

/- English proof (translation)
Establish `h1` using `(lo_le_rho_and_rho_le_hi hP (by omega) hb ρ).2`. Establish `h2` using `hi_le_hi_of_le hP (a := a + 1) (b := b) (by omega) (by omega) hb`. Establish `h3` using `hi_succ_lt_lo (P := P) a`. Establish `h4` using `(lo_le_rho_and_rho_le_hi hP ha (by omega) ρ).1`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem rho_lt_rho_of_lt (hP : P.OK) {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) (hb : b ≤ P.k - 1) (ρ : M.Ty P) :
    M.rho P ρ b < M.rho P ρ a := by
  have h1 := (lo_le_rho_and_rho_le_hi hP (by omega) hb ρ).2
  have h2 := hi_le_hi_of_le hP (a := a + 1) (b := b) (by omega) (by omega) hb
  have h3 := hi_succ_lt_lo (P := P) a
  have h4 := (lo_le_rho_and_rho_le_hi hP ha (by omega) ρ).1
  linarith

/- English proof (translation)
Rewrite `hl`, `hi` using `[Finset.mem_Icc]`. Break down `Nat.lt_or_gt_of_ne hil with h | h` into its components or cases. Conclude with `ne_of_gt (rho_lt_rho_of_lt hP hi.1 h hl.2 ρ)`. Conclude with `ne_of_lt (rho_lt_rho_of_lt hP hl.1 h hi.2 ρ)`.
-/
private theorem rho_ne_rho_of_ne (hP : P.OK) {l i : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1))
    (hi : i ∈ Finset.Icc 1 (P.k - 1)) (hil : i ≠ l) (ρ : M.Ty P) : M.rho P ρ i ≠ M.rho P ρ l := by
  rw [Finset.mem_Icc] at hl hi
  rcases Nat.lt_or_gt_of_ne hil with h | h
  · exact ne_of_gt (rho_lt_rho_of_lt hP hi.1 h hl.2 ρ)
  · exact ne_of_lt (rho_lt_rho_of_lt hP hl.1 h hi.2 ρ)

/- English proof (translation)
Unfold `M.xEx yl`. Rewrite using `[Finset.prod_ne_zero_iff]`. Introduce `i hi`. Rewrite `hi` using `[Finset.mem_sdiff, Finset.mem_singleton]`. Establish `hne` using `rho_ne_rho_of_ne hP hl hi.1 hi.2 ρ`.

Introduce `h`. Apply `hne` to reduce the goal to its premises. Establish `h' : ((-(M.rho P ρ l) + M.rho P ρ i : ℝ) : ℂ) = 0` using `by exact_mod_cast h`. Establish `h''` using `Complex.ofReal_eq_zero.mp h'`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem xEx_yl_ne (hP : P.OK) {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) (ρ : M.Ty P) :
    M.xEx P {l} ρ ((yl l ρ : ℝ) : ℂ) ≠ 0 := by
  unfold M.xEx yl
  rw [Finset.prod_ne_zero_iff]
  intro i hi
  rw [Finset.mem_sdiff, Finset.mem_singleton] at hi
  have hne := rho_ne_rho_of_ne hP hl hi.1 hi.2 ρ
  intro h
  apply hne
  have h' : ((-(M.rho P ρ l) + M.rho P ρ i : ℝ) : ℂ) = 0 := by exact_mod_cast h
  have h'' := Complex.ofReal_eq_zero.mp h'
  linarith

/- English proof (translation)
Use `conv_lhs => rw [decomp' κ (S l)]`. Use `Finset.sum_congr rfl fun ρ' _ => Finset.sum_congr rfl fun ρ _ => ?_` and prove the remaining obligations. Use `split_ifs with hU`. Rewrite using `[hT, projected_block_lower_sum κ S hR (hB _) hl hU, smul_smul, inv_mul_cancel₀ (xEx_yl_ne hP hl ρ), one_smul]`. Conclude with `blk_zero κ S hR hU`.
-/
theorem ss_expand (hR : Rai κ S) (hP : P.OK) (T B : ℂ → A) (hB : ∀ Y f, Commute (κ f) (B Y))
    (hT : ∀ Y, T Y = B Y + ∑ j ∈ Finset.Icc 1 (P.k - 1), S j * κ (fun π => M.xEx P {j} π Y))
    {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) :
    S l = ∑ ρ', ∑ ρ, if M.Up P l ρ ρ' then
      (M.xEx P {l} ρ ((yl l ρ : ℝ) : ℂ))⁻¹ • (pj κ ρ' * T ((yl l ρ : ℝ) : ℂ) * pj κ ρ) else 0 := by
  conv_lhs => rw [decomp' κ (S l)]
  refine Finset.sum_congr rfl fun ρ' _ => Finset.sum_congr rfl fun ρ _ => ?_
  split_ifs with hU
  · rw [hT, projected_block_lower_sum κ S hR (hB _) hl hU, smul_smul, inv_mul_cancel₀ (xEx_yl_ne hP hl ρ), one_smul]
  · exact blk_zero κ S hR hU

/- English proof (translation)
Use `conv_lhs => rw [decomp' κ (S l)]`. Use `Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun ρ' _ => ?_` and prove the remaining obligations. Use `split_ifs with hU`. Rewrite using `[hT, projected_block_upper_sum κ S hR (hB _) hl hU, smul_smul, inv_mul_cancel₀ (xEx_yl_ne hP hl ρ), one_smul]`. Conclude with `blk_zeroS κ S hR hU`.
-/
theorem ssS_expand (hR : RaiS κ S) (hP : P.OK) (T B : ℂ → A) (hB : ∀ Y f, Commute (κ f) (B Y))
    (hT : ∀ Y, T Y = B Y + ∑ j ∈ Finset.Icc 1 (P.k - 1), κ (fun π => M.xEx P {j} π Y) * S j)
    {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) :
    S l = ∑ ρ, ∑ ρ', if M.Up P l ρ ρ' then
      (M.xEx P {l} ρ ((yl l ρ : ℝ) : ℂ))⁻¹ • (pj κ ρ * T ((yl l ρ : ℝ) : ℂ) * pj κ ρ') else 0 := by
  conv_lhs => rw [decomp' κ (S l)]
  refine Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun ρ' _ => ?_
  split_ifs with hU
  · rw [hT, projected_block_upper_sum κ S hR (hB _) hl hU, smul_smul, inv_mul_cancel₀ (xEx_yl_ne hP hl ρ), one_smul]
  · exact blk_zeroS κ S hR hU

end gen

section intw

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}
  {e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)}
  (hsm : ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') ρ,
      Gauge.rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ ∈ MA.smSub P.r P.TT)
include hsm

/- English proof (translation)
Introduce `Φ`. Establish `h0 : Gauge.GC.trR P Bs e 0 = 0`. Establish `h` using `Gauge.GC.trR_smul hsm (0 : ℂ) 0`. Rewrite `h` using `[zero_smul, zero_smul]`. Then use the resulting hypothesis. Rewrite using `[Gauge.actA_zero]`.

Conclude with `h0`.
-/
theorem intw_zero : Gauge.GC.Intw P Bs e 0 0 := by
  intro Φ
  have h0 : Gauge.GC.trR P Bs e 0 = 0 := by
    have h := Gauge.GC.trR_smul hsm (0 : ℂ) 0
    rwa [zero_smul, zero_smul] at h
  rw [Gauge.actA_zero]
  exact h0

/- English proof (translation)
Introduce `Φ`. Rewrite using `[Gauge.GC.actA_smulM, ← h Φ, ← Gauge.GC.trR_smul hsm]`. Both sides reduce to the same expression.
-/
theorem intw_smul' (c : ℂ) {X : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} {X' : MA.A P (MA.DQ P)}
    (h : Gauge.GC.Intw P Bs e X X') : Gauge.GC.Intw P Bs e (c • X) (c • X') := by
  intro Φ
  rw [Gauge.GC.actA_smulM, ← h Φ, ← Gauge.GC.trR_smul hsm]
  rfl

/- English proof (translation)
Introduce `Φ`. Rewrite using `[Gauge.actA_add, ← hX Φ, ← hY Φ, ← Gauge.GC.trR_add hsm]`. Both sides reduce to the same expression.
-/
private theorem intw_add' {X Y : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} {X' Y' : MA.A P (MA.DQ P)}
    (hX : Gauge.GC.Intw P Bs e X X') (hY : Gauge.GC.Intw P Bs e Y Y') :
    Gauge.GC.Intw P Bs e (X + Y) (X' + Y') := by
  intro Φ
  rw [Gauge.actA_add, ← hX Φ, ← hY Φ, ← Gauge.GC.trR_add hsm]
  rfl

/- English proof (translation)
Use `revert h`. Use `Finset.induction_on s (fun _ => ?_) (fun a t hat ih h => ?_)` and prove the remaining obligations. Rewrite using `[Finset.sum_empty, Finset.sum_empty]`. Conclude with `intw_zero hsm`. Rewrite using `[Finset.sum_insert hat, Finset.sum_insert hat]`.

Conclude with `intw_add' hsm (h a (Finset.mem_insert_self a t)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))`.
-/
theorem intw_sum' {ι : Type} (s : Finset ι) (X : ι → Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))
    (X' : ι → MA.A P (MA.DQ P)) (h : ∀ i ∈ s, Gauge.GC.Intw P Bs e (X i) (X' i)) :
    Gauge.GC.Intw P Bs e (∑ i ∈ s, X i) (∑ i ∈ s, X' i) := by
  classical
  revert h
  refine Finset.induction_on s (fun _ => ?_) (fun a t hat ih h => ?_)
  · rw [Finset.sum_empty, Finset.sum_empty]
    exact intw_zero hsm
  · rw [Finset.sum_insert hat, Finset.sum_insert hat]
    exact intw_add' hsm (h a (Finset.mem_insert_self a t)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/- English proof (translation)
Use `split_ifs with hc`. Conclude with `h hc`. Conclude with `intw_zero hsm`.
-/
theorem intw_ite' (c : Prop) [Decidable c] {X : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} {X' : MA.A P (MA.DQ P)}
    (h : c → Gauge.GC.Intw P Bs e X X') : Gauge.GC.Intw P Bs e (if c then X else 0) (if c then X' else 0) := by
  split_ifs with hc
  · exact h hc
  · exact intw_zero hsm

end intw

/- English proof (translation)
Introduce `Φ`. Rewrite using `[Gauge.actA_mul, ← hY Φ, ← hX]`. Apply the tactic sequence `all_goals rfl`.
-/
private theorem intw_mul' {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}
    {Bs : B.RealPlaceData P.k P.r Wp Wq} {e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)}
    {X Y : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} {X' Y' : MA.A P (MA.DQ P)}
    (hX : Gauge.GC.Intw P Bs e X X') (hY : Gauge.GC.Intw P Bs e Y Y') :
    Gauge.GC.Intw P Bs e (X * Y) (X' * Y') := by
  intro Φ
  rw [Gauge.actA_mul, ← hY Φ, ← hX]
  all_goals rfl

/- English proof (translation)
Use `show κ' f * κ' g = κ' g * κ' f`. Rewrite using `[← map_mul, mul_comm, map_mul]`.
-/
private theorem commute_algHom_of_functions {T A' : Type} [Ring A'] [Algebra ℂ A'] (κ' : (T → ℂ) →ₐ[ℂ] A') (f g : T → ℂ) :
    Commute (κ' f) (κ' g) := by
  show κ' f * κ' g = κ' g * κ' f
  rw [← map_mul, mul_comm, map_mul]

/- English proof (translation)
Introduce `l f g hfg`. Establish `h` using `hR l (fun ρ => star (f ρ)) (fun ρ => star (g ρ)) (fun ρ ρ' hU => by show star (g ρ') = star (f ρ); rw [hfg ρ ρ' hU])`. Establish `h2` using `congrArg star h`. Rewrite `h2` using `[star_mul, star_mul, hst, hst]`. Simplify using `using h2`.
-/
private theorem raiS_star_of_rai_of_star_comm {P : M.Par} {A' : Type} [Ring A'] [StarRing A'] [Algebra ℂ A']
    (κ' : (M.Ty P → ℂ) →ₐ[ℂ] A') (S' : ℕ → A') (hR : Rai κ' S')
    (hst : ∀ f, star (κ' f) = κ' (fun ρ => star (f ρ))) : RaiS κ' (fun l => star (S' l)) := by
  intro l f g hfg
  have h := hR l (fun ρ => star (f ρ)) (fun ρ => star (g ρ))
    (fun ρ ρ' hU => by show star (g ρ') = star (f ρ); rw [hfg ρ ρ' hU])
  have h2 := congrArg star h
  rw [star_mul, star_mul, hst, hst] at h2
  simpa using h2

/- English proof (translation)
Establish `hk : MA.kap P (MA.DQ P) f = Matrix.diagonal fun π => algebraMap ℂ (MA.DQ P).Pr (f π)` using `by first`. Consider the case `rfl`. Consider the case `(ext i j; simp [MA.kap, Matrix.diagonal_apply])`. Rewrite using `[hk]`. Use `show Matrix.diagonal _ * Matrix.diagonal v = Matrix.diagonal v * Matrix.diagonal _`.

Rewrite using `[Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `π`. Conclude with `Algebra.commutes _ _`.
-/
private theorem commute_kap_diagonal {P : M.Par} (f : M.Ty P → ℂ) (v : M.Ty P → (MA.DQ P).Pr) :
    Commute (MA.kap P (MA.DQ P) f) (Matrix.diagonal v) := by
  have hk : MA.kap P (MA.DQ P) f = Matrix.diagonal fun π => algebraMap ℂ (MA.DQ P).Pr (f π) := by
    first
    | rfl
    | (ext i j; simp [MA.kap, Matrix.diagonal_apply])
  rw [hk]
  show Matrix.diagonal _ * Matrix.diagonal v = Matrix.diagonal v * Matrix.diagonal _
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext π
  exact Algebra.commutes _ _

/- English proof (translation)
Introduce `l f g hfg`. Establish `hk : ∀ h : M.Ty P → ℂ, MA.kap P (MA.DQ P) h = Matrix.diagonal fun π => algebraMap ℂ (MA.DQ P).Pr (h π)`. Introduce `h`. Use `first`. Consider the case `rfl`.

Consider the case `(ext i j; simp [MA.kap, Matrix.diagonal_apply])`. Rewrite using `[hk, hk]`. Use extensionality with `π' π`. Rewrite using `[Matrix.diagonal_mul, Matrix.mul_diagonal]`. Simplify using `only [MA.SS, Matrix.of_apply]`.

Use `split_ifs with hU`. Rewrite using `[hfg π π' hU, Algebra.commutes]`. Simplify using the standard rewrite rules.
-/
private theorem rai_kap_SS_DQ {P : M.Par} : Rai (MA.kap P (MA.DQ P)) (MA.SS P (MA.DQ P)) := by
  intro l f g hfg
  have hk : ∀ h : M.Ty P → ℂ,
      MA.kap P (MA.DQ P) h = Matrix.diagonal fun π => algebraMap ℂ (MA.DQ P).Pr (h π) := by
    intro h
    first
    | rfl
    | (ext i j; simp [MA.kap, Matrix.diagonal_apply])
  rw [hk, hk]
  ext π' π
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  simp only [MA.SS, Matrix.of_apply]
  split_ifs with hU
  · rw [hfg π π' hU, Algebra.commutes]
  · simp

/- English proof (translation)
Introduce `Wp Wq _ _ _ _ _ _ P Bs hk X d hAct e hF hQQ hκ l hl`. Take `⟨hPl, -, -, hRel, -⟩` from `hAct`. Establish `hP : P.OK` using `hPl.1`. Establish `hsm` using `Gauge.GC.radial_space_smoothness Wp Wq P Bs hPl hk e hF`. Establish `hpj : ∀ ρ : M.Ty P, Gauge.GC.Intw P Bs e (pj d.κ ρ) (pj (MA.kap P (MA.DQ P)) ρ)` using `fun ρ => hκ _`.

Establish `hfn : ∀ f (g : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')), g ∈ d.L.fns ∪ {d.L.nab, d.L.nabs} → Commute (d.κ f) g` using `fun f g hg => hRel.2.1 f g hg`. Establish `hdB : ∀ (Y : ℂ) f, Commute (d.κ f) (d.L.GG * d.x Y * d.L.l0 Y)`. Introduce `Y f`. Establish `hl0 : Commute (d.κ f) (d.L.l0 Y)` using `by show Commute (d.κ f) (-d.L.nab - algebraMap ℂ _ (Y + 1 / 2) * (d.L.ζb * d.L.GGi))`. Conclude with `(hfn f d.L.nab (by simp)).neg_right.sub_right ((Algebra.commute_algebraMap_right _ _).mul_right ((hfn f d.L.ζb (by simp [R.LevelData.fns])).mul_right (hfn f d.L.GGi (by simp [R.LevelData.fns]))))`.

Conclude with `((hfn f d.L.GG (by simp [R.LevelData.fns])).mul_right (commute_algHom_of_functions d.κ f (fun ρ => M.xC P ρ Y))).mul_right hl0`. Establish `hdB' : ∀ (Y : ℂ) f, Commute (d.κ f) (d.L.GG * d.x Y * d.L.m0 Y)`. Introduce `Y f`. Establish `hm0 : Commute (d.κ f) (d.L.m0 Y)` using `by show Commute (d.κ f) (-d.L.nabs - algebraMap ℂ _ (Y - 1 / 2) * (d.L.ζ * d.L.GGi))`. Conclude with `(hfn f d.L.nabs (by simp)).neg_right.sub_right ((Algebra.commute_algebraMap_right _ _).mul_right ((hfn f d.L.ζ (by simp [R.LevelData.fns])).mul_right (hfn f d.L.GGi (by simp [R.LevelData.fns]))))`.

Conclude with `((hfn f d.L.GG (by simp [R.LevelData.fns])).mul_right (commute_algHom_of_functions d.κ f (fun ρ => M.xC P ρ Y))).mul_right hm0`. Establish `hmB : ∀ (Y : ℂ) f, Commute (MA.kap P (MA.DQ P) f) (MA.ggA P (MA.DQ P) * MA.xA P (MA.DQ P) Y * MA.l0A P (MA.DQ P) Y)`. Introduce `Y f`. Establish `hl0 : Commute (MA.kap P (MA.DQ P) f) (MA.l0A P (MA.DQ P) Y)` using `by show Commute _ (-MA.nabA P (MA.DQ P) - algebraMap ℂ _ (Y + 1 / 2) * (MA.zbA P (MA.DQ P) * MA.ggiA P (MA.DQ P)))`. Conclude with `(commute_kap_diagonal f _).neg_right.sub_right ((Algebra.commute_algebraMap_right _ _).mul_right ((commute_kap_diagonal f _).mul_right (commute_kap_diagonal f _)))`.

Conclude with `((commute_kap_diagonal f _).mul_right (commute_algHom_of_functions (MA.kap P (MA.DQ P)) f (fun π => M.xC P π Y))).mul_right hl0`. Establish `hmB' : ∀ (Y : ℂ) f, Commute (MA.kap P (MA.DQ P) f) (MA.ggA P (MA.DQ P) * MA.xA P (MA.DQ P) Y * MA.m0A P (MA.DQ P) Y)`. Introduce `Y f`. Establish `hm0 : Commute (MA.kap P (MA.DQ P) f) (MA.m0A P (MA.DQ P) Y)` using `by show Commute _ (-MA.nabsA P (MA.DQ P) - algebraMap ℂ _ (Y - 1 / 2) * (MA.zA P (MA.DQ P) * MA.ggiA P (MA.DQ P)))`. Conclude with `(commute_kap_diagonal f _).neg_right.sub_right ((Algebra.commute_algebraMap_right _ _).mul_right ((commute_kap_diagonal f _).mul_right (commute_kap_diagonal f _)))`.

Conclude with `((commute_kap_diagonal f _).mul_right (commute_algHom_of_functions (MA.kap P (MA.DQ P)) f (fun π => M.xC P π Y))).mul_right hm0`. Establish `hRm : Rai (MA.kap P (MA.DQ P)) (MA.SS P (MA.DQ P))` using `rai_kap_SS_DQ`. Establish `hRSm : RaiS (MA.kap P (MA.DQ P)) (fun l => star (MA.SS P (MA.DQ P) l))` using `by first`. Consider the case `exact fun l f g h => Formalism.FourierDecayAlt.P.MAx1.ModelAlgebraRelations.Ss_shift (P := P) (D := MA.DQ P) l f g h`. Consider the case `exact fun l f g h => Formalism.FourierDecayAlt.P.MAx1.ModelAlgebraRelations.Ss_shift P (MA.DQ P) l f g h`.

Consider the case `exact fun l f g h => Formalism.FourierDecayAlt.P.MAx1.ModelAlgebraRelations.Ss_shift P l f g h`. Consider the case `exact raiS_star_of_rai_of_star_comm _ _ hRm (fun f => Formalism.FourierDecayAlt.P.MAx1.D5.star_kap (P := P) (D := MA.DQ P) f)`. Consider the case `exact raiS_star_of_rai_of_star_comm _ _ hRm (fun f => Formalism.FourierDecayAlt.P.MAx1.D5.star_kap P (MA.DQ P) f)`. Consider the case `exact raiS_star_of_rai_of_star_comm _ _ hRm (fun f => by`. Establish `hk : ∀ h : M.Ty P → ℂ, MA.kap P (MA.DQ P) h = Matrix.diagonal fun π => algebraMap ℂ (MA.DQ P).Pr (h π)` using `fun h => rfl`.

Rewrite using `[hk, hk, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]`. Use `congr 1`. Use function extensionality and compare the values at `π`. Use `first`. Consider the case `(rw [starRingEnd_apply, algebraMap_star_comm])`.

Consider the case `exact (algebraMap_star_comm (f π)).symm`. Consider the case `simp [Algebra.algebraMap_eq_smul_one, star_smul]`. Consider the case `(simp only [Algebra.algebraMap_eq_smul_one, star_smul, star_one]; rfl))`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `e1` using `ss_expand d.κ d.SS hRel.2.2.2.1 hP (fun Y => d.QQ Y 1 0) (fun Y => d.L.GG * d.x Y * d.L.l0 Y) hdB (fun Y => rfl) hl`.

Establish `e2` using `ss_expand (MA.kap P (MA.DQ P)) (MA.SS P (MA.DQ P)) hRm hP (fun Y => MA.QQr P (MA.DQ P) Y 1 0) (fun Y => MA.ggA P (MA.DQ P) * MA.xA P (MA.DQ P) Y * MA.l0A P (MA.DQ P) Y) hmB (fun Y => rfl) hl`. Rewrite using `[e1, e2]`. Use `intw_sum' hsm _ _ _ fun a _ => intw_sum' hsm _ _ _ fun b _ => intw_ite' hsm _ fun _ => intw_smul' hsm _ ?_` and prove the remaining obligations. Conclude with `intw_mul' (intw_mul' (hpj a) (hQQ (yl l b) 1 0)) (hpj b)`. Establish `e3` using `ssS_expand d.κ (fun l => star (d.SS l)) (raiS_star_of_rai_of_star_comm d.κ d.SS hRel.2.2.2.1 hRel.1) hP (fun Y => d.QQ Y 0 1) (fun Y => d.L.GG * d.x Y * d.L.m0 Y) hdB' (fun Y => rfl) hl`.

Establish `e4` using `ssS_expand (MA.kap P (MA.DQ P)) (fun l => star (MA.SS P (MA.DQ P) l)) hRSm hP (fun Y => MA.QQr P (MA.DQ P) Y 0 1) (fun Y => MA.ggA P (MA.DQ P) * MA.xA P (MA.DQ P) Y * MA.m0A P (MA.DQ P) Y) hmB' (fun Y => rfl) hl`. Rewrite using `[show star (d.SS l) = _ from e3, show star (MA.SS P (MA.DQ P) l) = _ from e4]`. Use `intw_sum' hsm _ _ _ fun a _ => intw_sum' hsm _ _ _ fun b _ => intw_ite' hsm _ fun _ => intw_smul' hsm _ ?_` and prove the remaining obligations. Conclude with `intw_mul' (intw_mul' (hpj a) (hQQ (yl l a) 0 1)) (hpj b)`.
-/
theorem quadratic_shift_identity : GQSS := by
  intro Wp Wq _ _ _ _ _ _ P Bs hk X d hAct e hF hQQ hκ l hl
  obtain ⟨hPl, -, -, hRel, -⟩ := hAct
  have hP : P.OK := hPl.1
  have hsm := Gauge.GC.radial_space_smoothness Wp Wq P Bs hPl hk e hF
  have hpj : ∀ ρ : M.Ty P, Gauge.GC.Intw P Bs e (pj d.κ ρ) (pj (MA.kap P (MA.DQ P)) ρ) :=
    fun ρ => hκ _
  have hfn : ∀ f (g : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')),
      g ∈ d.L.fns ∪ {d.L.nab, d.L.nabs} → Commute (d.κ f) g :=
    fun f g hg => hRel.2.1 f g hg
  have hdB : ∀ (Y : ℂ) f, Commute (d.κ f) (d.L.GG * d.x Y * d.L.l0 Y) := by
    intro Y f
    have hl0 : Commute (d.κ f) (d.L.l0 Y) := by
      show Commute (d.κ f) (-d.L.nab - algebraMap ℂ _ (Y + 1 / 2) * (d.L.ζb * d.L.GGi))
      exact (hfn f d.L.nab (by simp)).neg_right.sub_right ((Algebra.commute_algebraMap_right _ _).mul_right
        ((hfn f d.L.ζb (by simp [R.LevelData.fns])).mul_right (hfn f d.L.GGi (by simp [R.LevelData.fns]))))
    exact ((hfn f d.L.GG (by simp [R.LevelData.fns])).mul_right
      (commute_algHom_of_functions d.κ f (fun ρ => M.xC P ρ Y))).mul_right hl0
  have hdB' : ∀ (Y : ℂ) f, Commute (d.κ f) (d.L.GG * d.x Y * d.L.m0 Y) := by
    intro Y f
    have hm0 : Commute (d.κ f) (d.L.m0 Y) := by
      show Commute (d.κ f) (-d.L.nabs - algebraMap ℂ _ (Y - 1 / 2) * (d.L.ζ * d.L.GGi))
      exact (hfn f d.L.nabs (by simp)).neg_right.sub_right ((Algebra.commute_algebraMap_right _ _).mul_right
        ((hfn f d.L.ζ (by simp [R.LevelData.fns])).mul_right (hfn f d.L.GGi (by simp [R.LevelData.fns]))))
    exact ((hfn f d.L.GG (by simp [R.LevelData.fns])).mul_right
      (commute_algHom_of_functions d.κ f (fun ρ => M.xC P ρ Y))).mul_right hm0
  have hmB : ∀ (Y : ℂ) f, Commute (MA.kap P (MA.DQ P) f)
      (MA.ggA P (MA.DQ P) * MA.xA P (MA.DQ P) Y * MA.l0A P (MA.DQ P) Y) := by
    intro Y f
    have hl0 : Commute (MA.kap P (MA.DQ P) f) (MA.l0A P (MA.DQ P) Y) := by
      show Commute _ (-MA.nabA P (MA.DQ P) - algebraMap ℂ _ (Y + 1 / 2) * (MA.zbA P (MA.DQ P) * MA.ggiA P (MA.DQ P)))
      exact (commute_kap_diagonal f _).neg_right.sub_right
        ((Algebra.commute_algebraMap_right _ _).mul_right
          ((commute_kap_diagonal f _).mul_right
            (commute_kap_diagonal f _)))
    exact ((commute_kap_diagonal f _).mul_right
      (commute_algHom_of_functions (MA.kap P (MA.DQ P)) f (fun π => M.xC P π Y))).mul_right hl0
  have hmB' : ∀ (Y : ℂ) f, Commute (MA.kap P (MA.DQ P) f)
      (MA.ggA P (MA.DQ P) * MA.xA P (MA.DQ P) Y * MA.m0A P (MA.DQ P) Y) := by
    intro Y f
    have hm0 : Commute (MA.kap P (MA.DQ P) f) (MA.m0A P (MA.DQ P) Y) := by
      show Commute _ (-MA.nabsA P (MA.DQ P) - algebraMap ℂ _ (Y - 1 / 2) * (MA.zA P (MA.DQ P) * MA.ggiA P (MA.DQ P)))
      exact (commute_kap_diagonal f _).neg_right.sub_right
        ((Algebra.commute_algebraMap_right _ _).mul_right
          ((commute_kap_diagonal f _).mul_right
            (commute_kap_diagonal f _)))
    exact ((commute_kap_diagonal f _).mul_right
      (commute_algHom_of_functions (MA.kap P (MA.DQ P)) f (fun π => M.xC P π Y))).mul_right hm0
  have hRm : Rai (MA.kap P (MA.DQ P)) (MA.SS P (MA.DQ P)) := rai_kap_SS_DQ
  have hRSm : RaiS (MA.kap P (MA.DQ P)) (fun l => star (MA.SS P (MA.DQ P) l)) := by
    first
    | exact fun l f g h => Formalism.FourierDecayAlt.P.MAx1.ModelAlgebraRelations.Ss_shift (P := P) (D := MA.DQ P) l f g h
    | exact fun l f g h => Formalism.FourierDecayAlt.P.MAx1.ModelAlgebraRelations.Ss_shift P (MA.DQ P) l f g h
    | exact fun l f g h => Formalism.FourierDecayAlt.P.MAx1.ModelAlgebraRelations.Ss_shift P l f g h
    | exact raiS_star_of_rai_of_star_comm _ _ hRm (fun f => Formalism.FourierDecayAlt.P.MAx1.D5.star_kap (P := P) (D := MA.DQ P) f)
    | exact raiS_star_of_rai_of_star_comm _ _ hRm (fun f => Formalism.FourierDecayAlt.P.MAx1.D5.star_kap P (MA.DQ P) f)
    | exact raiS_star_of_rai_of_star_comm _ _ hRm (fun f => by
        have hk : ∀ h : M.Ty P → ℂ,
            MA.kap P (MA.DQ P) h = Matrix.diagonal fun π => algebraMap ℂ (MA.DQ P).Pr (h π) := fun h => rfl
        rw [hk, hk, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
        congr 1
        funext π
        first
        | (rw [starRingEnd_apply, algebraMap_star_comm])
        | exact (algebraMap_star_comm (f π)).symm
        | simp [Algebra.algebraMap_eq_smul_one, star_smul]
        | (simp only [Algebra.algebraMap_eq_smul_one, star_smul, star_one]; rfl))
  refine ⟨?_, ?_⟩
  · have e1 := ss_expand d.κ d.SS hRel.2.2.2.1 hP (fun Y => d.QQ Y 1 0)
      (fun Y => d.L.GG * d.x Y * d.L.l0 Y) hdB (fun Y => rfl) hl
    have e2 := ss_expand (MA.kap P (MA.DQ P)) (MA.SS P (MA.DQ P)) hRm hP (fun Y => MA.QQr P (MA.DQ P) Y 1 0)
      (fun Y => MA.ggA P (MA.DQ P) * MA.xA P (MA.DQ P) Y * MA.l0A P (MA.DQ P) Y) hmB (fun Y => rfl) hl
    rw [e1, e2]
    refine intw_sum' hsm _ _ _ fun a _ => intw_sum' hsm _ _ _ fun b _ =>
      intw_ite' hsm _ fun _ => intw_smul' hsm _ ?_
    exact intw_mul' (intw_mul' (hpj a) (hQQ (yl l b) 1 0)) (hpj b)
  · have e3 := ssS_expand d.κ (fun l => star (d.SS l)) (raiS_star_of_rai_of_star_comm d.κ d.SS hRel.2.2.2.1 hRel.1) hP
      (fun Y => d.QQ Y 0 1) (fun Y => d.L.GG * d.x Y * d.L.m0 Y) hdB' (fun Y => rfl) hl
    have e4 := ssS_expand (MA.kap P (MA.DQ P)) (fun l => star (MA.SS P (MA.DQ P) l))
      hRSm hP
      (fun Y => MA.QQr P (MA.DQ P) Y 0 1)
      (fun Y => MA.ggA P (MA.DQ P) * MA.xA P (MA.DQ P) Y * MA.m0A P (MA.DQ P) Y) hmB' (fun Y => rfl) hl
    rw [show star (d.SS l) = _ from e3, show star (MA.SS P (MA.DQ P) l) = _ from e4]
    refine intw_sum' hsm _ _ _ fun a _ => intw_sum' hsm _ _ _ fun b _ =>
      intw_ite' hsm _ fun _ => intw_smul' hsm _ ?_
    exact intw_mul' (intw_mul' (hpj a) (hQQ (yl l a) 0 1)) (hpj b)

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.GQ
