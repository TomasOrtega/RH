import Mathlib
import GroundTheory.PAdicHodge.RobbaSeries
import GroundTheory.PAdicHodge.HighIndexSingleZeroOne
import GroundTheory.PAdicHodge.RobbaBounded
import GroundTheory.PAdicHodge.RobbaNewton
import GroundTheory.PAdicHodge.RobbaClosed
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Filter Topology Laurent

set_option linter.unusedSectionVars false

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace Laurent

variable {a : ℤ → K}

/- English proof (translation)
Establish `hρ : 0 < ρ` using `h1.trans_le hle1`. Rewrite using `[← mul_max_of_nonneg _ _ (norm_nonneg x)]`. Use `mul_le_mul_of_nonneg_left ?_ (norm_nonneg x)` and prove the remaining obligations. Break down `le_total 0 n with hn | hn` into its components or cases. Conclude with `le_max_of_le_right (zpow_le_zpow_left₀ hn hρ.le hle2)`.

Use `le_max_of_le_left ?_` and prove the remaining obligations. Rewrite using `[show ρ ^ n = (ρ ^ (-n))⁻¹ by rw [zpow_neg, inv_inv], show ρ₁ ^ n = (ρ₁ ^ (-n))⁻¹ by rw [zpow_neg, inv_inv]]`. Conclude with `inv_anti₀ (by positivity) (zpow_le_zpow_left₀ (neg_nonneg.2 hn) h1.le hle1)`.
-/
theorem weight_le_max {ρ₁ ρ ρ₂ : ℝ} (h1 : 0 < ρ₁) (hle1 : ρ₁ ≤ ρ) (hle2 : ρ ≤ ρ₂) (x : K) (n : ℤ) :
    ‖x‖ * ρ ^ n ≤ max (‖x‖ * ρ₁ ^ n) (‖x‖ * ρ₂ ^ n) := by
  have hρ : 0 < ρ := h1.trans_le hle1
  rw [← mul_max_of_nonneg _ _ (norm_nonneg x)]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg x)
  rcases le_total 0 n with hn | hn
  · exact le_max_of_le_right (zpow_le_zpow_left₀ hn hρ.le hle2)
  · refine le_max_of_le_left ?_
    rw [show ρ ^ n = (ρ ^ (-n))⁻¹ by rw [zpow_neg, inv_inv],
      show ρ₁ ^ n = (ρ₁ ^ (-n))⁻¹ by rw [zpow_neg, inv_inv]]
    exact inv_anti₀ (by positivity) (zpow_le_zpow_left₀ (neg_nonneg.2 hn) h1.le hle1)

/- English proof (translation)
Establish `hF` using `(h1.finite_le hε).union (h2.finite_le hε)`. Take `⟨B, hB⟩` from `(hF.image (fun n : ℤ => |n|)).bddAbove`. Use `⟨B.toNat, fun n hn => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hcon`. Rewrite `hcon` using `[not_and_or, not_le, not_le]`.

Establish `hmem : n ∈ {n | ε ≤ ‖a n‖ * ρ₁ ^ n} ∪ {n | ε ≤ ‖a n‖ * ρ₂ ^ n}`. Break down `hcon with h | h` into its components or cases. Conclude with `Or.inl h.le`. Conclude with `Or.inr h.le`. Establish `h3 : |n| ≤ B` using `hB ⟨n, hmem, rfl⟩`.

Establish `h4` using `Int.self_le_toNat B`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_tail_le {ρ₁ ρ₂ : ℝ} (h1 : ConvergesAt a ρ₁) (h2 : ConvergesAt a ρ₂) {ε : ℝ}
    (hε : 0 < ε) : ∃ M : ℕ, ∀ n : ℤ, (M : ℤ) < |n| → ‖a n‖ * ρ₁ ^ n ≤ ε ∧ ‖a n‖ * ρ₂ ^ n ≤ ε := by
  have hF := (h1.finite_le hε).union (h2.finite_le hε)
  obtain ⟨B, hB⟩ := (hF.image (fun n : ℤ => |n|)).bddAbove
  refine ⟨B.toNat, fun n hn => ?_⟩
  by_contra hcon
  rw [not_and_or, not_le, not_le] at hcon
  have hmem : n ∈ {n | ε ≤ ‖a n‖ * ρ₁ ^ n} ∪ {n | ε ≤ ‖a n‖ * ρ₂ ^ n} := by
    rcases hcon with h | h
    · exact Or.inl h.le
    · exact Or.inr h.le
  have h3 : |n| ≤ B := hB ⟨n, hmem, rfl⟩
  have h4 := Int.self_le_toNat B
  linarith

/- English proof (translation)
The claim follows from `gaussNorm_le fun n => by by_cases hn : (M : ℤ) < |n| · have hnot : n ∉ Set.Icc (-(M : ℤ)) M := fun hm => by simp only [Set.mem_Icc] at hm; rcases lt_abs.1 hn with h' | h' <;> omega simp only [Pi.sub_apply, trunc, Set.indicator_of_notMem hnot, sub_zero] exact h n hn · have hm : n …`.
-/
theorem gaussNorm_tail_le {ρ : ℝ} (hρ : 0 < ρ) {M : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ n : ℤ, (M : ℤ) < |n| → ‖a n‖ * ρ ^ n ≤ ε) :
    gaussNorm (a - trunc a (Set.Icc (-(M : ℤ)) M)) ρ ≤ ε :=
  gaussNorm_le fun n => by
    by_cases hn : (M : ℤ) < |n|
    · have hnot : n ∉ Set.Icc (-(M : ℤ)) M := fun hm => by
        simp only [Set.mem_Icc] at hm; rcases lt_abs.1 hn with h' | h' <;> omega
      simp only [Pi.sub_apply, trunc, Set.indicator_of_notMem hnot, sub_zero]
      exact h n hn
    · have hm : n ∈ Set.Icc (-(M : ℤ)) M := by
        simp only [Set.mem_Icc]; rw [not_lt, abs_le] at hn; exact hn
      simp [trunc, Set.indicator_of_mem hm, hε]

/- English proof (translation)
Use `tendsto_const_nhds.congr' ?_` and prove the remaining obligations. Use `filter_upwards [(Set.finite_Icc (-(M : ℤ)) M).compl_mem_cofinite] with n hn`. Simplify using `[trunc, Set.indicator_of_notMem hn]`.
-/
theorem convergesAt_trunc_Icc (a : ℤ → K) (M : ℕ) (ρ : ℝ) :
    ConvergesAt (trunc a (Set.Icc (-(M : ℤ)) M)) ρ := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [(Set.finite_Icc (-(M : ℤ)) M).compl_mem_cofinite] with n hn
  simp [trunc, Set.indicator_of_notMem hn]

end Laurent

namespace Laurent

section MittagLeffler

open Classical in

def tailM (c : ℤ → K) (ρ₁ ρ₂ ε : ℝ) : ℕ :=
  if h : ∃ M : ℕ, ∀ n : ℤ, (M : ℤ) < |n| → ‖c n‖ * ρ₁ ^ n ≤ ε ∧ ‖c n‖ * ρ₂ ^ n ≤ ε
  then h.choose else 0

/- English proof (translation)
Establish `h` using `exists_tail_le h1 h2 hε`. Unfold `tailM`. Rewrite using `[dif_pos h]`. Conclude with `h.choose_spec`.
-/
theorem tailM_spec {c : ℤ → K} {ρ₁ ρ₂ ε : ℝ} (h1 : ConvergesAt c ρ₁) (h2 : ConvergesAt c ρ₂)
    (hε : 0 < ε) : ∀ n : ℤ, (tailM c ρ₁ ρ₂ ε : ℤ) < |n| →
      ‖c n‖ * ρ₁ ^ n ≤ ε ∧ ‖c n‖ * ρ₂ ^ n ≤ ε := by
  have h := exists_tail_le h1 h2 hε
  unfold tailM
  rw [dif_pos h]
  exact h.choose_spec

/- English proof (translation)
Set `eA : AnnulusRing K I` to `⟨A, hA⟩`. Set `eB : AnnulusRing K I` to `⟨B, hB⟩`. Set `ea : AnnulusRing K I` to `⟨a, ha⟩`. Set `eb : AnnulusRing K I` to `⟨b, hb⟩`. Set `ef : AnnulusRing K I` to `⟨f, hf⟩`.

Set `eg : AnnulusRing K I` to `⟨g, hg⟩`. Set `ec : AnnulusRing K I` to `⟨c, hc⟩`. Set `ec' : AnnulusRing K I` to `⟨c', hc'⟩`. Establish `k1 : eA * ef + eB * eg = 1` using `AnnulusRing.ext h1`. Establish `k2 : ea * ef + eb * eg = 1` using `AnnulusRing.ext h2`.

Establish `kc : ec = eB * (ea - eA) - eA * (eb - eB)` using `AnnulusRing.ext hcdef`. Establish `r1 : (ea - ec' * eg) - eA = (ec - ec') * eg`. Take the linear combination `eA * k2 - ea * k1 - eg * kc`. Establish `r2 : (eb + ec' * ef) - eB = -((ec - ec') * ef)`. Take the linear combination `eB * k2 - eb * k1 + ef * kc`.

Conclude with `⟨congrArg AnnulusRing.coeff r1, congrArg AnnulusRing.coeff r2⟩`.
-/
theorem ring_identities {I : Set ℝ} [Fact (∃ ρ ∈ I, 0 < ρ)] {A B a b f g c c' : ℤ → K}
    (hA : ∀ ρ ∈ I, 0 < ρ → ConvergesAt A ρ) (hB : ∀ ρ ∈ I, 0 < ρ → ConvergesAt B ρ)
    (ha : ∀ ρ ∈ I, 0 < ρ → ConvergesAt a ρ) (hb : ∀ ρ ∈ I, 0 < ρ → ConvergesAt b ρ)
    (hf : ∀ ρ ∈ I, 0 < ρ → ConvergesAt f ρ) (hg : ∀ ρ ∈ I, 0 < ρ → ConvergesAt g ρ)
    (hc : ∀ ρ ∈ I, 0 < ρ → ConvergesAt c ρ) (hc' : ∀ ρ ∈ I, 0 < ρ → ConvergesAt c' ρ)
    (h1 : cmul A f + cmul B g = Pi.single 0 1) (h2 : cmul a f + cmul b g = Pi.single 0 1)
    (hcdef : c = cmul B (a - A) - cmul A (b - B)) :
    (a - cmul c' g) - A = cmul (c - c') g ∧ (b + cmul c' f) - B = -cmul (c - c') f := by
  let eA : AnnulusRing K I := ⟨A, hA⟩
  let eB : AnnulusRing K I := ⟨B, hB⟩
  let ea : AnnulusRing K I := ⟨a, ha⟩
  let eb : AnnulusRing K I := ⟨b, hb⟩
  let ef : AnnulusRing K I := ⟨f, hf⟩
  let eg : AnnulusRing K I := ⟨g, hg⟩
  let ec : AnnulusRing K I := ⟨c, hc⟩
  let ec' : AnnulusRing K I := ⟨c', hc'⟩
  have k1 : eA * ef + eB * eg = 1 := AnnulusRing.ext h1
  have k2 : ea * ef + eb * eg = 1 := AnnulusRing.ext h2
  have kc : ec = eB * (ea - eA) - eA * (eb - eB) := AnnulusRing.ext hcdef
  have r1 : (ea - ec' * eg) - eA = (ec - ec') * eg := by
    linear_combination eA * k2 - ea * k1 - eg * kc
  have r2 : (eb + ec' * ef) - eB = -((ec - ec') * ef) := by
    linear_combination eB * k2 - eb * k1 + ef * kc
  exact ⟨congrArg AnnulusRing.coeff r1, congrArg AnnulusRing.coeff r2⟩

/- English proof (translation)
Use `tendsto_order.2 ⟨fun e he => Eventually.of_forall fun n => lt_of_lt_of_le he (by positivity), fun ε hε => ?_⟩` and prove the remaining obligations. Take `⟨K₀, hK⟩` from `h.weight_sub_le hρ (half_pos hε)`. Establish `hev` using `(hx (max K₀ K₁) (le_max_right _ _)).eventually (gt_mem_nhds (half_pos hε))`. Use `filter_upwards [hev] with n hn`. Establish `e : limSeq x n = (limSeq x n - x (max K₀ K₁) n) + x (max K₀ K₁) n` using `by ring`.

Rewrite using `[e]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← max_mul_of_nonneg _ _ (by positivity)]`. Conclude with `mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_add_le_max _ _) (by positivity)`. Use `_ < ε := max_lt ((hK _ (le_max_left _ _) n).trans_lt (half_lt_self hε)) (hn.trans (half_lt_self hε))`.
-/
theorem UCauchy.convergesAt_of_eventually {x : ℕ → ℤ → K} {ρ : ℝ} (hρ : 0 < ρ)
    (h : UCauchy x ρ) {K₁ : ℕ} (hx : ∀ k ≥ K₁, ConvergesAt (x k) ρ) :
    ConvergesAt (limSeq x) ρ := by
  refine tendsto_order.2 ⟨fun e he => Eventually.of_forall fun n => lt_of_lt_of_le he
    (by positivity), fun ε hε => ?_⟩
  obtain ⟨K₀, hK⟩ := h.weight_sub_le hρ (half_pos hε)
  have hev := (hx (max K₀ K₁) (le_max_right _ _)).eventually (gt_mem_nhds (half_pos hε))
  filter_upwards [hev] with n hn
  have e : limSeq x n = (limSeq x n - x (max K₀ K₁) n) + x (max K₀ K₁) n := by ring
  rw [e]
  calc ‖(limSeq x n - x (max K₀ K₁) n) + x (max K₀ K₁) n‖ * ρ ^ n
      ≤ max (‖limSeq x n - x (max K₀ K₁) n‖ * ρ ^ n) (‖x (max K₀ K₁) n‖ * ρ ^ n) := by
        rw [← max_mul_of_nonneg _ _ (by positivity)]
        exact mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_add_le_max _ _) (by positivity)
    _ < ε := max_lt ((hK _ (le_max_left _ _) n).trans_lt (half_lt_self hε))
        (hn.trans (half_lt_self hε))

variable {r : ℝ} {s : ℕ → ℝ} {f g : ℤ → K}

/- English proof (translation)
Use `choose a₀ b₀ hab₀ hid₀ using hloc`. Establish `hrs : ∀ k, r ≤ s k` using `fun k => hs0.trans (hmono (Nat.zero_le k))`. Establish `pos : ∀ ρ, r ≤ ρ → 0 < ρ` using `fun ρ h => hr.trans_le h`. Establish `fconv : ∀ k ρ, r ≤ ρ → ρ ≤ s k → ConvergesAt f ρ` using `fun k ρ h1 h2 => hf ρ h1 (h2.trans_lt (hs1 k))`. Establish `gconv : ∀ k ρ, r ≤ ρ → ρ ≤ s k → ConvergesAt g ρ` using `fun k ρ h1 h2 => hg ρ h1 (h2.trans_lt (hs1 k))`.

Set `C : ℕ → ℝ` to `fun k => 1 + gaussNorm f r + gaussNorm f (s (k - 1)) + gaussNorm g r + gaussNorm g (s (k - 1))`. Establish `gf0 : ∀ k, 0 ≤ gaussNorm f (s k)` using `fun k => gaussNorm_nonneg (pos _ (hrs k))`. Establish `gg0 : ∀ k, 0 ≤ gaussNorm g (s k)` using `fun k => gaussNorm_nonneg (pos _ (hrs k))`. Establish `gfr : 0 ≤ gaussNorm f r` using `gaussNorm_nonneg hr`. Establish `ggr : 0 ≤ gaussNorm g r` using `gaussNorm_nonneg hr`.

Establish `hC : ∀ k, 1 ≤ C k` using `fun k => by`. Use `gf0 (k - 1)` as an intermediate fact. Use `gg0 (k - 1)` as an intermediate fact. Simplify using `only [C]`. Combine the linear equalities and inequalities to obtain the conclusion.

Set `ε : ℕ → ℝ` to `fun k => (1 / 2) ^ k / C k`. Establish `hε : ∀ k, 0 < ε k` using `fun k => div_pos (by positivity) (by linarith [hC k])`. Set `step : ℕ → (ℤ → K) × (ℤ → K) → (ℤ → K) × (ℤ → K)` to `fun k AB =>`. Set `c` to `cmul AB.2 (a₀ (k + 1) - AB.1) - cmul AB.1 (b₀ (k + 1) - AB.2)`. Set `c'` to `trunc c (Set.Icc (-(tailM c r (s (k - 1)) (ε k) : ℤ)) (tailM c r (s (k - 1)) (ε k)))`.

Use the proof step `(a₀ (k + 1) - cmul c' g, b₀ (k + 1) + cmul c' f)`. Set `seq : ℕ → (ℤ → K) × (ℤ → K)` to `fun k => Nat.rec (a₀ 0, b₀ 0) step k`. Establish `seq_succ : ∀ k, seq (k + 1) = step k (seq k)` using `fun k => rfl`. Establish `inv : ∀ k, (∀ ρ, r ≤ ρ → ρ ≤ s k → ConvergesAt (seq k).1 ρ ∧ ConvergesAt (seq k).2 ρ) ∧ cmul (seq k).1 f + cmul (seq k).2 g = Pi.single 0 1`. Introduce `k`.

Proceed by induction on `k with`. Consider the case `zero => exact ⟨hab₀ 0, hid₀ 0⟩`. Consider the case `succ k ih`. Rewrite using `[seq_succ]`. Use `set c := cmul (seq k).2 (a₀ (k + 1) - (seq k).1) - cmul (seq k).1 (b₀ (k + 1) - (seq k).2)`.

Use `set M := tailM c r (s (k - 1)) (ε k)`. Establish `hc' : ∀ ρ, ConvergesAt (trunc c (Set.Icc (-(M : ℤ)) M)) ρ` using `fun ρ => convergesAt_trunc_Icc c M ρ`. Use `⟨fun ρ h1 h2 => ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Conclude with `((hab₀ (k + 1) ρ h1 h2).1).sub (pos ρ h1) ((hc' ρ).cmul (pos ρ h1) (gconv _ ρ h1 h2))`. Conclude with `((hab₀ (k + 1) ρ h1 h2).2).add (pos ρ h1) ((hc' ρ).cmul (pos ρ h1) (fconv _ ρ h1 h2))`.

Use `haveI : Fact (∃ ρ ∈ Set.Icc r (s (k + 1)), 0 < ρ) := ⟨⟨r, ⟨le_rfl, hrs _⟩, hr⟩⟩`. Set `I` to `Set.Icc r (s (k + 1))`. Establish `cv : ∀ x : ℤ → K, (∀ ρ, r ≤ ρ → ρ ≤ s (k + 1) → ConvergesAt x ρ) → ∀ ρ ∈ I, 0 < ρ → ConvergesAt x ρ` using `fun x hx ρ hρ _ => hx ρ hρ.1 hρ.2`. Set `ea : AnnulusRing K I` to `⟨a₀ (k + 1), cv _ fun ρ h1 h2 => (hab₀ _ ρ h1 h2).1⟩`. Set `eb : AnnulusRing K I` to `⟨b₀ (k + 1), cv _ fun ρ h1 h2 => (hab₀ _ ρ h1 h2).2⟩`.

Set `ef : AnnulusRing K I` to `⟨f, cv _ (fconv _)⟩`. Set `eg : AnnulusRing K I` to `⟨g, cv _ (gconv _)⟩`. Set `ec : AnnulusRing K I` to `⟨trunc c (Set.Icc (-(M : ℤ)) M), cv _ fun ρ _ _ => hc' ρ⟩`. Establish `k2 : ea * ef + eb * eg = 1` using `AnnulusRing.ext (hid₀ (k + 1))`. Establish `: (ea - ec * eg) * ef + (eb + ec * ef) * eg = 1` using `by linear_combination k2`.

Conclude with `congrArg AnnulusRing.coeff this`. Establish `small : ∀ k ρ, (ρ = r ∨ ρ = s (k - 1)) → gaussNorm ((seq (k + 1)).1 - (seq k).1) ρ ≤ (1 / 2) ^ k ∧ gaussNorm ((seq (k + 1)).2 - (seq k).2) ρ ≤ (1 / 2) ^ k`. Introduce `k ρ hρ`. Establish `hρr : r ≤ ρ` using `by rcases hρ with rfl | rfl; exacts [le_rfl, hrs _]`. Establish `hρk : ρ ≤ s k`.

Break down `hρ with rfl | rfl` into its components or cases. Use `exacts [hrs k, hmono (Nat.sub_le k 1)]`. Establish `hρ0` using `pos ρ hρr`. Rewrite using `[seq_succ]`. Use `set c := cmul (seq k).2 (a₀ (k + 1) - (seq k).1) - cmul (seq k).1 (b₀ (k + 1) - (seq k).2) with hcdef`.

Use `set M := tailM c r (s (k - 1)) (ε k)`. Use `set c' := trunc c (Set.Icc (-(M : ℤ)) M)`. Establish `hsk : s k ≤ s (k + 1)` using `hmono (Nat.le_succ k)`. Establish `cvk : ∀ ρ, r ≤ ρ → ρ ≤ s k → ConvergesAt c ρ` using `fun ρ h1 h2 => by`. Establish `h0` using `pos ρ h1`.

Take `⟨iA, iB⟩` from `(inv k).1 ρ h1 h2`. Take `⟨ja, jb⟩` from `hab₀ (k + 1) ρ h1 (h2.trans hsk)`. Conclude with `(iB.cmul h0 (ja.sub h0 iA)).sub h0 (iA.cmul h0 (jb.sub h0 iB))`. Use `haveI : Fact (∃ ρ ∈ Set.Icc r (s k), 0 < ρ) := ⟨⟨r, ⟨le_rfl, hrs _⟩, hr⟩⟩`. Take `⟨e1, e2⟩` from `ring_identities (I := Set.Icc r (s k)) (c' := c') (fun ρ hρ _ => ((inv k).1 ρ hρ.1 hρ.2).1) (fun ρ hρ _ => ((inv k).1 ρ hρ.1 hρ.2).2) (fun ρ hρ _ => (hab₀ (k + 1) ρ hρ.1 (hρ.2.trans hsk)).1) (fun ρ hρ _ => (hab₀ (k + 1) ρ hρ.1 (hρ.2.trans hsk)).2) (fun ρ hρ _ => fconv k ρ hρ.1 hρ …`.

Establish `hcc' : ConvergesAt (c - c') ρ` using `(cvk ρ hρr hρk).sub hρ0 (convergesAt_trunc_Icc c M ρ)`. Establish `htail : gaussNorm (c - c') ρ ≤ ε k`. Establish `hspec` using `tailM_spec (cvk r le_rfl (hrs k)) (cvk (s (k - 1)) (hrs _) (hmono (Nat.sub_le k 1))) (hε k)`. Use `gaussNorm_tail_le hρ0 (hε k).le fun n hn => ?_` and prove the remaining obligations. Break down `hρ with rfl | rfl` into its components or cases.

Conclude with `(hspec n hn).1`. Conclude with `(hspec n hn).2`. Establish `hgC : gaussNorm g ρ ≤ C k`. Apply the tactic sequence `rcases hρ with rfl | rfl <;> simp only [C] <;> linarith [gf0 (k - 1), gg0 (k - 1)]`. Establish `hfC : gaussNorm f ρ ≤ C k`.

Apply the tactic sequence `rcases hρ with rfl | rfl <;> simp only [C] <;> linarith [gf0 (k - 1), gg0 (k - 1)]`. Establish `hεC : ε k * C k = (1 / 2) ^ k` using `div_mul_cancel₀ _ (by linarith [hC k])`. Establish `hεpos` using `(hε k).le`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `gaussNorm ((a₀ (k + 1) - cmul c' g) - (seq k).1) ρ ≤ _`.

Rewrite using `[e1]`. Combine the equalities or inequalities in the displayed calculation. Express the relevant statement in the definitionally equal form `gaussNorm ((b₀ (k + 1) + cmul c' f) - (seq k).2) ρ ≤ _`. Rewrite using `[e2, gaussNorm_neg]`. Combine the equalities or inequalities in the displayed calculation.

Set `xA : ℕ → ℤ → K` to `fun k => (seq k).1`. Set `xB : ℕ → ℤ → K` to `fun k => (seq k).2`. Establish `cauchy : ∀ m ρ, r ≤ ρ → ρ ≤ s m → UCauchy xA ρ ∧ UCauchy xB ρ`. Introduce `m ρ h1 h2`. Establish `hρ0` using `pos ρ h1`.

Establish `key : ∀ j, m + 1 ≤ j → ∀ n, ‖xA (j + 1) n - xA j n‖ * ρ ^ n ≤ (1 / 2) ^ j ∧ ‖xB (j + 1) n - xB j n‖ * ρ ^ n ≤ (1 / 2) ^ j`. Introduce `j hj n`. Establish `hmj : s m ≤ s (j - 1)` using `hmono (by omega)`. Establish `hcv : ∀ ρ', r ≤ ρ' → ρ' ≤ s j → ConvergesAt (xA (j + 1) - xA j) ρ' ∧ ConvergesAt (xB (j + 1) - xB j) ρ'` using `fun ρ' g1 g2 => by`. Establish `h0` using `pos ρ' g1`.

Take `⟨u1, u2⟩` from `(inv (j + 1)).1 ρ' g1 (g2.trans (hmono (Nat.le_succ j)))`. Take `⟨v1, v2⟩` from `(inv j).1 ρ' g1 g2`. Conclude with `⟨u1.sub h0 v1, u2.sub h0 v2⟩`. Establish `hsj : s (j - 1) ≤ s j` using `hmono (Nat.sub_le j 1)`. Take `⟨sr1, sr2⟩` from `small j r (Or.inl rfl)`.

Take `⟨ss1, ss2⟩` from `small j (s (j - 1)) (Or.inr rfl)`. Prove the components needed by the constructor for the conclusion. Use `(weight_le_max hr h1 (h2.trans hmj) _ n).trans (max_le ?_ ?_)` and prove the remaining obligations. Conclude with `((hcv r le_rfl (hrs j)).1.le_gaussNorm n).trans sr1`. Conclude with `((hcv _ (hrs _) hsj).1.le_gaussNorm n).trans ss1`.

Use `(weight_le_max hr h1 (h2.trans hmj) _ n).trans (max_le ?_ ?_)` and prove the remaining obligations. Conclude with `((hcv r le_rfl (hrs j)).2.le_gaussNorm n).trans sr2`. Conclude with `((hcv _ (hrs _) hsj).2.le_gaussNorm n).trans ss2`. Establish `hpow : ∀ e > (0 : ℝ), ∃ K₀, ∀ j ≥ K₀, m + 1 ≤ j ∧ (1 / 2 : ℝ) ^ j ≤ e`. Introduce `e he`.

Take `⟨N, hN⟩` from `exists_pow_lt_of_lt_one he (by norm_num : (1 / 2 : ℝ) < 1)`. Use `⟨max N (m + 1), fun j hj => ⟨(le_max_right _ _).trans hj, ?_⟩⟩` and prove the remaining obligations. Conclude with `(pow_le_pow_of_le_one (by norm_num) (by norm_num) ((le_max_left _ _).trans hj)).trans hN.le`. Use `⟨fun e he => ?_, fun e he => ?_⟩` and prove the remaining obligations. Take `⟨K₀, hK⟩` from `hpow e he`.

Conclude with `⟨K₀, fun j hj n => ((key j (hK j hj).1 n).1).trans (hK j hj).2⟩`. Take `⟨K₀, hK⟩` from `hpow e he`. Conclude with `⟨K₀, fun j hj n => ((key j (hK j hj).1 n).2).trans (hK j hj).2⟩`. Establish `limconv : ∀ ρ, r ≤ ρ → ρ < 1 → ConvergesAt (limSeq xA) ρ ∧ ConvergesAt (limSeq xB) ρ`. Introduce `ρ h1 h2`.

Take `⟨m, hm⟩` from `hlim ρ h2`. Take `⟨cA, cB⟩` from `cauchy m ρ h1 hm`. Establish `ev : ∀ k ≥ m, ConvergesAt (xA k) ρ ∧ ConvergesAt (xB k) ρ` using `fun k hk => (inv k).1 ρ h1 (hm.trans (hmono hk))`. Conclude with `⟨cA.convergesAt_of_eventually (pos ρ h1) (K₁ := m) fun k hk => (ev k hk).1, cB.convergesAt_of_eventually (pos ρ h1) (K₁ := m) fun k hk => (ev k hk).2⟩`. Use `⟨limSeq xA, limSeq xB, limconv, ?_⟩` and prove the remaining obligations.

Take `⟨cA, cB⟩` from `cauchy 0 r le_rfl (hrs 0)`. Use `set D := cmul (limSeq xA) f + cmul (limSeq xB) g - Pi.single 0 1 with hD`. Establish `hDc : ConvergesAt D r`. Take `⟨l1, l2⟩` from `limconv r le_rfl ((hrs 0).trans_lt (hs1 0))`. Conclude with `((l1.cmul hr (hf r le_rfl ((hrs 0).trans_lt (hs1 0)))).add hr (l2.cmul hr (hg r le_rfl ((hrs 0).trans_lt (hs1 0))))).sub hr (convergesAt_single 0 1 r)`.

Establish `hbound : ∀ e > (0 : ℝ), gaussNorm D r ≤ e`. Introduce `e he`. Use `set G := 1 + gaussNorm f r + gaussNorm g r`. Establish `hG : 0 < G` using `by simp only [G]; linarith`. Take `⟨K₁, hK₁⟩` from `cA.gaussNorm_sub_le hr (div_pos he hG)`.

Take `⟨K₂, hK₂⟩` from `cB.gaussNorm_sub_le hr (div_pos he hG)`. Use `set k := max K₁ K₂`. Use `haveI : Fact (∃ ρ ∈ Set.Icc r (s 0), 0 < ρ) := ⟨⟨r, ⟨le_rfl, hrs _⟩, hr⟩⟩`. Set `I` to `Set.Icc r (s 0)`. Establish `cv0 : ∀ x : ℤ → K, (∀ ρ, r ≤ ρ → ρ ≤ s 0 → ConvergesAt x ρ) → ∀ ρ ∈ I, 0 < ρ → ConvergesAt x ρ` using `fun x hx ρ hρ _ => hx ρ hρ.1 hρ.2`.

Set `eA : AnnulusRing K I` to `⟨limSeq xA, cv0 _ fun ρ h1 h2 => (limconv ρ h1 (h2.trans_lt (hs1 0))).1⟩`. Set `eB : AnnulusRing K I` to `⟨limSeq xB, cv0 _ fun ρ h1 h2 => (limconv ρ h1 (h2.trans_lt (hs1 0))).2⟩`. Set `eAk : AnnulusRing K I` to `⟨xA k, cv0 _ fun ρ h1 h2 => ((inv k).1 ρ h1 (h2.trans (hmono (Nat.zero_le k)))).1⟩`. Set `eBk : AnnulusRing K I` to `⟨xB k, cv0 _ fun ρ h1 h2 => ((inv k).1 ρ h1 (h2.trans (hmono (Nat.zero_le k)))).2⟩`. Set `ef : AnnulusRing K I` to `⟨f, cv0 _ (fconv 0)⟩`.

Set `eg : AnnulusRing K I` to `⟨g, cv0 _ (gconv 0)⟩`. Establish `k1 : eAk * ef + eBk * eg = 1` using `AnnulusRing.ext (inv k).2`. Establish `iden : eA * ef + eB * eg - 1 = (eA - eAk) * ef + (eB - eBk) * eg`. Take the linear combination `k1`. Establish `hDeq : D = cmul (limSeq xA - xA k) f + cmul (limSeq xB - xB k) g` using `congrArg AnnulusRing.coeff iden`.

Establish `hconvA` using `(limconv r le_rfl ((hrs 0).trans_lt (hs1 0))).1.sub hr ((inv k).1 r le_rfl (hrs k)).1`. Establish `hconvB` using `(limconv r le_rfl ((hrs 0).trans_lt (hs1 0))).2.sub hr ((inv k).1 r le_rfl (hrs k)).2`. Establish `hfr` using `hf r le_rfl ((hrs 0).trans_lt (hs1 0))`. Establish `hgr` using `hg r le_rfl ((hrs 0).trans_lt (hs1 0))`. Rewrite using `[hDeq]`.

Use `(gaussNorm_add_le hr (hconvA.cmul hr hfr) (hconvB.cmul hr hgr)).trans (max_le ?_ ?_)` and prove the remaining obligations. Use `(gaussNorm_cmul_le hr hconvA hfr).trans ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `(gaussNorm_cmul_le hr hconvB hgr).trans ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Establish `hD0 : gaussNorm D r = 0` using `le_antisymm (le_of_forall_pos_le_add fun e he => by simpa using hbound e he) (gaussNorm_nonneg hr)`. Use `(gaussNorm_eq_zero_iff hr hDc).1 hD0` as an intermediate fact. Rewrite `this` using `[hD, sub_eq_zero]`. Conclude with `this`.
-/
theorem mittag_leffler (hr : 0 < r) (hs0 : r ≤ s 0) (hmono : Monotone s) (hs1 : ∀ k, s k < 1)
    (hlim : ∀ ρ < 1, ∃ k, ρ ≤ s k)
    (hf : ∀ ρ, r ≤ ρ → ρ < 1 → ConvergesAt f ρ) (hg : ∀ ρ, r ≤ ρ → ρ < 1 → ConvergesAt g ρ)
    (hloc : ∀ k, ∃ a b : ℤ → K, (∀ ρ, r ≤ ρ → ρ ≤ s k → ConvergesAt a ρ ∧ ConvergesAt b ρ) ∧
      cmul a f + cmul b g = Pi.single 0 1) :
    ∃ a b : ℤ → K, (∀ ρ, r ≤ ρ → ρ < 1 → ConvergesAt a ρ ∧ ConvergesAt b ρ) ∧
      cmul a f + cmul b g = Pi.single 0 1 := by
  choose a₀ b₀ hab₀ hid₀ using hloc
  have hrs : ∀ k, r ≤ s k := fun k => hs0.trans (hmono (Nat.zero_le k))
  have pos : ∀ ρ, r ≤ ρ → 0 < ρ := fun ρ h => hr.trans_le h
  have fconv : ∀ k ρ, r ≤ ρ → ρ ≤ s k → ConvergesAt f ρ := fun k ρ h1 h2 =>
    hf ρ h1 (h2.trans_lt (hs1 k))
  have gconv : ∀ k ρ, r ≤ ρ → ρ ≤ s k → ConvergesAt g ρ := fun k ρ h1 h2 =>
    hg ρ h1 (h2.trans_lt (hs1 k))

  let C : ℕ → ℝ := fun k => 1 + gaussNorm f r + gaussNorm f (s (k - 1)) + gaussNorm g r +
    gaussNorm g (s (k - 1))
  have gf0 : ∀ k, 0 ≤ gaussNorm f (s k) := fun k => gaussNorm_nonneg (pos _ (hrs k))
  have gg0 : ∀ k, 0 ≤ gaussNorm g (s k) := fun k => gaussNorm_nonneg (pos _ (hrs k))
  have gfr : 0 ≤ gaussNorm f r := gaussNorm_nonneg hr
  have ggr : 0 ≤ gaussNorm g r := gaussNorm_nonneg hr
  have hC : ∀ k, 1 ≤ C k := fun k => by
    have := gf0 (k - 1); have := gg0 (k - 1)
    simp only [C]; linarith
  let ε : ℕ → ℝ := fun k => (1 / 2) ^ k / C k
  have hε : ∀ k, 0 < ε k := fun k => div_pos (by positivity) (by linarith [hC k])
  let step : ℕ → (ℤ → K) × (ℤ → K) → (ℤ → K) × (ℤ → K) := fun k AB =>
    let c := cmul AB.2 (a₀ (k + 1) - AB.1) - cmul AB.1 (b₀ (k + 1) - AB.2)
    let c' := trunc c (Set.Icc (-(tailM c r (s (k - 1)) (ε k) : ℤ))
      (tailM c r (s (k - 1)) (ε k)))
    (a₀ (k + 1) - cmul c' g, b₀ (k + 1) + cmul c' f)
  let seq : ℕ → (ℤ → K) × (ℤ → K) := fun k => Nat.rec (a₀ 0, b₀ 0) step k
  have seq_succ : ∀ k, seq (k + 1) = step k (seq k) := fun k => rfl

  have inv : ∀ k, (∀ ρ, r ≤ ρ → ρ ≤ s k → ConvergesAt (seq k).1 ρ ∧ ConvergesAt (seq k).2 ρ) ∧
      cmul (seq k).1 f + cmul (seq k).2 g = Pi.single 0 1 := by
    intro k
    induction k with
    | zero => exact ⟨hab₀ 0, hid₀ 0⟩
    | succ k ih =>
      rw [seq_succ]
      set c := cmul (seq k).2 (a₀ (k + 1) - (seq k).1) - cmul (seq k).1 (b₀ (k + 1) - (seq k).2)
      set M := tailM c r (s (k - 1)) (ε k)
      have hc' : ∀ ρ, ConvergesAt (trunc c (Set.Icc (-(M : ℤ)) M)) ρ := fun ρ =>
        convergesAt_trunc_Icc c M ρ
      refine ⟨fun ρ h1 h2 => ⟨?_, ?_⟩, ?_⟩
      · exact ((hab₀ (k + 1) ρ h1 h2).1).sub (pos ρ h1)
          ((hc' ρ).cmul (pos ρ h1) (gconv _ ρ h1 h2))
      · exact ((hab₀ (k + 1) ρ h1 h2).2).add (pos ρ h1)
          ((hc' ρ).cmul (pos ρ h1) (fconv _ ρ h1 h2))
      · haveI : Fact (∃ ρ ∈ Set.Icc r (s (k + 1)), 0 < ρ) := ⟨⟨r, ⟨le_rfl, hrs _⟩, hr⟩⟩
        let I := Set.Icc r (s (k + 1))
        have cv : ∀ x : ℤ → K, (∀ ρ, r ≤ ρ → ρ ≤ s (k + 1) → ConvergesAt x ρ) →
            ∀ ρ ∈ I, 0 < ρ → ConvergesAt x ρ := fun x hx ρ hρ _ => hx ρ hρ.1 hρ.2
        let ea : AnnulusRing K I := ⟨a₀ (k + 1), cv _ fun ρ h1 h2 => (hab₀ _ ρ h1 h2).1⟩
        let eb : AnnulusRing K I := ⟨b₀ (k + 1), cv _ fun ρ h1 h2 => (hab₀ _ ρ h1 h2).2⟩
        let ef : AnnulusRing K I := ⟨f, cv _ (fconv _)⟩
        let eg : AnnulusRing K I := ⟨g, cv _ (gconv _)⟩
        let ec : AnnulusRing K I := ⟨trunc c (Set.Icc (-(M : ℤ)) M), cv _ fun ρ _ _ => hc' ρ⟩
        have k2 : ea * ef + eb * eg = 1 := AnnulusRing.ext (hid₀ (k + 1))
        have : (ea - ec * eg) * ef + (eb + ec * ef) * eg = 1 := by linear_combination k2
        exact congrArg AnnulusRing.coeff this

  have small : ∀ k ρ, (ρ = r ∨ ρ = s (k - 1)) →
      gaussNorm ((seq (k + 1)).1 - (seq k).1) ρ ≤ (1 / 2) ^ k ∧
      gaussNorm ((seq (k + 1)).2 - (seq k).2) ρ ≤ (1 / 2) ^ k := by
    intro k ρ hρ
    have hρr : r ≤ ρ := by rcases hρ with rfl | rfl; exacts [le_rfl, hrs _]
    have hρk : ρ ≤ s k := by
      rcases hρ with rfl | rfl; exacts [hrs k, hmono (Nat.sub_le k 1)]
    have hρ0 := pos ρ hρr
    rw [seq_succ]
    set c := cmul (seq k).2 (a₀ (k + 1) - (seq k).1) - cmul (seq k).1 (b₀ (k + 1) - (seq k).2)
      with hcdef
    set M := tailM c r (s (k - 1)) (ε k)
    set c' := trunc c (Set.Icc (-(M : ℤ)) M)
    have hsk : s k ≤ s (k + 1) := hmono (Nat.le_succ k)
    have cvk : ∀ ρ, r ≤ ρ → ρ ≤ s k → ConvergesAt c ρ := fun ρ h1 h2 => by
      have h0 := pos ρ h1
      obtain ⟨iA, iB⟩ := (inv k).1 ρ h1 h2
      obtain ⟨ja, jb⟩ := hab₀ (k + 1) ρ h1 (h2.trans hsk)
      exact (iB.cmul h0 (ja.sub h0 iA)).sub h0 (iA.cmul h0 (jb.sub h0 iB))
    haveI : Fact (∃ ρ ∈ Set.Icc r (s k), 0 < ρ) := ⟨⟨r, ⟨le_rfl, hrs _⟩, hr⟩⟩
    obtain ⟨e1, e2⟩ := ring_identities (I := Set.Icc r (s k)) (c' := c')
      (fun ρ hρ _ => ((inv k).1 ρ hρ.1 hρ.2).1) (fun ρ hρ _ => ((inv k).1 ρ hρ.1 hρ.2).2)
      (fun ρ hρ _ => (hab₀ (k + 1) ρ hρ.1 (hρ.2.trans hsk)).1)
      (fun ρ hρ _ => (hab₀ (k + 1) ρ hρ.1 (hρ.2.trans hsk)).2)
      (fun ρ hρ _ => fconv k ρ hρ.1 hρ.2) (fun ρ hρ _ => gconv k ρ hρ.1 hρ.2)
      (fun ρ hρ _ => cvk ρ hρ.1 hρ.2) (fun ρ _ _ => convergesAt_trunc_Icc c M ρ)
      (inv k).2 (hid₀ (k + 1)) hcdef
    have hcc' : ConvergesAt (c - c') ρ := (cvk ρ hρr hρk).sub hρ0 (convergesAt_trunc_Icc c M ρ)
    have htail : gaussNorm (c - c') ρ ≤ ε k := by
      have hspec := tailM_spec (cvk r le_rfl (hrs k)) (cvk (s (k - 1)) (hrs _)
        (hmono (Nat.sub_le k 1))) (hε k)
      refine gaussNorm_tail_le hρ0 (hε k).le fun n hn => ?_
      rcases hρ with rfl | rfl
      · exact (hspec n hn).1
      · exact (hspec n hn).2
    have hgC : gaussNorm g ρ ≤ C k := by
      rcases hρ with rfl | rfl <;> simp only [C] <;> linarith [gf0 (k - 1), gg0 (k - 1)]
    have hfC : gaussNorm f ρ ≤ C k := by
      rcases hρ with rfl | rfl <;> simp only [C] <;> linarith [gf0 (k - 1), gg0 (k - 1)]
    have hεC : ε k * C k = (1 / 2) ^ k := div_mul_cancel₀ _ (by linarith [hC k])
    have hεpos := (hε k).le
    refine ⟨?_, ?_⟩
    · change gaussNorm ((a₀ (k + 1) - cmul c' g) - (seq k).1) ρ ≤ _
      rw [e1]
      calc gaussNorm (cmul (c - c') g) ρ ≤ gaussNorm (c - c') ρ * gaussNorm g ρ :=
            gaussNorm_cmul_le hρ0 hcc' (gconv k ρ hρr hρk)
        _ ≤ ε k * C k := mul_le_mul htail hgC (gaussNorm_nonneg hρ0) hεpos
        _ = _ := hεC
    · change gaussNorm ((b₀ (k + 1) + cmul c' f) - (seq k).2) ρ ≤ _
      rw [e2, gaussNorm_neg]
      calc gaussNorm (cmul (c - c') f) ρ ≤ gaussNorm (c - c') ρ * gaussNorm f ρ :=
            gaussNorm_cmul_le hρ0 hcc' (fconv k ρ hρr hρk)
        _ ≤ ε k * C k := mul_le_mul htail hfC (gaussNorm_nonneg hρ0) hεpos
        _ = _ := hεC

  let xA : ℕ → ℤ → K := fun k => (seq k).1
  let xB : ℕ → ℤ → K := fun k => (seq k).2
  have cauchy : ∀ m ρ, r ≤ ρ → ρ ≤ s m → UCauchy xA ρ ∧ UCauchy xB ρ := by
    intro m ρ h1 h2
    have hρ0 := pos ρ h1
    have key : ∀ j, m + 1 ≤ j → ∀ n,
        ‖xA (j + 1) n - xA j n‖ * ρ ^ n ≤ (1 / 2) ^ j ∧
        ‖xB (j + 1) n - xB j n‖ * ρ ^ n ≤ (1 / 2) ^ j := by
      intro j hj n
      have hmj : s m ≤ s (j - 1) := hmono (by omega)
      have hcv : ∀ ρ', r ≤ ρ' → ρ' ≤ s j → ConvergesAt (xA (j + 1) - xA j) ρ' ∧
          ConvergesAt (xB (j + 1) - xB j) ρ' := fun ρ' g1 g2 => by
        have h0 := pos ρ' g1
        obtain ⟨u1, u2⟩ := (inv (j + 1)).1 ρ' g1 (g2.trans (hmono (Nat.le_succ j)))
        obtain ⟨v1, v2⟩ := (inv j).1 ρ' g1 g2
        exact ⟨u1.sub h0 v1, u2.sub h0 v2⟩
      have hsj : s (j - 1) ≤ s j := hmono (Nat.sub_le j 1)
      obtain ⟨sr1, sr2⟩ := small j r (Or.inl rfl)
      obtain ⟨ss1, ss2⟩ := small j (s (j - 1)) (Or.inr rfl)
      constructor
      · refine (weight_le_max hr h1 (h2.trans hmj) _ n).trans (max_le ?_ ?_)
        · exact ((hcv r le_rfl (hrs j)).1.le_gaussNorm n).trans sr1
        · exact ((hcv _ (hrs _) hsj).1.le_gaussNorm n).trans ss1
      · refine (weight_le_max hr h1 (h2.trans hmj) _ n).trans (max_le ?_ ?_)
        · exact ((hcv r le_rfl (hrs j)).2.le_gaussNorm n).trans sr2
        · exact ((hcv _ (hrs _) hsj).2.le_gaussNorm n).trans ss2
    have hpow : ∀ e > (0 : ℝ), ∃ K₀, ∀ j ≥ K₀, m + 1 ≤ j ∧ (1 / 2 : ℝ) ^ j ≤ e := by
      intro e he
      obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one he (by norm_num : (1 / 2 : ℝ) < 1)
      refine ⟨max N (m + 1), fun j hj => ⟨(le_max_right _ _).trans hj, ?_⟩⟩
      exact (pow_le_pow_of_le_one (by norm_num) (by norm_num) ((le_max_left _ _).trans hj)).trans
        hN.le
    refine ⟨fun e he => ?_, fun e he => ?_⟩
    · obtain ⟨K₀, hK⟩ := hpow e he
      exact ⟨K₀, fun j hj n => ((key j (hK j hj).1 n).1).trans (hK j hj).2⟩
    · obtain ⟨K₀, hK⟩ := hpow e he
      exact ⟨K₀, fun j hj n => ((key j (hK j hj).1 n).2).trans (hK j hj).2⟩

  have limconv : ∀ ρ, r ≤ ρ → ρ < 1 → ConvergesAt (limSeq xA) ρ ∧ ConvergesAt (limSeq xB) ρ := by
    intro ρ h1 h2
    obtain ⟨m, hm⟩ := hlim ρ h2
    obtain ⟨cA, cB⟩ := cauchy m ρ h1 hm
    have ev : ∀ k ≥ m, ConvergesAt (xA k) ρ ∧ ConvergesAt (xB k) ρ := fun k hk =>
      (inv k).1 ρ h1 (hm.trans (hmono hk))
    exact ⟨cA.convergesAt_of_eventually (pos ρ h1) (K₁ := m) fun k hk => (ev k hk).1,
      cB.convergesAt_of_eventually (pos ρ h1) (K₁ := m) fun k hk => (ev k hk).2⟩
  refine ⟨limSeq xA, limSeq xB, limconv, ?_⟩

  obtain ⟨cA, cB⟩ := cauchy 0 r le_rfl (hrs 0)
  set D := cmul (limSeq xA) f + cmul (limSeq xB) g - Pi.single 0 1 with hD
  have hDc : ConvergesAt D r := by
    obtain ⟨l1, l2⟩ := limconv r le_rfl ((hrs 0).trans_lt (hs1 0))
    exact ((l1.cmul hr (hf r le_rfl ((hrs 0).trans_lt (hs1 0)))).add hr
      (l2.cmul hr (hg r le_rfl ((hrs 0).trans_lt (hs1 0))))).sub hr (convergesAt_single 0 1 r)
  have hbound : ∀ e > (0 : ℝ), gaussNorm D r ≤ e := by
    intro e he
    set G := 1 + gaussNorm f r + gaussNorm g r
    have hG : 0 < G := by simp only [G]; linarith
    obtain ⟨K₁, hK₁⟩ := cA.gaussNorm_sub_le hr (div_pos he hG)
    obtain ⟨K₂, hK₂⟩ := cB.gaussNorm_sub_le hr (div_pos he hG)
    set k := max K₁ K₂
    haveI : Fact (∃ ρ ∈ Set.Icc r (s 0), 0 < ρ) := ⟨⟨r, ⟨le_rfl, hrs _⟩, hr⟩⟩
    let I := Set.Icc r (s 0)
    have cv0 : ∀ x : ℤ → K, (∀ ρ, r ≤ ρ → ρ ≤ s 0 → ConvergesAt x ρ) →
        ∀ ρ ∈ I, 0 < ρ → ConvergesAt x ρ := fun x hx ρ hρ _ => hx ρ hρ.1 hρ.2
    let eA : AnnulusRing K I := ⟨limSeq xA, cv0 _ fun ρ h1 h2 =>
      (limconv ρ h1 (h2.trans_lt (hs1 0))).1⟩
    let eB : AnnulusRing K I := ⟨limSeq xB, cv0 _ fun ρ h1 h2 =>
      (limconv ρ h1 (h2.trans_lt (hs1 0))).2⟩
    let eAk : AnnulusRing K I := ⟨xA k, cv0 _ fun ρ h1 h2 =>
      ((inv k).1 ρ h1 (h2.trans (hmono (Nat.zero_le k)))).1⟩
    let eBk : AnnulusRing K I := ⟨xB k, cv0 _ fun ρ h1 h2 =>
      ((inv k).1 ρ h1 (h2.trans (hmono (Nat.zero_le k)))).2⟩
    let ef : AnnulusRing K I := ⟨f, cv0 _ (fconv 0)⟩
    let eg : AnnulusRing K I := ⟨g, cv0 _ (gconv 0)⟩
    have k1 : eAk * ef + eBk * eg = 1 := AnnulusRing.ext (inv k).2
    have iden : eA * ef + eB * eg - 1 = (eA - eAk) * ef + (eB - eBk) * eg := by
      linear_combination k1
    have hDeq : D = cmul (limSeq xA - xA k) f + cmul (limSeq xB - xB k) g :=
      congrArg AnnulusRing.coeff iden
    have hconvA := (limconv r le_rfl ((hrs 0).trans_lt (hs1 0))).1.sub hr
      ((inv k).1 r le_rfl (hrs k)).1
    have hconvB := (limconv r le_rfl ((hrs 0).trans_lt (hs1 0))).2.sub hr
      ((inv k).1 r le_rfl (hrs k)).2
    have hfr := hf r le_rfl ((hrs 0).trans_lt (hs1 0))
    have hgr := hg r le_rfl ((hrs 0).trans_lt (hs1 0))
    rw [hDeq]
    refine (gaussNorm_add_le hr (hconvA.cmul hr hfr) (hconvB.cmul hr hgr)).trans (max_le ?_ ?_)
    · refine (gaussNorm_cmul_le hr hconvA hfr).trans ?_
      calc gaussNorm (limSeq xA - xA k) r * gaussNorm f r ≤ (e / G) * G :=
            mul_le_mul (hK₁ k (le_max_left _ _)) (by simp only [G]; linarith) gfr
              (div_pos he hG).le
        _ = e := div_mul_cancel₀ _ hG.ne'
    · refine (gaussNorm_cmul_le hr hconvB hgr).trans ?_
      calc gaussNorm (limSeq xB - xB k) r * gaussNorm g r ≤ (e / G) * G :=
            mul_le_mul (hK₂ k (le_max_right _ _)) (by simp only [G]; linarith) ggr
              (div_pos he hG).le
        _ = e := div_mul_cancel₀ _ hG.ne'
  have hD0 : gaussNorm D r = 0 :=
    le_antisymm (le_of_forall_pos_le_add fun e he => by simpa using hbound e he)
      (gaussNorm_nonneg hr)
  have := (gaussNorm_eq_zero_iff hr hDc).1 hD0
  rw [hD, sub_eq_zero] at this
  exact this

end MittagLeffler

end Laurent

end GroundTheory.PAdicHodge
