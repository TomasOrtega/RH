import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SameFns

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.RaiseFormula

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Conclude with `Fin.ext ((h i).trans (h' i).symm)`.
-/
theorem up_unique {j : ℕ} {a b c : M.Ty P} (h : M.Up P j a b) (h' : M.Up P j a c) : b = c := by
  funext i
  exact Fin.ext ((h i).trans (h' i).symm)

/- English proof (translation)
Rewrite `hl` using `[Finset.mem_Icc]`. Establish `h1` using `h ⟨l - 1, by omega⟩`. Establish `h2` using `h' ⟨l - 1, by omega⟩`. Establish `e : l - 1 + 1 = l` using `by omega`. Simplify using `only [e, if_true] at h1 h2`.

Assume the negation of the conclusion as `hne`. Rewrite `h2` using `[if_neg (fun x => hne x.symm)]`. Use linear arithmetic over natural numbers and integers.
-/
theorem up_index {l j : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) {a b : M.Ty P} (h : M.Up P l a b)
    (h' : M.Up P j a b) : j = l := by
  rw [Finset.mem_Icc] at hl
  have h1 := h ⟨l - 1, by omega⟩
  have h2 := h' ⟨l - 1, by omega⟩
  have e : l - 1 + 1 = l := by omega
  simp only [e, if_true] at h1 h2
  by_contra hne
  rw [if_neg (fun x => hne x.symm)] at h2
  omega

/- English proof (translation)
Rewrite `hl` using `[Finset.mem_Icc]`. Introduce and unpack `rfl`. Establish `h1` using `h ⟨l - 1, by omega⟩`. Establish `e : l - 1 + 1 = l` using `by omega`. Simplify using `only [e, if_true] at h1`.

Use linear arithmetic over natural numbers and integers.
-/
theorem up_ne {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) {a b : M.Ty P} (h : M.Up P l a b) : b ≠ a := by
  rw [Finset.mem_Icc] at hl
  rintro rfl
  have h1 := h ⟨l - 1, by omega⟩
  have e : l - 1 + 1 = l := by omega
  simp only [e, if_true] at h1
  omega

omit [StarRing A] in
/- English proof (translation)
Unfold `NF.proj`. Rewrite using `[← map_sum, ← map_one κ]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Simplify using `[Finset.sum_apply]`.
-/
theorem sum_proj (κ : (M.Ty P → ℂ) →ₐ[ℂ] A) : ∑ ρ, NF.proj κ ρ = 1 := by
  unfold NF.proj
  rw [← map_sum, ← map_one κ]
  congr 1
  funext x
  simp [Finset.sum_apply]

omit [StarRing A] in
/- English proof (translation)
Unfold `NF.proj`. Rewrite using `[← map_mul, ← map_smul]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Apply the tactic sequence `by_cases h : x = ρ <;> simp [h]`.
-/
theorem kap_mul_proj (κ : (M.Ty P → ℂ) →ₐ[ℂ] A) (f : M.Ty P → ℂ) (ρ : M.Ty P) :
    κ f * NF.proj κ ρ = f ρ • NF.proj κ ρ := by
  unfold NF.proj
  rw [← map_mul, ← map_smul]
  congr 1
  funext x
  by_cases h : x = ρ <;> simp [h]

omit [StarRing A] in
/- English proof (translation)
Use `kap_mul_proj κ (fun x => if x = ρ' then 1 else 0) ρ` as an intermediate fact. Rewrite `this` using `[if_neg (Ne.symm h), zero_smul]`. Conclude with `this`.
-/
theorem proj_mul_proj (κ : (M.Ty P → ℂ) →ₐ[ℂ] A) {ρ ρ' : M.Ty P} (h : ρ' ≠ ρ) :
    NF.proj κ ρ' * NF.proj κ ρ = 0 := by
  have := kap_mul_proj κ (fun x => if x = ρ' then 1 else 0) ρ
  rw [if_neg (Ne.symm h), zero_smul] at this
  exact this

/- English proof (translation)
Establish `h1` using `hd.2.2.2.1 j (fun a => if M.Up P j a ρ' then 1 else 0) (fun x => if x = ρ' then 1 else 0) (by`. Introduce `a b hab`. Distinguish the cases in `hb : b = ρ'`. Substitute `hb` using the available equality. Simplify using `[hab]`.

Establish `: ¬ M.Up P j a ρ'` using `fun h' => hb (up_unique hab h')`. Simplify using `[hb, this])`. Establish `h2 : NF.proj d.κ ρ' * d.SS j = _` using `h1`. Rewrite using `[h2, mul_assoc, kap_mul_proj, if_neg h, zero_smul, mul_zero]`.
-/
theorem proj_SS_proj (d : Q.NFData P A) (hd : d.Rel) {j : ℕ} {ρ ρ' : M.Ty P} (h : ¬ M.Up P j ρ ρ') :
    NF.proj d.κ ρ' * d.SS j * NF.proj d.κ ρ = 0 := by
  have h1 := hd.2.2.2.1 j (fun a => if M.Up P j a ρ' then 1 else 0) (fun x => if x = ρ' then 1 else 0) (by
    intro a b hab
    by_cases hb : b = ρ'
    · subst hb; simp [hab]
    · have : ¬ M.Up P j a ρ' := fun h' => hb (up_unique hab h')
      simp [hb, this])
  have h2 : NF.proj d.κ ρ' * d.SS j = _ := h1
  rw [h2, mul_assoc, kap_mul_proj, if_neg h, zero_smul, mul_zero]

/- English proof (translation)
Establish `hq : d.QQ Y 1 0 = d.L.GG * d.x Y * d.L.l0 Y + d.weightedSumBis Y` using `rfl`. Establish `hc : ∀ g ∈ d.L.fns ∪ {d.L.nab, d.L.nabs}, Commute (NF.proj d.κ ρ') g` using `fun g hg => hd.2.1 _ g hg`. Establish `c1 : Commute (NF.proj d.κ ρ') d.L.GG` using `hc _ (by simp [LevelData.fns])`. Establish `c2 : Commute (NF.proj d.κ ρ') d.L.GGi` using `hc _ (by simp [LevelData.fns])`. Establish `c3 : Commute (NF.proj d.κ ρ') d.L.ζb` using `hc _ (by simp [LevelData.fns])`.

Establish `c4 : Commute (NF.proj d.κ ρ') d.L.nab` using `hc _ (by simp)`. Establish `c5 : Commute (NF.proj d.κ ρ') (d.x Y)`. Unfold `NF.proj Q.NFData.x`. Conclude with `(Commute.all _ _).map d.κ`. Establish `c6 : Commute (NF.proj d.κ ρ') (d.L.l0 Y)`.

Unfold `LevelData.l0`. Conclude with `c4.neg_right.sub_right ((Algebra.commute_algebraMap_right _ _).mul_right (c3.mul_right c2))`. Establish `c7` using `(c1.mul_right c5).mul_right c6`. Rewrite using `[hq, mul_add, add_mul, c7.eq, mul_assoc _ (NF.proj d.κ ρ'), proj_mul_proj _ (up_ne hl h), mul_zero, zero_add]`. Unfold `Q.NFData.weightedSumBis`.

Establish `key : ∀ j, NF.proj d.κ ρ' * (d.SS j * d.κ fun ρ => M.xEx P {j} ρ Y) * NF.proj d.κ ρ = M.xEx P {j} ρ Y • (NF.proj d.κ ρ' * d.SS j * NF.proj d.κ ρ)`. Introduce `j`. Rewrite using `[← mul_assoc, mul_assoc _ (d.κ _), kap_mul_proj, mul_smul_comm]`. Rewrite using `[Finset.mul_sum, Finset.sum_mul, Finset.sum_eq_single l]`. Conclude with `key l`.

Introduce `j _ hj`. Rewrite using `[key, proj_SS_proj d hd (fun h' => hj (up_index hl h h')), smul_zero]`. Introduce `h'`. Conclude with `absurd hl h'`.
-/
theorem proj_raising_proj_eq_smul (d : Q.NFData P A) (hd : d.Rel) {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) (Y : ℂ)
    {ρ ρ' : M.Ty P} (h : M.Up P l ρ ρ') :
    NF.proj d.κ ρ' * d.QQ Y 1 0 * NF.proj d.κ ρ =
      M.xEx P {l} ρ Y • (NF.proj d.κ ρ' * d.SS l * NF.proj d.κ ρ) := by
  have hq : d.QQ Y 1 0 = d.L.GG * d.x Y * d.L.l0 Y + d.weightedSumBis Y := rfl
  have hc : ∀ g ∈ d.L.fns ∪ {d.L.nab, d.L.nabs}, Commute (NF.proj d.κ ρ') g := fun g hg => hd.2.1 _ g hg
  have c1 : Commute (NF.proj d.κ ρ') d.L.GG := hc _ (by simp [LevelData.fns])
  have c2 : Commute (NF.proj d.κ ρ') d.L.GGi := hc _ (by simp [LevelData.fns])
  have c3 : Commute (NF.proj d.κ ρ') d.L.ζb := hc _ (by simp [LevelData.fns])
  have c4 : Commute (NF.proj d.κ ρ') d.L.nab := hc _ (by simp)
  have c5 : Commute (NF.proj d.κ ρ') (d.x Y) := by
    unfold NF.proj Q.NFData.x
    exact (Commute.all _ _).map d.κ
  have c6 : Commute (NF.proj d.κ ρ') (d.L.l0 Y) := by
    unfold LevelData.l0
    exact c4.neg_right.sub_right ((Algebra.commute_algebraMap_right _ _).mul_right (c3.mul_right c2))
  have c7 := (c1.mul_right c5).mul_right c6
  rw [hq, mul_add, add_mul, c7.eq, mul_assoc _ (NF.proj d.κ ρ'), proj_mul_proj _ (up_ne hl h), mul_zero, zero_add]
  unfold Q.NFData.weightedSumBis
  have key : ∀ j, NF.proj d.κ ρ' * (d.SS j * d.κ fun ρ => M.xEx P {j} ρ Y) * NF.proj d.κ ρ =
      M.xEx P {j} ρ Y • (NF.proj d.κ ρ' * d.SS j * NF.proj d.κ ρ) := by
    intro j
    rw [← mul_assoc, mul_assoc _ (d.κ _), kap_mul_proj, mul_smul_comm]
  rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_eq_single l]
  · exact key l
  · intro j _ hj
    rw [key, proj_SS_proj d hd (fun h' => hj (up_index hl h h')), smul_zero]
  · intro h'; exact absurd hl h'

/- English proof (translation)
Unfold `M.xC at h`. Unfold `M.xEx`. Rewrite `h`, the goal using `[Finset.prod_ne_zero_iff]`. Conclude with `fun i hi => h i (Finset.mem_sdiff.1 hi).1`.
-/
theorem xEx_ne_zero (ex : Finset ℕ) (ρ : M.Ty P) (Y : ℂ) (h : M.xC P ρ Y ≠ 0) : M.xEx P ex ρ Y ≠ 0 := by
  unfold M.xC at h
  unfold M.xEx
  rw [Finset.prod_ne_zero_iff] at h ⊢
  exact fun i hi => h i (Finset.mem_sdiff.1 hi).1

/- English proof (translation)
Introduce `P A _ _ _ _ d hd l hl Y hY`. Establish `hr : d.Rel` using `hd.2.2.1`. Use `⟨fun ρ ρ' => if M.Up P l ρ ρ' then (M.xEx P {l} ρ Y)⁻¹ else 0, ?_⟩` and prove the remaining obligations. Establish `h0 : d.SS l = ∑ ρ, ∑ ρ', NF.proj d.κ ρ' * d.SS l * NF.proj d.κ ρ`. Repeatedly rewrite using `[← Finset.sum_mul, ← Finset.mul_sum]`.

Rewrite using `[sum_proj, one_mul, mul_one]`. Use `h0.trans (Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun ρ' _ => ?_)` and prove the remaining obligations. Distinguish the cases in `h : M.Up P l ρ ρ'`. Simplify using `only [if_pos h]`. Rewrite using `[proj_raising_proj_eq_smul d hr hl Y h, smul_smul, inv_mul_cancel₀ (xEx_ne_zero _ _ _ (hY ρ)), one_smul]`.

Simplify using `only [if_neg h]`. Rewrite using `[zero_smul, proj_SS_proj d hr h]`.
-/
theorem ss_formula : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ Y : ℂ, (∀ ρ : M.Ty P, M.xC P ρ Y ≠ 0) → ∃ co : M.Ty P → M.Ty P → ℂ, d.SS l = ∑ ρ, ∑ ρ', co ρ ρ' • (NF.proj d.κ ρ' * d.QQ Y 1 0 * NF.proj d.κ ρ) := by
  intro P A _ _ _ _ d hd l hl Y hY
  have hr : d.Rel := hd.2.2.1
  refine ⟨fun ρ ρ' => if M.Up P l ρ ρ' then (M.xEx P {l} ρ Y)⁻¹ else 0, ?_⟩
  have h0 : d.SS l = ∑ ρ, ∑ ρ', NF.proj d.κ ρ' * d.SS l * NF.proj d.κ ρ := by
    simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
    rw [sum_proj, one_mul, mul_one]
  refine h0.trans (Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun ρ' _ => ?_)
  by_cases h : M.Up P l ρ ρ'
  · simp only [if_pos h]
    rw [proj_raising_proj_eq_smul d hr hl Y h, smul_smul, inv_mul_cancel₀ (xEx_ne_zero _ _ _ (hY ρ)), one_smul]
  · simp only [if_neg h]
    rw [zero_smul, proj_SS_proj d hr h]

end GlobalTheory.HatNF.RaiseFormula
