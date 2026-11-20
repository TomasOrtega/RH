import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartEnergyCocycle
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartEnergySymm
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartEnergyIntegrable
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PHermFormCompare
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartHessCompare
import GroundTheory.HeightsAndTheta.Heights.Intersections.NotLtLtOfMemMinimalPrimes
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory Filter
open scoped ComplexOrder

noncomputable section

namespace ChartEnergyCocycleAlt

variable {e : ℕ}

def dens (s : Fin e → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) : (Fin e → ℂ) → ℝ :=
  maDensity (fun j => hermChartPot (s j))

def pairing (X Y : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (s : Fin e → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) : ℝ :=
  ∫ y, (hermChartPot X y - hermChartPot Y y) * dens s y

def blocks {α : Type*} (a b c : α) (i j : ℕ) : Fin e → α :=
  fun s => if (s : ℕ) < i then a else if (s : ℕ) < i + j then b else c

/- English proof (translation)
Unfold `blocks`. Use `split_ifs`. Use `exacts [hM, hN, hP]`.
-/
theorem blocks_posDef {M N P : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hM : M.PosDef) (hN : N.PosDef)
    (hP : P.PosDef) (i j : ℕ) (s : Fin e) : (blocks M N P i j s).PosDef := by
  unfold blocks
  split_ifs
  exacts [hM, hN, hP]

/- English proof (translation)
Rewrite using `[Function.update_apply]`. Use `split_ifs`. Use `exacts [hX, hT s]`.
-/
theorem update_posDef {T : Fin e → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hT : ∀ j, (T j).PosDef) (p : Fin e)
    {X : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hX : X.PosDef) (s : Fin e) : (Function.update T p X s).PosDef := by
  rw [Function.update_apply]
  split_ifs
  exacts [hX, hT s]

/- English proof (translation)
Establish `hCmp` using `HermFormCompare.proof`. Establish `hHess` using `ChartHessCompare.proof hCmp`. Use `choose C hC using fun j => hHess e (s j) Y (hs j) hY`. Take `⟨C₀, hC₀⟩` from `hHess e Y Y hY hY`. Take `⟨K, hK⟩` from `ChartEnergyIntegrableAlt.pot_sub_bound hCmp hX hY`.

Use `set C' : ℝ := 1 + ∑ j, |C j| with hC'`. Establish `hCj : ∀ j, C j ≤ C'` using `fun j => by`. Establish `h1` using `Finset.single_le_sum (f := fun j => |C j|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)`. Establish `h2` using `le_abs_self (C j)`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hbound : ∀ y, ‖dens s y‖ ≤ C' ^ e * maDensity (fun _ : Fin e => hermChartPot Y) y`. Introduce `y`. Use `set HN := cxHessian (hermChartPot Y) y with hHN`. Use `set A : Fin e → Matrix (Fin e) (Fin e) ℂ := fun j => cxHessian (hermChartPot (s j)) y with hAdef`. Use `set B : Fin e → Matrix (Fin e) (Fin e) ℂ := fun _ => ((C' : ℝ) : ℂ) • HN with hBdef`.

Establish `hNp : HN.PosSemidef` using `(hC₀ y).1.posSemidef`. Establish `hApsd : ∀ j, (A j).PosSemidef` using `fun j => (hC j y).1.posSemidef`. Establish `hAB : ∀ j, (B j - A j).PosSemidef` using `fun j => by`. Establish `h : ((C' : ℝ) : ℂ) • HN - A j = (((C j : ℝ) : ℂ) • HN - A j) + (((C' - C j : ℝ)) : ℂ) • HN`. Use `push_cast`.

Rewrite using `[sub_smul]`. Normalize the expressions using the abelian group laws. Use `show (((C' : ℝ) : ℂ) • HN - A j).PosSemidef`. Rewrite using `[h]`. Conclude with `(hC j y).2.add (hNp.smul (Complex.zero_le_real.2 (sub_nonneg.2 (hCj j))))`.

Establish `hmono : (mixedDisc A).re ≤ (mixedDisc B).re` using `ReciprocityTheory.AnForm.A.mdisc_re_mono A B hApsd hAB`. Establish `hnn : 0 ≤ (mixedDisc A).re` using `(ReciprocityTheory.AnForm.A.mdisc_nonneg_of_posSemidef A hApsd).2`. Establish `hB : mixedDisc B = ((C' : ℝ) : ℂ) ^ e * HN.det`. Establish `h` using `ReciprocityTheory.AnForm.A.mdisc_const (((C' : ℝ) : ℂ) • HN)`. Rewrite `h` using `[det_smul, Fintype.card_fin]`.

Conclude with `h`. Establish `hN1 : mixedDisc (fun _ : Fin e => HN) = HN.det` using `ReciprocityTheory.AnForm.A.mdisc_const HN`. Establish `hc : 0 ≤ (e.factorial : ℝ) * (2 / Real.pi) ^ e` using `by positivity`. Establish `hd : dens s y = (e.factorial : ℝ) * (2 / Real.pi) ^ e * (mixedDisc A).re` using `rfl`. Establish `hd0 : maDensity (fun _ : Fin e => hermChartPot Y) y = (e.factorial : ℝ) * (2 / Real.pi) ^ e * (mixedDisc (fun _ : Fin e => HN)).re` using `rfl`.

Rewrite using `[hd, hd0, hN1, Real.norm_eq_abs, abs_mul, abs_of_nonneg hc, abs_of_nonneg hnn]`. Rewrite `hmono` using `[hB, ← Complex.ofReal_pow, Complex.re_ofReal_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `hmeas : Measurable (dens s)` using `ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adb_measurable_maDensity _`. Establish `hmix : Integrable (dens s)` using `Integrable.mono' ((ChartDensityIntegrable.proof e Y hY).const_mul (C' ^ e)) hmeas.aestronglyMeasurable (Eventually.of_forall hbound)`.

Conclude with `hmix.bdd_mul ((ChartEnergyIntegrableAlt.measurable_hermChartPot X).sub (ChartEnergyIntegrableAlt.measurable_hermChartPot Y)).aestronglyMeasurable (Eventually.of_forall hK)`.
-/
theorem integrable_pairing {X Y : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hX : X.PosDef) (hY : Y.PosDef)
    {s : Fin e → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hs : ∀ j, (s j).PosDef) :
    Integrable (fun y : Fin e → ℂ => (hermChartPot X y - hermChartPot Y y) * dens s y) := by
  have hCmp := HermFormCompare.proof
  have hHess := ChartHessCompare.proof hCmp
  choose C hC using fun j => hHess e (s j) Y (hs j) hY
  obtain ⟨C₀, hC₀⟩ := hHess e Y Y hY hY
  obtain ⟨K, hK⟩ := ChartEnergyIntegrableAlt.pot_sub_bound hCmp hX hY
  set C' : ℝ := 1 + ∑ j, |C j| with hC'
  have hCj : ∀ j, C j ≤ C' := fun j => by
    have h1 := Finset.single_le_sum (f := fun j => |C j|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)
    have h2 := le_abs_self (C j)
    linarith
  have hbound : ∀ y, ‖dens s y‖ ≤ C' ^ e * maDensity (fun _ : Fin e => hermChartPot Y) y := by
    intro y
    set HN := cxHessian (hermChartPot Y) y with hHN
    set A : Fin e → Matrix (Fin e) (Fin e) ℂ := fun j => cxHessian (hermChartPot (s j)) y with hAdef
    set B : Fin e → Matrix (Fin e) (Fin e) ℂ := fun _ => ((C' : ℝ) : ℂ) • HN with hBdef
    have hNp : HN.PosSemidef := (hC₀ y).1.posSemidef
    have hApsd : ∀ j, (A j).PosSemidef := fun j => (hC j y).1.posSemidef
    have hAB : ∀ j, (B j - A j).PosSemidef := fun j => by
      have h : ((C' : ℝ) : ℂ) • HN - A j = (((C j : ℝ) : ℂ) • HN - A j) + (((C' - C j : ℝ)) : ℂ) • HN := by
        push_cast
        rw [sub_smul]
        abel
      show (((C' : ℝ) : ℂ) • HN - A j).PosSemidef
      rw [h]
      exact (hC j y).2.add (hNp.smul (Complex.zero_le_real.2 (sub_nonneg.2 (hCj j))))
    have hmono : (mixedDisc A).re ≤ (mixedDisc B).re := ReciprocityTheory.AnForm.A.mdisc_re_mono A B hApsd hAB
    have hnn : 0 ≤ (mixedDisc A).re := (ReciprocityTheory.AnForm.A.mdisc_nonneg_of_posSemidef A hApsd).2
    have hB : mixedDisc B = ((C' : ℝ) : ℂ) ^ e * HN.det := by
      have h := ReciprocityTheory.AnForm.A.mdisc_const (((C' : ℝ) : ℂ) • HN)
      rw [det_smul, Fintype.card_fin] at h
      exact h
    have hN1 : mixedDisc (fun _ : Fin e => HN) = HN.det := ReciprocityTheory.AnForm.A.mdisc_const HN
    have hc : 0 ≤ (e.factorial : ℝ) * (2 / Real.pi) ^ e := by positivity
    have hd : dens s y = (e.factorial : ℝ) * (2 / Real.pi) ^ e * (mixedDisc A).re := rfl
    have hd0 : maDensity (fun _ : Fin e => hermChartPot Y) y =
        (e.factorial : ℝ) * (2 / Real.pi) ^ e * (mixedDisc (fun _ : Fin e => HN)).re := rfl
    rw [hd, hd0, hN1, Real.norm_eq_abs, abs_mul, abs_of_nonneg hc, abs_of_nonneg hnn]
    rw [hB, ← Complex.ofReal_pow, Complex.re_ofReal_mul] at hmono
    calc (e.factorial : ℝ) * (2 / Real.pi) ^ e * (mixedDisc A).re
        ≤ (e.factorial : ℝ) * (2 / Real.pi) ^ e * (C' ^ e * HN.det.re) :=
          mul_le_mul_of_nonneg_left hmono hc
      _ = _ := by ring
  have hmeas : Measurable (dens s) := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adb_measurable_maDensity _
  have hmix : Integrable (dens s) :=
    Integrable.mono' ((ChartDensityIntegrable.proof e Y hY).const_mul (C' ^ e)) hmeas.aestronglyMeasurable
      (Eventually.of_forall hbound)
  exact hmix.bdd_mul ((ChartEnergyIntegrableAlt.measurable_hermChartPot X).sub
    (ChartEnergyIntegrableAlt.measurable_hermChartPot Y)).aestronglyMeasurable (Eventually.of_forall hK)

/- English proof (translation)
Unfold `pairing`. Rewrite using `[← integral_add (integrable_pairing hX hY hs) (integrable_pairing hY hZ hs)]`. Use `congr 1`. Use function extensionality and compare the values at `y`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pairing_add {X Y Z : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hX : X.PosDef) (hY : Y.PosDef) (hZ : Z.PosDef)
    {s : Fin e → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hs : ∀ j, (s j).PosDef) :
    pairing X Z s = pairing X Y s + pairing Y Z s := by
  unfold pairing
  rw [← integral_add (integrable_pairing hX hY hs) (integrable_pairing hY hZ hs)]
  congr 1
  funext y
  ring

/- English proof (translation)
Unfold `pairing`. Rewrite using `[← integral_sub (integrable_pairing hX hY hs) (integrable_pairing hX hY ht)]`. Use `congr 1`. Use function extensionality and compare the values at `y`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pairing_sub {X Y : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hX : X.PosDef) (hY : Y.PosDef)
    {s t : Fin e → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hs : ∀ j, (s j).PosDef) (ht : ∀ j, (t j).PosDef) :
    pairing X Y s - pairing X Y t = ∫ y, (hermChartPot X y - hermChartPot Y y) * (dens s y - dens t y) := by
  unfold pairing
  rw [← integral_sub (integrable_pairing hX hY hs) (integrable_pairing hX hY ht)]
  congr 1
  funext y
  ring

/- English proof (translation)
Unfold `pairing`. Use `integral_congr_ae (Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Simplify using `only [dens]`. Rewrite using `[show (fun j => hermChartPot ((s ∘ σ) j)) = (fun j => hermChartPot (s j)) ∘ σ from rfl, Inter.maDensity_comp_perm]`.
-/
theorem pairing_perm (X Y : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (s : Fin e → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ)
    (σ : Equiv.Perm (Fin e)) : pairing X Y (s ∘ σ) = pairing X Y s := by
  unfold pairing
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [dens]
  rw [show (fun j => hermChartPot ((s ∘ σ) j)) = (fun j => hermChartPot (s j)) ∘ σ from rfl,
    Inter.maDensity_comp_perm]

/- English proof (translation)
Take `⟨p, hpv⟩ : ∃ p : Fin e, (p : ℕ) = k + j` from `⟨⟨k + j, h⟩, rfl⟩`. Take `⟨q, hqv⟩ : ∃ q : Fin e, (q : ℕ) = k` from `⟨⟨k, by omega⟩, rfl⟩`. Use `set T := blocks M N P k (j + 1) with hTdef`. Establish `hT : ∀ s, (T s).PosDef` using `blocks_posDef hM hN hP k (j + 1)`. Establish `hTP : Function.update T p P = blocks M N P k j`.

Use function extensionality and compare the values at `s`. Simplify using `only [Function.update_apply, hTdef, blocks, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | rfl | omega`. Establish `hTN : Function.update T p N = T`. Use function extensionality and compare the values at `s`.

Simplify using `only [Function.update_apply, hTdef, blocks, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | rfl | omega`. Establish `key : ∀ s : Fin e, ((Equiv.swap q p s : Fin e) : ℕ) = if (s : ℕ) = k then k + j else if (s : ℕ) = k + j then k else s`. Introduce `s`. Rewrite using `[Equiv.swap_apply_def]`.

Apply the tactic sequence `split_ifs <;> (try simp only [Fin.ext_iff] at *) <;> omega`. Establish `hTM : Function.update T p M ∘ Equiv.swap q p = blocks M N P (k + 1) j`. Use function extensionality and compare the values at `s`. Simplify using `only [Function.comp_apply, Function.update_apply, hTdef, blocks, Fin.ext_iff, key]`. Apply the tactic sequence `split_ifs <;> first | rfl | omega`.

Establish `hsym` using `hS e M N N P T p hM hN hN hP hT`. Establish `e1 : pairing M N (Function.update T p N) - pairing M N (Function.update T p P) = pairing N P (Function.update T p M) - pairing N P (Function.update T p N)`. Rewrite using `[pairing_sub hM hN (update_posDef hT p hN) (update_posDef hT p hP), pairing_sub hN hP (update_posDef hT p hM) (update_posDef hT p hN)]`. Conclude with `hsym`. Rewrite `e1` using `[← pairing_perm N P (Function.update T p M) (Equiv.swap q p), hTM, hTP, hTN]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem step (hS : ChartEnergySymm.Statement) {M N P : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hM : M.PosDef)
    (hN : N.PosDef) (hP : P.PosDef) {k j : ℕ} (h : k + j < e) :
    pairing M N (blocks M N P k j) - pairing M N (blocks M N P k (j + 1)) =
      -(pairing N P (blocks M N P (k + 1) j) - pairing N P (blocks M N P k (j + 1))) := by
  obtain ⟨p, hpv⟩ : ∃ p : Fin e, (p : ℕ) = k + j := ⟨⟨k + j, h⟩, rfl⟩
  obtain ⟨q, hqv⟩ : ∃ q : Fin e, (q : ℕ) = k := ⟨⟨k, by omega⟩, rfl⟩
  set T := blocks M N P k (j + 1) with hTdef
  have hT : ∀ s, (T s).PosDef := blocks_posDef hM hN hP k (j + 1)
  have hTP : Function.update T p P = blocks M N P k j := by
    funext s
    simp only [Function.update_apply, hTdef, blocks, Fin.ext_iff]
    split_ifs <;> first | rfl | omega
  have hTN : Function.update T p N = T := by
    funext s
    simp only [Function.update_apply, hTdef, blocks, Fin.ext_iff]
    split_ifs <;> first | rfl | omega
  have key : ∀ s : Fin e, ((Equiv.swap q p s : Fin e) : ℕ) =
      if (s : ℕ) = k then k + j else if (s : ℕ) = k + j then k else s := by
    intro s
    rw [Equiv.swap_apply_def]
    split_ifs <;> (try simp only [Fin.ext_iff] at *) <;> omega
  have hTM : Function.update T p M ∘ Equiv.swap q p = blocks M N P (k + 1) j := by
    funext s
    simp only [Function.comp_apply, Function.update_apply, hTdef, blocks, Fin.ext_iff, key]
    split_ifs <;> first | rfl | omega
  have hsym := hS e M N N P T p hM hN hN hP hT
  have e1 : pairing M N (Function.update T p N) - pairing M N (Function.update T p P) =
      pairing N P (Function.update T p M) - pairing N P (Function.update T p N) := by
    rw [pairing_sub hM hN (update_posDef hT p hN) (update_posDef hT p hP),
      pairing_sub hN hP (update_posDef hT p hM) (update_posDef hT p hN)]
    exact hsym
  rw [← pairing_perm N P (Function.update T p M) (Equiv.swap q p), hTM, hTP, hTN] at e1
  linarith

/- English proof (translation)
The claim follows from `| 0 => by simp | e + 1 => by have ih := antidiag_telescope g e have h1 : ∀ k ∈ Finset.range (e + 1), ∑ j ∈ Finset.range (e + 1 - k), (g (k + 1) j - g k (j + 1)) = ∑ j ∈ Finset.range (e - k), (g (k + 1) j - g k (j + 1)) + (g (k + 1) (e - k) - g k (e - k + 1)) := by intro k hk rw [ …`.
-/
theorem antidiag_telescope (g : ℕ → ℕ → ℝ) : ∀ e : ℕ,
    ∑ k ∈ Finset.range (e + 1), ∑ j ∈ Finset.range (e - k), (g (k + 1) j - g k (j + 1)) =
      ∑ k ∈ Finset.range (e + 1), (g k 0 - g 0 k)
  | 0 => by simp
  | e + 1 => by
    have ih := antidiag_telescope g e
    have h1 : ∀ k ∈ Finset.range (e + 1), ∑ j ∈ Finset.range (e + 1 - k), (g (k + 1) j - g k (j + 1)) =
        ∑ j ∈ Finset.range (e - k), (g (k + 1) j - g k (j + 1)) + (g (k + 1) (e - k) - g k (e - k + 1)) := by
      intro k hk
      rw [Finset.mem_range] at hk
      rw [show e + 1 - k = e - k + 1 by omega, Finset.sum_range_succ]
    have h2 : ∑ k ∈ Finset.range (e + 1), (g (k + 1) (e - k) - g k (e - k + 1)) = g (e + 1) 0 - g 0 (e + 1) := by
      have h3 := Finset.sum_range_sub (fun k => g k (e + 1 - k)) (e + 1)
      simp only [Nat.sub_self, Nat.sub_zero] at h3
      rw [← h3]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_range] at hk
      rw [show e + 1 - (k + 1) = e - k by omega, show e + 1 - k = e - k + 1 by omega]
    rw [Finset.sum_range_succ _ (e + 1), Finset.sum_range_succ (fun k => g k 0 - g 0 k) (e + 1), ← ih,
      Nat.sub_self, Finset.sum_range_zero, add_zero, Finset.sum_congr rfl h1, Finset.sum_add_distrib, h2]

/- English proof (translation)
Unfold `chartMixedEnergy pairing dens`. Use `integral_congr_ae (Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Simplify using `only`. Use `congr 2`. Use function extensionality and compare the values at `j`.

Apply the tactic sequence `by_cases h : (j : ℕ) < k <;> simp [h]`.
-/
theorem chartMixedEnergy_eq (X Y : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (k : ℕ) :
    chartMixedEnergy X Y k = pairing X Y (fun s : Fin e => if (s : ℕ) < k then X else Y) := by
  unfold chartMixedEnergy pairing dens
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  congr 2
  funext j
  by_cases h : (j : ℕ) < k <;> simp [h]

end ChartEnergyCocycleAlt

open ChartEnergyCocycleAlt in

/- English proof (translation)
Introduce `e M N P hM hN hP`. Establish `hb` using `blocks_posDef hM hN hP`. Use `set g : ℕ → ℕ → ℝ := fun i j => pairing N P (blocks M N P i j) with hg`. Establish `e1 : ∀ k ∈ Finset.range (e + 1), chartMixedEnergy M P k = pairing M N (blocks M N P k 0) + g k 0`. Introduce `k _`.

Rewrite using `[chartMixedEnergy_eq, hg]`. Establish `: (fun s : Fin e => if (s : ℕ) < k then M else P) = blocks M N P k 0`. Use function extensionality and compare the values at `s`. Simplify using `only [blocks, add_zero]`. Apply the tactic sequence `split_ifs <;> rfl`.

Rewrite using `[this]`. Conclude with `pairing_add hM hN hP (hb k 0)`. Establish `e2 : ∀ k ∈ Finset.range (e + 1), chartMixedEnergy M N k = pairing M N (blocks M N P k (e - k))`. Introduce `k hk`. Rewrite `hk` using `[Finset.mem_range]`.

Rewrite using `[chartMixedEnergy_eq]`. Use `congr 1`. Use function extensionality and compare the values at `s`. Use `s.isLt` as an intermediate fact. Simplify using `only [blocks]`.

Apply the tactic sequence `split_ifs <;> first | rfl | omega`. Establish `e3 : ∀ k ∈ Finset.range (e + 1), chartMixedEnergy N P k = g 0 k`. Introduce `k _`. Rewrite using `[chartMixedEnergy_eq, hg]`. Use `congr 1`.

Use function extensionality and compare the values at `s`. Simplify using `only [blocks, zero_add]`. Apply the tactic sequence `split_ifs <;> first | rfl | omega`. Establish `tele : ∀ k ∈ Finset.range (e + 1), pairing M N (blocks M N P k 0) - pairing M N (blocks M N P k (e - k)) = -∑ j ∈ Finset.range (e - k), (g (k + 1) j - g k (j + 1))`. Introduce `k hk`.

Rewrite `hk` using `[Finset.mem_range]`. Rewrite using `[← Finset.sum_range_sub' (fun j => pairing M N (blocks M N P k j)), ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations. Rewrite `hj` using `[Finset.mem_range]`. Conclude with `step hS hM hN hP (by omega)`.

Establish `hsum : ∑ k ∈ Finset.range (e + 1), (pairing M N (blocks M N P k 0) - pairing M N (blocks M N P k (e - k))) = -∑ k ∈ Finset.range (e + 1), (g k 0 - g 0 k)`. Rewrite using `[Finset.sum_congr rfl tele, Finset.sum_neg_distrib, antidiag_telescope]`. Rewrite using `[Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_congr rfl e3, Finset.sum_add_distrib]`. Simplify using `only [Finset.sum_sub_distrib] at hsum`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem ChartEnergyCocycle.proof (hS : ChartEnergySymm.Statement) : ChartEnergyCocycle.Statement := by
  intro e M N P hM hN hP
  have hb := blocks_posDef hM hN hP
  set g : ℕ → ℕ → ℝ := fun i j => pairing N P (blocks M N P i j) with hg
  have e1 : ∀ k ∈ Finset.range (e + 1), chartMixedEnergy M P k =
      pairing M N (blocks M N P k 0) + g k 0 := by
    intro k _
    rw [chartMixedEnergy_eq, hg]
    have : (fun s : Fin e => if (s : ℕ) < k then M else P) = blocks M N P k 0 := by
      funext s
      simp only [blocks, add_zero]
      split_ifs <;> rfl
    rw [this]
    exact pairing_add hM hN hP (hb k 0)
  have e2 : ∀ k ∈ Finset.range (e + 1), chartMixedEnergy M N k = pairing M N (blocks M N P k (e - k)) := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [chartMixedEnergy_eq]
    congr 1
    funext s
    have := s.isLt
    simp only [blocks]
    split_ifs <;> first | rfl | omega
  have e3 : ∀ k ∈ Finset.range (e + 1), chartMixedEnergy N P k = g 0 k := by
    intro k _
    rw [chartMixedEnergy_eq, hg]
    congr 1
    funext s
    simp only [blocks, zero_add]
    split_ifs <;> first | rfl | omega
  have tele : ∀ k ∈ Finset.range (e + 1),
      pairing M N (blocks M N P k 0) - pairing M N (blocks M N P k (e - k)) =
        -∑ j ∈ Finset.range (e - k), (g (k + 1) j - g k (j + 1)) := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [← Finset.sum_range_sub' (fun j => pairing M N (blocks M N P k j)), ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    exact step hS hM hN hP (by omega)
  have hsum : ∑ k ∈ Finset.range (e + 1), (pairing M N (blocks M N P k 0) -
      pairing M N (blocks M N P k (e - k))) = -∑ k ∈ Finset.range (e + 1), (g k 0 - g 0 k) := by
    rw [Finset.sum_congr rfl tele, Finset.sum_neg_distrib, antidiag_telescope]
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_congr rfl e3, Finset.sum_add_distrib]
  simp only [Finset.sum_sub_distrib] at hsum
  linarith

end

end GroundTheory.Heights₂.Heights
