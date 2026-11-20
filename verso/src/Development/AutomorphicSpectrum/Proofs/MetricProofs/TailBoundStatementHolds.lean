import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.AnalyticForms.LeviForms.TailBound
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CompChartEventuallyEq

open MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open ReciprocityTheory.AnForm.P.TailBoundAlt

namespace GlobalTheory.CompanionTheory.Ar.Giv

noncomputable section

/- English proof (translation)
Establish `hI : ∀ Ψ : Fin (e + 1) → LocPot X, (∀ i, IsPotential A (Ψ i)) → MIntegrable A Ψ (logNormSec L s)` using `fun Ψ hΨ => logNormIntegrable A L s m W hL hs hsnc Ψ hΨ`. Establish `hvc : Continuous v` using `projLine_continuous_of_smooth A hv`. Establish `hvpot` using `isPotential_ofFun A v hv`. Establish `hadd` using `mIntAdd A P (LocPot.ofFun v) Φ hP hvpot hΦ (logNormSec L s) (hI _ (cons_pot A _ P Φ hP hΦ)) (hI _ (cons_pot A _ _ Φ hvpot hΦ))`. Establish `hpl` using `poincareLelong A L s m W B hL hs hsnc hB v hv Φ hΦ`.

Establish `hW : ∀ k, -(M + 1) * mInt (B k) (fun i => (Φ i).pullback Subtype.val continuous_subtype_val) (fun _ => 1) ≤ mInt (B k) (fun i => (Φ i).pullback Subtype.val continuous_subtype_val) (v ∘ Subtype.val)`. Introduce `k`. Use `haveI : CompactSpace (W k) := isCompact_iff_compactSpace.mp (SimpleNormalCrossingSliceCharts.isClosed_divisorComponent A L s m W hsnc k).isCompact`. Establish `hsm : (B k).Smooth (v ∘ Subtype.val)` using `(pullPsh A (B k) Subtype.val (hB k) L Set.univ v isOpen_univ hL).1 hv`. Conclude with `mInt_lower (B k) _ (fun i => isPotentialPullback A (B k) Subtype.val (hB k) (Φ i) (hΦ i)) (fun i => (pullPsh A (B k) Subtype.val (hB k) (Φ i) Set.univ v isOpen_univ (hΦ i)).2.1 (hΦp i)) _ (projLine_continuous_of_smooth (B k) hsm) (M + 1) (fun y => by`.

Simplify using `only [Function.comp]`. Combine the linear relations using `[(hvb y.1).1])`. Establish `hCLi : mInt A (Fin.cons L Φ) v ≤ C * ((M + 1) * mInt A (Fin.cons P Φ) (fun _ => 1))`. Establish `hPC` using `isPotentialRsmul A C P hP`. Establish `ha` using `mIntAdd A (P.rsmul C) L Φ hPC hL hΦ v (mIntegrableCont A _ (cons_pot A _ _ Φ hPC hΦ) v hvc) (mIntegrableCont A _ (cons_pot A _ _ Φ hL hΦ) v hvc)`.

Establish `hr` using `mIntRsmul A C P Φ hP hΦ v`. Establish `hn` using `mInt_nonpos A (Fin.cons (P.rsmul C + L) Φ) (cons_pot A _ _ Φ (isPotentialAdd A _ _ hPC hL) hΦ) (cons_pot A _ _ Φ hCL hΦp) v hvc (fun y => (hvb y).2)`. Establish `hlo` using `mInt_lower A (Fin.cons P Φ) (cons_pot A _ _ Φ hP hΦ) (cons_pot A _ _ Φ hPp hΦp) v hvc (M + 1) (fun y => by linarith [(hvb y).1])`. Rewrite `hn` using `[ha, hr]`. Use `mul_le_mul_of_nonneg_left hlo hC` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hadd, hpl]`. Establish `hsum : -(M + 1) * ∑ k, (m k : ℝ) * mInt (B k) (fun i => (Φ i).pullback Subtype.val continuous_subtype_val) (fun _ => 1) ≤ ∑ k, (m k : ℝ) * mInt (B k) (fun i => (Φ i).pullback Subtype.val continuous_subtype_val) (v ∘ Subtype.val)`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_le_sum fun k _ => ?_` and prove the remaining obligations.

Establish `hm : (0 : ℝ) ≤ m k` using `Nat.cast_nonneg _`. Use `mul_le_mul_of_nonneg_left (hW k) hm` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem tailEnergyStep {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas (e + 1) X) (L : LocPot X) (s : X → X → ℂ) {n : ℕ} (m : Fin n → ℕ)
    (W : Fin n → Set X) (B : ∀ k, FinHolAtlas e (W k)) (hB : ∀ k, HoloMap (B k) A Subtype.val)
    (hL : IsPotential A L) (hs : IsSection A L s) (hsnc : IsSNC A L s m W)
    (P : LocPot X) (hP : IsPotential A P) (hPp : IsPsh A P) (C : ℝ) (hC : 0 ≤ C)
    (hCL : IsPsh A (P.rsmul C + L))
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (hΦp : ∀ i, IsPsh A (Φ i))
    (v : X → ℝ) (hv : A.Smooth v) (M : ℝ) (hvb : ∀ y, -M - 1 ≤ v y ∧ v y ≤ 0) :
    mInt A (Fin.cons P Φ) (logNormSec L s) - (M + 1) * (∑ k, (m k : ℝ) *
        mInt (B k) (fun i => (Φ i).pullback Subtype.val continuous_subtype_val) (fun _ => 1) +
        C * mInt A (Fin.cons P Φ) (fun _ => 1)) ≤
      mInt A (Fin.cons (P + LocPot.ofFun v) Φ) (logNormSec L s) := by
  have hI : ∀ Ψ : Fin (e + 1) → LocPot X, (∀ i, IsPotential A (Ψ i)) →
      MIntegrable A Ψ (logNormSec L s) := fun Ψ hΨ => logNormIntegrable A L s m W hL hs hsnc Ψ hΨ
  have hvc : Continuous v := projLine_continuous_of_smooth A hv
  have hvpot := isPotential_ofFun A v hv
  have hadd := mIntAdd A P (LocPot.ofFun v) Φ hP hvpot hΦ (logNormSec L s)
    (hI _ (cons_pot A _ P Φ hP hΦ)) (hI _ (cons_pot A _ _ Φ hvpot hΦ))
  have hpl := poincareLelong A L s m W B hL hs hsnc hB v hv Φ hΦ
  have hW : ∀ k, -(M + 1) * mInt (B k) (fun i => (Φ i).pullback Subtype.val continuous_subtype_val)
      (fun _ => 1) ≤ mInt (B k) (fun i => (Φ i).pullback Subtype.val continuous_subtype_val)
      (v ∘ Subtype.val) := by
    intro k
    haveI : CompactSpace (W k) :=
      isCompact_iff_compactSpace.mp (SimpleNormalCrossingSliceCharts.isClosed_divisorComponent A L s m W hsnc k).isCompact
    have hsm : (B k).Smooth (v ∘ Subtype.val) :=
      (pullPsh A (B k) Subtype.val (hB k) L Set.univ v isOpen_univ hL).1 hv
    exact mInt_lower (B k) _ (fun i => isPotentialPullback A (B k) Subtype.val (hB k) (Φ i) (hΦ i))
      (fun i => (pullPsh A (B k) Subtype.val (hB k) (Φ i) Set.univ v isOpen_univ (hΦ i)).2.1 (hΦp i))
      _ (projLine_continuous_of_smooth (B k) hsm) (M + 1) (fun y => by
        simp only [Function.comp]; linarith [(hvb y.1).1])
  have hCLi : mInt A (Fin.cons L Φ) v ≤ C * ((M + 1) * mInt A (Fin.cons P Φ) (fun _ => 1)) := by
    have hPC := isPotentialRsmul A C P hP
    have ha := mIntAdd A (P.rsmul C) L Φ hPC hL hΦ v
      (mIntegrableCont A _ (cons_pot A _ _ Φ hPC hΦ) v hvc)
      (mIntegrableCont A _ (cons_pot A _ _ Φ hL hΦ) v hvc)
    have hr := mIntRsmul A C P Φ hP hΦ v
    have hn := mInt_nonpos A (Fin.cons (P.rsmul C + L) Φ)
      (cons_pot A _ _ Φ (isPotentialAdd A _ _ hPC hL) hΦ) (cons_pot A _ _ Φ hCL hΦp) v hvc
      (fun y => (hvb y).2)
    have hlo := mInt_lower A (Fin.cons P Φ) (cons_pot A _ _ Φ hP hΦ) (cons_pot A _ _ Φ hPp hΦp)
      v hvc (M + 1) (fun y => by linarith [(hvb y).1])
    rw [ha, hr] at hn
    have := mul_le_mul_of_nonneg_left hlo hC
    linarith
  rw [hadd, hpl]
  have hsum : -(M + 1) * ∑ k, (m k : ℝ) * mInt (B k)
      (fun i => (Φ i).pullback Subtype.val continuous_subtype_val) (fun _ => 1) ≤
      ∑ k, (m k : ℝ) * mInt (B k) (fun i => (Φ i).pullback Subtype.val continuous_subtype_val)
        (v ∘ Subtype.val) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    have hm : (0 : ℝ) ≤ m k := Nat.cast_nonneg _
    have := mul_le_mul_of_nonneg_left (hW k) hm
    linarith
  linarith

/- English proof (translation)
Establish `hB0` using `fun k => sncInducedAtlas A L s m W hL hs hsnc k`. Use `choose B hB using hB0`. Establish `hC0` using `fun j => exists_psh_chern_bound A (Θ j) L (hΘ j) (hΘp j) hL`. Use `choose C hC hCL hCL' using hC0`. Set `K : Fin (e + 1) → ℝ` to `fun j => ∑ k, (m k : ℝ) * mInt (B k) (fun i => (Θ (Equiv.swap 0 j i.succ)).pullback Subtype.val continuous_subtype_val) (fun _ => 1) + C j * mInt A Θ (fun _ => 1)`.

Set `Kn : ℕ → ℝ` to `fun t => if h : t < e + 1 then K ⟨t, h⟩ else 0`. Use `⟨∑ t ∈ Finset.range (e + 1), Kn t, fun M v hM hv hvp hvb => ?_⟩` and prove the remaining obligations. Set `G : ℕ → Fin (e + 1) → LocPot X` to `fun t i => if (i : ℕ) < t then Θ i + LocPot.ofFun (v i) else Θ i`. Set `w : ℕ → Fin (e + 1) → X → ℝ` to `fun t i => if (i : ℕ) < t then v i else fun _ => 0`. Establish `hGφ : ∀ t i, (G t i).φ = (Θ i + LocPot.ofFun (w t i)).φ`.

Introduce `t i`. Simplify using `only [G, w]`. Use `split_ifs`. Both sides reduce to the same expression. Use function extensionality and compare the values at `x y`.

Simplify using `[TailBoundAlt.add_φ, LocPot.ofFun]`. Establish `hw : ∀ t i, A.Smooth (w t i)`. Introduce `t i`. Simplify using `only [w]`. Use `split_ifs`.

Conclude with `hv i`. Introduce `j`. Conclude with `contDiffOn_const`. Establish `hGpot : ∀ t i, IsPotential A (G t i)`. Introduce `t i`.

Simplify using `only [G]`. Use `split_ifs`. Conclude with `isPotentialAdd A _ _ (hΘ i) (isPotential_ofFun A _ (hv i))`. Conclude with `hΘ i`. Establish `hGpsh : ∀ t i, IsPsh A (G t i)`.

Introduce `t i`. Simplify using `only [G]`. Use `split_ifs`. Conclude with `hvp i`. Conclude with `isPsh_of_isPosPot A _ (hΘp i)`.

Establish `hmass : ∀ t, mInt A (G t) (fun _ => 1) = mInt A Θ (fun _ => 1)`. Introduce `t`. Rewrite using `[mInt_congr_phi A (G t) (fun i => Θ i + LocPot.ofFun (w t i)) (hGφ t), massIndep A Θ (w t) hΘ (hw t)]`. Establish `hstep : ∀ t (ht : t < e + 1), mInt A (G t) (logNormSec L s) - (M + 1) * Kn t ≤ mInt A (G (t + 1)) (logNormSec L s)`. Introduce `t ht`.

Take `⟨j, hj⟩ : ∃ j : Fin (e + 1), (j : ℕ) = t` from `⟨⟨t, ht⟩, rfl⟩`. Set `Φ : Fin e → LocPot X` to `fun i => G t (Equiv.swap 0 j i.succ)`. Establish `hne : ∀ i : Fin e, ((Equiv.swap 0 j i.succ : Fin (e + 1)) : ℕ) ≠ t`. Introduce `i h`. Establish `h1 : Equiv.swap 0 j i.succ = j` using `Fin.ext (h.trans hj.symm)`.

Rewrite `h1` using `[Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]`. Conclude with `Fin.succ_ne_zero i h1`. Establish `hG1 : G (t + 1) ∘ Equiv.swap 0 j = Fin.cons (Θ j + LocPot.ofFun (v j)) Φ`. Use function extensionality and compare the values at `i`. Proceed by induction on `i using Fin.cases with`.

Consider the case `zero`. Simplify using `only [Function.comp, Equiv.swap_apply_left, Fin.cons_zero, G]`. Rewrite using `[if_pos (by omega)]`. Consider the case `succ i`. Simplify using `only [Function.comp, Fin.cons_succ, Φ, G]`.

Use `hne i` as an intermediate fact. Apply the tactic sequence `split_ifs <;> first | rfl | omega`. Establish `hG0 : G t ∘ Equiv.swap 0 j = Fin.cons (Θ j) Φ`. Use function extensionality and compare the values at `i`. Proceed by induction on `i using Fin.cases with`.

Consider the case `zero`. Simplify using `only [Function.comp, Equiv.swap_apply_left, Fin.cons_zero, G]`. Rewrite using `[if_neg (by omega)]`. Consider the case `succ i => simp only [Function.comp, Fin.cons_succ, Φ]`. Establish `e0 : ∀ g, mInt A (G t) g = mInt A (Fin.cons (Θ j) Φ) g` using `fun g => by`.

Rewrite using `[← hG0, mIntSymm]`. Establish `e1 : mInt A (G (t + 1)) (logNormSec L s) = mInt A (Fin.cons (Θ j + LocPot.ofFun (v j)) Φ) (logNormSec L s)`. Rewrite using `[← hG1, mIntSymm]`. Establish `e3 : ∀ k, mInt (B k) (fun i => (Φ i).pullback Subtype.val continuous_subtype_val) (fun _ => 1) = mInt (B k) (fun i => (Θ (Equiv.swap 0 j i.succ)).pullback Subtype.val continuous_subtype_val) (fun _ => 1)`. Introduce `k`.

Use `haveI : CompactSpace (W k) := isCompact_iff_compactSpace.mp (SimpleNormalCrossingSliceCharts.isClosed_divisorComponent A L s m W hsnc k).isCompact`. Rewrite using `[mInt_congr_phi (B k) _ (fun i => (Θ (Equiv.swap 0 j i.succ)).pullback Subtype.val continuous_subtype_val + LocPot.ofFun (w t (Equiv.swap 0 j i.succ) ∘ Subtype.val)) ?_]`. Conclude with `massIndep (B k) _ _ (fun i => isPotentialPullback A (B k) Subtype.val (hB k) _ (hΘ _)) (fun i => (pullPsh A (B k) Subtype.val (hB k) L Set.univ _ isOpen_univ hL).1 (hw t _))`. Introduce `i`. Use function extensionality and compare the values at `x y`.

Use `show (G t (Equiv.swap 0 j i.succ)).φ x.1 y.1 = _`. Rewrite using `[hGφ]`. Both sides reduce to the same expression. Establish `e4 : mInt A (Fin.cons (Θ j) Φ) (fun _ => 1) = mInt A Θ (fun _ => 1)`. Rewrite using `[← e0, hmass]`.

Establish `hKn : Kn t = K j`. Simplify using `only [Kn, dif_pos ht]`. Use `congr 1`. Conclude with `Fin.ext hj.symm`. Establish `hP` using `tailEnergyStep A L s m W B hB hL hs hsnc (Θ j) (hΘ j) (isPsh_of_isPosPot A _ (hΘp j)) (C j) (hC j) (hCL j) Φ (fun i => hGpot t _) (fun i => hGpsh t _) (v j) (hv j) M (hvb j)`.

Rewrite `hP` using `[Finset.sum_congr rfl (fun k _ => by rw [e3 k]), e4]`. Rewrite using `[e0, e1, hKn]`. Conclude with `hP`. Establish `hall : ∀ t, t ≤ e + 1 → mInt A Θ (logNormSec L s) - (M + 1) * ∑ u ∈ Finset.range t, Kn u ≤ mInt A (G t) (logNormSec L s)`. Introduce `t`.

Proceed by induction on `t with`. Consider the case `zero`. Introduce `_`. Establish `h0 : G 0 = Θ`. Use function extensionality and compare the values at `i`.

Simplify using `[G]`. Simplify using `[h0]`. Consider the case `succ t ih`. Introduce `ht`. Establish `h1` using `hstep t (by omega)`.

Establish `h2` using `ih (by omega)`. Rewrite using `[Finset.sum_range_succ]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hGe : G (e + 1) = fun i => Θ i + LocPot.ofFun (v i)`. Use function extensionality and compare the values at `i`.

Simplify using `[G, i.isLt]`. Use `hall (e + 1) le_rfl` as an intermediate fact. Rewrite `this` using `[hGe]`. Then use the resulting hypothesis.
-/
theorem tailTelescopeSucc {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas (e + 1) X) (Θ : Fin (e + 1) → LocPot X) (L : LocPot X) (s : X → X → ℂ) {n : ℕ}
    (m : Fin n → ℕ) (W : Fin n → Set X) (hΘ : ∀ i, IsPotential A (Θ i))
    (hΘp : ∀ i, IsPosPot A (Θ i)) (hL : IsPotential A L) (hs : IsSection A L s)
    (hsnc : IsSNC A L s m W) :
    ∃ K : ℝ, ∀ (M : ℝ) (v : Fin (e + 1) → X → ℝ), 0 ≤ M → (∀ i, A.Smooth (v i)) →
      (∀ i, IsPsh A (Θ i + LocPot.ofFun (v i))) → (∀ i y, -M - 1 ≤ v i y ∧ v i y ≤ 0) →
        mInt A Θ (logNormSec L s) - (M + 1) * K ≤
          mInt A (fun i => Θ i + LocPot.ofFun (v i)) (logNormSec L s) := by
  classical
  have hB0 := fun k => sncInducedAtlas A L s m W hL hs hsnc k
  choose B hB using hB0
  have hC0 := fun j => exists_psh_chern_bound A (Θ j) L (hΘ j) (hΘp j) hL
  choose C hC hCL hCL' using hC0
  let K : Fin (e + 1) → ℝ := fun j => ∑ k, (m k : ℝ) * mInt (B k)
      (fun i => (Θ (Equiv.swap 0 j i.succ)).pullback Subtype.val continuous_subtype_val) (fun _ => 1) +
      C j * mInt A Θ (fun _ => 1)
  let Kn : ℕ → ℝ := fun t => if h : t < e + 1 then K ⟨t, h⟩ else 0
  refine ⟨∑ t ∈ Finset.range (e + 1), Kn t, fun M v hM hv hvp hvb => ?_⟩
  let G : ℕ → Fin (e + 1) → LocPot X := fun t i =>
    if (i : ℕ) < t then Θ i + LocPot.ofFun (v i) else Θ i
  let w : ℕ → Fin (e + 1) → X → ℝ := fun t i => if (i : ℕ) < t then v i else fun _ => 0
  have hGφ : ∀ t i, (G t i).φ = (Θ i + LocPot.ofFun (w t i)).φ := by
    intro t i
    simp only [G, w]
    split_ifs
    · rfl
    · funext x y
      simp [TailBoundAlt.add_φ, LocPot.ofFun]
  have hw : ∀ t i, A.Smooth (w t i) := by
    intro t i
    simp only [w]
    split_ifs
    · exact hv i
    · intro j
      exact contDiffOn_const
  have hGpot : ∀ t i, IsPotential A (G t i) := by
    intro t i
    simp only [G]
    split_ifs
    · exact isPotentialAdd A _ _ (hΘ i) (isPotential_ofFun A _ (hv i))
    · exact hΘ i
  have hGpsh : ∀ t i, IsPsh A (G t i) := by
    intro t i
    simp only [G]
    split_ifs
    · exact hvp i
    · exact isPsh_of_isPosPot A _ (hΘp i)
  have hmass : ∀ t, mInt A (G t) (fun _ => 1) = mInt A Θ (fun _ => 1) := by
    intro t
    rw [mInt_congr_phi A (G t) (fun i => Θ i + LocPot.ofFun (w t i)) (hGφ t),
      massIndep A Θ (w t) hΘ (hw t)]
  have hstep : ∀ t (ht : t < e + 1), mInt A (G t) (logNormSec L s) - (M + 1) * Kn t ≤
      mInt A (G (t + 1)) (logNormSec L s) := by
    intro t ht
    obtain ⟨j, hj⟩ : ∃ j : Fin (e + 1), (j : ℕ) = t := ⟨⟨t, ht⟩, rfl⟩
    let Φ : Fin e → LocPot X := fun i => G t (Equiv.swap 0 j i.succ)
    have hne : ∀ i : Fin e, ((Equiv.swap 0 j i.succ : Fin (e + 1)) : ℕ) ≠ t := by
      intro i h
      have h1 : Equiv.swap 0 j i.succ = j := Fin.ext (h.trans hj.symm)
      rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_right] at h1
      exact Fin.succ_ne_zero i h1
    have hG1 : G (t + 1) ∘ Equiv.swap 0 j = Fin.cons (Θ j + LocPot.ofFun (v j)) Φ := by
      funext i
      induction i using Fin.cases with
      | zero =>
        simp only [Function.comp, Equiv.swap_apply_left, Fin.cons_zero, G]
        rw [if_pos (by omega)]
      | succ i =>
        simp only [Function.comp, Fin.cons_succ, Φ, G]
        have := hne i
        split_ifs <;> first | rfl | omega
    have hG0 : G t ∘ Equiv.swap 0 j = Fin.cons (Θ j) Φ := by
      funext i
      induction i using Fin.cases with
      | zero =>
        simp only [Function.comp, Equiv.swap_apply_left, Fin.cons_zero, G]
        rw [if_neg (by omega)]
      | succ i => simp only [Function.comp, Fin.cons_succ, Φ]
    have e0 : ∀ g, mInt A (G t) g = mInt A (Fin.cons (Θ j) Φ) g := fun g => by
      rw [← hG0, mIntSymm]
    have e1 : mInt A (G (t + 1)) (logNormSec L s) =
        mInt A (Fin.cons (Θ j + LocPot.ofFun (v j)) Φ) (logNormSec L s) := by
      rw [← hG1, mIntSymm]
    have e3 : ∀ k, mInt (B k) (fun i => (Φ i).pullback Subtype.val continuous_subtype_val)
        (fun _ => 1) = mInt (B k) (fun i => (Θ (Equiv.swap 0 j i.succ)).pullback Subtype.val
          continuous_subtype_val) (fun _ => 1) := by
      intro k
      haveI : CompactSpace (W k) :=
        isCompact_iff_compactSpace.mp (SimpleNormalCrossingSliceCharts.isClosed_divisorComponent A L s m W hsnc k).isCompact
      rw [mInt_congr_phi (B k) _ (fun i => (Θ (Equiv.swap 0 j i.succ)).pullback Subtype.val
        continuous_subtype_val + LocPot.ofFun (w t (Equiv.swap 0 j i.succ) ∘ Subtype.val)) ?_]
      · exact massIndep (B k) _ _
          (fun i => isPotentialPullback A (B k) Subtype.val (hB k) _ (hΘ _))
          (fun i => (pullPsh A (B k) Subtype.val (hB k) L Set.univ _ isOpen_univ hL).1 (hw t _))
      · intro i
        funext x y
        show (G t (Equiv.swap 0 j i.succ)).φ x.1 y.1 = _
        rw [hGφ]
        rfl
    have e4 : mInt A (Fin.cons (Θ j) Φ) (fun _ => 1) = mInt A Θ (fun _ => 1) := by
      rw [← e0, hmass]
    have hKn : Kn t = K j := by
      simp only [Kn, dif_pos ht]
      congr 1
      exact Fin.ext hj.symm
    have hP := tailEnergyStep A L s m W B hB hL hs hsnc (Θ j) (hΘ j) (isPsh_of_isPosPot A _ (hΘp j))
      (C j) (hC j) (hCL j) Φ (fun i => hGpot t _) (fun i => hGpsh t _) (v j) (hv j) M (hvb j)
    rw [Finset.sum_congr rfl (fun k _ => by rw [e3 k]), e4] at hP
    rw [e0, e1, hKn]
    exact hP
  have hall : ∀ t, t ≤ e + 1 → mInt A Θ (logNormSec L s) -
      (M + 1) * ∑ u ∈ Finset.range t, Kn u ≤ mInt A (G t) (logNormSec L s) := by
    intro t
    induction t with
    | zero =>
      intro _
      have h0 : G 0 = Θ := by
        funext i
        simp [G]
      simp [h0]
    | succ t ih =>
      intro ht
      have h1 := hstep t (by omega)
      have h2 := ih (by omega)
      rw [Finset.sum_range_succ]
      linarith
  have hGe : G (e + 1) = fun i => Θ i + LocPot.ofFun (v i) := by
    funext i
    simp [G, i.isLt]
  have := hall (e + 1) le_rfl
  rwa [hGe] at this

/- English proof (translation)
Consider the cases of `e with`. Consider the case `zero`. Use `⟨0, fun M v _ _ _ _ => ?_⟩` and prove the remaining obligations. Establish `h0 : (fun i => Θ i + LocPot.ofFun (v i)) = Θ` using `funext fun i => i.elim0`. Rewrite using `[h0]`.

Simplify using the standard rewrite rules. Consider the case `succ e => exact tailTelescopeSucc A Θ L s m W hΘ hΘp hL hs hsnc`.
-/
theorem tailTelescope {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas e X) (Θ : Fin e → LocPot X) (L : LocPot X) (s : X → X → ℂ) {n : ℕ}
    (m : Fin n → ℕ) (W : Fin n → Set X) (hΘ : ∀ i, IsPotential A (Θ i))
    (hΘp : ∀ i, IsPosPot A (Θ i)) (hL : IsPotential A L) (hs : IsSection A L s)
    (hsnc : IsSNC A L s m W) :
    ∃ K : ℝ, ∀ (M : ℝ) (v : Fin e → X → ℝ), 0 ≤ M → (∀ i, A.Smooth (v i)) →
      (∀ i, IsPsh A (Θ i + LocPot.ofFun (v i))) → (∀ i y, -M - 1 ≤ v i y ∧ v i y ≤ 0) →
        mInt A Θ (logNormSec L s) - (M + 1) * K ≤
          mInt A (fun i => Θ i + LocPot.ofFun (v i)) (logNormSec L s) := by
  cases e with
  | zero =>
    refine ⟨0, fun M v _ _ _ _ => ?_⟩
    have h0 : (fun i => Θ i + LocPot.ofFun (v i)) = Θ := funext fun i => i.elim0
    rw [h0]
    simp
  | succ e => exact tailTelescopeSucc A Θ L s m W hΘ hΘp hL hs hsnc

/- English proof (translation)
Introduce `e X _ _ _ _ _ A Θ L s n m W hΘ hΘp hL hs hsnc hle`. Take `⟨K, hK⟩` from `tailTelescope A Θ L s m W hΘ hΘp hL hs hsnc`. Use `⟨|Real.exp 1 * mInt A Θ (fun _ => 1) - 2 * mInt A Θ (logNormSec L s)| + 2 * |K|, fun M v hM hv hvp hvb => ?_⟩` and prove the remaining obligations. Establish `hvpot : ∀ i, IsPotential A (Θ i + LocPot.ofFun (v i))` using `fun i => isPotentialAdd A _ _ (hΘ i) (isPotential_ofFun A _ (hv i))`. Use `(TailBoundAlt.lintegral_rW_le A _ L s m W hvpot hvp hL hs hsnc hle).trans (ENNReal.ofReal_le_ofReal ?_)` and prove the remaining obligations.

Rewrite using `[massIndep A Θ v hΘ hv]`. Establish `h1` using `hK M v hM hv hvp hvb`. Establish `hb` using `le_abs_self (Real.exp 1 * mInt A Θ (fun _ => 1) - 2 * mInt A Θ (logNormSec L s))`. Establish `hb0` using `abs_nonneg (Real.exp 1 * mInt A Θ (fun _ => 1) - 2 * mInt A Θ (logNormSec L s))`. Establish `h2` using `mul_nonneg hb0 hM`.

Establish `h3` using `mul_le_mul_of_nonneg_left (le_abs_self K) (by linarith : (0 : ℝ) ≤ M + 1)`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem tailEnergyBound : EnergyBoundStatement := by
  intro e X _ _ _ _ _ A Θ L s n m W hΘ hΘp hL hs hsnc hle
  obtain ⟨K, hK⟩ := tailTelescope A Θ L s m W hΘ hΘp hL hs hsnc
  refine ⟨|Real.exp 1 * mInt A Θ (fun _ => 1) - 2 * mInt A Θ (logNormSec L s)| + 2 * |K|,
    fun M v hM hv hvp hvb => ?_⟩
  have hvpot : ∀ i, IsPotential A (Θ i + LocPot.ofFun (v i)) :=
    fun i => isPotentialAdd A _ _ (hΘ i) (isPotential_ofFun A _ (hv i))
  refine (TailBoundAlt.lintegral_rW_le A _ L s m W hvpot hvp hL hs hsnc hle).trans
    (ENNReal.ofReal_le_ofReal ?_)
  rw [massIndep A Θ v hΘ hv]
  have h1 := hK M v hM hv hvp hvb
  have hb := le_abs_self (Real.exp 1 * mInt A Θ (fun _ => 1) - 2 * mInt A Θ (logNormSec L s))
  have hb0 := abs_nonneg (Real.exp 1 * mInt A Θ (fun _ => 1) - 2 * mInt A Θ (logNormSec L s))
  have h2 := mul_nonneg hb0 hM
  have h3 := mul_le_mul_of_nonneg_left (le_abs_self K) (by linarith : (0 : ℝ) ≤ M + 1)
  nlinarith

/- English proof (translation)
Introduce `e X _ _ _ _ _ A Θ L s n m W hΘ hΘp hL hs hsnc hle`. Take `⟨CE, hCE⟩` from `tailEnergyBound A Θ L s m W hΘ hΘp hL hs hsnc hle`. Use `⟨16 * max CE 0, fun C₁ u hC₁ hu hpsh hbd R hR => ?_⟩` and prove the remaining obligations. Establish `hrge : ∀ y, Real.exp 1 ≤ rW L s y` using `rW_ge L s hle`. Take `⟨hrc, hro⟩` from `rW_open A L s hL hs`.

Establish `hbc : IsOpen (bdry s)ᶜ`. Establish `: (bdry s)ᶜ = ⋃ k : ℕ, {y | y ∉ bdry s ∧ rW L s y < k}`. Use extensionality with `y`. Simplify using `only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq]`. Prove the components needed by the constructor for the conclusion.

Introduce `hy`. Take `⟨k, hk⟩` from `exists_nat_gt (rW L s y)`. Conclude with `⟨k, hy, hk⟩`. Introduce and unpack `⟨k, hy, -⟩`. Conclude with `hy`.

Rewrite using `[this]`. Conclude with `isOpen_iUnion fun k => hro k`. Establish `hbm : MeasurableSet (bdry s)` using `(isOpen_compl_iff.1 hbc).measurableSet`. Establish `hrm : Measurable (rW L s)`. Establish `heq : rW L s = (bdry s)ᶜ.piecewise (rW L s) (fun _ => Real.exp 1)`.

Use function extensionality and compare the values at `y`. Distinguish the cases in `hy : y ∈ bdry s`. Establish `hy' : s y y = 0` using `hy`. Simplify using `[Set.piecewise, hy, rW, logNormSec, hy']`. Simplify using `[Set.piecewise, hy]`.

Rewrite using `[heq]`. Conclude with `ContinuousOn.measurable_piecewise hrc continuousOn_const hbm.compl`. Establish `hu0 : ∀ i y, u i y ≤ 0`. Introduce `i y`. Establish `hc : Continuous (u i)` using `projLine_continuous_of_smooth A (hu i)`.

Establish `hd : Dense (bdry s)ᶜ` using `interior_eq_empty_iff_dense_compl.1 (LeviFormBoundaryTopology.interior_bdry_eq_empty hs hsnc)`. Establish `hcl : closure ((bdry s)ᶜ) ⊆ {y | u i y ≤ 0}` using `closure_minimal (fun y hy => (hbd i y hy).2) (isClosed_le hc continuous_const)`. Rewrite `hcl` using `[hd.closure_eq]`. Conclude with `hcl (Set.mem_univ y)`. Establish `hΘpsh : ∀ i, IsPsh A (Θ i)` using `fun i => TailBoundAlt.isPsh_of_isPosPot A _ (hΘp i)`.

Establish `hupot : ∀ i, IsPotential A (Θ i + LocPot.ofFun (u i))` using `fun i => isPotentialAdd A _ _ (hΘ i) (isPotential_ofFun A _ (hu i))`. Use `set μ := maMeasure A (fun i => Θ i + LocPot.ofFun (u i)) with hμ`. Use `haveI : IsFiniteMeasure μ := (maMeasure_thm A _ hupot hpsh).1`. Establish `hK0 : 0 ≤ max CE 0 * (C₁ + 3)` using `mul_nonneg (le_max_right _ _) (by linarith)`. Establish `hfirst : ∀ R' : ℝ, Real.exp 1 ≤ R' → μ (bdry s ∪ {y | R' ≤ rW L s y}) ≤ ENNReal.ofReal (max CE 0 * (C₁ + 3) * Real.log R' / R')`.

Introduce `R' hR'`. Establish `hR0 : 0 < R'` using `lt_of_lt_of_le (Real.exp_pos 1) hR'`. Establish `hlogR : 1 ≤ Real.log R'`. Rewrite using `[← Real.log_exp 1]`. Conclude with `Real.log_le_log (Real.exp_pos 1) hR'`.

Use `set M := C₁ * Real.log R' + 2 with hMdef`. Establish `hM : 0 ≤ M` using `by positivity`. Establish `hcut` using `fun i => cutoff A (Θ i) (u i) M (hΘ i) (hΘpsh i) (hu i) (hpsh i) (hu0 i) hM`. Use `set v : Fin e → X → ℝ := fun i y => ReciprocityTheory.AnForm.A.regMax 1 ![u i y, -M] - 1 / 2 with hv`. Establish `hvs : ∀ i, A.Smooth (v i)` using `fun i => (hcut i).1`.

Establish `hvpsh : ∀ i, IsPsh A (Θ i + LocPot.ofFun (v i))` using `fun i => (hcut i).2.1`. Establish `hvb : ∀ i y, -M - 1 ≤ v i y ∧ v i y ≤ 0` using `fun i => (hcut i).2.2.1`. Establish `hveq : ∀ i y, -M + 1 ≤ u i y → v i y = u i y - 1 / 2` using `fun i => (hcut i).2.2.2`. Establish `hvpot : ∀ i, IsPotential A (Θ i + LocPot.ofFun (v i))` using `fun i => isPotentialAdd A _ _ (hΘ i) (isPotential_ofFun A _ (hvs i))`. Use `set μR := maMeasure A (fun i => Θ i + LocPot.ofFun (v i)) with hμR`.

Use `haveI : IsFiniteMeasure μR := (maMeasure_thm A _ hvpot hvpsh).1`. Use `set V := {y | y ∉ bdry s ∧ rW L s y < R'} with hV`. Establish `hagree : μ.restrict V = μR.restrict V`. Use `maMeasure_congr_open A Θ u v V (hro R') fun i => ⟨-1 / 2, fun y hy => ?_⟩` and prove the remaining obligations. Establish `hr` using `hrge y`.

Establish `hlog : Real.log (rW L s y) ≤ Real.log R'` using `Real.log_le_log (lt_of_lt_of_le (Real.exp_pos 1) hr) hy.2.le`. Establish `h1` using `(hbd i y hy.1).1`. Establish `: -M + 1 ≤ u i y` using `by nlinarith`. Rewrite using `[hveq i y this]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hmass : μ Set.univ = μR Set.univ`. Establish `key : ∀ (w : Fin e → X → ℝ), (∀ i, A.Smooth (w i)) → (∀ i, IsPsh A (Θ i + LocPot.ofFun (w i))) → (maMeasure A (fun i => Θ i + LocPot.ofFun (w i)) Set.univ).toReal = mInt A Θ (fun _ => 1)`. Introduce `w hws hwp`. Establish `hwpot : ∀ i, IsPotential A (Θ i + LocPot.ofFun (w i))` using `fun i => isPotentialAdd A _ _ (hΘ i) (isPotential_ofFun A _ (hws i))`. Take `⟨hfin, hint⟩` from `maMeasure_thm A _ hwpot hwp`.

Establish `h1` using `hint (fun _ => 1) measurable_const`. Establish `hI : MIntegrable A (fun i => Θ i + LocPot.ofFun (w i)) (fun _ => 1)` using `h1.1.2 (integrable_const _)`. Rewrite using `[← massIndep A Θ w hΘ hws, h1.2 hI, integral_const, smul_eq_mul, mul_one]`. Both sides reduce to the same expression. Rewrite using `[← ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _), key u hu hpsh, key v hvs hvpsh]`.

Establish `htr` using `tail_transfer μ μR V (hro R') hagree hmass`. Establish `hVc : Vᶜ = bdry s ∪ {y | R' ≤ rW L s y}`. Use extensionality with `y`. Simplify using `only [hV, Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_union, not_and_or, not_not, not_lt]`. Establish `hnull : μR (bdry s) = 0` using `bdry_null A L s m W hL hs hsnc _ hvpot`.

Use `set T := (bdry s)ᶜ ∩ {y | R' ≤ rW L s y} with hT`. Establish `hTm : MeasurableSet T` using `hbm.compl.inter (measurableSet_le measurable_const hrm)`. Establish `hmark : ENNReal.ofReal R' * μR T ≤ ENNReal.ofReal (CE * (M + 1))`. Combine the equalities or inequalities in the displayed calculation. Establish `hCM : CE * (M + 1) ≤ max CE 0 * (C₁ + 3) * Real.log R'`.

Establish `h1 : CE * (M + 1) ≤ max CE 0 * (M + 1)` using `mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)`. Establish `h2 : M + 1 ≤ (C₁ + 3) * Real.log R'`. Rewrite using `[hMdef]`. Use the polynomial consequences of the given equalities and inequalities. Establish `h3` using `mul_le_mul_of_nonneg_left h2 (le_max_right CE 0)`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hT' : μR T ≤ ENNReal.ofReal (max CE 0 * (C₁ + 3) * Real.log R' / R')`. Rewrite using `[ENNReal.ofReal_div_of_pos hR0, ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hR0)) (Or.inl ENNReal.ofReal_ne_top), mul_comm]`. Conclude with `hmark.trans (ENNReal.ofReal_le_ofReal hCM)`. Rewrite using `[← hVc, htr, hVc]`.

Combine the equalities or inequalities in the displayed calculation. Apply `measure_mono` to reduce the goal to its premises. Introduce `y hy`. Distinguish the cases in `hb : y ∈ bdry s`. Conclude with `Or.inl hb`.

Conclude with `Or.inr ⟨hb, hy.resolve_left hb⟩`. Use `_ ≤ μR (bdry s) + μR T := measure_union_le _ _`. Use `_ ≤ _ := by rw [hnull, zero_add]; exact hT'`. Use `⟨(hfirst R hR).trans (ENNReal.ofReal_le_ofReal ?_), ?_⟩` and prove the remaining obligations. Establish `hR0 : 0 < R` using `lt_of_lt_of_le (Real.exp_pos 1) hR`.

Establish `hlogR : 0 ≤ Real.log R` using `Real.log_nonneg (by linarith [Real.add_one_le_exp (1 : ℝ)])`. Establish `: max CE 0 * (C₁ + 3) * Real.log R / R ≤ 16 * (max CE 0 * (C₁ + 3) * Real.log R / R)`. Establish `: 0 ≤ max CE 0 * (C₁ + 3) * Real.log R / R` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation.

Establish `hsh` using `tail_shells (μ.restrict (bdry s)ᶜ) (rW L s) (max CE 0 * (C₁ + 3)) hrm hK0 (fun R' hR' => by`. Rewrite using `[Measure.restrict_apply (measurableSet_le measurable_const hrm)]`. Use `(measure_mono ?_).trans (hfirst R' hR')` and prove the remaining obligations. Introduce `y hy`. Conclude with `Or.inr hy.1) R hR`.

Rewrite `hsh` using `[Measure.restrict_restrict (measurableSet_le measurable_const hrm), Set.inter_comm]`. Use `hsh.trans (le_of_eq ?_)` and prove the remaining obligations. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tailBound_holds : TailBoundStatement := by
  intro e X _ _ _ _ _ A Θ L s n m W hΘ hΘp hL hs hsnc hle
  classical
  obtain ⟨CE, hCE⟩ := tailEnergyBound A Θ L s m W hΘ hΘp hL hs hsnc hle
  refine ⟨16 * max CE 0, fun C₁ u hC₁ hu hpsh hbd R hR => ?_⟩
  have hrge : ∀ y, Real.exp 1 ≤ rW L s y := rW_ge L s hle
  obtain ⟨hrc, hro⟩ := rW_open A L s hL hs
  have hbc : IsOpen (bdry s)ᶜ := by
    have : (bdry s)ᶜ = ⋃ k : ℕ, {y | y ∉ bdry s ∧ rW L s y < k} := by
      ext y
      simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq]
      constructor
      · intro hy
        obtain ⟨k, hk⟩ := exists_nat_gt (rW L s y)
        exact ⟨k, hy, hk⟩
      · rintro ⟨k, hy, -⟩
        exact hy
    rw [this]
    exact isOpen_iUnion fun k => hro k
  have hbm : MeasurableSet (bdry s) := (isOpen_compl_iff.1 hbc).measurableSet
  have hrm : Measurable (rW L s) := by
    have heq : rW L s = (bdry s)ᶜ.piecewise (rW L s) (fun _ => Real.exp 1) := by
      funext y
      by_cases hy : y ∈ bdry s
      · have hy' : s y y = 0 := hy
        simp [Set.piecewise, hy, rW, logNormSec, hy']
      · simp [Set.piecewise, hy]
    rw [heq]
    exact ContinuousOn.measurable_piecewise hrc continuousOn_const hbm.compl
  have hu0 : ∀ i y, u i y ≤ 0 := by
    intro i y
    have hc : Continuous (u i) := projLine_continuous_of_smooth A (hu i)
    have hd : Dense (bdry s)ᶜ := interior_eq_empty_iff_dense_compl.1 (LeviFormBoundaryTopology.interior_bdry_eq_empty hs hsnc)
    have hcl : closure ((bdry s)ᶜ) ⊆ {y | u i y ≤ 0} :=
      closure_minimal (fun y hy => (hbd i y hy).2) (isClosed_le hc continuous_const)
    rw [hd.closure_eq] at hcl
    exact hcl (Set.mem_univ y)
  have hΘpsh : ∀ i, IsPsh A (Θ i) := fun i => TailBoundAlt.isPsh_of_isPosPot A _ (hΘp i)
  have hupot : ∀ i, IsPotential A (Θ i + LocPot.ofFun (u i)) :=
    fun i => isPotentialAdd A _ _ (hΘ i) (isPotential_ofFun A _ (hu i))
  set μ := maMeasure A (fun i => Θ i + LocPot.ofFun (u i)) with hμ
  haveI : IsFiniteMeasure μ := (maMeasure_thm A _ hupot hpsh).1
  have hK0 : 0 ≤ max CE 0 * (C₁ + 3) := mul_nonneg (le_max_right _ _) (by linarith)

  have hfirst : ∀ R' : ℝ, Real.exp 1 ≤ R' → μ (bdry s ∪ {y | R' ≤ rW L s y}) ≤
      ENNReal.ofReal (max CE 0 * (C₁ + 3) * Real.log R' / R') := by
    intro R' hR'
    have hR0 : 0 < R' := lt_of_lt_of_le (Real.exp_pos 1) hR'
    have hlogR : 1 ≤ Real.log R' := by
      rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hR'
    set M := C₁ * Real.log R' + 2 with hMdef
    have hM : 0 ≤ M := by positivity
    have hcut := fun i => cutoff A (Θ i) (u i) M (hΘ i) (hΘpsh i) (hu i) (hpsh i) (hu0 i) hM
    set v : Fin e → X → ℝ := fun i y => ReciprocityTheory.AnForm.A.regMax 1 ![u i y, -M] - 1 / 2 with hv
    have hvs : ∀ i, A.Smooth (v i) := fun i => (hcut i).1
    have hvpsh : ∀ i, IsPsh A (Θ i + LocPot.ofFun (v i)) := fun i => (hcut i).2.1
    have hvb : ∀ i y, -M - 1 ≤ v i y ∧ v i y ≤ 0 := fun i => (hcut i).2.2.1
    have hveq : ∀ i y, -M + 1 ≤ u i y → v i y = u i y - 1 / 2 := fun i => (hcut i).2.2.2
    have hvpot : ∀ i, IsPotential A (Θ i + LocPot.ofFun (v i)) :=
      fun i => isPotentialAdd A _ _ (hΘ i) (isPotential_ofFun A _ (hvs i))
    set μR := maMeasure A (fun i => Θ i + LocPot.ofFun (v i)) with hμR
    haveI : IsFiniteMeasure μR := (maMeasure_thm A _ hvpot hvpsh).1
    set V := {y | y ∉ bdry s ∧ rW L s y < R'} with hV
    have hagree : μ.restrict V = μR.restrict V := by
      refine maMeasure_congr_open A Θ u v V (hro R') fun i => ⟨-1 / 2, fun y hy => ?_⟩
      have hr := hrge y
      have hlog : Real.log (rW L s y) ≤ Real.log R' :=
        Real.log_le_log (lt_of_lt_of_le (Real.exp_pos 1) hr) hy.2.le
      have h1 := (hbd i y hy.1).1
      have : -M + 1 ≤ u i y := by nlinarith
      rw [hveq i y this]; ring
    have hmass : μ Set.univ = μR Set.univ := by
      have key : ∀ (w : Fin e → X → ℝ), (∀ i, A.Smooth (w i)) →
          (∀ i, IsPsh A (Θ i + LocPot.ofFun (w i))) →
          (maMeasure A (fun i => Θ i + LocPot.ofFun (w i)) Set.univ).toReal =
            mInt A Θ (fun _ => 1) := by
        intro w hws hwp
        have hwpot : ∀ i, IsPotential A (Θ i + LocPot.ofFun (w i)) :=
          fun i => isPotentialAdd A _ _ (hΘ i) (isPotential_ofFun A _ (hws i))
        obtain ⟨hfin, hint⟩ := maMeasure_thm A _ hwpot hwp
        have h1 := hint (fun _ => 1) measurable_const
        have hI : MIntegrable A (fun i => Θ i + LocPot.ofFun (w i)) (fun _ => 1) :=
          h1.1.2 (integrable_const _)
        rw [← massIndep A Θ w hΘ hws, h1.2 hI, integral_const, smul_eq_mul, mul_one]
        rfl
      rw [← ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _),
        key u hu hpsh, key v hvs hvpsh]
    have htr := tail_transfer μ μR V (hro R') hagree hmass
    have hVc : Vᶜ = bdry s ∪ {y | R' ≤ rW L s y} := by
      ext y
      simp only [hV, Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_union, not_and_or, not_not,
        not_lt]
    have hnull : μR (bdry s) = 0 := bdry_null A L s m W hL hs hsnc _ hvpot
    set T := (bdry s)ᶜ ∩ {y | R' ≤ rW L s y} with hT
    have hTm : MeasurableSet T := hbm.compl.inter (measurableSet_le measurable_const hrm)
    have hmark : ENNReal.ofReal R' * μR T ≤ ENNReal.ofReal (CE * (M + 1)) := by
      calc ENNReal.ofReal R' * μR T = ∫⁻ _ in T, ENNReal.ofReal R' ∂μR := (setLIntegral_const _ _).symm
        _ ≤ ∫⁻ y in T, ENNReal.ofReal (rW L s y) ∂μR :=
            lintegral_mono_ae ((ae_restrict_iff' hTm).2 (Filter.Eventually.of_forall
              fun y hy => ENNReal.ofReal_le_ofReal hy.2))
        _ ≤ ∫⁻ y in (bdry s)ᶜ, ENNReal.ofReal (rW L s y) ∂μR :=
            lintegral_mono_set Set.inter_subset_left
        _ ≤ _ := hCE M v hM hvs hvpsh hvb
    have hCM : CE * (M + 1) ≤ max CE 0 * (C₁ + 3) * Real.log R' := by
      have h1 : CE * (M + 1) ≤ max CE 0 * (M + 1) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
      have h2 : M + 1 ≤ (C₁ + 3) * Real.log R' := by
        rw [hMdef]; nlinarith
      have h3 := mul_le_mul_of_nonneg_left h2 (le_max_right CE 0)
      linarith
    have hT' : μR T ≤ ENNReal.ofReal (max CE 0 * (C₁ + 3) * Real.log R' / R') := by
      rw [ENNReal.ofReal_div_of_pos hR0, ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hR0))
        (Or.inl ENNReal.ofReal_ne_top), mul_comm]
      exact hmark.trans (ENNReal.ofReal_le_ofReal hCM)
    rw [← hVc, htr, hVc]
    calc μR (bdry s ∪ {y | R' ≤ rW L s y}) ≤ μR (bdry s ∪ T) := by
          apply measure_mono
          intro y hy
          by_cases hb : y ∈ bdry s
          · exact Or.inl hb
          · exact Or.inr ⟨hb, hy.resolve_left hb⟩
      _ ≤ μR (bdry s) + μR T := measure_union_le _ _
      _ ≤ _ := by rw [hnull, zero_add]; exact hT'
  refine ⟨(hfirst R hR).trans (ENNReal.ofReal_le_ofReal ?_), ?_⟩
  · have hR0 : 0 < R := lt_of_lt_of_le (Real.exp_pos 1) hR
    have hlogR : 0 ≤ Real.log R := Real.log_nonneg (by linarith [Real.add_one_le_exp (1 : ℝ)])
    have : max CE 0 * (C₁ + 3) * Real.log R / R ≤ 16 * (max CE 0 * (C₁ + 3) * Real.log R / R) := by
      have : 0 ≤ max CE 0 * (C₁ + 3) * Real.log R / R := by positivity
      linarith
    calc _ ≤ _ := this
      _ = _ := by ring
  · have hsh := tail_shells (μ.restrict (bdry s)ᶜ) (rW L s) (max CE 0 * (C₁ + 3)) hrm hK0
      (fun R' hR' => by
        rw [Measure.restrict_apply (measurableSet_le measurable_const hrm)]
        refine (measure_mono ?_).trans (hfirst R' hR')
        intro y hy
        exact Or.inr hy.1) R hR
    rw [Measure.restrict_restrict (measurableSet_le measurable_const hrm), Set.inter_comm] at hsh
    refine hsh.trans (le_of_eq ?_)
    congr 1
    ring

end

end GlobalTheory.CompanionTheory.Ar.Giv
