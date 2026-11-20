import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StLemmaEScale
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPsh mInt maMeasure isPotentialAdd
  isPotentialRsmul isPotential_ofFun isPshAdd isPshRsmul maMeasureMono maMeasure_thm mIntegrableCont
  mIntSymm mIntRsmul st_mInt_congr_phi)

/- English proof (translation)
Introduce `x j y hy w`. Rewrite using `[hφ]`. Conclude with `hP x j y ⟨hy.1, hU x hy.2⟩ w`.
-/
theorem isPsh_of_φ_eq {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}
    {P Q : LocPot X} (hP : IsPsh A P) (hU : ∀ x, Q.U x ⊆ P.U x) (hφ : Q.φ = P.φ) : IsPsh A Q := by
  intro x j y hy w
  rw [hφ]
  exact hP x j y ⟨hy.1, hU x hy.2⟩ w

/- English proof (translation)
Take `_ | n` from `e`. Conclude with `j.elim0`. Use `set q := Φ ∘ Equiv.swap 0 j with hq`. Establish `h1 : Function.update Φ j ((Φ j).rsmul c) ∘ Equiv.swap 0 j = Fin.cons ((q 0).rsmul c) (Fin.tail q)`. Use function extensionality and compare the values at `i`.

Use `Fin.cases ?_ (fun i => ?_) i` and prove the remaining obligations. Simplify using `[hq]`. Establish `hne : Equiv.swap 0 j i.succ ≠ j`. Introduce `h`. Rewrite `h` using `[Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]`.

Conclude with `Fin.succ_ne_zero _ h`. Simplify using `only [Function.comp_apply, Fin.cons_succ, Fin.tail, hq, Function.update_of_ne hne]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem mInt_update_rsmul {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (c : ℝ)
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (j : Fin e) (g : X → ℝ) :
    mInt A (Function.update Φ j ((Φ j).rsmul c)) g = c * mInt A Φ g := by
  obtain _ | n := e
  · exact j.elim0
  set q := Φ ∘ Equiv.swap 0 j with hq
  have h1 : Function.update Φ j ((Φ j).rsmul c) ∘ Equiv.swap 0 j =
      Fin.cons ((q 0).rsmul c) (Fin.tail q) := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [hq]
    · have hne : Equiv.swap 0 j i.succ ≠ j := by
        intro h
        rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_right] at h
        exact Fin.succ_ne_zero _ h
      simp only [Function.comp_apply, Fin.cons_succ, Fin.tail, hq, Function.update_of_ne hne]
  calc mInt A (Function.update Φ j ((Φ j).rsmul c)) g
      = mInt A (Function.update Φ j ((Φ j).rsmul c) ∘ Equiv.swap 0 j) g := (mIntSymm A _ _ g).symm
    _ = mInt A (Fin.cons ((q 0).rsmul c) (Fin.tail q)) g := by rw [h1]
    _ = c * mInt A (Fin.cons (q 0) (Fin.tail q)) g :=
        mIntRsmul A c _ _ (hΦ _) (fun i => hΦ _) g
    _ = c * mInt A Φ g := by rw [Fin.cons_self_tail, hq, mIntSymm]

/- English proof (translation)
Establish `key : ∀ k ≤ e, mInt A (fun i : Fin e => if (i : ℕ) < k then (Φ i).rsmul c else Φ i) g = c ^ k * mInt A Φ g`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro _`. Simplify using the standard rewrite rules.

Consider the case `succ k ih`. Introduce `hk`. Use `set Ψ : Fin e → LocPot X := fun i => if (i : ℕ) < k then (Φ i).rsmul c else Φ i with hΨ`. Establish `hΨp : ∀ i, IsPotential A (Ψ i)` using `fun i => by`. Simplify using `only [hΨ]`.

Use `split_ifs`. Conclude with `isPotentialRsmul A c _ (hΦ i)`. Conclude with `hΦ i`. Establish `h : (fun i : Fin e => if (i : ℕ) < k + 1 then (Φ i).rsmul c else Φ i) = Function.update Ψ ⟨k, hk⟩ ((Ψ ⟨k, hk⟩).rsmul c)`. Use function extensionality and compare the values at `i`.

Distinguish the cases in `hi : i = ⟨k, hk⟩`. Substitute `hi` using the available equality. Simplify using `[hΨ]`. Establish `hi' : (i : ℕ) ≠ k` using `fun h => hi (Fin.ext h)`. Rewrite using `[Function.update_of_ne hi, hΨ]`.

Simplify using `only [Nat.lt_succ_iff_lt_or_eq, hi', or_false]`. Rewrite using `[h, mInt_update_rsmul A c Ψ hΨp, ih (Nat.le_of_succ_le hk), pow_succ]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `using key e le_rfl`.
-/
theorem mInt_rsmul_all {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (c : ℝ)
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (g : X → ℝ) :
    mInt A (fun i => (Φ i).rsmul c) g = c ^ e * mInt A Φ g := by
  have key : ∀ k ≤ e, mInt A (fun i : Fin e => if (i : ℕ) < k then (Φ i).rsmul c else Φ i) g =
      c ^ k * mInt A Φ g := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      set Ψ : Fin e → LocPot X := fun i => if (i : ℕ) < k then (Φ i).rsmul c else Φ i with hΨ
      have hΨp : ∀ i, IsPotential A (Ψ i) := fun i => by
        simp only [hΨ]; split_ifs
        · exact isPotentialRsmul A c _ (hΦ i)
        · exact hΦ i
      have h : (fun i : Fin e => if (i : ℕ) < k + 1 then (Φ i).rsmul c else Φ i) =
          Function.update Ψ ⟨k, hk⟩ ((Ψ ⟨k, hk⟩).rsmul c) := by
        funext i
        by_cases hi : i = ⟨k, hk⟩
        · subst hi; simp [hΨ]
        · have hi' : (i : ℕ) ≠ k := fun h => hi (Fin.ext h)
          rw [Function.update_of_ne hi, hΨ]
          simp only [Nat.lt_succ_iff_lt_or_eq, hi', or_false]
      rw [h, mInt_update_rsmul A c Ψ hΨp, ih (Nat.le_of_succ_le hk), pow_succ]
      ring
  simpa using key e le_rfl

/- English proof (translation)
Introduce `D X _ _ _ A Om M v hM hv hpsh`. Set `_ : MeasurableSpace X` to `borel X`. Establish `_ : BorelSpace X` using `⟨rfl⟩`. Establish `hM0 : M ≠ 0` using `by positivity`. Establish `hP : ∀ i, IsPotential A (potForm Om.pot (v i))` using `fun i => isPotentialAdd A _ _ Om.isPot (isPotential_ofFun A _ (hv i))`.

Establish `hW : ∀ i, IsPotential A (potForm Om.pot fun x => v i x / M)` using `fun i => isPotentialAdd A _ _ Om.isPot (isPotential_ofFun A _ fun j => (hv i j).div_const M)`. Establish `hQ` using `isPotentialRsmul A (M - 1) _ Om.isPot`. Establish `hQpsh` using `isPshRsmul A (M - 1) _ (by linarith) Om.isPot Om.isPsh`. Use `⟨fun i => ?_, fun g hg hg0 => ?_⟩` and prove the remaining obligations. Establish `h1` using `isPshRsmul A M⁻¹ _ (by positivity) (hP i) (hpsh i)`.

Establish `h2` using `isPshRsmul A (1 - M⁻¹) _ (by rw [sub_nonneg]; exact inv_le_one_of_one_le₀ hM) Om.isPot Om.isPsh`. Use `isPsh_of_φ_eq (isPshAdd A _ _ (isPotentialRsmul A _ _ (hP i)) (isPotentialRsmul A _ _ Om.isPot) h1 h2) (fun x y hy => ⟨hy, hy.1⟩) ?_` and prove the remaining obligations. Use function extensionality and compare the values at `x y`. Use `show Om.pot.φ x y + v i y / M = M⁻¹ * (Om.pot.φ x y + v i y) + (1 - M⁻¹) * Om.pot.φ x y`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Establish `hmono` using `maMeasureMono A _ (fun _ => Om.pot.rsmul (M - 1)) hP hpsh (fun _ => hQ) (fun _ => hQpsh)`. Establish `hS : ∀ i, IsPotential A (potForm Om.pot (v i) + Om.pot.rsmul (M - 1))` using `fun i => isPotentialAdd A _ _ (hP i) hQ`. Establish `hSpsh : ∀ i, IsPsh A (potForm Om.pot (v i) + Om.pot.rsmul (M - 1))` using `fun i => isPshAdd A _ _ (hP i) hQ (hpsh i) hQpsh`. Take `⟨_, hT'⟩` from `maMeasure_thm A _ hP hpsh`.

Take `⟨_, hS'⟩` from `maMeasure_thm A _ hS hSpsh`. Establish `hgm` using `hg.measurable`. Establish `e1` using `(hT' g hgm).2 (mIntegrableCont A _ hP g hg)`. Establish `e2` using `(hS' g hgm).2 (mIntegrableCont A _ hS g hg)`. Establish `hint` using `(hS' g hgm).1.1 (mIntegrableCont A _ hS g hg)`.

Establish `hle : mInt A (fun i => potForm Om.pot (v i)) g ≤ mInt A (fun i => potForm Om.pot (v i) + Om.pot.rsmul (M - 1)) g`. Rewrite using `[e1, e2]`. Conclude with `integral_mono_measure hmono (Filter.Eventually.of_forall hg0) hint`. Establish `e3 : mInt A (fun i => potForm Om.pot (v i) + Om.pot.rsmul (M - 1)) g = mInt A (fun i => (potForm Om.pot fun x => v i x / M).rsmul M) g`. Use `st_mInt_congr_phi A (fun i => ?_) g` and prove the remaining obligations.

Use function extensionality and compare the values at `x y`. Use `show Om.pot.φ x y + v i y + (M - 1) * Om.pot.φ x y = M * (Om.pot.φ x y + v i y / M)`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite `hle` using `[e3, mInt_rsmul_all A M _ hW]`.

Conclude with `hle`.
-/
theorem LemmaEScale.proof : LemmaEScale.Statement := by
  intro D X _ _ _ A Om M v hM hv hpsh
  let _ : MeasurableSpace X := borel X
  have _ : BorelSpace X := ⟨rfl⟩
  have hM0 : M ≠ 0 := by positivity
  have hP : ∀ i, IsPotential A (potForm Om.pot (v i)) := fun i =>
    isPotentialAdd A _ _ Om.isPot (isPotential_ofFun A _ (hv i))
  have hW : ∀ i, IsPotential A (potForm Om.pot fun x => v i x / M) := fun i =>
    isPotentialAdd A _ _ Om.isPot (isPotential_ofFun A _ fun j => (hv i j).div_const M)
  have hQ := isPotentialRsmul A (M - 1) _ Om.isPot
  have hQpsh := isPshRsmul A (M - 1) _ (by linarith) Om.isPot Om.isPsh
  refine ⟨fun i => ?_, fun g hg hg0 => ?_⟩
  · have h1 := isPshRsmul A M⁻¹ _ (by positivity) (hP i) (hpsh i)
    have h2 := isPshRsmul A (1 - M⁻¹) _ (by rw [sub_nonneg]; exact inv_le_one_of_one_le₀ hM)
      Om.isPot Om.isPsh
    refine isPsh_of_φ_eq (isPshAdd A _ _ (isPotentialRsmul A _ _ (hP i))
      (isPotentialRsmul A _ _ Om.isPot) h1 h2) (fun x y hy => ⟨hy, hy.1⟩) ?_
    funext x y
    show Om.pot.φ x y + v i y / M = M⁻¹ * (Om.pot.φ x y + v i y) + (1 - M⁻¹) * Om.pot.φ x y
    field_simp
    ring
  have hmono := maMeasureMono A _ (fun _ => Om.pot.rsmul (M - 1)) hP hpsh (fun _ => hQ)
    (fun _ => hQpsh)
  have hS : ∀ i, IsPotential A (potForm Om.pot (v i) + Om.pot.rsmul (M - 1)) := fun i =>
    isPotentialAdd A _ _ (hP i) hQ
  have hSpsh : ∀ i, IsPsh A (potForm Om.pot (v i) + Om.pot.rsmul (M - 1)) := fun i =>
    isPshAdd A _ _ (hP i) hQ (hpsh i) hQpsh
  obtain ⟨_, hT'⟩ := maMeasure_thm A _ hP hpsh
  obtain ⟨_, hS'⟩ := maMeasure_thm A _ hS hSpsh
  have hgm := hg.measurable
  have e1 := (hT' g hgm).2 (mIntegrableCont A _ hP g hg)
  have e2 := (hS' g hgm).2 (mIntegrableCont A _ hS g hg)
  have hint := (hS' g hgm).1.1 (mIntegrableCont A _ hS g hg)
  have hle : mInt A (fun i => potForm Om.pot (v i)) g ≤
      mInt A (fun i => potForm Om.pot (v i) + Om.pot.rsmul (M - 1)) g := by
    rw [e1, e2]
    exact integral_mono_measure hmono (Filter.Eventually.of_forall hg0) hint
  have e3 : mInt A (fun i => potForm Om.pot (v i) + Om.pot.rsmul (M - 1)) g =
      mInt A (fun i => (potForm Om.pot fun x => v i x / M).rsmul M) g := by
    refine st_mInt_congr_phi A (fun i => ?_) g
    funext x y
    show Om.pot.φ x y + v i y + (M - 1) * Om.pot.φ x y = M * (Om.pot.φ x y + v i y / M)
    field_simp
    ring
  rw [e3, mInt_rsmul_all A M _ hW] at hle
  exact hle

end GroundTheory.Heights₂.Heights.AnalyticLimit
