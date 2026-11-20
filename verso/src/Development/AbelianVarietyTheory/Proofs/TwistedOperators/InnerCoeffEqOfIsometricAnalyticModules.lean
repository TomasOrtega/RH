import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

namespace GlobalTheory.AnalyticVec

/- English proof (translation)
Establish `hd : ∀ w s, HasDerivAt (fun r : ℝ => U r (ι w)) (U s (ι (a w))) s`. Introduce `w s`. Establish `e : (fun r : ℝ => U r (ι w)) = fun r => U s (U (r - s) (ι w))`. Use function extensionality and compare the values at `r`. Establish `hr : r = s + (r - s)` using `by ring`.

Use `conv_lhs => rw [hr]`. Rewrite using `[hadd, ContinuousLinearMap.mul_apply]`. Rewrite using `[e]`. Establish `hs : HasDerivAt (fun r : ℝ => r - s) 1 s` using `(hasDerivAt_id s).sub_const s`. Establish `hz : HasDerivAt (fun r : ℝ => U r (ι w)) (ι (a w)) ((fun r : ℝ => r - s) s)`.

Simplify using `using hder w`. Establish `h2 : HasDerivAt ((fun r : ℝ => U r (ι w)) ∘ (fun r : ℝ => r - s)) ((1 : ℝ) • ι (a w)) s` using `HasDerivAt.scomp s hz hs`. Rewrite `h2` using `[one_smul]`. Conclude with `(U s).hasFDerivAt.comp_hasDerivAt s h2`. Establish `hit : ∀ n w, deriv^[n] (fun r : ℝ => L (U r (ι w))) = fun r => L (U r (ι (a^[n] w)))`.

Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro w`. Both sides reduce to the same expression. Consider the case `succ n ih`.

Introduce `w`. Rewrite using `[Function.iterate_succ_apply]`. Establish `hD : deriv (fun r : ℝ => L (U r (ι w))) = fun r => L (U r (ι (a w)))`. Use function extensionality and compare the values at `r`. Conclude with `(L.hasFDerivAt.comp_hasDerivAt r (hd w r)).deriv`.

Rewrite using `[hD, ih (a w), Function.iterate_succ_apply]`. Establish `hf : AnalyticOnNhd ℝ (fun r : ℝ => L (U r (ι v))) Set.univ` using `fun r _ => (L.analyticAt _).comp (han v r (Set.mem_univ r))`. Take `⟨p, hp⟩` from `hf 0 (Set.mem_univ 0)`. Establish `hc : ∀ n, p.coeff n = 0`. Introduce `n`.

Take `⟨ρ, hpr⟩` from `hp`. Establish `h1` using `hpr.factorial_smul 1 n`. Rewrite `h1` using `[← iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iterate, hit n v]`. Simplify using `only at h1`. Rewrite `h1` using `[h0, ContinuousLinearMap.one_apply, hL]`.

Establish `h2 : ((n.factorial : ℝ)) • p.coeff n = 0`. Rewrite using `[Nat.cast_smul_eq_nsmul ℝ]`. Conclude with `h1`. Conclude with `(smul_eq_zero.mp h2).resolve_left (by exact_mod_cast n.factorial_ne_zero)`. Establish `hp0 : p = 0`.

Use extensionality with `n y`. Rewrite using `[p.apply_eq_prod_smul_coeff, hc n, smul_zero]`. Both sides reduce to the same expression. Rewrite `hp` using `[hp0]`. Establish `hev : (fun r : ℝ => L (U r (ι v))) =ᶠ[nhds 0] 0` using `HasFPowerSeriesAt.eventually_eq_zero hp`.

Use `hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ 0) hev (Set.mem_univ t)` as an intermediate fact. Simplify using `using this`.
-/
theorem map_flow_eq_zero {V E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (ι : V → E) (a : V → V) (U : ℝ → E →L[ℝ] E) (h0 : U 0 = 1) (hadd : ∀ s t, U (s + t) = U s * U t)
    (hder : ∀ v, HasDerivAt (fun t : ℝ => U t (ι v)) (ι (a v)) 0)
    (han : ∀ v, AnalyticOnNhd ℝ (fun t : ℝ => U t (ι v)) Set.univ)
    (L : E →L[ℝ] F) (hL : ∀ v, L (ι v) = 0) (v : V) (t : ℝ) : L (U t (ι v)) = 0 := by
  have hd : ∀ w s, HasDerivAt (fun r : ℝ => U r (ι w)) (U s (ι (a w))) s := by
    intro w s
    have e : (fun r : ℝ => U r (ι w)) = fun r => U s (U (r - s) (ι w)) := by
      funext r
      have hr : r = s + (r - s) := by ring
      conv_lhs => rw [hr]
      rw [hadd, ContinuousLinearMap.mul_apply]
    rw [e]
    have hs : HasDerivAt (fun r : ℝ => r - s) 1 s := (hasDerivAt_id s).sub_const s
    have hz : HasDerivAt (fun r : ℝ => U r (ι w)) (ι (a w)) ((fun r : ℝ => r - s) s) := by
      simpa using hder w
    have h2 : HasDerivAt ((fun r : ℝ => U r (ι w)) ∘ (fun r : ℝ => r - s)) ((1 : ℝ) • ι (a w)) s :=
      HasDerivAt.scomp s hz hs
    rw [one_smul] at h2
    exact (U s).hasFDerivAt.comp_hasDerivAt s h2
  have hit : ∀ n w, deriv^[n] (fun r : ℝ => L (U r (ι w))) = fun r => L (U r (ι (a^[n] w))) := by
    intro n
    induction n with
    | zero => intro w; rfl
    | succ n ih =>
      intro w
      rw [Function.iterate_succ_apply]
      have hD : deriv (fun r : ℝ => L (U r (ι w))) = fun r => L (U r (ι (a w))) := by
        funext r
        exact (L.hasFDerivAt.comp_hasDerivAt r (hd w r)).deriv
      rw [hD, ih (a w), Function.iterate_succ_apply]
  have hf : AnalyticOnNhd ℝ (fun r : ℝ => L (U r (ι v))) Set.univ :=
    fun r _ => (L.analyticAt _).comp (han v r (Set.mem_univ r))
  obtain ⟨p, hp⟩ := hf 0 (Set.mem_univ 0)
  have hc : ∀ n, p.coeff n = 0 := by
    intro n
    obtain ⟨ρ, hpr⟩ := hp
    have h1 := hpr.factorial_smul 1 n
    rw [← iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iterate, hit n v] at h1
    dsimp only at h1
    rw [h0, ContinuousLinearMap.one_apply, hL] at h1
    have h2 : ((n.factorial : ℝ)) • p.coeff n = 0 := by
      rw [Nat.cast_smul_eq_nsmul ℝ]
      exact h1
    exact (smul_eq_zero.mp h2).resolve_left (by exact_mod_cast n.factorial_ne_zero)
  have hp0 : p = 0 := by
    ext n y
    rw [p.apply_eq_prod_smul_coeff, hc n, smul_zero]
    rfl
  rw [hp0] at hp
  have hev : (fun r : ℝ => L (U r (ι v))) =ᶠ[nhds 0] 0 := HasFPowerSeriesAt.eventually_eq_zero hp
  have := hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ 0) hev
    (Set.mem_univ t)
  simpa using this

/- English proof (translation)
Introduce `x y`. Set `U : ℝ → (π₁.H × π₂.H) →L[ℝ] (π₁.H × π₂.H)` to `fun s => ((π₁.π (T.expt (s • Y))).restrictScalars ℝ).prodMap ((π₂.π (T.expt (s • Y))).restrictScalars ℝ)`. Set `L : (π₁.H × π₂.H) →L[ℝ] ℂ` to `(((innerSL ℂ (j₁ x)).comp (π₁.π h)).restrictScalars ℝ).comp (ContinuousLinearMap.fst ℝ _ _) - (((innerSL ℂ (j₂ x)).comp (π₂.π h)).restrictScalars ℝ).comp (ContinuousLinearMap.snd ℝ _ _)`. Establish `key` using `map_flow_eq_zero (fun v => (j₁ v, j₂ v)) (M.act Y) U ?_ ?_ ?_ ?_ L ?_ y t`. Establish `e : L (U t (j₁ y, j₂ y)) = inner ℂ (j₁ x) (π₁.π (h * T.expt (t • Y)) (j₁ y)) - inner ℂ (j₂ x) (π₂.π (h * T.expt (t • Y)) (j₂ y))`.

Simplify using `[L, U, map_mul]`. Rewrite `key` using `[e, sub_eq_zero]`. Conclude with `key`. Use `ContinuousLinearMap.ext fun z => ?_` and prove the remaining obligations. Simplify using `[U, T.expt_zero]`.

Introduce `s r`. Use `ContinuousLinearMap.ext fun z => ?_` and prove the remaining obligations. Simplify using `[U, T.expt_add Y hY, map_mul]`. Both sides reduce to the same expression. Introduce `v`.

Conclude with `(hd1 v).prodMk (hd2 v)`. Introduce `v`. Conclude with `(ha1 v).prod (ha2 v)`. Introduce `v`. Simplify using `[L, hh]`.
-/
private theorem eventually_abs_le_half_add_of_doubling_bounds {p q : ℕ} (T : GrpData p q) (π₁ π₂ : URep T) (M : GKMod p q)
    (j₁ : M.V →ₗ[ℂ] π₁.H) (j₂ : M.V →ₗ[ℂ] π₂.H) (Y : Mat p q) (hY : Y ∈ upq p q)
    (hd1 : ∀ x, HasDerivAt (fun t : ℝ => π₁.π (T.expt (t • Y)) (j₁ x)) (j₁ (M.act Y x)) 0)
    (hd2 : ∀ x, HasDerivAt (fun t : ℝ => π₂.π (T.expt (t • Y)) (j₂ x)) (j₂ (M.act Y x)) 0)
    (ha1 : ∀ x, AnalyticOnNhd ℝ (fun t : ℝ => π₁.π (T.expt (t • Y)) (j₁ x)) Set.univ)
    (ha2 : ∀ x, AnalyticOnNhd ℝ (fun t : ℝ => π₂.π (T.expt (t • Y)) (j₂ x)) Set.univ)
    (h : T.G) (hh : ∀ x y, inner ℂ (j₁ x) (π₁.π h (j₁ y)) = inner ℂ (j₂ x) (π₂.π h (j₂ y)))
    (t : ℝ) : ∀ x y, inner ℂ (j₁ x) (π₁.π (h * T.expt (t • Y)) (j₁ y)) =
      inner ℂ (j₂ x) (π₂.π (h * T.expt (t • Y)) (j₂ y)) := by
  intro x y
  let U : ℝ → (π₁.H × π₂.H) →L[ℝ] (π₁.H × π₂.H) := fun s =>
    ((π₁.π (T.expt (s • Y))).restrictScalars ℝ).prodMap ((π₂.π (T.expt (s • Y))).restrictScalars ℝ)
  let L : (π₁.H × π₂.H) →L[ℝ] ℂ :=
    (((innerSL ℂ (j₁ x)).comp (π₁.π h)).restrictScalars ℝ).comp (ContinuousLinearMap.fst ℝ _ _) -
    (((innerSL ℂ (j₂ x)).comp (π₂.π h)).restrictScalars ℝ).comp (ContinuousLinearMap.snd ℝ _ _)
  have key := map_flow_eq_zero (fun v => (j₁ v, j₂ v)) (M.act Y) U ?_ ?_ ?_ ?_ L ?_ y t
  · have e : L (U t (j₁ y, j₂ y)) = inner ℂ (j₁ x) (π₁.π (h * T.expt (t • Y)) (j₁ y)) -
        inner ℂ (j₂ x) (π₂.π (h * T.expt (t • Y)) (j₂ y)) := by
      simp [L, U, map_mul]
    rw [e, sub_eq_zero] at key
    exact key
  · refine ContinuousLinearMap.ext fun z => ?_
    simp [U, T.expt_zero]
  · intro s r
    refine ContinuousLinearMap.ext fun z => ?_
    simp [U, T.expt_add Y hY, map_mul]
    rfl
  · intro v
    exact (hd1 v).prodMk (hd2 v)
  · intro v
    exact (ha1 v).prod (ha2 v)
  · intro v
    simp [L, hh]

/- English proof (translation)
Introduce `p q T hT π₁ π₂ M j₁ j₂ hd1 hd2 ha1 ha2 hiso`. Set `Q : T.G → Prop` to `fun h => ∀ x y, inner ℂ (j₁ x) (π₁.π h (j₁ y)) = inner ℂ (j₂ x) (π₂.π h (j₂ y))`. Set `S : Subgroup T.G` to `{ carrier := {g | ∀ h, Q h ↔ Q (h * g)} mul_mem' := fun {a b} ha hb h => (ha h).trans (by rw [hb (h * a), mul_assoc]) one_mem' := fun h => by rw [mul_one] inv_mem' := fun {g} hg h => by`. Establish `e` using `hg (h * g⁻¹)`. Rewrite `e` using `[inv_mul_cancel_right]`.

Conclude with `e.symm }`. Establish `hle : Subgroup.closure (T.expt '' upq p q) ≤ S`. Rewrite using `[Subgroup.closure_le]`. Introduce and unpack `_ ⟨Y, hY, rfl⟩ h`. Establish `e : T.expt Y * T.expt ((-1 : ℝ) • Y) = 1`.

Establish `e1` using `T.expt_add Y hY 1 (-1)`. Rewrite `e1` using `[one_smul, show (1 : ℝ) + -1 = 0 by norm_num, zero_smul, T.expt_zero]`. Conclude with `e1.symm`. Prove the components needed by the constructor for the conclusion. Introduce `hh`.

Establish `h2` using `eventually_abs_le_half_add_of_doubling_bounds T π₁ π₂ M j₁ j₂ Y hY (hd1 Y hY) (hd2 Y hY) (ha1 Y hY) (ha2 Y hY) h hh 1`. Rewrite `h2` using `[one_smul]`. Conclude with `h2`. Introduce `hh`. Establish `h2` using `eventually_abs_le_half_add_of_doubling_bounds T π₁ π₂ M j₁ j₂ Y hY (hd1 Y hY) (hd2 Y hY) (ha1 Y hY) (ha2 Y hY) (h * T.expt Y) hh (-1)`.

Rewrite `h2` using `[mul_assoc, e, mul_one]`. Conclude with `h2`. Establish `q1 : Q 1`. Introduce `x y`. Rewrite using `[map_one, map_one, ContinuousLinearMap.one_apply, ContinuousLinearMap.one_apply]`.

Conclude with `hiso x y`. Introduce `g`. Establish `hg : g ∈ S` using `hle (by rw [hT]; exact Subgroup.mem_top g)`. Establish `q2` using `(hg 1).mp q1`. Rewrite `q2` using `[one_mul]`.

Conclude with `q2`.
-/
theorem inner_apply_eq_of_analytic : ∀ (p q : ℕ) (T : GrpData p q), Subgroup.closure (T.expt '' upq p q) = ⊤ → ∀ (π₁ π₂ : URep T) (M : GKMod p q) (j₁ : M.V →ₗ[ℂ] π₁.H) (j₂ : M.V →ₗ[ℂ] π₂.H), (∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => π₁.π (T.expt (t • Y)) (j₁ x)) (j₁ (M.act Y x)) 0) → (∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => π₂.π (T.expt (t • Y)) (j₂ x)) (j₂ (M.act Y x)) 0) → (∀ Y ∈ upq p q, ∀ x, AnalyticOnNhd ℝ (fun t : ℝ => π₁.π (T.expt (t • Y)) (j₁ x)) Set.univ) → (∀ Y ∈ upq p q, ∀ x, AnalyticOnNhd ℝ (fun t : ℝ => π₂.π (T.expt (t • Y)) (j₂ x)) Set.univ) → (∀ x y, inner ℂ (j₁ x) (j₁ y) = inner ℂ (j₂ x) (j₂ y)) → ∀ g x y, inner ℂ (j₁ x) (π₁.π g (j₁ y)) = inner ℂ (j₂ x) (π₂.π g (j₂ y)) := by
  intro p q T hT π₁ π₂ M j₁ j₂ hd1 hd2 ha1 ha2 hiso
  let Q : T.G → Prop := fun h => ∀ x y, inner ℂ (j₁ x) (π₁.π h (j₁ y)) = inner ℂ (j₂ x) (π₂.π h (j₂ y))
  let S : Subgroup T.G :=
    { carrier := {g | ∀ h, Q h ↔ Q (h * g)}
      mul_mem' := fun {a b} ha hb h => (ha h).trans (by rw [hb (h * a), mul_assoc])
      one_mem' := fun h => by rw [mul_one]
      inv_mem' := fun {g} hg h => by
        have e := hg (h * g⁻¹)
        rw [inv_mul_cancel_right] at e
        exact e.symm }
  have hle : Subgroup.closure (T.expt '' upq p q) ≤ S := by
    rw [Subgroup.closure_le]
    rintro _ ⟨Y, hY, rfl⟩ h
    have e : T.expt Y * T.expt ((-1 : ℝ) • Y) = 1 := by
      have e1 := T.expt_add Y hY 1 (-1)
      rw [one_smul, show (1 : ℝ) + -1 = 0 by norm_num, zero_smul, T.expt_zero] at e1
      exact e1.symm
    constructor
    · intro hh
      have h2 := eventually_abs_le_half_add_of_doubling_bounds T π₁ π₂ M j₁ j₂ Y hY (hd1 Y hY) (hd2 Y hY) (ha1 Y hY) (ha2 Y hY) h hh 1
      rw [one_smul] at h2
      exact h2
    · intro hh
      have h2 := eventually_abs_le_half_add_of_doubling_bounds T π₁ π₂ M j₁ j₂ Y hY (hd1 Y hY) (hd2 Y hY) (ha1 Y hY) (ha2 Y hY)
        (h * T.expt Y) hh (-1)
      rw [mul_assoc, e, mul_one] at h2
      exact h2
  have q1 : Q 1 := by
    intro x y
    rw [map_one, map_one, ContinuousLinearMap.one_apply, ContinuousLinearMap.one_apply]
    exact hiso x y
  intro g
  have hg : g ∈ S := hle (by rw [hT]; exact Subgroup.mem_top g)
  have q2 := (hg 1).mp q1
  rw [one_mul] at q2
  exact q2

end GlobalTheory.AnalyticVec
