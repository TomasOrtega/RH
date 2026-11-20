import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftWeightCombinatorialDataULeUZero
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.ExpTie GlobalTheory.ExpTie.Lift

/- English proof (translation)
Introduce `D L j τ hv`. Establish `hS : (GlobalTheory.ExpTie.parOf L j).S = L.Sc` using `rfl`. Establish `hkc : Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) = D.R.k - 1` using `rfl`. Establish `hxm : (GlobalTheory.ExpTie.Lift.wts L j).xm τ = ⌈(GlobalTheory.ExpTie.Lift.wts L j).c τ⌉` using `rfl`. Establish `hxp : (GlobalTheory.ExpTie.Lift.wts L j).xp τ = ⌊(GlobalTheory.ExpTie.Lift.wts L j).c τ + L.Sc⌋` using `rfl`.

Establish `hrow : ∀ a, a < D.R.k - 1 → (GlobalTheory.ExpTie.Lift.wts L j).xm τ ≤ (GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a ∧ (GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a ≤ (GlobalTheory.ExpTie.Lift.wts L j).xp τ`. Introduce `a ha`. Establish `h1` using `hv.1 a ha`. Establish `h2` using `L.cloud_v τ ⟨a, ha⟩`. Establish `hlo : (GlobalTheory.ExpTie.Lift.wts L j).c τ ≤ ((GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a : ℝ)`.

Establish `: (0 : ℝ) ≤ (((D.hc τ).v ⟨a, ha⟩ : ℚ) : ℝ)` using `by exact_mod_cast h2.1`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hhi : ((GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a : ℝ) ≤ (GlobalTheory.ExpTie.Lift.wts L j).c τ + L.Sc`. Establish `: (((D.hc τ).v ⟨a, ha⟩ : ℚ) : ℝ) ≤ L.Sc` using `by exact_mod_cast h2.2`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[hxm, hxp]`. Conclude with `⟨Int.ceil_le.2 hlo, Int.le_floor.2 hhi⟩`. Establish `hk` using `D.R.m_add_three_le_k`. Establish `hm2` using `D.R.two_le_m`. Establish `h0` using `hrow 0 (by omega)`.

Use `⟨⟨?_, le_trans h0.1 h0.2, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hxm]`. Conclude with `Int.le_ceil _`. Rewrite using `[hxp, hS]`. Conclude with `Int.floor_le _`.

Introduce `a ha`. Rewrite `ha` using `[hkc]`. Conclude with `hrow a ha`.
-/
theorem GlobalTheory.ExpTie.Lift.window_cloud : ∀ {D : Formalism.BasicNotions.D7} (L : Formalism.BasicNotions.SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau), GlobalTheory.ExpTie.Lift.ValsAt L j τ → ((GlobalTheory.ExpTie.Lift.wts L j).c τ ≤ ((GlobalTheory.ExpTie.Lift.wts L j).xm τ : ℝ) ∧ (GlobalTheory.ExpTie.Lift.wts L j).xm τ ≤ (GlobalTheory.ExpTie.Lift.wts L j).xp τ ∧ ((GlobalTheory.ExpTie.Lift.wts L j).xp τ : ℝ) ≤ (GlobalTheory.ExpTie.Lift.wts L j).c τ + (GlobalTheory.ExpTie.parOf L j).S) ∧ ∀ a, a < Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) → (GlobalTheory.ExpTie.Lift.wts L j).xm τ ≤ (GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a ∧ (GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a ≤ (GlobalTheory.ExpTie.Lift.wts L j).xp τ := by
  intro D L j τ hv
  have hS : (GlobalTheory.ExpTie.parOf L j).S = L.Sc := rfl
  have hkc : Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) = D.R.k - 1 := rfl
  have hxm : (GlobalTheory.ExpTie.Lift.wts L j).xm τ = ⌈(GlobalTheory.ExpTie.Lift.wts L j).c τ⌉ := rfl
  have hxp : (GlobalTheory.ExpTie.Lift.wts L j).xp τ = ⌊(GlobalTheory.ExpTie.Lift.wts L j).c τ + L.Sc⌋ := rfl

  have hrow : ∀ a, a < D.R.k - 1 →
      (GlobalTheory.ExpTie.Lift.wts L j).xm τ ≤ (GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a ∧
        (GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a ≤ (GlobalTheory.ExpTie.Lift.wts L j).xp τ := by
    intro a ha
    have h1 := hv.1 a ha
    have h2 := L.cloud_v τ ⟨a, ha⟩
    have hlo : (GlobalTheory.ExpTie.Lift.wts L j).c τ ≤ ((GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a : ℝ) := by
      have : (0 : ℝ) ≤ (((D.hc τ).v ⟨a, ha⟩ : ℚ) : ℝ) := by exact_mod_cast h2.1
      linarith
    have hhi : ((GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a : ℝ) ≤ (GlobalTheory.ExpTie.Lift.wts L j).c τ + L.Sc := by
      have : (((D.hc τ).v ⟨a, ha⟩ : ℚ) : ℝ) ≤ L.Sc := by exact_mod_cast h2.2
      linarith
    rw [hxm, hxp]
    exact ⟨Int.ceil_le.2 hlo, Int.le_floor.2 hhi⟩
  have hk := D.R.m_add_three_le_k
  have hm2 := D.R.two_le_m
  have h0 := hrow 0 (by omega)
  refine ⟨⟨?_, le_trans h0.1 h0.2, ?_⟩, ?_⟩
  · rw [hxm]; exact Int.le_ceil _
  · rw [hxp, hS]; exact Int.floor_le _
  · intro a ha
    rw [hkc] at ha
    exact hrow a ha
