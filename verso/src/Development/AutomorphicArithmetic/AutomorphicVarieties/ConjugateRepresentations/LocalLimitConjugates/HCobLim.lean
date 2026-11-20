import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.AbsSolve
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private def Fty {I : Type} (f : (I → ℂ) → ℂ) : Prop :=
  ∃ L : I →₀ ℂ, ∀ b : I → ℂ, Finsupp.linearCombination ℂ b L = f b

/- English proof (translation)
Supply the required witnesses or components.
-/
private theorem fty_ev {I : Type} (a : ℂ) (i : I) : Fty fun b : I → ℂ => a * b i :=
  ⟨Finsupp.single i a, fun b => by rw [Finsupp.linearCombination_single, smul_eq_mul]⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
private theorem fty_sub {I : Type} {f g : (I → ℂ) → ℂ} (hf : Fty f) (hg : Fty g) : Fty fun b => f b - g b := by
  obtain ⟨L, hL⟩ := hf
  obtain ⟨M, hM⟩ := hg
  exact ⟨L - M, fun b => by rw [map_sub, hL, hM]⟩

/- English proof (translation)
Supply the required witnesses or components. A detailed English derivation is pending.
-/
private theorem fty_sum {I K : Type} (t : Finset K) (f : K → (I → ℂ) → ℂ) (hf : ∀ k, Fty (f k)) :
    Fty fun b => ∑ k ∈ t, f k b := by
  choose L hL using hf
  exact ⟨∑ k ∈ t, L k, fun b => by rw [map_sum]; exact Finset.sum_congr rfl fun k _ => hL k b⟩

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. Supply the required witnesses or components. A detailed English derivation is pending.
-/
private theorem fty_solve {I J : Type} (f : J → (I → ℂ) → ℂ) (hf : ∀ j, Fty (f j)) (c : J → ℂ) (cn : ℕ → J → ℂ)
    (h : ∀ k, ∃ b, ∀ j, f j b = cn k j) (hl : ∀ j, Tendsto (fun k => cn k j) atTop (𝓝 (c j))) :
    ∃ b, ∀ j, f j b = c j := by
  choose L hL using hf
  have hs : ∀ (b : I → ℂ) j, (L j).sum (fun i x => x * b i) = f j b := by
    intro b j
    rw [← hL, Finsupp.linearCombination_apply]
    rfl
  obtain ⟨b, hb⟩ := absSolve I J L c cn (fun k => by
    obtain ⟨b, hb⟩ := h k
    exact ⟨b, fun j => by rw [hs, hb]⟩) hl
  exact ⟨b, fun j => by rw [← hs, hb]⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Split into cases according to the possible forms of the given data. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact.

Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the indicated hypotheses using the stated equalities.

Treat this case separately. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Assume the hypotheses and unpack their components.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Both sides reduce to the same expression.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations.

Apply function extensionality and compare values at an arbitrary argument. Apply function extensionality and compare values at an arbitrary argument. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Cj.H.hCobLim :
    UpperTheory.V.Cj.H.HCobLim := by
  intro Γ S _ d ρ hρ q c cn h hl
  have hlim : ∀ x : List Γ, x.length = q + 1 → ∀ s i,
      Tendsto (fun k => (c - cn k) x s i) atTop (𝓝 (c x s i)) := by
    intro x hx s i
    have h1 : Tendsto (fun k => cn k x s i) atTop (𝓝 0) := tendsto_pi_nhds.1 (hl x hx s) i
    simpa using (tendsto_const_nhds (x := c x s i)).sub h1
  cases q with
  | zero =>
    intro x hx
    funext s i
    have h1 := hlim x hx s i
    have h2 : (fun k => (c - cn k) x s i) = fun _ => (0 : ℂ) := by
      funext k
      rw [h k x hx]
      rfl
    rw [h2] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  | succ q =>
    let cur : (List Γ × S × Fin d → ℂ) → List Γ → S → Fin d → ℂ := fun b x s i => b (x, s, i)
    let f : (Γ × {x : List Γ // x.length = q + 1} × S × Fin d) ⊕ ({x : List Γ // x.length = q + 2} × S × Fin d) →
        (List Γ × S × Fin d → ℂ) → ℂ :=
      Sum.elim (fun p b => cur b (p.2.1.1.map (p.1 * ·)) p.2.2.1 p.2.2.2 - ρ p.1 (cur b p.2.1.1) p.2.2.1 p.2.2.2)
        (fun p b => hd (cur b) p.1.1 p.2.1 p.2.2)
    have hf : ∀ j, Fty (f j) := by
      rintro (⟨γ, x, s, i⟩ | ⟨x, s, i⟩)
      · obtain ⟨s', B, hB⟩ := hρ γ s
        have e : f (Sum.inl (γ, x, s, i)) =
            fun b => 1 * b (x.1.map (γ * ·), s, i) - ∑ j, B i j * b (x.1, s', j) := by
          funext b
          simp only [f, Sum.elim_inl, hB, one_mul]
          rfl
        rw [e]
        exact fty_sub (fty_ev _ _) (fty_sum _ _ fun j => fty_ev _ _)
      · have e : f (Sum.inr (x, s, i)) =
            fun b => ∑ j ∈ Finset.range x.1.length, ((-1 : ℂ) ^ j) * b (x.1.eraseIdx j, s, i) := by
          funext b
          simp [f, cur, hd, Finset.sum_apply]
        rw [e]
        exact fty_sum _ _ fun j => fty_ev _ _
    obtain ⟨b, hb⟩ := fty_solve f hf (Sum.elim (fun _ => 0) fun p => c p.1.1 p.2.1 p.2.2)
      (fun k => Sum.elim (fun _ => 0) fun p => (c - cn k) p.1.1 p.2.1 p.2.2) (fun k => by
        obtain ⟨b, h1, h2⟩ := h k
        refine ⟨fun p => b p.1 p.2.1 p.2.2, ?_⟩
        rintro (⟨γ, x, s, i⟩ | ⟨x, s, i⟩)
        · change b (x.1.map (γ * ·)) s i - ρ γ (b x.1) s i = 0
          rw [h1 γ x.1 x.2, sub_self]
        · change hd b x.1 s i = (c - cn k) x.1 s i
          rw [h2 x.1 x.2]) (by
        rintro (p | ⟨x, s, i⟩)
        · exact tendsto_const_nhds
        · exact hlim x.1 x.2 s i)
    refine ⟨cur b, fun γ x hx => ?_, fun x hx => ?_⟩
    · funext s i
      exact sub_eq_zero.1 (hb (Sum.inl (γ, ⟨x, hx⟩, s, i)))
    · funext s i
      exact (hb (Sum.inr (⟨x, hx⟩, s, i))).symm
