import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubini

open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc UpperTheory.V.Z.Tf.Orb

/- English proof (translation)
Introduce `hG hX hC hP hH hU hA k _ _ _ _ _ E _ _ _ _ _ _ _ _ σ hσ n _ _ μE hμE δ hδ μ hμ a b a1 a2 b1 b2 ha`. Take `⟨g1, g2, g3, -, -⟩` from `hG E n`. Take `⟨c1, c2⟩` from `hC k E σ hσ n δ hδ`. Take `⟨-, i2, -⟩` from `hH _ _ c1 c2 μ hμ`. Take `⟨u1, u2⟩` from `hU E n μE hμE`.

Establish `hs` using `((hX k E).2.2 n).2 σ`. Establish `hl : (sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ Module.finrank k E = 1`. Rewrite using `[← sigmaGL_pow, ← IsGalois.card_aut_eq_finrank, pow_card_eq_one', sigmaGL_one]`. Establish `hp : ∀ (m : ℕ) x, a (((sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ m) x) = a x` using `fun m => by`. Proceed by induction on `m with`.

Consider the case `zero => intro x`. Both sides reduce to the same expression. Consider the case `succ m ih => intro x`. Rewrite using `[pow_succ_apply', ha, ih]`. Establish `t` using `hA _ μE hμE u1 u2 (sigmaGL σ) hs _ Module.finrank_pos.ne' hl δ (hP k E σ hσ n δ hδ) μ hμ i2 a b a1 a2 b1 b2`.

Simplify `t` using `only [hp]`.
-/
theorem UpperTheory.V.Z.Tf.Orb.twOrbComm :
    UpperTheory.V.Z.Tf.Orb.GLTop → UpperTheory.V.Z.Tf.Orb.ExtCont → UpperTheory.V.Z.Tf.Orb.TwCent → UpperTheory.V.Z.Tf.Orb.OrbProper → UpperTheory.V.Z.Tf.Orb.HaarComm → UpperTheory.V.Z.Tf.Orb.Unimod → UpperTheory.V.Z.Tf.Orb.AbsComm → UpperTheory.V.Z.Tf.Orb.TwOrbComm := by
  intro hG hX hC hP hH hU hA k _ _ _ _ _ E _ _ _ _ _ _ _ _ σ hσ n _ _ μE hμE δ hδ μ hμ a b a1 a2 b1 b2 ha
  obtain ⟨g1, g2, g3, -, -⟩ := hG E n
  obtain ⟨c1, c2⟩ := hC k E σ hσ n δ hδ
  obtain ⟨-, i2, -⟩ := hH _ _ c1 c2 μ hμ
  obtain ⟨u1, u2⟩ := hU E n μE hμE
  have hs := ((hX k E).2.2 n).2 σ
  have hl : (sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ Module.finrank k E = 1 := by
    rw [← sigmaGL_pow, ← IsGalois.card_aut_eq_finrank, pow_card_eq_one', sigmaGL_one]
  have hp : ∀ (m : ℕ) x, a (((sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ m) x) = a x := fun m => by
    induction m with
    | zero => intro x; rfl
    | succ m ih => intro x; rw [pow_succ_apply', ha, ih]
  have t := hA _ μE hμE u1 u2 (sigmaGL σ) hs _ Module.finrank_pos.ne' hl δ (hP k E σ hσ n δ hδ) μ hμ i2 a b a1 a2 b1 b2
  simpa only [hp] using t
