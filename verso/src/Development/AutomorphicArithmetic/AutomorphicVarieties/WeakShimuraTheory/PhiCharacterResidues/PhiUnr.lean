import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.ContinuousResLe

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

/- English proof (translation)
Introduce `Ω _ _ _ l _ c D T c' h K X n A v hA hv g hg`. Establish `hS : v ∉ K.s.S` using `by rw [← K.hV]; exact hv`. Establish `hl : ¬ A.valuation (l : Ω) < 1`. Introduce `hlt`. Apply `hS` to reduce the goal to its premises.

Use `left`. Apply `(hA (l : 𝓞 (W.Lp T.L))).1` to reduce the goal to its premises. Simplify using `using hlt`. Take `⟨hκ, hr⟩` from `K.unr A v hA hS g hg`. Establish `hβ : K.β g = 1` using `K.β_t (K.t_unr A hl hg)`.

Establish `hmem : resLe T.F_le g ∈ (T.fr ∅).N`. Use `⟨A, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `p hp`. Establish `hp' : p = l` using `by simpa using hp`. Rewrite using `[hp']`.

Conclude with `hl`. Conclude with `hg`. Establish `he : resQ T.F (resLe T.F_le g) = resQ T.L g`. Use extensionality with `x`. Both sides reduce to the same expression.

Rewrite using `[he]`. Conclude with `hr`. Rewrite using `[MonoidHom.mem_ker, UpperTheory.V.Ws.Link.rho_apply]`. Establish `hsc : K.sc n g = 1` using `by simp [UpperTheory.V.Ws.Link.sc, hκ, hβ]`. Rewrite using `[hsc, map_one, one_smul]`.

Conclude with `X.pair.kill _ hmem`.
-/
theorem UpperTheory.V.Ws.phiUnr :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (n : ℕ), ∀ (A : ValuationSubring Ω) (v : W.Plc (W.Lp T.L)), IsPlaceOver A v → v ∉ K.V.S' → Ine (F := T.L) A ≤ (K.rho X n).ker := by
  intro Ω _ _ _ l _ c D T c' h K X n A v hA hv g hg
  have hS : v ∉ K.s.S := by rw [← K.hV]; exact hv
  have hl : ¬ A.valuation (l : Ω) < 1 := by
    intro hlt
    apply hS
    left
    apply (hA (l : 𝓞 (W.Lp T.L))).1
    simpa using hlt
  obtain ⟨hκ, hr⟩ := K.unr A v hA hS g hg
  have hβ : K.β g = 1 := K.β_t (K.t_unr A hl hg)
  have hmem : resLe T.F_le g ∈ (T.fr ∅).N := by
    refine ⟨A, ?_, ?_, ?_⟩
    · intro p hp
      have hp' : p = l := by simpa using hp
      rw [hp']
      exact hl
    · exact hg
    · have he : resQ T.F (resLe T.F_le g) = resQ T.L g := by
        ext x
        rfl
      rw [he]
      exact hr
  rw [MonoidHom.mem_ker, UpperTheory.V.Ws.Link.rho_apply]
  have hsc : K.sc n g = 1 := by simp [UpperTheory.V.Ws.Link.sc, hκ, hβ]
  rw [hsc, map_one, one_smul]
  exact X.pair.kill _ hmem
