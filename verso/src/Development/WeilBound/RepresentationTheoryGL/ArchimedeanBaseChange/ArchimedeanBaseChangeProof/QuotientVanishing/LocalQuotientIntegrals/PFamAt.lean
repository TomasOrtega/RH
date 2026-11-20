import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.OneVanish

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc

namespace PositivityTheory.Rg.BcB.CV.FamilyAtPlace

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4

/- English proof (translation)
The claim follows from `IsCMField.complexEmbedding_complexConj E v.embedding x`.
-/
theorem emb_conj {E : Type} [Field E] [NumberField E] [IsCMField E] (v : InfinitePlace E) (x : E) :
    v.embedding (conjE E x) = starRingEnd ℂ (v.embedding x) :=
  IsCMField.complexEmbedding_complexConj E v.embedding x

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Establish `h1 : (locGL v (thetaE E n d)).val = ((thetaR (conjE E) n d).val).map v.embedding` using `rfl`. Establish `h2 : (locGL v d⁻¹).val = (d⁻¹ : GL (Fin n) E).val.map v.embedding` using `rfl`. Rewrite using `[h1, thetaR_val, thetaR_val, ← map_inv, h2]`. Use extensionality with `i j`.

Simplify using `[emb_conj]`.
-/
theorem locGL_theta {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (v : InfinitePlace E)
    (d : GL (Fin n) E) : locGL v (thetaE E n d) = thC n (locGL v d) := by
  apply Units.ext
  have h1 : (locGL v (thetaE E n d)).val = ((thetaR (conjE E) n d).val).map v.embedding := rfl
  have h2 : (locGL v d⁻¹).val = (d⁻¹ : GL (Fin n) E).val.map v.embedding := rfl
  rw [h1, thetaR_val, thetaR_val, ← map_inv, h2]
  ext i j
  simp [emb_conj]

/- English proof (translation)
Rewrite using `[nrm, map_mul, locGL_theta]`.
-/
theorem locGL_nrm {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (v : InfinitePlace E)
    (d : GL (Fin n) E) : locGL v (nrm d) = locGL v d * thC n (locGL v d) := by
  rw [nrm, map_mul, locGL_theta]

/- English proof (translation)
Introduce `_ hy x hx` and use `hy x (h hx)`.
-/
theorem perp_anti {K : Type} [Field K] (σ : K →+* K) {n : ℕ} {W W' : Submodule K (Fin n → K)} (h : W ≤ W') :
    perp σ W' ≤ perp σ W := fun _ hy x hx => hy x (h hx)

/- English proof (translation)
The claim follows from `Submodule.map_mono (perp_anti σ h)`.
-/
theorem perpD_anti {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (d : GL (Fin n) K) {W W' : Submodule K (Fin n → K)}
    (h : W ≤ W') : perpD σ d W' ≤ perpD σ d W :=
  Submodule.map_mono (perp_anti σ h)

end PositivityTheory.Rg.BcB.CV.FamilyAtPlace

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 PositivityTheory.Rg.BcB.CV.FamilyAtPlace in
/- English proof (translation)
Introduce `hLF hP E _ _ _ n m d Wof a V v hPar hV hemb`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← locGL_nrm]`. Establish `: (locGL v (nrm d)).val = (nrm d).val.map v.embedding` using `rfl`. Rewrite using `[this, Matrix.charpoly_map]`.

Conclude with `hPar.reg.map`. Use `⟨?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `continuous_pi fun e => (hP E n v (Wof e)).2.1`. Introduce `x`. Conclude with `((hP E n v (Wof 0)).2.2.2.1 hPar.zero).1 x`.

Introduce `x k hk`. Use function extensionality and compare the values at `e`. Conclude with `(hP E n v (Wof e)).2.2.1 x k hk`. Introduce `t ht x z`. Establish `hs` using `hemb t ht`.

Establish `key : ∀ e, pAt Wof v (t * x) e = pAt Wof v x e - sdot e (a (embInf n v t))`. Introduce `e`. Establish `h1` using `(hP E n v (Wof e)).2.2.2.2.2.2.2 t (embInf n v x)`. Rewrite `h1` using `[(hP E n v (Wof e)).2.2.2.2.1 x, hPar.degT _ hs]`. Simplify using `only [pAt]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `: pAt Wof v (t * x) + z = fun e => (pAt Wof v x + z) e - sdot e (a (embInf n v t))`. Use function extensionality and compare the values at `e`. Simplify using `only [Pi.add_apply, key]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this, hV _ hs]`. Introduce `e he`. Establish `hW : Wof e ≠ ⊥`. Introduce `h`. Take `⟨e0, _, hu⟩` from `hPar.uniq ⊥ (hPar.zero ▸ hPar.iso 0)`.

Conclude with `he ((hu e h).trans (hu 0 hPar.zero).symm)`. Take `⟨h1, h2, h3, h4, h5⟩` from `hLF E n d (Wof e) v (hPar.iso e) hW (hPar.perp e)`. Use `⟨_, _, ⟨h1, h2, h3, h4⟩, ?_⟩` and prove the remaining obligations. Introduce `u hu x e' he'`. Establish `hW' : Wof e' ≤ Wof e ∨ (Wof e ≤ Wof e' ∧ Wof e' ≤ perpD (conjE E) d (Wof e))`.

Break down `he' with h | h` into its components or cases. Conclude with `Or.inr ⟨hPar.mono _ _ h, (hPar.iso e').2.trans (perpD_anti _ _ (hPar.mono _ _ h))⟩`. Conclude with `Or.inl (hPar.mono _ _ h)`. Establish `c1` using `(hP E n v (Wof e')).1 (embInf n v u * embInf n v x)`. Establish `c2` using `(hP E n v (Wof e')).1 (embInf n v x)`.

Rewrite `c1` using `[map_mul, (hP E n v (Wof e')).2.2.2.2.1 u, (hP E n v (Wof e')).2.2.2.2.1 x]`. Rewrite `c2` using `[(hP E n v (Wof e')).2.2.2.2.1 x]`. Simplify using `only [pAt]`. Rewrite using `[← c1, ← c2]`. Conclude with `h5 (embInf n v x) u hu (Wof e') hW'`.
-/
theorem PositivityTheory.Rg.BcB.CV.pf_FamAt : PositivityTheory.Rg.BcB.D4.LocFlag → PositivityTheory.Rg.BcB.CV.Ploc → PositivityTheory.Rg.BcB.CV.FamAt := by
  intro hLF hP E _ _ _ n m d Wof a V v hPar hV hemb
  refine ⟨?_, ?_⟩
  · rw [← locGL_nrm]
    have : (locGL v (nrm d)).val = (nrm d).val.map v.embedding := rfl
    rw [this, Matrix.charpoly_map]
    exact hPar.reg.map
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact continuous_pi fun e => (hP E n v (Wof e)).2.1
    · intro x
      exact ((hP E n v (Wof 0)).2.2.2.1 hPar.zero).1 x
    · intro x k hk
      funext e
      exact (hP E n v (Wof e)).2.2.1 x k hk
    · intro t ht x z
      have hs := hemb t ht
      have key : ∀ e, pAt Wof v (t * x) e = pAt Wof v x e - sdot e (a (embInf n v t)) := by
        intro e
        have h1 := (hP E n v (Wof e)).2.2.2.2.2.2.2 t (embInf n v x)
        rw [(hP E n v (Wof e)).2.2.2.2.1 x, hPar.degT _ hs] at h1
        simp only [pAt]
        linarith
      have : pAt Wof v (t * x) + z = fun e => (pAt Wof v x + z) e - sdot e (a (embInf n v t)) := by
        funext e
        simp only [Pi.add_apply, key]
        ring
      rw [this, hV _ hs]
    · intro e he
      have hW : Wof e ≠ ⊥ := by
        intro h
        obtain ⟨e0, _, hu⟩ := hPar.uniq ⊥ (hPar.zero ▸ hPar.iso 0)
        exact he ((hu e h).trans (hu 0 hPar.zero).symm)
      obtain ⟨h1, h2, h3, h4, h5⟩ := hLF E n d (Wof e) v (hPar.iso e) hW (hPar.perp e)
      refine ⟨_, _, ⟨h1, h2, h3, h4⟩, ?_⟩
      intro u hu x e' he'
      have hW' : Wof e' ≤ Wof e ∨ (Wof e ≤ Wof e' ∧ Wof e' ≤ perpD (conjE E) d (Wof e)) := by
        rcases he' with h | h
        · exact Or.inr ⟨hPar.mono _ _ h, (hPar.iso e').2.trans (perpD_anti _ _ (hPar.mono _ _ h))⟩
        · exact Or.inl (hPar.mono _ _ h)
      have c1 := (hP E n v (Wof e')).1 (embInf n v u * embInf n v x)
      have c2 := (hP E n v (Wof e')).1 (embInf n v x)
      rw [map_mul, (hP E n v (Wof e')).2.2.2.2.1 u, (hP E n v (Wof e')).2.2.2.2.1 x] at c1
      rw [(hP E n v (Wof e')).2.2.2.2.1 x] at c2
      simp only [pAt]
      rw [← c1, ← c2]
      exact h5 (embInf n v x) u hu (Wof e') hW'
