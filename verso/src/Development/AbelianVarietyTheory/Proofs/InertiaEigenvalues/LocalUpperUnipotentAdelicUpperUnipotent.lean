import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspRep

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cornerGL_apply_loctri {R S : Type} [CommRing R] [CommRing S] {a : ℕ} (s : R →ₙ+* S)
    (g : GL (Fin a) R) (i j : Fin a) :
    (cornerGL a s g).val i j = (1 : Matrix (Fin a) (Fin a) S) i j - s ((1 : Matrix (Fin a) (Fin a) R) i j) + s (g.val i j) :=
  rfl

/- English proof (translation)
Rewrite using `[cornerGL_apply_loctri]`. Simplify using `[Matrix.one_apply_ne h]`.
-/
theorem cornerGL_apply_ne_loctri {R S : Type} [CommRing R] [CommRing S] {a : ℕ} (s : R →ₙ+* S)
    (g : GL (Fin a) R) {i j : Fin a} (h : i ≠ j) :
    (cornerGL a s g).val i j = s (g.val i j) := by
  rw [cornerGL_apply_loctri]
  simp [Matrix.one_apply_ne h]

/- English proof (translation)
Rewrite using `[cornerGL_apply_loctri, h]`. Simplify using the standard rewrite rules.
-/
theorem cornerGL_apply_diag_loctri {R S : Type} [CommRing R] [CommRing S] {a : ℕ} (s : R →ₙ+* S)
    (g : GL (Fin a) R) {j : Fin a} (h : g.val j j = 1) :
    (cornerGL a s g).val j j = 1 := by
  rw [cornerGL_apply_loctri, h]
  simp

/- English proof (translation)
Introduce `E _ _ _ a w u hlow hdiag`. Establish `hoff : ∀ i j : Fin a, i ≠ j → (finGL E a (locGL E a w u)).val i j = sFin E (sLoc E w (u.val i j))`. Introduce `i j h`. Rewrite using `[finGL, cornerGL_apply_ne_loctri _ _ h, locGL, cornerGL_apply_ne_loctri _ _ h]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `i j h`. Rewrite using `[hoff i j (ne_of_gt h), hlow i j h, map_zero, map_zero]`. Introduce `j`. Conclude with `cornerGL_apply_diag_loctri _ _ (cornerGL_apply_diag_loctri _ _ (hdiag j))`. Rewrite using `[map_sum, map_sum]`.

Use `Finset.sum_congr rfl fun p hp => ?_` and prove the remaining obligations. Establish `hp' : (p.2 : ℕ) = p.1 + 1` using `(Finset.mem_filter.mp hp).2`. Establish `hne : p.1 ≠ p.2`. Introduce `h`. Rewrite `hp'` using `[h]`.

Use linear arithmetic over natural numbers and integers. Conclude with `hoff p.1 p.2 hne`.
-/
theorem locTri_adelic : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E)) (u : GL (Fin a) (w.adicCompletion E)), (∀ i j : Fin a, j < i → u.val i j = 0) → (∀ j : Fin a, u.val j j = 1) → (∀ i j : Fin a, j < i → (finGL E a (locGL E a w u)).val i j = 0) ∧ (∀ j : Fin a, (finGL E a (locGL E a w u)).val j j = 1) ∧ ∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, (finGL E a (locGL E a w u)).val p.1 p.2 = sFin E (sLoc E w (∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, u.val p.1 p.2)) := by
  intro E _ _ _ a w u hlow hdiag
  have hoff : ∀ i j : Fin a, i ≠ j → (finGL E a (locGL E a w u)).val i j = sFin E (sLoc E w (u.val i j)) := by
    intro i j h
    rw [finGL, cornerGL_apply_ne_loctri _ _ h, locGL, cornerGL_apply_ne_loctri _ _ h]
  refine ⟨?_, ?_, ?_⟩
  · intro i j h
    rw [hoff i j (ne_of_gt h), hlow i j h, map_zero, map_zero]
  · intro j
    exact cornerGL_apply_diag_loctri _ _ (cornerGL_apply_diag_loctri _ _ (hdiag j))
  · rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp' : (p.2 : ℕ) = p.1 + 1 := (Finset.mem_filter.mp hp).2
    have hne : p.1 ≠ p.2 := by
      intro h; rw [h] at hp'; omega
    exact hoff p.1 p.2 hne

end GlobalTheory.CuspRep
