import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

/- English proof (translation)
Simplify using `only [rd, TensorProduct.tmul_add, map_add]`.
-/
private theorem rd_add' {p : ℕ} [Fact (Nat.Prime p)] {D : UPel.HT.Datum p} {G : HTGroup p}
    (L : Link D G) (x : (AfP p ⊗[ℚ] G.C)ˣ) (h : G.GAf) (a b : VQ D) :
    rd L x h (a + b) = rd L x h a + rd L x h b := by
  simp only [rd, TensorProduct.tmul_add, map_add]

/- English proof (translation)
Proceed by induction on `N with`. Consider the case `zero => simp only [zero_smul, rd, TensorProduct.tmul_zero, map_zero]`. Consider the case `succ n ih => rw [succ_nsmul, rd_add', ih, succ_nsmul]`.
-/
private theorem rd_nsmul' {p : ℕ} [Fact (Nat.Prime p)] {D : UPel.HT.Datum p} {G : HTGroup p}
    (L : Link D G) (x : (AfP p ⊗[ℚ] G.C)ˣ) (h : G.GAf) (N : ℕ) (a : VQ D) :
    rd L x h (N • a) = N • rd L x h a := by
  induction N with
  | zero => simp only [zero_smul, rd, TensorProduct.tmul_zero, map_zero]
  | succ n ih => rw [succ_nsmul, rd_add', ih, succ_nsmul]

/- English proof (translation)
Introduce `p _ D G L v t₀ ρ B PD RD N D' t P D'' t'' P'' w hw hP j j'' hj a ha`. Take `⟨hiso, hmark⟩` from `hw`. Take `⟨⟨hinj, hact, hsurj, s, hs, hform⟩, ⟨hA1, hA2⟩, hloc, Q, hQ, hQj, hrel⟩` from `ha`. Establish `key : ∀ w0 : VQ D, (∃ u : D'.La, w0 = j u) ↔ ∃ u : D''.La, w0 = j'' u`. Introduce `w0`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, rfl⟩`. Conclude with `⟨w.symm u, by rw [hj, LinearEquiv.apply_symm_apply]⟩`. Introduce and unpack `⟨u, rfl⟩`. Conclude with `⟨w u, hj u⟩`.

Use `⟨⟨?_, ?_, ?_, s, hs, ?_⟩, ⟨?_, ?_⟩, ?_, Q, hQ, ?_, hrel⟩` and prove the remaining obligations. Introduce `u u' huu`. Rewrite `huu` using `[hj, hj]`. Conclude with `w.injective (hinj huu)`. Introduce `c u`.

Rewrite using `[hj, hj, map_smul, hact]`. Introduce `w0`. Take `⟨m, u, hm, hmu⟩` from `hsurj w0`. Conclude with `⟨m, w.symm u, hm, by rw [hj, LinearEquiv.apply_symm_apply, hmu]⟩`. Introduce `u u'`.

Rewrite using `[hj, hj, ← hform, hiso]`. Introduce `w0`. Rewrite using `[← hA1 w0]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨r, u, hu⟩`.

Conclude with `⟨r, w u, by rw [hu, hj]⟩`. Introduce and unpack `⟨r, u, hu⟩`. Conclude with `⟨r, w.symm u, by rw [hu, hj, LinearEquiv.apply_symm_apply]⟩`. Introduce `a0`. Take `⟨e, he⟩` from `hmark a0`.

Take `⟨w1, hw1, hw1e⟩` from `hA2 a0`. Establish `he' : rd L (trivX B) a.1.1 (j e) ∈ LaHat D` using `(hA1 (j e)).1 ⟨0, e, by simp⟩`. Use `⟨w1 + rd L (trivX B) a.1.1 (j e), add_mem hw1 he', ?_⟩` and prove the remaining obligations. Rewrite using `[hj, he, map_add, map_nsmul, rd_add', rd_nsmul', hw1e, smul_add, add_assoc]`. Introduce `w0`.

Rewrite using `[← hloc w0]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m, u, hm, hu⟩`. Conclude with `⟨m, w u, hm, by rw [hu, hj]⟩`. Introduce and unpack `⟨m, u, hm, hu⟩`.

Conclude with `⟨m, w.symm u, hm, by rw [hu, hj, LinearEquiv.apply_symm_apply]⟩`. Introduce `u`. Rewrite using `[hj, hQj, hP]`.
-/
theorem UpperTheory.Gal.W2.coordMove_of :
    UpperTheory.Gal.W2.CoordMove := by
  intro p _ D G L v t₀ ρ B PD RD N D' t P D'' t'' P'' w hw hP j j'' hj a ha
  obtain ⟨hiso, hmark⟩ := hw
  obtain ⟨⟨hinj, hact, hsurj, s, hs, hform⟩, ⟨hA1, hA2⟩, hloc, Q, hQ, hQj, hrel⟩ := ha
  have key : ∀ w0 : VQ D, (∃ u : D'.La, w0 = j u) ↔ ∃ u : D''.La, w0 = j'' u := by
    intro w0
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨w.symm u, by rw [hj, LinearEquiv.apply_symm_apply]⟩
    · rintro ⟨u, rfl⟩
      exact ⟨w u, hj u⟩
  refine ⟨⟨?_, ?_, ?_, s, hs, ?_⟩, ⟨?_, ?_⟩, ?_, Q, hQ, ?_, hrel⟩
  · intro u u' huu
    rw [hj, hj] at huu
    exact w.injective (hinj huu)
  · intro c u
    rw [hj, hj, map_smul, hact]
  · intro w0
    obtain ⟨m, u, hm, hmu⟩ := hsurj w0
    exact ⟨m, w.symm u, hm, by rw [hj, LinearEquiv.apply_symm_apply, hmu]⟩
  · intro u u'
    rw [hj, hj, ← hform, hiso]
  · intro w0
    rw [← hA1 w0]
    constructor
    · rintro ⟨r, u, hu⟩
      exact ⟨r, w u, by rw [hu, hj]⟩
    · rintro ⟨r, u, hu⟩
      exact ⟨r, w.symm u, by rw [hu, hj, LinearEquiv.apply_symm_apply]⟩
  · intro a0
    obtain ⟨e, he⟩ := hmark a0
    obtain ⟨w1, hw1, hw1e⟩ := hA2 a0
    have he' : rd L (trivX B) a.1.1 (j e) ∈ LaHat D := (hA1 (j e)).1 ⟨0, e, by simp⟩
    refine ⟨w1 + rd L (trivX B) a.1.1 (j e), add_mem hw1 he', ?_⟩
    rw [hj, he, map_add, map_nsmul, rd_add', rd_nsmul', hw1e, smul_add, add_assoc]
  · intro w0
    rw [← hloc w0]
    constructor
    · rintro ⟨m, u, hm, hu⟩
      exact ⟨m, w u, hm, by rw [hu, hj]⟩
    · rintro ⟨m, u, hm, hu⟩
      exact ⟨m, w.symm u, hm, by rw [hu, hj, LinearEquiv.apply_symm_apply]⟩
  · intro u
    rw [hj, hQj, hP]
