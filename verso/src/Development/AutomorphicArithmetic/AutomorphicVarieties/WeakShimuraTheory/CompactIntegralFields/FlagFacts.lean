import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

/- English proof (translation)
Establish `h1 : f h = 0` using `by simpa using h0 1`. Establish `h2` using `hf (g * h * g⁻¹) g`. Establish `h3 : A (g * h * g⁻¹) = A h` using `by simp [mul_comm (A g) (A h)]`. Rewrite `h2` using `[h0, h3, inv_mul_cancel_right, hf, h1]`. Establish `h4 : f g * (a (A h) - a (B h)) = 0` using `by linear_combination -h2`.

Conclude with `(mul_eq_zero.1 h4).resolve_right (sub_ne_zero.2 hh)`.
-/
private theorem coc_zero {Γ O k : Type} [Group Γ] [CommRing O] [Field k] (a : O →+* k) (A B : Γ →* Oˣ) (f : Γ → k)
    (hf : ∀ g h, f (g * h) = a (A g) * f h + f g * a (B h)) (h : Γ) (hh : a (A h) ≠ a (B h))
    (h0 : ∀ g, f (g * h * g⁻¹) = 0) (g : Γ) : f g = 0 := by
  have h1 : f h = 0 := by simpa using h0 1
  have h2 := hf (g * h * g⁻¹) g
  have h3 : A (g * h * g⁻¹) = A h := by simp [mul_comm (A g) (A h)]
  rw [h0, h3, inv_mul_cancel_right, hf, h1] at h2
  have h4 : f g * (a (A h) - a (B h)) = 0 := by linear_combination -h2
  exact (mul_eq_zero.1 h4).resolve_right (sub_ne_zero.2 hh)

/- English proof (translation)
Use `⟨{ (g * resQ F h * g⁻¹).toRingEquiv with commutes' := fun x => ?_ }, rfl⟩` and prove the remaining obligations. Establish `h1` using `AlgEquiv.restrictNormal_commutes g⁻¹ F x`. Establish `h2` using `h.commutes ((AlgEquiv.restrictNormal g⁻¹ F) x)`. Rewrite `h2` using `[h1]`. Use `show g (h (g⁻¹ (algebraMap F Ω x))) = algebraMap F Ω x`.

Rewrite using `[h2]`. Conclude with `g.apply_symm_apply _`.
-/
private theorem conj_mem {Ω : Type} [Field Ω] [CharZero Ω] (F : IntermediateField ℚ Ω) [Normal ℚ F]
    (h : G F Ω) (g : G ℚ Ω) : ∃ h' : G F Ω, resQ F h' = g * resQ F h * g⁻¹ := by
  refine ⟨{ (g * resQ F h * g⁻¹).toRingEquiv with commutes' := fun x => ?_ }, rfl⟩
  have h1 := AlgEquiv.restrictNormal_commutes g⁻¹ F x
  have h2 := h.commutes ((AlgEquiv.restrictNormal g⁻¹ F) x)
  rw [h1] at h2
  show g (h (g⁻¹ (algebraMap F Ω x))) = algebraMap F Ω x
  rw [h2]
  exact g.apply_symm_apply _

/- English proof (translation)
Establish `h1 : IsUnit (x - y)`. Assume the negation of the conclusion as `hn`. Apply `h` to reduce the goal to its premises. Rewrite using `[← sub_eq_zero, ← map_sub, residue_eq_zero_iff]`. Conclude with `hn`.

Establish `h2` using `(h1.map a).ne_zero`. Rewrite `h2` using `[map_sub, sub_ne_zero]`. Then use the resulting hypothesis.
-/
private theorem ne_of_res {O k : Type} [CommRing O] [IsLocalRing O] [Field k] (a : O →+* k) {x y : O}
    (h : residue O x ≠ residue O y) : a x ≠ a y := by
  have h1 : IsUnit (x - y) := by
    by_contra hn
    apply h
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    exact hn
  have h2 := (h1.map a).ne_zero
  rwa [map_sub, sub_ne_zero] at h2

/- English proof (translation)
Establish `a21 : n 2 1 = 0` using `hq 2 1 (by decide) (by decide)`. Establish `r01 : r 0 1 = 0` using `hr 0 1 (by decide) (by decide)`. Establish `r02 : r 0 2 = 0` using `hr 0 2 (by decide) (by decide)`. Establish `r03 : r 0 3 = 0` using `hr 0 3 (by decide) (by decide)`. Establish `r13 : r 1 3 = 0` using `hr 1 3 (by decide) (by decide)`.

Establish `r21 : r 2 1 = 0` using `hr 2 1 (by decide) (by decide)`. Establish `r23 : r 2 3 = 0` using `hr 2 3 (by decide) (by decide)`. Take `⟨-, d, u⟩` from `hn`. Take `⟨g', d', u'⟩` from `hn'`. Establish `a01` using `u 0 1 (by decide)`.

Establish `b01` using `u' 0 1 (by decide)`. Establish `b02` using `u' 0 2 (by decide)`. Establish `b12` using `u' 1 2 (by decide)`. Establish `e21` using `hu 2 1 (by decide)`. Establish `e20` using `hu 2 0 (by decide)`.

Establish `e10` using `hu 1 0 (by decide)`. Establish `g20` using `congrFun (congrFun g' 2) 0`. Establish `g10` using `congrFun (congrFun g' 1) 0`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn, Fin.rev, a21, r01, r02, r03, r13, r21, r23, a01, b01, b02, b12, d, d', h1] at e21 e20 e10 g20 g10`. Rewrite `e20`, `g20` using `[e21]`.

Use `⟨e21, ?_, ?_⟩` and prove the remaining obligations. Take the linear combination `(r 0 0) * g20 - e20`. Take the linear combination `(r 0 0) * g10 - e10`.
-/
private theorem flag_facts {k : Type} [Field k] (n n' r : M4 k) (hn : IsLow n) (hq : SuppM qQ n) (hn' : IsLow n')
    (hr : SuppM nP r) (h1 : r 1 1 ≠ 0) (hu : IsUp (adj n' * r * n)) :
    n' 2 1 = 0 ∧ n' 2 0 * r 0 0 = r 2 0 + r 2 2 * n 2 0 ∧ n' 1 0 * r 0 0 = r 1 0 + r 1 1 * n 1 0 + r 1 2 * n 2 0 := by
  have a21 : n 2 1 = 0 := hq 2 1 (by decide) (by decide)
  have r01 : r 0 1 = 0 := hr 0 1 (by decide) (by decide)
  have r02 : r 0 2 = 0 := hr 0 2 (by decide) (by decide)
  have r03 : r 0 3 = 0 := hr 0 3 (by decide) (by decide)
  have r13 : r 1 3 = 0 := hr 1 3 (by decide) (by decide)
  have r21 : r 2 1 = 0 := hr 2 1 (by decide) (by decide)
  have r23 : r 2 3 = 0 := hr 2 3 (by decide) (by decide)
  obtain ⟨-, d, u⟩ := hn
  obtain ⟨g', d', u'⟩ := hn'
  have a01 := u 0 1 (by decide)
  have b01 := u' 0 1 (by decide)
  have b02 := u' 0 2 (by decide)
  have b12 := u' 1 2 (by decide)
  have e21 := hu 2 1 (by decide)
  have e20 := hu 2 0 (by decide)
  have e10 := hu 1 0 (by decide)
  have g20 := congrFun (congrFun g' 2) 0
  have g10 := congrFun (congrFun g' 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn, Fin.rev, a21, r01, r02, r03, r13, r21, r23, a01, b01, b02, b12, d, d', h1] at e21 e20 e10 g20 g10
  rw [e21] at e20 g20
  refine ⟨e21, ?_, ?_⟩
  · linear_combination (r 0 0) * g20 - e20
  · linear_combination (r 0 0) * g10 - e10

/- English proof (translation)
Introduce `Ω _ _ _ l _ c D _ T hT k _ a _ g0 s s' hs _ hov hres W`. Take `⟨hr, hfl⟩` from `hov`. Establish `hre : ∀ g, s'.r g = s.r (resQ T.F g)` using `fun g => by rw [hr]; rfl`. Establish `diag : ∀ g i, s.r g i i = a (chi D T.pr i g)` using `hs.res.res.diag`. Establish `ne0 : ∀ g i, s.r g i i ≠ 0` using `fun g i => by`.

Rewrite using `[diag]`. Conclude with `((chi D T.pr i g).isUnit.map a).ne_zero`. Establish `low : IsLow (s.n ())` using `hs.res.pair.low ()`. Establish `low' : ∀ v, IsLow (s'.n v)` using `hres.pair.low`. Establish `key : ∀ i j, i ≠ j → (∀ g h, s.r (g * h) i j = s.r g i i * s.r h i j + s.r g i j * s.r h j j) → (∀ g, s'.r g i j = 0) → ∀ g, s.r g i j = 0`.

Introduce `i j hij hc h0`. Use `coc_zero a (chi D T.pr i) (chi D T.pr j) (fun g => s.r g i j) (fun g h => by rw [hc, diag, diag]) (resQ T.F T.g0) (ne_of_res a (hT.1.dist i j hij)) fun g => ?_` and prove the remaining obligations. Take `⟨h', e⟩` from `conj_mem T.F T.g0 g`. Rewrite using `[← e, ← hre]`. Conclude with `h0 h'`.

Establish `z : ∀ g i j, i ≠ j → wt i j ∉ nP → s.r g i j = 0` using `hs.supp`. Establish `ff : ∀ v, ∃ g, s'.n v 2 1 = 0 ∧ s'.n v 2 0 * s.r g 0 0 = s.r g 2 0 + s.r g 2 2 * s.n () 2 0`. Introduce `v`. Take `⟨u, g, -, hu⟩` from `hfl v`. Use `flag_facts (s.n ()) (s'.n v) (s.r g) low hs.flag (low' v) (hs.supp g) (ne0 g 1) hu` as an intermediate fact.

Conclude with `⟨g, this.1, this.2.1⟩`. Establish `hq : ∀ v, SuppM qQ (s'.n v)`. Introduce `v i j hij hw`. Take `⟨g, h21, -⟩` from `ff v`. Establish `: i < j ∨ (i = 2 ∧ j = 1)` using `by revert i j; decide`.

Break down `this with h | ⟨rfl, rfl⟩` into its components or cases. Conclude with `(low' v).2.2 i j h`. Conclude with `h21`. Use `⟨⟨⟨hres.pair.mult, fun g hg => hres.pair.kill g ?_, hres.pair.nrm, hres.pair.low, hres.pair.flag, hres.pair.mu⟩, ⟨hres.res.diag, hres.res.char, hres.res.shape⟩, hres.cont⟩, ⟨fun g => by rw [hre]; exact hs.supp _, hq⟩, ?_⟩` and prove the remaining obligations. Take `⟨A, hA, h⟩` from `hg`.

Conclude with `⟨A, fun p hp => hA p (Finset.insert_subset_insert l (Finset.empty_subset W) hp), h⟩`. Break down `hs.ps with hps | ⟨hv, h20, -, hnc⟩` into its components or cases. Use `left`. Prove the components needed by the constructor for the conclusion. Assume the negation of the conclusion as `hn`.

Take `⟨g, i, j, hw, hg⟩` from `hps`. Use `hg (key i j ?_ (fun g h => ?_) (fun g => by_contra fun h => hn ⟨g, i, j, hw, h⟩) g)` and prove the remaining obligations. Use `clear hg`. Use `revert i j`. Evaluate the decidable proposition.

Establish `: (i = 2 ∧ j = 0) ∨ (i = 3 ∧ j = 1)` using `by clear hg; revert i j; decide`. Rewrite using `[map_mul, Matrix.mul_apply, Fin.sum_univ_four]`. Break down `this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩` into its components or cases. Rewrite using `[z g 2 1 (by decide) (by decide), z g 2 3 (by decide) (by decide)]; ring`. Rewrite using `[z h 0 1 (by decide) (by decide), z h 2 1 (by decide) (by decide)]; ring`.

Assume the negation of the conclusion as `hn`. Take `⟨g, i, j, hw, hg⟩` from `hs.be`. Establish `: i = 1 ∧ j = 2` using `by clear hg; revert i j; decide`. Take `⟨rfl, rfl⟩` from `this`. Use `hg (key 1 2 (by decide) (fun g h => ?_) (fun g => by_contra fun h => hn ⟨g, 1, 2, hw, h⟩) g)` and prove the remaining obligations.

Rewrite using `[map_mul, Matrix.mul_apply, Fin.sum_univ_four, z h 0 2 (by decide) (by decide), z g 1 3 (by decide) (by decide)]`. Expand and normalize the polynomial expressions, which then agree. Use `right`. Establish `y0 : ∀ g, s.r g 2 0 = 0` using `fun g => hv g 2 0 (by decide) (by decide)`. Use `⟨⟨fun g => by rw [hre]; exact hv _, fun v => ⟨hq v, fun h => ?_⟩⟩, ?_⟩` and prove the remaining obligations.

Take `⟨g, -, e⟩` from `ff v`. Establish `h' : s'.n v 2 0 = 0` using `h`. Rewrite `e` using `[h', y0, zero_mul, zero_add]`. Conclude with `mul_ne_zero (ne0 g 2) h20 e.symm`. Assume the negation of the conclusion as `hn`.

Establish `x0 : ∀ g, s.r g 1 0 = 0`. Use `key 1 0 (by decide) (fun g h => ?_) (fun g => by_contra fun h => hn ⟨g, 1, 0, by decide, h⟩)` and prove the remaining obligations. Rewrite using `[map_mul, Matrix.mul_apply, Fin.sum_univ_four, y0, z g 1 3 (by decide) (by decide)]`. Expand and normalize the polynomial expressions, which then agree. Use `hnc ⟨s.n () 1 0 / s.n () 2 0, fun g hg => ?_⟩` and prove the remaining obligations.

Take `⟨-, e1, e2⟩` from `flag_facts (s.n ()) (s.n ()) (s.r g) low hs.flag low (hs.supp g) (ne0 g 1) (hs.res.pair.flag () g hg)`. Rewrite `e1` using `[y0, zero_add, mul_comm]`. Establish `e3` using `mul_right_cancel₀ h20 e1`. Rewrite `e2` using `[x0, e3]`. Rewrite using `[← diag, ← diag]`.

Clear the denominators using the available nonvanishing facts. Take the linear combination `-e2`.
-/
theorem UpperTheory.V.Ws.goodQ :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ T : Tower D, T.Fit → ∀ (k : Type) [Field k] (a : c.O →+* k), (∀ x ∈ maximalIdeal c.O, a x = 0) → ∀ (g0 : G ℚ Ω) (s : PD Unit (G ℚ Ω) k) (s' : PD T.ι (G T.F Ω) k), LatShape D T.pr g0 a s → (∀ w ∈ roots, a ((frQ D T.pr g0).rt w g0) ≠ 1) →
      T.OverQ s s' → (T.fr ∅).IsRes a s' → ∀ W : Finset ℕ, (T.fr W).IsRes a s' ∧ s'.In nP ∧
        (Ent s'.r (-wPs) ∧ Ent s'.r wBe ∨ Fr.InV (Φ := T.fr ∅) s' ∧ Ent s'.r (-wAl)) := by
  intro Ω _ _ _ l _ c D _ T hT k _ a _ g0 s s' hs _ hov hres W
  obtain ⟨hr, hfl⟩ := hov
  have hre : ∀ g, s'.r g = s.r (resQ T.F g) := fun g => by rw [hr]; rfl
  have diag : ∀ g i, s.r g i i = a (chi D T.pr i g) := hs.res.res.diag
  have ne0 : ∀ g i, s.r g i i ≠ 0 := fun g i => by
    rw [diag]; exact ((chi D T.pr i g).isUnit.map a).ne_zero
  have low : IsLow (s.n ()) := hs.res.pair.low ()
  have low' : ∀ v, IsLow (s'.n v) := hres.pair.low

  have key : ∀ i j, i ≠ j → (∀ g h, s.r (g * h) i j = s.r g i i * s.r h i j + s.r g i j * s.r h j j) →
      (∀ g, s'.r g i j = 0) → ∀ g, s.r g i j = 0 := by
    intro i j hij hc h0
    refine coc_zero a (chi D T.pr i) (chi D T.pr j) (fun g => s.r g i j) (fun g h => by rw [hc, diag, diag])
      (resQ T.F T.g0) (ne_of_res a (hT.1.dist i j hij)) fun g => ?_
    obtain ⟨h', e⟩ := conj_mem T.F T.g0 g
    rw [← e, ← hre]
    exact h0 h'
  have z : ∀ g i j, i ≠ j → wt i j ∉ nP → s.r g i j = 0 := hs.supp
  have ff : ∀ v, ∃ g, s'.n v 2 1 = 0 ∧ s'.n v 2 0 * s.r g 0 0 = s.r g 2 0 + s.r g 2 2 * s.n () 2 0 := by
    intro v
    obtain ⟨u, g, -, hu⟩ := hfl v
    have := flag_facts (s.n ()) (s'.n v) (s.r g) low hs.flag (low' v) (hs.supp g) (ne0 g 1) hu
    exact ⟨g, this.1, this.2.1⟩
  have hq : ∀ v, SuppM qQ (s'.n v) := by
    intro v i j hij hw
    obtain ⟨g, h21, -⟩ := ff v
    have : i < j ∨ (i = 2 ∧ j = 1) := by revert i j; decide
    rcases this with h | ⟨rfl, rfl⟩
    · exact (low' v).2.2 i j h
    · exact h21
  refine ⟨⟨⟨hres.pair.mult, fun g hg => hres.pair.kill g ?_, hres.pair.nrm, hres.pair.low, hres.pair.flag, hres.pair.mu⟩,
    ⟨hres.res.diag, hres.res.char, hres.res.shape⟩, hres.cont⟩, ⟨fun g => by rw [hre]; exact hs.supp _, hq⟩, ?_⟩
  · obtain ⟨A, hA, h⟩ := hg
    exact ⟨A, fun p hp => hA p (Finset.insert_subset_insert l (Finset.empty_subset W) hp), h⟩
  rcases hs.ps with hps | ⟨hv, h20, -, hnc⟩
  · left
    constructor
    · by_contra hn
      obtain ⟨g, i, j, hw, hg⟩ := hps
      refine hg (key i j ?_ (fun g h => ?_) (fun g => by_contra fun h => hn ⟨g, i, j, hw, h⟩) g)
      · clear hg; revert i j; decide
      · have : (i = 2 ∧ j = 0) ∨ (i = 3 ∧ j = 1) := by clear hg; revert i j; decide
        rw [map_mul, Matrix.mul_apply, Fin.sum_univ_four]
        rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rw [z g 2 1 (by decide) (by decide), z g 2 3 (by decide) (by decide)]; ring
        · rw [z h 0 1 (by decide) (by decide), z h 2 1 (by decide) (by decide)]; ring
    · by_contra hn
      obtain ⟨g, i, j, hw, hg⟩ := hs.be
      have : i = 1 ∧ j = 2 := by clear hg; revert i j; decide
      obtain ⟨rfl, rfl⟩ := this
      refine hg (key 1 2 (by decide) (fun g h => ?_) (fun g => by_contra fun h => hn ⟨g, 1, 2, hw, h⟩) g)
      rw [map_mul, Matrix.mul_apply, Fin.sum_univ_four, z h 0 2 (by decide) (by decide), z g 1 3 (by decide) (by decide)]
      ring
  · right
    have y0 : ∀ g, s.r g 2 0 = 0 := fun g => hv g 2 0 (by decide) (by decide)
    refine ⟨⟨fun g => by rw [hre]; exact hv _, fun v => ⟨hq v, fun h => ?_⟩⟩, ?_⟩
    · obtain ⟨g, -, e⟩ := ff v
      have h' : s'.n v 2 0 = 0 := h
      rw [h', y0, zero_mul, zero_add] at e
      exact mul_ne_zero (ne0 g 2) h20 e.symm
    · by_contra hn
      have x0 : ∀ g, s.r g 1 0 = 0 := by
        refine key 1 0 (by decide) (fun g h => ?_) (fun g => by_contra fun h => hn ⟨g, 1, 0, by decide, h⟩)
        rw [map_mul, Matrix.mul_apply, Fin.sum_univ_four, y0, z g 1 3 (by decide) (by decide)]
        ring
      refine hnc ⟨s.n () 1 0 / s.n () 2 0, fun g hg => ?_⟩
      obtain ⟨-, e1, e2⟩ := flag_facts (s.n ()) (s.n ()) (s.r g) low hs.flag low (hs.supp g) (ne0 g 1)
        (hs.res.pair.flag () g hg)
      rw [y0, zero_add, mul_comm] at e1
      have e3 := mul_right_cancel₀ h20 e1
      rw [x0, e3] at e2
      rw [← diag, ← diag]
      field_simp
      linear_combination -e2
