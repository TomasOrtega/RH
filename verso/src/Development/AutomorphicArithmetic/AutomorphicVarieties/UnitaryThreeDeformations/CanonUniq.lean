import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

/- English proof (translation)
Set `φ` to `residue R`. Establish `h0 : φ.mapMatrix (h.val - 1) = 0`. Use extensionality with `a b`. Conclude with `(residue_eq_zero_iff _).2 (hc.hat a b)`. Establish `hh : φ.mapMatrix h.val = 1`.

Rewrite `h0` using `[map_sub, map_one, sub_eq_zero]`. Conclude with `h0`. Establish `hhi : φ.mapMatrix h⁻¹.val = 1`. Establish `e : φ.mapMatrix h⁻¹.val * φ.mapMatrix h.val = 1`. Rewrite using `[← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]`.

Rewrite `e` using `[hh, mul_one]`. Then use the resulting hypothesis. Use `⟨fun a => (h⁻¹.val * X * h.val) a a, hc.diag.diagonal_diag.symm, ?_⟩` and prove the remaining obligations. Introduce `a`. Rewrite using `[← residue_eq_zero_iff, map_sub, sub_eq_zero]`. Establish `e : φ.mapMatrix (h⁻¹.val * X * h.val) = φ.mapMatrix X`.

Rewrite using `[map_mul, map_mul, hh, hhi, one_mul, mul_one]`. Conclude with `congrFun (congrFun e a) a`.
-/
private theorem canon_eig {R : Type} [CommRing R] [IsLocalRing R] (X : Matrix (Fin 3) (Fin 3) R)
    (h : GL (Fin 3) R) (hc : Canon X h) :
    ∃ d : Fin 3 → R, ((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * X * h = diagonal d ∧
      ∀ a, d a - X a a ∈ maximalIdeal R := by
  let φ := residue R
  have h0 : φ.mapMatrix (h.val - 1) = 0 := by
    ext a b
    exact (residue_eq_zero_iff _).2 (hc.hat a b)
  have hh : φ.mapMatrix h.val = 1 := by
    rw [map_sub, map_one, sub_eq_zero] at h0
    exact h0
  have hhi : φ.mapMatrix h⁻¹.val = 1 := by
    have e : φ.mapMatrix h⁻¹.val * φ.mapMatrix h.val = 1 := by
      rw [← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
    rwa [hh, mul_one] at e
  refine ⟨fun a => (h⁻¹.val * X * h.val) a a, hc.diag.diagonal_diag.symm, ?_⟩
  intro a
  rw [← residue_eq_zero_iff, map_sub, sub_eq_zero]
  have e : φ.mapMatrix (h⁻¹.val * X * h.val) = φ.mapMatrix X := by
    rw [map_mul, map_mul, hh, hhi, one_mul, mul_one]
  exact congrFun (congrFun e a) a

/- English proof (translation)
Introduce `R _ _ X h h' hX hc hc'`. Take `⟨d, hd, hdX⟩` from `canon_eig X h hc`. Take `⟨d', hd', hd'X⟩` from `canon_eig X h' hc'`. Set `g : GL (Fin 3) R` to `h⁻¹ * h'`. Establish `key : diagonal d * g.val = g.val * diagonal d'`.

Rewrite using `[← hd, ← hd']`. Simplify using `only [g, Units.val_mul, Matrix.mul_assoc, Units.mul_inv_cancel_left]`. Establish `hg : ∀ a b, a ≠ b → g.val a b = 0`. Introduce `a b hab`. Establish `e` using `congrFun (congrFun key a) b`.

Rewrite `e` using `[Matrix.diagonal_mul, Matrix.mul_diagonal]`. Establish `hu : IsUnit (d a - d' b)`. Assume the negation of the conclusion as `hn`. Establish `hm : d a - d' b ∈ maximalIdeal R` using `hn`. Establish `hm2 : X a a - X b b ∈ maximalIdeal R`.

Establish `e2 : X a a - X b b = (d a - d' b) - (d a - X a a) + (d' b - X b b)` using `by ring`. Rewrite using `[e2]`. Conclude with `add_mem (sub_mem hm (hdX a)) (hd'X b)`. Conclude with `hm2 (hX a b hab)`. Establish `e3 : g.val a b * (d a - d' b) = 0`.

Rewrite using `[mul_sub, mul_comm (g.val a b) (d a), e, sub_self]`. Conclude with `hu.mul_left_eq_zero.1 e3`. Establish `hh' : h'.val = h.val * g.val`. Simplify using `only [g, Units.val_mul, Units.mul_inv_cancel_left]`. Establish `g1 : g.val = 1`.

Use extensionality with `a b`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Rewrite using `[Matrix.one_apply_eq]`. Establish `e` using `congrFun (congrFun hh' a) a`.

Rewrite `e` using `[Matrix.mul_apply, Finset.sum_eq_single a (fun c _ hc => by rw [hg c a hc, mul_zero]) (by simp), hc'.one a, hc.one a, one_mul]`. Conclude with `e.symm`. Rewrite using `[Matrix.one_apply_ne hab, hg a b hab]`. Establish `g1' : g = 1` using `Units.ext g1`. Conclude with `inv_mul_eq_one.1 g1'`.
-/
theorem UpperTheory.V.UnitaryThreeInertia.canon_unique :
    ∀ {R : Type} [CommRing R] [IsLocalRing R] (X : Matrix (Fin 3) (Fin 3) R) (h h' : GL (Fin 3) R), (∀ a b, a ≠ b → IsUnit (X a a - X b b)) → Canon X h → Canon X h' → h = h' := by
  intro R _ _ X h h' hX hc hc'
  obtain ⟨d, hd, hdX⟩ := canon_eig X h hc
  obtain ⟨d', hd', hd'X⟩ := canon_eig X h' hc'
  let g : GL (Fin 3) R := h⁻¹ * h'
  have key : diagonal d * g.val = g.val * diagonal d' := by
    rw [← hd, ← hd']
    simp only [g, Units.val_mul, Matrix.mul_assoc, Units.mul_inv_cancel_left]
  have hg : ∀ a b, a ≠ b → g.val a b = 0 := by
    intro a b hab
    have e := congrFun (congrFun key a) b
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at e
    have hu : IsUnit (d a - d' b) := by
      by_contra hn
      have hm : d a - d' b ∈ maximalIdeal R := hn
      have hm2 : X a a - X b b ∈ maximalIdeal R := by
        have e2 : X a a - X b b = (d a - d' b) - (d a - X a a) + (d' b - X b b) := by ring
        rw [e2]
        exact add_mem (sub_mem hm (hdX a)) (hd'X b)
      exact hm2 (hX a b hab)
    have e3 : g.val a b * (d a - d' b) = 0 := by
      rw [mul_sub, mul_comm (g.val a b) (d a), e, sub_self]
    exact hu.mul_left_eq_zero.1 e3
  have hh' : h'.val = h.val * g.val := by
    simp only [g, Units.val_mul, Units.mul_inv_cancel_left]
  have g1 : g.val = 1 := by
    ext a b
    by_cases hab : a = b
    · subst hab
      rw [Matrix.one_apply_eq]
      have e := congrFun (congrFun hh' a) a
      rw [Matrix.mul_apply, Finset.sum_eq_single a (fun c _ hc => by rw [hg c a hc, mul_zero])
        (by simp), hc'.one a, hc.one a, one_mul] at e
      exact e.symm
    · rw [Matrix.one_apply_ne hab, hg a b hab]
  have g1' : g = 1 := Units.ext g1
  exact inv_mul_eq_one.1 g1'
