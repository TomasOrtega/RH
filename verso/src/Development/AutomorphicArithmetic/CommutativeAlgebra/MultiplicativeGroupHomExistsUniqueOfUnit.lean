import Development.AutomorphicArithmetic.CupPullbacks.ConstCompSingle
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LocalQuotientHomExt
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC UpperTheory.Pbf

namespace UpperTheory.GqPt

/- English proof (translation)
Take `⟨k, rfl | rfl⟩` from `n.eq_nat_or_neg`. Rewrite using `[zpow_natCast, Units.val_pow_eq_pow_val]`. Express the relevant statement in the definitionally equal form `(LaurentPolynomial.T 1 : LqR q) ^ k = _`. Rewrite using `[LaurentPolynomial.T_pow]`. Simplify using the standard rewrite rules.

Rewrite using `[zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val]`. Express the relevant statement in the definitionally equal form `(LaurentPolynomial.T (-1) : LqR q) ^ k = _`. Rewrite using `[LaurentPolynomial.T_pow]`. Simplify using the standard rewrite rules.
-/
private theorem tR_zpow (q : ℕ) (n : ℤ) :
    (((tR q) ^ n : (LqR q)ˣ) : LqR q) = LaurentPolynomial.T n := by
  obtain ⟨k, rfl | rfl⟩ := n.eq_nat_or_neg
  · rw [zpow_natCast, Units.val_pow_eq_pow_val]
    change (LaurentPolynomial.T 1 : LqR q) ^ k = _
    rw [LaurentPolynomial.T_pow]; simp
  · rw [zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val]
    change (LaurentPolynomial.T (-1) : LqR q) ^ k = _
    rw [LaurentPolynomial.T_pow]; simp

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.LocalQuotientHomExt.hom_ext q h`.
-/
private theorem hom_ext (q : ℕ) {R : Type} [CommRing R] {f g : LqR q →+* R}
    (h : f (LaurentPolynomial.T 1) = g (LaurentPolynomial.T 1)) : f = g :=
  _root_.UpperTheory.Reformulated.B.LocalQuotientHomExt.hom_ext q h

private noncomputable def sec {X : Scheme.{0}} {R : CommRingCat.{0}} (f : X ⟶ Spec R) : R ⟶ Γ(X, ⊤) :=
  (Scheme.ΓSpecIso R).inv ≫ f.appTop

/- English proof (translation)
The claim follows from `ext_of_isAffine ((cancel_epi (Scheme.ΓSpecIso R).inv).1 h)`.
-/
private theorem sec_inj {X : Scheme.{0}} {R : CommRingCat.{0}} {f g : X ⟶ Spec R} (h : sec f = sec g) : f = g :=
  ext_of_isAffine ((cancel_epi (Scheme.ΓSpecIso R).inv).1 h)

/- English proof (translation)
Simplify using `only [sec, Scheme.Hom.comp_appTop]`. Rewrite using `[← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc, Scheme.toSpecΓ_appTop, Iso.inv_hom_id, Category.comp_id]`.
-/
private theorem sec_to {X : Scheme.{0}} {R : CommRingCat.{0}} (φ : R ⟶ Γ(X, ⊤)) :
    sec (X.toSpecΓ ≫ Spec.map φ) = φ := by
  simp only [sec, Scheme.Hom.comp_appTop]
  rw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc,
    Scheme.toSpecΓ_appTop, Iso.inv_hom_id, Category.comp_id]

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem val_map_tq (q : ℕ) {T : Scheme.{0}} (s : T ⟶ Gq q) :
    ((Units.map s.appTop.hom.toMonoidHom (tq q) : (Γ(T, ⊤))ˣ) : Γ(T, ⊤)) =
      (sec s).hom (LaurentPolynomial.T 1) := rfl

end UpperTheory.GqPt

open UpperTheory.GqPt in
/- English proof (translation)
Introduce `q _ T hq t`. Set `lam : Localization.Away (q : ℤ) →+* Γ(T, ⊤)` to `IsLocalization.Away.lift (q : ℤ) (g := Int.castRingHom Γ(T, ⊤)) (by simpa using hq)`. Set `φ : LqR q →+* Γ(T, ⊤)` to `LaurentPolynomial.eval₂ lam t`. Establish `hφ : φ (LaurentPolynomial.T 1) = t`. Simplify using `only [φ, LaurentPolynomial.eval₂_T, zpow_one]`.

Use `⟨T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ), ?_, ?_⟩` and prove the remaining obligations. Use `Units.ext ?_` and prove the remaining obligations. Rewrite using `[val_map_tq, sec_to]`. Conclude with `hφ`. Introduce `s hs`.

Use `sec_inj ?_` and prove the remaining obligations. Rewrite using `[sec_to]`. Use `CommRingCat.hom_ext (hom_ext q ?_)` and prove the remaining obligations. Establish `h1` using `val_map_tq q s`. Rewrite `h1` using `[hs]`.

Conclude with `h1.symm.trans hφ.symm`.
-/
theorem UpperTheory.multiplicativeGroup_hom_existsUnique_of_unit :
    ∀ (q : ℕ) [NeZero q] (T : Scheme.{0}), IsUnit ((q : ℕ) : Γ(T, ⊤)) → ∀ t : (Γ(T, ⊤))ˣ, ∃! s : T ⟶ Gq q, Units.map s.appTop.hom.toMonoidHom (tq q) = t := by
  intro q _ T hq t
  let lam : Localization.Away (q : ℤ) →+* Γ(T, ⊤) :=
    IsLocalization.Away.lift (q : ℤ) (g := Int.castRingHom Γ(T, ⊤)) (by simpa using hq)
  let φ : LqR q →+* Γ(T, ⊤) := LaurentPolynomial.eval₂ lam t
  have hφ : φ (LaurentPolynomial.T 1) = t := by
    simp only [φ, LaurentPolynomial.eval₂_T, zpow_one]
  refine ⟨T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ), ?_, ?_⟩
  · refine Units.ext ?_
    rw [val_map_tq, sec_to]
    exact hφ
  · intro s hs
    refine sec_inj ?_
    rw [sec_to]
    refine CommRingCat.hom_ext (hom_ext q ?_)
    have h1 := val_map_tq q s
    rw [hs] at h1
    exact h1.symm.trans hφ.symm
