import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

/- English proof (translation)
Introduce `hG hT B G _ X R _ _ T hgood m j hmj`. Prove the components needed by the constructor for the conclusion. Take `⟨m', hm'j, hnorm, hS⟩` from `X.deep j {(m, 1)}`. Establish `hm'm : X.K m' ≤ X.K m` using `fun u hu => by simpa using hS (m, 1) (by simp) u hu`. Take `⟨Γ, _, _, r, c, hr, huniq, hgal⟩` from `hT X m' j (X.isAdmissibleIntegralBasisChange_one hm'j) hnorm`.

Establish `hinj` using `hgood.inj (X.q j) (X.q m') _ (X.tr_q m' j 1 _ _) Γ _ hgal`. Establish `key : ∀ z, X.pl T m' j 1 z = X.pl T m' m 1 (X.pl T m j 1 z)` using `fun z => by`. Rewrite using `[X.pl_pl T (X.isAdmissibleIntegralBasisChange_one hm'm) (X.isAdmissibleIntegralBasisChange_one hmj), one_mul]`. Introduce `x y hxy`. Apply `hinj` to reduce the goal to its premises.

Rewrite using `[← X.pl_eq T (X.isAdmissibleIntegralBasisChange_one hm'j), key, key, hxy]`. Introduce `hnorm y hy`. Take `⟨Γ, _, _, r, c, hr, huniq, hgal⟩` from `hT X m j (X.isAdmissibleIntegralBasisChange_one hmj) hnorm`. Establish `ha : ∀ g : Γ, X.tr m m (r g) (c g).1 (c g).2 ≫ X.q m = X.q m` using `fun g => X.tr_q _ _ _ _ _`. Establish `hsurj` using `(hG T hgood (X.q j) (X.q m) _ (X.tr_q m j 1 _ _) Γ _ ha hgal y).2`.

Take `⟨x, hx⟩` from `hsurj (fun g => by rw [← X.pl_eq T (c g)]; exact hy _ (hr g))`. Conclude with `⟨x, by rw [X.pl_eq T (X.isAdmissibleIntegralBasisChange_one hmj)]; exact hx⟩`.
-/
theorem UpperTheory.Gal.G3.pPlInv :
    GalInv.{u} → TwGal → PlInv.{u} := by
  intro hG hT B G _ X R _ _ T hgood m j hmj
  constructor
  · obtain ⟨m', hm'j, hnorm, hS⟩ := X.deep j {(m, 1)}
    have hm'm : X.K m' ≤ X.K m := fun u hu => by simpa using hS (m, 1) (by simp) u hu
    obtain ⟨Γ, _, _, r, c, hr, huniq, hgal⟩ := hT X m' j (X.isAdmissibleIntegralBasisChange_one hm'j) hnorm
    have hinj := hgood.inj (X.q j) (X.q m') _ (X.tr_q m' j 1 _ _) Γ _ hgal
    have key : ∀ z, X.pl T m' j 1 z = X.pl T m' m 1 (X.pl T m j 1 z) := fun z => by
      rw [X.pl_pl T (X.isAdmissibleIntegralBasisChange_one hm'm) (X.isAdmissibleIntegralBasisChange_one hmj), one_mul]
    intro x y hxy
    apply hinj
    rw [← X.pl_eq T (X.isAdmissibleIntegralBasisChange_one hm'j), key, key, hxy]
  · intro hnorm y hy
    obtain ⟨Γ, _, _, r, c, hr, huniq, hgal⟩ := hT X m j (X.isAdmissibleIntegralBasisChange_one hmj) hnorm
    have ha : ∀ g : Γ, X.tr m m (r g) (c g).1 (c g).2 ≫ X.q m = X.q m := fun g => X.tr_q _ _ _ _ _
    have hsurj := (hG T hgood (X.q j) (X.q m) _ (X.tr_q m j 1 _ _) Γ _ ha hgal y).2
    obtain ⟨x, hx⟩ := hsurj (fun g => by rw [← X.pl_eq T (c g)]; exact hy _ (hr g))
    exact ⟨x, by rw [X.pl_eq T (X.isAdmissibleIntegralBasisChange_one hmj)]; exact hx⟩
