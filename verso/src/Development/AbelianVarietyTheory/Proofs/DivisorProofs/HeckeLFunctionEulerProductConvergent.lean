import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnimodularSolCoords
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory.CMTorsion
open GlobalTheory.WeierstrassCurve (scheme toSpec mapHom)

/- English proof (translation)
Introduce `G G' _ _ _ _ g p h`. Take `⟨hpb, hmul⟩` from `h`. Establish `h1 : ∀ P Q : 𝟙_ (Over (Sp ℂ)) ⟶ G', P.left ≫ p = Q.left ≫ p → P = Q`. Introduce `P Q hPQ`. Establish `hw : P.left ≫ G'.hom = Q.left ≫ G'.hom` using `by rw [Over.w P, Over.w Q]`.

Conclude with `Over.OverMorphism.ext (hpb.hom_ext hPQ hw)`. Establish `h2 : ∀ (P Q : 𝟙_ (Over (Sp ℂ)) ⟶ G) (P' Q' : 𝟙_ (Over (Sp ℂ)) ⟶ G'), P'.left ≫ p = spMap (g : ℂ →+* ℂ) ≫ P.left → Q'.left ≫ p = spMap (g : ℂ →+* ℂ) ≫ Q.left → (P' * Q').left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (P * Q).left`. Introduce `P Q P' Q' hP hQ`. Set `u : Over.mk ((𝟙_ (Over (Sp ℂ))).hom ≫ spMap (g : ℂ →+* ℂ)) ⟶ 𝟙_ (Over (Sp ℂ))` to `toUnit _`. Establish `hu : u.left = spMap (g : ℂ →+* ℂ)`.

Use `Over.w u` as an intermediate fact. Simplify using `using this`. Establish `key` using `hmul (𝟙_ (Over (Sp ℂ))) P' Q' (u ≫ P) (u ≫ Q) (by simp [hu, hP]) (by simp [hu, hQ])`. Rewrite using `[← key, ← MonObj.comp_mul]`. Simplify using `[hu]`.

Establish `h0 : (1 : 𝟙_ (Over (Sp ℂ)) ⟶ G').left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (1 : 𝟙_ (Over (Sp ℂ)) ⟶ G).left`. Establish `hw : (spMap (g : ℂ →+* ℂ) ≫ (1 : 𝟙_ (Over (Sp ℂ)) ⟶ G).left) ≫ G.hom = 𝟙 _ ≫ spMap (g : ℂ →+* ℂ)`. Rewrite using `[Category.assoc, Over.w]`. Simplify using the standard rewrite rules. Set `e' : Sp ℂ ⟶ G'.left` to `hpb.lift _ _ hw`.

Establish `he' : e' ≫ G'.hom = (𝟙_ (Over (Sp ℂ))).hom`. Simplify using `only [e', IsPullback.lift_snd]`. Both sides reduce to the same expression. Set `E' : 𝟙_ (Over (Sp ℂ)) ⟶ G'` to `Over.homMk e' he'`. Establish `hE : E'.left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (1 : 𝟙_ (Over (Sp ℂ)) ⟶ G).left`.

Simplify using `[E', e']`. Establish `hEE : E' * E' = E'`. Apply `h1` to reduce the goal to its premises. Rewrite using `[h2 1 1 E' E' hE hE, hE, _root_.mul_one (1 : 𝟙_ (Over (Sp ℂ)) ⟶ G)]`. Establish `: E' = 1` using `mul_eq_left.mp hEE`.

Rewrite using `[← this, hE]`. Use `⟨h1, h2, ?_⟩` and prove the remaining obligations. Introduce `J s P P' hs`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using h0`.

Consider the case `insert a s ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.prod_insert ha]`. Conclude with `h2 _ _ _ _ (hs a (Finset.mem_insert_self a s)) (ih fun i hi => hs i (Finset.mem_insert_of_mem hi))`.
-/
theorem GlobalTheory.GrpPullback.points_conj : ∀ (G G' : Over (Sp ℂ)) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (g : ℂ ≃+* ℂ) (p : G'.left ⟶ G.left), IsGrpPullback G' G (spMap (g : ℂ →+* ℂ)) p → (∀ P Q : 𝟙_ (Over (Sp ℂ)) ⟶ G', P.left ≫ p = Q.left ≫ p → P = Q) ∧ (∀ (P Q : 𝟙_ (Over (Sp ℂ)) ⟶ G) (P' Q' : 𝟙_ (Over (Sp ℂ)) ⟶ G'), P'.left ≫ p = spMap (g : ℂ →+* ℂ) ≫ P.left → Q'.left ≫ p = spMap (g : ℂ →+* ℂ) ≫ Q.left → (P' * Q').left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (P * Q).left) ∧ ∀ (J : Type) (s : Finset J) (P : J → (𝟙_ (Over (Sp ℂ)) ⟶ G)) (P' : J → (𝟙_ (Over (Sp ℂ)) ⟶ G')), (∀ i ∈ s, (P' i).left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (P i).left) → (∏ i ∈ s, P' i : 𝟙_ (Over (Sp ℂ)) ⟶ G').left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (∏ i ∈ s, P i : 𝟙_ (Over (Sp ℂ)) ⟶ G).left := by
  intro G G' _ _ _ _ g p h
  obtain ⟨hpb, hmul⟩ := h
  have h1 : ∀ P Q : 𝟙_ (Over (Sp ℂ)) ⟶ G', P.left ≫ p = Q.left ≫ p → P = Q := by
    intro P Q hPQ
    have hw : P.left ≫ G'.hom = Q.left ≫ G'.hom := by rw [Over.w P, Over.w Q]
    exact Over.OverMorphism.ext (hpb.hom_ext hPQ hw)
  have h2 : ∀ (P Q : 𝟙_ (Over (Sp ℂ)) ⟶ G) (P' Q' : 𝟙_ (Over (Sp ℂ)) ⟶ G'),
      P'.left ≫ p = spMap (g : ℂ →+* ℂ) ≫ P.left → Q'.left ≫ p = spMap (g : ℂ →+* ℂ) ≫ Q.left →
      (P' * Q').left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (P * Q).left := by
    intro P Q P' Q' hP hQ
    let u : Over.mk ((𝟙_ (Over (Sp ℂ))).hom ≫ spMap (g : ℂ →+* ℂ)) ⟶ 𝟙_ (Over (Sp ℂ)) := toUnit _
    have hu : u.left = spMap (g : ℂ →+* ℂ) := by
      have := Over.w u
      simpa using this
    have key := hmul (𝟙_ (Over (Sp ℂ))) P' Q' (u ≫ P) (u ≫ Q) (by simp [hu, hP]) (by simp [hu, hQ])
    rw [← key, ← MonObj.comp_mul]
    simp [hu]
  have h0 : (1 : 𝟙_ (Over (Sp ℂ)) ⟶ G').left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (1 : 𝟙_ (Over (Sp ℂ)) ⟶ G).left := by
    have hw : (spMap (g : ℂ →+* ℂ) ≫ (1 : 𝟙_ (Over (Sp ℂ)) ⟶ G).left) ≫ G.hom = 𝟙 _ ≫ spMap (g : ℂ →+* ℂ) := by
      rw [Category.assoc, Over.w]; simp
    let e' : Sp ℂ ⟶ G'.left := hpb.lift _ _ hw
    have he' : e' ≫ G'.hom = (𝟙_ (Over (Sp ℂ))).hom := by
      simp only [e', IsPullback.lift_snd]; rfl
    let E' : 𝟙_ (Over (Sp ℂ)) ⟶ G' := Over.homMk e' he'
    have hE : E'.left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (1 : 𝟙_ (Over (Sp ℂ)) ⟶ G).left := by
      simp [E', e']
    have hEE : E' * E' = E' := by
      apply h1
      rw [h2 1 1 E' E' hE hE, hE, _root_.mul_one (1 : 𝟙_ (Over (Sp ℂ)) ⟶ G)]
    have : E' = 1 := mul_eq_left.mp hEE
    rw [← this, hE]
  refine ⟨h1, h2, ?_⟩
  intro J s P P' hs
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact h2 _ _ _ _ (hs a (Finset.mem_insert_self a s)) (ih fun i hi => hs i (Finset.mem_insert_of_mem hi))
