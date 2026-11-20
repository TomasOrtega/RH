import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.IsConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

/- English proof (translation)
Take `⟨r, hr⟩` from `exists_add_pow_prime_eq hp (a - b) b`. Rewrite `hr` using `[sub_add_cancel, e, h]`. Establish `h0 : (a - b) ^ p = 0`. Simplify using `using hr.symm`. Conclude with `sub_eq_zero.mp (IsReduced.pow_eq_zero h0)`.
-/
private theorem pow_inj {R : Type*} [CommRing R] [_root_.IsReduced R] {p : ℕ} (hp : p.Prime)
    (h : (p : R) = 0) {a b : R} (e : a ^ p = b ^ p) : a = b := by
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp (a - b) b
  rw [sub_add_cancel, e, h] at hr
  have h0 : (a - b) ^ p = 0 := by
    simpa using hr.symm
  exact sub_eq_zero.mp (IsReduced.pow_eq_zero h0)

/- English proof (translation)
Establish `ha` using `ConcreteCategory.congr_hom hU a`. Simplify using `only [ConcreteCategory.comp_apply, hB, hC, map_pow] at ha`. Simplify using `using ha.symm`.
-/
private theorem step {p : ℕ} {A B C : CommRingCat} (u : A ⟶ B) (v : A ⟶ C) (FB : B ⟶ B) (FC : C ⟶ C)
    (r : B ⟶ C) (hB : ∀ x, FB x = x ^ p) (hC : ∀ x, FC x = x ^ p)
    (hU : v ≫ FC = (u ≫ FB) ≫ r) (a : A) : (u ≫ r).hom a ^ p = v.hom a ^ p := by
  have ha := ConcreteCategory.congr_hom hU a
  simp only [ConcreteCategory.comp_apply, hB, hC, map_pow] at ha
  simpa using ha.symm

/- English proof (translation)
Establish `hV (V : X.Opens) : (p : Γ(X, V)) = 0`. Use `congrArg (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom h` as an intermediate fact. Simplify using `using this`. Use `⟨fun {Y} f g e => ?_⟩` and prove the remaining obligations. Establish `hx (x : X) : f x = g x`.

Use `congrArg (fun φ : X ⟶ Y => φ x) e` as an intermediate fact. Simplify using `using this`. Use `Scheme.Hom.ext (by ext x; exact hx x) fun U => ?_` and prove the remaining obligations. Establish `hU` using `Scheme.Hom.congr_app e.symm U`. Rewrite `hU` using `[Scheme.Hom.comp_app, Scheme.Hom.comp_app]`.

Use extensionality with `a`. Apply `pow_inj (Fact.out : p.Prime) (hV _)` to reduce the goal to its premises. Conclude with `step (p := p) (f.app U) (g.app U) ((GlobalTheory.VB.frob X p h).app (f ⁻¹ᵁ U)) ((GlobalTheory.VB.frob X p h).app (g ⁻¹ᵁ U)) _ (GlobalTheory.VB.frob_app p h _) (GlobalTheory.VB.frob_app p h _) hU a`.
-/
private theorem frob_epi (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) [IsReduced X]
    (h : (p : Γ(X, ⊤)) = 0) : Epi (GlobalTheory.VB.frob X p h) := by
  have hV (V : X.Opens) : (p : Γ(X, V)) = 0 := by
    have := congrArg (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom h
    simpa using this
  refine ⟨fun {Y} f g e => ?_⟩
  have hx (x : X) : f x = g x := by
    have := congrArg (fun φ : X ⟶ Y => φ x) e
    simpa using this
  refine Scheme.Hom.ext (by ext x; exact hx x) fun U => ?_
  have hU := Scheme.Hom.congr_app e.symm U
  rw [Scheme.Hom.comp_app, Scheme.Hom.comp_app] at hU
  ext a
  apply pow_inj (Fact.out : p.Prime) (hV _)
  exact step (p := p) (f.app U) (g.app U) ((GlobalTheory.VB.frob X p h).app (f ⁻¹ᵁ U))
    ((GlobalTheory.VB.frob X p h).app (g ⁻¹ᵁ U)) _ (GlobalTheory.VB.frob_app p h _) (GlobalTheory.VB.frob_app p h _) hU a

/- English proof (translation)
Introduce `p _ X _ h`. Establish `hF` using `frob_epi p X h`. Use `⟨hF, fun j => ?_⟩` and prove the remaining obligations. Proceed by induction on `j with`. Consider the case `zero => exact (inferInstance : Epi (𝟙 X))`.

Consider the case `succ j ih`. Establish `: Epi (frobN p X h j)` using `ih`. Conclude with `epi_comp (GlobalTheory.VB.frob X p h) (frobN p X h j)`.
-/
theorem UpperTheory.Gal.Ord.epi :
    ∀ (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) [IsReduced X] (h : (p : Γ(X, ⊤)) = 0), Epi (GlobalTheory.VB.frob X p h) ∧ ∀ j, Epi (frobN p X h j) := by
  intro p _ X _ h
  have hF := frob_epi p X h
  refine ⟨hF, fun j => ?_⟩
  induction j with
  | zero => exact (inferInstance : Epi (𝟙 X))
  | succ j ih =>
    have : Epi (frobN p X h j) := ih
    exact epi_comp (GlobalTheory.VB.frob X p h) (frobN p X h j)
