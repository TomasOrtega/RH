import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitTorusPointsMulEquiv
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero`. Simplify using `only [Nat.mul_zero, pow_zero, pow_one]`. Express the relevant statement in the definitionally equal form `(Scheme.Hom.appTop (𝟙 G.left)).hom f = f`. Simplify using the standard rewrite rules.

Consider the case `succ j ih`. Establish `e : (show G ⟶ G from F ^ (m * (j + 1))).left = (show G ⟶ G from F ^ m).left ≫ (show G ⟶ G from F ^ (m * j)).left`. Rewrite using `[Nat.mul_succ, pow_add]`. Both sides reduce to the same expression. Rewrite using `[e, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, ih, map_pow, h, ← pow_mul, ← pow_add, Nat.mul_succ, add_comm]`.
-/
theorem appTop_pow_mul {S : Scheme.{0}} {G : Over S} (F : End G) (q m : ℕ) (f : Γ(G.left, ⊤))
    (h : (show G ⟶ G from F ^ m).left.appTop.hom f = f ^ (q ^ m)) (j : ℕ) :
    (show G ⟶ G from F ^ (m * j)).left.appTop.hom f = f ^ (q ^ (m * j)) := by
  induction j with
  | zero =>
    simp only [Nat.mul_zero, pow_zero, pow_one]
    change (Scheme.Hom.appTop (𝟙 G.left)).hom f = f
    simp
  | succ j ih =>
    have e : (show G ⟶ G from F ^ (m * (j + 1))).left =
        (show G ⟶ G from F ^ m).left ≫ (show G ⟶ G from F ^ (m * j)).left := by
      rw [Nat.mul_succ, pow_add]; rfl
    rw [e, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, ih, map_pow, h,
      ← pow_mul, ← pow_add, Nat.mul_succ, add_comm]

/- English proof (translation)
Establish `: IsAffine (splitTorusAff ZU X).left` using `inferInstanceAs (IsAffine (Spec _))`. Establish `: IsAffine (Spec ZU.{0})` using `inferInstance`. Conclude with `inferInstanceAs (IsAffine (pullback (splitTorusAff ZU X).hom (toZ (Sp k))))`.
-/
theorem isAffine_splitTorus (k : Type) [Field k] (X : Type) [AddCommGroup X] :
    IsAffine (splitTorus (Sp k) X).left := by
  have : IsAffine (splitTorusAff ZU X).left := inferInstanceAs (IsAffine (Spec _))
  have : IsAffine (Spec ZU.{0}) := inferInstance
  exact inferInstanceAs (IsAffine (pullback (splitTorusAff ZU X).hom (toZ (Sp k))))

/- English proof (translation)
Introduce `k _ X _ _ _ F q hF`. Use `isAffine_splitTorus k X` as an intermediate fact. Establish `key : ∀ χ : X, ∃ m : ℕ, 1 ≤ m ∧ (show splitTorus (Sp k) X ⟶ splitTorus (Sp k) X from F ^ m).left.appTop.hom (charUnit (Sp k) X χ).val = (charUnit (Sp k) X χ).val ^ (q ^ m)`. Introduce `χ`. Take `⟨m, hm, h, hh⟩` from `hF.2 ⊤ (isAffineOpen_top _) (charUnit (Sp k) X χ).val`.

Use `⟨m, hm, ?_⟩` and prove the remaining obligations. Rewrite using `[← hh, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]`. Both sides reduce to the same expression. Use `choose n0 hn1 hn using key`. Take `⟨s, hs⟩` from `Module.Finite.fg_top (R := ℤ) (M := X)`.

Use `⟨∏ x ∈ s, n0 x, Nat.succ_le_of_lt (Finset.prod_pos fun x _ => hn1 x), fun l => ?_⟩` and prove the remaining obligations. Set `e` to `splitTorusPointsEquiv (Sp k) X (splitTorus (Sp k) X)`. Apply `e.injective` to reduce the goal to its premises. Rewrite using `[map_pow]`. Establish `hgen : ∀ χ ∈ s, e (show splitTorus (Sp k) X ⟶ splitTorus (Sp k) X from F ^ ((∏ x ∈ s, n0 x) * l)) (Multiplicative.ofAdd χ) = (e (𝟙 _) ^ (q ^ ((∏ x ∈ s, n0 x) * l))) (Multiplicative.ofAdd χ)`.

Introduce `χ hχ`. Take `⟨c, hc⟩` from `Finset.dvd_prod_of_mem n0 hχ`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[MonoidHom.pow_apply, Units.val_pow_eq_pow_val, splitTorusPointsEquiv_val, splitTorusPointsEquiv_val, hc, Nat.mul_assoc, appTop_pow_mul F q _ _ (hn χ)]`. Use `congr 1`.

Use `MonoidHom.ext fun x => ?_` and prove the remaining obligations. Establish `hx : x.toAdd ∈ Submodule.span ℤ (s : Set X)` using `by rw [hs]; trivial`. Generalize the expression as in `e (show splitTorus (Sp k) X ⟶ splitTorus (Sp k) X from F ^ ((∏ x ∈ s, n0 x) * l)) = a at hgen ⊢`. Generalize the expression as in `(e (𝟙 _) ^ (q ^ ((∏ x ∈ s, n0 x) * l))) = b at hgen ⊢`. Express the relevant statement in the definitionally equal form `a (Multiplicative.ofAdd x.toAdd) = b (Multiplicative.ofAdd x.toAdd)`.

Generalize the expression as in `x.toAdd = w at hx ⊢`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact hgen y hy`. Consider the case `zero => simp`. Consider the case `add y z _ _ h1 h2 => rw [ofAdd_add, map_mul, map_mul, h1, h2]`.

Consider the case `smul n y _ h => rw [ofAdd_zsmul, map_zpow, map_zpow, h]`.
-/
theorem frobG_splitTorus_pow :
    ∀ (k : Type) [Field k] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (F : End (splitTorus (Sp k) X)) (q : ℕ), FrobG (splitTorus (Sp k) X) F q → ∃ m, 1 ≤ m ∧ ∀ l, (show splitTorus (Sp k) X ⟶ splitTorus (Sp k) X from F ^ (m * l)) = (𝟙 (splitTorus (Sp k) X)) ^ (q ^ (m * l)) := by
  intro k _ X _ _ _ F q hF
  classical
  have := isAffine_splitTorus k X
  have key : ∀ χ : X, ∃ m : ℕ, 1 ≤ m ∧
      (show splitTorus (Sp k) X ⟶ splitTorus (Sp k) X from F ^ m).left.appTop.hom
        (charUnit (Sp k) X χ).val = (charUnit (Sp k) X χ).val ^ (q ^ m) := by
    intro χ
    obtain ⟨m, hm, h, hh⟩ := hF.2 ⊤ (isAffineOpen_top _) (charUnit (Sp k) X χ).val
    refine ⟨m, hm, ?_⟩
    rw [← hh, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  choose n0 hn1 hn using key
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ) (M := X)
  refine ⟨∏ x ∈ s, n0 x, Nat.succ_le_of_lt (Finset.prod_pos fun x _ => hn1 x), fun l => ?_⟩
  let e := splitTorusPointsEquiv (Sp k) X (splitTorus (Sp k) X)
  apply e.injective
  rw [map_pow]
  have hgen : ∀ χ ∈ s, e (show splitTorus (Sp k) X ⟶ splitTorus (Sp k) X from
      F ^ ((∏ x ∈ s, n0 x) * l)) (Multiplicative.ofAdd χ) =
      (e (𝟙 _) ^ (q ^ ((∏ x ∈ s, n0 x) * l))) (Multiplicative.ofAdd χ) := by
    intro χ hχ
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem n0 hχ
    apply Units.ext
    rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, splitTorusPointsEquiv_val,
      splitTorusPointsEquiv_val, hc, Nat.mul_assoc, appTop_pow_mul F q _ _ (hn χ)]
    congr 1
  refine MonoidHom.ext fun x => ?_
  have hx : x.toAdd ∈ Submodule.span ℤ (s : Set X) := by rw [hs]; trivial
  generalize e (show splitTorus (Sp k) X ⟶ splitTorus (Sp k) X from
      F ^ ((∏ x ∈ s, n0 x) * l)) = a at hgen ⊢
  generalize (e (𝟙 _) ^ (q ^ ((∏ x ∈ s, n0 x) * l))) = b at hgen ⊢
  change a (Multiplicative.ofAdd x.toAdd) = b (Multiplicative.ofAdd x.toAdd)
  generalize x.toAdd = w at hx ⊢
  induction hx using Submodule.span_induction with
  | mem y hy => exact hgen y hy
  | zero => simp
  | add y z _ _ h1 h2 => rw [ofAdd_add, map_mul, map_mul, h1, h2]
  | smul n y _ h => rw [ofAdd_zsmul, map_zpow, map_zpow, h]

end GlobalTheory.SS
