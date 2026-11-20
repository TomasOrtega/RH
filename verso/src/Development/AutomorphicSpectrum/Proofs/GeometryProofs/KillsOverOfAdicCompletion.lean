import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EqZeroOfMemMapPow
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CharValMultiplicativeStatement
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SpecialMapFinite
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.KillsAdic

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.main s h I hI hU`.
-/
theorem ext_of_quotients {A : Type} [CommRing A] {Y Z : Scheme.{0}} {f g : Sp A ⟶ Y} (s : Y ⟶ Z) [IsSeparated s]
    (h : f ≫ s = g ≫ s) {N : Type} (I : N → Ideal A) (hI : ∀ x : A, (∀ n, x ∈ I n) → x = 0)
    (hU : ∀ n, spMap (Ideal.Quotient.mk (I n)) ≫ f = spMap (Ideal.Quotient.mk (I n)) ≫ g) : f = g :=
  _root_.UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.main s h I hI hU

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]

/- English proof (translation)
Substitute `e` using the available equality. Conclude with `(GlobalTheory.T.charVal_multiplicative S X A a).2.2.2.2.2 A' h t _ (by simp) χ`.
-/
theorem charVal_comp {A A' : Type} [CommRing A] [CommRing A'] {a : Sp A ⟶ S} {a' : Sp A' ⟶ S} (h : A →+* A')
    (e : spMap h ≫ a = a') (t : Over.mk a ⟶ splitTorus S X) (χ : X) :
    charVal ((Over.homMk (spMap h) e : Over.mk a' ⟶ Over.mk a) ≫ t) χ = h (charVal t χ) := by
  subst e
  exact (GlobalTheory.T.charVal_multiplicative S X A a).2.2.2.2.2 A' h t _ (by simp) χ

/- English proof (translation)
Establish `key : ∀ x x' : X, (x : X ⧸ Y) = x' → f x = f x'`. Introduce `x x' e`. Establish `hm : -x + x' ∈ Y` using `QuotientAddGroup.eq.1 e`. Establish `: x' = x + (-x + x')` using `by abel`. Rewrite using `[this, hadd, hY _ hm, _root_.mul_one]`.

Use `⟨{ toFun := fun q => f (Quotient.out (Multiplicative.toAdd q)) map_one' := ?_ map_mul' := ?_ }, fun χ => ?_⟩` and prove the remaining obligations. Rewrite using `[← h0]`. Conclude with `key _ _ (by simp)`. Introduce `p q`. Rewrite using `[← hadd]`.

Conclude with `key _ _ (by simp)`. Conclude with `key _ _ (by simp)`.
-/
theorem exists_factor {M : Type} [CommMonoid M] (Y : AddSubgroup X) (f : X → M) (h0 : f 0 = 1)
    (hadd : ∀ x y, f (x + y) = f x * f y) (hY : ∀ y ∈ Y, f y = 1) :
    ∃ v : Multiplicative (X ⧸ Y) →* M, ∀ χ : X, v (Multiplicative.ofAdd (χ : X ⧸ Y)) = f χ := by
  have key : ∀ x x' : X, (x : X ⧸ Y) = x' → f x = f x' := by
    intro x x' e
    have hm : -x + x' ∈ Y := QuotientAddGroup.eq.1 e
    have : x' = x + (-x + x') := by abel
    rw [this, hadd, hY _ hm, _root_.mul_one]
  refine ⟨{ toFun := fun q => f (Quotient.out (Multiplicative.toAdd q))
            map_one' := ?_
            map_mul' := ?_ }, fun χ => ?_⟩
  · rw [← h0]
    exact key _ _ (by simp)
  · intro p q
    rw [← hadd]
    exact key _ _ (by simp)
  · exact key _ _ (by simp)

/- English proof (translation)
Rewrite using `[Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (f ≫ toUnit T) (toUnit T')]`.
-/
theorem comp_one_over {T T' M : Over S} [GrpObj M] (f : T' ⟶ T) : f ≫ (1 : T ⟶ M) = 1 := by
  rw [Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (f ≫ toUnit T) (toUnit T')]

/- English proof (translation)
Set `c` to `algebraMap R (AddMonoidAlgebra R (X ⧸ Y))`. Set `I : ℕ → Ideal (AddMonoidAlgebra R (X ⧸ Y))` to `fun n => Ideal.map c (IsLocalRing.maximalIdeal R ^ (n + 1))`. Establish `hI : ∀ x, (∀ n, x ∈ I n) → x = 0` using `fun x hx => GlobalTheory.CompanionTheory.KrullGroupAlg.eq_zero_of_mem_map_pow R (X ⧸ Y) x fun n => Ideal.map_mono (Ideal.pow_le_pow_right (Nat.le_succ n)) (hx n)`. Use `Over.OverMorphism.ext (ext_of_quotients G.hom ?_ I hI fun n => ?_)` and prove the remaining obligations. Rewrite using `[Over.w, Over.w]`.

Set `J` to `IsLocalRing.maximalIdeal R ^ (n + 1)`. Set `gn : R ⧸ J →+* AddMonoidAlgebra R (X ⧸ Y) ⧸ I n` to `Ideal.quotientMap (I n) c Ideal.le_comap_map`. Establish `e : spMap (Ideal.Quotient.mk (I n)) ≫ spMap c ≫ b = spMap gn ≫ spMap (Ideal.Quotient.mk J) ≫ b`. Rewrite using `[← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]`. Both sides reduce to the same expression.

Set `m : Over.mk (spMap gn ≫ spMap (Ideal.Quotient.mk J) ≫ b) ⟶ Over.mk (spMap c ≫ b)` to `Over.homMk (spMap (Ideal.Quotient.mk (I n))) e`. Establish `hone` using `hk n _ gn (m ≫ t₀) (fun y hy => by`. Rewrite using `[charVal_comp, ht₀, (QuotientAddGroup.eq_zero_iff y).2 hy]`. Conclude with `map_one _)`. Establish `h4 : m ≫ (t₀ ≫ u) = m ≫ (1 : Over.mk (spMap c ≫ b) ⟶ G)`.

Conclude with `(Category.assoc m t₀ u).symm.trans (hone.trans (comp_one_over m).symm)`. Conclude with `congrArg (fun w => w.left) h4`.
-/
theorem universal_one {G : Over S} [GrpObj G] [IsSeparated G.hom] (u : splitTorus S X ⟶ G) (Y : AddSubgroup X)
    {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (b : Sp R ⟶ S)
    (hk : ∀ n : ℕ, KillsOver u Y (spMap (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1))) ≫ b))
    (t₀ : Over.mk (spMap (algebraMap R (AddMonoidAlgebra R (X ⧸ Y))) ≫ b) ⟶ splitTorus S X)
    (ht₀ : ∀ χ : X, charVal t₀ χ = AddMonoidAlgebra.single (χ : X ⧸ Y) 1) : t₀ ≫ u = 1 := by
  let c := algebraMap R (AddMonoidAlgebra R (X ⧸ Y))
  let I : ℕ → Ideal (AddMonoidAlgebra R (X ⧸ Y)) := fun n =>
    Ideal.map c (IsLocalRing.maximalIdeal R ^ (n + 1))
  have hI : ∀ x, (∀ n, x ∈ I n) → x = 0 := fun x hx =>
    GlobalTheory.CompanionTheory.KrullGroupAlg.eq_zero_of_mem_map_pow R (X ⧸ Y) x fun n =>
      Ideal.map_mono (Ideal.pow_le_pow_right (Nat.le_succ n)) (hx n)
  refine Over.OverMorphism.ext (ext_of_quotients G.hom ?_ I hI fun n => ?_)
  · rw [Over.w, Over.w]
  · let J := IsLocalRing.maximalIdeal R ^ (n + 1)
    let gn : R ⧸ J →+* AddMonoidAlgebra R (X ⧸ Y) ⧸ I n :=
      Ideal.quotientMap (I n) c Ideal.le_comap_map
    have e : spMap (Ideal.Quotient.mk (I n)) ≫ spMap c ≫ b = spMap gn ≫ spMap (Ideal.Quotient.mk J) ≫ b := by
      rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
      rfl
    let m : Over.mk (spMap gn ≫ spMap (Ideal.Quotient.mk J) ≫ b) ⟶ Over.mk (spMap c ≫ b) :=
      Over.homMk (spMap (Ideal.Quotient.mk (I n))) e
    have hone := hk n _ gn (m ≫ t₀) (fun y hy => by
      rw [charVal_comp, ht₀, (QuotientAddGroup.eq_zero_iff y).2 hy]
      exact map_one _)
    have h4 : m ≫ (t₀ ≫ u) = m ≫ (1 : Over.mk (spMap c ≫ b) ⟶ G) := by
      exact (Category.assoc m t₀ u).symm.trans (hone.trans (comp_one_over m).symm)
    exact congrArg (fun w => w.left) h4

/- English proof (translation)
Introduce `S G _ _ X _ u Y R _ _ _ b hk A _ g t ht`. Set `c` to `algebraMap R (AddMonoidAlgebra R (X ⧸ Y))`. Set `w₀ : Multiplicative X →* AddMonoidAlgebra R (X ⧸ Y)` to `(AddMonoidAlgebra.of R (X ⧸ Y)).comp (AddMonoidHom.toMultiplicative (QuotientAddGroup.mk' Y))`. Take `⟨t₀, ht₀⟩` from `(GlobalTheory.T.charVal_multiplicative S X _ (spMap c ≫ b)).2.2.2.2.1 w₀`. Establish `ht₀' : ∀ χ : X, charVal t₀ χ = AddMonoidAlgebra.single (χ : X ⧸ Y) 1` using `fun χ => ht₀ χ`.

Establish `hone` using `universal_one u Y b hk t₀ ht₀'`. Establish `hpts` using `(GlobalTheory.T.charVal_multiplicative S X A (spMap g ≫ b))`. Take `⟨v, hv⟩` from `exists_factor Y (charVal t) (hpts.2.2.2.1 t).1 (hpts.2.2.2.1 t).2 ht`. Set `h : AddMonoidAlgebra R (X ⧸ Y) →+* A` to `AddMonoidAlgebra.liftNCRingHom g v (fun _ _ => Commute.all _ _)`. Establish `hc : h.comp c = g`.

Use extensionality with `r`. Simplify using `[h, c]`. Establish `e : spMap h ≫ spMap c ≫ b = spMap g ≫ b`. Rewrite using `[← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hc]`. Set `m : Over.mk (spMap g ≫ b) ⟶ Over.mk (spMap c ≫ b)` to `Over.homMk (spMap h) e`.

Establish `htm : t = m ≫ t₀` using `hpts.1 _ _ fun χ => by`. Rewrite using `[charVal_comp, ht₀']`. Simplify using `[h, AddMonoidAlgebra.liftNCRingHom_single, hv]`. Rewrite using `[htm, Category.assoc, hone, comp_one_over]`.
-/
theorem killsOver_of_forall_pow : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsSeparated G.hom] (X : Type) [AddCommGroup X] (u : splitTorus S X ⟶ G) (Y : AddSubgroup X) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (b : Sp R ⟶ S), (∀ n : ℕ, KillsOver u Y (spMap (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1))) ≫ b)) → KillsOver u Y b := by
  intro S G _ _ X _ u Y R _ _ _ b hk A _ g t ht
  let c := algebraMap R (AddMonoidAlgebra R (X ⧸ Y))
  let w₀ : Multiplicative X →* AddMonoidAlgebra R (X ⧸ Y) :=
    (AddMonoidAlgebra.of R (X ⧸ Y)).comp (AddMonoidHom.toMultiplicative (QuotientAddGroup.mk' Y))
  obtain ⟨t₀, ht₀⟩ := (GlobalTheory.T.charVal_multiplicative S X _ (spMap c ≫ b)).2.2.2.2.1 w₀
  have ht₀' : ∀ χ : X, charVal t₀ χ = AddMonoidAlgebra.single (χ : X ⧸ Y) 1 := fun χ => ht₀ χ
  have hone := universal_one u Y b hk t₀ ht₀'
  have hpts := (GlobalTheory.T.charVal_multiplicative S X A (spMap g ≫ b))
  obtain ⟨v, hv⟩ := exists_factor Y (charVal t) (hpts.2.2.2.1 t).1 (hpts.2.2.2.1 t).2 ht
  let h : AddMonoidAlgebra R (X ⧸ Y) →+* A :=
    AddMonoidAlgebra.liftNCRingHom g v (fun _ _ => Commute.all _ _)
  have hc : h.comp c = g := by
    ext r
    simp [h, c]
  have e : spMap h ≫ spMap c ≫ b = spMap g ≫ b := by
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hc]
  let m : Over.mk (spMap g ≫ b) ⟶ Over.mk (spMap c ≫ b) := Over.homMk (spMap h) e
  have htm : t = m ≫ t₀ := hpts.1 _ _ fun χ => by
    rw [charVal_comp, ht₀']
    simp [h, AddMonoidAlgebra.liftNCRingHom_single, hv]
  rw [htm, Category.assoc, hone, comp_one_over]

end GlobalTheory.CompanionTheory.Ar.KillsAdic
