import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ProdIrrAndWeakNeronStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelMapGenericallyOpenImmersionCalculusStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericIsomorphismProductModelsStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAutomorphismPermutationMaxOrderMembersStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
namespace GlobalTheory.SS.NeutralModel

/- English proof (translation)
Use `choose f hf using tot`. Set `mul : Quotient r → Quotient r → Quotient r` to `fun a b => Quotient.mk r (f a.out b.out)`. Establish `hm : ∀ a b, T a.out b.out (mul a b).out` using `fun a b => resp _ _ _ _ (hf _ _) (r.symm (Quotient.mk_out _))`. Use `letI : Semigroup (Quotient r) := { mul := mul mul_assoc := fun a b c => by`. Use `assoc _ _ _ _ _ _ _ (hm a b) (hm (mul a b) c) (hm b c) (hm a (mul b c))` as an intermediate fact.

Establish `h2` using `Quotient.sound this`. Rewrite using `[Quotient.out_eq, Quotient.out_eq] at h2 }` and apply the resulting hypothesis. Use `letI : TopologicalSpace (Quotient r) := ⊥`. Use `haveI : DiscreteTopology (Quotient r) := ⟨rfl⟩`. Use `haveI : Nonempty (Quotient r) := ⟨Quotient.mk r (Classical.arbitrary S)⟩`.

Take `⟨e, he⟩` from `exists_idempotent_of_compact_t2_of_continuous_mul_left (M := Quotient r) (fun _ => continuous_of_discreteTopology)`. Use `⟨e.out, ?_⟩` and prove the remaining obligations. Use `hm e e` as an intermediate fact. Rewrite `this` using `[show mul e e = e from he]`. Then use the resulting hypothesis.
-/
theorem exists_idem_of_rel {S : Type} [Finite S] [Nonempty S] (r : Setoid S) (T : S → S → S → Prop)
    (tot : ∀ i j, ∃ k, T i j k) (resp : ∀ i j k k', T i j k → r k k' → T i j k')
    (assoc : ∀ i j l k m p q, T i j k → T k l m → T j l p → T i p q → r m q) : ∃ e, T e e e := by
  choose f hf using tot
  let mul : Quotient r → Quotient r → Quotient r := fun a b => Quotient.mk r (f a.out b.out)
  have hm : ∀ a b, T a.out b.out (mul a b).out := fun a b =>
    resp _ _ _ _ (hf _ _) (r.symm (Quotient.mk_out _))
  letI : Semigroup (Quotient r) :=
    { mul := mul
      mul_assoc := fun a b c => by
        have := assoc _ _ _ _ _ _ _ (hm a b) (hm (mul a b) c) (hm b c) (hm a (mul b c))
        have h2 := Quotient.sound this
        rwa [Quotient.out_eq, Quotient.out_eq] at h2 }
  letI : TopologicalSpace (Quotient r) := ⊥
  haveI : DiscreteTopology (Quotient r) := ⟨rfl⟩
  haveI : Nonempty (Quotient r) := ⟨Quotient.mk r (Classical.arbitrary S)⟩
  obtain ⟨e, he⟩ := exists_idempotent_of_compact_t2_of_continuous_mul_left (M := Quotient r)
    (fun _ => continuous_of_discreteTopology)
  refine ⟨e.out, ?_⟩
  have := hm e e
  rwa [show mul e e = e from he] at this

/- English proof (translation)
Use `choose σ hσ using tot`. Establish `hit : ∀ p, T p i (σ^[p] i)`. Introduce `p`. Proceed by induction on `p with`. Consider the case `zero => exact zero i`.

Consider the case `succ p ih => rw [Function.iterate_succ_apply']`. Conclude with `add _ _ _ _ _ ih (hσ _)`. Establish `hmul : ∀ d, T d i i → ∀ m, T (d * m) i i`. Introduce `d hd m`. Proceed by induction on `m with`.

Consider the case `zero => exact zero i`. Consider the case `succ m ih => rw [Nat.mul_succ]`. Conclude with `add _ _ _ _ _ ih hd`. Establish `key : ∀ p q : Fin (Fintype.card S + 1), p < q → σ^[p] i = σ^[q] i → T (Fintype.card S).factorial i i`. Introduce `p q hpq h`.

Establish `hq : (q : ℕ) = p + (q - p)` using `by have : (p : ℕ) < q := hpq; omega`. Establish `h1 : T (q - p) i i` using `sub p _ i _ (hit p) (by rw [← hq, h]; exact hit q)`. Take `⟨m, hm⟩ : (q - p : ℕ) ∣ (Fintype.card S).factorial` from `Nat.dvd_factorial (by have : (p : ℕ) < q := hpq; omega) (by have := q.2; omega)`. Rewrite using `[hm]`. Conclude with `hmul _ h1 m`.

Take `⟨p, q, hne, h⟩` from `Fintype.exists_ne_map_eq_of_card_lt (fun p : Fin (Fintype.card S + 1) => σ^[p] i) (by simp)`. Break down `lt_or_gt_of_ne hne with h' | h'` into its components or cases. Conclude with `key p q h' h`. Conclude with `key q p h' h.symm`.
-/
theorem rel_factorial {S : Type} [Fintype S] (T : ℕ → S → S → Prop) (tot : ∀ i, ∃ j, T 1 i j)
    (zero : ∀ i, T 0 i i) (add : ∀ p q i j k, T p i j → T q j k → T (p + q) i k)
    (sub : ∀ p d i j, T p i j → T (p + d) i j → T d i i) (i : S) : T (Fintype.card S).factorial i i := by
  choose σ hσ using tot
  have hit : ∀ p, T p i (σ^[p] i) := by
    intro p
    induction p with
    | zero => exact zero i
    | succ p ih => rw [Function.iterate_succ_apply']; exact add _ _ _ _ _ ih (hσ _)
  have hmul : ∀ d, T d i i → ∀ m, T (d * m) i i := by
    intro d hd m
    induction m with
    | zero => exact zero i
    | succ m ih => rw [Nat.mul_succ]; exact add _ _ _ _ _ ih hd
  have key : ∀ p q : Fin (Fintype.card S + 1), p < q → σ^[p] i = σ^[q] i → T (Fintype.card S).factorial i i := by
    intro p q hpq h
    have hq : (q : ℕ) = p + (q - p) := by have : (p : ℕ) < q := hpq; omega
    have h1 : T (q - p) i i := sub p _ i _ (hit p) (by rw [← hq, h]; exact hit q)
    obtain ⟨m, hm⟩ : (q - p : ℕ) ∣ (Fintype.card S).factorial :=
      Nat.dvd_factorial (by have : (p : ℕ) < q := hpq; omega) (by have := q.2; omega)
    rw [hm]; exact hmul _ h1 m
  obtain ⟨p, q, hne, h⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun p : Fin (Fintype.card S + 1) => σ^[p] i) (by simp)
  rcases lt_or_gt_of_ne hne with h' | h'
  · exact key p q h' h
  · exact key q p h' h.symm

section
variable {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A]

noncomputable def shearIso : A ⊗ A ≅ A ⊗ A where
  hom := shear A true
  inv := shear A false
  hom_inv_id := by
    ext <;> simp [shear, MonObj.comp_mul, GrpObj.comp_inv]
  inv_hom_id := by
    ext <;> simp [shear, MonObj.comp_mul, GrpObj.comp_inv]

instance : IsIso (shear A true) := (shearIso A).isIso_hom

/- English proof (translation)
Simplify using `[shear, MonObj.comp_mul, _root_.mul_assoc]`.
-/
theorem triple_fst :
    ((shear A true ⊗ₘ 𝟙 A) ≫ (α_ A A A).hom ≫ (𝟙 A ⊗ₘ (shear A true ≫ (β_ A A).hom)) ≫ (β_ A (A ⊗ A)).hom ≫
      (α_ A A A).hom) ≫ fst A (A ⊗ A) =
    ((α_ A A A).hom ≫ (𝟙 A ⊗ₘ (shear A true ≫ (β_ A A).hom)) ≫ (α_ A A A).inv ≫
      ((shear A true ≫ (β_ A A).hom) ⊗ₘ 𝟙 A) ≫ (α_ A A A).hom) ≫ fst A (A ⊗ A) := by
  simp [shear, MonObj.comp_mul, _root_.mul_assoc]

/- English proof (translation)
Simplify using `[shear, MonObj.comp_mul, GrpObj.comp_inv]`. Both sides reduce to the same expression.
-/
theorem inv_fst :
    ((β_ A A).hom ≫ shear A true ≫ (β_ A A).hom ≫ shear A false ≫ (β_ A A).hom) ≫ fst A A = fst A A ≫ ι[A] := by
  simp [shear, MonObj.comp_mul, GrpObj.comp_inv]
  rfl

noncomputable def invIso : A ≅ A := asIso ι[A]

variable {A} [IsCommMonObj A]

/- English proof (translation)
Simplify using `[transl]`.
-/
theorem transl_one : (transl (1 : 𝟙_ (Over (Sp K)) ⟶ A)).hom = 𝟙 A := by
  simp [transl]

/- English proof (translation)
Simplify using `[transl, MonObj.comp_mul, toUnit_unique (_ ≫ toUnit A) (toUnit A), ← Category.assoc, mul_left_comm, _root_.mul_assoc]`.
-/
theorem transl_mul (a b : 𝟙_ (Over (Sp K)) ⟶ A) : (transl a).hom ≫ (transl b).hom = (transl (a * b)).hom := by
  simp [transl, MonObj.comp_mul, toUnit_unique (_ ≫ toUnit A) (toUnit A), ← Category.assoc, mul_left_comm, _root_.mul_assoc]
end

/- English proof (translation)
Use `hA.smooth` as an intermediate fact. Use `hA.geomConnected` as an intermediate fact. Establish `: GeometricallyIntegral A.hom` using `GlobalTheory.geometricallyIntegral_of_smooth _`. Establish `h1 : IsIntegral A.left` using `GeometricallyIntegral.isIntegral_of_subsingleton A.hom`. Establish `: IsLocallyNoetherian A.left` using `LocallyOfFiniteType.isLocallyNoetherian A.hom`.

Establish `h2 : IsIntegral (A ⊗ A).left` using `inferInstanceAs (IsIntegral (pullback A.hom A.hom))`. Establish `: LocallyOfFiniteType (A ⊗ A).hom` using `by show LocallyOfFiniteType (pullback.fst _ _ ≫ A.hom); infer_instance`. Establish `: IsLocallyNoetherian (A ⊗ A).left` using `LocallyOfFiniteType.isLocallyNoetherian (A ⊗ A).hom`. Conclude with `⟨h1, h2, inferInstanceAs (IsIntegral (pullback A.hom (A ⊗ A).hom))⟩`.
-/
theorem integral_powers {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] (hA : IsAbelianScheme A) :
    IsIntegral A.left ∧ IsIntegral (A ⊗ A).left ∧ IsIntegral (A ⊗ (A ⊗ A)).left := by
  have := hA.smooth
  have := hA.geomConnected
  have : GeometricallyIntegral A.hom := GlobalTheory.geometricallyIntegral_of_smooth _
  have h1 : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have h2 : IsIntegral (A ⊗ A).left := inferInstanceAs (IsIntegral (pullback A.hom A.hom))
  have : LocallyOfFiniteType (A ⊗ A).hom := by
    show LocallyOfFiniteType (pullback.fst _ _ ≫ A.hom); infer_instance
  have : IsLocallyNoetherian (A ⊗ A).left := LocallyOfFiniteType.isLocallyNoetherian (A ⊗ A).hom
  exact ⟨h1, h2, inferInstanceAs (IsIntegral (pullback A.hom (A ⊗ A).hom))⟩

/- English proof (translation)
Introduce `R K _ _ _ _ _ hSH A _ _ hA n M hI hW`. Take `⟨h1, h2, h3⟩` from `integral_powers A hA`. Take `⟨hle, hcomp, hiso, hprod, hstr⟩` from `GlobalTheory.T.modelMapGenericallyOpenImmersion_calculus R K hSH`. Establish `hP : ∀ {B B' : Over (Sp K)} {X : Model R B} {Y : Model R B'}, X.Irr → Y.Irr → (X.prod Y).Irr` using `fun {B B' X Y} => (GlobalTheory.T.prod_irr_and_weakNeron' R K hSH B B').1 X Y`. Establish `hproj` using `GlobalTheory.T.generic_isomorphism_product_models R K hSH`.

Take `⟨S, hne, hS1, hS2⟩` from `GlobalTheory.T.exists_automorphism_permutation_maxOrder_members R K hSH A hA n M hI hW`. Establish `refl : ∀ {B : Over (Sp K)} {X : Model R B}, X.Irr → GenIso X X (𝟙 B)` using `fun {B X} h => hle B X X h X.le_refl`. Establish `comp : ∀ {B B' B'' : Over (Sp K)} {X : Model R B} {Y : Model R B'} {Z : Model R B''} {f : B ⟶ B'} {g : B' ⟶ B''}, Y.Irr → GenIso X Y f → GenIso Y Z g → GenIso X Z (f ≫ g)` using `fun {B B' B'' X Y Z f g} => hcomp B B' B'' X Y Z f g`. Establish `symm : ∀ {B B' : Over (Sp K)} {X : Model R B} {Y : Model R B'} (f : B ≅ B'), GenIso X Y f.hom → GenIso Y X f.inv` using `fun {B B' X Y} f => (hiso B B' X Y f).1`. Establish `prod : ∀ {B B' C C' : Over (Sp K)} {X : Model R B} {Y : Model R B'} {Z : Model R C} {V : Model R C'} {f : B ⟶ C} {g : B' ⟶ C'}, GenIso X Z f → GenIso Y V g → GenIso (X.prod Y) (Z.prod V) (f ⊗ₘ g)` using `fun {B B' C C' X Y Z V f g} => hprod B B' C C' X Y Z V f g`.

Establish `asc : ∀ i j k, GenIso (((M i).prod (M j)).prod (M k)) ((M i).prod ((M j).prod (M k))) (α_ A A A).hom` using `fun i j k => (hstr A A A _ _ _ (hI i) (hI j) (hI k)).1`. Establish `swp : ∀ {B B' : Over (Sp K)} {X : Model R B} {Y : Model R B'}, X.Irr → Y.Irr → GenIso (X.prod Y) (Y.prod X) (β_ B B').hom` using `fun {B B' X Y} hX hY => (hstr B B' B X Y X hX hY hX).2`. Establish `cmp : ∀ {C B : Over (Sp K)} [IsIntegral (A ⊗ B).left] {P : Model R C} {X X' : Model R A} {Y Y' : Model R B} (f g : C ⟶ A ⊗ B) [IsIso f], P.Irr → X.Irr → X'.Irr → Y.Irr → Y'.Irr → f ≫ fst A B = g ≫ fst A B → GenIso P (X.prod Y) f → GenIso P (X'.prod Y') g → GenIso X X' (𝟙 A)`. Introduce `C B _ P X X' Y Y' f g _ hP hX hX' hY hY' e hf hg`. Use `hproj A A B B X X' Y Y' (Iso.refl A) ((asIso f).inv ≫ g) hX hX' hY hY' ?_ (comp hP (symm (asIso f) hf) hg)` and prove the remaining obligations.

Simplify using `[← e]`. Set `r : Setoid S` to `{ r := fun i j => GenIso (M i) (M j) (𝟙 A) iseqv := ⟨fun i => refl (hI i), fun h => symm (Iso.refl A) h, fun h h' => by simpa using comp (hI _) h h'⟩ }`. Set `T : S → S → S → Prop` to `fun i j k => GenIso ((M i).prod (M j)) ((M i).prod (M k)) (shear A true)`. Establish `hT : ∀ {i j k : S}, T i j k → GenIso ((M i).prod (M j)) ((M k).prod (M i)) (shear A true ≫ (β_ A A).hom)` using `fun h => comp (hP (hI _) (hI _)) h (swp (hI _) (hI _))`. Use `haveI : Nonempty S := hne.to_subtype`.

Take `⟨e, he⟩` from `exists_idem_of_rel r T (by`. Introduce `i j`. Take `⟨i', hi', k, hk, h⟩` from `hS2 (shearIso A) i i.2 j j.2`. Establish `h0 : GenIso (M i) (M i') (𝟙 A)` using `hproj A A A A _ _ _ _ (Iso.refl A) _ (hI _) (hI _) (hI _) (hI _) (by simp [shearIso, shear]) h`. Use `comp (hP (hI _) (hI _)) h (prod (symm (Iso.refl A) h0) (refl (hI k)))` as an intermediate fact.

Use `⟨⟨k, hk⟩, ?_⟩` and prove the remaining obligations. Simplify `this)` using `[shearIso]`. Use the proof step `(by`. Introduce `i j k k' h h'`. Use `comp (hP (hI _) (hI _)) h (prod (refl (hI i)) h')` as an intermediate fact.

Simplify using `using this)`. Use the proof step `(by`. Introduce `i j l k m p q a b c d`. Use `cmp _ _ (hP (hP (hI i) (hI j)) (hI l)) (hI m) (hI q) (hP (hI k) (hI i)) (hP (hI i) (hI j)) (triple_fst A) ?_ ?_` and prove the remaining obligations. Conclude with `comp (hP (hP (hI _) (hI _)) (hI _)) (prod a (refl (hI l))) <| comp (hP (hI _) (hP (hI _) (hI _))) (asc _ _ _) <| comp (hP (hI _) (hP (hI _) (hI _))) (prod (refl (hI i)) (hT b)) <| comp (hP (hP (hI _) (hI _)) (hI _)) (swp (hI _) (hP (hI _) (hI _))) (asc _ _ _)`.

Conclude with `comp (hP (hI _) (hP (hI _) (hI _))) (asc _ _ _) <| comp (hP (hI _) (hP (hI _) (hI _))) (prod (refl (hI i)) (hT c)) <| comp (hP (hP (hI _) (hI _)) (hI _)) (symm (α_ A A A) (asc _ _ _)) <| comp (hP (hP (hI _) (hI _)) (hI _)) (prod (hT d) (refl (hI j))) (asc _ _ _))`. Establish `he' : GenIso ((M e).prod (M e)) ((M e).prod (M e)) (shear A false)` using `symm (shearIso A) he`. Establish `hee` using `hP (hI e) (hI e)`. Establish `hs` using `swp (hI e) (hI e)`. Apply the tactic sequence `refine ⟨M e, ⟨hI e, fun b => by cases b <;> assumption, ?_⟩, (Fintype.card S).factorial, Nat.factorial_pos _, fun a => ?_⟩`.

Conclude with `hproj A A A A _ _ _ _ (invIso A) _ (hI e) (hI e) (hI e) (hI e) (inv_fst A) (comp hee hs <| comp hee he <| comp hee hs <| comp hee he' hs)`. Use `rel_factorial (fun p (i j : S) => GenIso (M i) (M j) (transl (a ^ p)).hom) ?_ ?_ ?_ ?_ e` and prove the remaining obligations. Introduce `i`. Take `⟨j, hj, h⟩` from `hS1 (transl (a ^ 1)) i i.2`. Conclude with `⟨⟨j, hj⟩, h⟩`.

Introduce `i`. Simplify using `only [pow_zero, transl_one]`. Conclude with `refl (hI i)`. Introduce `p q i j k h h'`. Use `comp (hI _) h h'` as an intermediate fact.

Rewrite `this` using `[transl_mul, ← pow_add]`. Then use the resulting hypothesis. Introduce `p d i j h h'`. Use `comp (hI _) h' (symm _ h)` as an intermediate fact. Rewrite `this` using `[add_comm, pow_add, ← transl_mul, Category.assoc, Iso.hom_inv_id, Category.comp_id]`. Then use the resulting hypothesis.
-/
theorem exists_birLaw : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (n : ℕ) (M : Fin n → Model R A), (∀ i, (M i).Irr) → WeakNeron M → ∃ N : Model R A, BirLaw N ∧ ∃ c : ℕ, 1 ≤ c ∧ ∀ a : (𝟙_ (Over (Sp K)) ⟶ A), GenIso N N (transl (a ^ c)).hom := by
  intro R K _ _ _ _ _ hSH A _ _ hA n M hI hW
  obtain ⟨h1, h2, h3⟩ := integral_powers A hA
  obtain ⟨hle, hcomp, hiso, hprod, hstr⟩ := GlobalTheory.T.modelMapGenericallyOpenImmersion_calculus R K hSH
  have hP : ∀ {B B' : Over (Sp K)} {X : Model R B} {Y : Model R B'}, X.Irr → Y.Irr → (X.prod Y).Irr :=
    fun {B B' X Y} => (GlobalTheory.T.prod_irr_and_weakNeron' R K hSH B B').1 X Y
  have hproj := GlobalTheory.T.generic_isomorphism_product_models R K hSH
  obtain ⟨S, hne, hS1, hS2⟩ := GlobalTheory.T.exists_automorphism_permutation_maxOrder_members R K hSH A hA n M hI hW
  have refl : ∀ {B : Over (Sp K)} {X : Model R B}, X.Irr → GenIso X X (𝟙 B) :=
    fun {B X} h => hle B X X h X.le_refl
  have comp : ∀ {B B' B'' : Over (Sp K)} {X : Model R B} {Y : Model R B'} {Z : Model R B''} {f : B ⟶ B'}
      {g : B' ⟶ B''}, Y.Irr → GenIso X Y f → GenIso Y Z g → GenIso X Z (f ≫ g) :=
    fun {B B' B'' X Y Z f g} => hcomp B B' B'' X Y Z f g
  have symm : ∀ {B B' : Over (Sp K)} {X : Model R B} {Y : Model R B'} (f : B ≅ B'),
      GenIso X Y f.hom → GenIso Y X f.inv := fun {B B' X Y} f => (hiso B B' X Y f).1
  have prod : ∀ {B B' C C' : Over (Sp K)} {X : Model R B} {Y : Model R B'} {Z : Model R C} {V : Model R C'}
      {f : B ⟶ C} {g : B' ⟶ C'}, GenIso X Z f → GenIso Y V g → GenIso (X.prod Y) (Z.prod V) (f ⊗ₘ g) :=
    fun {B B' C C' X Y Z V f g} => hprod B B' C C' X Y Z V f g
  have asc : ∀ i j k, GenIso (((M i).prod (M j)).prod (M k)) ((M i).prod ((M j).prod (M k))) (α_ A A A).hom :=
    fun i j k => (hstr A A A _ _ _ (hI i) (hI j) (hI k)).1
  have swp : ∀ {B B' : Over (Sp K)} {X : Model R B} {Y : Model R B'}, X.Irr → Y.Irr →
      GenIso (X.prod Y) (Y.prod X) (β_ B B').hom :=
    fun {B B' X Y} hX hY => (hstr B B' B X Y X hX hY hX).2
  have cmp : ∀ {C B : Over (Sp K)} [IsIntegral (A ⊗ B).left] {P : Model R C} {X X' : Model R A} {Y Y' : Model R B}
      (f g : C ⟶ A ⊗ B) [IsIso f], P.Irr → X.Irr → X'.Irr → Y.Irr → Y'.Irr → f ≫ fst A B = g ≫ fst A B →
      GenIso P (X.prod Y) f → GenIso P (X'.prod Y') g → GenIso X X' (𝟙 A) := by
    intro C B _ P X X' Y Y' f g _ hP hX hX' hY hY' e hf hg
    refine hproj A A B B X X' Y Y' (Iso.refl A) ((asIso f).inv ≫ g) hX hX' hY hY' ?_
      (comp hP (symm (asIso f) hf) hg)
    simp [← e]
  let r : Setoid S :=
    { r := fun i j => GenIso (M i) (M j) (𝟙 A)
      iseqv := ⟨fun i => refl (hI i), fun h => symm (Iso.refl A) h,
        fun h h' => by simpa using comp (hI _) h h'⟩ }
  let T : S → S → S → Prop := fun i j k => GenIso ((M i).prod (M j)) ((M i).prod (M k)) (shear A true)
  have hT : ∀ {i j k : S}, T i j k →
      GenIso ((M i).prod (M j)) ((M k).prod (M i)) (shear A true ≫ (β_ A A).hom) :=
    fun h => comp (hP (hI _) (hI _)) h (swp (hI _) (hI _))
  haveI : Nonempty S := hne.to_subtype
  obtain ⟨e, he⟩ := exists_idem_of_rel r T
    (by
      intro i j
      obtain ⟨i', hi', k, hk, h⟩ := hS2 (shearIso A) i i.2 j j.2
      have h0 : GenIso (M i) (M i') (𝟙 A) :=
        hproj A A A A _ _ _ _ (Iso.refl A) _ (hI _) (hI _) (hI _) (hI _) (by simp [shearIso, shear]) h
      have := comp (hP (hI _) (hI _)) h (prod (symm (Iso.refl A) h0) (refl (hI k)))
      refine ⟨⟨k, hk⟩, ?_⟩
      simpa [shearIso] using this)
    (by
      intro i j k k' h h'
      have := comp (hP (hI _) (hI _)) h (prod (refl (hI i)) h')
      simpa using this)
    (by
      intro i j l k m p q a b c d
      refine cmp _ _ (hP (hP (hI i) (hI j)) (hI l)) (hI m) (hI q) (hP (hI k) (hI i)) (hP (hI i) (hI j))
        (triple_fst A) ?_ ?_
      · exact comp (hP (hP (hI _) (hI _)) (hI _)) (prod a (refl (hI l))) <|
          comp (hP (hI _) (hP (hI _) (hI _))) (asc _ _ _) <|
          comp (hP (hI _) (hP (hI _) (hI _))) (prod (refl (hI i)) (hT b)) <|
          comp (hP (hP (hI _) (hI _)) (hI _)) (swp (hI _) (hP (hI _) (hI _))) (asc _ _ _)
      · exact comp (hP (hI _) (hP (hI _) (hI _))) (asc _ _ _) <|
          comp (hP (hI _) (hP (hI _) (hI _))) (prod (refl (hI i)) (hT c)) <|
          comp (hP (hP (hI _) (hI _)) (hI _)) (symm (α_ A A A) (asc _ _ _)) <|
          comp (hP (hP (hI _) (hI _)) (hI _)) (prod (hT d) (refl (hI j))) (asc _ _ _))
  have he' : GenIso ((M e).prod (M e)) ((M e).prod (M e)) (shear A false) := symm (shearIso A) he
  have hee := hP (hI e) (hI e)
  have hs := swp (hI e) (hI e)
  refine ⟨M e, ⟨hI e, fun b => by cases b <;> assumption, ?_⟩, (Fintype.card S).factorial,
    Nat.factorial_pos _, fun a => ?_⟩
  · exact hproj A A A A _ _ _ _ (invIso A) _ (hI e) (hI e) (hI e) (hI e) (inv_fst A)
      (comp hee hs <| comp hee he <| comp hee hs <| comp hee he' hs)
  · refine rel_factorial (fun p (i j : S) => GenIso (M i) (M j) (transl (a ^ p)).hom) ?_ ?_ ?_ ?_ e
    · intro i
      obtain ⟨j, hj, h⟩ := hS1 (transl (a ^ 1)) i i.2
      exact ⟨⟨j, hj⟩, h⟩
    · intro i
      simp only [pow_zero, transl_one]
      exact refl (hI i)
    · intro p q i j k h h'
      have := comp (hI _) h h'
      rwa [transl_mul, ← pow_add] at this
    · intro p d i j h h'
      have := comp (hI _) h' (symm _ h)
      rwa [add_comm, pow_add, ← transl_mul, Category.assoc, Iso.hom_inv_id, Category.comp_id] at this

end GlobalTheory.SS.NeutralModel
