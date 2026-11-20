import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.EtaleCohomology.TateTwists.EtaleChapterCThree
import Development.EtaleCohomology.TateTwists.EtaleChapterCTwo
import Development.EtaleCohomology.TateTwists.FinitaryBaseChangeInjective
import Development.EtaleCohomology.TateTwists.FinitaryFilteredColimit
import Development.EtaleCohomology.TateTwists.FinitaryLowerBound
import Development.EtaleCohomology.TateTwists.StrictHenselianEtaleSection
import Development.EtaleCohomology.TateTwists.EtaleChapterAFive

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite TensorProduct GlobalTheory.EtC GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec

namespace LateralTheory.EtaleFoundations.CongruenceLocalDecomposition

def genHom (T K A : Type) [CommRing T] [CommRing K] [CommRing A] [Algebra T K] [Algebra T A] [Algebra (Polynomial T) A] :
    Polynomial K →+* K ⊗[T] A :=
  Polynomial.eval₂RingHom (Algebra.TensorProduct.includeLeftRingHom (R := T) (A := K) (B := A))
    ((1 : K) ⊗ₜ[T] algebraMap (Polynomial T) A Polynomial.X)

/- English proof (translation)
Take `⟨J, _, _, D, t, s, hs, hj⟩` from `h`. Use `⟨J, inferInstance, inferInstance, D, (Functor.const J).map (CommRingCat.ofHom (algebraMap R B)) ≫ t, s, hs, fun j => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Establish `h1 : RingHom.Etale (t.app j).hom` using `(hj j).1`. Establish `h0 : RingHom.Etale (algebraMap R B)` using `RingHom.etale_algebraMap.2 inferInstance`. Conclude with `RingHom.Etale.stableUnderComposition (algebraMap R B) (t.app j).hom h0 h1`.

Rewrite using `[NatTrans.comp_app, Category.assoc, (hj j).2, IsScalarTower.algebraMap_eq R B A]`. Both sides reduce to the same expression.
-/
theorem indEt_trans (R B A : Type) [CommRing R] [CommRing B] [CommRing A] [Algebra R B] [Algebra B A] [Algebra R A]
    [IsScalarTower R B A] [Algebra.Etale R B] (h : IndEt B A) : IndEt R A := by
  obtain ⟨J, _, _, D, t, s, hs, hj⟩ := h
  refine ⟨J, inferInstance, inferInstance, D, (Functor.const J).map (CommRingCat.ofHom (algebraMap R B)) ≫ t, s, hs,
    fun j => ⟨?_, ?_⟩⟩
  · have h1 : RingHom.Etale (t.app j).hom := (hj j).1
    have h0 : RingHom.Etale (algebraMap R B) := RingHom.etale_algebraMap.2 inferInstance
    exact RingHom.Etale.stableUnderComposition (algebraMap R B) (t.app j).hom h0 h1
  · rw [NatTrans.comp_app, Category.assoc, (hj j).2, IsScalarTower.algebraMap_eq R B A]
    rfl

def EtaleChapterANine : Prop := GlobalTheory.EtC.A9

def StrictHenselianAcyclic : Prop := GlobalTheory.EtC.B2

def TwFin : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ), Finitary (tw q i)

def TwLoc : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ),
  (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (y : Sec (tw q i) U),
    Loc U fun V g => ∃ c : ℕ, Sec.res g y = c • twGen i (ζ.map g.appTop.hom)) ∧
  (∀ (U : Scheme.{0}) [Nonempty U] (ζ : Prim q Γ(U, ⊤)) (c : ℕ), c • twGen i ζ = 0 → q ∣ c) ∧
  ∀ (V U : Scheme.{0}) (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)), Sec.res g (twGen i ζ) = twGen i (ζ.map g.appTop.hom)

def H0 : Prop := ∀ (q : ℕ) [NeZero q] (A C : Type) [CommRing A] [IsDomain A] [CommRing C] [IsDomain C] (f : A →+* C),
  Nonempty (Prim q A) → ∀ i : ℤ, Function.Bijective (pull _ (spMap f) (tw q i) 0)

def B3ind : Prop := ∀ (q : ℕ) [NeZero q] (T K B : Type) [CommRing T] [CommRing K] [CommRing B] [Algebra T K] [Algebra T B] (i : ℤ),
  (∀ (A : Type) [CommRing A] [Algebra B A] [Algebra T A] [IsScalarTower T B A], SH A → IndEt B A →
    Eqv _ (spMap (Algebra.TensorProduct.includeRight (R := T) (A := K) (B := A)).toRingHom) (tw q i)) →
  Eqv _ (spMap (Algebra.TensorProduct.includeRight (R := T) (A := K) (B := B)).toRingHom) (tw q i)

def AicBasic : Prop := ∀ (T : Type) [CommRing T] [IsDomain T], AIC T →
  IsIntegrallyClosed T ∧ IsAlgClosed (FractionRing T) ∧ ∀ (q : ℕ) [NeZero q], IsUnit (q : T) → Nonempty (Prim q T)

def IndDom : Prop := ∀ (R A : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing A] [IsLocalRing A] [Algebra R A],
  IndEt R A → IsDomain A ∧ IsIntegrallyClosed A ∧ Function.Injective (algebraMap R A)

def LocDom : Prop := ∀ (T A : Type) [CommRing T] [IsDomain T] [CommRing A] [IsDomain A] [Algebra T A],
  Function.Injective (algebraMap T A) → IsDomain (FractionRing T ⊗[T] A)

def BcInd : Prop := ∀ (T K A : Type) [CommRing T] [CommRing K] [CommRing A] [Algebra T K] [Algebra T A] [Algebra (Polynomial T) A]
  [IsScalarTower T (Polynomial T) A], IndEt (Polynomial T) A → IsIndEtale (genHom T K A)

def EtDed : Prop := ∀ (K E : Type) [Field K] [CommRing E] [Algebra (Polynomial K) E] [Algebra.Etale (Polynomial K) E]
  (p : Ideal E), p ∈ minimalPrimes E → IsDedekindDomain (E ⧸ p)

def Deg2 : Prop := ∀ (q : ℕ) [NeZero q] (K C : Type) [Field K] [IsAlgClosed K] [CommRing C] [IsDomain C] (f : Polynomial K →+* C),
  IsUnit (q : K) → IsIndEtale f → ∀ n i : ℤ, 2 ≤ n → Subsingleton (Ht q (sp C) n i)

def Deg1 : Prop := ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) →
  ∀ (A : Type) [CommRing A] [Algebra (Polynomial T) A] [Algebra T A] [IsScalarTower T (Polynomial T) A],
  SH A → IndEt (Polynomial T) A → ∀ i : ℤ, Subsingleton (Ht q (sp (FractionRing T ⊗[T] A)) 1 i)

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩`.
-/
theorem bij_of_subsingleton {α β : Type*} [Zero α] (f : α → β) (ha : Subsingleton α) (hb : Subsingleton β) :
    Function.Bijective f :=
  ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩

/- English proof (translation)
Introduce `q _ T _ _ _ hT hq B _ _ _ _ _ i`. Use `hB3 q T (FractionRing T) B i ?_` and prove the remaining obligations. Introduce `A _ _ _ _ hA hBA`. Use `letI : Algebra (Polynomial T) A := ((algebraMap B A).comp (algebraMap (Polynomial T) B)).toAlgebra`. Use `haveI : IsScalarTower (Polynomial T) B A := IsScalarTower.of_algebraMap_eq fun _ => rfl`.

Use `haveI : IsScalarTower T (Polynomial T) A := IsScalarTower.of_algebraMap_eq fun x => by`. Rewrite using `[IsScalarTower.algebraMap_apply T B A, IsScalarTower.algebraMap_apply T (Polynomial T) B]`. Both sides reduce to the same expression. Establish `hI : IndEt (Polynomial T) A` using `indEt_trans (Polynomial T) B A hBA`. Take `⟨hn, hK, hP⟩` from `hAic T hT`.

Take `⟨hH, hs⟩` from `hA`. Take `⟨hd, -, hinj⟩` from `hInd (Polynomial T) A hI`. Establish `hinjT : Function.Injective (algebraMap T A)`. Rewrite using `[IsScalarTower.algebraMap_eq T (Polynomial T) A, RingHom.coe_comp]`. Conclude with `hinj.comp Polynomial.C_injective`.

Use `haveI := hLoc T A hinjT`. Establish `hqK : IsUnit (q : FractionRing T)` using `by simpa using hq.map (algebraMap T (FractionRing T))`. Introduce `n`. Break down `lt_trichotomy n 0 with h | h | h` into its components or cases. Conclude with `bij_of_subsingleton _ ((hA9 _ _).1 _ n h) ((hA9 _ _).1 _ n h)`.

Substitute `h` using the available equality. Conclude with `hH0 q A _ _ ⟨(hP q hq).some.map (algebraMap T A)⟩ i`. Use `bij_of_subsingleton _ (hB2 _ A ⟨hH, hs⟩ _ n h) ?_` and prove the remaining obligations. Break down `(show n = 1 ∨ 2 ≤ n by omega) with h1 | h2` into its components or cases. Substitute `h1` using the available equality.

Conclude with `hD1 q T hT hq A ⟨hH, hs⟩ hI i`. Conclude with `hD2 q (FractionRing T) _ (genHom T (FractionRing T) A) hqK (hBc T _ A hI) n i h2`.
-/
theorem goal_of (hA9 : EtaleChapterANine) (hB2 : StrictHenselianAcyclic) (hH0 : H0) (hB3 : B3ind) (hAic : AicBasic) (hInd : IndDom) (hLoc : LocDom)
    (hBc : BcInd) (hD2 : Deg2) (hD1 : Deg1) : LateralTheory.EtaleFoundations.EtaleChapterCThree := by
  intro q _ T _ _ _ hT hq B _ _ _ _ _ i
  refine hB3 q T (FractionRing T) B i ?_
  intro A _ _ _ _ hA hBA
  letI : Algebra (Polynomial T) A := ((algebraMap B A).comp (algebraMap (Polynomial T) B)).toAlgebra
  haveI : IsScalarTower (Polynomial T) B A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower T (Polynomial T) A := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply T B A, IsScalarTower.algebraMap_apply T (Polynomial T) B]
    rfl
  have hI : IndEt (Polynomial T) A := indEt_trans (Polynomial T) B A hBA
  obtain ⟨hn, hK, hP⟩ := hAic T hT
  obtain ⟨hH, hs⟩ := hA
  obtain ⟨hd, -, hinj⟩ := hInd (Polynomial T) A hI
  have hinjT : Function.Injective (algebraMap T A) := by
    rw [IsScalarTower.algebraMap_eq T (Polynomial T) A, RingHom.coe_comp]
    exact hinj.comp Polynomial.C_injective
  haveI := hLoc T A hinjT
  have hqK : IsUnit (q : FractionRing T) := by simpa using hq.map (algebraMap T (FractionRing T))
  intro n
  rcases lt_trichotomy n 0 with h | h | h
  · exact bij_of_subsingleton _ ((hA9 _ _).1 _ n h) ((hA9 _ _).1 _ n h)
  · subst h
    exact hH0 q A _ _ ⟨(hP q hq).some.map (algebraMap T A)⟩ i
  · refine bij_of_subsingleton _ (hB2 _ A ⟨hH, hs⟩ _ n h) ?_
    rcases (show n = 1 ∨ 2 ≤ n by omega) with h1 | h2
    · subst h1
      exact hD1 q T hT hq A ⟨hH, hs⟩ hI i
    · exact hD2 q (FractionRing T) _ (genHom T (FractionRing T) A) hqK (hBc T _ A hI) n i h2

end LateralTheory.EtaleFoundations.CongruenceLocalDecomposition
