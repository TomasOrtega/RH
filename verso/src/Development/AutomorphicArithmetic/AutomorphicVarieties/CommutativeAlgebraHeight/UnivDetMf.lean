import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.UnivDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinE
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.GammaOneGammaZeroHomogeneousCocyclesFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LocallyConstantOfKernel

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.LocallyConstantOfKernel.lc_of_ker φ h`.
-/
private theorem lc_of_ker {G M : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group M]
    (φ : G →* M) (h : IsOpen (φ.ker : Set G)) : IsLocallyConstant φ :=
  _root_.UpperTheory.Reformulated.B.LocallyConstantOfKernel.lc_of_ker φ h

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(GDet.repAlg ρ A[X] _).det = _`. Use `congr 1`. Rewrite using `[map_sub, MonoidAlgebra.mapRingHom_single]`. Simplify using `[GDet.repAlg]`.
-/
private theorem chi_ofRep {n : ℕ} {A G : Type} [CommRing A] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) A) (g : G) :
    (GDet.ofRep ρ).chi (MonoidAlgebra.single g 1) =
      ((X : A[X]) • (1 : Matrix (Fin n) (Fin n) A[X]) - (ρ g).map (algebraMap A A[X])).det := by
  change (GDet.repAlg ρ A[X] _).det = _
  congr 1
  rw [map_sub, MonoidAlgebra.mapRingHom_single]
  simp [GDet.repAlg]

/- English proof (translation)
Introduce `i N`. Establish `h1 : IsLocallyConstant fun g j => χ j g`. Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `x`. Use `fun j => (lc_of_ker (χ j) (h j)).eventually_eq x` as an intermediate fact.

Conclude with `(Filter.eventually_all.2 this).mono fun y hy => funext hy`. Establish `h2` using `h1.comp fun v : Fin n → Aˣ => Ideal.Quotient.mk (I ^ N) ((-1) ^ i * (((X : A[X]) • (1 : Matrix (Fin n) (Fin n) A[X]) - (Matrix.diagonal fun j => (v j : A)).map (algebraMap A A[X])).det).coeff (n - i))`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `g`. Simplify using `only [GDet.lam, GDet.ofChars, chi_ofRep]`.

Both sides reduce to the same expression.
-/
private theorem cont_ofChars {n : ℕ} {A G : Type} [CommRing A] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (χ : Fin n → G →* Aˣ) (h : ∀ i, IsOpen ((χ i).ker : Set G)) (I : Ideal A) : (GDet.ofChars χ).IsCont I := by
  intro i N
  have h1 : IsLocallyConstant fun g j => χ j g := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have := fun j => (lc_of_ker (χ j) (h j)).eventually_eq x
    exact (Filter.eventually_all.2 this).mono fun y hy => funext hy
  have h2 := h1.comp fun v : Fin n → Aˣ => Ideal.Quotient.mk (I ^ N) ((-1) ^ i *
    (((X : A[X]) • (1 : Matrix (Fin n) (Fin n) A[X]) -
      (Matrix.diagonal fun j => (v j : A)).map (algebraMap A A[X])).det).coeff (n - i))
  convert h2 using 1
  funext g
  simp only [GDet.lam, GDet.ofChars, chi_ofRep]
  rfl

/- English proof (translation)
Establish `hinj : Function.Injective (residue k)` using `(residue k).injective`. Use `haveI : Finite (ResidueField k) := Finite.of_surjective _ residue_surjective`. Use `haveI : CharP (ResidueField k) l := charP_of_injective_ringHom hinj l`. Use `haveI : IsAdicComplete (maximalIdeal k) k := by`. Rewrite using `[maximalIdeal_eq_bot]`.

Use `infer_instance`. Set `u : kˣ →* (ResidueField k)ˣ` to `Units.map (residue k).toMonoidHom`. Establish `hu : Function.Injective u` using `Units.map_injective hinj`. Set `χ' : Fin n → G →* (ResidueField k)ˣ` to `fun i => u.comp (χ i)`. Establish `ho' : ∀ i, IsOpen ((χ' i).ker : Set G)` using `fun i => by`.

Establish `: (χ' i).ker = (χ i).ker` using `MonoidHom.ker_comp_of_injective _ _ hu`. Rewrite using `[this]`. Conclude with `ho i`. Establish `hi' : Function.Injective χ'` using `fun i j hij => hi (MonoidHom.ext fun g => hu (DFunLike.congr_fun hij g))`. Take `⟨h, hm⟩` from `exists_multFree_of_phiCond_of_injective_chars l χ' hP ho' hi'`.

Establish `hmap : (GDet.ofChars χ).map (residue k) = GDet.ofChars χ'`. Unfold `GDet.ofChars`. Rewrite using `[(d_gmap (GDet.ofRep (GDet.diagRep χ))).2.2.2]`. Use `congr 1`. Use extensionality with `g a b`.

Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Simplify using `[GDet.diagRep, χ', u]`. Simplify using `[GDet.diagRep, hab]`. Conclude with `(finE (GDet.ofChars χ) χ' (cont_ofChars χ ho _) hmap hm ∅).2.1`.
-/
private theorem fin_field (l : ℕ) [Fact l.Prime] {n : ℕ} {k G : Type} [Field k] [Finite k] [CharP k l] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (χ : Fin n → G →* kˣ)
    (hP : PhiCond G l) (ho : ∀ i, IsOpen ((χ i).ker : Set G)) (hi : Function.Injective χ) :
    Module.Finite k ((GDet.ofChars χ).CHQuot ∅) := by
  have hinj : Function.Injective (residue k) := (residue k).injective
  haveI : Finite (ResidueField k) := Finite.of_surjective _ residue_surjective
  haveI : CharP (ResidueField k) l := charP_of_injective_ringHom hinj l
  haveI : IsAdicComplete (maximalIdeal k) k := by
    rw [maximalIdeal_eq_bot]
    infer_instance
  let u : kˣ →* (ResidueField k)ˣ := Units.map (residue k).toMonoidHom
  have hu : Function.Injective u := Units.map_injective hinj
  let χ' : Fin n → G →* (ResidueField k)ˣ := fun i => u.comp (χ i)
  have ho' : ∀ i, IsOpen ((χ' i).ker : Set G) := fun i => by
    have : (χ' i).ker = (χ i).ker := MonoidHom.ker_comp_of_injective _ _ hu
    rw [this]
    exact ho i
  have hi' : Function.Injective χ' := fun i j hij =>
    hi (MonoidHom.ext fun g => hu (DFunLike.congr_fun hij g))
  obtain ⟨h, hm⟩ := exists_multFree_of_phiCond_of_injective_chars l χ' hP ho' hi'
  have hmap : (GDet.ofChars χ).map (residue k) = GDet.ofChars χ' := by
    unfold GDet.ofChars
    rw [(d_gmap (GDet.ofRep (GDet.diagRep χ))).2.2.2]
    congr 1
    ext g a b
    by_cases hab : a = b
    · subst hab
      simp [GDet.diagRep, χ', u]
    · simp [GDet.diagRep, hab]
  exact (finE (GDet.ofChars χ) χ' (cont_ofChars χ ho _) hmap hm ∅).2.1

/- English proof (translation)
Introduce `l _ O _ _ _ _ _ _ n G _ _ _ _ _ χ hP ho hi`. Conclude with `univDet l O (GDet.ofChars χ) hP (cont_ofChars χ ho _) (fin_field l χ hP ho hi)`.
-/
theorem UpperTheory.V.CA.univDet_mf :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] [CharP (ResidueField O) l] {n : ℕ} {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (χ : Fin n → G →* (ResidueField O)ˣ), PhiCond G l → (∀ i, IsOpen ((χ i).ker : Set G)) → Function.Injective χ → ∃ (R : Type) (_ : CommRing R) (_ : Algebra O R) (_ : IsCO O R) (D : GDet n R G), IsUnivDet O (GDet.ofChars χ) D := by
  intro l _ O _ _ _ _ _ _ n G _ _ _ _ _ χ hP ho hi
  exact univDet l O (GDet.ofChars χ) hP (cont_ofChars χ ho _) (fin_field l χ hP ho hi)
