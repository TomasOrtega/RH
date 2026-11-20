import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open GlobalTheory

namespace GlobalTheory.GermInterp

/- English proof (translation)
Establish `hT : {J : Ideal R | Q ≤ J ∧ J.IsMaximal}.Finite`. Use `(hfin.image PrimeSpectrum.asIdeal).subset ?_` and prove the remaining obligations. Introduce and unpack `J ⟨hQJ, hJ⟩`. Conclude with `⟨⟨J, hJ.isPrime⟩, le_trans hI hQJ, rfl⟩`. Establish `hJac : Q.jacobson = Q` using `IsJacobsonRing.out inferInstance hQ.isRadical`.

Establish `hinf : hT.toFinset.inf id ≤ Q`. Rewrite using `[Finset.inf_id_eq_sInf, Set.Finite.coe_toFinset]`. Conclude with `hJac.le`. Take `⟨M, hM, hMQ⟩` from `hQ.inf_le'.1 hinf`. Rewrite `hM` using `[Set.Finite.mem_toFinset]`.

Rewrite using `[show Q = M from le_antisymm hM.1 hMQ]`. Conclude with `hM.2`.
-/
theorem isMaximal_of_finite_primes {R : Type*} [CommRing R] [IsJacobsonRing R] (I : Ideal R)
    (hfin : {P : PrimeSpectrum R | I ≤ P.asIdeal}.Finite) (Q : Ideal R) (hQ : Q.IsPrime) (hI : I ≤ Q) :
    Q.IsMaximal := by
  have hT : {J : Ideal R | Q ≤ J ∧ J.IsMaximal}.Finite := by
    refine (hfin.image PrimeSpectrum.asIdeal).subset ?_
    rintro J ⟨hQJ, hJ⟩
    exact ⟨⟨J, hJ.isPrime⟩, le_trans hI hQJ, rfl⟩
  have hJac : Q.jacobson = Q := IsJacobsonRing.out inferInstance hQ.isRadical
  have hinf : hT.toFinset.inf id ≤ Q := by
    rw [Finset.inf_id_eq_sInf, Set.Finite.coe_toFinset]
    exact hJac.le
  obtain ⟨M, hM, hMQ⟩ := hQ.inf_le'.1 hinf
  rw [Set.Finite.mem_toFinset] at hM
  rw [show Q = M from le_antisymm hM.1 hMQ]
  exact hM.2

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `hMP : ¬ M ≤ P` using `fun hle => hne (hM.eq_of_le hP.ne_top hle)`. Take `⟨m, hmM, hmP⟩` from `Set.not_subset.1 hMP`. Establish `hmeet : ¬ Disjoint (I : Set R) (↑(M.primeCompl ⊔ Submonoid.powers m) : Set R)`. Introduce `hdis`.

Take `⟨Q, hQ, hIQ, hQdis⟩` from `Ideal.exists_le_prime_disjoint I _ hdis`. Establish `hQM : Q ≤ M`. Introduce `x hx`. Assume the negation of the conclusion as `hxM`. Conclude with `Set.disjoint_left.1 hQdis hx (Submonoid.mem_sup_left (show x ∈ M.primeCompl from hxM))`.

Establish `hmQ : m ∉ Q` using `fun hm => Set.disjoint_left.1 hQdis hm (Submonoid.mem_sup_right (Submonoid.mem_powers m))`. Conclude with `hmQ (((hmax Q hQ hIQ).eq_of_le hM.ne_top hQM) ▸ hmM)`. Take `⟨w, hwI, hwW⟩` from `Set.not_disjoint_iff.1 hmeet`. Take `⟨v, hv, u, hu, rfl⟩` from `Submonoid.mem_sup.1 hwW`. Take `⟨k, rfl⟩` from `(Submonoid.mem_powers_iff _ _).1 hu`.

Establish `hunit : IsUnit (algebraMap R S (m ^ k))` using `IsLocalization.map_units S (⟨m ^ k, fun h => hmP (hP.mem_of_pow_mem k h)⟩ : P.primeCompl)`. Establish `hvmap : v ∈ (I.map (algebraMap R S)).comap (algebraMap R S)`. Rewrite using `[Ideal.mem_comap]`. Establish `hw` using `Ideal.mem_map_of_mem (algebraMap R S) hwI`. Rewrite `hw` using `[map_mul]`.

Conclude with `(Ideal.mul_unit_mem_iff_mem _ hunit).1 hw`. Conclude with `hv (h hvmap)`.
-/
theorem eq_of_comap_map_le {R : Type*} [CommRing R] (I : Ideal R)
    (hmax : ∀ Q : Ideal R, Q.IsPrime → I ≤ Q → Q.IsMaximal) (P : Ideal R) [hP : P.IsPrime] (hI : I ≤ P)
    (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.AtPrime S P] (M : Ideal R) (hM : M.IsMaximal)
    (h : (I.map (algebraMap R S)).comap (algebraMap R S) ≤ M) : M = P := by
  by_contra hne
  have hMP : ¬ M ≤ P := fun hle => hne (hM.eq_of_le hP.ne_top hle)
  obtain ⟨m, hmM, hmP⟩ := Set.not_subset.1 hMP
  have hmeet : ¬ Disjoint (I : Set R) (↑(M.primeCompl ⊔ Submonoid.powers m) : Set R) := by
    intro hdis
    obtain ⟨Q, hQ, hIQ, hQdis⟩ := Ideal.exists_le_prime_disjoint I _ hdis
    have hQM : Q ≤ M := by
      intro x hx
      by_contra hxM
      exact Set.disjoint_left.1 hQdis hx
        (Submonoid.mem_sup_left (show x ∈ M.primeCompl from hxM))
    have hmQ : m ∉ Q := fun hm =>
      Set.disjoint_left.1 hQdis hm (Submonoid.mem_sup_right (Submonoid.mem_powers m))
    exact hmQ (((hmax Q hQ hIQ).eq_of_le hM.ne_top hQM) ▸ hmM)
  obtain ⟨w, hwI, hwW⟩ := Set.not_disjoint_iff.1 hmeet
  obtain ⟨v, hv, u, hu, rfl⟩ := Submonoid.mem_sup.1 hwW
  obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 hu
  have hunit : IsUnit (algebraMap R S (m ^ k)) :=
    IsLocalization.map_units S (⟨m ^ k, fun h => hmP (hP.mem_of_pow_mem k h)⟩ : P.primeCompl)
  have hvmap : v ∈ (I.map (algebraMap R S)).comap (algebraMap R S) := by
    rw [Ideal.mem_comap]
    have hw := Ideal.mem_map_of_mem (algebraMap R S) hwI
    rw [map_mul] at hw
    exact (Ideal.mul_unit_mem_iff_mem _ hunit).1 hw
  exact hv (h hvmap)

/- English proof (translation)
Establish `hmax : ∀ Q : Ideal R, Q.IsPrime → I ≤ Q → Q.IsMaximal` using `fun Q hQ hIQ => isMaximal_of_finite_primes I hfin Q hQ hIQ`. Set `N : κ → Ideal R` to `fun i => (I.map (algebraMap R (S i))).comap (algebraMap R (S i))`. Establish `key : ∀ i (M : Ideal R), M.IsMaximal → N i ≤ M → M = (P i).asIdeal` using `fun i M hM hle => eq_of_comap_map_le I hmax (P i).asIdeal (hI i) (S i) M hM hle`. Establish `hcop : Pairwise fun i j => IsCoprime (N i) (N j)`. Introduce `i j hij`.

Rewrite using `[Ideal.isCoprime_iff_sup_eq]`. Assume the negation of the conclusion as `hne`. Take `⟨M, hM, hle⟩` from `Ideal.exists_le_maximal _ hne`. Establish `e1` using `key i M hM (le_trans le_sup_left hle)`. Establish `e2` using `key j M hM (le_trans le_sup_right hle)`.

Conclude with `hij (hinj (PrimeSpectrum.ext (e1.symm.trans e2)))`. Establish `hfrac : ∀ i, ∃ x : R, ∃ s : (P i).asIdeal.primeCompl, IsLocalization.mk' (S i) x s = a i`. Introduce `i`. Take `⟨⟨x, s⟩, h⟩` from `IsLocalization.mk'_surjective (P i).asIdeal.primeCompl (a i)`. Conclude with `⟨x, s, h⟩`.

Use `choose x s hxs using hfrac`. Establish `hinv : ∀ i, ∃ t : R, (s i : R) * t - 1 ∈ N i`. Introduce `i`. Establish `hsup : N i ⊔ Ideal.span {(s i : R)} = ⊤`. Assume the negation of the conclusion as `hne`.

Take `⟨M, hM, hle⟩` from `Ideal.exists_le_maximal _ hne`. Establish `e` using `key i M hM (le_trans le_sup_left hle)`. Establish `hsM : (s i : R) ∈ M` using `hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))`. Rewrite `hsM` using `[e]`. Conclude with `(s i).2 hsM`.

Establish `h1 : (1 : R) ∈ N i ⊔ Ideal.span {(s i : R)}` using `hsup ▸ Submodule.mem_top`. Take `⟨y, hy, z, hz, hyz⟩` from `Submodule.mem_sup.1 h1`. Take `⟨t, rfl⟩` from `Ideal.mem_span_singleton'.1 hz`. Use `⟨t, ?_⟩` and prove the remaining obligations. Establish `e : (s i : R) * t - 1 = -y` using `by rw [← hyz]; ring`.

Rewrite using `[e]`. Conclude with `(N i).neg_mem hy`. Use `choose t ht using hinv`. Take `⟨z, hz⟩` from `Ideal.quotientInfToPiQuotient_surj hcop (fun i => Ideal.Quotient.mk (N i) (x i * t i))`. Take `⟨r, rfl⟩` from `Ideal.Quotient.mk_surjective z`.

Use `⟨r, fun i => ?_⟩` and prove the remaining obligations. Establish `hri : r - x i * t i ∈ N i`. Establish `e` using `congrFun hz i`. Rewrite `e` using `[Ideal.quotientInfToPiQuotient_mk']`. Conclude with `Ideal.Quotient.eq.1 e`.

Establish `h1 : algebraMap R (S i) r - algebraMap R (S i) (x i * t i) ∈ I.map (algebraMap R (S i))`. Rewrite using `[← map_sub]`. Conclude with `Ideal.mem_comap.1 hri`. Establish `h2 : algebraMap R (S i) (x i * t i) - a i ∈ I.map (algebraMap R (S i))`. Rewrite using `[← hxs i]`.

Establish `hst : algebraMap R (S i) ((s i : R) * t i - 1) ∈ I.map (algebraMap R (S i))` using `Ideal.mem_comap.1 (ht i)`. Establish `hspec` using `IsLocalization.mk'_spec (S i) (x i) (s i)`. Establish `e : algebraMap R (S i) (x i * t i) - IsLocalization.mk' (S i) (x i) (s i) = IsLocalization.mk' (S i) (x i) (s i) * algebraMap R (S i) ((s i : R) * t i - 1)`. Simplify using `only [map_sub, map_mul, map_one]`. Take the linear combination `(-(algebraMap R (S i) (t i))) * hspec`.

Rewrite using `[e]`. Conclude with `Ideal.mul_mem_left _ _ hst`. Use `Ideal.add_mem _ h1 h2 using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_sub_mem_map {R : Type*} [CommRing R] [IsJacobsonRing R] (I : Ideal R)
    (hfin : {P : PrimeSpectrum R | I ≤ P.asIdeal}.Finite) {κ : Type*} [Finite κ] (P : κ → PrimeSpectrum R)
    (hinj : Function.Injective P) (hI : ∀ i, I ≤ (P i).asIdeal) (S : κ → Type*) [∀ i, CommRing (S i)]
    [∀ i, Algebra R (S i)] [∀ i, IsLocalization.AtPrime (S i) (P i).asIdeal] (a : ∀ i, S i) :
    ∃ r : R, ∀ i, algebraMap R (S i) r - a i ∈ I.map (algebraMap R (S i)) := by
  have hmax : ∀ Q : Ideal R, Q.IsPrime → I ≤ Q → Q.IsMaximal :=
    fun Q hQ hIQ => isMaximal_of_finite_primes I hfin Q hQ hIQ
  let N : κ → Ideal R := fun i => (I.map (algebraMap R (S i))).comap (algebraMap R (S i))
  have key : ∀ i (M : Ideal R), M.IsMaximal → N i ≤ M → M = (P i).asIdeal :=
    fun i M hM hle => eq_of_comap_map_le I hmax (P i).asIdeal (hI i) (S i) M hM hle
  have hcop : Pairwise fun i j => IsCoprime (N i) (N j) := by
    intro i j hij
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    have e1 := key i M hM (le_trans le_sup_left hle)
    have e2 := key j M hM (le_trans le_sup_right hle)
    exact hij (hinj (PrimeSpectrum.ext (e1.symm.trans e2)))
  have hfrac : ∀ i, ∃ x : R, ∃ s : (P i).asIdeal.primeCompl, IsLocalization.mk' (S i) x s = a i := by
    intro i
    obtain ⟨⟨x, s⟩, h⟩ := IsLocalization.mk'_surjective (P i).asIdeal.primeCompl (a i)
    exact ⟨x, s, h⟩
  choose x s hxs using hfrac
  have hinv : ∀ i, ∃ t : R, (s i : R) * t - 1 ∈ N i := by
    intro i
    have hsup : N i ⊔ Ideal.span {(s i : R)} = ⊤ := by
      by_contra hne
      obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
      have e := key i M hM (le_trans le_sup_left hle)
      have hsM : (s i : R) ∈ M := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
      rw [e] at hsM
      exact (s i).2 hsM
    have h1 : (1 : R) ∈ N i ⊔ Ideal.span {(s i : R)} := hsup ▸ Submodule.mem_top
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 h1
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 hz
    refine ⟨t, ?_⟩
    have e : (s i : R) * t - 1 = -y := by rw [← hyz]; ring
    rw [e]
    exact (N i).neg_mem hy
  choose t ht using hinv
  obtain ⟨z, hz⟩ := Ideal.quotientInfToPiQuotient_surj hcop (fun i => Ideal.Quotient.mk (N i) (x i * t i))
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
  refine ⟨r, fun i => ?_⟩
  have hri : r - x i * t i ∈ N i := by
    have e := congrFun hz i
    rw [Ideal.quotientInfToPiQuotient_mk'] at e
    exact Ideal.Quotient.eq.1 e
  have h1 : algebraMap R (S i) r - algebraMap R (S i) (x i * t i) ∈ I.map (algebraMap R (S i)) := by
    rw [← map_sub]
    exact Ideal.mem_comap.1 hri
  have h2 : algebraMap R (S i) (x i * t i) - a i ∈ I.map (algebraMap R (S i)) := by
    rw [← hxs i]
    have hst : algebraMap R (S i) ((s i : R) * t i - 1) ∈ I.map (algebraMap R (S i)) :=
      Ideal.mem_comap.1 (ht i)
    have hspec := IsLocalization.mk'_spec (S i) (x i) (s i)
    have e : algebraMap R (S i) (x i * t i) - IsLocalization.mk' (S i) (x i) (s i) =
        IsLocalization.mk' (S i) (x i) (s i) * algebraMap R (S i) ((s i : R) * t i - 1) := by
      simp only [map_sub, map_mul, map_one]
      linear_combination (-(algebraMap R (S i) (t i))) * hspec
    rw [e]
    exact Ideal.mul_mem_left _ _ hst
  convert Ideal.add_mem _ h1 h2 using 1
  ring

/- English proof (translation)
Establish `h1 : hV.primeIdealOf ⟨y, hy⟩ ∈ hV.fromSpec ⁻¹ᵁ X.basicOpen g ↔ y ∈ X.basicOpen g` using `by show hV.fromSpec (hV.primeIdealOf ⟨y, hy⟩) ∈ X.basicOpen g ↔ _`. Rewrite using `[hV.fromSpec_primeIdealOf]`. Rewrite `h1` using `[hV.fromSpec_preimage_basicOpen]`. Prove the components needed by the constructor for the conclusion. Introduce `hg hyb`.

Conclude with `(h1.2 hyb) hg`. Introduce `hyb`. Assume the negation of the conclusion as `hg`. Conclude with `hyb (h1.1 hg)`.
-/
theorem mem_primeIdealOf_iff {X : Scheme.{0}} {V : X.Opens} (hV : IsAffineOpen V) (y : X) (hy : y ∈ V)
    (g : Γ(X, V)) : g ∈ (hV.primeIdealOf ⟨y, hy⟩).asIdeal ↔ y ∉ X.basicOpen g := by
  have h1 : hV.primeIdealOf ⟨y, hy⟩ ∈ hV.fromSpec ⁻¹ᵁ X.basicOpen g ↔ y ∈ X.basicOpen g := by
    show hV.fromSpec (hV.primeIdealOf ⟨y, hy⟩) ∈ X.basicOpen g ↔ _
    rw [hV.fromSpec_primeIdealOf]
  rw [hV.fromSpec_preimage_basicOpen] at h1
  constructor
  · intro hg hyb
    exact (h1.2 hyb) hg
  · intro hyb
    by_contra hg
    exact hyb (h1.1 hg)

/- English proof (translation)
Introduce `K _ X p V J f a hft hV hfin`. Set `I : Ideal Γ(X, V)` to `Ideal.span (Set.range f)`. Set `Z` to `{y : X | y ∈ V ∧ ∀ i, y ∉ X.basicOpen (f i)}`. Establish `: Finite Z` using `hfin.to_subtype`. Set `P : Z → PrimeSpectrum Γ(X, V)` to `fun k => hV.primeIdealOf ⟨k.1, k.2.1⟩`.

Establish `hIP : ∀ k, I ≤ (P k).asIdeal`. Introduce `k`. Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `(mem_primeIdealOf_iff hV k.1 k.2.1 (f i)).2 (k.2.2 i)`.

Establish `hinj : Function.Injective P`. Introduce `k k' e`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `e1` using `hV.fromSpec_primeIdealOf ⟨k.1, k.2.1⟩`. Establish `e2` using `hV.fromSpec_primeIdealOf ⟨k'.1, k'.2.1⟩`.

Establish `e3 : hV.primeIdealOf ⟨k.1, k.2.1⟩ = hV.primeIdealOf ⟨k'.1, k'.2.1⟩` using `e`. Rewrite `e1` using `[e3]`. Conclude with `e1.symm.trans e2`. Establish `hfinR : {Q : PrimeSpectrum Γ(X, V) | I ≤ Q.asIdeal}.Finite`. Use `(Set.finite_range P).subset ?_` and prove the remaining obligations.

Introduce `Q hQ`. Establish `hyV : hV.fromSpec Q ∈ V` using `hV.range_fromSpec.le ⟨Q, rfl⟩`. Establish `hQeq : hV.primeIdealOf ⟨hV.fromSpec Q, hyV⟩ = Q` using `hV.fromSpec.isOpenEmbedding.injective (hV.fromSpec_primeIdealOf ⟨hV.fromSpec Q, hyV⟩)`. Use `⟨⟨hV.fromSpec Q, hyV, fun i => ?_⟩, hQeq⟩` and prove the remaining obligations. Establish `hfi : f i ∈ (hV.primeIdealOf ⟨hV.fromSpec Q, hyV⟩).asIdeal`.

Rewrite using `[hQeq]`. Conclude with `hQ (Ideal.subset_span ⟨i, rfl⟩)`. Conclude with `(mem_primeIdealOf_iff hV _ hyV (f i)).1 hfi`. Establish `: IsJacobsonRing Γ(Sp K, ⊤)` using `isJacobsonRing_of_surjective ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm.toRingHom, RingEquiv.surjective _⟩`. Establish `: IsJacobsonRing Γ(X, V)` using `RingHom.FiniteType.isJacobsonRing (Scheme.Hom.finiteType_appLE p (isAffineOpen_top (Sp K)) hV (by intro x _; simp))`.

Use `letI alg : ∀ k : Z, Algebra Γ(X, V) (X.presheaf.stalk k.1) := fun k => TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨k.1, k.2.1⟩`. Establish `loc : ∀ k : Z, IsLocalization.AtPrime (X.presheaf.stalk k.1) (P k).asIdeal` using `fun k => hV.isLocalization_stalk ⟨k.1, k.2.1⟩`. Take `⟨r, hr⟩` from `exists_sub_mem_map I hfinR P hinj hIP (fun k => X.presheaf.stalk k.1) (fun k => a k.1)`. Use `⟨r, fun y hy hz => ?_⟩` and prove the remaining obligations. Set `k : Z` to `⟨y, hy, hz⟩`.

Establish `hgs : ∀ g : Γ(X, V), gs (𝟙 X) y V g = algebraMap Γ(X, V) (X.presheaf.stalk k.1) g`. Introduce `g`. Rewrite using `[gs_eq (𝟙 X) y V hy g]`. Both sides reduce to the same expression. Establish `hk` using `hr k`.

Rewrite `hk` using `[Ideal.map_span, ← Set.range_comp]`. Establish `e : (fun i => gs (𝟙 X) y V (f i)) = (algebraMap Γ(X, V) (X.presheaf.stalk k.1)) ∘ f`. Use function extensionality and compare the values at `i`. Conclude with `hgs (f i)`. Rewrite using `[e, hgs r]`.

Conclude with `hk`.
-/
theorem exists_germ_sub_mem : ∀ (K : Type) [Field K] (X : Scheme.{0}) (p : X ⟶ Sp K) (V : X.Opens) (J : Type) (f : J → Γ(X, V)) (a : ∀ y : X, X.presheaf.stalk y), LocallyOfFiniteType p → IsAffineOpen V → Set.Finite {y : X | y ∈ V ∧ ∀ i, y ∉ X.basicOpen (f i)} → ∃ r : Γ(X, V), ∀ y : X, y ∈ V → (∀ i, y ∉ X.basicOpen (f i)) → gs (𝟙 X) y V r - a y ∈ Ideal.span (Set.range fun i => gs (𝟙 X) y V (f i)) := by
  intro K _ X p V J f a hft hV hfin
  let I : Ideal Γ(X, V) := Ideal.span (Set.range f)
  let Z := {y : X | y ∈ V ∧ ∀ i, y ∉ X.basicOpen (f i)}
  have : Finite Z := hfin.to_subtype
  let P : Z → PrimeSpectrum Γ(X, V) := fun k => hV.primeIdealOf ⟨k.1, k.2.1⟩
  have hIP : ∀ k, I ≤ (P k).asIdeal := by
    intro k
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact (mem_primeIdealOf_iff hV k.1 k.2.1 (f i)).2 (k.2.2 i)
  have hinj : Function.Injective P := by
    intro k k' e
    apply Subtype.ext
    have e1 := hV.fromSpec_primeIdealOf ⟨k.1, k.2.1⟩
    have e2 := hV.fromSpec_primeIdealOf ⟨k'.1, k'.2.1⟩
    have e3 : hV.primeIdealOf ⟨k.1, k.2.1⟩ = hV.primeIdealOf ⟨k'.1, k'.2.1⟩ := e
    rw [e3] at e1
    exact e1.symm.trans e2
  have hfinR : {Q : PrimeSpectrum Γ(X, V) | I ≤ Q.asIdeal}.Finite := by
    refine (Set.finite_range P).subset ?_
    intro Q hQ
    have hyV : hV.fromSpec Q ∈ V := hV.range_fromSpec.le ⟨Q, rfl⟩
    have hQeq : hV.primeIdealOf ⟨hV.fromSpec Q, hyV⟩ = Q :=
      hV.fromSpec.isOpenEmbedding.injective (hV.fromSpec_primeIdealOf ⟨hV.fromSpec Q, hyV⟩)
    refine ⟨⟨hV.fromSpec Q, hyV, fun i => ?_⟩, hQeq⟩
    have hfi : f i ∈ (hV.primeIdealOf ⟨hV.fromSpec Q, hyV⟩).asIdeal := by
      rw [hQeq]
      exact hQ (Ideal.subset_span ⟨i, rfl⟩)
    exact (mem_primeIdealOf_iff hV _ hyV (f i)).1 hfi
  have : IsJacobsonRing Γ(Sp K, ⊤) :=
    isJacobsonRing_of_surjective ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm.toRingHom,
      RingEquiv.surjective _⟩
  have : IsJacobsonRing Γ(X, V) :=
    RingHom.FiniteType.isJacobsonRing
      (Scheme.Hom.finiteType_appLE p (isAffineOpen_top (Sp K)) hV (by intro x _; simp))
  letI alg : ∀ k : Z, Algebra Γ(X, V) (X.presheaf.stalk k.1) :=
    fun k => TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨k.1, k.2.1⟩
  have loc : ∀ k : Z, IsLocalization.AtPrime (X.presheaf.stalk k.1) (P k).asIdeal :=
    fun k => hV.isLocalization_stalk ⟨k.1, k.2.1⟩
  obtain ⟨r, hr⟩ := exists_sub_mem_map I hfinR P hinj hIP (fun k => X.presheaf.stalk k.1) (fun k => a k.1)
  refine ⟨r, fun y hy hz => ?_⟩
  let k : Z := ⟨y, hy, hz⟩
  have hgs : ∀ g : Γ(X, V), gs (𝟙 X) y V g = algebraMap Γ(X, V) (X.presheaf.stalk k.1) g := by
    intro g
    rw [gs_eq (𝟙 X) y V hy g]
    rfl
  have hk := hr k
  rw [Ideal.map_span, ← Set.range_comp] at hk
  have e : (fun i => gs (𝟙 X) y V (f i)) = (algebraMap Γ(X, V) (X.presheaf.stalk k.1)) ∘ f := by
    funext i
    exact hgs (f i)
  rw [e, hgs r]
  exact hk

end GlobalTheory.GermInterp
