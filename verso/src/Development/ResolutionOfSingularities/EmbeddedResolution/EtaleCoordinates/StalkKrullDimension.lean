import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothRegular
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.AffineSpaceJacobson
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

private noncomputable def fromSpecStalkPoint (X : Scheme.{u}) (x : X)
    (p : PrimeSpectrum (X.presheaf.stalk x)) : X :=
  (X.fromSpecStalk x).base p

/- English proof (authored)
The canonical map from the spectrum of the local ring at x into X is a topological embedding. An embedding preserves and reflects specialization, giving the equivalence.
-/
private theorem fromSpecStalkPoint_specializes_iff (X : Scheme.{u}) (x : X)
    (p q : PrimeSpectrum (X.presheaf.stalk x)) :
    fromSpecStalkPoint X x p ⤳ fromSpecStalkPoint X x q ↔ p ⤳ q :=
  (AlgebraicGeometry.Scheme.Hom.isEmbedding (X.fromSpecStalk x)).toIsInducing.specializes_iff

/- English proof (authored)
The image of the spectrum of the local ring at x consists exactly of the generizations of x. Since y specializes to x, it has a preimage in that spectrum.
-/
private theorem exists_fromSpecStalkPoint_eq_of_specializes (X : Scheme.{u}) (x : X) {y : X} (h : y ⤳ x) :
    ∃ p : PrimeSpectrum (X.presheaf.stalk x), fromSpecStalkPoint X x p = y := by
  have hy : y ∈ Set.range (X.fromSpecStalk x).base := by
    rw [AlgebraicGeometry.Scheme.range_fromSpecStalk]; exact h
  obtain ⟨p, hp⟩ := hy
  exact ⟨p, hp⟩

/- English proof (authored)
The ring dimension of the local ring equals the topological dimension of its spectrum. The canonical map embeds this spectrum into X, and the topological dimension of the embedded subspace is bounded by that of X.
-/
theorem ringKrullDim_stalk_le_topologicalKrullDim (X : Scheme.{u}) (x : X) :
    ringKrullDim (X.presheaf.stalk x) ≤ topologicalKrullDim X := by
  have hemb : Topology.IsEmbedding (X.fromSpecStalk x).base :=
    AlgebraicGeometry.Scheme.Hom.isEmbedding (X.fromSpecStalk x)
  have h1 : ringKrullDim (X.presheaf.stalk x) ≤
      topologicalKrullDim (PrimeSpectrum (X.presheaf.stalk x)) :=
    (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _).ge
  have h2 : topologicalKrullDim ↥(Spec (X.presheaf.stalk x)) ≤ topologicalKrullDim ↥X :=
    hemb.toIsInducing.topologicalKrullDim_le
  exact le_trans h1 h2

/- English proof (authored)
The canonical map from the stalk spectrum is a topological embedding. Apply reflection of specialization to the two image points.
-/
private theorem specializes_of_fromSpecStalk_base_specializes {X : Scheme.{u}} (x : X)
    {a b : PrimeSpectrum (X.presheaf.stalk x)}
    (hab : (X.fromSpecStalk x).base a ⤳ (X.fromSpecStalk x).base b) : a ⤳ b := by
  have hemb : Topology.IsEmbedding (X.fromSpecStalk x).base :=
    AlgebraicGeometry.Scheme.Hom.isEmbedding (X.fromSpecStalk x)
  exact hemb.toIsInducing.specializes_iff.mp hab

/- English proof (authored)
Take any strict chain of irreducible closed subsets of X. Choose the generic point of each subset. Inclusions in the chain give specializations from the larger subsets' generic points to the smaller ones. Distinct closed subsets have distinct generic points.

All these generic points are generizations of the generic point of the smallest subset, so they lift to the spectrum of the local ring there. The embedding reflects specialization, and the distinctness of the image points gives strictness. In reverse order the lifted points form a prime chain of the same length. The local dimension bound therefore bounds the length of the original chain. Taking the supremum over the chains gives the topological bound.
-/
theorem topologicalKrullDim_le_of_forall_ringKrullDim_stalk_le (X : Scheme.{u}) (d : WithBot ℕ∞)
    (h : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ d) :
    topologicalKrullDim X ≤ d := by
  unfold topologicalKrullDim
  refine iSup_le fun p => ?_
  have hSM := p.strictMono
  have key : ∀ i : Fin (p.length + 1), ∃ z : X, closure ({z} : Set X) = (p i : Set X) := by
    intro i
    obtain ⟨z, hz⟩ := QuasiSober.sober (p i).isIrreducible' (p i).isClosed'
    exact ⟨z, hz⟩
  choose y hy using key
  have hspec : ∀ i j : Fin (p.length + 1), i ≤ j → y j ⤳ y i := by
    intro i j hij
    have hsub : (p i : Set X) ⊆ (p j : Set X) :=
      SetLike.coe_subset_coe.mpr (hSM.monotone hij)
    have hmem : y i ∈ closure ({y j} : Set X) := by
      rw [hy j]
      apply hsub
      rw [← hy i]
      exact subset_closure rfl
    exact specializes_iff_mem_closure.mpr hmem
  have hinj : Function.Injective y := by
    intro i j hij
    apply hSM.injective
    apply SetLike.coe_injective
    rw [← hy i, ← hy j, hij]
  have hrange : ∀ i : Fin (p.length + 1),
      ∃ z : PrimeSpectrum (X.presheaf.stalk (y 0)), (X.fromSpecStalk (y 0)).base z = y i := by
    intro i
    have hmem : y i ∈ Set.range (X.fromSpecStalk (y 0)).base := by
      rw [Scheme.range_fromSpecStalk]
      exact hspec 0 i (Fin.zero_le i)
    exact hmem
  choose q hq using hrange
  have hg : StrictMono (fun i : Fin (p.length + 1) => q i.rev) := by
    intro i j hij
    have hlt : j.rev < i.rev := Fin.rev_lt_rev.mpr hij
    have hsp : (X.fromSpecStalk (y 0)).base (q i.rev) ⤳ (X.fromSpecStalk (y 0)).base (q j.rev) := by
      rw [hq i.rev, hq j.rev]
      exact hspec j.rev i.rev hlt.le
    have hle : q i.rev ≤ q j.rev :=
      (PrimeSpectrum.le_iff_specializes _ _).mpr
        (specializes_of_fromSpecStalk_base_specializes (y 0) hsp)
    refine lt_of_le_of_ne hle ?_
    intro hcon
    have hcon' : q i.rev = q j.rev := hcon
    have hyy : y i.rev = y j.rev :=
      (hq i.rev).symm.trans
        ((congrArg (fun z : PrimeSpectrum (X.presheaf.stalk (y 0)) =>
          (X.fromSpecStalk (y 0)).base z) hcon').trans (hq j.rev))
    have h4 := congrArg Fin.rev (hinj hyy)
    rw [Fin.rev_rev, Fin.rev_rev] at h4
    exact absurd h4 (ne_of_lt hij)
  have hlen : (p.length : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk (y 0)) :=
    le_iSup (fun t : LTSeries (PrimeSpectrum (X.presheaf.stalk (y 0))) => (t.length : WithBot ℕ∞))
      ⟨p.length, fun i => q i.rev, fun i => hg Fin.castSucc_lt_succ⟩
  exact le_trans hlen (h (y 0))

/- English proof (authored)
The map on stalks of the étale morphism is local, flat, essentially of finite type, and formally unramified. The source and target rings of this local map satisfy the regularity and Noetherian hypotheses of the dimension equality theorem. Their dimensions are therefore equal, giving the asserted inequality.
-/
theorem ringKrullDim_stalk_le_of_etale {Y W : Scheme.{u}} (f : Y ⟶ W)
    [AlgebraicGeometry.Etale f] (y : Y) [IsNoetherianRing (Y.presheaf.stalk y)]
    [_root_.IsRegularLocalRing (W.presheaf.stalk (f.base y))] :
    ringKrullDim (Y.presheaf.stalk y) ≤ ringKrullDim (W.presheaf.stalk (f.base y)) := by
  have hft : (f.stalkMap y).hom.EssFiniteType :=
    AlgebraicGeometry.LocallyOfFiniteType.stalkMap f y
  have hfu : (f.stalkMap y).hom.FormallyUnramified :=
    AlgebraicGeometry.FormallyUnramified.stalkMap f y
  let algStalk : Algebra (W.presheaf.stalk (f.base y)) (Y.presheaf.stalk y) :=
    (f.stalkMap y).hom.toAlgebra
  have : IsLocalHom (algebraMap (W.presheaf.stalk (f.base y)) (Y.presheaf.stalk y)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap y).hom)
  have : Module.Flat (W.presheaf.stalk (f.base y)) (Y.presheaf.stalk y) :=
    AlgebraicGeometry.Flat.stalkMap f y
  have : Algebra.EssFiniteType (W.presheaf.stalk (f.base y)) (Y.presheaf.stalk y) := hft
  have : Algebra.FormallyUnramified (W.presheaf.stalk (f.base y)) (Y.presheaf.stalk y) := hfu
  exact le_of_eq (FunctorialResolution.EmbeddedResolution.ringKrullDim_eq_of_flat_formallyUnramified
    (W.presheaf.stalk (f.base y)) (Y.presheaf.stalk y))

/- English proof (authored)
The étale morphism induces a local map from the stalk on W to the stalk on Y which is flat, formally unramified, and essentially of finite type. Apply the local dimension equality theorem, using regularity of the stalk on W and Noetherianity of the stalk on Y.
-/
theorem ringKrullDim_stalk_eq_of_etale {Y W : Scheme.{u}} (f : Y ⟶ W)
    [AlgebraicGeometry.Etale f] (y : Y) [IsNoetherianRing (Y.presheaf.stalk y)]
    [_root_.IsRegularLocalRing (W.presheaf.stalk (f.base y))] :
    ringKrullDim (Y.presheaf.stalk y) = ringKrullDim (W.presheaf.stalk (f.base y)) := by
  have hft : (f.stalkMap y).hom.EssFiniteType :=
    AlgebraicGeometry.LocallyOfFiniteType.stalkMap f y
  have hfu : (f.stalkMap y).hom.FormallyUnramified :=
    AlgebraicGeometry.FormallyUnramified.stalkMap f y
  let algStalk : Algebra (W.presheaf.stalk (f.base y)) (Y.presheaf.stalk y) :=
    (f.stalkMap y).hom.toAlgebra
  have : IsLocalHom (algebraMap (W.presheaf.stalk (f.base y)) (Y.presheaf.stalk y)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap y).hom)
  have : Module.Flat (W.presheaf.stalk (f.base y)) (Y.presheaf.stalk y) :=
    AlgebraicGeometry.Flat.stalkMap f y
  have : Algebra.EssFiniteType (W.presheaf.stalk (f.base y)) (Y.presheaf.stalk y) := hft
  have : Algebra.FormallyUnramified (W.presheaf.stalk (f.base y)) (Y.presheaf.stalk y) := hfu
  exact FunctorialResolution.EmbeddedResolution.ringKrullDim_eq_of_flat_formallyUnramified
    (W.presheaf.stalk (f.base y)) (Y.presheaf.stalk y)

/- English proof (authored)
Identify the affine scheme with the spectrum of its global section ring. Extend the prime corresponding to a to a maximal ideal. Its point is closed in the spectrum and remains closed under the affine homeomorphism.
-/
private theorem exists_isClosed_singleton_of_isAffine (A : Scheme.{u}) [IsAffine A] (a : A) :
    ∃ x : A, IsClosed ({x} : Set A) := by
  have h : ↥A ≃ₜ PrimeSpectrum ↥Γ(A, ⊤) := Scheme.homeoOfIso A.isoSpec
  have hp : PrimeSpectrum ↥Γ(A, ⊤) := h a
  obtain ⟨M, hM, -⟩ := Ideal.exists_le_maximal hp.asIdeal hp.isPrime.ne_top
  refine ⟨h.symm ⟨M, hM.isPrime⟩, ?_⟩
  have hq : IsClosed ({(⟨M, hM.isPrime⟩ : PrimeSpectrum ↥Γ(A, ⊤))} :
      Set (PrimeSpectrum ↥Γ(A, ⊤))) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr hM
  have h2 := h.symm.isClosedMap _ hq
  rwa [Set.image_singleton] at h2

/- English proof (authored)
A point of U exists by nonemptiness. The open subscheme U is affine, so the result for a nonempty affine scheme gives a closed point of U.
-/
theorem exists_isClosed_singleton_of_isAffineOpen {X : Scheme.{u}} (U : X.Opens)
    (hU : IsAffineOpen U) (hne : (U : Set X).Nonempty) :
    ∃ x : U.toScheme, IsClosed ({x} : Set U.toScheme) := by
  have : IsAffine U.toScheme := hU
  obtain ⟨x0, hx0⟩ := hne
  exact exists_isClosed_singleton_of_isAffine U.toScheme ⟨x0, hx0⟩

/- English proof (authored)
Choose a closed point of the affine open subscheme U by the preceding result. It consists of a point of X together with its membership in U. Take those data and the closedness proof in U.
-/
theorem exists_mem_isClosed_singleton_of_isAffineOpen {X : Scheme.{u}} (U : X.Opens)
    (hU : IsAffineOpen U) (hne : (U : Set X).Nonempty) :
    ∃ x : X, ∃ hx : x ∈ U, IsClosed ({(⟨x, hx⟩ : U.toScheme)} : Set U.toScheme) := by
  obtain ⟨x, hx⟩ := exists_isClosed_singleton_of_isAffineOpen U hU hne
  obtain ⟨y, hy⟩ := x
  exact ⟨y, hy, hx⟩

/- English proof (authored)
The topological Krull dimension of the prime spectrum of a ring equals the ring's Krull dimension. The displayed inequality follows.
-/
private theorem topologicalKrullDim_spec_le_ringKrullDim (R : CommRingCat.{u}) :
    topologicalKrullDim ↥(Spec R) ≤ ringKrullDim ↥R := by
  have h : topologicalKrullDim (PrimeSpectrum ↥R) = ringKrullDim ↥R :=
    PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim ↥R
  exact le_of_eq h

/- English proof (authored)
The affine-space isomorphism identifies it with the spectrum of the coordinate polynomial ring. The topological dimension equals that of this spectrum, which is the ring dimension of the polynomial ring.
-/
private theorem topologicalKrullDim_affineSpace_le_ringKrullDim (k : Type u) [Field k] (m : ℕ) :
    topologicalKrullDim ↥(AffineSpace (ULift.{u} (Fin m)) (Spec (CommRingCat.of k))) ≤
      ringKrullDim (MvPolynomial (ULift.{u} (Fin m)) k) := by
  let e := Scheme.homeoOfIso (AffineSpace.SpecIso (ULift.{u} (Fin m)) (CommRingCat.of k))
  have h3 := (Homeomorph.isEmbedding e).toIsInducing.topologicalKrullDim_le
  exact h3.trans
    (topologicalKrullDim_spec_le_ringKrullDim
      (CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k)))

/- English proof (authored)
The two index sets are bijective, so renaming the variables gives an isomorphism to the polynomial ring in m variables. Ring isomorphisms preserve Krull dimension, and that polynomial ring over the field has dimension m.
-/
private theorem ringKrullDim_mvPolynomial_uLift_le (k : Type u) [Field k] (m : ℕ) :
    ringKrullDim (MvPolynomial (ULift.{u} (Fin m)) k) ≤ ((m : ℕ∞) : WithBot ℕ∞) := by
  have he : ringKrullDim (MvPolynomial (ULift.{u} (Fin m)) k)
      = ringKrullDim (MvPolynomial (Fin m) k) :=
    ringKrullDim_eq_of_ringEquiv
      (MvPolynomial.renameEquiv k (Equiv.ulift : ULift.{u} (Fin m) ≃ Fin m)).toRingEquiv
  rw [he]
  simp

/- English proof (authored)
The affine-space stalk at the image is regular. The étale stalk dimension comparison bounds the dimension at y by the dimension of that target stalk. The target stalk dimension is bounded by the dimension of the whole affine space via the embedding of its spectrum, and the affine space has dimension m by its polynomial description.
-/
theorem ringKrullDim_stalk_le_of_etale_affineSpace {k : Type u} [Field k] {m : ℕ} {Y : Scheme.{u}}
    (c : Y ⟶ AffineSpace (ULift.{u} (Fin m)) (Spec (CommRingCat.of k)))
    [AlgebraicGeometry.Etale c] (y : Y) [IsNoetherianRing (Y.presheaf.stalk y)] :
    ringKrullDim (Y.presheaf.stalk y) ≤ ((m : ℕ∞) : WithBot ℕ∞) := by
  have hreg : _root_.IsRegularLocalRing
      ((AffineSpace (ULift.{u} (Fin m)) (Spec (CommRingCat.of k))).presheaf.stalk (c.base y)) :=
    isRegularLocalRing_stalk_affineSpace k (ULift.{u} (Fin m)) (c.base y)
  have h1 : ringKrullDim (Y.presheaf.stalk y) ≤
      ringKrullDim ((AffineSpace (ULift.{u} (Fin m)) (Spec (CommRingCat.of k))).presheaf.stalk
        (c.base y)) := ringKrullDim_stalk_le_of_etale c y
  have h2 := ringKrullDim_stalk_le_topologicalKrullDim
      (AffineSpace (ULift.{u} (Fin m)) (Spec (CommRingCat.of k))) (c.base y)
  exact h1.trans (h2.trans ((topologicalKrullDim_affineSpace_le_ringKrullDim k m).trans
    (ringKrullDim_mvPolynomial_uLift_le k m)))

/- English proof (authored)
Contraction of an ideal twice is contraction along the composite of the two ring maps in the appropriate order. Here the composite applies the isomorphism and then its inverse, so it is the identity on A. The contracted ideal is I.
-/
private theorem comap_comap_symm {A B : Type u} [CommRing A] [CommRing B] (φ : A ≃+* B)
    (I : Ideal A) : Ideal.comap (φ : A →+* B) (Ideal.comap (φ.symm : B →+* A) I) = I := by
  refine Ideal.ext fun a => ?_
  have h : (φ.symm : B →+* A) ((φ : A →+* B) a) = a := φ.symm_apply_apply a
  constructor
  · intro hmem
    have hmem' : (φ.symm : B →+* A) ((φ : A →+* B) a) ∈ I := hmem
    rwa [h] at hmem'
  · intro hmem
    show (φ.symm : B →+* A) ((φ : A →+* B) a) ∈ I
    rw [h]
    exact hmem

/- English proof (authored)
The double contraction is along the composite that applies the inverse isomorphism and then the isomorphism. This is the identity on B and returns J.
-/
private theorem comap_symm_comap {A B : Type u} [CommRing A] [CommRing B] (φ : A ≃+* B)
    (J : Ideal B) : Ideal.comap (φ.symm : B →+* A) (Ideal.comap (φ : A →+* B) J) = J := by
  refine Ideal.ext fun b => ?_
  have h : (φ : A →+* B) ((φ.symm : B →+* A) b) = b := φ.apply_symm_apply b
  constructor
  · intro hmem
    have hmem' : (φ : A →+* B) ((φ.symm : B →+* A) b) ∈ J := hmem
    rwa [h] at hmem'
  · intro hmem
    show (φ : A →+* B) ((φ.symm : B →+* A) b) ∈ J
    rw [h]
    exact hmem

/- English proof (authored)
Contract every prime in the given chain along the ring isomorphism. Contraction preserves inclusion, and it reflects equality because contraction along the inverse isomorphism recovers the original prime. Thus strict inclusions remain strict. The new chain has the same length and its last prime is the contraction of the given last prime.
-/
private theorem exists_ltSeries_comap {A B : Type u} [CommRing A] [CommRing B] (φ : A ≃+* B)
    (s : LTSeries (PrimeSpectrum B)) :
    ∃ t : LTSeries (PrimeSpectrum A), t.length = s.length ∧
      t.last.asIdeal = Ideal.comap (φ : A →+* B) s.last.asIdeal := by
  have hmono : Monotone (PrimeSpectrum.comap (φ : A →+* B)) := by
    intro p q h
    rw [← PrimeSpectrum.asIdeal_le_asIdeal, PrimeSpectrum.comap_asIdeal,
      PrimeSpectrum.comap_asIdeal]
    exact Ideal.comap_mono ((PrimeSpectrum.asIdeal_le_asIdeal p q).mpr h)
  have hinj : Function.Injective (PrimeSpectrum.comap (φ : A →+* B)) := by
    intro p q h
    have h' : Ideal.comap (φ : A →+* B) p.asIdeal = Ideal.comap (φ : A →+* B) q.asIdeal := by
      rw [← PrimeSpectrum.comap_asIdeal, ← PrimeSpectrum.comap_asIdeal, h]
    have h2 := congrArg (Ideal.comap (φ.symm : B →+* A)) h'
    rw [comap_symm_comap φ p.asIdeal, comap_symm_comap φ q.asIdeal] at h2
    exact PrimeSpectrum.ext h2
  have hstrict := hmono.strictMono_of_injective hinj
  exact ⟨⟨s.length, fun i => PrimeSpectrum.comap (φ : A →+* B) (s i), fun i => hstrict (s.step i)⟩,
    rfl, rfl⟩

/- English proof (authored)
A constant polynomial belongs to the extended ideal exactly when all its coefficients belong to I. Its only possibly nonzero coefficient is the original scalar, so membership is equivalent to that scalar belonging to I. This identifies the contraction with I.
-/
private theorem comap_C_map_C {S : Type u} [CommRing S] (I : Ideal S) :
    Ideal.comap (Polynomial.C : S →+* Polynomial S) (I.map (Polynomial.C : S →+* Polynomial S))
      = I := by
  refine Ideal.ext fun a => ?_
  constructor
  · intro h
    have h2 : (Polynomial.C a) ∈ I.map (Polynomial.C : S →+* Polynomial S) := h
    have h3 := (Ideal.mem_map_C_iff).mp h2 0
    simpa using h3
  · intro h
    exact Ideal.mem_map_of_mem _ h

/- English proof (authored)
Over a Jacobson base the map from S to the quotient by the maximal polynomial ideal is integral. The quotient is a field, so contraction of its zero maximal ideal is maximal in S. That contraction is exactly the contraction of the given polynomial ideal along the constants.
-/
private theorem isMaximal_comap_C {S : Type u} [CommRing S] [IsJacobsonRing S]
    (M' : Ideal (Polynomial S)) (hM' : M'.IsMaximal) :
    (Ideal.comap (Polynomial.C : S →+* Polynomial S) M').IsMaximal := by
  have := hM'
  have hint : ((Ideal.Quotient.mk M').comp (Polynomial.C : S →+* Polynomial S)).IsIntegral :=
    Polynomial.quotient_mk_comp_C_isIntegral_of_isJacobsonRing M'
  have hbot : (⊥ : Ideal (Polynomial S ⧸ M')).IsMaximal := by
    let fieldQuot : Field (Polynomial S ⧸ M') := Ideal.Quotient.field M'
    exact Ideal.bot_isMaximal
  have hmax := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal'
    ((Ideal.Quotient.mk M').comp (Polynomial.C : S →+* Polynomial S)) hint
    (⊥ : Ideal (Polynomial S ⧸ M'))
  have hker : Ideal.comap ((Ideal.Quotient.mk M').comp (Polynomial.C : S →+* Polynomial S))
      (⊥ : Ideal (Polynomial S ⧸ M')) = Ideal.comap (Polynomial.C : S →+* Polynomial S) M' := by
    refine Ideal.ext fun a => ?_
    rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_bot, RingHom.comp_apply,
      Ideal.Quotient.eq_zero_iff_mem]
  rw [← hker]
  exact hmax

/- English proof (authored)
If the extension of N were the maximal ideal M′, the polynomial variable would be outside M′, since its coefficient of degree one is 1 outside N. In the field quotient by M′ its class would have an inverse. Thus some polynomial times the variable would agree with 1 modulo the ideal extended from N. Taking constant coefficients forces 1 to lie in N, since the polynomial times the variable has zero constant coefficient. This contradicts that N is proper.
-/
private theorem map_C_ne_of_isMaximal {S : Type u} [CommRing S] (N : Ideal S) (hN : N.IsMaximal)
    (M' : Ideal (Polynomial S)) (hM' : M'.IsMaximal) :
    N.map (Polynomial.C : S →+* Polynomial S) ≠ M' := by
  intro h
  have hX : (Polynomial.X : Polynomial S) ∉ M' := by
    rw [← h]
    intro hmem
    have h1 := (Ideal.mem_map_C_iff).mp hmem 1
    rw [Polynomial.coeff_X_one] at h1
    exact hN.ne_top ((Ideal.eq_top_iff_one N).mpr h1)
  obtain ⟨y, i, hi, hyi⟩ := hM'.exists_inv hX
  rw [← h] at hi
  have hc := (Ideal.mem_map_C_iff).mp hi 0
  have h0 : (y * Polynomial.X + i).coeff 0 = (1 : Polynomial S).coeff 0 := by rw [hyi]
  rw [Polynomial.coeff_add, Polynomial.coeff_one_zero, Polynomial.mul_coeff_zero,
    Polynomial.coeff_X_zero, mul_zero, zero_add] at h0
  have hone : (1 : S) ∈ N := by rw [← h0]; exact hc
  exact hN.ne_top ((Ideal.eq_top_iff_one N).mpr hone)

/- English proof (authored)
Induct on the number of variables. For zero variables the maximal ideal itself is a chain of length zero. For the successor step, view the ring as a polynomial ring in one variable over the ring with n variables. The smaller ring is Jacobson because it is of finite type over a field, so the contraction N of the given maximal ideal is maximal. By induction there is a chain of length n ending at N.

Extend the primes in that chain to the one-variable polynomial ring. Extension preserves primality because the quotient by an extended prime is a polynomial ring over a domain. It preserves strict inclusion because contracting along constants recovers the original ideals. The last extended prime is contained in the given maximal ideal and is strictly smaller by the preceding result. Append the maximal ideal and transport the chain back along the polynomial-ring isomorphism.
-/
private theorem exists_ltSeries_of_isMaximal_mvPolynomial (k : Type u) [Field k] :
    ∀ (m : ℕ) (M : Ideal (MvPolynomial (Fin m) k)), M.IsMaximal →
      ∃ s : LTSeries (PrimeSpectrum (MvPolynomial (Fin m) k)),
        s.length = m ∧ s.last.asIdeal = M := by
  intro m
  induction m with
  | zero =>
    intro M hM
    exact ⟨RelSeries.singleton _ ⟨M, hM.isPrime⟩, rfl, rfl⟩
  | succ n ih =>
    intro M hM
    have := hM
    have hJ : IsJacobsonRing (MvPolynomial (Fin n) k) := by
      have : Algebra.FiniteType k (MvPolynomial (Fin n) k) := inferInstance
      exact isJacobsonRing_of_finiteType (A := k)
    let φ : MvPolynomial (Fin (n + 1)) k ≃+* Polynomial (MvPolynomial (Fin n) k) :=
      (MvPolynomial.finSuccEquiv k n).toRingEquiv
    let M' : Ideal (Polynomial (MvPolynomial (Fin n) k)) :=
      Ideal.comap
        (φ.symm : Polynomial (MvPolynomial (Fin n) k) →+* MvPolynomial (Fin (n + 1)) k) M
    have hM'max : M'.IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ (RingEquiv.surjective φ.symm)
    let N : Ideal (MvPolynomial (Fin n) k) :=
      Ideal.comap
        (Polynomial.C : MvPolynomial (Fin n) k →+* Polynomial (MvPolynomial (Fin n) k)) M'
    have hNmax : N.IsMaximal := isMaximal_comap_C M' hM'max
    obtain ⟨t, htlen, htlast⟩ := ih N hNmax
    have hFs : StrictMono (fun p : PrimeSpectrum (MvPolynomial (Fin n) k) =>
        (⟨p.asIdeal.map
            (Polynomial.C : MvPolynomial (Fin n) k →+* Polynomial (MvPolynomial (Fin n) k)),
          (Ideal.isPrime_map_C_iff_isPrime p.asIdeal).mpr p.isPrime⟩ :
          PrimeSpectrum (Polynomial (MvPolynomial (Fin n) k)))) := by
      refine Monotone.strictMono_of_injective ?_ ?_
      · intro p q hpq
        rw [← PrimeSpectrum.asIdeal_le_asIdeal]
        exact Ideal.map_mono ((PrimeSpectrum.asIdeal_le_asIdeal p q).mpr hpq)
      · intro p q hpq
        have h' : p.asIdeal.map
              (Polynomial.C : MvPolynomial (Fin n) k →+* Polynomial (MvPolynomial (Fin n) k))
            = q.asIdeal.map
              (Polynomial.C : MvPolynomial (Fin n) k →+* Polynomial (MvPolynomial (Fin n) k)) :=
          congrArg PrimeSpectrum.asIdeal hpq
        refine PrimeSpectrum.ext ?_
        rw [← comap_C_map_C p.asIdeal, ← comap_C_map_C q.asIdeal, h']
    let t1 : LTSeries (PrimeSpectrum (Polynomial (MvPolynomial (Fin n) k))) :=
      ⟨t.length, fun i => ⟨(t i).asIdeal.map
          (Polynomial.C : MvPolynomial (Fin n) k →+* Polynomial (MvPolynomial (Fin n) k)),
        (Ideal.isPrime_map_C_iff_isPrime (t i).asIdeal).mpr (t i).isPrime⟩,
        fun i => hFs (t.step i)⟩
    have ht1last : t1.last.asIdeal = N.map
        (Polynomial.C : MvPolynomial (Fin n) k →+* Polynomial (MvPolynomial (Fin n) k)) := by
      show (t.last).asIdeal.map
          (Polynomial.C : MvPolynomial (Fin n) k →+* Polynomial (MvPolynomial (Fin n) k)) = _
      rw [htlast]
    have hle : t1.last.asIdeal ≤ M' := by
      rw [ht1last]
      exact Ideal.map_le_iff_le_comap.mpr le_rfl
    have hlt : t1.last <
        (⟨M', hM'max.isPrime⟩ : PrimeSpectrum (Polynomial (MvPolynomial (Fin n) k))) := by
      refine lt_of_le_of_ne ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mp hle) ?_
      intro hEq
      have hEq' : t1.last.asIdeal = M' := congrArg PrimeSpectrum.asIdeal hEq
      rw [ht1last] at hEq'
      exact map_C_ne_of_isMaximal N hNmax M' hM'max hEq'
    obtain ⟨s, hslen, hslast⟩ := exists_ltSeries_comap φ (t1.snoc _ hlt)
    refine ⟨s, ?_, ?_⟩
    · rw [hslen]
      show t.length + 1 = n + 1
      rw [htlen]
    · rw [hslast, RelSeries.last_snoc]
      exact comap_comap_symm φ M

/- English proof (authored)
Reindex the variables by the bijection with the ordinary finite index set. The maximal ideal corresponds to a maximal ideal in the ordinary polynomial ring, where the preceding result gives the chain. Contraction along the isomorphism transports the chain back, preserving its length and recovering the original maximal ideal at its end.
-/
private theorem exists_ltSeries_of_isMaximal_mvPolynomial_uLift (k : Type u) [Field k] (m : ℕ)
    (M : Ideal (MvPolynomial (ULift.{u} (Fin m)) k)) (hM : M.IsMaximal) :
    ∃ s : LTSeries (PrimeSpectrum (MvPolynomial (ULift.{u} (Fin m)) k)),
      s.length = m ∧ s.last.asIdeal = M := by
  have := hM
  let φ : MvPolynomial (ULift.{u} (Fin m)) k ≃+* MvPolynomial (Fin m) k :=
    (MvPolynomial.renameEquiv k (Equiv.ulift : ULift.{u} (Fin m) ≃ Fin m)).toRingEquiv
  have hmax :
      (Ideal.comap (φ.symm : MvPolynomial (Fin m) k →+* MvPolynomial (ULift.{u} (Fin m)) k)
        M).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ (RingEquiv.surjective φ.symm)
  obtain ⟨t, htlen, htlast⟩ := exists_ltSeries_of_isMaximal_mvPolynomial k m _ hmax
  obtain ⟨s, hslen, hslast⟩ := exists_ltSeries_comap φ t
  refine ⟨s, by rw [hslen, htlen], ?_⟩
  rw [hslast, htlast]
  exact comap_comap_symm φ M

/- English proof (authored)
Each point in the specialization chain is a generization of x, so lift it to the spectrum of the stalk at x. The embedding reflects each specialization as inclusion of the lifted primes. The given points are distinct, so adjacent inclusions of primes are strict. This gives a prime chain of length n in the stalk and hence the lower bound.
-/
private theorem le_ringKrullDim_stalk_of_chain (X : Scheme.{u}) (x : X) (n : ℕ)
    (z : Fin (n + 1) → X) (hspec : ∀ i, z i ⤳ x)
    (hmono : ∀ i j : Fin (n + 1), i < j → z i ⤳ z j) (hinj : Function.Injective z) :
    ((n : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x) := by
  choose q hq using fun i => exists_fromSpecStalkPoint_eq_of_specializes X x (hspec i)
  have hstep : ∀ i : Fin n, q i.castSucc < q i.succ := by
    intro i
    have h1 : fromSpecStalkPoint X x (q i.castSucc) ⤳ fromSpecStalkPoint X x (q i.succ) := by
      rw [hq i.castSucc, hq i.succ]
      exact hmono _ _ Fin.castSucc_lt_succ
    have hle : q i.castSucc ≤ q i.succ :=
      (PrimeSpectrum.le_iff_specializes _ _).mpr
        ((fromSpecStalkPoint_specializes_iff X x _ _).mp h1)
    refine lt_of_le_of_ne hle ?_
    intro hEq
    have hz : z i.castSucc = z i.succ := by
      rw [← hq i.castSucc, ← hq i.succ, hEq]
    exact absurd (hinj hz) Fin.castSucc_lt_succ.ne
  have hlen : ((n : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x) :=
    le_iSup (fun t : LTSeries (PrimeSpectrum (X.presheaf.stalk x)) => (t.length : WithBot ℕ∞))
      ⟨n, q, hstep⟩
  have hcast : ((n : ℕ∞) : WithBot ℕ∞) = ((n : ℕ) : WithBot ℕ∞) := by norm_cast
  rw [hcast]
  exact hlen

/- English proof (authored)
Under the identification with the polynomial spectrum, the closed point corresponds to a maximal ideal. The polynomial prime-chain result gives a chain of length m ending at that ideal. Transporting this chain to affine space gives distinct points ordered by specialization, all specializing to x. The stalk chain criterion therefore gives dimension at least m.
-/
private theorem le_ringKrullDim_stalk_affineSpace (k : Type u) [Field k] (m : ℕ)
    (x : ↥(AffineSpace (ULift.{u} (Fin m)) (Spec (CommRingCat.of k))))
    (hx : IsClosed ({x} : Set ↥(AffineSpace (ULift.{u} (Fin m)) (Spec (CommRingCat.of k))))) :
    ((m : ℕ∞) : WithBot ℕ∞) ≤
      ringKrullDim
        ((AffineSpace (ULift.{u} (Fin m)) (Spec (CommRingCat.of k))).presheaf.stalk x) := by
  let e : ↥(AffineSpace (ULift.{u} (Fin m)) (Spec (CommRingCat.of k))) ≃ₜ
      PrimeSpectrum (MvPolynomial (ULift.{u} (Fin m)) k) :=
    Scheme.homeoOfIso (AffineSpace.SpecIso (ULift.{u} (Fin m)) (CommRingCat.of k))
  have hclosed : IsClosed ({e x} : Set (PrimeSpectrum (MvPolynomial (ULift.{u} (Fin m)) k))) := by
    have h2 := e.isClosedMap _ hx
    rwa [Set.image_singleton] at h2
  have hmax : (e x).asIdeal.IsMaximal :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal (e x)).mp hclosed
  obtain ⟨s, hslen, hslast⟩ := exists_ltSeries_of_isMaximal_mvPolynomial_uLift k m (e x).asIdeal
    hmax
  have hlast : s.last = e x := PrimeSpectrum.ext hslast
  have hspec : ∀ i, (fun j => e.symm (s j)) i ⤳ x := by
    intro i
    have h1 : s i ≤ s.last := s.strictMono.monotone (Fin.le_last i)
    have h2 : (s i) ⤳ s.last := (PrimeSpectrum.le_iff_specializes _ _).mp h1
    have h3 := h2.map e.symm.continuous
    rw [hlast, e.symm_apply_apply] at h3
    exact h3
  have hmono : ∀ i j, i < j → (fun l => e.symm (s l)) i ⤳ (fun l => e.symm (s l)) j := by
    intro i j hij
    have h1 : s i < s j := s.strictMono hij
    exact ((PrimeSpectrum.le_iff_specializes _ _).mp h1.le).map e.symm.continuous
  have hinj : Function.Injective (fun i => e.symm (s i)) := by
    intro i j hij
    exact s.strictMono.injective (e.symm.injective hij)
  have key := le_ringKrullDim_stalk_of_chain
    (AffineSpace (ULift.{u} (Fin m)) (Spec (CommRingCat.of k))) x s.length
    (fun i => e.symm (s i)) hspec hmono hinj
  rw [hslen] at key
  exact key

/- English proof (authored)
The dimension of the stalk at y is at most m by the affine-space bound. An étale map to affine space over a field takes a closed point to a closed point by the closed-point result. Thus the target stalk at the image of y has dimension at least m by the prime-chain construction. Its dimension equals the source stalk dimension by the étale comparison, giving equality.
-/
theorem ringKrullDim_stalk_eq_of_etale_affineSpace {k : Type u} [Field k] {m : ℕ} {Y : Scheme.{u}}
    (c : Y ⟶ AffineSpace (ULift.{u} (Fin m)) (Spec (CommRingCat.of k)))
    [AlgebraicGeometry.Etale c] (y : Y) [IsNoetherianRing (Y.presheaf.stalk y)]
    (hy : IsClosed ({y} : Set Y)) :
    ringKrullDim (Y.presheaf.stalk y) = ((m : ℕ∞) : WithBot ℕ∞) := by
  have hreg : _root_.IsRegularLocalRing
      ((AffineSpace (ULift.{u} (Fin m)) (Spec (CommRingCat.of k))).presheaf.stalk (c.base y)) :=
    isRegularLocalRing_stalk_affineSpace k (ULift.{u} (Fin m)) (c.base y)
  refine le_antisymm (ringKrullDim_stalk_le_of_etale_affineSpace c y) ?_
  have heq := ringKrullDim_stalk_eq_of_etale c y
  rw [heq]
  exact le_ringKrullDim_stalk_affineSpace k m (c.base y)
    (AlgebraicGeometry.Scheme.Hom.closePoints_subset_preimage_closedPoints c hy)

end FunctorialResolution.EmbeddedResolution
