import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueSectionOfDense
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenWeilIsIff
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.CharZeroPts

/- English proof (translation)
Set `ξ : Sp o` to `(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum o)`. Establish `hξ : ξ ⤳ s p` using `(PrimeSpectrum.le_iff_specializes _ _).1 bot_le`. Take `⟨q, hq, hq'⟩` from `Flat.generalizingMap s hξ`. Take `⟨K, _, _, x, hx⟩` from `FinEt.exists_algClosed_point S q`. Establish `hx' : ∀ u, x u = q` using `fun u => by`.

Establish `: x u ∈ Set.range x` using `⟨u, rfl⟩`. Rewrite `this` using `[hx]`. Then use the resulting hypothesis. Set `β : o →+* K` to `(Spec.preimage (x ≫ s)).hom`. Establish `hβ : x ≫ s = spMap β` using `(Spec.map_preimage (x ≫ s)).symm`. Establish `hinj : Function.Injective β`.

Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`. Establish `e : spMap β (default : PrimeSpectrum K) = ξ`. Rewrite using `[← hβ]`. Conclude with `(Scheme.Hom.comp_apply _ _ _).trans ((congrArg s (hx' _)).trans hq')`.

Establish `e' : a ∈ (spMap β (default : PrimeSpectrum K)).asIdeal` using `by show β a ∈ (default : PrimeSpectrum K).asIdeal`. Rewrite using `[ha]`. Conclude with `zero_mem _`. Rewrite `e'` using `[e]`. Conclude with `e'`.

Conclude with `⟨K, inferInstance, inferInstance, charZero_of_injective_ringHom hinj, x, β, hβ, fun u => (hx' u).symm ▸ hq⟩`.
-/
theorem exists_generization {o : Type} [CommRing o] [IsDomain o] [CharZero o] {S : Scheme.{0}} (s : S ⟶ Sp o) [Flat s]
    (p : S) : ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (_ : CharZero K) (x : Sp K ⟶ S) (β : o →+* K),
      x ≫ s = spMap β ∧ ∀ u, x u ⤳ p := by
  let ξ : Sp o := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum o)
  have hξ : ξ ⤳ s p := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
  obtain ⟨q, hq, hq'⟩ := Flat.generalizingMap s hξ
  obtain ⟨K, _, _, x, hx⟩ := FinEt.exists_algClosed_point S q
  have hx' : ∀ u, x u = q := fun u => by
    have : x u ∈ Set.range x := ⟨u, rfl⟩
    rwa [hx] at this
  let β : o →+* K := (Spec.preimage (x ≫ s)).hom
  have hβ : x ≫ s = spMap β := (Spec.map_preimage (x ≫ s)).symm
  have hinj : Function.Injective β := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have e : spMap β (default : PrimeSpectrum K) = ξ := by
      rw [← hβ]
      exact (Scheme.Hom.comp_apply _ _ _).trans ((congrArg s (hx' _)).trans hq')
    have e' : a ∈ (spMap β (default : PrimeSpectrum K)).asIdeal := by
      show β a ∈ (default : PrimeSpectrum K).asIdeal
      rw [ha]; exact zero_mem _
    rw [e] at e'
    exact e'
  exact ⟨K, inferInstance, inferInstance, charZero_of_injective_ringHom hinj, x, β, hβ, fun u => (hx' u).symm ▸ hq⟩

variable {S : Scheme.{0}}

abbrev toB {T : Scheme.{0}} (x : T ⟶ S) : Over.mk x ⟶ Out.baseOver S := Over.homMk x (by simp)

/- English proof (translation)
Use `choose n W hW hd using H1.exists_dim f`. Establish `: IsZariskiLocalAtSource (@SmoothOfRelativeDimension g)` using `HasRingHomProperty.instIsZariskiLocalAtSource`. Use `IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension g) W (top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hW y⟩) fun y => ?_` and prove the remaining obligations. Take `⟨k, _, z, hz, hg⟩` from `h y`. Establish `: ConnectedSpace ↥(pullback f (z ≫ f))` using `GeometricallyConnected.geometrically_connectedSpace (f := f) (z ≫ f) _ _ (IsPullback.of_hasPullback _ _)`.

Set `z' : Sp k ⟶ pullback f (z ≫ f)` to `pullback.lift z (𝟙 _) (Category.id_comp _).symm`. Take `⟨m, hm⟩` from `exists_dim_of_preconnected (pullback.snd f (z ≫ f)) (z' (default : PrimeSpectrum k))`. Establish `e₁ : n y = m` using `H1.dim_base (IsPullback.of_hasPullback _ _) (hd y) hm (z' (default : PrimeSpectrum k)) (by`. Establish `e : z' ≫ pullback.fst f (z ≫ f) = z` using `pullback.lift_fst _ _ _`. Establish `e'` using `congrArg (fun q : Sp k ⟶ X => q (default : PrimeSpectrum k)) e`.

Conclude with `(congrArg (fun u => u ∈ W y) e').mpr ((hz _).mem_open (W y).isOpen (hW y)))`. Rewrite using `[← hg m hm, ← e₁]`. Conclude with `hd y`.
-/
theorem smoothOfRelativeDimension_of_generization {X : Scheme.{0}} (f : X ⟶ S) [Smooth f] [GeometricallyConnected f]
    (g : ℕ) (h : ∀ y : X, ∃ (K : Type) (_ : Field K) (z : Sp K ⟶ X), (∀ u, z u ⤳ y) ∧
      ∀ m, SmoothOfRelativeDimension m (pullback.snd f (z ≫ f)) → m = g) : SmoothOfRelativeDimension g f := by
  choose n W hW hd using H1.exists_dim f
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension g) := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension g) W
    (top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hW y⟩) fun y => ?_
  obtain ⟨k, _, z, hz, hg⟩ := h y
  have : ConnectedSpace ↥(pullback f (z ≫ f)) :=
    GeometricallyConnected.geometrically_connectedSpace (f := f) (z ≫ f) _ _ (IsPullback.of_hasPullback _ _)
  let z' : Sp k ⟶ pullback f (z ≫ f) := pullback.lift z (𝟙 _) (Category.id_comp _).symm
  obtain ⟨m, hm⟩ := exists_dim_of_preconnected (pullback.snd f (z ≫ f)) (z' (default : PrimeSpectrum k))
  have e₁ : n y = m := H1.dim_base (IsPullback.of_hasPullback _ _) (hd y) hm (z' (default : PrimeSpectrum k)) (by
    have e : z' ≫ pullback.fst f (z ≫ f) = z := pullback.lift_fst _ _ _
    have e' := congrArg (fun q : Sp k ⟶ X => q (default : PrimeSpectrum k)) e
    exact (congrArg (fun u => u ∈ W y) e').mpr ((hz _).mem_open (W y).isOpen (hW y)))
  rw [← hg m hm, ← e₁]
  exact hd y

/- English proof (translation)
Take `⟨U, hU, H⟩` from `exists_clopen_weilIs_iff hL S P n (Out.baseOver S) x y c hn hu hx hy hc`. Use `(H _ (𝟙 _)).2 (by` as an intermediate fact. Introduce and unpack `_ ⟨p, rfl⟩`. Take `⟨K, _, z, hz, hw⟩` from `h p`. Conclude with `(hz (default : PrimeSpectrum K)).mem_closed hU ((H _ (toB z)).1 hw ⟨_, rfl⟩))`.

Rewrite `this` using `[Category.id_comp, Category.id_comp]`. Use `this` and compare the differences between its conclusion and the goal. Use `ext`. Simplify using the standard rewrite rules.
-/
theorem weilIs_of_generization (hL : Out.Laws) (P : Out.PolAV S) (n : ℕ) (x y : Out.baseOver S ⟶ P.A) (c : Γ(S, ⊤)ˣ)
    (hn : 0 < n) (hu : IsUnit (n : Γ(S, ⊤))) (hx : x ^ n = 1) (hy : y ^ n = 1) (hc : c ^ n = 1)
    (h : ∀ p : S, ∃ (K : Type) (_ : Field K) (z : Sp K ⟶ S), (∀ u, z u ⤳ p) ∧
      Out.WeilIs P.A P.L n (toB z ≫ x) (toB z ≫ y) (Units.map z.appTop.hom.toMonoidHom c)) :
    Out.WeilIs P.A P.L n x y c := by
  obtain ⟨U, hU, H⟩ := exists_clopen_weilIs_iff hL S P n (Out.baseOver S) x y c hn hu hx hy hc
  have := (H _ (𝟙 _)).2 (by
    rintro _ ⟨p, rfl⟩
    obtain ⟨K, _, z, hz, hw⟩ := h p
    exact (hz (default : PrimeSpectrum K)).mem_closed hU ((H _ (toB z)).1 hw ⟨_, rfl⟩))
  rw [Category.id_comp, Category.id_comp] at this
  convert this
  ext
  simp

/- English proof (translation)
Use `torsion_basis_of_dense S A k r pt _ hA hk hu hpt ?_ (fun p hp => hp) K x y hy` and prove the remaining obligations. Introduce `p`. Take `⟨K, _, _, z, hz, H⟩` from `h p`. Conclude with `(hz (default : PrimeSpectrum K)).mem_closed isClosed_closure (subset_closure ⟨K, inferInstance, inferInstance, z, ⟨_, rfl⟩, H⟩)`.
-/
theorem torsion_basis_of_generization (A : Over S) [GrpObj A] (k r : ℕ) (pt : Fin r → (Out.baseOver S ⟶ A))
    (hA : IsAbelianScheme A) (hk : 0 < k) (hu : IsUnit (k : Γ(S, ⊤))) (hpt : ∀ i, pt i ^ k = 1)
    (h : ∀ p : S, ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (z : Sp K ⟶ S), (∀ u, z u ⤳ p) ∧
      ∀ y : Over.mk z ⟶ A, y ^ k = 1 →
        ∃! c : Fin r → ZMod k, Out.linComb (fun i => toB z ≫ pt i) (fun i => (c i).val) = y)
    (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (y : Over.mk x ⟶ A) (hy : y ^ k = 1) :
    ∃! c : Fin r → ZMod k, Out.linComb (fun i => toB x ≫ pt i) (fun i => (c i).val) = y := by
  refine torsion_basis_of_dense S A k r pt _ hA hk hu hpt ?_ (fun p hp => hp) K x y hy
  intro p
  obtain ⟨K, _, _, z, hz, H⟩ := h p
  exact (hz (default : PrimeSpectrum K)).mem_closed isClosed_closure
    (subset_closure ⟨K, inferInstance, inferInstance, z, ⟨_, rfl⟩, H⟩)

end GlobalTheory.CharZeroPts
