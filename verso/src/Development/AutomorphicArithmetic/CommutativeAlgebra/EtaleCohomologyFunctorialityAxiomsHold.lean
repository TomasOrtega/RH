import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocallyIffAffineEtalePointCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafSectionsExactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchClsCocycleSecStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictlyHenselianIff
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace UpperTheory.Cb.SHAcyc

/- English proof (translation)
The claim follows from `congrArg (fun h => h.hom x) (φ.hom.naturality g.op)`.
-/
private theorem map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U)
    (x : Sec F U) : Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) :=
  congrArg (fun h => h.hom x) (φ.hom.naturality g.op)

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(F.obj.map (k ≫ g).op).hom x = _`. Rewrite using `[op_comp, Functor.map_comp]`. Both sides reduce to the same expression.
-/
private theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U)
    (x : Sec F U) : Sec.res (k ≫ g) x = Sec.res k (Sec.res g x) := by
  change (F.obj.map (k ≫ g).op).hom x = _
  rw [op_comp, Functor.map_comp]
  rfl

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(F.obj.map (𝟙 U).op).hom x = x`. Rewrite using `[op_id, CategoryTheory.Functor.map_id]`. Both sides reduce to the same expression.
-/
private theorem res_id {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (x : Sec F U) :
    Sec.res (𝟙 U) x = x := by
  change (F.obj.map (𝟙 U).op).hom x = x
  rw [op_id, CategoryTheory.Functor.map_id]
  rfl

/- English proof (translation)
Set `φ : CommRingCat.of A ⟶ Γ(V, ⊤)` to `Spec.preimage (V.isoSpec.inv ≫ g)`. Establish `hφ : Spec.map φ = V.isoSpec.inv ≫ g` using `Spec.map_preimage _`. Establish `hE : Etale (Spec.map φ)` using `by rw [hφ]; infer_instance`. Use `letI : Algebra A Γ(V, ⊤) := φ.hom.toAlgebra`. Use `haveI : Algebra.Etale A Γ(V, ⊤) := RingHom.etale_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @Etale)).1 hE)`.

Set `y : Spec Γ(V, ⊤)` to `V.isoSpec.hom v`. Establish `hy : Spec.map φ y = (IsLocalRing.closedPoint A : PrimeSpectrum A)`. Rewrite using `[hφ, Scheme.Hom.comp_apply, ← hv]`. Use `congr 1`. Express the relevant statement in the definitionally equal form `(V.isoSpec.hom ≫ V.isoSpec.inv) v = v`.

Simplify using the standard rewrite rules. Establish `hq : (PrimeSpectrum.asIdeal y).comap (algebraMap A Γ(V, ⊤)) = IsLocalRing.maximalIdeal A` using `congrArg PrimeSpectrum.asIdeal hy`. Use `haveI : (PrimeSpectrum.asIdeal y).IsPrime := PrimeSpectrum.isPrime y`. Take `⟨s, -⟩` from `(GlobalTheory.StrictHensel.strictlyHenselian_iff A).2 ⟨inferInstance, inferInstance⟩ Γ(V, ⊤) (PrimeSpectrum.asIdeal y) hq`. Use `⟨Spec.map (CommRingCat.ofHom s.toRingHom) ≫ V.isoSpec.inv, ?_⟩` and prove the remaining obligations.

Rewrite using `[Category.assoc, ← hφ, ← Spec.map_comp]`. Establish `: φ ≫ CommRingCat.ofHom s.toRingHom = 𝟙 _`. Use extensionality with `a`. Conclude with `s.commutes a`. Rewrite using `[this, Spec.map_id]`.
-/
private theorem exists_section (A : Type) [CommRing A] [HenselianLocalRing A]
    [IsSepClosed (IsLocalRing.ResidueField A)] {V : Scheme.{0}} [IsAffine V]
    (g : V ⟶ Spec (CommRingCat.of A)) [Etale g] (v : V)
    (hv : g v = (IsLocalRing.closedPoint A : PrimeSpectrum A)) :
    ∃ σ : Spec (CommRingCat.of A) ⟶ V, σ ≫ g = 𝟙 _ := by
  let φ : CommRingCat.of A ⟶ Γ(V, ⊤) := Spec.preimage (V.isoSpec.inv ≫ g)
  have hφ : Spec.map φ = V.isoSpec.inv ≫ g := Spec.map_preimage _
  have hE : Etale (Spec.map φ) := by rw [hφ]; infer_instance
  letI : Algebra A Γ(V, ⊤) := φ.hom.toAlgebra
  haveI : Algebra.Etale A Γ(V, ⊤) :=
    RingHom.etale_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @Etale)).1 hE)
  let y : Spec Γ(V, ⊤) := V.isoSpec.hom v
  have hy : Spec.map φ y = (IsLocalRing.closedPoint A : PrimeSpectrum A) := by
    rw [hφ, Scheme.Hom.comp_apply, ← hv]
    congr 1
    change (V.isoSpec.hom ≫ V.isoSpec.inv) v = v
    simp
  have hq : (PrimeSpectrum.asIdeal y).comap (algebraMap A Γ(V, ⊤)) = IsLocalRing.maximalIdeal A :=
    congrArg PrimeSpectrum.asIdeal hy
  haveI : (PrimeSpectrum.asIdeal y).IsPrime := PrimeSpectrum.isPrime y
  obtain ⟨s, -⟩ := (GlobalTheory.StrictHensel.strictlyHenselian_iff A).2 ⟨inferInstance, inferInstance⟩
    Γ(V, ⊤) (PrimeSpectrum.asIdeal y) hq
  refine ⟨Spec.map (CommRingCat.ofHom s.toRingHom) ≫ V.isoSpec.inv, ?_⟩
  rw [Category.assoc, ← hφ, ← Spec.map_comp]
  have : φ ≫ CommRingCat.ofHom s.toRingHom = 𝟙 _ := by
    ext a
    exact s.commutes a
  rw [this, Spec.map_id]

end UpperTheory.Cb.SHAcyc

open UpperTheory.Cb.SHAcyc in

/- English proof (translation)
Introduce `R _ A _ hA F n hn`. Take `⟨hH, hS⟩` from `hA`. Use `haveI := hH`. It suffices to establish `h : ∀ x : H R (sp A) F n, x = 0 from ⟨fun a b => by rw [h a, h b]⟩`. Introduce `x`.

Take `⟨α, rfl⟩` from `x.mk_surjective`. Establish `hz` using `(GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff R (Spec (CommRingCat.of A)) (res R F) (n - 1) n (n + 1) (by ring) rfl).2 α`. Establish `hloc` using `(GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness R F (Spec (CommRingCat.of A))).2.2.1 (n - 1) n (n + 1) hn (by ring) _ rfl hz.1`. Establish `hpts` using `(GlobalTheory.T.etaleLocally_iff_affine_etale_point_cover (Spec (CommRingCat.of A)) _ (by`. Introduce and unpack `V W g k ⟨y, hy⟩`.

Use `⟨Sec.res k y, ?_⟩` and prove the remaining obligations. Rewrite using `[map_res, hy, res_comp])).1 hloc`. Take `⟨V, g, hV, hg, ⟨v, hv⟩, y, hy⟩` from `hpts (IsLocalRing.closedPoint A : PrimeSpectrum A)`. Take `⟨σ, hσ⟩` from `exists_section A g v hv`. Use `hz.2.2 ⟨Sec.res σ y, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_res, hy, ← res_comp, hσ, res_id]`.
-/
theorem UpperTheory.etaleCohomology_functorialityAxioms_hold : GlobalTheory.EtC.B2 := by
  intro R _ A _ hA F n hn
  obtain ⟨hH, hS⟩ := hA
  haveI := hH
  suffices h : ∀ x : H R (sp A) F n, x = 0 from ⟨fun a b => by rw [h a, h b]⟩
  intro x
  obtain ⟨α, rfl⟩ := x.mk_surjective
  have hz := (GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff R (Spec (CommRingCat.of A)) (res R F) (n - 1) n (n + 1) (by ring) rfl).2 α
  have hloc := (GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness R F (Spec (CommRingCat.of A))).2.2.1 (n - 1) n (n + 1) hn (by ring) _ rfl hz.1
  have hpts := (GlobalTheory.T.etaleLocally_iff_affine_etale_point_cover (Spec (CommRingCat.of A)) _ (by
    rintro V W g k ⟨y, hy⟩
    refine ⟨Sec.res k y, ?_⟩
    rw [map_res, hy, res_comp])).1 hloc
  obtain ⟨V, g, hV, hg, ⟨v, hv⟩, y, hy⟩ := hpts (IsLocalRing.closedPoint A : PrimeSpectrum A)
  obtain ⟨σ, hσ⟩ := exists_section A g v hv
  refine hz.2.2 ⟨Sec.res σ y, ?_⟩
  rw [map_res, hy, ← res_comp, hσ, res_id]
