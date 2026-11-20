import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowIdeal

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

namespace GlobalTheory.CompanionTheory.GE

namespace KrullPts

/- English proof (translation)
Establish `hcl : IsClosed (q '' closure {y₀})` using `hq _ isClosed_closure`. Establish `hmem : q y₀ ∈ q '' closure {y₀}` using `⟨y₀, subset_closure rfl, rfl⟩`. Take `⟨y₁, hy₁, rfl⟩` from `h.mem_closed hcl hmem`. Conclude with `⟨y₁, specializes_iff_mem_closure.mpr hy₁, rfl⟩`.
-/
theorem exists_specialization_over {W S : Type*} [TopologicalSpace W] [TopologicalSpace S]
    {q : W → S} (hq : IsClosedMap q) {y₀ : W} {m : S} (h : q y₀ ⤳ m) :
    ∃ y₁, y₀ ⤳ y₁ ∧ q y₁ = m := by
  have hcl : IsClosed (q '' closure {y₀}) := hq _ isClosed_closure
  have hmem : q y₀ ∈ q '' closure {y₀} := ⟨y₀, subset_closure rfl, rfl⟩
  obtain ⟨y₁, hy₁, rfl⟩ := h.mem_closed hcl hmem
  exact ⟨y₁, specializes_iff_mem_closure.mpr hy₁, rfl⟩

/- English proof (translation)
Use `letI : Algebra Γ(X, V) Γ(Z, U) := (φ.appLE V U h).hom.toAlgebra`. Establish `e : Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) Γ(Z, U))) ≫ hV.fromSpec = hU.fromSpec ≫ φ` using `IsAffineOpen.SpecMap_appLE_fromSpec φ hV hU h`. Establish `key : ((a ⁻¹ᵁ U).ι ≫ q) ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) R)) = ((a ∣_ U) ≫ hU.isoSpec.hom) ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) Γ(Z, U)))`. Rewrite using `[← cancel_mono hV.fromSpec]`. Simplify using `only [Category.assoc, e]`.

Rewrite using `[← hc, ← hU.isoSpec_inv_ι]`. Simplify using `only [Category.assoc, Iso.hom_inv_id_assoc, morphismRestrict_ι_assoc]`. Conclude with `⟨pullback.lift _ _ key ≫ (pullbackSpecIso _ _ _).hom, by`. Rewrite using `[Category.assoc, pullbackSpecIso_hom_fst, pullback.lift_fst]⟩`.
-/
theorem exists_chart_map {X Z W : Scheme.{0}} (φ : Z ⟶ X) (V : X.Opens) (hV : IsAffineOpen V)
    {R : Type} [CommRing R] [Algebra Γ(X, V) R] (a : W ⟶ Z) (q : W ⟶ Spec (.of R))
    (hc : a ≫ φ = q ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) R)) ≫ hV.fromSpec)
    (U : Z.Opens) (hU : IsAffineOpen U) (h : U ≤ φ ⁻¹ᵁ V) :
    letI : Algebra Γ(X, V) Γ(Z, U) := (φ.appLE V U h).hom.toAlgebra
    ∃ l : (a ⁻¹ᵁ U).toScheme ⟶ Spec (.of (R ⊗[Γ(X, V)] Γ(Z, U))),
      l ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[Γ(X, V)] Γ(Z, U))) =
        (a ⁻¹ᵁ U).ι ≫ q := by
  letI : Algebra Γ(X, V) Γ(Z, U) := (φ.appLE V U h).hom.toAlgebra
  have e : Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) Γ(Z, U))) ≫ hV.fromSpec =
      hU.fromSpec ≫ φ := IsAffineOpen.SpecMap_appLE_fromSpec φ hV hU h
  have key : ((a ⁻¹ᵁ U).ι ≫ q) ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) R)) =
      ((a ∣_ U) ≫ hU.isoSpec.hom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) Γ(Z, U))) := by
    rw [← cancel_mono hV.fromSpec]
    simp only [Category.assoc, e]
    rw [← hc, ← hU.isoSpec_inv_ι]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, morphismRestrict_ι_assoc]
  exact ⟨pullback.lift _ _ key ≫ (pullbackSpecIso _ _ _).hom, by
    rw [Category.assoc, pullbackSpecIso_hom_fst, pullback.lift_fst]⟩

/- English proof (translation)
Take `⟨z₀, hz₀⟩` from `hz`. Set `g : Spec (.of R) ⟶ X` to `Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) R)) ≫ hV.fromSpec`. Set `a` to `pullback.fst φ g`. Set `q` to `pullback.snd φ g`. Establish `hc : a ≫ φ = q ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) R)) ≫ hV.fromSpec` using `pullback.condition`.

Take `⟨y₀, -, hq₀⟩` from `Scheme.Pullback.exists_preimage_pullback (f := φ) (g := g) z₀ (⟨p, hp⟩ : PrimeSpectrum R) hz₀`. Take `⟨m, hm, hpm⟩` from `Ideal.exists_le_maximal p hp.ne_top`. Establish `hspec : q y₀ ⤳ (⟨m, hm.isPrime⟩ : PrimeSpectrum R)`. Express the relevant statement in the definitionally equal form `pullback.snd φ g y₀ ⤳ _`. Rewrite using `[hq₀]`.

Conclude with `(PrimeSpectrum.le_iff_specializes _ _).mp hpm`. Take `⟨y₁, hsp, hq₁⟩` from `exists_specialization_over q.isClosedMap hspec`. Establish `hy₁ : a y₁ ∈ φ ⁻¹ᵁ V`. Establish `e : φ (a y₁) = hV.fromSpec (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) R)) (q y₁))`. Use `congr($hc y₁)` as an intermediate fact.

Simplify using `using this`. Express the relevant statement in the definitionally equal form `φ (a y₁) ∈ V`. Rewrite using `[e]`. Conclude with `hV.range_fromSpec.subset ⟨_, rfl⟩`. Take `⟨U', hU', hmem, hle⟩` from `TopologicalSpace.Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens hy₁`.

Establish `hU : IsAffineOpen U'` using `hU'`. Use `⟨U', hU, hle, ?_⟩` and prove the remaining obligations. Use `letI : Algebra Γ(X, V) Γ(Z, U') := (φ.appLE V U' hle).hom.toAlgebra`. Take `⟨l, hl⟩` from `exists_chart_map φ V hV a q hc U' hU hle`. Establish `hT₁ : y₁ ∈ a ⁻¹ᵁ U'` using `hmem`.

Establish `hT₀ : y₀ ∈ a ⁻¹ᵁ U'` using `hsp.mem_open (a ⁻¹ᵁ U').isOpen hT₁`. Set `t₀ : (a ⁻¹ᵁ U').toScheme` to `⟨y₀, hT₀⟩`. Set `t₁ : (a ⁻¹ᵁ U').toScheme` to `⟨y₁, hT₁⟩`. Establish `ht : t₀ ⤳ t₁` using `Topology.IsInducing.subtypeVal.specializes_iff.mp hsp`. Establish `hcomp : ∀ t : (a ⁻¹ᵁ U').toScheme, Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) (l t) = q t.1` using `fun t => congr($hl t)`.

Set `P₀ : PrimeSpectrum (R ⊗[Γ(X, V)] Γ(Z, U'))` to `l t₀`. Set `P₁ : PrimeSpectrum (R ⊗[Γ(X, V)] Γ(Z, U'))` to `l t₁`. Use `⟨P₀.asIdeal, P₁.asIdeal, P₀.isPrime, P₁.isPrime, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(PrimeSpectrum.le_iff_specializes P₀ P₁).mpr (ht.map l.continuous)`. Conclude with `congrArg PrimeSpectrum.asIdeal ((hcomp t₀).trans hq₀)`.

Establish `e : P₁.asIdeal.comap (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[Γ(X, V)] Γ(Z, U')) = m` using `congrArg PrimeSpectrum.asIdeal ((hcomp t₁).trans hq₁)`. Rewrite using `[e]`. Conclude with `hm`.
-/
theorem exists_chart_primes {X Z : Scheme.{0}} (φ : Z ⟶ X) [IsProper φ] (V : X.Opens)
    (hV : IsAffineOpen V) {R : Type} [CommRing R] [Algebra Γ(X, V) R] (p : Ideal R) (hp : p.IsPrime)
    (hz : ∃ z : Z, φ z = hV.fromSpec (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) R))
      (⟨p, hp⟩ : PrimeSpectrum R))) :
    ∃ (U : Z.Opens) (_ : IsAffineOpen U) (h : U ≤ φ ⁻¹ᵁ V),
      letI : Algebra Γ(X, V) Γ(Z, U) := (φ.appLE V U h).hom.toAlgebra
      ∃ Q₀ Q₁ : Ideal (R ⊗[Γ(X, V)] Γ(Z, U)), Q₀.IsPrime ∧ Q₁.IsPrime ∧ Q₀ ≤ Q₁ ∧
        Q₀.comap (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[Γ(X, V)] Γ(Z, U)) = p ∧
        (Q₁.comap (Algebra.TensorProduct.includeLeftRingHom :
          R →+* R ⊗[Γ(X, V)] Γ(Z, U))).IsMaximal := by
  obtain ⟨z₀, hz₀⟩ := hz
  let g : Spec (.of R) ⟶ X := Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) R)) ≫ hV.fromSpec
  let a := pullback.fst φ g
  let q := pullback.snd φ g
  have hc : a ≫ φ = q ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) R)) ≫ hV.fromSpec :=
    pullback.condition
  obtain ⟨y₀, -, hq₀⟩ := Scheme.Pullback.exists_preimage_pullback (f := φ) (g := g) z₀
    (⟨p, hp⟩ : PrimeSpectrum R) hz₀
  obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p hp.ne_top
  have hspec : q y₀ ⤳ (⟨m, hm.isPrime⟩ : PrimeSpectrum R) := by
    change pullback.snd φ g y₀ ⤳ _
    rw [hq₀]
    exact (PrimeSpectrum.le_iff_specializes _ _).mp hpm
  obtain ⟨y₁, hsp, hq₁⟩ := exists_specialization_over q.isClosedMap hspec
  have hy₁ : a y₁ ∈ φ ⁻¹ᵁ V := by
    have e : φ (a y₁) = hV.fromSpec (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) R)) (q y₁)) := by
      have := congr($hc y₁)
      simpa using this
    change φ (a y₁) ∈ V
    rw [e]
    exact hV.range_fromSpec.subset ⟨_, rfl⟩
  obtain ⟨U', hU', hmem, hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens hy₁
  have hU : IsAffineOpen U' := hU'
  refine ⟨U', hU, hle, ?_⟩
  letI : Algebra Γ(X, V) Γ(Z, U') := (φ.appLE V U' hle).hom.toAlgebra
  obtain ⟨l, hl⟩ := exists_chart_map φ V hV a q hc U' hU hle
  have hT₁ : y₁ ∈ a ⁻¹ᵁ U' := hmem
  have hT₀ : y₀ ∈ a ⁻¹ᵁ U' := hsp.mem_open (a ⁻¹ᵁ U').isOpen hT₁
  let t₀ : (a ⁻¹ᵁ U').toScheme := ⟨y₀, hT₀⟩
  let t₁ : (a ⁻¹ᵁ U').toScheme := ⟨y₁, hT₁⟩
  have ht : t₀ ⤳ t₁ := Topology.IsInducing.subtypeVal.specializes_iff.mp hsp
  have hcomp : ∀ t : (a ⁻¹ᵁ U').toScheme, Spec.map (CommRingCat.ofHom
      Algebra.TensorProduct.includeLeftRingHom) (l t) = q t.1 := fun t => congr($hl t)
  let P₀ : PrimeSpectrum (R ⊗[Γ(X, V)] Γ(Z, U')) := l t₀
  let P₁ : PrimeSpectrum (R ⊗[Γ(X, V)] Γ(Z, U')) := l t₁
  refine ⟨P₀.asIdeal, P₁.asIdeal, P₀.isPrime, P₁.isPrime, ?_, ?_, ?_⟩
  · exact (PrimeSpectrum.le_iff_specializes P₀ P₁).mpr (ht.map l.continuous)
  · exact congrArg PrimeSpectrum.asIdeal ((hcomp t₀).trans hq₀)
  · have e : P₁.asIdeal.comap
        (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[Γ(X, V)] Γ(Z, U')) = m :=
      congrArg PrimeSpectrum.asIdeal ((hcomp t₁).trans hq₁)
    rw [e]
    exact hm

end KrullPts

/- English proof (translation)
Introduce `X J Z ψ hψ V hV R _ _ f hiso p hp hJ hf`. Use `haveI := hψ`. Use `KrullPts.exists_chart_primes (ψ ≫ J.subschemeι) V hV p hp ?_` and prove the remaining obligations. Set `P : PrimeSpectrum Γ(X, V)` to `Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) R)) (⟨p, hp⟩ : PrimeSpectrum R)`. Express the relevant statement in the definitionally equal form `∃ z : Z, (ψ ≫ J.subschemeι) z = hV.fromSpec P`.

Establish `hxf : hV.fromSpec P ∈ X.basicOpen f`. Establish `h1 : P ∈ hV.fromSpec ⁻¹ᵁ X.basicOpen f`. Rewrite using `[hV.fromSpec_preimage_basicOpen]`. Conclude with `hf`. Conclude with `h1`.

Establish `hxV : hV.fromSpec P ∈ (V : Set X)` using `hV.range_fromSpec.subset ⟨_, rfl⟩`. Establish `hxs : hV.fromSpec P ∈ (J.support : Set X)`. Establish `h1 : hV.fromSpec P ∈ (J.support : Set X) ∩ (V : Set X)`. Establish `e` using `J.coe_support_inter ⟨V, hV⟩`. Use `e.symm.subset ⟨?_, hxV⟩` and prove the remaining obligations.

Rewrite using `[Scheme.mem_zeroLocus_iff]`. Introduce `b hb hbx`. Establish `h2 : P ∈ hV.fromSpec ⁻¹ᵁ X.basicOpen b` using `hbx`. Rewrite `h2` using `[hV.fromSpec_preimage_basicOpen]`. Conclude with `h2 (hJ (Ideal.mem_map_of_mem _ hb))`.

Conclude with `h1.1`. Take `⟨y, hy⟩` from `J.range_subschemeι.ge hxs`. Establish `hyD : y ∈ J.subschemeι ⁻¹ᵁ X.basicOpen f`. Express the relevant statement in the definitionally equal form `J.subschemeι y ∈ X.basicOpen f`. Rewrite using `[hy]`.

Conclude with `hxf`. Use `haveI := hiso`. Take `⟨w, hw⟩` from `(ψ ∣_ (J.subschemeι ⁻¹ᵁ X.basicOpen f)).surjective ⟨y, hyD⟩`. Establish `hψw : ψ w.1 = y` using `(morphismRestrict_base_coe ψ _ w).symm.trans (congrArg Subtype.val hw)`. Use `⟨w.1, ?_⟩` and prove the remaining obligations.

Rewrite using `[Scheme.Hom.comp_apply, hψw, hy]`.
-/
theorem exists_chart_primes_of_isProper : ∀ {X : Scheme.{0}} (J : X.IdealSheafData) {Z : Scheme.{0}} (ψ : Z ⟶ J.subscheme), IsProper ψ → ∀ (V : X.Opens) (hV : IsAffineOpen V) {R : Type} [CommRing R] [Algebra Γ(X, V) R] (f : Γ(X, V)), IsIso (ψ ∣_ (J.subschemeι ⁻¹ᵁ X.basicOpen f)) → ∀ p : Ideal R, p.IsPrime → (J.ideal ⟨V, hV⟩).map (algebraMap Γ(X, V) R) ≤ p → algebraMap Γ(X, V) R f ∉ p → ∃ (U : Z.Opens) (_ : IsAffineOpen U) (h : U ≤ (ψ ≫ J.subschemeι) ⁻¹ᵁ V), letI : Algebra Γ(X, V) Γ(Z, U) := ((ψ ≫ J.subschemeι).appLE V U h).hom.toAlgebra; ∃ Q₀ Q₁ : Ideal (R ⊗[Γ(X, V)] Γ(Z, U)), Q₀.IsPrime ∧ Q₁.IsPrime ∧ Q₀ ≤ Q₁ ∧ Q₀.comap (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[Γ(X, V)] Γ(Z, U)) = p ∧ (Q₁.comap (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[Γ(X, V)] Γ(Z, U))).IsMaximal := by
  intro X J Z ψ hψ V hV R _ _ f hiso p hp hJ hf
  haveI := hψ
  refine KrullPts.exists_chart_primes (ψ ≫ J.subschemeι) V hV p hp ?_
  let P : PrimeSpectrum Γ(X, V) :=
    Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) R)) (⟨p, hp⟩ : PrimeSpectrum R)
  change ∃ z : Z, (ψ ≫ J.subschemeι) z = hV.fromSpec P
  have hxf : hV.fromSpec P ∈ X.basicOpen f := by
    have h1 : P ∈ hV.fromSpec ⁻¹ᵁ X.basicOpen f := by
      rw [hV.fromSpec_preimage_basicOpen]
      exact hf
    exact h1
  have hxV : hV.fromSpec P ∈ (V : Set X) := hV.range_fromSpec.subset ⟨_, rfl⟩
  have hxs : hV.fromSpec P ∈ (J.support : Set X) := by
    have h1 : hV.fromSpec P ∈ (J.support : Set X) ∩ (V : Set X) := by
      have e := J.coe_support_inter ⟨V, hV⟩
      refine e.symm.subset ⟨?_, hxV⟩
      rw [Scheme.mem_zeroLocus_iff]
      intro b hb hbx
      have h2 : P ∈ hV.fromSpec ⁻¹ᵁ X.basicOpen b := hbx
      rw [hV.fromSpec_preimage_basicOpen] at h2
      exact h2 (hJ (Ideal.mem_map_of_mem _ hb))
    exact h1.1
  obtain ⟨y, hy⟩ := J.range_subschemeι.ge hxs
  have hyD : y ∈ J.subschemeι ⁻¹ᵁ X.basicOpen f := by
    change J.subschemeι y ∈ X.basicOpen f
    rw [hy]
    exact hxf
  haveI := hiso
  obtain ⟨w, hw⟩ := (ψ ∣_ (J.subschemeι ⁻¹ᵁ X.basicOpen f)).surjective ⟨y, hyD⟩
  have hψw : ψ w.1 = y :=
    (morphismRestrict_base_coe ψ _ w).symm.trans (congrArg Subtype.val hw)
  refine ⟨w.1, ?_⟩
  rw [Scheme.Hom.comp_apply, hψw, hy]

end GlobalTheory.CompanionTheory.GE
