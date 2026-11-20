import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GagaLineGeneratorComplexStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProperModelGenericFibreCompareStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeBasisPullbackDominantStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GermStalkClosedPointToBaseChange
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapGermEqGenMapGerm
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsVBOneOfChartGenerators
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InjectiveOfIsCptGen
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AlgClosedTensorIsDomainStatement
open TensorProduct
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.GagaRat

variable {X X' : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω']

/- English proof (translation)
Establish `e` using `Scheme.Hom.stalkSpecializes_stalkMap g _ _ q.2`. Establish `e2` using `congrArg (fun t => (t ≫ Scheme.stalkClosedPointTo ξ).hom s) e`. Establish `e3` using `Scheme.stalkClosedPointTo_comp ξ g`. Establish `e4` using `congrArg (fun t => (X'.presheaf.stalkSpecializes h ≫ t).hom s) e3`. Conclude with `e2.symm.trans e4.symm`.
-/
theorem genMap_stalkMap' (ξ : Sp Ω ⟶ X) (g : X ⟶ X') (q : Cpt ξ)
    (h : genPt (ξ ≫ g) ⤳ g q.1) (s : X'.presheaf.stalk (g q.1)) :
    genMap ξ q ((g.stalkMap q.1).hom s) = genMap (ξ ≫ g) ⟨g q.1, h⟩ s := by
  have e := Scheme.Hom.stalkSpecializes_stalkMap g _ _ q.2
  have e2 := congrArg (fun t => (t ≫ Scheme.stalkClosedPointTo ξ).hom s) e
  have e3 := Scheme.stalkClosedPointTo_comp ξ g
  have e4 := congrArg (fun t => (X'.presheaf.stalkSpecializes h ≫ t).hom s) e3
  exact e2.symm.trans e4.symm

section Spec

variable {R F : Type} [CommRing R] [Field F]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hi b hb`. Establish `h0 : CptModel.tS p.1 b = 0` using `hi (by rw [CptModel.genMap_toStalk, hb, map_zero])`. Establish `key : ∀ (q : PrimeSpectrum R) (b : R), algebraMap R ((Spec.structureSheaf R).presheaf.stalk q) b = 0 → ∃ u, u ∉ q.asIdeal ∧ u * b = 0` using `fun q b h => by`. Take `⟨⟨u, hu⟩, h'⟩` from `(IsLocalization.map_eq_zero_iff q.asIdeal.primeCompl _ b).1 h`.

Conclude with `⟨u, hu, h'⟩`. Conclude with `key p.1 b h0`. Introduce `H`. Use `(injective_iff_map_eq_zero _).2 fun x hx => ?_` and prove the remaining obligations. Take `⟨a, s, hs, h⟩` from `CptModel.exists_frac e p x`.

Establish `h1 : e a = 0`. Rewrite using `[← CptModel.genMap_toStalk e p, ← h, map_mul, hx, zero_mul]`. Take `⟨u, hu, hua⟩` from `H a h1`. Establish `h2 : CptModel.tS p.1 a = 0`. Establish `: CptModel.tS p.1 u * CptModel.tS p.1 a = 0` using `by rw [← map_mul, hua, map_zero]`.

Conclude with `(CptModel.isUnit_toStalk p.1 hu).mul_right_eq_zero.1 this`. Rewrite `h` using `[h2]`. Conclude with `(CptModel.isUnit_toStalk p.1 hs).mul_left_eq_zero.1 h`.
-/
theorem inj_iff (e : R →+* F) (p : Cpt (CptModel.pt e)) :
    Function.Injective (genMap (CptModel.pt e) p) ↔ ∀ b, e b = 0 → ∃ u, u ∉ p.1.asIdeal ∧ u * b = 0 := by
  constructor
  · intro hi b hb
    have h0 : CptModel.tS p.1 b = 0 := hi (by rw [CptModel.genMap_toStalk, hb, map_zero])
    have key : ∀ (q : PrimeSpectrum R) (b : R), algebraMap R ((Spec.structureSheaf R).presheaf.stalk q) b = 0 →
        ∃ u, u ∉ q.asIdeal ∧ u * b = 0 := fun q b h => by
      obtain ⟨⟨u, hu⟩, h'⟩ := (IsLocalization.map_eq_zero_iff q.asIdeal.primeCompl _ b).1 h
      exact ⟨u, hu, h'⟩
    exact key p.1 b h0
  · intro H
    refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    obtain ⟨a, s, hs, h⟩ := CptModel.exists_frac e p x
    have h1 : e a = 0 := by
      rw [← CptModel.genMap_toStalk e p, ← h, map_mul, hx, zero_mul]
    obtain ⟨u, hu, hua⟩ := H a h1
    have h2 : CptModel.tS p.1 a = 0 := by
      have : CptModel.tS p.1 u * CptModel.tS p.1 a = 0 := by rw [← map_mul, hua, map_zero]
      exact (CptModel.isUnit_toStalk p.1 hu).mul_right_eq_zero.1 this
    rw [h2] at h
    exact (CptModel.isUnit_toStalk p.1 hs).mul_left_eq_zero.1 h

end Spec

section Tensor

variable {K A Ω C : Type} [Field K] [CommRing A] [Algebra K A] [CommRing C] [Algebra K C]

/- English proof (translation)
Establish `hex : Function.Exact (LinearMap.ker φ.toLinearMap).subtype φ.toLinearMap` using `LinearMap.exact_subtype_ker_map _`. Establish `hex'` using `Module.Flat.rTensor_exact C hex`. Take `⟨w, rfl⟩` from `(hex' b).1 hb`. Use `clear hb`. Proceed by induction on `w using TensorProduct.induction_on with`.

Consider the case `zero => exact ⟨1, S.one_mem, by simp⟩`. Consider the case `tmul a c`. Take `⟨d, hd, h⟩` from `H a.1 a.2`. Conclude with `⟨d, hd, by simp [h]⟩`. Consider the case `add x y hx hy`.

Take `⟨d₁, m₁, h₁⟩` from `hx`. Take `⟨d₂, m₂, h₂⟩` from `hy`. Use `⟨d₁ * d₂, S.mul_mem m₁ m₂, ?_⟩` and prove the remaining obligations. Establish `e : (d₁ * d₂) ⊗ₜ[K] (1 : C) = (d₁ ⊗ₜ[K] (1 : C)) * (d₂ ⊗ₜ[K] (1 : C))` using `by simp`. Rewrite using `[map_add, e]`.

Take the linear combination `(d₂ ⊗ₜ[K] (1 : C)) * h₁ + (d₁ ⊗ₜ[K] (1 : C)) * h₂`.
-/
theorem tensor_ker [CommRing Ω] [Algebra K Ω] (φ : A →ₐ[K] Ω) (S : Submonoid A)
    (H : ∀ a, φ a = 0 → ∃ d ∈ S, d * a = 0) (b : A ⊗[K] C)
    (hb : Algebra.TensorProduct.map φ (AlgHom.id K C) b = 0) : ∃ d ∈ S, (d ⊗ₜ[K] (1 : C)) * b = 0 := by
  have hex : Function.Exact (LinearMap.ker φ.toLinearMap).subtype φ.toLinearMap :=
    LinearMap.exact_subtype_ker_map _
  have hex' := Module.Flat.rTensor_exact C hex
  obtain ⟨w, rfl⟩ := (hex' b).1 hb
  clear hb
  induction w using TensorProduct.induction_on with
  | zero => exact ⟨1, S.one_mem, by simp⟩
  | tmul a c =>
    obtain ⟨d, hd, h⟩ := H a.1 a.2
    exact ⟨d, hd, by simp [h]⟩
  | add x y hx hy =>
    obtain ⟨d₁, m₁, h₁⟩ := hx
    obtain ⟨d₂, m₂, h₂⟩ := hy
    refine ⟨d₁ * d₂, S.mul_mem m₁ m₂, ?_⟩
    have e : (d₁ * d₂) ⊗ₜ[K] (1 : C) = (d₁ ⊗ₜ[K] (1 : C)) * (d₂ ⊗ₜ[K] (1 : C)) := by simp
    rw [map_add, e]
    linear_combination (d₂ ⊗ₜ[K] (1 : C)) * h₁ + (d₁ ⊗ₜ[K] (1 : C)) * h₂

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨1, 0, by simp, by simp⟩`. Consider the case `tmul w c`. Take `⟨a, d, hd, h⟩` from `H w`. Conclude with `⟨d, a ⊗ₜ c, hd, by simp [mul_comm (φ d) w, h]⟩`.

Consider the case `add x y hx hy`. Take `⟨d₁, b₁, m₁, h₁⟩` from `hx`. Take `⟨d₂, b₂, m₂, h₂⟩` from `hy`. Use `⟨d₁ * d₂, (d₂ ⊗ₜ[K] (1 : C)) * b₁ + (d₁ ⊗ₜ[K] (1 : C)) * b₂, by simp [m₁, m₂], ?_⟩` and prove the remaining obligations. Establish `e : (φ (d₁ * d₂)) ⊗ₜ[K] (1 : C) = (φ d₁ ⊗ₜ[K] (1 : C)) * (φ d₂ ⊗ₜ[K] (1 : C))` using `by simp`.

Simplify using `only [map_add, map_mul (Algebra.TensorProduct.map φ (AlgHom.id K C)), ← h₁, ← h₂, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, e]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tensor_frac [Field Ω] [Algebra K Ω] (φ : A →ₐ[K] Ω) (H : ∀ w : Ω, ∃ a d, φ d ≠ 0 ∧ w * φ d = φ a)
    (x : Ω ⊗[K] C) : ∃ (d : A) (b : A ⊗[K] C), φ d ≠ 0 ∧
      ((φ d) ⊗ₜ[K] (1 : C)) * x = Algebra.TensorProduct.map φ (AlgHom.id K C) b := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨1, 0, by simp, by simp⟩
  | tmul w c =>
    obtain ⟨a, d, hd, h⟩ := H w
    exact ⟨d, a ⊗ₜ c, hd, by simp [mul_comm (φ d) w, h]⟩
  | add x y hx hy =>
    obtain ⟨d₁, b₁, m₁, h₁⟩ := hx
    obtain ⟨d₂, b₂, m₂, h₂⟩ := hy
    refine ⟨d₁ * d₂, (d₂ ⊗ₜ[K] (1 : C)) * b₁ + (d₁ ⊗ₜ[K] (1 : C)) * b₂, by simp [m₁, m₂], ?_⟩
    have e : (φ (d₁ * d₂)) ⊗ₜ[K] (1 : C) = (φ d₁ ⊗ₜ[K] (1 : C)) * (φ d₂ ⊗ₜ[K] (1 : C)) := by simp
    simp only [map_add, map_mul (Algebra.TensorProduct.map φ (AlgHom.id K C)), ← h₁, ← h₂,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, e]
    ring

end Tensor

section Transfer

variable {Y : Scheme.{0}} {R F : Type} [CommRing R] [Field F]

/- English proof (translation)
The claim follows from `(genMap_stalkMap' (CptModel.pt e) j p h x).symm`.
-/
theorem genMap_open (e : R →+* F) (j : Sp R ⟶ Y) (p : Cpt (CptModel.pt e))
    (h : genPt (CptModel.pt e ≫ j) ⤳ j p.1) (x : Y.presheaf.stalk (j p.1)) :
    genMap (CptModel.pt e ≫ j) ⟨j p.1, h⟩ x = genMap (CptModel.pt e) p ((j.stalkMap p.1).hom x) :=
  (genMap_stalkMap' (CptModel.pt e) j p h x).symm

/- English proof (translation)
The claim follows from `ConcreteCategory.bijective_of_isIso (j.stalkMap P)`.
-/
theorem stalkMap_bijective (j : Sp R ⟶ Y) [IsOpenImmersion j] (P : Sp R) :
    Function.Bijective (j.stalkMap P).hom :=
  ConcreteCategory.bijective_of_isIso (j.stalkMap P)

/- English proof (translation)
Substitute `hζ` using the available equality. Establish `h₀ : genPt (CptModel.pt e) ⤳ P` using `(PrimeSpectrum.le_iff_specializes _ _).1 (by`. Express the relevant statement in the definitionally equal form `(genPt (CptModel.pt e)).asIdeal ≤ P.asIdeal`. Rewrite using `[CptModel.genPt_asIdeal]`. Introduce `b hb`.

Take `⟨u, hu, hub⟩` from `H b hb`. Establish `h0 : u * b ∈ P.asIdeal` using `by rw [hub]; exact zero_mem _`. Conclude with `(P.isPrime.mem_or_mem h0).resolve_left hu)`. Use `⟨h₀.map j.continuous, fun h => ?_⟩` and prove the remaining obligations. Establish `hi` using `(inj_iff e ⟨P, h₀⟩).2 H`.

Introduce `x y hxy`. Rewrite `hxy` using `[genMap_open e j ⟨P, h₀⟩ h, genMap_open e j ⟨P, h₀⟩ h]`. Conclude with `(stalkMap_bijective j P).1 (hi hxy)`.
-/
theorem local_transfer (ζ : Sp F ⟶ Y) (j : Sp R ⟶ Y) [IsOpenImmersion j] (e : R →+* F)
    (hζ : spMap e ≫ j = ζ) (P : Sp R) (H : ∀ b, e b = 0 → ∃ u, u ∉ P.asIdeal ∧ u * b = 0) :
    genPt ζ ⤳ j P ∧ ∀ h : genPt ζ ⤳ j P, Function.Injective (genMap ζ ⟨j P, h⟩) := by
  subst hζ
  have h₀ : genPt (CptModel.pt e) ⤳ P := (PrimeSpectrum.le_iff_specializes _ _).1 (by
    change (genPt (CptModel.pt e)).asIdeal ≤ P.asIdeal
    rw [CptModel.genPt_asIdeal]
    intro b hb
    obtain ⟨u, hu, hub⟩ := H b hb
    have h0 : u * b ∈ P.asIdeal := by rw [hub]; exact zero_mem _
    exact (P.isPrime.mem_or_mem h0).resolve_left hu)
  refine ⟨h₀.map j.continuous, fun h => ?_⟩
  have hi := (inj_iff e ⟨P, h₀⟩).2 H
  intro x y hxy
  rw [genMap_open e j ⟨P, h₀⟩ h, genMap_open e j ⟨P, h₀⟩ h] at hxy
  exact (stalkMap_bijective j P).1 (hi hxy)

/- English proof (translation)
Substitute `hζ` using the available equality. Establish `h₀ : genPt (CptModel.pt e) ⤳ P` using `j.isOpenEmbedding.isInducing.specializes_iff.1 h`. Use `(inj_iff e ⟨P, h₀⟩).1 fun x y hxy => ?_` and prove the remaining obligations. Take `⟨x, rfl⟩` from `(stalkMap_bijective j P).2 x`. Take `⟨y, rfl⟩` from `(stalkMap_bijective j P).2 y`.

Rewrite `hxy` using `[← genMap_open e j ⟨P, h₀⟩ h, ← genMap_open e j ⟨P, h₀⟩ h]`. Rewrite using `[hi hxy]`.
-/
theorem local_descend (ζ : Sp F ⟶ Y) (j : Sp R ⟶ Y) [IsOpenImmersion j] (e : R →+* F)
    (hζ : spMap e ≫ j = ζ) (P : Sp R) (h : genPt ζ ⤳ j P)
    (hi : Function.Injective (genMap ζ ⟨j P, h⟩)) : ∀ b, e b = 0 → ∃ u, u ∉ P.asIdeal ∧ u * b = 0 := by
  subst hζ
  have h₀ : genPt (CptModel.pt e) ⤳ P := j.isOpenEmbedding.isInducing.specializes_iff.1 h
  refine (inj_iff e ⟨P, h₀⟩).1 fun x y hxy => ?_
  obtain ⟨x, rfl⟩ := (stalkMap_bijective j P).2 x
  obtain ⟨y, rfl⟩ := (stalkMap_bijective j P).2 y
  rw [← genMap_open e j ⟨P, h₀⟩ h, ← genMap_open e j ⟨P, h₀⟩ h] at hxy
  rw [hi hxy]

/- English proof (translation)
Substitute `hζ` using the available equality. Establish `h₀ : genPt (CptModel.pt e) ⤳ P` using `j.isOpenEmbedding.isInducing.specializes_iff.1 h`. Rewrite using `[← CptModel.mem_regAt_iff e ⟨P, h₀⟩ c]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, rfl⟩`.

Conclude with `⟨_, (genMap_open e j ⟨P, h₀⟩ h x).symm⟩`. Introduce and unpack `⟨x, rfl⟩`. Take `⟨x, rfl⟩` from `(stalkMap_bijective j P).2 x`. Conclude with `⟨x, genMap_open e j ⟨P, h₀⟩ h x⟩`.
-/
theorem reg_transfer (ζ : Sp F ⟶ Y) (j : Sp R ⟶ Y) [IsOpenImmersion j] (e : R →+* F)
    (hζ : spMap e ≫ j = ζ) (P : Sp R) (h : genPt ζ ⤳ j P) (c : F) :
    c ∈ regAt ζ ⟨j P, h⟩ ↔ ∃ a s : R, s ∉ P.asIdeal ∧ e s ≠ 0 ∧ c * e s = e a := by
  subst hζ
  have h₀ : genPt (CptModel.pt e) ⤳ P := j.isOpenEmbedding.isInducing.specializes_iff.1 h
  rw [← CptModel.mem_regAt_iff e ⟨P, h₀⟩ c]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨_, (genMap_open e j ⟨P, h₀⟩ h x).symm⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨x, rfl⟩ := (stalkMap_bijective j P).2 x
    exact ⟨x, genMap_open e j ⟨P, h₀⟩ h x⟩

end Transfer

/- English proof (translation)
Set `ψ : CommRingCat.of K ⟶ Γ(X, U)` to `Spec.preimage (hU.fromSpec ≫ s)`. Use `letI alg : Algebra K Γ(X, U) := ψ.hom.toAlgebra`. Establish `hψ : hU.fromSpec ≫ s = Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, U)))` using `(Spec.map_preimage _).symm`. Set `y : Sp C ⟶ Sp K` to `spMap (algebraMap K C)`. Set `m : pullback (hU.fromSpec ≫ s) y ⟶ pullback s y` to `pullback.lift (pullback.fst _ _ ≫ hU.fromSpec) (pullback.snd _ _) (by rw [Category.assoc, pullback.condition])`.

Establish `hpb : IsPullback (pullback.fst (hU.fromSpec ≫ s) y) m hU.fromSpec (pullback.fst s y)`. Use `IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback _ _)` and prove the remaining obligations. Rewrite using `[pullback.lift_snd]`. Conclude with `IsPullback.of_hasPullback _ _`. Establish `hm : IsOpenImmersion m` using `MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion) hpb (inferInstance : IsOpenImmersion hU.fromSpec)`.

Set `e : pullback (hU.fromSpec ≫ s) y ≅ Spec (.of (Γ(X, U) ⊗[K] C))` to `pullback.congrHom hψ rfl ≪≫ pullbackSpecIso K Γ(X, U) C`. Establish `hm1 : m ≫ pullback.fst s y = pullback.fst _ _ ≫ hU.fromSpec` using `pullback.lift_fst _ _ _`. Establish `hm2 : m ≫ pullback.snd s y = pullback.snd _ _` using `pullback.lift_snd _ _ _`. Establish `c1 : (pullback.congrHom hψ (rfl : y = y)).inv ≫ pullback.fst (hU.fromSpec ≫ s) y = pullback.fst _ y`. Simplify using `only [pullback.congrHom_inv, pullback.map]`.

Conclude with `(pullback.lift_fst _ _ _).trans (Category.comp_id _)`. Establish `c2 : (pullback.congrHom hψ (rfl : y = y)).inv ≫ pullback.snd (hU.fromSpec ≫ s) y = pullback.snd _ y`. Simplify using `only [pullback.congrHom_inv, pullback.map]`. Conclude with `(pullback.lift_snd _ _ _).trans (Category.comp_id _)`. Establish `he1 : e.inv ≫ pullback.fst (hU.fromSpec ≫ s) y = spMap (Algebra.TensorProduct.includeLeftRingHom (R` using `K) (A := Γ(X, U)) (B := C)) := by`.

Simplify using `only [e, Iso.trans_inv, Category.assoc, c1]`. Conclude with `pullbackSpecIso_inv_fst K Γ(X, U) C`. Establish `he2 : e.inv ≫ pullback.snd (hU.fromSpec ≫ s) y = spMap (Algebra.TensorProduct.includeRight (R` using `K) (A := Γ(X, U)) (B := C)).toRingHom := by`. Simplify using `only [e, Iso.trans_inv, Category.assoc, c2]`. Conclude with `pullbackSpecIso_inv_snd K Γ(X, U) C`.

Establish `hr : Set.range m = pullback.fst s y ⁻¹' (U : Set X)`. Establish `e2 : m = hpb.isoPullback.hom ≫ pullback.snd hU.fromSpec (pullback.fst s y)` using `(hpb.isoPullback_hom_snd).symm`. Rewrite using `[e2, Scheme.Hom.comp_base, TopCat.coe_comp, hpb.isoPullback.hom.surjective.range_comp, Scheme.Pullback.range_snd, hU.range_fromSpec]`. Use `⟨Γ(X, U), inferInstance, alg, hU.fromSpec, e.inv ≫ m, inferInstance, hU.range_fromSpec, hψ, inferInstance, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show (e.inv ≫ m) ≫ pullback.fst s y = _`.

Rewrite using `[Category.assoc, hm1, ← Category.assoc, he1]`. Use `show (e.inv ≫ m) ≫ pullback.snd s y = _`. Rewrite using `[Category.assoc, hm2, he2]`. Rewrite using `[Scheme.Hom.comp_base, TopCat.coe_comp, e.inv.surjective.range_comp]`. Conclude with `hr`.
-/
theorem exists_chart {K C : Type} [Field K] [CommRing C] [Algebra K C] (s : X ⟶ Sp K) (U : X.Opens)
    (hU : IsAffineOpen U) :
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra K A) (a : Sp A ⟶ X)
      (j : Sp (A ⊗[K] C) ⟶ pullback s (spMap (algebraMap K C))),
      IsOpenImmersion a ∧ Set.range a = (U : Set X) ∧ a ≫ s = spMap (algebraMap K A) ∧ IsOpenImmersion j ∧
      j ≫ pullback.fst s (spMap (algebraMap K C)) =
        spMap (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := A) (B := C)) ≫ a ∧
      j ≫ pullback.snd s (spMap (algebraMap K C)) =
        spMap (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := C)).toRingHom ∧
      Set.range j = pullback.fst s (spMap (algebraMap K C)) ⁻¹' (U : Set X) := by
  let ψ : CommRingCat.of K ⟶ Γ(X, U) := Spec.preimage (hU.fromSpec ≫ s)
  letI alg : Algebra K Γ(X, U) := ψ.hom.toAlgebra
  have hψ : hU.fromSpec ≫ s = Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, U))) := (Spec.map_preimage _).symm
  let y : Sp C ⟶ Sp K := spMap (algebraMap K C)
  let m : pullback (hU.fromSpec ≫ s) y ⟶ pullback s y :=
    pullback.lift (pullback.fst _ _ ≫ hU.fromSpec) (pullback.snd _ _)
      (by rw [Category.assoc, pullback.condition])
  have hpb : IsPullback (pullback.fst (hU.fromSpec ≫ s) y) m hU.fromSpec (pullback.fst s y) := by
    refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback _ _)
    rw [pullback.lift_snd]
    exact IsPullback.of_hasPullback _ _
  have hm : IsOpenImmersion m :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion) hpb
      (inferInstance : IsOpenImmersion hU.fromSpec)
  let e : pullback (hU.fromSpec ≫ s) y ≅ Spec (.of (Γ(X, U) ⊗[K] C)) :=
    pullback.congrHom hψ rfl ≪≫ pullbackSpecIso K Γ(X, U) C
  have hm1 : m ≫ pullback.fst s y = pullback.fst _ _ ≫ hU.fromSpec := pullback.lift_fst _ _ _
  have hm2 : m ≫ pullback.snd s y = pullback.snd _ _ := pullback.lift_snd _ _ _
  have c1 : (pullback.congrHom hψ (rfl : y = y)).inv ≫ pullback.fst (hU.fromSpec ≫ s) y =
      pullback.fst _ y := by
    simp only [pullback.congrHom_inv, pullback.map]
    exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have c2 : (pullback.congrHom hψ (rfl : y = y)).inv ≫ pullback.snd (hU.fromSpec ≫ s) y =
      pullback.snd _ y := by
    simp only [pullback.congrHom_inv, pullback.map]
    exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have he1 : e.inv ≫ pullback.fst (hU.fromSpec ≫ s) y =
      spMap (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := Γ(X, U)) (B := C)) := by
    simp only [e, Iso.trans_inv, Category.assoc, c1]
    exact pullbackSpecIso_inv_fst K Γ(X, U) C
  have he2 : e.inv ≫ pullback.snd (hU.fromSpec ≫ s) y =
      spMap (Algebra.TensorProduct.includeRight (R := K) (A := Γ(X, U)) (B := C)).toRingHom := by
    simp only [e, Iso.trans_inv, Category.assoc, c2]
    exact pullbackSpecIso_inv_snd K Γ(X, U) C
  have hr : Set.range m = pullback.fst s y ⁻¹' (U : Set X) := by
    have e2 : m = hpb.isoPullback.hom ≫ pullback.snd hU.fromSpec (pullback.fst s y) :=
      (hpb.isoPullback_hom_snd).symm
    rw [e2, Scheme.Hom.comp_base, TopCat.coe_comp, hpb.isoPullback.hom.surjective.range_comp,
      Scheme.Pullback.range_snd, hU.range_fromSpec]
  refine ⟨Γ(X, U), inferInstance, alg, hU.fromSpec, e.inv ≫ m, inferInstance, hU.range_fromSpec, hψ,
    inferInstance, ?_, ?_, ?_⟩
  · show (e.inv ≫ m) ≫ pullback.fst s y = _
    rw [Category.assoc, hm1, ← Category.assoc, he1]
  · show (e.inv ≫ m) ≫ pullback.snd s y = _
    rw [Category.assoc, hm2, he2]
  · rw [Scheme.Hom.comp_base, TopCat.coe_comp, e.inv.surjective.range_comp]
    exact hr

section BaseChange

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

/- English proof (translation)
Rewrite using `[spMap, spMap, ← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem spMap_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [spMap, spMap, ← Spec.map_comp]
  rfl

/- English proof (translation)
Establish `hr : Set.range ξ ⊆ Set.range a`. Introduce and unpack `_ ⟨z, rfl⟩`. Establish `: z = IsLocalRing.closedPoint Ω` using `Subsingleton.elim (α := PrimeSpectrum Ω) _ _`. Rewrite using `[this]`. Conclude with `h`.

Set `g` to `IsOpenImmersion.lift a ξ hr`. Use `⟨(Spec.preimage g).hom, ?_⟩` and prove the remaining obligations. Establish `e : CommRingCat.ofHom (Spec.preimage g).hom = Spec.preimage g` using `rfl`. Rewrite using `[spMap, e, Spec.map_preimage]`. Conclude with `IsOpenImmersion.lift_fac a ξ hr`.
-/
theorem exists_ringHom_of_mem {A : Type} [CommRing A] (a : Sp A ⟶ X) [IsOpenImmersion a] (ξ : Sp Ω ⟶ X)
    (h : genPt ξ ∈ Set.range a) : ∃ φ : A →+* Ω, spMap φ ≫ a = ξ := by
  have hr : Set.range ξ ⊆ Set.range a := by
    rintro _ ⟨z, rfl⟩
    have : z = IsLocalRing.closedPoint Ω := Subsingleton.elim (α := PrimeSpectrum Ω) _ _
    rw [this]
    exact h
  let g := IsOpenImmersion.lift a ξ hr
  refine ⟨(Spec.preimage g).hom, ?_⟩
  have e : CommRingCat.ofHom (Spec.preimage g).hom = Spec.preimage g := rfl
  rw [spMap, e, Spec.map_preimage]
  exact IsOpenImmersion.lift_fac a ξ hr

/- English proof (translation)
Take `⟨A, _, _, a, j, ha, hr, has, hj, hjf, hjs, hjr⟩` from `exists_chart (C := C) s U hU`. Take `⟨φ₀, hφ₀⟩` from `exists_ringHom_of_mem a ξ (by rw [hr]; exact hmem)`. Establish `hcomm : ∀ k, φ₀ (algebraMap K A k) = algebraMap K Ω k`. Establish `e : spMap (φ₀.comp (algebraMap K A)) = spMap (algebraMap K Ω)`. Rewrite using `[← hξs, ← hφ₀, Category.assoc, has, spMap_comp]`.

Establish `e2` using `Spec.map_injective e`. Conclude with `fun k => congrArg (fun t => t.hom k) e2`. Set `φ : A →ₐ[K] Ω` to `{ φ₀ with commutes' := hcomm }`. Use `⟨A, _, _, a, j, φ, ha, hr, hφ₀, hj, hjf, hjr, ?_⟩` and prove the remaining obligations. Apply `pullback.hom_ext` to reduce the goal to its premises.

Rewrite using `[Category.assoc, hjf, h1, ← Category.assoc, spMap_comp, ← hφ₀, ← Category.assoc, spMap_comp]`. Use `congr 2`. Rewrite using `[Category.assoc, hjs, h2, spMap_comp]`. Establish `e : ((algebraMap (Ω ⊗[K] C) (FractionRing (Ω ⊗[K] C))).comp (Algebra.TensorProduct.map φ (AlgHom.id K C)).toRingHom).comp (Algebra.TensorProduct.includeRight (R` using `K) (A := A) (B := C)).toRingHom = (algebraMap (Ω ⊗[K] C) (FractionRing (Ω ⊗[K] C))).comp (Algebra.TensorProduct.includeRight (R := K) (A := Ω) (B := C)).toRingHom := by`. Use extensionality with `x`.

Simplify using the standard rewrite rules. Rewrite using `[e]`.
-/
theorem chart_data {K C : Type} [Field K] [Field C] [Algebra K C] [Algebra K Ω] [IsDomain (Ω ⊗[K] C)]
    (s : X ⟶ Sp K) (ξ : Sp Ω ⟶ X) (hξs : ξ ≫ s = spMap (algebraMap K Ω))
    (ξ' : Sp (FractionRing (Ω ⊗[K] C)) ⟶ pullback s (spMap (algebraMap K C)))
    (h1 : ξ' ≫ pullback.fst s (spMap (algebraMap K C)) =
      spMap ((algebraMap (Ω ⊗[K] C) (FractionRing (Ω ⊗[K] C))).comp
        (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := Ω) (B := C))) ≫ ξ)
    (h2 : ξ' ≫ pullback.snd s (spMap (algebraMap K C)) =
      spMap ((algebraMap (Ω ⊗[K] C) (FractionRing (Ω ⊗[K] C))).comp
        (Algebra.TensorProduct.includeRight (R := K) (A := Ω) (B := C)).toRingHom))
    (U : X.Opens) (hU : IsAffineOpen U) (hmem : genPt ξ ∈ U) :
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra K A) (a : Sp A ⟶ X)
      (j : Sp (A ⊗[K] C) ⟶ pullback s (spMap (algebraMap K C))) (φ : A →ₐ[K] Ω),
      IsOpenImmersion a ∧ Set.range a = (U : Set X) ∧ spMap φ.toRingHom ≫ a = ξ ∧ IsOpenImmersion j ∧
      j ≫ pullback.fst s (spMap (algebraMap K C)) =
        spMap (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := A) (B := C)) ≫ a ∧
      Set.range j = pullback.fst s (spMap (algebraMap K C)) ⁻¹' (U : Set X) ∧
      spMap ((algebraMap (Ω ⊗[K] C) (FractionRing (Ω ⊗[K] C))).comp
        (Algebra.TensorProduct.map φ (AlgHom.id K C)).toRingHom) ≫ j = ξ' := by
  obtain ⟨A, _, _, a, j, ha, hr, has, hj, hjf, hjs, hjr⟩ := exists_chart (C := C) s U hU
  obtain ⟨φ₀, hφ₀⟩ := exists_ringHom_of_mem a ξ (by rw [hr]; exact hmem)
  have hcomm : ∀ k, φ₀ (algebraMap K A k) = algebraMap K Ω k := by
    have e : spMap (φ₀.comp (algebraMap K A)) = spMap (algebraMap K Ω) := by
      rw [← hξs, ← hφ₀, Category.assoc, has, spMap_comp]
    have e2 := Spec.map_injective e
    exact fun k => congrArg (fun t => t.hom k) e2
  let φ : A →ₐ[K] Ω := { φ₀ with commutes' := hcomm }
  refine ⟨A, _, _, a, j, φ, ha, hr, hφ₀, hj, hjf, hjr, ?_⟩
  apply pullback.hom_ext
  · rw [Category.assoc, hjf, h1, ← Category.assoc, spMap_comp, ← hφ₀, ← Category.assoc, spMap_comp]
    congr 2
  · rw [Category.assoc, hjs, h2, spMap_comp]
    have e : ((algebraMap (Ω ⊗[K] C) (FractionRing (Ω ⊗[K] C))).comp
        (Algebra.TensorProduct.map φ (AlgHom.id K C)).toRingHom).comp
          (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := C)).toRingHom =
        (algebraMap (Ω ⊗[K] C) (FractionRing (Ω ⊗[K] C))).comp
          (Algebra.TensorProduct.includeRight (R := K) (A := Ω) (B := C)).toRingHom := by
      ext x
      simp
    rw [e]

end BaseChange

section BaseChange2

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

/- English proof (translation)
Clear the denominators using the available nonvanishing facts.
-/
theorem frac_id {F : Type} [Field F] (u v p q : F) (hv : v ≠ 0) : u / v * (p * (q * v)) = q * (p * u) := by
  field_simp

/- English proof (translation)
Take `⟨x, hx⟩` from `p`. Take `rfl : x = genPt ξ` from `h`. Use `CptModel.regAt_self hξ` as an intermediate fact. Establish `h2 : w ∈ regAt ξ (CptModel.self ξ)` using `by rw [this]; trivial`. Conclude with `h2`.
-/
theorem mem_regAt_of_eq {ξ : Sp Ω ⟶ X} (hξ : IsCptGen ξ) (p : Cpt ξ) (h : p.1 = genPt ξ) (w : Ω) :
    w ∈ regAt ξ p := by
  obtain ⟨x, hx⟩ := p
  obtain rfl : x = genPt ξ := h
  have := CptModel.regAt_self hξ
  have h2 : w ∈ regAt ξ (CptModel.self ξ) := by rw [this]; trivial
  exact h2

/- English proof (translation)
Take `⟨x, hx⟩` from `p`. Take `rfl : x = genPt ξ` from `h`. Take `⟨t, ht⟩` from `hw`. Establish `h2 : genMap ξ (CptModel.self ξ) t = w` using `ht`. Rewrite `h2` using `[CptModel.genMap_self]`.

Conclude with `⟨t, h2⟩`.
-/
theorem exists_stalk_of_reg {ξ : Sp Ω ⟶ X} (p : Cpt ξ) (h : p.1 = genPt ξ) {w : Ω} (hw : w ∈ regAt ξ p) :
    ∃ x, (Scheme.stalkClosedPointTo ξ).hom x = w := by
  obtain ⟨x, hx⟩ := p
  obtain rfl : x = genPt ξ := h
  obtain ⟨t, ht⟩ := hw
  have h2 : genMap ξ (CptModel.self ξ) t = w := ht
  rw [CptModel.genMap_self] at h2
  exact ⟨t, h2⟩

/- English proof (translation)
Use `haveI hdom : IsDomain (Ω ⊗[K] C) := GlobalTheory.T.alg_closed_tensor_isDomain K Ω C fun a ha => by`. Take `⟨x, y, hy, h⟩` from `hCC a ha`. Conclude with `⟨x / y, by rw [map_div₀, ← h, mul_div_cancel_right₀ _ ((map_ne_zero _).2 hy)]⟩`. Set `aT` to `algebraMap (Ω ⊗[K] C) (FractionRing (Ω ⊗[K] C))`. Set `i : Ω →+* FractionRing (Ω ⊗[K] C)` to `aT.comp (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := Ω) (B := C))`.

Set `ic : C →+* FractionRing (Ω ⊗[K] C)` to `aT.comp (Algebra.TensorProduct.includeRight (R := K) (A := Ω) (B := C)).toRingHom`. Use `letI alg' : Algebra C (FractionRing (Ω ⊗[K] C)) := ic.toAlgebra`. Establish `hcond : (spMap i ≫ ξ) ≫ s = spMap ic ≫ spMap (algebraMap K C)`. Rewrite using `[Category.assoc, hξs, spMap_comp, spMap_comp]`. Establish `e : i.comp (algebraMap K Ω) = ic.comp (algebraMap K C)`.

Use extensionality with `k`. Establish `e0 : algebraMap K Ω k ⊗ₜ[K] (1 : C) = (1 : Ω) ⊗ₜ[K] algebraMap K C k`. Simplify using `only [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]`. Use `show aT (algebraMap K Ω k ⊗ₜ[K] (1 : C)) = aT ((1 : Ω) ⊗ₜ[K] algebraMap K C k)`. Rewrite using `[e0]`.

Rewrite using `[e]`. Set `ξ' : Sp (FractionRing (Ω ⊗[K] C)) ⟶ pullback s (spMap (algebraMap K C))` to `pullback.lift _ _ hcond`. Establish `h1 : ξ' ≫ pullback.fst s (spMap (algebraMap K C)) = spMap i ≫ ξ` using `pullback.lift_fst _ _ _`. Establish `h2 : ξ' ≫ pullback.snd s (spMap (algebraMap K C)) = spMap ic` using `pullback.lift_snd _ _ _`. Establish `hD : Dominates ξ' ξ (pullback.fst s (spMap (algebraMap K C))) i` using `h1`.

Establish `H1 : ∀ (p' : ↥(pullback s (spMap (algebraMap K C)))), genPt ξ ⤳ pullback.fst s (spMap (algebraMap K C)) p' → genPt ξ' ⤳ p' ∧ ∀ h : genPt ξ' ⤳ p', Function.Injective (genMap ξ' ⟨p', h⟩)`. Introduce `p' hp`. Take `⟨U, hU, hpU, -⟩` from `exists_isAffineOpen_mem_and_subset (show pullback.fst s (spMap (algebraMap K C)) p' ∈ (⊤ : X.Opens) from trivial)`. Take `⟨A, _, _, a, j, φ, ha, hr, hφ, hj, hjf, hjr, hjξ⟩` from `chart_data s ξ hξs ξ' h1 h2 U hU (hp.mem_open U.2 hpU)`. Establish `hpr : p' ∈ Set.range j` using `by rw [hjr]; exact hpU`.

Take `⟨P, rfl⟩` from `hpr`. Establish `hQ : a (spMap (Algebra.TensorProduct.includeLeftRingHom (R` using `K) (A := A) (B := C)) P) = pullback.fst s (spMap (algebraMap K C)) (j P) := by`. Use `congrArg (fun g => g P) hjf` as an intermediate fact. Simplify `this.symm` using `only [Scheme.Hom.comp_apply]`. Establish `h₁ : genPt ξ ⤳ a (spMap (Algebra.TensorProduct.includeLeftRingHom (R` using `K) (A := A) (B := C)) P) := by`.

Rewrite using `[hQ]`. Conclude with `hp`. Establish `H` using `local_descend ξ a φ.toRingHom hφ _ h₁ (hξ.inj ⟨_, h₁⟩)`. Use `local_transfer ξ' j _ hjξ P fun b hb => ?_` and prove the remaining obligations. Establish `hb' : Algebra.TensorProduct.map φ (AlgHom.id K C) b = 0` using `IsFractionRing.injective (Ω ⊗[K] C) (FractionRing (Ω ⊗[K] C)) (by simpa using hb)`.

Use `haveI hprime : (spMap (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := A) (B := C)) P).asIdeal.IsPrime := PrimeSpectrum.isPrime _`. Take `⟨d, hd, h⟩` from `tensor_ker φ (spMap (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := A) (B := C)) P).asIdeal.primeCompl (fun a ha => by`. Take `⟨u, hu, h⟩` from `H a ha`. Conclude with `⟨u, hu, h⟩) b hb'`. Conclude with `⟨d ⊗ₜ[K] (1 : C), hd, h⟩`.

Use `⟨FractionRing (Ω ⊗[K] C), inferInstance, alg', i, ξ', h2, hD, ⟨⟨?_, ?_⟩, fun p => ?_⟩, fun p' hp => (H1 p' hp).1⟩` and prove the remaining obligations. Establish `h0` using `(H1 (genPt ξ') (hD.specializes (CptModel.self ξ'))).2 (specializes_refl _)`. Establish `h3 : genMap ξ' ⟨genPt ξ', specializes_refl _⟩ = (Scheme.stalkClosedPointTo ξ').hom` using `CptModel.genMap_self ξ'`. Rewrite `h0` using `[h3]`. Conclude with `h0`.

Introduce `c`. Take `⟨U, hU, hpU, -⟩` from `exists_isAffineOpen_mem_and_subset (show genPt ξ ∈ (⊤ : X.Opens) from trivial)`. Take `⟨A, _, _, a, j, φ, ha, hr, hφ, hj, hjf, hjr, hjξ⟩` from `chart_data s ξ hξs ξ' h1 h2 U hU hpU`. Establish `hQ₀ : a (genPt (spMap φ.toRingHom)) = genPt ξ` using `congrArg genPt hφ`. Establish `hreg1 : genPt ξ ⤳ a (genPt (spMap φ.toRingHom))` using `by rw [hQ₀]`.

Establish `H : ∀ w : Ω, ∃ a' d, φ d ≠ 0 ∧ w * φ d = φ a'` using `fun w => by`. Take `⟨a', d, -, h0, he⟩` from `(reg_transfer ξ a φ.toRingHom hφ _ hreg1 w).1 (mem_regAt_of_eq hξ ⟨_, hreg1⟩ hQ₀ w)`. Conclude with `⟨a', d, h0, he⟩`. Generalize the expression as in `he : (algebraMap (Ω ⊗[K] C) (FractionRing (Ω ⊗[K] C))).comp (Algebra.TensorProduct.map φ (AlgHom.id K C)).toRingHom = e at hjξ`. Establish `hP₀ : j (genPt (spMap e)) = genPt ξ'` using `congrArg genPt hjξ`.

Establish `hreg2 : genPt ξ' ⤳ j (genPt (spMap e))` using `by rw [hP₀]`. Take `⟨x, y, hy, rfl⟩` from `IsFractionRing.div_surjective (A := Ω ⊗[K] C) c`. Take `⟨d₁, b₁, m₁, e₁⟩` from `tensor_frac φ H x`. Take `⟨d₂, b₂, m₂, e₂⟩` from `tensor_frac φ H y`. Establish `hy0 : aT y ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy`.

Establish `eD : ∀ d, e (d ⊗ₜ[K] (1 : C)) = i (φ d)` using `fun d => by`. Substitute `he` using the available equality. Use `show aT (Algebra.TensorProduct.map φ (AlgHom.id K C) (d ⊗ₜ[K] (1 : C))) = aT (φ d ⊗ₜ[K] (1 : C))`. Simplify using the standard rewrite rules. Establish `eb : ∀ (d : A) (b : A ⊗[K] C) (z : Ω ⊗[K] C), φ d ⊗ₜ[K] (1 : C) * z = Algebra.TensorProduct.map φ (AlgHom.id K C) b → e b = i (φ d) * aT z`.

Introduce `d b z hz`. Substitute `he` using the available equality. Use `show aT (Algebra.TensorProduct.map φ (AlgHom.id K C) b) = aT (φ d ⊗ₜ[K] (1 : C)) * aT z`. Rewrite using `[← hz, map_mul]`. Establish `i1 : i (φ d₁) ≠ 0` using `(map_ne_zero i).2 m₁`.

Establish `i2 : i (φ d₂) ≠ 0` using `(map_ne_zero i).2 m₂`. Establish `hne : e ((d₁ ⊗ₜ[K] (1 : C)) * b₂) ≠ 0`. Rewrite using `[map_mul, eD, eb d₂ b₂ y e₂]`. Conclude with `mul_ne_zero i1 (mul_ne_zero i2 hy0)`. Use `exists_stalk_of_reg ⟨_, hreg2⟩ hP₀ ((reg_transfer ξ' j e hjξ _ hreg2 _).2 ⟨(d₂ ⊗ₜ[K] (1 : C)) * b₁, (d₁ ⊗ₜ[K] (1 : C)) * b₂, ?_, hne, ?_⟩)` and prove the remaining obligations.

Introduce `hu`. Express the relevant statement in the definitionally equal form `_ ∈ (genPt (CptModel.pt e)).asIdeal at hu`. Rewrite `hu` using `[CptModel.genPt_asIdeal]`. Conclude with `hne hu`. Rewrite using `[map_mul, map_mul, eD, eD, eb d₁ b₁ x e₁, eb d₂ b₂ y e₂]`.

Conclude with `frac_id _ _ _ _ hy0`. Conclude with `(H1 p.1 (hD.specializes p)).2 p.2`.
-/
theorem cpt_base_change_dominates (K C : Type) [Field K] [CharZero K] [Field C] [Algebra K C] (s : X ⟶ Sp K)
    [Algebra K Ω] (ξ : Sp Ω ⟶ X) (hξs : ξ ≫ s = spMap (algebraMap K Ω)) (hξ : IsCptGen ξ)
    (hCC : ConstClosed K Ω) :
    ∃ (Ω' : Type) (_ : Field Ω') (_ : Algebra C Ω') (i : Ω →+* Ω')
      (ξ' : Sp Ω' ⟶ pullback s (spMap (algebraMap K C))),
      ξ' ≫ pullback.snd s (spMap (algebraMap K C)) = spMap (algebraMap C Ω') ∧
      Dominates ξ' ξ (pullback.fst s (spMap (algebraMap K C))) i ∧ IsCptGen ξ' ∧
      ∀ p' : ↥(pullback s (spMap (algebraMap K C))),
        genPt ξ ⤳ pullback.fst s (spMap (algebraMap K C)) p' → genPt ξ' ⤳ p' := by
  haveI hdom : IsDomain (Ω ⊗[K] C) := GlobalTheory.T.alg_closed_tensor_isDomain K Ω C fun a ha => by
    obtain ⟨x, y, hy, h⟩ := hCC a ha
    exact ⟨x / y, by rw [map_div₀, ← h, mul_div_cancel_right₀ _ ((map_ne_zero _).2 hy)]⟩
  let aT := algebraMap (Ω ⊗[K] C) (FractionRing (Ω ⊗[K] C))
  let i : Ω →+* FractionRing (Ω ⊗[K] C) :=
    aT.comp (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := Ω) (B := C))
  let ic : C →+* FractionRing (Ω ⊗[K] C) :=
    aT.comp (Algebra.TensorProduct.includeRight (R := K) (A := Ω) (B := C)).toRingHom
  letI alg' : Algebra C (FractionRing (Ω ⊗[K] C)) := ic.toAlgebra
  have hcond : (spMap i ≫ ξ) ≫ s = spMap ic ≫ spMap (algebraMap K C) := by
    rw [Category.assoc, hξs, spMap_comp, spMap_comp]
    have e : i.comp (algebraMap K Ω) = ic.comp (algebraMap K C) := by
      ext k
      have e0 : algebraMap K Ω k ⊗ₜ[K] (1 : C) = (1 : Ω) ⊗ₜ[K] algebraMap K C k := by
        simp only [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
      show aT (algebraMap K Ω k ⊗ₜ[K] (1 : C)) = aT ((1 : Ω) ⊗ₜ[K] algebraMap K C k)
      rw [e0]
    rw [e]
  let ξ' : Sp (FractionRing (Ω ⊗[K] C)) ⟶ pullback s (spMap (algebraMap K C)) := pullback.lift _ _ hcond
  have h1 : ξ' ≫ pullback.fst s (spMap (algebraMap K C)) = spMap i ≫ ξ := pullback.lift_fst _ _ _
  have h2 : ξ' ≫ pullback.snd s (spMap (algebraMap K C)) = spMap ic := pullback.lift_snd _ _ _
  have hD : Dominates ξ' ξ (pullback.fst s (spMap (algebraMap K C))) i := h1
  have H1 : ∀ (p' : ↥(pullback s (spMap (algebraMap K C)))),
      genPt ξ ⤳ pullback.fst s (spMap (algebraMap K C)) p' →
      genPt ξ' ⤳ p' ∧ ∀ h : genPt ξ' ⤳ p', Function.Injective (genMap ξ' ⟨p', h⟩) := by
    intro p' hp
    obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset
      (show pullback.fst s (spMap (algebraMap K C)) p' ∈ (⊤ : X.Opens) from trivial)
    obtain ⟨A, _, _, a, j, φ, ha, hr, hφ, hj, hjf, hjr, hjξ⟩ :=
      chart_data s ξ hξs ξ' h1 h2 U hU (hp.mem_open U.2 hpU)
    have hpr : p' ∈ Set.range j := by rw [hjr]; exact hpU
    obtain ⟨P, rfl⟩ := hpr
    have hQ : a (spMap (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := A) (B := C)) P) =
        pullback.fst s (spMap (algebraMap K C)) (j P) := by
      have := congrArg (fun g => g P) hjf
      simpa only [Scheme.Hom.comp_apply] using this.symm
    have h₁ : genPt ξ ⤳ a (spMap (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := A) (B := C)) P) := by
      rw [hQ]; exact hp
    have H := local_descend ξ a φ.toRingHom hφ _ h₁ (hξ.inj ⟨_, h₁⟩)
    refine local_transfer ξ' j _ hjξ P fun b hb => ?_
    have hb' : Algebra.TensorProduct.map φ (AlgHom.id K C) b = 0 :=
      IsFractionRing.injective (Ω ⊗[K] C) (FractionRing (Ω ⊗[K] C)) (by simpa using hb)
    haveI hprime : (spMap (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := A) (B := C)) P).asIdeal.IsPrime :=
      PrimeSpectrum.isPrime _
    obtain ⟨d, hd, h⟩ := tensor_ker φ
      (spMap (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := A) (B := C)) P).asIdeal.primeCompl
      (fun a ha => by
        obtain ⟨u, hu, h⟩ := H a ha
        exact ⟨u, hu, h⟩) b hb'
    exact ⟨d ⊗ₜ[K] (1 : C), hd, h⟩
  refine ⟨FractionRing (Ω ⊗[K] C), inferInstance, alg', i, ξ', h2, hD, ⟨⟨?_, ?_⟩, fun p => ?_⟩,
    fun p' hp => (H1 p' hp).1⟩
  · have h0 := (H1 (genPt ξ') (hD.specializes (CptModel.self ξ'))).2 (specializes_refl _)
    have h3 : genMap ξ' ⟨genPt ξ', specializes_refl _⟩ = (Scheme.stalkClosedPointTo ξ').hom :=
      CptModel.genMap_self ξ'
    rw [h3] at h0
    exact h0
  · intro c
    obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (show genPt ξ ∈ (⊤ : X.Opens) from trivial)
    obtain ⟨A, _, _, a, j, φ, ha, hr, hφ, hj, hjf, hjr, hjξ⟩ := chart_data s ξ hξs ξ' h1 h2 U hU hpU
    have hQ₀ : a (genPt (spMap φ.toRingHom)) = genPt ξ := congrArg genPt hφ
    have hreg1 : genPt ξ ⤳ a (genPt (spMap φ.toRingHom)) := by rw [hQ₀]
    have H : ∀ w : Ω, ∃ a' d, φ d ≠ 0 ∧ w * φ d = φ a' := fun w => by
      obtain ⟨a', d, -, h0, he⟩ :=
        (reg_transfer ξ a φ.toRingHom hφ _ hreg1 w).1 (mem_regAt_of_eq hξ ⟨_, hreg1⟩ hQ₀ w)
      exact ⟨a', d, h0, he⟩
    generalize he : (algebraMap (Ω ⊗[K] C) (FractionRing (Ω ⊗[K] C))).comp
      (Algebra.TensorProduct.map φ (AlgHom.id K C)).toRingHom = e at hjξ
    have hP₀ : j (genPt (spMap e)) = genPt ξ' := congrArg genPt hjξ
    have hreg2 : genPt ξ' ⤳ j (genPt (spMap e)) := by rw [hP₀]
    obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := Ω ⊗[K] C) c
    obtain ⟨d₁, b₁, m₁, e₁⟩ := tensor_frac φ H x
    obtain ⟨d₂, b₂, m₂, e₂⟩ := tensor_frac φ H y
    have hy0 : aT y ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
    have eD : ∀ d, e (d ⊗ₜ[K] (1 : C)) = i (φ d) := fun d => by
      subst he
      show aT (Algebra.TensorProduct.map φ (AlgHom.id K C) (d ⊗ₜ[K] (1 : C))) = aT (φ d ⊗ₜ[K] (1 : C))
      simp
    have eb : ∀ (d : A) (b : A ⊗[K] C) (z : Ω ⊗[K] C),
        φ d ⊗ₜ[K] (1 : C) * z = Algebra.TensorProduct.map φ (AlgHom.id K C) b → e b = i (φ d) * aT z := by
      intro d b z hz
      subst he
      show aT (Algebra.TensorProduct.map φ (AlgHom.id K C) b) = aT (φ d ⊗ₜ[K] (1 : C)) * aT z
      rw [← hz, map_mul]
    have i1 : i (φ d₁) ≠ 0 := (map_ne_zero i).2 m₁
    have i2 : i (φ d₂) ≠ 0 := (map_ne_zero i).2 m₂
    have hne : e ((d₁ ⊗ₜ[K] (1 : C)) * b₂) ≠ 0 := by
      rw [map_mul, eD, eb d₂ b₂ y e₂]
      exact mul_ne_zero i1 (mul_ne_zero i2 hy0)
    refine exists_stalk_of_reg ⟨_, hreg2⟩ hP₀ ((reg_transfer ξ' j e hjξ _ hreg2 _).2
      ⟨(d₂ ⊗ₜ[K] (1 : C)) * b₁, (d₁ ⊗ₜ[K] (1 : C)) * b₂, ?_, hne, ?_⟩)
    · intro hu
      change _ ∈ (genPt (CptModel.pt e)).asIdeal at hu
      rw [CptModel.genPt_asIdeal] at hu
      exact hne hu
    · rw [map_mul, map_mul, eD, eD, eb d₁ b₁ x e₁, eb d₂ b₂ y e₂]
      exact frac_id _ _ _ _ hy0
  · exact (H1 p.1 (hD.specializes p)).2 p.2

end BaseChange2

/- English proof (translation)
Take `⟨h1, s, hs, rfl⟩` from `h`. Take `⟨h2, s', hs', rfl⟩` from `h'`. Establish `: s = s'` using `hξ.inj ⟨centre z, h1⟩ (hs.trans hs'.symm)`. Rewrite using `[this]`.
-/
theorem val_eq {ξ : Sp Ω ⟶ X} {R : Type} [CommRing R] [IsLocalRing R] {z : Sp R ⟶ X} (hξ : IsCptGen ξ) {a : Ω}
    {r r' : R} (h : ValAt ξ z a r) (h' : ValAt ξ z a r') : r = r' := by
  obtain ⟨h1, s, hs, rfl⟩ := h
  obtain ⟨h2, s', hs', rfl⟩ := h'
  have : s = s' := hξ.inj ⟨centre z, h1⟩ (hs.trans hs'.symm)
  rw [this]

/- English proof (translation)
Take `⟨h1, s, rfl, rfl⟩` from `h`. Take `⟨h2, s', rfl, rfl⟩` from `h'`. Conclude with `⟨h1, s * s', map_mul _ _ _, map_mul _ _ _⟩`.
-/
theorem val_mul' {ξ : Sp Ω ⟶ X} {R : Type} [CommRing R] [IsLocalRing R] {z : Sp R ⟶ X} {a a' : Ω} {r r' : R}
    (h : ValAt ξ z a r) (h' : ValAt ξ z a' r') : ValAt ξ z (a * a') (r * r') := by
  obtain ⟨h1, s, rfl, rfl⟩ := h
  obtain ⟨h2, s', rfl, rfl⟩ := h'
  exact ⟨h1, s * s', map_mul _ _ _, map_mul _ _ _⟩

/- English proof (translation)
Take `⟨h, s, rfl, rfl⟩` from `hv`. Conclude with `⟨h', (f.stalkMap (centre z)).hom s, PullReg.stalkMap_comp_genMap hD ⟨centre z, h'⟩ h s, (congrArg (fun t => t.hom s) (Scheme.stalkClosedPointTo_comp z f)).symm⟩`.
-/
theorem val_pull {ξ : Sp Ω ⟶ X} {ξ' : Sp Ω' ⟶ X'} {f : X' ⟶ X} {i : Ω →+* Ω'} (hD : Dominates ξ' ξ f i)
    {R : Type} [CommRing R] [IsLocalRing R] (z : Sp R ⟶ X') (h' : genPt ξ' ⤳ centre z) {a : Ω} {r : R}
    (hv : ValAt ξ (z ≫ f) a r) : ValAt ξ' z (i a) r := by
  obtain ⟨h, s, rfl, rfl⟩ := hv
  exact ⟨h', (f.stalkMap (centre z)).hom s, PullReg.stalkMap_comp_genMap hD ⟨centre z, h'⟩ h s,
    (congrArg (fun t => t.hom s) (Scheme.stalkClosedPointTo_comp z f)).symm⟩

def cgerm {K : Type} [CommRing K] (x : Sp K) (c : K) : (Sp K).presheaf.stalk x :=
  (Sp K).presheaf.germ ⊤ x trivial ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c)

/- English proof (translation)
Substitute `hu` using the available equality. Establish `e` using `Scheme.germ_stalkClosedPointTo_Spec (CommRingCat.ofHom σ)`. Establish `e2` using `congrArg (fun t => t.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c)) e`. Simplify `e2` using `[cgerm]`.
-/
theorem closedPointTo_cgerm {K R : Type} [CommRing K] [CommRing R] [IsLocalRing R] (u : Sp R ⟶ Sp K)
    (σ : K →+* R) (hu : u = spMap σ) (c : K) :
    (Scheme.stalkClosedPointTo u).hom (cgerm (u (IsLocalRing.closedPoint R)) c) = σ c := by
  subst hu
  have e := Scheme.germ_stalkClosedPointTo_Spec (CommRingCat.ofHom σ)
  have e2 := congrArg (fun t => t.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c)) e
  simpa [cgerm] using e2

def cst {K : Type} [CommRing K] (s : X ⟶ Sp K) (x : X) (c : K) : X.presheaf.stalk x :=
  (s.stalkMap x).hom (cgerm (s x) c)

/- English proof (translation)
Establish `hg : genPt (ξ ≫ s) ⤳ s p.1` using `p.2.map s.continuous`. Rewrite using `[cst, genMap_stalkMap' ξ s p hg]`. Establish `e : ((Sp K).presheaf.stalkSpecializes hg).hom (cgerm (s p.1) c) = cgerm (genPt (ξ ≫ s)) c` using `congrArg (fun t => t.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c)) (TopCat.Presheaf.germ_stalkSpecializes (Sp K).presheaf (U := ⊤) trivial hg)`. Use `show (Scheme.stalkClosedPointTo (ξ ≫ s)).hom (((Sp K).presheaf.stalkSpecializes hg).hom (cgerm (s p.1) c)) = _`. Rewrite using `[e]`.

Conclude with `closedPointTo_cgerm (ξ ≫ s) (algebraMap K Ω) hs c`.
-/
theorem genMap_cst {K : Type} [Field K] [Algebra K Ω] {ξ : Sp Ω ⟶ X} (s : X ⟶ Sp K)
    (hs : ξ ≫ s = spMap (algebraMap K Ω)) (p : Cpt ξ) (c : K) :
    genMap ξ p (cst s p.1 c) = algebraMap K Ω c := by
  have hg : genPt (ξ ≫ s) ⤳ s p.1 := p.2.map s.continuous
  rw [cst, genMap_stalkMap' ξ s p hg]
  have e : ((Sp K).presheaf.stalkSpecializes hg).hom (cgerm (s p.1) c) = cgerm (genPt (ξ ≫ s)) c :=
    congrArg (fun t => t.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c))
      (TopCat.Presheaf.germ_stalkSpecializes (Sp K).presheaf (U := ⊤) trivial hg)
  show (Scheme.stalkClosedPointTo (ξ ≫ s)).hom (((Sp K).presheaf.stalkSpecializes hg).hom (cgerm (s p.1) c)) = _
  rw [e]
  exact closedPointTo_cgerm (ξ ≫ s) (algebraMap K Ω) hs c

/- English proof (translation)
Use `⟨h, cst s (centre z) c, genMap_cst s hs ⟨centre z, h⟩ c, ?_⟩` and prove the remaining obligations. Establish `e` using `congrArg (fun t => t.hom (cgerm (s (centre z)) c)) (Scheme.stalkClosedPointTo_comp z s)`. Conclude with `e.symm.trans (closedPointTo_cgerm (z ≫ s) σ hz c)`.
-/
theorem val_const {K : Type} [Field K] [Algebra K Ω] {ξ : Sp Ω ⟶ X} (s : X ⟶ Sp K)
    (hs : ξ ≫ s = spMap (algebraMap K Ω)) {R : Type} [CommRing R] [IsLocalRing R] (σ : K →+* R) (z : Sp R ⟶ X)
    (hz : z ≫ s = spMap σ) (h : genPt ξ ⤳ centre z) (c : K) : ValAt ξ z (algebraMap K Ω c) (σ c) := by
  refine ⟨h, cst s (centre z) c, genMap_cst s hs ⟨centre z, h⟩ c, ?_⟩
  have e := congrArg (fun t => t.hom (cgerm (s (centre z)) c)) (Scheme.stalkClosedPointTo_comp z s)
  exact e.symm.trans (closedPointTo_cgerm (z ≫ s) σ hz c)

/- English proof (translation)
Assemble the required witnesses or components as `⟨cst s p.1 c, genMap_cst s hs p c⟩`.
-/
theorem const_mem_regAt {K : Type} [Field K] [Algebra K Ω] {ξ : Sp Ω ⟶ X} (s : X ⟶ Sp K)
    (hs : ξ ≫ s = spMap (algebraMap K Ω)) (p : Cpt ξ) (c : K) : algebraMap K Ω c ∈ regAt ξ p :=
  ⟨cst s p.1 c, genMap_cst s hs p c⟩

/- English proof (translation)
Introduce `o ho` and use `⟨(map_ne_zero _).2 ho, const_mem_regAt s hs p o, by rw [← map_inv₀]; exact const_mem_regAt s hs p _⟩`.
-/
theorem mem_genFibre {K : Type} [Field K] [Algebra K Ω] {ξ : Sp Ω ⟶ X} (s : X ⟶ Sp K)
    (hs : ξ ≫ s = spMap (algebraMap K Ω)) (p : Cpt ξ) : p ∈ genFibre K ξ := fun o ho =>
  ⟨(map_ne_zero _).2 ho, const_mem_regAt s hs p o, by
    rw [← map_inv₀]; exact const_mem_regAt s hs p _⟩

/- English proof (translation)
Take `⟨U, hU, b, -, hq⟩` from `hVB p trivial`. Establish `hs : ∀ q : Cpt ξ, q.1 ∈ U → L q = Submodule.span (regAt ξ q) {b 0}` using `fun q hqU => by`. Use `(hq q trivial hqU).2` as an intermediate fact. Rewrite `this` using `[Set.range_unique]`. Then use the resulting hypothesis. Establish `hb0 : b 0 ≠ 0` using `(hq p trivial hU).1.ne_zero 0`.

Establish `h1 : t ∈ Submodule.span (regAt ξ p) {b 0}`. Rewrite using `[← hs p hU, ht.2]`. Conclude with `Submodule.mem_span_singleton_self t`. Establish `h2 : b 0 ∈ Submodule.span (regAt ξ p) {t}`. Rewrite using `[← ht.2, hs p hU]`.

Conclude with `Submodule.mem_span_singleton_self _`. Take `⟨u, hu⟩` from `Submodule.mem_span_singleton.1 h1`. Take `⟨v, hv⟩` from `Submodule.mem_span_singleton.1 h2`. Establish `hu' : (u : Ω) * b 0 = t` using `hu`. Establish `hv' : (v : Ω) * t = b 0` using `hv`.

Establish `huv : (v : Ω) * (u : Ω) = 1`. Establish `: (v : Ω) * (u : Ω) * b 0 = 1 * b 0` using `by rw [_root_.mul_assoc, hu', hv', _root_.one_mul]`. Conclude with `mul_right_cancel₀ hb0 this`. Establish `hu0 : (u : Ω) ≠ 0` using `right_ne_zero_of_mul_eq_one huv`. Establish `hui : (u : Ω)⁻¹ = v` using `(eq_inv_of_mul_eq_one_left huv).symm`.

Take `⟨V₁, m₁, H₁⟩` from `exists_open_mem_regAt ξ p (u : Ω) u.2`. Take `⟨V₂, m₂, H₂⟩` from `exists_open_mem_regAt ξ p (v : Ω) v.2`. Use `⟨U ⊓ V₁ ⊓ V₂, ⟨⟨hU, m₁⟩, m₂⟩, fun q hqV => ⟨ht.1, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[hs q hqV.1.1]`. Use `(span_singleton_eq_of_unitAt (u := (u : Ω)) ⟨hu0, H₁ q hqV.1.2, ?_⟩ ?_).symm` and prove the remaining obligations.

Rewrite using `[hui]`. Conclude with `H₂ q hqV.2`. Conclude with `hu'.symm`.
-/
theorem gen_near {ξ : Sp Ω ⟶ X} {L : Lat ξ Ω} (hVB : L.IsVB 1 ⊤) {p : Cpt ξ} {t : Ω} (ht : L.IsGenAt p t) :
    ∃ V : X.Opens, p.1 ∈ V ∧ ∀ q : Cpt ξ, q.1 ∈ V → L.IsGenAt q t := by
  obtain ⟨U, hU, b, -, hq⟩ := hVB p trivial
  have hs : ∀ q : Cpt ξ, q.1 ∈ U → L q = Submodule.span (regAt ξ q) {b 0} := fun q hqU => by
    have := (hq q trivial hqU).2
    rwa [Set.range_unique] at this
  have hb0 : b 0 ≠ 0 := (hq p trivial hU).1.ne_zero 0
  have h1 : t ∈ Submodule.span (regAt ξ p) {b 0} := by
    rw [← hs p hU, ht.2]; exact Submodule.mem_span_singleton_self t
  have h2 : b 0 ∈ Submodule.span (regAt ξ p) {t} := by
    rw [← ht.2, hs p hU]; exact Submodule.mem_span_singleton_self _
  obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.1 h1
  obtain ⟨v, hv⟩ := Submodule.mem_span_singleton.1 h2
  have hu' : (u : Ω) * b 0 = t := hu
  have hv' : (v : Ω) * t = b 0 := hv
  have huv : (v : Ω) * (u : Ω) = 1 := by
    have : (v : Ω) * (u : Ω) * b 0 = 1 * b 0 := by rw [_root_.mul_assoc, hu', hv', _root_.one_mul]
    exact mul_right_cancel₀ hb0 this
  have hu0 : (u : Ω) ≠ 0 := right_ne_zero_of_mul_eq_one huv
  have hui : (u : Ω)⁻¹ = v := (eq_inv_of_mul_eq_one_left huv).symm
  obtain ⟨V₁, m₁, H₁⟩ := exists_open_mem_regAt ξ p (u : Ω) u.2
  obtain ⟨V₂, m₂, H₂⟩ := exists_open_mem_regAt ξ p (v : Ω) v.2
  refine ⟨U ⊓ V₁ ⊓ V₂, ⟨⟨hU, m₁⟩, m₂⟩, fun q hqV => ⟨ht.1, ?_⟩⟩
  rw [hs q hqV.1.1]
  refine (span_singleton_eq_of_unitAt (u := (u : Ω)) ⟨hu0, H₁ q hqV.1.2, ?_⟩ ?_).symm
  · rw [hui]; exact H₂ q hqV.2
  · exact hu'.symm

/- English proof (translation)
Establish `h : t ∈ L p` using `by rw [ht.2]; exact Submodule.mem_span_singleton_self t`. Rewrite `h` using `[h1.2]`. Take `⟨r, hr⟩` from `Submodule.mem_span_singleton.1 h`. Establish `: (r : Ω) * 1 = t` using `hr`. Rewrite `this` using `[_root_.mul_one]`.

Rewrite using `[← this]`. Conclude with `r.2`.
-/
theorem reg_of_two_gens {ξ : Sp Ω ⟶ X} {L : Lat ξ Ω} {p : Cpt ξ} {t : Ω} (h1 : L.IsGenAt p 1)
    (ht : L.IsGenAt p t) : t ∈ regAt ξ p := by
  have h : t ∈ L p := by rw [ht.2]; exact Submodule.mem_span_singleton_self t
  rw [h1.2] at h
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 h
  have : (r : Ω) * 1 = t := hr
  rw [_root_.mul_one] at this
  rw [← this]
  exact r.2

/- English proof (translation)
The claim follows from `h (show IsLocalRing.closedPoint ℂ ∈ (⊤ : (Sp ℂ).Opens) from trivial)`.
-/
theorem centre_mem {z : Sp ℂ ⟶ X} {U : X.Opens} (h : ⊤ ≤ z ⁻¹ᵁ U) : centre z ∈ U :=
  h (show IsLocalRing.closedPoint ℂ ∈ (⊤ : (Sp ℂ).Opens) from trivial)

/- English proof (translation)
Rewrite using `[GlobalTheory.top_le_preimage_iff_mem]`. Establish `: (default : PrimeSpectrum ℂ) = IsLocalRing.closedPoint ℂ` using `Subsingleton.elim (α := PrimeSpectrum ℂ) _ _`. Rewrite using `[this]`. Conclude with `h`.
-/
theorem top_le_of_centre_mem {z : Sp ℂ ⟶ X} {U : X.Opens} (h : centre z ∈ U) : ⊤ ≤ z ⁻¹ᵁ U := by
  rw [GlobalTheory.top_le_preimage_iff_mem]
  have : (default : PrimeSpectrum ℂ) = IsLocalRing.closedPoint ℂ := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
  rw [this]
  exact h

/- English proof (translation)
Introduce `U g`. Take `⟨h1, h2⟩` from `h (f ⁻¹ᵁ U) ((f.app U).hom g)`. Establish `e : {b ∈ B | ⊤ ≤ (y b ≫ f) ⁻¹ᵁ U} = {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ (f ⁻¹ᵁ U)}`. Use extensionality with `b`. Simplify using `only [Set.mem_setOf_eq, GlobalTheory.top_le_preimage_comp]`.

Rewrite using `[e]`. Conclude with `⟨h1, h2.congr fun b _ => (GlobalTheory.valAt'_comp (y b) f U g).symm⟩`.
-/
theorem isHolTo_comp {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {B : Set V} {y : V → (Sp ℂ ⟶ X')}
    (f : X' ⟶ X) (h : IsHolTo B y) : IsHolTo B (fun b => y b ≫ f) := by
  intro U g
  obtain ⟨h1, h2⟩ := h (f ⁻¹ᵁ U) ((f.app U).hom g)
  have e : {b ∈ B | ⊤ ≤ (y b ≫ f) ⁻¹ᵁ U} = {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ (f ⁻¹ᵁ U)} := by
    ext b
    simp only [Set.mem_setOf_eq, GlobalTheory.top_le_preimage_comp]
  rw [e]
  exact ⟨h1, h2.congr fun b _ => (GlobalTheory.valAt'_comp (y b) f U g).symm⟩

/- English proof (translation)
The claim follows from `Spec.map_id _`.
-/
theorem spMap_id (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 _ := Spec.map_id _

/- English proof (translation)
Introduce `m B y hB hy hs b₀ hb₀ hy₀`. Take `⟨V, hV, hq⟩` from `gen_near hVB ht`. Establish `hol` using `isHolTo_comp f hy`. Establish `hyb : ∀ b ∈ B, (y b ≫ f) ≫ s = spMap σ` using `fun b hb => by`. Rewrite using `[Category.assoc, hc, ← Category.assoc, hs b hb, spMap_id, Category.id_comp]`.

Take `⟨ε, g, hε, hd, hg, H⟩` from `hE m B (fun b => y b ≫ f) hB hol hyb b₀ hb₀ (by simp only [hy₀])`. Establish `hopen` using `(hol V (0 : Γ(X, V))).1`. Establish `hb₀' : b₀ ∈ {b ∈ B | ⊤ ≤ (y b ≫ f) ⁻¹ᵁ V}` using `⟨hb₀, top_le_of_centre_mem (by rw [hy₀]; exact hV)⟩`. Take `⟨δ, hδ, hball⟩` from `Metric.isOpen_iff.1 hopen b₀ hb₀'`. Use `⟨min ε δ, g, lt_min hε hδ, hd.mono (ball_subset_ball (min_le_left _ _)), hg, ?_⟩` and prove the remaining obligations.

Introduce and unpack `b ⟨hbB, hbε⟩ hW r hr`. Establish `hbV` using `(hball (ball_subset_ball (min_le_right _ _) hbε)).2`. Establish `h' : genPt ξ' ⤳ centre (y b)` using `hr.choose`. Establish `hcen : genPt ξ ⤳ centre (y b ≫ f)` using `hD.specializes ⟨centre (y b), h'⟩`. Establish `hW' : ⊤ ≤ (y b ≫ f) ⁻¹ᵁ W` using `(GlobalTheory.top_le_preimage_comp _ _ _).2 hW`.

Take `⟨s₀, hs₀⟩` from `reg_of_two_gens (hW1 ⟨centre (y b ≫ f), hcen⟩ (centre_mem hW')) (hq ⟨centre (y b ≫ f), hcen⟩ (centre_mem hbV))`. Establish `hv : ValAt ξ (y b ≫ f) t ((Scheme.stalkClosedPointTo (y b ≫ f)).hom s₀)` using `⟨hcen, s₀, hs₀, rfl⟩`. Establish `e` using `val_eq hξ' (val_pull hD (y b) h' hv) hr`. Establish `H'` using `H b ⟨hbB, ball_subset_ball (min_le_left _ _) hbε⟩ hW' _ hv`. Rewrite `H'` using `[e]`.

Conclude with `H'`.
-/
theorem extends_pull {K : Type} [Field K] {σ : K →+* ℂ} {s : X ⟶ Sp K} {s' : X' ⟶ Sp ℂ} {ξ : Sp Ω ⟶ X}
    {ξ' : Sp Ω' ⟶ X'} {f : X' ⟶ X} {i : Ω →+* Ω'} (hc : f ≫ s = s' ≫ spMap σ) (hD : Dominates ξ' ξ f i)
    (hξ' : IsCptGen ξ') {L : Lat ξ Ω} (hVB : L.IsVB 1 ⊤) {W : X.Opens} {F : (Sp ℂ ⟶ X) → ℂ}
    (hW1 : ∀ p : Cpt ξ, p.1 ∈ W → L.IsGenAt p 1) {t : Ω} (x' : Sp ℂ ⟶ X') (h : genPt ξ ⤳ centre (x' ≫ f))
    (ht : L.IsGenAt ⟨centre (x' ≫ f), h⟩ t) (hE : ExtendsUnitAt s σ ξ W F t (x' ≫ f)) :
    ExtendsUnitAt s' (RingHom.id ℂ) ξ' (f ⁻¹ᵁ W) (fun y => F (y ≫ f)) (i t) x' := by
  intro m B y hB hy hs b₀ hb₀ hy₀
  obtain ⟨V, hV, hq⟩ := gen_near hVB ht
  have hol := isHolTo_comp f hy
  have hyb : ∀ b ∈ B, (y b ≫ f) ≫ s = spMap σ := fun b hb => by
    rw [Category.assoc, hc, ← Category.assoc, hs b hb, spMap_id, Category.id_comp]
  obtain ⟨ε, g, hε, hd, hg, H⟩ := hE m B (fun b => y b ≫ f) hB hol hyb b₀ hb₀ (by simp only [hy₀])
  have hopen := (hol V (0 : Γ(X, V))).1
  have hb₀' : b₀ ∈ {b ∈ B | ⊤ ≤ (y b ≫ f) ⁻¹ᵁ V} :=
    ⟨hb₀, top_le_of_centre_mem (by rw [hy₀]; exact hV)⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hopen b₀ hb₀'
  refine ⟨min ε δ, g, lt_min hε hδ, hd.mono (ball_subset_ball (min_le_left _ _)), hg, ?_⟩
  rintro b ⟨hbB, hbε⟩ hW r hr
  have hbV := (hball (ball_subset_ball (min_le_right _ _) hbε)).2
  have h' : genPt ξ' ⤳ centre (y b) := hr.choose
  have hcen : genPt ξ ⤳ centre (y b ≫ f) := hD.specializes ⟨centre (y b), h'⟩
  have hW' : ⊤ ≤ (y b ≫ f) ⁻¹ᵁ W := (GlobalTheory.top_le_preimage_comp _ _ _).2 hW
  obtain ⟨s₀, hs₀⟩ := reg_of_two_gens (hW1 ⟨centre (y b ≫ f), hcen⟩ (centre_mem hW'))
    (hq ⟨centre (y b ≫ f), hcen⟩ (centre_mem hbV))
  have hv : ValAt ξ (y b ≫ f) t ((Scheme.stalkClosedPointTo (y b ≫ f)).hom s₀) := ⟨hcen, s₀, hs₀, rfl⟩
  have e := val_eq hξ' (val_pull hD (y b) h' hv) hr
  have H' := H b ⟨hbB, ball_subset_ball (min_le_left _ _) hbε⟩ hW' _ hv
  rw [e] at H'
  exact H'

/- English proof (translation)
Introduce `K _ _ σ X s Ω _ _ ξ h1 h2 h3`. Use `letI : Algebra K ℂ := σ.toAlgebra`. Conclude with `cpt_base_change_dominates K ℂ s ξ h1 h2 h3`.
-/
theorem cpt_base_change : ∀ (K : Type) [Field K] [CharZero K] (σ : K →+* ℂ) (X : Scheme.{0}) (s : X ⟶ Sp K)
    (Ω : Type) [Field Ω] [Algebra K Ω] (ξ : Sp Ω ⟶ X), ξ ≫ s = spMap (algebraMap K Ω) → IsCptGen ξ →
    ConstClosed K Ω → ∃ (Ω' : Type) (_ : Field Ω') (_ : Algebra ℂ Ω') (i : Ω →+* Ω')
      (ξ' : Sp Ω' ⟶ pullback s (spMap σ)), ξ' ≫ pullback.snd s (spMap σ) = spMap (algebraMap ℂ Ω') ∧
      Dominates ξ' ξ (pullback.fst s (spMap σ)) i ∧ IsCptGen ξ' ∧
      ∀ p' : ↥(pullback s (spMap σ)), genPt ξ ⤳ pullback.fst s (spMap σ) p' → genPt ξ' ⤳ p' := by
  intro K _ _ σ X s Ω _ _ ξ h1 h2 h3
  letI : Algebra K ℂ := σ.toAlgebra
  exact cpt_base_change_dominates K ℂ s ξ h1 h2 h3

/- English proof (translation)
Introduce `a ha` and use `by have hi := ha.isIntegral obtain ⟨c, rfl⟩ := minpoly.mem_range_of_degree_eq_one ℂ a (IsAlgClosed.degree_eq_one_of_irreducible ℂ (minpoly.irreducible hi)) exact ⟨c, 1, one_ne_zero, by simp⟩`.
-/
theorem constClosed_complex (Ω' : Type) [Field Ω'] [Algebra ℂ Ω'] : ConstClosed ℂ Ω' := fun a ha => by
  have hi := ha.isIntegral
  obtain ⟨c, rfl⟩ := minpoly.mem_range_of_degree_eq_one ℂ a
    (IsAlgClosed.degree_eq_one_of_irreducible ℂ (minpoly.irreducible hi))
  exact ⟨c, 1, one_ne_zero, by simp⟩

end GlobalTheory.CompanionTheory.Ar.Flat.GagaRat

namespace GlobalTheory.CompanionTheory.Ar.Flat

open GagaRat in

/- English proof (translation)
Introduce `hG K _ σ X s Ω _ _ ξ L W F hP hS hξs hξ hCC hVB hW hW1 hext`. Use `haveI : CharZero K := σ.charZero`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective`. Take `⟨Ω', _, _, i, ξ', h1, hD, hξ', hsp⟩` from `cpt_base_change K σ X s Ω ξ hξs hξ hCC`. Establish `hc : pullback.fst s (spMap σ) ≫ s = pullback.snd s (spMap σ) ≫ spMap σ` using `pullback.condition`.

Generalize the expression as in `hf : pullback.fst s (spMap σ) = f at *`. Generalize the expression as in `hs' : pullback.snd s (spMap σ) = s' at *`. Establish `hpb : IsPullback f s' s (spMap σ)`. Rewrite using `[← hf, ← hs']`. Conclude with `IsPullback.of_hasPullback s (spMap σ)`.

Establish `hP' : IsProper s'` using `MorphismProperty.of_isPullback hpb hP`. Establish `hS' : Smooth s'` using `MorphismProperty.of_isPullback hpb hS`. Establish `hVB' : (L.pull ξ' f i.toAddMonoidHom).IsVB 1 ⊤`. Introduce `p' _`. Take `⟨U, hU, b, hb, hq⟩` from `hVB ⟨f p'.1, hD.specializes p'⟩ trivial`.

Establish `hb0 : b 0 ≠ 0` using `(hq ⟨f p'.1, hD.specializes p'⟩ trivial hU).1.ne_zero 0`. Establish `hib : i (b 0) ≠ 0` using `(map_ne_zero i).2 hb0`. Use `⟨f ⁻¹ᵁ U, hU, fun k => i (b k), ?_, fun q' _ hq' => ?_⟩` and prove the remaining obligations. Rewrite using `[Set.range_unique]`. Use `eq_top_iff.2 fun z _ => Submodule.mem_span_singleton.2 ⟨z / i (b default), ?_⟩` and prove the remaining obligations.

Conclude with `div_mul_cancel₀ z hib`. Conclude with `GlobalTheory.T.lattice_basis_pullback_dominant X Ω ξ _ Ω' ξ' f i Ω Ω' i.toAddMonoidHom hD (fun a e => by simp) L 1 b q' (hD.specializes q') (LinearIndependent.of_subsingleton 0 hib) (hq ⟨f q'.1, hD.specializes q'⟩ trivial hq')`. Establish `hW' : genPt ξ' ∈ f ⁻¹ᵁ W` using `by show f (genPt ξ') ∈ W`. Rewrite using `[hD.map_genPt]`. Conclude with `hW`.

Establish `hW1' : ∀ p' : Cpt ξ', p'.1 ∈ f ⁻¹ᵁ W → (L.pull ξ' f i.toAddMonoidHom).IsGenAt p' 1` using `fun p' hp' => by`. Take `⟨h, -, hg⟩` from `pull_reg_and_gen X Ω ξ _ Ω' ξ' f i hD p'`. Simplify using `using hg L 1 (hW1 ⟨f p'.1, h⟩ hp')`. Establish `hext' : ∀ (x : Sp ℂ ⟶ _) (h : genPt ξ' ⤳ centre x), x ≫ s' = spMap (RingHom.id ℂ) → ∃ t : Ω', (L.pull ξ' f i.toAddMonoidHom).IsGenAt ⟨centre x, h⟩ t ∧ ExtendsUnitAt s' (RingHom.id ℂ) ξ' (f ⁻¹ᵁ W) (fun y => F (y ≫ f)) t x`. Introduce `x h hx`.

Establish `hxs : (x ≫ f) ≫ s = spMap σ`. Rewrite using `[Category.assoc, hc, ← Category.assoc, hx, spMap_id, Category.id_comp]`. Establish `hcx : genPt ξ ⤳ centre (x ≫ f)` using `hD.specializes ⟨centre x, h⟩`. Take `⟨t, ht, hE⟩` from `hext (x ≫ f) hcx hxs`. Take `⟨h2, -, hg⟩` from `pull_reg_and_gen X Ω ξ _ Ω' ξ' f i hD ⟨centre x, h⟩`.

Conclude with `⟨i t, hg L t ht, extends_pull hc hD hξ' hVB hW1 x hcx ht hE⟩`. Take `⟨f', κ, hκ, hgen, hval⟩` from `GlobalTheory.T.gaga_line_generator_complex hG _ s' Ω' ξ' (L.pull ξ' f i.toAddMonoidHom) (f ⁻¹ᵁ W) (fun y => F (y ≫ f)) hP' hS' h1 hξ' (constClosed_complex Ω') hVB' hW' hW1' hext'`. Use `letI : Algebra K ℂ := σ.toAlgebra`. Use `haveI : IsProper s := hP`. Take `⟨t, c, hgt, hft⟩` from `GlobalTheory.T.proper_model_generic_fibre_compare X Ω ξ K s _ Ω' ξ' f i ℂ s' hξs (algebraMap K Ω).injective (algebraMap K ℂ).injective hpb h1 hD hξ hξ' hCC L f' (fun p _ => by`.

Take `⟨U, hU, b, hb, hq⟩` from `hVB p trivial`. Conclude with `⟨U, hU, b, hb, fun q _ hqU => hq q trivial hqU⟩) hgen`. Establish `hgt' : ∀ p : Cpt ξ, L.IsGenAt p t` using `fun p => hgt p (mem_genFibre s hξs p)`. Establish `hf0 : f' ≠ 0` using `(hgen ⟨genPt ξ', specializes_rfl⟩).1`. Establish `hc0 : c ≠ 0`.

Introduce and unpack `rfl`. Conclude with `hf0 (by rw [hft]; simp)`. Use `⟨t, κ / c, div_ne_zero hκ hc0, hgt', fun y hy hyW hyc => ?_⟩` and prove the remaining obligations. Establish `hlift : y ≫ s = 𝟙 _ ≫ spMap σ` using `by rw [hy, Category.id_comp]`. Take `⟨y', hy'f, hy's⟩ : ∃ y' : Sp ℂ ⟶ _, y' ≫ f = y ∧ y' ≫ s' = 𝟙 _` from `⟨hpb.lift y (𝟙 _) hlift, hpb.lift_fst _ _ _, hpb.lift_snd _ _ _⟩`.

Substitute `hy'f` using the available equality. Establish `hc' : genPt ξ' ⤳ centre y'` using `hsp _ hyc`. Establish `hys' : y' ≫ s' = spMap (RingHom.id ℂ)` using `by rw [hy's, spMap_id]`. Establish `hv1` using `hval y' hys' ((GlobalTheory.top_le_preimage_comp _ _ _).1 hyW) hc'`. Take `⟨s₀, hs₀⟩` from `reg_of_two_gens (hW1 ⟨centre (y' ≫ f), hyc⟩ (centre_mem hyW)) (hgt' ⟨centre (y' ≫ f), hyc⟩)`.

Establish `hv : ValAt ξ (y' ≫ f) t ((Scheme.stalkClosedPointTo (y' ≫ f)).hom s₀)` using `⟨hyc, s₀, hs₀, rfl⟩`. Establish `hv'` using `val_pull hD y' hc' hv`. Establish `hcv` using `val_const s' h1 (RingHom.id ℂ) y' hys' hc' c`. Establish `hm` using `val_mul' hcv hv'`. Rewrite `hm` using `[← hft]`.

Establish `e` using `val_eq hξ' hm hv1`. Establish `e' : (Scheme.stalkClosedPointTo (y' ≫ f)).hom s₀ = κ / c * F (y' ≫ f)`. Simplify using `only [RingHom.id_apply] at e`. Clear the denominators using the available nonvanishing facts. Take the linear combination `e`.

Rewrite using `[← e']`. Conclude with `hv`.
-/
theorem gaga_rat : GagaSections → ∀ (K : Type) [Field K] (σ : K →+* ℂ) (X : Scheme.{0}) (s : X ⟶ Sp K) (Ω : Type) [Field Ω] [Algebra K Ω] (ξ : Sp Ω ⟶ X) (L : Lat ξ Ω) (W : X.Opens) (F : (Sp ℂ ⟶ X) → ℂ), IsProper s → Smooth s → ξ ≫ s = spMap (algebraMap K Ω) → IsCptGen ξ → ConstClosed K Ω → L.IsVB 1 ⊤ → genPt ξ ∈ W → (∀ p : Cpt ξ, p.1 ∈ W → L.IsGenAt p 1) → (∀ (x : Sp ℂ ⟶ X) (h : genPt ξ ⤳ centre x), x ≫ s = spMap σ → ∃ t : Ω, L.IsGenAt ⟨centre x, h⟩ t ∧ ExtendsUnitAt s σ ξ W F t x) → ∃ (f : Ω) (κ : ℂ), κ ≠ 0 ∧ (∀ p : Cpt ξ, L.IsGenAt p f) ∧ ∀ y : Sp ℂ ⟶ X, y ≫ s = spMap σ → ⊤ ≤ y ⁻¹ᵁ W → genPt ξ ⤳ centre y → ValAt ξ y f (κ * F y) := by
  intro hG K _ σ X s Ω _ _ ξ L W F hP hS hξs hξ hCC hVB hW hW1 hext
  haveI : CharZero K := σ.charZero
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  obtain ⟨Ω', _, _, i, ξ', h1, hD, hξ', hsp⟩ := cpt_base_change K σ X s Ω ξ hξs hξ hCC
  have hc : pullback.fst s (spMap σ) ≫ s = pullback.snd s (spMap σ) ≫ spMap σ := pullback.condition
  generalize hf : pullback.fst s (spMap σ) = f at *
  generalize hs' : pullback.snd s (spMap σ) = s' at *
  have hpb : IsPullback f s' s (spMap σ) := by
    rw [← hf, ← hs']; exact IsPullback.of_hasPullback s (spMap σ)
  have hP' : IsProper s' := MorphismProperty.of_isPullback hpb hP
  have hS' : Smooth s' := MorphismProperty.of_isPullback hpb hS
  have hVB' : (L.pull ξ' f i.toAddMonoidHom).IsVB 1 ⊤ := by
    intro p' _
    obtain ⟨U, hU, b, hb, hq⟩ := hVB ⟨f p'.1, hD.specializes p'⟩ trivial
    have hb0 : b 0 ≠ 0 := (hq ⟨f p'.1, hD.specializes p'⟩ trivial hU).1.ne_zero 0
    have hib : i (b 0) ≠ 0 := (map_ne_zero i).2 hb0
    refine ⟨f ⁻¹ᵁ U, hU, fun k => i (b k), ?_, fun q' _ hq' => ?_⟩
    · rw [Set.range_unique]
      refine eq_top_iff.2 fun z _ => Submodule.mem_span_singleton.2 ⟨z / i (b default), ?_⟩
      exact div_mul_cancel₀ z hib
    · exact GlobalTheory.T.lattice_basis_pullback_dominant X Ω ξ _ Ω' ξ' f i Ω Ω' i.toAddMonoidHom hD
        (fun a e => by simp) L 1 b q' (hD.specializes q')
        (LinearIndependent.of_subsingleton 0 hib) (hq ⟨f q'.1, hD.specializes q'⟩ trivial hq')
  have hW' : genPt ξ' ∈ f ⁻¹ᵁ W := by
    show f (genPt ξ') ∈ W
    rw [hD.map_genPt]; exact hW
  have hW1' : ∀ p' : Cpt ξ', p'.1 ∈ f ⁻¹ᵁ W → (L.pull ξ' f i.toAddMonoidHom).IsGenAt p' 1 := fun p' hp' => by
    obtain ⟨h, -, hg⟩ := pull_reg_and_gen X Ω ξ _ Ω' ξ' f i hD p'
    simpa using hg L 1 (hW1 ⟨f p'.1, h⟩ hp')
  have hext' : ∀ (x : Sp ℂ ⟶ _) (h : genPt ξ' ⤳ centre x), x ≫ s' = spMap (RingHom.id ℂ) →
      ∃ t : Ω', (L.pull ξ' f i.toAddMonoidHom).IsGenAt ⟨centre x, h⟩ t ∧
        ExtendsUnitAt s' (RingHom.id ℂ) ξ' (f ⁻¹ᵁ W) (fun y => F (y ≫ f)) t x := by
    intro x h hx
    have hxs : (x ≫ f) ≫ s = spMap σ := by
      rw [Category.assoc, hc, ← Category.assoc, hx, spMap_id, Category.id_comp]
    have hcx : genPt ξ ⤳ centre (x ≫ f) := hD.specializes ⟨centre x, h⟩
    obtain ⟨t, ht, hE⟩ := hext (x ≫ f) hcx hxs
    obtain ⟨h2, -, hg⟩ := pull_reg_and_gen X Ω ξ _ Ω' ξ' f i hD ⟨centre x, h⟩
    exact ⟨i t, hg L t ht, extends_pull hc hD hξ' hVB hW1 x hcx ht hE⟩
  obtain ⟨f', κ, hκ, hgen, hval⟩ := GlobalTheory.T.gaga_line_generator_complex hG _ s' Ω' ξ' (L.pull ξ' f i.toAddMonoidHom) (f ⁻¹ᵁ W)
    (fun y => F (y ≫ f)) hP' hS' h1 hξ' (constClosed_complex Ω') hVB' hW' hW1' hext'
  letI : Algebra K ℂ := σ.toAlgebra
  haveI : IsProper s := hP
  obtain ⟨t, c, hgt, hft⟩ := GlobalTheory.T.proper_model_generic_fibre_compare X Ω ξ K s _ Ω' ξ' f i ℂ s' hξs (algebraMap K Ω).injective
    (algebraMap K ℂ).injective hpb h1 hD hξ hξ' hCC L f'
    (fun p _ => by
      obtain ⟨U, hU, b, hb, hq⟩ := hVB p trivial
      exact ⟨U, hU, b, hb, fun q _ hqU => hq q trivial hqU⟩) hgen
  have hgt' : ∀ p : Cpt ξ, L.IsGenAt p t := fun p => hgt p (mem_genFibre s hξs p)
  have hf0 : f' ≠ 0 := (hgen ⟨genPt ξ', specializes_rfl⟩).1
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hf0 (by rw [hft]; simp)
  refine ⟨t, κ / c, div_ne_zero hκ hc0, hgt', fun y hy hyW hyc => ?_⟩
  have hlift : y ≫ s = 𝟙 _ ≫ spMap σ := by rw [hy, Category.id_comp]
  obtain ⟨y', hy'f, hy's⟩ : ∃ y' : Sp ℂ ⟶ _, y' ≫ f = y ∧ y' ≫ s' = 𝟙 _ :=
    ⟨hpb.lift y (𝟙 _) hlift, hpb.lift_fst _ _ _, hpb.lift_snd _ _ _⟩
  subst hy'f
  have hc' : genPt ξ' ⤳ centre y' := hsp _ hyc
  have hys' : y' ≫ s' = spMap (RingHom.id ℂ) := by rw [hy's, spMap_id]
  have hv1 := hval y' hys' ((GlobalTheory.top_le_preimage_comp _ _ _).1 hyW) hc'
  obtain ⟨s₀, hs₀⟩ := reg_of_two_gens (hW1 ⟨centre (y' ≫ f), hyc⟩ (centre_mem hyW)) (hgt' ⟨centre (y' ≫ f), hyc⟩)
  have hv : ValAt ξ (y' ≫ f) t ((Scheme.stalkClosedPointTo (y' ≫ f)).hom s₀) := ⟨hyc, s₀, hs₀, rfl⟩
  have hv' := val_pull hD y' hc' hv
  have hcv := val_const s' h1 (RingHom.id ℂ) y' hys' hc' c
  have hm := val_mul' hcv hv'
  rw [← hft] at hm
  have e := val_eq hξ' hm hv1
  have e' : (Scheme.stalkClosedPointTo (y' ≫ f)).hom s₀ = κ / c * F (y' ≫ f) := by
    simp only [RingHom.id_apply] at e
    field_simp
    linear_combination e
  rw [← e']
  exact hv

end GlobalTheory.CompanionTheory.Ar.Flat
