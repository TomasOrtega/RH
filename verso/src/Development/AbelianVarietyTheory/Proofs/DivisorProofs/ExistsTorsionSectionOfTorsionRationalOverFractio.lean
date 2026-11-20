import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingDeterminedAtGenericPoint
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsFiniteEtaleCoverConstantTorsion
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsIffOfIsGrpPullbackComm
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemeGlueAffineCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionSectionExtendsAbLocus
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsConst

/- English proof (translation)
Take `⟨φ, rfl⟩` from `Spec.map_surjective τ`. Establish `hφ : Function.Injective φ.hom`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`. Establish `h1 : PrimeSpectrum.comap φ.hom w = ⊥` using `hw`.

Establish `h2 : a ∈ (PrimeSpectrum.comap φ.hom w).asIdeal` using `by show φ.hom a ∈ (w : PrimeSpectrum k).asIdeal`. Rewrite using `[ha]`. Conclude with `Ideal.zero_mem _`. Rewrite `h2` using `[h1]`. Conclude with `h2`.

Use `⟨IsFractionRing.lift hφ, ?_⟩` and prove the remaining obligations. Rewrite using `[← Spec.map_comp]`. Use `congr 1`. Use extensionality with `a`. Simplify using the standard rewrite rules.
-/
theorem exists_factor_generic {R : Type} [CommRing R] [IsDomain R] {k : Type} [Field k] (τ : Sp k ⟶ Sp R)
    (w : Sp k) (hw : τ w = (⊥ : PrimeSpectrum R)) : ∃ κ : FractionRing R →+* k, τ = spMap κ ≫ jK R := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective τ
  have hφ : Function.Injective φ.hom := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have h1 : PrimeSpectrum.comap φ.hom w = ⊥ := hw
    have h2 : a ∈ (PrimeSpectrum.comap φ.hom w).asIdeal := by
      show φ.hom a ∈ (w : PrimeSpectrum k).asIdeal
      rw [ha]; exact Ideal.zero_mem _
    rw [h1] at h2
    exact h2
  refine ⟨IsFractionRing.lift hφ, ?_⟩
  rw [← Spec.map_comp]
  congr 1
  ext a
  simp

/- English proof (translation)
Take `⟨x₀, h₀⟩` from `h K κ x hx`. Set `ρ : Over.mk (spMap κ ≫ jK R) ⟶ Over.mk (jK R)` to `Over.homMk (spMap κ) rfl`. Establish `e₀ : x = ρ ≫ x₀` using `Over.OverMorphism.ext h₀`. Establish `hfl : Flat (spMap κ)`. Use `letI := κ.toAlgebra`.

Conclude with `(HasRingHomProperty.Spec_iff (P := @Flat)).2 (RingHom.flat_algebraMap_iff.2 inferInstance)`. Establish `hsu : Surjective (spMap κ)` using `⟨fun p => ⟨Classical.arbitrary _, Subsingleton.elim (α := Sp (FractionRing R)) _ _⟩⟩`. Establish `hepi : Epi ρ.left` using `Flat.epi_of_flat_of_surjective (spMap κ)`. Establish `hx₀ : x₀ ^ n = 1`. Establish `: ρ ≫ x₀ ^ n = ρ ≫ 1` using `by rw [MonObj.comp_pow, ← e₀, hx, MonObj.comp_one]`.

Conclude with `Over.OverMorphism.ext ((cancel_epi ρ.left).1 congr(($this).left))`. Establish `hT : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp R)` using `fun p => by`. Use `⟨inferInstance, ?_⟩` and prove the remaining obligations. Establish `: (PrimeSpectrum.asIdeal p).IsPrime` using `PrimeSpectrum.isPrime p`. Establish `h` using `StructureSheaf.IsLocalization.to_stalk R p`.

Conclude with `@isIntegrallyClosed_of_isLocalization R ((Spec.structureSheaf R).presheaf.stalk p) _ _ (_) _ _ (PrimeSpectrum.asIdeal p).primeCompl (Ideal.primeCompl_le_nonZeroDivisors _) h`. Establish `j₁ : IsPreimmersion (jK R)` using `IsPreimmersion.of_isLocalization (nonZeroDivisors R)`. Establish `j₂ : Flat (jK R)` using `(HasRingHomProperty.Spec_iff (P := @Flat)).2 (RingHom.flat_algebraMap_iff.2 inferInstance)`. Establish `j₃ : IsDominant (jK R)` using `⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by`. Introduce `a ha`.

Establish `: a = 0` using `IsFractionRing.injective R (FractionRing R) (ha.trans (map_zero _).symm)`. Rewrite using `[this]`. Conclude with `Ideal.zero_mem _)⟩`. Establish `hp : IsProper A.hom` using `hA.proper`. Take `⟨s, hs₁, hs₂⟩` from `exists_section_of_pow_eq_one hT (jK R) A n hn _ x₀ hx₀ (𝟙 _) (Category.id_comp _)`.

Set `σ : 𝟙_ (Over (Sp R)) ⟶ A` to `Over.homMk s hs₁`. Establish `e₁ : toUnit (Over.mk (jK R)) ≫ σ = x₀`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[Over.comp_left, GlobalTheory.ObjPull.toUnit_left']`. Conclude with `hs₂.trans (Category.id_comp _)`.

Use `⟨σ, ?_, ?_⟩` and prove the remaining obligations. Establish `: toUnit (Over.mk (jK R)) ≫ σ ^ n = toUnit (Over.mk (jK R)) ≫ 1`. Rewrite using `[MonObj.comp_pow, e₁, hx₀, MonObj.comp_one]`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Establish `h2` using `congr(($this).left)`.

Rewrite `h2` using `[Over.comp_left, Over.comp_left, GlobalTheory.ObjPull.toUnit_left']`. Establish `: AlgebraicGeometry.IsReduced (𝟙_ (Over (Sp R))).left` using `inferInstanceAs (AlgebraicGeometry.IsReduced (Sp R))`. Conclude with `ext_of_isDominant_of_isSeparated A.hom (by rw [Over.w, Over.w]) (jK R) h2`. Rewrite using `[e₀, ← e₁, ← Category.assoc, comp_toUnit]`.
-/
theorem exists_section_generic {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] {n : ℕ} (hA : IsAbelianScheme A) (hn : IsUnit (n : Γ(Sp R, ⊤)))
    (h : TorsRat A n) {K : Type} [Field K] [IsAlgClosed K] (κ : FractionRing R →+* K)
    (x : Over.mk (spMap κ ≫ jK R) ⟶ A) (hx : x ^ n = 1) :
    ∃ σ : 𝟙_ (Over (Sp R)) ⟶ A, σ ^ n = 1 ∧ toUnit _ ≫ σ = x := by
  obtain ⟨x₀, h₀⟩ := h K κ x hx
  let ρ : Over.mk (spMap κ ≫ jK R) ⟶ Over.mk (jK R) := Over.homMk (spMap κ) rfl
  have e₀ : x = ρ ≫ x₀ := Over.OverMorphism.ext h₀
  have hfl : Flat (spMap κ) := by
    letI := κ.toAlgebra
    exact (HasRingHomProperty.Spec_iff (P := @Flat)).2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  have hsu : Surjective (spMap κ) := ⟨fun p => ⟨Classical.arbitrary _, Subsingleton.elim (α := Sp (FractionRing R)) _ _⟩⟩
  have hepi : Epi ρ.left := Flat.epi_of_flat_of_surjective (spMap κ)
  have hx₀ : x₀ ^ n = 1 := by
    have : ρ ≫ x₀ ^ n = ρ ≫ 1 := by rw [MonObj.comp_pow, ← e₀, hx, MonObj.comp_one]
    exact Over.OverMorphism.ext ((cancel_epi ρ.left).1 congr(($this).left))
  have hT : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp R) := fun p => by
    refine ⟨inferInstance, ?_⟩
    have : (PrimeSpectrum.asIdeal p).IsPrime := PrimeSpectrum.isPrime p
    have h := StructureSheaf.IsLocalization.to_stalk R p
    exact @isIntegrallyClosed_of_isLocalization R ((Spec.structureSheaf R).presheaf.stalk p) _ _ (_) _ _
      (PrimeSpectrum.asIdeal p).primeCompl (Ideal.primeCompl_le_nonZeroDivisors _) h
  have j₁ : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have j₂ : Flat (jK R) :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  have j₃ : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
    intro a ha
    have : a = 0 := IsFractionRing.injective R (FractionRing R) (ha.trans (map_zero _).symm)
    rw [this]; exact Ideal.zero_mem _)⟩
  have hp : IsProper A.hom := hA.proper
  obtain ⟨s, hs₁, hs₂⟩ := exists_section_of_pow_eq_one hT (jK R) A n hn _ x₀ hx₀ (𝟙 _) (Category.id_comp _)
  let σ : 𝟙_ (Over (Sp R)) ⟶ A := Over.homMk s hs₁
  have e₁ : toUnit (Over.mk (jK R)) ≫ σ = x₀ := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, GlobalTheory.ObjPull.toUnit_left']
    exact hs₂.trans (Category.id_comp _)
  refine ⟨σ, ?_, ?_⟩
  · have : toUnit (Over.mk (jK R)) ≫ σ ^ n = toUnit (Over.mk (jK R)) ≫ 1 := by
      rw [MonObj.comp_pow, e₁, hx₀, MonObj.comp_one]
    apply Over.OverMorphism.ext
    have h2 := congr(($this).left)
    rw [Over.comp_left, Over.comp_left, GlobalTheory.ObjPull.toUnit_left'] at h2
    have : AlgebraicGeometry.IsReduced (𝟙_ (Over (Sp R))).left := inferInstanceAs (AlgebraicGeometry.IsReduced (Sp R))
    exact ext_of_isDominant_of_isSeparated A.hom (by rw [Over.w, Over.w]) (jK R) h2
  · rw [e₀, ← e₁, ← Category.assoc, comp_toUnit]

/- English proof (translation)
Introduce `R _ _ _ _ A _ _ n hA hn h K _ _ t x hx`. Establish `hn' : IsUnit (n : Γ(Sp R, ⊤))`. Use `hn.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis. Take `⟨-, hfin, het⟩` from `GrpTangent.finiteEtale_mulN_torsion A hn'`.

Take `⟨y, hy, -⟩` from `LatticeTorsion.existsUnique_torsion A n x hx`. Take `⟨w⟩ : Nonempty (Sp K)` from `inferInstance`. Establish `hs : (⊥ : PrimeSpectrum R) ⤳ (torsion A n).hom (y.left w)` using `(PrimeSpectrum.le_iff_specializes _ _).1 bot_le`. Take `⟨z, hz, ez⟩` from `Flat.generalizingMap (torsion A n).hom hs`. Set `k` to `AlgebraicClosure ((torsion A n).left.residueField z)`.

Set `u : Sp k ⟶ (torsion A n).left` to `spMap (algebraMap ((torsion A n).left.residueField z) k) ≫ (torsion A n).left.fromSpecResidueField z`. Take `⟨v⟩ : Nonempty (Sp k)` from `inferInstance`. Establish `hu : u v = z`. Establish `: u v ∈ Set.range ((torsion A n).left.fromSpecResidueField z)` using `⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩`. Rewrite `this` using `[Scheme.range_fromSpecResidueField]`. Then use the resulting hypothesis.

Take `⟨κ, hκ⟩` from `exists_factor_generic (u ≫ (torsion A n).hom) v ((Scheme.Hom.comp_apply _ _ _).trans (by rw [hu]; exact ez))`. Set `u' : Over.mk (spMap κ ≫ jK R) ⟶ torsion A n` to `Over.homMk u hκ`. Take `⟨σ, hσ, eσ⟩` from `exists_section_generic A hA hn' h κ (u' ≫ torsion.ι A n) (by`. Rewrite using `[← MonObj.comp_pow, LatticeTorsion.torsionι_pow_eq_one, MonObj.comp_one])`. Take `⟨C, hC, hCz⟩` from `TorsionCover.exists_clopen_eq_one A hA hn' (torsion.ι A n * (toUnit _ ≫ σ)⁻¹) (by`.

Rewrite using `[mul_pow, inv_pow, ← MonObj.comp_pow, hσ, MonObj.comp_one, LatticeTorsion.torsionι_pow_eq_one, inv_one, _root_.mul_one])`. Establish `key : ∀ (T : Over (Sp R)) (a : T ⟶ torsion A n), a ≫ (torsion.ι A n * (toUnit _ ≫ σ)⁻¹) = 1 ↔ toUnit T ≫ σ = a ≫ torsion.ι A n` using `fun T a => by`. Rewrite using `[MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, comp_toUnit, mul_inv_eq_one, eq_comm]`. Establish `hzC : z ∈ C` using `(hCz _ u').1 ((key _ _).2 eσ) ⟨v, hu⟩`. Establish `hyC : y.left w ∈ C` using `hz.mem_closed hC.isClosed hzC`.

Use `⟨σ, hσ, ?_⟩` and prove the remaining obligations. Rewrite using `[← hy]`. Use `(key _ _).1 ((hCz _ y).2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨w', rfl⟩`. Rewrite using `[Subsingleton.elim (α := Sp K) w' w]` and apply the resulting hypothesis.
-/
theorem exists_section_of_torsRat : ∀ (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsNoetherianRing R₀] [IsIntegrallyClosed R₀] (A : Over (Sp R₀)) [GrpObj A] [IsCommMonObj A] (n : ℕ), IsAbelianScheme A → IsUnit (n : R₀) → TorsRat A n → ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ Sp R₀) (x : Over.mk t ⟶ A), x ^ n = 1 → ∃ σ : 𝟙_ (Over (Sp R₀)) ⟶ A, σ ^ n = 1 ∧ toUnit (Over.mk t) ≫ σ = x := by
  intro R _ _ _ _ A _ _ n hA hn h K _ _ t x hx
  have hn' : IsUnit (n : Γ(Sp R, ⊤)) := by
    have := hn.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    rwa [map_natCast] at this
  obtain ⟨-, hfin, het⟩ := GrpTangent.finiteEtale_mulN_torsion A hn'
  obtain ⟨y, hy, -⟩ := LatticeTorsion.existsUnique_torsion A n x hx
  obtain ⟨w⟩ : Nonempty (Sp K) := inferInstance
  have hs : (⊥ : PrimeSpectrum R) ⤳ (torsion A n).hom (y.left w) :=
    (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
  obtain ⟨z, hz, ez⟩ := Flat.generalizingMap (torsion A n).hom hs
  let k := AlgebraicClosure ((torsion A n).left.residueField z)
  let u : Sp k ⟶ (torsion A n).left :=
    spMap (algebraMap ((torsion A n).left.residueField z) k) ≫ (torsion A n).left.fromSpecResidueField z
  obtain ⟨v⟩ : Nonempty (Sp k) := inferInstance
  have hu : u v = z := by
    have : u v ∈ Set.range ((torsion A n).left.fromSpecResidueField z) := ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
    rwa [Scheme.range_fromSpecResidueField] at this
  obtain ⟨κ, hκ⟩ := exists_factor_generic (u ≫ (torsion A n).hom) v
    ((Scheme.Hom.comp_apply _ _ _).trans (by rw [hu]; exact ez))
  let u' : Over.mk (spMap κ ≫ jK R) ⟶ torsion A n := Over.homMk u hκ
  obtain ⟨σ, hσ, eσ⟩ := exists_section_generic A hA hn' h κ (u' ≫ torsion.ι A n) (by
    rw [← MonObj.comp_pow, LatticeTorsion.torsionι_pow_eq_one, MonObj.comp_one])
  obtain ⟨C, hC, hCz⟩ := TorsionCover.exists_clopen_eq_one A hA hn'
    (torsion.ι A n * (toUnit _ ≫ σ)⁻¹) (by
      rw [mul_pow, inv_pow, ← MonObj.comp_pow, hσ, MonObj.comp_one, LatticeTorsion.torsionι_pow_eq_one, inv_one,
        _root_.mul_one])
  have key : ∀ (T : Over (Sp R)) (a : T ⟶ torsion A n),
      a ≫ (torsion.ι A n * (toUnit _ ≫ σ)⁻¹) = 1 ↔ toUnit T ≫ σ = a ≫ torsion.ι A n := fun T a => by
    rw [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, comp_toUnit, mul_inv_eq_one, eq_comm]
  have hzC : z ∈ C := (hCz _ u').1 ((key _ _).2 eσ) ⟨v, hu⟩
  have hyC : y.left w ∈ C := hz.mem_closed hC.isClosed hzC
  refine ⟨σ, hσ, ?_⟩
  rw [← hy]
  refine (key _ _).1 ((hCz _ y).2 ?_)
  rintro _ ⟨w', rfl⟩
  rwa [Subsingleton.elim (α := Sp K) w' w]

end GlobalTheory.TorsConst
