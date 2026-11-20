import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalEndOfEighthPowerOfPolAVPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSymmetryHypothesisOfPolAVPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisationModelFiniteExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArithBaseFiniteContainingRootOfUnity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8ThetaSetupGenericPointExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpPolarizationPullbackStable
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFractionRingOfForallDiv
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaSystemOfPolarisedLevel
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsLevelStructureOfGenericOfFibrewiseIndep
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueSectionOfDense
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionSectionExtendsAbLocus
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.SympLevelExt

/- English proof (translation)
The claim follows from `LBIso.symm (LBIso.chartPull (chartPullLinComb L a (fun _ : PUnit => b) (fun _ => b ≫ a) (fun _ => 1) (𝟙 _) fun _ => (Category.id_comp _).symm) (chartPullId _) (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hL _)))`.
-/
theorem lbIso_pull_comp {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (a : Y ⟶ X) (b : Z ⟶ Y) :
    LBIso (L.pull (b ≫ a)) ((L.pull a).pull b) :=
  LBIso.symm (LBIso.chartPull (chartPullLinComb L a (fun _ : PUnit => b)
      (fun _ => b ≫ a) (fun _ => 1) (𝟙 _) fun _ => (Category.id_comp _).symm)
      (chartPullId _) (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hL _)))

/- English proof (translation)
Unfold `linComb`. Rewrite using `[map_list_prod, List.map_ofFn]`. Use `congr 1`. Use `congrArg List.ofFn (funext fun i => ?_)` and prove the remaining obligations. Conclude with `map_pow ρ (y i) (a i)`.
-/
theorem map_linComb {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {T : Over S}
    {T' : Over S'} (ρ : (T ⟶ A) →* (T' ⟶ A')) {n : ℕ} (y : Fin n → (T ⟶ A)) (a : Fin n → ℕ) :
    ρ (linComb y a) = linComb (fun i => ρ (y i)) a := by
  unfold linComb
  rw [map_list_prod, List.map_ofFn]
  congr 1
  refine congrArg List.ofFn (funext fun i => ?_)
  exact map_pow ρ (y i) (a i)

/- English proof (translation)
Introduce `p`. Establish `hs : (⊥ : PrimeSpectrum R) ⤳ p` using `(PrimeSpectrum.le_iff_specializes _ _).1 bot_le`. Conclude with `closure_mono (Set.singleton_subset_iff.2 hD) (specializes_iff_mem_closure.1 hs)`.
-/
theorem dense_of_bot_mem {R : Type} [CommRing R] [IsDomain R] (D : Set (Sp R))
    (hD : (⊥ : PrimeSpectrum R) ∈ D) : Dense D := by
  intro p
  have hs : (⊥ : PrimeSpectrum R) ⤳ p := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
  exact closure_mono (Set.singleton_subset_iff.2 hD) (specializes_iff_mem_closure.1 hs)

/- English proof (translation)
Establish `hn' : IsUnit (n : Γ(Sp R, ⊤))`. Use `hn.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis. Establish `hT : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp R)` using `fun p => by`. Use `⟨inferInstance, ?_⟩` and prove the remaining obligations.

Establish `: (PrimeSpectrum.asIdeal p).IsPrime` using `PrimeSpectrum.isPrime p`. Establish `h` using `StructureSheaf.IsLocalization.to_stalk R p`. Conclude with `@isIntegrallyClosed_of_isLocalization R ((Spec.structureSheaf R).presheaf.stalk p) _ _ (_) _ _ (PrimeSpectrum.asIdeal p).primeCompl (Ideal.primeCompl_le_nonZeroDivisors _) h`. Establish `j₁ : IsPreimmersion (spMap (algebraMap R F))` using `IsPreimmersion.of_isLocalization (nonZeroDivisors R)`. Establish `j₂ : Flat (spMap (algebraMap R F))` using `(HasRingHomProperty.Spec_iff (P := @Flat)).2 (RingHom.flat_algebraMap_iff.2 (IsLocalization.flat F (nonZeroDivisors R)))`.

Establish `j₃ : IsDominant (spMap (algebraMap R F))` using `⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by`. Introduce `a ha`. Establish `: a = 0` using `IsFractionRing.injective R F (ha.trans (map_zero _).symm)`. Rewrite using `[this]`. Conclude with `Ideal.zero_mem _)⟩`.

Take `⟨σ, hσ₁, hσ₂⟩` from `exists_section_of_pow_eq_one hT (spMap (algebraMap R F)) G n hn' _ x hx (𝟙 _) (by simp)`. Set `σ' : baseOver (Sp R) ⟶ G` to `Over.homMk σ (by simpa using hσ₁)`. Establish `hσ : spMap (algebraMap R F) ≫ σ'.left = x.left` using `by show spMap (algebraMap R F) ≫ σ = x.left`. Simplify using `using hσ₂`. Use `⟨σ', ?_, hσ⟩` and prove the remaining obligations.

Set `U : Over.mk ((baseOver (Sp F)).hom ≫ spMap (algebraMap R F)) ⟶ baseOver (Sp R)` to `Over.homMk (spMap (algebraMap R F)) (by simp)`. Establish `hU : U ≫ σ' = x` using `Over.OverMorphism.ext hσ`. Establish `e : U ≫ σ' ^ n = U ≫ 1` using `by rw [MonObj.comp_pow, MonObj.comp_one, hU, hx]`. Conclude with `over_points_ext_of_injective _ G R F (algebraMap R F) (IsFractionRing.injective R F) _ _ _ (congrArg (fun q => q.left) e)`.
-/
theorem extend_torsion {R F : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    [Field F] [Algebra R F] [IsFractionRing R F] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    [IsProper G.hom] (n : ℕ) (hn : IsUnit (n : R))
    (x : Over.mk ((baseOver (Sp F)).hom ≫ spMap (algebraMap R F)) ⟶ G) (hx : x ^ n = 1) :
    ∃ σ : baseOver (Sp R) ⟶ G, σ ^ n = 1 ∧ spMap (algebraMap R F) ≫ σ.left = x.left := by
  have hn' : IsUnit (n : Γ(Sp R, ⊤)) := by
    have := hn.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    rwa [map_natCast] at this
  have hT : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp R) := fun p => by
    refine ⟨inferInstance, ?_⟩
    have : (PrimeSpectrum.asIdeal p).IsPrime := PrimeSpectrum.isPrime p
    have h := StructureSheaf.IsLocalization.to_stalk R p
    exact @isIntegrallyClosed_of_isLocalization R ((Spec.structureSheaf R).presheaf.stalk p) _ _ (_) _ _
      (PrimeSpectrum.asIdeal p).primeCompl (Ideal.primeCompl_le_nonZeroDivisors _) h
  have j₁ : IsPreimmersion (spMap (algebraMap R F)) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have j₂ : Flat (spMap (algebraMap R F)) :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).2 (RingHom.flat_algebraMap_iff.2 (IsLocalization.flat F (nonZeroDivisors R)))
  have j₃ : IsDominant (spMap (algebraMap R F)) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
    intro a ha
    have : a = 0 := IsFractionRing.injective R F (ha.trans (map_zero _).symm)
    rw [this]; exact Ideal.zero_mem _)⟩
  obtain ⟨σ, hσ₁, hσ₂⟩ := exists_section_of_pow_eq_one hT (spMap (algebraMap R F)) G n hn' _ x hx (𝟙 _)
    (by simp)
  let σ' : baseOver (Sp R) ⟶ G := Over.homMk σ (by simpa using hσ₁)
  have hσ : spMap (algebraMap R F) ≫ σ'.left = x.left := by
    show spMap (algebraMap R F) ≫ σ = x.left
    simpa using hσ₂
  refine ⟨σ', ?_, hσ⟩
  let U : Over.mk ((baseOver (Sp F)).hom ≫ spMap (algebraMap R F)) ⟶ baseOver (Sp R) :=
    Over.homMk (spMap (algebraMap R F)) (by simp)
  have hU : U ≫ σ' = x := Over.OverMorphism.ext hσ
  have e : U ≫ σ' ^ n = U ≫ 1 := by rw [MonObj.comp_pow, MonObj.comp_one, hU, hx]
  exact over_points_ext_of_injective _ G R F (algebraMap R F) (IsFractionRing.injective R F) _ _ _
    (congrArg (fun q => q.left) e)

end GlobalTheory.SympLevelExt

namespace GlobalTheory.SympLevelExt

/- English proof (translation)
Set `s : Sp (AlgebraicClosure F) ⟶ Sp F` to `spMap (algebraMap F (AlgebraicClosure F))`. Set `T : Over (Sp F)` to `Over.mk s`. Set `ρ` to `pushHom hp T`. Establish `hinj : Function.Injective ρ` using `fun a b hab => by`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises.

Apply `hp.1.hom_ext` to reduce the goal to its premises. Conclude with `congrArg (fun q => q.left) hab`. Rewrite using `[Over.w a, Over.w b]`. Establish `hsurj : ∀ w : Over.mk (T.hom ≫ spMap (algebraMap R F)) ⟶ G, ∃ a, ρ a = w` using `fun w => ⟨Over.homMk (hp.1.lift w.left T.hom (Over.w w)) (hp.1.lift_snd _ _ _), Over.OverMorphism.ext (hp.1.lift_fst _ _ _)⟩`. Establish `hcomp : ∀ i, ρ ((Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp F)) ≫ lev₀.pt i) = (Over.homMk (s ≫ spMap (algebraMap R F)) (by simp) : Over.mk (s ≫ spMap (algebraMap R F)) ⟶ baseOver (Sp R)) ≫ y i` using `fun i => by`.

Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Use `show (s ≫ (lev₀.pt i).left) ≫ φ = (s ≫ spMap (algebraMap R F)) ≫ (y i).left`. Rewrite using `[Category.assoc, hy, Category.assoc]`. Establish `hlin : ∀ d : Fin (2 * Q.g) → ℕ, ρ (linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp F)) ≫ lev₀.pt i) d) = linComb (fun i => (Over.homMk (s ≫ spMap (algebraMap R F)) (by simp) : Over.mk (s ≫ spMap (algebraMap R F)) ⟶ baseOver (Sp R)) ≫ y i) d` using `fun d => by`. Rewrite using `[map_linComb]`.

Simplify using `only [hcomp]`. Take `⟨a, rfl⟩` from `hsurj z`. Establish `ha : a ^ k = 1` using `hinj (by rw [map_pow, hz, map_one])`. Take `⟨c, hc⟩` from `lev₀.span (AlgebraicClosure F) s a ha`. Use `⟨fun i => ((c i : ℕ) : ZMod k), ?_, ?_⟩` and prove the remaining obligations.

Use `show linComb _ (fun i => (((c i : ℕ) : ZMod k)).val) = ρ a`. Simplify using `only [ZMod.val_natCast_of_lt (Fin.is_lt _)]`. Rewrite using `[← hlin, hc]`. Introduce `c' hc'`. Establish `e : ρ (linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp F)) ≫ lev₀.pt i) (fun i => ((⟨(c' i).val, ZMod.val_lt (c' i)⟩ : Fin k) : ℕ))) = ρ a`.

Rewrite using `[hlin]`. Conclude with `hc'`. Establish `e'` using `lev₀.indep (AlgebraicClosure F) s _ c ((hinj e).trans hc.symm)`. Use function extensionality and compare the values at `i`. Use `congrArg (fun f => ((f i : ℕ) : ZMod k)) e'` as an intermediate fact.

Simplify using `using this`.
-/
theorem generic_basis {R F : Type} [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    {Q : PolAV (Sp F)} (G : Over (Sp R)) [GrpObj G] (φ : Q.A.left ⟶ G.left)
    (hp : IsGrpPullback Q.A G (spMap (algebraMap R F)) φ) (k : ℕ) [NeZero k] (ze₀ : Γ(Sp F, ⊤)ˣ)
    (lev₀ : Out.Level Q k ze₀) (y : Fin (2 * Q.g) → (baseOver (Sp R) ⟶ G))
    (hy : ∀ i, (lev₀.pt i).left ≫ φ = spMap (algebraMap R F) ≫ (y i).left)
    (z : Over.mk (spMap (algebraMap F (AlgebraicClosure F)) ≫ spMap (algebraMap R F)) ⟶ G) (hz : z ^ k = 1) :
    ∃! c : Fin (2 * Q.g) → ZMod k,
      linComb (fun i => (Over.homMk (spMap (algebraMap F (AlgebraicClosure F)) ≫ spMap (algebraMap R F))
        (by simp) : Over.mk (spMap (algebraMap F (AlgebraicClosure F)) ≫ spMap (algebraMap R F)) ⟶
          baseOver (Sp R)) ≫ y i) (fun i => (c i).val) = z := by
  let s : Sp (AlgebraicClosure F) ⟶ Sp F := spMap (algebraMap F (AlgebraicClosure F))
  let T : Over (Sp F) := Over.mk s
  let ρ := pushHom hp T
  have hinj : Function.Injective ρ := fun a b hab => by
    apply Over.OverMorphism.ext
    apply hp.1.hom_ext
    · exact congrArg (fun q => q.left) hab
    · rw [Over.w a, Over.w b]
  have hsurj : ∀ w : Over.mk (T.hom ≫ spMap (algebraMap R F)) ⟶ G, ∃ a, ρ a = w := fun w =>
    ⟨Over.homMk (hp.1.lift w.left T.hom (Over.w w)) (hp.1.lift_snd _ _ _),
      Over.OverMorphism.ext (hp.1.lift_fst _ _ _)⟩
  have hcomp : ∀ i, ρ ((Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp F)) ≫ lev₀.pt i) =
      (Over.homMk (s ≫ spMap (algebraMap R F)) (by simp) :
        Over.mk (s ≫ spMap (algebraMap R F)) ⟶ baseOver (Sp R)) ≫ y i := fun i => by
    apply Over.OverMorphism.ext
    show (s ≫ (lev₀.pt i).left) ≫ φ = (s ≫ spMap (algebraMap R F)) ≫ (y i).left
    rw [Category.assoc, hy, Category.assoc]
  have hlin : ∀ d : Fin (2 * Q.g) → ℕ,
      ρ (linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp F)) ≫ lev₀.pt i) d) =
      linComb (fun i => (Over.homMk (s ≫ spMap (algebraMap R F)) (by simp) :
        Over.mk (s ≫ spMap (algebraMap R F)) ⟶ baseOver (Sp R)) ≫ y i) d := fun d => by
    rw [map_linComb]
    simp only [hcomp]
  obtain ⟨a, rfl⟩ := hsurj z
  have ha : a ^ k = 1 := hinj (by rw [map_pow, hz, map_one])
  obtain ⟨c, hc⟩ := lev₀.span (AlgebraicClosure F) s a ha
  refine ⟨fun i => ((c i : ℕ) : ZMod k), ?_, ?_⟩
  · show linComb _ (fun i => (((c i : ℕ) : ZMod k)).val) = ρ a
    simp only [ZMod.val_natCast_of_lt (Fin.is_lt _)]
    rw [← hlin, hc]
  · intro c' hc'
    have e : ρ (linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp F)) ≫ lev₀.pt i)
        (fun i => ((⟨(c' i).val, ZMod.val_lt (c' i)⟩ : Fin k) : ℕ))) = ρ a := by
      rw [hlin]; exact hc'
    have e' := lev₀.indep (AlgebraicClosure F) s _ c ((hinj e).trans hc.symm)
    funext i
    have := congrArg (fun f => ((f i : ℕ) : ZMod k)) e'
    simpa using this

end GlobalTheory.SympLevelExt

namespace GlobalTheory.SympLevelExt

/- English proof (translation)
Introduce `R₁ _ P₁ R F _ _ _ _ _ _ _ h Q φ K ze hK hKu hg hpb hQL hlev`. Take `⟨lev₀⟩` from `hlev`. Consider the cases of `Q with`. Consider the case `mk QA QisAb Qg Qsm QL QisLB Qrig Qsym Qamp Qkt`. Simplify using `only at hg`.

Substitute `hg` using the available equality. Establish `hL` using `abelianSchemeLaws_all.1`. Use `haveI : NeZero K := ⟨hK.ne'⟩`. Set `j` to `spMap (algebraMap R F)`. Set `P : PolAV (Sp R)` to `StrictPull.polPull P₁ (spMap h)`.

Set `ψ : P.A.left ⟶ P₁.A.left` to `pullback.fst P₁.A.hom (spMap h)`. Establish `hψ : IsGrpPullback P.A P₁.A (spMap h) ψ` using `isGrpPullback_pullback P₁.A (spMap h)`. Establish `hc : spMap ((algebraMap R F).comp h) = j ≫ spMap h`. Simplify using `only [spMap, j, CommRingCat.ofHom_comp, Spec.map_comp]`. Establish `hw : φ ≫ P₁.A.hom = (QA.hom ≫ j) ≫ spMap h` using `by rw [hpb.1.w, hc, Category.assoc]`.

Set `φ' : QA.left ⟶ P.A.left` to `hψ.1.lift φ (QA.hom ≫ j) hw`. Establish `e₁ : φ' ≫ ψ = φ` using `hψ.1.lift_fst _ _ _`. Establish `e₂ : φ' ≫ P.A.hom = QA.hom ≫ j` using `hψ.1.lift_snd _ _ _`. Establish `hpb' : IsGrpPullback QA P.A j φ'` using `hψ.cancel (by rw [e₁, ← hc]; exact hpb) e₂`. Establish `hQL' : LBIso QL (P.L.pull φ')`.

Use `LBIso.trans QisLB (pull_isLB P₁.isLB _) (pull_isLB P.isLB _) hQL ?_` and prove the remaining obligations. Use `lbIso_pull_comp P₁.isLB ψ φ'` as an intermediate fact. Rewrite `this` using `[e₁]`. Conclude with `this`. Establish `hP : IsProper P.A.hom` using `P.isAb.proper`.

Use `P.isAb.comm` as an intermediate fact. Use `choose y hy₁ hy₂ using fun i : Fin (2 * P₁.g) => extend_torsion (R := R) (F := F) P.A K hKu (pushHom hpb' (baseOver (Sp F)) (lev₀.pt i)) (by rw [← map_pow, lev₀.torsion, map_one])`. Establish `hy : ∀ i, (lev₀.pt i).left ≫ φ' = j ≫ (y i).left` using `fun i => (hy₂ i).symm`. Establish `hKu' : IsUnit (K : Γ(Sp R, ⊤))`. Use `hKu.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom` as an intermediate fact.

Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis. Set `x : Sp (AlgebraicClosure F) ⟶ Sp R` to `spMap (algebraMap F (AlgebraicClosure F)) ≫ j`. Establish `hx : (⊥ : PrimeSpectrum R) ∈ Set.range x`. Take `⟨w⟩ : Nonempty (Sp (AlgebraicClosure F))` from `inferInstance`. Use `⟨w, ?_⟩` and prove the remaining obligations.

Apply `PrimeSpectrum.ext` to reduce the goal to its premises. Use `show Ideal.comap (algebraMap R F) (Ideal.comap (algebraMap F (AlgebraicClosure F)) (PrimeSpectrum.asIdeal w)) = ⊥`. Rewrite using `[@Ideal.eq_bot_of_prime _ _ (PrimeSpectrum.asIdeal w) (PrimeSpectrum.isPrime w), Ideal.comap_bot_of_injective _ (algebraMap F (AlgebraicClosure F)).injective, Ideal.comap_bot_of_injective _ (IsFractionRing.injective R F)]`. Establish `hbasis` using `torsion_basis_of_dense (Sp R) P.A K (2 * P₁.g) y (Set.range x) P.isAb hK hKu' hy₁ (dense_of_bot_mem _ hx) (fun p hp => ⟨AlgebraicClosure F, inferInstance, inferInstance, x, hp, fun z hz => generic_basis (Q := ⟨QA, QisAb, P₁.g, Qsm, QL, QisLB, Qrig, Qsym, Qamp, Qkt⟩) P.A φ' hpb' K …`. Establish `hind : ∀ (F' : Type) [Field F'] [IsAlgClosed F'] (s : Spec (CommRingCat.of F') ⟶ Sp R) (c c' : Fin (2 * P.g) → Fin K), linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp R)) ≫ y i) (fun i => (c i : ℕ)) = linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ ba …`.

Introduce `F' _ _ s c c' hcc`. Take `⟨d, -, hd⟩` from `hbasis F' s (linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp R)) ≫ y i) (fun i => (c i : ℕ))) (DenseBasis.linComb_pow_eq_one _ (fun i => by rw [← MonObj.comp_pow, hy₁, MonObj.comp_one]) _)`. Establish `h₁` using `hd (fun i => ((c i : ℕ) : ZMod K)) (by simp only [ZMod.val_natCast_of_lt (Fin.is_lt _)])`. Establish `h₂` using `hd (fun i => ((c' i : ℕ) : ZMod K)) (by simp only [ZMod.val_natCast_of_lt (Fin.is_lt _)]; exact hcc.symm)`. Use function extensionality and compare the values at `i`.

Apply `Fin.ext` to reduce the goal to its premises. Use `congrArg (fun f => (f i).val) (h₁.trans h₂.symm)` as an intermediate fact. Simplify `this` using `only [ZMod.val_natCast_of_lt (Fin.is_lt _)]`. Take `⟨lev, -⟩` from `level_of_generic_of_indep hL R F P ⟨QA, QisAb, P₁.g, Qsm, QL, QisLB, Qrig, Qsym, Qamp, Qkt⟩ φ' hpb' hQL' rfl K ze _ hKu rfl lev₀ y (fun i₀ i hi => by`. Take `rfl : i₀ = i` from `Fin.ext hi`.

Conclude with `hy i₀) hind`. Conclude with `⟨P, ψ, rfl, hψ, GlobalTheory.PolBaseChange.lbIso_refl P.isLB, ⟨lev⟩⟩`.
-/
theorem level_extends : ∀ {R₁ : Type} [CommRing R₁] (P₁ : PolAV (Sp R₁)) (R F : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Field F] [Algebra R F] [IsFractionRing R F] (h : R₁ →+* R) (Q : PolAV (Sp F)) (φ : Q.A.left ⟶ P₁.A.left) (K : ℕ) (ze : Rˣ), 0 < K → IsUnit (K : R) → Q.g = P₁.g → IsGrpPullback Q.A P₁.A (spMap ((algebraMap R F).comp h)) φ → LBIso Q.L (P₁.L.pull φ) → Nonempty (Out.Level Q K (unitOn (Units.map (algebraMap R F).toMonoidHom ze))) → ∃ (P : PolAV (Sp R)) (ψ : P.A.left ⟶ P₁.A.left), P.g = P₁.g ∧ IsGrpPullback P.A P₁.A (spMap h) ψ ∧ LBIso P.L (P₁.L.pull ψ) ∧ Nonempty (Out.Level P K (unitOn ze)) := by
  intro R₁ _ P₁ R F _ _ _ _ _ _ _ h Q φ K ze hK hKu hg hpb hQL hlev
  obtain ⟨lev₀⟩ := hlev
  cases Q with
  | mk QA QisAb Qg Qsm QL QisLB Qrig Qsym Qamp Qkt =>
  dsimp only at hg
  subst hg
  have hL := abelianSchemeLaws_all.1
  haveI : NeZero K := ⟨hK.ne'⟩
  let j := spMap (algebraMap R F)
  let P : PolAV (Sp R) := StrictPull.polPull P₁ (spMap h)
  let ψ : P.A.left ⟶ P₁.A.left := pullback.fst P₁.A.hom (spMap h)
  have hψ : IsGrpPullback P.A P₁.A (spMap h) ψ := isGrpPullback_pullback P₁.A (spMap h)
  have hc : spMap ((algebraMap R F).comp h) = j ≫ spMap h := by
    simp only [spMap, j, CommRingCat.ofHom_comp, Spec.map_comp]
  have hw : φ ≫ P₁.A.hom = (QA.hom ≫ j) ≫ spMap h := by rw [hpb.1.w, hc, Category.assoc]
  let φ' : QA.left ⟶ P.A.left := hψ.1.lift φ (QA.hom ≫ j) hw
  have e₁ : φ' ≫ ψ = φ := hψ.1.lift_fst _ _ _
  have e₂ : φ' ≫ P.A.hom = QA.hom ≫ j := hψ.1.lift_snd _ _ _
  have hpb' : IsGrpPullback QA P.A j φ' := hψ.cancel (by rw [e₁, ← hc]; exact hpb) e₂
  have hQL' : LBIso QL (P.L.pull φ') := by
    refine LBIso.trans QisLB (pull_isLB P₁.isLB _) (pull_isLB P.isLB _) hQL ?_
    have := lbIso_pull_comp P₁.isLB ψ φ'
    rw [e₁] at this
    exact this
  have hP : IsProper P.A.hom := P.isAb.proper
  have := P.isAb.comm
  choose y hy₁ hy₂ using fun i : Fin (2 * P₁.g) =>
    extend_torsion (R := R) (F := F) P.A K hKu (pushHom hpb' (baseOver (Sp F)) (lev₀.pt i))
      (by rw [← map_pow, lev₀.torsion, map_one])
  have hy : ∀ i, (lev₀.pt i).left ≫ φ' = j ≫ (y i).left := fun i => (hy₂ i).symm
  have hKu' : IsUnit (K : Γ(Sp R, ⊤)) := by
    have := hKu.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    rwa [map_natCast] at this
  let x : Sp (AlgebraicClosure F) ⟶ Sp R := spMap (algebraMap F (AlgebraicClosure F)) ≫ j
  have hx : (⊥ : PrimeSpectrum R) ∈ Set.range x := by
    obtain ⟨w⟩ : Nonempty (Sp (AlgebraicClosure F)) := inferInstance
    refine ⟨w, ?_⟩
    apply PrimeSpectrum.ext
    show Ideal.comap (algebraMap R F) (Ideal.comap (algebraMap F (AlgebraicClosure F)) (PrimeSpectrum.asIdeal w)) = ⊥
    rw [@Ideal.eq_bot_of_prime _ _ (PrimeSpectrum.asIdeal w) (PrimeSpectrum.isPrime w),
      Ideal.comap_bot_of_injective _ (algebraMap F (AlgebraicClosure F)).injective,
      Ideal.comap_bot_of_injective _ (IsFractionRing.injective R F)]
  have hbasis := torsion_basis_of_dense (Sp R) P.A K (2 * P₁.g) y (Set.range x) P.isAb hK hKu' hy₁
    (dense_of_bot_mem _ hx) (fun p hp => ⟨AlgebraicClosure F, inferInstance, inferInstance, x, hp,
      fun z hz => generic_basis (Q := ⟨QA, QisAb, P₁.g, Qsm, QL, QisLB, Qrig, Qsym, Qamp, Qkt⟩) P.A φ' hpb' K _ lev₀ y hy z hz⟩)
  have hind : ∀ (F' : Type) [Field F'] [IsAlgClosed F'] (s : Spec (CommRingCat.of F') ⟶ Sp R)
      (c c' : Fin (2 * P.g) → Fin K),
      linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp R)) ≫ y i) (fun i => (c i : ℕ)) =
        linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp R)) ≫ y i) (fun i => (c' i : ℕ)) →
      c = c' := by
    intro F' _ _ s c c' hcc
    obtain ⟨d, -, hd⟩ := hbasis F' s
      (linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp R)) ≫ y i) (fun i => (c i : ℕ)))
      (DenseBasis.linComb_pow_eq_one _ (fun i => by rw [← MonObj.comp_pow, hy₁, MonObj.comp_one]) _)
    have h₁ := hd (fun i => ((c i : ℕ) : ZMod K)) (by simp only [ZMod.val_natCast_of_lt (Fin.is_lt _)])
    have h₂ := hd (fun i => ((c' i : ℕ) : ZMod K)) (by simp only [ZMod.val_natCast_of_lt (Fin.is_lt _)]; exact hcc.symm)
    funext i
    apply Fin.ext
    have := congrArg (fun f => (f i).val) (h₁.trans h₂.symm)
    simpa only [ZMod.val_natCast_of_lt (Fin.is_lt _)] using this
  obtain ⟨lev, -⟩ := level_of_generic_of_indep hL R F P ⟨QA, QisAb, P₁.g, Qsm, QL, QisLB, Qrig, Qsym, Qamp, Qkt⟩ φ'
    hpb' hQL' rfl K ze _ hKu rfl lev₀ y (fun i₀ i hi => by
      obtain rfl : i₀ = i := Fin.ext hi
      exact hy i₀) hind
  exact ⟨P, ψ, rfl, hψ, GlobalTheory.PolBaseChange.lbIso_refl P.isLB, ⟨lev⟩⟩

end GlobalTheory.SympLevelExt
