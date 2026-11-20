import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HInv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimLtTopOfEssFiniteType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSurjectionCechDescentTateTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelwiseEquivalenceIsEquivalenceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivalenceBasicPropertiesStatement
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PiTensorLiftCompSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecWidePushoutIsoWidePullbackYonedaStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC.CechDescHInv

/- English proof (translation)
The claim follows from `GlobalTheory.T.spec_widePushout_iso_widePullback_yoneda A B T a k ι hι hu`.
-/
theorem yoneda_spec_widePullback (A B T : Type) [CommRing A] [CommRing B] [CommRing T] (a : A →+* B) (k : ℕ)
    (ι : Fin (k + 1) → (B →+* T)) (hι : ∀ j, (ι j).comp a = (ι 0).comp a)
    (hu : ∀ (R : Type) [CommRing R] (g : Fin (k + 1) → (B →+* R)), (∀ j, (g j).comp a = (g 0).comp a) →
      ∃! φ : T →+* R, ∀ j, φ.comp (ι j) = g j) :
    ∃ e : yoneda.obj (Spec (CommRingCat.of T)) ≅ widePullback (yoneda.obj (Spec (CommRingCat.of A)))
        (fun _ : Fin (k + 1) => yoneda.obj (Spec (CommRingCat.of B))) (fun _ => yoneda.map (Spec.map (CommRingCat.ofHom a))),
      ∀ j, e.hom ≫ WidePullback.π _ j = yoneda.map (Spec.map (CommRingCat.ofHom (ι j))) :=
  GlobalTheory.T.spec_widePushout_iso_widePullback_yoneda A B T a k ι hι hu

/- English proof (translation)
Use `letI : Algebra A R := ((g 0).comp (algebraMap A B)).toAlgebra`. Set `g' : Fin (k + 1) → (B →ₐ[A] R)` to `fun j => ⟨g j, fun r => RingHom.congr_fun (hg j) r⟩`. Use `⟨(GlobalTheory.piTensorLift g').toRingHom, fun j => ?_, fun ψ hψ => ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Conclude with `GlobalTheory.piTensorLift_single g' j x`.

Establish `hc : ∀ r : A, ψ (algebraMap A (PiTensorProduct A fun _ : Fin (k + 1) => B) r) = algebraMap A R r`. Introduce `r`. Establish `h1 : algebraMap A (PiTensorProduct A fun _ : Fin (k + 1) => B) r = PiTensorProduct.singleAlgHom (R` using `A) (A := fun _ : Fin (k + 1) => B) 0 (algebraMap A B r) := ((PiTensorProduct.singleAlgHom (R := A) (A := fun _ : Fin (k + 1) => B) 0).commutes r).symm`. Rewrite using `[h1]`. Conclude with `RingHom.congr_fun (hψ 0) (algebraMap A B r)`.

Set `ψ' : PiTensorProduct A (fun _ : Fin (k + 1) => B) →ₐ[A] R` to `⟨ψ, hc⟩`. Establish `: ψ' = GlobalTheory.piTensorLift g'` using `PiTensorProduct.algHom_ext fun j => by`. Use extensionality with `x`. Express the relevant statement in the definitionally equal form `ψ _ = _`. Rewrite using `[AlgHom.comp_apply, GlobalTheory.piTensorLift_single]`.

Conclude with `RingHom.congr_fun (hψ j) x`. Conclude with `congrArg AlgHom.toRingHom this`.
-/
theorem tensor_univ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (k : ℕ) (R : Type) [CommRing R]
    (g : Fin (k + 1) → (B →+* R)) (hg : ∀ j, (g j).comp (algebraMap A B) = (g 0).comp (algebraMap A B)) :
    ∃! φ : PiTensorProduct A (fun _ : Fin (k + 1) => B) →+* R,
      ∀ j, φ.comp (PiTensorProduct.singleAlgHom (R := A) (A := fun _ : Fin (k + 1) => B) j).toRingHom = g j := by
  classical
  letI : Algebra A R := ((g 0).comp (algebraMap A B)).toAlgebra
  let g' : Fin (k + 1) → (B →ₐ[A] R) := fun j => ⟨g j, fun r => RingHom.congr_fun (hg j) r⟩
  refine ⟨(GlobalTheory.piTensorLift g').toRingHom, fun j => ?_, fun ψ hψ => ?_⟩
  · ext x
    exact GlobalTheory.piTensorLift_single g' j x
  · have hc : ∀ r : A, ψ (algebraMap A (PiTensorProduct A fun _ : Fin (k + 1) => B) r) = algebraMap A R r := by
      intro r
      have h1 : algebraMap A (PiTensorProduct A fun _ : Fin (k + 1) => B) r =
          PiTensorProduct.singleAlgHom (R := A) (A := fun _ : Fin (k + 1) => B) 0 (algebraMap A B r) :=
        ((PiTensorProduct.singleAlgHom (R := A) (A := fun _ : Fin (k + 1) => B) 0).commutes r).symm
      rw [h1]
      exact RingHom.congr_fun (hψ 0) (algebraMap A B r)
    let ψ' : PiTensorProduct A (fun _ : Fin (k + 1) => B) →ₐ[A] R := ⟨ψ, hc⟩
    have : ψ' = GlobalTheory.piTensorLift g' := PiTensorProduct.algHom_ext fun j => by
      ext x
      change ψ _ = _
      rw [AlgHom.comp_apply, GlobalTheory.piTensorLift_single]
      exact RingHom.congr_fun (hψ j) x
    exact congrArg AlgHom.toRingHom this

/- English proof (translation)
Establish `hX : ∀ j, g j Polynomial.X = g 0 Polynomial.X` using `fun j => by`. Use `RingHom.congr_fun (hg j) Polynomial.X` as an intermediate fact. Simplify using `using this`. Take `⟨ψ, hψ, hψu⟩` from `hu R (fun j => (g j).comp Polynomial.C) (fun j => by`. Use extensionality with `x`.

Use `RingHom.congr_fun (hg j) (Polynomial.C x)` as an intermediate fact. Simplify using `using this)`. Use `⟨Polynomial.eval₂RingHom ψ (g 0 Polynomial.X), fun j => ?_, fun φ hφ => ?_⟩` and prove the remaining obligations. Apply `Polynomial.ringHom_ext` to reduce the goal to its premises. Introduce `b`.

Simplify using `using RingHom.congr_fun (hψ j) b`. Simplify using `[hX j]`. Establish `hC : φ.comp Polynomial.C = ψ` using `hψu _ (fun j => by`. Use extensionality with `b`. Simplify using `using RingHom.congr_fun (hφ j) (Polynomial.C b))`.

Apply `Polynomial.ringHom_ext` to reduce the goal to its premises. Introduce `t`. Simplify using `using RingHom.congr_fun hC t`. Simplify using `using RingHom.congr_fun (hφ 0) Polynomial.X`.
-/
theorem poly_univ (A B T : Type) [CommRing A] [CommRing B] [CommRing T] (a : A →+* B) (k : ℕ)
    (ι : Fin (k + 1) → (B →+* T))
    (hu : ∀ (R : Type) [CommRing R] (g : Fin (k + 1) → (B →+* R)), (∀ j, (g j).comp a = (g 0).comp a) →
      ∃! φ : T →+* R, ∀ j, φ.comp (ι j) = g j)
    (R : Type) [CommRing R] (g : Fin (k + 1) → (Polynomial B →+* R))
    (hg : ∀ j, (g j).comp (Polynomial.mapRingHom a) = (g 0).comp (Polynomial.mapRingHom a)) :
    ∃! φ : Polynomial T →+* R, ∀ j, φ.comp (Polynomial.mapRingHom (ι j)) = g j := by
  have hX : ∀ j, g j Polynomial.X = g 0 Polynomial.X := fun j => by
    have := RingHom.congr_fun (hg j) Polynomial.X
    simpa using this
  obtain ⟨ψ, hψ, hψu⟩ := hu R (fun j => (g j).comp Polynomial.C) (fun j => by
    ext x
    have := RingHom.congr_fun (hg j) (Polynomial.C x)
    simpa using this)
  refine ⟨Polynomial.eval₂RingHom ψ (g 0 Polynomial.X), fun j => ?_, fun φ hφ => ?_⟩
  · apply Polynomial.ringHom_ext
    · intro b
      simpa using RingHom.congr_fun (hψ j) b
    · simp [hX j]
  · have hC : φ.comp Polynomial.C = ψ := hψu _ (fun j => by
      ext b
      simpa using RingHom.congr_fun (hφ j) (Polynomial.C b))
    apply Polynomial.ringHom_ext
    · intro t
      simpa using RingHom.congr_fun hC t
    · simpa using RingHom.congr_fun (hφ 0) Polynomial.X

/- English proof (translation)
Use `⟨IsIntegralHom.SpecMap_iff.2 hi, ⟨fun (x : PrimeSpectrum A) => ?_⟩⟩` and prove the remaining obligations. Use `letI := φ.toAlgebra`. Use `haveI : Algebra.IsIntegral A B := ⟨hi⟩`. Establish `hle : (⊥ : Ideal B).comap (algebraMap A B) ≤ x.asIdeal`. Rewrite using `[← RingHom.ker_eq_comap_bot]`.

Conclude with `hk.trans (nilradical_le_prime x.asIdeal)`. Take `⟨Q, -, hQ, hQx⟩` from `Ideal.exists_ideal_over_prime_of_isIntegral x.asIdeal ⊥ hle`. Establish `: x ∈ Set.range (PrimeSpectrum.comap φ)` using `⟨⟨Q, hQ⟩, PrimeSpectrum.ext hQx⟩`. Conclude with `this`.
-/
theorem spec_integral_surj (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B) (hi : φ.IsIntegral)
    (hk : RingHom.ker φ ≤ nilradical A) :
    IsIntegralHom (Spec.map (CommRingCat.ofHom φ)) ∧ Surjective (Spec.map (CommRingCat.ofHom φ)) := by
  refine ⟨IsIntegralHom.SpecMap_iff.2 hi, ⟨fun (x : PrimeSpectrum A) => ?_⟩⟩
  letI := φ.toAlgebra
  haveI : Algebra.IsIntegral A B := ⟨hi⟩
  have hle : (⊥ : Ideal B).comap (algebraMap A B) ≤ x.asIdeal := by
    rw [← RingHom.ker_eq_comap_bot]
    exact hk.trans (nilradical_le_prime x.asIdeal)
  obtain ⟨Q, -, hQ, hQx⟩ := Ideal.exists_ideal_over_prime_of_isIntegral x.asIdeal ⊥ hle
  have : x ∈ Set.range (PrimeSpectrum.comap φ) := ⟨⟨Q, hQ⟩, PrimeSpectrum.ext hQx⟩
  exact this

/- English proof (translation)
Use `letI := (Polynomial.mapRingHom φ).toAlgebra`. Establish `hC : ∀ b : B, IsIntegral (Polynomial A) (Polynomial.C b)`. Introduce `b`. Take `⟨f, hf, hfb⟩` from `hi b`. Use `⟨f.map Polynomial.C, hf.map _, ?_⟩` and prove the remaining obligations.

Rewrite using `[Polynomial.eval₂_map]`. Establish `e : (algebraMap (Polynomial A) (Polynomial B)).comp Polynomial.C = Polynomial.C.comp φ`. Apply the tactic sequence `ext x <;> simp [RingHom.algebraMap_toAlgebra]`. Rewrite using `[e, ← Polynomial.hom_eval₂, hfb, map_zero]`. Establish `hXi : IsIntegral (Polynomial A) (Polynomial.X : Polynomial B)`.

Establish `: (Polynomial.X : Polynomial B) = algebraMap (Polynomial A) (Polynomial B) Polynomial.X`. Simplify using `[RingHom.algebraMap_toAlgebra]`. Rewrite using `[this]`. Conclude with `isIntegral_algebraMap`. Introduce `p`.

Express the relevant statement in the definitionally equal form `IsIntegral (Polynomial A) p`. Proceed by induction on `p using Polynomial.induction_on with`. Consider the case `C b => exact hC b`. Consider the case `add p r hp hr => exact hp.add hr`. Consider the case `monomial n b _ => exact (hC b).mul (hXi.pow _)`.
-/
theorem poly_isIntegral (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B) (hi : φ.IsIntegral) :
    (Polynomial.mapRingHom φ).IsIntegral := by
  letI := (Polynomial.mapRingHom φ).toAlgebra
  have hC : ∀ b : B, IsIntegral (Polynomial A) (Polynomial.C b) := by
    intro b
    obtain ⟨f, hf, hfb⟩ := hi b
    refine ⟨f.map Polynomial.C, hf.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have e : (algebraMap (Polynomial A) (Polynomial B)).comp Polynomial.C = Polynomial.C.comp φ := by
      ext x <;> simp [RingHom.algebraMap_toAlgebra]
    rw [e, ← Polynomial.hom_eval₂, hfb, map_zero]
  have hXi : IsIntegral (Polynomial A) (Polynomial.X : Polynomial B) := by
    have : (Polynomial.X : Polynomial B) = algebraMap (Polynomial A) (Polynomial B) Polynomial.X := by
      simp [RingHom.algebraMap_toAlgebra]
    rw [this]; exact isIntegral_algebraMap
  intro p
  change IsIntegral (Polynomial A) p
  induction p using Polynomial.induction_on with
  | C b => exact hC b
  | add p r hp hr => exact hp.add hr
  | monomial n b _ => exact (hC b).mul (hXi.pow _)

/- English proof (translation)
Introduce `p hp`. Rewrite using `[mem_nilradical, Polynomial.isNilpotent_iff]`. Introduce `n`. Rewrite using `[← mem_nilradical]`. Apply `hk` to reduce the goal to its premises.

Rewrite `hp`, the goal using `[RingHom.mem_ker]`. Use `congrArg (fun r => Polynomial.coeff r n) hp` as an intermediate fact. Simplify using `using this`.
-/
theorem poly_ker (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B) (hk : RingHom.ker φ ≤ nilradical A) :
    RingHom.ker (Polynomial.mapRingHom φ) ≤ nilradical (Polynomial A) := by
  intro p hp
  rw [mem_nilradical, Polynomial.isNilpotent_iff]
  intro n
  rw [← mem_nilradical]
  apply hk
  rw [RingHom.mem_ker] at hp ⊢
  have := congrArg (fun r => Polynomial.coeff r n) hp
  simpa using this

/- English proof (translation)
Use `hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom` as an intermediate fact. Simplify using `using this`.
-/
theorem isUnit_gamma (q : ℕ) (A : Type) [CommRing A] (hq : IsUnit (q : A)) :
    IsUnit (q : Γ(Spec (CommRingCat.of A), ⊤)) := by
  have := hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  simpa using this

/- English proof (translation)
Introduce `hint hker hq hT i`. Establish `hi : (algebraMap A B).IsIntegral` using `fun x => hint.isIntegral x`. Take `⟨hf1, hf2⟩` from `spec_integral_surj A B (algebraMap A B) hi hker`. Take `⟨hf1', hf2'⟩` from `spec_integral_surj _ _ (Polynomial.mapRingHom (algebraMap A B)) (poly_isIntegral A B _ hi) (poly_ker A B _ hker)`. Establish `hq' : IsUnit (q : Polynomial A)` using `by simpa using hq.map (Polynomial.C : A →+* Polynomial A)`.

Establish `E` using `GlobalTheory.T.etaleCohomologyEquivalence_basic_properties (ZMod q) (tw q i)`. Establish `h1` using `GlobalTheory.EtC.b4 q (Spec.map (CommRingCat.ofHom (algebraMap A B))) (isUnit_gamma q A hq) i`. Establish `h1'` using `GlobalTheory.EtC.b4 q (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap A B)))) (isUnit_gamma q _ hq') i`. Set `F : Arrow.mk (yoneda.map (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap A B))))) ⟶ Arrow.mk (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A B))))` to `Arrow.homMk (yoneda.map (Spec.map (CommRingCat.ofHom (Polynomial.C : B →+* Polynomial B)))) (yoneda.map (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)))) (by`. Simplify using `only [Arrow.mk_hom, ← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`.

Use `congr 3`. Apply the tactic sequence `ext x <;> simp)`. Set `m : cech (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap A B)))) ⟶ cech (Spec.map (CommRingCat.ofHom (algebraMap A B)))` to `Arrow.mapCechNerve F`. Establish `hsq : m ≫ cechAug (Spec.map (CommRingCat.ofHom (algebraMap A B))) = cechAug (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap A B)))) ≫ spMap (Polynomial.C : A →+* Polynomial A)` using `by clear E h1 h1' hT hf1 hf2 hf1' hf2' hint hker hq hq' hi`. Use `NatTrans.ext (funext fun n => ?_)` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `WidePullback.lift _ _ _ ≫ WidePullback.base _ = WidePullback.base _ ≫ yoneda.map (Spec.map _)`. Apply `WidePullback.lift_base` to reduce the goal to its premises. Establish `hm : Eqv _ m (tw q i)`. Use `GlobalTheory.T.levelwiseEquivalence_isEquivalence _ m _ (fun n => ?_)` and prove the remaining obligations. Use `clear h1 h1' hf1 hf2 hf1' hf2' hint hker hq hq' hi hsq`.

Use `set k := n.unop.len`. Set `T` to `PiTensorProduct A (fun _ : Fin (k + 1) => B)`. Set `ι : Fin (k + 1) → (B →+* T)` to `fun j => (PiTensorProduct.singleAlgHom (R := A) (A := fun _ : Fin (k + 1) => B) j).toRingHom`. Establish `hι : ∀ j, (ι j).comp (algebraMap A B) = (ι 0).comp (algebraMap A B)`. Introduce `j`.

Use extensionality with `x`. Simplify using `[ι]`. Establish `hu` using `tensor_univ A B k`. Take `⟨e, he⟩` from `yoneda_spec_widePullback A B T (algebraMap A B) k ι hι hu`. Establish `hι' : ∀ j, (Polynomial.mapRingHom (ι j)).comp (Polynomial.mapRingHom (algebraMap A B)) = (Polynomial.mapRingHom (ι 0)).comp (Polynomial.mapRingHom (algebraMap A B))`.

Introduce `j`. Rewrite using `[Polynomial.mapRingHom_comp, Polynomial.mapRingHom_comp, hι j]`. Take `⟨e', he'⟩` from `yoneda_spec_widePullback (Polynomial A) (Polynomial B) (Polynomial T) (Polynomial.mapRingHom (algebraMap A B)) k (fun j => Polynomial.mapRingHom (ι j)) hι' (poly_univ A B T (algebraMap A B) k ι (fun R _ g hg => hu R g hg))`. Set `mn : widePullback (yoneda.obj (Spec (CommRingCat.of (Polynomial A)))) (fun _ : Fin (k + 1) => yoneda.obj (Spec (CommRingCat.of (Polynomial B)))) (fun _ => yoneda.map (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap A B))))) ⟶ widePullback (yoneda.obj (Spec (CommRin …` to `WidePullback.lift (WidePullback.base _ ≫ yoneda.map (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)))) (fun j => WidePullback.π _ j ≫ yoneda.map (Spec.map (CommRingCat.ofHom (Polynomial.C : B →+* Polynomial B)))) (fun j => by`. Rewrite using `[Category.assoc, ← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← WidePullback.π_arrow _ j, Category.assoc, ← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`.

Use `congr 4`. Apply the tactic sequence `ext x <;> simp)`. Establish `hmn : m.app n = mn` using `rfl`. Establish `hπ : ∀ j, (e'.hom ≫ mn) ≫ WidePullback.π _ j = (yoneda.map (Spec.map (CommRingCat.ofHom (Polynomial.C : T →+* Polynomial T))) ≫ e.hom) ≫ WidePullback.π _ j`. Introduce `j`.

Rewrite using `[Category.assoc, WidePullback.lift_π, ← Category.assoc, he' j, Category.assoc, he j, ← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Use `congr 3`. Apply the tactic sequence `ext x <;> simp`. Establish `key : e'.hom ≫ mn = yoneda.map (Spec.map (CommRingCat.ofHom (Polynomial.C : T →+* Polynomial T))) ≫ e.hom`. Apply `WidePullback.hom_ext` to reduce the goal to its premises.

Conclude with `hπ`. Rewrite using `[← WidePullback.π_arrow _ 0, ← Category.assoc, ← Category.assoc, hπ 0]`. Establish `h3 : Eqv _ (disc.map e'.hom ≫ disc.map mn) (tw q i)`. Rewrite using `[← Functor.map_comp, key, Functor.map_comp]`. Conclude with `(E.2.1 _ _ _ _ _).1 (hT k i) (E.1 _ _ _ (disc.mapIso e).isIso_hom)`.

Rewrite using `[hmn]`. Conclude with `(E.2.1 _ _ _ _ _).2.1 (E.1 _ _ _ (disc.mapIso e').isIso_hom) h3`. Establish `h2 : Eqv _ (cechAug (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap A B)))) ≫ spMap (Polynomial.C : A →+* Polynomial A)) (tw q i)`. Rewrite using `[← hsq]`. Conclude with `(E.2.1 _ _ _ _ _).1 hm h1`.

Conclude with `(E.2.1 _ _ _ _ _).2.1 h1' h2`.
-/
theorem hInv_of_integral (q : ℕ) [NeZero q] (A B : Type) [CommRing A] [CommRing B] [Algebra A B] :
    Algebra.IsIntegral A B → RingHom.ker (algebraMap A B) ≤ nilradical A → IsUnit (q : A) →
    (∀ k : ℕ, HInv q (PiTensorProduct A (fun _ : Fin (k + 1) => B))) → HInv q A := by
  intro hint hker hq hT i
  have hi : (algebraMap A B).IsIntegral := fun x => hint.isIntegral x
  obtain ⟨hf1, hf2⟩ := spec_integral_surj A B (algebraMap A B) hi hker
  obtain ⟨hf1', hf2'⟩ := spec_integral_surj _ _ (Polynomial.mapRingHom (algebraMap A B))
    (poly_isIntegral A B _ hi) (poly_ker A B _ hker)
  have hq' : IsUnit (q : Polynomial A) := by simpa using hq.map (Polynomial.C : A →+* Polynomial A)
  have E := GlobalTheory.T.etaleCohomologyEquivalence_basic_properties (ZMod q) (tw q i)
  have h1 := GlobalTheory.EtC.b4 q (Spec.map (CommRingCat.ofHom (algebraMap A B))) (isUnit_gamma q A hq) i
  have h1' := GlobalTheory.EtC.b4 q (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap A B))))
    (isUnit_gamma q _ hq') i
  let F : Arrow.mk (yoneda.map (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap A B))))) ⟶
      Arrow.mk (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A B)))) :=
    Arrow.homMk (yoneda.map (Spec.map (CommRingCat.ofHom (Polynomial.C : B →+* Polynomial B))))
      (yoneda.map (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)))) (by
        simp only [Arrow.mk_hom, ← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
        congr 3
        ext x <;> simp)
  let m : cech (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap A B)))) ⟶
      cech (Spec.map (CommRingCat.ofHom (algebraMap A B))) := Arrow.mapCechNerve F
  have hsq : m ≫ cechAug (Spec.map (CommRingCat.ofHom (algebraMap A B))) =
      cechAug (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap A B)))) ≫
        spMap (Polynomial.C : A →+* Polynomial A) := by
    clear E h1 h1' hT hf1 hf2 hf1' hf2' hint hker hq hq' hi
    refine NatTrans.ext (funext fun n => ?_)
    change WidePullback.lift _ _ _ ≫ WidePullback.base _ = WidePullback.base _ ≫ yoneda.map (Spec.map _)
    apply WidePullback.lift_base
  have hm : Eqv _ m (tw q i) := by
    refine GlobalTheory.T.levelwiseEquivalence_isEquivalence _ m _ (fun n => ?_)
    clear h1 h1' hf1 hf2 hf1' hf2' hint hker hq hq' hi hsq
    set k := n.unop.len
    let T := PiTensorProduct A (fun _ : Fin (k + 1) => B)
    let ι : Fin (k + 1) → (B →+* T) := fun j =>
      (PiTensorProduct.singleAlgHom (R := A) (A := fun _ : Fin (k + 1) => B) j).toRingHom
    have hι : ∀ j, (ι j).comp (algebraMap A B) = (ι 0).comp (algebraMap A B) := by
      intro j; ext x; simp [ι]
    have hu := tensor_univ A B k
    obtain ⟨e, he⟩ := yoneda_spec_widePullback A B T (algebraMap A B) k ι hι hu
    have hι' : ∀ j, (Polynomial.mapRingHom (ι j)).comp (Polynomial.mapRingHom (algebraMap A B)) =
        (Polynomial.mapRingHom (ι 0)).comp (Polynomial.mapRingHom (algebraMap A B)) := by
      intro j; rw [Polynomial.mapRingHom_comp, Polynomial.mapRingHom_comp, hι j]
    obtain ⟨e', he'⟩ := yoneda_spec_widePullback (Polynomial A) (Polynomial B) (Polynomial T)
      (Polynomial.mapRingHom (algebraMap A B)) k (fun j => Polynomial.mapRingHom (ι j)) hι'
      (poly_univ A B T (algebraMap A B) k ι (fun R _ g hg => hu R g hg))
    let mn : widePullback (yoneda.obj (Spec (CommRingCat.of (Polynomial A))))
        (fun _ : Fin (k + 1) => yoneda.obj (Spec (CommRingCat.of (Polynomial B))))
        (fun _ => yoneda.map (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap A B))))) ⟶
        widePullback (yoneda.obj (Spec (CommRingCat.of A)))
        (fun _ : Fin (k + 1) => yoneda.obj (Spec (CommRingCat.of B)))
        (fun _ => yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A B)))) :=
      WidePullback.lift (WidePullback.base _ ≫ yoneda.map (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))))
        (fun j => WidePullback.π _ j ≫ yoneda.map (Spec.map (CommRingCat.ofHom (Polynomial.C : B →+* Polynomial B))))
        (fun j => by
          rw [Category.assoc, ← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
            ← WidePullback.π_arrow _ j, Category.assoc, ← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
          congr 4
          ext x <;> simp)
    have hmn : m.app n = mn := rfl
    have hπ : ∀ j, (e'.hom ≫ mn) ≫ WidePullback.π _ j =
        (yoneda.map (Spec.map (CommRingCat.ofHom (Polynomial.C : T →+* Polynomial T))) ≫ e.hom) ≫ WidePullback.π _ j := by
      intro j
      rw [Category.assoc, WidePullback.lift_π, ← Category.assoc, he' j, Category.assoc, he j,
        ← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Functor.map_comp, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp]
      congr 3
      ext x <;> simp
    have key : e'.hom ≫ mn = yoneda.map (Spec.map (CommRingCat.ofHom (Polynomial.C : T →+* Polynomial T))) ≫ e.hom := by
      apply WidePullback.hom_ext
      · exact hπ
      · rw [← WidePullback.π_arrow _ 0, ← Category.assoc, ← Category.assoc, hπ 0]
    have h3 : Eqv _ (disc.map e'.hom ≫ disc.map mn) (tw q i) := by
      rw [← Functor.map_comp, key, Functor.map_comp]
      exact (E.2.1 _ _ _ _ _).1 (hT k i) (E.1 _ _ _ (disc.mapIso e).isIso_hom)
    rw [hmn]
    exact (E.2.1 _ _ _ _ _).2.1 (E.1 _ _ _ (disc.mapIso e').isIso_hom) h3
  have h2 : Eqv _ (cechAug (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap A B)))) ≫
      spMap (Polynomial.C : A →+* Polynomial A)) (tw q i) := by
    rw [← hsq]; exact (E.2.1 _ _ _ _ _).1 hm h1
  exact (E.2.1 _ _ _ _ _).2.1 h1' h2

end GlobalTheory.EtC.CechDescHInv
