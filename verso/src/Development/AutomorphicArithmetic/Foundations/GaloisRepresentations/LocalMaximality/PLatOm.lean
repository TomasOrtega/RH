import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.DualForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularFormsIsBundleProjectiveCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardOpenCoordinateRingIsFractionRingIsNoetheStatement
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

/- English proof (translation)
Take `⟨n, f, g, hf, hg, hfg⟩` from `Module.Finite.exists_comp_eq_id_of_projective A P`. Set `S` to `nonZeroDivisors A`. Establish `hsurj : ∀ w : W, ∃ (s : S) (p : P), (s : A) • w = (p : W)`. Introduce `w`. Establish `hw : w ∈ Submodule.span F (P : Set W)` using `hP ▸ Submodule.mem_top`.

Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem z hz => exact ⟨1, ⟨z, hz⟩, by simp⟩`. Consider the case `zero => exact ⟨1, 0, by simp⟩`. Consider the case `add a b _ _ ha hb`. Take `⟨s, p, h⟩` from `ha`.

Take `⟨t, q, h'⟩` from `hb`. Use `⟨s * t, (t : A) • p + (s : A) • q, ?_⟩` and prove the remaining obligations. Simplify using `only [Submonoid.coe_mul, smul_add, Submodule.coe_add, Submodule.coe_smul, ← h, ← h', smul_smul]`. Rewrite using `[mul_comm (t : A) (s : A)]`. Consider the case `smul c a _ ha`.

Take `⟨s, p, h⟩` from `ha`. Take `⟨b, t, rfl⟩` from `IsLocalization.exists_mk'_eq S c`. Use `⟨s * t, b • p, ?_⟩` and prove the remaining obligations. Establish `ht : algebraMap A F (t : A) * IsLocalization.mk' F b t = algebraMap A F b` using `IsLocalization.mk'_spec' F b t`. Rewrite using `[Submodule.coe_smul, ← h, Submonoid.coe_mul, mul_comm, mul_smul, smul_comm (s : A), ← algebraMap_smul F (t : A), smul_smul, ht, algebraMap_smul, smul_comm]`.

Establish `hloc : IsLocalizedModule S P.subtype`. Use `⟨fun s => ?_, fun w => ?_, fun {p q} h => ⟨1, ?_⟩⟩` and prove the remaining obligations. Establish `hs : algebraMap A F (s : A) ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2`. Rewrite using `[Module.End.isUnit_iff]`. Prove the components needed by the constructor for the conclusion.

Introduce `a b h`. Simplify using `only [Module.algebraMap_end_apply] at h`. Rewrite `h` using `[← algebraMap_smul F (s : A) a, ← algebraMap_smul F (s : A) b]`. Conclude with `smul_right_injective W hs h`. Introduce `b`.

Use `⟨(algebraMap A F (s : A))⁻¹ • b, ?_⟩` and prove the remaining obligations. Simplify using `only [Module.algebraMap_end_apply]`. Rewrite using `[← algebraMap_smul F (s : A), smul_smul, mul_inv_cancel₀ hs, one_smul]`. Take `⟨s, p, h⟩` from `hsurj w`. Conclude with `⟨(p, s), h⟩`.

Establish `: p = q` using `Subtype.ext h`. Simplify using `[this]`. Set `ψ : Fin n → P →ₗ[A] F` to `fun k => Algebra.linearMap A F ∘ₗ LinearMap.proj k ∘ₗ g`. Establish `hunit : ∀ s : S, IsUnit (algebraMap A (Module.End A F) (s : A))` using `fun s => IsLocalizedModule.map_units (S := S) (f := Algebra.linearMap A F) s`. Set `Ψ : Fin n → W →ₗ[A] F` to `fun k => IsLocalizedModule.lift S P.subtype (ψ k) hunit`.

Establish `hΨ : ∀ k (p : P), Ψ k (p : W) = ψ k p` using `fun k p => IsLocalizedModule.lift_apply S P.subtype (ψ k) hunit p`. Set `φ : Fin n → W →ₗ[F] F` to `fun k => (Ψ k).extendScalarsOfIsLocalization S F`. Establish `hφ : ∀ k (p : P), φ k (p : W) = algebraMap A F (g p k)` using `fun k p => hΨ k p`. Establish `hid : ∀ p : P, (p : W) = ∑ k, φ k (p : W) • ((f (Pi.single k 1) : P) : W)`. Introduce `p`.

Establish `h1 : f (g p) = p` using `congrArg (fun u => u p) hfg`. Establish `h2 : g p = ∑ k, g p k • (Pi.single k (1 : A) : Fin n → A)`. Use extensionality with `j`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Use `conv_lhs => rw [← h1, h2]`.

Simplify using `[map_sum, hφ, algebraMap_smul]`. Use `⟨n, fun k => (f (Pi.single k 1) : P), φ, fun k => (f (Pi.single k 1)).2, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `k p hp`. Conclude with `⟨g ⟨p, hp⟩ k, (hφ k ⟨p, hp⟩).symm⟩`. Establish `: (LinearMap.id : W →ₗ[F] W) = ∑ k, (φ k).smulRight ((f (Pi.single k 1) : P) : W)`.

Use `LinearMap.ext_on hP ?_` and prove the remaining obligations. Introduce `p hp`. Simplify using `using hid ⟨p, hp⟩`. Introduce `w`. Simplify using `using congrArg (fun u => u w) this`.
-/
private theorem dual_of_lattice {A F W : Type} [CommRing A] [IsDomain A] [Field F] [Algebra A F] [IsFractionRing A F]
    [AddCommGroup W] [Module F W] [Module A W] [IsScalarTower A F W] (P : Submodule A W)
    [Module.Finite A P] [Module.Projective A P] (hP : Submodule.span F (P : Set W) = ⊤) :
    ∃ (n : ℕ) (v : Fin n → W) (φ : Fin n → W →ₗ[F] F), (∀ k, v k ∈ P) ∧
      (∀ k, ∀ p ∈ P, φ k p ∈ (algebraMap A F).range) ∧ ∀ w, w = ∑ k, φ k w • v k := by
  classical
  obtain ⟨n, f, g, hf, hg, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective A P
  let S := nonZeroDivisors A
  have hsurj : ∀ w : W, ∃ (s : S) (p : P), (s : A) • w = (p : W) := by
    intro w
    have hw : w ∈ Submodule.span F (P : Set W) := hP ▸ Submodule.mem_top
    induction hw using Submodule.span_induction with
    | mem z hz => exact ⟨1, ⟨z, hz⟩, by simp⟩
    | zero => exact ⟨1, 0, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨s, p, h⟩ := ha
      obtain ⟨t, q, h'⟩ := hb
      refine ⟨s * t, (t : A) • p + (s : A) • q, ?_⟩
      simp only [Submonoid.coe_mul, smul_add, Submodule.coe_add, Submodule.coe_smul, ← h, ← h', smul_smul]
      rw [mul_comm (t : A) (s : A)]
    | smul c a _ ha =>
      obtain ⟨s, p, h⟩ := ha
      obtain ⟨b, t, rfl⟩ := IsLocalization.exists_mk'_eq S c
      refine ⟨s * t, b • p, ?_⟩
      have ht : algebraMap A F (t : A) * IsLocalization.mk' F b t = algebraMap A F b := IsLocalization.mk'_spec' F b t
      rw [Submodule.coe_smul, ← h, Submonoid.coe_mul, mul_comm, mul_smul, smul_comm (s : A), ← algebraMap_smul F (t : A),
        smul_smul, ht, algebraMap_smul, smul_comm]
  have hloc : IsLocalizedModule S P.subtype := by
    refine ⟨fun s => ?_, fun w => ?_, fun {p q} h => ⟨1, ?_⟩⟩
    · have hs : algebraMap A F (s : A) ≠ 0 :=
        IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
      rw [Module.End.isUnit_iff]
      constructor
      · intro a b h
        simp only [Module.algebraMap_end_apply] at h
        rw [← algebraMap_smul F (s : A) a, ← algebraMap_smul F (s : A) b] at h
        exact smul_right_injective W hs h
      · intro b
        refine ⟨(algebraMap A F (s : A))⁻¹ • b, ?_⟩
        simp only [Module.algebraMap_end_apply]
        rw [← algebraMap_smul F (s : A), smul_smul, mul_inv_cancel₀ hs, one_smul]
    · obtain ⟨s, p, h⟩ := hsurj w
      exact ⟨(p, s), h⟩
    · have : p = q := Subtype.ext h
      simp [this]
  let ψ : Fin n → P →ₗ[A] F := fun k => Algebra.linearMap A F ∘ₗ LinearMap.proj k ∘ₗ g
  have hunit : ∀ s : S, IsUnit (algebraMap A (Module.End A F) (s : A)) := fun s =>
    IsLocalizedModule.map_units (S := S) (f := Algebra.linearMap A F) s
  let Ψ : Fin n → W →ₗ[A] F := fun k => IsLocalizedModule.lift S P.subtype (ψ k) hunit
  have hΨ : ∀ k (p : P), Ψ k (p : W) = ψ k p := fun k p =>
    IsLocalizedModule.lift_apply S P.subtype (ψ k) hunit p
  let φ : Fin n → W →ₗ[F] F := fun k => (Ψ k).extendScalarsOfIsLocalization S F
  have hφ : ∀ k (p : P), φ k (p : W) = algebraMap A F (g p k) := fun k p => hΨ k p
  have hid : ∀ p : P, (p : W) = ∑ k, φ k (p : W) • ((f (Pi.single k 1) : P) : W) := by
    intro p
    have h1 : f (g p) = p := congrArg (fun u => u p) hfg
    have h2 : g p = ∑ k, g p k • (Pi.single k (1 : A) : Fin n → A) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [← h1, h2]
    simp [map_sum, hφ, algebraMap_smul]
  refine ⟨n, fun k => (f (Pi.single k 1) : P), φ, fun k => (f (Pi.single k 1)).2, ?_, ?_⟩
  · rintro k p hp
    exact ⟨g ⟨p, hp⟩ k, (hφ k ⟨p, hp⟩).symm⟩
  · have : (LinearMap.id : W →ₗ[F] W) = ∑ k, (φ k).smulRight ((f (Pi.single k 1) : P) : W) := by
      refine LinearMap.ext_on hP ?_
      intro p hp
      simpa using hid ⟨p, hp⟩
    intro w
    simpa using congrArg (fun u => u w) this

/- English proof (translation)
Use `haveI : IsFractionRing (rA ℂ x {i}) F := (GlobalTheory.T.standardOpenCoordinateRing_isFractionRing_isNoetherianRing ℂ F d x hx {i} (Finset.singleton_nonempty i)).1`. Take `⟨s, hs, hsF⟩` from `hL.fg i`. Set `P : Submodule (rA ℂ x {i}) W` to `Submodule.span (rA ℂ x {i}) (L {i} : Set W)`. Establish `hPs : P = Submodule.span (rA ℂ x {i}) (s : Set W)`. Express the relevant statement in the definitionally equal form `Submodule.span (rA ℂ x {i}) (L {i} : Set W) = _`.

Rewrite using `[hs]`. Conclude with `Submodule.span_eq _`. Use `haveI : Module.Finite (rA ℂ x {i}) P := Module.Finite.iff_fg.2 ⟨s, hPs.symm⟩`. Use `haveI : Module.Projective (rA ℂ x {i}) P := hL.proj i`. Establish `hP : Submodule.span F (P : Set W) = ⊤`.

Rewrite using `[eq_top_iff, ← hsF]`. Use `Submodule.span_mono fun z hz => ?_` and prove the remaining obligations. Rewrite using `[hPs]`. Conclude with `Submodule.subset_span hz`. Take `⟨n, v, φ, hv, hφ, hid⟩` from `dual_of_lattice P hP`.

Take `⟨r, hr⟩` from `e.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 he)`. Establish `hre : ∀ w, r (e w) = w` using `fun w => LinearMap.congr_fun hr w`. Establish `hLI` using `hL.loc I i hi`. Establish `hLii` using `hL.loc {i} i (Finset.mem_singleton_self i)`. Establish `hPL : ∀ p ∈ P, p ∈ L {i}` using `fun p hp => by`.

Rewrite using `[hLii]`. Conclude with `hp`. Establish `hLsub : ∀ w ∈ L {i}, w ∈ L I` using `fun w hw => by`. Rewrite using `[hLI]`. Conclude with `Submodule.subset_span hw`.

Establish `hmono : rA ℂ x {i} ≤ rA ℂ x I` using `Algebra.adjoin_mono fun y ⟨a, ha, h⟩ => ⟨a, by rw [Finset.mem_singleton.1 ha]; exact hi, h⟩`. Establish `hsm : ∀ c ∈ rA ℂ x I, ∀ w ∈ L I, c • w ∈ L I` using `fun c hc w hw => by`. Rewrite `hw`, the goal using `[hLI]`. Conclude with `Submodule.smul_mem (Submodule.span (rA ℂ x I) (L {i} : Set W)) (⟨c, hc⟩ : rA ℂ x I) hw`. Establish `hval : ∀ k, ∀ w ∈ L I, φ k w ∈ rA ℂ x I`.

Introduce `k w hw`. Rewrite `hw` using `[hLI]`. Establish `hw' : w ∈ Submodule.span (rA ℂ x I) (L {i} : Set W)` using `hw`. Use `clear hw`. Proceed by induction on `hw' using Submodule.span_induction with`.

Consider the case `mem z hz`. Take `⟨y, hy⟩` from `hφ k z (Submodule.subset_span hz)`. Rewrite using `[← hy]`. Conclude with `hmono y.2`. Consider the case `zero => simpa using (rA ℂ x I).zero_mem`.

Consider the case `add a b _ _ ha hb`. Rewrite using `[map_add]`. Conclude with `(rA ℂ x I).add_mem ha hb`. Consider the case `smul c a _ ha`. Establish `: φ k (c • a) = (c : F) * φ k a`.

Rewrite using `[show c • a = (c : F) • a from rfl, map_smul, smul_eq_mul]`. Rewrite using `[this]`. Conclude with `(rA ℂ x I).mul_mem c.2 ha`. Use `⟨⟨fun c hc m hm => ?_, n, fun k => e (v k), fun k => φ k ∘ₗ r, fun k => ?_, fun k m hm => ?_, fun m hm => ?_⟩, fun w => ?_⟩` and prove the remaining obligations. Take `⟨w, rfl⟩` from `hM m hm`.

Rewrite using `[← map_smul]`. Conclude with `(hML _).1 (hsm c hc w ((hML w).2 hm))`. Conclude with `(hML _).1 (hLsub _ (hPL _ (hv k)))`. Take `⟨w, rfl⟩` from `hM m hm`. Simplify `hval k w ((hML w).2 hm)` using `[hre]`.

Take `⟨w, rfl⟩` from `hM m hm`. Simplify using `only [LinearMap.comp_apply, hre, ← map_smul, ← map_sum]`. Conclude with `congrArg e (hid w)`. Establish `hw : w ∈ Submodule.span F (s : Set W)` using `hsF ▸ Submodule.mem_top`. Establish `hsL : ∀ z ∈ s, e z ∈ M` using `fun z hz => (hML z).1 (hLsub z (hPL z (by rw [hPs]; exact Submodule.subset_span hz)))`.

Establish `hmap : (Submodule.span F (s : Set W)).map e ≤ Submodule.span F (M : Set V)`. Rewrite using `[Submodule.map_span]`. Use `Submodule.span_mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨z, hz, rfl⟩`. Conclude with `hsL z hz`.

Conclude with `hmap ⟨w, hw, rfl⟩`.
-/
private theorem lat_of_isBundle {F : Type} [Field F] [Algebra ℂ F] {d : ℕ} {x : Fin (d + 1) → F} (hx : IsPd ℂ x)
    {W V : Type} [AddCommGroup W] [Module F W] [Module ℂ W] [IsScalarTower ℂ F W]
    [AddCommGroup V] [Module F V] [Module ℂ V] [IsScalarTower ℂ F V] (e : W →ₗ[F] V)
    (he : Function.Injective e) (L : Finset (Fin (d + 1)) → Submodule ℂ W) (hL : IsBundle ℂ x L)
    (I : Finset (Fin (d + 1))) (i : Fin (d + 1)) (hi : i ∈ I) (M : Submodule ℂ V)
    (hM : ∀ m ∈ M, ∃ w, e w = m) (hML : ∀ w, w ∈ L I ↔ e w ∈ M) :
    Lat (rA ℂ x I) M ∧ ∀ w, e w ∈ Submodule.span F (M : Set V) := by
  classical
  haveI : IsFractionRing (rA ℂ x {i}) F := (GlobalTheory.T.standardOpenCoordinateRing_isFractionRing_isNoetherianRing ℂ F d x hx {i} (Finset.singleton_nonempty i)).1
  obtain ⟨s, hs, hsF⟩ := hL.fg i
  let P : Submodule (rA ℂ x {i}) W := Submodule.span (rA ℂ x {i}) (L {i} : Set W)
  have hPs : P = Submodule.span (rA ℂ x {i}) (s : Set W) := by
    change Submodule.span (rA ℂ x {i}) (L {i} : Set W) = _
    rw [hs]
    exact Submodule.span_eq _
  haveI : Module.Finite (rA ℂ x {i}) P := Module.Finite.iff_fg.2 ⟨s, hPs.symm⟩
  haveI : Module.Projective (rA ℂ x {i}) P := hL.proj i
  have hP : Submodule.span F (P : Set W) = ⊤ := by
    rw [eq_top_iff, ← hsF]
    refine Submodule.span_mono fun z hz => ?_
    rw [hPs]
    exact Submodule.subset_span hz
  obtain ⟨n, v, φ, hv, hφ, hid⟩ := dual_of_lattice P hP
  obtain ⟨r, hr⟩ := e.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 he)
  have hre : ∀ w, r (e w) = w := fun w => LinearMap.congr_fun hr w
  have hLI := hL.loc I i hi
  have hLii := hL.loc {i} i (Finset.mem_singleton_self i)
  have hPL : ∀ p ∈ P, p ∈ L {i} := fun p hp => by
    rw [hLii]
    exact hp
  have hLsub : ∀ w ∈ L {i}, w ∈ L I := fun w hw => by
    rw [hLI]
    exact Submodule.subset_span hw
  have hmono : rA ℂ x {i} ≤ rA ℂ x I := Algebra.adjoin_mono fun y ⟨a, ha, h⟩ =>
    ⟨a, by rw [Finset.mem_singleton.1 ha]; exact hi, h⟩
  have hsm : ∀ c ∈ rA ℂ x I, ∀ w ∈ L I, c • w ∈ L I := fun c hc w hw => by
    rw [hLI] at hw ⊢
    exact Submodule.smul_mem (Submodule.span (rA ℂ x I) (L {i} : Set W)) (⟨c, hc⟩ : rA ℂ x I) hw
  have hval : ∀ k, ∀ w ∈ L I, φ k w ∈ rA ℂ x I := by
    intro k w hw
    rw [hLI] at hw
    have hw' : w ∈ Submodule.span (rA ℂ x I) (L {i} : Set W) := hw
    clear hw
    induction hw' using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨y, hy⟩ := hφ k z (Submodule.subset_span hz)
      rw [← hy]
      exact hmono y.2
    | zero => simpa using (rA ℂ x I).zero_mem
    | add a b _ _ ha hb =>
      rw [map_add]
      exact (rA ℂ x I).add_mem ha hb
    | smul c a _ ha =>
      have : φ k (c • a) = (c : F) * φ k a := by
        rw [show c • a = (c : F) • a from rfl, map_smul, smul_eq_mul]
      rw [this]
      exact (rA ℂ x I).mul_mem c.2 ha
  refine ⟨⟨fun c hc m hm => ?_, n, fun k => e (v k), fun k => φ k ∘ₗ r, fun k => ?_, fun k m hm => ?_, fun m hm => ?_⟩, fun w => ?_⟩
  · obtain ⟨w, rfl⟩ := hM m hm
    rw [← map_smul]
    exact (hML _).1 (hsm c hc w ((hML w).2 hm))
  · exact (hML _).1 (hLsub _ (hPL _ (hv k)))
  · obtain ⟨w, rfl⟩ := hM m hm
    simpa [hre] using hval k w ((hML w).2 hm)
  · obtain ⟨w, rfl⟩ := hM m hm
    simp only [LinearMap.comp_apply, hre, ← map_smul, ← map_sum]
    exact congrArg e (hid w)
  · have hw : w ∈ Submodule.span F (s : Set W) := hsF ▸ Submodule.mem_top
    have hsL : ∀ z ∈ s, e z ∈ M := fun z hz => (hML z).1 (hLsub z (hPL z (by rw [hPs]; exact Submodule.subset_span hz)))
    have hmap : (Submodule.span F (s : Set W)).map e ≤ Submodule.span F (M : Set V) := by
      rw [Submodule.map_span]
      refine Submodule.span_mono ?_
      rintro _ ⟨z, hz, rfl⟩
      exact hsL z hz
    exact hmap ⟨w, hw, rfl⟩

/- English proof (translation)
Introduce `F K _ _ _ _ _ _ d x hc a I hI`. Take `⟨i, hi⟩` from `hI`. Establish `hB` using `GlobalTheory.T.regularForms_isBundle_projectiveCover ℂ F K d (xv x) hc a (⋀[K]^a Ω[K⁄ℂ]) (⋀[K]^a Ω[K⁄ℂ]).subtype Subtype.val_injective (Submodule.range_subtype _)`. Establish `hle : omB ℂ K (rB ℂ K (xv x) I) a ≤ (⋀[K]^a Ω[K⁄ℂ]).restrictScalars ℂ`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨b, -, v, -, rfl⟩`. Use `(⋀[K]^a Ω[K⁄ℂ]).smul_mem b ?_` and prove the remaining obligations. Rewrite using `[← ExteriorAlgebra.ιMulti_span_fixedDegree]`. Conclude with `Submodule.subset_span ⟨_, rfl⟩`. Establish `key` using `lat_of_isBundle hc.pd (((⋀[K]^a Ω[K⁄ℂ]).subtype).restrictScalars F) Subtype.val_injective _ hB I i hi (omB ℂ K (rB ℂ K (xv x) I) a) (fun m hm => ⟨⟨m, hle hm⟩, rfl⟩) (fun w => Iff.rfl)`.

Conclude with `⟨key.1, fun w hw => key.2 ⟨w, hw⟩⟩`.
-/
theorem UpperTheory.Gal.productCup_of_system.latOm_of :
    LatOm := by
  intro F K _ _ _ _ _ _ d x hc a I hI
  obtain ⟨i, hi⟩ := hI
  have hB := GlobalTheory.T.regularForms_isBundle_projectiveCover ℂ F K d (xv x) hc a (⋀[K]^a Ω[K⁄ℂ]) (⋀[K]^a Ω[K⁄ℂ]).subtype
    Subtype.val_injective (Submodule.range_subtype _)
  have hle : omB ℂ K (rB ℂ K (xv x) I) a ≤ (⋀[K]^a Ω[K⁄ℂ]).restrictScalars ℂ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, -, v, -, rfl⟩
    refine (⋀[K]^a Ω[K⁄ℂ]).smul_mem b ?_
    rw [← ExteriorAlgebra.ιMulti_span_fixedDegree]
    exact Submodule.subset_span ⟨_, rfl⟩
  have key := lat_of_isBundle hc.pd (((⋀[K]^a Ω[K⁄ℂ]).subtype).restrictScalars F) Subtype.val_injective _ hB I i hi
    (omB ℂ K (rB ℂ K (xv x) I) a) (fun m hm => ⟨⟨m, hle hm⟩, rfl⟩) (fun w => Iff.rfl)
  exact ⟨key.1, fun w hw => key.2 ⟨w, hw⟩⟩
