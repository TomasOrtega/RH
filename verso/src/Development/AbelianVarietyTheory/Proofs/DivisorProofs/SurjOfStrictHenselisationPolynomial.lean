import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStrictHenselisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndEtaleLocalizedPiecesTrans
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomExtLocalization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveResidueCompEtaleHenselian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpecialisationToStrictlyHenselian
open IsLocalRing Polynomial
open GlobalTheory.EtC

namespace GlobalTheory

/- English proof (translation)
Introduce `T _ A _ _ _ _ hSH hA`. Take `⟨hHA, hsepA⟩` from `hSH`. Set `y : Ideal (Polynomial T)` to `(maximalIdeal A).comap (algebraMap (Polynomial T) A)`. Use `haveI : y.IsPrime := Ideal.comap_isPrime _ _`. Take `⟨O, _, algRO, _, hloc, hsc, -, -, -, hind⟩` from `GlobalTheory.exists_strictHenselisation (Localization.AtPrime y) (SeparableClosure (ResidueField (Localization.AtPrime y)))`.

Use `letI algPO : Algebra (Polynomial T) O := ((algebraMap (Localization.AtPrime y) O).comp (algebraMap (Polynomial T) (Localization.AtPrime y))).toAlgebra`. Use `letI algTO : Algebra T O := ((algebraMap (Polynomial T) O).comp (algebraMap T (Polynomial T))).toAlgebra`. Use `haveI t1 : IsScalarTower T (Polynomial T) O := IsScalarTower.of_algebraMap_eq' rfl`. Use `haveI t2 : IsScalarTower (Polynomial T) (Localization.AtPrime y) O := IsScalarTower.of_algebraMap_eq' rfl`. Establish `hP` using `GlobalTheory.indEtale_localPieces_trans (Polynomial T) (Localization.AtPrime y) O ⟨Unit, inferInstance, inferInstance, inferInstance, fun _ => ⊤, monotone_const, fun _ => ⟨(), Algebra.mem_top⟩, fun _ => ⟨Polynomial T, inferInstance, inferInstance, inferInstance, y, inferInstance, …`.

Establish `hRO : (maximalIdeal O).comap (algebraMap (Localization.AtPrime y) O) = maximalIdeal (Localization.AtPrime y)`. Use extensionality with `x`. Simplify using `only [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff]`. Establish `hyO : (maximalIdeal O).comap (algebraMap (Polynomial T) O) = y`. Rewrite using `[IsScalarTower.algebraMap_eq (Polynomial T) (Localization.AtPrime y) O, ← Ideal.comap_comap, hRO]`.

Conclude with `Localization.AtPrime.comap_maximalIdeal`. Establish `hkO : ∀ r : Polynomial T, algebraMap (Polynomial T) (ResidueField O) r = 0 ↔ r ∈ y`. Introduce `r`. Rewrite using `[IsScalarTower.algebraMap_apply (Polynomial T) O (ResidueField O), ResidueField.algebraMap_eq, residue_eq_zero_iff, ← hyO, Ideal.mem_comap]`. Establish `hkA : ∀ r : Polynomial T, algebraMap (Polynomial T) (ResidueField A) r = 0 ↔ r ∈ y`.

Introduce `r`. Rewrite using `[IsScalarTower.algebraMap_apply (Polynomial T) A (ResidueField A), ResidueField.algebraMap_eq, residue_eq_zero_iff]`. Both sides reduce to the same expression. Use `letI algyO : Algebra y.ResidueField (ResidueField O) := (Ideal.ResidueField.lift y (algebraMap (Polynomial T) (ResidueField O)) (fun r hr => (hkO r).2 hr) (fun r hr => by`. Simplify using `only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff]`.

Conclude with `isUnit_iff_ne_zero.mpr (fun h => hr ((hkO r).1 h)))).toAlgebra`. Use `haveI : IsScalarTower (Polynomial T) y.ResidueField (ResidueField O) := .of_algebraMap_eq fun r => by`. Rewrite using `[RingHom.algebraMap_toAlgebra]`. Conclude with `(Ideal.ResidueField.lift_algebraMap y _ _ _ r).symm`. Use `letI algyA : Algebra y.ResidueField (ResidueField A) := (Ideal.ResidueField.lift y (algebraMap (Polynomial T) (ResidueField A)) (fun r hr => (hkA r).2 hr) (fun r hr => by`.

Simplify using `only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff]`. Conclude with `isUnit_iff_ne_zero.mpr (fun h => hr ((hkA r).1 h)))).toAlgebra`. Use `haveI : IsScalarTower (Polynomial T) y.ResidueField (ResidueField A) := .of_algebraMap_eq fun r => by`. Rewrite using `[RingHom.algebraMap_toAlgebra]`. Conclude with `(Ideal.ResidueField.lift_algebraMap y _ _ _ r).symm`.

Establish `hsepO : ∀ s : O, IsSeparable y.ResidueField (algebraMap O (ResidueField O) s)`. Introduce `s`. Take `⟨ι, _, _, _, Si, -, hcov, hpc⟩` from `hP`. Take `⟨i, hi⟩` from `hcov s`. Take `⟨B, _, _, _, q, _, ⟨e⟩⟩` from `hpc i`.

Set `F : Localization.AtPrime q →ₐ[Polynomial T] ResidueField O` to `(IsScalarTower.toAlgHom (Polynomial T) O (ResidueField O)).comp ((Si i).val.comp e.toAlgHom)`. Set `f : B →ₐ[Polynomial T] ResidueField O` to `F.comp (IsScalarTower.toAlgHom (Polynomial T) B (Localization.AtPrime q))`. Take `⟨⟨a, t⟩, hat⟩` from `IsLocalization.mk'_surjective q.primeCompl (e.symm ⟨s, hi⟩)`. Establish `hs : algebraMap O (ResidueField O) s = F (IsLocalization.mk' _ a t)`. Simplify using `only [F, AlgHom.comp_apply, hat]`.

Simplify using the standard rewrite rules. Establish `hft : f t ≠ 0`. Establish `: IsUnit (f t)` using `(IsLocalization.map_units (Localization.AtPrime q) t).map F`. Conclude with `this.ne_zero`. Establish `hmul : F (IsLocalization.mk' _ a t) * f t = f a`.

Simplify using `only [f, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', ← map_mul, IsLocalization.mk'_spec]`. Establish `hx : algebraMap O (ResidueField O) s = f a * (f t)⁻¹`. Rewrite using `[hs, eq_mul_inv_iff_mul_eq₀ hft, hmul]`. Rewrite using `[hx, ← mem_separableClosure_iff]`. Apply the tactic sequence `refine mul_mem ?_ (inv_mem ?_) <;> rw [mem_separableClosure_iff] <;>`.

Conclude with `GlobalTheory.Specialise.sepEtale (Polynomial T) B y _ f _`. Use `haveI : Algebra.IsSeparable y.ResidueField (ResidueField O) := ⟨fun x => by`. Take `⟨s, rfl⟩` from `residue_surjective x`. Use `hsepO s` as an intermediate fact. Rewrite using `[ResidueField.algebraMap_eq] at this⟩` and apply the resulting hypothesis.

Use `haveI : IsSepClosure y.ResidueField (ResidueField O) := ⟨hsc, inferInstance⟩`. Set `L` to `separableClosure y.ResidueField (ResidueField A)`. Set `e : ResidueField O ≃ₐ[y.ResidueField] L` to `IsSepClosure.equiv y.ResidueField (ResidueField O) L`. Set `ι : ResidueField O →ₐ[y.ResidueField] ResidueField A` to `L.val.comp e.toAlgHom`. Set `ψ₀ : O →ₐ[Polynomial T] ResidueField A` to `(ι.restrictScalars (Polynomial T)).comp (IsScalarTower.toAlgHom (Polynomial T) O (ResidueField O))`.

Take `⟨π, hπ⟩` from `(GlobalTheory.IndEtaleHensel.bijective_residue_comp (Polynomial T) O A hP).2 ψ₀`. Use `⟨O, inferInstance, algTO, algPO, t1, inferInstance, hsc, π, ?_, hP⟩` and prove the remaining obligations. Introduce `b`. Take `⟨E, _, _, _, φ, hb⟩` from `hA b`. Take `⟨e0, rfl⟩` from `(AlgHom.mem_range φ).1 hb`.

Set `f : E →ₐ[Polynomial T] ResidueField A` to `(IsScalarTower.toAlgHom (Polynomial T) A (ResidueField A)).comp φ`. Establish `hfL : ∀ x, f x ∈ L` using `fun x => mem_separableClosure_iff.2 (GlobalTheory.Specialise.sepEtale (Polynomial T) E y (ResidueField A) f x)`. Set `g : E →ₐ[Polynomial T] ResidueField O` to `{ toRingHom := (e.symm : L →+* ResidueField O).comp (f.toRingHom.codRestrict L hfL) commutes' := fun r => by`. Apply `e.injective` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `e (e.symm ⟨f (algebraMap _ E r), hfL _⟩) = _`.

Rewrite using `[AlgEquiv.apply_symm_apply]`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[IsScalarTower.algebraMap_apply (Polynomial T) y.ResidueField (ResidueField O), AlgEquiv.commutes]`. Express the relevant statement in the definitionally equal form `f (algebraMap _ E r) = _`. Rewrite using `[AlgHom.commutes, IsScalarTower.algebraMap_apply (Polynomial T) y.ResidueField (ResidueField A)]`.

Use `rfl }`. Take `⟨ψ, hψ⟩` from `(GlobalTheory.EtaleHensel.bijective_residue_comp (Polynomial T) E O).2 g`. Establish `hcomp : π.comp ψ = φ`. Apply `(GlobalTheory.EtaleHensel.bijective_residue_comp (Polynomial T) E A).1` to reduce the goal to its premises. Simplify using `only`.

Use extensionality with `x`. Establish `h1` using `DFunLike.congr_fun hπ (ψ x)`. Establish `h2` using `DFunLike.congr_fun hψ x`. Simplify using `only [AlgHom.comp_apply] at h1 h2 ⊢`. Rewrite using `[h1]`.

Express the relevant statement in the definitionally equal form `ι (IsScalarTower.toAlgHom (Polynomial T) O (ResidueField O) (ψ x)) = f x`. Rewrite using `[h2]`. Express the relevant statement in the definitionally equal form `((e (e.symm ⟨f x, hfL x⟩) : L) : ResidueField A) = f x`. Rewrite using `[AlgEquiv.apply_symm_apply]`. Conclude with `⟨ψ e0, DFunLike.congr_fun hcomp e0⟩`.
-/
theorem surj_of_strictHenselisation_polynomial : ∀ (T : Type) [CommRing T] (A : Type) [CommRing A]
    [Algebra (Polynomial T) A] [Algebra T A] [IsScalarTower T (Polynomial T) A], SH A →
    (∀ a : A, ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E)
      (_ : Algebra.Etale (Polynomial T) E) (φ : E →ₐ[Polynomial T] A), a ∈ φ.range) →
    ∃ (O : Type) (_ : CommRing O) (_ : Algebra T O) (_ : Algebra (Polynomial T) O)
      (_ : IsScalarTower T (Polynomial T) O) (_ : HenselianLocalRing O)
      (_ : IsSepClosed (IsLocalRing.ResidueField O)) (π : O →ₐ[Polynomial T] A),
      Function.Surjective π ∧ (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·))
        (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧
        (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (E : Type) (_ : CommRing E)
          (_ : Algebra (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E) (P : Ideal E)
          (_ : P.IsPrime), Nonempty (Localization.AtPrime P ≃ₐ[(Polynomial T)] Si i)) := by
  intro T _ A _ _ _ _ hSH hA
  obtain ⟨hHA, hsepA⟩ := hSH
  let y : Ideal (Polynomial T) := (maximalIdeal A).comap (algebraMap (Polynomial T) A)
  haveI : y.IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨O, _, algRO, _, hloc, hsc, -, -, -, hind⟩ :=
    GlobalTheory.exists_strictHenselisation (Localization.AtPrime y)
      (SeparableClosure (ResidueField (Localization.AtPrime y)))
  letI algPO : Algebra (Polynomial T) O :=
    ((algebraMap (Localization.AtPrime y) O).comp
      (algebraMap (Polynomial T) (Localization.AtPrime y))).toAlgebra
  letI algTO : Algebra T O := ((algebraMap (Polynomial T) O).comp (algebraMap T (Polynomial T))).toAlgebra
  haveI t1 : IsScalarTower T (Polynomial T) O := IsScalarTower.of_algebraMap_eq' rfl
  haveI t2 : IsScalarTower (Polynomial T) (Localization.AtPrime y) O :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hP := GlobalTheory.indEtale_localPieces_trans (Polynomial T) (Localization.AtPrime y) O
    ⟨Unit, inferInstance, inferInstance, inferInstance, fun _ => ⊤, monotone_const,
      fun _ => ⟨(), Algebra.mem_top⟩,
      fun _ => ⟨Polynomial T, inferInstance, inferInstance, inferInstance, y, inferInstance,
        ⟨Subalgebra.topEquiv.symm⟩⟩⟩ hind

  have hRO : (maximalIdeal O).comap (algebraMap (Localization.AtPrime y) O) =
      maximalIdeal (Localization.AtPrime y) := by
    ext x
    simp only [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff]
  have hyO : (maximalIdeal O).comap (algebraMap (Polynomial T) O) = y := by
    rw [IsScalarTower.algebraMap_eq (Polynomial T) (Localization.AtPrime y) O, ← Ideal.comap_comap,
      hRO]
    exact Localization.AtPrime.comap_maximalIdeal
  have hkO : ∀ r : Polynomial T, algebraMap (Polynomial T) (ResidueField O) r = 0 ↔ r ∈ y := by
    intro r
    rw [IsScalarTower.algebraMap_apply (Polynomial T) O (ResidueField O), ResidueField.algebraMap_eq,
      residue_eq_zero_iff, ← hyO, Ideal.mem_comap]
  have hkA : ∀ r : Polynomial T, algebraMap (Polynomial T) (ResidueField A) r = 0 ↔ r ∈ y := by
    intro r
    rw [IsScalarTower.algebraMap_apply (Polynomial T) A (ResidueField A), ResidueField.algebraMap_eq,
      residue_eq_zero_iff]
    rfl
  letI algyO : Algebra y.ResidueField (ResidueField O) :=
    (Ideal.ResidueField.lift y (algebraMap (Polynomial T) (ResidueField O)) (fun r hr => (hkO r).2 hr)
      (fun r hr => by
        simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
        exact isUnit_iff_ne_zero.mpr (fun h => hr ((hkO r).1 h)))).toAlgebra
  haveI : IsScalarTower (Polynomial T) y.ResidueField (ResidueField O) := .of_algebraMap_eq fun r => by
    rw [RingHom.algebraMap_toAlgebra]
    exact (Ideal.ResidueField.lift_algebraMap y _ _ _ r).symm
  letI algyA : Algebra y.ResidueField (ResidueField A) :=
    (Ideal.ResidueField.lift y (algebraMap (Polynomial T) (ResidueField A)) (fun r hr => (hkA r).2 hr)
      (fun r hr => by
        simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
        exact isUnit_iff_ne_zero.mpr (fun h => hr ((hkA r).1 h)))).toAlgebra
  haveI : IsScalarTower (Polynomial T) y.ResidueField (ResidueField A) := .of_algebraMap_eq fun r => by
    rw [RingHom.algebraMap_toAlgebra]
    exact (Ideal.ResidueField.lift_algebraMap y _ _ _ r).symm

  have hsepO : ∀ s : O, IsSeparable y.ResidueField (algebraMap O (ResidueField O) s) := by
    intro s
    obtain ⟨ι, _, _, _, Si, -, hcov, hpc⟩ := hP
    obtain ⟨i, hi⟩ := hcov s
    obtain ⟨B, _, _, _, q, _, ⟨e⟩⟩ := hpc i
    let F : Localization.AtPrime q →ₐ[Polynomial T] ResidueField O :=
      (IsScalarTower.toAlgHom (Polynomial T) O (ResidueField O)).comp ((Si i).val.comp e.toAlgHom)
    let f : B →ₐ[Polynomial T] ResidueField O :=
      F.comp (IsScalarTower.toAlgHom (Polynomial T) B (Localization.AtPrime q))
    obtain ⟨⟨a, t⟩, hat⟩ := IsLocalization.mk'_surjective q.primeCompl (e.symm ⟨s, hi⟩)
    have hs : algebraMap O (ResidueField O) s = F (IsLocalization.mk' _ a t) := by
      simp only [F, AlgHom.comp_apply, hat]
      simp
    have hft : f t ≠ 0 := by
      have : IsUnit (f t) :=
        (IsLocalization.map_units (Localization.AtPrime q) t).map F
      exact this.ne_zero
    have hmul : F (IsLocalization.mk' _ a t) * f t = f a := by
      simp only [f, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', ← map_mul,
        IsLocalization.mk'_spec]
    have hx : algebraMap O (ResidueField O) s = f a * (f t)⁻¹ := by
      rw [hs, eq_mul_inv_iff_mul_eq₀ hft, hmul]
    rw [hx, ← mem_separableClosure_iff]
    refine mul_mem ?_ (inv_mem ?_) <;> rw [mem_separableClosure_iff] <;>
      exact GlobalTheory.Specialise.sepEtale (Polynomial T) B y _ f _
  haveI : Algebra.IsSeparable y.ResidueField (ResidueField O) := ⟨fun x => by
    obtain ⟨s, rfl⟩ := residue_surjective x
    have := hsepO s
    rwa [ResidueField.algebraMap_eq] at this⟩
  haveI : IsSepClosure y.ResidueField (ResidueField O) := ⟨hsc, inferInstance⟩
  let L := separableClosure y.ResidueField (ResidueField A)
  let e : ResidueField O ≃ₐ[y.ResidueField] L := IsSepClosure.equiv y.ResidueField (ResidueField O) L
  let ι : ResidueField O →ₐ[y.ResidueField] ResidueField A := L.val.comp e.toAlgHom
  let ψ₀ : O →ₐ[Polynomial T] ResidueField A :=
    (ι.restrictScalars (Polynomial T)).comp (IsScalarTower.toAlgHom (Polynomial T) O (ResidueField O))
  obtain ⟨π, hπ⟩ := (GlobalTheory.IndEtaleHensel.bijective_residue_comp (Polynomial T) O A hP).2 ψ₀
  refine ⟨O, inferInstance, algTO, algPO, t1, inferInstance, hsc, π, ?_, hP⟩
  intro b
  obtain ⟨E, _, _, _, φ, hb⟩ := hA b
  obtain ⟨e0, rfl⟩ := (AlgHom.mem_range φ).1 hb
  let f : E →ₐ[Polynomial T] ResidueField A :=
    (IsScalarTower.toAlgHom (Polynomial T) A (ResidueField A)).comp φ
  have hfL : ∀ x, f x ∈ L := fun x =>
    mem_separableClosure_iff.2 (GlobalTheory.Specialise.sepEtale (Polynomial T) E y (ResidueField A) f x)
  let g : E →ₐ[Polynomial T] ResidueField O :=
    { toRingHom := (e.symm : L →+* ResidueField O).comp (f.toRingHom.codRestrict L hfL)
      commutes' := fun r => by
        apply e.injective
        change e (e.symm ⟨f (algebraMap _ E r), hfL _⟩) = _
        rw [AlgEquiv.apply_symm_apply]
        apply Subtype.ext
        rw [IsScalarTower.algebraMap_apply (Polynomial T) y.ResidueField (ResidueField O),
          AlgEquiv.commutes]
        change f (algebraMap _ E r) = _
        rw [AlgHom.commutes, IsScalarTower.algebraMap_apply (Polynomial T) y.ResidueField (ResidueField A)]
        rfl }
  obtain ⟨ψ, hψ⟩ := (GlobalTheory.EtaleHensel.bijective_residue_comp (Polynomial T) E O).2 g
  have hcomp : π.comp ψ = φ := by
    apply (GlobalTheory.EtaleHensel.bijective_residue_comp (Polynomial T) E A).1
    dsimp only
    ext x
    have h1 := DFunLike.congr_fun hπ (ψ x)
    have h2 := DFunLike.congr_fun hψ x
    simp only [AlgHom.comp_apply] at h1 h2 ⊢
    rw [h1]
    change ι (IsScalarTower.toAlgHom (Polynomial T) O (ResidueField O) (ψ x)) = f x
    rw [h2]
    change ((e (e.symm ⟨f x, hfL x⟩) : L) : ResidueField A) = f x
    rw [AlgEquiv.apply_symm_apply]
  exact ⟨ψ e0, DFunLike.congr_fun hcomp e0⟩

end GlobalTheory
