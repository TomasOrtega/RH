import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivialIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomExtLocalization
open IsLocalRing Polynomial

namespace GlobalTheory.Specialise

/- English proof (translation)
Set `P : Ideal A` to `RingHom.ker f`. Use `haveI : P.IsPrime := RingHom.ker_isPrime f`. Establish `hPQ : Q = P.comap (algebraMap R A)`. Use extensionality with `r`. Simplify using `only [P, Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes]`.

Rewrite using `[IsScalarTower.algebraMap_apply R Q.ResidueField L]`. Simplify using the standard rewrite rules. Use `haveI : P.LiesOver Q := ⟨hPQ⟩`. Use `letI := Localization.AtPrime.algebraOfLiesOver Q P`. Use `haveI : Localization.AtPrime.IsLiesOverAlgebra Q P := ⟨rfl⟩`.

Establish `hsep : Algebra.IsSeparable Q.ResidueField P.ResidueField` using `inferInstance`. Set `g : P.ResidueField →ₐ[R] L` to `Ideal.ResidueField.liftₐ P f le_rfl (fun x hx => by`. Simplify using `only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff]`. Conclude with `isUnit_iff_ne_zero.mpr (fun h => hx h))`. Establish `hg : ∀ x : A, g (algebraMap A P.ResidueField x) = f x` using `fun x => Ideal.ResidueField.liftₐ_algebraMap _ _ _ _ x`.

Set `g' : P.ResidueField →ₐ[Q.ResidueField] L` to `{ g.toRingHom with commutes' := by`. Establish `: g.toRingHom.comp (algebraMap Q.ResidueField P.ResidueField) = algebraMap Q.ResidueField L`. Apply `Ideal.ResidueField.ringHom_ext` to reduce the goal to its premises. Use extensionality with `r`. Simplify using `only [RingHom.comp_apply]`.

Rewrite using `[← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R A P.ResidueField]`. Conclude with `(hg _).trans (f.commutes r)`. Introduce `c`. Conclude with `DFunLike.congr_fun this c }`. Establish `h1 : g' (algebraMap A P.ResidueField a) = f a` using `hg a`.

Rewrite using `[← h1, isSeparable_map_iff g' g'.toRingHom.injective]`. Conclude with `Algebra.IsSeparable.isSeparable _ _`.
-/
theorem sepEtale (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Algebra.Etale R A]
    (Q : Ideal R) [Q.IsPrime] (L : Type) [Field L] [Algebra R L] [Algebra Q.ResidueField L]
    [IsScalarTower R Q.ResidueField L] (f : A →ₐ[R] L) (a : A) :
    IsSeparable Q.ResidueField (f a) := by
  let P : Ideal A := RingHom.ker f
  haveI : P.IsPrime := RingHom.ker_isPrime f
  have hPQ : Q = P.comap (algebraMap R A) := by
    ext r
    simp only [P, Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes]
    rw [IsScalarTower.algebraMap_apply R Q.ResidueField L]
    simp
  haveI : P.LiesOver Q := ⟨hPQ⟩
  letI := Localization.AtPrime.algebraOfLiesOver Q P
  haveI : Localization.AtPrime.IsLiesOverAlgebra Q P := ⟨rfl⟩
  have hsep : Algebra.IsSeparable Q.ResidueField P.ResidueField := inferInstance
  let g : P.ResidueField →ₐ[R] L := Ideal.ResidueField.liftₐ P f le_rfl (fun x hx => by
    simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
    exact isUnit_iff_ne_zero.mpr (fun h => hx h))
  have hg : ∀ x : A, g (algebraMap A P.ResidueField x) = f x := fun x =>
    Ideal.ResidueField.liftₐ_algebraMap _ _ _ _ x
  let g' : P.ResidueField →ₐ[Q.ResidueField] L :=
    { g.toRingHom with
      commutes' := by
        have : g.toRingHom.comp (algebraMap Q.ResidueField P.ResidueField) =
            algebraMap Q.ResidueField L := by
          apply Ideal.ResidueField.ringHom_ext
          ext r
          simp only [RingHom.comp_apply]
          rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
            IsScalarTower.algebraMap_apply R A P.ResidueField]
          exact (hg _).trans (f.commutes r)
        intro c
        exact DFunLike.congr_fun this c }
  have h1 : g' (algebraMap A P.ResidueField a) = f a := hg a
  rw [← h1, isSeparable_map_iff g' g'.toRingHom.injective]
  exact Algebra.IsSeparable.isSeparable _ _

/- English proof (translation)
Introduce `R S O _ _ _ _ _ _ _ _ Q y _ _ hQy hy hQ _ hpieces`. Use `haveI : Algebra.HasGoingDown R S := Algebra.HasGoingDown.of_flat`. Use `haveI : (maximalIdeal S).LiesOver y := ⟨hy.symm⟩`. Take `⟨Q₂, -, hQ₂p, hQ₂o⟩` from `Ideal.exists_ideal_le_liesOver_of_le (p := Q) (q := y) (maximalIdeal S) hQy`. Use `haveI := hQ₂p`.

Use `letI : Algebra Q.ResidueField Q₂.ResidueField := (Ideal.ResidueField.map Q Q₂ (algebraMap R S) hQ₂o.over).toAlgebra`. Use `haveI : IsScalarTower R Q.ResidueField Q₂.ResidueField := .of_algebraMap_eq fun r => by`. Rewrite using `[RingHom.algebraMap_toAlgebra, Ideal.ResidueField.map_algebraMap, ← IsScalarTower.algebraMap_apply]`. Establish `hsepS : ∀ s : S, IsSeparable Q.ResidueField (algebraMap S Q₂.ResidueField s)`. Introduce `s`.

Take `⟨ι, _, _, _, Si, -, hcov, hloc⟩` from `hpieces`. Take `⟨i, hi⟩` from `hcov s`. Take `⟨A, _, _, _, q, _, ⟨e⟩⟩` from `hloc i`. Set `F : Localization.AtPrime q →ₐ[R] Q₂.ResidueField` to `(IsScalarTower.toAlgHom R S Q₂.ResidueField).comp ((Si i).val.comp (e : _ →ₐ[R] _))`. Set `f : A →ₐ[R] Q₂.ResidueField` to `F.comp (IsScalarTower.toAlgHom R A (Localization.AtPrime q))`.

Take `⟨⟨a, t⟩, hat⟩` from `IsLocalization.mk'_surjective q.primeCompl (e.symm ⟨s, hi⟩)`. Establish `hs : algebraMap S Q₂.ResidueField s = F (IsLocalization.mk' _ a t)`. Simplify using `only [F, AlgHom.comp_apply, hat]`. Simplify using the standard rewrite rules. Establish `hft : f t ≠ 0`.

Establish `: IsUnit (f t)` using `(IsLocalization.map_units (Localization.AtPrime q) t).map F`. Conclude with `this.ne_zero`. Establish `hmul : F (IsLocalization.mk' _ a t) * f t = f a`. Simplify using `only [f, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', ← map_mul, IsLocalization.mk'_spec]`. Establish `hx : algebraMap S Q₂.ResidueField s = f a * (f t)⁻¹`.

Rewrite using `[hs, eq_mul_inv_iff_mul_eq₀ hft, hmul]`. Rewrite using `[hx, ← mem_separableClosure_iff]`. Apply the tactic sequence `refine mul_mem ?_ (inv_mem ?_) <;> rw [mem_separableClosure_iff] <;>`. Conclude with `sepEtale R A Q _ f _`. Use `haveI : Algebra.IsSeparable Q.ResidueField Q₂.ResidueField := ⟨fun x => by`.

Take `⟨u, v, -, rfl⟩` from `IsFractionRing.div_surjective (A := S ⧸ Q₂) x`. Take `⟨u, rfl⟩` from `Ideal.Quotient.mk_surjective u`. Take `⟨v, rfl⟩` from `Ideal.Quotient.mk_surjective v`. Rewrite using `[Ideal.algebraMap_quotient_residueField_mk, Ideal.algebraMap_quotient_residueField_mk, ← mem_separableClosure_iff]`. Conclude with `div_mem ((mem_separableClosure_iff).2 (hsepS u)) ((mem_separableClosure_iff).2 (hsepS v))⟩`.

Establish `hker : ∀ r : R, algebraMap R (ResidueField O) r = 0 ↔ r ∈ Q`. Introduce `r`. Rewrite using `[IsScalarTower.algebraMap_apply R O (ResidueField O), ResidueField.algebraMap_eq, residue_eq_zero_iff, ← hQ, Ideal.mem_comap]`. Use `letI : Algebra Q.ResidueField (ResidueField O) := (Ideal.ResidueField.lift Q (algebraMap R (ResidueField O)) (fun r hr => (hker r).2 hr) (fun r hr => by`. Simplify using `only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff]`.

Conclude with `isUnit_iff_ne_zero.mpr (fun h => hr ((hker r).1 h)))).toAlgebra`. Use `haveI : IsScalarTower R Q.ResidueField (ResidueField O) := .of_algebraMap_eq fun r => by`. Rewrite using `[RingHom.algebraMap_toAlgebra]`. Conclude with `(Ideal.ResidueField.lift_algebraMap Q _ _ _ r).symm`. Set `φ₀ : Q₂.ResidueField →ₐ[Q.ResidueField] ResidueField O` to `IsSepClosed.lift`.

Set `ψ : S →ₐ[R] ResidueField O` to `(φ₀.restrictScalars R).comp (IsScalarTower.toAlgHom R S Q₂.ResidueField)`. Take `⟨φ, -⟩` from `(GlobalTheory.IndEtaleHensel.bijective_residue_comp R S O hpieces).2 ψ`. Conclude with `⟨φ⟩`.
-/
theorem specialisation_exists : ∀ (R S O : Type) [CommRing R] [CommRing S] [IsLocalRing S] [CommRing O]
    [HenselianLocalRing O] [IsSepClosed (IsLocalRing.ResidueField O)] [Algebra R S] [Algebra R O]
    (Q y : Ideal R) [Q.IsPrime] [y.IsPrime], Q ≤ y →
    (IsLocalRing.maximalIdeal S).comap (algebraMap R S) = y →
    (IsLocalRing.maximalIdeal O).comap (algebraMap R O) = Q →
    Module.Flat R S → GlobalTheory.LocAcyc.LocPiecesEtale R S → Nonempty (S →ₐ[R] O) := by
  intro R S O _ _ _ _ _ _ _ _ Q y _ _ hQy hy hQ _ hpieces
  haveI : Algebra.HasGoingDown R S := Algebra.HasGoingDown.of_flat
  haveI : (maximalIdeal S).LiesOver y := ⟨hy.symm⟩
  obtain ⟨Q₂, -, hQ₂p, hQ₂o⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le (p := Q) (q := y) (maximalIdeal S) hQy
  haveI := hQ₂p
  letI : Algebra Q.ResidueField Q₂.ResidueField :=
    (Ideal.ResidueField.map Q Q₂ (algebraMap R S) hQ₂o.over).toAlgebra
  haveI : IsScalarTower R Q.ResidueField Q₂.ResidueField := .of_algebraMap_eq fun r => by
    rw [RingHom.algebraMap_toAlgebra, Ideal.ResidueField.map_algebraMap,
      ← IsScalarTower.algebraMap_apply]

  have hsepS : ∀ s : S, IsSeparable Q.ResidueField (algebraMap S Q₂.ResidueField s) := by
    intro s
    obtain ⟨ι, _, _, _, Si, -, hcov, hloc⟩ := hpieces
    obtain ⟨i, hi⟩ := hcov s
    obtain ⟨A, _, _, _, q, _, ⟨e⟩⟩ := hloc i
    let F : Localization.AtPrime q →ₐ[R] Q₂.ResidueField :=
      (IsScalarTower.toAlgHom R S Q₂.ResidueField).comp ((Si i).val.comp (e : _ →ₐ[R] _))
    let f : A →ₐ[R] Q₂.ResidueField :=
      F.comp (IsScalarTower.toAlgHom R A (Localization.AtPrime q))
    obtain ⟨⟨a, t⟩, hat⟩ := IsLocalization.mk'_surjective q.primeCompl (e.symm ⟨s, hi⟩)
    have hs : algebraMap S Q₂.ResidueField s = F (IsLocalization.mk' _ a t) := by
      simp only [F, AlgHom.comp_apply, hat]
      simp
    have hft : f t ≠ 0 := by
      have : IsUnit (f t) :=
        (IsLocalization.map_units (Localization.AtPrime q) t).map F
      exact this.ne_zero
    have hmul : F (IsLocalization.mk' _ a t) * f t = f a := by
      simp only [f, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', ← map_mul,
        IsLocalization.mk'_spec]
    have hx : algebraMap S Q₂.ResidueField s = f a * (f t)⁻¹ := by
      rw [hs, eq_mul_inv_iff_mul_eq₀ hft, hmul]
    rw [hx, ← mem_separableClosure_iff]
    refine mul_mem ?_ (inv_mem ?_) <;> rw [mem_separableClosure_iff] <;>
      exact sepEtale R A Q _ f _
  haveI : Algebra.IsSeparable Q.ResidueField Q₂.ResidueField := ⟨fun x => by
    obtain ⟨u, v, -, rfl⟩ := IsFractionRing.div_surjective (A := S ⧸ Q₂) x
    obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective u
    obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective v
    rw [Ideal.algebraMap_quotient_residueField_mk, Ideal.algebraMap_quotient_residueField_mk,
      ← mem_separableClosure_iff]
    exact div_mem ((mem_separableClosure_iff).2 (hsepS u)) ((mem_separableClosure_iff).2 (hsepS v))⟩

  have hker : ∀ r : R, algebraMap R (ResidueField O) r = 0 ↔ r ∈ Q := by
    intro r
    rw [IsScalarTower.algebraMap_apply R O (ResidueField O), ResidueField.algebraMap_eq,
      residue_eq_zero_iff, ← hQ, Ideal.mem_comap]
  letI : Algebra Q.ResidueField (ResidueField O) :=
    (Ideal.ResidueField.lift Q (algebraMap R (ResidueField O)) (fun r hr => (hker r).2 hr)
      (fun r hr => by
        simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
        exact isUnit_iff_ne_zero.mpr (fun h => hr ((hker r).1 h)))).toAlgebra
  haveI : IsScalarTower R Q.ResidueField (ResidueField O) := .of_algebraMap_eq fun r => by
    rw [RingHom.algebraMap_toAlgebra]
    exact (Ideal.ResidueField.lift_algebraMap Q _ _ _ r).symm
  let φ₀ : Q₂.ResidueField →ₐ[Q.ResidueField] ResidueField O := IsSepClosed.lift
  let ψ : S →ₐ[R] ResidueField O :=
    (φ₀.restrictScalars R).comp (IsScalarTower.toAlgHom R S Q₂.ResidueField)
  obtain ⟨φ, -⟩ := (GlobalTheory.IndEtaleHensel.bijective_residue_comp R S O hpieces).2 ψ
  exact ⟨φ⟩

end GlobalTheory.Specialise
