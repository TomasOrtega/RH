import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

/- English proof (translation)
Use `letI := f.toAlgebra`. Use `letI := (PowerSeries.map f).toAlgebra`. Use `haveI : Module.Finite K L := Module.Finite.of_finite`. Set `b` to `Module.finBasis K L`. Use `show Module.Finite (PowerSeries K) (PowerSeries L)`.

Use `⟨⟨Finset.univ.image (fun i => PowerSeries.C (b i)), ?_⟩⟩` and prove the remaining obligations. Rewrite using `[eq_top_iff]`. Introduce `φ _`. Establish `key : φ = ∑ i, (PowerSeries.mk fun n => b.repr (PowerSeries.coeff n φ) i) • PowerSeries.C (b i)`. Use extensionality with `n`.

Simplify using `only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_sum, PowerSeries.coeff_mul_C, PowerSeries.coeff_map, PowerSeries.coeff_mk]`. Conclude with `(b.sum_repr _).symm.trans (Finset.sum_congr rfl fun i _ => Algebra.smul_def _ _)`. Rewrite using `[key]`. Use `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
private theorem map_finite {K L : Type} [Field K] [Field L] [Finite L] (f : K →+* L) :
    (PowerSeries.map f).Finite := by
  classical
  letI := f.toAlgebra
  letI := (PowerSeries.map f).toAlgebra
  haveI : Module.Finite K L := Module.Finite.of_finite
  let b := Module.finBasis K L
  show Module.Finite (PowerSeries K) (PowerSeries L)
  refine ⟨⟨Finset.univ.image (fun i => PowerSeries.C (b i)), ?_⟩⟩
  rw [eq_top_iff]
  intro φ _
  have key : φ = ∑ i, (PowerSeries.mk fun n => b.repr (PowerSeries.coeff n φ) i) •
      PowerSeries.C (b i) := by
    ext n
    simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_sum, PowerSeries.coeff_mul_C,
      PowerSeries.coeff_map, PowerSeries.coeff_mk]
    exact (b.sum_repr _).symm.trans (Finset.sum_congr rfl fun i _ => Algebra.smul_def _ _)
  rw [key]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  simp

/- English proof (translation)
Use `⟨RingHom.injective _, fun y => ?_⟩` and prove the remaining obligations. Take `⟨x, rfl⟩` from `residue_surjective y`. Use `⟨PowerSeries.constantCoeff x, ?_⟩` and prove the remaining obligations. Rewrite using `[RingHom.comp_apply, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff, map_sub, PowerSeries.constantCoeff_C, sub_self]`. Conclude with `not_isUnit_zero`.
-/
private theorem bijective_residue_comp_powerSeries_C (F : Type) [Field F] :
    Function.Bijective ((residue (PowerSeries F)).comp (PowerSeries.C (R := F))) := by
  refine ⟨RingHom.injective _, fun y => ?_⟩
  obtain ⟨x, rfl⟩ := residue_surjective y
  refine ⟨PowerSeries.constantCoeff x, ?_⟩
  rw [RingHom.comp_apply, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff, mem_maximalIdeal,
    mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff, map_sub, PowerSeries.constantCoeff_C,
    sub_self]
  exact not_isUnit_zero

/- English proof (translation)
Introduce `l _ K _ _ _ d D hK hdD hD`. Establish `hd : d ≠ 0`. Introduce and unpack `rfl`. Conclude with `hD (zero_dvd_iff.mp hdD)`. Use `letI : Algebra (ZMod l) K := ZMod.algebra K l`.

Set `e` to `GaloisField.algEquivGaloisField l d hK`. Take `⟨g⟩` from `FiniteField.nonempty_algHom_of_finrank_dvd (F := ZMod l) (K := GaloisField l d) (L := GaloisField l D) (by rw [GaloisField.finrank l hd, GaloisField.finrank l hD]; exact hdD)`. Set `φ : K →+* GaloisField l D` to `(g.comp e.toAlgHom).toRingHom`. Establish `hcc : ∀ ψ : PowerSeries K, PowerSeries.constantCoeff (PowerSeries.map φ ψ) = φ (PowerSeries.constantCoeff ψ)`. Introduce `ψ`.

Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply]`. Use `haveI : CharP (PowerSeries (GaloisField l D)) l := charP_of_injective_ringHom (PowerSeries.C (R := GaloisField l D)).injective l`. Use `haveI : UpperTheory.V.Pa.IsEqDVR l (PowerSeries (GaloisField l D)) := ⟨by rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance, Finite.of_surjective _ (bijective_residue_comp_powerSeries_C (GaloisField l D)).2, inferInstance⟩`. Use `⟨PowerSeries (GaloisField l D), inferInstance, inferInstance, inferInstance, inferInstance, PowerSeries.map φ, PowerSeries.map_injective _ φ.injective, ⟨fun ψ hψ => ?_⟩, map_finite φ, ?_, ?_⟩` and prove the remaining obligations. Rewrite `hψ` using `[PowerSeries.isUnit_iff_constantCoeff, hcc, isUnit_iff_ne_zero, map_ne_zero_iff _ φ.injective]`.

Rewrite using `[PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero]`. Conclude with `hψ`. Rewrite using `[← Nat.card_congr (Equiv.ofBijective _ (bijective_residue_comp_powerSeries_C (GaloisField l D))), GaloisField.card l D hD]`. Rewrite using `[PowerSeries.map_X]`. Conclude with `PowerSeries.X_irreducible`.
-/
theorem UpperTheory.V.Pa.Det.resExt :
    ∀ (l : ℕ) [Fact l.Prime] {K : Type} [Field K] [Finite K] [CharP K l] (d D : ℕ), Nat.card K = l ^ d → d ∣ D → D ≠ 0 → ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : IsDiscreteValuationRing A') (_ : IsEqDVR l A') (j : PowerSeries K →+* A'), Function.Injective j ∧ IsLocalHom j ∧ j.Finite ∧ Nat.card (ResidueField A') = l ^ D ∧ Irreducible (j PowerSeries.X) := by
  intro l _ K _ _ _ d D hK hdD hD
  have hd : d ≠ 0 := by
    rintro rfl
    exact hD (zero_dvd_iff.mp hdD)
  letI : Algebra (ZMod l) K := ZMod.algebra K l
  let e := GaloisField.algEquivGaloisField l d hK
  obtain ⟨g⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := ZMod l)
    (K := GaloisField l d) (L := GaloisField l D)
    (by rw [GaloisField.finrank l hd, GaloisField.finrank l hD]; exact hdD)
  let φ : K →+* GaloisField l D := (g.comp e.toAlgHom).toRingHom
  have hcc : ∀ ψ : PowerSeries K, PowerSeries.constantCoeff (PowerSeries.map φ ψ) =
      φ (PowerSeries.constantCoeff ψ) := by
    intro ψ
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
  haveI : CharP (PowerSeries (GaloisField l D)) l :=
    charP_of_injective_ringHom (PowerSeries.C (R := GaloisField l D)).injective l
  haveI : UpperTheory.V.Pa.IsEqDVR l (PowerSeries (GaloisField l D)) :=
    ⟨by rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance,
      Finite.of_surjective _ (bijective_residue_comp_powerSeries_C (GaloisField l D)).2, inferInstance⟩
  refine ⟨PowerSeries (GaloisField l D), inferInstance, inferInstance, inferInstance, inferInstance,
    PowerSeries.map φ, PowerSeries.map_injective _ φ.injective, ⟨fun ψ hψ => ?_⟩,
    map_finite φ, ?_, ?_⟩
  · rw [PowerSeries.isUnit_iff_constantCoeff, hcc, isUnit_iff_ne_zero,
      map_ne_zero_iff _ φ.injective] at hψ
    rw [PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
    exact hψ
  · rw [← Nat.card_congr (Equiv.ofBijective _ (bijective_residue_comp_powerSeries_C (GaloisField l D))),
      GaloisField.card l D hD]
  · rw [PowerSeries.map_X]
    exact PowerSeries.X_irreducible
