import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ShaFamMono
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsSign
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.ClassFix

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

/- English proof (translation)
Introduce `E _ _ N _ H hlev`. Take `⟨j, ζ, hζ, hj⟩` from `hlev`. Use `haveI : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast NeZero.ne N⟩`. Use `haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) := CyclotomicField.isCyclotomicExtension N ℚ`. Use `haveI : IsAbelianGalois ℚ (CyclotomicField N ℚ) := IsCyclotomicExtension.isAbelianGalois {N} ℚ (CyclotomicField N ℚ)`.

Establish `hfs : KStar.TotallyRealRoots.fieldSubgroup N (CyclotomicField N ℚ) j.fieldRange = H`. Use extensionality with `u`. Unfold `KStar.TotallyRealRoots.fieldSubgroup`. Rewrite using `[Subgroup.mem_map_equiv]`. Use `set τ := (IsCyclotomicExtension.Rat.galEquivZMod N (CyclotomicField N ℚ)).symm u with hτdef`.

Establish `hu : IsCyclotomicExtension.Rat.galEquivZMod N (CyclotomicField N ℚ) τ = u`. Rewrite using `[hτdef]`. Conclude with `MulEquiv.apply_symm_apply _ u`. Establish `hτ : τ ζ = ζ ^ (u : ZMod N).val`. Rewrite using `[IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq N _ τ hζ.pow_eq_one, hu]`.

Rewrite using `[← hj τ u hτ, IntermediateField.mem_fixingSubgroup_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h x`. Conclude with `h (j x) ⟨x, rfl⟩`. Introduce and unpack `h _ ⟨x, rfl⟩`.

Conclude with `h x`. Establish `hfr : Module.finrank ℚ j.fieldRange = Module.finrank ℚ E`. Rewrite using `[(AlgEquiv.ofInjectiveField j).toLinearEquiv.finrank_eq]`. Both sides reduce to the same expression. Establish `hfin : Module.finrank ℚ E = H.index`.

Rewrite using `[← hfr, IntermediateField.finrank_eq_fixingSubgroup_index, ← hfs]`. Unfold `KStar.TotallyRealRoots.fieldSubgroup`. Conclude with `(Subgroup.index_map_of_bijective (MulEquiv.bijective _) _).symm`. Use `⟨IsAbelianGalois.of_algHom j, hfin, ?_⟩` and prove the remaining obligations. Introduce `Ω _ _ _ _`.

Use `haveI : IsScalarTower ℚ E Ω := inferInstance`. Use `haveI : IsAlgClosure E Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) E⟩`. Establish `heq : galOf ℚ E Ω = levH ℚ Ω H`. Use extensionality with `σ`. Rewrite using `[mem_galOf]`.

Unfold `levH`. Rewrite using `[Subgroup.mem_comap, ← hfs]`. Conclude with `LDataCardLeFinrank.classFix E Ω N (CyclotomicField N ℚ) j σ.toRingEquiv (cls ℚ Ω N σ) (fun z hz => cls_spec N σ z hz)`. Take `⟨-, hopen, hidx⟩` from `galEmbTop ℚ E Ω`. Use `⟨heq, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← heq, hidx, hfin]`. Rewrite using `[← heq]`. Conclude with `hopen`.
-/
theorem UpperTheory.V.Chr.levGal :
    ∀ (E : Type) [Field E] [NumberField E] (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ), HasLevel E N H → IsAbelianGalois ℚ E ∧ Module.finrank ℚ E = H.index ∧
          ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra E Ω], galOf ℚ E Ω = levH ℚ Ω H ∧ (levH ℚ Ω H).index = H.index ∧ IsOpen (levH ℚ Ω H : Set (G ℚ Ω)) := by
  intro E _ _ N _ H hlev
  obtain ⟨j, ζ, hζ, hj⟩ := hlev
  haveI : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast NeZero.ne N⟩
  haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) :=
    CyclotomicField.isCyclotomicExtension N ℚ
  haveI : IsAbelianGalois ℚ (CyclotomicField N ℚ) :=
    IsCyclotomicExtension.isAbelianGalois {N} ℚ (CyclotomicField N ℚ)
  have hfs : KStar.TotallyRealRoots.fieldSubgroup N (CyclotomicField N ℚ) j.fieldRange = H := by
    ext u
    unfold KStar.TotallyRealRoots.fieldSubgroup
    rw [Subgroup.mem_map_equiv]
    set τ := (IsCyclotomicExtension.Rat.galEquivZMod N (CyclotomicField N ℚ)).symm u with hτdef
    have hu : IsCyclotomicExtension.Rat.galEquivZMod N (CyclotomicField N ℚ) τ = u := by
      rw [hτdef]
      exact MulEquiv.apply_symm_apply _ u
    have hτ : τ ζ = ζ ^ (u : ZMod N).val := by
      rw [IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq N _ τ hζ.pow_eq_one, hu]
    rw [← hj τ u hτ, IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro h x
      exact h (j x) ⟨x, rfl⟩
    · rintro h _ ⟨x, rfl⟩
      exact h x
  have hfr : Module.finrank ℚ j.fieldRange = Module.finrank ℚ E := by
    rw [(AlgEquiv.ofInjectiveField j).toLinearEquiv.finrank_eq]
    rfl
  have hfin : Module.finrank ℚ E = H.index := by
    rw [← hfr, IntermediateField.finrank_eq_fixingSubgroup_index, ← hfs]
    unfold KStar.TotallyRealRoots.fieldSubgroup
    exact (Subgroup.index_map_of_bijective (MulEquiv.bijective _) _).symm
  refine ⟨IsAbelianGalois.of_algHom j, hfin, ?_⟩
  intro Ω _ _ _ _
  haveI : IsScalarTower ℚ E Ω := inferInstance
  haveI : IsAlgClosure E Ω :=
    ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) E⟩
  have heq : galOf ℚ E Ω = levH ℚ Ω H := by
    ext σ
    rw [mem_galOf]
    unfold levH
    rw [Subgroup.mem_comap, ← hfs]
    exact LDataCardLeFinrank.classFix E Ω N (CyclotomicField N ℚ) j σ.toRingEquiv (cls ℚ Ω N σ)
      (fun z hz => cls_spec N σ z hz)
  obtain ⟨-, hopen, hidx⟩ := galEmbTop ℚ E Ω
  refine ⟨heq, ?_, ?_⟩
  · rw [← heq, hidx, hfin]
  · rw [← heq]
    exact hopen
