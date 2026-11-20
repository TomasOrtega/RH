import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.W (Plc)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Establish `h : ∀ w : InfinitePlace E, ∃ y : w.Completion, y ^ m = (d : Ad E).1 w` using `fun w => by`. Set `e` to `InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)`. Take `⟨z, hz⟩` from `IsAlgClosed.exists_pow_nat_eq (e ((d : Ad E).1 w)) hm`. Conclude with `⟨e.symm z, e.injective (by rw [map_pow, e.apply_symm_apply, hz])⟩`. Use `choose y hy using h`.

Set `Y : Ad E` to `((y : InfiniteAdeleRing E), (1 : Af E))`. Establish `hY : Y ^ m = (d : Ad E)` using `Prod.ext (funext hy) ((one_pow m).trans hd.symm)`. Establish `hu : IsUnit Y` using `(isUnit_pow_iff hm.ne').1 (hY ▸ d.isUnit)`. Conclude with `⟨hu.unit, Units.ext (by rw [Units.val_pow_eq_pow_val, hu.unit_spec, hY])⟩`.
-/
private theorem exists_root (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] {m : ℕ} (hm : 0 < m)
    (d : Ideles E) (hd : pFin E (d : Ad E) = 1) : ∃ y : Ideles E, y ^ m = d := by
  have h : ∀ w : InfinitePlace E, ∃ y : w.Completion, y ^ m = (d : Ad E).1 w := fun w => by
    let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e ((d : Ad E).1 w)) hm
    exact ⟨e.symm z, e.injective (by rw [map_pow, e.apply_symm_apply, hz])⟩
  choose y hy using h
  let Y : Ad E := ((y : InfiniteAdeleRing E), (1 : Af E))
  have hY : Y ^ m = (d : Ad E) := Prod.ext (funext hy) ((one_pow m).trans hd.symm)
  have hu : IsUnit Y := (isUnit_pow_iff hm.ne').1 (hY ▸ d.isUnit)
  exact ⟨hu.unit, Units.ext (by rw [Units.val_pow_eq_pow_val, hu.unit_spec, hY])⟩

/- English proof (translation)
Introduce `E _ _ _ n ν m hm h`. Establish `h1 : ∀ x, ν.1 x ^ m = 1` using `fun x => congrArg (fun ξ : HChar E => ξ.1 x) h`. Use `⟨isOpen_ker_of_pow _ ?_ hm fun g => h1 _, ?_, ?_⟩` and prove the remaining obligations. Conclude with `ν.2.1.comp (Matrix.GeneralLinearGroup.continuous_det.comp continuous_subtype_val)`. Introduce `g hg`.

Take `⟨γ, hγ⟩` from `Subgroup.mem_subgroupOf.1 hg`. Rewrite using `[← hγ, chiDet_ratGL]`. Introduce `g hg`. Establish `hg' : Matrix.GeneralLinearGroup.map (pFin E) (g : GA E n) = 1` using `hg`. Take `⟨y, hy⟩` from `exists_root E hm (Matrix.GeneralLinearGroup.det (g : GA E n)) (by`.

Rewrite using `[← GlobalTheory.CuspRep.det_map, hg']`. Use the proof step `simp)`. Express the relevant statement in the definitionally equal form `ν.1 (Matrix.GeneralLinearGroup.det (g : GA E n)) = 1`. Rewrite using `[← hy, map_pow, h1]`.
-/
theorem UpperTheory.detCharacter_ker_open_trivial_rational_archimedean :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (ν : HChar E) (m : ℕ), 0 < m → ν.OrderDvd m → IsOpen (((chiDet n ν).comp (UA E n).subtype).ker : Set (UA E n)) ∧ (∀ g ∈ ratU E n, chiDet n ν (g : UA E n) = 1) ∧ ∀ g ∈ infU E n, chiDet n ν (g : UA E n) = 1 := by
  intro E _ _ _ n ν m hm h
  have h1 : ∀ x, ν.1 x ^ m = 1 := fun x => congrArg (fun ξ : HChar E => ξ.1 x) h
  refine ⟨isOpen_ker_of_pow _ ?_ hm fun g => h1 _, ?_, ?_⟩
  · exact ν.2.1.comp (Matrix.GeneralLinearGroup.continuous_det.comp continuous_subtype_val)
  · intro g hg
    obtain ⟨γ, hγ⟩ := Subgroup.mem_subgroupOf.1 hg
    rw [← hγ, chiDet_ratGL]
  · intro g hg
    have hg' : Matrix.GeneralLinearGroup.map (pFin E) (g : GA E n) = 1 := hg
    obtain ⟨y, hy⟩ := exists_root E hm (Matrix.GeneralLinearGroup.det (g : GA E n)) (by
      rw [← GlobalTheory.CuspRep.det_map, hg']; simp)
    change ν.1 (Matrix.GeneralLinearGroup.det (g : GA E n)) = 1
    rw [← hy, map_pow, h1]
