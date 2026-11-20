import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleLimits.SmulOfEqOfMemFixingSubgroup
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IntermediateField GroundTheory.Global FiniteSubfield

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

namespace IdeleLimit

def unitsIncl (F : FiniteSubfield) : F.1ˣ →* ℚ̄ˣ :=
  Units.map F.1.val.toRingHom.toMonoidHom

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_unitsIncl (F : FiniteSubfield) (u : F.1ˣ) : ((unitsIncl F u : ℚ̄ˣ) : ℚ̄) = ((u : F.1) : ℚ̄) :=
  rfl

/- English proof (translation)
Introduce `_ _ h` and use `Units.ext (Subtype.ext (congrArg (fun a : ℚ̄ˣ => (a : ℚ̄)) h))`.
-/
theorem unitsIncl_injective (F : FiniteSubfield) : Function.Injective (unitsIncl F) :=
  fun _ _ h => Units.ext (Subtype.ext (congrArg (fun a : ℚ̄ˣ => (a : ℚ̄)) h))

/- English proof (translation)
Establish `hint : IsIntegral ℚ (a : ℚ̄)` using `Algebra.IsIntegral.isIntegral _`. Set `F : FiniteSubfield` to `⟨ℚ⟮(a : ℚ̄)⟯, IntermediateField.adjoin.finiteDimensional hint⟩`. Establish `hmem : (a : ℚ̄) ∈ F.1` using `IntermediateField.mem_adjoin_simple_self ℚ (a : ℚ̄)`. Use `⟨F, Units.mk0 ⟨a, hmem⟩ fun h => a.ne_zero (congrArg Subtype.val h), Units.ext rfl⟩` and prove the remaining obligations.
-/
theorem exists_unitsIncl (a : ℚ̄ˣ) : ∃ (F : FiniteSubfield) (u : F.1ˣ), unitsIncl F u = a := by
  have hint : IsIntegral ℚ (a : ℚ̄) := Algebra.IsIntegral.isIntegral _
  let F : FiniteSubfield := ⟨ℚ⟮(a : ℚ̄)⟯, IntermediateField.adjoin.finiteDimensional hint⟩
  have hmem : (a : ℚ̄) ∈ F.1 := IntermediateField.mem_adjoin_simple_self ℚ (a : ℚ̄)
  refine ⟨F, Units.mk0 ⟨a, hmem⟩ fun h => a.ne_zero (congrArg Subtype.val h), Units.ext rfl⟩

/- English proof (translation)
The claim follows from `Units.ext rfl`.
-/
theorem unitsIncl_map {F E : FiniteSubfield} (h : F ≤ E) (u : F.1ˣ) :
    letI := algebraOfLE h
    unitsIncl E (Units.map (algebraMap F.1 E.1).toMonoidHom u) = unitsIncl F u :=
  Units.ext rfl

def diagOf (F : FiniteSubfield) : F.1ˣ →* IdeleLimit :=
  (of F).comp (IdeleGroup.diagonal F.1)

/- English proof (translation)
Use `letI := algebraOfLE h`. Express the relevant statement in the definitionally equal form `of E (IdeleGroup.diagonal E.1 _) = of F (IdeleGroup.diagonal F.1 u)`. Rewrite using `[← ideleEmbedding_diagonal]`. Conclude with `of_ideleMap h _`.
-/
theorem diagOf_map {F E : FiniteSubfield} (h : F ≤ E) (u : F.1ˣ) :
    letI := algebraOfLE h
    diagOf E (Units.map (algebraMap F.1 E.1).toMonoidHom u) = diagOf F u := by
  letI := algebraOfLE h
  change of E (IdeleGroup.diagonal E.1 _) = of F (IdeleGroup.diagonal F.1 u)
  rw [← ideleEmbedding_diagonal]
  exact of_ideleMap h _

/- English proof (translation)
Set `M : FiniteSubfield` to `⟨F.1 ⊔ F'.1, inferInstance⟩`. Establish `hM : F ≤ M` using `show F.1 ≤ F.1 ⊔ F'.1 from le_sup_left`. Establish `hM' : F' ≤ M` using `show F'.1 ≤ F.1 ⊔ F'.1 from le_sup_right`. Use `letI := algebraOfLE hM`. Use `letI := algebraOfLE hM'`.

Rewrite using `[← diagOf_map hM, ← diagOf_map hM']`. Use `congr 1`. Apply `unitsIncl_injective M` to reduce the goal to its premises. Rewrite using `[unitsIncl_map, unitsIncl_map, h]`.
-/
theorem diagOf_eq_of_unitsIncl_eq {F F' : FiniteSubfield} (u : F.1ˣ) (u' : F'.1ˣ)
    (h : unitsIncl F u = unitsIncl F' u') : diagOf F u = diagOf F' u' := by
  let M : FiniteSubfield := ⟨F.1 ⊔ F'.1, inferInstance⟩
  have hM : F ≤ M := show F.1 ≤ F.1 ⊔ F'.1 from le_sup_left
  have hM' : F' ≤ M := show F'.1 ≤ F.1 ⊔ F'.1 from le_sup_right
  letI := algebraOfLE hM
  letI := algebraOfLE hM'
  rw [← diagOf_map hM, ← diagOf_map hM']
  congr 1
  apply unitsIncl_injective M
  rw [unitsIncl_map, unitsIncl_map, h]

def diagFun (a : ℚ̄ˣ) : IdeleLimit :=
  diagOf (exists_unitsIncl a).choose (exists_unitsIncl a).choose_spec.choose

/- English proof (translation)
The claim follows from `diagOf_eq_of_unitsIncl_eq _ _ (exists_unitsIncl (unitsIncl F u)).choose_spec.choose_spec`.
-/
theorem diagFun_unitsIncl (F : FiniteSubfield) (u : F.1ˣ) : diagFun (unitsIncl F u) = diagOf F u :=
  diagOf_eq_of_unitsIncl_eq _ _ (exists_unitsIncl (unitsIncl F u)).choose_spec.choose_spec

def diag : ℚ̄ˣ →* IdeleLimit where
  toFun := diagFun
  map_one' := by
    obtain ⟨F⟩ := (inferInstance : Nonempty FiniteSubfield)
    rw [← map_one (unitsIncl F), diagFun_unitsIncl, map_one]
  map_mul' a b := by
    obtain ⟨F, u, rfl⟩ := exists_unitsIncl a
    obtain ⟨F', u', rfl⟩ := exists_unitsIncl b
    let M : FiniteSubfield := ⟨F.1 ⊔ F'.1, inferInstance⟩
    have hM : F ≤ M := show F.1 ≤ F.1 ⊔ F'.1 from le_sup_left
    have hM' : F' ≤ M := show F'.1 ≤ F.1 ⊔ F'.1 from le_sup_right
    letI := algebraOfLE hM
    letI := algebraOfLE hM'
    rw [← unitsIncl_map hM, ← unitsIncl_map hM', ← map_mul, diagFun_unitsIncl, diagFun_unitsIncl,
      diagFun_unitsIncl, map_mul]

/- English proof (translation)
The claim follows from `diagFun_unitsIncl F u`.
-/
theorem diag_unitsIncl (F : FiniteSubfield) (u : F.1ˣ) : diag (unitsIncl F u) = diagOf F u :=
  diagFun_unitsIncl F u

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_one]`. Introduce `a ha`. Take `⟨F, u, rfl⟩` from `exists_unitsIncl a`. Rewrite `ha` using `[diag_unitsIncl]`. Establish `h1 : IdeleGroup.diagonal F.1 u = 1` using `of_injective F (ha.trans (map_one _).symm)`.

Rewrite using `[IdeleGroup.diagonal_injective F.1 (h1.trans (map_one _).symm), map_one]`.
-/
theorem diag_injective : Function.Injective diag := by
  rw [injective_iff_map_eq_one]
  intro a ha
  obtain ⟨F, u, rfl⟩ := exists_unitsIncl a
  rw [diag_unitsIncl] at ha
  have h1 : IdeleGroup.diagonal F.1 u = 1 := of_injective F (ha.trans (map_one _).symm)
  rw [IdeleGroup.diagonal_injective F.1 (h1.trans (map_one _).symm), map_one]

/- English proof (translation)
Take `⟨F, u, rfl⟩` from `exists_unitsIncl a`. Establish `h : Units.map (σ : ℚ̄ →* ℚ̄) (unitsIncl F u) = unitsIncl (map σ F) (Units.map (mapEquiv σ F : F.1 →* (map σ F).1) u)` using `Units.ext rfl`. Rewrite using `[h, diag_unitsIncl, diag_unitsIncl, diagOf, diagOf, MonoidHom.comp_apply, MonoidHom.comp_apply, smul_of, ideleEquiv_diagonal]`.
-/
theorem diag_map (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) (a : ℚ̄ˣ) :
    diag (Units.map (σ : ℚ̄ →* ℚ̄) a) = σ • diag a := by
  obtain ⟨F, u, rfl⟩ := exists_unitsIncl a
  have h : Units.map (σ : ℚ̄ →* ℚ̄) (unitsIncl F u) =
      unitsIncl (map σ F) (Units.map (mapEquiv σ F : F.1 →* (map σ F).1) u) := Units.ext rfl
  rw [h, diag_unitsIncl, diag_unitsIncl, diagOf, diagOf, MonoidHom.comp_apply, MonoidHom.comp_apply,
    smul_of, ideleEquiv_diagonal]

/- English proof (translation)
Take `⟨F, u, rfl⟩` from `exists_unitsIncl a`. Rewrite using `[diag_unitsIncl, diagOf, MonoidHom.comp_apply, toClassLimit_of, IdeleClassGroup.mk_diagonal, map_one]`.
-/
theorem toClassLimit_diag (a : ℚ̄ˣ) : toClassLimit (diag a) = 1 := by
  obtain ⟨F, u, rfl⟩ := exists_unitsIncl a
  rw [diag_unitsIncl, diagOf, MonoidHom.comp_apply, toClassLimit_of, IdeleClassGroup.mk_diagonal,
    map_one]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, rfl⟩`. Conclude with `toClassLimit_diag a`. Introduce `hz`. Take `⟨F, x, rfl⟩` from `exists_of z`.

Rewrite `hz` using `[toClassLimit_of]`. Establish `h1 : IdeleClassGroup.mk F.1 x = 1` using `IdeleClassLimit.of_injective F (hz.trans (map_one _).symm)`. Establish `h2 : x ∈ (IdeleGroup.diagonal F.1).range`. Rewrite using `[← IdeleClassGroup.ker_mk]`. Conclude with `h1`.

Take `⟨u, rfl⟩` from `h2`. Conclude with `⟨unitsIncl F u, by rw [diag_unitsIncl]; rfl⟩`.
-/
theorem mem_range_diag_iff (z : IdeleLimit) : z ∈ diag.range ↔ toClassLimit z = 1 := by
  constructor
  · rintro ⟨a, rfl⟩
    exact toClassLimit_diag a
  · intro hz
    obtain ⟨F, x, rfl⟩ := exists_of z
    rw [toClassLimit_of] at hz
    have h1 : IdeleClassGroup.mk F.1 x = 1 :=
      IdeleClassLimit.of_injective F (hz.trans (map_one _).symm)
    have h2 : x ∈ (IdeleGroup.diagonal F.1).range := by
      rw [← IdeleClassGroup.ker_mk]
      exact h1
    obtain ⟨u, rfl⟩ := h2
    exact ⟨unitsIncl F u, by rw [diag_unitsIncl]; rfl⟩

end IdeleLimit

end

end GroundTheory.ProfCoh
