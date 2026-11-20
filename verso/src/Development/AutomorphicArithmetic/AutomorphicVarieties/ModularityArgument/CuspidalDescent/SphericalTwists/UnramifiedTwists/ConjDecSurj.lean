import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.RowProps

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.WeilDeligne UpperTheory.V.Af UpperTheory.V.Z.Win
open scoped Pointwise

namespace UpperTheory.V.Z.Desc.W

private def conjDec {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (A B : ValuationSubring Ω) (γ : G F Ω)
    (h : γ • A = B) : ↥(Dec (F := F) B) →* ↥(Dec (F := F) A) where
  toFun u := ⟨γ⁻¹ * u * γ, by
    have hu := mem_Dec.1 u.2
    rw [mem_Dec, mul_smul, mul_smul, h, hu, ← h, inv_smul_smul]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem conjDec_coe {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (A B : ValuationSubring Ω)
    (γ : G F Ω) (h : γ • A = B) (u : ↥(Dec (F := F) B)) :
    ((conjDec A B γ h u : ↥(Dec (F := F) A)) : G F Ω) = γ⁻¹ * u * γ := rfl

/- English proof (translation)
Introduce `v`. Use `⟨⟨γ * v * γ⁻¹, ?_⟩, ?_⟩` and prove the remaining obligations. Establish `hv` using `mem_Dec.1 v.2`. Establish `hA : γ⁻¹ • B = A` using `by rw [← h, inv_smul_smul]`. Rewrite using `[mem_Dec, mul_smul, mul_smul, hA, hv, h]`.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[conjDec_coe]`. Use `group`.
-/
private theorem conjDec_surj {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (A B : ValuationSubring Ω)
    (γ : G F Ω) (h : γ • A = B) : Function.Surjective (conjDec A B γ h) := by
  intro v
  refine ⟨⟨γ * v * γ⁻¹, ?_⟩, ?_⟩
  · have hv := mem_Dec.1 v.2
    have hA : γ⁻¹ • B = A := by rw [← h, inv_smul_smul]
    rw [mem_Dec, mul_smul, mul_smul, hA, hv, h]
  · apply Subtype.ext
    rw [conjDec_coe]
    group

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ l _ n r w A hA ψ hψ hne A' hA'`. Take `⟨γ, hγ⟩` from `exists_smul_eq_of_isPlaceOver hA hA'`. Take `⟨g, hg⟩` from `hψ`. Use `⟨fun i => (ψ i).comp (conjDec A A' γ hγ), ⟨g * r γ⁻¹, fun s => ?_⟩, ?_⟩` and prove the remaining obligations. Establish `key : g * r γ⁻¹ * r s * (g * r γ⁻¹)⁻¹ = g * r (conjDec A A' γ hγ s : G F Ω) * g⁻¹`.

Rewrite using `[conjDec_coe, map_mul, map_mul, map_inv]`. Use `group`. Use `⟨fun i j hij => ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[key]`. Simplify using `using (hg (conjDec A A' γ hγ s)).1 i j hij`.

Rewrite using `[key]`. Simplify using `using (hg (conjDec A A' γ hγ s)).2 i`. Introduce `i j hij`. Apply `hne i j` to reduce the goal to its premises. Use `ext1 u`.

Take `⟨v, rfl⟩` from `conjDec_surj A A' γ hγ u`. Establish `h1` using `DFunLike.congr_fun hij v`. Simplify using `only [MonoidHom.mul_apply, MonoidHom.comp_apply, Subgroup.coe_subtype] at h1 ⊢`. Rewrite using `[h1, conjDec_coe, map_mul, map_mul, map_inv]`. Use `congr 1`.

Rewrite using `[mul_comm _ ((GlobalTheory.GalOfCusp.cycBar F Ω l) γ), ← mul_assoc, mul_inv_cancel, one_mul]`.
-/
theorem unlOf : UpperTheory.V.Z.Desc.W.UnlOf := by
  intro F Ω _ _ _ _ _ l _ n r w A hA ψ hψ hne A' hA'
  obtain ⟨γ, hγ⟩ := exists_smul_eq_of_isPlaceOver hA hA'
  obtain ⟨g, hg⟩ := hψ
  refine ⟨fun i => (ψ i).comp (conjDec A A' γ hγ), ⟨g * r γ⁻¹, fun s => ?_⟩, ?_⟩
  · have key : g * r γ⁻¹ * r s * (g * r γ⁻¹)⁻¹ = g * r (conjDec A A' γ hγ s : G F Ω) * g⁻¹ := by
      rw [conjDec_coe, map_mul, map_mul, map_inv]
      group
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [key]
      simpa using (hg (conjDec A A' γ hγ s)).1 i j hij
    · rw [key]
      simpa using (hg (conjDec A A' γ hγ s)).2 i
  · intro i j hij
    apply hne i j
    ext1 u
    obtain ⟨v, rfl⟩ := conjDec_surj A A' γ hγ u
    have h1 := DFunLike.congr_fun hij v
    simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, Subgroup.coe_subtype] at h1 ⊢
    rw [h1, conjDec_coe, map_mul, map_mul, map_inv]
    congr 1
    rw [mul_comm _ ((GlobalTheory.GalOfCusp.cycBar F Ω l) γ), ← mul_assoc, mul_inv_cancel, one_mul]

end UpperTheory.V.Z.Desc.W
