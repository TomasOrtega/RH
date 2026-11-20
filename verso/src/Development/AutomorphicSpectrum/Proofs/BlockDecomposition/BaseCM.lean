import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SiegelOneDescent.Descend2

open NumberField Matrix
open scoped NumberField.AdeleRing
open PositivityTheory.RgEis PositivityTheory.RgEis.So GroundTheory.Global
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

namespace GlobalTheory.CompanionTheory.SgOneBase

/- English proof (translation)
Introduce `_ hFix hRat hInt hInf hLg hDel F E _ _ _ _ _ σ χ c hCM hUn hHk hRes ε`. Take `⟨hνc, hνi, hνfix, r, hrc, hrfix⟩` from `hFix F E σ χ c hCM hUn hHk hRes`. Take `⟨hrat, hrat'⟩` from `hRat F E σ χ c hCM hUn hHk hRes`. Establish `hint` using `hInt F E σ χ c hCM hUn hHk hRes`. Take `⟨hinf, hinf'⟩` from `hInf F E σ χ c hCM hUn hHk hRes`.

Take `⟨hlg, hlgσ⟩` from `hLg F E σ χ c hCM hUn hHk hRes`. Take `⟨δ0, α0, u0, hσδ, hδα, huO, huiO, hun⟩` from `hDel F E σ χ c hCM hUn hHk hRes`. Establish `hσi : ∀ x : E, (adCM σ χ).σ ((adCM σ χ).i x) = (adCM σ χ).i (σ x)`. Introduce `x`. Use `show Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ (Algebra.TensorProduct.includeRight x) = Algebra.TensorProduct.includeRight (σ x)`.

Simplify using `[Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]`. Set `f : IdeleGroup F →* Circle` to `χ.comp (Units.map (nuCM F E).toMonoidHom)`. Establish `hker : (IdeleGroup.diagonal F).range ≤ f.ker`. Introduce and unpack `_ ⟨a, rfl⟩`. Rewrite using `[MonoidHom.mem_ker]`.

Establish `e : Units.map (nuCM F E).toMonoidHom (IdeleGroup.diagonal F a) = Units.map (inclR (F` using `F) (E := E) (AF F) : E →* TensorProduct F (AF F) E) (Units.map (algebraMap F E : F →* E) a) := Units.ext (hrat a)`. Use `show χ (Units.map (nuCM F E).toMonoidHom (IdeleGroup.diagonal F a)) = 1`. Rewrite using `[e]`. Conclude with `hHk.2 _`. Establish `hfc : Continuous f` using `hHk.1.comp (Continuous.units_map _ hνc)`.

Set `ω : HeckeCharacter F` to `⟨QuotientGroup.lift _ f hker, (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 hfc⟩`. Establish `hω : ∀ x : IdeleGroup F, ω.toIdele x = (adCM σ χ).χ (Units.map (nuCM F E).toMonoidHom x)` using `fun x => rfl`. Break down `Int.units_eq_one_or ε with rfl | rfl` into its components or cases. Use `⟨r, δ0, α0, ω, ⟨hνc, hνi, hνfix, hrc, hrfix, hrat, hrat', hint, hinf, hinf', hlg, hlgσ, ?_, ⟨u0, hδα, huO, huiO, hun⟩, hω⟩⟩` and prove the remaining obligations. Rewrite using `[hσi, hσδ, map_neg]`.

Simplify using the standard rewrite rules. Use `⟨r, 1, 1, ω, ⟨hνc, hνi, hνfix, hrc, hrfix, hrat, hrat', hint, hinf, hinf', hlg, hlgσ, ?_, ⟨1, ?_, ?_, ?_, ?_⟩, hω⟩⟩` and prove the remaining obligations. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using `using (adCM σ χ).O.one_mem`.

Simplify using `using (adCM σ χ).O.one_mem`. Introduce `w`. Simplify using the standard rewrite rules.
-/
theorem baseCM : CMGood → BFix → BRat → BInt → BInf → BLg → BDel → BaseCM := by
  intro _ hFix hRat hInt hInf hLg hDel F E _ _ _ _ _ σ χ c hCM hUn hHk hRes ε
  obtain ⟨hνc, hνi, hνfix, r, hrc, hrfix⟩ := hFix F E σ χ c hCM hUn hHk hRes
  obtain ⟨hrat, hrat'⟩ := hRat F E σ χ c hCM hUn hHk hRes
  have hint := hInt F E σ χ c hCM hUn hHk hRes
  obtain ⟨hinf, hinf'⟩ := hInf F E σ χ c hCM hUn hHk hRes
  obtain ⟨hlg, hlgσ⟩ := hLg F E σ χ c hCM hUn hHk hRes
  obtain ⟨δ0, α0, u0, hσδ, hδα, huO, huiO, hun⟩ := hDel F E σ χ c hCM hUn hHk hRes
  have hσi : ∀ x : E, (adCM σ χ).σ ((adCM σ χ).i x) = (adCM σ χ).i (σ x) := by
    intro x
    show Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ (Algebra.TensorProduct.includeRight x) =
      Algebra.TensorProduct.includeRight (σ x)
    simp [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]
  let f : IdeleGroup F →* Circle := χ.comp (Units.map (nuCM F E).toMonoidHom)
  have hker : (IdeleGroup.diagonal F).range ≤ f.ker := by
    rintro _ ⟨a, rfl⟩
    rw [MonoidHom.mem_ker]
    have e : Units.map (nuCM F E).toMonoidHom (IdeleGroup.diagonal F a) =
        Units.map (inclR (F := F) (E := E) (AF F) : E →* TensorProduct F (AF F) E) (Units.map (algebraMap F E : F →* E) a) :=
      Units.ext (hrat a)
    show χ (Units.map (nuCM F E).toMonoidHom (IdeleGroup.diagonal F a)) = 1
    rw [e]
    exact hHk.2 _
  have hfc : Continuous f := hHk.1.comp (Continuous.units_map _ hνc)
  let ω : HeckeCharacter F :=
    ⟨QuotientGroup.lift _ f hker, (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 hfc⟩
  have hω : ∀ x : IdeleGroup F, ω.toIdele x = (adCM σ χ).χ (Units.map (nuCM F E).toMonoidHom x) := fun x => rfl
  rcases Int.units_eq_one_or ε with rfl | rfl
  · refine ⟨r, δ0, α0, ω, ⟨hνc, hνi, hνfix, hrc, hrfix, hrat, hrat', hint, hinf, hinf', hlg, hlgσ, ?_,
      ⟨u0, hδα, huO, huiO, hun⟩, hω⟩⟩
    rw [hσi, hσδ, map_neg]
    simp
  · refine ⟨r, 1, 1, ω, ⟨hνc, hνi, hνfix, hrc, hrfix, hrat, hrat', hint, hinf, hinf', hlg, hlgσ, ?_,
      ⟨1, ?_, ?_, ?_, ?_⟩, hω⟩⟩
    · simp
    · simp
    · simpa using (adCM σ χ).O.one_mem
    · simpa using (adCM σ χ).O.one_mem
    · intro w
      simp

end GlobalTheory.CompanionTheory.SgOneBase
