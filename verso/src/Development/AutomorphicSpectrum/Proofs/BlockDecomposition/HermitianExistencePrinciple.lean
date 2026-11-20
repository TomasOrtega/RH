import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemNormGroupIffEverywhereNorm
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.RgBase

open PositivityTheory.Rg.Base1

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Establish `e` using `GlobalTheory.Doubling.algebraMap_norm_eq h (R := AF F) x`. Rewrite `e` using `[Algebra.TensorProduct.algebraMap_apply]`. Rewrite using `[mul_comm]`. Conclude with `e`.
-/
theorem norm_tmul_one {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : AF F ⊗[F] E) :
    (Algebra.norm (AF F) x) ⊗ₜ[F] (1 : E) = sigR (AF F) σ x * x := by
  have e := GlobalTheory.Doubling.algebraMap_norm_eq h (R := AF F) x
  rw [Algebra.TensorProduct.algebraMap_apply] at e
  rw [mul_comm]
  exact e

/- English proof (translation)
Establish `hinj : Function.Injective (fun r : AF F => r ⊗ₜ[F] (1 : E))` using `Algebra.TensorProduct.includeLeft_injective (S := F) (algebraMap F E).injective`. Unfold `IsNm`. Rewrite using `[← norm_tmul_one h]`. Conclude with `⟨fun e => (hinj e).symm, fun e => by rw [e]⟩`.
-/
theorem isNm_iff {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : (AF F ⊗[F] E)ˣ) (a : (AF F)ˣ) :
    IsNm σ x a ↔ Algebra.norm (AF F) (x : AF F ⊗[F] E) = a := by
  have hinj : Function.Injective (fun r : AF F => r ⊗ₜ[F] (1 : E)) :=
    Algebra.TensorProduct.includeLeft_injective (S := F) (algebraMap F E).injective
  unfold IsNm
  rw [← norm_tmul_one h]
  exact ⟨fun e => (hinj e).symm, fun e => by rw [e]⟩

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ h`. Use `haveI : Algebra.IsQuadraticExtension F E := ⟨h.2.2.1⟩`. Use `⟨(GlobalTheory.IdeleNormChar.normSign (K := F) E).ker, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `a`. Rewrite using `[MonoidHom.mem_ker]`.

Prove the components needed by the constructor for the conclusion. Introduce `ha`. Take `⟨t, x, hx⟩` from `(GlobalTheory.IdeleNormChar.normSign_eq_one_iff E a).1 ha`. Use `⟨t, x, a / GlobalTheory.QuadSymbol.toUnits F (AdeleRing (𝓞 F) F) t, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(isNm_iff h x _).2 (congrArg Units.val hx)`.

Conclude with `(mul_div_cancel (GlobalTheory.QuadSymbol.toUnits F (AdeleRing (𝓞 F) F) t) a).symm`. Introduce and unpack `⟨t, x, n, hn, rfl⟩`. Establish `h1 : GlobalTheory.IdeleNormChar.normSign E (pr t) = 1` using `GlobalTheory.IdeleNormChar.normSign_toUnits E t`. Establish `h2 : GlobalTheory.IdeleNormChar.normSign E n = 1` using `GlobalTheory.IdeleNormChar.normSign_of_mem E ⟨x, Units.ext ((isNm_iff h x n).1 hn)⟩`. Rewrite using `[map_mul, h1, h2, one_mul]`.

Use `Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_ filter_upwards [GlobalTheory.IdeleNormChar.eventually_normSign (K := F) E] with a ha` and prove the remaining obligations. Conclude with `ha`. Take `⟨b, hb⟩` from `GlobalTheory.IdeleNormChar.exists_normSign_ne_one (K := F) E`. Establish `hr : (GlobalTheory.IdeleNormChar.normSign (K` using `F) E).range = ⊤ := by`. Rewrite using `[eq_top_iff]`.

Introduce `u _`. Break down `Int.units_eq_one_or u with rfl | rfl` into its components or cases. Conclude with `one_mem _`. Conclude with `⟨b, (Int.units_eq_one_or _).resolve_left hb⟩`. Rewrite using `[Subgroup.index_ker, hr, Subgroup.card_top, Nat.card_eq_fintype_card, Fintype.card_units_int]`.
-/
theorem hEx : HEx := by
  intro F E _ _ _ _ _ σ h
  haveI : Algebra.IsQuadraticExtension F E := ⟨h.2.2.1⟩
  refine ⟨(GlobalTheory.IdeleNormChar.normSign (K := F) E).ker, ?_, ?_, ?_⟩
  · intro a
    rw [MonoidHom.mem_ker]
    constructor
    · intro ha
      obtain ⟨t, x, hx⟩ := (GlobalTheory.IdeleNormChar.normSign_eq_one_iff E a).1 ha
      refine ⟨t, x, a / GlobalTheory.QuadSymbol.toUnits F (AdeleRing (𝓞 F) F) t, ?_, ?_⟩
      · exact (isNm_iff h x _).2 (congrArg Units.val hx)
      · exact (mul_div_cancel (GlobalTheory.QuadSymbol.toUnits F (AdeleRing (𝓞 F) F) t) a).symm
    · rintro ⟨t, x, n, hn, rfl⟩
      have h1 : GlobalTheory.IdeleNormChar.normSign E (pr t) = 1 := GlobalTheory.IdeleNormChar.normSign_toUnits E t
      have h2 : GlobalTheory.IdeleNormChar.normSign E n = 1 :=
        GlobalTheory.IdeleNormChar.normSign_of_mem E ⟨x, Units.ext ((isNm_iff h x n).1 hn)⟩
      rw [map_mul, h1, h2, one_mul]
  · refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    filter_upwards [GlobalTheory.IdeleNormChar.eventually_normSign (K := F) E] with a ha
    exact ha
  · obtain ⟨b, hb⟩ := GlobalTheory.IdeleNormChar.exists_normSign_ne_one (K := F) E
    have hr : (GlobalTheory.IdeleNormChar.normSign (K := F) E).range = ⊤ := by
      rw [eq_top_iff]
      intro u _
      rcases Int.units_eq_one_or u with rfl | rfl
      · exact one_mem _
      · exact ⟨b, (Int.units_eq_one_or _).resolve_left hb⟩
    rw [Subgroup.index_ker, hr, Subgroup.card_top, Nat.card_eq_fintype_card, Fintype.card_units_int]

end GlobalTheory.CompanionTheory.RgBase

end
