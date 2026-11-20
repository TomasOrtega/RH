import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTrigPolynomialAnnihilatingAdelicSchwartz
import GroundTheory.GlobalFields.TateThesis.AdelicCharDual
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open Matrix

noncomputable section

namespace GlobalTheory.FinCharCut

open GlobalTheory.FinTrig

/- English proof (translation)
Rewrite `hK` using `[nhds_pi, Filter.mem_pi]`. Take `⟨I, -, t, ht, hIt⟩` from `hK`. Establish `hW : (⋂ i, t i) ∈ nhds (0 : FiniteAdeleRing (𝓞 F) F)` using `Filter.iInter_mem.2 ht`. Take `⟨d, hd0, hd⟩` from `GroundTheory.Global.exists_forall_mul_mem_of_mem_nhds hW`. Use `⟨d, hd0, fun u hu => hIt fun i _ => ?_⟩` and prove the remaining obligations.

Establish `hdK : (algebraMap (𝓞 F) F d) ≠ 0`. Rewrite using `[Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)]` and apply the resulting hypothesis. Establish `hmem` using `hd (algebraMap F (FiniteAdeleRing (𝓞 F) F) ((d : F)⁻¹) * u i) (hu i)`. Establish `he : algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F d) * (algebraMap F (FiniteAdeleRing (𝓞 F) F) ((d : F)⁻¹) * u i) = u i`. Rewrite using `[← mul_assoc, ← map_mul]`.

Establish `: algebraMap (𝓞 F) F d * (d : F)⁻¹ = 1` using `mul_inv_cancel₀ hdK`. Rewrite using `[this, map_one, one_mul]`. Rewrite `hmem` using `[he]`. Conclude with `Set.mem_iInter.1 hmem i`.
-/
theorem exists_lev_subset {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (K : Set (κ → Af F)) (hK : K ∈ nhds (0 : κ → Af F)) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ u : κ → Af F, Lev d u → u ∈ K := by
  rw [nhds_pi, Filter.mem_pi] at hK
  obtain ⟨I, -, t, ht, hIt⟩ := hK
  have hW : (⋂ i, t i) ∈ nhds (0 : FiniteAdeleRing (𝓞 F) F) := Filter.iInter_mem.2 ht
  obtain ⟨d, hd0, hd⟩ := GroundTheory.Global.exists_forall_mul_mem_of_mem_nhds hW
  refine ⟨d, hd0, fun u hu => hIt fun i _ => ?_⟩
  have hdK : (algebraMap (𝓞 F) F d) ≠ 0 := by
    rwa [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)]
  have hmem := hd (algebraMap F (FiniteAdeleRing (𝓞 F) F) ((d : F)⁻¹) * u i) (hu i)
  have he : algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F d) *
      (algebraMap F (FiniteAdeleRing (𝓞 F) F) ((d : F)⁻¹) * u i) = u i := by
    rw [← mul_assoc, ← map_mul]
    have : algebraMap (𝓞 F) F d * (d : F)⁻¹ = 1 := mul_inv_cancel₀ hdK
    rw [this, map_one, one_mul]
  rw [he] at hmem
  exact Set.mem_iInter.1 hmem i

/- English proof (translation)
Introduce `F _ _ κ _ ψ hψ C K hC hK h0 y`. Take `⟨d, -, hdK⟩` from `exists_lev_subset K (hK.mem_nhds h0)`. Use `set yf : κ → FiniteAdeleRing (𝓞 F) F := fun i => (y i).2 with hyf`. Use `set C' := C ∩ {z | Lev d (z - yf)}ᶜ with hC'def`. Establish `hC' : IsCompact C'` using `hC.inter_right (isOpen_lev d yf).isClosed_compl`.

Take `⟨t, htC, hcov⟩` from `hC'.elim_nhds_subcover (fun a => {z | Lev d (z - a)}) (fun a _ => (isOpen_lev d a).mem_nhds (by simp only [Set.mem_setOf_eq, sub_self]; exact lev_zero d))`. Establish `hsep : ∀ a ∈ C', ∃ q ∈ (Q0 : Set (κ → AF F)), ψ (vecFin (a - yf) ⬝ᵥ q) ≠ 1 ∧ ∀ u, Lev d u → ψ (vecFin u ⬝ᵥ q) = 1` using `fun a ha => exists_sep ψ hψ d (a - yf) ha.2`. Use `choose! q hq0 hq1 hq2 using hsep`. Use `set c : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ := fun a => ψ (vecFin (a - yf) ⬝ᵥ q a) with hc`. Use `set φ : (κ → FiniteAdeleRing (𝓞 F) F) → (κ → AF F) → ℂ := fun a => (1 - c a)⁻¹ • (ψ (-(y ⬝ᵥ q a)) • chi ψ (q a) - c a • 1) with hφ`.

Establish `hφx : ∀ a ∈ C', ∀ x, φ a x = (1 - c a)⁻¹ * (ψ (vecFin ((fun i => (x i).2) - yf) ⬝ᵥ q a) - c a)`. Introduce `a ha x`. Establish `e1 : ψ (-(y ⬝ᵥ q a)) * ψ (x ⬝ᵥ q a) = ψ (vecFin ((fun i => (x i).2) - yf) ⬝ᵥ q a)`. Rewrite using `[← AddChar.map_add_eq_mul, neg_add_eq_sub, ← sub_dotProduct, dot_eq_vecFin (hq0 a ha)]`. Both sides reduce to the same expression.

Simplify using `only [hφ, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, chi, Pi.one_apply, mul_one]`. Rewrite using `[e1]`. Establish `hφmem : ∀ a ∈ t, φ a ∈ TP ψ` using `fun a ha => Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.smul_mem _ _ (chi_mem ψ (hq0 a (htC a ha)))) (Submodule.smul_mem _ _ (one_mem_TP ψ)))`. Take `⟨s, cc, hs, hP⟩` from `exists_of_mem_TP ψ (prod_mem_TP ψ t φ hφmem)`. Use `⟨s, cc, fun b hb i => fst_eq_zero (hs b hb i), ?_, fun x hxC hxK => ?_⟩` and prove the remaining obligations.

Rewrite using `[← hP y, Finset.prod_apply]`. Use `Finset.prod_eq_one fun a ha => ?_` and prove the remaining obligations. Rewrite using `[hφx a (htC a ha)]`. Establish `e0 : (fun i => (y i).2) - yf = 0` using `sub_self _`. Establish `hne : 1 - c a ≠ 0` using `sub_ne_zero.mpr (Ne.symm (hq1 a (htC a ha)))`.

Rewrite using `[e0, vecFin_zero, zero_dotProduct, AddChar.map_zero_eq_one, inv_mul_cancel₀ hne]`. Rewrite using `[← hP x, Finset.prod_apply]`. Establish `hL : ¬ Lev d ((fun i => (x i).2) - yf)`. Introduce `hL`. Use `hxK _ (hdK _ hL) ?_` and prove the remaining obligations.

Use function extensionality and compare the values at `i`. Simplify using `[yf]`. Establish `hxC' : (fun i => (x i).2) ∈ C'` using `⟨hxC, hL⟩`. Take `⟨a, hat, hxa⟩` from `Set.mem_iUnion₂.mp (hcov hxC')`. Rewrite using `[Finset.prod_eq_zero hat]`.

Rewrite using `[hφx a (htC a hat)]`. Establish `e : (fun i => (x i).2) - yf = ((fun i => (x i).2) - a) + (a - yf)` using `(sub_add_sub_cancel _ _ _).symm`. Rewrite using `[e, vecFin_add, add_dotProduct, AddChar.map_add_eq_mul, hq2 a (htC a hat) _ hxa, one_mul, sub_self, mul_zero]`.
-/
theorem fin_char_cut : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ (C K : Set (κ → Af F)), IsCompact C → IsOpen K → (0 : κ → Af F) ∈ K →
    ∀ y : κ → AF F, ∃ (s : Finset (κ → AF F)) (c : (κ → AF F) → ℂ), (∀ b ∈ s, ∀ i, (b i).1 = 0) ∧
      ∑ b ∈ s, c b * ψ (y ⬝ᵥ b) = 1 ∧
      ∀ x : κ → AF F, (fun i => (x i).2) ∈ C → (∀ k ∈ K, (fun i => (x i).2) ≠ (fun i => (y i).2) + k) →
        ∑ b ∈ s, c b * ψ (x ⬝ᵥ b) = 0 := by
  intro F _ _ κ _ ψ hψ C K hC hK h0 y
  classical
  obtain ⟨d, -, hdK⟩ := exists_lev_subset K (hK.mem_nhds h0)
  set yf : κ → FiniteAdeleRing (𝓞 F) F := fun i => (y i).2 with hyf
  set C' := C ∩ {z | Lev d (z - yf)}ᶜ with hC'def
  have hC' : IsCompact C' := hC.inter_right (isOpen_lev d yf).isClosed_compl
  obtain ⟨t, htC, hcov⟩ := hC'.elim_nhds_subcover (fun a => {z | Lev d (z - a)})
    (fun a _ => (isOpen_lev d a).mem_nhds (by simp only [Set.mem_setOf_eq, sub_self]; exact lev_zero d))
  have hsep : ∀ a ∈ C', ∃ q ∈ (Q0 : Set (κ → AF F)), ψ (vecFin (a - yf) ⬝ᵥ q) ≠ 1 ∧
      ∀ u, Lev d u → ψ (vecFin u ⬝ᵥ q) = 1 := fun a ha => exists_sep ψ hψ d (a - yf) ha.2
  choose! q hq0 hq1 hq2 using hsep
  set c : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ := fun a => ψ (vecFin (a - yf) ⬝ᵥ q a) with hc
  set φ : (κ → FiniteAdeleRing (𝓞 F) F) → (κ → AF F) → ℂ := fun a =>
    (1 - c a)⁻¹ • (ψ (-(y ⬝ᵥ q a)) • chi ψ (q a) - c a • 1) with hφ
  have hφx : ∀ a ∈ C', ∀ x, φ a x = (1 - c a)⁻¹ * (ψ (vecFin ((fun i => (x i).2) - yf) ⬝ᵥ q a) - c a) := by
    intro a ha x
    have e1 : ψ (-(y ⬝ᵥ q a)) * ψ (x ⬝ᵥ q a) = ψ (vecFin ((fun i => (x i).2) - yf) ⬝ᵥ q a) := by
      rw [← AddChar.map_add_eq_mul, neg_add_eq_sub, ← sub_dotProduct, dot_eq_vecFin (hq0 a ha)]
      rfl
    simp only [hφ, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, chi, Pi.one_apply, mul_one]
    rw [e1]
  have hφmem : ∀ a ∈ t, φ a ∈ TP ψ := fun a ha =>
    Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.smul_mem _ _ (chi_mem ψ (hq0 a (htC a ha))))
      (Submodule.smul_mem _ _ (one_mem_TP ψ)))
  obtain ⟨s, cc, hs, hP⟩ := exists_of_mem_TP ψ (prod_mem_TP ψ t φ hφmem)
  refine ⟨s, cc, fun b hb i => fst_eq_zero (hs b hb i), ?_, fun x hxC hxK => ?_⟩
  · rw [← hP y, Finset.prod_apply]
    refine Finset.prod_eq_one fun a ha => ?_
    rw [hφx a (htC a ha)]
    have e0 : (fun i => (y i).2) - yf = 0 := sub_self _
    have hne : 1 - c a ≠ 0 := sub_ne_zero.mpr (Ne.symm (hq1 a (htC a ha)))
    rw [e0, vecFin_zero, zero_dotProduct, AddChar.map_zero_eq_one, inv_mul_cancel₀ hne]
  · rw [← hP x, Finset.prod_apply]
    have hL : ¬ Lev d ((fun i => (x i).2) - yf) := by
      intro hL
      refine hxK _ (hdK _ hL) ?_
      funext i
      simp [yf]
    have hxC' : (fun i => (x i).2) ∈ C' := ⟨hxC, hL⟩
    obtain ⟨a, hat, hxa⟩ := Set.mem_iUnion₂.mp (hcov hxC')
    rw [Finset.prod_eq_zero hat]
    rw [hφx a (htC a hat)]
    have e : (fun i => (x i).2) - yf = ((fun i => (x i).2) - a) + (a - yf) := (sub_add_sub_cancel _ _ _).symm
    rw [e, vecFin_add, add_dotProduct, AddChar.map_add_eq_mul, hq2 a (htC a hat) _ hxa, one_mul, sub_self,
      mul_zero]

end GlobalTheory.FinCharCut
