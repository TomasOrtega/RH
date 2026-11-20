import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.IsMultiHomogIdealIff
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PIntNumPoint
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Assembly
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.BlockInclInjectiveOfEmbedding
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G

noncomputable section

universe u

namespace ProjContract

/- English proof (translation)
Rewrite using `[Finsupp.sum, finsum_eq_sum_of_support_subset]`. Introduce `W hW`. Rewrite `hW` using `[Function.mem_support]`. Rewrite using `[Finset.mem_coe, Finsupp.mem_support_iff]`. Introduce `h0`.

Conclude with `hW (by rw [h0, zero_mul])`.
-/
theorem finsum_mul_eq_sum {α : Type*} (D : α →₀ ℤ) (J : α → ℤ) :
    ∑ᶠ W, D W * J W = D.sum fun W m => m * J W := by
  classical
  rw [Finsupp.sum, finsum_eq_sum_of_support_subset]
  intro W hW
  rw [Function.mem_support] at hW
  rw [Finset.mem_coe, Finsupp.mem_support_iff]
  intro h0
  exact hW (by rw [h0, zero_mul])

section Theory

variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]

omit [DecidableEq K] in

/- English proof (translation)
Simplify using `only [NumbersDVR.ratDiv, AI.I1.ratDiv, Finsupp.sub_apply, Finsupp.mapRange_apply]`. Rewrite using `[Bridge.divCycle_eq, Bridge.divCycle_eq]`.
-/
theorem ratDiv_eq (P : Ideal (NumbersDVR.MRing ι F)) (f g : NumbersDVR.MRing ι F)
    (W : Ideal (NumbersDVR.MRing ι F)) :
    NumbersDVR.ratDiv P f g W = AI.I1.ratDiv P f g W := by
  simp only [NumbersDVR.ratDiv, AI.I1.ratDiv, Finsupp.sub_apply, Finsupp.mapRange_apply]
  rw [Bridge.divCycle_eq, Bridge.divCycle_eq]

/- English proof (translation)
Use `choose i hi using hP.relevant`. Establish `hd` using `(FieldNumbers.relDim_eq_iff_hasRelDim P 0).mp h0`. Establish `hV : AI.I1.IsProjVarF P 0` using `⟨(Bridge.isMultiProjPrime_iff P).mp hP, hd⟩`. Establish `h1` using `hI.1 P ![] i hV hi`. Establish `h2` using `NumbersDVR.IntNumPoint.proof FieldNumbers.IntNumBase.full F K ι P i hP hd hi`.

Establish `h3` using `(FieldNumbers.IntNumBase.full F K ι P hP h0).2`. Establish `h4 : FieldNumbers.resDeg P = Module.finrank F (@FieldNumbers.homFracDegZero _ _ _ _ _ P hP.isPrime)`. Rewrite using `[FieldNumbers.resDeg, dif_pos hP.isPrime]`. Rewrite using `[h1, ← h2, h3, h4]`. Use `cut P n hP hn bf bg f g hf hg hfP hgP bs := by`.

Establish `hd` using `(FieldNumbers.relDim_eq_iff_hasRelDim P (n + 1)).mp hn`. Rewrite using `[hI.2 P n bs _ f g ⟨(Bridge.isMultiProjPrime_iff P).mp hP, hd⟩ ⟨bf, bg, (Bridge.isMultiHomog_iff f bf).mp hf, (Bridge.isMultiHomog_iff g bg).mp hg, hfP, hgP, fun k => rfl⟩]`. Simplify using `only [NumbersDVR.cycEval, AI.I1.cycEval, ratDiv_eq]`. Conclude with `(finsum_mul_eq_sum _ _).symm`.
-/
theorem isIntersectionTheory (I : AI.I1.IFamily F ι) (hI : AI.I1.IsFieldIntersection I) :
    FieldNumbers.IsIntersectionTheory F I where
  base P hP h0 := by
    choose i hi using hP.relevant
    have hd := (FieldNumbers.relDim_eq_iff_hasRelDim P 0).mp h0
    have hV : AI.I1.IsProjVarF P 0 := ⟨(Bridge.isMultiProjPrime_iff P).mp hP, hd⟩
    have h1 := hI.1 P ![] i hV hi
    have h2 := NumbersDVR.IntNumPoint.proof FieldNumbers.IntNumBase.full F K ι P i hP hd hi
    have h3 := (FieldNumbers.IntNumBase.full F K ι P hP h0).2
    have h4 : FieldNumbers.resDeg P = Module.finrank F
        (@FieldNumbers.homFracDegZero _ _ _ _ _ P hP.isPrime) := by
      rw [FieldNumbers.resDeg, dif_pos hP.isPrime]
    rw [h1, ← h2, h3, h4]
  cut P n hP hn bf bg f g hf hg hfP hgP bs := by
    have hd := (FieldNumbers.relDim_eq_iff_hasRelDim P (n + 1)).mp hn
    rw [hI.2 P n bs _ f g ⟨(Bridge.isMultiProjPrime_iff P).mp hP, hd⟩
      ⟨bf, bg, (Bridge.isMultiHomog_iff f bf).mp hf, (Bridge.isMultiHomog_iff g bg).mp hg, hfP, hgP,
        fun k => rfl⟩]
    simp only [NumbersDVR.cycEval, AI.I1.cycEval, ratDiv_eq]
    exact (finsum_mul_eq_sum _ _).symm

end Theory

section Image

variable {F : Type u} [Field F] {K : Type} {ι : K → Type} {K' : Type} {ι' : K' → Type}
  {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')}

def emb (hv : AI.I1.IsBlockMap κ v) : K ↪ K' := ⟨κ, hv.1⟩

/- English proof (translation)
Use extensionality with `q`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨p, rfl⟩`. Establish `h` using `hv.2.2.1 p`. Use `revert h`.

Generalize the expression as in `v p = q`. Take `⟨a, b⟩` from `q`. Introduce and unpack `(rfl : a = κ p.1)`. Conclude with `⟨⟨p.1, b⟩, rfl⟩`. Introduce and unpack `⟨⟨k, x⟩, rfl⟩`.

Conclude with `hv.2.2.2 _ ⟨k, rfl⟩`.
-/
theorem range_eq (hv : AI.I1.IsBlockMap κ v) :
    Set.range v = Set.range (FieldNumbers.blockIncl (emb hv) ι') := by
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    have h := hv.2.2.1 p
    revert h
    generalize v p = q
    obtain ⟨a, b⟩ := q
    rintro (rfl : a = κ p.1)
    exact ⟨⟨p.1, b⟩, rfl⟩
  · rintro ⟨⟨k, x⟩, rfl⟩
    exact hv.2.2.2 _ ⟨k, rfl⟩

def blockEquiv (hv : AI.I1.IsBlockMap κ v) : (Σ k, ι k) ≃ (Σ k, ι' (emb hv k)) :=
  (Equiv.ofInjective v hv.2.1).trans ((Equiv.setCongr (range_eq hv)).trans
    (Equiv.ofInjective _ (FieldNumbers.PFContracted.blockIncl_injective_of_embedding (emb hv) ι')).symm)

/- English proof (translation)
Simplify using `[blockEquiv, Equiv.apply_ofInjective_symm]`.
-/
theorem blockIncl_blockEquiv (hv : AI.I1.IsBlockMap κ v) (p : Σ k, ι k) :
    FieldNumbers.blockIncl (emb hv) ι' (blockEquiv hv p) = v p := by
  simp [blockEquiv, Equiv.apply_ofInjective_symm]

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [AI.I1.imageVar, FieldNumbers.contractPrime, Ideal.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_rename]`. Establish `: (FieldNumbers.blockIncl (emb hv) ι' ∘ blockEquiv hv) = v` using `funext (blockIncl_blockEquiv hv)`. Rewrite using `[this]`.
-/
theorem imageVar_eq (hv : AI.I1.IsBlockMap κ v) (V' : Ideal (Geo.MRingOver F ι')) :
    AI.I1.imageVar F v V' = (FieldNumbers.contractPrime (emb hv) V').comap
      (rename (blockEquiv hv) : Geo.MRingOver F ι →ₐ[F] _).toRingHom := by
  ext x
  simp only [AI.I1.imageVar, FieldNumbers.contractPrime, Ideal.mem_comap, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, rename_rename]
  have : (FieldNumbers.blockIncl (emb hv) ι' ∘ blockEquiv hv) = v := funext (blockIncl_blockEquiv hv)
  rw [this]

/- English proof (translation)
Rewrite using `[imageVar_eq hv]`. Use `set J := FieldNumbers.contractPrime (emb hv) V'`. Set `e` to `(renameEquiv F (blockEquiv hv)).toRingEquiv`. Use `ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ J e ?_)` and prove the remaining obligations. Conclude with `(Ideal.map_comap_of_surjective _ e.surjective J).symm`.
-/
theorem ringKrullDim_imageVar (hv : AI.I1.IsBlockMap κ v) (V' : Ideal (Geo.MRingOver F ι')) :
    ringKrullDim (Geo.MRingOver F ι ⧸ AI.I1.imageVar F v V') =
      ringKrullDim (NumbersDVR.MRing (fun k => ι' (emb hv k)) F ⧸
        FieldNumbers.contractPrime (emb hv) V') := by
  rw [imageVar_eq hv]
  set J := FieldNumbers.contractPrime (emb hv) V'
  let e := (renameEquiv F (blockEquiv hv)).toRingEquiv
  refine ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ J e ?_)
  exact (Ideal.map_comap_of_surjective _ e.surjective J).symm

end Image

end ProjContract

open ProjContract in

/- English proof (translation)
Introduce `F _ K _ ι _ K' _ ι' _`. Introduce `I' hI' κ v V' e d L hv hV' hVd hde`. Establish `hrel : FieldNumbers.relDim V' = e` using `(FieldNumbers.relDim_eq_iff_hasRelDim V' e).mpr hV'.2`. Establish `hV'f : NumbersDVR.IsMultiProjPrime V'` using `(Bridge.isMultiProjPrime_iff V').mpr hV'.1`. Rewrite using `[FieldNumbers.IntNumUnique.full F K' ι' I' (isIntersectionTheory I' hI') V' hV'f e hrel]`.

Establish `hc : FieldNumbers.relDim (FieldNumbers.contractPrime (emb hv) V') = d`. Use `(FieldNumbers.relDim_eq_iff_hasRelDim _ d).mpr ?_` and prove the remaining obligations. Use `show ringKrullDim _ = _`. Rewrite using `[← ringKrullDim_imageVar hv]`. Conclude with `hVd.2`.

Conclude with `FieldNumbers.ProjectionFormulaContracted.full F K K' (emb hv) ι' V' hV'f e hrel (lt_of_eq_of_lt hc (FieldNumbers.PFContracted.natCast_lt_withBotWithTop hde)) L`.
-/
theorem ProjContract.full :
    ∀ (F : Type u) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)],
      ReciprocityTheory.ChartRestriction.G.AI.I1.ProjContractStatement F ι ι' := by
  intro F _ K _ ι _ K' _ ι' _
  classical
  intro I' hI' κ v V' e d L hv hV' hVd hde
  have hrel : FieldNumbers.relDim V' = e := (FieldNumbers.relDim_eq_iff_hasRelDim V' e).mpr hV'.2
  have hV'f : NumbersDVR.IsMultiProjPrime V' := (Bridge.isMultiProjPrime_iff V').mpr hV'.1
  rw [FieldNumbers.IntNumUnique.full F K' ι' I' (isIntersectionTheory I' hI') V' hV'f e hrel]
  have hc : FieldNumbers.relDim (FieldNumbers.contractPrime (emb hv) V') = d := by
    refine (FieldNumbers.relDim_eq_iff_hasRelDim _ d).mpr ?_
    show ringKrullDim _ = _
    rw [← ringKrullDim_imageVar hv]
    exact hVd.2
  exact FieldNumbers.ProjectionFormulaContracted.full F K K' (emb hv) ι' V' hV'f e hrel
    (lt_of_eq_of_lt hc (FieldNumbers.PFContracted.natCast_lt_withBotWithTop hde)) L

end

end GroundTheory.Heights₂.Heights.Targets
