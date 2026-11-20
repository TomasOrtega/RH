import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.ComapMaximalIdealParDVR
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

/- English proof (translation)
Introduce `K _ _ n e I f v hI hf W hW`. Establish `: v.asIdeal.IsMaximal` using `v.isMaximal`. Set `R` to `ParDVR e n v`. Set `E` to `(IsLocalRing.maximalIdeal R).ResidueField`. Set `k` to `v.asIdeal.ResidueField`.

Set `_ : Algebra k E` to `(resToKappa e n v).toAlgebra`. Take `⟨hQ, hQdim⟩` from `hDim K n e I f v hI hf W hW`. Take `⟨g, hg⟩` from `hExist k n (e + 1) (reduceMod v W) hQ hQdim`. Establish `hind` using `hInd K e n v`. Establish `hfin` using `(hCNF k E n e (reduceMod v W) g (parYκ e n v) hind hQ hg).1`.

Establish `hdeg` using `hCSD k E n e (reduceMod v W) g (parYκ e n v) hind hQ hg`. Set `ι : 𝓞 K →+* R` to `algebraMap (𝓞 K) R`. Set `ρ : R →+* E` to `algebraMap R E`. Establish `hρ : Function.Surjective ρ` using `Ideal.algebraMap_residueField_surjective _`. Set `Ψ : MvPolynomial (Fin n) R →+* MvPolynomial (Fin n) E` to `MvPolynomial.map ρ`.

Establish `hΨ : Function.Surjective Ψ` using `MvPolynomial.map_surjective _ hρ`. Establish `hcomp : ρ.comp ι = (algebraMap k E).comp (algebraMap (𝓞 K) k)`. Use extensionality with `a`. Conclude with `(Ideal.ResidueField.map_algebraMap _ _ _ _ a).symm`. Establish `hmm : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (φ₁ : A →+* B) (φ₂ : B →+* C), (MvPolynomial.map φ₂).comp (MvPolynomial.map φ₁) = (MvPolynomial.map (φ₂.comp φ₁) : MvPolynomial (Fin n) A →+* MvPolynomial (Fin n) C)` using `fun φ₁ φ₂ ↦ RingHom.ext fun p ↦ MvPolynomial.map_map _ _ p`.

Establish `hJW : integralModel I ⊔ Ideal.map C v.asIdeal ≤ W` using `hW.1.1.2`. Set `WR : Ideal (MvPolynomial (Fin n) R)` to `W.map (MvPolynomial.map ι)`. Set `S` to `secIdeal (modelR e I v) (parY e n v)`. Set `QE` to `(reduceMod v W).map (MvPolynomial.map (algebraMap k E))`. Set `T` to `secIdeal QE (parYκ e n v)`.

Establish `hWR : WR.map Ψ = QE`. Simplify using `only [WR, QE, reduceMod, Ideal.map_map, Ψ, hmm, hcomp]`. Both sides reduce to the same expression. Establish `hM : (modelR e I v).map Ψ ≤ QE`. Rewrite using `[← hWR]`.

Conclude with `Ideal.map_mono (Ideal.map_mono (le_sup_left.trans hJW))`. Establish `hA : (Ideal.span (Set.range (secForm (parY e n v)))).map Ψ = Ideal.span (Set.range (secForm (parYκ e n v)))`. Rewrite using `[Ideal.map_span, ← Set.range_comp]`. Use `congr 2`. Use function extensionality and compare the values at `i`.

Simplify using `[Ψ, secForm, linForm, parYκ, ρ]`. Both sides reduce to the same expression. Establish `hB : (Ideal.span {chartForm (parY e n v) - 1}).map Ψ = Ideal.span {chartForm (parYκ e n v) - 1}`. Rewrite using `[Ideal.map_span, Set.image_singleton]`. Use `congr 2`.

Simplify using `[Ψ, chartForm, linForm, parYκ, ρ]`. Both sides reduce to the same expression. Establish `hT : (S ⊔ WR).map Ψ = T`. Simplify using `only [S, T, secIdeal, Ideal.map_sup, hA, hB, hWR]`. Apply `le_antisymm` to reduce the goal to its premises.

Conclude with `sup_le (sup_le (sup_le (hM.trans (le_sup_left.trans le_sup_left)) (le_sup_right.trans le_sup_left)) le_sup_right) (le_sup_left.trans le_sup_left)`. Conclude with `sup_le (sup_le le_sup_right (le_sup_right.trans (le_sup_left.trans le_sup_left))) (le_sup_right.trans le_sup_left)`. Establish `hkerΨ : RingHom.ker Ψ ≤ WR`. Establish `h1 : ι = (algebraMap (MvPolynomial (Par e n) (𝓞 K)) R).comp C` using `IsScalarTower.algebraMap_eq _ _ _`. Establish `hmax : IsLocalRing.maximalIdeal R = v.asIdeal.map ι`.

Rewrite using `[h1, ← Ideal.map_map]`. Conclude with `Localization.AtPrime.map_eq_maximalIdeal.symm`. Rewrite using `[MvPolynomial.ker_map, Ideal.ker_algebraMap_residueField, hmax, Ideal.map_map, ← MvPolynomial.map_comp_C, ← Ideal.map_map]`. Conclude with `Ideal.map_mono (le_sup_right.trans hJW)`. Set `Φ : MvPolynomial (Fin n) R →ₐ[R] SecAlg QE (parYκ e n v)` to `{ toRingHom := (Ideal.Quotient.mk T).comp Ψ commutes' := fun r ↦ by`.

Simplify using `[Ψ, ρ]`. Use `rfl }`. Establish `hΦ : Function.Surjective Φ` using `Ideal.Quotient.mk_surjective.comp hΨ`. Establish `hker : RingHom.ker Φ = S ⊔ WR`. Establish `: RingHom.ker Φ = T.comap Ψ`.

Use extensionality with `x`. Simplify using `[Φ, RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]`. Rewrite using `[this, ← hT, Ideal.comap_map_of_surjective _ hΨ, ← RingHom.ker_eq_comap_bot]`. Conclude with `sup_eq_left.mpr (hkerΨ.trans le_sup_right)`. Establish `hsec : secIdealOf e I v W = WR.map (Ideal.Quotient.mkₐ R S)` using `rfl`.

Set `eq : (SecB e I v ⧸ secIdealOf e I v W) ≃ₐ[R] SecAlg QE (parYκ e n v)` to `((Ideal.quotientEquivAlgOfEq R hsec).trans (DoubleQuot.quotQuotEquivQuotSupₐ R S WR)).trans ((Ideal.quotientEquivAlgOfEq R hker.symm).trans (Ideal.quotientKerAlgEquivOfSurjective hΦ))`. Rewrite using `[eq.toLinearEquiv.length_eq, Module.length_eq_of_surjective hρ, Module.length_eq_finrank, hdeg]`.
-/
theorem SpecResidue.proof (hCSD : ChowSecDegree.Statement) (hCNF : ChowNormForm.Statement)
    (hDim : SpecCompDim.Statement) (hExist : ChowFormExists.Statement)
    (hInd : ResidueAlgIndep.Statement) : SpecResidue.Statement := by
  intro K _ _ n e I f v hI hf W hW
  have : v.asIdeal.IsMaximal := v.isMaximal
  let R := ParDVR e n v
  let E := (IsLocalRing.maximalIdeal R).ResidueField
  let k := v.asIdeal.ResidueField
  let _ : Algebra k E := (resToKappa e n v).toAlgebra
  obtain ⟨hQ, hQdim⟩ := hDim K n e I f v hI hf W hW
  obtain ⟨g, hg⟩ := hExist k n (e + 1) (reduceMod v W) hQ hQdim
  have hind := hInd K e n v
  have hfin := (hCNF k E n e (reduceMod v W) g (parYκ e n v) hind hQ hg).1
  have hdeg := hCSD k E n e (reduceMod v W) g (parYκ e n v) hind hQ hg

  let ι : 𝓞 K →+* R := algebraMap (𝓞 K) R
  let ρ : R →+* E := algebraMap R E
  have hρ : Function.Surjective ρ := Ideal.algebraMap_residueField_surjective _
  let Ψ : MvPolynomial (Fin n) R →+* MvPolynomial (Fin n) E := MvPolynomial.map ρ
  have hΨ : Function.Surjective Ψ := MvPolynomial.map_surjective _ hρ
  have hcomp : ρ.comp ι = (algebraMap k E).comp (algebraMap (𝓞 K) k) := by
    ext a
    exact (Ideal.ResidueField.map_algebraMap _ _ _ _ a).symm
  have hmm : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (φ₁ : A →+* B) (φ₂ : B →+* C),
      (MvPolynomial.map φ₂).comp (MvPolynomial.map φ₁) =
        (MvPolynomial.map (φ₂.comp φ₁) : MvPolynomial (Fin n) A →+* MvPolynomial (Fin n) C) :=
    fun φ₁ φ₂ ↦ RingHom.ext fun p ↦ MvPolynomial.map_map _ _ p

  have hJW : integralModel I ⊔ Ideal.map C v.asIdeal ≤ W := hW.1.1.2
  let WR : Ideal (MvPolynomial (Fin n) R) := W.map (MvPolynomial.map ι)
  let S := secIdeal (modelR e I v) (parY e n v)
  let QE := (reduceMod v W).map (MvPolynomial.map (algebraMap k E))
  let T := secIdeal QE (parYκ e n v)
  have hWR : WR.map Ψ = QE := by
    simp only [WR, QE, reduceMod, Ideal.map_map, Ψ, hmm, hcomp]
    rfl
  have hM : (modelR e I v).map Ψ ≤ QE := by
    rw [← hWR]
    exact Ideal.map_mono (Ideal.map_mono (le_sup_left.trans hJW))
  have hA : (Ideal.span (Set.range (secForm (parY e n v)))).map Ψ =
      Ideal.span (Set.range (secForm (parYκ e n v))) := by
    rw [Ideal.map_span, ← Set.range_comp]
    congr 2
    funext i
    simp [Ψ, secForm, linForm, parYκ, ρ]
    rfl
  have hB : (Ideal.span {chartForm (parY e n v) - 1}).map Ψ =
      Ideal.span {chartForm (parYκ e n v) - 1} := by
    rw [Ideal.map_span, Set.image_singleton]
    congr 2
    simp [Ψ, chartForm, linForm, parYκ, ρ]
    rfl
  have hT : (S ⊔ WR).map Ψ = T := by
    simp only [S, T, secIdeal, Ideal.map_sup, hA, hB, hWR]
    apply le_antisymm
    · exact sup_le (sup_le (sup_le (hM.trans (le_sup_left.trans le_sup_left))
        (le_sup_right.trans le_sup_left)) le_sup_right) (le_sup_left.trans le_sup_left)
    · exact sup_le (sup_le le_sup_right (le_sup_right.trans (le_sup_left.trans le_sup_left)))
        (le_sup_right.trans le_sup_left)
  have hkerΨ : RingHom.ker Ψ ≤ WR := by
    have h1 : ι = (algebraMap (MvPolynomial (Par e n) (𝓞 K)) R).comp C :=
      IsScalarTower.algebraMap_eq _ _ _
    have hmax : IsLocalRing.maximalIdeal R = v.asIdeal.map ι := by
      rw [h1, ← Ideal.map_map]
      exact Localization.AtPrime.map_eq_maximalIdeal.symm
    rw [MvPolynomial.ker_map, Ideal.ker_algebraMap_residueField, hmax, Ideal.map_map,
      ← MvPolynomial.map_comp_C, ← Ideal.map_map]
    exact Ideal.map_mono (le_sup_right.trans hJW)

  let Φ : MvPolynomial (Fin n) R →ₐ[R] SecAlg QE (parYκ e n v) :=
    { toRingHom := (Ideal.Quotient.mk T).comp Ψ
      commutes' := fun r ↦ by
        simp [Ψ, ρ]
        rfl }
  have hΦ : Function.Surjective Φ := Ideal.Quotient.mk_surjective.comp hΨ
  have hker : RingHom.ker Φ = S ⊔ WR := by
    have : RingHom.ker Φ = T.comap Ψ := by
      ext x
      simp [Φ, RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
    rw [this, ← hT, Ideal.comap_map_of_surjective _ hΨ, ← RingHom.ker_eq_comap_bot]
    exact sup_eq_left.mpr (hkerΨ.trans le_sup_right)
  have hsec : secIdealOf e I v W = WR.map (Ideal.Quotient.mkₐ R S) := rfl
  let eq : (SecB e I v ⧸ secIdealOf e I v W) ≃ₐ[R] SecAlg QE (parYκ e n v) :=
    ((Ideal.quotientEquivAlgOfEq R hsec).trans (DoubleQuot.quotQuotEquivQuotSupₐ R S WR)).trans
      ((Ideal.quotientEquivAlgOfEq R hker.symm).trans (Ideal.quotientKerAlgEquivOfSurjective hΦ))
  rw [eq.toLinearEquiv.length_eq, Module.length_eq_of_surjective hρ, Module.length_eq_finrank,
    hdeg]

end

end GroundTheory.Heights₂.Heights.Vertical
