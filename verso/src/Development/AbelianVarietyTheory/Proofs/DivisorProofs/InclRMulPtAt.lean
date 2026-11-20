import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInertLocalUniformizerImports
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertCoord

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : Pl F} {w : HeightOneSpectrum (𝓞 E)}

def ptAt (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v) : w.adicCompletion E →ₙ+* AE F E :=
  (GlobalTheory.AdelicU.Supp.singleTens E v).comp (InertChart.complEquiv hw h).symm.toRingHom.toNonUnitalRingHom

def locW (h : w.under (𝓞 F) = v) : AE F E →+* w.adicCompletion E := (toCompl h).comp (compFin F E v)

def kap (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v) {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) (w.adicCompletion E)) (B : Matrix (Fin n) (Fin n) (w.adicCompletion E)) :
    Matrix (Fin n) (Fin m) (w.adicCompletion E) →+ Matrix (Fin m) (Fin n) (AE F E) :=
  (AddMonoidHom.mapMatrix (ptAt hw h).toAddMonoidHom).comp
    { toFun := fun x => A * xᵀ * Bᵀ
      map_zero' := by simp
      map_add' := fun x y => by simp [Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul] }

variable (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem kap_apply {m n : ℕ} (A : Matrix (Fin m) (Fin m) (w.adicCompletion E)) (B : Matrix (Fin n) (Fin n) (w.adicCompletion E))
    (x : Matrix (Fin n) (Fin m) (w.adicCompletion E)) : kap hw h A B x = (A * xᵀ * Bᵀ).map (ptAt hw h) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ptAt_apply (z : w.adicCompletion E) :
    ptAt hw h z = GlobalTheory.AdelicU.Supp.singleTens E v ((InertChart.complEquiv hw h).symm z) := rfl

/- English proof (translation)
Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem locW_ptAt (z : w.adicCompletion E) : locW h (ptAt hw h z) = z := by
  change toCompl h (compFin F E v (GlobalTheory.AdelicU.Supp.singleTens E v ((InertChart.complEquiv hw h).symm z))) = z
  rw [GlobalTheory.AdelicU.Supp.compFin_singleTens_self]
  exact (InertChart.complEquiv hw h).apply_symm_apply z

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem at_ptAt (z : w.adicCompletion E) : At (evFin F v) (ptAt hw h z) :=
  GlobalTheory.ThK.at_evFin_iff.2 ⟨fun u => GlobalTheory.AdelicU.Supp.compInf_singleTens u v _,
    fun u hu => GlobalTheory.AdelicU.Supp.compFin_singleTens_ne hu _⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem ptAt_locW {z : AE F E} (hz : At (evFin F v) z) : ptAt hw h (locW h z) = z := by
  obtain ⟨h1, h2⟩ := GlobalTheory.ThK.at_evFin_iff.1 hz
  refine GlobalTheory.AdelicU.Supp.adTens_ext (fun u => ?_) fun u => ?_
  · rw [ptAt_apply, GlobalTheory.AdelicU.Supp.compInf_singleTens, h1 u]
  · by_cases e : u = v
    · subst e
      rw [ptAt_apply, GlobalTheory.AdelicU.Supp.compFin_singleTens_self]
      exact (InertChart.complEquiv hw h).symm_apply_apply _
    · rw [ptAt_apply, GlobalTheory.AdelicU.Supp.compFin_singleTens_ne e, h2 u e]

end GlobalTheory.InertCoord

namespace GlobalTheory.InertCoord

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : Pl F} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v)

/- English proof (translation)
Establish an intermediate fact. Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Express the relevant assertion in an equivalent form by its definition. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem cA_ptAt (σ : E →ₐ[F] E) {c : w.adicCompletion E →+* w.adicCompletion E} (hc : IsConjAt σ h c) (z : w.adicCompletion E) :
    cA σ (ptAt hw h z) = ptAt hw h (c z) := by
  have e1 : ∀ y : AE F E, cA σ y = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ y := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [e1, ptAt_apply, GlobalTheory.AdelicU.Supp.sigR_singleTens, ptAt_apply]
  congr 1
  apply (InertChart.complEquiv hw h).injective
  rw [RingEquiv.apply_symm_apply]
  have := hc ((InertChart.complEquiv hw h).symm z)
  change c (InertChart.complEquiv hw h ((InertChart.complEquiv hw h).symm z)) = _ at this
  rw [RingEquiv.apply_symm_apply] at this
  exact this.symm

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.
-/
theorem inclR_mul_ptAt (x : E) (z : w.adicCompletion E) :
    inclR (F := F) (AF F) x * ptAt hw h z = ptAt hw h (algebraMap E (w.adicCompletion E) x * z) := by
  rw [mul_comm, ptAt_apply, GlobalTheory.AdelicU.Supp.singleTens_mul, ptAt_apply]
  congr 1
  apply (InertChart.complEquiv hw h).injective
  rw [RingEquiv.apply_symm_apply, map_mul, RingEquiv.apply_symm_apply, mul_comm]
  congr 1
  change toCompl h (compFin F E v ((1 : AF F) ⊗ₜ[F] x)) = _
  rw [GlobalTheory.AdelicU.Supp.compFin_one_tmul, toCompl_tmul, map_one, one_mul]

end GlobalTheory.InertCoord

end
