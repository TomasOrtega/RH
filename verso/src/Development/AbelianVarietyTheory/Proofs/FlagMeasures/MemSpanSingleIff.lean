import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.Glue

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} in

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result.

Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Treat this case separately. Simplify to obtain the desired conclusion from the available facts. Treat this case separately. Simplify to obtain the desired conclusion from the available facts. Treat this case separately.

Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem _root_.GlobalTheory.HL.Glue.mem_span_single_iff {R : Type} [CommRing R] (O : Subring R) (n : ℕ)
    (v : Fin n → R) :
    v ∈ Submodule.span O (Set.range fun i => (Pi.single i 1 : Fin n → R)) ↔ ∀ i, v i ∈ O := by
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨j, rfl⟩ := hw
      intro i
      by_cases h : i = j
      · subst h; simp [O.one_mem]
      · simp [Pi.single_apply, h, O.zero_mem]
    | zero => intro i; simpa using O.zero_mem
    | add a b _ _ ha hb => intro i; simpa using O.add_mem (ha i) (hb i)
    | smul c a _ ha => intro i; simpa [Subring.smul_def] using O.mul_mem c.2 (ha i)
  · intro hv
    have hsum : v = ∑ i, (⟨v i, hv i⟩ : O) • (Pi.single i 1 : Fin n → R) := by
      ext j
      simp [Subring.smul_def, Finset.sum_apply, Pi.single_apply]
    rw [hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} in

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem _root_.GlobalTheory.HL.Glue.ιE_mem (A : _root_.GlobalTheory.HL.Places F E sig)
    (p : HeightOneSpectrum (𝓞 F)) (x : E) (hx : IsIntegral ℤ x) :
    (A.loc p).ιE x ∈ (A.L p).O := by
  rw [_root_.Formalism.MainNotions.S.Loc.LocE.O_def]
  exact (hx.map (A.loc p).ιE.toIntAlgHom).tower_top

end GlobalTheory.HL.Glue
