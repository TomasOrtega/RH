import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEqZpowMulUnit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthonormalBasisAndOneOrbit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEquivOfRetractions
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualLatticeUnipotentTranslateStandard
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermInvariantsIndependentOfWitnesses
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesComplementUnitaryActsOnTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBound
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGluingHomomorphismDefectGroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitEntries
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralOfMulVec
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HmUnit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalExtend
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsIntegralOfQuad
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.HL.StdPlace NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.FrameUnimod
open GlobalTheory.HL.Defect GlobalTheory.HL.Eichler GlobalTheory.HL.StdLat GlobalTheory.UnramOrder Matrix

/- English proof (translation)
Introduce `F _ _ _ _ _ E _ _ _ L r k S d Λ hT ha0`. Take `⟨hSD, hW, hM, -, -, -⟩` from `GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT`. Take `⟨-, -, ⟨c, hc0, hc⟩, -, -, hth0, -⟩` from `GlobalTheory.FrameBasic.main L r k S`. Take `⟨-, -, hv, hvu⟩` from `GlobalTheory.UnramVal.vE_valuation L S.ϖ S.ϖ_irr`. Establish `hn : (S.wit d Λ).1 ∈ S.N` using `hW.2.2.1`.

Establish `hn' : (S.wit d Λ).2 ∈ S.N'` using `hW.2.2.2.1`. Establish `hint : ∀ x ∈ Λ, ∀ y ∈ Λ, hf L S.Hm x y ∈ L.O` using `fun x hx y hy => (hSD.2 y).2 hy x hx`. Establish `hMe : S.M d Λ = Submodule.span L.O (Set.range (gens S (S.fr d Λ) (S.fr' d Λ)))` using `Mof_eq S _ _`. Establish `hg : ∀ i, gens S (S.fr d Λ) (S.fr' d Λ) i ∈ Λ` using `fun i => (hM (hMe ▸ Submodule.subset_span ⟨i, rfl⟩)).1`. Establish `hsp : ∀ j, S.spanTo (S.fr d Λ) j = S.spanTo S.f j`.

Take `⟨s, hs, h⟩` from `FrameOnto.exists_matrix S S.f S.T S.gram _ hn`. Conclude with `spanTo_eq S _ _ s hs h`. Establish `hsp' : ∀ j, S.spanTo (S.fr' d Λ) j = S.spanTo S.f' j`. Take `⟨s, hs, h⟩` from `FrameOnto.exists_matrix S S.f' S.T' S.gram' _ hn'`. Conclude with `spanTo_eq S _ _ s hs h`.

Establish `hdet : (Matrix.of fun i j => hf L S.Hm (gens S (S.fr d Λ) (S.fr' d Λ) i) (gens S (S.fr d Λ) (S.fr' d Λ) j)).det = algebraMap F E ((-1) ^ (r + 1) * S.th⁻¹ ^ (2 * (r + 1)) * c)`. Use `(det_gens S hn hn').trans ?_` and prove the remaining obligations. Rewrite using `[hc]`. Simplify using `only [map_mul, map_pow, map_neg, map_one]`. Establish `hc' : ((-1) ^ (r + 1) * S.th⁻¹ ^ (2 * (r + 1)) * c : F) ≠ 0`.

Simplify using `[hc0, hth0]`. Establish `hmem : ((-1) ^ (r + 1) * S.th⁻¹ ^ (2 * (r + 1)) * c : F) ∈ 𝒪[F]`. Rewrite using `[← algebraMap_mem_iff L, ← hdet]`. Conclude with `det_mem _ fun i j => hint _ (hg i) _ (hg j)`. Take `⟨w0, hw0⟩` from `hvu _ hc'`.

Take `⟨m, hm⟩` from `Int.eq_ofNat_of_zero_le ((hv _ hc').2 hmem)`. Rewrite `hw0` using `[hm, zpow_natCast]`. Establish `ha : S.a = m`. Establish `e1 : c = S.th ^ (2 * (r + 1)) * ((S.ϖ : F) ^ m * ((((-1) ^ (r + 1) * w0 : (𝒪[F])ˣ) : 𝒪[F]) : F))`. Establish `e2 : ((((-1) ^ (r + 1) * w0 : (𝒪[F])ˣ) : 𝒪[F]) : F) = (-1) ^ (r + 1) * ((w0 : 𝒪[F]) : F)`.

Simplify using the standard rewrite rules. Rewrite using `[e2, mul_left_comm ((S.ϖ : F) ^ m), ← hw0, ← mul_assoc ((-1 : F) ^ _), ← mul_assoc ((-1 : F) ^ _), ← mul_pow, inv_pow]`. Clear the denominators using the available nonvanishing facts. Simplify using the standard rewrite rules. Unfold `Frames.a Frames.vth`.

Unfold `Frames.th at e1`. Rewrite using `[hc, e1]`. Use `split_ifs`. Rewrite using `[← mul_assoc, ← pow_add, vE_pow_mul _ S.ϖ_irr]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[one_pow, one_mul, vE_pow_mul _ S.ϖ_irr]`. Expand and normalize the polynomial expressions, which then agree. Establish `hm0 : m = 0` using `by omega`. Rewrite `hw0` using `[hm0, pow_zero, one_mul]`.

Set `e : Fin (2 * (r + 1)) ≃ Fin (r + 1) ⊕ Fin (r + 1)` to `(finCongr (two_mul (r + 1))).trans finSumFinEquiv.symm`. Establish `hrange : Set.range (fun i => gens S (S.fr d Λ) (S.fr' d Λ) (e i)) = Set.range (gens S (S.fr d Λ) (S.fr' d Λ))` using `EquivLike.range_comp (gens S (S.fr d Λ) (S.fr' d Λ)) e`. Use `⟨fun i => gens S (S.fr d Λ) (S.fr' d Λ) (e i), ?_, ?_, fun i j => hint _ (hg _) _ (hg _), ?_⟩` and prove the remaining obligations. Rewrite using `[hrange, hMe]`. Rewrite using `[hrange]`.

Unfold `Frames.ME`. Rewrite using `[← hsp, ← hsp']`. Apply `le_antisymm` to reduce the goal to its premises. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨b | b, rfl⟩`.

Conclude with `Submodule.mem_sup_left (Submodule.subset_span ⟨b, b.2, rfl⟩)`. Simplify using `only [gens, Sum.elim_inr]`. Use `Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ ?_)` and prove the remaining obligations. Conclude with `Submodule.mem_sup_right (Submodule.subset_span ⟨b, b.2, rfl⟩)`. Conclude with `Submodule.mem_sup_left (Submodule.subset_span ⟨b, b.2, rfl⟩)`.

Establish `h1 : ∀ b, S.fr d Λ b ∈ Submodule.span E (Set.range (gens S (S.fr d Λ) (S.fr' d Λ)))` using `fun b => Submodule.subset_span ⟨Sum.inl b, rfl⟩`. Use `sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨b, -, rfl⟩`. Conclude with `h1 b`. Introduce and unpack `_ ⟨b, -, rfl⟩`.

Establish `h2 : S.fr' d Λ b = S.fr d Λ b + algebraMap F E S.th • gens S (S.fr d Λ) (S.fr' d Λ) (Sum.inr b)`. Simplify using `only [gens, Sum.elim_inr, smul_smul, ← map_mul, mul_inv_cancel₀ hth0, map_one, one_smul]`. Normalize the expressions using the abelian group laws. Rewrite using `[h2]`. Conclude with `Submodule.add_mem _ (h1 b) (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr b, rfl⟩))`.

Use `set Gm : Matrix (Fin (2 * (r + 1))) (Fin (2 * (r + 1))) E := Matrix.of fun i j => hf L S.Hm (gens S (S.fr d Λ) (S.fr' d Λ) (e i)) (gens S (S.fr d Λ) (S.fr' d Λ) (e j)) with hGm`. Establish `hGdet : Gm.det = algebraMap F E ((w0 : 𝒪[F]) : F)`. Establish `: Gm = (Matrix.of fun i j => hf L S.Hm (gens S (S.fr d Λ) (S.fr' d Λ) i) (gens S (S.fr d Λ) (S.fr' d Λ) j)).submatrix e e` using `rfl`. Rewrite using `[this, Matrix.det_submatrix_equiv_self, hdet, ← hw0]`. Establish `hA : ∀ i j, Gm i j ∈ L.O` using `fun i j => hint _ (hg _) _ (hg _)`.

Set `A : Matrix (Fin (2 * (r + 1))) (Fin (2 * (r + 1))) L.O` to `Matrix.of fun i j => ⟨Gm i j, hA i j⟩`. Establish `hAG : A.map L.O.subtype = Gm` using `rfl`. Establish `hadj : ∀ i j, Gm.adjugate i j ∈ L.O` using `fun i j => by`. Establish `h4 : A.adjugate.map L.O.subtype = Gm.adjugate`. Rewrite using `[← hAG]`.

Conclude with `RingHom.map_adjugate L.O.subtype A`. Rewrite using `[← h4]`. Conclude with `Subtype.property _`. Use `⟨algebraMap F E (((w0⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F) • Gm.adjugate, fun i j => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.smul_apply, smul_eq_mul]`.

Conclude with `L.O.mul_mem ((algebraMap_mem_iff L _).2 (w0⁻¹ : (𝒪[F])ˣ).1.2) (hadj i j)`. Rewrite using `[Matrix.mul_smul, Matrix.mul_adjugate, hGdet, smul_smul, ← map_mul]`. Establish `h8 : (((w0⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F) * ((w0 : 𝒪[F]) : F) = 1`. Rewrite using `[← Subring.coe_mul, Units.inv_mul]`. Simplify using the standard rewrite rules.

Rewrite using `[h8, map_one, one_smul]`.
-/
theorem frame_unimodular : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.a = 0 → ∃ u : Fin (2 * (r + 1)) → S.V, S.M d Λ = Submodule.span L.O (Set.range u) ∧ Submodule.span E (Set.range u) = S.ME ∧ (∀ i j, hf L S.Hm (u i) (u j) ∈ L.O) ∧ ∃ P : Matrix (Fin (2 * (r + 1))) (Fin (2 * (r + 1))) E, IsIntM L P ∧ (Matrix.of fun i j => hf L S.Hm (u i) (u j)) * P = 1 := by
  intro F _ _ _ _ _ E _ _ _ L r k S d Λ hT ha0
  obtain ⟨hSD, hW, hM, -, -, -⟩ := GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT
  obtain ⟨-, -, ⟨c, hc0, hc⟩, -, -, hth0, -⟩ := GlobalTheory.FrameBasic.main L r k S
  obtain ⟨-, -, hv, hvu⟩ := GlobalTheory.UnramVal.vE_valuation L S.ϖ S.ϖ_irr
  have hn : (S.wit d Λ).1 ∈ S.N := hW.2.2.1
  have hn' : (S.wit d Λ).2 ∈ S.N' := hW.2.2.2.1
  have hint : ∀ x ∈ Λ, ∀ y ∈ Λ, hf L S.Hm x y ∈ L.O := fun x hx y hy => (hSD.2 y).2 hy x hx
  have hMe : S.M d Λ = Submodule.span L.O (Set.range (gens S (S.fr d Λ) (S.fr' d Λ))) := Mof_eq S _ _
  have hg : ∀ i, gens S (S.fr d Λ) (S.fr' d Λ) i ∈ Λ := fun i =>
    (hM (hMe ▸ Submodule.subset_span ⟨i, rfl⟩)).1
  have hsp : ∀ j, S.spanTo (S.fr d Λ) j = S.spanTo S.f j := by
    obtain ⟨s, hs, h⟩ := FrameOnto.exists_matrix S S.f S.T S.gram _ hn
    exact spanTo_eq S _ _ s hs h
  have hsp' : ∀ j, S.spanTo (S.fr' d Λ) j = S.spanTo S.f' j := by
    obtain ⟨s, hs, h⟩ := FrameOnto.exists_matrix S S.f' S.T' S.gram' _ hn'
    exact spanTo_eq S _ _ s hs h
  have hdet : (Matrix.of fun i j => hf L S.Hm (gens S (S.fr d Λ) (S.fr' d Λ) i)
      (gens S (S.fr d Λ) (S.fr' d Λ) j)).det =
      algebraMap F E ((-1) ^ (r + 1) * S.th⁻¹ ^ (2 * (r + 1)) * c) := by
    refine (det_gens S hn hn').trans ?_
    rw [hc]; simp only [map_mul, map_pow, map_neg, map_one]
  have hc' : ((-1) ^ (r + 1) * S.th⁻¹ ^ (2 * (r + 1)) * c : F) ≠ 0 := by
    simp [hc0, hth0]
  have hmem : ((-1) ^ (r + 1) * S.th⁻¹ ^ (2 * (r + 1)) * c : F) ∈ 𝒪[F] := by
    rw [← algebraMap_mem_iff L, ← hdet]
    exact det_mem _ fun i j => hint _ (hg i) _ (hg j)
  obtain ⟨w0, hw0⟩ := hvu _ hc'
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le ((hv _ hc').2 hmem)
  rw [hm, zpow_natCast] at hw0
  have ha : S.a = m := by
    have e1 : c = S.th ^ (2 * (r + 1)) * ((S.ϖ : F) ^ m *
        ((((-1) ^ (r + 1) * w0 : (𝒪[F])ˣ) : 𝒪[F]) : F)) := by
      have e2 : ((((-1) ^ (r + 1) * w0 : (𝒪[F])ˣ) : 𝒪[F]) : F) = (-1) ^ (r + 1) * ((w0 : 𝒪[F]) : F) := by
        simp
      rw [e2, mul_left_comm ((S.ϖ : F) ^ m), ← hw0, ← mul_assoc ((-1 : F) ^ _), ← mul_assoc ((-1 : F) ^ _),
        ← mul_pow, inv_pow]
      field_simp
      simp
    unfold Frames.a Frames.vth
    unfold Frames.th at e1
    rw [hc, e1]
    split_ifs
    · rw [← mul_assoc, ← pow_add, vE_pow_mul _ S.ϖ_irr]; push_cast; ring
    · rw [one_pow, one_mul, vE_pow_mul _ S.ϖ_irr]; ring
  have hm0 : m = 0 := by omega
  rw [hm0, pow_zero, one_mul] at hw0
  let e : Fin (2 * (r + 1)) ≃ Fin (r + 1) ⊕ Fin (r + 1) :=
    (finCongr (two_mul (r + 1))).trans finSumFinEquiv.symm
  have hrange : Set.range (fun i => gens S (S.fr d Λ) (S.fr' d Λ) (e i)) =
      Set.range (gens S (S.fr d Λ) (S.fr' d Λ)) :=
    EquivLike.range_comp (gens S (S.fr d Λ) (S.fr' d Λ)) e
  refine ⟨fun i => gens S (S.fr d Λ) (S.fr' d Λ) (e i), ?_, ?_, fun i j => hint _ (hg _) _ (hg _), ?_⟩
  · rw [hrange, hMe]
  · rw [hrange]
    unfold Frames.ME
    rw [← hsp, ← hsp']
    apply le_antisymm
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨b | b, rfl⟩
      · exact Submodule.mem_sup_left (Submodule.subset_span ⟨b, b.2, rfl⟩)
      · simp only [gens, Sum.elim_inr]
        refine Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ ?_)
        · exact Submodule.mem_sup_right (Submodule.subset_span ⟨b, b.2, rfl⟩)
        · exact Submodule.mem_sup_left (Submodule.subset_span ⟨b, b.2, rfl⟩)
    · have h1 : ∀ b, S.fr d Λ b ∈ Submodule.span E (Set.range (gens S (S.fr d Λ) (S.fr' d Λ))) :=
        fun b => Submodule.subset_span ⟨Sum.inl b, rfl⟩
      refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
      · rintro _ ⟨b, -, rfl⟩
        exact h1 b
      · rintro _ ⟨b, -, rfl⟩
        have h2 : S.fr' d Λ b = S.fr d Λ b +
            algebraMap F E S.th • gens S (S.fr d Λ) (S.fr' d Λ) (Sum.inr b) := by
          simp only [gens, Sum.elim_inr, smul_smul, ← map_mul, mul_inv_cancel₀ hth0, map_one, one_smul]
          abel
        rw [h2]
        exact Submodule.add_mem _ (h1 b)
          (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr b, rfl⟩))
  · set Gm : Matrix (Fin (2 * (r + 1))) (Fin (2 * (r + 1))) E :=
      Matrix.of fun i j => hf L S.Hm (gens S (S.fr d Λ) (S.fr' d Λ) (e i))
        (gens S (S.fr d Λ) (S.fr' d Λ) (e j)) with hGm
    have hGdet : Gm.det = algebraMap F E ((w0 : 𝒪[F]) : F) := by
      have : Gm = (Matrix.of fun i j => hf L S.Hm (gens S (S.fr d Λ) (S.fr' d Λ) i)
          (gens S (S.fr d Λ) (S.fr' d Λ) j)).submatrix e e := rfl
      rw [this, Matrix.det_submatrix_equiv_self, hdet, ← hw0]
    have hA : ∀ i j, Gm i j ∈ L.O := fun i j => hint _ (hg _) _ (hg _)
    let A : Matrix (Fin (2 * (r + 1))) (Fin (2 * (r + 1))) L.O := Matrix.of fun i j => ⟨Gm i j, hA i j⟩
    have hAG : A.map L.O.subtype = Gm := rfl
    have hadj : ∀ i j, Gm.adjugate i j ∈ L.O := fun i j => by
      have h4 : A.adjugate.map L.O.subtype = Gm.adjugate := by
        rw [← hAG]; exact RingHom.map_adjugate L.O.subtype A
      rw [← h4]
      exact Subtype.property _
    refine ⟨algebraMap F E (((w0⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F) • Gm.adjugate, fun i j => ?_, ?_⟩
    · rw [Matrix.smul_apply, smul_eq_mul]
      exact L.O.mul_mem ((algebraMap_mem_iff L _).2 (w0⁻¹ : (𝒪[F])ˣ).1.2) (hadj i j)
    · rw [Matrix.mul_smul, Matrix.mul_adjugate, hGdet, smul_smul, ← map_mul]
      have h8 : (((w0⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F) * ((w0 : 𝒪[F]) : F) = 1 := by
        rw [← Subring.coe_mul, Units.inv_mul]; simp
      rw [h8, map_one, one_smul]

end GlobalTheory.HL.FrameUnimod
