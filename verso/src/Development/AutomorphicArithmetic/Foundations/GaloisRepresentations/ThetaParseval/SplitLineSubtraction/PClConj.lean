import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.SubtractOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankDdREqOfEquiv
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WdConjAbove
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

/- English proof (translation)
Set `s : Set (Qbar l)` to `Set.range (fun p : Fin n × Fin n => (A : Matrix (Fin n) (Fin n) (Qbar l)) p.1 p.2) ∪ Set.range (fun p : Fin n × Fin n => ((A⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) p.1 p.2)`. Establish `hs : s.Finite` using `(Set.finite_range _).union (Set.finite_range _)`. Use `haveI : Finite s := hs.to_subtype`. Use `⟨⟨IntermediateField.adjoin ℚ_[l] s, IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x⟩, fun i j => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Conclude with `IntermediateField.subset_adjoin _ _ (Or.inl ⟨(i, j), rfl⟩)`.

Conclude with `IntermediateField.subset_adjoin _ _ (Or.inr ⟨(i, j), rfl⟩)`.
-/
private theorem exists_finExt_gl {l n : ℕ} [Fact l.Prime] (A : GL (Fin n) (Qbar l)) :
    ∃ K : FinExt l, ∀ i j, (A : Matrix (Fin n) (Fin n) (Qbar l)) i j ∈ K.1 ∧
      ((A⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) i j ∈ K.1 := by
  let s : Set (Qbar l) := Set.range (fun p : Fin n × Fin n => (A : Matrix (Fin n) (Fin n) (Qbar l)) p.1 p.2) ∪
    Set.range (fun p : Fin n × Fin n => ((A⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) p.1 p.2)
  have hs : s.Finite := (Set.finite_range _).union (Set.finite_range _)
  haveI : Finite s := hs.to_subtype
  refine ⟨⟨IntermediateField.adjoin ℚ_[l] s,
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x⟩, fun i j => ⟨?_, ?_⟩⟩
  · exact IntermediateField.subset_adjoin _ _ (Or.inl ⟨(i, j), rfl⟩)
  · exact IntermediateField.subset_adjoin _ _ (Or.inr ⟨(i, j), rfl⟩)

/- English proof (translation)
Take `⟨LL', r₀, hm, hc⟩` from `hr`. Take `⟨h, M, hM⟩` from `GlobalTheory.ConjCrys.exists_conj_model A K hA hm`. Take `⟨-, hdR2, -, -⟩` from `GlobalTheory.Pst.local_ext P Bw h r₀`. Conclude with `⟨_, _, hM, (GlobalTheory.ConjCrys.local_conj P Bw _ M _).2.1 (hdR2.2 hc)⟩`.
-/
private theorem isdRAt_conj {l : ℕ} [Fact l.Prime] {P : LocPrime l} {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
    {Bw : LocBridge l E Ω Gw O} {m : ℕ} {r : ↥Gw →* GL (Fin m) (Qbar l)} (A : GL (Fin m) (Qbar l)) (K : FinExt l)
    (hA : ∀ i j, (A : Matrix (Fin m) (Fin m) (Qbar l)) i j ∈ K.1 ∧
      ((A⁻¹ : GL (Fin m) (Qbar l)) : Matrix (Fin m) (Fin m) (Qbar l)) i j ∈ K.1)
    (hr : IsdRAt P Bw r) : IsdRAt P Bw ((MulAut.conj A⁻¹).toMonoidHom.comp r) := by
  obtain ⟨LL', r₀, hm, hc⟩ := hr
  obtain ⟨h, M, hM⟩ := GlobalTheory.ConjCrys.exists_conj_model A K hA hm
  obtain ⟨-, hdR2, -, -⟩ := GlobalTheory.Pst.local_ext P Bw h r₀
  exact ⟨_, _, hM, (GlobalTheory.ConjCrys.local_conj P Bw _ M _).2.1 (hdR2.2 hc)⟩

/- English proof (translation)
Introduce `hCp hCont hPst E Ω _ _ _ _ _ l _ ι a r r' hr hiso w S J hcl`. Take `⟨g, hg⟩` from `id hiso`. Take `⟨h1, h2⟩` from `hcl`. Use `⟨fun hl A hA => ?_, ?_⟩` and prove the remaining obligations. Take `⟨i1, i2⟩` from `h1 hl A hA`.

Use `⟨fun s hs => ?_, fun σ hσ => ?_⟩` and prove the remaining obligations. Rewrite using `[hg, i1 s hs]`. Simplify using the standard rewrite rules. Establish `e : (r' σ⁻¹ : Matrix (Fin a) (Fin a) (Qbar l)).charpoly = (r σ⁻¹ : Matrix (Fin a) (Fin a) (Qbar l)).charpoly` using `(hCp (G E Ω) (Qbar l) a a).2.2 r r' hiso σ⁻¹`. Rewrite using `[e]`.

Conclude with `i2 σ hσ`. Introduce `P AI hT A h O _ _ _ Bw hj`. Take `⟨c1, c2, c3, c4⟩` from `h2 P AI hT A h O Bw hj`. Take `⟨K, hK⟩` from `exists_finExt_gl (g⁻¹)`. Establish `e : r'.comp (Dec (F` using `E) A).subtype = (MulAut.conj (g⁻¹)⁻¹).toMonoidHom.comp (r.comp (Dec (F := E) A).subtype) := by ext1 x`.

Simplify using `[hg, MulAut.conj_apply]`. Establish `hc' : Continuous r'` using `(hCont (G E Ω) (Qbar l) a a).2.1 r r' hiso hr`. Establish `cρ : Continuous (r.comp (Dec (F` using `E) A).subtype) := hr.comp continuous_subtype_val`. Establish `cρ' : Continuous (r'.comp (Dec (F` using `E) A).subtype) := hc'.comp continuous_subtype_val`. Establish `d' : IsdRAt P Bw (r'.comp (Dec (F` using `E) A).subtype) := by`.

Rewrite using `[e]`. Conclude with `isdRAt_conj _ K hK c2`. Use `⟨?_, d', fun τ LL' τ' hI => ?_, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[e]`. Conclude with `GlobalTheory.ConjCrys.isCrysAt_conj _ K hK c1`.

Rewrite using `[e]`. Conclude with `GlobalTheory.ConjCrys.isJumpsAt_conj _ K hK (c3 τ LL' τ' hI)`. Rewrite using `[GlobalTheory.ConjGal.wdAt_conj P ι Bw h hj (r.comp (Dec (F := E) A).subtype) (r'.comp (Dec (F := E) A).subtype) g (fun x => hg x) (hPst l P AI hT E Ω A O Bw a _ cρ c2) (hPst l P AI hT E Ω A O Bw a _ cρ' d')]`. Conclude with `c4 x`.
-/
theorem UpperTheory.Gal.TP.Sub.clConj_holds :
    CpFacts → ContLeft → PstOfDR → ClConj := by
  intro hCp hCont hPst E Ω _ _ _ _ _ l _ ι a r r' hr hiso w S J hcl
  obtain ⟨g, hg⟩ := id hiso
  obtain ⟨h1, h2⟩ := hcl
  refine ⟨fun hl A hA => ?_, ?_⟩
  · obtain ⟨i1, i2⟩ := h1 hl A hA
    refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
    · rw [hg, i1 s hs]
      simp
    · have e : (r' σ⁻¹ : Matrix (Fin a) (Fin a) (Qbar l)).charpoly =
          (r σ⁻¹ : Matrix (Fin a) (Fin a) (Qbar l)).charpoly :=
        (hCp (G E Ω) (Qbar l) a a).2.2 r r' hiso σ⁻¹
      rw [e]
      exact i2 σ hσ
  · intro P AI hT A h O _ _ _ Bw hj
    obtain ⟨c1, c2, c3, c4⟩ := h2 P AI hT A h O Bw hj
    obtain ⟨K, hK⟩ := exists_finExt_gl (g⁻¹)
    have e : r'.comp (Dec (F := E) A).subtype =
        (MulAut.conj (g⁻¹)⁻¹).toMonoidHom.comp (r.comp (Dec (F := E) A).subtype) := by
      ext1 x
      simp [hg, MulAut.conj_apply]
    have hc' : Continuous r' := (hCont (G E Ω) (Qbar l) a a).2.1 r r' hiso hr
    have cρ : Continuous (r.comp (Dec (F := E) A).subtype) := hr.comp continuous_subtype_val
    have cρ' : Continuous (r'.comp (Dec (F := E) A).subtype) := hc'.comp continuous_subtype_val
    have d' : IsdRAt P Bw (r'.comp (Dec (F := E) A).subtype) := by
      rw [e]
      exact isdRAt_conj _ K hK c2
    refine ⟨?_, d', fun τ LL' τ' hI => ?_, fun x => ?_⟩
    · rw [e]
      exact GlobalTheory.ConjCrys.isCrysAt_conj _ K hK c1
    · rw [e]
      exact GlobalTheory.ConjCrys.isJumpsAt_conj _ K hK (c3 τ LL' τ' hI)
    · rw [GlobalTheory.ConjGal.wdAt_conj P ι Bw h hj (r.comp (Dec (F := E) A).subtype)
        (r'.comp (Dec (F := E) A).subtype) g (fun x => hg x)
        (hPst l P AI hT E Ω A O Bw a _ cρ c2) (hPst l P AI hT E Ω A O Bw a _ cρ' d')]
      exact c4 x
