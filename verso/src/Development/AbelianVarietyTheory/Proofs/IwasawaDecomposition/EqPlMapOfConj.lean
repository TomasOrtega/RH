import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DatVtEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOrIsConjPlaceOfOverSplitPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimitiveHeckeLFunctionInvOfTrivialOnMaxReal
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MtIn.GenOff

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mem_iff_of_conj (D : D7) (s : ReciprocityTheory.Aut.SplitPlace D.host.E) {v : PlE D.host}
    (hc : Formalism.BasicNotions.IsConjPl D.host v s.w) (a : 𝓞 (maximalRealSubfield D.host.E)) :
    algebraMap _ (𝓞 D.host.E) a ∈ v.asIdeal ↔ a ∈ s.v.asIdeal := by
  rw [hc (algebraMap _ (𝓞 D.host.E) a) (algebraMap _ (𝓞 D.host.E) a) ?_, ← Ideal.mem_comap, s.w_under]
  rw [GlobalTheory.SplitPlaceOver.host_conj_eq']
  exact (IsCMField.complexConj_apply_eq_self D.host.E (a : maximalRealSubfield D.host.E)).symm

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem eq_of_conj (D : D7) {w v u : PlE D.host} (hw : Formalism.BasicNotions.IsConjPl D.host w u) (hv : Formalism.BasicNotions.IsConjPl D.host v u) :
    w = v := by
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  have hy : ((IsCMField.ringOfIntegersComplexConj D.host.E x : 𝓞 D.host.E) : D.host.E) = D.host.conj (x : D.host.E) := by
    rw [IsCMField.coe_ringOfIntegersComplexConj, GlobalTheory.SplitPlaceOver.host_conj_eq']
  exact (hw x _ hy).trans (hv x _ hy).symm

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem eq_plMap_of_conj (D : D7) {v u : PlE D.host} (hc : Formalism.BasicNotions.IsConjPl D.host v u) :
    u = Formalism.L2.Host.CT.plMap GlobalTheory.CMVal.InvConj.conjE v := by
  refine HeightOneSpectrum.ext (Ideal.ext fun z => ?_)
  set x := IsCMField.ringOfIntegersComplexConj D.host.E z
  have hz : z = RingOfIntegers.mapRingEquiv GlobalTheory.CMVal.InvConj.conjE x := by
    apply RingOfIntegers.ext
    show (z : D.host.E) = IsCMField.complexConj D.host.E (x : D.host.E)
    rw [IsCMField.coe_ringOfIntegersComplexConj, IsCMField.complexConj_apply_apply]
  have hy : (z : D.host.E) = D.host.conj (x : D.host.E) := by
    rw [GlobalTheory.SplitPlaceOver.host_conj_eq', IsCMField.coe_ringOfIntegersComplexConj, IsCMField.complexConj_apply_apply]
  rw [← (hc x z hy), hz, Formalism.L2.Host.CT.mem_plMap]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Reduce the conclusion to the remaining proof obligations. Prove the first alternative. Prove the second alternative. Establish an intermediate fact. Assume the hypotheses and unpack their components.

Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations. Separate the alternatives or extract the components of the hypothesis.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem gen_off_level : ∀ (D : D7) (cf : CharFrame D) (l : ℕ) (Q : Finset (PlE D.host)) (ψ : HChar D.host.E), (∀ v, v ∉ Q → ψ.UnrAt v) → ψ.TrivOn D.host.F → ∀ (j : Fin D.R.m) (v : PlE D.host) (k : ℕ) (s : ReciprocityTheory.Aut.SplitPlace D.host.E), GenAt D l Q v k → Formalism.BasicNotions.IsConjPl D.host v s.w → s.v ∉ gPl D ∪ qPl D (cf.mu0 j * ((if l = D.host.pde then cf.del' else cf.del) * ψ)) ∧ ¬ s.Above l := by
  intro D cf l Q ψ hψ hT j v k s hg hc
  obtain ⟨-, hvl, hvS, hvQ, -, -⟩ := hg
  have hvn : ∀ n : ℕ, ((n : ℕ) : 𝓞 (maximalRealSubfield D.host.E)) ∈ s.v.asIdeal → ((n : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal :=
    fun n h => by
      have := (mem_iff_of_conj D s hc (n : 𝓞 (maximalRealSubfield D.host.E))).2 h
      rwa [map_natCast] at this
  have hoff : ∀ w : PlE D.host, NG.OverPl w s.v → ∀ n : ℕ, ((n : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal →
      ((n : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal := fun w hw n h =>
    hvn n (by rw [← hw, Ideal.mem_comap, map_natCast]; exact h)
  have hg' : ∀ w : PlE D.host, NG.OverPl w s.v → ∀ k : Fin 2, w ∉ placesOver D.host.E (D.host.g k) := by
    intro w hw k hk
    have h := hoff w hw _ hk
    apply hvS
    refine ⟨?_, hvl⟩
    fin_cases k
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have hgPl : s.v ∉ gPl D := by
    rintro ⟨w, hw, k, hk⟩
    exact hg' w hw k hk
  refine ⟨?_, fun hl => hvl (hvn l hl)⟩
  rintro (h | ⟨-, w, hw, hu⟩)
  · exact hgPl h
  apply hu
  refine HChar.UnrAt.mul ((cf.isMu0 j).unr w fun k hk => hg' w hw k hk) (HChar.UnrAt.mul ?_ ?_)
  · split_ifs with hlp
    · exact cf.isDel'.unr w fun hp => hvS ⟨Or.inr (Or.inr (by rw [if_pos hlp]; exact hoff w hw _ hp)), hvl⟩
    · exact cf.isDel.unr w fun hp => hvS ⟨Or.inr (Or.inr (by rw [if_neg hlp]; exact hoff w hw _ hp)), hvl⟩
  · rcases GlobalTheory.SplitPlaceOver.eq_or_isConjPl D s w hw with e | e
    · rw [← e, eq_plMap_of_conj D hc]
      exact (GlobalTheory.CMVal.InvConj.unrAt_inv_iff ψ hT v).1 (HChar.UnrAt.inv (hψ v hvQ))
    · rw [eq_of_conj D e hc]
      exact hψ v hvQ

end GlobalTheory.MtIn.GenOff
