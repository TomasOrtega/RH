import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrConjApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealTrivialPointFiniteAdelicHomEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameConjStandardUnitaryMemUnitaryFiniteAdelicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameConjStandardRationalMemUnitaryRationalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameConjugatePrincipalCongruenceMemLatticeCongrStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStandardUnitaryFrameConjEqStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount

namespace GlobalTheory.FrameTransport

open GlobalTheory.FrameTransport in

/- English proof (translation)
Take `⟨uf, huf_def⟩ : ∃ uf, uf = finG V u` from `⟨_, rfl⟩`. Rewrite `hu` using `[← huf_def]`. Establish `hufU : uf ∈ UA D.sp.cm V.gram` using `by rw [huf_def]; exact GlobalTheory.LevSplit.finE_mem_UA V u.1`. Establish `lift : ∀ h : StandardLatticesGL3.GA D V.rank, ∃ g : GfC V, finG V g = frConj fr h.1 * uf⁻¹` using `fun h => GlobalTheory.T.exists_realTrivial_point_finiteAdelicHom_eq V _ (mul_mem (GlobalTheory.T.frameConj_standardUnitary_mem_unitaryFiniteAdelic V fr hfr h) (inv_mem hufU))`. Use `choose φ hφ using lift`.

Establish `hC : ∀ c ∈ GlobalTheory.FunObj.StdDatum.congLev D 𝔪 V.rank, uf * frConj fr c.1 * uf⁻¹ ∈ K`. Set `ρ : StandardLatticesGL3.GA D V.rank →* GL (Fin V.rank) (Lev.EAf D)` to `(MulAut.conj uf).toMonoidHom.comp ((frConj fr).comp (StandardLatticesGL3.GA D V.rank).subtype)`. Establish `hle : GlobalTheory.FunObj.StdDatum.congLev D 𝔪 V.rank ≤ K.comap ρ`. Use `(Subgroup.closure_le _).2 fun k hk => ?_` and prove the remaining obligations. Establish `hU : uf * frConj fr k.1 * uf⁻¹ ∈ UA D.sp.cm V.gram` using `mul_mem (mul_mem hufU (GlobalTheory.T.frameConj_standardUnitary_mem_unitaryFiniteAdelic V fr hfr k)) (inv_mem hufU)`.

Conclude with `hK (GlobalTheory.T.frameConjugate_principalCongruence_mem_latticeCongruence V fr uf Λ hu 𝔪 k hk.1 hk.2 hU)`. Introduce `c hc`. Conclude with `hle hc`. Use `⟨fun q => DoubleCoset.mk (ratFin V) (K.comap (finG V)) (φ (Quotient.out q)), ?_⟩` and prove the remaining obligations. Introduce `p`.

Take `⟨x, rfl⟩ : ∃ x, DoubleCoset.mk (ratFin V) (K.comap (finG V)) x = p` from `⟨Quotient.out p, DoubleCoset.out_eq' _ _ p⟩`. Take `⟨h, hh⟩` from `GlobalTheory.T.exists_standardUnitary_frameConj_eq V fr hfr (finG V x * uf) (mul_mem (GlobalTheory.LevSplit.finE_mem_UA V x.1) hufU)`. Use `⟨DoubleCoset.mk (GlobalTheory.NormSum.ratG D V.rank) (GlobalTheory.FunObj.StdDatum.congLev D 𝔪 V.rank) h, ?_⟩` and prove the remaining obligations. Use `show DoubleCoset.mk (ratFin V) (K.comap (finG V)) (φ (Quotient.out (DoubleCoset.mk (GlobalTheory.NormSum.ratG D V.rank) (GlobalTheory.FunObj.StdDatum.congLev D 𝔪 V.rank) h))) = _`. Take `⟨γ, hγ, c, hc, e⟩` from `(DoubleCoset.eq _ _ _ _).1 (DoubleCoset.out_eq' (GlobalTheory.NormSum.ratG D V.rank) (GlobalTheory.FunObj.StdDatum.congLev D 𝔪 V.rank) (DoubleCoset.mk (GlobalTheory.NormSum.ratG D V.rank) (GlobalTheory.FunObj.StdDatum.congLev D 𝔪 V.rank) h))`.

Generalize the expression as in `Quotient.out (DoubleCoset.mk (GlobalTheory.NormSum.ratG D V.rank) (GlobalTheory.FunObj.StdDatum.congLev D 𝔪 V.rank) h) = h' at e ⊢`. Take `⟨q, hq, hqe⟩` from `GlobalTheory.T.frameConj_standardRational_mem_unitaryRational V fr hfr γ hγ`. Take `⟨k, hk⟩` from `GlobalTheory.T.exists_realTrivial_point_finiteAdelicHom_eq V (uf * frConj fr c.1 * uf⁻¹) (mul_mem (mul_mem hufU (GlobalTheory.T.frameConj_standardUnitary_mem_unitaryFiniteAdelic V fr hfr c)) (inv_mem hufU))`. Use `(DoubleCoset.eq _ _ _ _).2 ⟨q, hq, k, ?_, ?_⟩` and prove the remaining obligations. Use `show finG V k ∈ K`.

Rewrite using `[hk]`. Conclude with `hC c hc`. Apply `finG_injective V` to reduce the goal to its premises. Establish `e1 : finG V x = frConj fr h.1 * uf⁻¹` using `by rw [hh]; group`. Establish `e2 : frConj fr h.1 = frConj fr γ.1 * frConj fr h'.1 * frConj fr c.1`.

Rewrite using `[e]`. Simplify using `only [Subgroup.coe_mul, map_mul]`. Establish `e3` using `hφ h'`. Simplify using `only [map_mul, hqe, e3, hk, e1, e2]`. Use `group`.
-/
theorem exists_surj_cls {D : D7} (V : HSp D) (fr : GL (Fin V.rank) D.host.E)
    (hfr : Formalism.UG.cT (↑D.sp.cm.sig) (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram *
      (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = 1)
    (u : GfC V) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hu : ∀ v, v ∈ Formalism.L2.Herm.hatL (colLat fr) ↔ (finG V u).val *ᵥ v ∈ Formalism.L2.Herm.hatL Λ)
    (𝔪 : Ideal (𝓞 D.host.E)) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D)))
    (hK : congLev D.sp.cm V.gram Λ 𝔪 ≤ K) :
    ∃ f : GlobalTheory.NormSum.Cls D V.rank (GlobalTheory.FunObj.StdDatum.congLev D 𝔪 V.rank) → FinCl V K, Function.Surjective f := by
  classical
  obtain ⟨uf, huf_def⟩ : ∃ uf, uf = finG V u := ⟨_, rfl⟩
  rw [← huf_def] at hu
  have hufU : uf ∈ UA D.sp.cm V.gram := by rw [huf_def]; exact GlobalTheory.LevSplit.finE_mem_UA V u.1
  have lift : ∀ h : StandardLatticesGL3.GA D V.rank, ∃ g : GfC V, finG V g = frConj fr h.1 * uf⁻¹ := fun h =>
    GlobalTheory.T.exists_realTrivial_point_finiteAdelicHom_eq V _ (mul_mem (GlobalTheory.T.frameConj_standardUnitary_mem_unitaryFiniteAdelic V fr hfr h) (inv_mem hufU))
  choose φ hφ using lift

  have hC : ∀ c ∈ GlobalTheory.FunObj.StdDatum.congLev D 𝔪 V.rank, uf * frConj fr c.1 * uf⁻¹ ∈ K := by
    let ρ : StandardLatticesGL3.GA D V.rank →* GL (Fin V.rank) (Lev.EAf D) :=
      (MulAut.conj uf).toMonoidHom.comp ((frConj fr).comp (StandardLatticesGL3.GA D V.rank).subtype)
    have hle : GlobalTheory.FunObj.StdDatum.congLev D 𝔪 V.rank ≤ K.comap ρ := by
      refine (Subgroup.closure_le _).2 fun k hk => ?_
      have hU : uf * frConj fr k.1 * uf⁻¹ ∈ UA D.sp.cm V.gram :=
        mul_mem (mul_mem hufU (GlobalTheory.T.frameConj_standardUnitary_mem_unitaryFiniteAdelic V fr hfr k)) (inv_mem hufU)
      exact hK (GlobalTheory.T.frameConjugate_principalCongruence_mem_latticeCongruence V fr uf Λ hu 𝔪 k hk.1 hk.2 hU)
    intro c hc
    exact hle hc
  refine ⟨fun q => DoubleCoset.mk (ratFin V) (K.comap (finG V)) (φ (Quotient.out q)), ?_⟩
  intro p
  obtain ⟨x, rfl⟩ : ∃ x, DoubleCoset.mk (ratFin V) (K.comap (finG V)) x = p := ⟨Quotient.out p, DoubleCoset.out_eq' _ _ p⟩
  obtain ⟨h, hh⟩ := GlobalTheory.T.exists_standardUnitary_frameConj_eq V fr hfr (finG V x * uf) (mul_mem (GlobalTheory.LevSplit.finE_mem_UA V x.1) hufU)
  refine ⟨DoubleCoset.mk (GlobalTheory.NormSum.ratG D V.rank) (GlobalTheory.FunObj.StdDatum.congLev D 𝔪 V.rank) h, ?_⟩
  show DoubleCoset.mk (ratFin V) (K.comap (finG V)) (φ (Quotient.out (DoubleCoset.mk (GlobalTheory.NormSum.ratG D V.rank) (GlobalTheory.FunObj.StdDatum.congLev D 𝔪 V.rank) h))) = _
  obtain ⟨γ, hγ, c, hc, e⟩ := (DoubleCoset.eq _ _ _ _).1
    (DoubleCoset.out_eq' (GlobalTheory.NormSum.ratG D V.rank) (GlobalTheory.FunObj.StdDatum.congLev D 𝔪 V.rank)
      (DoubleCoset.mk (GlobalTheory.NormSum.ratG D V.rank) (GlobalTheory.FunObj.StdDatum.congLev D 𝔪 V.rank) h))
  generalize Quotient.out (DoubleCoset.mk (GlobalTheory.NormSum.ratG D V.rank) (GlobalTheory.FunObj.StdDatum.congLev D 𝔪 V.rank) h) = h' at e ⊢
  obtain ⟨q, hq, hqe⟩ := GlobalTheory.T.frameConj_standardRational_mem_unitaryRational V fr hfr γ hγ
  obtain ⟨k, hk⟩ := GlobalTheory.T.exists_realTrivial_point_finiteAdelicHom_eq V (uf * frConj fr c.1 * uf⁻¹)
    (mul_mem (mul_mem hufU (GlobalTheory.T.frameConj_standardUnitary_mem_unitaryFiniteAdelic V fr hfr c)) (inv_mem hufU))
  refine (DoubleCoset.eq _ _ _ _).2 ⟨q, hq, k, ?_, ?_⟩
  · show finG V k ∈ K
    rw [hk]; exact hC c hc
  · apply finG_injective V
    have e1 : finG V x = frConj fr h.1 * uf⁻¹ := by rw [hh]; group
    have e2 : frConj fr h.1 = frConj fr γ.1 * frConj fr h'.1 * frConj fr c.1 := by
      rw [e]; simp only [Subgroup.coe_mul, map_mul]
    have e3 := hφ h'
    simp only [map_mul, hqe, e3, hk, e1, e2]
    group

/- English proof (translation)
Introduce `D T L sc G U hS X hX 𝔪 h𝔪 K hK`. Take `⟨f, hf⟩` from `exists_surj_cls (G.V X) (hS.fr X) (hS.fr_on X hX) (hS.u X) (G.Λ X) (hS.u_lat X hX) 𝔪 K hK`. Take `⟨-, hI, hJ⟩` from `GlobalTheory.NormSum.cls_finite_card_le D (G.V X).rank`. Take `⟨hne, hle⟩` from `GlobalTheory.congLev_relIndex_le D 𝔪 h𝔪 (G.V X).rank`. Take `⟨hfin, hcard⟩` from `hJ _ (GlobalTheory.FunObj.StdDatum.congLev_le 𝔪 _) hne`.

Establish `h1` using `Nat.card_le_card_of_surjective f hf`. Establish `hI' : (Nat.card (GlobalTheory.NormSum.Cls D (G.V X).rank (GlobalTheory.NormSum.intG D (G.V X).rank)) : ℝ) ≤ hBd D (G.V X).rank` using `hI`. Combine the equalities or inequalities in the displayed calculation. Conclude with `h1` after adjusting the coercions. Use `_ ≤ (Nat.card (GlobalTheory.NormSum.Cls D (G.V X).rank (GlobalTheory.NormSum.intG D (G.V X).rank)) : ℝ) * ((GlobalTheory.FunObj.StdDatum.congLev D 𝔪 (G.V X).rank).relIndex (GlobalTheory.NormSum.intG D (G.V X).rank) : ℝ) := by`.

Conclude with `hcard` after adjusting the coercions. Use `_ ≤ hBd D (G.V X).rank * (Ideal.absNorm 𝔪 : ℝ) ^ ((G.V X).rank ^ 2) := by`. Apply `mul_le_mul hI' (by exact_mod_cast hle) (by positivity)` to reduce the goal to its premises. Conclude with `le_trans (Nat.cast_nonneg _) hI'`.
-/
theorem finCl_card_le : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {U : Set T}, Std G U → ∀ X : Node, DefNode D.R.m X → ∀ 𝔪 : Ideal (𝓞 D.host.E), 𝔪 ≠ ⊥ → ∀ K : Subgroup (GL (Fin (G.V X).rank) (Lev.EAf D)), congLev D.sp.cm (G.V X).gram (G.Λ X) 𝔪 ≤ K → (Nat.card (FinCl (G.V X) K) : ℝ) ≤ hBd D (G.V X).rank * (Ideal.absNorm 𝔪 : ℝ) ^ ((G.V X).rank ^ 2) := by
  intro D T L sc G U hS X hX 𝔪 h𝔪 K hK
  obtain ⟨f, hf⟩ := exists_surj_cls (G.V X) (hS.fr X) (hS.fr_on X hX) (hS.u X) (G.Λ X) (hS.u_lat X hX) 𝔪 K hK
  obtain ⟨-, hI, hJ⟩ := GlobalTheory.NormSum.cls_finite_card_le D (G.V X).rank
  obtain ⟨hne, hle⟩ := GlobalTheory.congLev_relIndex_le D 𝔪 h𝔪 (G.V X).rank
  obtain ⟨hfin, hcard⟩ := hJ _ (GlobalTheory.FunObj.StdDatum.congLev_le 𝔪 _) hne
  have h1 := Nat.card_le_card_of_surjective f hf
  have hI' : (Nat.card (GlobalTheory.NormSum.Cls D (G.V X).rank (GlobalTheory.NormSum.intG D (G.V X).rank)) : ℝ) ≤ hBd D (G.V X).rank := hI
  calc (Nat.card (FinCl (G.V X) K) : ℝ)
      ≤ (Nat.card (GlobalTheory.NormSum.Cls D (G.V X).rank (GlobalTheory.FunObj.StdDatum.congLev D 𝔪 (G.V X).rank)) : ℝ) := by
        exact_mod_cast h1
    _ ≤ (Nat.card (GlobalTheory.NormSum.Cls D (G.V X).rank (GlobalTheory.NormSum.intG D (G.V X).rank)) : ℝ) *
          ((GlobalTheory.FunObj.StdDatum.congLev D 𝔪 (G.V X).rank).relIndex (GlobalTheory.NormSum.intG D (G.V X).rank) : ℝ) := by
        exact_mod_cast hcard
    _ ≤ hBd D (G.V X).rank * (Ideal.absNorm 𝔪 : ℝ) ^ ((G.V X).rank ^ 2) := by
        apply mul_le_mul hI' (by exact_mod_cast hle) (by positivity)
        exact le_trans (Nat.cast_nonneg _) hI'

end GlobalTheory.FrameTransport

end
