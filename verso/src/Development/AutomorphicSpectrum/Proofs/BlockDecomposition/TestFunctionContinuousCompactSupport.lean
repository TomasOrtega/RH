import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsTestZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOfIsBlockEmb
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.SmoothRep

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

/- English proof (translation)
Rewrite using `[(GlobalTheory.CuspQuot.isOpenEmbedding_val (E := E) (a := a)).isInducing.isCompact_iff]`. Establish `himg : (Units.val '' {y : GL (Fin a) (Cinf E) | toL y.val ∈ K}) = Matrix.of '' K`. Use extensionality with `m`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`.

Conclude with `⟨toL y.val, hy, by simp [toL]⟩`. Introduce and unpack `⟨x, hx, rfl⟩`. Take `⟨u, hu⟩` from `hs hx`. Use `⟨u, ?_, hu⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `toL u.val ∈ K`.

Rewrite using `[hu]`. Simplify `hx` using `[toL]`. Rewrite using `[himg]`. Conclude with `hK.image (continuous_id : Continuous (fun x : Lie E a => x))`.
-/
theorem isCompact_setOf_toL_mem {K : Set (Lie E a)} (hK : IsCompact K) (hs : K ⊆ invSet E a) :
    IsCompact {y : GL (Fin a) (Cinf E) | toL y.val ∈ K} := by
  rw [(GlobalTheory.CuspQuot.isOpenEmbedding_val (E := E) (a := a)).isInducing.isCompact_iff]
  have himg : (Units.val '' {y : GL (Fin a) (Cinf E) | toL y.val ∈ K}) = Matrix.of '' K := by
    ext m
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨toL y.val, hy, by simp [toL]⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨u, hu⟩ := hs hx
      refine ⟨u, ?_, hu⟩
      change toL u.val ∈ K
      rw [hu]
      simpa [toL] using hx
  rw [himg]
  exact hK.image (continuous_id : Continuous (fun x : Lie E a => x))

/- English proof (translation)
Establish `hpf` using `GlobalTheory.CuspRep.ContAut.continuous_map_pFin E a`. Establish `hpi` using `GlobalTheory.CuspRep.ContAut.continuous_map_pInf E a`. Establish `hclopen : IsClopen {v : GA E a | GeneralLinearGroup.map (pFin E) v ∈ U}` using `(IsClopen.preimage ⟨U.isClosed_of_isOpen hU, hU⟩ hpf)`. Establish `hval : Continuous fun v : GA E a => β (toL (GeneralLinearGroup.map (pInf E) v).val)` using `hβ.contDiff.continuous.comp ((Units.continuous_val (M := Matrix (Fin a) (Fin a) (Cinf E))).comp hpi)`. Unfold `ker`.

Use `Continuous.if (fun v hv => ?_) hval continuous_const` and prove the remaining obligations. Rewrite `hv` using `[hclopen.frontier_eq]`. Conclude with `absurd hv (Set.notMem_empty _)`.
-/
theorem continuous_ker {U : Subgroup (GL (Fin a) (Af E))} (hU : IsOpen (U : Set (GL (Fin a) (Af E))))
    {β : Lie E a → ℂ} (hβ : IsTest β) : Continuous (ker U β) := by
  have hpf := GlobalTheory.CuspRep.ContAut.continuous_map_pFin E a
  have hpi := GlobalTheory.CuspRep.ContAut.continuous_map_pInf E a
  have hclopen : IsClopen {v : GA E a | GeneralLinearGroup.map (pFin E) v ∈ U} :=
    (IsClopen.preimage ⟨U.isClosed_of_isOpen hU, hU⟩ hpf)
  have hval : Continuous fun v : GA E a => β (toL (GeneralLinearGroup.map (pInf E) v).val) :=
    hβ.contDiff.continuous.comp ((Units.continuous_val (M := Matrix (Fin a) (Fin a) (Cinf E))).comp hpi)
  classical
  unfold ker
  refine Continuous.if (fun v hv => ?_) hval continuous_const
  rw [hclopen.frontier_eq] at hv
  exact absurd hv (Set.notMem_empty _)

/- English proof (translation)
Establish `hT` using `isCompact_setOf_toL_mem (E := E) (a := a) hβ.compact hβ.support`. Use `HasCompactSupport.intro (K := (fun p : GL (Fin a) (Cinf E) × GL (Fin a) (Af E) => infGL E a p.1 * finGL E a p.2) '' ({y : GL (Fin a) (Cinf E) | toL y.val ∈ tsupport β} ×ˢ (U : Set (GL (Fin a) (Af E))))) ((hT.prod hUc).image ((GlobalTheory.CuspQuot.continuous_infGL.comp continuous …` and prove the remaining obligations. Assume the negation of the conclusion as `h0`. Unfold `ker at h0`. Use `split_ifs at h0 with hu`.

Conclude with `hg ⟨(_, _), ⟨subset_tsupport _ h0, hu⟩, infGL_mul_finGL g⟩`. Conclude with `h0 rfl`.
-/
theorem hasCompactSupport_ker {U : Subgroup (GL (Fin a) (Af E))}
    (hUc : IsCompact (U : Set (GL (Fin a) (Af E)))) {β : Lie E a → ℂ} (hβ : IsTest β) :
    HasCompactSupport (ker U β) := by
  have hT := isCompact_setOf_toL_mem (E := E) (a := a) hβ.compact hβ.support
  refine HasCompactSupport.intro (K := (fun p : GL (Fin a) (Cinf E) × GL (Fin a) (Af E) =>
      infGL E a p.1 * finGL E a p.2) '' ({y : GL (Fin a) (Cinf E) | toL y.val ∈ tsupport β} ×ˢ
        (U : Set (GL (Fin a) (Af E)))))
    ((hT.prod hUc).image ((GlobalTheory.CuspQuot.continuous_infGL.comp continuous_fst).mul
      ((GlobalTheory.BlockLevel.continuous_finGL a).comp continuous_snd))) fun g hg => ?_
  by_contra h0
  unfold ker at h0
  split_ifs at h0 with hu
  · exact hg ⟨(_, _), ⟨subset_tsupport _ h0, hu⟩, infGL_mul_finGL g⟩
  · exact h0 rfl

/- English proof (translation)
Introduce `E _ _ _ a U hU hUc β hβ`. Conclude with `⟨(continuous_ker hU hβ).comp continuous_inv, (hasCompactSupport_ker hUc hβ).comp_homeomorph (Homeomorph.inv (GA E a))⟩`.
-/
theorem continuous_hasCompactSupport_tst : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (U : Subgroup (GL (Fin a) (Af E))), IsOpen (U : Set (GL (Fin a) (Af E))) →
    IsCompact (U : Set (GL (Fin a) (Af E))) → ∀ β : Lie E a → ℂ, IsTest β →
    Continuous (tst U β) ∧ HasCompactSupport (tst U β) := by
  intro E _ _ _ a U hU hUc β hβ
  exact ⟨(continuous_ker hU hβ).comp continuous_inv,
    (hasCompactSupport_ker hUc hβ).comp_homeomorph (Homeomorph.inv (GA E a))⟩

end GlobalTheory.CompanionTheory.SmoothRep
