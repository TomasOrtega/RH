import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.UnipLat

open NumberField NumberField.InfinitePlace

namespace Formalism.L2.SG.Pf

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ hE _ φ hφ`. Take `⟨R, hR⟩` from `isBounded_iff_forall_norm_le.mp (ZSpan.fundamentalDomain_isBounded (mixedEmbedding.latticeBasis E))`. Use `⟨R, fun t => ?_⟩` and prove the remaining obligations. Set `w : InfinitePlace F → InfinitePlace E` to `fun v => InfinitePlace.mk (φ v)`. Establish `hw : ∀ v, (w v).comap (algebraMap F E) = v`.

Introduce `v`. Establish `hcomp : (φ v).comp (algebraMap F E) = v.embedding` using `RingHom.ext (hφ v)`. Simplify using `only [w, InfinitePlace.comap_mk, hcomp, InfinitePlace.mk_embedding]`. Establish `hinj : ∀ v v', w v = w v' → v = v'`. Introduce `v v' h`.

Rewrite using `[← hw v, ← hw v', h]`. Set `c : InfinitePlace F → ℂ` to `fun v => if (w v).embedding = φ v then t v else (starRingEnd ℂ) (t v)`. Set `x : mixedEmbedding.mixedSpace E` to `(0, fun u => if h : ∃ v, u.1 = w v then c h.choose else 0)`. Establish `hmem : x - ZSpan.fract (mixedEmbedding.latticeBasis E) x ∈ mixedEmbedding.integerLattice E`. Rewrite using `[← mixedEmbedding.mem_span_latticeBasis, ZSpan.fract_apply, sub_sub_cancel]`.

Conclude with `(ZSpan.floor _ x).2`. Take `⟨m, hm⟩` from `hmem`. Establish `hm' : mixedEmbedding E (m : E) = x - ZSpan.fract (mixedEmbedding.latticeBasis E) x` using `hm`. Use `⟨m, fun v => ?_⟩` and prove the remaining obligations. Establish `hc : (w v).IsComplex` using `hE.isComplex (w v)`.

Set `u : {u : InfinitePlace E // u.IsComplex}` to `⟨w v, hc⟩`. Establish `hxu : x.2 u = c v`. Establish `hex : ∃ v', u.1 = w v'` using `⟨v, rfl⟩`. Use `show (if h : ∃ v', u.1 = w v' then c h.choose else 0) = c v`. Rewrite using `[dif_pos hex, hinj _ _ hex.choose_spec.symm]`.

Establish `hfr : x - mixedEmbedding E (m : E) = ZSpan.fract (mixedEmbedding.latticeBasis E) x`. Rewrite using `[hm', sub_sub_cancel]`. Establish `hval : (ZSpan.fract (mixedEmbedding.latticeBasis E) x).2 u = c v - (w v).embedding (m : E)`. Rewrite using `[← hfr, Prod.snd_sub, Pi.sub_apply, hxu, mixedEmbedding.mixedEmbedding_apply_isComplex]`. Establish `hb : ‖c v - (w v).embedding (m : E)‖ ≤ R`.

Rewrite using `[← hval]`. Conclude with `((norm_le_pi_norm _ u).trans (norm_snd_le _)).trans (hR _ (ZSpan.fract_mem_fundamentalDomain _ x))`. Distinguish the cases in `h : (w v).embedding = φ v`. Establish `hcv : c v = t v` using `if_pos h`. Rewrite `hb` using `[hcv, h]`.

Conclude with `hb`. Establish `h2 : (w v).embedding = ComplexEmbedding.conjugate (φ v)` using `(InfinitePlace.embedding_mk_eq (φ v)).resolve_left h`. Establish `hcv : c v = (starRingEnd ℂ) (t v)` using `if_neg h`. Rewrite `hb` using `[hcv, h2, ComplexEmbedding.conjugate_coe_eq, ← map_sub, Complex.norm_conj]`. Conclude with `hb`.
-/
theorem oeApprox_holds : Formalism.L2.SG.Pf.UnipLat.OEApprox := by
  intro F E _ _ _ _ _ _ hE _ φ hφ
  classical

  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp
    (ZSpan.fundamentalDomain_isBounded (mixedEmbedding.latticeBasis E))
  refine ⟨R, fun t => ?_⟩

  let w : InfinitePlace F → InfinitePlace E := fun v => InfinitePlace.mk (φ v)
  have hw : ∀ v, (w v).comap (algebraMap F E) = v := by
    intro v
    have hcomp : (φ v).comp (algebraMap F E) = v.embedding := RingHom.ext (hφ v)
    simp only [w, InfinitePlace.comap_mk, hcomp, InfinitePlace.mk_embedding]
  have hinj : ∀ v v', w v = w v' → v = v' := by
    intro v v' h
    rw [← hw v, ← hw v', h]
  let c : InfinitePlace F → ℂ := fun v =>
    if (w v).embedding = φ v then t v else (starRingEnd ℂ) (t v)
  let x : mixedEmbedding.mixedSpace E :=
    (0, fun u => if h : ∃ v, u.1 = w v then c h.choose else 0)
  have hmem : x - ZSpan.fract (mixedEmbedding.latticeBasis E) x ∈
      mixedEmbedding.integerLattice E := by
    rw [← mixedEmbedding.mem_span_latticeBasis, ZSpan.fract_apply, sub_sub_cancel]
    exact (ZSpan.floor _ x).2
  obtain ⟨m, hm⟩ := hmem
  have hm' : mixedEmbedding E (m : E) = x - ZSpan.fract (mixedEmbedding.latticeBasis E) x := hm
  refine ⟨m, fun v => ?_⟩
  have hc : (w v).IsComplex := hE.isComplex (w v)
  let u : {u : InfinitePlace E // u.IsComplex} := ⟨w v, hc⟩
  have hxu : x.2 u = c v := by
    have hex : ∃ v', u.1 = w v' := ⟨v, rfl⟩
    show (if h : ∃ v', u.1 = w v' then c h.choose else 0) = c v
    rw [dif_pos hex, hinj _ _ hex.choose_spec.symm]
  have hfr : x - mixedEmbedding E (m : E) = ZSpan.fract (mixedEmbedding.latticeBasis E) x := by
    rw [hm', sub_sub_cancel]
  have hval : (ZSpan.fract (mixedEmbedding.latticeBasis E) x).2 u
      = c v - (w v).embedding (m : E) := by
    rw [← hfr, Prod.snd_sub, Pi.sub_apply, hxu, mixedEmbedding.mixedEmbedding_apply_isComplex]
  have hb : ‖c v - (w v).embedding (m : E)‖ ≤ R := by
    rw [← hval]
    exact ((norm_le_pi_norm _ u).trans (norm_snd_le _)).trans
      (hR _ (ZSpan.fract_mem_fundamentalDomain _ x))
  by_cases h : (w v).embedding = φ v
  · have hcv : c v = t v := if_pos h
    rw [hcv, h] at hb
    exact hb
  · have h2 : (w v).embedding = ComplexEmbedding.conjugate (φ v) :=
      (InfinitePlace.embedding_mk_eq (φ v)).resolve_left h
    have hcv : c v = (starRingEnd ℂ) (t v) := if_neg h
    rw [hcv, h2, ComplexEmbedding.conjugate_coe_eq, ← map_sub, Complex.norm_conj] at hb
    exact hb

end Formalism.L2.SG.Pf
