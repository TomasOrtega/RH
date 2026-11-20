import Mathlib
import Formalism.PeriodIntegrals.ScMuExists
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.InstDecomp

noncomputable section

open MeasureTheory
open scoped ENNReal Pointwise

namespace PI.ScMuExists.UnitaryGroupMassFormula

instance instSFiniteMuInf (I : Formalism.MainNotions.S.AutInst) : SFinite (muInf I) := by
  unfold muInf; infer_instance

instance instLeftInvMuInf (I : Formalism.MainNotions.S.AutInst) : (muInf I).IsMulLeftInvariant := by
  unfold muInf; infer_instance

/- English proof (translation)
Introduce `I r e f z hfr N H hN hNset hHset h hh`. Take `⟨N', H', hN', hH', -, -, hnorm'⟩` from `h4 I r e f z`. Establish `hmemN : ∀ x, x ∈ N ↔ x ∈ N'` using `fun x => by`. Rewrite using `[← SetLike.mem_coe, hNset, ← hN', SetLike.mem_coe]`. Establish `hmemH : ∀ x, x ∈ H ↔ x ∈ Hset I (frameSet I e f z)` using `fun x => by`.

Rewrite using `[← SetLike.mem_coe, hHset]`. Establish `hmemH' : ∀ x, x ∈ H ↔ x ∈ H'` using `fun x => by`. Rewrite using `[hmemH, ← hH', SetLike.mem_coe]`. Use `hm I.Ginf N H hN ?_ ?_ h hh` and prove the remaining obligations. Introduce `g hg x hx`.

Conclude with `(hmemN _).mpr (hnorm' g ((hmemH' g).mp hg) x ((hmemN x).mp hx))`. Introduce `g hg`. Take `⟨k, hk, p, hp, σ, hσ, hkp, hσp, C, hC⟩` from `hd I r e f z hfr g ((hmemH g).mp hg)`. Conclude with `⟨k, (hmemH k).mpr hk, p, (hmemH p).mpr hp, σ, (hmemH σ).mpr hσ, hkp, hσp, C, hC⟩`.
-/
theorem instConj_of (hm : GenModOne) (hd : InstDecomp) (h4 : SubFacts) : InstConj := by
  intro I r e f z hfr N H hN hNset hHset h hh
  obtain ⟨N', H', hN', hH', -, -, hnorm'⟩ := h4 I r e f z
  have hmemN : ∀ x, x ∈ N ↔ x ∈ N' := fun x => by
    rw [← SetLike.mem_coe, hNset, ← hN', SetLike.mem_coe]
  have hmemH : ∀ x, x ∈ H ↔ x ∈ Hset I (frameSet I e f z) := fun x => by
    rw [← SetLike.mem_coe, hHset]
  have hmemH' : ∀ x, x ∈ H ↔ x ∈ H' := fun x => by
    rw [hmemH, ← hH', SetLike.mem_coe]
  refine hm I.Ginf N H hN ?_ ?_ h hh
  · intro g hg x hx
    exact (hmemN _).mpr (hnorm' g ((hmemH' g).mp hg) x ((hmemN x).mp hx))
  · intro g hg
    obtain ⟨k, hk, p, hp, σ, hσ, hkp, hσp, C, hC⟩ := hd I r e f z hfr g ((hmemH g).mp hg)
    exact ⟨k, (hmemH k).mpr hk, p, (hmemH p).mpr hp, σ, (hmemH σ).mpr hσ, hkp, hσp, C, hC⟩

/- English proof (translation)
Introduce `I r e f z hee hff hef hz hzz`. Establish `hfr : IsFrame I e f z` using `⟨hee, hff, hef, hz, hzz⟩`. Take `⟨N, H, hNset, hHset, hN, hH, hnorm⟩` from `h4 I r e f z`. Take `⟨hNσ, hN0, hNc, hNinv, -, -⟩` from `h1 I.Ginf N hN`. Take `⟨hHσ, hH0, hHc, hHinv, -, -⟩` from `h1 I.Ginf H hH`.

Establish `hconj` using `h5 I r e f z hfr N H hN hNset hHset`. Establish `hprop` using `h6 I r e f z hfr N H hNset hHset`. Take `⟨hSf, hSmeas, hSc, hSinv, hSpos, hScpt⟩` from `h2 I.Ginf N H hN hH hnorm hconj hprop`. Use `hSf` as an intermediate fact. Take `⟨ν, hν⟩` from `h3 I.Ginf (muInf I) (mulMeas (haarSub N hN) (haarSub H hH)) ((N : Set I.Ginf) * (H : Set I.Ginf)) hSmeas hSc hSinv hSpos hScpt`.

Use `⟨haarSub N hN, haarSub H hH, ν, ?_, ?_, hν⟩` and prove the remaining obligations. Use `⟨hNσ, hN0, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hNset]`. Conclude with `hNc`. Introduce `s hs`.

Rewrite `hs` using `[← hNset]`. Conclude with `hNinv s hs`. Use `⟨hHσ, hH0, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[show Set.range e ∪ Set.range f ∪ {z} = frameSet I e f z from rfl, ← hHset]`. Conclude with `hHc`.

Introduce `s hs`. Rewrite `hs` using `[show Set.range e ∪ Set.range f ∪ {z} = frameSet I e f z from rfl, ← hHset]`. Conclude with `hHinv s hs`.
-/
theorem target_of (h1 : GenHaarSub) (h2 : GenSemi) (h3 : GenWeil) (h4 : SubFacts) (h5 : InstConj)
    (h6 : InstProper) : PI.ScMuExists.Target := by
  intro I r e f z hee hff hef hz hzz
  have hfr : IsFrame I e f z := ⟨hee, hff, hef, hz, hzz⟩
  obtain ⟨N, H, hNset, hHset, hN, hH, hnorm⟩ := h4 I r e f z
  obtain ⟨hNσ, hN0, hNc, hNinv, -, -⟩ := h1 I.Ginf N hN
  obtain ⟨hHσ, hH0, hHc, hHinv, -, -⟩ := h1 I.Ginf H hH
  have hconj := h5 I r e f z hfr N H hN hNset hHset
  have hprop := h6 I r e f z hfr N H hNset hHset
  obtain ⟨hSf, hSmeas, hSc, hSinv, hSpos, hScpt⟩ := h2 I.Ginf N H hN hH hnorm hconj hprop
  have := hSf
  obtain ⟨ν, hν⟩ := h3 I.Ginf (muInf I) (mulMeas (haarSub N hN) (haarSub H hH))
    ((N : Set I.Ginf) * (H : Set I.Ginf)) hSmeas hSc hSinv hSpos hScpt
  refine ⟨haarSub N hN, haarSub H hH, ν, ?_, ?_, hν⟩
  · refine ⟨hNσ, hN0, ?_, ?_⟩
    · rw [← hNset]
      exact hNc
    · intro s hs
      rw [← hNset] at hs
      exact hNinv s hs
  · refine ⟨hHσ, hH0, ?_, ?_⟩
    · rw [show Set.range e ∪ Set.range f ∪ {z} = frameSet I e f z from rfl, ← hHset]
      exact hHc
    · intro s hs
      rw [show Set.range e ∪ Set.range f ∪ {z} = frameSet I e f z from rfl, ← hHset] at hs
      exact hHinv s hs

/- English proof (translation)
Establish `h5 : InstConj` using `instConj_of hm hd h4`. Conclude with `target_of h1 h2 h3 h4 h5 h6`.
-/
theorem target_of_steps (h1 : GenHaarSub) (h2 : GenSemi) (h3 : GenWeil) (h4 : SubFacts) (hm : GenModOne)
    (hd : InstDecomp) (h6 : InstProper) : PI.ScMuExists.Target := by
  have h5 : InstConj := instConj_of hm hd h4
  exact target_of h1 h2 h3 h4 h5 h6

end PI.ScMuExists.UnitaryGroupMassFormula
