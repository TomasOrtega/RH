import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StGlob
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSupercuspidalTypeCharacterZmodPowStatement
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

/- English proof (translation)
Introduce `hC E _ _ w a l hl hw ha N hN`. Take `⟨m, -, J', lam, hJo, hJc, hJN, hJtf, -, -⟩` from `GlobalTheory.T.exists_supercuspidal_type_character_zmod_pow E w a l hl hw ha N hN 0`. Take `⟨J, hT, hp⟩` from `hC E w a l hl hw`. Take `⟨s, hs⟩` from `hT.small _ (hJo.mem_nhds J'.one_mem)`. Use `⟨fun n => J (s + n), ⟨fun n => hT.isOpen _, fun n => hT.compact _, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `i j hij`. Conclude with `hT.anti (Nat.add_le_add_left hij s)`. Introduce `n g hg x hx`. Conclude with `hT.normal (s + n) g (hT.anti (Nat.zero_le (s + 0)) hg) x hx`. Introduce `M hM`.

Take `⟨n, hn⟩` from `hT.small M hM`. Conclude with `⟨n, fun x hx => hn (hT.anti (Nat.le_add_left n s) hx)⟩`. Conclude with `fun x hx => hJN (hs hx)`. Conclude with `fun g hg ho => hJtf g (hs hg) ho`. Introduce `n x hx`.

Proceed by induction on `n with`. Consider the case `zero => simpa using hx`. Consider the case `succ n ih`. Rewrite using `[pow_succ, pow_mul]`. Conclude with `hp (s + n) _ ih`.
-/
theorem UpperTheory.Gal.Gen.tower_pf :
    UpperTheory.Gal.Gen.CongSub → UpperTheory.Gal.Gen.Tower := by
  intro hC E _ _ w a l hl hw ha N hN
  obtain ⟨m, -, J', lam, hJo, hJc, hJN, hJtf, -, -⟩ := GlobalTheory.T.exists_supercuspidal_type_character_zmod_pow E w a l hl hw ha N hN 0
  obtain ⟨J, hT, hp⟩ := hC E w a l hl hw
  obtain ⟨s, hs⟩ := hT.small _ (hJo.mem_nhds J'.one_mem)
  refine ⟨fun n => J (s + n), ⟨fun n => hT.isOpen _, fun n => hT.compact _, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro i j hij
    exact hT.anti (Nat.add_le_add_left hij s)
  · intro n g hg x hx
    exact hT.normal (s + n) g (hT.anti (Nat.zero_le (s + 0)) hg) x hx
  · intro M hM
    obtain ⟨n, hn⟩ := hT.small M hM
    exact ⟨n, fun x hx => hn (hT.anti (Nat.le_add_left n s) hx)⟩
  · exact fun x hx => hJN (hs hx)
  · exact fun g hg ho => hJtf g (hs hg) ho
  · intro n x hx
    induction n with
    | zero => simpa using hx
    | succ n ih =>
      rw [pow_succ, pow_mul]
      exact hp (s + n) _ ih
