import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalRingCardinality.HostCls

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.ColNorms

/- English proof (translation)
Establish `key : ∀ (a b : ℕ) (ha : a.Prime) (hb : b.Prime), a = b → (haveI : Fact a.Prime` using `⟨ha⟩ (deriv (DirichletCharacter.LFunction ((quadraticChar (ZMod a)).ringHomComp (Int.castRingHom ℂ))) 1 / DirichletCharacter.LFunction ((quadraticChar (ZMod a)).ringHomComp (Int.castRingHom ℂ)) 1).re) = (haveI : Fact b.Prime := ⟨hb⟩ (deriv (DirichletCharacter.LFunction ((quadrati …`. Introduce and unpack `a b ha hb rfl`. Both sides reduce to the same expression. Conclude with `key _ _ N.hyp.2.1 D.host.hyp.2.1 hd`.
-/
theorem logDerivLOne_eq_of_prime_eq (D : D7) (N : NumDatum) (hd : N.d = D.host.d) : N.logDerivativeAtOne = TaylorLogMetric.logDerivativeAtOne D := by
  have key : ∀ (a b : ℕ) (ha : a.Prime) (hb : b.Prime), a = b →
      (haveI : Fact a.Prime := ⟨ha⟩
       (deriv (DirichletCharacter.LFunction ((quadraticChar (ZMod a)).ringHomComp (Int.castRingHom ℂ))) 1 /
        DirichletCharacter.LFunction ((quadraticChar (ZMod a)).ringHomComp (Int.castRingHom ℂ)) 1).re) =
      (haveI : Fact b.Prime := ⟨hb⟩
       (deriv (DirichletCharacter.LFunction ((quadraticChar (ZMod b)).ringHomComp (Int.castRingHom ℂ))) 1 /
        DirichletCharacter.LFunction ((quadraticChar (ZMod b)).ringHomComp (Int.castRingHom ℂ)) 1).re) := by
    rintro a b ha hb rfl
    rfl
  exact key _ _ N.hyp.2.1 D.host.hyp.2.1 hd

/- English proof (translation)
Introduce `D N X s Pr h`. Establish `hrd : N.rd = D.host.rdE` using `h.rd_eq`. Take `⟨hR, hq, hd, hcc, -, -, hX, -⟩` from `h`. Establish `hv : N.v = D.host.v`. Rewrite using `[NumDatum.v, Host.v, hrd]`.

Establish `hL` using `logDerivLOne_eq_of_prime_eq D N hd`. Establish `hfr : Module.finrank ℚ X.E = Module.finrank ℚ D.host.E` using `(AlgEquiv.ofRingEquiv (f := s.iE) (fun x => by simp) : X.E ≃ₐ[ℚ] D.host.E).toLinearEquiv.finrank_eq`. Establish `hE : Module.finrank ℚ X.E = 2 * N.R.f`. Rewrite using `[hfr, D.host.finrank_E', hR]`. Establish `htower : Module.finrank ℚ X.F * Module.finrank X.F X.E = Module.finrank ℚ X.E` using `Module.finrank_mul_finrank ℚ X.F X.E`.

Use `⟨hrd, hv, hL, ?_, ?_, ?_, hE, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[NumDatum.logOm, TaylorLogMetric.logOmVal, hv, hL]`. Rewrite using `[TaylorLogMetric.fF, hR]`. Rewrite `htower` using `[hX.ok.rankE, hE]`. Rewrite using `[Fields.f, hX.ok.card_Tau]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[hrd, Host.rdE, hfr, discr_eq_discr_of_ringEquiv X.E s.iE]`. Rewrite using `[hcc]`. Use `⟨top_ne_bot, ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem numbers_of_hostTie : ∀ (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X), HostTie N s Pr → N.rd = D.host.rdE ∧ N.v = D.host.v ∧ N.logDerivativeAtOne = TaylorLogMetric.logDerivativeAtOne D ∧ N.logOm = TaylorLogMetric.logOmVal D ∧ TaylorLogMetric.fF D = N.R.f ∧ X.f = N.R.f ∧ Module.finrank ℚ X.E = 2 * N.R.f ∧ |(discr X.E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ X.E : ℝ)) = N.rd ∧ TaylorLogMetric.IsCurveIdeal D D.host.ccK := by
  intro D N X s Pr h
  have hrd : N.rd = D.host.rdE := h.rd_eq
  obtain ⟨hR, hq, hd, hcc, -, -, hX, -⟩ := h
  have hv : N.v = D.host.v := by
    rw [NumDatum.v, Host.v, hrd]
  have hL := logDerivLOne_eq_of_prime_eq D N hd
  have hfr : Module.finrank ℚ X.E = Module.finrank ℚ D.host.E :=
    (AlgEquiv.ofRingEquiv (f := s.iE) (fun x => by simp) : X.E ≃ₐ[ℚ] D.host.E).toLinearEquiv.finrank_eq
  have hE : Module.finrank ℚ X.E = 2 * N.R.f := by
    rw [hfr, D.host.finrank_E', hR]
  have htower : Module.finrank ℚ X.F * Module.finrank X.F X.E = Module.finrank ℚ X.E :=
    Module.finrank_mul_finrank ℚ X.F X.E
  refine ⟨hrd, hv, hL, ?_, ?_, ?_, hE, ?_, ?_⟩
  · rw [NumDatum.logOm, TaylorLogMetric.logOmVal, hv, hL]
  · rw [TaylorLogMetric.fF, hR]
  · rw [hX.ok.rankE, hE] at htower
    rw [Fields.f, hX.ok.card_Tau]
    omega
  · rw [hrd, Host.rdE, hfr, discr_eq_discr_of_ringEquiv X.E s.iE]
  · rw [hcc]
    refine ⟨top_ne_bot, ?_⟩
    simp

end GlobalTheory.ColNorms
