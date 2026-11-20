import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField IsDedekindDomain
open GlobalTheory.FunObj.SqNum (nuH halfRank IsTor)

noncomputable section

namespace GlobalTheory.ThmAUpper

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)

/- English proof (translation)
Establish `h0 : p.tupT D.what₂.mu0 = p.P.A3.A.μ0`. Rewrite using `[← p.P.div.tup.mu0]`. Conclude with `p.tupT_tup _`. Rewrite using `[← h0, p.tupXi _ (Or.inl rfl), p.Tp.trueColumnChoices_heckeChar_reference_eq_one]`.
-/
theorem xiH_base : p.R.toRealDat.toLevCh.xiH p.P.A3.A.μ0 = 1 := by
  have h0 : p.tupT D.what₂.mu0 = p.P.A3.A.μ0 := by
    rw [← p.P.div.tup.mu0]; exact p.tupT_tup _
  rw [← h0, p.tupXi _ (Or.inl rfl), p.Tp.trueColumnChoices_heckeChar_reference_eq_one]

/- English proof (translation)
Establish `h0 : p.tupT D.what₂.mu0 = p.P.A3.A.μ0`. Rewrite using `[← p.P.div.tup.mu0]`. Conclude with `p.tupT_tup _`. Establish `e1 : p.R.mu w = p.tupT (D.what₂.muAt (D.plEq.symm w))` using `by rw [p.tupAt]; simp`. Establish `htw : D.what₂.muAt (D.plEq.symm w) ≠ D.what₂.mu0` using `fun e => hw (by rw [e1, e, h0])`.

Establish `hmt : D.what₂.muAt (D.plEq.symm w) = D.what₂.muTw (D.plEq.symm w)` using `(D.what₂.muAt_or _).resolve_left htw`. Use `⟨htw, ?_⟩` and prove the remaining obligations. Rewrite using `[e1, p.tupXi _ (Or.inr ⟨_, rfl⟩), hmt, p.Tp.xi_tw]`.
-/
theorem xiH_twisted (w : HeightOneSpectrum (𝓞 D.what₂.LL)) (hw : p.R.mu w ≠ p.P.A3.A.μ0) :
    TwistedAt D (D.plEq.symm w) ∧ p.R.toRealDat.toLevCh.xiH (p.R.mu w) =
      p.R.C.delAt (D.what₂.places.resChar (D.plEq.symm w)) * p.Tp.psi (D.plEq.symm w) := by
  have h0 : p.tupT D.what₂.mu0 = p.P.A3.A.μ0 := by
    rw [← p.P.div.tup.mu0]; exact p.tupT_tup _
  have e1 : p.R.mu w = p.tupT (D.what₂.muAt (D.plEq.symm w)) := by rw [p.tupAt]; simp
  have htw : D.what₂.muAt (D.plEq.symm w) ≠ D.what₂.mu0 := fun e => hw (by rw [e1, e, h0])
  have hmt : D.what₂.muAt (D.plEq.symm w) = D.what₂.muTw (D.plEq.symm w) := (D.what₂.muAt_or _).resolve_left htw
  refine ⟨htw, ?_⟩
  rw [e1, p.tupXi _ (Or.inr ⟨_, rfl⟩), hmt, p.Tp.xi_tw]

end

/- English proof (translation)
Assume the negation of the conclusion as `hq`. Establish `hq'` using `D.what₂.places.resChar_prime w`. Establish `hnot : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) ∉ (D.plEq w).asIdeal`. Introduce `hin`. Take `⟨a, b, hab⟩ : IsCoprime ((D.what₂.places.resChar w : ℕ) : ℤ) (l : ℤ)` from `Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hq' hl).2 hq)`.

Apply `(D.plEq w).isPrime.ne_top` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one]`. Establish `e : (1 : 𝓞 D.what₂.LL) = (a : 𝓞 D.what₂.LL) * ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) + (b : 𝓞 D.what₂.LL) * ((l : ℕ) : 𝓞 D.what₂.LL)`. Conclude with `congrArg (Int.cast : ℤ → 𝓞 D.what₂.LL) hab.symm` after adjusting the coercions. Rewrite using `[e]`.

Conclude with `Ideal.add_mem _ (Ideal.mul_mem_left _ _ hin) (Ideal.mul_mem_left _ _ h)`. Establish `h1 : (D.plEq w).valuation D.what₂.LL (algebraMap (𝓞 D.what₂.LL) D.what₂.LL ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL)) = 1`. Rewrite using `[HeightOneSpectrum.valuation_of_algebraMap]`. Conclude with `HeightOneSpectrum.intValuation_eq_one_iff.2 hnot`. Establish `h2` using `D.what₂.places.val_resChar w`.

Rewrite `h2` using `[D.val_eq w _ (Nat.cast_ne_zero.2 hq'.ne_zero)]`. Establish `h3 : vAdd (D.plEq w) ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) = (D.what₂.places.ramIdx w : ℕ)`. Conclude with `h2` after adjusting the coercions. Establish `h4 : vAdd (D.plEq w) ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) = 0`. Unfold `vAdd`.

Rewrite using `[show ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) = algebraMap (𝓞 D.what₂.LL) D.what₂.LL ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) by simp, h1]`. Simplify using the standard rewrite rules. Use `D.what₂.places.ramIdx_pos w` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem resChar_eq {D : D7} (w : D.what₂.places.Pl) {l : ℕ} (hl : l.Prime)
    (h : ((l : ℕ) : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal) : D.what₂.places.resChar w = l := by
  by_contra hq
  have hq' := D.what₂.places.resChar_prime w
  have hnot : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) ∉ (D.plEq w).asIdeal := by
    intro hin
    obtain ⟨a, b, hab⟩ : IsCoprime ((D.what₂.places.resChar w : ℕ) : ℤ) (l : ℤ) :=
      Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hq' hl).2 hq)
    apply (D.plEq w).isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have e : (1 : 𝓞 D.what₂.LL) = (a : 𝓞 D.what₂.LL) * ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) +
        (b : 𝓞 D.what₂.LL) * ((l : ℕ) : 𝓞 D.what₂.LL) := by
      exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 D.what₂.LL) hab.symm
    rw [e]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hin) (Ideal.mul_mem_left _ _ h)
  have h1 : (D.plEq w).valuation D.what₂.LL (algebraMap (𝓞 D.what₂.LL) D.what₂.LL ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL)) = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.2 hnot
  have h2 := D.what₂.places.val_resChar w
  rw [D.val_eq w _ (Nat.cast_ne_zero.2 hq'.ne_zero)] at h2
  have h3 : vAdd (D.plEq w) ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) = (D.what₂.places.ramIdx w : ℕ) := by
    exact_mod_cast h2
  have h4 : vAdd (D.plEq w) ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) = 0 := by
    unfold vAdd
    rw [show ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) =
      algebraMap (𝓞 D.what₂.LL) D.what₂.LL ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) by simp, h1]
    simp
  have := D.what₂.places.ramIdx_pos w
  omega

/- English proof (translation)
Unfold `nuH`. Rewrite using `[(xiH_twisted p w hw).2, xiH_base p, mul_one, div_eq_mul_inv, div_eq_mul_inv]`. The two sides agree by associativity and commutativity.
-/
theorem nuH_twisted {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) {CF : ℝ} (G : Grid p CF) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) (hw : p.R.mu w ≠ p.P.A3.A.μ0)
    (i j : Fin D.R.m) : nuH G (p.R.mu w) i j = nuH G p.P.A3.A.μ0 i j *
      p.R.C.delAt (D.what₂.places.resChar (D.plEq.symm w)) * p.Tp.psi (D.plEq.symm w) := by
  unfold nuH
  rw [(xiH_twisted p w hw).2, xiH_base p, mul_one, div_eq_mul_inv, div_eq_mul_inv]
  ac_rfl

end GlobalTheory.ThmAUpper
