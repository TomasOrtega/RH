import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrConjApply
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDetSmulSubOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport

noncomputable section

namespace GlobalTheory.FrameTransport

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Establish `h1 : GlobalTheory.LFun.finAdEquiv D.host.F D.host.E ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x` using `(GlobalTheory.LFun.toFinAd_tmul (1 : Af D.host.F) x).trans (by rw [map_one, one_mul])`. Establish `h2 : GlobalTheory.BotFormula.toFinE D (StandardLatticesGL3.inc D x) = algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x` using `(GlobalTheory.LFun.toFinAd_tmul (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) x).trans (by rw [map_one, one_mul])`. Use `show (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm (GlobalTheory.BotFormula.toFinE D (StandardLatticesGL3.inc D x)) = _`. Rewrite using `[h2, ← h1, RingEquiv.symm_apply_apply]`.
-/
theorem toAfE_inc (D : D7) (x : D.host.E) :
    GlobalTheory.BotFormula.toAfE D (StandardLatticesGL3.inc D x) = (1 : Af D.host.F) ⊗ₜ[D.host.F] x := by
  have h1 : GlobalTheory.LFun.finAdEquiv D.host.F D.host.E ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) =
      algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x :=
    (GlobalTheory.LFun.toFinAd_tmul (1 : Af D.host.F) x).trans (by rw [map_one, one_mul])
  have h2 : GlobalTheory.BotFormula.toFinE D (StandardLatticesGL3.inc D x) = algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x :=
    (GlobalTheory.LFun.toFinAd_tmul (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) x).trans (by rw [map_one, one_mul])
  show (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm (GlobalTheory.BotFormula.toFinE D (StandardLatticesGL3.inc D x)) = _
  rw [h2, ← h1, RingEquiv.symm_apply_apply]

/- English proof (translation)
Use `show Lev.swapAE D (GlobalTheory.BotFormula.toAfE D (StandardLatticesGL3.inc D x)) = _`. Rewrite using `[toAfE_inc]`. Both sides reduce to the same expression.
-/
theorem adSwap_inc (D : D7) (x : D.host.E) : adSwap D (StandardLatticesGL3.inc D x) = inclEAf D x := by
  show Lev.swapAE D (GlobalTheory.BotFormula.toAfE D (StandardLatticesGL3.inc D x)) = _
  rw [toAfE_inc]
  rfl

/- English proof (translation)
Establish `e : (Lev.finE V g).val = (Formalism.L2.Theta.mt V g).map (fun y => Lev.swapAE D (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) y))` using `rfl`. Rewrite using `[e, show Formalism.L2.Theta.mt V g = _ from h]`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Simplify using `only [Matrix.map_apply]`. Use `show Lev.swapAE D (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) ((1 : AF D.host.F) ⊗ₜ[D.host.F] a i j)) = _`.

Rewrite using `[Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]`. Both sides reduce to the same expression.
-/
theorem finE_val_of_isRat {D : D7} {V : HSp D} {g : GA D V} {a : Matrix (Fin V.rank) (Fin V.rank) D.host.E}
    (h : GlobalTheory.RatAut.IsRat V g a) :
    (Lev.finE V g).val = a.map (inclEAf D) := by
  have e : (Lev.finE V g).val =
      (Formalism.L2.Theta.mt V g).map (fun y => Lev.swapAE D
        (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) y)) := rfl
  rw [e, show Formalism.L2.Theta.mt V g = _ from h]
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.map_apply]
  show Lev.swapAE D (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)
    ((1 : AF D.host.F) ⊗ₜ[D.host.F] a i j)) = _
  rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
  rfl

/- English proof (translation)
Introduce `D V fr hfr`. Set `S : Subgroup (StandardLatticesGL3.GA D V.rank)` to `((ratFin V).map (finG V)).comap ((frConj fr).comp (StandardLatticesGL3.GA D V.rank).subtype)`. It suffices to establish `hS : GlobalTheory.NormSum.ratG D V.rank ≤ S by`. Introduce `γ hγ`. Take `⟨q, hq, e⟩` from `hS hγ`.

Conclude with `⟨q, hq, e⟩`. Rewrite using `[GlobalTheory.NormSum.ratG, Subgroup.closure_le]`. Introduce and unpack `g ⟨γ₀, hγ₀⟩`. Establish `h1 : (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (StandardLatticesGL3.inc D) = 1` using `Matrix.map_one _ (map_zero _) (map_one _)`. Establish `hg : ((g.1 : Matrix (Fin V.rank) (Fin V.rank) (StandardLatticesGL3.AE D)).map (StandardLatticesGL3.sgA D)).transpose * (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (StandardLatticesGL3.inc D) * (g.1 : Matrix (Fin V.rank) (Fin V.rank) (StandardLatticesGL3.AE D)) = (1 : Matr …` using `g.2`.

Establish `hc : ((γ₀.map D.host.conj).transpose).map (StandardLatticesGL3.inc D) = ((γ₀.map (StandardLatticesGL3.inc D)).map (StandardLatticesGL3.sgA D)).transpose`. Use extensionality with `i j`. Simplify using `[StandardLatticesGL3.sgA, StandardLatticesGL3.inc, Formalism.UG.sigR, Formalism.UG.inclE]`. Establish `hu : (γ₀.map D.host.conj).transpose * γ₀ = 1`. Apply `Matrix.map_injective (GlobalTheory.NormSum.inc_inj D)` to reduce the goal to its premises.

Unfold `StandardLatticesGL3.IsRat at hγ₀`. Rewrite `hg` using `[hγ₀, h1, Matrix.mul_one, ← hc, ← Matrix.map_mul]`. Conclude with `hg.trans h1.symm`. Establish `hu' : γ₀ᴴ * γ₀ = 1`. Establish `: γ₀ᴴ = (γ₀.map D.host.conj).transpose` using `Matrix.ext fun i j => by show star (γ₀ j i) = D.host.conj (γ₀ j i)`.

Conclude with `Formalism.MainNotions.GlobalTheoryTheory.jnt_sig_eq_conj D (γ₀ j i)`. Rewrite using `[this, hu]`. Use `set F : Matrix (Fin V.rank) (Fin V.rank) D.host.E := (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) with hF`. Use `set Fi : Matrix (Fin V.rank) (Fin V.rank) D.host.E := (fr⁻¹ : GL (Fin V.rank) D.host.E).val with hFi`. Establish `hFFi : F * Fi = 1` using `by rw [hF, hFi, ← Units.val_mul, mul_inv_cancel, Units.val_one]`.

Establish `hfr' : Fᴴ * V.gram * F = 1` using `hfr`. Establish `hJ : V.gram = Fiᴴ * Fi`. Use `congrArg (fun M => Fiᴴ * M * Fi) hfr'` as an intermediate fact. Simplify using `only [Matrix.mul_one] at this`. Rewrite using `[← this, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, hFFi, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_assoc, hFFi, Matrix.mul_one]`.

Use `set a : Matrix (Fin V.rank) (Fin V.rank) D.host.E := F * γ₀ * Fi with ha`. Establish `hau : aᴴ * V.gram * a = V.gram`. Establish `e1 : aᴴ * V.gram * a = Fiᴴ * γ₀ᴴ * (Fᴴ * V.gram * F) * γ₀ * Fi`. Rewrite using `[ha, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]`. Simplify using `only [Matrix.mul_assoc]`.

Rewrite using `[e1, hfr', Matrix.mul_one, Matrix.mul_assoc Fiᴴ, hu', Matrix.mul_one, hJ]`. Take `⟨g', hg'Q, hg'⟩` from `GlobalTheory.RatAut.exists_of_unitary V hau`. Take `⟨k, k1, k2⟩` from `GlobalTheory.UnitarySplit.ga_glue V 1 (finHom V g') (one_mem _) (GlobalTheory.UnitarySplit.finHom_mem V g')`. Establish `hkC : k ∈ GfC V` using `MonoidHom.mem_ker.2 k1`. Establish `hfin : finG V ⟨k, hkC⟩ = Lev.finE V g'` using `by show Formalism.UG.bc (Lev.swapAE D) (finHom V k) = Formalism.UG.bc (Lev.swapAE D) (finHom V g')`.

Rewrite using `[k2]`. Use `⟨⟨k, hkC⟩, ⟨g', hg'Q, hfin.symm⟩, ?_⟩` and prove the remaining obligations. Use `show finG V ⟨k, hkC⟩ = frConj fr g.1`. Rewrite using `[hfin, frConj_apply]`. Apply `Units.ext` to reduce the goal to its premises.

Rewrite using `[finE_val_of_isRat hg', ← map_inv, Units.val_mul, Units.val_mul]`. Establish `eb : ∀ (M : GL (Fin V.rank) D.host.E), (Formalism.UG.bc (inclEAf D) M).val = M.val.map (inclEAf D)` using `fun M => rfl`. Establish `eg : (Formalism.UG.bc (adSwap D) g.1).val = γ₀.map (inclEAf D)` using `by show g.1.val.map (adSwap D) = _`. Unfold `StandardLatticesGL3.IsRat at hγ₀`. Rewrite using `[hγ₀, Matrix.map_map]`.

Conclude with `Matrix.ext fun i j => adSwap_inc D (γ₀ i j)`. Rewrite using `[eb, eb, eg, ha, Matrix.map_mul, Matrix.map_mul]`.
-/
theorem frConj_ratG : ∀ {D : D7} (V : HSp D) (fr : GL (Fin V.rank) D.host.E),
    Formalism.UG.cT (↑D.sp.cm.sig) (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram *
      (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = 1 →
    ∀ γ ∈ GlobalTheory.NormSum.ratG D V.rank, ∃ q ∈ ratFin V, finG V q = GlobalTheory.FrameTransport.frConj fr γ.1 := by
  intro D V fr hfr
  let S : Subgroup (StandardLatticesGL3.GA D V.rank) :=
    ((ratFin V).map (finG V)).comap ((frConj fr).comp (StandardLatticesGL3.GA D V.rank).subtype)
  suffices hS : GlobalTheory.NormSum.ratG D V.rank ≤ S by
    intro γ hγ
    obtain ⟨q, hq, e⟩ := hS hγ
    exact ⟨q, hq, e⟩
  rw [GlobalTheory.NormSum.ratG, Subgroup.closure_le]
  rintro g ⟨γ₀, hγ₀⟩

  have h1 : (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (StandardLatticesGL3.inc D) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  have hg : ((g.1 : Matrix (Fin V.rank) (Fin V.rank) (StandardLatticesGL3.AE D)).map (StandardLatticesGL3.sgA D)).transpose *
      (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (StandardLatticesGL3.inc D) * (g.1 : Matrix (Fin V.rank) (Fin V.rank) (StandardLatticesGL3.AE D)) =
      (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (StandardLatticesGL3.inc D) := g.2
  have hc : ((γ₀.map D.host.conj).transpose).map (StandardLatticesGL3.inc D) = ((γ₀.map (StandardLatticesGL3.inc D)).map (StandardLatticesGL3.sgA D)).transpose := by
    ext i j
    simp [StandardLatticesGL3.sgA, StandardLatticesGL3.inc, Formalism.UG.sigR, Formalism.UG.inclE]
  have hu : (γ₀.map D.host.conj).transpose * γ₀ = 1 := by
    apply Matrix.map_injective (GlobalTheory.NormSum.inc_inj D)
    unfold StandardLatticesGL3.IsRat at hγ₀
    rw [hγ₀, h1, Matrix.mul_one, ← hc, ← Matrix.map_mul] at hg
    exact hg.trans h1.symm
  have hu' : γ₀ᴴ * γ₀ = 1 := by
    have : γ₀ᴴ = (γ₀.map D.host.conj).transpose := Matrix.ext fun i j => by
      show star (γ₀ j i) = D.host.conj (γ₀ j i)
      exact Formalism.MainNotions.GlobalTheoryTheory.jnt_sig_eq_conj D (γ₀ j i)
    rw [this, hu]

  set F : Matrix (Fin V.rank) (Fin V.rank) D.host.E := (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) with hF
  set Fi : Matrix (Fin V.rank) (Fin V.rank) D.host.E := (fr⁻¹ : GL (Fin V.rank) D.host.E).val with hFi
  have hFFi : F * Fi = 1 := by rw [hF, hFi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hfr' : Fᴴ * V.gram * F = 1 := hfr
  have hJ : V.gram = Fiᴴ * Fi := by
    have := congrArg (fun M => Fiᴴ * M * Fi) hfr'
    simp only [Matrix.mul_one] at this
    rw [← this, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, hFFi, Matrix.conjTranspose_one,
      Matrix.one_mul, Matrix.mul_assoc, hFFi, Matrix.mul_one]
  set a : Matrix (Fin V.rank) (Fin V.rank) D.host.E := F * γ₀ * Fi with ha
  have hau : aᴴ * V.gram * a = V.gram := by
    have e1 : aᴴ * V.gram * a = Fiᴴ * γ₀ᴴ * (Fᴴ * V.gram * F) * γ₀ * Fi := by
      rw [ha, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    rw [e1, hfr', Matrix.mul_one, Matrix.mul_assoc Fiᴴ, hu', Matrix.mul_one, hJ]
  obtain ⟨g', hg'Q, hg'⟩ := GlobalTheory.RatAut.exists_of_unitary V hau
  obtain ⟨k, k1, k2⟩ := GlobalTheory.UnitarySplit.ga_glue V 1 (finHom V g') (one_mem _) (GlobalTheory.UnitarySplit.finHom_mem V g')
  have hkC : k ∈ GfC V := MonoidHom.mem_ker.2 k1
  have hfin : finG V ⟨k, hkC⟩ = Lev.finE V g' := by
    show Formalism.UG.bc (Lev.swapAE D) (finHom V k) = Formalism.UG.bc (Lev.swapAE D) (finHom V g')
    rw [k2]
  refine ⟨⟨k, hkC⟩, ⟨g', hg'Q, hfin.symm⟩, ?_⟩
  show finG V ⟨k, hkC⟩ = frConj fr g.1
  rw [hfin, frConj_apply]
  apply Units.ext
  rw [finE_val_of_isRat hg', ← map_inv, Units.val_mul, Units.val_mul]
  have eb : ∀ (M : GL (Fin V.rank) D.host.E),
      (Formalism.UG.bc (inclEAf D) M).val = M.val.map (inclEAf D) := fun M => rfl
  have eg : (Formalism.UG.bc (adSwap D) g.1).val =
      γ₀.map (inclEAf D) := by
    show g.1.val.map (adSwap D) = _
    unfold StandardLatticesGL3.IsRat at hγ₀
    rw [hγ₀, Matrix.map_map]
    exact Matrix.ext fun i j => adSwap_inc D (γ₀ i j)
  rw [eb, eb, eg, ha, Matrix.map_mul, Matrix.map_mul]

end GlobalTheory.FrameTransport
