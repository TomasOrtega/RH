import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.RhoDiv
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.RhoStar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.RhoBij

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.Dict.Br

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

/- English proof (translation)
Use `show P.φ v w h a + P.φ v w h 0 * P.rt w = _`. Simplify using the standard rewrite rules.
-/
private theorem rho_coe (P : Pre L) (v : Pl (Lp L)) (w : Plc L) (h : un w = v) (a : Kv v) :
    P.rho v w h ⟨a, 0⟩ = P.φ v w h a := by
  show P.φ v w h a + P.φ v w h 0 * P.rt w = _
  simp

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Establish `hE : IsEmpty {w : Plc L // un w = v}` using `⟨fun w => hne w.1 w.2⟩`. Establish `h01` using `(rhoBij L P v).1 (a₁ := 0) (a₂ := 1) (funext fun w => (hE.false w).elim)`. Conclude with `zero_ne_one h01`.
-/
private theorem exists_over (P : Pre L) (v : Pl (Lp L)) : ∃ w : Plc L, un w = v := by
  by_contra hne
  push_neg at hne
  have hE : IsEmpty {w : Plc L // un w = v} := ⟨fun w => hne w.1 w.2⟩
  have h01 := (rhoBij L P v).1 (a₁ := 0) (a₂ := 1) (funext fun w => (hE.false w).elim)
  exact zero_ne_one h01

/- English proof (translation)
Rewrite using `[pLoc_conjFin, HeightOneSpectrum.mem_adicCompletionIntegers, (conjLoc_spec _ w).2.2]`. Conclude with `hA _`.
-/
private theorem conj_int (a : Af L) (hA : ∀ u : Plc L, pLoc L u a ∈ u.adicCompletionIntegers L) (w : Plc L) :
    pLoc L w (cjF a) ∈ w.adicCompletionIntegers L := by
  rw [pLoc_conjFin, HeightOneSpectrum.mem_adicCompletionIntegers, (conjLoc_spec _ w).2.2]
  exact hA _

/- English proof (translation)
Establish `hf : ∀ u : Plc L, (if h : un u = v then P.rho v u h x else 0) ∈ u.adicCompletionIntegers L` using `fun u => by`. Distinguish the cases in `hu : un u = v`. Rewrite using `[dif_pos hu]`. Conclude with `hx u hu`. Rewrite using `[dif_neg hu]`.

Conclude with `zero_mem _`. Set `a : Af L` to `⟨fun u => if h : un u = v then P.rho v u h x else 0, Filter.Eventually.of_forall hf⟩`. Establish `ha : ∀ w h, P.rho v w h x = pLoc L w a` using `fun w h => by show _ = dite _ _ _`. Rewrite using `[dif_pos h]`. Rewrite using `[rhoStar L P v x a ha w h]`.

Conclude with `conj_int a hf w`.
-/
private theorem star_int (P : Pre L) (v : Pl (Lp L)) (x : Lsq (Kv v) (cv v P.Δ))
    (hx : ∀ w h, P.rho v w h x ∈ w.adicCompletionIntegers L) (w : Plc L) (h : un w = v) :
    P.rho v w h (star x) ∈ w.adicCompletionIntegers L := by
  classical
  have hf : ∀ u : Plc L, (if h : un u = v then P.rho v u h x else 0) ∈ u.adicCompletionIntegers L := fun u => by
    by_cases hu : un u = v
    · rw [dif_pos hu]; exact hx u hu
    · rw [dif_neg hu]; exact zero_mem _
  let a : Af L := ⟨fun u => if h : un u = v then P.rho v u h x else 0, Filter.Eventually.of_forall hf⟩
  have ha : ∀ w h, P.rho v w h x = pLoc L w a := fun w h => by
    show _ = dite _ _ _
    rw [dif_pos h]
  rw [rhoStar L P v x a ha w h]
  exact conj_int a hf w

end UpperTheory.V.Z.Sym.Dict.Br

/- English proof (translation)
Introduce `L _ _ _ P v x`. Prove the components needed by the constructor for the conclusion. Introduce `hx w h`. Take `⟨p, hp, he⟩` from `hx`. Set `f : Ov v →+* w.adicCompletionIntegers L` to `((P.φ v w h).comp (algebraMap (Ov v) (Kv v))).codRestrict (w.adicCompletionIntegers L) fun a => (rhoDiv L P v w h _).2 a.2`.

Establish `hc : (P.rho v w h).comp (algebraMap (Ov v) (Lsq (Kv v) (cv v P.Δ))) = (algebraMap (w.adicCompletionIntegers L) (Kw w)).comp f`. Use `RingHom.ext fun a => ?_` and prove the remaining obligations. Conclude with `rho_coe P v w h _`. Establish `hi : IsIntegral (w.adicCompletionIntegers L) (P.rho v w h x)`. Use `⟨p.map f, hp.map f, ?_⟩` and prove the remaining obligations.

Rewrite using `[Polynomial.eval₂_map, ← hc, ← Polynomial.hom_eval₂, he, map_zero]`. Take `⟨y, hy⟩` from `IsIntegrallyClosed.isIntegral_iff.1 hi`. Rewrite using `[← hy]`. Conclude with `y.2`. Introduce `hx`.

Take `⟨w, h⟩` from `exists_over P v`. Establish `hs` using `star_int P v x hx w h`. Establish `ht : 2 * x.re ∈ v.adicCompletionIntegers (Lp L)`. Rewrite using `[← rhoDiv L P v w h, ← rho_coe P v w h]`. Establish `: (⟨2 * x.re, 0⟩ : Lsq (Kv v) (cv v P.Δ)) = x + star x`.

Apply the tactic sequence `apply QuadraticAlgebra.ext <;> simp [two_mul]`. Rewrite using `[this, map_add]`. Conclude with `add_mem (hx w h) hs`. Establish `hn : x.re * x.re - cv v P.Δ * (x.im * x.im) ∈ v.adicCompletionIntegers (Lp L)`. Rewrite using `[← rhoDiv L P v w h, ← rho_coe P v w h]`.

Establish `: (⟨x.re * x.re - cv v P.Δ * (x.im * x.im), 0⟩ : Lsq (Kv v) (cv v P.Δ)) = x * star x`. Apply the tactic sequence `apply QuadraticAlgebra.ext <;> simp <;> ring`. Rewrite using `[this, map_mul]`. Conclude with `mul_mem (hx w h) hs`. Set `t : Ov v` to `⟨_, ht⟩`.

Set `n : Ov v` to `⟨_, hn⟩`. Use `⟨Polynomial.X ^ 2 - (Polynomial.C t * Polynomial.X + Polynomial.C (-n)), Polynomial.monic_X_pow_sub (Polynomial.degree_linear_le.trans_lt (by norm_num)), ?_⟩` and prove the remaining obligations. Establish `e1 : algebraMap (Ov v) (Lsq (Kv v) (cv v P.Δ)) t = ⟨2 * x.re, 0⟩` using `rfl`. Establish `e2 : algebraMap (Ov v) (Lsq (Kv v) (cv v P.Δ)) (-n) = ⟨-(x.re * x.re - cv v P.Δ * (x.im * x.im)), 0⟩` using `rfl`. Simplify using `only [Polynomial.eval₂_sub, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, e1, e2]`.

Apply the tactic sequence `apply QuadraticAlgebra.ext <;> simp [pow_two] <;> ring`.
-/
theorem UpperTheory.V.Z.Sym.Dict.Br.rhoInt :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (P : Pre L), ∀ v (x : Lsq (Kv v) (cv v P.Δ)), IsIntegral (Ov v) x ↔ ∀ w h, P.rho v w h x ∈ w.adicCompletionIntegers L := by
  intro L _ _ _ P v x
  constructor
  · intro hx w h
    obtain ⟨p, hp, he⟩ := hx
    let f : Ov v →+* w.adicCompletionIntegers L :=
      ((P.φ v w h).comp (algebraMap (Ov v) (Kv v))).codRestrict (w.adicCompletionIntegers L)
        fun a => (rhoDiv L P v w h _).2 a.2
    have hc : (P.rho v w h).comp (algebraMap (Ov v) (Lsq (Kv v) (cv v P.Δ))) =
        (algebraMap (w.adicCompletionIntegers L) (Kw w)).comp f := by
      refine RingHom.ext fun a => ?_
      exact rho_coe P v w h _
    have hi : IsIntegral (w.adicCompletionIntegers L) (P.rho v w h x) := by
      refine ⟨p.map f, hp.map f, ?_⟩
      rw [Polynomial.eval₂_map, ← hc, ← Polynomial.hom_eval₂, he, map_zero]
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
    rw [← hy]
    exact y.2
  · intro hx
    obtain ⟨w, h⟩ := exists_over P v
    have hs := star_int P v x hx w h
    have ht : 2 * x.re ∈ v.adicCompletionIntegers (Lp L) := by
      rw [← rhoDiv L P v w h, ← rho_coe P v w h]
      have : (⟨2 * x.re, 0⟩ : Lsq (Kv v) (cv v P.Δ)) = x + star x := by
        apply QuadraticAlgebra.ext <;> simp [two_mul]
      rw [this, map_add]
      exact add_mem (hx w h) hs
    have hn : x.re * x.re - cv v P.Δ * (x.im * x.im) ∈ v.adicCompletionIntegers (Lp L) := by
      rw [← rhoDiv L P v w h, ← rho_coe P v w h]
      have : (⟨x.re * x.re - cv v P.Δ * (x.im * x.im), 0⟩ : Lsq (Kv v) (cv v P.Δ)) = x * star x := by
        apply QuadraticAlgebra.ext <;> simp <;> ring
      rw [this, map_mul]
      exact mul_mem (hx w h) hs
    let t : Ov v := ⟨_, ht⟩
    let n : Ov v := ⟨_, hn⟩
    refine ⟨Polynomial.X ^ 2 - (Polynomial.C t * Polynomial.X + Polynomial.C (-n)),
      Polynomial.monic_X_pow_sub (Polynomial.degree_linear_le.trans_lt (by norm_num)), ?_⟩
    have e1 : algebraMap (Ov v) (Lsq (Kv v) (cv v P.Δ)) t = ⟨2 * x.re, 0⟩ := rfl
    have e2 : algebraMap (Ov v) (Lsq (Kv v) (cv v P.Δ)) (-n) = ⟨-(x.re * x.re - cv v P.Δ * (x.im * x.im)), 0⟩ := rfl
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, e1, e2]
    apply QuadraticAlgebra.ext <;> simp [pow_two] <;> ring
