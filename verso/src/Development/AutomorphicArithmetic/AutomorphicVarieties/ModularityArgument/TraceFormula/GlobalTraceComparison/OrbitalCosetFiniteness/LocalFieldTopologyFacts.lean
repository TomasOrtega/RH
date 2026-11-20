import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.OrbitalCosetFiniteness.CvGelfandAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.CvHecke
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.HintTranslate

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8 UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Th

/- English proof (translation)
Establish `R` using `hRing (GLw a w × GLw b w) (K2 a b w) hO hC`. Establish `L` using `hLin (GLw a w × GLw b w) (K2 a b w) hO hC (th2 a b w) hk y hy`. Establish `W` using `hTw (GLw a w × GLw b w) (K2 a b w) hO hC (th2 a b w) hc hi hk y hy`. Establish `V` using `cvHecke (GLw a w × GLw b w) (K2 a b w) hO hC`. Establish `X : ∀ x, IsHecke (K2 a b w) (fn2 a b w x)` using `exHecke2 E a b w`.

Establish `H1 : IsHecke (K2 a b w) ((K2 a b w : Set (GLw a w × GLw b w)).indicator 1)` using `X .one`. Proceed by induction on `he with`. Consider the case `one`. Introduce `h hh`. Establish `e1 : cv (K2 a b w) h (fn2 a b w .one) = h` using `(R h h h hh hh hh).2.1`.

Rewrite using `[e1]`. Consider the case `step c p`. Introduce `h hh`. Establish `HT : IsHecke (K2 a b w) (gen2 a b w (Fin.last a, Fin.last b))` using `X (.gen _)`. Establish `HP : IsHecke (K2 a b w) (gen2 a b w p)` using `X (.gen _)`.

Establish `HR : IsHecke (K2 a b w) (gen2 a b w (p.1.rev, p.2.rev))` using `X (.gen _)`. Establish `HPθ` using `(W _ _ HP HP).1`. Establish `HhT` using `V h _ hh HT`. Establish `HTP` using `V _ _ HT HP`. Establish `e1 : cv (K2 a b w) h (fn2 a b w (dEx p)) = fun y => cv (K2 a b w) h (cv (K2 a b w) (gen2 a b w (Fin.last a, Fin.last b)) (gen2 a b w p)) y + (-1) * cv (K2 a b w) h (gen2 a b w (p.1.rev, p.2.rev)) y`.

Use `(R h _ _ hh HTP HR).2.2.2 1 (-1)` as an intermediate fact. Simplify using `only [one_mul] at this`. Conclude with `this`. Establish `e2 : cv (K2 a b w) h (cv (K2 a b w) (gen2 a b w (Fin.last a, Fin.last b)) (gen2 a b w p)) = cv (K2 a b w) (gen2 a b w p) (cv (K2 a b w) h (gen2 a b w (Fin.last a, Fin.last b)))`. Rewrite using `[← (R h _ _ hh HT HP).1]`.

Conclude with `hComm E a b w _ _ HhT HP`. Establish `e3 : twOrb (th2 a b w) (K2 a b w) y (cv (K2 a b w) (gen2 a b w p) (cv (K2 a b w) h (gen2 a b w (Fin.last a, Fin.last b)))) = twOrb (th2 a b w) (K2 a b w) y (cv (K2 a b w) h (gen2 a b w (p.1.rev, p.2.rev)))`. Rewrite using `[(W _ _ HP HhT).2, (R h _ _ hh HT HPθ).1, hGen E hUnr a b w hw p]`. Establish `e4 : twOrb (th2 a b w) (K2 a b w) y (cv (K2 a b w) h (fn2 a b w (dEx p))) = 0`. Rewrite using `[e1, L _ _ (-1) (V h _ hh HTP) (V h _ hh HR), e2, e3]`.

Expand and normalize the polynomial expressions, which then agree. Establish `e5 : cv (K2 a b w) h (fn2 a b w (.add .one (.smul c (dEx p)))) = fun y => h y + c * cv (K2 a b w) h (fn2 a b w (dEx p)) y`. Use `(R h _ _ hh H1 (X (dEx p))).2.2.2 1 c` as an intermediate fact. Rewrite `this` using `[(R h h h hh hh hh).2.1]`. Simplify using `only [one_mul] at this`.

Conclude with `this`. Rewrite using `[e5, L _ _ c hh (V h _ hh (X _)), e4, mul_zero, add_zero]`. Consider the case `@mul x z _ _ ihx ihz`. Introduce `h hh`. Establish `e1 : cv (K2 a b w) h (fn2 a b w (.mul x z)) = cv (K2 a b w) (cv (K2 a b w) h (fn2 a b w x)) (fn2 a b w z)` using `((R h _ _ hh (X x) (X z)).1).symm`.

Rewrite using `[e1, ihz _ (V h _ hh (X x)), ihx h hh]`.
-/
private theorem orbit_unitary_compact_open {E : Type} [Field E] [NumberField E] [IsCMField E]
    (hTw : TwSwap) (hLin : TwLin) (hRing : CvRing) (hComm : CvComm2) (hGen : GenTw)
    (hUnr : GlobalTheory.BCT.Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (a b : ℕ)
    (hc : Continuous (th2 a b w)) (hi : ∀ x, th2 a b w (th2 a b w x) = x)
    (hk : ∀ k ∈ K2 a b w, th2 a b w k ∈ K2 a b w)
    (hO : IsOpen (K2 a b w : Set (GLw a w × GLw b w)))
    (hC : IsCompact (K2 a b w : Set (GLw a w × GLw b w)))
    (y : GLw a w × GLw b w) (hy : OrbFin (th2 a b w) (K2 a b w) y)
    {e : Ex (Fin (a + 1) × Fin (b + 1))} (he : U1 e) :
    ∀ h, IsHecke (K2 a b w) h →
      twOrb (th2 a b w) (K2 a b w) y (cv (K2 a b w) h (fn2 a b w e)) = twOrb (th2 a b w) (K2 a b w) y h := by
  have R := hRing (GLw a w × GLw b w) (K2 a b w) hO hC
  have L := hLin (GLw a w × GLw b w) (K2 a b w) hO hC (th2 a b w) hk y hy
  have W := hTw (GLw a w × GLw b w) (K2 a b w) hO hC (th2 a b w) hc hi hk y hy
  have V := cvHecke (GLw a w × GLw b w) (K2 a b w) hO hC
  have X : ∀ x, IsHecke (K2 a b w) (fn2 a b w x) := exHecke2 E a b w
  have H1 : IsHecke (K2 a b w) ((K2 a b w : Set (GLw a w × GLw b w)).indicator 1) := X .one
  induction he with
  | one =>
    intro h hh
    have e1 : cv (K2 a b w) h (fn2 a b w .one) = h := (R h h h hh hh hh).2.1
    rw [e1]
  | step c p =>
    intro h hh
    have HT : IsHecke (K2 a b w) (gen2 a b w (Fin.last a, Fin.last b)) := X (.gen _)
    have HP : IsHecke (K2 a b w) (gen2 a b w p) := X (.gen _)
    have HR : IsHecke (K2 a b w) (gen2 a b w (p.1.rev, p.2.rev)) := X (.gen _)
    have HPθ := (W _ _ HP HP).1
    have HhT := V h _ hh HT
    have HTP := V _ _ HT HP

    have e1 : cv (K2 a b w) h (fn2 a b w (dEx p)) = fun y =>
        cv (K2 a b w) h (cv (K2 a b w) (gen2 a b w (Fin.last a, Fin.last b)) (gen2 a b w p)) y +
          (-1) * cv (K2 a b w) h (gen2 a b w (p.1.rev, p.2.rev)) y := by
      have := (R h _ _ hh HTP HR).2.2.2 1 (-1)
      simp only [one_mul] at this
      exact this
    have e2 : cv (K2 a b w) h (cv (K2 a b w) (gen2 a b w (Fin.last a, Fin.last b)) (gen2 a b w p)) =
        cv (K2 a b w) (gen2 a b w p) (cv (K2 a b w) h (gen2 a b w (Fin.last a, Fin.last b))) := by
      rw [← (R h _ _ hh HT HP).1]
      exact hComm E a b w _ _ HhT HP
    have e3 : twOrb (th2 a b w) (K2 a b w) y
        (cv (K2 a b w) (gen2 a b w p) (cv (K2 a b w) h (gen2 a b w (Fin.last a, Fin.last b)))) =
        twOrb (th2 a b w) (K2 a b w) y (cv (K2 a b w) h (gen2 a b w (p.1.rev, p.2.rev))) := by
      rw [(W _ _ HP HhT).2, (R h _ _ hh HT HPθ).1, hGen E hUnr a b w hw p]
    have e4 : twOrb (th2 a b w) (K2 a b w) y (cv (K2 a b w) h (fn2 a b w (dEx p))) = 0 := by
      rw [e1, L _ _ (-1) (V h _ hh HTP) (V h _ hh HR), e2, e3]
      ring

    have e5 : cv (K2 a b w) h (fn2 a b w (.add .one (.smul c (dEx p)))) =
        fun y => h y + c * cv (K2 a b w) h (fn2 a b w (dEx p)) y := by
      have := (R h _ _ hh H1 (X (dEx p))).2.2.2 1 c
      rw [(R h h h hh hh hh).2.1] at this
      simp only [one_mul] at this
      exact this
    rw [e5, L _ _ c hh (V h _ hh (X _)), e4, mul_zero, add_zero]
  | @mul x z _ _ ihx ihz =>
    intro h hh
    have e1 : cv (K2 a b w) h (fn2 a b w (.mul x z)) =
        cv (K2 a b w) (cv (K2 a b w) h (fn2 a b w x)) (fn2 a b w z) :=
      ((R h _ _ hh (X x) (X z)).1).symm
    rw [e1, ihz _ (V h _ hh (X x)), ihx h hh]

/- English proof (translation)
Introduce `hTw hLin hRing hComm hTh hGen E _ _ _ hUnr w hw a b e he Q₁ Q₂ s₁ s₂`. Take `⟨hc, hi, hk, hfin⟩` from `hTh E hUnr a b w hw`. Establish `hO : IsOpen (K2 a b w : Set (GLw a w × GLw b w))` using `(GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).1.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).1`. Establish `hC : IsCompact (K2 a b w : Set (GLw a w × GLw b w))` using `(GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).2.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).2`. Establish `H1 : IsHecke (K2 a b w) ((K2 a b w : Set (GLw a w × GLw b w)).indicator 1)` using `exHecke2 E a b w .one`.

Establish `HE : IsHecke (K2 a b w) (fn2 a b w e)` using `exHecke2 E a b w e`. Unfold `stTw2 clSum`. Use `finsum_congr fun q => ?_` and prove the remaining obligations. Distinguish the cases in `hS : q.rep ∈ {y : GLw a w × GLw b w | (nrmL a w y.1).val.charpoly = Q₁ ∧ (nrmL b w y.2).val.charpoly = Q₂}`. Rewrite using `[if_pos hS, if_pos hS]`.

Establish `h1 : (nrmL a w q.rep.1).val.charpoly = Q₁` using `hS.1`. Establish `h2 : (nrmL b w q.rep.2).val.charpoly = Q₂` using `hS.2`. Establish `hy` using `hfin q.rep (h1 ▸ s₁) (h2 ▸ s₂)`. Establish `key` using `orbit_unitary_compact_open hTw hLin hRing hComm hGen hUnr w hw a b hc hi hk hO hC q.rep hy he _ H1`. Rewrite `key` using `[((hRing _ (K2 a b w) hO hC) _ _ _ HE HE HE).2.2.1]`.

Conclude with `congrArg _ key`. Rewrite using `[if_neg hS, if_neg hS]`.
-/
theorem stUnit_of :
    TwSwap → TwLin → CvRing → CvComm2 → Th2 → GenTw → UpperTheory.V.Z.Tf.GlobalTraceComparison.StUnit := by
  intro hTw hLin hRing hComm hTh hGen E _ _ _ hUnr w hw a b e he Q₁ Q₂ s₁ s₂
  obtain ⟨hc, hi, hk, hfin⟩ := hTh E hUnr a b w hw
  have hO : IsOpen (K2 a b w : Set (GLw a w × GLw b w)) :=
    (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).1.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).1
  have hC : IsCompact (K2 a b w : Set (GLw a w × GLw b w)) :=
    (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).2.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).2
  have H1 : IsHecke (K2 a b w) ((K2 a b w : Set (GLw a w × GLw b w)).indicator 1) := exHecke2 E a b w .one
  have HE : IsHecke (K2 a b w) (fn2 a b w e) := exHecke2 E a b w e
  unfold stTw2 clSum
  refine finsum_congr fun q => ?_
  by_cases hS : q.rep ∈ {y : GLw a w × GLw b w | (nrmL a w y.1).val.charpoly = Q₁ ∧ (nrmL b w y.2).val.charpoly = Q₂}
  · rw [if_pos hS, if_pos hS]
    have h1 : (nrmL a w q.rep.1).val.charpoly = Q₁ := hS.1
    have h2 : (nrmL b w q.rep.2).val.charpoly = Q₂ := hS.2
    have hy := hfin q.rep (h1 ▸ s₁) (h2 ▸ s₂)
    have key := orbit_unitary_compact_open hTw hLin hRing hComm hGen hUnr w hw a b hc hi hk hO hC q.rep hy he _ H1
    rw [((hRing _ (K2 a b w) hO hC) _ _ _ HE HE HE).2.2.1] at key
    exact congrArg _ key
  · rw [if_neg hS, if_neg hS]

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Th
