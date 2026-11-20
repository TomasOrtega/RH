import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.SphComm2
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.LocAlg
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.PositionTest
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.HintTranslate

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem heckeFunction_mul (a b : ℕ) (w : Pl E) (x y : Ex (Fin (a + 1) × Fin (b + 1))) :
    fn2 a b w (x.mul y) = PositivityTheory.Rg.BcN.F2.mconv (fn2 a b w x) (fn2 a b w y) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem heckeFunction_one (a b : ℕ) (w : Pl E) :
    fn2 a b w (.one : Ex (Fin (a + 1) × Fin (b + 1))) = (K2 a b w : Set _).indicator 1 := rfl

/- English proof (translation)
The claim follows from `UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.exHecke2 E a b w .one`.
-/
private theorem hecke_unit (a b : ℕ) (w : Pl E) :
    IsHecke (K2 a b w) (((K2 a b w : Subgroup _) : Set (GLw a w × GLw b w)).indicator (1 : GLw a w × GLw b w → ℂ)) :=
  UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.exHecke2 E a b w .one

/- English proof (translation)
Establish `L : Lv a b (∅ : Finset (Pl E))` using `⟨fun w => KGL w a, fun w => KGL w b, fun w => (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).1, fun w => (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).1, fun _ => le_rfl, fun _ => le_rfl, fun _ _ => ⟨rfl, rfl⟩⟩`. Conclude with `((locAlg E a b ∅ L w).2.2.2.2 f hf).1`.
-/
private theorem mconv_unit (a b : ℕ) (w : Pl E) {f : LF a b w} (hf : IsHecke (K2 a b w) f) :
    PositivityTheory.Rg.BcN.F2.mconv f ((K2 a b w : Set _).indicator 1) = f := by
  have L : Lv a b (∅ : Finset (Pl E)) := ⟨fun w => KGL w a, fun w => KGL w b,
    fun w => (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).1,
    fun w => (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).1, fun _ => le_rfl, fun _ => le_rfl,
    fun _ _ => ⟨rfl, rfl⟩⟩
  exact ((locAlg E a b ∅ L w).2.2.2.2 f hf).1

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => rfl`. Consider the case `succ k ih => show fn2 a b w (((.one : Ex (Fin (a + 1) × Fin (b + 1))).pow k).mul .one) = _`. Rewrite using `[heckeFunction_mul, ih, heckeFunction_one]`. Conclude with `mconv_unit a b w (hecke_unit a b w)`.
-/
private theorem heckeFunction_one_pow (a b : ℕ) (w : Pl E) (k : ℕ) :
    fn2 a b w ((.one : Ex (Fin (a + 1) × Fin (b + 1))).pow k) = (K2 a b w : Set _).indicator 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show fn2 a b w (((.one : Ex (Fin (a + 1) × Fin (b + 1))).pow k).mul .one) = _
    rw [heckeFunction_mul, ih, heckeFunction_one]
    exact mconv_unit a b w (hecke_unit a b w)

/- English proof (translation)
Introduce `E _ _ _ a b S Z L hZ φ T e₁ e₂ hφ hT`. Establish `hposition` using `positionTest E a b S Z L hZ`. Establish `hZw : ∀ w ∈ Z, seen φ L.ln w = φ w`. Introduce `w hw`. Use function extensionality and compare the values at `y`.

Establish `h` using `((locAlg E a b Z L w).2.2.2.1 (φ w) (hφ w hw)).1`. Simplify using `only [seen, if_pos (hZ w hw).2]`. Conclude with `congrFun h y`. Use `⟨hZw, fun k => ⟨⟨hT.1, fun w hw hs x => ?_⟩, ?_, ?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[Ex.ev_pow, hT.2 w hw hs]`.

Simplify using `[Ex.ev]`. Use function extensionality and compare the values at `w`. Distinguish the cases in `hwZ : w ∈ Z`. Establish `h` using `hZw w hwZ`. Use function extensionality and compare the values at `y`.

Establish `h'` using `congrFun h y`. Simplify using `only [seen, if_pos (hZ w hwZ).2, intersection_update_fsHerm_neg_one, fam, if_pos hwZ] at h' ⊢`. Conclude with `h'`. Distinguish the cases in `hwT : w ∈ T`. Distinguish the cases in `hs : IsSplitAt w`.

Use function extensionality and compare the values at `y`. Simplify using `only [seen, if_pos hs, intersection_update_fsHerm_neg_one, fam, if_neg hwZ, if_pos hwT]`. Both sides reduce to the same expression. Use function extensionality and compare the values at `y`. Simplify using `only [seen, if_neg hs, intersection_update_fsHerm_neg_one, fam, if_neg hwZ, if_pos hwT]`.

Rewrite using `[heckeFunction_mul, hT.2 w hwT hs, heckeFunction_one_pow, mconv_unit a b w (UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.exHecke2 E a b w _)]`. Distinguish the cases in `hs : IsSplitAt w`. Use function extensionality and compare the values at `y`. Simplify using `only [seen, if_pos hs, intersection_update_fsHerm_neg_one, fam, if_neg hwZ, if_neg hwT]`. Conclude with `congrFun (mconv_unit a b w (hecke_unit a b w)) y`.

Use function extensionality and compare the values at `y`. Simplify using `only [seen, if_neg hs, intersection_update_fsHerm_neg_one, fam, if_neg hwZ, if_neg hwT]`. Establish `h : fam Z T φ e₁ e₂ k = intersection_update_fsHerm_neg_one Z T φ fun w => ((e₁ w).pow k).mul ((e₂ w).pow k)`. Use function extensionality and compare the values at `w`. Simplify using `only [fam, intersection_update_fsHerm_neg_one]`.

Rewrite using `[h]`. Conclude with `(hposition.2.2 φ hφ).2 T _`. Use function extensionality and compare the values at `B₁ B₂`. Simplify using `only [UpperTheory.V.Z.Tf.GlobalTraceComparison.val, ev2, Ex.ev_pow, ← Finset.prod_pow, mul_pow]`.
-/
theorem seenFam : SeenFam := by
  intro E _ _ _ a b S Z L hZ φ T e₁ e₂ hφ hT
  have hposition := positionTest E a b S Z L hZ
  have hZw : ∀ w ∈ Z, seen φ L.ln w = φ w := by
    intro w hw
    funext y
    have h := ((locAlg E a b Z L w).2.2.2.1 (φ w) (hφ w hw)).1
    simp only [seen, if_pos (hZ w hw).2]
    exact congrFun h y
  refine ⟨hZw, fun k => ⟨⟨hT.1, fun w hw hs x => ?_⟩, ?_, ?_, ?_⟩⟩
  · rw [Ex.ev_pow, hT.2 w hw hs]
    simp [Ex.ev]
  · funext w
    by_cases hwZ : w ∈ Z
    · have h := hZw w hwZ
      funext y
      have h' := congrFun h y
      simp only [seen, if_pos (hZ w hwZ).2, intersection_update_fsHerm_neg_one, fam, if_pos hwZ] at h' ⊢
      exact h'
    · by_cases hwT : w ∈ T
      · by_cases hs : IsSplitAt w
        · funext y
          simp only [seen, if_pos hs, intersection_update_fsHerm_neg_one, fam, if_neg hwZ, if_pos hwT]
          rfl
        · funext y
          simp only [seen, if_neg hs, intersection_update_fsHerm_neg_one, fam, if_neg hwZ, if_pos hwT]
          rw [heckeFunction_mul, hT.2 w hwT hs, heckeFunction_one_pow, mconv_unit a b w (UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.exHecke2 E a b w _)]
      · by_cases hs : IsSplitAt w
        · funext y
          simp only [seen, if_pos hs, intersection_update_fsHerm_neg_one, fam, if_neg hwZ, if_neg hwT]
          exact congrFun (mconv_unit a b w (hecke_unit a b w)) y
        · funext y
          simp only [seen, if_neg hs, intersection_update_fsHerm_neg_one, fam, if_neg hwZ, if_neg hwT]
  · have h : fam Z T φ e₁ e₂ k = intersection_update_fsHerm_neg_one Z T φ fun w => ((e₁ w).pow k).mul ((e₂ w).pow k) := by
      funext w
      simp only [fam, intersection_update_fsHerm_neg_one]
    rw [h]
    exact (hposition.2.2 φ hφ).2 T _
  · funext B₁ B₂
    simp only [UpperTheory.V.Z.Tf.GlobalTraceComparison.val, ev2, Ex.ev_pow, ← Finset.prod_pow, mul_pow]

end UpperTheory.Zero.ConvolutionTheory.EB
