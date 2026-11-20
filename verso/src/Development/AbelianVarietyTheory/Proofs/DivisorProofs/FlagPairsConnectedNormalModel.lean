import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Adj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalModelTrivializingBlowup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapDegreeFinitePullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPairConnectedNormalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernRootFlagPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPairPullDivisorClassStatement

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

namespace GlobalTheory.FlagPairChain

open GlobalTheory.Vert GlobalTheory.Vert.Model

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/- English proof (translation)
Proceed by induction on `h using Relation.ReflTransGen.head_induction_on with`. Consider the case `refl => exact ⟨0, fun _ => b, rfl, rfl, finZeroElim⟩`. Consider the case `@head a c hac _ ih`. Take `⟨m, g, rfl, h₂, h₃⟩` from `ih`. Conclude with `⟨m + 1, Fin.cons a g, rfl, h₂, Fin.cases hac h₃⟩`.
-/
theorem exists_seq {α : Type*} {R : α → α → Prop} {a b : α} (h : Relation.ReflTransGen R a b) :
    ∃ (m : ℕ) (g : Fin (m + 1) → α), g 0 = a ∧ g (Fin.last m) = b ∧
      ∀ j : Fin m, R (g j.castSucc) (g j.succ) := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, fun _ => b, rfl, rfl, finZeroElim⟩
  | @head a c hac _ ih =>
    obtain ⟨m, g, rfl, h₂, h₃⟩ := ih
    exact ⟨m + 1, Fin.cons a g, rfl, h₂, Fin.cases hac h₃⟩

/- English proof (translation)
Simplify using `only [ck, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `hG : Gk (B'.toITh p) k ((B'.toITh p).c1 (((GlobalTheory.FlagPairExists.pairPull f.comp_str P).toFPair p).x i)) ((B'.toITh p).c1 (((GlobalTheory.FlagPairExists.pairPull f.comp_str P).toFPair p).x' i)) = picSymPull f.f (Gk (B.toITh p) k ((B.toITh p).c1 ((P.toFPair p).x i)) ((B.toIT …`. Simplify using `only [Gk, map_sum, map_mul, map_pow]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `c1 _ _ ^ a * c1 _ _ ^ _ = picSymPull f.f (c1 _ _) ^ a * picSymPull f.f (c1 _ _) ^ _`. Rewrite using `[← GlobalTheory.T.chern_root_flag_pullback _ _ f.f _ _ P.fl i, ← GlobalTheory.T.chern_root_flag_pullback _ _ f.f _ _ P.fl' i]`. Both sides reduce to the same expression. Rewrite using `[hG, ← map_mul]`. Express the relevant statement in the definitionally equal form `B'.capDeg_vp p (toQ ((GlobalTheory.FlagPairExists.pairPull f.comp_str P).div i).cls) _ = _ * B.capDeg_vp p (toQ (P.div i).cls) _`.

Rewrite using `[GlobalTheory.T.flag_pair_pull_divisor_class, ← vPullQ_toQ, hproj]`.
-/
theorem ck_pairPull (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p]
    {B B' : Model O} (f : Hom B' B)
    (hproj : ∀ (d : B.VDivQ) (Q : PicSym B.X), B'.capDeg_vp p (vPullQ f.comp_str d)
      (picSymPull f.f Q) = f.fibreDeg 1 * B.capDeg_vp p d Q)
    {E E' : B.X.Modules} {φ : B.GenIso E E'} {r : ℕ} (P : FlagPair φ r) (k : ℕ)
    (Q : PicSym B.X) :
    ck ((GlobalTheory.FlagPairExists.pairPull f.comp_str P).toFPair p) k (picSymPull f.f Q) =
      f.fibreDeg 1 * ck (P.toFPair p) k Q := by
  simp only [ck, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hG : Gk (B'.toITh p) k
      ((B'.toITh p).c1 (((GlobalTheory.FlagPairExists.pairPull f.comp_str P).toFPair p).x i))
      ((B'.toITh p).c1 (((GlobalTheory.FlagPairExists.pairPull f.comp_str P).toFPair p).x' i)) =
      picSymPull f.f (Gk (B.toITh p) k ((B.toITh p).c1 ((P.toFPair p).x i))
        ((B.toITh p).c1 ((P.toFPair p).x' i))) := by
    simp only [Gk, map_sum, map_mul, map_pow]
    refine Finset.sum_congr rfl fun a _ => ?_
    change c1 _ _ ^ a * c1 _ _ ^ _ = picSymPull f.f (c1 _ _) ^ a * picSymPull f.f (c1 _ _) ^ _
    rw [← GlobalTheory.T.chern_root_flag_pullback _ _ f.f _ _ P.fl i, ← GlobalTheory.T.chern_root_flag_pullback _ _ f.f _ _ P.fl' i]
    rfl
  rw [hG, ← map_mul]
  change B'.capDeg_vp p (toQ ((GlobalTheory.FlagPairExists.pairPull f.comp_str P).div i).cls) _ =
    _ * B.capDeg_vp p (toQ (P.div i).cls) _
  rw [GlobalTheory.T.flag_pair_pull_divisor_class, ← vPullQ_toQ, hproj]

end GlobalTheory.FlagPairChain

/- English proof (translation)
Introduce `O _ _ _ p _ _ _ B hB E E' φ r P P'`. Take `⟨B', f, hB', hf, hj⟩` from `GlobalTheory.T.flag_pair_connected_normal O p B hB E E' φ r P P'`. Take `⟨hpos, hproj⟩` from `GlobalTheory.T.cap_degree_finite_pullback O p B hB B' f hf`. Take `⟨m, g, h₀, h₁, h₂⟩` from `GlobalTheory.FlagPairChain.exists_seq hj`. Use `⟨B', f, m, g, hB', hf, hpos, fun k Q => ?_, fun k Q => ?_, h₂⟩` and prove the remaining obligations.

Rewrite using `[h₀]`. Conclude with `GlobalTheory.FlagPairChain.ck_pairPull p f hproj P k Q`. Rewrite using `[h₁]`. Conclude with `GlobalTheory.FlagPairChain.ck_pairPull p f hproj P' k Q`.
-/
theorem GlobalTheory.FlagPairChain.exists_chain_flagPair : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X → ∀ (E E' : B.X.Modules) (φ : B.GenIso E E') (r : ℕ) (P P' : GlobalTheory.Vert.Model.FlagPair φ r), ∃ (B' : GlobalTheory.Vert.Model O) (f : GlobalTheory.Vert.Model.Hom B' B) (m : ℕ) (g : Fin (m + 1) → GlobalTheory.Vert.Model.FlagPair (φ.pull f.comp_str) r), GlobalTheory.IsNormalScheme B'.X ∧ f.relDim = 0 ∧ 0 < f.fibreDeg 1 ∧ (∀ (k : ℕ) (Q : PicSym B.X), ck ((g 0).toFPair p) k (picSymPull f.f Q) = f.fibreDeg 1 * ck (P.toFPair p) k Q) ∧ (∀ (k : ℕ) (Q : PicSym B.X), ck ((g (Fin.last m)).toFPair p) k (picSymPull f.f Q) = f.fibreDeg 1 * ck (P'.toFPair p) k Q) ∧ ∀ j : Fin m, GlobalTheory.Vert.Model.FlagPair.Adj (g j.castSucc) (g j.succ) := by
  intro O _ _ _ p _ _ _ B hB E E' φ r P P'
  obtain ⟨B', f, hB', hf, hj⟩ := GlobalTheory.T.flag_pair_connected_normal O p B hB E E' φ r P P'
  obtain ⟨hpos, hproj⟩ := GlobalTheory.T.cap_degree_finite_pullback O p B hB B' f hf
  obtain ⟨m, g, h₀, h₁, h₂⟩ := GlobalTheory.FlagPairChain.exists_seq hj
  refine ⟨B', f, m, g, hB', hf, hpos, fun k Q => ?_, fun k Q => ?_, h₂⟩
  · rw [h₀]; exact GlobalTheory.FlagPairChain.ck_pairPull p f hproj P k Q
  · rw [h₁]; exact GlobalTheory.FlagPairChain.ck_pairPull p f hproj P' k Q
