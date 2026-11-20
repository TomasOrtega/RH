import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LocalMajorantConvergence
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RealDoublingNormStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MatrixEntryNormSumUpperRightBlockElementPLe
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.MeasUpq
import Formalism.LocalRingCardinality.SpanPowerMembership.SignSplitEquivInl
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SignFrameUnitaryIsoStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SingularValuesSubmatrixStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CartanOffBlockSubmatrixStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.IndefiniteRowSideFullHecke.LocalMajorantConvergence

noncomputable section
namespace GlobalTheory.RealHeight

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hcm n J hJ w b hb m hm s hs`. Take `⟨ε, hε⟩` from `hb`. Take `⟨τ⟩` from `(inferInstance : Nonempty (EmbOver E w))`. Establish `hDA` using `(GlobalTheory.T.real_doubling_norm).2 F E σ hcm n J hJ _ rfl w τ ε b hε`. Take `⟨Θ, hΘ⟩` from `GlobalTheory.T.sign_frame_unitary_iso F E σ hcm n J w τ ε b hε`.

Take `⟨i1, i2, i3, i4, i5, -⟩` from `GlobalTheory.UpqTopology.upq_lcsc (Formalism.BasicNotions.Examples₂.CD.nT ε) (Formalism.BasicNotions.Examples₂.CD.nF ε)`. Establish `hpq : Formalism.BasicNotions.Examples₂.CD.nT ε + Formalism.BasicNotions.Examples₂.CD.nF ε = n`. Simplify using `using Fintype.card_congr (Formalism.BasicNotions.Examples₂.CD.e0 ε)`. Establish `hrank : GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.realRank ε = min (Formalism.BasicNotions.Examples₂.CD.nT ε) (Formalism.BasicNotions.Examples₂.CD.nF ε)`. Unfold `GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.realRank Formalism.BasicNotions.Examples₂.CD.nT Formalism.BasicNotions.Examples₂.CD.nF`.

Use `congr 1`. Conclude with `Fintype.card_congr (Equiv.subtypeEquivRight (fun i => by simp))`. Establish `key : ∀ g : GArch σ J w, ((hgtH σ (dblGram finSumFinEquiv J) (absEw F E w) (KArch σ (dblGram finSumFinEquiv J) w b) (ioH w.Completion σ (rfl : dblGram finSumFinEquiv J = _) (g, 1)) : ℝ≥0) : ℝ) ^ (s + (n : ℝ) / 2) = GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower.coshPow ( …`. Introduce `g`. Take `⟨X, hX, hoff⟩` from `GlobalTheory.T.cartan_off_block_submatrix n ε (Θ g)`.

Rewrite `hX` using `[← hΘ g]`. Establish `h1` using `((hDA g).2.2.2 X hX).1`. Establish `hcp : GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.coshProd ε X = ∏ i ∈ Finset.range (min (Formalism.BasicNotions.Examples₂.CD.nT ε) (Formalism.BasicNotions.Examples₂.CD.nF ε)), Real.cosh (GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower.singVal (Glob …`. Unfold `GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.coshProd`. Rewrite using `[hrank]`.

Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Unfold `GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.singVal GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower.singVal`. Rewrite using `[hoff]`. Use `congr 1`. Conclude with `DFunLike.congr_fun (GlobalTheory.T.singular_values_submatrix _ _ _ _ _ _ _) i`.

Establish `hpos : 0 < GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.coshProd ε X` using `lt_of_lt_of_le one_pos (GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.one_le_coshProd ε X)`. Express the relevant statement in the definitionally equal form `((hgtArch σ (dblGram finSumFinEquiv J) w b (ioH w.Completion σ rfl (g, 1)) : ℝ≥0) : ℝ) ^ _ = _`. Rewrite using `[h1, GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower.coshPow, Real.finset_prod_rpow _ _ (fun i _ => (Real.cosh_pos _).le), ← hcp, Real.inv_rpow (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hpos.le, Real.rpow_neg hpos.le]`. Use `congr 2`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨m0, hm0⟩` from `Formalism.IndefR.Eqv.MU.isMinf_exists (Formalism.BasicNotions.Examples₂.CD.nT ε) (Formalism.BasicNotions.Examples₂.CD.nF ε)`. Establish `hint0 : Integrable (GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower.coshPow (2 * s + n)) m0` using `GlobalTheory.CartanInt.coshIntegral.1 _ _ m0 hm0 _ (by`. Establish `: ((Formalism.BasicNotions.Examples₂.CD.nT ε + Formalism.BasicNotions.Examples₂.CD.nF ε : ℕ) : ℝ) = n` using `by exact_mod_cast hpq`. Rewrite using `[this]`.

Use the proof step `linarith)`. Use `haveI := hm0.1`. Use `haveI : (m.map Θ).IsHaarMeasure := Θ.isHaarMeasure_map m`. Establish `e` using `Measure.isMulLeftInvariant_eq_smul (m.map Θ) m0`. Establish `hint1 : Integrable (GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower.coshPow (2 * s + n)) (m.map Θ)`.

Rewrite using `[e]`. Conclude with `hint0.smul_measure_nnreal`. Establish `hint2 : Integrable (GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower.coshPow (2 * s + n) ∘ Θ) m` using `(integrable_map_equiv Θ.toHomeomorph.toMeasurableEquiv _).1 hint1`. Unfold `HeightConv`. Use `hint2.congr (Filter.Eventually.of_forall fun g => ?_)` and prove the remaining obligations.

Conclude with `(key g).symm`.
-/
theorem heightConv_real : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (w : InfinitePlace F) (b : GL (Fin n) (w.Completion ⊗[F] E)), IsMajorantAt σ J w b → ∀ m : Measure (GArch σ J w), m.IsHaarMeasure → ∀ s : ℝ, (n : ℝ) / 2 - 1 < s → HeightConv σ (rfl : dblGram finSumFinEquiv J = _) (absEw F E w) (KArch σ (dblGram finSumFinEquiv J) w b) m s := by
  intro F E _ _ _ _ _ σ hcm n J hJ w b hb m hm s hs
  obtain ⟨ε, hε⟩ := hb
  obtain ⟨τ⟩ := (inferInstance : Nonempty (EmbOver E w))
  have hDA := (GlobalTheory.T.real_doubling_norm).2 F E σ hcm n J hJ _ rfl w τ ε b hε
  obtain ⟨Θ, hΘ⟩ := GlobalTheory.T.sign_frame_unitary_iso F E σ hcm n J w τ ε b hε
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.UpqTopology.upq_lcsc (Formalism.BasicNotions.Examples₂.CD.nT ε) (Formalism.BasicNotions.Examples₂.CD.nF ε)
  have hpq : Formalism.BasicNotions.Examples₂.CD.nT ε + Formalism.BasicNotions.Examples₂.CD.nF ε = n := by
    simpa using Fintype.card_congr (Formalism.BasicNotions.Examples₂.CD.e0 ε)
  have hrank : GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.realRank ε = min (Formalism.BasicNotions.Examples₂.CD.nT ε) (Formalism.BasicNotions.Examples₂.CD.nF ε) := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.realRank Formalism.BasicNotions.Examples₂.CD.nT Formalism.BasicNotions.Examples₂.CD.nF
    congr 1
    exact Fintype.card_congr (Equiv.subtypeEquivRight (fun i => by simp))
  have key : ∀ g : GArch σ J w, ((hgtH σ (dblGram finSumFinEquiv J) (absEw F E w) (KArch σ (dblGram finSumFinEquiv J) w b)
      (ioH w.Completion σ (rfl : dblGram finSumFinEquiv J = _) (g, 1)) : ℝ≥0) : ℝ) ^ (s + (n : ℝ) / 2) =
      GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower.coshPow (2 * s + n) (Θ g) := by
    intro g
    obtain ⟨X, hX, hoff⟩ := GlobalTheory.T.cartan_off_block_submatrix n ε (Θ g)
    rw [← hΘ g] at hX
    have h1 := ((hDA g).2.2.2 X hX).1
    have hcp : GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.coshProd ε X = ∏ i ∈ Finset.range (min (Formalism.BasicNotions.Examples₂.CD.nT ε) (Formalism.BasicNotions.Examples₂.CD.nF ε)),
        Real.cosh (GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower.singVal (GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower.cartanB (Θ g)) i) := by
      unfold GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.coshProd
      rw [hrank]
      refine Finset.prod_congr rfl fun i _ => ?_
      unfold GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.singVal GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower.singVal
      rw [hoff]
      congr 1
      exact DFunLike.congr_fun (GlobalTheory.T.singular_values_submatrix _ _ _ _ _ _ _) i
    have hpos : 0 < GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.coshProd ε X := lt_of_lt_of_le one_pos (GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.one_le_coshProd ε X)
    change ((hgtArch σ (dblGram finSumFinEquiv J) w b (ioH w.Completion σ rfl (g, 1)) : ℝ≥0) : ℝ) ^ _ = _
    rw [h1, GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower.coshPow, Real.finset_prod_rpow _ _ (fun i _ => (Real.cosh_pos _).le), ← hcp,
      Real.inv_rpow (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hpos.le, Real.rpow_neg hpos.le]
    congr 2
    push_cast; ring
  obtain ⟨m0, hm0⟩ := Formalism.IndefR.Eqv.MU.isMinf_exists (Formalism.BasicNotions.Examples₂.CD.nT ε) (Formalism.BasicNotions.Examples₂.CD.nF ε)
  have hint0 : Integrable (GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower.coshPow (2 * s + n)) m0 :=
    GlobalTheory.CartanInt.coshIntegral.1 _ _ m0 hm0 _ (by
      have : ((Formalism.BasicNotions.Examples₂.CD.nT ε + Formalism.BasicNotions.Examples₂.CD.nF ε : ℕ) : ℝ) = n := by exact_mod_cast hpq
      rw [this]; linarith)
  haveI := hm0.1
  haveI : (m.map Θ).IsHaarMeasure := Θ.isHaarMeasure_map m
  have e := Measure.isMulLeftInvariant_eq_smul (m.map Θ) m0
  have hint1 : Integrable (GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower.coshPow (2 * s + n)) (m.map Θ) := by
    rw [e]; exact hint0.smul_measure_nnreal
  have hint2 : Integrable (GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower.coshPow (2 * s + n) ∘ Θ) m :=
    (integrable_map_equiv Θ.toHomeomorph.toMeasurableEquiv _).1 hint1
  unfold HeightConv
  refine hint2.congr (Filter.Eventually.of_forall fun g => ?_)
  exact (key g).symm

end GlobalTheory.RealHeight
