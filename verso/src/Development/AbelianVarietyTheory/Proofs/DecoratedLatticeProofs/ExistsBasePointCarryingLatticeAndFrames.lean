import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevAtZ
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNormalFramesAndBasePointSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualImageAdelicPointWittCoreStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacuaStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicIsometries
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FlatSpaceComponents
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlaceIdempotentActsOnSupportedAndOff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeCompletionAtPlacesMemCompletedHermitianLaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLatticeCompletionAtPlacesOfFinPartMemHatLattiStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CorrectionOfTransport
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumPowersUnramifiedEtaTilde
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.FinPl.BasePoint

variable {D : D7}

/- English proof (translation)
Take `⟨α, rfl, -, h0⟩` from `hε`. Take `⟨hinf, hcomp⟩` from `placeIdempotent_infinite_and_finite_components D v _ α rfl`. Rewrite using `[mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere]`. Use `⟨hinf, fun w hw => ?_⟩` and prove the remaining obligations. Rewrite using `[hcomp, h0 w hw, TensorProduct.zero_tmul]`.
-/
theorem algebraMap_placeIdem_mem {v : Pl D} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) :
    algebraMap (AF D.host.F) (AE D) ε ∈ idAt D (· = v) := by
  obtain ⟨α, rfl, -, h0⟩ := hε
  obtain ⟨hinf, hcomp⟩ := placeIdempotent_infinite_and_finite_components D v _ α rfl
  rw [mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere]
  refine ⟨hinf, fun w hw => ?_⟩
  rw [hcomp, h0 w hw, TensorProduct.zero_tmul]

/- English proof (translation)
Rewrite `ha`, the goal using `[mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere]`. Conclude with `⟨ha.1, fun w hw => ha.2 w (fun hp => hw (h w hp))⟩`.
-/
theorem idAt_mono {P Q : Pl D → Prop} (h : ∀ v, P v → Q v) {a : AE D} (ha : a ∈ idAt D P) : a ∈ idAt D Q := by
  rw [mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere] at ha ⊢
  exact ⟨ha.1, fun w hw => ha.2 w (fun hp => hw (h w hp))⟩

/- English proof (translation)
Introduce `i`. Simplify using `only [Matrix.mulVec, dotProduct]`. Conclude with `Ideal.sum_mem _ fun j _ => I.mul_mem_left _ (hy j)`.
-/
theorem mulVec_mem' {I : Ideal (AE D)} {m n : ℕ} (A : Matrix (Fin m) (Fin n) (AE D)) {y : Fin n → AE D}
    (hy : ∀ i, y i ∈ I) : ∀ i, (A *ᵥ y) i ∈ I := by
  intro i
  simp only [Matrix.mulVec, dotProduct]
  exact Ideal.sum_mem _ fun j _ => I.mul_mem_left _ (hy j)

/- English proof (translation)
Establish `hz : ∀ l, algebraMap (AF D.host.F) (AE D) ε * y l = 0` using `fun l => (placeIdem_acts D u ε hε).2 _ (idAt_mono (fun w hw => by rw [hw]; exact huv) (hy l))`. Establish `h1 : (mt V h - 1) *ᵥ y = 0`. Use extensionality with `i`. Simplify using `only [Matrix.mulVec, dotProduct, Pi.zero_apply]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← he, hs i j]`. Use `_ = (mt V h - 1) i j * (algebraMap (AF D.host.F) (AE D) ε * y j) := by ring`. Use `_ = 0 := by rw [hz j, mul_zero]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem mulVec_fix {V : HSp D} {e : AE D} {ε : AF D.host.F} {u v : Pl D} (hε : IsPlaceIdem D u ε)
    (he : e + cA D e = algebraMap (AF D.host.F) (AE D) ε) {h : GA D V} (hs : SuppAt e V h) (huv : v ≠ u)
    {y : Fin V.rank → AE D} (hy : ∀ l, y l ∈ idAt D (· = v)) : mt V h *ᵥ y = y := by
  have hz : ∀ l, algebraMap (AF D.host.F) (AE D) ε * y l = 0 := fun l =>
    (placeIdem_acts D u ε hε).2 _ (idAt_mono (fun w hw => by rw [hw]; exact huv) (hy l))
  have h1 : (mt V h - 1) *ᵥ y = 0 := by
    ext i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    calc (mt V h - 1) i j * y j = (algebraMap (AF D.host.F) (AE D) ε * (mt V h - 1) i j) * y j := by
          rw [← he, hs i j]
      _ = (mt V h - 1) i j * (algebraMap (AF D.host.F) (AE D) ε * y j) := by ring
      _ = 0 := by rw [hz j, mul_zero]
  calc mt V h *ᵥ y = ((mt V h - 1) + 1) *ᵥ y := by rw [sub_add_cancel]
    _ = y := by rw [Matrix.add_mulVec, h1, Matrix.one_mulVec, zero_add]

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

/- English proof (translation)
Rewrite using `[← q.sec_pr a, q.pr_sec]`.
-/
theorem pr_e_mul (q : SplitPt D k) (a : AE D) : q.pr (q.e * a) = q.pr a := by
  rw [← q.sec_pr a, q.pr_sec]

/- English proof (translation)
Rewrite using `[← he, mul_add, q.split.1, q.split.2.1, add_zero]`.
-/
theorem e_mul_eps (q : SplitPt D k) {ε : AF D.host.F} (he : q.e + cA D q.e = algebraMap (AF D.host.F) (AE D) ε) :
    q.e * algebraMap (AF D.host.F) (AE D) ε = q.e := by
  rw [← he, mul_add, q.split.1, q.split.2.1, add_zero]

/- English proof (translation)
Use `show (mt V h).map q.pr = 1`. Take `⟨ε, hε, he⟩` from `q.above`. Take `⟨ε', hε', he'⟩` from `q'.above`. Establish `h0 : q.pr (algebraMap (AF D.host.F) (AE D) ε') = 0`. Rewrite using `[← pr_e_mul, ← e_mul_eps q he, mul_assoc, (placeIdem_acts D q.v ε hε).2 _ (idAt_mono (fun w hw => by rw [hw]; exact Ne.symm hne) (algebraMap_placeIdem_mem hε')), mul_zero, map_zero]`.

Use extensionality with `i j`. Establish `hij` using `hs i j`. Rewrite `hij` using `[he']`. Establish `h1 : q.pr ((mt V h - 1) i j) = 0` using `by rw [← hij, map_mul, h0, zero_mul]`. Establish `e2 : (mt V h) i j = (mt V h - 1) i j + (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j` using `by simp`.

Rewrite using `[Matrix.map_apply, e2, map_add, h1, zero_add]`. Apply the tactic sequence `by_cases hij' : i = j <;> simp [Matrix.one_apply, hij']`.
-/
theorem map_mt_eq_one (q : SplitPt D k) (q' : SplitPt D k') (hne : q.v ≠ q'.v) {V : HSp D} {h : GA D V}
    (hs : SuppAt q'.e V h) : (mt V h).map (GlobalTheory.LocMod.ofSplit q).π = 1 := by
  show (mt V h).map q.pr = 1
  obtain ⟨ε, hε, he⟩ := q.above
  obtain ⟨ε', hε', he'⟩ := q'.above
  have h0 : q.pr (algebraMap (AF D.host.F) (AE D) ε') = 0 := by
    rw [← pr_e_mul, ← e_mul_eps q he, mul_assoc,
      (placeIdem_acts D q.v ε hε).2 _ (idAt_mono (fun w hw => by rw [hw]; exact Ne.symm hne)
        (algebraMap_placeIdem_mem hε')), mul_zero, map_zero]
  ext i j
  have hij := hs i j
  rw [he'] at hij
  have h1 : q.pr ((mt V h - 1) i j) = 0 := by rw [← hij, map_mul, h0, zero_mul]
  have e2 : (mt V h) i j = (mt V h - 1) i j + (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j := by simp
  rw [Matrix.map_apply, e2, map_add, h1, zero_add]
  by_cases hij' : i = j <;> simp [Matrix.one_apply, hij']

/- English proof (translation)
Unfold `GlobalTheory.LocMod.Place.xi GlobalTheory.LocMod.Place.pr`. Introduce `h0`. Establish `h1 : (GlobalTheory.LocMod.ofSplit q).π (incA D D.host.xi0) * (GlobalTheory.LocMod.ofSplit q).π (incA D D.host.xi0⁻¹) = 1`. Rewrite using `[← map_mul, ← map_mul, mul_inv_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), map_one, map_one]`. Rewrite `h1` using `[h0, zero_mul]`.

Conclude with `zero_ne_one h1`.
-/
theorem xi_ne (q : SplitPt D k) : (GlobalTheory.LocMod.ofSplit q).xi ≠ 0 := by
  unfold GlobalTheory.LocMod.Place.xi GlobalTheory.LocMod.Place.pr
  intro h0
  have h1 : (GlobalTheory.LocMod.ofSplit q).π (incA D D.host.xi0) * (GlobalTheory.LocMod.ofSplit q).π (incA D D.host.xi0⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), map_one, map_one]
  rw [h0, zero_mul] at h1
  exact zero_ne_one h1

/- English proof (translation)
Assemble the required witnesses or components as `⟨GlobalTheory.T.latticeCompletionAtPlaces_mem_completedHermitianLattice D S L P y, GlobalTheory.T.mem_latticeCompletionAtPlaces_of_finPart_mem_hatLattice D S L P y hy⟩`.
-/
theorem latV_iff_hat' (S : HSp D) (L : Lat S) (P : Pl D → Prop) (y : Fin S.rank → AE D) (hy : ∀ i, y i ∈ idAt D P) :
    y ∈ latV S L P ↔ (fun i => Formalism.IndefR.Lev.swapAE D (finPart D (y i))) ∈ GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.hat L :=
  ⟨GlobalTheory.T.latticeCompletionAtPlaces_mem_completedHermitianLattice D S L P y, GlobalTheory.T.mem_latticeCompletionAtPlaces_of_finPart_mem_hatLattice D S L P y hy⟩

/- English proof (translation)
Establish `h : ((Formalism.IndefR.Lev.finE S x).val) = (mt S x).map ((Formalism.IndefR.Lev.swapAE D).comp (finPart D))`. Use extensionality with `i j`. Both sides reduce to the same expression. Rewrite using `[h]`. Use extensionality with `i`.

Conclude with `RingHom.map_mulVec ((Formalism.IndefR.Lev.swapAE D).comp (finPart D)) (mt S x) y i`.
-/
theorem finE_mulVec' (S : HSp D) (x : GA D S) (y : Fin S.rank → AE D) :
    (fun i => Formalism.IndefR.Lev.swapAE D (finPart D ((mt S x *ᵥ y) i))) =
      (Formalism.IndefR.Lev.finE S x).val *ᵥ (fun i => Formalism.IndefR.Lev.swapAE D (finPart D (y i))) := by
  have h : ((Formalism.IndefR.Lev.finE S x).val) = (mt S x).map ((Formalism.IndefR.Lev.swapAE D).comp (finPart D)) := by
    ext i j
    rfl
  rw [h]
  ext i
  exact RingHom.map_mulVec ((Formalism.IndefR.Lev.swapAE D).comp (finPart D)) (mt S x) y i

/- English proof (translation)
Take `⟨t₀, ht₀, htr⟩` from `(GlobalTheory.AdIsom.adelicIsometries D).2.2.1 V V (LinearEquiv.refl _ _) (fun _ _ => rfl) Λ L₀ hΛ hL₀ ∅ (by intro w hw; simp at hw) 0 (fun _ => 0) (fun _ => 0) (by simp) (by simp)`. Rewrite `htr` using `[LinearEquiv.refl_toLinearMap, GlobalTheory.AdIsomCorrection.mA_id, Matrix.mul_one]`. Use `⟨t₀, ht₀, fun P y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[latV_iff_hat' V Λ P y hy, latV_iff_hat' V L₀ P _ (mulVec_mem' _ hy), finE_mulVec']`. Conclude with `htr.2.1 _`.
-/
theorem exists_base (V : HSp D) (Λ L₀ : Lat V) (hΛ : IsSelfDualC V Λ) (hL₀ : IsSelfDualC V L₀) :
    ∃ t₀ ∈ GfC V, ∀ P, Moves V t₀ Λ L₀ P := by
  obtain ⟨t₀, ht₀, htr⟩ := (GlobalTheory.AdIsom.adelicIsometries D).2.2.1 V V (LinearEquiv.refl _ _) (fun _ _ => rfl) Λ L₀ hΛ hL₀
    ∅ (by intro w hw; simp at hw) 0 (fun _ => 0) (fun _ => 0) (by simp) (by simp)
  rw [LinearEquiv.refl_toLinearMap, GlobalTheory.AdIsomCorrection.mA_id, Matrix.mul_one] at htr
  refine ⟨t₀, ht₀, fun P y hy => ?_⟩
  rw [latV_iff_hat' V Λ P y hy, latV_iff_hat' V L₀ P _ (mulVec_mem' _ hy), finE_mulVec']
  exact htr.2.1 _

variable {J : Type} [Fintype J] {kk : J → Type} [∀ i, Field (kk i)] [∀ i, ValuativeRel (kk i)]
  [∀ i, TopologicalSpace (kk i)] [∀ i, IsNonarchimedeanLocalField (kk i)]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Conclude with `⟨1, one_mem _, fun v _ y _ => by rw [mt_one, Matrix.one_mulVec], fun i hi => by simp at hi⟩`. Consider the case `insert j s hj ih`. Take `⟨g, hg, hfix, hmv⟩` from `ih`.

Take `⟨h, hsupp, hmove⟩` from `(GlobalTheory.T.exists_normal_frames_and_base_point_split_place D (kk j) (GlobalTheory.LocMod.ofSplit (q j)) (xi_ne (q j))).2.2 V β (M j) (g * t₀)`. Use `⟨h * g, mul_mem (GlobalTheory.WeilProduct.mem_GfC_of_suppAt (q j).split hsupp) hg, ?_, ?_⟩` and prove the remaining obligations. Introduce `v hv y hy`. Rewrite using `[mt_mul, ← Matrix.mulVec_mulVec, hfix v hv y hy]`. Take `⟨ε, hε, he⟩` from `(q j).above`.

Conclude with `mulVec_fix hε he hsupp (hv j) hy`. Introduce `i hi`. Rewrite `hi` using `[Finset.mem_insert]`. Break down `hi with rfl | hi` into its components or cases. Rewrite using `[mul_assoc]`.

Conclude with `hmove`. Introduce `b hb`. Establish `hij : (q i).v ≠ (q j).v` using `fun h' => hj (by rw [← (hinj h' : i = j)]; exact hi)`. Rewrite using `[mul_assoc, mt_mul, Matrix.mul_assoc, Matrix.map_mul, map_mt_eq_one (q i) (q j) hij hsupp, Matrix.one_mul]`. Conclude with `hmv i hi b hb`.
-/
theorem exists_corr (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (q : ∀ i, SplitPt D (kk i))
    (hinj : Function.Injective (fun i => (q i).v)) (M : ∀ i, GL (Fin V.rank) (kk i)) (t₀ : GA D V) (s : Finset J) :
    ∃ g ∈ GfC V, (∀ v, (∀ i, v ≠ (q i).v) → ∀ y : Fin V.rank → AE D, (∀ l, y l ∈ idAt D (· = v)) → mt V g *ᵥ y = y) ∧
      ∀ i ∈ s, GlobalTheory.LocMod.MovedTo (GlobalTheory.LocMod.ofSplit (q i)) V (g * t₀) β (M i).val := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨1, one_mem _, fun v _ y _ => by rw [mt_one, Matrix.one_mulVec], fun i hi => by simp at hi⟩
  | insert j s hj ih =>
    obtain ⟨g, hg, hfix, hmv⟩ := ih
    obtain ⟨h, hsupp, hmove⟩ :=
      (GlobalTheory.T.exists_normal_frames_and_base_point_split_place D (kk j) (GlobalTheory.LocMod.ofSplit (q j)) (xi_ne (q j))).2.2 V β (M j) (g * t₀)
    refine ⟨h * g, mul_mem (GlobalTheory.WeilProduct.mem_GfC_of_suppAt (q j).split hsupp) hg, ?_, ?_⟩
    · intro v hv y hy
      rw [mt_mul, ← Matrix.mulVec_mulVec, hfix v hv y hy]
      obtain ⟨ε, hε, he⟩ := (q j).above
      exact mulVec_fix hε he hsupp (hv j) hy
    · intro i hi
      rw [Finset.mem_insert] at hi
      rcases hi with rfl | hi
      · rw [mul_assoc]; exact hmove
      · intro b hb
        have hij : (q i).v ≠ (q j).v := fun h' => hj (by rw [← (hinj h' : i = j)]; exact hi)
        rw [mul_assoc, mt_mul, Matrix.mul_assoc, Matrix.map_mul, map_mt_eq_one (q i) (q j) hij hsupp, Matrix.one_mul]
        exact hmv i hi b hb

end GlobalTheory.FinPl.BasePoint

open GlobalTheory.FinPl.BasePoint in

/- English proof (translation)
Introduce `D V Λ L₀ β hΛ hL₀ J _ kk _ _ _ _ q hinj M`. Take `⟨t₀, ht₀, hmv₀⟩` from `exists_base V Λ L₀ hΛ hL₀`. Take `⟨g, hg, hfix, hmv⟩` from `exists_corr V β q hinj M t₀ Finset.univ`. Take `⟨L, hL, hmoves⟩` from `(GlobalTheory.T.selfDual_image_adelicPoint_wittCore D V Λ hΛ).1 (g * t₀)`. Use `⟨g * t₀, mul_mem hg ht₀, L, hL, hmoves, ?_, fun i => hmv i (Finset.mem_univ i)⟩` and prove the remaining obligations.

Introduce `v hv`. Use extensionality with `y`. Distinguish the cases in `hy : ∀ l, y l ∈ idAt D (· = v)`. Establish `hz : ∀ l, (mt V t₀⁻¹ *ᵥ y) l ∈ idAt D (· = v)` using `mulVec_mem' _ hy`. Establish `h1 : mt V t₀ *ᵥ (mt V t₀⁻¹ *ᵥ y) = y`.

Rewrite using `[Matrix.mulVec_mulVec, ← mt_mul, mul_inv_cancel, mt_one, Matrix.one_mulVec]`. Establish `h2 : mt V (g * t₀) *ᵥ (mt V t₀⁻¹ *ᵥ y) = y`. Rewrite using `[mt_mul, ← Matrix.mulVec_mulVec, h1, hfix v hv y hy]`. Establish `a1` using `hmoves (· = v) _ hz`. Establish `a2` using `hmv₀ (· = v) _ hz`.

Rewrite `a1` using `[h2]`. Rewrite `a2` using `[h1]`. Conclude with `a1.symm.trans a2`. Establish `hsupp : ∀ (N : Lat V), IsSelfDualC V N → y ∉ latV V N (· = v)` using `fun N hN hyN => hy (((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· = v)).2 V).2.2.2 N y hN.1 |>.1 hyN).1`. Conclude with `iff_of_false (hsupp L hL) (hsupp L₀ hL₀)`.
-/
theorem GlobalTheory.FinPl.BasePoint.exists_move : ∀ (D : D7) (V : HSp D) (Λ L₀ : Lat V) (β : GL (Fin V.rank) (Lev.EAf D)), IsSelfDualC V Λ → IsSelfDualC V L₀ → ∀ (J : Type) [Fintype J] (k : J → Type) [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)] [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)] (q : ∀ i, SplitPt D (k i)), Function.Injective (fun i => (q i).v) → ∀ M : ∀ i, GL (Fin V.rank) (k i), ∃ t ∈ GfC V, ∃ L : Lat V, IsSelfDualC V L ∧ (∀ P, Moves V t Λ L P) ∧ (∀ v, (∀ i, v ≠ (q i).v) → latV V L (· = v) = latV V L₀ (· = v)) ∧ ∀ i, GlobalTheory.LocMod.MovedTo (GlobalTheory.LocMod.ofSplit (q i)) V t β (M i).val := by
  intro D V Λ L₀ β hΛ hL₀ J _ kk _ _ _ _ q hinj M
  obtain ⟨t₀, ht₀, hmv₀⟩ := exists_base V Λ L₀ hΛ hL₀
  obtain ⟨g, hg, hfix, hmv⟩ := exists_corr V β q hinj M t₀ Finset.univ
  obtain ⟨L, hL, hmoves⟩ := (GlobalTheory.T.selfDual_image_adelicPoint_wittCore D V Λ hΛ).1 (g * t₀)
  refine ⟨g * t₀, mul_mem hg ht₀, L, hL, hmoves, ?_, fun i => hmv i (Finset.mem_univ i)⟩
  intro v hv
  ext y
  by_cases hy : ∀ l, y l ∈ idAt D (· = v)
  · have hz : ∀ l, (mt V t₀⁻¹ *ᵥ y) l ∈ idAt D (· = v) := mulVec_mem' _ hy
    have h1 : mt V t₀ *ᵥ (mt V t₀⁻¹ *ᵥ y) = y := by
      rw [Matrix.mulVec_mulVec, ← mt_mul, mul_inv_cancel, mt_one, Matrix.one_mulVec]
    have h2 : mt V (g * t₀) *ᵥ (mt V t₀⁻¹ *ᵥ y) = y := by
      rw [mt_mul, ← Matrix.mulVec_mulVec, h1, hfix v hv y hy]
    have a1 := hmoves (· = v) _ hz
    have a2 := hmv₀ (· = v) _ hz
    rw [h2] at a1
    rw [h1] at a2
    exact a1.symm.trans a2
  · have hsupp : ∀ (N : Lat V), IsSelfDualC V N → y ∉ latV V N (· = v) := fun N hN hyN =>
      hy (((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· = v)).2 V).2.2.2 N y hN.1 |>.1 hyN).1
    exact iff_of_false (hsupp L hL) (hsupp L₀ hL₀)
