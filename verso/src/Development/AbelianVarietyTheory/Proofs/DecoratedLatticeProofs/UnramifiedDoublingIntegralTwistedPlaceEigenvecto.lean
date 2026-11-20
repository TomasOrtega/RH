import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType
import Formalism.LocalToGlobal.Columns.HeckeSp
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCompactParahoric
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasSumBilateral
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerBlockCoefficientIsSphericalHeckeEigenStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiInvariantEigenfunctionEqMulZonalSphericalStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TwistedPlaceDoubleCosetVolumeAndDisjointStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralBiInvariantHasSumDoubleCoset
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepChainStepMatrixCoefficientTwistedStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SupportParahoricBiTransformingDoubleCosets
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SupportParahoricBiTransformingDoubleCosetsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedDoublingSumGLConvergentLValueStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainStepIdentities
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsUnramifiedHeightFunctionLowerBlockStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricHeckeGenericEigenvalueMapMulStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedTwistSphericalFunctionReindexStatement

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section

namespace GlobalTheory.TwistedZeta

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def cellFun (r l t : ℕ) (ϖ : kˣ) (v : (Fin (l * t) → ℤ) → ℂ) (g : GL (Fin r ⊕ Blocks l t) k) : ℂ :=
  ∑' e : {e : Fin (l * t) → ℤ // Antitone e},
    (dcell ϖ (e.1 ∘ (blkEquiv l t).symm) : Set (GL (Fin r ⊕ Blocks l t) k)).indicator (fun _ => v e.1) g

/- English proof (translation)
Unfold `cellFun`. Rewrite using `[tsum_eq_single e]`. Conclude with `Set.indicator_of_mem hg _`. Introduce `e' he'`. Conclude with `Set.indicator_of_notMem (Set.disjoint_left.1 (hdisj he'.symm) hg) _`.
-/
theorem cellFun_of_mem {r l t : ℕ} {ϖ : kˣ} (v : (Fin (l * t) → ℤ) → ℂ)
    (hdisj : Pairwise (Function.onFun Disjoint fun e : {e : Fin (l * t) → ℤ // Antitone e} =>
      (dcell ϖ (e.1 ∘ (blkEquiv l t).symm) : Set (GL (Fin r ⊕ Blocks l t) k))))
    (e : {e : Fin (l * t) → ℤ // Antitone e}) {g : GL (Fin r ⊕ Blocks l t) k}
    (hg : g ∈ dcell ϖ (e.1 ∘ (blkEquiv l t).symm)) : cellFun r l t ϖ v g = v e.1 := by
  unfold cellFun
  rw [tsum_eq_single e]
  · exact Set.indicator_of_mem hg _
  · intro e' he'
    exact Set.indicator_of_notMem (Set.disjoint_left.1 (hdisj he'.symm) hg) _

/- English proof (translation)
Unfold `cellFun`. Simplify using `[Set.indicator_of_notMem (hg _)]`.
-/
theorem cellFun_of_notMem {r l t : ℕ} {ϖ : kˣ} (v : (Fin (l * t) → ℤ) → ℂ) {g : GL (Fin r ⊕ Blocks l t) k}
    (hg : ∀ e : {e : Fin (l * t) → ℤ // Antitone e}, g ∉ dcell ϖ (e.1 ∘ (blkEquiv l t).symm)) :
    cellFun r l t ϖ v g = 0 := by
  unfold cellFun
  simp [Set.indicator_of_notMem (hg _)]

/- English proof (translation)
Unfold `dcell`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨a, ha, b, hb, e⟩` from `DoubleCoset.mem_doubleCoset.1 h`. Use `DoubleCoset.mem_doubleCoset.2 ⟨j⁻¹ * a, mul_mem (inv_mem hj) ha, b * j'⁻¹, mul_mem hb (inv_mem hj'), ?_⟩` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Introduce `h`. Take `⟨a, ha, b, hb, rfl⟩` from `DoubleCoset.mem_doubleCoset.1 h`. Conclude with `DoubleCoset.mem_doubleCoset.2 ⟨j * a, mul_mem hj ha, b * j', mul_mem hb hj', by group⟩`.
-/
theorem mem_dcell_mul_iff {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] {ϖ : kˣ}
    {f : D → ℤ} {g j j' : GL (A ⊕ D) k} (hj : j ∈ parahoric k A D) (hj' : j' ∈ parahoric k A D) :
    j * g * j' ∈ dcell ϖ f ↔ g ∈ dcell ϖ f := by
  unfold dcell
  constructor
  · intro h
    obtain ⟨a, ha, b, hb, e⟩ := DoubleCoset.mem_doubleCoset.1 h
    refine DoubleCoset.mem_doubleCoset.2 ⟨j⁻¹ * a, mul_mem (inv_mem hj) ha, b * j'⁻¹, mul_mem hb (inv_mem hj'), ?_⟩
    calc g = j⁻¹ * (j * g * j') * j'⁻¹ := by group
      _ = _ := by rw [e]; group
  · intro h
    obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.1 h
    exact DoubleCoset.mem_doubleCoset.2 ⟨j * a, mul_mem hj ha, b * j', mul_mem hb hj', by group⟩

/- English proof (translation)
Unfold `cellFun`. Use `congr 1`. Use function extensionality and compare the values at `e`. Distinguish the cases in `h : g ∈ dcell ϖ (e.1 ∘ (blkEquiv l t).symm)`. Rewrite using `[Set.indicator_of_mem h, Set.indicator_of_mem ((mem_dcell_mul_iff hj hj').2 h)]`.

Rewrite using `[Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h ((mem_dcell_mul_iff hj hj').1 h'))]`.
-/
theorem cellFun_biinv {r l t : ℕ} {ϖ : kˣ} (v : (Fin (l * t) → ℤ) → ℂ) (g : GL (Fin r ⊕ Blocks l t) k)
    {j j' : GL (Fin r ⊕ Blocks l t) k} (hj : j ∈ parahoric k (Fin r) (Blocks l t))
    (hj' : j' ∈ parahoric k (Fin r) (Blocks l t)) : cellFun r l t ϖ v (j * g * j') = cellFun r l t ϖ v g := by
  unfold cellFun
  congr 1
  funext e
  by_cases h : g ∈ dcell ϖ (e.1 ∘ (blkEquiv l t).symm)
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((mem_dcell_mul_iff hj hj').2 h)]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h ((mem_dcell_mul_iff hj hj').1 h'))]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[val_torusElt, Matrix.one_apply, diagonal_apply]`.
-/
theorem torusElt_zero {n : Type} [Fintype n] [DecidableEq n] (ϖ : kˣ) : torusElt k n ϖ 0 = 1 := by
  ext i j
  simp [val_torusElt, Matrix.one_apply, diagonal_apply]

/- English proof (translation)
Rewrite using `[mtor, Sum.elim_zero_zero, torusElt_zero]`.
-/
theorem mtor_zero {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) :
    (mtor ϖ (0 : D → ℤ) : GL (A ⊕ D) k) = 1 := by
  rw [mtor, Sum.elim_zero_zero, torusElt_zero]

/- English proof (translation)
Unfold `sumAbs`. Conclude with `Equiv.sum_comp ε.symm (fun i => |e i|)`.
-/
theorem sumAbs_comp {N : ℕ} {D : Type} [Fintype D] (ε : Fin N ≃ D) (e : Fin N → ℤ) :
    sumAbs (e ∘ ε.symm) = sumAbs e := by
  unfold sumAbs
  exact Equiv.sum_comp ε.symm (fun i => |e i|)

/- English proof (translation)
Simplify using `[sumAbs, Fintype.sum_sum_type]`.
-/
theorem sumAbs_elim {A D : Type} [Fintype A] [Fintype D] (e : D → ℤ) :
    sumAbs (Sum.elim (0 : A → ℤ) e) = sumAbs e := by
  simp [sumAbs, Fintype.sum_sum_type]

/- English proof (translation)
Use `ext`. Rewrite using `[GeneralLinearGroup.val_det_apply, val_torusElt, det_diagonal]`. Proceed by induction on `(Finset.univ : Finset n) using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, _root_.zpow_add, Units.val_mul, ih, Units.val_zpow_eq_zpow_val ϖ (e i)]`.
-/
theorem det_torusElt {n : Type} [Fintype n] [DecidableEq n] (ϖ : kˣ) (e : n → ℤ) :
    GeneralLinearGroup.det (torusElt k n ϖ e) = ϖ ^ ∑ i, e i := by
  ext
  rw [GeneralLinearGroup.val_det_apply, val_torusElt, det_diagonal]
  induction (Finset.univ : Finset n) using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, _root_.zpow_add, Units.val_mul, ih, Units.val_zpow_eq_zpow_val ϖ (e i)]

/- English proof (translation)
Establish `h1 : ψ 1 = 1`. Establish `hb : (1 : GL (Fin N) k) ∈ borel k (Fin N)` using `(mem_borel _).2 fun i j hij => by`. Simplify using `[Matrix.one_apply, (ne_of_lt hij).symm]`. Rewrite using `[hψ.2 1 hb (fun _ => 1) (fun i => by simp)]`. Establish `: ord k 1 = 0`.

Use `ord_mul k 1 1` as an intermediate fact. Simplify using `at this`. Conclude with `this`. Simplify using `[this]`. Establish `hK : ∀ κ ∈ (KO k (Fin N) : Set (GL (Fin N) k)), ψ (κ * 1) = 1` using `fun κ hκ => by`.

Rewrite using `[mul_one, ← one_mul κ, hψ.1 1 κ hκ, h1]`. Unfold `zonalInt`. Rewrite using `[setIntegral_congr_fun (SplitFlip.isOpen_KO.measurableSet) hK]`. Simplify using `[Measure.real, hμK]`.
-/
theorem zonalInt_one {N : ℕ} [MeasurableSpace (GL (Fin N) k)] [BorelSpace (GL (Fin N) k)] (μK : Measure (GL (Fin N) k))
    (hμK : μK (KO k (Fin N)) = 1) {γ : Fin N → ℂ} {ψ : GL (Fin N) k → ℂ} (hψ : IsBorelSph k γ ψ) :
    zonalInt μK ψ 1 = 1 := by
  have h1 : ψ 1 = 1 := by
    have hb : (1 : GL (Fin N) k) ∈ borel k (Fin N) := (mem_borel _).2 fun i j hij => by
      simp [Matrix.one_apply, (ne_of_lt hij).symm]
    rw [hψ.2 1 hb (fun _ => 1) (fun i => by simp)]
    have : ord k 1 = 0 := by
      have := ord_mul k 1 1
      simp at this
      exact this
    simp [this]
  have hK : ∀ κ ∈ (KO k (Fin N) : Set (GL (Fin N) k)), ψ (κ * 1) = 1 := fun κ hκ => by
    rw [mul_one, ← one_mul κ, hψ.1 1 κ hκ, h1]
  unfold zonalInt
  rw [setIntegral_congr_fun (SplitFlip.isOpen_KO.measurableSet) hK]
  simp [Measure.real, hμK]

/- English proof (translation)
The claim follows from `GlobalTheory.T.isUnramifiedHeightFunction_lowerBlock`.
-/
theorem hgt_lower : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) (H : GL (A ⊕ D) k → ℝ),
    IsHgt ϖ H → IsHgt ϖ (fun m : GL D k => H (emb₂ k (Equiv.refl (A ⊕ D)) (1, m))) :=
  GlobalTheory.T.isUnramifiedHeightFunction_lowerBlock

/- English proof (translation)
The claim follows from `GlobalTheory.T.parahoricHeckeGenericEigenvalue_map_mul`.
-/
theorem genVal_map_mul : ∀ (q r N n : ℕ) (B : Multiset ℂˣ) (c : ℂˣ),
    genVal q r N (B.map (· * c)) n = (c : ℂ) ^ n * genVal q r N B n :=
  GlobalTheory.T.parahoricHeckeGenericEigenvalue_map_mul

/- English proof (translation)
The claim follows from `GlobalTheory.T.unramifiedTwist_sphericalFunction_reindex`.
-/
theorem twist_transport : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (D : Type) [Fintype D] [DecidableEq D] (N : ℕ) (ε : Fin N ≃ D) (ϖ : kˣ),
    valuation k (ϖ : k) = uniformizer k → ∀ (μ₀ : kˣ →* ℂˣ), IsUnram μ₀ → ∀ (β : Multiset ℂˣ) (f : GL D k → ℂ),
    (∀ κ ∈ KO k D, ∀ m, f (κ * m) = f m ∧ f (m * κ) = f m) →
    (∀ (s : Finset D) R, IsRepsK (torusElt k D ϖ (indic s)) R → ∀ m,
      ∑ g ∈ R, f (m * g) = genVal (resCard k) 0 (Fintype.card D) β s.card * f m) →
    ∀ f₂ : GL (Fin N) k → ℂ, (∀ m, f₂ m = (((μ₀ (GeneralLinearGroup.det m))⁻¹ : ℂˣ) : ℂ) *
      f (GlobalTheory.ChainStepSupp.reGL k ε m)) →
    (∀ κ ∈ KO k (Fin N), ∀ m, f₂ (κ * m) = f₂ m ∧ f₂ (m * κ) = f₂ m) ∧
    ∀ (s : Finset (Fin N)) R, IsRepsK (torusElt k (Fin N) ϖ (indic s)) R → ∀ m,
      ∑ g ∈ R, f₂ (m * g) = (((μ₀ ϖ)⁻¹ : ℂˣ) : ℂ) ^ s.card * genVal (resCard k) 0 N β s.card * f₂ m :=
  GlobalTheory.T.unramifiedTwist_sphericalFunction_reindex

/- English proof (translation)
Introduce `k _ _ _ _ ϖ hϖ r l t ξ μ₀ hξt hξr hμ₀ B α hαB H hH _ μK ψ hψ V _ _ π x ℓ hx hℓ e`. Establish `hH'` using `hgt_lower k (Fin r) (Blocks l t) ϖ H hH`. Use `set H' : GL (Blocks l t) k → ℝ := fun m => H (emb₂ k (Equiv.refl (Fin r ⊕ Blocks l t)) (1, m)) with hH'def`. Use `set f : GL (Blocks l t) k → ℂ := fun m => (((ξ (GeneralLinearGroup.det m))⁻¹ : ℂˣ) : ℂ) * ℓ (π (emb₂ k (Equiv.refl (Fin r ⊕ Blocks l t)) (1, m)) x) / ((Real.sqrt (H' m) : ℝ) : ℂ) ^ Fintype.card (Fin r) with hfdef`. Take `⟨hfK, hfH⟩` from `GlobalTheory.T.lowerBlockCoefficient_isSphericalHeckeEigen k (Fin r) (Blocks l t) ϖ hϖ ξ hξt hξr V π B x ℓ hx hℓ H' hH' f (fun m => rfl)`.

Use `set f₂ : GL (Fin (l * t)) k → ℂ := fun m => (((μ₀ (GeneralLinearGroup.det m))⁻¹ : ℂˣ) : ℂ) * f (GlobalTheory.ChainStepSupp.reGL k (blkEquiv l t) m) with hf₂def`. Take `⟨hf₂K, hf₂H⟩` from `twist_transport k (Blocks l t) (l * t) (blkEquiv l t) ϖ hϖ μ₀ hμ₀ (B.map (· * (ξ ϖ)⁻¹)) f hfK hfH f₂ (fun m => rfl)`. Establish `hα : Finset.univ.val.map α = (B.map (· * (ξ ϖ)⁻¹)).map (· * (μ₀ ϖ)⁻¹)`. Rewrite using `[hαB, Multiset.map_map]`. Use `congr 1`.

Use function extensionality and compare the values at `b`. Simplify using `only [Function.comp, MonoidHom.mul_apply, _root_.mul_inv_rev]`. Rewrite using `[mul_assoc, mul_comm (ξ ϖ)⁻¹]`. Establish `hz` using `hψ f₂ hf₂K (fun s R hR m => by rw [hf₂H s R hR m, hα, genVal_map_mul _ _ _ _ _ (μ₀ ϖ)⁻¹])`. Establish `hval` using `hz (torusElt k (Fin (l * t)) ϖ e)`.

Establish `hq : (0:ℝ) < resCard k` using `by exact_mod_cast (zero_lt_one.trans (one_lt_resCard k))`. Establish `hf₂1 : f₂ 1 = ℓ x`. Establish `h1 : H' 1 = 1`. Use `hH'.2 0` as an intermediate fact. Rewrite `this` using `[torusElt_zero]`.

Rewrite using `[this]`. Simplify using `[sumAbs]`. Establish `he1 : emb₂ k (Equiv.refl (Fin r ⊕ Blocks l t)) ((1 : GL (Fin r) k), (1 : GL (Blocks l t) k)) = 1` using `map_one _`. Simplify using `only [hf₂def, hfdef, map_one, h1, Real.sqrt_one, he1]`. Simplify using the standard rewrite rules.

Establish `hS : ((Real.sqrt (H' (torusElt k (Blocks l t) ϖ (e ∘ (blkEquiv l t).symm))) : ℝ) : ℂ) ^ Fintype.card (Fin r) = (((resCard k : ℝ) ^ (-(r : ℝ) / 2 * (sumAbs e : ℝ)) : ℝ) : ℂ)`. Rewrite using `[hH'.2, sumAbs_comp, Fintype.card_fin, ← Complex.ofReal_pow]`. Use `congr 1`. Rewrite using `[Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_mul hq.le, ← Real.rpow_natCast, ← Real.rpow_mul hq.le]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hsum : ∑ i, (e ∘ (blkEquiv l t).symm) i = ∑ i, e i` using `Equiv.sum_comp (blkEquiv l t).symm e`. Establish `hval' : f₂ (torusElt k (Fin (l * t)) ϖ e) = (((μ₀ ϖ : ℂˣ) : ℂ) ^ (∑ i, e i))⁻¹ * ((((ξ ϖ : ℂˣ) : ℂ) ^ (∑ i, e i))⁻¹ * ℓ (π (mtor ϖ (e ∘ (blkEquiv l t).symm)) x) / (((resCard k : ℝ) ^ (-(r : ℝ) / 2 * (sumAbs e : ℝ)) : ℝ) : ℂ))`. Simplify using `only [hf₂def, hfdef]`.

Rewrite using `[GlobalTheory.ChainStepSupp.reGL_torusElt, GlobalTheory.ChainStepSupp.emb₂_one_torusElt, hS, det_torusElt, det_torusElt, hsum]`. Simplify using `[map_zpow, Units.val_zpow_eq_zpow_val]`. Establish `key` using `hval'.symm.trans (hval.trans (by rw [hf₂1]))`. Establish `hA : ((μ₀ ϖ : ℂˣ) : ℂ) ≠ 0` using `Units.ne_zero _`. Establish `hB : ((ξ ϖ : ℂˣ) : ℂ) ≠ 0` using `Units.ne_zero _`.

Establish `hSne : (((resCard k : ℝ) ^ (-(r : ℝ) / 2 * (sumAbs e : ℝ)) : ℝ) : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos hq _).ne'`. Rewrite using `[MonoidHom.mul_apply, Units.val_mul, mul_zpow]`. Establish `alg : ∀ (X Y S L : ℂ), X ≠ 0 → Y ≠ 0 → S ≠ 0 → L = X * Y * S * (X⁻¹ * (Y⁻¹ * L / S))`. Introduce `X Y S L hX hY hS`. Clear the denominators using the available nonvanishing facts.

Establish `hAn` using `zpow_ne_zero (∑ i, e i) hA`. Establish `hBn` using `zpow_ne_zero (∑ i, e i) hB`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem lower_eigen : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k →
  ∀ (r l t : ℕ) (ξ μ₀ : kˣ →* ℂˣ), IsTame ξ → ¬ IsUnram ξ → IsUnram μ₀ →
  ∀ (B : Multiset ℂˣ) (α : Fin (l * t) → ℂˣ), Finset.univ.val.map α = B.map (· * ((μ₀ * ξ) ϖ)⁻¹) →
  ∀ H : GL (Fin r ⊕ Blocks l t) k → ℝ, IsHgt ϖ H →
  ∀ [MeasurableSpace (GL (Fin (l * t)) k)] (μK : Measure (GL (Fin (l * t)) k)) (ψ : GL (Fin (l * t)) k → ℂ),
  (∀ f : GL (Fin (l * t)) k → ℂ, (∀ κ ∈ KO k (Fin (l * t)), ∀ m, f (κ * m) = f m ∧ f (m * κ) = f m) →
    (∀ (s : Finset (Fin (l * t))) R, IsRepsK (torusElt k (Fin (l * t)) ϖ (indic s)) R → ∀ m,
      ∑ g ∈ R, f (m * g) = genVal (resCard k) 0 (l * t) (Finset.univ.val.map α) s.card * f m) →
    ∀ m, f m = f 1 * zonalInt μK ψ m) →
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin r ⊕ Blocks l t) k) V) (x : V)
    (ℓ : V →ₗ[ℂ] ℂ), IsGen π ξ ϖ B x → IsCoType π ξ ℓ → ∀ e : Fin (l * t) → ℤ,
  ℓ (π (mtor ϖ (e ∘ (blkEquiv l t).symm)) x) = (((μ₀ * ξ) ϖ : ℂˣ) : ℂ) ^ (∑ i, e i) *
    (((resCard k : ℝ) ^ (-(r : ℝ) / 2 * (sumAbs e : ℝ)) : ℝ) : ℂ) * zonalInt μK ψ (torusElt k (Fin (l * t)) ϖ e) * ℓ x := by
  intro k _ _ _ _ ϖ hϖ r l t ξ μ₀ hξt hξr hμ₀ B α hαB H hH _ μK ψ hψ V _ _ π x ℓ hx hℓ e
  classical
  have hH' := hgt_lower k (Fin r) (Blocks l t) ϖ H hH
  set H' : GL (Blocks l t) k → ℝ := fun m => H (emb₂ k (Equiv.refl (Fin r ⊕ Blocks l t)) (1, m)) with hH'def
  set f : GL (Blocks l t) k → ℂ := fun m => (((ξ (GeneralLinearGroup.det m))⁻¹ : ℂˣ) : ℂ) *
    ℓ (π (emb₂ k (Equiv.refl (Fin r ⊕ Blocks l t)) (1, m)) x) / ((Real.sqrt (H' m) : ℝ) : ℂ) ^ Fintype.card (Fin r)
    with hfdef
  obtain ⟨hfK, hfH⟩ := GlobalTheory.T.lowerBlockCoefficient_isSphericalHeckeEigen k (Fin r) (Blocks l t) ϖ hϖ ξ hξt hξr V π B x ℓ hx hℓ H' hH' f (fun m => rfl)
  set f₂ : GL (Fin (l * t)) k → ℂ := fun m => (((μ₀ (GeneralLinearGroup.det m))⁻¹ : ℂˣ) : ℂ) *
    f (GlobalTheory.ChainStepSupp.reGL k (blkEquiv l t) m) with hf₂def
  obtain ⟨hf₂K, hf₂H⟩ := twist_transport k (Blocks l t) (l * t) (blkEquiv l t) ϖ hϖ μ₀ hμ₀
    (B.map (· * (ξ ϖ)⁻¹)) f hfK hfH f₂ (fun m => rfl)
  have hα : Finset.univ.val.map α = (B.map (· * (ξ ϖ)⁻¹)).map (· * (μ₀ ϖ)⁻¹) := by
    rw [hαB, Multiset.map_map]
    congr 1
    funext b
    simp only [Function.comp, MonoidHom.mul_apply, _root_.mul_inv_rev]
    rw [mul_assoc, mul_comm (ξ ϖ)⁻¹]
  have hz := hψ f₂ hf₂K (fun s R hR m => by rw [hf₂H s R hR m, hα, genVal_map_mul _ _ _ _ _ (μ₀ ϖ)⁻¹])
  have hval := hz (torusElt k (Fin (l * t)) ϖ e)

  have hq : (0:ℝ) < resCard k := by exact_mod_cast (zero_lt_one.trans (one_lt_resCard k))
  have hf₂1 : f₂ 1 = ℓ x := by
    have h1 : H' 1 = 1 := by
      have := hH'.2 0
      rw [torusElt_zero] at this
      rw [this]; simp [sumAbs]
    have he1 : emb₂ k (Equiv.refl (Fin r ⊕ Blocks l t)) ((1 : GL (Fin r) k), (1 : GL (Blocks l t) k)) = 1 := map_one _
    simp only [hf₂def, hfdef, map_one, h1, Real.sqrt_one, he1]
    simp
  have hS : ((Real.sqrt (H' (torusElt k (Blocks l t) ϖ (e ∘ (blkEquiv l t).symm))) : ℝ) : ℂ) ^ Fintype.card (Fin r) =
      (((resCard k : ℝ) ^ (-(r : ℝ) / 2 * (sumAbs e : ℝ)) : ℝ) : ℂ) := by
    rw [hH'.2, sumAbs_comp, Fintype.card_fin, ← Complex.ofReal_pow]
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_mul hq.le, ← Real.rpow_natCast, ← Real.rpow_mul hq.le]
    congr 1
    push_cast; ring
  have hsum : ∑ i, (e ∘ (blkEquiv l t).symm) i = ∑ i, e i := Equiv.sum_comp (blkEquiv l t).symm e
  have hval' : f₂ (torusElt k (Fin (l * t)) ϖ e) = (((μ₀ ϖ : ℂˣ) : ℂ) ^ (∑ i, e i))⁻¹ *
      ((((ξ ϖ : ℂˣ) : ℂ) ^ (∑ i, e i))⁻¹ * ℓ (π (mtor ϖ (e ∘ (blkEquiv l t).symm)) x) /
        (((resCard k : ℝ) ^ (-(r : ℝ) / 2 * (sumAbs e : ℝ)) : ℝ) : ℂ)) := by
    simp only [hf₂def, hfdef]
    rw [GlobalTheory.ChainStepSupp.reGL_torusElt, GlobalTheory.ChainStepSupp.emb₂_one_torusElt, hS, det_torusElt, det_torusElt, hsum]
    simp [map_zpow, Units.val_zpow_eq_zpow_val]
  have key := hval'.symm.trans (hval.trans (by rw [hf₂1]))
  have hA : ((μ₀ ϖ : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hB : ((ξ ϖ : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hSne : (((resCard k : ℝ) ^ (-(r : ℝ) / 2 * (sumAbs e : ℝ)) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos hq _).ne'
  rw [MonoidHom.mul_apply, Units.val_mul, mul_zpow]
  have alg : ∀ (X Y S L : ℂ), X ≠ 0 → Y ≠ 0 → S ≠ 0 → L = X * Y * S * (X⁻¹ * (Y⁻¹ * L / S)) := by
    intro X Y S L hX hY hS; field_simp
  have hAn := zpow_ne_zero (∑ i, e i) hA
  have hBn := zpow_ne_zero (∑ i, e i) hB
  calc ℓ (π (mtor ϖ (e ∘ (blkEquiv l t).symm)) x)
      = ((μ₀ ϖ : ℂˣ) : ℂ) ^ (∑ i, e i) * ((ξ ϖ : ℂˣ) : ℂ) ^ (∑ i, e i) *
          (((resCard k : ℝ) ^ (-(r : ℝ) / 2 * (sumAbs e : ℝ)) : ℝ) : ℂ) *
          ((((μ₀ ϖ : ℂˣ) : ℂ) ^ (∑ i, e i))⁻¹ * ((((ξ ϖ : ℂˣ) : ℂ) ^ (∑ i, e i))⁻¹ *
            ℓ (π (mtor ϖ (e ∘ (blkEquiv l t).symm)) x) / (((resCard k : ℝ) ^ (-(r : ℝ) / 2 * (sumAbs e : ℝ)) : ℝ) : ℂ))) :=
        alg _ _ _ _ hAn hBn hSne
    _ = _ := by rw [key]; ring

/- English proof (translation)
Introduce `hUD k _ _ _ _ _ _ _ ν hν ϖ hϖ r t l ξ μ₀ hξu hξt hξr hμ₀ hμ₀u B α ρ hαB hαρ H hH _ _ m _ hm c hc`. Use `letI : MeasurableSpace (GL (Fin (l * t)) k) := borel _`. Use `haveI : BorelSpace (GL (Fin (l * t)) k) := ⟨rfl⟩`. Take `⟨μK, hμKH, hμK⟩` from `GlobalTheory.GLDoubling.Model.exists_haar (k := k) (l * t)`. Use `haveI := hμKH`.

Take `⟨ψ, hψB, hψ⟩` from `GlobalTheory.T.biInvariant_eigenfunction_eq_mul_zonalSpherical k (l * t) μK hμK ϖ hϖ α`. Take `⟨hvol, hdisj⟩` from `GlobalTheory.T.twistedPlace_doubleCoset_volume_and_disjoint k ϖ hϖ r l t m hm μK hμK`. Establish `hceq : c = fun g => ip ν (om (μ₀ * ξ) g (1 : GL (Fin r ⊕ Blocks (l + 1) t) k) (datum ξ)) (datum ξ)`. Use function extensionality and compare the values at `hc`. Take `⟨hcBi, hcSupp, hcVal⟩` from `GlobalTheory.T.weilRep_chainStep_matrixCoefficient_twisted k ν hν ϖ hϖ r t l ξ μ₀ hξu hξt hμ₀ hμ₀u`.

Rewrite `hcBi`, `hcSupp` using `[← hceq]`. Use `beta_reduce at hcVal`. Establish `hq : (0:ℝ) < resCard k` using `by exact_mod_cast (zero_lt_one.trans (one_lt_resCard k))`. Establish `hq1 : (1:ℝ) < resCard k` using `by exact_mod_cast one_lt_resCard k`. Use `set C0 : ℝ := volAdd ν r * ((resCard k : ℝ) ^ (r * ((l + 1) * t)))⁻¹ with hC0`.

Establish `hC0pos : 0 < C0`. Use `mul_pos ?_ (inv_pos.2 (pow_pos hq _))` and prove the remaining obligations. Rewrite using `[GlobalTheory.ChainStepIdentities.volAdd_eq k ν hν r]`. Use `Finset.prod_pos fun i hi => inv_pos.2 ?_` and prove the remaining obligations. Establish `hi1 : 1 ≤ i` using `(Finset.mem_Icc.1 hi).1`.

Unfold `zetaAt`. Conclude with `inv_pos.2 (sub_pos.2 (inv_lt_one_of_one_lt₀ (one_lt_pow₀ hq1 (by omega))))`. Establish `hcv : ∀ e : Fin (l * t) → ℤ, c (mtor ϖ (e ∘ (blkEquiv l t).symm)) = (((μ₀ * ξ) ϖ : ℂˣ) : ℂ) ^ (∑ i, e i) * ((C0 * (resCard k : ℝ) ^ (-((r + (l + 1) * t : ℕ) : ℝ) / 2 * (sumAbs e : ℝ)) : ℝ) : ℂ)`. Introduce `e`. Establish `hsE : ∑ i, (e ∘ (blkEquiv l t).symm) i = ∑ i, e i` using `Equiv.sum_comp (blkEquiv l t).symm e`.

Rewrite using `[hc, hcVal, hsE, sumAbs_comp, Complex.ofReal_mul C0, Complex.ofReal_cpow hq.le, hC0]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hc1 : c 1 = ((C0 : ℝ) : ℂ)`. Use `hcVal 0` as an intermediate fact.

Rewrite `this` using `[mtor_zero, ← hc]`. Rewrite using `[this]`. Simplify using `[sumAbs, C0]`. Use `set w : (Fin (l * t) → ℤ) → ℂ := fun e => (((resCard k : ℝ) ^ (-((2 * r + (l + 1) * t : ℕ) : ℝ) / 2 * (sumAbs e : ℝ)) : ℝ) : ℂ) * zonalInt μK ψ (torusElt k (Fin (l * t)) ϖ e) with hw`. Use `⟨by rw [hc1]; exact_mod_cast hC0pos.ne', cellFun r l t ϖ w, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `V _ _ π x ℓ hx hℓ g`. Establish `hE` using `lower_eigen k ϖ hϖ r l t ξ μ₀ hξt hξr hμ₀ B α hαB H hH μK ψ hψ V π x ℓ hx hℓ`. Distinguish the cases in `hg : ∃ e : {e : Fin (l * t) → ℤ // Antitone e}, g ∈ dcell ϖ (e.1 ∘ (blkEquiv l t).symm)`. Take `⟨e, hge⟩` from `hg`. Rewrite using `[cellFun_of_mem w hdisj e hge]`.

Take `⟨j, hj, j', hj', rfl⟩` from `DoubleCoset.mem_doubleCoset.1 hge`. Use `set a := (mtor ϖ (e.1 ∘ (blkEquiv l t).symm) : GL (Fin r ⊕ Blocks l t) k) with ha`. Use `set d := Units.mk0 _ (GlobalTheory.ChainStepSupp.det_lower_ne_zero hj)`. Use `set d' := Units.mk0 _ (GlobalTheory.ChainStepSupp.det_lower_ne_zero hj')`. Establish `hc_eq : c (j * a * j') = (ξ d : ℂ) * (ξ d' : ℂ) * c a`.

Rewrite using `[mul_assoc, (hcBi j hj d rfl _).1, (hcBi j' hj' d' rfl a).2]`. Expand and normalize the polynomial expressions, which then agree. Establish `hℓ_eq : ℓ (π (j * a * j') x) = (ξ d : ℂ) * (ξ d' : ℂ) * ℓ (π a x)`. Rewrite using `[map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hx.1 j' hj' d' rfl]`. Simplify using `only [map_smul, smul_eq_mul]`.

Rewrite using `[hℓ j hj d rfl]`. Expand and normalize the polynomial expressions, which then agree. Establish `u1 : starRingEnd ℂ (ξ d : ℂ) * (ξ d : ℂ) = 1`. Rewrite using `[Complex.conj_mul', hξu d]`. Simplify using the standard rewrite rules.

Establish `u2 : starRingEnd ℂ (ξ d' : ℂ) * (ξ d' : ℂ) = 1`. Rewrite using `[Complex.conj_mul', hξu d']`. Simplify using the standard rewrite rules. Establish `hM : ‖(((μ₀ * ξ) ϖ : ℂˣ) : ℂ)‖ = 1`. Rewrite using `[MonoidHom.mul_apply, Units.val_mul, norm_mul, hμ₀u, hξu, one_mul]`.

Establish `u3 : starRingEnd ℂ ((((μ₀ * ξ) ϖ : ℂˣ) : ℂ) ^ (∑ i, e.1 i)) * (((μ₀ * ξ) ϖ : ℂˣ) : ℂ) ^ (∑ i, e.1 i) = 1`. Rewrite using `[map_zpow₀, ← mul_zpow, Complex.conj_mul', hM]`. Simplify using the standard rewrite rules. Establish `hqab : (resCard k : ℝ) ^ (-((r + (l + 1) * t : ℕ) : ℝ) / 2 * (sumAbs e.1 : ℝ)) * (resCard k : ℝ) ^ (-(r : ℝ) / 2 * (sumAbs e.1 : ℝ)) = (resCard k : ℝ) ^ (-((2 * r + (l + 1) * t : ℕ) : ℝ) / 2 * (sumAbs e.1 : ℝ))`. Rewrite using `[← Real.rpow_add hq]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hc_eq, hℓ_eq, hcv e.1, hE e.1, hc1, hw]`. Simplify using `only [map_mul, Complex.conj_ofReal]`.

Establish `hqab'` using `congrArg (fun y : ℝ => (y : ℂ)) hqab`. Simplify using `only [Complex.ofReal_mul] at hqab' ⊢`. Take the linear combination `(↑C0 * zonalInt μK ψ (torusElt k (Fin (l * t)) ϖ e.1) * ℓ x) * ((starRingEnd ℂ (ξ d' : ℂ) * (ξ d' : ℂ) * (starRingEnd ℂ ((((μ₀ * ξ) ϖ : ℂˣ) : ℂ) ^ (∑ i, e.1 i)) * (((μ₀ * ξ) ϖ : ℂˣ) : ℂ) ^ (∑ i, e.1 i)) * ((((resCard k : ℝ) ^ (-((r + (l + 1) * t : ℕ) : ℝ) / 2 * (sumAbs e.1 : ℝ)) …`. Simplify using `only [not_exists] at hg`. Establish `hc0 : c g = 0`.

Assume the negation of the conclusion as `hne`. Take `⟨e, he, hge⟩` from `GlobalTheory.T.support_parahoricBiTransforming_doubleCosets k ϖ hϖ r l t ξ hξt hξr c hcBi hcSupp g hne`. Conclude with `hg ⟨e, he⟩ hge`. Rewrite using `[cellFun_of_notMem w hg, hc0]`. Simplify using the standard rewrite rules.

Introduce `g hgJ`. Establish `h0 : g ∈ dcell ϖ ((0 : Fin (l * t) → ℤ) ∘ (blkEquiv l t).symm)`. Establish `: ((0 : Fin (l * t) → ℤ) ∘ (blkEquiv l t).symm) = 0` using `rfl`. Rewrite using `[this]`. Unfold `dcell`.

Rewrite using `[mtor_zero]`. Conclude with `DoubleCoset.mem_doubleCoset.2 ⟨g, hgJ, 1, one_mem _, by simp⟩`. Rewrite using `[cellFun_of_mem w hdisj ⟨0, fun _ _ _ => le_refl _⟩ h0, hw]`. Simplify using `[sumAbs, torusElt_zero, zonalInt_one μK hμK hψB]`. Introduce `s hs`.

Take `⟨hsum, hhas⟩` from `GlobalTheory.T.unramified_doubling_sum_GL_convergent_L_value hUD k (l * t) μK hμK ϖ hϖ α ρ hαρ ψ hψB s hs`. Establish `hHtor : ∀ e : Fin (l * t) → ℤ, H (mtor ϖ (e ∘ (blkEquiv l t).symm)) = (resCard k : ℝ) ^ (-(sumAbs e))`. Introduce `e`. Rewrite using `[mtor, hH.2, sumAbs_elim, sumAbs_comp]`. Establish `hqC : ((resCard k : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hq.ne'`.

Establish `hterm : ∀ e : {e : Fin (l * t) → ℤ // Antitone e}, (m.real (dcell ϖ (e.1 ∘ (blkEquiv l t).symm)) : ℂ) * (cellFun r l t ϖ w (mtor ϖ (e.1 ∘ (blkEquiv l t).symm)) * (H (mtor ϖ (e.1 ∘ (blkEquiv l t).symm)) : ℂ) ^ (s - (t : ℂ) / 2)) = (μK.real (cell k (Fin (l * t)) ϖ e) : ℂ) * ((resCa …`. Introduce `e`. Establish `hmem : (mtor ϖ (e.1 ∘ (blkEquiv l t).symm) : GL (Fin r ⊕ Blocks l t) k) ∈ dcell ϖ (e.1 ∘ (blkEquiv l t).symm)` using `DoubleCoset.mem_doubleCoset.2 ⟨1, one_mem _, 1, one_mem _, by simp⟩`. Rewrite using `[cellFun_of_mem w hdisj e hmem, hHtor, hvol e.1]`. Simplify using `only [hw]`.

Establish `e1 : (((resCard k : ℝ) ^ ((r : ℤ) * sumAbs e.1) : ℝ) : ℂ) = ((resCard k : ℝ) : ℂ) ^ ((((r : ℤ) * sumAbs e.1 : ℤ) : ℝ) : ℂ)`. Rewrite using `[← Complex.ofReal_cpow hq.le, Real.rpow_intCast]`. Establish `e2 : (((resCard k : ℝ) ^ (-((2 * r + (l + 1) * t : ℕ) : ℝ) / 2 * (sumAbs e.1 : ℝ)) : ℝ) : ℂ) = ((resCard k : ℝ) : ℂ) ^ (((-((2 * r + (l + 1) * t : ℕ) : ℝ) / 2 * (sumAbs e.1 : ℝ)) : ℝ) : ℂ)`. Rewrite using `[Complex.ofReal_cpow hq.le]`. Establish `e3 : (((resCard k : ℝ) ^ (-(sumAbs e.1)) : ℝ) : ℂ) ^ (s - (t : ℂ) / 2) = ((resCard k : ℝ) : ℂ) ^ ((((-(sumAbs e.1) : ℤ) : ℝ) : ℂ) * (s - (t : ℂ) / 2))`.

Rewrite using `[← Real.rpow_intCast, Complex.cpow_mul_ofReal_nonneg hq.le]`. Establish `e4 : (resCard k : ℂ) ^ (-(((l * t : ℕ) : ℂ) / 2 + s) * (sumAbs e.1 : ℂ)) = ((resCard k : ℝ) : ℂ) ^ (-(((l * t : ℕ) : ℂ) / 2 + s) * (sumAbs e.1 : ℂ))`. Rewrite using `[Complex.ofReal_natCast]`. Establish `hadd : ((resCard k : ℝ) : ℂ) ^ ((((r : ℤ) * sumAbs e.1 : ℤ) : ℝ) : ℂ) * ((resCard k : ℝ) : ℂ) ^ (((-((2 * r + (l + 1) * t : ℕ) : ℝ) / 2 * (sumAbs e.1 : ℝ)) : ℝ) : ℂ) * ((resCard k : ℝ) : ℂ) ^ ((((-(sumAbs e.1) : ℤ) : ℝ) : ℂ) * (s - (t : ℂ) / 2)) = ((resCard k : ℝ) : ℂ) ^ (-(((l * …`. Rewrite using `[← Complex.cpow_add _ _ hqC, ← Complex.cpow_add _ _ hqC]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Complex.ofReal_mul, e1, e2, e3, e4, ← hadd]`. Expand and normalize the polynomial expressions, which then agree.

Use `set F : GL (Fin r ⊕ Blocks l t) k → ℂ := fun g => cellFun r l t ϖ w g * (H g : ℂ) ^ (s - (t : ℂ) / 2) with hF`. Establish `hFbi : ∀ g j, j ∈ parahoric k (Fin r) (Blocks l t) → ∀ j' ∈ parahoric k (Fin r) (Blocks l t), F (j * g * j') = F g`. Introduce `g j hj j' hj'`. Establish `hjK` using `(mem_parahoric.1 hj).1`. Establish `hj'K` using `(mem_parahoric.1 hj').1`.

Simplify using `only [hF, cellFun_biinv w g hj hj', (hH.1 j' hj'K (j * g)).2, (hH.1 j hjK g).1]`. Establish `hsupp : ∀ g, F g ≠ 0 → ∃ e : {e : Fin (l * t) → ℤ // Antitone e}, g ∈ DoubleCoset.doubleCoset (mtor ϖ (e.1 ∘ (blkEquiv l t).symm)) (parahoric k (Fin r) (Blocks l t) : Set (GL (Fin r ⊕ Blocks l t) k)) (parahoric k (Fin r) (Blocks l t))`. Introduce `g hg`. Assume the negation of the conclusion as `hne`. Simplify using `only [not_exists] at hne`.

Apply `hg` to reduce the goal to its premises. Simplify using `only [hF, cellFun_of_notMem w hne, zero_mul]`. Establish `hsumm : Summable fun e : {e : Fin (l * t) → ℤ // Antitone e} => m.real (DoubleCoset.doubleCoset (mtor ϖ (e.1 ∘ (blkEquiv l t).symm)) (parahoric k (Fin r) (Blocks l t) : Set (GL (Fin r ⊕ Blocks l t) k)) (parahoric k (Fin r) (Blocks l t))) * ‖F (mtor ϖ (e.1 ∘ (blkEquiv l t).symm))‖`. Use `hsum.congr fun e => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = m.real (dcell ϖ (e.1 ∘ (blkEquiv l t).symm)) * _`.

Rewrite using `[← hterm e, norm_mul, Complex.norm_real, Real.norm_of_nonneg measureReal_nonneg]`. Take `⟨hInt, hHas, -⟩` from `GlobalTheory.integral_biInvariant_hasSum_doubleCoset (GL (Fin r ⊕ Blocks l t) k) m (parahoric k (Fin r) (Blocks l t)) GlobalTheory.ParHecke.Model.isOpen_parahoric GlobalTheory.ParHecke.Model.isCompact_parahoric {e : Fin (l * t) → ℤ // Antitone e} (fun e => mtor ϖ (e.1 ∘ (blkEquiv …`. Use `⟨hInt, ?_⟩` and prove the remaining obligations. Establish `hfun : (fun e : {e : Fin (l * t) → ℤ // Antitone e} => ((m.real (DoubleCoset.doubleCoset (mtor ϖ (e.1 ∘ (blkEquiv l t).symm)) (parahoric k (Fin r) (Blocks l t) : Set (GL (Fin r ⊕ Blocks l t) k)) (parahoric k (Fin r) (Blocks l t))) : ℝ) : ℂ) * F (mtor ϖ (e.1 ∘ (blkEquiv l t).symm) …` using `funext hterm`. Rewrite `hHas` using `[hfun]`.

Conclude with `hHas.unique hhas`.
-/
theorem local_zeta_twisted : GlobalTheory.Published.UnramifiedDoublingGL → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (r t l : ℕ) (ξ μ₀ : kˣ →* ℂˣ), IsUnitaryChar ξ → IsTame ξ → ¬ IsUnram ξ → IsUnram μ₀ → IsUnitaryChar μ₀ → ∀ (B : Multiset ℂˣ) (α : Fin (l * t) → ℂˣ) (ρ : ℝ), Finset.univ.val.map α = B.map (· * ((μ₀ * ξ) ϖ)⁻¹) → (∀ x, ‖(α x : ℂ)‖ ≤ (resCard k : ℝ) ^ ρ ∧ ‖(α x : ℂ)‖⁻¹ ≤ (resCard k : ℝ) ^ ρ) → ∀ H : GL (Fin r ⊕ Blocks l t) k → ℝ, IsHgt ϖ H → ∀ [MeasurableSpace (GL (Fin r ⊕ Blocks l t) k)] [BorelSpace (GL (Fin r ⊕ Blocks l t) k)] (m : Measure (GL (Fin r ⊕ Blocks l t) k)) [m.IsHaarMeasure], m (parahoric k (Fin r) (Blocks l t)) = 1 → ∀ c : GL (Fin r ⊕ Blocks l t) k → ℂ, (∀ g, c g = ip ν (om (μ₀ * ξ) g (1 : GL (Fin r ⊕ Blocks (l + 1) t) k) (datum ξ)) (datum ξ)) → c 1 ≠ 0 ∧ ∃ ζ : GL (Fin r ⊕ Blocks l t) k → ℂ, (∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin r ⊕ Blocks l t) k) V) (x : V) (ℓ : V →ₗ[ℂ] ℂ), IsGen π ξ ϖ B x → IsCoType π ξ ℓ → ∀ g, starRingEnd ℂ (c g) * ℓ (π g x) = starRingEnd ℂ (c 1) * ζ g * ℓ x) ∧ (∀ g ∈ parahoric k (Fin r) (Blocks l t), ζ g = 1) ∧ ∀ s : ℂ, ρ - 1 / 2 < s.re → Integrable (fun g => ζ g * (H g : ℂ) ^ (s - (t : ℂ) / 2)) m ∧ ∫ g, ζ g * (H g : ℂ) ^ (s - (t : ℂ) / 2) ∂m = lFactor (resCard k) α (s + 1 / 2) * lFactor (resCard k) α⁻¹ (s + 1 / 2) * invNormFactor (resCard k) (l * t) s := by
  intro hUD k _ _ _ _ _ _ _ ν hν ϖ hϖ r t l ξ μ₀ hξu hξt hξr hμ₀ hμ₀u B α ρ hαB hαρ H hH _ _ m _ hm c hc
  classical
  letI : MeasurableSpace (GL (Fin (l * t)) k) := borel _
  haveI : BorelSpace (GL (Fin (l * t)) k) := ⟨rfl⟩
  obtain ⟨μK, hμKH, hμK⟩ := GlobalTheory.GLDoubling.Model.exists_haar (k := k) (l * t)
  haveI := hμKH
  obtain ⟨ψ, hψB, hψ⟩ := GlobalTheory.T.biInvariant_eigenfunction_eq_mul_zonalSpherical k (l * t) μK hμK ϖ hϖ α
  obtain ⟨hvol, hdisj⟩ := GlobalTheory.T.twistedPlace_doubleCoset_volume_and_disjoint k ϖ hϖ r l t m hm μK hμK
  have hceq : c = fun g => ip ν (om (μ₀ * ξ) g (1 : GL (Fin r ⊕ Blocks (l + 1) t) k) (datum ξ)) (datum ξ) :=
    funext hc
  obtain ⟨hcBi, hcSupp, hcVal⟩ := GlobalTheory.T.weilRep_chainStep_matrixCoefficient_twisted k ν hν ϖ hϖ r t l ξ μ₀ hξu hξt hμ₀ hμ₀u
  rw [← hceq] at hcBi hcSupp
  beta_reduce at hcVal
  have hq : (0:ℝ) < resCard k := by exact_mod_cast (zero_lt_one.trans (one_lt_resCard k))
  have hq1 : (1:ℝ) < resCard k := by exact_mod_cast one_lt_resCard k
  set C0 : ℝ := volAdd ν r * ((resCard k : ℝ) ^ (r * ((l + 1) * t)))⁻¹ with hC0
  have hC0pos : 0 < C0 := by
    refine mul_pos ?_ (inv_pos.2 (pow_pos hq _))
    rw [GlobalTheory.ChainStepIdentities.volAdd_eq k ν hν r]
    refine Finset.prod_pos fun i hi => inv_pos.2 ?_
    have hi1 : 1 ≤ i := (Finset.mem_Icc.1 hi).1
    unfold zetaAt
    exact inv_pos.2 (sub_pos.2 (inv_lt_one_of_one_lt₀ (one_lt_pow₀ hq1 (by omega))))
  have hcv : ∀ e : Fin (l * t) → ℤ, c (mtor ϖ (e ∘ (blkEquiv l t).symm)) = (((μ₀ * ξ) ϖ : ℂˣ) : ℂ) ^ (∑ i, e i) *
      ((C0 * (resCard k : ℝ) ^ (-((r + (l + 1) * t : ℕ) : ℝ) / 2 * (sumAbs e : ℝ)) : ℝ) : ℂ) := by
    intro e
    have hsE : ∑ i, (e ∘ (blkEquiv l t).symm) i = ∑ i, e i := Equiv.sum_comp (blkEquiv l t).symm e
    rw [hc, hcVal, hsE, sumAbs_comp, Complex.ofReal_mul C0, Complex.ofReal_cpow hq.le, hC0]
    push_cast
    ring
  have hc1 : c 1 = ((C0 : ℝ) : ℂ) := by
    have := hcVal 0
    rw [mtor_zero, ← hc] at this
    rw [this]; simp [sumAbs, C0]
  set w : (Fin (l * t) → ℤ) → ℂ := fun e => (((resCard k : ℝ) ^
      (-((2 * r + (l + 1) * t : ℕ) : ℝ) / 2 * (sumAbs e : ℝ)) : ℝ) : ℂ) *
      zonalInt μK ψ (torusElt k (Fin (l * t)) ϖ e) with hw
  refine ⟨by rw [hc1]; exact_mod_cast hC0pos.ne', cellFun r l t ϖ w, ?_, ?_, ?_⟩
  · intro V _ _ π x ℓ hx hℓ g
    have hE := lower_eigen k ϖ hϖ r l t ξ μ₀ hξt hξr hμ₀ B α hαB H hH μK ψ hψ V π x ℓ hx hℓ
    by_cases hg : ∃ e : {e : Fin (l * t) → ℤ // Antitone e}, g ∈ dcell ϖ (e.1 ∘ (blkEquiv l t).symm)
    · obtain ⟨e, hge⟩ := hg
      rw [cellFun_of_mem w hdisj e hge]
      obtain ⟨j, hj, j', hj', rfl⟩ := DoubleCoset.mem_doubleCoset.1 hge
      set a := (mtor ϖ (e.1 ∘ (blkEquiv l t).symm) : GL (Fin r ⊕ Blocks l t) k) with ha
      set d := Units.mk0 _ (GlobalTheory.ChainStepSupp.det_lower_ne_zero hj)
      set d' := Units.mk0 _ (GlobalTheory.ChainStepSupp.det_lower_ne_zero hj')
      have hc_eq : c (j * a * j') = (ξ d : ℂ) * (ξ d' : ℂ) * c a := by
        rw [mul_assoc, (hcBi j hj d rfl _).1, (hcBi j' hj' d' rfl a).2]; ring
      have hℓ_eq : ℓ (π (j * a * j') x) = (ξ d : ℂ) * (ξ d' : ℂ) * ℓ (π a x) := by
        rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hx.1 j' hj' d' rfl]
        simp only [map_smul, smul_eq_mul]
        rw [hℓ j hj d rfl]; ring
      have u1 : starRingEnd ℂ (ξ d : ℂ) * (ξ d : ℂ) = 1 := by
        rw [Complex.conj_mul', hξu d]; simp
      have u2 : starRingEnd ℂ (ξ d' : ℂ) * (ξ d' : ℂ) = 1 := by
        rw [Complex.conj_mul', hξu d']; simp
      have hM : ‖(((μ₀ * ξ) ϖ : ℂˣ) : ℂ)‖ = 1 := by
        rw [MonoidHom.mul_apply, Units.val_mul, norm_mul, hμ₀u, hξu, one_mul]
      have u3 : starRingEnd ℂ ((((μ₀ * ξ) ϖ : ℂˣ) : ℂ) ^ (∑ i, e.1 i)) * (((μ₀ * ξ) ϖ : ℂˣ) : ℂ) ^ (∑ i, e.1 i) = 1 := by
        rw [map_zpow₀, ← mul_zpow, Complex.conj_mul', hM]; simp
      have hqab : (resCard k : ℝ) ^ (-((r + (l + 1) * t : ℕ) : ℝ) / 2 * (sumAbs e.1 : ℝ)) *
          (resCard k : ℝ) ^ (-(r : ℝ) / 2 * (sumAbs e.1 : ℝ)) =
          (resCard k : ℝ) ^ (-((2 * r + (l + 1) * t : ℕ) : ℝ) / 2 * (sumAbs e.1 : ℝ)) := by
        rw [← Real.rpow_add hq]; congr 1; push_cast; ring
      rw [hc_eq, hℓ_eq, hcv e.1, hE e.1, hc1, hw]
      simp only [map_mul, Complex.conj_ofReal]
      have hqab' := congrArg (fun y : ℝ => (y : ℂ)) hqab
      simp only [Complex.ofReal_mul] at hqab' ⊢
      linear_combination (↑C0 * zonalInt μK ψ (torusElt k (Fin (l * t)) ϖ e.1) * ℓ x) *
        ((starRingEnd ℂ (ξ d' : ℂ) * (ξ d' : ℂ) * (starRingEnd ℂ ((((μ₀ * ξ) ϖ : ℂˣ) : ℂ) ^ (∑ i, e.1 i)) *
          (((μ₀ * ξ) ϖ : ℂˣ) : ℂ) ^ (∑ i, e.1 i)) *
          ((((resCard k : ℝ) ^ (-((r + (l + 1) * t : ℕ) : ℝ) / 2 * (sumAbs e.1 : ℝ)) : ℝ) : ℂ) *
          ((((resCard k : ℝ) ^ (-(r : ℝ) / 2 * (sumAbs e.1 : ℝ))) : ℝ) : ℂ))) * u1 +
        ((starRingEnd ℂ ((((μ₀ * ξ) ϖ : ℂˣ) : ℂ) ^ (∑ i, e.1 i)) * (((μ₀ * ξ) ϖ : ℂˣ) : ℂ) ^ (∑ i, e.1 i)) *
          ((((resCard k : ℝ) ^ (-((r + (l + 1) * t : ℕ) : ℝ) / 2 * (sumAbs e.1 : ℝ)) : ℝ) : ℂ) *
          ((((resCard k : ℝ) ^ (-(r : ℝ) / 2 * (sumAbs e.1 : ℝ))) : ℝ) : ℂ))) * u2 +
        (((((resCard k : ℝ) ^ (-((r + (l + 1) * t : ℕ) : ℝ) / 2 * (sumAbs e.1 : ℝ)) : ℝ) : ℂ) *
          ((((resCard k : ℝ) ^ (-(r : ℝ) / 2 * (sumAbs e.1 : ℝ))) : ℝ) : ℂ))) * u3 + hqab')
    · simp only [not_exists] at hg
      have hc0 : c g = 0 := by
        by_contra hne
        obtain ⟨e, he, hge⟩ := GlobalTheory.T.support_parahoricBiTransforming_doubleCosets k ϖ hϖ r l t ξ hξt hξr c hcBi hcSupp g hne
        exact hg ⟨e, he⟩ hge
      rw [cellFun_of_notMem w hg, hc0]; simp
  · intro g hgJ
    have h0 : g ∈ dcell ϖ ((0 : Fin (l * t) → ℤ) ∘ (blkEquiv l t).symm) := by
      have : ((0 : Fin (l * t) → ℤ) ∘ (blkEquiv l t).symm) = 0 := rfl
      rw [this]
      unfold dcell
      rw [mtor_zero]
      exact DoubleCoset.mem_doubleCoset.2 ⟨g, hgJ, 1, one_mem _, by simp⟩
    rw [cellFun_of_mem w hdisj ⟨0, fun _ _ _ => le_refl _⟩ h0, hw]
    simp [sumAbs, torusElt_zero, zonalInt_one μK hμK hψB]
  · intro s hs
    obtain ⟨hsum, hhas⟩ := GlobalTheory.T.unramified_doubling_sum_GL_convergent_L_value hUD k (l * t) μK hμK ϖ hϖ α ρ hαρ ψ hψB s hs
    have hHtor : ∀ e : Fin (l * t) → ℤ, H (mtor ϖ (e ∘ (blkEquiv l t).symm)) = (resCard k : ℝ) ^ (-(sumAbs e)) := by
      intro e; rw [mtor, hH.2, sumAbs_elim, sumAbs_comp]
    have hqC : ((resCard k : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
    have hterm : ∀ e : {e : Fin (l * t) → ℤ // Antitone e},
        (m.real (dcell ϖ (e.1 ∘ (blkEquiv l t).symm)) : ℂ) *
          (cellFun r l t ϖ w (mtor ϖ (e.1 ∘ (blkEquiv l t).symm)) *
            (H (mtor ϖ (e.1 ∘ (blkEquiv l t).symm)) : ℂ) ^ (s - (t : ℂ) / 2)) =
        (μK.real (cell k (Fin (l * t)) ϖ e) : ℂ) * ((resCard k : ℂ) ^ (-(((l * t : ℕ) : ℂ) / 2 + s) * (sumAbs e.1 : ℂ)) *
          zonalInt μK ψ (torusElt k (Fin (l * t)) ϖ e)) := by
      intro e
      have hmem : (mtor ϖ (e.1 ∘ (blkEquiv l t).symm) : GL (Fin r ⊕ Blocks l t) k) ∈
          dcell ϖ (e.1 ∘ (blkEquiv l t).symm) :=
        DoubleCoset.mem_doubleCoset.2 ⟨1, one_mem _, 1, one_mem _, by simp⟩
      rw [cellFun_of_mem w hdisj e hmem, hHtor, hvol e.1]
      simp only [hw]
      have e1 : (((resCard k : ℝ) ^ ((r : ℤ) * sumAbs e.1) : ℝ) : ℂ) =
          ((resCard k : ℝ) : ℂ) ^ ((((r : ℤ) * sumAbs e.1 : ℤ) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_cpow hq.le, Real.rpow_intCast]
      have e2 : (((resCard k : ℝ) ^ (-((2 * r + (l + 1) * t : ℕ) : ℝ) / 2 * (sumAbs e.1 : ℝ)) : ℝ) : ℂ) =
          ((resCard k : ℝ) : ℂ) ^ (((-((2 * r + (l + 1) * t : ℕ) : ℝ) / 2 * (sumAbs e.1 : ℝ)) : ℝ) : ℂ) := by
        rw [Complex.ofReal_cpow hq.le]
      have e3 : (((resCard k : ℝ) ^ (-(sumAbs e.1)) : ℝ) : ℂ) ^ (s - (t : ℂ) / 2) =
          ((resCard k : ℝ) : ℂ) ^ ((((-(sumAbs e.1) : ℤ) : ℝ) : ℂ) * (s - (t : ℂ) / 2)) := by
        rw [← Real.rpow_intCast, Complex.cpow_mul_ofReal_nonneg hq.le]
      have e4 : (resCard k : ℂ) ^ (-(((l * t : ℕ) : ℂ) / 2 + s) * (sumAbs e.1 : ℂ)) =
          ((resCard k : ℝ) : ℂ) ^ (-(((l * t : ℕ) : ℂ) / 2 + s) * (sumAbs e.1 : ℂ)) := by
        rw [Complex.ofReal_natCast]
      have hadd : ((resCard k : ℝ) : ℂ) ^ ((((r : ℤ) * sumAbs e.1 : ℤ) : ℝ) : ℂ) *
          ((resCard k : ℝ) : ℂ) ^ (((-((2 * r + (l + 1) * t : ℕ) : ℝ) / 2 * (sumAbs e.1 : ℝ)) : ℝ) : ℂ) *
          ((resCard k : ℝ) : ℂ) ^ ((((-(sumAbs e.1) : ℤ) : ℝ) : ℂ) * (s - (t : ℂ) / 2)) =
          ((resCard k : ℝ) : ℂ) ^ (-(((l * t : ℕ) : ℂ) / 2 + s) * (sumAbs e.1 : ℂ)) := by
        rw [← Complex.cpow_add _ _ hqC, ← Complex.cpow_add _ _ hqC]
        congr 1
        push_cast
        ring
      rw [Complex.ofReal_mul, e1, e2, e3, e4, ← hadd]
      ring
    set F : GL (Fin r ⊕ Blocks l t) k → ℂ := fun g => cellFun r l t ϖ w g * (H g : ℂ) ^ (s - (t : ℂ) / 2) with hF
    have hFbi : ∀ g j, j ∈ parahoric k (Fin r) (Blocks l t) → ∀ j' ∈ parahoric k (Fin r) (Blocks l t),
        F (j * g * j') = F g := by
      intro g j hj j' hj'
      have hjK := (mem_parahoric.1 hj).1
      have hj'K := (mem_parahoric.1 hj').1
      simp only [hF, cellFun_biinv w g hj hj', (hH.1 j' hj'K (j * g)).2, (hH.1 j hjK g).1]
    have hsupp : ∀ g, F g ≠ 0 → ∃ e : {e : Fin (l * t) → ℤ // Antitone e},
        g ∈ DoubleCoset.doubleCoset (mtor ϖ (e.1 ∘ (blkEquiv l t).symm))
          (parahoric k (Fin r) (Blocks l t) : Set (GL (Fin r ⊕ Blocks l t) k)) (parahoric k (Fin r) (Blocks l t)) := by
      intro g hg
      by_contra hne
      simp only [not_exists] at hne
      apply hg
      simp only [hF, cellFun_of_notMem w hne, zero_mul]
    have hsumm : Summable fun e : {e : Fin (l * t) → ℤ // Antitone e} =>
        m.real (DoubleCoset.doubleCoset (mtor ϖ (e.1 ∘ (blkEquiv l t).symm))
          (parahoric k (Fin r) (Blocks l t) : Set (GL (Fin r ⊕ Blocks l t) k)) (parahoric k (Fin r) (Blocks l t))) *
          ‖F (mtor ϖ (e.1 ∘ (blkEquiv l t).symm))‖ := by
      refine hsum.congr fun e => ?_
      change _ = m.real (dcell ϖ (e.1 ∘ (blkEquiv l t).symm)) * _
      rw [← hterm e, norm_mul, Complex.norm_real, Real.norm_of_nonneg measureReal_nonneg]
    obtain ⟨hInt, hHas, -⟩ := GlobalTheory.integral_biInvariant_hasSum_doubleCoset (GL (Fin r ⊕ Blocks l t) k) m
      (parahoric k (Fin r) (Blocks l t)) GlobalTheory.ParHecke.Model.isOpen_parahoric GlobalTheory.ParHecke.Model.isCompact_parahoric
      {e : Fin (l * t) → ℤ // Antitone e} (fun e => mtor ϖ (e.1 ∘ (blkEquiv l t).symm)) hdisj F hFbi hsupp hsumm
    refine ⟨hInt, ?_⟩
    have hfun : (fun e : {e : Fin (l * t) → ℤ // Antitone e} =>
        ((m.real (DoubleCoset.doubleCoset (mtor ϖ (e.1 ∘ (blkEquiv l t).symm))
          (parahoric k (Fin r) (Blocks l t) : Set (GL (Fin r ⊕ Blocks l t) k)) (parahoric k (Fin r) (Blocks l t))) : ℝ) : ℂ) *
          F (mtor ϖ (e.1 ∘ (blkEquiv l t).symm))) = fun e : {e : Fin (l * t) → ℤ // Antitone e} => (μK.real (cell k (Fin (l * t)) ϖ e) : ℂ) *
          ((resCard k : ℂ) ^ (-(((l * t : ℕ) : ℂ) / 2 + s) * (sumAbs e.1 : ℂ)) *
            zonalInt μK ψ (torusElt k (Fin (l * t)) ϖ e)) := funext hterm
    rw [hfun] at hHas
    exact hHas.unique hhas

end GlobalTheory.TwistedZeta
