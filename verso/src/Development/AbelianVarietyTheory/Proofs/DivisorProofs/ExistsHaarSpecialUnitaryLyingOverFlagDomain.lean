import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsContinuousGramSchmidt
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.UpperTriangularPreservesDiagonalIff
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MuFLtTopOfIsCompact
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DetNeZeroOfIsOrth
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ContinuousOnRmul
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasureStatements
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarIntegralEqUnitriangularChart

open NumberField MeasureTheory Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates Topology
open scoped ENNReal

namespace GlobalTheory.SUHaarOver

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

/- English proof (translation)
Establish `h` using `UnitaryInvMeasure.gram_lmulC X hn x τ`. Establish `hm : mat (X.lmulC n x) τ = n τ * mat x τ` using `rfl`. Rewrite `h` using `[hm, UnitaryFrames.gram_eq_mul, UnitaryFrames.gram_eq_mul]`. Establish `hd` using `congrArg Matrix.det h`. Establish `hK : (mat x τ).det * ((X.Gm.map τ.1).det * ((mat x τ).map (starRingEnd ℂ)).det) ≠ 0`.

Establish `h2` using `congrArg Matrix.det (hx τ)`. Rewrite `h2` using `[UnitaryFrames.gram_eq_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]`. Rewrite using `[h2, Matrix.det_diagonal]`. Use `Finset.prod_ne_zero_iff.2 fun a _ => ?_` and prove the remaining obligations. Unfold `sgn`.

Apply the tactic sequence `split_ifs <;> simp`. Simplify using `only [Matrix.det_mul, Matrix.det_transpose, Matrix.map_mul] at hd`. Establish `hc : ((n τ).map (starRingEnd ℂ)).det = starRingEnd ℂ (n τ).det` using `(RingHom.map_det _ _).symm`. Rewrite `hd` using `[hc]`. Establish `h3 : (n τ).det * (starRingEnd ℂ) (n τ).det = 1`.

Apply `mul_right_cancel₀ hK` to reduce the goal to its premises. Take the linear combination `hd`. Establish `h4 : ((Complex.normSq (n τ).det : ℝ) : ℂ) = 1` using `by rw [← Complex.mul_conj]; exact h3`. Establish `h5 : Complex.normSq (n τ).det = 1` using `by exact_mod_cast h4`. Rewrite `h5` using `[Complex.normSq_eq_norm_sq]`.

Establish `h6 : 0 ≤ ‖(n τ).det‖` using `norm_nonneg _`. Use polynomial arithmetic with `[h5, h6]`.
-/
theorem norm_det_eq_one (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x)
    {n : X.Ψ → Matrix (Fin r) (Fin r) ℂ} (hn : X.IsUnitaryC n) (τ : X.Ψ) : ‖(n τ).det‖ = 1 := by
  have h := UnitaryInvMeasure.gram_lmulC X hn x τ
  have hm : mat (X.lmulC n x) τ = n τ * mat x τ := rfl
  rw [hm, UnitaryFrames.gram_eq_mul, UnitaryFrames.gram_eq_mul] at h
  have hd := congrArg Matrix.det h
  have hK : (mat x τ).det * ((X.Gm.map τ.1).det * ((mat x τ).map (starRingEnd ℂ)).det) ≠ 0 := by
    have h2 := congrArg Matrix.det (hx τ)
    rw [UnitaryFrames.gram_eq_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h2
    rw [h2, Matrix.det_diagonal]
    refine Finset.prod_ne_zero_iff.2 fun a _ => ?_
    unfold sgn
    split_ifs <;> simp
  simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.map_mul] at hd
  have hc : ((n τ).map (starRingEnd ℂ)).det = starRingEnd ℂ (n τ).det := (RingHom.map_det _ _).symm
  rw [hc] at hd
  have h3 : (n τ).det * (starRingEnd ℂ) (n τ).det = 1 := by
    apply mul_right_cancel₀ hK
    linear_combination hd
  have h4 : ((Complex.normSq (n τ).det : ℝ) : ℂ) = 1 := by rw [← Complex.mul_conj]; exact h3
  have h5 : Complex.normSq (n τ).det = 1 := by exact_mod_cast h4
  rw [Complex.normSq_eq_norm_sq] at h5
  have h6 : 0 ≤ ‖(n τ).det‖ := norm_nonneg _
  nlinarith [h5, h6]

open UnitaryInvMeasure in

/- English proof (translation)
Introduce `E _ _ _ r X x _ _ hr hx`. Use `set H := UnitaryFrames.unitarySubgroup X with hHdef`. Use `letI : MeasurableSpace H := borel H`. Use `haveI : BorelSpace H := ⟨rfl⟩`. Establish `hHm : ∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)` using `fun _ => Iff.rfl`.

Take `⟨hLC, hSC, hfr⟩` from `UnitaryFrames.unitary_group_frames.2 r X H hHm`. Use `haveI := hLC`. Use `haveI := hSC`. Take `⟨-, ι, hιc, hι1, -⟩` from `hfr x hx`. Take `⟨νU, hνl, hνf, hν⟩` from `invMeas FrameMeasureClosed.measure_statements.2.1 GramSchmidtCont.exists_continuous_gramSchmidt isOrth_rmul_iff_unitary_diagonal (SatFin.muF_sat_lt_top FrameMeasureClosed.measure_statements.2.1) UnitaryFrames.unitary_group_frames.2 r X H hHm x hx`.

Use `haveI := hνl`. Use `haveI := hνf`. Set `M : (X.Ψ → GL (Fin r) ℂ) → X.Ψ → Matrix (Fin r) (Fin r) ℂ` to `fun g τ => (g τ : Matrix (Fin r) (Fin r) ℂ)`. Establish `hU : ∀ g : H, X.IsUnitaryC (M g.1)` using `fun g => g.2`. Establish `hMmul : ∀ g h : X.Ψ → GL (Fin r) ℂ, ∀ τ, M (g * h) τ = M g τ * M h τ` using `fun g h τ => by`.

Simplify using `only [M, Pi.mul_apply, Units.val_mul]`. Establish `hMc : ∀ τ, Continuous fun g : X.Ψ → GL (Fin r) ℂ => M g τ` using `fun τ => Units.continuous_val.comp (continuous_apply τ)`. Set `dC : H → X.Ψ → Circle` to `fun g τ => ⟨(M g.1 τ).det, by simpa [Submonoid.unitSphere] using norm_det_eq_one X hx (hU g) τ⟩`. Establish `hdC : ∀ g τ, ((dC g τ : Circle) : ℂ) = (M g.1 τ).det` using `fun _ _ => rfl`. Set `tU : H → Torus X` to `fun g τ a => if (a : ℕ) = 0 then (dC g τ)⁻¹ else 1`.

Set `cT : Torus X → H` to `fun t => ι (rmul x (diagF X t))`. Set `cU : H → H` to `fun g => cT (tU g)`. Establish `horthT : ∀ t, IsOrth X (rmul x (diagF X t))` using `fun t => (isOrth_rmul_iff_unitary_diagonal r X x _ hx (diagF_mem X t)).2 (diagF_unit X t)`. Establish `hcx : ∀ t, X.lmulC (M (cT t).1) x = rmul x (diagF X t)` using `fun t => hι1 _ (horthT t)`. Establish `hdCc : Continuous dC` using `continuous_pi fun τ => Continuous.subtype_mk ((hMc τ).comp continuous_subtype_val).matrix_det _`.

Establish `htUc : Continuous tU`. Use `continuous_pi fun τ => continuous_pi fun a => ?_` and prove the remaining obligations. Distinguish the cases in `ha : (a : ℕ) = 0`. Simplify using `only [tU, ha, if_true]`. Conclude with `((continuous_apply τ).comp hdCc).inv`.

Simplify using `only [tU, ha, if_false]`. Conclude with `continuous_const`. Establish `hcTc : Continuous cT`. Use `hιc.comp_continuous ?_ fun t => horthT t` and prove the remaining obligations. Conclude with `(continuous_rmul X).comp (continuous_const.prodMk (continuous_diagF X))`.

Establish `hcUc : Continuous cU` using `hcTc.comp htUc`. Establish `hdetc : ∀ (g : H) τ, (M (cU g).1 τ).det * (M g.1 τ).det = 1`. Introduce `g τ`. Establish `h1` using `congrArg Matrix.det (congrFun (hcx (tU g)) τ)`. Establish `e1 : X.lmulC (M (cU g).1) x τ = M (cU g).1 τ * mat x τ` using `rfl`.

Establish `e2 : rmul x (diagF X (tU g)) τ = mat x τ * mat (diagF X (tU g)) τ` using `rfl`. Establish `e3 : (mat (diagF X (tU g)) τ).det = ((M g.1 τ).det)⁻¹` using `by show (Matrix.diagonal fun a => ((tU g τ a : Circle) : ℂ)).det = _`. Rewrite using `[Matrix.det_diagonal, Finset.prod_eq_single (⟨0, hr⟩ : Fin r)]`. Simplify using `only [tU, if_true, Circle.coe_inv, hdC]`. Introduce `b _ hb`.

Establish `: (b : ℕ) ≠ 0` using `fun h => hb (Fin.ext h)`. Simplify using `only [tU, this, if_false, Circle.coe_one]`. Simplify using the standard rewrite rules. Establish `hx0` using `UnitaryFrames.det_ne_zero_of_isOrth X hx τ`. Establish `hg0 : (M g.1 τ).det ≠ 0`.

Introduce `h0`. Use `norm_det_eq_one X hx (hU g) τ` as an intermediate fact. Rewrite `this` using `[h0, norm_zero]`. Conclude with `zero_ne_one this`. Establish `h2 : (M (cU g).1 τ).det * (mat x τ).det = (mat x τ).det * ((M g.1 τ).det)⁻¹`.

Establish `h1' : (M (cU g).1 τ * mat x τ).det = (mat x τ * mat (diagF X (tU g)) τ).det`. Rewrite using `[← e1, ← e2]`. Conclude with `h1`. Rewrite `h1'` using `[Matrix.det_mul, Matrix.det_mul, e3]`. Conclude with `h1'`.

Establish `hi : (M g.1 τ).det * ((M g.1 τ).det)⁻¹ = 1` using `mul_inv_cancel₀ hg0`. Establish `h3 : (M (cU g).1 τ).det * (M g.1 τ).det = 1`. Apply `mul_right_cancel₀ hx0` to reduce the goal to its premises. Take the linear combination `(M g.1 τ).det * h2 + (mat x τ).det * hi`. Conclude with `h3`.

Establish `hpmem : ∀ g : H, (g * cU g).1 ∈ realSU X.Ψ X.Gm`. Introduce `g τ`. Use `⟨?_, (g * cU g).2 τ⟩` and prove the remaining obligations. Use `show (M (g.1 * (cU g).1) τ).det = 1`. Rewrite using `[hMmul, Matrix.det_mul, mul_comm]`.

Conclude with `hdetc g τ`. Set `p : H → realSU X.Ψ X.Gm` to `fun g => ⟨(g * cU g).1, hpmem g⟩`. Establish `hpc : Continuous p` using `Continuous.subtype_mk (continuous_subtype_val.comp (continuous_id.mul hcUc)) _`. Establish `hpm : Measurable p` using `hpc.measurable`. Set `incl : realSU X.Ψ X.Gm → H` to `fun s => ⟨s.1, fun τ => (s.2 τ).2⟩`.

Establish `hinclc : Continuous incl` using `Continuous.subtype_mk continuous_subtype_val _`. Establish `hpinv : ∀ (s : (realSU X.Ψ X.Gm)) (g : H), p (incl s * g) = s * p g`. Introduce `s g`. Establish `htU : tU (incl s * g) = tU g`. Establish `hd : dC (incl s * g) = dC g`.

Use function extensionality and compare the values at `τ`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show (M (s.1 * g.1) τ).det = (M g.1 τ).det`. Rewrite using `[hMmul, Matrix.det_mul, (s.2 τ).1, one_mul]`. Use function extensionality and compare the values at `τ a`.

Use `show (if (a : ℕ) = 0 then (dC (incl s * g) τ)⁻¹ else 1) = (if (a : ℕ) = 0 then (dC g τ)⁻¹ else 1)`. Rewrite using `[hd]`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show (incl s * g).1 * (cT (tU (incl s * g))).1 = s.1 * (g.1 * (cT (tU g)).1)`. Rewrite using `[htU, Subgroup.coe_mul, mul_assoc]`.

Establish `hkey : ∀ g : H, X.lmulC (M (g * cU g).1) x = rmul (X.lmulC (M g.1) x) (diagF X (tU g))`. Introduce `g`. Use function extensionality and compare the values at `τ`. Establish `hc` using `congrFun (hcx (tU g)) τ`. Use `show M ((g : X.Ψ → GL (Fin r) ℂ) * (cU g).1) τ * mat x τ = (M g.1 τ * mat x τ) * mat (diagF X (tU g)) τ`.

Establish `hc' : M (cU g).1 τ * mat x τ = mat x τ * mat (diagF X (tU g)) τ` using `hc`. Rewrite using `[hMmul, Matrix.mul_assoc, hc', Matrix.mul_assoc]`. Use `set ν : Measure (realSU X.Ψ X.Gm) := νU.map p with hνdef`. Establish `hνinv : ν.IsMulLeftInvariant` using `⟨fun s => by`. Establish `hm1 : Measurable fun h : realSU X.Ψ X.Gm => s * h` using `(continuous_const.mul continuous_id).measurable`.

Establish `hm2 : Measurable fun h : H => incl s * h` using `(continuous_const.mul continuous_id).measurable`. Rewrite using `[hνdef, Measure.map_map hm1 hpm, show (fun h => s * h) ∘ p = p ∘ (fun h => incl s * h) from funext fun g => (hpinv s g).symm, ← Measure.map_map hpm hm2, map_mul_left_eq_self]⟩`. Establish `hνfin : IsFiniteMeasureOnCompacts ν` using `⟨fun K hK => by`. Rewrite using `[hνdef, Measure.map_apply hpm hK.measurableSet]`. Establish `hC : IsCompact (Set.range cT)` using `isCompact_range hcTc`.

Establish `hK' : IsCompact (incl '' K)` using `hK.image hinclc`. Use `lt_of_le_of_lt (measure_mono ?_) (hK'.mul hC.inv).measure_lt_top` and prove the remaining obligations. Introduce `g hg`. Use `Set.mem_mul.2 ⟨incl (p g), ⟨p g, hg, rfl⟩, (cU g)⁻¹, Set.inv_mem_inv.2 ⟨tU g, rfl⟩, ?_⟩` and prove the remaining obligations. Establish `: incl (p g) = g * cU g` using `rfl`.

Rewrite using `[this, mul_inv_cancel_right]⟩`. Establish `huniv : ν Set.univ = muF X x Set.univ`. Establish `h1` using `hν (fun _ => 1) measurable_const (fun _ _ _ _ => rfl)`. Simplify using `only [lintegral_const, one_mul] at h1`. Rewrite using `[hνdef, Measure.map_apply hpm MeasurableSet.univ, Set.preimage_univ, h1]`.

Use `haveI := hνinv`. Use `haveI := hνfin`. Establish `hs` using `Measure.isMulLeftInvariant_eq_smul ν (Measure.haar : Measure (realSU X.Ψ X.Gm))`. Establish `hc0 : ν.haarScalarFactor (Measure.haar : Measure (realSU X.Ψ X.Gm)) ≠ 0`. Introduce `h0`.

Apply `FlagQuotHaar.muF_univ_ne_zero X hx` to reduce the goal to its premises. Rewrite using `[← huniv, hs, h0, zero_smul, Measure.coe_zero, Pi.zero_apply]`. Use `⟨ν, ?_, fun φ hφ hφb => ?_⟩` and prove the remaining obligations. Rewrite using `[hs, ENNReal.smul_def]`. Conclude with `Measure.IsHaarMeasure.smul _ (ENNReal.coe_ne_zero.2 hc0) ENNReal.coe_ne_top`.

Establish `hLc : Continuous fun g : realSU X.Ψ X.Gm => X.lmulC (fun τ => (((g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x`. Use `continuous_pi fun τ => ?_` and prove the remaining obligations. Conclude with `((hMc τ).comp continuous_subtype_val).matrix_mul continuous_const`. Establish `hm : Measurable fun g : realSU X.Ψ X.Gm => φ (X.lmulC (fun τ => (((g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x)` using `hφ.comp hLc.measurable`. Rewrite using `[hνdef, lintegral_map hm hpm, ← hν φ hφ hφb]`.

Use `lintegral_congr fun g => ?_` and prove the remaining obligations. Use `show φ (X.lmulC (M (g * cU g).1) x) = φ (X.lmulC (M g.1) x)`. Rewrite using `[hkey g]`. Conclude with `hφb _ (IC.orth_mem_dom X (orth_lmulC X (hU g) hx)) _ (diagF_mem X _)`.
-/
theorem exists_haar_lying_over : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (x : Frame X.Ψ r) [MeasurableSpace (realSU X.Ψ X.Gm)] [BorelSpace (realSU X.Ψ X.Gm)], 1 ≤ r → IsOrth X x →
    ∃ ν : Measure (realSU X.Ψ X.Gm), ν.IsHaarMeasure ∧ ∀ φ : Frame X.Ψ r → ℝ≥0∞, Measurable φ →
      (∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul y b) = φ y) →
      ∫⁻ g, φ (X.lmulC (fun τ => (((g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x) ∂ν =
        ∫⁻ z, φ (cpt X x z) ∂muF X x := by
  intro E _ _ _ r X x _ _ hr hx
  classical
  set H := UnitaryFrames.unitarySubgroup X with hHdef
  letI : MeasurableSpace H := borel H
  haveI : BorelSpace H := ⟨rfl⟩
  have hHm : ∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ) := fun _ => Iff.rfl
  obtain ⟨hLC, hSC, hfr⟩ := UnitaryFrames.unitary_group_frames.2 r X H hHm
  haveI := hLC
  haveI := hSC
  obtain ⟨-, ι, hιc, hι1, -⟩ := hfr x hx
  obtain ⟨νU, hνl, hνf, hν⟩ := invMeas FrameMeasureClosed.measure_statements.2.1
    GramSchmidtCont.exists_continuous_gramSchmidt isOrth_rmul_iff_unitary_diagonal
    (SatFin.muF_sat_lt_top FrameMeasureClosed.measure_statements.2.1)
    UnitaryFrames.unitary_group_frames.2 r X H hHm x hx
  haveI := hνl
  haveI := hνf
  let M : (X.Ψ → GL (Fin r) ℂ) → X.Ψ → Matrix (Fin r) (Fin r) ℂ := fun g τ => (g τ : Matrix (Fin r) (Fin r) ℂ)
  have hU : ∀ g : H, X.IsUnitaryC (M g.1) := fun g => g.2
  have hMmul : ∀ g h : X.Ψ → GL (Fin r) ℂ, ∀ τ, M (g * h) τ = M g τ * M h τ := fun g h τ => by
    simp only [M, Pi.mul_apply, Units.val_mul]
  have hMc : ∀ τ, Continuous fun g : X.Ψ → GL (Fin r) ℂ => M g τ := fun τ =>
    Units.continuous_val.comp (continuous_apply τ)

  let dC : H → X.Ψ → Circle := fun g τ =>
    ⟨(M g.1 τ).det, by simpa [Submonoid.unitSphere] using norm_det_eq_one X hx (hU g) τ⟩
  have hdC : ∀ g τ, ((dC g τ : Circle) : ℂ) = (M g.1 τ).det := fun _ _ => rfl
  let tU : H → Torus X := fun g τ a => if (a : ℕ) = 0 then (dC g τ)⁻¹ else 1
  let cT : Torus X → H := fun t => ι (rmul x (diagF X t))
  let cU : H → H := fun g => cT (tU g)
  have horthT : ∀ t, IsOrth X (rmul x (diagF X t)) := fun t =>
    (isOrth_rmul_iff_unitary_diagonal r X x _ hx (diagF_mem X t)).2 (diagF_unit X t)
  have hcx : ∀ t, X.lmulC (M (cT t).1) x = rmul x (diagF X t) := fun t => hι1 _ (horthT t)

  have hdCc : Continuous dC := continuous_pi fun τ =>
    Continuous.subtype_mk ((hMc τ).comp continuous_subtype_val).matrix_det _
  have htUc : Continuous tU := by
    refine continuous_pi fun τ => continuous_pi fun a => ?_
    by_cases ha : (a : ℕ) = 0
    · simp only [tU, ha, if_true]
      exact ((continuous_apply τ).comp hdCc).inv
    · simp only [tU, ha, if_false]
      exact continuous_const
  have hcTc : Continuous cT := by
    refine hιc.comp_continuous ?_ fun t => horthT t
    exact (continuous_rmul X).comp (continuous_const.prodMk (continuous_diagF X))
  have hcUc : Continuous cU := hcTc.comp htUc

  have hdetc : ∀ (g : H) τ, (M (cU g).1 τ).det * (M g.1 τ).det = 1 := by
    intro g τ
    have h1 := congrArg Matrix.det (congrFun (hcx (tU g)) τ)
    have e1 : X.lmulC (M (cU g).1) x τ = M (cU g).1 τ * mat x τ := rfl
    have e2 : rmul x (diagF X (tU g)) τ = mat x τ * mat (diagF X (tU g)) τ := rfl
    have e3 : (mat (diagF X (tU g)) τ).det = ((M g.1 τ).det)⁻¹ := by
      show (Matrix.diagonal fun a => ((tU g τ a : Circle) : ℂ)).det = _
      rw [Matrix.det_diagonal, Finset.prod_eq_single (⟨0, hr⟩ : Fin r)]
      · simp only [tU, if_true, Circle.coe_inv, hdC]
      · intro b _ hb
        have : (b : ℕ) ≠ 0 := fun h => hb (Fin.ext h)
        simp only [tU, this, if_false, Circle.coe_one]
      · simp
    have hx0 := UnitaryFrames.det_ne_zero_of_isOrth X hx τ
    have hg0 : (M g.1 τ).det ≠ 0 := by
      intro h0
      have := norm_det_eq_one X hx (hU g) τ
      rw [h0, norm_zero] at this
      exact zero_ne_one this

    have h2 : (M (cU g).1 τ).det * (mat x τ).det = (mat x τ).det * ((M g.1 τ).det)⁻¹ := by
      have h1' : (M (cU g).1 τ * mat x τ).det = (mat x τ * mat (diagF X (tU g)) τ).det := by
        rw [← e1, ← e2]; exact h1
      rw [Matrix.det_mul, Matrix.det_mul, e3] at h1'
      exact h1'
    have hi : (M g.1 τ).det * ((M g.1 τ).det)⁻¹ = 1 := mul_inv_cancel₀ hg0
    have h3 : (M (cU g).1 τ).det * (M g.1 τ).det = 1 := by
      apply mul_right_cancel₀ hx0
      linear_combination (M g.1 τ).det * h2 + (mat x τ).det * hi
    exact h3

  have hpmem : ∀ g : H, (g * cU g).1 ∈ realSU X.Ψ X.Gm := by
    intro g τ
    refine ⟨?_, (g * cU g).2 τ⟩
    show (M (g.1 * (cU g).1) τ).det = 1
    rw [hMmul, Matrix.det_mul, mul_comm]
    exact hdetc g τ
  let p : H → realSU X.Ψ X.Gm := fun g => ⟨(g * cU g).1, hpmem g⟩
  have hpc : Continuous p :=
    Continuous.subtype_mk (continuous_subtype_val.comp (continuous_id.mul hcUc)) _
  have hpm : Measurable p := hpc.measurable

  let incl : realSU X.Ψ X.Gm → H := fun s => ⟨s.1, fun τ => (s.2 τ).2⟩
  have hinclc : Continuous incl := Continuous.subtype_mk continuous_subtype_val _
  have hpinv : ∀ (s : (realSU X.Ψ X.Gm)) (g : H), p (incl s * g) = s * p g := by
    intro s g
    have htU : tU (incl s * g) = tU g := by
      have hd : dC (incl s * g) = dC g := by
        funext τ
        apply Subtype.ext
        show (M (s.1 * g.1) τ).det = (M g.1 τ).det
        rw [hMmul, Matrix.det_mul, (s.2 τ).1, one_mul]
      funext τ a
      show (if (a : ℕ) = 0 then (dC (incl s * g) τ)⁻¹ else 1) = (if (a : ℕ) = 0 then (dC g τ)⁻¹ else 1)
      rw [hd]
    apply Subtype.ext
    show (incl s * g).1 * (cT (tU (incl s * g))).1 = s.1 * (g.1 * (cT (tU g)).1)
    rw [htU, Subgroup.coe_mul, mul_assoc]

  have hkey : ∀ g : H, X.lmulC (M (g * cU g).1) x = rmul (X.lmulC (M g.1) x) (diagF X (tU g)) := by
    intro g
    funext τ
    have hc := congrFun (hcx (tU g)) τ
    show M ((g : X.Ψ → GL (Fin r) ℂ) * (cU g).1) τ * mat x τ = (M g.1 τ * mat x τ) * mat (diagF X (tU g)) τ
    have hc' : M (cU g).1 τ * mat x τ = mat x τ * mat (diagF X (tU g)) τ := hc
    rw [hMmul, Matrix.mul_assoc, hc', Matrix.mul_assoc]

  set ν : Measure (realSU X.Ψ X.Gm) := νU.map p with hνdef
  have hνinv : ν.IsMulLeftInvariant := ⟨fun s => by
    have hm1 : Measurable fun h : realSU X.Ψ X.Gm => s * h := (continuous_const.mul continuous_id).measurable
    have hm2 : Measurable fun h : H => incl s * h := (continuous_const.mul continuous_id).measurable
    rw [hνdef, Measure.map_map hm1 hpm,
      show (fun h => s * h) ∘ p = p ∘ (fun h => incl s * h) from funext fun g => (hpinv s g).symm,
      ← Measure.map_map hpm hm2, map_mul_left_eq_self]⟩
  have hνfin : IsFiniteMeasureOnCompacts ν := ⟨fun K hK => by
    rw [hνdef, Measure.map_apply hpm hK.measurableSet]
    have hC : IsCompact (Set.range cT) := isCompact_range hcTc
    have hK' : IsCompact (incl '' K) := hK.image hinclc
    refine lt_of_le_of_lt (measure_mono ?_) (hK'.mul hC.inv).measure_lt_top
    intro g hg
    refine Set.mem_mul.2 ⟨incl (p g), ⟨p g, hg, rfl⟩, (cU g)⁻¹, Set.inv_mem_inv.2 ⟨tU g, rfl⟩, ?_⟩
    have : incl (p g) = g * cU g := rfl
    rw [this, mul_inv_cancel_right]⟩
  have huniv : ν Set.univ = muF X x Set.univ := by
    have h1 := hν (fun _ => 1) measurable_const (fun _ _ _ _ => rfl)
    simp only [lintegral_const, one_mul] at h1
    rw [hνdef, Measure.map_apply hpm MeasurableSet.univ, Set.preimage_univ, h1]
  haveI := hνinv
  haveI := hνfin
  have hs := Measure.isMulLeftInvariant_eq_smul ν (Measure.haar : Measure (realSU X.Ψ X.Gm))
  have hc0 : ν.haarScalarFactor (Measure.haar : Measure (realSU X.Ψ X.Gm)) ≠ 0 := by
    intro h0
    apply FlagQuotHaar.muF_univ_ne_zero X hx
    rw [← huniv, hs, h0, zero_smul, Measure.coe_zero, Pi.zero_apply]
  refine ⟨ν, ?_, fun φ hφ hφb => ?_⟩
  · rw [hs, ENNReal.smul_def]
    exact Measure.IsHaarMeasure.smul _ (ENNReal.coe_ne_zero.2 hc0) ENNReal.coe_ne_top
  · have hLc : Continuous fun g : realSU X.Ψ X.Gm =>
        X.lmulC (fun τ => (((g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x := by
      refine continuous_pi fun τ => ?_
      exact ((hMc τ).comp continuous_subtype_val).matrix_mul continuous_const
    have hm : Measurable fun g : realSU X.Ψ X.Gm =>
        φ (X.lmulC (fun τ => (((g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x) :=
      hφ.comp hLc.measurable
    rw [hνdef, lintegral_map hm hpm, ← hν φ hφ hφb]
    refine lintegral_congr fun g => ?_
    show φ (X.lmulC (M (g * cU g).1) x) = φ (X.lmulC (M g.1) x)
    rw [hkey g]
    exact hφb _ (IC.orth_mem_dom X (orth_lmulC X (hU g) hx)) _ (diagF_mem X _)

end

end GlobalTheory.SUHaarOver
