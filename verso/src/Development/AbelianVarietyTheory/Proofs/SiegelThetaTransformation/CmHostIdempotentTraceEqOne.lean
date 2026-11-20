import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.ThetaSpanAdjoint
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HMatMulVecPerCrd
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilActionPreservesThetaAndInnerProduct
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaSeriesTestFunctionHolomorphicWeight
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelTestFunctionFiniteSumEquivariant
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ProdLevelOneThetaEqVacuumTheta
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaVacuumUnitaryColumnChangeUnitFactor
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaHeisenbergUnitaryColumnChange
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FgOfSmulLe
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ReadsExistsUniqueTheta
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FramedPointGeneratorIsThetaLevelOne
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsEvenRepsTensorLatticeAndSum
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ShortThetaValueComplexPointEqClassicalThetaStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsLiftOfProjective
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DualHalfLevelMarkingExistsAndMatch
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HeisenbergVacuumProjectionRootOfUnityPhasesStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.MultiplierSqMulDetUnitaryColumnChangeStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RootsLevelPointsSameVacuumTranslatesStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.PolyDerivLetterPushforwardEqColumnActionStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.PushforwardPreservesHarmonicPolynomialsAndLatticStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardToMultisetEqDegree

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

namespace GlobalTheory.Phase.ChangePt

section Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g q0 n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ}

/- English proof (translation)
Establish `h2 : 2 * (H.w0 : E) = 1 + (H.rt : E)`. Simplify `congrArg (algebraMap (𝓞 E) E) H.two_weight_eq_one_add_root` using `[map_ofNat]`. Establish `hs : (H.rt : E) ^ 2 = -(H.d : E)`. Simplify using `using congrArg (algebraMap (𝓞 E) E) H.rt_sq`. Establish `hc : cc (H.rt : E) = -(H.rt : E)`.

Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Apply `τ.injective` to reduce the goal to its premises. Establish `h1 : τ (H.rt : E) ^ 2 = -(H.d : ℂ)` using `by rw [← map_pow, hs]; simp`. Establish `hre : (τ (H.rt : E)).re = 0`. Establish `a1` using `congrArg Complex.re h1`.

Establish `a2` using `congrArg Complex.im h1`. Simplify using `[pow_two] at a1 a2`. Establish `hd : (0 : ℝ) < H.d` using `by exact_mod_cast H.d_prime.pos`. Assume the negation of the conclusion as `hne`. Establish `: (τ (H.rt : E)).im = 0`.

Establish `: (τ (H.rt : E)).re * (τ (H.rt : E)).im = 0` using `by linarith`. Conclude with `(mul_eq_zero.1 this).resolve_left hne`. Rewrite `a1` using `[this]`. Use polynomial arithmetic with `[mul_self_nonneg (τ (H.rt : E)).re]`. Rewrite using `[cc, IsCMField.complexEmbedding_complexConj, map_neg]`.

Apply the tactic sequence `apply Complex.ext <;> simp [hre]`. Establish `h3 : 2 * cc (H.w0 : E) = 1 + cc (H.rt : E)`. Use `congrArg (IsCMField.complexConj E) h2` as an intermediate fact. Simplify `this` using `[cc, map_ofNat]`. Establish `: 2 * ((H.w0 : E) + cc (H.w0 : E)) = 2 * 1` using `by linear_combination h2 + h3 + hc`.

Conclude with `mul_left_cancel₀ two_ne_zero this`.
-/
theorem cmHost_idempotent_trace_eq_one (H : Host E) : (H.w0 : E) + cc (H.w0 : E) = 1 := by
  have h2 : 2 * (H.w0 : E) = 1 + (H.rt : E) := by
    simpa [map_ofNat] using congrArg (algebraMap (𝓞 E) E) H.two_weight_eq_one_add_root
  have hs : (H.rt : E) ^ 2 = -(H.d : E) := by
    simpa using congrArg (algebraMap (𝓞 E) E) H.rt_sq
  have hc : cc (H.rt : E) = -(H.rt : E) := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    have h1 : τ (H.rt : E) ^ 2 = -(H.d : ℂ) := by rw [← map_pow, hs]; simp
    have hre : (τ (H.rt : E)).re = 0 := by
      have a1 := congrArg Complex.re h1
      have a2 := congrArg Complex.im h1
      simp [pow_two] at a1 a2
      have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
      by_contra hne
      have : (τ (H.rt : E)).im = 0 := by
        have : (τ (H.rt : E)).re * (τ (H.rt : E)).im = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left hne
      rw [this] at a1
      nlinarith [mul_self_nonneg (τ (H.rt : E)).re]
    rw [cc, IsCMField.complexEmbedding_complexConj, map_neg]
    apply Complex.ext <;> simp [hre]
  have h3 : 2 * cc (H.w0 : E) = 1 + cc (H.rt : E) := by
    have := congrArg (IsCMField.complexConj E) h2
    simpa [cc, map_ofNat] using this
  have : 2 * ((H.w0 : E) + cc (H.w0 : E)) = 2 * 1 := by linear_combination h2 + h3 + hc
  exact mul_left_cancel₀ two_ne_zero this

/- English proof (translation)
Establish `hM : l.Mb ≠ ⊥`. Introduce `h`. Establish `h₁` using `l.prod`. Rewrite `h₁` using `[h, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot]`. Establish `h₂ : l.M = 0` using `by exact_mod_cast h₁`.

Use `l.three_le` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `l.Mb.finiteQuotientOfFreeOfNeBot hM` as an intermediate fact. Use `Dw.fin` as an intermediate fact. Conclude with `Submodule.finite_quotient_smul l.Mb (N := (⊤ : Submodule (𝓞 E) Dw.La)) Module.Finite.fg_top`.
-/
theorem finite_levQ {H : Host E} (Dw : Datum H) (l : Geo.Tor.Level H) : Finite (LevQ Dw l) := by
  have hM : l.Mb ≠ ⊥ := by
    intro h
    have h₁ := l.prod
    rw [h, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot] at h₁
    have h₂ : l.M = 0 := by exact_mod_cast h₁
    have := l.three_le
    omega
  have := l.Mb.finiteQuotientOfFreeOfNeBot hM
  have := Dw.fin
  exact Submodule.finite_quotient_smul l.Mb (N := (⊤ : Submodule (𝓞 E) Dw.La)) Module.Finite.fg_top

/- English proof (translation)
Take `⟨k, hk, h1, h2⟩` from `hT`. Rewrite `h1`, `h2` using `[GenLatCmp.std_eq, GenLatCmp.span_smul_le]`. Establish `hk0 : 0 < k`. Break down `Nat.eq_zero_or_pos k with rfl | hk0` into its components or cases. Rewrite `hk` using `[Nat.coprime_zero_left]`.

Use linear arithmetic over natural numbers and integers. Conclude with `hk0`. Conclude with `⟨GenLatCmp.fg_of_smul_le hk0 h1, (GenLatCmp.unimod_iff Λ.La).1 hU, k, hk0, hk, h1, h2⟩`.
-/
theorem mem_vset (Λ : GenLat E n) {M : ℕ} (hM : 3 ≤ M) (hU : Λ.Unimod) (hT : Λ.TrivAt M) :
    Λ.La ∈ Vset E n M := by
  obtain ⟨k, hk, h1, h2⟩ := hT
  rw [GenLatCmp.std_eq, GenLatCmp.span_smul_le] at h1 h2
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [Nat.coprime_zero_left] at hk
      omega
    · exact hk0
  exact ⟨GenLatCmp.fg_of_smul_le hk0 h1, (GenLatCmp.unimod_iff Λ.La).1 hU, k, hk0, hk, h1, h2⟩

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using UnAct.thA_smul (X := X) (bas := bas) idx x 0 (0 : TF n g)`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, ← ih]`. Conclude with `UnAct.thA_add idx hs hx (hf a) (RecSum.isSB_sum s f hf)`.
-/
theorem thA_sum (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) {T : Type} (s : Finset T) (f : T → TF n g) (hf : ∀ i, IsSB (f i)) :
    thA X bas idx (∑ i ∈ s, f i) x = ∑ i ∈ s, thA X bas idx (f i) x := by
  induction s using Finset.induction_on with
  | empty => simpa using UnAct.thA_smul (X := X) (bas := bas) idx x 0 (0 : TF n g)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    exact UnAct.thA_add idx hs hx (hf a) (RecSum.isSB_sum s f hf)

/- English proof (translation)
Unfold `thP`. Rewrite using `[← Jet.polyDeriv_sum_fun P _ s W _ fun i _ => ThetaHol.differentiable_thA idx hs (hf i) hx, thA_sum idx hs hx s _ fun i => TensVac.sb_smul _ (hf i)]`. Use `congr 1`. Use function extensionality and compare the values at `z`. Simplify using `only [Finset.sum_apply, UnAct.thA_smul, Pi.smul_apply, smul_eq_mul]`.
-/
theorem theta_sum₂ (hr : X.p0 + q0 = r) (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) {T : Type} (s : Finset T) (W : T → ℂ) (f : T → TF n g) (hf : ∀ i, IsSB (f i))
    (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) :
    thP X hr bas idx (∑ i ∈ s, W i • f i) P x = ∑ i ∈ s, W i * thP X hr bas idx (f i) P x := by
  unfold thP
  rw [← Jet.polyDeriv_sum_fun P _ s W _ fun i _ => ThetaHol.differentiable_thA idx hs (hf i) hx,
    thA_sum idx hs hx s _ fun i => TensVac.sb_smul _ (hf i)]
  congr 1
  funext z
  simp only [Finset.sum_apply, UnAct.thA_smul, Pi.smul_apply, smul_eq_mul]

/- English proof (translation)
Establish `h1 (q) : W q • heisG X bas (Y q) (a • u) = (a * W q) • heisG X bas (Y q) u`. Use function extensionality and compare the values at `t`. Simplify using `only [heisG, heisS, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [h1]`.

Rewrite using `[finsum_eq_sum_of_fintype, theta_sum₂ hr idx hs hx _ _ _ fun q => ((heisG_laws E r X g bas idx n hs hn).2.2.2 (Y q) u hu).1, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun q _ => _root_.mul_assoc _ _ _`.
-/
theorem theta_finsum (hr : X.p0 + q0 = r) (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) (hn : Even n)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) {T : Type} [Fintype T] (W : T → ℂ)
    (Y : T → Matrix (Fin n) (Fin r) E) (a : ℂ) {u : TF n g} (hu : IsSB u)
    (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) :
    thP X hr bas idx (∑ᶠ q, W q • heisG X bas (Y q) (a • u)) P x =
      a * ∑ q, W q * thP X hr bas idx (heisG X bas (Y q) u) P x := by
  have h1 (q) : W q • heisG X bas (Y q) (a • u) = (a * W q) • heisG X bas (Y q) u := by
    funext t
    simp only [heisG, heisS, Pi.smul_apply, smul_eq_mul]
    ring
  simp only [h1]
  rw [finsum_eq_sum_of_fintype, theta_sum₂ hr idx hs hx _ _ _
    fun q => ((heisG_laws E r X g bas idx n hs hn).2.2.2 (Y q) u hu).1, Finset.mul_sum]
  exact Finset.sum_congr rfl fun q _ => _root_.mul_assoc _ _ _

omit [IsCMField E] in

/- English proof (translation)
Rewrite using `[← GenLatCmp.std_eq, ← AddSubgroup.inf_relIndex_left]`. Both sides reduce to the same expression.
-/
theorem index_Ln (Λ : GenLat E n) :
    (Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index =
      (stdL E n).toAddSubgroup.relIndex Λ.La.toAddSubgroup := by
  rw [← GenLatCmp.std_eq, ← AddSubgroup.inf_relIndex_left]
  rfl

omit [IsCMField E] in

/- English proof (translation)
Rewrite using `[← index_Ln Λ, GenLat.zCard, GenLat.mIdx, ← mul_pow]`. Use `congr 1`. Conclude with `(AddSubgroup.relIndex_mul_relIndex _ _ _ (Submodule.toAddSubgroup_mono hN.2.2) (Submodule.toAddSubgroup_mono (inf_le_left : Λ.Ln ≤ Λ.La))).symm`.
-/
theorem zCard_eq (Λ : GenLat E n) {N M : ℕ} (hN : Λ.LevOK N M) (r : ℕ) :
    Λ.zCard N r = Λ.mIdx N r * ((stdL E n).toAddSubgroup.relIndex Λ.La.toAddSubgroup) ^ r := by
  rw [← index_Ln Λ, GenLat.zCard, GenLat.mIdx, ← mul_pow]
  congr 1
  exact (AddSubgroup.relIndex_mul_relIndex _ _ _ (Submodule.toAddSubgroup_mono hN.2.2)
    (Submodule.toAddSubgroup_mono (inf_le_left : Λ.Ln ≤ Λ.La))).symm

end Classical

/- English proof (translation)
Substitute `hz` using the available equality. Establish `hm : (m : ℂ) ≠ 0` using `by exact_mod_cast (Nat.pos_of_mul_pos_right hz0).ne'`. Establish `hj : (0 : ℝ) < j` using `by exact_mod_cast Nat.pos_of_mul_pos_left hz0`. Establish `hs : ((Real.sqrt (j : ℝ) : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast (Real.sqrt_pos.2 hj).ne'`. Establish `h2 : (j : ℂ) = ((Real.sqrt (j : ℝ) : ℝ) : ℂ) * ((Real.sqrt (j : ℝ) : ℝ) : ℂ)`.

Conclude with `(Real.mul_self_sqrt hj.le).symm` after adjusting the coercions. Rewrite using `[Nat.cast_mul]`. Generalize the expression as in `((Real.sqrt (j : ℝ) : ℝ) : ℂ) = s at hs h2`. Rewrite using `[h2]`. Clear the denominators using the available nonvanishing facts.
-/
theorem cancel_idx {b κ S Q : ℂ} {m z j : ℕ} (hb : b ≠ 0) (hz0 : 0 < z) (hz : z = m * j) :
    b⁻¹ * (m : ℂ)⁻¹ * Q * (z : ℂ) * κ * ((((Real.sqrt (j : ℝ) : ℝ) : ℂ))⁻¹ * S) * b =
      Q * κ * S * ((Real.sqrt (j : ℝ) : ℝ) : ℂ) := by
  subst hz
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mul_pos_right hz0).ne'
  have hj : (0 : ℝ) < j := by exact_mod_cast Nat.pos_of_mul_pos_left hz0
  have hs : ((Real.sqrt (j : ℝ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hj).ne'
  have h2 : (j : ℂ) = ((Real.sqrt (j : ℝ) : ℝ) : ℂ) * ((Real.sqrt (j : ℝ) : ℝ) : ℂ) := by
    exact_mod_cast (Real.mul_self_sqrt hj.le).symm
  rw [Nat.cast_mul]
  generalize ((Real.sqrt (j : ℝ) : ℝ) : ℂ) = s at hs h2
  rw [h2]
  field_simp

/- English proof (translation)
Introduce `hci E _ _ _ H Dw l Xo c _ r g X bas idx e q0 n hr eL hs hrr hn hdir hty _ nab hnab Λ h hU hh hT hT'`. Establish `hw` using `cmHost_idempotent_trace_eq_one H`. Establish `hwi : IsIntegral ℤ (H.w0 : E)` using `H.w0.isIntegral_coe`. Take `⟨hU', hmv, hu, -⟩` from `(GlobalTheory.T.pushforward_preserves_harmonic_polynomials_and_lattices E H Dw l c n 0 h hh).2 Λ`. Establish `hΛ` using `mem_vset Λ l.three_le hU hT`.

Establish `hΛ'` using `mem_vset (actLat h Λ) l.three_le (hU' hU) hT'`. Establish `hΛ1 : Λ.La ∈ Vset E n 1` using `(GenLatCmp.genLat_vset E n _).2.2.1 1 _ (one_dvd _) hΛ`. Establish `hΛ1' : (actLat h Λ).La ∈ Vset E n 1` using `(GenLatCmp.genLat_vset E n _).2.2.1 1 _ (one_dvd _) hΛ'`. Take `⟨t, ht, hvac⟩` from `thA_vacuum_hAct E r X g bas idx n hs hn _ hwi hw h hu _ hΛ1 _ hΛ1' hmv`. Use `⟨t, ht, fun x L y A hx hL => ?_⟩` and prove the remaining obligations.

Take `⟨⟨v₀, hv₀⟩, -⟩` from `TensVac.vacua E r X g bas idx n hs hn _ hwi hw L hL 1 _ (Base.stdL_mem_Vset n 1)`. Establish `hcol` using `hvac L hL v₀ hv₀ x hx`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `h1` using `GlobalTheory.T.multiplier_sq_mul_det_unitary_column_change E r X g bas idx n hs hn _ hwi hw h hu _ hΛ1 _ hΛ1' L hL v₀ hv₀ x hx t ht hcol`. Establish `h2 : ∏ i : Fin g, rowType X (idx i) h.det = ∏ τ : E →+* ℂ, algebraMap c.F ℂ (embF c τ h.det) ^ Dw.mult τ`.

Simplify using `only [hty]`. Rewrite using `[e.prod_comp (fun ℓ : Lt1 Dw => Formalism.L2.PjFree.relab c (algebraMap c.F ℂ) ℓ.1 h.det), Fintype.prod_sigma]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Simplify using `[Formalism.L2.PjFree.relab]`. Rewrite `h1` using `[h2]`. Then use the resulting hypothesis.

Introduce `wq hwq N N' hN hN' a P hP b b' v v' hb hb' hv hv'`. Take `⟨θ, hθ, -⟩` from `(reads_existsUnique_theta E H Dw l Xo c r g X bas idx e x L y A hs hx hL 1 y.s).1`. Establish `hθ1` using `isTheta1_of_reads_generator E H Dw l Xo c r g X bas idx e x L y A hs hx hL θ hθ`. Take `⟨κ, hκ⟩` from `VacProd.prod_eq_mul_thA E r X g bas idx n hs hn _ hwi hw L hL v₀ hv₀ x hx θ hθ1`. Take `⟨mk, hmk, hA⟩` from `exists_mark E H Dw l Xo c r g X bas idx e x L y A hs hx hL`.

Establish `hroots` using `(DualMark.dual_marking E H Dw l r X L mk _ hL hmk (Complex.isPrimitiveRoot_exp _ l.odd.pos.ne')).2.2.2.2 n`. Take `⟨Y, hY⟩` from `hroots N hN.1.pos`. Take `⟨Y', hY'⟩` from `hroots N' hN'.1.pos`. Establish `e1` using `GlobalTheory.T.shortThetaValue_complexPoint_eq_classicalTheta hci E H Dw l Xo c r g X bas idx e x L y A hs hx hL q0 n hr eL hrr hn hdir nab hnab θ v₀ κ hθ hv₀ hκ mk hmk hA Λ.La hΛ N hN Y hY a P hP wq b v hv`. Establish `e2` using `GlobalTheory.T.shortThetaValue_complexPoint_eq_classicalTheta hci E H Dw l Xo c r g X bas idx e x L y A hs hx hL q0 n hr eL hrr hn hdir nab hnab θ v₀ κ hθ hv₀ hκ mk hmk hA (actLat h Λ).La hΛ' N' hN' Y' hY' a _ ((GlobalTheory.T.pushforward_preserves_harmonic_polynomials_and_lattic …`.

Take `⟨_, -, hproj⟩` from `GlobalTheory.T.heisenbergVacuum_projection_rootOfUnity_phases E r X g bas idx n hs hn _ hwi hw L hL v₀ hv₀`. Take `⟨hu1, -, hp1⟩` from `hproj _ hΛ1`. Take `⟨hu2, -, hp2⟩` from `hproj _ hΛ1'`. Take `⟨⟨σ, hσ⟩, hmove⟩` from `GlobalTheory.T.roots_levelPoints_same_vacuum_translates E H Dw l r X g bas n hs hn L hL mk hmk h hu _ hΛ _ hΛ' hmv N N' hN hN' Y Y' hY hY'`. Take `⟨-, -, -, hz1, -⟩` from `ZLat.exists_reps_sum E r X g bas idx n hs hn _ hwi hw L hL _ hΛ1 N hN.1 (hN.2.2.trans inf_le_left)`.

Take `⟨-, -, -, hz2, -⟩` from `ZLat.exists_reps_sum E r X g bas idx n hs hn _ hwi hw L hL _ hΛ1' N' hN'.1 (hN'.2.2.trans inf_le_left)`. Use `haveI := finite_levQ Dw l`. Use `haveI := Fintype.ofFinite (Fin n → LevQ Dw l)`. Generalize the expression as in `unitv (projA X bas (H.w0 : E) (tens Λ.La L) v₀) = u at hcol hu1 hp1`. Generalize the expression as in `unitv (projA X bas (H.w0 : E) (tens (actLat h Λ).La L) v₀) = u' at hcol hu2 hp2`.

Rewrite `e1` using `[gphi, hp1, theta_finsum hr idx hs hn hx _ _ _ hu1.1]`. Rewrite `e2` using `[gphi, hp2, theta_finsum hr idx hs hn hx _ _ _ hu2.1]`. Establish `hsum : ∑ q, algebraMap c.F ℂ (wq q) * thP X hr bas idx (heisG X bas (Y' q) u') (MvPolynomial.rename eL (MvPolynomial.map (algebraMap c.F ℂ) (pushLet c h P))) x = t * ∑ q, algebraMap c.F ℂ (wq q) * thP X hr bas idx (heisG X bas (Y q) u) (MvPolynomial.rename eL (MvPolynomial.map (a …`. Rewrite using `[← σ.sum_comp, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations.

Establish `hsb` using `((heisG_laws E r X g bas idx n hs hn).2.2.2 (Y q) u hu1.1).1`. Establish `hsb'` using `((heisG_laws E r X g bas idx n hs hn).2.2.2 (h * Y q) u' hu2.1).1`. Establish `han` using `(theta_holomorphic_weight E r X g q0 hr bas idx n hs hn 0 0 _ hsb' 0 (zero_mem _)).2.2.2 x hx`. Rewrite using `[hwq q _ (hσ q), hmove q _ (hσ q) u' hu2, thP, thP, GlobalTheory.T.polyDeriv_letter_pushforward_eq_column_action E H Dw l c _ r g X idx e q0 n hr eL hdir hty h P _ han,`. Use function extensionality and compare the values at `(thA_heisG_hAct E r X g bas idx n hs hn h hu u u' hu1.1 hu2.1 t x hx hcol (Y q)),`.

Use `mul_left_comm t, ← Jet.polyDeriv_smul_fun _ _ (ThetaHol.differentiable_thA idx hs hsb hx)]`. Both sides reduce to the same expression. Rewrite `e2` using `[hsum]`. Simplify using `only [map_mul, map_inv₀, map_natCast] at e1 e2`. Establish `hb0 : algebraMap c.F ℂ b ≠ 0` using `(map_ne_zero _).2 hb`.

Establish `hb0' : algebraMap c.F ℂ b' ≠ 0` using `(map_ne_zero _).2 hb'`. Rewrite using `[index_Ln, index_Ln, ← hrr, e2, cancel_idx hb0' hz2 (zCard_eq _ hN' r), mul_right_comm _ _ v, _root_.mul_assoc t, _root_.mul_comm _ v, e1, cancel_idx hb0 hz1 (zCard_eq _ hN r)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem change_at_point : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (q0 n : ℕ) (hr : X.p0 + q0 = r) (eL : LtN Dw n ≃ Harm.Var X.Ψ q0 X.p0 (Fin n)), IsSympl X bas → r = Dw.p + Dw.q → Even n → (∀ ℓ, letterDir X hr idx (eL ℓ) = Pi.single ℓ.2.2 (Pi.single (e.symm ⟨ℓ.1, ℓ.2.1⟩) 1)) → (∀ j, rowType X (idx j) = Formalism.L2.PjFree.relab c (algebraMap c.F ℂ) (e j).1) → ∀ [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (Λ : GenLat E n) (h : Matrix (Fin n) (Fin n) E), Λ.Unimod → IsUnitaryM h → Λ.TrivAt l.M → (actLat h Λ).TrivAt l.M → ∃ t : ℂ, ‖t‖ = 1 ∧ ∀ (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (_ : AnFib X bas idx e x L y), x ∈ X.dom → SelfD X L → IsMu (t ^ 2 * ∏ τ : E →+* ℂ, algebraMap c.F ℂ (embF c τ h.det) ^ Dw.mult τ) ∧ ∀ (wq : (Fin n → LevQ Dw l) → c.F), FixesDatum c h wq → ∀ N N' : ℕ, Λ.LevOK N l.M → (actLat h Λ).LevOK N' l.M → ∀ (a : (E →+* ℂ) × ℕ → ℕ), ∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), ∀ (b b' : c.F) (v v' : ℂ), b ≠ 0 → b' ≠ 0 → ShortValAt Xo c nab wq Λ b N P y v → ShortValAt Xo c nab wq (actLat h Λ) b' N' (pushLet c h P) y v' → v' * algebraMap c.F ℂ b' * (Real.sqrt (((Λ).Ln.toAddSubgroup.addSubgroupOf (Λ).La.toAddSubgroup).index ^ (Dw.p + Dw.q) : ℕ) : ℝ) = t * algebraMap c.F ℂ b * (Real.sqrt (((actLat h Λ).Ln.toAddSubgroup.addSubgroupOf (actLat h Λ).La.toAddSubgroup).index ^ (Dw.p + Dw.q) : ℕ) : ℝ) * v := by
  intro hci E _ _ _ H Dw l Xo c _ r g X bas idx e q0 n hr eL hs hrr hn hdir hty _ nab hnab Λ h hU hh hT hT'
  have hw := cmHost_idempotent_trace_eq_one H
  have hwi : IsIntegral ℤ (H.w0 : E) := H.w0.isIntegral_coe
  obtain ⟨hU', hmv, hu, -⟩ := (GlobalTheory.T.pushforward_preserves_harmonic_polynomials_and_lattices E H Dw l c n 0 h hh).2 Λ
  have hΛ := mem_vset Λ l.three_le hU hT
  have hΛ' := mem_vset (actLat h Λ) l.three_le (hU' hU) hT'
  have hΛ1 : Λ.La ∈ Vset E n 1 := (GenLatCmp.genLat_vset E n _).2.2.1 1 _ (one_dvd _) hΛ
  have hΛ1' : (actLat h Λ).La ∈ Vset E n 1 := (GenLatCmp.genLat_vset E n _).2.2.1 1 _ (one_dvd _) hΛ'
  obtain ⟨t, ht, hvac⟩ := thA_vacuum_hAct E r X g bas idx n hs hn _ hwi hw h hu _ hΛ1 _ hΛ1' hmv
  refine ⟨t, ht, fun x L y A hx hL => ?_⟩
  obtain ⟨⟨v₀, hv₀⟩, -⟩ := TensVac.vacua E r X g bas idx n hs hn _ hwi hw L hL 1 _ (Base.stdL_mem_Vset n 1)
  have hcol := hvac L hL v₀ hv₀ x hx
  refine ⟨?_, ?_⟩
  · have h1 := GlobalTheory.T.multiplier_sq_mul_det_unitary_column_change E r X g bas idx n hs hn _ hwi hw h hu _ hΛ1 _ hΛ1' L hL v₀ hv₀ x hx t ht hcol
    have h2 : ∏ i : Fin g, rowType X (idx i) h.det =
        ∏ τ : E →+* ℂ, algebraMap c.F ℂ (embF c τ h.det) ^ Dw.mult τ := by
      simp only [hty]
      rw [e.prod_comp (fun ℓ : Lt1 Dw => Formalism.L2.PjFree.relab c (algebraMap c.F ℂ) ℓ.1 h.det), Fintype.prod_sigma]
      refine Finset.prod_congr rfl fun τ _ => ?_
      simp [Formalism.L2.PjFree.relab]
    rwa [h2] at h1
  intro wq hwq N N' hN hN' a P hP b b' v v' hb hb' hv hv'
  obtain ⟨θ, hθ, -⟩ := (reads_existsUnique_theta E H Dw l Xo c r g X bas idx e x L y A hs hx hL 1 y.s).1
  have hθ1 := isTheta1_of_reads_generator E H Dw l Xo c r g X bas idx e x L y A hs hx hL θ hθ
  obtain ⟨κ, hκ⟩ := VacProd.prod_eq_mul_thA E r X g bas idx n hs hn _ hwi hw L hL v₀ hv₀ x hx θ hθ1
  obtain ⟨mk, hmk, hA⟩ := exists_mark E H Dw l Xo c r g X bas idx e x L y A hs hx hL
  have hroots := (DualMark.dual_marking E H Dw l r X L mk _ hL hmk
    (Complex.isPrimitiveRoot_exp _ l.odd.pos.ne')).2.2.2.2 n
  obtain ⟨Y, hY⟩ := hroots N hN.1.pos
  obtain ⟨Y', hY'⟩ := hroots N' hN'.1.pos
  have e1 := GlobalTheory.T.shortThetaValue_complexPoint_eq_classicalTheta hci E H Dw l Xo c r g X bas idx e x L y A hs hx hL q0 n hr eL hrr hn hdir nab hnab
    θ v₀ κ hθ hv₀ hκ mk hmk hA Λ.La hΛ N hN Y hY a P hP wq b v hv
  have e2 := GlobalTheory.T.shortThetaValue_complexPoint_eq_classicalTheta hci E H Dw l Xo c r g X bas idx e x L y A hs hx hL q0 n hr eL hrr hn hdir nab hnab
    θ v₀ κ hθ hv₀ hκ mk hmk hA (actLat h Λ).La hΛ' N' hN' Y' hY' a _
    ((GlobalTheory.T.pushforward_preserves_harmonic_polynomials_and_lattices E H Dw l c n a h hh).1 P hP) wq b' v' hv'
  obtain ⟨_, -, hproj⟩ := GlobalTheory.T.heisenbergVacuum_projection_rootOfUnity_phases E r X g bas idx n hs hn _ hwi hw L hL v₀ hv₀
  obtain ⟨hu1, -, hp1⟩ := hproj _ hΛ1
  obtain ⟨hu2, -, hp2⟩ := hproj _ hΛ1'
  obtain ⟨⟨σ, hσ⟩, hmove⟩ := GlobalTheory.T.roots_levelPoints_same_vacuum_translates E H Dw l r X g bas n hs hn L hL mk hmk h hu _ hΛ _ hΛ' hmv N N' hN hN'
    Y Y' hY hY'
  obtain ⟨-, -, -, hz1, -⟩ := ZLat.exists_reps_sum E r X g bas idx n hs hn _ hwi hw L hL _ hΛ1 N hN.1
    (hN.2.2.trans inf_le_left)
  obtain ⟨-, -, -, hz2, -⟩ := ZLat.exists_reps_sum E r X g bas idx n hs hn _ hwi hw L hL _ hΛ1' N' hN'.1
    (hN'.2.2.trans inf_le_left)
  haveI := finite_levQ Dw l
  haveI := Fintype.ofFinite (Fin n → LevQ Dw l)
  generalize unitv (projA X bas (H.w0 : E) (tens Λ.La L) v₀) = u at hcol hu1 hp1
  generalize unitv (projA X bas (H.w0 : E) (tens (actLat h Λ).La L) v₀) = u' at hcol hu2 hp2
  rw [gphi, hp1, theta_finsum hr idx hs hn hx _ _ _ hu1.1] at e1
  rw [gphi, hp2, theta_finsum hr idx hs hn hx _ _ _ hu2.1] at e2
  have hsum : ∑ q, algebraMap c.F ℂ (wq q) * thP X hr bas idx (heisG X bas (Y' q) u')
        (MvPolynomial.rename eL (MvPolynomial.map (algebraMap c.F ℂ) (pushLet c h P))) x =
      t * ∑ q, algebraMap c.F ℂ (wq q) * thP X hr bas idx (heisG X bas (Y q) u)
        (MvPolynomial.rename eL (MvPolynomial.map (algebraMap c.F ℂ) P)) x := by
    rw [← σ.sum_comp, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    have hsb := ((heisG_laws E r X g bas idx n hs hn).2.2.2 (Y q) u hu1.1).1
    have hsb' := ((heisG_laws E r X g bas idx n hs hn).2.2.2 (h * Y q) u' hu2.1).1
    have han := (theta_holomorphic_weight E r X g q0 hr bas idx n hs hn 0 0 _ hsb' 0 (zero_mem _)).2.2.2 x hx
    rw [hwq q _ (hσ q), hmove q _ (hσ q) u' hu2, thP, thP,
      GlobalTheory.T.polyDeriv_letter_pushforward_eq_column_action E H Dw l c _ r g X idx e q0 n hr eL hdir hty h P _ han,
      funext (thA_heisG_hAct E r X g bas idx n hs hn h hu u u' hu1.1 hu2.1 t x hx hcol (Y q)),
      mul_left_comm t, ← Jet.polyDeriv_smul_fun _ _ (ThetaHol.differentiable_thA idx hs hsb hx)]
    rfl
  rw [hsum] at e2
  simp only [map_mul, map_inv₀, map_natCast] at e1 e2
  have hb0 : algebraMap c.F ℂ b ≠ 0 := (map_ne_zero _).2 hb
  have hb0' : algebraMap c.F ℂ b' ≠ 0 := (map_ne_zero _).2 hb'
  rw [index_Ln, index_Ln, ← hrr, e2, cancel_idx hb0' hz2 (zCard_eq _ hN' r), mul_right_comm _ _ v,
    _root_.mul_assoc t, _root_.mul_comm _ v, e1, cancel_idx hb0 hz1 (zCard_eq _ hN r)]
  ring

end GlobalTheory.Phase.ChangePt
