import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelSigBijective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntMemModelSmall
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProdZpowLe
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TowerWeightOfZeroStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GoodOriginModelComponentBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.WeightSectionComponentValueStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CompleteDvrPadicEmbeddingStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TraceIntegralSubringExtensionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartLatticeSpecializationValueStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntegralFrameComponentValueStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformAllRootOriginBoundStatement
import Formalism.PadicSubsetSums.StableGradedCounts.ZBrauerNesbitt
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

namespace GlobalTheory.CompanionTheory.Ar.Plug
open FinTr

/- English proof (translation)
Introduce `hG E _ _ _ _ H Dw l Xo c r U h e hL hUn Y _ T o B b Fr Z Rd u s hs f hf hfZ hev p la hp hla v hv`. Take `⟨⟨q, T₀, io, e₀, ho, y, hy, η, hη, rfl⟩, rfl⟩` from `hv`. Use `show _ ≤ nval T₀.V e₀ (evI y f)`. Use `haveI hpf : Fact p.Prime := ⟨hp⟩`. Distinguish the cases in `hy0 : evI y f = 0`.

Rewrite using `[hy0, nval_zero]`. Conclude with `le_top`. Establish `hon : (letI` using `io.toAlgebra; GlobalTheory.AllWt.LiesOn Z y.1) := by`. Use `letI := io.toAlgebra`. Assume the negation of the conclusion as `hc`.

Conclude with `hy0 (GlobalTheory.AllWt.mem_suppOn.1 hfZ T₀.Fr y.1 ((GlobalTheory.AllWt.liesOff_iff Z y.1).2 hc))`. Establish `hLk` using `GlobalTheory.T.good_origin_model_component_bound hG E H Dw l Xo c r U h e hL Y T o _ _ Y _ _ _ _ (o.toTowerOrigin.Or B b) Fr Z Rd`. Establish `hram : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ o.toTowerOrigin.S B` using `fun p hp hd => by`. Rewrite using `[o.toTowerOrigin.S_iff]`. Use `⟨hp, Or.inr ((o.toTowerOrigin.bad_iff p).2 ⟨hp, ?_⟩)⟩` and prove the remaining obligations.

Conclude with `Dvd.dvd.mul_right (Dvd.dvd.mul_left hd 2) _`. Set `RM` to `T.M B b`. Set `Ow` to `o.toTowerOrigin.Or B b`. Set `x : RM.Ω` to `s / gauge Rd u`. Set `sc : (∀ k, RM.ι k) → RM.Ω` to `fun c' => s * ∏ k, RM.y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) * degOf RM u k))`.

Set `rt : (∀ k, RM.ι k) × (Σ k, RM.ι k) → RM.Ω` to `fun q => RM.y q.2 / RM.y ⟨q.2.1, q.1 q.2.1⟩`. Set `B₁ : Finset RM.Ω` to `{x, Rd.φ (evC h Z f)} ∪ Finset.univ.image sc ∪ Finset.univ.image rt`. Take `⟨B₂, B₃, hR⟩` from `GlobalTheory.T.uniform_all_root_origin_bound hG E H Dw l Xo c r U h e hL hUn _ _ Y _ RM _ _ Ow Fr Z Rd (o.omVB B b) hram hLk B₁`. Establish `hfinr : 0 < (letI` using `Rd.φ.toAlgebra; Module.finrank (Om Z) RM.Ω) := by`. Rewrite using `[Rd.deg]`.

Conclude with `Test.deg_pos Ow`. Establish `hfin : (letI` using `Rd.φ.toAlgebra; FiniteDimensional (Om Z) RM.Ω) := by`. Use `letI := Rd.φ.toAlgebra`. Conclude with `Module.finite_of_finrank_pos hfinr`. Use `haveI : CharZero (Om Z) := charZero_of_injective_algebraMap (algebraMap c.F (Om Z)).injective`.

Take `⟨Btr, hTr⟩` from `GlobalTheory.T.trace_integral_subring_extension (Om Z) RM.Ω Rd.φ (B₁ ∪ B₂) x hfin`. Take `⟨T', io', e', y', A', ev, ho', hy', hval, hB, -, halg, hreg⟩` from `GlobalTheory.T.weight_section_component_value hG E H Dw l Xo c r U h e hL Y Z u f hf (Btr ∪ B₃) la T₀ io e₀ ho y hy hon hy0`. Establish `hB3 : (↑B₃ : Set (Om Z)) ⊆ A'` using `fun b hb => hB (Finset.mem_coe.2 (Finset.mem_union_right _ (Finset.mem_coe.1 hb)))`. Take `⟨ι, hι⟩` from `GlobalTheory.T.complete_dvr_padic_embedding E H l c la T' io' e' p ho' hy' hla`. Take `⟨A, hA, hB0, hx, ht, hspec⟩` from `hTr A' (fun b hb => hB (Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_coe.1 hb))))`.

Establish `halgC : ∀ a, IsAlgebraic ℤ ((ι.comp ev) a)` using `fun a => by`. Take `⟨P, hP0, hP⟩` from `halg a`. Use `⟨P, hP0, ?_⟩` and prove the remaining obligations. Rewrite `hP`, the goal using `[Polynomial.aeval_def]`. Establish `e2 : ι.comp (algebraMap ℤ T'.Fr) = algebraMap ℤ (PadicAlgCl p)` using `RingHom.ext_int _ _`.

Use `show Polynomial.eval₂ (algebraMap ℤ (PadicAlgCl p)) (ι (ev a)) P = 0`. Rewrite using `[← e2, ← Polynomial.hom_eval₂, hP, map_zero]`. Take `⟨n, ev', h1, h2, h3⟩` from `hspec (PadicAlgCl p) (ι.comp ev) halgC`. Establish `hcf : evC h Z f ∈ A'`. Establish `e1 : evC h Z f = (letI` using `Rd.φ.toAlgebra; Algebra.trace (Om Z) RM.Ω x) := hev`.

Rewrite using `[e1]`. Conclude with `ht`. Establish `hy'0 : evI y' f ≠ 0` using `fun h0 => by`. Rewrite `hval` using `[h0, nval_zero, nval_of_ne hy0]`. Conclude with `EReal.coe_ne_top _ hval.symm`.

Establish `hW0` using `GlobalTheory.T.integral_frame_component_value E H Dw l Xo c r U h e hL Z _ f hf T' io' y' A' ev hreg hy'0 hcf`. Take `⟨W, hWdef⟩ : ∃ W, W = ι (ev ⟨_, hcf⟩)` from `⟨_, rfl⟩`. Establish `hW : W ≠ 0` using `by rw [hWdef]; exact (map_ne_zero ι).2 hW0`. Establish `hWsum : W = ∑ j, ev' j ⟨x, hx⟩`. Establish `e1 : (⟨evC h Z f, hcf⟩ : A') = ⟨_, ht⟩` using `Subtype.ext hev`.

Rewrite using `[hWdef, e1]`. Conclude with `h3`. Establish `hra : 0 < ramOverZ la` using `FinRd.ram_pos hla`. Establish `hra' : (0 : ℝ) < ramOverZ la` using `by exact_mod_cast hra`. Take `⟨s₀, hs₀⟩ : ∃ s₀ : ℝ, nval T'.V e' (evI y' f) = ((ramOverZ la * s₀ : ℝ) : EReal)` from `⟨((vV T'.V (evI y' f) : ℝ) / e') / ramOverZ la, by`.

Rewrite using `[nval_of_ne hy'0]`. Use `congr 1`. Use the proof step `field_simp⟩`. Take `⟨hw1, -, -, hw4, hw5, -⟩` from `GlobalTheory.T.tower_weight_of_zero E H Dw l Xo c RM u`. Establish `hn : ∀ j, (nOf u j : ℝ) = RM.coef (towerWt Dw (GlobalTheory.AllWt.wtOf Dw u 0).1) 0 j`.

Rewrite using `[hw1]`. Conclude with `hw4`. Establish `hL1 : ∑ r : RootIx Dw, |((-u r.1 r.2 : ℤ) : ℝ)| = GlobalTheory.CovHt.l1 u`. Rewrite using `[hw5]`. Simplify using `[Top.l1, reW, Fintype.sum_prod_type]`.

Establish `hfsec : f ∈ Rec.secZ Xo c (GlobalTheory.AllWt.wtOf Dw u 0).1`. Rewrite using `[← Test.secZ_eq]`. Conclude with `hf`. Establish `hpp : (0 : ℝ) < p` using `by exact_mod_cast hp.pos`. Establish `hlog : 0 < Real.log p` using `Real.log_pos (by exact_mod_cast hp.one_lt)`.

Take `⟨Cθ, hCθ⟩ : ∃ Cθ : ℝ, Cθ = if p ∈ o.toTowerOrigin.S B then 1 / ((p : ℝ) - 1) + (if p = 2 then 1 else 0) + (padicValInt p (discr E) : ℝ) / Module.finrank ℚ E else 0` from `⟨_, rfl⟩`. Take `⟨Ee, hEe⟩ : ∃ Ee : ℝ, Ee = Real.exp (GlobalTheory.CovHt.l1 u * (Cθ * Real.log p))` from `⟨_, rfl⟩`. Establish `hEp : 0 < Ee` using `by rw [hEe]; exact Real.exp_pos _`. Establish `hAB1 : ∀ b ∈ B₁, b ∈ A` using `fun b hb => hB0 (Finset.mem_coe.2 (Finset.mem_union_left _ hb))`. Establish `hmx : x ∈ B₁` using `Finset.mem_union_left _ (Finset.mem_union_left _ (by simp))`.

Establish `hmφ : Rd.φ (evC h Z f) ∈ B₁` using `Finset.mem_union_left _ (Finset.mem_union_left _ (by simp))`. Establish `hmsc : ∀ c', sc c' ∈ B₁` using `fun c' => Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem sc (Finset.mem_univ c')))`. Establish `hmrt : ∀ q, rt q ∈ B₁` using `fun q => Finset.mem_union_right _ (Finset.mem_image_of_mem rt (Finset.mem_univ q))`. Establish `hj : ∀ j, ‖ev' j ⟨x, hx⟩‖ ≤ (p : ℝ) ^ s₀ * (Ee * ‖W‖)`. Introduce `j`.

Take `⟨z, hz, rec, hHV, hrec, hrd⟩` from `hR A (fun b hb => hAB1 b (Finset.mem_coe.1 hb)) (fun b hb => hB0 (Finset.mem_coe.2 (Finset.mem_union_right _ (Finset.mem_coe.1 hb)))) A' hB3 p (ev' j) (h2 j) la T' io' e' y' ι ev hla ho' hy' hι hreg (fun a' => ⟨hA a', h1 j a'⟩)`. Establish `hHV' : ∀ b (hb : b ∈ B₁), Small.HasVal RM.y 0 b z (ev' j ⟨b, hAB1 b hb⟩)` using `fun b hb => hHV b _ hb`. Take `⟨w, hw, hwle⟩` from `GlobalTheory.T.chart_lattice_specialization_value RM.K RM.ι RM.Ω RM.y (PadicAlgCl p) z hz.1 A (ev' j) (degOf RM u) s hs (fun c' _ => ⟨fun k i => ⟨hAB1 _ (hmrt (c', ⟨k, i⟩)), hHV' _ (hmrt (c', ⟨k, i⟩))⟩, ⟨hAB1 _ (hmsc c'), hHV' _ (hmsc c')⟩⟩)`. Take `⟨v, hv, hvn⟩` from `hrd _ (nOf u) hn f hfsec`. Establish `hx1` using `hHV' x hmx`.

Establish `hφ` using `hHV' _ hmφ`. Establish `hW' : ev' j ⟨Rd.φ (evC h Z f), hAB1 _ hmφ⟩ = W` using `by rw [hWdef]; exact h1 j ⟨_, hcf⟩`. Rewrite `hφ` using `[hW']`. Establish `hid : s * Rd.φ (evC h Z f) = x * (Fr.rd f * ∏ r, Ow.e r ^ (-nOf u (some r)))`. Rewrite using `[← Test.gauge_mul Rd u hf]`.

Establish `hg` using `Test.gauge_ne_zero Rd u`. Simplify using `only [x]`. Clear the denominators using the available nonvanishing facts. Establish `ha` using `FinRd.hv_mul hw hφ`. Establish `hb` using `FinRd.hv_mul hx1 hv`.

Rewrite `ha` using `[add_zero]`. Rewrite `hb` using `[zero_add, ← hid]`. Establish `heq : w * W = ev' j ⟨x, hAB1 x hmx⟩ * v` using `Small.ReadFinTest.hasVal_unique hz.1 ha hb`. Establish `hsp : ∀ a : RM.K → ℤ, 0 < Small.supMet a z` using `fun a => Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.2 fun h0 => by`. Take `⟨i, hi⟩` from `hz.1.1 k`.

Conclude with `hi (congrFun h0 i)) _`. Establish `hsup : Small.supMet (degOf RM u) z ≤ (∏ r, rec r ^ nOf u (some r)) * Ee`. Rewrite using `[Test.degOf_eq, supMet_sum _ _ z hz.1.1, hEe, ← hL1]`. Conclude with `prod_zpow_le (fun r => Small.supMet (RM.xdeg r) z) rec (fun r => -u r.1 r.2) _ (fun r => hsp _) (fun r => (hrec r).1) (fun r => by rw [← hCθ] at *; exact (hrec r).2)`. Establish `hP : 0 < ∏ r, rec r ^ nOf u (some r)` using `Finset.prod_pos fun r _ => zpow_pos (hrec r).1 _`.

Establish `hvv` using `hvn s₀ hs₀`. Establish `h5 : ‖ev' j ⟨x, hx⟩‖ * ((p : ℝ) ^ (-s₀) * ∏ r, rec r ^ nOf u (some r)) ≤ ((∏ r, rec r ^ nOf u (some r)) * Ee) * ‖W‖`. Rewrite using `[← hvv, ← norm_mul, ← heq, norm_mul]`. Conclude with `mul_le_mul_of_nonneg_right (hwle.trans hsup) (norm_nonneg _)`. Establish `h6 : ‖ev' j ⟨x, hx⟩‖ * (p : ℝ) ^ (-s₀) ≤ Ee * ‖W‖`.

Use `le_of_mul_le_mul_right ?_ hP` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Establish `h7 : (p : ℝ) ^ s₀ * (p : ℝ) ^ (-s₀) = 1`. Rewrite using `[← Real.rpow_add hpp]`. Simplify using the standard rewrite rules.

Combine the equalities or inequalities in the displayed calculation. Take the linear combination `(-‖ev' j ⟨x, hx⟩‖) * h7`. Use `_ ≤ _ := mul_le_mul_of_nonneg_left h6 (Real.rpow_pos_of_pos hpp _).le`. Establish `hWle : ‖W‖ ≤ (p : ℝ) ^ s₀ * (Ee * ‖W‖)`. Establish `h0 : 0 ≤ (p : ℝ) ^ s₀ * (Ee * ‖W‖)` using `by positivity`.

Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg h0 (fun j (_ : j ∈ Finset.univ) => hj j)` as an intermediate fact. Rewrite `this` using `[← hWsum]`. Then use the resulting hypothesis. Establish `hWp : 0 < ‖W‖` using `norm_pos_iff.2 hW`. Establish `h8 : 1 ≤ (p : ℝ) ^ s₀ * Ee`. Use `le_of_mul_le_mul_right ?_ hWp` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Establish `h9 : 0 ≤ s₀ + GlobalTheory.CovHt.l1 u * Cθ`. Rewrite `h8` using `[Real.rpow_def_of_pos hpp, hEe, ← Real.exp_add]`. Establish `h10` using `Real.exp_le_exp.1 (by simpa using h8 : Real.exp 0 ≤ _)`. Establish `h11 : 0 ≤ Real.log p * (s₀ + GlobalTheory.CovHt.l1 u * Cθ)` using `by linarith`.

Conclude with `(mul_nonneg_iff_of_pos_left hlog).1 h11`. Establish `hres : Formalism.L2.Pj.resCharOf la = p`. Assume the negation of the conclusion as `hne`. Use `Formalism.L2.Pj.Crude.crv_not_mem la (fun hd => hne ?_) hla` and prove the remaining obligations. Conclude with `(Nat.prime_dvd_prime_iff_eq (Formalism.L2.Pj.Crude.resCharOf_prime la) hp).1 hd`.

Establish `hvp : (vLa la (p : c.F) : ℝ) = ramOverZ la`. Use `Formalism.L2.Pj.Crude.crv_vLa_char la` as an intermediate fact. Rewrite `this` using `[hres]`. Conclude with `this` after adjusting the coercions. Establish `hl0 : 0 ≤ GlobalTheory.CovHt.l1 u`.

Rewrite using `[← hL1]`. Conclude with `Finset.sum_nonneg fun _ _ => abs_nonneg _`. Establish `hex : Cθ ≤ if p ∈ o.toTowerOrigin.S B then exTwo E p else 0`. Rewrite using `[hCθ]`. Use `split_ifs with h1' h2'`.

Simplify using `only [exTwo, GlobalTheory.CovHt.htEx, if_pos h2', padicValInt]`. Establish `: (0 : ℝ) ≤ (padicValNat p (discr E).natAbs : ℝ) / Module.finrank ℚ E` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `only [exTwo, GlobalTheory.CovHt.htEx, if_neg h2', padicValInt]`. Establish `: (0 : ℝ) ≤ (padicValNat p (discr E).natAbs : ℝ) / Module.finrank ℚ E` using `by positivity`.

Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `le_rfl`. Rewrite using `[← hval, hs₀]`. Use `EReal.coe_le_coe_iff.2 ?_` and prove the remaining obligations. Rewrite using `[hvp]`.

Establish `h12` using `mul_nonneg hra'.le h9`. Establish `h13` using `mul_nonneg (mul_nonneg hra'.le hl0) (sub_nonneg.2 hex)`. Use polynomial arithmetic with `[h12, h13]`.
-/
theorem vs_fin : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → Ref.UnifAll Xo c → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (B : ℕ) (b : T.Comp) (Fr : Small.GenFrame (o.toTowerOrigin.Or B b)) (Z : Comp Xo c) (Rd : Reading Fr h Z) (u : GlobalTheory.AllWt.Weight Dw), ∀ s ∈ chartLatNm (T.M B b).y (degOf (T.M B b) u) 1, ∀ f ∈ GlobalTheory.AllWt.secZ Xo c (GlobalTheory.AllWt.exOf Dw u 0), f ∈ GlobalTheory.AllWt.suppOn Z → evC h Z f = trOf Rd u s → ∀ (p : ℕ) (la : HeightOneSpectrum (𝓞 c.F)), p.Prime → ((p : ℕ) : 𝓞 c.F) ∈ la.asIdeal → ∀ v ∈ (GlobalTheory.CompHt.recVals Xo c).1 la, ((-((vLa la (p : c.F) : ℝ) * (if p ∈ o.toTowerOrigin.S B then exTwo E p else 0) * GlobalTheory.CovHt.l1 u) : ℝ) : EReal) ≤ v f := by
  intro hG E _ _ _ _ H Dw l Xo c r U h e hL hUn Y _ T o B b Fr Z Rd u s hs f hf hfZ hev p la hp hla v hv
  obtain ⟨⟨q, T₀, io, e₀, ho, y, hy, η, hη, rfl⟩, rfl⟩ := hv
  show _ ≤ nval T₀.V e₀ (evI y f)
  haveI hpf : Fact p.Prime := ⟨hp⟩
  by_cases hy0 : evI y f = 0
  · rw [hy0, nval_zero]; exact le_top
  have hon : (letI := io.toAlgebra; GlobalTheory.AllWt.LiesOn Z y.1) := by
    letI := io.toAlgebra
    by_contra hc
    exact hy0 (GlobalTheory.AllWt.mem_suppOn.1 hfZ T₀.Fr y.1 ((GlobalTheory.AllWt.liesOff_iff Z y.1).2 hc))
  have hLk := GlobalTheory.T.good_origin_model_component_bound hG E H Dw l Xo c r U h e hL Y T o _ _ Y _ _ _ _ (o.toTowerOrigin.Or B b) Fr Z Rd
  have hram : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ o.toTowerOrigin.S B := fun p hp hd => by
    rw [o.toTowerOrigin.S_iff]
    refine ⟨hp, Or.inr ((o.toTowerOrigin.bad_iff p).2 ⟨hp, ?_⟩)⟩
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_left hd 2) _
  classical
  let RM := T.M B b
  let Ow := o.toTowerOrigin.Or B b
  let x : RM.Ω := s / gauge Rd u
  let sc : (∀ k, RM.ι k) → RM.Ω := fun c' => s * ∏ k, RM.y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) * degOf RM u k))
  let rt : (∀ k, RM.ι k) × (Σ k, RM.ι k) → RM.Ω := fun q => RM.y q.2 / RM.y ⟨q.2.1, q.1 q.2.1⟩
  let B₁ : Finset RM.Ω := {x, Rd.φ (evC h Z f)} ∪ Finset.univ.image sc ∪ Finset.univ.image rt
  obtain ⟨B₂, B₃, hR⟩ := GlobalTheory.T.uniform_all_root_origin_bound hG E H Dw l Xo c r U h e hL hUn _ _ Y _ RM _ _ Ow Fr Z Rd (o.omVB B b) hram hLk B₁
  have hfinr : 0 < (letI := Rd.φ.toAlgebra; Module.finrank (Om Z) RM.Ω) := by
    rw [Rd.deg]; exact Test.deg_pos Ow
  have hfin : (letI := Rd.φ.toAlgebra; FiniteDimensional (Om Z) RM.Ω) := by
    letI := Rd.φ.toAlgebra
    exact Module.finite_of_finrank_pos hfinr
  haveI : CharZero (Om Z) := charZero_of_injective_algebraMap (algebraMap c.F (Om Z)).injective
  obtain ⟨Btr, hTr⟩ := GlobalTheory.T.trace_integral_subring_extension (Om Z) RM.Ω Rd.φ (B₁ ∪ B₂) x hfin
  obtain ⟨T', io', e', y', A', ev, ho', hy', hval, hB, -, halg, hreg⟩ :=
    GlobalTheory.T.weight_section_component_value hG E H Dw l Xo c r U h e hL Y Z u f hf (Btr ∪ B₃) la T₀ io e₀ ho y hy hon hy0

  have hB3 : (↑B₃ : Set (Om Z)) ⊆ A' := fun b hb =>
    hB (Finset.mem_coe.2 (Finset.mem_union_right _ (Finset.mem_coe.1 hb)))
  obtain ⟨ι, hι⟩ := GlobalTheory.T.complete_dvr_padic_embedding E H l c la T' io' e' p ho' hy' hla
  obtain ⟨A, hA, hB0, hx, ht, hspec⟩ := hTr A' (fun b hb =>
    hB (Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_coe.1 hb))))
  have halgC : ∀ a, IsAlgebraic ℤ ((ι.comp ev) a) := fun a => by
    obtain ⟨P, hP0, hP⟩ := halg a
    refine ⟨P, hP0, ?_⟩
    rw [Polynomial.aeval_def] at hP ⊢
    have e2 : ι.comp (algebraMap ℤ T'.Fr) = algebraMap ℤ (PadicAlgCl p) := RingHom.ext_int _ _
    show Polynomial.eval₂ (algebraMap ℤ (PadicAlgCl p)) (ι (ev a)) P = 0
    rw [← e2, ← Polynomial.hom_eval₂, hP, map_zero]
  obtain ⟨n, ev', h1, h2, h3⟩ := hspec (PadicAlgCl p) (ι.comp ev) halgC
  have hcf : evC h Z f ∈ A' := by
    have e1 : evC h Z f = (letI := Rd.φ.toAlgebra; Algebra.trace (Om Z) RM.Ω x) := hev
    rw [e1]; exact ht
  have hy'0 : evI y' f ≠ 0 := fun h0 => by
    rw [h0, nval_zero, nval_of_ne hy0] at hval
    exact EReal.coe_ne_top _ hval.symm
  have hW0 := GlobalTheory.T.integral_frame_component_value E H Dw l Xo c r U h e hL Z _ f hf T' io' y' A' ev hreg hy'0 hcf
  obtain ⟨W, hWdef⟩ : ∃ W, W = ι (ev ⟨_, hcf⟩) := ⟨_, rfl⟩
  have hW : W ≠ 0 := by rw [hWdef]; exact (map_ne_zero ι).2 hW0
  have hWsum : W = ∑ j, ev' j ⟨x, hx⟩ := by
    have e1 : (⟨evC h Z f, hcf⟩ : A') = ⟨_, ht⟩ := Subtype.ext hev
    rw [hWdef, e1]
    exact h3
  have hra : 0 < ramOverZ la := FinRd.ram_pos hla
  have hra' : (0 : ℝ) < ramOverZ la := by exact_mod_cast hra
  obtain ⟨s₀, hs₀⟩ : ∃ s₀ : ℝ, nval T'.V e' (evI y' f) = ((ramOverZ la * s₀ : ℝ) : EReal) :=
    ⟨((vV T'.V (evI y' f) : ℝ) / e') / ramOverZ la, by
      rw [nval_of_ne hy'0]; congr 1; field_simp⟩
  obtain ⟨hw1, -, -, hw4, hw5, -⟩ := GlobalTheory.T.tower_weight_of_zero E H Dw l Xo c RM u
  have hn : ∀ j, (nOf u j : ℝ) = RM.coef (towerWt Dw (GlobalTheory.AllWt.wtOf Dw u 0).1) 0 j := by
    rw [hw1]; exact hw4
  have hL1 : ∑ r : RootIx Dw, |((-u r.1 r.2 : ℤ) : ℝ)| = GlobalTheory.CovHt.l1 u := by
    rw [hw5]
    simp [Top.l1, reW, Fintype.sum_prod_type]
  have hfsec : f ∈ Rec.secZ Xo c (GlobalTheory.AllWt.wtOf Dw u 0).1 := by
    rw [← Test.secZ_eq]; exact hf
  have hpp : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlog : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  obtain ⟨Cθ, hCθ⟩ : ∃ Cθ : ℝ, Cθ = if p ∈ o.toTowerOrigin.S B then 1 / ((p : ℝ) - 1) + (if p = 2 then 1 else 0) +
      (padicValInt p (discr E) : ℝ) / Module.finrank ℚ E else 0 := ⟨_, rfl⟩
  obtain ⟨Ee, hEe⟩ : ∃ Ee : ℝ, Ee = Real.exp (GlobalTheory.CovHt.l1 u * (Cθ * Real.log p)) := ⟨_, rfl⟩
  have hEp : 0 < Ee := by rw [hEe]; exact Real.exp_pos _
  have hAB1 : ∀ b ∈ B₁, b ∈ A := fun b hb => hB0 (Finset.mem_coe.2 (Finset.mem_union_left _ hb))
  have hmx : x ∈ B₁ := Finset.mem_union_left _ (Finset.mem_union_left _ (by simp))
  have hmφ : Rd.φ (evC h Z f) ∈ B₁ := Finset.mem_union_left _ (Finset.mem_union_left _ (by simp))
  have hmsc : ∀ c', sc c' ∈ B₁ := fun c' =>
    Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem sc (Finset.mem_univ c')))
  have hmrt : ∀ q, rt q ∈ B₁ := fun q =>
    Finset.mem_union_right _ (Finset.mem_image_of_mem rt (Finset.mem_univ q))
  have hj : ∀ j, ‖ev' j ⟨x, hx⟩‖ ≤ (p : ℝ) ^ s₀ * (Ee * ‖W‖) := by
    intro j
    obtain ⟨z, hz, rec, hHV, hrec, hrd⟩ := hR A (fun b hb => hAB1 b (Finset.mem_coe.1 hb))
      (fun b hb => hB0 (Finset.mem_coe.2 (Finset.mem_union_right _ (Finset.mem_coe.1 hb)))) A' hB3 p (ev' j) (h2 j)
      la T' io' e' y' ι ev hla ho' hy' hι hreg (fun a' => ⟨hA a', h1 j a'⟩)
    have hHV' : ∀ b (hb : b ∈ B₁), Small.HasVal RM.y 0 b z (ev' j ⟨b, hAB1 b hb⟩) := fun b hb => hHV b _ hb
    obtain ⟨w, hw, hwle⟩ := GlobalTheory.T.chart_lattice_specialization_value RM.K RM.ι RM.Ω RM.y (PadicAlgCl p) z hz.1 A (ev' j) (degOf RM u) s hs
      (fun c' _ => ⟨fun k i => ⟨hAB1 _ (hmrt (c', ⟨k, i⟩)), hHV' _ (hmrt (c', ⟨k, i⟩))⟩,
        ⟨hAB1 _ (hmsc c'), hHV' _ (hmsc c')⟩⟩)
    obtain ⟨v, hv, hvn⟩ := hrd _ (nOf u) hn f hfsec
    have hx1 := hHV' x hmx
    have hφ := hHV' _ hmφ
    have hW' : ev' j ⟨Rd.φ (evC h Z f), hAB1 _ hmφ⟩ = W := by rw [hWdef]; exact h1 j ⟨_, hcf⟩
    rw [hW'] at hφ
    have hid : s * Rd.φ (evC h Z f) = x * (Fr.rd f * ∏ r, Ow.e r ^ (-nOf u (some r))) := by
      rw [← Test.gauge_mul Rd u hf]
      have hg := Test.gauge_ne_zero Rd u
      simp only [x]
      field_simp
    have ha := FinRd.hv_mul hw hφ
    have hb := FinRd.hv_mul hx1 hv
    rw [add_zero] at ha
    rw [zero_add, ← hid] at hb
    have heq : w * W = ev' j ⟨x, hAB1 x hmx⟩ * v := Small.ReadFinTest.hasVal_unique hz.1 ha hb
    have hsp : ∀ a : RM.K → ℤ, 0 < Small.supMet a z := fun a =>
      Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.2 fun h0 => by
        obtain ⟨i, hi⟩ := hz.1.1 k
        exact hi (congrFun h0 i)) _
    have hsup : Small.supMet (degOf RM u) z ≤ (∏ r, rec r ^ nOf u (some r)) * Ee := by
      rw [Test.degOf_eq, supMet_sum _ _ z hz.1.1, hEe, ← hL1]
      exact prod_zpow_le (fun r => Small.supMet (RM.xdeg r) z) rec (fun r => -u r.1 r.2) _ (fun r => hsp _)
        (fun r => (hrec r).1) (fun r => by rw [← hCθ] at *; exact (hrec r).2)
    have hP : 0 < ∏ r, rec r ^ nOf u (some r) := Finset.prod_pos fun r _ => zpow_pos (hrec r).1 _
    have hvv := hvn s₀ hs₀
    have h5 : ‖ev' j ⟨x, hx⟩‖ * ((p : ℝ) ^ (-s₀) * ∏ r, rec r ^ nOf u (some r)) ≤
        ((∏ r, rec r ^ nOf u (some r)) * Ee) * ‖W‖ := by
      rw [← hvv, ← norm_mul, ← heq, norm_mul]
      exact mul_le_mul_of_nonneg_right (hwle.trans hsup) (norm_nonneg _)
    have h6 : ‖ev' j ⟨x, hx⟩‖ * (p : ℝ) ^ (-s₀) ≤ Ee * ‖W‖ := by
      refine le_of_mul_le_mul_right ?_ hP
      calc _ = ‖ev' j ⟨x, hx⟩‖ * ((p : ℝ) ^ (-s₀) * ∏ r, rec r ^ nOf u (some r)) := by ring
        _ ≤ _ := h5
        _ = _ := by ring
    have h7 : (p : ℝ) ^ s₀ * (p : ℝ) ^ (-s₀) = 1 := by
      rw [← Real.rpow_add hpp]; simp
    calc ‖ev' j ⟨x, hx⟩‖ = (p : ℝ) ^ s₀ * (‖ev' j ⟨x, hx⟩‖ * (p : ℝ) ^ (-s₀)) := by
          linear_combination (-‖ev' j ⟨x, hx⟩‖) * h7
      _ ≤ _ := mul_le_mul_of_nonneg_left h6 (Real.rpow_pos_of_pos hpp _).le
  have hWle : ‖W‖ ≤ (p : ℝ) ^ s₀ * (Ee * ‖W‖) := by
    have h0 : 0 ≤ (p : ℝ) ^ s₀ * (Ee * ‖W‖) := by positivity
    have := IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg h0 (fun j (_ : j ∈ Finset.univ) => hj j)
    rwa [← hWsum] at this
  have hWp : 0 < ‖W‖ := norm_pos_iff.2 hW
  have h8 : 1 ≤ (p : ℝ) ^ s₀ * Ee := by
    refine le_of_mul_le_mul_right ?_ hWp
    calc 1 * ‖W‖ = ‖W‖ := one_mul _
      _ ≤ _ := hWle
      _ = _ := by ring
  have h9 : 0 ≤ s₀ + GlobalTheory.CovHt.l1 u * Cθ := by
    rw [Real.rpow_def_of_pos hpp, hEe, ← Real.exp_add] at h8
    have h10 := Real.exp_le_exp.1 (by simpa using h8 : Real.exp 0 ≤ _)
    have h11 : 0 ≤ Real.log p * (s₀ + GlobalTheory.CovHt.l1 u * Cθ) := by linarith
    exact (mul_nonneg_iff_of_pos_left hlog).1 h11
  have hres : Formalism.L2.Pj.resCharOf la = p := by
    by_contra hne
    refine Formalism.L2.Pj.Crude.crv_not_mem la (fun hd => hne ?_) hla
    exact (Nat.prime_dvd_prime_iff_eq (Formalism.L2.Pj.Crude.resCharOf_prime la) hp).1 hd
  have hvp : (vLa la (p : c.F) : ℝ) = ramOverZ la := by
    have := Formalism.L2.Pj.Crude.crv_vLa_char la
    rw [hres] at this
    exact_mod_cast this
  have hl0 : 0 ≤ GlobalTheory.CovHt.l1 u := by
    rw [← hL1]; exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hex : Cθ ≤ if p ∈ o.toTowerOrigin.S B then exTwo E p else 0 := by
    rw [hCθ]
    split_ifs with h1' h2'
    · simp only [exTwo, GlobalTheory.CovHt.htEx, if_pos h2', padicValInt]
      have : (0 : ℝ) ≤ (padicValNat p (discr E).natAbs : ℝ) / Module.finrank ℚ E := by positivity
      linarith
    · simp only [exTwo, GlobalTheory.CovHt.htEx, if_neg h2', padicValInt]
      have : (0 : ℝ) ≤ (padicValNat p (discr E).natAbs : ℝ) / Module.finrank ℚ E := by positivity
      linarith
    · exact le_rfl
  rw [← hval, hs₀]
  refine EReal.coe_le_coe_iff.2 ?_
  rw [hvp]
  have h12 := mul_nonneg hra'.le h9
  have h13 := mul_nonneg (mul_nonneg hra'.le hl0) (sub_nonneg.2 hex)
  nlinarith [h12, h13]

end GlobalTheory.CompanionTheory.Ar.Plug
