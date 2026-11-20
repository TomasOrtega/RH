import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgePeriodGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartAtPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExponentialOfSemiAbelianFibreLinearChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConstForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsExpChartRescale
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelLatticeOfIsUnf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCochFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRiemannFormPeriodChartGenericFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CombMatMulVecIntCast
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj Matrix Topology
open Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CubeFib GlobalTheory.LieMet GlobalTheory.LieHt GlobalTheory.LocM.Frm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh GlobalTheory.Toroidal GlobalTheory.HeightParts GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.BdFib

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.ShFam.Hor.LogCh.PerChartKer

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c O _ β Y T σ U hσ hU x₀`. Take `⟨n, a₁, g, r₀, e, ex, ζ, hx₀, he0, hEC, hbd, hsurj, hζan, hζli, hζK, hζB, hζC, hζstd⟩` from `GlobalTheory.T.exists_framedChart_exponential_toroidalModel E H Dw l Xo c O β Y T σ x₀`. Establish `hEC'` using `hEC`. Take `⟨htarget, hholE, hsymmHol, hadd, hjoint, htan⟩` from `hEC'`. Set `a` to `min a₁ n`.

Establish `ha : a ≤ n` using `min_le_right _ _`. Establish `hka : ∀ k : Fin n, ((k : ℕ) < a ↔ (k : ℕ) < a₁)` using `fun k => by`. Simplify using `only [a, lt_min_iff, k.isLt, and_true]`. Establish `hsymm : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, e.symm z ∈ e.source` using `fun z hz => e.map_target (by rw [htarget]; exact hz)`. Establish `hExpAt : ∀ x ∈ e.source, IsExpAt T.Z.t (x.1 ≫ genι T.Z) (ex x)` using `fun x hx => ⟨hadd x hx, (htan x hx).1, (htan x hx).2⟩`.

Establish `hzero : ∀ x ∈ e.source, ex x 0 = 1` using `fun x hx => by`. Use `hadd x hx 0 0` as an intermediate fact. Rewrite `this` using `[add_zero]`. Conclude with `mul_eq_left.1 this.symm`. Establish `hHol : IsHolTo (Metric.ball (0 : Fin n → ℂ) 1 ×ˢ Set.univ) (fun zw : (Fin n → ℂ) × (Fin g → ℂ) => (ex (e.symm zw.1) zw.2).left)` using `htarget ▸ hjoint`.

Establish `hslice : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, IsHolTo Set.univ (fun w => (ex (e.symm z) w).left)` using `fun z hz => by`. Use `GlobalTheory.HolPeriods.isHolTo_comp (φ := fun w : Fin g → ℂ => (z, w)) hHol isOpen_univ ((differentiableOn_const z).prodMk differentiableOn_id) fun w _ => Set.mk_mem_prod hz (Set.mem_univ w)` as an intermediate fact. Simplify using `only at this`. Conclude with `this`. Establish `h0 : e.symm 0 = x₀` using `by rw [← he0]; exact e.left_inv hx₀`.

Establish `hmem0 : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1` using `Metric.mem_ball_self one_pos`. Establish `hinner : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → Inner (e.symm z)` using `fun z hz hnz => (hbd _ (hsymm z hz)).2 fun k hk => by`. Rewrite using `[e.right_inv (by rw [htarget]; exact hz)]`. Conclude with `hnz k ((hka k).2 hk)`. Set `K : (Fin n → ℂ) → Set (Fin g → ℂ)` to `fun z => {w | ex (e.symm z) w = 1}`.

Set `Pair : ℕ → (Fin n → ℂ) → (Fin g → ℂ) → (Fin g → ℂ) → ℂˣ → Prop` to `fun N z v w c => GlobalTheory.UU.CubWeil T.Z.t.cub N (ex (e.symm z) ((N : ℂ)⁻¹ • v)) (ex (e.symm z) ((N : ℂ)⁻¹ • w)) (unitOn c)`. Establish `hLF : IsLatFam (Metric.ball 0 1) K` using `GlobalTheory.T.exponentialKernels_isHolomorphicLatticeFamily E H T.Z.X T.Z.t n g (Metric.ball 0 1) (fun z => (e.symm z).1 ≫ genι T.Z) (fun z => ex (e.symm z)) Metric.isOpen_ball hHol fun z hz => hExpAt _ (hsymm z hz)`. Establish `hB0 : IsLatBasis (K 0) (ζ 0)` using `by show IsLatBasis {w | ex (e.symm 0) w = 1} (ζ 0)`. Rewrite using `[h0]`. Conclude with `hζB`.

Establish `hP1 : ∀ N z v w c c', Pair N z v w c → Pair N z v w c' → c = c'` using `fun N z v w c c' h h' => unitOn_injective (h.unique h')`. Establish `hP2 : ∀ (m N : ℕ) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → Fin n → ℂ) (v w : (Fin m → ℂ) → Fin g → ℂ) (c : ℂˣ) (b₀ b₁ : Fin m → ℂ), 0 < N → IsOpen B → _root_.IsPreconnected B → DifferentiableOn ℂ φ B → Set.MapsTo φ B (Metric.ball 0 1) → DifferentiableOn ℂ v B → DifferentiableOn ℂ …`. Introduce `m N B φ v w c b₀ b₁ hN hB hBc hφ hφm hv hw hK hb₀ hb₁ h`. Establish `h1` using `GlobalTheory.HolPeriods.isHolTo_comp (φ := fun b => (φ b, (N : ℂ)⁻¹ • v b)) hHol hB (hφ.prodMk ((differentiableOn_const ((N : ℂ)⁻¹)).smul hv)) fun b hb => Set.mk_mem_prod (hφm hb) (Set.mem_univ _)`. Establish `h2` using `GlobalTheory.HolPeriods.isHolTo_comp (φ := fun b => (φ b, (N : ℂ)⁻¹ • w b)) hHol hB (hφ.prodMk ((differentiableOn_const ((N : ℂ)⁻¹)).smul hw)) fun b hb => Set.mk_mem_prod (hφm hb) (Set.mem_univ _)`.

Simplify using `only at h1 h2`. Conclude with `GlobalTheory.T.cubicalWeilPairing_torsion_const_holomorphic_family T.Z.X T.Z.t.G T.Z.t.PP T.Z.t.cub m N B (fun b => (e.symm (φ b)).1 ≫ genι T.Z) (fun b => ex (e.symm (φ b)) ((N : ℂ)⁻¹ • v b)) (fun b => ex (e.symm (φ b)) ((N : ℂ)⁻¹ • w b)) c b₀ b₁ hN hB hBc h1 h2 (fun b hb => ⟨pow …`. Establish `hP3 : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm Hm u u).re) ∧ Submodule.span ℝ (K z) = ⊤ ∧ (∀ v ∈ K z, ∀ w ∈ K z, ∃ m : ℤ, (hermForm Hm v w).im = m) ∧ ∀ (N …`. Introduce `z hz hnz`. Take `⟨-, Hm, hH, hpos, hspan, hint, hw⟩` from `GlobalTheory.ShFam.Hor.LogCh.kernel_lattice_of_isUnf E H Dw l Xo c O β T.Z σ U hσ hU g (e.symm z) (ex (e.symm z)) (hinner z hz hnz) (hExpAt _ (hsymm z hz)) (hslice z hz)`.

Conclude with `⟨Hm, hH, hpos, hspan, fun v hv w hw' => hint v w hv hw', fun N v w hN hv hw' => hw N v w _ hN hv hw' rfl⟩`. Establish `hP4 : ∀ N : ℕ, 0 < N → ∃ S : Set (Fin r₀ → ZMod N), N ^ r₀ * Nat.card S = N ^ (2 * g) ∧ ∀ u u' : Fin r₀ → ℤ, (fun j => (u j : ZMod N)) ∈ S → Pair N 0 (∑ j, u j • ζ 0 j) (∑ j, u' j • ζ 0 j) 1`. Introduce `N hN`. Establish `hsl : IsHolTo Set.univ (fun w => (ex x₀ w).left)`. Use `hslice 0 hmem0` as an intermediate fact.

Rewrite `this` using `[h0]`. Conclude with `this`. Take `⟨Tt, hT1, hT2, hTc⟩` from `GlobalTheory.T.exists_toricTorsion_cubicalWeil_one_complexPoint E H T.Z.X T.Z.t (x₀.1 ≫ genι T.Z) g N (ex x₀) hN (hExpAt x₀ hx₀) hsurj hsl`. Take `⟨S, hSc, hS⟩` from `GlobalTheory.T.torsion_count_through_exponential_lattice_kernel _ g r₀ N (ex x₀) (ζ 0) Tt hN (hadd x₀ hx₀) hsurj hζB hT1 hTc`. Use `⟨S, hSc, fun u u' hu => ?_⟩` and prove the remaining obligations.

Use `show GlobalTheory.UU.CubWeil T.Z.t.cub N (ex (e.symm 0) ((N : ℂ)⁻¹ • ∑ j, u j • ζ 0 j)) (ex (e.symm 0) ((N : ℂ)⁻¹ • ∑ j, u' j • ζ 0 j)) (unitOn 1)`. Rewrite using `[h0, unitOn_one]`. Conclude with `hT2 _ (hS u hu) _ (pow_eq_one_of_map _ (hadd x₀ hx₀) (hzero x₀ hx₀) hN ((hζB.2 _).2 ⟨u', rfl⟩))`. Take `⟨r, lam, M, hc, hs, -, hMv, hrad⟩` from `GlobalTheory.ShFam.Hor.LogCh.ConstForm.constForm n a g r₀ K ζ Pair hLF hζan hζli hζK hB0 hζC hζstd hP1 hP2 hP3 hP4`. Establish `hM' : ∀ s ∈ logDom n a, ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm Hm u u).re) ∧ ∀ s' ∈ logDom n a, logExp a s' = logExp a s → ∀ i j, (hermForm Hm (lam s' i) (lam s' j)).im = M i j`.

Introduce `s hsD`. Establish `hz1 : logExp a s ∈ Metric.ball (0 : Fin n → ℂ) 1`. Rewrite using `[mem_ball_zero_iff, pi_norm_lt_iff one_pos]`. Introduce `k`. Establish `hk` using `hsD k`.

Distinguish the cases in `h : (k : ℕ) < a`. Simplify using `only [h, if_true] at hk`. Simplify using `only [logExp, h, if_true, Complex.norm_exp]`. Conclude with `Real.exp_lt_one_iff.2 hk`. Simplify using `only [h, if_false] at hk`.

Simplify `hk` using `only [logExp, h, if_false]`. Establish `hnz : ∀ k : Fin n, (k : ℕ) < a → logExp a s k ≠ 0` using `fun k hk => by`. Simplify using `only [logExp, hk, if_true]`. Conclude with `Complex.exp_ne_zero _`. Take `⟨Hm, hH, hpos, -, hint, hw⟩` from `hP3 _ hz1 hnz`.

Use `⟨Hm, hH, hpos, fun s' hs' he => hMv s' hs' Hm ?_ ?_⟩` and prove the remaining obligations. Rewrite using `[he]`. Conclude with `hint`. Rewrite using `[he]`. Conclude with `hw`.

Take `⟨rk, τ₀, B, P, ρ, d, hρ, hρ1, hd, hPC, hPd, hPu, hrel, hker⟩` from `GlobalTheory.ShFam.Hor.LogCh.PerChartKer.periodChart_ker n a g r₀ r ha K ζ lam M hLF hζan hζli hζK hB0 hζstd hc hs hM' hrad`. Take `⟨ch, hch, hchs, hchρ⟩` from `GlobalTheory.ShFam.Hor.LogCh.isExpChart_rescale E H Dw l Xo c O β T.Z σ n g e ex P ρ hEC hρ hρ1 hPd hPu`. Establish `hρ0 : (ρ : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.2 hρ.ne'`. Establish `hex : ∀ x ∈ ch.source, ∀ k, e x k = (ρ : ℂ) * ch x k` using `fun x hx k => by`. Rewrite using `[hchρ x hx]`.

Simplify using `[Complex.real_smul]`. Establish `hx₀ch : x₀ ∈ ch.source` using `(hchs x₀).2 ⟨hx₀, by rw [he0]; exact Metric.mem_ball_self hρ⟩`. Take `⟨Dn, hDn, hker'⟩` from `hker`. Use `⟨n, a, ha, g, rk, τ₀, B, ch, fun x v => ex x (P (e x) *ᵥ v), d, Dn, hPC, hch, hx₀ch, ?_, hd, hDn, ?_, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `k`.

Use `hex x₀ hx₀ch k` as an intermediate fact. Rewrite `this` using `[he0]`. Conclude with `((mul_eq_zero.1 this.symm).resolve_left hρ0)`. Introduce `x hx`. Establish `hxe` using `((hchs x).1 hx).1`.

Rewrite using `[hbd x hxe]`. Prove the components needed by the constructor for the conclusion. Introduce `h i hi`. Apply `h (Fin.castLE ha i) ((hka _).1 (by simp))` to reduce the goal to its premises. Rewrite using `[hex x hx, hi, mul_zero]`.

Introduce `h k hk hk0`. Apply `h ⟨k, (hka k).2 hk⟩` to reduce the goal to its premises. Rewrite `hk0` using `[hex x hx]`. Conclude with `(mul_eq_zero.1 hk0).resolve_left hρ0`. Introduce `x hx hin`.

Establish `hxe` using `((hchs x).1 hx).1`. Establish `hzb` using `((hchs x).1 hx).2`. Establish `hz1 : e x ∈ Metric.ball (0 : Fin n → ℂ) 1` using `by rw [← htarget]; exact e.map_source hxe`. Establish `hnz : ∀ k : Fin n, (k : ℕ) < a → e x k ≠ 0` using `fun k hk => (hbd x hxe).1 hin k ((hka k).1 hk)`. Take `⟨s, hsD, hsz⟩` from `GlobalTheory.ShFam.Hor.LogCh.PerChart.exists_logExp_eq n a (e x) hz1 hnz`.

Establish `hsl : IsHolTo Set.univ (fun w => (ex x w).left)`. Use `hslice (e x) hz1` as an intermediate fact. Rewrite `this` using `[e.left_inv hxe]`. Conclude with `this`. Take `⟨-, Hm, hH, hpos, -, hint, hweil⟩` from `GlobalTheory.ShFam.Hor.LogCh.kernel_lattice_of_isUnf E H Dw l Xo c O β T.Z σ U hσ hU g x (ex x) hin (hExpAt x hxe) hsl`.

Establish `hKz : ∀ w, w ∈ K (logExp a s) ↔ ex x w = 1` using `fun w => by`. Rewrite using `[hsz]`. Use `show ex (e.symm (e x)) w = 1 ↔ _`. Rewrite using `[e.left_inv hxe]`. Establish `hlamrel` using `hMv s hsD Hm (fun v hv w hw => hint v w ((hKz v).1 hv) ((hKz w).1 hw)) (fun N v w hN hv hw => by show GlobalTheory.UU.CubWeil T.Z.t.cub N (ex (e.symm (logExp a s)) ((N : ℂ)⁻¹ • v)) (ex (e.symm (logExp a s)) ((N : ℂ)⁻¹ • w)) _`.

Rewrite using `[hsz, e.left_inv hxe]`. Conclude with `hweil N v w _ hN ((hKz v).1 hv) ((hKz w).1 hw) rfl)`. Establish `key` using `hrel s hsD (hsz ▸ hzb) Hm hlamrel`. Establish `hchx : ρ⁻¹ • e x = ch x` using `by rw [hchρ x hx, smul_smul, inv_mul_cancel₀ hρ.ne', one_smul]`. Rewrite `key` using `[hsz, hchx]`.

Use `⟨fun k v w ζ' hk hv hw hζ' => ?_, fun large₂ hLg m m' => ?_⟩` and prove the remaining obligations. Rewrite `hζ'` using `[← key, GlobalTheory.ShFam.Hor.LogCh.PerChart.hermForm_pull']`. Establish `e1 : ∀ u : Fin g → ℂ, P (e x) *ᵥ ((k : ℂ)⁻¹ • u) = (k : ℂ)⁻¹ • (P (e x) *ᵥ u)` using `fun u => Matrix.mulVec_smul _ _ _`. Use `show GlobalTheory.UU.CubWeil T.Z.t.cub k (ex x (P (e x) *ᵥ ((k : ℂ)⁻¹ • v))) (ex x (P (e x) *ᵥ ((k : ℂ)⁻¹ • w))) (unitOn ζ')`. Rewrite using `[e1, e1]`.

Conclude with `hweil k _ _ ζ' hk hv hw hζ'`. Set `sL : Fin n → ℂ` to `fun k => if h : (k : ℕ) < a then large₂ ⟨k, h⟩ + ((Real.log ρ : ℝ) : ℂ) else e x k`. Establish `hsk : ∀ i : Fin a, sL (Fin.castLE ha i) = large₂ i + ((Real.log ρ : ℝ) : ℂ)` using `fun i => by`. Simplify using `only [sL, Fin.val_castLE, dif_pos i.isLt]`. Establish `hsexp : logExp a sL = e x`.

Use function extensionality and compare the values at `k`. Distinguish the cases in `hk : (k : ℕ) < a`. Establish `hc : Fin.castLE ha ⟨k, hk⟩ = k` using `Fin.ext rfl`. Simplify using `only [logExp, hk, if_true, sL, dif_pos hk]`. Rewrite using `[Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hρ, hLg ⟨k, hk⟩, hc, hex x hx k, mul_comm]`.

Simplify using `only [logExp, hk, if_false, sL, dif_neg hk]`. Establish `hsLD : sL ∈ logDom n a`. Introduce `k`. Establish `hek : ‖e x k‖ < 1` using `lt_of_lt_of_le ((pi_norm_lt_iff hρ).1 (mem_ball_zero_iff.1 hzb) k) hρ1`. Distinguish the cases in `hk : (k : ℕ) < a`.

Simplify using `only [hk, if_true]`. Establish `h1 : Complex.exp (sL k) = e x k`. Use `congrFun hsexp k` as an intermediate fact. Simplify `this` using `only [logExp, hk, if_true]`. Rewrite `hek` using `[← h1, Complex.norm_exp]`.

Conclude with `Real.exp_lt_one_iff.1 hek`. Simplify using `only [hk, if_false, sL, dif_neg hk]`. Conclude with `hek`. Establish `key2` using `hker' sL hsLD (by rw [hsexp]; exact hzb) large₂ hsk m m'`. Rewrite `key2` using `[hsexp, hchx]`.

Establish `key3 : ex (e.symm (e x)) (P (e x) *ᵥ ((Dn : ℂ) • ((fun i => (m i : ℂ)) + GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.period τ₀ B (ch x) large₂ *ᵥ fun i => (m' i : ℂ)))) = 1` using `key2`. Rewrite `key3` using `[e.left_inv hxe]`. Conclude with `key3`.
-/
theorem exists_period_chart_lattice_ker : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ x₀ : CxPts (genStr T.Z) σ, ∃ (n a : ℕ) (ha : a ≤ n) (g rk : ℕ) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (ch₀ : OpenPartialHomeomorph (CxPts (genStr T.Z) σ) (Fin n → ℂ)) (ex : ExpMaps T.Z σ g) (d : ℝ) (Dn : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.IsPeriodChart rk τ₀ B ∧ IsExpChart ch₀ ex ∧ x₀ ∈ ch₀.source ∧ ch₀ x₀ = 0 ∧ 0 < d ∧ 0 < Dn ∧ (∀ x ∈ ch₀.source, Inner x ↔ ∀ i : Fin a, ch₀ x (Fin.castLE ha i) ≠ 0) ∧ ∀ x ∈ ch₀.source, Inner x → (∀ (k : ℕ) (v w : Fin g → ℂ) (ζ : ℂˣ), 0 < k → ex x v = 1 → ex x w = 1 → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm (((d : ℝ) : ℂ) • (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B (ch₀ x))⁻¹) v w).im : ℂ) / k) → GlobalTheory.UU.CubWeil T.Z.t.cub k (ex x ((k : ℂ)⁻¹ • v)) (ex x ((k : ℂ)⁻¹ • w)) (unitOn ζ)) ∧ ∀ large₂ : Fin a → ℂ, (∀ i, Complex.exp (large₂ i) = ch₀ x (Fin.castLE ha i)) → ∀ m m' : Fin g → ℤ, ex x ((Dn : ℂ) • ((fun i => (m i : ℂ)) + GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.period τ₀ B (ch₀ x) large₂ *ᵥ fun i => (m' i : ℂ))) = 1 := by
  intro E _ _ _ H Dw l Xo c O _ β Y T σ U hσ hU x₀
  obtain ⟨n, a₁, g, r₀, e, ex, ζ, hx₀, he0, hEC, hbd, hsurj, hζan, hζli, hζK, hζB, hζC, hζstd⟩ :=
    GlobalTheory.T.exists_framedChart_exponential_toroidalModel E H Dw l Xo c O β Y T σ x₀
  have hEC' := hEC
  obtain ⟨htarget, hholE, hsymmHol, hadd, hjoint, htan⟩ := hEC'
  let a := min a₁ n
  have ha : a ≤ n := min_le_right _ _
  have hka : ∀ k : Fin n, ((k : ℕ) < a ↔ (k : ℕ) < a₁) := fun k => by
    simp only [a, lt_min_iff, k.isLt, and_true]
  have hsymm : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, e.symm z ∈ e.source := fun z hz =>
    e.map_target (by rw [htarget]; exact hz)
  have hExpAt : ∀ x ∈ e.source, IsExpAt T.Z.t (x.1 ≫ genι T.Z) (ex x) := fun x hx =>
    ⟨hadd x hx, (htan x hx).1, (htan x hx).2⟩
  have hzero : ∀ x ∈ e.source, ex x 0 = 1 := fun x hx => by
    have := hadd x hx 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have hHol : IsHolTo (Metric.ball (0 : Fin n → ℂ) 1 ×ˢ Set.univ)
      (fun zw : (Fin n → ℂ) × (Fin g → ℂ) => (ex (e.symm zw.1) zw.2).left) := htarget ▸ hjoint
  have hslice : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, IsHolTo Set.univ (fun w => (ex (e.symm z) w).left) :=
    fun z hz => by
      have := GlobalTheory.HolPeriods.isHolTo_comp (φ := fun w : Fin g → ℂ => (z, w)) hHol isOpen_univ
        ((differentiableOn_const z).prodMk differentiableOn_id) fun w _ => Set.mk_mem_prod hz (Set.mem_univ w)
      dsimp only at this
      exact this
  have h0 : e.symm 0 = x₀ := by rw [← he0]; exact e.left_inv hx₀
  have hmem0 : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.mem_ball_self one_pos
  have hinner : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → Inner (e.symm z) :=
    fun z hz hnz => (hbd _ (hsymm z hz)).2 fun k hk => by
      rw [e.right_inv (by rw [htarget]; exact hz)]
      exact hnz k ((hka k).2 hk)
  let K : (Fin n → ℂ) → Set (Fin g → ℂ) := fun z => {w | ex (e.symm z) w = 1}
  let Pair : ℕ → (Fin n → ℂ) → (Fin g → ℂ) → (Fin g → ℂ) → ℂˣ → Prop := fun N z v w c =>
    GlobalTheory.UU.CubWeil T.Z.t.cub N (ex (e.symm z) ((N : ℂ)⁻¹ • v)) (ex (e.symm z) ((N : ℂ)⁻¹ • w)) (unitOn c)
  have hLF : IsLatFam (Metric.ball 0 1) K :=
    GlobalTheory.T.exponentialKernels_isHolomorphicLatticeFamily E H T.Z.X T.Z.t n g (Metric.ball 0 1) (fun z => (e.symm z).1 ≫ genι T.Z) (fun z => ex (e.symm z))
      Metric.isOpen_ball hHol fun z hz => hExpAt _ (hsymm z hz)
  have hB0 : IsLatBasis (K 0) (ζ 0) := by
    show IsLatBasis {w | ex (e.symm 0) w = 1} (ζ 0)
    rw [h0]
    exact hζB
  have hP1 : ∀ N z v w c c', Pair N z v w c → Pair N z v w c' → c = c' := fun N z v w c c' h h' =>
    unitOn_injective (h.unique h')
  have hP2 : ∀ (m N : ℕ) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → Fin n → ℂ) (v w : (Fin m → ℂ) → Fin g → ℂ)
      (c : ℂˣ) (b₀ b₁ : Fin m → ℂ), 0 < N → IsOpen B → _root_.IsPreconnected B → DifferentiableOn ℂ φ B →
      Set.MapsTo φ B (Metric.ball 0 1) → DifferentiableOn ℂ v B → DifferentiableOn ℂ w B →
      (∀ b ∈ B, v b ∈ K (φ b) ∧ w b ∈ K (φ b)) → b₀ ∈ B → b₁ ∈ B →
      Pair N (φ b₀) (v b₀) (w b₀) c → Pair N (φ b₁) (v b₁) (w b₁) c := by
    intro m N B φ v w c b₀ b₁ hN hB hBc hφ hφm hv hw hK hb₀ hb₁ h
    have h1 := GlobalTheory.HolPeriods.isHolTo_comp (φ := fun b => (φ b, (N : ℂ)⁻¹ • v b)) hHol hB
      (hφ.prodMk ((differentiableOn_const ((N : ℂ)⁻¹)).smul hv)) fun b hb => Set.mk_mem_prod (hφm hb) (Set.mem_univ _)
    have h2 := GlobalTheory.HolPeriods.isHolTo_comp (φ := fun b => (φ b, (N : ℂ)⁻¹ • w b)) hHol hB
      (hφ.prodMk ((differentiableOn_const ((N : ℂ)⁻¹)).smul hw)) fun b hb => Set.mk_mem_prod (hφm hb) (Set.mem_univ _)
    dsimp only at h1 h2
    exact GlobalTheory.T.cubicalWeilPairing_torsion_const_holomorphic_family T.Z.X T.Z.t.G T.Z.t.PP T.Z.t.cub m N B (fun b => (e.symm (φ b)).1 ≫ genι T.Z)
      (fun b => ex (e.symm (φ b)) ((N : ℂ)⁻¹ • v b)) (fun b => ex (e.symm (φ b)) ((N : ℂ)⁻¹ • w b)) c b₀ b₁ hN hB hBc
      h1 h2
      (fun b hb => ⟨pow_eq_one_of_map _ (hadd _ (hsymm _ (hφm hb))) (hzero _ (hsymm _ (hφm hb))) hN (hK b hb).1,
        pow_eq_one_of_map _ (hadd _ (hsymm _ (hφm hb))) (hzero _ (hsymm _ (hφm hb))) hN (hK b hb).2⟩) hb₀ hb₁ h
  have hP3 : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) →
      ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm Hm u u).re) ∧
        Submodule.span ℝ (K z) = ⊤ ∧ (∀ v ∈ K z, ∀ w ∈ K z, ∃ m : ℤ, (hermForm Hm v w).im = m) ∧
        ∀ (N : ℕ) (v w : Fin g → ℂ), 0 < N → v ∈ K z → w ∈ K z →
          Pair N z v w (Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm Hm v w).im : ℂ) / N))
            (Complex.exp_ne_zero _)) := by
    intro z hz hnz
    obtain ⟨-, Hm, hH, hpos, hspan, hint, hw⟩ := GlobalTheory.ShFam.Hor.LogCh.kernel_lattice_of_isUnf E H Dw l Xo c O β T.Z σ U hσ hU g (e.symm z) (ex (e.symm z))
      (hinner z hz hnz) (hExpAt _ (hsymm z hz)) (hslice z hz)
    exact ⟨Hm, hH, hpos, hspan, fun v hv w hw' => hint v w hv hw', fun N v w hN hv hw' => hw N v w _ hN hv hw' rfl⟩
  have hP4 : ∀ N : ℕ, 0 < N → ∃ S : Set (Fin r₀ → ZMod N), N ^ r₀ * Nat.card S = N ^ (2 * g) ∧
      ∀ u u' : Fin r₀ → ℤ, (fun j => (u j : ZMod N)) ∈ S → Pair N 0 (∑ j, u j • ζ 0 j) (∑ j, u' j • ζ 0 j) 1 := by
    intro N hN
    have hsl : IsHolTo Set.univ (fun w => (ex x₀ w).left) := by
      have := hslice 0 hmem0
      rw [h0] at this
      exact this
    obtain ⟨Tt, hT1, hT2, hTc⟩ := GlobalTheory.T.exists_toricTorsion_cubicalWeil_one_complexPoint E H T.Z.X T.Z.t (x₀.1 ≫ genι T.Z) g N (ex x₀) hN (hExpAt x₀ hx₀) hsurj hsl
    obtain ⟨S, hSc, hS⟩ := GlobalTheory.T.torsion_count_through_exponential_lattice_kernel _ g r₀ N (ex x₀) (ζ 0) Tt hN (hadd x₀ hx₀) hsurj hζB hT1 hTc
    refine ⟨S, hSc, fun u u' hu => ?_⟩
    show GlobalTheory.UU.CubWeil T.Z.t.cub N (ex (e.symm 0) ((N : ℂ)⁻¹ • ∑ j, u j • ζ 0 j))
      (ex (e.symm 0) ((N : ℂ)⁻¹ • ∑ j, u' j • ζ 0 j)) (unitOn 1)
    rw [h0, unitOn_one]
    exact hT2 _ (hS u hu) _ (pow_eq_one_of_map _ (hadd x₀ hx₀) (hzero x₀ hx₀) hN ((hζB.2 _).2 ⟨u', rfl⟩))
  obtain ⟨r, lam, M, hc, hs, -, hMv, hrad⟩ :=
    GlobalTheory.ShFam.Hor.LogCh.ConstForm.constForm n a g r₀ K ζ Pair hLF hζan hζli hζK hB0 hζC hζstd hP1 hP2 hP3 hP4
  have hM' : ∀ s ∈ logDom n a, ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧
      (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm Hm u u).re) ∧
      ∀ s' ∈ logDom n a, logExp a s' = logExp a s → ∀ i j, (hermForm Hm (lam s' i) (lam s' j)).im = M i j := by
    intro s hsD
    have hz1 : logExp a s ∈ Metric.ball (0 : Fin n → ℂ) 1 := by
      rw [mem_ball_zero_iff, pi_norm_lt_iff one_pos]
      intro k
      have hk := hsD k
      by_cases h : (k : ℕ) < a
      · simp only [h, if_true] at hk
        simp only [logExp, h, if_true, Complex.norm_exp]
        exact Real.exp_lt_one_iff.2 hk
      · simp only [h, if_false] at hk
        simpa only [logExp, h, if_false] using hk
    have hnz : ∀ k : Fin n, (k : ℕ) < a → logExp a s k ≠ 0 := fun k hk => by
      simp only [logExp, hk, if_true]
      exact Complex.exp_ne_zero _
    obtain ⟨Hm, hH, hpos, -, hint, hw⟩ := hP3 _ hz1 hnz
    refine ⟨Hm, hH, hpos, fun s' hs' he => hMv s' hs' Hm ?_ ?_⟩
    · rw [he]; exact hint
    · rw [he]; exact hw
  obtain ⟨rk, τ₀, B, P, ρ, d, hρ, hρ1, hd, hPC, hPd, hPu, hrel, hker⟩ :=
    GlobalTheory.ShFam.Hor.LogCh.PerChartKer.periodChart_ker n a g r₀ r ha K ζ lam M hLF hζan hζli hζK hB0 hζstd hc hs hM' hrad
  obtain ⟨ch, hch, hchs, hchρ⟩ := GlobalTheory.ShFam.Hor.LogCh.isExpChart_rescale E H Dw l Xo c O β T.Z σ n g e ex P ρ hEC hρ hρ1 hPd hPu
  have hρ0 : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hρ.ne'
  have hex : ∀ x ∈ ch.source, ∀ k, e x k = (ρ : ℂ) * ch x k := fun x hx k => by
    rw [hchρ x hx]
    simp [Complex.real_smul]
  have hx₀ch : x₀ ∈ ch.source := (hchs x₀).2 ⟨hx₀, by rw [he0]; exact Metric.mem_ball_self hρ⟩
  obtain ⟨Dn, hDn, hker'⟩ := hker
  refine ⟨n, a, ha, g, rk, τ₀, B, ch, fun x v => ex x (P (e x) *ᵥ v), d, Dn, hPC, hch, hx₀ch, ?_, hd, hDn, ?_, ?_⟩
  · funext k
    have := hex x₀ hx₀ch k
    rw [he0] at this
    exact ((mul_eq_zero.1 this.symm).resolve_left hρ0)
  · intro x hx
    have hxe := ((hchs x).1 hx).1
    rw [hbd x hxe]
    constructor
    · intro h i hi
      apply h (Fin.castLE ha i) ((hka _).1 (by simp))
      rw [hex x hx, hi, mul_zero]
    · intro h k hk hk0
      apply h ⟨k, (hka k).2 hk⟩
      rw [hex x hx] at hk0
      exact (mul_eq_zero.1 hk0).resolve_left hρ0
  · intro x hx hin
    have hxe := ((hchs x).1 hx).1
    have hzb := ((hchs x).1 hx).2
    have hz1 : e x ∈ Metric.ball (0 : Fin n → ℂ) 1 := by rw [← htarget]; exact e.map_source hxe
    have hnz : ∀ k : Fin n, (k : ℕ) < a → e x k ≠ 0 := fun k hk =>
      (hbd x hxe).1 hin k ((hka k).1 hk)
    obtain ⟨s, hsD, hsz⟩ := GlobalTheory.ShFam.Hor.LogCh.PerChart.exists_logExp_eq n a (e x) hz1 hnz
    have hsl : IsHolTo Set.univ (fun w => (ex x w).left) := by
      have := hslice (e x) hz1
      rw [e.left_inv hxe] at this
      exact this
    obtain ⟨-, Hm, hH, hpos, -, hint, hweil⟩ :=
      GlobalTheory.ShFam.Hor.LogCh.kernel_lattice_of_isUnf E H Dw l Xo c O β T.Z σ U hσ hU g x (ex x) hin (hExpAt x hxe) hsl
    have hKz : ∀ w, w ∈ K (logExp a s) ↔ ex x w = 1 := fun w => by
      rw [hsz]
      show ex (e.symm (e x)) w = 1 ↔ _
      rw [e.left_inv hxe]
    have hlamrel := hMv s hsD Hm (fun v hv w hw => hint v w ((hKz v).1 hv) ((hKz w).1 hw))
      (fun N v w hN hv hw => by
        show GlobalTheory.UU.CubWeil T.Z.t.cub N (ex (e.symm (logExp a s)) ((N : ℂ)⁻¹ • v))
          (ex (e.symm (logExp a s)) ((N : ℂ)⁻¹ • w)) _
        rw [hsz, e.left_inv hxe]
        exact hweil N v w _ hN ((hKz v).1 hv) ((hKz w).1 hw) rfl)
    have key := hrel s hsD (hsz ▸ hzb) Hm hlamrel
    have hchx : ρ⁻¹ • e x = ch x := by rw [hchρ x hx, smul_smul, inv_mul_cancel₀ hρ.ne', one_smul]
    rw [hsz, hchx] at key
    refine ⟨fun k v w ζ' hk hv hw hζ' => ?_, fun large₂ hLg m m' => ?_⟩
    · rw [← key, GlobalTheory.ShFam.Hor.LogCh.PerChart.hermForm_pull'] at hζ'
      have e1 : ∀ u : Fin g → ℂ, P (e x) *ᵥ ((k : ℂ)⁻¹ • u) = (k : ℂ)⁻¹ • (P (e x) *ᵥ u) := fun u =>
        Matrix.mulVec_smul _ _ _
      show GlobalTheory.UU.CubWeil T.Z.t.cub k (ex x (P (e x) *ᵥ ((k : ℂ)⁻¹ • v))) (ex x (P (e x) *ᵥ ((k : ℂ)⁻¹ • w))) (unitOn ζ')
      rw [e1, e1]
      exact hweil k _ _ ζ' hk hv hw hζ'
    · let sL : Fin n → ℂ := fun k => if h : (k : ℕ) < a then large₂ ⟨k, h⟩ + ((Real.log ρ : ℝ) : ℂ) else e x k
      have hsk : ∀ i : Fin a, sL (Fin.castLE ha i) = large₂ i + ((Real.log ρ : ℝ) : ℂ) := fun i => by
        simp only [sL, Fin.val_castLE, dif_pos i.isLt]
      have hsexp : logExp a sL = e x := by
        funext k
        by_cases hk : (k : ℕ) < a
        · have hc : Fin.castLE ha ⟨k, hk⟩ = k := Fin.ext rfl
          simp only [logExp, hk, if_true, sL, dif_pos hk]
          rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hρ, hLg ⟨k, hk⟩, hc, hex x hx k, mul_comm]
        · simp only [logExp, hk, if_false, sL, dif_neg hk]
      have hsLD : sL ∈ logDom n a := by
        intro k
        have hek : ‖e x k‖ < 1 := lt_of_lt_of_le ((pi_norm_lt_iff hρ).1 (mem_ball_zero_iff.1 hzb) k) hρ1
        by_cases hk : (k : ℕ) < a
        · simp only [hk, if_true]
          have h1 : Complex.exp (sL k) = e x k := by
            have := congrFun hsexp k
            simpa only [logExp, hk, if_true] using this
          rw [← h1, Complex.norm_exp] at hek
          exact Real.exp_lt_one_iff.1 hek
        · simp only [hk, if_false, sL, dif_neg hk]
          exact hek
      have key2 := hker' sL hsLD (by rw [hsexp]; exact hzb) large₂ hsk m m'
      rw [hsexp, hchx] at key2
      have key3 : ex (e.symm (e x)) (P (e x) *ᵥ ((Dn : ℂ) • ((fun i => (m i : ℂ)) +
          GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.period τ₀ B (ch x) large₂ *ᵥ fun i => (m' i : ℂ)))) = 1 := key2
      rw [e.left_inv hxe] at key3
      exact key3

end GlobalTheory.ShFam.Hor.LogCh.PerChartKer
