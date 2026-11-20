import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExponentialFamilyPeriods
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeGram
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.OneLeftSpMap
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DerivationDeterminesChartStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DerivationVanishingConstantsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsExpChartStandardSmoothStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat

open GlobalTheory.CompanionTheory.Ar.Flat.ExpChart GlobalTheory.HolHom in

/- English proof (translation)
Introduce `R _ G _ _ g n M B ψ hsm hB b₀ hb₀`. Take `⟨V, t, ρ, hV, hρ, hss, hθ, hrat⟩` from `GlobalTheory.T.exists_exp_chart_standard_smooth R G g M (ψ b₀) hsm`. Use `letI : Algebra R Γ(G.left, V) := (cst G.hom V).toAlgebra`. Use `haveI : Algebra.IsStandardSmooth R Γ(G.left, V) := hss`. Establish `halg : ∀ r, algebraMap R Γ(G.left, V) r = cst G.hom V r` using `fun _ => rfl`.

Establish `h₀` using `(hθ (ψ b₀) hρ).1`. Set `χ₀ : Γ(G.left, V) →+* ℂ` to `evalHom (1 : Over.mk (spMap (ψ b₀)) ⟶ G).left V h₀`. Establish `hχv : ∀ a, valAt' (1 : Over.mk (spMap (ψ b₀)) ⟶ G).left V a = χ₀ a` using `fun a => valR_eq _ _ h₀ a`. Establish `hχc : χ₀.comp (algebraMap R Γ(G.left, V)) = ψ b₀` using `RingHom.ext fun r => by show χ₀ (cst G.hom V r) = ψ b₀ r`. Rewrite using `[← hχv]`.

Conclude with `val_cst V _ h₀ r`. Establish `ht₀ : ∀ c, χ₀ (t c) = 0` using `fun c => by rw [← hχv]; exact (hθ (ψ b₀) hρ).2.1 c`. Establish `hder : ∀ (θ : R →+* ℂ) (a : Fin g), θ ρ ≠ 0 → ∃ D : Γ(G.left, V) →+ ℂ, (∀ f, D f = TrivSqZeroExt.snd (valR (spMap (dualMap θ) ≫ (M.pt (Pi.single a 1)).left) V f)) ∧ (∀ r, D (cst G.hom V r) = 0) ∧ (∀ f f', D (f * f') = valAt' (1 : Over.mk (spMap θ) ⟶ G).left V f * D f' + valAt' (1 …`. Introduce `θ a hr`. Establish `hin` using `(hθ θ hr).1`.

Take `⟨D, hD, hL⟩` from `tan_der (tan_base M θ (Pi.single a 1)) hin`. Use `⟨D, hD, fun r => ?_, hL⟩` and prove the remaining obligations. Establish `hv` using `(le_preimage_dual_iff (tan_base M θ (Pi.single a 1)) V).2 hin`. Rewrite using `[hD, valR_eq _ _ hv, valR_cst G.hom V _ _ (tan_over M θ (Pi.single a 1)) hv]`. Simplify using `[TrivSqZeroExt.algebraMap_eq_inl']`.

Establish `hD₀ : ∀ D : Γ(G.left, V) →+ ℂ, (∀ r, D (algebraMap R _ r) = 0) → (∀ x y, D (x * y) = χ₀ x * D y + χ₀ y * D x) → (∀ c, D (t c) = 0) → D = 0`. Introduce `D hc hl hz`. Take `⟨c, hcD, -⟩` from `GlobalTheory.T.derivation_vanishing_constants R G g M (ψ b₀) hsm V hV h₀ D hc (fun f f' => by`. Rewrite using `[hχv, hχv]`. Conclude with `hl f f')`.

Establish `hc0 : ∀ a, c a = 0` using `fun a => by`. Use `hcD (t a)` as an intermediate fact. Rewrite `this` using `[hz a]`. Simplify using `only [(hθ (ψ b₀) hρ).2.2] at this`. Simplify using `using this.symm`.

Use extensionality with `f`. Rewrite using `[hcD f]`. Simplify using `[hc0]`. Establish `hS₀ : ∀ c, ∃ D : Γ(G.left, V) →+ ℂ, (∀ r, D (algebraMap R _ r) = 0) ∧ (∀ x y, D (x * y) = χ₀ x * D y + χ₀ y * D x) ∧ ∀ c', D (t c') = if c = c' then 1 else 0`. Introduce `c`.

Take `⟨D, hD, hc, hl⟩` from `hder (ψ b₀) c hρ`. Use `⟨D, hc, fun x y => ?_, fun c' => ?_⟩` and prove the remaining obligations. Rewrite using `[hl, hχv, hχv]`. Rewrite using `[hD]`. Conclude with `(hθ (ψ b₀) hρ).2.2 c c'`.

Take `⟨N, f, ε, δ, Ψa, hε, hδ, hεB, hΨ₀, hprop, hdiff, hft, huniq⟩` from `GlobalTheory.T.derivation_determines_chart R Γ(G.left, V) n g B ψ hB.1 hB.2 b₀ hb₀ χ₀ t hχc ht₀ hD₀ hS₀`. Establish `hev : ∀ᶠ b in 𝓝 b₀, ψ b ρ ≠ 0 ∧ ∀ j, ‖valAt' (1 : Over.mk (spMap (ψ b)) ⟶ G).left V (f j) - χ₀ (f j)‖ < δ`. Establish `hc : ∀ u, ContinuousAt (fun b => ψ b u) b₀` using `fun u => (hB.2 u).continuousOn.continuousAt (hB.1.mem_nhds hb₀)`. Establish `h1 : ∀ᶠ b in 𝓝 b₀, ψ b ρ ≠ 0` using `(hc ρ).eventually_ne hρ`. Establish `h2 : ∀ j, ∀ᶠ b in 𝓝 b₀, ‖valAt' (1 : Over.mk (spMap (ψ b)) ⟶ G).left V (f j) - χ₀ (f j)‖ < δ`.

Introduce `j`. Take `⟨u, k, hu⟩` from `hrat (f j)`. Establish `hq : ContinuousAt (fun b => ψ b u / ψ b ρ ^ k) b₀` using `(hc u).div ((hc ρ).pow k) (pow_ne_zero k hρ)`. Establish `hq0 : ψ b₀ u / ψ b₀ ρ ^ k = χ₀ (f j)`. Rewrite using `[div_eq_iff (pow_ne_zero k hρ), ← hu _ hρ, hχv]`.

Establish `hb` using `hq.eventually (Metric.ball_mem_nhds _ hδ)`. Use `filter_upwards [hb, h1] with b hb1 hb2`. Establish `: valAt' (1 : Over.mk (spMap (ψ b)) ⟶ G).left V (f j) = ψ b u / ψ b ρ ^ k`. Rewrite using `[eq_div_iff (pow_ne_zero k hb2)]`. Conclude with `hu _ hb2`.

Rewrite using `[this, ← hq0]`. Simplify `hb1` using `[dist_eq_norm]`. Use `filter_upwards [h1, eventually_all.2 h2] with b a1 a2 using ⟨a1, a2⟩`. Take `⟨ε₁, hε₁, hball⟩` from `Metric.eventually_nhds_iff_ball.1 hev`. Take `⟨ε', hε', h1', h2', h3'⟩ : ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε₁ ∧ ε' ≤ ε ∧ ε' ≤ δ` from `⟨min ε₁ (min ε δ), lt_min hε₁ (lt_min hε hδ), min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩`.

Establish `hex : ∀ b z, ∃ x : Over.mk (spMap (ψ b)) ⟶ G, b ∈ ball b₀ ε → z ∈ ball (0 : Fin g → ℂ) ε → ⊤ ≤ x.left ⁻¹ᵁ V ∧ ∀ a, valAt' x.left V a = Ψa b z a`. Introduce `b z`. Distinguish the cases in `h : b ∈ ball b₀ ε ∧ z ∈ ball (0 : Fin g → ℂ) ε`. Take `⟨x, hx, hv⟩` from `exists_pt hV (ψ b) (Ψa b z) (fun r => congrArg (fun q => q r) (hprop b h.1 z h.2).1)`. Conclude with `⟨x, fun _ _ => ⟨hx, hv⟩⟩`.

Conclude with `⟨1, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩`. Use `choose Ψ hΨ using hex`. Establish `hbε : ∀ b ∈ ball b₀ ε', b ∈ ball b₀ ε` using `fun b hb => ball_subset_ball h2' hb`. Establish `hzε : ∀ z ∈ ball (0 : Fin g → ℂ) ε', z ∈ ball (0 : Fin g → ℂ) ε` using `fun b hb => ball_subset_ball h2' hb`. Establish `hzero : (0 : Fin g → ℂ) ∈ ball (0 : Fin g → ℂ) ε'` using `mem_ball_self hε'`.

Establish `hone : ∀ b ∈ ball b₀ ε', Ψ b 0 = 1`. Introduce `b hb`. Take `⟨hb1, hb2⟩` from `hball b (ball_subset_ball h1' hb)`. Establish `hin` using `(hθ (ψ b) hb1).1`. Establish `hc : (evalHom (1 : Over.mk (spMap (ψ b)) ⟶ G).left V hin).comp (algebraMap R Γ(G.left, V)) = ψ b` using `RingHom.ext fun r => valR_cst G.hom V _ _ (Over.w _) hin r`.

Establish `hv : ∀ a, evalHom (1 : Over.mk (spMap (ψ b)) ⟶ G).left V hin a = valAt' (1 : Over.mk (spMap (ψ b)) ⟶ G).left V a` using `fun a => (valR_eq _ _ hin a).symm`. Use `(huniq b (ball_subset_ball h3' hb) _ hc (fun j => by rw [hv]; exact hb2 j)).2` as an intermediate fact. Establish `hz : (fun c => evalHom (1 : Over.mk (spMap (ψ b)) ⟶ G).left V hin (t c)) = 0`. Use function extensionality and compare the values at `c`. Rewrite using `[hv]`.

Conclude with `(hθ (ψ b) hb1).2.1 c`. Rewrite `this` using `[hz]`. Take `⟨hx, hvx⟩` from `hΨ b 0 (hbε b hb) (hzε 0 hzero)`. Use `pt_ext hV hx hin fun a => ?_` and prove the remaining obligations. Rewrite using `[hvx, ← this, hv]`.

Establish `hHol : ∀ p ∈ ball b₀ ε' ×ˢ ball (0 : Fin g → ℂ) ε', HolAt (fun q : (Fin n → ℂ) × (Fin g → ℂ) => (Ψ q.1 q.2).left) p`. Introduce `p hp`. Establish `hop : IsOpen (ball b₀ ε' ×ˢ ball (0 : Fin g → ℂ) ε')` using `isOpen_ball.prod isOpen_ball`. Establish `hnb` using `hop.mem_nhds hp`. Establish `hop' : IsOpen (ball b₀ ε ×ˢ ball (0 : Fin g → ℂ) ε)` using `isOpen_ball.prod isOpen_ball`.

Use `holAt_of_affine hV (hΨ _ _ (hbε _ hp.1) (hzε _ hp.2)).1 ?_ fun a => ?_` and prove the remaining obligations. Use `filter_upwards [hnb] with q hq using (hΨ _ _ (hbε _ hq.1) (hzε _ hq.2)).1`. Establish `hd : DifferentiableAt ℂ (fun bz : (Fin n → ℂ) × (Fin g → ℂ) => Ψa bz.1 bz.2 a) p` using `(hdiff a).differentiableAt (hop'.mem_nhds ⟨hbε _ hp.1, hzε _ hp.2⟩)`. Use `hd.congr_of_eventuallyEq ?_` and prove the remaining obligations. Use `filter_upwards [hnb] with q hq using (hΨ _ _ (hbε _ hq.1) (hzε _ hq.2)).2 a`.

Establish `hfib : ∀ b ∈ ball b₀ ε', HolAt (fun z => (Ψ b z).left) 0`. Introduce `b hb`. Use `(hHol (b, 0) ⟨hb, hzero⟩).precomp (k := fun z : Fin g → ℂ => (b, z)) (z := 0) ((differentiableAt_const b).prodMk differentiableAt_id)` as an intermediate fact. Conclude with `this`. Use `⟨V, t, N, f, ε', Ψ, hε', (ball_subset_ball h2').trans hεB, ?_, fun b hb => ⟨hone b hb, fun a => ?_, fun z hz => ?_⟩, ε', hε', fun b hb x hxV hnear => ?_⟩` and prove the remaining obligations.

Conclude with `isHolTo_of_holAt (isOpen_ball.prod isOpen_ball) hHol`. Take `⟨hb1, -⟩` from `hball b (ball_subset_ball h1' hb)`. Take `⟨hx, hvx⟩` from `hΨ b 0 (hbε b hb) (hzε 0 hzero)`. Take `⟨v', hv'⟩` from `(hfib b hb).exists_isDerivAt (Pi.single a 1)`. Establish `hb' : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (spMap (dualMap (ψ b)) ≫ (M.pt (Pi.single a 1)).left) = (Ψ b 0).left`.

Rewrite using `[tan_base M (ψ b) (Pi.single a 1), hone b hb]`. Take `⟨D₁, hD₁, hL₁⟩` from `tan_der hv'.1 hx`. Take `⟨D₂, hD₂, hL₂⟩` from `tan_der hb' hx`. Establish `hnb : ball (0 : Fin g → ℂ) ε' ∈ 𝓝 (0 : Fin g → ℂ)` using `ball_mem_nhds _ hε'`. Establish `hval : ∀ c, D₁ (t c) = if a = c then 1 else 0`.

Introduce `c`. Establish `e : (fun z => valAt' (Ψ b z).left V (t c)) =ᶠ[𝓝 0] fun z => z c` using `by filter_upwards [hnb] with z hz`. Rewrite using `[(hΨ b z (hbε b hb) (hzε z hz)).2]`. Conclude with `(hprop b (hbε b hb) z (hzε z hz)).2.1 c`. Rewrite using `[hD₁, hv'.2 V hx, e.fderiv_eq, (hasFDerivAt_apply c (0 : Fin g → ℂ)).fderiv]`.

Simplify using `[Pi.single_apply, eq_comm]`. Establish `hcon1 : ∀ r, D₁ (cst G.hom V r) = 0`. Introduce `r`. Establish `e : (fun z => valAt' (Ψ b z).left V (cst G.hom V r)) =ᶠ[𝓝 0] fun _ => ψ b r` using `by filter_upwards [hnb] with z hz`. Conclude with `val_cst V _ (hΨ b z (hbε b hb) (hzε z hz)).1 r`.

Rewrite using `[hD₁, hv'.2 V hx, e.fderiv_eq]`. Simplify using the standard rewrite rules. Take `⟨D₃, hD₃, hcon2, -⟩` from `hder (ψ b) a hb1`. Establish `hD23 : ∀ f, D₂ f = D₃ f` using `fun f => by rw [hD₂, hD₃]`. Establish `hz : D₁ - D₂ = 0`.

Use `(hprop b (hbε b hb) 0 (hzε 0 hzero)).2.2 _ (fun r => ?_) (fun x y => ?_) (fun c => ?_)` and prove the remaining obligations. Use `show D₁ (cst G.hom V r) - D₂ (cst G.hom V r) = 0`. Rewrite using `[hcon1, hD23, hcon2, sub_zero]`. Simplify using `only [AddMonoidHom.sub_apply]`. Rewrite using `[hL₁, hL₂, hvx, hvx]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [AddMonoidHom.sub_apply]`. Rewrite using `[hval, hD₂, (hθ (ψ b) hb1).2.2 a c, sub_self]`. Establish `heq : v' = spMap (dualMap (ψ b)) ≫ (M.pt (Pi.single a 1)).left`. Use `point_ext hV ((le_preimage_dual_iff hv'.1 V).2 hx) ((le_preimage_dual_iff hb' V).2 hx) fun f => ?_` and prove the remaining obligations.

Use `TrivSqZeroExt.ext ((fst_valR hv'.1 hx f).trans (fst_valR hb' hx f).symm) ?_` and prove the remaining obligations. Use `DFunLike.congr_fun hz f` as an intermediate fact. Simplify using `only [AddMonoidHom.sub_apply, AddMonoidHom.zero_apply, sub_eq_zero] at this`. Rewrite using `[← hD₁, ← hD₂, this]`. Rewrite using `[← heq]`.

Conclude with `(isDerivAt0_iff _ _ _).2 hv'`. Take `⟨hx, hvx⟩` from `hΨ b z (hbε b hb) (hzε z hz)`. Use `⟨hx, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[hvx]`. Conclude with `(hprop b (hbε b hb) z (hzε z hz)).2.1 a`.

Establish `hbδ` using `ball_subset_ball h3' hb`. Establish `hc : (evalHom x.left V hxV).comp (algebraMap R Γ(G.left, V)) = ψ b` using `RingHom.ext fun r => valR_cst G.hom V _ _ (Over.w x) hxV r`. Establish `hv : ∀ a, evalHom x.left V hxV a = valAt' x.left V a` using `fun a => (valR_eq _ _ hxV a).symm`. Establish `hΨb₀ : ∀ a, valAt' (Ψ b₀ 0).left V a = χ₀ a` using `fun a => by`. Rewrite using `[(hΨ b₀ 0 (mem_ball_self hε) (hzε 0 hzero)).2, hΨ₀]`.

Establish `hn : ∀ j, ‖evalHom x.left V hxV (f j) - χ₀ (f j)‖ < δ` using `fun j => by`. Rewrite using `[hv, ← hΨb₀]`. Conclude with `(hnear j).trans_le h3'`. Take `⟨-, hχ⟩` from `huniq b hbδ _ hc hn`. Establish `hmem : (fun a => valAt' x.left V (t a)) ∈ ball (0 : Fin g → ℂ) ε'`.

Rewrite using `[mem_ball_zero_iff, pi_norm_lt_iff hε']`. Introduce `c`. Take `⟨j, hj⟩` from `hft c`. Use `hnear j` as an intermediate fact. Rewrite `this` using `[hΨb₀, hj, ht₀, sub_zero]`.

Conclude with `this`. Use `⟨hmem, ?_⟩` and prove the remaining obligations. Take `⟨hx, hvx⟩` from `hΨ b _ (hbε b hb) (hzε _ hmem)`. Use `pt_ext hV hxV hx fun a => ?_` and prove the remaining obligations. Rewrite using `[hvx, ← hv, hχ]`.

Simplify using `only [hv]`.
-/
theorem exp_chart : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (g n : ℕ) (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)), Smooth G.hom → IsHolPts B ψ → ∀ b₀ ∈ B, ∃ (V : G.left.Opens) (t : Fin g → Γ(G.left, V)) (N : ℕ) (f : Fin N → Γ(G.left, V)) (ε : ℝ) (Ψ : ∀ b : Fin n → ℂ, (Fin g → ℂ) → (Over.mk (spMap (ψ b)) ⟶ G)), 0 < ε ∧ ball b₀ ε ⊆ B ∧ IsHolTo (ball b₀ ε ×ˢ ball (0 : Fin g → ℂ) ε) (fun bz : (Fin n → ℂ) × (Fin g → ℂ) => (Ψ bz.1 bz.2).left) ∧ (∀ b ∈ ball b₀ ε, Ψ b 0 = 1 ∧ (∀ a : Fin g, IsDerivAt0 (fun z => (Ψ b z).left) (Pi.single a 1) (spMap (dualMap (ψ b)) ≫ (M.pt (Pi.single a 1)).left)) ∧ ∀ z ∈ ball (0 : Fin g → ℂ) ε, ⊤ ≤ (Ψ b z).left ⁻¹ᵁ V ∧ ∀ a, valAt' (Ψ b z).left V (t a) = z a) ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ b ∈ ball b₀ δ, ∀ x : Over.mk (spMap (ψ b)) ⟶ G, ⊤ ≤ x.left ⁻¹ᵁ V → (∀ j, ‖valAt' x.left V (f j) - valAt' (Ψ b₀ 0).left V (f j)‖ < δ) → (fun a => valAt' x.left V (t a)) ∈ ball (0 : Fin g → ℂ) ε ∧ x = Ψ b (fun a => valAt' x.left V (t a)) := by
  intro R _ G _ _ g n M B ψ hsm hB b₀ hb₀
  obtain ⟨V, t, ρ, hV, hρ, hss, hθ, hrat⟩ := GlobalTheory.T.exists_exp_chart_standard_smooth R G g M (ψ b₀) hsm
  letI : Algebra R Γ(G.left, V) := (cst G.hom V).toAlgebra
  haveI : Algebra.IsStandardSmooth R Γ(G.left, V) := hss
  have halg : ∀ r, algebraMap R Γ(G.left, V) r = cst G.hom V r := fun _ => rfl
  have h₀ := (hθ (ψ b₀) hρ).1
  let χ₀ : Γ(G.left, V) →+* ℂ := evalHom (1 : Over.mk (spMap (ψ b₀)) ⟶ G).left V h₀
  have hχv : ∀ a, valAt' (1 : Over.mk (spMap (ψ b₀)) ⟶ G).left V a = χ₀ a := fun a => valR_eq _ _ h₀ a
  have hχc : χ₀.comp (algebraMap R Γ(G.left, V)) = ψ b₀ := RingHom.ext fun r => by
    show χ₀ (cst G.hom V r) = ψ b₀ r
    rw [← hχv]; exact val_cst V _ h₀ r
  have ht₀ : ∀ c, χ₀ (t c) = 0 := fun c => by rw [← hχv]; exact (hθ (ψ b₀) hρ).2.1 c
  have hder : ∀ (θ : R →+* ℂ) (a : Fin g), θ ρ ≠ 0 → ∃ D : Γ(G.left, V) →+ ℂ,
      (∀ f, D f = TrivSqZeroExt.snd (valR (spMap (dualMap θ) ≫ (M.pt (Pi.single a 1)).left) V f)) ∧
      (∀ r, D (cst G.hom V r) = 0) ∧
      (∀ f f', D (f * f') = valAt' (1 : Over.mk (spMap θ) ⟶ G).left V f * D f' +
        valAt' (1 : Over.mk (spMap θ) ⟶ G).left V f' * D f) := by
    intro θ a hr
    have hin := (hθ θ hr).1
    obtain ⟨D, hD, hL⟩ := tan_der (tan_base M θ (Pi.single a 1)) hin
    refine ⟨D, hD, fun r => ?_, hL⟩
    have hv := (le_preimage_dual_iff (tan_base M θ (Pi.single a 1)) V).2 hin
    rw [hD, valR_eq _ _ hv, valR_cst G.hom V _ _ (tan_over M θ (Pi.single a 1)) hv]
    simp [TrivSqZeroExt.algebraMap_eq_inl']
  have hD₀ : ∀ D : Γ(G.left, V) →+ ℂ, (∀ r, D (algebraMap R _ r) = 0) →
      (∀ x y, D (x * y) = χ₀ x * D y + χ₀ y * D x) → (∀ c, D (t c) = 0) → D = 0 := by
    intro D hc hl hz
    obtain ⟨c, hcD, -⟩ := GlobalTheory.T.derivation_vanishing_constants R G g M (ψ b₀) hsm V hV h₀ D hc (fun f f' => by
      rw [hχv, hχv]; exact hl f f')
    have hc0 : ∀ a, c a = 0 := fun a => by
      have := hcD (t a)
      rw [hz a] at this
      simp only [(hθ (ψ b₀) hρ).2.2] at this
      simpa using this.symm
    ext f
    rw [hcD f]
    simp [hc0]
  have hS₀ : ∀ c, ∃ D : Γ(G.left, V) →+ ℂ, (∀ r, D (algebraMap R _ r) = 0) ∧
      (∀ x y, D (x * y) = χ₀ x * D y + χ₀ y * D x) ∧ ∀ c', D (t c') = if c = c' then 1 else 0 := by
    intro c
    obtain ⟨D, hD, hc, hl⟩ := hder (ψ b₀) c hρ
    refine ⟨D, hc, fun x y => ?_, fun c' => ?_⟩
    · rw [hl, hχv, hχv]
    · rw [hD]; exact (hθ (ψ b₀) hρ).2.2 c c'
  obtain ⟨N, f, ε, δ, Ψa, hε, hδ, hεB, hΨ₀, hprop, hdiff, hft, huniq⟩ :=
    GlobalTheory.T.derivation_determines_chart R Γ(G.left, V) n g B ψ hB.1 hB.2 b₀ hb₀ χ₀ t hχc ht₀ hD₀ hS₀

  have hev : ∀ᶠ b in 𝓝 b₀, ψ b ρ ≠ 0 ∧
      ∀ j, ‖valAt' (1 : Over.mk (spMap (ψ b)) ⟶ G).left V (f j) - χ₀ (f j)‖ < δ := by
    have hc : ∀ u, ContinuousAt (fun b => ψ b u) b₀ := fun u =>
      (hB.2 u).continuousOn.continuousAt (hB.1.mem_nhds hb₀)
    have h1 : ∀ᶠ b in 𝓝 b₀, ψ b ρ ≠ 0 := (hc ρ).eventually_ne hρ
    have h2 : ∀ j, ∀ᶠ b in 𝓝 b₀,
        ‖valAt' (1 : Over.mk (spMap (ψ b)) ⟶ G).left V (f j) - χ₀ (f j)‖ < δ := by
      intro j
      obtain ⟨u, k, hu⟩ := hrat (f j)
      have hq : ContinuousAt (fun b => ψ b u / ψ b ρ ^ k) b₀ := (hc u).div ((hc ρ).pow k) (pow_ne_zero k hρ)
      have hq0 : ψ b₀ u / ψ b₀ ρ ^ k = χ₀ (f j) := by
        rw [div_eq_iff (pow_ne_zero k hρ), ← hu _ hρ, hχv]
      have hb := hq.eventually (Metric.ball_mem_nhds _ hδ)
      filter_upwards [hb, h1] with b hb1 hb2
      have : valAt' (1 : Over.mk (spMap (ψ b)) ⟶ G).left V (f j) = ψ b u / ψ b ρ ^ k := by
        rw [eq_div_iff (pow_ne_zero k hb2)]; exact hu _ hb2
      rw [this, ← hq0]
      simpa [dist_eq_norm] using hb1
    filter_upwards [h1, eventually_all.2 h2] with b a1 a2 using ⟨a1, a2⟩
  obtain ⟨ε₁, hε₁, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  obtain ⟨ε', hε', h1', h2', h3'⟩ : ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε₁ ∧ ε' ≤ ε ∧ ε' ≤ δ :=
    ⟨min ε₁ (min ε δ), lt_min hε₁ (lt_min hε hδ), min_le_left _ _,
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  have hex : ∀ b z, ∃ x : Over.mk (spMap (ψ b)) ⟶ G, b ∈ ball b₀ ε → z ∈ ball (0 : Fin g → ℂ) ε →
      ⊤ ≤ x.left ⁻¹ᵁ V ∧ ∀ a, valAt' x.left V a = Ψa b z a := by
    intro b z
    by_cases h : b ∈ ball b₀ ε ∧ z ∈ ball (0 : Fin g → ℂ) ε
    · obtain ⟨x, hx, hv⟩ := exists_pt hV (ψ b) (Ψa b z) (fun r => congrArg (fun q => q r) (hprop b h.1 z h.2).1)
      exact ⟨x, fun _ _ => ⟨hx, hv⟩⟩
    · exact ⟨1, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose Ψ hΨ using hex
  have hbε : ∀ b ∈ ball b₀ ε', b ∈ ball b₀ ε := fun b hb => ball_subset_ball h2' hb
  have hzε : ∀ z ∈ ball (0 : Fin g → ℂ) ε', z ∈ ball (0 : Fin g → ℂ) ε := fun b hb => ball_subset_ball h2' hb
  have hzero : (0 : Fin g → ℂ) ∈ ball (0 : Fin g → ℂ) ε' := mem_ball_self hε'
  have hone : ∀ b ∈ ball b₀ ε', Ψ b 0 = 1 := by
    intro b hb
    obtain ⟨hb1, hb2⟩ := hball b (ball_subset_ball h1' hb)
    have hin := (hθ (ψ b) hb1).1
    have hc : (evalHom (1 : Over.mk (spMap (ψ b)) ⟶ G).left V hin).comp (algebraMap R Γ(G.left, V)) = ψ b :=
      RingHom.ext fun r => valR_cst G.hom V _ _ (Over.w _) hin r
    have hv : ∀ a, evalHom (1 : Over.mk (spMap (ψ b)) ⟶ G).left V hin a = valAt' (1 : Over.mk (spMap (ψ b)) ⟶ G).left V a :=
      fun a => (valR_eq _ _ hin a).symm
    have := (huniq b (ball_subset_ball h3' hb) _ hc (fun j => by rw [hv]; exact hb2 j)).2
    have hz : (fun c => evalHom (1 : Over.mk (spMap (ψ b)) ⟶ G).left V hin (t c)) = 0 := by
      funext c
      rw [hv]; exact (hθ (ψ b) hb1).2.1 c
    rw [hz] at this
    obtain ⟨hx, hvx⟩ := hΨ b 0 (hbε b hb) (hzε 0 hzero)
    refine pt_ext hV hx hin fun a => ?_
    rw [hvx, ← this, hv]
  have hHol : ∀ p ∈ ball b₀ ε' ×ˢ ball (0 : Fin g → ℂ) ε', HolAt (fun q : (Fin n → ℂ) × (Fin g → ℂ) => (Ψ q.1 q.2).left) p := by
    intro p hp
    have hop : IsOpen (ball b₀ ε' ×ˢ ball (0 : Fin g → ℂ) ε') := isOpen_ball.prod isOpen_ball
    have hnb := hop.mem_nhds hp
    have hop' : IsOpen (ball b₀ ε ×ˢ ball (0 : Fin g → ℂ) ε) := isOpen_ball.prod isOpen_ball
    refine holAt_of_affine hV (hΨ _ _ (hbε _ hp.1) (hzε _ hp.2)).1 ?_ fun a => ?_
    · filter_upwards [hnb] with q hq using (hΨ _ _ (hbε _ hq.1) (hzε _ hq.2)).1
    · have hd : DifferentiableAt ℂ (fun bz : (Fin n → ℂ) × (Fin g → ℂ) => Ψa bz.1 bz.2 a) p :=
        (hdiff a).differentiableAt (hop'.mem_nhds ⟨hbε _ hp.1, hzε _ hp.2⟩)
      refine hd.congr_of_eventuallyEq ?_
      filter_upwards [hnb] with q hq using (hΨ _ _ (hbε _ hq.1) (hzε _ hq.2)).2 a
  have hfib : ∀ b ∈ ball b₀ ε', HolAt (fun z => (Ψ b z).left) 0 := by
    intro b hb
    have := (hHol (b, 0) ⟨hb, hzero⟩).precomp (k := fun z : Fin g → ℂ => (b, z)) (z := 0)
      ((differentiableAt_const b).prodMk differentiableAt_id)
    exact this
  refine ⟨V, t, N, f, ε', Ψ, hε', (ball_subset_ball h2').trans hεB, ?_, fun b hb => ⟨hone b hb, fun a => ?_, fun z hz => ?_⟩, ε', hε', fun b hb x hxV hnear => ?_⟩
  · exact isHolTo_of_holAt (isOpen_ball.prod isOpen_ball) hHol
  ·
    obtain ⟨hb1, -⟩ := hball b (ball_subset_ball h1' hb)
    obtain ⟨hx, hvx⟩ := hΨ b 0 (hbε b hb) (hzε 0 hzero)
    obtain ⟨v', hv'⟩ := (hfib b hb).exists_isDerivAt (Pi.single a 1)
    have hb' : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (spMap (dualMap (ψ b)) ≫ (M.pt (Pi.single a 1)).left) = (Ψ b 0).left := by
      rw [tan_base M (ψ b) (Pi.single a 1), hone b hb]
    obtain ⟨D₁, hD₁, hL₁⟩ := tan_der hv'.1 hx
    obtain ⟨D₂, hD₂, hL₂⟩ := tan_der hb' hx
    have hnb : ball (0 : Fin g → ℂ) ε' ∈ 𝓝 (0 : Fin g → ℂ) := ball_mem_nhds _ hε'
    have hval : ∀ c, D₁ (t c) = if a = c then 1 else 0 := by
      intro c
      have e : (fun z => valAt' (Ψ b z).left V (t c)) =ᶠ[𝓝 0] fun z => z c := by
        filter_upwards [hnb] with z hz
        rw [(hΨ b z (hbε b hb) (hzε z hz)).2]
        exact (hprop b (hbε b hb) z (hzε z hz)).2.1 c
      rw [hD₁, hv'.2 V hx, e.fderiv_eq, (hasFDerivAt_apply c (0 : Fin g → ℂ)).fderiv]
      simp [Pi.single_apply, eq_comm]
    have hcon1 : ∀ r, D₁ (cst G.hom V r) = 0 := by
      intro r
      have e : (fun z => valAt' (Ψ b z).left V (cst G.hom V r)) =ᶠ[𝓝 0] fun _ => ψ b r := by
        filter_upwards [hnb] with z hz
        exact val_cst V _ (hΨ b z (hbε b hb) (hzε z hz)).1 r
      rw [hD₁, hv'.2 V hx, e.fderiv_eq]
      simp
    obtain ⟨D₃, hD₃, hcon2, -⟩ := hder (ψ b) a hb1
    have hD23 : ∀ f, D₂ f = D₃ f := fun f => by rw [hD₂, hD₃]
    have hz : D₁ - D₂ = 0 := by
      refine (hprop b (hbε b hb) 0 (hzε 0 hzero)).2.2 _ (fun r => ?_) (fun x y => ?_) (fun c => ?_)
      · show D₁ (cst G.hom V r) - D₂ (cst G.hom V r) = 0
        rw [hcon1, hD23, hcon2, sub_zero]
      · simp only [AddMonoidHom.sub_apply]
        rw [hL₁, hL₂, hvx, hvx]
        ring
      · simp only [AddMonoidHom.sub_apply]
        rw [hval, hD₂, (hθ (ψ b) hb1).2.2 a c, sub_self]
    have heq : v' = spMap (dualMap (ψ b)) ≫ (M.pt (Pi.single a 1)).left := by
      refine point_ext hV ((le_preimage_dual_iff hv'.1 V).2 hx) ((le_preimage_dual_iff hb' V).2 hx) fun f => ?_
      refine TrivSqZeroExt.ext ((fst_valR hv'.1 hx f).trans (fst_valR hb' hx f).symm) ?_
      have := DFunLike.congr_fun hz f
      simp only [AddMonoidHom.sub_apply, AddMonoidHom.zero_apply, sub_eq_zero] at this
      rw [← hD₁, ← hD₂, this]
    rw [← heq]
    exact (isDerivAt0_iff _ _ _).2 hv'
  · obtain ⟨hx, hvx⟩ := hΨ b z (hbε b hb) (hzε z hz)
    refine ⟨hx, fun a => ?_⟩
    rw [hvx]
    exact (hprop b (hbε b hb) z (hzε z hz)).2.1 a
  · have hbδ := ball_subset_ball h3' hb
    have hc : (evalHom x.left V hxV).comp (algebraMap R Γ(G.left, V)) = ψ b :=
      RingHom.ext fun r => valR_cst G.hom V _ _ (Over.w x) hxV r
    have hv : ∀ a, evalHom x.left V hxV a = valAt' x.left V a := fun a => (valR_eq _ _ hxV a).symm
    have hΨb₀ : ∀ a, valAt' (Ψ b₀ 0).left V a = χ₀ a := fun a => by
      rw [(hΨ b₀ 0 (mem_ball_self hε) (hzε 0 hzero)).2, hΨ₀]
    have hn : ∀ j, ‖evalHom x.left V hxV (f j) - χ₀ (f j)‖ < δ := fun j => by
      rw [hv, ← hΨb₀]
      exact (hnear j).trans_le h3'
    obtain ⟨-, hχ⟩ := huniq b hbδ _ hc hn
    have hmem : (fun a => valAt' x.left V (t a)) ∈ ball (0 : Fin g → ℂ) ε' := by
      rw [mem_ball_zero_iff, pi_norm_lt_iff hε']
      intro c
      obtain ⟨j, hj⟩ := hft c
      have := hnear j
      rw [hΨb₀, hj, ht₀, sub_zero] at this
      exact this
    refine ⟨hmem, ?_⟩
    obtain ⟨hx, hvx⟩ := hΨ b _ (hbε b hb) (hzε _ hmem)
    refine pt_ext hV hxV hx fun a => ?_
    rw [hvx, ← hv, hχ]
    simp only [hv]

end GlobalTheory.CompanionTheory.Ar.Flat
