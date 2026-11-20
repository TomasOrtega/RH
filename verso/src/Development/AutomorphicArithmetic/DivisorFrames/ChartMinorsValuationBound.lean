import Development.AutomorphicArithmetic.LocalEmbeddings.RootFrame
import Development.AutomorphicArithmetic.DivisorFrames.LatticeMinorsValuationProfile
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentSectionsOnNormalModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct Matrix
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.RootFrame

/- English proof (translation)
Take `⟨_, h1, h2⟩` from `ioOf_spec F v e`. Establish `hp1 : (1 : ℝ) < (resP v : ℝ)` using `by exact_mod_cast hp.out.one_lt`. Establish `hl : 0 < Real.log (resP v)` using `Real.log_pos hp1`. Establish `hn : ‖ioOf (resP v) e (resP v : AlgebraicClosure F)‖ = ((resP v : ℕ) : ℝ)⁻¹`. Rewrite using `[map_natCast, ← Padic.norm_p, ← PadicComplex.norm_extends']`.

Simplify using the standard rewrite rules. Establish `hw : e.w (resP v : AlgebraicClosure F) < 1`. Establish `h3 : ¬ e.w (resP v : AlgebraicClosure F)⁻¹ ≤ 1`. Rewrite using `[← e.mem_O, ← h1, map_inv₀, norm_inv, hn, inv_inv, not_le]`. Conclude with `hp1`.

Rewrite `h3` using `[map_inv₀, not_le, one_lt_inv_iff₀]`. Conclude with `h3.2`. Establish `h0 : 0 < e.w (resP v : AlgebraicClosure F)` using `e.w.pos (Nat.cast_ne_zero.2 hp.out.ne_zero)`. Establish `hc : 0 < -Real.log (e.w (resP v)) / Real.log (resP v)` using `div_pos (neg_pos.2 (Real.log_neg h0 hw)) hl`. Use `⟨hc, fun a => ?_⟩` and prove the remaining obligations.

Break down `eq_or_ne a 0 with rfl | ha` into its components or cases. Simplify using `only [map_zero, norm_zero]`. Rewrite using `[Real.zero_rpow hc.ne']`. Establish `hna : 0 < ‖ioOf (resP v) e a‖` using `norm_pos_iff.2 ((map_ne_zero _).2 ha)`. Rewrite using `[Real.rpow_def_of_pos hna, mul_comm, ← h2 a, Real.exp_log (e.w.pos ha)]`.
-/
private theorem UpperTheory.extension_valuation_as_power {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (e : TrueGeo.Ext v) [hp : Fact (resP v).Prime] :
    0 < -Real.log (e.w (resP v)) / Real.log (resP v) ∧
      ∀ a, e.w a = ‖ioOf (resP v) e a‖ ^ (-Real.log (e.w (resP v)) / Real.log (resP v)) := by
  obtain ⟨_, h1, h2⟩ := ioOf_spec F v e
  have hp1 : (1 : ℝ) < (resP v : ℝ) := by exact_mod_cast hp.out.one_lt
  have hl : 0 < Real.log (resP v) := Real.log_pos hp1
  have hn : ‖ioOf (resP v) e (resP v : AlgebraicClosure F)‖ = ((resP v : ℕ) : ℝ)⁻¹ := by
    rw [map_natCast, ← Padic.norm_p, ← PadicComplex.norm_extends']
    simp
  have hw : e.w (resP v : AlgebraicClosure F) < 1 := by
    have h3 : ¬ e.w (resP v : AlgebraicClosure F)⁻¹ ≤ 1 := by
      rw [← e.mem_O, ← h1, map_inv₀, norm_inv, hn, inv_inv, not_le]
      exact hp1
    rw [map_inv₀, not_le, one_lt_inv_iff₀] at h3
    exact h3.2
  have h0 : 0 < e.w (resP v : AlgebraicClosure F) := e.w.pos (Nat.cast_ne_zero.2 hp.out.ne_zero)
  have hc : 0 < -Real.log (e.w (resP v)) / Real.log (resP v) := div_pos (neg_pos.2 (Real.log_neg h0 hw)) hl
  refine ⟨hc, fun a => ?_⟩
  rcases eq_or_ne a 0 with rfl | ha
  · simp only [map_zero, norm_zero]
    rw [Real.zero_rpow hc.ne']
  · have hna : 0 < ‖ioOf (resP v) e a‖ := norm_pos_iff.2 ((map_ne_zero _).2 ha)
    rw [Real.rpow_def_of_pos hna, mul_comm, ← h2 a, Real.exp_log (e.w.pos ha)]

/- English proof (translation)
Unfold `colMinor`. Rewrite using `[RingHom.map_det]`. Both sides reduce to the same expression.
-/
private theorem UpperTheory.colMinor_map {K L : Type} [CommRing K] [CommRing L] (φ : K →+* L) {n r : ℕ}
    (X : Matrix (Fin n) (Fin r) K) (k : ℕ) (hk : k ≤ r) (σ : Fin k → Fin n) :
    colMinor (X.map φ) k hk σ = φ (colMinor X k hk σ) := by
  unfold colMinor
  rw [RingHom.map_det]
  rfl

/- English proof (translation)
Introduce `E _ _ _ H X t F _ _ Y V W p hp ρ J U n r u P T κ f l h1 h2 h3 h4`. Use `⟨h1, h2, fun v e y z yt ht a ha => ?_⟩` and prove the remaining obligations. Take `⟨⟨δ, hδ, hκ, hinj, hlat⟩, hb⟩` from `h4 v e y z yt ht a ha`. Establish `hv : resP v = p` using `ht.1`. Substitute `hv` using the available equality.

Take `⟨hc, hw⟩` from `UpperTheory.extension_valuation_as_power v e`. Establish `hl : 0 < Real.log (resP v)` using `Real.log_pos (by exact_mod_cast hp.out.one_lt)`. Use `⟨?_, fun b hbU w hw1 k => ?_⟩` and prove the remaining obligations. Take `⟨ν, hν0, hν1, hν2, hν3⟩` from `UpperTheory.lattice_minors_valuation_profile E H X t (resP v) _ n r _ _ δ hδ hinj hlat`. Use `⟨fun k => ν k ^ (-Real.log (e.w (resP v)) / Real.log (resP v)), fun k hk => Real.rpow_pos_of_pos (hν0 k hk) _, fun i => ?_, fun k hk σ => ?_, fun k hk => ?_⟩` and prove the remaining obligations.

Establish `hs` using `GlobalTheory.LineNorm.Chart.stepLog_eq ρ u (resP v) i v e y hp.out (psi (resP v) e y) rfl`. Establish `hlt : ∀ x : Sp ℂ_[resP v] ⟶ X, GlobalTheory.ShFam.Pad.lat t (resP v) x (decide (resP v = resP v)) = latHT t (resP v) x`. Introduce `x`. Rewrite using `[decide_eq_true rfl]`. Both sides reduce to the same expression.

Rewrite `hs` using `[hlt, hν1 i, hκ]`. Rewrite using `[h3 i v e y rfl, hs, Real.log_rpow (hν0 _ i.2), Real.log_rpow (hν0 _ i.2.le)]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hw, ← UpperTheory.colMinor_map]`.

Conclude with `Real.rpow_le_rpow (norm_nonneg _) (hν2 k hk σ) hc.le`. Take `⟨σ, hσ⟩` from `hν3 k hk`. Conclude with `⟨σ, by rw [hw, ← UpperTheory.colMinor_map, hσ]⟩`. Establish `hm : ∀ (M : Matrix (Fin n) (Fin r) (AlgebraicClosure F)) k, (M.map (ioOf (resP v) e) *ᵥ (ioOf (resP v) e ∘ w)) k = ioOf (resP v) e ((M *ᵥ w) k)` using `fun M k => (RingHom.map_mulVec _ M w k).symm`. Use `hb b hbU (ioOf (resP v) e ∘ w) (fun k => by` as an intermediate fact.

Rewrite using `[hm]`. Use `hw1 k` as an intermediate fact. Rewrite `this` using `[hw]`. Assume the negation of the conclusion as `hcon`. Conclude with `absurd (Real.one_lt_rpow (not_le.1 hcon) hc) (not_lt.2 this)) k`.

Rewrite `this` using `[hm, hm, ← map_sub]`. Rewrite using `[hw]`. Conclude with `Real.rpow_lt_one (norm_nonneg _) this hc`.
-/
theorem UpperTheory.chart_minors_valuation_bound :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (W : Y.X.Opens) (p : ℕ) [Fact p.Prime] (ρ : Y.X ⟶ X) (J : Type) (U : J → V.X.Opens) (n r : ℕ) (u : (∀ y : Y.X, Fin r → (Sp (DualNumber (Y.X.presheaf.stalk y)) ⟶ t.G.left))) (P : J → Matrix (Fin n) (Fin r) V.G.functionField) (T : Y.X → Matrix (Fin r) (Fin r) Y.Fn) (κ : ℝ) (f : Fin r → Y.X → Y.Fn) (l : Fin r → PtFn Y), (∀ x, (T x).BlockTriangular id ∧ ∀ i, UnitAt x (f i x * T x i i)) → (∀ a (z : V.G), V.j z ∈ U a → ∀ k i, RegAt z (locM V (P a) T (V.π z) k i)) → (∀ i v e y, resP v = p → l i v e y = Real.log (e.w (TrueGeo.valAt y.1 (f i (below y.1) * T (below y.1) i i))) + stepLog t ρ u p i v e y + κ * Real.log (e.w (p : AlgebraicClosure F))) → CutAt t V W p ρ U u P T κ → SideData V W p U P T f l := by
  intro E _ _ _ H X t F _ _ Y V W p hp ρ J U n r u P T κ f l h1 h2 h3 h4
  refine ⟨h1, h2, fun v e y z yt ht a ha => ?_⟩
  obtain ⟨⟨δ, hδ, hκ, hinj, hlat⟩, hb⟩ := h4 v e y z yt ht a ha
  have hv : resP v = p := ht.1
  subst hv
  obtain ⟨hc, hw⟩ := UpperTheory.extension_valuation_as_power v e
  have hl : 0 < Real.log (resP v) := Real.log_pos (by exact_mod_cast hp.out.one_lt)
  refine ⟨?_, fun b hbU w hw1 k => ?_⟩
  · obtain ⟨ν, hν0, hν1, hν2, hν3⟩ := UpperTheory.lattice_minors_valuation_profile E H X t (resP v) _ n r _ _ δ hδ hinj hlat
    refine ⟨fun k => ν k ^ (-Real.log (e.w (resP v)) / Real.log (resP v)),
      fun k hk => Real.rpow_pos_of_pos (hν0 k hk) _, fun i => ?_, fun k hk σ => ?_, fun k hk => ?_⟩
    · have hs := GlobalTheory.LineNorm.Chart.stepLog_eq ρ u (resP v) i v e y hp.out (psi (resP v) e y) rfl
      have hlt : ∀ x : Sp ℂ_[resP v] ⟶ X, GlobalTheory.ShFam.Pad.lat t (resP v) x (decide (resP v = resP v)) = latHT t (resP v) x := by
        intro x
        rw [decide_eq_true rfl]
        rfl
      rw [hlt, hν1 i, hκ] at hs
      rw [h3 i v e y rfl, hs, Real.log_rpow (hν0 _ i.2), Real.log_rpow (hν0 _ i.2.le)]
      field_simp
      ring
    · rw [hw, ← UpperTheory.colMinor_map]
      exact Real.rpow_le_rpow (norm_nonneg _) (hν2 k hk σ) hc.le
    · obtain ⟨σ, hσ⟩ := hν3 k hk
      exact ⟨σ, by rw [hw, ← UpperTheory.colMinor_map, hσ]⟩
  · have hm : ∀ (M : Matrix (Fin n) (Fin r) (AlgebraicClosure F)) k,
        (M.map (ioOf (resP v) e) *ᵥ (ioOf (resP v) e ∘ w)) k = ioOf (resP v) e ((M *ᵥ w) k) :=
      fun M k => (RingHom.map_mulVec _ M w k).symm
    have := hb b hbU (ioOf (resP v) e ∘ w) (fun k => by
      rw [hm]
      have := hw1 k
      rw [hw] at this
      by_contra hcon
      exact absurd (Real.one_lt_rpow (not_le.1 hcon) hc) (not_lt.2 this)) k
    rw [hm, hm, ← map_sub] at this
    rw [hw]
    exact Real.rpow_lt_one (norm_nonneg _) this hc
