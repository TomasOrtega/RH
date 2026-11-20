import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientIntegralParabolicUnfolding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilFormulaRootExchangeParabolicIntersection
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemNormalizerOfTri
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProperTriple
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemFourierJacobiSubgroupIffParabolicMulColumn
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

noncomputable section
namespace GlobalTheory.QuotIntFJ
open GlobalTheory.QuotInt

open MeasureTheory ValuativeRel Matrix in
set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `k _ _ _ _ _ _ n _ _ c ρ hρ hρc ν _ μX _ μG _ f z z' hz hz'`. Take `⟨F₁, hF₁, hf₁, rfl⟩` from `hz`. Take `⟨F₂, hF₂, hf₂, rfl⟩` from `hz'`. Use `haveI := _root_.GlobalTheory.SplitWeil.secondCountable k`. Establish `hA` using `_root_.GlobalTheory.SplitWeil.volGL_haar k n ν`.

Establish `hB` using `_root_.GlobalTheory.SplitWeil.volGL_haar k (n ⊕ Fin c) ν`. Use `haveI := hA.1`. Use `haveI := hA.2.1`. Use `haveI := hB.1`. Use `haveI := hB.2.1`.

Use `set U := _root_.GlobalTheory.RootEx.N k n c (ρ + 1)`. Use `set μU := _root_.GlobalTheory.RootEx.volN ν n c (ρ + 1)`. Use `haveI : μU.IsHaarMeasure := _root_.GlobalTheory.RootEx.VolN.isHaarMeasure_volN ν (ρ + 1)`. Use `haveI : SFinite μU := by show SFinite (_root_.GlobalTheory.RootEx.volN ν n c (ρ + 1))`. Rewrite using `[_root_.GlobalTheory.RootEx.VolN.volN_eq]`.

Use `infer_instance`. Use `set emb := _root_.GlobalTheory.RootEx.embX (k := k) (n := n) c`. Use `set col := _root_.GlobalTheory.RootEx.colE (k := k) (n := n) c (ρ + 1)`. Set `m : GL n k × (U × (n → k)) → GL (n ⊕ Fin c) k` to `fun p => emb p.1 * ↑p.2.1 * col p.2.2`. Establish `hm : Continuous m`.

Use `(_root_.GlobalTheory.RootEx.QuotStep.continuous_embX.comp continuous_fst).mul (continuous_subtype_val.comp (continuous_fst.comp continuous_snd)) |>.mul ((_root_.GlobalTheory.RootEx.QuotStep.continuous_colE (ρ + 1)).comp (continuous_snd.comp continuous_snd))` and prove the remaining obligations. Establish `hSB : ∀ φ ∈ _root_.GlobalTheory.SplitWeil.SB (GL (n ⊕ Fin c) k), Continuous φ ∧ HasCompactSupport φ` using `fun φ hφ => ⟨hφ.1.continuous, hφ.2⟩`. Establish `hcs : ∀ φ ∈ _root_.GlobalTheory.SplitWeil.SB (GL (n ⊕ Fin c) k), ∃ D : Set (GL n k × (U × (n → k))), IsCompact D ∧ ∀ p, φ (m p) ≠ 0 → p ∈ D`. Introduce `φ hφ`. Take `⟨D, hD, hDm⟩` from `_root_.GlobalTheory.RootEx.ProperTriple.proper_triple k n c ρ hρ hρc (tsupport φ) (hSB φ hφ).2`.

Conclude with `⟨D, hD, fun p hp => hDm p (subset_tsupport _ hp)⟩`. Use `set μP := μX.prod (μU.prod (Measure.pi fun _ : n => ν))`. Establish `hint : ∀ φ ∈ _root_.GlobalTheory.SplitWeil.SB (GL (n ⊕ Fin c) k), Integrable (fun p => φ (m p)) μP`. Introduce `φ hφ`. Take `⟨D, hD, hDm⟩` from `hcs φ hφ`.

Use `((hSB φ hφ).1.comp hm).integrable_of_hasCompactSupport ?_` and prove the remaining obligations. Conclude with `HasCompactSupport.intro hD (fun p hp => by by_contra h; exact hp (hDm p h))`. Establish `hint2 : ∀ φ ∈ _root_.GlobalTheory.SplitWeil.SB (GL (n ⊕ Fin c) k), ∀ g : GL n k, Integrable (fun y : U × (n → k) => φ (m (g, y))) (μU.prod (Measure.pi fun _ : n => ν))`. Introduce `φ hφ g`. Take `⟨D, hD, hDm⟩` from `hcs φ hφ`.

Use `((hSB φ hφ).1.comp (hm.comp (Continuous.prodMk_right g))).integrable_of_hasCompactSupport ?_` and prove the remaining obligations. Conclude with `HasCompactSupport.intro (hD.image continuous_snd) (fun y hy => by by_contra h; exact hy ⟨(g, y), hDm _ h, rfl⟩)`. Use `set Λ : (GL (n ⊕ Fin c) k → ℂ) → ℂ := fun φ => ∫ (g : GL n k), ∫ (u : U), ∫ (β : n → k), φ (emb g * ↑u * col β) ∂Measure.pi fun _ ↦ ν ∂μU ∂μX with hΛ`. Establish `hΛP : ∀ φ ∈ _root_.GlobalTheory.SplitWeil.SB (GL (n ⊕ Fin c) k), Λ φ = ∫ p, φ (m p) ∂μP`. Introduce `φ hφ`.

Rewrite using `[integral_prod _ (hint φ hφ)]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)` and prove the remaining obligations. Conclude with `(integral_prod _ (hint2 φ hφ g)).symm`. Use `set R := _root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.RFJ k n c ρ`. Establish `hmR : ∀ p, m p ∈ R`.

Introduce `p`. Establish `h1 : emb p.1 ∈ R` using `(le_sup_right : _root_.GlobalTheory.RootEx.R k n c (ρ + 1) ≤ R) ((le_sup_left : emb.range ≤ _) ⟨p.1, rfl⟩)`. Establish `h2 : (p.2.1 : GL (n ⊕ Fin c) k) ∈ R` using `(le_sup_right : _root_.GlobalTheory.RootEx.R k n c (ρ + 1) ≤ R) ((le_sup_right : U ≤ _) p.2.1.2)`. Establish `h3 : col p.2.2 ∈ R` using `(le_sup_left : _root_.GlobalTheory.RootEx.R k n c ρ ≤ R) ((le_sup_right : _root_.GlobalTheory.RootEx.N k n c ρ ≤ _) (_root_.GlobalTheory.RootEx.Radical.colE_mem _ (Nat.lt_succ_self ρ)))`. Conclude with `R.mul_mem (R.mul_mem h1 h2) h3`.

Establish `hadd : ∀ φ ∈ _root_.GlobalTheory.SplitWeil.SB (GL (n ⊕ Fin c) k), ∀ ψ ∈ _root_.GlobalTheory.SplitWeil.SB (GL (n ⊕ Fin c) k), Λ (φ + ψ) = Λ φ + Λ ψ`. Introduce `φ hφ ψ hψ`. Rewrite using `[hΛP _ (add_mem hφ hψ), hΛP _ hφ, hΛP _ hψ, ← integral_add (hint φ hφ) (hint ψ hψ)]`. Both sides reduce to the same expression. Establish `hsmul : ∀ (a : ℂ) (φ : GL (n ⊕ Fin c) k → ℂ), (Λ fun g ↦ a * φ g) = a * Λ φ`.

Introduce `a φ`. Simplify using `only [hΛ]`. Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `g`.

Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `u`. Rewrite using `[← integral_const_mul]`. Establish `hloc : ∀ (φ ψ : GL (n ⊕ Fin c) k → ℂ), (∀ r ∈ R, φ r = ψ r) → Λ φ = Λ ψ`.

Introduce `φ ψ h`. Simplify using `only [hΛ]`. Use `congr 1`. Use function extensionality and compare the values at `g`. Use `congr 1`.

Use function extensionality and compare the values at `u`. Use `congr 1`. Use function extensionality and compare the values at `β`. Conclude with `h _ (hmR (g, u, β))`. Establish `hpos : ∀ φ ∈ _root_.GlobalTheory.SplitWeil.SB (GL (n ⊕ Fin c) k), (∀ g, φ g = 0 ∨ φ g = 1) → (∃ r ∈ R, φ r = 1) → Λ φ ≠ 0`.

Introduce `φ hφ h01 ⟨r, hr, hr1⟩`. Take `⟨r', hr', β, rfl⟩` from `((_root_.GlobalTheory.RootEx.FourierJacobiGroup.mem_RFJ_iff k n c ρ hρ hρc).1 r).1 hr`. Take `⟨x, u, hu, rfl⟩` from `_root_.GlobalTheory.RootEx.Radical.exists_of_mem_R hr'`. Establish `hre : ∀ p, φ (m p) = ((φ (m p)).re : ℂ)`. Introduce `p`.

Apply the tactic sequence `rcases h01 (m p) with h | h <;> simp [h]`. Rewrite using `[hΛP φ hφ, integral_congr_ae (Filter.Eventually.of_forall hre), integral_complex_ofReal]`. Take `⟨D, hD, hDm⟩` from `hcs φ hφ`. Establish `hpos` using `Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := μP) (x := (x, ⟨u, hu⟩, β)) (Complex.continuous_re.comp ((hSB φ hφ).1.comp hm)) (HasCompactSupport.intro hD (fun p hp => by`. Assume the negation of the conclusion as `h`.

Conclude with `hp (hDm p (fun h' => h (by simp [h'])))))`. Apply the tactic sequence `(fun p => by rcases h01 (m p) with h | h <;> simp [h])`. Use the proof step `(by show (φ (emb x * u * col β)).re ≠ 0; rw [hr1]; simp)`. Conclude with `hpos.ne'` after adjusting the coercions. Set `H : Subgroup (GL (n ⊕ Fin c) k)` to `{ carrier := {r | ∀ φ : GL (n ⊕ Fin c) k → ℂ, (Λ fun g ↦ φ (r * g)) = Λ φ} mul_mem' := fun {a b} ha hb φ => by`.

Establish `e : (fun g ↦ φ (a * b * g)) = fun g ↦ (fun y ↦ φ (a * y)) (b * g)`. Use function extensionality and compare the values at `g`. Simplify using `only [mul_assoc]`. Simplify using `only [Set.mem_setOf_eq] at ha hb ⊢`. Rewrite using `[e, hb (fun y ↦ φ (a * y)), ha φ]`.

Use the proof step `one_mem' := fun φ => by simp only [one_mul]`. Use the proof step `inv_mem' := fun {a} ha φ => by`. Simplify using `only [Set.mem_setOf_eq] at ha ⊢`. Use `ha (fun y ↦ φ (a⁻¹ * y))` as an intermediate fact. Simplify using `only [inv_mul_cancel_left] at this`.

Conclude with `this.symm }`. Establish `hembH : ∀ x : GL n k, emb x ∈ H`. Introduce `x φ`. Simplify using `only [hΛ]`. Establish `e : ∀ (g : GL n k) (u : U) (β : n → k), emb x * (emb g * ↑u * col β) = emb (x * g) * ↑u * col β`.

Introduce `g u β`. Simplify using `only [map_mul, mul_assoc]`. Simplify using `only [e]`. Conclude with `integral_mul_left_eq_self (μ := μX) (fun g ↦ ∫ (u : U), ∫ (β : n → k), φ (emb g * ↑u * col β) ∂Measure.pi fun _ ↦ ν ∂μU) x`. Establish `hUH : ∀ v ∈ U, v ∈ H`.

Introduce `v hv φ`. Simplify using `only [hΛ]`. Use `congr 1`. Use function extensionality and compare the values at `g`. Establish `hw : (emb g)⁻¹ * v * emb g ∈ U` using `_root_.GlobalTheory.RootEx.Model.conj_mem hv g`.

Establish `e : ∀ (u : U) (β : n → k), v * (emb g * ↑u * col β) = emb g * ↑((⟨_, hw⟩ : U) * u) * col β`. Introduce `u β`. Simplify using `only [Subgroup.coe_mul]`. Use `group`. Simplify using `only [e]`.

Conclude with `integral_mul_left_eq_self (μ := μU) (fun u : U ↦ ∫ (β : n → k), φ (emb g * ↑u * col β) ∂Measure.pi fun _ ↦ ν) (⟨_, hw⟩ : U)`. Establish `hcolH : ∀ γ : n → k, col γ ∈ H`. Introduce `γ φ`. Simplify using `only [hΛ]`. Use `congr 1`.

Use function extensionality and compare the values at `g`. Use `set δ : n → k := (↑g⁻¹ : Matrix n n k) *ᵥ γ`. Establish `hconj : emb g⁻¹ * col γ * (emb g⁻¹)⁻¹ = col δ` using `_root_.GlobalTheory.RootEx.QuotStep.conj_colE (ρ + 1) g⁻¹ γ`. Establish `e : ∀ (u : U) (β : n → k), col γ * (emb g * ↑u * col β) = emb g * (col δ * ↑u * (col δ)⁻¹) * col (δ + β)`. Introduce `u β`.

Establish `hc : col (δ + β) = col δ * col β` using `(_root_.GlobalTheory.RootEx.FourierJacobiGroup.colE_add (ρ + 1) δ β).symm`. Rewrite using `[hc, ← hconj]`. Simplify using `only [map_inv, inv_inv]`. Use `group`. Simplify using `only [e]`.

Establish `hβ : ∀ y : GL (n ⊕ Fin c) k, ∫ (β : n → k), φ (emb g * y * col (δ + β)) ∂(Measure.pi fun _ ↦ ν) = ∫ (β : n → k), φ (emb g * y * col β) ∂(Measure.pi fun _ ↦ ν)` using `fun y => integral_add_left_eq_self (fun β ↦ φ (emb g * y * col β)) δ`. Simplify using `only [hβ]`. Conclude with `_root_.GlobalTheory.RootEx.ConjVol.integral_conj_colE k n c ρ hρ hρc ν δ (fun y ↦ ∫ (β : n → k), φ (emb g * y * col β) ∂Measure.pi fun _ ↦ ν)`. Establish `hinv : ∀ r ∈ R, ∀ (φ : GL (n ⊕ Fin c) k → ℂ), (Λ fun g ↦ φ (r * g)) = Λ φ`. Introduce `r hr`.

Take `⟨r', hr', β, rfl⟩` from `((_root_.GlobalTheory.RootEx.FourierJacobiGroup.mem_RFJ_iff k n c ρ hρ hρc).1 r).1 hr`. Take `⟨x, u, hu, rfl⟩` from `_root_.GlobalTheory.RootEx.Radical.exists_of_mem_R hr'`. Conclude with `H.mul_mem (H.mul_mem (hembH x) (hUH u hu)) (hcolH β)`. Establish `hF : (F₁ - F₂) ∈ _root_.GlobalTheory.SplitWeil.SB (GL (n ⊕ Fin c) k)` using `sub_mem hF₁ hF₂`. Establish `hG : ∀ φ ∈ _root_.GlobalTheory.SplitWeil.SB (GL (n ⊕ Fin c) k), Integrable φ μG` using `fun φ hφ => (hSB φ hφ).1.integrable_of_hasCompactSupport (hSB φ hφ).2`.

Establish `hΛf : ∀ F ∈ _root_.GlobalTheory.SplitWeil.SB (GL (n ⊕ Fin c) k), (∀ h, f h = ∫ (g : GL n k), ∫ (u : U), ∫ (β : n → k), F (emb g * ↑u * col β * h) ∂(Measure.pi fun _ ↦ ν) ∂μU ∂μX) → ∀ h, (Λ fun g ↦ F (g * h)) = f h`. Introduce `F _ hf h`. Rewrite using `[hf h]`. Establish `key` using `_root_.GlobalTheory.QuotInt.integral_eq_zero_of_avg μG _ hB.2.2.2.2.1 hB.2.2.2.1 R Λ hadd hsmul hloc hinv hpos hF (fun h => by`. Establish `e : (fun g => (F₁ - F₂) (g * h)) = (fun g => F₁ (g * h)) + (fun g => (-1 : ℂ) * F₂ (g * h))`.

Use function extensionality and compare the values at `g`. Simplify using `[sub_eq_add_neg]`. Establish `hneg : (fun g => (-1 : ℂ) * F₂ (g * h)) ∈ _root_.GlobalTheory.SplitWeil.SB (GL (n ⊕ Fin c) k)` using `(_root_.GlobalTheory.SplitWeil.SB (GL (n ⊕ Fin c) k)).smul_mem (-1 : ℂ) (_root_.GlobalTheory.QuotInt.sb_right hF₂ h)`. Rewrite using `[e, hadd _ (_root_.GlobalTheory.QuotInt.sb_right hF₁ h) _ hneg, hsmul (-1) (fun g => F₂ (g * h)), hΛf F₁ hF₁ hf₁ h, hΛf F₂ hF₂ hf₂ h]`. Use the proof step `ring)`.

Establish `hsub : ∫ g, (F₁ - F₂) g ∂μG = ∫ g, F₁ g ∂μG - ∫ g, F₂ g ∂μG` using `integral_sub (hG _ hF₁) (hG _ hF₂)`. Rewrite `key` using `[hsub]`. Conclude with `sub_eq_zero.1 key`.
-/
theorem _root_.GlobalTheory.QuotIntFJ.quotIntFJ_unique : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n]
    [DecidableEq n] (c ρ : ℕ) (_ : 1 ≤ ρ) (_ : ρ < c) (ν : Measure k) [ν.IsAddHaarMeasure]
    (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure]
    (f : GL (n ⊕ Fin c) k → ℂ) (z z' : ℂ), _root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.IsQuotIntFJ ν μX μG ρ f z →
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.IsQuotIntFJ ν μX μG ρ f z' → z = z' := by
  intro k _ _ _ _ _ _ n _ _ c ρ hρ hρc ν _ μX _ μG _ f z z' hz hz'
  obtain ⟨F₁, hF₁, hf₁, rfl⟩ := hz
  obtain ⟨F₂, hF₂, hf₂, rfl⟩ := hz'
  haveI := _root_.GlobalTheory.SplitWeil.secondCountable k
  have hA := _root_.GlobalTheory.SplitWeil.volGL_haar k n ν
  have hB := _root_.GlobalTheory.SplitWeil.volGL_haar k (n ⊕ Fin c) ν
  haveI := hA.1; haveI := hA.2.1; haveI := hB.1; haveI := hB.2.1
  set U := _root_.GlobalTheory.RootEx.N k n c (ρ + 1)
  set μU := _root_.GlobalTheory.RootEx.volN ν n c (ρ + 1)
  haveI : μU.IsHaarMeasure := _root_.GlobalTheory.RootEx.VolN.isHaarMeasure_volN ν (ρ + 1)
  haveI : SFinite μU := by
    show SFinite (_root_.GlobalTheory.RootEx.volN ν n c (ρ + 1))
    rw [_root_.GlobalTheory.RootEx.VolN.volN_eq]; infer_instance
  set emb := _root_.GlobalTheory.RootEx.embX (k := k) (n := n) c
  set col := _root_.GlobalTheory.RootEx.colE (k := k) (n := n) c (ρ + 1)
  let m : GL n k × (U × (n → k)) → GL (n ⊕ Fin c) k := fun p => emb p.1 * ↑p.2.1 * col p.2.2
  have hm : Continuous m := by
    refine (_root_.GlobalTheory.RootEx.QuotStep.continuous_embX.comp continuous_fst).mul
      (continuous_subtype_val.comp (continuous_fst.comp continuous_snd)) |>.mul
      ((_root_.GlobalTheory.RootEx.QuotStep.continuous_colE (ρ + 1)).comp
        (continuous_snd.comp continuous_snd))
  have hSB : ∀ φ ∈ _root_.GlobalTheory.SplitWeil.SB (GL (n ⊕ Fin c) k), Continuous φ ∧ HasCompactSupport φ :=
    fun φ hφ => ⟨hφ.1.continuous, hφ.2⟩
  have hcs : ∀ φ ∈ _root_.GlobalTheory.SplitWeil.SB (GL (n ⊕ Fin c) k), ∃ D : Set (GL n k × (U × (n → k))),
      IsCompact D ∧ ∀ p, φ (m p) ≠ 0 → p ∈ D := by
    intro φ hφ
    obtain ⟨D, hD, hDm⟩ := _root_.GlobalTheory.RootEx.ProperTriple.proper_triple k n c ρ hρ hρc (tsupport φ) (hSB φ hφ).2
    exact ⟨D, hD, fun p hp => hDm p (subset_tsupport _ hp)⟩
  set μP := μX.prod (μU.prod (Measure.pi fun _ : n => ν))
  have hint : ∀ φ ∈ _root_.GlobalTheory.SplitWeil.SB (GL (n ⊕ Fin c) k),
      Integrable (fun p => φ (m p)) μP := by
    intro φ hφ
    obtain ⟨D, hD, hDm⟩ := hcs φ hφ
    refine ((hSB φ hφ).1.comp hm).integrable_of_hasCompactSupport ?_
    exact HasCompactSupport.intro hD (fun p hp => by by_contra h; exact hp (hDm p h))
  have hint2 : ∀ φ ∈ _root_.GlobalTheory.SplitWeil.SB (GL (n ⊕ Fin c) k), ∀ g : GL n k,
      Integrable (fun y : U × (n → k) => φ (m (g, y))) (μU.prod (Measure.pi fun _ : n => ν)) := by
    intro φ hφ g
    obtain ⟨D, hD, hDm⟩ := hcs φ hφ
    refine ((hSB φ hφ).1.comp (hm.comp (Continuous.prodMk_right g))).integrable_of_hasCompactSupport ?_
    exact HasCompactSupport.intro (hD.image continuous_snd)
      (fun y hy => by by_contra h; exact hy ⟨(g, y), hDm _ h, rfl⟩)
  set Λ : (GL (n ⊕ Fin c) k → ℂ) → ℂ := fun φ => ∫ (g : GL n k), ∫ (u : U),
      ∫ (β : n → k), φ (emb g * ↑u * col β) ∂Measure.pi fun _ ↦ ν ∂μU ∂μX with hΛ
  have hΛP : ∀ φ ∈ _root_.GlobalTheory.SplitWeil.SB (GL (n ⊕ Fin c) k), Λ φ = ∫ p, φ (m p) ∂μP := by
    intro φ hφ
    rw [integral_prod _ (hint φ hφ)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    exact (integral_prod _ (hint2 φ hφ g)).symm
  set R := _root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.RFJ k n c ρ
  have hmR : ∀ p, m p ∈ R := by
    intro p
    have h1 : emb p.1 ∈ R :=
      (le_sup_right : _root_.GlobalTheory.RootEx.R k n c (ρ + 1) ≤ R)
        ((le_sup_left : emb.range ≤ _) ⟨p.1, rfl⟩)
    have h2 : (p.2.1 : GL (n ⊕ Fin c) k) ∈ R :=
      (le_sup_right : _root_.GlobalTheory.RootEx.R k n c (ρ + 1) ≤ R)
        ((le_sup_right : U ≤ _) p.2.1.2)
    have h3 : col p.2.2 ∈ R := (le_sup_left : _root_.GlobalTheory.RootEx.R k n c ρ ≤ R)
      ((le_sup_right : _root_.GlobalTheory.RootEx.N k n c ρ ≤ _)
        (_root_.GlobalTheory.RootEx.Radical.colE_mem _ (Nat.lt_succ_self ρ)))
    exact R.mul_mem (R.mul_mem h1 h2) h3
  have hadd : ∀ φ ∈ _root_.GlobalTheory.SplitWeil.SB (GL (n ⊕ Fin c) k),
      ∀ ψ ∈ _root_.GlobalTheory.SplitWeil.SB (GL (n ⊕ Fin c) k), Λ (φ + ψ) = Λ φ + Λ ψ := by
    intro φ hφ ψ hψ
    rw [hΛP _ (add_mem hφ hψ), hΛP _ hφ, hΛP _ hψ, ← integral_add (hint φ hφ) (hint ψ hψ)]
    rfl
  have hsmul : ∀ (a : ℂ) (φ : GL (n ⊕ Fin c) k → ℂ), (Λ fun g ↦ a * φ g) = a * Λ φ := by
    intro a φ
    simp only [hΛ]
    rw [← integral_const_mul]; congr 1; funext g
    rw [← integral_const_mul]; congr 1; funext u
    rw [← integral_const_mul]
  have hloc : ∀ (φ ψ : GL (n ⊕ Fin c) k → ℂ), (∀ r ∈ R, φ r = ψ r) → Λ φ = Λ ψ := by
    intro φ ψ h
    simp only [hΛ]
    congr 1; funext g; congr 1; funext u; congr 1; funext β
    exact h _ (hmR (g, u, β))
  have hpos : ∀ φ ∈ _root_.GlobalTheory.SplitWeil.SB (GL (n ⊕ Fin c) k), (∀ g, φ g = 0 ∨ φ g = 1) →
      (∃ r ∈ R, φ r = 1) → Λ φ ≠ 0 := by
    intro φ hφ h01 ⟨r, hr, hr1⟩
    obtain ⟨r', hr', β, rfl⟩ :=
      ((_root_.GlobalTheory.RootEx.FourierJacobiGroup.mem_RFJ_iff k n c ρ hρ hρc).1 r).1 hr
    obtain ⟨x, u, hu, rfl⟩ := _root_.GlobalTheory.RootEx.Radical.exists_of_mem_R hr'
    have hre : ∀ p, φ (m p) = ((φ (m p)).re : ℂ) := by
      intro p
      rcases h01 (m p) with h | h <;> simp [h]
    rw [hΛP φ hφ, integral_congr_ae (Filter.Eventually.of_forall hre), integral_complex_ofReal]
    obtain ⟨D, hD, hDm⟩ := hcs φ hφ
    have hpos := Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := μP)
      (x := (x, ⟨u, hu⟩, β)) (Complex.continuous_re.comp ((hSB φ hφ).1.comp hm))
      (HasCompactSupport.intro hD (fun p hp => by
        by_contra h
        exact hp (hDm p (fun h' => h (by simp [h'])))))
      (fun p => by rcases h01 (m p) with h | h <;> simp [h])
      (by show (φ (emb x * u * col β)).re ≠ 0; rw [hr1]; simp)
    exact_mod_cast hpos.ne'
  let H : Subgroup (GL (n ⊕ Fin c) k) :=
    { carrier := {r | ∀ φ : GL (n ⊕ Fin c) k → ℂ, (Λ fun g ↦ φ (r * g)) = Λ φ}
      mul_mem' := fun {a b} ha hb φ => by
        have e : (fun g ↦ φ (a * b * g)) = fun g ↦ (fun y ↦ φ (a * y)) (b * g) := by
          funext g; simp only [mul_assoc]
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [e, hb (fun y ↦ φ (a * y)), ha φ]
      one_mem' := fun φ => by simp only [one_mul]
      inv_mem' := fun {a} ha φ => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        have := ha (fun y ↦ φ (a⁻¹ * y))
        simp only [inv_mul_cancel_left] at this
        exact this.symm }
  have hembH : ∀ x : GL n k, emb x ∈ H := by
    intro x φ
    simp only [hΛ]
    have e : ∀ (g : GL n k) (u : U) (β : n → k),
        emb x * (emb g * ↑u * col β) = emb (x * g) * ↑u * col β := by
      intro g u β; simp only [map_mul, mul_assoc]
    simp only [e]
    exact integral_mul_left_eq_self (μ := μX)
      (fun g ↦ ∫ (u : U), ∫ (β : n → k), φ (emb g * ↑u * col β) ∂Measure.pi fun _ ↦ ν ∂μU) x
  have hUH : ∀ v ∈ U, v ∈ H := by
    intro v hv φ
    simp only [hΛ]
    congr 1; funext g
    have hw : (emb g)⁻¹ * v * emb g ∈ U :=
      _root_.GlobalTheory.RootEx.Model.conj_mem hv g
    have e : ∀ (u : U) (β : n → k), v * (emb g * ↑u * col β) =
        emb g * ↑((⟨_, hw⟩ : U) * u) * col β := by
      intro u β; simp only [Subgroup.coe_mul]; group
    simp only [e]
    exact integral_mul_left_eq_self (μ := μU)
      (fun u : U ↦ ∫ (β : n → k), φ (emb g * ↑u * col β) ∂Measure.pi fun _ ↦ ν) (⟨_, hw⟩ : U)
  have hcolH : ∀ γ : n → k, col γ ∈ H := by
    intro γ φ
    simp only [hΛ]
    congr 1; funext g
    set δ : n → k := (↑g⁻¹ : Matrix n n k) *ᵥ γ
    have hconj : emb g⁻¹ * col γ * (emb g⁻¹)⁻¹ = col δ :=
      _root_.GlobalTheory.RootEx.QuotStep.conj_colE (ρ + 1) g⁻¹ γ
    have e : ∀ (u : U) (β : n → k), col γ * (emb g * ↑u * col β) =
        emb g * (col δ * ↑u * (col δ)⁻¹) * col (δ + β) := by
      intro u β
      have hc : col (δ + β) = col δ * col β := (_root_.GlobalTheory.RootEx.FourierJacobiGroup.colE_add (ρ + 1) δ β).symm
      rw [hc, ← hconj]
      simp only [map_inv, inv_inv]
      group
    simp only [e]
    have hβ : ∀ y : GL (n ⊕ Fin c) k,
        ∫ (β : n → k), φ (emb g * y * col (δ + β)) ∂(Measure.pi fun _ ↦ ν) =
        ∫ (β : n → k), φ (emb g * y * col β) ∂(Measure.pi fun _ ↦ ν) := fun y =>
      integral_add_left_eq_self (fun β ↦ φ (emb g * y * col β)) δ
    simp only [hβ]
    exact _root_.GlobalTheory.RootEx.ConjVol.integral_conj_colE k n c ρ hρ hρc ν δ
      (fun y ↦ ∫ (β : n → k), φ (emb g * y * col β) ∂Measure.pi fun _ ↦ ν)
  have hinv : ∀ r ∈ R, ∀ (φ : GL (n ⊕ Fin c) k → ℂ), (Λ fun g ↦ φ (r * g)) = Λ φ := by
    intro r hr
    obtain ⟨r', hr', β, rfl⟩ :=
      ((_root_.GlobalTheory.RootEx.FourierJacobiGroup.mem_RFJ_iff k n c ρ hρ hρc).1 r).1 hr
    obtain ⟨x, u, hu, rfl⟩ := _root_.GlobalTheory.RootEx.Radical.exists_of_mem_R hr'
    exact H.mul_mem (H.mul_mem (hembH x) (hUH u hu)) (hcolH β)
  have hF : (F₁ - F₂) ∈ _root_.GlobalTheory.SplitWeil.SB (GL (n ⊕ Fin c) k) := sub_mem hF₁ hF₂
  have hG : ∀ φ ∈ _root_.GlobalTheory.SplitWeil.SB (GL (n ⊕ Fin c) k), Integrable φ μG :=
    fun φ hφ => (hSB φ hφ).1.integrable_of_hasCompactSupport (hSB φ hφ).2
  have hΛf : ∀ F ∈ _root_.GlobalTheory.SplitWeil.SB (GL (n ⊕ Fin c) k),
      (∀ h, f h = ∫ (g : GL n k), ∫ (u : U), ∫ (β : n → k), F (emb g * ↑u * col β * h)
        ∂(Measure.pi fun _ ↦ ν) ∂μU ∂μX) → ∀ h, (Λ fun g ↦ F (g * h)) = f h := by
    intro F _ hf h
    rw [hf h]
  have key := _root_.GlobalTheory.QuotInt.integral_eq_zero_of_avg μG _ hB.2.2.2.2.1 hB.2.2.2.1
    R Λ hadd hsmul hloc hinv hpos hF (fun h => by
      have e : (fun g => (F₁ - F₂) (g * h)) =
          (fun g => F₁ (g * h)) + (fun g => (-1 : ℂ) * F₂ (g * h)) := by
        funext g; simp [sub_eq_add_neg]
      have hneg : (fun g => (-1 : ℂ) * F₂ (g * h)) ∈
          _root_.GlobalTheory.SplitWeil.SB (GL (n ⊕ Fin c) k) :=
        (_root_.GlobalTheory.SplitWeil.SB (GL (n ⊕ Fin c) k)).smul_mem (-1 : ℂ)
          (_root_.GlobalTheory.QuotInt.sb_right hF₂ h)
      rw [e, hadd _ (_root_.GlobalTheory.QuotInt.sb_right hF₁ h) _ hneg,
        hsmul (-1) (fun g => F₂ (g * h)), hΛf F₁ hF₁ hf₁ h, hΛf F₂ hF₂ hf₂ h]
      ring)
  have hsub : ∫ g, (F₁ - F₂) g ∂μG = ∫ g, F₁ g ∂μG - ∫ g, F₂ g ∂μG :=
    integral_sub (hG _ hF₁) (hG _ hF₂)
  rw [hsub] at key
  exact sub_eq_zero.1 key

end GlobalTheory.QuotIntFJ
