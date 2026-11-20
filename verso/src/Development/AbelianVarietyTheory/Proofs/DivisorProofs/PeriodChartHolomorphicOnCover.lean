import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOnPeriodChartCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicChartSmooth
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Set Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ArInt GlobalTheory.TorsionForm
open GlobalTheory.LieVB (omega)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt stdLat cov)
open GlobalTheory.CxForm (IsRegVar)
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped ComplexOrder
open CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

namespace GlobalTheory.PeriodChartOnto

/- English proof (translation)
Introduce `k _ S p A _ _ g h σ D c τ ex HP v hv`. Establish `hs` using `LieVB.sec_hom (MonObj.one (X := A))`. Take `⟨U, W, hx, hle, ch⟩` from `Conormal.exists_isChart hs (mem_ptsIn.1 (h.isVB.mem_pick (p := p) (σ := σ) (c.e.symm v)))`. Establish `hU : c.e.symm v ∈ ptsIn p σ U` using `mem_ptsIn.2 hx`. Set `c₀ : VB.Chart (omega A) g` to `⟨U, _, (h.isVB.pick (c.e.symm v)).isFrame.res hle⟩`.

Use `choose f hf using fun a => ch.d_surjective hs (c₀.e a)`. Establish `hG : (h.met σ).G c₀ (c.e.symm v) = HermFrame.chg (Matrix.of fun a b => cot ex W (f b) v a) ((2 : ℂ) • imPart τ v)`. Use extensionality with `a b`. Rewrite using `[← (h.met σ).form_frame c₀ hU, ← hf, ← hf, HermFrame.chg_apply]`. Conclude with `(HP.2.2 v hv).2.2.2.2 U W ch.le _ _ hU`.

Establish `hP` using `(h.met σ).posDef c₀ _ hU`. Rewrite `hP` using `[hG]`. Establish `hu` using `hP.det_pos.ne'.isUnit`. Rewrite `hu` using `[HermFrame.chg, det_mul, det_mul]`. Establish `e : (ex (v, 0)).1 = (c.e.symm v).1 ≫ LieVB.unitSec A` using `((HP.2.2 v hv).2.2.2.1 0).2 ⟨0, zero_mem _, by funext i; simp [GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.per, vecMul, dotProduct]⟩`.

Use `⟨W, f, ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `⊤ ≤ (ex (v, 0)).1 ⁻¹ᵁ W`. Rewrite using `[e]`. Conclude with `fun x hx' => ch.le (hU hx')`. Establish `ht : (Matrix.of fun a b => cot ex W (f a) v b) = (Matrix.of fun a b => cot ex W (f b) v a)ᵀ` using `by ext; rfl`.

Rewrite using `[ht]`. Conclude with `isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hu)`.
-/
theorem exists_frame_cot : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) (A : Over S) [GrpObj A] [QuasiSeparated A.hom] (g : ℕ) (h : VMetric p (omega A) g) (σ : k →+* ℂ) (D : ℕ) (c : AlgChart p σ D) (τ : V D → Matrix (Fin g) (Fin g) ℂ) (ex : Pt (V D) g → CxPts (A.hom ≫ p) σ), IsPeriodChart h c τ ex → ∀ v ∈ c.e.target, ∃ (W : A.left.Opens) (f : Fin g → Γ(A.left, W)), ex (v, 0) ∈ ptsIn (A.hom ≫ p) σ W ∧ IsUnit (Matrix.of fun a b => cot ex W (f a) v b).det := by
  intro k _ S p A _ _ g h σ D c τ ex HP v hv
  have hs := LieVB.sec_hom (MonObj.one (X := A))
  obtain ⟨U, W, hx, hle, ch⟩ := Conormal.exists_isChart hs (mem_ptsIn.1 (h.isVB.mem_pick (p := p) (σ := σ) (c.e.symm v)))
  have hU : c.e.symm v ∈ ptsIn p σ U := mem_ptsIn.2 hx
  let c₀ : VB.Chart (omega A) g := ⟨U, _, (h.isVB.pick (c.e.symm v)).isFrame.res hle⟩
  choose f hf using fun a => ch.d_surjective hs (c₀.e a)
  have hG : (h.met σ).G c₀ (c.e.symm v) =
      HermFrame.chg (Matrix.of fun a b => cot ex W (f b) v a) ((2 : ℂ) • imPart τ v) := by
    ext a b
    rw [← (h.met σ).form_frame c₀ hU, ← hf, ← hf, HermFrame.chg_apply]
    exact (HP.2.2 v hv).2.2.2.2 U W ch.le _ _ hU
  have hP := (h.met σ).posDef c₀ _ hU
  rw [hG] at hP
  have hu := hP.det_pos.ne'.isUnit
  rw [HermFrame.chg, det_mul, det_mul] at hu
  have e : (ex (v, 0)).1 = (c.e.symm v).1 ≫ LieVB.unitSec A :=
    ((HP.2.2 v hv).2.2.2.1 0).2 ⟨0, zero_mem _, by funext i; simp [GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.per, vecMul, dotProduct]⟩
  refine ⟨W, f, ?_, ?_⟩
  · change ⊤ ≤ (ex (v, 0)).1 ⁻¹ᵁ W
    rw [e]
    exact fun x hx' => ch.le (hU hx')
  · have ht : (Matrix.of fun a b => cot ex W (f a) v b) = (Matrix.of fun a b => cot ex W (f b) v a)ᵀ := by
      ext; rfl
    rw [ht]
    exact isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hu)

/- English proof (translation)
Introduce `k _ S p A _ g h σ D D' c τ ex HP c' v z₀ hv hs W f hW`. Establish `hB : IsOpen (cov c.e.target g)` using `c.e.open_target.prod isOpen_univ`. Establish `hcont : ContinuousOn ex (cov c.e.target g)` using `GlobalTheory.TrueCx.TorHolo.continuousOn_of_isHolTo HP.2.1`. Set `π : CxPts (A.hom ≫ p) σ → CxPts p σ` to `Points.PtsOver.map A.hom rfl _`. Establish `hover : ∀ w ∈ c.e.target, ∀ z, π (ex (w, z)) = c.e.symm w` using `fun w hw z => Subtype.ext ((HP.2.2 w hw).1 z)`.

Set `β : V D' → V D` to `fun ξ => c.e (π (c'.e.symm ξ))`. Set `a : V D' → (Sp ℂ ⟶ A.left)` to `fun ξ => (ex (β ξ, -z₀)).1`. Set `b : V D' → (Sp ℂ ⟶ A.left)` to `fun ξ => (c'.e.symm ξ).1`. Set `m : V D' → (Sp ℂ ⟶ pullback A.hom A.hom)` to `fun ξ => if hξ : a ξ ≫ A.hom = b ξ ≫ A.hom then pullback.lift (a ξ) (b ξ) hξ else pullback.lift (b ξ) (b ξ) rfl`. Set `μl : pullback A.hom A.hom ⟶ A.left` to `(MonObj.mul : A ⊗ A ⟶ A).left`.

Establish `hkey : ∀ w ∈ c.e.target, ∀ z, ex (w, z) ∈ c'.e.source → m (c'.e (ex (w, z))) ≫ μl = (ex (w, -z₀ + z)).1`. Introduce `w hw z hz`. Establish `e1 : c'.e.symm (c'.e (ex (w, z))) = ex (w, z)` using `c'.e.left_inv hz`. Establish `e2 : β (c'.e (ex (w, z))) = w`. Express the relevant statement in the definitionally equal form `c.e (π (c'.e.symm (c'.e (ex (w, z))))) = w`.

Rewrite using `[e1, hover w hw, c.e.right_inv hw]`. Establish `ha : a (c'.e (ex (w, z))) = (ex (w, -z₀)).1`. Express the relevant statement in the definitionally equal form `(ex (β (c'.e (ex (w, z))), -z₀)).1 = _`. Rewrite using `[e2]`. Establish `hb : b (c'.e (ex (w, z))) = (ex (w, z)).1`.

Express the relevant statement in the definitionally equal form `(c'.e.symm (c'.e (ex (w, z)))).1 = _`. Rewrite using `[e1]`. Establish `ho` using `(HP.2.2 w hw).1`. Establish `hab : a (c'.e (ex (w, z))) ≫ A.hom = b (c'.e (ex (w, z))) ≫ A.hom`. Rewrite using `[ha, hb, ho, ho]`.

Establish `hm : m (c'.e (ex (w, z))) = pullback.lift (a (c'.e (ex (w, z)))) (b (c'.e (ex (w, z)))) hab` using `dif_pos hab`. Set `x : Over.mk (c.e.symm w).1 ⟶ A` to `Over.homMk (ex (w, -z₀)).1 (ho _)`. Set `y : Over.mk (c.e.symm w).1 ⟶ A` to `Over.homMk (ex (w, z)).1 (ho _)`. Establish `hxy` using `(HP.2.2 w hw).2.1 (-z₀) z x y rfl rfl`. Rewrite using `[← hxy, CategoryTheory.Hom.mul_def, Over.comp_left, Over.lift_left, hm]`.

Use `congr 1`. Conclude with `pullback.hom_ext (by rw [pullback.lift_fst, pullback.lift_fst, ha]; rfl) (by rw [pullback.lift_snd, pullback.lift_snd, hb]; rfl)`. Establish `congrH : ∀ {X : Scheme.{0}} {B : Set (V D')} {c₁ c₂ : V D' → (Sp ℂ ⟶ X)}, IsHolTo B c₁ → (∀ ξ ∈ B, c₂ ξ = c₁ ξ) → IsHolTo B c₂`. Introduce `X B c₁ c₂ hc he U u`. Establish `e : {ξ ∈ B | ⊤ ≤ c₂ ξ ⁻¹ᵁ U} = {ξ ∈ B | ⊤ ≤ c₁ ξ ⁻¹ᵁ U}`.

Use extensionality with `ξ`. Conclude with `and_congr_right fun hξ => by rw [he ξ hξ]`. Rewrite using `[e]`. Conclude with `⟨(hc U u).1, (hc U u).2.congr fun ξ hξ => by rw [he ξ hξ.1]⟩`. Establish `hyπ : IsHolTo c'.e.target fun ξ => (π (c'.e.symm ξ)).1` using `GlobalTheory.HolFibre.isHolTo_comp (GlobalTheory.TrueCx.TorHolo.isHolTo_symm c') A.hom`.

Establish `hπc : ContinuousOn (fun ξ => π (c'.e.symm ξ)) c'.e.target` using `GlobalTheory.TrueCx.TorHolo.continuousOn_of_isHolTo hyπ`. Set `T` to `c'.e.target ∩ (fun ξ => π (c'.e.symm ξ)) ⁻¹' c.e.source`. Establish `hT : IsOpen T` using `hπc.isOpen_inter_preimage c'.e.open_target c.e.open_source`. Establish `hβ : ∀ ξ ∈ T, DifferentiableAt ℂ β ξ` using `fun ξ hξ => GlobalTheory.TrueCx.TorHolo.differentiableAt_chart c'.e.open_target hyπ c hξ.1 hξ.2`. Establish `hβT : ∀ ξ ∈ T, β ξ ∈ c.e.target` using `fun ξ hξ => c.e.map_source hξ.2`.

Establish `haH : IsHolTo T a`. Introduce `U u`. Take `⟨ho, hd⟩` from `HP.2.1 U u`. Set `kk : V D' → Pt (V D) g` to `fun ξ => (β ξ, -z₀)`. Establish `hkc : ContinuousOn kk T` using `fun ξ hξ => ((hβ ξ hξ).continuousAt.prodMk continuousAt_const).continuousWithinAt`.

Establish `e : {ξ ∈ T | ⊤ ≤ a ξ ⁻¹ᵁ U} = T ∩ kk ⁻¹' {P' ∈ cov c.e.target g | ⊤ ≤ (ex P').1 ⁻¹ᵁ U}`. Use extensionality with `ξ`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨h1, ⟨hβT ξ h1, trivial⟩, h2⟩`.

Introduce and unpack `⟨h1, -, h2⟩`. Conclude with `⟨h1, h2⟩`. Rewrite using `[e]`. Use `⟨hkc.isOpen_inter_preimage hT ho, fun ξ hξ => ?_⟩` and prove the remaining obligations. Establish `hk : DifferentiableAt ℂ kk ξ` using `(hβ ξ hξ.1).prodMk (differentiableAt_const _)`.

Conclude with `((hd.differentiableAt (ho.mem_nhds hξ.2)).comp ξ hk).differentiableWithinAt`. Establish `hbH : IsHolTo T b`. Introduce `U u`. Take `⟨ho, hd⟩` from `GlobalTheory.TrueCx.TorHolo.isHolTo_symm c' U u`. Establish `e : {ξ ∈ T | ⊤ ≤ b ξ ⁻¹ᵁ U} = T ∩ {ξ ∈ c'.e.target | ⊤ ≤ (c'.e.symm ξ).1 ⁻¹ᵁ U}`.

Use extensionality with `ξ`. Conclude with `⟨fun h => ⟨h.1, h.1.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩`. Rewrite using `[e]`. Conclude with `⟨hT.inter ho, hd.mono inter_subset_right⟩`. Establish `habT : ∀ ξ ∈ T, a ξ ≫ A.hom = b ξ ≫ A.hom`.

Introduce `ξ hξ`. Establish `h1 : a ξ ≫ A.hom = (c.e.symm (β ξ)).1` using `(HP.2.2 _ (hβT ξ hξ)).1 _`. Establish `h2 : c.e.symm (β ξ) = π (c'.e.symm ξ)` using `c.e.left_inv hξ.2`. Rewrite using `[h1, h2]`. Both sides reduce to the same expression.

Establish `hmH : IsHolTo T m`. Use `GlobalTheory.HolFibre.isHolTo_of_isPullback (IsPullback.of_hasPullback A.hom A.hom) ?_ ?_` and prove the remaining obligations. Conclude with `congrH haH fun ξ hξ => by`. Express the relevant statement in the definitionally equal form `m ξ ≫ pullback.fst _ _ = a ξ`. Rewrite using `[show m ξ = pullback.lift (a ξ) (b ξ) (habT ξ hξ) from dif_pos (habT ξ hξ), pullback.lift_fst]`.

Conclude with `congrH hbH fun ξ hξ => by`. Express the relevant statement in the definitionally equal form `m ξ ≫ pullback.snd _ _ = b ξ`. Rewrite using `[show m ξ = pullback.lift (a ξ) (b ξ) (habT ξ hξ) from dif_pos (habT ξ hξ), pullback.lift_snd]`. Establish `hmu : IsHolTo T fun ξ => m ξ ≫ μl` using `GlobalTheory.HolFibre.isHolTo_comp hmH μl`. Establish `hξ0 : c'.e (ex (v, z₀)) ∈ T`.

Use `⟨c'.e.map_source hs, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `π (c'.e.symm (c'.e (ex (v, z₀)))) ∈ c.e.source`. Rewrite using `[c'.e.left_inv hs, hover v hv]`. Conclude with `c.e.map_target hv`. Establish `hm0 : m (c'.e (ex (v, z₀))) ≫ μl = (ex (v, 0)).1`.

Rewrite using `[hkey v hv z₀ hs, neg_add_cancel]`. Use `⟨fun ξ => valAt' (m ξ ≫ μl) W f, ?_, ?_⟩` and prove the remaining obligations. Take `⟨ho, hd⟩` from `hmu W f`. Establish `hmem : c'.e (ex (v, z₀)) ∈ {ξ ∈ T | ⊤ ≤ (m ξ ≫ μl) ⁻¹ᵁ W}`. Use `⟨hξ0, ?_⟩` and prove the remaining obligations.

Rewrite using `[hm0]`. Conclude with `hW`. Conclude with `hd.differentiableAt (ho.mem_nhds hmem)`. Establish `hQ : ((v, z₀) : Pt (V D) g) ∈ cov c.e.target g` using `⟨hv, trivial⟩`. Establish `ht : Tendsto (fun q : Pt (V D) g => q + ((0 : V D), z₀)) (𝓝 (v, 0)) (𝓝 (v, z₀))`.

Apply the tactic sequence `have e : ((v, 0) : Pt (V D) g) + ((0 : V D), z₀) = (v, z₀) := by ext <;> simp`. Conclude with `(continuous_id.add continuous_const : Continuous fun q : Pt (V D) g => q + ((0 : V D), z₀)).tendsto' _ _ e`. Establish `h1 : ∀ᶠ q in 𝓝 ((v, 0) : Pt (V D) g), ex (q + ((0 : V D), z₀)) ∈ c'.e.source` using `ht.eventually ((hcont.continuousAt (hB.mem_nhds hQ)).preimage_mem_nhds (c'.e.open_source.mem_nhds hs))`. Establish `h2 : ∀ᶠ q in 𝓝 ((v, 0) : Pt (V D) g), q.1 ∈ c.e.target` using `continuous_fst.continuousAt.preimage_mem_nhds (c.e.open_target.mem_nhds hv)`. Use `filter_upwards [h1, h2] with q hq1 hq2`.

Apply the tactic sequence `have e2 : q + ((0 : V D), z₀) = (q.1, q.2 + z₀) := by ext <;> simp`. Rewrite `hq1`, the goal using `[e2]`. Express the relevant statement in the definitionally equal form `valAt' (ex q).1 W f = valAt' (m (c'.e (ex (q.1, q.2 + z₀))) ≫ μl) W f`. Rewrite using `[hkey q.1 hq2 _ hq1]`. Apply the tactic sequence `have e3 : ((q.1, -z₀ + (q.2 + z₀)) : Pt (V D) g) = q := by ext <;> simp`.

Rewrite using `[e3]`.
-/
theorem exists_transl_fn : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) (A : Over S) [GrpObj A] (g : ℕ) (h : VMetric p (omega A) g) (σ : k →+* ℂ) (D D' : ℕ) (c : AlgChart p σ D) (τ : V D → Matrix (Fin g) (Fin g) ℂ) (ex : Pt (V D) g → CxPts (A.hom ≫ p) σ), IsPeriodChart h c τ ex → ∀ (c' : AlgChart (A.hom ≫ p) σ D') (v : V D) (z₀ : Fin g → ℂ), v ∈ c.e.target → ex (v, z₀) ∈ c'.e.source → ∀ (W : A.left.Opens) (f : Γ(A.left, W)), ex (v, 0) ∈ ptsIn (A.hom ≫ p) σ W → ∃ M : V D' → ℂ, DifferentiableAt ℂ M (c'.e (ex (v, z₀))) ∧ ∀ᶠ q in 𝓝 ((v, 0) : Pt (V D) g), ev (A.hom ≫ p) σ W f (ex q) = M (c'.e (ex (q + ((0 : V D), z₀)))) := by
  intro k _ S p A _ g h σ D D' c τ ex HP c' v z₀ hv hs W f hW
  classical
  have hB : IsOpen (cov c.e.target g) := c.e.open_target.prod isOpen_univ
  have hcont : ContinuousOn ex (cov c.e.target g) := GlobalTheory.TrueCx.TorHolo.continuousOn_of_isHolTo HP.2.1
  let π : CxPts (A.hom ≫ p) σ → CxPts p σ := Points.PtsOver.map A.hom rfl _
  have hover : ∀ w ∈ c.e.target, ∀ z, π (ex (w, z)) = c.e.symm w := fun w hw z =>
    Subtype.ext ((HP.2.2 w hw).1 z)
  let β : V D' → V D := fun ξ => c.e (π (c'.e.symm ξ))
  let a : V D' → (Sp ℂ ⟶ A.left) := fun ξ => (ex (β ξ, -z₀)).1
  let b : V D' → (Sp ℂ ⟶ A.left) := fun ξ => (c'.e.symm ξ).1
  let m : V D' → (Sp ℂ ⟶ pullback A.hom A.hom) := fun ξ =>
    if hξ : a ξ ≫ A.hom = b ξ ≫ A.hom then pullback.lift (a ξ) (b ξ) hξ
    else pullback.lift (b ξ) (b ξ) rfl
  let μl : pullback A.hom A.hom ⟶ A.left := (MonObj.mul : A ⊗ A ⟶ A).left
  have hkey : ∀ w ∈ c.e.target, ∀ z, ex (w, z) ∈ c'.e.source →
      m (c'.e (ex (w, z))) ≫ μl = (ex (w, -z₀ + z)).1 := by
    intro w hw z hz
    have e1 : c'.e.symm (c'.e (ex (w, z))) = ex (w, z) := c'.e.left_inv hz
    have e2 : β (c'.e (ex (w, z))) = w := by
      change c.e (π (c'.e.symm (c'.e (ex (w, z))))) = w
      rw [e1, hover w hw, c.e.right_inv hw]
    have ha : a (c'.e (ex (w, z))) = (ex (w, -z₀)).1 := by
      change (ex (β (c'.e (ex (w, z))), -z₀)).1 = _
      rw [e2]
    have hb : b (c'.e (ex (w, z))) = (ex (w, z)).1 := by
      change (c'.e.symm (c'.e (ex (w, z)))).1 = _
      rw [e1]
    have ho := (HP.2.2 w hw).1
    have hab : a (c'.e (ex (w, z))) ≫ A.hom = b (c'.e (ex (w, z))) ≫ A.hom := by
      rw [ha, hb, ho, ho]
    have hm : m (c'.e (ex (w, z))) = pullback.lift (a (c'.e (ex (w, z)))) (b (c'.e (ex (w, z)))) hab :=
      dif_pos hab
    let x : Over.mk (c.e.symm w).1 ⟶ A := Over.homMk (ex (w, -z₀)).1 (ho _)
    let y : Over.mk (c.e.symm w).1 ⟶ A := Over.homMk (ex (w, z)).1 (ho _)
    have hxy := (HP.2.2 w hw).2.1 (-z₀) z x y rfl rfl
    rw [← hxy, CategoryTheory.Hom.mul_def, Over.comp_left, Over.lift_left, hm]
    congr 1
    exact pullback.hom_ext (by rw [pullback.lift_fst, pullback.lift_fst, ha]; rfl)
      (by rw [pullback.lift_snd, pullback.lift_snd, hb]; rfl)
  have congrH : ∀ {X : Scheme.{0}} {B : Set (V D')} {c₁ c₂ : V D' → (Sp ℂ ⟶ X)}, IsHolTo B c₁ →
      (∀ ξ ∈ B, c₂ ξ = c₁ ξ) → IsHolTo B c₂ := by
    intro X B c₁ c₂ hc he U u
    have e : {ξ ∈ B | ⊤ ≤ c₂ ξ ⁻¹ᵁ U} = {ξ ∈ B | ⊤ ≤ c₁ ξ ⁻¹ᵁ U} := by
      ext ξ
      exact and_congr_right fun hξ => by rw [he ξ hξ]
    rw [e]
    exact ⟨(hc U u).1, (hc U u).2.congr fun ξ hξ => by rw [he ξ hξ.1]⟩
  have hyπ : IsHolTo c'.e.target fun ξ => (π (c'.e.symm ξ)).1 :=
    GlobalTheory.HolFibre.isHolTo_comp (GlobalTheory.TrueCx.TorHolo.isHolTo_symm c') A.hom
  have hπc : ContinuousOn (fun ξ => π (c'.e.symm ξ)) c'.e.target :=
    GlobalTheory.TrueCx.TorHolo.continuousOn_of_isHolTo hyπ
  let T := c'.e.target ∩ (fun ξ => π (c'.e.symm ξ)) ⁻¹' c.e.source
  have hT : IsOpen T := hπc.isOpen_inter_preimage c'.e.open_target c.e.open_source
  have hβ : ∀ ξ ∈ T, DifferentiableAt ℂ β ξ := fun ξ hξ =>
    GlobalTheory.TrueCx.TorHolo.differentiableAt_chart c'.e.open_target hyπ c hξ.1 hξ.2
  have hβT : ∀ ξ ∈ T, β ξ ∈ c.e.target := fun ξ hξ => c.e.map_source hξ.2
  have haH : IsHolTo T a := by
    intro U u
    obtain ⟨ho, hd⟩ := HP.2.1 U u
    let kk : V D' → Pt (V D) g := fun ξ => (β ξ, -z₀)
    have hkc : ContinuousOn kk T := fun ξ hξ =>
      ((hβ ξ hξ).continuousAt.prodMk continuousAt_const).continuousWithinAt
    have e : {ξ ∈ T | ⊤ ≤ a ξ ⁻¹ᵁ U} =
        T ∩ kk ⁻¹' {P' ∈ cov c.e.target g | ⊤ ≤ (ex P').1 ⁻¹ᵁ U} := by
      ext ξ
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, ⟨hβT ξ h1, trivial⟩, h2⟩
      · rintro ⟨h1, -, h2⟩
        exact ⟨h1, h2⟩
    rw [e]
    refine ⟨hkc.isOpen_inter_preimage hT ho, fun ξ hξ => ?_⟩
    have hk : DifferentiableAt ℂ kk ξ := (hβ ξ hξ.1).prodMk (differentiableAt_const _)
    exact ((hd.differentiableAt (ho.mem_nhds hξ.2)).comp ξ hk).differentiableWithinAt
  have hbH : IsHolTo T b := by
    intro U u
    obtain ⟨ho, hd⟩ := GlobalTheory.TrueCx.TorHolo.isHolTo_symm c' U u
    have e : {ξ ∈ T | ⊤ ≤ b ξ ⁻¹ᵁ U} = T ∩ {ξ ∈ c'.e.target | ⊤ ≤ (c'.e.symm ξ).1 ⁻¹ᵁ U} := by
      ext ξ
      exact ⟨fun h => ⟨h.1, h.1.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
    rw [e]
    exact ⟨hT.inter ho, hd.mono inter_subset_right⟩
  have habT : ∀ ξ ∈ T, a ξ ≫ A.hom = b ξ ≫ A.hom := by
    intro ξ hξ
    have h1 : a ξ ≫ A.hom = (c.e.symm (β ξ)).1 := (HP.2.2 _ (hβT ξ hξ)).1 _
    have h2 : c.e.symm (β ξ) = π (c'.e.symm ξ) := c.e.left_inv hξ.2
    rw [h1, h2]
    rfl
  have hmH : IsHolTo T m := by
    refine GlobalTheory.HolFibre.isHolTo_of_isPullback (IsPullback.of_hasPullback A.hom A.hom) ?_ ?_
    · exact congrH haH fun ξ hξ => by
        change m ξ ≫ pullback.fst _ _ = a ξ
        rw [show m ξ = pullback.lift (a ξ) (b ξ) (habT ξ hξ) from dif_pos (habT ξ hξ), pullback.lift_fst]
    · exact congrH hbH fun ξ hξ => by
        change m ξ ≫ pullback.snd _ _ = b ξ
        rw [show m ξ = pullback.lift (a ξ) (b ξ) (habT ξ hξ) from dif_pos (habT ξ hξ), pullback.lift_snd]
  have hmu : IsHolTo T fun ξ => m ξ ≫ μl := GlobalTheory.HolFibre.isHolTo_comp hmH μl
  have hξ0 : c'.e (ex (v, z₀)) ∈ T := by
    refine ⟨c'.e.map_source hs, ?_⟩
    change π (c'.e.symm (c'.e (ex (v, z₀)))) ∈ c.e.source
    rw [c'.e.left_inv hs, hover v hv]
    exact c.e.map_target hv
  have hm0 : m (c'.e (ex (v, z₀))) ≫ μl = (ex (v, 0)).1 := by
    rw [hkey v hv z₀ hs, neg_add_cancel]
  refine ⟨fun ξ => valAt' (m ξ ≫ μl) W f, ?_, ?_⟩
  · obtain ⟨ho, hd⟩ := hmu W f
    have hmem : c'.e (ex (v, z₀)) ∈ {ξ ∈ T | ⊤ ≤ (m ξ ≫ μl) ⁻¹ᵁ W} := by
      refine ⟨hξ0, ?_⟩
      rw [hm0]
      exact hW
    exact hd.differentiableAt (ho.mem_nhds hmem)
  · have hQ : ((v, z₀) : Pt (V D) g) ∈ cov c.e.target g := ⟨hv, trivial⟩
    have ht : Tendsto (fun q : Pt (V D) g => q + ((0 : V D), z₀)) (𝓝 (v, 0)) (𝓝 (v, z₀)) := by
      have e : ((v, 0) : Pt (V D) g) + ((0 : V D), z₀) = (v, z₀) := by ext <;> simp
      exact (continuous_id.add continuous_const : Continuous fun q : Pt (V D) g => q + ((0 : V D), z₀)).tendsto' _ _ e
    have h1 : ∀ᶠ q in 𝓝 ((v, 0) : Pt (V D) g), ex (q + ((0 : V D), z₀)) ∈ c'.e.source :=
      ht.eventually ((hcont.continuousAt (hB.mem_nhds hQ)).preimage_mem_nhds (c'.e.open_source.mem_nhds hs))
    have h2 : ∀ᶠ q in 𝓝 ((v, 0) : Pt (V D) g), q.1 ∈ c.e.target :=
      continuous_fst.continuousAt.preimage_mem_nhds (c.e.open_target.mem_nhds hv)
    filter_upwards [h1, h2] with q hq1 hq2
    have e2 : q + ((0 : V D), z₀) = (q.1, q.2 + z₀) := by ext <;> simp
    rw [e2] at hq1 ⊢
    change valAt' (ex q).1 W f = valAt' (m (c'.e (ex (q.1, q.2 + z₀))) ≫ μl) W f
    rw [hkey q.1 hq2 _ hq1]
    have e3 : ((q.1, -z₀ + (q.2 + z₀)) : Pt (V D) g) = q := by ext <;> simp
    rw [e3]

/- English proof (translation)
Introduce `k _ S p A _ g h σ D D' c τ ex HP c' v z₀ hv hs`. Establish `hB : IsOpen (cov c.e.target g)` using `c.e.open_target.prod isOpen_univ`. Establish `hcont : ContinuousOn ex (cov c.e.target g)` using `GlobalTheory.TrueCx.TorHolo.continuousOn_of_isHolTo HP.2.1`. Set `π : CxPts (A.hom ≫ p) σ → CxPts p σ` to `Points.PtsOver.map A.hom rfl _`. Establish `hover : ∀ w ∈ c.e.target, ∀ z, π (ex (w, z)) = c.e.symm w` using `fun w hw z => Subtype.ext ((HP.2.2 w hw).1 z)`.

Use `⟨fun ξ => c.e (π (c'.e.symm ξ)), ?_, ?_⟩` and prove the remaining obligations. Establish `hy : IsHolTo c'.e.target fun ξ => (π (c'.e.symm ξ)).1` using `GlobalTheory.HolFibre.isHolTo_comp (GlobalTheory.TrueCx.TorHolo.isHolTo_symm c') A.hom`. Establish `h0 : c'.e.symm (c'.e (ex (v, z₀))) = ex (v, z₀)` using `c'.e.left_inv hs`. Establish `hsrc : π (c'.e.symm (c'.e (ex (v, z₀)))) ∈ c.e.source`. Rewrite using `[h0, hover v hv]`.

Conclude with `c.e.map_target hv`. Conclude with `GlobalTheory.TrueCx.TorHolo.differentiableAt_chart c'.e.open_target hy c (c'.e.map_source hs) hsrc`. Establish `hQ : ((v, z₀) : Pt (V D) g) ∈ cov c.e.target g` using `⟨hv, trivial⟩`. Establish `ht : Tendsto (fun q : Pt (V D) g => q + ((0 : V D), z₀)) (𝓝 (v, 0)) (𝓝 (v, z₀))`. Apply the tactic sequence `have e : ((v, 0) : Pt (V D) g) + ((0 : V D), z₀) = (v, z₀) := by ext <;> simp`.

Conclude with `(continuous_id.add continuous_const : Continuous fun q : Pt (V D) g => q + ((0 : V D), z₀)).tendsto' _ _ e`. Establish `h1 : ∀ᶠ q in 𝓝 ((v, 0) : Pt (V D) g), ex (q + ((0 : V D), z₀)) ∈ c'.e.source` using `ht.eventually ((hcont.continuousAt (hB.mem_nhds hQ)).preimage_mem_nhds (c'.e.open_source.mem_nhds hs))`. Establish `h2 : ∀ᶠ q in 𝓝 ((v, 0) : Pt (V D) g), q.1 ∈ c.e.target` using `continuous_fst.continuousAt.preimage_mem_nhds (c.e.open_target.mem_nhds hv)`. Use `filter_upwards [h1, h2] with q hq1 hq2`. Establish `e1 : c'.e.symm (c'.e (ex (q + ((0 : V D), z₀)))) = ex (q + ((0 : V D), z₀))` using `c'.e.left_inv hq1`.

Apply the tactic sequence `have e2 : q + ((0 : V D), z₀) = (q.1, q.2 + z₀) := by ext <;> simp`. Use `show q.1 = c.e (π (c'.e.symm (c'.e (ex (q + ((0 : V D), z₀))))))`. Rewrite using `[e1, e2, hover q.1 hq2, c.e.right_inv hq2]`.
-/
theorem exists_base_fn : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) (A : Over S) [GrpObj A] (g : ℕ) (h : VMetric p (omega A) g) (σ : k →+* ℂ) (D D' : ℕ) (c : AlgChart p σ D) (τ : V D → Matrix (Fin g) (Fin g) ℂ) (ex : Pt (V D) g → CxPts (A.hom ≫ p) σ), IsPeriodChart h c τ ex → ∀ (c' : AlgChart (A.hom ≫ p) σ D') (v : V D) (z₀ : Fin g → ℂ), v ∈ c.e.target → ex (v, z₀) ∈ c'.e.source → ∃ M : V D' → V D, DifferentiableAt ℂ M (c'.e (ex (v, z₀))) ∧ ∀ᶠ q in 𝓝 ((v, 0) : Pt (V D) g), q.1 = M (c'.e (ex (q + ((0 : V D), z₀)))) := by
  intro k _ S p A _ g h σ D D' c τ ex HP c' v z₀ hv hs
  have hB : IsOpen (cov c.e.target g) := c.e.open_target.prod isOpen_univ
  have hcont : ContinuousOn ex (cov c.e.target g) := GlobalTheory.TrueCx.TorHolo.continuousOn_of_isHolTo HP.2.1
  let π : CxPts (A.hom ≫ p) σ → CxPts p σ := Points.PtsOver.map A.hom rfl _
  have hover : ∀ w ∈ c.e.target, ∀ z, π (ex (w, z)) = c.e.symm w := fun w hw z =>
    Subtype.ext ((HP.2.2 w hw).1 z)
  refine ⟨fun ξ => c.e (π (c'.e.symm ξ)), ?_, ?_⟩
  · have hy : IsHolTo c'.e.target fun ξ => (π (c'.e.symm ξ)).1 :=
      GlobalTheory.HolFibre.isHolTo_comp (GlobalTheory.TrueCx.TorHolo.isHolTo_symm c') A.hom
    have h0 : c'.e.symm (c'.e (ex (v, z₀))) = ex (v, z₀) := c'.e.left_inv hs
    have hsrc : π (c'.e.symm (c'.e (ex (v, z₀)))) ∈ c.e.source := by
      rw [h0, hover v hv]; exact c.e.map_target hv
    exact GlobalTheory.TrueCx.TorHolo.differentiableAt_chart c'.e.open_target hy c (c'.e.map_source hs) hsrc
  · have hQ : ((v, z₀) : Pt (V D) g) ∈ cov c.e.target g := ⟨hv, trivial⟩
    have ht : Tendsto (fun q : Pt (V D) g => q + ((0 : V D), z₀)) (𝓝 (v, 0)) (𝓝 (v, z₀)) := by
      have e : ((v, 0) : Pt (V D) g) + ((0 : V D), z₀) = (v, z₀) := by ext <;> simp
      exact (continuous_id.add continuous_const : Continuous fun q : Pt (V D) g => q + ((0 : V D), z₀)).tendsto' _ _ e
    have h1 : ∀ᶠ q in 𝓝 ((v, 0) : Pt (V D) g), ex (q + ((0 : V D), z₀)) ∈ c'.e.source :=
      ht.eventually ((hcont.continuousAt (hB.mem_nhds hQ)).preimage_mem_nhds (c'.e.open_source.mem_nhds hs))
    have h2 : ∀ᶠ q in 𝓝 ((v, 0) : Pt (V D) g), q.1 ∈ c.e.target :=
      continuous_fst.continuousAt.preimage_mem_nhds (c.e.open_target.mem_nhds hv)
    filter_upwards [h1, h2] with q hq1 hq2
    have e1 : c'.e.symm (c'.e (ex (q + ((0 : V D), z₀)))) = ex (q + ((0 : V D), z₀)) := c'.e.left_inv hq1
    have e2 : q + ((0 : V D), z₀) = (q.1, q.2 + z₀) := by ext <;> simp
    show q.1 = c.e (π (c'.e.symm (c'.e (ex (q + ((0 : V D), z₀))))))
    rw [e1, e2, hover q.1 hq2, c.e.right_inv hq2]

/- English proof (translation)
Use `haveI := GlobalTheory.ChartSmooth.smooth_chart k S p σ D c`. Use `haveI := GlobalTheory.ChartSmooth.smooth_chart k A.left (A.hom ≫ p) σ D' c'`. Use `haveI : SmoothOfRelativeDimension g (A.hom ∣_ c.U) := (smoothOfRelativeDimension_isStableUnderBaseChange (n := g)).of_isPullback (isPullback_morphismRestrict A.hom c.U).flip hg`. Use `haveI : SmoothOfRelativeDimension (g + D) ((A.hom ⁻¹ᵁ c.U).ι ≫ A.hom ≫ p) := by`. Establish `e : (A.hom ⁻¹ᵁ c.U).ι ≫ A.hom ≫ p = (A.hom ∣_ c.U) ≫ (c.U.ι ≫ p)`.

Rewrite using `[← Category.assoc, ← morphismRestrict_ι, Category.assoc]`. Rewrite using `[e]`. Use `infer_instance`. Set `W : A.left.Opens` to `A.hom ⁻¹ᵁ c.U ⊓ c'.U`. Establish `h₁ : SmoothOfRelativeDimension (0 + (g + D)) (W.ι ≫ A.hom ≫ p)`.

Rewrite using `[← A.left.homOfLE_ι (inf_le_left : W ≤ A.hom ⁻¹ᵁ c.U), Category.assoc]`. Use `infer_instance`. Establish `h₂ : SmoothOfRelativeDimension (0 + D') (W.ι ≫ A.hom ≫ p)`. Rewrite using `[← A.left.homOfLE_ι (inf_le_right : W ≤ c'.U), Category.assoc]`. Use `infer_instance`.

Simplify using `using ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ h₂ h₁ ⟨x, hx, hx'⟩`.
-/
theorem chart_dim (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) (A : Over S) (g : ℕ)
    (hg : SmoothOfRelativeDimension g A.hom) (σ : k →+* ℂ) (D D' : ℕ) (c : AlgChart p σ D)
    (c' : AlgChart (A.hom ≫ p) σ D') (x : A.left) (hx : x ∈ A.hom ⁻¹ᵁ c.U) (hx' : x ∈ c'.U) :
    D' = g + D := by
  haveI := GlobalTheory.ChartSmooth.smooth_chart k S p σ D c
  haveI := GlobalTheory.ChartSmooth.smooth_chart k A.left (A.hom ≫ p) σ D' c'
  haveI : SmoothOfRelativeDimension g (A.hom ∣_ c.U) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := g)).of_isPullback
      (isPullback_morphismRestrict A.hom c.U).flip hg
  haveI : SmoothOfRelativeDimension (g + D) ((A.hom ⁻¹ᵁ c.U).ι ≫ A.hom ≫ p) := by
    have e : (A.hom ⁻¹ᵁ c.U).ι ≫ A.hom ≫ p = (A.hom ∣_ c.U) ≫ (c.U.ι ≫ p) := by
      rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
    rw [e]
    infer_instance
  let W : A.left.Opens := A.hom ⁻¹ᵁ c.U ⊓ c'.U
  have h₁ : SmoothOfRelativeDimension (0 + (g + D)) (W.ι ≫ A.hom ≫ p) := by
    rw [← A.left.homOfLE_ι (inf_le_left : W ≤ A.hom ⁻¹ᵁ c.U), Category.assoc]
    infer_instance
  have h₂ : SmoothOfRelativeDimension (0 + D') (W.ι ≫ A.hom ≫ p) := by
    rw [← A.left.homOfLE_ι (inf_le_right : W ≤ c'.U), Category.assoc]
    infer_instance
  simpa using ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ h₂ h₁ ⟨x, hx, hx'⟩

/- English proof (translation)
Take `⟨v, z₀⟩` from `Q`. Establish `hv : v ∈ c.e.target` using `hQ.1`. Establish `hcovO : IsOpen (cov c.e.target g)` using `c.e.open_target.prod isOpen_univ`. Take `⟨W, f, hW, hdet⟩` from `exists_frame_cot k S p A g h σ D c τ ex HP v hv`. Use `choose M hM hMe using fun a => exists_transl_fn k S p A g h σ D D' c τ ex HP c' v z₀ hv hc' W (f a) hW`.

Take `⟨M₀, hM₀, hM₀e⟩` from `exists_base_fn k S p A g h σ D D' c τ ex HP c' v z₀ hv hc'`. Set `Ψ : Pt (V D) g → V D'` to `fun x => c'.e (ex x)`. Establish `hΨd : HasFDerivAt Ψ (fderiv ℂ Ψ (v, z₀)) (v, z₀)` using `(GlobalTheory.TrueCx.TorHolo.differentiableAt_chart hcovO HP.2.1 c' hQ hc').hasFDerivAt`. Set `F : Pt (V D) g → (Fin g → ℂ)` to `fun x a => ev (A.hom ≫ p) σ W (f a) (ex x)`. Set `Φ : Pt (V D) g → Pt (V D) g` to `fun x => (x.1, F x)`.

Set `Mt : V D' → Pt (V D) g` to `fun ξ => (M₀ ξ, fun a => M a ξ)`. Establish `hMt : DifferentiableAt ℂ Mt (Ψ (v, z₀))` using `hM₀.prodMk (differentiableAt_pi.2 hM)`. Apply the tactic sequence `have hsh : ((v, 0) : Pt (V D) g) + ((0 : V D), z₀) = (v, z₀) := by ext <;> simp`. Establish `hΨd' : HasFDerivAt Ψ (fderiv ℂ Ψ (v, z₀)) (((v, 0) : Pt (V D) g) + ((0 : V D), z₀))`. Rewrite using `[hsh]`.

Conclude with `hΨd`. Establish `hΨ' : HasFDerivAt (fun x : Pt (V D) g => Ψ (x + ((0 : V D), z₀))) (fderiv ℂ Ψ (v, z₀)) (v, 0)`. Use `hΨd'.comp ((v, 0) : Pt (V D) g) ((hasFDerivAt_id ((v, 0) : Pt (V D) g)).add_const ((0 : V D), z₀))` as an intermediate fact. Rewrite `this` using `[ContinuousLinearMap.comp_id]`. Conclude with `this`.

Establish `hev : Φ =ᶠ[𝓝 ((v, 0) : Pt (V D) g)] Mt ∘ fun x => Ψ (x + ((0 : V D), z₀))` using `by filter_upwards [hM₀e, Filter.eventually_all.2 hMe] with x h0 h1`. Conclude with `Prod.ext h0 (funext h1)`. Establish `hMt' : HasFDerivAt Mt (fderiv ℂ Mt (Ψ (v, z₀))) (Ψ (((v, 0) : Pt (V D) g) + ((0 : V D), z₀)))`. Rewrite using `[hsh]`. Conclude with `hMt.hasFDerivAt`.

Establish `hΦ : HasFDerivAt Φ ((fderiv ℂ Mt (Ψ (v, z₀))).comp (fderiv ℂ Ψ (v, z₀))) (v, 0)` using `(hMt'.comp ((v, 0) : Pt (V D) g) hΨ').congr_of_eventuallyEq hev`. Establish `hF : DifferentiableAt ℂ F (v, 0)`. Use `differentiableAt_pi.2 fun a => ?_` and prove the remaining obligations. Take `⟨ho, hd⟩` from `HP.2.1 W (f a)`. Establish `hm : ((v, 0) : Pt (V D) g) ∈ {b ∈ cov c.e.target g | ⊤ ≤ (ex b).1 ⁻¹ᵁ W}` using `⟨⟨hv, trivial⟩, hW⟩`.

Conclude with `hd.differentiableAt (ho.mem_nhds hm)`. Establish `hΦ2 : HasFDerivAt Φ ((ContinuousLinearMap.fst ℂ (V D) (Fin g → ℂ)).prod (fderiv ℂ F (v, 0))) (v, 0)` using `hasFDerivAt_fst.prodMk hF.hasFDerivAt`. Establish `huq` using `hΦ.unique hΦ2`. Set `G : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)` to `(fderiv ℂ F (v, 0)).comp (ContinuousLinearMap.inr ℂ (V D) (Fin g → ℂ))`. Establish `hinc : HasFDerivAt (fun z : Fin g → ℂ => F (v, z)) G 0` using `hF.hasFDerivAt.comp (0 : Fin g → ℂ) (hasFDerivAt_prodMk_right v 0)`.

Establish `hcot : ∀ a b, cot ex W (f a) v b = G (Pi.single b 1) a`. Introduce `a b`. Use `(hasFDerivAt_apply a (F (v, 0))).comp (0 : Fin g → ℂ) hinc` as an intermediate fact. Conclude with `congrArg (· (Pi.single b 1)) this.fderiv`. Establish `hinj : Function.Injective (fderiv ℂ Ψ (v, z₀))`.

Use `(injective_iff_map_eq_zero _).2 fun x hx => ?_` and prove the remaining obligations. Establish `e1` using `congrArg (· x) huq`. Simplify using `only [ContinuousLinearMap.comp_apply, hx, map_zero, ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst'] at e1`. Establish `hx1 : x.1 = 0` using `(congrArg Prod.fst e1).symm`. Establish `hx2 : fderiv ℂ F (v, 0) x = 0` using `(congrArg Prod.snd e1).symm`.

Establish `hxe : x = ((0 : V D), x.2)` using `Prod.ext hx1 rfl`. Establish `hG : G x.2 = 0`. Rewrite `hx2` using `[hxe]`. Conclude with `hx2`. Establish `hx2s : x.2 = ∑ b, x.2 b • (Pi.single b (1 : ℂ) : Fin g → ℂ)`.

Use extensionality with `j`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Establish `hmv : (Matrix.of fun a b => cot ex W (f a) v b) *ᵥ x.2 = 0`. Use function extensionality and compare the values at `a`. Use `congrArg (· a) hG` as an intermediate fact.

Rewrite `this` using `[hx2s]`. Simplify using `only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.of_apply, hcot, Pi.zero_apply]`. Rewrite using `[← this]`. Conclude with `Finset.sum_congr rfl fun b _ => mul_comm _ _`.

Establish `hx2' : x.2 = 0` using `Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 hdet) (hmv.trans (Matrix.mulVec_zero _).symm)`. Conclude with `Prod.ext hx1 hx2'`. Conclude with `hinj`.
-/
theorem fderiv_injective (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) (A : Over S) [GrpObj A]
    [QuasiSeparated A.hom] (g : ℕ)
    (h : VMetric p (omega A) g) (σ : k →+* ℂ) (D D' : ℕ) (c : AlgChart p σ D)
    (τ : V D → Matrix (Fin g) (Fin g) ℂ) (ex : Pt (V D) g → CxPts (A.hom ≫ p) σ) (HP : IsPeriodChart h c τ ex)
    (c' : AlgChart (A.hom ≫ p) σ D') (Q : Pt (V D) g) (hQ : Q ∈ cov c.e.target g) (hc' : ex Q ∈ c'.e.source) :
    Function.Injective (fderiv ℂ (fun x => c'.e (ex x)) Q) := by
  obtain ⟨v, z₀⟩ := Q
  have hv : v ∈ c.e.target := hQ.1
  have hcovO : IsOpen (cov c.e.target g) := c.e.open_target.prod isOpen_univ
  obtain ⟨W, f, hW, hdet⟩ := exists_frame_cot k S p A g h σ D c τ ex HP v hv
  choose M hM hMe using fun a => exists_transl_fn k S p A g h σ D D' c τ ex HP c' v z₀ hv hc' W (f a) hW
  obtain ⟨M₀, hM₀, hM₀e⟩ := exists_base_fn k S p A g h σ D D' c τ ex HP c' v z₀ hv hc'
  let Ψ : Pt (V D) g → V D' := fun x => c'.e (ex x)
  have hΨd : HasFDerivAt Ψ (fderiv ℂ Ψ (v, z₀)) (v, z₀) := (GlobalTheory.TrueCx.TorHolo.differentiableAt_chart hcovO HP.2.1 c' hQ hc').hasFDerivAt
  let F : Pt (V D) g → (Fin g → ℂ) := fun x a => ev (A.hom ≫ p) σ W (f a) (ex x)
  let Φ : Pt (V D) g → Pt (V D) g := fun x => (x.1, F x)
  let Mt : V D' → Pt (V D) g := fun ξ => (M₀ ξ, fun a => M a ξ)
  have hMt : DifferentiableAt ℂ Mt (Ψ (v, z₀)) := hM₀.prodMk (differentiableAt_pi.2 hM)
  have hsh : ((v, 0) : Pt (V D) g) + ((0 : V D), z₀) = (v, z₀) := by ext <;> simp
  have hΨd' : HasFDerivAt Ψ (fderiv ℂ Ψ (v, z₀)) (((v, 0) : Pt (V D) g) + ((0 : V D), z₀)) := by
    rw [hsh]; exact hΨd
  have hΨ' : HasFDerivAt (fun x : Pt (V D) g => Ψ (x + ((0 : V D), z₀))) (fderiv ℂ Ψ (v, z₀)) (v, 0) := by
    have := hΨd'.comp ((v, 0) : Pt (V D) g) ((hasFDerivAt_id ((v, 0) : Pt (V D) g)).add_const ((0 : V D), z₀))
    rw [ContinuousLinearMap.comp_id] at this
    exact this
  have hev : Φ =ᶠ[𝓝 ((v, 0) : Pt (V D) g)] Mt ∘ fun x => Ψ (x + ((0 : V D), z₀)) := by
    filter_upwards [hM₀e, Filter.eventually_all.2 hMe] with x h0 h1
    exact Prod.ext h0 (funext h1)
  have hMt' : HasFDerivAt Mt (fderiv ℂ Mt (Ψ (v, z₀))) (Ψ (((v, 0) : Pt (V D) g) + ((0 : V D), z₀))) := by
    rw [hsh]; exact hMt.hasFDerivAt
  have hΦ : HasFDerivAt Φ ((fderiv ℂ Mt (Ψ (v, z₀))).comp (fderiv ℂ Ψ (v, z₀))) (v, 0) :=
    (hMt'.comp ((v, 0) : Pt (V D) g) hΨ').congr_of_eventuallyEq hev
  have hF : DifferentiableAt ℂ F (v, 0) := by
    refine differentiableAt_pi.2 fun a => ?_
    obtain ⟨ho, hd⟩ := HP.2.1 W (f a)
    have hm : ((v, 0) : Pt (V D) g) ∈ {b ∈ cov c.e.target g | ⊤ ≤ (ex b).1 ⁻¹ᵁ W} := ⟨⟨hv, trivial⟩, hW⟩
    exact hd.differentiableAt (ho.mem_nhds hm)
  have hΦ2 : HasFDerivAt Φ ((ContinuousLinearMap.fst ℂ (V D) (Fin g → ℂ)).prod (fderiv ℂ F (v, 0))) (v, 0) :=
    hasFDerivAt_fst.prodMk hF.hasFDerivAt
  have huq := hΦ.unique hΦ2
  let G : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ) := (fderiv ℂ F (v, 0)).comp (ContinuousLinearMap.inr ℂ (V D) (Fin g → ℂ))
  have hinc : HasFDerivAt (fun z : Fin g → ℂ => F (v, z)) G 0 :=
    hF.hasFDerivAt.comp (0 : Fin g → ℂ) (hasFDerivAt_prodMk_right v 0)
  have hcot : ∀ a b, cot ex W (f a) v b = G (Pi.single b 1) a := by
    intro a b
    have := (hasFDerivAt_apply a (F (v, 0))).comp (0 : Fin g → ℂ) hinc
    exact congrArg (· (Pi.single b 1)) this.fderiv
  have hinj : Function.Injective (fderiv ℂ Ψ (v, z₀)) := by
    refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    have e1 := congrArg (· x) huq
    simp only [ContinuousLinearMap.comp_apply, hx, map_zero, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.coe_fst'] at e1
    have hx1 : x.1 = 0 := (congrArg Prod.fst e1).symm
    have hx2 : fderiv ℂ F (v, 0) x = 0 := (congrArg Prod.snd e1).symm
    have hxe : x = ((0 : V D), x.2) := Prod.ext hx1 rfl
    have hG : G x.2 = 0 := by
      rw [hxe] at hx2
      exact hx2
    have hx2s : x.2 = ∑ b, x.2 b • (Pi.single b (1 : ℂ) : Fin g → ℂ) := by
      ext j; simp [Finset.sum_apply, Pi.single_apply]
    have hmv : (Matrix.of fun a b => cot ex W (f a) v b) *ᵥ x.2 = 0 := by
      funext a
      have := congrArg (· a) hG
      rw [hx2s] at this
      simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, hcot, Pi.zero_apply]
      rw [← this]
      exact Finset.sum_congr rfl fun b _ => mul_comm _ _
    have hx2' : x.2 = 0 := Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 hdet)
      (hmv.trans (Matrix.mulVec_zero _).symm)
    exact Prod.ext hx1 hx2'
  exact hinj

/- English proof (translation)
Establish `hinj` using `fderiv_injective k S p A g h σ D D' c τ ex HP c' Q hQ hc'`. Establish `hU : ⊤ ≤ ((ex Q).1 ≫ A.hom) ⁻¹ᵁ c.U`. Establish `e` using `(HP.2.2 Q.1 hQ.1).1 Q.2`. Rewrite `e` using `[show (Q.1, Q.2) = Q from rfl]`. Rewrite using `[e]`.

Conclude with `c.source_subset (c.e.map_target hQ.1)`. Establish `hD : D' = g + D` using `chart_dim k S p A g hg σ D D' c c' ((ex Q).1 (IsLocalRing.closedPoint ℂ)) (hU trivial) (mem_ptsIn.1 (c'.source_subset hc'))`. Establish `hdim : Module.finrank ℂ (Pt (V D) g) = Module.finrank ℂ (V D')`. Simplify using `[Module.finrank_prod, add_comm, hD]`. Conclude with `⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim (f := (fderiv ℂ (fun x => c'.e (ex x)) Q).toLinearMap)).1 hinj⟩`.
-/
theorem fderiv_bijective (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) (A : Over S) [GrpObj A]
    [QuasiSeparated A.hom] (g : ℕ)
    (hg : SmoothOfRelativeDimension g A.hom)
    (h : VMetric p (omega A) g) (σ : k →+* ℂ) (D D' : ℕ) (c : AlgChart p σ D)
    (τ : V D → Matrix (Fin g) (Fin g) ℂ) (ex : Pt (V D) g → CxPts (A.hom ≫ p) σ) (HP : IsPeriodChart h c τ ex)
    (c' : AlgChart (A.hom ≫ p) σ D') (Q : Pt (V D) g) (hQ : Q ∈ cov c.e.target g) (hc' : ex Q ∈ c'.e.source) :
    Function.Bijective (fderiv ℂ (fun x => c'.e (ex x)) Q) := by
  have hinj := fderiv_injective k S p A g h σ D D' c τ ex HP c' Q hQ hc'
  have hU : ⊤ ≤ ((ex Q).1 ≫ A.hom) ⁻¹ᵁ c.U := by
    have e := (HP.2.2 Q.1 hQ.1).1 Q.2
    rw [show (Q.1, Q.2) = Q from rfl] at e
    rw [e]
    exact c.source_subset (c.e.map_target hQ.1)
  have hD : D' = g + D := chart_dim k S p A g hg σ D D' c c' ((ex Q).1 (IsLocalRing.closedPoint ℂ))
    (hU trivial) (mem_ptsIn.1 (c'.source_subset hc'))
  have hdim : Module.finrank ℂ (Pt (V D) g) = Module.finrank ℂ (V D') := by
    simp [Module.finrank_prod, add_comm, hD]
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
    (f := (fderiv ℂ (fun x => c'.e (ex x)) Q).toLinearMap)).1 hinj⟩

/- English proof (translation)
Introduce `k _ S p D _ A _ D' h' g hA hg w σ c τ ex HP P hP x hx`. Use `haveI : IsProper A.hom := hA.proper`. Establish `hs : ex P ∈ (show AlgChart (A.hom ≫ p) σ D' from x.1.1).e.source`. Rewrite using `[← hx]`. Conclude with `x.2`.

Conclude with `(fderiv_bijective k S p A g hg w σ D D' c τ ex HP x.1.1 P hP hs).2`.
-/
theorem fderiv_surjective : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) (D : ℕ) (h : IsRegVar p D) (A : Over S) [GrpObj A] (D' : ℕ) (h' : IsRegVar (A.hom ≫ p) D') (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (w : VMetric p (omega A) g) (σ : k →+* ℂ) (c : AlgChart p σ D) (τ : V D → Matrix (Fin g) (Fin g) ℂ) (ex : Pt (V D) g → CxPts (A.hom ≫ p) σ), IsPeriodChart w c τ ex → ∀ P ∈ cov c.e.target g, ∀ x : (h'.atlas σ).Pt, x.pt = ex P → Function.Surjective (fderiv ℂ (x.ch ∘ ex) P) := by
  intro k _ S p D _ A _ D' h' g hA hg w σ c τ ex HP P hP x hx
  haveI : IsProper A.hom := hA.proper
  have hs : ex P ∈ (show AlgChart (A.hom ≫ p) σ D' from x.1.1).e.source := by
    rw [← hx]
    exact x.2
  exact (fderiv_bijective k S p A g hg w σ D D' c τ ex HP x.1.1 P hP hs).2

end GlobalTheory.PeriodChartOnto
