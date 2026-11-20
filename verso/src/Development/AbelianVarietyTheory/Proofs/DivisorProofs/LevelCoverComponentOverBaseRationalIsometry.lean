import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenScal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverReadingEqPowMulMovedFrameReading
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormGenEqOneOfFrOver
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsRationalIsometryOfTraceIsometry
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalIsometryMapsFlagDomainFrames
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ExistsNotIntegralLie
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnfFamily
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

noncomputable section

namespace GlobalTheory.LevModel

section Mark

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {g : ℕ}

/- English proof (translation)
Establish `hM0 : 0 < l.M` using `lt_of_lt_of_le (by norm_num) l.three_le`. Establish `hp0 : pd ≠ 0` using `fun h0 => by`. Use `l₂.three_le` as an intermediate fact. Rewrite `this` using `[hM, h0]`. Use linear arithmetic over natural numbers and integers.

Establish `hmap : l₂.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)` using `Ideal.map_mono hle`. Introduce `a ha`. Establish `j₂` using `F.ex_eta k P hP a (Submodule.smul_mono_left hmap ha)`. Establish `j₁ : toUnit _ ≫ Xo₂.univ.eta a ^ pd = F₂.ex k₂ P₂ ((l.M : ℂ)⁻¹ • P₂ (F₂.t k₂ a))`. Rewrite using `[MonObj.comp_pow, F₂.ex_eta k₂ P₂ hP₂ a ha, ← GlobalTheory.CoverExp.pow_of_add (F₂.ex_add k₂ P₂ hP₂), hM, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, Nat.cast_mul, mul_inv, mul_left_comm, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hp0), _root_.mul_one]`.

Establish `e : F.ex k P ((l.M : ℂ)⁻¹ • P (gam (F₂.t k₂ a))) = F.ex k P ((l.M : ℂ)⁻¹ • P (F.t k a))`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[hh, ← map_smul h, hx, ← j₁, ← j₂, Over.comp_left, Over.comp_left, Category.assoc, heta]`. Establish `w₂ : (toUnit (Over.mk (F₂.u k₂ P₂))).left = F₂.u k₂ P₂`. Simplify using `using Over.w (toUnit (Over.mk (F₂.u k₂ P₂)))`.

Establish `w₁ : (toUnit (Over.mk (F.u k P))).left = F.u k P`. Simplify using `using Over.w (toUnit (Over.mk (F.u k P)))`. Rewrite using `[w₂, w₁, ← Category.assoc, hu]`. Conclude with `(GlobalTheory.UnifPoint.div_eq_iff hP.2.1 (F.ex_add k P hP) (F.ex_ker k P hP) hM0 _ _).1 e`.
-/
theorem mark_of_exp {D : Datum H} {l l₂ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli D l} {Xo₂ : Moduli D l₂}
    {r : Xo₂.X ⟶ Xo.X} (m : SABMap Xo₂.univ.t Xo.univ.t r) (pd : ℕ) (hM : l₂.M = l.M * pd) (hle : l₂.Mb ≤ l.Mb)
    (heta : ∀ a, (Xo₂.univ.eta a ^ pd).left ≫ m.φ = r ≫ (Xo.univ.eta a).left)
    {σ : KA l →+* ℂ} {σ₂ : KA l₂ →+* ℂ} {ty ty₂ : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ ty)
    (F₂ : FamilyUnif Xo₂ σ₂ ty₂) (k : Fin F.n) (k₂ : Fin F₂.n) {P : (F.Di k).La →+ (Fin g → ℂ)}
    {P₂ : (F₂.Di k₂).La →+ (Fin g → ℂ)} (hP : IsPeriod (F.Di k) ty P) (hP₂ : IsPeriod (F₂.Di k₂) ty₂ P₂)
    (hu : F₂.u k₂ P₂ ≫ r = F.u k P)
    (gam : (F₂.Di k₂).La ≃ₗ[𝓞 E] (F.Di k).La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ))
    (hh : ∀ a, P (gam a) = h (P₂ a))
    (hx : ∀ z, (F.ex k P (h z)).left = (F₂.ex k₂ P₂ z).left ≫ m.φ) :
    ∀ a ∈ l₂.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
      ∃ x, gam (F₂.t k₂ a) = F.t k a + l.M • x := by
  have hM0 : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  have hp0 : pd ≠ 0 := fun h0 => by
    have := l₂.three_le
    rw [hM, h0] at this
    omega
  have hmap : l₂.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := Ideal.map_mono hle
  intro a ha
  have j₂ := F.ex_eta k P hP a (Submodule.smul_mono_left hmap ha)
  have j₁ : toUnit _ ≫ Xo₂.univ.eta a ^ pd = F₂.ex k₂ P₂ ((l.M : ℂ)⁻¹ • P₂ (F₂.t k₂ a)) := by
    rw [MonObj.comp_pow, F₂.ex_eta k₂ P₂ hP₂ a ha, ← GlobalTheory.CoverExp.pow_of_add (F₂.ex_add k₂ P₂ hP₂), hM,
      ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, Nat.cast_mul, mul_inv, mul_left_comm,
      mul_inv_cancel₀ (Nat.cast_ne_zero.2 hp0), _root_.mul_one]
  have e : F.ex k P ((l.M : ℂ)⁻¹ • P (gam (F₂.t k₂ a))) = F.ex k P ((l.M : ℂ)⁻¹ • P (F.t k a)) := by
    apply Over.OverMorphism.ext
    rw [hh, ← map_smul h, hx, ← j₁, ← j₂, Over.comp_left, Over.comp_left, Category.assoc, heta]
    have w₂ : (toUnit (Over.mk (F₂.u k₂ P₂))).left = F₂.u k₂ P₂ := by
      simpa using Over.w (toUnit (Over.mk (F₂.u k₂ P₂)))
    have w₁ : (toUnit (Over.mk (F.u k P))).left = F.u k P := by
      simpa using Over.w (toUnit (Over.mk (F.u k P)))
    rw [w₂, w₁, ← Category.assoc, hu]
  exact (GlobalTheory.UnifPoint.div_eq_iff hP.2.1 (F.ex_add k P hP) (F.ex_ker k P hP) hM0 _ _).1 e

end Mark

section Down

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.FrameLift

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ}

/- English proof (translation)
Take `⟨w, hw, hw', -⟩` from `d.m.lin`. Take `⟨p, k, p₁, p₂, hk, hk'⟩` from `exists_pm_iso d.m e`. Establish `hL` using `Xo.univ.t.PP.isLB`. Establish `hL₂` using `d.Xo₂.univ.t.PP.isLB`. Take `⟨s, hs⟩` from `exists_up hL hL₂ hw p₁ hk hk' y₂.s`.

Use `⟨⟨y₀.x, y₀.x_over, y₀.u, y₀.tan, y₀.eig, y₀.basis, s, fun s' => ?_⟩, rfl, rfl, (frOver_iff d _ _).2 ⟨e, hu, w, p, ⟨hw, hw'⟩, p₁, p₂, hs⟩⟩` and prove the remaining obligations. Take `⟨s₂', hs'⟩` from `exists_down hL hL₂ hw p₁ s'`. Use `(existsUnique_congr fun a => ?_).1 (y₂.gen s₂')` and prove the remaining obligations. Conclude with `(scal_iff (fst (Over.mk y₂.x) d.Xo₂.univ.t.G).left (toΓ S a) y₂.s s₂').trans ((rel_scal_iff hL hL₂ p₁ hk p₂ (toΓ S a) hs hs').trans (scal_iff (fst (Over.mk y₀.x) Xo.univ.t.G).left (toΓ S a) s s').symm)`.
-/
theorem exists_frOver_down (d : DeltaDat Xo c n) {S : Type} [CommRing S] [Algebra c.F S] [Algebra d.c₂.F S]
    (y₂ : FrPt d.Xo₂ d.c₂ S) (y₀ : FrPt Xo c S) (e : y₂.x ≫ d.r = y₀.x) (hu : ∀ τ i, y₂.u τ i ≫ d.m.φ = y₀.u τ i) :
    ∃ y : FrPt Xo c S, y.x = y₀.x ∧ y.u = y₀.u ∧ FrOver d y₂ y := by
  obtain ⟨w, hw, hw', -⟩ := d.m.lin
  obtain ⟨p, k, p₁, p₂, hk, hk'⟩ := exists_pm_iso d.m e
  have hL := Xo.univ.t.PP.isLB
  have hL₂ := d.Xo₂.univ.t.PP.isLB
  obtain ⟨s, hs⟩ := exists_up hL hL₂ hw p₁ hk hk' y₂.s
  refine ⟨⟨y₀.x, y₀.x_over, y₀.u, y₀.tan, y₀.eig, y₀.basis, s, fun s' => ?_⟩, rfl, rfl,
    (frOver_iff d _ _).2 ⟨e, hu, w, p, ⟨hw, hw'⟩, p₁, p₂, hs⟩⟩
  obtain ⟨s₂', hs'⟩ := exists_down hL hL₂ hw p₁ s'
  refine (existsUnique_congr fun a => ?_).1 (y₂.gen s₂')
  exact (scal_iff (fst (Over.mk y₂.x) d.Xo₂.univ.t.G).left (toΓ S a) y₂.s s₂').trans
    ((rel_scal_iff hL hL₂ p₁ hk p₂ (toΓ S a) hs hs').trans
      (scal_iff (fst (Over.mk y₀.x) Xo.univ.t.G).left (toΓ S a) s s').symm)

end Down

section Emb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ}

/- English proof (translation)
The claim follows from `(congrArg σ₂ (Subtype.ext rfl)).trans h`.
-/
theorem good_comp (d : DeltaDat Xo c n) (σ₂ : d.c₂.F →+* ℂ) (h : GoodEmb d.c₂ σ₂) :
    GoodEmb c (σ₂.comp (d.eF : c.F →+* d.c₂.F)) :=
  (congrArg σ₂ (Subtype.ext rfl)).trans h

/- English proof (translation)
Use function extensionality and compare the values at `i`. Apply the tactic sequence `cases i <;> simp [genScal]`.
-/
theorem genScal_eq {S : Type} [CommRing S] (t : Sˣ) :
    genScal (Dw := Dw) t = fun i => Option.elim i t (fun _ => 1) := by
  funext i
  cases i <;> simp [genScal]

end Emb

open AlgebraicGeometry CategoryTheory in
set_option maxHeartbeats 1600000 in

/- English proof (translation)
Introduce `D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hd σ₂ hσ₂ k₂`. Establish `hσ : GoodEmb c (σ₂.comp (d.eF : c.F →+* d.c₂.F))` using `good_comp d σ₂ hσ₂`. Use `set σ := σ₂.comp (d.eF : c.F →+* d.c₂.F) with hσe`. Establish `hA : l.A = 1` using `hL.levA`. Establish `hA₂ : d.l₂.A = 1` using `hL₂.levA`.

Establish `hU` using `hL.unf σ hσ`. Establish `hU₂` using `hL₂.unf σ₂ hσ₂`. Take `⟨hr₀, hW⟩` from `hL.modelW σ hσ`. Take `⟨hr₂, hW₂⟩` from `hL₂.modelW σ₂ hσ₂`. Establish `hpq : Dw.p ≠ Dw.q`.

Take `⟨hp, hq, -⟩` from `hL.dat`. Take `⟨h1, h2⟩` from `hL.inR`. Establish `hk` using `D.R.m_add_three_le_k`. Rewrite using `[hp, hq]`. Simplify using `only [Ranks.sigW, Ranks.r]`.

Use linear arithmetic over natural numbers and integers. Establish `hle : KA l ≤ KA d.l₂` using `by rw [KA, KA, hA, hA₂]`. Establish `hinc : (σ₂.comp (IntermediateField.inclusion d.c₂.le).toRingHom).comp (IntermediateField.inclusion hle).toRingHom = σ.comp (IntermediateField.inclusion c.le).toRingHom` using `RingHom.ext fun a => congrArg σ₂ (Subtype.ext rfl)`. Establish `hrel : ∀ τ : D.host.E →+* ℂ, relab c σ τ = relab d.c₂ σ₂ τ` using `fun τ => by`. Use extensionality with `a`.

Conclude with `congrArg σ₂ (Subtype.ext rfl)`. Take `⟨-, -, -, -, -, g, e, F, ik, φ, hEF, hper⟩` from `id hU`. Take `⟨-, -, -, -, -, g₂, e₂, F₂, ik₂, φ₂, hEF₂, hper₂⟩` from `id hU₂`. Take `rfl : g₂ = g` from `by simpa using Fintype.card_congr (e₂.trans e.symm)`. Take `⟨x₀, hx₀⟩` from `GlobalTheory.UnifFamily.dom_nonempty ((U₂ σ₂).X k₂)`.

Take `⟨P₀, hP₀, hp₀, hu₀, -⟩` from `hper₂ k₂ ⟨x₀, hx₀⟩`. Use `letI : Field (CAt σ) := inferInstanceAs (Field ℂ)`. Establish `hy : (F₂.u (ik₂ k₂) P₀ ≫ d.r) ≫ Xo.s = spMap (σ.comp (IntermediateField.inclusion c.le).toRingHom)`. Rewrite using `[CategoryTheory.Category.assoc, GlobalTheory.ClsVal.Cmp.point_over_of_ne hpq hA d hle, ← CategoryTheory.Category.assoc, F₂.over_σ _ P₀ hp₀, GlobalTheory.ClsVal.Cmp.spMap_comp', hinc]`. Take `⟨y, hyx⟩` from `GlobalTheory.NonIntegralFrameExample.exists_framed (c := c) (S := CAt σ) (F₂.u (ik₂ k₂) P₀ ≫ d.r) hy`.

Take `⟨k, x₁, t₁, hb⟩` from `hU.2.2.1 y`. Take `⟨P₁, hP₁, hp₁, hu₁, -⟩` from `hper k x₁`. Establish `hu : F₂.u (ik₂ k₂) P₀ ≫ d.r = F.u (ik k) P₁`. Rewrite using `[← hu₁, ← hb.1]`. Conclude with `hyx.symm`.

Take `⟨gam, hl, hg, hh, hx⟩` from `GlobalTheory.CoverFrameMod.exists_isometry_of_cover F₂ F d.m hp₀ hp₁ hu`. Establish `gM` using `mark_of_exp d.m d.pd hd.2.1 hd.1.2.1 hd.2.2.2.2.2.1.1 F F₂ (ik k) (ik₂ k₂) hp₁ hp₀ hu gam hl hh hx`. Apply the tactic sequence `obtain ⟨a, ε, hε, hξ, hmul, -, hiso⟩ := GlobalTheory.TraceIsometry.exists_gl_of_trace_isometry D.host.E D.R.r ((U₂ σ₂).X k₂) ((U σ).X k) (fun τ => (hL₂.xiAbs σ₂ hσ₂ k₂ τ).trans (hL.xiAbs σ hσ k τ).symm) ((φ₂ k₂).symm.trans (gam.trans (φ k))) (fun u v => by`. Establish `e₁` using `hEF k (gam ((φ₂ k₂).symm u)) (gam ((φ₂ k₂).symm v))`. Establish `e₂` using `hEF₂ k₂ ((φ₂ k₂).symm u) ((φ₂ k₂).symm v)`.

Rewrite `e₁` using `[hg]`. Rewrite `e₂` using `[LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]`. Conclude with `e₁.symm.trans e₂)`. Establish `hξ₀ : ((U σ).X k).ξ0 = ((U₂ σ₂).X k₂).ξ0` using `(hW k).2.trans (hW₂ k₂).2.symm`. Take `rfl : ε = 1` from `mul_right_cancel₀ ((U₂ σ₂).X k₂).ξ0_ne (by rw [← hξ, one_mul, hξ₀])`.

Establish `hG : ((U σ).X k).Gm = ((U₂ σ₂).X k₂).Gm` using `(hW k).1.trans (hW₂ k₂).1.symm`. Establish `hΨ : ∀ τ, τ ∈ ((U σ).X k).Ψ ↔ τ ∈ ((U₂ σ₂).X k₂).Ψ` using `fun τ => ((hU.2.1 k).2 τ).trans ((hU₂.2.1 k₂).2 τ).symm`. Establish `hp0 : ((U σ).X k).p0 = ((U₂ σ₂).X k₂).p0` using `(hU.2.1 k).1.trans (hU₂.2.1 k₂).1.symm`. Establish `hiso' : ∀ v w, herm ((U σ).X k).Gm ((a : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((a : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm ((U₂ σ₂).X k₂).Gm v w` using `fun v w => by`. Rewrite using `[hiso, one_mul]`.

Establish `hgam : ∀ b, (φ k (gam b) : Fin D.R.r → D.host.E) = (a : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec (φ₂ k₂ b : Fin D.R.r → D.host.E)` using `fun b => by`. Rewrite using `[hmul (φ₂ k₂ b)]`. Simplify using the standard rewrite rules. Use `⟨k, a, hG.symm, fun v w => ?_, ?_⟩` and prove the remaining obligations. Establish `h'` using `hiso' v w`.

Rewrite `h'` using `[hG]`. Then use the resulting hypothesis. Introduce `x hx x' hmv`. Apply the tactic sequence `have hx' : x' ∈ ((U σ).X k).dom := GlobalTheory.FrameDom.mem_dom_of_isometry _ _ _ _ a hp0 hΨ hiso' x x' hx hmv`. Use `⟨hx', ?_⟩` and prove the remaining obligations. Take `⟨Q₁, hQ₁, hq₁, hqu₁, hqv₁, hqn₁⟩` from `hper k ⟨x', hx'⟩`.

Take `⟨Q₂, hQ₂, hq₂, hqu₂, hqv₂, hqn₂⟩` from `hper₂ k₂ ⟨x, hx⟩`. Take `⟨c₁, c₂⟩` from `GlobalTheory.CoverFrameRead.point_over d hd hpq hA hle hinc e e₂ F F₂ (ik k) (ik₂ k₂) hq₁ hq₂ gam hg gM (fun b i => by`. Rewrite using `[hQ₁, hQ₂, hgam, Equiv.apply_symm_apply, hrel]`. Conclude with `GlobalTheory.CoverFrameRead.perFr_move _ _ hΨ hp0 hG a hiso' x x' hmv _ _ _)`. Establish `hx₂ : ((U₂ σ₂).un k₂ ⟨x, hx⟩).x ≫ d.r = ((U σ).un k ⟨x', hx'⟩).x`.

Rewrite using `[hqu₁, hqu₂]`. Conclude with `c₁`. Establish `hu₂ : ∀ τ i, ((U₂ σ₂).un k₂ ⟨x, hx⟩).u τ i ≫ d.m.φ = ((U σ).un k ⟨x', hx'⟩).u τ i` using `fun τ i => c₂ ⟨τ, i⟩ _ _ (hqv₁ τ i) (hqv₂ τ i)`. Use `letI : Algebra c.F (CAt σ₂) := σ.toAlgebra`. Take `⟨z, hzx, hzu, ho⟩` from `exists_frOver_down (S := CAt σ₂) d ((U₂ σ₂).un k₂ ⟨x, hx⟩) ((U σ).un k ⟨x', hx'⟩) hx₂ hu₂`.

Take `⟨t, ht⟩` from `GlobalTheory.GeoLevel.exists_frBor_gen (σ := σ) ((U σ).un k ⟨x', hx'⟩) z hzx hzu`. Establish `hn' : (∀ τ i, ‖dmin ((U₂ σ₂).X k₂).Gm x τ i‖ = 1) → ∀ τ i, ‖dmin ((U σ).X k).Gm x' τ i‖ = 1`. Introduce `hn τ i`. Take `⟨τ, h₁⟩` from `τ`. Establish `h₂` using `(hΨ τ).1 h₁`.

Establish `e' : dmin ((U σ).X k).Gm x' ⟨τ, h₁⟩ i = dmin ((U₂ σ₂).X k₂).Gm x ⟨τ, h₂⟩ i`. Unfold `dmin`. Rewrite using `[hmv τ h₂ h₁, GlobalTheory.FrameDom.gram_mul _ _ _ hiso' τ]`. Rewrite using `[e']`. Conclude with `hn _ _`.

Use `⟨t, fun hn => ?_, z, ?_, ho⟩` and prove the remaining obligations. Conclude with `GlobalTheory.CoverFrameMod.norm_gen_eq_one_of_frOver d F₂ F (ik₂ k₂) (ik k) Q₂ Q₁ ((U₂ σ₂).un k₂ ⟨x, hx⟩) ((U σ).un k ⟨x', hx'⟩) z (fun i => Option.elim i t (fun _ => 1)) hq₂ hq₁ hqu₂ hqu₁ (hqn₂ hn) (hqn₁ (hn' hn)) ho ht`. Establish `e' : genScal (Dw` using `Dw) (S := CAt σ₂) t = fun i => Option.elim i t (fun _ => 1) := genScal_eq _`. Conclude with `e'.symm ▸ ht`.
-/
theorem over_comp : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ σ₂, GoodEmb d.c₂ σ₂ → ∀ k₂ : (U₂ σ₂).Comp, ∃ (k : (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).Comp) (δ : GL (Fin D.R.r) D.host.E), ((U₂ σ₂).X k₂).Gm = ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Gm ∧ (∀ v w, herm ((U₂ σ₂).X k₂).Gm ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm ((U₂ σ₂).X k₂).Gm v w) ∧ GlobalTheory.LevModel.Over d σ₂ (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))) (U₂ σ₂) k₂ k δ := by
  intro D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hd σ₂ hσ₂ k₂
  have hσ : GoodEmb c (σ₂.comp (d.eF : c.F →+* d.c₂.F)) := good_comp d σ₂ hσ₂
  set σ := σ₂.comp (d.eF : c.F →+* d.c₂.F) with hσe
  have hA : l.A = 1 := hL.levA
  have hA₂ : d.l₂.A = 1 := hL₂.levA
  have hU := hL.unf σ hσ
  have hU₂ := hL₂.unf σ₂ hσ₂
  obtain ⟨hr₀, hW⟩ := hL.modelW σ hσ
  obtain ⟨hr₂, hW₂⟩ := hL₂.modelW σ₂ hσ₂
  have hpq : Dw.p ≠ Dw.q := by
    obtain ⟨hp, hq, -⟩ := hL.dat
    obtain ⟨h1, h2⟩ := hL.inR
    have hk := D.R.m_add_three_le_k
    rw [hp, hq]
    simp only [Ranks.sigW, Ranks.r]
    omega
  have hle : KA l ≤ KA d.l₂ := by rw [KA, KA, hA, hA₂]
  have hinc : (σ₂.comp (IntermediateField.inclusion d.c₂.le).toRingHom).comp
      (IntermediateField.inclusion hle).toRingHom = σ.comp (IntermediateField.inclusion c.le).toRingHom :=
    RingHom.ext fun a => congrArg σ₂ (Subtype.ext rfl)
  have hrel : ∀ τ : D.host.E →+* ℂ, relab c σ τ = relab d.c₂ σ₂ τ := fun τ => by
    ext a
    exact congrArg σ₂ (Subtype.ext rfl)
  obtain ⟨-, -, -, -, -, g, e, F, ik, φ, hEF, hper⟩ := id hU
  obtain ⟨-, -, -, -, -, g₂, e₂, F₂, ik₂, φ₂, hEF₂, hper₂⟩ := id hU₂
  obtain rfl : g₂ = g := by simpa using Fintype.card_congr (e₂.trans e.symm)
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.UnifFamily.dom_nonempty ((U₂ σ₂).X k₂)
  obtain ⟨P₀, hP₀, hp₀, hu₀, -⟩ := hper₂ k₂ ⟨x₀, hx₀⟩
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  have hy : (F₂.u (ik₂ k₂) P₀ ≫ d.r) ≫ Xo.s = spMap (σ.comp (IntermediateField.inclusion c.le).toRingHom) := by
    rw [CategoryTheory.Category.assoc, GlobalTheory.ClsVal.Cmp.point_over_of_ne hpq hA d hle,
      ← CategoryTheory.Category.assoc, F₂.over_σ _ P₀ hp₀, GlobalTheory.ClsVal.Cmp.spMap_comp', hinc]
  obtain ⟨y, hyx⟩ := GlobalTheory.NonIntegralFrameExample.exists_framed (c := c) (S := CAt σ) (F₂.u (ik₂ k₂) P₀ ≫ d.r) hy
  obtain ⟨k, x₁, t₁, hb⟩ := hU.2.2.1 y
  obtain ⟨P₁, hP₁, hp₁, hu₁, -⟩ := hper k x₁
  have hu : F₂.u (ik₂ k₂) P₀ ≫ d.r = F.u (ik k) P₁ := by
    rw [← hu₁, ← hb.1]
    exact hyx.symm
  obtain ⟨gam, hl, hg, hh, hx⟩ := GlobalTheory.CoverFrameMod.exists_isometry_of_cover F₂ F d.m hp₀ hp₁ hu
  have gM := mark_of_exp d.m d.pd hd.2.1 hd.1.2.1 hd.2.2.2.2.2.1.1 F F₂ (ik k) (ik₂ k₂) hp₁ hp₀ hu gam hl hh hx
  obtain ⟨a, ε, hε, hξ, hmul, -, hiso⟩ := GlobalTheory.TraceIsometry.exists_gl_of_trace_isometry D.host.E D.R.r
    ((U₂ σ₂).X k₂) ((U σ).X k) (fun τ => (hL₂.xiAbs σ₂ hσ₂ k₂ τ).trans (hL.xiAbs σ hσ k τ).symm)
    ((φ₂ k₂).symm.trans (gam.trans (φ k))) (fun u v => by
      have e₁ := hEF k (gam ((φ₂ k₂).symm u)) (gam ((φ₂ k₂).symm v))
      have e₂ := hEF₂ k₂ ((φ₂ k₂).symm u) ((φ₂ k₂).symm v)
      rw [hg] at e₁
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at e₂
      exact e₁.symm.trans e₂)
  have hξ₀ : ((U σ).X k).ξ0 = ((U₂ σ₂).X k₂).ξ0 := (hW k).2.trans (hW₂ k₂).2.symm
  obtain rfl : ε = 1 := mul_right_cancel₀ ((U₂ σ₂).X k₂).ξ0_ne (by rw [← hξ, one_mul, hξ₀])
  have hG : ((U σ).X k).Gm = ((U₂ σ₂).X k₂).Gm := (hW k).1.trans (hW₂ k₂).1.symm
  have hΨ : ∀ τ, τ ∈ ((U σ).X k).Ψ ↔ τ ∈ ((U₂ σ₂).X k₂).Ψ := fun τ =>
    ((hU.2.1 k).2 τ).trans ((hU₂.2.1 k₂).2 τ).symm
  have hp0 : ((U σ).X k).p0 = ((U₂ σ₂).X k₂).p0 := (hU.2.1 k).1.trans (hU₂.2.1 k₂).1.symm
  have hiso' : ∀ v w, herm ((U σ).X k).Gm ((a : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v)
      ((a : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm ((U₂ σ₂).X k₂).Gm v w := fun v w => by
    rw [hiso, one_mul]
  have hgam : ∀ b, (φ k (gam b) : Fin D.R.r → D.host.E) =
      (a : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec (φ₂ k₂ b : Fin D.R.r → D.host.E) := fun b => by
    rw [hmul (φ₂ k₂ b)]
    simp
  refine ⟨k, a, hG.symm, fun v w => ?_, ?_⟩
  · have h' := hiso' v w
    rwa [hG] at h'
  intro x hx x' hmv
  have hx' : x' ∈ ((U σ).X k).dom :=
    GlobalTheory.FrameDom.mem_dom_of_isometry _ _ _ _ a hp0 hΨ hiso' x x' hx hmv
  refine ⟨hx', ?_⟩
  obtain ⟨Q₁, hQ₁, hq₁, hqu₁, hqv₁, hqn₁⟩ := hper k ⟨x', hx'⟩
  obtain ⟨Q₂, hQ₂, hq₂, hqu₂, hqv₂, hqn₂⟩ := hper₂ k₂ ⟨x, hx⟩
  obtain ⟨c₁, c₂⟩ := GlobalTheory.CoverFrameRead.point_over d hd hpq hA hle hinc e e₂ F F₂ (ik k) (ik₂ k₂) hq₁ hq₂ gam hg gM
    (fun b i => by
      rw [hQ₁, hQ₂, hgam, Equiv.apply_symm_apply, hrel]
      exact GlobalTheory.CoverFrameRead.perFr_move _ _ hΨ hp0 hG a hiso' x x' hmv _ _ _)
  have hx₂ : ((U₂ σ₂).un k₂ ⟨x, hx⟩).x ≫ d.r = ((U σ).un k ⟨x', hx'⟩).x := by
    rw [hqu₁, hqu₂]
    exact c₁
  have hu₂ : ∀ τ i, ((U₂ σ₂).un k₂ ⟨x, hx⟩).u τ i ≫ d.m.φ = ((U σ).un k ⟨x', hx'⟩).u τ i :=
    fun τ i => c₂ ⟨τ, i⟩ _ _ (hqv₁ τ i) (hqv₂ τ i)
  letI : Algebra c.F (CAt σ₂) := σ.toAlgebra
  obtain ⟨z, hzx, hzu, ho⟩ := exists_frOver_down (S := CAt σ₂) d ((U₂ σ₂).un k₂ ⟨x, hx⟩) ((U σ).un k ⟨x', hx'⟩) hx₂ hu₂
  obtain ⟨t, ht⟩ := GlobalTheory.GeoLevel.exists_frBor_gen (σ := σ) ((U σ).un k ⟨x', hx'⟩) z hzx hzu
  have hn' : (∀ τ i, ‖dmin ((U₂ σ₂).X k₂).Gm x τ i‖ = 1) → ∀ τ i, ‖dmin ((U σ).X k).Gm x' τ i‖ = 1 := by
    intro hn τ i
    obtain ⟨τ, h₁⟩ := τ
    have h₂ := (hΨ τ).1 h₁
    have e' : dmin ((U σ).X k).Gm x' ⟨τ, h₁⟩ i = dmin ((U₂ σ₂).X k₂).Gm x ⟨τ, h₂⟩ i := by
      unfold dmin
      rw [hmv τ h₂ h₁, GlobalTheory.FrameDom.gram_mul _ _ _ hiso' τ]
    rw [e']
    exact hn _ _
  refine ⟨t, fun hn => ?_, z, ?_, ho⟩
  · exact GlobalTheory.CoverFrameMod.norm_gen_eq_one_of_frOver d F₂ F (ik₂ k₂) (ik k) Q₂ Q₁ ((U₂ σ₂).un k₂ ⟨x, hx⟩)
      ((U σ).un k ⟨x', hx'⟩) z (fun i => Option.elim i t (fun _ => 1)) hq₂ hq₁ hqu₂ hqu₁ (hqn₂ hn) (hqn₁ (hn' hn)) ho ht
  · have e' : genScal (Dw := Dw) (S := CAt σ₂) t = fun i => Option.elim i t (fun _ => 1) := genScal_eq _
    exact e'.symm ▸ ht

end GlobalTheory.LevModel
