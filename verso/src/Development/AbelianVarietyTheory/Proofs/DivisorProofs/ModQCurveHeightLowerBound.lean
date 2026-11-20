import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfCurveDegreesNonneg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfSurjectivePullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsumSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegDataOfCurveData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingHomOfCurve
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCurveOfDedekind
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjectiveCoverGoodReductionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationPartOfPulledActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoverSemiabelianPolarization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubDegsFreeModuleNonpos
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatOfSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiabelianActionAbelianGenericStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExtensionOfIso

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.TrueGeo
open scoped ENNReal Classical
open Limits

namespace GlobalTheory.CurveRootGeometry

open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.ShFam in

/- English proof (translation)
Introduce `hX h₁ h₂ D O hO A T H h B hB c q _ hq Z i _ _ _ hZ`. Establish `hq'` using `hq`. Rewrite `hq'` using `[O.setB_eq, Pad.setB, Finset.mem_union, not_or]`. Establish `hp : q.Prime` using `Fact.out`. Establish `hM : O.κ.l.M' ≠ 0` using `(Nat.lcm_pos (lt_of_lt_of_le (by norm_num) O.κ.l.three_le) O.κ.l.A_pos).ne'`.

Establish `hd0 : (discr D.host.E).natAbs ≠ 0` using `Int.natAbs_ne_zero.2 (discr_ne_zero _)`. Establish `hnd : ¬ q ∣ 2 * (discr D.host.E).natAbs * O.κ.l.M'` using `fun e => hq'.2 (Nat.mem_primeFactors.2 ⟨hp, e, mul_ne_zero (mul_ne_zero two_ne_zero hd0) hM⟩)`. Establish `hd : ¬ q ∣ (discr D.host.E).natAbs` using `fun e => hnd ((e.mul_left 2).mul_right _)`. Establish `h2 : q ≠ 2` using `fun e => hnd (e.dvd.trans ((dvd_mul_right 2 _).mul_right _))`. Set `P` to `FlagAr.setB O.Y B`.

Set `M` to `h.mdl P c`. Take `⟨W, a, b, hW, ha, hflag⟩` from `GlobalTheory.T.exists_projective_cover_good_reduction h₁ h₂ D O hO c P M q hq hd`. Take `⟨C, _, _, g, μ, hC, hμ, hdeg⟩` from `GlobalTheory.FbarCurve.exists_smooth_curve_over _ _ W M.V.p a M.V.ar.isProjOver hW ha q Z i hZ`. Set `k` to `AlgebraicClosure (ZMod q)`. Take `⟨t, ⟨mt⟩⟩` from `exists_sab (g ≫ b) O.s.T.Z.t`.

Use `t.semi` as an intermediate fact. Establish `ht : IsActPull t.act O.s.T.Z.t.act (g ≫ b) mt.φ` using `⟨mt.cart, mt.act⟩`. Take `⟨β, hβ⟩` from `exists_ringHom_of_curve hC.toIsProjCurve (g ≫ b ≫ O.s.T.Z.s)`. Establish `hsp` using `isSplitBy_intEmb O.κ.c hd β`. Establish `hs : Splits (𝓞 D.host.E) k` using `⟨_, inferInstance, _, hsp⟩`.

Establish `hbar` using `bar_involutive O.A.H`. Establish `hpol : PolGen (O.A.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) t.act`. Take `⟨t', ⟨mt'⟩⟩` from `exists_sab (geomGenPt C) t`. Establish `ht' : IsActPull t'.act t.act (geomGenPt C) mt'.φ` using `⟨mt'.cart, mt'.act⟩`. Establish `: CharP C.functionField q`.

Establish `e : (q : C.functionField) = 0`. Simplify using `using congrArg (C.presheaf.germ ⊤ (genericPoint C) trivial).hom (natCast_eq_zero C q k)`. Conclude with `(CharP.charP_iff_prime_eq_zero hp).2 e`. Conclude with `⟨t'.G, inferInstance, t'.act, mt'.φ, ht', GlobalTheory.T.polarization_part_of_pulled_action h₁ h₂ D O hO B q hq _ _ t'.G t'.act _ (ht'.comp ht)⟩`. Take `⟨C₁, _, _, π₁, hC₁, hπ₁, G₁, _, _, i₁, φ₁, hp₁, G', _, _, i', ρ, _, hρ, hepi, hker, hab⟩` from `GlobalTheory.T.exists_cover_semiabelian_polarization h₁ h₂ _ O.A.H q k C hC t.G t.act hpol`.

Take `⟨C₂, _, _, π₂, hC₂, hπ₂, G₂, _, _, i₂, φ₂, hp₂, hD⟩` from `GlobalTheory.T.semiabelian_action_abelian_generic hX h₁ h₂ _ O.A.H q h2 hd k C₁ hC₁ G' i' hab`. Establish `hseq` using `GlobalTheory.CurveRootGeometry.EigenSeq.hasSeq_of_hasDieu q k _ hs _ hbar C₂ hC₂ G₂ i₂ hD`. Take `⟨m₁, hm₁, hs₁⟩` from `GlobalTheory.CurvePullDeg.exists_scalesDeg k C C₁ hC hC₁ π₁ hπ₁`. Take `⟨m₂, hm₂, hs₂⟩` from `GlobalTheory.CurvePullDeg.exists_scalesDeg k C₁ C₂ hC₁ hC₂ π₂ hπ₂`. Establish `r₁` using `degRel_of_scalesDeg hs hπ₁.2.2 hs₁ hp₁`.

Establish `r₃` using `degRel_of_scalesDeg hs hπ₂.2.2 hs₂ hp₂`. Establish `r₂ : DegRel k i₁ i' 1`. Take `⟨g₁, -, hg₁⟩` from `exists_isVB_of_isSemiAbelian G₁`. Take `⟨g', -, hg'⟩` from `exists_isVB_of_isSemiAbelian G'`. Take `⟨e₁, e₂⟩` from `GlobalTheory.CurveRootGeometry.QuotDeg.quot_deg k C₁ hC₁ _ hs _ _ _ _ hg₁ hg' (lieAct i₁) (lieAct i') (lieMap ρ) (isEquivariant_lieMap ρ hρ) hepi hker`.

Conclude with `⟨fun σ => by simpa using e₁ σ, fun d hd => by simpa using e₂ d hd⟩`. Establish `rel` using `(r₁.trans r₂).trans r₃`. Set `dl (τ : D.host.E →+* ℂ) (n : ℕ) : ℤ` to `degLB k ((M.line P (.inl (τ, n))).B.pull (g ≫ a))`. Set `r (τ : D.what₂.Tau) (x : Fin O.N) : ℝ` to `μ * (topSelfIntersection (ZMod q) ((M.root P (τ, x)).B.pull i) 1 : ℝ)`. Establish `hr (τ : D.what₂.Tau) (x : Fin O.N) : r τ x = if (x : ℕ) < O.j then (dl (DV.tauEmb D τ) x : ℝ) else -(dl (conjEmb (DV.tauEmb D τ)) (O.N - 1 - x) : ℝ)`.

Simplify using `only [r]`. Rewrite using `[← hdeg _ (M.root P (τ, x)).isLB, Setup.LatModel.root]`. Use `split_ifs`. Both sides reduce to the same expression. Conclude with `degLB_pull_dual hC.toIsProjCurve (g ≫ a) (M.line P _).isLB` after adjusting the coercions.

Establish `hps (τ : D.what₂.Tau)` using `psum_root O.indef.2.le r τ (fun n => (dl (DV.tauEmb D τ) n : ℝ)) (fun n => (dl (conjEmb (DV.tauEmb D τ)) n : ℝ)) (hr τ)`. Establish `hf` using `hflag k C hC g t.G t.act mt.φ ht β hβ`. Establish `m₀ (τ : D.what₂.Tau) : O.S.Dw.mult (DV.tauEmb D τ) = O.j` using `O.L.ψ_val τ ▸ O.S.mult_psi O.L τ`. Establish `m₀' (τ : D.what₂.Tau) : O.S.Dw.mult (conjEmb (DV.tauEmb D τ)) = O.N - O.j` using `O.L.ψ_val τ ▸ O.S.mult_conj O.L τ`. Set `te (τ : D.what₂.Tau) : 𝓞 D.host.E →+* k` to `β.comp (intEmb O.κ.c (DV.tauEmb D τ))`.

Establish `tec (τ : D.host.E →+* ℂ) : (β.comp (intEmb O.κ.c τ)).comp (O.A.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = β.comp (intEmb O.κ.c (conjEmb τ))` using `by rw [intEmb_conjEmb, RingHom.comp_assoc]`. Establish `hmem (τ : D.host.E →+* ℂ) : β.comp (intEmb O.κ.c τ) ∈ Set.range te ↔ τ (O.A.H.rt : D.host.E) = O.A.H.rt0`. Use `⟨fun ⟨s, e⟩ => hsp.injective e ▸ O.A.cm s, fun e => ⟨O.L.ψ.symm ⟨τ, e⟩, ?_⟩⟩` and prove the remaining obligations. Simplify using `only [te]`. Rewrite using `[← O.L.ψ_val, Equiv.apply_symm_apply]`.

Establish `d₁ (τ : D.what₂.Tau) : (deg k (lieSub t.act (scal C (te τ))) : ℝ) = ∑ n ∈ Finset.range O.j, (dl (DV.tauEmb D τ) n : ℝ)`. Use `(hf (DV.tauEmb D τ)).2` as an intermediate fact. Rewrite `this` using `[m₀]`. Conclude with `this` after adjusting the coercions. Establish `d₂ (τ : D.what₂.Tau) : (deg k (lieSub t.act (scal C ((te τ).comp (O.A.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)))) : ℝ) = ∑ n ∈ Finset.range (O.N - O.j), (dl (conjEmb (DV.tauEmb D τ)) n : ℝ)`.

Use `(hf (conjEmb (DV.tauEmb D τ))).2` as an intermediate fact. Rewrite `this` using `[m₀', ← tec]`. Conclude with `this` after adjusting the coercions. Establish `key` using `curveData_of_hasSeq q O.j r hs hbar hC₂ rel hseq te (fun s s' e => O.L.ψ.injective (Subtype.ext (by rw [O.L.ψ_val, O.L.ψ_val]; exact hsp.injective e))) (fun σ => by`. Take `⟨τ, rfl⟩` from `hsp.exists_eq σ`.

Rewrite using `[tec, hmem, hmem]`. Conclude with `⟨fun e => AllWt.conj_not_mem ⟨τ, e⟩, fun e => by_contra fun e' => e (AllWt.conj_mem e')⟩)`. Use the proof step `(fun τ => by rw [d₁, (hps τ _ O.indef.2.le).1 le_rfl])`. Use the proof step `(fun τ => by rw [d₁, d₂, (hps τ _ le_rfl).2 O.indef.2.le]; simp)`. Use the proof step `(fun τ n _ b d => ⟨_, (hf (DV.tauEmb D τ)).1 n (by rwa [m₀]), by`.

Rewrite using `[(hps τ n d.le).1 b]`. Use `push_cast`. Use the proof step `rfl⟩)`. Use the proof step `(fun τ n b d => ⟨_, (hf (conjEmb (DV.tauEmb D τ))).1 (O.N - n) (by rw [m₀']; omega), by`. Rewrite using `[d₁, d₂, (hps τ n d.le).2 b.le]`.

Use `push_cast`. Use the proof step `rfl⟩)`. Use `⟨(m₂ * (1 * m₁) : ℕ) * μ, mul_pos (Nat.cast_pos.2 (by positivity)) hμ, ?_⟩` and prove the remaining obligations. Simplify `key` using `only [r, mul_assoc]`.
-/
theorem curveData_roots : GlobalTheory.CovTop.HypothesesXH → Hypotheses2 → HypothesesH → ∀ (D : D7) (O : Setup D), O.Core → ∀ (A : SlopeTestRemainingChoices O.Y) (T : Real0 O.Y) (H : Ht O.Y) (h : O.Reads A T H),
  ∀ (B : ℝ), 2 ≤ B → ∀ (c : O.s.Comp) (q : ℕ) [Fact q.Prime], q ∉ FlagAr.setB O.Y B →
  ∀ (Z : Scheme.{0}) (i : Z ⟶ (h.mdl (FlagAr.setB O.Y B) c).V.X) [IsClosedImmersion i] [IsIntegral Z]
    [Algebra (ZMod q) Γ(Z, ⊤)], topologicalKrullDim Z = 1 →
    ∃ μ : ℝ, 0 < μ ∧ GlobalTheory.CurveSemiAbelianConjecture.CurveData q O.j (fun (τ : D.what₂.Tau) (k : Fin O.N) =>
      μ * (topSelfIntersection (ZMod q) (((h.mdl (FlagAr.setB O.Y B) c).root (FlagAr.setB O.Y B) (τ, k)).B.pull i) 1 : ℝ)) := by
  intro hX h₁ h₂ D O hO A T H h B hB c q _ hq Z i _ _ _ hZ
  have hq' := hq
  rw [O.setB_eq, Pad.setB, Finset.mem_union, not_or] at hq'
  have hp : q.Prime := Fact.out
  have hM : O.κ.l.M' ≠ 0 := (Nat.lcm_pos (lt_of_lt_of_le (by norm_num) O.κ.l.three_le) O.κ.l.A_pos).ne'
  have hd0 : (discr D.host.E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (discr_ne_zero _)
  have hnd : ¬ q ∣ 2 * (discr D.host.E).natAbs * O.κ.l.M' := fun e =>
    hq'.2 (Nat.mem_primeFactors.2 ⟨hp, e, mul_ne_zero (mul_ne_zero two_ne_zero hd0) hM⟩)
  have hd : ¬ q ∣ (discr D.host.E).natAbs := fun e => hnd ((e.mul_left 2).mul_right _)
  have h2 : q ≠ 2 := fun e => hnd (e.dvd.trans ((dvd_mul_right 2 _).mul_right _))
  let P := FlagAr.setB O.Y B
  let M := h.mdl P c
  obtain ⟨W, a, b, hW, ha, hflag⟩ := GlobalTheory.T.exists_projective_cover_good_reduction h₁ h₂ D O hO c P M q hq hd
  obtain ⟨C, _, _, g, μ, hC, hμ, hdeg⟩ := GlobalTheory.FbarCurve.exists_smooth_curve_over _ _ W M.V.p a M.V.ar.isProjOver hW ha q Z i hZ
  let k := AlgebraicClosure (ZMod q)
  obtain ⟨t, ⟨mt⟩⟩ := exists_sab (g ≫ b) O.s.T.Z.t
  have := t.semi
  have ht : IsActPull t.act O.s.T.Z.t.act (g ≫ b) mt.φ := ⟨mt.cart, mt.act⟩
  obtain ⟨β, hβ⟩ := exists_ringHom_of_curve hC.toIsProjCurve (g ≫ b ≫ O.s.T.Z.s)
  have hsp := isSplitBy_intEmb O.κ.c hd β
  have hs : Splits (𝓞 D.host.E) k := ⟨_, inferInstance, _, hsp⟩
  have hbar := bar_involutive O.A.H

  have hpol : PolGen (O.A.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) t.act := by
    obtain ⟨t', ⟨mt'⟩⟩ := exists_sab (geomGenPt C) t
    have ht' : IsActPull t'.act t.act (geomGenPt C) mt'.φ := ⟨mt'.cart, mt'.act⟩
    have : CharP C.functionField q := by
      have e : (q : C.functionField) = 0 := by
        simpa using congrArg (C.presheaf.germ ⊤ (genericPoint C) trivial).hom (natCast_eq_zero C q k)
      exact (CharP.charP_iff_prime_eq_zero hp).2 e
    exact ⟨t'.G, inferInstance, t'.act, mt'.φ, ht', GlobalTheory.T.polarization_part_of_pulled_action h₁ h₂ D O hO B q hq _ _ t'.G t'.act _ (ht'.comp ht)⟩
  obtain ⟨C₁, _, _, π₁, hC₁, hπ₁, G₁, _, _, i₁, φ₁, hp₁, G', _, _, i', ρ, _, hρ, hepi, hker, hab⟩ :=
    GlobalTheory.T.exists_cover_semiabelian_polarization h₁ h₂ _ O.A.H q k C hC t.G t.act hpol
  obtain ⟨C₂, _, _, π₂, hC₂, hπ₂, G₂, _, _, i₂, φ₂, hp₂, hD⟩ := GlobalTheory.T.semiabelian_action_abelian_generic hX h₁ h₂ _ O.A.H q h2 hd k C₁ hC₁ G' i' hab
  have hseq := GlobalTheory.CurveRootGeometry.EigenSeq.hasSeq_of_hasDieu q k _ hs _ hbar C₂ hC₂ G₂ i₂ hD
  obtain ⟨m₁, hm₁, hs₁⟩ := GlobalTheory.CurvePullDeg.exists_scalesDeg k C C₁ hC hC₁ π₁ hπ₁
  obtain ⟨m₂, hm₂, hs₂⟩ := GlobalTheory.CurvePullDeg.exists_scalesDeg k C₁ C₂ hC₁ hC₂ π₂ hπ₂
  have r₁ := degRel_of_scalesDeg hs hπ₁.2.2 hs₁ hp₁
  have r₃ := degRel_of_scalesDeg hs hπ₂.2.2 hs₂ hp₂
  have r₂ : DegRel k i₁ i' 1 := by
    obtain ⟨g₁, -, hg₁⟩ := exists_isVB_of_isSemiAbelian G₁
    obtain ⟨g', -, hg'⟩ := exists_isVB_of_isSemiAbelian G'
    obtain ⟨e₁, e₂⟩ := GlobalTheory.CurveRootGeometry.QuotDeg.quot_deg k C₁ hC₁ _ hs _ _ _ _ hg₁ hg' (lieAct i₁) (lieAct i') (lieMap ρ)
      (isEquivariant_lieMap ρ hρ) hepi hker
    exact ⟨fun σ => by simpa using e₁ σ, fun d hd => by simpa using e₂ d hd⟩
  have rel := (r₁.trans r₂).trans r₃

  let dl (τ : D.host.E →+* ℂ) (n : ℕ) : ℤ := degLB k ((M.line P (.inl (τ, n))).B.pull (g ≫ a))
  let r (τ : D.what₂.Tau) (x : Fin O.N) : ℝ := μ * (topSelfIntersection (ZMod q) ((M.root P (τ, x)).B.pull i) 1 : ℝ)
  have hr (τ : D.what₂.Tau) (x : Fin O.N) : r τ x = if (x : ℕ) < O.j then (dl (DV.tauEmb D τ) x : ℝ)
      else -(dl (conjEmb (DV.tauEmb D τ)) (O.N - 1 - x) : ℝ) := by
    simp only [r]
    rw [← hdeg _ (M.root P (τ, x)).isLB, Setup.LatModel.root]
    split_ifs
    · rfl
    · exact_mod_cast degLB_pull_dual hC.toIsProjCurve (g ≫ a) (M.line P _).isLB
  have hps (τ : D.what₂.Tau) := psum_root O.indef.2.le r τ (fun n => (dl (DV.tauEmb D τ) n : ℝ))
    (fun n => (dl (conjEmb (DV.tauEmb D τ)) n : ℝ)) (hr τ)
  have hf := hflag k C hC g t.G t.act mt.φ ht β hβ
  have m₀ (τ : D.what₂.Tau) : O.S.Dw.mult (DV.tauEmb D τ) = O.j := O.L.ψ_val τ ▸ O.S.mult_psi O.L τ
  have m₀' (τ : D.what₂.Tau) : O.S.Dw.mult (conjEmb (DV.tauEmb D τ)) = O.N - O.j := O.L.ψ_val τ ▸ O.S.mult_conj O.L τ
  let te (τ : D.what₂.Tau) : 𝓞 D.host.E →+* k := β.comp (intEmb O.κ.c (DV.tauEmb D τ))
  have tec (τ : D.host.E →+* ℂ) : (β.comp (intEmb O.κ.c τ)).comp (O.A.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) =
      β.comp (intEmb O.κ.c (conjEmb τ)) := by rw [intEmb_conjEmb, RingHom.comp_assoc]
  have hmem (τ : D.host.E →+* ℂ) : β.comp (intEmb O.κ.c τ) ∈ Set.range te ↔ τ (O.A.H.rt : D.host.E) = O.A.H.rt0 := by
    refine ⟨fun ⟨s, e⟩ => hsp.injective e ▸ O.A.cm s, fun e => ⟨O.L.ψ.symm ⟨τ, e⟩, ?_⟩⟩
    simp only [te]
    rw [← O.L.ψ_val, Equiv.apply_symm_apply]
  have d₁ (τ : D.what₂.Tau) : (deg k (lieSub t.act (scal C (te τ))) : ℝ) =
      ∑ n ∈ Finset.range O.j, (dl (DV.tauEmb D τ) n : ℝ) := by
    have := (hf (DV.tauEmb D τ)).2
    rw [m₀] at this
    exact_mod_cast this
  have d₂ (τ : D.what₂.Tau) :
      (deg k (lieSub t.act (scal C ((te τ).comp (O.A.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)))) : ℝ) =
      ∑ n ∈ Finset.range (O.N - O.j), (dl (conjEmb (DV.tauEmb D τ)) n : ℝ) := by
    have := (hf (conjEmb (DV.tauEmb D τ))).2
    rw [m₀', ← tec] at this
    exact_mod_cast this
  have key := curveData_of_hasSeq q O.j r hs hbar hC₂ rel hseq te
    (fun s s' e => O.L.ψ.injective (Subtype.ext (by rw [O.L.ψ_val, O.L.ψ_val]; exact hsp.injective e)))
    (fun σ => by
      obtain ⟨τ, rfl⟩ := hsp.exists_eq σ
      rw [tec, hmem, hmem]
      exact ⟨fun e => AllWt.conj_not_mem ⟨τ, e⟩, fun e => by_contra fun e' => e (AllWt.conj_mem e')⟩)
    (fun τ => by rw [d₁, (hps τ _ O.indef.2.le).1 le_rfl])
    (fun τ => by rw [d₁, d₂, (hps τ _ le_rfl).2 O.indef.2.le]; simp)
    (fun τ n _ b d => ⟨_, (hf (DV.tauEmb D τ)).1 n (by rwa [m₀]), by
      rw [(hps τ n d.le).1 b]; push_cast; rfl⟩)
    (fun τ n b d => ⟨_, (hf (conjEmb (DV.tauEmb D τ))).1 (O.N - n) (by rw [m₀']; omega), by
      rw [d₁, d₂, (hps τ n d.le).2 b.le]; push_cast; rfl⟩)
  refine ⟨(m₂ * (1 * m₁) : ℕ) * μ, mul_pos (Nat.cast_pos.2 (by positivity)) hμ, ?_⟩
  simpa only [r, mul_assoc] using key

end GlobalTheory.CurveRootGeometry
