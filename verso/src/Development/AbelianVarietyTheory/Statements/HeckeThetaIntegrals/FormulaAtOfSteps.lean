import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousReGLSymm

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames

namespace GlobalTheory.RowClaim.StepsModel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7} {T : Type}

/- English proof (translation)
Proceed by induction on `hz using Subgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨w, x, rfl⟩` from `hz`. Use `⟨?_, hL w x⟩` and prove the remaining obligations. Establish `: ((L.xiH t) ^ n).loc w x = 1` using `by rw [show (L.xiH t) ^ n = 1 from hn]; rfl`.

Conclude with `this`. Consider the case `one => exact ⟨one_pow _, 1, by simp⟩`. Consider the case `mul a b _ _ ha hb`. Take `⟨x, hx⟩` from `ha.2`. Take `⟨y, hy⟩` from `hb.2`.

Conclude with `⟨by rw [mul_pow, ha.1, hb.1, one_mul], x * y, by simp [hx, hy]⟩`. Consider the case `inv a _ ha`. Take `⟨x, hx⟩` from `ha.2`. Conclude with `⟨by rw [inv_pow, ha.1, inv_one], x⁻¹, by simp [hx]⟩`.
-/
theorem xiVals_spec {L : LevCh D T} {t : T} {n : ℕ} (hn : (L.xiH t).OrderDvd n) (hL : LocIn D.what₂.embLL (L.xiH t))
    {z : ℂˣ} (hz : z ∈ xiVals L t) : z ^ n = 1 ∧ (z : ℂ) ∈ Set.range D.what₂.embLL := by
  induction hz using Subgroup.closure_induction with
  | mem z hz =>
    obtain ⟨w, x, rfl⟩ := hz
    refine ⟨?_, hL w x⟩
    have : ((L.xiH t) ^ n).loc w x = 1 := by rw [show (L.xiH t) ^ n = 1 from hn]; rfl
    exact this
  | one => exact ⟨one_pow _, 1, by simp⟩
  | mul a b _ _ ha hb =>
    obtain ⟨x, hx⟩ := ha.2
    obtain ⟨y, hy⟩ := hb.2
    exact ⟨by rw [mul_pow, ha.1, hb.1, one_mul], x * y, by simp [hx, hy]⟩
  | inv a _ ha =>
    obtain ⟨x, hx⟩ := ha.2
    exact ⟨by rw [inv_pow, ha.1, inv_one], x⁻¹, by simp [hx]⟩

/- English proof (translation)
Simplify using `using Bplus_smul W M 1 c φ F`.
-/
theorem bplus_smul_right {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G) (c : ℂ) (φ : Fn G (.top 0))
    (F : Fn G (.grid D.R.m 0)) : Bplus W M φ (c • F) = c * Bplus W M φ F := by
  simpa using Bplus_smul W M 1 c φ F

/- English proof (translation)
Substitute `he h1 h2 h3 h4` using the available equality. Clear the denominators using the available nonvanishing facts.
-/
theorem final_calc {e z z' c p b s u κ v w : ℂ} (he : e = z * z') (hz : z ≠ 0) (hz' : z' ≠ 0) (hc : c ≠ 0)
    (h1 : p = (z * c)⁻¹ * b) (h2 : b = z'⁻¹ * s * u) (h3 : u = κ * v) (h4 : w = s * v) : e * c * p = κ * w := by
  subst he h1 h2 h3 h4
  field_simp

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

set_option maxHeartbeats 4000000 in

/- English proof (translation)
Take `⟨τi, z, hF⟩` from `hF`. Take `⟨σ, z', hU⟩` from `hU τi`. Take `⟨hM, hJ⟩` from `hJ`. Take `⟨κ, hJ⟩` from `hJ σ`. Establish `key : ∀ t, ∃ e : D.what₂.LL, D.what₂.embLL e = (z t : ℂ) * z' t ∧ ∃ n : ℕ, 0 < n ∧ e ^ n = 1` using `fun t => by`.

Take `⟨n, hn, ho⟩` from `hL.xi_fin t`. Take `⟨h1, e, he⟩` from `xiVals_spec ho (hK.chars.xi t) (mul_mem (hF t).1 (hU t).1)`. Use `⟨e, he, n, hn, D.what₂.embLL.injective ?_⟩` and prove the remaining obligations. Rewrite using `[map_pow, he, map_one, ← Units.val_pow_eq_pow_val, h1, Units.val_one]`. Use `choose ze hze hzn using key`.

Use `⟨κ, ze, hzn, fun t x hx a => ?_⟩` and prove the remaining obligations. Take `⟨τ, hτ, hfl⟩` from `(hF t).2 (ch.Phi a)`. Take `⟨M, hMt⟩` from `exists_vol ch.G hL t`. Use `choose Mβ hMβ using hM t (ch.Phi a)`. Establish `hex : ∀ β ∈ ch.S.supp t (ch.Phi a), ch.S.IsExpansion t (ch.Phi a) β (Classical.epsilon (ch.S.IsExpansion t (ch.Phi a) β))` using `fun β hβ => Classical.epsilon_spec ((hS t a).ex β hβ)`.

Establish `e1 : psiK ch a (R.Th t (R.jX t x)) = Bplus ch.W ch.M (colFn ch a) (thetaChi ch.W ch.M ch.ρ (ch.Phi a) (ch.cv.lift t (R.jX t x)))`. Conclude with `congrArg (fun u => Bplus ch.W ch.M (colFn ch a) (thetaChi ch.W ch.M ch.ρ (ch.Phi a) u)) ((form_Th ch hC t _).trans (hP t x hx))`. Establish `e2` using `(hU t).2 a τ hτ M hMt Mβ (fun β => Classical.epsilon (ch.S.IsExpansion t (ch.Phi a) β)) (fun β hβ => ⟨hMβ β, hex β hβ⟩) (R.jX t x)`. Establish `e3 : (∑ᶠ β ∈ ch.S.supp t (ch.Phi a), (∏ w, ((ch.S.term t (ch.Phi a) β w).coef : ℂ)) * defTot t ch.S.toGridChoice (Mβ β) σ (Classical.epsilon (ch.S.IsExpansion t (ch.Phi a) β)) (colFn ch a) (formTop ch t (R.jX t x))) = κ * ch.S.vCore t (ch.Phi a) (psiC (ch.Psi a)) (ch.S.formC t (R …`. Rewrite using `[(hS t a).vCore_eq _ hex, finsum_mem_eq_finite_toFinset_sum _ (hS t a).fin, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun β hβ => ?_` and prove the remaining obligations. Establish `hβ'` using `(Set.Finite.mem_toFinset _).1 hβ`. Conclude with `(congrArg (HMul.hMul _) (hJ t a β hβ' (Mβ β) _ (hMβ β) (hex β hβ') (R.jX t x))).trans (mul_left_comm _ _ _)`. Establish `e4 : vK ch t x a = ch.S.sAA * ch.S.vCore t (ch.Phi a) (psiC (ch.Psi a)) (ch.S.formC t (R.jX t x))` using `rfl`. Establish `hct : cTot ch t ≠ 0` using `(cTot_ne_zero_iff ch t).2 fun i j => hc i j t`.

Establish `e5` using `congrArg (Bplus ch.W ch.M (colFn ch a)) (hfl M hMt (R.jX t x)).2`. Conclude with `final_calc (hze t) (z t).ne_zero (z' t).ne_zero hct (e1.trans (e5.trans (bplus_smul_right _ _ _ _ _))) e2 e3 e4`.
-/
theorem formulaAt_of_steps (hL : R.toLevCh.Is A.μ0) (hC : R.IsChain) (ch : Choice R) (hP : ProjAt ch) (hF : FlipAt ch)
    (hU : UnfoldAt ch) (hJ : JetsAt ch) (hc : ∀ i j t, ch.c i j t ≠ 0) (hS : ∀ t a, ch.S.SumOK t (ch.Phi a))
    (hK : ch.FieldOK) : ∃ κ ze, FormulaAt ch κ ze := by
  obtain ⟨τi, z, hF⟩ := hF
  obtain ⟨σ, z', hU⟩ := hU τi
  obtain ⟨hM, hJ⟩ := hJ
  obtain ⟨κ, hJ⟩ := hJ σ
  have key : ∀ t, ∃ e : D.what₂.LL, D.what₂.embLL e = (z t : ℂ) * z' t ∧ ∃ n : ℕ, 0 < n ∧ e ^ n = 1 := fun t => by
    obtain ⟨n, hn, ho⟩ := hL.xi_fin t
    obtain ⟨h1, e, he⟩ := xiVals_spec ho (hK.chars.xi t) (mul_mem (hF t).1 (hU t).1)
    refine ⟨e, he, n, hn, D.what₂.embLL.injective ?_⟩
    rw [map_pow, he, map_one, ← Units.val_pow_eq_pow_val, h1, Units.val_one]
  choose ze hze hzn using key
  refine ⟨κ, ze, hzn, fun t x hx a => ?_⟩
  obtain ⟨τ, hτ, hfl⟩ := (hF t).2 (ch.Phi a)
  obtain ⟨M, hMt⟩ := exists_vol ch.G hL t
  choose Mβ hMβ using hM t (ch.Phi a)
  have hex : ∀ β ∈ ch.S.supp t (ch.Phi a), ch.S.IsExpansion t (ch.Phi a) β
      (Classical.epsilon (ch.S.IsExpansion t (ch.Phi a) β)) := fun β hβ => Classical.epsilon_spec ((hS t a).ex β hβ)
  have e1 : psiK ch a (R.Th t (R.jX t x)) =
      Bplus ch.W ch.M (colFn ch a) (thetaChi ch.W ch.M ch.ρ (ch.Phi a) (ch.cv.lift t (R.jX t x))) := by
    exact congrArg (fun u => Bplus ch.W ch.M (colFn ch a) (thetaChi ch.W ch.M ch.ρ (ch.Phi a) u))
      ((form_Th ch hC t _).trans (hP t x hx))
  have e2 := (hU t).2 a τ hτ M hMt Mβ (fun β => Classical.epsilon (ch.S.IsExpansion t (ch.Phi a) β)) (fun β hβ => ⟨hMβ β, hex β hβ⟩) (R.jX t x)
  have e3 : (∑ᶠ β ∈ ch.S.supp t (ch.Phi a), (∏ w, ((ch.S.term t (ch.Phi a) β w).coef : ℂ)) *
      defTot t ch.S.toGridChoice (Mβ β) σ (Classical.epsilon (ch.S.IsExpansion t (ch.Phi a) β)) (colFn ch a)
        (formTop ch t (R.jX t x))) = κ * ch.S.vCore t (ch.Phi a) (psiC (ch.Psi a)) (ch.S.formC t (R.jX t x)) := by
    rw [(hS t a).vCore_eq _ hex, finsum_mem_eq_finite_toFinset_sum _ (hS t a).fin, Finset.mul_sum]
    refine Finset.sum_congr rfl fun β hβ => ?_
    have hβ' := (Set.Finite.mem_toFinset _).1 hβ
    exact (congrArg (HMul.hMul _) (hJ t a β hβ' (Mβ β) _ (hMβ β) (hex β hβ') (R.jX t x))).trans (mul_left_comm _ _ _)
  have e4 : vK ch t x a = ch.S.sAA * ch.S.vCore t (ch.Phi a) (psiC (ch.Psi a)) (ch.S.formC t (R.jX t x)) := rfl
  have hct : cTot ch t ≠ 0 := (cTot_ne_zero_iff ch t).2 fun i j => hc i j t
  have e5 := congrArg (Bplus ch.W ch.M (colFn ch a)) (hfl M hMt (R.jX t x)).2
  exact final_calc (hze t) (z t).ne_zero (z' t).ne_zero hct (e1.trans (e5.trans (bplus_smul_right _ _ _ _ _))) e2 e3 e4

/- English proof (translation)
Take `⟨C0, H⟩` from `((((hP.and hF).and hU).and hJ).and hc).and hS`. Use `⟨C0, fun ε CF h => ?_⟩` and prove the remaining obligations. Take `⟨x₀, H⟩` from `H ε CF h`. Use `⟨x₀, fun D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch i j hK => ?_⟩` and prove the remaining obligations. Take `⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, f⟩, g⟩` from `H D large₂ e hx Γ Pl0 T A Ks R F s ch i j`.

Conclude with `formulaAt_of_steps s.core.lev s.core.chain ch a b c d (fun i j t => (f i j t).2) g hK`.
-/
theorem formula2K_of_steps (hP : StepProj) (hF : StepFlip) (hU : StepUnfold) (hJ : StepJets) (hc : ConstK) (hS : SumOKK) :
    Formula2K := by
  obtain ⟨C0, H⟩ := ((((hP.and hF).and hU).and hJ).and hc).and hS
  refine ⟨C0, fun ε CF h => ?_⟩
  obtain ⟨x₀, H⟩ := H ε CF h
  refine ⟨x₀, fun D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch i j hK => ?_⟩
  obtain ⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, f⟩, g⟩ := H D large₂ e hx Γ Pl0 T A Ks R F s ch i j
  exact formulaAt_of_steps s.core.lev s.core.chain ch a b c d (fun i j t => (f i j t).2) g hK

/- English proof (translation)
Take `⟨M₀, -⟩` from `exists_vol G hL t`. Establish `H : ∀ X : Node, ∃ (μ : Measure (GA D (G.V X))) (𝓕 : Set (GA D (G.V X))), (∀ j (h : j < D.R.m) (e : X = .top j), by`. Substitute `e` using the available equality. Conclude with `if (Node.top j).neg D.R.m = 0 then IsMeasDef _ (S.levTop t Φ β j h) μ 𝓕 else Lev.IsMeasFD _ (S.levTop t Φ β j h) μ 𝓕) ∧`. Use the proof step `∀ i (h : i ≤ D.R.m) (e : X = .grid i D.R.m), by`.

Substitute `e; exact if (Node.grid i D.R.m).neg D.R.m = 0 then IsMeasDef _ (S.levRow t i h) μ 𝓕 else Lev.IsMeasFD _ (S.levRow t i h) μ 𝓕 := fun X => by` using the available equality. Distinguish the cases in `h1 : ∃ j, j < D.R.m ∧ X = .top j`. Take `⟨j, hj, rfl⟩` from `h1`. Establish `hV` using `node_isV G hL (X := .top j) hj.le`. Take `⟨μ, 𝓕, e⟩` from `exists_meas _ hV.sigOK (fun τ => congrArg Prod.snd (hV.sig τ)) _ (S.isCO_levTop W t Φ β hj)`.

Use `⟨μ, 𝓕, fun j' h e' => ?_, fun _ _ e' => by cases e'⟩` and prove the remaining obligations. Consider the cases of `e'`. Conclude with `e`. Distinguish the cases in `h2 : ∃ i, i ≤ D.R.m ∧ X = .grid i D.R.m`. Take `⟨i, hi, rfl⟩` from `h2`.

Establish `hV` using `node_isV G hL (X := .grid i D.R.m) ⟨hi, le_rfl⟩`. Take `⟨μ, 𝓕, e⟩` from `exists_meas _ hV.sigOK (fun τ => congrArg Prod.snd (hV.sig τ)) _ (S.isCO_levRow W t hi)`. Use `⟨μ, 𝓕, fun _ _ e' => (by cases e'), fun j' h e' => ?_⟩` and prove the remaining obligations. Consider the cases of `e'`. Conclude with `e`.

Conclude with `⟨0, ∅, fun j h e => absurd ⟨j, h, e⟩ h1, fun i h e => absurd ⟨i, h, e⟩ h2⟩`. Use `choose ν fd hν using H`. Conclude with `⟨⟨ν, fd, M₀.νN, M₀.fdN⟩, fun j h => (hν _).1 j h rfl, fun i h => (hν _).2 i h rfl⟩`.
-/
theorem exists_isTermVol {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {μ₀ : T}
    (hL : L.Is μ₀) (t : T) (Φ : G.Datum) (β : CosFam G t) : ∃ M, IsTermVol t S Φ β M := by
  obtain ⟨M₀, -⟩ := exists_vol G hL t
  have H : ∀ X : Node, ∃ (μ : Measure (GA D (G.V X))) (𝓕 : Set (GA D (G.V X))), (∀ j (h : j < D.R.m) (e : X = .top j), by
        subst e; exact if (Node.top j).neg D.R.m = 0 then IsMeasDef _ (S.levTop t Φ β j h) μ 𝓕
          else Lev.IsMeasFD _ (S.levTop t Φ β j h) μ 𝓕) ∧
      ∀ i (h : i ≤ D.R.m) (e : X = .grid i D.R.m), by
        subst e; exact if (Node.grid i D.R.m).neg D.R.m = 0 then IsMeasDef _ (S.levRow t i h) μ 𝓕
          else Lev.IsMeasFD _ (S.levRow t i h) μ 𝓕 := fun X => by
    by_cases h1 : ∃ j, j < D.R.m ∧ X = .top j
    · obtain ⟨j, hj, rfl⟩ := h1
      have hV := node_isV G hL (X := .top j) hj.le
      obtain ⟨μ, 𝓕, e⟩ := exists_meas _ hV.sigOK (fun τ => congrArg Prod.snd (hV.sig τ)) _ (S.isCO_levTop W t Φ β hj)
      refine ⟨μ, 𝓕, fun j' h e' => ?_, fun _ _ e' => by cases e'⟩
      cases e'; exact e
    · by_cases h2 : ∃ i, i ≤ D.R.m ∧ X = .grid i D.R.m
      · obtain ⟨i, hi, rfl⟩ := h2
        have hV := node_isV G hL (X := .grid i D.R.m) ⟨hi, le_rfl⟩
        obtain ⟨μ, 𝓕, e⟩ := exists_meas _ hV.sigOK (fun τ => congrArg Prod.snd (hV.sig τ)) _ (S.isCO_levRow W t hi)
        refine ⟨μ, 𝓕, fun _ _ e' => (by cases e'), fun j' h e' => ?_⟩
        cases e'; exact e
      · exact ⟨0, ∅, fun j h e => absurd ⟨j, h, e⟩ h1, fun i h e => absurd ⟨i, h, e⟩ h2⟩
  choose ν fd hν using H
  exact ⟨⟨ν, fd, M₀.νN, M₀.fdN⟩, fun j h => (hν _).1 j h rfl, fun i h => (hν _).2 i h rfl⟩

end GlobalTheory.RowClaim.StepsModel

end
