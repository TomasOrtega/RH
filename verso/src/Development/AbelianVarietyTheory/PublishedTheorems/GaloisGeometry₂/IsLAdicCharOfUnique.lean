import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.PolarizedGaloisRepPublished
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.PolarizedPairLineIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.NotIsPolarizedOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerOfInfConn

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.TheRec

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GalHyps.Model

/- English proof (translation)
Take `⟨x, hx⟩` from `Field.exists_primitive_element ℚ K`. Establish `hinj : ∀ φ φ' : K →+* ℂ, φ x = φ' x → φ = φ'` using `fun φ φ' e => by`. Use `(Field.primitive_element_iff_algHom_eq_of_eval' ℚ ℂ (fun _ => IsAlgClosed.splits _) x).1 hx (a₁ := φ.toRatAlgHom) (a₂ := φ'.toRatAlgHom) e` as an intermediate fact. Conclude with `RingHom.ext fun y => DFunLike.congr_fun this y`. Set `P : Polynomial ℂ` to `∏ φ : K →+* ℂ, (Polynomial.X + Polynomial.C (φ x)) ^ (m φ).toNat`.

Set `Q : Polynomial ℂ` to `∏ φ : K →+* ℂ, (Polynomial.X + Polynomial.C (φ x)) ^ (-m φ).toNat`. Take `⟨T, hT⟩` from `exists_nat_gt (∑ φ : K →+* ℂ, ‖φ x‖)`. Establish `hb : ∀ φ : K →+* ℂ, ‖φ x‖ < T` using `fun φ => (Finset.single_le_sum (f := fun φ : K →+* ℂ => ‖φ x‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ φ)).trans_lt hT`. Establish `hPQ : P = Q`. Use `Polynomial.eq_of_infinite_eval_eq _ _ (Set.infinite_of_injective_forall_mem (f := fun t : ℕ => ((T + t : ℕ) : ℂ)) (fun s t e => by simpa using e) fun t => ?_)` and prove the remaining obligations.

Establish `hne : ∀ φ : K →+* ℂ, ((T + t : ℕ) : ℂ) + φ x ≠ 0` using `fun φ e => by`. Establish `e' : φ x = -((T + t : ℕ) : ℂ)` using `by linear_combination e`. Use `hb φ` as an intermediate fact. Rewrite `this` using `[e', norm_neg, Complex.norm_natCast]`. Move the coercions through the operations in `at this`.

Combine the linear relations using `[Nat.cast_nonneg (α := ℝ) t]`. Establish `h0 : ((T + t : ℕ) : K) + x ≠ 0` using `fun e => hne ψ (by simpa using congrArg ψ e)`. Establish `h1` using `h (Units.mk0 _ h0) fun φ => by`. Use `hb (Complex.ofRealHom.comp φ)` as an intermediate fact. Simplify using `only [RingHom.comp_apply, Complex.ofRealHom_eq_coe, Complex.norm_real, Real.norm_eq_abs] at this`.

Simplify using `only [Units.val_mk0, map_add, map_natCast]`. Use `push_cast`. Combine the linear relations using `[Nat.cast_nonneg (α := ℝ) t, neg_abs_le (φ x)]`. Simplify using `only [Units.val_mk0, map_add, map_natCast] at h1`. Simplify using `only [Set.mem_setOf_eq, P, Q, Polynomial.eval_prod, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]`.

Rewrite using `[← one_mul (∏ φ : K →+* ℂ, _ ^ (-m φ).toNat), ← h1, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun φ _ => ?_` and prove the remaining obligations. Rewrite using `[← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hne φ)]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.

Assume the negation of the conclusion as `hc`. Establish `e` using `congrArg (Polynomial.eval (-ψ x)) hPQ`. Simplify using `only [P, Q, Polynomial.eval_prod, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C] at e`. Rewrite `e` using `[Finset.prod_eq_zero (Finset.mem_univ ψ) (by rw [neg_add_cancel]; exact zero_pow (by omega))]`. Use `Finset.prod_ne_zero_iff.2 (fun φ _ => ?_) e.symm` and prove the remaining obligations.

Distinguish the cases in `hφ : φ = ψ`. Rewrite using `[hφ, show (-m ψ).toNat = 0 by omega, pow_zero]; exact one_ne_zero`. Conclude with `pow_ne_zero _ fun e' => hφ (hinj _ _ (by linear_combination e'))`.
-/
theorem expo_nonpos {K : Type} [Field K] [NumberField K] (m : (K →+* ℂ) → ℤ)
    (h : ∀ k : Kˣ, (∀ φ : K →+* ℝ, 0 < φ (k : K)) → ∏ φ : K →+* ℂ, φ (k : K) ^ m φ = 1) (ψ : K →+* ℂ) : m ψ ≤ 0 := by
  obtain ⟨x, hx⟩ := Field.exists_primitive_element ℚ K
  have hinj : ∀ φ φ' : K →+* ℂ, φ x = φ' x → φ = φ' := fun φ φ' e => by
    have := (Field.primitive_element_iff_algHom_eq_of_eval' ℚ ℂ (fun _ => IsAlgClosed.splits _) x).1 hx
      (a₁ := φ.toRatAlgHom) (a₂ := φ'.toRatAlgHom) e
    exact RingHom.ext fun y => DFunLike.congr_fun this y
  let P : Polynomial ℂ := ∏ φ : K →+* ℂ, (Polynomial.X + Polynomial.C (φ x)) ^ (m φ).toNat
  let Q : Polynomial ℂ := ∏ φ : K →+* ℂ, (Polynomial.X + Polynomial.C (φ x)) ^ (-m φ).toNat
  obtain ⟨T, hT⟩ := exists_nat_gt (∑ φ : K →+* ℂ, ‖φ x‖)
  have hb : ∀ φ : K →+* ℂ, ‖φ x‖ < T := fun φ =>
    (Finset.single_le_sum (f := fun φ : K →+* ℂ => ‖φ x‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ φ)).trans_lt hT
  have hPQ : P = Q := by
    refine Polynomial.eq_of_infinite_eval_eq _ _ (Set.infinite_of_injective_forall_mem
      (f := fun t : ℕ => ((T + t : ℕ) : ℂ)) (fun s t e => by simpa using e) fun t => ?_)
    have hne : ∀ φ : K →+* ℂ, ((T + t : ℕ) : ℂ) + φ x ≠ 0 := fun φ e => by
      have e' : φ x = -((T + t : ℕ) : ℂ) := by linear_combination e
      have := hb φ
      rw [e', norm_neg, Complex.norm_natCast] at this
      push_cast at this
      linarith [Nat.cast_nonneg (α := ℝ) t]
    have h0 : ((T + t : ℕ) : K) + x ≠ 0 := fun e => hne ψ (by simpa using congrArg ψ e)
    have h1 := h (Units.mk0 _ h0) fun φ => by
      have := hb (Complex.ofRealHom.comp φ)
      simp only [RingHom.comp_apply, Complex.ofRealHom_eq_coe, Complex.norm_real, Real.norm_eq_abs] at this
      simp only [Units.val_mk0, map_add, map_natCast]
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) t, neg_abs_le (φ x)]
    simp only [Units.val_mk0, map_add, map_natCast] at h1
    simp only [Set.mem_setOf_eq, P, Q, Polynomial.eval_prod, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_C]
    rw [← one_mul (∏ φ : K →+* ℂ, _ ^ (-m φ).toNat), ← h1, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun φ _ => ?_
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hne φ)]
    congr 1
    omega
  by_contra hc
  have e := congrArg (Polynomial.eval (-ψ x)) hPQ
  simp only [P, Q, Polynomial.eval_prod, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_C] at e
  rw [Finset.prod_eq_zero (Finset.mem_univ ψ) (by rw [neg_add_cancel]; exact zero_pow (by omega))] at e
  refine Finset.prod_ne_zero_iff.2 (fun φ _ => ?_) e.symm
  by_cases hφ : φ = ψ
  · rw [hφ, show (-m ψ).toNat = 0 by omega, pow_zero]; exact one_ne_zero
  · exact pow_ne_zero _ fun e' => hφ (hinj _ _ (by linear_combination e'))

/- English proof (translation)
Establish `key : ∀ {n n' : (K →+* ℂ) → ℤ}, IsAlgPos χ n → IsAlgPos χ n' → ∀ ψ, n ψ ≤ n' ψ` using `fun {n n'} h h' ψ => by`. Use `expo_nonpos (n - n') (fun k hk => by` as an intermediate fact. Establish `hk0 : ∀ φ : K →+* ℂ, φ (k : K) ≠ 0` using `fun φ => by simp`. Simplify using `only [Pi.sub_apply, zpow_sub₀ (hk0 _), Finset.prod_div_distrib]`. Rewrite using `[← h k hk, ← h' k hk]`.

Conclude with `div_self (Units.ne_zero _)) ψ`. Simplify using `using this`. Conclude with `funext fun ψ => le_antisymm (key h h' ψ) (key h' h ψ)`.
-/
theorem isAlgPos_unique {K : Type} [Field K] [NumberField K] {χ : HChar K} {n n' : (K →+* ℂ) → ℤ}
    (h : IsAlgPos χ n) (h' : IsAlgPos χ n') : n = n' := by
  have key : ∀ {n n' : (K →+* ℂ) → ℤ}, IsAlgPos χ n → IsAlgPos χ n' → ∀ ψ, n ψ ≤ n' ψ := fun {n n'} h h' ψ => by
    have := expo_nonpos (n - n') (fun k hk => by
      have hk0 : ∀ φ : K →+* ℂ, φ (k : K) ≠ 0 := fun φ => by simp
      simp only [Pi.sub_apply, zpow_sub₀ (hk0 _), Finset.prod_div_distrib]
      rw [← h k hk, ← h' k hk]
      exact div_self (Units.ne_zero _)) ψ
    simpa using this
  exact funext fun ψ => le_antisymm (key h h' ψ) (key h' h ψ)

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}
  [IsAlgClosure E Ω] [IsCMField E]

/- English proof (translation)
Assemble the required witnesses or components as `⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.trans _ E Ω⟩`.
-/
theorem isAlgClosure_real : IsAlgClosure (maximalRealSubfield E) Ω :=
  ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.trans _ E Ω⟩

/- English proof (translation)
Take `⟨c, art, n, h1, h2, h3⟩` from `h`. Take `⟨c', art', n', h1', h2', h3'⟩` from `h'`. Take `rfl` from `isAlgPos_unique h2 h2'`. Use `isAlgClosure_real (E := E) (Ω := Ω)` as an intermediate fact. Conclude with `IsLAdicOf.eq_of_isGlobalArtin h1 h1' c c' h3 h3'`.
-/
theorem isLAdicCharOf_unique {ι : Qbar l ≃+* ℂ} {χ : HChar (maximalRealSubfield E)}
    {μ μ' : G (maximalRealSubfield E) Ω →* (Qbar l)ˣ} (h : IsLAdicCharOf ι χ μ) (h' : IsLAdicCharOf ι χ μ') :
    μ = μ' := by
  obtain ⟨c, art, n, h1, h2, h3⟩ := h
  obtain ⟨c', art', n', h1', h2', h3'⟩ := h'
  obtain rfl := isAlgPos_unique h2 h2'
  have := isAlgClosure_real (E := E) (Ω := Ω)
  exact IsLAdicOf.eq_of_isGlobalArtin h1 h1' c c' h3 h3'

variable {π : CuspSub E a} {χ : HChar (maximalRealSubfield E)} {ι : Qbar l ≃+* ℂ}
  {r : G E Ω →* GL (Fin a) (Qbar l)} {wt : ℤ} {HT : (E →+* Qbar l) → Multiset ℤ}

/- English proof (translation)
Establish `key : ∀ {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} {rc}, IsTheRec h rc → IsRec h rc` using `fun {A w h rc} hrc => by`. Take `⟨rc', h'⟩` from `hrec A w h`. Conclude with `hrc.2 rc' h'.toLit ▸ h'`. Use `exact`. Use the proof step `{ cont := H.cont ss := H.ss pol := fun μ hμ c hc => by`.

Take `⟨μ', h1, h2⟩` from `H.pol`. Rewrite using `[isLAdicCharOf_unique hμ h1]`. Conclude with `h2 c hc`. Use `away := fun w hl A h rc hrc σ hσ => (H.away w hl A h rc (key hrc) σ hσ).wdOf_eq hl`. Use `pure := fun w hl A h => H.tempered_wdOf hl h`.

Use `weights := fun τ m hm => by`. Rewrite using `[H.weights τ, CG.HasInfChar.infChar_eq (π := CG.mk π) hm]`. Use `weights_conj := H.weights_conj`. Use `above := fun P AI T w A h O _ _ _ Bw hj =>`. Establish `K` using `H.above P AI T w A h O Bw hj`.

Use the proof step `⟨K.deRham, K.jumps, fun σ hσ hI => ⟨(K.iwahori σ hσ hI).1, fun rc hrc => (K.iwahori σ hσ hI).2 rc (key hrc)⟩, K.crys⟩ }`.
-/
theorem props_of_isGalRepOf
    (hrec : ∀ (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), ∃ rc, IsRec h rc)
    (H : IsGalRepOf π χ ι r wt HT) : Props π χ ι r wt HT := by
  have key : ∀ {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} {rc},
      IsTheRec h rc → IsRec h rc := fun {A w h rc} hrc => by
    obtain ⟨rc', h'⟩ := hrec A w h
    exact hrc.2 rc' h'.toLit ▸ h'
  exact
  { cont := H.cont
    ss := H.ss
    pol := fun μ hμ c hc => by
      obtain ⟨μ', h1, h2⟩ := H.pol
      rw [isLAdicCharOf_unique hμ h1]
      exact h2 c hc
    away := fun w hl A h rc hrc σ hσ => (H.away w hl A h rc (key hrc) σ hσ).wdOf_eq hl
    pure := fun w hl A h => H.tempered_wdOf hl h
    weights := fun τ m hm => by
      rw [H.weights τ, CG.HasInfChar.infChar_eq (π := CG.mk π) hm]
    weights_conj := H.weights_conj
    above := fun P AI T w A h O _ _ _ Bw hj =>
      have K := H.above P AI T w A h O Bw hj
      ⟨K.deRham, K.jumps, fun σ hσ hI => ⟨(K.iwahori σ hσ hI).1, fun rc hrc => (K.iwahori σ hσ hI).2 rc (key hrc)⟩,
        K.crys⟩ }

/- English proof (translation)
The claim follows from `have hc : Continuous fun g => (r g : Matrix (Fin a) (Fin a) (Qbar l)) := Units.continuous_val.comp H.cont { cont := H.cont ss := H.ss pol := let ⟨μ, h⟩ := hμ; ⟨μ, h, H.pol μ h⟩ away := fun w hl A h rc hrc σ hσ => H.away w hl A h rc (hu.isTheRec_of_isRec hrc) σ hσ ▸ isWDOf_wdOf hl …`.
-/
theorem isGalRepOf_of_props (hu : RecUnique) (hμ : ∃ μ : G (maximalRealSubfield E) Ω →* (Qbar l)ˣ, IsLAdicCharOf ι χ μ)
    (H : Props π χ ι r wt HT) : IsGalRepOf π χ ι r wt HT :=
  have hc : Continuous fun g => (r g : Matrix (Fin a) (Fin a) (Qbar l)) := Units.continuous_val.comp H.cont
  { cont := H.cont
    ss := H.ss
    pol := let ⟨μ, h⟩ := hμ; ⟨μ, h, H.pol μ h⟩
    away := fun w hl A h rc hrc σ hσ => H.away w hl A h rc (hu.isTheRec_of_isRec hrc) σ hσ ▸ isWDOf_wdOf hl ι hc
    pure := fun w hl A h => ⟨_, isWDOf_wdOf hl ι hc, H.pure w hl A h⟩
    weights := fun τ => H.weights τ _ (by exact GlobalTheory.CuspRep.ParLaws.hasInfChar_infChar (CG.mk π) _)
    weights_conj := H.weights_conj
    above := fun P AI T w A h O _ _ _ Bw hj =>
      have K := H.above P AI T w A h O Bw hj
      ⟨K.deRham, K.jumps, fun σ hσ hI => ⟨(K.iwahori σ hσ hI).1,
        fun rc hrc => (K.iwahori σ hσ hI).2 rc (hu.isTheRec_of_isRec hrc)⟩, K.crys⟩ }

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ _ l _ ι a ha π χ h1 h2` and use `let ⟨r, wt, HT, K⟩ := H E Ω l ι a ha π χ h1 h2 ⟨r, wt, HT, props_of_isGalRepOf (fun A w h => (L.1 E Ω A w h).exists) K⟩`.
-/
theorem polarizedGaloisRep_of_pair (H : GlobalTheory.Published.GaloisRepOfPolarizedPair) (L : GlobalTheory.Published.LocalLanglandsGL) :
    GlobalTheory.Published.PolarizedGaloisRepPublished := fun E Ω _ _ _ _ _ _ l _ ι a ha π χ h1 h2 =>
  let ⟨r, wt, HT, K⟩ := H E Ω l ι a ha π χ h1 h2
  ⟨r, wt, HT, props_of_isGalRepOf (fun A w h => (L.1 E Ω A w h).exists) K⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨(GalOfCusp.Model.hyp_inhabited l).1, _, _, GlobalTheory.Published.PolarizedPairModel.hyp_triv⟩`.
-/
theorem hyp_inhabited (l : ℕ) [Fact l.Prime] : Nonempty (Qbar l ≃+* ℂ) ∧
    ∃ (π : CuspSub GalOfCusp.Model.Qi 1) (χ : HChar (maximalRealSubfield GalOfCusp.Model.Qi)),
      (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.PolarizedPair π χ :=
  ⟨(GalOfCusp.Model.hyp_inhabited l).1, _, _, GlobalTheory.Published.PolarizedPairModel.hyp_triv⟩

/- English proof (translation)
Apply `Multiset.map_injective (f := fun n : ℤ => (n : ℂ)) Int.cast_injective` to reduce the goal to its premises. Rewrite using `[H.weights τ _ (by exact GlobalTheory.CuspRep.ParLaws.hasInfChar_infChar (CG.ofChar ξ) _), CG.infChar_ofChar, hn]`. Simplify using the standard rewrite rules.
-/
theorem HT_char {ξ : HChar E} {r : G E Ω →* GL (Fin 1) (Qbar l)}
    (H : Props ((CuspSub.triv E le_rfl).twist ξ) χ ι r wt HT) (τ : E →+* Qbar l) {n : ℤ}
    (hn : expo ξ (ι.toRingHom.comp τ) = n) : HT τ = {-n} := by
  apply Multiset.map_injective (f := fun n : ℤ => (n : ℂ)) Int.cast_injective
  rw [H.weights τ _ (by exact GlobalTheory.CuspRep.ParLaws.hasInfChar_infChar (CG.ofChar ξ) _), CG.infChar_ofChar, hn]
  simp

/- English proof (translation)
Use `H.pure w hl A h` as an intermediate fact. Rewrite `this` using `[(GalOfCusp.Model.isWDOf_one hl h ι).wdOf_eq hl]`. Establish `e : (WD.mk (WDRep.diag h fun _ : Fin 1 => 1)).lpTw ((wt : ℝ) / 2) = WD.mk (WDRep.diag h fun _ : Fin 1 => qPow w ((wt : ℝ) / 2))`. Rewrite using `[WD.lpTw_mk]`. Use `WD.sound ⟨.refl _ _, fun σ v => ?_, fun v => rfl⟩` and prove the remaining obligations.

Use extensionality with `i`. Simplify using `[WDRep.tw, WDRep.twist, WDRep.diag, WDRep.ofChars]`. Rewrite `this` using `[e, WD.tempered_mk, WD.tempered_diag_iff]`. Establish `h1` using `this 0`. Establish `hq : (1 : ℝ) < ((normV w : ℕ) : ℝ)` using `by exact_mod_cast one_lt_normV w`.

Rewrite `h1` using `[norm_qPow, ← Real.rpow_zero ((normV w : ℕ) : ℝ), Real.rpow_right_inj (zero_lt_one.trans hq) hq.ne']`. Conclude with `(by linarith : (wt : ℝ) = 0)` after adjusting the coercions.
-/
theorem wt_eq_zero_of_one {π : CuspSub E 1} (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal)
    {A : ValuationSubring Ω} (h : IsPlaceOver A w)
    (H : Props π χ ι (1 : G E Ω →* GL (Fin 1) (Qbar l)) wt HT) : wt = 0 := by
  have := H.pure w hl A h
  rw [(GalOfCusp.Model.isWDOf_one hl h ι).wdOf_eq hl] at this
  have e : (WD.mk (WDRep.diag h fun _ : Fin 1 => 1)).lpTw ((wt : ℝ) / 2) =
      WD.mk (WDRep.diag h fun _ : Fin 1 => qPow w ((wt : ℝ) / 2)) := by
    rw [WD.lpTw_mk]
    refine WD.sound ⟨.refl _ _, fun σ v => ?_, fun v => rfl⟩
    ext i; simp [WDRep.tw, WDRep.twist, WDRep.diag, WDRep.ofChars]
  rw [e, WD.tempered_mk, WD.tempered_diag_iff] at this
  have h1 := this 0
  have hq : (1 : ℝ) < ((normV w : ℕ) : ℝ) := by exact_mod_cast one_lt_normV w
  rw [norm_qPow, ← Real.rpow_zero ((normV w : ℕ) : ℝ), Real.rpow_right_inj (zero_lt_one.trans hq) hq.ne'] at h1
  exact_mod_cast (by linarith : (wt : ℝ) = 0)

/- English proof (translation)
Use `isAlgClosure_real (E := E) (Ω := Ω)` as an intermediate fact. Take `⟨art, ha⟩` from `H (maximalRealSubfield E) Ω`. Take `⟨μ, h1, h2⟩` from `ha.exists_isLAdicOf ι hn`. Conclude with `⟨μ, h1, art, n, ha, hn, h2⟩`.
-/
theorem exists_isLAdicCharOf (H : GlobalTheory.Published.GlobalArtinReciprocity) (ι : Qbar l ≃+* ℂ)
    {n : (maximalRealSubfield E →+* ℂ) → ℤ} (hn : IsAlgPos χ n) :
    ∃ μ : G (maximalRealSubfield E) Ω →* (Qbar l)ˣ, IsLAdicCharOf ι χ μ := by
  have := isAlgClosure_real (E := E) (Ω := Ω)
  obtain ⟨art, ha⟩ := H (maximalRealSubfield E) Ω
  obtain ⟨μ, h1, h2⟩ := ha.exists_isLAdicOf ι hn
  exact ⟨μ, h1, art, n, ha, hn, h2⟩

end GlobalTheory.GalHyps.Model

end
