import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.UnramifiedTwists.SameOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WStmtx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSatLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TLocCompC

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.GalOfCusp GlobalTheory.WeilDeligne GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.DefiniteBC
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Gu
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
/- English proof (translation)
Introduce `E _ _ _ a π`. Use `⟨fun w σ hσ B => (_root_.UpperTheory.V.Af.satake_local_of_printed_results P E a w σ).2 _ π.finPart ((_root_.UpperTheory.V.Af.local_comp_complex_of_printed_results P E a π w).2 σ hσ) B, ?_⟩` and prove the remaining obligations. Conclude with `ExLib.eventually_sat (_root_.UpperTheory.V.Af.satake_local_of_printed_results P) π.finPart π.isSmooth_finPart fun w =>`. Set `⟨⟨σ, hσ⟩, hi⟩` to `_root_.UpperTheory.V.Af.local_comp_complex_of_printed_results P E a π w`. Use the proof step `⟨σ, hi σ hσ⟩`.
-/
private theorem satLink_of (P : _root_.UpperTheory.V.Af.Hypotheses') : SatLink := by
  intro E _ _ _ a π
  refine ⟨fun w σ hσ B => (_root_.UpperTheory.V.Af.satake_local_of_printed_results P E a w σ).2 _ π.finPart ((_root_.UpperTheory.V.Af.local_comp_complex_of_printed_results P E a π w).2 σ hσ) B, ?_⟩
  exact ExLib.eventually_sat (_root_.UpperTheory.V.Af.satake_local_of_printed_results P) π.finPart π.isSmooth_finPart fun w =>
    let ⟨⟨σ, hσ⟩, hi⟩ := _root_.UpperTheory.V.Af.local_comp_complex_of_printed_results P E a π w
    ⟨σ, hi σ hσ⟩
/- English proof (translation)
Establish `h0 : Ideal.span {((l : ℕ) : 𝓞 K)} ≠ 0`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `(Fact.out : l.Prime).ne_zero` after adjusting the coercions. Conclude with `(Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)`.
-/
private theorem ev_notMem {K : Type} [Field K] [NumberField K] (l : ℕ) [Fact l.Prime] :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ((l : ℕ) : 𝓞 K) ∉ v.asIdeal := by
  have h0 : Ideal.span {((l : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  exact (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)
/- English proof (translation)
Establish `h3` using `congrArg Polynomial.roots h`. Rewrite `h3` using `[roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C]`. Establish `hq : (0 : ℝ) < (normV w : ℕ)` using `Nat.cast_pos.2 (lt_trans one_pos (one_lt_normV w))`. Establish `h4` using `Multiset.map_injective (mul_right_injective₀ (Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos hq (((n : ℝ) - 1) / 2)).ne')) (a₁ := B.map Units.val) (a₂ := B'.map Units.val) (by simpa [algSat, Multiset.map_map] using h3)`. Conclude with `Multiset.map_injective Units.val_injective h4`.
-/
private theorem algSat_inj {L : Type} [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) (n : ℕ) {B B' : Multiset ℂˣ}
    (h : ((algSat n (normV w) B).map fun b => X - C b).prod = ((algSat n (normV w) B').map fun b => X - C b).prod) :
    B = B' := by
  have h3 := congrArg Polynomial.roots h
  rw [roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C] at h3
  have hq : (0 : ℝ) < (normV w : ℕ) := Nat.cast_pos.2 (lt_trans one_pos (one_lt_normV w))
  have h4 := Multiset.map_injective
    (mul_right_injective₀ (Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos hq (((n : ℝ) - 1) / 2)).ne')) (a₁ := B.map Units.val)
    (a₂ := B'.map Units.val) (by simpa [algSat, Multiset.map_map] using h3)
  exact Multiset.map_injective Units.val_injective h4
/- English proof (translation)
Establish `contCoeff : ∀ i : ℕ, Continuous fun M : Matrix (Fin n) (Fin n) (Qbar l) => M.charpoly.coeff i` using `fun i => by`. Establish `h : (fun M : Matrix (Fin n) (Fin n) (Qbar l) => M.charpoly.coeff i) = fun M => MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2) ((Matrix.charpoly.univ (Qbar l) (Fin n)).coeff i)`. Use function extensionality and compare the values at `M`. Conclude with `(Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id _) (fun ij : Fin n × Fin n => M ij.1 ij.2) i).symm`. Rewrite using `[h]`.

Conclude with `(MvPolynomial.continuous_eval _).comp (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))`. Establish `hD` using `GlobalTheory.Published.ChebotarevDegreeOne.dense (F := L) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne' (Filter.eventually_cofinite.1 hw)`. Use extensionality with `i`. Establish `h1 : Continuous fun g : G L Ω => (r g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i` using `(contCoeff i).comp (Units.continuous_val.comp (hr.comp continuous_inv))`. Use `congrFun (Continuous.ext_on hD h1 (hf i) ?_) g` and prove the remaining obligations.

Introduce and unpack `σ ⟨v, hv, hd, A, hA, hσ⟩`. Establish `h` using `not_not.1 hv (UpperTheory.isSplitAt_of_unramified_of_inertiaDeg_eq_one L v (hE v) hd) A hA σ hσ`. Simplify using `only [h]`.
-/
private theorem eq_of_split {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ}
    [Fact l.Prime] {n : ℕ} [IsCMField L]
    (hE : ∀ w : HeightOneSpectrum (𝓞 L), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield L)) w.asIdeal)
    (r : G L Ω →* GL (Fin n) (Qbar l)) (hr : Continuous r) (f : G L Ω → (Qbar l)[X])
    (hf : ∀ j, Continuous fun g => (f g).coeff j)
    (hw : ∀ᶠ w : HeightOneSpectrum (𝓞 L) in Filter.cofinite, IsSplitAt w → ∀ A : ValuationSubring Ω, IsPlaceOver A w →
      ∀ σ : G L Ω, IsFrob A (normV w) σ → (r σ⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly = f σ) (g : G L Ω) :
    (r g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly = f g := by
  have contCoeff : ∀ i : ℕ, Continuous fun M : Matrix (Fin n) (Fin n) (Qbar l) => M.charpoly.coeff i := fun i => by
    have h : (fun M : Matrix (Fin n) (Fin n) (Qbar l) => M.charpoly.coeff i) =
        fun M => MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2) ((Matrix.charpoly.univ (Qbar l) (Fin n)).coeff i) := by
      funext M
      exact (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id _) (fun ij : Fin n × Fin n => M ij.1 ij.2) i).symm
    rw [h]
    exact (MvPolynomial.continuous_eval _).comp (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))
  have hD := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := L) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne'
    (Filter.eventually_cofinite.1 hw)
  ext i
  have h1 : Continuous fun g : G L Ω => (r g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i :=
    (contCoeff i).comp (Units.continuous_val.comp (hr.comp continuous_inv))
  refine congrFun (Continuous.ext_on hD h1 (hf i) ?_) g
  rintro σ ⟨v, hv, hd, A, hA, hσ⟩
  have h := not_not.1 hv (UpperTheory.isSplitAt_of_unramified_of_inertiaDeg_eq_one L v (hE v) hd) A hA σ hσ
  simp only [h]
/- English proof (translation)
Simplify using `[spehInf]`.
-/
private theorem spehInf_one' (m : Multiset ℂ) : spehInf 1 m = m := by
  simp [spehInf]
/- English proof (translation)
Simplify using `[satTot, GlobalTheory.WeilDeligne.qPow_zero]`.
-/
private theorem satTot_one {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (S : Fin 1 → Multiset ℂˣ) :
    satTot w (fun _ => 1) S = S 0 := by
  simp [satTot, GlobalTheory.WeilDeligne.qPow_zero]
/- English proof (translation)
Introduce `Pr hBc hTw hSum hSp hOne E Ω _ _ _ _ _ _ hE l _ ι n hn π r hc hatt U hU hsat`. Establish `hLink` using `satLink_of Pr`. Take `⟨c, a, d, hsum, P, ρ, m, σ, hP, hS, hsplit⟩` from `hBc E hE n hn U hU`. Establish `hint : ∀ i (k : Fin (d i)) τ, (m i τ).Nodup ∧ ∀ z ∈ m i τ, ∃ j : ℤ, z + (ex n (d i) k : ℂ) / 2 = j` using `fun i k τ => by`. Take `⟨lam, hl⟩` from `GlobalTheory.T.exists_algebraicWeight_of_automorphic_definiteUnitary E n hn U hU τ`.

Conclude with `(UpperTheory.speh_parameter_strings n c d (m · τ) lam (hP.weight τ lam hl)).1 i k`. Take `⟨f, hfc, hf⟩` from `hSum E Ω l ι n c a d P m (fun i => (hP.pos i).1) hP.csd hP.inf hint`. Establish `hev : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ((l : ℕ) : 𝓞 E) ∉ w.asIdeal ∧ ∃ S : Fin c → Multiset ℂˣ, ∀ i, (CG.mk (P i)).HasSat w (S i)` using `by filter_upwards [ev_notMem (K := E) l, Filter.eventually_all.2 fun i => (hLink E _ (P i)).2] with w h1 h2`. Conclude with `⟨h1, Classical.skolem.1 h2⟩`. Establish `hall` using `eq_of_split hE r hc f hfc (by filter_upwards [hsat, hatt.2, hev] with w h1 ⟨b, hb, hF⟩ ⟨hw, S, hS'⟩ hs A hA s hs'`.

Take `⟨τ, b', h2, h3, h4⟩` from `h1 hs`. Take `rfl` from `hb.unique h4`. Take `rfl` from `hSp Pr.litN E n c a d hsum w (ρ · w) (σ · w) hP.pos (fun i => (hS i w).2.2) S (fun i => ((hLink E _ (P i)).1 w _ (hP.loc i w) _).1 (hS' i)) τ (UpperTheory.building_component_uniqueness E n U hU w hs _ _ _ _ h2 (hsplit w hs)) b h3`. Conclude with `Polynomial.map_injective ι.toRingHom ι.injective (((hF A hA).2 s hs').trans (hf w hw S hS' A hA s hs').symm))`. Establish `hπ : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ S : Fin c → Multiset ℂˣ, (∀ i, (CG.mk (P i)).HasSat w (S i)) ∧ (CG.mk π).HasSat w (satTot w d S)` using `by filter_upwards [hatt.2, hev] with w ⟨b, hb, hF⟩ ⟨hw, S, hS'⟩`.

Take `⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w` from `exists_isPlaceOver Ω w`. Take `⟨s, hs⟩` from `exists_isFrob hA`. Establish `h1` using `(hF A hA).2 s hs`. Rewrite `h1` using `[hall s, hf w hw S hS' A hA s hs]`. Conclude with `⟨S, hS', algSat_inj w n h1 ▸ hb⟩`.

Take `⟨rfl, hd⟩` from `hOne Pr.litN.aut.js.1 hTw E n c hn a d P π hP.pos hπ`. Take `rfl : d = fun _ => 1` from `funext hd`. Establish `hn' : a 0 = n` using `by simpa using hsum`. Take `rfl : a = fun _ => n` from `funext fun i => by rw [Subsingleton.elim i 0, hn']`. Take `rfl : π = P 0` from `CuspSub.ext (strongMultOneC E n π (P 0) (by filter_upwards [hπ] with w ⟨S, h1, h2⟩`.

Conclude with `⟨S 0, satTot_one w S ▸ h2, h1 0⟩))`. Use `⟨fun w hw τ hτ => ?_, fun φ => ?_⟩` and prove the remaining obligations. Use `Z.Desc.irrComp E n U hsum (P 0) w (ρ 0 w) (σ 0 w) (hP.loc 0 w) (hS 0 w).2.2 ?_ τ hτ` and prove the remaining obligations. Establish `e : (σ · w) = fun _ => σ 0 w` using `funext fun i => by rw [Subsingleton.elim i 0]`. Establish `key : ∀ s s' : Fin 1 → SmIrr (GL (Fin (1 * n)) (w.adicCompletion E)), s = s' → IsCompAlong U (locU n w) ((cLoc w).comp (locU n w).subtype) (locProd (N` using `fun _ : Fin 1 => 1 * n) hsum w s) → IsCompAlong U (locU n w) ((cLoc w).comp (locU n w).subtype) (locProd (N := fun _ : Fin 1 => 1 * n) hsum w s') := by`.

Introduce and unpack `s _ rfl h`. Conclude with `h`. Conclude with `key _ _ e (hsplit w hw)`. Take `⟨lam, hl⟩` from `GlobalTheory.T.exists_algebraicWeight_of_automorphic_definiteUnitary E n hn U hU φ`. Establish `e` using `hP.weight φ lam hl`.

Rewrite `e` using `[Fin.sum_univ_one, spehInf_one']`. Conclude with `⟨lam, hl, e ▸ hP.inf 0 φ⟩`.
-/
theorem UpperTheory.V.Z.Desc.W.same_of_statement :
    _root_.UpperTheory.V.Z.Desc.W.SameOfAlt := by
  intro Pr hBc hTw hSum hSp hOne E Ω _ _ _ _ _ _ hE l _ ι n hn π r hc hatt U hU hsat
  have hLink := satLink_of Pr
  obtain ⟨c, a, d, hsum, P, ρ, m, σ, hP, hS, hsplit⟩ := hBc E hE n hn U hU
  have hint : ∀ i (k : Fin (d i)) τ, (m i τ).Nodup ∧ ∀ z ∈ m i τ, ∃ j : ℤ, z + (ex n (d i) k : ℂ) / 2 = j := fun i k τ => by
    obtain ⟨lam, hl⟩ := GlobalTheory.T.exists_algebraicWeight_of_automorphic_definiteUnitary E n hn U hU τ
    exact (UpperTheory.speh_parameter_strings n c d (m · τ) lam (hP.weight τ lam hl)).1 i k
  obtain ⟨f, hfc, hf⟩ := hSum E Ω l ι n c a d P m (fun i => (hP.pos i).1) hP.csd hP.inf hint
  have hev : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ((l : ℕ) : 𝓞 E) ∉ w.asIdeal ∧
      ∃ S : Fin c → Multiset ℂˣ, ∀ i, (CG.mk (P i)).HasSat w (S i) := by
    filter_upwards [ev_notMem (K := E) l, Filter.eventually_all.2 fun i => (hLink E _ (P i)).2] with w h1 h2
    exact ⟨h1, Classical.skolem.1 h2⟩
  have hall := eq_of_split hE r hc f hfc (by
    filter_upwards [hsat, hatt.2, hev] with w h1 ⟨b, hb, hF⟩ ⟨hw, S, hS'⟩ hs A hA s hs'
    obtain ⟨τ, b', h2, h3, h4⟩ := h1 hs
    obtain rfl := hb.unique h4
    obtain rfl := hSp Pr.litN E n c a d hsum w (ρ · w) (σ · w) hP.pos (fun i => (hS i w).2.2) S
      (fun i => ((hLink E _ (P i)).1 w _ (hP.loc i w) _).1 (hS' i)) τ
      (UpperTheory.building_component_uniqueness E n U hU w hs _ _ _ _ h2 (hsplit w hs)) b h3
    exact Polynomial.map_injective ι.toRingHom ι.injective (((hF A hA).2 s hs').trans (hf w hw S hS' A hA s hs').symm))
  have hπ : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ S : Fin c → Multiset ℂˣ,
      (∀ i, (CG.mk (P i)).HasSat w (S i)) ∧ (CG.mk π).HasSat w (satTot w d S) := by
    filter_upwards [hatt.2, hev] with w ⟨b, hb, hF⟩ ⟨hw, S, hS'⟩
    obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w := exists_isPlaceOver Ω w
    obtain ⟨s, hs⟩ := exists_isFrob hA
    have h1 := (hF A hA).2 s hs
    rw [hall s, hf w hw S hS' A hA s hs] at h1
    exact ⟨S, hS', algSat_inj w n h1 ▸ hb⟩
  obtain ⟨rfl, hd⟩ := hOne Pr.litN.aut.js.1 hTw E n c hn a d P π hP.pos hπ
  obtain rfl : d = fun _ => 1 := funext hd
  have hn' : a 0 = n := by simpa using hsum
  obtain rfl : a = fun _ => n := funext fun i => by rw [Subsingleton.elim i 0, hn']
  obtain rfl : π = P 0 := CuspSub.ext (strongMultOneC E n π (P 0) (by
    filter_upwards [hπ] with w ⟨S, h1, h2⟩
    exact ⟨S 0, satTot_one w S ▸ h2, h1 0⟩))
  refine ⟨fun w hw τ hτ => ?_, fun φ => ?_⟩
  · refine Z.Desc.irrComp E n U hsum (P 0) w (ρ 0 w) (σ 0 w) (hP.loc 0 w) (hS 0 w).2.2 ?_ τ hτ
    have e : (σ · w) = fun _ => σ 0 w := funext fun i => by rw [Subsingleton.elim i 0]
    have key : ∀ s s' : Fin 1 → SmIrr (GL (Fin (1 * n)) (w.adicCompletion E)), s = s' →
        IsCompAlong U (locU n w) ((cLoc w).comp (locU n w).subtype) (locProd (N := fun _ : Fin 1 => 1 * n) hsum w s) →
        IsCompAlong U (locU n w) ((cLoc w).comp (locU n w).subtype) (locProd (N := fun _ : Fin 1 => 1 * n) hsum w s') := by
      rintro s _ rfl h
      exact h
    exact key _ _ e (hsplit w hw)
  · obtain ⟨lam, hl⟩ := GlobalTheory.T.exists_algebraicWeight_of_automorphic_definiteUnitary E n hn U hU φ
    have e := hP.weight φ lam hl
    rw [Fin.sum_univ_one, spehInf_one'] at e
    exact ⟨lam, hl, e ▸ hP.inf 0 φ⟩
end
