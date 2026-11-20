import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SetStab
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPointOfLastCoordinateDilationOnePrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlaceProjectionZeroIntegralIffComponentsAbove
import Formalism.LocalToGlobal.Columns.RecLevelCls

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

noncomputable section

namespace GlobalTheory.Mem.Col2.DiaPt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Take `⟨s, rfl, hs⟩` from `hs`. Take `⟨c, rfl⟩` from `Ideal.Quotient.mk_surjective c`. Rewrite using `[← map_mul, DilPt.hasRes_mk_iff]`. Establish `hC : Valued.v (algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E c)) ≤ 1`. Rewrite using `[valued_algebraMap]`.

Conclude with `HeightOneSpectrum.valuation_le_one _ _`. Establish `e : (∑ j, K j * U j) - algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E (c * s)) = ∑ j, (K j - if j = r then algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E c) else 0) * U j + algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E c) * (U r - algebraMap E (P.adicComplet …`. Simplify using `only [_root_.sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Use `Valuation.map_add_lt _ (Valuation.map_sum_lt _ one_ne_zero fun j _ => ?_) ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Use `lt_of_le_of_lt (mul_le_of_le_one_right' (hU j)) ?_` and prove the remaining obligations. Use `hK j` as an intermediate fact. Distinguish the cases in `hj : j = r`.

Rewrite `this` using `[if_pos hj, DilPt.hasRes_mk_iff]`. Rewrite using `[if_pos hj]` and apply the resulting hypothesis. Rewrite `this` using `[if_neg hj]`. Rewrite using `[if_neg hj, sub_zero]`. Conclude with `DilPt.hasRes_lt_one this`.

Rewrite using `[map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' hC) hs`.
-/
theorem hasRes_row {P : HeightOneSpectrum (𝓞 E)} {n : ℕ} (r : Fin n) (K U : Fin n → P.adicCompletion E)
    {c s : 𝓞 E ⧸ P.asIdeal} (hK : ∀ j, HasRes P (K j) (if j = r then c else 0)) (hU : ∀ j, Valued.v (U j) ≤ 1)
    (hs : HasRes P (U r) s) : HasRes P (∑ j, K j * U j) (c * s) := by
  obtain ⟨s, rfl, hs⟩ := hs
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
  rw [← map_mul, DilPt.hasRes_mk_iff]
  have hC : Valued.v (algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E c)) ≤ 1 := by
    rw [valued_algebraMap]
    exact HeightOneSpectrum.valuation_le_one _ _
  have e : (∑ j, K j * U j) - algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E (c * s)) =
      ∑ j, (K j - if j = r then algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E c) else 0) * U j +
        algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E c) *
          (U r - algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E s)) := by
    simp only [_root_.sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      map_mul]
    ring
  rw [e]
  refine Valuation.map_add_lt _ (Valuation.map_sum_lt _ one_ne_zero fun j _ => ?_) ?_
  · rw [map_mul]
    refine lt_of_le_of_lt (mul_le_of_le_one_right' (hU j)) ?_
    have := hK j
    by_cases hj : j = r
    · rw [if_pos hj, DilPt.hasRes_mk_iff] at this
      rwa [if_pos hj]
    · rw [if_neg hj] at this
      rw [if_neg hj, sub_zero]
      exact DilPt.hasRes_lt_one this
  · rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' hC) hs

variable [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

/- English proof (translation)
Establish `hat : ∀ P, d.1.at P = d'.1.at P` using `fun P => by unfold Deco.at; rw [hN]`. Establish `h0 : ∀ (P : HeightOneSpectrum (𝓞 E)) (s : 𝓞 E), s ∉ P.asIdeal → Ideal.Quotient.mk P.asIdeal s ≠ 0` using `fun P s hs h => hs (Ideal.Quotient.eq_zero_iff_mem.1 h)`. Use `Subtype.ext (Deco.ext hN (funext fun P => funext fun x => ?_) (funext fun P => funext fun x => ?_))` and prove the remaining obligations. Distinguish the cases in `hx : x ∈ d'.1.at P.1`. Take `⟨s, hs, h⟩` from `(mem_locP _ _ _).1 hx`.

Use `hf P _ h` as an intermediate fact. Rewrite `this` using `[d.2.f_smul P s x (hat _ ▸ hx), d'.2.f_smul P s x hx]`. Establish `hp` using `P.1.isPrime`. Conclude with `mul_left_cancel₀ (h0 _ s hs) this`. Rewrite using `[d.2.f_off P x (hat _ ▸ hx), d'.2.f_off P x hx]`.

Distinguish the cases in `hx : x ∈ d'.1.at P.1`. Take `⟨s, hs, h⟩` from `(mem_locP _ _ _).1 hx`. Use `hbe P _ h` as an intermediate fact. Rewrite `this` using `[d.2.be_smul P s x (hat _ ▸ hx), d'.2.be_smul P s x hx]`. Establish `hp` using `P.1.isPrime`.

Use function extensionality and compare the values at `i`. Conclude with `mul_left_cancel₀ (h0 _ s hs) (congrFun this i)`. Rewrite using `[d.2.be_off P x (hat _ ▸ hx), d'.2.be_off P x hx]`.
-/
theorem decoSet_ext {d d' : DecoSet E n ST SG} (hN : d.1.N = d'.1.N) (hf : ∀ P, ∀ x ∈ d'.1.N, d.1.f P x = d'.1.f P x)
    (hbe : ∀ w, ∀ x ∈ d'.1.N, d.1.be w x = d'.1.be w x) : d = d' := by
  have hat : ∀ P, d.1.at P = d'.1.at P := fun P => by unfold Deco.at; rw [hN]
  have h0 : ∀ (P : HeightOneSpectrum (𝓞 E)) (s : 𝓞 E), s ∉ P.asIdeal → Ideal.Quotient.mk P.asIdeal s ≠ 0 :=
    fun P s hs h => hs (Ideal.Quotient.eq_zero_iff_mem.1 h)
  refine Subtype.ext (Deco.ext hN (funext fun P => funext fun x => ?_) (funext fun P => funext fun x => ?_))
  · by_cases hx : x ∈ d'.1.at P.1
    · obtain ⟨s, hs, h⟩ := (mem_locP _ _ _).1 hx
      have := hf P _ h
      rw [d.2.f_smul P s x (hat _ ▸ hx), d'.2.f_smul P s x hx] at this
      have hp := P.1.isPrime
      exact mul_left_cancel₀ (h0 _ s hs) this
    · rw [d.2.f_off P x (hat _ ▸ hx), d'.2.f_off P x hx]
  · by_cases hx : x ∈ d'.1.at P.1
    · obtain ⟨s, hs, h⟩ := (mem_locP _ _ _).1 hx
      have := hbe P _ h
      rw [d.2.be_smul P s x (hat _ ▸ hx), d'.2.be_smul P s x hx] at this
      have hp := P.1.isPrime
      funext i
      exact mul_left_cancel₀ (h0 _ s hs) (congrFun this i)
    · rw [d.2.be_off P x (hat _ ▸ hx), d'.2.be_off P x hx]

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ hc n _ ST SG Q g k p c h ⟨p₀, hk, hk0⟩ htriv hrow`. Establish `hg : g ∈ UAd hc n`. Use `mul_mem h.uni (inv_mem hk.uni)` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel_right]`. Conclude with `this`.

Establish `hkc` using `hk.lat`. Rewrite `hkc` using `[hk0]`. Establish `hkI : ∀ z : Fin n → AfE F E, (∀ i, z i ∈ RInt F E) ↔ ∀ i, (((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ z) i ∈ RInt F E` using `fun z => (mem_latS_std z).symm.trans ((hkc z).trans (mem_latS_std _))`. Establish `hN : Formalism.UG.CS.globLat g (Formalism.L2.Col.stdLat E n) = p.deco.1.N`. Rewrite using `[← Formalism.UG.P.global_lattice_one_holds F E (Fin n) p.deco.1.N (Module.Finite.iff_fg.2 p.deco.2.lat.fg) p.deco.2.lat.span_eq_top]`.

Use extensionality with `w`. Use `(mem_globLat g w).trans ((hkI _).trans ?_)` and prove the remaining obligations. Establish `e : ((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ Formalism.L2.Col.pullV g w = GlobalTheory.Mem.Col2.pullV (g * k) w` using `(DilPt.pullbackVector_mul_right g k w).symm`. Rewrite using `[e]`. Use `(mem_latS_std _).symm.trans ((h.lat _).symm.trans ?_)` and prove the remaining obligations.

Use `show _ ↔ ((1⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ _ ∈ Formalism.L2.Herm.hatL (F := F) p.deco.1.N`. Rewrite using `[inv_one, Units.val_one, Matrix.one_mulVec]`. Establish `hone : ∀ w ∈ SG, ∀ i j, adAt F w ((k⁻¹ : GL (Fin n) (AfE F E)).1 i j) = if j = i then 1 else 0`. Introduce `w hw i j`. Establish `h1 : bc (prV (E` using `E) (w.under (𝓞 F))) k⁻¹ = 1 := by rw [map_inv, htriv w hw, inv_one]`.

Establish `h2 : prV (E` using `E) (w.under (𝓞 F)) ((k⁻¹ : GL (Fin n) (AfE F E)).1 i j) = if i = j then 1 else 0 := by`. Use `congrArg (fun x : GL (Fin n) _ => x.1 i j) h1` as an intermediate fact. Simplify using `only [Units.val_one, Matrix.one_apply] at this`. Conclude with `this`. Establish `h3 : prV (E` using `E) (w.under (𝓞 F)) ((k⁻¹ : GL (Fin n) (AfE F E)).1 i j - if j = i then 1 else 0) = 0 := by`.

Rewrite using `[map_sub, h2]`. Distinguish the cases in `hij : i = j`. Simplify using `[hij]`. Simplify using `[hij, Ne.symm hij]`. Establish `h4` using `(GlobalTheory.Mem.Col2.AdComp.prV_zero_int_iff F E _ _).1.1 h3 w rfl`.

Rewrite `h4` using `[map_sub, sub_eq_zero]`. Rewrite using `[h4]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hraw` using `rlc_decoOf_val hc n ST SG hg`. Establish `hint : ∀ x ∈ p.deco.1.N, ∀ i, GlobalTheory.Mem.Col2.pullV g x i ∈ RInt F E` using `fun x hx => (mem_globLat g x).1 (hN ▸ hx)`.

Use `⟨hg, decoSet_ext ?_ (fun P x hx => ?_) fun w x hx => ?_⟩` and prove the remaining obligations. Use `show (decoOf ST SG g).1.N = _`. Rewrite using `[hraw]`. Conclude with `hN`. Use `show (c P).1 * (decoOf ST SG g).1.f P x = _`.

Establish `hl : (lastIdx n).1 + 1 = n` using `Nat.sub_add_cancel (Nat.pos_of_ne_zero (NeZero.ne n))`. Establish `h1` using `h.f P x hx _ hl`. Rewrite `h1` using `[DilPt.pullbackVector_mul_right]`. Simplify using `only [Matrix.mulVec, dotProduct, map_sum, map_mul] at h1`. Establish `h2` using `hasRes_row (lastIdx n) _ (fun j => adAt F P.1 (GlobalTheory.Mem.Col2.pullV g x j)) (fun j => hrow P _ j hl) (fun j => (mem_rInt_iff F E _).1 (hint x hx j) P.1) (PtExist.hasRes_redA P.1 (hint x hx _))`.

Rewrite using `[hraw]`. Simplify using `only [decoRaw]`. Rewrite using `[if_pos (le_locP _ _ (hN ▸ hx))]`. Conclude with `h2.unique h1`. Use `show (decoOf ST SG g).1.be w x = _`.

Rewrite using `[hraw]`. Simplify using `only [decoRaw]`. Rewrite using `[if_pos (le_locP _ _ (hN ▸ hx))]`. Use function extensionality and compare the values at `i`. Establish `h1` using `h.be w x hx i`.

Rewrite `h1` using `[DilPt.pullbackVector_mul_right]`. Simplify using `only [Matrix.mulVec, dotProduct, map_sum, map_mul, hone w.1 w.2, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1`. Conclude with `(PtExist.hasRes_redA w.1 (hint x hx i)).unique h1`.
-/
theorem decoOf_dia_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (g k : GL (Fin n) (AfE F E)) (p : DecoF E n ST SG Q) (c : DiaG E ST), IsPtOf hc (g * k) p → (∃ p₀ : DecoF E n ∅ ∅ ∅, IsPtOf hc k p₀ ∧ p₀.deco.1.N = Formalism.L2.Col.stdLat E n) → (∀ w ∈ SG, bc (prV (E := E) (w.under (𝓞 F))) k = 1) → (∀ (P : ST) (r j : Fin n), r.1 + 1 = n → HasRes P.1 (adAt F P.1 ((k⁻¹ : GL (Fin n) (AfE F E)).1 r j)) (if j = r then (c P : 𝓞 E ⧸ P.1.asIdeal) else 0)) → g ∈ UAd hc n ∧ (decoOf ST SG g).dia c = p.deco := by
  intro F E _ _ _ _ _ _ hc n _ ST SG Q g k p c h ⟨p₀, hk, hk0⟩ htriv hrow
  classical
  have hg : g ∈ UAd hc n := by
    have := mul_mem h.uni (inv_mem hk.uni)
    rw [mul_inv_cancel_right] at this
    exact this
  have hkc := hk.lat
  rw [hk0] at hkc
  have hkI : ∀ z : Fin n → AfE F E, (∀ i, z i ∈ RInt F E) ↔
      ∀ i, (((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ z) i ∈ RInt F E :=
    fun z => (mem_latS_std z).symm.trans ((hkc z).trans (mem_latS_std _))
  have hN : Formalism.UG.CS.globLat g (Formalism.L2.Col.stdLat E n) = p.deco.1.N := by
    rw [← Formalism.UG.P.global_lattice_one_holds F E (Fin n) p.deco.1.N (Module.Finite.iff_fg.2 p.deco.2.lat.fg) p.deco.2.lat.span_eq_top]
    ext w
    refine (mem_globLat g w).trans ((hkI _).trans ?_)
    have e : ((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ Formalism.L2.Col.pullV g w =
        GlobalTheory.Mem.Col2.pullV (g * k) w := (DilPt.pullbackVector_mul_right g k w).symm
    rw [e]
    refine (mem_latS_std _).symm.trans ((h.lat _).symm.trans ?_)
    show _ ↔ ((1⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ _ ∈ Formalism.L2.Herm.hatL (F := F) p.deco.1.N
    rw [inv_one, Units.val_one, Matrix.one_mulVec]
  have hone : ∀ w ∈ SG, ∀ i j, adAt F w ((k⁻¹ : GL (Fin n) (AfE F E)).1 i j) = if j = i then 1 else 0 := by
    intro w hw i j
    have h1 : bc (prV (E := E) (w.under (𝓞 F))) k⁻¹ = 1 := by rw [map_inv, htriv w hw, inv_one]
    have h2 : prV (E := E) (w.under (𝓞 F)) ((k⁻¹ : GL (Fin n) (AfE F E)).1 i j) = if i = j then 1 else 0 := by
      have := congrArg (fun x : GL (Fin n) _ => x.1 i j) h1
      simp only [Units.val_one, Matrix.one_apply] at this
      exact this
    have h3 : prV (E := E) (w.under (𝓞 F)) ((k⁻¹ : GL (Fin n) (AfE F E)).1 i j - if j = i then 1 else 0) = 0 := by
      rw [map_sub, h2]
      by_cases hij : i = j
      · simp [hij]
      · simp [hij, Ne.symm hij]
    have h4 := (GlobalTheory.Mem.Col2.AdComp.prV_zero_int_iff F E _ _).1.1 h3 w rfl
    rw [map_sub, sub_eq_zero] at h4
    rw [h4]
    split_ifs <;> simp
  have hraw := rlc_decoOf_val hc n ST SG hg
  have hint : ∀ x ∈ p.deco.1.N, ∀ i, GlobalTheory.Mem.Col2.pullV g x i ∈ RInt F E := fun x hx =>
    (mem_globLat g x).1 (hN ▸ hx)
  refine ⟨hg, decoSet_ext ?_ (fun P x hx => ?_) fun w x hx => ?_⟩
  · show (decoOf ST SG g).1.N = _
    rw [hraw]
    exact hN
  · show (c P).1 * (decoOf ST SG g).1.f P x = _
    have hl : (lastIdx n).1 + 1 = n := Nat.sub_add_cancel (Nat.pos_of_ne_zero (NeZero.ne n))
    have h1 := h.f P x hx _ hl
    rw [DilPt.pullbackVector_mul_right] at h1
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul] at h1
    have h2 := hasRes_row (lastIdx n) _ (fun j => adAt F P.1 (GlobalTheory.Mem.Col2.pullV g x j)) (fun j => hrow P _ j hl)
      (fun j => (mem_rInt_iff F E _).1 (hint x hx j) P.1) (PtExist.hasRes_redA P.1 (hint x hx _))
    rw [hraw]
    simp only [decoRaw]
    rw [if_pos (le_locP _ _ (hN ▸ hx))]
    exact h2.unique h1
  · show (decoOf ST SG g).1.be w x = _
    rw [hraw]
    simp only [decoRaw]
    rw [if_pos (le_locP _ _ (hN ▸ hx))]
    funext i
    have h1 := h.be w x hx i
    rw [DilPt.pullbackVector_mul_right] at h1
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, hone w.1 w.2, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at h1
    exact (PtExist.hasRes_redA w.1 (hint x hx i)).unique h1

end GlobalTheory.Mem.Col2.DiaPt
