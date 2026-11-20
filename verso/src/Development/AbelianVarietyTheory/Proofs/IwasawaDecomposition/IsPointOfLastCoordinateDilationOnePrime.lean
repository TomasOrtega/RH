import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Matrix

noncomputable section

namespace GlobalTheory.Mem.Col2.DilPt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨r', hr', h⟩`. Establish `hm : r' - r ∈ P.asIdeal` using `Ideal.Quotient.eq.1 hr'`. Establish `h2 : Valued.v (algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E (r' - r))) < 1`. Rewrite using `[valued_algebraMap]`.

Conclude with `(HeightOneSpectrum.valuation_lt_one_iff_mem _ _).2 hm`. Establish `e : z - algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E r) = (z - algebraMap E _ (algebraMap (𝓞 E) E r')) + algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E (r' - r))`. Simplify using `only [map_sub]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Conclude with `Valuation.map_add_lt _ h h2`. Introduce `h`. Conclude with `⟨r, rfl, h⟩`.
-/
theorem hasRes_mk_iff {P : HeightOneSpectrum (𝓞 E)} {z : P.adicCompletion E} (r : 𝓞 E) :
    HasRes P z (Ideal.Quotient.mk P.asIdeal r) ↔ Valued.v (z - algebraMap E _ (algebraMap (𝓞 E) E r)) < 1 := by
  constructor
  · rintro ⟨r', hr', h⟩
    have hm : r' - r ∈ P.asIdeal := Ideal.Quotient.eq.1 hr'
    have h2 : Valued.v (algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E (r' - r))) < 1 := by
      rw [valued_algebraMap]
      exact (HeightOneSpectrum.valuation_lt_one_iff_mem _ _).2 hm
    have e : z - algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E r) =
        (z - algebraMap E _ (algebraMap (𝓞 E) E r')) + algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E (r' - r)) := by
      simp only [map_sub]
      ring
    rw [e]
    exact Valuation.map_add_lt _ h h2
  · intro h
    exact ⟨r, rfl, h⟩

/- English proof (translation)
Take `⟨r, -, hr⟩` from `h`. Establish `h1 : Valued.v (algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E r)) ≤ 1`. Rewrite using `[valued_algebraMap]`. Conclude with `HeightOneSpectrum.valuation_le_one _ _`. Establish `e : z = (z - algebraMap E _ (algebraMap (𝓞 E) E r)) + algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E r)`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `Valuation.map_add_le _ hr.le h1`.
-/
theorem hasRes_le_one {P : HeightOneSpectrum (𝓞 E)} {z : P.adicCompletion E} {c : 𝓞 E ⧸ P.asIdeal}
    (h : HasRes P z c) : Valued.v z ≤ 1 := by
  obtain ⟨r, -, hr⟩ := h
  have h1 : Valued.v (algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E r)) ≤ 1 := by
    rw [valued_algebraMap]
    exact HeightOneSpectrum.valuation_le_one _ _
  have e : z = (z - algebraMap E _ (algebraMap (𝓞 E) E r)) + algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E r) := by
    ring
  rw [e]
  exact Valuation.map_add_le _ hr.le h1

/- English proof (translation)
Use `(hasRes_mk_iff (P := P) (z := z) 0).1 (by simpa using h)` as an intermediate fact. Simplify using `using this`.
-/
theorem hasRes_lt_one {P : HeightOneSpectrum (𝓞 E)} {z : P.adicCompletion E} (h : HasRes P z 0) : Valued.v z < 1 := by
  have := (hasRes_mk_iff (P := P) (z := z) 0).1 (by simpa using h)
  simpa using this

/- English proof (translation)
Establish `e : (∑ j, Ki j * ∑ l, D j l * U l) - C * ∑ j, Ki j * U j = ∑ j, Ki j * ((∑ l, D j l * U l) - C * U j)`. Rewrite using `[Finset.mul_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Use `Valuation.map_sum_lt _ one_ne_zero fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Distinguish the cases in `hj : j = r`. Substitute `hj` using the available equality. Establish `e2 : (∑ l, D j l * U l) - C * U j = ∑ l, (D j l - if l = j then C else 0) * U l`.

Simplify using `only [_root_.sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Rewrite using `[e2]`. Use `lt_of_le_of_lt (mul_le_of_le_one_left' (hK j)) ?_` and prove the remaining obligations. Conclude with `Valuation.map_sum_lt _ one_ne_zero fun l _ => by`. Rewrite using `[map_mul]`.

Conclude with `lt_of_le_of_lt (mul_le_of_le_one_right' (hU l)) (hDr l)`. Use `lt_of_le_of_lt (mul_le_of_le_one_right' ?_) (hK' j hj)` and prove the remaining obligations. Use `Valuation.map_sub _ _ _ |>.trans (max_le ?_ ?_)` and prove the remaining obligations. Conclude with `Valuation.map_sum_le _ fun l _ => by`. Rewrite using `[map_mul]`.

Conclude with `mul_le_one' (hD j l) (hU l)`. Rewrite using `[map_mul]`. Conclude with `mul_le_one' hC (hU j)`.
-/
theorem last_sub_lt {P : HeightOneSpectrum (𝓞 E)} {n : ℕ} (r : Fin n) (Ki : Fin n → P.adicCompletion E)
    (D : Fin n → Fin n → P.adicCompletion E) (U : Fin n → P.adicCompletion E) (C : P.adicCompletion E)
    (hK : ∀ j, Valued.v (Ki j) ≤ 1) (hK' : ∀ j, j ≠ r → Valued.v (Ki j) < 1)
    (hD : ∀ j l, Valued.v (D j l) ≤ 1) (hDr : ∀ l, Valued.v (D r l - if l = r then C else 0) < 1)
    (hU : ∀ l, Valued.v (U l) ≤ 1) (hC : Valued.v C ≤ 1) :
    Valued.v ((∑ j, Ki j * ∑ l, D j l * U l) - C * ∑ j, Ki j * U j) < 1 := by
  have e : (∑ j, Ki j * ∑ l, D j l * U l) - C * ∑ j, Ki j * U j =
      ∑ j, Ki j * ((∑ l, D j l * U l) - C * U j) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e]
  refine Valuation.map_sum_lt _ one_ne_zero fun j _ => ?_
  rw [map_mul]
  by_cases hj : j = r
  · subst hj
    have e2 : (∑ l, D j l * U l) - C * U j = ∑ l, (D j l - if l = j then C else 0) * U l := by
      simp only [_root_.sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [e2]
    refine lt_of_le_of_lt (mul_le_of_le_one_left' (hK j)) ?_
    exact Valuation.map_sum_lt _ one_ne_zero fun l _ => by
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' (hU l)) (hDr l)
  · refine lt_of_le_of_lt (mul_le_of_le_one_right' ?_) (hK' j hj)
    refine Valuation.map_sub _ _ _ |>.trans (max_le ?_ ?_)
    · exact Valuation.map_sum_le _ fun l _ => by
        rw [map_mul]
        exact mul_le_one' (hD j l) (hU l)
    · rw [map_mul]
      exact mul_le_one' hC (hU j)

/- English proof (translation)
Unfold `GlobalTheory.Mem.Col2.pullV`. Rewrite using `[_root_.mul_inv_rev, _root_.mul_inv_rev, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]`.
-/
theorem pullbackVector_triple_mul {n : ℕ} (y δ k : GL (Fin n) (AfE F E)) (x : Sp E n) :
    GlobalTheory.Mem.Col2.pullV (y * δ * k) x =
      ((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ
        (((δ⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ GlobalTheory.Mem.Col2.pullV y x) := by
  unfold GlobalTheory.Mem.Col2.pullV
  rw [_root_.mul_inv_rev, _root_.mul_inv_rev, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

/- English proof (translation)
Unfold `GlobalTheory.Mem.Col2.pullV`. Rewrite using `[_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]`.
-/
theorem pullbackVector_mul_right {n : ℕ} (y k : GL (Fin n) (AfE F E)) (x : Sp E n) :
    GlobalTheory.Mem.Col2.pullV (y * k) x =
      ((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ GlobalTheory.Mem.Col2.pullV y x := by
  unfold GlobalTheory.Mem.Col2.pullV
  rw [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]

/- English proof (translation)
Rewrite using `[pullbackVector_triple_mul, pullbackVector_mul_right]`. Simplify using `only [Matrix.mulVec, dotProduct, map_sum, map_mul, ht, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]`.
-/
theorem adAt_pullV_triv {n : ℕ} (y δ k : GL (Fin n) (AfE F E)) (w : HeightOneSpectrum (𝓞 E))
    (ht : ∀ i j, adAt F w ((δ⁻¹ : GL (Fin n) (AfE F E)).1 i j) = if i = j then 1 else 0) (x : Sp E n) (i : Fin n) :
    adAt F w (GlobalTheory.Mem.Col2.pullV (y * δ * k) x i) = adAt F w (GlobalTheory.Mem.Col2.pullV (y * k) x i) := by
  rw [pullbackVector_triple_mul, pullbackVector_mul_right]
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, ht, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

/- English proof (translation)
Establish `h1 : ((δ⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F w) = 1`. Use extensionality with `a b`. Rewrite using `[Matrix.map_apply, ht, Matrix.one_apply]`. Establish `h2 : (δ : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F w) = 1`. Establish `e : (δ : Matrix (Fin n) (Fin n) (AfE F E)) * ((δ⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) = 1`.

Rewrite using `[← Units.val_mul, mul_inv_cancel, Units.val_one]`. Use `congrArg (fun M : Matrix (Fin n) (Fin n) (AfE F E) => M.map (adAt F w)) e` as an intermediate fact. Simplify using `only [Matrix.map_mul, h1, mul_one, Matrix.map_one (adAt F w) (map_zero _) (map_one _)] at this`. Conclude with `this`. Establish `e : ((y * δ * k : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F w) = ((y * k : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F w)`.

Simplify using `only [Units.val_mul, Matrix.map_mul, h2, mul_one]`. Conclude with `congrArg (fun M => M i j) e`.
-/
theorem adeleComponentAt_triple_mul_dilation_trivial {n : ℕ} (y δ k : GL (Fin n) (AfE F E)) (w : HeightOneSpectrum (𝓞 E))
    (ht : ∀ i j, adAt F w ((δ⁻¹ : GL (Fin n) (AfE F E)).1 i j) = if i = j then 1 else 0) (i j : Fin n) :
    adAt F w ((y * δ * k : GL (Fin n) (AfE F E)).1 i j) = adAt F w ((y * k : GL (Fin n) (AfE F E)).1 i j) := by
  have h1 : ((δ⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F w) = 1 := by
    ext a b
    rw [Matrix.map_apply, ht, Matrix.one_apply]
  have h2 : (δ : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F w) = 1 := by
    have e : (δ : Matrix (Fin n) (Fin n) (AfE F E)) * ((δ⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have := congrArg (fun M : Matrix (Fin n) (Fin n) (AfE F E) => M.map (adAt F w)) e
    simp only [Matrix.map_mul, h1, mul_one, Matrix.map_one (adAt F w) (map_zero _) (map_one _)] at this
    exact this
  have e : ((y * δ * k : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F w) =
      ((y * k : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F w) := by
    simp only [Units.val_mul, Matrix.map_mul, h2, mul_one]
  exact congrArg (fun M => M i j) e

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ hc n ST SG Q y δ k p p' P c b h hk hδ hkc hδi hδi' htriv hkr hδr hdeco hfr`. Establish `hy : y ∈ Formalism.L2.Herm.UstdAf hc n`. Use `mul_mem h.uni (inv_mem hk)` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel_right]`. Then use the resulting hypothesis. Establish `hkI : ∀ z : Fin n → AfE F E, (∀ i, z i ∈ RInt F E) ↔ ∀ i, (((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ z) i ∈ RInt F E` using `fun z => (mem_latS_std z).symm.trans ((hkc z).trans (mem_latS_std _))`.

Establish `hδI : ∀ z : Fin n → AfE F E, (∀ i, z i ∈ RInt F E) ↔ ∀ i, (((δ⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ z) i ∈ RInt F E`. Introduce `z`. Prove the components needed by the constructor for the conclusion. Introduce `hz i`. Conclude with `PtExist.mulVec_int hδi' hz i`.

Introduce `hz i`. Use `PtExist.mulVec_int hδi hz i` as an intermediate fact. Rewrite `this` using `[Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]`. Then use the resulting hypothesis. Establish `hN : p'.deco.1.N = p.deco.1.N` using `by rw [hdeco]; rfl`. Establish `hbe : p'.deco.1.be = p.deco.1.be` using `by rw [hdeco]; rfl`.

Establish `hf : ∀ (P' : ST) (x : Sp E n), p'.deco.1.f P' x = ((Pi.mulSingle (M` using `fun Q : ST => (𝓞 E ⧸ Q.1.asIdeal)ˣ) P c P' : (𝓞 E ⧸ P'.1.asIdeal)ˣ) : 𝓞 E ⧸ P'.1.asIdeal) * p.deco.1.f P' x := by`. Introduce `P' x`. Rewrite using `[hdeco]`. Both sides reduce to the same expression. Establish `hu : ∀ x ∈ p.deco.1.N, ∀ l, GlobalTheory.Mem.Col2.pullV y x l ∈ RInt F E`.

Introduce `x hx`. Use `(hkI _).2 ?_` and prove the remaining obligations. Rewrite using `[← pullbackVector_mul_right]`. Conclude with `(mem_latS_std _).1 ((h.lat _).1 (Submodule.subset_span ⟨x, hx, rfl⟩))`. Use `⟨mul_mem (mul_mem hy hδ) hk, fun z => ?_, fun P' x hx i hi => ?_, fun w x hx i => ?_, fun P' i j => ?_⟩` and prove the remaining obligations.

Rewrite using `[hN]`. Use `(h.lat z).trans ((mem_latS_std _).trans (Iff.trans ?_ (mem_latS_std _).symm))` and prove the remaining obligations. Establish `e1 : ((y * k : GL (Fin n) (AfE F E))⁻¹ : GL (Fin n) (AfE F E)).1 *ᵥ z = ((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ (((y⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ z)`. Rewrite using `[_root_.mul_inv_rev, Units.val_mul, Matrix.mulVec_mulVec]`. Establish `e2 : ((y * δ * k : GL (Fin n) (AfE F E))⁻¹ : GL (Fin n) (AfE F E)).1 *ᵥ z = ((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ (((δ⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ (((y⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E) …`.

Rewrite using `[_root_.mul_inv_rev, _root_.mul_inv_rev, Units.val_mul, Units.val_mul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]`. Rewrite using `[e1, e2]`. Conclude with `(hkI _).symm.trans ((hδI _).trans (hkI _))`. Rewrite `hx` using `[hN]`. Establish `hv` using `h.f P' x hx i hi`.

Rewrite using `[hf]`. Distinguish the cases in `hPP : P' = P`. Substitute `hPP` using the available equality. Rewrite using `[Pi.mulSingle_eq_same]`. Take `⟨s, hs, hv'⟩` from `hv`.

Take `⟨cr, hcr⟩` from `Ideal.Quotient.mk_surjective (c : 𝓞 E ⧸ P'.1.asIdeal)`. Rewrite using `[← hs, ← hcr, ← map_mul, hasRes_mk_iff]`. Establish `hint : ∀ a ∈ RInt F E, Valued.v (adAt F P'.1 a) ≤ 1` using `fun a ha => (mem_rInt_iff F E a).1 ha P'.1`. Establish `hCle : Valued.v (algebraMap E (P'.1.adicCompletion E) (algebraMap (𝓞 E) E cr)) ≤ 1`. Rewrite using `[valued_algebraMap]`.

Conclude with `HeightOneSpectrum.valuation_le_one _ _`. Establish `key` using `last_sub_lt i (fun j => adAt F P'.1 ((k⁻¹ : GL (Fin n) (AfE F E)).1 i j)) (fun j l => adAt F P'.1 ((δ⁻¹ : GL (Fin n) (AfE F E)).1 j l)) (fun l => adAt F P'.1 (GlobalTheory.Mem.Col2.pullV y x l)) (algebraMap E _ (algebraMap (𝓞 E) E cr)) (fun j => hasRes_le_one (hkr i j hi)) (fun j …`. Use `hkr i j hi` as an intermediate fact. Rewrite `this` using `[if_neg hj]`. Conclude with `hasRes_lt_one this)`.

Use the proof step `(fun j l => hint _ (hδi' j l))`. Use the proof step `(fun l => by`. Use `hδr i l hi` as an intermediate fact. Distinguish the cases in `hl : l = i`. Rewrite `this` using `[if_pos hl, ← hcr, hasRes_mk_iff]`.

Rewrite using `[if_pos hl]`. Conclude with `this`. Rewrite `this` using `[if_neg hl]`. Rewrite using `[if_neg hl, sub_zero]`. Conclude with `hasRes_lt_one this)`.

Use the proof step `(fun l => hint _ (hu x hx l)) hCle`. Rewrite `hv'` using `[pullbackVector_mul_right]`. Rewrite using `[pullbackVector_triple_mul]`. Simplify using `only [Matrix.mulVec, dotProduct, map_sum, map_mul] at hv' key ⊢`. Establish `e : (∑ j, adAt F P'.1 ((k⁻¹ : GL (Fin n) (AfE F E)).1 i j) * ∑ l, adAt F P'.1 ((δ⁻¹ : GL (Fin n) (AfE F E)).1 j l) * adAt F P'.1 (GlobalTheory.Mem.Col2.pullV y x l)) - algebraMap E (P'.1.adicCompletion E) (algebraMap (𝓞 E) E cr) * algebraMap E (P'.1.adicCompletion E) (algebraMap …` using `by ring`.

Rewrite using `[e]`. Use `Valuation.map_add_lt _ key ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' hCle) hv'`. Rewrite using `[Pi.mulSingle_eq_of_ne hPP, Units.val_one, one_mul, adAt_pullV_triv y δ k P'.1 (htriv P'.1 (Or.inr (Or.inr ⟨P'.2, fun e => hPP (Subtype.ext e)⟩))) x i]`.

Conclude with `hv`. Rewrite `hx` using `[hN]`. Rewrite using `[hbe, adAt_pullV_triv y δ k w.1 (htriv w.1 (Or.inl w.2)) x i]`. Conclude with `h.be w x hx i`. Rewrite using `[hfr, adeleComponentAt_triple_mul_dilation_trivial y δ k P'.1 (htriv P'.1 (Or.inr (Or.inl P'.2))) i j]`.

Conclude with `h.fr P' i j`.
-/
theorem isPointOf_last_coordinate_dilation_one_prime_alt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (y δ k : GL (Fin n) (AfE F E)) (p p' : DecoF E n ST SG Q) (P : ST) (c : (𝓞 E ⧸ P.1.asIdeal)ˣ) (b : 𝓞 E ⧸ P.1.asIdeal), IsPtOf hc (y * k) p → k ∈ Formalism.L2.Herm.UstdAf hc n → δ ∈ Formalism.L2.Herm.UstdAf hc n → Formalism.L2.Herm.Carries k (Formalism.L2.Col.stdLat E n) (Formalism.L2.Col.stdLat E n) → (∀ i j, δ.1 i j ∈ RInt F E) → (∀ i j, (δ⁻¹).1 i j ∈ RInt F E) → (∀ w : HeightOneSpectrum (𝓞 E), (w ∈ SG ∨ w ∈ Q ∨ (w ∈ ST ∧ w ≠ P.1)) → ∀ i j, adAt F w ((δ⁻¹).1 i j) = if i = j then 1 else 0) → (∀ r j : Fin n, r.1 + 1 = n → HasRes P.1 (adAt F P.1 ((k⁻¹).1 r j)) (if j = r then b else 0)) → (∀ r j : Fin n, r.1 + 1 = n → HasRes P.1 (adAt F P.1 ((δ⁻¹).1 r j)) (if j = r then (c : 𝓞 E ⧸ P.1.asIdeal) else 0)) → p'.deco = DecoSet.dia1 P c p.deco → p'.fr = p.fr → IsPtOf hc (y * δ * k) p' := by
  intro F E _ _ _ _ _ _ hc n ST SG Q y δ k p p' P c b h hk hδ hkc hδi hδi' htriv hkr hδr hdeco hfr
  classical
  have hy : y ∈ Formalism.L2.Herm.UstdAf hc n := by
    have := mul_mem h.uni (inv_mem hk)
    rwa [mul_inv_cancel_right] at this
  have hkI : ∀ z : Fin n → AfE F E, (∀ i, z i ∈ RInt F E) ↔
      ∀ i, (((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ z) i ∈ RInt F E :=
    fun z => (mem_latS_std z).symm.trans ((hkc z).trans (mem_latS_std _))
  have hδI : ∀ z : Fin n → AfE F E, (∀ i, z i ∈ RInt F E) ↔
      ∀ i, (((δ⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ z) i ∈ RInt F E := by
    intro z
    constructor
    · intro hz i
      exact PtExist.mulVec_int hδi' hz i
    · intro hz i
      have := PtExist.mulVec_int hδi hz i
      rwa [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec] at this
  have hN : p'.deco.1.N = p.deco.1.N := by rw [hdeco]; rfl
  have hbe : p'.deco.1.be = p.deco.1.be := by rw [hdeco]; rfl
  have hf : ∀ (P' : ST) (x : Sp E n), p'.deco.1.f P' x =
      ((Pi.mulSingle (M := fun Q : ST => (𝓞 E ⧸ Q.1.asIdeal)ˣ) P c P' : (𝓞 E ⧸ P'.1.asIdeal)ˣ) : 𝓞 E ⧸ P'.1.asIdeal) * p.deco.1.f P' x := by
    intro P' x
    rw [hdeco]
    rfl
  have hu : ∀ x ∈ p.deco.1.N, ∀ l, GlobalTheory.Mem.Col2.pullV y x l ∈ RInt F E := by
    intro x hx
    refine (hkI _).2 ?_
    rw [← pullbackVector_mul_right]
    exact (mem_latS_std _).1 ((h.lat _).1 (Submodule.subset_span ⟨x, hx, rfl⟩))
  refine ⟨mul_mem (mul_mem hy hδ) hk, fun z => ?_, fun P' x hx i hi => ?_, fun w x hx i => ?_, fun P' i j => ?_⟩
  · rw [hN]
    refine (h.lat z).trans ((mem_latS_std _).trans (Iff.trans ?_ (mem_latS_std _).symm))
    have e1 : ((y * k : GL (Fin n) (AfE F E))⁻¹ : GL (Fin n) (AfE F E)).1 *ᵥ z =
        ((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ
          (((y⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ z) := by
      rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mulVec_mulVec]
    have e2 : ((y * δ * k : GL (Fin n) (AfE F E))⁻¹ : GL (Fin n) (AfE F E)).1 *ᵥ z =
        ((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ
          (((δ⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ
            (((y⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ z)) := by
      rw [_root_.mul_inv_rev, _root_.mul_inv_rev, Units.val_mul, Units.val_mul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        Matrix.mul_assoc]
    rw [e1, e2]
    exact (hkI _).symm.trans ((hδI _).trans (hkI _))
  · rw [hN] at hx
    have hv := h.f P' x hx i hi
    rw [hf]
    by_cases hPP : P' = P
    · subst hPP
      rw [Pi.mulSingle_eq_same]
      obtain ⟨s, hs, hv'⟩ := hv
      obtain ⟨cr, hcr⟩ := Ideal.Quotient.mk_surjective (c : 𝓞 E ⧸ P'.1.asIdeal)
      rw [← hs, ← hcr, ← map_mul, hasRes_mk_iff]
      have hint : ∀ a ∈ RInt F E, Valued.v (adAt F P'.1 a) ≤ 1 := fun a ha => (mem_rInt_iff F E a).1 ha P'.1
      have hCle : Valued.v (algebraMap E (P'.1.adicCompletion E) (algebraMap (𝓞 E) E cr)) ≤ 1 := by
        rw [valued_algebraMap]
        exact HeightOneSpectrum.valuation_le_one _ _
      have key := last_sub_lt i (fun j => adAt F P'.1 ((k⁻¹ : GL (Fin n) (AfE F E)).1 i j))
        (fun j l => adAt F P'.1 ((δ⁻¹ : GL (Fin n) (AfE F E)).1 j l))
        (fun l => adAt F P'.1 (GlobalTheory.Mem.Col2.pullV y x l)) (algebraMap E _ (algebraMap (𝓞 E) E cr))
        (fun j => hasRes_le_one (hkr i j hi))
        (fun j hj => by
          have := hkr i j hi
          rw [if_neg hj] at this
          exact hasRes_lt_one this)
        (fun j l => hint _ (hδi' j l))
        (fun l => by
          have := hδr i l hi
          by_cases hl : l = i
          · rw [if_pos hl, ← hcr, hasRes_mk_iff] at this
            rw [if_pos hl]
            exact this
          · rw [if_neg hl] at this
            rw [if_neg hl, sub_zero]
            exact hasRes_lt_one this)
        (fun l => hint _ (hu x hx l)) hCle
      rw [pullbackVector_mul_right] at hv'
      rw [pullbackVector_triple_mul]
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul] at hv' key ⊢
      have e : (∑ j, adAt F P'.1 ((k⁻¹ : GL (Fin n) (AfE F E)).1 i j) *
            ∑ l, adAt F P'.1 ((δ⁻¹ : GL (Fin n) (AfE F E)).1 j l) * adAt F P'.1 (GlobalTheory.Mem.Col2.pullV y x l)) -
          algebraMap E (P'.1.adicCompletion E) (algebraMap (𝓞 E) E cr) *
            algebraMap E (P'.1.adicCompletion E) (algebraMap (𝓞 E) E s) =
          ((∑ j, adAt F P'.1 ((k⁻¹ : GL (Fin n) (AfE F E)).1 i j) *
            ∑ l, adAt F P'.1 ((δ⁻¹ : GL (Fin n) (AfE F E)).1 j l) * adAt F P'.1 (GlobalTheory.Mem.Col2.pullV y x l)) -
          algebraMap E (P'.1.adicCompletion E) (algebraMap (𝓞 E) E cr) *
            ∑ j, adAt F P'.1 ((k⁻¹ : GL (Fin n) (AfE F E)).1 i j) * adAt F P'.1 (GlobalTheory.Mem.Col2.pullV y x j)) +
          algebraMap E (P'.1.adicCompletion E) (algebraMap (𝓞 E) E cr) *
            ((∑ j, adAt F P'.1 ((k⁻¹ : GL (Fin n) (AfE F E)).1 i j) * adAt F P'.1 (GlobalTheory.Mem.Col2.pullV y x j)) -
              algebraMap E (P'.1.adicCompletion E) (algebraMap (𝓞 E) E s)) := by ring
      rw [e]
      refine Valuation.map_add_lt _ key ?_
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' hCle) hv'
    · rw [Pi.mulSingle_eq_of_ne hPP, Units.val_one, one_mul,
        adAt_pullV_triv y δ k P'.1 (htriv P'.1 (Or.inr (Or.inr ⟨P'.2, fun e => hPP (Subtype.ext e)⟩))) x i]
      exact hv
  · rw [hN] at hx
    rw [hbe, adAt_pullV_triv y δ k w.1 (htriv w.1 (Or.inl w.2)) x i]
    exact h.be w x hx i
  · rw [hfr, adeleComponentAt_triple_mul_dilation_trivial y δ k P'.1 (htriv P'.1 (Or.inr (Or.inl P'.2))) i j]
    exact h.fr P' i j

end GlobalTheory.Mem.Col2.DilPt
