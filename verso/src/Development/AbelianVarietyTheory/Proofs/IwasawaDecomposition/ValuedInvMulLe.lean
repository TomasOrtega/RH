import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.Splice

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]

omit [StarRing E] in

/- English proof (translation)
Take `⟨t, a, ha, e⟩` from `P.isMaximal.exists_inv hs`. Establish `hS : Valued.v (algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E s)) = 1`. Rewrite using `[valued_algebraMap]`. Conclude with `CharValCompare.val_of_notMem hs`. Take `⟨r, hr, hv⟩` from `h`.

Establish `hz : Valued.v z ≤ 1`. Establish `hR : Valued.v (algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E r)) ≤ 1`. Rewrite using `[valued_algebraMap]`. Conclude with `HeightOneSpectrum.valuation_le_one _ _`. Establish `e4 : algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E s) * z = (algebraMap E _ (algebraMap (𝓞 E) E s) * z - algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E r)) + algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E r)` using `by ring`.

Establish `h3` using `Valuation.map_add_le Valued.v hv.le hR`. Rewrite `h3` using `[← e4, map_mul, hS, one_mul]`. Conclude with `h3`. Establish `h1 : Ideal.Quotient.mk P.asIdeal (t * s) = 1`. Establish `e2 : t * s = 1 - a` using `by rw [← e]; ring`.

Rewrite using `[e2, map_sub, map_one, Ideal.Quotient.eq_zero_iff_mem.2 ha, sub_zero]`. Use `⟨t * r, by rw [map_mul, hr, ← mul_assoc, ← map_mul, h1, one_mul], ?_⟩` and prove the remaining obligations. Establish `e2 : algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E t) * algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E s) + algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E a) = 1`. Simplify using `only [← map_mul, ← map_add, e, map_one]`. Establish `e3 : z - algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E (t * r)) = algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E t) * (algebraMap E _ (algebraMap (𝓞 E) E s) * z - algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E r)) + algebraMap E (P.adicCompletion E) (algebra …`.

Rewrite using `[map_mul, map_mul]`. Take the linear combination `(-z) * e2`. Rewrite using `[e3]`. Establish `hT : Valued.v (algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E t)) ≤ 1`. Rewrite using `[valued_algebraMap]`.

Conclude with `HeightOneSpectrum.valuation_le_one _ _`. Establish `hA : Valued.v (algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E a)) < 1`. Rewrite using `[valued_algebraMap]`. Conclude with `(HeightOneSpectrum.valuation_lt_one_iff_mem _ _).2 ha`. Use `Valuation.map_add_lt _ ?_ ?_` and prove the remaining obligations.

Rewrite using `[map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' hT) hv`. Rewrite using `[map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_right' hz) hA`.
-/
theorem hasRes_of_mul {P : HeightOneSpectrum (𝓞 E)} {s : 𝓞 E} (hs : s ∉ P.asIdeal) {z : P.adicCompletion E}
    {c : 𝓞 E ⧸ P.asIdeal}
    (h : HasRes P (algebraMap E _ (algebraMap (𝓞 E) E s) * z) (Ideal.Quotient.mk P.asIdeal s * c)) : HasRes P z c := by
  obtain ⟨t, a, ha, e⟩ := P.isMaximal.exists_inv hs
  have hS : Valued.v (algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E s)) = 1 := by
    rw [valued_algebraMap]
    exact CharValCompare.val_of_notMem hs
  obtain ⟨r, hr, hv⟩ := h
  have hz : Valued.v z ≤ 1 := by
    have hR : Valued.v (algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E r)) ≤ 1 := by
      rw [valued_algebraMap]
      exact HeightOneSpectrum.valuation_le_one _ _
    have e4 : algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E s) * z =
        (algebraMap E _ (algebraMap (𝓞 E) E s) * z - algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E r)) +
          algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E r) := by ring
    have h3 := Valuation.map_add_le Valued.v hv.le hR
    rw [← e4, map_mul, hS, one_mul] at h3
    exact h3
  have h1 : Ideal.Quotient.mk P.asIdeal (t * s) = 1 := by
    have e2 : t * s = 1 - a := by rw [← e]; ring
    rw [e2, map_sub, map_one, Ideal.Quotient.eq_zero_iff_mem.2 ha, sub_zero]
  refine ⟨t * r, by rw [map_mul, hr, ← mul_assoc, ← map_mul, h1, one_mul], ?_⟩
  have e2 : algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E t) *
      algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E s) +
      algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E a) = 1 := by
    simp only [← map_mul, ← map_add, e, map_one]
  have e3 : z - algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E (t * r)) =
      algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E t) *
        (algebraMap E _ (algebraMap (𝓞 E) E s) * z - algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E r)) +
      algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E a) * z := by
    rw [map_mul, map_mul]
    linear_combination (-z) * e2
  rw [e3]
  have hT : Valued.v (algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E t)) ≤ 1 := by
    rw [valued_algebraMap]
    exact HeightOneSpectrum.valuation_le_one _ _
  have hA : Valued.v (algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E a)) < 1 := by
    rw [valued_algebraMap]
    exact (HeightOneSpectrum.valuation_lt_one_iff_mem _ _).2 ha
  refine Valuation.map_add_lt _ ?_ ?_
  · rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' hT) hv
  · rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' hz) hA

/- English proof (translation)
Establish `e` using `Formalism.L2.Col.pullV_osmul g s x i`. Establish `e' : pullV g (s • x) i = Formalism.UG.inclE (F` using `F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E s) * pullV g x i := e`. Rewrite using `[e', map_mul, adAt_inclE]`.
-/
theorem adAt_pullV_osmul {n : ℕ} (g : GL (Fin n) (AfE F E)) (w : HeightOneSpectrum (𝓞 E)) (s : 𝓞 E) (x : Sp E n)
    (i : Fin n) : adAt F w (pullV g (s • x) i) = algebraMap E _ (algebraMap (𝓞 E) E s) * adAt F w (pullV g x i) := by
  have e := Formalism.L2.Col.pullV_osmul g s x i
  have e' : pullV g (s • x) i = Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E s) * pullV g x i := e
  rw [e', map_mul, adAt_inclE]

omit [StarRing E] in

/- English proof (translation)
Use extensionality with `i j`. Conclude with `PtExist.ad_ext fun w => congrFun (congrFun (h w) i) j`.
-/
theorem mat_ext {n : ℕ} {M N : Matrix (Fin n) (Fin n) (AfE F E)} (h : ∀ w, M.map (adAt F w) = N.map (adAt F w)) : M = N := by
  ext i j
  exact PtExist.ad_ext fun w => congrFun (congrFun (h w) i) j

omit [StarRing E] in

/- English proof (translation)
Unfold `pullV`. Rewrite using `[RingHom.map_mulVec, RingHom.map_mulVec, hw]`.
-/
theorem adAt_pullV_congr {n : ℕ} {g k : GL (Fin n) (AfE F E)} {w : HeightOneSpectrum (𝓞 E)}
    (hw : ((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F w) =
      ((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F w)) (x : Sp E n) (i : Fin n) :
    adAt F w (pullV g x i) = adAt F w (pullV k x i) := by
  unfold pullV
  rw [RingHom.map_mulVec, RingHom.map_mulVec, hw]

/- English proof (translation)
Establish `key : ∀ u ∈ Formalism.L2.Herm.hatL (F` using `F) N', ∀ i, Valued.v (adAt F w ((((a⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ u) i)) ≤ 1 := by`. Introduce `u hu`. Proceed by induction on `hu using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨v, hv, rfl⟩` from `hx`.

Introduce `i`. Take `⟨s, hs, hsv⟩` from `(mem_locP _ _ _).1 (hl (le_locP w _ hv))`. Establish `h1` using `(mem_latS_std _).1 ((ha _).1 (Submodule.subset_span ⟨_, hsv, rfl⟩)) i`. Establish `h2 : Valued.v (afIso F E (Formalism.L2.Col.pullV a (s • v) i) w) ≤ 1` using `(mem_rInt_iff F E _).1 h1 w`. Rewrite `h2` using `[← adAt_apply, pullV_osmul, map_mul, map_mul, adAt_inclE, valued_algebraMap, CharValCompare.val_of_notMem hs, one_mul]`.

Conclude with `h2`. Consider the case `zero`. Introduce `i`. Simplify using the standard rewrite rules. Consider the case `add x y _ _ hx hy`.

Introduce `i`. Rewrite using `[Matrix.mulVec_add, Pi.add_apply, map_add]`. Conclude with `Valuation.map_add_le _ (hx i) (hy i)`. Consider the case `smul c x _ hx`. Introduce `i`.

Establish `e0 : c • x = (c : AfE F E) • x` using `rfl`. Rewrite using `[e0, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, map_mul, map_mul]`. Conclude with `mul_le_one' ((mem_rInt_iff F E _).1 c.2 w) (hx i)`. Establish `hu : (fun l => (b : Matrix (Fin n) (Fin n) (AfE F E)) l j) ∈ Formalism.L2.Herm.hatL (F` using `F) N' := by`. Use `(hb _).2 ((mem_latS_std _).2 fun l => ?_)` and prove the remaining obligations.

Simplify using `only [Matrix.mulVec, dotProduct]`. Rewrite using `[← Matrix.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_apply]`. Use `split_ifs`. Use `exacts [one_mem _, zero_mem _]`. Use `key _ hu i` as an intermediate fact.

Rewrite using `[Units.val_mul, Matrix.mul_apply]`. Conclude with `this`.
-/
theorem valued_inv_mul_le {n : ℕ} {w : HeightOneSpectrum (𝓞 E)} {a b : GL (Fin n) (AfE F E)}
    {N N' : Submodule (𝓞 E) (Sp E n)} (ha : Formalism.L2.Herm.Carries a (stdLat E n) N)
    (hb : Formalism.L2.Herm.Carries b (stdLat E n) N') (hl : Formalism.HermitianLatticesTheory.localization₂ w.asIdeal N' ≤ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal N)
    (i j : Fin n) :
    Valued.v (adAt F w (((a⁻¹ * b : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j)) ≤ 1 := by
  have key : ∀ u ∈ Formalism.L2.Herm.hatL (F := F) N', ∀ i,
      Valued.v (adAt F w ((((a⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ u) i)) ≤ 1 := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨v, hv, rfl⟩ := hx
      intro i
      obtain ⟨s, hs, hsv⟩ := (mem_locP _ _ _).1 (hl (le_locP w _ hv))
      have h1 := (mem_latS_std _).1 ((ha _).1 (Submodule.subset_span ⟨_, hsv, rfl⟩)) i
      have h2 : Valued.v (afIso F E (Formalism.L2.Col.pullV a (s • v) i) w) ≤ 1 := (mem_rInt_iff F E _).1 h1 w
      rw [← adAt_apply, pullV_osmul, map_mul, map_mul, adAt_inclE, valued_algebraMap, CharValCompare.val_of_notMem hs,
        one_mul] at h2
      exact h2
    | zero =>
      intro i
      simp
    | add x y _ _ hx hy =>
      intro i
      rw [Matrix.mulVec_add, Pi.add_apply, map_add]
      exact Valuation.map_add_le _ (hx i) (hy i)
    | smul c x _ hx =>
      intro i
      have e0 : c • x = (c : AfE F E) • x := rfl
      rw [e0, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, map_mul, map_mul]
      exact mul_le_one' ((mem_rInt_iff F E _).1 c.2 w) (hx i)
  have hu : (fun l => (b : Matrix (Fin n) (Fin n) (AfE F E)) l j) ∈ Formalism.L2.Herm.hatL (F := F) N' := by
    refine (hb _).2 ((mem_latS_std _).2 fun l => ?_)
    simp only [Matrix.mulVec, dotProduct]
    rw [← Matrix.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  have := key _ hu i
  rw [Units.val_mul, Matrix.mul_apply]
  exact this

section Splice

variable (hc : CMData F E)

local notation "σ" => Formalism.UG.sigR (CMData.sig hc) (FiniteAdeleRing (𝓞 F) F)

def splice {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (A B : Matrix (Fin n) (Fin n) (AfE F E)) :
    Matrix (Fin n) (Fin n) (AfE F E) :=
  Matrix.of fun i j => (1 - PtExist.idem F P - σ (PtExist.idem F P)) * A i j +
    (PtExist.idem F P + σ (PtExist.idem F P)) * B i j

open Classical in

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.map_apply]`. Simplify using `only [splice, Matrix.of_apply, map_add, map_mul, map_sub, map_one, PtExist.adAt_idem, PtExist.adAt_sig_idem]`. Distinguish the cases in `h1 : w = P`. Substitute `h1` using the available equality.

Simplify using `[hP]`. Apply the tactic sequence `by_cases h2 : conjPrime₂ w = P <;> simp [h1, h2]`.
-/
theorem map_splice {n : ℕ} {P : HeightOneSpectrum (𝓞 E)} (hP : conjPrime₂ P ≠ P) (A B : Matrix (Fin n) (Fin n) (AfE F E))
    (w : HeightOneSpectrum (𝓞 E)) :
    (splice hc P A B).map (adAt F w) = if w = P ∨ conjPrime₂ w = P then B.map (adAt F w) else A.map (adAt F w) := by
  ext i j
  rw [Matrix.map_apply]
  simp only [splice, Matrix.of_apply, map_add, map_mul, map_sub, map_one, PtExist.adAt_idem, PtExist.adAt_sig_idem]
  by_cases h1 : w = P
  · subst h1
    simp [hP]
  · by_cases h2 : conjPrime₂ w = P <;> simp [h1, h2]

end Splice

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ hc n ST SG Q h X X0 P h1 h2 h3 h4 hh hloc hf hbe hfr`. Take `⟨h0, hh0⟩` from `PtExist.exists_isPtOf_cm hc n ST SG Q X0 h1 h2 h3 h4`. Simplify using `only [Finset.mem_union, not_or] at h4`. Establish `hPc : conjPrime₂ P.1 ≠ P.1` using `fun e => (h4 P.1 (Or.inl P.2)).1 (by rw [e]; exact P.2)`. Establish `hfar : ∀ w : HeightOneSpectrum (𝓞 E), ¬(w = P.1 ∨ conjPrime₂ w = P.1) → w ≠ P.1 ∧ w ≠ conjPrime₂ P.1` using `fun w hw => ⟨fun e => hw (Or.inl e), fun e => hw (Or.inr (by rw [e, CharValCompare.conjP_conjP]))⟩`.

Establish `hnear : ∀ w : HeightOneSpectrum (𝓞 E), w ≠ P.1 → w ≠ conjPrime₂ P.1 → ¬(w = P.1 ∨ conjPrime₂ w = P.1)`. Introduce and unpack `w hw hw' (e | e)`. Conclude with `hw e`. Conclude with `hw' (by rw [← e, CharValCompare.conjP_conjP])`. Set `G` to `splice hc P.1 (h : Matrix (Fin n) (Fin n) (AfE F E)) (h0 : Matrix (Fin n) (Fin n) (AfE F E))`.

Set `G'` to `splice hc P.1 ((h⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) ((h0⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E))`. Establish `hGG : G' * G = 1`. Use `mat_ext fun w => ?_` and prove the remaining obligations. Rewrite using `[Matrix.map_mul, map_splice hc hPc, map_splice hc hPc, Matrix.map_one _ (map_zero _) (map_one _)]`. Use `split_ifs`.

Rewrite using `[← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]`. Rewrite using `[← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]`. Set `g : GL (Fin n) (AfE F E)` to `⟨G, G', mul_eq_one_comm.1 hGG, hGG⟩`. Establish `hg : g ∈ UAd hc n`. Rewrite using `[PtExist.mem_uad_iff, ← hGG]`.

Use `congr 1`. Use extensionality with `i j`. Use `show Formalism.UG.sigR (CMData.sig hc) (FiniteAdeleRing (𝓞 F) F) (G j i) = G' i j`. Simplify using `only [G, G', splice, Matrix.of_apply, map_add, map_mul, map_sub, map_one, PtExist.sig_sig, PtExist.inv_apply hh.uni, PtExist.inv_apply hh0.uni]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hGw : ∀ w, (g : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F w) = if w = P.1 ∨ conjPrime₂ w = P.1 then (h0 : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F w) else (h : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F w)` using `fun w => map_splice hc hPc _ _ w`. Establish `hGw' : ∀ w, ((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F w) = if w = P.1 ∨ conjPrime₂ w = P.1 then ((h0⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F w) else ((h⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F …` using `fun w => map_splice hc hPc _ _ w`. Use `⟨h⁻¹ * g, mul_mem (inv_mem hh.uni) hg, fun w hw hw' i j => ?_, ?_⟩` and prove the remaining obligations. Establish `e : ((h⁻¹ * g : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F w) = 1`. Rewrite using `[Units.val_mul, Matrix.map_mul, hGw, if_neg (hnear w hw hw'), ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]`.

Use `congrFun (congrFun e i) j` as an intermediate fact. Rewrite `this` using `[Matrix.map_apply, Matrix.one_apply]`. Conclude with `this`. Rewrite using `[mul_inv_cancel_left]`. Establish `k1 : ∀ i j, ((g⁻¹ * h0 : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j ∈ RInt F E`.

Introduce `i j`. Use `(mem_rInt_iff F E _).2 fun w => ?_` and prove the remaining obligations. Rewrite using `[← adAt_apply]`. Distinguish the cases in `hw : w = P.1 ∨ conjPrime₂ w = P.1`. Establish `e : ((g⁻¹ * h0 : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F w) = 1`.

Rewrite using `[Units.val_mul, Matrix.map_mul, hGw', if_pos hw, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]`. Use `congrFun (congrFun e i) j` as an intermediate fact. Rewrite `this` using `[Matrix.map_apply, Matrix.one_apply]`. Rewrite using `[this]`. Apply the tactic sequence `split_ifs <;> simp`.

Establish `e : ((g⁻¹ * h0 : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F w) = ((h⁻¹ * h0 : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F w)`. Rewrite using `[Units.val_mul, Matrix.map_mul, hGw', if_neg hw, ← Matrix.map_mul, ← Units.val_mul]`. Use `congrFun (congrFun e i) j` as an intermediate fact. Rewrite `this` using `[Matrix.map_apply, Matrix.map_apply]`. Rewrite using `[this]`.

Conclude with `valued_inv_mul_le hh.lat hh0.lat (hloc w (hfar w hw).1 (hfar w hw).2).le i j`. Establish `k2 : ∀ i j, ((h0⁻¹ * g : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j ∈ RInt F E`. Introduce `i j`. Use `(mem_rInt_iff F E _).2 fun w => ?_` and prove the remaining obligations. Rewrite using `[← adAt_apply]`.

Distinguish the cases in `hw : w = P.1 ∨ conjPrime₂ w = P.1`. Establish `e : ((h0⁻¹ * g : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F w) = 1`. Rewrite using `[Units.val_mul, Matrix.map_mul, hGw, if_pos hw, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]`. Use `congrFun (congrFun e i) j` as an intermediate fact. Rewrite `this` using `[Matrix.map_apply, Matrix.one_apply]`.

Rewrite using `[this]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `e : ((h0⁻¹ * g : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F w) = ((h0⁻¹ * h : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F w)`. Rewrite using `[Units.val_mul, Matrix.map_mul, hGw, if_neg hw, ← Matrix.map_mul, ← Units.val_mul]`. Use `congrFun (congrFun e i) j` as an intermediate fact.

Rewrite `this` using `[Matrix.map_apply, Matrix.map_apply]`. Rewrite using `[this]`. Conclude with `valued_inv_mul_le hh0.lat hh.lat (hloc w (hfar w hw).1 (hfar w hw).2).ge i j`. Use `⟨hg, fun u => (hh0.lat u).trans ((mem_latS_std _).trans (Iff.trans ⟨fun hz i => ?_, fun hz i => ?_⟩ (mem_latS_std _).symm)), fun P' x hx i hi => ?_, fun w x hx i => ?_, fun P'' i j => ?_⟩` and prove the remaining obligations. Use `PtExist.mulVec_int k1 hz i` as an intermediate fact.

Rewrite `this` using `[Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel_right]`. Then use the resulting hypothesis. Use `PtExist.mulVec_int k2 hz i` as an intermediate fact. Rewrite `this` using `[Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel_right]`. Then use the resulting hypothesis. Distinguish the cases in `hPP : P' = P`. Substitute `hPP` using the available equality.

Rewrite using `[adAt_pullV_congr (k := h0) (by rw [hGw', if_pos (Or.inl rfl)])]`. Conclude with `hh0.f P' x hx i hi`. Establish `hne : P'.1 ≠ P.1` using `fun e => hPP (Subtype.ext e)`. Establish `hn : ¬(P'.1 = P.1 ∨ conjPrime₂ P'.1 = P.1)`. Introduce and unpack `(e | e)`.

Conclude with `hne e`. Conclude with `(h4 P'.1 (Or.inl P'.2)).1 (by rw [e]; exact P.2)`. Rewrite using `[adAt_pullV_congr (k := h) (by rw [hGw', if_neg hn]), hf P' hPP]`. Establish `hx' : x ∈ Formalism.HermitianLatticesTheory.localization₂ P'.1.asIdeal X.deco.1.N`. Rewrite using `[← hloc P'.1 (hfar _ hn).1 (hfar _ hn).2]`.

Conclude with `le_locP _ _ hx`. Take `⟨s, hs, hsx⟩` from `(mem_locP _ _ _).1 hx'`. Use `hh.f P' _ hsx i hi` as an intermediate fact. Rewrite `this` using `[X.deco.2.f_smul P' s x hx', adAt_pullV_osmul]`. Conclude with `hasRes_of_mul hs this`.

Establish `hn : ¬(w.1 = P.1 ∨ conjPrime₂ w.1 = P.1)`. Introduce and unpack `(e | e)`. Conclude with `Finset.disjoint_left.1 h1 P.2 (by rw [← e]; exact w.2)`. Conclude with `(h4 w.1 (Or.inr (Or.inl w.2))).1 (by rw [e]; exact P.2)`. Rewrite using `[adAt_pullV_congr (k := h) (by rw [hGw', if_neg hn]), hbe]`.

Establish `hx' : x ∈ Formalism.HermitianLatticesTheory.localization₂ w.1.asIdeal X.deco.1.N`. Rewrite using `[← hloc w.1 (hfar _ hn).1 (hfar _ hn).2]`. Conclude with `le_locP _ _ hx`. Take `⟨s, hs, hsx⟩` from `(mem_locP _ _ _).1 hx'`. Use `hh.be w _ hsx i` as an intermediate fact.

Rewrite `this` using `[X.deco.2.be_smul w s x hx', Pi.smul_apply, smul_eq_mul, adAt_pullV_osmul]`. Conclude with `hasRes_of_mul hs this`. Establish `hn : ¬(P''.1 = P.1 ∨ conjPrime₂ P''.1 = P.1)`. Introduce and unpack `(e | e)`. Conclude with `Finset.disjoint_left.1 h2 P.2 (by rw [← e]; exact P''.2)`.

Conclude with `(h4 P''.1 (Or.inr (Or.inr P''.2))).1 (by rw [e]; exact P.2)`. Use `congrFun (congrFun (hGw P''.1) i) j` as an intermediate fact. Rewrite `this` using `[if_neg hn, Matrix.map_apply, Matrix.map_apply]`. Rewrite using `[this, hh.fr P'' i j, hfr]`.
-/
theorem exists_splice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))), ∀ (h : GL (Fin n) (AfE F E)) (X X0 : DecoF E n ST SG Q) (P : ST), Disjoint ST SG → Disjoint ST Q → Disjoint SG Q → (∀ w ∈ uSG ST (uSG SG Q), conjPrime₂ w ∉ uSG ST (uSG SG Q)) → IsPtOf hc h X → (∀ w : HeightOneSpectrum (𝓞 E), w ≠ P.1 → w ≠ conjPrime₂ P.1 → Formalism.HermitianLatticesTheory.localization₂ w.asIdeal X0.deco.1.N = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal X.deco.1.N) → (∀ P' : ST, P' ≠ P → X0.deco.1.f P' = X.deco.1.f P') → X0.deco.1.be = X.deco.1.be → X0.fr = X.fr → ∃ ε ∈ Formalism.L2.Herm.UstdAf hc n, (∀ w : HeightOneSpectrum (𝓞 E), w ≠ P.1 → w ≠ conjPrime₂ P.1 → ∀ i j, adAt F w (ε.1 i j) = if i = j then 1 else 0) ∧ IsPtOf hc (h * ε) X0 := by
  intro F E _ _ _ _ _ _ hc n ST SG Q h X X0 P h1 h2 h3 h4 hh hloc hf hbe hfr
  classical
  obtain ⟨h0, hh0⟩ := PtExist.exists_isPtOf_cm hc n ST SG Q X0 h1 h2 h3 h4
  simp only [Finset.mem_union, not_or] at h4
  have hPc : conjPrime₂ P.1 ≠ P.1 := fun e => (h4 P.1 (Or.inl P.2)).1 (by rw [e]; exact P.2)
  have hfar : ∀ w : HeightOneSpectrum (𝓞 E), ¬(w = P.1 ∨ conjPrime₂ w = P.1) → w ≠ P.1 ∧ w ≠ conjPrime₂ P.1 := fun w hw =>
    ⟨fun e => hw (Or.inl e), fun e => hw (Or.inr (by rw [e, CharValCompare.conjP_conjP]))⟩
  have hnear : ∀ w : HeightOneSpectrum (𝓞 E), w ≠ P.1 → w ≠ conjPrime₂ P.1 → ¬(w = P.1 ∨ conjPrime₂ w = P.1) := by
    rintro w hw hw' (e | e)
    · exact hw e
    · exact hw' (by rw [← e, CharValCompare.conjP_conjP])
  let G := splice hc P.1 (h : Matrix (Fin n) (Fin n) (AfE F E)) (h0 : Matrix (Fin n) (Fin n) (AfE F E))
  let G' := splice hc P.1 ((h⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E))
    ((h0⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E))
  have hGG : G' * G = 1 := by
    refine mat_ext fun w => ?_
    rw [Matrix.map_mul, map_splice hc hPc, map_splice hc hPc, Matrix.map_one _ (map_zero _) (map_one _)]
    split_ifs
    · rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
    · rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  let g : GL (Fin n) (AfE F E) := ⟨G, G', mul_eq_one_comm.1 hGG, hGG⟩
  have hg : g ∈ UAd hc n := by
    rw [PtExist.mem_uad_iff, ← hGG]
    congr 1
    ext i j
    show Formalism.UG.sigR (CMData.sig hc) (FiniteAdeleRing (𝓞 F) F) (G j i) = G' i j
    simp only [G, G', splice, Matrix.of_apply, map_add, map_mul, map_sub, map_one, PtExist.sig_sig,
      PtExist.inv_apply hh.uni, PtExist.inv_apply hh0.uni]
    ring
  have hGw : ∀ w, (g : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F w) = if w = P.1 ∨ conjPrime₂ w = P.1 then
      (h0 : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F w) else (h : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F w) :=
    fun w => map_splice hc hPc _ _ w
  have hGw' : ∀ w, ((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F w) =
      if w = P.1 ∨ conjPrime₂ w = P.1 then ((h0⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F w)
      else ((h⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F w) :=
    fun w => map_splice hc hPc _ _ w

  refine ⟨h⁻¹ * g, mul_mem (inv_mem hh.uni) hg, fun w hw hw' i j => ?_, ?_⟩
  · have e : ((h⁻¹ * g : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F w) = 1 := by
      rw [Units.val_mul, Matrix.map_mul, hGw, if_neg (hnear w hw hw'), ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
    have := congrFun (congrFun e i) j
    rw [Matrix.map_apply, Matrix.one_apply] at this
    exact this
  rw [mul_inv_cancel_left]

  have k1 : ∀ i j, ((g⁻¹ * h0 : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j ∈ RInt F E := by
    intro i j
    refine (mem_rInt_iff F E _).2 fun w => ?_
    rw [← adAt_apply]
    by_cases hw : w = P.1 ∨ conjPrime₂ w = P.1
    · have e : ((g⁻¹ * h0 : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F w) = 1 := by
        rw [Units.val_mul, Matrix.map_mul, hGw', if_pos hw, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel,
          Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
      have := congrFun (congrFun e i) j
      rw [Matrix.map_apply, Matrix.one_apply] at this
      rw [this]
      split_ifs <;> simp
    · have e : ((g⁻¹ * h0 : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F w) =
          ((h⁻¹ * h0 : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F w) := by
        rw [Units.val_mul, Matrix.map_mul, hGw', if_neg hw, ← Matrix.map_mul, ← Units.val_mul]
      have := congrFun (congrFun e i) j
      rw [Matrix.map_apply, Matrix.map_apply] at this
      rw [this]
      exact valued_inv_mul_le hh.lat hh0.lat (hloc w (hfar w hw).1 (hfar w hw).2).le i j
  have k2 : ∀ i j, ((h0⁻¹ * g : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j ∈ RInt F E := by
    intro i j
    refine (mem_rInt_iff F E _).2 fun w => ?_
    rw [← adAt_apply]
    by_cases hw : w = P.1 ∨ conjPrime₂ w = P.1
    · have e : ((h0⁻¹ * g : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F w) = 1 := by
        rw [Units.val_mul, Matrix.map_mul, hGw, if_pos hw, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel,
          Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
      have := congrFun (congrFun e i) j
      rw [Matrix.map_apply, Matrix.one_apply] at this
      rw [this]
      split_ifs <;> simp
    · have e : ((h0⁻¹ * g : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F w) =
          ((h0⁻¹ * h : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F w) := by
        rw [Units.val_mul, Matrix.map_mul, hGw, if_neg hw, ← Matrix.map_mul, ← Units.val_mul]
      have := congrFun (congrFun e i) j
      rw [Matrix.map_apply, Matrix.map_apply] at this
      rw [this]
      exact valued_inv_mul_le hh0.lat hh.lat (hloc w (hfar w hw).1 (hfar w hw).2).ge i j
  refine ⟨hg, fun u => (hh0.lat u).trans ((mem_latS_std _).trans (Iff.trans ⟨fun hz i => ?_, fun hz i => ?_⟩
    (mem_latS_std _).symm)), fun P' x hx i hi => ?_, fun w x hx i => ?_, fun P'' i j => ?_⟩
  · have := PtExist.mulVec_int k1 hz i
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel_right] at this
  · have := PtExist.mulVec_int k2 hz i
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel_right] at this
  · by_cases hPP : P' = P
    · subst hPP
      rw [adAt_pullV_congr (k := h0) (by rw [hGw', if_pos (Or.inl rfl)])]
      exact hh0.f P' x hx i hi
    · have hne : P'.1 ≠ P.1 := fun e => hPP (Subtype.ext e)
      have hn : ¬(P'.1 = P.1 ∨ conjPrime₂ P'.1 = P.1) := by
        rintro (e | e)
        · exact hne e
        · exact (h4 P'.1 (Or.inl P'.2)).1 (by rw [e]; exact P.2)
      rw [adAt_pullV_congr (k := h) (by rw [hGw', if_neg hn]), hf P' hPP]
      have hx' : x ∈ Formalism.HermitianLatticesTheory.localization₂ P'.1.asIdeal X.deco.1.N := by
        rw [← hloc P'.1 (hfar _ hn).1 (hfar _ hn).2]
        exact le_locP _ _ hx
      obtain ⟨s, hs, hsx⟩ := (mem_locP _ _ _).1 hx'
      have := hh.f P' _ hsx i hi
      rw [X.deco.2.f_smul P' s x hx', adAt_pullV_osmul] at this
      exact hasRes_of_mul hs this
  · have hn : ¬(w.1 = P.1 ∨ conjPrime₂ w.1 = P.1) := by
      rintro (e | e)
      · exact Finset.disjoint_left.1 h1 P.2 (by rw [← e]; exact w.2)
      · exact (h4 w.1 (Or.inr (Or.inl w.2))).1 (by rw [e]; exact P.2)
    rw [adAt_pullV_congr (k := h) (by rw [hGw', if_neg hn]), hbe]
    have hx' : x ∈ Formalism.HermitianLatticesTheory.localization₂ w.1.asIdeal X.deco.1.N := by
      rw [← hloc w.1 (hfar _ hn).1 (hfar _ hn).2]
      exact le_locP _ _ hx
    obtain ⟨s, hs, hsx⟩ := (mem_locP _ _ _).1 hx'
    have := hh.be w _ hsx i
    rw [X.deco.2.be_smul w s x hx', Pi.smul_apply, smul_eq_mul, adAt_pullV_osmul] at this
    exact hasRes_of_mul hs this
  · have hn : ¬(P''.1 = P.1 ∨ conjPrime₂ P''.1 = P.1) := by
      rintro (e | e)
      · exact Finset.disjoint_left.1 h2 P.2 (by rw [← e]; exact P''.2)
      · exact (h4 P''.1 (Or.inr (Or.inr P''.2))).1 (by rw [e]; exact P.2)
    have := congrFun (congrFun (hGw P''.1) i) j
    rw [if_neg hn, Matrix.map_apply, Matrix.map_apply] at this
    rw [this, hh.fr P'' i j, hfr]

end GlobalTheory.Mem.Col2.Splice
