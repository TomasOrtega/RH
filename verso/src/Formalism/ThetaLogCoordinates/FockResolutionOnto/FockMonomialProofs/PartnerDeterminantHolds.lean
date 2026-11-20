import Formalism.ThetaLogCoordinates.FockResolutionOnto.StatementA
import Formalism.PolynomialDimension.MultinomialDepth.PartnerM
import Formalism.MahlerMeasure.MahlerMeasureProofs.SmithZp
import Formalism.MahlerMeasure.MahlerMeasureProofs.MeanGam

namespace Formalism.InvariantFactorPaths.L4

open Formalism.GM Formalism.GM.M MvPolynomial Finset

/- English proof (translation)
Introduce `p _ Vs _ _ _ _ be k g D hli hpart`. Establish `hp1 : (1 : ℝ) < p` using `by exact_mod_cast (Fact.out : p.Prime).one_lt`. Establish `hp0 : (0 : ℝ) < p` using `by linarith`. Use `set G : Matrix (Fin k) (Fin k) ℚ_[p] := Matrix.of fun a b => be (g a) (g b) with hG`. Take `⟨U, V, dg, hU, hV, hUd, hVd, hGUV⟩` from `Formalism.GM.TM.smith_qp smith_form_p_adic_integers G`.

Set `φ : ℤ_[p] →+* ℚ_[p]` to `PadicInt.Coe.ringHom`. Set `U' : Matrix (Fin k) (Fin k) ℤ_[p]` to `fun x y => ⟨U x y, hU x y⟩`. Set `V' : Matrix (Fin k) (Fin k) ℤ_[p]` to `fun x y => ⟨V x y, hV x y⟩`. Establish `hU'map : U'.map φ = U` using `by ext x y; rfl`. Establish `hU'det : IsUnit U'.det`.

Rewrite using `[PadicInt.isUnit_iff]`. Establish `: ((U'.det : ℤ_[p]) : ℚ_[p]) = U.det`. Rewrite using `[← hU'map, show U'.map φ = φ.mapMatrix U' from rfl, ← RingHom.map_det]`. Both sides reduce to the same expression. Rewrite using `[PadicInt.norm_def, this, hUd]`.

Use `set W : Matrix (Fin k) (Fin k) ℤ_[p] := U'⁻¹ with hW`. Establish `hWU : W * U' = 1` using `Matrix.nonsing_inv_mul _ hU'det`. Establish `hsm : ∀ (a : ℤ_[p]) (x : Vs), a • x = (a : ℚ_[p]) • x` using `fun a x => by`. Rewrite using `[← PadicInt.algebraMap_apply, algebraMap_smul]`. Establish `hd : ∀ i, (p : ℝ) ^ (-D) ≤ ‖dg i‖`.

Introduce `i`. Use `set u : Vs := ∑ a, W i a • g a with hu`. Establish `huL : u ∈ Submodule.span ℤ_[p] (Set.range g)` using `Submodule.mem_span_range_iff_exists_fun ℤ_[p] |>.mpr ⟨W i, rfl⟩`. Establish `hprim : ∀ (a : ℤ_[p]) (x : Vs), x ∈ Submodule.span ℤ_[p] (Set.range g) → u = a • x → IsUnit a`. Introduce `a x hx hux`.

Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun ℤ_[p]).mp hx`. Establish `h0 : ∑ b, (W i b - a * c b) • g b = 0`. Simplify using `only [sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum]`. Rewrite using `[← hu, hux, sub_self]`. Establish `h1` using `Fintype.linearIndependent_iff.mp hli _ h0`.

Establish `h2 : (W * U') i i = a * ∑ b, c b * U' b i`. Rewrite using `[Matrix.mul_apply, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[sub_eq_zero.mp (h1 b)]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `h2` using `[hWU, Matrix.one_apply_eq]`. Conclude with `IsUnit.of_mul_eq_one _ h2.symm`. Take `⟨u', hu'L, hu'⟩` from `hpart u huL hprim`. Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun ℤ_[p]).mp hu'L`. Establish `hWG : ∀ b, be u (g b) = dg i * V i b`.

Introduce `b`. Establish `e1 : be u (g b) = ((W.map φ) * G) i b`. Rewrite using `[Matrix.mul_apply, hu, map_sum, LinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[hsm, map_smul, LinearMap.smul_apply, smul_eq_mul]`.

Both sides reduce to the same expression. Establish `e2 : (W.map φ) * U = 1`. Rewrite using `[← hU'map, ← Matrix.map_mul, hWU]`. Conclude with `Matrix.map_one φ (map_zero φ) (map_one φ)`. Rewrite using `[e1, hGUV, ← Matrix.mul_assoc, ← Matrix.mul_assoc, e2, Matrix.one_mul, Matrix.diagonal_mul]`.

Establish `hval : be u (∑ b, c b • g b) = dg i * ((∑ b, c b * V' i b : ℤ_[p]) : ℚ_[p])`. Rewrite using `[map_sum, PadicInt.coe_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[hsm, map_smul, smul_eq_mul, hWG b, PadicInt.coe_mul]`. Use `show _ = dg i * ((c b : ℚ_[p]) * V i b)`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `hu'` using `[hval, norm_mul]`. Use `hu'.trans ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hGUV, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, norm_mul, norm_mul, hUd, hVd, one_mul, mul_one, norm_prod]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.rpow_mul_natCast hp0.le]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ ∏ i, ‖dg i‖ := Finset.prod_le_prod (fun _ _ => (Real.rpow_pos_of_pos hp0 _).le) fun i _ => hd i`.
-/
theorem partner_determinant_holds : PartnerDet := by
  intro p _ Vs _ _ _ _ be k g D hli hpart
  classical
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  set G : Matrix (Fin k) (Fin k) ℚ_[p] := Matrix.of fun a b => be (g a) (g b) with hG
  obtain ⟨U, V, dg, hU, hV, hUd, hVd, hGUV⟩ := Formalism.GM.TM.smith_qp smith_form_p_adic_integers G
  let φ : ℤ_[p] →+* ℚ_[p] := PadicInt.Coe.ringHom
  let U' : Matrix (Fin k) (Fin k) ℤ_[p] := fun x y => ⟨U x y, hU x y⟩
  let V' : Matrix (Fin k) (Fin k) ℤ_[p] := fun x y => ⟨V x y, hV x y⟩
  have hU'map : U'.map φ = U := by ext x y; rfl
  have hU'det : IsUnit U'.det := by
    rw [PadicInt.isUnit_iff]
    have : ((U'.det : ℤ_[p]) : ℚ_[p]) = U.det := by
      rw [← hU'map, show U'.map φ = φ.mapMatrix U' from rfl, ← RingHom.map_det]; rfl
    rw [PadicInt.norm_def, this, hUd]
  set W : Matrix (Fin k) (Fin k) ℤ_[p] := U'⁻¹ with hW
  have hWU : W * U' = 1 := Matrix.nonsing_inv_mul _ hU'det
  have hsm : ∀ (a : ℤ_[p]) (x : Vs), a • x = (a : ℚ_[p]) • x := fun a x => by
    rw [← PadicInt.algebraMap_apply, algebraMap_smul]

  have hd : ∀ i, (p : ℝ) ^ (-D) ≤ ‖dg i‖ := by
    intro i
    set u : Vs := ∑ a, W i a • g a with hu
    have huL : u ∈ Submodule.span ℤ_[p] (Set.range g) :=
      Submodule.mem_span_range_iff_exists_fun ℤ_[p] |>.mpr ⟨W i, rfl⟩
    have hprim : ∀ (a : ℤ_[p]) (x : Vs), x ∈ Submodule.span ℤ_[p] (Set.range g) → u = a • x → IsUnit a := by
      intro a x hx hux
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ_[p]).mp hx
      have h0 : ∑ b, (W i b - a * c b) • g b = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum]
        rw [← hu, hux, sub_self]
      have h1 := Fintype.linearIndependent_iff.mp hli _ h0
      have h2 : (W * U') i i = a * ∑ b, c b * U' b i := by
        rw [Matrix.mul_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [sub_eq_zero.mp (h1 b)]; ring
      rw [hWU, Matrix.one_apply_eq] at h2
      exact IsUnit.of_mul_eq_one _ h2.symm
    obtain ⟨u', hu'L, hu'⟩ := hpart u huL hprim
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ_[p]).mp hu'L
    have hWG : ∀ b, be u (g b) = dg i * V i b := by
      intro b
      have e1 : be u (g b) = ((W.map φ) * G) i b := by
        rw [Matrix.mul_apply, hu, map_sum, LinearMap.sum_apply]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hsm, map_smul, LinearMap.smul_apply, smul_eq_mul]; rfl
      have e2 : (W.map φ) * U = 1 := by
        rw [← hU'map, ← Matrix.map_mul, hWU]
        exact Matrix.map_one φ (map_zero φ) (map_one φ)
      rw [e1, hGUV, ← Matrix.mul_assoc, ← Matrix.mul_assoc, e2, Matrix.one_mul, Matrix.diagonal_mul]
    have hval : be u (∑ b, c b • g b) = dg i * ((∑ b, c b * V' i b : ℤ_[p]) : ℚ_[p]) := by
      rw [map_sum, PadicInt.coe_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hsm, map_smul, smul_eq_mul, hWG b, PadicInt.coe_mul]
      show _ = dg i * ((c b : ℚ_[p]) * V i b)
      ring
    rw [hval, norm_mul] at hu'
    refine hu'.trans ?_
    calc ‖dg i‖ * ‖((∑ b, c b * V' i b : ℤ_[p]) : ℚ_[p])‖ ≤ ‖dg i‖ * 1 :=
          mul_le_mul_of_nonneg_left (PadicInt.norm_le_one _) (norm_nonneg _)
      _ = ‖dg i‖ := mul_one _
  rw [hGUV, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, norm_mul, norm_mul, hUd, hVd, one_mul, mul_one,
    norm_prod]
  calc (p : ℝ) ^ (-(D * k)) = ∏ _i : Fin k, (p : ℝ) ^ (-D) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.rpow_mul_natCast hp0.le]
        congr 1; ring
    _ ≤ ∏ i, ‖dg i‖ := Finset.prod_le_prod (fun _ _ => (Real.rpow_pos_of_pos hp0 _).le) fun i _ => hd i

section Gr
variable {p : ℕ} [Fact p.Prime] {K r : ℕ} [NeZero r]

/- English proof (translation)
Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨f, hf, rfl⟩`. Establish `hfI : f ∈ IntPol p (Fin (K + 1) × Fin r)` using `(Submodule.mem_inf.mp (Submodule.mem_inf.mp hf).1).2`. Use `Formalism.GM.TM.mem_intPol_of_norm _ fun m => ?_` and prove the remaining obligations. Rewrite using `[Formalism.GM.MeanGammaLemmas.coeff_initPart]`.

Use `split_ifs`. Conclude with `Formalism.CountingSumsFrames.intPol_norm f hfI m`. Simplify using the standard rewrite rules.
-/
theorem grLat_le_int (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r)
    (w : Fin r → ℤ) (v : Fin (K + 1) × Fin r) (e : ℕ) :
    grLat p LLw J M ρ w v e ≤ IntPol p (Fin (K + 1) × Fin r) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨f, hf, rfl⟩
  have hfI : f ∈ IntPol p (Fin (K + 1) × Fin r) := (Submodule.mem_inf.mp (Submodule.mem_inf.mp hf).1).2
  refine Formalism.GM.TM.mem_intPol_of_norm _ fun m => ?_
  rw [Formalism.GM.MeanGammaLemmas.coeff_initPart]
  split_ifs
  · exact Formalism.CountingSumsFrames.intPol_norm f hfI m
  · simp

/- English proof (translation)
Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨f, hf, rfl⟩`. Establish `hfM : f ∈ MMw p LLw J M ρ w` using `(Submodule.mem_inf.mp (Submodule.mem_inf.mp hf).1).1`. Establish `hfP : f ∈ Pol p r LLw` using `(Submodule.mem_inf.mp (Submodule.mem_inf.mp (Submodule.mem_inf.mp hfM).1).1).1`. Use `show initPart v e f ∈ Pol p r LLw`.

Unfold `Pol at hfP ⊢`. Rewrite `hfP`, the goal using `[mem_restrictSupport_iff]`. Introduce `m hm`. Rewrite `hm` using `[Finset.mem_coe, mem_support_iff, Formalism.GM.MeanGammaLemmas.coeff_initPart]`. Use `hfP (Finset.mem_coe.mpr (mem_support_iff.mpr ?_))` and prove the remaining obligations.

Introduce `h0`. Apply `hm` to reduce the goal to its premises. Rewrite using `[h0, ite_self]`.
-/
theorem grLat_le_pol (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r)
    (w : Fin r → ℤ) (v : Fin (K + 1) × Fin r) (e : ℕ) :
    grLat p LLw J M ρ w v e ≤ (Pol p r LLw).restrictScalars ℤ_[p] := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨f, hf, rfl⟩
  have hfM : f ∈ MMw p LLw J M ρ w := (Submodule.mem_inf.mp (Submodule.mem_inf.mp hf).1).1
  have hfP : f ∈ Pol p r LLw :=
    (Submodule.mem_inf.mp (Submodule.mem_inf.mp (Submodule.mem_inf.mp hfM).1).1).1
  show initPart v e f ∈ Pol p r LLw
  unfold Pol at hfP ⊢
  rw [mem_restrictSupport_iff] at hfP ⊢
  intro m hm
  rw [Finset.mem_coe, mem_support_iff, Formalism.GM.MeanGammaLemmas.coeff_initPart] at hm
  refine hfP (Finset.mem_coe.mpr (mem_support_iff.mpr ?_))
  intro h0
  apply hm
  rw [h0, ite_self]

end Gr

/- English proof (translation)
Introduce `p _ K r _ LLw q J M ρ w e D c κ hProj hSat hκ k g hli hspan`. Establish `hp1 : (1 : ℝ) < p` using `by exact_mod_cast (Fact.out : p.Prime).one_lt`. Establish `hp0 : (0 : ℝ) < p` using `by linarith`. Establish `hpQ : (p : ℚ_[p]) ≠ 0` using `by exact_mod_cast (Fact.out : p.Prime).ne_zero`. Take `⟨Pr, hPr⟩` from `hProj`.

Establish `key` using `partner_determinant_holds p (MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (Formalism.GM.TM.fockBil LLw LinearMap.id) k g κ hli ?_`. Conclude with `key`. Introduce `u hu hprim`. Rewrite `hu`, `hprim` using `[hspan]`. Use `set Gr := grLat p LLw J M ρ w (Fin.last K, ρ) e with hGr`.

Use `set XX := grSpan p LLw J M ρ w e with hXX`. Establish `hGX : ∀ x ∈ Gr, x ∈ XX` using `fun x hx => Submodule.subset_span hx`. Establish `hu0 : u ≠ 0`. Introduce `h0`. Use `hprim 0 0 (Submodule.zero_mem _) (by rw [h0, smul_zero])` as an intermediate fact.

Conclude with `not_isUnit_zero this`. Establish `huI : u ∈ IntPol p (Fin (K + 1) × Fin r)` using `grLat_le_int LLw J M ρ w _ e hu`. Establish `huP : u ∈ Pol p r LLw` using `grLat_le_pol LLw J M ρ w _ e hu`. Establish `hne : u.support.Nonempty` using `by rwa [Finset.nonempty_iff_ne_empty, Ne, support_eq_empty]`. Take `⟨m, hm, hmax⟩` from `Finset.exists_max_image u.support (fun m => ‖coeff m u‖) hne`.

Use `set a := coeff m u with ha`. Establish `ha0 : a ≠ 0` using `mem_support_iff.mp hm`. Establish `han : 0 < ‖a‖` using `norm_pos_iff.mpr ha0`. Establish `hmD : MultiDeg LLw m`. Unfold `Pol at huP`.

Rewrite `huP` using `[mem_restrictSupport_iff]`. Conclude with `huP (Finset.mem_coe.mpr hm)`. Use `set u0 := a⁻¹ • u with hu0def`. Establish `hu0I : u0 ∈ IntPol p (Fin (K + 1) × Fin r)`. Use `Formalism.GM.TM.mem_intPol_of_norm _ fun m' => ?_` and prove the remaining obligations.

Rewrite using `[hu0def, coeff_smul, smul_eq_mul, norm_mul, norm_inv, inv_mul_le_iff₀ han, mul_one]`. Distinguish the cases in `hm' : m' ∈ u.support`. Conclude with `hmax m' hm'`. Rewrite using `[notMem_support_iff.mp hm', norm_zero]`. Conclude with `han.le`.

Establish `hu0X : u0 ∈ XX` using `XX.smul_mem _ (hGX u hu)`. Establish `hu0c : ‖coeff m u0‖ = 1`. Rewrite using `[hu0def, coeff_smul, smul_eq_mul, ← ha, inv_mul_cancel₀ ha0, norm_one]`. Establish `huu0 : u = a • u0` using `by rw [hu0def, smul_smul, mul_inv_cancel₀ ha0, one_smul]`. Establish `hy : ((p : ℚ_[p]) ^ c) • u0 ∈ Gr` using `hSat u0 hu0X hu0I`.

Establish `hpc : ((p : ℚ_[p]) ^ c) ≠ 0` using `pow_ne_zero _ hpQ`. Establish `hnpc : ‖(p : ℚ_[p]) ^ c‖ = ((p : ℝ) ^ c)⁻¹` using `by rw [norm_pow, Padic.norm_p, inv_pow]`. Establish `hnpD : ‖(p : ℚ_[p]) ^ D‖ = ((p : ℝ) ^ D)⁻¹` using `by rw [norm_pow, Padic.norm_p, inv_pow]`. Establish `hage : ((p : ℝ) ^ c)⁻¹ ≤ ‖a‖`. Assume the negation of the conclusion as `hlt`.

Use `push Not at hlt`. Establish `hb : ‖a / (p : ℚ_[p]) ^ c‖ < 1`. Rewrite using `[norm_div, hnpc, div_inv_eq_mul]`. Establish `hpc' : (0 : ℝ) < (p : ℝ) ^ c` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.

Set `b : ℤ_[p]` to `⟨a / (p : ℚ_[p]) ^ c, hb.le⟩`. Establish `hub : u = b • (((p : ℚ_[p]) ^ c) • u0)`. Rewrite using `[← algebraMap_smul ℚ_[p] b, PadicInt.algebraMap_apply, smul_smul]`. Use `show u = (a / (p : ℚ_[p]) ^ c * (p : ℚ_[p]) ^ c) • u0`. Rewrite using `[div_mul_cancel₀ _ hpc]`.

Conclude with `huu0`. Establish `hunit` using `hprim b _ hy hub`. Rewrite `hunit` using `[PadicInt.isUnit_iff]`. Establish `: ‖b‖ = ‖a / (p : ℚ_[p]) ^ c‖` using `rfl`. Combine the linear equalities and inequalities to obtain the conclusion.

Take `⟨hP1, hP2, hP3⟩` from `hPr m hmD`. Use `⟨((p : ℚ_[p]) ^ c) • (((p : ℚ_[p]) ^ D) • Pr (monomial m 1)), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hspan]`. Conclude with `hSat _ (XX.smul_mem _ hP1) hP2`. Rewrite using `[Formalism.GM.TM.fockBil_apply, LinearMap.id_apply, Formalism.CountingSumsFrames.fockN_smul_right', Formalism.CountingSumsFrames.fockN_smul_right']`.

Establish `e1 : fockN p LLw u (Pr (monomial m 1)) = a * fockN p LLw u0 (monomial m 1)`. Unfold `fockN`. Rewrite using `[hP3 u (hGX u hu)]`. Use `conv_lhs => rw [huu0]`. Rewrite using `[Formalism.GM.TM.fock_smul_left, mul_div_assoc]`.

Establish `e2` using `Formalism.CountingSumsFrames.fockN_monomial_ge LLw u0 m hmD hu0c`. Rewrite using `[e1, norm_mul, norm_mul, norm_mul, hnpc, hnpD]`. Establish `hpc' : (0 : ℝ) < ((p : ℝ) ^ c)⁻¹` using `by positivity`. Establish `hpD' : (0 : ℝ) < ((p : ℝ) ^ D)⁻¹` using `by positivity`. Establish `h1 : (p : ℝ) ^ (-κ) ≤ (p : ℝ) ^ (-((D + 2 * c : ℕ) : ℝ))` using `Real.rpow_le_rpow_of_exponent_le hp1.le (by linarith)`.

Establish `h2 : (p : ℝ) ^ (-((D + 2 * c : ℕ) : ℝ)) = ((p : ℝ) ^ c)⁻¹ * (((p : ℝ) ^ D)⁻¹ * (((p : ℝ) ^ c)⁻¹ * 1))`. Rewrite using `[Real.rpow_neg hp0.le, Real.rpow_natCast, pow_add, two_mul, pow_add]`. Clear the denominators using the available nonvanishing facts. Rewrite `h1` using `[h2]`. Use `h1.trans ?_` and prove the remaining obligations.

Use `gcongr`.
-/
theorem graded_piece_bound_holds : GradedPieceBound := by
  intro p _ K r _ LLw q J M ρ w e D c κ hProj hSat hκ k g hli hspan
  classical
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hpQ : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  obtain ⟨Pr, hPr⟩ := hProj
  have key := partner_determinant_holds p (MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (Formalism.GM.TM.fockBil LLw LinearMap.id) k g κ hli
    ?_
  · exact key
  intro u hu hprim
  rw [hspan] at hu hprim
  set Gr := grLat p LLw J M ρ w (Fin.last K, ρ) e with hGr
  set XX := grSpan p LLw J M ρ w e with hXX
  have hGX : ∀ x ∈ Gr, x ∈ XX := fun x hx => Submodule.subset_span hx
  have hu0 : u ≠ 0 := by
    intro h0
    have := hprim 0 0 (Submodule.zero_mem _) (by rw [h0, smul_zero])
    exact not_isUnit_zero this
  have huI : u ∈ IntPol p (Fin (K + 1) × Fin r) := grLat_le_int LLw J M ρ w _ e hu
  have huP : u ∈ Pol p r LLw := grLat_le_pol LLw J M ρ w _ e hu
  have hne : u.support.Nonempty := by rwa [Finset.nonempty_iff_ne_empty, Ne, support_eq_empty]
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image u.support (fun m => ‖coeff m u‖) hne
  set a := coeff m u with ha
  have ha0 : a ≠ 0 := mem_support_iff.mp hm
  have han : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  have hmD : MultiDeg LLw m := by
    unfold Pol at huP
    rw [mem_restrictSupport_iff] at huP
    exact huP (Finset.mem_coe.mpr hm)
  set u0 := a⁻¹ • u with hu0def
  have hu0I : u0 ∈ IntPol p (Fin (K + 1) × Fin r) := by
    refine Formalism.GM.TM.mem_intPol_of_norm _ fun m' => ?_
    rw [hu0def, coeff_smul, smul_eq_mul, norm_mul, norm_inv, inv_mul_le_iff₀ han, mul_one]
    by_cases hm' : m' ∈ u.support
    · exact hmax m' hm'
    · rw [notMem_support_iff.mp hm', norm_zero]; exact han.le
  have hu0X : u0 ∈ XX := XX.smul_mem _ (hGX u hu)
  have hu0c : ‖coeff m u0‖ = 1 := by
    rw [hu0def, coeff_smul, smul_eq_mul, ← ha, inv_mul_cancel₀ ha0, norm_one]
  have huu0 : u = a • u0 := by rw [hu0def, smul_smul, mul_inv_cancel₀ ha0, one_smul]
  have hy : ((p : ℚ_[p]) ^ c) • u0 ∈ Gr := hSat u0 hu0X hu0I
  have hpc : ((p : ℚ_[p]) ^ c) ≠ 0 := pow_ne_zero _ hpQ
  have hnpc : ‖(p : ℚ_[p]) ^ c‖ = ((p : ℝ) ^ c)⁻¹ := by rw [norm_pow, Padic.norm_p, inv_pow]
  have hnpD : ‖(p : ℚ_[p]) ^ D‖ = ((p : ℝ) ^ D)⁻¹ := by rw [norm_pow, Padic.norm_p, inv_pow]

  have hage : ((p : ℝ) ^ c)⁻¹ ≤ ‖a‖ := by
    by_contra hlt
    push Not at hlt
    have hb : ‖a / (p : ℚ_[p]) ^ c‖ < 1 := by
      rw [norm_div, hnpc, div_inv_eq_mul]
      have hpc' : (0 : ℝ) < (p : ℝ) ^ c := by positivity
      calc ‖a‖ * (p : ℝ) ^ c < ((p : ℝ) ^ c)⁻¹ * (p : ℝ) ^ c := mul_lt_mul_of_pos_right hlt hpc'
        _ = 1 := inv_mul_cancel₀ hpc'.ne'
    let b : ℤ_[p] := ⟨a / (p : ℚ_[p]) ^ c, hb.le⟩
    have hub : u = b • (((p : ℚ_[p]) ^ c) • u0) := by
      rw [← algebraMap_smul ℚ_[p] b, PadicInt.algebraMap_apply, smul_smul]
      show u = (a / (p : ℚ_[p]) ^ c * (p : ℚ_[p]) ^ c) • u0
      rw [div_mul_cancel₀ _ hpc]; exact huu0
    have hunit := hprim b _ hy hub
    rw [PadicInt.isUnit_iff] at hunit
    have : ‖b‖ = ‖a / (p : ℚ_[p]) ^ c‖ := rfl
    linarith
  obtain ⟨hP1, hP2, hP3⟩ := hPr m hmD
  refine ⟨((p : ℚ_[p]) ^ c) • (((p : ℚ_[p]) ^ D) • Pr (monomial m 1)), ?_, ?_⟩
  · rw [hspan]
    exact hSat _ (XX.smul_mem _ hP1) hP2
  · rw [Formalism.GM.TM.fockBil_apply, LinearMap.id_apply, Formalism.CountingSumsFrames.fockN_smul_right', Formalism.CountingSumsFrames.fockN_smul_right']
    have e1 : fockN p LLw u (Pr (monomial m 1)) = a * fockN p LLw u0 (monomial m 1) := by
      unfold fockN
      rw [hP3 u (hGX u hu)]
      conv_lhs => rw [huu0]
      rw [Formalism.GM.TM.fock_smul_left, mul_div_assoc]
    have e2 := Formalism.CountingSumsFrames.fockN_monomial_ge LLw u0 m hmD hu0c
    rw [e1, norm_mul, norm_mul, norm_mul, hnpc, hnpD]
    have hpc' : (0 : ℝ) < ((p : ℝ) ^ c)⁻¹ := by positivity
    have hpD' : (0 : ℝ) < ((p : ℝ) ^ D)⁻¹ := by positivity
    have h1 : (p : ℝ) ^ (-κ) ≤ (p : ℝ) ^ (-((D + 2 * c : ℕ) : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hp1.le (by linarith)
    have h2 : (p : ℝ) ^ (-((D + 2 * c : ℕ) : ℝ)) = ((p : ℝ) ^ c)⁻¹ * (((p : ℝ) ^ D)⁻¹ * (((p : ℝ) ^ c)⁻¹ * 1)) := by
      rw [Real.rpow_neg hp0.le, Real.rpow_natCast, pow_add, two_mul, pow_add]
      field_simp
    rw [h2] at h1
    refine h1.trans ?_
    gcongr

end Formalism.InvariantFactorPaths.L4
