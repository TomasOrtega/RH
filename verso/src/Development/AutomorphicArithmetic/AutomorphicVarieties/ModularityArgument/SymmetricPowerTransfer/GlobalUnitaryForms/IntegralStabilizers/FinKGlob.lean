import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.FinKLoc
import GroundTheory.GlobalFields.Adele.Approximation

noncomputable section

namespace UpperTheory.V.Z.Sym.Glob.FK

open NumberField IsDedekindDomain Matrix Loc

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lmap_re {K K' : Type} [Field K] [Field K'] (f : K →+* K') {Δ : K} (x : Lsq K Δ) : (lmap f Δ x).re = f x.re := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lmap_im {K K' : Type} [Field K] [Field K'] (f : K →+* K') {Δ : K} (x : Lsq K Δ) : (lmap f Δ x).im = f x.im := rfl

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Supply the required witnesses or components.
-/
theorem int_iff (v : Pl F) (x : Kv v) : IsIntegral (Ov v) x ↔ x ∈ v.adicCompletionIntegers F := by
  rw [IsIntegrallyClosed.isIntegral_iff]
  exact ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩

/- English proof (translation)
Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem int_glob (x : F) : IsIntegral ℤ x ↔ ∀ v : Pl F, IsIntegral (Ov v) (cv v x) := by
  simp only [int_iff]
  refine ⟨fun h v => HeightOneSpectrum.coe_algebraMap_mem (𝓞 F) F v ⟨x, h⟩, fun h => ?_⟩
  obtain ⟨z, hz⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F x fun v =>
    (GroundTheory.Global.coe_mem_adicCompletionIntegers_iff v x).1 (h v)
  rw [← hz]
  exact RingOfIntegers.isIntegral_coe z

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the indicated hypotheses using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Rewrite the indicated hypotheses using the stated equalities.

Simplify to obtain the desired conclusion from the available facts. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts.
-/
theorem den_glob (x : F) : ∃ c : ℕ, c ≠ 0 ∧ IsIntegral ℤ ((c : F) * x) := by
  obtain ⟨m, hm0, hm⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x)).exists_integral_multiple
  refine ⟨m.natAbs, Int.natAbs_ne_zero.2 hm0, ?_⟩
  rw [zsmul_eq_mul] at hm
  rcases Int.natAbs_eq m with h | h
  · rw [h] at hm; simpa using hm
  · rw [h] at hm; simpa using hm.neg

/- English proof (translation)
Introduce a local definition for the expression. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem approx_F (a : ∀ v : Pl F, Kv v) {e f : F} (he : e ≠ 0) (hf : f ≠ 0) (ha : ∀ v, IsIntegral (Ov v) (cv v e * a v)) :
    ∃ x : F, ∀ v, ∃ r, IsIntegral (Ov v) r ∧ a v = cv v x + cv v f * r := by
  let b : FiniteAdeleRing (𝓞 F) F := ⟨fun v => cv v e * a v, Filter.Eventually.of_forall fun v => (int_iff v _).1 (ha v)⟩
  obtain ⟨k, hk⟩ := GroundTheory.Global.exists_sub_mem_integralFiniteAdeles (algebraMap F (FiniteAdeleRing (𝓞 F) F) (e * f)⁻¹ * b)
  refine ⟨f * k, fun v => ⟨cv v (e * f)⁻¹ * (cv v e * a v) - cv v k, (int_iff v _).2 (hk v), ?_⟩⟩
  have h1 : cv v e ≠ 0 := (map_ne_zero _).2 he
  have h2 : cv v f ≠ 0 := (map_ne_zero _).2 hf
  rw [map_inv₀, map_mul, map_mul]
  field_simp
  ring

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem den_loc (v : Pl F) (x : Kv v) : ∃ n : ℕ, n ≠ 0 ∧ IsIntegral (Ov v) ((n : Kv v) * x) := by
  have hU : IsOpen {w : Kv v | x - w ∈ v.adicCompletionIntegers F} :=
    (Valued.isOpen_valuationSubring (Kv v)).preimage (continuous_const.sub continuous_id)
  obtain ⟨z, hz⟩ := (HeightOneSpectrum.denseRange_algebraMap (K := F) v).exists_mem_open hU ⟨x, by simp⟩
  obtain ⟨n, hn, h⟩ := den_glob z
  refine ⟨n, hn, ?_⟩
  have h1 := (int_glob _).1 h v
  rw [map_mul, map_natCast] at h1
  have e : (n : Kv v) * x = n * cv v z + n * (x - cv v z) := by ring
  rw [e]
  exact h1.add ((isIntegral_natCast (R := Ov v) (B := Kv v) n).mul ((int_iff v _).2 hz))

variable {Δ : F}

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem int_cD {c : ℕ} (hc : IsIntegral ℤ ((c : F) * Δ)) (v : Pl F) : IsIntegral (Ov v) ((c : Kv v) * cv v Δ) := by
  have h1 := (int_glob _).1 hc v
  rwa [map_mul, map_natCast] at h1

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem approx_L (hΔ : Δ ≠ 0) (a : ∀ v : Pl F, Lsq (Kv v) (cv v Δ)) (ha : ∀ v, IsIntegral (Ov v) (a v)) {n : ℕ} (hn : n ≠ 0) :
    ∃ x : Lsq F Δ, ∀ v, ∃ r, IsIntegral (Ov v) r ∧ a v = lmap (cv v) Δ x + n • r := by
  obtain ⟨c, hc0, hc⟩ := den_glob Δ
  have hn' : (n : F) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hc' : (c : F) ≠ 0 := Nat.cast_ne_zero.2 hc0
  obtain ⟨x, hx⟩ := approx_F (fun v => (a v).re) (e := 2) two_ne_zero hn' fun v => by
    rw [map_ofNat]; exact int_re _ (ha v)
  obtain ⟨y, hy⟩ := approx_F (fun v => (a v).im) (e := 2 * c * Δ) (by simp [hc0, hΔ]) (mul_ne_zero hn' hc') fun v => by
    rw [map_mul, map_mul, map_ofNat, map_natCast]; exact int_im _ (int_cD hc v) (ha v)
  refine ⟨⟨x, y⟩, fun v => ?_⟩
  obtain ⟨r, hr, e1⟩ := hx v
  obtain ⟨s, hs, e2⟩ := hy v
  refine ⟨_, int_mk _ (int_cD hc v) hr hs, ?_⟩
  ext : 1
  · rw [e1]; simp [lmap]
  · rw [e2]; simp [lmap, mul_assoc]

variable (Δ)

abbrev MM : Type := ∀ v : Pl F, Matrix (Fin 2) (Fin 2) (Lsq (Kv v) (cv v Δ))

def RR : Subring (MM Δ) := ⨅ v, (RL (cv v Δ) (Ov v)).comap (Pi.evalRingHom _ v)

def jj : Matrix (Fin 2) (Fin 2) (Lsq F Δ) →+* MM Δ := Pi.ringHom fun v => (lmap (cv v) Δ).mapMatrix

variable {Δ}

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem mem_RR {m : MM Δ} : m ∈ RR Δ ↔ ∀ v, m v ∈ RL (cv v Δ) (Ov v) := Subring.mem_iInf

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem jj_apply (y : Matrix (Fin 2) (Fin 2) (Lsq F Δ)) (v : Pl F) : jj Δ y v = y.map (lmap (cv v) Δ) := rfl

/- English proof (translation)
Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem pl_ne : Nonempty (Pl F) := by
  obtain ⟨I, hI⟩ := Ideal.exists_maximal (𝓞 F)
  exact ⟨⟨I, hI.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hI (RingOfIntegers.not_isField F)⟩⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem lam_shape {y : Matrix (Fin 2) (Fin 2) (Lsq F Δ)} (h : y ∈ (RR Δ).comap (jj Δ)) : Shape y := by
  obtain ⟨v⟩ := pl_ne (F := F)
  exact shape_of_map (cv v) (mem_RR.1 h v).1

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Use the resulting assumption. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Use the resulting assumption.
-/
theorem lam_int {c : ℕ} (hc : IsIntegral ℤ ((c : F) * Δ)) {y : Matrix (Fin 2) (Fin 2) (Lsq F Δ)} (h : y ∈ (RR Δ).comap (jj Δ)) (i j : Fin 2) :
    IsIntegral ℤ (2 * (y i j).re) ∧ IsIntegral ℤ (2 * c * Δ * (y i j).im) := by
  have h1 : ∀ v : Pl F, IsIntegral (Ov v) (lmap (cv v) Δ (y i j)) := fun v => by
    have h2 := (mem_RR.1 (Subring.mem_comap.1 h) v).2 i j
    rwa [jj_apply, Matrix.map_apply] at h2
  refine ⟨(int_glob _).2 fun v => ?_, (int_glob _).2 fun v => ?_⟩
  · have h2 := int_re _ (h1 v)
    rw [lmap_re] at h2
    rwa [map_mul, map_ofNat]
  · have h2 := int_im _ (int_cD hc v) (h1 v)
    rw [lmap_im] at h2
    rwa [map_mul, map_mul, map_mul, map_ofNat, map_natCast]

/- English proof (translation)
Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Apply function extensionality and compare values at an arbitrary argument. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem lam_fg (hΔ : Δ ≠ 0) : Module.Finite ℤ ((RR Δ).comap (jj Δ)) := by
  obtain ⟨c, hc0, hc⟩ := den_glob Δ
  let ψ : (RR Δ).comap (jj Δ) →+ (Fin 2 → Fin 2 → 𝓞 F × 𝓞 F) := AddMonoidHom.mk'
    (fun y i j => (⟨_, (lam_int hc y.2 i j).1⟩, ⟨_, (lam_int hc y.2 i j).2⟩)) fun x y => by
      funext i j
      refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
      · exact mul_add _ _ _
      · exact mul_add _ _ _
  refine Module.Finite.of_injective ψ.toIntLinearMap fun x y h => Subtype.ext (Matrix.ext fun i j => ?_)
  have h1 := congrFun (congrFun h i) j
  exact QuadraticAlgebra.ext (mul_left_cancel₀ two_ne_zero (congrArg Subtype.val (congrArg Prod.fst h1)))
    (mul_left_cancel₀ (by simp [hc0, hΔ]) (congrArg Subtype.val (congrArg Prod.snd h1)))

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem approx_R (hΔ : Δ ≠ 0) : ∀ m ∈ RR Δ, ∀ n : ℕ, n ≠ 0 → ∃ x ∈ (RR Δ).comap (jj Δ), ∃ r ∈ RR Δ, m = jj Δ x + (n : MM Δ) * r := by
  intro m hm n hn
  obtain ⟨a, ha⟩ := approx_L hΔ (fun v => m v 0 0) (fun v => (mem_RR.1 hm v).2 0 0) hn
  obtain ⟨b, hb⟩ := approx_L hΔ (fun v => m v 0 1) (fun v => (mem_RR.1 hm v).2 0 1) hn
  choose r hr ha using ha
  choose s hs hb using hb
  have h1 : (fun v => qm (r v) (s v) : MM Δ) ∈ RR Δ := mem_RR.2 fun v => qm_mem _ (hr v) (hs v)
  have e : m = jj Δ (qm a b) + (n : MM Δ) * fun v => qm (r v) (s v) := by
    funext v
    rw [← nsmul_eq_mul, Pi.add_apply, Pi.smul_apply, jj_apply, qm_map, (mem_RR.1 hm v).1.eq, ha v, hb v]
    ext i j : 1
    fin_cases i <;> fin_cases j <;> simp [qm, add_comm]
  refine ⟨qm a b, ?_, _, h1, e⟩
  rw [Subring.mem_comap, ← sub_eq_of_eq_add e]
  exact sub_mem hm (mul_mem (natCast_mem _ n) h1)

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem form_pos (hneg : ∀ σ : F →+* ℝ, σ Δ < 0) (σ : F →+* ℝ) (a b : Lsq F Δ) :
    let d := σ (a.re ^ 2 - Δ * a.im ^ 2 + b.re ^ 2 - Δ * b.im ^ 2)
    σ a.re ^ 2 ≤ d ∧ σ b.re ^ 2 ≤ d ∧ -σ Δ * σ a.im ^ 2 ≤ d ∧ -σ Δ * σ b.im ^ 2 ≤ d := by
  have h := hneg σ
  have h1 : 0 ≤ -σ Δ * σ a.im ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have h2 : 0 ≤ -σ Δ * σ b.im ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  simp only [map_add, map_sub, map_mul, map_pow]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [sq_nonneg (σ a.re), sq_nonneg (σ b.re)]

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem real_emb [IsTotallyReal F] (φ : F →+* ℂ) : ∃ σ : F →+* ℝ, ∀ x, (σ x : ℂ) = φ x :=
  ⟨(IsTotallyReal.complexEmbedding_isReal φ).embedding, fun x => ComplexEmbedding.IsReal.coe_embedding_apply _ x⟩

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem unit_of_shape [IsTotallyReal F] (hneg : ∀ σ : F →+* ℝ, σ Δ < 0) {y : Matrix (Fin 2) (Fin 2) (Lsq F Δ)} (h : Shape y) (h0 : y ≠ 0) :
    ∃ g : DX Δ, mt g = y := by
  rw [h.eq]
  refine exists_DX fun hd => h0 ?_
  obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
  obtain ⟨σ, -⟩ := real_emb φ
  have := form_pos hneg σ (y 0 0) (y 0 1)
  rw [hd, map_zero] at this
  obtain ⟨h1, h2, h3, h4⟩ := this
  have hσ := hneg σ
  have z : ∀ x : F, σ x ^ 2 ≤ 0 → x = 0 := fun x hx => (map_eq_zero σ).1 (pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm hx (sq_nonneg _)))
  have a0 : y 0 0 = 0 := QuadraticAlgebra.ext (z _ h1) (z _ (by nlinarith [sq_nonneg (σ (y 0 0).im)]))
  have b0 : y 0 1 = 0 := QuadraticAlgebra.ext (z _ h2) (z _ (by nlinarith [sq_nonneg (σ (y 0 1).im)]))
  rw [h.eq, a0, b0]
  ext i j : 1
  fin_cases i <;> fin_cases j <;> simp [qm]

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem box_fin [IsTotallyReal F] {e : F} (he : e ≠ 0) (d : F) :
    {x : F | IsIntegral ℤ (e * x) ∧ ∀ σ : F →+* ℝ, σ (e * x) ^ 2 ≤ σ d}.Finite := by
  have h := Embeddings.finite_of_norm_le F ℂ (∑ φ : F →+* ℂ, (‖φ d‖ + 1))
  refine (h.preimage (f := fun x : F => e * x) (mul_right_injective₀ he).injOn).subset ?_
  rintro x ⟨hx, hA⟩
  refine ⟨hx, fun φ => ?_⟩
  refine le_trans ?_ (Finset.single_le_sum (f := fun φ : F →+* ℂ => ‖φ d‖ + 1) (fun _ _ => by positivity) (Finset.mem_univ φ))
  obtain ⟨σ, hσ⟩ := real_emb φ
  have h1 := hA σ
  rw [← hσ, ← hσ, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  rw [← sq_abs] at h1
  nlinarith [le_abs_self (σ d), abs_nonneg (σ (e * x)), sq_nonneg (|σ (e * x)| - 1), abs_nonneg (σ d)]

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Simplify using the standard rewrite rules. Use the polynomial consequences of the given equalities and inequalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Supply the required witnesses or components.
-/
theorem det_fin [IsTotallyReal F] (hneg : ∀ σ : F →+* ℝ, σ Δ < 0) (hΔ : Δ ≠ 0) (d : Lsq F Δ) :
    {y : Matrix (Fin 2) (Fin 2) (Lsq F Δ) | y ∈ (RR Δ).comap (jj Δ) ∧ y.det = d}.Finite := by
  obtain ⟨c, hc0, hc⟩ := den_glob Δ
  have h1 := box_fin (F := F) (e := 2) two_ne_zero (4 * d.re)
  have h2 := box_fin (F := F) (e := 2 * c * Δ) (by simp [hc0, hΔ]) (-(4 * c ^ 2 * Δ) * d.re)
  refine ((((h1.prod h2).prod (h1.prod h2)).image fun p => qm ⟨p.1.1, p.1.2⟩ ⟨p.2.1, p.2.2⟩)).subset ?_
  rintro y ⟨hy, hd⟩
  have hs := lam_shape hy
  refine ⟨(((y 0 0).re, (y 0 0).im), ((y 0 1).re, (y 0 1).im)), ?_, hs.eq.symm⟩
  rw [hs.eq, det_qm] at hd
  have hd' : d.re = (y 0 0).re ^ 2 - Δ * (y 0 0).im ^ 2 + (y 0 1).re ^ 2 - Δ * (y 0 1).im ^ 2 := by rw [← hd]; rfl
  have k1 : ∀ (σ : F →+* ℝ) (x : F), σ x ^ 2 ≤ σ d.re → σ (2 * x) ^ 2 ≤ σ (4 * d.re) := fun σ x h => by
    simp only [map_mul, map_ofNat]; nlinarith
  have k2 : ∀ (σ : F →+* ℝ) (x : F), -σ Δ * σ x ^ 2 ≤ σ d.re → σ (2 * c * Δ * x) ^ 2 ≤ σ (-(4 * c ^ 2 * Δ) * d.re) := fun σ x h => by
    simp only [map_mul, map_ofNat, map_neg, map_pow, map_natCast]
    have := mul_le_mul_of_nonneg_left h (show 0 ≤ 4 * (c : ℝ) ^ 2 * -σ Δ from mul_nonneg (by positivity) (by linarith [hneg σ]))
    nlinarith
  have f := fun σ => form_pos hneg σ (y 0 0) (y 0 1)
  rw [← hd'] at f
  exact ⟨⟨⟨(lam_int hc hy 0 0).1, fun σ => k1 σ _ (f σ).1⟩, (lam_int hc hy 0 0).2, fun σ => k2 σ _ (f σ).2.2.1⟩,
    ⟨(lam_int hc hy 0 1).1, fun σ => k1 σ _ (f σ).2.1⟩, (lam_int hc hy 0 1).2, fun σ => k2 σ _ (f σ).2.2.2⟩

variable (Δ) in

def rho : DA Δ →* MM Δ where
  toFun g v := mt (g.1 v)
  map_one' := rfl
  map_mul' _ _ := rfl

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails.

Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem den_rho (g : DA Δ) : ∃ n : ℕ, n ≠ 0 ∧ (n : MM Δ) * rho Δ g ∈ RR Δ := by
  obtain ⟨c, hc0, hc⟩ := den_glob Δ
  have hT : {v : Pl F | g.1 v ∉ KD (cv v Δ) (Ov v)}.Finite := Filter.eventually_cofinite.1 g.2
  choose n hn0 hn using fun v : Pl F => den_mat (Ov v) (c := c)
    (by rw [← map_natCast (cv v)]; exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hc0)) (int_cD hc v) (den_loc v) (shape_mt (g.1 v))
  refine ⟨∏ v ∈ hT.toFinset, n v, Finset.prod_ne_zero_iff.2 fun v _ => hn0 v, mem_RR.2 fun v => ?_⟩
  rw [← nsmul_eq_mul, Pi.smul_apply]
  by_cases hv : g.1 v ∈ KD (cv v Δ) (Ov v)
  · exact nsmul_mem ((mem_KD _ _).1 hv).1 _
  · obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem n (hT.mem_toFinset.2 hv)
    rw [hk, mul_nsmul, nsmul_eq_mul (n v)]
    exact nsmul_mem (hn v) k

end UpperTheory.V.Z.Sym.Glob.FK
