import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.ApartOfNotMem
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct

/- English proof (translation)
Take `⟨a, rfl⟩` from `T.Φ_surj x`. Take `⟨b, rfl⟩` from `T.Φ_surj y`. Rewrite using `[← map_mul, T.Φ_int]`. Introduce `w hw`. Rewrite using `[map_mul, map_mul]`.

Conclude with `mul_le_one' ((T.Φ_int a).1 hx w hw) ((T.Φ_int b).1 hy w hw)`.
-/
private theorem ohat_mul {E : Type} [Field E] [NumberField E] [IsCMField E] {p : ℕ} (T : AdT p E)
    {x y : AfP p ⊗[ℚ] E} (hx : x ∈ OHat p E) (hy : y ∈ OHat p E) : x * y ∈ OHat p E := by
  obtain ⟨a, rfl⟩ := T.Φ_surj x
  obtain ⟨b, rfl⟩ := T.Φ_surj y
  rw [← map_mul, T.Φ_int]
  intro w hw
  rw [map_mul, map_mul]
  exact mul_le_one' ((T.Φ_int a).1 hx w hw) ((T.Φ_int b).1 hy w hw)

/- English proof (translation)
Rewrite using `[← map_one T.Φ, T.Φ_int]`. Introduce `w hw`. Simplify using the standard rewrite rules.
-/
private theorem one_mem_ohat {E : Type} [Field E] [NumberField E] [IsCMField E] {p : ℕ} (T : AdT p E) :
    (1 : AfP p ⊗[ℚ] E) ∈ OHat p E := by
  rw [← map_one T.Φ, T.Φ_int]
  intro w hw
  simp

/- English proof (translation)
Introduce `hL E _ _ _ A n p _ S T g`. Take `⟨ν, -, hact, hlat⟩` from `hL E A n p S T.μ T.mu`. Establish `hM : T.μ (S.mx (T.j g)) = (T.a * mat g * T.a⁻¹).val.map T.Φ` using `T.j_mx g`. Generalize the expression as in `hY : T.a * mat g * T.a⁻¹ = Y at hM ⊢`. Establish `hactM : ∀ v, ν (S.L.actG (T.j g) v) = (Y.val.map T.Φ) *ᵥ ν v` using `fun v => by rw [hact, hM]`.

Establish `hcol : ∀ k i, ((Y.val.map T.Φ) *ᵥ (Pi.single k 1 : Fin n → AfP p ⊗[ℚ] E)) i = T.Φ (Y.val i k)`. Introduce `k i`. Simplify using `[Matrix.mulVec_single_one]`. Establish `hsingle : ∀ k, ν.symm (Pi.single k 1) ∈ LaHat S.D`. Introduce `k`.

Rewrite using `[hlat]`. Introduce `i`. Rewrite using `[ν.apply_symm_apply, Pi.single_apply]`. Use `split_ifs`. Conclude with `one_mem_ohat T.toAdT`.

Conclude with `zero_mem _`. Establish `hΦ1 : ∀ i k, T.Φ ((1 : Matrix (Fin n) (Fin n) (Af E)) i k) = (1 : Matrix (Fin n) (Fin n) (AfP p ⊗[ℚ] E)) i k`. Introduce `i k`. Rewrite using `[Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.

Establish `hw1 : ∀ (w : Plc E) i k, pLoc E w ((1 : Matrix (Fin n) (Fin n) (Af E)) i k) = (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i k`. Introduce `w i k`. Rewrite using `[Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Prove the components needed by the constructor for the conclusion.

Prove the components needed by the constructor for the conclusion. Introduce `h w hw i k`. Use `(hlat _).1 (h _ (hsingle k)) i` as an intermediate fact. Rewrite `this` using `[hactM, ν.apply_symm_apply, hcol, T.Φ_int]`. Conclude with `this w hw`.

Introduce `h v hv`. Rewrite using `[hlat]`. Introduce `i`. Rewrite using `[hactM]`. Establish `hv'` using `(hlat v).1 hv`.

Simplify using `only [Matrix.mulVec, dotProduct]`. Use `sum_mem fun k _ => ohat_mul T.toAdT ?_ (hv' k)` and prove the remaining obligations. Rewrite using `[Matrix.map_apply, T.Φ_int]`. Conclude with `fun w hw => h w hw i k`. Introduce `N hN`.

Prove the components needed by the constructor for the conclusion. Introduce `h w hw i k`. Take `⟨u, hu, e⟩` from `h _ (hsingle k)`. Establish `e2` using `congrFun (congrArg ν e) i`. Rewrite `e2` using `[hactM, ν.apply_symm_apply, hcol, map_add, map_nsmul, ν.apply_symm_apply]`.

Establish `hui` using `(hlat u).1 hu i`. Take `⟨x, hx⟩` from `T.Φ_surj (ν u i)`. Establish `hxi` using `(T.Φ_int x).1 (hx ▸ hui) w hw`. Establish `e3 : T.Φ (Y.val i k - (1 : Matrix (Fin n) (Fin n) (Af E)) i k - (N : Af E) * x) = 0`. Rewrite using `[map_sub, map_sub, map_mul, hΦ1, hx, map_natCast, e2, Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, Matrix.one_apply, Pi.single_apply]`.

Simplify using `[eq_comm]`. Establish `e4` using `(T.Φ_ker _).1 e3 w hw`. Rewrite `e4` using `[map_sub, map_sub, map_mul, hw1, map_natCast, sub_eq_zero, sub_eq_iff_eq_add']`. Establish `e5 : ((GeneralLinearGroup.map (pLoc E w) Y).val - 1) i k = (N : w.adicCompletion E) * pLoc E w x`. Rewrite using `[Matrix.sub_apply]`.

Use `show pLoc E w (Y.val i k) - _ = _`. Rewrite using `[e4]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e5, map_mul]`. Conclude with `mul_le_of_le_one_right' hxi`.

Introduce `h v hv`. Establish `hv'` using `(hlat v).1 hv`. Establish `hN0 : (N : E) ≠ 0` using `Nat.cast_ne_zero.2 hN.ne'`. Take `⟨Ninv, hNinvdef⟩ : ∃ Ninv : Af E, Ninv = algebraMap E (Af E) ((N : E)⁻¹)` from `⟨_, rfl⟩`. Establish `hNinv : (N : Af E) * Ninv = 1`.

Rewrite using `[hNinvdef, ← map_natCast (algebraMap E (Af E)) N, ← map_mul, mul_inv_cancel₀ hN0, map_one]`. Take `⟨C, hCdef⟩ : ∃ C : Matrix (Fin n) (Fin n) (AfP p ⊗[ℚ] E), ∀ i k, C i k = T.Φ (Ninv * (Y.val - 1) i k)` from `⟨Matrix.of fun i k => T.Φ (Ninv * (Y.val - 1) i k), fun _ _ => rfl⟩`. Establish `hC : Y.val.map T.Φ = 1 + ((N : AfP p ⊗[ℚ] E)) • C`. Use extensionality with `i k`. Rewrite using `[Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, ← hΦ1, hCdef, ← map_natCast T.Φ N, ← map_mul, ← map_add]`.

Use `congr 1`. Rewrite using `[← mul_assoc, hNinv, one_mul, Matrix.sub_apply]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨ν.symm (C *ᵥ ν v), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hlat]`.

Introduce `i`. Rewrite using `[ν.apply_symm_apply]`. Simplify using `only [Matrix.mulVec, dotProduct]`. Use `sum_mem fun k _ => ohat_mul T.toAdT ?_ (hv' k)` and prove the remaining obligations. Rewrite using `[hCdef, T.Φ_int]`.

Introduce `w hw`. Establish `h1` using `h w hw i k`. Establish `hp' : (N : w.adicCompletion E) * pLoc E w Ninv = 1`. Rewrite using `[← map_natCast (pLoc E w) N, ← map_mul, hNinv, map_one]`. Establish `h2 : (N : w.adicCompletion E) ≠ 0` using `left_ne_zero_of_mul_eq_one hp'`.

Establish `h3 : pLoc E w Ninv = (N : w.adicCompletion E)⁻¹` using `eq_inv_of_mul_eq_one_right hp'`. Establish `e : pLoc E w ((Y.val - 1) i k) = ((GeneralLinearGroup.map (pLoc E w) Y).val - 1) i k`. Rewrite using `[Matrix.sub_apply, map_sub, hw1, Matrix.sub_apply]`. Both sides reduce to the same expression. Rewrite using `[map_mul, h3, e, map_mul, map_inv₀]`.

Conclude with `(inv_mul_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 h2))).2 h1`. Apply `ν.injective` to reduce the goal to its premises. Rewrite using `[hactM, hC, map_add, map_nsmul, ν.apply_symm_apply, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Nat.cast_smul_eq_nsmul]`.
-/
theorem UpperTheory.Gal.W2.Seed.pKNIff :
    LatCoord → KNIff := by
  intro hL E _ _ _ A n p _ S T g
  obtain ⟨ν, -, hact, hlat⟩ := hL E A n p S T.μ T.mu
  have hM : T.μ (S.mx (T.j g)) = (T.a * mat g * T.a⁻¹).val.map T.Φ := T.j_mx g
  generalize hY : T.a * mat g * T.a⁻¹ = Y at hM ⊢
  have hactM : ∀ v, ν (S.L.actG (T.j g) v) = (Y.val.map T.Φ) *ᵥ ν v := fun v => by rw [hact, hM]
  have hcol : ∀ k i, ((Y.val.map T.Φ) *ᵥ (Pi.single k 1 : Fin n → AfP p ⊗[ℚ] E)) i = T.Φ (Y.val i k) := by
    intro k i
    simp [Matrix.mulVec_single_one]
  have hsingle : ∀ k, ν.symm (Pi.single k 1) ∈ LaHat S.D := by
    intro k
    rw [hlat]
    intro i
    rw [ν.apply_symm_apply, Pi.single_apply]
    split_ifs
    · exact one_mem_ohat T.toAdT
    · exact zero_mem _
  have hΦ1 : ∀ i k, T.Φ ((1 : Matrix (Fin n) (Fin n) (Af E)) i k) = (1 : Matrix (Fin n) (Fin n) (AfP p ⊗[ℚ] E)) i k := by
    intro i k
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hw1 : ∀ (w : Plc E) i k, pLoc E w ((1 : Matrix (Fin n) (Fin n) (Af E)) i k) = (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i k := by
    intro w i k
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  constructor
  · constructor
    · intro h w hw i k
      have := (hlat _).1 (h _ (hsingle k)) i
      rw [hactM, ν.apply_symm_apply, hcol, T.Φ_int] at this
      exact this w hw
    · intro h v hv
      rw [hlat]
      intro i
      rw [hactM]
      have hv' := (hlat v).1 hv
      simp only [Matrix.mulVec, dotProduct]
      refine sum_mem fun k _ => ohat_mul T.toAdT ?_ (hv' k)
      rw [Matrix.map_apply, T.Φ_int]
      exact fun w hw => h w hw i k
  · intro N hN
    constructor
    · intro h w hw i k
      obtain ⟨u, hu, e⟩ := h _ (hsingle k)
      have e2 := congrFun (congrArg ν e) i
      rw [hactM, ν.apply_symm_apply, hcol, map_add, map_nsmul, ν.apply_symm_apply] at e2
      have hui := (hlat u).1 hu i
      obtain ⟨x, hx⟩ := T.Φ_surj (ν u i)
      have hxi := (T.Φ_int x).1 (hx ▸ hui) w hw
      have e3 : T.Φ (Y.val i k - (1 : Matrix (Fin n) (Fin n) (Af E)) i k - (N : Af E) * x) = 0 := by
        rw [map_sub, map_sub, map_mul, hΦ1, hx, map_natCast, e2, Pi.add_apply, Pi.smul_apply, nsmul_eq_mul,
          Matrix.one_apply, Pi.single_apply]
        simp [eq_comm]
      have e4 := (T.Φ_ker _).1 e3 w hw
      rw [map_sub, map_sub, map_mul, hw1, map_natCast, sub_eq_zero, sub_eq_iff_eq_add'] at e4
      have e5 : ((GeneralLinearGroup.map (pLoc E w) Y).val - 1) i k = (N : w.adicCompletion E) * pLoc E w x := by
        rw [Matrix.sub_apply]
        show pLoc E w (Y.val i k) - _ = _
        rw [e4]
        ring
      rw [e5, map_mul]
      exact mul_le_of_le_one_right' hxi
    · intro h v hv
      have hv' := (hlat v).1 hv
      have hN0 : (N : E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
      obtain ⟨Ninv, hNinvdef⟩ : ∃ Ninv : Af E, Ninv = algebraMap E (Af E) ((N : E)⁻¹) := ⟨_, rfl⟩
      have hNinv : (N : Af E) * Ninv = 1 := by
        rw [hNinvdef, ← map_natCast (algebraMap E (Af E)) N, ← map_mul, mul_inv_cancel₀ hN0, map_one]
      obtain ⟨C, hCdef⟩ : ∃ C : Matrix (Fin n) (Fin n) (AfP p ⊗[ℚ] E),
          ∀ i k, C i k = T.Φ (Ninv * (Y.val - 1) i k) := ⟨Matrix.of fun i k => T.Φ (Ninv * (Y.val - 1) i k), fun _ _ => rfl⟩
      have hC : Y.val.map T.Φ = 1 + ((N : AfP p ⊗[ℚ] E)) • C := by
        ext i k
        rw [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, ← hΦ1, hCdef,
          ← map_natCast T.Φ N, ← map_mul, ← map_add]
        congr 1
        rw [← mul_assoc, hNinv, one_mul, Matrix.sub_apply]
        ring
      refine ⟨ν.symm (C *ᵥ ν v), ?_, ?_⟩
      · rw [hlat]
        intro i
        rw [ν.apply_symm_apply]
        simp only [Matrix.mulVec, dotProduct]
        refine sum_mem fun k _ => ohat_mul T.toAdT ?_ (hv' k)
        rw [hCdef, T.Φ_int]
        intro w hw
        have h1 := h w hw i k
        have hp' : (N : w.adicCompletion E) * pLoc E w Ninv = 1 := by
          rw [← map_natCast (pLoc E w) N, ← map_mul, hNinv, map_one]
        have h2 : (N : w.adicCompletion E) ≠ 0 := left_ne_zero_of_mul_eq_one hp'
        have h3 : pLoc E w Ninv = (N : w.adicCompletion E)⁻¹ := eq_inv_of_mul_eq_one_right hp'
        have e : pLoc E w ((Y.val - 1) i k) = ((GeneralLinearGroup.map (pLoc E w) Y).val - 1) i k := by
          rw [Matrix.sub_apply, map_sub, hw1, Matrix.sub_apply]
          rfl
        rw [map_mul, h3, e, map_mul, map_inv₀]
        exact (inv_mul_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 h2))).2 h1
      · apply ν.injective
        rw [hactM, hC, map_add, map_nsmul, ν.apply_symm_apply, Matrix.add_mulVec, Matrix.one_mulVec,
          Matrix.smul_mulVec, Nat.cast_smul_eq_nsmul]
