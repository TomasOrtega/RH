import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoTwistedClassNormCompatibleCyclotomic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KmapComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SCls
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.CdFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.CoeffSlD
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpecialLinearGroupIntMapZmodSurjective

open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

namespace UpperTheory.V.Z.Kato.Nb

/- English proof (translation)
Rewrite using `[ZMod.natCast_val, ZMod.cast_intCast h]`.
-/
private theorem valCast {M N : ℕ} [NeZero M] (h : N ∣ M) (k : ℤ) : (((k : ZMod M)).val : ZMod N) = (k : ZMod N) := by
  rw [ZMod.natCast_val, ZMod.cast_intCast h]

/- English proof (translation)
Establish `h1 : (M : ℤ) ∣ k - (((k : ZMod M)).val : ℤ)`. Rewrite using `[← ZMod.intCast_zmod_eq_zero_iff_dvd]`. Simplify using the standard rewrite rules. Establish `h2 : ((l ^ n : ℕ) : ℤ) ∣ k - (((k : ZMod M)).val : ℤ)` using `(Int.natCast_dvd_natCast.2 h).trans h1`. Establish `h3` using `map_dvd (Int.castRingHom ℤ_[l]) h2`.

Simplify `h3` using `only [eq_intCast, Int.cast_natCast, Int.cast_sub, Nat.cast_pow, Int.cast_pow]`.
-/
private theorem valDvd {M l n : ℕ} [Fact l.Prime] [NeZero M] (h : l ^ n ∣ M) (k : ℤ) :
    (l : ℤ_[l]) ^ n ∣ (k : ℤ_[l]) - (((k : ZMod M)).val : ℤ_[l]) := by
  have h1 : (M : ℤ) ∣ k - (((k : ZMod M)).val : ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; simp
  have h2 : ((l ^ n : ℕ) : ℤ) ∣ k - (((k : ZMod M)).val : ℤ) := (Int.natCast_dvd_natCast.2 h).trans h1
  have h3 := map_dvd (Int.castRingHom ℤ_[l]) h2
  simpa only [eq_intCast, Int.cast_natCast, Int.cast_sub, Nat.cast_pow, Int.cast_pow] using h3

/- English proof (translation)
Establish `hg0 : ((g 1 0 : ℤ) : ZMod N) = 0` using `(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hg`. Establish `dg : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1`. Use `g.det_coe` as an intermediate fact. Rewrite `this` using `[Matrix.det_fin_two]`. Then use the resulting hypothesis. Establish `dh : h 0 0 * h 1 1 - h 0 1 * h 1 0 = 1`.

Use `h.det_coe` as an intermediate fact. Rewrite `this` using `[Matrix.det_fin_two]`. Then use the resulting hypothesis. Establish `dg'` using `congrArg (fun z : ℤ => (z : ZMod N)) dg`. Establish `dh'` using `congrArg (fun z : ℤ => (z : ZMod N)) dh`. Establish `e00 : (g⁻¹ * h) 0 0 = g 1 1 * h 0 0 - g 0 1 * h 1 0`.

Simplify using `[Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]`. Expand and normalize the polynomial expressions, which then agree. Establish `e10 : (g⁻¹ * h) 1 0 = - g 1 0 * h 0 0 + g 0 0 * h 1 0`. Simplify using `[Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]`. Establish `e11 : (g⁻¹ * h) 1 1 = - g 1 0 * h 0 1 + g 0 0 * h 1 1`.

Simplify using `[Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]`. Simplify using `only [Cnd, Gam, en, Subgroup.mem_inf, CongruenceSubgroup.Gamma1_mem, CongruenceSubgroup.Gamma0_mem, e00, e10, e11, Matrix.map_apply, eq_intCast, valCast hN, valCast hl]`. Move the coercions through the operations in `at dg' dh' ⊢`. Rewrite `dg'`, the goal using `[hg0]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨h1, h2, h3⟩`. Use `⟨⟨?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[h1, h2]`. Take the linear combination `dg'`. Rewrite `dh'` using `[h1, h2]`.

Take the linear combination `dh'`. Rewrite using `[h1]`. Expand and normalize the polynomial expressions, which then agree. Take the linear combination `-h3`. Introduce and unpack `⟨⟨h1, -, h2⟩, h3⟩`.

Establish `h4 : ((h 1 0 : ℤ) : ZMod N) = 0` using `by linear_combination (g 1 1 : ZMod N) * h2 - (h 1 0 : ZMod N) * dg'`. Use `⟨h4, ?_, ?_⟩` and prove the remaining obligations. Rewrite `h1` using `[h4]`. Take the linear combination `(g 0 0 : ZMod N) * h1 - (h 0 0 : ZMod N) * dg'`. Take the linear combination `-h3`.
-/
private theorem cnd_iff {l N M : ℕ} [NeZero M] (hN : N ∣ M) (hl : l ∣ M) (g h : SL(2, ℤ)) (hg : (N : ℤ) ∣ en g 1 0) :
    Cnd l N g ((h : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod M))) ↔ g⁻¹ * h ∈ Gam N l := by
  have hg0 : ((g 1 0 : ℤ) : ZMod N) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hg
  have dg : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have := g.det_coe; rwa [Matrix.det_fin_two] at this
  have dh : h 0 0 * h 1 1 - h 0 1 * h 1 0 = 1 := by
    have := h.det_coe; rwa [Matrix.det_fin_two] at this
  have dg' := congrArg (fun z : ℤ => (z : ZMod N)) dg
  have dh' := congrArg (fun z : ℤ => (z : ZMod N)) dh
  have e00 : (g⁻¹ * h) 0 0 = g 1 1 * h 0 0 - g 0 1 * h 1 0 := by
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; ring
  have e10 : (g⁻¹ * h) 1 0 = - g 1 0 * h 0 0 + g 0 0 * h 1 0 := by
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  have e11 : (g⁻¹ * h) 1 1 = - g 1 0 * h 0 1 + g 0 0 * h 1 1 := by
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  simp only [Cnd, Gam, en, Subgroup.mem_inf, CongruenceSubgroup.Gamma1_mem, CongruenceSubgroup.Gamma0_mem, e00, e10, e11,
    Matrix.map_apply, eq_intCast, valCast hN, valCast hl]
  push_cast at dg' dh' ⊢
  rw [hg0] at dg' ⊢
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · rw [h1, h2]; linear_combination dg'
    · rw [h1, h2] at dh'; linear_combination dh'
    · rw [h1]; ring
    · linear_combination -h3
  · rintro ⟨⟨h1, -, h2⟩, h3⟩
    have h4 : ((h 1 0 : ℤ) : ZMod N) = 0 := by linear_combination (g 1 1 : ZMod N) * h2 - (h 1 0 : ZMod N) * dg'
    refine ⟨h4, ?_, ?_⟩
    · rw [h4] at h1; linear_combination (g 0 0 : ZMod N) * h1 - (h 0 0 : ZMod N) * dg'
    · linear_combination -h3

/- English proof (translation)
Take `⟨k, hk⟩` from `hh`. Establish `dh : h 0 0 * h 1 1 - h 0 1 * h 1 0 = 1`. Use `h.det_coe` as an intermediate fact. Rewrite `this` using `[Matrix.det_fin_two]`. Then use the resulting hypothesis. Set `h' : SL(2, ℤ)` to `⟨!![h 0 0, N * h 0 1; k, h 1 1], by`.

Rewrite using `[Matrix.det_fin_two_of]`. Rewrite `dh` using `[hk]`. Take the linear combination `dh⟩`. Establish `hD : !![(N : ℤ), 0; 0, 1] * (h : Matrix (Fin 2) (Fin 2) ℤ) = (h' : Matrix (Fin 2) (Fin 2) ℤ) * !![(N : ℤ), 0; 0, 1]`. Use extensionality with `i j`.

Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [h', Matrix.mul_apply, Fin.sum_univ_two, hk, mul_comm]`. Establish `hc` using `(sCdFacts N M₀ M hM).2.2.2 _ _ hD`. Take `⟨-, s2, s3, -⟩` from `sSlD Ω ε X N (Nat.pos_of_ne_zero (NeZero.ne N))`. Take `⟨c1, -, -, c4, c5, -⟩` from `sCls Ω ε X l n`. Take `⟨-, -, -, -, a5, -⟩` from `sApi Ω ε X l n`.

Establish `hx : x ᵥ* cD N M₀ m = rt x h'` using `by rw [hm, hc]; rfl`. Establish `hy : y ᵥ* cD N M₀ m = rt y h'` using `by rw [hm, hc]; rfl`. Rewrite using `[hx, hy]`. Establish `r1` using `c5 (X.sl (toGQ (h : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv _ _ (c1 (slU X (toGQ !![(N : ℤ), 0; 0, 1]) (a x y)))`. Establish `r2` using `c1 (slU X (toGQ !![(N : ℤ), 0; 0, 1]) (a (rt x h') (rt y h')))`.

Establish `r3` using `c4 _ _ _ _ r1 r2 (by`. Take `⟨t, ht⟩` from `(ha x y hxy).2 h'`. Use `⟨slU X (toGQ !![(N : ℤ), 0; 0, 1]) t, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_pow, ← map_mul, ← ht]`. Apply `Units.ext` to reduce the goal to its premises.

Use `s2 _ _ (by rw [h.det_coe]; exact one_pos) hD (a x y : X.K)` as an intermediate fact. Rewrite `this` using `[s3 h']`. Conclude with `this)`. Introduce `u`. Establish `hk : (l : ℤ_[l]) ^ n ∣ ((mZl l (h : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 0) ^ w - (((1 : ZMod M).val : ℤ_[l])) * (((m 0 0).val : ℤ_[l]) * u 0 + ((m 0 1).val : ℤ_[l]) * u 1) ^ w`.

Establish `b1` using `valDvd hl 1`. Establish `b2` using `valDvd hl (h 0 0)`. Establish `b3` using `valDvd hl (h 0 1)`. Rewrite `b1`, `b2`, `b3`, the goal using `[← Ideal.mem_span_singleton, ← Ideal.Quotient.eq]`. Rewrite `b1` using `[Int.cast_one, Int.cast_one]`.

Simplify using `only [hm, mZl, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply, eq_intCast, map_mul, map_pow, map_add, ← b1, ← b2, ← b3, map_one, one_mul]`. Establish `r4` using `a5 _ _ (clsK X l n (slD X N (a (rt x h') (rt y h') : X.K))) hk`. Establish `r5` using `congrArg (fun z => ((mZl l (h : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 0) ^ w • z) r3`. Simplify using `only [smul_zero, ← map_smul] at r5`. Establish `r6` using `congrArg₂ (· + ·) r5 r4`.

Simplify using `only [← map_add, add_zero, smul_sub] at r6`. Use `show AdicCompletion.eval _ _ _ (X.kmap l _ (_ • _) - _) = 0`. Rewrite using `[← r6]`. Rewrite using `[map_smul]`. Conclude with `congrArg (AdicCompletion.eval (idl l) (X.Kl l) n) (sub_add_sub_cancel (G := X.Khat l) _ _ _).symm`.
-/
private theorem term (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime]
    (n N M₀ M w : ℕ) [NeZero N] [NeZero M₀] [NeZero M] (hM : M = N * M₀) (hl : l ^ n ∣ M) (x y : Row M₀) (hxy : Ok x y)
    (a : Fam X M₀) (ha : Eqv X (l ^ n) M₀ a) (h : SL(2, ℤ)) (hh : (N : ℤ) ∣ h 1 0) (m : Matrix (Fin 2) (Fin 2) (ZMod M))
    (hm : m = (h : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod M))) :
    CgF X l n (X.act l (h : Matrix (Fin 2) (Fin 2) ℤ) fun u => (u 0) ^ w • clsK X l n (slD X N (a x y : X.K)))
      (fun u => ((((1 : ZMod M).val : ℤ_[l])) * (((m 0 0).val : ℤ_[l]) * u 0 + ((m 0 1).val : ℤ_[l]) * u 1) ^ w) •
        clsK X l n (slD X N (a (x ᵥ* cD N M₀ m) (y ᵥ* cD N M₀ m) : X.K))) := by
  obtain ⟨k, hk⟩ := hh
  have dh : h 0 0 * h 1 1 - h 0 1 * h 1 0 = 1 := by
    have := h.det_coe; rwa [Matrix.det_fin_two] at this
  let h' : SL(2, ℤ) := ⟨!![h 0 0, N * h 0 1; k, h 1 1], by
    rw [Matrix.det_fin_two_of]; rw [hk] at dh; linear_combination dh⟩
  have hD : !![(N : ℤ), 0; 0, 1] * (h : Matrix (Fin 2) (Fin 2) ℤ) = (h' : Matrix (Fin 2) (Fin 2) ℤ) * !![(N : ℤ), 0; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h', Matrix.mul_apply, Fin.sum_univ_two, hk, mul_comm]
  have hc := (sCdFacts N M₀ M hM).2.2.2 _ _ hD
  obtain ⟨-, s2, s3, -⟩ := sSlD Ω ε X N (Nat.pos_of_ne_zero (NeZero.ne N))
  obtain ⟨c1, -, -, c4, c5, -⟩ := sCls Ω ε X l n
  obtain ⟨-, -, -, -, a5, -⟩ := sApi Ω ε X l n
  have hx : x ᵥ* cD N M₀ m = rt x h' := by rw [hm, hc]; rfl
  have hy : y ᵥ* cD N M₀ m = rt y h' := by rw [hm, hc]; rfl
  rw [hx, hy]
  have r1 := c5 (X.sl (toGQ (h : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv _ _ (c1 (slU X (toGQ !![(N : ℤ), 0; 0, 1]) (a x y)))
  have r2 := c1 (slU X (toGQ !![(N : ℤ), 0; 0, 1]) (a (rt x h') (rt y h')))
  have r3 := c4 _ _ _ _ r1 r2 (by
    obtain ⟨t, ht⟩ := (ha x y hxy).2 h'
    refine ⟨slU X (toGQ !![(N : ℤ), 0; 0, 1]) t, ?_⟩
    rw [← map_pow, ← map_mul, ← ht]
    apply Units.ext
    have := s2 _ _ (by rw [h.det_coe]; exact one_pos) hD (a x y : X.K)
    rw [s3 h'] at this
    exact this)
  intro u
  have hk : (l : ℤ_[l]) ^ n ∣ ((mZl l (h : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 0) ^ w -
      (((1 : ZMod M).val : ℤ_[l])) * (((m 0 0).val : ℤ_[l]) * u 0 + ((m 0 1).val : ℤ_[l]) * u 1) ^ w := by
    have b1 := valDvd hl 1
    have b2 := valDvd hl (h 0 0)
    have b3 := valDvd hl (h 0 1)
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq] at b1 b2 b3 ⊢
    rw [Int.cast_one, Int.cast_one] at b1
    simp only [hm, mZl, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply, eq_intCast, map_mul, map_pow, map_add,
      ← b1, ← b2, ← b3, map_one, one_mul]
  have r4 := a5 _ _ (clsK X l n (slD X N (a (rt x h') (rt y h') : X.K))) hk
  have r5 := congrArg (fun z => ((mZl l (h : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 0) ^ w • z) r3
  simp only [smul_zero, ← map_smul] at r5
  have r6 := congrArg₂ (· + ·) r5 r4
  simp only [← map_add, add_zero, smul_sub] at r6
  show AdicCompletion.eval _ _ _ (X.kmap l _ (_ • _) - _) = 0
  rw [← r6]
  rw [map_smul]
  exact congrArg (AdicCompletion.eval (idl l) (X.Kl l) n) (sub_add_sub_cancel (G := X.Khat l) _ _ _).symm

end UpperTheory.V.Z.Kato.Nb

/- English proof (translation)
Introduce `Ω _ _ _ ε X l _ n N M₀ M w _ _ _ g L x y hxy a ha`. Establish `hN : N ∣ M` using `L.eq ▸ dvd_mul_right N M₀`. Establish `hln : l ^ n ∣ M` using `L.eq ▸ L.dl.mul_left N`. Establish `hl : l ∣ M` using `(dvd_pow_self l (by have := L.pos; omega)).trans hln`. Set `r : SL(2, ℤ) →* SL(2, ZMod M)` to `Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M))`.

Establish `hr : ∀ γ, r (liftSL M γ) = γ` using `fun γ => Classical.epsilon_spec (GlobalTheory.specialLinearGroup_map_intCast_zmod_surjective M γ)`. Set `φ : SL(2, ZMod M) → GL (Fin 2) (ZMod M)` to `fun γ => Matrix.SpecialLinearGroup.toGL (r g * γ)`. Establish `hφ : ∀ δ, (φ (r δ) : Matrix (Fin 2) (Fin 2) (ZMod M)) = ((g * δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod M))`. Introduce `δ`. Simplify using `only [φ, ← map_mul r]`.

Both sides reduce to the same expression. Establish `hdet : ∀ γ, Matrix.GeneralLinearGroup.det (φ γ) = 1` using `fun γ => Units.ext (r g * γ).det_coe`. Establish `hC : ∀ γ ∈ img (Gam N l) M, Cnd l N g (φ γ : Matrix (Fin 2) (Fin 2) (ZMod M))`. Introduce `γ hγ`. Take `⟨δ, hδ, rfl⟩` from `(Finset.mem_filter.1 hγ).2`.

Express the relevant statement in the definitionally equal form `Cnd l N g (φ (r δ) : Matrix (Fin 2) (Fin 2) (ZMod M))`. Rewrite using `[hφ, cnd_iff hN hl g _ L.g0]`. Simplify using `using hδ`. Set `S : GL (Fin 2) (ZMod M) → X.Fn l` to `fun m u => (((((Matrix.GeneralLinearGroup.det m)⁻¹ : (ZMod M)ˣ) : ZMod M).val : ℤ_[l]) * ((((m : Matrix (Fin 2) (Fin 2) (ZMod M)) 0 0).val : ℤ_[l]) * u 0 + (((m : Matrix (Fin 2) (Fin 2) (ZMod M)) 0 1).val : ℤ_[l]) * u 1) ^ w) • clsK X l n (slD X N (a (x ᵥ* cD N M₀ (m : Matrix (Fi …`. Establish `hXi : Xi X l n N M₀ M w g x y (fun z => z = 1) a = ∑ γ ∈ img (Gam N l) M, S (φ γ)`.

Use function extensionality and compare the values at `u`. Rewrite using `[Finset.sum_apply]`. Unfold `Xi`. Use `symm`. Use `Finset.sum_bij (fun γ _ => φ γ) ?_ ?_ ?_ ?_` and prove the remaining obligations.

Introduce `γ hγ`. Simplify using `only [Finset.mem_filter]`. Conclude with `⟨Finset.mem_univ _, hC γ hγ, hdet γ⟩`. Introduce `γ _ γ' _ e`. Conclude with `mul_left_cancel (Matrix.SpecialLinearGroup.toGL_injective e)`.

Introduce `m hm`. Simplify using `only [Finset.mem_filter] at hm`. Take `⟨-, h1, h2⟩` from `hm`. Set `s : SL(2, ZMod M)` to `⟨m, congrArg Units.val h2⟩`. Establish `e : φ (r (g⁻¹ * liftSL M s)) = m`.

Apply `Units.ext` to reduce the goal to its premises. Simplify using `only [φ, map_mul r, map_inv r, hr, mul_inv_cancel_left]`. Both sides reduce to the same expression. Use `⟨r (g⁻¹ * liftSL M s), Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨_, ?_, rfl⟩⟩, e⟩` and prove the remaining obligations. Rewrite `h1` using `[← e, hφ, mul_inv_cancel_left, cnd_iff hN hl g _ L.g0]`.

Conclude with `h1`. Introduce `γ _`. Both sides reduce to the same expression. Rewrite using `[hXi]`. Use `(sApi Ω ε X l n).2.2.2.1 _ _ _ _ fun γ hγ => ?_` and prove the remaining obligations.

Establish `h1` using `hφ (liftSL M γ)`. Rewrite `h1` using `[hr]`. Establish `h2` using `(hC γ hγ).1`. Rewrite `h2` using `[h1, Matrix.map_apply, eq_intCast, valCast hN, ZMod.intCast_zmod_eq_zero_iff_dvd]`. Use `term Ω ε X l n N M₀ M w L.eq hln x y hxy a ha _ h2 _ h1` as an intermediate fact.

Simplify `this` using `only [S, hdet, inv_one, Units.val_one]`.
-/
theorem UpperTheory.V.Z.Kato.Nb.sXiOne :
    UpperTheory.V.Z.Kato.Nb.SXiOne := by
  intro Ω _ _ _ ε X l _ n N M₀ M w _ _ _ g L x y hxy a ha
  have hN : N ∣ M := L.eq ▸ dvd_mul_right N M₀
  have hln : l ^ n ∣ M := L.eq ▸ L.dl.mul_left N
  have hl : l ∣ M := (dvd_pow_self l (by have := L.pos; omega)).trans hln
  let r : SL(2, ℤ) →* SL(2, ZMod M) := Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M))
  have hr : ∀ γ, r (liftSL M γ) = γ := fun γ => Classical.epsilon_spec (GlobalTheory.specialLinearGroup_map_intCast_zmod_surjective M γ)
  let φ : SL(2, ZMod M) → GL (Fin 2) (ZMod M) := fun γ => Matrix.SpecialLinearGroup.toGL (r g * γ)
  have hφ : ∀ δ, (φ (r δ) : Matrix (Fin 2) (Fin 2) (ZMod M)) =
      ((g * δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod M)) := by
    intro δ
    simp only [φ, ← map_mul r]; rfl
  have hdet : ∀ γ, Matrix.GeneralLinearGroup.det (φ γ) = 1 := fun γ => Units.ext (r g * γ).det_coe
  have hC : ∀ γ ∈ img (Gam N l) M, Cnd l N g (φ γ : Matrix (Fin 2) (Fin 2) (ZMod M)) := by
    intro γ hγ
    obtain ⟨δ, hδ, rfl⟩ := (Finset.mem_filter.1 hγ).2
    change Cnd l N g (φ (r δ) : Matrix (Fin 2) (Fin 2) (ZMod M))
    rw [hφ, cnd_iff hN hl g _ L.g0]
    simpa using hδ
  let S : GL (Fin 2) (ZMod M) → X.Fn l := fun m u =>
    (((((Matrix.GeneralLinearGroup.det m)⁻¹ : (ZMod M)ˣ) : ZMod M).val : ℤ_[l]) *
        ((((m : Matrix (Fin 2) (Fin 2) (ZMod M)) 0 0).val : ℤ_[l]) * u 0 +
          (((m : Matrix (Fin 2) (Fin 2) (ZMod M)) 0 1).val : ℤ_[l]) * u 1) ^ w) •
      clsK X l n (slD X N (a (x ᵥ* cD N M₀ (m : Matrix (Fin 2) (Fin 2) (ZMod M)))
        (y ᵥ* cD N M₀ (m : Matrix (Fin 2) (Fin 2) (ZMod M))) : X.K))
  have hXi : Xi X l n N M₀ M w g x y (fun z => z = 1) a = ∑ γ ∈ img (Gam N l) M, S (φ γ) := by
    funext u
    rw [Finset.sum_apply]
    unfold Xi
    symm
    refine Finset.sum_bij (fun γ _ => φ γ) ?_ ?_ ?_ ?_
    · intro γ hγ
      simp only [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hC γ hγ, hdet γ⟩
    · intro γ _ γ' _ e
      exact mul_left_cancel (Matrix.SpecialLinearGroup.toGL_injective e)
    · intro m hm
      simp only [Finset.mem_filter] at hm
      obtain ⟨-, h1, h2⟩ := hm
      let s : SL(2, ZMod M) := ⟨m, congrArg Units.val h2⟩
      have e : φ (r (g⁻¹ * liftSL M s)) = m := by
        apply Units.ext
        simp only [φ, map_mul r, map_inv r, hr, mul_inv_cancel_left]; rfl
      refine ⟨r (g⁻¹ * liftSL M s), Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨_, ?_, rfl⟩⟩, e⟩
      rw [← e, hφ, mul_inv_cancel_left, cnd_iff hN hl g _ L.g0] at h1
      exact h1
    · intro γ _; rfl
  rw [hXi]
  refine (sApi Ω ε X l n).2.2.2.1 _ _ _ _ fun γ hγ => ?_
  have h1 := hφ (liftSL M γ)
  rw [hr] at h1
  have h2 := (hC γ hγ).1
  rw [h1, Matrix.map_apply, eq_intCast, valCast hN, ZMod.intCast_zmod_eq_zero_iff_dvd] at h2
  have := term Ω ε X l n N M₀ M w L.eq hln x y hxy a ha _ h2 _ h1
  simpa only [S, hdet, inv_one, Units.val_one] using this
