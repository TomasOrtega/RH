import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.LUnH
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.GamMono
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.EvalSmulCong
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.SlFixPoly
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.NegOneNot
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionTowerIntegrality
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlMulToRingEquiv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerUnitClassModPrimePowProperties
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.Kd.K4 Polynomial
open scoped Matrix MatrixGroups

namespace UpperTheory.Kd.K4.LiftH

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

/- English proof (translation)
Establish `h : 0 < (γ : Matrix (Fin 2) (Fin 2) ℤ).det` using `by simp`. Unfold `toGQ`. Rewrite using `[dif_pos h]`. Use extensionality with `i j`. Simplify using `[ofSL]`.
-/
private theorem toGQ_sl (γ : SL(2, ℤ)) : toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ) = ofSL γ := by
  have h : 0 < (γ : Matrix (Fin 2) (Fin 2) ℤ).det := by simp
  unfold toGQ
  rw [dif_pos h]
  ext i j
  simp [ofSL]

/- English proof (translation)
Rewrite using `[map_smul]`. Take `⟨z, hz⟩` from `Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (idl l) (X.Kl l) n y)`. Rewrite using `[← hz, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Conclude with `GlobalTheory.KZ.ClsMod.smul_mem_of_toZModPow hs z`.
-/
private theorem ev_smul (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (s : ℤ_[l]) (hs : PadicInt.toZModPow n s = 0)
    (y : X.Khat l) : AdicCompletion.eval (idl l) (X.Kl l) n (s • y) = 0 := by
  rw [map_smul]
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (idl l) (X.Kl l) n y)
  rw [← hz, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact GlobalTheory.KZ.ClsMod.smul_mem_of_toZModPow hs z

/- English proof (translation)
Establish `e : sec X l w lam (c • (x - y)) = c • (sec X l w lam x - sec X l w lam y)`. Use function extensionality and compare the values at `v`. Simplify using `only [sec, Pi.smul_apply, Pi.sub_apply]`. Rewrite using `[smul_comm, smul_sub]`. Establish `: trH X l w γ lam (c • (x - y)) = c • (trH X l w γ lam x - trH X l w γ lam y)`.

Unfold `trH`. Rewrite using `[e, ← Finset.sum_sub_distrib, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, map_sub]`. Rewrite using `[this]`.

Both sides reduce to the same expression.
-/
private theorem tr_sub (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (w : ℕ) {ι : Type} [Fintype ι] (γ : ι → SL(2, ℤ))
    (lam : Fin 2 → ℤ) (c : ℤ_[l]) (x y : X.Khat l) (u : Fin 2 → ℤ_[l]) :
    trH X l w γ lam (c • (x - y)) u = c • (trH X l w γ lam x u - trH X l w γ lam y u) := by
  have e : sec X l w lam (c • (x - y)) = c • (sec X l w lam x - sec X l w lam y) := by
    funext v
    simp only [sec, Pi.smul_apply, Pi.sub_apply]
    rw [smul_comm, smul_sub]
  have : trH X l w γ lam (c • (x - y)) = c • (trH X l w γ lam x - trH X l w γ lam y) := by
    unfold trH
    rw [e, ← Finset.sum_sub_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, map_sub]
  rw [this]; rfl

/- English proof (translation)
Unfold `trH`. Rewrite using `[Finset.sum_apply, Finset.sum_apply, ← Finset.sum_add_distrib, map_sum]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Simplify using `only [Tower.act, LinearMap.coe_mk, AddHom.coe_mk, sec, map_smul]`. Rewrite using `[toGQ_sl, toGQ_sl, map_mul ofSL, Tower.sl_mul_toRingEquiv, ← Tower.kmap_kmap, ← add_smul]`.

Apply `ev_smul` to reduce the goal to its premises. Rewrite using `[Matrix.SpecialLinearGroup.coe_mul, mZl_mul, ← Matrix.mulVec_mulVec]`. Generalize the expression as in `mZl l (γ i : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u = v`. Rewrite `hz` using `[CongruenceSubgroup.Gamma_mem]`. Take `⟨h00, h01, h10, h11⟩` from `hz`.

Simplify using `only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg, neg_eq_zero] at h00 h01 h10 h11`. Establish `g00` using `neg_eq_iff_eq_neg.1 h00`. Establish `g11` using `neg_eq_iff_eq_neg.1 h11`. Establish `e : PadicInt.toZModPow n ((lam 0 : ℤ_[l]) * (mZl l (z : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ v) 0 + (lam 1 : ℤ_[l]) * (mZl l (z : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ v) 1) = - PadicInt.toZModPow n ((lam 0 : ℤ_[l]) * v 0 + (lam 1 : ℤ_[l]) * v 1)`. Simplify using `only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, mZl, Matrix.map_apply, map_add, map_mul, map_intCast, eq_intCast]`.

Rewrite using `[g00, g11, h01, h10]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[map_add, map_pow, map_pow, e, hw.neg_pow, neg_add_cancel]`.
-/
private theorem tr_z_eq_transfer (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (w n : ℕ) (hw : Odd w) {ι : Type} [Fintype ι] (γ : ι → SL(2, ℤ))
    (lam : Fin 2 → ℤ) (x : X.Khat l) (z : SL(2, ℤ)) (hz : -z ∈ CongruenceSubgroup.Gamma (l ^ n)) (u : Fin 2 → ℤ_[l]) :
    AdicCompletion.eval (idl l) (X.Kl l) n (trH X l w (fun i => z * γ i) lam x u +
      trH X l w γ lam (X.kmap l (X.sl (ofSL z)).toRingEquiv x) u) = 0 := by
  unfold trH
  rw [Finset.sum_apply, Finset.sum_apply, ← Finset.sum_add_distrib, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  simp only [Tower.act, LinearMap.coe_mk, AddHom.coe_mk, sec, map_smul]
  rw [toGQ_sl, toGQ_sl, map_mul ofSL, Tower.sl_mul_toRingEquiv, ← Tower.kmap_kmap, ← add_smul]
  apply ev_smul
  rw [Matrix.SpecialLinearGroup.coe_mul, mZl_mul, ← Matrix.mulVec_mulVec]
  generalize mZl l (γ i : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u = v
  rw [CongruenceSubgroup.Gamma_mem] at hz
  obtain ⟨h00, h01, h10, h11⟩ := hz
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg, neg_eq_zero] at h00 h01 h10 h11
  have g00 := neg_eq_iff_eq_neg.1 h00
  have g11 := neg_eq_iff_eq_neg.1 h11
  have e : PadicInt.toZModPow n ((lam 0 : ℤ_[l]) * (mZl l (z : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ v) 0 +
      (lam 1 : ℤ_[l]) * (mZl l (z : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ v) 1) =
      - PadicInt.toZModPow n ((lam 0 : ℤ_[l]) * v 0 + (lam 1 : ℤ_[l]) * v 1) := by
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, mZl, Matrix.map_apply, map_add, map_mul, map_intCast,
      eq_intCast]
    rw [g00, g11, h01, h10]; ring
  rw [map_add, map_pow, map_pow, e, hw.neg_pow, neg_add_cancel]

/- English proof (translation)
Use `⟨fun i => Γ.mul_mem hz (h.1 i), fun δ hδ => ?_⟩` and prove the remaining obligations. Establish `key : ∀ i, δ * (z * γ i)⁻¹ ∈ H ↔ z⁻¹ * δ * (γ i)⁻¹ ∈ H`. Introduce `i`. Establish `h1` using `hc (z⁻¹ * δ * (γ i)⁻¹)`. Establish `e : z⁻¹ * δ * (γ i)⁻¹ = ((z⁻¹ * δ * (γ i)⁻¹) * z * (z⁻¹ * δ * (γ i)⁻¹)⁻¹ * z⁻¹) * (δ * (z * γ i)⁻¹)` using `by group`.

Rewrite using `[e, H.mul_mem_cancel_left h1]`. Simplify using `only [key]`. Conclude with `h.2 _ (Γ.mul_mem (Γ.inv_mem hz) hδ)`.
-/
private theorem isTransversal_left_mul (H Γ : Subgroup SL(2, ℤ)) {ι : Type} (γ : ι → SL(2, ℤ)) (h : IsTr H Γ γ) (z : SL(2, ℤ)) (hz : z ∈ Γ)
    (hc : ∀ g : SL(2, ℤ), g * z * g⁻¹ * z⁻¹ ∈ H) : IsTr H Γ fun i => z * γ i := by
  refine ⟨fun i => Γ.mul_mem hz (h.1 i), fun δ hδ => ?_⟩
  have key : ∀ i, δ * (z * γ i)⁻¹ ∈ H ↔ z⁻¹ * δ * (γ i)⁻¹ ∈ H := by
    intro i
    have h1 := hc (z⁻¹ * δ * (γ i)⁻¹)
    have e : z⁻¹ * δ * (γ i)⁻¹ = ((z⁻¹ * δ * (γ i)⁻¹) * z * (z⁻¹ * δ * (γ i)⁻¹)⁻¹ * z⁻¹) * (δ * (z * γ i)⁻¹) := by
      group
    rw [e, H.mul_mem_cancel_left h1]
  simp only [key]
  exact h.2 _ (Γ.mul_mem (Γ.inv_mem hz) hδ)

/- English proof (translation)
Use `⟨fun c => ValuationSubring.mem_comap.2 ?_, ValuationSubring.mem_comap.2 ?_⟩` and prove the remaining obligations. Establish `: (X.sl (ofSL z)).toRingEquiv.toRingHom (algebraMap Ω X.K c) = algebraMap Ω X.K c` using `(X.sl (ofSL z)).commutes c`. Rewrite using `[this]`. Conclude with `hW.1 c`. Establish `: (X.sl (ofSL z)).toRingEquiv.toRingHom X.jK = X.jK` using `X.j_inv z`.

Rewrite using `[this]`. Conclude with `hW.2`.
-/
private theorem overY_comap (X : Tower Ω ε) (z : SL(2, ℤ)) (W : ValuationSubring X.K) (hW : X.OverY W) :
    X.OverY (W.comap (X.sl (ofSL z)).toRingEquiv.toRingHom) := by
  refine ⟨fun c => ValuationSubring.mem_comap.2 ?_, ValuationSubring.mem_comap.2 ?_⟩
  · have : (X.sl (ofSL z)).toRingEquiv.toRingHom (algebraMap Ω X.K c) = algebraMap Ω X.K c := (X.sl (ofSL z)).commutes c
    rw [this]; exact hW.1 c
  · have : (X.sl (ofSL z)).toRingEquiv.toRingHom X.jK = X.jK := X.j_inv z
    rw [this]; exact hW.2

end UpperTheory.Kd.K4.LiftH

open UpperTheory.Kd.K4.LiftH in
/- English proof (translation)
Introduce `Ω _ _ _ ε X l _ N w hl2 hN hlN hw`. Establish `hp : l.Prime` using `Fact.out`. Take `⟨c, hc⟩` from `liftL ε X l N w hl2`. Take `⟨E, hE, heb⟩` from `eb ε X`. Establish `h2E : ((2 * E : ℕ) : ℤ_[l]) ≠ 0` using `Nat.cast_ne_zero.2 (by omega)`.

Establish `hu` using `PadicInt.unitCoeff_spec h2E`. Use `set s := ((2 * E : ℕ) : ℤ_[l]).valuation`. Use `set un := PadicInt.unitCoeff h2E`. Use `⟨c + s, ?_⟩` and prove the remaining obligations. Introduce `n H M hM hMH hH ι _ γ hγ lam a x haU hinv hrep`.

Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Use `⟨0, Submodule.zero_mem _, fun u => ?_⟩` and prove the remaining obligations. Rewrite using `[← one_smul ℤ_[l] (_ - _)]`. Apply `ev_smul` to reduce the goal to its premises. Use `haveI : Subsingleton (ZMod (l ^ 0)) := by rw [pow_zero]; infer_instance`.

Conclude with `Subsingleton.elim _ _`. Establish `hm1 : (-1 : SL(2, ℤ)) ∉ H`. Introduce `h`. Establish `h1` using `(CongruenceSubgroup.Gamma_mem.1 (hH h).2).1`. Establish `h2 : ((2 : ℕ) : ZMod (l ^ n)) = 0`.

Simplify using `at h1`. Use `push_cast`. Take the linear combination `-h1`. Rewrite `h2` using `[ZMod.natCast_eq_zero_iff]`. Conclude with `hl2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 ((dvd_pow_self l hn.ne').trans h2))`.

Take `⟨z, hz1, hzN, hzc, -, f, hfH, h, hh, hfe⟩` from `h90 ε X H M l (l ^ n) a hM (pow_pos hp.pos n) hp hMH hm1 hinv n N hN hlN`. Establish `hzG : z ∈ Gam N l`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `CongruenceSubgroup.Gamma_mem.1 hzN` as an intermediate fact. Conclude with `(CongruenceSubgroup.Gamma1_mem N z).2 ⟨this.1, this.2.2.2, this.2.2.1⟩`.

Establish `h10` using `(CongruenceSubgroup.Gamma_mem.1 hz1).2.2.1`. Simplify using `only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg, neg_eq_zero] at h10`. Use `CongruenceSubgroup.Gamma0_mem.2 ?_` and prove the remaining obligations. Rewrite `h10`, the goal using `[ZMod.intCast_zmod_eq_zero_iff_dvd]`. Conclude with `(Int.natCast_dvd_natCast.2 (dvd_pow_self l hn.ne')).trans h10`.

Use `set φ := (X.sl (ofSL z)).toRingEquiv with hφ`. Use `set a' : X.Kˣ := Units.map φ.toMonoidHom a with ha'`. Establish `ha'v : (a' : X.K) = X.sl (ofSL z) (a : X.K)` using `rfl`. Establish `ha'U : a' ∈ X.Un (l ^ n)` using `GlobalTheory.KZ.KmapA.un_map X φ (overY_comap X z) _ a haU`. Establish `hf0 : f ≠ 0`.

Introduce and unpack `rfl`. Rewrite `hfe` using `[← ha'v, zero_mul]`. Conclude with `div_ne_zero a.ne_zero a'.ne_zero hfe`. Use `set fu : X.Kˣ := Units.mk0 f hf0 with hfu`. Establish `hae : a = (fu * a') * (Units.mk0 h hh) ^ (l ^ n)`.

Apply `Units.ext` to reduce the goal to its premises. Rewrite `hfe` using `[← ha'v, div_eq_iff a'.ne_zero]`. Simplify using `only [Units.val_mul, Units.val_pow_eq_pow_val, hfu, Units.val_mk0]`. Rewrite using `[hfe]`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨-, p2, p3, p4, -, p6, -⟩` from `GlobalTheory.KZ.H3.cls_props Ω ε X l n`. Establish `hrf : AdicCompletion.eval (idl l) (X.Kl l) n (x - X.kmap l φ x) = X.cls l n fu`. Rewrite using `[map_sub, p6 φ x a hrep, hrep, (p2 a _).2 ⟨_, hae⟩, p3, add_sub_cancel_right]`. Establish `hpow : ∀ k : ℕ, X.cls l n (fu ^ k) = (k : ℤ_[l]) • X.cls l n fu`. Introduce `k`.

Proceed by induction on `k with`. Consider the case `zero => simp [p4]`. Consider the case `succ k ih => rw [pow_succ, p3, ih, Nat.cast_succ, add_smul, one_smul]`. Establish `hrE : Rep X l n (fu ^ E) ((E : ℤ_[l]) • (x - X.kmap l φ x))`. Unfold `Rep`.

Rewrite using `[map_smul, hrf, hpow]`. Establish `hL : LUnH X H (l ^ n) ((fu ^ E : X.Kˣ) : X.K)`. Use `⟨Units.ne_zero _, ?_, fun W hW => ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_pow_eq_pow_val]`. Conclude with `pow_mem hfH E`.

Take `⟨g, hg⟩` from `haU W hW`. Take `⟨g', hg'⟩` from `ha'U W hW`. Establish `hne : (g : X.K) / g' / h ≠ 0` using `div_ne_zero (div_ne_zero g.ne_zero g'.ne_zero) hh`. Take `⟨y, hy, hy0, hyv⟩` from `heb W hW _ hne`. Use `⟨y, (mem_lev_iff X H y).2 fun δ _ => (mem_lev_iff X ⊤ y).1 hy δ trivial, hy0, ?_⟩` and prove the remaining obligations.

Establish `hfe' : f = (a : X.K) / a' / h ^ (l ^ n)`. Rewrite using `[ha'v, hfe, mul_div_assoc, div_self (pow_ne_zero _ hh), mul_one]`. Establish `e : ((fu ^ E : X.Kˣ) : X.K) / y ^ (l ^ n) = (((a : X.K) / (g : X.K) ^ (l ^ n)) / ((a' : X.K) / (g' : X.K) ^ (l ^ n))) ^ E * (((g : X.K) / g' / h) ^ E / y) ^ (l ^ n)`. Rewrite using `[Units.val_pow_eq_pow_val, hfu, Units.val_mk0, hfe', div_pow (_ ^ E) y, ← pow_mul, mul_comm E, pow_mul, ← mul_div_assoc, ← mul_pow]`. Use `congr 2`.

Use `g.ne_zero` as an intermediate fact. Use `g'.ne_zero` as an intermediate fact. Use `a'.ne_zero` as an intermediate fact. Simplify using `only [div_pow]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[e, map_mul, map_pow, map_pow, map_div₀, hg, hg', hyv]`. Simplify using the standard rewrite rules. Take `⟨b, hbB, hb⟩` from `hc n H M hn hM hMH hH ι γ hγ lam (fu ^ E) _ hL hrE`. Use `⟨((un⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) • b, Submodule.smul_mem _ _ hbB, fun u => ?_⟩` and prove the remaining obligations. Establish `t1` using `((trc ε X l N w n H hH ι γ hγ lam a x hrep).2.2.1 hinv ι _ (isTransversal_left_mul H _ γ hγ z hzG hzc) x hrep) u`.

Establish `t2` using `tr_z_eq_transfer X l w n hw γ lam x z hz1 u`. Establish `t3` using `hb u`. Rewrite `t3` using `[tr_sub]`. Establish `hv : ((un⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) * (2 * (E : ℤ_[l])) = (l : ℤ_[l]) ^ s`. Establish `e : (2 * (E : ℤ_[l])) = (un : ℤ_[l]) * (l : ℤ_[l]) ^ s`.

Rewrite using `[← hu]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, ← mul_assoc, Units.inv_mul, one_mul]`. Generalize the expression as in `((un⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) = v at hv ⊢`.

Generalize the expression as in `hA : trH X l w γ lam x u = A at t1 t3 ⊢`. Generalize the expression as in `trH X l w (fun i => z * γ i) lam x u = B at t1 t2`. Generalize the expression as in `trH X l w γ lam (X.kmap l φ x) u = C at t2 t3`. Establish `key : (v • b) u - ((l : ℤ_[l]) ^ (c + s)) • A = v • (b u - ((l : ℤ_[l]) ^ c) • ((E : ℤ_[l]) • (A - C))) - (v * (l : ℤ_[l]) ^ c * (E : ℤ_[l])) • (A - B) - (v * (l : ℤ_[l]) ^ c * (E : ℤ_[l])) • (B + C)`. Rewrite using `[pow_add, ← hv, Pi.smul_apply]`.

Use `module`. Rewrite using `[key, map_sub, map_sub, map_smul, map_smul, map_smul, t1, t2, t3]`. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.Kd.K4.liftH :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∀ (l : ℕ) [Fact l.Prime] (N w : ℕ), l ≠ 2 → 0 < N → Nat.Coprime l N → Odd w → ∃ c : ℕ, ∀ (n : ℕ) (H : Subgroup SL(2, ℤ)) (M : ℕ), 0 < M →
      CongruenceSubgroup.Gamma M ≤ H → H ≤ Gam N l ⊓ CongruenceSubgroup.Gamma (l ^ n) → ∀ (ι : Type) [Fintype ι] (γ : ι → SL(2, ℤ)), IsTr H (Gam N l) γ →
      ∀ (lam : Fin 2 → ℤ) (a : X.Kˣ) (x : X.Khat l), a ∈ X.Un (l ^ n) → InvH X H (l ^ n) a → Rep X l n a x →
        ∃ b, LiftB X l N w n c (trH X l w γ lam x) b := by
  intro Ω _ _ _ ε X l _ N w hl2 hN hlN hw
  have hp : l.Prime := Fact.out
  obtain ⟨c, hc⟩ := liftL ε X l N w hl2
  obtain ⟨E, hE, heb⟩ := eb ε X
  have h2E : ((2 * E : ℕ) : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hu := PadicInt.unitCoeff_spec h2E
  set s := ((2 * E : ℕ) : ℤ_[l]).valuation
  set un := PadicInt.unitCoeff h2E
  refine ⟨c + s, ?_⟩
  intro n H M hM hMH hH ι _ γ hγ lam a x haU hinv hrep
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨0, Submodule.zero_mem _, fun u => ?_⟩
    rw [← one_smul ℤ_[l] (_ - _)]
    apply ev_smul
    haveI : Subsingleton (ZMod (l ^ 0)) := by rw [pow_zero]; infer_instance
    exact Subsingleton.elim _ _
  have hm1 : (-1 : SL(2, ℤ)) ∉ H := by
    intro h
    have h1 := (CongruenceSubgroup.Gamma_mem.1 (hH h).2).1
    have h2 : ((2 : ℕ) : ZMod (l ^ n)) = 0 := by
      simp at h1
      push_cast
      linear_combination -h1
    rw [ZMod.natCast_eq_zero_iff] at h2
    exact hl2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 ((dvd_pow_self l hn.ne').trans h2))
  obtain ⟨z, hz1, hzN, hzc, -, f, hfH, h, hh, hfe⟩ :=
    h90 ε X H M l (l ^ n) a hM (pow_pos hp.pos n) hp hMH hm1 hinv n N hN hlN
  have hzG : z ∈ Gam N l := by
    refine ⟨?_, ?_⟩
    · have := CongruenceSubgroup.Gamma_mem.1 hzN
      exact (CongruenceSubgroup.Gamma1_mem N z).2 ⟨this.1, this.2.2.2, this.2.2.1⟩
    · have h10 := (CongruenceSubgroup.Gamma_mem.1 hz1).2.2.1
      simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg, neg_eq_zero] at h10
      refine CongruenceSubgroup.Gamma0_mem.2 ?_
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h10 ⊢
      exact (Int.natCast_dvd_natCast.2 (dvd_pow_self l hn.ne')).trans h10
  set φ := (X.sl (ofSL z)).toRingEquiv with hφ
  set a' : X.Kˣ := Units.map φ.toMonoidHom a with ha'
  have ha'v : (a' : X.K) = X.sl (ofSL z) (a : X.K) := rfl
  have ha'U : a' ∈ X.Un (l ^ n) := GlobalTheory.KZ.KmapA.un_map X φ (overY_comap X z) _ a haU
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [← ha'v, zero_mul] at hfe
    exact div_ne_zero a.ne_zero a'.ne_zero hfe
  set fu : X.Kˣ := Units.mk0 f hf0 with hfu
  have hae : a = (fu * a') * (Units.mk0 h hh) ^ (l ^ n) := by
    apply Units.ext
    rw [← ha'v, div_eq_iff a'.ne_zero] at hfe
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, hfu, Units.val_mk0]
    rw [hfe]; ring
  obtain ⟨-, p2, p3, p4, -, p6, -⟩ := GlobalTheory.KZ.H3.cls_props Ω ε X l n
  have hrf : AdicCompletion.eval (idl l) (X.Kl l) n (x - X.kmap l φ x) = X.cls l n fu := by
    rw [map_sub, p6 φ x a hrep, hrep, (p2 a _).2 ⟨_, hae⟩, p3, add_sub_cancel_right]
  have hpow : ∀ k : ℕ, X.cls l n (fu ^ k) = (k : ℤ_[l]) • X.cls l n fu := by
    intro k
    induction k with
    | zero => simp [p4]
    | succ k ih => rw [pow_succ, p3, ih, Nat.cast_succ, add_smul, one_smul]
  have hrE : Rep X l n (fu ^ E) ((E : ℤ_[l]) • (x - X.kmap l φ x)) := by
    unfold Rep
    rw [map_smul, hrf, hpow]
  have hL : LUnH X H (l ^ n) ((fu ^ E : X.Kˣ) : X.K) := by
    refine ⟨Units.ne_zero _, ?_, fun W hW => ?_⟩
    · rw [Units.val_pow_eq_pow_val]; exact pow_mem hfH E
    · obtain ⟨g, hg⟩ := haU W hW
      obtain ⟨g', hg'⟩ := ha'U W hW
      have hne : (g : X.K) / g' / h ≠ 0 := div_ne_zero (div_ne_zero g.ne_zero g'.ne_zero) hh
      obtain ⟨y, hy, hy0, hyv⟩ := heb W hW _ hne
      refine ⟨y, (mem_lev_iff X H y).2 fun δ _ => (mem_lev_iff X ⊤ y).1 hy δ trivial, hy0, ?_⟩
      have hfe' : f = (a : X.K) / a' / h ^ (l ^ n) := by
        rw [ha'v, hfe, mul_div_assoc, div_self (pow_ne_zero _ hh), mul_one]
      have e : ((fu ^ E : X.Kˣ) : X.K) / y ^ (l ^ n) =
          (((a : X.K) / (g : X.K) ^ (l ^ n)) / ((a' : X.K) / (g' : X.K) ^ (l ^ n))) ^ E *
            (((g : X.K) / g' / h) ^ E / y) ^ (l ^ n) := by
        rw [Units.val_pow_eq_pow_val, hfu, Units.val_mk0, hfe', div_pow (_ ^ E) y, ← pow_mul, mul_comm E, pow_mul,
          ← mul_div_assoc, ← mul_pow]
        congr 2
        have := g.ne_zero
        have := g'.ne_zero
        have := a'.ne_zero
        simp only [div_pow]
        field_simp
      rw [e, map_mul, map_pow, map_pow, map_div₀, hg, hg', hyv]; simp
  obtain ⟨b, hbB, hb⟩ := hc n H M hn hM hMH hH ι γ hγ lam (fu ^ E) _ hL hrE
  refine ⟨((un⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) • b, Submodule.smul_mem _ _ hbB, fun u => ?_⟩
  have t1 := ((trc ε X l N w n H hH ι γ hγ lam a x hrep).2.2.1 hinv ι _ (isTransversal_left_mul H _ γ hγ z hzG hzc) x hrep) u
  have t2 := tr_z_eq_transfer X l w n hw γ lam x z hz1 u
  have t3 := hb u
  rw [tr_sub] at t3
  have hv : ((un⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) * (2 * (E : ℤ_[l])) = (l : ℤ_[l]) ^ s := by
    have e : (2 * (E : ℤ_[l])) = (un : ℤ_[l]) * (l : ℤ_[l]) ^ s := by
      rw [← hu]; push_cast; ring
    rw [e, ← mul_assoc, Units.inv_mul, one_mul]
  generalize ((un⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) = v at hv ⊢
  generalize hA : trH X l w γ lam x u = A at t1 t3 ⊢
  generalize trH X l w (fun i => z * γ i) lam x u = B at t1 t2
  generalize trH X l w γ lam (X.kmap l φ x) u = C at t2 t3
  have key : (v • b) u - ((l : ℤ_[l]) ^ (c + s)) • A =
      v • (b u - ((l : ℤ_[l]) ^ c) • ((E : ℤ_[l]) • (A - C))) -
        (v * (l : ℤ_[l]) ^ c * (E : ℤ_[l])) • (A - B) - (v * (l : ℤ_[l]) ^ c * (E : ℤ_[l])) • (B + C) := by
    rw [pow_add, ← hv, Pi.smul_apply]
    module
  rw [key, map_sub, map_sub, map_smul, map_smul, map_smul, t1, t2, t3]
  simp
