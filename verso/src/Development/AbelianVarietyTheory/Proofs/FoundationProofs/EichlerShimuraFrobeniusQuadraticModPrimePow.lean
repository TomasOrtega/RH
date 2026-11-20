import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeOperatorCommGaloisActionModularTowerStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerShimuraKummerModularUnitStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerBettiModuleFreeFiniteStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlMulToRingEquiv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MobToGQScalar
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalMulApply
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerUnitClassModPrimePowProperties
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlTwoPosRatMobiusBasicLaws
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCommonLevelSpanMultiple
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspFunctionalValueModPrimePowDiamondIndepende
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BettiFunctionSubMemOfColumnsCongr
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CyclotomicCharacterFrobV
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumActUpperRep
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitEvalEqKummerClass

noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ.ESmod

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

/- English proof (translation)
Use `Submodule.smul_induction_on hx (fun r hr y _ => ?_) (fun y z hy hz => ?_)` and prove the remaining obligations. Rewrite using `[map_smul]`. Conclude with `Submodule.smul_mem_smul hr Submodule.mem_top`. Rewrite using `[map_add]`. Conclude with `Submodule.add_mem _ hy hz`.
-/
theorem map_mem_smul_top {R A B : Type} [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (I : Ideal R) (φ : A →ₗ[R] B) {x : A} (hx : x ∈ I • (⊤ : Submodule R A)) :
    φ x ∈ I • (⊤ : Submodule R B) := by
  refine Submodule.smul_induction_on hx (fun r hr y _ => ?_) (fun y z hy hz => ?_)
  · rw [map_smul]; exact Submodule.smul_mem_smul hr Submodule.mem_top
  · rw [map_add]; exact Submodule.add_mem _ hy hz

/- English proof (translation)
Take `⟨V, hV, hs⟩` from `h`. Use `⟨V, hV, fun x hx => ⟨(hs x hx).1, ?_, (hs x hx).2⟩⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hy`. Establish `hy0 : s.symm x ≠ 0` using `fun e => hy (e ▸ V.zero_mem)`. Establish `hi : (s.symm x)⁻¹ ∈ V` using `(V.mem_or_inv_mem _).resolve_left hy`.

Establish `h1 : 1 < V.valuation (s.symm x)`. Assume the negation of the conclusion as `hle`. Conclude with `hy ((V.valuation_le_one_iff _).1 (not_lt.1 hle))`. Establish `h2 : V.valuation ((s.symm x)⁻¹) < 1`. Rewrite using `[map_inv₀]`.

Conclude with `inv_lt_one_of_one_lt₀ h1`. Establish `h3 : V.valuation (((s.symm x)⁻¹) ^ q) < 1`. Rewrite using `[map_pow]`. Conclude with `pow_lt_one₀ zero_le' h2 hq.ne'`. Establish `h4` using `(hs _ hi).2`.

Establish `h5 : V.valuation (s ((s.symm x)⁻¹)) < 1`. Use `Valuation.map_add_lt V.valuation h4 h3` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis. Rewrite `h5` using `[map_inv₀, AlgEquiv.apply_symm_apply]`. Establish `hx0 : x ≠ 0` using `fun e => hy0 (by rw [e, map_zero])`.

Establish `h6 : V.valuation x ≤ 1` using `(V.valuation_le_one_iff _).2 hx`. Establish `h7 : V.valuation (x * x⁻¹) < 1`. Rewrite using `[map_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite `h7` using `[mul_inv_cancel₀ hx0, map_one]`.

Conclude with `lt_irrefl _ h7`.
-/
theorem exists_frobV {q : ℕ} (hq : 0 < q) {s : Ω ≃ₐ[ℚ] Ω} (h : FrobAt q s) : ∃ V, ES.FrobV V q s := by
  obtain ⟨V, hV, hs⟩ := h
  refine ⟨V, hV, fun x hx => ⟨(hs x hx).1, ?_, (hs x hx).2⟩⟩
  by_contra hy
  have hy0 : s.symm x ≠ 0 := fun e => hy (e ▸ V.zero_mem)
  have hi : (s.symm x)⁻¹ ∈ V := (V.mem_or_inv_mem _).resolve_left hy
  have h1 : 1 < V.valuation (s.symm x) := by
    by_contra hle
    exact hy ((V.valuation_le_one_iff _).1 (not_lt.1 hle))
  have h2 : V.valuation ((s.symm x)⁻¹) < 1 := by
    rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ h1
  have h3 : V.valuation (((s.symm x)⁻¹) ^ q) < 1 := by
    rw [map_pow]; exact pow_lt_one₀ zero_le' h2 hq.ne'
  have h4 := (hs _ hi).2
  have h5 : V.valuation (s ((s.symm x)⁻¹)) < 1 := by
    have := Valuation.map_add_lt V.valuation h4 h3
    rwa [sub_add_cancel] at this
  rw [map_inv₀, AlgEquiv.apply_symm_apply] at h5
  have hx0 : x ≠ 0 := fun e => hy0 (by rw [e, map_zero])
  have h6 : V.valuation x ≤ 1 := (V.valuation_le_one_iff _).2 hx
  have h7 : V.valuation (x * x⁻¹) < 1 := by
    rw [map_mul]
    calc V.valuation x * V.valuation x⁻¹ ≤ 1 * V.valuation x⁻¹ := mul_le_mul_left h6 _
      _ < 1 := by rwa [one_mul]
  rw [mul_inv_cancel₀ hx0, map_one] at h7
  exact lt_irrefl _ h7

/- English proof (translation)
Rewrite using `[← Units.val_mul, ← map_mul]`. Establish `: s.toRingEquiv * s.symm.toRingEquiv = 1`. Use extensionality with `x`. Conclude with `s.apply_symm_apply x`. Rewrite using `[this, map_one, Units.val_one]`.
-/
theorem chi_mul_symm (l : ℕ) [Fact l.Prime] (s : Ω ≃ₐ[ℚ] Ω) :
    (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) * (cyclotomicCharacter Ω l s.symm.toRingEquiv : ℤ_[l]) = 1 := by
  rw [← Units.val_mul, ← map_mul]
  have : s.toRingEquiv * s.symm.toRingEquiv = 1 := by
    ext x; exact s.apply_symm_apply x
  rw [this, map_one, Units.val_one]

/- English proof (translation)
Establish `h1 : ∀ f, X.gal 1 f = f` using `fun f => by`. Apply `(X.gal 1).injective` to reduce the goal to its premises. Rewrite using `[← X.gal_mul_apply, mul_one]`. Establish `h2 : (X.gal s.symm).trans (X.gal s) = RingEquiv.refl _`. Use extensionality with `f`.

Establish `: s * s.symm = 1` using `mul_inv_cancel s`. Rewrite using `[RingEquiv.trans_apply, ← X.gal_mul_apply, this, h1]`. Both sides reduce to the same expression. Use function extensionality and compare the values at `u`. Use `show X.kmap l (X.gal s) (X.kmap l (X.gal s.symm) (b _)) = b u`.

Rewrite using `[X.kmap_kmap, h2, X.kmap_refl]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Use `fin_cases i`. Simplify using the standard rewrite rules.

Use `chi_mul_symm l s` as an intermediate fact. Simplify using `only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]`. Rewrite using `[← mul_assoc, mul_comm (cyclotomicCharacter Ω l s.symm.toRingEquiv : ℤ_[l]), this, one_mul]`.
-/
theorem galB_galB_symm (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (s : Ω ≃ₐ[ℚ] Ω) (b : X.Fn l) :
    X.galB l s (X.galB l s.symm b) = b := by
  have h1 : ∀ f, X.gal 1 f = f := fun f => by
    apply (X.gal 1).injective
    rw [← X.gal_mul_apply, mul_one]
  have h2 : (X.gal s.symm).trans (X.gal s) = RingEquiv.refl _ := by
    ext f
    have : s * s.symm = 1 := mul_inv_cancel s
    rw [RingEquiv.trans_apply, ← X.gal_mul_apply, this, h1]; rfl
  funext u
  show X.kmap l (X.gal s) (X.kmap l (X.gal s.symm) (b _)) = b u
  rw [X.kmap_kmap, h2, X.kmap_refl]
  congr 1
  funext i
  fin_cases i
  · simp
  · have := chi_mul_symm l s
    simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [← mul_assoc, mul_comm (cyclotomicCharacter Ω l s.symm.toRingEquiv : ℤ_[l]), this, one_mul]

def defect (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (M q : ℕ) (σ : SL(2, ℤ)) (s : Ω ≃ₐ[ℚ] Ω) :
    X.Khat l →ₗ[ℤ_[l]] X.Khat l :=
  (∑ j ∈ Finset.range q, X.kmap l (X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)])).toRingEquiv) +
    X.kmap l (X.sl (toGQ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1]))).toRingEquiv -
    (X.kmap l (X.gal s) + (q : ℤ_[l]) • (X.kmap l (X.gal s.symm)).comp (X.kmap l (X.sl (ofSL σ)).toRingEquiv))

/- English proof (translation)
Take `⟨-, hiff, hmul, hone, -, hk, -⟩` from `H3.cls_props Ω ε X l n`. Establish `hprod : ∀ (t : Finset ℕ) (F : ℕ → X.Kˣ), X.cls l n (∏ j ∈ t, F j) = ∑ j ∈ t, X.cls l n (F j)`. Introduce `t F`. Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty => simpa using hone`.

Consider the case `insert a t ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, hmul, ih]`. Establish `hpow : ∀ (k : ℕ) (F : X.Kˣ), X.cls l n (F ^ k) = (k : ℤ_[l]) • X.cls l n F`. Introduce `k F`. Proceed by induction on `k with`. Consider the case `zero => simpa using hone`.

Consider the case `succ k ih => rw [pow_succ, hmul, ih, Nat.cast_succ, add_smul, one_smul]`. Rewrite using `[AdicCompletion.pow_smul_top_eq_ker_eval (Submodule.fg_span_singleton _), LinearMap.mem_ker]`. Simplify using `only [defect, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.sum_apply, map_sub, map_add, map_sum, map_smul]`. Rewrite using `[hk _ _ _ hc, hk _ _ _ hc, hk _ _ _ (hk _ _ _ hc), Finset.sum_congr rfl (fun j _ => hk _ _ _ hc), sub_eq_zero, ← hprod, ← hmul, ← hpow, ← hmul, hiff]`. Use `⟨g, Units.ext ?_⟩` and prove the remaining obligations.

Simplify using `using h`.
-/
theorem defect_mem (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n M q : ℕ) (σ : SL(2, ℤ)) (s : Ω ≃ₐ[ℚ] Ω)
    (c : X.Khat l) (f g : X.Kˣ) (hc : AdicCompletion.eval (idl l) (X.Kl l) n c = X.cls l n f)
    (h : (∏ j ∈ Finset.range q, X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)]) (f : X.K)) *
      X.sl (toGQ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) (f : X.K) =
      X.gal s (f : X.K) * (X.gal s.symm (X.sl (ofSL σ) (f : X.K))) ^ q * (g : X.K) ^ (l ^ n)) :
    defect X l M q σ s c ∈ (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l)) := by
  obtain ⟨-, hiff, hmul, hone, -, hk, -⟩ := H3.cls_props Ω ε X l n
  have hprod : ∀ (t : Finset ℕ) (F : ℕ → X.Kˣ), X.cls l n (∏ j ∈ t, F j) = ∑ j ∈ t, X.cls l n (F j) := by
    intro t F
    induction t using Finset.induction_on with
    | empty => simpa using hone
    | insert a t ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, hmul, ih]
  have hpow : ∀ (k : ℕ) (F : X.Kˣ), X.cls l n (F ^ k) = (k : ℤ_[l]) • X.cls l n F := by
    intro k F
    induction k with
    | zero => simpa using hone
    | succ k ih => rw [pow_succ, hmul, ih, Nat.cast_succ, add_smul, one_smul]
  rw [AdicCompletion.pow_smul_top_eq_ker_eval (Submodule.fg_span_singleton _), LinearMap.mem_ker]
  simp only [defect, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.sum_apply, map_sub, map_add, map_sum, map_smul]
  rw [hk _ _ _ hc, hk _ _ _ hc, hk _ _ _ (hk _ _ _ hc), Finset.sum_congr rfl (fun j _ => hk _ _ _ hc),
    sub_eq_zero, ← hprod, ← hmul, ← hpow, ← hmul, hiff]
  refine ⟨g, Units.ext ?_⟩
  simpa using h

/- English proof (translation)
Rewrite using `[Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Take `⟨k, hk⟩` from `(ZMod.intCast_zmod_eq_zero_iff_dvd x M).1 hx`. Take `⟨m, hm⟩` from `hM`. Conclude with `⟨(m : ℤ_[l]) * (k : ℤ_[l]), by rw [hk, hm]; push_cast; ring⟩`.
-/
theorem int_mem_pow {l : ℕ} [Fact l.Prime] {n M : ℕ} (hM : l ^ n ∣ M) {x : ℤ} (hx : (x : ZMod M) = 0) :
    (x : ℤ_[l]) ∈ (idl l) ^ n := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd x M).1 hx
  obtain ⟨m, hm⟩ := hM
  exact ⟨(m : ℤ_[l]) * (k : ℤ_[l]), by rw [hk, hm]; push_cast; ring⟩

/- English proof (translation)
Establish `h2 : IsCoprime (q : ℤ) ((M : ℤ) * M)`. Use `Nat.isCoprime_iff_coprime.2 h` as an intermediate fact. Conclude with `this.mul_right this`. Take `⟨a, k, e⟩` from `h2`. Use `⟨⟨!![a, (M : ℤ); -k * M, (q : ℤ)], ?_⟩, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Matrix.det_fin_two_of]`. Take the linear combination `e`. Apply the tactic sequence `all_goals simp [en]`.
-/
theorem exists_diag (M q : ℕ) (h : Nat.Coprime q M) :
    ∃ σ : SL(2, ℤ), (en σ 0 1 : ZMod M) = 0 ∧ (en σ 1 0 : ZMod M) = 0 ∧ (en σ 1 1 : ZMod M) = q := by
  have h2 : IsCoprime (q : ℤ) ((M : ℤ) * M) := by
    have := Nat.isCoprime_iff_coprime.2 h
    exact this.mul_right this
  obtain ⟨a, k, e⟩ := h2
  refine ⟨⟨!![a, (M : ℤ); -k * M, (q : ℤ)], ?_⟩, ?_, ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]; linear_combination e
  all_goals simp [en]

/- English proof (translation)
Establish `hbB : b ∈ X.B N l w` using `Submodule.subset_span hb`. Establish `cast : ∀ {D : ℕ}, D ∣ M → ∀ {x y : ℤ}, (x : ZMod M) = y → (x : ZMod D) = y`. Introduce `D hD x y hxy`. Use `congrArg (ZMod.castHom hD (ZMod D)) hxy` as an intermediate fact. Simplify using `using this`.

Establish `hσ : IsDiam N l q σ`. Use `⟨⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Use `CongruenceSubgroup.Gamma0_mem.2 ?_` and prove the remaining obligations. Simplify `cast hN (x := en σ 1 0) (y := 0) (by simpa using h10)` using `[en]`. Use `CongruenceSubgroup.Gamma0_mem.2 ?_` and prove the remaining obligations.

Simplify `cast hl (x := en σ 1 0) (y := 0) (by simpa using h10)` using `[en]`. Simplify `h11)` using `using cast hN (x := en σ 1 1) (y := (q : ℤ)) (by simpa`. Establish `hdet : (0 : ℤ) < (!![(q : ℤ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).det`. Simplify `hq` using `[Matrix.det_fin_two]`. Establish `hdiam : X.diam N l q b = X.act l (σ : Matrix (Fin 2) (Fin 2) ℤ) b` using `(X.act_isDiam_eq hbB hσ).symm`.

Establish `hT : X.heckeT N l q b = ∑ j ∈ Finset.range q, X.act l !![1, (j * M : ℤ); 0, (q : ℤ)] b + X.act l ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1]) b`. Rewrite using `[← ES.sum_act_upper_rep ε X N l q M hq hqM b hb.2, Tower.heckeT, LinearMap.add_apply, LinearMap.sum_apply, ← Tower.act_act Ω ε X l _ _ (by simp) hdet, ← Tower.act_act Ω ε X l _ _ (by simp) hdet, X.act_isDiam_eq hbB hσ]`. Establish `e01` using `int_mem_pow hln h01`. Establish `e10` using `int_mem_pow hln h10`. Establish `e11 : ((en σ 1 1 - q : ℤ) : ℤ_[l]) ∈ (idl l) ^ n` using `int_mem_pow hln (by push_cast; rw [h11, sub_self])`.

Establish `e00 : ((en σ 0 0 * q - 1 : ℤ) : ℤ_[l]) ∈ (idl l) ^ n`. Use `int_mem_pow hln ?_` and prove the remaining obligations. Establish `hd : en σ 0 0 * en σ 1 1 - en σ 0 1 * en σ 1 0 = 1`. Use `σ.det_coe` as an intermediate fact. Rewrite `this` using `[Matrix.det_fin_two]`. Then use the resulting hypothesis.

Use `congrArg (Int.cast : ℤ → ZMod M) hd` as an intermediate fact. Move the coercions through the operations in `at this ⊢`. Rewrite `this` using `[h01, h11]`. Take the linear combination `this`. Establish `eM : ((M : ℤ) : ℤ_[l]) ∈ (idl l) ^ n` using `int_mem_pow hln (by simp)`.

Move the coercions through the operations in `at e11 e00 eM`. Use `set v : Fin 2 → ℤ_[l] := ![u 0, (q : ℤ_[l]) * u 1] with hv`. Establish `hA : ∀ j : ℕ, X.act l !![1, (j * M : ℤ); 0, (q : ℤ)] b u - X.kmap l (X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)])).toRingEquiv (b v) ∈ (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l))`. Introduce `j`. Use `show X.kmap l _ _ - _ ∈ _`.

Rewrite using `[← map_sub]`. Use `map_mem_smul_top _ _ (X.B_sub_mem N l w b hbB n _ _ ?_)` and prove the remaining obligations. Introduce `i`. Use `fin_cases i`. Establish `: (mZl l !![1, (j * M : ℤ); 0, (q : ℤ)] *ᵥ u) 0 - v 0 = (M : ℤ_[l]) * (j * u 1)`.

Simplify using `[mZl, hv, Matrix.mulVec, dotProduct, Fin.sum_univ_two]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `this ▸ Ideal.mul_mem_right _ _ eM`. Establish `: (mZl l !![1, (j * M : ℤ); 0, (q : ℤ)] *ᵥ u) 1 - v 1 = 0`. Simplify using `[mZl, hv, Matrix.mulVec, dotProduct, Fin.sum_univ_two]`.

Conclude with `this ▸ Ideal.zero_mem _`. Establish `key : ∀ i, (mZl l (σ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ ![(q : ℤ_[l]) * u 0, u 1]) i - v i ∈ (idl l) ^ n`. Introduce `i`. Use `fin_cases i`. Establish `: (mZl l (σ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ ![(q : ℤ_[l]) * u 0, u 1]) 0 - v 0 = ((en σ 0 0 : ℤ_[l]) * q - 1) * u 0 + (en σ 0 1 : ℤ_[l]) * u 1`.

Simplify using `[mZl, hv, en, Matrix.mulVec, dotProduct, Fin.sum_univ_two]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `this ▸ Ideal.add_mem _ (Ideal.mul_mem_right _ _ e00) (Ideal.mul_mem_right _ _ e01)`. Establish `: (mZl l (σ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ ![(q : ℤ_[l]) * u 0, u 1]) 1 - v 1 = (en σ 1 0 : ℤ_[l]) * (q * u 0) + ((en σ 1 1 : ℤ_[l]) - q) * u 1`. Simplify using `[mZl, hv, en, Matrix.mulVec, dotProduct, Fin.sum_univ_two]`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `this ▸ Ideal.add_mem _ (Ideal.mul_mem_right _ _ e10) (Ideal.mul_mem_right _ _ e11)`. Establish `hB : X.act l ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1]) b u - X.kmap l (X.sl (toGQ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1]))).toRingEquiv (b v) ∈ (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l))` using `by show X.kmap l _ _ - _ ∈ _`. Rewrite using `[← map_sub]`. Use `map_mem_smul_top _ _ (X.B_sub_mem N l w b hbB n _ _ ?_)` and prove the remaining obligations.

Establish `: mZl l !![(q : ℤ), 0; 0, 1] *ᵥ u = ![(q : ℤ_[l]) * u 0, u 1]`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `fin_cases i <;> simp [mZl, Matrix.mulVec, dotProduct, Fin.sum_univ_two]`. Rewrite using `[mZl_mul, ← Matrix.mulVec_mulVec, this]`. Conclude with `key`.

Establish `hhom : ∀ x : Fin 2 → ℤ_[l], ((q : ℤ_[l]) ^ w) • b x = b ((q : ℤ_[l]) • x)`. Take `⟨c, -, hc⟩` from `hb.1`. Introduce `x`. Rewrite using `[hc, hc, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[smul_smul]`. Use `congr 1`. Establish `hi : (i : ℕ) + (w - i) = w` using `Nat.add_sub_cancel' (Nat.lt_succ_iff.1 i.2)`. Simplify using `only [Pi.smul_apply, smul_eq_mul, mul_pow]`. Establish `hp : (q : ℤ_[l]) ^ w = (q : ℤ_[l]) ^ (i : ℕ) * (q : ℤ_[l]) ^ (w - i)` using `by rw [← pow_add, hi]`.

Rewrite using `[hp]`. Expand and normalize the polynomial expressions, which then agree. Establish `hC : (((q : ℤ_[l]) ^ (w + 1)) • X.galB l s.symm (X.diam N l q b)) u - (q : ℤ_[l]) • X.kmap l (X.gal s.symm) (X.kmap l (X.sl (ofSL σ)).toRingEquiv (b v)) ∈ (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l))`. Rewrite using `[hdiam, Pi.smul_apply, pow_succ', mul_smul, ← smul_sub]`. Use `Submodule.smul_mem _ _ ?_` and prove the remaining obligations.

Use `show ((q : ℤ_[l]) ^ w) • X.kmap l (X.gal s.symm) (X.kmap l (X.sl (toGQ _)).toRingEquiv (b _)) - _ ∈ _`. Rewrite using `[MobLaws.toGQ_SL, ← map_smul, ← map_smul, ← map_sub, ← map_sub, hhom]`. Use `map_mem_smul_top _ _ (map_mem_smul_top _ _ (X.B_sub_mem N l w b hbB n _ _ ?_))` and prove the remaining obligations. Establish `h1` using `chi_mul_symm l s`. Rewrite `h1` using `[hχ]`.

Establish `: (q : ℤ_[l]) • ![u 0, (cyclotomicCharacter Ω l s.symm.toRingEquiv : ℤ_[l]) * u 1] = ![(q : ℤ_[l]) * u 0, u 1]`. Use function extensionality and compare the values at `i`. Use `fin_cases i`. Simplify using the standard rewrite rules. Simplify using `only [Fin.mk_one, Pi.smul_apply, Matrix.cons_val_one, Matrix.cons_val_zero, smul_eq_mul]`.

Rewrite using `[← mul_assoc, h1, one_mul]`. Rewrite using `[← Matrix.mulVec_smul, this]`. Conclude with `key`. Establish `hG : X.galB l s b u = X.kmap l (X.gal s) (b v)` using `by show X.kmap l (X.gal s) (b ![u 0, (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) * u 1]) = _`. Rewrite using `[hχ]`.

Establish `hS` using `Submodule.sum_mem _ (fun j (_ : j ∈ Finset.range q) => hA j)`. Establish `hall` using `Submodule.sub_mem _ (Submodule.sub_mem _ (Submodule.sub_mem _ hC hS) hB) (hD v)`. Use `hall using 1` and compare the differences between its conclusion and the goal. Simplify using `only [defect, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.sum_apply, hT, Pi.add_apply, Pi.sub_apply, Finset.sum_apply, hG, Finset.sum_sub_distrib]`. Normalize the expressions using the abelian group laws.
-/
theorem rel_of_defect [IsAlgClosure ℚ Ω] (X : Tower Ω ε) (N l w : ℕ) [Fact l.Prime] (n M q : ℕ) (σ : SL(2, ℤ))
    (s : Ω ≃ₐ[ℚ] Ω) (b : X.Fn l) (hb : b ∈ X.BSet N l w) (hN : N ∣ M) (hl : l ∣ M) (hln : l ^ n ∣ M)
    (hq : 0 < q) (hqM : Nat.Coprime q M) (hχ : (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) = q)
    (h01 : (en σ 0 1 : ZMod M) = 0) (h10 : (en σ 1 0 : ZMod M) = 0) (h11 : (en σ 1 1 : ZMod M) = q)
    (hD : ∀ v, defect X l M q σ s (b v) ∈ (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l))) (u : Fin 2 → ℤ_[l]) :
    (X.galB l s b - X.heckeT N l q b + ((q : ℤ_[l]) ^ (w + 1)) • X.galB l s.symm (X.diam N l q b)) u ∈
      (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l)) := by
  have hbB : b ∈ X.B N l w := Submodule.subset_span hb
  have cast : ∀ {D : ℕ}, D ∣ M → ∀ {x y : ℤ}, (x : ZMod M) = y → (x : ZMod D) = y := by
    intro D hD x y hxy
    have := congrArg (ZMod.castHom hD (ZMod D)) hxy
    simpa using this
  have hσ : IsDiam N l q σ := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · refine CongruenceSubgroup.Gamma0_mem.2 ?_
      simpa [en] using cast hN (x := en σ 1 0) (y := 0) (by simpa using h10)
    · refine CongruenceSubgroup.Gamma0_mem.2 ?_
      simpa [en] using cast hl (x := en σ 1 0) (y := 0) (by simpa using h10)
    · simpa using cast hN (x := en σ 1 1) (y := (q : ℤ)) (by simpa using h11)
  have hdet : (0 : ℤ) < (!![(q : ℤ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).det := by
    simpa [Matrix.det_fin_two] using hq
  have hdiam : X.diam N l q b = X.act l (σ : Matrix (Fin 2) (Fin 2) ℤ) b := (X.act_isDiam_eq hbB hσ).symm
  have hT : X.heckeT N l q b = ∑ j ∈ Finset.range q, X.act l !![1, (j * M : ℤ); 0, (q : ℤ)] b +
      X.act l ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1]) b := by
    rw [← ES.sum_act_upper_rep ε X N l q M hq hqM b hb.2, Tower.heckeT, LinearMap.add_apply, LinearMap.sum_apply,
      ← Tower.act_act Ω ε X l _ _ (by simp) hdet, ← Tower.act_act Ω ε X l _ _ (by simp) hdet,
      X.act_isDiam_eq hbB hσ]
  have e01 := int_mem_pow hln h01
  have e10 := int_mem_pow hln h10
  have e11 : ((en σ 1 1 - q : ℤ) : ℤ_[l]) ∈ (idl l) ^ n := int_mem_pow hln (by push_cast; rw [h11, sub_self])
  have e00 : ((en σ 0 0 * q - 1 : ℤ) : ℤ_[l]) ∈ (idl l) ^ n := by
    refine int_mem_pow hln ?_
    have hd : en σ 0 0 * en σ 1 1 - en σ 0 1 * en σ 1 0 = 1 := by
      have := σ.det_coe
      rwa [Matrix.det_fin_two] at this
    have := congrArg (Int.cast : ℤ → ZMod M) hd
    push_cast at this ⊢
    rw [h01, h11] at this
    linear_combination this
  have eM : ((M : ℤ) : ℤ_[l]) ∈ (idl l) ^ n := int_mem_pow hln (by simp)
  push_cast at e11 e00 eM
  set v : Fin 2 → ℤ_[l] := ![u 0, (q : ℤ_[l]) * u 1] with hv
  have hA : ∀ j : ℕ, X.act l !![1, (j * M : ℤ); 0, (q : ℤ)] b u -
      X.kmap l (X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)])).toRingEquiv (b v) ∈
      (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l)) := by
    intro j
    show X.kmap l _ _ - _ ∈ _
    rw [← map_sub]
    refine map_mem_smul_top _ _ (X.B_sub_mem N l w b hbB n _ _ ?_)
    intro i
    fin_cases i
    · have : (mZl l !![1, (j * M : ℤ); 0, (q : ℤ)] *ᵥ u) 0 - v 0 = (M : ℤ_[l]) * (j * u 1) := by
        simp [mZl, hv, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring
      exact this ▸ Ideal.mul_mem_right _ _ eM
    · have : (mZl l !![1, (j * M : ℤ); 0, (q : ℤ)] *ᵥ u) 1 - v 1 = 0 := by
        simp [mZl, hv, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      exact this ▸ Ideal.zero_mem _
  have key : ∀ i, (mZl l (σ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ ![(q : ℤ_[l]) * u 0, u 1]) i - v i ∈ (idl l) ^ n := by
    intro i
    fin_cases i
    · have : (mZl l (σ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ ![(q : ℤ_[l]) * u 0, u 1]) 0 - v 0 =
          ((en σ 0 0 : ℤ_[l]) * q - 1) * u 0 + (en σ 0 1 : ℤ_[l]) * u 1 := by
        simp [mZl, hv, en, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring
      exact this ▸ Ideal.add_mem _ (Ideal.mul_mem_right _ _ e00) (Ideal.mul_mem_right _ _ e01)
    · have : (mZl l (σ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ ![(q : ℤ_[l]) * u 0, u 1]) 1 - v 1 =
          (en σ 1 0 : ℤ_[l]) * (q * u 0) + ((en σ 1 1 : ℤ_[l]) - q) * u 1 := by
        simp [mZl, hv, en, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring
      exact this ▸ Ideal.add_mem _ (Ideal.mul_mem_right _ _ e10) (Ideal.mul_mem_right _ _ e11)
  have hB : X.act l ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1]) b u -
      X.kmap l (X.sl (toGQ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1]))).toRingEquiv (b v) ∈
      (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l)) := by
    show X.kmap l _ _ - _ ∈ _
    rw [← map_sub]
    refine map_mem_smul_top _ _ (X.B_sub_mem N l w b hbB n _ _ ?_)
    have : mZl l !![(q : ℤ), 0; 0, 1] *ᵥ u = ![(q : ℤ_[l]) * u 0, u 1] := by
      funext i
      fin_cases i <;> simp [mZl, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [mZl_mul, ← Matrix.mulVec_mulVec, this]
    exact key
  have hhom : ∀ x : Fin 2 → ℤ_[l], ((q : ℤ_[l]) ^ w) • b x = b ((q : ℤ_[l]) • x) := by
    obtain ⟨c, -, hc⟩ := hb.1
    intro x
    rw [hc, hc, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul]
    congr 1
    have hi : (i : ℕ) + (w - i) = w := Nat.add_sub_cancel' (Nat.lt_succ_iff.1 i.2)
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
    have hp : (q : ℤ_[l]) ^ w = (q : ℤ_[l]) ^ (i : ℕ) * (q : ℤ_[l]) ^ (w - i) := by rw [← pow_add, hi]
    rw [hp]; ring
  have hC : (((q : ℤ_[l]) ^ (w + 1)) • X.galB l s.symm (X.diam N l q b)) u -
      (q : ℤ_[l]) • X.kmap l (X.gal s.symm) (X.kmap l (X.sl (ofSL σ)).toRingEquiv (b v)) ∈
      (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l)) := by
    rw [hdiam, Pi.smul_apply, pow_succ', mul_smul, ← smul_sub]
    refine Submodule.smul_mem _ _ ?_
    show ((q : ℤ_[l]) ^ w) • X.kmap l (X.gal s.symm) (X.kmap l (X.sl (toGQ _)).toRingEquiv (b _)) - _ ∈ _
    rw [MobLaws.toGQ_SL, ← map_smul, ← map_smul, ← map_sub, ← map_sub, hhom]
    refine map_mem_smul_top _ _ (map_mem_smul_top _ _ (X.B_sub_mem N l w b hbB n _ _ ?_))
    have h1 := chi_mul_symm l s
    rw [hχ] at h1
    have : (q : ℤ_[l]) • ![u 0, (cyclotomicCharacter Ω l s.symm.toRingEquiv : ℤ_[l]) * u 1] =
        ![(q : ℤ_[l]) * u 0, u 1] := by
      funext i
      fin_cases i
      · simp
      · simp only [Fin.mk_one, Pi.smul_apply, Matrix.cons_val_one, Matrix.cons_val_zero, smul_eq_mul]
        rw [← mul_assoc, h1, one_mul]
    rw [← Matrix.mulVec_smul, this]
    exact key
  have hG : X.galB l s b u = X.kmap l (X.gal s) (b v) := by
    show X.kmap l (X.gal s) (b ![u 0, (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) * u 1]) = _
    rw [hχ]
  have hS := Submodule.sum_mem _ (fun j (_ : j ∈ Finset.range q) => hA j)
  have hall := Submodule.sub_mem _ (Submodule.sub_mem _ (Submodule.sub_mem _ hC hS) hB) (hD v)
  convert hall using 1
  simp only [defect, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.sum_apply, hT, Pi.add_apply, Pi.sub_apply, Finset.sum_apply, hG, Finset.sum_sub_distrib]
  abel

/- English proof (translation)
Establish `hl : l.Prime` using `Fact.out`. Take `⟨c, hcA, hc⟩` from `hb.1`. Use `choose f hfU hf using fun i => ES.exists_un_eval_eq_cls ε X hj l n (c i) (hcA i)`. Use `choose m hm0 hm using fun i => X.level (f i : X.K)`. Use `set M : ℕ := N * (l * l ^ n) * ∏ i, m i with hM`.

Establish `hM0 : 0 < M` using `Nat.mul_pos (Nat.mul_pos hN (Nat.mul_pos hl.pos (pow_pos hl.pos n))) (Finset.prod_pos fun i _ => hm0 i)`. Establish `hNM : N ∣ M` using `⟨_, by rw [hM, mul_assoc]⟩`. Establish `hlM : l ∣ M` using `⟨N * l ^ n * ∏ i, m i, by rw [hM]; ring⟩`. Establish `hnM : l ^ n ∣ M` using `⟨N * l * ∏ i, m i, by rw [hM]; ring⟩`. Establish `hmM : ∀ i, m i ∣ M` using `fun i => Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) _`.

Use `choose S hS using fun i => GlobalTheory.T.eichlerShimura_kummer_modularUnit ε X hε hj l M n (f i) hM0 hlM (hfU i) (fun γ hγ => hm i γ (gamma_le_of_dvd (hmM i) hγ))`. Use `⟨Finset.univ.biUnion S ∪ M.primeFactors, fun q hq hqS s hs u => ?_⟩` and prove the remaining obligations. Rewrite `hqS` using `[Finset.mem_union, not_or, Finset.mem_biUnion, Nat.mem_primeFactors]`. Establish `hqM : ¬ q ∣ M` using `fun h => hqS.2 ⟨hq, h, hM0.ne'⟩`. Establish `hcop : Nat.Coprime q M` using `(Nat.Prime.coprime_iff_not_dvd hq).2 hqM`.

Establish `hql : q ≠ l` using `fun h => hqM (h ▸ hlM)`. Take `⟨V, hV⟩` from `exists_frobV hq.pos hs`. Take `⟨σ, h01, h10, h11⟩` from `exists_diag M q hcop`. Use `rel_of_defect X N l w n M q σ s b hb hNM hlM hnM hq.pos hcop (ES.cyclotomicCharacter_frobV l q hq hql V s hV) h01 h10 h11 (fun v => ?_) u` and prove the remaining obligations. Rewrite using `[hc, map_sum]`.

Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul]`. Take `⟨g, hg⟩` from `hS i q hq (fun h => hqS.1 ⟨i, Finset.mem_univ i, h⟩) s hs σ ⟨h01, h10, h11⟩`. Conclude with `Submodule.smul_mem _ _ (defect_mem X l n M q σ s (c i) (f i) g (hf i) hg)`.
-/
theorem rel_BSet [IsAlgClosure ℚ Ω] (X : Tower Ω ε) (hε : Function.Injective ε)
    (hj : ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) (N l w : ℕ) [Fact l.Prime] (hN : 0 < N)
    (n : ℕ) (b : X.Fn l) (hb : b ∈ X.BSet N l w) :
    ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ s : Ω ≃ₐ[ℚ] Ω, FrobAt q s → ∀ u,
      (X.galB l s b - X.heckeT N l q b + ((q : ℤ_[l]) ^ (w + 1)) • X.galB l s.symm (X.diam N l q b)) u ∈
        (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l)) := by
  classical
  have hl : l.Prime := Fact.out
  obtain ⟨c, hcA, hc⟩ := hb.1
  choose f hfU hf using fun i => ES.exists_un_eval_eq_cls ε X hj l n (c i) (hcA i)
  choose m hm0 hm using fun i => X.level (f i : X.K)
  set M : ℕ := N * (l * l ^ n) * ∏ i, m i with hM
  have hM0 : 0 < M := Nat.mul_pos (Nat.mul_pos hN (Nat.mul_pos hl.pos (pow_pos hl.pos n)))
    (Finset.prod_pos fun i _ => hm0 i)
  have hNM : N ∣ M := ⟨_, by rw [hM, mul_assoc]⟩
  have hlM : l ∣ M := ⟨N * l ^ n * ∏ i, m i, by rw [hM]; ring⟩
  have hnM : l ^ n ∣ M := ⟨N * l * ∏ i, m i, by rw [hM]; ring⟩
  have hmM : ∀ i, m i ∣ M := fun i => Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) _
  choose S hS using fun i => GlobalTheory.T.eichlerShimura_kummer_modularUnit ε X hε hj l M n (f i) hM0 hlM (hfU i)
    (fun γ hγ => hm i γ (gamma_le_of_dvd (hmM i) hγ))
  refine ⟨Finset.univ.biUnion S ∪ M.primeFactors, fun q hq hqS s hs u => ?_⟩
  rw [Finset.mem_union, not_or, Finset.mem_biUnion, Nat.mem_primeFactors] at hqS
  have hqM : ¬ q ∣ M := fun h => hqS.2 ⟨hq, h, hM0.ne'⟩
  have hcop : Nat.Coprime q M := (Nat.Prime.coprime_iff_not_dvd hq).2 hqM
  have hql : q ≠ l := fun h => hqM (h ▸ hlM)
  obtain ⟨V, hV⟩ := exists_frobV hq.pos hs
  obtain ⟨σ, h01, h10, h11⟩ := exists_diag M q hcop
  refine rel_of_defect X N l w n M q σ s b hb hNM hlM hnM hq.pos hcop
    (ES.cyclotomicCharacter_frobV l q hq hql V s hV) h01 h10 h11 (fun v => ?_) u
  rw [hc, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_smul]
  obtain ⟨g, hg⟩ := hS i q hq (fun h => hqS.1 ⟨i, Finset.mem_univ i, h⟩) s hs σ ⟨h01, h10, h11⟩
  exact Submodule.smul_mem _ _ (defect_mem X l n M q σ s (c i) (f i) g (hf i) hg)

end GlobalTheory.KZ.ESmod

namespace GlobalTheory.KZ

open ESmod in

/- English proof (translation)
Introduce `Ω _ _ _ ε X hε hj N l w _ hl2 hN hNl hw n`. Establish `hl : l.Prime` using `Fact.out`. Establish `hfg : (Submodule.span ℤ_[l] (X.BSet N l w)).FG` using `Module.Finite.iff_fg.1 (GlobalTheory.T.kummerBettiModule_free_finite ε X hε hj N l w hl2 hN hNl hw).2`. Take `⟨G, hG, hspan⟩` from `(Submodule.fg_span_iff_fg_span_finset_subset _).1 hfg`. Use `choose S hS using fun b : G => rel_BSet X hε hj N l w (by omega) n b (hG b.2)`.

Use `⟨Finset.univ.biUnion S ∪ (N * l).primeFactors, fun q hq hqS s hs b hb u => ?_⟩` and prove the remaining obligations. Rewrite `hqS` using `[Finset.mem_union, not_or, Finset.mem_biUnion, Nat.mem_primeFactors]`. Establish `hadm : admitted N l (Letter.T q)` using `⟨hq, fun h => hqS.2 ⟨hq, h, Nat.mul_ne_zero (by omega) hl.ne_zero⟩⟩`. Set `L : X.Fn l →ₗ[ℤ_[l]] X.Fn l` to `X.galB l s - X.heckeT N l q + ((q : ℤ_[l]) ^ (w + 1)) • (X.galB l s.symm).comp (X.diam N l q)`. Establish `hL : ∀ u, L b u ∈ (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l))`.

Establish `hb' : b ∈ Submodule.span ℤ_[l] (G : Set (X.Fn l))` using `hspan ▸ hb`. Use `clear hb`. Proceed by induction on `hb' using Submodule.span_induction with`. Consider the case `mem x hx => exact hS ⟨x, hx⟩ q hq (fun h => hqS.1 ⟨_, Finset.mem_univ _, h⟩) s hs`. Consider the case `zero => intro u`.

Rewrite using `[map_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy => intro u`. Rewrite using `[map_add]`. Conclude with `Submodule.add_mem _ (hx u) (hy u)`.

Consider the case `smul a x _ hx => intro u`. Rewrite using `[map_smul]`. Conclude with `Submodule.smul_mem _ _ (hx u)`. Establish `hcomm : X.heckeT N l q (X.galB l s b) = X.galB l s (X.heckeT N l q b)` using `GlobalTheory.T.hecke_operator_comm_galois_action_modular_tower ε X hε hj N l w hl2 hN hNl hw (Letter.T q) hadm s b hb`. Establish `e : X.galB l s (X.galB l s b) - X.heckeT N l q (X.galB l s b) + ((q : ℤ_[l]) ^ (w + 1)) • X.diam N l q b = X.galB l s (L b)`.

Simplify using `only [L, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply, map_add, map_sub, map_smul, galB_galB_symm, hcomm]`. Rewrite using `[e]`. Conclude with `map_mem_smul_top _ (X.kmap l (X.gal s)) (hL _)`.
-/
theorem eichlerShimura_B_mod : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ n : ℕ, ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ s : Ω ≃ₐ[ℚ] Ω, FrobAt q s → ∀ b ∈ X.B N l w, ∀ u, (X.galB l s (X.galB l s b) - X.heckeT N l q (X.galB l s b) + ((q : ℤ_[l]) ^ (w + 1)) • X.diam N l q b) u ∈ (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l)) := by
  classical
  intro Ω _ _ _ ε X hε hj N l w _ hl2 hN hNl hw n
  have hl : l.Prime := Fact.out
  have hfg : (Submodule.span ℤ_[l] (X.BSet N l w)).FG :=
    Module.Finite.iff_fg.1 (GlobalTheory.T.kummerBettiModule_free_finite ε X hε hj N l w hl2 hN hNl hw).2
  obtain ⟨G, hG, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1 hfg
  choose S hS using fun b : G => rel_BSet X hε hj N l w (by omega) n b (hG b.2)
  refine ⟨Finset.univ.biUnion S ∪ (N * l).primeFactors, fun q hq hqS s hs b hb u => ?_⟩
  rw [Finset.mem_union, not_or, Finset.mem_biUnion, Nat.mem_primeFactors] at hqS
  have hadm : admitted N l (Letter.T q) := ⟨hq, fun h => hqS.2 ⟨hq, h, Nat.mul_ne_zero (by omega) hl.ne_zero⟩⟩
  let L : X.Fn l →ₗ[ℤ_[l]] X.Fn l :=
    X.galB l s - X.heckeT N l q + ((q : ℤ_[l]) ^ (w + 1)) • (X.galB l s.symm).comp (X.diam N l q)
  have hL : ∀ u, L b u ∈ (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l)) := by
    have hb' : b ∈ Submodule.span ℤ_[l] (G : Set (X.Fn l)) := hspan ▸ hb
    clear hb
    induction hb' using Submodule.span_induction with
    | mem x hx => exact hS ⟨x, hx⟩ q hq (fun h => hqS.1 ⟨_, Finset.mem_univ _, h⟩) s hs
    | zero => intro u; rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => intro u; rw [map_add]; exact Submodule.add_mem _ (hx u) (hy u)
    | smul a x _ hx => intro u; rw [map_smul]; exact Submodule.smul_mem _ _ (hx u)
  have hcomm : X.heckeT N l q (X.galB l s b) = X.galB l s (X.heckeT N l q b) :=
    GlobalTheory.T.hecke_operator_comm_galois_action_modular_tower ε X hε hj N l w hl2 hN hNl hw (Letter.T q) hadm s b hb
  have e : X.galB l s (X.galB l s b) - X.heckeT N l q (X.galB l s b) + ((q : ℤ_[l]) ^ (w + 1)) • X.diam N l q b =
      X.galB l s (L b) := by
    simp only [L, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply, map_add,
      map_sub, map_smul, galB_galB_symm, hcomm]
  rw [e]
  exact map_mem_smul_top _ (X.kmap l (X.gal s)) (hL _)

end GlobalTheory.KZ
