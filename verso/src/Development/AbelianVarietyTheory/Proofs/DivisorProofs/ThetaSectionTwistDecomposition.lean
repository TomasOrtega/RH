import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TranslationInv
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAddFundamentalDomainLatticeDomain
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
open Matrix MeasureTheory Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm
open scoped Real ContDiff

namespace GlobalTheory.CoverDecomp

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[per, Matrix.vecMul, dotProduct, Finset.sum_add_distrib, add_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem per_add {g : ℕ} (t : Matrix (Fin g) (Fin g) ℂ) (x y : Fl g) :
    per t (x + y) = per t x + per t y := by
  funext i
  simp [per, Matrix.vecMul, dotProduct, Finset.sum_add_distrib, add_mul]
  ring

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[per, Matrix.vecMul, dotProduct]`.
-/
theorem per_zero {g : ℕ} (t : Matrix (Fin g) (Fin g) ℂ) : per t 0 = 0 := by
  funext i
  simp [per, Matrix.vecMul, dotProduct]

/- English proof (translation)
Introduce `E _ _ g m B τ M M' j hj hMM' _ b hb f hf`. Use `haveI : Fintype (↥M' ⧸ M.submoduleOf M') := Fintype.ofFinite _`. Establish `hP : ∀ z : Fin g → ℂ, ((b, z) : Pt E g) ∈ cov B g` using `fun z => ⟨hb, trivial⟩`. Establish `hne : ∀ l ∈ M', ∀ z, j l (b, z) ≠ 0` using `fun l hl z => (hj.1 l hl).2 _ (hP z)`. Establish `hcoc : ∀ l ∈ M', ∀ l' ∈ M', ∀ z, j (l + l') (b, z) = j l (b, z + per (τ b) l') * j l' (b, z)` using `fun l hl l' hl' z => hj.2 l hl l' hl' _ (hP z)`.

Use `set G : Fl g → (Fin g → ℂ) → Ext m := fun l z => (j l (b, z))⁻¹ • f (z + per (τ b) l) with hGdef`. Establish `hGinv : ∀ l ∈ M', ∀ n ∈ M, G (n + l) = G l`. Introduce `l hl n hn`. Use function extensionality and compare the values at `z`. Simplify using `only [hGdef]`.

Establish `h1` using `hf.2 n hn (z + per (τ b) l)`. Rewrite using `[hcoc n (hMM' hn) l hl z, per_add, add_comm (per (τ b) n), ← add_assoc, h1, smul_smul]`. Use `congr 1`. Use `hne n (hMM' hn) (z + per (τ b) l)` as an intermediate fact. Clear the denominators using the available nonvanishing facts.

Establish `hGshift : ∀ l ∈ M', ∀ l' ∈ M', ∀ z, G l' (z + per (τ b) l) = j l (b, z) • G (l' + l) z`. Introduce `l hl l' hl' z`. Simplify using `only [hGdef]`. Rewrite using `[hcoc l' hl' l hl z, per_add, smul_smul, add_assoc, add_comm (per (τ b) l)]`. Use `congr 1`.

Use `hne l hl z` as an intermediate fact. Clear the denominators using the available nonvanishing facts. Establish `hGsm : ∀ l ∈ M', ContDiff ℝ ∞ (G l)`. Introduce `l hl`. Establish `hd : Differentiable ℂ (fun z : Fin g → ℂ => j l (b, z))`.

Rewrite using `[← differentiableOn_univ]`. Conclude with `(hj.1 l hl).1.comp ((differentiableOn_const b).prodMk differentiableOn_id) fun z _ => hP z`. Establish `hi : Differentiable ℂ (fun z : Fin g → ℂ => (j l (b, z))⁻¹)` using `hd.inv fun z => hne l hl z`. Establish `hc : ContDiff ℝ ∞ (fun z : Fin g → ℂ => (j l (b, z))⁻¹)` using `(GlobalTheory.SCV.contDiff_of_differentiable hi _).restrict_scalars ℝ`. Conclude with `hc.smul (hf.1.comp (contDiff_id.add contDiff_const))`.

Set `r : (↥M' ⧸ M.submoduleOf M') → ↥M'` to `Function.surjInv (Submodule.Quotient.mk_surjective (M.submoduleOf M'))`. Establish `hr : ∀ l : ↥M', G (r (Submodule.Quotient.mk l) : Fl g) = G l`. Introduce `l`. Establish `h1 : (Submodule.Quotient.mk (r (Submodule.Quotient.mk l)) : ↥M' ⧸ M.submoduleOf M') = Submodule.Quotient.mk l` using `Function.surjInv_eq _ _`. Rewrite `h1` using `[Submodule.Quotient.eq]`.

Establish `h2 : ((r (Submodule.Quotient.mk l) : Fl g) - l) ∈ M` using `h1`. Use `hGinv l l.2 _ h2` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis. Establish `hN : ((Fintype.card (↥M' ⧸ M.submoduleOf M') : ℂ)) ≠ 0` using `Nat.cast_ne_zero.2 Fintype.card_ne_zero`. Use `⟨fun χ z => ((Fintype.card (↥M' ⧸ M.submoduleOf M') : ℂ))⁻¹ • ∑ q, (χ q)⁻¹ • G (r q) z, fun χ => ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Conclude with `(ContDiff.sum fun q _ => (hGsm _ (r q).2).const_smul _).const_smul _`. Introduce `l hl z`. Simplify using `only [twistFactor, dif_pos hl]`. Use `set a : ↥M' ⧸ M.submoduleOf M' := Submodule.Quotient.mk ⟨l, hl⟩ with ha`. Establish `hshift : ∀ q, G (r q) (z + per (τ b) l) = j l (b, z) • G (r (q + a)) z`.

Introduce `q`. Rewrite using `[hGshift l hl _ (r q).2 z]`. Use `congr 1`. Establish `hq : (Submodule.Quotient.mk (r q) : ↥M' ⧸ M.submoduleOf M') = q` using `Function.surjInv_eq _ q`. Use `hr (r q + ⟨l, hl⟩)` as an intermediate fact.

Rewrite `this` using `[Submodule.Quotient.mk_add, hq]`. Conclude with `congrFun this.symm z`. Simplify using `only [hshift]`. Establish `hre : ∑ q, (χ q)⁻¹ • (j l (b, z) • G (r (q + a)) z) = ∑ q, (χ (q - a))⁻¹ • (j l (b, z) • G (r q) z)` using `Fintype.sum_equiv (Equiv.addRight a) _ _ fun q => by`. Simplify using `only [Equiv.coe_addRight, add_sub_cancel_right]`.

Establish `hχ : ∀ q, (χ (q - a))⁻¹ = χ a * (χ q)⁻¹`. Introduce `q`. Rewrite using `[sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv, mul_inv, inv_inv, mul_comm]`. Rewrite using `[hre]`. Simplify using `only [hχ, Finset.smul_sum, smul_smul]`.

Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Introduce `z`. Establish `hsum : ∀ q : ↥M' ⧸ M.submoduleOf M', ∑ χ : AddChar (↥M' ⧸ M.submoduleOf M') ℂ, (χ q)⁻¹ = if q = 0 then (Fintype.card (↥M' ⧸ M.submoduleOf M') : ℂ) else 0`.

Introduce `q`. Repeatedly rewrite using `[← AddChar.map_neg_eq_inv]`. Rewrite using `[AddChar.sum_apply_eq_ite]`. Simplify using `[neg_eq_zero]`. Establish `hj0 : j 0 (b, z) = 1`.

Establish `h` using `hcoc 0 (zero_mem _) 0 (zero_mem _) z`. Rewrite `h` using `[per_zero, add_zero, add_zero]`. Establish `h0` using `hne 0 (zero_mem _) z`. Conclude with `(mul_eq_left₀ h0).1 h.symm`. Establish `h0 : G (r 0 : Fl g) = G 0`.

Use `hr 0` as an intermediate fact. Rewrite `this` using `[Submodule.Quotient.mk_zero]`. Then use the resulting hypothesis. Rewrite using `[finsum_eq_sum_of_fintype, ← Finset.smul_sum, Finset.sum_comm]`. Simplify using `only [← Finset.sum_smul, hsum, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Rewrite using `[smul_smul, inv_mul_cancel₀ hN, one_smul, h0]`.

Simplify using `only [hGdef, hj0, inv_one, one_smul, per_zero, add_zero]`.
-/
theorem isSec_eq_finsum_twist : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g m : ℕ}
    {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ} {M M' : Submodule ℤ (Fl g)}
    {j : Fl g → Pt E g → ℂ}, IsFactor B τ M' j → M ≤ M' →
    ∀ [Finite (↥M' ⧸ M.submoduleOf M')] (b : E), b ∈ B → ∀ (f : (Fin g → ℂ) → Ext m),
    IsSec τ M j b f → ∃ F : AddChar (↥M' ⧸ M.submoduleOf M') ℂ → (Fin g → ℂ) → Ext m,
      (∀ χ, IsSec τ M' (twistFactor M M' χ j) b (F χ)) ∧ ∀ z, ∑ᶠ χ, F χ z = f z := by
  intro E _ _ g m B τ M M' j hj hMM' _ b hb f hf
  classical
  haveI : Fintype (↥M' ⧸ M.submoduleOf M') := Fintype.ofFinite _
  have hP : ∀ z : Fin g → ℂ, ((b, z) : Pt E g) ∈ cov B g := fun z => ⟨hb, trivial⟩
  have hne : ∀ l ∈ M', ∀ z, j l (b, z) ≠ 0 := fun l hl z => (hj.1 l hl).2 _ (hP z)
  have hcoc : ∀ l ∈ M', ∀ l' ∈ M', ∀ z,
      j (l + l') (b, z) = j l (b, z + per (τ b) l') * j l' (b, z) :=
    fun l hl l' hl' z => hj.2 l hl l' hl' _ (hP z)
  set G : Fl g → (Fin g → ℂ) → Ext m := fun l z => (j l (b, z))⁻¹ • f (z + per (τ b) l) with hGdef
  have hGinv : ∀ l ∈ M', ∀ n ∈ M, G (n + l) = G l := by
    intro l hl n hn
    funext z
    simp only [hGdef]
    have h1 := hf.2 n hn (z + per (τ b) l)
    rw [hcoc n (hMM' hn) l hl z, per_add, add_comm (per (τ b) n), ← add_assoc, h1, smul_smul]
    congr 1
    have := hne n (hMM' hn) (z + per (τ b) l)
    field_simp
  have hGshift : ∀ l ∈ M', ∀ l' ∈ M', ∀ z,
      G l' (z + per (τ b) l) = j l (b, z) • G (l' + l) z := by
    intro l hl l' hl' z
    simp only [hGdef]
    rw [hcoc l' hl' l hl z, per_add, smul_smul, add_assoc, add_comm (per (τ b) l)]
    congr 1
    have := hne l hl z
    field_simp
  have hGsm : ∀ l ∈ M', ContDiff ℝ ∞ (G l) := by
    intro l hl
    have hd : Differentiable ℂ (fun z : Fin g → ℂ => j l (b, z)) := by
      rw [← differentiableOn_univ]
      exact (hj.1 l hl).1.comp ((differentiableOn_const b).prodMk differentiableOn_id) fun z _ => hP z
    have hi : Differentiable ℂ (fun z : Fin g → ℂ => (j l (b, z))⁻¹) :=
      hd.inv fun z => hne l hl z
    have hc : ContDiff ℝ ∞ (fun z : Fin g → ℂ => (j l (b, z))⁻¹) :=
      (GlobalTheory.SCV.contDiff_of_differentiable hi _).restrict_scalars ℝ
    exact hc.smul (hf.1.comp (contDiff_id.add contDiff_const))
  let r : (↥M' ⧸ M.submoduleOf M') → ↥M' :=
    Function.surjInv (Submodule.Quotient.mk_surjective (M.submoduleOf M'))
  have hr : ∀ l : ↥M', G (r (Submodule.Quotient.mk l) : Fl g) = G l := by
    intro l
    have h1 : (Submodule.Quotient.mk (r (Submodule.Quotient.mk l)) : ↥M' ⧸ M.submoduleOf M') =
        Submodule.Quotient.mk l := Function.surjInv_eq _ _
    rw [Submodule.Quotient.eq] at h1
    have h2 : ((r (Submodule.Quotient.mk l) : Fl g) - l) ∈ M := h1
    have := hGinv l l.2 _ h2
    rwa [sub_add_cancel] at this
  have hN : ((Fintype.card (↥M' ⧸ M.submoduleOf M') : ℂ)) ≠ 0 :=
    Nat.cast_ne_zero.2 Fintype.card_ne_zero
  refine ⟨fun χ z => ((Fintype.card (↥M' ⧸ M.submoduleOf M') : ℂ))⁻¹ •
    ∑ q, (χ q)⁻¹ • G (r q) z, fun χ => ⟨?_, ?_⟩, ?_⟩
  · exact (ContDiff.sum fun q _ => (hGsm _ (r q).2).const_smul _).const_smul _
  · intro l hl z
    simp only [twistFactor, dif_pos hl]
    set a : ↥M' ⧸ M.submoduleOf M' := Submodule.Quotient.mk ⟨l, hl⟩ with ha
    have hshift : ∀ q, G (r q) (z + per (τ b) l) = j l (b, z) • G (r (q + a)) z := by
      intro q
      rw [hGshift l hl _ (r q).2 z]
      congr 1
      have hq : (Submodule.Quotient.mk (r q) : ↥M' ⧸ M.submoduleOf M') = q :=
        Function.surjInv_eq _ q
      have := hr (r q + ⟨l, hl⟩)
      rw [Submodule.Quotient.mk_add, hq] at this
      exact congrFun this.symm z
    simp only [hshift]
    have hre : ∑ q, (χ q)⁻¹ • (j l (b, z) • G (r (q + a)) z) =
        ∑ q, (χ (q - a))⁻¹ • (j l (b, z) • G (r q) z) :=
      Fintype.sum_equiv (Equiv.addRight a) _ _ fun q => by
        simp only [Equiv.coe_addRight, add_sub_cancel_right]
    have hχ : ∀ q, (χ (q - a))⁻¹ = χ a * (χ q)⁻¹ := by
      intro q
      rw [sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv, mul_inv, inv_inv, mul_comm]
    rw [hre]
    simp only [hχ, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun q _ => ?_
    congr 1
    ring
  · intro z
    have hsum : ∀ q : ↥M' ⧸ M.submoduleOf M', ∑ χ : AddChar (↥M' ⧸ M.submoduleOf M') ℂ, (χ q)⁻¹ =
        if q = 0 then (Fintype.card (↥M' ⧸ M.submoduleOf M') : ℂ) else 0 := by
      intro q
      simp_rw [← AddChar.map_neg_eq_inv]
      rw [AddChar.sum_apply_eq_ite]
      simp [neg_eq_zero]
    have hj0 : j 0 (b, z) = 1 := by
      have h := hcoc 0 (zero_mem _) 0 (zero_mem _) z
      rw [per_zero, add_zero, add_zero] at h
      have h0 := hne 0 (zero_mem _) z
      exact (mul_eq_left₀ h0).1 h.symm
    have h0 : G (r 0 : Fl g) = G 0 := by
      have := hr 0
      rwa [Submodule.Quotient.mk_zero] at this
    rw [finsum_eq_sum_of_fintype, ← Finset.smul_sum, Finset.sum_comm]
    simp only [← Finset.sum_smul, hsum, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
    rw [smul_smul, inv_mul_cancel₀ hN, one_smul, h0]
    simp only [hGdef, hj0, inv_one, one_smul, per_zero, add_zero]

end GlobalTheory.CoverDecomp
