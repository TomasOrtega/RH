import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SemilinearExtensionBases

noncomputable section

open scoped TensorProduct
open Module

namespace GlobalTheory.SemilinearExt

open GlobalTheory.IndefiniteRowSideFullHecke.SemilinearExtensionBases

section

variable {O K K'' : Type} [CommRing O] [Field K] [Algebra O K] [IsFractionRing O K]
  [Field K''] [Algebra O K''] [Algebra K K''] [IsScalarTower O K K'']
  {Fm : Type} [AddCommGroup Fm] [Module K Fm] [Module O Fm] [IsScalarTower O K Fm]

/- English proof (translation)
Take `⟨⟨a, b⟩, hc⟩` from `IsLocalization.mk'_surjective (nonZeroDivisors O) c`. Simplify using `only at hc`. Substitute `hc` using the available equality. Establish `hb : algebraMap O K (b : O) ≠ 0` using `(IsLocalization.map_units K b).ne_zero`. Use `set m₀ : Fm := (algebraMap O K (b : O))⁻¹ • m with hm₀`.

Establish `h1 : (b : O) • m₀ = m`. Rewrite using `[← algebraMap_smul K (b : O) m₀, hm₀, smul_smul, mul_inv_cancel₀ hb, one_smul]`. Establish `h2 : IsLocalization.mk' K a b • m = (a : O) • m₀`. Rewrite using `[← algebraMap_smul K a m₀, hm₀, smul_smul, ← div_eq_mul_inv, IsFractionRing.mk'_eq_div]`. Establish `h3 : (b : O) • algebraMap K K'' (IsLocalization.mk' K a b) = (a : O) • (1 : K'')`.

Rewrite using `[Algebra.smul_def, Algebra.smul_def, mul_one, IsScalarTower.algebraMap_apply O K K'' (b : O), IsScalarTower.algebraMap_apply O K K'' a, ← map_mul, IsLocalization.mk'_spec']`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem algebraMap_tmul (c : K) (m : Fm) :
    algebraMap K K'' c ⊗ₜ[O] m = (1 : K'') ⊗ₜ[O] (c • m) := by
  obtain ⟨⟨a, b⟩, hc⟩ := IsLocalization.mk'_surjective (nonZeroDivisors O) c
  dsimp only at hc
  subst hc
  have hb : algebraMap O K (b : O) ≠ 0 := (IsLocalization.map_units K b).ne_zero
  set m₀ : Fm := (algebraMap O K (b : O))⁻¹ • m with hm₀
  have h1 : (b : O) • m₀ = m := by
    rw [← algebraMap_smul K (b : O) m₀, hm₀, smul_smul, mul_inv_cancel₀ hb, one_smul]
  have h2 : IsLocalization.mk' K a b • m = (a : O) • m₀ := by
    rw [← algebraMap_smul K a m₀, hm₀, smul_smul, ← div_eq_mul_inv, IsFractionRing.mk'_eq_div]
  have h3 : (b : O) • algebraMap K K'' (IsLocalization.mk' K a b) = (a : O) • (1 : K'') := by
    rw [Algebra.smul_def, Algebra.smul_def, mul_one, IsScalarTower.algebraMap_apply O K K'' (b : O),
      IsScalarTower.algebraMap_apply O K K'' a, ← map_mul, IsLocalization.mk'_spec']
  calc algebraMap K K'' (IsLocalization.mk' K a b) ⊗ₜ[O] m
      = algebraMap K K'' (IsLocalization.mk' K a b) ⊗ₜ[O] ((b : O) • m₀) := by rw [h1]
    _ = ((b : O) • algebraMap K K'' (IsLocalization.mk' K a b)) ⊗ₜ[O] m₀ :=
        (TensorProduct.smul_tmul _ _ _).symm
    _ = ((a : O) • (1 : K'')) ⊗ₜ[O] m₀ := by rw [h3]
    _ = (1 : K'') ⊗ₜ[O] ((a : O) • m₀) := TensorProduct.smul_tmul _ _ _
    _ = (1 : K'') ⊗ₜ[O] (IsLocalization.mk' K a b • m) := by rw [h2]

/- English proof (translation)
Establish `: TensorProduct.CompatibleSMul O K K'' Fm` using `⟨fun c x m => by`. Rewrite using `[Algebra.smul_def, mul_comm, ← smul_eq_mul x, ← TensorProduct.smul_tmul', algebraMap_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]⟩`. Use `⟨(Algebra.TensorProduct.basis K'' b).map (TensorProduct.equivOfCompatibleSMul O K K'' K'' Fm), fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[Basis.map_apply, Algebra.TensorProduct.basis_apply]`. Both sides reduce to the same expression.
-/
theorem exists_basis_tensor {ι : Type} (b : Basis ι K Fm) :
    ∃ c : Basis ι K'' (K'' ⊗[O] Fm), ∀ i, c i = (1 : K'') ⊗ₜ[O] b i := by
  have : TensorProduct.CompatibleSMul O K K'' Fm := ⟨fun c x m => by
    rw [Algebra.smul_def, mul_comm, ← smul_eq_mul x, ← TensorProduct.smul_tmul', algebraMap_tmul,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one]⟩
  refine ⟨(Algebra.TensorProduct.basis K'' b).map (TensorProduct.equivOfCompatibleSMul O K K'' K'' Fm),
    fun i => ?_⟩
  rw [Basis.map_apply, Algebra.TensorProduct.basis_apply]
  rfl

end

def extOfBasis {L L' V V' : Type} [Field L] [Field L'] [AddCommGroup V] [Module L V] [AddCommGroup V'] [Module L' V']
    (σ : L →+* L') {n : ℕ} (B : Basis (Fin n) L V) (w : Fin n → V') : V →ₛₗ[σ] V' where
  toFun x := ∑ k, σ (B.repr x k) • w k
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a x := by simp [mul_smul, Finset.smul_sum]

/- English proof (translation)
Use `show ∑ j, σ (B.repr (B k) j) • w j = w k`. Rewrite using `[B.repr_self, Finset.sum_eq_single k]`. Simplify using the standard rewrite rules. Introduce `j _ hj`. Simplify using `[hj]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ k) h`.
-/
theorem extOfBasis_basis {L L' V V' : Type} [Field L] [Field L'] [AddCommGroup V] [Module L V] [AddCommGroup V']
    [Module L' V'] (σ : L →+* L') {n : ℕ} (B : Basis (Fin n) L V) (w : Fin n → V') (k : Fin n) :
    extOfBasis σ B w (B k) = w k := by
  show ∑ j, σ (B.repr (B k) j) • w j = w k
  rw [B.repr_self, Finset.sum_eq_single k]
  · simp
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ k) h

/- English proof (translation)
Establish `: Module.Finite L V` using `Module.Finite.of_basis B`. Establish `: Module.Finite L' V'` using `Module.Finite.of_basis C`. Establish `: Finite ι` using `Module.Finite.finite_basis b`. Use `haveI : Fintype ι := Fintype.ofFinite ι`. Establish `hspan : ⊤ ≤ Submodule.span L' (Set.range fun i => e (b i))`.

Rewrite using `[← C.span_eq, Submodule.span_le]`. Introduce and unpack `_ ⟨k, rfl⟩`. Rewrite using `[← h k, ← b.sum_repr (B k), map_sum]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smulₛₗ]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Establish `hcard : Fintype.card ι = finrank L' V'`. Rewrite using `[finrank_eq_card_basis C, ← finrank_eq_card_basis B, finrank_eq_card_basis b]`. Conclude with `⟨basisOfTopLeSpanOfCardEqFinrank _ hspan hcard, fun i => by simp⟩`.
-/
theorem carries_of_basis {L L' V V' : Type} [Field L] [Field L'] [AddCommGroup V] [Module L V] [AddCommGroup V']
    [Module L' V'] {σ : L →+* L'} (e : V →ₛₗ[σ] V') {n : ℕ} (B : Basis (Fin n) L V) (C : Basis (Fin n) L' V')
    (h : ∀ k, e (B k) = C k) {ι : Type} (b : Basis ι L V) : ∃ c : Basis ι L' V', ∀ i, c i = e (b i) := by
  classical
  have : Module.Finite L V := Module.Finite.of_basis B
  have : Module.Finite L' V' := Module.Finite.of_basis C
  have : Finite ι := Module.Finite.finite_basis b
  haveI : Fintype ι := Fintype.ofFinite ι
  have hspan : ⊤ ≤ Submodule.span L' (Set.range fun i => e (b i)) := by
    rw [← C.span_eq, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    rw [← h k, ← b.sum_repr (B k), map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hcard : Fintype.card ι = finrank L' V' := by
    rw [finrank_eq_card_basis C, ← finrank_eq_card_basis B, finrank_eq_card_basis b]
  exact ⟨basisOfTopLeSpanOfCardEqFinrank _ hspan hcard, fun i => by simp⟩

/- English proof (translation)
Introduce `Ks LL WL _ _ _ _ _ _ _ WK hForm O K K'' _ _ _ _ _ _ _ _ _ _ emb hemb Fm _ _ _ _ eF`. Take `⟨n, bv, -, hKs, hspanK, hLL, hspanL⟩` from `hForm`. Set `B : Basis (Fin n) LL WL` to `Basis.mk hLL hspanL.ge`. Establish `hB : ∀ k, B k = bv k` using `fun k => Basis.mk_apply _ _ _`. Set `BK : Basis (Fin n) Ks WK` to `(Basis.span hKs).map (LinearEquiv.ofEq _ _ hspanK)`.

Establish `hBK : ∀ k, (BK k : WL) = bv k` using `fun k => by simp [BK, Basis.span_apply]`. Set `bF : Basis (Fin n) K Fm` to `(Algebra.TensorProduct.basis K BK).map eF.symm`. Take `⟨c, hc⟩` from `exists_basis_tensor (O := O) (K'' := K'') bF`. Establish `hck : ∀ k, c k = (1 : K'') ⊗ₜ[O] eF.symm ((1 : K) ⊗ₜ[Ks] BK k)` using `fun k => by`. Rewrite using `[hc, Basis.map_apply, Algebra.TensorProduct.basis_apply]`.

Establish `hscal : ∀ (a : Ks) (m : Fm), emb (algebraMap Ks LL a) ⊗ₜ[O] m = (1 : K'') ⊗ₜ[O] (algebraMap Ks K a • m)`. Introduce `a m`. Rewrite using `[← RingHom.comp_apply emb (algebraMap Ks LL) a, hemb, RingHom.comp_apply, algebraMap_tmul]`. Establish `hf : ∀ e : WL →ₛₗ[emb] K'' ⊗[O] Fm, (∀ k, e (bv k) = (1 : K'') ⊗ₜ[O] eF.symm ((1 : K) ⊗ₜ[Ks] BK k)) → ∀ f : WK, e f = (1 : K'') ⊗ₜ[O] eF.symm ((1 : K) ⊗ₜ[Ks] f)`. Introduce `e he f`.

Establish `hterm : ∀ (r : Ks) (j : Fin n), e (r • bv j) = (1 : K'') ⊗ₜ[O] eF.symm ((1 : K) ⊗ₜ[Ks] (r • BK j))`. Introduce `r j`. Rewrite using `[← algebraMap_smul LL r (bv j), map_smulₛₗ, he, TensorProduct.smul_tmul', smul_eq_mul, mul_one, hscal, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]`. Establish `hsum : (f : WL) = ∑ j, BK.repr f j • bv j` using `by conv_lhs => rw [← BK.sum_repr f]`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, hBK]`.

Rewrite using `[hsum, map_sum]`. Repeatedly rewrite using `[hterm]`. Rewrite using `[← TensorProduct.tmul_sum, ← map_sum eF.symm, ← TensorProduct.tmul_sum, BK.sum_repr]`. Establish `hext : ∀ e : WL →ₛₗ[emb] K'' ⊗[O] Fm, (∀ k, e (bv k) = (1 : K'') ⊗ₜ[O] eF.symm ((1 : K) ⊗ₜ[Ks] BK k)) → IsExt O emb eF e`. Introduce `e he ι _ a f`.

Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smulₛₗ, hf e he, TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Establish `hval : ∀ e : WL →ₛₗ[emb] K'' ⊗[O] Fm, IsExt O emb eF e → ∀ k, e (bv k) = (1 : K'') ⊗ₜ[O] eF.symm ((1 : K) ⊗ₜ[Ks] BK k)`. Introduce `e he k`.

Rewrite using `[← hBK]`. Conclude with `he.apply_coe (BK k)`. Set `e₀ : WL →ₛₗ[emb] K'' ⊗[O] Fm` to `extOfBasis emb B fun k => (1 : K'') ⊗ₜ[O] eF.symm ((1 : K) ⊗ₜ[Ks] BK k)`. Establish `he₀ : ∀ k, e₀ (bv k) = (1 : K'') ⊗ₜ[O] eF.symm ((1 : K) ⊗ₜ[Ks] BK k)` using `fun k => by`. Rewrite using `[← hB]`.

Conclude with `extOfBasis_basis emb B _ k`. Use `⟨⟨e₀, hext e₀ he₀, fun e' he' => B.ext fun k => ?_⟩, fun e he => ?_, fun a m => ?_⟩` and prove the remaining obligations. Rewrite using `[hB, hval e' he' k, he₀ k]`. Conclude with `fun ι b => carries_of_basis e B c (fun k => by rw [hB, hval e he k, hck k]) b`. Conclude with `hscal a m`.
-/
theorem semilinearExtension : SemilinearExtension := by
  intro Ks LL WL _ _ _ _ _ _ _ WK hForm O K K'' _ _ _ _ _ _ _ _ _ _ emb hemb Fm _ _ _ _ eF
  obtain ⟨n, bv, -, hKs, hspanK, hLL, hspanL⟩ := hForm
  let B : Basis (Fin n) LL WL := Basis.mk hLL hspanL.ge
  have hB : ∀ k, B k = bv k := fun k => Basis.mk_apply _ _ _
  let BK : Basis (Fin n) Ks WK := (Basis.span hKs).map (LinearEquiv.ofEq _ _ hspanK)
  have hBK : ∀ k, (BK k : WL) = bv k := fun k => by simp [BK, Basis.span_apply]
  let bF : Basis (Fin n) K Fm := (Algebra.TensorProduct.basis K BK).map eF.symm
  obtain ⟨c, hc⟩ := exists_basis_tensor (O := O) (K'' := K'') bF
  have hck : ∀ k, c k = (1 : K'') ⊗ₜ[O] eF.symm ((1 : K) ⊗ₜ[Ks] BK k) := fun k => by
    rw [hc, Basis.map_apply, Algebra.TensorProduct.basis_apply]
  have hscal : ∀ (a : Ks) (m : Fm),
      emb (algebraMap Ks LL a) ⊗ₜ[O] m = (1 : K'') ⊗ₜ[O] (algebraMap Ks K a • m) := by
    intro a m
    rw [← RingHom.comp_apply emb (algebraMap Ks LL) a, hemb, RingHom.comp_apply, algebraMap_tmul]
  have hf : ∀ e : WL →ₛₗ[emb] K'' ⊗[O] Fm,
      (∀ k, e (bv k) = (1 : K'') ⊗ₜ[O] eF.symm ((1 : K) ⊗ₜ[Ks] BK k)) →
      ∀ f : WK, e f = (1 : K'') ⊗ₜ[O] eF.symm ((1 : K) ⊗ₜ[Ks] f) := by
    intro e he f
    have hterm : ∀ (r : Ks) (j : Fin n),
        e (r • bv j) = (1 : K'') ⊗ₜ[O] eF.symm ((1 : K) ⊗ₜ[Ks] (r • BK j)) := by
      intro r j
      rw [← algebraMap_smul LL r (bv j), map_smulₛₗ, he, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
        hscal, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one, Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul]
    have hsum : (f : WL) = ∑ j, BK.repr f j • bv j := by
      conv_lhs => rw [← BK.sum_repr f]
      simp only [Submodule.coe_sum, Submodule.coe_smul, hBK]
    rw [hsum, map_sum]
    simp_rw [hterm]
    rw [← TensorProduct.tmul_sum, ← map_sum eF.symm, ← TensorProduct.tmul_sum, BK.sum_repr]
  have hext : ∀ e : WL →ₛₗ[emb] K'' ⊗[O] Fm,
      (∀ k, e (bv k) = (1 : K'') ⊗ₜ[O] eF.symm ((1 : K) ⊗ₜ[Ks] BK k)) → IsExt O emb eF e := by
    intro e he ι _ a f
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smulₛₗ, hf e he, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hval : ∀ e : WL →ₛₗ[emb] K'' ⊗[O] Fm, IsExt O emb eF e →
      ∀ k, e (bv k) = (1 : K'') ⊗ₜ[O] eF.symm ((1 : K) ⊗ₜ[Ks] BK k) := by
    intro e he k
    rw [← hBK]
    exact he.apply_coe (BK k)
  let e₀ : WL →ₛₗ[emb] K'' ⊗[O] Fm :=
    extOfBasis emb B fun k => (1 : K'') ⊗ₜ[O] eF.symm ((1 : K) ⊗ₜ[Ks] BK k)
  have he₀ : ∀ k, e₀ (bv k) = (1 : K'') ⊗ₜ[O] eF.symm ((1 : K) ⊗ₜ[Ks] BK k) := fun k => by
    rw [← hB]
    exact extOfBasis_basis emb B _ k
  refine ⟨⟨e₀, hext e₀ he₀, fun e' he' => B.ext fun k => ?_⟩, fun e he => ?_, fun a m => ?_⟩
  · rw [hB, hval e' he' k, he₀ k]
  · exact fun ι b => carries_of_basis e B c (fun k => by rw [hB, hval e he k, hck k]) b
  · exact hscal a m

end GlobalTheory.SemilinearExt
