import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsMuModelChartUnit
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree

open GroundTheory.Heights₂.Heights.LowerBoundFree Submodule Module

namespace WedgeTransition

/- English proof (translation)
Set `T : (Fin n → R) →ₗ[R] M` to `(Pi.basisFun R (Fin n)).constr R v`. Establish `h` using `congrArg (fun g => g (fun q a => A a q)) (AlternatingMap.eq_smul_basis_det (Pi.basisFun R (Fin n)) (f.compLinearMap T))`. Establish `hT : ∀ x, T x = ∑ a, x a • v a` using `fun x => by`. Simplify using `[T, Basis.constr_apply_fintype]`. Establish `hTe : (fun i => T (Pi.basisFun R (Fin n) i)) = v` using `funext fun i => by simp [T]`.

Simplify using `only [AlternatingMap.compLinearMap_apply, AlternatingMap.smul_apply, Pi.basisFun_det_apply, smul_eq_mul] at h`. Establish `e1 : (fun i => T fun a => A a i) = fun q => ∑ a, A a q • v a` using `funext fun q => hT _`. Rewrite `h` using `[e1, hTe]`. Rewrite using `[h, mul_comm]`. Use `congr 1`.

Conclude with `Matrix.det_transpose A`.
-/
theorem alternating_sum_smul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
    (f : M [⋀^Fin n]→ₗ[R] R) (v : Fin n → M) (A : Matrix (Fin n) (Fin n) R) :
    f (fun q => ∑ a, A a q • v a) = A.det * f v := by
  let T : (Fin n → R) →ₗ[R] M := (Pi.basisFun R (Fin n)).constr R v
  have h := congrArg (fun g => g (fun q a => A a q))
    (AlternatingMap.eq_smul_basis_det (Pi.basisFun R (Fin n)) (f.compLinearMap T))
  have hT : ∀ x, T x = ∑ a, x a • v a := fun x => by
    simp [T, Basis.constr_apply_fintype]
  have hTe : (fun i => T (Pi.basisFun R (Fin n) i)) = v := funext fun i => by simp [T]
  simp only [AlternatingMap.compLinearMap_apply, AlternatingMap.smul_apply, Pi.basisFun_det_apply,
    smul_eq_mul] at h
  have e1 : (fun i => T fun a => A a i) = fun q => ∑ a, A a q • v a := funext fun q => hT _
  rw [e1, hTe] at h
  rw [h, mul_comm]
  congr 1
  exact Matrix.det_transpose A

/- English proof (translation)
Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact. Simplify using `[tailIdx] at this`. Use linear arithmetic over natural numbers and integers.
-/
theorem castLE_ne_tailIdx {j N : ℕ} (hj : j ≤ N) (a : Fin j) (a' : Fin (N - j)) :
    Fin.castLE hj a ≠ tailIdx hj a' := by
  intro h
  have := congrArg Fin.val h
  simp [tailIdx] at this
  omega

def splitEquiv {j N : ℕ} (hj : j ≤ N) : Fin j ⊕ Fin (N - j) ≃ Fin N :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_cancel' hj))

/- English proof (translation)
The claim follows from `Fin.ext (by simp [splitEquiv])`.
-/
theorem splitEquiv_inl {j N : ℕ} (hj : j ≤ N) (a : Fin j) : splitEquiv hj (Sum.inl a) = Fin.castLE hj a :=
  Fin.ext (by simp [splitEquiv])

/- English proof (translation)
The claim follows from `Fin.ext (by simp [splitEquiv, tailIdx])`.
-/
theorem splitEquiv_inr {j N : ℕ} (hj : j ≤ N) (a : Fin (N - j)) : splitEquiv hj (Sum.inr a) = tailIdx hj a :=
  Fin.ext (by simp [splitEquiv, tailIdx])

/- English proof (translation)
Rewrite using `[← (splitEquiv hj).sum_comp, Fintype.sum_sum_type]`. Simplify using `[splitEquiv_inl, splitEquiv_inr]`.
-/
theorem sum_split {M : Type*} [AddCommMonoid M] {j N : ℕ} (hj : j ≤ N) (g : Fin N → M) :
    ∑ p, g p = ∑ a, g (Fin.castLE hj a) + ∑ a, g (tailIdx hj a) := by
  rw [← (splitEquiv hj).sum_comp, Fintype.sum_sum_type]
  simp [splitEquiv_inl, splitEquiv_inr]

/- English proof (translation)
Rewrite using `[← Matrix.det_submatrix_equiv_self (splitEquiv hj) G, ← Matrix.fromBlocks_toBlocks (G.submatrix (splitEquiv hj) (splitEquiv hj))]`. Establish `h21 : (G.submatrix (splitEquiv hj) (splitEquiv hj)).toBlocks₂₁ = 0`. Use extensionality with `a a'`. Simplify using `[Matrix.toBlocks₂₁, splitEquiv_inl, splitEquiv_inr, h0]`. Rewrite using `[h21, Matrix.det_fromBlocks_zero₂₁]`.

Use `congr 2`.
-/
theorem det_split_of_zero {R : Type*} [CommRing R] {j N : ℕ} (hj : j ≤ N) (G : Matrix (Fin N) (Fin N) R)
    (h0 : ∀ a a', G (tailIdx hj a) (Fin.castLE hj a') = 0) :
    G.det = (G.submatrix (Fin.castLE hj) (Fin.castLE hj)).det *
      (G.submatrix (tailIdx hj) (tailIdx hj)).det := by
  rw [← Matrix.det_submatrix_equiv_self (splitEquiv hj) G,
    ← Matrix.fromBlocks_toBlocks (G.submatrix (splitEquiv hj) (splitEquiv hj))]
  have h21 : (G.submatrix (splitEquiv hj) (splitEquiv hj)).toBlocks₂₁ = 0 := by
    ext a a'
    simp [Matrix.toBlocks₂₁, splitEquiv_inl, splitEquiv_inr, h0]
  rw [h21, Matrix.det_fromBlocks_zero₂₁]
  congr 2

variable {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] (F : Submodule Ω V) {N j : ℕ} (hj : j ≤ N)

/- English proof (translation)
Set `B` to `Basis.mk hli hsp.ge`. Establish `: Module.Finite Ω V` using `Module.Finite.of_basis B`. Establish `hV : Module.finrank Ω V = N` using `by simpa using Module.finrank_eq_card_basis B`. Establish `hFr : Module.finrank Ω F = j`. Rewrite using `[← hF, finrank_span_eq_card (hli.comp _ (Fin.castLE_injective hj))]`.

Simplify using the standard rewrite rules. Establish `hQ` using `Submodule.finrank_quotient_add_finrank F`. Set `w : Fin (N - j) → V ⧸ F` to `fun a => F.mkQ (b' (tailIdx hj a))`. Establish `hspan : ⊤ ≤ span Ω (Set.range w)`. Introduce `x _`.

Take `⟨v, rfl⟩` from `Submodule.Quotient.mk_surjective F x`. Establish `h1 : F.mkQ v ∈ span Ω (F.mkQ '' Set.range b')`. Rewrite using `[← Submodule.map_span, hsp]`. Conclude with `⟨v, trivial, rfl⟩`. Use `(Submodule.span_le.mpr ?_) h1` and prove the remaining obligations.

Introduce and unpack `_ ⟨_, ⟨i, rfl⟩, rfl⟩`. Distinguish the cases in `hi : i.val < j`. Establish `hmem : b' i ∈ F` using `hF ▸ subset_span ⟨⟨i, hi⟩, rfl⟩`. Establish `: F.mkQ (b' i) = 0` using `by simpa using hmem`. Rewrite using `[SetLike.mem_coe, this]`.

Conclude with `zero_mem _`. Establish `: i = tailIdx hj ⟨i - j, by omega⟩` using `Fin.ext (by simp [tailIdx]; omega)`. Rewrite using `[this]`. Conclude with `subset_span ⟨_, rfl⟩`. Establish `hli' : LinearIndependent Ω w` using `linearIndependent_of_top_le_span_of_card_eq_finrank hspan (by simp; omega)`.

Set `Q` to `Basis.mk hli' hspan`. Use `⟨exteriorPower.alternatingMapLinearEquiv Q.det, ?_⟩` and prove the remaining obligations. Rewrite using `[quotWedge, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]`. Establish `: (fun a => F.mkQ (b' (tailIdx hj a))) = ⇑Q` using `funext fun a => (Basis.mk_apply hli' hspan a).symm`. Rewrite using `[this, Basis.det_self]`.
-/
theorem exists_form_quotWedge_eq_one {b' : Fin N → V} (hli : LinearIndependent Ω b')
    (hsp : span Ω (Set.range b') = ⊤) (hF : span Ω (Set.range (b' ∘ Fin.castLE hj)) = F) :
    ∃ ℓ : ⋀[Ω]^(N - j) (V ⧸ F) →ₗ[Ω] Ω, ℓ (quotWedge F hj b') = 1 := by
  let B := Basis.mk hli hsp.ge
  have : Module.Finite Ω V := Module.Finite.of_basis B
  have hV : Module.finrank Ω V = N := by simpa using Module.finrank_eq_card_basis B
  have hFr : Module.finrank Ω F = j := by
    rw [← hF, finrank_span_eq_card (hli.comp _ (Fin.castLE_injective hj))]
    simp
  have hQ := Submodule.finrank_quotient_add_finrank F
  let w : Fin (N - j) → V ⧸ F := fun a => F.mkQ (b' (tailIdx hj a))
  have hspan : ⊤ ≤ span Ω (Set.range w) := by
    intro x _
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective F x
    have h1 : F.mkQ v ∈ span Ω (F.mkQ '' Set.range b') := by
      rw [← Submodule.map_span, hsp]
      exact ⟨v, trivial, rfl⟩
    refine (Submodule.span_le.mpr ?_) h1
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    by_cases hi : i.val < j
    · have hmem : b' i ∈ F := hF ▸ subset_span ⟨⟨i, hi⟩, rfl⟩
      have : F.mkQ (b' i) = 0 := by simpa using hmem
      rw [SetLike.mem_coe, this]
      exact zero_mem _
    · have : i = tailIdx hj ⟨i - j, by omega⟩ := Fin.ext (by simp [tailIdx]; omega)
      rw [this]
      exact subset_span ⟨_, rfl⟩
  have hli' : LinearIndependent Ω w :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspan (by simp; omega)
  let Q := Basis.mk hli' hspan
  refine ⟨exteriorPower.alternatingMapLinearEquiv Q.det, ?_⟩
  rw [quotWedge, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  have : (fun a => F.mkQ (b' (tailIdx hj a))) = ⇑Q := funext fun a => (Basis.mk_apply hli' hspan a).symm
  rw [this, Basis.det_self]

/- English proof (translation)
Set `B` to `Basis.mk hb'.1 hb'.2.1.ge`. Establish `hB : ∀ i, B i = b' i` using `fun i => Basis.mk_apply _ _ i`. Set `S` to `B.toMatrix b`. Establish `hexp : ∀ q, b q = ∑ p, S p q • b' p`. Introduce `q`.

Simplify using `only [S, Basis.toMatrix_apply, ← hB]`. Conclude with `(B.sum_repr (b q)).symm`. Establish `hzero : ∀ a a', S (tailIdx hj a) (Fin.castLE hj a') = 0`. Introduce `a a'`. Establish `hm : b (Fin.castLE hj a') ∈ span Ω (Set.range (b' ∘ Fin.castLE hj))` using `hb'.2.2 ▸ hb.2.2 ▸ subset_span ⟨a', rfl⟩`.

Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun Ω).mp hm`. Simplify using `only [S, Basis.toMatrix_apply, ← hc, Function.comp_apply, ← hB, map_sum, map_smul, Basis.repr_self, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, Finsupp.single_apply, castLE_ne_tailIdx, if_false, smul_zero, Finset.sum_const_zero]`. Establish `hF' : ∀ a, b' (Fin.castLE hj a) ∈ F` using `fun a => hb'.2.2 ▸ subset_span ⟨a, rfl⟩`. Establish `hφ : φ b = S.det * φ b'`. Rewrite using `[← alternating_sum_smul φ b' S]`.

Conclude with `congrArg φ (funext hexp)`. Establish `hψ : ψ (b ∘ Fin.castLE hj) = (S.submatrix (Fin.castLE hj) (Fin.castLE hj)).det * ψ (b' ∘ Fin.castLE hj)`. Rewrite using `[← alternating_sum_smul ψ (b' ∘ Fin.castLE hj)]`. Use `congrArg ψ (funext fun q => ?_)` and prove the remaining obligations. Rewrite using `[Function.comp_apply, hexp, sum_split hj]`.

Simplify using `[hzero]`. Establish `hq : ∀ ℓ' : ⋀[Ω]^(N - j) (V ⧸ F) →ₗ[Ω] Ω, ℓ' (quotWedge F hj b) = (S.submatrix (tailIdx hj) (tailIdx hj)).det * ℓ' (quotWedge F hj b')`. Introduce `ℓ'`. Use `alternating_sum_smul (ℓ'.compAlternatingMap (exteriorPower.ιMulti Ω (N - j))) (fun a => F.mkQ (b' (tailIdx hj a))) (S.submatrix (tailIdx hj) (tailIdx hj))` as an intermediate fact. Simplify using `only [LinearMap.compAlternatingMap_apply, Matrix.submatrix_apply] at this`.

Rewrite using `[quotWedge, quotWedge, ← this]`. Use `congr 2`. Use function extensionality and compare the values at `q`. Rewrite using `[hexp, map_sum, sum_split hj]`. Establish `h0 : ∀ a, F.mkQ (S (Fin.castLE hj a) (tailIdx hj q) • b' (Fin.castLE hj a)) = 0` using `fun a => by`.

Simplify using `using Or.inr (hF' a)`. Simplify using `only [h0, Finset.sum_const_zero, zero_add, map_smul]`. Establish `hdet` using `det_split_of_zero hj S hzero`. Rewrite using `[hφ, hψ, hq ℓ, hℓ, hdet]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem one_factor {b b' : Fin N → V}
    (hb : LinearIndependent Ω b ∧ span Ω (Set.range b) = ⊤ ∧ span Ω (Set.range (b ∘ Fin.castLE hj)) = F)
    (hb' : LinearIndependent Ω b' ∧ span Ω (Set.range b') = ⊤ ∧ span Ω (Set.range (b' ∘ Fin.castLE hj)) = F)
    (φ : V [⋀^Fin N]→ₗ[Ω] Ω) (ψ : V [⋀^Fin j]→ₗ[Ω] Ω) (ℓ : ⋀[Ω]^(N - j) (V ⧸ F) →ₗ[Ω] Ω)
    (hℓ : ℓ (quotWedge F hj b') = 1) :
    φ b * ψ (b' ∘ Fin.castLE hj) = φ b' * ψ (b ∘ Fin.castLE hj) * ℓ (quotWedge F hj b) := by
  let B := Basis.mk hb'.1 hb'.2.1.ge
  have hB : ∀ i, B i = b' i := fun i => Basis.mk_apply _ _ i
  let S := B.toMatrix b
  have hexp : ∀ q, b q = ∑ p, S p q • b' p := by
    intro q
    simp only [S, Basis.toMatrix_apply, ← hB]
    exact (B.sum_repr (b q)).symm
  have hzero : ∀ a a', S (tailIdx hj a) (Fin.castLE hj a') = 0 := by
    intro a a'
    have hm : b (Fin.castLE hj a') ∈ span Ω (Set.range (b' ∘ Fin.castLE hj)) :=
      hb'.2.2 ▸ hb.2.2 ▸ subset_span ⟨a', rfl⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun Ω).mp hm
    simp only [S, Basis.toMatrix_apply, ← hc, Function.comp_apply, ← hB, map_sum, map_smul,
      Basis.repr_self, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
      Finsupp.single_apply, castLE_ne_tailIdx, if_false, smul_zero, Finset.sum_const_zero]
  have hF' : ∀ a, b' (Fin.castLE hj a) ∈ F := fun a => hb'.2.2 ▸ subset_span ⟨a, rfl⟩
  have hφ : φ b = S.det * φ b' := by
    rw [← alternating_sum_smul φ b' S]
    exact congrArg φ (funext hexp)
  have hψ : ψ (b ∘ Fin.castLE hj) = (S.submatrix (Fin.castLE hj) (Fin.castLE hj)).det * ψ (b' ∘ Fin.castLE hj) := by
    rw [← alternating_sum_smul ψ (b' ∘ Fin.castLE hj)]
    refine congrArg ψ (funext fun q => ?_)
    rw [Function.comp_apply, hexp, sum_split hj]
    simp [hzero]
  have hq : ∀ ℓ' : ⋀[Ω]^(N - j) (V ⧸ F) →ₗ[Ω] Ω,
      ℓ' (quotWedge F hj b) = (S.submatrix (tailIdx hj) (tailIdx hj)).det * ℓ' (quotWedge F hj b') := by
    intro ℓ'
    have := alternating_sum_smul (ℓ'.compAlternatingMap (exteriorPower.ιMulti Ω (N - j)))
      (fun a => F.mkQ (b' (tailIdx hj a))) (S.submatrix (tailIdx hj) (tailIdx hj))
    simp only [LinearMap.compAlternatingMap_apply, Matrix.submatrix_apply] at this
    rw [quotWedge, quotWedge, ← this]
    congr 2
    funext q
    rw [hexp, map_sum, sum_split hj]
    have h0 : ∀ a, F.mkQ (S (Fin.castLE hj a) (tailIdx hj q) • b' (Fin.castLE hj a)) = 0 := fun a => by
      simpa using Or.inr (hF' a)
    simp only [h0, Finset.sum_const_zero, zero_add, map_smul]
  have hdet := det_split_of_zero hj S hzero
  rw [hφ, hψ, hq ℓ, hℓ, hdet]
  ring

end WedgeTransition

/- English proof (translation)
Introduce and unpack `Ψ _ Ω _ E _ _ F N j r s hj hr hs rfl rfl b b' hb hb' φ ψ κ κ' h`. Use `choose ℓ hℓ using fun τ => WedgeTransition.exists_form_quotWedge_eq_one (F τ) hj (hb' τ).1 (hb' τ).2.1 (hb' τ).2.2`. Establish `key` using `congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra Ω Ψ Ω).compLinearMap ℓ)) h`. Simplify using `only [map_smul, PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply, hℓ, Finset.prod_const_one, smul_eq_mul, mul_one] at key`. Establish `hτ : ∀ τ, φ τ (b τ ∘ Fin.castLE hs) * ψ τ (b' τ ∘ Fin.castLE hr) = φ τ (b' τ ∘ Fin.castLE hs) * ψ τ (b τ ∘ Fin.castLE hr) * ℓ τ (quotWedge (F τ) hj (b τ))` using `fun τ => WedgeTransition.one_factor (F τ) hj (hb τ) (hb' τ) (φ τ) (ψ τ) (ℓ τ) (hℓ τ)`.

Rewrite using `[Finset.prod_congr rfl fun τ _ => hτ τ, Finset.prod_mul_distrib, ← key]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem WedgeTransition.proof : WedgeTransition.Statement := by
  rintro Ψ _ Ω _ E _ _ F N j r s hj hr hs rfl rfl b b' hb hb' φ ψ κ κ' h
  classical
  choose ℓ hℓ using fun τ => WedgeTransition.exists_form_quotWedge_eq_one (F τ) hj (hb' τ).1 (hb' τ).2.1
    (hb' τ).2.2
  have key := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra Ω Ψ Ω).compLinearMap ℓ)) h
  simp only [map_smul, PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply, hℓ, Finset.prod_const_one, smul_eq_mul, mul_one] at key
  have hτ : ∀ τ, φ τ (b τ ∘ Fin.castLE hs) * ψ τ (b' τ ∘ Fin.castLE hr) =
      φ τ (b' τ ∘ Fin.castLE hs) * ψ τ (b τ ∘ Fin.castLE hr) * ℓ τ (quotWedge (F τ) hj (b τ)) :=
    fun τ => WedgeTransition.one_factor (F τ) hj (hb τ) (hb' τ) (φ τ) (ψ τ) (ℓ τ) (hℓ τ)
  rw [Finset.prod_congr rfl fun τ _ => hτ τ, Finset.prod_mul_distrib, ← key]
  ring

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree
