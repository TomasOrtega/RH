import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent

noncomputable section

open Matrix Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct

namespace GlobalTheory.RegSS.IdemTorus

section Lin

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {ι : Type} [Fintype ι]
  [DecidableEq ι]

def idemLin (p : ι → Matrix n n A) (c : ι → A) : Matrix n n A := 1 + ∑ k, (c k - 1) • p k

/- English proof (translation)
Unfold `idemLin`. Rewrite using `[add_mul, one_mul, Finset.sum_mul, Finset.sum_eq_single k]`. Rewrite using `[smul_mul_assoc, hi, sub_smul, one_smul]`. Normalize the expressions using the abelian group laws. Introduce `l _ hl`.

Rewrite using `[smul_mul_assoc, ho l k hl, smul_zero]`. Simplify using the standard rewrite rules.
-/
theorem idemLin_mul_idem {p : ι → Matrix n n A} (hi : ∀ k, p k * p k = p k)
    (ho : ∀ k l, k ≠ l → p k * p l = 0) (c : ι → A) (k : ι) :
    idemLin p c * p k = c k • p k := by
  unfold idemLin
  rw [add_mul, one_mul, Finset.sum_mul, Finset.sum_eq_single k]
  · rw [smul_mul_assoc, hi, sub_smul, one_smul]; abel
  · intro l _ hl; rw [smul_mul_assoc, ho l k hl, smul_zero]
  · simp

/- English proof (translation)
Establish `h : idemLin p c * idemLin p c' = idemLin p c + ∑ k, (c' k - 1) • (idemLin p c * p k)` using `by conv_lhs => rw [show idemLin p c' = 1 + ∑ k, (c' k - 1) • p k from rfl]`. Rewrite using `[mul_add, mul_one, Finset.mul_sum]`. Repeatedly rewrite using `[mul_smul_comm]`. Rewrite using `[h]`. Repeatedly rewrite using `[idemLin_mul_idem hi ho, smul_smul]`.

Unfold `idemLin`. Rewrite using `[add_assoc, ← Finset.sum_add_distrib]`. Use `congr 1`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← add_smul]`.

Use `congr 1`. Simplify using `only [Pi.mul_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem idemLin_mul {p : ι → Matrix n n A} (hi : ∀ k, p k * p k = p k)
    (ho : ∀ k l, k ≠ l → p k * p l = 0) (c c' : ι → A) :
    idemLin p (c * c') = idemLin p c * idemLin p c' := by
  have h : idemLin p c * idemLin p c' = idemLin p c + ∑ k, (c' k - 1) • (idemLin p c * p k) := by
    conv_lhs => rw [show idemLin p c' = 1 + ∑ k, (c' k - 1) • p k from rfl]
    rw [mul_add, mul_one, Finset.mul_sum]
    simp_rw [mul_smul_comm]
  rw [h]
  simp_rw [idemLin_mul_idem hi ho, smul_smul]
  unfold idemLin
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← add_smul]; congr 1; simp only [Pi.mul_apply]; ring

/- English proof (translation)
Simplify using `[idemLin]`.
-/
theorem idemLin_one (p : ι → Matrix n n A) : idemLin p 1 = 1 := by
  simp [idemLin]

/- English proof (translation)
The claim follows from `(Commute.one_right x).add_right (Commute.sum_right _ _ _ fun k _ => (h k).smul_right _)`.
-/
theorem idemLin_commute (p : ι → Matrix n n A) (x : Matrix n n A) (h : ∀ k, Commute x (p k))
    (c : ι → A) : Commute x (idemLin p c) :=
  (Commute.one_right x).add_right (Commute.sum_right _ _ _ fun k _ => (h k).smul_right _)

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[idemLin, Matrix.sum_apply, Matrix.one_apply, map_sum, apply_ite]`.
-/
theorem idemLin_map {B : Type} [CommRing B] (g : A →+* B) (p : ι → Matrix n n A) (c : ι → A) :
    (idemLin p c).map g = idemLin (fun k => (p k).map g) (fun k => g (c k)) := by
  ext i j
  simp [idemLin, Matrix.sum_apply, Matrix.one_apply, map_sum, apply_ite]

/- English proof (translation)
Establish `: cT σ (∑ k, M k) = ∑ k, cT σ (M k)`. Use extensionality with `i j`. Simplify using `[cT, Matrix.sum_apply, map_sum]`. Simplify using `only [adj, this, Finset.mul_sum, Finset.sum_mul]`.
-/
theorem adj_sum (σ : A →+* A) (J : Matrix n n A) (M : ι → Matrix n n A) :
    adj σ J (∑ k, M k) = ∑ k, adj σ J (M k) := by
  have : cT σ (∑ k, M k) = ∑ k, cT σ (M k) := by
    ext i j; simp [cT, Matrix.sum_apply, map_sum]
  simp only [adj, this, Finset.mul_sum, Finset.sum_mul]

/- English proof (translation)
Unfold `idemLin`. Rewrite using `[adj_add, adj_one σ hJ, adj_sum]`. Repeatedly rewrite using `[adj_smul, map_sub, map_one]`.
-/
theorem adj_idemLin (σ : A →+* A) {J : Matrix n n A} (hJ : IsUnit J.det) (p : ι → Matrix n n A)
    (c : ι → A) : adj σ J (idemLin p c) = idemLin (fun k => adj σ J (p k)) (fun k => σ (c k)) := by
  unfold idemLin
  rw [adj_add, adj_one σ hJ, adj_sum]
  simp_rw [adj_smul, map_sub, map_one]

/- English proof (translation)
Unfold `idemLin`. Use `congr 1`. Use `Equiv.sum_comp (Equiv.sumComm (Fin s) (Fin s)) (fun k => (c k.swap - 1) • p k)` as an intermediate fact. Simplify `this` using `[Sum.swap_swap]`.
-/
theorem idemLin_swap {s : ℕ} (p : Fin s ⊕ Fin s → Matrix n n A) (c : Fin s ⊕ Fin s → A) :
    idemLin (fun k => p k.swap) c = idemLin p (fun k => c k.swap) := by
  unfold idemLin
  congr 1
  have := Equiv.sum_comp (Equiv.sumComm (Fin s) (Fin s)) (fun k => (c k.swap - 1) • p k)
  simpa [Sum.swap_swap] using this

end Lin

end GlobalTheory.RegSS.IdemTorus

namespace GlobalTheory.RegSS.IdemTorus

section Torus

variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {n : Type} [Fintype n] [DecidableEq n]

def idemFam (σ : E →ₐ[F] E) (J : Matrix n n E) {s : ℕ} (ε : Fin s → Matrix n n E) :
    Fin s ⊕ Fin s → Matrix n n E :=
  Sum.elim ε (fun i => adj (σ : E →+* E) J (ε i))

def idemCoef (R : Type) [CommRing R] [Algebra F R] {s : ℕ} (t : Fin s → Rˣ) :
    Fin s ⊕ Fin s → E ⊗[F] R :=
  Sum.elim (fun i => (1 : E) ⊗ₜ[F] (t i : R)) (fun i => (1 : E) ⊗ₜ[F] (((t i)⁻¹ : Rˣ) : R))

/- English proof (translation)
Apply the tactic sequence `funext k; cases k <;> simp [idemCoef, Algebra.TensorProduct.one_def]`.
-/
theorem idemCoef_one (R : Type) [CommRing R] [Algebra F R] {s : ℕ} :
    idemCoef (F := F) (E := E) R (1 : Fin s → Rˣ) = 1 := by
  funext k; cases k <;> simp [idemCoef, Algebra.TensorProduct.one_def]

/- English proof (translation)
Apply the tactic sequence `funext k; cases k <;> simp [idemCoef, Algebra.TensorProduct.tmul_mul_tmul, mul_comm]`.
-/
theorem idemCoef_mul (R : Type) [CommRing R] [Algebra F R] {s : ℕ} (a b : Fin s → Rˣ) :
    idemCoef (F := F) (E := E) R (a * b) = idemCoef R a * idemCoef R b := by
  funext k; cases k <;> simp [idemCoef, Algebra.TensorProduct.tmul_mul_tmul, mul_comm]

/- English proof (translation)
Apply the tactic sequence `funext k; cases k <;> simp [idemCoef]`.
-/
theorem idemCoef_swap (R : Type) [CommRing R] [Algebra F R] {s : ℕ} (t : Fin s → Rˣ) :
    (fun k => idemCoef (F := F) (E := E) R t k.swap) = idemCoef R t⁻¹ := by
  funext k; cases k <;> simp [idemCoef]

/- English proof (translation)
Apply the tactic sequence `cases k <;> simp [idemCoef, sigR]`.
-/
theorem sigR_idemCoef (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] {s : ℕ}
    (t : Fin s → Rˣ) (k : Fin s ⊕ Fin s) : sigR σ R (idemCoef R t k) = idemCoef R t k := by
  cases k <;> simp [idemCoef, sigR]

/- English proof (translation)
Take `⟨φ, hφ⟩` from `Module.Projective.exists_dual_eq_one F he`. Introduce `x y h`. Use `congrArg (fun z => TensorProduct.lid F R (LinearMap.rTensor R φ z)) h` as an intermediate fact. Simplify `this` using `[hφ]`.
-/
theorem tmul_right_injective {e : E} (he : e ≠ 0) (R : Type) [CommRing R] [Algebra F R] :
    Function.Injective (fun x : R => e ⊗ₜ[F] x) := by
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one F he
  intro x y h
  have := congrArg (fun z => TensorProduct.lid F R (LinearMap.rTensor R φ z)) h
  simpa [hφ] using this

end Torus

end GlobalTheory.RegSS.IdemTorus

namespace GlobalTheory.RegSS.IdemTorus

section Main

variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {n : Type} [Fintype n] [DecidableEq n]

/- English proof (translation)
Take `⟨hmem, -, hid, hor, had⟩` from `h`. Establish `hcomm : ∀ a b : Matrix n n E, a ∈ genAlg (γ : Matrix n n E) → b ∈ genAlg (γ : Matrix n n E) → a * b = b * a` using `fun a b ha hb => congrArg Subtype.val (mul_comm (⟨a, ha⟩ : genAlg (γ : Matrix n n E)) ⟨b, hb⟩)`. Establish `hmem' : ∀ k, idemFam σ J ε k ∈ genAlg (γ : Matrix n n E)`. Introduce `k`. Consider the cases of `k with`.

Consider the case `inl i => exact hmem i`. Consider the case `inr i => exact hA.2.2.2.2.1 _ (hmem i)`. Use `⟨?_, ?_, ?_, fun k => commute_of_mem_genAlg rfl (hmem' k)⟩` and prove the remaining obligations. Introduce `k`. Consider the cases of `k with`.

Consider the case `inl i => exact hid i`. Consider the case `inr i`. Simplify using `only [idemFam, Sum.elim_inr]`. Rewrite using `[← adj_mul _ hR.nondeg, hid]`. Introduce `k l hkl`.

Consider the cases of `k with`. Consider the case `inl i`. Consider the cases of `l with`. Consider the case `inl j => exact hor i j (fun e => hkl (congrArg _ e))`. Consider the case `inr j => exact had i j`.

Consider the case `inr i`. Consider the cases of `l with`. Consider the case `inl j`. Simplify using `only [idemFam, Sum.elim_inl, Sum.elim_inr]`. Rewrite using `[hcomm _ (ε j) (hA.2.2.2.2.1 _ (hmem i)) (hmem j), had]`.

Consider the case `inr j`. Simplify using `only [idemFam, Sum.elim_inr]`. Rewrite using `[← adj_mul _ hR.nondeg, hor j i (fun e => hkl (congrArg _ e.symm)), adj_zero]`. Introduce `k`. Consider the cases of `k with`.

Consider the case `inl i => rfl`. Consider the case `inr i => exact adj_adj _ hR.quad.invol hR.herm hR.nondeg _`.
-/
theorem idemFam_facts {σ : E →ₐ[F] E} {J : Matrix n n E} {γ : GL n E} (hR : IsRegular σ J γ)
    (hA : ClauseAlg σ J γ) {s : ℕ} {ε : Fin s → Matrix n n E} (h : IsIdemFamily σ J γ ε) :
    (∀ k, idemFam σ J ε k * idemFam σ J ε k = idemFam σ J ε k) ∧
    (∀ k l, k ≠ l → idemFam σ J ε k * idemFam σ J ε l = 0) ∧
    (∀ k, adj (σ : E →+* E) J (idemFam σ J ε k) = idemFam σ J ε k.swap) ∧
    ∀ k, (γ : Matrix n n E) * idemFam σ J ε k = idemFam σ J ε k * (γ : Matrix n n E) := by
  obtain ⟨hmem, -, hid, hor, had⟩ := h
  have hcomm : ∀ a b : Matrix n n E, a ∈ genAlg (γ : Matrix n n E) → b ∈ genAlg (γ : Matrix n n E) →
      a * b = b * a := fun a b ha hb =>
    congrArg Subtype.val (mul_comm (⟨a, ha⟩ : genAlg (γ : Matrix n n E)) ⟨b, hb⟩)
  have hmem' : ∀ k, idemFam σ J ε k ∈ genAlg (γ : Matrix n n E) := by
    intro k
    cases k with
    | inl i => exact hmem i
    | inr i => exact hA.2.2.2.2.1 _ (hmem i)
  refine ⟨?_, ?_, ?_, fun k => commute_of_mem_genAlg rfl (hmem' k)⟩
  · intro k
    cases k with
    | inl i => exact hid i
    | inr i =>
      simp only [idemFam, Sum.elim_inr]
      rw [← adj_mul _ hR.nondeg, hid]
  · intro k l hkl
    cases k with
    | inl i =>
      cases l with
      | inl j => exact hor i j (fun e => hkl (congrArg _ e))
      | inr j => exact had i j
    | inr i =>
      cases l with
      | inl j =>
        simp only [idemFam, Sum.elim_inl, Sum.elim_inr]
        rw [hcomm _ (ε j) (hA.2.2.2.2.1 _ (hmem i)) (hmem j), had]
      | inr j =>
        simp only [idemFam, Sum.elim_inr]
        rw [← adj_mul _ hR.nondeg, hor j i (fun e => hkl (congrArg _ e.symm)), adj_zero]
  · intro k
    cases k with
    | inl i => rfl
    | inr i => exact adj_adj _ hR.quad.invol hR.herm hR.nondeg _

def idemFamR (σ : E →ₐ[F] E) (J : Matrix n n E) {s : ℕ} (ε : Fin s → Matrix n n E) (R : Type)
    [CommRing R] [Algebra F R] : Fin s ⊕ Fin s → Matrix n n (E ⊗[F] R) :=
  fun k => (idemFam σ J ε k).map (inclE (F := F) R)

variable {σ : E →ₐ[F] E} {J : Matrix n n E} {s : ℕ} {ε : Fin s → Matrix n n E}

/- English proof (translation)
Simplify using `only [idemFamR]`. Rewrite using `[← Matrix.map_mul, hi]`.
-/
theorem idemFamR_idem (hi : ∀ k, idemFam σ J ε k * idemFam σ J ε k = idemFam σ J ε k)
    (R : Type) [CommRing R] [Algebra F R] (k : Fin s ⊕ Fin s) :
    idemFamR σ J ε R k * idemFamR σ J ε R k = idemFamR σ J ε R k := by
  simp only [idemFamR]; rw [← Matrix.map_mul, hi]

/- English proof (translation)
Simplify using `only [idemFamR]`. Rewrite using `[← Matrix.map_mul, ho k l hkl, Matrix.map_zero _ (map_zero _)]`.
-/
theorem idemFamR_orth (ho : ∀ k l, k ≠ l → idemFam σ J ε k * idemFam σ J ε l = 0)
    (R : Type) [CommRing R] [Algebra F R] (k l : Fin s ⊕ Fin s) (hkl : k ≠ l) :
    idemFamR σ J ε R k * idemFamR σ J ε R l = 0 := by
  simp only [idemFamR]; rw [← Matrix.map_mul, ho k l hkl, Matrix.map_zero _ (map_zero _)]

def idemHom (hi : ∀ k, idemFam σ J ε k * idemFam σ J ε k = idemFam σ J ε k)
    (ho : ∀ k l, k ≠ l → idemFam σ J ε k * idemFam σ J ε l = 0) (R : Type) [CommRing R]
    [Algebra F R] : (Fin s → Rˣ) →* Matrix n n (E ⊗[F] R) where
  toFun t := idemLin (idemFamR σ J ε R) (idemCoef R t)
  map_one' := by simp only [idemCoef_one]; exact idemLin_one _
  map_mul' a b := by
    simp only [idemCoef_mul]
    exact idemLin_mul (idemFamR_idem hi R) (idemFamR_orth ho R) _ _

end Main

/- English proof (translation)
Introduce `F E _ _ _ _ n _ _ σ J γ hR hA s ε h`. Take `⟨hi, ho, had, hγ⟩` from `idemFam_facts hR hA h`. Establish `hJ' : ∀ (R : Type) [CommRing R] [Algebra F R], IsUnit (J.map (inclE (F` using `F) R)).det := fun R _ _ => isUnit_det_map _ hR.nondeg`. Establish `hadR : ∀ (R : Type) [CommRing R] [Algebra F R] (k : Fin s ⊕ Fin s), adj (sigR σ R) (J.map (inclE (F` using `F) R)) (idemFamR σ J ε R k) = idemFamR σ J ε R k.swap := by`. Introduce `R _ _ k`.

Simplify using `only [idemFamR]`. Rewrite using `[adj_map (σ : E →+* E) (sigR σ R) (inclE R) (inclE_conj σ R) hR.nondeg, had]`. Establish `hadjHom : ∀ (R : Type) [CommRing R] [Algebra F R] (t : Fin s → Rˣ), adj (sigR σ R) (J.map (inclE (F` using `F) R)) (idemHom hi ho R t) = idemHom hi ho R t⁻¹ := by`. Introduce `R _ _ t`. Use `show adj _ _ (idemLin _ _) = idemLin _ _`.

Rewrite using `[adj_idemLin _ (hJ' R)]`. Establish `e1 : (fun k => adj (sigR σ R) (J.map (inclE (F` using `F) R)) (idemFamR σ J ε R k)) = fun k => idemFamR σ J ε R k.swap := funext (hadR R)`. Establish `e2 : (fun k => sigR σ R (idemCoef R t k)) = idemCoef R t` using `funext (sigR_idemCoef σ R t)`. Rewrite using `[e1, e2, idemLin_swap, idemCoef_swap]`. Use `⟨⟨(fun R _ _ => (idemHom hi ho R).toHomUnits), ?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Introduce `R _ _ t`. Use `Subgroup.mem_inf.2 ⟨?_, ?_⟩` and prove the remaining obligations. Use `(mem_UJ_iff_mul_adj (sigR σ R) (hJ' R) _).2 ?_` and prove the remaining obligations. Rewrite using `[MonoidHom.coe_toHomUnits, hadjHom, ← map_mul, mul_inv_cancel, map_one]`. Use `Subgroup.mem_centralizer_singleton_iff.2 (Units.ext ?_) show idemHom hi ho R t * (γ : Matrix n n E).map (inclE (F := F) R) = (γ : Matrix n n E).map (inclE (F := F) R) * idemHom hi ho R t` and prove the remaining obligations.

Use `(idemLin_commute _ _ (fun k => ?_) _).eq.symm` and prove the remaining obligations. Use `show (γ : Matrix n n E).map (inclE (F := F) R) * (idemFam σ J ε k).map (inclE (F := F) R) = (idemFam σ J ε k).map (inclE (F := F) R) * (γ : Matrix n n E).map (inclE (F := F) R)`. Rewrite using `[← Matrix.map_mul, ← Matrix.map_mul, hγ]`. Introduce `R _ _ a b hab`. Use function extensionality and compare the values at `i`.

Apply `Units.ext` to reduce the goal to its premises. Establish `h1` using `congrArg (fun g : GL n (E ⊗[F] R) => (g : Matrix n n (E ⊗[F] R)) * idemFamR σ J ε R (.inl i)) hab`. Express the relevant statement in the definitionally equal form `idemLin _ (idemCoef R a) * _ = idemLin _ (idemCoef R b) * _ at h1`. Rewrite `h1` using `[idemLin_mul_idem (idemFamR_idem hi R) (idemFamR_orth ho R), idemLin_mul_idem (idemFamR_idem hi R) (idemFamR_orth ho R)]`. Choose the witnesses or unpack the hypotheses as in `⟨k, l, hkl⟩ : ∃ k l, ε i k l ≠ 0 := by`.

Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `h.2.1 i (Matrix.ext hc)`. Establish `h2` using `congrFun (congrFun h1 k) l`. Simplify using `[idemFamR, idemFam, idemCoef, inclE, Algebra.TensorProduct.tmul_mul_tmul] at h2`.

Conclude with `tmul_right_injective hkl R h2`. Introduce `R S _ _ _ _ f t`. Use `Units.ext ?_` and prove the remaining obligations. Use `show idemLin (idemFamR σ J ε S) (idemCoef S _) = (idemLin (idemFamR σ J ε R) (idemCoef R t)).map (Algebra.TensorProduct.map (AlgHom.id F E) f).toRingHom`. Rewrite using `[idemLin_map]`.

Use `congr 1`. Use function extensionality and compare the values at `k`. Simplify using `only [idemFamR, Matrix.map_map]`. Use `congr 1`. Use function extensionality and compare the values at `x`.

Simplify using `[inclE]`. Use function extensionality and compare the values at `k`. Apply the tactic sequence `cases k <;> simp [idemCoef]`. Introduce `R _ _ t i`. Conclude with `idemLin_mul_idem (idemFamR_idem hi R) (idemFamR_orth ho R) _ (.inl i)`.
-/
theorem subtorusOfIdempotents : SubtorusOfIdempotents := by
  intro F E _ _ _ _ n _ _ σ J γ hR hA s ε h
  obtain ⟨hi, ho, had, hγ⟩ := idemFam_facts hR hA h
  have hJ' : ∀ (R : Type) [CommRing R] [Algebra F R], IsUnit (J.map (inclE (F := F) R)).det :=
    fun R _ _ => isUnit_det_map _ hR.nondeg
  have hadR : ∀ (R : Type) [CommRing R] [Algebra F R] (k : Fin s ⊕ Fin s),
      adj (sigR σ R) (J.map (inclE (F := F) R)) (idemFamR σ J ε R k) = idemFamR σ J ε R k.swap := by
    intro R _ _ k
    simp only [idemFamR]
    rw [adj_map (σ : E →+* E) (sigR σ R) (inclE R) (inclE_conj σ R) hR.nondeg, had]
  have hadjHom : ∀ (R : Type) [CommRing R] [Algebra F R] (t : Fin s → Rˣ),
      adj (sigR σ R) (J.map (inclE (F := F) R)) (idemHom hi ho R t) = idemHom hi ho R t⁻¹ := by
    intro R _ _ t
    show adj _ _ (idemLin _ _) = idemLin _ _
    rw [adj_idemLin _ (hJ' R)]
    have e1 : (fun k => adj (sigR σ R) (J.map (inclE (F := F) R)) (idemFamR σ J ε R k)) =
        fun k => idemFamR σ J ε R k.swap := funext (hadR R)
    have e2 : (fun k => sigR σ R (idemCoef R t k)) = idemCoef R t := funext (sigR_idemCoef σ R t)
    rw [e1, e2, idemLin_swap, idemCoef_swap]
  refine ⟨⟨(fun R _ _ => (idemHom hi ho R).toHomUnits), ?_, ?_, ?_⟩, ?_⟩
  · intro R _ _ t
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · refine (mem_UJ_iff_mul_adj (sigR σ R) (hJ' R) _).2 ?_
      rw [MonoidHom.coe_toHomUnits, hadjHom, ← map_mul, mul_inv_cancel, map_one]
    · refine Subgroup.mem_centralizer_singleton_iff.2 (Units.ext ?_)
      show idemHom hi ho R t * (γ : Matrix n n E).map (inclE (F := F) R) =
        (γ : Matrix n n E).map (inclE (F := F) R) * idemHom hi ho R t
      refine (idemLin_commute _ _ (fun k => ?_) _).eq.symm
      show (γ : Matrix n n E).map (inclE (F := F) R) * (idemFam σ J ε k).map (inclE (F := F) R) =
        (idemFam σ J ε k).map (inclE (F := F) R) * (γ : Matrix n n E).map (inclE (F := F) R)
      rw [← Matrix.map_mul, ← Matrix.map_mul, hγ]
  · intro R _ _ a b hab
    funext i
    apply Units.ext
    have h1 := congrArg (fun g : GL n (E ⊗[F] R) =>
      (g : Matrix n n (E ⊗[F] R)) * idemFamR σ J ε R (.inl i)) hab
    change idemLin _ (idemCoef R a) * _ = idemLin _ (idemCoef R b) * _ at h1
    rw [idemLin_mul_idem (idemFamR_idem hi R) (idemFamR_orth ho R),
      idemLin_mul_idem (idemFamR_idem hi R) (idemFamR_orth ho R)] at h1
    obtain ⟨k, l, hkl⟩ : ∃ k l, ε i k l ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact h.2.1 i (Matrix.ext hc)
    have h2 := congrFun (congrFun h1 k) l
    simp [idemFamR, idemFam, idemCoef, inclE, Algebra.TensorProduct.tmul_mul_tmul] at h2
    exact tmul_right_injective hkl R h2
  · intro R S _ _ _ _ f t
    refine Units.ext ?_
    show idemLin (idemFamR σ J ε S) (idemCoef S _) =
      (idemLin (idemFamR σ J ε R) (idemCoef R t)).map
        (Algebra.TensorProduct.map (AlgHom.id F E) f).toRingHom
    rw [idemLin_map]
    congr 1
    · funext k
      simp only [idemFamR, Matrix.map_map]
      congr 1
      funext x
      simp [inclE]
    · funext k
      cases k <;> simp [idemCoef]
  · intro R _ _ t i
    exact idemLin_mul_idem (idemFamR_idem hi R) (idemFamR_orth ho R) _ (.inl i)

end GlobalTheory.RegSS.IdemTorus
