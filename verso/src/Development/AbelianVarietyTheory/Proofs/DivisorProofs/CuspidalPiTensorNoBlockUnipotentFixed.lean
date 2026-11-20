import Mathlib
import Formalism.PadicSubsetSums.CentralIdempotents.GaloisConjCentralIdempotent
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BlockEmbeddingFactors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviTensorBlockExt

noncomputable section

namespace GlobalTheory.HcIrr

open CategoryTheory Polynomial Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.DIV

section UnipGroup

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ}

/- English proof (translation)
Rewrite using `[Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single i]`. Rewrite using `[hg.2 i i rfl, if_pos rfl, one_mul, hh.2 i j hij]`. Introduce `k _ hki`. Break down `lt_trichotomy (b k) (b i) with hlt | heq | hgt` into its components or cases. Rewrite using `[hg.1.1 i k hlt, zero_mul]`.

Rewrite using `[hg.2 i k heq.symm, if_neg (Ne.symm hki), zero_mul]`. Rewrite using `[hh.1.1 k j (by rw [← hij]; exact hgt), mul_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ i) h`.
-/
theorem unip_diag_mul (b : ι → Fin s) {g h : GL ι K} (hg : g ∈ unip K b) (hh : h ∈ unip K b)
    (i j : ι) (hij : b i = b j) : ((g * h : GL ι K) : Matrix ι ι K) i j = if i = j then 1 else 0 := by
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [hg.2 i i rfl, if_pos rfl, one_mul, hh.2 i j hij]
  · intro k _ hki
    rcases lt_trichotomy (b k) (b i) with hlt | heq | hgt
    · rw [hg.1.1 i k hlt, zero_mul]
    · rw [hg.2 i k heq.symm, if_neg (Ne.symm hki), zero_mul]
    · rw [hh.1.1 k j (by rw [← hij]; exact hgt), mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

/- English proof (translation)
Establish `h1 : ((g⁻¹ * g : GL ι K) : Matrix ι ι K) i j = if i = j then 1 else 0`. Rewrite using `[inv_mul_cancel, Units.val_one, Matrix.one_apply]`. Rewrite `h1` using `[Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single j]`. Rewrite `h1` using `[hg.2 j j rfl, if_pos rfl, mul_one]`. Then use the resulting hypothesis. Introduce `k _ hkj`.

Break down `lt_trichotomy (b k) (b i) with hlt | heq | hgt` into its components or cases. Rewrite using `[hg.1.2 i k hlt, zero_mul]`. Rewrite using `[hg.2 k j (heq.trans hij), if_neg hkj, mul_zero]`. Rewrite using `[hg.1.1 k j (by rw [← hij]; exact hgt), mul_zero]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ j) h`.
-/
theorem unip_diag_inv (b : ι → Fin s) {g : GL ι K} (hg : g ∈ unip K b)
    (i j : ι) (hij : b i = b j) : ((g⁻¹ : GL ι K) : Matrix ι ι K) i j = if i = j then 1 else 0 := by
  have h1 : ((g⁻¹ * g : GL ι K) : Matrix ι ι K) i j = if i = j then 1 else 0 := by
    rw [inv_mul_cancel, Units.val_one, Matrix.one_apply]
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single j] at h1
  · rwa [hg.2 j j rfl, if_pos rfl, mul_one] at h1
  · intro k _ hkj
    rcases lt_trichotomy (b k) (b i) with hlt | heq | hgt
    · rw [hg.1.2 i k hlt, zero_mul]
    · rw [hg.2 k j (heq.trans hij), if_neg hkj, mul_zero]
    · rw [hg.1.1 k j (by rw [← hij]; exact hgt), mul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

def cuspUnipGroup (b : ι → Fin s) : Subgroup (GL ι K) where
  carrier := unip K b
  one_mem' := ⟨one_mem _, fun i j _ => by rw [Units.val_one, Matrix.one_apply]⟩
  mul_mem' hg hh := ⟨mul_mem hg.1 hh.1, unip_diag_mul b hg hh⟩
  inv_mem' hg := ⟨inv_mem hg.1, unip_diag_inv b hg⟩

end UnipGroup

/- English proof (translation)
Set `f : U → ((lam c : Type) →ₗ[ℂ] (lam c : Type))` to `fun u => (lam c).ρ u`. Establish `hinv : ∀ (g : U) (v : (lam c : Type)), f g (∑ u : U, f u v) = ∑ u : U, f u v`. Introduce `g v`. Establish `hm : ∀ u : U, f g (f u v) = f (g * u) v` using `fun u => by`. Simplify using `only [f, Subgroup.coe_mul, map_mul, Module.End.mul_apply]`.

Rewrite using `[map_sum]`. Repeatedly rewrite using `[hm]`. Conclude with `Equiv.sum_comp (Equiv.mulLeft g) (fun u => f u v)`. Establish `hA : (∑ u : U, f u) = 0`. Use extensionality with `v`.

Rewrite using `[LinearMap.sum_apply, LinearMap.zero_apply]`. Conclude with `hU _ fun u hu => hinv ⟨u, hu⟩ v`. Set `F` to `PiTensorProduct.mapMultilinear ℂ (fun c => (lam c : Type)) (fun c => (lam c : Type))`. Set `m : ∀ c', (lam c' : Type) →ₗ[ℂ] (lam c' : Type)` to `fun c' => LinearMap.id`. Establish `h1 : F (Function.update m c (∑ u : U, f u)) y = (Fintype.card U) • y`.

Rewrite using `[MultilinearMap.map_update_sum, LinearMap.sum_apply]`. Establish `: ∀ u : U, F (Function.update m c (f u)) y = y` using `fun u => hy u u.2`. Repeatedly rewrite using `[this]`. Rewrite using `[Finset.sum_const, Finset.card_univ]`. Rewrite `h1` using `[hA, MultilinearMap.map_update_zero, LinearMap.zero_apply]`.

Establish `hcard : (Fintype.card U : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 Fintype.card_ne_zero`. Rewrite `h1` using `[← Nat.cast_smul_eq_nsmul ℂ]`. Conclude with `(smul_eq_zero.1 h1.symm).resolve_left hcard`.
-/
theorem tensor_eq_zero_of_fixed {K : Type} [Field K] [Fintype K] [DecidableEq K] {r s : ℕ} (b : Fin r → Fin s)
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)) (c : Fin s)
    (U : Subgroup (GL {i // b i = c} K))
    (hU : ∀ v : (lam c : Type), (∀ u ∈ U, (lam c).ρ u v = v) → v = 0)
    (y : PiTensorProduct ℂ (fun c => (lam c : Type)))
    (hy : ∀ u ∈ U, PiTensorProduct.map (Function.update
      (fun c' => (LinearMap.id : (lam c' : Type) →ₗ[ℂ] (lam c' : Type))) c ((lam c).ρ u)) y = y) :
    y = 0 := by
  classical
  let f : U → ((lam c : Type) →ₗ[ℂ] (lam c : Type)) := fun u => (lam c).ρ u
  have hinv : ∀ (g : U) (v : (lam c : Type)), f g (∑ u : U, f u v) = ∑ u : U, f u v := by
    intro g v
    have hm : ∀ u : U, f g (f u v) = f (g * u) v := fun u => by
      simp only [f, Subgroup.coe_mul, map_mul, Module.End.mul_apply]
    rw [map_sum]
    simp_rw [hm]
    exact Equiv.sum_comp (Equiv.mulLeft g) (fun u => f u v)
  have hA : (∑ u : U, f u) = 0 := by
    ext v
    rw [LinearMap.sum_apply, LinearMap.zero_apply]
    exact hU _ fun u hu => hinv ⟨u, hu⟩ v
  let F := PiTensorProduct.mapMultilinear ℂ (fun c => (lam c : Type)) (fun c => (lam c : Type))
  let m : ∀ c', (lam c' : Type) →ₗ[ℂ] (lam c' : Type) := fun c' => LinearMap.id
  have h1 : F (Function.update m c (∑ u : U, f u)) y = (Fintype.card U) • y := by
    rw [MultilinearMap.map_update_sum, LinearMap.sum_apply]
    have : ∀ u : U, F (Function.update m c (f u)) y = y := fun u => hy u u.2
    simp_rw [this]
    rw [Finset.sum_const, Finset.card_univ]
  rw [hA, MultilinearMap.map_update_zero, LinearMap.zero_apply] at h1
  have hcard : (Fintype.card U : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [← Nat.cast_smul_eq_nsmul ℂ] at h1
  exact (smul_eq_zero.1 h1.symm).resolve_left hcard

/- English proof (translation)
Introduce `K _ _ _ r s b lam hcusp S ⟨i, j, hb, hi, hj⟩ y hy`. Establish `hb' : b i = b j` using `Fin.ext hb`. Set `c` to `b i`. Set `b₂ : {k // b k = c} → Fin 2` to `fun k => if k.1 ∈ S then 0 else 1`. Establish `hsurj : Function.Surjective b₂`.

Introduce `t`. Use `fin_cases t`. Conclude with `⟨⟨i, rfl⟩, by simp [b₂, hi]⟩`. Conclude with `⟨⟨j, hb'.symm⟩, by simp [b₂, hj]⟩`. Use `tensor_eq_zero_of_fixed b lam c (cuspUnipGroup b₂) (fun v hv => hcusp c 2 b₂ hsurj le_rfl v hv) y ?_` and prove the remaining obligations.

Introduce `u' hu'`. Establish `hu : u' ∈ unip K b₂` using `hu'`. Rewrite using `[← leviTensor_blockExt b lam c u']`. Apply `hy` to reduce the goal to its premises. Introduce `x z hxz`.

Distinguish the cases in `hin : b x = c ∧ b z = c`. Use `⟨by simp only [natBlocks, hin.1, hin.2], ?_⟩` and prove the remaining obligations. Establish `e` using `blockExt_in b c u' ⟨x, hin.1⟩ ⟨z, hin.2⟩`. Simplify using `only at e`. Rewrite `hxz` using `[e]`.

Assume the negation of the conclusion as `hcon`. Apply `hxz` to reduce the goal to its premises. Apply the tactic sequence `by_cases hxS : x ∈ S <;> by_cases hzS : z ∈ S`. Rewrite using `[hu.2 ⟨x, hin.1⟩ ⟨z, hin.2⟩ (by simp [b₂, hxS, hzS])]`. Simplify using `[Matrix.one_apply, Subtype.ext_iff]`.

Conclude with `absurd ⟨hxS, hzS⟩ hcon`. Rewrite using `[hu.1.1 ⟨x, hin.1⟩ ⟨z, hin.2⟩ (by simp [b₂, hxS, hzS]), Matrix.one_apply_ne (by rintro rfl; exact hxS hzS)]`. Rewrite using `[hu.2 ⟨x, hin.1⟩ ⟨z, hin.2⟩ (by simp [b₂, hxS, hzS])]`. Simplify using `[Matrix.one_apply, Subtype.ext_iff]`. Conclude with `absurd (blockExt_out b c u' x z hin) hxz`.
-/
theorem cuspidal_tensor_no_unip_fixed : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (r s : ℕ) (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)), (∀ c, IsCuspidal K (lam c)) → ∀ S : Finset (Fin r), (∃ i j, natBlocks b i = natBlocks b j ∧ i ∈ S ∧ j ∉ S) → ∀ y : PiTensorProduct ℂ (fun c => (lam c : Type)), (∀ u : blockTri (κ := K) (natBlocks b), (∀ i j, ((u : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) i j ≠ (1 : Matrix (Fin r) (Fin r) K) i j → natBlocks b i = natBlocks b j ∧ i ∈ S ∧ j ∉ S) → leviTensor b lam u y = y) → y = 0 := by
  intro K _ _ _ r s b lam hcusp S ⟨i, j, hb, hi, hj⟩ y hy
  have hb' : b i = b j := Fin.ext hb
  let c := b i
  let b₂ : {k // b k = c} → Fin 2 := fun k => if k.1 ∈ S then 0 else 1
  have hsurj : Function.Surjective b₂ := by
    intro t
    fin_cases t
    · exact ⟨⟨i, rfl⟩, by simp [b₂, hi]⟩
    · exact ⟨⟨j, hb'.symm⟩, by simp [b₂, hj]⟩
  refine tensor_eq_zero_of_fixed b lam c (cuspUnipGroup b₂)
    (fun v hv => hcusp c 2 b₂ hsurj le_rfl v hv) y ?_
  intro u' hu'
  have hu : u' ∈ unip K b₂ := hu'
  rw [← leviTensor_blockExt b lam c u']
  apply hy
  intro x z hxz
  by_cases hin : b x = c ∧ b z = c
  · refine ⟨by simp only [natBlocks, hin.1, hin.2], ?_⟩
    have e := blockExt_in b c u' ⟨x, hin.1⟩ ⟨z, hin.2⟩
    dsimp only at e
    rw [e] at hxz
    by_contra hcon
    apply hxz
    by_cases hxS : x ∈ S <;> by_cases hzS : z ∈ S
    · rw [hu.2 ⟨x, hin.1⟩ ⟨z, hin.2⟩ (by simp [b₂, hxS, hzS])]
      simp [Matrix.one_apply, Subtype.ext_iff]
    · exact absurd ⟨hxS, hzS⟩ hcon
    · rw [hu.1.1 ⟨x, hin.1⟩ ⟨z, hin.2⟩ (by simp [b₂, hxS, hzS]),
        Matrix.one_apply_ne (by rintro rfl; exact hxS hzS)]
    · rw [hu.2 ⟨x, hin.1⟩ ⟨z, hin.2⟩ (by simp [b₂, hxS, hzS])]
      simp [Matrix.one_apply, Subtype.ext_iff]
  · exact absurd (blockExt_out b c u' x z hin) hxz

end GlobalTheory.HcIrr
