import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.CharacterCosetSumEqZeroOfSubgroupSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockParabolicSubgroupLeviProjectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumMemEq

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct Matrix
open scoped Classical

noncomputable section
namespace GlobalTheory.Shin.FreeHc

variable {F : Type} [Field F]

/- English proof (translation)
Establish `h1 : ∀ u ∈ T, (∑ g, if g ∈ S then φ (g * ψ u) else 0) = ∑ g, if g ∈ S then φ g else 0` using `fun u hu => Fintype.sum_equiv (Equiv.mulRight (ψ u)) _ _ (fun g => by`. Simplify using `[Subgroup.mul_mem_cancel_right S (hψ u hu)])`. Establish `h2 : (∑ u, if u ∈ T then (∑ g, if g ∈ S then φ g else 0) else 0) = 0`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun u _ => ?_` and prove the remaining obligations.

Distinguish the cases in `hu : u ∈ T`. Simplify using `only [hu, if_true]`. Conclude with `(h1 u hu).symm`. Simplify using `[hu]`. Use `_ = ∑ g, ∑ u, (if u ∈ T then (if g ∈ S then φ (g * ψ u) else 0) else 0) := Finset.sum_comm`.

Use `_ = 0 := by`. Use `Finset.sum_eq_zero fun g _ => ?_` and prove the remaining obligations. Distinguish the cases in `hg : g ∈ S`. Simplify `h g hg` using `[hg]`. Simplify using `[hg]`.

Rewrite `h2` using `[← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]`. Break down `mul_eq_zero.1 h2 with h3 | h3` into its components or cases. It suffices to derive a contradiction. Take `⟨u, hu⟩` from `hT`. Establish `: (Finset.univ.filter (· ∈ T)).card ≠ 0` using `Finset.card_ne_zero.2 ⟨u, by simp [hu]⟩`.

Conclude with `this (by exact_mod_cast h3)`. Conclude with `h3`.
-/
theorem avg {G H : Type} [Group G] [Fintype G] [Fintype H] (S : Subgroup G) (T : Set H) (hT : T.Nonempty)
    (ψ : H → G) (hψ : ∀ u ∈ T, ψ u ∈ S) (φ : G → ℂ)
    (h : ∀ g ∈ S, (∑ u, if u ∈ T then φ (g * ψ u) else 0) = 0) :
    (∑ g, if g ∈ S then φ g else 0) = 0 := by
  have h1 : ∀ u ∈ T, (∑ g, if g ∈ S then φ (g * ψ u) else 0) = ∑ g, if g ∈ S then φ g else 0 :=
    fun u hu => Fintype.sum_equiv (Equiv.mulRight (ψ u)) _ _ (fun g => by
      simp [Subgroup.mul_mem_cancel_right S (hψ u hu)])
  have h2 : (∑ u, if u ∈ T then (∑ g, if g ∈ S then φ g else 0) else 0) = 0 := by
    calc _ = ∑ u, ∑ g, (if u ∈ T then (if g ∈ S then φ (g * ψ u) else 0) else 0) := by
            refine Finset.sum_congr rfl fun u _ => ?_
            by_cases hu : u ∈ T
            · simp only [hu, if_true]; exact (h1 u hu).symm
            · simp [hu]
      _ = ∑ g, ∑ u, (if u ∈ T then (if g ∈ S then φ (g * ψ u) else 0) else 0) := Finset.sum_comm
      _ = 0 := by
            refine Finset.sum_eq_zero fun g _ => ?_
            by_cases hg : g ∈ S
            · simpa [hg] using h g hg
            · simp [hg]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul] at h2
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exfalso
    obtain ⟨u, hu⟩ := hT
    have : (Finset.univ.filter (· ∈ T)).card ≠ 0 :=
      Finset.card_ne_zero.2 ⟨u, by simp [hu]⟩
    exact this (by exact_mod_cast h3)
  · exact h3

/- English proof (translation)
Rewrite using `[finsum_eq_sum_of_fintype, ← Finset.sum_filter]`. Conclude with `(Finset.sum_subtype _ (by simp) χ).symm`.
-/
theorem sub_sum {G : Type} [Group G] [Fintype G] (H : Subgroup G) (χ : G → ℂ) :
    ∑ᶠ u : H, χ u = ∑ g, if g ∈ H then χ g else 0 := by
  rw [finsum_eq_sum_of_fintype, ← Finset.sum_filter]
  exact (Finset.sum_subtype _ (by simp) χ).symm

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [Set.mem_ofPred_eq, fixSet, eLast, single_dotProduct, one_mul]`. Prove the components needed by the constructor for the conclusion. Introduce `h w hw`. Use extensionality with `i`.

Simplify using `only [mulVec, dotProduct]`. Rewrite using `[show w i = ∑ j, (1 : Matrix (Fin m) (Fin m) F) i j * w j by simp [Matrix.one_apply]]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Distinguish the cases in `hj : (j : ℕ) + 1 < m`. Rewrite using `[h i j hj]`.

Establish `: j = ⟨m - 1, by omega⟩` using `Fin.ext (by simp; omega)`. Rewrite using `[this, hw]`. Simplify using the standard rewrite rules. Introduce `h i j hj`. Establish `hne : (⟨m - 1, by omega⟩ : Fin m) ≠ j`.

Introduce `h'`. Rewrite `hj` using `[← h']`. Simplify using `at hj`. Use linear arithmetic over natural numbers and integers. Use `congrFun (h (Pi.single j 1) (by rw [Pi.single_eq_of_ne hne])) i` as an intermediate fact.

Simplify `this` using `[mulVec_single_one, Matrix.one_apply, Pi.single_apply]`.
-/
theorem hyp_eq {m : ℕ} (hm : 0 < m) :
    {x : GL (Fin m) F | ∀ i j : Fin m, (j : ℕ) + 1 < m →
      (x : Matrix (Fin m) (Fin m) F) i j = (1 : Matrix (Fin m) (Fin m) F) i j} = fixSet (eLast m hm) := by
  ext x
  simp only [Set.mem_ofPred_eq, fixSet, eLast, single_dotProduct, one_mul]
  constructor
  · intro h w hw
    ext i
    simp only [mulVec, dotProduct]
    rw [show w i = ∑ j, (1 : Matrix (Fin m) (Fin m) F) i j * w j by simp [Matrix.one_apply]]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : (j : ℕ) + 1 < m
    · rw [h i j hj]
    · have : j = ⟨m - 1, by omega⟩ := Fin.ext (by simp; omega)
      rw [this, hw]
      simp
  · intro h i j hj
    have hne : (⟨m - 1, by omega⟩ : Fin m) ≠ j := by
      intro h'; rw [← h'] at hj; simp at hj; omega
    have := congrFun (h (Pi.single j 1) (by rw [Pi.single_eq_of_ne hne])) i
    simpa [mulVec_single_one, Matrix.one_apply, Pi.single_apply] using this

/- English proof (translation)
Establish `he : eLast (F` using `F) m hm ≠ 0 := by`. Introduce `h`. Use `congrFun h ⟨m - 1, by omega⟩` as an intermediate fact. Simplify using `[eLast] at this`. Take `⟨g, hg⟩` from `Submodule.exists_linearEquiv_restrict_eq ((LinearEquiv.toSpanNonzeroSingleton F (Fin m → F) (eLast m hm) he).symm.trans (LinearEquiv.toSpanNonzeroSingleton F (Fin m → F) f hf))`.

Establish `h1` using `hg ⟨eLast m hm, Submodule.mem_span_singleton_self _⟩`. Rewrite `h1` using `[← LinearEquiv.toSpanNonzeroSingleton_one F (Fin m → F) (eLast m hm) he, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, LinearEquiv.toSpanNonzeroSingleton_one, LinearEquiv.toSpanNonzeroSingleton_one]`. Use `set M := LinearMap.toMatrix' g.toLinearMap with hM`. Use `set N := LinearMap.toMatrix' g.symm.toLinearMap with hN`. Establish `hMN : M * N = 1` using `by rw [hM, hN, ← LinearMap.toMatrix'_comp]; simp`.

Establish `hNM : N * M = 1` using `by rw [hM, hN, ← LinearMap.toMatrix'_comp]; simp`. Use `⟨⟨Mᵀ, Nᵀ, by rw [← transpose_mul, hNM, transpose_one], by rw [← transpose_mul, hMN, transpose_one]⟩, ?_⟩` and prove the remaining obligations. Use `show eLast m hm ᵥ* Mᵀ = f`. Rewrite using `[vecMul_transpose, hM, LinearMap.toMatrix'_mulVec]`. Conclude with `h1.symm`.
-/
theorem exists_row {m : ℕ} (hm : 0 < m) (f : Fin m → F) (hf : f ≠ 0) :
    ∃ z : GL (Fin m) F, eLast m hm ᵥ* (z : Matrix (Fin m) (Fin m) F) = f := by
  have he : eLast (F := F) m hm ≠ 0 := by
    intro h
    have := congrFun h ⟨m - 1, by omega⟩
    simp [eLast] at this
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq
    ((LinearEquiv.toSpanNonzeroSingleton F (Fin m → F) (eLast m hm) he).symm.trans
      (LinearEquiv.toSpanNonzeroSingleton F (Fin m → F) f hf))
  have h1 := hg ⟨eLast m hm, Submodule.mem_span_singleton_self _⟩
  rw [← LinearEquiv.toSpanNonzeroSingleton_one F (Fin m → F) (eLast m hm) he, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply, LinearEquiv.toSpanNonzeroSingleton_one,
    LinearEquiv.toSpanNonzeroSingleton_one] at h1
  set M := LinearMap.toMatrix' g.toLinearMap with hM
  set N := LinearMap.toMatrix' g.symm.toLinearMap with hN
  have hMN : M * N = 1 := by rw [hM, hN, ← LinearMap.toMatrix'_comp]; simp
  have hNM : N * M = 1 := by rw [hM, hN, ← LinearMap.toMatrix'_comp]; simp
  refine ⟨⟨Mᵀ, Nᵀ, by rw [← transpose_mul, hNM, transpose_one], by rw [← transpose_mul, hMN, transpose_one]⟩, ?_⟩
  show eLast m hm ᵥ* Mᵀ = f
  rw [vecMul_transpose, hM, LinearMap.toMatrix'_mulVec]
  exact h1.symm

/- English proof (translation)
Establish `hm : 0 < m`. Break down `Nat.eq_zero_or_pos m with h | h` into its components or cases. Substitute `h` using the available equality. Conclude with `absurd (_root_.funext fun (i : Fin 0) => Fin.elim0 i) hf`. Conclude with `h`.

Take `⟨z, hz⟩` from `exists_row hm f hf`. Rewrite using `[← hz, ← sum_conj (eLast m hm) z Y]`. Simplify using `only [hY]`. Rewrite using `[← finsum_mem_eq, ← hyp_eq hm]`. Conclude with `hfree hm`.
-/
theorem transfer {m : ℕ} [Fintype (GL (Fin m) F)] (Y : GL (Fin m) F → ℂ) (hY : ∀ x y, Y (y⁻¹ * x * y) = Y x)
    (hfree : HFree Y) (f : Fin m → F) (hf : f ≠ 0) : (∑ x, if x ∈ fixSet f then Y x else 0) = 0 := by
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; exact absurd (_root_.funext fun (i : Fin 0) => Fin.elim0 i) hf
    · exact h
  obtain ⟨z, hz⟩ := exists_row hm f hf
  rw [← hz, ← sum_conj (eLast m hm) z Y]
  simp only [hY]
  rw [← finsum_mem_eq, ← hyp_eq hm]
  exact hfree hm

/- English proof (translation)
Rewrite using `[vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow]`.
-/
theorem detOne {m : ℕ} (u v : Fin m → F) : (1 + vecMulVec u v).det = 1 + v ⬝ᵥ u := by
  rw [vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow]

/- English proof (translation)
Unfold `toG`. Rewrite using `[dif_pos u.isUnit]`. Conclude with `Units.ext (IsUnit.unit_spec _)`.
-/
theorem toG_val {m : ℕ} (u : GL (Fin m) F) : toG (u : Matrix (Fin m) (Fin m) F) = u := by
  unfold toG
  rw [dif_pos u.isUnit]
  exact Units.ext (IsUnit.unit_spec _)

/- English proof (translation)
Unfold `toG`. Rewrite using `[dif_pos h]`. Conclude with `IsUnit.unit_spec _`.
-/
theorem toG_coe {m : ℕ} (M : Matrix (Fin m) (Fin m) F) (h : IsUnit M) : ((toG M : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = M := by
  unfold toG
  rw [dif_pos h]
  exact IsUnit.unit_spec _

/- English proof (translation)
Unfold `ent`. Rewrite using `[dif_pos ⟨by omega, by omega⟩]`. Both sides reduce to the same expression.
-/
theorem ent_castAdd {a b : ℕ} (M : Matrix (Fin (a + b)) (Fin (a + b)) F) (i j : Fin a) :
    ent M (i : ℕ) (j : ℕ) = M (Fin.castAdd b i) (Fin.castAdd b j) := by
  unfold ent
  rw [dif_pos ⟨by omega, by omega⟩]
  rfl

/- English proof (translation)
Unfold `ent`. Rewrite using `[dif_pos ⟨by omega, by omega⟩]`. Both sides reduce to the same expression.
-/
theorem ent_natAdd {a b : ℕ} (M : Matrix (Fin (a + b)) (Fin (a + b)) F) (i j : Fin b) :
    ent M (a + (i : ℕ)) (a + (j : ℕ)) = M (Fin.natAdd a i) (Fin.natAdd a j) := by
  unfold ent
  rw [dif_pos ⟨by omega, by omega⟩]
  rfl

/- English proof (translation)
Take `⟨i, hi⟩` from `Function.ne_iff.1 hf`. Use `⟨Pi.single i (f i)⁻¹, ?_⟩` and prove the remaining obligations. Rewrite using `[dotProduct_single]`. Conclude with `mul_inv_cancel₀ hi`.
-/
theorem exists_dot_one {m : ℕ} (f : Fin m → F) (hf : f ≠ 0) : ∃ w₀ : Fin m → F, f ⬝ᵥ w₀ = 1 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hf
  refine ⟨Pi.single i (f i)⁻¹, ?_⟩
  rw [dotProduct_single]
  exact mul_inv_cancel₀ hi

/- English proof (translation)
Use `set fa : Fin a → F := fun i => f (Fin.castAdd b i) with hfa`. Take `⟨w₀, hw₀⟩` from `exists_dot_one fa hf`. Set `vt : GL (Fin a) F → Fin (a + b) → F` to `fun u => Fin.append ((u : Matrix (Fin a) (Fin a) F) *ᵥ w₀ - w₀) (0 : Fin b → F)`. Use `⟨fun u => toG (1 + vecMulVec (vt u) f), fun u hu => ?_⟩` and prove the remaining obligations. Establish `hkey` using `key fa w₀ hw₀ u hu`.

Establish `hdot : f ⬝ᵥ vt u = fa ⬝ᵥ ((u : Matrix (Fin a) (Fin a) F) *ᵥ w₀ - w₀)`. Simplify using `[vt, dotProduct, Fin.sum_univ_add, hfa]`. Establish `hunit : IsUnit (1 + vecMulVec (vt u) f)`. Rewrite using `[Matrix.isUnit_iff_isUnit_det, detOne, hdot, ← detOne, ← hkey]`. Conclude with `Matrix.isUnits_det_units u`.

Establish `hc` using `toG_coe _ hunit`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `w hw`. Rewrite using `[hc, add_mulVec, one_mulVec, vmv_mulVec, hw, zero_smul, add_zero]`. Introduce `i j hj hi`.

Take `⟨k, rfl⟩ : ∃ k : Fin b, i = Fin.natAdd a k` from `⟨⟨i - a, by omega⟩, Fin.ext (by simp; omega)⟩`. Establish `hne : Fin.natAdd a k ≠ j` using `fun h => by rw [← h] at hj; simp at hj`. Rewrite using `[hc]`. Simplify using `[vt, vecMulVec, Matrix.one_apply, hne]`. Unfold `tlG conv_rhs => rw [← toG_val u]`.

Use `congr 1`. Use extensionality with `i j`. Unfold `tl`. Rewrite using `[ent_castAdd, hc]`. Use `conv_rhs => rw [hkey]`.

Simplify using `[vt, vecMulVec, Matrix.one_apply, hfa]`. Unfold `brG`. Rewrite using `[← toG_val (1 : GL (Fin b) F)]`. Use `congr 1`. Use extensionality with `i j`.

Unfold `br`. Rewrite using `[ent_natAdd, hc]`. Simplify using `[vt, vecMulVec, Matrix.one_apply]`.
-/
theorem sec1 (a b : ℕ) (f : Fin (a + b) → F) (hf : (fun i => f (Fin.castAdd b i)) ≠ 0) :
    ∃ ψ : GL (Fin a) F → GL (Fin (a + b)) F, ∀ u ∈ fixSet (fun i => f (Fin.castAdd b i)),
      ψ u ∈ fixSet f ∧ InPar a (ψ u) ∧ tlG a (ψ u) = u ∧ brG a b (ψ u) = 1 := by
  set fa : Fin a → F := fun i => f (Fin.castAdd b i) with hfa
  obtain ⟨w₀, hw₀⟩ := exists_dot_one fa hf
  let vt : GL (Fin a) F → Fin (a + b) → F := fun u =>
    Fin.append ((u : Matrix (Fin a) (Fin a) F) *ᵥ w₀ - w₀) (0 : Fin b → F)
  refine ⟨fun u => toG (1 + vecMulVec (vt u) f), fun u hu => ?_⟩
  have hkey := key fa w₀ hw₀ u hu
  have hdot : f ⬝ᵥ vt u = fa ⬝ᵥ ((u : Matrix (Fin a) (Fin a) F) *ᵥ w₀ - w₀) := by
    simp [vt, dotProduct, Fin.sum_univ_add, hfa]
  have hunit : IsUnit (1 + vecMulVec (vt u) f) := by
    rw [Matrix.isUnit_iff_isUnit_det, detOne, hdot, ← detOne, ← hkey]
    exact Matrix.isUnits_det_units u
  have hc := toG_coe _ hunit
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w hw
    rw [hc, add_mulVec, one_mulVec, vmv_mulVec, hw, zero_smul, add_zero]
  · intro i j hj hi
    obtain ⟨k, rfl⟩ : ∃ k : Fin b, i = Fin.natAdd a k := ⟨⟨i - a, by omega⟩, Fin.ext (by simp; omega)⟩
    have hne : Fin.natAdd a k ≠ j := fun h => by rw [← h] at hj; simp at hj
    rw [hc]
    simp [vt, vecMulVec, Matrix.one_apply, hne]
  · unfold tlG
    conv_rhs => rw [← toG_val u]
    congr 1
    ext i j
    unfold tl
    rw [ent_castAdd, hc]
    conv_rhs => rw [hkey]
    simp [vt, vecMulVec, Matrix.one_apply, hfa]
  · unfold brG
    rw [← toG_val (1 : GL (Fin b) F)]
    congr 1
    ext i j
    unfold br
    rw [ent_natAdd, hc]
    simp [vt, vecMulVec, Matrix.one_apply]

/- English proof (translation)
Use `set fb : Fin b → F := fun j => f (Fin.natAdd a j) with hfb`. Establish `h0' : ∀ i, f (Fin.castAdd b i) = 0` using `fun i => congrFun h0 i`. Take `⟨w₀, hw₀⟩` from `exists_dot_one fb hf`. Set `vt : GL (Fin b) F → Fin (a + b) → F` to `fun u => Fin.append (0 : Fin a → F) ((u : Matrix (Fin b) (Fin b) F) *ᵥ w₀ - w₀)`. Use `⟨fun u => toG (1 + vecMulVec (vt u) f), fun u hu => ?_⟩` and prove the remaining obligations.

Establish `hkey` using `key fb w₀ hw₀ u hu`. Establish `hdot : f ⬝ᵥ vt u = fb ⬝ᵥ ((u : Matrix (Fin b) (Fin b) F) *ᵥ w₀ - w₀)`. Simplify using `[vt, dotProduct, Fin.sum_univ_add, hfb]`. Establish `hunit : IsUnit (1 + vecMulVec (vt u) f)`. Rewrite using `[Matrix.isUnit_iff_isUnit_det, detOne, hdot, ← detOne, ← hkey]`.

Conclude with `Matrix.isUnits_det_units u`. Establish `hc` using `toG_coe _ hunit`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `w hw`. Rewrite using `[hc, add_mulVec, one_mulVec, vmv_mulVec, hw, zero_smul, add_zero]`.

Introduce `i j hj hi`. Take `⟨k, rfl⟩ : ∃ k : Fin b, i = Fin.natAdd a k` from `⟨⟨i - a, by omega⟩, Fin.ext (by simp; omega)⟩`. Take `⟨l, rfl⟩ : ∃ l : Fin a, j = Fin.castAdd b l` from `⟨⟨j, hj⟩, Fin.ext (by simp)⟩`. Establish `hne : Fin.natAdd a k ≠ Fin.castAdd b l` using `fun h => by`. Use `congrArg Fin.val h` as an intermediate fact.

Simplify using `at this`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hc]`. Simplify using `[vecMulVec, Matrix.one_apply, hne, h0']`. Unfold `tlG`.

Rewrite using `[← toG_val (1 : GL (Fin a) F)]`. Use `congr 1`. Use extensionality with `i j`. Unfold `tl`. Rewrite using `[ent_castAdd, hc]`.

Simplify using `[vt, vecMulVec, Matrix.one_apply]`. Unfold `brG conv_rhs => rw [← toG_val u]`. Use `congr 1`. Use extensionality with `i j`. Unfold `br`.

Rewrite using `[ent_natAdd, hc]`. Use `conv_rhs => rw [hkey]`. Simplify using `[vt, vecMulVec, Matrix.one_apply, hfb]`.
-/
theorem sec2 (a b : ℕ) (f : Fin (a + b) → F) (h0 : (fun i => f (Fin.castAdd b i)) = 0)
    (hf : (fun j => f (Fin.natAdd a j)) ≠ 0) :
    ∃ ψ : GL (Fin b) F → GL (Fin (a + b)) F, ∀ u ∈ fixSet (fun j => f (Fin.natAdd a j)),
      ψ u ∈ fixSet f ∧ InPar a (ψ u) ∧ tlG a (ψ u) = 1 ∧ brG a b (ψ u) = u := by
  set fb : Fin b → F := fun j => f (Fin.natAdd a j) with hfb
  have h0' : ∀ i, f (Fin.castAdd b i) = 0 := fun i => congrFun h0 i
  obtain ⟨w₀, hw₀⟩ := exists_dot_one fb hf
  let vt : GL (Fin b) F → Fin (a + b) → F := fun u =>
    Fin.append (0 : Fin a → F) ((u : Matrix (Fin b) (Fin b) F) *ᵥ w₀ - w₀)
  refine ⟨fun u => toG (1 + vecMulVec (vt u) f), fun u hu => ?_⟩
  have hkey := key fb w₀ hw₀ u hu
  have hdot : f ⬝ᵥ vt u = fb ⬝ᵥ ((u : Matrix (Fin b) (Fin b) F) *ᵥ w₀ - w₀) := by
    simp [vt, dotProduct, Fin.sum_univ_add, hfb]
  have hunit : IsUnit (1 + vecMulVec (vt u) f) := by
    rw [Matrix.isUnit_iff_isUnit_det, detOne, hdot, ← detOne, ← hkey]
    exact Matrix.isUnits_det_units u
  have hc := toG_coe _ hunit
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w hw
    rw [hc, add_mulVec, one_mulVec, vmv_mulVec, hw, zero_smul, add_zero]
  · intro i j hj hi
    obtain ⟨k, rfl⟩ : ∃ k : Fin b, i = Fin.natAdd a k := ⟨⟨i - a, by omega⟩, Fin.ext (by simp; omega)⟩
    obtain ⟨l, rfl⟩ : ∃ l : Fin a, j = Fin.castAdd b l := ⟨⟨j, hj⟩, Fin.ext (by simp)⟩
    have hne : Fin.natAdd a k ≠ Fin.castAdd b l := fun h => by
      have := congrArg Fin.val h; simp at this; omega
    rw [hc]
    simp [vecMulVec, Matrix.one_apply, hne, h0']
  · unfold tlG
    rw [← toG_val (1 : GL (Fin a) F)]
    congr 1
    ext i j
    unfold tl
    rw [ent_castAdd, hc]
    simp [vt, vecMulVec, Matrix.one_apply]
  · unfold brG
    conv_rhs => rw [← toG_val u]
    congr 1
    ext i j
    unfold br
    rw [ent_natAdd, hc]
    conv_rhs => rw [hkey]
    simp [vt, vecMulVec, Matrix.one_apply, hfb]

/- English proof (translation)
Establish `h0` using `transfer Y (fun x y => isChar_conj hY x y) hfree f hf`. Establish `h1 : ∑ᶠ u : fixSub f, Y u = 0`. Rewrite using `[sub_sum]`. Conclude with `h0`. Establish `h2` using `char_coset_sum_eq_zero (GL (Fin m) F) Y hY (fixSub f) h1 c`.

Rewrite `h2` using `[sub_sum (fixSub f) (fun u => Y (c * u))]`. Conclude with `h2`.
-/
theorem coset_zero {m : ℕ} [Finite F] [Fintype (GL (Fin m) F)] (Y : GL (Fin m) F → ℂ) (hY : IsChar ℂ ℂ Y)
    (hfree : HFree Y) (f : Fin m → F) (hf : f ≠ 0) (c : GL (Fin m) F) :
    (∑ u, if u ∈ fixSet f then Y (c * u) else 0) = 0 := by
  have h0 := transfer Y (fun x y => isChar_conj hY x y) hfree f hf
  have h1 : ∑ᶠ u : fixSub f, Y u = 0 := by
    rw [sub_sum]; exact h0
  have h2 := char_coset_sum_eq_zero (GL (Fin m) F) Y hY (fixSub f) h1 c
  rw [sub_sum (fixSub f) (fun u => Y (c * u))] at h2
  exact h2

/- English proof (translation)
Take `⟨P, π, hmem, -, hπ, -, -⟩` from `GlobalTheory.T.exists_blockParabolic_subgroup_levi_projection F a b (a + b) rfl`. Establish `hmul : ∀ p q : GL (Fin (a + b)) F, InPar a p → InPar a q → InPar a (p * q) ∧ tlG a (p * q) = tlG a p * tlG a q ∧ brG a b (p * q) = brG a b p * brG a b q`. Introduce `p q hp hq`. Establish `hp'` using `(hmem p).2 hp`. Establish `hq'` using `(hmem q).2 hq`.

Establish `h` using `map_mul π ⟨p, hp'⟩ ⟨q, hq'⟩`. Rewrite `h` using `[hπ, hπ, hπ]`. Use `⟨(hmem _).1 (P.mul_mem hp' hq'), ?_, ?_⟩` and prove the remaining obligations. Conclude with `congrArg Prod.fst h`. Conclude with `congrArg Prod.snd h`.

Establish `hnot : ∀ p q : GL (Fin (a + b)) F, ¬ InPar a p → InPar a q → ¬ InPar a (p * q)`. Introduce `p q hp hq hpq`. Apply `hp` to reduce the goal to its premises. Use `P.mul_mem ((hmem _).2 hpq) (P.inv_mem ((hmem _).2 hq))` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel_right]`.

Conclude with `(hmem _).1 this`. Establish `hS : ∀ g, g ∈ fixSub f ↔ g ∈ fixSet f` using `fun _ => Iff.rfl`. Repeatedly rewrite using `[← hS]`. Distinguish the cases in `h0 : (fun i => f (Fin.castAdd b i)) = 0`. Establish `hf2 : (fun j => f (Fin.natAdd a j)) ≠ 0`.

Introduce `h2`. Apply `hf` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Use `Fin.addCases (fun i => ?_) (fun j => ?_) i` and prove the remaining obligations. Conclude with `congrFun h0 i`.

Conclude with `congrFun h2 j`. Take `⟨ψ, hψ⟩` from `sec2 a b f h0 hf2`. Use `haveI : Fintype (GL (Fin b) F) := Fintype.ofFinite _`. Use `avg (fixSub f) (fixSet fun j => f (Fin.natAdd a j)) ⟨1, (fixSub _).one_mem⟩ ψ (fun u hu => (hψ u hu).1) _ fun g hg => ?_` and prove the remaining obligations. Distinguish the cases in `hpg : InPar a g`.

Establish `: ∀ u, (if u ∈ fixSet (fun j => f (Fin.natAdd a j)) then (if InPar a (g * ψ u) then A (tlG a (g * ψ u)) * B (brG a b (g * ψ u)) else 0) else 0) = A (tlG a g) * (if u ∈ fixSet (fun j => f (Fin.natAdd a j)) then B (brG a b g * u) else 0)`. Introduce `u`. Distinguish the cases in `hu : u ∈ fixSet (fun j => f (Fin.natAdd a j))`. Take `⟨-, hp, ht, hb⟩` from `hψ u hu`. Take `⟨h1, h2, h3⟩` from `hmul g (ψ u) hpg hp`.

Simplify using `[hu, h1, h2, h3, ht, hb]`. Simplify using `[hu]`. Rewrite using `[Finset.sum_congr rfl fun u _ => this u, ← Finset.mul_sum, coset_zero B hB hfB _ hf2, mul_zero]`. Use `Finset.sum_eq_zero fun u _ => ?_` and prove the remaining obligations. Distinguish the cases in `hu : u ∈ fixSet (fun j => f (Fin.natAdd a j))`.

Simplify using `[hu, hnot g (ψ u) hpg (hψ u hu).2.1]`. Simplify using `[hu]`. Take `⟨ψ, hψ⟩` from `sec1 a b f h0 haveI : Fintype (GL (Fin a) F) := Fintype.ofFinite _`. Use `avg (fixSub f) (fixSet fun i => f (Fin.castAdd b i)) ⟨1, (fixSub _).one_mem⟩ ψ (fun u hu => (hψ u hu).1) _ fun g hg => ?_` and prove the remaining obligations. Distinguish the cases in `hpg : InPar a g`.

Establish `: ∀ u, (if u ∈ fixSet (fun i => f (Fin.castAdd b i)) then (if InPar a (g * ψ u) then A (tlG a (g * ψ u)) * B (brG a b (g * ψ u)) else 0) else 0) = B (brG a b g) * (if u ∈ fixSet (fun i => f (Fin.castAdd b i)) then A (tlG a g * u) else 0)`. Introduce `u`. Distinguish the cases in `hu : u ∈ fixSet (fun i => f (Fin.castAdd b i))`. Take `⟨-, hp, ht, hb⟩` from `hψ u hu`. Take `⟨h1, h2, h3⟩` from `hmul g (ψ u) hpg hp`.

Simplify using `[hu, h1, h2, h3, ht, hb, mul_comm]`. Simplify using `[hu]`. Rewrite using `[Finset.sum_congr rfl fun u _ => this u, ← Finset.mul_sum, coset_zero A hA hfA _ h0, mul_zero]`. Use `Finset.sum_eq_zero fun u _ => ?_` and prove the remaining obligations. Distinguish the cases in `hu : u ∈ fixSet (fun i => f (Fin.castAdd b i))`.

Simplify using `[hu, hnot g (ψ u) hpg (hψ u hu).2.1]`. Simplify using `[hu]`.
-/
theorem core [Finite F] (a b : ℕ) [Fintype (GL (Fin (a + b)) F)] (A : GL (Fin a) F → ℂ) (B : GL (Fin b) F → ℂ)
    (hA : IsChar ℂ ℂ A) (hB : IsChar ℂ ℂ B) (hfA : HFree A) (hfB : HFree B) (f : Fin (a + b) → F) (hf : f ≠ 0) :
    (∑ g, if g ∈ fixSet f then
      (if InPar a g then A (tlG a g) * B (brG a b g) else 0) else 0) = 0 := by
  obtain ⟨P, π, hmem, -, hπ, -, -⟩ := GlobalTheory.T.exists_blockParabolic_subgroup_levi_projection F a b (a + b) rfl
  have hmul : ∀ p q : GL (Fin (a + b)) F, InPar a p → InPar a q →
      InPar a (p * q) ∧ tlG a (p * q) = tlG a p * tlG a q ∧ brG a b (p * q) = brG a b p * brG a b q := by
    intro p q hp hq
    have hp' := (hmem p).2 hp
    have hq' := (hmem q).2 hq
    have h := map_mul π ⟨p, hp'⟩ ⟨q, hq'⟩
    rw [hπ, hπ, hπ] at h
    refine ⟨(hmem _).1 (P.mul_mem hp' hq'), ?_, ?_⟩
    · exact congrArg Prod.fst h
    · exact congrArg Prod.snd h
  have hnot : ∀ p q : GL (Fin (a + b)) F, ¬ InPar a p → InPar a q → ¬ InPar a (p * q) := by
    intro p q hp hq hpq
    apply hp
    have := P.mul_mem ((hmem _).2 hpq) (P.inv_mem ((hmem _).2 hq))
    rw [mul_inv_cancel_right] at this
    exact (hmem _).1 this
  have hS : ∀ g, g ∈ fixSub f ↔ g ∈ fixSet f := fun _ => Iff.rfl
  simp_rw [← hS]
  by_cases h0 : (fun i => f (Fin.castAdd b i)) = 0
  · have hf2 : (fun j => f (Fin.natAdd a j)) ≠ 0 := by
      intro h2
      apply hf
      funext i
      refine Fin.addCases (fun i => ?_) (fun j => ?_) i
      · exact congrFun h0 i
      · exact congrFun h2 j
    obtain ⟨ψ, hψ⟩ := sec2 a b f h0 hf2
    haveI : Fintype (GL (Fin b) F) := Fintype.ofFinite _
    refine avg (fixSub f) (fixSet fun j => f (Fin.natAdd a j)) ⟨1, (fixSub _).one_mem⟩ ψ
      (fun u hu => (hψ u hu).1) _ fun g hg => ?_
    by_cases hpg : InPar a g
    · have : ∀ u, (if u ∈ fixSet (fun j => f (Fin.natAdd a j)) then
          (if InPar a (g * ψ u) then A (tlG a (g * ψ u)) * B (brG a b (g * ψ u)) else 0) else 0) =
          A (tlG a g) * (if u ∈ fixSet (fun j => f (Fin.natAdd a j)) then B (brG a b g * u) else 0) := by
        intro u
        by_cases hu : u ∈ fixSet (fun j => f (Fin.natAdd a j))
        · obtain ⟨-, hp, ht, hb⟩ := hψ u hu
          obtain ⟨h1, h2, h3⟩ := hmul g (ψ u) hpg hp
          simp [hu, h1, h2, h3, ht, hb]
        · simp [hu]
      rw [Finset.sum_congr rfl fun u _ => this u, ← Finset.mul_sum, coset_zero B hB hfB _ hf2, mul_zero]
    · refine Finset.sum_eq_zero fun u _ => ?_
      by_cases hu : u ∈ fixSet (fun j => f (Fin.natAdd a j))
      · simp [hu, hnot g (ψ u) hpg (hψ u hu).2.1]
      · simp [hu]
  · obtain ⟨ψ, hψ⟩ := sec1 a b f h0
    haveI : Fintype (GL (Fin a) F) := Fintype.ofFinite _
    refine avg (fixSub f) (fixSet fun i => f (Fin.castAdd b i)) ⟨1, (fixSub _).one_mem⟩ ψ
      (fun u hu => (hψ u hu).1) _ fun g hg => ?_
    by_cases hpg : InPar a g
    · have : ∀ u, (if u ∈ fixSet (fun i => f (Fin.castAdd b i)) then
          (if InPar a (g * ψ u) then A (tlG a (g * ψ u)) * B (brG a b (g * ψ u)) else 0) else 0) =
          B (brG a b g) * (if u ∈ fixSet (fun i => f (Fin.castAdd b i)) then A (tlG a g * u) else 0) := by
        intro u
        by_cases hu : u ∈ fixSet (fun i => f (Fin.castAdd b i))
        · obtain ⟨-, hp, ht, hb⟩ := hψ u hu
          obtain ⟨h1, h2, h3⟩ := hmul g (ψ u) hpg hp
          simp [hu, h1, h2, h3, ht, hb, mul_comm]
        · simp [hu]
      rw [Finset.sum_congr rfl fun u _ => this u, ← Finset.mul_sum, coset_zero A hA hfA _ h0, mul_zero]
    · refine Finset.sum_eq_zero fun u _ => ?_
      by_cases hu : u ∈ fixSet (fun i => f (Fin.castAdd b i))
      · simp [hu, hnot g (ψ u) hpg (hψ u hu).2.1]
      · simp [hu]

/- English proof (translation)
Introduce `F _ _ a b n hn A B hA hB hfA hfB`. Substitute `hn` using the available equality. Introduce `hpos`. Use `haveI : Fintype (GL (Fin (a + b)) F) := Fintype.ofFinite _`. Rewrite using `[hyp_eq hpos, finsum_mem_eq]`.

Establish `hgal : ∀ y : GL (Fin (a + b)) F, gal (RingHom.id F) (a + b) y = y` using `fun y => by ext; simp [gal]`. Simplify using `only [hc, hcTw, hgal, finsum_eq_sum_of_fintype]`. Establish `: ∀ x : GL (Fin (a + b)) F, (if x ∈ fixSet (eLast (a + b) hpos) then (Nat.card {p : GL (Fin (a + b)) F // InPar a p} : ℂ)⁻¹ * ∑ y : GL (Fin (a + b)) F, (if InPar a (y⁻¹ * x * y) then A (tlG a (y⁻¹ * x * y)) * B (brG a b (y⁻¹ * x * y)) else 0) else 0) = (Nat.card {p : GL (Fin (a + …`. Introduce `x`. Apply the tactic sequence `by_cases hx : x ∈ fixSet (eLast (a + b) hpos) <;> simp [hx]`.

Rewrite using `[Finset.sum_congr rfl fun x _ => this x, ← Finset.mul_sum, Finset.sum_comm]`. Use `mul_eq_zero_of_right _ (Finset.sum_eq_zero fun y _ => ?_)` and prove the remaining obligations. Rewrite using `[sum_conj (eLast (a + b) hpos) y (fun g => if InPar a g then A (tlG a g) * B (brG a b g) else 0)]`. Use `core a b A B hA hB hfA hfB _ ?_` and prove the remaining obligations. Introduce `h`.

Establish `h2` using `congrArg (fun v => v ᵥ* ((y⁻¹ : GL (Fin (a + b)) F) : Matrix (Fin (a + b)) (Fin (a + b)) F)) h`. Simplify using `only [vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vecMul_one, zero_vecMul] at h2`. Establish `h3` using `congrFun h2 ⟨a + b - 1, by omega⟩`. Simplify using `[eLast] at h3`.
-/
theorem hfree_hc : ∀ (F : Type) [Field F] [Finite F], ∀ (a b n : ℕ), n = a + b → ∀ (A : GL (Fin a) F → ℂ)
    (B : GL (Fin b) F → ℂ), IsChar ℂ ℂ A → IsChar ℂ ℂ B → HFree A → HFree B → HFree (hc a b A B n) := by
  intro F _ _ a b n hn A B hA hB hfA hfB
  subst hn
  intro hpos
  haveI : Fintype (GL (Fin (a + b)) F) := Fintype.ofFinite _
  rw [hyp_eq hpos, finsum_mem_eq]
  have hgal : ∀ y : GL (Fin (a + b)) F, gal (RingHom.id F) (a + b) y = y := fun y => by
    ext; simp [gal]
  simp only [hc, hcTw, hgal, finsum_eq_sum_of_fintype]
  have : ∀ x : GL (Fin (a + b)) F, (if x ∈ fixSet (eLast (a + b) hpos) then
      (Nat.card {p : GL (Fin (a + b)) F // InPar a p} : ℂ)⁻¹ * ∑ y : GL (Fin (a + b)) F,
        (if InPar a (y⁻¹ * x * y) then A (tlG a (y⁻¹ * x * y)) * B (brG a b (y⁻¹ * x * y)) else 0) else 0) =
      (Nat.card {p : GL (Fin (a + b)) F // InPar a p} : ℂ)⁻¹ * ∑ y : GL (Fin (a + b)) F,
        (if x ∈ fixSet (eLast (a + b) hpos) then
          (if InPar a (y⁻¹ * x * y) then A (tlG a (y⁻¹ * x * y)) * B (brG a b (y⁻¹ * x * y)) else 0) else 0) := by
    intro x
    by_cases hx : x ∈ fixSet (eLast (a + b) hpos) <;> simp [hx]
  rw [Finset.sum_congr rfl fun x _ => this x, ← Finset.mul_sum, Finset.sum_comm]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun y _ => ?_)
  rw [sum_conj (eLast (a + b) hpos) y
    (fun g => if InPar a g then A (tlG a g) * B (brG a b g) else 0)]
  refine core a b A B hA hB hfA hfB _ ?_
  intro h
  have h2 := congrArg (fun v => v ᵥ* ((y⁻¹ : GL (Fin (a + b)) F) : Matrix (Fin (a + b)) (Fin (a + b)) F)) h
  simp only [vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vecMul_one, zero_vecMul] at h2
  have h3 := congrFun h2 ⟨a + b - 1, by omega⟩
  simp [eLast] at h3

end GlobalTheory.Shin.FreeHc
