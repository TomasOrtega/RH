import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.CardFilterLtInj

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.GluingBases

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
/- English proof (translation)
Introduce `K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hUc hpos hΛ₀ M hM hMi 𝔭 h𝔭 b a hba hc`. Use `h𝔭.isPrime` as an intermediate fact. Establish `hne : 𝔭 ≠ ⊥` using `Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (RingOfIntegers.not_isField F)`. Use `set W := orthK h U with hW`. Use `set m := finrank K W with hm`.

Use `set P : Finset (Fin (finrank K U)) := Finset.univ.filter (fun i => vF 𝔭 (a i) ≠ 0) with hP`. Establish `hPc : P.card < m` using `hc`. Establish `hPm : ∀ i, (P.filter (· < i)).card < m` using `fun i => lt_of_le_of_lt (Finset.card_filter_le _ _) hPc`. Set `τ : Fin (finrank K U) → Fin m` to `fun i => ⟨(P.filter (· < i)).card, hPm i⟩`. Establish `hτ : ∀ i k, vF 𝔭 (a i) ≠ 0 → vF 𝔭 (a k) ≠ 0 → τ i = τ k → i = k`.

Introduce `i k hi hk e`. Conclude with `card_filter_lt_inj P (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩) (Finset.mem_filter.2 ⟨Finset.mem_univ _, hk⟩) (congrArg Fin.val e)`. Establish `hτl : ∀ i, vF 𝔭 (a i) ≠ 0 → (τ i : ℕ) + 1 < m`. Introduce `i hi`. Use `card_filter_lt_lt P (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)` as an intermediate fact.

Use `show (P.filter (· < i)).card + 1 < m`. Use linear arithmetic over natural numbers and integers. Use `choose nF hnpos hncong using fun i => exists_totPos_congr (K := K) h𝔭 hne (a i) (2 * vF 𝔭 (a i))`. Set `t : Fin m → K` to `fun j => if hj : ∃ i, vF 𝔭 (a i) ≠ 0 ∧ τ i = j then algebraMap F K (nF hj.choose) else 1`. Establish `hts : ∀ j, star (t j) = t j`.

Introduce `j`. Simplify using `only [t]`. Use `split_ifs`. Conclude with `star_fix hF _`. Conclude with `star_one K`.

Establish `htp : ∀ j, TotPos (t j)`. Introduce `j`. Simplify using `only [t]`. Use `split_ifs`. Conclude with `hnpos _`.

Introduce `φ`. Rewrite using `[map_one]`. Simplify using the standard rewrite rules. Establish `htpart : ∀ i, vF 𝔭 (a i) ≠ 0 → t (τ i) = algebraMap F K (nF i)`. Introduce `i hi`.

Establish `hj : ∃ i', vF 𝔭 (a i') ≠ 0 ∧ τ i' = τ i` using `⟨i, hi, rfl⟩`. Simplify using `only [t, dif_pos hj]`. Rewrite using `[hτ _ _ hj.choose_spec.1 hi hj.choose_spec.2]`. Establish `htnp : ∀ j, (∀ i, vF 𝔭 (a i) ≠ 0 → τ i ≠ j) → t j = 1`. Introduce `j hj`.

Establish `: ¬ ∃ i, vF 𝔭 (a i) ≠ 0 ∧ τ i = j` using `fun ⟨i, hi, e⟩ => hj i hi e`. Simplify using `only [t, dif_neg this]`. Set `h' : W →ₗ⋆[K] W →ₗ[K] K` to `(LinearMap.lcomp K K W.subtype).comp (h.comp W.subtype)`. Establish `h'a : ∀ x y : W, h' x y = h x y` using `fun x y => rfl`. Establish `hsym' : ∀ x y : W, star (h' x y) = h' y x`.

Introduce `x y`. Rewrite using `[h'a, h'a, ← starRingEnd_apply]`. Conclude with `hs.eq _ _`. Establish `hpos' : ∀ x : W, x ≠ 0 → TotPos (h' x x)`. Introduce `x hx φ`.

Rewrite using `[h'a]`. Conclude with `hpos x x.2 (fun e => hx (Subtype.ext e)) φ`. Establish `hm1 : m - 1 + 1 = m` using `by omega`. Take `⟨v, ho, hv1, hvl⟩` from `exists_presc_family hK h' hsym' hpos' (m - 1) (by omega) (fun j => t (Fin.cast hm1 j)) (fun j => hts _) (fun j => htp _)`. Set `w : Fin m → V` to `fun j => (v (Fin.cast hm1.symm j) : V)`.

Establish `hwo : ∀ j k, j ≠ k → h (w j) (w k) = 0`. Introduce `j k hjk`. Conclude with `ho _ _ (fun e => hjk (Fin.ext (by have := congrArg Fin.val e; simpa using this)))`. Establish `hwn : ∀ j : Fin m, (j : ℕ) + 1 < m → h (w j) (w j) = t j`. Introduce `j hj`.

Establish `hne' : Fin.cast hm1.symm j ≠ Fin.last (m - 1)`. Introduce `e`. Use `congrArg Fin.val e` as an intermediate fact. Simplify using `at this`. Use linear arithmetic over natural numbers and integers.

Use `hv1 _ hne'` as an intermediate fact. Simplify `this` using `[w, h'a]`. Establish `hwn0 : ∀ j, h (w j) (w j) ≠ 0`. Introduce `j`. Distinguish the cases in `hj : (j : ℕ) + 1 < m`.

Rewrite using `[hwn j hj]`. Conclude with `TotPos.ne_zero' (htp j)`. Establish `hjl` using `j.isLt`. Establish `hl : Fin.cast hm1.symm j = Fin.last (m - 1)` using `by ext; simp; omega`. Establish `: v (Fin.cast hm1.symm j) ≠ 0` using `by rw [hl]; exact hvl`.

Conclude with `TotPos.ne_zero' (hpos' _ this)`. Establish `hfix : ∀ j, ∃ x : F, h (w j) (w j) = algebraMap F K x` using `fun j => by`. Take `⟨x, hx⟩` from `(hF _).1 (by rw [← starRingEnd_apply]; exact hs.eq (w j) (w j))`. Conclude with `⟨x, hx.symm⟩`. Use `choose c hcw using hfix`.

Take `⟨π, s₀, hu⟩` from `exists_isUnif0 h𝔭`. Use `⟨π, w, c, τ, fun j => (v _).2, hwo, fun j => ⟨hcw j, fun h0 => hwn0 j (by rw [hcw j, h0, map_zero])⟩, hτ, ⟨s₀, hu⟩, ?_, hτl, ?_⟩` and prove the remaining obligations. Introduce `i hi`. Establish `e : algebraMap F K (c (τ i)) = algebraMap F K (nF i)`. Rewrite using `[← hcw, hwn _ (hτl i hi), htpart i hi]`.

Rewrite using `[(algebraMap F K).injective e]`. Conclude with `hncong i`. Introduce `j hj hnp`. Establish `e : c j = 1`. Apply `(algebraMap F K).injective` to reduce the goal to its premises.

Rewrite using `[← hcw, hwn j hj, htnp j hnp, map_one]`. Rewrite using `[e, inv_one, map_one]`. Conclude with `⟨(SP K 𝔭).one_mem, (SP K 𝔭).one_mem⟩`.
-/
theorem gluing_vectors_exist : GlueVecsPre := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hUc hpos hΛ₀ M hM hMi 𝔭 h𝔭 b a hba hc
  have := h𝔭.isPrime
  have hne : 𝔭 ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (RingOfIntegers.not_isField F)
  set W := orthK h U with hW
  set m := finrank K W with hm
  set P : Finset (Fin (finrank K U)) := Finset.univ.filter (fun i => vF 𝔭 (a i) ≠ 0) with hP
  have hPc : P.card < m := hc
  have hPm : ∀ i, (P.filter (· < i)).card < m := fun i =>
    lt_of_le_of_lt (Finset.card_filter_le _ _) hPc
  let τ : Fin (finrank K U) → Fin m := fun i => ⟨(P.filter (· < i)).card, hPm i⟩
  have hτ : ∀ i k, vF 𝔭 (a i) ≠ 0 → vF 𝔭 (a k) ≠ 0 → τ i = τ k → i = k := by
    intro i k hi hk e
    exact card_filter_lt_inj P (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)
      (Finset.mem_filter.2 ⟨Finset.mem_univ _, hk⟩) (congrArg Fin.val e)
  have hτl : ∀ i, vF 𝔭 (a i) ≠ 0 → (τ i : ℕ) + 1 < m := by
    intro i hi
    have := card_filter_lt_lt P (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)
    show (P.filter (· < i)).card + 1 < m
    omega
  choose nF hnpos hncong using fun i => exists_totPos_congr (K := K) h𝔭 hne (a i) (2 * vF 𝔭 (a i))
  let t : Fin m → K := fun j =>
    if hj : ∃ i, vF 𝔭 (a i) ≠ 0 ∧ τ i = j then algebraMap F K (nF hj.choose) else 1
  have hts : ∀ j, star (t j) = t j := by
    intro j; simp only [t]; split_ifs
    · exact star_fix hF _
    · exact star_one K
  have htp : ∀ j, TotPos (t j) := by
    intro j; simp only [t]; split_ifs
    · exact hnpos _
    · intro φ; rw [map_one]; simp
  have htpart : ∀ i, vF 𝔭 (a i) ≠ 0 → t (τ i) = algebraMap F K (nF i) := by
    intro i hi
    have hj : ∃ i', vF 𝔭 (a i') ≠ 0 ∧ τ i' = τ i := ⟨i, hi, rfl⟩
    simp only [t, dif_pos hj]
    rw [hτ _ _ hj.choose_spec.1 hi hj.choose_spec.2]
  have htnp : ∀ j, (∀ i, vF 𝔭 (a i) ≠ 0 → τ i ≠ j) → t j = 1 := by
    intro j hj
    have : ¬ ∃ i, vF 𝔭 (a i) ≠ 0 ∧ τ i = j := fun ⟨i, hi, e⟩ => hj i hi e
    simp only [t, dif_neg this]
  let h' : W →ₗ⋆[K] W →ₗ[K] K := (LinearMap.lcomp K K W.subtype).comp (h.comp W.subtype)
  have h'a : ∀ x y : W, h' x y = h x y := fun x y => rfl
  have hsym' : ∀ x y : W, star (h' x y) = h' y x := by
    intro x y; rw [h'a, h'a, ← starRingEnd_apply]; exact hs.eq _ _
  have hpos' : ∀ x : W, x ≠ 0 → TotPos (h' x x) := by
    intro x hx φ; rw [h'a]; exact hpos x x.2 (fun e => hx (Subtype.ext e)) φ
  have hm1 : m - 1 + 1 = m := by omega
  obtain ⟨v, ho, hv1, hvl⟩ := exists_presc_family hK h' hsym' hpos' (m - 1) (by omega)
    (fun j => t (Fin.cast hm1 j)) (fun j => hts _) (fun j => htp _)
  let w : Fin m → V := fun j => (v (Fin.cast hm1.symm j) : V)
  have hwo : ∀ j k, j ≠ k → h (w j) (w k) = 0 := by
    intro j k hjk
    exact ho _ _ (fun e => hjk (Fin.ext (by have := congrArg Fin.val e; simpa using this)))
  have hwn : ∀ j : Fin m, (j : ℕ) + 1 < m → h (w j) (w j) = t j := by
    intro j hj
    have hne' : Fin.cast hm1.symm j ≠ Fin.last (m - 1) := by
      intro e; have := congrArg Fin.val e; simp at this; omega
    have := hv1 _ hne'
    simpa [w, h'a] using this
  have hwn0 : ∀ j, h (w j) (w j) ≠ 0 := by
    intro j
    by_cases hj : (j : ℕ) + 1 < m
    · rw [hwn j hj]; exact TotPos.ne_zero' (htp j)
    · have hjl := j.isLt
      have hl : Fin.cast hm1.symm j = Fin.last (m - 1) := by
        ext; simp; omega
      have : v (Fin.cast hm1.symm j) ≠ 0 := by rw [hl]; exact hvl
      exact TotPos.ne_zero' (hpos' _ this)
  have hfix : ∀ j, ∃ x : F, h (w j) (w j) = algebraMap F K x := fun j => by
    obtain ⟨x, hx⟩ := (hF _).1 (by rw [← starRingEnd_apply]; exact hs.eq (w j) (w j))
    exact ⟨x, hx.symm⟩
  choose c hcw using hfix
  obtain ⟨π, s₀, hu⟩ := exists_isUnif0 h𝔭
  refine ⟨π, w, c, τ, fun j => (v _).2, hwo,
    fun j => ⟨hcw j, fun h0 => hwn0 j (by rw [hcw j, h0, map_zero])⟩, hτ, ⟨s₀, hu⟩, ?_, hτl, ?_⟩
  · intro i hi
    have e : algebraMap F K (c (τ i)) = algebraMap F K (nF i) := by
      rw [← hcw, hwn _ (hτl i hi), htpart i hi]
    rw [(algebraMap F K).injective e]
    exact hncong i
  · intro j hj hnp
    have e : c j = 1 := by
      apply (algebraMap F K).injective
      rw [← hcw, hwn j hj, htnp j hnp, map_one]
    rw [e, inv_one, map_one]
    exact ⟨(SP K 𝔭).one_mem, (SP K 𝔭).one_mem⟩

end Formalism.L2.SG.Pf.GluingBases
