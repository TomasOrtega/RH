import Mathlib
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ExistsHasLeadingCoeffOfMemSpanBelow
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.HermitianLatticeCounting.P
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt.RatNormal

section
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ}

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨b, hb, rfl⟩`. Establish `h1 : f b.castSucc - F.e b.castSucc ∈ F.Xa n` using `Xa_mono F (le_of_lt hb) (hf b.castSucc)`. Simplify using `using Submodule.add_mem _ h1 (e_mem_Xa F b hb)`.

Proceed by induction on `n with`. Consider the case `zero => rw [Xa_zero]`. Conclude with `bot_le`. Consider the case `succ n ih`. Establish `hm : Submodule.span K ((fun b : Fin r => f b.castSucc) '' {b | b.val < n}) ≤ Submodule.span K ((fun b : Fin r => f b.castSucc) '' {b | b.val < n + 1})` using `Submodule.span_mono (Set.image_mono fun b (hb : b.val < n) => Nat.lt_succ_of_lt hb)`.

Rewrite using `[FlagD.Xa, Submodule.span_le]`. Introduce and unpack `_ ⟨b, hb, rfl⟩`. Establish `hb' : b.val ≤ n` using `Nat.lt_succ_iff.mp hb`. Establish `h1` using `hm (ih (Xa_mono F hb' (hf b.castSucc)))`. Establish `h2 : f b.castSucc ∈ Submodule.span K ((fun b : Fin r => f b.castSucc) '' {b | b.val < n + 1})` using `Submodule.subset_span ⟨b, hb, rfl⟩`.

Simplify using `using Submodule.sub_mem _ h2 h1`.
-/
theorem span_change (F : FlagD H r) (f : Fin (r + 1) → V) (hf : ∀ a, f a - F.e a ∈ F.Xa a.val) (n : ℕ) :
    Submodule.span K ((fun b : Fin r => f b.castSucc) '' {b | b.val < n}) = F.Xa n := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨b, hb, rfl⟩
    have h1 : f b.castSucc - F.e b.castSucc ∈ F.Xa n := Xa_mono F (le_of_lt hb) (hf b.castSucc)
    simpa using Submodule.add_mem _ h1 (e_mem_Xa F b hb)
  · induction n with
    | zero => rw [Xa_zero]; exact bot_le
    | succ n ih =>
      have hm : Submodule.span K ((fun b : Fin r => f b.castSucc) '' {b | b.val < n}) ≤
          Submodule.span K ((fun b : Fin r => f b.castSucc) '' {b | b.val < n + 1}) :=
        Submodule.span_mono (Set.image_mono fun b (hb : b.val < n) => Nat.lt_succ_of_lt hb)
      rw [FlagD.Xa, Submodule.span_le]
      rintro _ ⟨b, hb, rfl⟩
      have hb' : b.val ≤ n := Nat.lt_succ_iff.mp hb
      have h1 := hm (ih (Xa_mono F hb' (hf b.castSucc)))
      have h2 : f b.castSucc ∈ Submodule.span K ((fun b : Fin r => f b.castSucc) '' {b | b.val < n + 1}) :=
        Submodule.subset_span ⟨b, hb, rfl⟩
      simpa using Submodule.sub_mem _ h2 h1

/- English proof (translation)
Establish `hX : ∀ a : Fin r, f a.castSucc ∈ F.X` using `fun a => by`. Simplify using `using Submodule.add_mem _ (Xa_le_X F _ (hf a.castSucc)) (e_mem_X F a)`. Take `⟨x, hx, hz⟩ : ∃ x ∈ F.X, f (Fin.last r) = F.z + x` from `⟨_, Xa_le_X F _ (hf (Fin.last r)), by simp [FlagD.z]⟩`. Use `⟨⟨f, F.T, ?_, fun a b => X_iso F (hX a) (hX b), fun a => ?_, ?_, F.hT⟩, rfl, rfl, fun n => span_change F f hf n⟩` and prove the remaining obligations. Rewrite using `[linearIndependent_iff_card_eq_finrank_span]`.

Establish `h` using `span_change F f hf r`. Establish `h2 : {b : Fin r | b.val < r} = Set.univ` using `Set.eq_univ_of_forall fun b => b.isLt`. Rewrite `h` using `[h2, Set.image_univ]`. Rewrite using `[Set.finrank, h, Fintype.card_fin]`. Conclude with `(finrank_X F).symm`.

Rewrite using `[hz, map_add, pairing_isotropicSpan_lastVector F (hX a), X_iso F (hX a) hx, add_zero]`. Rewrite using `[hz]`. Simplify using `only [map_add, LinearMap.add_apply, pairing_lastVector_lastVector, pairing_isotropicSpan_lastVector F hx, z_X F hx, X_iso F hx hx, add_zero]`.
-/
theorem exists_reframe (F : FlagD H r) (f : Fin (r + 1) → V) (hf : ∀ a, f a - F.e a ∈ F.Xa a.val) :
    ∃ G : FlagD H r, G.e = f ∧ G.T = F.T ∧ ∀ n, G.Xa n = F.Xa n := by
  have hX : ∀ a : Fin r, f a.castSucc ∈ F.X := fun a => by
    simpa using Submodule.add_mem _ (Xa_le_X F _ (hf a.castSucc)) (e_mem_X F a)
  obtain ⟨x, hx, hz⟩ : ∃ x ∈ F.X, f (Fin.last r) = F.z + x :=
    ⟨_, Xa_le_X F _ (hf (Fin.last r)), by simp [FlagD.z]⟩
  refine ⟨⟨f, F.T, ?_, fun a b => X_iso F (hX a) (hX b), fun a => ?_, ?_, F.hT⟩, rfl, rfl,
    fun n => span_change F f hf n⟩
  · rw [linearIndependent_iff_card_eq_finrank_span]
    have h := span_change F f hf r
    have h2 : {b : Fin r | b.val < r} = Set.univ := Set.eq_univ_of_forall fun b => b.isLt
    rw [h2, Set.image_univ] at h
    rw [Set.finrank, h, Fintype.card_fin]
    exact (finrank_X F).symm
  · rw [hz, map_add, pairing_isotropicSpan_lastVector F (hX a), X_iso F (hX a) hx, add_zero]
  · rw [hz]
    simp only [map_add, LinearMap.add_apply, pairing_lastVector_lastVector, pairing_isotropicSpan_lastVector F hx, z_X F hx, X_iso F hx hx, add_zero]

omit [StarRing K] in

/- English proof (translation)
Establish `hT : A.BlockTriangular OrderDual.toDual` using `fun a b hab => h0 a b hab`. Establish `hd : A.det = 1` using `by rw [Matrix.det_of_lowerTriangular A hT]; simp [h1]`. Establish `hu : IsUnit A.det` using `by rw [hd]; exact isUnit_one`. Use `letI := A.invertibleOfIsUnitDet hu`. Establish `hM` using `Matrix.blockTriangular_inv_of_blockTriangular hT`.

Establish `hM0 : ∀ a b, a < b → A⁻¹ a b = 0` using `fun a b hab => hM hab`. Establish `hI` using `Matrix.nonsing_inv_mul A hu`. Use `⟨A⁻¹, hI, hM0, fun a => ?_⟩` and prove the remaining obligations. Establish `h` using `congrFun (congrFun hI a) a`. Rewrite `h` using `[Matrix.mul_apply, Finset.sum_eq_single a, h1, mul_one, Matrix.one_apply_eq]`.

Conclude with `h`. Introduce `b _ hb`. Break down `lt_or_gt_of_ne hb with hb | hb` into its components or cases. Rewrite using `[h0 b a hb, mul_zero]`. Rewrite using `[hM0 a b hb, zero_mul]`.

Simplify using the standard rewrite rules.
-/
theorem exists_inv_lower {j : ℕ} (A : Matrix (Fin j) (Fin j) K) (h0 : ∀ a b, a < b → A a b = 0)
    (h1 : ∀ a, A a a = 1) :
    ∃ M : Matrix (Fin j) (Fin j) K, M * A = 1 ∧ (∀ a b, a < b → M a b = 0) ∧ ∀ a, M a a = 1 := by
  have hT : A.BlockTriangular OrderDual.toDual := fun a b hab => h0 a b hab
  have hd : A.det = 1 := by rw [Matrix.det_of_lowerTriangular A hT]; simp [h1]
  have hu : IsUnit A.det := by rw [hd]; exact isUnit_one
  letI := A.invertibleOfIsUnitDet hu
  have hM := Matrix.blockTriangular_inv_of_blockTriangular hT
  have hM0 : ∀ a b, a < b → A⁻¹ a b = 0 := fun a b hab => hM hab
  have hI := Matrix.nonsing_inv_mul A hu
  refine ⟨A⁻¹, hI, hM0, fun a => ?_⟩
  have h := congrFun (congrFun hI a) a
  rw [Matrix.mul_apply, Finset.sum_eq_single a, h1, mul_one, Matrix.one_apply_eq] at h
  · exact h
  · intro b _ hb
    rcases lt_or_gt_of_ne hb with hb | hb
    · rw [h0 b a hb, mul_zero]
    · rw [hM0 a b hb, zero_mul]
  · simp

/- English proof (translation)
Rewrite using `[← Finset.add_sum_erase _ _ (Finset.mem_univ a), h1, one_smul, add_sub_cancel_left]`. Use `Submodule.sum_mem _ fun b hb => ?_` and prove the remaining obligations. Break down `lt_or_gt_of_ne (Finset.ne_of_mem_erase hb) with hb | hb` into its components or cases. Conclude with `Submodule.smul_mem _ _ (e_mem_Xa F (Fin.castLE hj b) hb)`. Rewrite using `[h0 a b hb, zero_smul]`.

Conclude with `Submodule.zero_mem _`.
-/
theorem comb_sub_mem (F : FlagD H r) {j : ℕ} (hj : j ≤ r) (M : Matrix (Fin j) (Fin j) K)
    (h0 : ∀ a b, a < b → M a b = 0) (h1 : ∀ a, M a a = 1) (a : Fin j) :
    ∑ b, M a b • F.e (Fin.castLE (hj.trans (Nat.le_succ r)) b) - F.e (Fin.castLE (hj.trans (Nat.le_succ r)) a) ∈
      F.Xa a.val := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), h1, one_smul, add_sub_cancel_left]
  refine Submodule.sum_mem _ fun b hb => ?_
  rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hb) with hb | hb
  · exact Submodule.smul_mem _ _ (e_mem_Xa F (Fin.castLE hj b) hb)
  · rw [h0 a b hb, zero_smul]; exact Submodule.zero_mem _

/- English proof (translation)
Take `⟨x, hx, h⟩` from `Dl_solveL F F' hj hD (fun b => H.B y (F'.e (Fin.castLE (hj.trans (Nat.le_succ r)) b)))`. Use `⟨x, hx, perp_Xa F' fun b hb => B_swap0 H ?_⟩` and prove the remaining obligations. Use `h ⟨b.val, hb⟩` as an intermediate fact. Rewrite using `[map_sub, LinearMap.sub_apply, sub_eq_zero]`. Conclude with `this.symm`.
-/
theorem exists_perp (F F' : FlagD H r) {j : ℕ} (hj : j ≤ r) (hD : Dl F F' j (hj.trans (Nat.le_succ r)) ≠ 0) (y : V) :
    ∃ x ∈ F.Xa j, ∀ u ∈ F'.Xa j, H.B u (y - x) = 0 := by
  obtain ⟨x, hx, h⟩ := Dl_solveL F F' hj hD (fun b => H.B y (F'.e (Fin.castLE (hj.trans (Nat.le_succ r)) b)))
  refine ⟨x, hx, perp_Xa F' fun b hb => B_swap0 H ?_⟩
  have := h ⟨b.val, hb⟩
  rw [map_sub, LinearMap.sub_apply, sub_eq_zero]
  exact this.symm

/- English proof (translation)
Take `⟨hc, -, h3, h4, -, -, hX, -, hz⟩` from `hS`. Proceed by induction on `a using Fin.lastCases with`. Consider the case `last`. Take `⟨x, hx, hp⟩` from `exists_perp F F' hj hD F.z`. Use `⟨F.z - x, ?_, ?_⟩` and prove the remaining obligations.

Establish `: F.z - x - F.e (Fin.last r) = -x` using `by simp [FlagD.z]`. Rewrite using `[this]`. Conclude with `Submodule.neg_mem _ (Xa_le_X F _ hx)`. Take `⟨x1, hx1, x', hx', hs⟩` from `Submodule.mem_sup.mp hz`. Rewrite `hx1` using `[hX]`.

Take `⟨x2, hx2, i, hi, rfl⟩` from `Submodule.mem_sup.mp hx1`. Establish `hv : i + x' ∈ F'.X` using `Submodule.add_mem _ hi.2 hx'`. Establish `he : x2 + c • x = F'.z - c • (F.z - x) - (i + x')`. Rewrite using `[smul_sub, ← sub_add, ← hs]`. Normalize the expressions using the abelian group laws.

Establish `h0 : x2 + c • x = 0`. Use `Dl_injL F F' hj hD (Submodule.add_mem _ hx2 (Submodule.smul_mem _ _ hx)) fun u hu => B_swap0 H ?_` and prove the remaining obligations. Establish `hu'` using `Xa_le_X F' _ hu`. Rewrite using `[he, map_sub, map_sub, map_smulₛₗ, hp u hu, pairing_isotropicSpan_lastVector F' hu', X_iso F' hu' hv]`. Simplify using the standard rewrite rules.

Rewrite `he` using `[h0]`. Establish `: c • (F.z - x) - F'.e (Fin.last r) = -(i + x')`. Rewrite using `[← sub_eq_zero.mp he.symm]`. Simplify using `[FlagD.z]`. Rewrite using `[this]`.

Conclude with `Submodule.neg_mem _ hv`. Consider the case `cast a`. Take `⟨x, hx, al, al', hl, hl'⟩` from `h4 a ha`. Take `⟨b, bl, bl', hb, hb', -, hbc⟩` from `h3 x hx (level_ne_zero F hl)`. Take `⟨-, rfl⟩` from `level_unique F hl hb`.

Take `⟨-, rfl⟩` from `level_unique F' hl' hb'`. Use `⟨al⁻¹ • x, ?_, ?_⟩` and prove the remaining obligations. Use `Submodule.smul_mem _ al⁻¹ hl.2` as an intermediate fact. Rewrite `this` using `[smul_sub, smul_smul, inv_mul_cancel₀ hl.1, one_smul]`. Then use the resulting hypothesis. Use `Submodule.smul_mem _ al'⁻¹ hl'.2` as an intermediate fact.

Rewrite `this` using `[smul_sub, smul_smul, inv_mul_cancel₀ hl'.1, one_smul]`. Establish `h2 : c * al⁻¹ = al'⁻¹` using `by rw [hbc]; field_simp`. Rewrite using `[smul_smul, h2]` and apply the resulting hypothesis.
-/
theorem exists_common (F F' : FlagD H r) {j : ℕ} (hj : j ≤ r) {c : K} (hS : NFShape F F' j c)
    (hD : Dl F F' j (hj.trans (Nat.le_succ r)) ≠ 0) (a : Fin (r + 1)) (ha : j ≤ a.val) :
    ∃ y, y - F.e a ∈ F.Xa a.val ∧ c • y - F'.e a ∈ F'.Xa a.val := by
  obtain ⟨hc, -, h3, h4, -, -, hX, -, hz⟩ := hS
  induction a using Fin.lastCases with
  | last =>
    obtain ⟨x, hx, hp⟩ := exists_perp F F' hj hD F.z
    refine ⟨F.z - x, ?_, ?_⟩
    · have : F.z - x - F.e (Fin.last r) = -x := by simp [FlagD.z]
      rw [this]
      exact Submodule.neg_mem _ (Xa_le_X F _ hx)
    · obtain ⟨x1, hx1, x', hx', hs⟩ := Submodule.mem_sup.mp hz
      rw [hX] at hx1
      obtain ⟨x2, hx2, i, hi, rfl⟩ := Submodule.mem_sup.mp hx1
      have hv : i + x' ∈ F'.X := Submodule.add_mem _ hi.2 hx'
      have he : x2 + c • x = F'.z - c • (F.z - x) - (i + x') := by
        rw [smul_sub, ← sub_add, ← hs]; abel
      have h0 : x2 + c • x = 0 := by
        refine Dl_injL F F' hj hD (Submodule.add_mem _ hx2 (Submodule.smul_mem _ _ hx)) fun u hu => B_swap0 H ?_
        have hu' := Xa_le_X F' _ hu
        rw [he, map_sub, map_sub, map_smulₛₗ, hp u hu, pairing_isotropicSpan_lastVector F' hu', X_iso F' hu' hv]
        simp
      rw [h0] at he
      have : c • (F.z - x) - F'.e (Fin.last r) = -(i + x') := by
        rw [← sub_eq_zero.mp he.symm]; simp [FlagD.z]
      rw [this]
      exact Submodule.neg_mem _ hv
  | cast a =>
    obtain ⟨x, hx, al, al', hl, hl'⟩ := h4 a ha
    obtain ⟨b, bl, bl', hb, hb', -, hbc⟩ := h3 x hx (level_ne_zero F hl)
    obtain ⟨-, rfl⟩ := level_unique F hl hb
    obtain ⟨-, rfl⟩ := level_unique F' hl' hb'
    refine ⟨al⁻¹ • x, ?_, ?_⟩
    · have := Submodule.smul_mem _ al⁻¹ hl.2
      rwa [smul_sub, smul_smul, inv_mul_cancel₀ hl.1, one_smul] at this
    · have := Submodule.smul_mem _ al'⁻¹ hl'.2
      rw [smul_sub, smul_smul, inv_mul_cancel₀ hl'.1, one_smul] at this
      have h2 : c * al⁻¹ = al'⁻¹ := by rw [hbc]; field_simp
      rwa [smul_smul, h2]

/- English proof (translation)
Establish `hn : G.e b.castSucc ∉ Submodule.span K ((fun a : Fin r => G.e a.castSucc) '' {b}ᶜ)` using `G.indep.notMem_span_image (by simp)`. Establish `h` using `mt (memOfOrthogonalOrthogonal K V H _ (G.e b.castSucc)) hn`. Use `push_neg at h`. Take `⟨v, hv, hb⟩` from `h`. Use `⟨star (H.B (G.e b.castSucc) v)⁻¹ • v, fun a => ?_⟩` and prove the remaining obligations.

Rewrite using `[map_smulₛₗ]`. Use `split_ifs with hab`. Substitute `hab` using the available equality. Rewrite using `[starRingEnd_apply, star_star, smul_eq_mul, inv_mul_cancel₀ hb]`. Rewrite using `[hv _ (Submodule.subset_span ⟨a, hab, rfl⟩)]`.

Simplify using the standard rewrite rules.
-/
theorem exists_dual [FiniteDimensional K V] (G : FlagD H r) (b : Fin r) :
    ∃ y, ∀ a : Fin r, H.B (G.e a.castSucc) y = if a = b then 1 else 0 := by
  have hn : G.e b.castSucc ∉ Submodule.span K ((fun a : Fin r => G.e a.castSucc) '' {b}ᶜ) :=
    G.indep.notMem_span_image (by simp)
  have h := mt (memOfOrthogonalOrthogonal K V H _ (G.e b.castSucc)) hn
  push_neg at h
  obtain ⟨v, hv, hb⟩ := h
  refine ⟨star (H.B (G.e b.castSucc) v)⁻¹ • v, fun a => ?_⟩
  rw [map_smulₛₗ]
  split_ifs with hab
  · subst hab
    rw [starRingEnd_apply, star_star, smul_eq_mul, inv_mul_cancel₀ hb]
  · rw [hv _ (Submodule.subset_span ⟨a, hab, rfl⟩)]; simp

/- English proof (translation)
Establish `hp : ∀ a : Fin (r + 1), j ≤ a.val → ∀ u ∈ G'.Xa j, H.B u (G.e a) = 0` using `fun a ha u hu => by`. Establish `h` using `e_X G' a (Xa_le_X G' _ hu)`. Rewrite `h` using `[same a ha, map_smul, LinearMap.smul_apply, smul_eq_mul]`. Conclude with `B_swap0 H ((mul_eq_zero.mp h).resolve_left hc)`. Establish `h1 : ∀ b : Fin r, ∃ y, (∀ a : Fin r, H.B (G.e a.castSucc) y = if a = b then 1 else 0) ∧ (∀ u ∈ G'.Xa j, H.B u y = 0) ∧ H.B G.z y = 0` using `fun b => by`.

Take `⟨y, hy⟩` from `exists_dual G b`. Take `⟨x, hx, hxp⟩` from `hs y`. Use `⟨y - x + star (H.B G.z (y - x) / G.T) • G.z, fun a => ?_, fun u hu => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_sub, map_smulₛₗ, hy, e_X G _ hx, pairing_isotropicSpan_lastVector G (e_mem_X G a)]`. Simplify using the standard rewrite rules.

Use `hp (Fin.last r) hj u hu` as an intermediate fact. Rewrite using `[map_add, hxp u hu, map_smulₛₗ, FlagD.z, this]`. Simplify using the standard rewrite rules. Rewrite using `[map_add, map_smulₛₗ, pairing_lastVector_lastVector]`. Use `G.hT` as an intermediate fact.

Simplify using `only [starRingEnd_apply, star_star, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Use `choose y hy1 hy2 hy3 using h1`. Take `⟨s, hsd⟩ : ∃ s : Fin r → V, ∀ b, s b = ∑ a ∈ Finset.univ.filter (fun a : Fin r => j ≤ a.val), (H.B (y b) (y a) / 2) • G.e a.castSucc` from `⟨_, fun _ => rfl⟩`.

Establish `hsX : ∀ b, s b ∈ G.X` using `fun b => by`. Rewrite using `[hsd]`. Conclude with `Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (e_mem_X G a)`. Establish `hsy : ∀ a b : Fin r, j ≤ b.val → H.B (s a) (y b) = H.B (y a) (y b) / 2` using `fun a b hb => by`. Rewrite using `[hsd, map_sum, LinearMap.sum_apply]`.

Simplify using `[hy1, hb]`. Use `⟨fun b => y b - s b, fun a b => ?_, fun b u hu => ?_, fun b => ?_, fun a b ha hb => ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, hy1, e_X G _ (hsX b), sub_zero]`. Rewrite using `[map_sub, hy2 b u hu, hsd, map_sum, Finset.sum_eq_zero, sub_zero]`. Introduce `a ha`.

Rewrite using `[map_smulₛₗ, hp a.castSucc (Finset.mem_filter.mp ha).2 u hu, smul_zero]`. Rewrite using `[map_sub, hy3, z_X G (hsX b), sub_zero]`. Establish `h2 : H.B (y a) (s b) = H.B (y a) (y b) / 2`. Rewrite using `[← H.herm (s b), hsy b a ha, star_div₀, H.herm]`. Simplify using the standard rewrite rules.

Simplify using `only [map_sub, LinearMap.sub_apply, h2, hsy a b hb, X_iso G (hsX a) (hsX b)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_ist [FiniteDimensional K V] [CharZero K] (G G' : FlagD H r) {j : ℕ} (hj : j ≤ r) {c : K} (hc : c ≠ 0)
    (same : ∀ a : Fin (r + 1), j ≤ a.val → G'.e a = c • G.e a)
    (hs : ∀ y, ∃ x ∈ G.X, ∀ u ∈ G'.Xa j, H.B u (y - x) = 0) :
    ∃ ist : Fin r → V, (∀ a b : Fin r, H.B (G.e a.castSucc) (ist b) = if a = b then 1 else 0) ∧
      (∀ b, ∀ u ∈ G'.Xa j, H.B u (ist b) = 0) ∧ (∀ b, H.B G.z (ist b) = 0) ∧
      ∀ a b : Fin r, j ≤ a.val → j ≤ b.val → H.B (ist a) (ist b) = 0 := by
  have hp : ∀ a : Fin (r + 1), j ≤ a.val → ∀ u ∈ G'.Xa j, H.B u (G.e a) = 0 := fun a ha u hu => by
    have h := e_X G' a (Xa_le_X G' _ hu)
    rw [same a ha, map_smul, LinearMap.smul_apply, smul_eq_mul] at h
    exact B_swap0 H ((mul_eq_zero.mp h).resolve_left hc)
  have h1 : ∀ b : Fin r, ∃ y, (∀ a : Fin r, H.B (G.e a.castSucc) y = if a = b then 1 else 0) ∧
      (∀ u ∈ G'.Xa j, H.B u y = 0) ∧ H.B G.z y = 0 := fun b => by
    obtain ⟨y, hy⟩ := exists_dual G b
    obtain ⟨x, hx, hxp⟩ := hs y
    refine ⟨y - x + star (H.B G.z (y - x) / G.T) • G.z, fun a => ?_, fun u hu => ?_, ?_⟩
    · rw [map_add, map_sub, map_smulₛₗ, hy, e_X G _ hx, pairing_isotropicSpan_lastVector G (e_mem_X G a)]; simp
    · have := hp (Fin.last r) hj u hu
      rw [map_add, hxp u hu, map_smulₛₗ, FlagD.z, this]; simp
    · rw [map_add, map_smulₛₗ, pairing_lastVector_lastVector]
      have := G.hT
      simp only [starRingEnd_apply, star_star, smul_eq_mul]
      field_simp
      ring
  choose y hy1 hy2 hy3 using h1
  obtain ⟨s, hsd⟩ : ∃ s : Fin r → V, ∀ b, s b = ∑ a ∈ Finset.univ.filter (fun a : Fin r => j ≤ a.val),
      (H.B (y b) (y a) / 2) • G.e a.castSucc := ⟨_, fun _ => rfl⟩
  have hsX : ∀ b, s b ∈ G.X := fun b => by
    rw [hsd]; exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (e_mem_X G a)
  have hsy : ∀ a b : Fin r, j ≤ b.val → H.B (s a) (y b) = H.B (y a) (y b) / 2 := fun a b hb => by
    rw [hsd, map_sum, LinearMap.sum_apply]
    simp [hy1, hb]
  refine ⟨fun b => y b - s b, fun a b => ?_, fun b u hu => ?_, fun b => ?_, fun a b ha hb => ?_⟩
  · rw [map_sub, hy1, e_X G _ (hsX b), sub_zero]
  · rw [map_sub, hy2 b u hu, hsd, map_sum, Finset.sum_eq_zero, sub_zero]
    intro a ha
    rw [map_smulₛₗ, hp a.castSucc (Finset.mem_filter.mp ha).2 u hu, smul_zero]
  · rw [map_sub, hy3, z_X G (hsX b), sub_zero]
  · have h2 : H.B (y a) (s b) = H.B (y a) (y b) / 2 := by
      rw [← H.herm (s b), hsy b a ha, star_div₀, H.herm]; simp
    simp only [map_sub, LinearMap.sub_apply, h2, hsy a b hb, X_iso G (hsX a) (hsX b)]
    ring

end

/- English proof (translation)
Introduce `K V _ _ _ _ _ _ _ _ H _ r F F' j hj c T 𝔡 w sgn A B hNF hT hT' hpos h𝔡 h𝔡s h0 h1 hZ`. Take `⟨hS, hcn, hD, -⟩` from `hNF`. Take `⟨M, hM, hM0, hM1⟩` from `exists_inv_lower A (fun a b h => (h0 a b h).1) fun a => (h1 a).1`. Take `⟨M', hM', hM0', hM1'⟩` from `exists_inv_lower B.transpose (fun a b h => (h0 a b h).2) fun a => (h1 a).2`. Use `choose y hy hy' using exists_common F F' hj hS hD`.

Take `⟨f, hf⟩ : ∃ f : Fin (r + 1) → V, ∀ a, f a = if h : a.val < j then ∑ b, M ⟨a.val, h⟩ b • F.e (Fin.castLE (hj.trans (Nat.le_succ r)) b) else y a (not_lt.mp h)` from `⟨_, fun _ => rfl⟩`. Take `⟨f', hf'⟩ : ∃ f' : Fin (r + 1) → V, ∀ a, f' a = if h : a.val < j then ∑ b, (M'.map star) ⟨a.val, h⟩ b • F'.e (Fin.castLE (hj.trans (Nat.le_succ r)) b) else c • y a (not_lt.mp h)` from `⟨_, fun _ => rfl⟩`. Establish `hF : ∀ a, f a - F.e a ∈ F.Xa a.val` using `fun a => by`. Rewrite using `[hf]`. Use `split_ifs with h`.

Conclude with `comb_sub_mem F hj M hM0 hM1 ⟨a.val, h⟩`. Conclude with `hy a _`. Establish `hF' : ∀ a, f' a - F'.e a ∈ F'.Xa a.val` using `fun a => by`. Rewrite using `[hf']`. Use `split_ifs with h`.

Conclude with `comb_sub_mem F' hj (M'.map star) (fun a b h => by simp [hM0' a b h]) (fun a => by simp [hM1' a]) ⟨a.val, h⟩`. Conclude with `hy' a _`. Take `⟨G, hG, hGT, hGX⟩` from `exists_reframe F f hF`. Take `⟨G', hG', hGT', hGX'⟩` from `exists_reframe F' f' hF'`. Establish `same : ∀ a : Fin (r + 1), j ≤ a.val → G'.e a = c • G.e a` using `fun a ha => by`.

Rewrite using `[hG, hG', hf, hf', dif_neg (not_lt.mpr ha), dif_neg (not_lt.mpr ha)]`. Take `⟨ist, i1, i2, i3, i4⟩` from `exists_ist G G' hj hS.1 same fun v => by`. Take `⟨x, hx, hp⟩` from `exists_perp F F' hj hD v`. Conclude with `⟨x, Xa_le_X G j (by rwa [hGX]), fun u hu => hp u (by rwa [← hGX'])⟩`. Establish `hcn' : c * star c = 1`.

Rewrite `hcn` using `[hT', ← hT]`. Conclude with `mul_right_cancel₀ F.hT (by rw [hcn, one_mul])`. Establish `hBM : B * M'.transpose = 1`. Use `congrArg Matrix.transpose hM'` as an intermediate fact. Rewrite `this` using `[Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one]`. Then use the resulting hypothesis.

Establish `hW : M * (Zhat F F').submatrix (Fin.castLE (hj.trans (Nat.le_succ r))) (Fin.castLE (hj.trans (Nat.le_succ r))) * M'.transpose = Matrix.of fun a b => w.mat a b * ((sgn b : ℤ) : K)`. Rewrite using `[hZ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hM, Matrix.one_mul, Matrix.mul_assoc, hBM, Matrix.mul_one]`. Establish `pair : ∀ a b : Fin j, H.B (G.e (Fin.castLE (hj.trans (Nat.le_succ r)) a)) (G'.e (Fin.castLE (hj.trans (Nat.le_succ r)) b)) = w.mat a b * ((sgn b : ℤ) : K)` using `fun a b => by`. Establish `h` using `congrFun (congrFun hW a) b`. Rewrite `h` using `[Matrix.of_apply]`.

Rewrite using `[← h, hG, hG', hf, hf', dif_pos (show (Fin.castLE (hj.trans (Nat.le_succ r)) a).val < j from a.isLt), dif_pos (show (Fin.castLE (hj.trans (Nat.le_succ r)) b).val < j from b.isLt), map_sum, Matrix.mul_apply]`. Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Rewrite using `[map_smulₛₗ, B_sum_left, Matrix.mul_apply]`. Rewrite using `[starRingEnd_apply, Matrix.map_apply, star_star, smul_eq_mul, mul_comm]`. Both sides reduce to the same expression.

Establish `posdef : ∀ σ : K →+* ℂ, G.PosDefAt σ` using `fun σ v hv hvX => by`. Establish `hXX : G.X = F.X` using `hGX r`. Use `hpos σ v (fun a => ?_) (by rwa [← hXX])` and prove the remaining obligations. Establish `h2 : H.B (f a - F.e a) v = 0` using `perp_X G (fun b => hv b.castSucc) _ (by rw [hXX]; exact Xa_le_X F _ (hF a))`. Establish `h3` using `hv a`.

Rewrite `h3` using `[hG]`. Rewrite `h2` using `[map_sub, LinearMap.sub_apply, h3, zero_sub, neg_eq_zero]`. Then use the resulting hypothesis. Use `⟨⟨G, G', j, hj, c, hcn', T, hGT.trans hT, hGT'.trans hT', same, w, sgn, pair, ist, fun a b _ => i1 a b, fun a b ha _ => i2 b _ (e_mem_Xa G' a ha), fun b _ => i3 b, i4, posdef, 𝔡, h𝔡, h𝔡s⟩, rfl, rfl, rfl, rfl, ?_, ?_⟩` and prove the remaining obligations. Introduce `a`. Use `show G.e a - _ ∈ _`.

Rewrite using `[hG]`. Conclude with `hF a`. Introduce `a`. Use `show G'.e a - _ ∈ _`. Rewrite using `[hG']`.

Conclude with `hF' a`.
-/
theorem exists_nf : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (F F' : FlagD H r) (j : ℕ) (hj : j ≤ r) (c : K) (T : ℕ) (𝔡 : Ideal (𝓞 K)) (w : Formalism.MainNotions.S.Loc.Pt K j) (sgn : Fin j → ℤˣ) (A B : Matrix (Fin j) (Fin j) K), NFFull F F' j hj c → F.T = T → F'.T = T → (∀ σ : K →+* ℂ, F.PosDefAt σ) → 𝔡 ≠ ⊥ → (∀ x ∈ 𝔡, ∃ y ∈ 𝔡, (y : K) = star (x : K)) → (∀ a b, a < b → A a b = 0 ∧ B b a = 0) → (∀ a, A a a = 1 ∧ B a a = 1) → ((Zhat F F').submatrix (Fin.castLE (hj.trans (Nat.le_succ r))) (Fin.castLE (hj.trans (Nat.le_succ r))) = A * (Matrix.of fun a b => w.mat a b * ((sgn b : ℤ) : K)) * B) → ∃ N : NF H r, N.j = j ∧ N.c = c ∧ N.T = T ∧ N.𝔡 = 𝔡 ∧ (∀ a, N.F.e a - F.e a ∈ F.Xa a.val) ∧ ∀ a, N.F'.e a - F'.e a ∈ F'.Xa a.val := by
  intro K V _ _ _ _ _ _ _ _ H _ r F F' j hj c T 𝔡 w sgn A B hNF hT hT' hpos h𝔡 h𝔡s h0 h1 hZ
  obtain ⟨hS, hcn, hD, -⟩ := hNF
  obtain ⟨M, hM, hM0, hM1⟩ := exists_inv_lower A (fun a b h => (h0 a b h).1) fun a => (h1 a).1
  obtain ⟨M', hM', hM0', hM1'⟩ := exists_inv_lower B.transpose (fun a b h => (h0 a b h).2) fun a => (h1 a).2
  choose y hy hy' using exists_common F F' hj hS hD
  obtain ⟨f, hf⟩ : ∃ f : Fin (r + 1) → V, ∀ a, f a = if h : a.val < j then
      ∑ b, M ⟨a.val, h⟩ b • F.e (Fin.castLE (hj.trans (Nat.le_succ r)) b) else y a (not_lt.mp h) := ⟨_, fun _ => rfl⟩
  obtain ⟨f', hf'⟩ : ∃ f' : Fin (r + 1) → V, ∀ a, f' a = if h : a.val < j then
      ∑ b, (M'.map star) ⟨a.val, h⟩ b • F'.e (Fin.castLE (hj.trans (Nat.le_succ r)) b)
      else c • y a (not_lt.mp h) := ⟨_, fun _ => rfl⟩
  have hF : ∀ a, f a - F.e a ∈ F.Xa a.val := fun a => by
    rw [hf]
    split_ifs with h
    · exact comb_sub_mem F hj M hM0 hM1 ⟨a.val, h⟩
    · exact hy a _
  have hF' : ∀ a, f' a - F'.e a ∈ F'.Xa a.val := fun a => by
    rw [hf']
    split_ifs with h
    · exact comb_sub_mem F' hj (M'.map star) (fun a b h => by simp [hM0' a b h]) (fun a => by simp [hM1' a]) ⟨a.val, h⟩
    · exact hy' a _
  obtain ⟨G, hG, hGT, hGX⟩ := exists_reframe F f hF
  obtain ⟨G', hG', hGT', hGX'⟩ := exists_reframe F' f' hF'
  have same : ∀ a : Fin (r + 1), j ≤ a.val → G'.e a = c • G.e a := fun a ha => by
    rw [hG, hG', hf, hf', dif_neg (not_lt.mpr ha), dif_neg (not_lt.mpr ha)]
  obtain ⟨ist, i1, i2, i3, i4⟩ := exists_ist G G' hj hS.1 same fun v => by
    obtain ⟨x, hx, hp⟩ := exists_perp F F' hj hD v
    exact ⟨x, Xa_le_X G j (by rwa [hGX]), fun u hu => hp u (by rwa [← hGX'])⟩
  have hcn' : c * star c = 1 := by
    rw [hT', ← hT] at hcn
    exact mul_right_cancel₀ F.hT (by rw [hcn, one_mul])
  have hBM : B * M'.transpose = 1 := by
    have := congrArg Matrix.transpose hM'
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this
  have hW : M * (Zhat F F').submatrix (Fin.castLE (hj.trans (Nat.le_succ r))) (Fin.castLE (hj.trans (Nat.le_succ r))) *
      M'.transpose = Matrix.of fun a b => w.mat a b * ((sgn b : ℤ) : K) := by
    rw [hZ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hM, Matrix.one_mul, Matrix.mul_assoc, hBM, Matrix.mul_one]
  have pair : ∀ a b : Fin j, H.B (G.e (Fin.castLE (hj.trans (Nat.le_succ r)) a))
      (G'.e (Fin.castLE (hj.trans (Nat.le_succ r)) b)) = w.mat a b * ((sgn b : ℤ) : K) := fun a b => by
    have h := congrFun (congrFun hW a) b
    rw [Matrix.of_apply] at h
    rw [← h, hG, hG', hf, hf', dif_pos (show (Fin.castLE (hj.trans (Nat.le_succ r)) a).val < j from a.isLt),
      dif_pos (show (Fin.castLE (hj.trans (Nat.le_succ r)) b).val < j from b.isLt), map_sum, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [map_smulₛₗ, B_sum_left, Matrix.mul_apply]
    rw [starRingEnd_apply, Matrix.map_apply, star_star, smul_eq_mul, mul_comm]
    rfl
  have posdef : ∀ σ : K →+* ℂ, G.PosDefAt σ := fun σ v hv hvX => by
    have hXX : G.X = F.X := hGX r
    refine hpos σ v (fun a => ?_) (by rwa [← hXX])
    have h2 : H.B (f a - F.e a) v = 0 :=
      perp_X G (fun b => hv b.castSucc) _ (by rw [hXX]; exact Xa_le_X F _ (hF a))
    have h3 := hv a
    rw [hG] at h3
    rwa [map_sub, LinearMap.sub_apply, h3, zero_sub, neg_eq_zero] at h2
  refine ⟨⟨G, G', j, hj, c, hcn', T, hGT.trans hT, hGT'.trans hT', same, w, sgn, pair, ist, fun a b _ => i1 a b,
    fun a b ha _ => i2 b _ (e_mem_Xa G' a ha), fun b _ => i3 b, i4, posdef, 𝔡, h𝔡, h𝔡s⟩, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro a; show G.e a - _ ∈ _; rw [hG]; exact hF a
  · intro a; show G'.e a - _ ∈ _; rw [hG']; exact hF' a

end GlobalTheory.DegCnt.RatNormal
