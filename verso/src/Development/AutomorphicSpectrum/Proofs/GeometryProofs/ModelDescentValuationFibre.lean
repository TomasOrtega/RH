import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPreFamilyOfLatticeFamilyTwo
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Cartier
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinGradedFrameIff
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MemSpanOverOfMem
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocFreeMapMkQIff
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

namespace GlobalTheory.CompanionTheory.Ar.Num.FlagPairExt

noncomputable section

section Frame

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {K : Type} [Fintype K] {J : K → Type}
  {N : ℕ} {E : Type} [AddCommGroup E] [Module Ω E]

/- English proof (translation)
Establish `hm : ∀ i, ∃ v ∈ B.lat c, (∀ j, i < j → w.repr v j = 0) ∧ w.repr v i = ∏ k, y ⟨k, c k⟩ ^ b i k`. Introduce `i`. Establish `hmem : (∏ k, y ⟨k, c k⟩ ^ b i k) ∈ GroundTheory.Heights₂.Heights.NumbersDVR.degLat o y (b i) c` using `⟨1, Subalgebra.one_mem _, (one_mul _).symm⟩`. Rewrite `hmem` using `[← h.graded c hc i]`. Conclude with `hmem`.

Use `choose u hu hup hdiag using hm`. Use `⟨u, hu, hup, hdiag, ?_⟩` and prove the remaining obligations. Establish `key : ∀ n : ℕ, ∀ v ∈ B.lat c, (∀ j : Fin N, n ≤ (j : ℕ) → w.repr v j = 0) → ∃ a : Fin N → Ω, (∀ j, a j ∈ chartRing o (segreVec y) c) ∧ v = ∑ j, a j • u j`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero`. Introduce `v _ h0`. Use `⟨0, fun _ => Subalgebra.zero_mem _, ?_⟩` and prove the remaining obligations. Establish `hv0 : v = 0` using `w.repr.injective (by`. Use extensionality with `j`.

Simplify using `using h0 j (Nat.zero_le _))`. Simplify using `[hv0]`. Consider the case `succ n ih`. Introduce `v hv h0`. Distinguish the cases in `hn : n < N`.

Set `i : Fin N` to `⟨n, hn⟩`. Establish `hs : w.repr v i ∈ GroundTheory.Heights₂.Heights.NumbersDVR.degLat o y (b i) c`. Rewrite using `[← h.graded c hc i]`. Conclude with `⟨v, hv, fun j hj => h0 j hj, rfl⟩`. Take `⟨t, ht, hts⟩` from `hs`.

Establish `hv' : v - t • u i ∈ B.lat c` using `sub_mem hv (B.stable c t ht _ (hu i))`. Establish `hz : ∀ j : Fin N, n ≤ (j : ℕ) → w.repr (v - t • u i) j = 0`. Introduce `j hj`. Break down `eq_or_lt_of_le hj with e | e` into its components or cases. Establish `hji : j = i` using `Fin.ext e.symm`.

Substitute `hji` using the available equality. Simplify using `[hts, hdiag]`. Establish `hij : i < j` using `e`. Simplify using `[h0 j e, hup i j hij]`. Take `⟨a, ha, hav⟩` from `ih _ hv' hz`.

Use `⟨a + Pi.single i t, fun j => ?_, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hji : j = i`. Rewrite using `[hji]`. Simplify using `using Subalgebra.add_mem _ (ha i) ht`. Simplify `ha j` using `[Pi.single_apply, hji]`.

Establish `e1 : v = (v - t • u i) + t • u i` using `by abel`. Rewrite using `[e1, hav]`. Simplify using `[add_smul, Finset.sum_add_distrib, Pi.single_apply, ite_smul]`. Conclude with `ih v hv fun j hj => absurd j.2 (by omega)`. Conclude with `fun v hv => key N v hv fun j hj => absurd j.2 (not_lt.2 hj)`.
-/
theorem exists_frame (y : (Σ k, J k) → Ω) (B : ChartBundle o (segreVec y) N E)
    (w : Module.Basis (Fin N) Ω E) (b : Fin N → K → ℤ) (h : IsFlagFrame y B w b) (c : ∀ k, J k)
    (hc : segreVec y c ≠ 0) :
    ∃ u : Fin N → E, (∀ i, u i ∈ B.lat c) ∧ (∀ i j, i < j → w.repr (u i) j = 0) ∧
      (∀ i, w.repr (u i) i = ∏ k, y ⟨k, c k⟩ ^ b i k) ∧
      ∀ v ∈ B.lat c, ∃ a : Fin N → Ω, (∀ j, a j ∈ chartRing o (segreVec y) c) ∧
        v = ∑ j, a j • u j := by
  classical
  have hm : ∀ i, ∃ v ∈ B.lat c, (∀ j, i < j → w.repr v j = 0) ∧
      w.repr v i = ∏ k, y ⟨k, c k⟩ ^ b i k := by
    intro i
    have hmem : (∏ k, y ⟨k, c k⟩ ^ b i k) ∈
        GroundTheory.Heights₂.Heights.NumbersDVR.degLat o y (b i) c :=
      ⟨1, Subalgebra.one_mem _, (one_mul _).symm⟩
    rw [← h.graded c hc i] at hmem
    exact hmem
  choose u hu hup hdiag using hm
  refine ⟨u, hu, hup, hdiag, ?_⟩
  have key : ∀ n : ℕ, ∀ v ∈ B.lat c, (∀ j : Fin N, n ≤ (j : ℕ) → w.repr v j = 0) →
      ∃ a : Fin N → Ω, (∀ j, a j ∈ chartRing o (segreVec y) c) ∧ v = ∑ j, a j • u j := by
    intro n
    induction n with
    | zero =>
      intro v _ h0
      refine ⟨0, fun _ => Subalgebra.zero_mem _, ?_⟩
      have hv0 : v = 0 := w.repr.injective (by
        ext j
        simpa using h0 j (Nat.zero_le _))
      simp [hv0]
    | succ n ih =>
      intro v hv h0
      by_cases hn : n < N
      · let i : Fin N := ⟨n, hn⟩
        have hs : w.repr v i ∈ GroundTheory.Heights₂.Heights.NumbersDVR.degLat o y (b i) c := by
          rw [← h.graded c hc i]
          exact ⟨v, hv, fun j hj => h0 j hj, rfl⟩
        obtain ⟨t, ht, hts⟩ := hs
        have hv' : v - t • u i ∈ B.lat c := sub_mem hv (B.stable c t ht _ (hu i))
        have hz : ∀ j : Fin N, n ≤ (j : ℕ) → w.repr (v - t • u i) j = 0 := by
          intro j hj
          rcases eq_or_lt_of_le hj with e | e
          · have hji : j = i := Fin.ext e.symm
            subst hji
            simp [hts, hdiag]
          · have hij : i < j := e
            simp [h0 j e, hup i j hij]
        obtain ⟨a, ha, hav⟩ := ih _ hv' hz
        refine ⟨a + Pi.single i t, fun j => ?_, ?_⟩
        · by_cases hji : j = i
          · rw [hji]
            simpa using Subalgebra.add_mem _ (ha i) ht
          · simpa [Pi.single_apply, hji] using ha j
        · have e1 : v = (v - t • u i) + t • u i := by abel
          rw [e1, hav]
          simp [add_smul, Finset.sum_add_distrib, Pi.single_apply, ite_smul]
      · exact ih v hv fun j hj => absurd j.2 (by omega)
  exact fun v hv => key N v hv fun j hj => absurd j.2 (not_lt.2 hj)

/- English proof (translation)
Establish `hr : x i / x j ∈ chartRing o x j` using `Algebra.subset_adjoin ⟨i, rfl⟩`. Proceed by induction on `ha using Algebra.adjoin_induction with`. Consider the case `mem t ht`. Take `⟨k, rfl⟩` from `ht`. Use `⟨1, ?_⟩` and prove the remaining obligations.

Establish `e : (x i / x j) ^ 1 * (x k / x i) = x k / x j`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`. Conclude with `Algebra.subset_adjoin ⟨k, rfl⟩`. Consider the case `algebraMap r => exact ⟨0, by simpa using Subalgebra.algebraMap_mem _ r⟩`.

Consider the case `add s t _ _ hs ht`. Take `⟨n, hn⟩` from `hs`. Take `⟨m, hm⟩` from `ht`. Use `⟨n + m, ?_⟩` and prove the remaining obligations. Establish `e : (x i / x j) ^ (n + m) * (s + t) = (x i / x j) ^ m * ((x i / x j) ^ n * s) + (x i / x j) ^ n * ((x i / x j) ^ m * t)` using `by ring`.

Rewrite using `[e]`. Conclude with `Subalgebra.add_mem _ (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hr _) hn) (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hr _) hm)`. Consider the case `mul s t _ _ hs ht`. Take `⟨n, hn⟩` from `hs`. Take `⟨m, hm⟩` from `ht`.

Use `⟨n + m, ?_⟩` and prove the remaining obligations. Establish `e : (x i / x j) ^ (n + m) * (s * t) = ((x i / x j) ^ n * s) * ((x i / x j) ^ m * t)`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `Subalgebra.mul_mem _ hn hm`.
-/
theorem exists_ratio_pow_mul_mem {ι : Type} (x : ι → Ω) (i j : ι) (hi : x i ≠ 0) {a : Ω}
    (ha : a ∈ chartRing o x i) : ∃ n : ℕ, (x i / x j) ^ n * a ∈ chartRing o x j := by
  have hr : x i / x j ∈ chartRing o x j := Algebra.subset_adjoin ⟨i, rfl⟩
  induction ha using Algebra.adjoin_induction with
  | mem t ht =>
    obtain ⟨k, rfl⟩ := ht
    refine ⟨1, ?_⟩
    have e : (x i / x j) ^ 1 * (x k / x i) = x k / x j := by
      field_simp
    rw [e]
    exact Algebra.subset_adjoin ⟨k, rfl⟩
  | algebraMap r => exact ⟨0, by simpa using Subalgebra.algebraMap_mem _ r⟩
  | add s t _ _ hs ht =>
    obtain ⟨n, hn⟩ := hs
    obtain ⟨m, hm⟩ := ht
    refine ⟨n + m, ?_⟩
    have e : (x i / x j) ^ (n + m) * (s + t) =
        (x i / x j) ^ m * ((x i / x j) ^ n * s) + (x i / x j) ^ n * ((x i / x j) ^ m * t) := by ring
    rw [e]
    exact Subalgebra.add_mem _ (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hr _) hn)
      (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hr _) hm)
  | mul s t _ _ hs ht =>
    obtain ⟨n, hn⟩ := hs
    obtain ⟨m, hm⟩ := ht
    refine ⟨n + m, ?_⟩
    have e : (x i / x j) ^ (n + m) * (s * t) = ((x i / x j) ^ n * s) * ((x i / x j) ^ m * t) := by
      ring
    rw [e]
    exact Subalgebra.mul_mem _ hn hm

end Frame

section Extension

variable {O Ω O' Ω' : Type} [CommRing O] [Field Ω] [Algebra O Ω] [CommRing O'] [Algebra O O']
  [Field Ω'] [Algebra Ω Ω'] [Algebra O' Ω'] [Algebra O Ω'] [IsScalarTower O O' Ω']
  [IsScalarTower O Ω Ω'] {K : Type} [Fintype K] {J : K → Type}

variable (Ω') in

abbrev bcPt (y : (Σ k, J k) → Ω) : (Σ k, J k) → Ω' := fun v => algebraMap Ω Ω' (y v)

/- English proof (translation)
Simplify using `[segreVec, map_prod]`.
-/
theorem segreVec_bcPt (y : (Σ k, J k) → Ω) (c : ∀ k, J k) :
    segreVec (bcPt Ω' y) c = algebraMap Ω Ω' (segreVec y c) := by
  simp [segreVec, map_prod]

/- English proof (translation)
Introduce `h0`. Apply `h` to reduce the goal to its premises. Rewrite using `[segreVec_bcPt, h0, map_zero]`.
-/
theorem segreVec_ne_zero_of_bcPt {y : (Σ k, J k) → Ω} {c : ∀ k, J k}
    (h : segreVec (bcPt Ω' y) c ≠ 0) : segreVec y c ≠ 0 := by
  intro h0
  apply h
  rw [segreVec_bcPt, h0, map_zero]

/- English proof (translation)
Proceed by induction on `ha using Algebra.adjoin_induction with`. Consider the case `mem t ht`. Take `⟨j, rfl⟩` from `ht`. Rewrite using `[map_div₀, ← segreVec_bcPt, ← segreVec_bcPt]`. Conclude with `Algebra.subset_adjoin ⟨j, rfl⟩`.

Consider the case `algebraMap r`. Rewrite using `[← IsScalarTower.algebraMap_apply O Ω Ω', IsScalarTower.algebraMap_apply O O' Ω']`. Conclude with `Subalgebra.algebraMap_mem _ _`. Consider the case `add s t _ _ hs ht => rw [map_add]`. Conclude with `Subalgebra.add_mem _ hs ht`.

Consider the case `mul s t _ _ hs ht => rw [map_mul]`. Conclude with `Subalgebra.mul_mem _ hs ht`.
-/
theorem map_mem_chartRing (y : (Σ k, J k) → Ω) (c : ∀ k, J k) {a : Ω}
    (ha : a ∈ chartRing O (segreVec y) c) :
    algebraMap Ω Ω' a ∈ chartRing O' (segreVec (bcPt Ω' y)) c := by
  induction ha using Algebra.adjoin_induction with
  | mem t ht =>
    obtain ⟨j, rfl⟩ := ht
    rw [map_div₀, ← segreVec_bcPt, ← segreVec_bcPt]
    exact Algebra.subset_adjoin ⟨j, rfl⟩
  | algebraMap r =>
    rw [← IsScalarTower.algebraMap_apply O Ω Ω', IsScalarTower.algebraMap_apply O O' Ω']
    exact Subalgebra.algebraMap_mem _ _
  | add s t _ _ hs ht => rw [map_add]; exact Subalgebra.add_mem _ hs ht
  | mul s t _ _ hs ht => rw [map_mul]; exact Subalgebra.mul_mem _ hs ht

variable {r : ℕ}

/- English proof (translation)
Rewrite using `[map_smul, algebraMap_smul]`.
-/
theorem bcMap_smul (t : Ω) (v : Fin r → Ω) :
    bcMap Ω Ω' (Fin r) (t • v) = algebraMap Ω Ω' t • bcMap Ω Ω' (Fin r) v := by
  rw [map_smul, algebraMap_smul]

/- English proof (translation)
Establish `hρ : x' i / x' j = algebraMap Ω Ω' (x i / x j)` using `by rw [map_div₀, hx, hx]`. Establish `hr : x' i / x' j ∈ chartRing O' x' j` using `Algebra.subset_adjoin ⟨i, rfl⟩`. Take `⟨ρ, hρd⟩ : ∃ ρ, ρ = x' i / x' j` from `⟨_, rfl⟩`. Rewrite `hρ`, `hr`, the goal using `[← hρd]`. Unfold `spanOver at he ⊢`.

Proceed by induction on `he using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨a, ha, _, ⟨v, hv, rfl⟩, rfl⟩` from `hz`. Take `⟨n, hn⟩` from `exists_ratio_pow_mul_mem x' i j hi ha`. Rewrite `hn` using `[← hρd]`.

Take `⟨m, hm⟩` from `hov v hv`. Use `⟨n + m, ?_⟩` and prove the remaining obligations. Establish `e1 : ρ ^ (n + m) • a • bcMap Ω Ω' (Fin r) v = (ρ ^ n * a) • bcMap Ω Ω' (Fin r) ((x i / x j) ^ m • v)`. Rewrite using `[bcMap_smul, map_pow, ← hρ, pow_add, smul_smul, smul_smul]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1]`. Conclude with `AddSubgroup.subset_closure ⟨_, hn, _, ⟨_, hm, rfl⟩, rfl⟩`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add z t _ _ hz ht`.

Take `⟨n, hn⟩` from `hz`. Take `⟨m, hm⟩` from `ht`. Use `⟨n + m, ?_⟩` and prove the remaining obligations. Establish `e1 : ρ ^ (n + m) • (z + t) = ρ ^ m • (ρ ^ n • z) + ρ ^ n • (ρ ^ m • t)`. Rewrite using `[smul_add, smul_smul, smul_smul, ← pow_add, ← pow_add, add_comm m n]`.

Rewrite using `[e1]`. Conclude with `add_mem (LocFreeBC.smul_mem_spanOver _ _ (Subalgebra.pow_mem _ hr _) hn) (LocFreeBC.smul_mem_spanOver _ _ (Subalgebra.pow_mem _ hr _) hm)`. Consider the case `neg z _ hz`. Take `⟨n, hn⟩` from `hz`. Conclude with `⟨n, by simpa using neg_mem hn⟩`.
-/
theorem span_overlap {ι : Type} (x : ι → Ω) (x' : ι → Ω') (hx : ∀ i, x' i = algebraMap Ω Ω' (x i))
    (L : ι → AddSubgroup (Fin r → Ω)) (i j : ι) (hi : x' i ≠ 0)
    (hov : ∀ e ∈ L i, ∃ m : ℕ, (x i / x j) ^ m • e ∈ L j) (e : Fin r → Ω')
    (he : e ∈ spanOver (chartRing O' x' i) (bcMap Ω Ω' (Fin r) '' (L i : Set (Fin r → Ω)))) :
    ∃ m : ℕ, (x' i / x' j) ^ m • e ∈
      spanOver (chartRing O' x' j) (bcMap Ω Ω' (Fin r) '' (L j : Set (Fin r → Ω))) := by
  have hρ : x' i / x' j = algebraMap Ω Ω' (x i / x j) := by rw [map_div₀, hx, hx]
  have hr : x' i / x' j ∈ chartRing O' x' j := Algebra.subset_adjoin ⟨i, rfl⟩
  obtain ⟨ρ, hρd⟩ : ∃ ρ, ρ = x' i / x' j := ⟨_, rfl⟩
  rw [← hρd] at hρ hr ⊢
  unfold spanOver at he ⊢
  induction he using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, _, ⟨v, hv, rfl⟩, rfl⟩ := hz
    obtain ⟨n, hn⟩ := exists_ratio_pow_mul_mem x' i j hi ha
    rw [← hρd] at hn
    obtain ⟨m, hm⟩ := hov v hv
    refine ⟨n + m, ?_⟩
    have e1 : ρ ^ (n + m) • a • bcMap Ω Ω' (Fin r) v =
        (ρ ^ n * a) • bcMap Ω Ω' (Fin r) ((x i / x j) ^ m • v) := by
      rw [bcMap_smul, map_pow, ← hρ, pow_add, smul_smul, smul_smul]
      congr 1
      ring
    rw [e1]
    exact AddSubgroup.subset_closure ⟨_, hn, _, ⟨_, hm, rfl⟩, rfl⟩
  | zero => exact ⟨0, by simp⟩
  | add z t _ _ hz ht =>
    obtain ⟨n, hn⟩ := hz
    obtain ⟨m, hm⟩ := ht
    refine ⟨n + m, ?_⟩
    have e1 : ρ ^ (n + m) • (z + t) = ρ ^ m • (ρ ^ n • z) + ρ ^ n • (ρ ^ m • t) := by
      rw [smul_add, smul_smul, smul_smul, ← pow_add, ← pow_add, add_comm m n]
    rw [e1]
    exact add_mem (LocFreeBC.smul_mem_spanOver _ _ (Subalgebra.pow_mem _ hr _) hn)
      (LocFreeBC.smul_mem_spanOver _ _ (Subalgebra.pow_mem _ hr _) hm)
  | neg z _ hz =>
    obtain ⟨n, hn⟩ := hz
    exact ⟨n, by simpa using neg_mem hn⟩

/- English proof (translation)
Establish `hR : ∀ a ∈ chartRing O (segreVec y) c, algebraMap Ω Ω' a ∈ (chartRing O' (segreVec (bcPt Ω' y)) c).restrictScalars O` using `fun a ha => (Subalgebra.mem_restrictScalars O).mpr (map_mem_chartRing (O' := O') y c ha)`. Conclude with `LocFreeBC.locFree_baseChange (chartRing O (segreVec y) c) _ hR (bcMap Ω Ω' (Fin r)) (LatticeGoodness.isBaseChange_bcMap Ω Ω' _) r (B.lat c) ⟨B.stable c, B.frame c hc⟩`.
-/
theorem locFree_ext {y : (Σ k, J k) → Ω} (B : ChartBundle O (segreVec y) r (Fin r → Ω))
    (c : ∀ k, J k) (hc : segreVec y c ≠ 0) :
    LocFree ((chartRing O' (segreVec (bcPt Ω' y)) c).restrictScalars O) r
      (spanOver ((chartRing O' (segreVec (bcPt Ω' y)) c).restrictScalars O)
        (bcMap Ω Ω' (Fin r) '' (B.lat c : Set (Fin r → Ω)))) := by
  have hR : ∀ a ∈ chartRing O (segreVec y) c, algebraMap Ω Ω' a ∈
      (chartRing O' (segreVec (bcPt Ω' y)) c).restrictScalars O := fun a ha =>
    (Subalgebra.mem_restrictScalars O).mpr (map_mem_chartRing (O' := O') y c ha)
  exact LocFreeBC.locFree_baseChange (chartRing O (segreVec y) c) _ hR (bcMap Ω Ω' (Fin r))
    (LatticeGoodness.isBaseChange_bcMap Ω Ω' _) r (B.lat c) ⟨B.stable c, B.frame c hc⟩

def extBundle (O' : Type) [CommRing O'] [Algebra O O'] {Ω' : Type} [Field Ω'] [Algebra Ω Ω']
    [Algebra O' Ω'] [Algebra O Ω'] [IsScalarTower O O' Ω'] [IsScalarTower O Ω Ω']
    {y : (Σ k, J k) → Ω} (B : ChartBundle O (segreVec y) r (Fin r → Ω)) :
    ChartBundle O' (segreVec (bcPt Ω' y)) r (Fin r → Ω') where
  lat c := spanOver (chartRing O' (segreVec (bcPt Ω' y)) c)
    (bcMap Ω Ω' (Fin r) '' (B.lat c : Set (Fin r → Ω)))
  stable c a ha e he := LocFreeBC.smul_mem_spanOver _ _ ha he
  frame c hc := (locFree_ext (O' := O') B c (segreVec_ne_zero_of_bcPt hc)).2
  overlap i j hi hj e he := span_overlap (segreVec y) (segreVec (bcPt Ω' y))
    (fun c => segreVec_bcPt y c) B.lat i j hi (B.overlap i j (segreVec_ne_zero_of_bcPt hi)
      (segreVec_ne_zero_of_bcPt hj)) e he

def extBasis (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] (w : Module.Basis (Fin r) Ω (Fin r → Ω)) :
    Module.Basis (Fin r) Ω' (Fin r → Ω') :=
  IsBaseChange.basis w (LatticeGoodness.isBaseChange_bcMap Ω Ω' (Fin r))

/- English proof (translation)
Simplify using `[extBasis, IsBaseChange.basis_apply]`.
-/
theorem extBasis_apply (w : Module.Basis (Fin r) Ω (Fin r → Ω)) (i : Fin r) :
    extBasis Ω' w i = bcMap Ω Ω' (Fin r) (w i) := by
  simp [extBasis, IsBaseChange.basis_apply]

/- English proof (translation)
Establish `e1 : bcMap Ω Ω' (Fin r) e = ∑ i, algebraMap Ω Ω' (w.repr e i) • extBasis Ω' w i` using `by conv_lhs => rw [← w.sum_repr e]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[bcMap_smul, extBasis_apply]`. Rewrite using `[e1, GroundTheory.Heights₂.Heights.NumbersDVR.GradedFrameCharacterisation.repr_sum_smul]`.

Simplify using `[Module.Basis.repr_self, Finsupp.single_apply]`.
-/
theorem extBasis_repr (w : Module.Basis (Fin r) Ω (Fin r → Ω)) (e : Fin r → Ω) (j : Fin r) :
    (extBasis Ω' w).repr (bcMap Ω Ω' (Fin r) e) j = algebraMap Ω Ω' (w.repr e j) := by
  classical
  have e1 : bcMap Ω Ω' (Fin r) e = ∑ i, algebraMap Ω Ω' (w.repr e i) • extBasis Ω' w i := by
    conv_lhs => rw [← w.sum_repr e]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [bcMap_smul, extBasis_apply]
  rw [e1, GroundTheory.Heights₂.Heights.NumbersDVR.GradedFrameCharacterisation.repr_sum_smul]
  simp [Module.Basis.repr_self, Finsupp.single_apply]

/- English proof (translation)
Unfold `spanOver at he`. Proceed by induction on `he using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨t, ht, _, ⟨v, hv, rfl⟩, rfl⟩` from `hz`. Take `⟨a, ha, rfl⟩` from `hgen v hv`.

Use `⟨fun j => t * algebraMap Ω Ω' (a j), fun j => Subalgebra.mul_mem _ ht (hR _ (ha j)), ?_⟩` and prove the remaining obligations. Rewrite using `[map_sum, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[bcMap_smul, smul_smul]`. Consider the case `zero => exact ⟨0, fun _ => Subalgebra.zero_mem _, by simp⟩`.

Consider the case `add z t _ _ hz ht`. Take `⟨a, ha, rfl⟩` from `hz`. Take `⟨b, hb, rfl⟩` from `ht`. Conclude with `⟨a + b, fun j => Subalgebra.add_mem _ (ha j) (hb j), by`. Simplify using `[add_smul, Finset.sum_add_distrib]⟩`.

Consider the case `neg z _ hz`. Take `⟨a, ha, rfl⟩` from `hz`. Conclude with `⟨-a, fun j => by simpa using Subalgebra.neg_mem _ (ha j), by simp⟩`.
-/
theorem exists_coeff_of_mem_span {ι : Type} (x' : ι → Ω') (c : ι) (R : Subalgebra O Ω)
    (hR : ∀ a ∈ R, algebraMap Ω Ω' a ∈ chartRing O' x' c) (L : AddSubgroup (Fin r → Ω))
    (u : Fin r → Fin r → Ω)
    (hgen : ∀ v ∈ L, ∃ a : Fin r → Ω, (∀ j, a j ∈ R) ∧ v = ∑ j, a j • u j) (e : Fin r → Ω')
    (he : e ∈ spanOver (chartRing O' x' c) (bcMap Ω Ω' (Fin r) '' (L : Set (Fin r → Ω)))) :
    ∃ a : Fin r → Ω', (∀ j, a j ∈ chartRing O' x' c) ∧
      e = ∑ j, a j • bcMap Ω Ω' (Fin r) (u j) := by
  unfold spanOver at he
  induction he using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨t, ht, _, ⟨v, hv, rfl⟩, rfl⟩ := hz
    obtain ⟨a, ha, rfl⟩ := hgen v hv
    refine ⟨fun j => t * algebraMap Ω Ω' (a j), fun j => Subalgebra.mul_mem _ ht (hR _ (ha j)), ?_⟩
    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [bcMap_smul, smul_smul]
  | zero => exact ⟨0, fun _ => Subalgebra.zero_mem _, by simp⟩
  | add z t _ _ hz ht =>
    obtain ⟨a, ha, rfl⟩ := hz
    obtain ⟨b, hb, rfl⟩ := ht
    exact ⟨a + b, fun j => Subalgebra.add_mem _ (ha j) (hb j), by
      simp [add_smul, Finset.sum_add_distrib]⟩
  | neg z _ hz =>
    obtain ⟨a, ha, rfl⟩ := hz
    exact ⟨-a, fun j => by simpa using Subalgebra.neg_mem _ (ha j), by simp⟩

/- English proof (translation)
Use `⟨fun c hc i => ?_⟩` and prove the remaining obligations. Establish `hc0` using `segreVec_ne_zero_of_bcPt hc`. Take `⟨u, hu, hup, hdiag, hgen⟩` from `exists_frame y B w b h c hc0`. Establish `hmne : ∀ i, ∏ k, y ⟨k, c k⟩ ^ b i k ≠ 0` using `fun i => Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (Finset.prod_ne_zero_iff.1 hc0 k (Finset.mem_univ k))`. Establish `hmon : ∀ i, algebraMap Ω Ω' (∏ k, y ⟨k, c k⟩ ^ b i k) = ∏ k, bcPt Ω' y ⟨k, c k⟩ ^ b i k` using `fun i => by simp [map_prod, map_zpow₀]`.

Establish `hup' : ∀ q j : Fin r, q < j → (extBasis Ω' w).repr (bcMap Ω Ω' (Fin r) (u q)) j = 0` using `fun q j hqj => by`. Rewrite using `[extBasis_repr, hup q j hqj, map_zero]`. Establish `hd' : ∀ q, (extBasis Ω' w).repr (bcMap Ω Ω' (Fin r) (u q)) q ≠ 0` using `fun q => by`. Rewrite using `[extBasis_repr, hdiag q]`. Conclude with `(map_ne_zero _).2 (hmne q)`.

Establish `hdi : (extBasis Ω' w).repr (bcMap Ω Ω' (Fin r) (u i)) i = ∏ k, bcPt Ω' y ⟨k, c k⟩ ^ b i k`. Rewrite using `[extBasis_repr, hdiag i, hmon]`. Use extensionality with `s`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨e, he, hvan, rfl⟩`.

Take `⟨a, ha, rfl⟩` from `exists_coeff_of_mem_span (O' := O') _ c _ (fun t ht => map_mem_chartRing y c ht) (B.lat c) u hgen e he`. Establish `hz` using `GroundTheory.Heights₂.Heights.NumbersDVR.GradedFrameCharacterisation.coeff_eq_zero_of_tri (extBasis Ω' w) (fun j => bcMap Ω Ω' (Fin r) (u j)) hup' hd' a ((i : ℕ) + 1) (fun j hj => hvan j (Fin.lt_def.2 hj))`. Use `⟨a i, ha i, ?_⟩` and prove the remaining obligations. Rewrite using `[GroundTheory.Heights₂.Heights.NumbersDVR.GradedFrameCharacterisation.repr_sum_smul, Finset.sum_eq_single i, hdi]`. Introduce `q _ hq`.

Break down `lt_or_gt_of_ne hq with hlt | hgt` into its components or cases. Rewrite using `[hup' q i hlt, mul_zero]`. Rewrite using `[hz q (Fin.lt_def.1 hgt), zero_mul]`. Simplify using the standard rewrite rules. Introduce and unpack `⟨a, ha, rfl⟩`.

Use `⟨a • bcMap Ω Ω' (Fin r) (u i), AddSubgroup.subset_closure ⟨a, ha, _, ⟨u i, hu i, rfl⟩, rfl⟩, fun j hj => ?_, ?_⟩` and prove the remaining obligations. Simplify using `[hup' i j hj]`. Simplify using `[hdi]`.
-/
theorem isFlagFrame_ext {y : (Σ k, J k) → Ω} (B : ChartBundle O (segreVec y) r (Fin r → Ω))
    (w : Module.Basis (Fin r) Ω (Fin r → Ω)) (b : Fin r → K → ℤ) (h : IsFlagFrame y B w b) :
    IsFlagFrame (bcPt Ω' y) (extBundle O' B) (extBasis Ω' w) b := by
  refine ⟨fun c hc i => ?_⟩
  have hc0 := segreVec_ne_zero_of_bcPt hc
  obtain ⟨u, hu, hup, hdiag, hgen⟩ := exists_frame y B w b h c hc0
  have hmne : ∀ i, ∏ k, y ⟨k, c k⟩ ^ b i k ≠ 0 := fun i =>
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (Finset.prod_ne_zero_iff.1 hc0 k (Finset.mem_univ k))
  have hmon : ∀ i, algebraMap Ω Ω' (∏ k, y ⟨k, c k⟩ ^ b i k) =
      ∏ k, bcPt Ω' y ⟨k, c k⟩ ^ b i k := fun i => by simp [map_prod, map_zpow₀]
  have hup' : ∀ q j : Fin r, q < j →
      (extBasis Ω' w).repr (bcMap Ω Ω' (Fin r) (u q)) j = 0 := fun q j hqj => by
    rw [extBasis_repr, hup q j hqj, map_zero]
  have hd' : ∀ q, (extBasis Ω' w).repr (bcMap Ω Ω' (Fin r) (u q)) q ≠ 0 := fun q => by
    rw [extBasis_repr, hdiag q]
    exact (map_ne_zero _).2 (hmne q)
  have hdi : (extBasis Ω' w).repr (bcMap Ω Ω' (Fin r) (u i)) i =
      ∏ k, bcPt Ω' y ⟨k, c k⟩ ^ b i k := by
    rw [extBasis_repr, hdiag i, hmon]
  ext s
  constructor
  · rintro ⟨e, he, hvan, rfl⟩
    obtain ⟨a, ha, rfl⟩ := exists_coeff_of_mem_span (O' := O') _ c _
      (fun t ht => map_mem_chartRing y c ht) (B.lat c) u hgen e he
    have hz := GroundTheory.Heights₂.Heights.NumbersDVR.GradedFrameCharacterisation.coeff_eq_zero_of_tri
      (extBasis Ω' w) (fun j => bcMap Ω Ω' (Fin r) (u j)) hup' hd' a ((i : ℕ) + 1)
      (fun j hj => hvan j (Fin.lt_def.2 hj))
    refine ⟨a i, ha i, ?_⟩
    rw [GroundTheory.Heights₂.Heights.NumbersDVR.GradedFrameCharacterisation.repr_sum_smul,
      Finset.sum_eq_single i, hdi]
    · intro q _ hq
      rcases lt_or_gt_of_ne hq with hlt | hgt
      · rw [hup' q i hlt, mul_zero]
      · rw [hz q (Fin.lt_def.1 hgt), zero_mul]
    · simp
  · rintro ⟨a, ha, rfl⟩
    refine ⟨a • bcMap Ω Ω' (Fin r) (u i),
      AddSubgroup.subset_closure ⟨a, ha, _, ⟨u i, hu i, rfl⟩, rfl⟩, fun j hj => ?_, ?_⟩
    · simp [hup' i j hj]
    · simp [hdi]

end Extension

section Vertical

variable {O Ω O' Ω' : Type} [CommRing O] [Field Ω] [Algebra O Ω] [CommRing O'] [Algebra O O']
  [Field Ω'] [Algebra Ω Ω'] [Algebra O' Ω'] [Algebra O Ω'] [IsScalarTower O O' Ω']
  [IsScalarTower O Ω Ω'] {K : Type} {J : K → Type}

open GroundTheory.Heights₂.Heights.NumbersDVR in
/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a`. Simplify using `[pointConeMap, MvPolynomial.algebraMap_apply, ← IsScalarTower.algebraMap_apply O O' Ω', ← IsScalarTower.algebraMap_apply O Ω Ω']`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p v hp`.

Simplify using `only [map_mul, hp, MvPolynomial.map_X]`. Simplify using `[pointConeMap]`.
-/
theorem pointConeMap_map (y : (Σ k, J k) → Ω) (f : MRing J O) :
    pointConeMap O' (bcPt Ω' y) (MvPolynomial.map (algebraMap O O') f) =
      MvPolynomial.map (algebraMap Ω Ω') (pointConeMap O y f) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    simp [pointConeMap, MvPolynomial.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply O O' Ω', ← IsScalarTower.algebraMap_apply O Ω Ω']
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, MvPolynomial.map_X]
    simp [pointConeMap]

open GroundTheory.Heights₂.Heights.NumbersDVR in
/- English proof (translation)
Simplify using `only [pointIdeal, RingHom.mem_ker, pointConeMap_map]`. Conclude with `map_eq_zero_iff _ (MvPolynomial.map_injective _ (algebraMap Ω Ω').injective)`.
-/
theorem map_mem_pointIdeal_iff (y : (Σ k, J k) → Ω) (f : MRing J O) :
    MvPolynomial.map (algebraMap O O') f ∈ pointIdeal O' (bcPt Ω' y) ↔ f ∈ pointIdeal O y := by
  simp only [pointIdeal, RingHom.mem_ker, pointConeMap_map]
  exact map_eq_zero_iff _ (MvPolynomial.map_injective _ (algebraMap Ω Ω').injective)

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a`. Simplify using `[← IsScalarTower.algebraMap_apply O O' Ω', ← IsScalarTower.algebraMap_apply O Ω Ω']`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p v hp => simp only [map_mul, hp, MvPolynomial.map_X, aeval_X]`.
-/
theorem aeval_map (y : (Σ k, J k) → Ω) (f : GroundTheory.Heights₂.Heights.NumbersDVR.MRing J O) :
    aeval (bcPt Ω' y) (MvPolynomial.map (algebraMap O O') f) = algebraMap Ω Ω' (aeval y f) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    simp [← IsScalarTower.algebraMap_apply O O' Ω', ← IsScalarTower.algebraMap_apply O Ω Ω']
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp => simp only [map_mul, hp, MvPolynomial.map_X, aeval_X]

variable [DecidableEq K]

open GroundTheory.Heights₂.Heights.NumbersDVR in
/- English proof (translation)
Introduce `d hd`. Rewrite `hd` using `[coeff_map]`. Conclude with `h fun h0 => hd (by rw [h0, map_zero])`.
-/
theorem isMultiHomog_map {f : MRing J O} {b : K → ℕ} (h : IsMultiHomog f b) :
    IsMultiHomog (MvPolynomial.map (algebraMap O O') f) b := by
  intro d hd
  rw [coeff_map] at hd
  exact h fun h0 => hd (by rw [h0, map_zero])

open GroundTheory.Heights₂.Heights.NumbersDVR in

/- English proof (translation)
Use `IsVerticalDivisor.of_unit_off_special ?_ ?_ ?_ ?_` and prove the remaining obligations. Take `⟨bf, bg, hf, hg, hb⟩` from `hD.degrees`. Conclude with `⟨bf, bg, isMultiHomog_map hf, isMultiHomog_map hg, hb⟩`. Rewrite using `[map_mem_pointIdeal_iff]`. Conclude with `hD.num_not_mem`.

Rewrite using `[map_mem_pointIdeal_iff]`. Conclude with `hD.den_not_mem`. Introduce `W hW hPW hrel hϖW`. Establish `hinj' : Function.Injective (algebraMap O O')`. Introduce `a a' haa`.

Apply `hinj` to reduce the goal to its premises. Apply `(algebraMap Ω Ω').injective` to reduce the goal to its premises. Rewrite using `[← IsScalarTower.algebraMap_apply O Ω Ω', ← IsScalarTower.algebraMap_apply O Ω Ω', IsScalarTower.algebraMap_apply O O' Ω', IsScalarTower.algebraMap_apply O O' Ω', haa]`. Set `φ : MRing J O →+* MRing J O'` to `MvPolynomial.map (algebraMap O O')`. Establish `hφ : ∀ h, MvPolynomial.map (algebraMap O O') h = φ h` using `fun _ => rfl`.

Establish `hle : pointIdeal O y ≤ W.comap φ` using `fun h hh => by`. Rewrite using `[Ideal.mem_comap]`. Conclude with `hPW ((map_mem_pointIdeal_iff y h).2 hh)`. Establish `hrel' : GroundTheory.Heights₂.Heights.NumbersDVR.IsRelevant (W.comap φ)`. Introduce `k`.

Take `⟨i, hi⟩` from `hrel k`. Conclude with `⟨i, by rw [Ideal.mem_comap]; simpa [φ] using hi⟩`. Establish `hϖ0 : algebraMap O O' ϖ ≠ 0` using `fun h0 => hϖ.ne_zero (hinj' (by rw [h0, map_zero]))`. Take `⟨n, hn⟩` from `IsDiscreteValuationRing.associated_pow_irreducible hϖ0 hϖ'`. Establish `hϖ1 : (C ϖ : MRing J O) ∉ W.comap φ`.

Rewrite using `[Ideal.mem_comap]`. Introduce `hm`. Apply `hϖW` to reduce the goal to its premises. Take `⟨t, ht⟩` from `hn`. Establish `hpow : (C ϖ' : MRing J O') ^ n ∈ W`.

Rewrite using `[← C_pow, ← ht, C_mul]`. Conclude with `W.mul_mem_right _ (by simpa [φ] using hm)`. Conclude with `hW.mem_of_pow_mem n hpow`. Take `⟨u, v, hu, hv, huv⟩` from `hD.unit_off_special (W.comap φ) (Ideal.comap_isPrime φ W) hle hrel' hϖ1`. Use `⟨φ u, φ v, hu, hv, ?_⟩` and prove the remaining obligations.

Use `(map_mem_pointIdeal_iff (O' := O') (Ω' := Ω') y _).2 huv` as an intermediate fact. Simplify `this` using `[hφ, map_sub, map_mul]`.
-/
theorem isVerticalDivisor_ext [Fintype K] [IsDomain O] [IsDiscreteValuationRing O] [IsDomain O']
    [IsDiscreteValuationRing O'] (y : (Σ k, J k) → Ω)
    (hinj : Function.Injective (algebraMap O Ω)) {ϖ : O} {ϖ' : O'} (hϖ : Irreducible ϖ)
    (hϖ' : Irreducible ϖ') {b : K → ℤ} {f g : MRing J O}
    (hD : IsVerticalDivisor (pointIdeal O y) ϖ b f g) :
    IsVerticalDivisor (pointIdeal O' (bcPt Ω' y)) ϖ' b (MvPolynomial.map (algebraMap O O') f)
      (MvPolynomial.map (algebraMap O O') g) := by
  refine IsVerticalDivisor.of_unit_off_special ?_ ?_ ?_ ?_
  · obtain ⟨bf, bg, hf, hg, hb⟩ := hD.degrees
    exact ⟨bf, bg, isMultiHomog_map hf, isMultiHomog_map hg, hb⟩
  · rw [map_mem_pointIdeal_iff]; exact hD.num_not_mem
  · rw [map_mem_pointIdeal_iff]; exact hD.den_not_mem
  · intro W hW hPW hrel hϖW
    have hinj' : Function.Injective (algebraMap O O') := by
      intro a a' haa
      apply hinj
      apply (algebraMap Ω Ω').injective
      rw [← IsScalarTower.algebraMap_apply O Ω Ω', ← IsScalarTower.algebraMap_apply O Ω Ω',
        IsScalarTower.algebraMap_apply O O' Ω', IsScalarTower.algebraMap_apply O O' Ω', haa]
    let φ : MRing J O →+* MRing J O' := MvPolynomial.map (algebraMap O O')
    have hφ : ∀ h, MvPolynomial.map (algebraMap O O') h = φ h := fun _ => rfl
    have hle : pointIdeal O y ≤ W.comap φ := fun h hh => by
      rw [Ideal.mem_comap]
      exact hPW ((map_mem_pointIdeal_iff y h).2 hh)
    have hrel' : GroundTheory.Heights₂.Heights.NumbersDVR.IsRelevant (W.comap φ) := by
      intro k
      obtain ⟨i, hi⟩ := hrel k
      exact ⟨i, by rw [Ideal.mem_comap]; simpa [φ] using hi⟩
    have hϖ0 : algebraMap O O' ϖ ≠ 0 := fun h0 =>
      hϖ.ne_zero (hinj' (by rw [h0, map_zero]))
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible hϖ0 hϖ'
    have hϖ1 : (C ϖ : MRing J O) ∉ W.comap φ := by
      rw [Ideal.mem_comap]
      intro hm
      apply hϖW
      obtain ⟨t, ht⟩ := hn
      have hpow : (C ϖ' : MRing J O') ^ n ∈ W := by
        rw [← C_pow, ← ht, C_mul]
        exact W.mul_mem_right _ (by simpa [φ] using hm)
      exact hW.mem_of_pow_mem n hpow
    obtain ⟨u, v, hu, hv, huv⟩ :=
      hD.unit_off_special (W.comap φ) (Ideal.comap_isPrime φ W) hle hrel' hϖ1
    refine ⟨φ u, φ v, hu, hv, ?_⟩
    have := (map_mem_pointIdeal_iff (O' := O') (Ω' := Ω') y _).2 huv
    simpa [hφ, map_sub, map_mul] using this

end Vertical

/- English proof (translation)
Introduce `O _ _ _ Ω _ _ _ K _ _ J _ y d hmodel _ O' _ _ _ _ _ _ Ω' _ _ _ _ _ _ _ ϖ ϖ' hϖ hϖ' r B B' w w' T hp`. Establish `hinj : Function.Injective (algebraMap O Ω)`. Introduce `a a' haa`. Establish `hz : ∀ z : O, algebraMap O Ω z = 0 → z = 0`. Introduce `z hz`.

Establish `hm : (MvPolynomial.C z : GroundTheory.Heights₂.Heights.NumbersDVR.MRing J O) ∈ pointIdeal O y`. Simplify using `[pointIdeal, RingHom.mem_ker, GroundTheory.Heights₂.Heights.NumbersDVR.pointConeMap, MvPolynomial.algebraMap_apply, hz]`. Use `hmodel.noTorsion` as an intermediate fact. Establish `hb : z ∈ (pointIdeal O y).comap (MvPolynomial.C : O →+* GroundTheory.Heights₂.Heights.NumbersDVR.MRing J O)` using `hm`. Rewrite `hb` using `[this]`.

Simplify using `using hb`. Conclude with `sub_eq_zero.1 (hz _ (by rw [map_sub, haa, sub_self]))`. Use `⟨extBundle O' B, extBundle O' B', extBasis Ω' w, extBasis Ω' w', fun c _ => ⟨rfl, rfl⟩, ⟨isFlagFrame_ext B w _ hp.flag, isFlagFrame_ext B' w' _ hp.flag', fun i j hij => ?_, fun i => isVerticalDivisor_ext y hinj hϖ hϖ' (hp.vertical i), fun i => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[extBasis_apply, extBasis_repr, hp.sameFlag i j hij, map_zero]`. Use `show aeval (bcPt Ω' y) (MvPolynomial.map (algebraMap O O') (T.f i)) = (extBasis Ω' w).repr (extBasis Ω' w' i) i * aeval (bcPt Ω' y) (MvPolynomial.map (algebraMap O O') (T.g i))`.

Rewrite using `[aeval_map, aeval_map, extBasis_apply, extBasis_repr, hp.generic i, map_mul]`.
-/
theorem flagPair_ext : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [CharZero Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d → IsIntegrallyClosedIn O Ω → ∀ (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')] [Algebra.IsAlgebraic O O'] (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [Algebra O' Ω'] [Algebra O Ω'] [IsScalarTower O O' Ω'] [IsScalarTower O Ω Ω'], Function.Injective (algebraMap O' Ω') → ∀ (ϖ : O) (ϖ' : O'), Irreducible ϖ → Irreducible ϖ' → ∀ (r : ℕ) (B B' : ChartBundle O (segreVec y) r (Fin r → Ω)) (w w' : Module.Basis (Fin r) Ω (Fin r → Ω)) (T : LocPair J O (Fin r)), IsFlagPair ϖ y B B' w w' T.x T.x' T.f T.g → ∃ (C₁ C₁' : ChartBundle O' (segreVec (fun v => algebraMap Ω Ω' (y v))) r (Fin r → Ω')) (v v' : Module.Basis (Fin r) Ω' (Fin r → Ω')), (∀ c, segreVec y c ≠ 0 → C₁.lat c = spanOver (chartRing O' (segreVec (fun v => algebraMap Ω Ω' (y v))) c) (bcMap Ω Ω' _ '' B.lat c) ∧ C₁'.lat c = spanOver (chartRing O' (segreVec (fun v => algebraMap Ω Ω' (y v))) c) (bcMap Ω Ω' _ '' B'.lat c)) ∧ IsFlagPair ϖ' (fun v => algebraMap Ω Ω' (y v)) C₁ C₁' v v' T.x T.x' (T.map (algebraMap O O')).f (T.map (algebraMap O O')).g := by
  intro O _ _ _ Ω _ _ _ K _ _ J _ y d hmodel _ O' _ _ _ _ _ _ Ω' _ _ _ _ _ _ _ ϖ ϖ' hϖ hϖ' r B B' w w' T hp
  have hinj : Function.Injective (algebraMap O Ω) := by
    intro a a' haa
    have hz : ∀ z : O, algebraMap O Ω z = 0 → z = 0 := by
      intro z hz
      have hm : (MvPolynomial.C z : GroundTheory.Heights₂.Heights.NumbersDVR.MRing J O) ∈ pointIdeal O y := by
        simp [pointIdeal, RingHom.mem_ker, GroundTheory.Heights₂.Heights.NumbersDVR.pointConeMap,
          MvPolynomial.algebraMap_apply, hz]
      have := hmodel.noTorsion
      have hb : z ∈ (pointIdeal O y).comap (MvPolynomial.C : O →+* GroundTheory.Heights₂.Heights.NumbersDVR.MRing J O) := hm
      rw [this] at hb
      simpa using hb
    exact sub_eq_zero.1 (hz _ (by rw [map_sub, haa, sub_self]))
  refine ⟨extBundle O' B, extBundle O' B', extBasis Ω' w, extBasis Ω' w', fun c _ => ⟨rfl, rfl⟩,
    ⟨isFlagFrame_ext B w _ hp.flag, isFlagFrame_ext B' w' _ hp.flag', fun i j hij => ?_,
      fun i => isVerticalDivisor_ext y hinj hϖ hϖ' (hp.vertical i), fun i => ?_⟩⟩
  · rw [extBasis_apply, extBasis_repr, hp.sameFlag i j hij, map_zero]
  · show aeval (bcPt Ω' y) (MvPolynomial.map (algebraMap O O') (T.f i)) =
      (extBasis Ω' w).repr (extBasis Ω' w' i) i *
        aeval (bcPt Ω' y) (MvPolynomial.map (algebraMap O O') (T.g i))
    rw [aeval_map, aeval_map, extBasis_apply, extBasis_repr, hp.generic i, map_mul]

end
end GlobalTheory.CompanionTheory.Ar.Num.FlagPairExt
