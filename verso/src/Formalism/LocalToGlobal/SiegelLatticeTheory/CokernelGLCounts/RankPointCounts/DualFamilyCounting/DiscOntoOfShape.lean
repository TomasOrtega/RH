import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.EQMulDiagQMulEQMem

open NumberField Module Matrix

open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

noncomputable section

namespace Formalism.L2.SG.Pf.discriminantNormShapes

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds Formalism.HermitianLattices.Ext.L3.traceDeterminantCongruences Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms
  Formalism.HermitianLattices.Ext.L3.localValuationFiltration Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G5

def NormShape : Prop :=
  ∀ (K F : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [Fact (IsFixF K F)], Formalism.HermitianLatticesTheory.IsCMUnram K →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ (m : ℕ) (a : Fin m → 𝓞 F), (∀ i, a i ≠ 0) →
    ∀ k : ℕ, 2 * vJof 𝔭 a + 1 ≤ k → ∀ Y : udPre K 𝔭 k a,
      ∃ Y' P W Z₀ : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k),
        Y' - Y.1 = Z₀ * diagQ K 𝔭 k a ∧ P * diagQ K 𝔭 k a = diagQ K 𝔭 k a * Y' ∧
        Y'ᴴ * diagQ K 𝔭 k a * Y' - diagQ K 𝔭 k a = diagQ K 𝔭 k a * W * diagQ K 𝔭 k a ∧
        Wᴴ = W ∧ eQ K 𝔭 k a * W * eQ K 𝔭 k a = W ∧
        eQ K 𝔭 k a * P = eQ K 𝔭 k a * P * eQ K 𝔭 k a ∧
        P * eQ K 𝔭 k a = eQ K 𝔭 k a * P * eQ K 𝔭 k a

/- English proof (translation)
Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, sub_eq_zero, RingHom.map_det]`. Establish `hM : (Ideal.Quotient.mk I).mapMatrix (1 + N) = 1`. Use extensionality with `i j`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality.

Simplify using `[Ideal.Quotient.eq_zero_iff_mem.mpr (hN i i)]`. Simplify using `[Matrix.one_apply_ne hij, Ideal.Quotient.eq_zero_iff_mem.mpr (hN i j)]`. Rewrite using `[hM, Matrix.det_one]`.
-/
theorem det_one_add_sub_mem {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    {I : Ideal R} {N : Matrix n n R} (hN : ∀ i j, N i j ∈ I) : (1 + N).det - 1 ∈ I := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, sub_eq_zero, RingHom.map_det]
  have hM : (Ideal.Quotient.mk I).mapMatrix (1 + N) = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Ideal.Quotient.eq_zero_iff_mem.mpr (hN i i)]
    · simp [Matrix.one_apply_ne hij, Ideal.Quotient.eq_zero_iff_mem.mpr (hN i j)]
  rw [hM, Matrix.det_one]

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [Fact (IsFixF K F)] {m : ℕ}

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

/- English proof (translation)
Establish `hbdd : BddAbove {e : ℕ | x ∈ 𝔭 ^ e}`. Establish `h0 : x ∉ ⨅ n : ℕ, 𝔭 ^ n`. Rewrite using `[Ideal.iInf_pow_eq_bot_of_isDomain 𝔭 h𝔭.ne_top]`. Simplify using `using hx`. Simplify using `only [Submodule.mem_iInf, not_forall] at h0`.

Take `⟨n, hn⟩` from `h0`. Use `⟨n, fun e he => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Conclude with `hn (Ideal.pow_le_pow_right hlt.le he)`.

Use `⟨?_, fun h => ?_⟩` and prove the remaining obligations. Establish `h1` using `Nat.sSup_mem (s := {e : ℕ | x ∈ 𝔭 ^ e}) ⟨0, by simp⟩ hbdd`. Conclude with `h1`. Establish `h2 : vF 𝔭 x + 1 ≤ vF 𝔭 x` using `le_csSup hbdd h`. Use linear arithmetic over natural numbers and integers.
-/
private theorem mem_pow_vF_not_mem_pow_vF_succ {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {x : 𝓞 F} (hx : x ≠ 0) :
    x ∈ 𝔭 ^ vF 𝔭 x ∧ x ∉ 𝔭 ^ (vF 𝔭 x + 1) := by
  have hbdd : BddAbove {e : ℕ | x ∈ 𝔭 ^ e} := by
    have h0 : x ∉ ⨅ n : ℕ, 𝔭 ^ n := by
      rw [Ideal.iInf_pow_eq_bot_of_isDomain 𝔭 h𝔭.ne_top]
      simpa using hx
    simp only [Submodule.mem_iInf, not_forall] at h0
    obtain ⟨n, hn⟩ := h0
    refine ⟨n, fun e he => ?_⟩
    by_contra hlt
    push_neg at hlt
    exact hn (Ideal.pow_le_pow_right hlt.le he)
  refine ⟨?_, fun h => ?_⟩
  · have h1 := Nat.sSup_mem (s := {e : ℕ | x ∈ 𝔭 ^ e}) ⟨0, by simp⟩ hbdd
    exact h1
  · have h2 : vF 𝔭 x + 1 ≤ vF 𝔭 x := le_csSup hbdd h
    omega

/- English proof (translation)
Establish `hkP : extP K 𝔭 ^ k = extP K 𝔭 ^ (k - e) * extP K 𝔭 ^ e`. Rewrite using `[← pow_add, Nat.sub_add_cancel hek]`. Take `⟨J, hJ⟩ : 𝔭 ^ e ∣ Ideal.span {a}` from `Ideal.dvd_span_singleton.mpr ha`. Establish `hJP : J ⊔ 𝔭 = ⊤`. Assume the negation of the conclusion as `hne`.

Establish `hle : J ≤ 𝔭` using `le_sup_left.trans (le_of_eq (h𝔭.eq_of_le hne le_sup_right).symm)`. Apply `ha'` to reduce the goal to its premises. Establish `h1 : a ∈ 𝔭 ^ e * J`. Rewrite using `[← hJ]`. Conclude with `Ideal.mem_span_singleton_self a`.

Rewrite using `[pow_succ]`. Conclude with `Ideal.mul_mono_right hle h1`. Establish `hspan : Ideal.span {algebraMap (𝓞 F) (𝓞 K) a} = extP K 𝔭 ^ e * J.map (algebraMap (𝓞 F) (𝓞 K))`. Establish `h1` using `congrArg (Ideal.map (algebraMap (𝓞 F) (𝓞 K))) hJ`. Rewrite `h1` using `[Ideal.map_span, Set.image_singleton, Ideal.map_mul, Ideal.map_pow]`.

Conclude with `h1`. Establish `hcop : IsCoprime (extP K 𝔭 ^ (k - e)) (J.map (algebraMap (𝓞 F) (𝓞 K)))`. Apply `IsCoprime.pow_left` to reduce the goal to its premises. Rewrite using `[Ideal.isCoprime_iff_sup_eq]`. Establish `h1` using `congrArg (Ideal.map (algebraMap (𝓞 F) (𝓞 K))) hJP`.

Rewrite `h1` using `[Ideal.map_sup, Ideal.map_top]`. Rewrite using `[sup_comm]`. Conclude with `h1`. Establish `hιinj : ∀ x : 𝓞 F, algebraMap (𝓞 F) (𝓞 K) x = 0 → x = 0`. Introduce `x hx`.

Establish `h1 : algebraMap F K (algebraMap (𝓞 F) F x) = 0`. Rewrite using `[← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K, hx, map_zero]`. Rewrite `h1` using `[map_eq_zero_iff _ (algebraMap F K).injective]`. Conclude with `IsFractionRing.injective (𝓞 F) F (by rw [h1, map_zero])`. Establish `ha0 : a ≠ 0` using `fun h => ha' (h ▸ Ideal.zero_mem _)`.

Establish `hPe : extP K 𝔭 ^ e ≠ 0`. Rewrite using `[Ne, Ideal.zero_eq_bot]`. Introduce `h0`. Rewrite `hspan` using `[h0, Ideal.bot_mul, Ideal.span_singleton_eq_bot]`. Conclude with `ha0 (hιinj a hspan)`.

Establish `hdiv : extP K 𝔭 ^ (k - e) * extP K 𝔭 ^ e ∣ (Ideal.span {w} * J.map (algebraMap (𝓞 F) (𝓞 K))) * extP K 𝔭 ^ e`. Rewrite using `[← hkP]`. Establish `h2 : extP K 𝔭 ^ k ∣ Ideal.span {w * algebraMap (𝓞 F) (𝓞 K) a}` using `Ideal.dvd_span_singleton.mpr hw`. Rewrite `h2` using `[← Ideal.span_singleton_mul_span_singleton, hspan, mul_comm (extP K 𝔭 ^ e), ← mul_assoc]`. Conclude with `h2`.

Rewrite `hdiv` using `[mul_dvd_mul_iff_right hPe]`. Conclude with `Ideal.dvd_span_singleton.mp (hcop.dvd_of_dvd_mul_right hdiv)`.
-/
private theorem mem_extP_pow_sub_of_mul_mem {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {a : 𝓞 F} {e k : ℕ}
    (ha : a ∈ 𝔭 ^ e) (ha' : a ∉ 𝔭 ^ (e + 1)) (hek : e ≤ k) {w : 𝓞 K}
    (hw : w * ι a ∈ extP K 𝔭 ^ k) : w ∈ extP K 𝔭 ^ (k - e) := by
  have hkP : extP K 𝔭 ^ k = extP K 𝔭 ^ (k - e) * extP K 𝔭 ^ e := by
    rw [← pow_add, Nat.sub_add_cancel hek]
  obtain ⟨J, hJ⟩ : 𝔭 ^ e ∣ Ideal.span {a} := Ideal.dvd_span_singleton.mpr ha
  have hJP : J ⊔ 𝔭 = ⊤ := by
    by_contra hne
    have hle : J ≤ 𝔭 := le_sup_left.trans (le_of_eq (h𝔭.eq_of_le hne le_sup_right).symm)
    apply ha'
    have h1 : a ∈ 𝔭 ^ e * J := by
      rw [← hJ]
      exact Ideal.mem_span_singleton_self a
    rw [pow_succ]
    exact Ideal.mul_mono_right hle h1
  have hspan : Ideal.span {algebraMap (𝓞 F) (𝓞 K) a} =
      extP K 𝔭 ^ e * J.map (algebraMap (𝓞 F) (𝓞 K)) := by
    have h1 := congrArg (Ideal.map (algebraMap (𝓞 F) (𝓞 K))) hJ
    rw [Ideal.map_span, Set.image_singleton, Ideal.map_mul, Ideal.map_pow] at h1
    exact h1
  have hcop : IsCoprime (extP K 𝔭 ^ (k - e)) (J.map (algebraMap (𝓞 F) (𝓞 K))) := by
    apply IsCoprime.pow_left
    rw [Ideal.isCoprime_iff_sup_eq]
    have h1 := congrArg (Ideal.map (algebraMap (𝓞 F) (𝓞 K))) hJP
    rw [Ideal.map_sup, Ideal.map_top] at h1
    rw [sup_comm]
    exact h1
  have hιinj : ∀ x : 𝓞 F, algebraMap (𝓞 F) (𝓞 K) x = 0 → x = 0 := by
    intro x hx
    have h1 : algebraMap F K (algebraMap (𝓞 F) F x) = 0 := by
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K, hx,
        map_zero]
    rw [map_eq_zero_iff _ (algebraMap F K).injective] at h1
    exact IsFractionRing.injective (𝓞 F) F (by rw [h1, map_zero])
  have ha0 : a ≠ 0 := fun h => ha' (h ▸ Ideal.zero_mem _)
  have hPe : extP K 𝔭 ^ e ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot]
    intro h0
    rw [h0, Ideal.bot_mul, Ideal.span_singleton_eq_bot] at hspan
    exact ha0 (hιinj a hspan)
  have hdiv : extP K 𝔭 ^ (k - e) * extP K 𝔭 ^ e ∣
      (Ideal.span {w} * J.map (algebraMap (𝓞 F) (𝓞 K))) * extP K 𝔭 ^ e := by
    rw [← hkP]
    have h2 : extP K 𝔭 ^ k ∣ Ideal.span {w * algebraMap (𝓞 F) (𝓞 K) a} :=
      Ideal.dvd_span_singleton.mpr hw
    rw [← Ideal.span_singleton_mul_span_singleton, hspan, mul_comm (extP K 𝔭 ^ e),
      ← mul_assoc] at h2
    exact h2
  rw [mul_dvd_mul_iff_right hPe] at hdiv
  exact Ideal.dvd_span_singleton.mp (hcop.dvd_of_dvd_mul_right hdiv)

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Introduce `k hk`. Simplify using `using hk`. Consider the case `@insert i s hi ih`.

Introduce `k hk`. Rewrite `hk` using `[Finset.prod_insert hi]`. Rewrite using `[Finset.sum_insert hi]`. Take `⟨h1, h2⟩` from `mem_pow_vF_not_mem_pow_vF_succ h𝔭 (ha i)`. Distinguish the cases in `hle : vF 𝔭 (a i) ≤ k`.

Establish `h3 : (w * ∏ j ∈ s, ι (a j)) * ι (a i) ∈ extP K 𝔭 ^ k`. Use `hk using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Establish `h4` using `ih (k - vF 𝔭 (a i)) (mem_extP_pow_sub_of_mul_mem h𝔭 h1 h2 hle h3)`. Rewrite `h4` using `[Nat.sub_sub]`. Then use the resulting hypothesis.

Establish `h5 : k - (vF 𝔭 (a i) + ∑ j ∈ s, vF 𝔭 (a j)) = 0` using `by omega`. Rewrite using `[h5, pow_zero, Ideal.one_eq_top]`. Conclude with `Submodule.mem_top`.
-/
private theorem mem_extP_pow_sub_sum_vF_of_mul_prod_mem {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (a : Fin m → 𝓞 F)
    (ha : ∀ i, a i ≠ 0) (w : 𝓞 K) (s : Finset (Fin m)) :
    ∀ k, w * ∏ i ∈ s, ι (a i) ∈ extP K 𝔭 ^ k → w ∈ extP K 𝔭 ^ (k - ∑ i ∈ s, vF 𝔭 (a i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro k hk
    simpa using hk
  | @insert i s hi ih =>
    intro k hk
    rw [Finset.prod_insert hi] at hk
    rw [Finset.sum_insert hi]
    obtain ⟨h1, h2⟩ := mem_pow_vF_not_mem_pow_vF_succ h𝔭 (ha i)
    by_cases hle : vF 𝔭 (a i) ≤ k
    · have h3 : (w * ∏ j ∈ s, ι (a j)) * ι (a i) ∈ extP K 𝔭 ^ k := by
        convert hk using 1
        ring
      have h4 := ih (k - vF 𝔭 (a i)) (mem_extP_pow_sub_of_mul_mem h𝔭 h1 h2 hle h3)
      rwa [Nat.sub_sub] at h4
    · have h5 : k - (vF 𝔭 (a i) + ∑ j ∈ s, vF 𝔭 (a j)) = 0 := by omega
      rw [h5, pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top

/- English proof (translation)
Establish `hk0 : k ≠ 0` using `by omega`. Establish `hPk : extP K 𝔭 ^ k ≤ extP K 𝔭` using `Ideal.pow_le_self hk0`. Establish `hnil : ∀ z ∈ (extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ k)), IsNilpotent z`. Introduce `z hz`. Take `⟨w, rfl⟩` from `Ideal.Quotient.mk_surjective z`.

Establish `hw : w ∈ extP K 𝔭` using `(Ideal.mem_quotient_iff_mem hPk).mp hz`. Conclude with `⟨k, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.pow_mem_pow hw k⟩`. Establish `hmat : Yᴴ * P * diagQ K 𝔭 k a = diagQ K 𝔭 k a * (1 + W * diagQ K 𝔭 k a)`. Rewrite using `[Matrix.mul_assoc, hPY, ← Matrix.mul_assoc, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, ← hW]`. Normalize the expressions using the abelian group laws.

Establish `hdet` using `congrArg Matrix.det hmat`. Simplify using `only [Matrix.det_mul] at hdet`. Establish `hδ : (diagQ K 𝔭 k a).det = Ideal.Quotient.mk (extP K 𝔭 ^ k) (∏ i, ι (a i))`. Simplify using `only [diagQ, Matrix.det_diagonal, map_prod]`. Establish `hu` using `det_one_add_sub_mem hWH`.

Take `⟨w, hw⟩` from `Ideal.Quotient.mk_surjective (Yᴴ.det * P.det - (1 + W * diagQ K 𝔭 k a).det)`. Establish `hx : w * ∏ i, ι (a i) ∈ extP K 𝔭 ^ k`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_mul, hw, ← hδ, sub_mul, hdet]`. Expand and normalize the polynomial expressions, which then agree. Establish `hv : vJof 𝔭 a = ∑ i, vF 𝔭 (a i)` using `rfl`.

Establish `hw1 : w ∈ extP K 𝔭`. Establish `h1` using `mem_extP_pow_sub_sum_vF_of_mul_prod_mem h𝔭 a ha w Finset.univ k hx`. Conclude with `Ideal.pow_le_self (by rw [hv] at hk; omega) h1`. Establish `hsum : Yᴴ.det * P.det - 1 ∈ (extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ k))`. Establish `h2 : Yᴴ.det * P.det - 1 = (Yᴴ.det * P.det - (1 + W * diagQ K 𝔭 k a).det) + ((1 + W * diagQ K 𝔭 k a).det - 1)` using `by ring`.

Rewrite using `[h2]`. Use `Ideal.add_mem _ ?_ hu` and prove the remaining obligations. Rewrite using `[← hw]`. Conclude with `Ideal.mem_map_of_mem _ hw1`. Establish `hunit : IsUnit (Yᴴ.det * P.det)`.

Establish `h3` using `(hnil _ hsum).isUnit_one_add`. Establish `h4 : 1 + (Yᴴ.det * P.det - 1) = Yᴴ.det * P.det` using `by ring`. Rewrite `h3` using `[h4]`. Conclude with `h3`. Conclude with `isUnit_of_mul_isUnit_right hunit`.
-/
theorem isUnit_det_of_witness {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {a : Fin m → 𝓞 F}
    (ha : ∀ i, a i ≠ 0) {k : ℕ} (hk : vJof 𝔭 a + 1 ≤ k)
    {Y P W : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k)}
    (hPY : P * diagQ K 𝔭 k a = diagQ K 𝔭 k a * Y)
    (hW : Yᴴ * diagQ K 𝔭 k a * Y - diagQ K 𝔭 k a = diagQ K 𝔭 k a * W * diagQ K 𝔭 k a)
    (hWH : ∀ i j, (W * diagQ K 𝔭 k a) i j ∈ (extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ k))) :
    IsUnit P.det := by
  classical
  have hk0 : k ≠ 0 := by omega
  have hPk : extP K 𝔭 ^ k ≤ extP K 𝔭 := Ideal.pow_le_self hk0
  have hnil : ∀ z ∈ (extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ k)), IsNilpotent z := by
    intro z hz
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
    have hw : w ∈ extP K 𝔭 := (Ideal.mem_quotient_iff_mem hPk).mp hz
    exact ⟨k, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.pow_mem_pow hw k⟩
  have hmat : Yᴴ * P * diagQ K 𝔭 k a = diagQ K 𝔭 k a * (1 + W * diagQ K 𝔭 k a) := by
    rw [Matrix.mul_assoc, hPY, ← Matrix.mul_assoc, Matrix.mul_add, Matrix.mul_one,
      ← Matrix.mul_assoc, ← hW]
    abel
  have hdet := congrArg Matrix.det hmat
  simp only [Matrix.det_mul] at hdet
  have hδ : (diagQ K 𝔭 k a).det = Ideal.Quotient.mk (extP K 𝔭 ^ k) (∏ i, ι (a i)) := by
    simp only [diagQ, Matrix.det_diagonal, map_prod]
  have hu := det_one_add_sub_mem hWH
  obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective
    (Yᴴ.det * P.det - (1 + W * diagQ K 𝔭 k a).det)
  have hx : w * ∏ i, ι (a i) ∈ extP K 𝔭 ^ k := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, hw, ← hδ, sub_mul, hdet]
    ring
  have hv : vJof 𝔭 a = ∑ i, vF 𝔭 (a i) := rfl
  have hw1 : w ∈ extP K 𝔭 := by
    have h1 := mem_extP_pow_sub_sum_vF_of_mul_prod_mem h𝔭 a ha w Finset.univ k hx
    exact Ideal.pow_le_self (by rw [hv] at hk; omega) h1
  have hsum : Yᴴ.det * P.det - 1 ∈ (extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) := by
    have h2 : Yᴴ.det * P.det - 1 = (Yᴴ.det * P.det - (1 + W * diagQ K 𝔭 k a).det) +
        ((1 + W * diagQ K 𝔭 k a).det - 1) := by ring
    rw [h2]
    refine Ideal.add_mem _ ?_ hu
    rw [← hw]
    exact Ideal.mem_map_of_mem _ hw1
  have hunit : IsUnit (Yᴴ.det * P.det) := by
    have h3 := (hnil _ hsum).isUnit_one_add
    have h4 : 1 + (Yᴴ.det * P.det - 1) = Yᴴ.det * P.det := by ring
    rw [h4] at h3
    exact h3
  exact isUnit_of_mul_isUnit_right hunit

/- English proof (translation)
Simplify using `only [eQ, Matrix.diagonal_mul_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem eQ_mul_self (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : Fin m → 𝓞 F) :
    eQ K 𝔭 k a * eQ K 𝔭 k a = eQ K 𝔭 k a := by
  simp only [eQ, Matrix.diagonal_mul_diagonal]
  congr 1
  funext j
  split_ifs <;> simp

/- English proof (translation)
Simplify using `only [eQ, diagQ, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply]`. Use `split_ifs with h1 h2`. Rewrite using `[one_mul]`. Conclude with `Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ h2)`. Rewrite using `[zero_mul]`.

Conclude with `Ideal.zero_mem _`. Conclude with `Ideal.zero_mem _`.
-/
theorem eQ_mul_diagQ_mem {𝔭 : Ideal (𝓞 F)} {k : ℕ} (a : Fin m → 𝓞 F) (i j : Fin m) :
    (eQ K 𝔭 k a * diagQ K 𝔭 k a) i j ∈ (extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) := by
  simp only [eQ, diagQ, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply]
  split_ifs with h1 h2
  · rw [one_mul]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ h2)
  · rw [zero_mul]
    exact Ideal.zero_mem _
  · exact Ideal.zero_mem _

/- English proof (translation)
Introduce `K F _ _ _ _ _ _ _ hK 𝔭 h𝔭 m a ha k hk Y`. Take `⟨Y', P, W, Z₀, h1, h2, h3, h4, h5, h6, h7⟩` from `hS K F hK 𝔭 h𝔭 m a ha k hk Y`. Use `⟨Y', P, W, Z₀, h1, h2, h3, h4, h5, h6, h7, ?_⟩` and prove the remaining obligations. Use `isUnit_det_of_witness h𝔭 ha (by omega) h2 h3 ?_` and prove the remaining obligations. Introduce `i j`.

Rewrite using `[← h5, show eQ K 𝔭 k a * W * eQ K 𝔭 k a * diagQ K 𝔭 k a = (eQ K 𝔭 k a * W) * (eQ K 𝔭 k a * diagQ K 𝔭 k a) by simp only [Matrix.mul_assoc], Matrix.mul_apply]`. Conclude with `Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (eQ_mul_diagQ_mem a l j)`.
-/
theorem normOnto_of_shape (hS : NormShape) : NormOnto := by
  intro K F _ _ _ _ _ _ _ hK 𝔭 h𝔭 m a ha k hk Y
  obtain ⟨Y', P, W, Z₀, h1, h2, h3, h4, h5, h6, h7⟩ := hS K F hK 𝔭 h𝔭 m a ha k hk Y
  refine ⟨Y', P, W, Z₀, h1, h2, h3, h4, h5, h6, h7, ?_⟩
  refine isUnit_det_of_witness h𝔭 ha (by omega) h2 h3 ?_
  intro i j
  rw [← h5, show eQ K 𝔭 k a * W * eQ K 𝔭 k a * diagQ K 𝔭 k a =
      (eQ K 𝔭 k a * W) * (eQ K 𝔭 k a * diagQ K 𝔭 k a) by simp only [Matrix.mul_assoc],
    Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (eQ_mul_diagQ_mem a l j)

/- English proof (translation)
The claim follows from `discOnto_of_norm hU (normOnto_of_shape hS)`.
-/
theorem discOnto_of_shape (hU : UDModel) (hS : NormShape) : DiscOnto := discOnto_of_norm hU (normOnto_of_shape hS)

end Formalism.L2.SG.Pf.discriminantNormShapes
