import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Formalism.MainNotions.G

variable {W Q : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Q] [Algebra W Q] [IsFractionRing W Q]
  (ϖ : W) (hϖ : Irreducible ϖ)

local notation "π" => algebraMap W Q ϖ

include hϖ

/- English proof (translation)
The claim follows from `(map_ne_zero_iff _ (IsFractionRing.injective W Q)).mpr hϖ.ne_zero`.
-/
theorem pi_ne : π ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective W Q)).mpr hϖ.ne_zero

/- English proof (translation)
Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := W) q`. Take `⟨N, hN⟩` from `IsDiscreteValuationRing.associated_pow_irreducible (nonZeroDivisors.ne_zero hb) hϖ`. Take `⟨u, hu⟩` from `hN`. Use `⟨N, fun M hM => ⟨ϖ ^ (M - N) * a * u, ?_⟩⟩` and prove the remaining obligations. Establish `hb0 : algebraMap W Q b ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective W Q)).mpr (nonZeroDivisors.ne_zero hb)`.

Establish `h1 : algebraMap W Q b * algebraMap W Q u = π ^ N` using `by rw [← map_mul, hu, map_pow]`. Rewrite using `[map_mul, map_mul, map_pow]`. Establish `h2 : π ^ M = π ^ (M - N) * π ^ N` using `by rw [← pow_add, Nat.sub_add_cancel hM]`. Rewrite using `[h2, ← h1]`. Clear the denominators using the available nonvanishing facts.
-/
theorem exists_den (q : Q) : ∃ N : ℕ, ∀ M, N ≤ M → π ^ M * q ∈ (algebraMap W Q).range := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := W) q
  obtain ⟨N, hN⟩ := IsDiscreteValuationRing.associated_pow_irreducible (nonZeroDivisors.ne_zero hb) hϖ
  obtain ⟨u, hu⟩ := hN
  refine ⟨N, fun M hM => ⟨ϖ ^ (M - N) * a * u, ?_⟩⟩
  have hb0 : algebraMap W Q b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective W Q)).mpr (nonZeroDivisors.ne_zero hb)
  have h1 : algebraMap W Q b * algebraMap W Q u = π ^ N := by rw [← map_mul, hu, map_pow]
  rw [map_mul, map_mul, map_pow]
  have h2 : π ^ M = π ^ (M - N) * π ^ N := by rw [← pow_add, Nat.sub_add_cancel hM]
  rw [h2, ← h1]
  field_simp

/- English proof (translation)
Use `choose N hN using fun i => exists_den (Q := Q) ϖ hϖ (q i)`. Conclude with `⟨∑ i, N i, fun i => hN i _ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))⟩`.
-/
theorem exists_den_fin {ι : Type} [Fintype ι] (q : ι → Q) : ∃ N : ℕ, ∀ i, π ^ N * q i ∈ (algebraMap W Q).range := by
  choose N hN using fun i => exists_den (Q := Q) ϖ hϖ (q i)
  exact ⟨∑ i, N i, fun i => hN i _ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))⟩

/- English proof (translation)
Establish `hp` using `pi_ne (Q := Q) ϖ hϖ`. Set `J : Ideal W` to `{ carrier := {a | ∃ x ∈ I, algebraMap W Q a = π ^ N * x} add_mem' := by`. Introduce and unpack `a b ⟨x, hx, h1⟩ ⟨y, hy, h2⟩`. Conclude with `⟨x + y, I.add_mem hx hy, by rw [map_add, h1, h2, mul_add]⟩`. Use the proof step `zero_mem' := ⟨0, I.zero_mem, by simp⟩`.

Use the proof step `smul_mem' := by`. Introduce and unpack `c a ⟨x, hx, h1⟩`. Conclude with `⟨c • x, I.smul_mem c hx, by rw [smul_eq_mul, map_mul, h1, Algebra.smul_def]; ring⟩ }`. Establish `hJ : J ≠ ⊥`. Take `⟨x, hx, hx0⟩` from `h0`.

Take `⟨a, ha⟩` from `hN x hx`. Introduce `hb`. Establish `: a ∈ J` using `⟨x, hx, ha⟩`. Rewrite `this` using `[hb, Ideal.mem_bot]`. Rewrite `ha` using `[this, map_zero]`.

Conclude with `(mul_ne_zero (pow_ne_zero _ hp) hx0) ha.symm`. Take `⟨m, hm⟩` from `IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hJ hϖ`. Use `⟨(m : ℤ) - N, ?_, fun x hx => ?_⟩` and prove the remaining obligations. Establish `: ϖ ^ m ∈ J` using `by rw [hm]; exact Ideal.mem_span_singleton_self _`. Take `⟨x, hx, h1⟩` from `this`.

Establish `: π ^ ((m : ℤ) - N) = x`. Rewrite using `[zpow_sub₀ hp, zpow_natCast, zpow_natCast, ← map_pow, h1]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`. Conclude with `hx`.

Take `⟨a, ha⟩` from `hN x hx`. Establish `: a ∈ J` using `⟨x, hx, ha⟩`. Rewrite `this` using `[hm, Ideal.mem_span_singleton]`. Take `⟨b, rfl⟩` from `this`. Use `⟨b, ?_⟩` and prove the remaining obligations.

Rewrite using `[zpow_sub₀ hp, zpow_natCast, zpow_natCast]`. Rewrite `ha` using `[map_mul, map_pow]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[mul_comm x, ← ha]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_gen_pow (I : Submodule W Q) (h0 : ∃ x ∈ I, x ≠ 0) (N : ℕ)
    (hN : ∀ x ∈ I, π ^ N * x ∈ (algebraMap W Q).range) :
    ∃ n : ℤ, π ^ n ∈ I ∧ ∀ x ∈ I, ∃ a : W, x = algebraMap W Q a * π ^ n := by
  have hp := pi_ne (Q := Q) ϖ hϖ
  let J : Ideal W :=
    { carrier := {a | ∃ x ∈ I, algebraMap W Q a = π ^ N * x}
      add_mem' := by
        rintro a b ⟨x, hx, h1⟩ ⟨y, hy, h2⟩
        exact ⟨x + y, I.add_mem hx hy, by rw [map_add, h1, h2, mul_add]⟩
      zero_mem' := ⟨0, I.zero_mem, by simp⟩
      smul_mem' := by
        rintro c a ⟨x, hx, h1⟩
        exact ⟨c • x, I.smul_mem c hx, by rw [smul_eq_mul, map_mul, h1, Algebra.smul_def]; ring⟩ }
  have hJ : J ≠ ⊥ := by
    obtain ⟨x, hx, hx0⟩ := h0
    obtain ⟨a, ha⟩ := hN x hx
    intro hb
    have : a ∈ J := ⟨x, hx, ha⟩
    rw [hb, Ideal.mem_bot] at this
    rw [this, map_zero] at ha
    exact (mul_ne_zero (pow_ne_zero _ hp) hx0) ha.symm
  obtain ⟨m, hm⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hJ hϖ
  refine ⟨(m : ℤ) - N, ?_, fun x hx => ?_⟩
  · have : ϖ ^ m ∈ J := by rw [hm]; exact Ideal.mem_span_singleton_self _
    obtain ⟨x, hx, h1⟩ := this
    have : π ^ ((m : ℤ) - N) = x := by
      rw [zpow_sub₀ hp, zpow_natCast, zpow_natCast, ← map_pow, h1]
      field_simp
    rw [this]; exact hx
  · obtain ⟨a, ha⟩ := hN x hx
    have : a ∈ J := ⟨x, hx, ha⟩
    rw [hm, Ideal.mem_span_singleton] at this
    obtain ⟨b, rfl⟩ := this
    refine ⟨b, ?_⟩
    rw [zpow_sub₀ hp, zpow_natCast, zpow_natCast]
    rw [map_mul, map_pow] at ha
    field_simp
    rw [mul_comm x, ← ha]; ring

variable {k : ℕ}

def tailL (L : Submodule W (Fin k → Q)) (c : ℕ) : Submodule W (Fin k → Q) where
  carrier := {y | y ∈ L ∧ ∀ i : Fin k, i.val < c → y i = 0}
  add_mem' := by
    rintro a b ⟨h1, h2⟩ ⟨h3, h4⟩
    exact ⟨L.add_mem h1 h3, fun i hi => by rw [Pi.add_apply, h2 i hi, h4 i hi, add_zero]⟩
  zero_mem' := ⟨L.zero_mem, fun _ _ => rfl⟩
  smul_mem' := by
    rintro r a ⟨h1, h2⟩
    exact ⟨L.smul_mem r h1, fun i hi => by rw [Pi.smul_apply, h2 i hi, smul_zero]⟩

/- English proof (translation)
Establish `hp` using `pi_ne (Q := Q) ϖ hϖ`. Take `⟨g, hg, rfl⟩` from `hL`. Take `⟨N, hN⟩` from `exists_den_fin (Q := Q) ϖ hϖ (fun x : Fin k × Fin k => g x.1 x.2)`. Establish `hbd : ∀ y ∈ colSpan W g, ∀ i, π ^ N * y i ∈ (algebraMap W Q).range`. Introduce `y hy i`.

Unfold `colSpan at hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy => obtain ⟨c, rfl⟩ := hy`. Conclude with `hN (i, c)`. Consider the case `zero => exact ⟨0, by simp⟩`.

Consider the case `add y z _ _ h1 h2`. Rewrite using `[Pi.add_apply, mul_add]`. Conclude with `(algebraMap W Q).range.add_mem h1 h2`. Consider the case `smul r y _ h1`. Rewrite using `[Pi.smul_apply, Algebra.smul_def, mul_left_comm]`.

Conclude with `(algebraMap W Q).range.mul_mem ⟨r, rfl⟩ h1`. Take `⟨N', hN'⟩` from `exists_den_fin (Q := Q) ϖ hϖ (fun x : Fin k × Fin k => g⁻¹ x.1 x.2)`. Establish `hunit : ∀ c : Fin k, (π ^ N') • (Pi.single c (1 : Q) : Fin k → Q) ∈ colSpan W g`. Introduce `c`. Use `choose a ha using fun j : Fin k => hN' (j, c)`.

Establish `: (π ^ N') • (Pi.single c (1 : Q) : Fin k → Q) = ∑ j, a j • (fun i => g i j)`. Use function extensionality and compare the values at `i`. Rewrite using `[Finset.sum_apply]`. Simplify using `only [Pi.smul_apply, Algebra.smul_def, ha, smul_eq_mul]`. Establish `h1 : (g * g⁻¹) i c = (1 : Matrix (Fin k) (Fin k) Q) i c` using `by rw [Matrix.mul_nonsing_inv g hg]`.

Rewrite `h1` using `[Matrix.mul_apply]`. Establish `h2 : ∑ j, π ^ N' * g⁻¹ j c * g i j = π ^ N' * ∑ j, g i j * g⁻¹ j c`. Rewrite using `[Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring`. Rewrite using `[h2, h1, Matrix.one_apply, Pi.single_apply]`. Apply the tactic sequence `by_cases hic : i = c <;> simp [hic]`.

Rewrite using `[this]`. Conclude with `Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)`. Establish `hgen : ∀ c : Fin k, ∃ n : ℤ, (∃ x ∈ tailL (colSpan W g) c.val, x c = π ^ n) ∧ ∀ y ∈ tailL (colSpan W g) c.val, ∃ a : W, y c = algebraMap W Q a * π ^ n`. Introduce `c`. Take `⟨n, h1, h2⟩` from `exists_gen_pow (Q := Q) ϖ hϖ ((tailL (colSpan W g) c.val).map (LinearMap.proj (R := W) (φ := fun _ : Fin k => Q) c)) ⟨π ^ N', ⟨_, ⟨hunit c, fun i hi => by`.

Rewrite using `[Pi.smul_apply, Pi.single_eq_of_ne (Fin.ne_of_lt hi), smul_zero]⟩, by simp⟩, pow_ne_zero _ hp⟩ N`. Use the proof step `(by rintro _ ⟨y, hy, rfl⟩; exact hbd y hy.1 c)`. Take `⟨x, hx, hxc⟩` from `h1`. Conclude with `⟨n, ⟨x, hx, hxc⟩, fun y hy => h2 _ ⟨y, hy, rfl⟩⟩`. Use `choose n hx hy using hgen`.

Use `choose x hxm hxc using hx`. Use `⟨fun i c => x c i, n, fun i j hij => (hxm j).2 i hij, fun a => hxc a, ?_⟩` and prove the remaining obligations. Apply `le_antisymm` to reduce the goal to its premises. Establish `key : ∀ d : ℕ, ∀ y ∈ colSpan W g, (∀ i : Fin k, i.val + d < k → y i = 0) → y ∈ colSpan W (fun i c => x c i)`. Introduce `d`.

Proceed by induction on `d with`. Consider the case `zero`. Introduce `y _ h0`. Establish `: y = 0` using `funext fun i => h0 i (by simpa using i.2)`. Rewrite using `[this]`.

Conclude with `Submodule.zero_mem _`. Consider the case `succ d ih`. Introduce `y hyL h0`. Distinguish the cases in `hd : d < k`. Set `c : Fin k` to `⟨k - (d + 1), by omega⟩`.

Establish `hyt : y ∈ tailL (colSpan W g) c.val` using `⟨hyL, fun i hi => h0 i (by`. Establish `: i.val < k - (d + 1)` using `hi`. Use the proof step `omega)⟩`. Take `⟨a, ha⟩` from `hy c y hyt`. Establish `h2 : y - a • x c ∈ colSpan W (fun i c => x c i)`.

Use `ih _ (Submodule.sub_mem _ hyL (Submodule.smul_mem _ _ (hxm c).1)) fun i hi => ?_` and prove the remaining obligations. Rewrite using `[Pi.sub_apply, Pi.smul_apply, Algebra.smul_def]`. Distinguish the cases in `hic : i.val < c.val`. Rewrite using `[hyt.2 i hic, (hxm c).2 i hic, mul_zero, sub_zero]`. Establish `: i = c` using `Fin.ext (by`.

Establish `h3 : c.val = k - (d + 1)` using `rfl`. Use the proof step `omega)`. Rewrite using `[this, ha, hxc c, sub_self]`. Establish `h3 : y = (y - a • x c) + a • x c` using `by abel`. Rewrite using `[h3]`.

Conclude with `Submodule.add_mem _ h2 (Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩))`. Conclude with `ih y hyL fun i hi => absurd hi (by omega)`. Conclude with `fun y hyL => key k y hyL fun i hi => absurd hi (by omega)`. Unfold `colSpan`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨c, rfl⟩`. Conclude with `(hxm c).1`.
-/
theorem hermite (L : Submodule W (Fin k → Q)) (hL : IsLattice W L) :
    ∃ (A : Matrix (Fin k) (Fin k) Q) (n : Fin k → ℤ), (∀ i j, i < j → A i j = 0) ∧ (∀ a, A a a = π ^ n a) ∧
      L = colSpan W A := by
  classical
  have hp := pi_ne (Q := Q) ϖ hϖ
  obtain ⟨g, hg, rfl⟩ := hL

  obtain ⟨N, hN⟩ := exists_den_fin (Q := Q) ϖ hϖ (fun x : Fin k × Fin k => g x.1 x.2)
  have hbd : ∀ y ∈ colSpan W g, ∀ i, π ^ N * y i ∈ (algebraMap W Q).range := by
    intro y hy i
    unfold colSpan at hy
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨c, rfl⟩ := hy; exact hN (i, c)
    | zero => exact ⟨0, by simp⟩
    | add y z _ _ h1 h2 =>
      rw [Pi.add_apply, mul_add]; exact (algebraMap W Q).range.add_mem h1 h2
    | smul r y _ h1 =>
      rw [Pi.smul_apply, Algebra.smul_def, mul_left_comm]
      exact (algebraMap W Q).range.mul_mem ⟨r, rfl⟩ h1

  obtain ⟨N', hN'⟩ := exists_den_fin (Q := Q) ϖ hϖ (fun x : Fin k × Fin k => g⁻¹ x.1 x.2)
  have hunit : ∀ c : Fin k, (π ^ N') • (Pi.single c (1 : Q) : Fin k → Q) ∈ colSpan W g := by
    intro c
    choose a ha using fun j : Fin k => hN' (j, c)
    have : (π ^ N') • (Pi.single c (1 : Q) : Fin k → Q) = ∑ j, a j • (fun i => g i j) := by
      funext i
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, Algebra.smul_def, ha, smul_eq_mul]
      have h1 : (g * g⁻¹) i c = (1 : Matrix (Fin k) (Fin k) Q) i c := by rw [Matrix.mul_nonsing_inv g hg]
      rw [Matrix.mul_apply] at h1
      have h2 : ∑ j, π ^ N' * g⁻¹ j c * g i j = π ^ N' * ∑ j, g i j * g⁻¹ j c := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      rw [h2, h1, Matrix.one_apply, Pi.single_apply]
      by_cases hic : i = c <;> simp [hic]
    rw [this]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

  have hgen : ∀ c : Fin k, ∃ n : ℤ, (∃ x ∈ tailL (colSpan W g) c.val, x c = π ^ n) ∧
      ∀ y ∈ tailL (colSpan W g) c.val, ∃ a : W, y c = algebraMap W Q a * π ^ n := by
    intro c
    obtain ⟨n, h1, h2⟩ := exists_gen_pow (Q := Q) ϖ hϖ
      ((tailL (colSpan W g) c.val).map (LinearMap.proj (R := W) (φ := fun _ : Fin k => Q) c))
      ⟨π ^ N', ⟨_, ⟨hunit c, fun i hi => by
        rw [Pi.smul_apply, Pi.single_eq_of_ne (Fin.ne_of_lt hi), smul_zero]⟩, by simp⟩, pow_ne_zero _ hp⟩ N
      (by rintro _ ⟨y, hy, rfl⟩; exact hbd y hy.1 c)
    obtain ⟨x, hx, hxc⟩ := h1
    exact ⟨n, ⟨x, hx, hxc⟩, fun y hy => h2 _ ⟨y, hy, rfl⟩⟩
  choose n hx hy using hgen
  choose x hxm hxc using hx
  refine ⟨fun i c => x c i, n, fun i j hij => (hxm j).2 i hij, fun a => hxc a, ?_⟩
  apply le_antisymm
  · have key : ∀ d : ℕ, ∀ y ∈ colSpan W g, (∀ i : Fin k, i.val + d < k → y i = 0) →
        y ∈ colSpan W (fun i c => x c i) := by
      intro d
      induction d with
      | zero =>
        intro y _ h0
        have : y = 0 := funext fun i => h0 i (by simpa using i.2)
        rw [this]; exact Submodule.zero_mem _
      | succ d ih =>
        intro y hyL h0
        by_cases hd : d < k
        · let c : Fin k := ⟨k - (d + 1), by omega⟩
          have hyt : y ∈ tailL (colSpan W g) c.val := ⟨hyL, fun i hi => h0 i (by
            have : i.val < k - (d + 1) := hi
            omega)⟩
          obtain ⟨a, ha⟩ := hy c y hyt
          have h2 : y - a • x c ∈ colSpan W (fun i c => x c i) := by
            refine ih _ (Submodule.sub_mem _ hyL (Submodule.smul_mem _ _ (hxm c).1)) fun i hi => ?_
            rw [Pi.sub_apply, Pi.smul_apply, Algebra.smul_def]
            by_cases hic : i.val < c.val
            · rw [hyt.2 i hic, (hxm c).2 i hic, mul_zero, sub_zero]
            · have : i = c := Fin.ext (by
                have h3 : c.val = k - (d + 1) := rfl
                omega)
              rw [this, ha, hxc c, sub_self]
          have h3 : y = (y - a • x c) + a • x c := by abel
          rw [h3]
          exact Submodule.add_mem _ h2 (Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩))
        · exact ih y hyL fun i hi => absurd hi (by omega)
    exact fun y hyL => key k y hyL fun i hi => absurd hi (by omega)
  · unfold colSpan
    rw [Submodule.span_le]
    rintro _ ⟨c, rfl⟩
    exact (hxm c).1

end Formalism.BasicNotions.Examples₂.NZ
