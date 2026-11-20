import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBCGlob

namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

variable {H : Type} {f : ℕ}

def phiG (Y : Finset H) (κ : H → H → ℂ) (K : Fin f → H × ℂ → H × ℂ → ℂ) (x x' : crystallineComparison.V f) : ℂ :=
  if Good x ∧ Good x' then phi Y κ K x x' else 0

def phiRG (Y : Finset H) (κ : H → H → ℂ) (U P Q : Fin f → H × ℂ → H × ℂ → ℂ) (x x' : crystallineComparison.V f) : ℂ :=
  if Good x ∧ Good x' then phiR Y κ U P Q x x' else 0

/- English proof (translation)
Unfold `phiG phiRG phiR`. Distinguish the cases in `hx : Good x`. Distinguish the cases in `hx' : Good x'`. Simplify using `only [hx, hx', and_self, if_true]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `[hx, hx']`. Simplify using `[hx]`.
-/
theorem phiG_split (Y : Finset H) (κ : H → H → ℂ) (U P Q : Fin f → H × ℂ → H × ℂ → ℂ) (x x' : crystallineComparison.V f) :
    phiG Y κ U x x' = phiRG Y κ U P Q x x' + phiG Y κ P x x' + conj (phiG Y κ P x' x) - phiG Y κ Q x x' := by
  unfold phiG phiRG phiR
  by_cases hx : Good x
  · by_cases hx' : Good x'
    · simp only [hx, hx', and_self, if_true]
      ring
    · simp [hx, hx']
  · simp [hx]

/- English proof (translation)
Use `set T' := T.filter (fun x => Good x) with hT'`. Establish `hXs : ∀ v, ∀ z ∈ T'.image (fun x => x v), z ≠ 0`. Introduce `v z hz`. Take `⟨x, hx, rfl⟩` from `Finset.mem_image.mp hz`. Conclude with `(Finset.mem_filter.mp hx).2 v`.

Set `kv : Fin f → (H × ℂ ⊕ H × ℂ) → (H × ℂ ⊕ H × ℂ) → ℂ` to `fun v a b => match a, b with`. Consider the case `.inl p, .inl q => U v p q`. Consider the case `.inl p, .inr q => P v p q`. Consider the case `.inr q, .inl p => conj (P v p q)`. Consider the case `.inr p, .inr q => Q v p q`.

Establish `hMv : ∀ v, (Matrix.of fun a b : ((Y ×ˢ T'.image (fun x => x v)).disjSum (Y ×ˢ T'.image (fun x => x v))) => kv v a b).PosSemidef`. Introduce `v`. Establish `h` using `hblk v _ (hXs v)`. Unfold `KB.BlockPSD TB.PSDOn at h`. Use `h using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `a b`. Apply the tactic sequence `rcases a with ⟨a | a, ha⟩ <;> rcases b with ⟨b | b, hb⟩ <;> rfl`. Set `pt : Fin f → (T' × Y) × Bool → (H × ℂ ⊕ H × ℂ)` to `fun v i => if i.2 then Sum.inl (i.1.2.1, i.1.1.1 v) else Sum.inr (i.1.2.1, i.1.1.1 v)`. Establish `hpt : ∀ v i, pt v i ∈ (Y ×ˢ T'.image (fun x => x v)).disjSum (Y ×ˢ T'.image (fun x => x v))`. Introduce `v i`.

Establish `hm : (i.1.2.1, i.1.1.1 v) ∈ Y ×ˢ T'.image (fun x => x v)` using `Finset.mem_product.mpr ⟨i.1.2.2, Finset.mem_image_of_mem _ i.1.1.2⟩`. Distinguish the cases in `hs : i.2`. Simplify using `only [pt, hs, if_true]`. Conclude with `Finset.inl_mem_disjSum.mpr hm`. Simplify using `only [pt, hs]`.

Conclude with `Finset.inr_mem_disjSum.mpr hm`. Set `L : Matrix ((T' × Y) × Bool) ((T' × Y) × Bool) ℂ` to `fun i j => κ i.1.2.1 j.1.2.1 * ∏ v, kv v (pt v i) (pt v j)`. Establish `hL : L.PosSemidef`. Establish `hk : (Matrix.of fun i j : (T' × Y) × Bool => κ i.1.2.1 j.1.2.1).PosSemidef`. Use `hκ.submatrix (fun i : (T' × Y) × Bool => i.1.2)` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Use extensionality with `i j`. Simplify using the standard rewrite rules. Establish `hprod : ∀ s : Finset (Fin f), (Matrix.of fun i j : (T' × Y) × Bool => κ i.1.2.1 j.1.2.1 * ∏ v ∈ s, kv v (pt v i) (pt v j)).PosSemidef`. Introduce `s`.

Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using hk`. Consider the case `insert a s ha ih`. Establish `hA` using `(hMv a).submatrix (fun i : (T' × Y) × Bool => (⟨pt a i, hpt a i⟩ : ((Y ×ˢ T'.image (fun x => x a)).disjSum (Y ×ˢ T'.image (fun x => x a)))))`. Establish `hh` using `hA.hadamard ih`.

Establish `key : (Matrix.of fun i j : (T' × Y) × Bool => κ i.1.2.1 j.1.2.1 * ∏ v ∈ insert a s, kv v (pt v i) (pt v j)) = ((Matrix.of fun a' b' : ((Y ×ˢ T'.image (fun x => x a)).disjSum (Y ×ˢ T'.image (fun x => x a))) => kv a a' b').submatrix (fun i => (⟨pt a i, hpt a i⟩ : ((Y ×ˢ T'.image (f …`. Use extensionality with `i j`. Simplify using `only [Matrix.hadamard_apply, Matrix.submatrix_apply, Matrix.of_apply, Finset.prod_insert ha]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key]`.

Conclude with `hh`. Conclude with `hprod Finset.univ`. Set `sg : Bool → ℂ` to `fun s => if s then 1 else -1`. Set `R : Matrix ((T' × Y) × Bool) T ℂ` to `fun i x => if i.1.1.1 = x.1 then sg i.2 else 0`. Establish `hR0 : ∀ x : T, ¬ Good x.1 → ∀ i, R i x = 0`.

Introduce `x hx i`. Establish `: i.1.1.1 ≠ x.1`. Introduce `he`. Conclude with `hx (he ▸ (Finset.mem_filter.mp i.1.1.2).2)`. Simplify using `[R, this]`.

Establish `hcol : ∀ x : T, ∀ hx : Good x.1, ∀ g : (T' × Y) × Bool → ℂ, ∑ i, R i x * g i = ∑ h : Y, (g ((⟨x.1, Finset.mem_filter.mpr ⟨x.2, hx⟩⟩, h), true) - g ((⟨x.1, Finset.mem_filter.mpr ⟨x.2, hx⟩⟩, h), false))`. Introduce `x hx g`. Rewrite using `[Fintype.sum_prod_type, Fintype.sum_prod_type]`. Rewrite using `[Fintype.sum_eq_single (⟨x.1, Finset.mem_filter.mpr ⟨x.2, hx⟩⟩ : T')]`. Use `Finset.sum_congr rfl fun h _ => ?_` and prove the remaining obligations.

Simplify using `[R, sg, Fintype.sum_bool]`. Expand and normalize the polynomial expressions, which then agree. Introduce `a ha`. Establish `: a.1 ≠ x.1` using `fun he => ha (Subtype.ext he)`. Simplify using `[R, this]`.

Establish `hstar : ∀ i x, star (R i x) = R i x`. Introduce `i x`. Simplify using `only [R, sg]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hconjP : ∀ x y : crystallineComparison.V f, conj (phi Y κ P y x) = ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, conj (P v (h', y v) (h, x v))`.

Introduce `x y`. Unfold `phi`. Simplify using `only [map_sum, map_mul, map_prod]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun h hh => Finset.sum_congr rfl fun h' hh' => ?_` and prove the remaining obligations.

Use `congr 1`. Use `hκ.1.apply ⟨h, hh⟩ ⟨h', hh'⟩` as an intermediate fact. Simplify using `using this`. Unfold `TB.PSDOn`. Establish `hfin` using `hL.conjTranspose_mul_mul_same R`.

Rewrite `hfin` using `[Matrix.mul_assoc]`. Use `hfin using 1` and compare the differences between its conclusion and the goal. Use extensionality with `x y`. Simplify using `only [Matrix.mul_apply, Matrix.conjTranspose_apply, hstar, Matrix.of_apply]`. Distinguish the cases in `hx : Good x.1`.

Distinguish the cases in `hy : Good y.1`. Rewrite using `[hcol x hx]`. Simplify using `only [mul_comm (L _ _) (R _ y), hcol y hy]`. Simplify using `only [phiRG, phiR, hx, hy, and_self, if_true, hconjP]`. Unfold `phi`.

Simplify using `only [← Finset.sum_coe_sort Y]`. Simplify using `only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun h' _ => ?_` and prove the remaining obligations. Simplify using `only [L, pt, kv, if_true, Bool.false_eq_true, if_false]`. Expand and normalize the polynomial expressions, which then agree.

Establish `: ∀ j, R j y = 0` using `hR0 y hy`. Simplify using `[this, phiRG, hy]`. Establish `: ∀ i, R i x = 0` using `hR0 x hx`. Simplify using `[this, phiRG, hx]`.
-/
theorem phiRG_psd (Y : Finset H) (κ : H → H → ℂ) (hκ : TB.PSDOn Y κ) (U P Q : Fin f → H × ℂ → H × ℂ → ℂ)
    (hblk : ∀ v (Xs : Finset ℂ), (∀ x ∈ Xs, x ≠ 0) → KB.BlockPSD (Y ×ˢ Xs) (Y ×ˢ Xs) (U v) (P v) (Q v))
    (T : Finset (crystallineComparison.V f)) : TB.PSDOn T (phiRG Y κ U P Q) := by
  classical
  set T' := T.filter (fun x => Good x) with hT'
  have hXs : ∀ v, ∀ z ∈ T'.image (fun x => x v), z ≠ 0 := by
    intro v z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact (Finset.mem_filter.mp hx).2 v
  let kv : Fin f → (H × ℂ ⊕ H × ℂ) → (H × ℂ ⊕ H × ℂ) → ℂ := fun v a b => match a, b with
    | .inl p, .inl q => U v p q
    | .inl p, .inr q => P v p q
    | .inr q, .inl p => conj (P v p q)
    | .inr p, .inr q => Q v p q
  have hMv : ∀ v, (Matrix.of fun a b : ((Y ×ˢ T'.image (fun x => x v)).disjSum
      (Y ×ˢ T'.image (fun x => x v))) => kv v a b).PosSemidef := by
    intro v
    have h := hblk v _ (hXs v)
    unfold KB.BlockPSD TB.PSDOn at h
    convert h using 1
    ext a b
    rcases a with ⟨a | a, ha⟩ <;> rcases b with ⟨b | b, hb⟩ <;> rfl
  let pt : Fin f → (T' × Y) × Bool → (H × ℂ ⊕ H × ℂ) := fun v i =>
    if i.2 then Sum.inl (i.1.2.1, i.1.1.1 v) else Sum.inr (i.1.2.1, i.1.1.1 v)
  have hpt : ∀ v i, pt v i ∈ (Y ×ˢ T'.image (fun x => x v)).disjSum (Y ×ˢ T'.image (fun x => x v)) := by
    intro v i
    have hm : (i.1.2.1, i.1.1.1 v) ∈ Y ×ˢ T'.image (fun x => x v) :=
      Finset.mem_product.mpr ⟨i.1.2.2, Finset.mem_image_of_mem _ i.1.1.2⟩
    by_cases hs : i.2
    · simp only [pt, hs, if_true]; exact Finset.inl_mem_disjSum.mpr hm
    · simp only [pt, hs]; exact Finset.inr_mem_disjSum.mpr hm
  let L : Matrix ((T' × Y) × Bool) ((T' × Y) × Bool) ℂ := fun i j =>
    κ i.1.2.1 j.1.2.1 * ∏ v, kv v (pt v i) (pt v j)
  have hL : L.PosSemidef := by
    have hk : (Matrix.of fun i j : (T' × Y) × Bool => κ i.1.2.1 j.1.2.1).PosSemidef := by
      have := hκ.submatrix (fun i : (T' × Y) × Bool => i.1.2)
      convert this using 1
      ext i j
      simp
    have hprod : ∀ s : Finset (Fin f), (Matrix.of fun i j : (T' × Y) × Bool =>
        κ i.1.2.1 j.1.2.1 * ∏ v ∈ s, kv v (pt v i) (pt v j)).PosSemidef := by
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using hk
      | insert a s ha ih =>
        have hA := (hMv a).submatrix (fun i : (T' × Y) × Bool => (⟨pt a i, hpt a i⟩ :
          ((Y ×ˢ T'.image (fun x => x a)).disjSum (Y ×ˢ T'.image (fun x => x a)))))
        have hh := hA.hadamard ih
        have key : (Matrix.of fun i j : (T' × Y) × Bool =>
            κ i.1.2.1 j.1.2.1 * ∏ v ∈ insert a s, kv v (pt v i) (pt v j)) =
            ((Matrix.of fun a' b' : ((Y ×ˢ T'.image (fun x => x a)).disjSum
              (Y ×ˢ T'.image (fun x => x a))) => kv a a' b').submatrix
              (fun i => (⟨pt a i, hpt a i⟩ : ((Y ×ˢ T'.image (fun x => x a)).disjSum
                (Y ×ˢ T'.image (fun x => x a)))))
              (fun i => (⟨pt a i, hpt a i⟩ : ((Y ×ˢ T'.image (fun x => x a)).disjSum
                (Y ×ˢ T'.image (fun x => x a)))))).hadamard
            (Matrix.of fun i j : (T' × Y) × Bool => κ i.1.2.1 j.1.2.1 * ∏ v ∈ s, kv v (pt v i) (pt v j)) := by
          ext i j
          simp only [Matrix.hadamard_apply, Matrix.submatrix_apply, Matrix.of_apply, Finset.prod_insert ha]
          ring
        rw [key]
        exact hh
    exact hprod Finset.univ
  let sg : Bool → ℂ := fun s => if s then 1 else -1
  let R : Matrix ((T' × Y) × Bool) T ℂ := fun i x => if i.1.1.1 = x.1 then sg i.2 else 0
  have hR0 : ∀ x : T, ¬ Good x.1 → ∀ i, R i x = 0 := by
    intro x hx i
    have : i.1.1.1 ≠ x.1 := by
      intro he
      exact hx (he ▸ (Finset.mem_filter.mp i.1.1.2).2)
    simp [R, this]
  have hcol : ∀ x : T, ∀ hx : Good x.1, ∀ g : (T' × Y) × Bool → ℂ,
      ∑ i, R i x * g i = ∑ h : Y, (g ((⟨x.1, Finset.mem_filter.mpr ⟨x.2, hx⟩⟩, h), true)
        - g ((⟨x.1, Finset.mem_filter.mpr ⟨x.2, hx⟩⟩, h), false)) := by
    intro x hx g
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    rw [Fintype.sum_eq_single (⟨x.1, Finset.mem_filter.mpr ⟨x.2, hx⟩⟩ : T')]
    · refine Finset.sum_congr rfl fun h _ => ?_
      simp [R, sg, Fintype.sum_bool]
      ring
    · intro a ha
      have : a.1 ≠ x.1 := fun he => ha (Subtype.ext he)
      simp [R, this]
  have hstar : ∀ i x, star (R i x) = R i x := by
    intro i x
    simp only [R, sg]
    split_ifs <;> simp
  have hconjP : ∀ x y : crystallineComparison.V f, conj (phi Y κ P y x) =
      ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, conj (P v (h', y v) (h, x v)) := by
    intro x y
    unfold phi
    simp only [map_sum, map_mul, map_prod]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun h hh => Finset.sum_congr rfl fun h' hh' => ?_
    congr 1
    have := hκ.1.apply ⟨h, hh⟩ ⟨h', hh'⟩
    simpa using this
  unfold TB.PSDOn
  have hfin := hL.conjTranspose_mul_mul_same R
  rw [Matrix.mul_assoc] at hfin
  convert hfin using 1
  ext x y
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hstar, Matrix.of_apply]
  by_cases hx : Good x.1
  · by_cases hy : Good y.1
    · rw [hcol x hx]
      simp only [mul_comm (L _ _) (R _ y), hcol y hy]
      simp only [phiRG, phiR, hx, hy, and_self, if_true, hconjP]
      unfold phi
      simp only [← Finset.sum_coe_sort Y]
      simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun h' _ => ?_
      simp only [L, pt, kv, if_true, Bool.false_eq_true, if_false]
      ring
    · have : ∀ j, R j y = 0 := hR0 y hy
      simp [this, phiRG, hy]
  · have : ∀ i, R i x = 0 := hR0 x hx
    simp [this, phiRG, hx]

/- English proof (translation)
Unfold `phi`. Rewrite using `[Finset.sum_mul]`. Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun h hh => ?_)` and prove the remaining obligations. Rewrite using `[Finset.sum_mul]`. Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun h' hh' => ?_)` and prove the remaining obligations.

Rewrite using `[norm_mul, norm_prod]`. Use `gcongr`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem phi_bound (Y : Finset H) (κ : H → H → ℂ) (K : Fin f → H × ℂ → H × ℂ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (x x' : crystallineComparison.V f) (hK : ∀ v, ∀ h ∈ Y, ∀ h' ∈ Y, ‖K v (h, x v) (h', x' v)‖ ≤ B) :
    ‖phi Y κ K x x'‖ ≤ (∑ h ∈ Y, ∑ h' ∈ Y, ‖κ h h'‖) * B ^ f := by
  unfold phi
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun h hh => ?_)
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun h' hh' => ?_)
  rw [norm_mul, norm_prod]
  gcongr
  calc ∏ v, ‖K v (h, x v) (h', x' v)‖ ≤ ∏ _v : Fin f, B :=
        Finset.prod_le_prod (fun v _ => norm_nonneg _) (fun v _ => hK v h hh h' hh')
    _ = B ^ f := by simp

end

end Formalism.FourierDecayAlt.P.PBC
