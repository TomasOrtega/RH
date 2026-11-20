import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsStrictDom
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPermWOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemIwUIff
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SatPow

noncomputable section

namespace GlobalTheory.CompanionTheory.SatPow.IwFact

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

def UpI (W : Matrix (Fin n) (Fin n) L) : Prop :=
  (∀ a b, b < a → W a b = 0) ∧ (∀ a, W a a = 1) ∧ ∀ a b, Valued.v (W a b) ≤ 1

def IwM (N : Matrix (Fin n) (Fin n) L) : Prop :=
  (∀ a b, Valued.v (N a b) ≤ 1) ∧ (∀ a b, b < a → Valued.v (N a b) < 1) ∧ ∀ a, Valued.v (N a a) = 1

/- English proof (translation)
Use `⟨fun a b h => Matrix.one_apply_ne h.ne', fun a => Matrix.one_apply_eq a, fun a b => ?_⟩` and prove the remaining obligations. Distinguish the cases in `h : a = b`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Matrix.one_apply_ne h]`.
-/
theorem upI_one : UpI (1 : Matrix (Fin n) (Fin n) L) := by
  refine ⟨fun a b h => Matrix.one_apply_ne h.ne', fun a => Matrix.one_apply_eq a, fun a b => ?_⟩
  by_cases h : a = b
  · subst h; simp
  · simp [Matrix.one_apply_ne h]

omit [Valued L (WithZero (Multiplicative ℤ))] in
/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_single a (fun k _ hk => ?_) (by simp)` and prove the remaining obligations. Break down `lt_or_gt_of_ne hk with h | h` into its components or cases. Rewrite using `[hA a k h, zero_mul]`. Rewrite using `[hB k a h, mul_zero]`.
-/
theorem upper_mul_diag {A B : Matrix (Fin n) (Fin n) L} (hA : ∀ a b, b < a → A a b = 0)
    (hB : ∀ a b, b < a → B a b = 0) (a : Fin n) : (A * B) a a = A a a * B a a := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single a (fun k _ hk => ?_) (by simp)
  rcases lt_or_gt_of_ne hk with h | h
  · rw [hA a k h, zero_mul]
  · rw [hB k a h, mul_zero]

omit [Valued L (WithZero (Multiplicative ℤ))] in
/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Break down `lt_or_ge k a with h1 | h1` into its components or cases. Rewrite using `[hA a k h1, zero_mul]`. Rewrite using `[hB k b (lt_of_lt_of_le h h1), mul_zero]`.
-/
theorem upper_mul {A B : Matrix (Fin n) (Fin n) L} (hA : ∀ a b, b < a → A a b = 0)
    (hB : ∀ a b, b < a → B a b = 0) (a b : Fin n) (h : b < a) : (A * B) a b = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge k a with h1 | h1
  · rw [hA a k h1, zero_mul]
  · rw [hB k b (lt_of_lt_of_le h h1), mul_zero]

/- English proof (translation)
Use `⟨upper_mul hA.1 hB.1, fun a => ?_, fun a b => ?_⟩` and prove the remaining obligations. Rewrite using `[upper_mul_diag hA.1 hB.1, hA.2.1, hB.2.1, one_mul]`. Rewrite using `[Matrix.mul_apply]`. Use `Valuation.map_sum_le _ fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`.

Conclude with `(mul_le_of_le_one_right' (hB.2.2 k b)).trans (hA.2.2 a k)`.
-/
theorem UpI.mul {A B : Matrix (Fin n) (Fin n) L} (hA : UpI A) (hB : UpI B) : UpI (A * B) := by
  refine ⟨upper_mul hA.1 hB.1, fun a => ?_, fun a b => ?_⟩
  · rw [upper_mul_diag hA.1 hB.1, hA.2.1, hB.2.1, one_mul]
  · rw [Matrix.mul_apply]
    refine Valuation.map_sum_le _ fun k _ => ?_
    rw [map_mul]
    exact (mul_le_of_le_one_right' (hB.2.2 k b)).trans (hA.2.2 a k)

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `hN`. Establish `hc0 : N c c ≠ 0`. Introduce `h`. Use `h3 c` as an intermediate fact. Rewrite `this` using `[h, map_zero]`.

Conclude with `zero_ne_one this`. Set `x : Fin n → L` to `fun a => if a < c then N a c / N c c else 0`. Establish `hxa : ∀ a, ¬ a < c → x a = 0` using `fun a h => if_neg h`. Establish `hxl : ∀ a, a < c → x a = N a c / N c c` using `fun a h => if_pos h`. Establish `hxv : ∀ a, Valued.v (x a) ≤ 1`.

Introduce `a`. Distinguish the cases in `h : a < c`. Rewrite using `[hxl a h, map_div₀, h3 c, div_one]`. Conclude with `h1 a c`. Rewrite using `[hxa a h, map_zero]`.

Conclude with `zero_le'`. Establish `hxc : x c = 0` using `hxa c (lt_irrefl c)`. Set `R : Matrix (Fin n) (Fin n) L` to `Matrix.vecMulVec x (Pi.single c 1)`. Establish `hR : ∀ a b, R a b = if b = c then x a else 0`. Introduce `a b`.

Simplify using `[R, Matrix.vecMulVec_apply, Pi.single_apply]`. Establish `hRR : R * R = 0`. Use extensionality with `a b`. Rewrite using `[Matrix.mul_apply]`. Simplify using `[hR, hxc]`.

Establish `hRN : ∀ a b, (R * N) a b = x a * N c b`. Introduce `a b`. Rewrite using `[Matrix.mul_apply]`. Simplify using `[hR]`. Establish `hE' : ∀ a b, ((1 - R) * N) a b = N a b - x a * N c b`.

Introduce `a b`. Rewrite using `[Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, hRN]`. Establish `hxN : ∀ a b, Valued.v (x a * N c b) ≤ 1` using `fun a b => by`. Rewrite using `[map_mul]`. Conclude with `(mul_le_of_le_one_right' (h1 c b)).trans (hxv a)`.

Use `⟨1 + R, 1 - R, ⟨fun a b hba => ?_, fun a => ?_, fun a b => ?_⟩, ?_, ⟨fun a b => ?_, fun a b hba => ?_, fun a => ?_⟩, fun a ha => ?_, fun a b hb => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.add_apply, Matrix.one_apply_ne hba.ne', hR, zero_add] split_ifs with h`. Substitute `h` using the available equality. Conclude with `hxa a (not_lt.2 hba.le)`. Both sides reduce to the same expression.

Rewrite using `[Matrix.add_apply, Matrix.one_apply_eq, hR] split_ifs with h`. Substitute `h` using the available equality. Rewrite using `[hxc, add_zero]`. Rewrite using `[add_zero]`. Rewrite using `[Matrix.add_apply]`.

Use `Valuation.map_add_le _ (upI_one.2.2 a b) ?_` and prove the remaining obligations. Rewrite using `[hR]`. Use `split_ifs`. Conclude with `hxv a`. Rewrite using `[map_zero]`.

Conclude with `zero_le'`. Establish `: (1 + R) * (1 - R) = 1 - R * R` using `by noncomm_ring`. Rewrite using `[this, hRR, sub_zero]`. Rewrite using `[hE']`. Conclude with `Valuation.map_sub_le _ (h1 a b) (hxN a b)`.

Rewrite using `[hE']`. Distinguish the cases in `h : a < c`. Use `Valuation.map_sub_lt _ (h2 a b hba) ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `(mul_le_of_le_one_left' (hxv a)).trans_lt (h2 c b (hba.trans h))`.

Rewrite using `[hxa a h, zero_mul, sub_zero]`. Conclude with `h2 a b hba`. Rewrite using `[hE']`. Distinguish the cases in `h : a < c`. Establish `: Valued.v (x a * N c a) < Valued.v (N a a)`.

Rewrite using `[h3 a, map_mul]`. Conclude with `(mul_le_of_le_one_left' (hxv a)).trans_lt (h2 c a h)`. Rewrite using `[Valuation.map_sub_eq_of_lt_left _ this, h3 a]`. Rewrite using `[hxa a h, zero_mul, sub_zero]`. Conclude with `h3 a`.

Rewrite using `[hE', hxl a ha]`. Clear the denominators using the available nonvanishing facts. Simplify using the standard rewrite rules. Rewrite using `[hE', hb, mul_zero, sub_zero]`.
-/
theorem elim_step {N : Matrix (Fin n) (Fin n) L} (hN : IwM N) (c : Fin n) :
    ∃ E E' : Matrix (Fin n) (Fin n) L, UpI E ∧ E * E' = 1 ∧ IwM (E' * N) ∧
      (∀ a, a < c → (E' * N) a c = 0) ∧ ∀ a b, N c b = 0 → (E' * N) a b = N a b := by
  classical
  obtain ⟨h1, h2, h3⟩ := hN
  have hc0 : N c c ≠ 0 := by
    intro h
    have := h3 c
    rw [h, map_zero] at this
    exact zero_ne_one this
  let x : Fin n → L := fun a => if a < c then N a c / N c c else 0
  have hxa : ∀ a, ¬ a < c → x a = 0 := fun a h => if_neg h
  have hxl : ∀ a, a < c → x a = N a c / N c c := fun a h => if_pos h
  have hxv : ∀ a, Valued.v (x a) ≤ 1 := by
    intro a
    by_cases h : a < c
    · rw [hxl a h, map_div₀, h3 c, div_one]; exact h1 a c
    · rw [hxa a h, map_zero]; exact zero_le'
  have hxc : x c = 0 := hxa c (lt_irrefl c)
  let R : Matrix (Fin n) (Fin n) L := Matrix.vecMulVec x (Pi.single c 1)
  have hR : ∀ a b, R a b = if b = c then x a else 0 := by
    intro a b
    simp [R, Matrix.vecMulVec_apply, Pi.single_apply]
  have hRR : R * R = 0 := by
    ext a b
    rw [Matrix.mul_apply]
    simp [hR, hxc]
  have hRN : ∀ a b, (R * N) a b = x a * N c b := by
    intro a b
    rw [Matrix.mul_apply]
    simp [hR]
  have hE' : ∀ a b, ((1 - R) * N) a b = N a b - x a * N c b := by
    intro a b
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, hRN]
  have hxN : ∀ a b, Valued.v (x a * N c b) ≤ 1 := fun a b => by
    rw [map_mul]
    exact (mul_le_of_le_one_right' (h1 c b)).trans (hxv a)
  refine ⟨1 + R, 1 - R, ⟨fun a b hba => ?_, fun a => ?_, fun a b => ?_⟩, ?_, ⟨fun a b => ?_, fun a b hba => ?_, fun a => ?_⟩,
    fun a ha => ?_, fun a b hb => ?_⟩
  · rw [Matrix.add_apply, Matrix.one_apply_ne hba.ne', hR, zero_add]
    split_ifs with h
    · subst h; exact hxa a (not_lt.2 hba.le)
    · rfl
  · rw [Matrix.add_apply, Matrix.one_apply_eq, hR]
    split_ifs with h
    · subst h; rw [hxc, add_zero]
    · rw [add_zero]
  · rw [Matrix.add_apply]
    refine Valuation.map_add_le _ (upI_one.2.2 a b) ?_
    rw [hR]
    split_ifs
    · exact hxv a
    · rw [map_zero]; exact zero_le'
  · have : (1 + R) * (1 - R) = 1 - R * R := by noncomm_ring
    rw [this, hRR, sub_zero]
  · rw [hE']
    exact Valuation.map_sub_le _ (h1 a b) (hxN a b)
  · rw [hE']
    by_cases h : a < c
    · refine Valuation.map_sub_lt _ (h2 a b hba) ?_
      rw [map_mul]
      exact (mul_le_of_le_one_left' (hxv a)).trans_lt (h2 c b (hba.trans h))
    · rw [hxa a h, zero_mul, sub_zero]
      exact h2 a b hba
  · rw [hE']
    by_cases h : a < c
    · have : Valued.v (x a * N c a) < Valued.v (N a a) := by
        rw [h3 a, map_mul]
        exact (mul_le_of_le_one_left' (hxv a)).trans_lt (h2 c a h)
      rw [Valuation.map_sub_eq_of_lt_left _ this, h3 a]
    · rw [hxa a h, zero_mul, sub_zero]
      exact h3 a
  · rw [hE', hxl a ha]
    field_simp
    simp
  · rw [hE', hb, mul_zero, sub_zero]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Conclude with `⟨1, M, upI_one, hM, by simp, fun a b _ h => absurd b.2 (by omega)⟩`. Consider the case `succ k ih`. Take `⟨W, N, hW, hN, hMW, hz⟩` from `ih (by omega)`.

Establish `hcn : n - 1 - k < n` using `by omega`. Take `⟨E, E', hE, hEE, hI, hc, hs⟩` from `elim_step hN ⟨n - 1 - k, hcn⟩`. Use `⟨W * E, E' * N, hW.mul hE, hI, ?_, fun a b hab hb => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc E, hEE, Matrix.one_mul]`. Conclude with `hMW`.

Distinguish the cases in `hbc : b.val = n - 1 - k`. Establish `: b = ⟨n - 1 - k, hcn⟩` using `Fin.ext hbc`. Rewrite `hab`, the goal using `[this]`. Conclude with `hc a hab`. Establish `hcb : (⟨n - 1 - k, hcn⟩ : Fin n) < b`.

Rewrite using `[Fin.lt_def]`. Use `show n - 1 - k < b.val`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hs a b (hz _ b hcb (by omega)), hz a b hab (by omega)]`.
-/
theorem exists_fact {M : Matrix (Fin n) (Fin n) L} (hM : IwM M) (k : ℕ) (hk : k ≤ n) :
    ∃ W N : Matrix (Fin n) (Fin n) L, UpI W ∧ IwM N ∧ M = W * N ∧
      ∀ a b : Fin n, a < b → n ≤ b.val + k → N a b = 0 := by
  induction k with
  | zero =>
    exact ⟨1, M, upI_one, hM, by simp, fun a b _ h => absurd b.2 (by omega)⟩
  | succ k ih =>
    obtain ⟨W, N, hW, hN, hMW, hz⟩ := ih (by omega)
    have hcn : n - 1 - k < n := by omega
    obtain ⟨E, E', hE, hEE, hI, hc, hs⟩ := elim_step hN ⟨n - 1 - k, hcn⟩
    refine ⟨W * E, E' * N, hW.mul hE, hI, ?_, fun a b hab hb => ?_⟩
    · rw [Matrix.mul_assoc, ← Matrix.mul_assoc E, hEE, Matrix.one_mul]
      exact hMW
    · by_cases hbc : b.val = n - 1 - k
      · have : b = ⟨n - 1 - k, hcn⟩ := Fin.ext hbc
        rw [this] at hab ⊢
        exact hc a hab
      · have hcb : (⟨n - 1 - k, hcn⟩ : Fin n) < b := by
          rw [Fin.lt_def]
          show n - 1 - k < b.val
          omega
        rw [hs a b (hz _ b hcb (by omega)), hz a b hab (by omega)]

def tau (σ : L →+* L) (A : Matrix (Fin n) (Fin n) L) : Matrix (Fin n) (Fin n) L :=
  fun a b => σ (A b.rev a.rev)

omit [Valued L (WithZero (Multiplicative ℤ))] in
/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [tau, Matrix.mul_apply, map_sum, map_mul]`. Use `Fintype.sum_equiv Fin.revPerm _ _ fun k => ?_` and prove the remaining obligations. Simplify using `[mul_comm]`.
-/
theorem tau_mul (σ : L →+* L) (A B : Matrix (Fin n) (Fin n) L) : tau σ (A * B) = tau σ B * tau σ A := by
  ext a b
  simp only [tau, Matrix.mul_apply, map_sum, map_mul]
  refine Fintype.sum_equiv Fin.revPerm _ _ fun k => ?_
  simp [mul_comm]

/- English proof (translation)
Establish `hinv : tau σ (g : Matrix (Fin n) (Fin n) L) = (g⁻¹).val`. Use extensionality with `a b`. Conclude with `((GlobalTheory.LGrp.mem_GU_iff σ n g).1 hg a b).symm`. Establish `h1 : tau σ (g : Matrix (Fin n) (Fin n) L) * (g : Matrix (Fin n) (Fin n) L) = 1`. Rewrite using `[hinv, ← Units.val_mul, inv_mul_cancel, Units.val_one]`.

Rewrite `h1` using `[hgW, tau_mul]`. Establish `hup : ∀ a b, b < a → tau σ W a b = 0` using `fun a b h => by show σ (W b.rev a.rev) = 0`. Rewrite using `[hW.1 _ _ (Fin.rev_lt_rev.2 h), map_zero]`. Establish `hlo : ∀ a b, a < b → tau σ Y a b = 0` using `fun a b h => by show σ (Y b.rev a.rev) = 0`. Rewrite using `[hY _ _ (Fin.rev_lt_rev.2 h), map_zero]`.

Establish `hPQ : (tau σ W * W) * (Y * tau σ Y) = 1`. Establish `h2 : tau σ Y * (tau σ W * W * Y) = 1`. Simplify `h1` using `only [Matrix.mul_assoc]`. Establish `h3` using `mul_eq_one_comm.1 h2`. Simplify `h3` using `only [Matrix.mul_assoc]`.

Establish `hQ : Matrix.BlockTriangular (Y * tau σ Y) OrderDual.toDual`. Establish `hb1 : Matrix.BlockTriangular Y OrderDual.toDual` using `fun a b h => hY a b h`. Establish `hb2 : Matrix.BlockTriangular (tau σ Y) OrderDual.toDual` using `fun a b h => hlo a b h`. Conclude with `hb1.mul hb2`. Use `letI : Invertible (Y * tau σ Y) := ⟨tau σ W * W, hPQ, mul_eq_one_comm.1 hPQ⟩`.

Establish `hinvQ` using `Matrix.blockTriangular_inv_of_blockTriangular hQ`. Rewrite `hinvQ` using `[Matrix.inv_eq_left_inv hPQ]`. Use extensionality with `a b`. Break down `lt_trichotomy a b with h | h | h` into its components or cases. Rewrite using `[hinvQ (show OrderDual.toDual b < OrderDual.toDual a from h), Matrix.one_apply_ne h.ne]`.

Substitute `h` using the available equality. Rewrite using `[upper_mul_diag hup hW.1, hW.2.1, mul_one, Matrix.one_apply_eq]`. Use `show σ (W a.rev a.rev) = 1`. Rewrite using `[hW.2.1, map_one]`. Rewrite using `[upper_mul hup hW.1 a b h, Matrix.one_apply_ne h.ne']`.
-/
theorem tau_mul_self {σ : L →+* L} (g : GL (Fin n) L) (hg : g ∈ GU σ n) {W Y : Matrix (Fin n) (Fin n) L}
    (hW : UpI W) (hY : ∀ a b : Fin n, a < b → Y a b = 0) (hgW : (g : Matrix (Fin n) (Fin n) L) = W * Y) :
    tau σ W * W = 1 := by
  have hinv : tau σ (g : Matrix (Fin n) (Fin n) L) = (g⁻¹).val := by
    ext a b
    exact ((GlobalTheory.LGrp.mem_GU_iff σ n g).1 hg a b).symm
  have h1 : tau σ (g : Matrix (Fin n) (Fin n) L) * (g : Matrix (Fin n) (Fin n) L) = 1 := by
    rw [hinv, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [hgW, tau_mul] at h1
  have hup : ∀ a b, b < a → tau σ W a b = 0 := fun a b h => by
    show σ (W b.rev a.rev) = 0
    rw [hW.1 _ _ (Fin.rev_lt_rev.2 h), map_zero]
  have hlo : ∀ a b, a < b → tau σ Y a b = 0 := fun a b h => by
    show σ (Y b.rev a.rev) = 0
    rw [hY _ _ (Fin.rev_lt_rev.2 h), map_zero]
  have hPQ : (tau σ W * W) * (Y * tau σ Y) = 1 := by
    have h2 : tau σ Y * (tau σ W * W * Y) = 1 := by
      simpa only [Matrix.mul_assoc] using h1
    have h3 := mul_eq_one_comm.1 h2
    simpa only [Matrix.mul_assoc] using h3
  have hQ : Matrix.BlockTriangular (Y * tau σ Y) OrderDual.toDual := by
    have hb1 : Matrix.BlockTriangular Y OrderDual.toDual := fun a b h => hY a b h
    have hb2 : Matrix.BlockTriangular (tau σ Y) OrderDual.toDual := fun a b h => hlo a b h
    exact hb1.mul hb2
  letI : Invertible (Y * tau σ Y) := ⟨tau σ W * W, hPQ, mul_eq_one_comm.1 hPQ⟩
  have hinvQ := Matrix.blockTriangular_inv_of_blockTriangular hQ
  rw [Matrix.inv_eq_left_inv hPQ] at hinvQ
  ext a b
  rcases lt_trichotomy a b with h | h | h
  · rw [hinvQ (show OrderDual.toDual b < OrderDual.toDual a from h), Matrix.one_apply_ne h.ne]
  · subst h
    rw [upper_mul_diag hup hW.1, hW.2.1, mul_one, Matrix.one_apply_eq]
    show σ (W a.rev a.rev) = 1
    rw [hW.2.1, map_one]
  · rw [upper_mul hup hW.1 a b h, Matrix.one_apply_ne h.ne']

/- English proof (translation)
Establish `hx0 : Valued.v x ≠ 0` using `(Valuation.ne_zero_iff _).2 hx`. Establish `hy0 : Valued.v y ≠ 0` using `(Valuation.ne_zero_iff _).2 hy`. Unfold `ordL at h`. Rewrite `h` using `[dif_neg hx0, dif_neg hy0]`. Rewrite using `[← WithZero.coe_unzero hx0, ← WithZero.coe_unzero hy0, WithZero.coe_lt_coe]`.

Use `show Multiplicative.toAdd (WithZero.unzero hy0) < Multiplicative.toAdd (WithZero.unzero hx0)`. Use linear arithmetic over natural numbers and integers.
-/
theorem v_lt_of_ordL_lt {x y : L} (hx : x ≠ 0) (hy : y ≠ 0) (h : ordL x < ordL y) :
    Valued.v y < Valued.v x := by
  have hx0 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  have hy0 : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  unfold ordL at h
  rw [dif_neg hx0, dif_neg hy0] at h
  rw [← WithZero.coe_unzero hx0, ← WithZero.coe_unzero hy0, WithZero.coe_lt_coe]
  show Multiplicative.toAdd (WithZero.unzero hy0) < Multiplicative.toAdd (WithZero.unzero hx0)
  omega

/- English proof (translation)
Establish `hd : (t : Matrix (Fin n) (Fin n) L) = Matrix.diagonal fun i => (t : Matrix (Fin n) (Fin n) L) i i`. Use extensionality with `i j`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[Matrix.diagonal_apply_ne _ hij, ht i j hij]`. Establish `hone : (t⁻¹).val * (t : Matrix (Fin n) (Fin n) L) = 1`. Rewrite using `[← Units.val_mul, inv_mul_cancel, Units.val_one]`. Apply the tactic sequence `have hentry : ∀ i j, (t⁻¹).val i j * (t : Matrix (Fin n) (Fin n) L) j j = (1 : Matrix (Fin n) (Fin n) L) i j := by`. Introduce `i j`.

Establish `h` using `congrFun (congrFun hone i) j`. Rewrite `h` using `[hd, Matrix.mul_diagonal]`. Establish `e` using `congrFun (congrFun hd j) j`. Simplify using `using h`. Establish `hne : ∀ i, (t : Matrix (Fin n) (Fin n) L) i i ≠ 0`.

Introduce `i h`. Apply the tactic sequence `have := hentry i i`. Rewrite `this` using `[h, mul_zero, Matrix.one_apply_eq]`. Conclude with `zero_ne_one this`. Establish `hTi : (t⁻¹).val = Matrix.diagonal fun i => ((t : Matrix (Fin n) (Fin n) L) i i)⁻¹`.

Use extensionality with `i j`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Rewrite using `[Matrix.diagonal_apply_eq]`. Conclude with `eq_inv_of_mul_eq_one_left (by rw [hentry, Matrix.one_apply_eq])`.

Rewrite using `[Matrix.diagonal_apply_ne _ hij]`. Apply the tactic sequence `have := hentry i j`. Rewrite `this` using `[Matrix.one_apply_ne hij]`. Conclude with `(mul_eq_zero.1 this).resolve_right (hne j)`. Use `⟨?_, hne a⟩` and prove the remaining obligations.

Establish `h4 : ((t⁻¹).val * Y * t.val) a b = ((t⁻¹).val * Y) a b * (t : Matrix (Fin n) (Fin n) L) b b` using `by conv_lhs => rw [hd]`. Rewrite using `[Matrix.mul_diagonal]`. Rewrite using `[h4, hTi, Matrix.diagonal_mul]`.
-/
theorem diag_conj_apply {t : GL (Fin n) L} (ht : IsDiagM t) (Y : Matrix (Fin n) (Fin n) L) (a b : Fin n) :
    ((t⁻¹).val * Y * t.val) a b = ((t : Matrix (Fin n) (Fin n) L) a a)⁻¹ * Y a b * (t : Matrix (Fin n) (Fin n) L) b b ∧
      (t : Matrix (Fin n) (Fin n) L) a a ≠ 0 := by
  classical
  have hd : (t : Matrix (Fin n) (Fin n) L) = Matrix.diagonal fun i => (t : Matrix (Fin n) (Fin n) L) i i := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.diagonal_apply_ne _ hij, ht i j hij]
  have hone : (t⁻¹).val * (t : Matrix (Fin n) (Fin n) L) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hentry : ∀ i j, (t⁻¹).val i j * (t : Matrix (Fin n) (Fin n) L) j j = (1 : Matrix (Fin n) (Fin n) L) i j := by
    intro i j
    have h := congrFun (congrFun hone i) j
    rw [hd, Matrix.mul_diagonal] at h
    have e := congrFun (congrFun hd j) j
    simpa using h
  have hne : ∀ i, (t : Matrix (Fin n) (Fin n) L) i i ≠ 0 := by
    intro i h
    have := hentry i i
    rw [h, mul_zero, Matrix.one_apply_eq] at this
    exact zero_ne_one this
  have hTi : (t⁻¹).val = Matrix.diagonal fun i => ((t : Matrix (Fin n) (Fin n) L) i i)⁻¹ := by
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq]
      exact eq_inv_of_mul_eq_one_left (by rw [hentry, Matrix.one_apply_eq])
    · rw [Matrix.diagonal_apply_ne _ hij]
      have := hentry i j
      rw [Matrix.one_apply_ne hij] at this
      exact (mul_eq_zero.1 this).resolve_right (hne j)
  refine ⟨?_, hne a⟩
  have h4 : ((t⁻¹).val * Y * t.val) a b = ((t⁻¹).val * Y) a b * (t : Matrix (Fin n) (Fin n) L) b b := by
    conv_lhs => rw [hd]
    rw [Matrix.mul_diagonal]
  rw [h4, hTi, Matrix.diagonal_mul]

/- English proof (translation)
Introduce `L _ _ σ n _ hσv t hD hS i hi`. Take `⟨hi1, hi2⟩` from `(mem_iwU_iff hσv i).1 hi`. Establish `hi3` using `iwU_diag hσv hi`. Take `⟨W, Y, hW, hY, hMW, hz⟩` from `exists_fact (M := ((i : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) ⟨hi1, hi2, hi3⟩ n le_rfl`. Establish `hz' : ∀ a b : Fin n, a < b → Y a b = 0` using `fun a b h => hz a b h (by omega)`.

Establish `hPW : tau σ W * W = 1` using `tau_mul_self (i : GL (Fin n) L) i.2 hW hz' hMW`. Set `Wg : GL (Fin n) L` to `⟨W, tau σ W, mul_eq_one_comm.1 hPW, hPW⟩`. Establish `hWmem : Wg ∈ GU σ n` using `(GlobalTheory.LGrp.mem_GU_iff σ n Wg).2 fun a b => rfl`. Set `u : GU σ n` to `⟨Wg, hWmem⟩`. Set `y : GU σ n` to `u⁻¹ * i`.

Establish `hyval : ((y : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Y` using `by show tau σ W * ((i : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Y`. Rewrite using `[hMW, ← Matrix.mul_assoc, hPW, Matrix.one_mul]`. Establish `hconj : ∀ a b, (((t⁻¹ * y * t : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a b = (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a a)⁻¹ * Y a b * ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) b b`. Introduce `a b`. Rewrite using `[← (diag_conj_apply hD Y a b).1, ← hyval]`.

Both sides reduce to the same expression. Establish `hne : ∀ a, ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a a ≠ 0` using `fun a => (diag_conj_apply hD Y a a).2`. Establish `hlow : ∀ a b : Fin n, b < a → Valued.v ((((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a a)⁻¹ * Y a b * ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) b b) < 1`. Introduce `a b h`. Establish `hlt` using `v_lt_of_ordL_lt (hne a) (hne b) (hS b a h)`.

Establish `hva : Valued.v (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a a) ≠ 0` using `(Valuation.ne_zero_iff _).2 (hne a)`. Rewrite using `[map_mul, map_mul, map_inv₀, mul_comm _ (Valued.v (Y a b)), mul_assoc]`. Use `(mul_le_of_le_one_left' (hY.1 a b)).trans_lt ?_` and prove the remaining obligations. Rewrite using `[inv_mul_lt_iff₀ (zero_lt_iff.2 hva), mul_one]`. Conclude with `hlt`.

Use `⟨u, (mem_iwU_iff hσv u).2 ⟨hW.2.2, fun a b h => ?_⟩, ⟨hW.1, hW.2.1⟩, y, (mem_iwU_iff hσv y).2 ⟨?_, ?_⟩, (mem_iwU_iff hσv _).2 ⟨fun a b => ?_, fun a b h => ?_⟩, ?_⟩` and prove the remaining obligations. Use `show Valued.v (W a b) < 1`. Rewrite using `[hW.1 a b h, map_zero]`. Conclude with `zero_lt_one`. Rewrite using `[hyval]`.

Conclude with `hY.1`. Rewrite using `[hyval]`. Conclude with `hY.2.1`. Rewrite using `[hconj]`. Break down `lt_trichotomy a b with h | h | h` into its components or cases.

Rewrite using `[hz' a b h, mul_zero, zero_mul, map_zero]`. Conclude with `zero_le'`. Substitute `h` using the available equality. Rewrite using `[mul_comm _ (Y a a), mul_assoc, inv_mul_cancel₀ (hne a), mul_one]`. Conclude with `hY.1 a a`.

Conclude with `(hlow a b h).le`. Rewrite using `[hconj]`. Conclude with `hlow a b h`. Use `show i = u * (u⁻¹ * i)`. Simplify using the standard rewrite rules.
-/
theorem iwahori_fact : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ),
    (∀ x, σ (σ x) = x) → (∀ x, Valued.v (σ x) = Valued.v x) → ∀ t : GU σ n, IsDiagM (t : GL (Fin n) L) →
    IsStrictDom (t : GL (Fin n) L) → ∀ i ∈ IwU σ n, ∃ u ∈ IwU σ n, IsUnipU u ∧ ∃ y ∈ IwU σ n,
      t⁻¹ * y * t ∈ IwU σ n ∧ i = u * y := by
  intro L _ _ σ n _ hσv t hD hS i hi
  obtain ⟨hi1, hi2⟩ := (mem_iwU_iff hσv i).1 hi
  have hi3 := iwU_diag hσv hi
  obtain ⟨W, Y, hW, hY, hMW, hz⟩ := exists_fact (M := ((i : GL (Fin n) L) : Matrix (Fin n) (Fin n) L))
    ⟨hi1, hi2, hi3⟩ n le_rfl
  have hz' : ∀ a b : Fin n, a < b → Y a b = 0 := fun a b h => hz a b h (by omega)
  have hPW : tau σ W * W = 1 := tau_mul_self (i : GL (Fin n) L) i.2 hW hz' hMW
  let Wg : GL (Fin n) L := ⟨W, tau σ W, mul_eq_one_comm.1 hPW, hPW⟩
  have hWmem : Wg ∈ GU σ n := (GlobalTheory.LGrp.mem_GU_iff σ n Wg).2 fun a b => rfl
  let u : GU σ n := ⟨Wg, hWmem⟩
  let y : GU σ n := u⁻¹ * i
  have hyval : ((y : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Y := by
    show tau σ W * ((i : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Y
    rw [hMW, ← Matrix.mul_assoc, hPW, Matrix.one_mul]
  have hconj : ∀ a b, (((t⁻¹ * y * t : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a b =
      (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a a)⁻¹ * Y a b *
        ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) b b := by
    intro a b
    rw [← (diag_conj_apply hD Y a b).1, ← hyval]
    rfl
  have hne : ∀ a, ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a a ≠ 0 := fun a =>
    (diag_conj_apply hD Y a a).2
  have hlow : ∀ a b : Fin n, b < a → Valued.v
      ((((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a a)⁻¹ * Y a b *
        ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) b b) < 1 := by
    intro a b h
    have hlt := v_lt_of_ordL_lt (hne a) (hne b) (hS b a h)
    have hva : Valued.v (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a a) ≠ 0 :=
      (Valuation.ne_zero_iff _).2 (hne a)
    rw [map_mul, map_mul, map_inv₀, mul_comm _ (Valued.v (Y a b)), mul_assoc]
    refine (mul_le_of_le_one_left' (hY.1 a b)).trans_lt ?_
    rw [inv_mul_lt_iff₀ (zero_lt_iff.2 hva), mul_one]
    exact hlt
  refine ⟨u, (mem_iwU_iff hσv u).2 ⟨hW.2.2, fun a b h => ?_⟩, ⟨hW.1, hW.2.1⟩, y,
    (mem_iwU_iff hσv y).2 ⟨?_, ?_⟩, (mem_iwU_iff hσv _).2 ⟨fun a b => ?_, fun a b h => ?_⟩, ?_⟩
  · show Valued.v (W a b) < 1
    rw [hW.1 a b h, map_zero]
    exact zero_lt_one
  · rw [hyval]; exact hY.1
  · rw [hyval]; exact hY.2.1
  · rw [hconj]
    rcases lt_trichotomy a b with h | h | h
    · rw [hz' a b h, mul_zero, zero_mul, map_zero]; exact zero_le'
    · subst h
      rw [mul_comm _ (Y a a), mul_assoc, inv_mul_cancel₀ (hne a), mul_one]
      exact hY.1 a a
    · exact (hlow a b h).le
  · rw [hconj]; exact hlow a b h
  · show i = u * (u⁻¹ * i)
    simp

end GlobalTheory.CompanionTheory.SatPow.IwFact

end
