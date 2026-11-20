import Development.WeilBound.ThetaLifts.Reductions.SiegelMod
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore

set_option linter.unusedSectionVars false

noncomputable section

open Topology Set Matrix
open Formalism.UG (cT cT_mul cT_one)

namespace PositivityTheory.ThKR.Sieg

section Alg

variable {R : Type} [CommRing R] {s : R →+* R} {n k : ℕ} {J : Matrix (Fin n) (Fin n) R} {X Y : Matrix (Fin n) (Fin k) R}

/- English proof (translation)
Establish `key : ∀ m (i j : Fin k), j.val < i.val + m → ((B - 1) ^ m) i j = 0`. Introduce `m`. Proceed by induction on `m with`. Consider the case `zero`. Introduce `i j hij`.

Rewrite using `[pow_zero, Matrix.one_apply_ne]`. Introduce `e`. Substitute `e` using the available equality. Use linear arithmetic over natural numbers and integers. Consider the case `succ m ih`.

Introduce `i j hij`. Rewrite using `[pow_succ, Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun l _ => ?_` and prove the remaining obligations. Distinguish the cases in `hl : l.val < i.val + m`. Rewrite using `[ih i l hl, zero_mul]`.

Establish `hjl : j.val ≤ l.val` using `by omega`. Break down `hjl.lt_or_eq with h' | h'` into its components or cases. Establish `hne : l ≠ j` using `fun e => by rw [e] at h'; exact lt_irrefl _ h'`. Rewrite using `[Matrix.sub_apply, hB (show id j < id l from h'), Matrix.one_apply_ne hne, sub_zero, mul_zero]`. Establish `e : l = j` using `Fin.ext h'.symm`.

Rewrite using `[e, Matrix.sub_apply, hd, Matrix.one_apply_eq, sub_self, mul_zero]`. Use extensionality with `i j`. Rewrite using `[key k i j (by omega), Matrix.zero_apply]`.
-/
theorem sub_one_pow_eq_zero {B : Matrix (Fin k) (Fin k) R} (hB : B.BlockTriangular id) (hd : ∀ i, B i i = 1) :
    (B - 1) ^ k = 0 := by
  have key : ∀ m (i j : Fin k), j.val < i.val + m → ((B - 1) ^ m) i j = 0 := by
    intro m
    induction m with
    | zero =>
      intro i j hij
      rw [pow_zero, Matrix.one_apply_ne]
      intro e
      subst e
      omega
    | succ m ih =>
      intro i j hij
      rw [pow_succ, Matrix.mul_apply]
      refine Finset.sum_eq_zero fun l _ => ?_
      by_cases hl : l.val < i.val + m
      · rw [ih i l hl, zero_mul]
      · have hjl : j.val ≤ l.val := by omega
        rcases hjl.lt_or_eq with h' | h'
        · have hne : l ≠ j := fun e => by rw [e] at h'; exact lt_irrefl _ h'
          rw [Matrix.sub_apply, hB (show id j < id l from h'), Matrix.one_apply_ne hne, sub_zero, mul_zero]
        · have e : l = j := Fin.ext h'.symm
          rw [e, Matrix.sub_apply, hd, Matrix.one_apply_eq, sub_self, mul_zero]
  ext i j
  rw [key k i j (by omega), Matrix.zero_apply]

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => rw [pow_zero, pow_zero, cT_one]`. Consider the case `succ m ih => rw [pow_succ, cT_mul, ih, pow_succ']`.
-/
theorem cT_pow (P : Matrix (Fin k) (Fin k) R) (m : ℕ) : cT s (P ^ m) = cT s P ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, cT_one]
  | succ m ih => rw [pow_succ, cT_mul, ih, pow_succ']

/- English proof (translation)
Take `⟨-, h2, h3, h4⟩` from `h.par hU hB`. Use `set Q := cT s X * J * (U * Y) with hQdef`. Establish `hP : IsNilpotent (cT s (B - 1))` using `⟨k, by rw [← cT_pow, sub_one_pow_eq_zero hBt hd, cT_zero]⟩`. Establish `hcB : cT s B = 1 + cT s (B - 1)` using `by rw [cT_sub, cT_one]; abel`. Establish `hQ1 : Q - 1 = -(Q * cT s (B - 1))`.

Establish `e` using `h3`. Rewrite `e` using `[hcB, Matrix.mul_add, Matrix.mul_one]`. Rewrite using `[eq_neg_iff_add_eq_zero, sub_add_eq_add_sub, e, sub_self]`. Establish `hcomm : Commute Q (cT s (B - 1))`. Rewrite using `[cT_sub, cT_one]`.

Conclude with `(show Commute Q (cT s B) from h3.trans h2.symm).sub_right (Commute.one_right Q)`. Establish `hQn : IsNilpotent (Q - 1)`. Rewrite using `[hQ1]`. Conclude with `(hcomm.isNilpotent_mul_left hP).neg`. Take `⟨a, ha⟩` from `hQn`.

Establish `hXN : cT s X * J * (U - 1) = (Q - 1) * (cT s X * J)`. Rewrite using `[Matrix.mul_sub, Matrix.mul_one, h4, Matrix.sub_mul, Matrix.one_mul]`. Establish `hMN : ∀ m : ℕ, cT s X * J * (U - 1) ^ m = (Q - 1) ^ m * (cT s X * J)`. Introduce `m`. Proceed by induction on `m with`.

Consider the case `zero => rw [pow_zero, pow_zero, Matrix.mul_one, Matrix.one_mul]`. Consider the case `succ m ih => rw [pow_succ', ← Matrix.mul_assoc, hXN, Matrix.mul_assoc, ih, ← Matrix.mul_assoc, ← pow_succ']`. Establish `hNX1 : (U - 1) * X = X * (B - 1)`. Rewrite using `[Matrix.sub_mul, hB, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one]`. Establish `hNX : ∀ m : ℕ, (U - 1) ^ m * X = X * (B - 1) ^ m`.

Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => rw [pow_zero, pow_zero, Matrix.one_mul, Matrix.mul_one]`. Consider the case `succ m ih => rw [pow_succ, Matrix.mul_assoc, hNX1, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, ← pow_succ]`. Establish `h0 : cT s X * J * (U - 1) ^ a = 0` using `by rw [hMN, ha, Matrix.zero_mul]`.

Use `⟨k + (a + 1), ?_⟩` and prove the remaining obligations. Rewrite using `[pow_add, pow_succ', hA _ h0, ← Matrix.mul_assoc, hNX, sub_one_pow_eq_zero hBt hd, Matrix.mul_zero, Matrix.zero_mul]`.
-/
theorem Fr.isNilpotent_sub_one (h : Fr s J X Y) {U : Matrix (Fin n) (Fin n) R} (hU : cT s U * J * U = J)
    {B : Matrix (Fin k) (Fin k) R} (hB : U * X = X * B) (hBt : B.BlockTriangular id) (hd : ∀ i, B i i = 1)
    (A : Matrix (Fin k) (Fin n) R) (hA : ∀ Z : Matrix (Fin n) (Fin n) R, cT s X * J * Z = 0 → (U - 1) * Z = X * (A * Z)) :
    IsNilpotent (U - 1) := by
  obtain ⟨-, h2, h3, h4⟩ := h.par hU hB
  set Q := cT s X * J * (U * Y) with hQdef
  have hP : IsNilpotent (cT s (B - 1)) := ⟨k, by rw [← cT_pow, sub_one_pow_eq_zero hBt hd, cT_zero]⟩
  have hcB : cT s B = 1 + cT s (B - 1) := by rw [cT_sub, cT_one]; abel
  have hQ1 : Q - 1 = -(Q * cT s (B - 1)) := by
    have e := h3
    rw [hcB, Matrix.mul_add, Matrix.mul_one] at e
    rw [eq_neg_iff_add_eq_zero, sub_add_eq_add_sub, e, sub_self]
  have hcomm : Commute Q (cT s (B - 1)) := by
    rw [cT_sub, cT_one]
    exact (show Commute Q (cT s B) from h3.trans h2.symm).sub_right (Commute.one_right Q)
  have hQn : IsNilpotent (Q - 1) := by
    rw [hQ1]
    exact (hcomm.isNilpotent_mul_left hP).neg
  obtain ⟨a, ha⟩ := hQn
  have hXN : cT s X * J * (U - 1) = (Q - 1) * (cT s X * J) := by
    rw [Matrix.mul_sub, Matrix.mul_one, h4, Matrix.sub_mul, Matrix.one_mul]
  have hMN : ∀ m : ℕ, cT s X * J * (U - 1) ^ m = (Q - 1) ^ m * (cT s X * J) := by
    intro m
    induction m with
    | zero => rw [pow_zero, pow_zero, Matrix.mul_one, Matrix.one_mul]
    | succ m ih => rw [pow_succ', ← Matrix.mul_assoc, hXN, Matrix.mul_assoc, ih, ← Matrix.mul_assoc, ← pow_succ']
  have hNX1 : (U - 1) * X = X * (B - 1) := by
    rw [Matrix.sub_mul, hB, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one]
  have hNX : ∀ m : ℕ, (U - 1) ^ m * X = X * (B - 1) ^ m := by
    intro m
    induction m with
    | zero => rw [pow_zero, pow_zero, Matrix.one_mul, Matrix.mul_one]
    | succ m ih => rw [pow_succ, Matrix.mul_assoc, hNX1, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, ← pow_succ]
  have h0 : cT s X * J * (U - 1) ^ a = 0 := by rw [hMN, ha, Matrix.zero_mul]
  refine ⟨k + (a + 1), ?_⟩
  rw [pow_add, pow_succ', hA _ h0, ← Matrix.mul_assoc, hNX, sub_one_pow_eq_zero hBt hd, Matrix.mul_zero,
    Matrix.zero_mul]

/- English proof (translation)
Establish `h1' : cT s X * (J * Z) = 0` using `by rw [← Matrix.mul_assoc]; exact h1`. Establish `h2' : cT s Y * (J * Z) = 0` using `by rw [← Matrix.mul_assoc]; exact h2`. Establish `e : (1 - X * (cT s Y * J) - Y * (cT s X * J)) * Z = Z`. Simplify using `only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, h1', h2', Matrix.mul_zero, sub_zero]`. Rewrite using `[← e, ← Matrix.mul_assoc, hb]`.
-/
theorem Fr.mul_eq_self (h : Fr s J X Y) {b : Matrix (Fin n) (Fin n) R}
    (hb : b * (1 - X * (cT s Y * J) - Y * (cT s X * J)) = 1 - X * (cT s Y * J) - Y * (cT s X * J))
    (Z : Matrix (Fin n) (Fin n) R) (h1 : cT s X * J * Z = 0) (h2 : cT s Y * J * Z = 0) : b * Z = Z := by
  have h1' : cT s X * (J * Z) = 0 := by rw [← Matrix.mul_assoc]; exact h1
  have h2' : cT s Y * (J * Z) = 0 := by rw [← Matrix.mul_assoc]; exact h2
  have e : (1 - X * (cT s Y * J) - Y * (cT s X * J)) * Z = Z := by
    simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, h1', h2', Matrix.mul_zero, sub_zero]
  rw [← e, ← Matrix.mul_assoc, hb]

end Alg

section Top

/- English proof (translation)
Establish `step : ∀ m : ℕ, N ^ (m + 1 + 1) = 0 → N ^ (m + 1) = 0`. Introduce `m hm`. Assume the negation of the conclusion as `hne`. Establish `hlin : ∀ j : ℕ, N ^ m * (1 + N) ^ j = N ^ m + (j : ℂ) • N ^ (m + 1)`. Introduce `j`.

Proceed by induction on `j with`. Consider the case `zero => simp`. Consider the case `succ j ih`. Rewrite using `[pow_succ, ← Matrix.mul_assoc, ih]`. Simplify using `only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_one, Matrix.smul_mul, ← pow_succ, hm, smul_zero, add_zero, Nat.cast_succ, add_smul, one_smul]`.

Normalize the expressions using the abelian group laws. Choose the witnesses or unpack the hypotheses as in `⟨a, b, hab⟩ : ∃ a b, (N ^ (m + 1)) a b ≠ 0 := by`. Assume the negation of the conclusion as `hall`. Use `push Not at hall`. Conclude with `hne (Matrix.ext hall)`.

Establish `hg : Continuous fun M : Matrix (Fin n) (Fin n) ℂ => (N ^ m * M) a b` using `(continuous_const.matrix_mul continuous_id).matrix_elem a b`. Take `⟨R, hR⟩` from `(hC.image hg).isBounded.exists_norm_le`. Take `⟨j, hj⟩` from `exists_nat_gt ((R + ‖(N ^ m) a b‖) / ‖(N ^ (m + 1)) a b‖)`. Establish `h1` using `hR _ ⟨_, hp j, rfl⟩`. Simplify using `only [hlin, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at h1`.

Establish `h2 : ‖(j : ℂ) * (N ^ (m + 1)) a b‖ ≤ R + ‖(N ^ m) a b‖`. Establish `e : (j : ℂ) * (N ^ (m + 1)) a b = ((N ^ m) a b + (j : ℂ) * (N ^ (m + 1)) a b) - (N ^ m) a b` using `by ring`. Rewrite using `[e]`. Conclude with `(norm_sub_le _ _).trans (by linarith)`. Rewrite `h2` using `[norm_mul, Complex.norm_natCast, ← le_div_iff₀ (norm_pos_iff.2 hab)]`.

Conclude with `absurd (hj.trans_le h2) (lt_irrefl _)`. Establish `hall : ∀ m : ℕ, N ^ (m + 1) = 0 → N = 0`. Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => intro h`.

Rewrite `h` using `[zero_add, pow_one]`. Then use the resulting hypothesis. Consider the case `succ m ih => intro h`. Conclude with `ih (step m h)`. Take `⟨p, hp0⟩` from `hN`. Break down `p with _ | p` into its components or cases.

Rewrite using `[← Matrix.mul_one N, ← pow_zero N, hp0, Matrix.mul_zero]`. Conclude with `hall p hp0`.
-/
theorem eq_zero_of_isNilpotent_of_pow_mem {n : ℕ} {N : Matrix (Fin n) (Fin n) ℂ} (hN : IsNilpotent N)
    {C : Set (Matrix (Fin n) (Fin n) ℂ)} (hC : IsCompact C) (hp : ∀ j : ℕ, (1 + N) ^ j ∈ C) : N = 0 := by
  have step : ∀ m : ℕ, N ^ (m + 1 + 1) = 0 → N ^ (m + 1) = 0 := by
    intro m hm
    by_contra hne
    have hlin : ∀ j : ℕ, N ^ m * (1 + N) ^ j = N ^ m + (j : ℂ) • N ^ (m + 1) := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        rw [pow_succ, ← Matrix.mul_assoc, ih]
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_one, Matrix.smul_mul, ← pow_succ, hm, smul_zero,
          add_zero, Nat.cast_succ, add_smul, one_smul]
        abel
    obtain ⟨a, b, hab⟩ : ∃ a b, (N ^ (m + 1)) a b ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hne (Matrix.ext hall)
    have hg : Continuous fun M : Matrix (Fin n) (Fin n) ℂ => (N ^ m * M) a b :=
      (continuous_const.matrix_mul continuous_id).matrix_elem a b
    obtain ⟨R, hR⟩ := (hC.image hg).isBounded.exists_norm_le
    obtain ⟨j, hj⟩ := exists_nat_gt ((R + ‖(N ^ m) a b‖) / ‖(N ^ (m + 1)) a b‖)
    have h1 := hR _ ⟨_, hp j, rfl⟩
    simp only [hlin, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at h1
    have h2 : ‖(j : ℂ) * (N ^ (m + 1)) a b‖ ≤ R + ‖(N ^ m) a b‖ := by
      have e : (j : ℂ) * (N ^ (m + 1)) a b = ((N ^ m) a b + (j : ℂ) * (N ^ (m + 1)) a b) - (N ^ m) a b := by ring
      rw [e]
      exact (norm_sub_le _ _).trans (by linarith)
    rw [norm_mul, Complex.norm_natCast, ← le_div_iff₀ (norm_pos_iff.2 hab)] at h2
    exact absurd (hj.trans_le h2) (lt_irrefl _)
  have hall : ∀ m : ℕ, N ^ (m + 1) = 0 → N = 0 := by
    intro m
    induction m with
    | zero => intro h; rwa [zero_add, pow_one] at h
    | succ m ih => intro h; exact ih (step m h)
  obtain ⟨p, hp0⟩ := hN
  rcases p with _ | p
  · rw [← Matrix.mul_one N, ← pow_zero N, hp0, Matrix.mul_zero]
  · exact hall p hp0

end Top

end PositivityTheory.ThKR.Sieg

namespace PositivityTheory.ThKR

open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open GlobalTheory.Orb (archMat archMat_apply archMat_eq_archEquiv continuous_infEmb)
open scoped TensorProduct

section Adelic

/- English proof (translation)
Simplify using `[sigR, inclR]`.
-/
theorem sigR_inclR {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (e : E) : sigR R σ (inclR R e) = inclR R (σ e) := by
  simp [sigR, inclR]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a e => simp [sigR, hσ]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`.
-/
theorem sigR_sigR {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) (x : R ⊗[F] E) : sigR R σ (sigR R σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [sigR, hσ]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [cT, Matrix.map_apply, Matrix.transpose_apply]`. Conclude with `(sigR_inclR R σ _).symm`.
-/
theorem map_cT_inclR {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {a b : Type} (P : Matrix a b E) :
    (Formalism.UG.cT (σ : E →+* E) P).map (inclR R) = Formalism.UG.cT (sigR R σ) (P.map (inclR R)) := by
  ext i j
  simp only [cT, Matrix.map_apply, Matrix.transpose_apply]
  exact (sigR_inclR R σ _).symm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n r : ℕ} {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin r) E}

/- English proof (translation)
Rewrite using `[Matrix.map_mul, Matrix.map_mul, map_cT_inclR]`. Both sides reduce to the same expression.
-/
theorem gram_adMat {a b : ℕ} (P : Matrix (Fin n) (Fin a) E) (Q : Matrix (Fin n) (Fin b) E) :
    Formalism.UG.cT (sigR (AF F) σ) (adMat F P) * JR (F := F) (AF F) J * adMat F Q = (Formalism.UG.cT (σ : E →+* E) P * J * Q).map (inclR (F := F) (AF F)) := by
  rw [Matrix.map_mul, Matrix.map_mul, map_cT_inclR]
  rfl

/- English proof (translation)
The claim follows from `sigR_sigR (AF F) (sigma_sigma h) herm := by have cJ : Formalism.UG.cT (σ : E →+* E) J = J := Matrix.ext fun i j => hJ.1 i j rw [JR, ← map_cT_inclR, cJ] xx := by rw [gram_adMat, hW.xx, Matrix.map_zero _ (map_zero _)] yy := by rw [gram_adMat, hW.yy, Matrix.map_zero _ (map_zero _)] …`.
-/
theorem fr_adMat (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) :
    Sieg.Fr (sigR (AF F) σ) (JR (F := F) (AF F) J) (adMat F X) (adMat F Y) where
  ss := sigR_sigR (AF F) (sigma_sigma h)
  herm := by
    have cJ : Formalism.UG.cT (σ : E →+* E) J = J := Matrix.ext fun i j => hJ.1 i j
    rw [JR, ← map_cT_inclR, cJ]
  xx := by rw [gram_adMat, hW.xx, Matrix.map_zero _ (map_zero _)]
  yy := by rw [gram_adMat, hW.yy, Matrix.map_zero _ (map_zero _)]
  xy := by rw [gram_adMat, hW.xy, Matrix.map_one _ (map_zero _) (map_one _)]

/- English proof (translation)
The claim follows from `g.2`.
-/
theorem unitary_matHom (g : GAd σ J) :
    Formalism.UG.cT (sigR (AF F) σ) (matHom _ σ J g).1 * JR (F := F) (AF F) J * (matHom _ σ J g).1 = JR (F := F) (AF F) J :=
  g.2

/- English proof (translation)
Take `⟨τ⟩ : Nonempty (EmbOver E w)` from `inferInstance`. Take `⟨B, hBt, hd, hB, hz⟩` from `hu`. Establish `hfr` using `fr_adMat h hJ hW`. Set `P0 : Matrix (Fin n) (Fin n) E` to `1 - Y * (Formalism.UG.cT (σ : E →+* E) X * J)`. Establish `hM : Formalism.UG.cT (σ : E →+* E) X * J * P0 = 0`.

Simplify using `only [P0]`. Rewrite using `[Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hW.xy, Matrix.one_mul, sub_self]`. Establish `hcol : ∀ j, (Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ (fun i => P0 i j) = 0` using `fun j =>`. Use function extensionality and compare the values at `fun k => congrFun (congrFun hM k) j`. Use `choose a ha using fun j => hz (fun i => P0 i j) (hcol j)`.

Set `A : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)` to `Matrix.of fun k j => a j k`. Establish `hUA : ((matHom _ σ J u).1 - 1) * P0.map (inclR (F` using `F) (AF F)) = adMat F X * A := by`. Use extensionality with `i j`. Conclude with `congrFun (ha j) i`. Establish `hP0 : P0.map (inclR (F` using `F) (AF F)) = 1 - adMat F Y * (Formalism.UG.cT (sigR (AF F) σ) (adMat F X) * JR (F := F) (AF F) J) := by`.

Simplify using `only [P0]`. Rewrite using `[Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_mul, Matrix.map_mul, map_cT_inclR]`. Both sides reduce to the same expression. Establish `hA : ∀ Z : Matrix (Fin n) (Fin n) (AF F ⊗[F] E), Formalism.UG.cT (sigR (AF F) σ) (adMat F X) * JR (F` using `F) (AF F) J * Z = 0 → ((matHom _ σ J u).1 - 1) * Z = adMat F X * (A * Z) := by`. Introduce `Z hZ`.

Establish `e : P0.map (inclR (F` using `F) (AF F)) * Z = Z := by`. Rewrite using `[hP0, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hZ, Matrix.mul_zero, sub_zero]`. Combine the equalities or inequalities in the displayed calculation. Establish `hnil` using `hfr.isNilpotent_sub_one (unitary_matHom u) hB hBt hd A hA`. Set `φ : AF F ⊗[F] E →+* ℂ` to `(infEmb τ).comp (compInf F E w)`.

Establish `hmat : ∀ g : GAd σ J, archMat σ J τ (projArch σ J w g) = (matHom _ σ J g).1.map φ` using `fun g => by`. Rewrite using `[archMat_apply, matHom_projArch]`. Both sides reduce to the same expression. Establish `hN : IsNilpotent (archMat σ J τ (projArch σ J w u) - 1)`. Use `hnil.map (φ.mapMatrix : Matrix (Fin n) (Fin n) (AF F ⊗[F] E) →+* Matrix (Fin n) (Fin n) ℂ)` as an intermediate fact.

Rewrite `this` using `[map_sub, map_one, RingHom.mapMatrix_apply]`. Rewrite using `[hmat]` and apply the resulting hypothesis. Establish `hcA : Continuous fun y : GArch σ J w => archMat σ J τ y`. Simplify using `only [archMat_apply]`. Conclude with `(Units.continuous_val.comp (isEmbedding_matHom _ σ J).continuous).matrix_map (continuous_infEmb τ)`.

Establish `hc : Continuous fun g : GAd σ J => archMat σ J τ (projArch σ J w g)` using `hcA.comp (continuous_projArch σ J w)`. Establish `h0` using `Sieg.eq_zero_of_isNilpotent_of_pow_mem hN (hK.image hc) fun j => ⟨u ^ j, K.pow_mem huK j, by simp only [add_sub_cancel, map_pow]⟩`. Establish `h1 : archMat σ J τ (projArch σ J w u) = 1` using `sub_eq_zero.1 h0`. Apply `(archEquiv J h τ).injective` to reduce the goal to its premises. Use `Subtype.ext (Units.ext ?_)` and prove the remaining obligations.

Rewrite using `[← archMat_eq_archEquiv J h, ← archMat_eq_archEquiv J h, h1, map_one]`.
-/
theorem projArch_eq_one_of_unipMin (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y)
    {K : Subgroup (GAd σ J)} (hK : IsCompact (K : Set (GAd σ J))) {u : GAd σ J} (hu : u ∈ unipMin σ J X)
    (huK : u ∈ K) (w : InfinitePlace F) : projArch σ J w u = 1 := by
  obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
  obtain ⟨B, hBt, hd, hB, hz⟩ := hu
  have hfr := fr_adMat h hJ hW
  let P0 : Matrix (Fin n) (Fin n) E := 1 - Y * (Formalism.UG.cT (σ : E →+* E) X * J)
  have hM : Formalism.UG.cT (σ : E →+* E) X * J * P0 = 0 := by
    simp only [P0]
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hW.xy, Matrix.one_mul, sub_self]
  have hcol : ∀ j, (Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ (fun i => P0 i j) = 0 := fun j =>
    funext fun k => congrFun (congrFun hM k) j
  choose a ha using fun j => hz (fun i => P0 i j) (hcol j)
  let A : Matrix (Fin r) (Fin n) (AF F ⊗[F] E) := Matrix.of fun k j => a j k
  have hUA : ((matHom _ σ J u).1 - 1) * P0.map (inclR (F := F) (AF F)) = adMat F X * A := by
    ext i j
    exact congrFun (ha j) i
  have hP0 : P0.map (inclR (F := F) (AF F)) =
      1 - adMat F Y * (Formalism.UG.cT (sigR (AF F) σ) (adMat F X) * JR (F := F) (AF F) J) := by
    simp only [P0]
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_mul, Matrix.map_mul,
      map_cT_inclR]
    rfl
  have hA : ∀ Z : Matrix (Fin n) (Fin n) (AF F ⊗[F] E), Formalism.UG.cT (sigR (AF F) σ) (adMat F X) * JR (F := F) (AF F) J * Z = 0 →
      ((matHom _ σ J u).1 - 1) * Z = adMat F X * (A * Z) := by
    intro Z hZ
    have e : P0.map (inclR (F := F) (AF F)) * Z = Z := by
      rw [hP0, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hZ, Matrix.mul_zero, sub_zero]
    calc ((matHom _ σ J u).1 - 1) * Z = ((matHom _ σ J u).1 - 1) * (P0.map (inclR (F := F) (AF F)) * Z) := by rw [e]
      _ = adMat F X * (A * Z) := by rw [← Matrix.mul_assoc, hUA, Matrix.mul_assoc]
  have hnil := hfr.isNilpotent_sub_one (unitary_matHom u) hB hBt hd A hA
  let φ : AF F ⊗[F] E →+* ℂ := (infEmb τ).comp (compInf F E w)
  have hmat : ∀ g : GAd σ J, archMat σ J τ (projArch σ J w g) = (matHom _ σ J g).1.map φ := fun g => by
    rw [archMat_apply, matHom_projArch]
    rfl
  have hN : IsNilpotent (archMat σ J τ (projArch σ J w u) - 1) := by
    have := hnil.map (φ.mapMatrix : Matrix (Fin n) (Fin n) (AF F ⊗[F] E) →+* Matrix (Fin n) (Fin n) ℂ)
    rw [map_sub, map_one, RingHom.mapMatrix_apply] at this
    rwa [hmat]
  have hcA : Continuous fun y : GArch σ J w => archMat σ J τ y := by
    simp only [archMat_apply]
    exact (Units.continuous_val.comp (isEmbedding_matHom _ σ J).continuous).matrix_map (continuous_infEmb τ)
  have hc : Continuous fun g : GAd σ J => archMat σ J τ (projArch σ J w g) := hcA.comp (continuous_projArch σ J w)
  have h0 := Sieg.eq_zero_of_isNilpotent_of_pow_mem hN (hK.image hc) fun j =>
    ⟨u ^ j, K.pow_mem huK j, by simp only [add_sub_cancel, map_pow]⟩
  have h1 : archMat σ J τ (projArch σ J w u) = 1 := sub_eq_zero.1 h0
  apply (archEquiv J h τ).injective
  refine Subtype.ext (Units.ext ?_)
  rw [← archMat_eq_archEquiv J h, ← archMat_eq_archEquiv J h, h1, map_one]

/- English proof (translation)
Take `⟨l, hl, hlK, u, hu, huK, rfl⟩` from `hG m hm hmK`. Establish `hfr` using `fr_adMat h hJ hW`. Set `P : Matrix (Fin n) (Fin n) E` to `1 - X * (Formalism.UG.cT (σ : E →+* E) Y * J) - Y * (Formalism.UG.cT (σ : E →+* E) X * J)`. Establish `hPX : Formalism.UG.cT (σ : E →+* E) X * J * P = 0`. Simplify using `only [P]`.

Rewrite using `[Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc _ Y, hW.xx, hW.xy, Matrix.zero_mul, Matrix.one_mul, sub_zero, sub_self]`. Establish `yx : Formalism.UG.cT (σ : E →+* E) Y * J * X = 1` using `(show Sieg.Fr (σ : E →+* E) J X Y from ⟨sigma_sigma h, Matrix.ext fun i j => hJ.1 i j, hW.xx, hW.yy, hW.xy⟩).yx`. Establish `hPY : Formalism.UG.cT (σ : E →+* E) Y * J * P = 0`. Simplify using `only [P]`. Rewrite using `[Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc _ Y, yx, hW.yy, Matrix.zero_mul, Matrix.one_mul, sub_zero, sub_self]`.

Establish `hbP : (matHom _ σ J b).1 * P.map (inclR (F` using `F) (AF F)) = P.map (inclR (F := F) (AF F)) := by`. Use extensionality with `i j`. Conclude with `congrFun (hbV (fun k => P k j) (funext fun k => congrFun (congrFun hPX k) j) (funext fun k => congrFun (congrFun hPY k) j)) i`. Establish `hPad : P.map (inclR (F` using `F) (AF F)) = 1 - adMat F X * (Formalism.UG.cT (sigR (AF F) σ) (adMat F Y) * JR (F := F) (AF F) J) - adMat F Y * (Formalism.UG.cT (sigR (AF F) σ) (adMat F X) * JR (F := F) (AF F) J) := by`. Simplify using `only [P]`.

Rewrite using `[Matrix.map_sub _ (map_sub _), Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, map_cT_inclR, map_cT_inclR]`. Both sides reduce to the same expression. Rewrite `hbP` using `[hPad]`. Establish `hlb : b * l = l * b`. Take `⟨d, d', hd, hd'⟩` from `hl`.

Apply `matHom_injective _ σ J` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul, Units.val_mul, Units.val_mul]`. Conclude with `hfr.comm (unitary_matHom l) hd hd' hbX hbY (by rw [diagonal_mul_diagonal, diagonal_mul_diagonal]; simp [mul_comm]) (by rw [diagonal_mul_diagonal, diagonal_mul_diagonal]; simp [mul_comm]) fun Z h1 h2 => hfr.mul_eq_self hbP Z h1 h2`. Establish `hub : b * u = u * b`.

Establish `hw` using `projArch_eq_one_of_unipMin h hJ hW hK hu huK`. Use `GAd_ext σ J (fun w => by rw [map_mul, map_mul, hw, mul_one, one_mul]) fun v => by` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, mem_infPts_iff_forall.1 hb v, mul_one, one_mul]`. Rewrite using `[← mul_assoc, hlb, mul_assoc, hub, mul_assoc]`.
-/
theorem commute_of_good_position (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y)
    {b : GAd σ J} (hb : b ∈ infPts σ J) {dX dY : Fin r → AF F ⊗[F] E}
    (hbX : (matHom _ σ J b).1 * adMat F X = adMat F X * diagonal dX)
    (hbY : (matHom _ σ J b).1 * adMat F Y = adMat F Y * diagonal dY)
    (hbV : ∀ z : Fin n → E, (Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ z = 0 → (Formalism.UG.cT (σ : E →+* E) Y * J) *ᵥ z = 0 →
      (matHom _ σ J b).1 *ᵥ (fun i => inclR (F := F) (AF F) (z i)) = fun i => inclR (F := F) (AF F) (z i))
    {K : Subgroup (GAd σ J)} (hK : IsCompact (K : Set (GAd σ J))) (hG : GoodPosition σ J X Y K)
    {m : GAd σ J} (hm : m ∈ minPar σ J X) (hmK : m ∈ K) : b * m = m * b := by
  obtain ⟨l, hl, hlK, u, hu, huK, rfl⟩ := hG m hm hmK
  have hfr := fr_adMat h hJ hW
  let P : Matrix (Fin n) (Fin n) E := 1 - X * (Formalism.UG.cT (σ : E →+* E) Y * J) - Y * (Formalism.UG.cT (σ : E →+* E) X * J)
  have hPX : Formalism.UG.cT (σ : E →+* E) X * J * P = 0 := by
    simp only [P]
    rw [Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc _ Y, hW.xx, hW.xy,
      Matrix.zero_mul, Matrix.one_mul, sub_zero, sub_self]
  have yx : Formalism.UG.cT (σ : E →+* E) Y * J * X = 1 :=
    (show Sieg.Fr (σ : E →+* E) J X Y from ⟨sigma_sigma h, Matrix.ext fun i j => hJ.1 i j, hW.xx, hW.yy, hW.xy⟩).yx
  have hPY : Formalism.UG.cT (σ : E →+* E) Y * J * P = 0 := by
    simp only [P]
    rw [Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc _ Y, yx, hW.yy,
      Matrix.zero_mul, Matrix.one_mul, sub_zero, sub_self]
  have hbP : (matHom _ σ J b).1 * P.map (inclR (F := F) (AF F)) = P.map (inclR (F := F) (AF F)) := by
    ext i j
    exact congrFun (hbV (fun k => P k j) (funext fun k => congrFun (congrFun hPX k) j)
      (funext fun k => congrFun (congrFun hPY k) j)) i
  have hPad : P.map (inclR (F := F) (AF F)) = 1 - adMat F X * (Formalism.UG.cT (sigR (AF F) σ) (adMat F Y) * JR (F := F) (AF F) J) -
      adMat F Y * (Formalism.UG.cT (sigR (AF F) σ) (adMat F X) * JR (F := F) (AF F) J) := by
    simp only [P]
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, map_cT_inclR, map_cT_inclR]
    rfl
  rw [hPad] at hbP
  have hlb : b * l = l * b := by
    obtain ⟨d, d', hd, hd'⟩ := hl
    apply matHom_injective _ σ J
    apply Units.ext
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul]
    exact hfr.comm (unitary_matHom l) hd hd' hbX hbY (by rw [diagonal_mul_diagonal, diagonal_mul_diagonal]; simp [mul_comm])
      (by rw [diagonal_mul_diagonal, diagonal_mul_diagonal]; simp [mul_comm]) fun Z h1 h2 => hfr.mul_eq_self hbP Z h1 h2
  have hub : b * u = u * b := by
    have hw := projArch_eq_one_of_unipMin h hJ hW hK hu huK
    refine GAd_ext σ J (fun w => by rw [map_mul, map_mul, hw, mul_one, one_mul]) fun v => by
      rw [map_mul, map_mul, mem_infPts_iff_forall.1 hb v, mul_one, one_mul]
  rw [← mul_assoc, hlb, mul_assoc, hub, mul_assoc]

end Adelic

end PositivityTheory.ThKR

end
