import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InjectiveWedgeHighestCoefficient

open Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.PairMult

variable {n : ℕ}

def AdFamL (lev : Fin n → ℕ) {ι : Type} [Fintype ι] (w : ι → FreeAlgebra ℂ (Bool × Fin n × Fin n))
    (M : Fin n → Fin n → Matrix ι ι ℂ) : Prop :=
  (∀ c d i j, star (M c d j i) = M d c i j) ∧
  ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (X1 X2 : Fin n → Fin n → Module.End ℂ W), LRel lev X1 X2 →
    ∀ c d, lev c = lev d → ∀ i, (X1 c d + X2 c d) * evB lev X1 X2 (w i) - evB lev X1 X2 (w i) * (X1 c d + X2 c d) =
      ∑ j, M c d j i • evB lev X1 X2 (w j)

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `hX`. Simplify using `only [evB, FreeAlgebra.lift_ι_apply]`. Distinguish the cases in `hab : lev a = lev b`. Establish `e1 : d = a → lev c = lev b` using `fun h => by rw [hcd, h, hab]`. Establish `e2 : b = c → lev a = lev d` using `fun h => by rw [hab, h, hcd]`.

Apply the tactic sequence `have k1 : (if d = a then (if lev c = lev b then (if s = true then X1 c b else X2 c b) else 0) else 0) = if d = a then (if s = true then X1 c b else X2 c b) else 0 := by split_ifs with h h' <;> first | rfl | exact absurd (e1 h) h'`. Apply the tactic sequence `have k2 : (if b = c then (if lev a = lev d then (if s = true then X1 a d else X2 a d) else 0) else 0) = if b = c then (if s = true then X1 a d else X2 a d) else 0 := by split_ifs with h h' <;> first | rfl | exact absurd (e2 h) h'`. Rewrite using `[k1, k2, if_pos hab]`. Consider the cases of `s`. Establish `e` using `h2 c d a b hcd hab`.

Establish `k` using `(h3 c d a b hcd hab).eq`. Simplify using `only [Bool.false_eq_true, if_false, add_mul, mul_add]`. Rewrite using `[k, ← e]`. Normalize the expressions using the abelian group laws. Establish `e` using `h1 c d a b hcd hab`.

Establish `k` using `(h3 a b c d hab hcd).eq`. Simplify using `only [if_true, add_mul, mul_add]`. Rewrite using `[k, ← e]`. Normalize the expressions using the abelian group laws. Establish `e1 : d = a → ¬ lev c = lev b` using `fun h => by rw [hcd, h]; exact hab`.

Establish `e2 : b = c → ¬ lev a = lev d` using `fun h => by rw [← hcd, ← h]; exact hab`. Apply the tactic sequence `have k1 : (if d = a then (if lev c = lev b then (if s = true then X1 c b else X2 c b) else 0) else 0) = 0 := by split_ifs with h h' <;> first | rfl | exact absurd h' (e1 h)`. Apply the tactic sequence `have k2 : (if b = c then (if lev a = lev d then (if s = true then X1 a d else X2 a d) else 0) else 0) = 0 := by split_ifs with h h' <;> first | rfl | exact absurd h' (e2 h)`. Rewrite using `[k1, k2, if_neg hab]`. Simplify using the standard rewrite rules.
-/
theorem ad_letter {lev : Fin n → ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] {X1 X2 : Fin n → Fin n → Module.End ℂ W}
    (hX : LRel lev X1 X2) {c d : Fin n} (hcd : lev c = lev d) (s : Bool) (a b : Fin n) :
    (X1 c d + X2 c d) * evB lev X1 X2 (FreeAlgebra.ι ℂ (s, a, b)) -
        evB lev X1 X2 (FreeAlgebra.ι ℂ (s, a, b)) * (X1 c d + X2 c d) =
      (if d = a then evB lev X1 X2 (FreeAlgebra.ι ℂ (s, c, b)) else 0) -
        (if b = c then evB lev X1 X2 (FreeAlgebra.ι ℂ (s, a, d)) else 0) := by
  obtain ⟨h1, h2, h3⟩ := hX
  simp only [evB, FreeAlgebra.lift_ι_apply]
  by_cases hab : lev a = lev b
  · have e1 : d = a → lev c = lev b := fun h => by rw [hcd, h, hab]
    have e2 : b = c → lev a = lev d := fun h => by rw [hab, h, hcd]
    have k1 : (if d = a then (if lev c = lev b then (if s = true then X1 c b else X2 c b) else 0) else 0) =
        if d = a then (if s = true then X1 c b else X2 c b) else 0 := by
      split_ifs with h h' <;> first | rfl | exact absurd (e1 h) h'
    have k2 : (if b = c then (if lev a = lev d then (if s = true then X1 a d else X2 a d) else 0) else 0) =
        if b = c then (if s = true then X1 a d else X2 a d) else 0 := by
      split_ifs with h h' <;> first | rfl | exact absurd (e2 h) h'
    rw [k1, k2, if_pos hab]
    cases s
    · have e := h2 c d a b hcd hab
      have k := (h3 c d a b hcd hab).eq
      simp only [Bool.false_eq_true, if_false, add_mul, mul_add]
      rw [k, ← e]
      abel
    · have e := h1 c d a b hcd hab
      have k := (h3 a b c d hab hcd).eq
      simp only [if_true, add_mul, mul_add]
      rw [k, ← e]
      abel
  · have e1 : d = a → ¬ lev c = lev b := fun h => by rw [hcd, h]; exact hab
    have e2 : b = c → ¬ lev a = lev d := fun h => by rw [← hcd, ← h]; exact hab
    have k1 : (if d = a then (if lev c = lev b then (if s = true then X1 c b else X2 c b) else 0) else 0) = 0 := by
      split_ifs with h h' <;> first | rfl | exact absurd h' (e1 h)
    have k2 : (if b = c then (if lev a = lev d then (if s = true then X1 a d else X2 a d) else 0) else 0) = 0 := by
      split_ifs with h h' <;> first | rfl | exact absurd h' (e2 h)
    rw [k1, k2, if_neg hab]
    simp

/- English proof (translation)
Proceed by induction on `a using FreeAlgebra.induction with`. Consider the case `grade0 r`. Use `⟨Unit, inferInstance, fun _ => 1, fun _ _ => 0, fun _ => r, ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `c d i j`. Simplify using the standard rewrite rules.

Introduce `W _ _ X1 X2 _ c d _ i`. Simplify using the standard rewrite rules. Simplify using `[Algebra.algebraMap_eq_smul_one]`. Consider the case `grade1 x`. Use `⟨Bool × Fin n × Fin n, inferInstance, fun p => FreeAlgebra.ι ℂ p, fun c d => Matrix.of fun j i => (if d = i.2.1 ∧ j = (i.1, c, i.2.2) then 1 else 0) - (if i.2.2 = c ∧ j = (i.1, i.2.1, d) then 1 else 0), Pi.single x 1, ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Introduce and unpack `c d ⟨s, i1, i2⟩ ⟨t, j1, j2⟩`. Simplify using `only [Matrix.of_apply, star_sub, Prod.mk.injEq, apply_ite star, star_one, star_zero]`. Use `congr 1`. Apply `if_congr _ rfl rfl` to reduce the goal to its premises. Apply the tactic sequence `constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> exact ⟨h3.symm, h2.symm, h1.symm, h4.symm⟩`.

Apply `if_congr _ rfl rfl` to reduce the goal to its premises. Apply the tactic sequence `constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> exact ⟨h4, h2.symm, h3.symm, h1⟩`. Introduce and unpack `W _ _ X1 X2 hX c d hcd ⟨s, a, b⟩`. Establish `h` using `ad_letter hX hcd s a b`. Simplify using `only [Matrix.of_apply, sub_smul, Finset.sum_sub_distrib]`.

Rewrite using `[h]`. Use `congr 1`. Apply the tactic sequence `by_cases h1 : d = a <;> simp [h1]`. Apply the tactic sequence `by_cases h1 : b = c <;> simp [h1]`. Simplify using `[Pi.single_apply]`.

Consider the case `mul a b ha hb`. Take `⟨ι, _, w, M, t, ⟨h1, h2⟩, rfl⟩` from `ha`. Take `⟨ι', _, w', M', t', ⟨h1', h2'⟩, rfl⟩` from `hb`. Use `⟨ι × ι', inferInstance, fun p => w p.1 * w' p.2, fun c d => Matrix.of fun j i => (if j.2 = i.2 then M c d j.1 i.1 else 0) + (if j.1 = i.1 then M' c d j.2 i.2 else 0), fun p => t p.1 * t' p.2, ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `c d ⟨i1, i2⟩ ⟨j1, j2⟩`.

Simplify using `only [Matrix.of_apply, star_add, apply_ite star, star_zero, h1, h1', eq_comm]`. Introduce and unpack `W _ _ X1 X2 hX c d hcd ⟨i, i'⟩`. Establish `e1` using `h2 W X1 X2 hX c d hcd i`. Establish `e2` using `h2' W X1 X2 hX c d hcd i'`. Establish `: (X1 c d + X2 c d) * evB lev X1 X2 (w i * w' i') - evB lev X1 X2 (w i * w' i') * (X1 c d + X2 c d) = ((X1 c d + X2 c d) * evB lev X1 X2 (w i) - evB lev X1 X2 (w i) * (X1 c d + X2 c d)) * evB lev X1 X2 (w' i') + evB lev X1 X2 (w i) * ((X1 c d + X2 c d) * evB lev X1 X2 (w' i') - e …`.

Rewrite using `[map_mul]`. Use `noncomm_ring`. Simplify using `only []`. Rewrite using `[this, e1, e2]`. Simplify using `only [Matrix.of_apply, add_smul, Finset.sum_add_distrib, Fintype.sum_prod_type, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true, map_mul, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]`.

Use `congr 1`. Rewrite using `[Finset.sum_comm]`. Simplify using the standard rewrite rules. Rewrite using `[Finset.sum_mul_sum, Fintype.sum_prod_type]`. Simplify using `only [smul_mul_smul_comm]`.

Consider the case `add a b ha hb`. Take `⟨ι, _, w, M, t, ⟨h1, h2⟩, rfl⟩` from `ha`. Take `⟨ι', _, w', M', t', ⟨h1', h2'⟩, rfl⟩` from `hb`. Use `⟨ι ⊕ ι', inferInstance, Sum.elim w w', fun c d => Matrix.fromBlocks (M c d) 0 0 (M' c d), Sum.elim t t', ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `rintro c d (i | i) (j | j) <;> simp [← h1 d c, ← h1' d c]`.

Introduce and unpack `W _ _ X1 X2 hX c d hcd (i | i)`. Simplify using `[Fintype.sum_sum_type, h2 W X1 X2 hX c d hcd]`. Simplify using `[Fintype.sum_sum_type, h2' W X1 X2 hX c d hcd]`. Simplify using `[Fintype.sum_sum_type]`.
-/
theorem exists_adFamL (lev : Fin n → ℕ) (a : FreeAlgebra ℂ (Bool × Fin n × Fin n)) :
    ∃ (ι : Type) (_ : Fintype ι) (w : ι → FreeAlgebra ℂ (Bool × Fin n × Fin n)) (M : Fin n → Fin n → Matrix ι ι ℂ)
      (t : ι → ℂ), AdFamL lev w M ∧ a = ∑ i, t i • w i := by
  classical
  induction a using FreeAlgebra.induction with
  | grade0 r =>
    refine ⟨Unit, inferInstance, fun _ => 1, fun _ _ => 0, fun _ => r, ⟨?_, ?_⟩, ?_⟩
    · intro c d i j; simp
    · intro W _ _ X1 X2 _ c d _ i; simp
    · simp [Algebra.algebraMap_eq_smul_one]
  | grade1 x =>
    refine ⟨Bool × Fin n × Fin n, inferInstance, fun p => FreeAlgebra.ι ℂ p,
      fun c d => Matrix.of fun j i => (if d = i.2.1 ∧ j = (i.1, c, i.2.2) then 1 else 0) -
        (if i.2.2 = c ∧ j = (i.1, i.2.1, d) then 1 else 0),
      Pi.single x 1, ⟨?_, ?_⟩, ?_⟩
    · rintro c d ⟨s, i1, i2⟩ ⟨t, j1, j2⟩
      simp only [Matrix.of_apply, star_sub, Prod.mk.injEq, apply_ite star, star_one, star_zero]
      congr 1
      · apply if_congr _ rfl rfl
        constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> exact ⟨h3.symm, h2.symm, h1.symm, h4.symm⟩
      · apply if_congr _ rfl rfl
        constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> exact ⟨h4, h2.symm, h3.symm, h1⟩
    · rintro W _ _ X1 X2 hX c d hcd ⟨s, a, b⟩
      have h := ad_letter hX hcd s a b
      simp only [Matrix.of_apply, sub_smul, Finset.sum_sub_distrib]
      rw [h]
      congr 1
      · by_cases h1 : d = a <;> simp [h1]
      · by_cases h1 : b = c <;> simp [h1]
    · simp [Pi.single_apply]
  | mul a b ha hb =>
    obtain ⟨ι, _, w, M, t, ⟨h1, h2⟩, rfl⟩ := ha
    obtain ⟨ι', _, w', M', t', ⟨h1', h2'⟩, rfl⟩ := hb
    refine ⟨ι × ι', inferInstance, fun p => w p.1 * w' p.2,
      fun c d => Matrix.of fun j i => (if j.2 = i.2 then M c d j.1 i.1 else 0) + (if j.1 = i.1 then M' c d j.2 i.2 else 0),
      fun p => t p.1 * t' p.2, ⟨?_, ?_⟩, ?_⟩
    · rintro c d ⟨i1, i2⟩ ⟨j1, j2⟩
      simp only [Matrix.of_apply, star_add, apply_ite star, star_zero, h1, h1', eq_comm]
    · rintro W _ _ X1 X2 hX c d hcd ⟨i, i'⟩
      have e1 := h2 W X1 X2 hX c d hcd i
      have e2 := h2' W X1 X2 hX c d hcd i'
      have : (X1 c d + X2 c d) * evB lev X1 X2 (w i * w' i') - evB lev X1 X2 (w i * w' i') * (X1 c d + X2 c d) =
          ((X1 c d + X2 c d) * evB lev X1 X2 (w i) - evB lev X1 X2 (w i) * (X1 c d + X2 c d)) * evB lev X1 X2 (w' i') +
            evB lev X1 X2 (w i) *
              ((X1 c d + X2 c d) * evB lev X1 X2 (w' i') - evB lev X1 X2 (w' i') * (X1 c d + X2 c d)) := by
        rw [map_mul]; noncomm_ring
      simp only []
      rw [this, e1, e2]
      simp only [Matrix.of_apply, add_smul, Finset.sum_add_distrib, Fintype.sum_prod_type, ite_smul, zero_smul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, map_mul, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
        mul_smul_comm]
      congr 1
      rw [Finset.sum_comm]
      simp
    · rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
      simp only [smul_mul_smul_comm]
  | add a b ha hb =>
    obtain ⟨ι, _, w, M, t, ⟨h1, h2⟩, rfl⟩ := ha
    obtain ⟨ι', _, w', M', t', ⟨h1', h2'⟩, rfl⟩ := hb
    refine ⟨ι ⊕ ι', inferInstance, Sum.elim w w', fun c d => Matrix.fromBlocks (M c d) 0 0 (M' c d),
      Sum.elim t t', ⟨?_, ?_⟩, ?_⟩
    · rintro c d (i | i) (j | j) <;> simp [← h1 d c, ← h1' d c]
    · rintro W _ _ X1 X2 hX c d hcd (i | i)
      · simp [Fintype.sum_sum_type, h2 W X1 X2 hX c d hcd]
      · simp [Fintype.sum_sum_type, h2' W X1 X2 hX c d hcd]
    · simp [Fintype.sum_sum_type]

/- English proof (translation)
Simplify using `only [map_sum, map_smul, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc, ← Finset.sum_sub_distrib, ← smul_sub, h.2 W X1 X2 hX c d hcd, Finset.smul_sum, Matrix.mulVec, dotProduct, Finset.sum_smul, smul_smul]`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [mul_comm]`.
-/
theorem AdFamL.comm {lev : Fin n → ℕ} {ι : Type} [Fintype ι] {w : ι → FreeAlgebra ℂ (Bool × Fin n × Fin n)}
    {M : Fin n → Fin n → Matrix ι ι ℂ} (h : AdFamL lev w M) {W : Type} [AddCommGroup W] [Module ℂ W]
    {X1 X2 : Fin n → Fin n → Module.End ℂ W} (hX : LRel lev X1 X2) {c d : Fin n} (hcd : lev c = lev d) (t : ι → ℂ) :
    (X1 c d + X2 c d) * evB lev X1 X2 (∑ i, t i • w i) - evB lev X1 X2 (∑ i, t i • w i) * (X1 c d + X2 c d) =
      evB lev X1 X2 (∑ j, (M c d *ᵥ t) j • w j) := by
  simp only [map_sum, map_smul, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
    ← Finset.sum_sub_distrib, ← smul_sub, h.2 W X1 X2 hX c d hcd, Finset.smul_sum, Matrix.mulVec, dotProduct,
    Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

/- English proof (translation)
Introduce `n lev V _ _ X1 X2 L a hX hL ha`. Take `⟨ι, _, w, M, t, hM, rfl⟩` from `exists_adFamL lev a`. Set `N : Submodule ℂ (EuclideanSpace ℂ ι)` to `{ carrier := {x | ∀ s ∈ L, evB lev X1 X2 (∑ i, x i • w i) s = 0} add_mem' := by`. Introduce `x y hx hy s hs`. Use `hx s hs` as an intermediate fact.

Use `hy s hs` as an intermediate fact. Simplify using `only [PiLp.add_apply, add_smul, Finset.sum_add_distrib, map_add, LinearMap.add_apply, *, add_zero]`. Use the proof step `zero_mem' := by intro s hs; simp`. Use the proof step `smul_mem' := by`. Introduce `r x hx s hs`.

Use `hx s hs` as an intermediate fact. Simplify using `only [PiLp.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, map_smul, LinearMap.smul_apply, this, smul_zero] }`. Establish `hN : ∀ x, x ∈ N ↔ ∀ s ∈ L, evB lev X1 X2 (∑ i, x i • w i) s = 0` using `fun x => Iff.rfl`. Set `D : Fin n → Fin n → Module.End ℂ (EuclideanSpace ℂ ι)` to `fun c d => Matrix.toEuclideanLin (M c d)`. Establish `hD : ∀ c d x, (D c d x).ofLp = M c d *ᵥ x.ofLp` using `fun c d x => rfl`.

Establish `hadj : ∀ c d x y, ⟪x, D c d y⟫_ℂ = ⟪D d c x, y⟫_ℂ`. Introduce `c d x y`. Establish `: M d c = (M c d)ᴴ` using `by ext i j; simp [Matrix.conjTranspose_apply, ← hM.1 c d]`. Simplify using `only [D]`. Rewrite using `[this, Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_left]`.

Establish `hDN : ∀ c d, lev c = lev d → ∀ x ∈ N, D c d x ∈ N`. Introduce `c d hcd x hx`. Rewrite `hx`, the goal using `[hN]`. Introduce `s hs`. Rewrite using `[hD, ← hM.comm hX hcd]`.

Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply, hx s hs, hx _ (hL c d hcd s hs), map_zero, sub_zero]`. Establish `ht : ∀ c d, lev c = lev d → D c d (WithLp.toLp 2 t) ∈ N`. Introduce `c d hcd`. Rewrite using `[hN]`. Introduce `s hs`.

Rewrite using `[hD, ← hM.comm hX hcd]`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply, ha c d hcd s hs, sub_self]`. Take `⟨k, hk, t', ht', e⟩` from `N.exists_add_mem_mem_orthogonal (WithLp.toLp 2 t)`. Establish `h0 : ∀ c d, lev c = lev d → D c d t' = 0`. Introduce `c d hcd`.

Establish `h1 : D c d t' ∈ N`. Use `N.sub_mem (ht c d hcd) (hDN c d hcd k hk)` as an intermediate fact. Rewrite `this` using `[e, map_add, add_sub_cancel_left]`. Then use the resulting hypothesis. Rewrite using `[← inner_self_eq_zero (𝕜 := ℂ), hadj]`. Conclude with `(Submodule.mem_orthogonal _ _).1 ht' _ (hDN d c hcd.symm _ h1)`.

Use `⟨∑ i, t' i • w i, ?_, ?_⟩` and prove the remaining obligations. Introduce `V' _ _ Y1 Y2 hY c d hcd`. Use `hM.comm hY hcd t'.ofLp` as an intermediate fact. Rewrite `this` using `[← hD, h0 c d hcd]`. Establish `h2 : evB lev Y1 Y2 (∑ j, (0 : EuclideanSpace ℂ ι).ofLp j • w j) = 0` using `by simp`.

Rewrite `this` using `[h2]`. Conclude with `sub_eq_zero.1 this`. Introduce `s hs`. Establish `e' : ∀ i, t i = k i + t' i` using `fun i => congrArg (fun x : EuclideanSpace ℂ ι => x i) e`. Use `(hN k).1 hk s hs` as an intermediate fact.

Simplify using `only [e', add_smul, Finset.sum_add_distrib, map_add, LinearMap.add_apply, this, zero_add]`.
-/
theorem invL : InvL := by
  classical
  intro n lev V _ _ X1 X2 L a hX hL ha
  obtain ⟨ι, _, w, M, t, hM, rfl⟩ := exists_adFamL lev a
  let N : Submodule ℂ (EuclideanSpace ℂ ι) :=
    { carrier := {x | ∀ s ∈ L, evB lev X1 X2 (∑ i, x i • w i) s = 0}
      add_mem' := by
        intro x y hx hy s hs
        have := hx s hs
        have := hy s hs
        simp only [PiLp.add_apply, add_smul, Finset.sum_add_distrib, map_add, LinearMap.add_apply, *, add_zero]
      zero_mem' := by intro s hs; simp
      smul_mem' := by
        intro r x hx s hs
        have := hx s hs
        simp only [PiLp.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, map_smul, LinearMap.smul_apply, this,
          smul_zero] }
  have hN : ∀ x, x ∈ N ↔ ∀ s ∈ L, evB lev X1 X2 (∑ i, x i • w i) s = 0 := fun x => Iff.rfl
  let D : Fin n → Fin n → Module.End ℂ (EuclideanSpace ℂ ι) := fun c d => Matrix.toEuclideanLin (M c d)
  have hD : ∀ c d x, (D c d x).ofLp = M c d *ᵥ x.ofLp := fun c d x => rfl
  have hadj : ∀ c d x y, ⟪x, D c d y⟫_ℂ = ⟪D d c x, y⟫_ℂ := by
    intro c d x y
    have : M d c = (M c d)ᴴ := by ext i j; simp [Matrix.conjTranspose_apply, ← hM.1 c d]
    simp only [D]
    rw [this, Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_left]
  have hDN : ∀ c d, lev c = lev d → ∀ x ∈ N, D c d x ∈ N := by
    intro c d hcd x hx
    rw [hN] at hx ⊢
    intro s hs
    rw [hD, ← hM.comm hX hcd]
    simp only [LinearMap.sub_apply, Module.End.mul_apply, hx s hs, hx _ (hL c d hcd s hs), map_zero, sub_zero]
  have ht : ∀ c d, lev c = lev d → D c d (WithLp.toLp 2 t) ∈ N := by
    intro c d hcd
    rw [hN]
    intro s hs
    rw [hD, ← hM.comm hX hcd]
    simp only [LinearMap.sub_apply, Module.End.mul_apply, ha c d hcd s hs, sub_self]
  obtain ⟨k, hk, t', ht', e⟩ := N.exists_add_mem_mem_orthogonal (WithLp.toLp 2 t)
  have h0 : ∀ c d, lev c = lev d → D c d t' = 0 := by
    intro c d hcd
    have h1 : D c d t' ∈ N := by
      have := N.sub_mem (ht c d hcd) (hDN c d hcd k hk)
      rwa [e, map_add, add_sub_cancel_left] at this
    rw [← inner_self_eq_zero (𝕜 := ℂ), hadj]
    exact (Submodule.mem_orthogonal _ _).1 ht' _ (hDN d c hcd.symm _ h1)
  refine ⟨∑ i, t' i • w i, ?_, ?_⟩
  · intro V' _ _ Y1 Y2 hY c d hcd
    have := hM.comm hY hcd t'.ofLp
    rw [← hD, h0 c d hcd] at this
    have h2 : evB lev Y1 Y2 (∑ j, (0 : EuclideanSpace ℂ ι).ofLp j • w j) = 0 := by simp
    rw [h2] at this
    exact sub_eq_zero.1 this
  · intro s hs
    have e' : ∀ i, t i = k i + t' i := fun i => congrArg (fun x : EuclideanSpace ℂ ι => x i) e
    have := (hN k).1 hk s hs
    simp only [e', add_smul, Finset.sum_add_distrib, map_add, LinearMap.add_apply, this, zero_add]

end GlobalTheory.CompanionTheory.PairMult
