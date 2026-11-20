import Formalism.LocalToGlobal.Columns.KOneCharacterTrivialNearOne
import Formalism.LocalToGlobal.Columns.ChainInstY
import Formalism.LocalToGlobal.Columns.ChainTwPsi

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section TwTopQ

variable {E : Type} [Field E] [NumberField E] [StarRing E]

/- English proof (translation)
Apply `hM` to reduce the goal to its premises. Use `show coarse r [b] a.1 < coarse r [b] l.1`. Unfold `coarse`. Simplify using `only [blkIdx, if_pos ha, if_neg (not_lt.2 hl)]`. Use linear arithmetic over natural numbers and integers.
-/
theorem twTQ_HQ_entry {κ : Type} [CommRing κ] {n r b : ℕ} {M : GL (Fin n) κ} (hM : M ∈ HQ κ n r b) {a l : Fin n} (ha : a.1 < r)
    (hl : r ≤ l.1) : (M : Matrix (Fin n) (Fin n) κ) l a = 0 := by
  apply hM
  show coarse r [b] a.1 < coarse r [b] l.1
  unfold coarse
  simp only [blkIdx, if_pos ha, if_neg (not_lt.2 hl)]
  omega

def twInit {n : ℕ} (x : Sp E n) : Sp E (n - 1) := fun i => x ⟨i.1, by have := i.2; omega⟩

def twSnoc {n : ℕ} (x' : Sp E (n - 1)) (t : E) : Sp E n := fun l => if h : l.1 < n - 1 then x' ⟨l.1, h⟩ else t

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[twInit, twSnoc, i.2]`.
-/
theorem twInit_snoc {n : ℕ} (x' : Sp E (n - 1)) (t : E) : twInit (twSnoc (n := n) x' t) = x' := by
  funext i
  simp [twInit, twSnoc, i.2]

variable (P : HeightOneSpectrum (𝓞 E))

def twLastI {n : ℕ} (hn : 0 < n) : Fin n := ⟨n - 1, by omega⟩

/- English proof (translation)
Establish `hq0 : (qOf P : E) ≠ 0` using `by exact_mod_cast (Formalism.L2.Ker.qOf_pos P).ne'`. Rewrite `hx`, the goal using `[twParL_mem]`. Establish `hxI : ∀ l, IntAt P (x l)` using `fun l => by`. Use `hx l` as an intermediate fact. Distinguish the cases in `hl : r ≤ l.1 ∧ l.1 < n`.

Rewrite `this` using `[if_pos hl, zpow_one]`. Establish `e : x l = (qOf P : E) * ((qOf P : E)⁻¹ * x l)` using `by field_simp`. Rewrite using `[e]`. Conclude with `(ciIntAt_q (P := P) (q := qOf P)).mul this`. Rewrite `this` using `[if_neg hl]`.

Simplify using `using this`. Establish `hxD : ∀ l : Fin n, r ≤ l.1 → IntAt P ((qOf P : E)⁻¹ * x l)` using `fun l hl => by`. Use `hx l` as an intermediate fact. Rewrite `this` using `[if_pos ⟨hl, l.2⟩, zpow_one]`. Conclude with `this`.

Introduce `l`. Rewrite using `[hH]`. Distinguish the cases in `hl : l.1 < n - 1`. Rewrite using `[dif_pos hl]`. Distinguish the cases in `hDl : r ≤ l.1`.

Rewrite using `[if_pos ⟨hDl, l.2⟩, zpow_one]`. Rewrite using `[twApply_coordE h' (twInit x) ⟨l.1, hl⟩, Finset.mul_sum]`. Apply `twIntAt_sum` to reduce the goal to its premises. Introduce `a`. Establish `ea : (twE a : Sp E (n - 1)) = Pi.single a 1`.

Use function extensionality and compare the values at `j`. Unfold `twE`. Simplify using `[Pi.single_apply, eq_comm]`. Rewrite using `[ea]`. Distinguish the cases in `ha : a.1 < r`.

Establish `e : ((qOf P : E))⁻¹ * (twInit x a * h' (Pi.single a 1) ⟨l.1, hl⟩) = twInit x a * (h' (Pi.single a 1) ⟨l.1, hl⟩ / (qOf P : E))` using `by field_simp`. Rewrite using `[e]`. Conclude with `(hxI _).mul (hD a ⟨l.1, hl⟩ ha hDl)`. Establish `hxa` using `hxD ⟨a.1, by have := a.2; omega⟩ (by show r ≤ a.1; omega)`. Establish `e : ((qOf P : E))⁻¹ * (twInit x a * h' (Pi.single a 1) ⟨l.1, hl⟩) = ((qOf P : E))⁻¹ * x ⟨a.1, by have` using `a.2; omega⟩ * h' (Pi.single a 1) ⟨l.1, hl⟩ := by`.

Unfold `twInit`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Use `hxa.mul (hint _ (fun j => ?_) _)` and prove the remaining obligations. Distinguish the cases in `hj : j = a`.

Substitute `hj; simp only [Pi.single_eq_same]; exact ⟨1, 1, one_notMem P, by simp⟩` using the available equality. Rewrite using `[Pi.single_eq_of_ne hj]; exact ⟨0, 1, one_notMem P, by simp⟩`. Rewrite using `[if_neg (fun h => hDl h.1), zpow_zero, inv_one, one_mul]`. Conclude with `hint (twInit x) (fun i => hxI _) ⟨l.1, hl⟩`. Rewrite using `[dif_neg hl]`.

Conclude with `hx l`.
-/
theorem twPar_block {n r : ℕ} (hr : r < n) (H : Sp E n ≃ₗ[E] Sp E n) (h' : Sp E (n - 1) ≃ₗ[E] Sp E (n - 1))
    (hH : ∀ x (l : Fin n), H x l = if h : l.1 < n - 1 then h' (twInit x) ⟨l.1, h⟩ else x l)
    (hint : ∀ x' : Sp E (n - 1), (∀ i, IntAt P (x' i)) → ∀ i, IntAt P (h' x' i))
    (hD : ∀ a l : Fin (n - 1), a.1 < r → r ≤ l.1 → IntAt P (h' (Pi.single a 1) l / (qOf P : E)))
    (x : Sp E n) (hx : x ∈ LocE.parL P (qOf P) r n 0) : H x ∈ LocE.parL P (qOf P) r n 0 := by
  have hq0 : (qOf P : E) ≠ 0 := by exact_mod_cast (Formalism.L2.Ker.qOf_pos P).ne'
  rw [twParL_mem] at hx ⊢
  have hxI : ∀ l, IntAt P (x l) := fun l => by
    have := hx l
    by_cases hl : r ≤ l.1 ∧ l.1 < n
    · rw [if_pos hl, zpow_one] at this
      have e : x l = (qOf P : E) * ((qOf P : E)⁻¹ * x l) := by field_simp
      rw [e]; exact (ciIntAt_q (P := P) (q := qOf P)).mul this
    · rw [if_neg hl] at this; simpa using this
  have hxD : ∀ l : Fin n, r ≤ l.1 → IntAt P ((qOf P : E)⁻¹ * x l) := fun l hl => by
    have := hx l
    rw [if_pos ⟨hl, l.2⟩, zpow_one] at this
    exact this
  intro l
  rw [hH]
  by_cases hl : l.1 < n - 1
  · rw [dif_pos hl]
    by_cases hDl : r ≤ l.1
    · rw [if_pos ⟨hDl, l.2⟩, zpow_one]
      rw [twApply_coordE h' (twInit x) ⟨l.1, hl⟩, Finset.mul_sum]
      apply twIntAt_sum
      intro a
      have ea : (twE a : Sp E (n - 1)) = Pi.single a 1 := by
        funext j; unfold twE; simp [Pi.single_apply, eq_comm]
      rw [ea]
      by_cases ha : a.1 < r
      · have e : ((qOf P : E))⁻¹ * (twInit x a * h' (Pi.single a 1) ⟨l.1, hl⟩) =
            twInit x a * (h' (Pi.single a 1) ⟨l.1, hl⟩ / (qOf P : E)) := by field_simp
        rw [e]
        exact (hxI _).mul (hD a ⟨l.1, hl⟩ ha hDl)
      · have hxa := hxD ⟨a.1, by have := a.2; omega⟩ (by show r ≤ a.1; omega)
        have e : ((qOf P : E))⁻¹ * (twInit x a * h' (Pi.single a 1) ⟨l.1, hl⟩) =
            ((qOf P : E))⁻¹ * x ⟨a.1, by have := a.2; omega⟩ * h' (Pi.single a 1) ⟨l.1, hl⟩ := by
          unfold twInit; ring
        rw [e]
        refine hxa.mul (hint _ (fun j => ?_) _)
        by_cases hj : j = a
        · subst hj; simp only [Pi.single_eq_same]; exact ⟨1, 1, one_notMem P, by simp⟩
        · rw [Pi.single_eq_of_ne hj]; exact ⟨0, 1, one_notMem P, by simp⟩
    · rw [if_neg (fun h => hDl h.1), zpow_zero, inv_one, one_mul]
      exact hint (twInit x) (fun i => hxI _) ⟨l.1, hl⟩
  · rw [dif_neg hl]
    exact hx l

/- English proof (translation)
Establish `hn : 0 < n` using `by omega`. Use `set Gm : Sp E n ≃ₗ[E] Sp E n := (G : Sp E n ≃ₗ[E] Sp E n) with hGm`. Establish `hinitG : ∀ x, twInit (Gm x) = g' (twInit x)` using `fun x => by`. Use function extensionality and compare the values at `i`. Use `show Gm x ⟨i.1, by have := i.2; omega⟩ = g' (twInit x) i`.

Rewrite using `[hblk, dif_pos i.2]`. Establish `hlastG : ∀ x, Gm x (twLastI hn) = x (twLastI hn)` using `fun x => by`. Rewrite using `[hblk, dif_neg (by unfold twLastI; simp)]`. Establish `hinv : ∀ x (l : Fin n), Gm.symm x l = if h : l.1 < n - 1 then g'.symm (twInit x) ⟨l.1, h⟩ else x l`. Introduce `x l`.

Establish `hx : Gm (Gm.symm x) = x` using `Gm.apply_symm_apply x`. Distinguish the cases in `h : l.1 < n - 1`. Rewrite using `[dif_pos h]`. Establish `e1 : twInit (Gm.symm x) = g'.symm (twInit x)`. Establish `h2` using `hinitG (Gm.symm x)`.

Rewrite `h2` using `[hx]`. Rewrite using `[h2, LinearEquiv.symm_apply_apply]`. Use `congrFun e1 ⟨l.1, h⟩` as an intermediate fact. Unfold `twInit at this`. Conclude with `this`.

Rewrite using `[dif_neg h]`. Use `congrFun hx l` as an intermediate fact. Rewrite `this` using `[hblk, dif_neg h]`. Conclude with `this`. Establish `hinitG' : ∀ x, twInit (Gm.symm x) = g'.symm (twInit x)` using `fun x => by`.

Use function extensionality and compare the values at `i`. Use `show Gm.symm x ⟨i.1, by have := i.2; omega⟩ = g'.symm (twInit x) i`. Rewrite using `[hinv, dif_pos i.2]`. Establish `hlastG' : ∀ x, Gm.symm x (twLastI hn) = x (twLastI hn)` using `fun x => by`. Rewrite using `[hinv, dif_neg (by unfold twLastI; simp)]`.

Establish `hstd : ∀ v : Sp E n, (∀ l, IntAt P (v l)) → ∀ l, IntAt P (Gm v l)` using `fun v hv => (twStd_mem _).1 ((G.2 v).2 ((twStd_mem _).2 hv))`. Establish `hstd' : ∀ v : Sp E n, (∀ l, IntAt P (v l)) → ∀ l, IntAt P (Gm.symm v l)` using `fun v hv => (twStd_mem _).1 (((G⁻¹).2 v).2 ((twStd_mem _).2 hv))`. Establish `hsnoc : ∀ x' : Sp E (n - 1), (∀ i, IntAt P (x' i)) → ∀ l, IntAt P (twSnoc (n` using `n) x' 0 l) := fun x' hx l => by`. Unfold `twSnoc`. Use `split_ifs`.

Conclude with `hx _`. Conclude with `⟨0, 1, one_notMem P, by simp⟩`. Establish `hg1 : ∀ x' : Sp E (n - 1), (∀ i, IntAt P (x' i)) → ∀ i, IntAt P (g' x' i)` using `fun x' hx i => by`. Establish `h1` using `hstd _ (hsnoc x' hx) ⟨i.1, by have := i.2; omega⟩`. Rewrite `h1` using `[hblk, dif_pos i.2, twInit_snoc]`.

Conclude with `h1`. Establish `hg2 : ∀ x' : Sp E (n - 1), (∀ i, IntAt P (x' i)) → ∀ i, IntAt P (g'.symm x' i)` using `fun x' hx i => by`. Establish `h1` using `hstd' _ (hsnoc x' hx) ⟨i.1, by have := i.2; omega⟩`. Rewrite `h1` using `[hinv, dif_pos i.2, twInit_snoc]`. Conclude with `h1`.

Establish `hsc : ∀ (f : Sp E (n - 1) ≃ₗ[E] Sp E (n - 1)), (∀ x' : Sp E (n - 1), (∀ i, IntAt P (x' i)) → ∀ i, IntAt P (f x' i)) → ∀ x' : Sp E (n - 1), (∀ i, IntAt P (((qOf P : E) ^ (c : ℤ))⁻¹ * x' i)) → ∀ i, IntAt P (((qOf P : E) ^ (c : ℤ))⁻¹ * f x' i)` using `fun f hf x' hx i => by`. Establish `h1` using `hf (((qOf P : E) ^ (c : ℤ))⁻¹ • x') (fun j => by simpa [Pi.smul_apply, smul_eq_mul] using hx j) i`. Rewrite `h1` using `[map_smul]`. Simplify `h1` using `[Pi.smul_apply, smul_eq_mul]`. Establish `hJ : Gm ∈ LocE.JQ P (qOf P) r n 0`.

Use `⟨G.2, fun x => ⟨fun h => ?_, twPar_block P hr Gm g' hblk hg1 hDA x⟩⟩` and prove the remaining obligations. Use `twPar_block P hr Gm.symm g'.symm hinv hg2 hDA' _ h` as an intermediate fact. Rewrite `this` using `[LinearEquiv.symm_apply_apply]`. Then use the resulting hypothesis. Establish `hL : ∀ (x : Sp E n), x ∈ LocE.sclLat P (qOf P) n (kOneLastExponents n c) ↔ (∀ i, IntAt P (twInit x i)) ∧ IntAt P (((qOf P : E) ^ (c : ℤ))⁻¹ * x (twLastI hn))`. Introduce `x`.

Rewrite using `[ciMem_sclLat]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨fun i => ?_, ?_⟩` and prove the remaining obligations. Use `h ⟨i.1, by have := i.2; omega⟩` as an intermediate fact.

Unfold `kOneLastExponents at this`. Rewrite `this` using `[if_neg (show ¬ (i.1 + 1 = n) by have := i.2; omega)]`. Simplify `this` using `[twInit]`. Use `h (twLastI hn)` as an intermediate fact. Establish `e : kOneLastExponents n c (twLastI hn).1 = (c : ℤ)` using `by unfold kOneLastExponents twLastI; rw [if_pos (by simp; omega)]`.

Rewrite `this` using `[e]`. Conclude with `this`. Introduce and unpack `⟨h1, h2⟩ l`. Unfold `kOneLastExponents`. Distinguish the cases in `hl : l.1 + 1 = n`.

Rewrite using `[if_pos hl]`. Establish `e : l = twLastI hn` using `Fin.ext (by unfold twLastI; simp; omega)`. Rewrite using `[e]`. Conclude with `h2`. Rewrite using `[if_neg hl]`.

Simplify `h1 ⟨l.1, by have := l.2; omega⟩` using `[twInit]`. Establish `hX : ∀ (x : Sp E n), x ∈ LocE.sclLat P (qOf P) n (twistedLevelExponent n c) ↔ (∀ i, IntAt P (((qOf P : E) ^ (c : ℤ))⁻¹ * twInit x i)) ∧ IntAt P (x (twLastI hn))`. Introduce `x`. Rewrite using `[ciMem_sclLat]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Use `⟨fun i => ?_, ?_⟩` and prove the remaining obligations. Use `h ⟨i.1, by have := i.2; omega⟩` as an intermediate fact. Unfold `twistedLevelExponent at this`. Rewrite `this` using `[if_neg (show ¬ (i.1 + 1 = n) by have := i.2; omega)]`.

Simplify `this` using `[twInit]`. Use `h (twLastI hn)` as an intermediate fact. Establish `e : twistedLevelExponent n c (twLastI hn).1 = 0` using `by unfold twistedLevelExponent twLastI; rw [if_pos (by simp; omega)]`. Rewrite `this` using `[e, zpow_zero, inv_one, one_mul]`. Conclude with `this`.

Introduce and unpack `⟨h1, h2⟩ l`. Unfold `twistedLevelExponent`. Distinguish the cases in `hl : l.1 + 1 = n`. Rewrite using `[if_pos hl]`. Establish `e : l = twLastI hn` using `Fin.ext (by unfold twLastI; simp; omega)`.

Rewrite using `[e]`. Simplify using `using h2`. Rewrite using `[if_neg hl]`. Simplify `h1 ⟨l.1, by have := l.2; omega⟩` using `[twInit]`. Use `⟨hJ, fun x => ?_, fun x => ?_, fun w hw => ?_⟩` and prove the remaining obligations.

Use `show Gm x ∈ _ ↔ x ∈ _`. Rewrite using `[hL, hL, hinitG, hlastG]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Use `⟨fun i => ?_, h2⟩` and prove the remaining obligations.

Use `hg2 _ h1 i` as an intermediate fact. Rewrite `this` using `[LinearEquiv.symm_apply_apply]`. Then use the resulting hypothesis. Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨hg1 _ h1, h2⟩`. Use `show Gm x ∈ _ ↔ x ∈ _`.

Rewrite using `[hX, hX, hinitG, hlastG]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Use `⟨fun i => ?_, h2⟩` and prove the remaining obligations. Use `hsc g'.symm hg2 _ h1 i` as an intermediate fact.

Rewrite `this` using `[LinearEquiv.symm_apply_apply]`. Then use the resulting hypothesis. Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨hsc g' hg1 _ h1, h2⟩`. Rewrite `hw` using `[hX]`. Rewrite using `[ciMem_sclLat]`.

Introduce `l`. Use `show IntAt P (((qOf P : E) ^ (c : ℤ))⁻¹ * (Gm w l - w l))`. Rewrite using `[hblk]`. Distinguish the cases in `hl : l.1 < n - 1`. Rewrite using `[dif_pos hl, mul_sub]`.

Establish `a1` using `hsc g' hg1 _ hw.1 ⟨l.1, hl⟩`. Establish `a2` using `hw.1 ⟨l.1, hl⟩`. Unfold `twInit at a2`. Conclude with `ciIntAt_sub a1 a2`. Rewrite using `[dif_neg hl, sub_self, mul_zero]; exact ⟨0, 1, one_notMem P, by simp⟩`.
-/
theorem mem_kOne_of_block {n r c : ℕ} (hr : r < n) (G : ↥(GLint E n P)) (g' : Sp E (n - 1) ≃ₗ[E] Sp E (n - 1))
    (hblk : ∀ x (l : Fin n), (G : Sp E n ≃ₗ[E] Sp E n) x l = if h : l.1 < n - 1 then g' (twInit x) ⟨l.1, h⟩ else x l)
    (hDA : ∀ a l : Fin (n - 1), a.1 < r → r ≤ l.1 → IntAt P (g' (Pi.single a 1) l / (qOf P : E)))
    (hDA' : ∀ a l : Fin (n - 1), a.1 < r → r ≤ l.1 → IntAt P (g'.symm (Pi.single a 1) l / (qOf P : E))) :
    G ∈ twK1H P n r c := by
  have hn : 0 < n := by omega
  set Gm : Sp E n ≃ₗ[E] Sp E n := (G : Sp E n ≃ₗ[E] Sp E n) with hGm
  have hinitG : ∀ x, twInit (Gm x) = g' (twInit x) := fun x => by
    funext i
    show Gm x ⟨i.1, by have := i.2; omega⟩ = g' (twInit x) i
    rw [hblk, dif_pos i.2]
  have hlastG : ∀ x, Gm x (twLastI hn) = x (twLastI hn) := fun x => by
    rw [hblk, dif_neg (by unfold twLastI; simp)]
  have hinv : ∀ x (l : Fin n), Gm.symm x l = if h : l.1 < n - 1 then g'.symm (twInit x) ⟨l.1, h⟩ else x l := by
    intro x l
    have hx : Gm (Gm.symm x) = x := Gm.apply_symm_apply x
    by_cases h : l.1 < n - 1
    · rw [dif_pos h]
      have e1 : twInit (Gm.symm x) = g'.symm (twInit x) := by
        have h2 := hinitG (Gm.symm x)
        rw [hx] at h2
        rw [h2, LinearEquiv.symm_apply_apply]
      have := congrFun e1 ⟨l.1, h⟩
      unfold twInit at this
      exact this
    · rw [dif_neg h]
      have := congrFun hx l
      rw [hblk, dif_neg h] at this
      exact this
  have hinitG' : ∀ x, twInit (Gm.symm x) = g'.symm (twInit x) := fun x => by
    funext i
    show Gm.symm x ⟨i.1, by have := i.2; omega⟩ = g'.symm (twInit x) i
    rw [hinv, dif_pos i.2]
  have hlastG' : ∀ x, Gm.symm x (twLastI hn) = x (twLastI hn) := fun x => by
    rw [hinv, dif_neg (by unfold twLastI; simp)]

  have hstd : ∀ v : Sp E n, (∀ l, IntAt P (v l)) → ∀ l, IntAt P (Gm v l) := fun v hv =>
    (twStd_mem _).1 ((G.2 v).2 ((twStd_mem _).2 hv))
  have hstd' : ∀ v : Sp E n, (∀ l, IntAt P (v l)) → ∀ l, IntAt P (Gm.symm v l) := fun v hv =>
    (twStd_mem _).1 (((G⁻¹).2 v).2 ((twStd_mem _).2 hv))
  have hsnoc : ∀ x' : Sp E (n - 1), (∀ i, IntAt P (x' i)) → ∀ l, IntAt P (twSnoc (n := n) x' 0 l) := fun x' hx l => by
    unfold twSnoc; split_ifs
    · exact hx _
    · exact ⟨0, 1, one_notMem P, by simp⟩
  have hg1 : ∀ x' : Sp E (n - 1), (∀ i, IntAt P (x' i)) → ∀ i, IntAt P (g' x' i) := fun x' hx i => by
    have h1 := hstd _ (hsnoc x' hx) ⟨i.1, by have := i.2; omega⟩
    rw [hblk, dif_pos i.2, twInit_snoc] at h1
    exact h1
  have hg2 : ∀ x' : Sp E (n - 1), (∀ i, IntAt P (x' i)) → ∀ i, IntAt P (g'.symm x' i) := fun x' hx i => by
    have h1 := hstd' _ (hsnoc x' hx) ⟨i.1, by have := i.2; omega⟩
    rw [hinv, dif_pos i.2, twInit_snoc] at h1
    exact h1
  have hsc : ∀ (f : Sp E (n - 1) ≃ₗ[E] Sp E (n - 1)), (∀ x' : Sp E (n - 1), (∀ i, IntAt P (x' i)) → ∀ i, IntAt P (f x' i)) →
      ∀ x' : Sp E (n - 1), (∀ i, IntAt P (((qOf P : E) ^ (c : ℤ))⁻¹ * x' i)) → ∀ i, IntAt P (((qOf P : E) ^ (c : ℤ))⁻¹ * f x' i) :=
    fun f hf x' hx i => by
      have h1 := hf (((qOf P : E) ^ (c : ℤ))⁻¹ • x') (fun j => by simpa [Pi.smul_apply, smul_eq_mul] using hx j) i
      rw [map_smul] at h1
      simpa [Pi.smul_apply, smul_eq_mul] using h1
  have hJ : Gm ∈ LocE.JQ P (qOf P) r n 0 := by
    refine ⟨G.2, fun x => ⟨fun h => ?_, twPar_block P hr Gm g' hblk hg1 hDA x⟩⟩
    have := twPar_block P hr Gm.symm g'.symm hinv hg2 hDA' _ h
    rwa [LinearEquiv.symm_apply_apply] at this

  have hL : ∀ (x : Sp E n), x ∈ LocE.sclLat P (qOf P) n (kOneLastExponents n c) ↔ (∀ i, IntAt P (twInit x i)) ∧
      IntAt P (((qOf P : E) ^ (c : ℤ))⁻¹ * x (twLastI hn)) := by
    intro x
    rw [ciMem_sclLat]
    constructor
    · intro h
      refine ⟨fun i => ?_, ?_⟩
      · have := h ⟨i.1, by have := i.2; omega⟩
        unfold kOneLastExponents at this
        rw [if_neg (show ¬ (i.1 + 1 = n) by have := i.2; omega)] at this
        simpa [twInit] using this
      · have := h (twLastI hn)
        have e : kOneLastExponents n c (twLastI hn).1 = (c : ℤ) := by unfold kOneLastExponents twLastI; rw [if_pos (by simp; omega)]
        rw [e] at this
        exact this
    · rintro ⟨h1, h2⟩ l
      unfold kOneLastExponents
      by_cases hl : l.1 + 1 = n
      · rw [if_pos hl]
        have e : l = twLastI hn := Fin.ext (by unfold twLastI; simp; omega)
        rw [e]; exact h2
      · rw [if_neg hl]
        simpa [twInit] using h1 ⟨l.1, by have := l.2; omega⟩
  have hX : ∀ (x : Sp E n), x ∈ LocE.sclLat P (qOf P) n (twistedLevelExponent n c) ↔
      (∀ i, IntAt P (((qOf P : E) ^ (c : ℤ))⁻¹ * twInit x i)) ∧ IntAt P (x (twLastI hn)) := by
    intro x
    rw [ciMem_sclLat]
    constructor
    · intro h
      refine ⟨fun i => ?_, ?_⟩
      · have := h ⟨i.1, by have := i.2; omega⟩
        unfold twistedLevelExponent at this
        rw [if_neg (show ¬ (i.1 + 1 = n) by have := i.2; omega)] at this
        simpa [twInit] using this
      · have := h (twLastI hn)
        have e : twistedLevelExponent n c (twLastI hn).1 = 0 := by unfold twistedLevelExponent twLastI; rw [if_pos (by simp; omega)]
        rw [e, zpow_zero, inv_one, one_mul] at this
        exact this
    · rintro ⟨h1, h2⟩ l
      unfold twistedLevelExponent
      by_cases hl : l.1 + 1 = n
      · rw [if_pos hl]
        have e : l = twLastI hn := Fin.ext (by unfold twLastI; simp; omega)
        rw [e]; simpa using h2
      · rw [if_neg hl]
        simpa [twInit] using h1 ⟨l.1, by have := l.2; omega⟩
  refine ⟨hJ, fun x => ?_, fun x => ?_, fun w hw => ?_⟩
  · show Gm x ∈ _ ↔ x ∈ _
    rw [hL, hL, hinitG, hlastG]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun i => ?_, h2⟩
      have := hg2 _ h1 i
      rwa [LinearEquiv.symm_apply_apply] at this
    · rintro ⟨h1, h2⟩
      exact ⟨hg1 _ h1, h2⟩
  · show Gm x ∈ _ ↔ x ∈ _
    rw [hX, hX, hinitG, hlastG]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun i => ?_, h2⟩
      have := hsc g'.symm hg2 _ h1 i
      rwa [LinearEquiv.symm_apply_apply] at this
    · rintro ⟨h1, h2⟩
      exact ⟨hsc g' hg1 _ h1, h2⟩
  · rw [hX] at hw
    rw [ciMem_sclLat]
    intro l
    show IntAt P (((qOf P : E) ^ (c : ℤ))⁻¹ * (Gm w l - w l))
    rw [hblk]
    by_cases hl : l.1 < n - 1
    · rw [dif_pos hl, mul_sub]
      have a1 := hsc g' hg1 _ hw.1 ⟨l.1, hl⟩
      have a2 := hw.1 ⟨l.1, hl⟩
      unfold twInit at a2
      exact ciIntAt_sub a1 a2
    · rw [dif_neg hl, sub_self, mul_zero]; exact ⟨0, 1, one_notMem P, by simp⟩

end TwTopQ

end Formalism.L2.Col
