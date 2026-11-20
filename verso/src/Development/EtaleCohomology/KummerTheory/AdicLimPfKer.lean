import Development.EtaleCohomology.KummerTheory.AdicLimPf
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsBisTail

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

universe u

namespace LateralTheory.KummerTheory.KerPf

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.DYra4.main S t`.
-/
theorem seqSec (S : ℕ → Type u) [∀ a, Finite (S a)] [∀ a, Nonempty (S a)] (t : ∀ a, S (a + 1) → S a) :
    ∃ s : ∀ a, S a, ∀ a, t a (s (a + 1)) = s a :=
  _root_.UpperTheory.Reformulated.B.DYra4.main S t

variable (l : ℕ) [Fact l.Prime]

/- English proof (translation)
Establish `hl : NeZero l` using `⟨(Fact.out : l.Prime).ne_zero⟩`. Introduce `a`. Proceed by induction on `a with`. Consider the case `zero => exact (@hA (l ^ m) (l ^ m) _ dvd_rfl E).2.2.1 n i _`. Consider the case `succ a ih`.

Establish `h` using `(@hA (l ^ (m + (a + 1))) (l ^ (m + a)) _ (pow_dvd_pow l (by omega)) E).2.2.2 (l ^ m) (pow_dvd_pow l (by omega)) n i (x.1 (m + (a + 1)))`. Rewrite using `[← h, ← ih]`. Conclude with `congrArg _ (x.2 (m + a))`.
-/
theorem redk (hA : A11) (E : Spc) (n i : ℤ) (x : Hl l E n i) (m : ℕ) :
    ∀ a : ℕ, red (l ^ (m + a)) (l ^ m) E n i (x.1 (m + a)) = x.1 m := by
  have hl : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  intro a
  induction a with
  | zero => exact (@hA (l ^ m) (l ^ m) _ dvd_rfl E).2.2.1 n i _
  | succ a ih =>
    have h := (@hA (l ^ (m + (a + 1))) (l ^ (m + a)) _ (pow_dvd_pow l (by omega)) E).2.2.2 (l ^ m)
      (pow_dvd_pow l (by omega)) n i (x.1 (m + (a + 1)))
    rw [← h, ← ih]
    exact congrArg _ (x.2 (m + a))

omit [Fact l.Prime] in
/- English proof (translation)
Rewrite using `[← Nat.cast_smul_eq_nsmul (ZMod (l ^ k)), (CharP.cast_eq_zero_iff (ZMod (l ^ k)) (l ^ k) _).2 (pow_dvd_pow l hkb), zero_smul]`.
-/
theorem smul_zero_of (E : Spc) (n i : ℤ) (k b : ℕ) (hkb : k ≤ b) (z : Ht (l ^ k) E n i) : (l ^ b) • z = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod (l ^ k)), (CharP.cast_eq_zero_iff (ZMod (l ^ k)) (l ^ k) _).2 (pow_dvd_pow l hkb), zero_smul]

/- English proof (translation)
Take `⟨u, d, h⟩` from `hB b`. Set `S : ℕ → Type 1` to `fun a => {w : Ht (l ^ a) E n i // u a n w = x.1 (b + a)}`. Establish `hS : ∀ a, Finite (S a)` using `fun a => by have := hFin a n; exact Subtype.finite`. Establish `hN : ∀ a, Nonempty (S a)` using `fun a => by`. Take `⟨w, hw⟩` from `((h a n).1 (x.1 (b + a))).1 (by rw [redk l hA E n i x b a]; exact hx)`.

Conclude with `⟨⟨w, hw⟩⟩`. Set `t : ∀ a, S (a + 1) → S a` to `fun a w => ⟨red (l ^ (a + 1)) (l ^ a) E n i w.1, by`. Rewrite using `[← (h a n).2.2.2.2.2 w.1, w.2]`. Conclude with `x.2 (b + a)⟩`. Take `⟨s, hs⟩` from `seqSec S t`.

Set `y : Hl l E n i` to `⟨fun a => (s a).1, fun a => congrArg Subtype.val (hs a)⟩`. Use `⟨y, ?_⟩` and prove the remaining obligations. Establish `e : ((l : ℤ_[l]) ^ b) • y = (l ^ b : ℕ) • y`. Rewrite using `[← Nat.cast_smul_eq_nsmul ℤ_[l]]`. Use `push_cast`.

Both sides reduce to the same expression. Rewrite using `[e]`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `k`. Express the relevant statement in the definitionally equal form `x.1 k = (l ^ b) • (s k).1`.

Break down `le_or_gt b k with hk | hk` into its components or cases. Take `⟨a, rfl⟩` from `Nat.exists_eq_add_of_le hk`. Establish `hr` using `redk l hA E n i y a b`. Rewrite `hr` using `[Nat.add_comm a b]`. Rewrite using `[← (h a n).2.2.2.1 ((s (b + a)).1)]`.

Express the relevant statement in the definitionally equal form `x.1 (b + a) = u a n (red _ _ E n i (y.1 (b + a)))`. Rewrite using `[hr]`. Conclude with `(s a).2.symm`. Rewrite using `[smul_zero_of l E n i k b hk.le]`. Take `⟨c, rfl⟩` from `Nat.exists_eq_add_of_le hk.le`.

Rewrite using `[← redk l hA E n i x k c]`. Express the relevant statement in the definitionally equal form `red _ _ E n i (lev l x (k + c)) = 0`. Rewrite using `[hx, map_zero]`.
-/
theorem ker (hA : A11) (E : Spc) (i : ℤ) (hB : ∀ b, BockData l b E i)
    (hFin : ∀ (k : ℕ) (n : ℤ), Finite (Ht (l ^ k) E n i)) (n : ℤ) (b : ℕ) (x : Hl l E n i) (hx : lev l x b = 0) :
    ∃ y : Hl l E n i, x = ((l : ℤ_[l]) ^ b) • y := by
  obtain ⟨u, d, h⟩ := hB b
  let S : ℕ → Type 1 := fun a => {w : Ht (l ^ a) E n i // u a n w = x.1 (b + a)}
  have hS : ∀ a, Finite (S a) := fun a => by have := hFin a n; exact Subtype.finite
  have hN : ∀ a, Nonempty (S a) := fun a => by
    obtain ⟨w, hw⟩ := ((h a n).1 (x.1 (b + a))).1 (by rw [redk l hA E n i x b a]; exact hx)
    exact ⟨⟨w, hw⟩⟩
  let t : ∀ a, S (a + 1) → S a := fun a w => ⟨red (l ^ (a + 1)) (l ^ a) E n i w.1, by
    rw [← (h a n).2.2.2.2.2 w.1, w.2]; exact x.2 (b + a)⟩
  obtain ⟨s, hs⟩ := seqSec S t
  let y : Hl l E n i := ⟨fun a => (s a).1, fun a => congrArg Subtype.val (hs a)⟩
  refine ⟨y, ?_⟩
  have e : ((l : ℤ_[l]) ^ b) • y = (l ^ b : ℕ) • y := by
    rw [← Nat.cast_smul_eq_nsmul ℤ_[l]]; push_cast; rfl
  rw [e]
  apply Subtype.ext
  funext k
  change x.1 k = (l ^ b) • (s k).1
  rcases le_or_gt b k with hk | hk
  · obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hk
    have hr := redk l hA E n i y a b
    rw [Nat.add_comm a b] at hr
    rw [← (h a n).2.2.2.1 ((s (b + a)).1)]
    change x.1 (b + a) = u a n (red _ _ E n i (y.1 (b + a)))
    rw [hr]
    exact (s a).2.symm
  · rw [smul_zero_of l E n i k b hk.le]
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hk.le
    rw [← redk l hA E n i x k c]
    change red _ _ E n i (lev l x (k + c)) = 0
    rw [hx, map_zero]

end LateralTheory.KummerTheory.KerPf

namespace LateralTheory.KummerTheory

/- English proof (translation)
Introduce `hA l _ E i hB hFin n k x hx` and use `KerPf.ker l hA E i hB hFin n k x hx`.
-/
theorem AdicKer_holds : AdicKer := fun hA l _ E i hB hFin n k x hx => KerPf.ker l hA E i hB hFin n k x hx

end LateralTheory.KummerTheory
