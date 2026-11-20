import ReciprocityTheory.DualLattices.SeriesState
import ReciprocityTheory.DualLattices.InstAddCommMonoidFibreFst
import ReciprocityTheory.DualLattices.NsmulFstAddSnd

noncomputable section

namespace ReciprocityTheory.PGsh

universe u

variable {R₀ : Type u} [CommRing R₀]

namespace BX

variable (B : BX R₀) {R : LAlg R₀}

/- English proof (translation)
Substitute `h` using the available equality. Prove the components needed by the constructor for the conclusion. Introduce `e`. Rewrite using `[← e]`. Both sides reduce to the same expression.

Introduce `e`. Conclude with `eq_of_heq (Sigma.mk.inj e).2`.
-/
lemma castFst_eq_iff {a b y : B.G R} (h : a = b) (u : B.P R a y) (w : B.P R b y) :
    B.tr1 h u = w ↔ (⟨a, u⟩ : B.S1 R y) = ⟨b, w⟩ := by
  subst h
  constructor
  · intro e
    rw [← e]
    rfl
  · intro e
    exact eq_of_heq (Sigma.mk.inj e).2

/- English proof (translation)
Substitute `h` using the available equality. Prove the components needed by the constructor for the conclusion. Introduce `e`. Rewrite using `[← e]`. Both sides reduce to the same expression.

Introduce `e`. Conclude with `eq_of_heq (Sigma.mk.inj e).2`.
-/
lemma castSnd_eq_iff {a b x : B.G R} (h : a = b) (u : B.P R x a) (w : B.P R x b) :
    B.tr2 h u = w ↔ (⟨a, u⟩ : B.S2 R x) = ⟨b, w⟩ := by
  subst h
  constructor
  · intro e
    rw [← e]
    rfl
  · intro e
    exact eq_of_heq (Sigma.mk.inj e).2

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
lemma castFst_smul {a b y : B.G R} (h : a = b) (l : (R : Type u)ˣ) (u : B.P R a y) :
    B.tr1 h (B.smul l u) = B.smul l (B.tr1 h u) := by
  subst h
  rfl

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
lemma castSnd_smul {a b x : B.G R} (h : a = b) (l : (R : Type u)ˣ) (u : B.P R x a) :
    B.tr2 h (B.smul l u) = B.smul l (B.tr2 h u) := by
  subst h
  rfl

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
lemma castSnd_addFst {x x' y y' : B.G R} (h : y = y') (u : B.P R x y) (u' : B.P R x' y) :
    B.tr2 h (B.add1 u u') = B.add1 (B.tr2 h u) (B.tr2 h u') := by
  subst h
  rfl

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
lemma castFst_addSnd {x x' y y' : B.G R} (h : x = x') (u : B.P R x y) (u' : B.P R x y') :
    B.tr1 h (B.add2 u u') = B.add2 (B.tr1 h u) (B.tr1 h u') := by
  subst h
  rfl

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
lemma swap_castSnd {x y y' : B.G R} (h : y = y') (u : B.P R x y) :
    B.sw (B.tr2 h u) = B.tr1 h (B.sw u) := by
  subst h
  rfl

/- English proof (translation)
Rewrite using `[← B.sw_sw (B.nsmul1 (B.sw u) n), B.sw_nsmul1, B.sw_sw]`.
-/
lemma sw_nsmul2 {x y : B.G R} (u : B.P R x y) (n : ℕ) :
    B.sw (B.nsmul2 u n) = B.nsmul1 (B.sw u) n := by
  rw [← B.sw_sw (B.nsmul1 (B.sw u) n), B.sw_nsmul1, B.sw_sw]

/- English proof (translation)
Take `⟨u⟩` from `B.nonempty R x y`. Take `⟨l₁, hl₁, -⟩` from `B.trans (B.zero1 y) (B.tr1 hx (B.nsmul1 u N))`. Take `⟨l₂, hl₂, -⟩` from `B.trans (B.zero2 x) (B.tr2 hy (B.nsmul2 u N))`. Conclude with `⟨l₁ / l₂, hx, hy, u, l₁, l₂, hl₁.symm, hl₂.symm, rfl⟩`.
-/
theorem pairing_exists (N : ℕ) (x y : B.G R) (hx : N • x = 0) (hy : N • y = 0) :
    ∃ z, B.IsPairing N x y z := by
  obtain ⟨u⟩ := B.nonempty R x y
  obtain ⟨l₁, hl₁, -⟩ := B.trans (B.zero1 y) (B.tr1 hx (B.nsmul1 u N))
  obtain ⟨l₂, hl₂, -⟩ := B.trans (B.zero2 x) (B.tr2 hy (B.nsmul2 u N))
  exact ⟨l₁ / l₂, hx, hy, u, l₁, l₂, hl₁.symm, hl₂.symm, rfl⟩

/- English proof (translation)
Take `⟨hx, hy, u, l₁, l₂, e₁, e₂, rfl⟩` from `h`. Take `⟨hx', hy', u', m₁, m₂, f₁, f₂, rfl⟩` from `h'`. Take `⟨c, hc, -⟩` from `B.trans u u'`. Substitute `hc` using the available equality. Establish `inj : ∀ {a b : B.G R} (v : B.P R a b) (l l' : (R : Type u)ˣ), B.smul l v = B.smul l' v → l = l'` using `fun v l l' h => (B.trans v (B.smul l v)).unique rfl h.symm`.

Rewrite `f₁` using `[B.nsmul1_smul, B.castFst_smul, e₁, ← B.mul_smul]`. Rewrite `f₂` using `[B.nsmul2_smul, B.castSnd_smul, e₂, ← B.mul_smul]`. Rewrite using `[← inj _ _ _ f₁, ← inj _ _ _ f₂]`. Conclude with `(mul_div_mul_left_eq_div _ _ _).symm`.
-/
theorem pairing_unique (N : ℕ) (x y : B.G R) (z z' : (R : Type u)ˣ) (h : B.IsPairing N x y z)
    (h' : B.IsPairing N x y z') : z = z' := by
  obtain ⟨hx, hy, u, l₁, l₂, e₁, e₂, rfl⟩ := h
  obtain ⟨hx', hy', u', m₁, m₂, f₁, f₂, rfl⟩ := h'

  obtain ⟨c, hc, -⟩ := B.trans u u'
  subst hc
  have inj : ∀ {a b : B.G R} (v : B.P R a b) (l l' : (R : Type u)ˣ), B.smul l v = B.smul l' v → l = l' :=
    fun v l l' h => (B.trans v (B.smul l v)).unique rfl h.symm
  rw [B.nsmul1_smul, B.castFst_smul, e₁, ← B.mul_smul] at f₁
  rw [B.nsmul2_smul, B.castSnd_smul, e₂, ← B.mul_smul] at f₂
  rw [← inj _ _ _ f₁, ← inj _ _ _ f₂]
  exact (mul_div_mul_left_eq_div _ _ _).symm

/- English proof (translation)
Take `⟨hx, hy, u, l₁, l₂, e₁, e₂, rfl⟩` from `h`. Take `⟨hx', hy', u', m₁, m₂, f₁, f₂, rfl⟩` from `h'`. Establish `hxx : N • (x + x') = 0` using `by rw [nsmul_add, hx, hx', add_zero]`. Establish `hsm : ∀ (c : (R : Type u)ˣ) {a b : B.G R} (e : a = b) (v : B.P R a y) (v' : B.P R b y), HEq v v' → HEq (B.smul c v) (B.smul c v')`. Introduce `c a b e v v' hv`.

Substitute `e` using the available equality. Rewrite using `[eq_of_heq hv]`. Use `⟨hxx, hy, B.add1 u u', l₁ * m₁, l₂ * m₂, ?_, ?_, div_mul_div_comm _ _ _ _⟩` and prove the remaining obligations. Establish `hS : (⟨N • (x + x'), B.nsmul1 (B.add1 u u') N⟩ : B.S1 R y) = ⟨N • x + N • x', B.add1 (B.nsmul1 u N) (B.nsmul1 u' N)⟩`. Rewrite using `[← B.fibreFst_nsmul_mk]`.

Use `show N • (B.S1mk u + B.S1mk u') = _`. Rewrite using `[smul_add, B.fibreFst_nsmul_mk, B.fibreFst_nsmul_mk]`. Both sides reduce to the same expression. Establish `e₁'` using `(B.castFst_eq_iff hx _ _).1 e₁`. Establish `f₁'` using `(B.castFst_eq_iff hx' _ _).1 f₁`.

Rewrite using `[B.castFst_eq_iff, hS]`. Establish `ee : B.S1mk (B.nsmul1 u N) = B.S1mk (B.smul l₁ (B.zero1 y))` using `e₁'`. Establish `ff : B.S1mk (B.nsmul1 u' N) = B.S1mk (B.smul m₁ (B.zero1 y))` using `f₁'`. Use `show B.S1mk (B.add1 (B.nsmul1 u N) (B.nsmul1 u' N)) = B.S1mk (B.smul (l₁ * m₁) (B.zero1 y))`. Establish `step : B.S1mk (B.add1 (B.nsmul1 u N) (B.nsmul1 u' N)) = B.S1mk (B.nsmul1 u N) + B.S1mk (B.nsmul1 u' N)` using `rfl`.

Establish `step2 : B.S1mk (B.smul l₁ (B.zero1 y)) + B.S1mk (B.smul m₁ (B.zero1 y)) = B.S1mk (B.add1 (B.smul l₁ (B.zero1 y)) (B.smul m₁ (B.zero1 y)))` using `rfl`. Rewrite using `[step, ee, ff, step2, B.addFst_smul]`. Conclude with `Sigma.ext (add_zero 0) (hsm _ (add_zero 0) _ _ (B.zeroFst_add (B.zero1 y)))`. Rewrite using `[B.nsmulSnd_addFst, B.castSnd_addFst, e₂, f₂, B.addFst_smul, B.zeroSnd_addFst]`.
-/
theorem isPairingValue_add_left (N : ℕ) (x x' y : B.G R) (z z' : (R : Type u)ˣ) (h : B.IsPairing N x y z)
    (h' : B.IsPairing N x' y z') : B.IsPairing N (x + x') y (z * z') := by
  obtain ⟨hx, hy, u, l₁, l₂, e₁, e₂, rfl⟩ := h
  obtain ⟨hx', hy', u', m₁, m₂, f₁, f₂, rfl⟩ := h'
  have hxx : N • (x + x') = 0 := by rw [nsmul_add, hx, hx', add_zero]
  have hsm : ∀ (c : (R : Type u)ˣ) {a b : B.G R} (e : a = b) (v : B.P R a y) (v' : B.P R b y), HEq v v' →
      HEq (B.smul c v) (B.smul c v') := by
    intro c a b e v v' hv
    subst e
    rw [eq_of_heq hv]
  refine ⟨hxx, hy, B.add1 u u', l₁ * m₁, l₂ * m₂, ?_, ?_, div_mul_div_comm _ _ _ _⟩
  ·
    have hS : (⟨N • (x + x'), B.nsmul1 (B.add1 u u') N⟩ : B.S1 R y) =
        ⟨N • x + N • x', B.add1 (B.nsmul1 u N) (B.nsmul1 u' N)⟩ := by
      rw [← B.fibreFst_nsmul_mk]
      show N • (B.S1mk u + B.S1mk u') = _
      rw [smul_add, B.fibreFst_nsmul_mk, B.fibreFst_nsmul_mk]
      rfl
    have e₁' := (B.castFst_eq_iff hx _ _).1 e₁
    have f₁' := (B.castFst_eq_iff hx' _ _).1 f₁
    rw [B.castFst_eq_iff, hS]
    have ee : B.S1mk (B.nsmul1 u N) = B.S1mk (B.smul l₁ (B.zero1 y)) := e₁'
    have ff : B.S1mk (B.nsmul1 u' N) = B.S1mk (B.smul m₁ (B.zero1 y)) := f₁'
    show B.S1mk (B.add1 (B.nsmul1 u N) (B.nsmul1 u' N)) = B.S1mk (B.smul (l₁ * m₁) (B.zero1 y))
    have step : B.S1mk (B.add1 (B.nsmul1 u N) (B.nsmul1 u' N)) = B.S1mk (B.nsmul1 u N) + B.S1mk (B.nsmul1 u' N) := rfl
    have step2 : B.S1mk (B.smul l₁ (B.zero1 y)) + B.S1mk (B.smul m₁ (B.zero1 y)) =
        B.S1mk (B.add1 (B.smul l₁ (B.zero1 y)) (B.smul m₁ (B.zero1 y))) := rfl
    rw [step, ee, ff, step2, B.addFst_smul]
    exact Sigma.ext (add_zero 0) (hsm _ (add_zero 0) _ _ (B.zeroFst_add (B.zero1 y)))
  · rw [B.nsmulSnd_addFst, B.castSnd_addFst, e₂, f₂, B.addFst_smul, B.zeroSnd_addFst]

/- English proof (translation)
Take `⟨hx, hy, u, l₁, l₂, e₁, e₂, rfl⟩` from `h`. Take `⟨hx', hy', u', m₁, m₂, f₁, f₂, rfl⟩` from `h'`. Establish `hyy : N • (y + y') = 0` using `by rw [nsmul_add, hy, hy', add_zero]`. Establish `hsm : ∀ (c : (R : Type u)ˣ) {a b : B.G R} (e : a = b) (v : B.P R x a) (v' : B.P R x b), HEq v v' → HEq (B.smul c v) (B.smul c v')`. Introduce `c a b e v v' hv`.

Substitute `e` using the available equality. Rewrite using `[eq_of_heq hv]`. Use `⟨hx, hyy, B.add2 u u', l₁ * m₁, l₂ * m₂, ?_, ?_, div_mul_div_comm _ _ _ _⟩` and prove the remaining obligations. Rewrite using `[B.nsmulFst_addSnd, B.castFst_addSnd, e₁, f₁, B.addSnd_smul, B.zeroFst_addSnd]`. Establish `hS : (⟨N • (y + y'), B.nsmul2 (B.add2 u u') N⟩ : B.S2 R x) = ⟨N • y + N • y', B.add2 (B.nsmul2 u N) (B.nsmul2 u' N)⟩`.

Rewrite using `[← B.fibreSnd_nsmul_mk]`. Use `show N • (B.S2mk u + B.S2mk u') = _`. Rewrite using `[smul_add, B.fibreSnd_nsmul_mk, B.fibreSnd_nsmul_mk]`. Both sides reduce to the same expression. Establish `e₂'` using `(B.castSnd_eq_iff hy _ _).1 e₂`.

Establish `f₂'` using `(B.castSnd_eq_iff hy' _ _).1 f₂`. Rewrite using `[B.castSnd_eq_iff, hS]`. Establish `ee : B.S2mk (B.nsmul2 u N) = B.S2mk (B.smul l₂ (B.zero2 x))` using `e₂'`. Establish `ff : B.S2mk (B.nsmul2 u' N) = B.S2mk (B.smul m₂ (B.zero2 x))` using `f₂'`. Use `show B.S2mk (B.add2 (B.nsmul2 u N) (B.nsmul2 u' N)) = B.S2mk (B.smul (l₂ * m₂) (B.zero2 x))`.

Establish `step : B.S2mk (B.add2 (B.nsmul2 u N) (B.nsmul2 u' N)) = B.S2mk (B.nsmul2 u N) + B.S2mk (B.nsmul2 u' N)` using `rfl`. Establish `step2 : B.S2mk (B.smul l₂ (B.zero2 x)) + B.S2mk (B.smul m₂ (B.zero2 x)) = B.S2mk (B.add2 (B.smul l₂ (B.zero2 x)) (B.smul m₂ (B.zero2 x)))` using `rfl`. Rewrite using `[step, ee, ff, step2, B.addSnd_smul]`. Conclude with `Sigma.ext (add_zero 0) (hsm _ (add_zero 0) _ _ (B.zeroSnd_add (B.zero2 x)))`.
-/
theorem isPairingValue_add_right (N : ℕ) (x y y' : B.G R) (z z' : (R : Type u)ˣ) (h : B.IsPairing N x y z)
    (h' : B.IsPairing N x y' z') : B.IsPairing N x (y + y') (z * z') := by
  obtain ⟨hx, hy, u, l₁, l₂, e₁, e₂, rfl⟩ := h
  obtain ⟨hx', hy', u', m₁, m₂, f₁, f₂, rfl⟩ := h'
  have hyy : N • (y + y') = 0 := by rw [nsmul_add, hy, hy', add_zero]
  have hsm : ∀ (c : (R : Type u)ˣ) {a b : B.G R} (e : a = b) (v : B.P R x a) (v' : B.P R x b), HEq v v' →
      HEq (B.smul c v) (B.smul c v') := by
    intro c a b e v v' hv
    subst e
    rw [eq_of_heq hv]
  refine ⟨hx, hyy, B.add2 u u', l₁ * m₁, l₂ * m₂, ?_, ?_, div_mul_div_comm _ _ _ _⟩
  · rw [B.nsmulFst_addSnd, B.castFst_addSnd, e₁, f₁, B.addSnd_smul, B.zeroFst_addSnd]
  ·
    have hS : (⟨N • (y + y'), B.nsmul2 (B.add2 u u') N⟩ : B.S2 R x) =
        ⟨N • y + N • y', B.add2 (B.nsmul2 u N) (B.nsmul2 u' N)⟩ := by
      rw [← B.fibreSnd_nsmul_mk]
      show N • (B.S2mk u + B.S2mk u') = _
      rw [smul_add, B.fibreSnd_nsmul_mk, B.fibreSnd_nsmul_mk]
      rfl
    have e₂' := (B.castSnd_eq_iff hy _ _).1 e₂
    have f₂' := (B.castSnd_eq_iff hy' _ _).1 f₂
    rw [B.castSnd_eq_iff, hS]
    have ee : B.S2mk (B.nsmul2 u N) = B.S2mk (B.smul l₂ (B.zero2 x)) := e₂'
    have ff : B.S2mk (B.nsmul2 u' N) = B.S2mk (B.smul m₂ (B.zero2 x)) := f₂'
    show B.S2mk (B.add2 (B.nsmul2 u N) (B.nsmul2 u' N)) = B.S2mk (B.smul (l₂ * m₂) (B.zero2 x))
    have step : B.S2mk (B.add2 (B.nsmul2 u N) (B.nsmul2 u' N)) = B.S2mk (B.nsmul2 u N) + B.S2mk (B.nsmul2 u' N) := rfl
    have step2 : B.S2mk (B.smul l₂ (B.zero2 x)) + B.S2mk (B.smul m₂ (B.zero2 x)) =
        B.S2mk (B.add2 (B.smul l₂ (B.zero2 x)) (B.smul m₂ (B.zero2 x))) := rfl
    rw [step, ee, ff, step2, B.addSnd_smul]
    exact Sigma.ext (add_zero 0) (hsm _ (add_zero 0) _ _ (B.zeroSnd_add (B.zero2 x)))

/- English proof (translation)
Establish `swap_castFst : ∀ {a b c : B.G R} (e : a = b) (v : B.P R a c), B.sw (B.tr1 e v) = B.tr2 e (B.sw v)`. Introduce `a b c e v`. Substitute `e` using the available equality. Both sides reduce to the same expression. Take `⟨hx, hy, u, l₁, l₂, e₁, e₂, rfl⟩` from `h`.

Use `⟨hy, hx, B.sw u, l₂, l₁, ?_, ?_, inv_div l₁ l₂⟩` and prove the remaining obligations. Rewrite using `[← B.sw_nsmul2, ← B.swap_castSnd, e₂, B.sw_smul, B.sw_zero2]`. Rewrite using `[← B.sw_nsmul1, ← swap_castFst, e₁, B.sw_smul, B.sw_zero1]`.
-/
theorem pairing_sw (N : ℕ) (x y : B.G R) (z : (R : Type u)ˣ) (h : B.IsPairing N x y z) :
    B.IsPairing N y x z⁻¹ := by
  have swap_castFst : ∀ {a b c : B.G R} (e : a = b) (v : B.P R a c), B.sw (B.tr1 e v) = B.tr2 e (B.sw v) := by
    intro a b c e v
    subst e
    rfl
  obtain ⟨hx, hy, u, l₁, l₂, e₁, e₂, rfl⟩ := h
  refine ⟨hy, hx, B.sw u, l₂, l₁, ?_, ?_, inv_div l₁ l₂⟩
  · rw [← B.sw_nsmul2, ← B.swap_castSnd, e₂, B.sw_smul, B.sw_zero2]
  · rw [← B.sw_nsmul1, ← swap_castFst, e₁, B.sw_smul, B.sw_zero1]

/- English proof (translation)
Take `⟨hx, hy, u, l₁, l₂, e₁, e₂, rfl⟩` from `h`. Establish `inj : ∀ {a b : B.G R} (v : B.P R a b) (l l' : (R : Type u)ˣ), B.smul l v = B.smul l' v → l = l'` using `fun v l l' h => (B.trans v (B.smul l v)).unique rfl h.symm`. Establish `hsmH : ∀ (c : (R : Type u)ˣ) {a a' b b' : B.G R} (ea : a = a') (eb : b = b') (v : B.P R a b) (v' : B.P R a' b'), HEq v v' → HEq (B.smul c v) (B.smul c v')`. Introduce `c a a' b b' ea eb v v' hv`. Substitute `ea` using the available equality.

Substitute `eb` using the available equality. Rewrite using `[eq_of_heq hv]`. Establish `htr1 : ∀ {a b b' : B.G R} (e : b = b') (v : B.P R b a), HEq (B.tr1 e v) v`. Introduce `a b b' e v`. Substitute `e` using the available equality.

Both sides reduce to the same expression. Establish `htr2 : ∀ {a b b' : B.G R} (e : b = b') (v : B.P R a b), HEq (B.tr2 e v) v`. Introduce `a b b' e v`. Substitute `e` using the available equality. Both sides reduce to the same expression.

Establish `hz : B.zero1 (0 : B.G R) = B.zero2 0`. Take `⟨c, hc, -⟩` from `B.trans (B.zero2 (0 : B.G R)) (B.zero1 0)`. Establish `h1 : HEq (B.add1 (B.zero1 (0 : B.G R)) (B.zero2 0)) (B.zero2 (0 : B.G R))` using `B.zeroFst_add _`. Establish `h2 : B.add1 (B.zero1 (0 : B.G R)) (B.zero2 0) = B.smul c (B.zero2 (0 + 0 : B.G R))`. Rewrite using `[← hc, show B.add1 (B.smul c (B.zero2 (0 : B.G R))) (B.zero2 0) = B.add1 (B.smul c (B.zero2 (0 : B.G R))) (B.smul 1 (B.zero2 0)) by rw [B.one_smul], B.addFst_smul, mul_one, B.zeroSnd_addFst]`.

Establish `h3 : HEq (B.smul c (B.zero2 (0 + 0 : B.G R))) (B.smul c (B.zero2 (0 : B.G R)))` using `hsmH c (add_zero 0) rfl _ _ (congr_arg_heq B.zero2 (add_zero (0 : B.G R)))`. Establish `h4 : HEq (B.smul c (B.zero2 (0 : B.G R))) (B.zero2 (0 : B.G R))` using `h3.symm.trans (h2 ▸ h1)`. Establish `hc1 : c = 1` using `inj _ _ _ ((eq_of_heq h4).trans (B.one_smul _).symm)`. Rewrite using `[← hc, hc1, B.one_smul]`. Establish `L : HEq (B.nsmul2 (B.nsmul1 u N) N) (B.smul (l₁ ^ N) (B.zero1 (0 : B.G R)))`.

Establish `a1 : HEq (B.nsmul1 u N) (B.smul l₁ (B.zero1 y))` using `(htr1 hx _).symm.trans (heq_of_eq e₁)`. Use `(B.nsmul2_hcongr hx rfl N a1).trans ?_` and prove the remaining obligations. Rewrite using `[B.nsmul2_smul]`. Conclude with `hsmH _ rfl hy _ _ ((B.nsmul2_zero1 y N).trans (congr_arg_heq B.zero1 hy))`. Establish `Rr : HEq (B.nsmul1 (B.nsmul2 u N) N) (B.smul (l₂ ^ N) (B.zero2 (0 : B.G R)))`.

Establish `a2 : HEq (B.nsmul2 u N) (B.smul l₂ (B.zero2 x))` using `(htr2 hy _).symm.trans (heq_of_eq e₂)`. Use `(B.nsmul1_hcongr rfl hy N a2).trans ?_` and prove the remaining obligations. Rewrite using `[B.nsmul1_smul]`. Conclude with `hsmH _ hx rfl _ _ ((B.nsmul1_zero2 x N).trans (congr_arg_heq B.zero2 hx))`. Establish `key` using `eq_of_heq (L.symm.trans ((heq_of_eq (B.nsmul_comm u N N)).trans Rr))`.

Rewrite `key` using `[hz]`. Rewrite using `[div_pow, inj _ _ _ key, div_self']`.
-/
theorem pairing_pow (N : ℕ) (x y : B.G R) (z : (R : Type u)ˣ) (h : B.IsPairing N x y z) :
    z ^ N = 1 := by
  obtain ⟨hx, hy, u, l₁, l₂, e₁, e₂, rfl⟩ := h
  have inj : ∀ {a b : B.G R} (v : B.P R a b) (l l' : (R : Type u)ˣ), B.smul l v = B.smul l' v → l = l' :=
    fun v l l' h => (B.trans v (B.smul l v)).unique rfl h.symm
  have hsmH : ∀ (c : (R : Type u)ˣ) {a a' b b' : B.G R} (ea : a = a') (eb : b = b') (v : B.P R a b)
      (v' : B.P R a' b'), HEq v v' → HEq (B.smul c v) (B.smul c v') := by
    intro c a a' b b' ea eb v v' hv
    subst ea
    subst eb
    rw [eq_of_heq hv]
  have htr1 : ∀ {a b b' : B.G R} (e : b = b') (v : B.P R b a), HEq (B.tr1 e v) v := by
    intro a b b' e v
    subst e
    rfl
  have htr2 : ∀ {a b b' : B.G R} (e : b = b') (v : B.P R a b), HEq (B.tr2 e v) v := by
    intro a b b' e v
    subst e
    rfl

  have hz : B.zero1 (0 : B.G R) = B.zero2 0 := by
    obtain ⟨c, hc, -⟩ := B.trans (B.zero2 (0 : B.G R)) (B.zero1 0)
    have h1 : HEq (B.add1 (B.zero1 (0 : B.G R)) (B.zero2 0)) (B.zero2 (0 : B.G R)) := B.zeroFst_add _
    have h2 : B.add1 (B.zero1 (0 : B.G R)) (B.zero2 0) = B.smul c (B.zero2 (0 + 0 : B.G R)) := by
      rw [← hc, show B.add1 (B.smul c (B.zero2 (0 : B.G R))) (B.zero2 0) =
        B.add1 (B.smul c (B.zero2 (0 : B.G R))) (B.smul 1 (B.zero2 0)) by rw [B.one_smul],
        B.addFst_smul, mul_one, B.zeroSnd_addFst]
    have h3 : HEq (B.smul c (B.zero2 (0 + 0 : B.G R))) (B.smul c (B.zero2 (0 : B.G R))) :=
      hsmH c (add_zero 0) rfl _ _ (congr_arg_heq B.zero2 (add_zero (0 : B.G R)))
    have h4 : HEq (B.smul c (B.zero2 (0 : B.G R))) (B.zero2 (0 : B.G R)) := h3.symm.trans (h2 ▸ h1)
    have hc1 : c = 1 := inj _ _ _ ((eq_of_heq h4).trans (B.one_smul _).symm)
    rw [← hc, hc1, B.one_smul]

  have L : HEq (B.nsmul2 (B.nsmul1 u N) N) (B.smul (l₁ ^ N) (B.zero1 (0 : B.G R))) := by
    have a1 : HEq (B.nsmul1 u N) (B.smul l₁ (B.zero1 y)) := (htr1 hx _).symm.trans (heq_of_eq e₁)
    refine (B.nsmul2_hcongr hx rfl N a1).trans ?_
    rw [B.nsmul2_smul]
    exact hsmH _ rfl hy _ _ ((B.nsmul2_zero1 y N).trans (congr_arg_heq B.zero1 hy))
  have Rr : HEq (B.nsmul1 (B.nsmul2 u N) N) (B.smul (l₂ ^ N) (B.zero2 (0 : B.G R))) := by
    have a2 : HEq (B.nsmul2 u N) (B.smul l₂ (B.zero2 x)) := (htr2 hy _).symm.trans (heq_of_eq e₂)
    refine (B.nsmul1_hcongr rfl hy N a2).trans ?_
    rw [B.nsmul1_smul]
    exact hsmH _ hx rfl _ _ ((B.nsmul1_zero2 x N).trans (congr_arg_heq B.zero2 hx))
  have key := eq_of_heq (L.symm.trans ((heq_of_eq (B.nsmul_comm u N N)).trans Rr))
  rw [hz] at key
  rw [div_pow, inj _ _ _ key, div_self']

/- English proof (translation)
Take `⟨hx, hy, u, l₁, l₂, e₁, e₂, rfl⟩` from `h`. Establish `hx' : N • B.map f x = 0` using `by rw [← map_nsmul, hx, map_zero]`. Establish `hy' : N • B.map f y = 0` using `by rw [← map_nsmul, hy, map_zero]`. Establish `hsm1 : ∀ (c : (S : Type u)ˣ) {a b b' : B.G S} (e : b = b') (v : B.P S b a) (v' : B.P S b' a), HEq v v' → HEq (B.smul c v) (B.smul c v')`. Introduce `c a b b' e v v' hv`.

Substitute `e` using the available equality. Rewrite using `[eq_of_heq hv]`. Establish `hsm2 : ∀ (c : (S : Type u)ˣ) {a b b' : B.G S} (e : b = b') (v : B.P S a b) (v' : B.P S a b'), HEq v v' → HEq (B.smul c v) (B.smul c v')`. Introduce `c a b b' e v v' hv`. Substitute `e` using the available equality.

Rewrite using `[eq_of_heq hv]`. Establish `hpm1 : ∀ {a b b' : B.G R} (e : b = b') (v : B.P R b a) (v' : B.P R b' a), HEq v v' → HEq (B.pmap f v) (B.pmap f v')`. Introduce `a b b' e v v' hv`. Substitute `e` using the available equality. Rewrite using `[eq_of_heq hv]`.

Establish `hpm2 : ∀ {a b b' : B.G R} (e : b = b') (v : B.P R a b) (v' : B.P R a b'), HEq v v' → HEq (B.pmap f v) (B.pmap f v')`. Introduce `a b b' e v v' hv`. Substitute `e` using the available equality. Rewrite using `[eq_of_heq hv]`. Establish `htr1 : ∀ {a b b' : B.G R} (e : b = b') (v : B.P R b a), HEq v (B.tr1 e v)`.

Introduce `a b b' e v`. Substitute `e` using the available equality. Both sides reduce to the same expression. Establish `htr2 : ∀ {a b b' : B.G R} (e : b = b') (v : B.P R a b), HEq v (B.tr2 e v)`. Introduce `a b b' e v`.

Substitute `e` using the available equality. Both sides reduce to the same expression. Use `⟨hx', hy', B.pmap f u, Units.map _ l₁, Units.map _ l₂, ?_, ?_, map_div _ _ _⟩` and prove the remaining obligations. Rewrite using `[B.castFst_eq_iff]`. Use `Sigma.ext hx' ?_` and prove the remaining obligations.

Use `(B.pmap_nsmul1 f u N).symm.trans ?_` and prove the remaining obligations. Use `(hpm1 hx _ _ (htr1 hx _)).trans ?_` and prove the remaining obligations. Rewrite using `[e₁, B.pmap_smul]`. Conclude with `hsm1 _ (map_zero _) _ _ (B.zeroFst_nat f y)`. Rewrite using `[B.castSnd_eq_iff]`.

Use `Sigma.ext hy' ?_` and prove the remaining obligations. Use `(B.pmap_nsmul2 f u N).symm.trans ?_` and prove the remaining obligations. Use `(hpm2 hy _ _ (htr2 hy _)).trans ?_` and prove the remaining obligations. Rewrite using `[e₂, B.pmap_smul]`. Conclude with `hsm2 _ (map_zero _) _ _ (B.zeroSnd_nat f x)`.
-/
theorem pairing_map {S : LAlg R₀} (f : LHom R S) (N : ℕ) (x y : B.G R) (z : (R : Type u)ˣ)
    (h : B.IsPairing N x y z) :
    B.IsPairing N (B.map f x) (B.map f y) (Units.map (f.1 : R →* S) z) := by
  obtain ⟨hx, hy, u, l₁, l₂, e₁, e₂, rfl⟩ := h
  have hx' : N • B.map f x = 0 := by rw [← map_nsmul, hx, map_zero]
  have hy' : N • B.map f y = 0 := by rw [← map_nsmul, hy, map_zero]

  have hsm1 : ∀ (c : (S : Type u)ˣ) {a b b' : B.G S} (e : b = b') (v : B.P S b a) (v' : B.P S b' a), HEq v v' →
      HEq (B.smul c v) (B.smul c v') := by
    intro c a b b' e v v' hv
    subst e
    rw [eq_of_heq hv]
  have hsm2 : ∀ (c : (S : Type u)ˣ) {a b b' : B.G S} (e : b = b') (v : B.P S a b) (v' : B.P S a b'), HEq v v' →
      HEq (B.smul c v) (B.smul c v') := by
    intro c a b b' e v v' hv
    subst e
    rw [eq_of_heq hv]
  have hpm1 : ∀ {a b b' : B.G R} (e : b = b') (v : B.P R b a) (v' : B.P R b' a), HEq v v' →
      HEq (B.pmap f v) (B.pmap f v') := by
    intro a b b' e v v' hv
    subst e
    rw [eq_of_heq hv]
  have hpm2 : ∀ {a b b' : B.G R} (e : b = b') (v : B.P R a b) (v' : B.P R a b'), HEq v v' →
      HEq (B.pmap f v) (B.pmap f v') := by
    intro a b b' e v v' hv
    subst e
    rw [eq_of_heq hv]
  have htr1 : ∀ {a b b' : B.G R} (e : b = b') (v : B.P R b a), HEq v (B.tr1 e v) := by
    intro a b b' e v
    subst e
    rfl
  have htr2 : ∀ {a b b' : B.G R} (e : b = b') (v : B.P R a b), HEq v (B.tr2 e v) := by
    intro a b b' e v
    subst e
    rfl
  refine ⟨hx', hy', B.pmap f u, Units.map _ l₁, Units.map _ l₂, ?_, ?_, map_div _ _ _⟩
  · rw [B.castFst_eq_iff]
    refine Sigma.ext hx' ?_
    refine (B.pmap_nsmul1 f u N).symm.trans ?_
    refine (hpm1 hx _ _ (htr1 hx _)).trans ?_
    rw [e₁, B.pmap_smul]
    exact hsm1 _ (map_zero _) _ _ (B.zeroFst_nat f y)
  · rw [B.castSnd_eq_iff]
    refine Sigma.ext hy' ?_
    refine (B.pmap_nsmul2 f u N).symm.trans ?_
    refine (hpm2 hy _ _ (htr2 hy _)).trans ?_
    rw [e₂, B.pmap_smul]
    exact hsm2 _ (map_zero _) _ _ (B.zeroSnd_nat f x)

/- English proof (translation)
Take `⟨hx', hy', u, l₁, l₂, e₁, e₂, rfl⟩` from `h`. Establish `inj : ∀ {a b : B.G R} (v : B.P R a b) (l l' : (R : Type u)ˣ), B.smul l v = B.smul l' v → l = l'` using `fun v l l' h => (B.trans v (B.smul l v)).unique rfl h.symm`. Establish `hsmH : ∀ (c : (R : Type u)ˣ) {a a' b b' : B.G R} (ea : a = a') (eb : b = b') (v : B.P R a b) (v' : B.P R a' b'), HEq v v' → HEq (B.smul c v) (B.smul c v')`. Introduce `c a a' b b' ea eb v v' hv`. Substitute `ea` using the available equality.

Substitute `eb` using the available equality. Rewrite using `[eq_of_heq hv]`. Establish `htr1 : ∀ {a b b' : B.G R} (e : b = b') (v : B.P R b a), HEq (B.tr1 e v) v`. Introduce `a b b' e v`. Substitute `e` using the available equality.

Both sides reduce to the same expression. Establish `htr2 : ∀ {a b b' : B.G R} (e : b = b') (v : B.P R a b), HEq (B.tr2 e v) v`. Introduce `a b b' e v`. Substitute `e` using the available equality. Both sides reduce to the same expression.

Establish `hpy : N • (p • y) = 0` using `by rw [smul_smul, hy]`. Take `⟨c, hc, -⟩` from `B.trans (B.zero1 y) (B.tr1 hx (B.nsmul1 u N))`. Establish `hS1 : (⟨(N * p) • x, B.nsmul1 u (N * p)⟩ : B.S1 R y) = ⟨p • (N • x), B.nsmul1 (B.nsmul1 u N) p⟩`. Rewrite using `[← B.fibreFst_nsmul_mk, ← B.fibreFst_nsmul_mk, show B.S1mk (B.nsmul1 u N) = N • B.S1mk u from (B.fibreFst_nsmul_mk u N).symm, smul_smul, mul_comm]`. Establish `hH1 : HEq (B.nsmul1 u (N * p)) (B.nsmul1 (B.nsmul1 u N) p)` using `(Sigma.mk.inj hS1).2`.

Establish `chain : HEq (B.smul l₁ (B.zero1 y)) (B.smul (c ^ p) (B.zero1 y))`. Use `(heq_of_eq e₁).symm.trans ((htr1 hx' _).trans (hH1.trans ?_))` and prove the remaining obligations. Use `(B.nsmul1_hcongr hx rfl p ((htr1 hx _).symm.trans (heq_of_eq hc.symm))).trans ?_` and prove the remaining obligations. Rewrite using `[B.nsmul1_smul]`. Conclude with `hsmH _ (smul_zero p) rfl _ _ (B.nsmul1_zero1 y p)`.

Establish `hl : l₁ = c ^ p` using `inj _ _ _ (eq_of_heq chain)`. Establish `hS2 : (⟨N • (p • y), B.nsmul2 (B.nsmul2 u p) N⟩ : B.S2 R x) = ⟨(N * p) • y, B.nsmul2 u (N * p)⟩`. Rewrite using `[← B.fibreSnd_nsmul_mk, ← B.fibreSnd_nsmul_mk, show B.S2mk (B.nsmul2 u p) = p • B.S2mk u from (B.fibreSnd_nsmul_mk u p).symm, smul_smul]`. Establish `hH2 : HEq (B.nsmul2 (B.nsmul2 u p) N) (B.nsmul2 u (N * p))` using `(Sigma.mk.inj hS2).2`. Use `⟨hx, hpy, B.nsmul2 u p, c ^ p, l₂, ?_, ?_, by rw [hl]⟩` and prove the remaining obligations.

Rewrite using `[← B.nsmul_comm]`. Use `eq_of_heq ((htr1 hx _).trans ?_)` and prove the remaining obligations. Use `(B.nsmul2_hcongr hx rfl p ((htr1 hx _).symm.trans (heq_of_eq hc.symm))).trans ?_` and prove the remaining obligations. Rewrite using `[B.nsmul2_smul]`. Conclude with `hsmH _ rfl rfl _ _ (B.nsmul2_zero1 y p)`.

Conclude with `eq_of_heq ((htr2 hpy _).trans (hH2.trans ((htr2 hy' _).symm.trans (heq_of_eq e₂))))`.
-/
theorem pairing_mul (N p : ℕ) (x y : B.G R) (z : (R : Type u)ˣ) (hx : N • x = 0)
    (hy : (N * p) • y = 0) (h : B.IsPairing (N * p) x y z) : B.IsPairing N x (p • y) z := by
  obtain ⟨hx', hy', u, l₁, l₂, e₁, e₂, rfl⟩ := h
  have inj : ∀ {a b : B.G R} (v : B.P R a b) (l l' : (R : Type u)ˣ), B.smul l v = B.smul l' v → l = l' :=
    fun v l l' h => (B.trans v (B.smul l v)).unique rfl h.symm
  have hsmH : ∀ (c : (R : Type u)ˣ) {a a' b b' : B.G R} (ea : a = a') (eb : b = b') (v : B.P R a b)
      (v' : B.P R a' b'), HEq v v' → HEq (B.smul c v) (B.smul c v') := by
    intro c a a' b b' ea eb v v' hv
    subst ea
    subst eb
    rw [eq_of_heq hv]
  have htr1 : ∀ {a b b' : B.G R} (e : b = b') (v : B.P R b a), HEq (B.tr1 e v) v := by
    intro a b b' e v
    subst e
    rfl
  have htr2 : ∀ {a b b' : B.G R} (e : b = b') (v : B.P R a b), HEq (B.tr2 e v) v := by
    intro a b b' e v
    subst e
    rfl
  have hpy : N • (p • y) = 0 := by rw [smul_smul, hy]
  obtain ⟨c, hc, -⟩ := B.trans (B.zero1 y) (B.tr1 hx (B.nsmul1 u N))

  have hS1 : (⟨(N * p) • x, B.nsmul1 u (N * p)⟩ : B.S1 R y) = ⟨p • (N • x), B.nsmul1 (B.nsmul1 u N) p⟩ := by
    rw [← B.fibreFst_nsmul_mk, ← B.fibreFst_nsmul_mk,
      show B.S1mk (B.nsmul1 u N) = N • B.S1mk u from (B.fibreFst_nsmul_mk u N).symm, smul_smul, mul_comm]
  have hH1 : HEq (B.nsmul1 u (N * p)) (B.nsmul1 (B.nsmul1 u N) p) := (Sigma.mk.inj hS1).2
  have chain : HEq (B.smul l₁ (B.zero1 y)) (B.smul (c ^ p) (B.zero1 y)) := by
    refine (heq_of_eq e₁).symm.trans ((htr1 hx' _).trans (hH1.trans ?_))
    refine (B.nsmul1_hcongr hx rfl p ((htr1 hx _).symm.trans (heq_of_eq hc.symm))).trans ?_
    rw [B.nsmul1_smul]
    exact hsmH _ (smul_zero p) rfl _ _ (B.nsmul1_zero1 y p)
  have hl : l₁ = c ^ p := inj _ _ _ (eq_of_heq chain)

  have hS2 : (⟨N • (p • y), B.nsmul2 (B.nsmul2 u p) N⟩ : B.S2 R x) = ⟨(N * p) • y, B.nsmul2 u (N * p)⟩ := by
    rw [← B.fibreSnd_nsmul_mk, ← B.fibreSnd_nsmul_mk,
      show B.S2mk (B.nsmul2 u p) = p • B.S2mk u from (B.fibreSnd_nsmul_mk u p).symm, smul_smul]
  have hH2 : HEq (B.nsmul2 (B.nsmul2 u p) N) (B.nsmul2 u (N * p)) := (Sigma.mk.inj hS2).2
  refine ⟨hx, hpy, B.nsmul2 u p, c ^ p, l₂, ?_, ?_, by rw [hl]⟩
  · rw [← B.nsmul_comm]
    refine eq_of_heq ((htr1 hx _).trans ?_)
    refine (B.nsmul2_hcongr hx rfl p ((htr1 hx _).symm.trans (heq_of_eq hc.symm))).trans ?_
    rw [B.nsmul2_smul]
    exact hsmH _ rfl rfl _ _ (B.nsmul2_zero1 y p)
  · exact eq_of_heq ((htr2 hpy _).trans (hH2.trans ((htr2 hy' _).symm.trans (heq_of_eq e₂))))

end BX

/- English proof (translation)
Use `⟨fun R N x y hx hy => B.pairing_exists N x y hx hy, fun R N x y z z' h h' => B.pairing_unique N x y z z' h h', fun R N x x' y z z' w h h' hw => B.pairing_unique N _ _ _ _ hw (B.isPairingValue_add_left N x x' y z z' h h'), fun R N x y y' z z' w h h' hw => B.pairing_unique N _ _ _ …` and prove the remaining obligations. Rewrite using `[← B.pairing_unique N y x _ _ (B.pairing_sw N x y z h) h', mul_inv_cancel]`.
-/
theorem pairingProperties (B : BX R₀) : PairingPropertiesStatement B := by
  refine ⟨fun R N x y hx hy => B.pairing_exists N x y hx hy,
    fun R N x y z z' h h' => B.pairing_unique N x y z z' h h',
    fun R N x x' y z z' w h h' hw => B.pairing_unique N _ _ _ _ hw (B.isPairingValue_add_left N x x' y z z' h h'),
    fun R N x y y' z z' w h h' hw => B.pairing_unique N _ _ _ _ hw (B.isPairingValue_add_right N x y y' z z' h h'),
    fun R N x y z z' h h' => ?_, fun R N x y z h => B.pairing_pow N x y z h,
    fun R S f N x y z h => B.pairing_map f N x y z h,
    fun R N p x y z hx hy h => B.pairing_mul N p x y z hx hy h⟩
  rw [← B.pairing_unique N y x _ _ (B.pairing_sw N x y z h) h', mul_inv_cancel]

end ReciprocityTheory.PGsh
