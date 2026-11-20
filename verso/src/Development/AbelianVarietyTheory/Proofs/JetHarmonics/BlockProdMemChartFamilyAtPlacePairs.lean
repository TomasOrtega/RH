import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.IsSelfOf
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GapParts
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ProdDetMemHaO
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FlagOfLetterNumberingRowData

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MemPair

section Blocks

open scoped BigOperators
open Classical Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj GlobalTheory.RowAt

/- English proof (translation)
Rewrite using `[Finset.prod_eq_single g, Finset.prod_eq_single a, Finset.prod_eq_single n]`. Simplify using the standard rewrite rules. Introduce `k _ hk`. Simplify using `[hk]`. Introduce `hn`.

Establish `: e = 0`. Assume the negation of the conclusion as `he`. Conclude with `hn (Finset.mem_range.2 (Nat.lt_succ_of_le (h he)))`. Simplify using `[this]`. Introduce `a' _ ha`.

Simplify using `[ha]`. Simplify using the standard rewrite rules. Introduce `g' _ hg`. Simplify using `[hg]`. Simplify using the standard rewrite rules.
-/
theorem prod_pow_single {R : Type} [CommMonoid R] {d : ℕ} [NeZero d] (f : Fin 2 → ZMod d → ℕ → R)
    (M : Fin 2 → ZMod d → ℕ) (g : Fin 2) (a : ZMod d) (n e : ℕ) (h : e ≠ 0 → n ≤ M g a) :
    ∏ g', ∏ a', ∏ k ∈ Finset.range (M g' a' + 1), f g' a' k ^ (if g' = g ∧ a' = a ∧ k = n then e else 0)
      = f g a n ^ e := by
  rw [Finset.prod_eq_single g, Finset.prod_eq_single a, Finset.prod_eq_single n]
  · simp
  · intro k _ hk
    simp [hk]
  · intro hn
    have : e = 0 := by
      by_contra he
      exact hn (Finset.mem_range.2 (Nat.lt_succ_of_le (h he)))
    simp [this]
  · intro a' _ ha
    simp [ha]
  · simp
  · intro g' _ hg
    simp [hg]
  · simp

variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type}
  [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J) (F : RF.Flag X)

/- English proof (translation)
Consider the cases of `b with`. Consider the case `bi g a i y`. Simplify using `only [RF.GlobalTheory.wt, pow_add, Finset.prod_mul_distrib]`. Rewrite using `[prod_pow_single (fun g' a' k => MvPolynomial.rename (F.letter g' a') (minorK C ((RF.GlobalTheory.bi g a i y).what₂ X.n) (X.rkF g' a') k)) M g a X.n, prod_pow_single (fun g' a' k => MvPolynomial.rename (F.letter g' a') (minorK C ((RF.GlobalTheory.bi g a i y).what₂ X.n) (X.rkF g' …`. Both sides reduce to the same expression.

Introduce `he`. Use `h _ _ _ ?_` and prove the remaining obligations. Simplify using `[RF.GlobalTheory.wt, he]`. Introduce `he`. Use `h _ _ _ ?_` and prove the remaining obligations.

Simplify using `only [RF.GlobalTheory.wt, and_self, if_true]`. Use linear arithmetic over natural numbers and integers. Consider the case `ch g a u`. Simplify using `only [RF.GlobalTheory.wt]`. Rewrite using `[prod_pow_single (fun g' a' k => MvPolynomial.rename (F.letter g' a') (minorK C ((RF.GlobalTheory.ch g a u).what₂ X.n) (X.rkF g' a') k)) M g a X.n]`.

Both sides reduce to the same expression. Introduce `he`. Use `h _ _ _ ?_` and prove the remaining obligations. Simplify using `[RF.GlobalTheory.wt, he]`. Consider the case `mon g e N`.

Rewrite using `[Finset.prod_eq_single g]`. Use `show (∏ a : ZMod d, MvPolynomial.rename (F.letter g a) (monP C N (X.rkF g a) (e a))) = ∏ a : ZMod d, ∏ k ∈ Finset.range (M g a + 1), MvPolynomial.rename (F.letter g a) (minorK C N (X.rkF g a) k) ^ (RF.GlobalTheory.mon g e N).wt X g a k`. Use `Finset.prod_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[monP, map_prod]`. Establish `h1 : ∀ k ∈ Finset.Icc 1 (min N (X.rkF g a)), (RF.GlobalTheory.mon g e N).wt X g a k = e a k`.

Introduce `k hk`. Rewrite `hk` using `[Finset.mem_Icc]`. Simplify using `only [RF.GlobalTheory.wt]`. Rewrite using `[if_pos ⟨trivial, hk⟩]`. Use `Finset.prod_congr_of_eq_on_inter ?_ ?_ ?_` and prove the remaining obligations.

Introduce `k hk hk'`. Establish `: e a k = 0`. Assume the negation of the conclusion as `he`. Conclude with `hk' (Finset.mem_range.2 (Nat.lt_succ_of_le (h g a k (by rwa [h1 k hk]))))`. Rewrite using `[this, pow_zero, map_one]`.

Introduce `k _ hk`. Rewrite `hk` using `[Finset.mem_Icc]`. Simplify using `only [RF.GlobalTheory.wt]`. Rewrite using `[if_neg (fun h => hk h.2), pow_zero]`. Introduce `k hk _`.

Rewrite using `[h1 k hk, map_pow]`. Introduce `g' _ hg`. Simplify using `[RF.GlobalTheory.wt, hg]`. Simplify using the standard rewrite rules.
-/
theorem poly_eq (b : RF.GlobalTheory d) (M : Fin 2 → ZMod d → ℕ) (h : ∀ g a k, b.wt X g a k ≠ 0 → k ≤ M g a) :
    b.poly X F = ∏ g, ∏ a, ∏ k ∈ Finset.range (M g a + 1),
      MvPolynomial.rename (F.letter g a) (minorK C (b.what₂ X.n) (X.rkF g a) k) ^ b.wt X g a k := by
  cases b with
  | bi g a i y =>
    simp only [RF.GlobalTheory.wt, pow_add, Finset.prod_mul_distrib]
    rw [prod_pow_single (fun g' a' k => MvPolynomial.rename (F.letter g' a')
        (minorK C ((RF.GlobalTheory.bi g a i y).what₂ X.n) (X.rkF g' a') k)) M g a X.n,
      prod_pow_single (fun g' a' k => MvPolynomial.rename (F.letter g' a')
        (minorK C ((RF.GlobalTheory.bi g a i y).what₂ X.n) (X.rkF g' a') k)) M (1 - g) (a + (i : ZMod d)) X.n]
    · rfl
    · intro he
      refine h _ _ _ ?_
      simp [RF.GlobalTheory.wt, he]
    · intro he
      refine h _ _ _ ?_
      simp only [RF.GlobalTheory.wt, and_self, if_true]
      omega
  | ch g a u =>
    simp only [RF.GlobalTheory.wt]
    rw [prod_pow_single (fun g' a' k => MvPolynomial.rename (F.letter g' a')
        (minorK C ((RF.GlobalTheory.ch g a u).what₂ X.n) (X.rkF g' a') k)) M g a X.n]
    · rfl
    · intro he
      refine h _ _ _ ?_
      simp [RF.GlobalTheory.wt, he]
  | mon g e N =>
    rw [Finset.prod_eq_single g]
    · show (∏ a : ZMod d, MvPolynomial.rename (F.letter g a) (monP C N (X.rkF g a) (e a))) =
        ∏ a : ZMod d, ∏ k ∈ Finset.range (M g a + 1),
          MvPolynomial.rename (F.letter g a) (minorK C N (X.rkF g a) k) ^ (RF.GlobalTheory.mon g e N).wt X g a k
      refine Finset.prod_congr rfl fun a _ => ?_
      rw [monP, map_prod]
      have h1 : ∀ k ∈ Finset.Icc 1 (min N (X.rkF g a)), (RF.GlobalTheory.mon g e N).wt X g a k = e a k := by
        intro k hk
        rw [Finset.mem_Icc] at hk
        simp only [RF.GlobalTheory.wt]
        rw [if_pos ⟨trivial, hk⟩]
      refine Finset.prod_congr_of_eq_on_inter ?_ ?_ ?_
      · intro k hk hk'
        have : e a k = 0 := by
          by_contra he
          exact hk' (Finset.mem_range.2 (Nat.lt_succ_of_le (h g a k (by rwa [h1 k hk]))))
        rw [this, pow_zero, map_one]
      · intro k _ hk
        rw [Finset.mem_Icc] at hk
        simp only [RF.GlobalTheory.wt]
        rw [if_neg (fun h => hk h.2), pow_zero]
      · intro k hk _
        rw [h1 k hk, map_pow]
    · intro g' _ hg
      simp [RF.GlobalTheory.wt, hg]
    · simp

/- English proof (translation)
Consider the cases of `b with`. Consider the case `bi g' a' i y`. Simplify using `only [RF.GlobalTheory.wt] at h`. Assume the negation of the conclusion as `hk`. Establish `: k ≠ X.n` using `fun e => hk (le_of_eq e)`.

Simplify using `[this] at h`. Consider the case `ch g' a' u`. Simplify using `only [RF.GlobalTheory.wt] at h`. Assume the negation of the conclusion as `hk`. Establish `: k ≠ X.n` using `fun e => hk (le_of_eq e)`.

Simplify using `[this] at h`. Consider the case `mon g' e N`. Simplify using `only [RF.GlobalTheory.wt] at h`. Assume the negation of the conclusion as `hk`. Rewrite `h` using `[if_neg]`.

Conclude with `h rfl`. Introduce and unpack `⟨-, -, h3⟩`. Conclude with `hk (h3.trans (min_le_left _ _))`.
-/
theorem le_rows (b : RF.GlobalTheory d) (g : Fin 2) (a : ZMod d) (k : ℕ) (h : b.wt X g a k ≠ 0) : k ≤ b.what₂ X.n := by
  cases b with
  | bi g' a' i y =>
    simp only [RF.GlobalTheory.wt] at h
    by_contra hk
    have : k ≠ X.n := fun e => hk (le_of_eq e)
    simp [this] at h
  | ch g' a' u =>
    simp only [RF.GlobalTheory.wt] at h
    by_contra hk
    have : k ≠ X.n := fun e => hk (le_of_eq e)
    simp [this] at h
  | mon g' e N =>
    simp only [RF.GlobalTheory.wt] at h
    by_contra hk
    rw [if_neg] at h
    · exact h rfl
    · rintro ⟨-, -, h3⟩
      exact hk (h3.trans (min_le_left _ _))

/- English proof (translation)
Establish `hg : ∀ g : Fin 2, 1 - g ≠ g` using `by decide`. Consider the cases of `b with`. Consider the case `bi g' a'' i y`. Simplify using `only [RF.GlobalTheory.wt] at h h'`. Prove the components needed by the constructor for the conclusion.

Assume the negation of the conclusion as `hk`. Simplify using `[hk] at h`. Assume the negation of the conclusion as `hk`. Simplify using `[hk] at h'`. Consider the case `ch g' a'' u`.

Simplify using `only [RF.GlobalTheory.wt] at h h'`. Prove the components needed by the constructor for the conclusion. Assume the negation of the conclusion as `hk`. Simplify using `[hk] at h`. Assume the negation of the conclusion as `hk`.

Simplify using `[hk] at h'`. Consider the case `mon g' e N`. Simplify using `only [RF.GlobalTheory.wt] at h h'`. Establish `h1 : g = g'`. Assume the negation of the conclusion as `hk`.

Simplify using `[hk] at h`. Establish `h2 : 1 - g = g'`. Assume the negation of the conclusion as `hk`. Simplify using `[hk] at h'`. Conclude with `absurd (h2.trans h1.symm) (hg g)`.
-/
theorem both_groups (b : RF.GlobalTheory d) (g : Fin 2) (a a' : ZMod d) (k k' : ℕ) (h : b.wt X g a k ≠ 0)
    (h' : b.wt X (1 - g) a' k' ≠ 0) : k = X.n ∧ k' = X.n := by
  have hg : ∀ g : Fin 2, 1 - g ≠ g := by decide
  cases b with
  | bi g' a'' i y =>
    simp only [RF.GlobalTheory.wt] at h h'
    constructor
    · by_contra hk
      simp [hk] at h
    · by_contra hk
      simp [hk] at h'
  | ch g' a'' u =>
    simp only [RF.GlobalTheory.wt] at h h'
    constructor
    · by_contra hk
      simp [hk] at h
    · by_contra hk
      simp [hk] at h'
  | mon g' e N =>
    simp only [RF.GlobalTheory.wt] at h h'
    have h1 : g = g' := by
      by_contra hk
      simp [hk] at h
    have h2 : 1 - g = g' := by
      by_contra hk
      simp [hk] at h'
    exact absurd (h2.trans h1.symm) (hg g)

end Blocks

section Letters

open scoped BigOperators
open Classical Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj GlobalTheory.RowAt

variable {Ty : Type} (r : Ty → ℕ) {Orb : Type} {d : ℕ} (tau : Orb → Fin 2 → ZMod d → Ty)

abbrev Ix (o : Orb) (g : Fin 2) : Type := Σ a : ZMod d, Fin (r (tau o g a))

def toRow (w : WVO (Ix r tau)) : Σ τ : Ty, Fin (r τ) := ⟨tau w.1 w.2.1 w.2.2.1, w.2.2.2⟩

def toLet {n : ℕ} (x : Fin n × WVO (Ix r tau)) : Formalism.L2.Pj.Letter Ty r n :=
  ⟨tau x.2.1 x.2.2.1 x.2.2.2.1, x.2.2.2.2, x.1⟩

/- English proof (translation)
Introduce and unpack `⟨o, g, a, i⟩ ⟨o', g', a', i'⟩ h`. Establish `h1 : ((o, g, a) : Orb × Fin 2 × ZMod d) = (o', g', a')` using `inj (congrArg Sigma.fst h)`. Simplify using `only [Prod.mk.injEq] at h1`. Take `⟨rfl, rfl, rfl⟩` from `h1`. Establish `h2 : i = i'` using `eq_of_heq (Sigma.mk.inj h).2`.

Rewrite using `[h2]`.
-/
theorem toRow_inj (inj : Function.Injective fun x : Orb × Fin 2 × ZMod d => tau x.1 x.2.1 x.2.2) :
    Function.Injective (toRow r tau) := by
  rintro ⟨o, g, a, i⟩ ⟨o', g', a', i'⟩ h
  have h1 : ((o, g, a) : Orb × Fin 2 × ZMod d) = (o', g', a') := inj (congrArg Sigma.fst h)
  simp only [Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl, rfl⟩ := h1
  have h2 : i = i' := eq_of_heq (Sigma.mk.inj h).2
  rw [h2]

/- English proof (translation)
Take `⟨s, i⟩` from `x`. Substitute `h1` using the available equality. Conclude with `congrArg _ (Fin.ext h2)`.
-/
theorem sigma_eq {A : Type} {m : A → ℕ} (x : Σ s, Fin (m s)) (a : A) (c : Fin (m a)) (h1 : x.1 = a)
    (h2 : (x.2 : ℕ) = c) : x = ⟨a, c⟩ := by
  obtain ⟨s, i⟩ := x
  subst h1
  exact congrArg _ (Fin.ext h2)

variable {C : Type} [Field C] {V : VF C} [NeZero d] [Fintype Orb]

/- English proof (translation)
Establish `hi` using `toRow_inj r tau inj`. Establish `hx : ∀ x : Fin n × WVO (Ix r tau), (⟨(toLet r tau x).1, (toLet r tau x).2.1⟩ : Σ τ : Ty, Fin (r τ)) = toRow r tau x.2` using `fun _ => rfl`. Use `⟨fun ℓ w => if toRow r tau w = ⟨ℓ.1, ℓ.2.1⟩ then 1 else 0, ?_, ?_⟩` and prove the remaining obligations. Introduce `ℓ hℓ`. Take `⟨x, -, rfl⟩` from `Finset.mem_image.1 (MvPolynomial.vars_rename _ _ hℓ)`.

Use `beta_reduce`. Rewrite using `[hx, Finset.sum_eq_single x.2]`. Rewrite using `[hU, if_pos rfl, one_smul]`. Introduce `w _ hw`. Rewrite using `[if_neg (fun h => hw (hi h)), zero_smul]`.

Simplify using the standard rewrite rules. Rewrite using `[MvPolynomial.aeval_rename]`. Establish `: ((fun ℓ : Formalism.L2.Pj.Letter Ty r n => ∑ w : WVO (Ix r tau), MvPolynomial.C (if toRow r tau w = ⟨ℓ.1, ℓ.2.1⟩ then (1 : C) else 0) * MvPolynomial.X (ℓ.2.2, w)) ∘ toLet r tau) = (MvPolynomial.X : _ → MvPolynomial (Fin n × WVO (Ix r tau)) C)`. Use function extensionality and compare the values at `x`. Simplify using `only [Function.comp]`.

Rewrite using `[hx, Finset.sum_eq_single x.2]`. Rewrite using `[if_pos rfl, map_one, one_mul]`. Both sides reduce to the same expression. Introduce `w _ hw`. Rewrite using `[if_neg (fun h => hw (hi h)), map_zero, zero_mul]`.

Simplify using the standard rewrite rules. Rewrite using `[this, MvPolynomial.aeval_X_left_apply]`.
-/
theorem isImgO {dd n : ℕ} (inj : Function.Injective fun x : Orb × Fin 2 × ZMod d => tau x.1 x.2.1 x.2.2)
    (X : ∀ o, RawChart C d (Ix r tau o) (Fin dd)) (U : (Σ τ : Ty, Fin (r τ)) → Fin dd → C)
    (hU : ∀ w : WVO (Ix r tau), (X w.1).u w.2.1 w.2.2 = U (toRow r tau w))
    (Q : MvPolynomial (Fin n × WVO (Ix r tau)) C) :
    IsImgO X (fun ℓ : Formalism.L2.Pj.Letter Ty r n => ℓ.2.2) (fun ℓ => U ⟨ℓ.1, ℓ.2.1⟩)
      (MvPolynomial.rename (toLet r tau) Q) Q := by
  have hi := toRow_inj r tau inj
  have hx : ∀ x : Fin n × WVO (Ix r tau),
      (⟨(toLet r tau x).1, (toLet r tau x).2.1⟩ : Σ τ : Ty, Fin (r τ)) = toRow r tau x.2 := fun _ => rfl
  refine ⟨fun ℓ w => if toRow r tau w = ⟨ℓ.1, ℓ.2.1⟩ then 1 else 0, ?_, ?_⟩
  · intro ℓ hℓ
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 (MvPolynomial.vars_rename _ _ hℓ)
    beta_reduce
    rw [hx, Finset.sum_eq_single x.2]
    · rw [hU, if_pos rfl, one_smul]
    · intro w _ hw
      rw [if_neg (fun h => hw (hi h)), zero_smul]
    · simp
  · rw [MvPolynomial.aeval_rename]
    have : ((fun ℓ : Formalism.L2.Pj.Letter Ty r n => ∑ w : WVO (Ix r tau),
        MvPolynomial.C (if toRow r tau w = ⟨ℓ.1, ℓ.2.1⟩ then (1 : C) else 0) * MvPolynomial.X (ℓ.2.2, w)) ∘
          toLet r tau) = (MvPolynomial.X : _ → MvPolynomial (Fin n × WVO (Ix r tau)) C) := by
      funext x
      simp only [Function.comp]
      rw [hx, Finset.sum_eq_single x.2]
      · rw [if_pos rfl, map_one, one_mul]
        rfl
      · intro w _ hw
        rw [if_neg (fun h => hw (hi h)), map_zero, zero_mul]
      · simp
    rw [this, MvPolynomial.aeval_X_left_apply]

def ind (C : Type) [Field C] {N n : ℕ} (col : Fin N → Fin n) (k : ℕ) (ρ : Fin k) (b : Fin n) : C :=
  if h : ρ.val < N then (if b = col ⟨ρ.val, h⟩ then 1 else 0) else 0

/- English proof (translation)
Rewrite using `[minorK, dif_pos ⟨hN, hr⟩, toAll, MvPolynomial.rename_rename, MvPolynomial.rename_rename, MvPolynomial.rename_rename, AlgHom.map_det]`. Use `congr 1`. Use extensionality with `ρ i : 2`. Simplify using `only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, MvPolynomial.rename_X, GlobalTheory.CombMinor.cMat]`. Establish `hρ : ρ.val < N` using `lt_of_lt_of_le ρ.2 hN`.

Rewrite using `[Finset.sum_eq_single (col ⟨ρ.val, hρ⟩)]`. Rewrite using `[ind, dif_pos hρ, if_pos rfl, map_one, one_mul]`. Use `congr 1`. Simplify using `only [Function.comp, RF.Flag.letter]`. Rewrite using `[sigma_eq _ a (Fin.castLE hk i) (h1 g a (Fin.castLE hr i)) (h2 g a (Fin.castLE hr i))]`.

Both sides reduce to the same expression. Introduce `b _ hb`. Rewrite using `[ind, dif_pos hρ, if_neg hb, map_zero, zero_mul]`. Simplify using the standard rewrite rules.
-/
theorem rename_minor {J : Fin 2 → Type} [∀ g, Fintype (J g)] (o : Orb) (X : RowData C V d (Ix r tau o) J)
    (F : RF.Flag X) (h1 : ∀ g a c, (F.en g a c).1 = a) (h2 : ∀ g a c, ((F.en g a c).2 : ℕ) = c)
    {N n : ℕ} (col : Fin N → Fin n) (g : Fin 2) (a : ZMod d) (k : ℕ) (hk : k ≤ r (tau o g a)) (hN : k ≤ N)
    (hr : k ≤ X.rkF g a) :
    MvPolynomial.rename (toLet r tau) (toAll o (MvPolynomial.rename
      (fun x : Fin N × WV (Ix r tau o) => (col x.1, x.2))
        (MvPolynomial.rename (F.letter g a) (minorK C N (X.rkF g a) k)))) =
      (GlobalTheory.CombMinor.cMat (tau o g a) k hk (ind C col k)).det := by
  rw [minorK, dif_pos ⟨hN, hr⟩, toAll, MvPolynomial.rename_rename, MvPolynomial.rename_rename,
    MvPolynomial.rename_rename, AlgHom.map_det]
  congr 1
  ext ρ i : 2
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, MvPolynomial.rename_X,
    GlobalTheory.CombMinor.cMat]
  have hρ : ρ.val < N := lt_of_lt_of_le ρ.2 hN
  rw [Finset.sum_eq_single (col ⟨ρ.val, hρ⟩)]
  · rw [ind, dif_pos hρ, if_pos rfl, map_one, one_mul]
    congr 1
    simp only [Function.comp, RF.Flag.letter]
    rw [sigma_eq _ a (Fin.castLE hk i) (h1 g a (Fin.castLE hr i)) (h2 g a (Fin.castLE hr i))]
    rfl
  · intro b _ hb
    rw [ind, dif_pos hρ, if_neg hb, map_zero, zero_mul]
  · simp

/- English proof (translation)
Rewrite using `[Fin.sum_univ_eq_sum_range (fun k => if i < k then f k else 0) (m + 1), ← Finset.sum_filter]`. Use `Finset.sum_congr ?_ fun _ _ => rfl` and prove the remaining obligations. Use extensionality with `k`. Simplify using `only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]`. Use linear arithmetic over natural numbers and integers.
-/
theorem sum_fin_gap (m i : ℕ) (f : ℕ → ℕ) :
    ∑ k : Fin (m + 1), (if i < k.val then f k.val else 0) = ∑ k ∈ Finset.Icc (i + 1) m, f k := by
  rw [Fin.sum_univ_eq_sum_range (fun k => if i < k then f k else 0) (m + 1), ← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext k
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
  omega

/- English proof (translation)
Establish `hg1 : ∀ g : Fin 2, 1 - g ≠ g` using `by decide`. Establish `hL' : ∀ o g s k, ∑ i : Fin (L o).length, (RF.blkAt L o i).wt (X o) g s k = gap (r (tau o g s)) (a (tau o g s)) k`. Introduce `o g s k`. Rewrite using `[← hL]`. Conclude with `RF.sum_get (L o) fun q => q.1.wt (X o) g s k`.

Establish `hle : ∀ o i g s k, (RF.blkAt L o i).wt (X o) g s k ≠ 0 → k ≤ r (tau o g s)`. Introduce `o i g s k h`. Use `((gap_sums _ _ (hdom (tau o g s))).1 k ?_).2` and prove the remaining obligations. Rewrite using `[← hL']`. Introduce `h0`.

Conclude with `h ((Finset.sum_eq_zero_iff.1 h0) i (Finset.mem_univ _))`. Establish `key` using `GlobalTheory.CombMinor.prod_det_mem_HaO Ty r n C O cc isX a (Σ o, Σ _i : Fin (L o).length, Σ g : Fin 2, Σ s : ZMod d, Fin (r (tau o g s) + 1)) (fun α => tau α.1 α.2.2.1 α.2.2.2.1) (fun α => α.2.2.2.2.val) (fun α => Nat.le_of_lt_succ α.2.2.2.2.2) (fun α => ind C (fun ρ => pl ⟨α.1, …`. Use `key using 1` and compare the differences between its conclusion and the goal. Rewrite using `[map_prod, Fintype.prod_sigma]`. Use `Finset.prod_congr rfl fun o _ => ?_` and prove the remaining obligations.

Establish `ht : ∀ (P : Fin (L o).length → MvPolynomial (Fin n × WV (Ix r tau o)) C), toAll o (∏ i, P i) = ∏ i, toAll (I` using `Ix r tau) o (P i) := fun P => by unfold toAll; rw [map_prod]`. Rewrite using `[prodAll, ht, map_prod, Fintype.prod_sigma]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[poly_eq (X o) (F o) _ (fun g s => r (tau o g s)) (hle o i), toAll, Fintype.prod_sigma]`. Simplify using `only [map_prod, map_pow]`.

Use `Finset.prod_congr rfl fun g _ => ?_` and prove the remaining obligations. Rewrite using `[Fintype.prod_sigma]`. Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[← Fin.prod_univ_eq_prod_range]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations.

Distinguish the cases in `he : (RF.blkAt L o i).wt (X o) g s k.val = 0`. Simplify using `only [he, pow_zero]`. Use `congr 1`. Conclude with `rename_minor r tau o (X o) (F o) (h1 o) (h2 o) (fun ρ => pl ⟨o, i, ρ⟩) g s k.val (Nat.le_of_lt_succ k.2) (le_rows _ _ _ _ _ he) (by rw [hrk]; exact Nat.le_of_lt_succ k.2)`. Introduce `α ρ b`.

Unfold `ind`. Use `split_ifs`. Conclude with `O.one_mem`. Conclude with `O.zero_mem`. Conclude with `O.zero_mem`.

Introduce `τ h`. Take `⟨⟨o, g, s⟩, rfl⟩` from `surj τ`. Establish `h3 : ((o, 1 - g, s) : Orb × Fin 2 × ZMod d) = (o, g, s)` using `inj ((hcc o g s).symm.trans h)`. Simplify using `only [Prod.mk.injEq] at h3`. Conclude with `hg1 g h3.2.1`.

Introduce and unpack `⟨o, i, g, s, k⟩ ⟨o', i', g', s', k'⟩ he he' hσ ρ ρ' b`. Establish `h3 : ((o', g', s') : Orb × Fin 2 × ZMod d) = (o, 1 - g, s)` using `inj (hσ.trans (hcc o g s))`. Simplify using `only [Prod.mk.injEq] at h3`. Take `⟨rfl, rfl, rfl⟩` from `h3`. Assume the negation of the conclusion as `hc`.

Rewrite `hc` using `[not_or]`. Take `⟨hc, hc'⟩` from `hc`. Simplify using `only [ind] at hc hc'`. Apply the tactic sequence `split_ifs at hc hc' with a1 a2 a3 a4 <;> try contradiction`. Establish `h4` using `hpl (a2.symm.trans a4)`.

Establish `h5 : i = i'` using `congrArg Sigma.fst (eq_of_heq (Sigma.mk.inj h4).2)`. Substitute `h5` using the available equality. Take `⟨e1, e2⟩` from `both_groups _ _ _ _ _ _ _ he he'`. Establish `b1` using `k.2`. Establish `b2` using `k'.2`.

Apply the tactic sequence `rcases hsm o' g s' with h | h <;> simp only at e1 e2 <;> omega`. Introduce `τ i`. Take `⟨⟨o, g, s⟩, rfl⟩` from `surj τ`. Simplify using `only at i ⊢`. Rewrite using `[← (((gap_sums _ _ (hdom (tau o g s))).2 _ le_rfl).1 i.val i.2), ← sum_fin_gap, Finset.sum_filter, Fintype.sum_sigma, Finset.sum_eq_single o]`.

Rewrite using `[Fintype.sum_sigma]`. Simplify using `only [← hL']`. Establish `: ∀ k : Fin (r (tau o g s) + 1), (if i.val < k.val then ∑ j : Fin (L o).length, (RF.blkAt L o j).wt (X o) g s k.val else 0) = ∑ j : Fin (L o).length, if i.val < k.val then (RF.blkAt L o j).wt (X o) g s k.val else 0`. Introduce `k`. Apply the tactic sequence `split_ifs <;> simp`.

Rewrite using `[Finset.sum_congr rfl fun k _ => this k]`. Use `Eq.trans ?_ Finset.sum_comm` and prove the remaining obligations. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Fintype.sum_sigma, Finset.sum_eq_single g]`. Rewrite using `[Fintype.sum_sigma, Finset.sum_eq_single s]`.

Simplify using the standard rewrite rules. Introduce `s' _ hs`. Use `Finset.sum_eq_zero fun k _ => if_neg fun h => hs ?_` and prove the remaining obligations. Establish `h3 : ((o, g, s') : Orb × Fin 2 × ZMod d) = (o, g, s)` using `inj h.1`. Simplify using `using h3`.

Simplify using the standard rewrite rules. Introduce `g' _ hs`. Use `Finset.sum_eq_zero fun k _ => if_neg fun h => hs ?_` and prove the remaining obligations. Establish `h3 : ((o, g', k.1) : Orb × Fin 2 × ZMod d) = (o, g, s)` using `inj h.1`. Simplify using `only [Prod.mk.injEq] at h3`.

Conclude with `h3.2.1`. Simplify using the standard rewrite rules. Introduce `o' _ hs`. Use `Finset.sum_eq_zero fun k _ => if_neg fun h => hs ?_` and prove the remaining obligations. Establish `h3 : ((o', k.2.1, k.2.2.1) : Orb × Fin 2 × ZMod d) = (o, g, s)` using `inj h.1`.

Simplify using `only [Prod.mk.injEq] at h3`. Conclude with `h3.1`. Simplify using the standard rewrite rules.
-/
theorem prod_mem [Fintype Ty] (O : Subring C) (cc : Ty → Ty) (isX : Ty → Prop) (a : Ty → ℕ → ℕ)
    (inj : Function.Injective fun x : Orb × Fin 2 × ZMod d => tau x.1 x.2.1 x.2.2)
    (surj : Function.Surjective fun x : Orb × Fin 2 × ZMod d => tau x.1 x.2.1 x.2.2)
    (hcc : ∀ o g s, cc (tau o g s) = tau o (1 - g) s)
    {J : Orb → Fin 2 → Type} [∀ o g, Fintype (J o g)] (X : ∀ o, RowData C V d (Ix r tau o) (J o))
    (F : ∀ o, RF.Flag (X o)) (h1 : ∀ o g a c, ((F o).en g a c).1 = a)
    (h2 : ∀ o g a c, (((F o).en g a c).2 : ℕ) = c) (hrk : ∀ o g s, (X o).rkF g s = r (tau o g s))
    (hsm : ∀ o g s, r (tau o g s) < (X o).n ∨ r (tau o (1 - g) s) < (X o).n)
    (hdom : ∀ τ i j, i ≤ j → j < r τ → a τ j ≤ a τ i) {n : ℕ} (L : Orb → List (RF.GlobalTheory d × ℝ))
    (hL : ∀ o g s k, ((L o).map fun q => q.1.wt (X o) g s k).sum = gap (r (tau o g s)) (a (tau o g s)) k)
    (pl : (Σ o, Σ i : Fin (L o).length, Fin (RF.rowsAt X L o i)) → Fin n) (hpl : Function.Injective pl) :
    MvPolynomial.rename (toLet r tau)
      (∏ o, toAll o (prodAll (RF.plAt n pl o) fun i => (RF.blkAt L o i).poly (X o) (F o))) ∈
        HaO r n C O cc isX a := by
  have hg1 : ∀ g : Fin 2, 1 - g ≠ g := by decide
  have hL' : ∀ o g s k, ∑ i : Fin (L o).length, (RF.blkAt L o i).wt (X o) g s k =
      gap (r (tau o g s)) (a (tau o g s)) k := by
    intro o g s k
    rw [← hL]
    exact RF.sum_get (L o) fun q => q.1.wt (X o) g s k
  have hle : ∀ o i g s k, (RF.blkAt L o i).wt (X o) g s k ≠ 0 → k ≤ r (tau o g s) := by
    intro o i g s k h
    refine ((gap_sums _ _ (hdom (tau o g s))).1 k ?_).2
    rw [← hL']
    intro h0
    exact h ((Finset.sum_eq_zero_iff.1 h0) i (Finset.mem_univ _))
  have key := GlobalTheory.CombMinor.prod_det_mem_HaO Ty r n C O cc isX a
    (Σ o, Σ _i : Fin (L o).length, Σ g : Fin 2, Σ s : ZMod d, Fin (r (tau o g s) + 1))
    (fun α => tau α.1 α.2.2.1 α.2.2.2.1) (fun α => α.2.2.2.2.val) (fun α => Nat.le_of_lt_succ α.2.2.2.2.2)
    (fun α => ind C (fun ρ => pl ⟨α.1, α.2.1, ρ⟩) α.2.2.2.2.val)
    (fun α => (RF.blkAt L α.1 α.2.1).wt (X α.1) α.2.2.1 α.2.2.2.1 α.2.2.2.2.val) ?_ ?_ ?_ ?_
  · convert key using 1
    rw [map_prod, Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun o _ => ?_
    have ht : ∀ (P : Fin (L o).length → MvPolynomial (Fin n × WV (Ix r tau o)) C),
        toAll o (∏ i, P i) = ∏ i, toAll (I := Ix r tau) o (P i) := fun P => by unfold toAll; rw [map_prod]
    rw [prodAll, ht, map_prod, Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [poly_eq (X o) (F o) _ (fun g s => r (tau o g s)) (hle o i), toAll, Fintype.prod_sigma]
    simp only [map_prod, map_pow]
    refine Finset.prod_congr rfl fun g _ => ?_
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [← Fin.prod_univ_eq_prod_range]
    refine Finset.prod_congr rfl fun k _ => ?_
    by_cases he : (RF.blkAt L o i).wt (X o) g s k.val = 0
    · simp only [he, pow_zero]
    · congr 1
      exact rename_minor r tau o (X o) (F o) (h1 o) (h2 o) (fun ρ => pl ⟨o, i, ρ⟩) g s k.val
        (Nat.le_of_lt_succ k.2) (le_rows _ _ _ _ _ he) (by rw [hrk]; exact Nat.le_of_lt_succ k.2)
  · intro α ρ b
    unfold ind
    split_ifs
    · exact O.one_mem
    · exact O.zero_mem
    · exact O.zero_mem
  · intro τ h
    obtain ⟨⟨o, g, s⟩, rfl⟩ := surj τ
    have h3 : ((o, 1 - g, s) : Orb × Fin 2 × ZMod d) = (o, g, s) := inj ((hcc o g s).symm.trans h)
    simp only [Prod.mk.injEq] at h3
    exact hg1 g h3.2.1
  · rintro ⟨o, i, g, s, k⟩ ⟨o', i', g', s', k'⟩ he he' hσ ρ ρ' b
    have h3 : ((o', g', s') : Orb × Fin 2 × ZMod d) = (o, 1 - g, s) := inj (hσ.trans (hcc o g s))
    simp only [Prod.mk.injEq] at h3
    obtain ⟨rfl, rfl, rfl⟩ := h3
    by_contra hc
    rw [not_or] at hc
    obtain ⟨hc, hc'⟩ := hc
    simp only [ind] at hc hc'
    split_ifs at hc hc' with a1 a2 a3 a4 <;> try contradiction
    have h4 := hpl (a2.symm.trans a4)
    have h5 : i = i' := congrArg Sigma.fst (eq_of_heq (Sigma.mk.inj h4).2)
    subst h5
    obtain ⟨e1, e2⟩ := both_groups _ _ _ _ _ _ _ he he'
    have b1 := k.2
    have b2 := k'.2
    rcases hsm o' g s' with h | h <;> simp only at e1 e2 <;> omega
  · intro τ i
    obtain ⟨⟨o, g, s⟩, rfl⟩ := surj τ
    simp only at i ⊢
    rw [← (((gap_sums _ _ (hdom (tau o g s))).2 _ le_rfl).1 i.val i.2), ← sum_fin_gap, Finset.sum_filter,
      Fintype.sum_sigma, Finset.sum_eq_single o]
    · rw [Fintype.sum_sigma]
      simp only [← hL']
      have : ∀ k : Fin (r (tau o g s) + 1), (if i.val < k.val then
          ∑ j : Fin (L o).length, (RF.blkAt L o j).wt (X o) g s k.val else 0) =
          ∑ j : Fin (L o).length, if i.val < k.val then (RF.blkAt L o j).wt (X o) g s k.val else 0 := by
        intro k
        split_ifs <;> simp
      rw [Finset.sum_congr rfl fun k _ => this k]
      refine Eq.trans ?_ Finset.sum_comm
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Fintype.sum_sigma, Finset.sum_eq_single g]
      · rw [Fintype.sum_sigma, Finset.sum_eq_single s]
        · simp
        · intro s' _ hs
          refine Finset.sum_eq_zero fun k _ => if_neg fun h => hs ?_
          have h3 : ((o, g, s') : Orb × Fin 2 × ZMod d) = (o, g, s) := inj h.1
          simpa using h3
        · simp
      · intro g' _ hs
        refine Finset.sum_eq_zero fun k _ => if_neg fun h => hs ?_
        have h3 : ((o, g', k.1) : Orb × Fin 2 × ZMod d) = (o, g, s) := inj h.1
        simp only [Prod.mk.injEq] at h3
        exact h3.2.1
      · simp
    · intro o' _ hs
      refine Finset.sum_eq_zero fun k _ => if_neg fun h => hs ?_
      have h3 : ((o', k.2.1, k.2.2.1) : Orb × Fin 2 × ZMod d) = (o, g, s) := inj h.1
      simp only [Prod.mk.injEq] at h3
      exact h3.1
    · simp

end Letters

section Main

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

/- English proof (translation)
Introduce `E _ _ _ H Dw lv Xo c _ _ T io y C3 C _ _ V ι _ k Y _ Orb _ d _ lab ha hg surj hrk hj Hy F hF a hdom n L _ hL pl hpl`. Use `⟨_, ?_, isImgO Dw.mult lab.tau ha.inj (fun o => Y.raw (pairOfLab ha hg o)) (fun w i => ι (chartUnitVectors C3 w i)) (fun w => rfl) _⟩` and prove the remaining obligations. Use `prod_mem Dw.mult lab.tau V.RR _ _ (fun τ i => a (τ, i)) ha.inj surj ?_ (fun o => RF.rd Y (pairOfLab ha hg) Hy o) F (fun o g s q => (F o).en_ty g s q) hF ?_ ?_ ?_ L (fun o => hL o (Finset.mem_univ o)) pl hpl` and prove the remaining obligations. Introduce `o g s fin_cases g`. Conclude with `(ha.conj o s).symm`.

Use `show ComplexEmbedding.conjugate (lab.tau o 1 s) = lab.tau o 0 s`. Rewrite using `[ha.conj]`. Conclude with `star_star _`. Introduce `o g s`. Conclude with `(GlobalTheory.flag_of_numbering C V d (fun _ => ZMod d) (fun g s => Dw.mult (lab.tau o g s)) (fun _ => Equiv.refl _) _ (RF.rd Y (pairOfLab ha hg) Hy o) (fun _ _ => rfl)).1 g s`.

Introduce `o g s show _ < lab.n ∨ _ < lab.n`. Distinguish the cases in `hb : lab.big o g s`. Use `right`. Rewrite using `[(hrk o).2.2 (1 - g) s (fun h => ((hrk o).1 g s).1 h hb)]`. Conclude with `hj`.

Use `left`. Rewrite using `[(hrk o).2.2 g s hb]`. Conclude with `hj`. Introduce `τ i j hij hj'`. Conclude with `hdom τ ⟨i, lt_of_le_of_lt hij hj'⟩ ⟨j, hj'⟩ hij`.
-/
theorem blkMemSt_pair : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], (∀ x : 𝓞 E, star x = H.bar x) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y → ∀ (Orb : Type) [Fintype Orb] (d : ℕ) [NeZero d] (lab : Lab E Orb d) (ha : LabArith V io ι lab) (hg : LabGeo C3 ι Y lab), Function.Surjective (fun x : Orb × Fin 2 × ZMod d => lab.tau x.1 x.2.1 x.2.2) → lab.RankOK Dw → lab.j' < lab.n → ∀ (Hy : ∀ o, (Y.raw (pairOfLab ha hg o)).Hyps V) (F : ∀ o, RF.Flag (RF.rd Y (pairOfLab ha hg) Hy o)), (∀ o g s q, (((F o).en g s q).2 : ℕ) = q) → ∀ (a : (E →+* ℂ) × ℕ → ℕ), DomW Dw a → ∀ n : ℕ, RF.BlockMembershipChart Y (pairOfLab ha hg) Hy (chartLetterSystem C3 V ι a) n F Finset.univ (fun o g s => gap (Dw.mult (lab.tau o g s)) fun i => a (lab.tau o g s, i)) := by
  intro E _ _ _ H Dw lv Xo c _ _ T io y C3 C _ _ V ι _ k Y _ Orb _ d _ lab ha hg surj hrk hj Hy F hF a hdom n L _ hL pl hpl
  refine ⟨_, ?_, isImgO Dw.mult lab.tau ha.inj (fun o => Y.raw (pairOfLab ha hg o))
    (fun w i => ι (chartUnitVectors C3 w i)) (fun w => rfl) _⟩
  refine prod_mem Dw.mult lab.tau V.RR _ _ (fun τ i => a (τ, i)) ha.inj surj ?_
    (fun o => RF.rd Y (pairOfLab ha hg) Hy o) F (fun o g s q => (F o).en_ty g s q) hF ?_ ?_ ?_ L
    (fun o => hL o (Finset.mem_univ o)) pl hpl
  · intro o g s
    fin_cases g
    · exact (ha.conj o s).symm
    · show ComplexEmbedding.conjugate (lab.tau o 1 s) = lab.tau o 0 s
      rw [ha.conj]
      exact star_star _
  · intro o g s
    exact (GlobalTheory.flag_of_numbering C V d (fun _ => ZMod d) (fun g s => Dw.mult (lab.tau o g s))
      (fun _ => Equiv.refl _) _ (RF.rd Y (pairOfLab ha hg) Hy o) (fun _ _ => rfl)).1 g s
  · intro o g s
    show _ < lab.n ∨ _ < lab.n
    by_cases hb : lab.big o g s
    · right
      rw [(hrk o).2.2 (1 - g) s (fun h => ((hrk o).1 g s).1 h hb)]
      exact hj
    · left
      rw [(hrk o).2.2 g s hb]
      exact hj
  · intro τ i j hij hj'
    exact hdom τ ⟨i, lt_of_le_of_lt hij hj'⟩ ⟨j, hj'⟩ hij

end Main

end GlobalTheory.MemPair
