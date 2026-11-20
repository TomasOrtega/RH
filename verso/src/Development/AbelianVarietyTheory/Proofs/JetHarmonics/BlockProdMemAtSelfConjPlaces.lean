import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.IsSelfOf
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GapParts
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ProdDetMemHaO

set_option autoImplicit false

noncomputable section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.SelfConjMem

/- English proof (translation)
Distinguish the cases in `hu : u = 0`. Simplify using `[hu]`. Take `⟨h1, h2⟩` from `h hu`. Rewrite using `[Finset.prod_eq_single g0, Finset.prod_eq_single a0, Finset.prod_eq_single (n - 1)]`. Establish `: n - 1 + 1 = n` using `by omega`.

Simplify using `[this]`. Introduce `k _ hk`. Establish `: k + 1 ≠ n` using `by omega`. Simplify using `[this]`. Introduce `hk`.

Conclude with `absurd (Finset.mem_range.2 (by omega)) hk`. Introduce `a _ ha`. Simplify using `[ha]`. Simplify using the standard rewrite rules. Introduce `g _ hg`.

Simplify using `[hg]`. Simplify using the standard rewrite rules.
-/
theorem prod_single_pow {R : Type} [CommMonoid R] {d : ℕ} [NeZero d] (rk : Fin 2 → ZMod d → ℕ)
    (M : Fin 2 → ZMod d → ℕ → R) (g0 : Fin 2) (a0 : ZMod d) (n u : ℕ) (h : u ≠ 0 → 1 ≤ n ∧ n ≤ rk g0 a0) :
    ∏ g, ∏ a, ∏ k ∈ Finset.range (rk g a), M g a (k + 1) ^ (if g = g0 ∧ a = a0 ∧ k + 1 = n then u else 0) =
      M g0 a0 n ^ u := by
  by_cases hu : u = 0
  · simp [hu]
  obtain ⟨h1, h2⟩ := h hu
  rw [Finset.prod_eq_single g0, Finset.prod_eq_single a0, Finset.prod_eq_single (n - 1)]
  · have : n - 1 + 1 = n := by omega
    simp [this]
  · intro k _ hk
    have : k + 1 ≠ n := by omega
    simp [this]
  · intro hk
    exact absurd (Finset.mem_range.2 (by omega)) hk
  · intro a _ ha
    simp [ha]
  · simp
  · intro g _ hg
    simp [hg]
  · simp

section Block

variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type}
  [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J) (F : RF.Flag X)

/- English proof (translation)
Consider the cases of `b with`. Consider the case `bi g0 a0 i y`. Assume the negation of the conclusion as `hk`. Establish `: k ≠ X.n` using `fun e => hk (le_of_eq e)`. Conclude with `h (by simp [RF.GlobalTheory.wt, this])`.

Consider the case `ch g0 a0 u`. Assume the negation of the conclusion as `hk`. Establish `: k ≠ X.n` using `fun e => hk (le_of_eq e)`. Conclude with `h (by simp [RF.GlobalTheory.wt, this])`. Consider the case `mon g0 e N`.

Assume the negation of the conclusion as `hk`. Establish `: ¬ k ≤ N` using `hk`. Conclude with `h (by simp [RF.GlobalTheory.wt, this])`.
-/
theorem le_rows_of_wt (b : RF.GlobalTheory d) (g : Fin 2) (a : ZMod d) (k : ℕ) (h : b.wt X g a k ≠ 0) : k ≤ b.what₂ X.n := by
  cases b with
  | bi g0 a0 i y =>
    by_contra hk
    have : k ≠ X.n := fun e => hk (le_of_eq e)
    exact h (by simp [RF.GlobalTheory.wt, this])
  | ch g0 a0 u =>
    by_contra hk
    have : k ≠ X.n := fun e => hk (le_of_eq e)
    exact h (by simp [RF.GlobalTheory.wt, this])
  | mon g0 e N =>
    by_contra hk
    have : ¬ k ≤ N := hk
    exact h (by simp [RF.GlobalTheory.wt, this])

/- English proof (translation)
Consider the cases of `b with`. Consider the case `bi g0 a0 i y => show (MvPolynomial.rename (F.letter g0 a0) (minorK C X.n (X.rkF g0 a0) X.n) ^ (V.l ^ i * y) * MvPolynomial.rename (F.letter (1 - g0) (a0 + (i : ZMod d))) (minorK C X.n (X.rkF (1 - g0) (a0 + (i : ZMod d))) X.n) ^ y : MvPolynomial (Fin X.n × WV I) C) = ∏ g, ∏ a, ∏ k …`. Simplify using `only [RF.GlobalTheory.wt, pow_add, Finset.prod_mul_distrib]`. Rewrite using `[prod_single_pow X.rkF (fun g a k => MvPolynomial.rename (F.letter g a) (minorK C X.n (X.rkF g a) k)), prod_single_pow X.rkF (fun g a k => MvPolynomial.rename (F.letter g a) (minorK C X.n (X.rkF g a) k))]`. Introduce `hy`.

Apply `h` to reduce the goal to its premises. Simplify using `[RF.GlobalTheory.wt, hy]`. Introduce `hy`. Apply `h` to reduce the goal to its premises. Simplify using `only [RF.GlobalTheory.wt, and_self, if_true]`.

Use linear arithmetic over natural numbers and integers. Consider the case `ch g0 a0 u => show (MvPolynomial.rename (F.letter g0 a0) (minorK C X.n (X.rkF g0 a0) X.n) ^ u : MvPolynomial (Fin X.n × WV I) C) = ∏ g, ∏ a, ∏ k ∈ Finset.range (X.rkF g a), MvPolynomial.rename (F.letter g a) (minorK C X.n (X.rkF g a) (k + 1)) ^ (RF.GlobalTheory.ch g0 a0 u).wt X g …`. Simplify using `only [RF.GlobalTheory.wt]`. Rewrite using `[prod_single_pow X.rkF (fun g a k => MvPolynomial.rename (F.letter g a) (minorK C X.n (X.rkF g a) k))]`. Introduce `hy`.

Apply `h` to reduce the goal to its premises. Simplify using `[RF.GlobalTheory.wt, hy]`. Consider the case `mon g0 e N => show (∏ a : ZMod d, MvPolynomial.rename (F.letter g0 a) (monP C N (X.rkF g0 a) (e a)) : MvPolynomial (Fin N × WV I) C) = ∏ g, ∏ a, ∏ k ∈ Finset.range (X.rkF g a), MvPolynomial.rename (F.letter g a) (minorK C N (X.rkF g a) (k + 1)) ^ (RF.GlobalTheory.mon g0 e N).wt X …`. Simplify using `only [RF.GlobalTheory.wt]`. Use `symm`.

Rewrite using `[Finset.prod_eq_single g0]`. Use `symm`. Use `Finset.prod_congr rfl fun a _ => ?_` and prove the remaining obligations. Unfold `monP`. Rewrite using `[map_prod]`.

Simplify using `only [map_pow]`. Rewrite using `[← Finset.prod_subset (s₁ := Finset.range (min N (X.rkF g0 a))) (Finset.range_subset_range.2 (min_le_right _ _))]`. Rewrite using `[Finset.range_eq_Ico, Finset.prod_Ico_add' (fun k => MvPolynomial.rename (F.letter g0 a) (minorK C N (X.rkF g0 a) k) ^ (if True ∧ 1 ≤ k ∧ k ≤ min N (X.rkF g0 a) then e a k else 0)) 0 _ 1]`. Rewrite using `[show Finset.Ico (0 + 1) (min N (X.rkF g0 a) + 1) = Finset.Icc 1 (min N (X.rkF g0 a)) from by`. Use extensionality with `x`.

Simplify using `only [Finset.mem_Ico, Finset.mem_Icc]`. Use the proof step `omega]`. Use `Finset.prod_congr rfl fun k hk => ?_` and prove the remaining obligations. Rewrite using `[if_pos ⟨trivial, Finset.mem_Icc.1 hk⟩]`. Introduce `k _ hk`.

Rewrite using `[if_neg, pow_zero]`. Rewrite `hk` using `[Finset.mem_range]`. Use linear arithmetic over natural numbers and integers. Introduce `g _ hg`. Simplify using `[hg]`.

Simplify using the standard rewrite rules.
-/
theorem poly_eq_prod (b : RF.GlobalTheory d) (h : ∀ g a k, b.wt X g a k ≠ 0 → 1 ≤ k ∧ k ≤ X.rkF g a) :
    b.poly X F = ∏ g, ∏ a, ∏ k ∈ Finset.range (X.rkF g a),
      MvPolynomial.rename (F.letter g a) (minorK C (b.what₂ X.n) (X.rkF g a) (k + 1)) ^ b.wt X g a (k + 1) := by
  cases b with
  | bi g0 a0 i y =>
    show (MvPolynomial.rename (F.letter g0 a0) (minorK C X.n (X.rkF g0 a0) X.n) ^ (V.l ^ i * y) *
        MvPolynomial.rename (F.letter (1 - g0) (a0 + (i : ZMod d)))
          (minorK C X.n (X.rkF (1 - g0) (a0 + (i : ZMod d))) X.n) ^ y : MvPolynomial (Fin X.n × WV I) C) =
      ∏ g, ∏ a, ∏ k ∈ Finset.range (X.rkF g a),
        MvPolynomial.rename (F.letter g a) (minorK C X.n (X.rkF g a) (k + 1)) ^
          (RF.GlobalTheory.bi g0 a0 i y).wt X g a (k + 1)
    simp only [RF.GlobalTheory.wt, pow_add, Finset.prod_mul_distrib]
    rw [prod_single_pow X.rkF (fun g a k => MvPolynomial.rename (F.letter g a) (minorK C X.n (X.rkF g a) k)),
      prod_single_pow X.rkF (fun g a k => MvPolynomial.rename (F.letter g a) (minorK C X.n (X.rkF g a) k))]
    · intro hy
      apply h
      simp [RF.GlobalTheory.wt, hy]
    · intro hy
      apply h
      simp only [RF.GlobalTheory.wt, and_self, if_true]
      omega
  | ch g0 a0 u =>
    show (MvPolynomial.rename (F.letter g0 a0) (minorK C X.n (X.rkF g0 a0) X.n) ^ u : MvPolynomial (Fin X.n × WV I) C) =
      ∏ g, ∏ a, ∏ k ∈ Finset.range (X.rkF g a),
        MvPolynomial.rename (F.letter g a) (minorK C X.n (X.rkF g a) (k + 1)) ^
          (RF.GlobalTheory.ch g0 a0 u).wt X g a (k + 1)
    simp only [RF.GlobalTheory.wt]
    rw [prod_single_pow X.rkF (fun g a k => MvPolynomial.rename (F.letter g a) (minorK C X.n (X.rkF g a) k))]
    · intro hy
      apply h
      simp [RF.GlobalTheory.wt, hy]
  | mon g0 e N =>
    show (∏ a : ZMod d, MvPolynomial.rename (F.letter g0 a) (monP C N (X.rkF g0 a) (e a)) :
        MvPolynomial (Fin N × WV I) C) =
      ∏ g, ∏ a, ∏ k ∈ Finset.range (X.rkF g a),
        MvPolynomial.rename (F.letter g a) (minorK C N (X.rkF g a) (k + 1)) ^
          (RF.GlobalTheory.mon g0 e N).wt X g a (k + 1)
    simp only [RF.GlobalTheory.wt]
    symm
    rw [Finset.prod_eq_single g0]
    symm
    · refine Finset.prod_congr rfl fun a _ => ?_
      unfold monP
      rw [map_prod]
      simp only [map_pow]
      rw [← Finset.prod_subset (s₁ := Finset.range (min N (X.rkF g0 a))) (Finset.range_subset_range.2 (min_le_right _ _))]
      · rw [Finset.range_eq_Ico, Finset.prod_Ico_add' (fun k => MvPolynomial.rename (F.letter g0 a) (minorK C N (X.rkF g0 a) k) ^ (if True ∧ 1 ≤ k ∧ k ≤ min N (X.rkF g0 a) then e a k else 0)) 0 _ 1]
        rw [show Finset.Ico (0 + 1) (min N (X.rkF g0 a) + 1) = Finset.Icc 1 (min N (X.rkF g0 a)) from by
          ext x; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega]
        refine Finset.prod_congr rfl fun k hk => ?_
        rw [if_pos ⟨trivial, Finset.mem_Icc.1 hk⟩]
      · intro k _ hk
        rw [if_neg, pow_zero]
        rw [Finset.mem_range] at hk
        omega
    · intro g _ hg
      simp [hg]
    · simp

end Block

section Image

variable {C : Type} [Field C] {Ty : Type} {r : Ty → ℕ} {Orb : Type} [Fintype Orb] (tau : Orb → ZMod 2 → Ty)
  {N n : ℕ} (pl : Fin N × Fin 2 ↪ Fin n)

variable (r) in

abbrev Var : Type := WVO fun (o : Orb) (_ : Fin 2) => Σ s : ZMod 2, Fin (r (tau o s))

def lt (ρ : Fin N) (w : Var r tau) (col : Fin 2) : Letter Ty r n := ⟨tau w.1 w.2.2.1, w.2.2.2, pl (ρ, col)⟩

def sub (gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C) (x : Fin N × Var r tau) : MvPolynomial (Letter Ty r n) C :=
  ∑ col, MvPolynomial.C (gm x.2.1 x.2.2.2.1 col x.2.2.1) * MvPolynomial.X (lt tau pl x.1 x.2 col)

def co (gi : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C) (ℓ : Letter Ty r n) (x : Fin N × Var r tau) : C :=
  ∑ col, if ℓ = lt tau pl x.1 x.2 col then gi x.2.1 x.2.2.2.1 x.2.2.1 col else 0

omit [Fintype Orb] in
/- English proof (translation)
Take `⟨o, g, s, i⟩` from `w`. Take `⟨o', g', s', i'⟩` from `w'`. Establish `h1 : tau o s = tau o' s'` using `congrArg Sigma.fst h`. Establish `h2 : ((o, s) : Orb × ZMod 2) = (o', s')` using `hinj h1`. Take `⟨rfl, rfl⟩` from `Prod.mk.inj h2`.

Establish `h3` using `eq_of_heq (Sigma.mk.inj h).2`. Take `⟨rfl, h4⟩` from `Prod.mk.inj h3`. Take `⟨rfl, rfl⟩` from `Prod.mk.inj (pl.injective h4)`. Conclude with `⟨rfl, rfl, rfl⟩`.
-/
theorem lt_eq (hinj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2) {ρ ρ' : Fin N} {w w' : Var r tau}
    {col col' : Fin 2} (h : lt tau pl ρ w col = lt tau pl ρ' w' col') :
    ρ = ρ' ∧ col = col' ∧ w' = ⟨w.1, w'.2.1, w.2.2⟩ := by
  obtain ⟨o, g, s, i⟩ := w
  obtain ⟨o', g', s', i'⟩ := w'
  have h1 : tau o s = tau o' s' := congrArg Sigma.fst h
  have h2 : ((o, s) : Orb × ZMod 2) = (o', s') := hinj h1
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
  have h3 := eq_of_heq (Sigma.mk.inj h).2
  obtain ⟨rfl, h4⟩ := Prod.mk.inj h3
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pl.injective h4)
  exact ⟨rfl, rfl, rfl⟩

omit [Fintype Orb] in
/- English proof (translation)
The claim follows from `Finset.sum_eq_zero fun _ _ => if_neg fun e => h (lt_eq tau pl hinj e).1.symm`.
-/
theorem co_ne (hinj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2)
    (gi : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C) {ρ ρ' : Fin N} (w w' : Var r tau) (col : Fin 2) (h : ρ' ≠ ρ) :
    co tau pl gi (lt tau pl ρ w col) (ρ', w') = 0 :=
  Finset.sum_eq_zero fun _ _ => if_neg fun e => h (lt_eq tau pl hinj e).1.symm

/- English proof (translation)
Establish `hi : Function.Injective fun g : Fin 2 => (⟨w.1, g, w.2.2⟩ : Var r tau)` using `fun g g' e => congrArg (fun x : Var r tau => x.2.1) e`. Rewrite using `[← Finset.sum_subset (Finset.subset_univ (Finset.univ.image fun g : Fin 2 => (⟨w.1, g, w.2.2⟩ : Var r tau))), Finset.sum_image fun g _ g' _ e => hi e]`. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Use `congr 1`. Unfold `co`.

Rewrite using `[Finset.sum_eq_single col]`. Conclude with `if_pos rfl`. Introduce `col' _ hc`. Conclude with `if_neg fun e => hc (lt_eq tau pl hinj e).2.1.symm`. Simplify using the standard rewrite rules.

Introduce `w' _ hw`. Establish `: co tau pl gi (lt tau pl ρ w col) (ρ, w') = 0` using `Finset.sum_eq_zero fun _ _ => if_neg fun e => hw (Finset.mem_image.2 ⟨w'.2.1, Finset.mem_univ _, (lt_eq tau pl hinj e).2.2.symm⟩)`. Rewrite using `[this, zero_smul]`.
-/
theorem sum_co (hinj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2)
    (gi : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C) {M : Type} [AddCommGroup M] [Module C M] (f : Var r tau → M)
    (ρ : Fin N) (w : Var r tau) (col : Fin 2) :
    ∑ w', co tau pl gi (lt tau pl ρ w col) (ρ, w') • f w' = ∑ g, gi w.1 w.2.2.1 g col • f ⟨w.1, g, w.2.2⟩ := by
  have hi : Function.Injective fun g : Fin 2 => (⟨w.1, g, w.2.2⟩ : Var r tau) :=
    fun g g' e => congrArg (fun x : Var r tau => x.2.1) e
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image fun g : Fin 2 => (⟨w.1, g, w.2.2⟩ : Var r tau))),
    Finset.sum_image fun g _ g' _ e => hi e]
  · refine Finset.sum_congr rfl fun g _ => ?_
    congr 1
    unfold co
    rw [Finset.sum_eq_single col]
    · exact if_pos rfl
    · intro col' _ hc
      exact if_neg fun e => hc (lt_eq tau pl hinj e).2.1.symm
    · simp
  · intro w' _ hw
    have : co tau pl gi (lt tau pl ρ w col) (ρ, w') = 0 :=
      Finset.sum_eq_zero fun _ _ => if_neg fun e =>
        hw (Finset.mem_image.2 ⟨w'.2.1, Finset.mem_univ _, (lt_eq tau pl hinj e).2.2.symm⟩)
    rw [this, zero_smul]

/- English proof (translation)
Use `⟨co tau pl gi, fun ℓ hℓ => ?_, ?_⟩` and prove the remaining obligations. Establish `h1` using `MvPolynomial.vars_bind₁ (sub tau pl gm) Q hℓ`. Take `⟨x, -, hx⟩` from `Finset.mem_biUnion.1 h1`. Take `⟨col, -, hc⟩` from `Finset.mem_biUnion.1 (MvPolynomial.vars_sum_subset _ _ hx)`. Establish `h2 : ℓ = lt tau pl x.1 x.2 col`.

Use `MvPolynomial.vars_mul _ _ hc` as an intermediate fact. Simplify `this` using `[MvPolynomial.vars_C, MvPolynomial.vars_X]`. Substitute `h2` using the available equality. Use `⟨x.1, col, rfl, fun ρ' w h => co_ne tau pl hinj gi _ _ _ h, ?_⟩` and prove the remaining obligations. Rewrite using `[sum_co tau pl hinj gi (fun w => (X w.1).u w.2.1 w.2.2)]`.

Use function extensionality and compare the values at `z`. Establish `h3 : ∑ g, gm x.2.1 x.2.2.2.1 z.1 g * gi x.2.1 x.2.2.2.1 g col = if z.1 = col then 1 else 0`. Establish `h0 : gm x.2.1 x.2.2.2.1 * gi x.2.1 x.2.2.2.1 = 1` using `mul_eq_one_comm.1 (hg x.2.1 x.2.2.2.1)`. Use `congrFun (congrFun h0 z.1) col` as an intermediate fact. Rewrite `this` using `[Matrix.mul_apply, Matrix.one_apply]`. Then use the resulting hypothesis.

Simplify using `only [Finset.sum_apply, Pi.smul_apply, hu, smul_eq_mul]`. Establish `h4 : ∀ g, gi x.2.1 x.2.2.2.1 g col * (gm x.2.1 x.2.2.2.1 z.1 g * uv ⟨tau x.2.1 x.2.2.2.1, x.2.2.2.2⟩ z.2) = (gm x.2.1 x.2.2.2.1 z.1 g * gi x.2.1 x.2.2.2.1 g col) * uv ⟨tau x.2.1 x.2.2.2.1, x.2.2.2.2⟩ z.2` using `fun g => by ring`. Simplify using `only [h4, ← Finset.sum_mul, h3]`. Use `split_ifs`. Rewrite using `[one_mul]`.

Both sides reduce to the same expression. Rewrite using `[zero_mul]`. Establish `key : (MvPolynomial.aeval (fun ℓ => ∑ x, MvPolynomial.C (co tau pl gi ℓ x) * MvPolynomial.X x)).comp (MvPolynomial.aeval (sub tau pl gm)) = AlgHom.id C (MvPolynomial (Fin N × Var r tau) C)`. Use `MvPolynomial.algHom_ext fun x => ?_` and prove the remaining obligations. Establish `h1 : ∀ col, (∑ x', MvPolynomial.C (co tau pl gi (lt tau pl x.1 x.2 col) x') * MvPolynomial.X x' : MvPolynomial (Fin N × Var r tau) C) = ∑ g, gi x.2.1 x.2.2.2.1 g col • MvPolynomial.X (x.1, ⟨x.2.1, g, x.2.2.2⟩)`.

Introduce `col`. Rewrite using `[Fintype.sum_prod_type, Finset.sum_eq_single x.1]`. Rewrite using `[← sum_co tau pl hinj gi (fun w => (MvPolynomial.X (x.1, w) : MvPolynomial (Fin N × Var r tau) C))]`. Conclude with `Finset.sum_congr rfl fun w _ => (MvPolynomial.smul_eq_C_mul _ _).symm`. Introduce `ρ _ h`.

Conclude with `Finset.sum_eq_zero fun w _ => by rw [co_ne tau pl hinj gi _ _ _ h, map_zero, zero_mul]`. Simplify using the standard rewrite rules. Simplify using `only [AlgHom.comp_apply, MvPolynomial.aeval_X, sub, map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, h1, AlgHom.id_apply]`. Simplify using `only [← MvPolynomial.smul_eq_C_mul, Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm]`.

Establish `h3 : ∀ g, ∑ col, gm x.2.1 x.2.2.2.1 col x.2.2.1 * gi x.2.1 x.2.2.2.1 g col = if g = x.2.2.1 then 1 else 0`. Introduce `g`. Use `congrFun (congrFun (hg x.2.1 x.2.2.2.1) g) x.2.2.1` as an intermediate fact. Rewrite `this` using `[Matrix.mul_apply, Matrix.one_apply]`. Rewrite using `[← this]`.

Conclude with `Finset.sum_congr rfl fun _ _ => mul_comm _ _`. Simplify using `only [← Finset.sum_smul, h3, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Conclude with `(congrArg (fun φ => φ Q) key).symm`.
-/
theorem isImgS_sub (hinj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2)
    (gm gi : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C) (hg : ∀ o s, gi o s * gm o s = 1) {dd : ℕ}
    (X : ∀ o, RawChart C 2 (fun _ => Σ s : ZMod 2, Fin (r (tau o s))) (Fin 2 × Fin dd))
    (uv : (Σ τ : Ty, Fin (r τ)) → Fin dd → C)
    (hu : ∀ o g c x, (X o).u g c x = gm o c.1 x.1 g * uv ⟨tau o c.1, c.2⟩ x.2)
    (Q : MvPolynomial (Fin N × Var r tau) C) :
    IsImgS X pl (fun ℓ : Letter Ty r n => ℓ.2.2) (fun ℓ => uv ⟨ℓ.1, ℓ.2.1⟩) (MvPolynomial.aeval (sub tau pl gm) Q) Q := by
  refine ⟨co tau pl gi, fun ℓ hℓ => ?_, ?_⟩
  · have h1 := MvPolynomial.vars_bind₁ (sub tau pl gm) Q hℓ
    obtain ⟨x, -, hx⟩ := Finset.mem_biUnion.1 h1
    obtain ⟨col, -, hc⟩ := Finset.mem_biUnion.1 (MvPolynomial.vars_sum_subset _ _ hx)
    have h2 : ℓ = lt tau pl x.1 x.2 col := by
      have := MvPolynomial.vars_mul _ _ hc
      simpa [MvPolynomial.vars_C, MvPolynomial.vars_X] using this
    subst h2
    refine ⟨x.1, col, rfl, fun ρ' w h => co_ne tau pl hinj gi _ _ _ h, ?_⟩
    rw [sum_co tau pl hinj gi (fun w => (X w.1).u w.2.1 w.2.2)]
    funext z
    have h3 : ∑ g, gm x.2.1 x.2.2.2.1 z.1 g * gi x.2.1 x.2.2.2.1 g col = if z.1 = col then 1 else 0 := by
      have h0 : gm x.2.1 x.2.2.2.1 * gi x.2.1 x.2.2.2.1 = 1 := mul_eq_one_comm.1 (hg x.2.1 x.2.2.2.1)
      have := congrFun (congrFun h0 z.1) col
      rwa [Matrix.mul_apply, Matrix.one_apply] at this
    simp only [Finset.sum_apply, Pi.smul_apply, hu, smul_eq_mul]
    have h4 : ∀ g, gi x.2.1 x.2.2.2.1 g col * (gm x.2.1 x.2.2.2.1 z.1 g * uv ⟨tau x.2.1 x.2.2.2.1, x.2.2.2.2⟩ z.2) =
        (gm x.2.1 x.2.2.2.1 z.1 g * gi x.2.1 x.2.2.2.1 g col) * uv ⟨tau x.2.1 x.2.2.2.1, x.2.2.2.2⟩ z.2 := fun g => by ring
    simp only [h4, ← Finset.sum_mul, h3]
    split_ifs
    · rw [one_mul]; rfl
    · rw [zero_mul]
  · have key : (MvPolynomial.aeval (fun ℓ => ∑ x, MvPolynomial.C (co tau pl gi ℓ x) * MvPolynomial.X x)).comp
        (MvPolynomial.aeval (sub tau pl gm)) = AlgHom.id C (MvPolynomial (Fin N × Var r tau) C) := by
      refine MvPolynomial.algHom_ext fun x => ?_
      have h1 : ∀ col, (∑ x', MvPolynomial.C (co tau pl gi (lt tau pl x.1 x.2 col) x') * MvPolynomial.X x' :
          MvPolynomial (Fin N × Var r tau) C) =
          ∑ g, gi x.2.1 x.2.2.2.1 g col • MvPolynomial.X (x.1, ⟨x.2.1, g, x.2.2.2⟩) := by
        intro col
        rw [Fintype.sum_prod_type, Finset.sum_eq_single x.1]
        · rw [← sum_co tau pl hinj gi (fun w => (MvPolynomial.X (x.1, w) : MvPolynomial (Fin N × Var r tau) C))]
          exact Finset.sum_congr rfl fun w _ => (MvPolynomial.smul_eq_C_mul _ _).symm
        · intro ρ _ h
          exact Finset.sum_eq_zero fun w _ => by rw [co_ne tau pl hinj gi _ _ _ h, map_zero, zero_mul]
        · simp
      simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, sub, map_sum, map_mul, MvPolynomial.aeval_C,
        MvPolynomial.algebraMap_eq, h1, AlgHom.id_apply]
      simp only [← MvPolynomial.smul_eq_C_mul, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      have h3 : ∀ g, ∑ col, gm x.2.1 x.2.2.2.1 col x.2.2.1 * gi x.2.1 x.2.2.2.1 g col = if g = x.2.2.1 then 1 else 0 := by
        intro g
        have := congrFun (congrFun (hg x.2.1 x.2.2.2.1) g) x.2.2.1
        rw [Matrix.mul_apply, Matrix.one_apply] at this
        rw [← this]
        exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
      simp only [← Finset.sum_smul, h3, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact (congrArg (fun φ => φ Q) key).symm

end Image

def sh (g : Fin 2) : ZMod 2 := if g = 0 then 0 else 1

section One

variable {C : Type} [Field C] {V : VF C} {m : ZMod 2 → ℕ} {J : Fin 2 → Type} [∀ g, Fintype (J g)]
  (X : RowData C V 2 (fun _ => Σ s : ZMod 2, Fin (m s)) J) (F : RF.Flag X)

/- English proof (translation)
Unfold `RowData.rkF`. Simplify using `only [hty, add_left_inj]`. Establish `: (Finset.univ.filter fun c : Σ s : ZMod 2, Fin (m s) => c.1 = s) = Finset.univ.map ⟨fun i : Fin (m s) => (⟨s, i⟩ : Σ s : ZMod 2, Fin (m s)), fun _ _ e => eq_of_heq (Sigma.mk.inj e).2⟩`. Use extensionality with `⟨s', i⟩`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Function.Embedding.coeFn_mk]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl`. Conclude with `⟨i, rfl⟩`. Introduce and unpack `⟨i', h⟩`. Conclude with `(congrArg Sigma.fst h).symm`.

Rewrite using `[this, Finset.card_map, Finset.card_univ, Fintype.card_fin]`.
-/
theorem rkF_eq (hty : ∀ g c, (X.G g).ty (Sum.inl c) = c.1 + sh g) (g : Fin 2) (s : ZMod 2) :
    X.rkF g (s + sh g) = m s := by
  unfold RowData.rkF
  simp only [hty, add_left_inj]
  have : (Finset.univ.filter fun c : Σ s : ZMod 2, Fin (m s) => c.1 = s) =
      Finset.univ.map ⟨fun i : Fin (m s) => (⟨s, i⟩ : Σ s : ZMod 2, Fin (m s)), fun _ _ e => eq_of_heq (Sigma.mk.inj e).2⟩ := by
    ext ⟨s', i⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Function.Embedding.coeFn_mk]
    constructor
    · rintro rfl
      exact ⟨i, rfl⟩
    · rintro ⟨i', h⟩
      exact (congrArg Sigma.fst h).symm
  rw [this, Finset.card_map, Finset.card_univ, Fintype.card_fin]

/- English proof (translation)
Establish `h1` using `F.en_ty g (s + sh g) q`. Establish `h2` using `hen g (s + sh g) q`. Rewrite `h1` using `[hty, add_left_inj]`. Generalize the expression as in `F.en g (s + sh g) q = c at h1 h2`. Take `⟨s', i'⟩` from `c`.

Simplify using `only at h1 h2`. Substitute `h1` using the available equality. Rewrite using `[Fin.ext (h2.trans h)]`.
-/
theorem en_eq (hty : ∀ g c, (X.G g).ty (Sum.inl c) = c.1 + sh g) (hen : ∀ g a q, ((F.en g a q).2 : ℕ) = q)
    (g : Fin 2) (s : ZMod 2) (q : Fin (X.rkF g (s + sh g))) (i : Fin (m s)) (h : (q : ℕ) = i) :
    F.en g (s + sh g) q = ⟨s, i⟩ := by
  have h1 := F.en_ty g (s + sh g) q
  have h2 := hen g (s + sh g) q
  rw [hty, add_left_inj] at h1
  generalize F.en g (s + sh g) q = c at h1 h2
  obtain ⟨s', i'⟩ := c
  dsimp only at h1 h2
  subst h1
  rw [Fin.ext (h2.trans h)]

/- English proof (translation)
Establish `key : (∀ g a k, b.wt X g a k ≠ 0 → k = X.n) → s = s'`. Introduce `hk`. Establish `e1` using `(h _ _ _ h1).2`. Establish `e2` using `(h _ _ _ h2).2`. Rewrite `e1` using `[rkF_eq X hty, hk _ _ _ h1]`.

Rewrite `e2` using `[rkF_eq X hty, hk _ _ _ h2]`. Establish `t : ∀ s : ZMod 2, s ≠ 1 → s = 0` using `by decide`. Rewrite using `[t s (by rintro rfl; omega), t s' (by rintro rfl; omega)]`. Consider the cases of `b with`. Consider the case `bi g0 a0 i y`.

Use `key fun g a k hk => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `e`. Conclude with `hk (by simp [RF.GlobalTheory.wt, e])`. Consider the case `ch g0 a0 u`. Use `key fun g a k hk => ?_` and prove the remaining obligations.

Assume the negation of the conclusion as `e`. Conclude with `hk (by simp [RF.GlobalTheory.wt, e])`. Consider the case `mon g0 e N`. Take `⟨s0, hs0⟩` from `hmon g0 e N rfl`. Simplify using `only [RF.GlobalTheory.wt, ne_eq, ite_eq_right_iff, Classical.not_imp] at h1 h2`.

Take `⟨⟨rfl, -⟩, h1⟩` from `h1`. Take `⟨⟨rfl, -⟩, h2⟩` from `h2`. Establish `e1 : s + sh g' = s0` using `by_contra fun e => h1 (hs0 _ _ e)`. Establish `e2 : s' + sh g' = s0` using `by_contra fun e => h2 (hs0 _ _ e)`. Conclude with `add_right_cancel (e1.trans e2.symm)`.
-/
theorem one_type (hty : ∀ g c, (X.G g).ty (Sum.inl c) = c.1 + sh g) (hn : m 1 < X.n) (b : RF.GlobalTheory 2)
    (hmon : ∀ g e N, b = RF.GlobalTheory.mon g e N → ∃ s : ZMod 2, ∀ a k, a ≠ s → e a k = 0)
    (h : ∀ g a k, b.wt X g a k ≠ 0 → 1 ≤ k ∧ k ≤ X.rkF g a) {g g' : Fin 2} {s s' : ZMod 2} {k k' : ℕ}
    (h1 : b.wt X g (s + sh g) k ≠ 0) (h2 : b.wt X g' (s' + sh g') k' ≠ 0) : s = s' := by
  have key : (∀ g a k, b.wt X g a k ≠ 0 → k = X.n) → s = s' := by
    intro hk
    have e1 := (h _ _ _ h1).2
    have e2 := (h _ _ _ h2).2
    rw [rkF_eq X hty, hk _ _ _ h1] at e1
    rw [rkF_eq X hty, hk _ _ _ h2] at e2
    have t : ∀ s : ZMod 2, s ≠ 1 → s = 0 := by decide
    rw [t s (by rintro rfl; omega), t s' (by rintro rfl; omega)]
  cases b with
  | bi g0 a0 i y =>
    refine key fun g a k hk => ?_
    by_contra e
    exact hk (by simp [RF.GlobalTheory.wt, e])
  | ch g0 a0 u =>
    refine key fun g a k hk => ?_
    by_contra e
    exact hk (by simp [RF.GlobalTheory.wt, e])
  | mon g0 e N =>
    obtain ⟨s0, hs0⟩ := hmon g0 e N rfl
    simp only [RF.GlobalTheory.wt, ne_eq, ite_eq_right_iff, Classical.not_imp] at h1 h2
    obtain ⟨⟨rfl, -⟩, h1⟩ := h1
    obtain ⟨⟨rfl, -⟩, h2⟩ := h2
    have e1 : s + sh g' = s0 := by_contra fun e => h1 (hs0 _ _ e)
    have e2 : s' + sh g' = s0 := by_contra fun e => h2 (hs0 _ _ e)
    exact add_right_cancel (e1.trans e2.symm)

end One

def cf {C : Type} [Field C] {N n what₂ : ℕ} (pl : Fin N × Fin 2 ↪ Fin n) (pr : Fin what₂ → Fin N) (M : Fin 2 → C)
    (ρ : ℕ) (b : Fin n) : C :=
  if h : ρ < what₂ then ∑ col, if b = pl (pr ⟨ρ, h⟩, col) then M col else 0 else 0

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Apply `h` to reduce the goal to its premises. Unfold `cf`. Use `split_ifs with h1`. Conclude with `Finset.sum_eq_zero fun col _ => if_neg fun e => hc ⟨_, _, e⟩`.

Both sides reduce to the same expression.
-/
theorem cf_ne {C : Type} [Field C] {N n what₂ : ℕ} (pl : Fin N × Fin 2 ↪ Fin n) (pr : Fin what₂ → Fin N) (M : Fin 2 → C)
    (ρ : ℕ) (b : Fin n) (h : cf pl pr M ρ b ≠ 0) : ∃ ρ' col, b = pl (pr ρ', col) := by
  by_contra hc
  apply h
  unfold cf
  split_ifs with h1
  · exact Finset.sum_eq_zero fun col _ => if_neg fun e => hc ⟨_, _, e⟩
  · rfl

section Mem

variable {C : Type} [Field C] {V : VF C} {Ty : Type} {r : Ty → ℕ} {Orb : Type} [Fintype Orb] (tau : Orb → ZMod 2 → Ty)
  {N n : ℕ} (pl : Fin N × Fin 2 ↪ Fin n) (gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C)
  {J : Orb → Fin 2 → Type} [∀ o g, Fintype (J o g)]
  (X : ∀ o, RowData C V 2 (fun _ => Σ s : ZMod 2, Fin (r (tau o s))) (J o)) (F : ∀ o, RF.Flag (X o))

omit [Fintype Orb] in

/- English proof (translation)
Establish `hk' : k ≤ (X o).rkF g (s + sh g)` using `by rw [rkF_eq (X o) (hty o)]; exact hk`. Unfold `minorK toAll`. Rewrite using `[dif_pos ⟨hr, hk'⟩, AlgHom.map_det, AlgHom.map_det, AlgHom.map_det, AlgHom.map_det]`. Use `congr 1`. Use `Matrix.ext fun ρ i => ?_` and prove the remaining obligations.

Simplify using `only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, MvPolynomial.rename_X, MvPolynomial.aeval_X, RF.Flag.letter]`. Rewrite using `[en_eq (X o) (F o) (hty o) (hen o) g s _ (Fin.castLE hk i) rfl]`. Establish `hρ : (ρ : ℕ) < what₂` using `lt_of_lt_of_le ρ.2 hr`. Simplify using `only [cf, dif_pos hρ, map_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`.

Unfold `sub`. Use `Finset.sum_congr rfl fun col _ => ?_` and prove the remaining obligations. Use `symm`. Rewrite using `[Finset.sum_eq_single (pl (pr ⟨ρ, hρ⟩, col))]`. Rewrite using `[if_pos rfl]`.

Both sides reduce to the same expression. Introduce `b _ hb`. Rewrite using `[if_neg hb, map_zero, zero_mul]`. Simplify using the standard rewrite rules.
-/
theorem sub_minor (hty : ∀ o g c, ((X o).G g).ty (Sum.inl c) = c.1 + sh g)
    (hen : ∀ o g a q, (((F o).en g a q).2 : ℕ) = q) (o : Orb) {what₂ : ℕ} (pr : Fin what₂ → Fin N) (g : Fin 2)
    (s : ZMod 2) (k : ℕ) (hk : k ≤ r (tau o s)) (hr : k ≤ what₂) :
    MvPolynomial.aeval (sub tau pl gm) (toAll (I := fun (o : Orb) (_ : Fin 2) => Σ s : ZMod 2, Fin (r (tau o s))) o
      (MvPolynomial.rename (fun x : Fin what₂ × WV (fun _ => Σ s : ZMod 2, Fin (r (tau o s))) => (pr x.1, x.2))
        (MvPolynomial.rename ((F o).letter g (s + sh g)) (minorK C what₂ ((X o).rkF g (s + sh g)) k)))) =
      (Matrix.of fun ρ i : Fin k => ∑ b, MvPolynomial.C (cf pl pr (fun col => gm o s col g) ρ b) *
        (MvPolynomial.X ⟨tau o s, Fin.castLE hk i, b⟩ : MvPolynomial (Letter Ty r n) C)).det := by
  have hk' : k ≤ (X o).rkF g (s + sh g) := by rw [rkF_eq (X o) (hty o)]; exact hk
  unfold minorK toAll
  rw [dif_pos ⟨hr, hk'⟩, AlgHom.map_det, AlgHom.map_det, AlgHom.map_det, AlgHom.map_det]
  congr 1
  refine Matrix.ext fun ρ i => ?_
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, MvPolynomial.rename_X, MvPolynomial.aeval_X,
    RF.Flag.letter]
  rw [en_eq (X o) (F o) (hty o) (hen o) g s _ (Fin.castLE hk i) rfl]
  have hρ : (ρ : ℕ) < what₂ := lt_of_lt_of_le ρ.2 hr
  simp only [cf, dif_pos hρ, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  unfold sub
  refine Finset.sum_congr rfl fun col _ => ?_
  symm
  rw [Finset.sum_eq_single (pl (pr ⟨ρ, hρ⟩, col))]
  · rw [if_pos rfl]
    rfl
  · intro b _ hb
    rw [if_neg hb, map_zero, zero_mul]
  · simp

end Mem

section Main

variable {C : Type} [Field C] {V : VF C} {Ty : Type} [Fintype Ty] {r : Ty → ℕ} {Orb : Type} [Fintype Orb]
  (tau : Orb → ZMod 2 → Ty)
  {N n : ℕ} (pl : Fin N × Fin 2 ↪ Fin n) (gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C)
  {J : Orb → Fin 2 → Type} [∀ o g, Fintype (J o g)]
  (X : ∀ o, RowData C V 2 (fun _ => Σ s : ZMod 2, Fin (r (tau o s))) (J o)) (F : ∀ o, RF.Flag (X o))

/- English proof (translation)
Establish `hwt' : ∀ o s k, ∑ i : Fin (L o).length, ∑ g, (RF.blkAt L o i).wt (X o) g (s + sh g) k = gap (r (tau o s)) (a (tau o s)) k`. Introduce `o s k`. Rewrite using `[← hwt, ← RF.sum_get]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Fin.sum_univ_two]`.

Establish `e0 : s + sh 0 = s` using `add_zero s`. Establish `e1 : s + sh 1 = s + 1` using `rfl`. Rewrite using `[e0, e1]`. Establish `hsupp : ∀ o i g b k, (RF.blkAt L o i).wt (X o) g b k ≠ 0 → 1 ≤ k ∧ k ≤ (X o).rkF g b`. Introduce `o i g b k h`.

Take `⟨s, rfl⟩ : ∃ s, b = s + sh g` from `⟨b - sh g, by ring⟩`. Rewrite using `[rkF_eq (X o) (hty o)]`. Use `(gap_sums _ _ (hdom (tau o s))).1 k ?_` and prove the remaining obligations. Rewrite using `[← hwt']`. Introduce `e`.

Conclude with `h (Finset.sum_eq_zero_iff.1 (Finset.sum_eq_zero_iff.1 e i (Finset.mem_univ _)) g (Finset.mem_univ _))`. Establish `key` using `GlobalTheory.CombMinor.prod_det_mem_HaO Ty r n C O cc isX a (Σ o, Fin (L o).length × Fin 2 × Σ s : ZMod 2, Fin (r (tau o s))) (fun α => tau α.1 α.2.2.2.1) (fun α => α.2.2.2.2 + 1) (fun α => α.2.2.2.2.2) (fun α ρ b => cf pl (fun ρ => pc ⟨α.1, α.2.1, ρ⟩) (fun col => gm α.1 α.2.2.2. …`. Use `key using 1` and compare the differences between its conclusion and the goal. Rewrite using `[map_prod, Fintype.prod_sigma]`. Use `Finset.prod_congr rfl fun o _ => ?_` and prove the remaining obligations.

Rewrite using `[Fintype.prod_prod_type]`. Establish `hm : ∀ (K : Type) [Fintype K] (f : K → MvPolynomial (Fin N × WV fun _ => Σ s : ZMod 2, Fin (r (tau o s))) C), toAll (I` using `fun (o : Orb) (_ : Fin 2) => Σ s : ZMod 2, Fin (r (tau o s))) o (∏ i, f i) = ∏ i, toAll (I := fun (o : Orb) (_ : Fin 2) => Σ s : ZMod 2, Fin (r (tau o s))) o (f i) := fun K _ f => map_prod _ _ _`. Unfold `prodAll`. Rewrite using `[hm, map_prod]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations.

Use `beta_reduce`. Rewrite using `[poly_eq_prod (X o) (F o) _ (hsupp o i), map_prod, hm, map_prod, Fintype.prod_prod_type]`. Use `Finset.prod_congr rfl fun g _ => ?_` and prove the remaining obligations. Rewrite using `[← Equiv.prod_comp (Equiv.addRight (sh g)), map_prod, hm, map_prod, Fintype.prod_sigma]`. Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations.

Simplify using `only [Equiv.coe_addRight]`. Rewrite using `[show Finset.range ((X o).rkF g (s + sh g)) = Finset.range (r (tau o s)) from by rw [rkF_eq (X o) (hty o)], Finset.prod_range, map_prod, hm, map_prod]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Distinguish the cases in `he : (RF.blkAt L o i).wt (X o) g (s + sh g) (k + 1) = 0`. Rewrite using `[he, pow_zero, pow_zero, map_one]`.

Unfold `toAll`. Rewrite using `[map_one, map_one]`. Rewrite using `[← sub_minor tau pl gm X F hty hen o (fun ρ => pc ⟨o, i, ρ⟩) g s (k + 1) k.2 (le_rows_of_wt _ _ _ _ _ he)]`. Unfold `toAll`. Rewrite using `[map_pow, map_pow, map_pow]`.

Both sides reduce to the same expression. Introduce `α ρ b`. Unfold `cf`. Use `split_ifs`. Use `O.sum_mem fun col _ => ?_ split_ifs` and prove the remaining obligations.

Conclude with `hO _ _ _ _`. Conclude with `O.zero_mem`. Conclude with `O.zero_mem`. Introduce and unpack `⟨o, i, g, s, k⟩ ⟨o', i', g', s', k'⟩ h1 h2 h3 ρ ρ' b`. Assume the negation of the conclusion as `hc`.

Rewrite `hc` using `[not_or]`. Take `⟨ρ1, col, e1⟩` from `cf_ne _ _ _ _ _ hc.1`. Take `⟨ρ2, col', e2⟩` from `cf_ne _ _ _ _ _ hc.2`. Establish `e3` using `hpc (congrArg Prod.fst (pl.injective (e1.symm.trans e2)))`. Simplify using `only at e3 h1 h2 h3`.

Take `rfl : o = o'` from `congrArg Sigma.fst e3`. Take `rfl : i = i'` from `congrArg Sigma.fst (eq_of_heq (Sigma.mk.inj e3).2)`. Take `rfl : s = s'` from `one_type (X o) (hty o) (hn o) _ (hmon o _ (List.get_mem _ _)) (hsupp o i) h1 h2`. Conclude with `hcc _ h3.symm`. Introduce `τ i`.

Take `⟨⟨o, s⟩, rfl⟩` from `hbij.2 τ`. Simplify using `only at i ⊢`. Rewrite using `[Finset.sum_filter, Fintype.sum_sigma, Finset.sum_eq_single o]`. Rewrite using `[← ((gap_sums _ _ (hdom (tau o s))).2 _ le_rfl).1 i i.2]`. Simplify using `only [Fintype.sum_prod_type, Fintype.sum_sigma, ← hwt']`.

Rewrite using `[Finset.sum_comm (s := Finset.Icc _ _)]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm (s := Finset.Icc _ _)]`. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single s]`.

Rewrite using `[Fin.sum_univ_eq_sum_range (fun k => if tau o s = tau o s ∧ (i : ℕ) < k + 1 then (RF.blkAt L o j).wt (X o) g (s + sh g) (k + 1) else 0), Finset.range_eq_Ico, Finset.sum_Ico_add' (fun k => if tau o s = tau o s ∧ (i : ℕ) < k then (RF.blkAt L o j).wt (X o) g (s + sh g) k else 0) 0 _ …`. Use `Finset.sum_congr ?_ fun _ _ => rfl` and prove the remaining obligations. Use extensionality with `x`. Simplify using `only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Icc, true_and]`. Use linear arithmetic over natural numbers and integers.

Introduce `s' _ hs`. Conclude with `Finset.sum_eq_zero fun k _ => if_neg fun e => hs (congrArg Prod.snd (hbij.1 (a₁ := (o, s')) (a₂ := (o, s)) e.1))`. Simplify using the standard rewrite rules. Introduce `o' _ ho`. Conclude with `Finset.sum_eq_zero fun k _ => if_neg fun e => ho (congrArg Prod.fst (hbij.1 (a₁ := (o', k.2.2.1)) (a₂ := (o, s)) e.1))`.

Simplify using the standard rewrite rules.
-/
theorem sub_blocks_mem (hbij : Function.Bijective fun x : Orb × ZMod 2 => tau x.1 x.2)
    (O : Subring C) (hO : ∀ o s i j, gm o s i j ∈ O) (cc : Ty → Ty) (hcc : ∀ τ, cc τ ≠ τ) (isX : Ty → Prop)
    (a : Ty → ℕ → ℕ) (hdom : ∀ τ i j, i ≤ j → j < r τ → a τ j ≤ a τ i)
    (hty : ∀ o g c, ((X o).G g).ty (Sum.inl c) = c.1 + sh g)
    (hen : ∀ o g a q, (((F o).en g a q).2 : ℕ) = q) (hn : ∀ o, r (tau o 1) < (X o).n)
    (L : Orb → List (RF.GlobalTheory 2 × ℝ))
    (hmon : ∀ o, ∀ q ∈ L o, ∀ g e N, q.1 = RF.GlobalTheory.mon g e N → ∃ s : ZMod 2, ∀ a k, a ≠ s → e a k = 0)
    (hwt : ∀ o s k, ((L o).map fun q => q.1.wt (X o) 0 s k + q.1.wt (X o) 1 (s + 1) k).sum =
      gap (r (tau o s)) (a (tau o s)) k)
    (pc : (Σ o, Σ i : Fin (L o).length, Fin (RF.rowsAt X L o i)) → Fin N) (hpc : Function.Injective pc) :
    MvPolynomial.aeval (sub tau pl gm)
      (∏ o, toAll (I := fun (o : Orb) (_ : Fin 2) => Σ s : ZMod 2, Fin (r (tau o s))) o
        (prodAll (RF.plAt N pc o) fun i => (RF.blkAt L o i).poly (X o) (F o))) ∈ HaO r n C O cc isX a := by
  have hwt' : ∀ o s k, ∑ i : Fin (L o).length, ∑ g, (RF.blkAt L o i).wt (X o) g (s + sh g) k =
      gap (r (tau o s)) (a (tau o s)) k := by
    intro o s k
    rw [← hwt, ← RF.sum_get]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fin.sum_univ_two]
    have e0 : s + sh 0 = s := add_zero s
    have e1 : s + sh 1 = s + 1 := rfl
    rw [e0, e1]
  have hsupp : ∀ o i g b k, (RF.blkAt L o i).wt (X o) g b k ≠ 0 → 1 ≤ k ∧ k ≤ (X o).rkF g b := by
    intro o i g b k h
    obtain ⟨s, rfl⟩ : ∃ s, b = s + sh g := ⟨b - sh g, by ring⟩
    rw [rkF_eq (X o) (hty o)]
    refine (gap_sums _ _ (hdom (tau o s))).1 k ?_
    rw [← hwt']
    intro e
    exact h (Finset.sum_eq_zero_iff.1 (Finset.sum_eq_zero_iff.1 e i (Finset.mem_univ _)) g (Finset.mem_univ _))
  have key := GlobalTheory.CombMinor.prod_det_mem_HaO Ty r n C O cc isX a
    (Σ o, Fin (L o).length × Fin 2 × Σ s : ZMod 2, Fin (r (tau o s)))
    (fun α => tau α.1 α.2.2.2.1) (fun α => α.2.2.2.2 + 1) (fun α => α.2.2.2.2.2)
    (fun α ρ b => cf pl (fun ρ => pc ⟨α.1, α.2.1, ρ⟩) (fun col => gm α.1 α.2.2.2.1 col α.2.2.1) ρ b)
    (fun α => (RF.blkAt L α.1 α.2.1).wt (X α.1) α.2.2.1 (α.2.2.2.1 + sh α.2.2.1) (α.2.2.2.2 + 1)) ?_ hcc ?_ ?_
  · convert key using 1
    rw [map_prod, Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun o _ => ?_
    rw [Fintype.prod_prod_type]
    have hm : ∀ (K : Type) [Fintype K] (f : K → MvPolynomial (Fin N × WV fun _ => Σ s : ZMod 2, Fin (r (tau o s))) C),
        toAll (I := fun (o : Orb) (_ : Fin 2) => Σ s : ZMod 2, Fin (r (tau o s))) o (∏ i, f i) =
          ∏ i, toAll (I := fun (o : Orb) (_ : Fin 2) => Σ s : ZMod 2, Fin (r (tau o s))) o (f i) :=
      fun K _ f => map_prod _ _ _
    unfold prodAll
    rw [hm, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    beta_reduce
    rw [poly_eq_prod (X o) (F o) _ (hsupp o i), map_prod, hm, map_prod, Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun g _ => ?_
    rw [← Equiv.prod_comp (Equiv.addRight (sh g)), map_prod, hm, map_prod, Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun s _ => ?_
    simp only [Equiv.coe_addRight]
    rw [show Finset.range ((X o).rkF g (s + sh g)) = Finset.range (r (tau o s)) from by rw [rkF_eq (X o) (hty o)],
      Finset.prod_range, map_prod, hm, map_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    by_cases he : (RF.blkAt L o i).wt (X o) g (s + sh g) (k + 1) = 0
    · rw [he, pow_zero, pow_zero, map_one]
      unfold toAll
      rw [map_one, map_one]
    · rw [← sub_minor tau pl gm X F hty hen o (fun ρ => pc ⟨o, i, ρ⟩) g s (k + 1) k.2 (le_rows_of_wt _ _ _ _ _ he)]
      unfold toAll
      rw [map_pow, map_pow, map_pow]
      rfl
  · intro α ρ b
    unfold cf
    split_ifs
    · refine O.sum_mem fun col _ => ?_
      split_ifs
      · exact hO _ _ _ _
      · exact O.zero_mem
    · exact O.zero_mem
  · rintro ⟨o, i, g, s, k⟩ ⟨o', i', g', s', k'⟩ h1 h2 h3 ρ ρ' b
    by_contra hc
    rw [not_or] at hc
    obtain ⟨ρ1, col, e1⟩ := cf_ne _ _ _ _ _ hc.1
    obtain ⟨ρ2, col', e2⟩ := cf_ne _ _ _ _ _ hc.2
    have e3 := hpc (congrArg Prod.fst (pl.injective (e1.symm.trans e2)))
    dsimp only at e3 h1 h2 h3
    obtain rfl : o = o' := congrArg Sigma.fst e3
    obtain rfl : i = i' := congrArg Sigma.fst (eq_of_heq (Sigma.mk.inj e3).2)
    obtain rfl : s = s' := one_type (X o) (hty o) (hn o) _ (hmon o _ (List.get_mem _ _)) (hsupp o i) h1 h2
    exact hcc _ h3.symm
  · intro τ i
    obtain ⟨⟨o, s⟩, rfl⟩ := hbij.2 τ
    dsimp only at i ⊢
    rw [Finset.sum_filter, Fintype.sum_sigma, Finset.sum_eq_single o]
    · rw [← ((gap_sums _ _ (hdom (tau o s))).2 _ le_rfl).1 i i.2]
      simp only [Fintype.sum_prod_type, Fintype.sum_sigma, ← hwt']
      rw [Finset.sum_comm (s := Finset.Icc _ _)]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_comm (s := Finset.Icc _ _)]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [Finset.sum_eq_single s]
      · rw [Fin.sum_univ_eq_sum_range (fun k => if tau o s = tau o s ∧ (i : ℕ) < k + 1 then
          (RF.blkAt L o j).wt (X o) g (s + sh g) (k + 1) else 0), Finset.range_eq_Ico,
          Finset.sum_Ico_add' (fun k => if tau o s = tau o s ∧ (i : ℕ) < k then
            (RF.blkAt L o j).wt (X o) g (s + sh g) k else 0) 0 _ 1, ← Finset.sum_filter]
        refine Finset.sum_congr ?_ fun _ _ => rfl
        ext x
        simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Icc, true_and]
        omega
      · intro s' _ hs
        exact Finset.sum_eq_zero fun k _ => if_neg fun e =>
          hs (congrArg Prod.snd (hbij.1 (a₁ := (o, s')) (a₂ := (o, s)) e.1))
      · simp
    · intro o' _ ho
      exact Finset.sum_eq_zero fun k _ => if_neg fun e =>
        ho (congrArg Prod.fst (hbij.1 (a₁ := (o', k.2.2.1)) (a₂ := (o, s)) e.1))
    · simp

end Main

/- English proof (translation)
Introduce `E _ _ _ H Dw lv Xo c _ _ T io y C3 C _ _ V ι _ k Y _ Orb _ lab ha hsurj hrk hj p hp Hy F hen a hdom N n pl`. Introduce `L hmon hwt pc hpc`. Use `⟨_, sub_blocks_mem (r := Dw.mult) lab.tau pl (fun o => (p o).gm) (fun o => (Y.rawSelf (p o)).rowData (Hy o)) F ⟨ha.inj, hsurj⟩ V.RR ?_ ComplexEmbedding.conjugate conj_ne_self_of_CM (InPsi H) (fun τ i => a (τ, i)) ?_ ?_ hen ?_ L hmon hwt pc hpc, ?_⟩` and prove the remaining obligations. Introduce `o s i j`. Take `⟨M, hM⟩` from `(p o).gm_lim 0`.

Establish `h1` using `(hM s i j)`. Rewrite `h1` using `[Nat.cast_zero]`. Establish `h2` using `h1.add ((p o).em_int s (M i j))`. Rewrite `h2` using `[sub_add_cancel]`. Then use the resulting hypothesis. Introduce `τ i j hij hj`.

Conclude with `hdom τ ⟨i, by omega⟩ ⟨j, hj⟩ hij`. Introduce `o g x show (if g = 0 then (p o).ty0 x else (p o).ty0 x + (p o).hd) = x.1 + sh g`. Rewrite using `[hp.ty0, hp.hd]`. Unfold `sh`. Use `split_ifs`.

Rewrite using `[add_zero]`. Both sides reduce to the same expression. Introduce `o show _ < (p o).n`. Rewrite using `[hp.n, (hrk o).2]`. Conclude with `hj`.

Use `isImgS_sub (r := Dw.mult) lab.tau pl ha.inj (fun o => (p o).gm) (fun o s => Matrix.of fun g col => (p o).gm (s + (p o).hd) col (1 - g)) ?_ (fun o => Y.rawSelf (p o)) (fun ℓ i => ι (chartUnitVectors C3 ℓ i)) ?_ _` and prove the remaining obligations. Introduce `o s`. Use extensionality with `g g'`. Rewrite using `[Matrix.mul_apply, Matrix.one_apply]`. Simplify using `only [Matrix.of_apply]`.

Rewrite using `[(p o).gm_hyp]`. Apply the tactic sequence `fin_cases g <;> fin_cases g' <;> simp`. Introduce `o g x z show (p o).gm ((p o).ty0 x) z.1 g * (p o).e x z.2 = _`. Rewrite using `[hp.ty0, hp.e]`.
-/
theorem blkMemC_self : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], (∀ x : 𝓞 E, star x = H.bar x) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y → ∀ (Orb : Type) [Fintype Orb] (lab : LabS E Orb), ArithS V io ι lab → Function.Surjective (fun x : Orb × ZMod 2 => lab.tau x.1 x.2) → lab.RankOK Dw → lab.j' < lab.n → ∀ p : ∀ o, SelfData Y 2 (lab.II Dw o), IsSelfOf C3 ι Y lab p → ∀ (Hy : ∀ o, (Y.rawSelf (p o)).Hyps V) (F : ∀ o, RF.Flag ((Y.rawSelf (p o)).rowData (Hy o))), (∀ o g s q, (((F o).en g s q).2 : ℕ) = q) → ∀ (a : (E →+* ℂ) × ℕ → ℕ), DomW Dw a → ∀ (N n : ℕ) (pl : Fin N × Fin 2 ↪ Fin n), RF.BlockMembershipSelfConjugate (fun o => (Y.rawSelf (p o)).rowData (Hy o)) N F (imgFamS Y p (chartLetterSystem C3 V ι a) pl) (fun o s => gap (Dw.mult (lab.tau o s)) fun i => a (lab.tau o s, i)) := by
  intro E _ _ _ H Dw lv Xo c _ _ T io y C3 C _ _ V ι _ k Y _ Orb _ lab ha hsurj hrk hj p hp Hy F hen a hdom N n pl
  intro L hmon hwt pc hpc
  refine ⟨_, sub_blocks_mem (r := Dw.mult) lab.tau pl (fun o => (p o).gm)
    (fun o => (Y.rawSelf (p o)).rowData (Hy o)) F ⟨ha.inj, hsurj⟩ V.RR ?_ ComplexEmbedding.conjugate
    conj_ne_self_of_CM (InPsi H) (fun τ i => a (τ, i)) ?_ ?_ hen ?_ L hmon hwt pc hpc, ?_⟩
  · intro o s i j
    obtain ⟨M, hM⟩ := (p o).gm_lim 0
    have h1 := (hM s i j)
    rw [Nat.cast_zero] at h1
    have h2 := h1.add ((p o).em_int s (M i j))
    rwa [sub_add_cancel] at h2
  · intro τ i j hij hj
    exact hdom τ ⟨i, by omega⟩ ⟨j, hj⟩ hij
  · intro o g x
    show (if g = 0 then (p o).ty0 x else (p o).ty0 x + (p o).hd) = x.1 + sh g
    rw [hp.ty0, hp.hd]
    unfold sh
    split_ifs
    · rw [add_zero]
    · rfl
  · intro o
    show _ < (p o).n
    rw [hp.n, (hrk o).2]
    exact hj
  · refine isImgS_sub (r := Dw.mult) lab.tau pl ha.inj (fun o => (p o).gm)
      (fun o s => Matrix.of fun g col => (p o).gm (s + (p o).hd) col (1 - g)) ?_ (fun o => Y.rawSelf (p o))
      (fun ℓ i => ι (chartUnitVectors C3 ℓ i)) ?_ _
    · intro o s
      ext g g'
      rw [Matrix.mul_apply, Matrix.one_apply]
      simp only [Matrix.of_apply]
      rw [(p o).gm_hyp]
      fin_cases g <;> fin_cases g' <;> simp
    · intro o g x z
      show (p o).gm ((p o).ty0 x) z.1 g * (p o).e x z.2 = _
      rw [hp.ty0, hp.e]

end GlobalTheory.SelfConjMem
