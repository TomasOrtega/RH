import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.LettersFreeOfRank
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.WachLettersFree

noncomputable section

namespace GlobalTheory.WachLettersCompare

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition GlobalTheory.IndefiniteRowSideFullHecke.WachLettersFreeness

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

attribute [local instance] letterModule

/- English proof (translation)
Use function extensionality and compare the values at `j`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Simplify using `[letE]`. Simplify using `[letE, h]`.
-/
theorem mul_letE (i : ZMod n) (a : LetA O n) : a * letE i = Pi.single i (a i) := by
  funext j
  by_cases h : j = i
  · subst h; simp [letE]
  · simp [letE, h]

/- English proof (translation)
Rewrite using `[mul_letE]`. Simplify using `[letE]`.
-/
theorem letE_mul_self (i : ZMod n) : (letE i : LetA O n) * letE i = letE i := by
  rw [mul_letE]; simp [letE]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Use `⟨(W.N T).smul_mem _ hy, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(letE i : LetA O n) • ((letE i : LetA O n) • y) = (letE i : LetA O n) • y`. Rewrite using `[smul_smul, letE_mul_self]`.

Introduce and unpack `⟨hx, he⟩`. Conclude with `⟨x, hx, he⟩`.
-/
theorem mem_Nl_iff (i : ZMod n) (x : W.DD T) :
    x ∈ W.Nl T i ↔ x ∈ W.N T ∧ (letE i : LetA O n) • x = x := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨(W.N T).smul_mem _ hy, ?_⟩
    change (letE i : LetA O n) • ((letE i : LetA O n) • y) = (letE i : LetA O n) • y
    rw [smul_smul, letE_mul_self]
  · rintro ⟨hx, he⟩
    exact ⟨x, hx, he⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨x, hx, rfl⟩`.
-/
theorem letE_smul_mem (i : ZMod n) {x : W.DD T} (hx : x ∈ W.N T) :
    (letE i : LetA O n) • x ∈ W.Nl T i := ⟨x, hx, rfl⟩

/- English proof (translation)
Use `W.φD_smul T (algebraMap (LetA O n) W.EE a) x` as an intermediate fact. Rewrite `this` using `[algebraMap_smul, W.φE_ext, algebraMap_smul]`. Conclude with `this`.
-/
theorem φD_smulA (a : LetA O n) (x : W.DD T) : W.φD T (a • x) = W.φA a • W.φD T x := by
  have := W.φD_smul T (algebraMap (LetA O n) W.EE a) x
  rw [algebraMap_smul, W.φE_ext, algebraMap_smul] at this
  exact this

/- English proof (translation)
Use `W.γD_smul T g (algebraMap (LetA O n) W.EE a) x` as an intermediate fact. Rewrite `this` using `[algebraMap_smul, W.γE_ext, algebraMap_smul]`. Conclude with `this`.
-/
theorem γD_smulA (g : W.Gam) (a : LetA O n) (x : W.DD T) :
    W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  have := W.γD_smul T g (algebraMap (LetA O n) W.EE a) x
  rw [algebraMap_smul, W.γE_ext, algebraMap_smul] at this
  exact this

/- English proof (translation)
Use function extensionality and compare the values at `j`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Simplify using `[LocWach.γA, letγ, letE]`. Simplify using `[LocWach.γA, letγ, letE, h]`.
-/
theorem γA_letE (g : W.Gam) (i : ZMod n) : W.γA g (letE i) = letE i := by
  funext j
  by_cases h : j = i
  · subst h; simp [LocWach.γA, letγ, letE]
  · simp [LocWach.γA, letγ, letE, h]

include W in

/- English proof (translation)
Use `PD.finK₀` as an intermediate fact. Conclude with `⟨by rw [W.n_eq]; exact Module.finrank_pos.ne'⟩`.
-/
theorem neZero_letters : NeZero n := by
  have := PD.finK₀
  exact ⟨by rw [W.n_eq]; exact Module.finrank_pos.ne'⟩

/- English proof (translation)
Establish `hq : IsUnit (algebraMap (LetA O n) W.EE W.q)`. Establish `h1 : (letπ : LetA O n) * W.q = (1 + letπ) ^ PD.p - 1`. Use function extensionality and compare the values at `i`. Simplify `W.q₀_def` using `[letπ, LocWach.q]`. Use `set x := algebraMap (LetA O n) W.EE letπ with hx`.

Take `⟨r, hr⟩` from `exists_add_pow_prime_eq PD.hp (1 : W.EE) x`. Take `⟨u, hu⟩ : IsUnit (x ^ PD.p)` from `W.EE_π.pow _`. Use `W.EE_complete` as an intermediate fact. Establish `hj : ((PD.p : ℕ) : W.EE) ∈ Ideal.jacobson (⊥ : Ideal W.EE)` using `IsAdicComplete.le_jacobson_bot (Ideal.span {((PD.p : ℕ) : W.EE)}) (Ideal.mem_span_singleton_self _)`. Establish `h2` using `(Ideal.mem_jacobson_bot.1 hj) (x * r * (↑u⁻¹ : W.EE))`.

Establish `h3 : x * algebraMap (LetA O n) W.EE W.q = (((PD.p : ℕ) : W.EE) * (x * r * (↑u⁻¹ : W.EE)) + 1) * u`. Rewrite using `[hx, ← map_mul, h1, map_sub, map_pow, map_add, map_one, ← hx, hr, ← hu]`. Use `u.inv_mul` as an intermediate fact. Take the linear combination `(-((PD.p : ℕ) : W.EE) * x * r) * this`. Conclude with `isUnit_of_mul_isUnit_right (h3 ▸ h2.mul u.isUnit)`.

Establish `key : ∀ k : ℕ, IsUnit (algebraMap (LetA O n) W.EE ((W.φA ^ k) W.q))`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simpa using hq`. Consider the case `succ k ih`.

Rewrite using `[pow_succ', AlgHom.mul_apply]`. Use `W.φE_ext ((W.φA ^ k) W.q)` as an intermediate fact. Conclude with `this ▸ ih.map W.φE`. Conclude with `key _`.
-/
theorem isUnit_Q : IsUnit (algebraMap (LetA O n) W.EE W.Q) := by
  have hq : IsUnit (algebraMap (LetA O n) W.EE W.q) := by
    have h1 : (letπ : LetA O n) * W.q = (1 + letπ) ^ PD.p - 1 := by
      funext i
      simpa [letπ, LocWach.q] using W.q₀_def
    set x := algebraMap (LetA O n) W.EE letπ with hx
    obtain ⟨r, hr⟩ := exists_add_pow_prime_eq PD.hp (1 : W.EE) x
    obtain ⟨u, hu⟩ : IsUnit (x ^ PD.p) := W.EE_π.pow _
    have := W.EE_complete
    have hj : ((PD.p : ℕ) : W.EE) ∈ Ideal.jacobson (⊥ : Ideal W.EE) :=
      IsAdicComplete.le_jacobson_bot (Ideal.span {((PD.p : ℕ) : W.EE)})
        (Ideal.mem_span_singleton_self _)
    have h2 := (Ideal.mem_jacobson_bot.1 hj) (x * r * (↑u⁻¹ : W.EE))
    have h3 : x * algebraMap (LetA O n) W.EE W.q =
        (((PD.p : ℕ) : W.EE) * (x * r * (↑u⁻¹ : W.EE)) + 1) * u := by
      rw [hx, ← map_mul, h1, map_sub, map_pow, map_add, map_one, ← hx, hr, ← hu]
      have := u.inv_mul
      linear_combination (-((PD.p : ℕ) : W.EE) * x * r) * this
    exact isUnit_of_mul_isUnit_right (h3 ▸ h2.mul u.isUnit)
  have key : ∀ k : ℕ, IsUnit (algebraMap (LetA O n) W.EE ((W.φA ^ k) W.q)) := by
    intro k
    induction k with
    | zero => simpa using hq
    | succ k ih =>
      rw [pow_succ', AlgHom.mul_apply]
      have := W.φE_ext ((W.φA ^ k) W.q)
      exact this ▸ ih.map W.φE
  exact key _

/- English proof (translation)
Rewrite `h` using `[← algebraMap_smul W.EE, ← algebraMap_smul W.EE (W.Q ^ m) y, map_pow]`. Conclude with `((isUnit_Q W).pow m).smul_left_cancel.1 h`.
-/
theorem Q_pow_smul_cancel (m : ℕ) {x y : W.DD T} (h : W.Q ^ m • x = W.Q ^ m • y) : x = y := by
  rw [← algebraMap_smul W.EE, ← algebraMap_smul W.EE (W.Q ^ m) y, map_pow] at h
  exact ((isUnit_Q W).pow m).smul_left_cancel.1 h

variable {W T}

/- English proof (translation)
Rewrite using `[← phi_letE W i, ← φD_smulA, ((mem_Nl_iff W T _ x).1 hx).2]`.
-/
theorem φD_fixed (i : ZMod n) {x : W.DD T} (hx : x ∈ W.Nl T (i - 1)) :
    (letE i : LetA O n) • W.φD T x = W.φD T x := by
  rw [← phi_letE W i, ← φD_smulA, ((mem_Nl_iff W T _ x).1 hx).2]

/- English proof (translation)
Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨z, hz, rfl⟩` from `hx`. Rewrite using `[← phi_letE W i, ← φD_smulA]`. Conclude with `Submodule.subset_span ⟨_, letE_smul_mem W T _ hz, rfl⟩`.

Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [smul_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul a x _ hx => rw [smul_comm]`. Conclude with `Submodule.smul_mem _ a hx`.
-/
theorem letE_smul_φpull (i : ZMod n) {y : W.DD T} (hy : y ∈ W.φpull T) :
    (letE i : LetA O n) • y ∈ phiPullLetter W T i := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z, hz, rfl⟩ := hx
    rw [← phi_letE W i, ← φD_smulA]
    exact Submodule.subset_span ⟨_, letE_smul_mem W T _ hz, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ a hx

variable (W T)

end Generic

end GlobalTheory.WachLettersCompare
