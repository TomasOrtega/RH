import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

namespace GlobalTheory.OneBasis.Places

/- English proof (translation)
Rewrite using `[← O.valuation_le_one_iff, ← O.valuation_le_one_iff, map_inv₀]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨?_, h.le, by simp [h]⟩` and prove the remaining obligations. Introduce and unpack `rfl`.

Simplify using `at h`. Introduce and unpack `⟨h0, h1, h2⟩`. Establish `: 0 < O.valuation x`. Rewrite using `[zero_lt_iff]`. Simplify using `using h0`.

Conclude with `le_antisymm h1 ((inv_le_one₀ this).1 h2)`.
-/
theorem val_eq_one_iff {F : Type} [Field F] (O : ValuationSubring F) (x : F) :
    O.valuation x = 1 ↔ x ≠ 0 ∧ x ∈ O ∧ x⁻¹ ∈ O := by
  rw [← O.valuation_le_one_iff, ← O.valuation_le_one_iff, map_inv₀]
  constructor
  · intro h
    refine ⟨?_, h.le, by simp [h]⟩
    rintro rfl
    simp at h
  · rintro ⟨h0, h1, h2⟩
    have : 0 < O.valuation x := by
      rw [zero_lt_iff]; simpa using h0
    exact le_antisymm h1 ((inv_le_one₀ this).1 h2)

/- English proof (translation)
Simplify using `only [val_eq_one_iff, ValuationSubring.mem_comap, map_inv₀, ne_eq, map_eq_zero]`.
-/
theorem val_comap {K F : Type} [Field K] [Field F] (σ : K →+* F) (O : ValuationSubring F) (x : K) :
    (O.comap σ).valuation x = 1 ↔ O.valuation (σ x) = 1 := by
  simp only [val_eq_one_iff, ValuationSubring.mem_comap, map_inv₀, ne_eq, map_eq_zero]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun i j => ⟨A i j, h i j⟩, rfl⟩`.
-/
theorem exists_lift {F : Type} [Field F] (O : ValuationSubring F) {r : ℕ} (A : Matrix (Fin r) (Fin r) F)
    (h : ∀ i j, A i j ∈ O) : ∃ A' : Matrix (Fin r) (Fin r) O, A'.map O.subtype = A :=
  ⟨fun i j => ⟨A i j, h i j⟩, rfl⟩

/- English proof (translation)
Take `⟨A', rfl⟩` from `exists_lift O A h`. Rewrite using `[O.valuation_le_one_iff, ← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Conclude with `(A'.det).2`.
-/
theorem det_mem {F : Type} [Field F] (O : ValuationSubring F) {r : ℕ} (A : Matrix (Fin r) (Fin r) F)
    (h : ∀ i j, A i j ∈ O) : O.valuation A.det ≤ 1 := by
  obtain ⟨A', rfl⟩ := exists_lift O A h
  rw [O.valuation_le_one_iff, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (A'.det).2

/- English proof (translation)
Establish `hs : Submodule.span k (Set.range v) = ⊤`. Assume the negation of the conclusion as `hne`. Take `⟨φ, hφ0, hφ⟩` from `Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)`. Establish `e : ∀ x : Fin r → k, φ x = (fun i => φ (Pi.single i 1)) ⬝ᵥ x`. Introduce `x`.

Rewrite using `[LinearMap.pi_apply_eq_sum_univ]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[smul_eq_mul, mul_comm]`. Use `congr 2`. Use extensionality with `j`.

Simplify using `[Pi.single_apply, eq_comm]`. Take `⟨i, hi⟩` from `h (fun i => φ (Pi.single i 1)) (by`. Introduce `h0`. Apply `hφ0` to reduce the goal to its premises. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations.

Rewrite using `[e, h0]`. Use the proof step `simp)`. Conclude with `hi (by rw [← e]; exact hφ (Submodule.subset_span ⟨i, rfl⟩))`. Take `⟨b, hb, hsp, hli⟩` from `exists_linearIndependent k (Set.range v)`. Set `B : Module.Basis b k (Fin r → k)` to `Module.Basis.mk hli (by`.

Rewrite using `[Subtype.range_coe_subtype, Set.setOf_mem_eq, hsp, hs])`. Set `e : Fin r ≃ b` to `(Pi.basisFun k (Fin r)).indexEquiv B`. Use `choose f hf using fun i : Fin r => hb (e i).2`. Use `⟨f, ?_⟩` and prove the remaining obligations. Establish `hl : LinearIndependent k (Matrix.of fun i j => v (f i) j).row`.

Use `hli.comp e e.injective` as an intermediate fact. Establish `e2 : (Matrix.of fun i j => v (f i) j).row = Subtype.val ∘ e` using `funext fun i => hf i`. Rewrite using `[e2]`. Conclude with `this`. Conclude with `((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_rows_iff_isUnit.1 hl)).ne_zero`.
-/
theorem exists_det_ne_zero {k J : Type} [Field k] {r : ℕ} (v : J → Fin r → k)
    (h : ∀ a : Fin r → k, a ≠ 0 → ∃ i, a ⬝ᵥ v i ≠ 0) :
    ∃ f : Fin r → J, (Matrix.of fun i j => v (f i) j).det ≠ 0 := by
  classical
  have hs : Submodule.span k (Set.range v) = ⊤ := by
    by_contra hne
    obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    have e : ∀ x : Fin r → k, φ x = (fun i => φ (Pi.single i 1)) ⬝ᵥ x := by
      intro x
      rw [LinearMap.pi_apply_eq_sum_univ]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_eq_mul, mul_comm]
      congr 2
      ext j
      simp [Pi.single_apply, eq_comm]
    obtain ⟨i, hi⟩ := h (fun i => φ (Pi.single i 1)) (by
      intro h0
      apply hφ0
      refine LinearMap.ext fun x => ?_
      rw [e, h0]
      simp)
    exact hi (by rw [← e]; exact hφ (Submodule.subset_span ⟨i, rfl⟩))
  obtain ⟨b, hb, hsp, hli⟩ := exists_linearIndependent k (Set.range v)
  let B : Module.Basis b k (Fin r → k) := Module.Basis.mk hli (by
    rw [Subtype.range_coe_subtype, Set.setOf_mem_eq, hsp, hs])
  let e : Fin r ≃ b := (Pi.basisFun k (Fin r)).indexEquiv B
  choose f hf using fun i : Fin r => hb (e i).2
  refine ⟨f, ?_⟩
  have hl : LinearIndependent k (Matrix.of fun i j => v (f i) j).row := by
    have := hli.comp e e.injective
    have e2 : (Matrix.of fun i j => v (f i) j).row = Subtype.val ∘ e := funext fun i => hf i
    rw [e2]
    exact this
  exact ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_rows_iff_isUnit.1 hl)).ne_zero

/- English proof (translation)
Establish `key : ∀ x : O, residue O x ≠ 0 ↔ O.valuation (x : F) = 1` using `fun x => by`. Rewrite using `[residue_ne_zero_iff_isUnit, O.valuation_eq_one_iff]`. Take `⟨f, hf⟩` from `exists_det_ne_zero (fun i j => residue O ⟨v i j, hv i j⟩) (by`. Introduce `a ha`. Use `choose a' ha' using fun i => residue_surjective (R := O) (a i)`.

Take `⟨i₀, hi₀⟩` from `Function.ne_iff.1 ha`. Take `⟨i, hi⟩` from `h (fun i => a' i) (fun i => (a' i).2) ⟨i₀, (key _).1 (by rw [ha']; exact hi₀)⟩`. Use `⟨i, ?_⟩` and prove the remaining obligations. Use `(key (a' ⬝ᵥ fun j => ⟨v i j, hv i j⟩)).2 (by` as an intermediate fact. Rewrite using `[← hi]`.

Use `congr 1`. Conclude with `map_sum O.subtype _ _)`. Simplify `this)` using `[dotProduct, ha']`. Use `⟨f, ?_⟩` and prove the remaining obligations. Use `(key (Matrix.of fun i j => (⟨v (f i) j, hv _ _⟩ : O)).det).1 (by` as an intermediate fact.

Rewrite using `[RingHom.map_det]`. Conclude with `hf)`. Rewrite using `[← this]`. Use `congr 1`. Conclude with `(RingHom.map_det O.subtype (Matrix.of fun i j => (⟨v (f i) j, hv _ _⟩ : O))).symm`.
-/
theorem exists_det_unit {F J : Type} [Field F] (O : ValuationSubring F) {r : ℕ} (v : J → Fin r → F)
    (hv : ∀ i j, v i j ∈ O)
    (h : ∀ a : Fin r → F, (∀ i, a i ∈ O) → (∃ i, O.valuation (a i) = 1) → ∃ i, O.valuation (a ⬝ᵥ v i) = 1) :
    ∃ f : Fin r → J, O.valuation (Matrix.of fun i j => v (f i) j).det = 1 := by
  have key : ∀ x : O, residue O x ≠ 0 ↔ O.valuation (x : F) = 1 := fun x => by
    rw [residue_ne_zero_iff_isUnit, O.valuation_eq_one_iff]
  obtain ⟨f, hf⟩ := exists_det_ne_zero (fun i j => residue O ⟨v i j, hv i j⟩) (by
    intro a ha
    choose a' ha' using fun i => residue_surjective (R := O) (a i)
    obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 ha
    obtain ⟨i, hi⟩ := h (fun i => a' i) (fun i => (a' i).2) ⟨i₀, (key _).1 (by rw [ha']; exact hi₀)⟩
    refine ⟨i, ?_⟩
    have := (key (a' ⬝ᵥ fun j => ⟨v i j, hv i j⟩)).2 (by
      rw [← hi]; congr 1
      exact map_sum O.subtype _ _)
    simpa [dotProduct, ha'] using this)
  refine ⟨f, ?_⟩
  have := (key (Matrix.of fun i j => (⟨v (f i) j, hv _ _⟩ : O)).det).1 (by
    rw [RingHom.map_det]; exact hf)
  rw [← this]
  congr 1
  exact (RingHom.map_det O.subtype (Matrix.of fun i j => (⟨v (f i) j, hv _ _⟩ : O))).symm

/- English proof (translation)
Establish `e : (Matrix.of fun i j => Matrix.vecMul (Em i) B⁻¹ j / p j) * Matrix.diagonal p = Em * B⁻¹`. Use extensionality with `i j`. Rewrite using `[Matrix.mul_diagonal, Matrix.of_apply, div_mul_cancel₀ _ (hp j)]`. Both sides reduce to the same expression. Establish `e2 : Em * M = (Matrix.of fun i j => Matrix.vecMul (Em i) B⁻¹ j / p j) * Matrix.diagonal p * (B * M)`.

Rewrite using `[e, Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ (Ne.isUnit hB)]`. Rewrite using `[e2, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem det_split {F : Type} [Field F] {r : ℕ} (B Em M : Matrix (Fin r) (Fin r) F) (p : Fin r → F) (hB : B.det ≠ 0)
    (hp : ∀ i, p i ≠ 0) :
    (Em * M).det = (∏ i, p i) * ((Matrix.of fun i j => Matrix.vecMul (Em i) B⁻¹ j / p j).det * (B * M).det) := by
  have e : (Matrix.of fun i j => Matrix.vecMul (Em i) B⁻¹ j / p j) * Matrix.diagonal p = Em * B⁻¹ := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.of_apply, div_mul_cancel₀ _ (hp j)]
    rfl
  have e2 : Em * M = (Matrix.of fun i j => Matrix.vecMul (Em i) B⁻¹ j / p j) * Matrix.diagonal p * (B * M) := by
    rw [e, Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ (Ne.isUnit hB)]
  rw [e2, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
  ring

/- English proof (translation)
Use `(h _).2 ?_ j` and prove the remaining obligations. Rewrite using `[Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (Ne.isUnit hB), Matrix.vecMul_one]`. Conclude with `Submodule.subset_span he`.
-/
theorem coord_mem {F : Type} [Field F] (O : ValuationSubring F) {r : ℕ} {B : Matrix (Fin r) (Fin r) F} {p : Fin r → F}
    {s : Set (Fin r → F)} (hB : B.det ≠ 0)
    (h : ∀ a : Fin r → F, (∀ i, a i / p i ∈ O) ↔ Matrix.vecMul a B ∈ Submodule.span O s) {e : Fin r → F} (he : e ∈ s)
    (j : Fin r) : Matrix.vecMul e B⁻¹ j / p j ∈ O := by
  refine (h _).2 ?_ j
  rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (Ne.isUnit hB), Matrix.vecMul_one]
  exact Submodule.subset_span he

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Establish `hall : ∀ x ∈ Submodule.span O s, O.valuation (a ⬝ᵥ fun j => Matrix.vecMul x B⁻¹ j / p j) < 1`. Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem e he`. Use `lt_of_le_of_ne ?_ (hne e he)` and prove the remaining obligations. Rewrite using `[O.valuation_le_one_iff]`. Conclude with `sum_mem fun j _ => mul_mem (ha j) (coord_mem O hB h he j)`. Consider the case `zero => simp [dotProduct]`.

Consider the case `add x y _ _ hx hy`. Establish `: (a ⬝ᵥ fun j => Matrix.vecMul (x + y) B⁻¹ j / p j) = (a ⬝ᵥ fun j => Matrix.vecMul x B⁻¹ j / p j) + (a ⬝ᵥ fun j => Matrix.vecMul y B⁻¹ j / p j)`. Simplify using `[dotProduct, Matrix.add_vecMul, add_div, mul_add, Finset.sum_add_distrib]`. Rewrite using `[this]`. Conclude with `Valuation.map_add_lt _ hx hy`.

Consider the case `smul c x _ hx`. Establish `: (a ⬝ᵥ fun j => Matrix.vecMul (c • x) B⁻¹ j / p j) = (c : F) * (a ⬝ᵥ fun j => Matrix.vecMul x B⁻¹ j / p j)`. Establish `: c • x = (c : F) • x` using `rfl`. Rewrite using `[this, Matrix.smul_vecMul]`. Simplify using `only [dotProduct, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]`.

Conclude with `Finset.sum_congr rfl fun j _ => by ring`. Rewrite using `[this, map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' (O.valuation_le_one c)) hx`. Take `⟨i, hi⟩` from `ha1`. Establish `h1` using `hall _ ((h (Pi.single i (p i))).1 fun j => by`.

Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using `[hp j]`. Simplify using `[hj])`. Rewrite `h1` using `[Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ (Ne.isUnit hB), Matrix.vecMul_one]`.

Establish `: (a ⬝ᵥ fun j => (Pi.single i (p i) : Fin r → F) j / p j) = a i`. Rewrite using `[dotProduct, Finset.sum_eq_single i]`. Simplify using `[hp i]`. Introduce `j _ hj`. Simplify using `[hj]`.

Simplify using the standard rewrite rules. Rewrite `h1` using `[this, hi]`. Conclude with `lt_irrefl _ h1`.
-/
theorem coord_prim {F : Type} [Field F] (O : ValuationSubring F) {r : ℕ} {B : Matrix (Fin r) (Fin r) F} {p : Fin r → F}
    {s : Set (Fin r → F)} (hB : B.det ≠ 0) (hp : ∀ i, p i ≠ 0)
    (h : ∀ a : Fin r → F, (∀ i, a i / p i ∈ O) ↔ Matrix.vecMul a B ∈ Submodule.span O s) (a : Fin r → F)
    (ha : ∀ i, a i ∈ O) (ha1 : ∃ i, O.valuation (a i) = 1) :
    ∃ e ∈ s, O.valuation (a ⬝ᵥ fun j => Matrix.vecMul e B⁻¹ j / p j) = 1 := by
  classical
  by_contra hne
  push Not at hne
  have hall : ∀ x ∈ Submodule.span O s, O.valuation (a ⬝ᵥ fun j => Matrix.vecMul x B⁻¹ j / p j) < 1 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem e he =>
      refine lt_of_le_of_ne ?_ (hne e he)
      rw [O.valuation_le_one_iff]
      exact sum_mem fun j _ => mul_mem (ha j) (coord_mem O hB h he j)
    | zero => simp [dotProduct]
    | add x y _ _ hx hy =>
      have : (a ⬝ᵥ fun j => Matrix.vecMul (x + y) B⁻¹ j / p j) =
          (a ⬝ᵥ fun j => Matrix.vecMul x B⁻¹ j / p j) + (a ⬝ᵥ fun j => Matrix.vecMul y B⁻¹ j / p j) := by
        simp [dotProduct, Matrix.add_vecMul, add_div, mul_add, Finset.sum_add_distrib]
      rw [this]
      exact Valuation.map_add_lt _ hx hy
    | smul c x _ hx =>
      have : (a ⬝ᵥ fun j => Matrix.vecMul (c • x) B⁻¹ j / p j) =
          (c : F) * (a ⬝ᵥ fun j => Matrix.vecMul x B⁻¹ j / p j) := by
        have : c • x = (c : F) • x := rfl
        rw [this, Matrix.smul_vecMul]
        simp only [dotProduct, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [this, map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' (O.valuation_le_one c)) hx
  obtain ⟨i, hi⟩ := ha1
  have h1 := hall _ ((h (Pi.single i (p i))).1 fun j => by
    by_cases hj : j = i
    · subst hj; simp [hp j]
    · simp [hj])
  rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ (Ne.isUnit hB), Matrix.vecMul_one] at h1
  have : (a ⬝ᵥ fun j => (Pi.single i (p i) : Fin r → F) j / p j) = a i := by
    rw [dotProduct, Finset.sum_eq_single i]
    · simp [hp i]
    · intro j _ hj; simp [hj]
    · simp
  rw [this, hi] at h1
  exact lt_irrefl _ h1

def torsHs {K : Type} [Field K] {r : ℕ} (T : Tab K r) (O : ValuationSubring K) (k : ℕ) : Subgroup T.Pt :=
  Subgroup.closure {y | ∃ x c, T.C k x c ∧ x ^ (k ^ 2) = 1 ∧ O.valuation c = 1 ∧ y = x ^ k}

/- English proof (translation)
Establish `: torsHs T O k ≤ (powMonoidHom k : T.Pt →* T.Pt).ker`. Use `(Subgroup.closure_le _).2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, c, -, hx, -, rfl⟩`. Express the relevant statement in the definitionally equal form `(x ^ k) ^ k = 1`. Rewrite using `[← pow_mul, ← sq, hx]`.

Conclude with `this hh`.
-/
theorem torsHs_pow {K : Type} [Field K] {r : ℕ} (T : Tab K r) (O : ValuationSubring K) (k : ℕ) {h : T.Pt}
    (hh : h ∈ torsHs T O k) : h ^ k = 1 := by
  have : torsHs T O k ≤ (powMonoidHom k : T.Pt →* T.Pt).ker := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨x, c, -, hx, -, rfl⟩
    change (x ^ k) ^ k = 1
    rw [← pow_mul, ← sq, hx]
  exact this hh

/- English proof (translation)
Introduce `K _ r T N n d κ P S₀ hN hn hd hS₀ hF hP hU`. Establish `hC : ∀ j x c, T.C (n ^ j) x c → S₀.valuation c = 1 → ∀ S ∈ P, S.valuation c = 1`. Introduce `j x c hc h1`. Use `hU c (fun S hS => ?_) h1` and prove the remaining obligations. Take `⟨K', _, σ, O, T', B, rfl, ⟨β, -, -, hβ, -⟩, -, -, hL, -⟩` from `hP S hS`.

Conclude with `hL j _ _ (hβ _ _ _ hc)`. Establish `hI : ∀ (K' : Type) [Field K'] (σ : K →+* K') (O : ValuationSubring K') (T' : Tab K' r) (B : Matrix (Fin r) (Fin r) K'), O.comap σ ∈ P → T.Near N n d κ σ O T' B → ∀ j h l, h ∈ torsHs T S₀ (n ^ j) → T.Λ (n ^ j) h l → ∀ i, B.mulVec (σ ∘ l) i ∈ O`. Introduce and unpack `K' _ σ O T' B hO ⟨⟨β, -, -, hβ, hΛ⟩, -, -, -, hL, -⟩ j h l hh hl`. Use `hL j (β h) _ ?_ (hΛ _ _ _ hl)` and prove the remaining obligations. Establish `: torsHs T S₀ (n ^ j) ≤ (T'.Hs O (n ^ j)).comap β`.

Use `(Subgroup.closure_le _).2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, c, hc, -, h1, rfl⟩`. Conclude with `Subgroup.subset_closure ⟨β x, σ c, hβ _ _ _ hc, (val_comap σ O c).1 (hC j x c hc h1 _ hO), map_pow _ _ _⟩`. Conclude with `this hh`. Take `⟨K₀, _, σ₀, O₀, T₀, B₀, hO₀, hN₀⟩` from `hP S₀ hS₀`.

Establish `hI₀` using `hI K₀ σ₀ O₀ T₀ B₀ (hO₀ ▸ hS₀) hN₀`. Take `⟨⟨β, hβo, hβE, hβC, hβΛ⟩, ⟨hqE, hqC⟩, hB₀, -, -, hprim, p₀, hp₀, hκ₀, hsp₀⟩` from `hN₀`. Establish `hH : ∀ j, T₀.Hs O₀ (n ^ j) ≤ (torsHs T S₀ (n ^ j)).map β`. Introduce `j`. Use `(Subgroup.closure_le _).2 ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨x', c', hc', h1, rfl⟩`. Take `⟨x, hx, rfl⟩` from `hβo _ x' (Nat.one_le_pow _ _ (Nat.one_le_pow _ _ hn)) (hqC j _ _ hc').1`. Take `⟨c, hc⟩` from `hF.2.1 j x hx`. Take `rfl` from `(hqC j _ _ hc').2 _ (hβC _ _ _ hc)`. Conclude with `⟨x ^ n ^ j, Subgroup.subset_closure ⟨x, c, hc, hx, hO₀ ▸ (val_comap σ₀ O₀ c).2 h1, rfl⟩, map_pow _ _ _⟩`.

Take `⟨f, hf⟩` from `exists_det_unit (J := {l : Fin r → K // ∃ j h, h ∈ torsHs T S₀ (n ^ j) ∧ T.Λ (n ^ j) h l}) O₀ (fun l => B₀.mulVec (σ₀ ∘ l.1)) (fun ⟨l, j, h, hh, hl⟩ => hI₀ j h l hh hl) (by`. Introduce `a ha ha1`. Take `⟨j, h', hh', hv⟩` from `hprim a ha ha1`. Take `⟨h, hh, rfl⟩` from `hH j hh'`. Take `⟨l, hl⟩` from `hF.2.2 j h (torsHs_pow T S₀ _ hh)`.

Conclude with `⟨⟨l, j, h, hh, hl⟩, hv _ (hβΛ _ _ _ hl)⟩)`. Take `⟨g, hg⟩` from `exists_det_unit (J := {e : Fin r → K // ∃ x, T.E x e}) O₀ (fun e j => Matrix.vecMul (σ₀ ∘ e.1) B₀⁻¹ j / p₀ j) (fun ⟨e, x, he⟩ => coord_mem O₀ hB₀ hsp₀ ⟨β x, hβE _ _ he⟩) (by`. Introduce `a ha ha1`. Take `⟨e', ⟨x', he'⟩, hv⟩` from `coord_prim O₀ hB₀ hp₀ hsp₀ a ha ha1`. Take `⟨x, hx, rfl⟩` from `hβo _ x' hN (hqE _ _ he').1`.

Take `⟨e, he⟩` from `hF.1 x hx`. Take `rfl` from `(hqE _ _ he').2 _ (hβE _ _ he)`. Conclude with `⟨⟨e, x, he⟩, hv⟩)`. Set `M : Matrix (Fin r) (Fin r) K` to `Matrix.of fun i j => (f j).1 i`. Set `Em : Matrix (Fin r) (Fin r) K` to `Matrix.of fun i j => (g i).1 j`.

Establish `hM₀ : O₀.valuation (B₀ * M.map σ₀).det = 1`. Rewrite using `[← Matrix.det_transpose]`. Conclude with `hf`. Establish `hval : ∀ (K' : Type) [Field K'] (σ : K →+* K') (O : ValuationSubring K') (B : Matrix (Fin r) (Fin r) K') (p : Fin r → K'), B.det ≠ 0 → (∀ i, p i ≠ 0) → O.valuation ((∏ i, p i) ^ d) = O.valuation (σ κ) → O.valuation (σ ((Em * M).det ^ d / κ)) = (O.valuation (Matrix.of fun i j => M …`. Introduce `K' _ σ O B p hB hp hκ`.

Establish `h0 : O.valuation ((∏ i, p i) ^ d) ≠ 0`. Rewrite using `[Valuation.ne_zero_iff]`. Conclude with `pow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun i _ => hp i)`. Rewrite using `[map_div₀, map_pow, RingHom.map_det, map_mul, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, det_split B _ _ p hB hp, map_div₀, ← hκ, mul_pow, map_mul, mul_div_cancel_left₀ _ h0, map_pow, map_mul]`. Both sides reduce to the same expression.

Establish `hle : ∀ (K' : Type) [Field K'] (σ : K →+* K') (O : ValuationSubring K') (T' : Tab K' r) (B : Matrix (Fin r) (Fin r) K'), O.comap σ ∈ P → T.Near N n d κ σ O T' B → (∀ i j, (B * M.map σ) i j ∈ O) ∧ ∃ w, w ≤ 1 ∧ O.valuation (σ ((Em * M).det ^ d / κ)) = (w * O.valuation (B * M.map σ) …`. Introduce `K' _ σ O T' B hO hN'`. Use `⟨fun i j => ?_, ?_⟩` and prove the remaining obligations. Take `⟨k, h, hh, hl⟩` from `(f j).2`. Conclude with `hI K' σ O T' B hO hN' k h _ hh hl i`.

Take `⟨⟨β', -, hE', -⟩, -, hB, -, -, -, p, hp, hκ, hsp⟩` from `hN'`. Use `⟨_, det_mem O _ fun i j => ?_, hval K' σ O B p hB hp hκ⟩` and prove the remaining obligations. Take `⟨x, hx⟩` from `(g i).2`. Conclude with `coord_mem O hB hsp ⟨β' x, hE' _ _ hx⟩ j`. Establish `hall` using `hU ((Em * M).det ^ d / κ) (fun S hS => by`.

Take `⟨K', _, σ, O, T', B, rfl, hN'⟩` from `hP S hS`. Take `⟨h1, w, hw, h2⟩` from `hle K' σ O T' B hS hN'`. Rewrite using `[ValuationSubring.mem_comap, ← O.valuation_le_one_iff, h2]`. Conclude with `pow_le_one' (mul_le_one' hw (det_mem O _ h1)) _) (by`. Rewrite using `[← hO₀, val_comap, hval K₀ σ₀ O₀ B₀ p₀ hB₀ hp₀ hκ₀, hM₀, hg]`.

Use the proof step `simp)`. Establish `hMdet : M.det ≠ 0`. Introduce `h0`. Rewrite `hM₀` using `[Matrix.det_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0]`. Simplify using `at hM₀`.

Use `⟨M⁻¹, fun K' _ σ O T' B hO hN' => ?_⟩` and prove the remaining obligations. Take `⟨h1, w, hw, h2⟩` from `hle K' σ O T' B hO hN'`. Rewrite `h2` using `[(val_comap σ O _).1 (hall _ hO)]`. Establish `h3 : O.valuation (B * M.map σ).det = 1`. Use `le_antisymm (det_mem O _ h1) (not_lt.1 fun hlt => ?_)` and prove the remaining obligations.

Conclude with `(pow_lt_one' (lt_of_le_of_lt (mul_le_of_le_one_left' hw) hlt) (by omega : d ≠ 0)).ne' h2`. Take `⟨A, hA⟩` from `exists_lift O _ h1`. Establish `hAu : IsUnit A.det`. Rewrite using `[O.valuation_eq_one_iff, ← h3, ← hA]`. Use `congr 1`.

Conclude with `RingHom.map_det O.subtype A`. Use `⟨A⁻¹, Matrix.isUnit_nonsing_inv_det _ hAu, ?_⟩` and prove the remaining obligations. Use `Matrix.left_inv_eq_left_inv (A := M.map σ) ?_ ?_` and prove the remaining obligations. Rewrite using `[← Matrix.map_mul, Matrix.nonsing_inv_mul _ (Ne.isUnit hMdet), Matrix.map_one _ (map_zero σ) (map_one σ)]`. Rewrite using `[Matrix.mul_assoc, ← hA, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hAu, Matrix.map_one _ (map_zero _) (map_one _)]`.
-/
theorem exists_basis_all_places : ∀ (K : Type) [Field K] (r : ℕ) (T : Tab K r) (N n d : ℕ) (κ : K) (P : Set (ValuationSubring K)) (S₀ : ValuationSubring K), 1 ≤ N → 1 ≤ n → 1 ≤ d → S₀ ∈ P → T.Full N n → (∀ S ∈ P, ∃ (K' : Type) (_ : Field K') (σ : K →+* K') (O : ValuationSubring K') (T' : Tab K' r) (B : Matrix (Fin r) (Fin r) K'), O.comap σ = S ∧ T.Near N n d κ σ O T' B) → (∀ x : K, (∀ S ∈ P, x ∈ S) → S₀.valuation x = 1 → ∀ S ∈ P, S.valuation x = 1) → ∃ Φ : Matrix (Fin r) (Fin r) K, ∀ (K' : Type) [Field K'] (σ : K →+* K') (O : ValuationSubring K') (T' : Tab K' r) (B : Matrix (Fin r) (Fin r) K'), O.comap σ ∈ P → T.Near N n d κ σ O T' B → ∃ U : Matrix (Fin r) (Fin r) O, IsUnit U.det ∧ Φ.map σ = U.map O.subtype * B := by
  intro K _ r T N n d κ P S₀ hN hn hd hS₀ hF hP hU
  classical

  have hC : ∀ j x c, T.C (n ^ j) x c → S₀.valuation c = 1 → ∀ S ∈ P, S.valuation c = 1 := by
    intro j x c hc h1
    refine hU c (fun S hS => ?_) h1
    obtain ⟨K', _, σ, O, T', B, rfl, ⟨β, -, -, hβ, -⟩, -, -, hL, -⟩ := hP S hS
    exact hL j _ _ (hβ _ _ _ hc)

  have hI : ∀ (K' : Type) [Field K'] (σ : K →+* K') (O : ValuationSubring K') (T' : Tab K' r)
      (B : Matrix (Fin r) (Fin r) K'), O.comap σ ∈ P → T.Near N n d κ σ O T' B →
      ∀ j h l, h ∈ torsHs T S₀ (n ^ j) → T.Λ (n ^ j) h l → ∀ i, B.mulVec (σ ∘ l) i ∈ O := by
    rintro K' _ σ O T' B hO ⟨⟨β, -, -, hβ, hΛ⟩, -, -, -, hL, -⟩ j h l hh hl
    refine hL j (β h) _ ?_ (hΛ _ _ _ hl)
    have : torsHs T S₀ (n ^ j) ≤ (T'.Hs O (n ^ j)).comap β := by
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨x, c, hc, -, h1, rfl⟩
      exact Subgroup.subset_closure ⟨β x, σ c, hβ _ _ _ hc, (val_comap σ O c).1 (hC j x c hc h1 _ hO), map_pow _ _ _⟩
    exact this hh
  obtain ⟨K₀, _, σ₀, O₀, T₀, B₀, hO₀, hN₀⟩ := hP S₀ hS₀
  have hI₀ := hI K₀ σ₀ O₀ T₀ B₀ (hO₀ ▸ hS₀) hN₀
  obtain ⟨⟨β, hβo, hβE, hβC, hβΛ⟩, ⟨hqE, hqC⟩, hB₀, -, -, hprim, p₀, hp₀, hκ₀, hsp₀⟩ := hN₀
  have hH : ∀ j, T₀.Hs O₀ (n ^ j) ≤ (torsHs T S₀ (n ^ j)).map β := by
    intro j
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨x', c', hc', h1, rfl⟩
    obtain ⟨x, hx, rfl⟩ := hβo _ x' (Nat.one_le_pow _ _ (Nat.one_le_pow _ _ hn)) (hqC j _ _ hc').1
    obtain ⟨c, hc⟩ := hF.2.1 j x hx
    obtain rfl := (hqC j _ _ hc').2 _ (hβC _ _ _ hc)
    exact ⟨x ^ n ^ j, Subgroup.subset_closure ⟨x, c, hc, hx, hO₀ ▸ (val_comap σ₀ O₀ c).2 h1, rfl⟩, map_pow _ _ _⟩
  obtain ⟨f, hf⟩ := exists_det_unit (J := {l : Fin r → K // ∃ j h, h ∈ torsHs T S₀ (n ^ j) ∧ T.Λ (n ^ j) h l}) O₀
    (fun l => B₀.mulVec (σ₀ ∘ l.1)) (fun ⟨l, j, h, hh, hl⟩ => hI₀ j h l hh hl) (by
      intro a ha ha1
      obtain ⟨j, h', hh', hv⟩ := hprim a ha ha1
      obtain ⟨h, hh, rfl⟩ := hH j hh'
      obtain ⟨l, hl⟩ := hF.2.2 j h (torsHs_pow T S₀ _ hh)
      exact ⟨⟨l, j, h, hh, hl⟩, hv _ (hβΛ _ _ _ hl)⟩)
  obtain ⟨g, hg⟩ := exists_det_unit (J := {e : Fin r → K // ∃ x, T.E x e}) O₀
    (fun e j => Matrix.vecMul (σ₀ ∘ e.1) B₀⁻¹ j / p₀ j)
    (fun ⟨e, x, he⟩ => coord_mem O₀ hB₀ hsp₀ ⟨β x, hβE _ _ he⟩) (by
      intro a ha ha1
      obtain ⟨e', ⟨x', he'⟩, hv⟩ := coord_prim O₀ hB₀ hp₀ hsp₀ a ha ha1
      obtain ⟨x, hx, rfl⟩ := hβo _ x' hN (hqE _ _ he').1
      obtain ⟨e, he⟩ := hF.1 x hx
      obtain rfl := (hqE _ _ he').2 _ (hβE _ _ he)
      exact ⟨⟨e, x, he⟩, hv⟩)
  let M : Matrix (Fin r) (Fin r) K := Matrix.of fun i j => (f j).1 i
  let Em : Matrix (Fin r) (Fin r) K := Matrix.of fun i j => (g i).1 j
  have hM₀ : O₀.valuation (B₀ * M.map σ₀).det = 1 := by
    rw [← Matrix.det_transpose]
    exact hf

  have hval : ∀ (K' : Type) [Field K'] (σ : K →+* K') (O : ValuationSubring K') (B : Matrix (Fin r) (Fin r) K')
      (p : Fin r → K'), B.det ≠ 0 → (∀ i, p i ≠ 0) → O.valuation ((∏ i, p i) ^ d) = O.valuation (σ κ) →
      O.valuation (σ ((Em * M).det ^ d / κ)) =
        (O.valuation (Matrix.of fun i j => Matrix.vecMul (σ ∘ (g i).1) B⁻¹ j / p j).det *
          O.valuation (B * M.map σ).det) ^ d := by
    intro K' _ σ O B p hB hp hκ
    have h0 : O.valuation ((∏ i, p i) ^ d) ≠ 0 := by
      rw [Valuation.ne_zero_iff]
      exact pow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun i _ => hp i)
    rw [map_div₀, map_pow, RingHom.map_det, map_mul, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply,
      det_split B _ _ p hB hp, map_div₀, ← hκ, mul_pow, map_mul, mul_div_cancel_left₀ _ h0, map_pow, map_mul]
    rfl
  have hle : ∀ (K' : Type) [Field K'] (σ : K →+* K') (O : ValuationSubring K') (T' : Tab K' r)
      (B : Matrix (Fin r) (Fin r) K'), O.comap σ ∈ P → T.Near N n d κ σ O T' B →
      (∀ i j, (B * M.map σ) i j ∈ O) ∧ ∃ w, w ≤ 1 ∧
        O.valuation (σ ((Em * M).det ^ d / κ)) = (w * O.valuation (B * M.map σ).det) ^ d := by
    intro K' _ σ O T' B hO hN'
    refine ⟨fun i j => ?_, ?_⟩
    · obtain ⟨k, h, hh, hl⟩ := (f j).2
      exact hI K' σ O T' B hO hN' k h _ hh hl i
    · obtain ⟨⟨β', -, hE', -⟩, -, hB, -, -, -, p, hp, hκ, hsp⟩ := hN'
      refine ⟨_, det_mem O _ fun i j => ?_, hval K' σ O B p hB hp hκ⟩
      obtain ⟨x, hx⟩ := (g i).2
      exact coord_mem O hB hsp ⟨β' x, hE' _ _ hx⟩ j
  have hall := hU ((Em * M).det ^ d / κ) (fun S hS => by
      obtain ⟨K', _, σ, O, T', B, rfl, hN'⟩ := hP S hS
      obtain ⟨h1, w, hw, h2⟩ := hle K' σ O T' B hS hN'
      rw [ValuationSubring.mem_comap, ← O.valuation_le_one_iff, h2]
      exact pow_le_one' (mul_le_one' hw (det_mem O _ h1)) _) (by
      rw [← hO₀, val_comap, hval K₀ σ₀ O₀ B₀ p₀ hB₀ hp₀ hκ₀, hM₀, hg]
      simp)
  have hMdet : M.det ≠ 0 := by
    intro h0
    rw [Matrix.det_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0] at hM₀
    simp at hM₀
  refine ⟨M⁻¹, fun K' _ σ O T' B hO hN' => ?_⟩
  obtain ⟨h1, w, hw, h2⟩ := hle K' σ O T' B hO hN'
  rw [(val_comap σ O _).1 (hall _ hO)] at h2
  have h3 : O.valuation (B * M.map σ).det = 1 := by
    refine le_antisymm (det_mem O _ h1) (not_lt.1 fun hlt => ?_)
    exact (pow_lt_one' (lt_of_le_of_lt (mul_le_of_le_one_left' hw) hlt) (by omega : d ≠ 0)).ne' h2
  obtain ⟨A, hA⟩ := exists_lift O _ h1
  have hAu : IsUnit A.det := by
    rw [O.valuation_eq_one_iff, ← h3, ← hA]
    congr 1
    exact RingHom.map_det O.subtype A
  refine ⟨A⁻¹, Matrix.isUnit_nonsing_inv_det _ hAu, ?_⟩
  refine Matrix.left_inv_eq_left_inv (A := M.map σ) ?_ ?_
  · rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (Ne.isUnit hMdet), Matrix.map_one _ (map_zero σ) (map_one σ)]
  · rw [Matrix.mul_assoc, ← hA, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hAu,
      Matrix.map_one _ (map_zero _) (map_one _)]

end GlobalTheory.OneBasis.Places
