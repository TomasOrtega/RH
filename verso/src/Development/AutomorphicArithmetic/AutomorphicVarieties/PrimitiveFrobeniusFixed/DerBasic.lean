import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.GalBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PlaceBasic

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

section
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

/- English proof (translation)
Unfold `der1`. Conclude with `Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ ((map_ne_zero _).2 hu)`.
-/
private theorem derivation_ne_zero (q : ℕ) (t : G ℚ Ω) {u : Ω} (hu : u ≠ 0) : der1 q t u ≠ 0 := by
  unfold der1
  exact Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ ((map_ne_zero _).2 hu)

/- English proof (translation)
Unfold `der1`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, mul_pow]`.
-/
private theorem derivation_mul (q : ℕ) (t : G ℚ Ω) (u v : Ω) : der1 q t (u * v) = der1 q t u * der1 q t v := by
  unfold der1
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_mul, mul_pow]

/- English proof (translation)
Unfold `der1`. Rewrite using `[← Finset.prod_zpow]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_zpow₀, ← zpow_natCast ((t ^ i) u ^ k) i, ← zpow_natCast ((t ^ i) u) i, ← zpow_mul, ← zpow_mul, mul_comm]`.
-/
private theorem derivation_zpow (q : ℕ) (t : G ℚ Ω) (u : Ω) (k : ℤ) : der1 q t (u ^ k) = der1 q t u ^ k := by
  unfold der1
  rw [← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_zpow₀, ← zpow_natCast ((t ^ i) u ^ k) i, ← zpow_natCast ((t ^ i) u) i, ← zpow_mul, ← zpow_mul,
    mul_comm]

/- English proof (translation)
Unfold `der1`. Rewrite using `[map_prod]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_pow, h]`.
-/
private theorem derivation_galois_equivariant (q : ℕ) (t g : G ℚ Ω) (u : Ω) (h : ∀ s : G ℚ Ω, g (s u) = s (g u)) :
    g (der1 q t u) = der1 q t (g u) := by
  unfold der1
  rw [map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_pow, h]

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil => simp only [der.eq_1]`. Consider the case `cons q L ih => rw [der.eq_2, der.eq_2, der.eq_2, ih, derivation_mul]`.
-/
private theorem der_mul (τ : ℕ → G ℚ Ω) (L : List ℕ) (u v : Ω) : der τ L (u * v) = der τ L u * der τ L v := by
  induction L with
  | nil => simp only [der.eq_1]
  | cons q L ih => rw [der.eq_2, der.eq_2, der.eq_2, ih, derivation_mul]

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil => rw [der.eq_1]`. Consider the case `cons q L ih`. Rewrite using `[der.eq_2, ih]`. Unfold `der1`.

Simplify using the standard rewrite rules.
-/
private theorem der_one (τ : ℕ → G ℚ Ω) (L : List ℕ) : der τ L (1 : Ω) = 1 := by
  induction L with
  | nil => rw [der.eq_1]
  | cons q L ih =>
    rw [der.eq_2, ih]
    unfold der1
    simp

private def derHom (τ : ℕ → G ℚ Ω) (L : List ℕ) : Ω →* Ω where
  toFun := der τ L
  map_one' := der_one τ L
  map_mul' := der_mul τ L

/- English proof (translation)
Establish `key : ∀ (a : ℕ → Ω) (n : ℕ), (∏ i ∈ Finset.range n, a (i + 1) ^ i) * (∏ i ∈ Finset.range n, a i) * a n = a 0 * a n ^ n * ∏ i ∈ Finset.range n, a i ^ i`. Introduce `a n`. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`.

Rewrite using `[Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ]`. Combine the equalities or inequalities in the displayed calculation. Establish `hD : der1 q t u ≠ 0` using `derivation_ne_zero q t hu`. Establish `hN : nrm q t u ≠ 0`. Unfold `nrm`.

Conclude with `Finset.prod_ne_zero_iff.mpr fun i _ => (map_ne_zero _).mpr hu`. Establish `htD : t (der1 q t u) = ∏ i ∈ Finset.range (q - 1), ((t ^ (i + 1)) u) ^ i`. Unfold `der1`. Rewrite using `[map_prod]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[map_pow, pow_succ', AlgEquiv.mul_apply]`. Establish `hk` using `key (fun i => (t ^ i) u) (q - 1)`. Simplify using `only [pow_zero, AlgEquiv.one_apply, h] at hk`. Rewrite using `[div_eq_div_iff hD hN, htD]`. Establish `hD' : der1 q t u = ∏ i ∈ Finset.range (q - 1), ((t ^ i) u) ^ i` using `rfl`.

Establish `hN' : nrm q t u = ∏ i ∈ Finset.range (q - 1), (t ^ i) u` using `rfl`. Rewrite using `[hD', hN']`. Apply `mul_right_cancel₀ hu` to reduce the goal to its premises. Take the linear combination `hk`.
-/
private theorem tele (q : ℕ) (t : G ℚ Ω) (u : Ω) (hu : u ≠ 0) (h : (t ^ (q - 1)) u = u) :
    t (der1 q t u) / der1 q t u = u ^ (q - 1) / nrm q t u := by
  have key : ∀ (a : ℕ → Ω) (n : ℕ),
      (∏ i ∈ Finset.range n, a (i + 1) ^ i) * (∏ i ∈ Finset.range n, a i) * a n =
        a 0 * a n ^ n * ∏ i ∈ Finset.range n, a i ^ i := by
    intro a n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ]
      calc (∏ i ∈ Finset.range n, a (i + 1) ^ i) * a (n + 1) ^ n * ((∏ i ∈ Finset.range n, a i) * a n) * a (n + 1)
          = ((∏ i ∈ Finset.range n, a (i + 1) ^ i) * (∏ i ∈ Finset.range n, a i) * a n) * a (n + 1) ^ (n + 1) := by ring
        _ = a 0 * a n ^ n * (∏ i ∈ Finset.range n, a i ^ i) * a (n + 1) ^ (n + 1) := by rw [ih]
        _ = a 0 * a (n + 1) ^ (n + 1) * ((∏ i ∈ Finset.range n, a i ^ i) * a n ^ n) := by ring
  have hD : der1 q t u ≠ 0 := derivation_ne_zero q t hu
  have hN : nrm q t u ≠ 0 := by
    unfold nrm
    exact Finset.prod_ne_zero_iff.mpr fun i _ => (map_ne_zero _).mpr hu
  have htD : t (der1 q t u) = ∏ i ∈ Finset.range (q - 1), ((t ^ (i + 1)) u) ^ i := by
    unfold der1
    rw [map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_pow, pow_succ', AlgEquiv.mul_apply]
  have hk := key (fun i => (t ^ i) u) (q - 1)
  simp only [pow_zero, AlgEquiv.one_apply, h] at hk
  rw [div_eq_div_iff hD hN, htD]
  have hD' : der1 q t u = ∏ i ∈ Finset.range (q - 1), ((t ^ i) u) ^ i := rfl
  have hN' : nrm q t u = ∏ i ∈ Finset.range (q - 1), (t ^ i) u := rfl
  rw [hD', hN']
  apply mul_right_cancel₀ hu
  linear_combination hk

end

/- English proof (translation)
Introduce `Ω _ _ _ N r hN τ L u hu hfix`. Take `⟨-, -, -, -, -, hcomm, -, -, -, -⟩` from `galBasic Ω N hN`. Establish `hfix1 : ∀ (q : ℕ) (t : G ℚ Ω) (x : Ω), (∀ g ∈ fixMu ℚ Ω N, g x = x) → ∀ g ∈ fixMu ℚ Ω N, g (der1 q t x) = der1 q t x`. Introduce `q t x hx g hg`. Rewrite using `[derivation_galois_equivariant q t g x (fun s => hcomm x hx g s), hx g hg]`.

Establish `hfixL : ∀ (L : List ℕ) (x : Ω), (∀ g ∈ fixMu ℚ Ω N, g x = x) → ∀ g ∈ fixMu ℚ Ω N, g (der τ L x) = der τ L x`. Introduce `L x hx`. Proceed by induction on `L with`. Consider the case `nil => simpa only [der.eq_1] using hx`. Consider the case `cons q L ih`.

Rewrite using `[der.eq_2]`. Conclude with `hfix1 q (τ q) _ ih`. Establish `hneL : ∀ L : List ℕ, der τ L u ≠ 0`. Introduce `L`. Proceed by induction on `L with`.

Consider the case `nil`. Rewrite using `[der.eq_1]`. Conclude with `hu`. Consider the case `cons q L ih`. Rewrite using `[der.eq_2]`.

Conclude with `derivation_ne_zero q (τ q) ih`. Establish `hcommL : ∀ (L : List ℕ) (x : Ω), (∀ g ∈ fixMu ℚ Ω N, g x = x) → ∀ g : G ℚ Ω, g (der τ L x) = der τ L (g x)`. Introduce `L x hx g`. Proceed by induction on `L with`. Consider the case `nil => simp only [der.eq_1]`.

Consider the case `cons q L ih`. Rewrite using `[der.eq_2, der.eq_2, derivation_galois_equivariant q (τ q) g _ (fun s => hcomm _ (hfixL L x hx) g s), ih]`. Establish `hder1 : ∀ (L : List ℕ) (x : Ω), (∀ g ∈ fixMu ℚ Ω N, g x = x) → ∀ (q : ℕ) (t : G ℚ Ω), der τ L (der1 q t x) = der1 q t (der τ L x)`. Introduce `L x hx q t`. Establish `e : der τ L (der1 q t x) = derHom τ L (der1 q t x)` using `rfl`.

Rewrite using `[e]`. Unfold `der1`. Rewrite using `[map_prod]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_pow]`.

Use `show der τ L ((t ^ i) x) ^ i = _`. Rewrite using `[← hcommL L x hx]`. Establish `hconj : ∀ x : Ω, (∀ A : ValuationSubring Ω, ¬ Over A r → A.valuation x = 1) → ∀ (s : G ℚ Ω) (A : ValuationSubring Ω), ¬ Over A r → A.valuation (s x) = 1`. Introduce `x hx s A hA`. Take `⟨-, -, -, hlt, heq⟩` from `(placeBasic Ω).2.2.2.2.2.2.2.2.2 (s⁻¹ • A) s`.

Establish `hsA : s • (s⁻¹ • A) = A` using `smul_inv_smul s A`. Rewrite `hlt`, `heq` using `[hsA]`. Apply `(heq x).mpr` to reduce the goal to its premises. Apply `hx` to reduce the goal to its premises. Introduce `hB`.

Apply `hA` to reduce the goal to its premises. Establish `hr` using `(hlt (r : Ω)).mpr hB`. Use `show A.valuation (r : Ω) < 1`. Simplify using `using hr`. Establish `hvalL : (∀ A : ValuationSubring Ω, ¬ Over A r → A.valuation u = 1) → ∀ (L : List ℕ) (A : ValuationSubring Ω), ¬ Over A r → A.valuation (der τ L u) = 1`.

Introduce `hu1 L`. Proceed by induction on `L with`. Consider the case `nil => simpa only [der.eq_1] using hu1`. Consider the case `cons q L ih`. Introduce `A hA`.

Rewrite using `[der.eq_2]`. Unfold `der1`. Rewrite using `[map_prod]`. Apply `Finset.prod_eq_one` to reduce the goal to its premises. Introduce `i _`.

Rewrite using `[Valuation.map_pow, hconj _ ih _ A hA, one_pow]`. Establish `hzpowL : ∀ (L : List ℕ) (k : ℤ), der τ L (u ^ k) = der τ L u ^ k`. Introduce `L k`. Proceed by induction on `L with`. Consider the case `nil => simp only [der.eq_1]`.

Consider the case `cons q L ih => rw [der.eq_2, der.eq_2, ih, derivation_zpow]`. Establish `hperm : ∀ L' : List ℕ, L.Perm L' → der τ L u = der τ L' u`. Introduce `L' hp`. Proceed by induction on `hp with`. Consider the case `nil => rfl`.

Consider the case `cons q _ ih => rw [der.eq_2, der.eq_2, ih]`. Consider the case `swap a b l`. Rewrite using `[der.eq_2, der.eq_2, der.eq_2, der.eq_2]`. Establish `hx` using `hfixL l u hfix`. Establish `h1 : der1 b (τ b) (der1 a (τ a) (der τ l u)) = der τ [b] (der1 a (τ a) (der τ l u))`.

Rewrite using `[der.eq_2, der.eq_1]`. Rewrite using `[h1, hder1 [b] _ hx, der.eq_2, der.eq_1]`. Consider the case `trans _ _ ih1 ih2 => exact ih1.trans ih2`. Conclude with `⟨hneL L, hfixL L u hfix, fun g => hcommL L u hfix g, fun h => hvalL h L, der_mul τ L u, hzpowL L, fun q => hder1 L u hfix q (τ q), hperm, fun q _ h => tele q (τ q) u hu h⟩`.
-/
theorem UpperTheory.V.ML.derBasic :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (N r : ℕ), N ≠ 0 → ∀ (τ : ℕ → G ℚ Ω) (L : List ℕ) (u : Ω), u ≠ 0 → (∀ g ∈ fixMu ℚ Ω N, g u = u) →
    der τ L u ≠ 0 ∧ (∀ g ∈ fixMu ℚ Ω N, g (der τ L u) = der τ L u) ∧ (∀ g : G ℚ Ω, g (der τ L u) = der τ L (g u)) ∧
    ((∀ A : ValuationSubring Ω, ¬ Over A r → A.valuation u = 1) → ∀ A : ValuationSubring Ω, ¬ Over A r → A.valuation (der τ L u) = 1) ∧
    (∀ v : Ω, der τ L (u * v) = der τ L u * der τ L v) ∧ (∀ k : ℤ, der τ L (u ^ k) = der τ L u ^ k) ∧
    (∀ q, der τ L (der1 q (τ q) u) = der1 q (τ q) (der τ L u)) ∧ (∀ L', L.Perm L' → der τ L u = der τ L' u) ∧
    ∀ q : ℕ, 1 ≤ q → (τ q ^ (q - 1)) u = u → τ q (der1 q (τ q) u) / der1 q (τ q) u = u ^ (q - 1) / nrm q (τ q) u := by
  intro Ω _ _ _ N r hN τ L u hu hfix
  obtain ⟨-, -, -, -, -, hcomm, -, -, -, -⟩ := galBasic Ω N hN
  have hfix1 : ∀ (q : ℕ) (t : G ℚ Ω) (x : Ω), (∀ g ∈ fixMu ℚ Ω N, g x = x) →
      ∀ g ∈ fixMu ℚ Ω N, g (der1 q t x) = der1 q t x := by
    intro q t x hx g hg
    rw [derivation_galois_equivariant q t g x (fun s => hcomm x hx g s), hx g hg]
  have hfixL : ∀ (L : List ℕ) (x : Ω), (∀ g ∈ fixMu ℚ Ω N, g x = x) →
      ∀ g ∈ fixMu ℚ Ω N, g (der τ L x) = der τ L x := by
    intro L x hx
    induction L with
    | nil => simpa only [der.eq_1] using hx
    | cons q L ih =>
      rw [der.eq_2]
      exact hfix1 q (τ q) _ ih
  have hneL : ∀ L : List ℕ, der τ L u ≠ 0 := by
    intro L
    induction L with
    | nil =>
      rw [der.eq_1]
      exact hu
    | cons q L ih =>
      rw [der.eq_2]
      exact derivation_ne_zero q (τ q) ih
  have hcommL : ∀ (L : List ℕ) (x : Ω), (∀ g ∈ fixMu ℚ Ω N, g x = x) →
      ∀ g : G ℚ Ω, g (der τ L x) = der τ L (g x) := by
    intro L x hx g
    induction L with
    | nil => simp only [der.eq_1]
    | cons q L ih =>
      rw [der.eq_2, der.eq_2, derivation_galois_equivariant q (τ q) g _ (fun s => hcomm _ (hfixL L x hx) g s), ih]
  have hder1 : ∀ (L : List ℕ) (x : Ω), (∀ g ∈ fixMu ℚ Ω N, g x = x) →
      ∀ (q : ℕ) (t : G ℚ Ω), der τ L (der1 q t x) = der1 q t (der τ L x) := by
    intro L x hx q t
    have e : der τ L (der1 q t x) = derHom τ L (der1 q t x) := rfl
    rw [e]
    unfold der1
    rw [map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_pow]
    show der τ L ((t ^ i) x) ^ i = _
    rw [← hcommL L x hx]
  have hconj : ∀ x : Ω, (∀ A : ValuationSubring Ω, ¬ Over A r → A.valuation x = 1) →
      ∀ (s : G ℚ Ω) (A : ValuationSubring Ω), ¬ Over A r → A.valuation (s x) = 1 := by
    intro x hx s A hA
    obtain ⟨-, -, -, hlt, heq⟩ := (placeBasic Ω).2.2.2.2.2.2.2.2.2 (s⁻¹ • A) s
    have hsA : s • (s⁻¹ • A) = A := smul_inv_smul s A
    rw [hsA] at hlt heq
    apply (heq x).mpr
    apply hx
    intro hB
    apply hA
    have hr := (hlt (r : Ω)).mpr hB
    show A.valuation (r : Ω) < 1
    simpa using hr
  have hvalL : (∀ A : ValuationSubring Ω, ¬ Over A r → A.valuation u = 1) →
      ∀ (L : List ℕ) (A : ValuationSubring Ω), ¬ Over A r → A.valuation (der τ L u) = 1 := by
    intro hu1 L
    induction L with
    | nil => simpa only [der.eq_1] using hu1
    | cons q L ih =>
      intro A hA
      rw [der.eq_2]
      unfold der1
      rw [map_prod]
      apply Finset.prod_eq_one
      intro i _
      rw [Valuation.map_pow, hconj _ ih _ A hA, one_pow]
  have hzpowL : ∀ (L : List ℕ) (k : ℤ), der τ L (u ^ k) = der τ L u ^ k := by
    intro L k
    induction L with
    | nil => simp only [der.eq_1]
    | cons q L ih => rw [der.eq_2, der.eq_2, ih, derivation_zpow]
  have hperm : ∀ L' : List ℕ, L.Perm L' → der τ L u = der τ L' u := by
    intro L' hp
    induction hp with
    | nil => rfl
    | cons q _ ih => rw [der.eq_2, der.eq_2, ih]
    | swap a b l =>
      rw [der.eq_2, der.eq_2, der.eq_2, der.eq_2]
      have hx := hfixL l u hfix
      have h1 : der1 b (τ b) (der1 a (τ a) (der τ l u)) = der τ [b] (der1 a (τ a) (der τ l u)) := by
        rw [der.eq_2, der.eq_1]
      rw [h1, hder1 [b] _ hx, der.eq_2, der.eq_1]
    | trans _ _ ih1 ih2 => exact ih1.trans ih2
  exact ⟨hneL L, hfixL L u hfix, fun g => hcommL L u hfix g, fun h => hvalL h L, der_mul τ L u, hzpowL L,
    fun q => hder1 L u hfix q (τ q), hperm, fun q _ h => tele q (τ q) u hu h⟩
