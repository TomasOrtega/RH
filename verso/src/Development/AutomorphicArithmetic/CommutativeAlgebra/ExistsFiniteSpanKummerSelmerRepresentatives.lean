import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.IsChart

open GroundTheory.FunctionField UpperTheory.Et.Sel
open scoped TensorProduct

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp [divisor_one]`. Consider the case `succ n ih => rw [pow_succ, divisor_mul (pow_ne_zero _ hx) hx, ih, succ_nsmul]`.
-/
private lemma UpperTheory.exists_finite_span_kummerSelmer_representatives.divisor_pow' {k K : Type} [Field k] [Field K] [Algebra k K] [IsFunctionField k K]
    {x : K} (hx : x ≠ 0) (n : ℕ) : divisor (x ^ n) = n • (divisor x : Divisor k K) := by
  induction n with
  | zero => simp [divisor_one]
  | succ n ih => rw [pow_succ, divisor_mul (pow_ne_zero _ hx) hx, ih, succ_nsmul]

/- English proof (translation)
Introduce `k K _ _ _ _ _ q _`. Establish `hcl : algebraicClosure k K = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce `z hz`. Rewrite `hz` using `[mem_algebraicClosure_iff]`.

Rewrite using `[IntermediateField.mem_bot]`. Conclude with `minpoly.mem_range_of_degree_eq_one k z (IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hz.isIntegral))`. Take `⟨x, hxt, hfd⟩` from `IsFunctionField.exists_transcendental_finiteDimensional (k := k) (K := K)`. Establish `hd : 0 < Module.finrank (IntermediateField.adjoin k ({x} : Set K)) K` using `Module.finrank_pos`. Use `set E : Divisor k K := genus k K • poleDivisor x with hE`.

Establish `hdegE : (genus k K : ℤ) ≤ Divisor.deg E`. Rewrite using `[hE, map_nsmul, Divisor.deg_poleDivisor hxt, nsmul_eq_mul]`. Establish `h1 : (1 : ℤ) ≤ (Module.finrank (IntermediateField.adjoin k ({x} : Set K)) K : ℤ)`. Conclude with `hd` after adjusting the coercions. Establish `h2 : (0 : ℤ) ≤ (genus k K : ℤ)` using `by positivity`.

Use the polynomial consequences of the given equalities and inequalities. Use `set V := (q • E).L with hV`. Set `b` to `Module.finBasis k V`. Use `⟨Module.finrank k V, fun i => (b i : K), ?_⟩` and prove the remaining obligations. Introduce `f hf`.

Establish `hf' : ∀ w : Place k K, (q : ℤ) ∣ w.ord (f : K)` using `hf`. Establish `hq : (q : ℤ) ≠ 0` using `by exact_mod_cast (NeZero.ne q)`. Set `D : Divisor k K` to `Finsupp.mapRange (fun z : ℤ => z / (q : ℤ)) (by simp) (divisor (f : K))`. Establish `hD : divisor (f : K) = q • D`. Use extensionality with `w`.

Simplify using `only [D, Finsupp.smul_apply, Finsupp.mapRange_apply, nsmul_eq_mul]`. Rewrite using `[Int.mul_ediv_cancel', divisor_apply]`. Rewrite using `[divisor_apply]`. Conclude with `hf' w`. Establish `hdegD : Divisor.deg D = 0`.

Establish `h0` using `Divisor.deg_divisor (k := k) (f : K)`. Rewrite `h0` using `[hD, map_nsmul, nsmul_eq_mul]`. Break down `mul_eq_zero.mp h0 with h | h` into its components or cases. Conclude with `absurd h hq`. Conclude with `h`.

Establish `hri` using `Divisor.riemann_inequality hcl (D + E)`. Rewrite `hri` using `[map_add, hdegD, zero_add]`. Establish `hpos : 0 < Module.finrank k (D + E).L` using `by omega`. Take `⟨⟨h, hmem⟩, hne⟩` from `Module.finrank_pos_iff_exists_ne_zero.mp hpos`. Establish `hh : h ≠ 0` using `fun h0 => hne (Subtype.ext h0)`.

Establish `hle` using `(Divisor.mem_L_iff_le hh).mp hmem`. Set `u : Kˣ` to `Units.mk0 h hh`. Establish `hval : ((f * u ^ q : Kˣ) : K) = (f : K) * h ^ q` using `by simp [u]`. Establish `hgne : ((f * u ^ q : Kˣ) : K) ≠ 0` using `Units.ne_zero _`. Establish `hgdiv : divisor ((f * u ^ q : Kˣ) : K) = q • (D + divisor h)`.

Rewrite using `[hval, divisor_mul f.ne_zero (pow_ne_zero _ hh), UpperTheory.exists_finite_span_kummerSelmer_representatives.divisor_pow' hh, hD, smul_add]`. Establish `hgV : ((f * u ^ q : Kˣ) : K) ∈ V`. Rewrite using `[hV, Divisor.mem_L_iff_le hgne, hgdiv, ← smul_add]`. Establish `h3 : D + divisor h + E = divisor h + (D + E)` using `by abel`. Rewrite using `[h3]`.

Conclude with `nsmul_nonneg hle q`. Use `⟨f * u ^ q, ?_, ?_, u⁻¹, by group⟩` and prove the remaining obligations. Introduce `w`. Rewrite using `[← divisor_apply, hgdiv, Finsupp.smul_apply, nsmul_eq_mul]`. Conclude with `Dvd.intro _ rfl`.

Use `⟨fun i => b.repr ⟨_, hgV⟩ i, ?_⟩` and prove the remaining obligations. Establish `hs` using `b.sum_repr ⟨_, hgV⟩`. Establish `hs'` using `congrArg Subtype.val hs`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul] at hs'`. Conclude with `hs'.symm`.
-/
theorem UpperTheory.exists_finite_span_kummerSelmer_representatives :
    ∀ (k K : Type) [Field k] [IsAlgClosed k] [Field K] [Algebra k K] [IsFunctionField k K] (q : ℕ) [NeZero q], ∃ (n : ℕ) (v : Fin n → K), ∀ f ∈ SelAll k K q, ∃ g ∈ SelAll k K q, (∃ c : Fin n → k, (g : K) = ∑ i, c i • v i) ∧ ∃ u : Kˣ, f = g * u ^ q := by
  intro k K _ _ _ _ _ q _
  have hcl : algebraicClosure k K = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [mem_algebraicClosure_iff] at hz
    rw [IntermediateField.mem_bot]
    exact minpoly.mem_range_of_degree_eq_one k z
      (IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hz.isIntegral))
  obtain ⟨x, hxt, hfd⟩ := IsFunctionField.exists_transcendental_finiteDimensional (k := k) (K := K)
  have hd : 0 < Module.finrank (IntermediateField.adjoin k ({x} : Set K)) K := Module.finrank_pos
  set E : Divisor k K := genus k K • poleDivisor x with hE
  have hdegE : (genus k K : ℤ) ≤ Divisor.deg E := by
    rw [hE, map_nsmul, Divisor.deg_poleDivisor hxt, nsmul_eq_mul]
    have h1 : (1 : ℤ) ≤ (Module.finrank (IntermediateField.adjoin k ({x} : Set K)) K : ℤ) := by
      exact_mod_cast hd
    have h2 : (0 : ℤ) ≤ (genus k K : ℤ) := by positivity
    nlinarith
  set V := (q • E).L with hV
  let b := Module.finBasis k V
  refine ⟨Module.finrank k V, fun i => (b i : K), ?_⟩
  intro f hf
  have hf' : ∀ w : Place k K, (q : ℤ) ∣ w.ord (f : K) := hf
  have hq : (q : ℤ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  let D : Divisor k K := Finsupp.mapRange (fun z : ℤ => z / (q : ℤ)) (by simp) (divisor (f : K))
  have hD : divisor (f : K) = q • D := by
    ext w
    simp only [D, Finsupp.smul_apply, Finsupp.mapRange_apply, nsmul_eq_mul]
    rw [Int.mul_ediv_cancel', divisor_apply]
    rw [divisor_apply]
    exact hf' w
  have hdegD : Divisor.deg D = 0 := by
    have h0 := Divisor.deg_divisor (k := k) (f : K)
    rw [hD, map_nsmul, nsmul_eq_mul] at h0
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h hq
    · exact h
  have hri := Divisor.riemann_inequality hcl (D + E)
  rw [map_add, hdegD, zero_add] at hri
  have hpos : 0 < Module.finrank k (D + E).L := by omega
  obtain ⟨⟨h, hmem⟩, hne⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  have hh : h ≠ 0 := fun h0 => hne (Subtype.ext h0)
  have hle := (Divisor.mem_L_iff_le hh).mp hmem
  let u : Kˣ := Units.mk0 h hh
  have hval : ((f * u ^ q : Kˣ) : K) = (f : K) * h ^ q := by simp [u]
  have hgne : ((f * u ^ q : Kˣ) : K) ≠ 0 := Units.ne_zero _
  have hgdiv : divisor ((f * u ^ q : Kˣ) : K) = q • (D + divisor h) := by
    rw [hval, divisor_mul f.ne_zero (pow_ne_zero _ hh), UpperTheory.exists_finite_span_kummerSelmer_representatives.divisor_pow' hh, hD, smul_add]
  have hgV : ((f * u ^ q : Kˣ) : K) ∈ V := by
    rw [hV, Divisor.mem_L_iff_le hgne, hgdiv, ← smul_add]
    have h3 : D + divisor h + E = divisor h + (D + E) := by abel
    rw [h3]
    exact nsmul_nonneg hle q
  refine ⟨f * u ^ q, ?_, ?_, u⁻¹, by group⟩
  · intro w
    rw [← divisor_apply, hgdiv, Finsupp.smul_apply, nsmul_eq_mul]
    exact Dvd.intro _ rfl
  · refine ⟨fun i => b.repr ⟨_, hgV⟩ i, ?_⟩
    have hs := b.sum_repr ⟨_, hgV⟩
    have hs' := congrArg Subtype.val hs
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hs'
    exact hs'.symm
