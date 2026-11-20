import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange

noncomputable section

open NumberField
open scoped TensorProduct Matrix Classical
open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

namespace UpperTheory.Gal.W2

/- English proof (translation)
Establish `hinj : Function.Injective (Algebra.linearMap ℤ ℤ_[p])`. Introduce `a b h`. Conclude with `RingHom.injective_int (algebraMap ℤ ℤ_[p]) h`. Establish `h1` using `Module.Flat.lTensor_preserves_injective_linearMap (M := O) (Algebra.linearMap ℤ ℤ_[p]) hinj`. Introduce `x y hxy`.

Establish `h2 : x ⊗ₜ[ℤ] (1 : ℤ) = y ⊗ₜ[ℤ] (1 : ℤ)` using `h1 (by simpa using hxy)`. Establish `h3` using `congrArg (TensorProduct.rid ℤ O) h2`. Simplify using `using h3`.
-/
private theorem tens_inj (p : ℕ) [Fact p.Prime] {O : Type} [Ring O] [Module.Free ℤ O] :
    Function.Injective (fun x : O => x ⊗ₜ[ℤ] (1 : ℤ_[p])) := by
  have hinj : Function.Injective (Algebra.linearMap ℤ ℤ_[p]) := by
    intro a b h
    exact RingHom.injective_int (algebraMap ℤ ℤ_[p]) h
  have h1 := Module.Flat.lTensor_preserves_injective_linearMap (M := O) (Algebra.linearMap ℤ ℤ_[p]) hinj
  intro x y hxy
  have h2 : x ⊗ₜ[ℤ] (1 : ℤ) = y ⊗ₜ[ℤ] (1 : ℤ) := h1 (by simpa using hxy)
  have h3 := congrArg (TensorProduct.rid ℤ O) h2
  simpa using h3

/- English proof (translation)
Substitute `hm` using the available equality. Apply `tens_inj p` to reduce the goal to its premises. Establish `hc : ∀ A B : Matrix (Fin 1) (Fin 1) R, A * B = B * A`. Introduce `A B`. Use extensionality with `i j`.

Take `rfl : i = 0` from `Subsingleton.elim _ _`. Take `rfl : j = 0` from `Subsingleton.elim _ _`. Simplify using `[Matrix.mul_apply, mul_comm]`. Use `hc (f (x ⊗ₜ[ℤ] (1 : ℤ_[p]))) (f (y ⊗ₜ[ℤ] (1 : ℤ_[p])))` as an intermediate fact. Rewrite `this` using `[← map_mul, ← map_mul]`.

Establish `h2` using `f.injective this`. Simplify using `using h2`.
-/
private theorem comm_of_split (p : ℕ) [Fact p.Prime] {O : Type} [Ring O] [Module.Free ℤ O] {R : Type} [CommRing R]
    {m : ℕ} (hm : m = 1) (f : (O ⊗[ℤ] ℤ_[p]) ≃+* Matrix (Fin m) (Fin m) R) (x y : O) : x * y = y * x := by
  subst hm
  apply tens_inj p
  have hc : ∀ A B : Matrix (Fin 1) (Fin 1) R, A * B = B * A := by
    intro A B
    ext i j
    obtain rfl : i = 0 := Subsingleton.elim _ _
    obtain rfl : j = 0 := Subsingleton.elim _ _
    simp [Matrix.mul_apply, mul_comm]
  have := hc (f (x ⊗ₜ[ℤ] (1 : ℤ_[p]))) (f (y ⊗ₜ[ℤ] (1 : ℤ_[p])))
  rw [← map_mul, ← map_mul] at this
  have h2 := f.injective this
  simpa using h2

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `c hc`. Assume the negation of the conclusion as `h0`. Establish `hI : RingHom.ker (algebraMap (𝓞 F) O) ≠ ⊥` using `fun h => h0 (by`. Establish `h1 : c ∈ RingHom.ker (algebraMap (𝓞 F) O)` using `hc`.

Rewrite `h1` using `[h]`. Simplify using `using h1)`. Establish `hN` using `Ideal.absNorm_mem (RingHom.ker (algebraMap (𝓞 F) O))`. Establish `hN0 : Ideal.absNorm (RingHom.ker (algebraMap (𝓞 F) O)) ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`.

Conclude with `hI`. Rewrite `hN` using `[RingHom.mem_ker, map_natCast]`. Establish `h1 : (Ideal.absNorm (RingHom.ker (algebraMap (𝓞 F) O)) : ℤ) • (1 : O) = 0`. Rewrite using `[zsmul_one]`. Conclude with `hN` after adjusting the coercions.

Break down `smul_eq_zero.mp h1 with h | h` into its components or cases. Conclude with `hN0 (by exact_mod_cast h)`. Conclude with `one_ne_zero h`.
-/
private theorem a_inj {F : Type} [Field F] [NumberField F] {O : Type} [Ring O] [Algebra (𝓞 F) O] [Nontrivial O]
    [Module.Free ℤ O] : Function.Injective (algebraMap (𝓞 F) O) := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  by_contra h0
  have hI : RingHom.ker (algebraMap (𝓞 F) O) ≠ ⊥ := fun h => h0 (by
    have h1 : c ∈ RingHom.ker (algebraMap (𝓞 F) O) := hc
    rw [h] at h1
    simpa using h1)
  have hN := Ideal.absNorm_mem (RingHom.ker (algebraMap (𝓞 F) O))
  have hN0 : Ideal.absNorm (RingHom.ker (algebraMap (𝓞 F) O)) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact hI
  rw [RingHom.mem_ker, map_natCast] at hN
  have h1 : (Ideal.absNorm (RingHom.ker (algebraMap (𝓞 F) O)) : ℤ) • (1 : O) = 0 := by
    rw [zsmul_one]
    exact_mod_cast hN
  rcases smul_eq_zero.mp h1 with h | h
  · exact hN0 (by exact_mod_cast h)
  · exact one_ne_zero h

/- English proof (translation)
Introduce `x`. Take `⟨c, e, he, hx⟩` from `hc x`. Use `letI : CommRing O := { (inferInstance : Ring O) with mul_comm := hcomm }`. Take `⟨P, hP, hPx⟩ : IsIntegral ℤ x` from `IsIntegral.of_finite ℤ x`. Establish `hQ : Polynomial.eval₂ (algebraMap ℤ O) (algebraMap ℤ O e * x) (P.scaleRoots e) = 0`.

Rewrite using `[Polynomial.scaleRoots_eval₂_mul, hPx, mul_zero]`. Establish `hex : algebraMap ℤ O e * x = algebraMap (𝓞 F) O c`. Rewrite using `[← hx]`. Simplify using `[zsmul_eq_mul]`. Establish `hQ2 : Polynomial.eval₂ (algebraMap ℤ (𝓞 F)) c (P.scaleRoots e) = 0`.

Apply `a_inj (O := O)` to reduce the goal to its premises. Rewrite using `[map_zero, Polynomial.hom_eval₂, ← hex, ← hQ]`. Use `congr 1`. Conclude with `RingHom.ext_int _ _`. Establish `hQ3 : Polynomial.eval₂ (algebraMap ℤ F) (c : F) (P.scaleRoots e) = 0`.

Use `congrArg (algebraMap (𝓞 F) F) hQ2` as an intermediate fact. Rewrite `this` using `[map_zero, Polynomial.hom_eval₂]`. Rewrite using `[← this]`. Use `congr 1`. Establish `heF : (algebraMap ℤ F e) ≠ 0` using `by simpa using he`.

Establish `hcF : (c : F) = algebraMap ℤ F e * ((c : F) / algebraMap ℤ F e)` using `by field_simp`. Rewrite `hQ3` using `[hcF, Polynomial.scaleRoots_eval₂_mul]`. Establish `hint : IsIntegral ℤ ((c : F) / algebraMap ℤ F e)` using `⟨P, hP, (mul_eq_zero.mp hQ3).resolve_left (pow_ne_zero _ heF)⟩`. Take `⟨c', hc'⟩` from `(IsIntegralClosure.isIntegral_iff (A := 𝓞 F)).1 hint`. Use `⟨c', ?_⟩` and prove the remaining obligations.

Establish `hcc : c = e • c'`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[hcF, ← hc']`. Simplify using `[zsmul_eq_mul]`. Establish `h3 : e • (algebraMap (𝓞 F) O c' - x) = 0`.

Rewrite using `[smul_sub, hx, hcc, zsmul_eq_mul, zsmul_eq_mul]`. Simplify using the standard rewrite rules. Break down `smul_eq_zero.mp h3 with h | h` into its components or cases. Conclude with `absurd h he`. Conclude with `sub_eq_zero.mp h`.
-/
private theorem a_onto {F : Type} [Field F] [NumberField F] {O : Type} [Ring O] [Algebra (𝓞 F) O] [Nontrivial O]
    [Module.Free ℤ O] [Module.Finite ℤ O] (hcomm : ∀ x y : O, x * y = y * x)
    (hc : ∀ x : O, ∃ c : 𝓞 F, ∃ e : ℤ, e ≠ 0 ∧ e • x = algebraMap (𝓞 F) O c) :
    Function.Surjective (algebraMap (𝓞 F) O) := by
  intro x
  obtain ⟨c, e, he, hx⟩ := hc x
  letI : CommRing O := { (inferInstance : Ring O) with mul_comm := hcomm }
  obtain ⟨P, hP, hPx⟩ : IsIntegral ℤ x := IsIntegral.of_finite ℤ x
  have hQ : Polynomial.eval₂ (algebraMap ℤ O) (algebraMap ℤ O e * x) (P.scaleRoots e) = 0 := by
    rw [Polynomial.scaleRoots_eval₂_mul, hPx, mul_zero]
  have hex : algebraMap ℤ O e * x = algebraMap (𝓞 F) O c := by
    rw [← hx]; simp [zsmul_eq_mul]
  have hQ2 : Polynomial.eval₂ (algebraMap ℤ (𝓞 F)) c (P.scaleRoots e) = 0 := by
    apply a_inj (O := O)
    rw [map_zero, Polynomial.hom_eval₂, ← hex, ← hQ]
    congr 1
    exact RingHom.ext_int _ _
  have hQ3 : Polynomial.eval₂ (algebraMap ℤ F) (c : F) (P.scaleRoots e) = 0 := by
    have := congrArg (algebraMap (𝓞 F) F) hQ2
    rw [map_zero, Polynomial.hom_eval₂] at this
    rw [← this]
    congr 1
  have heF : (algebraMap ℤ F e) ≠ 0 := by simpa using he
  have hcF : (c : F) = algebraMap ℤ F e * ((c : F) / algebraMap ℤ F e) := by field_simp
  rw [hcF, Polynomial.scaleRoots_eval₂_mul] at hQ3
  have hint : IsIntegral ℤ ((c : F) / algebraMap ℤ F e) :=
    ⟨P, hP, (mul_eq_zero.mp hQ3).resolve_left (pow_ne_zero _ heF)⟩
  obtain ⟨c', hc'⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 F)).1 hint
  refine ⟨c', ?_⟩
  have hcc : c = e • c' := by
    apply RingOfIntegers.ext
    rw [hcF, ← hc']
    simp [zsmul_eq_mul]
  have h3 : e • (algebraMap (𝓞 F) O c' - x) = 0 := by
    rw [smul_sub, hx, hcc, zsmul_eq_mul, zsmul_eq_mul]
    simp
  rcases smul_eq_zero.mp h3 with h | h
  · exact absurd h he
  · exact sub_eq_zero.mp h

/- English proof (translation)
Establish `hne : (starRingEnd ℂ) r ≠ r`. Introduce `h`. Take `⟨t, rfl⟩` from `Complex.conj_eq_iff_real.mp h`. Establish `h1 : (t : ℂ) ^ 2 - (tr : ℝ) * t + (nm : ℝ) = 0` using `by simpa using hr`. Establish `h2 : t ^ 2 - (tr : ℝ) * t + (nm : ℝ) = 0` using `by exact_mod_cast h1`.

Establish `h3 : ((tr : ℝ)) ^ 2 - 4 * (nm : ℝ) < 0` using `by exact_mod_cast hd`. Use polynomial arithmetic with `[sq_nonneg (2 * t - tr)]`. Use `⟨hne, ?_⟩` and prove the remaining obligations. Establish `hr' : ((starRingEnd ℂ) r) ^ 2 - tr * (starRingEnd ℂ) r + nm = 0`. Use `congrArg (starRingEnd ℂ) hr` as an intermediate fact.

Simplify using `using this`. Establish `hs : r + (starRingEnd ℂ) r = tr`. Establish `h1 : (r - (starRingEnd ℂ) r) * (r + (starRingEnd ℂ) r - tr) = 0`. Take the linear combination `hr - hr'`. Break down `mul_eq_zero.mp h1 with h | h` into its components or cases.

Conclude with `absurd (sub_eq_zero.mp h).symm hne`. Conclude with `sub_eq_zero.mp h`. Establish `h2 : (z - r) * (z - (starRingEnd ℂ) r) = 0`. Rewrite `hz`, `hr` using `[← hs]`. Take the linear combination `hz - hr`.

Break down `mul_eq_zero.mp h2 with h | h` into its components or cases. Conclude with `Or.inl (sub_eq_zero.mp h)`. Conclude with `Or.inr (sub_eq_zero.mp h)`.
-/
private theorem root_cases (tr nm : ℤ) (hd : tr ^ 2 - 4 * nm < 0) (r z : ℂ) (hr : r ^ 2 - tr * r + nm = 0)
    (hz : z ^ 2 - tr * z + nm = 0) : (starRingEnd ℂ) r ≠ r ∧ (z = r ∨ z = (starRingEnd ℂ) r) := by
  have hne : (starRingEnd ℂ) r ≠ r := by
    intro h
    obtain ⟨t, rfl⟩ := Complex.conj_eq_iff_real.mp h
    have h1 : (t : ℂ) ^ 2 - (tr : ℝ) * t + (nm : ℝ) = 0 := by simpa using hr
    have h2 : t ^ 2 - (tr : ℝ) * t + (nm : ℝ) = 0 := by exact_mod_cast h1
    have h3 : ((tr : ℝ)) ^ 2 - 4 * (nm : ℝ) < 0 := by exact_mod_cast hd
    nlinarith [sq_nonneg (2 * t - tr)]
  refine ⟨hne, ?_⟩
  have hr' : ((starRingEnd ℂ) r) ^ 2 - tr * (starRingEnd ℂ) r + nm = 0 := by
    have := congrArg (starRingEnd ℂ) hr
    simpa using this
  have hs : r + (starRingEnd ℂ) r = tr := by
    have h1 : (r - (starRingEnd ℂ) r) * (r + (starRingEnd ℂ) r - tr) = 0 := by
      linear_combination hr - hr'
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd (sub_eq_zero.mp h).symm hne
    · exact sub_eq_zero.mp h
  have h2 : (z - r) * (z - (starRingEnd ℂ) r) = 0 := by
    rw [← hs] at hz hr
    linear_combination hz - hr
  rcases mul_eq_zero.mp h2 with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (sub_eq_zero.mp h)

/- English proof (translation)
Establish `hinv : ∀ σ : F →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ` using `ComplexEmbedding.involutive_conjugate F`. Establish `hc0 : ComplexEmbedding.conjugate t₀ ≠ t₀` using `cx t₀`. Establish `hw : ∀ τ, typeMult n t₀ ε τ + typeMult n t₀ ε (ComplexEmbedding.conjugate τ) = n`. Introduce `τ`. Distinguish the cases in `h1 : τ = t₀`.

Substitute `h1` using the available equality. Simplify using `only [typeMult, if_true, if_neg hc0]`. Use linear arithmetic over natural numbers and integers. Distinguish the cases in `h2 : τ = ComplexEmbedding.conjugate t₀`. Substitute `h2` using the available equality.

Simplify using `only [typeMult, hinv, if_neg hc0, if_true]`. Use linear arithmetic over natural numbers and integers. Establish `h3 : ComplexEmbedding.conjugate τ ≠ t₀` using `fun h => h2 (by rw [← h, hinv])`. Establish `h4 : ComplexEmbedding.conjugate τ ≠ ComplexEmbedding.conjugate t₀` using `fun h => h1 ((ComplexEmbedding.involutive_conjugate F).injective h)`. Simplify using `only [typeMult, if_neg h1, if_neg h2, if_neg h3, if_neg h4]`.

Rewrite using `[← Nat.mul_add, eps τ h1 h2, Nat.mul_one]`. Establish `hs : ∑ τ : F →+* ℂ, typeMult n t₀ ε (ComplexEmbedding.conjugate τ) = ∑ τ : F →+* ℂ, typeMult n t₀ ε τ` using `Equiv.sum_comp (Function.Involutive.toPerm _ (ComplexEmbedding.involutive_conjugate F)) (typeMult n t₀ ε)`. Establish `h2 : ∑ τ : F →+* ℂ, (typeMult n t₀ ε τ + typeMult n t₀ ε (ComplexEmbedding.conjugate τ)) = n * Module.finrank ℚ F`. Simplify using `only [hw, Finset.sum_const, Finset.card_univ, smul_eq_mul]`. Rewrite using `[Embeddings.card F ℂ, mul_comm]`.

Rewrite `h2` using `[Finset.sum_add_distrib, hs]`. Use linear arithmetic over natural numbers and integers.
-/
private theorem sum_mult {F : Type} [Field F] [NumberField F] (n : ℕ) (hn : 1 ≤ n) (t₀ : F →+* ℂ)
    (ε : (F →+* ℂ) → ℕ) (cx : ∀ τ : F →+* ℂ, ComplexEmbedding.conjugate τ ≠ τ)
    (eps : ∀ τ, τ ≠ t₀ → τ ≠ ComplexEmbedding.conjugate t₀ → ε τ + ε (ComplexEmbedding.conjugate τ) = 1) :
    2 * ∑ τ : F →+* ℂ, typeMult n t₀ ε τ = n * Module.finrank ℚ F := by
  have hinv : ∀ σ : F →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ :=
    ComplexEmbedding.involutive_conjugate F
  have hc0 : ComplexEmbedding.conjugate t₀ ≠ t₀ := cx t₀
  have hw : ∀ τ, typeMult n t₀ ε τ + typeMult n t₀ ε (ComplexEmbedding.conjugate τ) = n := by
    intro τ
    by_cases h1 : τ = t₀
    · subst h1
      simp only [typeMult, if_true, if_neg hc0]
      omega
    by_cases h2 : τ = ComplexEmbedding.conjugate t₀
    · subst h2
      simp only [typeMult, hinv, if_neg hc0, if_true]
      omega
    have h3 : ComplexEmbedding.conjugate τ ≠ t₀ := fun h => h2 (by rw [← h, hinv])
    have h4 : ComplexEmbedding.conjugate τ ≠ ComplexEmbedding.conjugate t₀ := fun h =>
      h1 ((ComplexEmbedding.involutive_conjugate F).injective h)
    simp only [typeMult, if_neg h1, if_neg h2, if_neg h3, if_neg h4]
    rw [← Nat.mul_add, eps τ h1 h2, Nat.mul_one]
  have hs : ∑ τ : F →+* ℂ, typeMult n t₀ ε (ComplexEmbedding.conjugate τ) = ∑ τ : F →+* ℂ, typeMult n t₀ ε τ :=
    Equiv.sum_comp (Function.Involutive.toPerm _ (ComplexEmbedding.involutive_conjugate F)) (typeMult n t₀ ε)
  have h2 : ∑ τ : F →+* ℂ, (typeMult n t₀ ε τ + typeMult n t₀ ε (ComplexEmbedding.conjugate τ)) =
      n * Module.finrank ℚ F := by
    simp only [hw, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    rw [Embeddings.card F ℂ, mul_comm]
  rw [Finset.sum_add_distrib, hs] at h2
  omega

/- English proof (translation)
Introduce `p _ D ha hm t₀ ht`. Use `haveI := D.freeO`. Use `haveI := D.finO`. Establish `hd : 0 < Module.finrank ℚ D.F` using `Module.finrank_pos`. Use `haveI : Nontrivial D.O := by`.

Apply `Module.nontrivial_of_finrank_pos (R := ℤ)` to reduce the goal to its premises. Rewrite using `[D.rankO, hm]`. Simplify using `using hd`. Take `⟨f⟩` from `D.splitP`. Establish `hcomm : ∀ x y : D.O, x * y = y * x` using `comm_of_split p hm f.toRingEquiv`.

Establish `hinj : Function.Injective (algebraMap (𝓞 D.F) D.O)` using `a_inj`. Establish `honto : Function.Surjective (algebraMap (𝓞 D.F) D.O)` using `a_onto hcomm fun x => D.central x (hcomm x)`. Set `e : 𝓞 D.F ≃+* D.O` to `RingEquiv.ofBijective (algebraMap (𝓞 D.F) D.O) ⟨hinj, honto⟩`. Establish `he : ∀ c : 𝓞 D.F, e.symm (algebraMap (𝓞 D.F) D.O c) = c` using `fun c => e.symm_apply_apply c`. Establish `h0 : 0 < D.a` using `by omega`.

Establish `ht0 : t₀ (D.ω : D.F) = D.ρc`. Rewrite using `[← ht ⟨0, h0⟩]`. Conclude with `D.tau_ω _`. Establish `hroot : ∀ τ : D.F →+* ℂ, (τ (D.ω : D.F)) ^ 2 - D.tr * τ (D.ω : D.F) + D.nm = 0`. Introduce `τ`.

Establish `h1` using `congrArg (fun x : 𝓞 D.F => τ (x : D.F)) D.tr_eq`. Establish `h2` using `congrArg (fun x : 𝓞 D.F => τ (x : D.F)) D.nm_eq`. Simplify using `only [map_add, map_mul, map_intCast] at h1 h2`. Rewrite using `[← h1, ← h2]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hcx : ∀ τ : D.F →+* ℂ, ComplexEmbedding.conjugate τ ≠ τ`. Introduce `τ h`. Establish `hc : (InfinitePlace.mk τ).IsComplex` using `IsTotallyComplex.isComplex _`. Conclude with `(InfinitePlace.isComplex_mk_iff.mp hc) (ComplexEmbedding.isReal_iff.mpr h)`. Establish `heps : ∀ τ, τ ≠ t₀ → τ ≠ ComplexEmbedding.conjugate t₀ → epsD D τ + epsD D (ComplexEmbedding.conjugate τ) = 1`.

Introduce `τ _ _`. Take `⟨hne, hcase⟩` from `root_cases D.tr D.nm D.disc_neg D.ρc (τ (D.ω : D.F)) D.ρc_root (hroot τ)`. Unfold `epsD`. Rewrite using `[ComplexEmbedding.conjugate_coe_eq]`. Break down `hcase with h | h` into its components or cases.

Rewrite using `[h, if_pos rfl, if_neg hne]`. Rewrite using `[h, if_neg hne, Complex.conj_conj, if_pos rfl]`. Establish `hsum : ∑ τ : D.F →+* ℂ, typeMult D.n t₀ (epsD D) τ = D.g`. Establish `h2` using `sum_mult D.n D.n_pos t₀ (epsD D) hcx heps`. Unfold `Datum.g`.

Rewrite using `[hm, one_mul, ← h2]`. Simplify using the standard rewrite rules. Take `⟨E⟩ : Nonempty (Fin D.g ≃ Σ τ : D.F →+* ℂ, Fin (typeMult D.n t₀ (epsD D) τ))` from `⟨(Fintype.equivFinOfCardEq (by simp [hsum])).symm⟩`. Set `ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ` to `(Matrix.diagonalRingHom (Fin D.g) ℂ).comp ((Pi.ringHom fun i => ((E i).1).comp (algebraMap (𝓞 D.F) D.F)).comp (e.symm : D.O →+* 𝓞 D.F))`. Establish `hρ : ∀ c : 𝓞 D.F, ρ (algebraMap (𝓞 D.F) D.O c) = Matrix.diagonal fun i => (E i).1 (c : D.F)`.

Introduce `c`. Simplify using `only [ρ, RingHom.comp_apply, RingHom.coe_coe, he]`. Both sides reduce to the same expression. Use `⟨ρ, ⟨honto, fun c => ⟨D.bar c, ?_, fun τ => ?_⟩, hcx, D.n_pos, heps, fun c => ?_⟩⟩` and prove the remaining obligations. Use `show (D.star (algebraMap (𝓞 D.F) D.O c)).unop = _`.

Rewrite using `[D.star_F]`. Both sides reduce to the same expression. Rewrite using `[D.bar_eq, IsCMField.complexEmbedding_complexConj]`. Rewrite using `[hρ, Matrix.trace_diagonal, Equiv.sum_comp E (fun s : (Σ τ : D.F →+* ℂ, Fin (typeMult D.n t₀ (epsD D) τ)) => s.1 (c : D.F)), Fintype.sum_sigma]`. Simplify using the standard rewrite rules.
-/
theorem rhoSig_of : RhoSig := by
  intro p _ D ha hm t₀ ht
  haveI := D.freeO
  haveI := D.finO
  have hd : 0 < Module.finrank ℚ D.F := Module.finrank_pos
  haveI : Nontrivial D.O := by
    apply Module.nontrivial_of_finrank_pos (R := ℤ)
    rw [D.rankO, hm]
    simpa using hd
  obtain ⟨f⟩ := D.splitP
  have hcomm : ∀ x y : D.O, x * y = y * x := comm_of_split p hm f.toRingEquiv
  have hinj : Function.Injective (algebraMap (𝓞 D.F) D.O) := a_inj
  have honto : Function.Surjective (algebraMap (𝓞 D.F) D.O) :=
    a_onto hcomm fun x => D.central x (hcomm x)
  let e : 𝓞 D.F ≃+* D.O := RingEquiv.ofBijective (algebraMap (𝓞 D.F) D.O) ⟨hinj, honto⟩
  have he : ∀ c : 𝓞 D.F, e.symm (algebraMap (𝓞 D.F) D.O c) = c := fun c => e.symm_apply_apply c
  have h0 : 0 < D.a := by omega
  have ht0 : t₀ (D.ω : D.F) = D.ρc := by
    rw [← ht ⟨0, h0⟩]
    exact D.tau_ω _
  have hroot : ∀ τ : D.F →+* ℂ, (τ (D.ω : D.F)) ^ 2 - D.tr * τ (D.ω : D.F) + D.nm = 0 := by
    intro τ
    have h1 := congrArg (fun x : 𝓞 D.F => τ (x : D.F)) D.tr_eq
    have h2 := congrArg (fun x : 𝓞 D.F => τ (x : D.F)) D.nm_eq
    simp only [map_add, map_mul, map_intCast] at h1 h2
    rw [← h1, ← h2]
    ring
  have hcx : ∀ τ : D.F →+* ℂ, ComplexEmbedding.conjugate τ ≠ τ := by
    intro τ h
    have hc : (InfinitePlace.mk τ).IsComplex := IsTotallyComplex.isComplex _
    exact (InfinitePlace.isComplex_mk_iff.mp hc) (ComplexEmbedding.isReal_iff.mpr h)
  have heps : ∀ τ, τ ≠ t₀ → τ ≠ ComplexEmbedding.conjugate t₀ →
      epsD D τ + epsD D (ComplexEmbedding.conjugate τ) = 1 := by
    intro τ _ _
    obtain ⟨hne, hcase⟩ := root_cases D.tr D.nm D.disc_neg D.ρc (τ (D.ω : D.F)) D.ρc_root (hroot τ)
    unfold epsD
    rw [ComplexEmbedding.conjugate_coe_eq]
    rcases hcase with h | h
    · rw [h, if_pos rfl, if_neg hne]
    · rw [h, if_neg hne, Complex.conj_conj, if_pos rfl]
  have hsum : ∑ τ : D.F →+* ℂ, typeMult D.n t₀ (epsD D) τ = D.g := by
    have h2 := sum_mult D.n D.n_pos t₀ (epsD D) hcx heps
    unfold Datum.g
    rw [hm, one_mul, ← h2]
    simp
  obtain ⟨E⟩ : Nonempty (Fin D.g ≃ Σ τ : D.F →+* ℂ, Fin (typeMult D.n t₀ (epsD D) τ)) :=
    ⟨(Fintype.equivFinOfCardEq (by simp [hsum])).symm⟩
  let ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ :=
    (Matrix.diagonalRingHom (Fin D.g) ℂ).comp
      ((Pi.ringHom fun i => ((E i).1).comp (algebraMap (𝓞 D.F) D.F)).comp (e.symm : D.O →+* 𝓞 D.F))
  have hρ : ∀ c : 𝓞 D.F, ρ (algebraMap (𝓞 D.F) D.O c) = Matrix.diagonal fun i => (E i).1 (c : D.F) := by
    intro c
    simp only [ρ, RingHom.comp_apply, RingHom.coe_coe, he]
    rfl
  refine ⟨ρ, ⟨honto, fun c => ⟨D.bar c, ?_, fun τ => ?_⟩, hcx, D.n_pos, heps, fun c => ?_⟩⟩
  · show (D.star (algebraMap (𝓞 D.F) D.O c)).unop = _
    rw [D.star_F]
    rfl
  · rw [D.bar_eq, IsCMField.complexEmbedding_complexConj]
  · rw [hρ, Matrix.trace_diagonal,
      Equiv.sum_comp E (fun s : (Σ τ : D.F →+* ℂ, Fin (typeMult D.n t₀ (epsD D) τ)) => s.1 (c : D.F)),
      Fintype.sum_sigma]
    simp

end UpperTheory.Gal.W2
