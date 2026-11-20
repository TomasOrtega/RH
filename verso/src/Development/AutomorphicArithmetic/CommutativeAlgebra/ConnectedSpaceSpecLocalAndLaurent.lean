import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

/- English proof (translation)
Rewrite using `[connectedSpace_iff_clopen]`. Use `⟨inferInstance, fun s hs => ?_⟩` and prove the remaining obligations. Take `⟨e, he, rfl⟩` from `PrimeSpectrum.isClopen_iff.mp hs`. Break down `h e he with rfl | rfl` into its components or cases. Use `left`.

Simplify using the standard rewrite rules. Use `right`. Simplify using the standard rewrite rules.
-/
private theorem conn_of_idem (R : Type) [CommRing R] [Nontrivial R]
    (h : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1) : ConnectedSpace (PrimeSpectrum R) := by
  rw [connectedSpace_iff_clopen]
  refine ⟨inferInstance, fun s hs => ?_⟩
  obtain ⟨e, he, rfl⟩ := PrimeSpectrum.isClopen_iff.mp hs
  rcases h e he with rfl | rfl
  · left
    simp
  · right
    simp

/- English proof (translation)
Break down `IsLocalRing.isUnit_or_isUnit_one_sub_self e with h | h` into its components or cases. Use `right`. Establish `h1 : e * e = e * 1` using `by rw [he.eq, mul_one]`. Conclude with `h.mul_left_cancel h1`. Use `left`.

Establish `h1 : (1 - e) * e = (1 - e) * 0` using `by rw [mul_zero, sub_mul, one_mul, he.eq, sub_self]`. Conclude with `h.mul_left_cancel h1`.
-/
private theorem idem_local (O : Type) [CommRing O] [IsLocalRing O] (e : O)
    (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self e with h | h
  · right
    have h1 : e * e = e * 1 := by rw [he.eq, mul_one]
    exact h.mul_left_cancel h1
  · left
    have h1 : (1 - e) * e = (1 - e) * 0 := by rw [mul_zero, sub_mul, one_mul, he.eq, sub_self]
    exact h.mul_left_cancel h1

/- English proof (translation)
Use `set I : Ideal O := Ideal.span ((e.coeff.support.image e.coeff : Finset O) : Set O) with hI`. Establish `hfg : I.FG` using `⟨_, rfl⟩`. Establish `hmem : ∀ n, e.coeff n ∈ I`. Introduce `n`. Distinguish the cases in `hn : n ∈ e.coeff.support`.

Conclude with `Ideal.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hn))`. Rewrite using `[Finsupp.notMem_support_iff.1 hn]`. Conclude with `zero_mem _`. Establish `hsq : I ≤ I * I`. Rewrite using `[hI, Ideal.span_le]`.

Introduce `x hx`. Take `⟨n, -, rfl⟩` from `Finset.mem_image.1 (Finset.mem_coe.1 hx)`. Establish `h2 : e.coeff n = (e * e).coeff n` using `by rw [he.eq]`. Rewrite using `[← hI, h2, AddMonoidAlgebra.coeff_mul]`. Simplify using `only [Finsupp.sum]`.

Use `Ideal.sum_mem _ fun i _ => Ideal.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Use `split_ifs`. Conclude with `Ideal.mul_mem_mul (hmem i) (hmem j)`. Conclude with `zero_mem _`. Establish `hidem : IsIdempotentElem I` using `le_antisymm Ideal.mul_le_right hsq`.

Take `⟨f, hf, hIf⟩` from `(Ideal.isIdempotentElem_iff_of_fg I hfg).mp hidem`. Establish `hfI : f ∈ I` using `hIf ▸ Submodule.mem_span_singleton_self f`. Establish `hIm : I ≤ IsLocalRing.maximalIdeal O`. Rewrite using `[hI, Ideal.span_le]`. Introduce `x hx`.

Take `⟨n, -, rfl⟩` from `Finset.mem_image.1 (Finset.mem_coe.1 hx)`. Conclude with `hm n`. Establish `hf0 : f = 0`. Break down `idem_local O f hf with h | h` into its components or cases. Conclude with `h`.

It suffices to derive a contradiction. Use `hIm hfI` as an intermediate fact. Rewrite `this` using `[h]`. Conclude with `(IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 this)`. Apply `AddMonoidAlgebra.ext` to reduce the goal to its premises.

Use extensionality with `n`. Establish `hn` using `hmem n`. Rewrite `hn` using `[hIf, hf0]`. Take `⟨a, ha⟩` from `Submodule.mem_span_singleton.1 hn`. Rewrite using `[← ha, smul_zero]`.

Both sides reduce to the same expression.
-/
private theorem idem_zero (O : Type) [CommRing O] [IsLocalRing O] (e : LaurentPolynomial O)
    (he : IsIdempotentElem e) (hm : ∀ n, e.coeff n ∈ IsLocalRing.maximalIdeal O) : e = 0 := by
  classical
  set I : Ideal O := Ideal.span ((e.coeff.support.image e.coeff : Finset O) : Set O) with hI
  have hfg : I.FG := ⟨_, rfl⟩
  have hmem : ∀ n, e.coeff n ∈ I := by
    intro n
    by_cases hn : n ∈ e.coeff.support
    · exact Ideal.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hn))
    · rw [Finsupp.notMem_support_iff.1 hn]
      exact zero_mem _
  have hsq : I ≤ I * I := by
    rw [hI, Ideal.span_le]
    intro x hx
    obtain ⟨n, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
    have h2 : e.coeff n = (e * e).coeff n := by rw [he.eq]
    rw [← hI, h2, AddMonoidAlgebra.coeff_mul]
    simp only [Finsupp.sum]
    refine Ideal.sum_mem _ fun i _ => Ideal.sum_mem _ fun j _ => ?_
    split_ifs
    · exact Ideal.mul_mem_mul (hmem i) (hmem j)
    · exact zero_mem _
  have hidem : IsIdempotentElem I := le_antisymm Ideal.mul_le_right hsq
  obtain ⟨f, hf, hIf⟩ := (Ideal.isIdempotentElem_iff_of_fg I hfg).mp hidem
  have hfI : f ∈ I := hIf ▸ Submodule.mem_span_singleton_self f
  have hIm : I ≤ IsLocalRing.maximalIdeal O := by
    rw [hI, Ideal.span_le]
    intro x hx
    obtain ⟨n, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
    exact hm n
  have hf0 : f = 0 := by
    rcases idem_local O f hf with h | h
    · exact h
    · exfalso
      have := hIm hfI
      rw [h] at this
      exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 this)
  apply AddMonoidAlgebra.ext
  ext n
  have hn := hmem n
  rw [hIf, hf0] at hn
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hn
  rw [← ha, smul_zero]
  rfl

/- English proof (translation)
Use `set φ := AddMonoidAlgebra.mapRingHom ℤ (IsLocalRing.residue O) with hφ`. Establish `key : ∀ x : LaurentPolynomial O, φ x = 0 → ∀ n, x.coeff n ∈ IsLocalRing.maximalIdeal O`. Introduce `x hx n`. Use `congrArg (fun y => AddMonoidAlgebra.coeff y n) hx` as an intermediate fact. Simplify using `only [hφ, AddMonoidAlgebra.coeff_mapRingHom] at this`.

Rewrite using `[← IsLocalRing.residue_eq_zero_iff]`. Simplify using `using this`. Break down `IsIdempotentElem.iff_eq_zero_or_one.1 (he.map φ) with h | h` into its components or cases. Use `left`. Conclude with `idem_zero O e he (key e h)`.

Use `right`. Establish `h1 : 1 - e = 0` using `idem_zero O (1 - e) he.one_sub (key _ (by rw [map_sub, map_one, h, sub_self]))`. Conclude with `(sub_eq_zero.1 h1).symm`.
-/
private theorem idem_laurent (O : Type) [CommRing O] [IsLocalRing O] (e : LaurentPolynomial O)
    (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  set φ := AddMonoidAlgebra.mapRingHom ℤ (IsLocalRing.residue O) with hφ
  have key : ∀ x : LaurentPolynomial O, φ x = 0 → ∀ n, x.coeff n ∈ IsLocalRing.maximalIdeal O := by
    intro x hx n
    have := congrArg (fun y => AddMonoidAlgebra.coeff y n) hx
    simp only [hφ, AddMonoidAlgebra.coeff_mapRingHom] at this
    rw [← IsLocalRing.residue_eq_zero_iff]
    simpa using this
  rcases IsIdempotentElem.iff_eq_zero_or_one.1 (he.map φ) with h | h
  · left
    exact idem_zero O e he (key e h)
  · right
    have h1 : 1 - e = 0 := idem_zero O (1 - e) he.one_sub (key _ (by rw [map_sub, map_one, h, sub_self]))
    exact (sub_eq_zero.1 h1).symm

/- English proof (translation)
Introduce `O _ _`. Conclude with `⟨conn_of_idem O (idem_local O), conn_of_idem _ (idem_laurent O)⟩`.
-/
theorem UpperTheory.connectedSpace_spec_local_and_laurent :
    ∀ (O : Type) [CommRing O] [IsLocalRing O], ConnectedSpace (Spec (CommRingCat.of O)) ∧ ConnectedSpace (Spec (CommRingCat.of (LaurentPolynomial O))) := by
  intro O _ _
  exact ⟨conn_of_idem O (idem_local O), conn_of_idem _ (idem_laurent O)⟩
