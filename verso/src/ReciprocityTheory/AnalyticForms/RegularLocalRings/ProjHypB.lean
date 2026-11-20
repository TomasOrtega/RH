import ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjHypA

namespace ReciprocityTheory.AnForm.R

open MvPolynomial

noncomputable section

variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Use `set R := MvPolynomial (Σ k, ι k) ℂ`. Establish `hMp : M.IsPrime` using `hM.1.1`. Establish `hcM : chartIdeal P p ≤ M` using `hM.1.2`. Establish `hX1 : ∀ k, (X ⟨k, p k⟩ - 1 : R) ∈ M` using `fun k => hcM (Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩))`. Establish `hXM : ∀ k, (X ⟨k, p k⟩ : R) ∉ M` using `fun k h => hMp.ne_top ((Ideal.eq_top_iff_one _).mpr (by`.

Use `M.sub_mem h (hX1 k)` as an intermediate fact. Simplify using `using this))`. Take `⟨q, hq, hqM⟩` from `Ideal.exists_minimalPrimes_le (le_sup_left.trans hcM : P ≤ M)`. Establish `hqp : q.IsPrime` using `hq.1.1`. Establish `hPq : P ≤ q` using `hq.1.2`.

Use `set s : R := ∏ k, X ⟨k, p k⟩`. Establish `hsq : s ∉ q`. Introduce `h`. Take `⟨k, -, hk⟩` from `(Ideal.IsPrime.prod_mem_iff (p := q)).mp h`. Conclude with `hXM k (hqM hk)`.

Establish `hdis : Disjoint (Submonoid.powers s : Set R) ↑q` using `(Ideal.disjoint_powers_iff_notMem_of_isPrime s).mpr hsq`. Set `A` to `Localization.Away s`. Establish `hu : ∀ k, IsUnit (algebraMap R A (X ⟨k, p k⟩))` using `fun k => isUnit_of_dvd_unit (map_dvd (algebraMap R A) (Finset.dvd_prod_of_mem (fun k => (X ⟨k, p k⟩ : R)) (Finset.mem_univ k))) (IsLocalization.Away.algebraMap_isUnit (S := A) s)`. Set `u : K → A` to `fun k => ((hu k).unit⁻¹ : Aˣ)`. Establish `hu1 : ∀ k, u k * algebraMap R A (X ⟨k, p k⟩) = 1` using `fun k => (hu k).val_inv_mul`.

Set `σ : R →+* A` to `eval₂Hom (algebraMap ℂ A) (fun r => u r.1 * algebraMap R A (X r))`. Establish `hσ : ∀ (f : R) (a : K → ℕ), IsMultiHomog f a → σ f = (∏ k, u k ^ a k) * algebraMap R A f`. Introduce `f a hf`. Use `show eval₂ (algebraMap ℂ A) (fun r => u r.1 * algebraMap R A (X r)) f = _`. Rewrite using `[eval₂_smul_of_isMultiHomog' (algebraMap ℂ A) hf u (fun r => algebraMap R A (X r))]`.

Use `congr 1`. Use `conv_rhs => rw [← eval₂_eta f, eval₂_comp_left]`. Use `congr 1`. Set `Q : Ideal A` to `Ideal.map (algebraMap R A) q`. Establish `hQp : Q.IsPrime` using `IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers s) A q hqp hdis`.

Establish `hQq : Q.comap (algebraMap R A) = q` using `IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers s) A hqp hdis`. Set `M' : Ideal R` to `Q.comap σ`. Establish `: M'.IsPrime` using `Ideal.comap_isPrime σ Q`. Establish `hs1 : IsUnit (Ideal.Quotient.mk M s)`. Establish `: ∀ k, Ideal.Quotient.mk M (X ⟨k, p k⟩) = 1` using `fun k => by`.

Rewrite using `[← sub_eq_zero, ← map_one (Ideal.Quotient.mk M), ← map_sub, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hX1 k`. Simplify using `[s, map_prod, this]`. Set `φ : A →+* R ⧸ M` to `IsLocalization.Away.lift s hs1`. Establish `hφa : ∀ x : R, φ (algebraMap R A x) = Ideal.Quotient.mk M x` using `fun x => IsLocalization.Away.lift_eq s hs1 x`.

Establish `hφu : ∀ k, φ (u k) = 1` using `fun k => by`. Establish `h` using `congrArg φ (hu1 k)`. Rewrite `h` using `[map_mul, map_one, hφa]`. Establish `hx : Ideal.Quotient.mk M (X ⟨k, p k⟩) = 1`. Rewrite using `[← sub_eq_zero, ← map_one (Ideal.Quotient.mk M), ← map_sub, Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `hX1 k`. Rewrite `h` using `[hx, mul_one]`. Conclude with `h`. Establish `hφσ : φ.comp σ = Ideal.Quotient.mk M`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises.

Introduce `c`. Simplify using `[σ, IsScalarTower.algebraMap_apply ℂ R A, hφa]`. Both sides reduce to the same expression. Introduce `r`. Simplify using `[σ, hφa, hφu]`.

Establish `hM'M : M' ≤ M`. Introduce `g hg`. Establish `hQ : Q ≤ (⊥ : Ideal (R ⧸ M)).comap φ`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `x hx`.

Simplify using `only [Ideal.mem_comap, hφa, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hqM hx`. Establish `h0` using `hQ hg`. Simplify using `only [Ideal.mem_comap, Ideal.mem_bot] at h0`. Establish `: Ideal.Quotient.mk M g = 0` using `by rw [← hφσ]; exact h0`.

Conclude with `Ideal.Quotient.eq_zero_iff_mem.mp this`. Establish `hcM' : chartIdeal P p ≤ M'`. Use `sup_le ?_ ?_` and prove the remaining obligations. Take `⟨S, hS, hPS⟩` from `hP`. Rewrite using `[hPS, Ideal.span_le]`.

Introduce `f hfS`. Take `⟨a, ha⟩` from `hS f hfS`. Use `show σ f ∈ Q`. Rewrite using `[hσ f a ha]`. Conclude with `Q.mul_mem_left _ (Ideal.mem_map_of_mem _ (hPq (hPS ▸ Ideal.subset_span hfS)))`.

Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨k, rfl⟩`. Use `show σ _ ∈ Q`. Establish `: σ (X ⟨k, p k⟩ - 1) = 0`. Establish `hσX : σ (X ⟨k, p k⟩) = u k * algebraMap R A (X ⟨k, p k⟩)` using `eval₂_X _ _ _`.

Rewrite using `[map_sub, map_one, hσX, hu1, sub_self]`. Rewrite using `[this]`. Conclude with `Q.zero_mem`. Establish `hMM' : M ≤ M'` using `hM.2 ⟨inferInstance, hcM'⟩ hM'M`. Use `⟨q, hq, fun k => ⟨p k, fun h => hXM k (hqM h)⟩, ?_⟩` and prove the remaining obligations.

Take `⟨T, hT, hDT⟩` from `hD`. Rewrite using `[hDT, Ideal.span_le]`. Introduce `f hfT`. Take `⟨a, ha⟩` from `hT f hfT`. Establish `hfM' : σ f ∈ Q` using `hMM' (hDM (hDT ▸ Ideal.subset_span hfT))`.

Rewrite `hfM'` using `[hσ f a ha]`. Establish `hunit : IsUnit (∏ k, u k ^ a k)` using `IsUnit.prod_univ_iff.mpr fun k => ((hu k).unit⁻¹).isUnit.pow _`. Establish `: algebraMap R A f ∈ Q`. Use `Q.mul_mem_left (hunit.unit⁻¹ : Aˣ).1 hfM'` as an intermediate fact. Rewrite `this` using `[← mul_assoc, hunit.val_inv_mul, one_mul]`. Then use the resulting hypothesis.

Rewrite using `[← hQq]`. Conclude with `this`.
-/
theorem exists_relevant_minimalPrime_of_chart {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)}
    (hP : IsMultiHomogIdeal P) (hD : IsMultiHomogIdeal D) (p : (k : K) → ι k)
    (M : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (hM : M ∈ (chartIdeal P p).minimalPrimes)
    (hDM : D ≤ M) :
    ∃ q ∈ P.minimalPrimes, IsRelevant q ∧ D ≤ q := by
  classical
  set R := MvPolynomial (Σ k, ι k) ℂ
  have hMp : M.IsPrime := hM.1.1
  have hcM : chartIdeal P p ≤ M := hM.1.2
  have hX1 : ∀ k, (X ⟨k, p k⟩ - 1 : R) ∈ M := fun k =>
    hcM (Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩))
  have hXM : ∀ k, (X ⟨k, p k⟩ : R) ∉ M := fun k h =>
    hMp.ne_top ((Ideal.eq_top_iff_one _).mpr (by
      have := M.sub_mem h (hX1 k); simpa using this))
  obtain ⟨q, hq, hqM⟩ := Ideal.exists_minimalPrimes_le (le_sup_left.trans hcM : P ≤ M)
  have hqp : q.IsPrime := hq.1.1
  have hPq : P ≤ q := hq.1.2
  set s : R := ∏ k, X ⟨k, p k⟩
  have hsq : s ∉ q := by
    intro h
    obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (p := q)).mp h
    exact hXM k (hqM hk)
  have hdis : Disjoint (Submonoid.powers s : Set R) ↑q :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime s).mpr hsq
  let A := Localization.Away s
  have hu : ∀ k, IsUnit (algebraMap R A (X ⟨k, p k⟩)) := fun k =>
    isUnit_of_dvd_unit (map_dvd (algebraMap R A)
      (Finset.dvd_prod_of_mem (fun k => (X ⟨k, p k⟩ : R)) (Finset.mem_univ k)))
      (IsLocalization.Away.algebraMap_isUnit (S := A) s)
  let u : K → A := fun k => ((hu k).unit⁻¹ : Aˣ)
  have hu1 : ∀ k, u k * algebraMap R A (X ⟨k, p k⟩) = 1 := fun k => (hu k).val_inv_mul
  let σ : R →+* A := eval₂Hom (algebraMap ℂ A) (fun r => u r.1 * algebraMap R A (X r))
  have hσ : ∀ (f : R) (a : K → ℕ), IsMultiHomog f a →
      σ f = (∏ k, u k ^ a k) * algebraMap R A f := by
    intro f a hf
    show eval₂ (algebraMap ℂ A) (fun r => u r.1 * algebraMap R A (X r)) f = _
    rw [eval₂_smul_of_isMultiHomog' (algebraMap ℂ A) hf u (fun r => algebraMap R A (X r))]
    congr 1
    conv_rhs => rw [← eval₂_eta f, eval₂_comp_left]
    congr 1
  let Q : Ideal A := Ideal.map (algebraMap R A) q
  have hQp : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers s) A q hqp hdis
  have hQq : Q.comap (algebraMap R A) = q :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers s) A hqp hdis
  let M' : Ideal R := Q.comap σ
  have : M'.IsPrime := Ideal.comap_isPrime σ Q

  have hs1 : IsUnit (Ideal.Quotient.mk M s) := by
    have : ∀ k, Ideal.Quotient.mk M (X ⟨k, p k⟩) = 1 := fun k => by
      rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk M), ← map_sub,
        Ideal.Quotient.eq_zero_iff_mem]; exact hX1 k
    simp [s, map_prod, this]
  let φ : A →+* R ⧸ M := IsLocalization.Away.lift s hs1
  have hφa : ∀ x : R, φ (algebraMap R A x) = Ideal.Quotient.mk M x := fun x =>
    IsLocalization.Away.lift_eq s hs1 x
  have hφu : ∀ k, φ (u k) = 1 := fun k => by
    have h := congrArg φ (hu1 k)
    rw [map_mul, map_one, hφa] at h
    have hx : Ideal.Quotient.mk M (X ⟨k, p k⟩) = 1 := by
      rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk M), ← map_sub,
        Ideal.Quotient.eq_zero_iff_mem]; exact hX1 k
    rw [hx, mul_one] at h; exact h
  have hφσ : φ.comp σ = Ideal.Quotient.mk M := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [σ, IsScalarTower.algebraMap_apply ℂ R A, hφa]; rfl
    · intro r
      simp [σ, hφa, hφu]
  have hM'M : M' ≤ M := by
    intro g hg
    have hQ : Q ≤ (⊥ : Ideal (R ⧸ M)).comap φ := by
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      simp only [Ideal.mem_comap, hφa, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
      exact hqM hx
    have h0 := hQ hg
    simp only [Ideal.mem_comap, Ideal.mem_bot] at h0
    have : Ideal.Quotient.mk M g = 0 := by rw [← hφσ]; exact h0
    exact Ideal.Quotient.eq_zero_iff_mem.mp this

  have hcM' : chartIdeal P p ≤ M' := by
    refine sup_le ?_ ?_
    · obtain ⟨S, hS, hPS⟩ := hP
      rw [hPS, Ideal.span_le]
      intro f hfS
      obtain ⟨a, ha⟩ := hS f hfS
      show σ f ∈ Q
      rw [hσ f a ha]
      exact Q.mul_mem_left _ (Ideal.mem_map_of_mem _ (hPq (hPS ▸ Ideal.subset_span hfS)))
    · rw [Ideal.span_le]
      rintro _ ⟨k, rfl⟩
      show σ _ ∈ Q
      have : σ (X ⟨k, p k⟩ - 1) = 0 := by
        have hσX : σ (X ⟨k, p k⟩) = u k * algebraMap R A (X ⟨k, p k⟩) := eval₂_X _ _ _
        rw [map_sub, map_one, hσX, hu1, sub_self]
      rw [this]; exact Q.zero_mem
  have hMM' : M ≤ M' := hM.2 ⟨inferInstance, hcM'⟩ hM'M
  refine ⟨q, hq, fun k => ⟨p k, fun h => hXM k (hqM h)⟩, ?_⟩
  obtain ⟨T, hT, hDT⟩ := hD
  rw [hDT, Ideal.span_le]
  intro f hfT
  obtain ⟨a, ha⟩ := hT f hfT
  have hfM' : σ f ∈ Q := hMM' (hDM (hDT ▸ Ideal.subset_span hfT))
  rw [hσ f a ha] at hfM'
  have hunit : IsUnit (∏ k, u k ^ a k) :=
    IsUnit.prod_univ_iff.mpr fun k => ((hu k).unit⁻¹).isUnit.pow _
  have : algebraMap R A f ∈ Q := by
    have := Q.mul_mem_left (hunit.unit⁻¹ : Aˣ).1 hfM'
    rwa [← mul_assoc, hunit.val_inv_mul, one_mul] at this
  rw [← hQq]; exact this

end

end ReciprocityTheory.AnForm.R
