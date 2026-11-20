import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ExistsNonzeroLowCocycle
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocFlat
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.IsInternalCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocRho

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

/- English proof (translation)
Use `algebraize [f]`. Establish `h0 : ∑ i : Fin 1, (fun _ : Fin 1 => a) i • (fun _ : Fin 1 => (1 : R)) i = 0`. Rewrite using `[Fin.sum_univ_one, Algebra.smul_def, mul_one]`. Conclude with `ha`. Take `⟨k, c, y, hy, hc⟩` from `Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := A) (M := R) (f := fun _ : Fin 1 => a) (x := fun _ : Fin 1 => (1 : R)) h0`.

Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Establish `h1 : (1 : R) = ∑ j, c 0 j • y j` using `hy 0`. Establish `hone : (1 : R) ∈ maximalIdeal R`. Rewrite using `[h1]`.

Use `Ideal.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def]`. Use `Ideal.mul_mem_right _ _ ?_` and prove the remaining obligations. Assume the negation of the conclusion as `h'`. Use `hne (c 0 j) h' ?_` and prove the remaining obligations.

Establish `h2 : a * c 0 j = 0`. Use `hc j` as an intermediate fact. Rewrite `this` using `[Fin.sum_univ_one]`. Then use the resulting hypothesis. Rewrite `h2` using `[mul_comm]`. Then use the resulting hypothesis. Conclude with `(maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 hone)`.
-/
private theorem ann_of_flat {A R : Type} [CommRing A] [CommRing R] [IsLocalRing R] (f : A →+* R) (hf : f.Flat)
    {a : A} (ha : f a = 0) : ∃ s, s ∉ (maximalIdeal R).comap f ∧ s * a = 0 := by
  algebraize [f]
  have h0 : ∑ i : Fin 1, (fun _ : Fin 1 => a) i • (fun _ : Fin 1 => (1 : R)) i = 0 := by
    rw [Fin.sum_univ_one, Algebra.smul_def, mul_one]
    exact ha
  obtain ⟨k, c, y, hy, hc⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero
    (R := A) (M := R) (f := fun _ : Fin 1 => a) (x := fun _ : Fin 1 => (1 : R)) h0
  by_contra hne
  push_neg at hne
  have h1 : (1 : R) = ∑ j, c 0 j • y j := hy 0
  have hone : (1 : R) ∈ maximalIdeal R := by
    rw [h1]
    refine Ideal.sum_mem _ fun j _ => ?_
    rw [Algebra.smul_def]
    refine Ideal.mul_mem_right _ _ ?_
    by_contra h'
    refine hne (c 0 j) h' ?_
    have h2 : a * c 0 j = 0 := by
      have := hc j
      rwa [Fin.sum_univ_one] at this
    rwa [mul_comm] at h2
  exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 hone)

/- English proof (translation)
Take `⟨t, rfl⟩` from `hI`. Use `choose! s hs hsa using fun g (hg : g ∈ t) => h g (Ideal.subset_span hg)`. Use `⟨∏ g ∈ t, s g, ?_, fun a ha => ?_⟩` and prove the remaining obligations. Introduce `hmem`. Take `⟨g, hg, hgx⟩` from `Ideal.IsPrime.prod_mem_iff.1 hmem`.

Conclude with `hs g hg hgx`. Proceed by induction on `ha using Submodule.span_induction with`. Consider the case `mem g hg => rw [← Finset.prod_erase_mul _ _ hg, mul_assoc, hsa g hg, mul_zero]`. Consider the case `zero => simp`. Consider the case `add u v _ _ hu hv => rw [mul_add, hu, hv, add_zero]`.

Consider the case `smul r u _ hu => rw [smul_eq_mul, mul_left_comm, hu, mul_zero]`.
-/
private theorem ann_ideal {A : Type} [CommRing A] (x : Ideal A) [hx : x.IsPrime] (I : Ideal A) (hI : I.FG)
    (h : ∀ a ∈ I, ∃ s, s ∉ x ∧ s * a = 0) : ∃ s, s ∉ x ∧ ∀ a ∈ I, s * a = 0 := by
  classical
  obtain ⟨t, rfl⟩ := hI
  choose! s hs hsa using fun g (hg : g ∈ t) => h g (Ideal.subset_span hg)
  refine ⟨∏ g ∈ t, s g, ?_, fun a ha => ?_⟩
  · intro hmem
    obtain ⟨g, hg, hgx⟩ := Ideal.IsPrime.prod_mem_iff.1 hmem
    exact hs g hg hgx
  · induction ha using Submodule.span_induction with
    | mem g hg => rw [← Finset.prod_erase_mul _ _ hg, mul_assoc, hsa g hg, mul_zero]
    | zero => simp
    | add u v _ _ hu hv => rw [mul_add, hu, hv, add_zero]
    | smul r u _ hu => rw [smul_eq_mul, mul_left_comm, hu, mul_zero]

/- English proof (translation)
Introduce `l _ O _ _ _ _ F C₀ hF S x L hx E hg`. Take `⟨hfl, hmax, hB⟩` from `UpperTheory.V.Fr.loc_flat hF (Or.inr rfl) S x L`. Establish `hA : IsNoetherianRing S.A` using `(UpperTheory.V.Fr.gr_A hF (Or.inr rfl) S).2.2.2.2.2.1`. Establish `h0 : L.ρ.ee ≤ ⊥`. Rewrite using `[E.ee, Ideal.span_le]`.

Introduce and unpack `_ ⟨i, rfl⟩`. Use `i.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `h1 : S.u.ee ≤ L.im ⊥` using `((UpperTheory.V.Fr.loc_rho hF (Or.inr rfl) S x L).2.2.1 ⊥).2.2.1 h0`. Use `haveI := hmax.isPrime`.

Take `⟨s, hs, hs0⟩` from `ann_ideal x S.u.ee (IsNoetherian.noetherian _) fun a ha => by`. Use `ann_of_flat (L.ι : S.A →+* L.R) hfl (a := a) (h1 ha)` as an intermediate fact. Rewrite `this` using `[L.lies]`. Then use the resulting hypothesis. Establish `hxB : (⟨x, hmax.isPrime⟩ : PrimeSpectrum S.A) ∈ S.BB` using `⟨hB, hx⟩`. Establish `hcl` using `(UpperTheory.V.Fr.preconnected_rank_three hF S).2.2 hxB`.

Take `⟨p, hp1, -, hp2⟩` from `mem_closure_iff.1 hcl (PrimeSpectrum.basicOpen s) (PrimeSpectrum.basicOpen s).isOpen hs`. Use `hp2 fun a ha => ?_` and prove the remaining obligations. Establish `h2 : s * a ∈ p.asIdeal`. Rewrite using `[hs0 a ha]`. Conclude with `zero_mem _`.

Conclude with `(p.isPrime.mem_or_mem h2).resolve_left hp1`.
-/
theorem UpperTheory.V.Fr.gpos :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ}, F.Ok C₀ → ∀ S : Space O F 3, ∀ (x : Ideal S.A) (L : S.Loc x), ¬ S.u.triP ≤ x → ∀ E : L.EPres, E.g ≠ 0 := by
  intro l _ O _ _ _ _ F C₀ hF S x L hx E hg
  obtain ⟨hfl, hmax, hB⟩ := UpperTheory.V.Fr.loc_flat hF (Or.inr rfl) S x L
  have hA : IsNoetherianRing S.A := (UpperTheory.V.Fr.gr_A hF (Or.inr rfl) S).2.2.2.2.2.1
  have h0 : L.ρ.ee ≤ ⊥ := by
    rw [E.ee, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    have := i.2
    omega
  have h1 : S.u.ee ≤ L.im ⊥ := ((UpperTheory.V.Fr.loc_rho hF (Or.inr rfl) S x L).2.2.1 ⊥).2.2.1 h0
  haveI := hmax.isPrime
  obtain ⟨s, hs, hs0⟩ := ann_ideal x S.u.ee (IsNoetherian.noetherian _) fun a ha => by
    have := ann_of_flat (L.ι : S.A →+* L.R) hfl (a := a) (h1 ha)
    rwa [L.lies] at this
  have hxB : (⟨x, hmax.isPrime⟩ : PrimeSpectrum S.A) ∈ S.BB := ⟨hB, hx⟩
  have hcl := (UpperTheory.V.Fr.preconnected_rank_three hF S).2.2 hxB
  obtain ⟨p, hp1, -, hp2⟩ := mem_closure_iff.1 hcl (PrimeSpectrum.basicOpen s)
    (PrimeSpectrum.basicOpen s).isOpen hs
  refine hp2 fun a ha => ?_
  have h2 : s * a ∈ p.asIdeal := by
    rw [hs0 a ha]
    exact zero_mem _
  exact (p.isPrime.mem_or_mem h2).resolve_left hp1
