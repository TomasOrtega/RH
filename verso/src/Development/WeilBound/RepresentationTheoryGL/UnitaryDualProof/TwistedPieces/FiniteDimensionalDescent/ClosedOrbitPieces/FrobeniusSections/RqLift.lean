import Mathlib

noncomputable section

namespace PositivityTheory.RgUd.TP.Desc.Piece.PSect

open Module Polynomial

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]

def Iq (A : Type*) [CommRing A] [Algebra k A] (χ : k[X]) (q : ℕ) : Ideal A[X] :=
  Ideal.span {χ.map (algebraMap k A)} ⊔
    Ideal.span {y | ∃ r ∈ (Ideal.span {χ.map (algebraMap k A)}).radical, y = r ^ q}

abbrev Rq (A : Type*) [CommRing A] [Algebra k A] (χ : k[X]) (q : ℕ) : Type _ := A[X] ⧸ Iq A χ q

/- English proof (translation)
Establish `hmon : (χ.map (algebraMap k A)).Monic` using `hχ.map _`. Establish `: Module.Finite A (A[X] ⧸ Ideal.span {χ.map (algebraMap k A)})` using `(AdjoinRoot.powerBasis' hmon).finite`. Establish `hle : Ideal.span {χ.map (algebraMap k A)} ≤ Iq A χ q` using `le_sup_left`. Set `φ` to `Ideal.Quotient.factorₐ A hle`. Establish `hsurj : Function.Surjective φ`.

Introduce `y`. Take `⟨P, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Conclude with `⟨Ideal.Quotient.mk _ P, rfl⟩`. Establish `: Module.Finite A (Rq A χ q)` using `Module.Finite.of_surjective φ.toLinearMap hsurj`. Conclude with `Module.Finite.trans A (Rq A χ q)`.
-/
theorem rq_fin [FiniteDimensional k A] (χ : k[X]) (hχ : χ.Monic) (q : ℕ) :
    FiniteDimensional k (Rq A χ q) := by
  classical
  have hmon : (χ.map (algebraMap k A)).Monic := hχ.map _
  have : Module.Finite A (A[X] ⧸ Ideal.span {χ.map (algebraMap k A)}) := (AdjoinRoot.powerBasis' hmon).finite
  have hle : Ideal.span {χ.map (algebraMap k A)} ≤ Iq A χ q := le_sup_left
  let φ := Ideal.Quotient.factorₐ A hle
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk _ P, rfl⟩
  have : Module.Finite A (Rq A χ q) := Module.Finite.of_surjective φ.toLinearMap hsurj
  exact Module.Finite.trans A (Rq A χ q)

/- English proof (translation)
Take `⟨P, rfl⟩` from `Ideal.Quotient.mk_surjective r`. Take `⟨m, hm⟩` from `hr`. Rewrite `hm`, the goal using `[← map_pow, Ideal.Quotient.eq_zero_iff_mem]`. Break down `Nat.eq_zero_or_pos q with rfl | hq` into its components or cases. Rewrite using `[pow_zero]`.

Conclude with `Ideal.mem_sup_right (Ideal.subset_span ⟨0, Ideal.zero_mem _, (pow_zero _).symm⟩)`. Establish `hle : Iq A χ q ≤ (Ideal.span {χ.map (algebraMap k A)}).radical`. Use `sup_le Ideal.le_radical ?_` and prove the remaining obligations. Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨r, hr, rfl⟩`.

Conclude with `Ideal.pow_mem_of_mem _ hr q hq`. Establish `hP : P ∈ (Ideal.span {χ.map (algebraMap k A)}).radical` using `(Ideal.radical_isRadical _) ⟨m, hle hm⟩`. Conclude with `Ideal.mem_sup_right (Ideal.subset_span ⟨P, hP, rfl⟩)`.
-/
theorem rq_nil (χ : k[X]) (q : ℕ) (r : Rq A χ q) (hr : IsNilpotent r) : r ^ q = 0 := by
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective r
  obtain ⟨m, hm⟩ := hr
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem] at hm ⊢
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · rw [pow_zero]
    exact Ideal.mem_sup_right (Ideal.subset_span ⟨0, Ideal.zero_mem _, (pow_zero _).symm⟩)
  · have hle : Iq A χ q ≤ (Ideal.span {χ.map (algebraMap k A)}).radical := by
      refine sup_le Ideal.le_radical ?_
      rw [Ideal.span_le]
      rintro _ ⟨r, hr, rfl⟩
      exact Ideal.pow_mem_of_mem _ hr q hq
    have hP : P ∈ (Ideal.span {χ.map (algebraMap k A)}).radical :=
      (Ideal.radical_isRadical _) ⟨m, hle hm⟩
    exact Ideal.mem_sup_right (Ideal.subset_span ⟨P, hP, rfl⟩)
/- English proof (translation)
Use `Fintype.ofFinite ι` as an intermediate fact. Use `⟨fun J => ?_⟩` and prove the remaining obligations. Establish `hsurj : ∀ i, Function.Surjective (Pi.evalRingHom R i)` using `fun i y => ⟨Pi.single i y, by simp⟩`. Establish `hgen : ∀ i, ∃ a : R i, J.map (Pi.evalRingHom R i) = Ideal.span {a}` using `fun i => by`. Take `⟨a, ha⟩` from `(hR i).principal (J.map (Pi.evalRingHom R i))`.

Conclude with `⟨a, ha⟩`. Use `choose g hg using hgen`. Establish `hgJ : g ∈ J`. Establish `hpre : ∀ i, ∃ h ∈ J, h i = g i` using `fun i => by`. Establish `hm : g i ∈ J.map (Pi.evalRingHom R i)`.

Rewrite using `[hg i]`. Conclude with `Ideal.subset_span rfl`. Take `⟨h, hh, he⟩` from `(Ideal.mem_map_iff_of_surjective _ (hsurj i)).mp hm`. Conclude with `⟨h, hh, he⟩`. Use `choose h hh he using hpre`.

Establish `e : g = ∑ i, Pi.single i (1 : R i) * h i`. Use function extensionality and compare the values at `j`. Simplify using `only [Finset.sum_apply, Pi.mul_apply]`. Rewrite using `[Finset.sum_eq_single j]`. Rewrite using `[Pi.single_eq_same, one_mul, he]`.

Introduce `i _ hij`. Rewrite using `[Pi.single_eq_of_ne (Ne.symm hij), zero_mul]`. Introduce `hj`. Conclude with `absurd (Finset.mem_univ j) hj`. Rewrite using `[e]`.

Conclude with `J.sum_mem (fun i _ => J.mul_mem_left _ (hh i))`. Use `⟨g, le_antisymm ?_ ?_⟩` and prove the remaining obligations. Introduce `x hx`. Establish `hc : ∀ i, ∃ c : R i, c * g i = x i` using `fun i => by`. Establish `hm : x i ∈ J.map (Pi.evalRingHom R i)` using `Ideal.mem_map_of_mem _ hx`.

Rewrite `hm` using `[hg i]`. Conclude with `Ideal.mem_span_singleton'.mp hm`. Use `choose c hc using hc`. Conclude with `Ideal.mem_span_singleton'.mpr ⟨c, funext hc⟩`. Conclude with `(Ideal.span_le).mpr (Set.singleton_subset_iff.mpr hgJ)`.
-/
private theorem isPrincipalIdealRing_pi {ι : Type*} [Finite ι] (R : ι → Type*) [∀ i, CommRing (R i)]
    (hR : ∀ i, IsPrincipalIdealRing (R i)) : IsPrincipalIdealRing (∀ i, R i) := by
  classical
  have := Fintype.ofFinite ι
  refine ⟨fun J => ?_⟩
  have hsurj : ∀ i, Function.Surjective (Pi.evalRingHom R i) := fun i y => ⟨Pi.single i y, by simp⟩
  have hgen : ∀ i, ∃ a : R i, J.map (Pi.evalRingHom R i) = Ideal.span {a} := fun i => by
    obtain ⟨a, ha⟩ := (hR i).principal (J.map (Pi.evalRingHom R i))
    exact ⟨a, ha⟩
  choose g hg using hgen
  have hgJ : g ∈ J := by
    have hpre : ∀ i, ∃ h ∈ J, h i = g i := fun i => by
      have hm : g i ∈ J.map (Pi.evalRingHom R i) := by
        rw [hg i]
        exact Ideal.subset_span rfl
      obtain ⟨h, hh, he⟩ := (Ideal.mem_map_iff_of_surjective _ (hsurj i)).mp hm
      exact ⟨h, hh, he⟩
    choose h hh he using hpre
    have e : g = ∑ i, Pi.single i (1 : R i) * h i := by
      funext j
      simp only [Finset.sum_apply, Pi.mul_apply]
      rw [Finset.sum_eq_single j]
      · rw [Pi.single_eq_same, one_mul, he]
      · intro i _ hij
        rw [Pi.single_eq_of_ne (Ne.symm hij), zero_mul]
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    rw [e]
    exact J.sum_mem (fun i _ => J.mul_mem_left _ (hh i))
  refine ⟨g, le_antisymm ?_ ?_⟩
  · intro x hx
    have hc : ∀ i, ∃ c : R i, c * g i = x i := fun i => by
      have hm : x i ∈ J.map (Pi.evalRingHom R i) := Ideal.mem_map_of_mem _ hx
      rw [hg i] at hm
      exact Ideal.mem_span_singleton'.mp hm
    choose c hc using hc
    exact Ideal.mem_span_singleton'.mpr ⟨c, funext hc⟩
  · exact (Ideal.span_le).mpr (Set.singleton_subset_iff.mpr hgJ)

/- English proof (translation)
Establish `hA : IsArtinianRing A` using `IsArtinianRing.of_finite k A`. Establish `hPI : IsPrincipalIdealRing ((I : MaximalSpectrum A) → (A ⧸ I.asIdeal)[X])` using `isPrincipalIdealRing_pi _ (fun I => by`. Use `I.isMaximal` as an intermediate fact. Use `letI : Field (A ⧸ I.asIdeal) := Ideal.Quotient.field _`. Conclude with `EuclideanDomain.to_principal_ideal_domain)`.

Establish `hPI' : IsPrincipalIdealRing ((∀ I : MaximalSpectrum A, A ⧸ I.asIdeal)[X])` using `IsPrincipalIdealRing.of_surjective (Polynomial.piEquiv (fun I : MaximalSpectrum A => A ⧸ I.asIdeal)).symm (Polynomial.piEquiv _).symm.surjective`. Establish `hAX : IsPrincipalIdealRing A[X]` using `IsPrincipalIdealRing.of_surjective (Polynomial.mapEquiv (IsArtinianRing.equivPi A).symm.toRingEquiv) (Polynomial.mapEquiv _).surjective`. Conclude with `IsPrincipalIdealRing.of_surjective (Ideal.Quotient.mk (Iq A χ q)) Ideal.Quotient.mk_surjective`.
-/
theorem rq_pir [FiniteDimensional k A] [IsReduced A] (χ : k[X]) (q : ℕ) :
    IsPrincipalIdealRing (Rq A χ q) := by
  classical
  have hA : IsArtinianRing A := IsArtinianRing.of_finite k A
  have hPI : IsPrincipalIdealRing ((I : MaximalSpectrum A) → (A ⧸ I.asIdeal)[X]) :=
    isPrincipalIdealRing_pi _ (fun I => by
      have := I.isMaximal
      letI : Field (A ⧸ I.asIdeal) := Ideal.Quotient.field _
      exact EuclideanDomain.to_principal_ideal_domain)
  have hPI' : IsPrincipalIdealRing ((∀ I : MaximalSpectrum A, A ⧸ I.asIdeal)[X]) :=
    IsPrincipalIdealRing.of_surjective (Polynomial.piEquiv (fun I : MaximalSpectrum A => A ⧸ I.asIdeal)).symm
      (Polynomial.piEquiv _).symm.surjective
  have hAX : IsPrincipalIdealRing A[X] :=
    IsPrincipalIdealRing.of_surjective (Polynomial.mapEquiv (IsArtinianRing.equivPi A).symm.toRingEquiv)
      (Polynomial.mapEquiv _).surjective
  exact IsPrincipalIdealRing.of_surjective (Ideal.Quotient.mk (Iq A χ q)) Ideal.Quotient.mk_surjective

/- English proof (translation)
Take `⟨P, rfl⟩` from `Ideal.Quotient.mk_surjective r`. Break down `subsingleton_or_nontrivial A with hA | hA` into its components or cases. Conclude with `⟨0, by congr 1; exact Subsingleton.elim _ _⟩`. Establish `hmon : (χ.map (algebraMap k A)).Monic` using `hχ.map _`. Establish `hmem : P - P %ₘ χ.map (algebraMap k A) ∈ Iq A χ q`.

Establish `e : P - P %ₘ χ.map (algebraMap k A) = χ.map (algebraMap k A) * (P /ₘ χ.map (algebraMap k A))`. Establish `h` using `modByMonic_add_div P (χ.map (algebraMap k A))`. Take the linear combination `-h`. Rewrite using `[e]`. Conclude with `Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))`.

Establish `hdeg : (P %ₘ χ.map (algebraMap k A)).degree < d`. Combine the equalities or inequalities in the displayed calculation. Use `⟨fun l => (P %ₘ χ.map (algebraMap k A)).coeff l, ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.Quotient.eq.mpr hmem]`. Use `congr 1`.

Rewrite using `[show (∑ l : Fin d, C ((P %ₘ χ.map (algebraMap k A)).coeff (l : ℕ)) * X ^ (l : ℕ)) = ∑ i ∈ Finset.range d, C ((P %ₘ χ.map (algebraMap k A)).coeff i) * X ^ i from (Finset.sum_range (fun i => C ((P %ₘ χ.map (algebraMap k A)).coeff i) * X ^ i)).symm]`. Distinguish the cases in `h0 : P %ₘ χ.map (algebraMap k A) = 0`. Rewrite using `[h0]`. Simplify using the standard rewrite rules. Establish `h` using `as_sum_range' _ d ((natDegree_lt_iff_degree_lt h0).mpr hdeg)`.

Simplify using `only [← C_mul_X_pow_eq_monomial] at h`. Conclude with `h`.
-/
theorem rq_rep (χ : k[X]) (hχ : χ.Monic) (q d : ℕ) (hd : χ.natDegree ≤ d) (r : Rq A χ q) :
    ∃ a : Fin d → A, r = Ideal.Quotient.mk _ (∑ l : Fin d, C (a l) * X ^ (l : ℕ)) := by
  classical
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective r
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact ⟨0, by congr 1; exact Subsingleton.elim _ _⟩
  have hmon : (χ.map (algebraMap k A)).Monic := hχ.map _
  have hmem : P - P %ₘ χ.map (algebraMap k A) ∈ Iq A χ q := by
    have e : P - P %ₘ χ.map (algebraMap k A) = χ.map (algebraMap k A) * (P /ₘ χ.map (algebraMap k A)) := by
      have h := modByMonic_add_div P (χ.map (algebraMap k A))
      linear_combination -h
    rw [e]
    exact Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
  have hdeg : (P %ₘ χ.map (algebraMap k A)).degree < d :=
    calc (P %ₘ χ.map (algebraMap k A)).degree < (χ.map (algebraMap k A)).degree := degree_modByMonic_lt _ hmon
      _ ≤ (χ.map (algebraMap k A)).natDegree := degree_le_natDegree
      _ ≤ d := by exact_mod_cast natDegree_map_le.trans hd
  refine ⟨fun l => (P %ₘ χ.map (algebraMap k A)).coeff l, ?_⟩
  rw [Ideal.Quotient.eq.mpr hmem]
  congr 1
  rw [show (∑ l : Fin d, C ((P %ₘ χ.map (algebraMap k A)).coeff (l : ℕ)) * X ^ (l : ℕ)) =
      ∑ i ∈ Finset.range d, C ((P %ₘ χ.map (algebraMap k A)).coeff i) * X ^ i from
    (Finset.sum_range (fun i => C ((P %ₘ χ.map (algebraMap k A)).coeff i) * X ^ i)).symm]
  by_cases h0 : P %ₘ χ.map (algebraMap k A) = 0
  · rw [h0]
    simp
  · have h := as_sum_range' _ d ((natDegree_lt_iff_degree_lt h0).mpr hdeg)
    simp only [← C_mul_X_pow_eq_monomial] at h
    exact h

/- English proof (translation)
Set `f : A[X] →+* B` to `Polynomial.eval₂RingHom' ι.toRingHom x hc`. Establish `hf : ∀ P : A[X], f P = P.eval₂ ι.toRingHom x` using `fun P => rfl`. Establish `hχ0 : f (χ.map (algebraMap k A)) = 0`. Rewrite using `[hf, Polynomial.eval₂_map]`. Establish `e : ι.toRingHom.comp (algebraMap k A) = algebraMap k B`.

Use extensionality with `c`. Conclude with `ι.commutes c`. Rewrite using `[e, ← Polynomial.aeval_def, hχ]`. Establish `hspan : ∀ P ∈ Ideal.span {χ.map (algebraMap k A)}, f P = 0`. Introduce `P hP`.

Take `⟨Q, rfl⟩` from `Ideal.mem_span_singleton'.mp hP`. Rewrite using `[map_mul, hχ0, mul_zero]`. Establish `hle : Iq A χ q ≤ RingHom.ker f`. Unfold `Iq`. Apply `sup_le` to reduce the goal to its premises.

Introduce `P hP`. Conclude with `(RingHom.mem_ker).mpr (hspan P hP)`. Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨r, hr, rfl⟩`. Take `⟨m, hm⟩` from `hr`.

Establish `hnil : IsNilpotent (r.eval₂ ι.toRingHom x)` using `⟨m, by rw [← hf, ← map_pow, hspan _ hm]⟩`. Rewrite using `[SetLike.mem_coe, RingHom.mem_ker, map_pow, hf]`. Conclude with `hq r hnil`. Set `F : A[X] →ₐ[k] B` to `{ f with commutes' := fun c => by show Polynomial.eval₂ ι.toRingHom x (algebraMap k A[X] c) = algebraMap k B c`. Rewrite using `[Polynomial.algebraMap_apply, Polynomial.eval₂_C]`.

Conclude with `ι.commutes c }`. Conclude with `⟨Ideal.Quotient.liftₐ _ F (fun a ha => hle ha), fun P => rfl⟩`.
-/
theorem rq_lift {B : Type*} [Ring B] [Algebra k B] (ι : A →ₐ[k] B) (x : B) (hc : ∀ a, Commute (ι a) x)
    (χ : k[X]) (hχ : aeval x χ = 0) (q : ℕ)
    (hq : ∀ P : A[X], IsNilpotent (P.eval₂ ι.toRingHom x) → (P.eval₂ ι.toRingHom x) ^ q = 0) :
    ∃ ρ : Rq A χ q →ₐ[k] B, ∀ P : A[X], ρ (Ideal.Quotient.mk _ P) = P.eval₂ ι.toRingHom x := by
  let f : A[X] →+* B := Polynomial.eval₂RingHom' ι.toRingHom x hc
  have hf : ∀ P : A[X], f P = P.eval₂ ι.toRingHom x := fun P => rfl
  have hχ0 : f (χ.map (algebraMap k A)) = 0 := by
    rw [hf, Polynomial.eval₂_map]
    have e : ι.toRingHom.comp (algebraMap k A) = algebraMap k B := by
      ext c
      exact ι.commutes c
    rw [e, ← Polynomial.aeval_def, hχ]
  have hspan : ∀ P ∈ Ideal.span {χ.map (algebraMap k A)}, f P = 0 := by
    intro P hP
    obtain ⟨Q, rfl⟩ := Ideal.mem_span_singleton'.mp hP
    rw [map_mul, hχ0, mul_zero]
  have hle : Iq A χ q ≤ RingHom.ker f := by
    unfold Iq
    apply sup_le
    · intro P hP
      exact (RingHom.mem_ker).mpr (hspan P hP)
    · rw [Ideal.span_le]
      rintro _ ⟨r, hr, rfl⟩
      obtain ⟨m, hm⟩ := hr
      have hnil : IsNilpotent (r.eval₂ ι.toRingHom x) := ⟨m, by rw [← hf, ← map_pow, hspan _ hm]⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, map_pow, hf]
      exact hq r hnil
  let F : A[X] →ₐ[k] B :=
    { f with
      commutes' := fun c => by
        show Polynomial.eval₂ ι.toRingHom x (algebraMap k A[X] c) = algebraMap k B c
        rw [Polynomial.algebraMap_apply, Polynomial.eval₂_C]
        exact ι.commutes c }
  exact ⟨Ideal.Quotient.liftₐ _ F (fun a ha => hle ha), fun P => rfl⟩

end PositivityTheory.RgUd.TP.Desc.Piece.PSect
