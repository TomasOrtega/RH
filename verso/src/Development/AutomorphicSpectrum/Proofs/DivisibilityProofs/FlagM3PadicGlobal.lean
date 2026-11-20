import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CycNumIntAndComb
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FinitePlacesModelFamilyStatement
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num.PlacesFlagM3

/- English proof (translation)
Use `(Ideal.finite_minimalPrimes_of_isNoetherianRing _ (P ⊔ Ideal.span {f})).subset ?_` and prove the remaining obligations. Introduce `W hW`. Assume the negation of the conclusion as `h`. Apply `hW` to reduce the goal to its premises. Unfold `divCycle`.

Rewrite using `[dif_neg (fun h' => h h'.1)]`.
-/
theorem divCycle_support_finite {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {O : Type} [CommRing O] [IsNoetherianRing O] (P : Ideal (MRing ι O)) (f : MRing ι O) :
    (Function.support (divCycle P f)).Finite := by
  refine (Ideal.finite_minimalPrimes_of_isNoetherianRing _ (P ⊔ Ideal.span {f})).subset ?_
  intro W hW
  by_contra h
  apply hW
  unfold divCycle
  rw [dif_neg (fun h' => h h'.1)]

/- English proof (translation)
Unfold `cycEval ratDiv`. Simplify using `only [sub_mul]`. Use `finsum_sub_distrib ?_ ?_` and prove the remaining obligations. Conclude with `(divCycle_support_finite P f).subset (Function.support_mul_subset_left _ _)`. Conclude with `(divCycle_support_finite P g).subset (Function.support_mul_subset_left _ _)`.
-/
theorem cycEval_ratDiv {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {O : Type} [CommRing O] [IsNoetherianRing O] (n : Ideal (MRing ι O) → ℤ) (P : Ideal (MRing ι O))
    (f g : MRing ι O) :
    cycEval n (ratDiv P f g) = cycEval n (divCycle P f) - cycEval n (divCycle P g) := by
  unfold cycEval ratDiv
  simp only [sub_mul]
  refine finsum_sub_distrib ?_ ?_
  · exact (divCycle_support_finite P f).subset (Function.support_mul_subset_left _ _)
  · exact (divCycle_support_finite P g).subset (Function.support_mul_subset_left _ _)

section Numbers

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Establish `hint` using `fun Z hZ H => (cycNum_int_and_comb O K ι (Fin r ⊕ Fin r) (Sum.elim T.x T.x') Q).1 Z hZ H`. Unfold `LocPair.ck pairNum`. Use `push_cast`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[cycEval_ratDiv, hint _ (divCycle_support_finite P _), hint _ (divCycle_support_finite P _)]`.

Use `push_cast`. Both sides reduce to the same expression.
-/
theorem ck_cast {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {r : ℕ}
    (T : LocPair ι O (Fin r)) (P : Ideal (MRing ι O)) (k : ℕ) (Q : List (K → ℤ)) :
    ((T.ck P k Q : ℤ) : ℝ) = ∑ i, (cycNum (divCycle P (T.f i)) (Sum.elim T.x T.x')
        (MvPolynomial.map (Int.castRingHom ℝ) (psumExpansion r k i)) Q -
      cycNum (divCycle P (T.g i)) (Sum.elim T.x T.x')
        (MvPolynomial.map (Int.castRingHom ℝ) (psumExpansion r k i)) Q) := by
  have hint := fun Z hZ H =>
    (cycNum_int_and_comb O K ι (Fin r ⊕ Fin r) (Sum.elim T.x T.x') Q).1 Z hZ H
  unfold LocPair.ck pairNum
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [cycEval_ratDiv, hint _ (divCycle_support_finite P _), hint _ (divCycle_support_finite P _)]
  push_cast
  rfl

omit [Fintype K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
Establish `h` using `hH (mem_support_iff.mp hμ)`. Unfold `classList`. Simplify using `[Finsupp.card_toMultiset]`. Rewrite using `[← h, Finsupp.weight_apply]`. Simplify using `[Finsupp.sum]`.
-/
theorem length_classList {σ : Type} (cls : σ → K → ℤ) {H : MvPolynomial σ ℝ} {e : ℕ}
    (hH : H.IsHomogeneous e) {μ : σ →₀ ℕ} (hμ : μ ∈ H.support) : (classList cls μ).length = e := by
  have h := hH (mem_support_iff.mp hμ)
  unfold classList
  simp [Finsupp.card_toMultiset]
  rw [← h, Finsupp.weight_apply]
  simp [Finsupp.sum]

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Unfold `cycNum`. Simplify using `only [Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun μ hμ => ?_` and prove the remaining obligations. Rewrite using `[h _ (by rw [List.length_append, length_classList cls hH hμ, he])]`.

Use `push_cast`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cycNum_transfer {O₀ : Type} [CommRing O₀] [IsDomain O₀] [IsDiscreteValuationRing O₀]
    {Λ : Type} [Fintype Λ] {O : Λ → Type} [∀ l, CommRing (O l)] [∀ l, IsDomain (O l)]
    [∀ l, IsDiscreteValuationRing (O l)] (Z₀ : Ideal (MRing ι O₀) → ℤ)
    (Z : ∀ l, Ideal (MRing ι (O l)) → ℤ) (fd : Λ → ℕ) (D : ℕ)
    (h : ∀ L : List (K → ℤ), L.length = D → cycList Z₀ L = ∑ l, (fd l : ℤ) * cycList (Z l) L)
    {σ : Type} (cls : σ → K → ℤ) {H : MvPolynomial σ ℝ} {e : ℕ} (hH : H.IsHomogeneous e)
    (Q : List (K → ℤ)) (he : e + Q.length = D) :
    cycNum Z₀ cls H Q = ∑ l, (fd l : ℝ) * cycNum (Z l) cls H Q := by
  unfold cycNum
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  rw [h _ (by rw [List.length_append, length_classList cls hH hμ, he])]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

/- English proof (translation)
Unfold `bracket`. Establish `hl : ∀ τ' : Ψ ⊕ Ψ, (liePs (N` using `N) j (k - 1) τ').IsHomogeneous (k - 1) := by`. Introduce `τ'`. Consider the cases of `τ' with`. Consider the case `inl t`.

Use `IsHomogeneous.sum _ _ _ fun i _ => ?_` and prove the remaining obligations. Simplify using `using (isHomogeneous_X ℝ (t, i)).pow (k - 1)`. Consider the case `inr t`. Use `IsHomogeneous.sum _ _ _ fun i _ => ?_` and prove the remaining obligations. Use `((isHomogeneous_C (Ψ × Fin N) (-1 : ℝ)).mul (isHomogeneous_X ℝ (t, i))).pow (k - 1)` as an intermediate fact.

Simplify using `using this`. Establish `hs : (∑ τ', C (co φ p k (Sum.inl τ) τ') * liePs (N` using `N) j (k - 1) τ').IsHomogeneous (k - 1) := by`. Use `IsHomogeneous.sum _ _ _ fun τ' _ => ?_` and prove the remaining obligations. Simplify using `using (isHomogeneous_C (Ψ × Fin N) _).mul (hl τ')`. Simplify using `using (isHomogeneous_C (Ψ × Fin N) (k : ℝ)).mul hs`.
-/
theorem bracket_isHomogeneous (j : ℕ) (φ : Equiv.Perm (Ψ ⊕ Ψ)) (p k : ℕ) (τ : Ψ) :
    (bracket (N := N) j φ p k τ).IsHomogeneous (k - 1) := by
  unfold bracket
  have hl : ∀ τ' : Ψ ⊕ Ψ, (liePs (N := N) j (k - 1) τ').IsHomogeneous (k - 1) := by
    intro τ'
    cases τ' with
    | inl t =>
      refine IsHomogeneous.sum _ _ _ fun i _ => ?_
      simpa using (isHomogeneous_X ℝ (t, i)).pow (k - 1)
    | inr t =>
      refine IsHomogeneous.sum _ _ _ fun i _ => ?_
      have := ((isHomogeneous_C (Ψ × Fin N) (-1 : ℝ)).mul (isHomogeneous_X ℝ (t, i))).pow (k - 1)
      simpa using this
  have hs : (∑ τ', C (co φ p k (Sum.inl τ) τ') * liePs (N := N) j (k - 1) τ').IsHomogeneous (k - 1) := by
    refine IsHomogeneous.sum _ _ _ fun τ' _ => ?_
    simpa using (isHomogeneous_C (Ψ × Fin N) _).mul (hl τ')
  simpa using (isHomogeneous_C (Ψ × Fin N) (k : ℝ)).mul hs

end Numbers

section Transfer

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

/- English proof (translation)
Introduce `τ k hk Q hQ`. Establish `hQ' : k - 1 + Q.length = D` using `by omega`. Establish `hloc'` using `fun l => hloc l τ k hk Q hQ`. Rewrite using `[cycNum_transfer _ _ fd D hp _ (bracket_isHomogeneous j φ p k τ) Q hQ', ck_cast]`. Establish `hG : ∀ i, (MvPolynomial.map (Int.castRingHom ℝ) (psumExpansion N k i)).IsHomogeneous (k - 1)` using `fun i => (isHomogeneous_psumExpansion N k i).map _`.

Establish `hterm : ∀ l, cycNum (divCycle (P l) (C (p : O l))) T₀.x (bracket j φ p k τ) Q = (((((T l).comp fun i : Fin N => (τ, i)).ck (P l) k Q : ℤ)) : ℝ)`. Introduce `l`. Rewrite using `[hloc' l, hx l]`. Simplify using `only [hterm, ck_cast, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `e₁` using `cycNum_transfer _ _ fd D (hf (τ, i)) (Sum.elim (T₀.x ∘ fun i : Fin N => (τ, i)) (T₀.x' ∘ fun i : Fin N => (τ, i))) (hG i) Q hQ'`. Establish `e₂` using `cycNum_transfer _ _ fd D (hg (τ, i)) (Sum.elim (T₀.x ∘ fun i : Fin N => (τ, i)) (T₀.x' ∘ fun i : Fin N => (τ, i))) (hG i) Q hQ'`. Simplify using `only [LocPair.comp, Function.comp_apply, hx, hx']`. Rewrite using `[e₁, e₂, ← Finset.sum_sub_distrib]`.

Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem flag_m3_of_places {O₀ : Type} [CommRing O₀] [IsDomain O₀] [IsDiscreteValuationRing O₀]
    {Λ : Type} [Fintype Λ] {O : Λ → Type} [∀ l, CommRing (O l)] [∀ l, IsDomain (O l)]
    [∀ l, IsDiscreteValuationRing (O l)] (P₀ : Ideal (MRing ι O₀)) (P : ∀ l, Ideal (MRing ι (O l)))
    (fd : Λ → ℕ) (D p j : ℕ) (φ : Equiv.Perm (Ψ ⊕ Ψ)) (T₀ : LocPair ι O₀ (Ψ × Fin N))
    (T : ∀ l, LocPair ι (O l) (Ψ × Fin N)) (hx : ∀ l, (T l).x = T₀.x) (hx' : ∀ l, (T l).x' = T₀.x')
    (hf : ∀ i (L : List (K → ℤ)), L.length = D → cycList (divCycle P₀ (T₀.f i)) L =
      ∑ l, (fd l : ℤ) * cycList (divCycle (P l) ((T l).f i)) L)
    (hg : ∀ i (L : List (K → ℤ)), L.length = D → cycList (divCycle P₀ (T₀.g i)) L =
      ∑ l, (fd l : ℤ) * cycList (divCycle (P l) ((T l).g i)) L)
    (hp : ∀ L : List (K → ℤ), L.length = D → cycList (divCycle P₀ (C (p : O₀))) L =
      ∑ l, (fd l : ℤ) * cycList (divCycle (P l) (C (p : O l))) L)
    (hloc : ∀ l, FlagChernComparison (P l) D p j φ (T l)) : FlagChernComparison P₀ D p j φ T₀ := by
  intro τ k hk Q hQ
  have hQ' : k - 1 + Q.length = D := by omega
  have hloc' := fun l => hloc l τ k hk Q hQ
  rw [cycNum_transfer _ _ fd D hp _ (bracket_isHomogeneous j φ p k τ) Q hQ', ck_cast]
  have hG : ∀ i, (MvPolynomial.map (Int.castRingHom ℝ)
      (psumExpansion N k i)).IsHomogeneous (k - 1) := fun i =>
    (isHomogeneous_psumExpansion N k i).map _
  have hterm : ∀ l, cycNum (divCycle (P l) (C (p : O l))) T₀.x (bracket j φ p k τ) Q =
      (((((T l).comp fun i : Fin N => (τ, i)).ck (P l) k Q : ℤ)) : ℝ) := by
    intro l
    rw [hloc' l, hx l]
  simp only [hterm, ck_cast, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e₁ := cycNum_transfer _ _ fd D (hf (τ, i)) (Sum.elim (T₀.x ∘ fun i : Fin N => (τ, i))
    (T₀.x' ∘ fun i : Fin N => (τ, i))) (hG i) Q hQ'
  have e₂ := cycNum_transfer _ _ fd D (hg (τ, i)) (Sum.elim (T₀.x ∘ fun i : Fin N => (τ, i))
    (T₀.x' ∘ fun i : Fin N => (τ, i))) (hG i) Q hQ'
  simp only [LocPair.comp, Function.comp_apply, hx, hx']
  rw [e₁, e₂, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

end Transfer

section Ring

variable {A : Type} [CommRing A] [IsDedekindDomain A] [Module.Finite ℤ A]

/- English proof (translation)
Establish `hfin` using `Ideal.finite_minimalPrimes_of_isNoetherianRing A (Ideal.span {a})`. Use `Set.Finite.to_subtype (hfin.subset ?_)` and prove the remaining obligations. Introduce and unpack `n ⟨hn, han⟩`. Establish `hn0 : n ≠ ⊥` using `fun h => ha (by simpa [h] using han)`. Establish `hmax` using `Ring.DimensionLEOne.maximalOfPrime hn0 hn`.

Use `⟨⟨hn, (Ideal.span_singleton_le_iff_mem n).2 han⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `q ⟨hq, hqa⟩ hqn`. Establish `hq0 : q ≠ ⊥` using `fun h => ha (by`. Establish `: a ∈ q` using `(Ideal.span_singleton_le_iff_mem q).1 hqa`. Simplify `this)` using `[h]`.

Conclude with `(Ring.DimensionLEOne.maximalOfPrime hq0 hq).eq_of_le hn.ne_top hqn |>.ge`.
-/
theorem finite_primes_containing {a : A} (ha : a ≠ 0) :
    Finite {n : Ideal A // n.IsPrime ∧ a ∈ n} := by
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing A (Ideal.span {a})
  refine Set.Finite.to_subtype (hfin.subset ?_)
  rintro n ⟨hn, han⟩
  have hn0 : n ≠ ⊥ := fun h => ha (by simpa [h] using han)
  have hmax := Ring.DimensionLEOne.maximalOfPrime hn0 hn
  refine ⟨⟨hn, (Ideal.span_singleton_le_iff_mem n).2 han⟩, ?_⟩
  rintro q ⟨hq, hqa⟩ hqn
  have hq0 : q ≠ ⊥ := fun h => ha (by
    have : a ∈ q := (Ideal.span_singleton_le_iff_mem q).1 hqa
    simpa [h] using this)
  exact (Ring.DimensionLEOne.maximalOfPrime hq0 hq).eq_of_le hn.ne_top hqn |>.ge

/- English proof (translation)
Establish `hn0 : n ≠ ⊥` using `fun h => hp (by simpa [h] using hpn)`. Use `haveI hmax : n.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hn0 hn`. Use `haveI : Module.Finite ℤ (A ⧸ n) := Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℤ n).toLinearMap (Ideal.Quotient.mkₐ_surjective ℤ n)`. Establish `hz : (((p : ℕ) : A ⧸ n)) = 0`. Use `Ideal.Quotient.eq_zero_iff_mem.2 hpn` as an intermediate fact.

Simplify using `using this`. Establish `htor : Module.IsTorsion ℤ (A ⧸ n)`. Introduce `x`. Use `⟨⟨((p : ℕ) : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast p.2.ne_zero)⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((p : ℕ) : ℤ) • x = 0`.

Rewrite using `[zsmul_eq_mul]`. Simplify using `[hz]`. Use `haveI : Finite (A ⧸ n) := Module.finite_of_fg_torsion _ htor`. Use `letI : Field (A ⧸ n) := Ideal.Quotient.field n`. Use `haveI : CharP (A ⧸ n) (p : ℕ) := (CharP.charP_iff_prime_eq_zero p.2).2 hz`.

Use `letI : Fintype (A ⧸ n) := Fintype.ofFinite _`. Take `⟨m, -, hm⟩` from `FiniteField.card (A ⧸ n) (p : ℕ)`. Conclude with `⟨m, by rw [Nat.card_eq_fintype_card, hm]⟩`.
-/
theorem exists_card_residue (p : Nat.Primes) (hp : ((p : ℕ) : A) ≠ 0) (n : Ideal A) [hn : n.IsPrime]
    (hpn : ((p : ℕ) : A) ∈ n) : ∃ f : ℕ, Nat.card (A ⧸ n) = (p : ℕ) ^ f := by
  have hn0 : n ≠ ⊥ := fun h => hp (by simpa [h] using hpn)
  haveI hmax : n.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hn0 hn
  haveI : Module.Finite ℤ (A ⧸ n) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℤ n).toLinearMap (Ideal.Quotient.mkₐ_surjective ℤ n)
  have hz : (((p : ℕ) : A ⧸ n)) = 0 := by
    have := Ideal.Quotient.eq_zero_iff_mem.2 hpn
    simpa using this
  have htor : Module.IsTorsion ℤ (A ⧸ n) := by
    intro x
    refine ⟨⟨((p : ℕ) : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast p.2.ne_zero)⟩, ?_⟩
    change ((p : ℕ) : ℤ) • x = 0
    rw [zsmul_eq_mul]
    simp [hz]
  haveI : Finite (A ⧸ n) := Module.finite_of_fg_torsion _ htor
  letI : Field (A ⧸ n) := Ideal.Quotient.field n
  haveI : CharP (A ⧸ n) (p : ℕ) := (CharP.charP_iff_prime_eq_zero p.2).2 hz
  letI : Fintype (A ⧸ n) := Fintype.ofFinite _
  obtain ⟨m, -, hm⟩ := FiniteField.card (A ⧸ n) (p : ℕ)
  exact ⟨m, by rw [Nat.card_eq_fintype_card, hm]⟩

end Ring

section Main

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Ω : Type} [Field Ω] {y : (Σ k, ι k) → Ω}

/- English proof (translation)
Introduce `h`. Establish `h' : ((p : ℕ) : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MvPolynomial (Σ k, ι k) ℤ)` using `h`. Establish `hb : (mCoordIdeal y).comap (C : ℤ →+* MvPolynomial (Σ k, ι k) ℤ) = ⊥` using `hh`. Rewrite `h'` using `[hb, Ideal.mem_bot]`. Conclude with `p.2.ne_zero (by exact_mod_cast h')`.
-/
theorem C_prime_notMem (hh : IsHorizontal (mCoordIdeal y)) (p : Nat.Primes) :
    (C ((p : ℕ) : ℤ) : MvPolynomial (Σ k, ι k) ℤ) ∉ mCoordIdeal y := by
  intro h
  have h' : ((p : ℕ) : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MvPolynomial (Σ k, ι k) ℤ) := h
  have hb : (mCoordIdeal y).comap (C : ℤ →+* MvPolynomial (Σ k, ι k) ℤ) = ⊥ := hh
  rw [hb, Ideal.mem_bot] at h'
  exact p.2.ne_zero (by exact_mod_cast h')

/- English proof (translation)
Introduce `h`. Apply `C_prime_notMem hh p` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `_ ∈ RingHom.ker _`. Rewrite using `[RingHom.mem_ker]`. Simplify using `[ReciprocityTheory.ChartRestriction.G.Geo.mConeMap, h]`.

Conclude with `(map_natCast (C : Ω →+* MvPolynomial K Ω) (p : ℕ)).symm.trans (by rw [h, map_zero])`.
-/
theorem prime_ne_zero_field (hh : IsHorizontal (mCoordIdeal y)) (p : Nat.Primes) :
    ((p : ℕ) : Ω) ≠ 0 := by
  intro h
  apply C_prime_notMem hh p
  change _ ∈ RingHom.ker _
  rw [RingHom.mem_ker]
  simp [ReciprocityTheory.ChartRestriction.G.Geo.mConeMap, h]
  exact (map_natCast (C : Ω →+* MvPolynomial K Ω) (p : ℕ)).symm.trans (by rw [h, map_zero])

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

/- English proof (translation)
Establish `hnum` using `GlobalTheory.T.finite_places_model_family K ι Ω y A hinj hc D hv p Λ m hm hcov O fd hfd`. Establish `hCp` using `C_prime_notMem hv.2.2.1 p`. Establish `hconst : ∀ (R : Type) [CommRing R], MvPolynomial.map (Int.castRingHom R) (C ((p : ℕ) : ℤ) : MvPolynomial (Σ k, ι k) ℤ) = C ((p : ℕ) : R)`. Introduce `R _`. Simplify using the standard rewrite rules.

Use `flag_m3_of_places _ (fun l => pointIdeal (O l) y) fd D p j φ _ (fun l => T.map (Int.castRingHom (O l))) (fun _ => rfl) (fun _ => rfl) ?_ ?_ ?_ hloc` and prove the remaining obligations. Introduce `i L hL`. Take `⟨⟨bf, _, hbf, _, _⟩, hf, _, _⟩` from `hT i`. Conclude with `hnum bf (T.f i) hbf hf L hL`. Introduce `i L hL`.

Take `⟨⟨_, bg, _, hbg, _⟩, _, hg, _⟩` from `hT i`. Conclude with `hnum bg (T.g i) hbg hg L hL`. Introduce `L hL`. Establish `h` using `hnum 0 (C ((p : ℕ) : ℤ)) (isWeightedHomogeneous_C _ _) hCp L hL`. Simplify using `only [hconst] at h`.

Conclude with `h`.
-/
theorem flag_m3_padic_of_family {A : Type} [CommRing A] [Algebra A Ω] [IsDedekindDomain A] [Module.Finite ℤ A]
    (hinj : Function.Injective (algebraMap A Ω)) (hc : HasConstants ℤ A y) (D : ℕ)
    (hv : IsArithVar (mCoordIdeal y) (D + 1)) (p : Nat.Primes) (j : ℕ) (φ : Equiv.Perm (Ψ ⊕ Ψ))
    (S : Finset Nat.Primes) (T : LocPair ι ℤ (Ψ × Fin N)) (hT : T.IsVertOff (mCoordIdeal y) S)
    (Λ : Type) [Fintype Λ] (m : Λ → Ideal A) [∀ l, (m l).IsPrime] (hm : Function.Injective m)
    (hcov : ∀ n : Ideal A, n.IsPrime → (((p : ℕ) : A) ∈ n ↔ n ∈ Set.range m))
    (O : Λ → Type) [∀ l, CommRing (O l)] [∀ l, IsDomain (O l)] [∀ l, IsDiscreteValuationRing (O l)]
    [∀ l, Algebra A (O l)] [∀ l, IsLocalization.AtPrime (O l) (m l)] [∀ l, Algebra (O l) Ω]
    [∀ l, IsScalarTower A (O l) Ω] (fd : Λ → ℕ) (hfd : ∀ l, Nat.card (A ⧸ m l) = (p : ℕ) ^ fd l)
    (hloc : ∀ l, FlagChernComparison (pointIdeal (O l) y) D p j φ (T.map (Int.castRingHom (O l)))) :
    FlagChernComparison (extTo (ZP p) (mCoordIdeal y)) D p j φ (T.map (Int.castRingHom (ZP p))) := by
  have hnum := GlobalTheory.T.finite_places_model_family K ι Ω y A hinj hc D hv p Λ m hm hcov O fd hfd
  have hCp := C_prime_notMem hv.2.2.1 p
  have hconst : ∀ (R : Type) [CommRing R], MvPolynomial.map (Int.castRingHom R)
      (C ((p : ℕ) : ℤ) : MvPolynomial (Σ k, ι k) ℤ) = C ((p : ℕ) : R) := by
    intro R _
    simp
  refine flag_m3_of_places _ (fun l => pointIdeal (O l) y) fd D p j φ _
    (fun l => T.map (Int.castRingHom (O l))) (fun _ => rfl) (fun _ => rfl) ?_ ?_ ?_ hloc
  · intro i L hL
    obtain ⟨⟨bf, _, hbf, _, _⟩, hf, _, _⟩ := hT i
    exact hnum bf (T.f i) hbf hf L hL
  · intro i L hL
    obtain ⟨⟨_, bg, _, hbg, _⟩, _, hg, _⟩ := hT i
    exact hnum bg (T.g i) hbg hg L hL
  · intro L hL
    have h := hnum 0 (C ((p : ℕ) : ℤ)) (isWeightedHomogeneous_C _ _) hCp L hL
    simp only [hconst] at h
    exact h

/- English proof (translation)
Introduce `K _ _ ι _ Ω _ y A _ _ _ _ hinj hc D hv p Ψ _ _ N j φ S T hT hpl`. Establish `hpΩ` using `prime_ne_zero_field hv.2.2.1 p`. Establish `hpA : ((p : ℕ) : A) ≠ 0` using `fun h => hpΩ (by`. Use `congrArg (algebraMap A Ω) h` as an intermediate fact. Simplify using `using this)`.

Use `haveI hfin := finite_primes_containing hpA`. Use `letI : Fintype {n : Ideal A // n.IsPrime ∧ ((p : ℕ) : A) ∈ n} := Fintype.ofFinite _`. Use `haveI hpr : ∀ l : {n : Ideal A // n.IsPrime ∧ ((p : ℕ) : A) ∈ n}, (l.1).IsPrime := fun l => l.2.1`. Establish `hne : ∀ l : {n : Ideal A // n.IsPrime ∧ ((p : ℕ) : A) ∈ n}, l.1 ≠ ⊥` using `fun l h => hpA (by simpa [h] using l.2.2)`. Use `haveI hdom : ∀ l : {n : Ideal A // n.IsPrime ∧ ((p : ℕ) : A) ∈ n}, IsDomain (Localization.AtPrime l.1) := fun l => IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors _)`.

Use `haveI hdvr : ∀ l : {n : Ideal A // n.IsPrime ∧ ((p : ℕ) : A) ∈ n}, IsDiscreteValuationRing (Localization.AtPrime l.1) := fun l => IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A (hne l) _`. Establish `hunit : ∀ (l : {n : Ideal A // n.IsPrime ∧ ((p : ℕ) : A) ∈ n}) (s : (l.1).primeCompl), IsUnit (algebraMap A Ω s)` using `fun l s => by`. Use `IsUnit.mk0 _ fun h => s.2 ?_` and prove the remaining obligations. Establish `: (s : A) = 0` using `hinj (by simpa using h)`. Simplify using `[this]`.

Use `letI halg : ∀ l : {n : Ideal A // n.IsPrime ∧ ((p : ℕ) : A) ∈ n}, Algebra (Localization.AtPrime l.1) Ω := fun l => (IsLocalization.lift (M := (l.1).primeCompl) (S := Localization.AtPrime l.1) (hunit l)).toAlgebra`. Use `haveI htow : ∀ l : {n : Ideal A // n.IsPrime ∧ ((p : ℕ) : A) ∈ n}, IsScalarTower A (Localization.AtPrime l.1) Ω := fun l => IsScalarTower.of_algebraMap_eq fun a => (IsLocalization.lift_eq (hunit l) a).symm`. Use `choose fd hfd using fun l : {n : Ideal A // n.IsPrime ∧ ((p : ℕ) : A) ∈ n} => exists_card_residue p hpA l.1 l.2.2`. Establish `hloc : ∀ l : {n : Ideal A // n.IsPrime ∧ ((p : ℕ) : A) ∈ n}, FlagChernComparison (pointIdeal (Localization.AtPrime l.1) y) D p j φ (T.map (Int.castRingHom (Localization.AtPrime l.1)))` using `fun l => hpl l.1 l.2.2 (Localization.AtPrime l.1)`. Establish `hcov : ∀ n : Ideal A, n.IsPrime → (((p : ℕ) : A) ∈ n ↔ n ∈ Set.range (Subtype.val : {n : Ideal A // n.IsPrime ∧ ((p : ℕ) : A) ∈ n} → Ideal A))`.

Introduce `n hn`. Conclude with `⟨fun h => ⟨⟨n, hn, h⟩, rfl⟩, by rintro ⟨l, rfl⟩; exact l.2.2⟩`. Conclude with `flag_m3_padic_of_family hinj hc D hv p j φ S T hT {n : Ideal A // n.IsPrime ∧ ((p : ℕ) : A) ∈ n} Subtype.val Subtype.val_injective hcov (fun l => Localization.AtPrime l.1) fd hfd hloc`.
-/
theorem flag_m3_padic : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (A : Type) [CommRing A] [Algebra A Ω] [IsDedekindDomain A] [Module.Finite ℤ A], Function.Injective (algebraMap A Ω) → HasConstants ℤ A y → ∀ D : ℕ, IsArithVar (mCoordIdeal y) (D + 1) → ∀ (p : Nat.Primes) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (φ : Equiv.Perm (Ψ ⊕ Ψ)) (S : Finset Nat.Primes) (T : LocPair ι ℤ (Ψ × Fin N)), T.IsVertOff (mCoordIdeal y) S → (AtPlacesOver A Ω p fun O _ _ _ _ => FlagChernComparison (pointIdeal O y) D p j φ (T.map (Int.castRingHom O))) → FlagChernComparison (extTo (ZP p) (mCoordIdeal y)) D p j φ (T.map (Int.castRingHom (ZP p))) := by
  intro K _ _ ι _ Ω _ y A _ _ _ _ hinj hc D hv p Ψ _ _ N j φ S T hT hpl
  have hpΩ := prime_ne_zero_field hv.2.2.1 p
  have hpA : ((p : ℕ) : A) ≠ 0 := fun h => hpΩ (by
    have := congrArg (algebraMap A Ω) h
    simpa using this)
  haveI hfin := finite_primes_containing hpA
  letI : Fintype {n : Ideal A // n.IsPrime ∧ ((p : ℕ) : A) ∈ n} := Fintype.ofFinite _
  haveI hpr : ∀ l : {n : Ideal A // n.IsPrime ∧ ((p : ℕ) : A) ∈ n}, (l.1).IsPrime := fun l => l.2.1
  have hne : ∀ l : {n : Ideal A // n.IsPrime ∧ ((p : ℕ) : A) ∈ n}, l.1 ≠ ⊥ := fun l h =>
    hpA (by simpa [h] using l.2.2)
  haveI hdom : ∀ l : {n : Ideal A // n.IsPrime ∧ ((p : ℕ) : A) ∈ n},
      IsDomain (Localization.AtPrime l.1) := fun l =>
    IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors _)
  haveI hdvr : ∀ l : {n : Ideal A // n.IsPrime ∧ ((p : ℕ) : A) ∈ n},
      IsDiscreteValuationRing (Localization.AtPrime l.1) := fun l =>
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A (hne l) _
  have hunit : ∀ (l : {n : Ideal A // n.IsPrime ∧ ((p : ℕ) : A) ∈ n}) (s : (l.1).primeCompl),
      IsUnit (algebraMap A Ω s) := fun l s => by
    refine IsUnit.mk0 _ fun h => s.2 ?_
    have : (s : A) = 0 := hinj (by simpa using h)
    simp [this]
  letI halg : ∀ l : {n : Ideal A // n.IsPrime ∧ ((p : ℕ) : A) ∈ n},
      Algebra (Localization.AtPrime l.1) Ω := fun l =>
    (IsLocalization.lift (M := (l.1).primeCompl) (S := Localization.AtPrime l.1) (hunit l)).toAlgebra
  haveI htow : ∀ l : {n : Ideal A // n.IsPrime ∧ ((p : ℕ) : A) ∈ n},
      IsScalarTower A (Localization.AtPrime l.1) Ω := fun l =>
    IsScalarTower.of_algebraMap_eq fun a => (IsLocalization.lift_eq (hunit l) a).symm
  choose fd hfd using fun l : {n : Ideal A // n.IsPrime ∧ ((p : ℕ) : A) ∈ n} =>
    exists_card_residue p hpA l.1 l.2.2
  have hloc : ∀ l : {n : Ideal A // n.IsPrime ∧ ((p : ℕ) : A) ∈ n},
      FlagChernComparison (pointIdeal (Localization.AtPrime l.1) y) D p j φ
        (T.map (Int.castRingHom (Localization.AtPrime l.1))) := fun l =>
    hpl l.1 l.2.2 (Localization.AtPrime l.1)
  have hcov : ∀ n : Ideal A, n.IsPrime → (((p : ℕ) : A) ∈ n ↔
      n ∈ Set.range (Subtype.val : {n : Ideal A // n.IsPrime ∧ ((p : ℕ) : A) ∈ n} → Ideal A)) := by
    intro n hn
    exact ⟨fun h => ⟨⟨n, hn, h⟩, rfl⟩, by rintro ⟨l, rfl⟩; exact l.2.2⟩
  exact flag_m3_padic_of_family hinj hc D hv p j φ S T hT {n : Ideal A // n.IsPrime ∧ ((p : ℕ) : A) ∈ n}
    Subtype.val Subtype.val_injective hcov (fun l => Localization.AtPrime l.1) fd hfd hloc

end Main

end GlobalTheory.CompanionTheory.Ar.Num.PlacesFlagM3
