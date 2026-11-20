import Mathlib

noncomputable section

open AddMonoidAlgebra

namespace GlobalTheory.GroupAlg

variable (R : Type*) [CommRing R] {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (u : Y →+ X)

abbrev mapAlgebra : Algebra R[Y] R[X] := (mapDomainRingHom R u).toAlgebra

/- English proof (translation)
The claim follows from `letI := mapAlgebra R u IsScalarTower.of_algebraMap_eq fun a => ((mapDomainAlgHom R R u).commutes a).symm`.
-/
theorem mapAlgebra_tower : letI := mapAlgebra R u; IsScalarTower R R[Y] R[X] :=
  letI := mapAlgebra R u
  IsScalarTower.of_algebraMap_eq fun a => ((mapDomainAlgHom R R u).commutes a).symm

def cosetComb : letI := mapAlgebra R u; ((X ⧸ u.range) →₀ R[Y]) →ₗ[R[Y]] R[X] :=
  letI := mapAlgebra R u
  Finsupp.linearCombination R[Y] (fun c : X ⧸ u.range => (single c.out 1 : R[X]))

/- English proof (translation)
Use `letI := mapAlgebra R u`. Rewrite using `[cosetComb, Finsupp.linearCombination_single, Algebra.smul_def]`. Express the relevant statement in the definitionally equal form `mapDomain u (single y r) * _ = _`. Rewrite using `[mapDomain_single, single_mul_single, mul_one]`.
-/
theorem cosetComb_single (c : X ⧸ u.range) (y : Y) (r : R) :
    cosetComb R u (Finsupp.single c (single y r)) = single (u y + c.out) r := by
  letI := mapAlgebra R u
  rw [cosetComb, Finsupp.linearCombination_single, Algebra.smul_def]
  change mapDomain u (single y r) * _ = _
  rw [mapDomain_single, single_mul_single, mul_one]

/- English proof (translation)
Take `⟨⟨_, y, rfl⟩, h⟩` from `QuotientAddGroup.mk_out_eq_mul u.range x`. Conclude with `⟨-y, by rw [h]; simp⟩`.
-/
theorem exists_add_out (x : X) :
    ∃ y, u y + (QuotientAddGroup.mk x : X ⧸ u.range).out = x := by
  obtain ⟨⟨_, y, rfl⟩, h⟩ := QuotientAddGroup.mk_out_eq_mul u.range x
  exact ⟨-y, by rw [h]; simp⟩

/- English proof (translation)
Introduce `p`. Proceed by induction on `p using AddMonoidAlgebra.induction_linear with`. Consider the case `zero => exact ⟨0, map_zero _⟩`. Consider the case `add s t hs ht`. Take `⟨a, rfl⟩` from `hs`.

Take `⟨b, rfl⟩` from `ht`. Conclude with `⟨a + b, map_add _ _ _⟩`. Consider the case `single x r`. Take `⟨y, hy⟩` from `exists_add_out u x`. Conclude with `⟨_, (cosetComb_single R u _ y r).trans (by rw [hy])⟩`.
-/
theorem cosetComb_surjective : Function.Surjective (cosetComb R u) := by
  intro p
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => exact ⟨0, map_zero _⟩
  | add s t hs ht =>
    obtain ⟨a, rfl⟩ := hs
    obtain ⟨b, rfl⟩ := ht
    exact ⟨a + b, map_add _ _ _⟩
  | single x r =>
    obtain ⟨y, hy⟩ := exists_add_out u x
    exact ⟨_, (cosetComb_single R u _ y r).trans (by rw [hy])⟩

/- English proof (translation)
Use `⟨?_, fun x => ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨c, y⟩ ⟨d, z⟩ h dsimp only at h`. Establish `h1 : ∀ (c : X ⧸ u.range) y, (QuotientAddGroup.mk (u y + c.out) : X ⧸ u.range) = c`. Introduce `c y`. Rewrite using `[QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff (N := u.range) (u y)).2 ⟨y, rfl⟩, zero_add, QuotientAddGroup.out_eq']`.

Take `rfl : c = d` from `by rw [← h1 c y, h, h1]`. Take `rfl : y = z` from `hu (add_right_cancel h)`. Both sides reduce to the same expression. Take `⟨y, hy⟩` from `exists_add_out u x`. Conclude with `⟨⟨_, y⟩, hy⟩`.
-/
theorem coset_bijective (hu : Function.Injective u) :
    Function.Bijective (fun p : (Σ _ : X ⧸ u.range, Y) => u p.2 + p.1.out) := by
  refine ⟨?_, fun x => ?_⟩
  · rintro ⟨c, y⟩ ⟨d, z⟩ h
    dsimp only at h
    have h1 : ∀ (c : X ⧸ u.range) y, (QuotientAddGroup.mk (u y + c.out) : X ⧸ u.range) = c := by
      intro c y
      rw [QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff (N := u.range) (u y)).2 ⟨y, rfl⟩, zero_add,
        QuotientAddGroup.out_eq']
    obtain rfl : c = d := by rw [← h1 c y, h, h1]
    obtain rfl : y = z := hu (add_right_cancel h)
    rfl
  · obtain ⟨y, hy⟩ := exists_add_out u x
    exact ⟨⟨_, y⟩, hy⟩

/- English proof (translation)
Use `letI := mapAlgebra R u`. Use `haveI := mapAlgebra_tower R u`. Set `b : Module.Basis (Σ _ : X ⧸ u.range, Y) R ((X ⧸ u.range) →₀ R[Y])` to `Finsupp.basis fun _ => AddMonoidAlgebra.basis Y R`. Set `e` to `b.equiv (AddMonoidAlgebra.basis X R) (Equiv.ofBijective _ (coset_bijective u hu))`. Establish `: (cosetComb R u).restrictScalars R = e.toLinearMap`.

Use `b.ext fun p => ?_` and prove the remaining obligations. Take `⟨c, y⟩` from `p`. Rewrite using `[LinearEquiv.coe_coe, Module.Basis.equiv_apply]`. Simplify using `[b, cosetComb_single]`. Establish `h2 : ⇑(cosetComb R u) = e` using `congrArg DFunLike.coe this`.

Rewrite using `[h2]`. Conclude with `e.injective`.
-/
theorem cosetComb_injective (hu : Function.Injective u) : Function.Injective (cosetComb R u) := by
  letI := mapAlgebra R u
  haveI := mapAlgebra_tower R u
  let b : Module.Basis (Σ _ : X ⧸ u.range, Y) R ((X ⧸ u.range) →₀ R[Y]) :=
    Finsupp.basis fun _ => AddMonoidAlgebra.basis Y R
  let e := b.equiv (AddMonoidAlgebra.basis X R) (Equiv.ofBijective _ (coset_bijective u hu))
  have : (cosetComb R u).restrictScalars R = e.toLinearMap := by
    refine b.ext fun p => ?_
    obtain ⟨c, y⟩ := p
    rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply]
    simp [b, cosetComb_single]
  have h2 : ⇑(cosetComb R u) = e := congrArg DFunLike.coe this
  rw [h2]
  exact e.injective

def cosetBasis (hu : Function.Injective u) :
    letI := mapAlgebra R u; Module.Basis (X ⧸ u.range) R[Y] R[X] :=
  letI := mapAlgebra R u
  .ofRepr (LinearEquiv.ofBijective (cosetComb R u)
    ⟨cosetComb_injective R u hu, cosetComb_surjective R u⟩).symm

/- English proof (translation)
The claim follows from `letI := mapAlgebra R u .of_basis (cosetBasis R u hu)`.
-/
theorem free_of_injective (hu : Function.Injective u) :
    letI := mapAlgebra R u; Module.Free R[Y] R[X] :=
  letI := mapAlgebra R u
  .of_basis (cosetBasis R u hu)

/- English proof (translation)
Use `letI := mapAlgebra R u`. Use `free_of_injective R u hu` as an intermediate fact. Express the relevant statement in the definitionally equal form `Module.FaithfullyFlat R[Y] R[X]`. Break down `subsingleton_or_nontrivial R with h | h` into its components or cases. Establish `: Subsingleton R[Y]` using `Module.subsingleton R _`.

Conclude with `⟨fun m hm => (hm.ne_top (Subsingleton.elim _ _)).elim⟩`. Use `infer_instance`.
-/
theorem faithfullyFlat_of_injective (hu : Function.Injective u) :
    (mapDomainRingHom R u).FaithfullyFlat := by
  letI := mapAlgebra R u
  have := free_of_injective R u hu
  change Module.FaithfullyFlat R[Y] R[X]
  rcases subsingleton_or_nontrivial R with h | h
  · have : Subsingleton R[Y] := Module.subsingleton R _
    exact ⟨fun m hm => (hm.ne_top (Subsingleton.elim _ _)).elim⟩
  · infer_instance

/- English proof (translation)
Use `letI := mapAlgebra R u`. Conclude with `Module.Finite.of_surjective (cosetComb R u) (cosetComb_surjective R u)`.
-/
theorem finite_of_finiteIndex [u.range.FiniteIndex] : (mapDomainRingHom R u).Finite := by
  letI := mapAlgebra R u
  exact Module.Finite.of_surjective (cosetComb R u) (cosetComb_surjective R u)

/- English proof (translation)
Use `letI := mapAlgebra R u`. Use `free_of_injective R u hu` as an intermediate fact. Establish `: Module.Finite R[Y] R[X]` using `finite_of_finiteIndex R u`. Establish `: Module.FinitePresentation R[Y] R[X]` using `Module.finitePresentation_of_projective _ _`. Conclude with `(inferInstance : Algebra.FinitePresentation R[Y] R[X])`.
-/
theorem finitePresentation_of_injective (hu : Function.Injective u) [u.range.FiniteIndex] :
    (mapDomainRingHom R u).FinitePresentation := by
  letI := mapAlgebra R u
  have := free_of_injective R u hu
  have : Module.Finite R[Y] R[X] := finite_of_finiteIndex R u
  have : Module.FinitePresentation R[Y] R[X] := Module.finitePresentation_of_projective _ _
  exact (inferInstance : Algebra.FinitePresentation R[Y] R[X])

/- English proof (translation)
Use `letI := mapAlgebra R u`. Use `free_of_injective R u hu` as an intermediate fact. Establish `: Module.Finite R[Y] R[X]` using `finite_of_finiteIndex R u`. Establish `: Nontrivial R[Y]` using `p.nontrivial`. Express the relevant statement in the definitionally equal form `Module.rankAtStalk (R := R[Y]) R[X] p = _`.

Rewrite using `[Module.rankAtStalk_eq_finrank_of_free, Module.finrank_eq_nat_card_basis (cosetBasis R u hu)]`. Both sides reduce to the same expression.
-/
theorem finrank_of_injective (hu : Function.Injective u) [u.range.FiniteIndex]
    (p : PrimeSpectrum R[Y]) : (mapDomainRingHom R u).finrank p = u.range.index := by
  letI := mapAlgebra R u
  have := free_of_injective R u hu
  have : Module.Finite R[Y] R[X] := finite_of_finiteIndex R u
  have : Nontrivial R[Y] := p.nontrivial
  change Module.rankAtStalk (R := R[Y]) R[X] p = _
  rw [Module.rankAtStalk_eq_finrank_of_free, Module.finrank_eq_nat_card_basis (cosetBasis R u hu)]
  rfl

/- English proof (translation)
Introduce `p`. Proceed by induction on `p using AddMonoidAlgebra.induction_linear with`. Consider the case `zero => exact ⟨0, map_zero _⟩`. Consider the case `add s t hs ht`. Take `⟨a, rfl⟩` from `hs`.

Take `⟨b, rfl⟩` from `ht`. Conclude with `⟨a + b, map_add _ _ _⟩`. Consider the case `single x r`. Take `⟨y, rfl⟩` from `hu x`. Conclude with `⟨single y r, mapDomain_single⟩`.
-/
theorem surjective_of_surjective (hu : Function.Surjective u) :
    Function.Surjective (mapDomainRingHom R u) := by
  intro p
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => exact ⟨0, map_zero _⟩
  | add s t hs ht =>
    obtain ⟨a, rfl⟩ := hs
    obtain ⟨b, rfl⟩ := ht
    exact ⟨a + b, map_add _ _ _⟩
  | single x r =>
    obtain ⟨y, rfl⟩ := hu x
    exact ⟨single y r, mapDomain_single⟩

/- English proof (translation)
Rewrite using `[Algebra.FormallyUnramified.iff_comp_injective]`. Introduce `B _ _ I hI f g h`. Use extensionality with `x`. Establish `hB : IsUnit (n : B)` using `by simpa using hn.map (algebraMap R B)`. Establish `hfg : f (single x 1) - g (single x 1) ∈ I`.

Rewrite using `[← Ideal.Quotient.eq]`. Conclude with `DFunLike.congr_fun h (single x 1)`. Establish `hp : ∀ k : R[X] →ₐ[R] B, k (single x 1) ^ n = 1` using `fun k => by`. Rewrite using `[← map_pow, single_pow, hX, one_pow, ← one_def, map_one]`. Use `set a := f (single x 1)`.

Use `set b := g (single x 1)`. Establish `hi : (a - b) * (a - b) = 0`. Use `Ideal.mul_mem_mul hfg hfg` as an intermediate fact. Rewrite `this` using `[← pow_two, hI, Ideal.mem_bot]`. Then use the resulting hypothesis. Establish `key : ∀ m : ℕ, b * a ^ m = b ^ (m + 1) + m * b ^ m * (a - b)`.

Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih`. Rewrite using `[pow_succ a, ← mul_assoc, ih]`.

Use `push_cast`. Take the linear combination `(m * b ^ m) * hi`. Establish `h3` using `key n`. Rewrite `h3` using `[pow_succ b, hp f, hp g]`. Establish `h4 : (n : B) * (a - b) = 0` using `by linear_combination -h3`.

Establish `h5 : a - b = 0` using `(hB.mul_right_eq_zero).1 h4`. Conclude with `sub_eq_zero.1 h5`.
-/
theorem formallyUnramified_of_isUnit (n : ℕ) (hn : IsUnit (n : R)) (hX : ∀ x : X, n • x = 0) :
    Algebra.FormallyUnramified R R[X] := by
  rw [Algebra.FormallyUnramified.iff_comp_injective]
  intro B _ _ I hI f g h
  ext x
  have hB : IsUnit (n : B) := by simpa using hn.map (algebraMap R B)
  have hfg : f (single x 1) - g (single x 1) ∈ I := by
    rw [← Ideal.Quotient.eq]
    exact DFunLike.congr_fun h (single x 1)
  have hp : ∀ k : R[X] →ₐ[R] B, k (single x 1) ^ n = 1 := fun k => by
    rw [← map_pow, single_pow, hX, one_pow, ← one_def, map_one]
  set a := f (single x 1)
  set b := g (single x 1)
  have hi : (a - b) * (a - b) = 0 := by
    have := Ideal.mul_mem_mul hfg hfg
    rwa [← pow_two, hI, Ideal.mem_bot] at this
  have key : ∀ m : ℕ, b * a ^ m = b ^ (m + 1) + m * b ^ m * (a - b) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ a, ← mul_assoc, ih]
      push_cast
      linear_combination (m * b ^ m) * hi
  have h3 := key n
  rw [pow_succ b, hp f, hp g] at h3
  have h4 : (n : B) * (a - b) = 0 := by linear_combination -h3
  have h5 : a - b = 0 := (hB.mul_right_eq_zero).1 h4
  exact sub_eq_zero.1 h5

/- English proof (translation)
Use `formallyUnramified_of_isUnit R (X := X) _ hn fun x => card_nsmul_eq_zero'` as an intermediate fact. Establish `: Module.FinitePresentation R R[X]` using `Module.finitePresentation_of_projective _ _`. Conclude with `Algebra.Etale.of_formallyUnramified_of_flat`.
-/
theorem etale_of_isUnit_card [Finite X] (hn : IsUnit (Nat.card X : R)) : Algebra.Etale R R[X] := by
  have := formallyUnramified_of_isUnit R (X := X) _ hn fun x => card_nsmul_eq_zero'
  have : Module.FinitePresentation R R[X] := Module.finitePresentation_of_projective _ _
  exact Algebra.Etale.of_formallyUnramified_of_flat

end GlobalTheory.GroupAlg
