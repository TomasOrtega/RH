import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsBaseChange
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ChowFormExtend

section Incidence

variable {F : Type*} [Field F] {n : ℕ}

def incidenceIdeal (I : Ideal (MvPolynomial (Fin n) F)) (k : ℕ) :
    Ideal (MvPolynomial ((Fin k × Fin n) ⊕ Fin n) F) :=
  I.map (rename Sum.inr) ⊔
    Ideal.span (Set.range fun i : Fin k => ∑ j, X (Sum.inl (i, j)) * X (Sum.inr j))

/- English proof (translation)
Establish `key : z ∈ zeroLocus E (incidenceIdeal I k) ↔ incidenceIdeal I k ≤ vanishingIdeal F {z}` using `⟨fun h p hp => (mem_vanishingIdeal_singleton_iff z p).2 (h p hp), fun h p hp => (mem_vanishingIdeal_singleton_iff z p).1 (h hp)⟩`. Rewrite using `[key, incidenceIdeal, sup_le_iff, Ideal.map_le_iff_le_comap, Ideal.span_le, Set.range_subset_iff]`. Use `and_congr ⟨fun h g hg => ?_, fun h g hg => ?_⟩ (forall_congr' fun i => ?_)` and prove the remaining obligations. Use `h hg` as an intermediate fact. Rewrite `this` using `[Ideal.mem_comap, mem_vanishingIdeal_singleton_iff, aeval_rename]`. Then use the resulting hypothesis.

Rewrite using `[Ideal.mem_comap, mem_vanishingIdeal_singleton_iff, aeval_rename]`. Conclude with `h g hg`. Rewrite using `[SetLike.mem_coe, mem_vanishingIdeal_singleton_iff]`. Simplify using the standard rewrite rules.
-/
theorem mem_zeroLocus_incidenceIdeal {E : Type*} [Field E] [Algebra F E]
    (I : Ideal (MvPolynomial (Fin n) F)) (k : ℕ) (z : (Fin k × Fin n) ⊕ Fin n → E) :
    z ∈ zeroLocus E (incidenceIdeal I k) ↔
      (∀ g ∈ I, aeval (z ∘ Sum.inr) g = 0) ∧ ∀ i, ∑ j, z (Sum.inl (i, j)) * z (Sum.inr j) = 0 := by
  have key : z ∈ zeroLocus E (incidenceIdeal I k) ↔ incidenceIdeal I k ≤ vanishingIdeal F {z} :=
    ⟨fun h p hp => (mem_vanishingIdeal_singleton_iff z p).2 (h p hp),
      fun h p hp => (mem_vanishingIdeal_singleton_iff z p).1 (h hp)⟩
  rw [key, incidenceIdeal, sup_le_iff, Ideal.map_le_iff_le_comap, Ideal.span_le, Set.range_subset_iff]
  refine and_congr ⟨fun h g hg => ?_, fun h g hg => ?_⟩ (forall_congr' fun i => ?_)
  · have := h hg
    rwa [Ideal.mem_comap, mem_vanishingIdeal_singleton_iff, aeval_rename] at this
  · rw [Ideal.mem_comap, mem_vanishingIdeal_singleton_iff, aeval_rename]
    exact h g hg
  · rw [SetLike.mem_coe, mem_vanishingIdeal_singleton_iff]
    simp

/- English proof (translation)
Rewrite using `[← vanishingIdeal_zeroLocus_eq_radical (K := AlgebraicClosure F) (incidenceIdeal I k)]`. Simplify using `only [mem_vanishingIdeal_iff, mem_zeroLocus_incidenceIdeal]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `h j z ⟨hI, hlin⟩`. Rewrite using `[map_mul, aeval_X, aeval_rename]`.

Distinguish the cases in `hx : z ∘ Sum.inr = 0`. Rewrite using `[show z (Sum.inr j) = 0 from congrFun hx j, zero_mul]`. Rewrite using `[h (z ∘ Sum.inl) ⟨z ∘ Sum.inr, hx, hI, hlin⟩, mul_zero]`. Introduce and unpack `h u ⟨x, hx, hI, hlin⟩`. Take `⟨j, hj⟩ : ∃ j, x j ≠ 0` from `Function.ne_iff.1 hx`.

Use `h j (Sum.elim u x) ⟨by simpa using hI, by simpa using hlin⟩` as an intermediate fact. Rewrite `this` using `[map_mul, aeval_X, aeval_rename]`. Simplify `this` using `[hj]`.
-/
theorem vanishes_incidence_iff (I : Ideal (MvPolynomial (Fin n) F)) (k : ℕ)
    (g : MvPolynomial (Fin k × Fin n) F) :
    (∀ u ∈ incidence I k, aeval u g = 0) ↔
      ∀ j, X (Sum.inr j) * rename Sum.inl g ∈ (incidenceIdeal I k).radical := by
  rw [← vanishingIdeal_zeroLocus_eq_radical (K := AlgebraicClosure F) (incidenceIdeal I k)]
  simp only [mem_vanishingIdeal_iff, mem_zeroLocus_incidenceIdeal]
  constructor
  · rintro h j z ⟨hI, hlin⟩
    rw [map_mul, aeval_X, aeval_rename]
    by_cases hx : z ∘ Sum.inr = 0
    · rw [show z (Sum.inr j) = 0 from congrFun hx j, zero_mul]
    · rw [h (z ∘ Sum.inl) ⟨z ∘ Sum.inr, hx, hI, hlin⟩, mul_zero]
  · rintro h u ⟨x, hx, hI, hlin⟩
    obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := Function.ne_iff.1 hx
    have := h j (Sum.elim u x) ⟨by simpa using hI, by simpa using hlin⟩
    rw [map_mul, aeval_X, aeval_rename] at this
    simpa [hj] using this

/- English proof (translation)
Rewrite using `[incidenceIdeal, incidenceIdeal, Ideal.map_sup, Ideal.map_span]`. Use `congr 1`. Rewrite using `[← Ideal.map_coe (rename Sum.inr), ← Ideal.map_coe (rename Sum.inr), Ideal.map_map, Ideal.map_map]`. Use `congr 1`. Apply the tactic sequence `apply ringHom_ext <;> intro <;> simp`.

Use `congr 1`. Use extensionality with `p`. Simplify using the standard rewrite rules.
-/
theorem incidenceIdeal_map {K L : Type*} [Field K] [Field L] (σ : K →+* L)
    (I : Ideal (MvPolynomial (Fin n) K)) (k : ℕ) :
    incidenceIdeal (I.map (MvPolynomial.map σ)) k =
      (incidenceIdeal I k).map (MvPolynomial.map σ) := by
  rw [incidenceIdeal, incidenceIdeal, Ideal.map_sup, Ideal.map_span]
  congr 1
  · rw [← Ideal.map_coe (rename Sum.inr), ← Ideal.map_coe (rename Sum.inr), Ideal.map_map, Ideal.map_map]
    congr 1
    apply ringHom_ext <;> intro <;> simp
  · congr 1
    ext p
    simp

/- English proof (translation)
The claim follows from `le_antisymm ((h K L σ ι J.radical (Ideal.radical_isRadical J)).radical_le_iff.2 (Ideal.map_mono Ideal.le_radical)) (Ideal.map_radical_le _)`.
-/
theorem radical_map_eq (h : RadicalBaseChange.Statement) {K L : Type} [Field K] [PerfectField K]
    [Field L] (σ : K →+* L) {ι : Type} (J : Ideal (MvPolynomial ι K)) :
    (J.map (MvPolynomial.map σ)).radical = J.radical.map (MvPolynomial.map σ) :=
  le_antisymm
    ((h K L σ ι J.radical (Ideal.radical_isRadical J)).radical_le_iff.2
      (Ideal.map_mono Ideal.le_radical))
    (Ideal.map_radical_le _)

end Incidence

section Coord

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {Y : Type*}

def coordPoly (φ : L →ₗ[K] K) : MvPolynomial Y L →+ MvPolynomial Y K where
  toFun p := AddMonoidAlgebra.map φ.toAddMonoidHom p
  map_zero' := by
    ext m
    rw [coeff_addMonoidAlgebraMap, coeff_zero, coeff_zero, map_zero]
  map_add' p q := by
    ext m
    simp only [coeff_addMonoidAlgebraMap, coeff_add, map_add]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coeff_coordPoly (φ : L →ₗ[K] K) (p : MvPolynomial Y L) (m : Y →₀ ℕ) :
    coeff m (coordPoly φ p) = φ (coeff m p) :=
  rfl

/- English proof (translation)
Use extensionality with `m`. Rewrite using `[coeff_coordPoly, coeff_C_mul, coeff_C_mul, coeff_map, mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]`.
-/
theorem coordPoly_C_mul_map (φ : L →ₗ[K] K) (a : L) (q : MvPolynomial Y K) :
    coordPoly φ (C a * map (algebraMap K L) q) = C (φ a) * q := by
  ext m
  rw [coeff_coordPoly, coeff_C_mul, coeff_C_mul, coeff_map, mul_comm, ← Algebra.smul_def, map_smul,
    smul_eq_mul, mul_comm]

variable {β : Type*} [DecidableEq β]

def coordSupport (b : Module.Basis β K L) (p : MvPolynomial Y L) : Finset β :=
  p.support.biUnion fun m => (b.repr (coeff m p)).support

/- English proof (translation)
Use extensionality with `m`. Rewrite using `[coeff_sum]`. Repeatedly rewrite using `[coeff_C_mul, coeff_map, coeff_coordPoly, Module.Basis.coord_apply, mul_comm (b _), ← Algebra.smul_def]`. Use `conv_rhs => rw [← b.linearCombination_repr (coeff m p)]`. Rewrite using `[Finsupp.linearCombination_apply, Finsupp.sum]`.

Use `symm`. Apply `Finset.sum_subset` to reduce the goal to its premises. Introduce `c hc`. Establish `hm : m ∈ p.support`. Rewrite using `[mem_support_iff]`.

Introduce `h0`. Rewrite `hc` using `[h0, map_zero]`. Simplify using `at hc`. Conclude with `Finset.mem_biUnion.2 ⟨m, hm, hc⟩`. Introduce `c _ hc`.

Rewrite using `[Finsupp.notMem_support_iff.1 hc, zero_smul]`.
-/
theorem sum_coordPoly (b : Module.Basis β K L) (p : MvPolynomial Y L) :
    ∑ c ∈ coordSupport b p, C (b c) * map (algebraMap K L) (coordPoly (b.coord c) p) = p := by
  ext m
  rw [coeff_sum]
  simp_rw [coeff_C_mul, coeff_map, coeff_coordPoly, Module.Basis.coord_apply, mul_comm (b _),
    ← Algebra.smul_def]
  conv_rhs => rw [← b.linearCombination_repr (coeff m p)]
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  symm
  apply Finset.sum_subset
  · intro c hc
    have hm : m ∈ p.support := by
      rw [mem_support_iff]
      intro h0
      rw [h0, map_zero] at hc
      simp at hc
    exact Finset.mem_biUnion.2 ⟨m, hm, hc⟩
  · intro c _ hc
    rw [Finsupp.notMem_support_iff.1 hc, zero_smul]

/- English proof (translation)
Rewrite using `[map_sum]`. Repeatedly rewrite using `[coordPoly_C_mul_map, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]`. Simplify using `[apply_ite C, ite_mul]`.
-/
theorem coordPoly_sum (b : Module.Basis β K L) (S : Finset β) (h : β → MvPolynomial Y K) (c : β) :
    coordPoly (b.coord c) (∑ c' ∈ S, C (b c') * map (algebraMap K L) (h c')) =
      if c ∈ S then h c else 0 := by
  rw [map_sum]
  simp_rw [coordPoly_C_mul_map, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  simp [apply_ite C, ite_mul]

/- English proof (translation)
Establish `hp' : p ∈ Submodule.span (MvPolynomial Y L) ((map (algebraMap K L)) '' T)` using `hp`. Use `clear hp`. Use `revert c`. Proceed by induction on `hp' using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨t, ht, rfl⟩` from `hx`. Introduce `c`. Establish `e` using `coordPoly_C_mul_map (b.coord c) (1 : L) t`. Rewrite `e` using `[C_1, one_mul]`. Rewrite using `[e]`.

Conclude with `T.mul_mem_left _ ht`. Consider the case `zero => intro c`. Rewrite using `[map_zero]`. Conclude with `T.zero_mem`. Consider the case `add x y _ _ hx hy => intro c`.

Rewrite using `[map_add]`. Conclude with `T.add_mem (hx c) (hy c)`. Consider the case `smul r x _ hx`. Introduce `c`. Establish `e : r * x = ∑ c₁ ∈ coordSupport b r, ∑ c₂ ∈ coordSupport b x, C (b c₁ * b c₂) * map (algebraMap K L) (coordPoly (b.coord c₁) r * coordPoly (b.coord c₂) x)` using `by conv_lhs => rw [← sum_coordPoly b r, ← sum_coordPoly b x]`.

Rewrite using `[Finset.sum_mul_sum]`. Use `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_` and prove the remaining obligations. Rewrite using `[C_mul, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[smul_eq_mul, e, map_sum]`.

Use `T.sum_mem fun c₁ _ => ?_` and prove the remaining obligations. Rewrite using `[map_sum]`. Use `T.sum_mem fun c₂ _ => ?_` and prove the remaining obligations. Rewrite using `[coordPoly_C_mul_map]`. Conclude with `T.mul_mem_left _ (T.mul_mem_left _ (hx c₂))`.
-/
theorem coordPoly_mem_of_mem_map (b : Module.Basis β K L) (T : Ideal (MvPolynomial Y K))
    {p : MvPolynomial Y L} (hp : p ∈ T.map (map (algebraMap K L))) (c : β) :
    coordPoly (b.coord c) p ∈ T := by
  have hp' : p ∈ Submodule.span (MvPolynomial Y L) ((map (algebraMap K L)) '' T) := hp
  clear hp
  revert c
  induction hp' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, ht, rfl⟩ := hx
    intro c
    have e := coordPoly_C_mul_map (b.coord c) (1 : L) t
    rw [C_1, one_mul] at e
    rw [e]
    exact T.mul_mem_left _ ht
  | zero => intro c; rw [map_zero]; exact T.zero_mem
  | add x y _ _ hx hy => intro c; rw [map_add]; exact T.add_mem (hx c) (hy c)
  | smul r x _ hx =>
    intro c
    have e : r * x = ∑ c₁ ∈ coordSupport b r, ∑ c₂ ∈ coordSupport b x,
        C (b c₁ * b c₂) * map (algebraMap K L) (coordPoly (b.coord c₁) r * coordPoly (b.coord c₂) x) := by
      conv_lhs => rw [← sum_coordPoly b r, ← sum_coordPoly b x]
      rw [Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
      rw [C_mul, map_mul]
      ring
    rw [smul_eq_mul, e, map_sum]
    refine T.sum_mem fun c₁ _ => ?_
    rw [map_sum]
    refine T.sum_mem fun c₂ _ => ?_
    rw [coordPoly_C_mul_map]
    exact T.mul_mem_left _ (T.mul_mem_left _ (hx c₂))

end Coord

/- English proof (translation)
Take `⟨hf0, hf⟩` from `hf`. Use `set R := (incidenceIdeal I k).radical`. Establish `hK` using `fun g => vanishes_incidence_iff I k g`. Establish `hrad : (incidenceIdeal (I.map (map (algebraMap K L))) k).radical = R.map (map (algebraMap K L))`. Rewrite using `[incidenceIdeal_map, radical_map_eq h]`.

Establish `hmapX : ∀ (j : Fin n) (p : MvPolynomial (Fin k × Fin n) K), map (algebraMap K L) (X (Sum.inr j) * rename Sum.inl p) = X (Sum.inr j) * rename Sum.inl (map (algebraMap K L) p)`. Introduce `j p`. Rewrite using `[map_mul, map_X, map_rename]`. Use `⟨fun h0 => hf0 (map_injective _ (algebraMap K L).injective (by rw [h0, map_zero])), fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[vanishes_incidence_iff, hrad]`.

Prove the components needed by the constructor for the conclusion. Introduce `hg classical`. Set `b` to `Module.Basis.ofVectorSpace K L`. Use `set S := coordSupport b g`. Use `set hc := fun c => coordPoly (b.coord c) g`.

Establish `hsum : ∑ c ∈ S, C (b c) * map (algebraMap K L) (hc c) = g` using `sum_coordPoly b g`. Establish `hdiv : ∀ c ∈ S, ∃ q, hc c = f * q`. Introduce `c hcS`. Use `(hf _).1 ((hK _).2 fun j => ?_)` and prove the remaining obligations. Establish `e : X (Sum.inr j) * rename Sum.inl g = ∑ c' ∈ S, C (b c') * map (algebraMap K L) (X (Sum.inr j) * rename Sum.inl (hc c'))` using `by conv_lhs => rw [← hsum]`.

Rewrite using `[map_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun c' _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, rename_C, hmapX]`. Expand and normalize the polynomial expressions, which then agree. Establish `hmem` using `coordPoly_mem_of_mem_map b R (e ▸ hg j) c`.

Rewrite `hmem` using `[coordPoly_sum, if_pos hcS]`. Then use the resulting hypothesis. Use `choose! q hq using hdiv`. Use `⟨∑ c ∈ S, C (b c) * map (algebraMap K L) (q c), ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [← hsum]`. Rewrite using `[Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun c hcS => ?_` and prove the remaining obligations. Rewrite using `[hq c hcS, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Introduce and unpack `⟨q, rfl⟩ j`. Establish `hfR : X (Sum.inr j) * rename Sum.inl f ∈ R` using `(hK f).1 ((hf f).2 dvd_rfl) j`.

Establish `hmem` using `Ideal.mem_map_of_mem (map (algebraMap K L)) hfR`. Rewrite `hmem` using `[hmapX]`. Rewrite using `[map_mul (rename Sum.inl), ← mul_assoc]`. Conclude with `Ideal.mul_mem_right _ _ hmem`.
-/
theorem isChowForm_map (h : RadicalBaseChange.Statement) {K L : Type} [Field K] [PerfectField K]
    [Field L] [Algebra K L] {n k : ℕ} (I : Ideal (MvPolynomial (Fin n) K))
    (f : MvPolynomial (Fin k × Fin n) K) (hf : IsChowForm I k f) :
    IsChowForm (I.map (map (algebraMap K L))) k (map (algebraMap K L) f) := by
  obtain ⟨hf0, hf⟩ := hf
  set R := (incidenceIdeal I k).radical
  have hK := fun g => vanishes_incidence_iff I k g
  have hrad : (incidenceIdeal (I.map (map (algebraMap K L))) k).radical = R.map (map (algebraMap K L)) := by
    rw [incidenceIdeal_map, radical_map_eq h]
  have hmapX : ∀ (j : Fin n) (p : MvPolynomial (Fin k × Fin n) K),
      map (algebraMap K L) (X (Sum.inr j) * rename Sum.inl p) =
        X (Sum.inr j) * rename Sum.inl (map (algebraMap K L) p) := by
    intro j p
    rw [map_mul, map_X, map_rename]
  refine ⟨fun h0 => hf0 (map_injective _ (algebraMap K L).injective (by rw [h0, map_zero])), fun g => ?_⟩
  rw [vanishes_incidence_iff, hrad]
  constructor
  · intro hg
    classical
    let b := Module.Basis.ofVectorSpace K L
    set S := coordSupport b g
    set hc := fun c => coordPoly (b.coord c) g
    have hsum : ∑ c ∈ S, C (b c) * map (algebraMap K L) (hc c) = g := sum_coordPoly b g
    have hdiv : ∀ c ∈ S, ∃ q, hc c = f * q := by
      intro c hcS
      refine (hf _).1 ((hK _).2 fun j => ?_)
      have e : X (Sum.inr j) * rename Sum.inl g = ∑ c' ∈ S,
          C (b c') * map (algebraMap K L) (X (Sum.inr j) * rename Sum.inl (hc c')) := by
        conv_lhs => rw [← hsum]
        rw [map_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun c' _ => ?_
        rw [map_mul, rename_C, hmapX]
        ring
      have hmem := coordPoly_mem_of_mem_map b R (e ▸ hg j) c
      rwa [coordPoly_sum, if_pos hcS] at hmem
    choose! q hq using hdiv
    refine ⟨∑ c ∈ S, C (b c) * map (algebraMap K L) (q c), ?_⟩
    conv_lhs => rw [← hsum]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c hcS => ?_
    rw [hq c hcS, map_mul]
    ring
  · rintro ⟨q, rfl⟩ j
    have hfR : X (Sum.inr j) * rename Sum.inl f ∈ R := (hK f).1 ((hf f).2 dvd_rfl) j
    have hmem := Ideal.mem_map_of_mem (map (algebraMap K L)) hfR
    rw [hmapX] at hmem
    rw [map_mul (rename Sum.inl), ← mul_assoc]
    exact Ideal.mul_mem_right _ _ hmem

/- English proof (translation)
Introduce `K L _ _ _ σ n k I f hf`. Set `_ : Algebra K L` to `σ.toAlgebra`. Conclude with `isChowForm_map h I f hf`.
-/
theorem proof (h : RadicalBaseChange.Statement) : ChowFormExtend.Statement := by
  intro K L _ _ _ σ n k I f hf
  let _ : Algebra K L := σ.toAlgebra
  exact isChowForm_map h I f hf

end ChowFormExtend

end

end GroundTheory.Heights₂.Heights
