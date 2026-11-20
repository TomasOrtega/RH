import Mathlib
import Formalism.LocalToGlobal.Columns.ScaledRamifiedLattice
import Formalism.LocalToGlobal.Columns.BaseLemmas
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Development.AbelianVarietyTheory.Counterexamples.PlaceInjectivity.StandardDeterminantUnits

open NumberField IsDedekindDomain Matrix

noncomputable section

namespace GlobalTheory.CharValCompare

open Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.Ker GlobalTheory.Survey.StandardDeterminantUnits

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

omit [StarRing E] in
/- English proof (translation)
Use `⟨val_le_one_of_intAt, fun h => ?_⟩` and prove the remaining obligations. Take `⟨r, s, hs⟩` from `P.exists_primeCompl_mul_eq_of_integer a h`. Conclude with `⟨r, s, s.2, by rw [mul_comm]; exact hs⟩`.
-/
theorem intAt_iff {P : HeightOneSpectrum (𝓞 E)} {a : E} : IntAt P a ↔ P.valuation E a ≤ 1 := by
  refine ⟨val_le_one_of_intAt, fun h => ?_⟩
  obtain ⟨r, s, hs⟩ := P.exists_primeCompl_mul_eq_of_integer a h
  exact ⟨r, s, s.2, by rw [mul_comm]; exact hs⟩

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[mem_conjP, mem_conjP, cO_cO]`.
-/
theorem conjP_conjP (P : HeightOneSpectrum (𝓞 E)) : conjPrime₂ (conjPrime₂ P) = P := by
  ext x
  rw [mem_conjP, mem_conjP, cO_cO]

/- English proof (translation)
Take `⟨r, s, hs, e⟩` from `h`. Use `⟨cO E r, cO E s, by rwa [mem_conjP, cO_cO], ?_⟩` and prove the remaining obligations. Rewrite using `[algebraMap_cO, algebraMap_cO, ← e, star_mul']`.
-/
theorem intAt_star {P : HeightOneSpectrum (𝓞 E)} {a : E} (h : IntAt P a) : IntAt (conjPrime₂ P) (star a) := by
  obtain ⟨r, s, hs, e⟩ := h
  refine ⟨cO E r, cO E s, by rwa [mem_conjP, cO_cO], ?_⟩
  rw [algebraMap_cO, algebraMap_cO, ← e, star_mul']

omit [StarRing E] in
/- English proof (translation)
Rewrite using `[intAt_iff, intAt_iff, map_inv₀]`. Establish `h1 : 0 < P.valuation E a` using `zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 h0)`. Rewrite using `[inv_le_one₀ h1]`. Conclude with `⟨fun h => ⟨h.le, h.ge⟩, fun h => le_antisymm h.1 h.2⟩`.
-/
theorem val_eq_one_iff {P : HeightOneSpectrum (𝓞 E)} {a : E} (h0 : a ≠ 0) :
    P.valuation E a = 1 ↔ IntAt P a ∧ IntAt P a⁻¹ := by
  rw [intAt_iff, intAt_iff, map_inv₀]
  have h1 : 0 < P.valuation E a := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 h0)
  rw [inv_le_one₀ h1]
  exact ⟨fun h => ⟨h.le, h.ge⟩, fun h => le_antisymm h.1 h.2⟩

/- English proof (translation)
Establish `h0 : a ≠ 0` using `by rintro rfl; simp at h`. Rewrite `h` using `[val_eq_one_iff h0]`. Rewrite using `[val_eq_one_iff (by simpa using h0), ← star_inv₀]`. Conclude with `⟨intAt_star h.1, intAt_star h.2⟩`.
-/
theorem val_star_eq_one {P : HeightOneSpectrum (𝓞 E)} {a : E} (h : P.valuation E a = 1) :
    (conjPrime₂ P).valuation E (star a) = 1 := by
  have h0 : a ≠ 0 := by rintro rfl; simp at h
  rw [val_eq_one_iff h0] at h
  rw [val_eq_one_iff (by simpa using h0), ← star_inv₀]
  exact ⟨intAt_star h.1, intAt_star h.2⟩

def IsFr (P : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E n)) (f : Sp E n ≃ₗ[E] Sp E n) : Prop :=
  ∀ x, f x ∈ localization₂ P.asIdeal N ↔ x ∈ stdAt E n P

/- English proof (translation)
Take `⟨b, hb⟩` from `Formalism.BasicNotions.SkeletonIndexLemmas.exists_basis_locP P hN.fg hN.span_eq_top (n := n) (by simp)`. Set `f : Sp E n ≃ₗ[E] Sp E n` to `b.equivFun`. Establish `h1 : gmap f (Submodule.span (𝓞 E) (Set.range b)) = stdLat E n`. Rewrite using `[stdLat_eq_span]`. Unfold `gmap`.

Rewrite using `[Submodule.map_span, ← Set.range_comp]`. Use `congr 2`. Use function extensionality and compare the values at `i j`. Simplify using `[f, Pi.single_apply, eq_comm]`. Use `⟨f.symm, fun x => ?_⟩` and prove the remaining obligations.

Rewrite using `[← hb, stdAt, ← h1, mem_localization_gmap]`.
-/
theorem exists_isFr (P : HeightOneSpectrum (𝓞 E)) {N : Submodule (𝓞 E) (Sp E n)}
    (hN : Submodule.IsLattice E N) : ∃ f, IsFr P N f := by
  obtain ⟨b, hb⟩ := Formalism.BasicNotions.SkeletonIndexLemmas.exists_basis_locP P hN.fg hN.span_eq_top (n := n) (by simp)
  let f : Sp E n ≃ₗ[E] Sp E n := b.equivFun
  have h1 : gmap f (Submodule.span (𝓞 E) (Set.range b)) = stdLat E n := by
    rw [stdLat_eq_span]
    unfold gmap
    rw [Submodule.map_span, ← Set.range_comp]
    congr 2
    funext i j
    simp [f, Pi.single_apply, eq_comm]
  refine ⟨f.symm, fun x => ?_⟩
  rw [← hb, stdAt, ← h1, mem_localization_gmap]

omit [StarRing E] in
/- English proof (translation)
The claim follows from `Classical.epsilon_spec (p := fun f : Sp E n ≃ₗ[E] Sp E n => ∀ x, f x ∈ localization₂ P.asIdeal N ↔ x ∈ stdAt E n P) h`.
-/
theorem isFr_frameAt {P : HeightOneSpectrum (𝓞 E)} {N : Submodule (𝓞 E) (Sp E n)} (h : ∃ f, IsFr P N f) :
    IsFr P N (frameAt P N) :=
  Classical.epsilon_spec (p := fun f : Sp E n ≃ₗ[E] Sp E n => ∀ x, f x ∈ localization₂ P.asIdeal N ↔ x ∈ stdAt E n P) h

/- English proof (translation)
Establish `h1` using `val_det_le_one (P := P) (g : Sp E n →ₗ[E] Sp E n) fun x hx => (hg x).2 hx`. Establish `h2` using `val_det_le_one (P := P) (g.symm : Sp E n →ₗ[E] Sp E n) fun x hx => (hg _).1 (by simpa using hx)`. Establish `h3 : LinearMap.det (g : Sp E n →ₗ[E] Sp E n) * LinearMap.det (g.symm : Sp E n →ₗ[E] Sp E n) = 1` using `LinearEquiv.det_mul_det_symm g`. Establish `h4` using `congrArg (P.valuation E) h3`. Rewrite `h4` using `[map_mul, map_one]`.

Apply `le_antisymm h1` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation.
-/
theorem val_det_eq_one {P : HeightOneSpectrum (𝓞 E)} (g : Sp E n ≃ₗ[E] Sp E n)
    (hg : ∀ x, g x ∈ stdAt E n P ↔ x ∈ stdAt E n P) : P.valuation E (LinearMap.det (g : Sp E n →ₗ[E] Sp E n)) = 1 := by
  have h1 := val_det_le_one (P := P) (g : Sp E n →ₗ[E] Sp E n) fun x hx => (hg x).2 hx
  have h2 := val_det_le_one (P := P) (g.symm : Sp E n →ₗ[E] Sp E n) fun x hx => (hg _).1 (by simpa using hx)
  have h3 : LinearMap.det (g : Sp E n →ₗ[E] Sp E n) * LinearMap.det (g.symm : Sp E n →ₗ[E] Sp E n) = 1 :=
    LinearEquiv.det_mul_det_symm g
  have h4 := congrArg (P.valuation E) h3
  rw [map_mul, map_one] at h4
  apply le_antisymm h1
  calc (1 : _) = _ := h4.symm
    _ ≤ _ := mul_le_of_le_one_right' h2

abbrev dt (f : Sp E n ≃ₗ[E] Sp E n) : E := ((LinearEquiv.det f : Eˣ) : E)

omit [NumberField E] [StarRing E] in
/- English proof (translation)
The claim follows from `LinearEquiv.coe_det f`.
-/
theorem dt_eq (f : Sp E n ≃ₗ[E] Sp E n) : dt f = LinearMap.det (f : Sp E n →ₗ[E] Sp E n) := LinearEquiv.coe_det f

omit [NumberField E] [StarRing E] in
/- English proof (translation)
The claim follows from `Units.ne_zero _`.
-/
theorem dt_ne (f : Sp E n ≃ₗ[E] Sp E n) : dt f ≠ 0 := Units.ne_zero _

/- English proof (translation)
The claim follows from `le_locP P _ (by simpa using single_mem_stdLat (E := E) i 1)`.
-/
theorem single_mem_stdAt (P : HeightOneSpectrum (𝓞 E)) (i : Fin n) : (Pi.single i (1 : E) : Sp E n) ∈ stdAt E n P :=
  le_locP P _ (by simpa using single_mem_stdLat (E := E) i 1)

omit [StarRing E] in
/- English proof (translation)
The claim follows from `Finset.sum_induction f (IntAt P) (fun _ _ => IntAt.add) (by simpa using IntAt.coe P 0) h`.
-/
theorem intAt_sum {P : HeightOneSpectrum (𝓞 E)} {ι : Type} (s : Finset ι) (f : ι → E) (h : ∀ i ∈ s, IntAt P (f i)) :
    IntAt P (∑ i ∈ s, f i) :=
  Finset.sum_induction f (IntAt P) (fun _ _ => IntAt.add) (by simpa using IntAt.coe P 0) h

/- English proof (translation)
Set `F : Matrix (Fin n) (Fin n) E` to `LinearMap.toMatrix' (f : Sp E n →ₗ[E] Sp E n)`. Establish `hF : ∀ z x : Sp E n, hStd E n (f z) x = hStd E n z (Fᴴ *ᵥ x)`. Introduce `z x`. Establish `: f z = F *ᵥ z` using `by simp [F, LinearMap.toMatrix'_mulVec]`. Rewrite using `[this]`.

Express the relevant statement in the definitionally equal form `star (F *ᵥ z) ⬝ᵥ x = star z ⬝ᵥ (Fᴴ *ᵥ x)`. Rewrite using `[Matrix.star_mulVec, Matrix.dotProduct_mulVec]`. Establish `key : ∀ x, Fᴴ *ᵥ x ∈ stdAt E n (conjPrime₂ P) ↔ x ∈ localization₂ (conjPrime₂ P).asIdeal N`. Introduce `x`. Rewrite using `[mem_at_conj hN.1.fg hN.2, stdAt, mem_localization_standardLattice]`.

Prove the components needed by the constructor for the conclusion. Introduce `h y hy`. Take `⟨z, rfl⟩` from `f.surjective y`. Rewrite using `[hF, hStd_apply]`. Establish `hz` using `(mem_localization_standardLattice P z).1 ((hf z).1 hy)`.

Conclude with `intAt_sum _ _ fun i _ => (intAt_star (hz i)).mul (h i)`. Introduce `h i`. Use `h _ ((hf _).2 (single_mem_stdAt P i))` as an intermediate fact. Rewrite `this` using `[hF, hStd_single_left]`. Then use the resulting hypothesis. Establish `hd : LinearMap.det (Matrix.toLin' Fᴴ ∘ₗ (f' : Sp E n →ₗ[E] Sp E n)) = star (dt f) * dt f'`.

Rewrite using `[LinearMap.det_comp, LinearMap.det_toLin', Matrix.det_conjTranspose, LinearMap.det_toMatrix', dt_eq, dt_eq]`. Establish `h0 : LinearMap.det (Matrix.toLin' Fᴴ ∘ₗ (f' : Sp E n →ₗ[E] Sp E n)) ≠ 0`. Rewrite using `[hd]`. Conclude with `mul_ne_zero (star_ne_zero.2 (dt_ne _)) (dt_ne _)`. Use `val_det_eq_one (P := conjPrime₂ P) (LinearMap.equivOfDetNeZero _ h0) fun x => by` as an intermediate fact.

Rewrite using `[← hf' x, ← key]`. Both sides reduce to the same expression. Rewrite using `[← hd]`. Conclude with `this`.
-/
theorem val_dual {P : HeightOneSpectrum (𝓞 E)} {N : Submodule (𝓞 E) (Sp E n)} (hN : IsSdLat N)
    {f f' : Sp E n ≃ₗ[E] Sp E n} (hf : IsFr P N f) (hf' : IsFr (conjPrime₂ P) N f') :
    (conjPrime₂ P).valuation E (star (dt f) * dt f') = 1 := by
  classical
  let F : Matrix (Fin n) (Fin n) E := LinearMap.toMatrix' (f : Sp E n →ₗ[E] Sp E n)
  have hF : ∀ z x : Sp E n, hStd E n (f z) x = hStd E n z (Fᴴ *ᵥ x) := by
    intro z x
    have : f z = F *ᵥ z := by simp [F, LinearMap.toMatrix'_mulVec]
    rw [this]
    change star (F *ᵥ z) ⬝ᵥ x = star z ⬝ᵥ (Fᴴ *ᵥ x)
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec]
  have key : ∀ x, Fᴴ *ᵥ x ∈ stdAt E n (conjPrime₂ P) ↔ x ∈ localization₂ (conjPrime₂ P).asIdeal N := by
    intro x
    rw [mem_at_conj hN.1.fg hN.2, stdAt, mem_localization_standardLattice]
    constructor
    · intro h y hy
      obtain ⟨z, rfl⟩ := f.surjective y
      rw [hF, hStd_apply]
      have hz := (mem_localization_standardLattice P z).1 ((hf z).1 hy)
      exact intAt_sum _ _ fun i _ => (intAt_star (hz i)).mul (h i)
    · intro h i
      have := h _ ((hf _).2 (single_mem_stdAt P i))
      rwa [hF, hStd_single_left] at this
  have hd : LinearMap.det (Matrix.toLin' Fᴴ ∘ₗ (f' : Sp E n →ₗ[E] Sp E n)) = star (dt f) * dt f' := by
    rw [LinearMap.det_comp, LinearMap.det_toLin', Matrix.det_conjTranspose, LinearMap.det_toMatrix', dt_eq, dt_eq]
  have h0 : LinearMap.det (Matrix.toLin' Fᴴ ∘ₗ (f' : Sp E n →ₗ[E] Sp E n)) ≠ 0 := by
    rw [hd]
    exact mul_ne_zero (star_ne_zero.2 (dt_ne _)) (dt_ne _)
  have := val_det_eq_one (P := conjPrime₂ P) (LinearMap.equivOfDetNeZero _ h0) fun x => by
    rw [← hf' x, ← key]
    rfl
  rw [← hd]
  exact this

def detI (N : Submodule (𝓞 E) (Sp E n)) : Submodule (𝓞 E) E :=
  Submodule.span (𝓞 E) {x | ∃ A : Matrix (Fin n) (Fin n) E, (∀ v ∈ stdLat E n, A.mulVec v ∈ N) ∧ x = A.det}

def Gen (P : HeightOneSpectrum (𝓞 E)) (I : Submodule (𝓞 E) E) (a : E) : Prop :=
  a ≠ 0 ∧ ∀ x, x ∈ localization₂ P.asIdeal I ↔ P.valuation E x ≤ P.valuation E a

omit [StarRing E] in
/- English proof (translation)
Rewrite using `[HeightOneSpectrum.valuation_of_algebraMap]`. Conclude with `(HeightOneSpectrum.intValuation_eq_one_iff).2 hs`.
-/
theorem val_of_notMem {P : HeightOneSpectrum (𝓞 E)} {s : 𝓞 E} (hs : s ∉ P.asIdeal) :
    P.valuation E (algebraMap (𝓞 E) E s) = 1 := by
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  exact (HeightOneSpectrum.intValuation_eq_one_iff).2 hs

omit [StarRing E] in
/- English proof (translation)
Use `⟨h0, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩` and prove the remaining obligations. Take `⟨s, hs, hx⟩` from `hx`. Use `h _ hx` as an intermediate fact. Rewrite `this` using `[Algebra.smul_def, map_mul, val_of_notMem hs, one_mul]`. Then use the resulting hypothesis. Take `⟨s, hs, ha⟩` from `ha`.

Establish `h1 : IntAt P (x / a)`. Rewrite using `[intAt_iff, map_div₀]`. Conclude with `div_le_one_of_le₀ hx zero_le`. Take `⟨r, t, ht, e⟩` from `h1`. Use `⟨s * t, P.asIdeal.primeCompl.mul_mem hs ht, ?_⟩` and prove the remaining obligations.

Establish `: (s * t) • x = r • (s • a)`. Simplify using `only [Algebra.smul_def, map_mul]`. Rewrite using `[← e]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`.

Conclude with `I.smul_mem _ ha`.
-/
theorem gen_of {P : HeightOneSpectrum (𝓞 E)} {I : Submodule (𝓞 E) E} {a : E} (h0 : a ≠ 0) (ha : a ∈ localization₂ P.asIdeal I)
    (h : ∀ x ∈ I, P.valuation E x ≤ P.valuation E a) : Gen P I a := by
  refine ⟨h0, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · obtain ⟨s, hs, hx⟩ := hx
    have := h _ hx
    rwa [Algebra.smul_def, map_mul, val_of_notMem hs, one_mul] at this
  · obtain ⟨s, hs, ha⟩ := ha
    have h1 : IntAt P (x / a) := by
      rw [intAt_iff, map_div₀]
      exact div_le_one_of_le₀ hx zero_le
    obtain ⟨r, t, ht, e⟩ := h1
    refine ⟨s * t, P.asIdeal.primeCompl.mul_mem hs ht, ?_⟩
    have : (s * t) • x = r • (s • a) := by
      simp only [Algebra.smul_def, map_mul]
      rw [← e]
      field_simp
    rw [this]
    exact I.smul_mem _ ha

omit [StarRing E] in
/- English proof (translation)
The claim follows from `le_antisymm ((hb.2 a).1 ((ha.2 a).2 le_rfl)) ((ha.2 b).1 ((hb.2 b).2 le_rfl))`.
-/
theorem Gen.val_eq {P : HeightOneSpectrum (𝓞 E)} {I : Submodule (𝓞 E) E} {a b : E} (ha : Gen P I a) (hb : Gen P I b) :
    P.valuation E a = P.valuation E b :=
  le_antisymm ((hb.2 a).1 ((ha.2 a).2 le_rfl)) ((ha.2 b).1 ((hb.2 b).2 le_rfl))

/- English proof (translation)
Use `gen_of (dt_ne _) ?_ ?_` and prove the remaining obligations. Establish `: ∀ i : Fin n, ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • f (Pi.single i 1) ∈ N` using `fun i => (mem_locP _ _ _).1 ((hf _).2 (single_mem_stdAt P i)) choose s hs hs' using this`. Establish `hp : ∏ i, s i ∉ P.asIdeal` using `fun hm => by`. Take `⟨y, _, h⟩` from `(Ideal.IsPrime.prod_mem_iff (hp := P.isPrime)).1 hm`. Conclude with `hs y h`.

Use `⟨(∏ i, s i) ^ n, P.asIdeal.primeCompl.pow_mem hp n, Submodule.subset_span ⟨algebraMap (𝓞 E) E (∏ i, s i) • LinearMap.toMatrix' (f : Sp E n →ₗ[E] Sp E n), fun v hv => ?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[Matrix.smul_mulVec, LinearMap.toMatrix'_mulVec, algebraMap_smul]`. Rewrite `hv` using `[stdLat_eq_span]`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem y hy`.

Take `⟨i, rfl⟩` from `hy`. Rewrite using `[← Finset.prod_erase_mul _ s (Finset.mem_univ i), mul_smul]`. Conclude with `N.smul_mem _ (hs' i)`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => rw [map_add, smul_add]`.

Conclude with `add_mem ha hb`. Consider the case `smul c a _ ha`. Rewrite using `[← algebraMap_smul E c a, map_smul, algebraMap_smul, smul_comm]`. Conclude with `N.smul_mem _ ha`. Rewrite using `[Matrix.det_smul, LinearMap.det_toMatrix', dt_eq, Algebra.smul_def, map_pow, Fintype.card_fin]`.

Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨A, hA, rfl⟩` from `hy`. Establish `h1` using `val_det_le_one (P := P) ((f.symm : Sp E n →ₗ[E] Sp E n) ∘ₗ Matrix.toLin' A) fun x hx => by`.

Rewrite using `[← hf]`. Take `⟨s, hs, hx⟩` from `hx`. Use `⟨s, hs, ?_⟩` and prove the remaining obligations. Use `hA _ hx` as an intermediate fact. Rewrite `this` using `[← algebraMap_smul E s x, Matrix.mulVec_smul, algebraMap_smul]`.

Simplify using `using this`. Establish `h2 : A.det = dt f * LinearMap.det ((f.symm : Sp E n →ₗ[E] Sp E n) ∘ₗ Matrix.toLin' A)`. Rewrite using `[LinearMap.det_comp, LinearMap.det_toLin', ← mul_assoc, dt_eq, LinearEquiv.det_mul_det_symm, one_mul]`. Rewrite using `[h2, map_mul]`. Conclude with `mul_le_of_le_one_right' h1`.

Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => exact Valuation.map_add_le _ ha hb`. Consider the case `smul c a _ ha`. Rewrite using `[Algebra.smul_def, map_mul]`. Conclude with `le_trans (mul_le_of_le_one_left' (P.valuation_le_one (K := E) c)) ha`.
-/
theorem gen_detI {P : HeightOneSpectrum (𝓞 E)} {N : Submodule (𝓞 E) (Sp E n)} {f : Sp E n ≃ₗ[E] Sp E n} (hf : IsFr P N f) :
    Gen P (detI N) (dt f) := by
  classical
  refine gen_of (dt_ne _) ?_ ?_
  · have : ∀ i : Fin n, ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • f (Pi.single i 1) ∈ N := fun i =>
      (mem_locP _ _ _).1 ((hf _).2 (single_mem_stdAt P i))
    choose s hs hs' using this
    have hp : ∏ i, s i ∉ P.asIdeal := fun hm => by
      obtain ⟨y, _, h⟩ := (Ideal.IsPrime.prod_mem_iff (hp := P.isPrime)).1 hm
      exact hs y h
    refine ⟨(∏ i, s i) ^ n, P.asIdeal.primeCompl.pow_mem hp n, Submodule.subset_span
      ⟨algebraMap (𝓞 E) E (∏ i, s i) • LinearMap.toMatrix' (f : Sp E n →ₗ[E] Sp E n), fun v hv => ?_, ?_⟩⟩
    · rw [Matrix.smul_mulVec, LinearMap.toMatrix'_mulVec, algebraMap_smul]
      rw [stdLat_eq_span] at hv
      induction hv using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨i, rfl⟩ := hy
        rw [← Finset.prod_erase_mul _ s (Finset.mem_univ i), mul_smul]
        exact N.smul_mem _ (hs' i)
      | zero => simp
      | add a b _ _ ha hb => rw [map_add, smul_add]; exact add_mem ha hb
      | smul c a _ ha =>
        rw [← algebraMap_smul E c a, map_smul, algebraMap_smul, smul_comm]
        exact N.smul_mem _ ha
    · rw [Matrix.det_smul, LinearMap.det_toMatrix', dt_eq, Algebra.smul_def, map_pow, Fintype.card_fin]
  · intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨A, hA, rfl⟩ := hy
      have h1 := val_det_le_one (P := P) ((f.symm : Sp E n →ₗ[E] Sp E n) ∘ₗ Matrix.toLin' A) fun x hx => by
        rw [← hf]
        obtain ⟨s, hs, hx⟩ := hx
        refine ⟨s, hs, ?_⟩
        have := hA _ hx
        rw [← algebraMap_smul E s x, Matrix.mulVec_smul, algebraMap_smul] at this
        simpa using this
      have h2 : A.det = dt f * LinearMap.det ((f.symm : Sp E n →ₗ[E] Sp E n) ∘ₗ Matrix.toLin' A) := by
        rw [LinearMap.det_comp, LinearMap.det_toLin', ← mul_assoc, dt_eq, LinearEquiv.det_mul_det_symm, one_mul]
      rw [h2, map_mul]
      exact mul_le_of_le_one_right' h1
    | zero => simp
    | add a b _ _ ha hb => exact Valuation.map_add_le _ ha hb
    | smul c a _ ha =>
      rw [Algebra.smul_def, map_mul]
      exact le_trans (mul_le_of_le_one_left' (P.valuation_le_one (K := E) c)) ha

def NormOne (I : Submodule (𝓞 E) E) : Prop :=
  ∃ J : Submodule (𝓞 E) E, (∀ x, x ∈ J ↔ star x ∈ I) ∧ I * J = 1

def barI (I : Submodule (𝓞 E) E) : Submodule (𝓞 E) E where
  carrier := {x | star x ∈ I}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    show star (a + b) ∈ I
    rw [star_add]; exact add_mem ha hb
  smul_mem' := fun c a ha => by
    show star (c • a) ∈ I
    rw [Algebra.smul_def, star_mul', ← algebraMap_cO, ← Algebra.smul_def]
    exact I.smul_mem _ ha

/- English proof (translation)
Use `⟨barI (detI N), fun _ => Iff.rfl, ?_⟩` and prove the remaining obligations. Use `choose f hf using fun P => exists_isFr P hN.1`. Establish `hg` using `fun P => gen_detI (hf P)`. Establish `hd : ∀ P : HeightOneSpectrum (𝓞 E), P.valuation E (star (dt (f (conjPrime₂ P))) * dt (f P)) = 1` using `fun P => by`. Use `val_dual hN (hf (conjPrime₂ P)) (f' := f P) (by rw [conjP_conjP]; exact hf P)` as an intermediate fact.

Rewrite `this` using `[conjP_conjP]`. Then use the resulting hypothesis. Establish `hle : detI N * barI (detI N) ≤ 1`. Rewrite using `[Submodule.mul_le]`. Introduce `x hx y hy`. Take `⟨r, hr⟩` from `HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E (x * y) fun P => by`.

Establish `h1` using `((hg P).2 x).1 (le_locP P _ hx)`. Establish `h2` using `((hg (conjPrime₂ P)).2 (star y)).1 (le_locP _ _ hy)`. Establish `h3 : IntAt (conjPrime₂ P) (star y / dt (f (conjPrime₂ P)))`. Rewrite using `[intAt_iff, map_div₀]`. Conclude with `div_le_one_of_le₀ h2 zero_le`.

Establish `h4` using `intAt_iff.1 (intAt_star h3)`. Rewrite `h4` using `[conjP_conjP, star_div₀, star_star]`. Establish `h5 : x * y = (x * star (dt (f (conjPrime₂ P)))) * (y / star (dt (f (conjPrime₂ P))))`. Establish `: star (dt (f (conjPrime₂ P))) ≠ 0` using `star_ne_zero.2 (dt_ne _)`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[h5, map_mul]`. Use `mul_le_one' ?_ h4` and prove the remaining obligations. Rewrite using `[← hd P, map_mul, map_mul, mul_comm]`. Conclude with `mul_le_mul_right h1 _`. Conclude with `Submodule.mem_one.2 ⟨r, hr⟩`.

Use `le_antisymm hle ?_` and prove the remaining obligations. Rewrite using `[Submodule.one_le]`. Assume the negation of the conclusion as `h1`. Establish `hne : (detI N * barI (detI N)).comap (Algebra.linearMap (𝓞 E) E) ≠ ⊤` using `fun h => h1 (by`. Establish `: (1 : 𝓞 E) ∈ (detI N * barI (detI N)).comap (Algebra.linearMap (𝓞 E) E)` using `h ▸ Submodule.mem_top`.

Simplify using `using this)`. Take `⟨M, hM, hle'⟩` from `Ideal.exists_le_maximal _ hne`. Set `P : HeightOneSpectrum (𝓞 E)` to `⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField E)⟩`. Take `⟨s, hs, h2⟩` from `(mem_locP _ _ _).1 (((hg P).2 _).2 le_rfl)`. Take `⟨t, ht, h3⟩` from `(mem_locP _ _ _).1 (((hg (conjPrime₂ P)).2 _).2 le_rfl)`.

Establish `h4 : star (t • dt (f (conjPrime₂ P))) ∈ barI (detI N)` using `by show star (star _) ∈ detI N`. Rewrite using `[star_star]` and apply the resulting hypothesis. Establish `h5` using `Submodule.mul_mem_mul h2 h4`. Take `⟨r, hr⟩` from `Submodule.mem_one.1 (hle h5)`. Establish `h6 : r ∈ P.asIdeal` using `hle' (by`.

Rewrite using `[Submodule.mem_comap, Algebra.linearMap_apply]`. Rewrite using `[hr])` and apply the resulting hypothesis. Establish `h7 : P.valuation E (algebraMap (𝓞 E) E r) = 1`. Rewrite using `[hr, Algebra.smul_def, Algebra.smul_def, star_mul', ← algebraMap_cO, mul_mul_mul_comm, map_mul, map_mul, val_of_notMem hs, val_of_notMem (s := cO E t) ht, mul_comm (dt _), hd P]`. Simplify using the standard rewrite rules.

Rewrite `h7` using `[HeightOneSpectrum.valuation_of_algebraMap]`. Conclude with `(HeightOneSpectrum.intValuation_eq_one_iff).1 h7 h6`.
-/
theorem normOne_detI {N : Submodule (𝓞 E) (Sp E n)} (hN : IsSdLat N) : NormOne (detI N) := by
  refine ⟨barI (detI N), fun _ => Iff.rfl, ?_⟩
  choose f hf using fun P => exists_isFr P hN.1
  have hg := fun P => gen_detI (hf P)
  have hd : ∀ P : HeightOneSpectrum (𝓞 E), P.valuation E (star (dt (f (conjPrime₂ P))) * dt (f P)) = 1 := fun P => by
    have := val_dual hN (hf (conjPrime₂ P)) (f' := f P) (by rw [conjP_conjP]; exact hf P)
    rwa [conjP_conjP] at this
  have hle : detI N * barI (detI N) ≤ 1 := by
    rw [Submodule.mul_le]
    intro x hx y hy
    obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E (x * y) fun P => by
      have h1 := ((hg P).2 x).1 (le_locP P _ hx)
      have h2 := ((hg (conjPrime₂ P)).2 (star y)).1 (le_locP _ _ hy)
      have h3 : IntAt (conjPrime₂ P) (star y / dt (f (conjPrime₂ P))) := by
        rw [intAt_iff, map_div₀]
        exact div_le_one_of_le₀ h2 zero_le
      have h4 := intAt_iff.1 (intAt_star h3)
      rw [conjP_conjP, star_div₀, star_star] at h4
      have h5 : x * y = (x * star (dt (f (conjPrime₂ P)))) * (y / star (dt (f (conjPrime₂ P)))) := by
        have : star (dt (f (conjPrime₂ P))) ≠ 0 := star_ne_zero.2 (dt_ne _)
        field_simp
      rw [h5, map_mul]
      refine mul_le_one' ?_ h4
      rw [← hd P, map_mul, map_mul, mul_comm]
      exact mul_le_mul_right h1 _
    exact Submodule.mem_one.2 ⟨r, hr⟩
  refine le_antisymm hle ?_
  rw [Submodule.one_le]
  by_contra h1
  have hne : (detI N * barI (detI N)).comap (Algebra.linearMap (𝓞 E) E) ≠ ⊤ := fun h => h1 (by
    have : (1 : 𝓞 E) ∈ (detI N * barI (detI N)).comap (Algebra.linearMap (𝓞 E) E) := h ▸ Submodule.mem_top
    simpa using this)
  obtain ⟨M, hM, hle'⟩ := Ideal.exists_le_maximal _ hne
  let P : HeightOneSpectrum (𝓞 E) := ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField E)⟩
  obtain ⟨s, hs, h2⟩ := (mem_locP _ _ _).1 (((hg P).2 _).2 le_rfl)
  obtain ⟨t, ht, h3⟩ := (mem_locP _ _ _).1 (((hg (conjPrime₂ P)).2 _).2 le_rfl)
  have h4 : star (t • dt (f (conjPrime₂ P))) ∈ barI (detI N) := by
    show star (star _) ∈ detI N
    rwa [star_star]
  have h5 := Submodule.mul_mem_mul h2 h4
  obtain ⟨r, hr⟩ := Submodule.mem_one.1 (hle h5)
  have h6 : r ∈ P.asIdeal := hle' (by
    rw [Submodule.mem_comap, Algebra.linearMap_apply]
    rwa [hr])
  have h7 : P.valuation E (algebraMap (𝓞 E) E r) = 1 := by
    rw [hr, Algebra.smul_def, Algebra.smul_def, star_mul', ← algebraMap_cO, mul_mul_mul_comm, map_mul, map_mul,
      val_of_notMem hs, val_of_notMem (s := cO E t) ht, mul_comm (dt _), hd P]
    simp
  rw [HeightOneSpectrum.valuation_of_algebraMap] at h7
  exact (HeightOneSpectrum.intValuation_eq_one_iff).1 h7 h6

def lat1 (I : Submodule (𝓞 E) E) : Submodule (𝓞 E) (Sp E 1) :=
  I.comap ((LinearMap.proj (0 : Fin 1) : Sp E 1 →ₗ[E] E).restrictScalars (𝓞 E))

omit [NumberField E] [StarRing E] in
/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_rank_one_lattice (I : Submodule (𝓞 E) E) (x : Sp E 1) : x ∈ lat1 I ↔ x 0 ∈ I := Iff.rfl

omit [NumberField E] [StarRing E] in
/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_localization_rank_one_lattice (P : HeightOneSpectrum (𝓞 E)) (I : Submodule (𝓞 E) E) (x : Sp E 1) :
    x ∈ localization₂ P.asIdeal (lat1 I) ↔ x 0 ∈ localization₂ P.asIdeal I := Iff.rfl

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[detI, Submodule.span_le]`. Introduce and unpack `_ ⟨A, hA, rfl⟩`. Use `hA _ (single_mem_stdLat (E := E) (0 : Fin 1) 1)` as an intermediate fact. Rewrite `this` using `[mem_rank_one_lattice]`.

Simplify `this` using `[Matrix.det_unique]`. Introduce `x hx`. Use `Submodule.subset_span ⟨x • 1, fun v hv => ?_, by simp⟩` and prove the remaining obligations. Take `⟨r, hr⟩` from `Submodule.mem_one.1 (hv 0 (Set.mem_univ _))`. Rewrite using `[mem_rank_one_lattice, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.smul_apply, ← hr, smul_eq_mul, mul_comm, ← Algebra.smul_def]`.

Conclude with `I.smul_mem _ hx`.
-/
theorem det_ideal_rank_one_lattice (I : Submodule (𝓞 E) E) : detI (lat1 I) = I := by
  apply le_antisymm
  · rw [detI, Submodule.span_le]
    rintro _ ⟨A, hA, rfl⟩
    have := hA _ (single_mem_stdLat (E := E) (0 : Fin 1) 1)
    rw [mem_rank_one_lattice] at this
    simpa [Matrix.det_unique] using this
  · intro x hx
    refine Submodule.subset_span ⟨x • 1, fun v hv => ?_, by simp⟩
    obtain ⟨r, hr⟩ := Submodule.mem_one.1 (hv 0 (Set.mem_univ _))
    rw [mem_rank_one_lattice, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.smul_apply, ← hr, smul_eq_mul, mul_comm, ← Algebra.smul_def]
    exact I.smul_mem _ hx

/- English proof (translation)
Take `⟨J, hJ, hIJ⟩` from `hI`. Use `⟨⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Establish `hfg : I.FG` using `Submodule.fg_of_isUnit (IsUnit.of_mul_eq_one J hIJ)`. Establish `: lat1 I = I.map ((LinearEquiv.funUnique (Fin 1) (𝓞 E) E).symm : E →ₗ[𝓞 E] Sp E 1)`. Rewrite using `[Submodule.map_equiv_eq_comap_symm]`.

Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `hfg.map _`. Take `⟨a, ha, h0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot (p := I) (by`. Introduce and unpack `rfl`.

Rewrite `hIJ` using `[Submodule.bot_mul]`. Establish `: (1 : E) ∈ (⊥ : Submodule (𝓞 E) E)` using `hIJ ▸ Submodule.mem_one.2 ⟨1, map_one _⟩`. Simplify using `at this)`. Rewrite using `[eq_top_iff]`. Introduce `x _`.

Establish `: x = (x 0 / a) • (fun _ => a : Sp E 1)`. Use function extensionality and compare the values at `i`. Rewrite using `[Subsingleton.elim i 0]`. Simplify using `[h0]`. Rewrite using `[this]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ha)`. Use extensionality with `x`. Rewrite using `[mem_dual, mem_rank_one_lattice]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Establish `h1 : ∀ z ∈ I * J, z * x 0 ∈ I`. Introduce `z hz`. Use `Submodule.mul_induction_on hz (fun a ha b hb => ?_) fun a b ha hb => by rw [add_mul]; exact add_mem ha hb` and prove the remaining obligations. Use `h (fun _ => star b) ((hJ b).1 hb)` as an intermediate fact. Rewrite `this` using `[hStd_apply, Fin.sum_univ_one, star_star]`.

Take `⟨r, hr⟩` from `Submodule.mem_one.1 this`. Rewrite using `[mul_assoc, ← hr, mul_comm, ← Algebra.smul_def]`. Conclude with `I.smul_mem _ ha`. Simplify using `using h1 1 (hIJ ▸ Submodule.mem_one.2 ⟨1, map_one _⟩)`. Introduce `h y hy`.

Rewrite using `[hStd_apply, Fin.sum_univ_one, mul_comm, ← hIJ]`. Conclude with `Submodule.mul_mem_mul h ((hJ _).2 (by rw [star_star]; exact hy))`.
-/
theorem self_dual_rank_one_lattice {I : Submodule (𝓞 E) E} (hI : NormOne I) : IsSdLat (lat1 I) := by
  obtain ⟨J, hJ, hIJ⟩ := hI
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have hfg : I.FG := Submodule.fg_of_isUnit (IsUnit.of_mul_eq_one J hIJ)
    have : lat1 I = I.map ((LinearEquiv.funUnique (Fin 1) (𝓞 E) E).symm : E →ₗ[𝓞 E] Sp E 1) := by
      rw [Submodule.map_equiv_eq_comap_symm]
      rfl
    rw [this]
    exact hfg.map _
  · obtain ⟨a, ha, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := I) (by
      rintro rfl
      rw [Submodule.bot_mul] at hIJ
      have : (1 : E) ∈ (⊥ : Submodule (𝓞 E) E) := hIJ ▸ Submodule.mem_one.2 ⟨1, map_one _⟩
      simp at this)
    rw [eq_top_iff]
    intro x _
    have : x = (x 0 / a) • (fun _ => a : Sp E 1) := by
      funext i
      rw [Subsingleton.elim i 0]
      simp [h0]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ha)
  · ext x
    rw [mem_dual, mem_rank_one_lattice]
    constructor
    · intro h
      have h1 : ∀ z ∈ I * J, z * x 0 ∈ I := by
        intro z hz
        refine Submodule.mul_induction_on hz (fun a ha b hb => ?_) fun a b ha hb => by rw [add_mul]; exact add_mem ha hb
        have := h (fun _ => star b) ((hJ b).1 hb)
        rw [hStd_apply, Fin.sum_univ_one, star_star] at this
        obtain ⟨r, hr⟩ := Submodule.mem_one.1 this
        rw [mul_assoc, ← hr, mul_comm, ← Algebra.smul_def]
        exact I.smul_mem _ ha
      simpa using h1 1 (hIJ ▸ Submodule.mem_one.2 ⟨1, map_one _⟩)
    · intro h y hy
      rw [hStd_apply, Fin.sum_univ_one, mul_comm, ← hIJ]
      exact Submodule.mul_mem_mul h ((hJ _).2 (by rw [star_star]; exact hy))

def detFr (f : Sp E n ≃ₗ[E] Sp E n) : Sp E 1 ≃ₗ[E] Sp E 1 := LinearEquiv.smulOfUnit (LinearEquiv.det f)

omit [NumberField E] [StarRing E] in
/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[LinearEquiv.coe_det]`. Establish `: (detFr f : Sp E 1 →ₗ[E] Sp E 1) = dt f • LinearMap.id`. Use extensionality with `x i`. Both sides reduce to the same expression.

Rewrite using `[this, LinearMap.det_smul]`. Simplify using the standard rewrite rules.
-/
theorem det_detFr (f : Sp E n ≃ₗ[E] Sp E n) : LinearEquiv.det (detFr f) = LinearEquiv.det f := by
  apply Units.ext
  rw [LinearEquiv.coe_det]
  have : (detFr f : Sp E 1 →ₗ[E] Sp E 1) = dt f • LinearMap.id := by
    ext x i
    rfl
  rw [this, LinearMap.det_smul]
  simp

/- English proof (translation)
Introduce `x`. Rewrite using `[mem_localization_rank_one_lattice, (gen_detI hf).2, stdAt, mem_localization_standardLattice, Fin.forall_fin_one, intAt_iff]`. Establish `: detFr f x 0 = dt f * x 0` using `rfl`. Rewrite using `[this, map_mul]`. Conclude with `mul_le_iff_le_one_right (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 (dt_ne _)))`.
-/
theorem isFr_detFr {P : HeightOneSpectrum (𝓞 E)} {N : Submodule (𝓞 E) (Sp E n)} {f : Sp E n ≃ₗ[E] Sp E n} (hf : IsFr P N f) :
    IsFr P (lat1 (detI N)) (detFr f) := by
  intro x
  rw [mem_localization_rank_one_lattice, (gen_detI hf).2, stdAt, mem_localization_standardLattice, Fin.forall_fin_one, intAt_iff]
  have : detFr f x 0 = dt f * x 0 := rfl
  rw [this, map_mul]
  exact mul_le_iff_le_one_right (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 (dt_ne _)))

/- English proof (translation)
Unfold `ordDet ordE`. Rewrite using `[(gen_detI (isFr_frameAt ⟨f, hf⟩)).val_eq (gen_detI hf)]`.
-/
theorem ordDet_eq {P : HeightOneSpectrum (𝓞 E)} {N : Submodule (𝓞 E) (Sp E n)} {f : Sp E n ≃ₗ[E] Sp E n} (hf : IsFr P N f) :
    ordDet P N = ordE P (dt f) := by
  unfold ordDet ordE
  rw [(gen_detI (isFr_frameAt ⟨f, hf⟩)).val_eq (gen_detI hf)]

/- English proof (translation)
Take `⟨f, hf⟩` from `exists_isFr P hN`. Rewrite using `[ordDet_eq hf, ordDet_eq (isFr_detFr hf), dt, det_detFr]`.
-/
theorem order_det_rank_one_lattice (P : HeightOneSpectrum (𝓞 E)) {N : Submodule (𝓞 E) (Sp E n)} (hN : Submodule.IsLattice E N) :
    ordDet P (lat1 (detI N)) = ordDet P N := by
  obtain ⟨f, hf⟩ := exists_isFr P hN
  rw [ordDet_eq hf, ordDet_eq (isFr_detFr hf), dt, det_detFr]

omit [StarRing E] in
/- English proof (translation)
Establish `h1 : P.valuation E a ≠ 0` using `(Valuation.ne_zero_iff _).2 h0`. Unfold `ordE`. Rewrite using `[neg_eq_zero]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Rewrite using `[← WithZero.exp_log h1, h, WithZero.exp_zero]`. Introduce `h`. Rewrite using `[h, WithZero.log_one]`.
-/
theorem ordE_eq_zero_iff {P : HeightOneSpectrum (𝓞 E)} {a : E} (h0 : a ≠ 0) : ordE P a = 0 ↔ P.valuation E a = 1 := by
  have h1 : P.valuation E a ≠ 0 := (Valuation.ne_zero_iff _).2 h0
  unfold ordE
  rw [neg_eq_zero]
  constructor
  · intro h
    rw [← WithZero.exp_log h1, h, WithZero.exp_zero]
  · intro h
    rw [h, WithZero.log_one]

/- English proof (translation)
Rewrite using `[ordDet_eq (f := 1) (fun x => by rw [h]; rfl), ordE_eq_zero_iff (dt_ne _)]`. Simplify using the standard rewrite rules.
-/
theorem ordDet_of_std {P : HeightOneSpectrum (𝓞 E)} {N : Submodule (𝓞 E) (Sp E n)} (h : localization₂ P.asIdeal N = stdAt E n P) :
    ordDet P N = 0 := by
  rw [ordDet_eq (f := 1) (fun x => by rw [h]; rfl), ordE_eq_zero_iff (dt_ne _)]
  simp

/- English proof (translation)
Take `⟨f, hf⟩` from `exists_isFr P hN.1`. Take `⟨f', hf'⟩` from `exists_isFr (conjPrime₂ P) hN.1`. Use `val_dual hN hf hf'` as an intermediate fact. Rewrite `h` using `[ordDet_eq hf, ordE_eq_zero_iff (dt_ne _)]`. Rewrite `this` using `[map_mul, val_star_eq_one h, one_mul]`.

Rewrite using `[ordDet_eq hf', ordE_eq_zero_iff (dt_ne _)]` and apply the resulting hypothesis.
-/
theorem ordDet_conj {P : HeightOneSpectrum (𝓞 E)} {N : Submodule (𝓞 E) (Sp E n)} (hN : IsSdLat N) (h : ordDet P N = 0) :
    ordDet (conjPrime₂ P) N = 0 := by
  obtain ⟨f, hf⟩ := exists_isFr P hN.1
  obtain ⟨f', hf'⟩ := exists_isFr (conjPrime₂ P) hN.1
  have := val_dual hN hf hf'
  rw [ordDet_eq hf, ordE_eq_zero_iff (dt_ne _)] at h
  rw [map_mul, val_star_eq_one h, one_mul] at this
  rwa [ordDet_eq hf', ordE_eq_zero_iff (dt_ne _)]

/- English proof (translation)
Take `⟨f, hf⟩` from `exists_isFr P hN`. Rewrite `h` using `[ordDet_eq hf, ordE_eq_zero_iff (dt_ne _)]`. Use extensionality with `x`. Rewrite using `[mem_localization_rank_one_lattice, (gen_detI hf).2, stdAt, mem_localization_standardLattice, Fin.forall_fin_one, intAt_iff, h]`.
-/
theorem standard_rank_one_lattice_of_det {P : HeightOneSpectrum (𝓞 E)} {N : Submodule (𝓞 E) (Sp E n)} (hN : Submodule.IsLattice E N)
    (h : ordDet P N = 0) : localization₂ P.asIdeal (lat1 (detI N)) = stdAt E 1 P := by
  obtain ⟨f, hf⟩ := exists_isFr P hN
  rw [ordDet_eq hf, ordE_eq_zero_iff (dt_ne _)] at h
  ext x
  rw [mem_localization_rank_one_lattice, (gen_detI hf).2, stdAt, mem_localization_standardLattice, Fin.forall_fin_one, intAt_iff, h]

omit [NumberField E] [StarRing E] in
/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, hs, h⟩`. Take `⟨r, hr⟩` from `Submodule.mem_one.1 h`. Conclude with `⟨r, s, hs, by rw [hr, Algebra.smul_def]⟩`. Introduce and unpack `⟨r, s, hs, h⟩`.

Conclude with `⟨s, hs, Submodule.mem_one.2 ⟨r, by rw [← h, Algebra.smul_def]⟩⟩`.
-/
theorem mem_localization_one (P : HeightOneSpectrum (𝓞 E)) (x : E) : x ∈ localization₂ P.asIdeal (1 : Submodule (𝓞 E) E) ↔ IntAt P x := by
  constructor
  · rintro ⟨s, hs, h⟩
    obtain ⟨r, hr⟩ := Submodule.mem_one.1 h
    exact ⟨r, s, hs, by rw [hr, Algebra.smul_def]⟩
  · rintro ⟨r, s, hs, h⟩
    exact ⟨s, hs, Submodule.mem_one.2 ⟨r, by rw [← h, Algebra.smul_def]⟩⟩

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[mem_localization_rank_one_lattice, h, stdAt, mem_localization_standardLattice, Fin.forall_fin_one, mem_localization_one]`.
-/
theorem standard_rank_one_lattice_of_local {P : HeightOneSpectrum (𝓞 E)} {I : Submodule (𝓞 E) E}
    (h : localization₂ P.asIdeal I = localization₂ P.asIdeal (1 : Submodule (𝓞 E) E)) : localization₂ P.asIdeal (lat1 I) = stdAt E 1 P := by
  ext x
  rw [mem_localization_rank_one_lattice, h, stdAt, mem_localization_standardLattice, Fin.forall_fin_one, mem_localization_one]

omit [StarRing E] in

/- English proof (translation)
Take `rfl` from `eq_prW_of_mem w hp h`. Establish `hp0 : ((prW w : ℕ) : 𝓞 E) ≠ 0` using `by exact_mod_cast hp.ne_zero`. Establish `hv : w.valuation E ((prW w : ℕ) : E) = w.intValuation ((prW w : ℕ) : 𝓞 E)`. Rewrite using `[← HeightOneSpectrum.valuation_of_algebraMap (K := E)]`. Conclude with `congrArg _ (map_natCast (algebraMap (𝓞 E) E) _).symm`.

Establish `hne0 : w.intValuation ((prW w : ℕ) : 𝓞 E) ≠ 0` using `w.intValuation_ne_zero _ hp0`. Establish `hmem : ∀ k : ℕ, ((prW w : ℕ) : 𝓞 E) ∈ w.asIdeal ^ k ↔ (k : ℤ) ≤ ordE w ((prW w : ℕ) : E)`. Introduce `k`. Rewrite using `[← w.intValuation_le_pow_iff_mem, ordE, hv, ← WithZero.log_le_iff_le_exp hne0, le_neg]`. Take `⟨m, hm⟩` from `Int.eq_ofNat_of_zero_le ((hmem 0).1 (by simp))`.

Establish `hmap : (w.asIdeal.under ℤ).map (algebraMap ℤ (𝓞 E)) = Ideal.span {((prW w : ℕ) : 𝓞 E)}` using `by conv_lhs => rw [← Int.ideal_span_absNorm_eq_self (w.asIdeal.under ℤ)]`. Rewrite using `[Ideal.map_span, Set.image_singleton]`. Use `congr 2`. Simplify using `[prW]`. Establish `hne : w.asIdeal.under ℤ ≠ ⊥`.

Introduce `h`. Rewrite `hmap` using `[h, Ideal.map_bot]`. Conclude with `hp0 (Ideal.span_singleton_eq_bot.1 hmap.symm)`. Establish `h1 : (w.asIdeal.under ℤ).ramificationIdx' w.asIdeal = m`. Apply `Ideal.ramificationIdx'_spec` to reduce the goal to its premises.

Rewrite using `[hmap, Ideal.span_singleton_le_iff_mem, hmem, hm]`. Rewrite using `[hmap, Ideal.span_singleton_le_iff_mem, hmem, hm]`. Use `push_cast`. Use linear arithmetic over natural numbers and integers. Establish `h2 : (w.asIdeal.under ℤ).ramificationIdx' w.asIdeal = w.asIdeal.ramificationIdx ℤ` using `Ideal.ramificationIdx'_eq_ramificationIdx _ _ hne`.

Unfold `eW`. Rewrite using `[← h2, h1, hm]`.
-/
theorem ordE_prime (w : HeightOneSpectrum (𝓞 E)) {p : ℕ} (hp : p.Prime) (h : ((p : ℕ) : 𝓞 E) ∈ w.asIdeal) :
    ordE w (p : E) = eW w := by
  obtain rfl := eq_prW_of_mem w hp h
  have hp0 : ((prW w : ℕ) : 𝓞 E) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hv : w.valuation E ((prW w : ℕ) : E) = w.intValuation ((prW w : ℕ) : 𝓞 E) := by
    rw [← HeightOneSpectrum.valuation_of_algebraMap (K := E)]
    exact congrArg _ (map_natCast (algebraMap (𝓞 E) E) _).symm
  have hne0 : w.intValuation ((prW w : ℕ) : 𝓞 E) ≠ 0 := w.intValuation_ne_zero _ hp0
  have hmem : ∀ k : ℕ, ((prW w : ℕ) : 𝓞 E) ∈ w.asIdeal ^ k ↔ (k : ℤ) ≤ ordE w ((prW w : ℕ) : E) := by
    intro k
    rw [← w.intValuation_le_pow_iff_mem, ordE, hv, ← WithZero.log_le_iff_le_exp hne0, le_neg]
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le ((hmem 0).1 (by simp))
  have hmap : (w.asIdeal.under ℤ).map (algebraMap ℤ (𝓞 E)) = Ideal.span {((prW w : ℕ) : 𝓞 E)} := by
    conv_lhs => rw [← Int.ideal_span_absNorm_eq_self (w.asIdeal.under ℤ)]
    rw [Ideal.map_span, Set.image_singleton]
    congr 2
    simp [prW]
  have hne : w.asIdeal.under ℤ ≠ ⊥ := by
    intro h
    rw [h, Ideal.map_bot] at hmap
    exact hp0 (Ideal.span_singleton_eq_bot.1 hmap.symm)
  have h1 : (w.asIdeal.under ℤ).ramificationIdx' w.asIdeal = m := by
    apply Ideal.ramificationIdx'_spec
    · rw [hmap, Ideal.span_singleton_le_iff_mem, hmem, hm]
    · rw [hmap, Ideal.span_singleton_le_iff_mem, hmem, hm]
      push_cast
      omega
  have h2 : (w.asIdeal.under ℤ).ramificationIdx' w.asIdeal = w.asIdeal.ramificationIdx ℤ :=
    Ideal.ramificationIdx'_eq_ramificationIdx _ _ hne
  unfold eW
  rw [← h2, h1, hm]

end GlobalTheory.CharValCompare
