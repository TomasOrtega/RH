import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DltEqZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyDvdPowOfAevalEqZero

noncomputable section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial

namespace GlobalTheory.UnitLemma.TorusPts

section Ring

variable {A : Type} [CommRing A] {I : Type} [Fintype I]

def tt (f h c d : I → A) : A := 1 + ∑ i, ((c i - 1) * f i + (d i - 1) * h i)

/- English proof (translation)
Unfold `tt`. Rewrite using `[mul_add, Finset.mul_sum, Finset.sum_eq_single j]`. Take the linear combination `(c j - 1) * hf j + (d j - 1) * hfh j j`. Introduce `i _ hi`. Take the linear combination `(c i - 1) * hff j i hi.symm + (d i - 1) * hfh j i`.

Simplify using the standard rewrite rules.
-/
theorem f_mul_tt (f h c d : I → A) (hf : ∀ i, f i * f i = f i) (hff : ∀ i j, i ≠ j → f i * f j = 0)
    (hfh : ∀ i j, f i * h j = 0) (j : I) : f j * tt f h c d = c j * f j := by
  classical
  unfold tt
  rw [mul_add, Finset.mul_sum, Finset.sum_eq_single j]
  · linear_combination (c j - 1) * hf j + (d j - 1) * hfh j j
  · intro i _ hi
    linear_combination (c i - 1) * hff j i hi.symm + (d i - 1) * hfh j i
  · simp

/- English proof (translation)
Unfold `tt`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun i _ => add_comm _ _`.
-/
theorem tt_swap (f h c d : I → A) : tt f h c d = tt h f d c := by
  unfold tt
  congr 1
  exact Finset.sum_congr rfl fun i _ => add_comm _ _

/- English proof (translation)
Establish `h1` using `f_mul_tt f h c' d' hf hff hfh`. Establish `h2` using `f_mul_tt h f d' c' hh hhh (fun i j => by rw [mul_comm]; exact hfh j i)`. Rewrite `h2` using `[← tt_swap]`. Establish `h3 : tt f h c d * tt f h c' d' = tt f h c' d' + ∑ i, ((c i - 1) * (f i * tt f h c' d') + (d i - 1) * (h i * tt f h c' d'))` using `by conv_lhs => arg 1; unfold tt`. Rewrite using `[add_mul, one_mul, Finset.sum_mul]`.

Use `congr 1`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`. Rewrite using `[h3]`. Simplify using `only [h1, h2]`. Unfold `tt`.

Rewrite using `[add_assoc, ← Finset.sum_add_distrib]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun i _ => by simp only [Pi.mul_apply]; ring`.
-/
theorem tt_mul (f h c d c' d' : I → A) (hf : ∀ i, f i * f i = f i) (hff : ∀ i j, i ≠ j → f i * f j = 0)
    (hh : ∀ i, h i * h i = h i) (hhh : ∀ i j, i ≠ j → h i * h j = 0)
    (hfh : ∀ i j, f i * h j = 0) : tt f h c d * tt f h c' d' = tt f h (c * c') (d * d') := by
  have h1 := f_mul_tt f h c' d' hf hff hfh
  have h2 := f_mul_tt h f d' c' hh hhh (fun i j => by rw [mul_comm]; exact hfh j i)
  rw [← tt_swap] at h2
  have h3 : tt f h c d * tt f h c' d' =
      tt f h c' d' + ∑ i, ((c i - 1) * (f i * tt f h c' d') + (d i - 1) * (h i * tt f h c' d')) := by
    conv_lhs => arg 1; unfold tt
    rw [add_mul, one_mul, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h3]
  simp only [h1, h2]
  unfold tt
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by simp only [Pi.mul_apply]; ring

/- English proof (translation)
Simplify using `[tt]`.
-/
theorem tt_one (f h : I → A) : tt f h 1 1 = 1 := by simp [tt]

end Ring

/- English proof (translation)
Use `nontriviality O`. Use `⟨X ^ 2 - X, ?_, ?_⟩` and prove the remaining obligations. Use `monicity!`. Simplify using `[pow_two, hf]`.
-/
theorem isIntegral_idem {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {f : A} (hf : f * f = f) :
    IsIntegral O f := by
  nontriviality O
  refine ⟨X ^ 2 - X, ?_, ?_⟩
  · monicity!
  · simp [pow_two, hf]

/- English proof (translation)
Set `J : Ideal B.A` to `Ideal.span {1 - f}`. Establish `hJ : J ≠ ⊤`. Introduce `h`. Establish `: (1 : B.A) ∈ J` using `h ▸ Submodule.mem_top`. Take `⟨r, hr⟩` from `Ideal.mem_span_singleton'.1 this`.

Apply `h0` to reduce the goal to its premises. Take the linear combination `(-f) * hr - r * hf`. Use `haveI : Nontrivial (B.A ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hJ`. Set `φ : K.E →ₐ[K.O] B.A ⧸ J` to `(Ideal.Quotient.mkₐ K.O J).comp (IsScalarTower.toAlgHom K.O K.E B.A)`. Establish `hinj : Function.Injective φ` using `φ.toRingHom.injective`.

Rewrite using `[← isIntegral_algHom_iff φ hinj]`. Establish `h1` using `hx.map (Ideal.Quotient.mkₐ K.O J)`. Establish `h2 : Ideal.Quotient.mkₐ K.O J (algebraMap K.E B.A x * f) = φ x` using `by show Ideal.Quotient.mk J _ = Ideal.Quotient.mk J (algebraMap K.E B.A x)`. Rewrite using `[Ideal.Quotient.eq]`. Conclude with `Ideal.mem_span_singleton'.2 ⟨-algebraMap K.E B.A x, by ring⟩`.

Rewrite `h1` using `[h2]`. Then use the resulting hypothesis.
-/
theorem isIntegral_of_mul_idem {K : UQ} (B : InvAlg K) {f : B.A} (hf : f * f = f) (h0 : f ≠ 0) (x : K.E)
    (hx : IsIntegral K.O (algebraMap K.E B.A x * f)) : IsIntegral K.O x := by
  let J : Ideal B.A := Ideal.span {1 - f}
  have hJ : J ≠ ⊤ := by
    intro h
    have : (1 : B.A) ∈ J := h ▸ Submodule.mem_top
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 this
    apply h0
    linear_combination (-f) * hr - r * hf
  haveI : Nontrivial (B.A ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hJ
  let φ : K.E →ₐ[K.O] B.A ⧸ J := (Ideal.Quotient.mkₐ K.O J).comp (IsScalarTower.toAlgHom K.O K.E B.A)
  have hinj : Function.Injective φ := φ.toRingHom.injective
  rw [← isIntegral_algHom_iff φ hinj]
  have h1 := hx.map (Ideal.Quotient.mkₐ K.O J)
  have h2 : Ideal.Quotient.mkₐ K.O J (algebraMap K.E B.A x * f) = φ x := by
    show Ideal.Quotient.mk J _ = Ideal.Quotient.mk J (algebraMap K.E B.A x)
    rw [Ideal.Quotient.eq]
    exact Ideal.mem_span_singleton'.2 ⟨-algebraMap K.E B.A x, by ring⟩
  rwa [h2] at h1

/- English proof (translation)
Assume the negation of the conclusion as `hlt`. Use `push Not at hlt`. Take `⟨r, hr⟩` from `(IsIntegrallyClosed.isIntegral_iff).1 h`. Establish `ha0 : algebraMap K.O K.E a ≠ 0`. Simplify using `using ha.1`.

Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_lt hlt`. Establish `h1 : algebraMap K.O K.E (a * (a ^ d * r)) = algebraMap K.O K.E 1`. Simplify using `only [map_mul, map_pow, map_one, hr]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Establish `h2` using `IsFractionRing.injective K.O K.E h1`. Conclude with `ha.2.1 (IsUnit.of_mul_eq_one _ h2)`.
-/
theorem le_of_isIntegral {K : UQ} {a : K.O} (ha : K.Small a) (n m : ℕ)
    (h : IsIntegral K.O (((algebraMap K.O K.E a) ^ n)⁻¹ * (algebraMap K.O K.E a) ^ m)) : n ≤ m := by
  by_contra hlt
  push Not at hlt
  obtain ⟨r, hr⟩ := (IsIntegrallyClosed.isIntegral_iff).1 h
  have ha0 : algebraMap K.O K.E a ≠ 0 := by
    simpa using ha.1
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hlt
  have h1 : algebraMap K.O K.E (a * (a ^ d * r)) = algebraMap K.O K.E 1 := by
    simp only [map_mul, map_pow, map_one, hr]
    field_simp
    ring
  have h2 := IsFractionRing.injective K.O K.E h1
  exact ha.2.1 (IsUnit.of_mul_eq_one _ h2)

/- English proof (translation)
Introduce `K B ι _ e S a ha hP k`. Take `⟨hC, hP⟩` from `hP`. Use `choose F hFi hF0 _ _ hFS using hP`. Set `f : {i // i ∉ S} → B.A` to `fun i => F i`. Set `h : {i // i ∉ S} → B.A` to `fun i => B.σ (F i)`.

Establish `hf : ∀ i, f i * f i = f i` using `fun i => hFi i`. Establish `hh : ∀ i, h i * h i = h i` using `fun i => by show B.σ _ * B.σ _ = B.σ _`. Rewrite using `[← map_mul, hFi i]`. Establish `hfe : ∀ i, f i = f i * e i` using `fun i => by`. Rewrite using `[(hFS i i.2).2]`.

Take the linear combination `-(hf i) - (hFS i i.2).1`. Establish `hhe : ∀ i, h i = h i * e i` using `fun i => by`. Rewrite using `[(hFS i i.2).2]`. Take the linear combination `-(hh i) - (hFS i i.2).1`. Establish `hee : ∀ i j : {i // i ∉ S}, i ≠ j → e i * e j = 0` using `fun i j hij => hC.ortho (fun h => hij (Subtype.ext h))`.

Establish `hff : ∀ i j, i ≠ j → f i * f j = 0` using `fun i j hij => by`. Rewrite using `[hfe i, hfe j]`. Take the linear combination `f i * f j * hee i j hij`. Establish `hhh : ∀ i j, i ≠ j → h i * h j = 0` using `fun i j hij => by`. Rewrite using `[hhe i, hhe j]`.

Take the linear combination `h i * h j * hee i j hij`. Establish `hfh : ∀ i j, f i * h j = 0` using `fun i j => by`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Conclude with `(hFS i i.2).1`.

Rewrite using `[hfe i, hhe j]`. Take the linear combination `f i * h j * hee i j hij`. Use `set α : K.E := algebraMap K.O K.E a with hα`. Establish `hα0 : α ≠ 0` using `by simpa [hα] using ha.1`. Set `c : ({i // i ∉ S} → Fin (k + 1)) → {i // i ∉ S} → B.A` to `fun n i => algebraMap K.E B.A (α ^ (n i : ℕ))`.

Set `d : ({i // i ∉ S} → Fin (k + 1)) → {i // i ∉ S} → B.A` to `fun n i => algebraMap K.E B.A (α ^ (n i : ℕ))⁻¹`. Establish `hcd : ∀ n, c n * d n = 1` using `fun n => by`. Use function extensionality and compare the values at `i`. Use `show algebraMap K.E B.A _ * algebraMap K.E B.A _ = 1`. Rewrite using `[← map_mul, mul_inv_cancel₀ (pow_ne_zero _ hα0), map_one]`.

Establish `hinv : ∀ n, tt f h (c n) (d n) * tt f h (d n) (c n) = 1` using `fun n => by`. Rewrite using `[tt_mul f h _ _ _ _ hf hff hh hhh hfh, hcd, mul_comm (d n), hcd, tt_one]`. Establish `hσ : ∀ n, B.σ (tt f h (c n) (d n)) = tt f h (d n) (c n)` using `fun n => by`. Rewrite using `[tt_swap f h (d n)]`. Unfold `tt`.

Establish `hcα : K.c α = α` using `ha.2.2`. Simplify using `only [map_add, map_one, map_sum, map_mul, map_sub, c, d, f, h, B.σ_σ, B.σ_alg, map_inv₀, map_pow, hcα]`. Set `u : ({i // i ∉ S} → Fin (k + 1)) → B.Aˣ` to `fun n => ⟨tt f h (c n) (d n), tt f h (d n) (c n), hinv n, by rw [mul_comm]; exact hinv n⟩`. Set `t : ({i // i ∉ S} → Fin (k + 1)) → B.T` to `fun n => ⟨u n, by show tt f h (c n) (d n) * B.σ (tt f h (c n) (d n)) = 1`. Rewrite using `[hσ, hinv]⟩`.

Establish `hαA : algebraMap K.O B.A a = algebraMap K.E B.A α` using `IsScalarTower.algebraMap_apply _ _ _ _`. Establish `hia : IsIntegral K.O (algebraMap K.E B.A α)` using `hαA ▸ isIntegral_algebraMap`. Establish `key : ∀ n m, ((t n)⁻¹ * t m) ∈ (intUnits K.O B.A).subgroupOf B.T → ∀ i, (n i : ℕ) ≤ m i`. Introduce `n m hnm i`. Establish `h1 : IsIntegral K.O (tt f h (d n) (c n) * tt f h (c m) (d m))` using `hnm.1`.

Rewrite `h1` using `[tt_mul f h _ _ _ _ hf hff hh hhh hfh]`. Establish `h2` using `(isIntegral_idem (O := K.O) (hf i)).mul h1`. Rewrite `h2` using `[f_mul_tt f h _ _ hf hff hfh]`. Apply `le_of_isIntegral ha` to reduce the goal to its premises. Apply `isIntegral_of_mul_idem B (hf i) (hF0 i)` to reduce the goal to its premises.

Rewrite using `[map_mul]`. Conclude with `h2`. Use `⟨fun n => QuotientGroup.mk (t n), ?_, ?_⟩` and prove the remaining obligations. Introduce `n m hnm`. Use function extensionality and compare the values at `i`.

Conclude with `Fin.ext (le_antisymm (key n m (QuotientGroup.eq.1 hnm) i) (key m n (QuotientGroup.eq.1 hnm.symm) i))`. Introduce `n`. Take `⟨w, hw⟩` from `QuotientGroup.mk_out_eq_mul ((intUnits K.O B.A).subgroupOf B.T) (t n)`. Use `show IsIntegral K.O (((((QuotientGroup.mk (t n) : B.T ⧸ (intUnits K.O B.A).subgroupOf B.T).out : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * algebraMap K.O B.A a ^ k : B.A)`. Rewrite using `[hw, Subgroup.coe_mul, mul_inv_rev, Units.val_mul, mul_assoc]`.

Use `IsIntegral.mul w.2.2 ?_` and prove the remaining obligations. Use `show IsIntegral K.O (tt f h (d n) (c n) * _)`. Rewrite using `[hαA]`. Unfold `tt`. Rewrite using `[add_mul, Finset.sum_mul]`.

Use `IsIntegral.add (by rw [one_mul]; exact hia.pow k) (IsIntegral.sum _ fun i _ => ?_)` and prove the remaining obligations. Take `⟨r, hr⟩` from `Nat.exists_eq_add_of_le (Nat.lt_succ_iff.1 (n i).2)`. Establish `h1 : d n i * algebraMap K.E B.A α ^ k = algebraMap K.E B.A α ^ r`. Use `congrFun (hcd n) i` as an intermediate fact. Simplify using `only [Pi.mul_apply, Pi.one_apply, c, map_pow] at this`.

Generalize the expression as in `(n i : ℕ) = j at hr this`. Rewrite using `[hr, pow_add]`. Take the linear combination `algebraMap K.E B.A α ^ r * this`. Establish `h2 : ((d n i - 1) * f i + (c n i - 1) * h i) * algebraMap K.E B.A α ^ k = (algebraMap K.E B.A α ^ r - algebraMap K.E B.A α ^ k) * f i + (algebraMap K.E B.A α ^ (n i : ℕ) - 1) * h i * algebraMap K.E B.A α ^ k`. Rewrite using `[← h1]`.

Simplify using `only [c, map_pow]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h2]`. Conclude with `(((hia.pow r).sub (hia.pow k)).mul (isIntegral_idem (hf i))).add ((((hia.pow _).sub isIntegral_one).mul (isIntegral_idem (hh i))).mul (hia.pow k))`.
-/
theorem torus_points : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] (e : ι → B.A) (S : Finset ι) (a : K.O), K.Small a → IsPre B e S → ∀ k : ℕ, ∃ f : ({i // i ∉ S} → Fin (k + 1)) → B.T ⧸ (intUnits K.O B.A).subgroupOf B.T, Function.Injective f ∧ ∀ n, IsIntegral K.O ((((Quotient.out (f n) : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * algebraMap K.O B.A a ^ k : B.A) := by
  intro K B ι _ e S a ha hP k
  classical
  obtain ⟨hC, hP⟩ := hP
  choose F hFi hF0 _ _ hFS using hP
  let f : {i // i ∉ S} → B.A := fun i => F i
  let h : {i // i ∉ S} → B.A := fun i => B.σ (F i)
  have hf : ∀ i, f i * f i = f i := fun i => hFi i
  have hh : ∀ i, h i * h i = h i := fun i => by
    show B.σ _ * B.σ _ = B.σ _
    rw [← map_mul, hFi i]
  have hfe : ∀ i, f i = f i * e i := fun i => by
    rw [(hFS i i.2).2]
    linear_combination -(hf i) - (hFS i i.2).1
  have hhe : ∀ i, h i = h i * e i := fun i => by
    rw [(hFS i i.2).2]
    linear_combination -(hh i) - (hFS i i.2).1
  have hee : ∀ i j : {i // i ∉ S}, i ≠ j → e i * e j = 0 := fun i j hij =>
    hC.ortho (fun h => hij (Subtype.ext h))
  have hff : ∀ i j, i ≠ j → f i * f j = 0 := fun i j hij => by
    rw [hfe i, hfe j]; linear_combination f i * f j * hee i j hij
  have hhh : ∀ i j, i ≠ j → h i * h j = 0 := fun i j hij => by
    rw [hhe i, hhe j]; linear_combination h i * h j * hee i j hij
  have hfh : ∀ i j, f i * h j = 0 := fun i j => by
    by_cases hij : i = j
    · subst hij; exact (hFS i i.2).1
    · rw [hfe i, hhe j]; linear_combination f i * h j * hee i j hij
  set α : K.E := algebraMap K.O K.E a with hα
  have hα0 : α ≠ 0 := by simpa [hα] using ha.1
  let c : ({i // i ∉ S} → Fin (k + 1)) → {i // i ∉ S} → B.A := fun n i => algebraMap K.E B.A (α ^ (n i : ℕ))
  let d : ({i // i ∉ S} → Fin (k + 1)) → {i // i ∉ S} → B.A := fun n i => algebraMap K.E B.A (α ^ (n i : ℕ))⁻¹
  have hcd : ∀ n, c n * d n = 1 := fun n => by
    funext i
    show algebraMap K.E B.A _ * algebraMap K.E B.A _ = 1
    rw [← map_mul, mul_inv_cancel₀ (pow_ne_zero _ hα0), map_one]
  have hinv : ∀ n, tt f h (c n) (d n) * tt f h (d n) (c n) = 1 := fun n => by
    rw [tt_mul f h _ _ _ _ hf hff hh hhh hfh, hcd, mul_comm (d n), hcd, tt_one]
  have hσ : ∀ n, B.σ (tt f h (c n) (d n)) = tt f h (d n) (c n) := fun n => by
    rw [tt_swap f h (d n)]
    unfold tt
    have hcα : K.c α = α := ha.2.2
    simp only [map_add, map_one, map_sum, map_mul, map_sub, c, d, f, h, B.σ_σ, B.σ_alg, map_inv₀, map_pow, hcα]
  let u : ({i // i ∉ S} → Fin (k + 1)) → B.Aˣ := fun n =>
    ⟨tt f h (c n) (d n), tt f h (d n) (c n), hinv n, by rw [mul_comm]; exact hinv n⟩
  let t : ({i // i ∉ S} → Fin (k + 1)) → B.T := fun n => ⟨u n, by
    show tt f h (c n) (d n) * B.σ (tt f h (c n) (d n)) = 1
    rw [hσ, hinv]⟩
  have hαA : algebraMap K.O B.A a = algebraMap K.E B.A α := IsScalarTower.algebraMap_apply _ _ _ _
  have hia : IsIntegral K.O (algebraMap K.E B.A α) := hαA ▸ isIntegral_algebraMap
  have key : ∀ n m, ((t n)⁻¹ * t m) ∈ (intUnits K.O B.A).subgroupOf B.T → ∀ i, (n i : ℕ) ≤ m i := by
    intro n m hnm i
    have h1 : IsIntegral K.O (tt f h (d n) (c n) * tt f h (c m) (d m)) := hnm.1
    rw [tt_mul f h _ _ _ _ hf hff hh hhh hfh] at h1
    have h2 := (isIntegral_idem (O := K.O) (hf i)).mul h1
    rw [f_mul_tt f h _ _ hf hff hfh] at h2
    apply le_of_isIntegral ha
    apply isIntegral_of_mul_idem B (hf i) (hF0 i)
    rw [map_mul]
    exact h2
  refine ⟨fun n => QuotientGroup.mk (t n), ?_, ?_⟩
  · intro n m hnm
    funext i
    exact Fin.ext (le_antisymm (key n m (QuotientGroup.eq.1 hnm) i) (key m n (QuotientGroup.eq.1 hnm.symm) i))
  · intro n
    obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul ((intUnits K.O B.A).subgroupOf B.T) (t n)
    show IsIntegral K.O (((((QuotientGroup.mk (t n) : B.T ⧸ (intUnits K.O B.A).subgroupOf B.T).out : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * algebraMap K.O B.A a ^ k : B.A)
    rw [hw, Subgroup.coe_mul, mul_inv_rev, Units.val_mul, mul_assoc]
    refine IsIntegral.mul w.2.2 ?_
    show IsIntegral K.O (tt f h (d n) (c n) * _)
    rw [hαA]
    unfold tt
    rw [add_mul, Finset.sum_mul]
    refine IsIntegral.add (by rw [one_mul]; exact hia.pow k) (IsIntegral.sum _ fun i _ => ?_)
    obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le (Nat.lt_succ_iff.1 (n i).2)
    have h1 : d n i * algebraMap K.E B.A α ^ k = algebraMap K.E B.A α ^ r := by
      have := congrFun (hcd n) i
      simp only [Pi.mul_apply, Pi.one_apply, c, map_pow] at this
      generalize (n i : ℕ) = j at hr this
      rw [hr, pow_add]
      linear_combination algebraMap K.E B.A α ^ r * this
    have h2 : ((d n i - 1) * f i + (c n i - 1) * h i) * algebraMap K.E B.A α ^ k =
        (algebraMap K.E B.A α ^ r - algebraMap K.E B.A α ^ k) * f i +
          (algebraMap K.E B.A α ^ (n i : ℕ) - 1) * h i * algebraMap K.E B.A α ^ k := by
      rw [← h1]; simp only [c, map_pow]; ring
    rw [h2]
    exact (((hia.pow r).sub (hia.pow k)).mul (isIntegral_idem (hf i))).add
      ((((hia.pow _).sub isIntegral_one).mul (isIntegral_idem (hh i))).mul (hia.pow k))

end GlobalTheory.UnitLemma.TorusPts
