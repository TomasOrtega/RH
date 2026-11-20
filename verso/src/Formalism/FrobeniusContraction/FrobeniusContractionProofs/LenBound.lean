import Formalism.FrobeniusContraction.Statement

noncomputable section

namespace Formalism.WachCohomologyFacts.PLenBound

variable {O : Type} [CommRing O]

/- English proof (translation)
Establish `hker : ∀ i, Ideal.span {a} ≤ LinearMap.ker (LinearMap.toSpanSingleton O P (v i))` using `fun i => by`. Use `Ideal.span_le.2 (Set.singleton_subset_iff.2 ?_)` and prove the remaining obligations. Use `show LinearMap.toSpanSingleton O P (v i) a = 0`. Rewrite using `[LinearMap.toSpanSingleton_apply]`. Conclude with `hv i`.

Set `f : ι → (O ⧸ Ideal.span {a} →ₗ[O] P)` to `fun i => (Ideal.span {a}).liftQ (LinearMap.toSpanSingleton O P (v i)) (hker i)`. Set `g : (ι → O ⧸ Ideal.span {a}) →ₗ[O] P` to `∑ i, f i ∘ₗ LinearMap.proj i`. Establish `hg : ∀ i, g (Pi.single i (Submodule.Quotient.mk 1)) = v i`. Introduce `i`. Use `show (∑ j, f j ∘ₗ LinearMap.proj j) (Pi.single i (Submodule.Quotient.mk 1)) = v i`.

Rewrite using `[LinearMap.sum_apply, Finset.sum_eq_single i]`. Rewrite using `[LinearMap.comp_apply, LinearMap.proj_apply, Pi.single_eq_same] show LinearMap.toSpanSingleton O P (v i) 1 = v i`. Rewrite using `[LinearMap.toSpanSingleton_apply, one_smul]`. Introduce `j _ hj`. Rewrite using `[LinearMap.comp_apply, LinearMap.proj_apply, Pi.single_eq_of_ne hj, map_zero]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ i) h`. Establish `hsurj : Function.Surjective g`. Rewrite using `[← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`.

Conclude with `⟨_, hg i⟩`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Module.length_pi, ENat.card_eq_coe_fintype_card]`.
-/
theorem length_le_of_span {P : Type} [AddCommGroup P] [Module O P] {ι : Type} [Fintype ι]
    (v : ι → P) (a : O) (hspan : Submodule.span O (Set.range v) = ⊤) (hv : ∀ i, a • v i = 0) :
    Module.length O P ≤ (Fintype.card ι : ℕ∞) * Module.length O (O ⧸ Ideal.span {a}) := by
  classical
  have hker : ∀ i, Ideal.span {a} ≤ LinearMap.ker (LinearMap.toSpanSingleton O P (v i)) := fun i => by
    refine Ideal.span_le.2 (Set.singleton_subset_iff.2 ?_)
    show LinearMap.toSpanSingleton O P (v i) a = 0
    rw [LinearMap.toSpanSingleton_apply]
    exact hv i
  let f : ι → (O ⧸ Ideal.span {a} →ₗ[O] P) := fun i =>
    (Ideal.span {a}).liftQ (LinearMap.toSpanSingleton O P (v i)) (hker i)
  let g : (ι → O ⧸ Ideal.span {a}) →ₗ[O] P := ∑ i, f i ∘ₗ LinearMap.proj i
  have hg : ∀ i, g (Pi.single i (Submodule.Quotient.mk 1)) = v i := by
    intro i
    show (∑ j, f j ∘ₗ LinearMap.proj j) (Pi.single i (Submodule.Quotient.mk 1)) = v i
    rw [LinearMap.sum_apply, Finset.sum_eq_single i]
    · rw [LinearMap.comp_apply, LinearMap.proj_apply, Pi.single_eq_same]
      show LinearMap.toSpanSingleton O P (v i) 1 = v i
      rw [LinearMap.toSpanSingleton_apply, one_smul]
    · intro j _ hj
      rw [LinearMap.comp_apply, LinearMap.proj_apply, Pi.single_eq_of_ne hj, map_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hsurj : Function.Surjective g := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨_, hg i⟩
  calc Module.length O P ≤ Module.length O (ι → O ⧸ Ideal.span {a}) :=
        Module.length_le_of_surjective g hsurj
    _ = (Fintype.card ι : ℕ∞) * Module.length O (O ⧸ Ideal.span {a}) := by
        rw [Module.length_pi, ENat.card_eq_coe_fintype_card]

/- English proof (translation)
Proceed by induction on `e with`. Consider the case `zero`. Rewrite using `[pow_zero, Ideal.span_singleton_one, Nat.cast_zero, zero_mul]`. Use `haveI : Subsingleton (O ⧸ (⊤ : Ideal O)) := ⟨fun x y => by`. Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`.

Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`. Conclude with `(Submodule.Quotient.eq _).2 Submodule.mem_top⟩`. Conclude with `le_of_eq (Module.length_eq_zero)`. Consider the case `succ e ih`. Establish `hle : Ideal.span {a ^ (e + 1)} ≤ Ideal.span {a ^ e}` using `Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow a (Nat.le_succ e))`.

Establish `hex` using `Module.length_eq_add_of_exact (LinearMap.ker (Submodule.factor hle)).subtype (Submodule.factor hle) (Submodule.injective_subtype _) (Submodule.factor_surjective hle) (LinearMap.exact_subtype_ker_map _)`. Set `f0 : O →ₗ[O] O ⧸ Ideal.span {a ^ (e + 1)}` to `(Ideal.span {a ^ (e + 1)}).mkQ ∘ₗ LinearMap.mulLeft O (a ^ e)`. Establish `hf0 : Ideal.span {a} ≤ LinearMap.ker f0`. Use `Ideal.span_le.2 (Set.singleton_subset_iff.2 ?_)` and prove the remaining obligations. Use `show (Ideal.span {a ^ (e + 1)}).mkQ (a ^ e * a) = 0`.

Rewrite using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, ← pow_succ]`. Conclude with `Ideal.subset_span rfl`. Set `f` to `(Ideal.span {a}).liftQ f0 hf0`. Establish `hfk : ∀ x, f x ∈ LinearMap.ker (Submodule.factor hle)`. Introduce `x`.

Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Rewrite using `[LinearMap.mem_ker]`. Use `show (Submodule.Quotient.mk (a ^ e * y) : O ⧸ Ideal.span {a ^ e}) = 0`. Rewrite using `[Submodule.Quotient.mk_eq_zero]`. Conclude with `Ideal.mem_span_singleton'.2 ⟨y, mul_comm _ _⟩`.

Set `f' : O ⧸ Ideal.span {a} →ₗ[O] LinearMap.ker (Submodule.factor hle)` to `LinearMap.codRestrict _ f hfk`. Establish `hf'surj : Function.Surjective f'`. Introduce and unpack `⟨z, hz⟩`. Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective _ z`. Establish `hy : y ∈ Ideal.span {a ^ e}`.

Rewrite `hz` using `[LinearMap.mem_ker]`. Conclude with `(Submodule.Quotient.mk_eq_zero _).1 hz`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.1 hy`. Use `⟨Submodule.Quotient.mk c, Subtype.ext ?_⟩` and prove the remaining obligations. Use `show (Submodule.Quotient.mk (a ^ e * c) : O ⧸ Ideal.span {a ^ (e + 1)}) = Submodule.Quotient.mk (c * a ^ e)`.

Rewrite using `[mul_comm]`. Establish `hk` using `Module.length_le_of_surjective f' hf'surj`. Rewrite using `[hex, Nat.cast_succ, add_mul, one_mul]`. Conclude with `(add_le_add hk ih).trans (le_of_eq (add_comm _ _))`.
-/
theorem length_quot_pow_le (a : O) (e : ℕ) :
    Module.length O (O ⧸ Ideal.span {a ^ e}) ≤ (e : ℕ∞) * Module.length O (O ⧸ Ideal.span {a}) := by
  induction e with
  | zero =>
    rw [pow_zero, Ideal.span_singleton_one, Nat.cast_zero, zero_mul]
    haveI : Subsingleton (O ⧸ (⊤ : Ideal O)) := ⟨fun x y => by
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      exact (Submodule.Quotient.eq _).2 Submodule.mem_top⟩
    exact le_of_eq (Module.length_eq_zero)
  | succ e ih =>
    have hle : Ideal.span {a ^ (e + 1)} ≤ Ideal.span {a ^ e} :=
      Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow a (Nat.le_succ e))
    have hex := Module.length_eq_add_of_exact (LinearMap.ker (Submodule.factor hle)).subtype
      (Submodule.factor hle) (Submodule.injective_subtype _) (Submodule.factor_surjective hle)
      (LinearMap.exact_subtype_ker_map _)
    let f0 : O →ₗ[O] O ⧸ Ideal.span {a ^ (e + 1)} :=
      (Ideal.span {a ^ (e + 1)}).mkQ ∘ₗ LinearMap.mulLeft O (a ^ e)
    have hf0 : Ideal.span {a} ≤ LinearMap.ker f0 := by
      refine Ideal.span_le.2 (Set.singleton_subset_iff.2 ?_)
      show (Ideal.span {a ^ (e + 1)}).mkQ (a ^ e * a) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, ← pow_succ]
      exact Ideal.subset_span rfl
    let f := (Ideal.span {a}).liftQ f0 hf0
    have hfk : ∀ x, f x ∈ LinearMap.ker (Submodule.factor hle) := by
      intro x
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [LinearMap.mem_ker]
      show (Submodule.Quotient.mk (a ^ e * y) : O ⧸ Ideal.span {a ^ e}) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact Ideal.mem_span_singleton'.2 ⟨y, mul_comm _ _⟩
    let f' : O ⧸ Ideal.span {a} →ₗ[O] LinearMap.ker (Submodule.factor hle) := LinearMap.codRestrict _ f hfk
    have hf'surj : Function.Surjective f' := by
      rintro ⟨z, hz⟩
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
      have hy : y ∈ Ideal.span {a ^ e} := by
        rw [LinearMap.mem_ker] at hz
        exact (Submodule.Quotient.mk_eq_zero _).1 hz
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
      refine ⟨Submodule.Quotient.mk c, Subtype.ext ?_⟩
      show (Submodule.Quotient.mk (a ^ e * c) : O ⧸ Ideal.span {a ^ (e + 1)}) = Submodule.Quotient.mk (c * a ^ e)
      rw [mul_comm]
    have hk := Module.length_le_of_surjective f' hf'surj
    rw [hex, Nat.cast_succ, add_mul, one_mul]
    exact (add_le_add hk ih).trans (le_of_eq (add_comm _ _))

end PLenBound

open PLenBound in
/- English proof (translation)
Introduce `O M _ _ _ ℓ g e Z Bc I s hs hZ hBI hkill`. Establish `hsZ : ∀ x ∈ s, x ∈ Z` using `fun x hx => hZ ▸ Submodule.mem_sup_left (Submodule.subset_span hx)`. Set `v : s → ↥Z ⧸ I.comap Z.subtype` to `fun x => Submodule.Quotient.mk ⟨x.1, hsZ x.1 x.2⟩`. Establish `hspan : Submodule.span O (Set.range v) = ⊤`. Establish `hle' : Submodule.span O (s : Set M) ⊔ Bc ≤ ((Submodule.span O (Set.range v)).comap (I.comap Z.subtype).mkQ).map Z.subtype`.

Rewrite using `[sup_le_iff, Submodule.span_le]`. Prove the components needed by the constructor for the conclusion. Introduce `x hx`. Use `⟨⟨x, hsZ x hx⟩, ?_, rfl⟩` and prove the remaining obligations. Conclude with `Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩`.

Introduce `b hb`. Establish `hbZ : b ∈ Z` using `hZ ▸ Submodule.mem_sup_right hb`. Use `⟨⟨b, hbZ⟩, ?_, rfl⟩` and prove the remaining obligations. Use `show Submodule.Quotient.mk _ ∈ Submodule.span O (Set.range v)`. Rewrite using `[(Submodule.Quotient.mk_eq_zero _).2 (show (⟨b, hbZ⟩ : Z) ∈ I.comap Z.subtype from hBI hb)]`.

Conclude with `Submodule.zero_mem _`. Establish `hle` using `hZ.symm.le.trans hle'`. Rewrite using `[eq_top_iff]`. Introduce and unpack `q -`. Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ q`.

Take `⟨t, ht, htz⟩` from `hle z.2`. Establish `htz' : t = z` using `Subtype.ext htz`. Rewrite using `[← htz']`. Conclude with `ht`. Establish `hv : ∀ i, ((ℓ : O) ^ e) • v i = 0`.

Introduce `i`. Rewrite using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Use `show ((ℓ : O) ^ e) • (i.1 : M) ∈ I`. Use `hkill i.1 (hsZ i.1 i.2)` as an intermediate fact. Rewrite `this` using `[← Nat.cast_smul_eq_nsmul O, Nat.cast_pow]`. Then use the resulting hypothesis.

Establish `h1` using `length_le_of_span v ((ℓ : O) ^ e) hspan hv`. Establish `h2` using `length_quot_pow_le (ℓ : O) e`. Establish `hcard : (Fintype.card s : ℕ∞) ≤ g`. Rewrite using `[Fintype.card_coe]`. Conclude with `hs` after adjusting the coercions.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem quotientLengthBound_holds : Formalism.WachCohomologyFacts.LenBound := by
  intro O M _ _ _ ℓ g e Z Bc I s hs hZ hBI hkill
  classical
  have hsZ : ∀ x ∈ s, x ∈ Z := fun x hx => hZ ▸ Submodule.mem_sup_left (Submodule.subset_span hx)
  let v : s → ↥Z ⧸ I.comap Z.subtype := fun x => Submodule.Quotient.mk ⟨x.1, hsZ x.1 x.2⟩
  have hspan : Submodule.span O (Set.range v) = ⊤ := by
    have hle' : Submodule.span O (s : Set M) ⊔ Bc ≤
        ((Submodule.span O (Set.range v)).comap (I.comap Z.subtype).mkQ).map Z.subtype := by
      rw [sup_le_iff, Submodule.span_le]
      constructor
      · intro x hx
        refine ⟨⟨x, hsZ x hx⟩, ?_, rfl⟩
        exact Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩
      · intro b hb
        have hbZ : b ∈ Z := hZ ▸ Submodule.mem_sup_right hb
        refine ⟨⟨b, hbZ⟩, ?_, rfl⟩
        show Submodule.Quotient.mk _ ∈ Submodule.span O (Set.range v)
        rw [(Submodule.Quotient.mk_eq_zero _).2 (show (⟨b, hbZ⟩ : Z) ∈ I.comap Z.subtype from hBI hb)]
        exact Submodule.zero_mem _
    have hle := hZ.symm.le.trans hle'
    rw [eq_top_iff]
    rintro q -
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨t, ht, htz⟩ := hle z.2
    have htz' : t = z := Subtype.ext htz
    rw [← htz']
    exact ht
  have hv : ∀ i, ((ℓ : O) ^ e) • v i = 0 := by
    intro i
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    show ((ℓ : O) ^ e) • (i.1 : M) ∈ I
    have := hkill i.1 (hsZ i.1 i.2)
    rwa [← Nat.cast_smul_eq_nsmul O, Nat.cast_pow] at this
  have h1 := length_le_of_span v ((ℓ : O) ^ e) hspan hv
  have h2 := length_quot_pow_le (ℓ : O) e
  have hcard : (Fintype.card s : ℕ∞) ≤ g := by
    rw [Fintype.card_coe]
    exact_mod_cast hs
  calc Module.length O (↥Z ⧸ I.comap Z.subtype)
      ≤ (Fintype.card s : ℕ∞) * Module.length O (O ⧸ Ideal.span {(ℓ : O) ^ e}) := h1
    _ ≤ (g : ℕ∞) * ((e : ℕ∞) * Module.length O (O ⧸ Ideal.span {(ℓ : O)})) := mul_le_mul' hcard h2
    _ = (g : ℕ∞) * (e : ℕ∞) * Module.length O (O ⧸ Ideal.span {(ℓ : O)}) := by rw [mul_assoc]

end Formalism.WachCohomologyFacts
