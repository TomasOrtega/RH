import Mathlib

noncomputable section

namespace Formalism.MainNotions.BridgeLevelGenA

open scoped nonZeroDivisors

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

def coprS (g : R) : Submonoid R where
  carrier := {s | IsCoprime s g ∧ s ≠ 0}
  one_mem' := ⟨isCoprime_one_left, one_ne_zero⟩
  mul_mem' := fun {_ _} ha hb => ⟨IsCoprime.mul_left ha.1 hb.1, mul_ne_zero ha.2 hb.2⟩

/- English proof (translation)
Introduce `_ hs` and use `mem_nonZeroDivisors_of_ne_zero hs.2`.
-/
theorem coprS_le (g : R) : coprS g ≤ R⁰ := fun _ hs => mem_nonZeroDivisors_of_ne_zero hs.2

/- English proof (translation)
Assume the negation of the conclusion as `hgP`. Establish `hmax : P.IsMaximal` using `hP.isMaximal hP0`. Establish `htop : P ⊔ Ideal.span {g} = ⊤`. Assume the negation of the conclusion as `h`. Establish `e` using `hmax.eq_of_le h le_sup_left`.

Apply `hgP` to reduce the goal to its premises. Rewrite using `[e]`. Conclude with `Ideal.mem_sup_right (Ideal.mem_span_singleton_self g)`. Take `⟨a, ha, c, hc, hac⟩` from `Submodule.mem_sup.1 (htop ▸ Submodule.mem_top : (1 : R) ∈ P ⊔ Ideal.span {g})`. Take `⟨d, rfl⟩` from `Ideal.mem_span_singleton'.1 hc`.

Take `⟨p, hp, hp0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hP0`. Distinguish the cases in `ha0 : a = 0`. Substitute `ha0` using the available equality. Establish `hco : IsCoprime p g` using `⟨0, d, by simpa using hac⟩`. Conclude with `Set.disjoint_left.1 hd ⟨hco, hp0⟩ hp`.

Establish `hco : IsCoprime a g` using `⟨1, d, by rw [one_mul]; exact hac⟩`. Conclude with `Set.disjoint_left.1 hd ⟨hco, ha0⟩ ha`.
-/
theorem mem_of_disjoint (g : R) {P : Ideal R} (hP : P.IsPrime) (hP0 : P ≠ ⊥)
    (hd : Disjoint (coprS g : Set R) (P : Set R)) : g ∈ P := by
  by_contra hgP
  have hmax : P.IsMaximal := hP.isMaximal hP0
  have htop : P ⊔ Ideal.span {g} = ⊤ := by
    by_contra h
    have e := hmax.eq_of_le h le_sup_left
    apply hgP
    rw [e]
    exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self g)
  obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.1 (htop ▸ Submodule.mem_top : (1 : R) ∈ P ⊔ Ideal.span {g})
  obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.1 hc
  obtain ⟨p, hp, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
  by_cases ha0 : a = 0
  · subst ha0
    have hco : IsCoprime p g := ⟨0, d, by simpa using hac⟩
    exact Set.disjoint_left.1 hd ⟨hco, hp0⟩ hp
  · have hco : IsCoprime a g := ⟨1, d, by rw [one_mul]; exact hac⟩
    exact Set.disjoint_left.1 hd ⟨hco, ha0⟩ ha

/- English proof (translation)
Establish `hI : Ideal.span {g} ≠ 0`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `hg`. Use `((Ideal.finite_factors hI).image (fun v => v.asIdeal)).insert ⊥ |>.subset ?_` and prove the remaining obligations. Introduce and unpack `P ⟨hP, hd⟩`.

Distinguish the cases in `hP0 : P = ⊥`. Conclude with `Or.inl hP0`. Use `Or.inr ⟨⟨P, hP, hP0⟩, ?_, rfl⟩ show P ∣ Ideal.span {g}` and prove the remaining obligations. Rewrite using `[Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]`. Conclude with `mem_of_disjoint g hP hP0 hd`.
-/
theorem primes_finite (g : R) (hg : g ≠ 0) :
    {P : Ideal R | P.IsPrime ∧ Disjoint (coprS g : Set R) (P : Set R)}.Finite := by
  have hI : Ideal.span {g} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hg
  refine ((Ideal.finite_factors hI).image (fun v => v.asIdeal)).insert ⊥ |>.subset ?_
  rintro P ⟨hP, hd⟩
  by_cases hP0 : P = ⊥
  · exact Or.inl hP0
  · refine Or.inr ⟨⟨P, hP, hP0⟩, ?_, rfl⟩
    show P ∣ Ideal.span {g}
    rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]
    exact mem_of_disjoint g hP hP0 hd

variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/- English proof (translation)
Use `set S := coprS g with hSdef`. Set `A` to `Localization.subalgebra.ofField K S (coprS_le g)`. Establish `: IsDedekindDomain A` using `IsLocalization.isDedekindDomain R (coprS_le g) A`. Establish `: IsFractionRing A K` using `IsFractionRing.isFractionRing_of_isDomain_of_isLocalization S A K`. Establish `: IsPrincipalIdealRing A`.

Use `IsPrincipalIdealRing.of_finite_primes ?_` and prove the remaining obligations. Use `((primes_finite g hg).preimage (IsLocalization.orderEmbedding S A).injective.injOn).subset ?_` and prove the remaining obligations. Introduce `J hJ`. Conclude with `(IsLocalization.isPrime_iff_isPrime_disjoint S A J).1 hJ`. Set `M : Submodule A (Fin n → K)` to `Submodule.span A (L : Set (Fin n → K))`.

Establish `: Module.Finite A M`. Take `⟨s, hs⟩` from `hL`. Establish `e : M = Submodule.span A (s : Set (Fin n → K))` using `by show Submodule.span A (L : Set (Fin n → K)) = _`. Rewrite using `[← hs, Submodule.span_span_of_tower]`. Rewrite using `[Module.Finite.iff_fg, e]`.

Conclude with `⟨s, rfl⟩`. Establish `: Module.IsTorsionFree A M`. Use `⟨fun r hr x y hxy => Subtype.ext ?_⟩` and prove the remaining obligations. Establish `hr0 : (r : K) ≠ 0`. Introduce `h`.

Conclude with `hr.ne_zero (Subtype.ext (by simpa using h))`. Establish `h` using `congrArg (fun z : M => (z : Fin n → K)) hxy`. Simplify using `only [Submodule.coe_smul, Subalgebra.smul_def] at h`. Conclude with `smul_right_injective _ hr0 h`. Establish `: Module.Free A M` using `Module.free_of_finite_type_torsion_free'`.

Set `ι` to `Module.Free.ChooseBasisIndex A M`. Set `b : Module.Basis ι A M` to `Module.Free.chooseBasis A M`. Establish `hcard : Fintype.card ι ≤ n`. Establish `hli : LinearIndependent A (fun i => (b i : Fin n → K))` using `b.linearIndependent.map' M.subtype (Submodule.ker_subtype M)`. Establish `hK` using `(LinearIndependent.iff_fractionRing A K).1 hli`.

Simplify using `using hK.fintype_card_le_finrank`. Establish `hden : ∀ v ∈ M, ∃ s ∈ S, algebraMap R K s • v ∈ L`. Introduce `v hv`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, S.one_mem, by simpa using hx⟩`.

Consider the case `zero => exact ⟨1, S.one_mem, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨s, hs, hsx⟩` from `hx`. Take `⟨t, ht, hty⟩` from `hy`. Use `⟨s * t, S.mul_mem hs ht, ?_⟩` and prove the remaining obligations.

Establish `e : algebraMap R K (s * t) • (x + y) = t • (algebraMap R K s • x) + s • (algebraMap R K t • y)`. Rewrite using `[smul_add, ← algebraMap_smul K t (algebraMap R K s • x), ← algebraMap_smul K s (algebraMap R K t • y), smul_smul, smul_smul, ← map_mul, ← map_mul, mul_comm t s]`. Rewrite using `[e]`. Conclude with `L.add_mem (L.smul_mem t hsx) (L.smul_mem s hty)`. Consider the case `smul a x _ hx`.

Take `⟨s, hs, hsx⟩` from `hx`. Take `⟨⟨r, t⟩, hrt⟩` from `IsLocalization.mk'_surjective S a`. Use `⟨t * s, S.mul_mem t.2 hs, ?_⟩` and prove the remaining obligations. Establish `ha : (a : K) * algebraMap R K t = algebraMap R K r`. Rewrite using `[← hrt]`.

Establish `h2 : ((IsLocalization.mk' A r t * algebraMap R A t : A) : K) = ((algebraMap R A r : A) : K)` using `congrArg Subtype.val (IsLocalization.mk'_spec A r t)`. Rewrite `h2` using `[Subalgebra.coe_mul, Subalgebra.coe_algebraMap, Subalgebra.coe_algebraMap]`. Conclude with `h2`. Establish `e : algebraMap R K (t * s) • (a • x) = r • (algebraMap R K s • x)`. Rewrite using `[Subalgebra.smul_def, smul_smul, ← algebraMap_smul K r, smul_smul, map_mul, ← ha]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `L.smul_mem r hsx`. Use `choose sd hsd hsdL using fun i => hden (b i : Fin n → K) (b i).2`.

Use `set s : R := ∏ i, sd i with hs`. Establish `hsS : s ∈ S` using `S.prod_mem fun i _ => hsd i`. Set `ℓ : ι → (Fin n → K)` to `fun i => algebraMap R K s • (b i : Fin n → K)`. Establish `hℓ : ∀ i, ℓ i ∈ L`. Introduce `i`.

Take `⟨c, hc⟩ : sd i ∣ s` from `Finset.dvd_prod_of_mem _ (Finset.mem_univ i)`. Establish `e : ℓ i = c • (algebraMap R K (sd i) • (b i : Fin n → K))` using `by show algebraMap R K s • (b i : Fin n → K) = _`. Rewrite using `[hc, ← algebraMap_smul K c, smul_smul, ← map_mul, mul_comm c (sd i)]`. Rewrite using `[e]`. Conclude with `L.smul_mem c (hsdL i)`.

Establish `hx : ∀ x ∈ L, ∃ (a : ι → R) (w : Fin n → K), w ∈ L ∧ x = ∑ i, a i • ℓ i + g • w`. Introduce `x hxL`. Establish `hxM : x ∈ M` using `Submodule.subset_span hxL`. Use `set c := b.repr ⟨x, hxM⟩ with hc`. Take `⟨t, ht⟩` from `IsLocalization.exist_integer_multiples S Finset.univ (fun i => c i)`.

Use `choose r hr using fun i => ht i (Finset.mem_univ i)`. Establish `hsum : x = ∑ i, (c i : K) • (b i : Fin n → K)`. Use `congrArg (fun z : M => (z : Fin n → K)) (b.sum_repr ⟨x, hxM⟩)` as an intermediate fact. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, Subalgebra.smul_def] at this`. Rewrite `this` using `[← hc]`.

Conclude with `this.symm`. Establish `hri : ∀ i, algebraMap R K (r i) = algebraMap R K (t : R) * (c i : K)`. Introduce `i`. Establish `h2 : ((algebraMap R A (r i) : A) : K) = (((t : R) • c i : A) : K)` using `congrArg Subtype.val (hr i)`. Rewrite `h2` using `[Subalgebra.coe_algebraMap, Algebra.smul_def, Subalgebra.coe_mul, Subalgebra.coe_algebraMap]`.

Conclude with `h2`. Use `set u : R := (t : R) * s with hu_def`. Establish `hux : algebraMap R K u • x = ∑ i, r i • ℓ i`. Rewrite using `[hsum, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Use `show _ = r i • (algebraMap R K s • (b i : Fin n → K))`. Rewrite using `[← algebraMap_smul K (r i), smul_smul, smul_smul, hri, hu_def, map_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hu : u ∈ S` using `S.mul_mem t.2 hsS`.

Take `⟨α, β, hαβ⟩` from `hu.1`. Use `⟨fun i => α * r i, β • x, L.smul_mem β hxL, ?_⟩` and prove the remaining obligations. Establish `h1 : algebraMap R K α * algebraMap R K u + algebraMap R K g * algebraMap R K β = 1`. Rewrite using `[← map_mul, ← map_mul, ← map_add, mul_comm g β, hαβ, map_one]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[h1, one_smul]`. Use `_ = α • (algebraMap R K u • x) + g • (β • x) := by`. Rewrite using `[add_smul, ← smul_smul, ← smul_smul, algebraMap_smul K α, algebraMap_smul K g, algebraMap_smul K β]`. Use `_ = _ := by`. Rewrite using `[hux, Finset.smul_sum]`.

Simplify using `only [smul_smul]`. Set `e` to `Fintype.equivFin ι`. Use `⟨Fintype.card ι, fun j => ℓ (e.symm j), hcard, fun j => hℓ _, fun x hxL => ?_⟩` and prove the remaining obligations. Take `⟨a, w, hw, hxw⟩` from `hx x hxL`. Use `⟨fun j => a (e.symm j), w, hw, ?_⟩` and prove the remaining obligations.

Rewrite using `[hxw]`. Use `congr 1`. Conclude with `(Equiv.sum_comp e.symm (fun i => a i • ℓ i)).symm`.
-/
theorem gen_mod (g : R) (hg : g ≠ 0) {n : ℕ} (L : Submodule R (Fin n → K)) (hL : L.FG) :
    ∃ (m : ℕ) (ℓ : Fin m → (Fin n → K)), m ≤ n ∧ (∀ j, ℓ j ∈ L) ∧
      ∀ x ∈ L, ∃ (a : Fin m → R) (w : Fin n → K), w ∈ L ∧ x = ∑ j, a j • ℓ j + g • w := by
  classical
  set S := coprS g with hSdef
  let A := Localization.subalgebra.ofField K S (coprS_le g)
  have : IsDedekindDomain A := IsLocalization.isDedekindDomain R (coprS_le g) A
  have : IsFractionRing A K := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization S A K
  have : IsPrincipalIdealRing A := by
    refine IsPrincipalIdealRing.of_finite_primes ?_
    refine ((primes_finite g hg).preimage (IsLocalization.orderEmbedding S A).injective.injOn).subset ?_
    intro J hJ
    exact (IsLocalization.isPrime_iff_isPrime_disjoint S A J).1 hJ
  let M : Submodule A (Fin n → K) := Submodule.span A (L : Set (Fin n → K))
  have : Module.Finite A M := by
    obtain ⟨s, hs⟩ := hL
    have e : M = Submodule.span A (s : Set (Fin n → K)) := by
      show Submodule.span A (L : Set (Fin n → K)) = _
      rw [← hs, Submodule.span_span_of_tower]
    rw [Module.Finite.iff_fg, e]
    exact ⟨s, rfl⟩
  have : Module.IsTorsionFree A M := by
    refine ⟨fun r hr x y hxy => Subtype.ext ?_⟩
    have hr0 : (r : K) ≠ 0 := by
      intro h
      exact hr.ne_zero (Subtype.ext (by simpa using h))
    have h := congrArg (fun z : M => (z : Fin n → K)) hxy
    simp only [Submodule.coe_smul, Subalgebra.smul_def] at h
    exact smul_right_injective _ hr0 h
  have : Module.Free A M := Module.free_of_finite_type_torsion_free'
  let ι := Module.Free.ChooseBasisIndex A M
  let b : Module.Basis ι A M := Module.Free.chooseBasis A M

  have hcard : Fintype.card ι ≤ n := by
    have hli : LinearIndependent A (fun i => (b i : Fin n → K)) :=
      b.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
    have hK := (LinearIndependent.iff_fractionRing A K).1 hli
    simpa using hK.fintype_card_le_finrank

  have hden : ∀ v ∈ M, ∃ s ∈ S, algebraMap R K s • v ∈ L := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx => exact ⟨1, S.one_mem, by simpa using hx⟩
    | zero => exact ⟨1, S.one_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨s, hs, hsx⟩ := hx
      obtain ⟨t, ht, hty⟩ := hy
      refine ⟨s * t, S.mul_mem hs ht, ?_⟩
      have e : algebraMap R K (s * t) • (x + y) = t • (algebraMap R K s • x) + s • (algebraMap R K t • y) := by
        rw [smul_add, ← algebraMap_smul K t (algebraMap R K s • x), ← algebraMap_smul K s (algebraMap R K t • y),
          smul_smul, smul_smul, ← map_mul, ← map_mul, mul_comm t s]
      rw [e]
      exact L.add_mem (L.smul_mem t hsx) (L.smul_mem s hty)
    | smul a x _ hx =>
      obtain ⟨s, hs, hsx⟩ := hx
      obtain ⟨⟨r, t⟩, hrt⟩ := IsLocalization.mk'_surjective S a
      refine ⟨t * s, S.mul_mem t.2 hs, ?_⟩
      have ha : (a : K) * algebraMap R K t = algebraMap R K r := by
        rw [← hrt]
        have h2 : ((IsLocalization.mk' A r t * algebraMap R A t : A) : K) = ((algebraMap R A r : A) : K) :=
          congrArg Subtype.val (IsLocalization.mk'_spec A r t)
        rw [Subalgebra.coe_mul, Subalgebra.coe_algebraMap, Subalgebra.coe_algebraMap] at h2
        exact h2
      have e : algebraMap R K (t * s) • (a • x) = r • (algebraMap R K s • x) := by
        rw [Subalgebra.smul_def, smul_smul, ← algebraMap_smul K r, smul_smul, map_mul, ← ha]
        congr 1; ring
      rw [e]
      exact L.smul_mem r hsx
  choose sd hsd hsdL using fun i => hden (b i : Fin n → K) (b i).2
  set s : R := ∏ i, sd i with hs
  have hsS : s ∈ S := S.prod_mem fun i _ => hsd i
  let ℓ : ι → (Fin n → K) := fun i => algebraMap R K s • (b i : Fin n → K)
  have hℓ : ∀ i, ℓ i ∈ L := by
    intro i
    obtain ⟨c, hc⟩ : sd i ∣ s := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    have e : ℓ i = c • (algebraMap R K (sd i) • (b i : Fin n → K)) := by
      show algebraMap R K s • (b i : Fin n → K) = _
      rw [hc, ← algebraMap_smul K c, smul_smul, ← map_mul, mul_comm c (sd i)]
    rw [e]
    exact L.smul_mem c (hsdL i)

  have hx : ∀ x ∈ L, ∃ (a : ι → R) (w : Fin n → K), w ∈ L ∧ x = ∑ i, a i • ℓ i + g • w := by
    intro x hxL
    have hxM : x ∈ M := Submodule.subset_span hxL
    set c := b.repr ⟨x, hxM⟩ with hc
    obtain ⟨t, ht⟩ := IsLocalization.exist_integer_multiples S Finset.univ (fun i => c i)
    choose r hr using fun i => ht i (Finset.mem_univ i)
    have hsum : x = ∑ i, (c i : K) • (b i : Fin n → K) := by
      have := congrArg (fun z : M => (z : Fin n → K)) (b.sum_repr ⟨x, hxM⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul, Subalgebra.smul_def] at this
      rw [← hc] at this
      exact this.symm
    have hri : ∀ i, algebraMap R K (r i) = algebraMap R K (t : R) * (c i : K) := by
      intro i
      have h2 : ((algebraMap R A (r i) : A) : K) = (((t : R) • c i : A) : K) := congrArg Subtype.val (hr i)
      rw [Subalgebra.coe_algebraMap, Algebra.smul_def, Subalgebra.coe_mul, Subalgebra.coe_algebraMap] at h2
      exact h2
    set u : R := (t : R) * s with hu_def
    have hux : algebraMap R K u • x = ∑ i, r i • ℓ i := by
      rw [hsum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      show _ = r i • (algebraMap R K s • (b i : Fin n → K))
      rw [← algebraMap_smul K (r i), smul_smul, smul_smul, hri, hu_def, map_mul]
      congr 1; ring
    have hu : u ∈ S := S.mul_mem t.2 hsS
    obtain ⟨α, β, hαβ⟩ := hu.1
    refine ⟨fun i => α * r i, β • x, L.smul_mem β hxL, ?_⟩
    have h1 : algebraMap R K α * algebraMap R K u + algebraMap R K g * algebraMap R K β = 1 := by
      rw [← map_mul, ← map_mul, ← map_add, mul_comm g β, hαβ, map_one]
    calc x = (algebraMap R K α * algebraMap R K u + algebraMap R K g * algebraMap R K β) • x := by
          rw [h1, one_smul]
      _ = α • (algebraMap R K u • x) + g • (β • x) := by
          rw [add_smul, ← smul_smul, ← smul_smul, algebraMap_smul K α, algebraMap_smul K g, algebraMap_smul K β]
      _ = _ := by
          rw [hux, Finset.smul_sum]
          simp only [smul_smul]

  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun j => ℓ (e.symm j), hcard, fun j => hℓ _, fun x hxL => ?_⟩
  obtain ⟨a, w, hw, hxw⟩ := hx x hxL
  refine ⟨fun j => a (e.symm j), w, hw, ?_⟩
  rw [hxw]
  congr 1
  exact (Equiv.sum_comp e.symm (fun i => a i • ℓ i)).symm

end Formalism.MainNotions.BridgeLevelGenA

end
