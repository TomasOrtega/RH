import Mathlib

namespace GlobalTheory.CoprimeBasisExistence

open NumberField nonZeroDivisors

def coprimeSet (A : Type*) [CommRing A] (m : ℕ) : Submonoid A where
  carrier := {x | ∃ k : ℕ, 0 < k ∧ k.Coprime m ∧ (k : A) = x}
  one_mem' := ⟨1, one_pos, by simp, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, ha', rfl⟩ ⟨b, hb, hb', rfl⟩
    exact ⟨a * b, mul_pos ha hb, Nat.Coprime.mul_left ha' hb', by simp⟩

/- English proof (translation)
Introduce and unpack `_ ⟨k, hk, _, rfl⟩`. Conclude with `mem_nonZeroDivisors_of_ne_zero (Nat.cast_ne_zero.2 hk.ne')`.
-/
theorem coprimeSet_le (A : Type*) [CommRing A] [IsDomain A] [CharZero A] (m : ℕ) :
    coprimeSet A m ≤ A⁰ := by
  rintro _ ⟨k, hk, _, rfl⟩
  exact mem_nonZeroDivisors_of_ne_zero (Nat.cast_ne_zero.2 hk.ne')

/- English proof (translation)
Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `hn hnP`. Distinguish the cases in `hc : n.Coprime m`.

Conclude with `absurd hnP (fun h => hP.ne_top (Ideal.eq_top_of_isUnit_mem _ h (hu n hn hc)))`. Establish `hg0 : 0 < Nat.gcd n m` using `Nat.gcd_pos_of_pos_left m hn`. Establish `hg1 : 1 < Nat.gcd n m`. Rewrite `hc` using `[Nat.Coprime]`. Use linear arithmetic over natural numbers and integers.

Establish `hn' : n = Nat.gcd n m * (n / Nat.gcd n m)` using `(Nat.mul_div_cancel' (Nat.gcd_dvd_left n m)).symm`. Establish `hmul : ((Nat.gcd n m : R) * ((n / Nat.gcd n m : ℕ) : R)) ∈ P`. Rewrite using `[← Nat.cast_mul, ← hn']`. Conclude with `hnP`. Break down `hP.mem_or_mem hmul with h1 | h1` into its components or cases.

Take `⟨c, hc'⟩` from `Nat.gcd_dvd_right n m`. Establish `e : (m : R) = (Nat.gcd n m : R) * (c : R)`. Rewrite using `[← Nat.cast_mul, ← hc']`. Rewrite using `[e]`. Conclude with `P.mul_mem_right _ h1`.

Establish `hlt : n / Nat.gcd n m < n` using `Nat.div_lt_self hn hg1`. Establish `hpos : 0 < n / Nat.gcd n m` using `Nat.div_pos (Nat.gcd_le_left m hn) hg0`. Conclude with `ih (n / Nat.gcd n m) hlt hpos h1`.
-/
theorem mem_of_natCast_mem {R : Type*} [CommRing R] (m : ℕ)
    (hu : ∀ k : ℕ, 0 < k → k.Coprime m → IsUnit (k : R)) (P : Ideal R) (hP : P.IsPrime) :
    ∀ n : ℕ, 0 < n → (n : R) ∈ P → (m : R) ∈ P := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hnP
    by_cases hc : n.Coprime m
    · exact absurd hnP (fun h => hP.ne_top (Ideal.eq_top_of_isUnit_mem _ h (hu n hn hc)))
    · have hg0 : 0 < Nat.gcd n m := Nat.gcd_pos_of_pos_left m hn
      have hg1 : 1 < Nat.gcd n m := by
        rw [Nat.Coprime] at hc
        omega
      have hn' : n = Nat.gcd n m * (n / Nat.gcd n m) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left n m)).symm
      have hmul : ((Nat.gcd n m : R) * ((n / Nat.gcd n m : ℕ) : R)) ∈ P := by
        rw [← Nat.cast_mul, ← hn']
        exact hnP
      rcases hP.mem_or_mem hmul with h1 | h1
      · obtain ⟨c, hc'⟩ := Nat.gcd_dvd_right n m
        have e : (m : R) = (Nat.gcd n m : R) * (c : R) := by
          rw [← Nat.cast_mul, ← hc']
        rw [e]
        exact P.mul_mem_right _ h1
      · have hlt : n / Nat.gcd n m < n := Nat.div_lt_self hn hg1
        have hpos : 0 < n / Nat.gcd n m := Nat.div_pos (Nat.gcd_le_left m hn) hg0
        exact ih (n / Nat.gcd n m) hlt hpos h1

/- English proof (translation)
Establish `hS` using `coprimeSet_le (𝓞 K) m`. Establish `: IsDedekindDomain R` using `IsLocalization.isDedekindDomain (𝓞 K) hS R`. Establish `hinj` using `IsLocalization.injective R hS`. Establish `hm0 : (m : R) ≠ 0`. Rewrite using `[← map_natCast (algebraMap (𝓞 K) R), map_ne_zero_iff _ hinj]`.

Conclude with `Nat.cast_ne_zero.mpr hm.ne'`. Establish `hu : ∀ k : ℕ, 0 < k → k.Coprime m → IsUnit (k : R)`. Introduce `k hk hc`. Use `IsLocalization.map_units R (⟨(k : 𝓞 K), k, hk, hc, rfl⟩ : coprimeSet (𝓞 K) m)` as an intermediate fact. Simplify using `using this`.

Use `IsPrincipalIdealRing.of_finite_primes ?_` and prove the remaining obligations. Establish `hI : Ideal.span {(m : R)} ≠ 0` using `by simpa using hm0`. Use `(((Ideal.finite_factors hI).image (fun v => v.asIdeal)).insert ⊥).subset ?_` and prove the remaining obligations. Introduce `P hP`. Establish `hP : P.IsPrime` using `hP`.

Distinguish the cases in `h0 : P = ⊥`. Conclude with `Or.inl h0`. Use `Or.inr ⟨⟨P, hP, h0⟩, ?_, rfl⟩` and prove the remaining obligations. Establish `h1 : P.under (𝓞 K) ≠ ⊥` using `(IsLocalization.bot_lt_under_prime _ R hS P h0).ne'`. Establish `h2` using `Ideal.absNorm_mem (P.under (𝓞 K))`.

Establish `h3 : Ideal.absNorm (P.under (𝓞 K)) ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]` and apply the resulting hypothesis. Establish `h4 : ((Ideal.absNorm (P.under (𝓞 K)) : ℕ) : R) ∈ P`. Rewrite using `[← map_natCast (algebraMap (𝓞 K) R)]`. Conclude with `h2`.

Use `mem_of_natCast_mem m hu P hP _ (Nat.pos_of_ne_zero h3) h4` as an intermediate fact. Simplify `this` using `[Ideal.dvd_iff_le]`.
-/
theorem isPrincipalIdealRing_loc {K : Type} [Field K] [NumberField K] (m : ℕ) (hm : 0 < m)
    (R : Type) [CommRing R] [IsDomain R] [Algebra (𝓞 K) R]
    [IsLocalization (coprimeSet (𝓞 K) m) R] : IsPrincipalIdealRing R := by
  classical
  have hS := coprimeSet_le (𝓞 K) m
  have : IsDedekindDomain R := IsLocalization.isDedekindDomain (𝓞 K) hS R
  have hinj := IsLocalization.injective R hS
  have hm0 : (m : R) ≠ 0 := by
    rw [← map_natCast (algebraMap (𝓞 K) R), map_ne_zero_iff _ hinj]
    exact Nat.cast_ne_zero.mpr hm.ne'
  have hu : ∀ k : ℕ, 0 < k → k.Coprime m → IsUnit (k : R) := by
    intro k hk hc
    have := IsLocalization.map_units R (⟨(k : 𝓞 K), k, hk, hc, rfl⟩ : coprimeSet (𝓞 K) m)
    simpa using this
  refine IsPrincipalIdealRing.of_finite_primes ?_
  have hI : Ideal.span {(m : R)} ≠ 0 := by simpa using hm0
  refine (((Ideal.finite_factors hI).image (fun v => v.asIdeal)).insert ⊥).subset ?_
  intro P hP
  have hP : P.IsPrime := hP
  by_cases h0 : P = ⊥
  · exact Or.inl h0
  · refine Or.inr ⟨⟨P, hP, h0⟩, ?_, rfl⟩
    have h1 : P.under (𝓞 K) ≠ ⊥ := (IsLocalization.bot_lt_under_prime _ R hS P h0).ne'
    have h2 := Ideal.absNorm_mem (P.under (𝓞 K))
    have h3 : Ideal.absNorm (P.under (𝓞 K)) ≠ 0 := by
      rwa [Ne, Ideal.absNorm_eq_zero_iff]
    have h4 : ((Ideal.absNorm (P.under (𝓞 K)) : ℕ) : R) ∈ P := by
      rw [← map_natCast (algebraMap (𝓞 K) R)]
      exact h2
    have := mem_of_natCast_mem m hu P hP _ (Nat.pos_of_ne_zero h3) h4
    simpa [Ideal.dvd_iff_le] using this

/- English proof (translation)
Establish `hS` using `coprimeSet_le (𝓞 K) m`. Use `set R := Localization.subalgebra K (coprimeSet (𝓞 K) m) hS with hR`. Establish `: IsPrincipalIdealRing R` using `isPrincipalIdealRing_loc (K := K) m hm R`. Establish `hst : IsScalarTower (𝓞 K) R V` using `⟨fun a r v => by`. Express the relevant statement in the definitionally equal form `((a • (r : K)) • v) = a • ((r : K) • v)`.

Rewrite using `[smul_assoc]⟩`. Establish `key : ∀ (M : Submodule (𝓞 K) V) (v : V), v ∈ Submodule.span R (M : Set V) → ∃ k : ℕ, 0 < k ∧ k.Coprime m ∧ k • v ∈ M`. Introduce `M v hv`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, one_pos, by simp, by simpa using hx⟩`.

Consider the case `zero => exact ⟨1, one_pos, by simp, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨a, ha, ha', hx⟩` from `hx`. Take `⟨b, hb, hb', hy⟩` from `hy`. Use `⟨a * b, mul_pos ha hb, Nat.Coprime.mul_left ha' hb', ?_⟩` and prove the remaining obligations.

Rewrite using `[smul_add]`. Use `M.add_mem ?_ ?_` and prove the remaining obligations. Rewrite using `[mul_comm, mul_smul]`. Conclude with `M.nsmul_mem hx b`. Rewrite using `[mul_smul]`.

Conclude with `M.nsmul_mem hy a`. Consider the case `smul r x _ hx`. Take `⟨a, ha, ha', hx⟩` from `hx`. Take `⟨⟨c, _, b, hb, hb', rfl⟩, hc⟩` from `IsLocalization.surj (coprimeSet (𝓞 K) m) r`. Use `⟨a * b, mul_pos ha hb, Nat.Coprime.mul_left ha' hb', ?_⟩` and prove the remaining obligations.

Establish `h1 : (a * b) • r • x = c • (a • x)`. Simplify using `only [map_natCast] at hc`. Rewrite using `[← algebraMap_smul R c, ← hc, mul_smul, smul_comm a, smul_comm a, mul_smul, Nat.cast_smul_eq_nsmul, smul_comm b r]`. Rewrite using `[h1]`. Conclude with `M.smul_mem c hx`.

Set `N : Submodule R V` to `Submodule.span R (L : Set V)`. Establish `hN : N.FG`. Take `⟨s, hs⟩` from `hL`. Use `⟨s, ?_⟩` and prove the remaining obligations. Simplify using `only [N, ← hs]`.

Conclude with `(Submodule.span_span_of_tower (𝓞 K) R (s : Set V)).symm`. Establish `: Module.Finite R N` using `Module.Finite.iff_fg.mpr hN`. Establish `: Module.IsTorsionFree R V`. Use `Module.IsTorsionFree.of_smul_eq_zero fun r v h => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(r : K) • v = 0 at h`.

Break down `smul_eq_zero.mp h with h | h` into its components or cases. Conclude with `Or.inl (Subtype.ext h)`. Conclude with `Or.inr h`. Take `⟨r, e⟩` from `Module.basisOfFiniteTypeTorsionFree' (R := R) (M := N)`. Use `choose k hk hk' hkL using fun i => key L (e i : V) (e i).2`.

Use `⟨r, fun i => k i • (e i : V), ?_, hkL, ?_⟩` and prove the remaining obligations. Establish `h1 : LinearIndependent R (fun i => (e i : V))` using `e.linearIndependent.map' N.subtype N.ker_subtype`. Establish `h2 : LinearIndependent K (fun i => (e i : V))` using `(LinearIndependent.iff_fractionRing R K).mp h1`. Establish `h3` using `h2.units_smul (fun i => Units.mk0 (k i : K) (Nat.cast_ne_zero.mpr (hk i).ne'))`. Use `h3 using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `i`. Simplify using `[Units.smul_def, Nat.cast_smul_eq_nsmul]`. Introduce `w hw`. Establish `hwN : w ∈ N` using `Submodule.subset_span hw`. Establish `h1 : w ∈ Submodule.span R ((Submodule.span (𝓞 K) (Set.range fun i => k i • (e i : V)) : Submodule (𝓞 K) V) : Set V)`.

Establish `h2 : w = ∑ i, e.repr ⟨w, hwN⟩ i • (e i : V)`. Use `congrArg Subtype.val (e.sum_repr ⟨w, hwN⟩)` as an intermediate fact. Rewrite `this` using `[Submodule.coe_sum]`. Conclude with `this.symm`. Rewrite using `[h2]`.

Use `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Establish `hu : IsUnit (k i : R)`. Use `IsLocalization.map_units R (⟨(k i : 𝓞 K), k i, hk i, hk' i, rfl⟩ : coprimeSet (𝓞 K) m)` as an intermediate fact. Simplify using `using this`. Take `⟨u, hu⟩` from `hu`.

Establish `h3 : (e i : V) = ((u⁻¹ : Rˣ) : R) • (k i • (e i : V))`. Rewrite using `[← Nat.cast_smul_eq_nsmul R, ← hu, ← mul_smul, Units.inv_mul, one_smul]`. Rewrite using `[h3]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span (Submodule.subset_span ⟨i, rfl⟩))`. Take `⟨a, -, ha, h⟩` from `key _ w h1`.

Conclude with `⟨a, ha, h⟩`.
-/
theorem exists_basis_coprime {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (m : ℕ) (hm : 0 < m)
    (L : Submodule (𝓞 K) V) (hL : L.FG) :
    ∃ (r : ℕ) (b : Fin r → V), LinearIndependent K b ∧ (∀ i, b i ∈ L) ∧
      ∀ w ∈ L, ∃ k : ℕ, Nat.Coprime k m ∧ k • w ∈ Submodule.span (𝓞 K) (Set.range b) := by
  classical
  have hS := coprimeSet_le (𝓞 K) m
  set R := Localization.subalgebra K (coprimeSet (𝓞 K) m) hS with hR
  have : IsPrincipalIdealRing R := isPrincipalIdealRing_loc (K := K) m hm R
  have hst : IsScalarTower (𝓞 K) R V := ⟨fun a r v => by
    change ((a • (r : K)) • v) = a • ((r : K) • v)
    rw [smul_assoc]⟩

  have key : ∀ (M : Submodule (𝓞 K) V) (v : V), v ∈ Submodule.span R (M : Set V) →
      ∃ k : ℕ, 0 < k ∧ k.Coprime m ∧ k • v ∈ M := by
    intro M v hv
    induction hv using Submodule.span_induction with
    | mem x hx => exact ⟨1, one_pos, by simp, by simpa using hx⟩
    | zero => exact ⟨1, one_pos, by simp, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, ha', hx⟩ := hx
      obtain ⟨b, hb, hb', hy⟩ := hy
      refine ⟨a * b, mul_pos ha hb, Nat.Coprime.mul_left ha' hb', ?_⟩
      rw [smul_add]
      refine M.add_mem ?_ ?_
      · rw [mul_comm, mul_smul]; exact M.nsmul_mem hx b
      · rw [mul_smul]; exact M.nsmul_mem hy a
    | smul r x _ hx =>
      obtain ⟨a, ha, ha', hx⟩ := hx
      obtain ⟨⟨c, _, b, hb, hb', rfl⟩, hc⟩ := IsLocalization.surj (coprimeSet (𝓞 K) m) r
      refine ⟨a * b, mul_pos ha hb, Nat.Coprime.mul_left ha' hb', ?_⟩
      have h1 : (a * b) • r • x = c • (a • x) := by
        simp only [map_natCast] at hc
        rw [← algebraMap_smul R c, ← hc, mul_smul, smul_comm a, smul_comm a, mul_smul,
          Nat.cast_smul_eq_nsmul, smul_comm b r]
      rw [h1]
      exact M.smul_mem c hx
  let N : Submodule R V := Submodule.span R (L : Set V)
  have hN : N.FG := by
    obtain ⟨s, hs⟩ := hL
    refine ⟨s, ?_⟩
    simp only [N, ← hs]
    exact (Submodule.span_span_of_tower (𝓞 K) R (s : Set V)).symm
  have : Module.Finite R N := Module.Finite.iff_fg.mpr hN
  have : Module.IsTorsionFree R V := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r v h => ?_
    change (r : K) • v = 0 at h
    rcases smul_eq_zero.mp h with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr h
  obtain ⟨r, e⟩ := Module.basisOfFiniteTypeTorsionFree' (R := R) (M := N)
  choose k hk hk' hkL using fun i => key L (e i : V) (e i).2
  refine ⟨r, fun i => k i • (e i : V), ?_, hkL, ?_⟩
  · have h1 : LinearIndependent R (fun i => (e i : V)) :=
      e.linearIndependent.map' N.subtype N.ker_subtype
    have h2 : LinearIndependent K (fun i => (e i : V)) :=
      (LinearIndependent.iff_fractionRing R K).mp h1
    have h3 := h2.units_smul (fun i => Units.mk0 (k i : K) (Nat.cast_ne_zero.mpr (hk i).ne'))
    convert h3 using 1
    funext i
    simp [Units.smul_def, Nat.cast_smul_eq_nsmul]
  · intro w hw
    have hwN : w ∈ N := Submodule.subset_span hw
    have h1 : w ∈ Submodule.span R
        ((Submodule.span (𝓞 K) (Set.range fun i => k i • (e i : V)) : Submodule (𝓞 K) V) : Set V) := by
      have h2 : w = ∑ i, e.repr ⟨w, hwN⟩ i • (e i : V) := by
        have := congrArg Subtype.val (e.sum_repr ⟨w, hwN⟩)
        rw [Submodule.coe_sum] at this
        exact this.symm
      rw [h2]
      refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
      have hu : IsUnit (k i : R) := by
        have := IsLocalization.map_units R
          (⟨(k i : 𝓞 K), k i, hk i, hk' i, rfl⟩ : coprimeSet (𝓞 K) m)
        simpa using this
      obtain ⟨u, hu⟩ := hu
      have h3 : (e i : V) = ((u⁻¹ : Rˣ) : R) • (k i • (e i : V)) := by
        rw [← Nat.cast_smul_eq_nsmul R, ← hu, ← mul_smul, Units.inv_mul, one_smul]
      rw [h3]
      exact Submodule.smul_mem _ _
        (Submodule.subset_span (Submodule.subset_span ⟨i, rfl⟩))
    obtain ⟨a, -, ha, h⟩ := key _ w h1
    exact ⟨a, ha, h⟩

end GlobalTheory.CoprimeBasisExistence
