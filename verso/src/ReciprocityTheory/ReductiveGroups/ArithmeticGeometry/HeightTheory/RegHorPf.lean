import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.RegAVpt

namespace ReciprocityTheory.ChartRestriction.G.T0

open IsLocalRing

/- English proof (translation)
Introduce `hu`. Establish `htop : (⊤ : Submodule O V) ≤ maximalIdeal O • ⊤`. Introduce `v _`. Take `⟨w, hw⟩ : ∃ w : V, algebraMap O V π * w = v` from `⟨hu.unit⁻¹ * v, by rw [← mul_assoc, IsUnit.mul_val_inv, one_mul]⟩`. Rewrite using `[← hw, ← Algebra.smul_def]`.

Conclude with `Submodule.smul_mem_smul hπ Submodule.mem_top`. Establish `hbot` using `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal O) ⊤ Module.Finite.fg_top htop (IsLocalRing.maximalIdeal_le_jacobson _)`. Establish `h1 : (1 : V) ∈ (⊥ : Submodule O V)` using `hbot ▸ Submodule.mem_top`. Conclude with `one_ne_zero ((Submodule.mem_bot O).mp h1)`.
-/
theorem not_isUnit_algebraMap_of_finite {O V : Type} [CommRing O] [IsLocalRing O] [CommRing V]
    [Nontrivial V] [Algebra O V] [Module.Finite O V] (π : O) (hπ : π ∈ maximalIdeal O) :
    ¬ IsUnit (algebraMap O V π) := by
  intro hu
  have htop : (⊤ : Submodule O V) ≤ maximalIdeal O • ⊤ := by
    intro v _
    obtain ⟨w, hw⟩ : ∃ w : V, algebraMap O V π * w = v :=
      ⟨hu.unit⁻¹ * v, by rw [← mul_assoc, IsUnit.mul_val_inv, one_mul]⟩
    rw [← hw, ← Algebra.smul_def]
    exact Submodule.smul_mem_smul hπ Submodule.mem_top
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal O) ⊤
    Module.Finite.fg_top htop (IsLocalRing.maximalIdeal_le_jacobson _)
  have h1 : (1 : V) ∈ (⊥ : Submodule O V) := hbot ▸ Submodule.mem_top
  exact one_ne_zero ((Submodule.mem_bot O).mp h1)

/- English proof (translation)
Assume the negation of the conclusion as `hno`. Take `⟨a, s, haP, hsP, hfas⟩` from `hdvr hno`. Establish `hinj : Function.Injective (algebraMap A (FractionRing A))` using `IsFractionRing.injective A (FractionRing A)`. Establish `hf0 : f ≠ 0`. Introduce and unpack `rfl`.

Conclude with `hno ⟨0, 1, (Ideal.ne_top_iff_one P).mp (Ideal.IsPrime.ne_top ‹_›), by simp⟩`. Establish `hs0 : algebraMap A (FractionRing A) s ≠ 0`. Rewrite using `[map_ne_zero_iff _ hinj]`. Introduce and unpack `rfl`. Conclude with `hsP P.zero_mem`.

Establish `ha0 : a ≠ 0`. Introduce and unpack `rfl`. Rewrite `hfas` using `[map_zero, mul_eq_zero]`. Break down `hfas with h | h` into its components or cases. Conclude with `hf0 (inv_eq_zero.mp h)`.

Conclude with `hs0 h`. Establish `hfa : f * algebraMap A (FractionRing A) a = algebraMap A (FractionRing A) s`. Rewrite using `[← hfas, ← mul_assoc, mul_inv_cancel₀ hf0, one_mul]`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Establish `hmax : maximalIdeal O = Ideal.span {ϖ}` using `hϖ.maximalIdeal_eq`.

Establish `hϖm : ϖ ∈ maximalIdeal O` using `(mem_maximalIdeal _).mpr hϖ.not_isUnit`. Establish `hmapw : Ideal.map (algebraMap O A) (maximalIdeal O) = Ideal.span {algebraMap O A ϖ}`. Rewrite using `[hmax, Ideal.map_span, Set.image_singleton]`. Establish `hwP : algebraMap O A ϖ ∉ P` using `fun h => hh (by rw [hmapw, Ideal.span_le, Set.singleton_subset_iff]; exact h)`. Establish `hws : algebraMap O A ϖ * s ∉ P` using `fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hwP hsP`.

Establish `hws0 : algebraMap A (FractionRing A) (algebraMap O A ϖ * s) ≠ 0`. Rewrite using `[map_ne_zero_iff _ hinj]`. Introduce and unpack `h`. Conclude with `hws (h ▸ P.zero_mem)`. Establish `hOA : Function.Injective (algebraMap O A)`.

Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Assume the negation of the conclusion as `hx0`. Take `⟨n, u, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ`. Rewrite `hx` using `[map_mul, map_pow, mul_eq_zero]`.

Break down `hx with h | h` into its components or cases. Conclude with `(u.isUnit.map (algebraMap O A)).ne_zero h`. Conclude with `hwP (pow_eq_zero_iff'.mp h |>.1 ▸ P.zero_mem)`. Use `set y : FractionRing A := algebraMap A (FractionRing A) a / algebraMap A (FractionRing A) (algebraMap O A ϖ * s) with hy`. Set `B : Subalgebra A (FractionRing A)` to `Algebra.adjoin A {y}`.

Establish `hyB : y ∈ B` using `Algebra.subset_adjoin rfl`. Set `S : Subalgebra A (FractionRing A)` to `{ carrier := {x | ∃ a' p t : A, p ∈ P ∧ t ∉ P ∧ x * algebraMap A (FractionRing A) t = algebraMap A (FractionRing A) (a' * t + p)} mul_mem' := by`. Introduce and unpack `x1 x2 ⟨a1, p1, t1, hp1, ht1, h1⟩ ⟨a2, p2, t2, hp2, ht2, h2⟩`. Use `⟨a1 * a2, a1 * t1 * p2 + a2 * t2 * p1 + p1 * p2, t1 * t2, P.add_mem (P.add_mem (P.mul_mem_left _ hp2) (P.mul_mem_left _ hp1)) (P.mul_mem_left _ hp2), fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim ht1 ht2, ?_⟩` and prove the remaining obligations. Establish `: x1 * x2 * algebraMap A (FractionRing A) (t1 * t2) = (x1 * algebraMap A (FractionRing A) t1) * (x2 * algebraMap A (FractionRing A) t2)`.

Rewrite using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, h1, h2, ← map_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Use the proof step `add_mem' := by`. Introduce and unpack `x1 x2 ⟨a1, p1, t1, hp1, ht1, h1⟩ ⟨a2, p2, t2, hp2, ht2, h2⟩`. Use `⟨a1 + a2, p1 * t2 + p2 * t1, t1 * t2, P.add_mem (P.mul_mem_right _ hp1) (P.mul_mem_right _ hp2), fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim ht1 ht2, ?_⟩` and prove the remaining obligations. Establish `: (x1 + x2) * algebraMap A (FractionRing A) (t1 * t2) = (x1 * algebraMap A (FractionRing A) t1) * algebraMap A (FractionRing A) t2 + (x2 * algebraMap A (FractionRing A) t2) * algebraMap A (FractionRing A) t1`. Rewrite using `[map_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, h1, h2, ← map_mul, ← map_mul, ← map_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Use the proof step `algebraMap_mem' := fun r => ⟨r, 0, 1, P.zero_mem, (Ideal.ne_top_iff_one P).mp (Ideal.IsPrime.ne_top ‹_›), by simp⟩ }`.

Establish `hyS : y ∈ S` using `⟨0, a, algebraMap O A ϖ * s, haP, hws, by`. Rewrite using `[hy, div_mul_cancel₀ _ hws0]`. Use the proof step `simp⟩`. Establish `hBS : B ≤ S` using `Algebra.adjoin_le (Set.singleton_subset_iff.mpr hyS)`. Establish `hcoe : ∀ r : O, ((algebraMap O B r : B) : FractionRing A) = algebraMap A (FractionRing A) (algebraMap O A r)` using `fun r => by`.

Rewrite using `[← IsScalarTower.algebraMap_apply O A (FractionRing A)]`. Both sides reduce to the same expression. Establish `hOB : Function.Injective (algebraMap O B)`. Introduce `r1 r2 h`. Apply `hOA` to reduce the goal to its premises.

Apply `hinj` to reduce the goal to its premises. Rewrite using `[← hcoe, ← hcoe, h]`. Establish `: Module.Flat O B`. Rewrite using `[Module.Flat.flat_iff_torsion_eq_bot_of_isBezout]`. Use `eq_bot_iff.mpr fun x hx => ?_` and prove the remaining obligations.

Take `⟨r, hr⟩` from `(Submodule.mem_torsion_iff x).mp hx`. Rewrite `hr` using `[Submonoid.smul_def, Algebra.smul_def]`. Break down `mul_eq_zero.mp hr with h | h` into its components or cases. Conclude with `absurd (hOB (h.trans (map_zero _).symm)) (nonZeroDivisors.coe_ne_zero r)`. Rewrite using `[h]`.

Conclude with `Submodule.zero_mem _`. Establish `: Algebra.FiniteType A B` using `(Subalgebra.fg_iff_finiteType B).mp (by simpa using Subalgebra.fg_adjoin_finset ({y} : Finset _))`. Establish `: Algebra.FiniteType O B` using `Algebra.FiniteType.trans (S := A) inferInstance inferInstance`. Establish `hsp : Ideal.map (algebraMap O B) (maximalIdeal O) ≠ ⊤`. Rewrite using `[hmax, Ideal.map_span, Set.image_singleton, Ne, Ideal.span_singleton_eq_top]`.

Introduce and unpack `⟨u, hu⟩`. Take `⟨a', p, t, hp, ht, h⟩` from `hBS (↑u⁻¹ : B).2`. Apply `hmeet` to reduce the goal to its premises. Rewrite using `[eq_top_iff, hmapw]`. Establish `hwb : algebraMap A (FractionRing A) (algebraMap O A ϖ) * ((↑u⁻¹ : B) : FractionRing A) = 1`.

Rewrite using `[← hcoe, ← hu, ← Subalgebra.coe_mul, Units.mul_inv, Subalgebra.coe_one]`. Establish `hkey : algebraMap A (FractionRing A) (t - algebraMap O A ϖ * (a' * t + p)) = 0`. Rewrite using `[map_sub, map_mul, ← h]`. Combine the equalities or inequalities in the displayed calculation. Establish `hk` using `hinj (hkey.trans (map_zero _).symm)`.

Establish `htw : t * (1 - algebraMap O A ϖ * a') ∈ P`. Establish `: t * (1 - algebraMap O A ϖ * a') = algebraMap O A ϖ * p`. Take the linear combination `hk`. Rewrite using `[this]`. Conclude with `P.mul_mem_left _ hp`.

Establish `h1 : 1 - algebraMap O A ϖ * a' ∈ P` using `(Ideal.IsPrime.mem_or_mem ‹_› htw).resolve_left ht`. Establish `: (1 : A) = (1 - algebraMap O A ϖ * a') + algebraMap O A ϖ * a'` using `by ring`. Introduce `z _`. Rewrite using `[← mul_one z, this, mul_add]`. Conclude with `Submodule.add_mem _ (Ideal.mem_sup_left (P.mul_mem_left _ h1)) (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))))`.

Establish `heas : algebraMap A B (e * a * s) ≠ 0`. Introduce `h`. Establish `h'` using `congrArg (fun x : B => (x : FractionRing A)) h`. Simplify using `only [Subalgebra.coe_algebraMap, ZeroMemClass.coe_zero] at h'`. Use `hinj (h'.trans (map_zero _).symm)` as an intermediate fact.

Break down `mul_eq_zero.mp this with h2 | h2` into its components or cases. Break down `mul_eq_zero.mp h2 with h3 | h3` into its components or cases. Conclude with `he h3`. Conclude with `ha0 h3`. Conclude with `hsP (h2 ▸ P.zero_mem)`.

Take `⟨V, _, _, _, _, _, φ, hφ⟩` from `av_point hsp _ heas`. Set `φA : A →ₐ[O] V` to `φ.comp (IsScalarTower.toAlgHom O A B)`. Establish `hφA : ∀ x : A, φA x = φ (algebraMap A B x)` using `fun x => rfl`. Rewrite `hφ` using `[map_mul, map_mul, map_mul, map_mul]`. Establish `hφe : φA e ≠ 0` using `by rw [hφA]; intro h; apply hφ; rw [h]; ring`.

Establish `hφa : φA a ≠ 0` using `by rw [hφA]; intro h; apply hφ; rw [h]; ring`. Establish `hφs : φA s ≠ 0` using `by rw [hφA]; intro h; apply hφ; rw [h]; ring`. Take `⟨v, hv⟩` from `hf V φA s a hfa hφa hφe`. Establish `hab : algebraMap A B a = algebraMap O B ϖ * algebraMap A B s * ⟨y, hyB⟩`. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `only [Subalgebra.coe_mul, Subalgebra.coe_algebraMap]`. Rewrite using `[IsScalarTower.algebraMap_apply O A (FractionRing A) ϖ, hy, ← map_mul]`. Clear the denominators using the available nonvanishing facts. Establish `hφab : φA a = algebraMap O V ϖ * φA s * φ ⟨y, hyB⟩`. Rewrite using `[hφA, hab, map_mul, map_mul, AlgHom.commutes]`.

Both sides reduce to the same expression. Rewrite `hv` using `[hφab]`. Establish `hunit : algebraMap O V ϖ * (v * φ ⟨y, hyB⟩) = 1`. Establish `h2 : φA s * (1 - algebraMap O V ϖ * (v * φ ⟨y, hyB⟩)) = 0`. Take the linear combination `hv`.

Establish `h3` using `(mul_eq_zero.mp h2).resolve_left hφs`. Take the linear combination `-h3`. Conclude with `not_isUnit_algebraMap_of_finite ϖ hϖm ⟨⟨algebraMap O V ϖ, v * φ ⟨y, hyB⟩, hunit, by rw [mul_comm]; exact hunit⟩, rfl⟩`.
-/
theorem reg_horizontal_pf {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [CharZero O]
    [CommRing A] [IsDomain A] [Algebra O A] [Algebra.FiniteType O A] [Module.Flat O A]
    (P : Ideal A) [P.IsPrime] (hh : ¬ Ideal.map (algebraMap O A) (maximalIdeal O) ≤ P)
    (hmeet : P ⊔ Ideal.map (algebraMap O A) (maximalIdeal O) ≠ ⊤) (e : A) (he : e ≠ 0)
    (f : FractionRing A)
    (hdvr : (¬ ∃ a s : A, s ∉ P ∧ f * algebraMap A (FractionRing A) s = algebraMap A (FractionRing A) a) →
      ∃ a s : A, a ∈ P ∧ s ∉ P ∧ f⁻¹ * algebraMap A (FractionRing A) s = algebraMap A (FractionRing A) a)
    (hf : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra O V]
      [Module.Finite O V] (φ : A →ₐ[O] V) (a b : A),
      f * algebraMap A (FractionRing A) b = algebraMap A (FractionRing A) a → φ b ≠ 0 → φ e ≠ 0 →
      ∃ v : V, φ a = v * φ b) :
    ∃ a s : A, s ∉ P ∧ f * algebraMap A (FractionRing A) s = algebraMap A (FractionRing A) a := by
  classical
  by_contra hno
  obtain ⟨a, s, haP, hsP, hfas⟩ := hdvr hno
  have hinj : Function.Injective (algebraMap A (FractionRing A)) :=
    IsFractionRing.injective A (FractionRing A)
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hno ⟨0, 1, (Ideal.ne_top_iff_one P).mp (Ideal.IsPrime.ne_top ‹_›), by simp⟩
  have hs0 : algebraMap A (FractionRing A) s ≠ 0 := by
    rw [map_ne_zero_iff _ hinj]; rintro rfl; exact hsP P.zero_mem
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, mul_eq_zero] at hfas
    rcases hfas with h | h
    · exact hf0 (inv_eq_zero.mp h)
    · exact hs0 h
  have hfa : f * algebraMap A (FractionRing A) a = algebraMap A (FractionRing A) s := by
    rw [← hfas, ← mul_assoc, mul_inv_cancel₀ hf0, one_mul]

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hmax : maximalIdeal O = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  have hϖm : ϖ ∈ maximalIdeal O := (mem_maximalIdeal _).mpr hϖ.not_isUnit
  have hmapw : Ideal.map (algebraMap O A) (maximalIdeal O) = Ideal.span {algebraMap O A ϖ} := by
    rw [hmax, Ideal.map_span, Set.image_singleton]
  have hwP : algebraMap O A ϖ ∉ P := fun h =>
    hh (by rw [hmapw, Ideal.span_le, Set.singleton_subset_iff]; exact h)
  have hws : algebraMap O A ϖ * s ∉ P := fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hwP hsP
  have hws0 : algebraMap A (FractionRing A) (algebraMap O A ϖ * s) ≠ 0 := by
    rw [map_ne_zero_iff _ hinj]; rintro h; exact hws (h ▸ P.zero_mem)

  have hOA : Function.Injective (algebraMap O A) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
    rw [map_mul, map_pow, mul_eq_zero] at hx
    rcases hx with h | h
    · exact (u.isUnit.map (algebraMap O A)).ne_zero h
    · exact hwP (pow_eq_zero_iff'.mp h |>.1 ▸ P.zero_mem)

  set y : FractionRing A := algebraMap A (FractionRing A) a /
    algebraMap A (FractionRing A) (algebraMap O A ϖ * s) with hy
  let B : Subalgebra A (FractionRing A) := Algebra.adjoin A {y}
  have hyB : y ∈ B := Algebra.subset_adjoin rfl

  let S : Subalgebra A (FractionRing A) :=
    { carrier := {x | ∃ a' p t : A, p ∈ P ∧ t ∉ P ∧
        x * algebraMap A (FractionRing A) t = algebraMap A (FractionRing A) (a' * t + p)}
      mul_mem' := by
        rintro x1 x2 ⟨a1, p1, t1, hp1, ht1, h1⟩ ⟨a2, p2, t2, hp2, ht2, h2⟩
        refine ⟨a1 * a2, a1 * t1 * p2 + a2 * t2 * p1 + p1 * p2, t1 * t2,
          P.add_mem (P.add_mem (P.mul_mem_left _ hp2) (P.mul_mem_left _ hp1)) (P.mul_mem_left _ hp2),
          fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim ht1 ht2, ?_⟩
        have : x1 * x2 * algebraMap A (FractionRing A) (t1 * t2) =
            (x1 * algebraMap A (FractionRing A) t1) * (x2 * algebraMap A (FractionRing A) t2) := by
          rw [map_mul]; ring
        rw [this, h1, h2, ← map_mul]
        congr 1
        ring
      add_mem' := by
        rintro x1 x2 ⟨a1, p1, t1, hp1, ht1, h1⟩ ⟨a2, p2, t2, hp2, ht2, h2⟩
        refine ⟨a1 + a2, p1 * t2 + p2 * t1, t1 * t2,
          P.add_mem (P.mul_mem_right _ hp1) (P.mul_mem_right _ hp2),
          fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim ht1 ht2, ?_⟩
        have : (x1 + x2) * algebraMap A (FractionRing A) (t1 * t2) =
            (x1 * algebraMap A (FractionRing A) t1) * algebraMap A (FractionRing A) t2 +
              (x2 * algebraMap A (FractionRing A) t2) * algebraMap A (FractionRing A) t1 := by
          rw [map_mul]; ring
        rw [this, h1, h2, ← map_mul, ← map_mul, ← map_add]
        congr 1
        ring
      algebraMap_mem' := fun r => ⟨r, 0, 1, P.zero_mem, (Ideal.ne_top_iff_one P).mp
        (Ideal.IsPrime.ne_top ‹_›), by simp⟩ }
  have hyS : y ∈ S := ⟨0, a, algebraMap O A ϖ * s, haP, hws, by
    rw [hy, div_mul_cancel₀ _ hws0]; simp⟩
  have hBS : B ≤ S := Algebra.adjoin_le (Set.singleton_subset_iff.mpr hyS)

  have hcoe : ∀ r : O, ((algebraMap O B r : B) : FractionRing A) =
      algebraMap A (FractionRing A) (algebraMap O A r) := fun r => by
    rw [← IsScalarTower.algebraMap_apply O A (FractionRing A)]
    rfl
  have hOB : Function.Injective (algebraMap O B) := by
    intro r1 r2 h
    apply hOA; apply hinj
    rw [← hcoe, ← hcoe, h]
  have : Module.Flat O B := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout]
    refine eq_bot_iff.mpr fun x hx => ?_
    obtain ⟨r, hr⟩ := (Submodule.mem_torsion_iff x).mp hx
    rw [Submonoid.smul_def, Algebra.smul_def] at hr
    rcases mul_eq_zero.mp hr with h | h
    · exact absurd (hOB (h.trans (map_zero _).symm)) (nonZeroDivisors.coe_ne_zero r)
    · rw [h]; exact Submodule.zero_mem _
  have : Algebra.FiniteType A B :=
    (Subalgebra.fg_iff_finiteType B).mp (by simpa using Subalgebra.fg_adjoin_finset ({y} : Finset _))
  have : Algebra.FiniteType O B := Algebra.FiniteType.trans (S := A) inferInstance inferInstance

  have hsp : Ideal.map (algebraMap O B) (maximalIdeal O) ≠ ⊤ := by
    rw [hmax, Ideal.map_span, Set.image_singleton, Ne, Ideal.span_singleton_eq_top]
    rintro ⟨u, hu⟩
    obtain ⟨a', p, t, hp, ht, h⟩ := hBS (↑u⁻¹ : B).2
    apply hmeet
    rw [eq_top_iff, hmapw]
    have hwb : algebraMap A (FractionRing A) (algebraMap O A ϖ) * ((↑u⁻¹ : B) : FractionRing A) = 1 := by
      rw [← hcoe, ← hu, ← Subalgebra.coe_mul, Units.mul_inv, Subalgebra.coe_one]
    have hkey : algebraMap A (FractionRing A) (t - algebraMap O A ϖ * (a' * t + p)) = 0 := by
      rw [map_sub, map_mul, ← h]
      calc algebraMap A (FractionRing A) t - algebraMap A (FractionRing A) (algebraMap O A ϖ) *
            (((↑u⁻¹ : B) : FractionRing A) * algebraMap A (FractionRing A) t)
          = algebraMap A (FractionRing A) t - (algebraMap A (FractionRing A) (algebraMap O A ϖ) *
            ((↑u⁻¹ : B) : FractionRing A)) * algebraMap A (FractionRing A) t := by ring
        _ = 0 := by rw [hwb, one_mul, sub_self]
    have hk := hinj (hkey.trans (map_zero _).symm)
    have htw : t * (1 - algebraMap O A ϖ * a') ∈ P := by
      have : t * (1 - algebraMap O A ϖ * a') = algebraMap O A ϖ * p := by
        linear_combination hk
      rw [this]; exact P.mul_mem_left _ hp
    have h1 : 1 - algebraMap O A ϖ * a' ∈ P :=
      (Ideal.IsPrime.mem_or_mem ‹_› htw).resolve_left ht
    have : (1 : A) = (1 - algebraMap O A ϖ * a') + algebraMap O A ϖ * a' := by ring
    intro z _
    rw [← mul_one z, this, mul_add]
    exact Submodule.add_mem _ (Ideal.mem_sup_left (P.mul_mem_left _ h1))
      (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _
        (Ideal.subset_span rfl))))

  have heas : algebraMap A B (e * a * s) ≠ 0 := by
    intro h
    have h' := congrArg (fun x : B => (x : FractionRing A)) h
    simp only [Subalgebra.coe_algebraMap, ZeroMemClass.coe_zero] at h'
    have := hinj (h'.trans (map_zero _).symm)
    rcases mul_eq_zero.mp this with h2 | h2
    · rcases mul_eq_zero.mp h2 with h3 | h3
      · exact he h3
      · exact ha0 h3
    · exact hsP (h2 ▸ P.zero_mem)
  obtain ⟨V, _, _, _, _, _, φ, hφ⟩ := av_point hsp _ heas
  let φA : A →ₐ[O] V := φ.comp (IsScalarTower.toAlgHom O A B)
  have hφA : ∀ x : A, φA x = φ (algebraMap A B x) := fun x => rfl
  rw [map_mul, map_mul, map_mul, map_mul] at hφ
  have hφe : φA e ≠ 0 := by rw [hφA]; intro h; apply hφ; rw [h]; ring
  have hφa : φA a ≠ 0 := by rw [hφA]; intro h; apply hφ; rw [h]; ring
  have hφs : φA s ≠ 0 := by rw [hφA]; intro h; apply hφ; rw [h]; ring
  obtain ⟨v, hv⟩ := hf V φA s a hfa hφa hφe

  have hab : algebraMap A B a = algebraMap O B ϖ * algebraMap A B s * ⟨y, hyB⟩ := by
    apply Subtype.ext
    simp only [Subalgebra.coe_mul, Subalgebra.coe_algebraMap]
    rw [IsScalarTower.algebraMap_apply O A (FractionRing A) ϖ, hy, ← map_mul]
    field_simp
  have hφab : φA a = algebraMap O V ϖ * φA s * φ ⟨y, hyB⟩ := by
    rw [hφA, hab, map_mul, map_mul, AlgHom.commutes]
    rfl
  rw [hφab] at hv
  have hunit : algebraMap O V ϖ * (v * φ ⟨y, hyB⟩) = 1 := by
    have h2 : φA s * (1 - algebraMap O V ϖ * (v * φ ⟨y, hyB⟩)) = 0 := by
      linear_combination hv
    have h3 := (mul_eq_zero.mp h2).resolve_left hφs
    linear_combination -h3
  exact not_isUnit_algebraMap_of_finite ϖ hϖm
    ⟨⟨algebraMap O V ϖ, v * φ ⟨y, hyB⟩, hunit, by rw [mul_comm]; exact hunit⟩, rfl⟩

end ReciprocityTheory.ChartRestriction.G.T0
