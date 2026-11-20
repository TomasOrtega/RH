import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup

noncomputable section

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma.HilbertNinety

/- English proof (translation)
Use `letI : Module ℚ B.A := Module.compHom B.A (algebraMap ℚ K.E)`. Set `b : B.A →+ B.A` to `{ toFun := fun a => a + B.σ a * B.σ u map_zero' := by simp map_add' := by intro x y; simp only [map_add]; ring }`. Establish `hb : ∀ a, b a = a + B.σ a * B.σ u` using `fun a => rfl`. Establish `hbσ : ∀ a, B.σ (b a) = b a * u`. Introduce `a`.

Rewrite using `[hb, map_add, map_mul, B.σ_σ, B.σ_σ]`. Take the linear combination `(-(B.σ a)) * hu`. Take `⟨x, y, hxy, hne⟩` from `K.c_res`. Use `set e : K.E := algebraMap K.O K.E x with he`. Establish `hce : K.c e - e ≠ 0`.

Introduce `h`. Rewrite `h` using `[sub_eq_zero, he, hxy]`. Use `IsFractionRing.injective K.O K.E h` as an intermediate fact. Conclude with `hne (by rw [this, sub_self]; exact Ideal.zero_mem _)`. Establish `key : ∀ z : B.A, algebraMap K.E B.A (K.c e - e) * z = algebraMap K.E B.A (K.c e) * b z - b (algebraMap K.E B.A e * z)`.

Introduce `z`. Rewrite using `[hb, hb, map_mul, B.σ_alg, map_sub]`. Expand and normalize the polynomial expressions, which then agree. Use `haveI : IsArtinianRing B.A := IsArtinianRing.of_finite K.E B.A`. Use `haveI : Fintype (MaximalSpectrum B.A) := Fintype.ofFinite _`.

Set `S : MaximalSpectrum B.A → Submodule ℚ B.A` to `fun m => { carrier := {a | b a ∈ m.asIdeal} add_mem' := fun {a c} ha hc => by`. Express the relevant statement in the definitionally equal form `b (a + c) ∈ m.asIdeal`. Rewrite using `[map_add]`. Conclude with `m.asIdeal.add_mem ha hc`. Use the proof step `zero_mem' := by change b 0 ∈ m.asIdeal; rw [map_zero]; exact m.asIdeal.zero_mem`.

Use the proof step `smul_mem' := fun q a ha => by`. Express the relevant statement in the definitionally equal form `b (q • a) ∈ m.asIdeal`. Rewrite using `[map_rat_smul]`. Express the relevant statement in the definitionally equal form `(algebraMap ℚ K.E q) • b a ∈ m.asIdeal`. Rewrite using `[Algebra.smul_def]`.

Conclude with `m.asIdeal.mul_mem_left _ ha }`. Establish `hS : ⊤ ∉ Finset.univ.image S`. Introduce `h`. Take `⟨m, -, hm⟩` from `Finset.mem_image.1 h`. Establish `hall : ∀ a, b a ∈ m.asIdeal` using `fun a => by`.

Establish `: a ∈ S m` using `hm ▸ Submodule.mem_top`. Conclude with `this`. Establish `h1 : algebraMap K.E B.A (K.c e - e) ∈ m.asIdeal`. Use `key 1` as an intermediate fact. Rewrite `this` using `[mul_one]`.

Rewrite using `[this]`. Conclude with `m.asIdeal.sub_mem (m.asIdeal.mul_mem_left _ (hall 1)) (hall _)`. Apply `m.isMaximal.ne_top` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one]`. Establish `h2 : algebraMap K.E B.A (K.c e - e)⁻¹ * algebraMap K.E B.A (K.c e - e) = 1`.

Rewrite using `[← map_mul, inv_mul_cancel₀ hce, map_one]`. Rewrite using `[← h2]`. Conclude with `m.asIdeal.mul_mem_left _ h1`. Establish `h3` using `Subspace.biUnion_ne_univ_of_top_notMem hS`. Take `⟨a, ha⟩` from `(Set.ne_univ_iff_exists_notMem _).1 h3`.

Establish `hunit : IsUnit (b a)`. Assume the negation of the conclusion as `hn`. Take `⟨m, hm, hxm⟩` from `exists_max_ideal_of_mem_nonunits hn`. Apply `ha` to reduce the goal to its premises. Conclude with `Set.mem_biUnion (x := S ⟨m, hm⟩) (by simp) hxm`.

Conclude with `⟨hunit.unit, by rw [IsUnit.unit_spec]; exact hbσ a⟩`.
-/
theorem exists_unit_sigma (K : UQ) (B : InvAlg K) (u : B.A) (hu : u * B.σ u = 1) :
    ∃ β : B.Aˣ, B.σ (β : B.A) = β * u := by
  classical
  letI : Module ℚ B.A := Module.compHom B.A (algebraMap ℚ K.E)
  let b : B.A →+ B.A :=
    { toFun := fun a => a + B.σ a * B.σ u
      map_zero' := by simp
      map_add' := by intro x y; simp only [map_add]; ring }
  have hb : ∀ a, b a = a + B.σ a * B.σ u := fun a => rfl
  have hbσ : ∀ a, B.σ (b a) = b a * u := by
    intro a
    rw [hb, map_add, map_mul, B.σ_σ, B.σ_σ]
    linear_combination (-(B.σ a)) * hu
  obtain ⟨x, y, hxy, hne⟩ := K.c_res
  set e : K.E := algebraMap K.O K.E x with he
  have hce : K.c e - e ≠ 0 := by
    intro h
    rw [sub_eq_zero, he, hxy] at h
    have := IsFractionRing.injective K.O K.E h
    exact hne (by rw [this, sub_self]; exact Ideal.zero_mem _)
  have key : ∀ z : B.A, algebraMap K.E B.A (K.c e - e) * z =
      algebraMap K.E B.A (K.c e) * b z - b (algebraMap K.E B.A e * z) := by
    intro z
    rw [hb, hb, map_mul, B.σ_alg, map_sub]
    ring
  haveI : IsArtinianRing B.A := IsArtinianRing.of_finite K.E B.A
  haveI : Fintype (MaximalSpectrum B.A) := Fintype.ofFinite _
  let S : MaximalSpectrum B.A → Submodule ℚ B.A := fun m =>
    { carrier := {a | b a ∈ m.asIdeal}
      add_mem' := fun {a c} ha hc => by
        change b (a + c) ∈ m.asIdeal
        rw [map_add]; exact m.asIdeal.add_mem ha hc
      zero_mem' := by change b 0 ∈ m.asIdeal; rw [map_zero]; exact m.asIdeal.zero_mem
      smul_mem' := fun q a ha => by
        change b (q • a) ∈ m.asIdeal
        rw [map_rat_smul]
        change (algebraMap ℚ K.E q) • b a ∈ m.asIdeal
        rw [Algebra.smul_def]
        exact m.asIdeal.mul_mem_left _ ha }
  have hS : ⊤ ∉ Finset.univ.image S := by
    intro h
    obtain ⟨m, -, hm⟩ := Finset.mem_image.1 h
    have hall : ∀ a, b a ∈ m.asIdeal := fun a => by
      have : a ∈ S m := hm ▸ Submodule.mem_top
      exact this
    have h1 : algebraMap K.E B.A (K.c e - e) ∈ m.asIdeal := by
      have := key 1
      rw [mul_one] at this
      rw [this]
      exact m.asIdeal.sub_mem (m.asIdeal.mul_mem_left _ (hall 1)) (hall _)
    apply m.isMaximal.ne_top
    rw [Ideal.eq_top_iff_one]
    have h2 : algebraMap K.E B.A (K.c e - e)⁻¹ * algebraMap K.E B.A (K.c e - e) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hce, map_one]
    rw [← h2]
    exact m.asIdeal.mul_mem_left _ h1
  have h3 := Subspace.biUnion_ne_univ_of_top_notMem hS
  obtain ⟨a, ha⟩ := (Set.ne_univ_iff_exists_notMem _).1 h3
  have hunit : IsUnit (b a) := by
    by_contra hn
    obtain ⟨m, hm, hxm⟩ := exists_max_ideal_of_mem_nonunits hn
    apply ha
    exact Set.mem_biUnion (x := S ⟨m, hm⟩) (by simp) hxm
  exact ⟨hunit.unit, by rw [IsUnit.unit_spec]; exact hbσ a⟩

end GlobalTheory.UnitLemma.HilbertNinety
