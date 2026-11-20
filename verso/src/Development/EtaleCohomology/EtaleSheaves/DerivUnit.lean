import Development.EtaleCohomology.EtaleSheaves.A9OfA0A1EigenbasisA6

noncomputable section
open CategoryTheory AlgebraicGeometry GlobalTheory.EtC Polynomial IsLocalRing

namespace LateralTheory.E.LeafClosedSH0PfPrim
open LateralTheory.E.E4 LateralTheory.E.LeafClosedSH0Pf

/- English proof (translation)
Establish `hq0 : q ≠ 0` using `by rintro rfl; simp at hq`. Take `⟨g, hg⟩` from `cyclotomic.dvd_X_pow_sub_one q C`. Establish `hzq : z ^ q = 1`. Use `congrArg (eval z) hg` as an intermediate fact. Simplify using `only [eval_sub, eval_pow, eval_X, eval_one, eval_mul, hz, zero_mul] at this`.

Conclude with `sub_eq_zero.mp this`. Establish `hzu : IsUnit z` using `IsUnit.of_pow_eq_one hzq hq0`. Establish `hd` using `congrArg (fun p => (derivative p).eval z) hg`. Simplify using `only [derivative_mul, derivative_sub, derivative_X_pow, derivative_one, sub_zero, eval_add, eval_mul, eval_C, eval_pow, eval_X, hz, zero_mul, add_zero] at hd`. Establish `hu : IsUnit ((q : C) * z ^ (q - 1))` using `hq.mul (hzu.pow _)`.

Establish `hu' : IsUnit ((derivative (cyclotomic q C)).eval z * g.eval z)`. Rewrite using `[← hd]`. Simplify using `using hu`. Conclude with `isUnit_of_mul_isUnit_left hu'`.
-/
theorem derivUnit {C : Type} [CommRing C] [Nontrivial C] (q : ℕ) (z : C) (hq : IsUnit (q : C))
    (hz : (cyclotomic q C).eval z = 0) : IsUnit ((derivative (cyclotomic q C)).eval z) := by
  have hq0 : q ≠ 0 := by rintro rfl; simp at hq
  obtain ⟨g, hg⟩ := cyclotomic.dvd_X_pow_sub_one q C
  have hzq : z ^ q = 1 := by
    have := congrArg (eval z) hg
    simp only [eval_sub, eval_pow, eval_X, eval_one, eval_mul, hz, zero_mul] at this
    exact sub_eq_zero.mp this
  have hzu : IsUnit z := IsUnit.of_pow_eq_one hzq hq0
  have hd := congrArg (fun p => (derivative p).eval z) hg
  simp only [derivative_mul, derivative_sub, derivative_X_pow, derivative_one, sub_zero, eval_add, eval_mul,
    eval_C, eval_pow, eval_X, hz, zero_mul, add_zero] at hd
  have hu : IsUnit ((q : C) * z ^ (q - 1)) := hq.mul (hzu.pow _)
  have hu' : IsUnit ((derivative (cyclotomic q C)).eval z * g.eval z) := by
    rw [← hd]; simpa using hu
  exact isUnit_of_mul_isUnit_left hu'

/- English proof (translation)
Rewrite using `[Polynomial.eval_map, eval₂_at_apply]`.
-/
theorem evalHom {B C : Type} [CommRing B] [CommRing C] (f : B →+* C) (p : B[X]) (x : B) :
    f (p.eval x) = (p.map f).eval (f x) := by
  rw [Polynomial.eval_map, eval₂_at_apply]

/- English proof (translation)
Introduce `q B C _ _ _ _ f hf ζ`. Establish `hloc : IsLocalHom f` using `IsLocalHom.of_surjective f hf`. Take `⟨z, hqC, hz⟩` from `ζ`. Establish `hz' : (cyclotomic q C).eval z = 0`. Rewrite `hz` using `[aeval_def, ← Polynomial.eval_map, map_cyclotomic]`.

Conclude with `hz`. Establish `hqB : IsUnit (q : B)`. Establish `: IsUnit (f (q : B))` using `by simpa using hqC`. Conclude with `(isUnit_map_iff f _).mp this`. Take `⟨a0, rfl⟩` from `hf z`.

Establish `hker : (cyclotomic q B).eval a0 ∈ maximalIdeal B`. Rewrite using `[mem_maximalIdeal, mem_nonunits_iff]`. Introduce `hu`. Use `hu.map f` as an intermediate fact. Rewrite `this` using `[evalHom, map_cyclotomic, hz']`.

Conclude with `not_isUnit_zero this`. Establish `hder : IsUnit ((derivative (cyclotomic q B)).eval a0)`. Apply `(isUnit_map_iff f _).mp` to reduce the goal to its premises. Rewrite using `[evalHom, ← derivative_map, map_cyclotomic]`. Conclude with `derivUnit q (f a0) hqC hz'`.

Establish `: IsLocalRing C` using `IsLocalRing.of_surjective' f hf`. Take `⟨a, ha, ham⟩` from `HenselianLocalRing.is_henselian (cyclotomic q B) (cyclotomic.monic q B) a0 hker hder`. Establish `hfa : (cyclotomic q C).eval (f a) = 0`. Rewrite using `[← map_cyclotomic q f, ← evalHom, ha.eq_zero, map_zero]`. Use `⟨⟨a, hqB, ?_⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[aeval_def, ← Polynomial.eval_map, map_cyclotomic]`. Conclude with `ha.eq_zero`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `f a = f a0`. Use `IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub hfa hz' ?_ (derivUnit q (f a) hqC hfa)` and prove the remaining obligations.

Rewrite using `[← map_sub, isUnit_map_iff]`. Conclude with `(mem_maximalIdeal _).mp ham`.
-/
theorem primLift : LeafPrimLift := by
  intro q B C _ _ _ _ f hf ζ
  have hloc : IsLocalHom f := IsLocalHom.of_surjective f hf
  obtain ⟨z, hqC, hz⟩ := ζ
  have hz' : (cyclotomic q C).eval z = 0 := by
    rw [aeval_def, ← Polynomial.eval_map, map_cyclotomic] at hz; exact hz
  have hqB : IsUnit (q : B) := by
    have : IsUnit (f (q : B)) := by simpa using hqC
    exact (isUnit_map_iff f _).mp this
  obtain ⟨a0, rfl⟩ := hf z
  have hker : (cyclotomic q B).eval a0 ∈ maximalIdeal B := by
    rw [mem_maximalIdeal, mem_nonunits_iff]; intro hu
    have := hu.map f
    rw [evalHom, map_cyclotomic, hz'] at this
    exact not_isUnit_zero this
  have hder : IsUnit ((derivative (cyclotomic q B)).eval a0) := by
    apply (isUnit_map_iff f _).mp
    rw [evalHom, ← derivative_map, map_cyclotomic]
    exact derivUnit q (f a0) hqC hz'
  have : IsLocalRing C := IsLocalRing.of_surjective' f hf
  obtain ⟨a, ha, ham⟩ := HenselianLocalRing.is_henselian (cyclotomic q B) (cyclotomic.monic q B) a0 hker hder
  have hfa : (cyclotomic q C).eval (f a) = 0 := by
    rw [← map_cyclotomic q f, ← evalHom, ha.eq_zero, map_zero]
  refine ⟨⟨a, hqB, ?_⟩, ?_⟩
  · rw [aeval_def, ← Polynomial.eval_map, map_cyclotomic]; exact ha.eq_zero
  · apply Subtype.ext
    change f a = f a0
    refine IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub hfa hz' ?_ (derivUnit q (f a) hqC hfa)
    rw [← map_sub, isUnit_map_iff]
    exact (mem_maximalIdeal _).mp ham

end LateralTheory.E.LeafClosedSH0PfPrim
