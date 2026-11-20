import Development.EtaleCohomology.EtaleSheaves.A9OfA0A1EigenbasisA6

noncomputable section
open CategoryTheory AlgebraicGeometry GlobalTheory.EtC Polynomial IsLocalRing

namespace LateralTheory.E.LeafClosedSH0PfPrim
open LateralTheory.E.E4 LateralTheory.E.LeafClosedSH0Pf

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
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
Rewrite the conclusion using the stated equalities.
-/
theorem evalHom {B C : Type} [CommRing B] [CommRing C] (f : B →+* C) (p : B[X]) (x : B) :
    f (p.eval x) = (p.map f).eval (f x) := by
  rw [Polynomial.eval_map, eval₂_at_apply]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Express the relevant assertion in an equivalent form by its definition. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
