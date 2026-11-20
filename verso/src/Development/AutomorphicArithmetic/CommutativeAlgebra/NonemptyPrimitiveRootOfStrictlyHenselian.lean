import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

/- English proof (translation)
Introduce `q _ O _ hO hq`. Take `⟨hH, hsep⟩` from `hO`. Establish `key : ∀ (p : Polynomial O) (x : O), IsLocalRing.residue O (p.eval x) = (p.map (IsLocalRing.residue O)).eval (IsLocalRing.residue O x)`. Introduce `p x`. Rewrite using `[Polynomial.eval_map, Polynomial.eval₂_hom]`.

Establish `hqk : ((q : ℕ) : IsLocalRing.ResidueField O) ≠ 0`. Use `(IsLocalRing.residue_ne_zero_iff_isUnit (q : O)).2 hq` as an intermediate fact. Simplify using `using this`. Use `haveI : NeZero ((q : ℕ) : IsLocalRing.ResidueField O) := ⟨hqk⟩`. Establish `hdeg : (Polynomial.cyclotomic q (IsLocalRing.ResidueField O)).degree ≠ 0`.

Rewrite using `[Polynomial.degree_cyclotomic]`. Conclude with `(Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q))).ne'` after adjusting the coercions. Take `⟨r, hr⟩` from `IsSepClosed.exists_root _ hdeg (Polynomial.separable_cyclotomic q (IsLocalRing.ResidueField O))`. Take `⟨a₀, rfl⟩` from `IsLocalRing.residue_surjective r`. Establish `h1 : (Polynomial.cyclotomic q O).eval a₀ ∈ IsLocalRing.maximalIdeal O`.

Rewrite using `[← IsLocalRing.residue_eq_zero_iff, key, Polynomial.map_cyclotomic]`. Conclude with `hr`. Establish `h2 : IsUnit ((Polynomial.derivative (Polynomial.cyclotomic q O)).eval a₀)`. Rewrite using `[← IsLocalRing.residue_ne_zero_iff_isUnit, key, ← Polynomial.derivative_map, Polynomial.map_cyclotomic]`. Establish `h0` using `(Polynomial.separable_cyclotomic q (IsLocalRing.ResidueField O)).aeval_derivative_ne_zero (x := IsLocalRing.residue O a₀) (by simpa [Polynomial.coe_aeval_eq_eval] using hr)`.

Simplify `h0` using `[Polynomial.coe_aeval_eq_eval]`. Take `⟨a, ha, -⟩` from `HenselianLocalRing.is_henselian (Polynomial.cyclotomic q O) (Polynomial.cyclotomic.monic q O) a₀ h1 h2`. Use `⟨⟨a, hq, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]`. Conclude with `ha`.
-/
theorem UpperTheory.nonempty_primitive_root_of_strictly_henselian :
    ∀ (q : ℕ) [NeZero q] (O : Type) [CommRing O], SH O → IsUnit (q : O) → Nonempty (Prim q O) := by
  intro q _ O _ hO hq
  obtain ⟨hH, hsep⟩ := hO
  have key : ∀ (p : Polynomial O) (x : O), IsLocalRing.residue O (p.eval x) =
      (p.map (IsLocalRing.residue O)).eval (IsLocalRing.residue O x) := by
    intro p x
    rw [Polynomial.eval_map, Polynomial.eval₂_hom]
  have hqk : ((q : ℕ) : IsLocalRing.ResidueField O) ≠ 0 := by
    have := (IsLocalRing.residue_ne_zero_iff_isUnit (q : O)).2 hq
    simpa using this
  haveI : NeZero ((q : ℕ) : IsLocalRing.ResidueField O) := ⟨hqk⟩
  have hdeg : (Polynomial.cyclotomic q (IsLocalRing.ResidueField O)).degree ≠ 0 := by
    rw [Polynomial.degree_cyclotomic]
    exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q))).ne'
  obtain ⟨r, hr⟩ := IsSepClosed.exists_root _ hdeg
    (Polynomial.separable_cyclotomic q (IsLocalRing.ResidueField O))
  obtain ⟨a₀, rfl⟩ := IsLocalRing.residue_surjective r
  have h1 : (Polynomial.cyclotomic q O).eval a₀ ∈ IsLocalRing.maximalIdeal O := by
    rw [← IsLocalRing.residue_eq_zero_iff, key, Polynomial.map_cyclotomic]
    exact hr
  have h2 : IsUnit ((Polynomial.derivative (Polynomial.cyclotomic q O)).eval a₀) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, key, ← Polynomial.derivative_map,
      Polynomial.map_cyclotomic]
    have h0 := (Polynomial.separable_cyclotomic q (IsLocalRing.ResidueField O)).aeval_derivative_ne_zero
      (x := IsLocalRing.residue O a₀) (by simpa [Polynomial.coe_aeval_eq_eval] using hr)
    simpa [Polynomial.coe_aeval_eq_eval] using h0
  obtain ⟨a, ha, -⟩ := HenselianLocalRing.is_henselian (Polynomial.cyclotomic q O)
    (Polynomial.cyclotomic.monic q O) a₀ h1 h2
  refine ⟨⟨a, hq, ?_⟩⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
  exact ha
