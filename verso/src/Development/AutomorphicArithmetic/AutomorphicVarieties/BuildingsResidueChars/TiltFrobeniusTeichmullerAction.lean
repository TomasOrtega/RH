import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.WdDefs
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalLetter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSubLtOneOfFix
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module Topology Polynomial

namespace UpperTheory.V.Af.Wd

variable {l : ℕ} [hl : Fact l.Prime]

open scoped Formalism.Per in
/- English proof (translation)
Establish `h1 : 1 < l ^ m` using `Nat.one_lt_pow hm.ne' hl.out.one_lt`. Establish `hz : y.untilt ^ l ^ m = y.untilt` using `by rw [← map_pow, hy]`. Establish `hz' : ((y.untilt : OC l) : ℂ_[l]) ^ l ^ m = (y.untilt : OC l)`. Use `congrArg (fun t : OC l => (t : ℂ_[l])) hz` as an intermediate fact. Simplify using `using this`.

Establish `hint : IsIntegral (Om l) ((y.untilt : OC l) : ℂ_[l])`. Use `⟨X ^ l ^ m - X, monic_X_pow_sub (by rw [degree_X]; exact_mod_cast h1), ?_⟩` and prove the remaining obligations. Simplify using `[hz']`. Take `⟨x, hx⟩` from `minpoly.mem_range_of_degree_eq_one (Om l) _ (IsAlgClosed.degree_eq_one_of_irreducible (Om l) (minpoly.irreducible hint))`. Use `⟨y.untilt, x, hx.symm, ?_, (PreTilt.mk_untilt_eq_coeff_zero y).symm⟩` and prove the remaining obligations.

Apply `(algebraMap (Om l) ℂ_[l]).injective` to reduce the goal to its premises. Establish `hx' : algebraMap (Om l) ℂ_[l] x = (y.untilt : OC l)` using `hx`. Rewrite using `[map_pow, hx', hz']`.
-/
private theorem tf_lift (y : OCb l) {m : ℕ} (hm : 0 < m) (hy : y ^ l ^ m = y) :
    ∃ (z : OC l) (x : Om l), (z : ℂ_[l]) = (x : ℂ_[l]) ∧ x ^ l ^ m = x ∧
      PreTilt.coeff 0 y = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) z := by
  have h1 : 1 < l ^ m := Nat.one_lt_pow hm.ne' hl.out.one_lt
  have hz : y.untilt ^ l ^ m = y.untilt := by rw [← map_pow, hy]
  have hz' : ((y.untilt : OC l) : ℂ_[l]) ^ l ^ m = (y.untilt : OC l) := by
    have := congrArg (fun t : OC l => (t : ℂ_[l])) hz
    simpa using this
  have hint : IsIntegral (Om l) ((y.untilt : OC l) : ℂ_[l]) := by
    refine ⟨X ^ l ^ m - X, monic_X_pow_sub (by rw [degree_X]; exact_mod_cast h1), ?_⟩
    simp [hz']
  obtain ⟨x, hx⟩ := minpoly.mem_range_of_degree_eq_one (Om l) _
    (IsAlgClosed.degree_eq_one_of_irreducible (Om l) (minpoly.irreducible hint))
  refine ⟨y.untilt, x, hx.symm, ?_, (PreTilt.mk_untilt_eq_coeff_zero y).symm⟩
  apply (algebraMap (Om l) ℂ_[l]).injective
  have hx' : algebraMap (Om l) ℂ_[l] x = (y.untilt : OC l) := hx
  rw [map_pow, hx', hz']

/- English proof (translation)
Take `⟨y', h1, h2⟩` from `AI.actT_coeff g y 0 _ h0`. Rewrite `h1` using `[hzx, AI.actC_ext, hg, PadicComplex.coe_eq, map_pow, ← PadicComplex.coe_eq, ← hzx]`. Establish `h3 : y' = z ^ k` using `Subtype.ext (by rw [h1]; simp)`. Use `GlobalTheory.UnramifiedCrys.eq_of_coeff_zero hm (by rw [← map_pow, hy]) (by rw [← pow_mul, mul_comm, pow_mul, hy]) ?_` and prove the remaining obligations. Rewrite using `[h2, map_pow, h0, h3]`.

Conclude with `map_pow _ _ _`.
-/
private theorem tf_act {P : LocPrime l} (AI : LocAinf l P) (y : OCb l) {m : ℕ} (hm : 0 < m) (hy : y ^ l ^ m = y)
    {z : OC l} {x : Om l} (hzx : (z : ℂ_[l]) = (x : ℂ_[l]))
    (h0 : PreTilt.coeff 0 y = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) z)
    (g : GQ l) (k : ℕ) (hg : g x = x ^ k) : AI.actT g y = y ^ k := by
  obtain ⟨y', h1, h2⟩ := AI.actT_coeff g y 0 _ h0
  rw [hzx, AI.actC_ext, hg, PadicComplex.coe_eq, map_pow, ← PadicComplex.coe_eq, ← hzx] at h1
  have h3 : y' = z ^ k := Subtype.ext (by rw [h1]; simp)
  refine GlobalTheory.UnramifiedCrys.eq_of_coeff_zero hm (by rw [← map_pow, hy])
    (by rw [← pow_mul, mul_comm, pow_mul, hy]) ?_
  rw [h2, map_pow, h0, h3]
  exact map_pow _ _ _

/- English proof (translation)
Establish `h1 : 1 < l ^ m` using `Nat.one_lt_pow hm.ne' hl.out.one_lt`. Use `⟨l ^ m - 1, by omega, fun h => ?_, ?_⟩` and prove the remaining obligations. Establish `h2` using `(Nat.dvd_sub_iff_right h1.le (dvd_pow_self l hm.ne')).mp h`. Conclude with `hl.out.one_lt.ne' (Nat.dvd_one.mp h2)`. Apply `mul_right_cancel₀ h0` to reduce the goal to its premises.

Rewrite using `[← pow_succ, one_mul, Nat.sub_add_cancel h1.le, hx]`.
-/
private theorem tf_root {x : Om l} {m : ℕ} (hm : 0 < m) (hx : x ^ l ^ m = x) (h0 : x ≠ 0) :
    ∃ n, 0 < n ∧ ¬ l ∣ n ∧ x ^ n = 1 := by
  have h1 : 1 < l ^ m := Nat.one_lt_pow hm.ne' hl.out.one_lt
  refine ⟨l ^ m - 1, by omega, fun h => ?_, ?_⟩
  · have h2 := (Nat.dvd_sub_iff_right h1.le (dvd_pow_self l hm.ne')).mp h
    exact hl.out.one_lt.ne' (Nat.dvd_one.mp h2)
  · apply mul_right_cancel₀ h0
    rw [← pow_succ, one_mul, Nat.sub_add_cancel h1.le, hx]

end UpperTheory.V.Af.Wd

open UpperTheory.V.Af.Wd in
/- English proof (translation)
Introduce `l hl y m hm hy g k hg`. Take `⟨z, x, hzx, hx, h0⟩` from `tf_lift y hm hy`. Use `tf_act _ y hm hy hzx h0 g (l ^ k) ?_` and prove the remaining obligations. Distinguish the cases in `hx0 : x = 0`. Rewrite using `[hx0, map_zero, zero_pow (pow_ne_zero _ hl.out.ne_zero)]`.

Take `⟨n, hn0, hn, hxn⟩` from `tf_root hm hx hx0`. Establish `hmem : x ∈ Formalism.BasicNotions.Loc.MaximalUnramifiedExtension l` using `IntermediateField.subset_adjoin _ _ ⟨n, hn0, hn, hxn⟩`. Establish `h1` using `hg ⟨x, hmem⟩`. Rewrite `h1` using `[GlobalTheory.Pst.frobUr_pow_root k ⟨x, hmem⟩ n hn0 hn (Subtype.ext hxn)]`. Conclude with `h1`.
-/
theorem UpperTheory.tilt_frobenius_teichmuller_action :
    UpperTheory.V.Af.Wd.TiltFrob := by
  intro l hl y m hm hy g k hg
  obtain ⟨z, x, hzx, hx, h0⟩ := tf_lift y hm hy
  refine tf_act _ y hm hy hzx h0 g (l ^ k) ?_
  by_cases hx0 : x = 0
  · rw [hx0, map_zero, zero_pow (pow_ne_zero _ hl.out.ne_zero)]
  obtain ⟨n, hn0, hn, hxn⟩ := tf_root hm hx hx0
  have hmem : x ∈ Formalism.BasicNotions.Loc.MaximalUnramifiedExtension l := IntermediateField.subset_adjoin _ _ ⟨n, hn0, hn, hxn⟩
  have h1 := hg ⟨x, hmem⟩
  rw [GlobalTheory.Pst.frobUr_pow_root k ⟨x, hmem⟩ n hn0 hn (Subtype.ext hxn)] at h1
  exact h1
