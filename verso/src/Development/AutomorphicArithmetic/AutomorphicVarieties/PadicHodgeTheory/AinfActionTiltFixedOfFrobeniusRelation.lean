import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaWDDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedIsCrysAndJumpEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ConclusionFinite
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSubLtOneOfFix
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W

namespace UpperTheory.V.Loc

variable {l : ℕ} [hl : Fact l.Prime]

open Polynomial in
open scoped Formalism.Per in
/- English proof (translation)
Establish `h1 : 1 < l ^ m` using `Nat.one_lt_pow hm.ne' hl.out.one_lt`. Establish `hz : y.untilt ^ l ^ m = y.untilt` using `by rw [← map_pow, hy]`. Establish `hz' : ((y.untilt : OC l) : ℂ_[l]) ^ l ^ m = (y.untilt : OC l)`. Use `congrArg (fun t : OC l => (t : ℂ_[l])) hz` as an intermediate fact. Simplify using `using this`.

Establish `hint : IsIntegral (Om l) ((y.untilt : OC l) : ℂ_[l])`. Use `⟨X ^ l ^ m - X, monic_X_pow_sub (by rw [degree_X]; exact_mod_cast h1), ?_⟩` and prove the remaining obligations. Simplify using `[hz']`. Take `⟨x, hx⟩` from `minpoly.mem_range_of_degree_eq_one (Om l) _ (IsAlgClosed.degree_eq_one_of_irreducible (Om l) (minpoly.irreducible hint))`. Use `⟨y.untilt, x, hx.symm, ?_, (PreTilt.mk_untilt_eq_coeff_zero y).symm⟩` and prove the remaining obligations.

Apply `(algebraMap (Om l) ℂ_[l]).injective` to reduce the goal to its premises. Establish `hx' : algebraMap (Om l) ℂ_[l] x = (y.untilt : OC l)` using `hx`. Rewrite using `[map_pow, hx', hz']`.
-/
private theorem tfab_lift (y : OCb l) {m : ℕ} (hm : 0 < m) (hy : y ^ l ^ m = y) :
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
Establish `h1 : 1 < l ^ m` using `Nat.one_lt_pow hm.ne' hl.out.one_lt`. Use `⟨l ^ m - 1, by omega, fun h => ?_, ?_⟩` and prove the remaining obligations. Establish `h2` using `(Nat.dvd_sub_iff_right h1.le (dvd_pow_self l hm.ne')).mp h`. Conclude with `hl.out.one_lt.ne' (Nat.dvd_one.mp h2)`. Apply `mul_right_cancel₀ h0` to reduce the goal to its premises.

Rewrite using `[← pow_succ, one_mul, Nat.sub_add_cancel h1.le, hx]`.
-/
private theorem tfab_root {x : Om l} {m : ℕ} (hm : 0 < m) (hx : x ^ l ^ m = x) (h0 : x ≠ 0) :
    ∃ n, 0 < n ∧ ¬ l ∣ n ∧ x ^ n = 1 := by
  have h1 : 1 < l ^ m := Nat.one_lt_pow hm.ne' hl.out.one_lt
  refine ⟨l ^ m - 1, by omega, fun h => ?_, ?_⟩
  · have h2 := (Nat.dvd_sub_iff_right h1.le (dvd_pow_self l hm.ne')).mp h
    exact hl.out.one_lt.ne' (Nat.dvd_one.mp h2)
  · apply mul_right_cancel₀ h0
    rw [← pow_succ, one_mul, Nat.sub_add_cancel h1.le, hx]

end UpperTheory.V.Loc

/- English proof (translation)
Introduce `l hl P AI g a b hg y m hm hy`. Take `⟨z, x, hzx, hx, h0⟩` from `UpperTheory.V.Loc.tfab_lift y hm hy`. Establish `hgx : g (x ^ l ^ b) = x ^ l ^ a`. Distinguish the cases in `hx0 : x = 0`. Rewrite using `[hx0, zero_pow (pow_ne_zero _ hl.out.ne_zero), zero_pow (pow_ne_zero _ hl.out.ne_zero), map_zero]`.

Take `⟨n, hn0, hn, hxn⟩` from `UpperTheory.V.Loc.tfab_root hm hx hx0`. Establish `hmem : x ∈ MaximalUnramifiedExtension l` using `IntermediateField.subset_adjoin _ _ ⟨n, hn0, hn, hxn⟩`. Establish `h1` using `hg ⟨x, hmem⟩`. Rewrite `h1` using `[GlobalTheory.Pst.frobUr_pow_root b ⟨x, hmem⟩ n hn0 hn (Subtype.ext hxn), GlobalTheory.Pst.frobUr_pow_root a ⟨x, hmem⟩ n hn0 hn (Subtype.ext hxn)]`. Conclude with `h1`.

Establish `hc : ∀ k : ℕ, PreTilt.coeff 0 (y ^ k) = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) (z ^ k)` using `fun k => by`. Rewrite using `[map_pow, h0]`. Conclude with `(map_pow _ _ _).symm`. Establish `hz : ∀ k : ℕ, ((z ^ k : OC l) : ℂ_[l]) = ((x ^ k : Om l) : ℂ_[l])` using `fun k => by`. Rewrite using `[PadicComplex.coe_eq, map_pow, ← PadicComplex.coe_eq, ← hzx]`.

Simplify using the standard rewrite rules. Establish `hp : ∀ k : ℕ, (y ^ k) ^ l ^ m = y ^ k` using `fun k => by rw [← pow_mul, mul_comm, pow_mul, hy]`. Take `⟨y', h1, h2⟩` from `AI.actT_coeff g (y ^ l ^ b) 0 _ (hc _)`. Rewrite `h1` using `[hz, AI.actC_ext, hgx, ← hz]`. Use `GlobalTheory.UnramifiedCrys.eq_of_coeff_zero hm (by rw [← map_pow, hp]) (hp _) ?_` and prove the remaining obligations.

Rewrite using `[h2, hc, Subtype.ext h1]`.
-/
theorem UpperTheory.Ainf_action_tilt_fixed_of_frobenius_relation :
    ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (g : GQ l) (a b : ℕ), (∀ c : ↥(MaximalUnramifiedExtension l), g (((GlobalTheory.Pst.frobUr l ^ b) c : ↥(MaximalUnramifiedExtension l)) : Om l) = (((GlobalTheory.Pst.frobUr l ^ a) c : ↥(MaximalUnramifiedExtension l)) : Om l)) → ∀ (y : OCb l) (m : ℕ), 0 < m → y ^ l ^ m = y → AI.actT g (y ^ l ^ b) = y ^ l ^ a := by
  intro l hl P AI g a b hg y m hm hy
  obtain ⟨z, x, hzx, hx, h0⟩ := UpperTheory.V.Loc.tfab_lift y hm hy
  have hgx : g (x ^ l ^ b) = x ^ l ^ a := by
    by_cases hx0 : x = 0
    · rw [hx0, zero_pow (pow_ne_zero _ hl.out.ne_zero), zero_pow (pow_ne_zero _ hl.out.ne_zero), map_zero]
    obtain ⟨n, hn0, hn, hxn⟩ := UpperTheory.V.Loc.tfab_root hm hx hx0
    have hmem : x ∈ MaximalUnramifiedExtension l := IntermediateField.subset_adjoin _ _ ⟨n, hn0, hn, hxn⟩
    have h1 := hg ⟨x, hmem⟩
    rw [GlobalTheory.Pst.frobUr_pow_root b ⟨x, hmem⟩ n hn0 hn (Subtype.ext hxn),
      GlobalTheory.Pst.frobUr_pow_root a ⟨x, hmem⟩ n hn0 hn (Subtype.ext hxn)] at h1
    exact h1
  have hc : ∀ k : ℕ, PreTilt.coeff 0 (y ^ k) = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) (z ^ k) := fun k => by
    rw [map_pow, h0]
    exact (map_pow _ _ _).symm
  have hz : ∀ k : ℕ, ((z ^ k : OC l) : ℂ_[l]) = ((x ^ k : Om l) : ℂ_[l]) := fun k => by
    rw [PadicComplex.coe_eq, map_pow, ← PadicComplex.coe_eq, ← hzx]
    simp
  have hp : ∀ k : ℕ, (y ^ k) ^ l ^ m = y ^ k := fun k => by rw [← pow_mul, mul_comm, pow_mul, hy]
  obtain ⟨y', h1, h2⟩ := AI.actT_coeff g (y ^ l ^ b) 0 _ (hc _)
  rw [hz, AI.actC_ext, hgx, ← hz] at h1
  refine GlobalTheory.UnramifiedCrys.eq_of_coeff_zero hm (by rw [← map_pow, hp]) (hp _) ?_
  rw [h2, hc, Subtype.ext h1]
