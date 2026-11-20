import Formalism.SharpRestriction.GrowthBounds.RootWeights.StableSubspaceCompleteReducibility

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section v2dpAbs

variable {R : Type*} [CommRing R] {σ ι : Type*} [DecidableEq ι]

def dividedPowerExponent (src dst : ι → σ) (m : σ →₀ ℕ) (f : ι →₀ ℕ) : σ →₀ ℕ :=
  (m - Finsupp.mapDomain src f) + Finsupp.mapDomain dst f

def dividedPowerCoefficient (sg : ι → R) (src : ι → σ) (s : Finset ι) (m : σ →₀ ℕ) (f : ι →₀ ℕ) : R :=
  ∏ l ∈ s, sg l ^ (f l) * ((m (src l)).choose (f l) : R)

def dividedPowerMonomialTerm (sg : ι → R) (src dst : ι → σ) (s : Finset ι) (m : σ →₀ ℕ) (f : ι →₀ ℕ) : MvPolynomial σ R :=
  monomial (dividedPowerExponent src dst m f) (dividedPowerCoefficient sg src s m f)

def dividedPowerMonomialSum (sg : ι → R) (src dst : ι → σ) (s : Finset ι) (k : ℕ) (m : σ →₀ ℕ) : MvPolynomial σ R :=
  ∑ f ∈ Finset.finsuppAntidiag s k, dividedPowerMonomialTerm sg src dst s m f

def polarizationDerivation (sg : ι → R) (src dst : ι → σ) (l : ι) : MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  sg l • ((LinearMap.mulLeft R (X (dst l))) ∘ₗ (pderiv (src l)).toLinearMap)

/- English proof (translation)
Establish `h1 : Finsupp.mapDomain src f (src l) = f l` using `Finsupp.mapDomain_apply hs f l`. Establish `h2 : ∀ g : ι →₀ ℕ, Finsupp.mapDomain dst g (src l) = 0` using `fun g => Finsupp.mapDomain_of_notMem_range _ _ (by rintro ⟨l', h⟩; exact hd l l' h)`. Establish `hexp : Finsupp.single (dst l) 1 + (dividedPowerExponent src dst m f - Finsupp.single (src l) 1) = dividedPowerExponent src dst m (f + Finsupp.single l 1)`. Use extensionality with `v`. Simplify using `only [dividedPowerExponent, Finsupp.mapDomain_add, Finsupp.mapDomain_single, Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]`.

Distinguish the cases in `hv : src l = v`. Substitute `hv` using the available equality. Establish `h3` using `hd l l`. Simplify using `only [h1, h2, h3, if_true, if_false]`. Use linear arithmetic over natural numbers and integers.

Simplify using `only [hv, if_false]`. Use linear arithmetic over natural numbers and integers. Establish `he : dividedPowerExponent src dst m f (src l) = m (src l) - f l`. Simplify using `[dividedPowerExponent, h1, h2]`. Establish `hcf : sg l * (dividedPowerCoefficient sg src s m f * ((dividedPowerExponent src dst m f (src l) : ℕ) : R)) = ((f l + 1 : ℕ) : R) * dividedPowerCoefficient sg src s m (f + Finsupp.single l 1)`.

Rewrite using `[he]`. Unfold `dividedPowerCoefficient`. Rewrite using `[← Finset.mul_prod_erase s _ hl, ← Finset.mul_prod_erase s _ hl]`. Establish `h4 : ∏ x ∈ s.erase l, sg x ^ ((f + Finsupp.single l 1 : ι →₀ ℕ) x) * ((m (src x)).choose ((f + Finsupp.single l 1 : ι →₀ ℕ) x) : R) = ∏ x ∈ s.erase l, sg x ^ (f x) * ((m (src x)).choose (f x) : R)`. Apply `Finset.prod_congr rfl` to reduce the goal to its premises.

Introduce `x hx`. Establish `hx' : x ≠ l` using `(Finset.mem_erase.1 hx).1`. Simplify using `[hx'.symm]`. Rewrite using `[h4]`. Establish `hc : ((m (src l)).choose (f l + 1) : R) * ((f l + 1 : ℕ) : R) = ((m (src l)).choose (f l) : R) * ((m (src l) - f l : ℕ) : R)`.

Conclude with `congrArg (Nat.cast (R := R)) (Nat.choose_succ_right_eq (m (src l)) (f l))` after adjusting the coercions. Simplify using `only [Finsupp.add_apply, Finsupp.single_eq_same, pow_succ]`. Generalize the expression as in `(∏ x ∈ s.erase l, sg x ^ (f x) * ((m (src x)).choose (f x) : R)) = Er`. Take the linear combination `(-(sg l ^ f l * sg l * Er)) * hc`. Simplify using `only [polarizationDerivation, dividedPowerMonomialTerm, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe, pderiv_monomial]`.

Rewrite using `[X, monomial_mul, hexp, one_mul, smul_monomial, smul_eq_mul, hcf, ← nsmul_eq_mul, map_nsmul]`.
-/
theorem polarization_dividedPowerTerm (sg : ι → R) (src dst : ι → σ) (hs : Function.Injective src) (hd : ∀ l l', dst l' ≠ src l)
    (s : Finset ι) (m : σ →₀ ℕ) (f : ι →₀ ℕ) (l : ι) (hl : l ∈ s) :
    polarizationDerivation sg src dst l (dividedPowerMonomialTerm sg src dst s m f) =
      (f l + 1) • dividedPowerMonomialTerm sg src dst s m (f + Finsupp.single l 1) := by
  classical
  have h1 : Finsupp.mapDomain src f (src l) = f l := Finsupp.mapDomain_apply hs f l
  have h2 : ∀ g : ι →₀ ℕ, Finsupp.mapDomain dst g (src l) = 0 := fun g =>
    Finsupp.mapDomain_of_notMem_range _ _ (by rintro ⟨l', h⟩; exact hd l l' h)
  have hexp : Finsupp.single (dst l) 1 + (dividedPowerExponent src dst m f - Finsupp.single (src l) 1) =
      dividedPowerExponent src dst m (f + Finsupp.single l 1) := by
    ext v
    simp only [dividedPowerExponent, Finsupp.mapDomain_add, Finsupp.mapDomain_single, Finsupp.add_apply,
      Finsupp.tsub_apply, Finsupp.single_apply]
    by_cases hv : src l = v
    · subst hv
      have h3 := hd l l
      simp only [h1, h2, h3, if_true, if_false]
      omega
    · simp only [hv, if_false]
      omega
  have he : dividedPowerExponent src dst m f (src l) = m (src l) - f l := by
    simp [dividedPowerExponent, h1, h2]
  have hcf : sg l * (dividedPowerCoefficient sg src s m f * ((dividedPowerExponent src dst m f (src l) : ℕ) : R)) =
      ((f l + 1 : ℕ) : R) * dividedPowerCoefficient sg src s m (f + Finsupp.single l 1) := by
    rw [he]
    unfold dividedPowerCoefficient
    rw [← Finset.mul_prod_erase s _ hl, ← Finset.mul_prod_erase s _ hl]
    have h4 : ∏ x ∈ s.erase l, sg x ^ ((f + Finsupp.single l 1 : ι →₀ ℕ) x) *
        ((m (src x)).choose ((f + Finsupp.single l 1 : ι →₀ ℕ) x) : R) =
        ∏ x ∈ s.erase l, sg x ^ (f x) * ((m (src x)).choose (f x) : R) := by
      apply Finset.prod_congr rfl
      intro x hx
      have hx' : x ≠ l := (Finset.mem_erase.1 hx).1
      simp [hx'.symm]
    rw [h4]
    have hc : ((m (src l)).choose (f l + 1) : R) * ((f l + 1 : ℕ) : R) =
        ((m (src l)).choose (f l) : R) * ((m (src l) - f l : ℕ) : R) := by
      exact_mod_cast congrArg (Nat.cast (R := R)) (Nat.choose_succ_right_eq (m (src l)) (f l))
    simp only [Finsupp.add_apply, Finsupp.single_eq_same, pow_succ]
    generalize (∏ x ∈ s.erase l, sg x ^ (f x) * ((m (src x)).choose (f x) : R)) = Er
    linear_combination (-(sg l ^ f l * sg l * Er)) * hc
  simp only [polarizationDerivation, dividedPowerMonomialTerm, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
    Derivation.coeFn_coe, pderiv_monomial]
  rw [X, monomial_mul, hexp, one_mul, smul_monomial, smul_eq_mul, hcf, ← nsmul_eq_mul, map_nsmul]

/- English proof (translation)
Establish `hL : ∑ g ∈ Finset.finsuppAntidiag s (k + 1), (g l) • F g = ∑ g ∈ (Finset.finsuppAntidiag s (k + 1)).filter (fun g => g l ≠ 0), (g l) • F g`. Use `(Finset.sum_filter_of_ne ?_).symm` and prove the remaining obligations. Introduce `g _ h h0`. Apply `h` to reduce the goal to its premises. Simplify using `[h0]`.

Rewrite using `[hL]`. Use `symm`. Apply `Finset.sum_nbij' (fun f => f + Finsupp.single l 1) (fun g => g - Finsupp.single l 1)` to reduce the goal to its premises. Introduce `f hf`. Simplify using `only [Finset.mem_coe, Finset.mem_filter, Finset.mem_finsuppAntidiag] at hf ⊢`.

Use `⟨⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← hf.1]`. Simplify using `[Finset.sum_add_distrib, Finsupp.single_apply, hl]`. Introduce `x hx`. Break down `Finset.mem_union.1 (Finsupp.support_add hx) with h | h` into its components or cases.

Conclude with `hf.2 h`. Rewrite using `[Finset.mem_singleton.1 (Finsupp.support_single_subset h)]`. Conclude with `hl`. Simplify using the standard rewrite rules. Introduce `g hg`.

Simplify using `only [Finset.mem_coe, Finset.mem_filter, Finset.mem_finsuppAntidiag] at hg ⊢`. Establish `hle : Finsupp.single l 1 ≤ g` using `Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hg.2)`. Establish `hg' : g - Finsupp.single l 1 + Finsupp.single l 1 = g` using `tsub_add_cancel_of_le hle`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `hsum : ∑ x ∈ s, (g - Finsupp.single l 1 : ι →₀ ℕ) x + ∑ x ∈ s, (Finsupp.single l 1 : ι →₀ ℕ) x = ∑ x ∈ s, g x`.

Rewrite using `[← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl (fun x _ => by rw [← Finsupp.add_apply, hg'])`. Establish `h1 : ∑ x ∈ s, (Finsupp.single l 1 : ι →₀ ℕ) x = 1`. Simplify using `[Finsupp.single_apply, hl]`. Establish `h2 : ∑ x ∈ s, g x = k + 1` using `hg.1.1`.

Establish `h3 : ∑ x ∈ s, (g - Finsupp.single l 1 : ι →₀ ℕ) x = k` using `by omega`. Conclude with `h3`. Introduce `x hx`. Apply `hg.1.2` to reduce the goal to its premises. Rewrite `hx`, the goal using `[Finsupp.mem_support_iff]`.

Introduce `h0`. Apply `hx` to reduce the goal to its premises. Simplify using `[h0]`. Introduce `f _`. Simplify using the standard rewrite rules.

Introduce `g hg`. Simplify using `only [Finset.mem_coe, Finset.mem_filter, Finset.mem_finsuppAntidiag] at hg`. Conclude with `tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hg.2))`. Introduce `f _`. Simplify using the standard rewrite rules.
-/
theorem finsuppAntidiag_succ_reindex {N : Type*} [AddCommMonoid N] (s : Finset ι) (k : ℕ) (l : ι) (hl : l ∈ s)
    (F : (ι →₀ ℕ) → N) :
    ∑ g ∈ Finset.finsuppAntidiag s (k + 1), (g l) • F g =
      ∑ f ∈ Finset.finsuppAntidiag s k, (f l + 1) • F (f + Finsupp.single l 1) := by
  have hL : ∑ g ∈ Finset.finsuppAntidiag s (k + 1), (g l) • F g =
      ∑ g ∈ (Finset.finsuppAntidiag s (k + 1)).filter (fun g => g l ≠ 0), (g l) • F g := by
    refine (Finset.sum_filter_of_ne ?_).symm
    intro g _ h h0
    apply h
    simp [h0]
  rw [hL]
  symm
  apply Finset.sum_nbij' (fun f => f + Finsupp.single l 1) (fun g => g - Finsupp.single l 1)
  · intro f hf
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_finsuppAntidiag] at hf ⊢
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [← hf.1]
      simp [Finset.sum_add_distrib, Finsupp.single_apply, hl]
    · intro x hx
      rcases Finset.mem_union.1 (Finsupp.support_add hx) with h | h
      · exact hf.2 h
      · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset h)]
        exact hl
    · simp
  · intro g hg
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_finsuppAntidiag] at hg ⊢
    have hle : Finsupp.single l 1 ≤ g := Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hg.2)
    have hg' : g - Finsupp.single l 1 + Finsupp.single l 1 = g := tsub_add_cancel_of_le hle
    refine ⟨?_, ?_⟩
    · have hsum : ∑ x ∈ s, (g - Finsupp.single l 1 : ι →₀ ℕ) x + ∑ x ∈ s, (Finsupp.single l 1 : ι →₀ ℕ) x =
          ∑ x ∈ s, g x := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun x _ => by rw [← Finsupp.add_apply, hg'])
      have h1 : ∑ x ∈ s, (Finsupp.single l 1 : ι →₀ ℕ) x = 1 := by
        simp [Finsupp.single_apply, hl]
      have h2 : ∑ x ∈ s, g x = k + 1 := hg.1.1
      have h3 : ∑ x ∈ s, (g - Finsupp.single l 1 : ι →₀ ℕ) x = k := by omega
      exact h3
    · intro x hx
      apply hg.1.2
      rw [Finsupp.mem_support_iff] at hx ⊢
      intro h0
      apply hx
      simp [h0]
  · intro f _
    simp
  · intro g hg
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_finsuppAntidiag] at hg
    exact tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hg.2))
  · intro f _
    simp

/- English proof (translation)
Establish `h1 : (∑ l ∈ s, polarizationDerivation sg src dst l) (dividedPowerMonomialSum sg src dst s k m) = ∑ l ∈ s, ∑ f ∈ Finset.finsuppAntidiag s k, polarizationDerivation sg src dst l (dividedPowerMonomialTerm sg src dst s m f)`. Rewrite using `[LinearMap.sum_apply]`. Conclude with `Finset.sum_congr rfl (fun l _ => map_sum _ _ _)`. Establish `h2 : ∀ l ∈ s, ∑ f ∈ Finset.finsuppAntidiag s k, polarizationDerivation sg src dst l (dividedPowerMonomialTerm sg src dst s m f) = ∑ g ∈ Finset.finsuppAntidiag s (k + 1), (g l) • dividedPowerMonomialTerm sg src dst s m g`. Introduce `l hl`.

Rewrite using `[finsuppAntidiag_succ_reindex s k l hl (dividedPowerMonomialTerm sg src dst s m)]`. Conclude with `Finset.sum_congr rfl (fun f _ => polarization_dividedPowerTerm sg src dst hs hd s m f l hl)`. Rewrite using `[h1, Finset.sum_congr rfl h2, Finset.sum_comm]`. Unfold `dividedPowerMonomialSum`. Rewrite using `[Finset.smul_sum]`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `g hg`. Rewrite using `[← Finset.sum_smul, (Finset.mem_finsuppAntidiag.1 hg).1]`.
-/
theorem polarization_dividedPowerSum_succ (sg : ι → R) (src dst : ι → σ) (hs : Function.Injective src) (hd : ∀ l l', dst l' ≠ src l)
    (s : Finset ι) (m : σ →₀ ℕ) (k : ℕ) :
    (∑ l ∈ s, polarizationDerivation sg src dst l) (dividedPowerMonomialSum sg src dst s k m) = (k + 1) • dividedPowerMonomialSum sg src dst s (k + 1) m := by
  have h1 : (∑ l ∈ s, polarizationDerivation sg src dst l) (dividedPowerMonomialSum sg src dst s k m) =
      ∑ l ∈ s, ∑ f ∈ Finset.finsuppAntidiag s k, polarizationDerivation sg src dst l (dividedPowerMonomialTerm sg src dst s m f) := by
    rw [LinearMap.sum_apply]
    exact Finset.sum_congr rfl (fun l _ => map_sum _ _ _)
  have h2 : ∀ l ∈ s, ∑ f ∈ Finset.finsuppAntidiag s k, polarizationDerivation sg src dst l (dividedPowerMonomialTerm sg src dst s m f) =
      ∑ g ∈ Finset.finsuppAntidiag s (k + 1), (g l) • dividedPowerMonomialTerm sg src dst s m g := by
    intro l hl
    rw [finsuppAntidiag_succ_reindex s k l hl (dividedPowerMonomialTerm sg src dst s m)]
    exact Finset.sum_congr rfl (fun f _ => polarization_dividedPowerTerm sg src dst hs hd s m f l hl)
  rw [h1, Finset.sum_congr rfl h2, Finset.sum_comm]
  unfold dividedPowerMonomialSum
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro g hg
  rw [← Finset.sum_smul, (Finset.mem_finsuppAntidiag.1 hg).1]

/- English proof (translation)
Simplify using `[dividedPowerMonomialSum, dividedPowerMonomialTerm, dividedPowerExponent, dividedPowerCoefficient, Finset.finsuppAntidiag_zero]`.
-/
theorem dividedPowerMonomialSum_zero (sg : ι → R) (src dst : ι → σ) (s : Finset ι) (m : σ →₀ ℕ) :
    dividedPowerMonomialSum sg src dst s 0 m = monomial m 1 := by
  simp [dividedPowerMonomialSum, dividedPowerMonomialTerm, dividedPowerExponent, dividedPowerCoefficient, Finset.finsuppAntidiag_zero]

end v2dpAbs

end Formalism.MainNotions.G.GLWeightTheory
