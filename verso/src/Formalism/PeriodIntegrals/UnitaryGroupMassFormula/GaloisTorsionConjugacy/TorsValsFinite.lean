import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaloisTorsionConjugacy.IncAdjInclusion
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaloisTorsionConjugacy.WpOnto
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaloisTorsionConjugacy.AddDbl

noncomputable section

namespace PI.GalTorsConj.W

open Polynomial Formalism.L2.Th1.F

/- English proof (translation)
Introduce `ω hω`. Rewrite using `[← nsmul_eq_mul]`. Conclude with `nsmul_mem hω n`.
-/
theorem mulStable_nat (L : PeriodPair) (n : ℕ) : MulStable L (n : ℂ) := by
  intro ω hω
  rw [← nsmul_eq_mul]
  exact nsmul_mem hω n

/- English proof (translation)
Establish `hα : (n : ℂ) ≠ 0` using `by exact_mod_cast hn.ne'`. Take `⟨S, hS⟩` from `kerRepsExist L (n : ℂ) hα (mulStable_nat L n)`. Use `(S.finite_toSet.image L.weierstrassP).subset ?_` and prove the remaining obligations. Introduce and unpack `v ⟨s, h1, h2, rfl⟩`. Take `⟨P, hP, hsP⟩` from `hS.2.2 s h1 h2`.

Use `⟨P, hP, ?_⟩` and prove the remaining obligations. Establish `e : s = P + (s - P)` using `by ring`. Rewrite using `[e, wp_add_mem L P hsP]`.
-/
theorem tors_vals_finite (L : PeriodPair) (n : ℕ) (hn : 0 < n) :
    {v : ℂ | ∃ s, (n : ℂ) * s ∈ L.lattice ∧ s ∉ L.lattice ∧ L.weierstrassP s = v}.Finite := by
  have hα : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  obtain ⟨S, hS⟩ := kerRepsExist L (n : ℂ) hα (mulStable_nat L n)
  refine (S.finite_toSet.image L.weierstrassP).subset ?_
  rintro v ⟨s, h1, h2, rfl⟩
  obtain ⟨P, hP, hsP⟩ := hS.2.2 s h1 h2
  refine ⟨P, hP, ?_⟩
  have e : s = P + (s - P) := by ring
  rw [e, wp_add_mem L P hsP]

/- English proof (translation)
Establish `hk : Transcendental M (x + k)`. Introduce `halg`. Apply `hx` to reduce the goal to its premises. Establish `h2 : IsIntegral M (k : ℂ)`. Simplify using `using (isIntegral_algebraMap (R := M) (A := ℂ) (x := (k : M)))`.

Simplify using `using (halg.isIntegral.sub h2).isAlgebraic`. Establish `hφ : nonZeroDivisors M[X] ≤ (nonZeroDivisors ℂ).comap (aeval (x + k) : M[X] →ₐ[M] ℂ)`. Introduce `p hp`. Simplify using `only [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero] at hp ⊢`. Introduce `h0`.

Conclude with `hk ⟨p, hp, h0⟩`. Use `⟨(RatFunc.liftAlgHom (aeval (x + k) : M[X] →ₐ[M] ℂ) hφ).comp (RatFunc.algEquivOfTranscendental x hx).symm.toAlgHom, ?_⟩` and prove the remaining obligations. Rewrite using `[AlgHom.comp_apply]`. Express the relevant statement in the definitionally equal form `RatFunc.liftAlgHom _ hφ ((RatFunc.algEquivOfTranscendental x hx).symm _) = _`. Rewrite using `[RatFunc.algEquivOfTranscendental_symm_gen]`.

Use `RatFunc.liftAlgHom_apply_div (aeval (x + k) : M[X] →ₐ[M] ℂ) hφ X 1` as an intermediate fact. Simplify using `using this`.
-/
theorem shift_emb (M : IntermediateField ℚ ℂ) (x : ℂ) (hx : Transcendental M x) (k : ℕ) :
    ∃ σ : IntermediateField.adjoin M {x} →ₐ[M] ℂ,
      σ (IntermediateField.AdjoinSimple.gen M x) = x + k := by
  have hk : Transcendental M (x + k) := by
    intro halg
    apply hx
    have h2 : IsIntegral M (k : ℂ) := by
      simpa using (isIntegral_algebraMap (R := M) (A := ℂ) (x := (k : M)))
    simpa using (halg.isIntegral.sub h2).isAlgebraic
  have hφ : nonZeroDivisors M[X] ≤ (nonZeroDivisors ℂ).comap (aeval (x + k) : M[X] →ₐ[M] ℂ) := by
    intro p hp
    simp only [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero] at hp ⊢
    intro h0
    exact hk ⟨p, hp, h0⟩
  refine ⟨(RatFunc.liftAlgHom (aeval (x + k) : M[X] →ₐ[M] ℂ) hφ).comp
    (RatFunc.algEquivOfTranscendental x hx).symm.toAlgHom, ?_⟩
  rw [AlgHom.comp_apply]
  change RatFunc.liftAlgHom _ hφ ((RatFunc.algEquivOfTranscendental x hx).symm _) = _
  rw [RatFunc.algEquivOfTranscendental_symm_gen]
  have := RatFunc.liftAlgHom_apply_div (aeval (x + k) : M[X] →ₐ[M] ℂ) hφ X 1
  simpa using this

def rsHom (M : IntermediateField ℚ ℂ) (E : IntermediateField M ℂ) (σ : E →ₐ[M] ℂ) :
    E.restrictScalars ℚ →ₐ[ℚ] ℂ :=
  RingHom.toRatAlgHom
    { toFun := fun z => σ ⟨z, z.2⟩
      map_one' := σ.map_one
      map_mul' := fun a b => σ.map_mul ⟨a, a.2⟩ ⟨b, b.2⟩
      map_zero' := σ.map_zero
      map_add' := fun a b => σ.map_add ⟨a, a.2⟩ ⟨b, b.2⟩ }

/- English proof (translation)
Establish `hx'` using `mem_algebraicClosure_iff.mpr hx`. Establish `ha'` using `mem_algebraicClosure_iff.mpr ha`. Establish `hb'` using `mem_algebraicClosure_iff.mpr hb`. Establish `h4 : (4 : ℂ) ∈ algebraicClosure F ℂ`. Use `natCast_mem (algebraicClosure F ℂ) 4` as an intermediate fact.

Conclude with `this` after adjusting the coercions. Establish `hw : 4 * x ^ 3 - a * x - b ∈ algebraicClosure F ℂ` using `sub_mem (sub_mem (mul_mem h4 (pow_mem hx' 3)) (mul_mem ha' hx')) hb'`. Rewrite `hw` using `[← hsq]`. Conclude with `IsAlgebraic.of_pow two_pos (mem_algebraicClosure_iff.mp hw)`.
-/
theorem alg_of_sq {F : Type*} [Field F] [Algebra F ℂ] {x y a b : ℂ}
    (hsq : y ^ 2 = 4 * x ^ 3 - a * x - b)
    (hx : IsAlgebraic F x) (ha : IsAlgebraic F a) (hb : IsAlgebraic F b) : IsAlgebraic F y := by
  have hx' := mem_algebraicClosure_iff.mpr hx
  have ha' := mem_algebraicClosure_iff.mpr ha
  have hb' := mem_algebraicClosure_iff.mpr hb
  have h4 : (4 : ℂ) ∈ algebraicClosure F ℂ := by
    have := natCast_mem (algebraicClosure F ℂ) 4
    exact_mod_cast this
  have hw : 4 * x ^ 3 - a * x - b ∈ algebraicClosure F ℂ :=
    sub_mem (sub_mem (mul_mem h4 (pow_mem hx' 3)) (mul_mem ha' hx')) hb'
  rw [← hsq] at hw
  exact IsAlgebraic.of_pow two_pos (mem_algebraicClosure_iff.mp hw)

/- English proof (translation)
Assume the negation of the conclusion as `htr`. Apply `(tors_vals_finite L n hn).not_infinite` to reduce the goal to its premises. Use `Set.infinite_of_injective_forall_mem (f := fun k : ℕ => L.weierstrassP t + k) ?_ ?_` and prove the remaining obligations. Introduce `a b hab`. Simplify using `only at hab`.

Conclude with `add_left_cancel hab` after adjusting the coercions. Introduce `k`. Take `⟨σ, hσ⟩` from `shift_emb M (L.weierstrassP t) htr k`. Set `Mx : IntermediateField ℚ ℂ` to `(IntermediateField.adjoin M {L.weierstrassP t}).restrictScalars ℚ`. Establish `hMx : ∀ z ∈ M, z ∈ Mx` using `fun z hz => (IntermediateField.adjoin M {L.weierstrassP t}).algebraMap_mem ⟨z, hz⟩`.

Establish `hxMx : L.weierstrassP t ∈ Mx` using `IntermediateField.mem_adjoin_simple_self M _`. Set `M₂ : IntermediateField ℚ ℂ` to `(algebraicClosure Mx ℂ).restrictScalars ℚ`. Establish `hle : Mx ≤ M₂` using `fun z hz => by show z ∈ algebraicClosure Mx ℂ`. Conclude with `mem_algebraicClosure_iff.mpr (isAlgebraic_algebraMap (⟨z, hz⟩ : Mx))`. Establish `halg₂ : ∀ z ∈ M₂, IsAlgebraic Mx z` using `fun z hz => mem_algebraicClosure_iff.mp hz`.

Take `⟨ρ₂, hρ₂⟩` from `extRho Mx M₂ hle halg₂ (rsHom M _ σ)`. Establish `hg2₂ : L.g₂ ∈ M₂` using `hle (hMx _ hg2)`. Establish `hg3₂ : L.g₃ ∈ M₂` using `hle (hMx _ hg3)`. Establish `hx₂ : L.weierstrassP t ∈ M₂` using `hle hxMx`. Establish `hy₂ : L.derivWeierstrassP t ∈ M₂`.

Establish `hsq : L.derivWeierstrassP t ^ 2 = 4 * L.weierstrassP t ^ 3 - L.g₂ * L.weierstrassP t - L.g₃`. Establish `e` using `L.derivWeierstrassP_sq t ht`. Take the linear combination `e`. Use `show L.derivWeierstrassP t ∈ algebraicClosure Mx ℂ`. Conclude with `mem_algebraicClosure_iff.mpr (alg_of_sq hsq (isAlgebraic_algebraMap (⟨_, hxMx⟩ : Mx)) (isAlgebraic_algebraMap (⟨_, hMx _ hg2⟩ : Mx)) (isAlgebraic_algebraMap (⟨_, hMx _ hg3⟩ : Mx)))`.

Establish `hfix : ∀ z (hz : z ∈ M) (hz₂ : z ∈ M₂), ρ₂ ⟨z, hz₂⟩ = z`. Introduce `z hz hz₂`. Establish `e1 : (⟨z, hz₂⟩ : M₂) = IntermediateField.inclusion hle ⟨z, hMx z hz⟩` using `rfl`. Rewrite using `[e1, hρ₂]`. Conclude with `σ.commutes ⟨z, hz⟩`.

Establish `hρx : ρ₂ ⟨_, hx₂⟩ = L.weierstrassP t + k`. Establish `e1 : (⟨_, hx₂⟩ : M₂) = IntermediateField.inclusion hle ⟨_, hxMx⟩` using `rfl`. Rewrite using `[e1, hρ₂]`. Conclude with `hσ`. Establish `hg2' : L.g₂ = ρ₂ ⟨_, hg2₂⟩` using `(hfix _ hg2 hg2₂).symm`.

Establish `hg3' : L.g₃ = ρ₂ ⟨_, hg3₂⟩` using `(hfix _ hg3 hg3₂).symm`. Take `⟨t₂, hst⟩` from `st_exists (L := L) (L' := L) (M := M₂) (ρ := ρ₂) pOnto hg2₂ hg3₂ hg2' hg3' t (Or.inr ⟨hx₂, hy₂⟩)`. Establish `hn₂` using `(st_mem_iff (st_nsmul addLaw dblLaw hg2₂ hg2' hst n)).mp hnt`. Break down `hst with ⟨h1, -⟩ | ⟨-, h2, hx', hy', e1, -⟩` into its components or cases. Conclude with `absurd h1 ht`.

Use `⟨t₂, hn₂, h2, ?_⟩` and prove the remaining obligations. Rewrite using `[e1]`. Conclude with `hρx`.
-/
theorem wp_isAlgebraic (L : PeriodPair) (M : IntermediateField ℚ ℂ) (hg2 : L.g₂ ∈ M)
    (hg3 : L.g₃ ∈ M) (n : ℕ) (t : ℂ) (hn : 0 < n) (hnt : (n : ℂ) * t ∈ L.lattice)
    (ht : t ∉ L.lattice) : IsAlgebraic M (L.weierstrassP t) := by
  by_contra htr
  apply (tors_vals_finite L n hn).not_infinite
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => L.weierstrassP t + k) ?_ ?_
  · intro a b hab
    simp only at hab
    exact_mod_cast add_left_cancel hab
  intro k
  obtain ⟨σ, hσ⟩ := shift_emb M (L.weierstrassP t) htr k
  let Mx : IntermediateField ℚ ℂ := (IntermediateField.adjoin M {L.weierstrassP t}).restrictScalars ℚ
  have hMx : ∀ z ∈ M, z ∈ Mx := fun z hz =>
    (IntermediateField.adjoin M {L.weierstrassP t}).algebraMap_mem ⟨z, hz⟩
  have hxMx : L.weierstrassP t ∈ Mx := IntermediateField.mem_adjoin_simple_self M _
  let M₂ : IntermediateField ℚ ℂ := (algebraicClosure Mx ℂ).restrictScalars ℚ
  have hle : Mx ≤ M₂ := fun z hz => by
    show z ∈ algebraicClosure Mx ℂ
    exact mem_algebraicClosure_iff.mpr (isAlgebraic_algebraMap (⟨z, hz⟩ : Mx))
  have halg₂ : ∀ z ∈ M₂, IsAlgebraic Mx z := fun z hz => mem_algebraicClosure_iff.mp hz
  obtain ⟨ρ₂, hρ₂⟩ := extRho Mx M₂ hle halg₂ (rsHom M _ σ)
  have hg2₂ : L.g₂ ∈ M₂ := hle (hMx _ hg2)
  have hg3₂ : L.g₃ ∈ M₂ := hle (hMx _ hg3)
  have hx₂ : L.weierstrassP t ∈ M₂ := hle hxMx
  have hy₂ : L.derivWeierstrassP t ∈ M₂ := by
    have hsq : L.derivWeierstrassP t ^ 2
        = 4 * L.weierstrassP t ^ 3 - L.g₂ * L.weierstrassP t - L.g₃ := by
      have e := L.derivWeierstrassP_sq t ht
      linear_combination e
    show L.derivWeierstrassP t ∈ algebraicClosure Mx ℂ
    exact mem_algebraicClosure_iff.mpr (alg_of_sq hsq
      (isAlgebraic_algebraMap (⟨_, hxMx⟩ : Mx))
      (isAlgebraic_algebraMap (⟨_, hMx _ hg2⟩ : Mx))
      (isAlgebraic_algebraMap (⟨_, hMx _ hg3⟩ : Mx)))
  have hfix : ∀ z (hz : z ∈ M) (hz₂ : z ∈ M₂), ρ₂ ⟨z, hz₂⟩ = z := by
    intro z hz hz₂
    have e1 : (⟨z, hz₂⟩ : M₂) = IntermediateField.inclusion hle ⟨z, hMx z hz⟩ := rfl
    rw [e1, hρ₂]
    exact σ.commutes ⟨z, hz⟩
  have hρx : ρ₂ ⟨_, hx₂⟩ = L.weierstrassP t + k := by
    have e1 : (⟨_, hx₂⟩ : M₂) = IntermediateField.inclusion hle ⟨_, hxMx⟩ := rfl
    rw [e1, hρ₂]
    exact hσ
  have hg2' : L.g₂ = ρ₂ ⟨_, hg2₂⟩ := (hfix _ hg2 hg2₂).symm
  have hg3' : L.g₃ = ρ₂ ⟨_, hg3₂⟩ := (hfix _ hg3 hg3₂).symm
  obtain ⟨t₂, hst⟩ := st_exists (L := L) (L' := L) (M := M₂) (ρ := ρ₂) pOnto hg2₂ hg3₂ hg2' hg3' t
    (Or.inr ⟨hx₂, hy₂⟩)
  have hn₂ := (st_mem_iff (st_nsmul addLaw dblLaw hg2₂ hg2' hst n)).mp hnt
  rcases hst with ⟨h1, -⟩ | ⟨-, h2, hx', hy', e1, -⟩
  · exact absurd h1 ht
  · refine ⟨t₂, hn₂, h2, ?_⟩
    rw [e1]
    exact hρx

end PI.GalTorsConj.W

end
