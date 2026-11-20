import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockHarmonicSplitting.FockInnerSelfReNonneg

noncomputable section

open MvPolynomial

namespace PI.FHS

variable {σ : Type*}

def FockV (σ : Type*) : Type _ := MvPolynomial σ ℂ

instance : AddCommGroup (FockV σ) := inferInstanceAs (AddCommGroup (MvPolynomial σ ℂ))

instance : Module ℂ (FockV σ) := inferInstanceAs (Module ℂ (MvPolynomial σ ℂ))

@[instance_reducible]
def fockCore : InnerProductSpace.Core ℂ (FockV σ) where
  inner P Q := FockH1Action.fockInner (σ := σ) P Q
  conj_inner_symm x y := fockInner_conj (σ := σ) x y
  re_inner_nonneg x := by simpa using fockInner_self_re_nonneg (σ := σ) x
  add_left x y z := fockInner_add_left (σ := σ) x y z
  smul_left x y r := fockInner_smul_left (σ := σ) r x y
  definite _ h := fockInner_self_eq_zero (σ := σ) h

/- English proof (translation)
Use `first`. Consider the case `exact inferInstance`. Consider the case `(let c : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun _ => n)`. Establish `hS : (Set.Icc (0 : σ →₀ ℕ) c).Finite` using `Set.finite_Icc 0 c`. Establish `hle : FockH1Action.homog σ n ≤ Submodule.span ℂ ((fun d => MvPolynomial.monomial d (1 : ℂ)) '' Set.Icc (0 : σ →₀ ℕ) c)`.

Introduce `p hp`. Establish `hph : p.IsHomogeneous n` using `(MvPolynomial.mem_homogeneousSubmodule n p).1 hp`. Rewrite using `[p.as_sum]`. Use `Submodule.sum_mem _ (fun d hd => ?_)` and prove the remaining obligations. Establish `hmono : MvPolynomial.monomial d (MvPolynomial.coeff d p) = MvPolynomial.coeff d p • MvPolynomial.monomial d (1 : ℂ)` using `by first`.

Consider the case `simp [MvPolynomial.smul_monomial]`. Consider the case `rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]`. Rewrite using `[hmono]`. Apply the tactic sequence `refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨d, ⟨by first | exact zero_le | exact bot_le | simp, ?_⟩, rfl⟩)`. Establish `hp0 : p ≠ 0`.

Introduce and unpack `rfl`. Simplify using `at hd`. Establish `htd : p.totalDegree ≤ n` using `by first`. Consider the case `exact hph.totalDegree_le`. Consider the case `exact (hph.totalDegree hp0).le`.

Establish `hsum : (d.sum fun _ e => e) ≤ n` using `(MvPolynomial.le_totalDegree hd).trans htd`. Introduce `i`. Establish `h1 : d i ≤ d.sum (fun _ e => e)`. Distinguish the cases in `hi : i ∈ d.support`. Conclude with `Finset.single_le_sum (f := fun j => d j) (fun j _ => Nat.zero_le _) hi`.

Rewrite `hi` using `[Finsupp.mem_support_iff, not_not]`. Rewrite using `[hi]`. Conclude with `Nat.zero_le _`. Simplify `h1.trans hsum` using `[c]`. Use `haveI : FiniteDimensional ℂ (Submodule.span ℂ ((fun d => MvPolynomial.monomial d (1 : ℂ)) '' Set.Icc (0 : σ →₀ ℕ) c)) := FiniteDimensional.span_of_finite ℂ (hS.image _)`.

Conclude with `Submodule.finiteDimensional_of_le hle)`.
-/
private lemma finiteDimensional_homog' [Fintype σ] (n : ℕ) :
    FiniteDimensional ℂ (FockH1Action.homog σ n) := by
  classical
  first
  | exact inferInstance
  | (let c : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun _ => n)
     have hS : (Set.Icc (0 : σ →₀ ℕ) c).Finite := Set.finite_Icc 0 c
     have hle : FockH1Action.homog σ n ≤ Submodule.span ℂ
         ((fun d => MvPolynomial.monomial d (1 : ℂ)) '' Set.Icc (0 : σ →₀ ℕ) c) := by
       intro p hp
       have hph : p.IsHomogeneous n := (MvPolynomial.mem_homogeneousSubmodule n p).1 hp
       rw [p.as_sum]
       refine Submodule.sum_mem _ (fun d hd => ?_)
       have hmono : MvPolynomial.monomial d (MvPolynomial.coeff d p)
           = MvPolynomial.coeff d p • MvPolynomial.monomial d (1 : ℂ) := by
         first
         | simp [MvPolynomial.smul_monomial]
         | rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
       rw [hmono]
       refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨d, ⟨by first | exact zero_le | exact bot_le | simp, ?_⟩, rfl⟩)
       have hp0 : p ≠ 0 := by
         rintro rfl
         simp at hd
       have htd : p.totalDegree ≤ n := by
         first
         | exact hph.totalDegree_le
         | exact (hph.totalDegree hp0).le
       have hsum : (d.sum fun _ e => e) ≤ n := (MvPolynomial.le_totalDegree hd).trans htd
       intro i
       have h1 : d i ≤ d.sum (fun _ e => e) := by
         by_cases hi : i ∈ d.support
         · exact Finset.single_le_sum (f := fun j => d j) (fun j _ => Nat.zero_le _) hi
         · rw [Finsupp.mem_support_iff, not_not] at hi
           rw [hi]
           exact Nat.zero_le _
       simpa [c] using h1.trans hsum
     haveI : FiniteDimensional ℂ (Submodule.span ℂ
         ((fun d => MvPolynomial.monomial d (1 : ℂ)) '' Set.Icc (0 : σ →₀ ℕ) c)) :=
       FiniteDimensional.span_of_finite ℂ (hS.image _)
     exact Submodule.finiteDimensional_of_le hle)

set_option maxHeartbeats 800000 in

/- English proof (translation)
Use `haveI : FiniteDimensional ℂ (FockH1Action.homog σ n) := finiteDimensional_homog' n`. Establish `hfin : FiniteDimensional ℂ K` using `Submodule.finiteDimensional_of_le hK`. Set `K' : Submodule ℂ (FockV σ)` to `K`. Use `haveI : FiniteDimensional ℂ K' := hfin`. Use `letI : NormedAddCommGroup (FockV σ) := (fockCore (σ := σ)).toNormedAddCommGroup`.

Use `letI : InnerProductSpace ℂ (FockV σ) := by first`. Consider the case `exact InnerProductSpace.ofCore (fockCore (σ := σ)).toCore`. Consider the case `exact InnerProductSpace.ofCore (fockCore (σ := σ)).toPreInnerProductSpaceCore`. Consider the case `exact InnerProductSpace.ofCore (fockCore (σ := σ))`. Use `haveI hproj : K'.HasOrthogonalProjection := inferInstance`.

Set `g : FockV σ` to `f`. Set `P` to `K'.orthogonalProjection g`. Establish `hP : ∀ x ∈ K', inner ℂ x (g - (P : FockV σ)) = 0` using `by first`. Consider the case `exact K'.orthogonalProjection_inner_eq_zero g`. Consider the case `exact fun x hx => (K'.mem_orthogonal _).1 (K'.sub_orthogonalProjection_mem_orthogonal g) x hx`.

Consider the case `exact fun x hx => (K'.mem_orthogonal _).1 (K'.sub_starProjection_mem_orthogonal g) x hx`. Establish `key : ∀ x y : FockV σ, inner ℂ x y = FockH1Action.fockInner (σ` using `σ) x y := fun _ _ => rfl`. Set `q : MvPolynomial σ ℂ` to `(P : FockV σ)`. Establish `hsub : g - (P : FockV σ) = (show FockV σ from f - q)` using `rfl`. Use `⟨(P : FockV σ), P.2, fun x hx => ?_⟩` and prove the remaining obligations.

Establish `h1` using `hP x hx`. Rewrite `h1` using `[hsub]`. Establish `h2 : FockH1Action.fockInner (σ` using `σ) x (f - q) = 0 := (key x (f - q)).symm.trans h1`. Conclude with `h2`.
-/
lemma exists_orth [Fintype σ] (K : Submodule ℂ (MvPolynomial σ ℂ)) (n : ℕ)
    (hK : K ≤ FockH1Action.homog σ n) (f : MvPolynomial σ ℂ) :
    ∃ y ∈ K, ∀ x ∈ K, FockH1Action.fockInner x (f - y) = 0 := by
  classical
  haveI : FiniteDimensional ℂ (FockH1Action.homog σ n) := finiteDimensional_homog' n
  have hfin : FiniteDimensional ℂ K := Submodule.finiteDimensional_of_le hK
  let K' : Submodule ℂ (FockV σ) := K
  haveI : FiniteDimensional ℂ K' := hfin
  letI : NormedAddCommGroup (FockV σ) := (fockCore (σ := σ)).toNormedAddCommGroup
  letI : InnerProductSpace ℂ (FockV σ) := by
    first
    | exact InnerProductSpace.ofCore (fockCore (σ := σ)).toCore
    | exact InnerProductSpace.ofCore (fockCore (σ := σ)).toPreInnerProductSpaceCore
    | exact InnerProductSpace.ofCore (fockCore (σ := σ))
  haveI hproj : K'.HasOrthogonalProjection := inferInstance
  let g : FockV σ := f
  let P := K'.orthogonalProjection g
  have hP : ∀ x ∈ K', inner ℂ x (g - (P : FockV σ)) = 0 := by
    first
    | exact K'.orthogonalProjection_inner_eq_zero g
    | exact fun x hx => (K'.mem_orthogonal _).1 (K'.sub_orthogonalProjection_mem_orthogonal g) x hx
    | exact fun x hx => (K'.mem_orthogonal _).1 (K'.sub_starProjection_mem_orthogonal g) x hx
  have key : ∀ x y : FockV σ, inner ℂ x y = FockH1Action.fockInner (σ := σ) x y := fun _ _ => rfl
  let q : MvPolynomial σ ℂ := (P : FockV σ)
  have hsub : g - (P : FockV σ) = (show FockV σ from f - q) := rfl
  refine ⟨(P : FockV σ), P.2, fun x hx => ?_⟩
  have h1 := hP x hx
  rw [hsub] at h1
  have h2 : FockH1Action.fockInner (σ := σ) x (f - q) = 0 := (key x (f - q)).symm.trans h1
  exact h2

end PI.FHS
