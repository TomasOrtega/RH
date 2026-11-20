import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TrivFlagMod
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.FlagMinor
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SameGenericSymm
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ClassListMapDomainPerm
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairCocycle
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PScalarQuotient
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.OfSteps
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeFiniteProjectiveBaseChange
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SameGenericFlagDifferenceStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SameGenericBundleChainStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SameGenericFlagComparisonStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartBundleBaseExtensionStatement
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XBundleOfFamily
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XPullLine
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XPullPreserve
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XFlagframeDual
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace PositivityTheory.Xgn.A_rootnum_dual

section Lists

variable {K : Type*} {σ : Type*}

/- English proof (translation)
Set `φ : (K → ℤ) →+ ℤ` to `AddMonoidHom.mk' (fun v => A (v :: l)) fun v w => hA v w l`. Conclude with `map_neg φ u`.
-/
theorem headAdd_neg {A : List (K → ℤ) → ℤ} (hA : HeadAdd A) (u : K → ℤ)
    (l : List (K → ℤ)) : A ((-u) :: l) = -A (u :: l) := by
  let φ : (K → ℤ) →+ ℤ := AddMonoidHom.mk' (fun v => A (v :: l)) fun v w => hA v w l
  exact map_neg φ u

/- English proof (translation)
Proceed by induction on `l generalizing r with`. Consider the case `nil => simp`. Consider the case `cons u l ih`. Rewrite using `[List.map_cons, List.cons_append, headAdd_neg hA, hp _ _ (List.perm_middle (a := u) (l₁ := l.map (- ·)) (l₂ := r)).symm, ih, hp _ _ (List.perm_middle (a := u) (l₁ := l) (l₂ := r)), List.length_cons, List.cons_append]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem map_neg_append {A : List (K → ℤ) → ℤ} (hp : PermInv A) (hA : HeadAdd A)
    (l r : List (K → ℤ)) : A (l.map (- ·) ++ r) = (-1) ^ l.length * A (l ++ r) := by
  induction l generalizing r with
  | nil => simp
  | cons u l ih =>
    rw [List.map_cons, List.cons_append, headAdd_neg hA,
      hp _ _ (List.perm_middle (a := u) (l₁ := l.map (- ·)) (l₂ := r)).symm, ih,
      hp _ _ (List.perm_middle (a := u) (l₁ := l) (l₂ := r)), List.length_cons, List.cons_append]
    ring

/- English proof (translation)
Establish `h1` using `hH (mem_support_iff.mp hμ)`. Rewrite using `[← h1]`. Simplify using `only [classList, Multiset.length_toList, Multiset.card_map, Finsupp.card_toMultiset, Finsupp.weight_apply]`. Simplify using `[Finsupp.sum]`.
-/
theorem length_classList (cls : σ → K → ℤ) {H : MvPolynomial σ ℤ} {n : ℕ}
    (hH : H.IsHomogeneous n) {μ : σ →₀ ℕ} (hμ : μ ∈ H.support) :
    (classList cls μ).length = n := by
  have h1 := hH (mem_support_iff.mp hμ)
  rw [← h1]
  simp only [classList, Multiset.length_toList, Multiset.card_map, Finsupp.card_toMultiset,
    Finsupp.weight_apply]
  simp [Finsupp.sum]

/- English proof (translation)
Unfold `polyVal`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun μ hμ => ?_` and prove the remaining obligations. Establish `hperm : (classList (fun s => -cls s) μ).Perm ((classList cls μ).map (- ·) ++ [])`. Unfold `classList`.

Rewrite using `[List.append_nil, ← Multiset.coe_eq_coe, ← Multiset.map_coe, Multiset.coe_toList, Multiset.coe_toList, Multiset.map_map]`. Both sides reduce to the same expression. Rewrite using `[hp _ _ hperm, map_neg_append hp hA, length_classList cls hH hμ, List.append_nil]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem polyVal_neg {A : List (K → ℤ) → ℤ} (hp : PermInv A) (hA : HeadAdd A)
    (cls : σ → K → ℤ) {H : MvPolynomial σ ℤ} {n : ℕ} (hH : H.IsHomogeneous n) :
    polyVal A (fun s => -cls s) H = (-1) ^ n * polyVal A cls H := by
  unfold polyVal
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have hperm : (classList (fun s => -cls s) μ).Perm ((classList cls μ).map (- ·) ++ []) := by
    unfold classList
    rw [List.append_nil, ← Multiset.coe_eq_coe, ← Multiset.map_coe, Multiset.coe_toList,
      Multiset.coe_toList, Multiset.map_map]
    rfl
  rw [hp _ _ hperm, map_neg_append hp hA, length_classList cls hH hμ, List.append_nil]
  ring

end Lists

section Numbers

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [Fintype K] [∀ k, Fintype (ι k)] in
/- English proof (translation)
Take `⟨bf, bg, hf, hg, hb⟩` from `hD.degrees`. Use `⟨bg, bf, hg, hf, ?_⟩` and prove the remaining obligations. Rewrite using `[← hb]`. Use function extensionality and compare the values at `k`. Simplify using the standard rewrite rules.

Use `num_not_mem := hD.den_not_mem`. Use `den_not_mem := hD.num_not_mem`. Use `vertical := fun W hW => hD.vertical W fun h => hW (by`. Unfold `ratDiv at h ⊢`. Use the proof step `linarith)`.

Use `unit_off_special := by`. Introduce `W hW hPW hrel hϖ`. Take `⟨u, v, hu, hv, h⟩` from `hD.unit_off_special W hW hPW hrel hϖ`. Use `⟨v, u, hv, hu, ?_⟩` and prove the remaining obligations. Rewrite using `[← neg_sub]`.

Conclude with `P.neg_mem h`.
-/
theorem isVerticalDivisor_swap {P : Ideal (MRing ι O)} {ϖ : O} {b : K → ℤ} {f g : MRing ι O}
    (hD : IsVerticalDivisor P ϖ b f g) : IsVerticalDivisor P ϖ (-b) g f where
  degrees := by
    obtain ⟨bf, bg, hf, hg, hb⟩ := hD.degrees
    refine ⟨bg, bf, hg, hf, ?_⟩
    rw [← hb]
    funext k
    simp
  num_not_mem := hD.den_not_mem
  den_not_mem := hD.num_not_mem
  vertical := fun W hW => hD.vertical W fun h => hW (by
    unfold ratDiv at h ⊢
    linarith)
  unit_off_special := by
    intro W hW hPW hrel hϖ
    obtain ⟨u, v, hu, hv, h⟩ := hD.unit_off_special W hW hPW hrel hϖ
    refine ⟨v, u, hv, hu, ?_⟩
    rw [← neg_sub]
    exact P.neg_mem h

/- English proof (translation)
Unfold `pairNum`. Rewrite using `[Finset.mul_sum]`. Use `Fintype.sum_equiv Fin.revPerm _ _ fun i => ?_` and prove the remaining obligations. Establish `hH` using `isHomogeneous_psumExpansion N k i`. Establish `hn : k - 1 + Q.length = d` using `by omega`.

Establish `hcls : (Sum.elim (fun j : Fin N => -b j.rev) (fun j : Fin N => -b' j.rev)) = fun s => -(Sum.elim (fun j : Fin N => b j.rev) (fun j : Fin N => b' j.rev)) s`. Use function extensionality and compare the values at `s`. Apply the tactic sequence `cases s <;> simp`. Unfold `cycEval`. Rewrite using `[mul_finsum]`.

Use `finsum_congr fun W => ?_` and prove the remaining obligations. Establish `hr : ratDiv P (g i.rev) (f i.rev) W = -ratDiv P (f i.rev) (g i.rev) W`. Unfold `ratDiv`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Fin.revPerm_apply]`.

Use `beta_reduce`. Rewrite using `[hr]`. Distinguish the cases in `hW : ratDiv P (f i.rev) (g i.rev) W = 0`. Simplify using `[hW]`. Rewrite using `[classNum_eq_polyVal _ hH hn, hcls, polyVal_neg (listNum_perm W Q d) (listNum_headAdd IntNumAddFirst.full hϖ hP (hD i.rev) hW Q) _ hH, ← classNum_eq_polyVal _ hH hn, classNum_psumExpansion _ _ k _ hQ, classNum_psumExpansion _ _ k _ hQ]`.

Take `⟨j, rfl⟩ : ∃ j, k = j + 1` from `⟨k - 1, by omega⟩`. Rewrite using `[Nat.add_sub_cancel]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pairNum_dual {ϖ : O} (hϖ : Irreducible ϖ) {P : Ideal (MRing ι O)} {d : ℕ}
    (hP : IsModelOver P d) {N : ℕ} {b b' : Fin N → K → ℤ} {f g : Fin N → MRing ι O}
    (hD : ∀ i, IsVerticalDivisor P ϖ (b i - b' i) (f i) (g i))
    {k : ℕ} (hk : 1 ≤ k) {Q : List (K → ℤ)} (hQ : Q.length + k = d + 1) :
    pairNum P (fun j => -b j.rev) (fun j => -b' j.rev) (fun j => g j.rev) (fun j => f j.rev)
        (psumExpansion N k) Q =
      (-1) ^ k * pairNum P b b' f g (psumExpansion N k) Q := by
  unfold pairNum
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv Fin.revPerm _ _ fun i => ?_
  have hH := isHomogeneous_psumExpansion N k i
  have hn : k - 1 + Q.length = d := by omega
  have hcls : (Sum.elim (fun j : Fin N => -b j.rev) (fun j : Fin N => -b' j.rev)) =
      fun s => -(Sum.elim (fun j : Fin N => b j.rev) (fun j : Fin N => b' j.rev)) s := by
    funext s
    cases s <;> simp
  unfold cycEval
  rw [mul_finsum]
  refine finsum_congr fun W => ?_
  have hr : ratDiv P (g i.rev) (f i.rev) W = -ratDiv P (f i.rev) (g i.rev) W := by
    unfold ratDiv
    ring
  rw [Fin.revPerm_apply]
  beta_reduce
  rw [hr]
  by_cases hW : ratDiv P (f i.rev) (g i.rev) W = 0
  · simp [hW]
  rw [classNum_eq_polyVal _ hH hn, hcls,
    polyVal_neg (listNum_perm W Q d)
      (listNum_headAdd IntNumAddFirst.full hϖ hP (hD i.rev) hW Q) _ hH,
    ← classNum_eq_polyVal _ hH hn, classNum_psumExpansion _ _ k _ hQ,
    classNum_psumExpansion _ _ k _ hQ]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  ring

/- English proof (translation)
Establish `: P.IsPrime` using `hP.multiProj.isPrime`. Establish `hC : (C a : MRing ι O) ∉ P`. Introduce `hmem`. Establish `h1 : a ∈ P.comap (C : O →+* MRing ι O)` using `hmem`. Rewrite `h1` using `[hP.noTorsion]`.

Conclude with `ha (Ideal.mem_bot.mp h1)`. Take `⟨n, u, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ`. Establish `hD` using `ScalarQuotient.isVerticalDivisor_const P ϖ u n hC`. Establish `hH` using `isHomogeneous_psum N j`. Unfold `cycEval`.

Rewrite using `[mul_finsum]`. Use `finsum_congr fun W => ?_` and prove the remaining obligations. Distinguish the cases in `hW : divCycle P (C ((u : O) * ϖ ^ n)) W = 0`. Simplify using `only [hW, zero_mul, mul_zero]`. Establish `hW' : ratDiv P (C ((u : O) * ϖ ^ n)) 1 W ≠ 0`.

Unfold `ratDiv`. Rewrite using `[divCycle_one, sub_zero]` and apply the resulting hypothesis. Establish `e : polyVal (listNum W Q d) (fun i : Fin N => b i.rev) (psum (Fin N) ℤ j) = polyVal (listNum W Q d) b (psum (Fin N) ℤ j)` using `by conv_rhs => rw [← psum_isSymmetric (Fin N) ℤ j Fin.revPerm, polyVal_rename]`. Both sides reduce to the same expression. Use `beta_reduce`.

Rewrite using `[classNum_eq_polyVal _ hH hQ, classNum_eq_polyVal _ hH hQ, polyVal_neg (listNum_perm W Q d) (listNum_headAdd IntNumAddFirst.full hϖ hP hD hW' Q) (fun i : Fin N => b i.rev) hH, e]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem root_dual {ϖ : O} (hϖ : Irreducible ϖ) {P : Ideal (MRing ι O)} {d : ℕ}
    (hP : IsModelOver P d) {N : ℕ} (b : Fin N → K → ℤ) {a : O} (ha : a ≠ 0)
    {j : ℕ} {Q : List (K → ℤ)} (hQ : j + Q.length = d) :
    cycEval (fun W => classNum (fun i : Fin N => -b i.rev) (psum (Fin N) ℤ j) Q W)
        (divCycle P (C a)) =
      (-1) ^ j * cycEval (fun W => classNum b (psum (Fin N) ℤ j) Q W) (divCycle P (C a)) := by
  have : P.IsPrime := hP.multiProj.isPrime
  have hC : (C a : MRing ι O) ∉ P := by
    intro hmem
    have h1 : a ∈ P.comap (C : O →+* MRing ι O) := hmem
    rw [hP.noTorsion] at h1
    exact ha (Ideal.mem_bot.mp h1)
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  have hD := ScalarQuotient.isVerticalDivisor_const P ϖ u n hC
  have hH := isHomogeneous_psum N j
  unfold cycEval
  rw [mul_finsum]
  refine finsum_congr fun W => ?_
  by_cases hW : divCycle P (C ((u : O) * ϖ ^ n)) W = 0
  · simp only [hW, zero_mul, mul_zero]
  have hW' : ratDiv P (C ((u : O) * ϖ ^ n)) 1 W ≠ 0 := by
    unfold ratDiv
    rwa [divCycle_one, sub_zero]
  have e : polyVal (listNum W Q d) (fun i : Fin N => b i.rev) (psum (Fin N) ℤ j) =
      polyVal (listNum W Q d) b (psum (Fin N) ℤ j) := by
    conv_rhs => rw [← psum_isSymmetric (Fin N) ℤ j Fin.revPerm, polyVal_rename]
    rfl
  beta_reduce
  rw [classNum_eq_polyVal _ hH hQ, classNum_eq_polyVal _ hH hQ,
    polyVal_neg (listNum_perm W Q d) (listNum_headAdd IntNumAddFirst.full hϖ hP hD hW' Q)
      (fun i : Fin N => b i.rev) hH, e]
  ring

end Numbers

section Lattices

variable {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
  {V V₁ : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup V₁] [Module Ω V₁]

/- English proof (translation)
Set `L' : Submodule R V` to `{ L with smul_mem' := fun a e he => h.1 a a.2 e he }`. Take `⟨k, φ, v, hφ, hv⟩` from `LocFreeProj.exists_dualBasis (L := L') (r := N) h`. Use `choose l hl using fun i => hβ.2 (φ i)`. Establish `hl' : ∀ i e, β e (l i) = φ i e` using `fun i e => by rw [← hl i]; rfl`. Use `⟨k, fun i => v i, l, fun i => (v i).2, fun i e he => ?_, fun e => ?_, fun w => ?_⟩` and prove the remaining obligations.

Rewrite using `[hl']`. Conclude with `hφ i e he`. Simplify using `only [hl']`. Conclude with `hv e`. Apply `hβ.1` to reduce the goal to its premises.

Use extensionality with `e`. Rewrite using `[LinearMap.flip_apply, LinearMap.flip_apply, map_sum]`. Use `conv_rhs => rw [← hv e, map_sum, LinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, map_smul, LinearMap.smul_apply, hl', smul_eq_mul, smul_eq_mul, mul_comm]`.
-/
theorem exists_system (R : Subalgebra O Ω) {N : ℕ} (L : AddSubgroup V) (h : LocFree R N L)
    (β : V →ₗ[Ω] V₁ →ₗ[Ω] Ω) (hβ : Function.Bijective β.flip) :
    ∃ (k : ℕ) (v : Fin k × Fin N → V) (l : Fin k × Fin N → V₁), (∀ i, v i ∈ L) ∧
      (∀ i, ∀ e ∈ L, β e (l i) ∈ R) ∧ (∀ e, ∑ i, β e (l i) • v i = e) ∧
      ∀ w, ∑ i, β (v i) w • l i = w := by
  let L' : Submodule R V := { L with smul_mem' := fun a e he => h.1 a a.2 e he }
  obtain ⟨k, φ, v, hφ, hv⟩ := LocFreeProj.exists_dualBasis (L := L') (r := N) h
  choose l hl using fun i => hβ.2 (φ i)
  have hl' : ∀ i e, β e (l i) = φ i e := fun i e => by rw [← hl i]; rfl
  refine ⟨k, fun i => v i, l, fun i => (v i).2, fun i e he => ?_, fun e => ?_, fun w => ?_⟩
  · rw [hl']
    exact hφ i e he
  · simp only [hl']
    exact hv e
  · apply hβ.1
    ext e
    rw [LinearMap.flip_apply, LinearMap.flip_apply, map_sum]
    conv_rhs => rw [← hv e, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, map_smul, LinearMap.smul_apply, hl', smul_eq_mul, smul_eq_mul, mul_comm]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hw`. Proceed by induction on `hw using AddSubgroup.closure_induction with`. Consider the case `mem w hw`. Take `⟨a, ha, e, he, rfl⟩` from `hw`.

Introduce `v hv`. Proceed by induction on `hv using AddSubgroup.closure_induction with`. Consider the case `mem v hv`. Take `⟨c, hc, y, hy, rfl⟩` from `hv`. Rewrite using `[map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]`.

Conclude with `R'.mul_mem ha (R'.mul_mem hc (hR _ ((hM e).1 he y hy)))`. Consider the case `zero => rw [map_zero, LinearMap.zero_apply]`. Conclude with `R'.zero_mem`. Consider the case `add x y _ _ hx hy => rw [map_add, LinearMap.add_apply]`. Conclude with `R'.add_mem hx hy`.

Consider the case `neg x _ hx => rw [map_neg, LinearMap.neg_apply]`. Conclude with `R'.neg_mem hx`. Consider the case `zero => intro v _`. Rewrite using `[map_zero]`. Conclude with `R'.zero_mem`.

Consider the case `add x y _ _ hx hy => intro v hv`. Rewrite using `[map_add]`. Conclude with `R'.add_mem (hx v hv) (hy v hv)`. Consider the case `neg x _ hx => intro v hv`. Rewrite using `[map_neg]`.

Conclude with `R'.neg_mem (hx v hv)`. Introduce `hw`. Take `⟨k, v, l, hv, hl, -, hs⟩` from `exists_system R L h β hβ`. Rewrite using `[← hs w]`. Conclude with `AddSubgroup.sum_mem _ fun i _ => AddSubgroup.subset_closure ⟨_, hw _ (AddSubgroup.subset_closure ⟨1, R'.one_mem, _, hv i, (one_smul _ _).symm⟩), _, (hM _).2 (hl i), rfl⟩`.
-/
theorem dual_closure (R R' : Subalgebra O Ω) (hR : ∀ a ∈ R, a ∈ R') {N : ℕ} (L : AddSubgroup V)
    (h : LocFree R N L) (β : V →ₗ[Ω] V₁ →ₗ[Ω] Ω) (hβ : Function.Bijective β.flip)
    (M : AddSubgroup V₁) (hM : ∀ w, w ∈ M ↔ ∀ v ∈ L, β v w ∈ R) (w : V₁) :
    w ∈ AddSubgroup.closure {v | ∃ a ∈ R', ∃ e ∈ M, v = a • e} ↔
      ∀ v ∈ AddSubgroup.closure {v | ∃ a ∈ R', ∃ e ∈ L, v = a • e}, β v w ∈ R' := by
  constructor
  · intro hw
    induction hw using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a, ha, e, he, rfl⟩ := hw
      intro v hv
      induction hv using AddSubgroup.closure_induction with
      | mem v hv =>
        obtain ⟨c, hc, y, hy, rfl⟩ := hv
        rw [map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
        exact R'.mul_mem ha (R'.mul_mem hc (hR _ ((hM e).1 he y hy)))
      | zero => rw [map_zero, LinearMap.zero_apply]; exact R'.zero_mem
      | add x y _ _ hx hy => rw [map_add, LinearMap.add_apply]; exact R'.add_mem hx hy
      | neg x _ hx => rw [map_neg, LinearMap.neg_apply]; exact R'.neg_mem hx
    | zero => intro v _; rw [map_zero]; exact R'.zero_mem
    | add x y _ _ hx hy => intro v hv; rw [map_add]; exact R'.add_mem (hx v hv) (hy v hv)
    | neg x _ hx => intro v hv; rw [map_neg]; exact R'.neg_mem (hx v hv)
  · intro hw
    obtain ⟨k, v, l, hv, hl, -, hs⟩ := exists_system R L h β hβ
    rw [← hs w]
    exact AddSubgroup.sum_mem _ fun i _ => AddSubgroup.subset_closure
      ⟨_, hw _ (AddSubgroup.subset_closure ⟨1, R'.one_mem, _, hv i, (one_smul _ _).symm⟩), _,
        (hM _).2 (hl i), rfl⟩

/- English proof (translation)
Introduce `w hw`. Take `⟨k, v, l, hv, hl, hs, -⟩` from `exists_system R L' h β hβ`. Use `choose c hc0 hc using fun i => hg (v i) (hv i)`. Use `⟨∏ i, c i, Finset.prod_ne_zero_iff.2 fun i _ => hc0 i, (hM' _).2 fun e he => ?_⟩` and prove the remaining obligations. Establish `key : algebraMap O Ω (∏ i, c i) • e ∈ L`.

Rewrite using `[← hs e, Finset.smul_sum]`. Use `AddSubgroup.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[smul_comm, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), map_mul, mul_smul]`. Conclude with `hL _ (hl i e he) _ (hL _ (R.algebraMap_mem _) _ (hc i))`. Use `(hM w).1 hw _ key` as an intermediate fact.

Rewrite `this` using `[map_smul, LinearMap.smul_apply]`. Rewrite using `[map_smul]`. Conclude with `this`.
-/
theorem dual_generic [IsDomain O] (R : Subalgebra O Ω) {N : ℕ} (L L' : AddSubgroup V)
    (hL : ∀ a ∈ R, ∀ e ∈ L, a • e ∈ L)
    (h : LocFree R N L') (β : V →ₗ[Ω] V₁ →ₗ[Ω] Ω) (hβ : Function.Bijective β.flip)
    (M M' : AddSubgroup V₁) (hM : ∀ w, w ∈ M ↔ ∀ v ∈ L, β v w ∈ R)
    (hM' : ∀ w, w ∈ M' ↔ ∀ v ∈ L', β v w ∈ R)
    (hg : ∀ v ∈ L', ∃ c : O, c ≠ 0 ∧ algebraMap O Ω c • v ∈ L) :
    ∀ w ∈ M, ∃ c : O, c ≠ 0 ∧ algebraMap O Ω c • w ∈ M' := by
  classical
  intro w hw
  obtain ⟨k, v, l, hv, hl, hs, -⟩ := exists_system R L' h β hβ
  choose c hc0 hc using fun i => hg (v i) (hv i)
  refine ⟨∏ i, c i, Finset.prod_ne_zero_iff.2 fun i _ => hc0 i, (hM' _).2 fun e he => ?_⟩
  have key : algebraMap O Ω (∏ i, c i) • e ∈ L := by
    rw [← hs e, Finset.smul_sum]
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    rw [smul_comm, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), map_mul, mul_smul]
    exact hL _ (hl i e he) _ (hL _ (R.algebraMap_mem _) _ (hc i))
  have := (hM w).1 hw _ key
  rw [map_smul, LinearMap.smul_apply] at this
  rw [map_smul]
  exact this

end Lattices

section Bundles

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Ω : Type} [Field Ω]
  [Algebra O Ω] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {x : (Σ k, ι k) → Ω} {N : ℕ} {V : Type} [AddCommGroup V] [Module Ω V]
  {V₁ : Type} [AddCommGroup V₁] [Module Ω V₁] {β : V →ₗ[Ω] V₁ →ₗ[Ω] Ω}

/- English proof (translation)
Use `⟨hD.1, fun s hs w => ?_⟩` and prove the remaining obligations. Establish `hx` using `A_pull_preserve.below_ne x z s hs`. Rewrite using `[hE s hs, hF s hs]`. Conclude with `dual_closure _ _ (fun a ha => A_pull_line.map_mem (AlgHom.id O Ω) x z s hs a ha) _ (((t_bundle_of_family O Ω K ι x N V).2 E).2 _ hx) β hD.1 _ (hD.2 _ hx) w`.
-/
theorem pull_dual {E : ChartBundle O (mseg x) N V} {F : ChartBundle O (mseg x) N V₁}
    (hD : IsDualLat O x β E.lat F.lat) {K' : Type} [Fintype K'] {ι' : K' → Type}
    [∀ k, Fintype (ι' k)] {z : (Σ k, ι' k) → Ω} {EB : ChartBundle O (mseg (joinCoord x z)) N V}
    {FB : ChartBundle O (mseg (joinCoord x z)) N V₁} (hE : IsPull O x z E EB)
    (hF : IsPull O x z F FB) : IsDualLat O (joinCoord x z) β EB.lat FB.lat := by
  refine ⟨hD.1, fun s hs w => ?_⟩
  have hx := A_pull_preserve.below_ne x z s hs
  rw [hE s hs, hF s hs]
  exact dual_closure _ _ (fun a ha => A_pull_line.map_mem (AlgHom.id O Ω) x z s hs a ha) _
    (((t_bundle_of_family O Ω K ι x N V).2 E).2 _ hx) β hD.1 _ (hD.2 _ hx) w

/- English proof (translation)
Introduce `s hs`. Establish `h` using `((t_bundle_of_family O Ω K ι x N V).2 E).2 s hs`. Establish `h'` using `((t_bundle_of_family O Ω K ι x N V).2 E').2 s hs`. Conclude with `⟨dual_generic _ _ _ h.1 h' β hD.1 _ _ (hD.2 s hs) (hD'.2 s hs) (hS s hs).2, dual_generic _ _ _ h'.1 h β hD.1 _ _ (hD'.2 s hs) (hD.2 s hs) (hS s hs).1⟩`.
-/
theorem sameGeneric_dual {E E' : ChartBundle O (mseg x) N V} {F F' : ChartBundle O (mseg x) N V₁}
    (hS : SameGeneric O x E E') (hD : IsDualLat O x β E.lat F.lat)
    (hD' : IsDualLat O x β E'.lat F'.lat) : SameGeneric O x F F' := by
  intro s hs
  have h := ((t_bundle_of_family O Ω K ι x N V).2 E).2 s hs
  have h' := ((t_bundle_of_family O Ω K ι x N V).2 E').2 s hs
  exact ⟨dual_generic _ _ _ h.1 h' β hD.1 _ _ (hD.2 s hs) (hD'.2 s hs) (hS s hs).2,
    dual_generic _ _ _ h'.1 h β hD.1 _ _ (hD'.2 s hs) (hD.2 s hs) (hS s hs).1⟩

end Bundles

end PositivityTheory.Xgn.A_rootnum_dual

open PositivityTheory.Xgn.A_rootnum_dual in
/- English proof (translation)
Introduce `O _ _ _ Ω _ _ K _ _ ι _ x d N V _ _ V₁ _ _ β E E' F F' hM hS hD hD'`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Take `⟨K', _, _, ι', _, z, EB, w, b, hm, hb, hj⟩` from `GlobalTheory.T.same_generic_bundle_chain O Ω K ι x d hM N 1 V ![E, E'] (by`. Introduce `j`. Use `fin_cases j`.

Conclude with `fun s _ => ⟨fun v hv => ⟨1, one_ne_zero, by simpa using hv⟩, fun v hv => ⟨1, one_ne_zero, by simpa using hv⟩⟩`. Conclude with `hS)`. Establish `hp : IsPull O x z E (EB 0)` using `(hj 0).1`. Establish `hp' : IsPull O x z E' (EB 1)` using `(hj 1).1`. Take `⟨-, hB⟩` from `(BundleExamples.isModelOver_iff O _ d).mp hm`.

Establish `hB' : IsModelOver (pointIdeal O (joinCoord x z)) d` using `hB`. Establish `hSB` using `(PositivityTheory.Xgn.t_pull_preserve O Ω K ι x N V E E' K' ι' z _ _ hp hp').2.1 hS`. Take `⟨-, f, g, hfp⟩` from `GlobalTheory.T.same_generic_flag_comparison O Ω (K ⊕ K') (Sum.elim ι ι') (joinCoord x z) ϖ hϖ d hB' N V (EB 0) (EB 1) hSB w w (b 0) (b 1) (hj 0).2 (hj 1).2 (fun i j hij => by simp [Module.Basis.repr_self, hij.ne])`. Take `⟨FB, hF⟩` from `(GlobalTheory.T.chart_bundle_base_extension O Ω K ι x N V₁ F).1 K' ι' z`. Take `⟨F'B, hF'⟩` from `(GlobalTheory.T.chart_bundle_base_extension O Ω K ι x N V₁ F').1 K' ι' z`.

Take `⟨w₁, hw₁⟩` from `PositivityTheory.Xgn.A_flagframe_dual.exists_dual β hD.1 w`. Establish `hw : ∀ i j, β (w i) (w₁ j) = if i = j.rev then 1 else 0` using `fun i j => by`. Rewrite using `[hw₁]`. Simplify using `[Finsupp.single_apply]`. Establish `hfp₁ : IsFlagPair ϖ (joinCoord x z) FB F'B w₁ w₁ (fun j => -b 0 j.rev) (fun j => -b 1 j.rev) (fun j => g j.rev) (fun j => f j.rev)`.

Use `⟨PositivityTheory.Xgn.t_flagframe_dual O Ω _ _ _ N V V₁ _ _ β (pull_dual hD hp hF) w _ hfp.flag w₁ hw, PositivityTheory.Xgn.t_flagframe_dual O Ω _ _ _ N V V₁ _ _ β (pull_dual hD' hp' hF') w _ hfp.flag' w₁ hw, fun i j hij => by simp [Module.Basis.repr_self, hij.ne], fun i => ?_, f …` and prove the remaining obligations. Establish `h` using `isVerticalDivisor_swap (hfp.vertical i.rev)`. Establish `e : -b 0 i.rev - -b 1 i.rev = -(b 0 i.rev - b 1 i.rev)` using `by abel`. Rewrite using `[e]`. Conclude with `h`.

Establish `h` using `hfp.generic i.rev`. Rewrite `h`, the goal using `[Module.Basis.repr_self, Finsupp.single_eq_same, one_mul]`. Conclude with `h.symm`. Take `⟨h1, h2⟩` from `GlobalTheory.T.same_generic_flag_difference O Ω K ι x ϖ hϖ d hM N V E E' hS K' ι' z hm hb _ _ hp hp' w w _ _ f g hfp`. Take `⟨h3, h4⟩` from `GlobalTheory.T.same_generic_flag_difference O Ω K ι x ϖ hϖ d hM N V₁ F F' (sameGeneric_dual hS hD hD') K' ι' z hm hb _ _ hF hF' w₁ w₁ _ _ _ _ hfp₁`.

Use `⟨fun k hk1 hk2 q L Q hQ => ?_, fun j hj q L Q hQ a ha => ?_⟩` and prove the remaining obligations. Rewrite using `[h1 k hk1 hk2 q L Q hQ, h3 k hk1 hk2 q L Q hQ, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun μ hμ => ?_` and prove the remaining obligations. Rewrite using `[pairNum_dual hϖ hB' hfp.vertical hk1 (by rw [length_classList _ hQ hμ]; omega)]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h2 j _ (psum_isSymmetric _ _ j) (isHomogeneous_psum N j) hj q L Q hQ a ha, h4 j _ (psum_isSymmetric _ _ j) (isHomogeneous_psum N j) hj q L Q hQ a ha, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun μ hμ => ?_` and prove the remaining obligations. Rewrite using `[root_dual hϖ hB' (b 0) ha (by rw [length_classList _ hQ hμ]; omega)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem PositivityTheory.Xgn.t_rootnum_dual : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (V₁ : Type) [AddCommGroup V₁] [Module Ω V₁] (β : V →ₗ[Ω] V₁ →ₗ[Ω] Ω) (E E' : ChartBundle O (mseg x) N V) (F F' : ChartBundle O (mseg x) N V₁), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → SameGeneric O x E E' → IsDualLat O x β E.lat F.lat → IsDualLat O x β E'.lat F'.lat → (∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d + 1 - k) → ck O x d N F F' k L Q = (-1) ^ k * ck O x d N E E' k L Q) ∧ ∀ (j : ℕ), j ≤ d → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d - j) → ∀ a : O, a ≠ 0 → rootNum O x d N F (psum (Fin N) ℤ j) L Q a = (-1) ^ j * rootNum O x d N E (psum (Fin N) ℤ j) L Q a := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x d N V _ _ V₁ _ _ β E E' F F' hM hS hD hD'
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨K', _, _, ι', _, z, EB, w, b, hm, hb, hj⟩ := GlobalTheory.T.same_generic_bundle_chain O Ω K ι x d hM N 1 V ![E, E'] (by
    intro j
    fin_cases j
    · exact fun s _ => ⟨fun v hv => ⟨1, one_ne_zero, by simpa using hv⟩,
        fun v hv => ⟨1, one_ne_zero, by simpa using hv⟩⟩
    · exact hS)
  have hp : IsPull O x z E (EB 0) := (hj 0).1
  have hp' : IsPull O x z E' (EB 1) := (hj 1).1
  obtain ⟨-, hB⟩ := (BundleExamples.isModelOver_iff O _ d).mp hm
  have hB' : IsModelOver (pointIdeal O (joinCoord x z)) d := hB
  have hSB := (PositivityTheory.Xgn.t_pull_preserve O Ω K ι x N V E E' K' ι' z _ _ hp hp').2.1 hS
  obtain ⟨-, f, g, hfp⟩ := GlobalTheory.T.same_generic_flag_comparison O Ω (K ⊕ K') (Sum.elim ι ι') (joinCoord x z) ϖ hϖ d hB' N V
    (EB 0) (EB 1) hSB w w (b 0) (b 1) (hj 0).2 (hj 1).2
    (fun i j hij => by simp [Module.Basis.repr_self, hij.ne])
  obtain ⟨FB, hF⟩ := (GlobalTheory.T.chart_bundle_base_extension O Ω K ι x N V₁ F).1 K' ι' z
  obtain ⟨F'B, hF'⟩ := (GlobalTheory.T.chart_bundle_base_extension O Ω K ι x N V₁ F').1 K' ι' z
  obtain ⟨w₁, hw₁⟩ := PositivityTheory.Xgn.A_flagframe_dual.exists_dual β hD.1 w
  have hw : ∀ i j, β (w i) (w₁ j) = if i = j.rev then 1 else 0 := fun i j => by
    rw [hw₁]; simp [Finsupp.single_apply]
  have hfp₁ : IsFlagPair ϖ (joinCoord x z) FB F'B w₁ w₁ (fun j => -b 0 j.rev) (fun j => -b 1 j.rev)
      (fun j => g j.rev) (fun j => f j.rev) := by
    refine ⟨PositivityTheory.Xgn.t_flagframe_dual O Ω _ _ _ N V V₁ _ _ β (pull_dual hD hp hF) w _ hfp.flag w₁ hw,
      PositivityTheory.Xgn.t_flagframe_dual O Ω _ _ _ N V V₁ _ _ β (pull_dual hD' hp' hF') w _ hfp.flag' w₁ hw,
      fun i j hij => by simp [Module.Basis.repr_self, hij.ne], fun i => ?_, fun i => ?_⟩
    · have h := isVerticalDivisor_swap (hfp.vertical i.rev)
      have e : -b 0 i.rev - -b 1 i.rev = -(b 0 i.rev - b 1 i.rev) := by abel
      rw [e]
      exact h
    · have h := hfp.generic i.rev
      rw [Module.Basis.repr_self, Finsupp.single_eq_same, one_mul] at h ⊢
      exact h.symm
  obtain ⟨h1, h2⟩ := GlobalTheory.T.same_generic_flag_difference O Ω K ι x ϖ hϖ d hM N V E E' hS K' ι' z hm hb _ _ hp hp'
    w w _ _ f g hfp
  obtain ⟨h3, h4⟩ := GlobalTheory.T.same_generic_flag_difference O Ω K ι x ϖ hϖ d hM N V₁ F F' (sameGeneric_dual hS hD hD')
    K' ι' z hm hb _ _ hF hF' w₁ w₁ _ _ _ _ hfp₁
  refine ⟨fun k hk1 hk2 q L Q hQ => ?_, fun j hj q L Q hQ a ha => ?_⟩
  · rw [h1 k hk1 hk2 q L Q hQ, h3 k hk1 hk2 q L Q hQ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    rw [pairNum_dual hϖ hB' hfp.vertical hk1 (by rw [length_classList _ hQ hμ]; omega)]
    ring
  · rw [h2 j _ (psum_isSymmetric _ _ j) (isHomogeneous_psum N j) hj q L Q hQ a ha,
      h4 j _ (psum_isSymmetric _ _ j) (isHomogeneous_psum N j) hj q L Q hQ a ha, Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    rw [root_dual hϖ hB' (b 0) ha (by rw [length_classList _ hQ hμ]; omega)]
    ring
