import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.DualWeightVectorApplyEqZeroOfNeNeg
import Formalism.SharpRestriction.GrowthBounds.ProjectionOfIsotypicDecomposition
import Formalism.SharpRestriction.GrowthBounds.RootWeights.WeightConditionFromIntegralForm

noncomputable section

open Finset

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.G.Joints

section field

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/- English proof (translation)
Establish `hm : ∀ f g : Module.End K V, f.dualMap * g.dualMap = (g * f).dualMap` using `fun f g => LinearMap.ext fun φ => LinearMap.ext fun x => rfl`. Establish `hs : ∀ f g : Module.End K V, (f - g).dualMap = f.dualMap - g.dualMap` using `fun f g => LinearMap.ext fun φ => LinearMap.ext fun x => by simp [LinearMap.dualMap_apply]`. Establish `hn : ∀ f : Module.End K V, (-f).dualMap = -f.dualMap` using `fun f => LinearMap.ext fun φ => LinearMap.ext fun x => by simp [LinearMap.dualMap_apply]`. Establish `h0 : (0 : Module.End K V).dualMap = 0` using `LinearMap.ext fun φ => LinearMap.ext fun x => by simp [LinearMap.dualMap_apply]`. Simplify using `only [Formalism.MainNotions.CovariantDegrees.dualOps, neg_mul_neg, hm]`.

Rewrite using `[← hs, show E c d * E a b - E a b * E c d = -(E a b * E c d - E c d * E a b) from (neg_sub _ _).symm, hR a b c d]`. Apply the tactic sequence `split_ifs <;> simp only [hn, hs, h0] <;> abel`.
-/
theorem dualOperators_commutator_relation (E : GLOps n K V)
    (hR : ∀ a b c d, E a b * E c d - E c d * E a b = (if b = c then E a d else 0) - (if d = a then E c b else 0))
    (a b c d : Fin n) :
    dualOps E a b * dualOps E c d - dualOps E c d * dualOps E a b =
      (if b = c then dualOps E a d else 0) - (if d = a then dualOps E c b else 0) := by
  have hm : ∀ f g : Module.End K V, f.dualMap * g.dualMap = (g * f).dualMap :=
    fun f g => LinearMap.ext fun φ => LinearMap.ext fun x => rfl
  have hs : ∀ f g : Module.End K V, (f - g).dualMap = f.dualMap - g.dualMap :=
    fun f g => LinearMap.ext fun φ => LinearMap.ext fun x => by simp [LinearMap.dualMap_apply]
  have hn : ∀ f : Module.End K V, (-f).dualMap = -f.dualMap :=
    fun f => LinearMap.ext fun φ => LinearMap.ext fun x => by simp [LinearMap.dualMap_apply]
  have h0 : (0 : Module.End K V).dualMap = 0 :=
    LinearMap.ext fun φ => LinearMap.ext fun x => by simp [LinearMap.dualMap_apply]
  simp only [Formalism.MainNotions.CovariantDegrees.dualOps, neg_mul_neg, hm]
  rw [← hs, show E c d * E a b - E a b * E c d = -(E a b * E c d - E c d * E a b) from (neg_sub _ _).symm,
    hR a b c d]
  split_ifs <;> simp only [hn, hs, h0] <;> abel

/- English proof (translation)
Establish `hspan : Submodule.span K (⋃ ν : Fin n → ℤ, (weightSp E ν : Set V)) = ⊤`. Rewrite using `[Submodule.span_iUnion]`. Simplify `hE` using `only [Submodule.span_eq]`. Take `⟨b, hbs, hbspan, hbli⟩` from `exists_linearIndependent K (⋃ ν : Fin n → ℤ, (weightSp E ν : Set V))`. Establish `hbtop : ⊤ ≤ Submodule.span K (Set.range ((↑) : b → V))`.

Rewrite using `[Subtype.range_coe, hbspan, hspan]`. Set `B : Module.Basis b K V` to `Module.Basis.mk hbli hbtop`. Use `haveI : Finite b := Module.Finite.finite_basis B`. Establish `hwt : ∀ (x : V) (ν : Fin n → ℤ), x ∈ weightSp E ν → ∀ a, E a a x = ((ν a : ℤ) : K) • x`. Introduce `x ν hx a`.

Unfold `Formalism.MainNotions.G.weightSp at hx`. Establish `hx'` using `(Submodule.mem_iInf _).1 hx a`. Rewrite `hx'` using `[LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]`. Simplify using `using hx'`. Rewrite using `[eq_top_iff, ← B.dualBasis.span_eq, Submodule.span_le]`.

Introduce and unpack `_ ⟨i, rfl⟩`. Take `⟨ν, hν⟩` from `Set.mem_iUnion.1 (hbs i.2)`. Use `Submodule.mem_iSup_of_mem (-ν) ?_` and prove the remaining obligations. Unfold `Formalism.MainNotions.G.weightSp`. Use `(Submodule.mem_iInf _).2 fun a => ?_` and prove the remaining obligations.

Rewrite using `[LinearMap.mem_ker]`. Use `B.ext fun j => ?_` and prove the remaining obligations. Take `⟨ν', hν'⟩` from `Set.mem_iUnion.1 (hbs j.2)`. Establish `hBj : (B j : V) = j` using `Module.Basis.mk_apply hbli hbtop j`. Establish `hj : (B j : V) ∈ weightSp E ν'` using `by rw [hBj]; exact hν'`.

Simplify using `only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, Formalism.MainNotions.CovariantDegrees.dualOps, LinearMap.neg_apply, LinearMap.dualMap_apply, LinearMap.zero_apply]`. Rewrite using `[hwt _ _ hj a, map_smul, B.dualBasis_apply_self]`. Distinguish the cases in `hij : j = i`. Establish `h1 : E a a (B j) = ((ν' a : ℤ) : K) • B j` using `hwt _ _ hj a`. Establish `h2 : E a a (B j) = ((ν a : ℤ) : K) • B j` using `hwt _ _ (by rw [hBj, hij]; exact hν) a`.

Establish `hK : ((ν' a : ℤ) : K) = ν a` using `smul_left_injective K (B.ne_zero j) (h1.symm.trans h2)`. Rewrite using `[if_pos hij, hK]`. Simplify using the standard rewrite rules. Rewrite using `[if_neg hij]`. Simplify using the standard rewrite rules.
-/
theorem dualOperators_iSup_weightSpace_eq_top [CharZero K] [FiniteDimensional K V] (E : GLOps n K V)
    (hE : (⨆ nu : Fin n → ℤ, weightSp E nu) = ⊤) : (⨆ nu : Fin n → ℤ, weightSp (dualOps E) nu) = ⊤ := by
  classical
  have hspan : Submodule.span K (⋃ ν : Fin n → ℤ, (weightSp E ν : Set V)) = ⊤ := by
    rw [Submodule.span_iUnion]
    simpa only [Submodule.span_eq] using hE
  obtain ⟨b, hbs, hbspan, hbli⟩ := exists_linearIndependent K (⋃ ν : Fin n → ℤ, (weightSp E ν : Set V))
  have hbtop : ⊤ ≤ Submodule.span K (Set.range ((↑) : b → V)) := by
    rw [Subtype.range_coe, hbspan, hspan]
  let B : Module.Basis b K V := Module.Basis.mk hbli hbtop
  haveI : Finite b := Module.Finite.finite_basis B
  have hwt : ∀ (x : V) (ν : Fin n → ℤ), x ∈ weightSp E ν → ∀ a, E a a x = ((ν a : ℤ) : K) • x := by
    intro x ν hx a
    unfold Formalism.MainNotions.G.weightSp at hx
    have hx' := (Submodule.mem_iInf _).1 hx a
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hx'
    simpa using hx'
  rw [eq_top_iff, ← B.dualBasis.span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  obtain ⟨ν, hν⟩ := Set.mem_iUnion.1 (hbs i.2)
  refine Submodule.mem_iSup_of_mem (-ν) ?_
  unfold Formalism.MainNotions.G.weightSp
  refine (Submodule.mem_iInf _).2 fun a => ?_
  rw [LinearMap.mem_ker]
  refine B.ext fun j => ?_
  obtain ⟨ν', hν'⟩ := Set.mem_iUnion.1 (hbs j.2)
  have hBj : (B j : V) = j := Module.Basis.mk_apply hbli hbtop j
  have hj : (B j : V) ∈ weightSp E ν' := by rw [hBj]; exact hν'
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, Formalism.MainNotions.CovariantDegrees.dualOps,
    LinearMap.neg_apply, LinearMap.dualMap_apply, LinearMap.zero_apply]
  rw [hwt _ _ hj a, map_smul, B.dualBasis_apply_self]
  by_cases hij : j = i
  · have h1 : E a a (B j) = ((ν' a : ℤ) : K) • B j := hwt _ _ hj a
    have h2 : E a a (B j) = ((ν a : ℤ) : K) • B j := hwt _ _ (by rw [hBj, hij]; exact hν) a
    have hK : ((ν' a : ℤ) : K) = ν a := smul_left_injective K (B.ne_zero j) (h1.symm.trans h2)
    rw [if_pos hij, hK]
    simp
  · rw [if_neg hij]
    simp

/- English proof (translation)
Assemble the required witnesses or components as `⟨dualOperators_commutator_relation E hE.1, fun _ => ⟨⊤, inferInstance, Submodule.mem_top, fun _ _ _ _ => Submodule.mem_top⟩, dualOperators_iSup_weightSpace_eq_top E hE.2.2⟩`.
-/
theorem dualOperators_isGLRep [CharZero K] [FiniteDimensional K V] (E : GLOps n K V) (hE : IsGLRep E) : IsGLRep (dualOps E) := ⟨dualOperators_commutator_relation E hE.1, fun _ => ⟨⊤, inferInstance, Submodule.mem_top, fun _ _ _ _ => Submodule.mem_top⟩,
    dualOperators_iSup_weightSpace_eq_top E hE.2.2⟩

/- English proof (translation)
Establish `h' : Antitone mu` using `h`. Introduce `a b hab`. Use `show -mu (Fin.rev b) ≤ -mu (Fin.rev a)`. Conclude with `neg_le_neg (h' (Fin.rev_le_rev.2 hab))`.
-/
theorem dominant_dualWeight {mu : Fin n → ℤ} (h : Dominant mu) : Dominant (dualWt mu) := by
  have h' : Antitone mu := h
  intro a b hab
  show -mu (Fin.rev b) ≤ -mu (Fin.rev a)
  exact neg_le_neg (h' (Fin.rev_le_rev.2 hab))

end field

section lattice

variable {n : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {V : Type*} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

/- English proof (translation)
Take `⟨hR, -, ⟨hv0, hvl, hraise⟩, hspan⟩` from `hI`. Establish `rel` using `hR.1`. Establish `hwt : ∀ (ν : Fin n → ℤ) (y : V), y ∈ weightSp E ν ↔ ∀ a, E a a y = ((ν a : ℤ) : KK O) • y`. Introduce `ν y`. Unfold `Formalism.MainNotions.G.weightSp`.

Simplify using `only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]`. Establish `hshift : ∀ (a b : Fin n) (ν : Fin n → ℤ) (y : V), y ∈ weightSp E ν → E a b y ∈ weightSp E (ν + Pi.single a 1 - Pi.single b 1)`. Introduce `a b ν y hy`. Rewrite `hy`, the goal using `[hwt]`. Introduce `c`.

Establish `h` using `congrArg (fun T : Module.End (KK O) V => T y) (rel c c a b)`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply, hy c, map_smul] at h`. Rewrite `h` using `[sub_eq_iff_eq_add]`. Rewrite using `[h]`. Apply the tactic sequence `rcases eq_or_ne c a with rfl | hca <;> rcases eq_or_ne b c with rfl | hbc`.

Simplify using `[Pi.single_apply]`. Simplify using `only [eq_self_iff_true, if_true, if_neg hbc, LinearMap.zero_apply, sub_zero, Pi.add_apply, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hbc.symm, Int.cast_add, Int.cast_one, add_smul, one_smul]`. Normalize the expressions using the abelian group laws. Simplify using `only [eq_self_iff_true, if_true, if_neg hca, LinearMap.zero_apply, zero_sub, Pi.add_apply, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hca, add_zero, Int.cast_sub, Int.cast_one, sub_smul, one_smul]`. Normalize the expressions using the abelian group laws.

Simplify using `[Pi.single_apply, hca, hbc, hbc.symm]`. Set `L : Submonoid (Module.End (KK O) V)` to `Submonoid.closure {T | ∃ a b, b < a ∧ T = E a b}`. Set `U : Submodule (KK O) V` to `Submodule.span (KK O) {y | ∃ u ∈ L, y = u v}`. Establish `hLU : ∀ u ∈ L, ∀ y ∈ U, u y ∈ U`. Introduce `u hu y hy`.

Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨w, hw, rfl⟩` from `hz`. Conclude with `Submodule.subset_span ⟨u * w, L.mul_mem hu hw, rfl⟩`. Consider the case `zero => simp`.

Consider the case `add y z _ _ hy hz`. Rewrite using `[map_add]`. Conclude with `U.add_mem hy hz`. Consider the case `smul c y _ hy`. Rewrite using `[map_smul]`.

Conclude with `U.smul_mem c hy`. Establish `hv : v ∈ U` using `Submodule.subset_span ⟨1, L.one_mem, rfl⟩`. Establish `base : ∀ c d, E c d v ∈ U`. Introduce `c d`. Break down `lt_trichotomy c d with h | rfl | h` into its components or cases.

Rewrite using `[hraise c d h]`. Conclude with `U.zero_mem`. Rewrite using `[(hwt lam v).1 hvl c]`. Conclude with `U.smul_mem _ hv`. Conclude with `Submodule.subset_span ⟨E c d, Submonoid.subset_closure ⟨c, d, h, rfl⟩, rfl⟩`.

Establish `key : ∀ u ∈ L, ∀ c d, E c d (u v) ∈ U`. Introduce `u hu`. Proceed by induction on `hu using Submonoid.closure_induction_left with`. Consider the case `one`. Introduce `c d`.

Conclude with `base c d`. Consider the case `mul_left x hx y hy ih`. Introduce `c d`. Take `⟨a, b, hab, rfl⟩` from `hx`. Rewrite using `[Module.End.mul_apply]`.

Establish `h` using `congrArg (fun T : Module.End (KK O) V => T (y v)) (rel c d a b)`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply] at h`. Rewrite `h` using `[sub_eq_iff_eq_add]`. Rewrite using `[h]`. Use `U.add_mem (U.sub_mem ?_ ?_) (hLU _ (Submonoid.subset_closure ⟨a, b, hab, rfl⟩) _ (ih c d))` and prove the remaining obligations.

Use `split_ifs`. Conclude with `ih c b`. Simplify using the standard rewrite rules. Use `split_ifs`. Conclude with `ih a d`.

Simplify using the standard rewrite rules. Establish `hEU : ∀ c d, ∀ y ∈ U, E c d y ∈ U`. Introduce `c d y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem z hz`.

Take `⟨u, hu, rfl⟩` from `hz`. Conclude with `key u hu c d`. Consider the case `zero => simp`. Consider the case `add y z _ _ hy hz`. Rewrite using `[map_add]`.

Conclude with `U.add_mem hy hz`. Consider the case `smul t y _ hy`. Rewrite using `[map_smul]`. Conclude with `U.smul_mem t hy`. Establish `hUtop : U = ⊤`.

Rewrite using `[eq_top_iff, ← hspan]`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨u, hu, rfl⟩`. Proceed by induction on `hu using Submonoid.closure_induction_left with`. Consider the case `one => exact hv`.

Consider the case `mul_left x hx y _ ih`. Take `⟨⟨a, b⟩, rfl⟩` from `hx`. Rewrite using `[Module.End.mul_apply]`. Conclude with `hEU a b _ ih`. Establish `hLw : ∀ u ∈ L, (∃ t : KK O, u v = t • v) ∨ ∃ ν : Fin n → ℤ, ∑ c : Fin n, ((c : ℕ) : ℤ) * lam c < ∑ c : Fin n, ((c : ℕ) : ℤ) * ν c ∧ u v ∈ weightSp E ν`.

Introduce `u hu`. Proceed by induction on `hu using Submonoid.closure_induction_left with`. Consider the case `one => exact Or.inl ⟨1, by simp⟩`. Consider the case `mul_left x hx y _ ih`. Take `⟨a, b, hab, rfl⟩` from `hx`.

Rewrite using `[Module.End.mul_apply]`. Use `right`. Establish `hsum : ∀ ν : Fin n → ℤ, ∑ c : Fin n, ((c : ℕ) : ℤ) * (ν + Pi.single a 1 - Pi.single b 1 : Fin n → ℤ) c = ∑ c : Fin n, ((c : ℕ) : ℤ) * ν c + ((a : ℕ) : ℤ) - ((b : ℕ) : ℤ)`. Introduce `ν`. Simplify using `only [Pi.add_apply, Pi.sub_apply, mul_sub, mul_add, Finset.sum_add_distrib, Finset.sum_sub_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.

Establish `hpos : ((b : ℕ) : ℤ) < ((a : ℕ) : ℤ)`. Use `Fin.lt_def.1 hab` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Break down `ih with ⟨t, ht⟩ | ⟨ν, hν, hyν⟩` into its components or cases. Use `⟨lam + Pi.single a 1 - Pi.single b 1, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hsum]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[ht, map_smul]`. Conclude with `Submodule.smul_mem _ _ (hshift a b lam v hvl)`. Use `⟨ν + Pi.single a 1 - Pi.single b 1, ?_, hshift a b ν _ hyν⟩` and prove the remaining obligations.

Rewrite using `[hsum]`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨H, hHdef⟩ : ∃ H : Module.End (KK O) V, H = ∑ c : Fin n, ((c : ℕ) : KK O) • E c c` from `⟨_, rfl⟩`. Establish `hH : ∀ (ν : Fin n → ℤ) (y : V), y ∈ weightSp E ν → H y = ((∑ c : Fin n, ((c : ℕ) : ℤ) * ν c : ℤ) : KK O) • y`. Introduce `ν y hy`.

Rewrite `hy` using `[hwt]`. Rewrite using `[hHdef, LinearMap.sum_apply]`. Simplify using `only [LinearMap.smul_apply, hy, smul_smul]`. Rewrite using `[← Finset.sum_smul]`. Use `congr 1`.

Use `norm_cast`. Take `⟨μ0, hμ0⟩ : ∃ μ0 : KK O, μ0 = ((∑ c : Fin n, ((c : ℕ) : ℤ) * lam c : ℤ) : KK O)` from `⟨_, rfl⟩`. Establish `hUle : U ≤ Submodule.span (KK O) {v} ⊔ ⨆ (j : KK O) (_ : j ≠ μ0), H.eigenspace j`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨u, hu, rfl⟩`.

Break down `hLw u hu with ⟨t, ht⟩ | ⟨ν, hν, hyν⟩` into its components or cases. Rewrite using `[ht]`. Conclude with `Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v))`. Apply `Submodule.mem_sup_right` to reduce the goal to its premises. Establish `hne : ((∑ c : Fin n, ((c : ℕ) : ℤ) * ν c : ℤ) : KK O) ≠ μ0`.

Introduce `heq`. Rewrite `heq` using `[hμ0]`. Use `Int.cast_injective heq` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem hne ((Module.End.mem_eigenspace_iff).2 (hH ν _ hyν)))`.

Establish `hx' : x ∈ Submodule.span (KK O) {v} ⊔ ⨆ (j : KK O) (_ : j ≠ μ0), H.eigenspace j` using `hUle (hUtop ▸ Submodule.mem_top)`. Take `⟨y, hy, w, hw, hyw⟩` from `Submodule.mem_sup.1 hx'`. Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.1 hy`. Use `⟨c, ?_⟩` and prove the remaining obligations. Establish `hw' : w = x - c • v`.

Rewrite using `[← hyw]`. Normalize the expressions using the abelian group laws. Establish `hin1 : w ∈ H.eigenspace μ0`. Rewrite using `[hw', Module.End.mem_eigenspace_iff, map_sub, map_smul, hH lam x hx, hH lam v hvl, ← hμ0, smul_sub, smul_comm c μ0 v]`. Establish `h0 : w = 0` using `(Submodule.disjoint_def.1 ((Module.End.eigenspaces_iSupIndep H) μ0)) w hin1 hw`.

Rewrite `hw'` using `[h0]`. Conclude with `(sub_eq_zero.1 hw'.symm)`.
-/
theorem highestWeightSpace_eq_span_highestWeightVector [CharZero (KK O)] {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V} (hI : IsIrrHW E lam v) {x : V}
    (hx : x ∈ weightSp E lam) : ∃ c : KK O, x = c • v := by
  obtain ⟨hR, -, ⟨hv0, hvl, hraise⟩, hspan⟩ := hI
  have rel := hR.1
  have hwt : ∀ (ν : Fin n → ℤ) (y : V), y ∈ weightSp E ν ↔ ∀ a, E a a y = ((ν a : ℤ) : KK O) • y := by
    intro ν y
    unfold Formalism.MainNotions.G.weightSp
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply, sub_eq_zero]
  have hshift : ∀ (a b : Fin n) (ν : Fin n → ℤ) (y : V), y ∈ weightSp E ν →
      E a b y ∈ weightSp E (ν + Pi.single a 1 - Pi.single b 1) := by
    intro a b ν y hy
    rw [hwt] at hy ⊢
    intro c
    have h := congrArg (fun T : Module.End (KK O) V => T y) (rel c c a b)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, hy c, map_smul] at h
    rw [sub_eq_iff_eq_add] at h
    rw [h]
    rcases eq_or_ne c a with rfl | hca <;> rcases eq_or_ne b c with rfl | hbc
    · simp [Pi.single_apply]
    · simp only [eq_self_iff_true, if_true, if_neg hbc, LinearMap.zero_apply, sub_zero, Pi.add_apply,
        Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hbc.symm, Int.cast_add, Int.cast_one, add_smul,
        one_smul]
      abel
    · simp only [eq_self_iff_true, if_true, if_neg hca, LinearMap.zero_apply, zero_sub, Pi.add_apply,
        Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hca, add_zero, Int.cast_sub, Int.cast_one, sub_smul,
        one_smul]
      abel
    · simp [Pi.single_apply, hca, hbc, hbc.symm]
  let L : Submonoid (Module.End (KK O) V) := Submonoid.closure {T | ∃ a b, b < a ∧ T = E a b}
  let U : Submodule (KK O) V := Submodule.span (KK O) {y | ∃ u ∈ L, y = u v}
  have hLU : ∀ u ∈ L, ∀ y ∈ U, u y ∈ U := by
    intro u hu y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨w, hw, rfl⟩ := hz
      exact Submodule.subset_span ⟨u * w, L.mul_mem hu hw, rfl⟩
    | zero => simp
    | add y z _ _ hy hz =>
      rw [map_add]
      exact U.add_mem hy hz
    | smul c y _ hy =>
      rw [map_smul]
      exact U.smul_mem c hy
  have hv : v ∈ U := Submodule.subset_span ⟨1, L.one_mem, rfl⟩
  have base : ∀ c d, E c d v ∈ U := by
    intro c d
    rcases lt_trichotomy c d with h | rfl | h
    · rw [hraise c d h]
      exact U.zero_mem
    · rw [(hwt lam v).1 hvl c]
      exact U.smul_mem _ hv
    · exact Submodule.subset_span ⟨E c d, Submonoid.subset_closure ⟨c, d, h, rfl⟩, rfl⟩
  have key : ∀ u ∈ L, ∀ c d, E c d (u v) ∈ U := by
    intro u hu
    induction hu using Submonoid.closure_induction_left with
    | one =>
      intro c d
      exact base c d
    | mul_left x hx y hy ih =>
      intro c d
      obtain ⟨a, b, hab, rfl⟩ := hx
      rw [Module.End.mul_apply]
      have h := congrArg (fun T : Module.End (KK O) V => T (y v)) (rel c d a b)
      simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
      rw [sub_eq_iff_eq_add] at h
      rw [h]
      refine U.add_mem (U.sub_mem ?_ ?_) (hLU _ (Submonoid.subset_closure ⟨a, b, hab, rfl⟩) _ (ih c d))
      · split_ifs
        · exact ih c b
        · simp
      · split_ifs
        · exact ih a d
        · simp
  have hEU : ∀ c d, ∀ y ∈ U, E c d y ∈ U := by
    intro c d y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨u, hu, rfl⟩ := hz
      exact key u hu c d
    | zero => simp
    | add y z _ _ hy hz =>
      rw [map_add]
      exact U.add_mem hy hz
    | smul t y _ hy =>
      rw [map_smul]
      exact U.smul_mem t hy
  have hUtop : U = ⊤ := by
    rw [eq_top_iff, ← hspan]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, hu, rfl⟩
    induction hu using Submonoid.closure_induction_left with
    | one => exact hv
    | mul_left x hx y _ ih =>
      obtain ⟨⟨a, b⟩, rfl⟩ := hx
      rw [Module.End.mul_apply]
      exact hEU a b _ ih
  have hLw : ∀ u ∈ L, (∃ t : KK O, u v = t • v) ∨ ∃ ν : Fin n → ℤ,
      ∑ c : Fin n, ((c : ℕ) : ℤ) * lam c < ∑ c : Fin n, ((c : ℕ) : ℤ) * ν c ∧ u v ∈ weightSp E ν := by
    intro u hu
    induction hu using Submonoid.closure_induction_left with
    | one => exact Or.inl ⟨1, by simp⟩
    | mul_left x hx y _ ih =>
      obtain ⟨a, b, hab, rfl⟩ := hx
      rw [Module.End.mul_apply]
      right
      have hsum : ∀ ν : Fin n → ℤ, ∑ c : Fin n, ((c : ℕ) : ℤ) * (ν + Pi.single a 1 - Pi.single b 1 : Fin n → ℤ) c =
          ∑ c : Fin n, ((c : ℕ) : ℤ) * ν c + ((a : ℕ) : ℤ) - ((b : ℕ) : ℤ) := by
        intro ν
        simp only [Pi.add_apply, Pi.sub_apply, mul_sub, mul_add, Finset.sum_add_distrib,
          Finset.sum_sub_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
          Finset.mem_univ, if_true]
      have hpos : ((b : ℕ) : ℤ) < ((a : ℕ) : ℤ) := by
        have := Fin.lt_def.1 hab
        omega
      rcases ih with ⟨t, ht⟩ | ⟨ν, hν, hyν⟩
      · refine ⟨lam + Pi.single a 1 - Pi.single b 1, ?_, ?_⟩
        · rw [hsum]
          linarith
        · rw [ht, map_smul]
          exact Submodule.smul_mem _ _ (hshift a b lam v hvl)
      · refine ⟨ν + Pi.single a 1 - Pi.single b 1, ?_, hshift a b ν _ hyν⟩
        rw [hsum]
        linarith
  obtain ⟨H, hHdef⟩ : ∃ H : Module.End (KK O) V, H = ∑ c : Fin n, ((c : ℕ) : KK O) • E c c := ⟨_, rfl⟩
  have hH : ∀ (ν : Fin n → ℤ) (y : V), y ∈ weightSp E ν →
      H y = ((∑ c : Fin n, ((c : ℕ) : ℤ) * ν c : ℤ) : KK O) • y := by
    intro ν y hy
    rw [hwt] at hy
    rw [hHdef, LinearMap.sum_apply]
    simp only [LinearMap.smul_apply, hy, smul_smul]
    rw [← Finset.sum_smul]
    congr 1
    norm_cast
  obtain ⟨μ0, hμ0⟩ : ∃ μ0 : KK O, μ0 = ((∑ c : Fin n, ((c : ℕ) : ℤ) * lam c : ℤ) : KK O) := ⟨_, rfl⟩
  have hUle : U ≤ Submodule.span (KK O) {v} ⊔ ⨆ (j : KK O) (_ : j ≠ μ0), H.eigenspace j := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, hu, rfl⟩
    rcases hLw u hu with ⟨t, ht⟩ | ⟨ν, hν, hyν⟩
    · rw [ht]
      exact Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v))
    · apply Submodule.mem_sup_right
      have hne : ((∑ c : Fin n, ((c : ℕ) : ℤ) * ν c : ℤ) : KK O) ≠ μ0 := by
        intro heq
        rw [hμ0] at heq
        have := Int.cast_injective heq
        linarith
      exact Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem hne
        ((Module.End.mem_eigenspace_iff).2 (hH ν _ hyν)))
  have hx' : x ∈ Submodule.span (KK O) {v} ⊔ ⨆ (j : KK O) (_ : j ≠ μ0), H.eigenspace j :=
    hUle (hUtop ▸ Submodule.mem_top)
  obtain ⟨y, hy, w, hw, hyw⟩ := Submodule.mem_sup.1 hx'
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
  refine ⟨c, ?_⟩
  have hw' : w = x - c • v := by
    rw [← hyw]
    abel
  have hin1 : w ∈ H.eigenspace μ0 := by
    rw [hw', Module.End.mem_eigenspace_iff, map_sub, map_smul, hH lam x hx, hH lam v hvl, ← hμ0, smul_sub, smul_comm c μ0 v]
  have h0 : w = 0 := (Submodule.disjoint_def.1 ((Module.End.eigenspaces_iSupIndep H) μ0)) w hin1 hw
  rw [h0] at hw'
  exact (sub_eq_zero.1 hw'.symm)

end lattice

section gen

variable {n : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {V : Type} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

/- English proof (translation)
Establish `hfd : FiniteDimensional (KK O) V` using `irreducible_highest_weight_findim hI`. Use `set G' : Submodule (KK O) (Module.Dual (KK O) V) := Submodule.span (KK O) {x | ∃ u ∈ Umon (dualOps E), x = u v'} with hG'`. Establish `hG'st : ∀ a b, ∀ φ ∈ G', dualOps E a b φ ∈ G'`. Introduce `a b φ hφ`. Proceed by induction on `hφ using Submodule.span_induction with`.

Consider the case `mem y hy`. Take `⟨u, hu, rfl⟩` from `hy`. Conclude with `Submodule.subset_span ⟨dualOps E a b * u, Submonoid.mul_mem _ (Submonoid.subset_closure ⟨(a, b), rfl⟩) hu, rfl⟩`. Consider the case `zero => rw [map_zero]`. Conclude with `Submodule.zero_mem _`.

Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul c x _ hx => rw [map_smul]`. Conclude with `Submodule.smul_mem _ _ hx`. Establish `hv'G : v' ∈ G'` using `Submodule.subset_span ⟨1, Submonoid.one_mem _, rfl⟩`.

Use `set Z : Submodule (KK O) V := G'.dualCoannihilator with hZ`. Establish `hZst : ∀ a b, ∀ x ∈ Z, E a b x ∈ Z`. Introduce `a b x hx`. Rewrite `hx`, the goal using `[hZ, Submodule.mem_dualCoannihilator]`. Introduce `φ hφ`.

Use `hx _ (hG'st a b φ hφ)` as an intermediate fact. Rewrite `this` using `[dualOperators_apply, neg_eq_zero]`. Conclude with `this`. Take `⟨Z', hc, hZ'st⟩` from `weight_condition_from_integral_form D (KK O) V n E hI.1 Z hZst`. Establish `hvtop : v ∈ Z ⊔ Z'` using `hc.sup_eq_top ▸ Submodule.mem_top`.

Take `⟨z, hz, z', hz', hsum⟩` from `Submodule.mem_sup.1 hvtop`. Establish `hzw : z ∈ weightSp E mu`. Rewrite using `[mem_weightSpace_iff_diag_scalar]`. Introduce `a`. Establish `h1 : E a a z - (mu a : KK O) • z ∈ Z` using `Submodule.sub_mem _ (hZst a a z hz) (Submodule.smul_mem _ _ hz)`.

Establish `h2 : E a a z' - (mu a : KK O) • z' ∈ Z'` using `Submodule.sub_mem _ (hZ'st a a z' hz') (Submodule.smul_mem _ _ hz')`. Establish `h3 : (E a a z - (mu a : KK O) • z) + (E a a z' - (mu a : KK O) • z') = 0`. Use `mem_weightSpace_iff_diag_scalar.1 hI.2.2.1.2.1 a` as an intermediate fact. Rewrite `this` using `[← hsum, map_add, smul_add]`. Rewrite `this` using `[← sub_eq_zero]`.

Rewrite using `[← this]`. Normalize the expressions using the abelian group laws. Establish `h4 : E a a z - (mu a : KK O) • z = -(E a a z' - (mu a : KK O) • z')` using `eq_neg_of_add_eq_zero_left h3`. Establish `h5 : E a a z - (mu a : KK O) • z ∈ Z ⊓ Z'` using `⟨h1, h4 ▸ Submodule.neg_mem _ h2⟩`. Rewrite `h5` using `[hc.inf_eq_bot, Submodule.mem_bot]`.

Conclude with `sub_eq_zero.1 h5`. Take `⟨c, hcz⟩` from `highestWeightSpace_eq_span_highestWeightVector hI hzw`. Establish `hZbot : Z = ⊥`. Distinguish the cases in `hc0 : c = 0`. Establish `hvZ' : v ∈ Z'`.

Rewrite using `[← hsum, hcz, hc0, zero_smul, zero_add]`. Conclude with `hz'`. Establish `htop` using `irreducible_stable_contains_eq_top hI hZ'st hvZ'`. Use `hc.inf_eq_bot` as an intermediate fact. Rewrite `this` using `[htop, inf_top_eq]`. Then use the resulting hypothesis.

It suffices to derive a contradiction. Establish `hvZ : v ∈ Z`. Establish `: v = c⁻¹ • z` using `by rw [hcz, smul_smul, inv_mul_cancel₀ hc0, one_smul]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ hz`.

Establish `htop` using `irreducible_stable_contains_eq_top hI hZst hvZ`. Apply `hv0` to reduce the goal to its premises. Use extensionality with `x`. Establish `hx : x ∈ Z` using `htop ▸ Submodule.mem_top`. Rewrite `hx` using `[hZ, Submodule.mem_dualCoannihilator]`.

Conclude with `hx v' hv'G`. Establish `h6` using `Subspace.dualCoannihilator_dualAnnihilator_eq (W := G')`. Rewrite `h6` using `[← hZ, hZbot, Submodule.dualAnnihilator_bot]`. Conclude with `h6.symm`.
-/
theorem contragredient_span_highestWeight_eq_top (D : Formalism.BasicNotions.D7) [CharZero (KK O)] {E : GLOps n (KK O) V} {mu : Fin n → ℤ} {v : V}
    {v' : Module.Dual (KK O) V} (hI : IsIrrHW E mu v) (hv0 : v' ≠ 0) :
    Submodule.span (KK O) {x | ∃ u ∈ Umon (dualOps E), x = u v'} = ⊤ := by
  have hfd : FiniteDimensional (KK O) V := irreducible_highest_weight_findim hI
  set G' : Submodule (KK O) (Module.Dual (KK O) V) :=
    Submodule.span (KK O) {x | ∃ u ∈ Umon (dualOps E), x = u v'} with hG'
  have hG'st : ∀ a b, ∀ φ ∈ G', dualOps E a b φ ∈ G' := by
    intro a b φ hφ
    induction hφ using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨u, hu, rfl⟩ := hy
      exact Submodule.subset_span ⟨dualOps E a b * u,
        Submonoid.mul_mem _ (Submonoid.subset_closure ⟨(a, b), rfl⟩) hu, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  have hv'G : v' ∈ G' := Submodule.subset_span ⟨1, Submonoid.one_mem _, rfl⟩
  set Z : Submodule (KK O) V := G'.dualCoannihilator with hZ
  have hZst : ∀ a b, ∀ x ∈ Z, E a b x ∈ Z := by
    intro a b x hx
    rw [hZ, Submodule.mem_dualCoannihilator] at hx ⊢
    intro φ hφ
    have := hx _ (hG'st a b φ hφ)
    rw [dualOperators_apply, neg_eq_zero] at this
    exact this
  obtain ⟨Z', hc, hZ'st⟩ := weight_condition_from_integral_form D (KK O) V n E hI.1 Z hZst
  have hvtop : v ∈ Z ⊔ Z' := hc.sup_eq_top ▸ Submodule.mem_top
  obtain ⟨z, hz, z', hz', hsum⟩ := Submodule.mem_sup.1 hvtop
  have hzw : z ∈ weightSp E mu := by
    rw [mem_weightSpace_iff_diag_scalar]
    intro a
    have h1 : E a a z - (mu a : KK O) • z ∈ Z := Submodule.sub_mem _ (hZst a a z hz) (Submodule.smul_mem _ _ hz)
    have h2 : E a a z' - (mu a : KK O) • z' ∈ Z' :=
      Submodule.sub_mem _ (hZ'st a a z' hz') (Submodule.smul_mem _ _ hz')
    have h3 : (E a a z - (mu a : KK O) • z) + (E a a z' - (mu a : KK O) • z') = 0 := by
      have := mem_weightSpace_iff_diag_scalar.1 hI.2.2.1.2.1 a
      rw [← hsum, map_add, smul_add] at this
      rw [← sub_eq_zero] at this
      rw [← this]
      abel
    have h4 : E a a z - (mu a : KK O) • z = -(E a a z' - (mu a : KK O) • z') := eq_neg_of_add_eq_zero_left h3
    have h5 : E a a z - (mu a : KK O) • z ∈ Z ⊓ Z' := ⟨h1, h4 ▸ Submodule.neg_mem _ h2⟩
    rw [hc.inf_eq_bot, Submodule.mem_bot] at h5
    exact sub_eq_zero.1 h5
  obtain ⟨c, hcz⟩ := highestWeightSpace_eq_span_highestWeightVector hI hzw
  have hZbot : Z = ⊥ := by
    by_cases hc0 : c = 0
    · have hvZ' : v ∈ Z' := by
        rw [← hsum, hcz, hc0, zero_smul, zero_add]
        exact hz'
      have htop := irreducible_stable_contains_eq_top hI hZ'st hvZ'
      have := hc.inf_eq_bot
      rwa [htop, inf_top_eq] at this
    · exfalso
      have hvZ : v ∈ Z := by
        have : v = c⁻¹ • z := by rw [hcz, smul_smul, inv_mul_cancel₀ hc0, one_smul]
        rw [this]
        exact Submodule.smul_mem _ _ hz
      have htop := irreducible_stable_contains_eq_top hI hZst hvZ
      apply hv0
      ext x
      have hx : x ∈ Z := htop ▸ Submodule.mem_top
      rw [hZ, Submodule.mem_dualCoannihilator] at hx
      exact hx v' hv'G
  have h6 := Subspace.dualCoannihilator_dualAnnihilator_eq (W := G')
  rw [← hZ, hZbot, Submodule.dualAnnihilator_bot] at h6
  exact h6.symm

end gen

/- English proof (translation)
Unfold `Formalism.MainNotions.G.ColumnFamilies.ContragredientIrreducibleGeneratedByHighestWeight`. Introduce `p _ O _ _ _ _ S n V _ _ _ _ E mu v v' hI hH`. Use `haveI : CharZero (KK O) := charZero_of_injective_algebraMap (IsFractionRing.injective O (KK O))`. Take `⟨W, hWf, hvW, hWs⟩` from `hI.1.2.1 v`. Use `haveI : FiniteDimensional (KK O) V := by`.

Establish `hle : (⊤ : Submodule (KK O) V) ≤ W`. Rewrite using `[← hI.2.2.2, Submodule.span_le]`. Introduce and unpack `_ ⟨u, hu, rfl⟩`. Proceed by induction on `hu using Submonoid.closure_induction_left with`. Consider the case `one => exact hvW`.

Consider the case `mul_left x hx y _ ih`. Take `⟨⟨a, b⟩, rfl⟩` from `hx`. Conclude with `hWs a b _ ih`. Establish `hWt : W = ⊤` using `top_le_iff.1 hle`. Substitute `hWt` using the available equality.

Conclude with `Module.Finite.equiv (LinearEquiv.ofTop (⊤ : Submodule (KK O) V) rfl)`. Conclude with `⟨dualOperators_isGLRep E hI.1, dominant_dualWeight hI.2.1, hH, contragredient_span_highestWeight_eq_top D hI hH.1⟩`.
-/
theorem contragredientIrreducible_generated (D : Formalism.BasicNotions.D7) : ContragredientIrreducibleGeneratedByHighestWeight := by
  unfold Formalism.MainNotions.G.ColumnFamilies.ContragredientIrreducibleGeneratedByHighestWeight
  intro p _ O _ _ _ _ S n V _ _ _ _ E mu v v' hI hH
  haveI : CharZero (KK O) := charZero_of_injective_algebraMap (IsFractionRing.injective O (KK O))
  obtain ⟨W, hWf, hvW, hWs⟩ := hI.1.2.1 v
  haveI : FiniteDimensional (KK O) V := by
    have hle : (⊤ : Submodule (KK O) V) ≤ W := by
      rw [← hI.2.2.2, Submodule.span_le]
      rintro _ ⟨u, hu, rfl⟩
      induction hu using Submonoid.closure_induction_left with
      | one => exact hvW
      | mul_left x hx y _ ih =>
        obtain ⟨⟨a, b⟩, rfl⟩ := hx
        exact hWs a b _ ih
    have hWt : W = ⊤ := top_le_iff.1 hle
    subst hWt
    exact Module.Finite.equiv (LinearEquiv.ofTop (⊤ : Submodule (KK O) V) rfl)
  exact ⟨dualOperators_isGLRep E hI.1, dominant_dualWeight hI.2.1, hH, contragredient_span_highestWeight_eq_top D hI hH.1⟩

/- English proof (translation)
Introduce `p _ O _ _ _ _ S n V _ _ _ _ E mu v v' hI hv'`. Establish `hcz : CharZero (KK O)` using `charZero_of_injective_algebraMap (IsFractionRing.injective O (KK O))`. Establish `hI'` using `contragredientIrreducible_generated D p O S n V E mu v v' hI hv'`. Establish `hdw : dualWt mu = -lowWt mu` using `rfl`. Prove the components needed by the constructor for the conclusion.

Introduce `x hx hvx`. Rewrite using `[← Module.forall_dual_apply_eq_zero_iff (KK O) x]`. Introduce `φ`. Establish `hφ : φ ∈ ⨆ nu : Fin n → ℤ, weightSp (dualOps E) nu` using `hI'.1.2.2 ▸ Submodule.mem_top`. Proceed by induction on `hφ using Submodule.iSup_induction' with`.

Consider the case `mem nu ψ hψ`. Distinguish the cases in `hnu : nu = dualWt mu`. Substitute `hnu` using the available equality. Take `⟨c, rfl⟩` from `highestWeightSpace_eq_span_highestWeightVector hI' hψ`. Rewrite using `[LinearMap.smul_apply, hvx, smul_zero]`.

Conclude with `dual_weightVector_apply_eq_zero_of_ne_neg E hψ hx (fun h => hnu (h.trans hdw.symm))`. Consider the case `zero => rfl`. Consider the case `add a b _ _ ha hb => rw [LinearMap.add_apply, ha, hb, add_zero]`. Introduce `nu hnu x hx`. Use `dual_weightVector_apply_eq_zero_of_ne_neg E hv'.2.1 hx (fun h => hnu ?_)` and prove the remaining obligations.

Establish `: -lowWt mu = -nu` using `hdw.symm.trans h`. Conclude with `(neg_injective this).symm`.
-/
theorem dualFunctional_lowestWeight_injective (D : Formalism.BasicNotions.D7) : DualFunctionalInjectiveOnLowestWeightSpace := by
  intro p _ O _ _ _ _ S n V _ _ _ _ E mu v v' hI hv'
  have hcz : CharZero (KK O) := charZero_of_injective_algebraMap (IsFractionRing.injective O (KK O))
  have hI' := contragredientIrreducible_generated D p O S n V E mu v v' hI hv'
  have hdw : dualWt mu = -lowWt mu := rfl
  constructor
  · intro x hx hvx
    rw [← Module.forall_dual_apply_eq_zero_iff (KK O) x]
    intro φ
    have hφ : φ ∈ ⨆ nu : Fin n → ℤ, weightSp (dualOps E) nu := hI'.1.2.2 ▸ Submodule.mem_top
    induction hφ using Submodule.iSup_induction' with
    | mem nu ψ hψ =>
      by_cases hnu : nu = dualWt mu
      · subst hnu
        obtain ⟨c, rfl⟩ := highestWeightSpace_eq_span_highestWeightVector hI' hψ
        rw [LinearMap.smul_apply, hvx, smul_zero]
      · exact dual_weightVector_apply_eq_zero_of_ne_neg E hψ hx (fun h => hnu (h.trans hdw.symm))
    | zero => rfl
    | add a b _ _ ha hb => rw [LinearMap.add_apply, ha, hb, add_zero]
  · intro nu hnu x hx
    refine dual_weightVector_apply_eq_zero_of_ne_neg E hv'.2.1 hx (fun h => hnu ?_)
    have : -lowWt mu = -nu := hdw.symm.trans h
    exact (neg_injective this).symm

end Formalism.MainNotions.G.ColumnFamilies
