import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClassPresBasic
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalFamilyOrthogonalDecomposition

noncomputable section

open Polynomial Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links

namespace GlobalTheory.AdjBlock

section Linear

variable {K V H E : Type} [Field K] [AddCommGroup V] [Module K V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {σ : K →+* ℂ} {j : V →ₛₗ[σ] H} {ι : Type} [Fintype ι] {b : Module.Basis ι K V}

/- English proof (translation)
Use `conv_lhs => rw [← b.sum_repr v]`. Simplify using `only [map_sum, map_smulₛₗ]`.
-/
theorem map_eq_sum (j : V →ₛₗ[σ] H) (b : Module.Basis ι K V) (v : V) : j v = ∑ i, σ (b.repr v i) • j (b i) := by
  conv_lhs => rw [← b.sum_repr v]
  simp only [map_sum, map_smulₛₗ]

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `v hv`. Rewrite `hv` using `[map_eq_sum j b]`. Establish `h` using `Fintype.linearIndependent_iff.1 hli _ hv`. Use `b.repr.injective (Finsupp.ext fun i => ?_)` and prove the remaining obligations.

Simplify using `using h i`.
-/
theorem injective_of_li (hli : LinearIndependent ℂ fun i => j (b i)) : Function.Injective j := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  rw [map_eq_sum j b] at hv
  have h := Fintype.linearIndependent_iff.1 hli _ hv
  refine b.repr.injective (Finsupp.ext fun i => ?_)
  simpa using h i

/- English proof (translation)
Establish `h2 : ⊤ ≤ Submodule.span ℂ (Set.range fun i => j (b i))`. Rewrite using `[← hsp, Submodule.span_le]`. Introduce and unpack `_ ⟨v, rfl⟩`. Rewrite using `[map_eq_sum j b]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.

Use `⟨(Module.Basis.mk hli h2).constr ℂ fun i => j (f (b i)), fun v => ?_⟩` and prove the remaining obligations. Establish `h3 : ∀ i, ((Module.Basis.mk hli h2).constr ℂ fun i => j (f (b i))) (j (b i)) = j (f (b i))` using `fun i => by`. Use `(Module.Basis.mk hli h2).constr_basis ℂ (fun i => j (f (b i))) i` as an intermediate fact. Rewrite `this` using `[Module.Basis.mk_apply]`. Then use the resulting hypothesis. Rewrite using `[map_eq_sum j b v, map_sum]`.

Use `conv_rhs => rw [← b.sum_repr v]`. Simplify using `only [map_sum, map_smul, map_smulₛₗ, h3]`.
-/
theorem exists_cx (hli : LinearIndependent ℂ fun i => j (b i)) (hsp : Submodule.span ℂ (Set.range j) = ⊤)
    (f : Module.End K V) : ∃ U : Module.End ℂ H, ∀ v, U (j v) = j (f v) := by
  have h2 : ⊤ ≤ Submodule.span ℂ (Set.range fun i => j (b i)) := by
    rw [← hsp, Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    rw [map_eq_sum j b]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨(Module.Basis.mk hli h2).constr ℂ fun i => j (f (b i)), fun v => ?_⟩
  have h3 : ∀ i, ((Module.Basis.mk hli h2).constr ℂ fun i => j (f (b i))) (j (b i)) = j (f (b i)) := fun i => by
    have := (Module.Basis.mk hli h2).constr_basis ℂ (fun i => j (f (b i))) i
    rwa [Module.Basis.mk_apply] at this
  rw [map_eq_sum j b v, map_sum]
  conv_rhs => rw [← b.sum_repr v]
  simp only [map_sum, map_smul, map_smulₛₗ, h3]

/- English proof (translation)
The claim follows from `LinearMap.ext_on_range hsp h`.
-/
theorem ext_of_span {X : Type} [AddCommGroup X] [Module ℂ X] (hsp : Submodule.span ℂ (Set.range j) = ⊤)
    {f g : H →ₗ[ℂ] X} (h : ∀ v, f (j v) = g (j v)) : f = g :=
  LinearMap.ext_on_range hsp h

/- English proof (translation)
Establish `hcU : Col.PairComm U` using `fun i i' => ext_of_span hsp fun v => by`. Simplify using `only [Module.End.mul_apply, hU]`. Conclude with `congrArg j (LinearMap.congr_fun (hc i i').eq v)`. Establish `h1 : ∀ x, Col.eigAt op x ≤ (Col.eigAt U fun i => σ (x i)).comap j`. Introduce `x v hv`.

Rewrite using `[Submodule.mem_comap, Col.eigAt, Submodule.mem_iInf]`. Introduce `i`. Take `⟨k, hk⟩` from `(Module.End.mem_maxGenEigenspace _ _ _).1 (Col.eigAt_le op x i hv)`. Use `(Module.End.mem_maxGenEigenspace _ _ _).2 ⟨k, ?_⟩` and prove the remaining obligations. Establish `: ∀ (k : ℕ) w, ((U i - σ (x i) • (1 : Module.End ℂ H)) ^ k) (j w) = j (((op i - x i • (1 : Module.End K V)) ^ k) w)`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro w`. Simplify using the standard rewrite rules. Consider the case `succ k ih`.

Introduce `w`. Rewrite using `[pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ← ih]`. Simplify using `[hU, map_smulₛₗ]`. Rewrite using `[this, hk, map_zero]`. Establish `h2 : ∀ Q : (I → K) → Prop, Col.eigSum op Q ≤ (Col.eigSum U fun y => ∃ x, Q x ∧ y = fun i => σ (x i)).comap j` using `fun Q => iSup₂_le fun x hx => (h1 x).trans (Submodule.comap_mono (Col.eigAt_le_eigSum ⟨x, hx, rfl⟩))`.

Introduce `v hv`. Take `⟨a, ha, c, hc', rfl⟩` from `Submodule.mem_sup.1 ((Col.isCompl_eigSum hc hs C).sup_eq_top ▸ (Submodule.mem_top : v ∈ (⊤ : Submodule K V)))`. Establish `h3 : j c ∈ Col.eigSum U fun y => CC y ∨ ∃ x, C x ∧ y = fun i => σ (x i)`. Rewrite using `[Col.eigSum_or]`. Establish `: j c = j (a + c) - j a` using `by rw [map_add]; abel`.

Rewrite using `[this]`. Conclude with `Submodule.sub_mem _ (Submodule.mem_sup_left hv) (Submodule.mem_sup_right (h2 _ ha))`. Establish `h4 : Disjoint (Col.eigSum U fun y => CC y ∨ ∃ x, C x ∧ y = fun i => σ (x i)) (Col.eigSum U fun y => ∃ x, ¬ C x ∧ y = fun i => σ (x i))`. Use `Col.disjoint_eigSum hcU ?_` and prove the remaining obligations. Introduce and unpack `y hy ⟨x, hx, rfl⟩`.

Break down `hy with hy | ⟨x', hx', he⟩` into its components or cases. Conclude with `hx (hC x hy)`. Establish `: x = x'` using `funext fun i => σ.injective (congrFun he i)`. Conclude with `hx (this ▸ hx')`. Establish `h5 : j c = 0` using `(Submodule.disjoint_def.1 h4) _ h3 (h2 _ hc')`.

Establish `h6 : c = 0` using `hj (by rw [h5, map_zero])`. Rewrite using `[h6, add_zero]`. Conclude with `ha`.
-/
theorem comap_eigSum_le {I : Type} [FiniteDimensional K V] [FiniteDimensional ℂ H] (hj : Function.Injective j)
    (hsp : Submodule.span ℂ (Set.range j) = ⊤) {op : I → Module.End K V} {U : I → Module.End ℂ H}
    (hU : ∀ i v, U i (j v) = j (op i v)) (hc : Col.PairComm op) (hs : Col.SplitOver op)
    {C : (I → K) → Prop} {CC : (I → ℂ) → Prop} (hC : ∀ x, CC (fun i => σ (x i)) → C x) :
    (Col.eigSum U CC).comap j ≤ Col.eigSum op C := by
  have hcU : Col.PairComm U := fun i i' => ext_of_span hsp fun v => by
    simp only [Module.End.mul_apply, hU]
    exact congrArg j (LinearMap.congr_fun (hc i i').eq v)
  have h1 : ∀ x, Col.eigAt op x ≤ (Col.eigAt U fun i => σ (x i)).comap j := by
    intro x v hv
    rw [Submodule.mem_comap, Col.eigAt, Submodule.mem_iInf]
    intro i
    obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 (Col.eigAt_le op x i hv)
    refine (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨k, ?_⟩
    have : ∀ (k : ℕ) w, ((U i - σ (x i) • (1 : Module.End ℂ H)) ^ k) (j w) =
        j (((op i - x i • (1 : Module.End K V)) ^ k) w) := by
      intro k
      induction k with
      | zero => intro w; simp
      | succ k ih =>
        intro w
        rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ← ih]
        simp [hU, map_smulₛₗ]
    rw [this, hk, map_zero]
  have h2 : ∀ Q : (I → K) → Prop, Col.eigSum op Q ≤
      (Col.eigSum U fun y => ∃ x, Q x ∧ y = fun i => σ (x i)).comap j := fun Q =>
    iSup₂_le fun x hx => (h1 x).trans (Submodule.comap_mono (Col.eigAt_le_eigSum ⟨x, hx, rfl⟩))
  intro v hv
  obtain ⟨a, ha, c, hc', rfl⟩ := Submodule.mem_sup.1
    ((Col.isCompl_eigSum hc hs C).sup_eq_top ▸ (Submodule.mem_top : v ∈ (⊤ : Submodule K V)))
  have h3 : j c ∈ Col.eigSum U fun y => CC y ∨ ∃ x, C x ∧ y = fun i => σ (x i) := by
    rw [Col.eigSum_or]
    have : j c = j (a + c) - j a := by rw [map_add]; abel
    rw [this]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left hv) (Submodule.mem_sup_right (h2 _ ha))
  have h4 : Disjoint (Col.eigSum U fun y => CC y ∨ ∃ x, C x ∧ y = fun i => σ (x i))
      (Col.eigSum U fun y => ∃ x, ¬ C x ∧ y = fun i => σ (x i)) := by
    refine Col.disjoint_eigSum hcU ?_
    rintro y hy ⟨x, hx, rfl⟩
    rcases hy with hy | ⟨x', hx', he⟩
    · exact hx (hC x hy)
    · have : x = x' := funext fun i => σ.injective (congrFun he i)
      exact hx (this ▸ hx')
  have h5 : j c = 0 := (Submodule.disjoint_def.1 h4) _ h3 (h2 _ hc')
  have h6 : c = 0 := hj (by rw [h5, map_zero])
  rw [h6, add_zero]
  exact ha

/- English proof (translation)
Introduce and unpack `v ⟨u, hu⟩`. Use `⟨v, hj ?_⟩` and prove the remaining obligations. Establish `h1 : innerₛₗ ℂ (j (e v)) = innerₛₗ ℂ (j v)` using `ext_of_span hsp fun w => by`. Simplify using `only [innerₛₗ_apply_apply]`. Rewrite using `[he, ← hu, LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_left, hΘ]`.

Conclude with `ext_inner_right ℂ fun w => LinearMap.congr_fun h1 w`.
-/
theorem comap_range_adjoint_le [FiniteDimensional ℂ H] [FiniteDimensional ℂ E] (hj : Function.Injective j)
    (hsp : Submodule.span ℂ (Set.range j) = ⊤) {e : Module.End K V}
    (he : ∀ v w, inner ℂ (j (e v)) (j w) = inner ℂ (j v) (j (e w))) {Θ : H →ₗ[ℂ] E}
    (hΘ : ∀ v, Θ (j (e v)) = Θ (j v)) :
    (LinearMap.range (LinearMap.adjoint Θ)).comap j ≤ LinearMap.range e := by
  rintro v ⟨u, hu⟩
  refine ⟨v, hj ?_⟩
  have h1 : innerₛₗ ℂ (j (e v)) = innerₛₗ ℂ (j v) := ext_of_span hsp fun w => by
    simp only [innerₛₗ_apply_apply]
    rw [he, ← hu, LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_left, hΘ]
  exact ext_inner_right ℂ fun w => LinearMap.congr_fun h1 w

/- English proof (translation)
Simplify using `only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smulₛₗ, sum_inner, inner_sum, inner_smul_left, inner_smul_right, ha]`. Use `Fintype.sum_equiv (Equiv.inv G) _ _ fun g => ?_` and prove the remaining obligations. Rewrite using `[Equiv.inv_apply, ← hr g v, ← Module.End.mul_apply (r g) (r g⁻¹), ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]`.
-/
theorem sum_selfAdj {G : Type} [Group G] [Fintype G] (r : Representation K G V) (a : G → K)
    (ha : ∀ g, starRingEnd ℂ (σ (a g)) = σ (a g⁻¹))
    (hr : ∀ g v w, inner ℂ (j (r g v)) (j (r g w)) = inner ℂ (j v) (j w)) (v w : V) :
    inner ℂ (j ((∑ g, a g • r g) v)) (j w) = inner ℂ (j v) (j ((∑ g, a g • r g) w)) := by
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smulₛₗ, sum_inner, inner_sum, inner_smul_left,
    inner_smul_right, ha]
  refine Fintype.sum_equiv (Equiv.inv G) _ _ fun g => ?_
  rw [Equiv.inv_apply, ← hr g v, ← Module.End.mul_apply (r g) (r g⁻¹), ← map_mul, mul_inv_cancel, map_one,
    Module.End.one_apply]

end Linear

section Poly

def eigOf (q : ℕ) (g : ℂ[X]) (k : ℕ) : ℂ := g.coeff k / ((-1) ^ k * (q : ℂ) ^ (k * (k - 1) / 2))

/- English proof (translation)
Simplify using `only [Col.heckePolyOf, finsetSum_coeff, coeff_C_mul_X_pow]`. Rewrite using `[Finset.sum_ite_eq]`. Simplify using `only [Finset.mem_range, Nat.lt_succ_iff]`.
-/
theorem coeff_heckePolyOf {L : Type} [Field L] (n q : ℕ) (a : ℕ → L) (k : ℕ) :
    (Col.heckePolyOf n q a).coeff k = if k ≤ n then (-1) ^ k * (q : L) ^ (k * (k - 1) / 2) * a k else 0 := by
  simp only [Col.heckePolyOf, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_range, Nat.lt_succ_iff]

/- English proof (translation)
The claim follows from `natDegree_le_iff_coeff_eq_zero.2 fun k hk => by rw [coeff_heckePolyOf, if_neg (by omega)]`.
-/
theorem natDegree_heckePolyOf {L : Type} [Field L] (n q : ℕ) (a : ℕ → L) : (Col.heckePolyOf n q a).natDegree ≤ n :=
  natDegree_le_iff_coeff_eq_zero.2 fun k hk => by rw [coeff_heckePolyOf, if_neg (by omega)]

/- English proof (translation)
Establish `: (q : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hq.ne'`. Rewrite using `[eigOf, coeff_heckePolyOf, if_pos hk]`. Clear the denominators using the available nonvanishing facts.
-/
theorem eigOf_heckePolyOf {n q : ℕ} (hq : 0 < q) (a : ℕ → ℂ) {k : ℕ} (hk : k ≤ n) :
    eigOf q (Col.heckePolyOf n q a) k = a k := by
  have : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq.ne'
  rw [eigOf, coeff_heckePolyOf, if_pos hk]
  field_simp

/- English proof (translation)
Establish `: (q : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hq.ne'`. Use extensionality with `k`. Rewrite using `[coeff_heckePolyOf]`. Use `split_ifs with h`. Rewrite using `[eigOf]`.

Clear the denominators using the available nonvanishing facts. Conclude with `(coeff_eq_zero_of_natDegree_lt (by omega)).symm`.
-/
theorem heckePolyOf_eigOf {n q : ℕ} (hq : 0 < q) {g : ℂ[X]} (hg : g.natDegree ≤ n) :
    Col.heckePolyOf n q (eigOf q g) = g := by
  have : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq.ne'
  ext k
  rw [coeff_heckePolyOf]
  split_ifs with h
  · rw [eigOf]; field_simp
  · exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm

/- English proof (translation)
Proceed by induction on `bl with`. Consider the case `nil => simp`. Consider the case `cons ν bl ih`. Rewrite using `[List.map_cons, List.prod_cons, List.length_cons, mul_coeff_zero, ih.2]`. Use `⟨natDegree_mul_le.trans ?_, ?_⟩` and prove the remaining obligations.

Establish `: (Col.blockPoly (ν P) q t).natDegree ≤ t`. Use `(natDegree_prod_le _ _).trans ((Finset.sum_le_card_nsmul _ _ 1 fun c _ => ?_).trans (by simp))` and prove the remaining obligations. Use `compute_degree`. Use polynomial arithmetic with `[ih.1]`. Rewrite using `[mul_one, coeff_zero_eq_eval_zero]`.

Simplify using `[Col.blockPoly, eval_prod]`.
-/
theorem blocks_spec {L Pl : Type} [Field L] (bl : List (Pl → L)) (P : Pl) (q t : ℕ) :
    (bl.map fun ν => Col.blockPoly (ν P) q t).prod.natDegree ≤ bl.length * t ∧
      (bl.map fun ν => Col.blockPoly (ν P) q t).prod.coeff 0 = 1 := by
  induction bl with
  | nil => simp
  | cons ν bl ih =>
    rw [List.map_cons, List.prod_cons, List.length_cons, mul_coeff_zero, ih.2]
    refine ⟨natDegree_mul_le.trans ?_, ?_⟩
    · have : (Col.blockPoly (ν P) q t).natDegree ≤ t := by
        refine (natDegree_prod_le _ _).trans ((Finset.sum_le_card_nsmul _ _ 1 fun c _ => ?_).trans (by simp))
        compute_degree
      nlinarith [ih.1]
    · rw [mul_one, coeff_zero_eq_eval_zero]
      simp [Col.blockPoly, eval_prod]

end Poly

section Core

variable {K V H E Pl : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  {σ : K →+* ℂ} {j : V →ₛₗ[σ] H} {ι : Type} [Fintype ι] {b : Module.Basis ι K V}

/- English proof (translation)
Use `choose U hU using fun i => exists_cx hli hsp (op i)`. Establish `hd : (Col.eigSum U (Col.HasBlocks n q t (bl.map fun ν P => σ (ν P)))).comap j ≤ Col.eigSum op (Col.HasBlocks n q t bl)` using `comap_eigSum_le (injective_of_li hli) hsp hU hc hs fun x hx => (Col.hasBlocks_map σ n q t bl x).1 hx`. Use `le_trans (Submodule.comap_mono ?_) hd` and prove the remaining obligations. Establish `htop : ⨆ c, Col.eigAt T c = ⊤` using `Col.iSup_eigAt_eq_top hTc fun i => Module.End.iSup_maxGenEigenspace_eq_top (T i)`. Rewrite using `[LinearMap.range_eq_map, ← htop, Submodule.map_iSup]`.

Use `iSup_le fun c => ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨e, he, rfl⟩`. Distinguish the cases in `he0 : e = 0`. Rewrite using `[he0, map_zero]`. Conclude with `Submodule.zero_mem _`.

Establish `hce : ∀ i, T i e = c i • e` using `fun i => by`. Use `Col.eigAt_le T c i he` as an intermediate fact. Rewrite `this` using `[NormalFamily.maxGenEigenspace_eq (hTn i), Module.End.mem_eigenspace_iff]`. Then use the resulting hypothesis. Establish `hc0 : ∀ P, c (P, 0) = 1` using `fun P => by`. Use `hce (P, 0)` as an intermediate fact.

Rewrite `this` using `[hT0, Module.End.one_apply]`. Conclude with `smul_left_injective ℂ he0 (by simpa using this.symm)`. Take `⟨g, hg⟩ : ∃ g : Pl → ℂ[X], ∀ P, g P = (Col.heckePoly r q c P).comp (C (s P) * X) * ((bl.map fun ν => Col.blockPoly (ν P) (q P) t).prod).map σ` from `⟨_, fun _ => rfl⟩`. Establish `hdeg : ∀ P, (g P).natDegree ≤ n` using `fun P => by`. Rewrite using `[hg]`.

Use `natDegree_mul_le.trans ?_` and prove the remaining obligations. Rewrite using `[hn]`. Use `add_le_add (natDegree_comp_le.trans ?_) (natDegree_map_le.trans (blocks_spec bl P _ t).1)` and prove the remaining obligations. Establish `h1 : (C (s P) * X).natDegree ≤ 1` using `by compute_degree`. Conclude with `(Nat.mul_le_mul (natDegree_heckePolyOf _ _ _) h1).trans (by simp)`.

Establish `hg0 : ∀ P, (g P).coeff 0 = 1` using `fun P => by`. Rewrite using `[hg, mul_coeff_zero, coeff_map, (blocks_spec bl P _ t).2, map_one, mul_one, coeff_zero_eq_eval_zero, eval_comp]`. Simplify using `only [eval_mul, eval_C, eval_X, mul_zero]`. Rewrite using `[← coeff_zero_eq_eval_zero, Col.heckePoly, coeff_heckePolyOf, if_pos (Nat.zero_le _), hc0]`. Simplify using the standard rewrite rules.

Use `Col.eigAt_le_eigSum (x := fun i => eigOf (q i.1) (g i.1) i.2) (fun P => ?_) (Col.mem_eigAt_of_forall_apply ?_)` and prove the remaining obligations. Use `show _ ∣ Col.heckePolyOf n (q P) (eigOf (q P) (g P))`. Rewrite using `[heckePolyOf_eigOf (hq P) (hdeg P)]`. Use `Dvd.intro_left ((Col.heckePoly r q c P).comp (C (s P) * X)) ?_` and prove the remaining obligations. Simplify using `only [hg, Polynomial.map_list_prod, List.map_map, Function.comp_def, Col.map_blockPoly]`.

Introduce and unpack `⟨P, k⟩`. Break down `Nat.eq_zero_or_pos k with rfl | hk` into its components or cases. Establish `: U (P, 0) = 1` using `ext_of_span hsp fun v => by rw [hU, h0]; rfl`. Rewrite using `[this]`. Simplify using `[eigOf, hg0]`.

Distinguish the cases in `hkn : k ≤ n`. Use `show _ = eigOf (q P) (g P) k • _`. Rewrite using `[hg]`. Conclude with `hup c e hce P k hk hkn _ (hU _)`. Establish `: U (P, k) = 0` using `ext_of_span hsp fun v => by rw [hU, hz P k (by omega)]; simp`.

Rewrite using `[this]`. Simplify using `[eigOf, coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hdeg P) (not_le.1 hkn))]`.
-/
theorem comap_range_adjoint_le_blockSum (hli : LinearIndependent ℂ fun i => j (b i))
    (hsp : Submodule.span ℂ (Set.range j) = ⊤) {op : Pl × ℕ → Module.End K V} (hc : Col.PairComm op)
    (hs : Col.SplitOver op) {n r t : ℕ} {q : Pl → ℕ} (hq : ∀ P, 0 < q P) {bl : List (Pl → K)}
    (hn : n = r + bl.length * t) (h0 : ∀ P, op (P, 0) = 1) (hz : ∀ P k, n < k → op (P, k) = 0)
    (Θ : H →ₗ[ℂ] E) {T : Pl × ℕ → Module.End ℂ E} (hT0 : ∀ P, T (P, 0) = 1) (hTc : Col.PairComm T)
    (hTn : ∀ i, Commute (T i) (LinearMap.adjoint (T i))) (s : Pl → ℂ)
    (hup : ∀ (c : Pl × ℕ → ℂ) (e : E), (∀ i, T i e = c i • e) → ∀ P k, 1 ≤ k → k ≤ n → ∀ U : Module.End ℂ H,
      (∀ v, U (j v) = j (op (P, k) v)) → U (LinearMap.adjoint Θ e) =
        eigOf (q P) ((Col.heckePoly r q c P).comp (C (s P) * X) *
          ((bl.map fun ν => Col.blockPoly (ν P) (q P) t).prod).map σ) k • LinearMap.adjoint Θ e) :
    (LinearMap.range (LinearMap.adjoint Θ)).comap j ≤ Col.blockSum n q t bl op := by
  choose U hU using fun i => exists_cx hli hsp (op i)
  have hd : (Col.eigSum U (Col.HasBlocks n q t (bl.map fun ν P => σ (ν P)))).comap j ≤
      Col.eigSum op (Col.HasBlocks n q t bl) :=
    comap_eigSum_le (injective_of_li hli) hsp hU hc hs fun x hx => (Col.hasBlocks_map σ n q t bl x).1 hx
  refine le_trans (Submodule.comap_mono ?_) hd
  have htop : ⨆ c, Col.eigAt T c = ⊤ :=
    Col.iSup_eigAt_eq_top hTc fun i => Module.End.iSup_maxGenEigenspace_eq_top (T i)
  rw [LinearMap.range_eq_map, ← htop, Submodule.map_iSup]
  refine iSup_le fun c => ?_
  rintro _ ⟨e, he, rfl⟩
  by_cases he0 : e = 0
  · rw [he0, map_zero]; exact Submodule.zero_mem _
  have hce : ∀ i, T i e = c i • e := fun i => by
    have := Col.eigAt_le T c i he
    rwa [NormalFamily.maxGenEigenspace_eq (hTn i), Module.End.mem_eigenspace_iff] at this
  have hc0 : ∀ P, c (P, 0) = 1 := fun P => by
    have := hce (P, 0)
    rw [hT0, Module.End.one_apply] at this
    exact smul_left_injective ℂ he0 (by simpa using this.symm)
  obtain ⟨g, hg⟩ : ∃ g : Pl → ℂ[X], ∀ P, g P = (Col.heckePoly r q c P).comp (C (s P) * X) *
    ((bl.map fun ν => Col.blockPoly (ν P) (q P) t).prod).map σ := ⟨_, fun _ => rfl⟩
  have hdeg : ∀ P, (g P).natDegree ≤ n := fun P => by
    rw [hg]
    refine natDegree_mul_le.trans ?_
    rw [hn]
    refine add_le_add (natDegree_comp_le.trans ?_) (natDegree_map_le.trans (blocks_spec bl P _ t).1)
    have h1 : (C (s P) * X).natDegree ≤ 1 := by compute_degree
    exact (Nat.mul_le_mul (natDegree_heckePolyOf _ _ _) h1).trans (by simp)
  have hg0 : ∀ P, (g P).coeff 0 = 1 := fun P => by
    rw [hg, mul_coeff_zero, coeff_map, (blocks_spec bl P _ t).2, map_one, mul_one, coeff_zero_eq_eval_zero, eval_comp]
    simp only [eval_mul, eval_C, eval_X, mul_zero]
    rw [← coeff_zero_eq_eval_zero, Col.heckePoly, coeff_heckePolyOf, if_pos (Nat.zero_le _), hc0]
    simp
  refine Col.eigAt_le_eigSum (x := fun i => eigOf (q i.1) (g i.1) i.2) (fun P => ?_)
    (Col.mem_eigAt_of_forall_apply ?_)
  · show _ ∣ Col.heckePolyOf n (q P) (eigOf (q P) (g P))
    rw [heckePolyOf_eigOf (hq P) (hdeg P)]
    refine Dvd.intro_left ((Col.heckePoly r q c P).comp (C (s P) * X)) ?_
    simp only [hg, Polynomial.map_list_prod, List.map_map, Function.comp_def, Col.map_blockPoly]
  · rintro ⟨P, k⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have : U (P, 0) = 1 := ext_of_span hsp fun v => by rw [hU, h0]; rfl
      rw [this]
      simp [eigOf, hg0]
    · by_cases hkn : k ≤ n
      · show _ = eigOf (q P) (g P) k • _
        rw [hg]
        exact hup c e hce P k hk hkn _ (hU _)
      · have : U (P, k) = 0 := ext_of_span hsp fun v => by rw [hU, hz P k (by omega)]; simp
        rw [this]
        simp [eigOf, coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hdeg P) (not_le.1 hkn))]

end Core

section Pres

variable {G Γ W K : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [Field K] [NumberField K] [StarRing K] {ι : Γ →* G} {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W}
  {J : Subgroup G} {χ : J →* ℂˣ} (P : Bridge.ClassPres ι S σ ρ J χ) (M : HMod (G → W))
  (hM : M.Is (Bridge.AdForms ι ρ J χ) (Bridge.adInner ι J P.y)) {j : S.Forms →ₛₗ[σ] M.H}
  (hj : ∀ x, M.e (j x) = P.extL x)

include hM hj

/- English proof (translation)
Take `⟨-, h2, ⟨h3, h4⟩, -⟩` from `classPres_basic ι S σ ρ J χ P`. Use `⟨LinearIndependent.of_comp M.e (by simpa only [Function.comp_def, hj] using h3), ?_, fun x y => ?_⟩` and prove the remaining obligations. Use `Submodule.map_injective_of_injective hM.1 ?_` and prove the remaining obligations. Rewrite using `[Submodule.map_top, hM.2.1, ← h4, Submodule.map_span, ← Set.range_comp]`. Simplify using `only [Function.comp_def, hj]`.

Rewrite using `[hM.2.2, hj, hj]`. Conclude with `h2 x y`.
-/
theorem model_form : (LinearIndependent ℂ fun i => j (S.basis i)) ∧ Submodule.span ℂ (Set.range j) = ⊤ ∧
    ∀ x y, inner ℂ (j x) (j y) = σ (S.csum (x : S.Cl → S.V) (y : S.Cl → S.V)) := by
  obtain ⟨-, h2, ⟨h3, h4⟩, -⟩ := classPres_basic ι S σ ρ J χ P
  refine ⟨LinearIndependent.of_comp M.e (by simpa only [Function.comp_def, hj] using h3), ?_, fun x y => ?_⟩
  · refine Submodule.map_injective_of_injective hM.1 ?_
    rw [Submodule.map_top, hM.2.1, ← h4, Submodule.map_span, ← Set.range_comp]
    simp only [Function.comp_def, hj]
  · rw [hM.2.2, hj, hj]
    exact h2 x y

/- English proof (translation)
Set `L : (G → W) →ₗ[ℂ] (G → W)` to `{ toFun := Bridge.dcOp B map_add' := fun F F' => by funext h; simp [Bridge.dcOp, Finset.sum_add_distrib] map_smul' := fun a F => by funext h; simp [Bridge.dcOp, Finset.smul_sum] }`. Establish `: M.e ∘ₗ U = L ∘ₗ M.e` using `ext_of_span (model_form P M hM hj).2.1 fun v => by`. Simplify using `only [LinearMap.comp_apply, hU, hj]`. Conclude with `hf v`. Conclude with `LinearMap.congr_fun this y`.
-/
theorem model_dcOp {f : Module.End K S.Forms} {B : Finset G}
    (hf : ∀ x : S.Forms, P.ext (f x : S.Cl → S.V) = Bridge.dcOp B (P.ext (x : S.Cl → S.V)))
    {U : Module.End ℂ M.H} (hU : ∀ v, U (j v) = j (f v)) (y : M.H) : M.e (U y) = Bridge.dcOp B (M.e y) := by
  let L : (G → W) →ₗ[ℂ] (G → W) :=
    { toFun := Bridge.dcOp B
      map_add' := fun F F' => by funext h; simp [Bridge.dcOp, Finset.sum_add_distrib]
      map_smul' := fun a F => by funext h; simp [Bridge.dcOp, Finset.smul_sum] }
  have : M.e ∘ₗ U = L ∘ₗ M.e := ext_of_span (model_form P M hM hj).2.1 fun v => by
    simp only [LinearMap.comp_apply, hU, hj]
    exact hf v
  exact LinearMap.congr_fun this y

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `model_form P M hM hj`. Rewrite using `[goodAt, level_idempotent_bot, mul_one]`. Use `comap_range_adjoint_le (injective_of_li h1) h2 (sum_selfAdj r _ (fun g => ?_) fun g v w => ?_) fun v => ?_` and prove the remaining obligations. Simplify using `only [coeff_idemOf, map_sum, map_mul, map_div₀, map_natCast, inv_inv]`. Use `Finset.sum_congr rfl fun c hc => ?_` and prove the remaining obligations.

Rewrite using `[← (hX c hc).map_inv σ, ← (hX c hc).map_inv σ, inv_one, inv_inv]`. Rewrite using `[h3, h3, hr.unitary]`. Rewrite using `[← he (j v)]`. Simplify using `only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smulₛₗ, hΘ, RingHom.id_apply]`.
-/
theorem model_good {G0 E : Type} [Group G0] [Fintype G0] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {r : Representation K G0 S.Forms} (hr : S.ActGood r) {X : Finset (G0 → K)}
    (hX : ∀ c ∈ X, IsAbsIrrChar c) {Θ : M.H →ₗ[ℂ] E} (gE : Representation ℂ G0 E)
    (hΘ : ∀ g v, Θ (j (r g v)) = gE g (Θ (j v)))
    (he : ∀ y, ∑ g, σ ((idemOf X).coeff g) • gE g (Θ y) = Θ y) :
    (LinearMap.range (LinearMap.adjoint Θ)).comap j ≤ LinearMap.range (S.gaOp r (goodAt X (⊥ : Subgroup G0) 1)) := by
  obtain ⟨h1, h2, h3⟩ := model_form P M hM hj
  rw [goodAt, level_idempotent_bot, mul_one]
  refine comap_range_adjoint_le (injective_of_li h1) h2 (sum_selfAdj r _ (fun g => ?_) fun g v w => ?_) fun v => ?_
  · simp only [coeff_idemOf, map_sum, map_mul, map_div₀, map_natCast, inv_inv]
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [← (hX c hc).map_inv σ, ← (hX c hc).map_inv σ, inv_one, inv_inv]
  · rw [h3, h3, hr.unitary]
  · rw [← he (j v)]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smulₛₗ, hΘ, RingHom.id_apply]

end Pres

/- English proof (translation)
Use `conv_rhs => rw [← idemOf_mul_self X hX]`. Simplify using `only [coeff_mul_fin, map_sum, map_smul, Finset.smul_sum, Finset.sum_smul, map_mul]`. Rewrite using `[Finset.sum_comm (f := fun h x => (σ ((idemOf X).coeff x) * σ ((idemOf X).coeff (x⁻¹ * h))) • ρ h z)]`. Use `Finset.sum_congr rfl fun g _ => Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun h => ?_` and prove the remaining obligations. Simplify using `[mul_smul]`.
-/
theorem idem_idem {K G E : Type} [Field K] [CharZero K] [Group G] [Fintype G] [AddCommGroup E] [Module ℂ E]
    (σ : K →+* ℂ) {X : Finset (G → K)} (hX : ∀ c ∈ X, IsAbsIrrChar c) (ρ : Representation ℂ G E) (z : E) :
    ∑ g, σ ((idemOf X).coeff g) • ρ g (∑ h, σ ((idemOf X).coeff h) • ρ h z) = ∑ h, σ ((idemOf X).coeff h) • ρ h z := by
  conv_rhs => rw [← idemOf_mul_self X hX]
  simp only [coeff_mul_fin, map_sum, map_smul, Finset.smul_sum, Finset.sum_smul, map_mul]
  rw [Finset.sum_comm (f := fun h x => (σ ((idemOf X).coeff x) * σ ((idemOf X).coeff (x⁻¹ * h))) • ρ h z)]
  refine Finset.sum_congr rfl fun g _ => Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun h => ?_
  simp [mul_smul]

/- English proof (translation)
Establish `: Tw.map s (LinearMap.adjoint f) = LinearMap.adjoint (Tw.map s f)`. Rewrite using `[LinearMap.eq_adjoint_iff]`. Introduce `x y`. Rewrite using `[Tw.inner_eq, Tw.inner_eq]`. Conclude with `congrArg (cj s) (LinearMap.adjoint_inner_left f (Tw.out y) (Tw.out x))`.

Rewrite using `[← this]`. Conclude with `Iff.rfl`.
-/
theorem mem_range_adjoint_tw {E E' : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [FiniteDimensional ℂ E'] (s : Bool) (f : E →ₗ[ℂ] E') (y : E) :
    Tw.mk s y ∈ LinearMap.range (LinearMap.adjoint (Tw.map s f)) ↔ y ∈ LinearMap.range (LinearMap.adjoint f) := by
  have : Tw.map s (LinearMap.adjoint f) = LinearMap.adjoint (Tw.map s f) := by
    rw [LinearMap.eq_adjoint_iff]
    intro x y
    rw [Tw.inner_eq, Tw.inner_eq]
    exact congrArg (cj s) (LinearMap.adjoint_inner_left f (Tw.out y) (Tw.out x))
  rw [← this]
  exact Iff.rfl

end GlobalTheory.AdjBlock

end
