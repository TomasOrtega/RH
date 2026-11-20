import Mathlib
open scoped TensorProduct

namespace GlobalTheory.HilbChart

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {N r : ℕ}
  (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N)

noncomputable def sc (a m b : Fin N) : A := e.repr (e a * e m) b

variable {S : Type} [CommRing S] [Algebra A S]

noncomputable def coord (c : Fin N → Fin r → S) : S ⊗[A] B →ₗ[S] (Fin r → S) :=
  (Algebra.TensorProduct.basis S e).constr S c

noncomputable def ell (c : Fin N → Fin r → S) (m : Fin N) : S ⊗[A] B :=
  (1 : S) ⊗ₜ[A] e m - ∑ k, c m k • ((1 : S) ⊗ₜ[A] e (σ k))

noncomputable def chartIdeal (c : Fin N → Fin r → S) : Ideal (S ⊗[A] B) :=
  Ideal.span (Set.range (ell e σ c))

noncomputable def mulDefect (c : Fin N → Fin r → S) (a m : Fin N) (k : Fin r) : S :=
  ∑ b, algebraMap A S (sc e a m b) * c b k -
    ∑ k', c m k' * ∑ b, algebraMap A S (sc e a (σ k') b) * c b k

def IsChart (c : Fin N → Fin r → S) : Prop :=
  (∀ k k', c (σ k) k' = Pi.single (M := fun _ => S) k 1 k') ∧ ∀ a m k, mulDefect e σ c a m k = 0

end GlobalTheory.HilbChart

namespace GlobalTheory.HilbChart
variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {N r : ℕ}
  (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) {S : Type} [CommRing S] [Algebra A S]

/- English proof (translation)
Rewrite using `[← Algebra.TensorProduct.basis_apply]`. Conclude with `Module.Basis.constr_basis _ _ _ _`.
-/
theorem coord_one_tmul_basis (c : Fin N → Fin r → S) (m : Fin N) :
    coord e c ((1:S) ⊗ₜ e m) = c m := by
  rw [← Algebra.TensorProduct.basis_apply]; exact Module.Basis.constr_basis _ _ _ _

/- English proof (translation)
Use function extensionality and compare the values at `j`. Simplify using `[Finset.sum_apply, Pi.single_apply]`.
-/
theorem sum_smul_single (v : Fin r → S) : ∑ k, v k • (Pi.single k (1:S) : Fin r → S) = v := by
  funext j; simp [Finset.sum_apply, Pi.single_apply]

/- English proof (translation)
Rewrite using `[coord, Module.Basis.constr_apply, Finsupp.sum_fintype]`. Simplify using the standard rewrite rules.
-/
theorem coord_apply (c : Fin N → Fin r → S) (y : S ⊗[A] B) :
    coord e c y = ∑ m, (Algebra.TensorProduct.basis S e).repr y m • c m := by
  rw [coord, Module.Basis.constr_apply, Finsupp.sum_fintype]; simp

/- English proof (translation)
Use `conv_lhs => rw [← e.sum_repr x]`. Simplify using `only [TensorProduct.tmul_sum, map_sum, TensorProduct.tmul_smul]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.map_smul_of_tower, coord_one_tmul_basis]`.
-/
theorem coord_one_tmul (c : Fin N → Fin r → S) (x : B) :
    coord e c ((1:S) ⊗ₜ x) = ∑ b, e.repr x b • c b := by
  conv_lhs => rw [← e.sum_repr x]
  simp only [TensorProduct.tmul_sum, map_sum, TensorProduct.tmul_smul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [LinearMap.map_smul_of_tower, coord_one_tmul_basis]

/- English proof (translation)
Use `set bS := Algebra.TensorProduct.basis S e`. Rewrite using `[coord_apply]`. Simplify using `only [ell, smul_sub, Finset.sum_sub_distrib, Finset.smul_sum, smul_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_smul]`. Rewrite using `[Finset.sum_comm (γ := Fin r)]`. Establish `: ∑ m, bS.repr y m • ((1:S) ⊗ₜ[A] e m) = y` using `by conv_rhs => rw [← bS.sum_repr y]`.

Simplify using `[bS]`. Rewrite using `[this]`. Normalize the expressions using the abelian group laws.
-/
theorem decomp (c : Fin N → Fin r → S) (y : S ⊗[A] B) :
    y = ∑ m, (Algebra.TensorProduct.basis S e).repr y m • ell e σ c m +
      ∑ k, coord e c y k • ((1:S) ⊗ₜ[A] e (σ k)) := by
  set bS := Algebra.TensorProduct.basis S e
  rw [coord_apply]
  simp only [ell, smul_sub, Finset.sum_sub_distrib, Finset.smul_sum, smul_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Finset.sum_smul]
  rw [Finset.sum_comm (γ := Fin r)]
  have : ∑ m, bS.repr y m • ((1:S) ⊗ₜ[A] e m) = y := by
    conv_rhs => rw [← bS.sum_repr y]
    simp [bS]
  rw [this]; abel

/- English proof (translation)
The claim follows from `funext (hc k)`.
-/
theorem coord_sigma {c : Fin N → Fin r → S} (hc : ∀ k k', c (σ k) k' = Pi.single (M := fun _ => S) k 1 k')
    (k : Fin r) : c (σ k) = Pi.single k 1 := funext (hc k)

/- English proof (translation)
Simplify using `only [ell, map_sub, map_sum, map_smul, coord_one_tmul_basis, coord_sigma σ hc, sum_smul_single, sub_self]`.
-/
theorem coord_ell {c : Fin N → Fin r → S} (hc : ∀ k k', c (σ k) k' = Pi.single (M := fun _ => S) k 1 k')
    (m : Fin N) : coord e c (ell e σ c m) = 0 := by
  simp only [ell, map_sub, map_sum, map_smul, coord_one_tmul_basis, coord_sigma σ hc, sum_smul_single, sub_self]

/- English proof (translation)
Simplify using `only [ell, mul_sub, Finset.mul_sum, mul_smul_comm, Algebra.TensorProduct.tmul_mul_tmul, mul_one, map_sub, map_sum, map_smul, coord_one_tmul]`. Simplify using `only [mulDefect, sc, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Simplify using `only [Algebra.smul_def, Finset.mul_sum]`.
-/
theorem coord_mul_ell (c : Fin N → Fin r → S) (a m : Fin N) (k : Fin r) :
    coord e c (((1:S) ⊗ₜ[A] e a) * ell e σ c m) k = mulDefect e σ c a m k := by
  simp only [ell, mul_sub, Finset.mul_sum, mul_smul_comm, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
    map_sub, map_sum, map_smul, coord_one_tmul]
  simp only [mulDefect, sc, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp only [Algebra.smul_def, Finset.mul_sum]

/- English proof (translation)
Use `set bS := Algebra.TensorProduct.basis S e`. Establish `hy' : y = ∑ m, bS.repr y m • ell e σ c m`. Use `decomp e σ c y` as an intermediate fact. Rewrite `this` using `[hy]`. Simplify using `using this`.

Rewrite using `[← bS.sum_repr z, hy']`. Simplify using `only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, map_sum, map_smul]`. Use `Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun m _ => ?_` and prove the remaining obligations. Establish `: coord e c (bS m * ell e σ c a) = 0`. Use function extensionality and compare the values at `k`.

Rewrite using `[Algebra.TensorProduct.basis_apply, coord_mul_ell]`. Conclude with `hc.2 m a k`. Rewrite using `[this, smul_zero]`.
-/
theorem coord_mul_eq_zero {c : Fin N → Fin r → S} (hc : IsChart e σ c) (z y : S ⊗[A] B)
    (hy : coord e c y = 0) : coord e c (z * y) = 0 := by
  set bS := Algebra.TensorProduct.basis S e
  have hy' : y = ∑ m, bS.repr y m • ell e σ c m := by
    have := decomp e σ c y; rw [hy] at this; simpa using this
  rw [← bS.sum_repr z, hy']
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, map_sum, map_smul]
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun m _ => ?_
  have : coord e c (bS m * ell e σ c a) = 0 := by
    funext k; rw [Algebra.TensorProduct.basis_apply, coord_mul_ell]; exact hc.2 m a k
  rw [this, smul_zero]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hy`. Use `Submodule.span_induction ?_ ?_ ?_ ?_ hy` and prove the remaining obligations. Introduce and unpack `_ ⟨m, rfl⟩`. Conclude with `coord_ell e σ hc.1 m`.

Simplify using the standard rewrite rules. Introduce `u v _ _ hu hv`. Rewrite using `[map_add, hu, hv, add_zero]`. Introduce `z u _ hu`. Conclude with `coord_mul_eq_zero e σ hc z u hu`.

Introduce `hy`. Rewrite using `[decomp e σ c y, hy]`. Simplify using `only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero]`. Use `Ideal.sum_mem _ fun m _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def]`.

Conclude with `Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨m, rfl⟩)`.
-/
theorem mem_chartIdeal_iff {c : Fin N → Fin r → S} (hc : IsChart e σ c) (y : S ⊗[A] B) :
    y ∈ chartIdeal e σ c ↔ coord e c y = 0 := by
  constructor
  · intro hy
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨m, rfl⟩; exact coord_ell e σ hc.1 m
    · simp
    · intro u v _ _ hu hv; rw [map_add, hu, hv, add_zero]
    · intro z u _ hu; exact coord_mul_eq_zero e σ hc z u hu
  · intro hy
    rw [decomp e σ c y, hy]
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero]
    refine Ideal.sum_mem _ fun m _ => ?_
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨m, rfl⟩)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mk_smul (J : Ideal (S ⊗[A] B)) (s : S) (y : S ⊗[A] B) :
    Ideal.Quotient.mk J (s • y) = s • Ideal.Quotient.mk J y := rfl

/- English proof (translation)
Simplify using `only [map_sum, map_smul, coord_one_tmul_basis, hc, sum_smul_single]`.
-/
theorem sum_smul_tmul_sigma (c : Fin N → Fin r → S) (v : Fin r → S) (hc : ∀ k, c (σ k) = Pi.single k 1) :
    coord e c (∑ k, v k • ((1:S) ⊗ₜ[A] e (σ k))) = v := by
  simp only [map_sum, map_smul, coord_one_tmul_basis, hc, sum_smul_single]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg`. Simplify using `only [← mk_smul, ← map_sum, Ideal.Quotient.eq_zero_iff_mem, mem_chartIdeal_iff e σ hc] at hg`. Rewrite `hg` using `[sum_smul_tmul_sigma e σ c g (coord_sigma σ hc.1)]`.

Introduce `k`. Rewrite using `[hg]`. Both sides reduce to the same expression. Rewrite using `[Submodule.eq_top_iff']`. Introduce `x`.

Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Rewrite using `[decomp e σ c y, map_add, map_sum, map_sum]`. Establish `h0 : ∀ m, Ideal.Quotient.mk (chartIdeal e σ c) ((Algebra.TensorProduct.basis S e).repr y m • ell e σ c m) = 0` using `fun m => by`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem, Algebra.smul_def]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨m, rfl⟩)`.

Simplify using `only [h0, Finset.sum_const_zero, zero_add]`. Use `Submodule.sum_mem _ fun k _ => ?_` and prove the remaining obligations. Rewrite using `[mk_smul]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)`.
-/
theorem quotient_basis {c : Fin N → Fin r → S} (hc : IsChart e σ c) :
    LinearIndependent S (fun k => Ideal.Quotient.mk (chartIdeal e σ c) ((1 : S) ⊗ₜ[A] e (σ k))) ∧
    Submodule.span S (Set.range (fun k => Ideal.Quotient.mk (chartIdeal e σ c) ((1 : S) ⊗ₜ[A] e (σ k)))) = ⊤ := by
  constructor
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [← mk_smul, ← map_sum, Ideal.Quotient.eq_zero_iff_mem, mem_chartIdeal_iff e σ hc] at hg
    rw [sum_smul_tmul_sigma e σ c g (coord_sigma σ hc.1)] at hg
    intro k; rw [hg]; rfl
  · rw [Submodule.eq_top_iff']
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [decomp e σ c y, map_add, map_sum, map_sum]
    have h0 : ∀ m, Ideal.Quotient.mk (chartIdeal e σ c)
        ((Algebra.TensorProduct.basis S e).repr y m • ell e σ c m) = 0 := fun m => by
      rw [Ideal.Quotient.eq_zero_iff_mem, Algebra.smul_def]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨m, rfl⟩)
    simp only [h0, Finset.sum_const_zero, zero_add]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [mk_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

variable {S' : Type} [CommRing S'] [Algebra A S']

/- English proof (translation)
Simplify using `[ell, TensorProduct.smul_tmul', smul_eq_mul, mul_one]`.
-/
theorem map_ell (φ : S →ₐ[A] S') (c : Fin N → Fin r → S) (m : Fin N) :
    Algebra.TensorProduct.map φ (AlgHom.id A B) (ell e σ c m) = ell e σ (fun m k => φ (c m k)) m := by
  simp [ell, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/- English proof (translation)
Rewrite using `[chartIdeal, chartIdeal, Ideal.map_span, ← Set.range_comp]`. Establish `: (⇑(Algebra.TensorProduct.map φ (AlgHom.id A B)) ∘ ell e σ c) = ell e σ (fun m k => φ (c m k))` using `funext (map_ell e σ φ c)`. Rewrite using `[this]`.
-/
theorem map_chartIdeal (φ : S →ₐ[A] S') (c : Fin N → Fin r → S) :
    (chartIdeal e σ c).map (Algebra.TensorProduct.map φ (AlgHom.id A B)) =
      chartIdeal e σ (fun m k => φ (c m k)) := by
  rw [chartIdeal, chartIdeal, Ideal.map_span, ← Set.range_comp]
  have : (⇑(Algebra.TensorProduct.map φ (AlgHom.id A B)) ∘ ell e σ c) =
      ell e σ (fun m k => φ (c m k)) := funext (map_ell e σ φ c)
  rw [this]

/- English proof (translation)
Use `⟨fun k k' => ?_, fun a m k => ?_⟩` and prove the remaining obligations. Use `show φ (c (σ k) k') = _`. Apply the tactic sequence `rw [hc.1]; by_cases h : k' = k <;> simp [Pi.single_apply, h]`. Establish `: mulDefect e σ (fun m k => φ (c m k)) a m k = φ (mulDefect e σ c a m k)`. Simplify using `[mulDefect, map_sub, map_sum, map_mul, AlgHom.commutes]`.

Rewrite using `[this, hc.2, map_zero]`.
-/
theorem IsChart.map {c : Fin N → Fin r → S} (hc : IsChart e σ c) (φ : S →ₐ[A] S') :
    IsChart e σ (fun m k => φ (c m k)) := by
  refine ⟨fun k k' => ?_, fun a m k => ?_⟩
  · show φ (c (σ k) k') = _
    rw [hc.1]; by_cases h : k' = k <;> simp [Pi.single_apply, h]
  · have : mulDefect e σ (fun m k => φ (c m k)) a m k = φ (mulDefect e σ c a m k) := by
      simp [mulDefect, map_sub, map_sum, map_mul, AlgHom.commutes]
    rw [this, hc.2, map_zero]

/- English proof (translation)
Use function extensionality and compare the values at `m`. Establish `h1` using `(mem_chartIdeal_iff e σ hc _).1 (h (Ideal.subset_span ⟨m, rfl⟩))`. Simplify using `only [ell, map_sub, map_sum, map_smul, coord_one_tmul_basis, coord_sigma σ hc.1, sum_smul_single] at h1`. Conclude with `sub_eq_zero.1 h1`.
-/
theorem eq_of_chartIdeal_le {c d : Fin N → Fin r → S} (hc : IsChart e σ c)
    (h : chartIdeal e σ d ≤ chartIdeal e σ c) : c = d := by
  funext m
  have h1 := (mem_chartIdeal_iff e σ hc _).1 (h (Ideal.subset_span ⟨m, rfl⟩))
  simp only [ell, map_sub, map_sum, map_smul, coord_one_tmul_basis, coord_sigma σ hc.1,
    sum_smul_single] at h1
  exact sub_eq_zero.1 h1

/- English proof (translation)
Set `bq` to `Module.Basis.mk hli hsp.ge`. Set `c : Fin N → Fin r → S` to `fun m k => bq.repr (Ideal.Quotient.mk J ((1:S) ⊗ₜ[A] e m)) k`. Establish `hbq : ∀ k, bq k = Ideal.Quotient.mk J ((1 : S) ⊗ₜ[A] e (σ k))` using `fun k => Module.Basis.mk_apply _ _ _`. Establish `ha : ∀ k k', c (σ k) k' = Pi.single (M` using `fun _ => S) k 1 k' := by`. Introduce `k k'`.

Simplify using `only [c, ← hbq, Module.Basis.repr_self, Finsupp.single_apply, Pi.single_apply]`. Distinguish the cases in `h : k = k'`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h, Ne.symm h]`.

Establish `hell : ∀ m, Ideal.Quotient.mk J (ell e σ c m) = 0`. Introduce `m`. Simplify using `only [ell, map_sub, map_sum, mk_smul, ← hbq]`. Rewrite using `[sub_eq_zero]`. Conclude with `(bq.sum_repr _).symm`.

Establish `hq : ∀ y, Ideal.Quotient.mk J y = ∑ k, coord e c y k • bq k`. Introduce `y`. Use `conv_lhs => rw [decomp e σ c y]`. Simplify using `only [map_add, map_sum, mk_smul, hell, smul_zero, Finset.sum_const_zero, zero_add, hbq]`. Establish `hmem : ∀ y, y ∈ J ↔ coord e c y = 0`.

Introduce `y`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, hq y]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `funext ((Fintype.linearIndependent_iff.1 bq.linearIndependent) _ h)`.

Introduce `h`. Simplify using `[h]`. Establish `hc : IsChart e σ c`. Use `⟨ha, fun a m k => ?_⟩` and prove the remaining obligations. Rewrite using `[← coord_mul_ell]`.

Establish `: ell e σ c m ∈ J` using `(hmem _).2 (coord_ell e σ ha m)`. Rewrite using `[(hmem _).1 (J.mul_mem_left _ this)]`. Both sides reduce to the same expression. Use `⟨c, hc, ?_⟩` and prove the remaining obligations. Use extensionality with `y`.

Rewrite using `[mem_chartIdeal_iff e σ hc, hmem]`.
-/
theorem exists_chart_of_quotient (J : Ideal (S ⊗[A] B))
    (hli : LinearIndependent S (fun k => Ideal.Quotient.mk J ((1 : S) ⊗ₜ[A] e (σ k))))
    (hsp : Submodule.span S (Set.range (fun k => Ideal.Quotient.mk J ((1 : S) ⊗ₜ[A] e (σ k)))) = ⊤) :
    ∃ c : Fin N → Fin r → S, IsChart e σ c ∧ chartIdeal e σ c = J := by
  let bq := Module.Basis.mk hli hsp.ge
  let c : Fin N → Fin r → S := fun m k => bq.repr (Ideal.Quotient.mk J ((1:S) ⊗ₜ[A] e m)) k
  have hbq : ∀ k, bq k = Ideal.Quotient.mk J ((1 : S) ⊗ₜ[A] e (σ k)) := fun k => Module.Basis.mk_apply _ _ _
  have ha : ∀ k k', c (σ k) k' = Pi.single (M := fun _ => S) k 1 k' := by
    intro k k'
    simp only [c, ← hbq, Module.Basis.repr_self, Finsupp.single_apply, Pi.single_apply]
    by_cases h : k = k'
    · subst h; simp
    · simp [h, Ne.symm h]
  have hell : ∀ m, Ideal.Quotient.mk J (ell e σ c m) = 0 := by
    intro m
    simp only [ell, map_sub, map_sum, mk_smul, ← hbq]
    rw [sub_eq_zero]
    exact (bq.sum_repr _).symm
  have hq : ∀ y, Ideal.Quotient.mk J y = ∑ k, coord e c y k • bq k := by
    intro y
    conv_lhs => rw [decomp e σ c y]
    simp only [map_add, map_sum, mk_smul, hell, smul_zero, Finset.sum_const_zero, zero_add, hbq]
  have hmem : ∀ y, y ∈ J ↔ coord e c y = 0 := by
    intro y
    rw [← Ideal.Quotient.eq_zero_iff_mem, hq y]
    constructor
    · intro h
      exact funext ((Fintype.linearIndependent_iff.1 bq.linearIndependent) _ h)
    · intro h; simp [h]
  have hc : IsChart e σ c := by
    refine ⟨ha, fun a m k => ?_⟩
    rw [← coord_mul_ell]
    have : ell e σ c m ∈ J := (hmem _).2 (coord_ell e σ ha m)
    rw [(hmem _).1 (J.mul_mem_left _ this)]; rfl
  refine ⟨c, hc, ?_⟩
  ext y
  rw [mem_chartIdeal_iff e σ hc, hmem]

/- English proof (translation)
Simplify using `[mulDefect, map_sub, map_sum, map_mul, AlgHom.commutes]`.
-/
theorem mulDefect_map (φ : S →ₐ[A] S') (c : Fin N → Fin r → S) (a m : Fin N) (k : Fin r) :
    mulDefect e σ (fun m k => φ (c m k)) a m k = φ (mulDefect e σ c a m k) := by
  simp [mulDefect, map_sub, map_sum, map_mul, AlgHom.commutes]

noncomputable def rels : (Fin r × Fin r) ⊕ (Fin N × Fin N × Fin r) → MvPolynomial (Fin N × Fin r) A
  | .inl p => MvPolynomial.X (σ p.1, p.2) - MvPolynomial.C (Pi.single (M := fun _ => A) p.1 1 p.2)
  | .inr p => mulDefect e σ (fun m k => (MvPolynomial.X (m, k) : MvPolynomial (Fin N × Fin r) A)) p.1 p.2.1 p.2.2

/- English proof (translation)
Establish `hd : ∀ a m k, MvPolynomial.aeval (fun p : Fin N × Fin r => c p.1 p.2) (mulDefect e σ (fun m k => (MvPolynomial.X (m, k) : MvPolynomial (Fin N × Fin r) A)) a m k) = mulDefect e σ c a m k`. Introduce `a m k`. Rewrite using `[← mulDefect_map]`. Simplify using the standard rewrite rules. Establish `hs : ∀ k k' : Fin r, algebraMap A S (Pi.single (M` using `fun _ => A) k 1 k') = Pi.single (M := fun _ => S) k 1 k' := by`.

Apply the tactic sequence `intro k k'; by_cases h : k' = k <;> simp [Pi.single_apply, h]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨ha, hb⟩ (⟨k, k'⟩ | ⟨a, m, k⟩)`. Simplify using `[rels, ha, hs]`. Simplify using `only [rels]`.

Rewrite using `[hd, hb]`. Introduce `h`. Use `⟨fun k k' => ?_, fun a m k => ?_⟩` and prove the remaining obligations. Use `h (.inl (k, k'))` as an intermediate fact. Simplify using `only [rels, map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C, hs] at this`.

Conclude with `sub_eq_zero.1 this`. Use `h (.inr (a, m, k))` as an intermediate fact. Simplify using `only [rels] at this`. Rewrite `this` using `[hd]`. Then use the resulting hypothesis.
-/
theorem isChart_iff_aeval (c : Fin N → Fin r → S) :
    IsChart e σ c ↔ ∀ i, MvPolynomial.aeval (fun p : Fin N × Fin r => c p.1 p.2) (rels e σ i) = 0 := by
  have hd : ∀ a m k, MvPolynomial.aeval (fun p : Fin N × Fin r => c p.1 p.2)
      (mulDefect e σ (fun m k => (MvPolynomial.X (m, k) : MvPolynomial (Fin N × Fin r) A)) a m k) =
      mulDefect e σ c a m k := by
    intro a m k
    rw [← mulDefect_map]; simp
  have hs : ∀ k k' : Fin r, algebraMap A S (Pi.single (M := fun _ => A) k 1 k') =
      Pi.single (M := fun _ => S) k 1 k' := by
    intro k k'; by_cases h : k' = k <;> simp [Pi.single_apply, h]
  constructor
  · rintro ⟨ha, hb⟩ (⟨k, k'⟩ | ⟨a, m, k⟩)
    · simp [rels, ha, hs]
    · simp only [rels]; rw [hd, hb]
  · intro h
    refine ⟨fun k k' => ?_, fun a m k => ?_⟩
    · have := h (.inl (k, k'))
      simp only [rels, map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C, hs] at this
      exact sub_eq_zero.1 this
    · have := h (.inr (a, m, k))
      simp only [rels] at this; rwa [hd] at this

noncomputable def relIdeal : Ideal (MvPolynomial (Fin N × Fin r) A) := Ideal.span (Set.range (rels e σ))

abbrev ChartRing := MvPolynomial (Fin N × Fin r) A ⧸ relIdeal e σ

noncomputable def univChart : Fin N → Fin r → ChartRing e σ :=
  fun m k => Ideal.Quotient.mk (relIdeal e σ) (MvPolynomial.X (m, k))

/- English proof (translation)
Rewrite using `[isChart_iff_aeval]`. Introduce `i`. Establish `: MvPolynomial.aeval (fun p : Fin N × Fin r => univChart e σ p.1 p.2) = Ideal.Quotient.mkₐ A (relIdeal e σ)`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `p`.

Simplify using `[univChart]`. Rewrite using `[this, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `Ideal.subset_span ⟨i, rfl⟩`.
-/
theorem isChart_univChart : IsChart e σ (univChart e σ) := by
  rw [isChart_iff_aeval]
  intro i
  have : MvPolynomial.aeval (fun p : Fin N × Fin r => univChart e σ p.1 p.2) =
      Ideal.Quotient.mkₐ A (relIdeal e σ) := by
    apply MvPolynomial.algHom_ext; intro p; simp [univChart]
  rw [this, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨i, rfl⟩

end GlobalTheory.HilbChart

open GlobalTheory.HilbChart in
/- English proof (translation)
Introduce `A B _ _ _ N r e σ`. Establish `hC` using `isChart_univChart e σ`. Use `⟨ChartRing e σ, inferInstance, inferInstance, chartIdeal e σ (univChart e σ), ?_, (quotient_basis e σ hC).1, (quotient_basis e σ hC).2, ?_⟩` and prove the remaining obligations. Conclude with `Algebra.FinitePresentation.quotient (Submodule.fg_span (Set.finite_range _))`. Introduce `A' _ _ J' hli hsp`.

Take `⟨c, hc, hJ⟩` from `exists_chart_of_quotient e σ J' hli hsp`. Set `ψ : MvPolynomial (Fin N × Fin r) A →ₐ[A] A'` to `MvPolynomial.aeval (fun p => c p.1 p.2)`. Establish `hψ : ∀ a ∈ relIdeal e σ, ψ a = 0`. Introduce `a ha`. Establish `hle : relIdeal e σ ≤ RingHom.ker ψ`.

Rewrite using `[relIdeal, Ideal.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `(isChart_iff_aeval e σ c).1 hc i`. Conclude with `hle ha`. Set `φ : ChartRing e σ →ₐ[A] A'` to `Ideal.Quotient.liftₐ _ ψ hψ`.

Establish `hφ : (fun m k => φ (univChart e σ m k)) = c`. Use function extensionality and compare the values at `m k`. Express the relevant statement in the definitionally equal form `ψ (MvPolynomial.X (m, k)) = c m k`. Simplify using `[ψ]`. Use `⟨φ, ?_, ?_⟩` and prove the remaining obligations.

Use `show J' = _`. Rewrite using `[map_chartIdeal, hφ, hJ]`. Introduce `φ' hφ'`. Rewrite `hφ'` using `[map_chartIdeal, ← hJ]`. Establish `h1 : c = fun m k => φ' (univChart e σ m k)` using `eq_of_chartIdeal_le e σ hc hφ'.ge`.

Apply `Ideal.Quotient.algHom_ext` to reduce the goal to its premises. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `p`. Establish `h2` using `congrFun (congrFun (h1.symm.trans hφ.symm) p.1) p.2`. Simplify `h2` using `[univChart]`.
-/
theorem GlobalTheory.hilbChart_representable : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (N r : ℕ) (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N), ∃ (C : Type) (_ : CommRing C) (_ : Algebra A C) (J : Ideal (C ⊗[A] B)), Algebra.FinitePresentation A C ∧ LinearIndependent C (fun k => Ideal.Quotient.mk J ((1 : C) ⊗ₜ[A] e (σ k))) ∧ Submodule.span C (Set.range (fun k => Ideal.Quotient.mk J ((1 : C) ⊗ₜ[A] e (σ k)))) = ⊤ ∧ ∀ (A' : Type) [CommRing A'] [Algebra A A'] (J' : Ideal (A' ⊗[A] B)), LinearIndependent A' (fun k => Ideal.Quotient.mk J' ((1 : A') ⊗ₜ[A] e (σ k))) → Submodule.span A' (Set.range (fun k => Ideal.Quotient.mk J' ((1 : A') ⊗ₜ[A] e (σ k)))) = ⊤ → ∃! φ : C →ₐ[A] A', J' = J.map (Algebra.TensorProduct.map φ (AlgHom.id A B)) := by
  intro A B _ _ _ N r e σ
  have hC := isChart_univChart e σ
  refine ⟨ChartRing e σ, inferInstance, inferInstance, chartIdeal e σ (univChart e σ), ?_,
    (quotient_basis e σ hC).1, (quotient_basis e σ hC).2, ?_⟩
  · exact Algebra.FinitePresentation.quotient (Submodule.fg_span (Set.finite_range _))
  · intro A' _ _ J' hli hsp
    obtain ⟨c, hc, hJ⟩ := exists_chart_of_quotient e σ J' hli hsp
    let ψ : MvPolynomial (Fin N × Fin r) A →ₐ[A] A' := MvPolynomial.aeval (fun p => c p.1 p.2)
    have hψ : ∀ a ∈ relIdeal e σ, ψ a = 0 := by
      intro a ha
      have hle : relIdeal e σ ≤ RingHom.ker ψ := by
        rw [relIdeal, Ideal.span_le]
        rintro _ ⟨i, rfl⟩
        exact (isChart_iff_aeval e σ c).1 hc i
      exact hle ha
    let φ : ChartRing e σ →ₐ[A] A' := Ideal.Quotient.liftₐ _ ψ hψ
    have hφ : (fun m k => φ (univChart e σ m k)) = c := by
      funext m k
      change ψ (MvPolynomial.X (m, k)) = c m k
      simp [ψ]
    refine ⟨φ, ?_, ?_⟩
    · show J' = _
      rw [map_chartIdeal, hφ, hJ]
    · intro φ' hφ'
      rw [map_chartIdeal, ← hJ] at hφ'
      have h1 : c = fun m k => φ' (univChart e σ m k) := eq_of_chartIdeal_le e σ hc hφ'.ge
      apply Ideal.Quotient.algHom_ext
      apply MvPolynomial.algHom_ext
      intro p
      have h2 := congrFun (congrFun (h1.symm.trans hφ.symm) p.1) p.2
      simpa [univChart] using h2
