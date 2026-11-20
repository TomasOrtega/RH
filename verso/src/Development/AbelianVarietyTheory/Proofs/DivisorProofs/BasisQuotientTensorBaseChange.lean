import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfSecAlgTop
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace GlobalTheory

/- English proof (translation)
Use `set f := Algebra.TensorProduct.map ψ (AlgHom.id A B) with hf`. Use `set J' := J.map f with hJ'`. Set `bas : Module.Basis (Fin r) C ((C ⊗[A] B) ⧸ J)` to `Module.Basis.mk hli hsp.ge`. Establish `bas_apply : ∀ k, bas k = Ideal.Quotient.mk J ((1 : C) ⊗ₜ[A] v k)` using `fun k => Module.Basis.mk_apply _ _ _`. Set `Φ : (C ⊗[A] B) → (Fin r → R)` to `fun x k => ψ (bas.repr (Ideal.Quotient.mk J x) k)`.

Establish `mkC : ∀ (c : C) (x : C ⊗[A] B), Ideal.Quotient.mk J (c • x) = c • Ideal.Quotient.mk J x` using `fun c x => map_smul (Ideal.Quotient.mkₐ C J) c x`. Establish `Φ_add : ∀ x y, Φ (x + y) = Φ x + Φ y`. Introduce `x y`. Use function extensionality and compare the values at `k`. Simplify using `[Φ, map_add]`.

Establish `Φ_zero : Φ 0 = 0` using `by funext k; simp [Φ]`. Establish `Φ_smul : ∀ (c : C) x, Φ (c • x) = ψ c • Φ x`. Introduce `c x`. Use function extensionality and compare the values at `k`. Simplify using `[Φ, mkC]`.

Establish `Φ_J : ∀ x ∈ J, Φ x = 0`. Introduce `x hx`. Use function extensionality and compare the values at `k`. Simplify using `[Φ, Ideal.Quotient.eq_zero_iff_mem.mpr hx]`. Establish `Φ_v : ∀ k, Φ ((1 : C) ⊗ₜ[A] v k) = Pi.single k 1`.

Introduce `k`. Use function extensionality and compare the values at `j`. Simplify using `only [Φ, ← bas_apply, Module.Basis.repr_self]`. Distinguish the cases in `h : j = k`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Finsupp.single_apply, Pi.single_apply, Ne.symm h, h]`. Set `g : B →ₗ[A] (Fin r → R)` to `{ toFun := fun b => Φ ((1 : C) ⊗ₜ[A] b) map_add' := fun x y => by simp only [TensorProduct.tmul_add]; exact Φ_add _ _ map_smul' := fun a x => by`. Simplify using `only [RingHom.id_apply]`. Rewrite using `[TensorProduct.tmul_smul, ← algebraMap_smul C a ((1 : C) ⊗ₜ[A] x), Φ_smul, AlgHom.commutes, algebraMap_smul] }`.

Set `ℓ : R ⊗[A] B →ₗ[R] (Fin r → R)` to `LinearMap.liftBaseChange R g`. Establish `ℓ_tmul : ∀ (s : R) (b : B), ℓ (s ⊗ₜ[A] b) = s • Φ ((1 : C) ⊗ₜ[A] b)`. Introduce `s b`. Simplify using `[ℓ, g]`. Establish `key : ∀ x : C ⊗[A] B, ℓ (f x) = Φ x`.

Introduce `x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp [Φ_zero]`. Consider the case `tmul c b`. Rewrite using `[hf, Algebra.TensorProduct.map_tmul, ℓ_tmul]`.

Establish `: c ⊗ₜ[A] b = c • ((1 : C) ⊗ₜ[A] b)`. Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Rewrite using `[this, Φ_smul]`. Both sides reduce to the same expression. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy, Φ_add]`.

Establish `f_smul : ∀ (c : C) (y : C ⊗[A] B), f (c • y) = ψ c • f y`. Introduce `c y`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul c' b`.

Rewrite using `[TensorProduct.smul_tmul', hf, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, map_mul]`. Consider the case `add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]`. Establish `f_one : ∀ b : B, f ((1 : C) ⊗ₜ[A] b) = (1 : R) ⊗ₜ[A] b`. Introduce `b`. Rewrite using `[hf, Algebra.TensorProduct.map_tmul, map_one]`.

Both sides reduce to the same expression. Establish `kill : ∀ y ∈ J', ℓ y = 0`. Set `K : Ideal (R ⊗[A] B)` to `{ carrier := {y | ∀ a, ℓ (a * y) = 0} add_mem' := fun {x y} hx hy a => by rw [mul_add, map_add, hx a, hy a, add_zero] zero_mem' := fun a => by simp smul_mem' := fun c {x} hx a => by show ℓ (a * (c * x)) = 0`. Rewrite using `[← mul_assoc]`. Conclude with `hx _ }`.

Establish `hJK : J' ≤ K`. Rewrite using `[hJ', Ideal.map_le_iff_le_comap]`. Introduce `j hj a`. Proceed by induction on `a using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul s b`. Establish `: (s ⊗ₜ[A] b) * f j = s • f (((1 : C) ⊗ₜ[A] b) * j)`. Rewrite using `[map_mul, f_one, ← smul_mul_assoc, TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Rewrite using `[this, map_smul, key, Φ_J _ (J.mul_mem_left _ hj), smul_zero]`. Consider the case `add x y hx hy => rw [add_mul, map_add, hx, hy, add_zero]`.

Introduce `y hy`. Use `hJK hy 1` as an intermediate fact. Simplify using `using this`. Establish `mkR : ∀ (s : R) (x : R ⊗[A] B), Ideal.Quotient.mk J' (s • x) = s • Ideal.Quotient.mk J' x` using `fun s x => map_smul (Ideal.Quotient.mkₐ R J') s x`. Prove the components needed by the constructor for the conclusion.

Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `c hc`. Establish `hmem : (∑ k, c k • ((1 : R) ⊗ₜ[A] v k)) ∈ J'`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sum]`. Simplify `hc` using `[mkR]`.

Establish `h0` using `kill _ hmem`. Rewrite `h0` using `[map_sum]`. Simplify using `only [map_smul, ℓ_tmul, one_smul, Φ_v] at h0`. Introduce `i`. Use `congrFun h0 i` as an intermediate fact.

Simplify `this` using `[Finset.sum_apply, Pi.single_apply]`. Rewrite using `[eq_top_iff]`. Introduce and unpack `z -`. Take `⟨w, rfl⟩` from `Ideal.Quotient.mk_surjective z`. Establish `hbase : ∀ x : C ⊗[A] B, Ideal.Quotient.mk J' (f x) ∈ Submodule.span R (Set.range (fun k => Ideal.Quotient.mk J' ((1 : R) ⊗ₜ[A] v k)))`.

Introduce `x`. Establish `hx` using `bas.sum_repr (Ideal.Quotient.mk J x)`. Use `set c := bas.repr (Ideal.Quotient.mk J x)`. Establish `hmem : x - ∑ k, c k • ((1 : C) ⊗ₜ[A] v k) ∈ J`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_sum]`.

Simplify using `only [mkC, ← bas_apply]`. Rewrite using `[hx, sub_self]`. Establish `hmem' : f x - ∑ k, ψ (c k) • ((1 : R) ⊗ₜ[A] v k) ∈ J'`. Use `Ideal.mem_map_of_mem f hmem` as an intermediate fact. Rewrite `this` using `[map_sub, map_sum]`.

Simplify `this` using `only [f_smul, f_one]`. Rewrite using `[← sub_add_cancel (f x) (∑ k, ψ (c k) • ((1 : R) ⊗ₜ[A] v k)), map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hmem', zero_add, map_sum]`. Use `Submodule.sum_mem _ (fun k _ => ?_)` and prove the remaining obligations. Rewrite using `[mkR]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)`.

Proceed by induction on `w using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul s b`. Establish `: s ⊗ₜ[A] b = s • f ((1 : C) ⊗ₜ[A] b)`. Rewrite using `[f_one, TensorProduct.smul_tmul', smul_eq_mul, mul_one]`.

Rewrite using `[this, mkR]`. Conclude with `Submodule.smul_mem _ _ (hbase _)`. Consider the case `add x y hx hy => rw [map_add]`. Conclude with `Submodule.add_mem _ hx hy`.
-/
theorem quotient_basis_baseChange (A B C R : Type) [CommRing A] [CommRing B] [Algebra A B]
    [CommRing C] [Algebra A C] [CommRing R] [Algebra A R] {r : ℕ} (v : Fin r → B)
    (J : Ideal (C ⊗[A] B)) (ψ : C →ₐ[A] R)
    (hli : LinearIndependent C (fun k => Ideal.Quotient.mk J ((1 : C) ⊗ₜ[A] v k)))
    (hsp : Submodule.span C (Set.range (fun k => Ideal.Quotient.mk J ((1 : C) ⊗ₜ[A] v k))) = ⊤) :
    LinearIndependent R (fun k => Ideal.Quotient.mk (J.map (Algebra.TensorProduct.map ψ (AlgHom.id A B))) ((1 : R) ⊗ₜ[A] v k)) ∧
    Submodule.span R (Set.range (fun k => Ideal.Quotient.mk (J.map (Algebra.TensorProduct.map ψ (AlgHom.id A B))) ((1 : R) ⊗ₜ[A] v k))) = ⊤ := by
  set f := Algebra.TensorProduct.map ψ (AlgHom.id A B) with hf
  set J' := J.map f with hJ'
  let bas : Module.Basis (Fin r) C ((C ⊗[A] B) ⧸ J) := Module.Basis.mk hli hsp.ge
  have bas_apply : ∀ k, bas k = Ideal.Quotient.mk J ((1 : C) ⊗ₜ[A] v k) := fun k => Module.Basis.mk_apply _ _ _
  let Φ : (C ⊗[A] B) → (Fin r → R) := fun x k => ψ (bas.repr (Ideal.Quotient.mk J x) k)
  have mkC : ∀ (c : C) (x : C ⊗[A] B), Ideal.Quotient.mk J (c • x) = c • Ideal.Quotient.mk J x :=
    fun c x => map_smul (Ideal.Quotient.mkₐ C J) c x
  have Φ_add : ∀ x y, Φ (x + y) = Φ x + Φ y := by
    intro x y; funext k; simp [Φ, map_add]
  have Φ_zero : Φ 0 = 0 := by funext k; simp [Φ]
  have Φ_smul : ∀ (c : C) x, Φ (c • x) = ψ c • Φ x := by
    intro c x; funext k
    simp [Φ, mkC]
  have Φ_J : ∀ x ∈ J, Φ x = 0 := by
    intro x hx; funext k; simp [Φ, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
  have Φ_v : ∀ k, Φ ((1 : C) ⊗ₜ[A] v k) = Pi.single k 1 := by
    intro k; funext j
    simp only [Φ, ← bas_apply, Module.Basis.repr_self]
    by_cases h : j = k
    · subst h; simp
    · simp [Finsupp.single_apply, Pi.single_apply, Ne.symm h, h]
  let g : B →ₗ[A] (Fin r → R) :=
    { toFun := fun b => Φ ((1 : C) ⊗ₜ[A] b)
      map_add' := fun x y => by simp only [TensorProduct.tmul_add]; exact Φ_add _ _
      map_smul' := fun a x => by
        simp only [RingHom.id_apply]
        rw [TensorProduct.tmul_smul, ← algebraMap_smul C a ((1 : C) ⊗ₜ[A] x), Φ_smul,
          AlgHom.commutes, algebraMap_smul] }
  let ℓ : R ⊗[A] B →ₗ[R] (Fin r → R) := LinearMap.liftBaseChange R g
  have ℓ_tmul : ∀ (s : R) (b : B), ℓ (s ⊗ₜ[A] b) = s • Φ ((1 : C) ⊗ₜ[A] b) := by
    intro s b; simp [ℓ, g]
  have key : ∀ x : C ⊗[A] B, ℓ (f x) = Φ x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp [Φ_zero]
    | tmul c b =>
      rw [hf, Algebra.TensorProduct.map_tmul, ℓ_tmul]
      have : c ⊗ₜ[A] b = c • ((1 : C) ⊗ₜ[A] b) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this, Φ_smul]; rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy, Φ_add]
  have f_smul : ∀ (c : C) (y : C ⊗[A] B), f (c • y) = ψ c • f y := by
    intro c y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul c' b =>
      rw [TensorProduct.smul_tmul', hf, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
        TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, map_mul]
    | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
  have f_one : ∀ b : B, f ((1 : C) ⊗ₜ[A] b) = (1 : R) ⊗ₜ[A] b := by
    intro b; rw [hf, Algebra.TensorProduct.map_tmul, map_one]; rfl
  have kill : ∀ y ∈ J', ℓ y = 0 := by
    let K : Ideal (R ⊗[A] B) :=
      { carrier := {y | ∀ a, ℓ (a * y) = 0}
        add_mem' := fun {x y} hx hy a => by rw [mul_add, map_add, hx a, hy a, add_zero]
        zero_mem' := fun a => by simp
        smul_mem' := fun c {x} hx a => by
          show ℓ (a * (c * x)) = 0
          rw [← mul_assoc]; exact hx _ }
    have hJK : J' ≤ K := by
      rw [hJ', Ideal.map_le_iff_le_comap]
      intro j hj a
      induction a using TensorProduct.induction_on with
      | zero => simp
      | tmul s b =>
        have : (s ⊗ₜ[A] b) * f j = s • f (((1 : C) ⊗ₜ[A] b) * j) := by
          rw [map_mul, f_one, ← smul_mul_assoc, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [this, map_smul, key, Φ_J _ (J.mul_mem_left _ hj), smul_zero]
      | add x y hx hy => rw [add_mul, map_add, hx, hy, add_zero]
    intro y hy
    have := hJK hy 1
    simpa using this
  have mkR : ∀ (s : R) (x : R ⊗[A] B), Ideal.Quotient.mk J' (s • x) = s • Ideal.Quotient.mk J' x :=
    fun s x => map_smul (Ideal.Quotient.mkₐ R J') s x
  constructor
  · rw [Fintype.linearIndependent_iff]
    intro c hc
    have hmem : (∑ k, c k • ((1 : R) ⊗ₜ[A] v k)) ∈ J' := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum]
      simpa [mkR] using hc
    have h0 := kill _ hmem
    rw [map_sum] at h0
    simp only [map_smul, ℓ_tmul, one_smul, Φ_v] at h0
    intro i
    have := congrFun h0 i
    simpa [Finset.sum_apply, Pi.single_apply] using this
  · rw [eq_top_iff]
    rintro z -
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
    have hbase : ∀ x : C ⊗[A] B, Ideal.Quotient.mk J' (f x) ∈
        Submodule.span R (Set.range (fun k => Ideal.Quotient.mk J' ((1 : R) ⊗ₜ[A] v k))) := by
      intro x
      have hx := bas.sum_repr (Ideal.Quotient.mk J x)
      set c := bas.repr (Ideal.Quotient.mk J x)
      have hmem : x - ∑ k, c k • ((1 : C) ⊗ₜ[A] v k) ∈ J := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_sum]
        simp only [mkC, ← bas_apply]
        rw [hx, sub_self]
      have hmem' : f x - ∑ k, ψ (c k) • ((1 : R) ⊗ₜ[A] v k) ∈ J' := by
        have := Ideal.mem_map_of_mem f hmem
        rw [map_sub, map_sum] at this
        simpa only [f_smul, f_one] using this
      rw [← sub_add_cancel (f x) (∑ k, ψ (c k) • ((1 : R) ⊗ₜ[A] v k)), map_add,
        Ideal.Quotient.eq_zero_iff_mem.mpr hmem', zero_add, map_sum]
      refine Submodule.sum_mem _ (fun k _ => ?_)
      rw [mkR]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul s b =>
      have : s ⊗ₜ[A] b = s • f ((1 : C) ⊗ₜ[A] b) := by
        rw [f_one, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this, mkR]
      exact Submodule.smul_mem _ _ (hbase _)
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

end GlobalTheory
