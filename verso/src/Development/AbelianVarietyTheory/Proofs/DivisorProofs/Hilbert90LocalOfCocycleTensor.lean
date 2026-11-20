import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueBaseChangeEqOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvertibleOfFaithfullyFlat
open TensorProduct

namespace GlobalTheory.FlatDescent

/- English proof (translation)
Introduce `R S _ _ _ _ _ _ c hc p hp`. Set `θ : S →ₗ[S] S ⊗[R] S` to `LinearMap.toSpanSingleton S (S ⊗[R] S) (c : S ⊗[R] S)`. Establish `hθ : ∀ n, θ n = (n ⊗ₜ[R] (1 : S)) * (c : S ⊗[R] S)` using `fun n => by`. Simplify using `[θ, Algebra.smul_def]`. Set `ψ : (S ⊗[R] S) ⊗[R] S →ₐ[R] S ⊗[R] S` to `Algebra.TensorProduct.lift (S := R) (AlgHom.id R (S ⊗[R] S)) (Algebra.TensorProduct.includeRight) (fun _ _ => Commute.all _ _)`.

Establish `h1 : ∀ x, ψ (Algebra.TensorProduct.includeLeft (R` using `R) (S := R) (A := S ⊗[R] S) (B := S) x) = x := by`. Introduce `x`. Simplify using `[ψ, ← Algebra.TensorProduct.one_def]`. Establish `h2 : ∀ x, ψ (Algebra.TensorProduct.map (Algebra.TensorProduct.includeRight (R` using `R) (A := S) (B := S)) (AlgHom.id R S) x) = (1 : S) ⊗ₜ[R] Algebra.TensorProduct.lmul' R x := by`. Introduce `x`.

Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy, tmul_add]`. Consider the case `tmul a b => simp [ψ]`. Establish `h3 : ∀ x, ψ (Algebra.TensorProduct.map (Algebra.TensorProduct.includeLeft (R` using `R) (S := R) (A := S) (B := S)) (AlgHom.id R S) x) = x := by`.

Introduce `x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul a b => simp [ψ]`.

Establish `hμ : Algebra.TensorProduct.lmul' R (c : S ⊗[R] S) = 1`. Establish `h` using `congrArg ψ hc`. Rewrite `h` using `[map_mul, h1, h2, h3]`. Establish `h' : (1 : S) ⊗ₜ[R] Algebra.TensorProduct.lmul' R (c : S ⊗[R] S) = (1 : S) ⊗ₜ[R] (1 : S)` using `(Units.mul_right_inj c).1 (h.trans (mul_one _).symm)`. Conclude with `Module.FaithfullyFlat.tensorProduct_mk_injective (A := R) (B := S) S h'`.

Establish `hact : ∀ x, act R S S x = Algebra.TensorProduct.lmul' R x`. Introduce `x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.

Consider the case `tmul a b => simp`. Establish `hcounit : ∀ n, act R S S (θ n) = n`. Introduce `n`. Establish `hθ' : θ n = n • (c : S ⊗[R] S)` using `rfl`. Rewrite using `[hθ', (act R S S).map_smul, hact, hμ, smul_eq_mul, mul_one]`.

Set `e` to `(TensorProduct.assoc R S S S)`. Establish `hL0 : ∀ (a b : S) (z : S ⊗[R] S), a ⊗ₜ[R] (b • z) = e (Algebra.TensorProduct.includeLeft (R` using `R) (S := R) (A := S ⊗[R] S) (B := S) (a ⊗ₜ[R] b) * Algebra.TensorProduct.map (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := S)) (AlgHom.id R S) z) := by`. Introduce `a b z`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `add x y hx hy => simp only [map_add, hx, hy, mul_add, smul_add, tmul_add]`. Consider the case `tmul a' b'`. Simplify using `only [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.includeLeft_apply, AlgHom.id_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, e, TensorProduct.assoc_tmul, smul_tmul', smul_eq_mul]`. Establish `hL : ∀ x : S ⊗[R] S, (θ.restrictScalars R).lTensor S x = e (Algebra.TensorProduct.includeLeft (R` using `R) (S := R) (A := S ⊗[R] S) (B := S) x * Algebra.TensorProduct.map (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := S)) (AlgHom.id R S) (c : S ⊗[R] S)) := by`. Introduce `x`.

Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy, add_mul]`. Consider the case `tmul a b`. Rewrite using `[LinearMap.lTensor_tmul, LinearMap.coe_restrictScalars]`.

Conclude with `hL0 a b _`. Establish `hR : ∀ x : S ⊗[R] S, (TensorProduct.mk R S S 1).lTensor S x = e (Algebra.TensorProduct.map (Algebra.TensorProduct.includeLeft (R` using `R) (S := R) (A := S) (B := S)) (AlgHom.id R S) x) := by`. Introduce `x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul a b => simp [e]`. Establish `hsmul : ∀ (g : S →ₗ[R] S ⊗[R] S) (n : S) (x : S ⊗[R] S), g.lTensor S (n • x) = n • g.lTensor S x`. Introduce `g n x`. Proceed by induction on `x using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [smul_add, map_add, hx, hy]`. Consider the case `tmul a b => simp [smul_tmul']`. Establish `hcoassoc : ∀ n, (θ.restrictScalars R).lTensor S (θ n) = (TensorProduct.mk R S S 1).lTensor S (θ n)`. Introduce `n`.

Establish `hθ' : θ n = n • (c : S ⊗[R] S)` using `rfl`. Rewrite using `[hθ', hsmul, hsmul, hL, hR, hc]`. Establish `hD : IsDescentDatum θ` using `⟨hcounit, hcoassoc⟩`. Use `haveI : Module.Invertible R (invariants θ) := hD.invertible_invariants`. Choose the witnesses or unpack the hypotheses as in `⟨f, m, hfm⟩ : ∃ (f : Module.Dual R (invariants θ)) (m : invariants θ), f m ∉ p := by`.

Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Take `⟨T, hT⟩` from `((Module.Invertible.linearEquiv R (invariants θ)).symm 1).exists_finset`. Establish `h1 : (1 : R) = ∑ i ∈ T, i.1 i.2`. Use `congrArg (Module.Invertible.linearEquiv R (invariants θ)) hT` as an intermediate fact.

Simplify `this` using `[Module.Invertible.linearEquiv, map_sum]`. Conclude with `hp.ne_top ((Ideal.eq_top_iff_one _).2 (h1 ▸ Ideal.sum_mem _ fun i _ => hcon i.1 i.2))`. Establish `hcomm : ∀ x : invariants θ, f m • x = f x • m`. Introduce `x`. Use `congrArg (TensorProduct.lift ((LinearMap.lsmul R (invariants θ)).comp f)) (Module.Invertible.tmul_comm (m₁ := m) (m₂ := x))` as an intermediate fact.

Simplify using `using this`. Take `⟨y, hy⟩` from `hD.bijective_extend.2 1`. Establish `hspan : ∀ y : S ⊗[R] invariants θ, algebraMap R S (f m) * extend S (invariants θ) y ∈ Ideal.span {(m : S)}`. Introduce `y`. Proceed by induction on `y using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `add x y hx hy => rw [map_add, mul_add]`. Conclude with `Ideal.add_mem _ hx hy`. Consider the case `tmul b x`. Establish `hx : algebraMap R S (f m) * (x : S) = algebraMap R S (f x) * (m : S)`.

Use `congrArg Subtype.val (hcomm x)` as an intermediate fact. Simplify `this` using `[Algebra.smul_def]`. Rewrite using `[extend_tmul, smul_eq_mul, mul_left_comm, hx, ← mul_assoc]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)`. Take `⟨s, hs⟩` from `Ideal.mem_span_singleton'.1 (hspan y)`.

Use `⟨f m, hfm, m, s, 1, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hθ]`. Conclude with `mem_invariants.1 m.2`. Rewrite using `[pow_one, mul_comm, hs, hy, mul_one]`.
-/
theorem hilbert90_local_of_cocycle : ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R] [Module.Finite R S]
    [Module.FaithfullyFlat R S] (c : (S ⊗[R] S)ˣ),
    Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := S ⊗[R] S) (B := S) (c : S ⊗[R] S) *
        Algebra.TensorProduct.map (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := S)) (AlgHom.id R S) (c : S ⊗[R] S) =
      Algebra.TensorProduct.map (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := S) (B := S)) (AlgHom.id R S) (c : S ⊗[R] S) →
    ∀ p : Ideal R, p.IsPrime → ∃ r ∉ p, ∃ m s : S, ∃ n : ℕ,
      (m ⊗ₜ[R] (1 : S)) * (c : S ⊗[R] S) = (1 : S) ⊗ₜ[R] m ∧ m * s = algebraMap R S r ^ n := by
  intro R S _ _ _ _ _ _ c hc p hp
  classical
  let θ : S →ₗ[S] S ⊗[R] S := LinearMap.toSpanSingleton S (S ⊗[R] S) (c : S ⊗[R] S)
  have hθ : ∀ n, θ n = (n ⊗ₜ[R] (1 : S)) * (c : S ⊗[R] S) := fun n => by
    simp [θ, Algebra.smul_def]

  let ψ : (S ⊗[R] S) ⊗[R] S →ₐ[R] S ⊗[R] S :=
    Algebra.TensorProduct.lift (S := R) (AlgHom.id R (S ⊗[R] S))
      (Algebra.TensorProduct.includeRight) (fun _ _ => Commute.all _ _)
  have h1 : ∀ x, ψ (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := S ⊗[R] S) (B := S) x) = x := by
    intro x; simp [ψ, ← Algebra.TensorProduct.one_def]
  have h2 : ∀ x, ψ (Algebra.TensorProduct.map (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := S))
      (AlgHom.id R S) x) = (1 : S) ⊗ₜ[R] Algebra.TensorProduct.lmul' R x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy, tmul_add]
    | tmul a b => simp [ψ]
  have h3 : ∀ x, ψ (Algebra.TensorProduct.map (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := S) (B := S))
      (AlgHom.id R S) x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a b => simp [ψ]
  have hμ : Algebra.TensorProduct.lmul' R (c : S ⊗[R] S) = 1 := by
    have h := congrArg ψ hc
    rw [map_mul, h1, h2, h3] at h
    have h' : (1 : S) ⊗ₜ[R] Algebra.TensorProduct.lmul' R (c : S ⊗[R] S) = (1 : S) ⊗ₜ[R] (1 : S) :=
      (Units.mul_right_inj c).1 (h.trans (mul_one _).symm)
    exact Module.FaithfullyFlat.tensorProduct_mk_injective (A := R) (B := S) S h'
  have hact : ∀ x, act R S S x = Algebra.TensorProduct.lmul' R x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a b => simp
  have hcounit : ∀ n, act R S S (θ n) = n := by
    intro n
    have hθ' : θ n = n • (c : S ⊗[R] S) := rfl
    rw [hθ', (act R S S).map_smul, hact, hμ, smul_eq_mul, mul_one]

  let e := (TensorProduct.assoc R S S S)
  have hL0 : ∀ (a b : S) (z : S ⊗[R] S), a ⊗ₜ[R] (b • z) =
      e (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := S ⊗[R] S) (B := S) (a ⊗ₜ[R] b) *
        Algebra.TensorProduct.map (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := S))
          (AlgHom.id R S) z) := by
    intro a b z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy, mul_add, smul_add, tmul_add]
    | tmul a' b' =>
      simp only [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.includeRight_apply,
        Algebra.TensorProduct.includeLeft_apply, AlgHom.id_apply,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, e, TensorProduct.assoc_tmul, smul_tmul',
        smul_eq_mul]
  have hL : ∀ x : S ⊗[R] S, (θ.restrictScalars R).lTensor S x =
      e (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := S ⊗[R] S) (B := S) x *
        Algebra.TensorProduct.map (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := S))
          (AlgHom.id R S) (c : S ⊗[R] S)) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy, add_mul]
    | tmul a b =>
      rw [LinearMap.lTensor_tmul, LinearMap.coe_restrictScalars]
      exact hL0 a b _
  have hR : ∀ x : S ⊗[R] S, (TensorProduct.mk R S S 1).lTensor S x =
      e (Algebra.TensorProduct.map (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := S) (B := S))
        (AlgHom.id R S) x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a b => simp [e]
  have hsmul : ∀ (g : S →ₗ[R] S ⊗[R] S) (n : S) (x : S ⊗[R] S),
      g.lTensor S (n • x) = n • g.lTensor S x := by
    intro g n x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
    | tmul a b => simp [smul_tmul']
  have hcoassoc : ∀ n, (θ.restrictScalars R).lTensor S (θ n) = (TensorProduct.mk R S S 1).lTensor S (θ n) := by
    intro n
    have hθ' : θ n = n • (c : S ⊗[R] S) := rfl
    rw [hθ', hsmul, hsmul, hL, hR, hc]
  have hD : IsDescentDatum θ := ⟨hcounit, hcoassoc⟩
  haveI : Module.Invertible R (invariants θ) := hD.invertible_invariants

  obtain ⟨f, m, hfm⟩ : ∃ (f : Module.Dual R (invariants θ)) (m : invariants θ), f m ∉ p := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨T, hT⟩ := ((Module.Invertible.linearEquiv R (invariants θ)).symm 1).exists_finset
    have h1 : (1 : R) = ∑ i ∈ T, i.1 i.2 := by
      have := congrArg (Module.Invertible.linearEquiv R (invariants θ)) hT
      simpa [Module.Invertible.linearEquiv, map_sum] using this
    exact hp.ne_top ((Ideal.eq_top_iff_one _).2 (h1 ▸ Ideal.sum_mem _ fun i _ => hcon i.1 i.2))
  have hcomm : ∀ x : invariants θ, f m • x = f x • m := by
    intro x
    have := congrArg (TensorProduct.lift ((LinearMap.lsmul R (invariants θ)).comp f))
      (Module.Invertible.tmul_comm (m₁ := m) (m₂ := x))
    simpa using this
  obtain ⟨y, hy⟩ := hD.bijective_extend.2 1
  have hspan : ∀ y : S ⊗[R] invariants θ,
      algebraMap R S (f m) * extend S (invariants θ) y ∈ Ideal.span {(m : S)} := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, mul_add]; exact Ideal.add_mem _ hx hy
    | tmul b x =>
      have hx : algebraMap R S (f m) * (x : S) = algebraMap R S (f x) * (m : S) := by
        have := congrArg Subtype.val (hcomm x)
        simpa [Algebra.smul_def] using this
      rw [extend_tmul, smul_eq_mul, mul_left_comm, hx, ← mul_assoc]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 (hspan y)
  refine ⟨f m, hfm, m, s, 1, ?_, ?_⟩
  · rw [← hθ]; exact mem_invariants.1 m.2
  · rw [pow_one, mul_comm, hs, hy, mul_one]

end GlobalTheory.FlatDescent
