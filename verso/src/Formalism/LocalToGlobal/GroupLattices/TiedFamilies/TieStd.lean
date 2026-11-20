import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.TiedRec
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.RecAct

noncomputable section

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG NumberField Matrix

namespace Formalism.L2.G

/- English proof (translation)
Set `b' : Module.Basis (Fin n) E (Fin n → E)` to `b.map c`. Set `M : Matrix (Fin n) (Fin n) E` to `(Pi.basisFun E (Fin n)).toMatrix b'`. Set `M' : Matrix (Fin n) (Fin n) E` to `b'.toMatrix (Pi.basisFun E (Fin n))`. Establish `h1 : M * M' = 1` using `Module.Basis.toMatrix_mul_toMatrix_flip _ _`. Establish `h2 : M' * M = 1` using `Module.Basis.toMatrix_mul_toMatrix_flip _ _`.

Set `B : GL (Fin n) E` to `⟨M, M', h1, h2⟩`. Establish `hM : ∀ i a, M i a = c (b a) i` using `fun i a => by`. Simplify using `[M, b', Module.Basis.toMatrix_apply]`. Use `⟨B, ?_, fun x => ?_⟩` and prove the remaining obligations. Use extensionality with `a a'`.

Use `hb a a'` as an intermediate fact. Rewrite `this` using `[hc]`. Rewrite using `[Matrix.one_apply, ← this]`. Simplify using `only [hform, Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply, B, hM, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`.

Establish `e1 : L0.map ((c : V →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E)) = Submodule.span (𝓞 E) (Set.range b')`. Rewrite using `[hL, Submodule.map_span, ← Set.range_comp]`. Both sides reduce to the same expression. Rewrite using `[e1, Module.Basis.mem_span_iff_repr_mem]`. Establish `e2 : (B⁻¹ : GL (Fin n) E).1 *ᵥ x = b'.repr x` using `by show M' *ᵥ x = b'.repr x`.

Establish `h3` using `Module.Basis.toMatrix_mulVec_repr (Pi.basisFun E (Fin n)) b' x`. Establish `h4 : ((Pi.basisFun E (Fin n)).repr x : Fin n → E) = x` using `funext fun i => Pi.basisFun_repr E (Fin n) x i`. Rewrite `h3` using `[h4]`. Conclude with `h3`. Rewrite using `[e2]`.

Both sides reduce to the same expression.
-/
theorem stdB_core {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] {n : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (h : V → V → E)
    (c : V ≃ₗ[E] (Fin n → E)) (hc : ∀ x y, h x y = hform σ J (c x) (c y)) (b : Module.Basis (Fin n) E V)
    (hb : ∀ a a', h (b a) (b a') = if a = a' then 1 else 0) (L0 : Submodule (𝓞 E) V)
    (hL : L0 = Submodule.span (𝓞 E) (Set.range b)) :
    ∃ B : GL (Fin n) E, cT σ B.1 * J * B.1 = 1 ∧
      ∀ x : Fin n → E, x ∈ L0.map ((c : V →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E)) ↔
        ∀ a, ((B⁻¹ : GL (Fin n) E).1 *ᵥ x) a ∈ (algebraMap (𝓞 E) E).range := by
  classical
  let b' : Module.Basis (Fin n) E (Fin n → E) := b.map c
  let M : Matrix (Fin n) (Fin n) E := (Pi.basisFun E (Fin n)).toMatrix b'
  let M' : Matrix (Fin n) (Fin n) E := b'.toMatrix (Pi.basisFun E (Fin n))
  have h1 : M * M' = 1 := Module.Basis.toMatrix_mul_toMatrix_flip _ _
  have h2 : M' * M = 1 := Module.Basis.toMatrix_mul_toMatrix_flip _ _
  let B : GL (Fin n) E := ⟨M, M', h1, h2⟩
  have hM : ∀ i a, M i a = c (b a) i := fun i a => by
    simp [M, b', Module.Basis.toMatrix_apply]
  refine ⟨B, ?_, fun x => ?_⟩
  · ext a a'
    have := hb a a'
    rw [hc] at this
    rw [Matrix.one_apply, ← this]
    simp only [hform, Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply, B, hM, Finset.sum_mul]
    rw [Finset.sum_comm]
  · have e1 : L0.map ((c : V →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E)) = Submodule.span (𝓞 E) (Set.range b') := by
      rw [hL, Submodule.map_span, ← Set.range_comp]
      rfl
    rw [e1, Module.Basis.mem_span_iff_repr_mem]
    have e2 : (B⁻¹ : GL (Fin n) E).1 *ᵥ x = b'.repr x := by
      show M' *ᵥ x = b'.repr x
      have h3 := Module.Basis.toMatrix_mulVec_repr (Pi.basisFun E (Fin n)) b' x
      have h4 : ((Pi.basisFun E (Fin n)).repr x : Fin n → E) = x := funext fun i => Pi.basisFun_repr E (Fin n) x i
      rw [h4] at h3
      exact h3
    rw [e2]
    rfl

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Rewrite using `[Formalism.L2.Herm.hT_crd D.sp.cm]`. Unfold `hform`. Rewrite using `[← (finCongr (rankN D 0 (Nat.zero_le _))).sum_comp]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[← (finCongr (rankN D 0 (Nat.zero_le _))).sum_comp]`.

Both sides reduce to the same expression.
-/
theorem hermitian_form_frame_coordinates (D : D7) (x y : (D.sp.X 0).V) :
    (D.sp.X 0).hT x y = hform (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))
      (crdN D 0 (Nat.zero_le _) x) (crdN D 0 (Nat.zero_le _) y) := by
  rw [Formalism.L2.Herm.hT_crd D.sp.cm]
  unfold hform
  rw [← (finCongr (rankN D 0 (Nat.zero_le _))).sum_comp]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← (finCongr (rankN D 0 (Nat.zero_le _))).sum_comp]
  rfl

/- English proof (translation)
Take `⟨b, hb, hL⟩` from `h`. Take `⟨B, h1, h2⟩` from `stdB_core (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) (fun x y => (D.sp.X 0).hT x y) (crdN D 0 (Nat.zero_le _)) (hermitian_form_frame_coordinates D) (b.reindex (finCongr (rankN D 0 (Nat.zero_le _)))) (fun a a' => by`. Simplify using `only [Module.Basis.reindex_apply]`. Rewrite using `[hb]`. Use the proof step `simp)`.

Use the proof step `(D.sp.X 0).L0 (by rw [hL, Module.Basis.range_reindex])`. Use `⟨(reGL (rank_eq_first_level D.R) D.host.E).symm B, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[MulEquiv.apply_symm_apply]`. Conclude with `h1`. Rewrite using `[MulEquiv.apply_symm_apply]`.

Conclude with `h2`.
-/
theorem exists_stdB (D : D7) (h : Formalism.L2.Herm.IsStd (D.sp.X 0)) : ∃ B : GL (Fin D.R.k) D.host.E, Cmp.StdB D B := by
  obtain ⟨b, hb, hL⟩ := h
  obtain ⟨B, h1, h2⟩ := stdB_core (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))
    (fun x y => (D.sp.X 0).hT x y) (crdN D 0 (Nat.zero_le _)) (hermitian_form_frame_coordinates D)
    (b.reindex (finCongr (rankN D 0 (Nat.zero_le _))))
    (fun a a' => by
      simp only [Module.Basis.reindex_apply]
      rw [hb]
      simp)
    (D.sp.X 0).L0 (by rw [hL, Module.Basis.range_reindex])
  refine ⟨(reGL (rank_eq_first_level D.R) D.host.E).symm B, ?_, ?_⟩
  · rw [MulEquiv.apply_symm_apply]
    exact h1
  · rw [MulEquiv.apply_symm_apply]
    exact h2

/- English proof (translation)
The claim follows from `exists_stdB D (h.1 0 (Nat.zero_le _))`.
-/
theorem exists_stdB_of_tied (D : D7) (h : Formalism.L2.Herm.StdTied D) : ∃ B : GL (Fin D.R.k) D.host.E, Cmp.StdB D B :=
  exists_stdB D (h.1 0 (Nat.zero_le _))

end Formalism.L2.G
