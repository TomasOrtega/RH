import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

namespace PositivityTheory.HtPt.Gi

/- English proof (translation)
Introduce `p _ C _ _ _ v O _ _ _ hv hp hO E _ _ c La _ _ EF N u h`. Use `h.free` as an intermediate fact. Use `h.finite` as an intermediate fact. Set `ρ : 𝓞 E →+* Module.End C (C ⊗[ℤ] La)` to `(Module.End.baseChangeHom ℤ C La).toRingHom.comp (Module.toModuleEnd ℤ La)`. Establish `hρ : ∀ (a : 𝓞 E) (s : C) (x : La), ρ a (s ⊗ₜ x) = s ⊗ₜ (a • x)` using `fun a s x => rfl`.

Set `e : C ⊗[ℤ] La →ₗ[C] C ⊗[ℤ] La →ₗ[C] C` to `LinearMap.BilinForm.baseChange C EF`. Establish `he : ∀ (s t : C) (x y : La), e (s ⊗ₜ x) (t ⊗ₜ y) = (EF x y : C) * (s * t)` using `fun s t x y => by`. Simplify using `only [e, LinearMap.BilinForm.baseChange_tmul, zsmul_eq_mul]`. Establish `he1 : ∀ x y : La, e (1 ⊗ₜ x) (1 ⊗ₜ y) = (EF x y : C)` using `fun x y => by rw [he]; simp`. Set `T : Submodule O (C ⊗[ℤ] La)` to `Submodule.span O (Set.range fun x : La => (1 : C) ⊗ₜ[ℤ] x)`.

Establish `hT : ∀ x : La, (1 : C) ⊗ₜ[ℤ] x ∈ T` using `fun x => Submodule.subset_span ⟨x, rfl⟩`. Set `b` to `Module.Free.chooseBasis ℤ La`. Set `B` to `Algebra.TensorProduct.basis C b`. Establish `hB : ∀ i, B i = 1 ⊗ₜ b i` using `fun i => Algebra.TensorProduct.basis_apply b i`. Use `choose b' hb' using fun i => h.unimod.2 (b.coord i)`.

Establish `hrep : ∀ i y, e (1 ⊗ₜ b' i) y = B.repr y i`. Introduce `i y`. Establish `: e (1 ⊗ₜ b' i) = B.coord i` using `B.ext fun j => by`. Rewrite using `[Module.Basis.coord_apply, B.repr_self, hB, he1, hb', Module.Basis.coord_apply, b.repr_self]`. Simplify using `only [Finsupp.single_apply]`.

Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[this]`. Both sides reduce to the same expression. Establish `hskew : ∀ x y, EF x y = -EF y x` using `fun x y => by`. Use `h.alt (x + y)` as an intermediate fact.

Simplify using `only [map_add, LinearMap.add_apply, h.alt] at this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `eskew : ∀ x y, e x y = -e y x`. Introduce `x y`. Proceed by induction on `x with`.

Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `tmul s x`. Proceed by induction on `y with`.

Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `tmul t y => rw [he, he, hskew]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hTb : T = Submodule.span O (Set.range B)`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨x, rfl⟩`.

Express the relevant statement in the definitionally equal form `(1 : C) ⊗ₜ[ℤ] x ∈ Submodule.span O (Set.range B)`. Rewrite using `[← b.sum_repr x, tmul_sum]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[tmul_smul, ← hB]`. Conclude with `zsmul_mem (Submodule.subset_span (R := O) (Set.mem_range_self (f := B) i)) _`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Rewrite using `[hB]`. Conclude with `hT _`. Establish `hsp : Submodule.span C (T : Set (C ⊗[ℤ] La)) = ⊤`.

Rewrite using `[hTb, Submodule.span_span_of_tower, B.span_eq]`. Set `w : Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E) → C ⊗[ℤ] La` to `fun q => ρ (RingOfIntegers.basis E q.2) (1 ⊗ₜ u q.1)`. Establish `hTw : T = Submodule.span O (Set.range w)`. Apply `le_antisymm` to reduce the goal to its premises. Use `Submodule.le_of_le_smul_of_le_jacobson_bot (I := Ideal.span {(p : O)}) ?_ (IsAdicComplete.le_jacobson_bot _) ?_` and prove the remaining obligations.

Rewrite using `[hTb]`. Conclude with `Submodule.fg_span (Set.finite_range B)`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, rfl⟩`. Take `⟨a, x', rfl⟩` from `h.span x`.

Express the relevant statement in the definitionally equal form `(1 : C) ⊗ₜ[ℤ] _ ∈ Submodule.span O (Set.range w) ⊔ Ideal.span {(p : O)} • T`. Rewrite using `[tmul_add]`. Use `Submodule.add_mem_sup ?_ ?_` and prove the remaining obligations. Rewrite using `[tmul_sum]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[← (RingOfIntegers.basis E).sum_repr (a i), Finset.sum_smul, tmul_sum]`. Use `Submodule.sum_mem _ fun k _ => ?_` and prove the remaining obligations. Rewrite using `[smul_assoc, tmul_smul]`. Conclude with `zsmul_mem (Submodule.subset_span (R := O) (Set.mem_range_self (f := w) (i, k))) _`. Rewrite using `[tmul_smul, ← Nat.cast_smul_eq_nsmul O]`.

Conclude with `Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) (hT _)`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨q, rfl⟩`. Conclude with `hT _`. Use `⟨ρ, T, e, fun a x => hρ a 1 x, rfl, ⟨?_, hsp, hTw⟩, he1, fun x => ?_, fun y hy => ?_, ?_, fun a x y => ?_⟩` and prove the remaining obligations.

Use `linearIndependent_of_top_le_span_of_card_eq_finrank (b := w) ?_ ?_` and prove the remaining obligations. Rewrite using `[← hsp, hTw, Submodule.span_span_of_tower]`. Rewrite using `[Module.finrank_baseChange, h.rank, Fintype.card_prod, Fintype.card_fin, ← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank]`. Use `eskew x x` as an intermediate fact. Establish `h2 : (2 : C) * e x x = 0` using `by linear_combination this`.

Simplify using `using h2`. Conclude with `B.ext_elem fun i => by rw [← hrep, hy]; simp`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `y hy`. Rewrite using `[hTb, ← B.sum_repr y]`.

Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Take `⟨o, ho⟩` from `hy _ (hT (b' i))`. Rewrite using `[← hrep, ← ho, algebraMap_smul]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨y, rfl⟩ x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨x, rfl⟩` from `hx`. Conclude with `⟨(EF x y : O), by rw [he1, map_intCast]⟩`.

Consider the case `zero => simp`. Consider the case `add x x' _ _ hx hx'`. Rewrite using `[map_add, LinearMap.add_apply]`. Conclude with `Subring.add_mem _ hx hx'`. Consider the case `smul o x _ hx`.

Rewrite using `[← algebraMap_smul C o x, map_smul, LinearMap.smul_apply, smul_eq_mul]`. Conclude with `Subring.mul_mem _ ⟨o, rfl⟩ hx`. Proceed by induction on `x with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]`.

Consider the case `tmul s x`. Proceed by induction on `y with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Consider the case `tmul t y => rw [hρ, hρ, he, he, h.adj]`.
-/
theorem free_on_lift : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (La : Type) [AddCommGroup La] [Module (𝓞 E) La] (EF : La →ₗ[ℤ] La →ₗ[ℤ] ℤ) (N : ℕ) (u : Fin N → La), IsPolLattice c p EF u → ∃ (ρ : 𝓞 E →+* Module.End C (C ⊗[ℤ] La)) (T : Submodule O (C ⊗[ℤ] La)) (e : C ⊗[ℤ] La →ₗ[C] C ⊗[ℤ] La →ₗ[C] C), (∀ (a : 𝓞 E) (x : La), ρ a (1 ⊗ₜ x) = 1 ⊗ₜ (a • x)) ∧ T = Submodule.span O (Set.range fun x : La => (1 : C) ⊗ₜ[ℤ] x) ∧ IsFreeOn ρ T (fun i => 1 ⊗ₜ u i) ∧ (∀ x y : La, e (1 ⊗ₜ x) (1 ⊗ₜ y) = (EF x y : C)) ∧ (∀ x, e x x = 0) ∧ (∀ y, (∀ x, e x y = 0) → y = 0) ∧ dualLat e T = T ∧ ∀ (a : 𝓞 E) x y, e (ρ a x) y = e x (ρ (RingOfIntegers.mapRingEquiv c a) y) := by
  intro p _ C _ _ _ v O _ _ _ hv hp hO E _ _ c La _ _ EF N u h
  classical
  have := h.free
  have := h.finite
  let ρ : 𝓞 E →+* Module.End C (C ⊗[ℤ] La) :=
    (Module.End.baseChangeHom ℤ C La).toRingHom.comp (Module.toModuleEnd ℤ La)
  have hρ : ∀ (a : 𝓞 E) (s : C) (x : La), ρ a (s ⊗ₜ x) = s ⊗ₜ (a • x) := fun a s x => rfl
  let e : C ⊗[ℤ] La →ₗ[C] C ⊗[ℤ] La →ₗ[C] C := LinearMap.BilinForm.baseChange C EF
  have he : ∀ (s t : C) (x y : La), e (s ⊗ₜ x) (t ⊗ₜ y) = (EF x y : C) * (s * t) := fun s t x y => by
    simp only [e, LinearMap.BilinForm.baseChange_tmul, zsmul_eq_mul]
  have he1 : ∀ x y : La, e (1 ⊗ₜ x) (1 ⊗ₜ y) = (EF x y : C) := fun x y => by rw [he]; simp
  let T : Submodule O (C ⊗[ℤ] La) := Submodule.span O (Set.range fun x : La => (1 : C) ⊗ₜ[ℤ] x)
  have hT : ∀ x : La, (1 : C) ⊗ₜ[ℤ] x ∈ T := fun x => Submodule.subset_span ⟨x, rfl⟩
  let b := Module.Free.chooseBasis ℤ La
  let B := Algebra.TensorProduct.basis C b
  have hB : ∀ i, B i = 1 ⊗ₜ b i := fun i => Algebra.TensorProduct.basis_apply b i
  choose b' hb' using fun i => h.unimod.2 (b.coord i)
  have hrep : ∀ i y, e (1 ⊗ₜ b' i) y = B.repr y i := by
    intro i y
    have : e (1 ⊗ₜ b' i) = B.coord i := B.ext fun j => by
      rw [Module.Basis.coord_apply, B.repr_self, hB, he1, hb', Module.Basis.coord_apply, b.repr_self]
      simp only [Finsupp.single_apply]
      split_ifs <;> simp
    rw [this]; rfl
  have hskew : ∀ x y, EF x y = -EF y x := fun x y => by
    have := h.alt (x + y)
    simp only [map_add, LinearMap.add_apply, h.alt] at this
    linarith
  have eskew : ∀ x y, e x y = -e y x := by
    intro x y
    induction x with
    | zero => simp
    | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]; ring
    | tmul s x =>
      induction y with
      | zero => simp
      | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]; ring
      | tmul t y => rw [he, he, hskew]; push_cast; ring
  have hTb : T = Submodule.span O (Set.range B) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      change (1 : C) ⊗ₜ[ℤ] x ∈ Submodule.span O (Set.range B)
      rw [← b.sum_repr x, tmul_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [tmul_smul, ← hB]
      exact zsmul_mem (Submodule.subset_span (R := O) (Set.mem_range_self (f := B) i)) _
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [hB]; exact hT _
  have hsp : Submodule.span C (T : Set (C ⊗[ℤ] La)) = ⊤ := by
    rw [hTb, Submodule.span_span_of_tower, B.span_eq]
  let w : Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E) → C ⊗[ℤ] La := fun q =>
    ρ (RingOfIntegers.basis E q.2) (1 ⊗ₜ u q.1)
  have hTw : T = Submodule.span O (Set.range w) := by
    apply le_antisymm
    · refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := Ideal.span {(p : O)}) ?_
        (IsAdicComplete.le_jacobson_bot _) ?_
      · rw [hTb]; exact Submodule.fg_span (Set.finite_range B)
      · refine Submodule.span_le.2 ?_
        rintro _ ⟨x, rfl⟩
        obtain ⟨a, x', rfl⟩ := h.span x
        change (1 : C) ⊗ₜ[ℤ] _ ∈ Submodule.span O (Set.range w) ⊔ Ideal.span {(p : O)} • T
        rw [tmul_add]
        refine Submodule.add_mem_sup ?_ ?_
        · rw [tmul_sum]
          refine Submodule.sum_mem _ fun i _ => ?_
          rw [← (RingOfIntegers.basis E).sum_repr (a i), Finset.sum_smul, tmul_sum]
          refine Submodule.sum_mem _ fun k _ => ?_
          rw [smul_assoc, tmul_smul]
          exact zsmul_mem (Submodule.subset_span (R := O) (Set.mem_range_self (f := w) (i, k))) _
        · rw [tmul_smul, ← Nat.cast_smul_eq_nsmul O]
          exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) (hT _)
    · rw [Submodule.span_le]
      rintro _ ⟨q, rfl⟩
      exact hT _
  refine ⟨ρ, T, e, fun a x => hρ a 1 x, rfl, ⟨?_, hsp, hTw⟩, he1, fun x => ?_, fun y hy => ?_, ?_, fun a x y => ?_⟩
  · refine linearIndependent_of_top_le_span_of_card_eq_finrank (b := w) ?_ ?_
    · rw [← hsp, hTw, Submodule.span_span_of_tower]
    · rw [Module.finrank_baseChange, h.rank, Fintype.card_prod, Fintype.card_fin,
        ← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank]
  · have := eskew x x
    have h2 : (2 : C) * e x x = 0 := by linear_combination this
    simpa using h2
  · exact B.ext_elem fun i => by rw [← hrep, hy]; simp
  · apply le_antisymm
    · intro y hy
      rw [hTb, ← B.sum_repr y]
      refine Submodule.sum_mem _ fun i _ => ?_
      obtain ⟨o, ho⟩ := hy _ (hT (b' i))
      rw [← hrep, ← ho, algebraMap_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨y, rfl⟩ x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨x, rfl⟩ := hx
        exact ⟨(EF x y : O), by rw [he1, map_intCast]⟩
      | zero => simp
      | add x x' _ _ hx hx' =>
        rw [map_add, LinearMap.add_apply]; exact Subring.add_mem _ hx hx'
      | smul o x _ hx =>
        rw [← algebraMap_smul C o x, map_smul, LinearMap.smul_apply, smul_eq_mul]
        exact Subring.mul_mem _ ⟨o, rfl⟩ hx
  · induction x with
    | zero => simp
    | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
    | tmul s x =>
      induction y with
      | zero => simp
      | add a b ha hb => simp only [map_add, ha, hb]
      | tmul t y => rw [hρ, hρ, he, he, h.adj]

end PositivityTheory.HtPt.Gi
