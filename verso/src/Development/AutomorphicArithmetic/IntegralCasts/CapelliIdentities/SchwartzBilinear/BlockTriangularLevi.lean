import Mathlib

namespace UpperTheory.Reformulated.B.P6.BlockTriangularLevi

open scoped Sigma DFunLike EquivLike Equiv Matrix CommSemiring CommRing Membership Set Preorder PartialOrder SemilatticeInf Lattice DistribLattice MulZeroClass Units Semiring HMul MulOne MulOneClass Monoid DivInvMonoid Group OfNat One Inv InvOneClass DivInvOneMonoid DivisionMonoid Subgroup Submonoid Subsemigroup Subtype SetLike MulZeroOneClass MonoidHom OneHom Pi PUnit Fin Finset HAdd AddMonoidWithOne AddGroupWithOne Ring DivisionRing Field CommGroup Circle DivisionSemiring Semifield Complex SeminormedRing SeminormedCommRing NormedCommRing NormedField AddChar Zero HSub

noncomputable def GlobalTheory.SmGL.blk :
    {α n : Type} → {m : α → Type} → (a : α) × m a ≃ n → n → α :=
  fun {α n : Type} {m : α → Type} (e : (a : α) × m a ≃ n) (i : n) ↦ Sigma.fst (β := fun (a : α) ↦ m a) (DFunLike.coe (β := fun (x_h1 : n) ↦ (a : α) × m a) e.symm i)

/- English proof (translation)
Use `show (e.symm (e ⟨a, i⟩)).1 = a`. Rewrite using `[Equiv.symm_apply_apply]`.
-/
theorem blockIndex_sigma_equiv {α n : Type} {m : α → Type} (e : (a : α) × m a ≃ n) (a : α) (i : m a) :
    GlobalTheory.SmGL.blk (m := m) e (e ⟨a, i⟩) = a := by
  show (e.symm (e ⟨a, i⟩)).1 = a
  rw [Equiv.symm_apply_apply]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.submatrix_apply, Matrix.mul_apply]`. Rewrite using `[← e.sum_comp, Fintype.sum_sigma, Finset.sum_eq_single a]`. Introduce `b _ hb`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises.

Introduce `l _`. Break down `lt_or_gt_of_ne hb with h | h` into its components or cases. Establish `h' : GlobalTheory.SmGL.blk (m` using `m) e (e ⟨b, l⟩) < GlobalTheory.SmGL.blk (m := m) e (e ⟨a, i⟩) := by`. Rewrite using `[blockIndex_sigma_equiv, blockIndex_sigma_equiv]`. Conclude with `h`.

Rewrite using `[hX h', zero_mul]`. Establish `h' : GlobalTheory.SmGL.blk (m` using `m) e (e ⟨a, j⟩) < GlobalTheory.SmGL.blk (m := m) e (e ⟨b, l⟩) := by`. Rewrite using `[blockIndex_sigma_equiv, blockIndex_sigma_equiv]`. Conclude with `h`. Rewrite using `[hY h', mul_zero]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ a) h`.
-/
theorem blockTriangular_mul_submatrix {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
    [∀ a, Fintype (m a)] [Fintype n] (e : (a : α) × m a ≃ n) (a : α) (X Y : Matrix n n R)
    (hX : X.BlockTriangular (GlobalTheory.SmGL.blk (m := m) e))
    (hY : Y.BlockTriangular (GlobalTheory.SmGL.blk (m := m) e)) :
    (X * Y).submatrix (fun i : m a => e ⟨a, i⟩) (fun i : m a => e ⟨a, i⟩)
      = X.submatrix (fun i : m a => e ⟨a, i⟩) (fun i : m a => e ⟨a, i⟩)
        * Y.submatrix (fun i : m a => e ⟨a, i⟩) (fun i : m a => e ⟨a, i⟩) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  rw [← e.sum_comp, Fintype.sum_sigma, Finset.sum_eq_single a]
  · intro b _ hb
    apply Finset.sum_eq_zero
    intro l _
    rcases lt_or_gt_of_ne hb with h | h
    · have h' : GlobalTheory.SmGL.blk (m := m) e (e ⟨b, l⟩) < GlobalTheory.SmGL.blk (m := m) e (e ⟨a, i⟩) := by
        rw [blockIndex_sigma_equiv, blockIndex_sigma_equiv]; exact h
      rw [hX h', zero_mul]
    · have h' : GlobalTheory.SmGL.blk (m := m) e (e ⟨a, j⟩) < GlobalTheory.SmGL.blk (m := m) e (e ⟨b, l⟩) := by
        rw [blockIndex_sigma_equiv, blockIndex_sigma_equiv]; exact h
      rw [hY h', mul_zero]
  · intro h
    exact absurd (Finset.mem_univ a) h

/- English proof (translation)
Introduce `R _ α n m _ _ _ e x y hx hy`. Use `show ((x * y : GL n R) : Matrix n n R).BlockTriangular _`. Rewrite using `[Units.val_mul]`. Conclude with `Matrix.BlockTriangular.mul hx hy`.
-/
theorem GlobalTheory.SmGL.parab_obl_1 :
    ∀ (R : Type) [inst_h0 : CommRing R] {α n : Type} {m : α → Type} [inst_h2 : LinearOrder α] [inst_h3 : Fintype n] [inst_h4 : DecidableEq n] (e : (a : α) × m a ≃ n) {x y : GL n R}, Membership.mem (γ := Set (GL n R)) {g : GL n R | g.val.BlockTriangular (GlobalTheory.SmGL.blk (m := m) e)} x → Membership.mem (γ := Set (GL n R)) {g : GL n R | g.val.BlockTriangular (GlobalTheory.SmGL.blk (m := m) e)} y → Membership.mem (γ := Set (GL n R)) {g : GL n R | g.val.BlockTriangular (GlobalTheory.SmGL.blk (m := m) e)} (x * y) := by
  intro R _ α n m _ _ _ e x y hx hy
  show ((x * y : GL n R) : Matrix n n R).BlockTriangular _
  rw [Units.val_mul]
  exact Matrix.BlockTriangular.mul hx hy

/- English proof (translation)
Introduce `R _ α n m _ _ _ e`. Use `show ((1 : GL n R) : Matrix n n R).BlockTriangular _`. Rewrite using `[Units.val_one]`. Conclude with `Matrix.blockTriangular_one`.
-/
theorem GlobalTheory.SmGL.parab_obl_2 :
    ∀ (R : Type) [inst_h0 : CommRing R] {α n : Type} {m : α → Type} [inst_h2 : LinearOrder α] [inst_h3 : Fintype n] [inst_h4 : DecidableEq n] (e : (a : α) × m a ≃ n), Membership.mem (γ := Set (GL n R)) {g : GL n R | g.val.BlockTriangular (GlobalTheory.SmGL.blk (m := m) e)} (OfNat.ofNat (nat_lit 1)) := by
  intro R _ α n m _ _ _ e
  show ((1 : GL n R) : Matrix n n R).BlockTriangular _
  rw [Units.val_one]
  exact Matrix.blockTriangular_one

/- English proof (translation)
Introduce `R _ α n m _ _ _ e x hx`. Use `show ((x⁻¹ : GL n R) : Matrix n n R).BlockTriangular _`. Rewrite using `[Matrix.coe_units_inv]`. Use `haveI : Invertible (x : Matrix n n R) := x.invertible`. Conclude with `Matrix.blockTriangular_inv_of_blockTriangular hx`.
-/
theorem GlobalTheory.SmGL.parab_obl_3 :
    ∀ (R : Type) [inst_h0 : CommRing R] {α n : Type} {m : α → Type} [inst_h2 : LinearOrder α] [inst_h3 : Fintype n] [inst_h4 : DecidableEq n] (e : (a : α) × m a ≃ n) {x : GL n R}, Membership.mem (γ := Set (GL n R)) {g : GL n R | g.val.BlockTriangular (GlobalTheory.SmGL.blk (m := m) e)} x → Membership.mem (γ := Set (GL n R)) {g : GL n R | g.val.BlockTriangular (GlobalTheory.SmGL.blk (m := m) e)} x⁻¹ := by
  intro R _ α n m _ _ _ e x hx
  show ((x⁻¹ : GL n R) : Matrix n n R).BlockTriangular _
  rw [Matrix.coe_units_inv]
  haveI : Invertible (x : Matrix n n R) := x.invertible
  exact Matrix.blockTriangular_inv_of_blockTriangular hx

noncomputable def GlobalTheory.SmGL.parab :
    (R : Type) → [inst_h0 : CommRing R] → {α n : Type} → {m : α → Type} → [inst_h2 : LinearOrder α] → [inst_h3 : Fintype n] → [inst_h4 : DecidableEq n] → (a : α) × m a ≃ n → Subgroup (GL n R) :=
  fun (R : Type) {inst_h0 : CommRing R} {α n : Type} {m : α → Type} {inst_h2 : LinearOrder α} {inst_h3 : Fintype n} {inst_h4 : DecidableEq n} (e : (a : α) × m a ≃ n) ↦ { carrier := {g : GL n R | g.val.BlockTriangular (GlobalTheory.SmGL.blk (m := m) e)}, mul_mem' := @GlobalTheory.SmGL.parab_obl_1 R inst_h0 α n m inst_h2 inst_h3 inst_h4 e, one_mem' := GlobalTheory.SmGL.parab_obl_2 R (m := m) e, inv_mem' := @GlobalTheory.SmGL.parab_obl_3 R inst_h0 α n m inst_h2 inst_h3 inst_h4 e }

@[reducible] noncomputable def GlobalTheory.SmGL.Levi :
    (R : Type) → [inst_h0 : CommRing R] → {α : Type} → (m : α → Type) → [inst_h2 : (a : α) → Fintype (m a)] → [inst_h3 : (a : α) → DecidableEq (m a)] → Type :=
  fun (R : Type) {inst_f0 : CommRing R} {α : Type} (m : α → Type) {inst_f1 : (a : α) → Fintype (m a)} {inst_f2 : (a : α) → DecidableEq (m a)} ↦ (a : α) → GL (m a) R

/- English proof (translation)
Introduce `R _ α n m _ _ _ _ _ e a`. Use `show ((1 : GL n R) : Matrix n n R).submatrix _ _ = 1`. Rewrite using `[Units.val_one]`. Conclude with `Matrix.submatrix_one _ (e.injective.comp sigma_mk_injective)`.
-/
theorem GlobalTheory.SmGL.diagBlock_obl_1 :
    ∀ (R : Type) [inst_h0 : CommRing R] {α n : Type} {m : α → Type} [inst_h2 : LinearOrder α] [inst_h3 : (a : α) → Fintype (m a)] [inst_h4 : (a : α) → DecidableEq (m a)] [inst_h5 : Fintype n] [inst_h6 : DecidableEq n] (e : (a : α) × m a ≃ n) (a : α), Eq (α := Matrix (m a) (m a) R) (Matrix.submatrix (m := n) (n := n) (Units.val (Subtype.val (p := fun (x : GL n R) ↦ Membership.mem (γ := Subgroup (GL n R)) (GlobalTheory.SmGL.parab R (m := m) e) x) (OfNat.ofNat (nat_lit 1)))) (fun (i : m a) ↦ DFunLike.coe (β := fun (x_h7 : (a : α) × m a) ↦ n) e (Sigma.mk (β := fun (a : α) ↦ m a) a i)) fun (i : m a) ↦ DFunLike.coe (β := fun (x_h8 : (a : α) × m a) ↦ n) e (Sigma.mk (β := fun (a : α) ↦ m a) a i)) (OfNat.ofNat (nat_lit 1)) := by
  intro R _ α n m _ _ _ _ _ e a
  show ((1 : GL n R) : Matrix n n R).submatrix _ _ = 1
  rw [Units.val_one]
  exact Matrix.submatrix_one _ (e.injective.comp sigma_mk_injective)

/- English proof (translation)
Introduce `R _ α n m _ _ _ _ _ _ e a x y`. Establish `hx : ((x : GL n R) : Matrix n n R).BlockTriangular (GlobalTheory.SmGL.blk (m` using `m) e) := x.2`. Establish `hy : ((y : GL n R) : Matrix n n R).BlockTriangular (GlobalTheory.SmGL.blk (m` using `m) e) := y.2`. Establish `key` using `blockTriangular_mul_submatrix e a _ _ hx hy`. Conclude with `key`.
-/
theorem GlobalTheory.SmGL.diagBlock_obl_2 :
    ∀ (R : Type) [inst_h0 : CommRing R] {α n : Type} {m : α → Type} [inst_h2 : Fintype α] [inst_h3 : LinearOrder α] [inst_h4 : (a : α) → Fintype (m a)] [inst_h5 : (a : α) → DecidableEq (m a)] [inst_h6 : Fintype n] [inst_h7 : DecidableEq n] (e : (a : α) × m a ≃ n) (a : α) (x y : ↥(GlobalTheory.SmGL.parab R (m := m) e)), ((x * y).val (p := fun (x : GL n R) ↦ Membership.mem (γ := Subgroup (GL n R)) (GlobalTheory.SmGL.parab R (m := m) e) x).val.submatrix (fun (i : m a) ↦ DFunLike.coe (β := fun (x_h8 : (a : α) × m a) ↦ n) e (Sigma.mk (β := fun (a : α) ↦ m a) a i)) fun (i : m a) ↦ DFunLike.coe (β := fun (x_h9 : (a : α) × m a) ↦ n) e (Sigma.mk (β := fun (a : α) ↦ m a) a i)) = HMul.hMul (α := Matrix (m a) (m a) R) (x.val (p := fun (x : GL n R) ↦ Membership.mem (γ := Subgroup (GL n R)) (GlobalTheory.SmGL.parab R (m := m) e) x).val.submatrix (fun (i : m a) ↦ DFunLike.coe (β := fun (x_h10 : (a : α) × m a) ↦ n) e (Sigma.mk (β := fun (a : α) ↦ m a) a i)) fun (i : m a) ↦ DFunLike.coe (β := fun (x_h11 : (a : α) × m a) ↦ n) e (Sigma.mk (β := fun (a : α) ↦ m a) a i)) (y.val (p := fun (x : GL n R) ↦ Membership.mem (γ := Subgroup (GL n R)) (GlobalTheory.SmGL.parab R (m := m) e) x).val.submatrix (fun (i : m a) ↦ DFunLike.coe (β := fun (x_h12 : (a : α) × m a) ↦ n) e (Sigma.mk (β := fun (a : α) ↦ m a) a i)) fun (i : m a) ↦ DFunLike.coe (β := fun (x_h13 : (a : α) × m a) ↦ n) e (Sigma.mk (β := fun (a : α) ↦ m a) a i)) := by
  intro R _ α n m _ _ _ _ _ _ e a x y
  have hx : ((x : GL n R) : Matrix n n R).BlockTriangular (GlobalTheory.SmGL.blk (m := m) e) := x.2
  have hy : ((y : GL n R) : Matrix n n R).BlockTriangular (GlobalTheory.SmGL.blk (m := m) e) := y.2
  have key := blockTriangular_mul_submatrix e a _ _ hx hy
  exact key

noncomputable def GlobalTheory.SmGL.diagBlock :
    (R : Type) → [inst_h0 : CommRing R] → {α n : Type} → {m : α → Type} → [inst_h2 : Fintype α] → [inst_h3 : LinearOrder α] → [inst_h4 : (a : α) → Fintype (m a)] → [inst_h5 : (a : α) → DecidableEq (m a)] → [inst_h6 : Fintype n] → [inst_h7 : DecidableEq n] → (e : (a : α) × m a ≃ n) → (a : α) → ↥(GlobalTheory.SmGL.parab R (m := m) e) →* Matrix (m a) (m a) R :=
  fun (R : Type) {inst_f3 : CommRing R} {α n : Type} {m : α → Type} {inst_f4 : Fintype α} {inst_f5 : LinearOrder α} {inst_f6 : (a : α) → Fintype (m a)} {inst_f7 : (a : α) → DecidableEq (m a)} {inst_f8 : Fintype n} {inst_f9 : DecidableEq n} (e : (a : α) × m a ≃ n) (a : α) ↦ { toFun := fun (p : ↥(GlobalTheory.SmGL.parab R (m := m) e)) ↦ p.val (p := fun (x : GL n R) ↦ Membership.mem (γ := Subgroup (GL n R)) (GlobalTheory.SmGL.parab R (m := m) e) x).val.submatrix (fun (i : m a) ↦ DFunLike.coe (β := fun (x_h8 : (a : α) × m a) ↦ n) e (Sigma.mk (β := fun (a : α) ↦ m a) a i)) fun (i : m a) ↦ DFunLike.coe (β := fun (x_h9 : (a : α) × m a) ↦ n) e (Sigma.mk (β := fun (a : α) ↦ m a) a i), map_one' := GlobalTheory.SmGL.diagBlock_obl_1 R (m := m) e a, map_mul' := GlobalTheory.SmGL.diagBlock_obl_2 R (m := m) e a }

noncomputable def GlobalTheory.SmGL.leviProj :
    (R : Type) → [inst_h0 : CommRing R] → {α n : Type} → {m : α → Type} → [inst_h2 : Fintype α] → [inst_h3 : LinearOrder α] → [inst_h4 : (a : α) → Fintype (m a)] → [inst_h5 : (a : α) → DecidableEq (m a)] → [inst_h6 : Fintype n] → [inst_h7 : DecidableEq n] → (e : (a : α) × m a ≃ n) → ↥(GlobalTheory.SmGL.parab R (m := m) e) →* GlobalTheory.SmGL.Levi R m :=
  fun (R : Type) {inst_f10 : CommRing R} {α n : Type} {m : α → Type} {inst_f11 : Fintype α} {inst_f12 : LinearOrder α} {inst_f13 : (a : α) → Fintype (m a)} {inst_f14 : (a : α) → DecidableEq (m a)} {inst_f15 : Fintype n} {inst_f16 : DecidableEq n} (e : (a : α) × m a ≃ n) ↦ MonoidHom.pi (f := fun (a : α) ↦ GL (m a) R) fun (a : α) ↦ MonoidHom.toHomUnits (GlobalTheory.SmGL.diagBlock R (m := m) e a)

noncomputable def GlobalTheory.SmGL.unipRad :
    (R : Type) → [inst_h0 : CommRing R] → {α n : Type} → {m : α → Type} → [inst_h2 : Fintype α] → [inst_h3 : LinearOrder α] → [inst_h4 : (a : α) → Fintype (m a)] → [inst_h5 : (a : α) → DecidableEq (m a)] → [inst_h6 : Fintype n] → [inst_h7 : DecidableEq n] → (a : α) × m a ≃ n → Subgroup (GL n R) :=
  fun (R : Type) {inst_f17 : CommRing R} {α n : Type} {m : α → Type} {inst_f18 : Fintype α} {inst_f19 : LinearOrder α} {inst_f20 : (a : α) → Fintype (m a)} {inst_f21 : (a : α) → DecidableEq (m a)} {inst_f22 : Fintype n} {inst_f23 : DecidableEq n} (e : (a : α) × m a ≃ n) ↦ Subgroup.map (G := ↥(GlobalTheory.SmGL.parab R (m := m) e)) (Subgroup.subtype (GlobalTheory.SmGL.parab R (m := m) e)) (MonoidHom.ker (GlobalTheory.SmGL.leviProj R (m := m) e))

noncomputable def GlobalTheory.SmGL.points :
    (n : Type) → (_ : n) × Unit ≃ n :=
  fun (n : Type) ↦ Equiv.sigmaUnique n fun (x_h0 : n) ↦ Unit

noncomputable def GlobalTheory.SmGL.unipB :
    (R : Type) → [inst_h0 : CommRing R] → (n : Type) → [inst_h1 : Fintype n] → [inst_h2 : DecidableEq n] → [inst_h3 : LinearOrder n] → Subgroup (GL n R) :=
  fun (R : Type) {inst_f24 : CommRing R} (n : Type) {inst_f25 : Fintype n} {inst_f26 : DecidableEq n} {inst_f27 : LinearOrder n} ↦ GlobalTheory.SmGL.unipRad R (m := fun (a : n) ↦ Unit) (GlobalTheory.SmGL.points n)

noncomputable def GlobalTheory.Whittaker.superDiag :
    {R : Type} → [inst_h0 : CommRing R] → {n : ℕ} → GL (Fin n) R → R :=
  fun {R : Type} {inst_f28 : CommRing R} {n : ℕ} (g : GL (Fin n) R) ↦ ∑ i : Fin n, ∑ j : Fin n with j.val = i.val + OfNat.ofNat (nat_lit 1), g.val i j

noncomputable def DiscreteGroups.sglob.LConv.IsWhitTest :
    {k : Type} → [inst_h0 : Field k] → [inst_h1 : TopologicalSpace k] → {m : ℕ} → AddChar k Circle → (GL (Fin m) k → ℂ) → Prop :=
  fun {k : Type} {inst_f29 : Field k} {inst_f30 : TopologicalSpace k} {m : ℕ} (ψ : AddChar k Circle) (f : GL (Fin m) k → ℂ) ↦ (∀ (u : GL (Fin m) k), Membership.mem (γ := Subgroup (GL (Fin m) k)) (GlobalTheory.SmGL.unipB k (Fin m)) u → ∀ (g : GL (Fin m) k), f (u * g) = Subtype.val (p := fun (x : ℂ) ↦ Membership.mem (γ := Submonoid ℂ) (Submonoid.unitSphere ℂ) x) (DFunLike.coe (β := fun (x_h4 : k) ↦ Circle) ψ (GlobalTheory.Whittaker.superDiag u)) * f g) ∧ IsLocallyConstant f ∧ ∃ (C : Set (GL (Fin m) k)), IsCompact C ∧ ∀ (g : GL (Fin m) k), f g ≠ OfNat.ofNat (nat_lit 0) → ∃ (u : GL (Fin m) k), Membership.mem (γ := Subgroup (GL (Fin m) k)) (GlobalTheory.SmGL.unipB k (Fin m)) u ∧ ∃ c ∈ C, g = u * c

/- English proof (translation)
Introduce `k _ _ m ψ f f' hf hf'`. Unfold `DiscreteGroups.sglob.LConv.IsWhitTest at hf hf' ⊢`. Take `⟨h1, h2, C, hC, h3⟩` from `hf`. Take `⟨h1', h2', C', hC', h3'⟩` from `hf'`. Use `⟨?_, h2.sub h2', C ∪ C', hC.union hC', ?_⟩` and prove the remaining obligations.

Introduce `u hu g beta_reduce`. Rewrite using `[h1 u hu g, h1' u hu g, mul_sub]`. Introduce `g hg beta_reduce at hg`. Distinguish the cases in `hfg : f g = 0`. Establish `hfg' : f' g ≠ 0`.

Introduce `h`. Apply `hg` to reduce the goal to its premises. Rewrite using `[hfg, h, sub_zero]`. Take `⟨u, hu, c, hc, rfl⟩` from `h3' g hfg'`. Conclude with `⟨u, hu, c, Set.mem_union_right _ hc, rfl⟩`.

Take `⟨u, hu, c, hc, rfl⟩` from `h3 g hfg`. Conclude with `⟨u, hu, c, Set.mem_union_left _ hc, rfl⟩`.
-/
theorem DiscreteGroups.sglob.LConv.IsWhitTest.sub :
    ∀ {k : Type} [inst_h0 : Field k] [inst_h1 : TopologicalSpace k] {m : ℕ} {ψ : AddChar k Circle} {f f' : GL (Fin m) k → ℂ}, DiscreteGroups.sglob.LConv.IsWhitTest ψ f → DiscreteGroups.sglob.LConv.IsWhitTest ψ f' → DiscreteGroups.sglob.LConv.IsWhitTest (m := m) ψ fun (g : GL (Fin m) k) ↦ f g - f' g := by
  intro k _ _ m ψ f f' hf hf'
  unfold DiscreteGroups.sglob.LConv.IsWhitTest at hf hf' ⊢
  obtain ⟨h1, h2, C, hC, h3⟩ := hf
  obtain ⟨h1', h2', C', hC', h3'⟩ := hf'
  refine ⟨?_, h2.sub h2', C ∪ C', hC.union hC', ?_⟩
  · intro u hu g
    beta_reduce
    rw [h1 u hu g, h1' u hu g, mul_sub]
  · intro g hg
    beta_reduce at hg
    by_cases hfg : f g = 0
    · have hfg' : f' g ≠ 0 := by
        intro h
        apply hg
        rw [hfg, h, sub_zero]
      obtain ⟨u, hu, c, hc, rfl⟩ := h3' g hfg'
      exact ⟨u, hu, c, Set.mem_union_right _ hc, rfl⟩
    · obtain ⟨u, hu, c, hc, rfl⟩ := h3 g hfg
      exact ⟨u, hu, c, Set.mem_union_left _ hc, rfl⟩

end UpperTheory.Reformulated.B.P6.BlockTriangularLevi
