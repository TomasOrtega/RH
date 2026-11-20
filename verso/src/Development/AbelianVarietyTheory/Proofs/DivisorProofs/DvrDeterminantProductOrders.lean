import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasisOfBot
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

noncomputable section
namespace GlobalTheory.ShiftBasis

section Lat
variable {O : Type} [CommRing O] (C : Type) [Field C] [Algebra O C] {Λ : Type} [CommRing Λ] {h : ℕ}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨t, ht⟩`. Use `⟨z.2, ?_⟩` and prove the remaining obligations. Use `Submodule.mem_sup.2 ⟨incl C h t, Submodule.mem_map_of_mem Submodule.mem_top, -((fun i => algebraMap O C (t i)) - (z : Fin h → C)), ?_, ?_⟩` and prove the remaining obligations. Conclude with `(Submodule.restrictScalars_mem _ _ _).2 (Submodule.neg_mem _ ht)`.

Use extensionality with `i`. Simplify using `[incl]`. Introduce and unpack `⟨-, hz⟩`. Take `⟨y, hy, u, hu, hyu⟩` from `Submodule.mem_sup.1 hz`. Take `⟨t, -, rfl⟩` from `Submodule.mem_map.1 hy`.

Use `⟨t, ?_⟩` and prove the remaining obligations. Establish `: (fun i => algebraMap O C (t i)) - (z : Fin h → C) = -u`. Rewrite using `[← hyu]`. Use extensionality with `i`. Simplify using `[incl]`.

Rewrite using `[this]`. Conclude with `Submodule.neg_mem _ ((Submodule.restrictScalars_mem _ _ _).1 hu)`.
-/
theorem mem_quotLattice_iff (ρ : Λ → Matrix (Fin h) (Fin h) O) (τ : Λ →+* O) (z : eig C ρ τ) :
    z ∈ quotLattice C ρ τ ↔ (z : Fin h → C) ∈ eigPart C ρ τ ⊤ := by
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨z.2, ?_⟩
    refine Submodule.mem_sup.2 ⟨incl C h t, Submodule.mem_map_of_mem Submodule.mem_top,
      -((fun i => algebraMap O C (t i)) - (z : Fin h → C)), ?_, ?_⟩
    · exact (Submodule.restrictScalars_mem _ _ _).2 (Submodule.neg_mem _ ht)
    · ext i; simp [incl]
  · rintro ⟨-, hz⟩
    obtain ⟨y, hy, u, hu, hyu⟩ := Submodule.mem_sup.1 hz
    obtain ⟨t, -, rfl⟩ := Submodule.mem_map.1 hy
    refine ⟨t, ?_⟩
    have : (fun i => algebraMap O C (t i)) - (z : Fin h → C) = -u := by
      rw [← hyu]; ext i; simp [incl]
    rw [this]
    exact Submodule.neg_mem _ ((Submodule.restrictScalars_mem _ _ _).1 hu)
end Lat

section Wedge
variable (C : Type) [Field C]

/- English proof (translation)
Use `set f := (exteriorPower.ιMulti C N (M := M)).compLinearMap (Fintype.linearCombination C x)`. Establish `h3 : f (fun i => c i) = exteriorPower.ιMulti C N (fun i => ∑ j, c i j • x j)`. Simplify using `only [f, AlternatingMap.compLinearMap_apply, Fintype.linearCombination_apply]`. Establish `h4 : f (Pi.basisFun C (Fin N)) = exteriorPower.ιMulti C N x`. Simplify using `only [f, AlternatingMap.compLinearMap_apply]`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using `[Fintype.linearCombination_apply, Pi.single_apply]`. Establish `key : ∀ ψ : Module.Dual C (⋀[C]^N M), ψ (f (fun i => c i)) = ψ (c.det • f (Pi.basisFun C (Fin N)))`. Introduce `ψ`.

Establish `h` using `AlternatingMap.eq_smul_basis_det (Pi.basisFun C (Fin N)) (ψ.compAlternatingMap f)`. Use `congrArg (fun g => g (fun i => c i)) h` as an intermediate fact. Simplify using `only [LinearMap.compAlternatingMap_apply, AlternatingMap.smul_apply, smul_eq_mul, Pi.basisFun_det_apply] at this`. Rewrite using `[this, map_smul, smul_eq_mul, mul_comm]`. Both sides reduce to the same expression.

Establish `: f (fun i => c i) - c.det • f (Pi.basisFun C (Fin N)) = 0`. Rewrite using `[← Module.forall_dual_apply_eq_zero_iff C]`. Introduce `ψ`. Rewrite using `[map_sub, key, sub_self]`. Rewrite using `[← h3, ← h4]`.

Conclude with `sub_eq_zero.mp this`.
-/
theorem iotaMulti_comb {M : Type} [AddCommGroup M] [Module C M] (N : ℕ) (x : Fin N → M)
    (c : Matrix (Fin N) (Fin N) C) :
    exteriorPower.ιMulti C N (fun i => ∑ j, c i j • x j) = c.det • exteriorPower.ιMulti C N x := by
  set f := (exteriorPower.ιMulti C N (M := M)).compLinearMap (Fintype.linearCombination C x)
  have h3 : f (fun i => c i) = exteriorPower.ιMulti C N (fun i => ∑ j, c i j • x j) := by
    simp only [f, AlternatingMap.compLinearMap_apply, Fintype.linearCombination_apply]
  have h4 : f (Pi.basisFun C (Fin N)) = exteriorPower.ιMulti C N x := by
    simp only [f, AlternatingMap.compLinearMap_apply]
    congr 1; funext i
    simp [Fintype.linearCombination_apply, Pi.single_apply]
  have key : ∀ ψ : Module.Dual C (⋀[C]^N M), ψ (f (fun i => c i)) =
      ψ (c.det • f (Pi.basisFun C (Fin N))) := by
    intro ψ
    have h := AlternatingMap.eq_smul_basis_det (Pi.basisFun C (Fin N)) (ψ.compAlternatingMap f)
    have := congrArg (fun g => g (fun i => c i)) h
    simp only [LinearMap.compAlternatingMap_apply, AlternatingMap.smul_apply, smul_eq_mul,
      Pi.basisFun_det_apply] at this
    rw [this, map_smul, smul_eq_mul, mul_comm]
    rfl
  have : f (fun i => c i) - c.det • f (Pi.basisFun C (Fin N)) = 0 := by
    rw [← Module.forall_dual_apply_eq_zero_iff C]
    intro ψ; rw [map_sub, key, sub_self]
  rw [← h3, ← h4]
  exact sub_eq_zero.mp this

end Wedge

/- English proof (translation)
Introduce `p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ a b h D τ w n hw hn`. Use `set E := eigPart C (actT D) τ ⊤ with hE`. Establish `hwQ : ∀ i, w i ∈ E ∧ alC C D (w i) = 0`. Introduce `i`. Establish `: w i ∈ wQuot C D τ` using `hw.2 ▸ Submodule.subset_span ⟨i, rfl⟩`.

Conclude with `⟨this.1, this.2⟩`. Establish `hnQ : ∀ j, ∃ y, y ∈ E ∧ alC C D y = n j`. Introduce `j`. Establish `: n j ∈ alQuot C D τ` using `hn.2 ▸ Submodule.subset_span ⟨j, rfl⟩`. Take `⟨y, hy, hyj⟩` from `Submodule.mem_map.1 this`.

Conclude with `⟨y, hy, hyj⟩`. Use `choose t htE htn using hnQ`. Use `set vec : Fin (a + b) → Fin h → C := Fin.append w t with hvec`. Establish `hvecE : ∀ i, vec i ∈ E`. Introduce `i`.

Use `Fin.addCases (fun j => ?_) (fun j => ?_) i` and prove the remaining obligations. Simplify `(hwQ j).1` using `[vec]`. Simplify `htE j` using `[vec]`. Establish `hEeig : ∀ y ∈ E, y ∈ eig C (actT D) τ` using `fun y hy => hy.1`. Set `x : Fin (a + b) → eig C (actT D) τ` to `fun i => ⟨vec i, hEeig _ (hvecE i)⟩`.

Establish `hxv : ∀ i, (x i : Fin h → C) = vec i` using `fun i => rfl`. Establish `hspan : Submodule.span O (Set.range vec) = E`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`.

Conclude with `hvecE i`. Introduce `y hy`. Establish `h1 : alC C D y ∈ alQuot C D τ` using `Submodule.mem_map_of_mem (f := (alC C D).restrictScalars O) hy`. Rewrite `h1` using `[← hn.2]`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun O).1 h1`.

Establish `h2 : y - ∑ j, c j • t j ∈ wQuot C D τ`. Use `⟨E.sub_mem hy (E.sum_mem fun j _ => E.smul_mem _ (htE j)), ?_⟩` and prove the remaining obligations. Use `show alC C D (y - ∑ j, c j • t j) = 0`. Rewrite using `[map_sub, map_sum, ← hc]`. Simplify using `only [LinearMap.map_smul_of_tower, htn, sub_self]`.

Rewrite `h2` using `[← hw.2]`. Take `⟨d, hd⟩` from `(Submodule.mem_span_range_iff_exists_fun O).1 h2`. Establish `: y = ∑ i, d i • vec (Fin.castAdd b i) + ∑ j, c j • vec (Fin.natAdd a j)`. Simplify using `only [vec, Fin.append_left, Fin.append_right]`. Rewrite using `[hd]`.

Normalize the expressions using the abelian group laws. Rewrite using `[this]`. Apply the tactic sequence `refine Submodule.add_mem _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_) (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_) <;>`. Conclude with `Submodule.subset_span ⟨_, rfl⟩`. Establish `hind : LinearIndependent C vec`.

Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg`. Rewrite `hg` using `[Fin.sum_univ_add]`. Simplify using `only [vec, Fin.append_left, Fin.append_right] at hg`. Establish `h1` using `congrArg (alC C D) hg`.

Simplify using `only [map_add, map_sum, map_smul, (hwQ _).2, smul_zero, Finset.sum_const_zero, zero_add, htn, map_zero] at h1`. Establish `hb : ∀ j, g (Fin.natAdd a j) = 0` using `(Fintype.linearIndependent_iff.1 hn.1) (fun j => g (Fin.natAdd a j)) h1`. Simplify using `only [hb, zero_smul, Finset.sum_const_zero, add_zero] at hg`. Establish `ha : ∀ i, g (Fin.castAdd b i) = 0` using `(Fintype.linearIndependent_iff.1 hw.1) (fun i => g (Fin.castAdd b i)) hg`. Introduce `i`.

Conclude with `Fin.addCases ha hb i`. Use `⟨x, fun i => by simp [x, vec], fun i => by simp [x, vec, htn], ⟨hind, hspan⟩, ?_⟩` and prove the remaining obligations. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[detLattice, Submodule.span_le]`. Introduce and unpack `_ ⟨z, hz, rfl⟩`.

Establish `hzE : ∀ i, (z i : Fin h → C) ∈ Submodule.span O (Set.range vec)` using `fun i => by`. Rewrite using `[hspan]`. Conclude with `(mem_quotLattice_iff C _ _ _).1 (hz i)`. Use `choose c hc using fun i => (Submodule.mem_span_range_iff_exists_fun O).1 (hzE i)`. Establish `hzc : z = fun i => ∑ j, (Matrix.of fun i j => algebraMap O C (c i j)) i j • x j`.

Use function extensionality and compare the values at `i`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← hc i, Submodule.coe_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Submodule.coe_smul, hxv, Matrix.of_apply, algebraMap_smul]`.

Establish `hdet : (Matrix.of fun i j => algebraMap O C (c i j)).det = algebraMap O C (Matrix.of c).det`. Rewrite using `[RingHom.map_det]`. Both sides reduce to the same expression. Rewrite using `[hzc, iotaMulti_comb, hdet, algebraMap_smul]`. Conclude with `Submodule.mem_span_singleton.2 ⟨_, rfl⟩`.

Rewrite using `[Submodule.span_le, Set.singleton_subset_iff]`. Conclude with `Submodule.subset_span ⟨x, fun i => (mem_quotLattice_iff C _ _ _).2 (hvecE i), rfl⟩`.
-/
theorem shift_basis : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (a b h : ℕ) (D : Datum ε h Λ) (τ : Λ →+* O) (w : Fin a → Fin h → C) (n : Fin b → Fin h → C), IsBasisOf C (wQuot C D τ) w → IsBasisOf C (alQuot C D τ) n → ∃ x : Fin (a + b) → eig C (actT D) τ, (∀ i, (x (Fin.castAdd b i) : Fin h → C) = w i) ∧ (∀ i, alC C D (x (Fin.natAdd a i)) = n i) ∧ IsBasisOf C (eigPart C (actT D) τ ⊤) (fun i => (x i : Fin h → C)) ∧ detLattice C (actT D) τ (a + b) = Submodule.span O {exteriorPower.ιMulti C (a + b) x} := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ a b h D τ w n hw hn
  set E := eigPart C (actT D) τ ⊤ with hE
  have hwQ : ∀ i, w i ∈ E ∧ alC C D (w i) = 0 := by
    intro i
    have : w i ∈ wQuot C D τ := hw.2 ▸ Submodule.subset_span ⟨i, rfl⟩
    exact ⟨this.1, this.2⟩
  have hnQ : ∀ j, ∃ y, y ∈ E ∧ alC C D y = n j := by
    intro j
    have : n j ∈ alQuot C D τ := hn.2 ▸ Submodule.subset_span ⟨j, rfl⟩
    obtain ⟨y, hy, hyj⟩ := Submodule.mem_map.1 this
    exact ⟨y, hy, hyj⟩
  choose t htE htn using hnQ
  set vec : Fin (a + b) → Fin h → C := Fin.append w t with hvec
  have hvecE : ∀ i, vec i ∈ E := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa [vec] using (hwQ j).1
    · simpa [vec] using htE j
  have hEeig : ∀ y ∈ E, y ∈ eig C (actT D) τ := fun y hy => hy.1
  let x : Fin (a + b) → eig C (actT D) τ := fun i => ⟨vec i, hEeig _ (hvecE i)⟩
  have hxv : ∀ i, (x i : Fin h → C) = vec i := fun i => rfl
  have hspan : Submodule.span O (Set.range vec) = E := by
    apply le_antisymm
    · rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; exact hvecE i
    · intro y hy
      have h1 : alC C D y ∈ alQuot C D τ := Submodule.mem_map_of_mem (f := (alC C D).restrictScalars O) hy
      rw [← hn.2] at h1
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 h1
      have h2 : y - ∑ j, c j • t j ∈ wQuot C D τ := by
        refine ⟨E.sub_mem hy (E.sum_mem fun j _ => E.smul_mem _ (htE j)), ?_⟩
        show alC C D (y - ∑ j, c j • t j) = 0
        rw [map_sub, map_sum, ← hc]
        simp only [LinearMap.map_smul_of_tower, htn, sub_self]
      rw [← hw.2] at h2
      obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 h2
      have : y = ∑ i, d i • vec (Fin.castAdd b i) + ∑ j, c j • vec (Fin.natAdd a j) := by
        simp only [vec, Fin.append_left, Fin.append_right]
        rw [hd]; abel
      rw [this]
      refine Submodule.add_mem _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_)
        (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_) <;>
        exact Submodule.subset_span ⟨_, rfl⟩
  have hind : LinearIndependent C vec := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_add] at hg
    simp only [vec, Fin.append_left, Fin.append_right] at hg
    have h1 := congrArg (alC C D) hg
    simp only [map_add, map_sum, map_smul, (hwQ _).2, smul_zero, Finset.sum_const_zero, zero_add,
      htn, map_zero] at h1
    have hb : ∀ j, g (Fin.natAdd a j) = 0 :=
      (Fintype.linearIndependent_iff.1 hn.1) (fun j => g (Fin.natAdd a j)) h1
    simp only [hb, zero_smul, Finset.sum_const_zero, add_zero] at hg
    have ha : ∀ i, g (Fin.castAdd b i) = 0 :=
      (Fintype.linearIndependent_iff.1 hw.1) (fun i => g (Fin.castAdd b i)) hg
    intro i
    exact Fin.addCases ha hb i
  refine ⟨x, fun i => by simp [x, vec], fun i => by simp [x, vec, htn], ⟨hind, hspan⟩, ?_⟩
  apply le_antisymm
  · rw [detLattice, Submodule.span_le]
    rintro _ ⟨z, hz, rfl⟩
    have hzE : ∀ i, (z i : Fin h → C) ∈ Submodule.span O (Set.range vec) := fun i => by
      rw [hspan]; exact (mem_quotLattice_iff C _ _ _).1 (hz i)
    choose c hc using fun i => (Submodule.mem_span_range_iff_exists_fun O).1 (hzE i)
    have hzc : z = fun i => ∑ j, (Matrix.of fun i j => algebraMap O C (c i j)) i j • x j := by
      funext i; apply Subtype.ext
      rw [← hc i, Submodule.coe_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Submodule.coe_smul, hxv, Matrix.of_apply, algebraMap_smul]
    have hdet : (Matrix.of fun i j => algebraMap O C (c i j)).det
        = algebraMap O C (Matrix.of c).det := by
      rw [RingHom.map_det]; rfl
    rw [hzc, iotaMulti_comb, hdet, algebraMap_smul]
    exact Submodule.mem_span_singleton.2 ⟨_, rfl⟩
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact Submodule.subset_span ⟨x, fun i => (mem_quotLattice_iff C _ _ _).2 (hvecE i), rfl⟩

end GlobalTheory.ShiftBasis
