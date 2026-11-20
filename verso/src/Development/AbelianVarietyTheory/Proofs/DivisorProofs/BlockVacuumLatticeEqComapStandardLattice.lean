import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkLat
import Formalism.LocalToGlobal.InertKernelTheory.StatementAlg
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.BaseVacuum
open Classical

namespace GlobalTheory.BaseVacuum

/- English proof (translation)
Rewrite using `[B.gC_spec]`. Use function extensionality and compare the values at `w'`. Simplify using `only [xv, LinearEquiv.apply_symm_apply]`. Distinguish the cases in `h : w' = w`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[h]`.
-/
theorem gC_xv {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (w : Fin 4 × D.what₂.Tau) :
    B.gC (fun w' => TaylorLogMetric.embT D w'.2 (xv B w w'.1)) = Pi.single w 1 := by
  rw [B.gC_spec]
  funext w'
  simp only [xv, LinearEquiv.apply_symm_apply]
  by_cases h : w' = w
  · subst h; simp
  · simp [h]

/- English proof (translation)
Use function extensionality and compare the values at `w`. Simplify using `only [blk, TaylorLogMetric.embV, TaylorLogMetric.tor0, putB, Prod.mk.eta, Equiv.symm_apply_apply]`. Distinguish the cases in `h : k' = k`. Simplify using `[h]`. Simplify using `[h]`.
-/
theorem blk_embV_putB (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {n n' : ℕ} (k k' : Fin n' × Fin n)
    (x : Fin 4 → D.host.E) :
    blk D k' (TaylorLogMetric.embV D (TaylorLogMetric.tor0 D cc δ) (putB D k x) : TaylorLogMetric.VC D (n * 2) (n' * 2)) =
      if k' = k then (fun w => TaylorLogMetric.embT D w.2 (x w.1)) else (0 : Fin 4 × D.what₂.Tau → ℂ) := by
  funext w
  simp only [blk, TaylorLogMetric.embV, TaylorLogMetric.tor0, putB, Prod.mk.eta, Equiv.symm_apply_apply]
  by_cases h : k' = k
  · simp [h]
  · simp [h]

/- English proof (translation)
Use function extensionality and compare the values at `p`. Rewrite using `[phi_apply, bas, blk_embV_putB]`. Distinguish the cases in `h : p.1 = (ixE D n n' j).1`. Rewrite using `[if_pos h, gC_xv]`. Distinguish the cases in `h2 : p.2 = (ixE D n n' j).2`.

Establish `: p = ixE D n n' j` using `Prod.ext h h2`. Substitute `this` using the available equality. Simplify using the standard rewrite rules. Establish `: p ≠ ixE D n n' j` using `fun e => h2 (by rw [e])`. Simplify using `[h2, this]`.

Rewrite using `[if_neg h, B.gC.map_zero]`. Establish `: p ≠ ixE D n n' j` using `fun e => h (by rw [e])`. Simplify using `[this]`.
-/
theorem phi_embV_bas {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (n n' : ℕ)
    (j : Fin (TaylorLogMetric.fF D * (n * 2) * (n' * 2))) :
    phi B n n' (TaylorLogMetric.embV D (TaylorLogMetric.tor0 D cc δ) (bas B n n' j)) = Pi.single (ixE D n n' j) 1 := by
  funext p
  rw [phi_apply, bas, blk_embV_putB]
  by_cases h : p.1 = (ixE D n n' j).1
  · rw [if_pos h, gC_xv]
    by_cases h2 : p.2 = (ixE D n n' j).2
    · have : p = ixE D n n' j := Prod.ext h h2
      subst this; simp
    · have : p ≠ ixE D n n' j := fun e => h2 (by rw [e])
      simp [h2, this]
  · rw [if_neg h, B.gC.map_zero]
    have : p ≠ ixE D n n' j := fun e => h (by rw [e])
    simp [this]

/- English proof (translation)
Introduce `D cc δ B n n'`. Apply `le_antisymm` to reduce the goal to its premises. Unfold `StandardLatticesGL3.LaB`. Rewrite using `[AddSubgroup.closure_le]`. Introduce and unpack `z ⟨w, hw, j, rfl⟩`.

Use `show phi B n n' (w • TaylorLogMetric.embV D (TaylorLogMetric.tor0 D cc δ) (bas B n n' j)) ∈ stdLat B.L (Ix D n n')`. Rewrite using `[map_smul, phi_embV_bas]`. Establish `hw' : w ∈ B.L.lattice.toAddSubgroup` using `by rw [B.lat]; exact hw`. Simplify using `only [stdLat, AddSubgroup.mem_pi, Set.mem_univ, true_implies]`. Introduce `p`.

Distinguish the cases in `h : p = ixE D n n' j`. Substitute `h` using the available equality. Simplify using `using hw'`. Simplify using `[h]`. Introduce `x hx`.

Establish `hx' : phi B n n' x ∈ stdLat B.L (Ix D n n')` using `hx`. Simplify using `only [stdLat, AddSubgroup.mem_pi, Set.mem_univ, true_implies] at hx'`. Establish `hsum : phi B n n' x = ∑ p, phi B n n' x p • (Pi.single p 1 : Ix D n n' → ℂ)`. Use function extensionality and compare the values at `q`. Simplify using `[Finset.sum_apply, Pi.single_apply]`.

Establish `hsing : ∀ p, (phi B n n').symm (Pi.single p 1) = TaylorLogMetric.embV D (TaylorLogMetric.tor0 D cc δ) (bas B n n' ((ixE D n n').symm p))`. Introduce `p`. Rewrite using `[LinearEquiv.symm_apply_eq, phi_embV_bas, Equiv.apply_symm_apply]`. Establish `hxe : x = ∑ p, phi B n n' x p • TaylorLogMetric.embV D (TaylorLogMetric.tor0 D cc δ) (bas B n n' ((ixE D n n').symm p))` using `by conv_lhs => rw [← (phi B n n').symm_apply_apply x, hsum]`. Rewrite using `[map_sum]`.

Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, hsing]`. Rewrite using `[hxe]`. Use `AddSubgroup.sum_mem _ fun p _ => AddSubgroup.subset_closure ?_` and prove the remaining obligations. Use `⟨phi B n n' x p, ?_, (ixE D n n').symm p, rfl⟩` and prove the remaining obligations.

Use `hx' p` as an intermediate fact. Rewrite `this` using `[B.lat]`. Conclude with `this`.
-/
theorem laB_eq_comap : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (n n' : ℕ),
    StandardLatticesGL3.LaB D (TaylorLogMetric.tor0 D cc δ) (bas B n n') =
      (stdLat B.L (Ix D n n')).comap (phi B n n' : TaylorLogMetric.VC D (n * 2) (n' * 2) →ₗ[ℂ] (Ix D n n' → ℂ)).toAddMonoidHom := by
  intro D cc δ B n n'
  apply le_antisymm
  · unfold StandardLatticesGL3.LaB
    rw [AddSubgroup.closure_le]
    rintro z ⟨w, hw, j, rfl⟩
    show phi B n n' (w • TaylorLogMetric.embV D (TaylorLogMetric.tor0 D cc δ) (bas B n n' j)) ∈ stdLat B.L (Ix D n n')
    rw [map_smul, phi_embV_bas]
    have hw' : w ∈ B.L.lattice.toAddSubgroup := by rw [B.lat]; exact hw
    simp only [stdLat, AddSubgroup.mem_pi, Set.mem_univ, true_implies]
    intro p
    by_cases h : p = ixE D n n' j
    · subst h; simpa using hw'
    · simp [h]
  · intro x hx
    have hx' : phi B n n' x ∈ stdLat B.L (Ix D n n') := hx
    simp only [stdLat, AddSubgroup.mem_pi, Set.mem_univ, true_implies] at hx'
    have hsum : phi B n n' x = ∑ p, phi B n n' x p • (Pi.single p 1 : Ix D n n' → ℂ) := by
      funext q
      simp [Finset.sum_apply, Pi.single_apply]
    have hsing : ∀ p, (phi B n n').symm (Pi.single p 1) =
        TaylorLogMetric.embV D (TaylorLogMetric.tor0 D cc δ) (bas B n n' ((ixE D n n').symm p)) := by
      intro p
      rw [LinearEquiv.symm_apply_eq, phi_embV_bas, Equiv.apply_symm_apply]
    have hxe : x = ∑ p, phi B n n' x p • TaylorLogMetric.embV D (TaylorLogMetric.tor0 D cc δ) (bas B n n' ((ixE D n n').symm p)) := by
      conv_lhs => rw [← (phi B n n').symm_apply_apply x, hsum]
      rw [map_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [map_smul, hsing]
    rw [hxe]
    refine AddSubgroup.sum_mem _ fun p _ => AddSubgroup.subset_closure ?_
    refine ⟨phi B n n' x p, ?_, (ixE D n n').symm p, rfl⟩
    have := hx' p
    rw [B.lat] at this
    exact this

end GlobalTheory.BaseVacuum
