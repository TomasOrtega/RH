import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DensGSO

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open Formalism.MainNotions.S ValuativeRel

/- English proof (translation)
Establish `: S.IsLattice F` using `⟨hfg, hsp⟩`. Establish `hr : Module.finrank 𝒪[F] S = n`. Simplify using `using Submodule.IsLattice.finrank_of_pi F S`. Set `b0 : Module.Basis (Fin n) 𝒪[F] S` to `Module.finBasisOfFinrankEq 𝒪[F] S hr`. Set `b` to `b0.extendOfIsLattice F`.

Establish `hb : ∀ k, b k = (b0 k : Fin n → F)` using `fun k => by simp [b]`. Use `⟨b, fun k => by rw [hb]; exact (b0 k).2, fun v => ⟨fun hv k => ?_, fun h => ?_⟩⟩` and prove the remaining obligations. Establish `key : v = b.equivFun.symm (fun k => ((b0.repr ⟨v, hv⟩ k : 𝒪[F]) : F))`. Rewrite using `[Module.Basis.equivFun_symm_apply]`. Establish `h1 : ∑ i, ((b0.repr ⟨v, hv⟩ i • b0 i : S) : Fin n → F) = v`.

Rewrite using `[← Submodule.coe_sum, b0.sum_repr]`. Use `conv_lhs => rw [← h1]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[hb, Submodule.coe_smul]`. Both sides reduce to the same expression.

Establish `h2` using `congrArg b.equivFun key`. Rewrite `h2` using `[LinearEquiv.apply_symm_apply, Module.Basis.equivFun_apply]`. Rewrite using `[h2]`. Conclude with `(b0.repr ⟨v, hv⟩ k).2`. Rewrite using `[← b.sum_repr v]`.

Use `Submodule.sum_mem _ fun k _ => ?_` and prove the remaining obligations. Use `S.smul_mem (⟨b.repr v k, h k⟩ : 𝒪[F]) (show b k ∈ S by rw [hb]; exact (b0 k).2)` as an intermediate fact. Conclude with `this`.
-/
theorem latBasis_exists (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ) (S : Submodule 𝒪[F] (Fin n → F))
    (hfg : S.FG) (hsp : Submodule.span F (S : Set (Fin n → F)) = ⊤) :
    ∃ b : Module.Basis (Fin n) F (Fin n → F), (∀ k, b k ∈ S) ∧
      ∀ v, v ∈ S ↔ ∀ k, b.repr v k ∈ 𝒪[F] := by
  have : S.IsLattice F := ⟨hfg, hsp⟩
  have hr : Module.finrank 𝒪[F] S = n := by
    simpa using Submodule.IsLattice.finrank_of_pi F S
  let b0 : Module.Basis (Fin n) 𝒪[F] S := Module.finBasisOfFinrankEq 𝒪[F] S hr
  let b := b0.extendOfIsLattice F
  have hb : ∀ k, b k = (b0 k : Fin n → F) := fun k => by simp [b]
  refine ⟨b, fun k => by rw [hb]; exact (b0 k).2, fun v => ⟨fun hv k => ?_, fun h => ?_⟩⟩
  · have key : v = b.equivFun.symm (fun k => ((b0.repr ⟨v, hv⟩ k : 𝒪[F]) : F)) := by
      rw [Module.Basis.equivFun_symm_apply]
      have h1 : ∑ i, ((b0.repr ⟨v, hv⟩ i • b0 i : S) : Fin n → F) = v := by
        rw [← Submodule.coe_sum, b0.sum_repr]
      conv_lhs => rw [← h1]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hb, Submodule.coe_smul]
      rfl
    have h2 := congrArg b.equivFun key
    rw [LinearEquiv.apply_symm_apply, Module.Basis.equivFun_apply] at h2
    rw [h2]
    exact (b0.repr ⟨v, hv⟩ k).2
  · rw [← b.sum_repr v]
    refine Submodule.sum_mem _ fun k _ => ?_
    have := S.smul_mem (⟨b.repr v k, h k⟩ : 𝒪[F]) (show b k ∈ S by rw [hb]; exact (b0 k).2)
    exact this

section Herm

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

end Herm

section Coord

variable {F : Type} [Field F] {E : Type} [CommRing E] [Algebra F E]
variable {V : Type} [AddCommGroup V] [Module E V]

def sig (e : E ≃ₐ[F] F × F) {n : ℕ} (β : Module.Basis (Fin n) E V) (x : V) : (Fin n → F) × (Fin n → F) :=
  (fun k => (e (β.repr x k)).1, fun k => (e (β.repr x k)).2)

def tau (e : E ≃ₐ[F] F × F) {n : ℕ} (β : Module.Basis (Fin n) E V) (p : (Fin n → F) × (Fin n → F)) : V :=
  ∑ k, e.symm (p.1 k, p.2 k) • β k

/- English proof (translation)
Unfold `sig tau`. Use `first`. Consider the case `simp only [Basis.repr_sum_self, AlgEquiv.apply_symm_apply]`. Consider the case `simp [map_sum, Finsupp.single_apply]`.
-/
theorem sig_tau (e : E ≃ₐ[F] F × F) {n : ℕ} (β : Module.Basis (Fin n) E V) (p : (Fin n → F) × (Fin n → F)) :
    sig e β (tau e β p) = p := by
  unfold sig tau
  first
  | simp only [Basis.repr_sum_self, AlgEquiv.apply_symm_apply]
  | simp [map_sum, Finsupp.single_apply]

/- English proof (translation)
Unfold `sig tau`. Simplify using `only [Prod.mk.eta, AlgEquiv.symm_apply_apply]`. Conclude with `β.sum_repr x`.
-/
theorem tau_sig (e : E ≃ₐ[F] F × F) {n : ℕ} (β : Module.Basis (Fin n) E V) (x : V) :
    tau e β (sig e β x) = x := by
  unfold sig tau
  simp only [Prod.mk.eta, AlgEquiv.symm_apply_apply]
  exact β.sum_repr x

/- English proof (translation)
Apply the tactic sequence `refine Prod.ext ?_ ?_ <;> funext k <;> simp [sig, map_add]`.
-/
theorem sig_add (e : E ≃ₐ[F] F × F) {n : ℕ} (β : Module.Basis (Fin n) E V) (x y : V) :
    sig e β (x + y) = sig e β x + sig e β y := by
  refine Prod.ext ?_ ?_ <;> funext k <;> simp [sig, map_add]

/- English proof (translation)
Apply the tactic sequence `refine Prod.ext ?_ ?_ <;> funext k <;> simp [sig, map_mul]`.
-/
theorem sig_smul (e : E ≃ₐ[F] F × F) {n : ℕ} (β : Module.Basis (Fin n) E V) (a : E) (x : V) :
    sig e β (a • x) = ((e a).1 • (sig e β x).1, (e a).2 • (sig e β x).2) := by
  refine Prod.ext ?_ ?_ <;> funext k <;> simp [sig, map_mul]

/- English proof (translation)
Unfold `tau`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl (fun k _ => ?_)` and prove the remaining obligations. Rewrite using `[← add_smul, ← map_add]`. Both sides reduce to the same expression.
-/
theorem tau_add (e : E ≃ₐ[F] F × F) {n : ℕ} (β : Module.Basis (Fin n) E V) (p q : (Fin n → F) × (Fin n → F)) :
    tau e β (p + q) = tau e β p + tau e β q := by
  unfold tau
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← add_smul, ← map_add]
  rfl

/- English proof (translation)
Unfold `tau`. Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_congr rfl (fun k _ => ?_)` and prove the remaining obligations. Rewrite using `[smul_smul]`. Use `congr 1`.

Establish `h1 : (((e a).1 • p.1) k, ((e a).2 • p.2) k) = e a * (p.1 k, p.2 k)` using `Prod.ext (by simp) (by simp)`. Rewrite using `[h1, map_mul, AlgEquiv.symm_apply_apply]`.
-/
theorem tau_smul (e : E ≃ₐ[F] F × F) {n : ℕ} (β : Module.Basis (Fin n) E V) (a : E)
    (p : (Fin n → F) × (Fin n → F)) :
    tau e β ((e a).1 • p.1, (e a).2 • p.2) = a • tau e β p := by
  unfold tau
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [smul_smul]
  congr 1
  have h1 : (((e a).1 • p.1) k, ((e a).2 • p.2) k) = e a * (p.1 k, p.2 k) :=
    Prod.ext (by simp) (by simp)
  rw [h1, map_mul, AlgEquiv.symm_apply_apply]

/- English proof (translation)
Apply the tactic sequence `refine Prod.ext ?_ ?_ <;> funext k <;> simp [sig]`.
-/
theorem sig_zero (e : E ≃ₐ[F] F × F) {n : ℕ} (β : Module.Basis (Fin n) E V) : sig e β 0 = 0 := by
  refine Prod.ext ?_ ?_ <;> funext k <;> simp [sig]

end Coord

end PI.UnitaryGroupMassFormula.CntFormula
