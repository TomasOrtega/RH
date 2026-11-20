import Formalism.LocalToGlobal.GlobalTheory.GL4.LowerSlopeInequalityFamily

open Module NumberField

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions.flipTwoThree

section Fun

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {u : D.what₂.Word} (CV : ColVal D u)

/- English proof (translation)
Use `conv_lhs => rw [← (D.sp.X 0).frame.sum_repr z]`. Rewrite using `[map_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => CV.bc_smul c τ _ _`.
-/
theorem bc_sum_repr (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) (z : (D.sp.X 0).V) :
    CV.bc c τ z = ∑ i, CV.rho τ ((D.sp.X 0).frame.repr z i) • CV.bc c τ ((D.sp.X 0).frame i) := by
  conv_lhs => rw [← (D.sp.X 0).frame.sum_repr z]
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => CV.bc_smul c τ _ _

/- English proof (translation)
Rewrite using `[← (CV.Q_good c τ).2.2]`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce `x hx`. Establish `hx' : x ∈ (Submodule.span D.what₂.LL (Set.range fun i => CV.bc c τ ((D.sp.X 0).frame i))).restrictScalars (𝓞 D.what₂.LL)`. Rewrite `hx` using `[CV.bc_L c τ]`.

Use `(Submodule.span_le.2 ?_) hx` and prove the remaining obligations. Introduce and unpack `_ ⟨z, -, rfl⟩`. Rewrite using `[SetLike.mem_coe, Submodule.restrictScalars_mem, bc_sum_repr CV c τ z]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))`. Conclude with `hx'`.
-/
theorem span_bc_frame (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) :
    ⊤ ≤ Submodule.span D.what₂.LL (Set.range fun i => CV.bc c τ ((D.sp.X 0).frame i)) := by
  rw [← (CV.Q_good c τ).2.2]
  refine Submodule.span_le.2 ?_
  intro x hx
  have hx' : x ∈ (Submodule.span D.what₂.LL (Set.range fun i => CV.bc c τ ((D.sp.X 0).frame i))).restrictScalars (𝓞 D.what₂.LL) := by
    rw [CV.bc_L c τ] at hx
    refine (Submodule.span_le.2 ?_) hx
    rintro _ ⟨z, -, rfl⟩
    rw [SetLike.mem_coe, Submodule.restrictScalars_mem, bc_sum_repr CV c τ z]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  exact hx'

/- English proof (translation)
Rewrite using `[Fintype.card_fin, finrank_eq_card_basis (CV.Q c τ).b, Fintype.card_congr (CV.eQ c τ), Fintype.card_fin, D.sp.rank0, Ranks.N_zero]`.
-/
theorem card_frame_eq (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) :
    Fintype.card (Fin (D.sp.X 0).rank) = finrank D.what₂.LL (CV.Q c τ).V := by
  rw [Fintype.card_fin, finrank_eq_card_basis (CV.Q c τ).b, Fintype.card_congr (CV.eQ c τ), Fintype.card_fin, D.sp.rank0, Ranks.N_zero]

def bcBasis (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) : Basis (Fin (D.sp.X 0).rank) D.what₂.LL (CV.Q c τ).V :=
  basisOfTopLeSpanOfCardEqFinrank (fun i => CV.bc c τ ((D.sp.X 0).frame i)) (span_bc_frame CV c τ) (card_frame_eq CV c τ)

/- English proof (translation)
Unfold `bcBasis`. Rewrite using `[coe_basisOfTopLeSpanOfCardEqFinrank]`.
-/
theorem bcBasis_apply (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) (i : Fin (D.sp.X 0).rank) :
    bcBasis CV c τ i = CV.bc c τ ((D.sp.X 0).frame i) := by
  unfold bcBasis
  rw [coe_basisOfTopLeSpanOfCardEqFinrank]

def bcFun (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) (y : (D.sp.X 0).V) : (CV.Q c τ).V →ₗ[D.what₂.LL] D.what₂.LL :=
  (bcBasis CV c τ).constr D.what₂.LL fun i => CV.rho τ ((D.sp.X 0).hT y ((D.sp.X 0).frame i))

/- English proof (translation)
Rewrite using `[bc_sum_repr CV c τ z, map_sum]`. Repeatedly rewrite using `[map_smul]`. Establish `h1 : ∀ i, bcFun CV c τ y (CV.bc c τ ((D.sp.X 0).frame i)) = CV.rho τ ((D.sp.X 0).hT y ((D.sp.X 0).frame i))` using `fun i => by`. Unfold `bcFun`. Rewrite using `[← bcBasis_apply CV c τ i, Basis.constr_basis]`.

Repeatedly rewrite using `[h1, smul_eq_mul, ← map_mul]`. Rewrite using `[← map_sum]`. Use `congr 1`. Use `conv_rhs => rw [← (D.sp.X 0).frame.sum_repr z]`. Rewrite using `[map_sum]`.

Conclude with `Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]`.
-/
theorem bcFun_bc (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) (y z : (D.sp.X 0).V) :
    bcFun CV c τ y (CV.bc c τ z) = CV.rho τ ((D.sp.X 0).hT y z) := by
  rw [bc_sum_repr CV c τ z, map_sum]
  simp_rw [map_smul]
  have h1 : ∀ i, bcFun CV c τ y (CV.bc c τ ((D.sp.X 0).frame i)) = CV.rho τ ((D.sp.X 0).hT y ((D.sp.X 0).frame i)) := fun i => by
    unfold bcFun
    rw [← bcBasis_apply CV c τ i, Basis.constr_basis]
  simp_rw [h1, smul_eq_mul, ← map_mul]
  rw [← map_sum]
  congr 1
  conv_rhs => rw [← (D.sp.X 0).frame.sum_repr z]
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]

/- English proof (translation)
Rewrite `hx` using `[CV.bc_L c τ]`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨z, hz, rfl⟩` from `hx`. Rewrite using `[bcFun_bc]`.

Take `⟨o, ho⟩` from `hy z hz`. Establish `e : (D.sp.X 0).hT y z = starRingEnd D.host.E ((D.sp.X 0).hT z y)` using `((D.sp.X 0).herm.eq z y).symm`. Rewrite using `[e, ← ho]`. Conclude with `((o.isIntegral_coe.map (starRingEnd D.host.E).toIntAlgHom).map (CV.rho τ).toIntAlgHom)`. Consider the case `zero => rw [map_zero]`.

Conclude with `isIntegral_zero`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `hx.add hy`. Consider the case `smul a x _ hx`. Rewrite using `[← algebraMap_smul D.what₂.LL a x, map_smul, smul_eq_mul]`.

Conclude with `a.isIntegral_coe.mul hx`.
-/
theorem bcFun_int (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) {y : (D.sp.X 0).V}
    (hy : y ∈ dualSub (D.sp.X 0) (D.clsLat u 0 c)) {x : (CV.Q c τ).V} (hx : x ∈ (CV.Q c τ).L) :
    IsIntegral ℤ (bcFun CV c τ y x) := by
  rw [CV.bc_L c τ] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z, hz, rfl⟩ := hx
    rw [bcFun_bc]
    obtain ⟨o, ho⟩ := hy z hz
    have e : (D.sp.X 0).hT y z = starRingEnd D.host.E ((D.sp.X 0).hT z y) := ((D.sp.X 0).herm.eq z y).symm
    rw [e, ← ho]
    exact ((o.isIntegral_coe.map (starRingEnd D.host.E).toIntAlgHom).map (CV.rho τ).toIntAlgHom)
  | zero => rw [map_zero]; exact isIntegral_zero
  | add x y _ _ hx hy => rw [map_add]; exact hx.add hy
  | smul a x _ hx =>
    rw [← algebraMap_smul D.what₂.LL a x, map_smul, smul_eq_mul]
    exact a.isIntegral_coe.mul hx

end Fun

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
