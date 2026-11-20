import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial TensorProduct Module GlobalTheory.Pst

namespace GlobalTheory.Pst

/- English proof (translation)
Establish `h : Function.Exact (CAlgHom : P.R.B →ₐ[ℚ_[l]] Bst P).toLinearMap (monSt P)` using `fun p => (monSt_eq_zero_iff P p).trans ⟨fun ⟨b, hb⟩ => ⟨b, hb.symm⟩, fun ⟨b, hb⟩ => ⟨b, hb.symm⟩⟩`. Conclude with `Module.Flat.lTensor_exact V h x`.
-/
theorem monV_eq_zero_iff_mem_range_crisIncl {l : ℕ} [Fact l.Prime] (P : LocPrime l)
    (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
    (V : Type) [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    (x : V ⊗[ℚ_[l]] Bst P) : monV P LL V x = 0 ↔ ∃ y, crisIncl P LL V y = x := by
  have h : Function.Exact (CAlgHom : P.R.B →ₐ[ℚ_[l]] Bst P).toLinearMap (monSt P) := fun p =>
    (monSt_eq_zero_iff P p).trans ⟨fun ⟨b, hb⟩ => ⟨b, hb.symm⟩, fun ⟨b, hb⟩ => ⟨b, hb.symm⟩⟩
  exact Module.Flat.lTensor_exact V h x

/- English proof (translation)
Introduce `l _ P K LL V _ _ _ _ ρ x`. Establish `key : ∀ y, crisIncl P ↥LL.1 V y ∈ Dst P ρ ↔ y ∈ Dcris (P.PD K) ρ` using `fun y => by`. Rewrite using `[mem_Dst, Dcris, Submodule.mem_iInf]`. Use `forall_congr' fun g => ?_` and prove the remaining obligations. Rewrite using `[stRep_crisIncl, (crisIncl_injective P).eq_iff, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]`.

Rewrite using `[monV_eq_zero_iff_mem_range_crisIncl, Submodule.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hx, y, rfl⟩`. Conclude with `⟨y, (key y).mp hx, rfl⟩`. Introduce and unpack `⟨y, hy, rfl⟩`.

Conclude with `⟨(key y).mpr hy, y, rfl⟩`.
-/
theorem mem_Dst_and_monV_eq_zero_iff : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (x : V ⊗[ℚ_[l]] Bst P), (x ∈ Dst P ρ ∧ monV P ↥LL.1 V x = 0) ↔ x ∈ (Dcris (P.PD K) ρ).map (crisIncl P ↥LL.1 V) := by
  intro l _ P K LL V _ _ _ _ ρ x
  have key : ∀ y, crisIncl P ↥LL.1 V y ∈ Dst P ρ ↔ y ∈ Dcris (P.PD K) ρ := fun y => by
    rw [mem_Dst, Dcris, Submodule.mem_iInf]
    refine forall_congr' fun g => ?_
    rw [stRep_crisIncl, (crisIncl_injective P).eq_iff, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero]
  rw [monV_eq_zero_iff_mem_range_crisIncl, Submodule.mem_map]
  constructor
  · rintro ⟨hx, y, rfl⟩
    exact ⟨y, (key y).mp hx, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨(key y).mpr hy, y, rfl⟩

end GlobalTheory.Pst
