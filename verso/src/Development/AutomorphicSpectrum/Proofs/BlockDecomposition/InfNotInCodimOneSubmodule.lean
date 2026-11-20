import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.RgGuCore

/- English proof (translation)
Take `⟨a, haA, haT⟩` from `SetLike.not_le_iff_exists.mp hA`. Take `⟨c, hcC, hcT⟩` from `SetLike.not_le_iff_exists.mp hC`. Take `⟨v₀, hv₀⟩` from `rank_le_one_iff.mp hT`. Take `⟨s, hs⟩` from `hv₀ (Submodule.Quotient.mk a)`. Take `⟨t, ht⟩` from `hv₀ (Submodule.Quotient.mk c)`.

Establish `hs0 : s ≠ 0`. Introduce and unpack `rfl`. Apply `haT` to reduce the goal to its premises. Rewrite using `[← Submodule.Quotient.mk_eq_zero T, ← hs, zero_smul]`. Establish `hdiff : c - (t * s⁻¹) • a ∈ T`.

Rewrite using `[← Submodule.Quotient.mk_eq_zero T, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, ← hs, ← ht, smul_smul, mul_assoc, inv_mul_cancel₀ hs0, mul_one, sub_self]`. Establish `hsum : c - (t * s⁻¹) • a ∈ A ⊔ C` using `Submodule.sub_mem _ (Submodule.mem_sup_right hcC) (Submodule.mem_sup_left (Submodule.smul_mem _ _ haA))`. Take `⟨x, hx, y, hy, hxy⟩` from `Submodule.mem_sup.mp (hmod (Submodule.mem_inf.mpr ⟨hsum, hdiff⟩))`. Rewrite `hx`, `hy` using `[Submodule.mem_inf]`. Establish `hw : c - y = (t * s⁻¹) • a + x`.

Combine the equalities or inequalities in the displayed calculation. Establish `hwA : c - y ∈ A` using `hw ▸ Submodule.add_mem _ (Submodule.smul_mem _ _ haA) hx.1`. Establish `hwC : c - y ∈ C` using `Submodule.sub_mem _ hcC hy.1`. Introduce `h`. Apply `hcT` to reduce the goal to its premises.

Establish `hwT : c - y ∈ T` using `h (Submodule.mem_inf.mpr ⟨hwA, hwC⟩)`. Simplify using `using Submodule.add_mem _ hwT hy.2`.
-/
theorem not_inf_le_of_rank_quotient_le_one {V : Type} [AddCommGroup V] [Module ℂ V]
    (T A C : Submodule ℂ V) (hT : Module.rank ℂ (V ⧸ T) ≤ 1)
    (hmod : (A ⊔ C) ⊓ T ≤ A ⊓ T ⊔ C ⊓ T) (hA : ¬ A ≤ T) (hC : ¬ C ≤ T) :
    ¬ A ⊓ C ≤ T := by
  obtain ⟨a, haA, haT⟩ := SetLike.not_le_iff_exists.mp hA
  obtain ⟨c, hcC, hcT⟩ := SetLike.not_le_iff_exists.mp hC
  obtain ⟨v₀, hv₀⟩ := rank_le_one_iff.mp hT
  obtain ⟨s, hs⟩ := hv₀ (Submodule.Quotient.mk a)
  obtain ⟨t, ht⟩ := hv₀ (Submodule.Quotient.mk c)
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply haT
    rw [← Submodule.Quotient.mk_eq_zero T, ← hs, zero_smul]
  have hdiff : c - (t * s⁻¹) • a ∈ T := by
    rw [← Submodule.Quotient.mk_eq_zero T, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul,
      ← hs, ← ht, smul_smul, mul_assoc, inv_mul_cancel₀ hs0, mul_one, sub_self]
  have hsum : c - (t * s⁻¹) • a ∈ A ⊔ C :=
    Submodule.sub_mem _ (Submodule.mem_sup_right hcC)
      (Submodule.mem_sup_left (Submodule.smul_mem _ _ haA))
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp (hmod (Submodule.mem_inf.mpr ⟨hsum, hdiff⟩))
  rw [Submodule.mem_inf] at hx hy
  have hw : c - y = (t * s⁻¹) • a + x := by
    calc c - y = (c - (t * s⁻¹) • a - (x + y)) + (t * s⁻¹) • a + x := by abel
      _ = (t * s⁻¹) • a + x := by rw [hxy, sub_self, zero_add]
  have hwA : c - y ∈ A := hw ▸ Submodule.add_mem _ (Submodule.smul_mem _ _ haA) hx.1
  have hwC : c - y ∈ C := Submodule.sub_mem _ hcC hy.1
  intro h
  apply hcT
  have hwT : c - y ∈ T := h (Submodule.mem_inf.mpr ⟨hwA, hwC⟩)
  simpa using Submodule.add_mem _ hwT hy.2

/- English proof (translation)
Rewrite `hmod` using `[Subrepresentation.toSubmodule_sup]`. Rewrite using `[Subrepresentation.toSubmodule_inf]`. Conclude with `GlobalTheory.CompanionTheory.RgGuCore.not_inf_le_of_rank_quotient_le_one T A.toSubmodule C.toSubmodule hT hmod hA hC`.
-/
theorem gen_core_meet {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (T : Submodule ℂ V) (hT : Module.rank ℂ (V ⧸ T) ≤ 1)
    (A C : Subrepresentation ρ)
    (hmod : (A ⊔ C).toSubmodule ⊓ T ≤ A.toSubmodule ⊓ T ⊔ C.toSubmodule ⊓ T)
    (hA : ¬ A.toSubmodule ≤ T) (hC : ¬ C.toSubmodule ≤ T) :
    ¬ (A ⊓ C).toSubmodule ≤ T := by
  rw [Subrepresentation.toSubmodule_sup] at hmod
  rw [Subrepresentation.toSubmodule_inf]
  exact GlobalTheory.CompanionTheory.RgGuCore.not_inf_le_of_rank_quotient_le_one T A.toSubmodule C.toSubmodule hT hmod hA hC

end GlobalTheory.CompanionTheory.RgGuCore
