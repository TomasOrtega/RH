import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumRepSubgroupEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOfValILeOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonJacquetOfPerm

open MeasureTheory ValuativeRel GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic

noncomputable section

namespace GlobalTheory.RadRedLift

/- English proof (translation)
Use `choose A hA using fun i j => IsLocalRing.residue_surjective (R := 𝒪[k]) ((v : Matrix n n 𝓀[k]) i j)`. Set `B : Matrix n n 𝒪[k]` to `Matrix.of fun i j => if blk e i < blk e j then A i j else (1 : Matrix n n 𝒪[k]) i j`. Establish `h1 : (IsLocalRing.residue 𝒪[k]).mapMatrix B = v`. Use extensionality with `i j`. Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply, B, Matrix.of_apply]`.

Use `split_ifs with hij`. Conclude with `hA i j`. Rewrite using `[CuspMax.mem_unipRad_iff_entries.1 hv i j hij]`. Simplify using `only [Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.

Establish `hd : IsUnit B.det`. Rewrite using `[← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, h1]`. Conclude with `(Matrix.GeneralLinearGroup.det v).ne_zero`. Take `⟨u, hu⟩` from `(Matrix.isUnit_iff_isUnit_det _).2 hd`. Use `⟨GlobalTheory.LocGL.toKO k n u, CuspMax.mem_unipRad_iff_entries.2 fun i j hij => ?_, Units.ext ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `algebraMap 𝒪[k] k ((u : Matrix n n 𝒪[k]) i j) = _`. Rewrite using `[hu]`. Simplify using `only [B, Matrix.of_apply, if_neg hij, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Simplify using `only [GlobalTheory.LocGL.redK, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]`.

Rewrite using `[← h1, ← hu]`. Both sides reduce to the same expression.
-/
theorem exists_lift_unipRad (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
    [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) (v : GL n 𝓀[k]) (hv : v ∈ unipRad 𝓀[k] e) :
    ∃ w : KO k n, (w : GL n k) ∈ unipRad k e ∧ GlobalTheory.LocGL.redK k n w = v := by
  classical
  choose A hA using fun i j => IsLocalRing.residue_surjective (R := 𝒪[k]) ((v : Matrix n n 𝓀[k]) i j)
  let B : Matrix n n 𝒪[k] := Matrix.of fun i j => if blk e i < blk e j then A i j else (1 : Matrix n n 𝒪[k]) i j
  have h1 : (IsLocalRing.residue 𝒪[k]).mapMatrix B = v := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, B, Matrix.of_apply]
    split_ifs with hij
    · exact hA i j
    · rw [CuspMax.mem_unipRad_iff_entries.1 hv i j hij]
      simp only [Matrix.one_apply]
      split_ifs <;> simp
  have hd : IsUnit B.det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, h1]
    exact (Matrix.GeneralLinearGroup.det v).ne_zero
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hd
  refine ⟨GlobalTheory.LocGL.toKO k n u, CuspMax.mem_unipRad_iff_entries.2 fun i j hij => ?_, Units.ext ?_⟩
  · change algebraMap 𝒪[k] k ((u : Matrix n n 𝒪[k]) i j) = _
    rw [hu]
    simp only [B, Matrix.of_apply, if_neg hij, Matrix.one_apply]
    split_ifs <;> simp
  · simp only [GlobalTheory.LocGL.redK, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    rw [← h1, ← hu]; rfl

/- English proof (translation)
Introduce `k _ _ _ _ r a b h g₀`. Take `⟨k₀, p, hp, rfl⟩` from `GlobalTheory.ValIwasawa.iwasawa 𝒪[k] k r g₀`. Set `κ : KO k (Fin r)` to `⟨Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) k₀, k₀, rfl⟩`. Establish `hpP : p ∈ stdMaxParab k h` using `(mem_stdMaxParab h).2 fun i j hj hi => hp (show j < i from by`. Rewrite using `[Fin.lt_def]`.

Use the proof step `omega)`. Use `⟨GlobalTheory.LocGL.redK k (Fin r) κ, fun v hv => ?_⟩` and prove the remaining obligations. Take `⟨w, hw, rfl⟩` from `exists_lift_unipRad k _ v hv`. Use `⟨(κ * w * κ⁻¹ : KO k (Fin r)), (κ * w * κ⁻¹).2, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_conjBy]`.

Establish `hn` using `parab_le_normalizer k _ (inv_mem hpP)`. Use `(Subgroup.mem_normalizer_iff.1 hn (w : GL (Fin r) k)).1 hw` as an intermediate fact. Establish `e : ((Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) k₀ : GL (Fin r) k) * p)⁻¹ * ((κ * w * κ⁻¹ : KO k (Fin r)) : GL (Fin r) k) * (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) k₀ * p) = p⁻¹ * w * p⁻¹⁻¹`. Express the relevant statement in the definitionally equal form `((κ : GL (Fin r) k) * p)⁻¹ * ((κ : GL (Fin r) k) * w * (κ : GL (Fin r) k)⁻¹) * ((κ : GL (Fin r) k) * p) = _`. Use `group`.

Rewrite using `[e]`. Conclude with `this`. Rewrite using `[← map_inv, ← map_mul, ← map_mul]`.
-/
theorem red_lift : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {r a b : ℕ} (h : a + b = r) (g₀ : GL (Fin r) k), ∃ c : GL (Fin r) 𝓀[k], ∀ v ∈ stdMaxRad 𝓀[k] h,
    ∃ (u : GL (Fin r) k) (hu : u ∈ KO k (Fin r)), u ∈ conjBy g₀ (stdMaxRad k h) ∧
      GlobalTheory.LocGL.redK k (Fin r) ⟨u, hu⟩ = c * v * c⁻¹ := by
  intro k _ _ _ _ r a b h g₀
  obtain ⟨k₀, p, hp, rfl⟩ := GlobalTheory.ValIwasawa.iwasawa 𝒪[k] k r g₀
  let κ : KO k (Fin r) := ⟨Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) k₀, k₀, rfl⟩
  have hpP : p ∈ stdMaxParab k h := (mem_stdMaxParab h).2 fun i j hj hi => hp (show j < i from by
    rw [Fin.lt_def]; omega)
  refine ⟨GlobalTheory.LocGL.redK k (Fin r) κ, fun v hv => ?_⟩
  obtain ⟨w, hw, rfl⟩ := exists_lift_unipRad k _ v hv
  refine ⟨(κ * w * κ⁻¹ : KO k (Fin r)), (κ * w * κ⁻¹).2, ?_, ?_⟩
  · rw [mem_conjBy]
    have hn := parab_le_normalizer k _ (inv_mem hpP)
    have := (Subgroup.mem_normalizer_iff.1 hn (w : GL (Fin r) k)).1 hw
    have e : ((Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) k₀ : GL (Fin r) k) * p)⁻¹ *
        ((κ * w * κ⁻¹ : KO k (Fin r)) : GL (Fin r) k) * (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) k₀ * p) =
        p⁻¹ * w * p⁻¹⁻¹ := by
      change ((κ : GL (Fin r) k) * p)⁻¹ * ((κ : GL (Fin r) k) * w * (κ : GL (Fin r) k)⁻¹) * ((κ : GL (Fin r) k) * p) = _
      group
    rw [e]
    exact this
  · rw [← map_inv, ← map_mul, ← map_mul]

end GlobalTheory.RadRedLift
