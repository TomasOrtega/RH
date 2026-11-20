import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Cint
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NoLeak
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFamilyTraceVolumeConstStatement

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.RefVol

/- English proof (translation)
Rewrite using `[← AddSubgroup.inf_relIndex_right (P ⊓ A) K, ← AddSubgroup.inf_relIndex_right A K]`. Use `congr 1`. Use extensionality with `x`. Simplify using `only [AddSubgroup.mem_inf]`. Conclude with `⟨fun hx => ⟨hx.1.2, hx.2⟩, fun hx => ⟨⟨h hx.2, hx.1⟩, hx.2⟩⟩`.
-/
theorem relIndex_inf_of_le {G : Type*} [AddGroup G] (P A K : AddSubgroup G) (h : K ≤ P) :
    (P ⊓ A).relIndex K = A.relIndex K := by
  rw [← AddSubgroup.inf_relIndex_right (P ⊓ A) K, ← AddSubgroup.inf_relIndex_right A K]
  congr 1
  ext x
  simp only [AddSubgroup.mem_inf]
  exact ⟨fun hx => ⟨hx.1.2, hx.2⟩, fun hx => ⟨⟨h hx.2, hx.1⟩, hx.2⟩⟩

/- English proof (translation)
Unfold `AddSubgroup.relIndex`. Rewrite using `[← AddSubgroup.index_prod, ← AddSubgroup.index_comap_of_surjective _ (f := (AddSubgroup.prodEquiv A' B').toAddMonoidHom) (AddSubgroup.prodEquiv A' B').surjective]`. Use `congr 1`.
-/
theorem relIndex_prod {G H : Type*} [AddGroup G] [AddGroup H] (A A' : AddSubgroup G)
    (B B' : AddSubgroup H) :
    (A.prod B).relIndex (A'.prod B') = A.relIndex A' * B.relIndex B' := by
  unfold AddSubgroup.relIndex
  rw [← AddSubgroup.index_prod,
    ← AddSubgroup.index_comap_of_surjective _ (f := (AddSubgroup.prodEquiv A' B').toAddMonoidHom)
      (AddSubgroup.prodEquiv A' B').surjective]
  congr 1

/- English proof (translation)
Rewrite using `[relIndex_inf_of_le _ _ _ inf_le_left, AddSubgroup.relIndex_comap, inf_comm A, relIndex_inf_of_le _ _ _ inf_le_right]`. Use `congr 1`. Use extensionality with `y`. Simplify using `only [AddSubgroup.mem_map, AddSubgroup.mem_inf, AddSubgroup.mem_comap]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨x, ⟨h1, h2⟩, rfl⟩`. Conclude with `⟨h2, x, h1, rfl⟩`. Introduce and unpack `⟨h2, x, h1, rfl⟩`. Conclude with `⟨x, ⟨h1, h2⟩, rfl⟩`.
-/
theorem relIndex_inf_comap {G H : Type*} [AddGroup G] [AddGroup H] (φ : G →+ H) (P : AddSubgroup G)
    (A B : AddSubgroup H) :
    (P ⊓ A.comap φ).relIndex (P ⊓ B.comap φ) = (A ⊓ P.map φ).relIndex (B ⊓ P.map φ) := by
  rw [relIndex_inf_of_le _ _ _ inf_le_left, AddSubgroup.relIndex_comap, inf_comm A,
    relIndex_inf_of_le _ _ _ inf_le_right]
  congr 1
  ext y
  simp only [AddSubgroup.mem_map, AddSubgroup.mem_inf, AddSubgroup.mem_comap]
  constructor
  · rintro ⟨x, ⟨h1, h2⟩, rfl⟩
    exact ⟨h2, x, h1, rfl⟩
  · rintro ⟨h2, x, h1, rfl⟩
    exact ⟨x, ⟨h1, h2⟩, rfl⟩

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

/- English proof (translation)
Unfold `Frames.th`. Use `split_ifs`. Conclude with `fun h => S.ϖ_irr.ne_zero (Subtype.ext h)`. Conclude with `one_ne_zero`.
-/
theorem th_ne : S.th ≠ 0 := by
  unfold Frames.th
  split_ifs
  · exact fun h => S.ϖ_irr.ne_zero (Subtype.ext h)
  · exact one_ne_zero

noncomputable def sumDiv : S.V × S.V →+ S.V :=
  (algebraMap F E S.th⁻¹ • (LinearMap.id : S.V →ₗ[E] S.V)).toAddMonoidHom.comp
    (AddMonoidHom.fst S.V S.V + AddMonoidHom.snd S.V S.V)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sumDiv_apply (p : S.V × S.V) : sumDiv S p = algebraMap F E S.th⁻¹ • (p.1 + p.2) := rfl

/- English proof (translation)
Rewrite using `[← map_mul, mul_inv_cancel₀ (th_ne S), map_one]`.
-/
theorem th_mul : algebraMap F E S.th * algebraMap F E S.th⁻¹ = 1 := by
  rw [← map_mul, mul_inv_cancel₀ (th_ne S), map_one]

/- English proof (translation)
Unfold `Frames.refB`. Use `congr 1`. Use extensionality with `p`. Simplify using `only [AddSubgroup.mem_comap, AddSubgroup.mem_map, sumDiv_apply]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, hy, h⟩`. Establish `h' : algebraMap F E S.th • y = p.1 + p.2` using `h`. Rewrite using `[← h', smul_smul, mul_comm (algebraMap F E S.th⁻¹), th_mul, one_smul]`. Conclude with `hy`. Introduce `h`.

Use `⟨_, h, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `algebraMap F E S.th • (algebraMap F E S.th⁻¹ • (p.1 + p.2)) = p.1 + p.2`. Rewrite using `[smul_smul, th_mul, one_smul]`.
-/
theorem refB_eq (J : ℕ) (Λ : Submodule L.O S.V) :
    S.refB J Λ = ((S.spanTo S.f J).toAddSubgroup.prod (S.spanTo S.f' J).toAddSubgroup) ⊓
      Λ.toAddSubgroup.comap (sumDiv S) := by
  unfold Frames.refB
  congr 1
  ext p
  simp only [AddSubgroup.mem_comap, AddSubgroup.mem_map, sumDiv_apply]
  constructor
  · rintro ⟨y, hy, h⟩
    have h' : algebraMap F E S.th • y = p.1 + p.2 := h
    rw [← h', smul_smul, mul_comm (algebraMap F E S.th⁻¹), th_mul, one_smul]
    exact hy
  · intro h
    refine ⟨_, h, ?_⟩
    change algebraMap F E S.th • (algebraMap F E S.th⁻¹ • (p.1 + p.2)) = p.1 + p.2
    rw [smul_smul, th_mul, one_smul]

/- English proof (translation)
Use extensionality with `y`. Simplify using `only [AddSubgroup.mem_map, AddSubgroup.mem_prod, Submodule.mem_toAddSubgroup, sumDiv_apply]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨p, ⟨h1, h2⟩, rfl⟩`. Conclude with `Submodule.smul_mem _ _ (Submodule.add_mem_sup h1 h2)`.

Introduce `h`. Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.1 h`. Use `⟨(algebraMap F E S.th • a, algebraMap F E S.th • b), ⟨X.smul_mem _ ha, X'.smul_mem _ hb⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← smul_add, smul_smul, mul_comm (algebraMap F E S.th⁻¹), th_mul, one_smul]`.
-/
theorem map_sumDiv (X X' : Submodule E S.V) :
    (X.toAddSubgroup.prod X'.toAddSubgroup).map (sumDiv S) = (X ⊔ X').toAddSubgroup := by
  ext y
  simp only [AddSubgroup.mem_map, AddSubgroup.mem_prod, Submodule.mem_toAddSubgroup, sumDiv_apply]
  constructor
  · rintro ⟨p, ⟨h1, h2⟩, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.add_mem_sup h1 h2)
  · intro h
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 h
    refine ⟨(algebraMap F E S.th • a, algebraMap F E S.th • b),
      ⟨X.smul_mem _ ha, X'.smul_mem _ hb⟩, ?_⟩
    rw [← smul_add, smul_smul, mul_comm (algebraMap F E S.th⁻¹), th_mul, one_smul]

/- English proof (translation)
Rewrite using `[refB_eq, refB_eq, relIndex_inf_comap, map_sumDiv]`. Both sides reduce to the same expression.
-/
theorem refB_relIndex (J : ℕ) (Λ Λ' : Submodule L.O S.V) :
    (S.refB J Λ).relIndex (S.refB J Λ') =
      (Λ ⊓ (S.spanTo S.f J ⊔ S.spanTo S.f' J).restrictScalars L.O).toAddSubgroup.relIndex
        (Λ' ⊓ (S.spanTo S.f J ⊔ S.spanTo S.f' J).restrictScalars L.O).toAddSubgroup := by
  rw [refB_eq, refB_eq, relIndex_inf_comap, map_sumDiv]
  rfl

/- English proof (translation)
Unfold `Frames.refA`. Rewrite using `[relIndex_prod, relIndex_prod, AddSubgroup.relIndex_self, mul_one, refB_relIndex]`. Both sides reduce to the same expression.
-/
theorem refA_relIndex (J : ℕ) (Λ Λ' : Submodule L.O S.V) :
    (S.refA J Λ).relIndex (S.refA J Λ') =
      (Λ ⊓ (S.spanTo S.f J ⊔ S.spanTo S.f' J).restrictScalars L.O).toAddSubgroup.relIndex
        (Λ' ⊓ (S.spanTo S.f J ⊔ S.spanTo S.f' J).restrictScalars L.O).toAddSubgroup *
      (Λ ⊓ (perp L S.Hm (S.spanTo S.f J ⊔ S.spanTo S.f' J)).restrictScalars L.O).toAddSubgroup.relIndex
        (Λ' ⊓ (perp L S.Hm (S.spanTo S.f J ⊔ S.spanTo S.f' J)).restrictScalars L.O).toAddSubgroup := by
  unfold Frames.refA
  rw [relIndex_prod, relIndex_prod, AddSubgroup.relIndex_self, mul_one, refB_relIndex]
  rfl

end GlobalTheory.RefVol

/- English proof (translation)
Introduce `F _ _ _ _ _ E _ _ _ L r k S j β βJ d Λ h1 h2 Λ' h3 h4`. Establish `a` using `GlobalTheory.T.hermitianFamily_trace_volume_const L r k S j β βJ d Λ h1 h2 Λ' h3 h4 _ (Or.inl rfl)`. Establish `b` using `GlobalTheory.T.hermitianFamily_trace_volume_const L r k S j β βJ d Λ h1 h2 Λ' h3 h4 _ (Or.inr rfl)`. Rewrite using `[GlobalTheory.RefVol.refA_relIndex, GlobalTheory.RefVol.refA_relIndex]`. Conclude with `⟨by rw [a.1, b.1], mul_ne_zero a.2.1 b.2.1⟩`.
-/
theorem GlobalTheory.RefVol.main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ Λ', S.IsTerm d Λ' → S.InFF β (j + 1) βJ d Λ' → (S.refA (j + 1) Λ).relIndex (S.refA (j + 1) Λ') = (S.refA (j + 1) Λ').relIndex (S.refA (j + 1) Λ) ∧ (S.refA (j + 1) Λ).relIndex (S.refA (j + 1) Λ') ≠ 0 := by
  intro F _ _ _ _ _ E _ _ _ L r k S j β βJ d Λ h1 h2 Λ' h3 h4
  have a := GlobalTheory.T.hermitianFamily_trace_volume_const L r k S j β βJ d Λ h1 h2 Λ' h3 h4 _ (Or.inl rfl)
  have b := GlobalTheory.T.hermitianFamily_trace_volume_const L r k S j β βJ d Λ h1 h2 Λ' h3 h4 _ (Or.inr rfl)
  rw [GlobalTheory.RefVol.refA_relIndex, GlobalTheory.RefVol.refA_relIndex]
  exact ⟨by rw [a.1, b.1], mul_ne_zero a.2.1 b.2.1⟩
