import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped TensorProduct

namespace GlobalTheory.FrameTransfer

open Formalism.L2.DIV Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem entry_mem {β β' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}
    (hβ : IsFrame β Λ) (hβ' : IsFrame β' Λ) (i j : Fin n) :
    ((β⁻¹ * β' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) i j ∈ Formalism.L2.Herm.intAf F E := by
  have key := (hβ (β'.1 *ᵥ Pi.single j 1)).1 ((hβ' _).2 (by
    intro k
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    by_cases h : k = j
    · subst h; simp only [Pi.single_eq_same]; exact Subring.one_mem _
    · rw [Pi.single_eq_of_ne h]; exact Subring.zero_mem _)) i
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, Matrix.mulVec_single_one] at key
  exact key

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem exists_int {β β' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}
    (hβ : IsFrame β Λ) (hβ' : IsFrame β' Λ) : ∃ y : GL (Fin n) (Formalism.L2.Herm.intAf F E), intGL F E n y = β⁻¹ * β' := by
  set φ := (Formalism.L2.Herm.intAf F E).subtype
  have hinj : Function.Injective (RingHom.mapMatrix (m := Fin n) φ) := fun a b h => by
    ext i j; exact congrArg Subtype.val (Subtype.ext (congrFun (congrFun h i) j))
  let M : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E) := fun i j => ⟨_, entry_mem hβ hβ' i j⟩
  let M' : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E) := fun i j => ⟨_, entry_mem hβ' hβ i j⟩
  have hM : RingHom.mapMatrix φ M = ((β⁻¹ * β' : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) := rfl
  have hM' : RingHom.mapMatrix φ M' = ((β'⁻¹ * β : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) := rfl
  have e1 : M * M' = 1 := hinj (by
    rw [map_mul, map_one, hM, hM', ← Units.val_mul]
    simp)
  have e2 : M' * M = 1 := hinj (by
    rw [map_mul, map_one, hM, hM', ← Units.val_mul]
    simp)
  exact ⟨⟨M, M', e1, e2⟩, Units.ext hM⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem st_le {β β' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}
    (hβ : IsFrame β Λ) (hβ' : IsFrame β' Λ) : St β' ≤ St β := by
  obtain ⟨y, hy⟩ := exists_int hβ hβ'
  rintro x ⟨z, rfl⟩
  refine ⟨y * z * y⁻¹, ?_⟩
  simp only [frGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv, hy]
  group

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem st_eq {β β' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}
    (hβ : IsFrame β Λ) (hβ' : IsFrame β' Λ) : St β = St β' :=
  le_antisymm (st_le hβ' hβ) (st_le hβ hβ')

section Lev

variable [StarRing E] {LL : Type} [CommRing LL]

/- English proof (translation)
Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components.

Reduce the conclusion to the remaining proof obligations.
-/
theorem mem_parLev_iff {hc : CMData F E} {J : Matrix (Fin n) (Fin n) E} {β β' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)}
    {D : LevDat E LL n} (hSt : St β = St β')
    (hg : ∀ PP ∈ D.Pg, ∀ x, redFn β PP x = redFn β' PP x) (hq : ∀ PP ∈ D.Q, ∀ x, redFn β PP x = redFn β' PP x)
    (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : x ∈ parLev hc J β D ↔ x ∈ parLev hc J β' D := by
  simp only [parLev, Subgroup.mem_inf, Subgroup.mem_iInf, mem_parah, hSt]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    refine ⟨⟨⟨h1, h2⟩, fun PP hP => ⟨(h3 PP hP).1, hg PP hP x ▸ (h3 PP hP).2⟩⟩, fun PP hP => ⟨(h4 PP hP).1, hq PP hP x ▸ (h4 PP hP).2⟩⟩
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    refine ⟨⟨⟨h1, h2⟩, fun PP hP => ⟨(h3 PP hP).1, (hg PP hP x).symm ▸ (h3 PP hP).2⟩⟩, fun PP hP => ⟨(h4 PP hP).1, (hq PP hP x).symm ▸ (h4 PP hP).2⟩⟩

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem rTup_eq {β β' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {D : LevDat E LL n}
    (hg : ∀ PP ∈ D.Pg, ∀ x, redFn β PP x = redFn β' PP x) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
    rTup β D x = rTup β' D x := by
  funext PP
  simp only [rTup, hg PP.1 PP.2 x]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mem_lev_iff {hc : CMData F E} {J : Matrix (Fin n) (Fin n) E} {β β' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)}
    {D : LevDat E LL n} (hSt : St β = St β')
    (hg : ∀ PP ∈ D.Pg, ∀ x, redFn β PP x = redFn β' PP x) (hq : ∀ PP ∈ D.Q, ∀ x, redFn β PP x = redFn β' PP x)
    (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : x ∈ lev hc J β D ↔ x ∈ lev hc J β' D := by
  show (x ∈ parLev hc J β D ∧ rTup β D x ∈ D.P.H) ↔ (x ∈ parLev hc J β' D ∧ rTup β' D x ∈ D.P.H)
  rw [mem_parLev_iff hSt hg hq, rTup_eq hg]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Reduce the equality to equality of the corresponding arguments. A detailed English derivation is pending.
-/
theorem levFn_eq {β β' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {D : LevDat E LL n}
    (hg : ∀ PP ∈ D.Pg, ∀ x, redFn β PP x = redFn β' PP x) (hq : ∀ PP ∈ D.Q, ∀ x, redFn β PP x = redFn β' PP x)
    (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : levFn β D x = levFn β' D x := by
  unfold levFn
  rw [rTup_eq hg]
  congr 1
  · congr 1
    exact Finset.prod_congr rfl fun PP hP => by rw [hg PP hP x]
  · exact Finset.prod_congr rfl fun PP hP => by rw [hq PP hP x]

end Lev

end GlobalTheory.FrameTransfer

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem GlobalTheory.levS_levChi_of_frames : ∀ {D : D7} (V : HSp D) (β β' : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (L : LevDat D.host.E ℂ V.rank), IsFrame β Λ → IsFrame β' Λ → (∀ PP ∈ L.Pg, ∀ x, redFn β PP x = redFn β' PP x) → (∀ PP ∈ L.Q, ∀ x, redFn β PP x = redFn β' PP x) → ∀ κ : GA D V, (κ ∈ levS V β L ↔ κ ∈ levS V β' L) ∧ levChi V β L κ = levChi V β' L κ := by
  intro D V β β' Λ L hβ hβ' hg hq κ
  have hSt := GlobalTheory.FrameTransfer.st_eq hβ hβ'
  refine ⟨?_, ?_⟩
  · show κ ∈ levG V β L ↔ κ ∈ levG V β' L
    simp only [levG, levA, Subgroup.mem_inf, Subgroup.mem_comap]
    rw [GlobalTheory.FrameTransfer.mem_lev_iff hSt hg hq]
  · unfold levChi
    rw [GlobalTheory.FrameTransfer.levFn_eq hg hq]
