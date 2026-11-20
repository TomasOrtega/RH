import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemFormsIffExistsEquivariantExtensionStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelPrimeIncidenceFiniteFibresStableStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UopIsExtStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelChainTransitionIsExtKernelSumStatement

noncomputable section

namespace GlobalTheory.LvT

open Formalism.BasicNotions Classical NumberField
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

variable {D : D7} {u : D.what₂.Word} {X : Ch D u} {i : ℕ}

namespace PtModel

variable (M : PtModel X i)

/- English proof (translation)
By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations.

Apply function extensionality and compare values at an arbitrary argument. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts.
-/
theorem inc_eq_image (v : X.A.vT) (p : M.Pt) :
    {p₁ | M.Inc v p p₁} =
      (fun q => ((p.1, Function.update p.2 v q) : M.Pt)) '' {q | (p.2 v).Inc q} := by
  ext p₁
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨p₁.2 v, h3, ?_⟩
    refine Prod.ext h1.symm ?_
    funext v'
    by_cases hv : v' = v
    · subst hv; simp
    · simp [Function.update_of_ne hv, h2 v' hv]
  · rintro ⟨q, hq, rfl⟩
    refine ⟨rfl, fun v' hv => by simp [Function.update_of_ne hv], ?_⟩
    simpa using hq

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem update_pt_injective (v : X.A.vT) (p : M.Pt) :
    Function.Injective (fun q => ((p.1, Function.update p.2 v q) : M.Pt)) := by
  intro q q' h
  have := congrArg (fun r : M.Pt => r.2 v) h
  simpa using this

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem finsum_inc_eq (v : X.A.vT) (p : M.Pt) (F : M.Pt → M.Val) :
    (∑ᶠ p₁ ∈ {p₁ | M.Inc v p p₁}, F p₁) =
      ∑ᶠ q ∈ {q | (p.2 v).Inc q}, F (p.1, Function.update p.2 v q) := by
  rw [inc_eq_image, finsum_mem_image (M.update_pt_injective v p).injOn]

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem finite_inc_loc (v : X.A.vT) (p : M.Pt) : {q | (p.2 v).Inc q}.Finite := by
  have h := ((GlobalTheory.T.levelPrime_incidence_finite_fibres_stable D u X i M v).1 p).1
  rw [inc_eq_image] at h
  exact Set.Finite.of_finite_image h (M.update_pt_injective v p).injOn

/- English proof (translation)
Consider separately whether the proposition holds or fails. Substitute using the available equality. Both sides reduce to the same expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem finsum_inc_comm (v v' : X.A.vT) (p : M.Pt) (F : M.Pt → M.Val) :
    (∑ᶠ p₁ ∈ {p₁ | M.Inc v p p₁}, ∑ᶠ p₂ ∈ {p₂ | M.Inc v' p₁ p₂}, F p₂) =
      ∑ᶠ p₁ ∈ {p₁ | M.Inc v' p p₁}, ∑ᶠ p₂ ∈ {p₂ | M.Inc v p₁ p₂}, F p₂ := by
  by_cases hv : v = v'
  · subst hv; rfl
  have hv' : v' ≠ v := fun h => hv h.symm
  rw [finsum_inc_eq, finsum_inc_eq]
  simp only [finsum_inc_eq, Function.update_of_ne hv, Function.update_of_ne hv']
  rw [finsum_mem_comm _ (M.finite_inc_loc v p) (M.finite_inc_loc v' p)]
  simp only [Function.update_comm hv]

end PtModel

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem formsStable_of_tgtEq : ∀ (D : D7) (u : D.what₂.Word) (X : Ch D u) (Lv : LevTie X) (Kt : KerTie Lv),
    (∀ i h, (Kt i h).TgtEq) → FormsStable X := by
  intro D u X Lv Kt hK
  refine ⟨fun i hi v φ hφ => ?_, fun i hi v v' φ hφ => ?_, fun i hi φ hφ => ?_⟩
  · obtain ⟨Φ, hΦ⟩ := (GlobalTheory.T.mem_forms_iff_exists_equivariant_extension D u X i (Lv i hi) φ).1 hφ
    exact (GlobalTheory.T.mem_forms_iff_exists_equivariant_extension D u X i (Lv i hi) _).2 ⟨_, GlobalTheory.T.isExt_Uop_finsum_inc_of_isExt D u X i (Lv i hi) v φ Φ hΦ⟩
  · obtain ⟨Φ, hΦ⟩ := (GlobalTheory.T.mem_forms_iff_exists_equivariant_extension D u X i (Lv i hi) φ).1 hφ
    have h1 := GlobalTheory.T.isExt_Uop_finsum_inc_of_isExt D u X i (Lv i hi) v _ _ (GlobalTheory.T.isExt_Uop_finsum_inc_of_isExt D u X i (Lv i hi) v' φ Φ hΦ)
    have h2 := GlobalTheory.T.isExt_Uop_finsum_inc_of_isExt D u X i (Lv i hi) v' _ _ (GlobalTheory.T.isExt_Uop_finsum_inc_of_isExt D u X i (Lv i hi) v φ Φ hΦ)
    funext c
    rw [h1.1 c, h2.1 c]
    simp only []
    rw [(Lv i hi).finsum_inc_comm v v']
  · obtain ⟨Φ, hΦ⟩ := (GlobalTheory.T.mem_forms_iff_exists_equivariant_extension D u X i (Lv i hi.le) φ).1 hφ
    exact (GlobalTheory.T.mem_forms_iff_exists_equivariant_extension D u X (i + 1) (Lv (i + 1) hi) _).2
      ⟨_, GlobalTheory.T.levelChainTransition_isExt_kernel_sum D u X i (Lv i hi.le) (Lv (i + 1) hi) (Kt i hi) φ Φ (hK i hi) hΦ⟩

end GlobalTheory.LvT
