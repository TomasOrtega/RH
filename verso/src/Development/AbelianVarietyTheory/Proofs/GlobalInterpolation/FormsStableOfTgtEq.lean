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
Use extensionality with `p₁`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2, h3⟩`. Use `⟨p₁.2 v, h3, ?_⟩` and prove the remaining obligations. Use `Prod.ext h1.symm ?_` and prove the remaining obligations.

Use function extensionality and compare the values at `v'`. Distinguish the cases in `hv : v' = v`. Substitute `hv` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Function.update_of_ne hv, h2 v' hv]`.

Introduce and unpack `⟨q, hq, rfl⟩`. Use `⟨rfl, fun v' hv => by simp [Function.update_of_ne hv], ?_⟩` and prove the remaining obligations. Simplify using `using hq`.
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
Introduce `q q' h`. Use `congrArg (fun r : M.Pt => r.2 v) h` as an intermediate fact. Simplify using `using this`.
-/
theorem update_pt_injective (v : X.A.vT) (p : M.Pt) :
    Function.Injective (fun q => ((p.1, Function.update p.2 v q) : M.Pt)) := by
  intro q q' h
  have := congrArg (fun r : M.Pt => r.2 v) h
  simpa using this

/- English proof (translation)
Rewrite using `[inc_eq_image, finsum_mem_image (M.update_pt_injective v p).injOn]`.
-/
theorem finsum_inc_eq (v : X.A.vT) (p : M.Pt) (F : M.Pt → M.Val) :
    (∑ᶠ p₁ ∈ {p₁ | M.Inc v p p₁}, F p₁) =
      ∑ᶠ q ∈ {q | (p.2 v).Inc q}, F (p.1, Function.update p.2 v q) := by
  rw [inc_eq_image, finsum_mem_image (M.update_pt_injective v p).injOn]

/- English proof (translation)
Establish `h` using `((GlobalTheory.T.levelPrime_incidence_finite_fibres_stable D u X i M v).1 p).1`. Rewrite `h` using `[inc_eq_image]`. Conclude with `Set.Finite.of_finite_image h (M.update_pt_injective v p).injOn`.
-/
theorem finite_inc_loc (v : X.A.vT) (p : M.Pt) : {q | (p.2 v).Inc q}.Finite := by
  have h := ((GlobalTheory.T.levelPrime_incidence_finite_fibres_stable D u X i M v).1 p).1
  rw [inc_eq_image] at h
  exact Set.Finite.of_finite_image h (M.update_pt_injective v p).injOn

/- English proof (translation)
Distinguish the cases in `hv : v = v'`. Substitute `hv` using the available equality. Both sides reduce to the same expression. Establish `hv' : v' ≠ v` using `fun h => hv h.symm`. Rewrite using `[finsum_inc_eq, finsum_inc_eq]`.

Simplify using `only [finsum_inc_eq, Function.update_of_ne hv, Function.update_of_ne hv']`. Rewrite using `[finsum_mem_comm _ (M.finite_inc_loc v p) (M.finite_inc_loc v' p)]`. Simplify using `only [Function.update_comm hv]`.
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
Introduce `D u X Lv Kt hK`. Use `⟨fun i hi v φ hφ => ?_, fun i hi v v' φ hφ => ?_, fun i hi φ hφ => ?_⟩` and prove the remaining obligations. Take `⟨Φ, hΦ⟩` from `(GlobalTheory.T.mem_forms_iff_exists_equivariant_extension D u X i (Lv i hi) φ).1 hφ`. Conclude with `(GlobalTheory.T.mem_forms_iff_exists_equivariant_extension D u X i (Lv i hi) _).2 ⟨_, GlobalTheory.T.isExt_Uop_finsum_inc_of_isExt D u X i (Lv i hi) v φ Φ hΦ⟩`. Take `⟨Φ, hΦ⟩` from `(GlobalTheory.T.mem_forms_iff_exists_equivariant_extension D u X i (Lv i hi) φ).1 hφ`.

Establish `h1` using `GlobalTheory.T.isExt_Uop_finsum_inc_of_isExt D u X i (Lv i hi) v _ _ (GlobalTheory.T.isExt_Uop_finsum_inc_of_isExt D u X i (Lv i hi) v' φ Φ hΦ)`. Establish `h2` using `GlobalTheory.T.isExt_Uop_finsum_inc_of_isExt D u X i (Lv i hi) v' _ _ (GlobalTheory.T.isExt_Uop_finsum_inc_of_isExt D u X i (Lv i hi) v φ Φ hΦ)`. Use function extensionality and compare the values at `c`. Rewrite using `[h1.1 c, h2.1 c]`. Simplify using `only []`.

Rewrite using `[(Lv i hi).finsum_inc_comm v v']`. Take `⟨Φ, hΦ⟩` from `(GlobalTheory.T.mem_forms_iff_exists_equivariant_extension D u X i (Lv i hi.le) φ).1 hφ`. Conclude with `(GlobalTheory.T.mem_forms_iff_exists_equivariant_extension D u X (i + 1) (Lv (i + 1) hi) _).2 ⟨_, GlobalTheory.T.levelChainTransition_isExt_kernel_sum D u X i (Lv i hi.le) (Lv (i + 1) hi) (Kt i hi) φ Φ (hK i hi) hΦ⟩`.
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
