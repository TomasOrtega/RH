import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DOpMemDStep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActsDIffDOp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuaSpanFiniteDimensionalDualPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalArchimedeanSchwartzFockOperatorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerOperatorsCommutatorScalarStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerTranslationOperatorShiftStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergEquivariantIsometry
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardEvaluationGoodModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardEvaluationModelIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSkewAdaptedDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigurationAGaussianIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigurationALocalEvaluation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigurationALocalIntegralStatement
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.ConeEuler
open GlobalTheory.ThK.EvAt0.PolD GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)
open Classical

noncomputable section

namespace GlobalTheory.ShiftEvPol

section Core

variable {M₀ M₁ ι ι₁ : Type} [AddCommGroup M₀] [Module ℂ M₀] [AddCommGroup M₁] [Module ℂ M₁]

def wordsIn (D : ι → M₀ →ₗ[ℂ] M₀) (S : Set ι) (P : Submodule ℂ M₀) (m : ℕ) : Submodule ℂ M₀ :=
  Nat.rec (motive := fun _ => Submodule ℂ M₀) P
    (fun _ Q => Q ⊔ Submodule.span ℂ {h | ∃ c ∈ S, ∃ x ∈ Q, h = D c x}) m

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem wordsIn_succ (D : ι → M₀ →ₗ[ℂ] M₀) (S : Set ι) (P : Submodule ℂ M₀) (m : ℕ) :
    wordsIn D S P (m + 1) = wordsIn D S P m ⊔ Submodule.span ℂ {h | ∃ c ∈ S, ∃ x ∈ wordsIn D S P m, h = D c x} := rfl

/- English proof (translation)
Rewrite using `[wordsIn_succ]`. Conclude with `le_sup_left`.
-/
theorem wordsIn_le_succ (D : ι → M₀ →ₗ[ℂ] M₀) (S : Set ι) (P : Submodule ℂ M₀) (m : ℕ) :
    wordsIn D S P m ≤ wordsIn D S P (m + 1) := by
  rw [wordsIn_succ]; exact le_sup_left

/- English proof (translation)
The claim follows from `monotone_nat_of_le_succ fun m => wordsIn_le_succ D S P m`.
-/
theorem wordsIn_mono (D : ι → M₀ →ₗ[ℂ] M₀) (S : Set ι) (P : Submodule ℂ M₀) : Monotone (wordsIn D S P) :=
  monotone_nat_of_le_succ fun m => wordsIn_le_succ D S P m

/- English proof (translation)
Rewrite using `[wordsIn_succ]`. Conclude with `Submodule.mem_sup_right (Submodule.subset_span ⟨c, hc, x, hx, rfl⟩)`.
-/
theorem mem_wordsIn_succ (D : ι → M₀ →ₗ[ℂ] M₀) (S : Set ι) (P : Submodule ℂ M₀) {m : ℕ} {c : ι} (hc : c ∈ S) {x : M₀}
    (hx : x ∈ wordsIn D S P m) : D c x ∈ wordsIn D S P (m + 1) := by
  rw [wordsIn_succ]
  exact Submodule.mem_sup_right (Submodule.subset_span ⟨c, hc, x, hx, rfl⟩)

/- English proof (translation)
Establish `red : ∀ j h, h ∈ wordsIn D (IA ∪ IM) (Submodule.span ℂ P0) j → (∀ d ∈ ID, D d h ∈ wordsIn D (IA ∪ IM) (Submodule.span ℂ P0) (j + 1)) → ∀ c, D c h ∈ wordsIn D (IA ∪ IM) (Submodule.span ℂ P0) (j + 1)`. Introduce `j h hh hd c`. Take `⟨a, ha, m, hm, d, hd', e⟩` from `hdec c`. Rewrite using `[e, LinearMap.add_apply, LinearMap.add_apply]`. Conclude with `add_mem (add_mem (mem_wordsIn_succ D _ _ (Or.inl ha) hh) (mem_wordsIn_succ D _ _ (Or.inr hm) hh)) (hd d hd')`.

Introduce `j`. Proceed by induction on `j with`. Consider the case `zero`. Introduce `h hh`. Use `red 0 h hh fun d hd => ?_` and prove the remaining obligations.

Proceed by induction on `hh using Submodule.span_induction with`. Consider the case `mem g hg`. Take `⟨a, ha, z, e⟩` from `hvac g hg d hd`. Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ z (mem_wordsIn_succ D _ _ (Or.inl ha) (Submodule.subset_span hg))`.

Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`. Consider the case `smul r x _ hx => rw [map_smul]`.

Conclude with `Submodule.smul_mem _ r hx`. Consider the case `succ j ih`. Introduce `h hh`. Use `red (j + 1) h hh fun d hd => ?_` and prove the remaining obligations. Rewrite `hh` using `[wordsIn_succ]`.

Take `⟨h₁, h₁m, h₂, h₂m, rfl⟩` from `Submodule.mem_sup.1 hh`. Rewrite using `[map_add]`. Use `add_mem (wordsIn_le_succ D _ _ _ (ih h₁ h₁m d)) ?_` and prove the remaining obligations. Use `clear hh`. Proceed by induction on `h₂m using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨c', hc', x', hx', rfl⟩` from `hx`. Take `⟨s, hs⟩` from `hcomm d c'`. Establish `e : D d (D c' x') = D c' (D d x') + s • x'` using `by rw [← hs x']; abel`. Rewrite using `[e]`.

Conclude with `add_mem (mem_wordsIn_succ D _ _ hc' (ih x' hx' d)) (Submodule.smul_mem _ s (wordsIn_mono D _ _ (by omega) hx'))`. Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`.

Consider the case `smul r x _ hx => rw [map_smul]`. Conclude with `Submodule.smul_mem _ r hx`.
-/
theorem comm_step (D : ι → M₀ →ₗ[ℂ] M₀) (IA IM ID : Set ι) (P0 : Set M₀)
    (hdec : ∀ c, ∃ a ∈ IA, ∃ m ∈ IM, ∃ d ∈ ID, D c = D a + D m + D d)
    (hcomm : ∀ c c', ∃ s : ℂ, ∀ x, D c (D c' x) - D c' (D c x) = s • x)
    (hvac : ∀ g ∈ P0, ∀ d ∈ ID, ∃ a ∈ IA, ∃ z : ℂ, D d g = z • D a g) :
    ∀ j, ∀ h ∈ wordsIn D (IA ∪ IM) (Submodule.span ℂ P0) j, ∀ c,
      D c h ∈ wordsIn D (IA ∪ IM) (Submodule.span ℂ P0) (j + 1) := by
  have red : ∀ j h, h ∈ wordsIn D (IA ∪ IM) (Submodule.span ℂ P0) j →
      (∀ d ∈ ID, D d h ∈ wordsIn D (IA ∪ IM) (Submodule.span ℂ P0) (j + 1)) →
      ∀ c, D c h ∈ wordsIn D (IA ∪ IM) (Submodule.span ℂ P0) (j + 1) := by
    intro j h hh hd c
    obtain ⟨a, ha, m, hm, d, hd', e⟩ := hdec c
    rw [e, LinearMap.add_apply, LinearMap.add_apply]
    exact add_mem (add_mem (mem_wordsIn_succ D _ _ (Or.inl ha) hh) (mem_wordsIn_succ D _ _ (Or.inr hm) hh)) (hd d hd')
  intro j
  induction j with
  | zero =>
    intro h hh
    refine red 0 h hh fun d hd => ?_
    induction hh using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨a, ha, z, e⟩ := hvac g hg d hd
      rw [e]
      exact Submodule.smul_mem _ z (mem_wordsIn_succ D _ _ (Or.inl ha) (Submodule.subset_span hg))
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx
  | succ j ih =>
    intro h hh
    refine red (j + 1) h hh fun d hd => ?_
    rw [wordsIn_succ] at hh
    obtain ⟨h₁, h₁m, h₂, h₂m, rfl⟩ := Submodule.mem_sup.1 hh
    rw [map_add]
    refine add_mem (wordsIn_le_succ D _ _ _ (ih h₁ h₁m d)) ?_
    clear hh
    induction h₂m using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c', hc', x', hx', rfl⟩ := hx
      obtain ⟨s, hs⟩ := hcomm d c'
      have e : D d (D c' x') = D c' (D d x') + s • x' := by rw [← hs x']; abel
      rw [e]
      exact add_mem (mem_wordsIn_succ D _ _ hc' (ih x' hx' d))
        (Submodule.smul_mem _ s (wordsIn_mono D _ _ (by omega) hx'))
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

/- English proof (translation)
Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => exact le_rfl`. Consider the case `succ j ih`. Rewrite using `[wordsIn_succ D Set.univ]`.

Use `sup_le (ih.trans (wordsIn_le_succ _ _ _ _)) (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨c, -, x, hx, rfl⟩`. Conclude with `comm_step D IA IM ID P0 hdec hcomm hvac j x (ih hx) c`.
-/
theorem words_le (D : ι → M₀ →ₗ[ℂ] M₀) (IA IM ID : Set ι) (P0 : Set M₀)
    (hdec : ∀ c, ∃ a ∈ IA, ∃ m ∈ IM, ∃ d ∈ ID, D c = D a + D m + D d)
    (hcomm : ∀ c c', ∃ s : ℂ, ∀ x, D c (D c' x) - D c' (D c x) = s • x)
    (hvac : ∀ g ∈ P0, ∀ d ∈ ID, ∃ a ∈ IA, ∃ z : ℂ, D d g = z • D a g) :
    ∀ j, wordsIn D Set.univ (Submodule.span ℂ P0) j ≤ wordsIn D (IA ∪ IM) (Submodule.span ℂ P0) j := by
  intro j
  induction j with
  | zero => exact le_rfl
  | succ j ih =>
    rw [wordsIn_succ D Set.univ]
    refine sup_le (ih.trans (wordsIn_le_succ _ _ _ _)) (Submodule.span_le.2 ?_)
    rintro _ ⟨c, -, x, hx, rfl⟩
    exact comm_step D IA IM ID P0 hdec hcomm hvac j x (ih hx) c

/- English proof (translation)
Introduce `j`. Proceed by induction on `j with`. Consider the case `zero`. Introduce `h hh`. Proceed by induction on `hh using Submodule.span_induction with`.

Consider the case `mem g hg => exact hbase g hg`. Consider the case `zero => rw [map_zero, map_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add, map_add]`. Conclude with `add_mem hx hy`.

Consider the case `smul r x _ hx => rw [map_smul, map_smul]`. Conclude with `Submodule.smul_mem _ r hx`. Consider the case `succ j ih`. Introduce `h hh`. Rewrite `hh` using `[wordsIn_succ]`.

Take `⟨h₁, h₁m, h₂, h₂m, rfl⟩` from `Submodule.mem_sup.1 hh`. Rewrite using `[map_add, map_add]`. Use `add_mem (wordsIn_le_succ _ _ _ _ (ih h₁ h₁m)) ?_` and prove the remaining obligations. Use `clear hh`. Proceed by induction on `h₂m using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨c, hc, x', hx', rfl⟩` from `hx`. Take `⟨t, ht⟩` from `hconj c`. Rewrite using `[ht, map_add, map_smul]`. Use `add_mem ?_ (Submodule.smul_mem _ t (wordsIn_le_succ _ _ _ _ (ih x' hx')))` and prove the remaining obligations.

Break down `hc with hc | hc` into its components or cases. Rewrite using `[hkill c hc]`. Conclude with `zero_mem _`. Take `⟨c₁, hc₁⟩` from `hint c hc`. Rewrite using `[hc₁]`.

Conclude with `mem_wordsIn_succ D₁ _ _ (Set.mem_univ c₁) (ih x' hx')`. Consider the case `zero => rw [map_zero, map_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add, map_add]`. Conclude with `add_mem hx hy`.

Consider the case `smul r x _ hx => rw [map_smul, map_smul]`. Conclude with `Submodule.smul_mem _ r hx`.
-/
theorem ev_step (D : ι → M₀ →ₗ[ℂ] M₀) (D₁ : ι₁ → M₁ →ₗ[ℂ] M₁) (IA IM : Set ι) (P0 : Set M₀) (Q0 : Submodule ℂ M₁)
    (R : M₀ →ₗ[ℂ] M₀) (ei : M₀ →ₗ[ℂ] M₁)
    (hconj : ∀ c, ∃ t : ℂ, ∀ x, R (D c x) = D c (R x) + t • R x)
    (hkill : ∀ c ∈ IA, ∀ x, ei (D c x) = 0)
    (hint : ∀ c ∈ IM, ∃ c₁, ∀ x, ei (D c x) = D₁ c₁ (ei x))
    (hbase : ∀ g ∈ P0, ei (R g) ∈ Q0) :
    ∀ j, ∀ h ∈ wordsIn D (IA ∪ IM) (Submodule.span ℂ P0) j, ei (R h) ∈ wordsIn D₁ Set.univ Q0 j := by
  intro j
  induction j with
  | zero =>
    intro h hh
    induction hh using Submodule.span_induction with
    | mem g hg => exact hbase g hg
    | zero => rw [map_zero, map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add, map_add]; exact add_mem hx hy
    | smul r x _ hx => rw [map_smul, map_smul]; exact Submodule.smul_mem _ r hx
  | succ j ih =>
    intro h hh
    rw [wordsIn_succ] at hh
    obtain ⟨h₁, h₁m, h₂, h₂m, rfl⟩ := Submodule.mem_sup.1 hh
    rw [map_add, map_add]
    refine add_mem (wordsIn_le_succ _ _ _ _ (ih h₁ h₁m)) ?_
    clear hh
    induction h₂m using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, hc, x', hx', rfl⟩ := hx
      obtain ⟨t, ht⟩ := hconj c
      rw [ht, map_add, map_smul]
      refine add_mem ?_ (Submodule.smul_mem _ t (wordsIn_le_succ _ _ _ _ (ih x' hx')))
      rcases hc with hc | hc
      · rw [hkill c hc]; exact zero_mem _
      · obtain ⟨c₁, hc₁⟩ := hint c hc
        rw [hc₁]
        exact mem_wordsIn_succ D₁ _ _ (Set.mem_univ c₁) (ih x' hx')
    | zero => rw [map_zero, map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add, map_add]; exact add_mem hx hy
    | smul r x _ hx => rw [map_smul, map_smul]; exact Submodule.smul_mem _ r hx

end Core

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [dOp_apply, SchwartzMap.add_apply, map_add, lin, Pi.add_apply, mul_add, Finset.sum_add_distrib]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dOp_add {κ : Type} [Fintype κ] (a b a' b' : κ → mixedEmbedding.mixedSpace F) (f : SInf F κ) :
    dOp (a + a') (b + b') f = dOp a b f + dOp a' b' f := by
  ext x
  simp only [dOp_apply, SchwartzMap.add_apply, map_add, lin, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  push_cast
  ring

end GlobalTheory.ShiftEvPol

open GlobalTheory.ShiftEvPol in

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ _ B b a' G G₁ H H' X om om' hC hT hG e hE ei ev _ hev hpe m`. Establish `hψ : IsStd B.ψ` using `hT.base.std`. Establish `hM : G.M.IsGood B.ψ` using `hT.geo.hM`. Set `D : ((Fin (b + 2) × Fin (b + 2 + a') → mixedEmbedding.mixedSpace F) × (Fin (b + 2) × Fin (b + 2 + a') → mixedEmbedding.mixedSpace F)) → SInf F (Fin (b + 2) × Fin (b + 2 + a')) →ₗ[ℂ] SInf F (Fin (b + 2) × Fin (b + 2 + a'))` to `fun c => ((dOp c.1 c.2 : SInf F _ →L[ℂ] SInf F _) : SInf F _ →ₗ[ℂ] SInf F _)`. Set `D₁ : ((Fin b × Fin (b + a') → mixedEmbedding.mixedSpace F) × (Fin b × Fin (b + a') → mixedEmbedding.mixedSpace F)) → SInf F (Fin b × Fin (b + a')) →ₗ[ℂ] SInf F (Fin b × Fin (b + a'))` to `fun c => ((dOp c.1 c.2 : SInf F _ →L[ℂ] SInf F _) : SInf F _ →ₗ[ℂ] SInf F _)`.

Establish `D_add : ∀ p q, D (p + q) = D p + D q` using `fun p q => LinearMap.ext fun f => dOp_add p.1 p.2 q.1 q.2 f`. Set `IA : Set ((Fin (b + 2) × Fin (b + 2 + a') → mixedEmbedding.mixedSpace F) × (Fin (b + 2) × Fin (b + 2 + a') → mixedEmbedding.mixedSpace F))` to `{c | ∃ y z, c = coordI G.M (Matrix.vecMulVec y (incV F H'.x) + Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ z))}`. Set `IM : Set ((Fin (b + 2) × Fin (b + 2 + a') → mixedEmbedding.mixedSpace F) × (Fin (b + 2) × Fin (b + 2 + a') → mixedEmbedding.mixedSpace F))` to `{c | ∃ x : Matrix (Fin b) (Fin (b + a')) (AE F E), c = coordI G.M (incM F H.ι * x * (incM F H'.ι)ᵀ)}`. Set `ID : Set ((Fin (b + 2) × Fin (b + 2 + a') → mixedEmbedding.mixedSpace F) × (Fin (b + 2) × Fin (b + 2 + a') → mixedEmbedding.mixedSpace F))` to `{c | ∃ y z, c = coordI G.M (Matrix.vecMulVec y (incV F H'.y) + Matrix.vecMulVec (incV F H.y) (incM F H'.ι *ᵥ z))}`. Set `P0 : Set (SInf F (Fin (b + 2) × Fin (b + 2 + a')))` to `{g | GaussD G.M B.emb g}`.

Set `Q0 : Submodule ℂ (SInf F (Fin b × Fin (b + a')))` to `(GlobalTheory.FockKFin.vacSp G.M B.emb).map (ei : SInf F _ →ₗ[ℂ] SInf F _)`. Establish `hdec : ∀ c, ∃ a ∈ IA, ∃ mm ∈ IM, ∃ d ∈ ID, D c = D a + D mm + D d`. Introduce `c`. Take `⟨y, y', z, z', x, hu⟩` from `GlobalTheory.T.hermitian_skew_adapted_decomposition F E σ B _ _ _ _ G.V G.W G₁.V G₁.W H H' _ _ _ _ _ _ _ _ hT.geo.hV hT.geo.hW hC.hH hC.hH' (G.M.co.e.symm (liftV c.1, liftV c.2))`. Establish `hc : c = coordI G.M (G.M.co.e.symm (liftV c.1, liftV c.2))` using `(coordI_lift G.M c).symm`.

Use `⟨_, ⟨y, z, rfl⟩, _, ⟨x, rfl⟩, _, ⟨y', z', rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← D_add, ← D_add, ← coordI_add, ← coordI_add, ← hu, ← hc]`. Establish `hcomm : ∀ c c', ∃ s : ℂ, ∀ x, D c (D c' x) - D c' (D c x) = s • x`. Introduce `c c'`. Take `⟨s, hs⟩` from `GlobalTheory.T.schrodinger_operators_commutator_scalar F _ c.1 c.2 c'.1 c'.2`.

Conclude with `⟨s, fun x => hs x⟩`. Establish `hvac : ∀ g ∈ P0, ∀ d ∈ ID, ∃ a ∈ IA, ∃ z : ℂ, D d g = z • D a g`. Introduce and unpack `g hg d ⟨y, z, rfl⟩`. Take `⟨y₁, z₁, h⟩` from `GlobalTheory.T.configuration_a_gaussian_integral F E σ B b a' G G₁ H H' X om om' hC hT g hg y z`. Conclude with `⟨_, ⟨y₁, z₁, rfl⟩, -Complex.I, h⟩`.

Establish `hkill : ∀ c ∈ IA, ∀ x, ei (D c x) = 0`. Introduce and unpack `c ⟨y, z, rfl⟩ x`. Establish `k` using `GlobalTheory.T.standard_evaluation_good_model F E σ B _ _ _ _ G.V G.W G₁.V G₁.W G.M G₁.M H.ι H'.ι (isoA H H') e hψ hM hG hE ei ev (fun v => (hev v).1) hpe`. Rewrite using `[coordI_add, D_add, LinearMap.add_apply, map_add]`. Establish `h1` using `k (Matrix.vecMulVec y (incV F H'.x)) (fun t => Or.inl ⟨realAd F t • y, by rw [Matrix.smul_vecMulVec]⟩) x`.

Establish `h2` using `k (Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ z)) (fun t => Or.inr ⟨realAd F t • z, by rw [Matrix.mulVec_smul, Matrix.vecMulVec_smul]⟩) x`. Express the relevant statement in the definitionally equal form `ei (dOp _ _ x) + ei (dOp _ _ x) = 0`. Rewrite using `[h1, h2, add_zero]`. Establish `hint : ∀ c ∈ IM, ∃ c₁, ∀ x, ei (D c x) = D₁ c₁ (ei x)`. Introduce and unpack `c ⟨x, rfl⟩`.

Conclude with `⟨coordI G₁.M x, fun f => GlobalTheory.T.standard_evaluation_model_integral F E σ B _ _ _ _ G.V G.W G₁.V G₁.W G.M G₁.M H.ι H'.ι (isoA H H') e hψ hM hG hE ei ev (fun v => (hev v).1) hpe x f⟩`. Establish `hpolw : ∀ j, GlobalTheory.FockKFin.polLe G.M B.emb j ≤ wordsIn D Set.univ (Submodule.span ℂ P0) j`. Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => exact le_rfl`.

Consider the case `succ j ih`. Rewrite using `[GlobalTheory.FockKFin.polLe_succ, wordsIn_succ]`. Use `sup_le_sup ih ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.FockKFin.dStep]`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨a, b', f, hf, rfl⟩`. Conclude with `Submodule.subset_span ⟨(a, b'), Set.mem_univ _, f, ih hf, rfl⟩`. Establish `hPair : IsPair B G.M X.β (X.β / X.α) om (b + 2 - G.p) G.p (b + 2 + a' - (G.p + G.q)) (G.p + G.q)`. Use `⟨hT.base, hT.geo.hV, hT.geo.hW, hT.geo.hM, hT.chars.heckeβ, ⟨hT.chars.heckeβ.1.div' hT.chars.heckeα.1, fun x => by` and prove the remaining obligations. Simplify using `only [MonoidHom.div_apply, hT.chars.heckeβ.2 x, hT.chars.heckeα.2 x, div_self']⟩,`.

Use the proof step `hT.chars.resβ, fun x => ?_, hT.weil⟩`. Establish `e1` using `hT.chars.resβ x`. Establish `e2` using `hT.chars.resα x`. Rewrite using `[MonoidHom.div_apply, Circle.coe_div, e1, e2]`. Use `split_ifs`.

Simplify using the standard rewrite rules. Establish `h : ((-1 : ℂ) ^ a') * (-1) ^ a' = 1` using `by rw [← pow_add, ← two_mul, pow_mul]; norm_num`. Rewrite using `[div_eq_iff (pow_ne_zero _ (by norm_num)), pow_add (-1 : ℂ) (b + 2) a', mul_assoc, h, mul_one]`. Use `⟨wordsIn D₁ Set.univ Q0 m, ?_, ?_, ?_⟩` and prove the remaining obligations. Proceed by induction on `m with`.

Consider the case `zero => haveI := GlobalTheory.T.fockVacua_span_finiteDimensional_dualPair F E σ B (b + 2) (b + 2 + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ hPair`. Express the relevant statement in the definitionally equal form `FiniteDimensional ℂ Q0`. Use `infer_instance`. Consider the case `succ j ih`. Rewrite using `[wordsIn_succ]`.

Use `haveI := ih`. Use `haveI := GlobalTheory.T.finiteDimensional_archimedeanSchwartzFockOperatorSpan F _ _ ih`. Establish `hle : Submodule.span ℂ {h | ∃ c ∈ (Set.univ : Set _), ∃ x ∈ wordsIn D₁ Set.univ Q0 j, h = D₁ c x} ≤ GlobalTheory.FockKFin.dStep (wordsIn D₁ Set.univ Q0 j)`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨c, -, x, hx, rfl⟩`.

Conclude with `GlobalTheory.FockKFin.dOp_mem_dStep _ c.1 c.2 hx`. Use `haveI := Submodule.finiteDimensional_of_le hle`. Use `infer_instance`. Proceed by induction on `m with`. Consider the case `zero`.

Express the relevant statement in the definitionally equal form `Q0 ≤ _`. Use `Submodule.map_le_iff_le_comap.2 (Submodule.span_le.2 fun g hg => ?_)` and prove the remaining obligations. Conclude with `GlobalTheory.ThK.EvAt0.PolEv.gauss_mem hψ G₁.M B.emb (GlobalTheory.T.configuration_a_local_integral F E σ B b a' G G₁ H H' X om om' hC hT hG e hE ei ev (fun v => (hev v).1) hpe g hg)`. Consider the case `succ j ih`. Rewrite using `[wordsIn_succ]`.

Use `sup_le ih (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨c, -, x, hx, rfl⟩`. Conclude with `GlobalTheory.ThK.EvAt0.PolEv.dOp_mem hψ G₁.M B.emb c.1 c.2 (ih hx)`. Introduce `l hl h hh`. Establish `hex : ∀ f : SInf F (Fin (b + 2) × Fin (b + 2 + a')), ∃ f₁ : SInf F (Fin (b + 2) × Fin (b + 2 + a')), Acts (evI F) (G.M.co.rho B.ψ (partInf F (shiftA H H' l))) f f₁` using `fun f => ⟨_, (locOpInf_rho G.M.co hψ _ f).1⟩`.

Establish `hT' : IsLinearMap ℂ (G.M.co.rho B.ψ (partInf F (shiftA H H' l)))` using `⟨fun f g => funext fun x => mul_add _ _ _, fun c f => funext fun x => mul_left_comm _ _ _⟩`. Set `R : SInf F (Fin (b + 2) × Fin (b + 2 + a')) →ₗ[ℂ] SInf F (Fin (b + 2) × Fin (b + 2 + a'))` to `{ toFun := locOpInf (G.M.co.rho B.ψ (partInf F (shiftA H H' l))) map_add' := fun f g => by simpa using locOpInf_lin hT' hex 1 1 f g map_smul' := fun c f => by simpa using locOpInf_lin hT' hex c 0 f 0 }`. Establish `hconj : ∀ c, ∃ t : ℂ, ∀ x, R (D c x) = D c (R x) + t • R x`. Introduce `c`. Take `⟨t, ht⟩` from `GlobalTheory.T.schrodinger_translation_operator_shift F _ (coordI G.M (shiftA H H' l)) c.1 c.2`.

Conclude with `⟨t, fun x => ht x _ _ (locOpInf_rho G.M.co hψ _ x).2 (locOpInf_rho G.M.co hψ _ _).2⟩`. Establish `hbase : ∀ g ∈ P0, ei (R g) ∈ Q0`. Introduce `g hg`. Take `⟨c, hc⟩` from `GlobalTheory.T.configuration_a_local_evaluation F E σ B b a' G G₁ H H' X om om' hC hT hG e hE ei ev (fun v => (hev v).1) hpe l hl g hg`. Express the relevant statement in the definitionally equal form `ei (locOpInf _ g) ∈ Q0`.

Rewrite using `[hc]`. Conclude with `Q0.smul_mem c (Submodule.mem_map_of_mem (Submodule.subset_span hg))`. Conclude with `ev_step D D₁ IA IM P0 Q0 R (ei : SInf F _ →ₗ[ℂ] SInf F _) hconj hkill hint hbase m h (words_le D IA IM ID P0 hdec hcomm hvac m (hpolw m hh))`.
-/
theorem GlobalTheory.ShiftEvPol.shiftEv_polLe : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), GlobalTheory.FunPr.Hypotheses₂ →
    ∀ (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a'))
    (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    CfgA B G G₁ H H' → IsTriple B G X om om' → G₁.M.IsGood B.ψ →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e →
    ∀ (ei : SInf F (Fin (b + 2) × Fin (b + 2 + a')) →L[ℂ] SInf F (Fin b × Fin (b + a')))
      (ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (b + 2 + a') → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (b + a') → Fv F v) → ℂ),
      ei ≠ 0 → (∀ v, ev v (G.M.vac v) = G₁.M.vac v ∧ (SB _).map (ev v) = SB _) →
      (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    ∀ m : ℕ, ∃ V : Submodule ℂ (SInf F (Fin b × Fin (b + a'))), FiniteDimensional ℂ V ∧ V ≤ G₁.M.Pol B.ψ B.emb ∧
      ∀ l ∈ idelesAt E (evI F), ∀ h ∈ GlobalTheory.FockKFin.polLe G.M B.emb m,
        ei (locOpInf (G.M.co.rho B.ψ (partInf F (shiftA H H' l))) h) ∈ V := by
  intro F E _ _ _ _ _ σ _ B b a' G G₁ H H' X om om' hC hT hG e hE ei ev _ hev hpe m
  have hψ : IsStd B.ψ := hT.base.std
  have hM : G.M.IsGood B.ψ := hT.geo.hM
  let D : ((Fin (b + 2) × Fin (b + 2 + a') → mixedEmbedding.mixedSpace F) ×
      (Fin (b + 2) × Fin (b + 2 + a') → mixedEmbedding.mixedSpace F)) →
      SInf F (Fin (b + 2) × Fin (b + 2 + a')) →ₗ[ℂ] SInf F (Fin (b + 2) × Fin (b + 2 + a')) :=
    fun c => ((dOp c.1 c.2 : SInf F _ →L[ℂ] SInf F _) : SInf F _ →ₗ[ℂ] SInf F _)
  let D₁ : ((Fin b × Fin (b + a') → mixedEmbedding.mixedSpace F) × (Fin b × Fin (b + a') → mixedEmbedding.mixedSpace F)) →
      SInf F (Fin b × Fin (b + a')) →ₗ[ℂ] SInf F (Fin b × Fin (b + a')) :=
    fun c => ((dOp c.1 c.2 : SInf F _ →L[ℂ] SInf F _) : SInf F _ →ₗ[ℂ] SInf F _)
  have D_add : ∀ p q, D (p + q) = D p + D q := fun p q => LinearMap.ext fun f => dOp_add p.1 p.2 q.1 q.2 f
  let IA : Set ((Fin (b + 2) × Fin (b + 2 + a') → mixedEmbedding.mixedSpace F) ×
      (Fin (b + 2) × Fin (b + 2 + a') → mixedEmbedding.mixedSpace F)) :=
    {c | ∃ y z, c = coordI G.M (Matrix.vecMulVec y (incV F H'.x) + Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ z))}
  let IM : Set ((Fin (b + 2) × Fin (b + 2 + a') → mixedEmbedding.mixedSpace F) ×
      (Fin (b + 2) × Fin (b + 2 + a') → mixedEmbedding.mixedSpace F)) :=
    {c | ∃ x : Matrix (Fin b) (Fin (b + a')) (AE F E), c = coordI G.M (incM F H.ι * x * (incM F H'.ι)ᵀ)}
  let ID : Set ((Fin (b + 2) × Fin (b + 2 + a') → mixedEmbedding.mixedSpace F) ×
      (Fin (b + 2) × Fin (b + 2 + a') → mixedEmbedding.mixedSpace F)) :=
    {c | ∃ y z, c = coordI G.M (Matrix.vecMulVec y (incV F H'.y) + Matrix.vecMulVec (incV F H.y) (incM F H'.ι *ᵥ z))}
  let P0 : Set (SInf F (Fin (b + 2) × Fin (b + 2 + a'))) := {g | GaussD G.M B.emb g}
  let Q0 : Submodule ℂ (SInf F (Fin b × Fin (b + a'))) :=
    (GlobalTheory.FockKFin.vacSp G.M B.emb).map (ei : SInf F _ →ₗ[ℂ] SInf F _)

  have hdec : ∀ c, ∃ a ∈ IA, ∃ mm ∈ IM, ∃ d ∈ ID, D c = D a + D mm + D d := by
    intro c
    obtain ⟨y, y', z, z', x, hu⟩ := GlobalTheory.T.hermitian_skew_adapted_decomposition F E σ B _ _ _ _ G.V G.W G₁.V G₁.W H H' _ _ _ _ _ _ _ _ hT.geo.hV hT.geo.hW hC.hH hC.hH'
      (G.M.co.e.symm (liftV c.1, liftV c.2))
    have hc : c = coordI G.M (G.M.co.e.symm (liftV c.1, liftV c.2)) := (coordI_lift G.M c).symm
    refine ⟨_, ⟨y, z, rfl⟩, _, ⟨x, rfl⟩, _, ⟨y', z', rfl⟩, ?_⟩
    rw [← D_add, ← D_add, ← coordI_add, ← coordI_add, ← hu, ← hc]
  have hcomm : ∀ c c', ∃ s : ℂ, ∀ x, D c (D c' x) - D c' (D c x) = s • x := by
    intro c c'
    obtain ⟨s, hs⟩ := GlobalTheory.T.schrodinger_operators_commutator_scalar F _ c.1 c.2 c'.1 c'.2
    exact ⟨s, fun x => hs x⟩
  have hvac : ∀ g ∈ P0, ∀ d ∈ ID, ∃ a ∈ IA, ∃ z : ℂ, D d g = z • D a g := by
    rintro g hg d ⟨y, z, rfl⟩
    obtain ⟨y₁, z₁, h⟩ := GlobalTheory.T.configuration_a_gaussian_integral F E σ B b a' G G₁ H H' X om om' hC hT g hg y z
    exact ⟨_, ⟨y₁, z₁, rfl⟩, -Complex.I, h⟩
  have hkill : ∀ c ∈ IA, ∀ x, ei (D c x) = 0 := by
    rintro c ⟨y, z, rfl⟩ x
    have k := GlobalTheory.T.standard_evaluation_good_model F E σ B _ _ _ _ G.V G.W G₁.V G₁.W G.M G₁.M H.ι H'.ι (isoA H H') e hψ hM hG hE ei ev
      (fun v => (hev v).1) hpe
    rw [coordI_add, D_add, LinearMap.add_apply, map_add]
    have h1 := k (Matrix.vecMulVec y (incV F H'.x)) (fun t => Or.inl ⟨realAd F t • y, by rw [Matrix.smul_vecMulVec]⟩) x
    have h2 := k (Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ z))
      (fun t => Or.inr ⟨realAd F t • z, by rw [Matrix.mulVec_smul, Matrix.vecMulVec_smul]⟩) x
    change ei (dOp _ _ x) + ei (dOp _ _ x) = 0
    rw [h1, h2, add_zero]
  have hint : ∀ c ∈ IM, ∃ c₁, ∀ x, ei (D c x) = D₁ c₁ (ei x) := by
    rintro c ⟨x, rfl⟩
    exact ⟨coordI G₁.M x, fun f => GlobalTheory.T.standard_evaluation_model_integral F E σ B _ _ _ _ G.V G.W G₁.V G₁.W G.M G₁.M H.ι H'.ι (isoA H H') e hψ hM hG hE ei ev
      (fun v => (hev v).1) hpe x f⟩
  have hpolw : ∀ j, GlobalTheory.FockKFin.polLe G.M B.emb j ≤ wordsIn D Set.univ (Submodule.span ℂ P0) j := by
    intro j
    induction j with
    | zero => exact le_rfl
    | succ j ih =>
      rw [GlobalTheory.FockKFin.polLe_succ, wordsIn_succ]
      refine sup_le_sup ih ?_
      rw [GlobalTheory.FockKFin.dStep]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨a, b', f, hf, rfl⟩
      exact Submodule.subset_span ⟨(a, b'), Set.mem_univ _, f, ih hf, rfl⟩
  have hPair : IsPair B G.M X.β (X.β / X.α) om (b + 2 - G.p) G.p (b + 2 + a' - (G.p + G.q)) (G.p + G.q) := by
    refine ⟨hT.base, hT.geo.hV, hT.geo.hW, hT.geo.hM, hT.chars.heckeβ,
      ⟨hT.chars.heckeβ.1.div' hT.chars.heckeα.1, fun x => by
        simp only [MonoidHom.div_apply, hT.chars.heckeβ.2 x, hT.chars.heckeα.2 x, div_self']⟩,
      hT.chars.resβ, fun x => ?_, hT.weil⟩
    have e1 := hT.chars.resβ x
    have e2 := hT.chars.resα x
    rw [MonoidHom.div_apply, Circle.coe_div, e1, e2]
    split_ifs
    · simp
    · have h : ((-1 : ℂ) ^ a') * (-1) ^ a' = 1 := by rw [← pow_add, ← two_mul, pow_mul]; norm_num
      rw [div_eq_iff (pow_ne_zero _ (by norm_num)), pow_add (-1 : ℂ) (b + 2) a', mul_assoc, h, mul_one]
  refine ⟨wordsIn D₁ Set.univ Q0 m, ?_, ?_, ?_⟩
  · induction m with
    | zero =>
      haveI := GlobalTheory.T.fockVacua_span_finiteDimensional_dualPair F E σ B (b + 2) (b + 2 + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ hPair
      change FiniteDimensional ℂ Q0
      infer_instance
    | succ j ih =>
      rw [wordsIn_succ]
      haveI := ih
      haveI := GlobalTheory.T.finiteDimensional_archimedeanSchwartzFockOperatorSpan F _ _ ih
      have hle : Submodule.span ℂ {h | ∃ c ∈ (Set.univ : Set _), ∃ x ∈ wordsIn D₁ Set.univ Q0 j, h = D₁ c x} ≤
          GlobalTheory.FockKFin.dStep (wordsIn D₁ Set.univ Q0 j) := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨c, -, x, hx, rfl⟩
        exact GlobalTheory.FockKFin.dOp_mem_dStep _ c.1 c.2 hx
      haveI := Submodule.finiteDimensional_of_le hle
      infer_instance
  · induction m with
    | zero =>
      change Q0 ≤ _
      refine Submodule.map_le_iff_le_comap.2 (Submodule.span_le.2 fun g hg => ?_)
      exact GlobalTheory.ThK.EvAt0.PolEv.gauss_mem hψ G₁.M B.emb
        (GlobalTheory.T.configuration_a_local_integral F E σ B b a' G G₁ H H' X om om' hC hT hG e hE ei ev (fun v => (hev v).1) hpe g hg)
    | succ j ih =>
      rw [wordsIn_succ]
      refine sup_le ih (Submodule.span_le.2 ?_)
      rintro _ ⟨c, -, x, hx, rfl⟩
      exact GlobalTheory.ThK.EvAt0.PolEv.dOp_mem hψ G₁.M B.emb c.1 c.2 (ih hx)
  · intro l hl h hh
    have hex : ∀ f : SInf F (Fin (b + 2) × Fin (b + 2 + a')),
        ∃ f₁ : SInf F (Fin (b + 2) × Fin (b + 2 + a')), Acts (evI F) (G.M.co.rho B.ψ (partInf F (shiftA H H' l))) f f₁ :=
      fun f => ⟨_, (locOpInf_rho G.M.co hψ _ f).1⟩
    have hT' : IsLinearMap ℂ (G.M.co.rho B.ψ (partInf F (shiftA H H' l))) :=
      ⟨fun f g => funext fun x => mul_add _ _ _, fun c f => funext fun x => mul_left_comm _ _ _⟩
    let R : SInf F (Fin (b + 2) × Fin (b + 2 + a')) →ₗ[ℂ] SInf F (Fin (b + 2) × Fin (b + 2 + a')) :=
      { toFun := locOpInf (G.M.co.rho B.ψ (partInf F (shiftA H H' l)))
        map_add' := fun f g => by simpa using locOpInf_lin hT' hex 1 1 f g
        map_smul' := fun c f => by simpa using locOpInf_lin hT' hex c 0 f 0 }
    have hconj : ∀ c, ∃ t : ℂ, ∀ x, R (D c x) = D c (R x) + t • R x := by
      intro c
      obtain ⟨t, ht⟩ := GlobalTheory.T.schrodinger_translation_operator_shift F _ (coordI G.M (shiftA H H' l)) c.1 c.2
      exact ⟨t, fun x => ht x _ _ (locOpInf_rho G.M.co hψ _ x).2 (locOpInf_rho G.M.co hψ _ _).2⟩
    have hbase : ∀ g ∈ P0, ei (R g) ∈ Q0 := by
      intro g hg
      obtain ⟨c, hc⟩ := GlobalTheory.T.configuration_a_local_evaluation F E σ B b a' G G₁ H H' X om om' hC hT hG e hE ei ev (fun v => (hev v).1) hpe l hl g hg
      change ei (locOpInf _ g) ∈ Q0
      rw [hc]
      exact Q0.smul_mem c (Submodule.mem_map_of_mem (Submodule.subset_span hg))
    exact ev_step D D₁ IA IM P0 Q0 R (ei : SInf F _ →ₗ[ℂ] SInf F _) hconj hkill hint hbase m h
      (words_le D IA IM ID P0 hdec hcomm hvac m (hpolw m hh))
