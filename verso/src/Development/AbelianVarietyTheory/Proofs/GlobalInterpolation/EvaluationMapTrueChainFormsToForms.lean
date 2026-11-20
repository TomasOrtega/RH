import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LowerTieTwAt
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TrueWeightsEqDescentShiftedWeightsInterlaceStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InvTrKEmbGLApply
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.BranchingOk
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `B X I hI l Z l0 u a`. Establish `hW` using `fun τ => GlobalTheory.T.trueWeights_eq_descentShiftedWeights_interlace I hI l Z u a τ`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `swap`. Establish `⟨τ⟩ : Nonempty B.fields.Tau` using `inferInstance`.

Conclude with `(hW τ).2.2.2.2`. Introduce `φ hφ`. Use `set M := I.fm l u a with hM`. Establish `key : ∀ x ∈ (M.lat B.R.m).L, ∃ y, M.ptEmb y = (I.per l u a).lowerMap ((I.per l u a).evz (M.emb B.R.m x))`. Introduce `x hx`.

Take `⟨y, -, hy⟩` from `GlobalTheory.LvT.BuiltChain.exists_image (Q := I.perIn u a) B.fields.emb B.embLL (B.hcW u) GlobalTheory.LvT.BuiltChain.branching_ok (l.ch u a) (l.per u a) (fun τ => (hW τ).2.2.1) (fun τ => (hW τ).2.2.2.1) ((l.fmL u a).fam B.R.m) (l.fmL u a).famP x hx`. Conclude with `⟨y, hy⟩`. Establish `rat : ∀ x, ∃ y, M.ptEmb y = (I.per l u a).lowerMap ((I.per l u a).evz (M.emb B.R.m x))`. Introduce `x`. Establish `hx : x ∈ Submodule.span B.LL ((M.lat B.R.m).L : Set (M.lat B.R.m).V)`.

Rewrite using `[(M.lat_good B.R.m).2.2]`. Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx => exact key x hx`. Consider the case `zero => exact ⟨0, by simp⟩`.

Consider the case `add a b _ _ ha hb`. Take `⟨y, e⟩` from `ha`. Take `⟨z, e'⟩` from `hb`. Conclude with `⟨y + z, by rw [map_add, map_add, map_add, map_add, e, e']⟩`. Consider the case `smul r a _ ha`.

Take `⟨y, e⟩` from `ha`. Use `⟨r • y, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, e, LinearMap.map_smul, LinearMap.map_smul]`. Establish `ptMem : ∀ y, M.ptEmb y ∈ M.ptC`. Introduce `y`.

Rewrite using `[← M.ptEmb_basis.2, ← M.ptLat.b.sum_repr y, map_sum]`. Use `Submodule.sum_mem _ fun a _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.map_smulₛₗ]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)`. Establish `hφ' : φ ∈ M.Fi B.R.m` using `hφ`.

Rewrite `hφ'` using `[← (M.emb_basis B.R.m).2]`. Establish `hle : Submodule.span ℂ (Set.range fun a => M.emb B.R.m ((M.lat B.R.m).b a)) ≤ M.ptC.comap ((I.per l u a).lowerMap ∘ₗ (I.per l u a).evz)`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨b, rfl⟩`. Take `⟨y, e⟩` from `rat ((M.lat B.R.m).b b)`.

Use `show (I.per l u a).lowerMap ((I.per l u a).evz _) ∈ M.ptC`. Rewrite using `[← e]`. Conclude with `ptMem y`. Conclude with `hle hφ'`.
-/
theorem GlobalTheory.PerQ.ptT_forms_built : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word) (a : I.ι), (∀ φ ∈ ((I.tw l l0 Z).fm u a).Fi B.R.m, GlobalTheory.PerQ.PtT (I.rec7 l Z) u a φ ∈ ((I.tw l l0 Z).fm u a).ptC) ∧ ((I.rec7 l Z).fm u).SgInterlace := by
  intro B X I hI l Z l0 u a
  have hW := fun τ => GlobalTheory.T.trueWeights_eq_descentShiftedWeights_interlace I hI l Z u a τ
  refine ⟨?_, ?_⟩
  swap
  · have ⟨τ⟩ : Nonempty B.fields.Tau := inferInstance
    exact (hW τ).2.2.2.2
  intro φ hφ
  set M := I.fm l u a with hM
  have key : ∀ x ∈ (M.lat B.R.m).L, ∃ y, M.ptEmb y =
      (I.per l u a).lowerMap ((I.per l u a).evz (M.emb B.R.m x)) := by
    intro x hx
    obtain ⟨y, -, hy⟩ := GlobalTheory.LvT.BuiltChain.exists_image (Q := I.perIn u a) B.fields.emb B.embLL (B.hcW u)
      GlobalTheory.LvT.BuiltChain.branching_ok (l.ch u a) (l.per u a)
      (fun τ => (hW τ).2.2.1) (fun τ => (hW τ).2.2.2.1) ((l.fmL u a).fam B.R.m) (l.fmL u a).famP x hx
    exact ⟨y, hy⟩
  have rat : ∀ x, ∃ y, M.ptEmb y = (I.per l u a).lowerMap ((I.per l u a).evz (M.emb B.R.m x)) := by
    intro x
    have hx : x ∈ Submodule.span B.LL ((M.lat B.R.m).L : Set (M.lat B.R.m).V) := by
      rw [(M.lat_good B.R.m).2.2]; trivial
    induction hx using Submodule.span_induction with
    | mem x hx => exact key x hx
    | zero => exact ⟨0, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨y, e⟩ := ha
      obtain ⟨z, e'⟩ := hb
      exact ⟨y + z, by rw [map_add, map_add, map_add, map_add, e, e']⟩
    | smul r a _ ha =>
      obtain ⟨y, e⟩ := ha
      refine ⟨r • y, ?_⟩
      rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, e, LinearMap.map_smul, LinearMap.map_smul]
  have ptMem : ∀ y, M.ptEmb y ∈ M.ptC := by
    intro y
    rw [← M.ptEmb_basis.2, ← M.ptLat.b.sum_repr y, map_sum]
    refine Submodule.sum_mem _ fun a _ => ?_
    rw [LinearMap.map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  have hφ' : φ ∈ M.Fi B.R.m := hφ
  rw [← (M.emb_basis B.R.m).2] at hφ'
  have hle : Submodule.span ℂ (Set.range fun a => M.emb B.R.m ((M.lat B.R.m).b a)) ≤
      M.ptC.comap ((I.per l u a).lowerMap ∘ₗ (I.per l u a).evz) := by
    rw [Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    obtain ⟨y, e⟩ := rat ((M.lat B.R.m).b b)
    show (I.per l u a).lowerMap ((I.per l u a).evz _) ∈ M.ptC
    rw [← e]
    exact ptMem y
  exact hle hφ'
