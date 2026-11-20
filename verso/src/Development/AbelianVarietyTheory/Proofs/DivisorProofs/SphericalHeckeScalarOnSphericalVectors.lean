import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Definitions.Divisors.InstCMHostS
import Formalism.LocalToGlobal.IndefiniteReal.PartsRow
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalHeckeCombinationsCommuteFixedVectorsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumTranslatesEqDoubleCosetAverageStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankLeAleph0SmoothIrreducibleUnitaryAdelicStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

noncomputable section

namespace GlobalTheory.SphScalar

open GlobalTheory.SphLabelOps

section Abstract

variable {G M : Type} [Group G] [AddCommGroup M] [Module ℂ M]

/- English proof (translation)
The claim follows from `GlobalTheory.T.sum_translates_eq_doubleCoset_average ρ K s a R w hR hw hm`.
-/
theorem avg (ρ : G →* Module.End ℂ M) (K : Subgroup G) {ι : Type} (s : Finset ι) (a : ι → G) (R : ι → Finset G)
    (w : ι → M)
    (hR : ∀ i ∈ s, (∀ γ ∈ R i, ∃ k₁ ∈ K, ∃ k₂ ∈ K, γ = k₁ * a i * k₂) ∧
      ∀ x : G, (∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * a i * k₂) → ∃! γ, γ ∈ R i ∧ γ⁻¹ * x ∈ K)
    (hw : ∀ i ∈ s, ∀ k ∈ K, ρ k (w i) = w i)
    (hm : ∀ k ∈ K, ρ k (∑ i ∈ s, ρ (a i) (w i)) = ∑ i ∈ s, ρ (a i) (w i)) :
    ∑ i ∈ s, ρ (a i) (w i) = ∑ i ∈ s, ((R i).card : ℂ)⁻¹ • ∑ γ ∈ R i, ρ γ (w i) :=
  GlobalTheory.T.sum_translates_eq_doubleCoset_average ρ K s a R w hR hw hm

def fixS (ρ : G →* Module.End ℂ M) (S : Submodule ℂ M) (K : Subgroup G) : Submodule ℂ M where
  carrier := {x | x ∈ S ∧ ∀ k ∈ K, ρ k x = x}
  add_mem' := fun {x y} hx hy => ⟨S.add_mem hx.1 hy.1, fun k hk => by rw [map_add, hx.2 k hk, hy.2 k hk]⟩
  zero_mem' := ⟨S.zero_mem, fun k _ => map_zero _⟩
  smul_mem' := fun c x hx => ⟨S.smul_mem c hx.1, fun k hk => by rw [map_smul, hx.2 k hk]⟩

/- English proof (translation)
Take `⟨w0, hw0W, hw0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hW0`. Use `le_antisymm hW fun m hm => ?_` and prove the remaining obligations. Use `set O : Submodule ℂ M := Submodule.span ℂ (Set.range fun g => ρ g w0) with hOdef`. Establish `hOS : O ≤ S` using `Submodule.span_le.2 (by rintro _ ⟨g, rfl⟩; exact hS g w0 (hW hw0W).1)`. Establish `hOst : ∀ g, ∀ x ∈ O, ρ g x ∈ O`.

Introduce `g x hx`. Establish `: O.map (ρ g) ≤ O`. Rewrite using `[hOdef, Submodule.map_span_le]`. Introduce and unpack `_ ⟨h, rfl⟩`. Conclude with `Submodule.subset_span ⟨g * h, by show ρ (g * h) w0 = ρ g (ρ h w0); rw [map_mul, Module.End.mul_apply]⟩`.

Conclude with `this (Submodule.mem_map_of_mem hx)`. Establish `hO : O = S`. Break down `hirr O hOS hOst with h | h` into its components or cases. It suffices to derive a contradiction. Apply `hw0` to reduce the goal to its premises.

Establish `: w0 ∈ O` using `Submodule.subset_span ⟨1, by show ρ 1 w0 = w0; rw [map_one, Module.End.one_apply]⟩`. Rewrite `this` using `[h]`. Conclude with `(Submodule.mem_bot ℂ).1 this`. Conclude with `h`. Establish `hmO : m ∈ O` using `hO ▸ hm.1`.

Take `⟨c, hc⟩` from `Finsupp.mem_span_range_iff_exists_finsupp.1 hmO`. Use `choose! aa haa bb hbb hab using hdec`. Establish `key : m = ∑ g ∈ c.support, ρ (aa g) (c g • ρ (bb g) w0)`. Rewrite using `[← hc, Finsupp.sum]`. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations.

Rewrite using `[map_smul, ← Module.End.mul_apply, ← map_mul, ← hab g]`. Establish `hwW : ∀ g, c g • ρ (bb g) w0 ∈ W` using `fun g => W.smul_mem _ (hWb _ (hbb g) _ hw0W)`. Establish `hwK : ∀ g ∈ c.support, ∀ k ∈ K, ρ k (c g • ρ (bb g) w0) = c g • ρ (bb g) w0` using `fun g _ k hk => (hW (hwW g)).2 k hk`. Establish `hmK : ∀ k ∈ K, ρ k (∑ g ∈ c.support, ρ (aa g) (c g • ρ (bb g) w0)) = ∑ g ∈ c.support, ρ (aa g) (c g • ρ (bb g) w0)`. Rewrite using `[← key]`.

Conclude with `hm.2`. Establish `e` using `avg ρ K c.support aa (fun g => R (aa g)) (fun g => c g • ρ (bb g) w0) (fun g _ => hR _ (haa g)) hwK hmK`. Rewrite using `[key, e]`. Conclude with `W.sum_mem fun g _ => W.smul_mem _ (hWR _ (haa g) _ (hwW g))`.
-/
theorem fixS_simple (ρ : G →* Module.End ℂ M) (S : Submodule ℂ M) (hS : ∀ g, ∀ x ∈ S, ρ g x ∈ S)
    (hirr : ∀ S' : Submodule ℂ M, S' ≤ S → (∀ g, ∀ x ∈ S', ρ g x ∈ S') → S' = ⊥ ∨ S' = S)
    (K : Subgroup G) (Loc Away : Set G) (hdec : ∀ g, ∃ a ∈ Loc, ∃ b ∈ Away, g = a * b)
    (R : G → Finset G) (hR : ∀ a ∈ Loc, Reps K a (R a))
    (W : Submodule ℂ M) (hW : W ≤ fixS ρ S K) (hW0 : W ≠ ⊥)
    (hWR : ∀ a ∈ Loc, ∀ x ∈ W, ∑ γ ∈ R a, ρ γ x ∈ W)
    (hWb : ∀ b ∈ Away, ∀ x ∈ W, ρ b x ∈ W) : W = fixS ρ S K := by
  obtain ⟨w0, hw0W, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  refine le_antisymm hW fun m hm => ?_
  set O : Submodule ℂ M := Submodule.span ℂ (Set.range fun g => ρ g w0) with hOdef
  have hOS : O ≤ S := Submodule.span_le.2 (by rintro _ ⟨g, rfl⟩; exact hS g w0 (hW hw0W).1)
  have hOst : ∀ g, ∀ x ∈ O, ρ g x ∈ O := by
    intro g x hx
    have : O.map (ρ g) ≤ O := by
      rw [hOdef, Submodule.map_span_le]
      rintro _ ⟨h, rfl⟩
      exact Submodule.subset_span ⟨g * h, by show ρ (g * h) w0 = ρ g (ρ h w0); rw [map_mul, Module.End.mul_apply]⟩
    exact this (Submodule.mem_map_of_mem hx)
  have hO : O = S := by
    rcases hirr O hOS hOst with h | h
    · exfalso
      apply hw0
      have : w0 ∈ O := Submodule.subset_span ⟨1, by show ρ 1 w0 = w0; rw [map_one, Module.End.one_apply]⟩
      rw [h] at this
      exact (Submodule.mem_bot ℂ).1 this
    · exact h
  have hmO : m ∈ O := hO ▸ hm.1
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hmO
  choose! aa haa bb hbb hab using hdec
  have key : m = ∑ g ∈ c.support, ρ (aa g) (c g • ρ (bb g) w0) := by
    rw [← hc, Finsupp.sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [map_smul, ← Module.End.mul_apply, ← map_mul, ← hab g]
  have hwW : ∀ g, c g • ρ (bb g) w0 ∈ W := fun g => W.smul_mem _ (hWb _ (hbb g) _ hw0W)
  have hwK : ∀ g ∈ c.support, ∀ k ∈ K, ρ k (c g • ρ (bb g) w0) = c g • ρ (bb g) w0 := fun g _ k hk =>
    (hW (hwW g)).2 k hk
  have hmK : ∀ k ∈ K, ρ k (∑ g ∈ c.support, ρ (aa g) (c g • ρ (bb g) w0)) =
      ∑ g ∈ c.support, ρ (aa g) (c g • ρ (bb g) w0) := by
    rw [← key]; exact hm.2
  have e := avg ρ K c.support aa (fun g => R (aa g)) (fun g => c g • ρ (bb g) w0) (fun g _ => hR _ (haa g)) hwK hmK
  rw [key, e]
  exact W.sum_mem fun g _ => W.smul_mem _ (hWR _ (haa g) _ (hwW g))

/- English proof (translation)
Use `set F := fixS ρ S K with hFdef`. Establish `hRF : ∀ a ∈ Loc, ∀ x ∈ F, ∑ γ ∈ R a, ρ γ x ∈ F`. Introduce `a ha x hx`. Use `⟨S.sum_mem fun γ _ => hS γ x hx.1, fun k hk => ?_⟩` and prove the remaining obligations. Rewrite using `[map_sum]`.

Use `(hR a ha).sum_eq (hR a ha) hk (fun g => ρ g x) (fun y l hl => by rw [map_mul, Module.End.mul_apply, hx.2 l hl])` as an intermediate fact. Simplify `this` using `only [map_mul, Module.End.mul_apply]`. Establish `hbF : ∀ b ∈ Away, ∀ x ∈ F, ρ b x ∈ F` using `fun b hb x hx => ⟨hS b x hx.1, fun k hk => by`. Rewrite using `[← Module.End.mul_apply, ← map_mul, hcomm k hk b hb, map_mul, Module.End.mul_apply, hx.2 k hk]⟩`. Establish `stab : ∀ W : Submodule ℂ M, W ≤ F → (∀ a ∈ Loc, ∀ x ∈ W, ∑ γ ∈ R a, ρ γ x ∈ W) → (∀ b ∈ Away, ∀ x ∈ W, ρ b x ∈ W) → W = ⊥ ∨ W = F` using `fun W h1 h2 h3 => by`.

Distinguish the cases in `h0 : W = ⊥`. Conclude with `Or.inl h0`. Conclude with `Or.inr (fixS_simple ρ S hS hirr K Loc Away hdec R hR W h1 h0 h2 h3)`. Establish `hrankF : Module.rank ℂ F ≤ Cardinal.aleph0` using `(Submodule.rank_mono (fun x (hx : x ∈ F) => hx.1)).trans hrank`. Distinguish the cases in `hF : Nontrivial F`.

Use `swap`. Use `⟨0, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite `hF` using `[not_nontrivial_iff_subsingleton]`. Establish `: (⟨x, hx⟩ : F) = 0` using `Subsingleton.elim _ _`. Establish `hx0 : x = 0` using `congrArg Subtype.val this`.

Rewrite using `[hx0, map_zero, smul_zero]`. Set `TF : Module.End ℂ F` to `T.restrict hTS`. Take `⟨c, hc⟩` from `GlobalTheory.LocGL.exists_not_isUnit_sub hrankF TF`. Establish `hTF : ∀ y : F, ((TF - algebraMap ℂ (Module.End ℂ F) c) y : M) = T y - c • (y : M)` using `fun y => rfl`. Use `⟨c, ?_⟩` and prove the remaining obligations.

Set `W1 : Submodule ℂ M` to `{ carrier := {x | x ∈ F ∧ T x = c • x} add_mem' := fun {x y} hx hy => ⟨F.add_mem hx.1 hy.1, by rw [map_add, hx.2, hy.2, smul_add]⟩ zero_mem' := ⟨F.zero_mem, by rw [map_zero, smul_zero]⟩ smul_mem' := fun a x hx => ⟨F.smul_mem a hx.1, by rw [map_smul, hx.2, smul_comm]⟩ }`. Set `W2 : Submodule ℂ M` to `{ carrier := {x | ∃ y ∈ F, x = T y - c • y} add_mem' := by`. Introduce and unpack `_ _ ⟨y, hy, rfl⟩ ⟨y', hy', rfl⟩`. Conclude with `⟨y + y', F.add_mem hy hy', by rw [map_add, smul_add]; abel⟩`. Use the proof step `zero_mem' := ⟨0, F.zero_mem, by rw [map_zero, smul_zero, sub_zero]⟩`.

Use the proof step `smul_mem' := by`. Introduce and unpack `a _ ⟨y, hy, rfl⟩`. Conclude with `⟨a • y, F.smul_mem a hy, by rw [map_smul, smul_sub, smul_comm a c]⟩ }`. Establish `hW1 : W1 = ⊥ ∨ W1 = F`. Use `stab W1 (fun x hx => hx.1) (fun a ha x hx => ⟨hRF a ha x hx.1, ?_⟩) (fun b hb x hx => ⟨hbF b hb x hx.1, ?_⟩)` and prove the remaining obligations.

Rewrite using `[hTR a ha x hx.1, hx.2]`. Simplify using `only [map_smul, Finset.smul_sum]`. Rewrite using `[hTb b hb x hx.1, hx.2, map_smul]`. Break down `hW1 with h1 | h1` into its components or cases. Use `swap`.

Introduce `x hx`. Establish `: x ∈ W1` using `h1 ▸ hx`. Conclude with `this.2`. It suffices to derive a contradiction. Establish `hinj : ∀ y ∈ F, T y - c • y = 0 → y = 0`.

Introduce `y hy e`. Establish `: y ∈ W1` using `⟨hy, sub_eq_zero.1 e⟩`. Rewrite `this` using `[h1]`. Conclude with `(Submodule.mem_bot ℂ).1 this`. Establish `hW2 : W2 = ⊥ ∨ W2 = F`.

Use `stab W2 ?_ ?_ ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `F.sub_mem (hTS y hy) (F.smul_mem c hy)`. Introduce and unpack `a ha _ ⟨y, hy, rfl⟩`. Use `⟨∑ γ ∈ R a, ρ γ y, hRF a ha y hy, ?_⟩` and prove the remaining obligations.

Rewrite using `[hTR a ha y hy]`. Simplify using `only [map_sub, map_smul, Finset.sum_sub_distrib, Finset.smul_sum]`. Introduce and unpack `b hb _ ⟨y, hy, rfl⟩`. Use `⟨ρ b y, hbF b hb y hy, ?_⟩` and prove the remaining obligations. Rewrite using `[hTb b hb y hy, map_sub, map_smul]`.

Apply `hc` to reduce the goal to its premises. Rewrite using `[Module.End.isUnit_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `y y' e`. Establish `e' : ((TF - algebraMap ℂ (Module.End ℂ F) c) (y - y') : M) = 0`.

Rewrite using `[map_sub, e, sub_self]`. Both sides reduce to the same expression. Rewrite `e'` using `[hTF]`. Conclude with `sub_eq_zero.1 (Subtype.ext (hinj _ (y - y').2 e'))`. Introduce `z`.

Break down `hW2 with h2 | h2` into its components or cases. It suffices to derive a contradiction. Take `⟨y, hy⟩` from `exists_ne (0 : F)`. Establish `: (T y - c • (y : M)) ∈ W2` using `⟨y, y.2, rfl⟩`. Rewrite `this` using `[h2]`.

Conclude with `hy (Subtype.ext (hinj _ y.2 ((Submodule.mem_bot ℂ).1 this)))`. Establish `: (z : M) ∈ W2` using `by rw [h2]; exact z.2`. Take `⟨y, hy, e⟩` from `this`. Conclude with `⟨⟨y, hy⟩, Subtype.ext (by rw [hTF]; exact e.symm)⟩`.
-/
theorem abs_scalar (ρ : G →* Module.End ℂ M) (S : Submodule ℂ M) (hS : ∀ g, ∀ x ∈ S, ρ g x ∈ S)
    (hirr : ∀ S' : Submodule ℂ M, S' ≤ S → (∀ g, ∀ x ∈ S', ρ g x ∈ S') → S' = ⊥ ∨ S' = S)
    (hrank : Module.rank ℂ S ≤ Cardinal.aleph0)
    (K : Subgroup G) (Loc Away : Set G) (hdec : ∀ g, ∃ a ∈ Loc, ∃ b ∈ Away, g = a * b)
    (hcomm : ∀ k ∈ K, ∀ b ∈ Away, k * b = b * k)
    (R : G → Finset G) (hR : ∀ a ∈ Loc, Reps K a (R a))
    (T : M →ₗ[ℂ] M)
    (hTS : ∀ x ∈ fixS ρ S K, T x ∈ fixS ρ S K)
    (hTb : ∀ b ∈ Away, ∀ x ∈ fixS ρ S K, T (ρ b x) = ρ b (T x))
    (hTR : ∀ a ∈ Loc, ∀ x ∈ fixS ρ S K, T (∑ γ ∈ R a, ρ γ x) = ∑ γ ∈ R a, ρ γ (T x)) :
    ∃ c : ℂ, ∀ x ∈ fixS ρ S K, T x = c • x := by
  classical
  set F := fixS ρ S K with hFdef
  have hRF : ∀ a ∈ Loc, ∀ x ∈ F, ∑ γ ∈ R a, ρ γ x ∈ F := by
    intro a ha x hx
    refine ⟨S.sum_mem fun γ _ => hS γ x hx.1, fun k hk => ?_⟩
    rw [map_sum]
    have := (hR a ha).sum_eq (hR a ha) hk (fun g => ρ g x)
      (fun y l hl => by rw [map_mul, Module.End.mul_apply, hx.2 l hl])
    simpa only [map_mul, Module.End.mul_apply] using this
  have hbF : ∀ b ∈ Away, ∀ x ∈ F, ρ b x ∈ F := fun b hb x hx =>
    ⟨hS b x hx.1, fun k hk => by
      rw [← Module.End.mul_apply, ← map_mul, hcomm k hk b hb, map_mul, Module.End.mul_apply, hx.2 k hk]⟩
  have stab : ∀ W : Submodule ℂ M, W ≤ F → (∀ a ∈ Loc, ∀ x ∈ W, ∑ γ ∈ R a, ρ γ x ∈ W) →
      (∀ b ∈ Away, ∀ x ∈ W, ρ b x ∈ W) → W = ⊥ ∨ W = F := fun W h1 h2 h3 => by
    by_cases h0 : W = ⊥
    · exact Or.inl h0
    · exact Or.inr (fixS_simple ρ S hS hirr K Loc Away hdec R hR W h1 h0 h2 h3)
  have hrankF : Module.rank ℂ F ≤ Cardinal.aleph0 :=
    (Submodule.rank_mono (fun x (hx : x ∈ F) => hx.1)).trans hrank
  by_cases hF : Nontrivial F
  swap
  · refine ⟨0, fun x hx => ?_⟩
    rw [not_nontrivial_iff_subsingleton] at hF
    have : (⟨x, hx⟩ : F) = 0 := Subsingleton.elim _ _
    have hx0 : x = 0 := congrArg Subtype.val this
    rw [hx0, map_zero, smul_zero]
  let TF : Module.End ℂ F := T.restrict hTS
  obtain ⟨c, hc⟩ := GlobalTheory.LocGL.exists_not_isUnit_sub hrankF TF
  have hTF : ∀ y : F, ((TF - algebraMap ℂ (Module.End ℂ F) c) y : M) = T y - c • (y : M) := fun y => rfl
  refine ⟨c, ?_⟩
  let W1 : Submodule ℂ M :=
    { carrier := {x | x ∈ F ∧ T x = c • x}
      add_mem' := fun {x y} hx hy => ⟨F.add_mem hx.1 hy.1, by rw [map_add, hx.2, hy.2, smul_add]⟩
      zero_mem' := ⟨F.zero_mem, by rw [map_zero, smul_zero]⟩
      smul_mem' := fun a x hx => ⟨F.smul_mem a hx.1, by rw [map_smul, hx.2, smul_comm]⟩ }
  let W2 : Submodule ℂ M :=
    { carrier := {x | ∃ y ∈ F, x = T y - c • y}
      add_mem' := by
        rintro _ _ ⟨y, hy, rfl⟩ ⟨y', hy', rfl⟩
        exact ⟨y + y', F.add_mem hy hy', by rw [map_add, smul_add]; abel⟩
      zero_mem' := ⟨0, F.zero_mem, by rw [map_zero, smul_zero, sub_zero]⟩
      smul_mem' := by
        rintro a _ ⟨y, hy, rfl⟩
        exact ⟨a • y, F.smul_mem a hy, by rw [map_smul, smul_sub, smul_comm a c]⟩ }
  have hW1 : W1 = ⊥ ∨ W1 = F := by
    refine stab W1 (fun x hx => hx.1) (fun a ha x hx => ⟨hRF a ha x hx.1, ?_⟩) (fun b hb x hx => ⟨hbF b hb x hx.1, ?_⟩)
    · rw [hTR a ha x hx.1, hx.2]
      simp only [map_smul, Finset.smul_sum]
    · rw [hTb b hb x hx.1, hx.2, map_smul]
  rcases hW1 with h1 | h1
  swap
  · intro x hx
    have : x ∈ W1 := h1 ▸ hx
    exact this.2
  exfalso
  have hinj : ∀ y ∈ F, T y - c • y = 0 → y = 0 := by
    intro y hy e
    have : y ∈ W1 := ⟨hy, sub_eq_zero.1 e⟩
    rw [h1] at this
    exact (Submodule.mem_bot ℂ).1 this
  have hW2 : W2 = ⊥ ∨ W2 = F := by
    refine stab W2 ?_ ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact F.sub_mem (hTS y hy) (F.smul_mem c hy)
    · rintro a ha _ ⟨y, hy, rfl⟩
      refine ⟨∑ γ ∈ R a, ρ γ y, hRF a ha y hy, ?_⟩
      rw [hTR a ha y hy]
      simp only [map_sub, map_smul, Finset.sum_sub_distrib, Finset.smul_sum]
    · rintro b hb _ ⟨y, hy, rfl⟩
      refine ⟨ρ b y, hbF b hb y hy, ?_⟩
      rw [hTb b hb y hy, map_sub, map_smul]
  apply hc
  rw [Module.End.isUnit_iff]
  constructor
  · intro y y' e
    have e' : ((TF - algebraMap ℂ (Module.End ℂ F) c) (y - y') : M) = 0 := by
      rw [map_sub, e, sub_self]; rfl
    rw [hTF] at e'
    exact sub_eq_zero.1 (Subtype.ext (hinj _ (y - y').2 e'))
  · intro z
    rcases hW2 with h2 | h2
    · exfalso
      obtain ⟨y, hy⟩ := exists_ne (0 : F)
      have : (T y - c • (y : M)) ∈ W2 := ⟨y, y.2, rfl⟩
      rw [h2] at this
      exact hy (Subtype.ext (hinj _ y.2 ((Submodule.mem_bot ℂ).1 this)))
    · have : (z : M) ∈ W2 := by rw [h2]; exact z.2
      obtain ⟨y, hy, e⟩ := this
      exact ⟨⟨y, hy⟩, Subtype.ext (by rw [hTF]; exact e.symm)⟩

end Abstract

section Concrete

variable {D : D7} {V : HSp D} {n : ℕ}

/- English proof (translation)
The claim follows from `GlobalTheory.T.rank_le_aleph0_smooth_irreducible_unitaryAdelic π`.
-/
theorem countRank {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (π : Formalism.L2.NG.FinTyp L n) :
    Module.rank ℂ π.S ≤ Cardinal.aleph0 :=
  GlobalTheory.T.rank_le_aleph0_smooth_irreducible_unitaryAdelic π

def rtHom (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) :
    Formalism.AUTREP.GAf L n →* Module.End ℂ (Formalism.AUTREP.GAf L n → ℂ) where
  toFun h := Formalism.L2.NG.rt L n h
  map_one' := LinearMap.ext fun f => principalLevelFrame.rt_one f
  map_mul' g h := LinearMap.ext fun f => (principalLevelFrame.rt_rt g h f).symm

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem rtHom_apply (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (h : Formalism.AUTREP.GAf L n)
    (f : Formalism.AUTREP.GAf L n → ℂ) : rtHom L n h f = Formalism.L2.NG.rt L n h f := rfl

def rtA (V : HSp D) : GA D V →* Module.End ℂ (GA D V → ℂ) where
  toFun g := { toFun := fun F x => F (x * g), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  map_one' := by ext F x; simp
  map_mul' g h := by ext F x; simp [mul_assoc]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem rtA_apply (V : HSp D) (g : GA D V) (F : GA D V → ℂ) (x : GA D V) : rtA V g F x = F (x * g) := rfl

/- English proof (translation)
Establish `hx : ∃ x, Q.ψ x = Q.ψ h` using `⟨h, rfl⟩`. Unfold `principalLevelFrame.pre`. Rewrite using `[dif_pos hx]`. Conclude with `Q.inj hx.choose_spec`.
-/
theorem pre_psi (Q : principalLevelFrame.RowPsi V n) (h : Formalism.AUTREP.GAf D.host.E n) : principalLevelFrame.pre Q (Q.ψ h) = h := by
  have hx : ∃ x, Q.ψ x = Q.ψ h := ⟨h, rfl⟩
  unfold principalLevelFrame.pre
  rw [dif_pos hx]
  exact Q.inj hx.choose_spec

open Classical in

def ext0 (Q : principalLevelFrame.RowPsi V n) : (Formalism.AUTREP.GAf D.host.E n → ℂ) →ₗ[ℂ] (GA D V → ℂ) where
  toFun x g := if ∃ y, Q.ψ y = g then x (principalLevelFrame.pre Q g) else 0
  map_add' x y := by
    funext g
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c x := by
    funext g
    simp only [Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp

/- English proof (translation)
Simplify using `only [ext0, LinearMap.coe_mk, AddHom.coe_mk]`. Rewrite using `[if_pos ⟨h, rfl⟩, pre_psi]`.
-/
theorem extendByZeroThroughUnitaryFrame_psi (Q : principalLevelFrame.RowPsi V n) (x : Formalism.AUTREP.GAf D.host.E n → ℂ) (h : Formalism.AUTREP.GAf D.host.E n) :
    ext0 Q x (Q.ψ h) = x h := by
  simp only [ext0, LinearMap.coe_mk, AddHom.coe_mk]
  rw [if_pos ⟨h, rfl⟩, pre_psi]

/- English proof (translation)
Use function extensionality and compare the values at `g`. Distinguish the cases in `hg : ∃ y, Q.ψ y = g`. Take `⟨y, rfl⟩` from `hg`. Rewrite using `[rtA_apply, ← map_mul, extendByZeroThroughUnitaryFrame_psi, extendByZeroThroughUnitaryFrame_psi, principalLevelFrame.rt_apply]`. Establish `hg' : ¬ ∃ y, Q.ψ y = g * Q.ψ h` using `fun ⟨y, hy⟩ => hg ⟨y * h⁻¹, by rw [map_mul, hy, map_inv, mul_inv_cancel_right]⟩`.

Rewrite using `[rtA_apply]`. Simplify using `only [ext0, LinearMap.coe_mk, AddHom.coe_mk]`. Rewrite using `[if_neg hg, if_neg hg']`.
-/
theorem extendByZeroThroughUnitaryFrame_right_translate (Q : principalLevelFrame.RowPsi V n) (x : Formalism.AUTREP.GAf D.host.E n → ℂ) (h : Formalism.AUTREP.GAf D.host.E n) :
    ext0 Q (Formalism.L2.NG.rt D.host.E n h x) = rtA V (Q.ψ h) (ext0 Q x) := by
  funext g
  by_cases hg : ∃ y, Q.ψ y = g
  · obtain ⟨y, rfl⟩ := hg
    rw [rtA_apply, ← map_mul, extendByZeroThroughUnitaryFrame_psi, extendByZeroThroughUnitaryFrame_psi, principalLevelFrame.rt_apply]
  · have hg' : ¬ ∃ y, Q.ψ y = g * Q.ψ h := fun ⟨y, hy⟩ =>
      hg ⟨y * h⁻¹, by rw [map_mul, hy, map_inv, mul_inv_cancel_right]⟩
    rw [rtA_apply]
    simp only [ext0, LinearMap.coe_mk, AddHom.coe_mk]
    rw [if_neg hg, if_neg hg']

/- English proof (translation)
The claim follows from `funext fun h => by have := congrFun H (Q.ψ h) rwa [extendByZeroThroughUnitaryFrame_psi, extendByZeroThroughUnitaryFrame_psi] at this`.
-/
theorem extendByZeroThroughUnitaryFrame_injective (Q : principalLevelFrame.RowPsi V n) {x x' : Formalism.AUTREP.GAf D.host.E n → ℂ} (H : ext0 Q x = ext0 Q x') :
    x = x' := funext fun h => by
  have := congrFun H (Q.ψ h)
  rwa [extendByZeroThroughUnitaryFrame_psi, extendByZeroThroughUnitaryFrame_psi] at this

/- English proof (translation)
Unfold `principalLevelFrame.Hecke₃`. Rewrite using `[principalLevelFrame.heckeG_apply, map_sum]`. Use `Finset.sum_congr rfl fun γ hγ => ?_` and prove the remaining obligations. Take `⟨y, rfl⟩` from `hR γ hγ`. Rewrite using `[pre_psi, extendByZeroThroughUnitaryFrame_right_translate]`.
-/
theorem extendByZeroThroughUnitaryFrame_hecke (Q : principalLevelFrame.RowPsi V n) (R : Finset (GA D V)) (hR : ∀ γ ∈ R, ∃ y, Q.ψ y = γ)
    (x : Formalism.AUTREP.GAf D.host.E n → ℂ) :
    ext0 Q (principalLevelFrame.Hecke₃ Q R x) = ∑ γ ∈ R, rtA V γ (ext0 Q x) := by
  unfold principalLevelFrame.Hecke₃
  rw [principalLevelFrame.heckeG_apply, map_sum]
  refine Finset.sum_congr rfl fun γ hγ => ?_
  obtain ⟨y, rfl⟩ := hR γ hγ
  rw [pre_psi, extendByZeroThroughUnitaryFrame_right_translate]

/- English proof (translation)
Unfold `GlobalTheory.Hk3.opOf`. Rewrite using `[Finsupp.sum_single_index (by rw [zero_smul]), one_smul, LinearMap.sum_apply]`.
-/
theorem opOf_single {M : Type} [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (P : Pl D.host.E)
    (d : List ℤ) (u : M) : GlobalTheory.Hk3.opOf π P (Finsupp.single d 1) u = ∑ γ ∈ GlobalTheory.Hk3.rep V P d, π γ u := by
  unfold GlobalTheory.Hk3.opOf
  rw [Finsupp.sum_single_index (by rw [zero_smul]), one_smul, LinearMap.sum_apply]

/- English proof (translation)
Use `⟨fun γ' hγ' => ?_, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨γ, hγ, rfl⟩` from `Finset.mem_image.1 hγ'`. Take `⟨g, rfl⟩` from `hR γ hγ`. Take `⟨k1, hk1, k2, hk2, e⟩` from `h.1 _ hγ`. Take `⟨g1, rfl⟩` from `hK k1 hk1`.

Take `⟨g2, rfl⟩` from `hK k2 hk2`. Use `⟨g1, hk1, g2, hk2, ?_⟩` and prove the remaining obligations. Rewrite using `[hpre]`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[e, map_mul, map_mul]`.

Take `⟨k1, hk1, k2, hk2, rfl⟩` from `hx`. Take `⟨γ, ⟨hγ, hγK⟩, huniq⟩` from `h.2 (ψ k1 * ψ a * ψ k2) ⟨_, hk1, _, hk2, rfl⟩`. Take `⟨g, rfl⟩` from `hR γ hγ`. Use `⟨g, ⟨Finset.mem_image.2 ⟨ψ g, hγ, hpre g⟩, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Subgroup.mem_comap, map_mul, map_inv, map_mul, map_mul]`.

Conclude with `hγK`. Introduce and unpack `g' ⟨hg', hg'K⟩`. Take `⟨γ', hγ', rfl⟩` from `Finset.mem_image.1 hg'`. Take `⟨g'', rfl⟩` from `hR γ' hγ'`. Rewrite `hg'K`, the goal using `[hpre]`.

Rewrite `hg'K` using `[Subgroup.mem_comap, map_mul, map_inv, map_mul, map_mul]`. Conclude with `hinj (huniq (ψ g'') ⟨hγ', hg'K⟩)`.
-/
theorem reps_comap {G H : Type} [Group G] [Group H] [DecidableEq G] (ψ : G →* H) (hinj : Function.Injective ψ)
    (K : Subgroup H) (hK : ∀ k ∈ K, ∃ g, ψ g = k) (pre : H → G) (hpre : ∀ g, pre (ψ g) = g) {a : G}
    {R : Finset H} (hR : ∀ γ ∈ R, ∃ g, ψ g = γ) (h : Reps K (ψ a) R) : Reps (K.comap ψ) a (R.image pre) := by
  refine ⟨fun γ' hγ' => ?_, fun x hx => ?_⟩
  · obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.1 hγ'
    obtain ⟨g, rfl⟩ := hR γ hγ
    obtain ⟨k1, hk1, k2, hk2, e⟩ := h.1 _ hγ
    obtain ⟨g1, rfl⟩ := hK k1 hk1
    obtain ⟨g2, rfl⟩ := hK k2 hk2
    refine ⟨g1, hk1, g2, hk2, ?_⟩
    rw [hpre]
    apply hinj
    rw [e, map_mul, map_mul]
  · obtain ⟨k1, hk1, k2, hk2, rfl⟩ := hx
    obtain ⟨γ, ⟨hγ, hγK⟩, huniq⟩ := h.2 (ψ k1 * ψ a * ψ k2) ⟨_, hk1, _, hk2, rfl⟩
    obtain ⟨g, rfl⟩ := hR γ hγ
    refine ⟨g, ⟨Finset.mem_image.2 ⟨ψ g, hγ, hpre g⟩, ?_⟩, ?_⟩
    · rw [Subgroup.mem_comap, map_mul, map_inv, map_mul, map_mul]
      exact hγK
    · rintro g' ⟨hg', hg'K⟩
      obtain ⟨γ', hγ', rfl⟩ := Finset.mem_image.1 hg'
      obtain ⟨g'', rfl⟩ := hR γ' hγ'
      rw [hpre] at hg'K ⊢
      rw [Subgroup.mem_comap, map_mul, map_inv, map_mul, map_mul] at hg'K
      exact hinj (huniq (ψ g'') ⟨hγ', hg'K⟩)

/- English proof (translation)
Take `⟨e', f', ϖ, α, -, h', -, -, -, -, -, -, -, hs, hc⟩` from `hR`. Take `⟨-, rfl⟩` from `((GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).2.2.1 P e f hef).2.2.2.1 e' f' h'`. Establish `hK' : {k | k ∈ KsphC V ∅ ∧ SuppF V f' k} = (Kv : Set (GA D V))` using `(GlobalTheory.SphLabelOps.hyp_eq hef).symm.trans hK`. Rewrite `hc` using `[IsCosetRep, hK']`. Conclude with `⟨fun γ hγ => ⟨(hc.1 γ hγ).1, hs γ hγ⟩, α, fun γ hγ => (hc.1 γ hγ).2, hc.2⟩`.
-/
theorem sphOp_facts {P : HeightOneSpectrum (𝓞 D.host.E)} {e f : AE D} {Kv : Subgroup (GA D V)} {d : List ℤ}
    {R : Finset (GA D V)} (hef : IsPrimeIdem P e f) (hK : hyp V P = Kv) (hR : SphOp V P d R) :
    (∀ γ ∈ R, γ ∈ GfC V ∧ SuppF V f γ) ∧ ∃ α, Reps Kv α R := by
  obtain ⟨e', f', ϖ, α, -, h', -, -, -, -, -, -, -, hs, hc⟩ := hR
  obtain ⟨-, rfl⟩ := ((GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).2.2.1 P e f hef).2.2.2.1 e' f' h'
  have hK' : {k | k ∈ KsphC V ∅ ∧ SuppF V f' k} = (Kv : Set (GA D V)) := (GlobalTheory.SphLabelOps.hyp_eq hef).symm.trans hK
  rw [IsCosetRep, hK'] at hc
  exact ⟨fun γ hγ => ⟨(hc.1 γ hγ).1, hs γ hγ⟩, α, fun γ hγ => (hc.1 γ hγ).2, hc.2⟩

end Concrete

section Main

open GlobalTheory.IdemSupport

/- English proof (translation)
Introduce `D V n hF Q _ π Pr d B hB`. Establish `SG` using `supported_group_and_prime_idempotents V`. Take `⟨Kv, hKv⟩` from `GlobalTheory.SphLabelOps.exists_hyp V Pr`. Take `⟨e, f, hef⟩` from `SG.2.1 Pr`. Take `⟨hff, hcf, hfG, -, -⟩` from `SG.2.2.1 Pr e f hef`.

Take `⟨-, hsplit, hcomm0⟩` from `SG.1 f hff hcf`. Establish `hf0 : f * (1 - f) = 0` using `by rw [mul_sub, mul_one, hff, sub_self]`. Establish `hKvG : ∀ k ∈ Kv, k ∈ GfC V` using `fun k hk => by`. Establish `: k ∈ hyp V Pr` using `by rw [hKv]; exact hk`. Conclude with `this.1.1`.

Establish `hKvS : ∀ k ∈ Kv, SuppF V f k` using `fun k hk => by`. Establish `: k ∈ hyp V Pr` using `by rw [hKv]; exact hk`. Rewrite `this` using `[GlobalTheory.SphLabelOps.hyp_eq hef]`. Conclude with `this.2`. Establish `hon : ∀ g ∈ GfC V, ∃ y, Q.ψ y = g` using `fun g hg => Q.onto g hg`.

Set `K : Subgroup (Formalism.AUTREP.GAf D.host.E n)` to `Kv.comap Q.ψ`. Set `Loc : Set (Formalism.AUTREP.GAf D.host.E n)` to `{h | SuppF V f (Q.ψ h)}`. Set `Away : Set (Formalism.AUTREP.GAf D.host.E n)` to `{h | SuppF V (1 - f) (Q.ψ h)}`. Establish `hdec : ∀ g, ∃ a ∈ Loc, ∃ b ∈ Away, g = a * b`. Introduce `g`.

Take `⟨g1, g2, h1, h2, hg⟩` from `hsplit (Q.ψ g)`. Take `⟨a, rfl⟩` from `hon g1 (hfG g1 h1)`. Establish `hg2 : g2 ∈ GfC V`. Establish `: g2 = (Q.ψ a)⁻¹ * Q.ψ g` using `by rw [hg, inv_mul_cancel_left]`. Rewrite using `[this]`.

Conclude with `(GfC V).mul_mem ((GfC V).inv_mem (Q.into a)) (Q.into g)`. Take `⟨b, rfl⟩` from `hon g2 hg2`. Conclude with `⟨a, h1, b, h2, Q.inj (by rw [hg, map_mul])⟩`. Establish `hcomm : ∀ k ∈ K, ∀ b ∈ Away, k * b = b * k` using `fun k hk b hb => Q.inj (by rw [map_mul, map_mul]; exact (hcomm0 (1 - f) _ _ hf0 (hKvS _ hk) hb).eq)`. Establish `hlab : ∀ a ∈ Loc, ∃ dd, IsLab V Pr dd ∧ ∀ γ ∈ GlobalTheory.Hk3.rep V Pr dd, ∃ k₁ ∈ hyp V Pr, ∃ k₂ ∈ hyp V Pr, γ = k₁ * Q.ψ a * k₂` using `fun a ha => by`.

Take `⟨dd, h1, h2, -⟩` from `(GlobalTheory.SphLabelOps.label_operators V Pr).2.2.2.2 e f (Q.ψ a) hef ha`. Conclude with `⟨dd, h1, h2⟩`. Use `choose! dd hdd1 hdd2 using hlab`. Establish `hsph : ∀ a ∈ Loc, SphOp V Pr (dd a) (GlobalTheory.Hk3.rep V Pr (dd a))` using `fun a ha => by`. Establish `h` using `hdd1 a ha`.

Unfold `GlobalTheory.Hk3.rep`. Rewrite using `[dif_pos h]`. Conclude with `h.choose_spec`. Establish `hrepG : ∀ a ∈ Loc, ∀ γ ∈ GlobalTheory.Hk3.rep V Pr (dd a), ∃ y, Q.ψ y = γ` using `fun a ha γ hγ => hon γ ((sphOp_facts hef hKv (hsph a ha)).1 γ hγ).1`. Establish `hrepsV : ∀ a ∈ Loc, Reps Kv (Q.ψ a) (GlobalTheory.Hk3.rep V Pr (dd a))`.

Introduce `a ha`. Take `⟨-, α, hα⟩` from `sphOp_facts hef hKv (hsph a ha)`. Take `⟨γ0, ⟨hγ0, -⟩, -⟩` from `hα.2 α ⟨1, one_mem _, 1, one_mem _, by group⟩`. Take `⟨k1, hk1, k2, hk2, e1⟩` from `hα.1 γ0 hγ0`. Take `⟨k1', hk1', k2', hk2', e2⟩` from `hdd2 a ha γ0 hγ0`.

Rewrite `hk1'`, `hk2'` using `[hKv]`. Establish `hαe : α = (k1⁻¹ * k1') * Q.ψ a * (k2' * k2⁻¹)`. Rewrite `e2` using `[e1]`. Combine the equalities or inequalities in the displayed calculation. Rewrite `hα` using `[hαe]`.

Conclude with `Reps.of_dc (mul_mem (inv_mem hk1) hk1') (mul_mem hk2' (inv_mem hk2)) hα`. Set `R : Formalism.AUTREP.GAf D.host.E n → Finset (Formalism.AUTREP.GAf D.host.E n)` to `fun a => (GlobalTheory.Hk3.rep V Pr (dd a)).image (principalLevelFrame.pre Q)`. Establish `hR : ∀ a ∈ Loc, Reps K a (R a)` using `fun a ha => reps_comap Q.ψ Q.inj Kv (fun k hk => hon k (hKvG k hk)) (principalLevelFrame.pre Q) (pre_psi Q) (hrepG a ha) (hrepsV a ha)`. Establish `hsumR : ∀ a ∈ Loc, ∀ x : Formalism.AUTREP.GAf D.host.E n → ℂ, ∑ γ ∈ R a, rtHom D.host.E n γ x = principalLevelFrame.Hecke₃ Q (GlobalTheory.Hk3.rep V Pr (dd a)) x`. Introduce `a ha x`.

Unfold `principalLevelFrame.Hecke₃`. Rewrite using `[principalLevelFrame.heckeG_apply, Finset.sum_image]`. Both sides reduce to the same expression. Introduce `γ hγ γ' hγ' e`. Take `⟨y, rfl⟩` from `hrepG a ha γ hγ`.

Take `⟨y', rfl⟩` from `hrepG a ha γ' hγ'`. Rewrite `e` using `[pre_psi, pre_psi]`. Rewrite using `[e]`. Take `⟨hBG, -⟩` from `sphOp_facts hef hKv hB`. Establish `hBr : ∀ γ ∈ B, ∃ y, Q.ψ y = γ` using `fun γ hγ => hon γ (hBG γ hγ).1`.

Establish `hfixA : ∀ x : Formalism.AUTREP.GAf D.host.E n → ℂ, (∀ k ∈ K, rtHom D.host.E n k x = x) → ∀ k ∈ hyp V Pr, rtA V k (ext0 Q x) = ext0 Q x`. Introduce `x hx k hk`. Establish `hk' : k ∈ Kv` using `by rw [hKv] at hk; exact hk`. Take `⟨κ, rfl⟩` from `hon k (hKvG k hk')`. Rewrite using `[← extendByZeroThroughUnitaryFrame_right_translate]`.

Conclude with `congrArg _ (hx κ hk')`. Establish `hfixBack : ∀ x : Formalism.AUTREP.GAf D.host.E n → ℂ, (∀ k ∈ hyp V Pr, rtA V k (ext0 Q x) = ext0 Q x) → ∀ k ∈ K, rtHom D.host.E n k x = x`. Introduce `x hx k hk`. Apply `extendByZeroThroughUnitaryFrame_injective Q` to reduce the goal to its premises. Rewrite using `[rtHom_apply, extendByZeroThroughUnitaryFrame_right_translate]`.

Conclude with `hx _ (by rw [hKv]; exact hk)`. Establish `hBop : ∀ x : Formalism.AUTREP.GAf D.host.E n → ℂ, (∀ k ∈ K, rtHom D.host.E n k x = x) → ext0 Q (principalLevelFrame.Hecke₃ Q B x) = GlobalTheory.Hk3.opOf (rtA V) Pr (Finsupp.single d 1) (ext0 Q x)`. Introduce `x hx`. Rewrite using `[extendByZeroThroughUnitaryFrame_hecke Q B hBr]`. Conclude with `((GlobalTheory.SphLabelOps.label_operators V Pr).1 d B hB).2 _ (rtA V) _ (hfixA x hx)`.

Establish `hRop : ∀ a ∈ Loc, ∀ x : Formalism.AUTREP.GAf D.host.E n → ℂ, ext0 Q (principalLevelFrame.Hecke₃ Q (GlobalTheory.Hk3.rep V Pr (dd a)) x) = GlobalTheory.Hk3.opOf (rtA V) Pr (Finsupp.single (dd a) 1) (ext0 Q x)`. Introduce `a ha x`. Rewrite using `[extendByZeroThroughUnitaryFrame_hecke Q _ (hrepG a ha), opOf_single]`. Establish `hopfix : ∀ c, ∀ x : Formalism.AUTREP.GAf D.host.E n → ℂ, (∀ k ∈ K, rtHom D.host.E n k x = x) → ∀ k ∈ hyp V Pr, rtA V k (GlobalTheory.Hk3.opOf (rtA V) Pr c (ext0 Q x)) = GlobalTheory.Hk3.opOf (rtA V) Pr c (ext0 Q x)` using `fun c x hx => (GlobalTheory.SphLabelOps.label_operators V Pr).2.1 c _ (rtA V) _ (hfixA x hx)`. Establish `hTB : ∀ x : Formalism.AUTREP.GAf D.host.E n → ℂ, principalLevelFrame.Hecke₃ Q B x = ∑ γ ∈ B, rtHom D.host.E n (principalLevelFrame.pre Q γ) x`.

Introduce `x`. Unfold `principalLevelFrame.Hecke₃`. Rewrite using `[principalLevelFrame.heckeG_apply]`. Both sides reduce to the same expression. Choose the witnesses or unpack the hypotheses as in `⟨c, hc⟩ : ∃ c : ℂ, ∀ x ∈ fixS (rtHom D.host.E n) π.S K, principalLevelFrame.Hecke₃ Q B x = c • x := by`.

Use `abs_scalar (rtHom D.host.E n) π.S (fun g x hx => π.stable g x hx) π.irr (countRank π) K Loc Away hdec hcomm R hR (principalLevelFrame.Hecke₃ Q B) ?_ ?_ ?_` and prove the remaining obligations. Introduce `x hx`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hTB]`. Conclude with `π.S.sum_mem fun γ _ => π.stable _ x hx.1`.

Apply `hfixBack` to reduce the goal to its premises. Rewrite using `[hBop x hx.2]`. Conclude with `hopfix _ x hx.2`. Introduce `b hb x _`. Rewrite using `[hTB, hTB, map_sum]`.

Use `Finset.sum_congr rfl fun γ hγ => ?_` and prove the remaining obligations. Rewrite using `[← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]`. Use `congr 2`. Take `⟨y, rfl⟩` from `hBr γ hγ`. Rewrite using `[pre_psi]`.

Conclude with `Q.inj (by rw [map_mul, map_mul]; exact (hcomm0 (1 - f) _ _ hf0 (hBG _ hγ).2 hb).eq)`. Introduce `a ha x hx`. Rewrite using `[hsumR a ha, hsumR a ha]`. Apply `extendByZeroThroughUnitaryFrame_injective Q` to reduce the goal to its premises. Establish `hx' : ∀ k ∈ K, rtHom D.host.E n k (principalLevelFrame.Hecke₃ Q (GlobalTheory.Hk3.rep V Pr (dd a)) x) = principalLevelFrame.Hecke₃ Q (GlobalTheory.Hk3.rep V Pr (dd a)) x`.

Apply `hfixBack` to reduce the goal to its premises. Rewrite using `[hRop a ha]`. Conclude with `hopfix _ x hx.2`. Establish `hx'' : ∀ k ∈ K, rtHom D.host.E n k (principalLevelFrame.Hecke₃ Q B x) = principalLevelFrame.Hecke₃ Q B x`. Apply `hfixBack` to reduce the goal to its premises.

Rewrite using `[hBop x hx.2]`. Conclude with `hopfix _ x hx.2`. Rewrite using `[hBop _ hx', hRop a ha, hRop a ha, hBop x hx.2]`. Conclude with `GlobalTheory.T.sphericalHeckeCombinations_commute_fixedVectors V Pr _ _ _ (rtA V) _ (hfixA x hx.2)`. Conclude with `⟨c, fun x hx hfx => hc x ⟨hx, fun k hk => hfx k (by rw [hKv]; exact hk)⟩⟩`.
-/
theorem spherical_scalar : ∀ {D : D7} {V : HSp D} {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E)
    (Q : principalLevelFrame.RowPsi V n), StdPsi hF Q → ∀ (π : Formalism.L2.NG.FinTyp D.host.E n) Pr d B, SphOp V Pr d B →
      ∃ a : ℂ, ∀ x ∈ π.S, (∀ κ, Q.ψ κ ∈ hyp V Pr → Formalism.L2.NG.rt D.host.E n κ x = x) →
        principalLevelFrame.Hecke₃ Q B x = a • x := by
  intro D V n hF Q _ π Pr d B hB
  classical
  have SG := supported_group_and_prime_idempotents V
  obtain ⟨Kv, hKv⟩ := GlobalTheory.SphLabelOps.exists_hyp V Pr
  obtain ⟨e, f, hef⟩ := SG.2.1 Pr
  obtain ⟨hff, hcf, hfG, -, -⟩ := SG.2.2.1 Pr e f hef
  obtain ⟨-, hsplit, hcomm0⟩ := SG.1 f hff hcf
  have hf0 : f * (1 - f) = 0 := by rw [mul_sub, mul_one, hff, sub_self]
  have hKvG : ∀ k ∈ Kv, k ∈ GfC V := fun k hk => by
    have : k ∈ hyp V Pr := by rw [hKv]; exact hk
    exact this.1.1
  have hKvS : ∀ k ∈ Kv, SuppF V f k := fun k hk => by
    have : k ∈ hyp V Pr := by rw [hKv]; exact hk
    rw [GlobalTheory.SphLabelOps.hyp_eq hef] at this
    exact this.2
  have hon : ∀ g ∈ GfC V, ∃ y, Q.ψ y = g := fun g hg => Q.onto g hg
  let K : Subgroup (Formalism.AUTREP.GAf D.host.E n) := Kv.comap Q.ψ
  let Loc : Set (Formalism.AUTREP.GAf D.host.E n) := {h | SuppF V f (Q.ψ h)}
  let Away : Set (Formalism.AUTREP.GAf D.host.E n) := {h | SuppF V (1 - f) (Q.ψ h)}
  have hdec : ∀ g, ∃ a ∈ Loc, ∃ b ∈ Away, g = a * b := by
    intro g
    obtain ⟨g1, g2, h1, h2, hg⟩ := hsplit (Q.ψ g)
    obtain ⟨a, rfl⟩ := hon g1 (hfG g1 h1)
    have hg2 : g2 ∈ GfC V := by
      have : g2 = (Q.ψ a)⁻¹ * Q.ψ g := by rw [hg, inv_mul_cancel_left]
      rw [this]
      exact (GfC V).mul_mem ((GfC V).inv_mem (Q.into a)) (Q.into g)
    obtain ⟨b, rfl⟩ := hon g2 hg2
    exact ⟨a, h1, b, h2, Q.inj (by rw [hg, map_mul])⟩
  have hcomm : ∀ k ∈ K, ∀ b ∈ Away, k * b = b * k := fun k hk b hb =>
    Q.inj (by rw [map_mul, map_mul]; exact (hcomm0 (1 - f) _ _ hf0 (hKvS _ hk) hb).eq)

  have hlab : ∀ a ∈ Loc, ∃ dd, IsLab V Pr dd ∧
      ∀ γ ∈ GlobalTheory.Hk3.rep V Pr dd, ∃ k₁ ∈ hyp V Pr, ∃ k₂ ∈ hyp V Pr, γ = k₁ * Q.ψ a * k₂ := fun a ha => by
    obtain ⟨dd, h1, h2, -⟩ := (GlobalTheory.SphLabelOps.label_operators V Pr).2.2.2.2 e f (Q.ψ a) hef ha
    exact ⟨dd, h1, h2⟩
  choose! dd hdd1 hdd2 using hlab
  have hsph : ∀ a ∈ Loc, SphOp V Pr (dd a) (GlobalTheory.Hk3.rep V Pr (dd a)) := fun a ha => by
    have h := hdd1 a ha
    unfold GlobalTheory.Hk3.rep
    rw [dif_pos h]
    exact h.choose_spec
  have hrepG : ∀ a ∈ Loc, ∀ γ ∈ GlobalTheory.Hk3.rep V Pr (dd a), ∃ y, Q.ψ y = γ := fun a ha γ hγ =>
    hon γ ((sphOp_facts hef hKv (hsph a ha)).1 γ hγ).1
  have hrepsV : ∀ a ∈ Loc, Reps Kv (Q.ψ a) (GlobalTheory.Hk3.rep V Pr (dd a)) := by
    intro a ha
    obtain ⟨-, α, hα⟩ := sphOp_facts hef hKv (hsph a ha)
    obtain ⟨γ0, ⟨hγ0, -⟩, -⟩ := hα.2 α ⟨1, one_mem _, 1, one_mem _, by group⟩
    obtain ⟨k1, hk1, k2, hk2, e1⟩ := hα.1 γ0 hγ0
    obtain ⟨k1', hk1', k2', hk2', e2⟩ := hdd2 a ha γ0 hγ0
    rw [hKv] at hk1' hk2'
    have hαe : α = (k1⁻¹ * k1') * Q.ψ a * (k2' * k2⁻¹) := by
      rw [e1] at e2
      calc α = k1⁻¹ * (k1 * α * k2) * k2⁻¹ := by group
        _ = _ := by rw [e2]; group
    rw [hαe] at hα
    exact Reps.of_dc (mul_mem (inv_mem hk1) hk1') (mul_mem hk2' (inv_mem hk2)) hα
  let R : Formalism.AUTREP.GAf D.host.E n → Finset (Formalism.AUTREP.GAf D.host.E n) :=
    fun a => (GlobalTheory.Hk3.rep V Pr (dd a)).image (principalLevelFrame.pre Q)
  have hR : ∀ a ∈ Loc, Reps K a (R a) := fun a ha =>
    reps_comap Q.ψ Q.inj Kv (fun k hk => hon k (hKvG k hk)) (principalLevelFrame.pre Q) (pre_psi Q) (hrepG a ha) (hrepsV a ha)
  have hsumR : ∀ a ∈ Loc, ∀ x : Formalism.AUTREP.GAf D.host.E n → ℂ,
      ∑ γ ∈ R a, rtHom D.host.E n γ x = principalLevelFrame.Hecke₃ Q (GlobalTheory.Hk3.rep V Pr (dd a)) x := by
    intro a ha x
    unfold principalLevelFrame.Hecke₃
    rw [principalLevelFrame.heckeG_apply, Finset.sum_image]
    · rfl
    · intro γ hγ γ' hγ' e
      obtain ⟨y, rfl⟩ := hrepG a ha γ hγ
      obtain ⟨y', rfl⟩ := hrepG a ha γ' hγ'
      rw [pre_psi, pre_psi] at e
      rw [e]

  obtain ⟨hBG, -⟩ := sphOp_facts hef hKv hB
  have hBr : ∀ γ ∈ B, ∃ y, Q.ψ y = γ := fun γ hγ => hon γ (hBG γ hγ).1

  have hfixA : ∀ x : Formalism.AUTREP.GAf D.host.E n → ℂ, (∀ k ∈ K, rtHom D.host.E n k x = x) →
      ∀ k ∈ hyp V Pr, rtA V k (ext0 Q x) = ext0 Q x := by
    intro x hx k hk
    have hk' : k ∈ Kv := by rw [hKv] at hk; exact hk
    obtain ⟨κ, rfl⟩ := hon k (hKvG k hk')
    rw [← extendByZeroThroughUnitaryFrame_right_translate]
    exact congrArg _ (hx κ hk')
  have hfixBack : ∀ x : Formalism.AUTREP.GAf D.host.E n → ℂ, (∀ k ∈ hyp V Pr, rtA V k (ext0 Q x) = ext0 Q x) →
      ∀ k ∈ K, rtHom D.host.E n k x = x := by
    intro x hx k hk
    apply extendByZeroThroughUnitaryFrame_injective Q
    rw [rtHom_apply, extendByZeroThroughUnitaryFrame_right_translate]
    exact hx _ (by rw [hKv]; exact hk)
  have hBop : ∀ x : Formalism.AUTREP.GAf D.host.E n → ℂ, (∀ k ∈ K, rtHom D.host.E n k x = x) →
      ext0 Q (principalLevelFrame.Hecke₃ Q B x) = GlobalTheory.Hk3.opOf (rtA V) Pr (Finsupp.single d 1) (ext0 Q x) := by
    intro x hx
    rw [extendByZeroThroughUnitaryFrame_hecke Q B hBr]
    exact ((GlobalTheory.SphLabelOps.label_operators V Pr).1 d B hB).2 _ (rtA V) _ (hfixA x hx)
  have hRop : ∀ a ∈ Loc, ∀ x : Formalism.AUTREP.GAf D.host.E n → ℂ,
      ext0 Q (principalLevelFrame.Hecke₃ Q (GlobalTheory.Hk3.rep V Pr (dd a)) x) =
        GlobalTheory.Hk3.opOf (rtA V) Pr (Finsupp.single (dd a) 1) (ext0 Q x) := by
    intro a ha x
    rw [extendByZeroThroughUnitaryFrame_hecke Q _ (hrepG a ha), opOf_single]
  have hopfix : ∀ c, ∀ x : Formalism.AUTREP.GAf D.host.E n → ℂ, (∀ k ∈ K, rtHom D.host.E n k x = x) →
      ∀ k ∈ hyp V Pr, rtA V k (GlobalTheory.Hk3.opOf (rtA V) Pr c (ext0 Q x)) = GlobalTheory.Hk3.opOf (rtA V) Pr c (ext0 Q x) :=
    fun c x hx => (GlobalTheory.SphLabelOps.label_operators V Pr).2.1 c _ (rtA V) _ (hfixA x hx)

  have hTB : ∀ x : Formalism.AUTREP.GAf D.host.E n → ℂ, principalLevelFrame.Hecke₃ Q B x = ∑ γ ∈ B, rtHom D.host.E n (principalLevelFrame.pre Q γ) x := by
    intro x
    unfold principalLevelFrame.Hecke₃
    rw [principalLevelFrame.heckeG_apply]
    rfl
  obtain ⟨c, hc⟩ : ∃ c : ℂ, ∀ x ∈ fixS (rtHom D.host.E n) π.S K, principalLevelFrame.Hecke₃ Q B x = c • x := by
    refine abs_scalar (rtHom D.host.E n) π.S (fun g x hx => π.stable g x hx) π.irr (countRank π)
      K Loc Away hdec hcomm R hR (principalLevelFrame.Hecke₃ Q B) ?_ ?_ ?_
    ·
      intro x hx
      refine ⟨?_, ?_⟩
      · rw [hTB]
        exact π.S.sum_mem fun γ _ => π.stable _ x hx.1
      · apply hfixBack
        rw [hBop x hx.2]
        exact hopfix _ x hx.2
    ·
      intro b hb x _
      rw [hTB, hTB, map_sum]
      refine Finset.sum_congr rfl fun γ hγ => ?_
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2
      obtain ⟨y, rfl⟩ := hBr γ hγ
      rw [pre_psi]
      exact Q.inj (by rw [map_mul, map_mul]; exact (hcomm0 (1 - f) _ _ hf0 (hBG _ hγ).2 hb).eq)
    ·
      intro a ha x hx
      rw [hsumR a ha, hsumR a ha]
      apply extendByZeroThroughUnitaryFrame_injective Q
      have hx' : ∀ k ∈ K, rtHom D.host.E n k (principalLevelFrame.Hecke₃ Q (GlobalTheory.Hk3.rep V Pr (dd a)) x) =
          principalLevelFrame.Hecke₃ Q (GlobalTheory.Hk3.rep V Pr (dd a)) x := by
        apply hfixBack
        rw [hRop a ha]
        exact hopfix _ x hx.2
      have hx'' : ∀ k ∈ K, rtHom D.host.E n k (principalLevelFrame.Hecke₃ Q B x) = principalLevelFrame.Hecke₃ Q B x := by
        apply hfixBack
        rw [hBop x hx.2]
        exact hopfix _ x hx.2
      rw [hBop _ hx', hRop a ha, hRop a ha, hBop x hx.2]
      exact GlobalTheory.T.sphericalHeckeCombinations_commute_fixedVectors V Pr _ _ _ (rtA V) _ (hfixA x hx.2)

  exact ⟨c, fun x hx hfx => hc x ⟨hx, fun k hk => hfx k (by rw [hKv]; exact hk)⟩⟩

end Main

end GlobalTheory.SphScalar

end
