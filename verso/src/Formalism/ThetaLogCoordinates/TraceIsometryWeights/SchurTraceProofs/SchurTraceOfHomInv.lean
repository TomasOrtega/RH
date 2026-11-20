import Formalism.ThetaLogCoordinates.TraceIsometryWeights.StatementB
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.HomRelationHolds

namespace Formalism.InvariantFactorPaths.PW

open Finset Formalism.GM.DimensionMonotonicity

section gen

variable {K V V₁ V₂ : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup V₁] [Module K V₁]
  [AddCommGroup V₂] [Module K V₂] {n : ℕ}

/- English proof (translation)
Introduce `a b c d`. Use extensionality with `x`. Establish `h` using `G.comm a b c d x`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply]`. Rewrite using `[h]`.

Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem glRel_of (G : GlW K V n) : GlRel G.E := by
  intro a b c d
  ext x
  have h := G.comm a b c d x
  simp only [LinearMap.sub_apply, Module.End.mul_apply]
  rw [h]
  split_ifs <;> simp

def mapsInto (V₁ : Type) [AddCommGroup V₁] [Module K V₁] (W : Submodule K V₂) : Submodule K (V₁ →ₗ[K] V₂) where
  carrier := {φ | ∀ x, φ x ∈ W}
  add_mem' := fun {φ ψ} hφ hψ x => by rw [LinearMap.add_apply]; exact W.add_mem (hφ x) (hψ x)
  zero_mem' := fun x => by rw [LinearMap.zero_apply]; exact W.zero_mem
  smul_mem' := fun c φ hφ x => by rw [LinearMap.smul_apply]; exact W.smul_mem c (hφ x)

/- English proof (translation)
Establish `key : ∀ μ x, φ (G₁.comp μ x) = 0`. Introduce `μ x`. Assume the negation of the conclusion as `hy`. Establish `hx' : G₁.comp μ x ≠ 0` using `fun h => hy (by rw [h, map_zero])`. Establish `hE : G₂.E z z (φ (G₁.comp μ x)) = ((k + μ z : ℤ) : K) • φ (G₁.comp μ x)`.

Establish `h` using `congrArg (fun ψ : V₁ →ₗ[K] V₂ => ψ (G₁.comp μ x)) he`. Simplify using `only [homAct_apply, LinearMap.smul_apply] at h`. Rewrite `h` using `[G₁.diag, map_smul]`. Rewrite using `[Int.cast_add, add_smul, ← h]`. Normalize the expressions using the abelian group laws.

Establish `hc : ∀ ν, G₂.comp ν (φ (G₁.comp μ x)) = 0`. Introduce `ν`. Assume the negation of the conclusion as `hν`. Establish `e1` using `G₂.comp_Ecc ν z (φ (G₁.comp μ x))`. Rewrite `e1` using `[hE, map_smul]`.

Establish `e2 : (((k + μ z : ℤ) : K) - ((ν z : ℤ) : K)) • G₂.comp ν (φ (G₁.comp μ x)) = 0`. Rewrite using `[sub_smul, e1, sub_self]`. Break down `smul_eq_zero.mp e2 with h | h` into its components or cases. Establish `h3 : k + μ z = ν z` using `by exact_mod_cast sub_eq_zero.mp h`. Establish `h4` using `hb μ ν (G₁.comp μ x) _ hx' hν (G₂.graded_of hW ν _ (hφ _)) (G₁.isWt_comp μ x) (G₂.isWt_comp ν _) z`.

Rewrite `h4` using `[← h3, add_sub_cancel_right]`. Use linear arithmetic over natural numbers and integers. Conclude with `hν h`. Apply `hy` to reduce the goal to its premises. Establish `h` using `G₂.sum_comp (φ (G₁.comp μ x)) ∅ (fun ν _ => hc ν)`.

Simplify using `using h.symm`. Use extensionality with `x`. Take `⟨S, hS⟩` from `G₁.dec x`. Rewrite using `[← G₁.sum_comp x S hS, map_sum, LinearMap.zero_apply]`. Conclude with `Finset.sum_eq_zero fun μ _ => key μ x`.
-/
theorem hom_eig_zero [CharZero K] (G₁ : GlW K V₁ n) (G₂ : GlW K V₂ n) (W : Submodule K V₂) (l : ℕ)
    (hW : G₂.Stable W) (hb : WtBound2 G₁ G₂ W l) (z : Fin n) (k : ℤ) (φ : V₁ →ₗ[K] V₂) (hφ : ∀ x, φ x ∈ W)
    (he : homAct G₁.E G₂.E z z φ = (k : K) • φ) (hk : (l : ℤ) < |k|) : φ = 0 := by
  have key : ∀ μ x, φ (G₁.comp μ x) = 0 := by
    intro μ x
    by_contra hy
    have hx' : G₁.comp μ x ≠ 0 := fun h => hy (by rw [h, map_zero])
    have hE : G₂.E z z (φ (G₁.comp μ x)) = ((k + μ z : ℤ) : K) • φ (G₁.comp μ x) := by
      have h := congrArg (fun ψ : V₁ →ₗ[K] V₂ => ψ (G₁.comp μ x)) he
      simp only [homAct_apply, LinearMap.smul_apply] at h
      rw [G₁.diag, map_smul] at h
      rw [Int.cast_add, add_smul, ← h]
      abel
    have hc : ∀ ν, G₂.comp ν (φ (G₁.comp μ x)) = 0 := by
      intro ν
      by_contra hν
      have e1 := G₂.comp_Ecc ν z (φ (G₁.comp μ x))
      rw [hE, map_smul] at e1
      have e2 : (((k + μ z : ℤ) : K) - ((ν z : ℤ) : K)) • G₂.comp ν (φ (G₁.comp μ x)) = 0 := by
        rw [sub_smul, e1, sub_self]
      rcases smul_eq_zero.mp e2 with h | h
      · have h3 : k + μ z = ν z := by exact_mod_cast sub_eq_zero.mp h
        have h4 := hb μ ν (G₁.comp μ x) _ hx' hν (G₂.graded_of hW ν _ (hφ _)) (G₁.isWt_comp μ x)
          (G₂.isWt_comp ν _) z
        rw [← h3, add_sub_cancel_right] at h4
        omega
      · exact hν h
    apply hy
    have h := G₂.sum_comp (φ (G₁.comp μ x)) ∅ (fun ν _ => hc ν)
    simpa using h.symm
  ext x
  obtain ⟨S, hS⟩ := G₁.dec x
  rw [← G₁.sum_comp x S hS, map_sum, LinearMap.zero_apply]
  exact Finset.sum_eq_zero fun μ _ => key μ x

end gen

/- English proof (translation)
Introduce `K V₁ V₂ _ _ _ _ _ _ n G₁ G₂ W l hW hb φ hφ h0`. Establish `hrel : GlRel (homAct G₁.E G₂.E)` using `hom_relation_holds K V₁ V₂ (Fin n) G₁.E G₂.E (glRel_of G₁) (glRel_of G₂)`. Take `⟨c1, c2, c3⟩` from `h1 K (V₁ →ₗ[K] V₂) (Fin n) (homAct G₁.E G₂.E) hrel l (mapsInto V₁ W) (fun a b ψ hψ x => by`. Rewrite using `[homAct_apply]`. Conclude with `W.sub_mem (hW a b _ (hψ x)) (hψ _))`.

Use the proof step `(fun z k ψ hψ he hk => hom_eig_zero G₁ G₂ W l hW hb z k ψ hψ he hk)`. Use the proof step `(List.finRange n) (List.nodup_finRange n) φ hφ (fun a _ => h0 a)`. Use `⟨fun a b x => ?_, c2, c3⟩` and prove the remaining obligations. Establish `h` using `congrArg (fun ψ : V₁ →ₗ[K] V₂ => ψ x) (c1 a (List.mem_finRange a) b (List.mem_finRange b))`. Simplify using `only [homAct_apply, LinearMap.zero_apply] at h`.

Conclude with `(sub_eq_zero.mp h).symm`.
-/
theorem homInv_of (h1 : InvInv) : HomInv := by
  intro K V₁ V₂ _ _ _ _ _ _ n G₁ G₂ W l hW hb φ hφ h0
  have hrel : GlRel (homAct G₁.E G₂.E) := hom_relation_holds K V₁ V₂ (Fin n) G₁.E G₂.E (glRel_of G₁) (glRel_of G₂)
  obtain ⟨c1, c2, c3⟩ := h1 K (V₁ →ₗ[K] V₂) (Fin n) (homAct G₁.E G₂.E) hrel l (mapsInto V₁ W)
    (fun a b ψ hψ x => by
      rw [homAct_apply]
      exact W.sub_mem (hW a b _ (hψ x)) (hψ _))
    (fun z k ψ hψ he hk => hom_eig_zero G₁ G₂ W l hW hb z k ψ hψ he hk)
    (List.finRange n) (List.nodup_finRange n) φ hφ (fun a _ => h0 a)
  refine ⟨fun a b x => ?_, c2, c3⟩
  have h := congrArg (fun ψ : V₁ →ₗ[K] V₂ => ψ x) (c1 a (List.mem_finRange a) b (List.mem_finRange b))
  simp only [homAct_apply, LinearMap.zero_apply] at h
  exact (sub_eq_zero.mp h).symm

/- English proof (translation)
Introduce `K V _ _ _ _ n G W l hW hfd hfW hb la h hh hhW hh0 φ h0`. Establish `hUW : G.gS {h} ≤ W` using `G.gS_le (by simpa using hhW) hW`. Establish `: FiniteDimensional K (G.gS {h})` using `Submodule.finiteDimensional_of_le hUW`. Take `⟨c1, -, c3⟩` from `h2 K (G.gS {h}) (G.gS {h}) n (res G _ (G.gS_stable {h})) (res G _ (G.gS_stable {h})) ⊤ l (fun _ _ _ _ => Submodule.mem_top) (fun μ ν x y hx hy _ hwx hwy c => hb μ ν x y (fun e => hx (Subtype.ext e)) (fun e => hy (Subtype.ext e)) (hUW x.2) (hUW y.2) (congrArg Subtype.val hwx) (con …`. Generalize the expression as in `InvOp (homAct (res G _ (G.gS_stable {h})).E (res G _ (G.gS_stable {h})).E) l (List.finRange n) φ = ψ at c1 c3 ⊢`.

Establish `hmem : h ∈ G.gS {h}` using `G.subset_gS {h} rfl`. Establish `hwt : (res G _ (G.gS_stable {h})).IsWt la ⟨h, hmem⟩` using `Subtype.ext hh.1`. Establish `hwψ : (res G _ (G.gS_stable {h})).IsWt la (ψ ⟨h, hmem⟩)` using `Formalism.CountingSumsFrames.GlX.isWt_of_eig _ (fun c => by`. Rewrite using `[← c1, (res G _ (G.gS_stable {h})).E_diag_of_isWt hwt c, map_smul])`. Take `⟨c, hc⟩` from `G.comp_top_of_mem hh (ψ ⟨h, hmem⟩).2`.

Establish `hc' : ((ψ ⟨h, hmem⟩ : G.gS {h}) : V) = c • h`. Rewrite using `[← hc]`. Conclude with `(congrArg Subtype.val hwψ).symm`. Establish `hle : G.gS {h} ≤ Submodule.map (G.gS {h}).subtype (LinearMap.ker (ψ - c • LinearMap.id))`. Apply `G.gS_le` to reduce the goal to its premises.

Introduce `y hy`. Rewrite `hy` using `[Set.mem_singleton_iff]`. Substitute `hy` using the available equality. Use `⟨⟨y, hmem⟩, ?_, rfl⟩` and prove the remaining obligations. Simplify using `only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]`.

Rewrite using `[sub_eq_zero]`. Conclude with `Subtype.ext hc'`. Introduce and unpack `a b _ ⟨y, hy, rfl⟩`. Use `⟨(res G _ (G.gS_stable {h})).E a b y, ?_, rfl⟩` and prove the remaining obligations. Simplify using `only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at hy ⊢`.

Rewrite using `[c1, ← map_smul, ← map_sub, hy, map_zero]`. Establish `hψ : ψ = c • LinearMap.id`. Use extensionality with `x`. Take `⟨y, hy, hyx⟩` from `hle x.2`. Establish `hyx' : y = x` using `Subtype.ext hyx`.

Substitute `hyx'` using the available equality. Simplify using `only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at hy`. Rewrite using `[sub_eq_zero.mp hy]`. Both sides reduce to the same expression. Establish `htr : LinearMap.trace K _ (ψ - φ) = 0` using `hom_trace_holds K (G.gS {h}) (Fin n) _ _ c3`.

Establish `: Nontrivial (G.gS {h})` using `⟨⟨⟨h, hmem⟩, 0, fun e => hh0 (congrArg Subtype.val e)⟩⟩`. Establish `hfr : (Module.finrank K (G.gS {h}) : K) ≠ 0`. Conclude with `(Module.finrank_pos (R := K) (M := G.gS {h})).ne'` after adjusting the coercions. Rewrite `htr` using `[map_sub, sub_eq_zero, hψ, map_smul, LinearMap.trace_id, smul_eq_mul]`. Rewrite using `[hψ, ← htr, mul_div_assoc, div_self hfr, mul_one]`.
-/
theorem schurTrace_of_homInv (h2 : HomInv) : SchurTrace := by
  intro K V _ _ _ _ n G W l hW hfd hfW hb la h hh hhW hh0 φ h0
  have hUW : G.gS {h} ≤ W := G.gS_le (by simpa using hhW) hW
  have : FiniteDimensional K (G.gS {h}) := Submodule.finiteDimensional_of_le hUW
  obtain ⟨c1, -, c3⟩ := h2 K (G.gS {h}) (G.gS {h}) n (res G _ (G.gS_stable {h})) (res G _ (G.gS_stable {h})) ⊤ l
    (fun _ _ _ _ => Submodule.mem_top)
    (fun μ ν x y hx hy _ hwx hwy c => hb μ ν x y (fun e => hx (Subtype.ext e)) (fun e => hy (Subtype.ext e))
      (hUW x.2) (hUW y.2) (congrArg Subtype.val hwx) (congrArg Subtype.val hwy) c)
    φ (fun _ => Submodule.mem_top) h0
  generalize InvOp (homAct (res G _ (G.gS_stable {h})).E (res G _ (G.gS_stable {h})).E) l (List.finRange n) φ = ψ
    at c1 c3 ⊢
  have hmem : h ∈ G.gS {h} := G.subset_gS {h} rfl
  have hwt : (res G _ (G.gS_stable {h})).IsWt la ⟨h, hmem⟩ := Subtype.ext hh.1
  have hwψ : (res G _ (G.gS_stable {h})).IsWt la (ψ ⟨h, hmem⟩) :=
    Formalism.CountingSumsFrames.GlX.isWt_of_eig _ (fun c => by
      rw [← c1, (res G _ (G.gS_stable {h})).E_diag_of_isWt hwt c, map_smul])
  obtain ⟨c, hc⟩ := G.comp_top_of_mem hh (ψ ⟨h, hmem⟩).2
  have hc' : ((ψ ⟨h, hmem⟩ : G.gS {h}) : V) = c • h := by
    rw [← hc]; exact (congrArg Subtype.val hwψ).symm
  have hle : G.gS {h} ≤ Submodule.map (G.gS {h}).subtype (LinearMap.ker (ψ - c • LinearMap.id)) := by
    apply G.gS_le
    · intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      refine ⟨⟨y, hmem⟩, ?_, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
      rw [sub_eq_zero]
      exact Subtype.ext hc'
    · rintro a b _ ⟨y, hy, rfl⟩
      refine ⟨(res G _ (G.gS_stable {h})).E a b y, ?_, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply] at hy ⊢
      rw [c1, ← map_smul, ← map_sub, hy, map_zero]
  have hψ : ψ = c • LinearMap.id := by
    ext x
    obtain ⟨y, hy, hyx⟩ := hle x.2
    have hyx' : y = x := Subtype.ext hyx
    subst hyx'
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply] at hy
    rw [sub_eq_zero.mp hy]
    rfl
  have htr : LinearMap.trace K _ (ψ - φ) = 0 := hom_trace_holds K (G.gS {h}) (Fin n) _ _ c3
  have : Nontrivial (G.gS {h}) := ⟨⟨⟨h, hmem⟩, 0, fun e => hh0 (congrArg Subtype.val e)⟩⟩
  have hfr : (Module.finrank K (G.gS {h}) : K) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := K) (M := G.gS {h})).ne'
  rw [map_sub, sub_eq_zero, hψ, map_smul, LinearMap.trace_id, smul_eq_mul] at htr
  rw [hψ, ← htr, mul_div_assoc, div_self hfr, mul_one]

/- English proof (translation)
The claim follows from `schurTrace_of_homInv (homInv_of h1)`.
-/
theorem schurTrace_of (h1 : InvInv) : SchurTrace := schurTrace_of_homInv (homInv_of h1)

end Formalism.InvariantFactorPaths.PW
