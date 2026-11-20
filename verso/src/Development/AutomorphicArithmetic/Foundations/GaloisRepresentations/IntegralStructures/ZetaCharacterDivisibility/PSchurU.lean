import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.CharOfZeta
import Development.AutomorphicArithmetic.DivisorFrames.FiniteDimensionalAutomorphicFormsUnitaryOfTypeLe
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.Int.Div

/- English proof (translation)
Introduce `E _ _ _ a U hU z hz`. Take `⟨φ, hφU, hφ0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hU.ne_bot`. Establish `hcomm : ∀ (x : UA E a) (ψ : UA E a → ℂ), RU E a z (RU E a x ψ) = RU E a x (RU E a z ψ)` using `fun x ψ => by`. Rewrite using `[GlobalTheory.DefU.RU_RU, GlobalTheory.DefU.RU_RU, hz]`. Set `S : Submodule ℂ (UA E a → ℂ)` to `Submodule.span ℂ (Set.range fun k : infU E a => RU E a k φ)`.

Use `haveI hSfd : FiniteDimensional ℂ S := (hU.aut φ hφU).kfin`. Establish `hSU : S ≤ U` using `Submodule.span_le.2 (by`. Introduce and unpack `_ ⟨k, rfl⟩`. Conclude with `hU.stable _ _ hφU)`. Establish `hφS : φ ∈ S` using `Submodule.subset_span ⟨1, by simp⟩`.

Establish `hSst : ∀ x : infU E a, ∀ v ∈ S, RU E a x v ∈ S`. Introduce `x v hv`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem v hv`. Take `⟨k, rfl⟩` from `hv`.

Conclude with `Submodule.subset_span ⟨x * k, by simp only [Subgroup.coe_mul, GlobalTheory.DefU.RU_RU]⟩`. Consider the case `zero => rw [map_zero]`. Conclude with `S.zero_mem`. Consider the case `add p q _ _ hp hq => rw [map_add]`. Conclude with `S.add_mem hp hq`.

Consider the case `smul c p _ hp => rw [map_smul]`. Conclude with `S.smul_mem c hp`. Set `ρ : infU E a → Module.End ℂ S` to `fun x => (RU E a x).restrict (hSst x)`. Set `K : Subgroup (finU E a)` to `{ carrier := {k | RU E a k φ = φ} one_mem' := by`. Express the relevant statement in the definitionally equal form `RU E a ((1 : finU E a) : UA E a) φ = φ`.

Simplify using the standard rewrite rules. Use the proof step `mul_mem' := fun {p q} hp hq => by`. Establish `hp' : RU E a p φ = φ` using `hp`. Establish `hq' : RU E a q φ = φ` using `hq`. Express the relevant statement in the definitionally equal form `RU E a ((p * q : finU E a) : UA E a) φ = φ`.

Rewrite using `[Subgroup.coe_mul, ← GlobalTheory.DefU.RU_RU, hq', hp']`. Use the proof step `inv_mem' := fun {p} hp => by`. Establish `hp' : RU E a p φ = φ` using `hp`. Express the relevant statement in the definitionally equal form `RU E a ((p⁻¹ : finU E a) : UA E a) φ = φ`. Use `conv_lhs => rw [← hp']`.

Rewrite using `[GlobalTheory.DefU.RU_RU, Subgroup.coe_inv, inv_mul_cancel, map_one, Module.End.one_apply] }`. Establish `hKo : IsOpen (K : Set (finU E a))` using `(hU.aut φ hφU).level`. Establish `hKS : ∀ k ∈ K, ∀ v ∈ S, RU E a (k : finU E a) v = v`. Introduce `k hk v hv`. Establish `hk' : RU E a k φ = φ` using `hk`.

Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem v hv`. Take `⟨x, rfl⟩` from `hv`. Express the relevant statement in the definitionally equal form `RU E a k (RU E a x φ) = RU E a x φ`. Rewrite using `[GlobalTheory.DefU.RU_RU, GlobalTheory.DefU.fin_mul_inf k.2 x.2, ← GlobalTheory.DefU.RU_RU, hk']`.

Consider the case `zero => rw [map_zero]`. Consider the case `add p q _ _ hp hq => rw [map_add, hp, hq]`. Consider the case `smul c p _ hp => rw [map_smul, hp]`. Set `M : Submodule ℂ (S →ₗ[ℂ] (UA E a → ℂ))` to `{ carrier := {f | (∀ v, f v ∈ U) ∧ (∀ (x : infU E a) v, f (ρ x v) = RU E a x (f v)) ∧ ∀ k ∈ K, ∀ v, RU E a (k : finU E a) (f v) = f v} add_mem' := fun {f g} hf hg => ⟨fun v => U.add_mem (hf.1 v) (hg.1 v), fun x v => by rw [LinearMap.add_apply, LinearMap.add_apply, hf.2.1, hg.2.1, …`. Use `haveI hMfd : FiniteDimensional ℂ M := UpperTheory.finiteDimensional_automorphicForms_unitary_of_type_level E a S ρ K hKo M fun f hf => ⟨fun v γ hγ g => (hU.aut _ (hf.1 v)).left γ hγ g, hf.2.1, hf.2.2⟩`.

Establish `hsub : S.subtype ∈ M` using `⟨fun v => hSU v.2, fun _ _ => rfl, fun k hk v => hKS k hk v.1 v.2⟩`. Use `haveI : Nontrivial M := ⟨⟨⟨S.subtype, hsub⟩, 0, fun h => hφ0 (by`. Establish `h1` using `LinearMap.congr_fun (congrArg Subtype.val h) (⟨φ, hφS⟩ : S)`. Conclude with `h1)⟩⟩`. Set `T : Module.End ℂ M` to `{ toFun := fun f => ⟨(RU E a z).comp f.1, fun v => hU.stable z _ (f.2.1 v), fun x v => by`.

Rewrite using `[LinearMap.comp_apply, LinearMap.comp_apply, f.2.2.1, hcomm],`. Use `fun k hk v => by`. Rewrite using `[LinearMap.comp_apply, ← hcomm, f.2.2.2 k hk]⟩`. Use the proof step `map_add' := fun f g => Subtype.ext (LinearMap.ext fun v => map_add (RU E a z) _ _)`. Use the proof step `map_smul' := fun c f => Subtype.ext (LinearMap.ext fun v => map_smul (RU E a z) c _) }`.

Take `⟨c, hc⟩` from `Module.End.exists_eigenvalue T`. Take `⟨f, hf⟩` from `hc.exists_hasEigenvector`. Establish `hTf : ∀ v, RU E a z (f.1 v) = c • f.1 v` using `fun v => LinearMap.congr_fun (congrArg Subtype.val hf.apply_eq_smul) v`. Establish `hfne : ∃ v, f.1 v ≠ 0`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Conclude with `hf.2 (Subtype.ext (LinearMap.ext h))`. Take `⟨v, hv⟩` from `hfne`. Set `W : Submodule ℂ (UA E a → ℂ)` to `{ carrier := {ψ | ψ ∈ U ∧ RU E a z ψ = c • ψ} add_mem' := fun {p q} hp hq => ⟨U.add_mem hp.1 hq.1, by rw [map_add, hp.2, hq.2, smul_add]⟩ zero_mem' := ⟨U.zero_mem, by rw [map_zero, smul_zero]⟩ smul_mem' := fun b p hp => ⟨U.smul_mem b hp.1, by rw [map_smul, hp.2, smul_comm]⟩ }`. Establish `hWU : W ≤ U` using `fun _ h => h.1`.

Establish `hWst : ∀ x, ∀ ψ ∈ W, RU E a x ψ ∈ W` using `fun x ψ hψ => ⟨hU.stable x ψ hψ.1, by rw [hcomm, hψ.2, map_smul]⟩`. Establish `hvW : f.1 v ∈ W` using `⟨f.2.1 v, hTf v⟩`. Break down `hU.irred W hWU hWst with h | h` into its components or cases. Conclude with `absurd ((Submodule.mem_bot ℂ).1 (h ▸ hvW)) hv`. Conclude with `⟨c, fun ψ hψ => (h ▸ hψ : ψ ∈ W).2⟩`.
-/
theorem UpperTheory.Gal.Int.Div.schurU_of :
    SchurU := by
  intro E _ _ _ a U hU z hz
  classical
  obtain ⟨φ, hφU, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU.ne_bot
  have hcomm : ∀ (x : UA E a) (ψ : UA E a → ℂ), RU E a z (RU E a x ψ) = RU E a x (RU E a z ψ) := fun x ψ => by
    rw [GlobalTheory.DefU.RU_RU, GlobalTheory.DefU.RU_RU, hz]
  let S : Submodule ℂ (UA E a → ℂ) := Submodule.span ℂ (Set.range fun k : infU E a => RU E a k φ)
  haveI hSfd : FiniteDimensional ℂ S := (hU.aut φ hφU).kfin
  have hSU : S ≤ U := Submodule.span_le.2 (by
    rintro _ ⟨k, rfl⟩
    exact hU.stable _ _ hφU)
  have hφS : φ ∈ S := Submodule.subset_span ⟨1, by simp⟩
  have hSst : ∀ x : infU E a, ∀ v ∈ S, RU E a x v ∈ S := by
    intro x v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨k, rfl⟩ := hv
      exact Submodule.subset_span ⟨x * k, by simp only [Subgroup.coe_mul, GlobalTheory.DefU.RU_RU]⟩
    | zero => rw [map_zero]; exact S.zero_mem
    | add p q _ _ hp hq => rw [map_add]; exact S.add_mem hp hq
    | smul c p _ hp => rw [map_smul]; exact S.smul_mem c hp
  let ρ : infU E a → Module.End ℂ S := fun x => (RU E a x).restrict (hSst x)
  let K : Subgroup (finU E a) :=
    { carrier := {k | RU E a k φ = φ}
      one_mem' := by
        change RU E a ((1 : finU E a) : UA E a) φ = φ
        simp
      mul_mem' := fun {p q} hp hq => by
        have hp' : RU E a p φ = φ := hp
        have hq' : RU E a q φ = φ := hq
        change RU E a ((p * q : finU E a) : UA E a) φ = φ
        rw [Subgroup.coe_mul, ← GlobalTheory.DefU.RU_RU, hq', hp']
      inv_mem' := fun {p} hp => by
        have hp' : RU E a p φ = φ := hp
        change RU E a ((p⁻¹ : finU E a) : UA E a) φ = φ
        conv_lhs => rw [← hp']
        rw [GlobalTheory.DefU.RU_RU, Subgroup.coe_inv, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hKo : IsOpen (K : Set (finU E a)) := (hU.aut φ hφU).level
  have hKS : ∀ k ∈ K, ∀ v ∈ S, RU E a (k : finU E a) v = v := by
    intro k hk v hv
    have hk' : RU E a k φ = φ := hk
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨x, rfl⟩ := hv
      change RU E a k (RU E a x φ) = RU E a x φ
      rw [GlobalTheory.DefU.RU_RU, GlobalTheory.DefU.fin_mul_inf k.2 x.2, ← GlobalTheory.DefU.RU_RU, hk']
    | zero => rw [map_zero]
    | add p q _ _ hp hq => rw [map_add, hp, hq]
    | smul c p _ hp => rw [map_smul, hp]
  let M : Submodule ℂ (S →ₗ[ℂ] (UA E a → ℂ)) :=
    { carrier := {f | (∀ v, f v ∈ U) ∧ (∀ (x : infU E a) v, f (ρ x v) = RU E a x (f v)) ∧
        ∀ k ∈ K, ∀ v, RU E a (k : finU E a) (f v) = f v}
      add_mem' := fun {f g} hf hg => ⟨fun v => U.add_mem (hf.1 v) (hg.1 v),
        fun x v => by rw [LinearMap.add_apply, LinearMap.add_apply, hf.2.1, hg.2.1, map_add],
        fun k hk v => by rw [LinearMap.add_apply, map_add, hf.2.2 k hk, hg.2.2 k hk]⟩
      zero_mem' := ⟨fun _ => U.zero_mem, fun x v => by simp, fun k _ v => by simp⟩
      smul_mem' := fun c f hf => ⟨fun v => U.smul_mem c (hf.1 v),
        fun x v => by rw [LinearMap.smul_apply, LinearMap.smul_apply, hf.2.1, map_smul],
        fun k hk v => by rw [LinearMap.smul_apply, map_smul, hf.2.2 k hk]⟩ }
  haveI hMfd : FiniteDimensional ℂ M := UpperTheory.finiteDimensional_automorphicForms_unitary_of_type_level E a S ρ K hKo M fun f hf =>
    ⟨fun v γ hγ g => (hU.aut _ (hf.1 v)).left γ hγ g, hf.2.1, hf.2.2⟩
  have hsub : S.subtype ∈ M :=
    ⟨fun v => hSU v.2, fun _ _ => rfl, fun k hk v => hKS k hk v.1 v.2⟩
  haveI : Nontrivial M := ⟨⟨⟨S.subtype, hsub⟩, 0, fun h => hφ0 (by
    have h1 := LinearMap.congr_fun (congrArg Subtype.val h) (⟨φ, hφS⟩ : S)
    exact h1)⟩⟩
  let T : Module.End ℂ M :=
    { toFun := fun f => ⟨(RU E a z).comp f.1, fun v => hU.stable z _ (f.2.1 v),
        fun x v => by
          rw [LinearMap.comp_apply, LinearMap.comp_apply, f.2.2.1, hcomm],
        fun k hk v => by
          rw [LinearMap.comp_apply, ← hcomm, f.2.2.2 k hk]⟩
      map_add' := fun f g => Subtype.ext (LinearMap.ext fun v => map_add (RU E a z) _ _)
      map_smul' := fun c f => Subtype.ext (LinearMap.ext fun v => map_smul (RU E a z) c _) }
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue T
  obtain ⟨f, hf⟩ := hc.exists_hasEigenvector
  have hTf : ∀ v, RU E a z (f.1 v) = c • f.1 v := fun v =>
    LinearMap.congr_fun (congrArg Subtype.val hf.apply_eq_smul) v
  have hfne : ∃ v, f.1 v ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf.2 (Subtype.ext (LinearMap.ext h))
  obtain ⟨v, hv⟩ := hfne
  let W : Submodule ℂ (UA E a → ℂ) :=
    { carrier := {ψ | ψ ∈ U ∧ RU E a z ψ = c • ψ}
      add_mem' := fun {p q} hp hq => ⟨U.add_mem hp.1 hq.1, by rw [map_add, hp.2, hq.2, smul_add]⟩
      zero_mem' := ⟨U.zero_mem, by rw [map_zero, smul_zero]⟩
      smul_mem' := fun b p hp => ⟨U.smul_mem b hp.1, by rw [map_smul, hp.2, smul_comm]⟩ }
  have hWU : W ≤ U := fun _ h => h.1
  have hWst : ∀ x, ∀ ψ ∈ W, RU E a x ψ ∈ W := fun x ψ hψ =>
    ⟨hU.stable x ψ hψ.1, by rw [hcomm, hψ.2, map_smul]⟩
  have hvW : f.1 v ∈ W := ⟨f.2.1 v, hTf v⟩
  rcases hU.irred W hWU hWst with h | h
  · exact absurd ((Submodule.mem_bot ℂ).1 (h ▸ hvW)) hv
  · exact ⟨c, fun ψ hψ => (h ▸ hψ : ψ ∈ W).2⟩
