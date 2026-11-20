import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.IsOpenForallMulVec
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.GOfPrime

noncomputable section

namespace MassDataIdxK

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain Topology
open scoped Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes TensorProduct Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : ℕ} (v : HeightOneSpectrum (𝓞 F))

/- English proof (translation)
Use `fdFE (F := F) (E := E)` as an intermediate fact. Use `MassDataIdxSteps.tens_topRing (F := F) (E := E) v` as an intermediate fact. Take `⟨hKo, hKc⟩` from `kloc_open_compact v L hL hfg`. Take `⟨hΛo, hΛc⟩` from `latOpenCompact v L hL hfg`. Establish `hHc` using `isClosed_HR v σ J`.

Set `K : Subgroup (HA (Fv F v) σ J)` to `(Kloc (E := E) v (L : Set (Fin n → E))).comap (HR (Fv F v) σ J).subtype`. Establish `hKset : (K : Set (HA (Fv F v) σ J)) = Formalism.L2.SG.TypedSets.Kv σ J (L : Set (Fin n → E)) v` using `rfl`. Establish `hKo' : IsOpen (K : Set (HA (Fv F v) σ J))` using `hKo.preimage continuous_subtype_val`. Use `⟨K, hKset, hKo', hHc.isClosedEmbedding_subtypeVal.isCompact_preimage hKc, ?_⟩` and prove the remaining obligations. Use `set Λ : Set (Fin n → Fv F v ⊗[F] E) := (latLoc (E := E) v (L : Set (Fin n → E)) : Set (Fin n → Fv F v ⊗[F] E)) with hΛ`.

Use `set U : Set (Fin n → Fv F v ⊗[F] E) := {w | ∃ z ∈ Λ, w = (g : v.adicCompletionIntegers F) • z} with hUdef`. Establish `hc : ((g : v.adicCompletionIntegers F) : Fv F v) ≠ 0`. Establish `: ((g : v.adicCompletionIntegers F) : Fv F v) = algebraMap F (Fv F v) g` using `by simp`. Rewrite using `[this]`. Conclude with `(map_ne_zero _).2 (Nat.cast_ne_zero.2 hg)`.

Establish `hU : IsOpen U`. Establish `: U = (fun z => ((g : v.adicCompletionIntegers F) : Fv F v) • z) '' Λ`. Use extensionality with `w`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz, rfl⟩`.

Conclude with `⟨z, hz, rfl⟩`. Introduce and unpack `⟨z, hz, rfl⟩`. Conclude with `⟨z, hz, rfl⟩`. Rewrite using `[this]`. Conclude with `isOpenMap_smul₀ hc _ hΛo`.

Establish `hS : IsOpen {h : GL (Fin n) (Fv F v ⊗[F] E) | ((h : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) - 1) ∈ {A : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) | ∀ y ∈ Λ, A *ᵥ y ∈ U}}` using `(isOpen_forall_mulVec v hΛc hU).preimage (Units.continuous_val.sub continuous_const)`. Establish `heq : Formalism.L2.SG.TypedSets.Kgv σ J (L : Set (Fin n → E)) g v = (K : Set (HA (Fv F v) σ J)) ∩ (Subtype.val ⁻¹' {h : GL (Fin n) (Fv F v ⊗[F] E) | ((h : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) - 1) ∈ {A : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) | ∀ y ∈ Λ, A *ᵥ y ∈ U}})` using `Set.ext fun x => Iff.rfl`. Rewrite using `[heq]`. Conclude with `hKo'.inter (hS.preimage continuous_subtype_val)`.
-/
theorem stK_gen (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (hfg : L.FG) (g : ℕ) (hg : g ≠ 0) :
    ∃ K : Subgroup (HA (Fv F v) σ J),
      (K : Set (HA (Fv F v) σ J)) = Formalism.L2.SG.TypedSets.Kv σ J (L : Set (Fin n → E)) v ∧
      IsOpen (K : Set (HA (Fv F v) σ J)) ∧ IsCompact (K : Set (HA (Fv F v) σ J)) ∧
      IsOpen (Formalism.L2.SG.TypedSets.Kgv σ J (L : Set (Fin n → E)) g v) := by
  have := fdFE (F := F) (E := E)
  have := MassDataIdxSteps.tens_topRing (F := F) (E := E) v
  obtain ⟨hKo, hKc⟩ := kloc_open_compact v L hL hfg
  obtain ⟨hΛo, hΛc⟩ := latOpenCompact v L hL hfg
  have hHc := isClosed_HR v σ J
  let K : Subgroup (HA (Fv F v) σ J) :=
    (Kloc (E := E) v (L : Set (Fin n → E))).comap (HR (Fv F v) σ J).subtype
  have hKset : (K : Set (HA (Fv F v) σ J)) = Formalism.L2.SG.TypedSets.Kv σ J (L : Set (Fin n → E)) v := rfl
  have hKo' : IsOpen (K : Set (HA (Fv F v) σ J)) := hKo.preimage continuous_subtype_val
  refine ⟨K, hKset, hKo', hHc.isClosedEmbedding_subtypeVal.isCompact_preimage hKc, ?_⟩
  set Λ : Set (Fin n → Fv F v ⊗[F] E) := (latLoc (E := E) v (L : Set (Fin n → E)) : Set (Fin n → Fv F v ⊗[F] E)) with hΛ
  set U : Set (Fin n → Fv F v ⊗[F] E) := {w | ∃ z ∈ Λ, w = (g : v.adicCompletionIntegers F) • z} with hUdef
  have hc : ((g : v.adicCompletionIntegers F) : Fv F v) ≠ 0 := by
    have : ((g : v.adicCompletionIntegers F) : Fv F v) = algebraMap F (Fv F v) g := by simp
    rw [this]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hg)
  have hU : IsOpen U := by
    have : U = (fun z => ((g : v.adicCompletionIntegers F) : Fv F v) • z) '' Λ := by
      ext w
      constructor
      · rintro ⟨z, hz, rfl⟩; exact ⟨z, hz, rfl⟩
      · rintro ⟨z, hz, rfl⟩; exact ⟨z, hz, rfl⟩
    rw [this]
    exact isOpenMap_smul₀ hc _ hΛo
  have hS : IsOpen {h : GL (Fin n) (Fv F v ⊗[F] E) |
      ((h : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) - 1) ∈
        {A : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) | ∀ y ∈ Λ, A *ᵥ y ∈ U}} :=
    (isOpen_forall_mulVec v hΛc hU).preimage (Units.continuous_val.sub continuous_const)
  have heq : Formalism.L2.SG.TypedSets.Kgv σ J (L : Set (Fin n → E)) g v =
      (K : Set (HA (Fv F v) σ J)) ∩ (Subtype.val ⁻¹' {h : GL (Fin n) (Fv F v ⊗[F] E) |
        ((h : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) - 1) ∈
          {A : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) | ∀ y ∈ Λ, A *ᵥ y ∈ U}}) :=
    Set.ext fun x => Iff.rfl
  rw [heq]
  exact hKo'.inter (hS.preimage continuous_subtype_val)

end MassDataIdxK

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.TypedSets Formalism.L2.SG.HidaSetting

/- English proof (translation)
The claim follows from `MassDataIdxK.stK_gen p.1 X.B.I.cm.sig X.B.I.J X.B.I.L X.B.I.L_span X.B.I.L_fg (gOf p) (gOf_prime X p).ne_zero`.
-/
theorem stK_holds {D : Formalism.BasicNotions.D7} (X : HidaSetting D) (p : TypX X) : StK X p :=
  MassDataIdxK.stK_gen p.1 X.B.I.cm.sig X.B.I.J X.B.I.L X.B.I.L_span X.B.I.L_fg (gOf p) (gOf_prime X p).ne_zero

end MassDataIdxSteps
