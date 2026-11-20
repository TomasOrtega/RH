import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SpanMono

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

/- English proof (translation)
Introduce `Ω _ _ _ l _ c D hD M h0 K _ _ ξ ξ' hrep`. Establish `hent : ∀ g i j, ξ (M.ent g i j) = ξ' (M.ent g i j)`. Introduce `g i j`. Use `congrArg (fun r => r g i j) hrep` as an intermediate fact. Simplify `this` using `[Model.rep, mapRep, Model.rS, RingHom.mapMatrix_apply]`.

Set `Q : Subalgebra c.O M.S` to `(AlgHom.equalizer ξ ξ').map M.SS.val`. Establish `hQent : ∀ g i j, M.ru.hom g i j ∈ Q`. Introduce `g i j`. Conclude with `⟨M.ent g i j, hent g i j, rfl⟩`. Establish `hQmono : ∀ w, mono M.ru.hom w ⊆ (Q : Set M.S)`.

Introduce `w y hy`. Take `⟨L, -, rfl⟩` from `hy`. Apply `Subalgebra.list_prod_mem` to reduce the goal to its premises. Introduce `z hz`. Take `⟨a, -, rfl⟩` from `List.mem_map.mp hz`.

Conclude with `hQent _ _ _`. Establish `hle : (⨆ j, M.sPart j) ≤ Subalgebra.toSubmodule Q`. Use `iSup_le fun w => ?_` and prove the remaining obligations. Rewrite using `[spanMono D hD M h0 w, Submodule.span_le]`. Conclude with `hQmono w`.

Apply `AlgHom.ext` to reduce the goal to its premises. Introduce `x`. Establish `hx : (x : M.S) ∈ ⨆ j, M.sPart j` using `x.2`. Take `⟨y, hy, hyx⟩` from `hle hx`. Establish `: y = x` using `Subtype.ext hyx`.

Rewrite using `[← this]`. Conclude with `hy`.
-/
theorem UpperTheory.V.GradeZeroInterpolatingElement.ptExt :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, D.Fin0 → ∀ (K : Type) [CommRing K] [Algebra c.O K] (ξ ξ' : M.SS →ₐ[c.O] K), M.rep ξ = M.rep ξ' → ξ = ξ' := by
  intro Ω _ _ _ l _ c D hD M h0 K _ _ ξ ξ' hrep
  have hent : ∀ g i j, ξ (M.ent g i j) = ξ' (M.ent g i j) := by
    intro g i j
    have := congrArg (fun r => r g i j) hrep
    simpa [Model.rep, mapRep, Model.rS, RingHom.mapMatrix_apply] using this
  let Q : Subalgebra c.O M.S := (AlgHom.equalizer ξ ξ').map M.SS.val
  have hQent : ∀ g i j, M.ru.hom g i j ∈ Q := by
    intro g i j
    exact ⟨M.ent g i j, hent g i j, rfl⟩
  have hQmono : ∀ w, mono M.ru.hom w ⊆ (Q : Set M.S) := by
    intro w y hy
    obtain ⟨L, -, rfl⟩ := hy
    apply Subalgebra.list_prod_mem
    intro z hz
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hz
    exact hQent _ _ _
  have hle : (⨆ j, M.sPart j) ≤ Subalgebra.toSubmodule Q := by
    refine iSup_le fun w => ?_
    rw [spanMono D hD M h0 w, Submodule.span_le]
    exact hQmono w
  apply AlgHom.ext
  intro x
  have hx : (x : M.S) ∈ ⨆ j, M.sPart j := x.2
  obtain ⟨y, hy, hyx⟩ := hle hx
  have : y = x := Subtype.ext hyx
  rw [← this]
  exact hy
