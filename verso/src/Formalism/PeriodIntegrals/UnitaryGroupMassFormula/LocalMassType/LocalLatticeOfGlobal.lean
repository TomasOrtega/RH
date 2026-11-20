import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.Development

noncomputable section

namespace PI.LocMassTypL

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain
  PI.LocMassTypW
open scoped TensorProduct

section Rat

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] {n : ℕ}

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[ratV, map_add]`.
-/
theorem ratV_add (x y : Fin n → E) : ratV (F := F) R (x + y) = ratV (F := F) R x + ratV (F := F) R y := by
  funext i; simp [ratV, map_add]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[ratV]`.
-/
theorem ratV_zero : ratV (F := F) R (0 : Fin n → E) = 0 := by
  funext i; simp [ratV]

/- English proof (translation)
Use function extensionality and compare the values at `j`. Simplify using `[ratV, map_sum, Finset.sum_apply]`.
-/
theorem ratV_sum {ι : Type} (s : Finset ι) (x : ι → Fin n → E) :
    ratV (F := F) R (∑ i ∈ s, x i) = ∑ i ∈ s, ratV (F := F) R (x i) := by
  funext j; simp [ratV, map_sum, Finset.sum_apply]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[ratV, map_zsmul]`.
-/
theorem ratV_zsmul (m : ℤ) (x : Fin n → E) : ratV (F := F) R (m • x) = m • ratV (F := F) R x := by
  funext i; simp [ratV, map_zsmul]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[ratV, map_mul]`.
-/
theorem ratV_smul (a : E) (x : Fin n → E) :
    ratV (F := F) R (a • x) = inclR (F := F) R a • ratV (F := F) R x := by
  funext i; simp [ratV, map_mul]

end Rat

/- English proof (translation)
Introduce `F E _ _ _ _ _ v n Λ hL`. Take `⟨L, hL, hLΛ⟩` from `hL`. Take `⟨S, hS⟩` from `hL.fg`. Set `b` to `NumberField.RingOfIntegers.basis E`. Use `set T : Set (Fin n → E) := Set.range (fun p : Module.Free.ChooseBasisIndex ℤ (𝓞 E) × S => (b p.1 : 𝓞 E) • (p.2 : Fin n → E)) with hT`.

Establish `hTfin : T.Finite` using `Set.finite_range _`. Establish `hTL : T ⊆ (L : Set (Fin n → E))`. Introduce and unpack `_ ⟨⟨j, s⟩, rfl⟩`. Conclude with `L.smul_mem _ (hS ▸ Submodule.subset_span (Finset.mem_coe.2 s.2))`. Establish `key : ∀ x ∈ L, ratV (F` using `F) (Fv F v) x ∈ Submodule.span (v.adicCompletionIntegers F) (ratV (F := F) (Fv F v) '' T) := by`.

Introduce `x hx`. Rewrite `hx` using `[← hS]`. Take `⟨f, -, rfl⟩` from `(Submodule.mem_span_finset).1 hx`. Rewrite using `[ratV_sum]`. Use `Submodule.sum_mem _ fun s hs => ?_` and prove the remaining obligations.

Rewrite using `[← b.sum_repr (f s), Finset.sum_smul, ratV_sum]`. Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Rewrite using `[smul_assoc, ratV_zsmul]`. Establish `hmem : ratV (F` using `F) (Fv F v) ((b j : 𝓞 E) • s) ∈ ratV (F := F) (Fv F v) '' T := ⟨_, ⟨(j, ⟨s, hs⟩), rfl⟩, rfl⟩`. Conclude with `zsmul_mem (Submodule.subset_span hmem) _`.

Establish `heq : latLoc (E` using `E) v Λ = Submodule.span (v.adicCompletionIntegers F) (ratV (F := F) (Fv F v) '' T) := by`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[latLoc, Submodule.span_le]`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Rewrite `hx` using `[← hLΛ]`.

Conclude with `key x hx`. Rewrite using `[latLoc]`. Conclude with `Submodule.span_mono (Set.image_mono (by rw [← hLΛ]; exact hTL))`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[heq]`.

Conclude with `Submodule.fg_span (hTfin.image _)`. Establish `hspan : ∀ x ∈ Submodule.span E (L : Set (Fin n → E)), ratV (F` using `F) (Fv F v) x ∈ Submodule.span (Fv F v ⊗[F] E) (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E)) := by`. Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`.

Apply `Submodule.subset_span` to reduce the goal to its premises. Use `show ratV (F := F) (Fv F v) y ∈ latLoc (E := E) v Λ`. Conclude with `Submodule.subset_span ⟨y, hLΛ ▸ hy, rfl⟩`. Consider the case `zero => rw [ratV_zero]`. Conclude with `Submodule.zero_mem _`.

Consider the case `add y z _ _ h1 h2 => rw [ratV_add]`. Conclude with `Submodule.add_mem _ h1 h2`. Consider the case `smul a y _ h => rw [ratV_smul]`. Conclude with `Submodule.smul_mem _ _ h`. Rewrite using `[eq_top_iff]`.

Introduce `y _`. Rewrite using `[pi_eq_sum_univ y]`. Use `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Use `hspan (fun j => if i = j then (1 : E) else 0) (by rw [hL.span_eq_top]; trivial)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `j`. Apply the tactic sequence `by_cases hij : i = j <;> simp [ratV, hij]`.
-/
theorem local_lattice_of_global : LatOfGlob := by
  intro F E _ _ _ _ _ v n Λ hL
  obtain ⟨L, hL, hLΛ⟩ := hL
  classical
  obtain ⟨S, hS⟩ := hL.fg
  let b := NumberField.RingOfIntegers.basis E
  set T : Set (Fin n → E) := Set.range (fun p : Module.Free.ChooseBasisIndex ℤ (𝓞 E) × S =>
    (b p.1 : 𝓞 E) • (p.2 : Fin n → E)) with hT
  have hTfin : T.Finite := Set.finite_range _
  have hTL : T ⊆ (L : Set (Fin n → E)) := by
    rintro _ ⟨⟨j, s⟩, rfl⟩
    exact L.smul_mem _ (hS ▸ Submodule.subset_span (Finset.mem_coe.2 s.2))
  have key : ∀ x ∈ L, ratV (F := F) (Fv F v) x ∈
      Submodule.span (v.adicCompletionIntegers F) (ratV (F := F) (Fv F v) '' T) := by
    intro x hx
    rw [← hS] at hx
    obtain ⟨f, -, rfl⟩ := (Submodule.mem_span_finset).1 hx
    rw [ratV_sum]
    refine Submodule.sum_mem _ fun s hs => ?_
    rw [← b.sum_repr (f s), Finset.sum_smul, ratV_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [smul_assoc, ratV_zsmul]
    have hmem : ratV (F := F) (Fv F v) ((b j : 𝓞 E) • s) ∈ ratV (F := F) (Fv F v) '' T :=
      ⟨_, ⟨(j, ⟨s, hs⟩), rfl⟩, rfl⟩
    exact zsmul_mem (Submodule.subset_span hmem) _
  have heq : latLoc (E := E) v Λ =
      Submodule.span (v.adicCompletionIntegers F) (ratV (F := F) (Fv F v) '' T) := by
    apply le_antisymm
    · rw [latLoc, Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      rw [← hLΛ] at hx
      exact key x hx
    · rw [latLoc]
      exact Submodule.span_mono (Set.image_mono (by rw [← hLΛ]; exact hTL))
  refine ⟨?_, ?_⟩
  · rw [heq]; exact Submodule.fg_span (hTfin.image _)
  · have hspan : ∀ x ∈ Submodule.span E (L : Set (Fin n → E)),
        ratV (F := F) (Fv F v) x ∈ Submodule.span (Fv F v ⊗[F] E)
          (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E)) := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem y hy =>
        apply Submodule.subset_span
        show ratV (F := F) (Fv F v) y ∈ latLoc (E := E) v Λ
        exact Submodule.subset_span ⟨y, hLΛ ▸ hy, rfl⟩
      | zero => rw [ratV_zero]; exact Submodule.zero_mem _
      | add y z _ _ h1 h2 => rw [ratV_add]; exact Submodule.add_mem _ h1 h2
      | smul a y _ h => rw [ratV_smul]; exact Submodule.smul_mem _ _ h
    rw [eq_top_iff]
    intro y _
    rw [pi_eq_sum_univ y]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    have := hspan (fun j => if i = j then (1 : E) else 0) (by rw [hL.span_eq_top]; trivial)
    convert this using 1
    funext j
    by_cases hij : i = j <;> simp [ratV, hij]

end PI.LocMassTypL
