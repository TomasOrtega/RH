import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

/- English proof (translation)
Set `V : OpenSubgroup (GL (Fin n) (Af E))` to `{ carrier := {k | TR.finRep E n k φ = φ} mul_mem' := fun {a b} ha hb => by`. Simplify using `only [Set.mem_setOf_eq] at ha hb ⊢`. Rewrite using `[map_mul, Module.End.mul_apply, hb, ha]`. Use the proof step `one_mem' := by simp`. Use the proof step `inv_mem' := fun {a} ha => by`.

Simplify using `only [Set.mem_setOf_eq] at ha ⊢`. Use `conv_lhs => rw [← ha]`. Rewrite using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]`. Use the proof step `isOpen' := (π.cusp φ hφ).1.level }`. Take `⟨S, hS⟩` from `hL E n V`.

Use `⟨S, fun g k hk => ?_⟩` and prove the remaining obligations. Establish `h : TR.finRep E n k φ = φ` using `hS k hk`. Conclude with `congrArg (fun ψ : TR.Sm E n => ψ.1 g) h`.
-/
private theorem lev (hL : LevelS) {E : Type} [Field E] [NumberField E] [IsTotallyReal E] {n : ℕ} (π : CuspSub E n)
    (φ : TR.Sm E n) (hφ : φ ∈ π.V) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 E)), ∀ g k, InKS S k → φ.1 (g * finGL E n k) = φ.1 g := by
  let V : OpenSubgroup (GL (Fin n) (Af E)) :=
    { carrier := {k | TR.finRep E n k φ = φ}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, Module.End.mul_apply, hb, ha]
      one_mem' := by simp
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
      isOpen' := (π.cusp φ hφ).1.level }
  obtain ⟨S, hS⟩ := hL E n V
  refine ⟨S, fun g k hk => ?_⟩
  have h : TR.finRep E n k φ = φ := hS k hk
  exact congrArg (fun ψ : TR.Sm E n => ψ.1 g) h

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun w hw => hk.1 w (h hw), hk.2⟩`.
-/
private theorem inKS_mono {E : Type} [Field E] [NumberField E] {n : ℕ} {S T : Finset (HeightOneSpectrum (𝓞 E))}
    (h : S ⊆ T) {k : GL (Fin n) (Af E)} (hk : InKS T k) : InKS S k :=
  ⟨fun w hw => hk.1 w (h hw), hk.2⟩

/- English proof (translation)
Introduce `hP hL E _ _ _ n π π' hs φ hφ φ' hφ'`. Take `⟨S₁, h₁⟩` from `lev hL π φ hφ`. Take `⟨S₂, h₂⟩` from `lev hL π' φ' hφ'`. Establish `hf` using `Filter.eventually_cofinite.1 ((hP E).2.and hs)`. Establish `hB : ∀ w : HeightOneSpectrum (𝓞 E), ∃ B : Multiset ℂˣ, w ∉ hf.toFinset → GoodAt w (psiL w) ∧ π.HasSat w B ∧ π'.HasSat w B` using `fun w => by`.

Distinguish the cases in `hw : w ∈ hf.toFinset`. Conclude with `⟨0, fun h => absurd hw h⟩`. Rewrite `hw` using `[Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not]`. Take `⟨hg, B, hB⟩` from `hw`. Conclude with `⟨B, fun _ => ⟨hg, hB⟩⟩`.

Use `choose B hB using hB`. Use `⟨hf.toFinset ∪ (S₁ ∪ S₂), B, fun w hw => hB w fun h => hw (Finset.mem_union_left _ h), fun g k hk => h₁ g k (inKS_mono ?_ hk), fun g k hk => h₂ g k (inKS_mono ?_ hk)⟩` and prove the remaining obligations. Conclude with `Finset.subset_union_left.trans Finset.subset_union_right`. Conclude with `Finset.subset_union_right.trans Finset.subset_union_right`.
-/
theorem UpperTheory.V.Af.Smo.setUp :
    UpperTheory.V.Af.Smo.PsiLoc → UpperTheory.V.Af.Smo.LevelS → UpperTheory.V.Af.Smo.SetUp := by
  intro hP hL E _ _ _ n π π' hs φ hφ φ' hφ'
  classical
  obtain ⟨S₁, h₁⟩ := lev hL π φ hφ
  obtain ⟨S₂, h₂⟩ := lev hL π' φ' hφ'
  have hf := Filter.eventually_cofinite.1 ((hP E).2.and hs)
  have hB : ∀ w : HeightOneSpectrum (𝓞 E), ∃ B : Multiset ℂˣ, w ∉ hf.toFinset →
      GoodAt w (psiL w) ∧ π.HasSat w B ∧ π'.HasSat w B := fun w => by
    by_cases hw : w ∈ hf.toFinset
    · exact ⟨0, fun h => absurd hw h⟩
    · rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hw
      obtain ⟨hg, B, hB⟩ := hw
      exact ⟨B, fun _ => ⟨hg, hB⟩⟩
  choose B hB using hB
  refine ⟨hf.toFinset ∪ (S₁ ∪ S₂), B, fun w hw => hB w fun h => hw (Finset.mem_union_left _ h),
    fun g k hk => h₁ g k (inKS_mono ?_ hk), fun g k hk => h₂ g k (inKS_mono ?_ hk)⟩
  · exact Finset.subset_union_left.trans Finset.subset_union_right
  · exact Finset.subset_union_right.trans Finset.subset_union_right
