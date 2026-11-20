import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.UnlinkedProductIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInSupportOfMultiProd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InSupportOfIsSubquotient
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory

/- English proof (translation)
Introduce `hτ hex ⟨T, f, hf⟩`. Set `W' : Subrepresentation τ` to `⟨(LinearMap.ker (q.toLinearMap ∘ₗ T.toSubmodule.subtype)).map f.toLinearMap, by`. Introduce and unpack `g _ ⟨t, ht, rfl⟩`. Use `⟨T.toRepresentation g t, ?_, (f.isIntertwining _ _ g t)⟩` and prove the remaining obligations. Establish `ht' : q (t : V) = 0` using `ht`.

Use `show q (ρ g (t : V)) = 0`. Rewrite using `[q.isIntertwining, ht', map_zero]⟩`. Break down `hτ.eq_bot_or_eq_top W' with h | h` into its components or cases. Use `right`. Establish `hvan : ∀ t : T.toSubmodule, q (t : V) = 0 → f t = 0`.

Introduce `t ht`. Establish `hm : f t ∈ W'.toSubmodule` using `⟨t, ht, rfl⟩`. Rewrite `hm` using `[h]`. Conclude with `hm`. Set `S : Subrepresentation κ` to `⟨T.toSubmodule.map q.toLinearMap, by`.

Introduce and unpack `g _ ⟨v, hv, rfl⟩`. Conclude with `⟨ρ g v, T.apply_mem_toSubmodule g hv, q.isIntertwining _ _ g v⟩⟩`. Set `q' : T.toSubmodule →ₗ[ℂ] S.toSubmodule` to `LinearMap.codRestrict S.toSubmodule (q.toLinearMap ∘ₗ T.toSubmodule.subtype) (fun t => ⟨t, t.2, rfl⟩)`. Establish `hq' : Function.Surjective q'`. Introduce and unpack `⟨_, v, hv, rfl⟩`.

Conclude with `⟨⟨v, hv⟩, rfl⟩`. Establish `hker : LinearMap.ker q' ≤ LinearMap.ker f.toLinearMap`. Introduce `t ht`. Establish `: q (t : V) = 0` using `congrArg Subtype.val (ht : q' t = 0)`. Conclude with `hvan t this`.

Set `e` to `q'.quotKerEquivOfSurjective hq'`. Set `φ : S.toSubmodule →ₗ[ℂ] U` to `((LinearMap.ker q').liftQ f.toLinearMap hker) ∘ₗ e.symm.toLinearMap`. Establish `hφ : ∀ t, φ (q' t) = f t`. Introduce `t`. Use `show (LinearMap.ker q').liftQ f.toLinearMap hker (e.symm (q' t)) = f t`.

Establish `: e.symm (q' t) = Submodule.Quotient.mk t`. Rewrite using `[LinearEquiv.symm_apply_eq]`. Both sides reduce to the same expression. Rewrite using `[this]`. Both sides reduce to the same expression.

Use `⟨S, ⟨φ, fun g => ?_⟩, fun u => ?_⟩` and prove the remaining obligations. Use extensionality with `s`. Take `⟨t, rfl⟩` from `hq' s`. Establish `h1 : S.toRepresentation g (q' t) = q' (T.toRepresentation g t)` using `Subtype.ext (q.isIntertwining _ _ g t).symm`. Use `show φ (S.toRepresentation g (q' t)) = τ g (φ (q' t))`.

Rewrite using `[h1, hφ, hφ]`. Conclude with `f.isIntertwining _ _ g t`. Take `⟨t, rfl⟩` from `hf u`. Conclude with `⟨q' t, hφ t⟩`. Use `left`.

Set `R : Subrepresentation α` to `⟨T.toSubmodule.comap i.toLinearMap, by`. Introduce `g a ha`. Use `show i (α g a) ∈ T.toSubmodule`. Rewrite using `[i.isIntertwining]`. Conclude with `T.apply_mem_toSubmodule g ha⟩`.

Set `j : R.toSubmodule →ₗ[ℂ] T.toSubmodule` to `LinearMap.codRestrict T.toSubmodule (i.toLinearMap ∘ₗ R.toSubmodule.subtype) (fun a => a.2)`. Use `⟨R, ⟨f.toLinearMap ∘ₗ j, fun g => ?_⟩, fun u => ?_⟩` and prove the remaining obligations. Use extensionality with `a show f (j (R.toRepresentation g a)) = τ g (f (j a))`. Establish `h1 : j (R.toRepresentation g a) = T.toRepresentation g (j a)` using `Subtype.ext (i.isIntertwining _ _ g a)`. Rewrite using `[h1]`.

Conclude with `f.isIntertwining _ _ g (j a)`. Establish `hu : u ∈ W'.toSubmodule` using `by rw [h]; trivial`. Take `⟨t, ht, rfl⟩` from `hu`. Take `⟨a, ha⟩` from `hex t ht`. Establish `haR : a ∈ R.toSubmodule` using `by show i a ∈ T.toSubmodule`.

Rewrite using `[ha]`. Conclude with `t.2`. Use `⟨⟨a, haR⟩, ?_⟩` and prove the remaining obligations. Use `show f (j ⟨a, haR⟩) = f t`. Use `congr 1`.

Conclude with `Subtype.ext ha`.
-/
theorem isSubquotient_of_exact_middle (G : Type) [Group G] (U V A Q : Type) [AddCommGroup U] [Module ℂ U]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup A] [Module ℂ A] [AddCommGroup Q] [Module ℂ Q]
    (τ : Representation ℂ G U) (ρ : Representation ℂ G V) (α : Representation ℂ G A)
    (κ : Representation ℂ G Q) (i : α.IntertwiningMap ρ) (q : ρ.IntertwiningMap κ) :
    τ.IsIrreducible → (∀ v, q v = 0 → ∃ a, i a = v) → IsSubquotient τ ρ →
      IsSubquotient τ α ∨ IsSubquotient τ κ := by
  intro hτ hex ⟨T, f, hf⟩

  let W' : Subrepresentation τ :=
    ⟨(LinearMap.ker (q.toLinearMap ∘ₗ T.toSubmodule.subtype)).map f.toLinearMap, by
      rintro g _ ⟨t, ht, rfl⟩
      refine ⟨T.toRepresentation g t, ?_, (f.isIntertwining _ _ g t)⟩
      have ht' : q (t : V) = 0 := ht
      show q (ρ g (t : V)) = 0
      rw [q.isIntertwining, ht', map_zero]⟩
  rcases hτ.eq_bot_or_eq_top W' with h | h
  ·
    right
    have hvan : ∀ t : T.toSubmodule, q (t : V) = 0 → f t = 0 := by
      intro t ht
      have hm : f t ∈ W'.toSubmodule := ⟨t, ht, rfl⟩
      rw [h] at hm
      exact hm
    let S : Subrepresentation κ := ⟨T.toSubmodule.map q.toLinearMap, by
      rintro g _ ⟨v, hv, rfl⟩
      exact ⟨ρ g v, T.apply_mem_toSubmodule g hv, q.isIntertwining _ _ g v⟩⟩
    let q' : T.toSubmodule →ₗ[ℂ] S.toSubmodule :=
      LinearMap.codRestrict S.toSubmodule (q.toLinearMap ∘ₗ T.toSubmodule.subtype)
        (fun t => ⟨t, t.2, rfl⟩)
    have hq' : Function.Surjective q' := by
      rintro ⟨_, v, hv, rfl⟩
      exact ⟨⟨v, hv⟩, rfl⟩
    have hker : LinearMap.ker q' ≤ LinearMap.ker f.toLinearMap := by
      intro t ht
      have : q (t : V) = 0 := congrArg Subtype.val (ht : q' t = 0)
      exact hvan t this
    let e := q'.quotKerEquivOfSurjective hq'
    let φ : S.toSubmodule →ₗ[ℂ] U := ((LinearMap.ker q').liftQ f.toLinearMap hker) ∘ₗ e.symm.toLinearMap
    have hφ : ∀ t, φ (q' t) = f t := by
      intro t
      show (LinearMap.ker q').liftQ f.toLinearMap hker (e.symm (q' t)) = f t
      have : e.symm (q' t) = Submodule.Quotient.mk t := by
        rw [LinearEquiv.symm_apply_eq]; rfl
      rw [this]; rfl
    refine ⟨S, ⟨φ, fun g => ?_⟩, fun u => ?_⟩
    · ext s
      obtain ⟨t, rfl⟩ := hq' s
      have h1 : S.toRepresentation g (q' t) = q' (T.toRepresentation g t) :=
        Subtype.ext (q.isIntertwining _ _ g t).symm
      show φ (S.toRepresentation g (q' t)) = τ g (φ (q' t))
      rw [h1, hφ, hφ]
      exact f.isIntertwining _ _ g t
    · obtain ⟨t, rfl⟩ := hf u
      exact ⟨q' t, hφ t⟩
  ·
    left
    let R : Subrepresentation α := ⟨T.toSubmodule.comap i.toLinearMap, by
      intro g a ha
      show i (α g a) ∈ T.toSubmodule
      rw [i.isIntertwining]
      exact T.apply_mem_toSubmodule g ha⟩
    let j : R.toSubmodule →ₗ[ℂ] T.toSubmodule :=
      LinearMap.codRestrict T.toSubmodule (i.toLinearMap ∘ₗ R.toSubmodule.subtype) (fun a => a.2)
    refine ⟨R, ⟨f.toLinearMap ∘ₗ j, fun g => ?_⟩, fun u => ?_⟩
    · ext a
      show f (j (R.toRepresentation g a)) = τ g (f (j a))
      have h1 : j (R.toRepresentation g a) = T.toRepresentation g (j a) :=
        Subtype.ext (i.isIntertwining _ _ g a)
      rw [h1]
      exact f.isIntertwining _ _ g (j a)
    · have hu : u ∈ W'.toSubmodule := by rw [h]; trivial
      obtain ⟨t, ht, rfl⟩ := hu
      obtain ⟨a, ha⟩ := hex t ht
      have haR : a ∈ R.toSubmodule := by
        show i a ∈ T.toSubmodule
        rw [ha]; exact t.2
      refine ⟨⟨a, haR⟩, ?_⟩
      show f (j ⟨a, haR⟩) = f t
      congr 1
      exact Subtype.ext ha

end GlobalTheory
