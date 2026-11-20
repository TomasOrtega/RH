import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SplitAt

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

/- English proof (translation)
Introduce `H M _ _ _ _ _ _ ρ x hx`. Establish `hmul : ∀ a b : H, ρ (a * b) x = ρ a (ρ b x)` using `fun a b => by`. Rewrite using `[map_mul, Module.End.mul_apply]`. Set `S : Subgroup H` to `{ carrier := {h | ρ h x = x} mul_mem' := fun {a b} ha hb => by`. Establish `ha' : ρ a x = x` using `ha`.

Establish `hb' : ρ b x = x` using `hb`. Use `show ρ (a * b) x = x`. Rewrite using `[hmul, hb', ha']`. Use the proof step `one_mem' := by show ρ 1 x = x`. Simplify using the standard rewrite rules.

Use the proof step `inv_mem' := fun {a} ha => by`. Establish `ha' : ρ a x = x` using `ha`. Use `show ρ a⁻¹ x = x`. Use `conv_lhs => rw [← ha']`. Rewrite using `[← hmul]`.

Simplify using `}`. Establish `hSo : IsOpen (S : Set H)` using `Subgroup.isOpen_of_mem_nhds S hx`. Use `haveI : Finite (H ⧸ S) := Subgroup.quotient_finite_of_isOpen S hSo`. Use `haveI : Fintype (H ⧸ S) := Fintype.ofFinite _`. Establish `key : ∀ k k' : H, (k : H ⧸ S) = k' → ρ k x = ρ k' x`.

Introduce `k k' h`. Establish `h2 : ρ (k⁻¹ * k') x = x` using `QuotientGroup.eq.mp h`. Combine the equalities or inequalities in the displayed calculation. Use `⟨Finset.univ.image (fun q : H ⧸ S => (Quotient.out q : H)), ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ ((1 : H) : H ⧸ S))⟩, ?_⟩` and prove the remaining obligations. Introduce `h`.

Establish `hinj : Function.Injective (fun q : H ⧸ S => (Quotient.out q : H))` using `fun a b hab => Quotient.out_injective hab`. Rewrite using `[Finset.sum_image hinj.injOn, map_sum]`. Use `Fintype.sum_equiv (ι := H ⧸ S) (κ := H ⧸ S) (MulAction.toPerm h) _ _ ?_` and prove the remaining obligations. Introduce `q`. Use `show ρ h (ρ (Quotient.out q) x) = ρ (Quotient.out (h • q)) x`.

Rewrite using `[← hmul]`. Apply `key` to reduce the goal to its premises. Rewrite using `[QuotientGroup.out_eq']`. Use `conv_rhs => rw [← QuotientGroup.out_eq' q]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.ConvolutionTheory.R2.H.avg :
    ∀ (H M : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H] [AddCommGroup M] [Module ℂ M]
      (ρ : H →* Module.End ℂ M) (x : M), (∀ᶠ h in 𝓝 (1 : H), ρ h x = x) →
      ∃ s : Finset H, s.Nonempty ∧ ∀ h, ρ h (∑ k ∈ s, ρ k x) = ∑ k ∈ s, ρ k x := by
  intro H M _ _ _ _ _ _ ρ x hx
  have hmul : ∀ a b : H, ρ (a * b) x = ρ a (ρ b x) := fun a b => by
    rw [map_mul, Module.End.mul_apply]
  let S : Subgroup H :=
    { carrier := {h | ρ h x = x}
      mul_mem' := fun {a b} ha hb => by
        have ha' : ρ a x = x := ha
        have hb' : ρ b x = x := hb
        show ρ (a * b) x = x
        rw [hmul, hb', ha']
      one_mem' := by
        show ρ 1 x = x
        simp
      inv_mem' := fun {a} ha => by
        have ha' : ρ a x = x := ha
        show ρ a⁻¹ x = x
        conv_lhs => rw [← ha']
        rw [← hmul]
        simp }
  have hSo : IsOpen (S : Set H) := Subgroup.isOpen_of_mem_nhds S hx
  haveI : Finite (H ⧸ S) := Subgroup.quotient_finite_of_isOpen S hSo
  haveI : Fintype (H ⧸ S) := Fintype.ofFinite _
  have key : ∀ k k' : H, (k : H ⧸ S) = k' → ρ k x = ρ k' x := by
    intro k k' h
    have h2 : ρ (k⁻¹ * k') x = x := QuotientGroup.eq.mp h
    calc ρ k x = ρ k (ρ (k⁻¹ * k') x) := by rw [h2]
      _ = ρ k' x := by rw [← hmul]; simp
  refine ⟨Finset.univ.image (fun q : H ⧸ S => (Quotient.out q : H)),
    ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ ((1 : H) : H ⧸ S))⟩, ?_⟩
  intro h
  have hinj : Function.Injective (fun q : H ⧸ S => (Quotient.out q : H)) :=
    fun a b hab => Quotient.out_injective hab
  rw [Finset.sum_image hinj.injOn, map_sum]
  refine Fintype.sum_equiv (ι := H ⧸ S) (κ := H ⧸ S) (MulAction.toPerm h) _ _ ?_
  intro q
  show ρ h (ρ (Quotient.out q) x) = ρ (Quotient.out (h • q)) x
  rw [← hmul]
  apply key
  rw [QuotientGroup.out_eq']
  conv_rhs => rw [← QuotientGroup.out_eq' q]
  rfl
