import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AevalElimEqRenameLinearSubstitution
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AlgebraicIndependentScaledForms

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

/- English proof (translation)
Take `⟨J, hJ⟩` from `hd.a1 c`. Take `⟨δ, hδ⟩` from `ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence.exists_dual_derivations (K := K) (d.x c) J hJ`. Establish `hy : d.affineCoord c (d.jc c) = 1` using `scalarRatio_self (hd.w_base c)`. Set `ρ : Option (Fin d.D) → Fin (d.D + 2)` to `fun o => (finSuccEquiv (d.D + 1)).symm (some ((finSuccEquiv d.D).symm o))`. Establish `hρ : Function.Injective ρ`.

Introduce `o o' h`. Simplify `h` using `[ρ]`. Establish `hind` using `algebraicIndependent_scaledForms (K := K) (d.affineCoord c) (d.jc c) hy J δ hδ ρ hρ`. Set `e : (Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2) ≃ Option ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Option (Fin d.D))` to `{ toFun := fun x => match x with`. Consider the case `Sum.inl p => some (Sum.inl p)`.

Consider the case `Sum.inr i => (finSuccEquiv (d.D + 1) i).map fun j => Sum.inr (finSuccEquiv d.D j)`. Use `invFun := fun y => match y with`. Consider the case `none => Sum.inr 0`. Consider the case `some (Sum.inl p) => Sum.inl p`. Consider the case `some (Sum.inr o) => Sum.inr (ρ o)`.

Use `left_inv := by`. Introduce and unpack `(p | i)`. Both sides reduce to the same expression. Apply the tactic sequence `rcases h : finSuccEquiv (d.D + 1) i with _ | j <;>`. Use `(finSuccEquiv (d.D + 1)).symm_apply_apply i` as an intermediate fact.

Rewrite `this` using `[h]`. Simplify `this` using `[h, ρ]`. Use `right_inv := by`. Introduce and unpack `(_ | p | o)`. Simplify using the standard rewrite rules.

Both sides reduce to the same expression. Simplify using `[ρ] }`. Set `g` to `(MvPolynomial.renameEquiv K e).trans (MvPolynomial.optionEquivLeft K ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Option (Fin d.D)))`. Set `gr` to `g.toRingEquiv`. Rewrite using `[← RingEquiv.height_comap gr.symm (RingHom.ker (d.scaledSubstitution c))]`.

Use `haveI hk : (RingHom.ker (d.scaledSubstitution c)).IsPrime := RingHom.ker_isPrime _`. Use `haveI : (Ideal.comap gr.symm (RingHom.ker (d.scaledSubstitution c))).IsPrime := Ideal.comap_isPrime _ _`. Use `ReciprocityTheory.CA.height_le_one_of_comap_C_eq_bot _ ?_` and prove the remaining obligations. Rewrite using `[eq_bot_iff]`. Introduce `a ha`.

Rewrite `ha` using `[Ideal.mem_comap, Ideal.mem_comap, RingHom.mem_ker]`. Rewrite using `[Ideal.mem_bot]`. Establish `h2 : (MvPolynomial.optionEquivLeft K ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Option (Fin d.D))).symm (Polynomial.C a) = MvPolynomial.rename some a`. Rewrite using `[AlgEquiv.symm_apply_eq]`. Conclude with `(optionEquivLeft_rename_some' a).symm`.

Establish `h1 : gr.symm (Polynomial.C a) = MvPolynomial.rename (fun s => e.symm (some s)) a` using `by show (MvPolynomial.renameEquiv K e).symm ((MvPolynomial.optionEquivLeft K ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Option (Fin d.D))).symm (Polynomial.C a)) = _`. Rewrite using `[h2, MvPolynomial.renameEquiv_symm, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_rename]`. Both sides reduce to the same expression. Rewrite `ha` using `[h1, scaledSubstitution_eq, MvPolynomial.aeval_rename]`. Establish `hfam : (Sum.elim (fun p => (MvPolynomial.X (some p) : MvPolynomial (Option (Fin (d.D + 2) × Fin (d.N + 1))) (Ω c))) (fun i => MvPolynomial.X none * ∑ j, MvPolynomial.X (some (i, j)) * MvPolynomial.C (d.affineCoord c j))) ∘ (fun s => e.symm (some s)) = Sum.elim (fun p => (MvPolyno …`.

Use function extensionality and compare the values at `s`. Apply the tactic sequence `rcases s with p | o <;> rfl`. Rewrite `ha` using `[hfam]`. Conclude with `(injective_iff_map_eq_zero _).mp hind a ha`.
-/
theorem height_ker_scaledSubstitution_le_one (hd : d.AxH 𝒜) (c : ι) : (RingHom.ker (d.scaledSubstitution c)).height ≤ 1 := by
  classical
  obtain ⟨J, hJ⟩ := hd.a1 c
  obtain ⟨δ, hδ⟩ := ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence.exists_dual_derivations (K := K) (d.x c) J hJ
  have hy : d.affineCoord c (d.jc c) = 1 := scalarRatio_self (hd.w_base c)
  let ρ : Option (Fin d.D) → Fin (d.D + 2) := fun o =>
    (finSuccEquiv (d.D + 1)).symm (some ((finSuccEquiv d.D).symm o))
  have hρ : Function.Injective ρ := by
    intro o o' h
    simpa [ρ] using h
  have hind := algebraicIndependent_scaledForms (K := K) (d.affineCoord c) (d.jc c) hy J δ hδ ρ hρ
  let e : (Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2) ≃
      Option ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Option (Fin d.D)) :=
    { toFun := fun x => match x with
        | Sum.inl p => some (Sum.inl p)
        | Sum.inr i => (finSuccEquiv (d.D + 1) i).map fun j => Sum.inr (finSuccEquiv d.D j)
      invFun := fun y => match y with
        | none => Sum.inr 0
        | some (Sum.inl p) => Sum.inl p
        | some (Sum.inr o) => Sum.inr (ρ o)
      left_inv := by
        rintro (p | i)
        · rfl
        · rcases h : finSuccEquiv (d.D + 1) i with _ | j <;>
          · have := (finSuccEquiv (d.D + 1)).symm_apply_apply i
            rw [h] at this
            simpa [h, ρ] using this
      right_inv := by
        rintro (_ | p | o)
        · simp
        · rfl
        · simp [ρ] }
  let g := (MvPolynomial.renameEquiv K e).trans
    (MvPolynomial.optionEquivLeft K ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Option (Fin d.D)))
  let gr := g.toRingEquiv
  rw [← RingEquiv.height_comap gr.symm (RingHom.ker (d.scaledSubstitution c))]
  haveI hk : (RingHom.ker (d.scaledSubstitution c)).IsPrime := RingHom.ker_isPrime _
  haveI : (Ideal.comap gr.symm (RingHom.ker (d.scaledSubstitution c))).IsPrime := Ideal.comap_isPrime _ _
  refine ReciprocityTheory.CA.height_le_one_of_comap_C_eq_bot _ ?_
  rw [eq_bot_iff]
  intro a ha
  rw [Ideal.mem_comap, Ideal.mem_comap, RingHom.mem_ker] at ha
  rw [Ideal.mem_bot]
  have h2 : (MvPolynomial.optionEquivLeft K ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Option (Fin d.D))).symm
      (Polynomial.C a) = MvPolynomial.rename some a := by
    rw [AlgEquiv.symm_apply_eq]
    exact (optionEquivLeft_rename_some' a).symm
  have h1 : gr.symm (Polynomial.C a) = MvPolynomial.rename (fun s => e.symm (some s)) a := by
    show (MvPolynomial.renameEquiv K e).symm ((MvPolynomial.optionEquivLeft K
      ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Option (Fin d.D))).symm (Polynomial.C a)) = _
    rw [h2, MvPolynomial.renameEquiv_symm, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_rename]
    rfl
  rw [h1, scaledSubstitution_eq, MvPolynomial.aeval_rename] at ha
  have hfam : (Sum.elim (fun p => (MvPolynomial.X (some p) :
        MvPolynomial (Option (Fin (d.D + 2) × Fin (d.N + 1))) (Ω c)))
      (fun i => MvPolynomial.X none *
        ∑ j, MvPolynomial.X (some (i, j)) * MvPolynomial.C (d.affineCoord c j))) ∘
      (fun s => e.symm (some s)) =
      Sum.elim (fun p => (MvPolynomial.X (some p) :
        MvPolynomial (Option (Fin (d.D + 2) × Fin (d.N + 1))) (Ω c)))
      (fun o => MvPolynomial.X none *
        ∑ j, MvPolynomial.X (some (ρ o, j)) * MvPolynomial.C (d.affineCoord c j)) := by
    funext s
    rcases s with p | o <;> rfl
  rw [hfam] at ha
  exact (injective_iff_map_eq_zero _).mp hind a ha

end Data

end ReciprocityTheory.ChartRestriction.G.T0
