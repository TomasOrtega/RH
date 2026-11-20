import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TupleActions.InstMulActionTup

open CategoryTheory

namespace UpperTheory.V.Af.BA.ResolutionExactness

variable {Γ : Type} [Group Γ]

/- English proof (translation)
Use extensionality with `x`. Conclude with `h.apply_apply_eq_zero x`.
-/
private theorem comp_zero_of {A B C : Rep.{0} ℂ Γ} {f : A ⟶ B} {g : B ⟶ C}
    (h : Function.Exact f.hom g.hom) : f ≫ g = 0 := by
  ext x
  exact h.apply_apply_eq_zero x

/- English proof (translation)
Conclude with `(forget₂ (Rep ℂ Γ) (ModuleCat ℂ)).reflects_exact_of_faithful _ ((ShortComplex.moduleCat_exact_iff _).2 fun x hx => (h x).1 hx)`.
-/
private theorem exact_of {A B C : Rep.{0} ℂ Γ} {f : A ⟶ B} {g : B ⟶ C} (w : f ≫ g = 0)
    (h : Function.Exact f.hom g.hom) : (ShortComplex.mk f g w).Exact := by
  exact (forget₂ (Rep ℂ Γ) (ModuleCat ℂ)).reflects_exact_of_faithful _
    ((ShortComplex.moduleCat_exact_iff _).2 fun x hx => (h x).1 hx)

set_option backward.isDefEq.respectTransparency false in
/- English proof (translation)
Introduce `Γ _ X d ε hX hε h0 hd`. Establish `hdd : ∀ p, d (p + 1) ≫ d p = 0` using `fun p => comp_zero_of (hd p)`. Set `K : ChainComplex (Rep ℂ Γ) ℕ` to `ChainComplex.of X d hdd`. Establish `hK : ∀ j, K.d (j + 1) j = d j` using `fun j => by simp [K]`. Establish `hK0 : K.d 1 0 ≫ ε = 0`.

Rewrite using `[hK 0]`. Conclude with `comp_zero_of h0`. Set `π : K ⟶ (ChainComplex.single₀ (Rep ℂ Γ)).obj (Rep.trivial ℂ Γ ℂ)` to `(ChainComplex.toSingle₀Equiv _ _).symm ⟨ε, hK0⟩`. Establish `hπ0 : π.f 0 = ε` using `by simp [π]`. Set `P : ProjectiveResolution (Rep.trivial ℂ Γ ℂ)` to `{ complex := K projective := hX π := π quasiIso := ⟨fun n => by`.

Consider the cases of `n with`. Consider the case `zero`. Rewrite using `[ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']`. Use `⟨exact_of _ ?_, ?_⟩` and prove the remaining obligations. Use `show Function.Exact (K.d 1 0).hom (π.f 0).hom`.

Rewrite using `[hπ0, hK 0]`. Conclude with `h0`. Use `show Epi (π.f 0)`. Rewrite using `[hπ0, Rep.epi_iff_surjective]`. Conclude with `hε`.

Apply the tactic sequence `all_goals rfl`. Consider the case `succ m`. Rewrite using `[quasiIsoAt_iff_exactAt']`. Rewrite using `[HomologicalComplex.exactAt_iff' _ (m + 2) (m + 1) m (by simp) (by simp)]`. Use `exact_of _ ?_` and prove the remaining obligations.

Use `show Function.Exact (K.d (m + 2) (m + 1)).hom (K.d (m + 1) m).hom`. Rewrite using `[hK, hK]`. Conclude with `hd m`. Apply `ChainComplex.exactAt_succ_single_obj⟩ }` to reduce the goal to its premises. Use `⟨P, fun p => ⟨Iso.refl _⟩, fun e he0 he => ?_⟩` and prove the remaining obligations.

Use `⟨ChainComplex.ofHom (X := K) (Y := K) e (fun i => by rw [hK]; exact he i), ?_, fun p hp => hp⟩` and prove the remaining obligations. Apply `(ChainComplex.toSingle₀Equiv _ _).injective` to reduce the goal to its premises. Use `ext1`. Simplify using `[P, hπ0, he0]`.
-/
private theorem main : UpperTheory.V.Af.BA.ResOf := by
  intro Γ _ X d ε hX hε h0 hd
  have hdd : ∀ p, d (p + 1) ≫ d p = 0 := fun p => comp_zero_of (hd p)
  let K : ChainComplex (Rep ℂ Γ) ℕ := ChainComplex.of X d hdd
  have hK : ∀ j, K.d (j + 1) j = d j := fun j => by simp [K]
  have hK0 : K.d 1 0 ≫ ε = 0 := by
    rw [hK 0]
    exact comp_zero_of h0
  let π : K ⟶ (ChainComplex.single₀ (Rep ℂ Γ)).obj (Rep.trivial ℂ Γ ℂ) :=
    (ChainComplex.toSingle₀Equiv _ _).symm ⟨ε, hK0⟩
  have hπ0 : π.f 0 = ε := by simp [π]
  let P : ProjectiveResolution (Rep.trivial ℂ Γ ℂ) :=
    { complex := K
      projective := hX
      π := π
      quasiIso := ⟨fun n => by
        cases n with
        | zero =>
          rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
          · refine ⟨exact_of _ ?_, ?_⟩
            · show Function.Exact (K.d 1 0).hom (π.f 0).hom
              rw [hπ0, hK 0]
              exact h0
            · show Epi (π.f 0)
              rw [hπ0, Rep.epi_iff_surjective]
              exact hε
          all_goals rfl
        | succ m =>
          rw [quasiIsoAt_iff_exactAt']
          · rw [HomologicalComplex.exactAt_iff' _ (m + 2) (m + 1) m (by simp) (by simp)]
            refine exact_of _ ?_
            show Function.Exact (K.d (m + 2) (m + 1)).hom (K.d (m + 1) m).hom
            rw [hK, hK]
            exact hd m
          · apply ChainComplex.exactAt_succ_single_obj⟩ }
  refine ⟨P, fun p => ⟨Iso.refl _⟩, fun e he0 he => ?_⟩
  refine ⟨ChainComplex.ofHom (X := K) (Y := K) e (fun i => by rw [hK]; exact he i), ?_, fun p hp => hp⟩
  apply (ChainComplex.toSingle₀Equiv _ _).injective
  ext1
  simp [P, hπ0, he0]

end UpperTheory.V.Af.BA.ResolutionExactness

/- English proof (translation)
The claim follows from `UpperTheory.V.Af.BA.ResolutionExactness.main`.
-/
theorem UpperTheory.repResolution_exists :
    UpperTheory.V.Af.BA.ResOf :=
  UpperTheory.V.Af.BA.ResolutionExactness.main
