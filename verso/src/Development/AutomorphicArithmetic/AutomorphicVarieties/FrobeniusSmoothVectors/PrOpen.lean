import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PresDefs

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

/- English proof (translation)
Introduce `l _ k _ _ F C₀ n hF O _ _ R _ _ _ B hB`. Establish `hent : ∀ i j, IsLocallyConstant fun s => ((B.bar O).r s).mat i j` using `fun i j => by`. Establish `hk : ∀ a ∈ maximalIdeal R ^ 1, (res O R : R →+* ResidueField O) a = 0` using `fun a ha => by`. Rewrite `ha` using `[pow_one]`. Conclude with `(res_eq_zero_iff O R a).2 ha`.

Conclude with `(hB i j 1).comp (Ideal.Quotient.lift _ (res O R : R →+* ResidueField O) hk)`. Establish `hmat : IsLocallyConstant fun s => ((B.bar O).r s).mat`. Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `x`. Establish `h : ∀ᶠ y in nhds x, ∀ i j, ((B.bar O).r y).mat i j = ((B.bar O).r x).mat i j` using `Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => (hent i j).eventually_eq x`.

Conclude with `h.mono fun y hy => Matrix.ext hy`. Establish `hr : IsOpen ((B.bar O).r.ker : Set F.Γ)`. Establish `e : ((B.bar O).r.ker : Set F.Γ) = {s | ((B.bar O).r s).mat = 1} ∩ (F.del.ker : Set F.Γ)`. Use extensionality with `s`. Prove the components needed by the constructor for the conclusion.

Introduce `hs`. Establish `hs' : (B.bar O).r s = 1` using `hs`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show ((B.bar O).r s).mat = 1`. Rewrite using `[hs']`.

Both sides reduce to the same expression. Use `show F.del s = 1`. Rewrite using `[← (B.bar O).nu s, hs']`. Both sides reduce to the same expression. Introduce and unpack `⟨h1, h2⟩ show (B.bar O).r s = 1`.

Use `SemidirectProduct.ext (Units.ext h1) ?_` and prove the remaining obligations. Rewrite using `[(B.bar O).nu s]`. Conclude with `h2`. Rewrite using `[e]`. Conclude with `(hmat.isOpen_fiber 1).inter hF.del_open`.

Use `⟨hr, Subgroup.isOpen_mono (fun s hs => ?_) hr, hmat⟩` and prove the remaining obligations. Establish `hs' : (B.bar O).r s = 1` using `hs`. Use `show GG.ad n _ ((B.bar O).r s) = 1`. Rewrite using `[hs', map_one]`.
-/
theorem UpperTheory.V.Fr.pr_open :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (B : Box F n R), B.Cont (maximalIdeal R) → IsOpen ((B.bar O).r.ker : Set F.Γ) ∧ IsOpen ((B.bar O).ad.ker : Set F.Γ) ∧ IsLocallyConstant fun s => ((B.bar O).r s).mat := by
  intro l _ k _ _ F C₀ n hF O _ _ R _ _ _ B hB
  have hent : ∀ i j, IsLocallyConstant fun s => ((B.bar O).r s).mat i j := fun i j => by
    have hk : ∀ a ∈ maximalIdeal R ^ 1, (res O R : R →+* ResidueField O) a = 0 := fun a ha => by
      rw [pow_one] at ha
      exact (res_eq_zero_iff O R a).2 ha
    exact (hB i j 1).comp (Ideal.Quotient.lift _ (res O R : R →+* ResidueField O) hk)
  have hmat : IsLocallyConstant fun s => ((B.bar O).r s).mat := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have h : ∀ᶠ y in nhds x, ∀ i j, ((B.bar O).r y).mat i j = ((B.bar O).r x).mat i j :=
      Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => (hent i j).eventually_eq x
    exact h.mono fun y hy => Matrix.ext hy
  have hr : IsOpen ((B.bar O).r.ker : Set F.Γ) := by
    have e : ((B.bar O).r.ker : Set F.Γ) =
        {s | ((B.bar O).r s).mat = 1} ∩ (F.del.ker : Set F.Γ) := by
      ext s
      constructor
      · intro hs
        have hs' : (B.bar O).r s = 1 := hs
        refine ⟨?_, ?_⟩
        · show ((B.bar O).r s).mat = 1
          rw [hs']
          rfl
        · show F.del s = 1
          rw [← (B.bar O).nu s, hs']
          rfl
      · rintro ⟨h1, h2⟩
        show (B.bar O).r s = 1
        refine SemidirectProduct.ext (Units.ext h1) ?_
        rw [(B.bar O).nu s]
        exact h2
    rw [e]
    exact (hmat.isOpen_fiber 1).inter hF.del_open
  refine ⟨hr, Subgroup.isOpen_mono (fun s hs => ?_) hr, hmat⟩
  have hs' : (B.bar O).r s = 1 := hs
  show GG.ad n _ ((B.bar O).r s) = 1
  rw [hs', map_one]
