import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

/- English proof (translation)
The claim follows from `inferInstanceAs (Subsingleton (PrimeSpectrum Ω))`.
-/
private theorem sp_subsingleton (Ω : Type) [Field Ω] : Subsingleton ↑(UpperTheory.Gal.G3.sp Ω) :=
  inferInstanceAs (Subsingleton (PrimeSpectrum Ω))

/- English proof (translation)
Use `haveI := sp_subsingleton Ω`. Establish `p : ↑(UpperTheory.Gal.G3.sp Ω)` using `show PrimeSpectrum Ω from ⟨⊥, Ideal.bot_prime⟩`. Take `⟨⟨j, y⟩, hq⟩ : ∃ q, (sigmaMk (fun _ : J => W)).symm (u p) = q` from `⟨_, rfl⟩`. Establish `hy : Sigma.ι (fun _ : J => W) j y = u p`. Rewrite using `[← sigmaMk_mk, ← hq, Homeomorph.apply_symm_apply]`.

Use `⟨j, IsOpenImmersion.lift (Sigma.ι (fun _ : J => W) j) u ?_, IsOpenImmersion.lift_fac _ _ _⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨z, rfl⟩`. Take `rfl : z = p` from `Subsingleton.elim _ _`. Conclude with `⟨y, hy⟩`.
-/
private theorem exists_factor_ι {J : Type} {W : Scheme.{0}} (Ω : Type) [Field Ω]
    (u : UpperTheory.Gal.G3.sp Ω ⟶ ∐ (fun _ : J => W)) :
    ∃ (j : J) (x : UpperTheory.Gal.G3.sp Ω ⟶ W), x ≫ Sigma.ι (fun _ : J => W) j = u := by
  haveI := sp_subsingleton Ω
  have p : ↑(UpperTheory.Gal.G3.sp Ω) := show PrimeSpectrum Ω from ⟨⊥, Ideal.bot_prime⟩
  obtain ⟨⟨j, y⟩, hq⟩ : ∃ q, (sigmaMk (fun _ : J => W)).symm (u p) = q := ⟨_, rfl⟩
  have hy : Sigma.ι (fun _ : J => W) j y = u p := by
    rw [← sigmaMk_mk, ← hq, Homeomorph.apply_symm_apply]
  refine ⟨j, IsOpenImmersion.lift (Sigma.ι (fun _ : J => W) j) u ?_,
    IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨z, rfl⟩
  obtain rfl : z = p := Subsingleton.elim _ _
  exact ⟨y, hy⟩

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `he` using `isEmpty_of_commSq_sigmaι_of_ne (g := fun _ : J => W) ⟨h⟩ hne`. Conclude with `he.false (show PrimeSpectrum Ω from ⟨⊥, Ideal.bot_prime⟩)`.
-/
private theorem index_eq_of_ι {J : Type} {W : Scheme.{0}} (Ω : Type) [Field Ω] {j j' : J}
    {x x' : UpperTheory.Gal.G3.sp Ω ⟶ W}
    (h : x ≫ Sigma.ι (fun _ : J => W) j = x' ≫ Sigma.ι (fun _ : J => W) j') : j = j' := by
  by_contra hne
  have he := isEmpty_of_commSq_sigmaι_of_ne (g := fun _ : J => W) ⟨h⟩ hne
  exact he.false (show PrimeSpectrum Ω from ⟨⊥, Ideal.bot_prime⟩)

/- English proof (translation)
Introduce `Z Y W s c J σ hs Ω _ x y hxy`. Take `⟨hσ, hiso⟩` from `hs`. Use `haveI := hiso`. Set `e` to `Limits.Sigma.desc (fun j : J => pullback.lift (σ j) (𝟙 W) (by rw [Category.id_comp]; exact hσ j))`. Establish `hι : ∀ j, Sigma.ι (fun _ : J => W) j ≫ e = pullback.lift (σ j) (𝟙 W) (by rw [Category.id_comp]; exact hσ j)` using `fun j => Sigma.ι_desc _ _`.

Take `⟨j, x', hx'⟩` from `exists_factor_ι Ω (pullback.lift y x hxy ≫ inv e)`. Establish `h1 : x' ≫ Sigma.ι (fun _ : J => W) j ≫ e = pullback.lift y x hxy`. Rewrite using `[← Category.assoc, hx', Category.assoc, IsIso.inv_hom_id, Category.comp_id]`. Rewrite `h1` using `[hι]`. Establish `hsnd` using `congrArg (· ≫ pullback.snd s c) h1`.

Establish `hfst` using `congrArg (· ≫ pullback.fst s c) h1`. Simplify using `only [Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.comp_id] at hsnd hfst`. Rewrite `hfst` using `[hsnd]`. Use `⟨j, hfst, fun j' hj' => ?_⟩` and prove the remaining obligations. Establish `hj'' : x ≫ σ j' = y` using `hj'`.

Apply `index_eq_of_ι Ω (x := x) (x' := x')` to reduce the goal to its premises. Rewrite using `[hx']`. Apply `(cancel_mono e).mp` to reduce the goal to its premises. Rewrite using `[Category.assoc, hι, Category.assoc, IsIso.inv_hom_id, Category.comp_id]`. Apply `pullback.hom_ext` to reduce the goal to its premises.

Rewrite using `[Category.assoc, pullback.lift_fst, pullback.lift_fst, hj'']`. Rewrite using `[Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.comp_id]`.
-/
theorem UpperTheory.Gal.G3.pPtsOfSplits :
    PtsOfSplits := by
  intro Z Y W s c J σ hs Ω _ x y hxy
  obtain ⟨hσ, hiso⟩ := hs
  haveI := hiso
  let e := Limits.Sigma.desc (fun j : J =>
    pullback.lift (σ j) (𝟙 W) (by rw [Category.id_comp]; exact hσ j))
  have hι : ∀ j, Sigma.ι (fun _ : J => W) j ≫ e =
      pullback.lift (σ j) (𝟙 W) (by rw [Category.id_comp]; exact hσ j) :=
    fun j => Sigma.ι_desc _ _
  obtain ⟨j, x', hx'⟩ := exists_factor_ι Ω (pullback.lift y x hxy ≫ inv e)
  have h1 : x' ≫ Sigma.ι (fun _ : J => W) j ≫ e = pullback.lift y x hxy := by
    rw [← Category.assoc, hx', Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [hι] at h1
  have hsnd := congrArg (· ≫ pullback.snd s c) h1
  have hfst := congrArg (· ≫ pullback.fst s c) h1
  simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.comp_id] at hsnd hfst
  rw [hsnd] at hfst
  refine ⟨j, hfst, fun j' hj' => ?_⟩
  have hj'' : x ≫ σ j' = y := hj'
  apply index_eq_of_ι Ω (x := x) (x' := x')
  rw [hx']
  apply (cancel_mono e).mp
  rw [Category.assoc, hι, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, hj'']
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.comp_id]
