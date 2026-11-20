import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

/- English proof (translation)
Use `haveI : Subsingleton ↑(UpperTheory.Gal.G3.sp Ω) := inferInstanceAs (Subsingleton (PrimeSpectrum Ω))`. Establish `pt : ↑(UpperTheory.Gal.G3.sp Ω)` using `show PrimeSpectrum Ω from ⟨⊥, Ideal.bot_prime⟩`. Take `⟨⟨j, y⟩, hq⟩ : ∃ q, (sigmaMk (fun _ : J => W)).symm (p pt) = q` from `⟨_, rfl⟩`. Establish `hy : Sigma.ι (fun _ : J => W) j y = p pt`. Rewrite using `[← sigmaMk_mk, ← hq, Homeomorph.apply_symm_apply]`.

Use `⟨j, IsOpenImmersion.lift (Sigma.ι (fun _ : J => W) j) p ?_, (IsOpenImmersion.lift_fac _ _ _).symm⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨z, rfl⟩`. Take `rfl : z = pt` from `Subsingleton.elim _ _`. Conclude with `⟨y, hy⟩`.
-/
private theorem exists_factor {W : Scheme.{0}} {J : Type} (Ω : Type) [Field Ω]
    (p : UpperTheory.Gal.G3.sp Ω ⟶ ∐ (fun _ : J => W)) :
    ∃ (j : J) (x : UpperTheory.Gal.G3.sp Ω ⟶ W), p = x ≫ Sigma.ι (fun _ : J => W) j := by
  haveI : Subsingleton ↑(UpperTheory.Gal.G3.sp Ω) := inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
  have pt : ↑(UpperTheory.Gal.G3.sp Ω) := show PrimeSpectrum Ω from ⟨⊥, Ideal.bot_prime⟩
  obtain ⟨⟨j, y⟩, hq⟩ : ∃ q, (sigmaMk (fun _ : J => W)).symm (p pt) = q := ⟨_, rfl⟩
  have hy : Sigma.ι (fun _ : J => W) j y = p pt := by
    rw [← sigmaMk_mk, ← hq, Homeomorph.apply_symm_apply]
  refine ⟨j, IsOpenImmersion.lift (Sigma.ι (fun _ : J => W) j) p ?_,
    (IsOpenImmersion.lift_fac _ _ _).symm⟩
  rintro _ ⟨z, rfl⟩
  obtain rfl : z = pt := Subsingleton.elim _ _
  exact ⟨y, hy⟩

/- English proof (translation)
Introduce `hIso Z Y W s _ _ c J _ σ hσ hpts`. Use `⟨hσ, ?_⟩` and prove the remaining obligations. Set `e` to `Limits.Sigma.desc (fun j : J => pullback.lift (σ j) (𝟙 W) (by rw [Category.id_comp]; exact hσ j))`. Establish `hι : ∀ j, Sigma.ι (fun _ : J => W) j ≫ e = pullback.lift (σ j) (𝟙 W) (by rw [Category.id_comp]; exact hσ j)` using `fun j => Sigma.ι_desc _ _`. Establish `hlift : ∀ j, Etale (pullback.lift (σ j) (𝟙 W) (by rw [Category.id_comp]; exact hσ j) : W ⟶ pullback s c)`.

Introduce `j`. Use `haveI : Etale (pullback.lift (σ j) (𝟙 W) (by rw [Category.id_comp]; exact hσ j) ≫ pullback.snd s c) := by`. Rewrite using `[pullback.lift_snd]`. Use `infer_instance`. Conclude with `Etale.of_comp _ (pullback.snd s c)`.

Use `haveI : IsZariskiLocalAtSource @Etale := HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Etale)`. Use `haveI : Etale e := IsZariskiLocalAtSource.sigmaDesc (P := @Etale) hlift`. Use `show IsIso e`. Apply `hIso e` to reduce the goal to its premises. Introduce `Ω _ _ z`.

Take `⟨j, hj, huniq⟩` from `hpts Ω (z ≫ pullback.snd s c) (z ≫ pullback.fst s c) (by rw [Category.assoc, Category.assoc, pullback.condition])`. Establish `hz : (z ≫ pullback.snd s c) ≫ Sigma.ι (fun _ : J => W) j ≫ e = z`. Rewrite using `[hι]`. Apply `pullback.hom_ext` to reduce the goal to its premises. Simplify using `only [Category.assoc, pullback.lift_fst]`.

Rewrite using `[← Category.assoc]`. Conclude with `hj`. Simplify using `only [Category.assoc, pullback.lift_snd, Category.comp_id]`. Use `⟨(z ≫ pullback.snd s c) ≫ Sigma.ι (fun _ : J => W) j, by rw [Category.assoc]; exact hz, fun q hq => ?_⟩` and prove the remaining obligations. Take `⟨j', x', rfl⟩` from `exists_factor Ω q`.

Rewrite `hq` using `[Category.assoc, hι]`. Establish `hs` using `congrArg (· ≫ pullback.snd s c) hq`. Establish `hf` using `congrArg (· ≫ pullback.fst s c) hq`. Simplify using `only [Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.comp_id] at hs hf`. Establish `hjj : j' = j` using `huniq j' (by rw [← hs]; exact hf)`.

Rewrite using `[hjj, hs]`.
-/
theorem UpperTheory.Gal.G3.pSplitsPts :
    IsoPts → SplitsPts := by
  intro hIso Z Y W s _ _ c J _ σ hσ hpts
  refine ⟨hσ, ?_⟩
  let e := Limits.Sigma.desc (fun j : J =>
    pullback.lift (σ j) (𝟙 W) (by rw [Category.id_comp]; exact hσ j))
  have hι : ∀ j, Sigma.ι (fun _ : J => W) j ≫ e =
      pullback.lift (σ j) (𝟙 W) (by rw [Category.id_comp]; exact hσ j) :=
    fun j => Sigma.ι_desc _ _
  have hlift : ∀ j, Etale (pullback.lift (σ j) (𝟙 W)
      (by rw [Category.id_comp]; exact hσ j) : W ⟶ pullback s c) := by
    intro j
    haveI : Etale (pullback.lift (σ j) (𝟙 W) (by rw [Category.id_comp]; exact hσ j) ≫
        pullback.snd s c) := by
      rw [pullback.lift_snd]; infer_instance
    exact Etale.of_comp _ (pullback.snd s c)
  haveI : IsZariskiLocalAtSource @Etale :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Etale)
  haveI : Etale e := IsZariskiLocalAtSource.sigmaDesc (P := @Etale) hlift
  show IsIso e
  apply hIso e
  intro Ω _ _ z
  obtain ⟨j, hj, huniq⟩ := hpts Ω (z ≫ pullback.snd s c) (z ≫ pullback.fst s c)
    (by rw [Category.assoc, Category.assoc, pullback.condition])
  have hz : (z ≫ pullback.snd s c) ≫ Sigma.ι (fun _ : J => W) j ≫ e = z := by
    rw [hι]
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]
      rw [← Category.assoc]
      exact hj
    · simp only [Category.assoc, pullback.lift_snd, Category.comp_id]
  refine ⟨(z ≫ pullback.snd s c) ≫ Sigma.ι (fun _ : J => W) j,
    by rw [Category.assoc]; exact hz, fun q hq => ?_⟩
  obtain ⟨j', x', rfl⟩ := exists_factor Ω q
  rw [Category.assoc, hι] at hq
  have hs := congrArg (· ≫ pullback.snd s c) hq
  have hf := congrArg (· ≫ pullback.fst s c) hq
  simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.comp_id] at hs hf
  have hjj : j' = j := huniq j' (by rw [← hs]; exact hf)
  rw [hjj, hs]
