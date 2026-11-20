import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.XSmulSucc
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.FCechLoc
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.FibInit
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.FRiCalc

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
universe w w' v u v' u' v'' u''

namespace CrystallineSemistableComparison.B

/- English proof (translation)
Use function extensionality and compare the values at `s`. Express the relevant statement in the definitionally equal form `∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (H.map (GlobalTheory.CatH.toLast i s)).hom (ε _ x) = 0`. Rewrite using `[Fin.sum_univ_two, hε, hε]`. Simplify using the standard rewrite rules.
-/
theorem zar_d_aug {R : Type} [CommRing R] {D : Type*} [Category D] (H : D ⥤ ModuleCat.{w} R)
    {M : Type w'} [AddCommGroup M] [Module R M] (ε : ∀ X, M →ₗ[R] H.obj X)
    (hε : ∀ {X Y : D} (f : X ⟶ Y) x, (H.map f).hom (ε X x) = ε Y x) (x : M) :
    d H 0 (aug H ε x) = 0 := by
  funext s
  change ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (H.map (GlobalTheory.CatH.toLast i s)).hom (ε _ x) = 0
  rw [Fin.sum_univ_two, hε, hε]
  simp

/- English proof (translation)
Establish `hVe : ∀ S (e : E) (f : obj S ⟶ e), ∀ k ∈ S.1, V k (φ ≫ ψ e)`. Introduce `S e f k hk`. Use `hV k _ (eqToHom (eo S).symm ≫ τ.map f) (h1 S.1 k hk)` as an intermediate fact. Rewrite `this` using `[Category.assoc, ← Category.assoc (lam S.1), ← hobj, hψ]`. Then use the resulting hypothesis. Establish `hsub : ∀ S (e : E), Subsingleton (obj S ⟶ e)`.

Introduce `S e`. Use `⟨fun f g => τ.map_injective ?_⟩` and prove the remaining obligations. Establish `hf : lam S.1 ≫ (eqToHom (eo S).symm ≫ τ.map f) = ψ e`. Rewrite using `[← Category.assoc, ← hobj, hψ]`. Establish `hg : lam S.1 ≫ (eqToHom (eo S).symm ≫ τ.map g) = ψ e`.

Rewrite using `[← Category.assoc, ← hobj, hψ]`. Use `(h2 S.1 _ (ψ e) (hVe S e f)).unique hf hg` as an intermediate fact. Conclude with `(cancel_epi _).1 this`. Establish `hex : ∀ S (e : E), (∀ k ∈ S.1, V k (φ ≫ ψ e)) → Nonempty (obj S ⟶ e)`. Introduce `S e h`.

Take `⟨χ, hχ, -⟩` from `h2 S.1 _ (ψ e) h`. Take `⟨f, -⟩` from `hfull (obj S) e (eqToHom (eo S) ≫ χ) (by rw [hobj]; simpa using hχ)`. Conclude with `⟨f⟩`. Set `U : E ⥤ {S : Finset (Fin m) // S.Nonempty}` to `{ obj := fun e => ⟨Finset.univ.filter (fun k => V k (φ ≫ ψ e)), by`. Take `⟨k, hk⟩` from `hE e`.

Conclude with `⟨k, by simpa using hk⟩⟩`. Use `map := fun {e e'} f => homOfLE (by`. Introduce `k hk`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢`. Use `hV k _ (τ.map f) hk` as an intermediate fact.

Rewrite using `[Category.assoc, hψ] at this) }` and apply the resulting hypothesis. Establish `hU : ∀ (S : {S : Finset (Fin m) // S.Nonempty}) (e : E), S.1 ⊆ (U.obj e).1 ↔ ∀ k ∈ S.1, V k (φ ≫ ψ e)`. Introduce `S e`. Prove the components needed by the constructor for the conclusion. Introduce `h k hk`.

Use `h hk` as an intermediate fact. Simplify `this` using `[U]`. Introduce `h k hk`. Simplify `h k hk` using `[U]`. Set `Λ : {S : Finset (Fin m) // S.Nonempty} ⥤ E` to `{ obj := obj map := fun {S S'} h => Classical.choice (hex S (obj S') (fun k hk => hVe S' (obj S') (𝟙 _) k (leOfHom h hk))) map_id := fun S => (hsub S (obj S)).elim _ _ map_comp := fun {S _ _} _ _ => (hsub S _).elim _ _ }`.

Set `adjn : Λ ⊣ U` to `Adjunction.mkOfHomEquiv { homEquiv := fun S e => { toFun := fun f => homOfLE ((hU S e).2 (hVe S e f)) invFun := fun h => Classical.choice (hex S e ((hU S e).1 (leOfHom h))) left_inv := fun f => (hsub S e).elim _ _ right_inv := fun h => Subsingleton.elim _ _ } homEquiv_naturality_ …`. Establish `hA` using `CrystallineSemistableComparison.P.adj (τ ⋙ F) Λ U adjn`. Establish `hB` using `CrystallineSemistableComparison.B.P.cech_loc F T' Lc lam (Λ ⋙ τ) eo (fun S S' h => by`. Rewrite using `[← Category.assoc, ← hobj, ← hobj]`. Conclude with `hψ (Λ.map h)) hL`.

Establish `hup : ∀ n, UpTo (1 : R) ((Mor.restrict (τ ⋙ F) Λ).hom.mapH n)` using `fun n => ((CrystallineSemistableComparison.P.upTo_alg ((Mor.restrict (τ ⋙ F) Λ).hom.mapH n) LinearMap.id 1 1).2.2.2.2).2 (hA n)`. Establish `hd : ∀ x, (cx (τ ⋙ F)).d 0 (aug (τ ⋙ F) (fun e => (F.map (ψ e)).hom) x) = 0` using `zar_d_aug (τ ⋙ F) _ (fun {e e'} f x => by`. Express the relevant statement in the definitionally equal form `(F.map (τ.map f)).hom ((F.map (ψ e)).hom x) = (F.map (ψ e')).hom x`. Rewrite using `[← hψ f, F.map_comp]`. Use the proof step `rfl)`.

Establish `e1 : (Mor.restrict (τ ⋙ F) Λ).hom.f 0 ∘ₗ aug (τ ⋙ F) (fun e => (F.map (ψ e)).hom) = aug ((Λ ⋙ τ) ⋙ F) fun S => (F.map (lam S.1 ≫ eqToHom (eo S).symm)).hom`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `x`. Use function extensionality and compare the values at `s`. Express the relevant statement in the definitionally equal form `(F.map (ψ (obj (s.obj (Fin.last 0))))).hom x = _`.

Rewrite using `[hobj]`. Both sides reduce to the same expression. Use `((CrystallineSemistableComparison.P.res_transfer (Mor.restrict (τ ⋙ F) Λ).hom (aug (τ ⋙ F) fun e => (F.map (ψ e)).hom) 1 1 hup).2 hd (by rw [e1]; exact hB))` as an intermediate fact. Rewrite `this` using `[mul_one]`. Then use the resulting hypothesis.
-/
theorem zariski_cocycle_refinement {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R)
    {E : Type*} [Category E] (τ : E ⥤ C) [τ.Faithful] {T T' : C} (φ : T ⟶ T')
    (ψ : ∀ e, T' ⟶ τ.obj e) (hψ : ∀ {e e' : E} (f : e ⟶ e'), ψ e ≫ τ.map f = ψ e')
    {m : ℕ} (V : Fin m → ∀ ⦃T'' : C⦄, (T ⟶ T'') → Prop)
    (hV : ∀ k ⦃T₁ T₂ : C⦄ (ψ : T ⟶ T₁) (χ : T₁ ⟶ T₂), V k ψ → V k (ψ ≫ χ))
    (hE : ∀ e, ∃ k, V k (φ ≫ ψ e))
    (Lc : Finset (Fin m) → C) (lam : ∀ S, T' ⟶ Lc S)
    (h1 : ∀ S, ∀ k ∈ S, V k (φ ≫ lam S))
    (h2 : ∀ S (T'' : C) (ψ : T' ⟶ T''), (∀ k ∈ S, V k (φ ≫ ψ)) → ∃! χ : Lc S ⟶ T'', lam S ≫ χ = ψ)
    (hL : LocMod F T' Lc lam)
    (hfull : ∀ (e e' : E) (χ : τ.obj e ⟶ τ.obj e'), ψ e ≫ χ = ψ e' → ∃ f : e ⟶ e', τ.map f = χ)
    (obj : {S : Finset (Fin m) // S.Nonempty} → E) (eo : ∀ S, τ.obj (obj S) = Lc S.1)
    (hobj : ∀ S, ψ (obj S) = lam S.1 ≫ eqToHom (eo S).symm) :
    (cx (τ ⋙ F)).ResUpTo 1 (aug (τ ⋙ F) fun e => (F.map (ψ e)).hom) := by
  classical

  have hVe : ∀ S (e : E) (f : obj S ⟶ e), ∀ k ∈ S.1, V k (φ ≫ ψ e) := by
    intro S e f k hk
    have := hV k _ (eqToHom (eo S).symm ≫ τ.map f) (h1 S.1 k hk)
    rwa [Category.assoc, ← Category.assoc (lam S.1), ← hobj, hψ] at this
  have hsub : ∀ S (e : E), Subsingleton (obj S ⟶ e) := by
    intro S e
    refine ⟨fun f g => τ.map_injective ?_⟩
    have hf : lam S.1 ≫ (eqToHom (eo S).symm ≫ τ.map f) = ψ e := by
      rw [← Category.assoc, ← hobj, hψ]
    have hg : lam S.1 ≫ (eqToHom (eo S).symm ≫ τ.map g) = ψ e := by
      rw [← Category.assoc, ← hobj, hψ]
    have := (h2 S.1 _ (ψ e) (hVe S e f)).unique hf hg
    exact (cancel_epi _).1 this
  have hex : ∀ S (e : E), (∀ k ∈ S.1, V k (φ ≫ ψ e)) → Nonempty (obj S ⟶ e) := by
    intro S e h
    obtain ⟨χ, hχ, -⟩ := h2 S.1 _ (ψ e) h
    obtain ⟨f, -⟩ := hfull (obj S) e (eqToHom (eo S) ≫ χ) (by rw [hobj]; simpa using hχ)
    exact ⟨f⟩
  let U : E ⥤ {S : Finset (Fin m) // S.Nonempty} :=
    { obj := fun e => ⟨Finset.univ.filter (fun k => V k (φ ≫ ψ e)), by
          obtain ⟨k, hk⟩ := hE e
          exact ⟨k, by simpa using hk⟩⟩
      map := fun {e e'} f => homOfLE (by
          intro k hk
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
          have := hV k _ (τ.map f) hk
          rwa [Category.assoc, hψ] at this) }
  have hU : ∀ (S : {S : Finset (Fin m) // S.Nonempty}) (e : E), S.1 ⊆ (U.obj e).1 ↔ ∀ k ∈ S.1, V k (φ ≫ ψ e) := by
    intro S e
    constructor
    · intro h k hk
      have := h hk
      simpa [U] using this
    · intro h k hk
      simpa [U] using h k hk
  let Λ : {S : Finset (Fin m) // S.Nonempty} ⥤ E :=
    { obj := obj
      map := fun {S S'} h => Classical.choice (hex S (obj S') (fun k hk =>
          hVe S' (obj S') (𝟙 _) k (leOfHom h hk)))
      map_id := fun S => (hsub S (obj S)).elim _ _
      map_comp := fun {S _ _} _ _ => (hsub S _).elim _ _ }
  let adjn : Λ ⊣ U := Adjunction.mkOfHomEquiv
    { homEquiv := fun S e =>
        { toFun := fun f => homOfLE ((hU S e).2 (hVe S e f))
          invFun := fun h => Classical.choice (hex S e ((hU S e).1 (leOfHom h)))
          left_inv := fun f => (hsub S e).elim _ _
          right_inv := fun h => Subsingleton.elim _ _ }
      homEquiv_naturality_left_symm := fun {S _ _} _ _ => (hsub S _).elim _ _
      homEquiv_naturality_right := fun _ _ => Subsingleton.elim _ _ }
  have hA := CrystallineSemistableComparison.P.adj (τ ⋙ F) Λ U adjn
  have hB := CrystallineSemistableComparison.B.P.cech_loc F T' Lc lam (Λ ⋙ τ) eo (fun S S' h => by
    rw [← Category.assoc, ← hobj, ← hobj]
    exact hψ (Λ.map h)) hL
  have hup : ∀ n, UpTo (1 : R) ((Mor.restrict (τ ⋙ F) Λ).hom.mapH n) := fun n =>
    ((CrystallineSemistableComparison.P.upTo_alg ((Mor.restrict (τ ⋙ F) Λ).hom.mapH n)
      LinearMap.id 1 1).2.2.2.2).2 (hA n)
  have hd : ∀ x, (cx (τ ⋙ F)).d 0 (aug (τ ⋙ F) (fun e => (F.map (ψ e)).hom) x) = 0 :=
    zar_d_aug (τ ⋙ F) _ (fun {e e'} f x => by
      change (F.map (τ.map f)).hom ((F.map (ψ e)).hom x) = (F.map (ψ e')).hom x
      rw [← hψ f, F.map_comp]
      rfl)
  have e1 : (Mor.restrict (τ ⋙ F) Λ).hom.f 0 ∘ₗ aug (τ ⋙ F) (fun e => (F.map (ψ e)).hom) =
      aug ((Λ ⋙ τ) ⋙ F) fun S => (F.map (lam S.1 ≫ eqToHom (eo S).symm)).hom := by
    apply LinearMap.ext
    intro x
    funext s
    change (F.map (ψ (obj (s.obj (Fin.last 0))))).hom x = _
    rw [hobj]
    rfl
  have := ((CrystallineSemistableComparison.P.res_transfer (Mor.restrict (τ ⋙ F) Λ).hom
    (aug (τ ⋙ F) fun e => (F.map (ψ e)).hom) 1 1 hup).2 hd (by rw [e1]; exact hB))
  rwa [mul_one] at this

/- English proof (translation)
Take `⟨hQm, hcov⟩` from `hZ`. Set `ιQ` to `ObjectProperty.ι (Q : ObjectProperty C)`. Establish `key : ∀ T : C, (cx (StructuredArrow.proj T ιQ ⋙ ιQ ⋙ F)).ResUpTo 1 (aug (StructuredArrow.proj T ιQ ⋙ ιQ ⋙ F) fun x => (F.map x.hom).hom)`. Introduce `T`. Take `⟨m, V, hV, hVQ, hloc⟩` from `hcov T`.

Set `FK : StructuredArrow T ιQ ⥤ ModuleCat.{w} R` to `StructuredArrow.proj T ιQ ⋙ ιQ ⋙ F`. Set `P' : ObjectProperty (StructuredArrow T ιQ)` to `fun x => ∃ k, V k x.hom`. Set `incl` to `P'.ι`. Establish `z2 : ∀ x : StructuredArrow T ιQ, (cx (StructuredArrow.proj x incl ⋙ incl ⋙ FK)).ResUpTo 1 (aug (StructuredArrow.proj x incl ⋙ incl ⋙ FK) fun y => (FK.map y.hom).hom)`. Introduce `x`.

Take `⟨Lc, lam, h1, h2, ⟨hL⟩⟩` from `hloc x.right.obj x.hom`. Establish `hQS : ∀ S : {S : Finset (Fin m) // S.Nonempty}, Q (Lc S.1)` using `fun S => hVQ S.2.choose _ (h1 S.1 _ S.2.choose_spec)`. Set `obj : {S : Finset (Fin m) // S.Nonempty} → StructuredArrow x incl` to `fun S => StructuredArrow.mk (Y := (⟨StructuredArrow.mk (Y := (⟨Lc S.1, hQS S⟩ : ObjectProperty.FullSubcategory (Q : ObjectProperty C))) (x.hom ≫ lam S.1), ⟨S.2.choose, h1 S.1 _ S.2.choose_spec⟩⟩ : P'.FullSubcategory)) (StructuredArrow.homMk (ObjectProperty.homMk (lam S.1)) rfl)`. Use `CrystallineSemistableComparison.B.zariski_cocycle_refinement F (StructuredArrow.proj x incl ⋙ incl ⋙ StructuredArrow.proj T ιQ ⋙ ιQ) x.hom (fun e => e.hom.right.hom) (fun {e e'} f => ?_) V hV (fun e => ?_) Lc lam h1 h2 hL (fun e e' χ h => ?_) obj (fun S => rfl) (fun S => ?_)` and prove the remaining obligations. Conclude with `congrArg (fun g => g.right.hom) (StructuredArrow.w f)`.

Take `⟨k, hk⟩` from `e.right.property`. Establish `w1 : x.hom ≫ e.hom.right.hom = e.right.obj.hom` using `StructuredArrow.w e.hom`. Conclude with `⟨k, by rw [w1]; exact hk⟩`. Establish `w1 : x.hom ≫ e.hom.right.hom = e.right.obj.hom` using `StructuredArrow.w e.hom`. Establish `w2 : x.hom ≫ e'.hom.right.hom = e'.right.obj.hom` using `StructuredArrow.w e'.hom`.

Establish `w' : e.right.obj.hom ≫ ιQ.map (ObjectProperty.homMk χ) = e'.right.obj.hom`. Rewrite using `[← w1, ← w2, Category.assoc]`. Conclude with `congrArg (fun g => x.hom ≫ g) h`. Use `⟨StructuredArrow.homMk (ObjectProperty.homMk (StructuredArrow.homMk (ObjectProperty.homMk χ) w')) ?_, rfl⟩` and prove the remaining obligations. Conclude with `StructuredArrow.hom_ext _ _ (ObjectProperty.hom_ext _ h)`.

Simplify using `only [eqToHom_refl, Category.comp_id]`. Both sides reduce to the same expression. Establish `hup : ∀ j, UpTo (1 : R) ((Mor.restrict FK incl).hom.mapH j)` using `fun j => by`. Use `CrystallineSemistableComparison.B.P.fib (Mor.restrict FK incl) 1 (fun x => z2 x) j j le_rfl` as an intermediate fact. Rewrite `this` using `[one_pow]`. Then use the resulting hypothesis.

Take `⟨Lc, lam, h1, h2, ⟨hL⟩⟩` from `hloc T (𝟙 T)`. Establish `hQS : ∀ S : {S : Finset (Fin m) // S.Nonempty}, Q (Lc S.1)` using `fun S => hVQ S.2.choose _ (h1 S.1 _ S.2.choose_spec)`. Establish `h1' : ∀ S, ∀ k ∈ S, V k (lam S)` using `fun S k hk => by simpa using h1 S k hk`. Set `obj : {S : Finset (Fin m) // S.Nonempty} → P'.FullSubcategory` to `fun S => ⟨StructuredArrow.mk (Y := (⟨Lc S.1, hQS S⟩ : ObjectProperty.FullSubcategory (Q : ObjectProperty C))) (lam S.1), ⟨S.2.choose, h1' S.1 _ S.2.choose_spec⟩⟩`. Establish `hK'` using `CrystallineSemistableComparison.B.zariski_cocycle_refinement F (incl ⋙ StructuredArrow.proj T ιQ ⋙ ιQ) (𝟙 T) (fun e => e.obj.hom) (fun {e e'} f => StructuredArrow.w f.hom) V hV (fun e => by`.

Take `⟨k, hk⟩` from `e.property`. Conclude with `⟨k, by rw [Category.id_comp]; exact hk⟩) Lc lam h1 h2 hL`. Use the proof step `(fun e e' χ h => ⟨ObjectProperty.homMk (StructuredArrow.homMk (ObjectProperty.homMk χ) h), rfl⟩)`. Use `obj (fun S => rfl) (fun S => by simp only [eqToHom_refl, Category.comp_id]; rfl)`. Establish `e2 : (Mor.restrict FK incl).hom.f 0 ∘ₗ aug FK (fun x => (F.map x.hom).hom) = aug ((incl ⋙ StructuredArrow.proj T ιQ ⋙ ιQ) ⋙ F) fun e => (F.map e.obj.hom).hom`.

Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `a`. Use function extensionality and compare the values at `s`. Both sides reduce to the same expression. Use `(CrystallineSemistableComparison.P.res_transfer (Mor.restrict FK incl).hom (aug FK fun x => (F.map x.hom).hom) 1 1 hup).2 (zar_d_aug FK _ (fun {x y} f a => by` as an intermediate fact.

Express the relevant statement in the definitionally equal form `(F.map (ιQ.map f.right)).hom ((F.map x.hom).hom a) = (F.map y.hom).hom a`. Rewrite using `[← StructuredArrow.w f, F.map_comp]`. Use the proof step `rfl)) (by rw [e2]; exact hK')`. Rewrite `this` using `[mul_one]`. Then use the resulting hypothesis. Introduce `j hj`.

Use `CrystallineSemistableComparison.B.P.fib (Mor.restrict F ιQ) 1 (fun T => key T) j j le_rfl` as an intermediate fact. Rewrite `this` using `[one_pow]`. Then use the resulting hypothesis.
-/
theorem zar_main {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R)
    (Q : C → Prop) (hZ : ZarCov F Q) (n : ℕ) : RI 1 n F (ObjectProperty.ι (Q : ObjectProperty C)) := by
  classical
  obtain ⟨hQm, hcov⟩ := hZ
  let ιQ := ObjectProperty.ι (Q : ObjectProperty C)
  have key : ∀ T : C, (cx (StructuredArrow.proj T ιQ ⋙ ιQ ⋙ F)).ResUpTo 1
      (aug (StructuredArrow.proj T ιQ ⋙ ιQ ⋙ F) fun x => (F.map x.hom).hom) := by
    intro T
    obtain ⟨m, V, hV, hVQ, hloc⟩ := hcov T
    let FK : StructuredArrow T ιQ ⥤ ModuleCat.{w} R := StructuredArrow.proj T ιQ ⋙ ιQ ⋙ F
    let P' : ObjectProperty (StructuredArrow T ιQ) := fun x => ∃ k, V k x.hom
    let incl := P'.ι
    have z2 : ∀ x : StructuredArrow T ιQ, (cx (StructuredArrow.proj x incl ⋙ incl ⋙ FK)).ResUpTo 1
        (aug (StructuredArrow.proj x incl ⋙ incl ⋙ FK) fun y => (FK.map y.hom).hom) := by
      intro x
      obtain ⟨Lc, lam, h1, h2, ⟨hL⟩⟩ := hloc x.right.obj x.hom
      have hQS : ∀ S : {S : Finset (Fin m) // S.Nonempty}, Q (Lc S.1) := fun S =>
        hVQ S.2.choose _ (h1 S.1 _ S.2.choose_spec)
      let obj : {S : Finset (Fin m) // S.Nonempty} → StructuredArrow x incl := fun S =>
        StructuredArrow.mk (Y := (⟨StructuredArrow.mk
            (Y := (⟨Lc S.1, hQS S⟩ : ObjectProperty.FullSubcategory (Q : ObjectProperty C))) (x.hom ≫ lam S.1),
            ⟨S.2.choose, h1 S.1 _ S.2.choose_spec⟩⟩ : P'.FullSubcategory))
          (StructuredArrow.homMk (ObjectProperty.homMk (lam S.1)) rfl)
      refine CrystallineSemistableComparison.B.zariski_cocycle_refinement F (StructuredArrow.proj x incl ⋙ incl ⋙ StructuredArrow.proj T ιQ ⋙ ιQ) x.hom
        (fun e => e.hom.right.hom) (fun {e e'} f => ?_) V hV (fun e => ?_) Lc lam h1 h2 hL
        (fun e e' χ h => ?_) obj (fun S => rfl) (fun S => ?_)
      · exact congrArg (fun g => g.right.hom) (StructuredArrow.w f)
      · obtain ⟨k, hk⟩ := e.right.property
        have w1 : x.hom ≫ e.hom.right.hom = e.right.obj.hom := StructuredArrow.w e.hom
        exact ⟨k, by rw [w1]; exact hk⟩
      · have w1 : x.hom ≫ e.hom.right.hom = e.right.obj.hom := StructuredArrow.w e.hom
        have w2 : x.hom ≫ e'.hom.right.hom = e'.right.obj.hom := StructuredArrow.w e'.hom
        have w' : e.right.obj.hom ≫ ιQ.map (ObjectProperty.homMk χ) = e'.right.obj.hom := by
          rw [← w1, ← w2, Category.assoc]
          exact congrArg (fun g => x.hom ≫ g) h
        refine ⟨StructuredArrow.homMk (ObjectProperty.homMk (StructuredArrow.homMk (ObjectProperty.homMk χ) w')) ?_, rfl⟩
        exact StructuredArrow.hom_ext _ _ (ObjectProperty.hom_ext _ h)
      · simp only [eqToHom_refl, Category.comp_id]
        rfl
    have hup : ∀ j, UpTo (1 : R) ((Mor.restrict FK incl).hom.mapH j) := fun j => by
      have := CrystallineSemistableComparison.B.P.fib (Mor.restrict FK incl) 1 (fun x => z2 x) j j le_rfl
      rwa [one_pow] at this
    obtain ⟨Lc, lam, h1, h2, ⟨hL⟩⟩ := hloc T (𝟙 T)
    have hQS : ∀ S : {S : Finset (Fin m) // S.Nonempty}, Q (Lc S.1) := fun S =>
      hVQ S.2.choose _ (h1 S.1 _ S.2.choose_spec)
    have h1' : ∀ S, ∀ k ∈ S, V k (lam S) := fun S k hk => by simpa using h1 S k hk
    let obj : {S : Finset (Fin m) // S.Nonempty} → P'.FullSubcategory := fun S =>
      ⟨StructuredArrow.mk (Y := (⟨Lc S.1, hQS S⟩ : ObjectProperty.FullSubcategory (Q : ObjectProperty C))) (lam S.1),
        ⟨S.2.choose, h1' S.1 _ S.2.choose_spec⟩⟩
    have hK' := CrystallineSemistableComparison.B.zariski_cocycle_refinement F (incl ⋙ StructuredArrow.proj T ιQ ⋙ ιQ) (𝟙 T) (fun e => e.obj.hom)
      (fun {e e'} f => StructuredArrow.w f.hom) V hV
      (fun e => by
        obtain ⟨k, hk⟩ := e.property
        exact ⟨k, by rw [Category.id_comp]; exact hk⟩) Lc lam h1 h2 hL
      (fun e e' χ h => ⟨ObjectProperty.homMk (StructuredArrow.homMk (ObjectProperty.homMk χ) h), rfl⟩)
      obj (fun S => rfl) (fun S => by simp only [eqToHom_refl, Category.comp_id]; rfl)
    have e2 : (Mor.restrict FK incl).hom.f 0 ∘ₗ aug FK (fun x => (F.map x.hom).hom) =
        aug ((incl ⋙ StructuredArrow.proj T ιQ ⋙ ιQ) ⋙ F) fun e => (F.map e.obj.hom).hom := by
      apply LinearMap.ext
      intro a
      funext s
      rfl
    have := (CrystallineSemistableComparison.P.res_transfer (Mor.restrict FK incl).hom (aug FK fun x => (F.map x.hom).hom) 1 1 hup).2
      (zar_d_aug FK _ (fun {x y} f a => by
        change (F.map (ιQ.map f.right)).hom ((F.map x.hom).hom a) = (F.map y.hom).hom a
        rw [← StructuredArrow.w f, F.map_comp]
        rfl)) (by rw [e2]; exact hK')
    rwa [mul_one] at this
  intro j hj
  have := CrystallineSemistableComparison.B.P.fib (Mor.restrict F ιQ) 1 (fun T => key T) j j le_rfl
  rwa [one_pow] at this

end CrystallineSemistableComparison.B

/- English proof (translation)
Introduce `R _ C _ C' _ F Q ι hι hZ n`. Use `hι.full` as an intermediate fact. Use `hι.faithful` as an intermediate fact. Set `L` to `ObjectProperty.lift (Q : ObjectProperty C) ι hι.mem`. Establish `: L.EssSurj` using `⟨fun Y => by`.

Take `⟨T₁, ⟨i⟩⟩` from `hι.ess Y.obj Y.property`. Conclude with `⟨T₁, ⟨ObjectProperty.isoMk _ i⟩⟩⟩`. Establish `: L.IsEquivalence` using `{}`. Establish `h1` using `CrystallineSemistableComparison.B.zar_main F Q hZ n`. Establish `h2 : RI 1 n ((ObjectProperty.ι (Q : ObjectProperty C)) ⋙ F) L` using `(CrystallineSemistableComparison.B.P.ri_calc ((ObjectProperty.ι (Q : ObjectProperty C)) ⋙ F) L (𝟭 C') 1 1 n).2.2.2.2.2.1 inferInstance`.

Establish `h3` using `(CrystallineSemistableComparison.B.P.ri_calc F (ObjectProperty.ι (Q : ObjectProperty C)) L 1 1 n).1 h1 h2`. Rewrite `h3` using `[mul_one]`. Conclude with `(CrystallineSemistableComparison.B.P.ri_calc F (L ⋙ ObjectProperty.ι (Q : ObjectProperty C)) (𝟭 C') 1 1 n).2.2.2.2.1 ι (ObjectProperty.liftCompιIso _ ι hι.mem) h3`.
-/
theorem CrystallineSemistableComparison.B.P.zar : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] (F : C ⥤ ModuleCat.{w} R) (Q : C → Prop) (ι : C' ⥤ C), Onto ι Q → ZarCov F Q → ∀ n, RI 1 n F ι := by
  intro R _ C _ C' _ F Q ι hι hZ n
  have := hι.full
  have := hι.faithful
  let L := ObjectProperty.lift (Q : ObjectProperty C) ι hι.mem
  have : L.EssSurj := ⟨fun Y => by
    obtain ⟨T₁, ⟨i⟩⟩ := hι.ess Y.obj Y.property
    exact ⟨T₁, ⟨ObjectProperty.isoMk _ i⟩⟩⟩
  have : L.IsEquivalence := {}
  have h1 := CrystallineSemistableComparison.B.zar_main F Q hZ n
  have h2 : RI 1 n ((ObjectProperty.ι (Q : ObjectProperty C)) ⋙ F) L :=
    (CrystallineSemistableComparison.B.P.ri_calc ((ObjectProperty.ι (Q : ObjectProperty C)) ⋙ F) L (𝟭 C') 1 1 n).2.2.2.2.2.1 inferInstance
  have h3 := (CrystallineSemistableComparison.B.P.ri_calc F (ObjectProperty.ι (Q : ObjectProperty C)) L 1 1 n).1 h1 h2
  rw [mul_one] at h3
  exact (CrystallineSemistableComparison.B.P.ri_calc F (L ⋙ ObjectProperty.ι (Q : ObjectProperty C)) (𝟭 C') 1 1 n).2.2.2.2.1 ι
    (ObjectProperty.liftCompιIso _ ι hι.mem) h3
