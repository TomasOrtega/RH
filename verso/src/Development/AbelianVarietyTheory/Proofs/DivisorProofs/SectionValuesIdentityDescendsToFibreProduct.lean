import Development.AbelianVarietyTheory.Definitions.Divisors.LabExt
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointFlatOfModificationOfDomain
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.ValDescent

/- English proof (translation)
Use `show Spec.map _ = Spec.map _ ≫ Spec.map _`. Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem spMap_comp {A B C' : Type} [CommRing A] [CommRing B] [CommRing C'] (f : A →+* B) (g : B →+* C') :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]; rfl

/- English proof (translation)
Use `haveI : Mono (jK R) := Scheme.Spec.map_mono (CommRingCat.ofHom (algebraMap R (FractionRing R))).op`. Conclude with `(cancel_mono (jK R)).1 h`.
-/
theorem eq_of_comp_jK {R : Type} [CommRing R] [IsDomain R] {X : Scheme.{0}} {f g : X ⟶ Sp (FractionRing R)}
    (h : f ≫ jK R = g ≫ jK R) : f = g := by
  haveI : Mono (jK R) := Scheme.Spec.map_mono (CommRingCat.ofHom (algebraMap R (FractionRing R))).op
  exact (cancel_mono (jK R)).1 h

/- English proof (translation)
Introduce `R _ _ _ _ D C k W _ _ _ T F _ _ _ hF σ s w H Z p p' hpp z J hJ`. Use `C.semi.smooth` as an intermediate fact. Use `haveI : Flat T.G.hom := MorphismProperty.of_isPullback (P := @Flat) T.cart.1 inferInstance`. Use `haveI : Flat C.gp := Modif.flat_gp R C.toModif`. Use `haveI : Flat C.α := MorphismProperty.of_isPullback (P := @Flat) C.α_cart.1.flip inferInstance`.

Use `haveI : Flat (pullback.fst T.β C.α) := MorphismProperty.of_isPullback (P := @Flat) (IsPullback.of_hasPullback T.β C.α).flip inferInstance`. Use `set q₁ : pullback T.β C.α ⟶ T.G.left := pullback.fst T.β C.α with hq₁`. Use `set q₂ : pullback T.β C.α ⟶ C.A.A.left := pullback.snd T.β C.α with hq₂`. Establish `hq : q₁ ≫ T.β = q₂ ≫ C.α` using `pullback.condition`. Use `set ρ : W →+* F := (algebraMap (FractionRing W) F).comp (algebraMap W _) with hρ`.

Establish `hρi : Function.Injective ρ` using `(algebraMap (FractionRing W) F).injective.comp (IsFractionRing.injective W _)`. Use `set d : pullback (q₁ ≫ T.G.hom) (spMap ρ) ⟶ pullback T.β C.α := pullback.fst _ _ with hd`. Use `set t : pullback (q₁ ≫ T.G.hom) (spMap ρ) ⟶ Sp F := pullback.snd _ _ with ht`. Establish `hdt : d ≫ q₁ ≫ T.G.hom = t ≫ spMap ρ` using `pullback.condition`. Establish `hinj : ∀ V, Function.Injective (d.app V)`.

Introduce `V`. Establish `: IsDominant (spMap ρ)` using `⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (((RingHom.injective_iff_ker_eq_bot _).1 hρi).le.trans bot_le)⟩`. Use `IsSchemeTheoreticallyDominant.of_isDominant (spMap ρ)` as an intermediate fact. Establish `: IsSchemeTheoreticallyDominant d` using `IsSchemeTheoreticallyDominant.of_isPullback (IsPullback.of_hasPullback (q₁ ≫ T.G.hom) (spMap ρ)).flip`. Establish `: QuasiCompact d` using `MorphismProperty.of_isPullback (P := @QuasiCompact) (IsPullback.of_hasPullback (q₁ ≫ T.G.hom) (spMap ρ)).flip inferInstance`.

Conclude with `d.app_injective V`. Establish `hover : t ≫ jFK (R` using `R) F = d ≫ q₂ ≫ C.A.A.hom := by`. Apply `ValDescent.eq_of_comp_jK` to reduce the goal to its premises. Establish `e₁ : jFK (R` using `R) F ≫ jK R = spMap ρ ≫ spMap T.φ := by`. Rewrite using `[← spMap_comp, ← spMap_comp]`.

Use `congr 1`. Conclude with `RingHom.ext hF`. Establish `e₂ : T.G.hom ≫ spMap T.φ = T.β ≫ C.G.hom ≫ C.π`. Rewrite using `[← T.ξ_π, ← Category.assoc, ← T.cart.1.w, Category.assoc]`. Establish `e₃ : C.α ≫ C.G.hom ≫ C.π = C.A.A.hom ≫ jK R`.

Rewrite using `[← Category.assoc, C.α_cart.1.w, Category.assoc, C.gp_π]`. Rewrite using `[Category.assoc, e₁, ← Category.assoc, ← hdt, Category.assoc, Category.assoc, e₂, ← Category.assoc q₁, hq, Category.assoc, e₃]`. Simplify using `only [Category.assoc]`. Set `P' : Over (Sp (FractionRing R))` to `Over.mk (d ≫ q₂ ≫ C.A.A.hom)`. Set `ℓ : P' ⟶ TFK (R` to `R) F ⊗ C.A.A := lift (Over.homMk t hover) (Over.homMk (d ≫ q₂) (Category.assoc _ _ _))`.

Establish `hfst : ℓ.left ≫ (fst (TFK (R` using `R) F) C.A.A).left = t := by`. Rewrite using `[← Over.comp_left, lift_fst]`. Both sides reduce to the same expression. Establish `hsnd : ℓ.left ≫ (snd (TFK (R` using `R) F) C.A.A).left = d ≫ q₂ := by`. Rewrite using `[← Over.comp_left, lift_snd]`.

Both sides reduce to the same expression. Establish `hL : C.P.L.L.IsLB` using `C.P.L.isLB`. Use `set i := J (p ≫ T.β) with hi`. Use `set Vβ := LB.wchart C.P.L.L (fun _ : Fin 1 => T.β) (fun _ => i) with hVβ`. Use `set Vα := LB.wchart C.P.L.L (fun _ : Fin 1 => C.α) (fun _ => i) with hVα`.

Use `set V : (pullback T.β C.α).Opens := q₁ ⁻¹ᵁ Vβ ⊓ q₂ ⁻¹ᵁ Vα with hV`. Establish `l₀ : V ≤ q₁ ⁻¹ᵁ ⊤` using `fun _ _ => trivial`. Set `a : Γ(pullback T.β C.α, V)` to `((pullback T.β C.α).presheaf.map (homOfLE (inf_le_left : V ≤ q₁ ⁻¹ᵁ Vβ)).op).hom ((q₁.app Vβ).hom (σ.f fun _ => i))`. Set `b : Γ(pullback T.β C.α, V)` to `((pullback T.β C.α).presheaf.map (homOfLE l₀).op).hom ((q₁.app ⊤).hom (scal T.G.hom w)) * ((pullback T.β C.α).presheaf.map (homOfLE (inf_le_right : V ≤ q₂ ⁻¹ᵁ Vα)).op).hom ((q₂.app Vα).hom (s.f fun _ => i))`. Establish `ka : ∀ (Z₀ : Scheme.{0}) (r : Z₀ ⟶ pullback T.β C.α) (z₀ : Z₀) (J₀ : (Z₀ ⟶ C.G.left) → C.P.L.L.ι) (hr : r z₀ ∈ V), J₀ ((r ≫ q₁) ≫ T.β) = i → gs r z₀ V a = sval σ (r ≫ q₁) z₀ J₀`.

Introduce `Z₀ r z₀ J₀ hr hJ₀`. Rewrite using `[sval_of σ (r ≫ q₁) z₀ J₀ (fun _ => i) (fun _ => hJ₀)]`. Conclude with `(gs_res r z₀ _ hr _).trans (gs_pull r q₁ z₀ Vβ hr.1 _)`. Establish `kb : ∀ (Z₀ : Scheme.{0}) (r : Z₀ ⟶ pullback T.β C.α) (z₀ : Z₀) (J₀ : (Z₀ ⟶ C.G.left) → C.P.L.L.ι) (hr : r z₀ ∈ V), J₀ ((r ≫ q₂) ≫ C.α) = i → gs r z₀ V b = gs (r ≫ q₁) z₀ ⊤ (scal T.G.hom w) * sval s (r ≫ q₂) z₀ J₀`. Introduce `Z₀ r z₀ J₀ hr hJ₀`.

Rewrite using `[sval_of s (r ≫ q₂) z₀ J₀ (fun _ => i) (fun _ => hJ₀)]`. Conclude with `(gs_mul r z₀ V hr _ _).trans (congrArg₂ (· * ·) ((gs_res r z₀ _ hr _).trans (gs_pull r q₁ z₀ ⊤ trivial _)) ((gs_res r z₀ _ hr _).trans (gs_pull r q₂ z₀ Vα hr.2 _)))`. Establish `hab : a = b`. Apply `hinj V` to reduce the goal to its premises. Use `fn_ext fun x hx => ?_` and prove the remaining obligations.

Rewrite using `[gs_pull (𝟙 _) d x V hx, gs_pull (𝟙 _) d x V hx, Category.id_comp]`. Establish `hmem : ((d ≫ q₁) ≫ T.β) x ∈ C.P.L.L.U i` using `Set.mem_iInter.1 hx.1 0`. Take `⟨J', hJ', eJ'⟩` from `exists_good C.P.L.L hL x (fun _ : Fin 1 => (d ≫ q₁) ≫ T.β) (fun _ => i) (fun _ _ _ => rfl) (fun _ => hmem)`. Establish `e₁ : J' ((d ≫ q₁) ≫ T.β) = i` using `eJ' 0`. Establish `e₂ : J' ((d ≫ q₂) ≫ C.α) = i` using `by rw [Category.assoc, ← hq, ← Category.assoc]; exact e₁`.

Rewrite using `[ka _ d x J' hx e₁, kb _ d x J' hx e₂]`. Establish `h₁ : (d ≫ q₁) ≫ T.β = ℓ.left ≫ (snd (TFK (R` using `R) F) C.A.A).left ≫ C.α := by`. Rewrite using `[← Category.assoc, hsnd, Category.assoc, Category.assoc, hq]`. Establish `h₂ : (d ≫ q₁) ≫ T.G.hom = ℓ.left ≫ (fst (TFK (R` using `R) F) C.A.A).left ≫ spMap ρ := by`. Rewrite using `[← Category.assoc, hfst, Category.assoc, hdt]`.

Use `H _ (d ≫ q₁) ℓ.left h₁ h₂ x J' hJ'` as an intermediate fact. Rewrite `this` using `[hsnd]`. Conclude with `this`. Use `set u : Z ⟶ pullback T.β C.α := pullback.lift p p' hpp with hu`. Establish `hu₁ : u ≫ q₁ = p` using `pullback.lift_fst _ _ _`.

Establish `hu₂ : u ≫ q₂ = p'` using `pullback.lift_snd _ _ _`. Establish `hz : u z ∈ V`. Use `⟨Set.mem_iInter.2 fun _ => ?_, Set.mem_iInter.2 fun _ => ?_⟩` and prove the remaining obligations. Establish `h : (p ≫ T.β) z ∈ C.P.L.L.U i` using `hJ (p ≫ T.β)`. Rewrite `h` using `[← hu₁]`.

Conclude with `h`. Establish `h : (p ≫ T.β) z ∈ C.P.L.L.U i` using `hJ (p ≫ T.β)`. Rewrite `h` using `[hpp, ← hu₂]`. Conclude with `h`. Establish `A` using `ka Z u z J hz (by rw [hu₁])`.

Establish `B` using `kb Z u z J hz (by rw [hu₂, ← hpp])`. Rewrite `A`, `B` using `[hu₁]`. Rewrite `B` using `[hu₂]`. Rewrite `A` using `[hab]`. Conclude with `A.symm.trans B`.
-/
theorem desc : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F], (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ (σ : SecK C.P.L.L T.β k) (s : SecK C.P.L.L C.α k) (w : W), (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left), p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = p' ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs p z ⊤ (scal T.G.hom w) * sval s (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z J) → ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs p z ⊤ (scal T.G.hom w) * sval s p' z J := by
  intro R _ _ _ _ D C k W _ _ _ T F _ _ _ hF σ s w H Z p p' hpp z J hJ
  have := C.semi.smooth
  haveI : Flat T.G.hom := MorphismProperty.of_isPullback (P := @Flat) T.cart.1 inferInstance
  haveI : Flat C.gp := Modif.flat_gp R C.toModif
  haveI : Flat C.α := MorphismProperty.of_isPullback (P := @Flat) C.α_cart.1.flip inferInstance
  haveI : Flat (pullback.fst T.β C.α) :=
    MorphismProperty.of_isPullback (P := @Flat) (IsPullback.of_hasPullback T.β C.α).flip inferInstance
  set q₁ : pullback T.β C.α ⟶ T.G.left := pullback.fst T.β C.α with hq₁
  set q₂ : pullback T.β C.α ⟶ C.A.A.left := pullback.snd T.β C.α with hq₂
  have hq : q₁ ≫ T.β = q₂ ≫ C.α := pullback.condition
  set ρ : W →+* F := (algebraMap (FractionRing W) F).comp (algebraMap W _) with hρ
  have hρi : Function.Injective ρ := (algebraMap (FractionRing W) F).injective.comp (IsFractionRing.injective W _)
  set d : pullback (q₁ ≫ T.G.hom) (spMap ρ) ⟶ pullback T.β C.α := pullback.fst _ _ with hd
  set t : pullback (q₁ ≫ T.G.hom) (spMap ρ) ⟶ Sp F := pullback.snd _ _ with ht
  have hdt : d ≫ q₁ ≫ T.G.hom = t ≫ spMap ρ := pullback.condition
  have hinj : ∀ V, Function.Injective (d.app V) := by
    intro V
    have : IsDominant (spMap ρ) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
      (((RingHom.injective_iff_ker_eq_bot _).1 hρi).le.trans bot_le)⟩
    have := IsSchemeTheoreticallyDominant.of_isDominant (spMap ρ)
    have : IsSchemeTheoreticallyDominant d :=
      IsSchemeTheoreticallyDominant.of_isPullback (IsPullback.of_hasPullback (q₁ ≫ T.G.hom) (spMap ρ)).flip
    have : QuasiCompact d := MorphismProperty.of_isPullback (P := @QuasiCompact)
      (IsPullback.of_hasPullback (q₁ ≫ T.G.hom) (spMap ρ)).flip inferInstance
    exact d.app_injective V

  have hover : t ≫ jFK (R := R) F = d ≫ q₂ ≫ C.A.A.hom := by
    apply ValDescent.eq_of_comp_jK
    have e₁ : jFK (R := R) F ≫ jK R = spMap ρ ≫ spMap T.φ := by
      rw [← spMap_comp, ← spMap_comp]
      congr 1
      exact RingHom.ext hF
    have e₂ : T.G.hom ≫ spMap T.φ = T.β ≫ C.G.hom ≫ C.π := by
      rw [← T.ξ_π, ← Category.assoc, ← T.cart.1.w, Category.assoc]
    have e₃ : C.α ≫ C.G.hom ≫ C.π = C.A.A.hom ≫ jK R := by
      rw [← Category.assoc, C.α_cart.1.w, Category.assoc, C.gp_π]
    rw [Category.assoc, e₁, ← Category.assoc, ← hdt, Category.assoc, Category.assoc, e₂, ← Category.assoc q₁,
      hq, Category.assoc, e₃]
    simp only [Category.assoc]
  let P' : Over (Sp (FractionRing R)) := Over.mk (d ≫ q₂ ≫ C.A.A.hom)
  let ℓ : P' ⟶ TFK (R := R) F ⊗ C.A.A := lift (Over.homMk t hover) (Over.homMk (d ≫ q₂) (Category.assoc _ _ _))
  have hfst : ℓ.left ≫ (fst (TFK (R := R) F) C.A.A).left = t := by
    rw [← Over.comp_left, lift_fst]; rfl
  have hsnd : ℓ.left ≫ (snd (TFK (R := R) F) C.A.A).left = d ≫ q₂ := by
    rw [← Over.comp_left, lift_snd]; rfl

  have hL : C.P.L.L.IsLB := C.P.L.isLB
  set i := J (p ≫ T.β) with hi
  set Vβ := LB.wchart C.P.L.L (fun _ : Fin 1 => T.β) (fun _ => i) with hVβ
  set Vα := LB.wchart C.P.L.L (fun _ : Fin 1 => C.α) (fun _ => i) with hVα
  set V : (pullback T.β C.α).Opens := q₁ ⁻¹ᵁ Vβ ⊓ q₂ ⁻¹ᵁ Vα with hV
  have l₀ : V ≤ q₁ ⁻¹ᵁ ⊤ := fun _ _ => trivial
  let a : Γ(pullback T.β C.α, V) :=
    ((pullback T.β C.α).presheaf.map (homOfLE (inf_le_left : V ≤ q₁ ⁻¹ᵁ Vβ)).op).hom ((q₁.app Vβ).hom (σ.f fun _ => i))
  let b : Γ(pullback T.β C.α, V) :=
    ((pullback T.β C.α).presheaf.map (homOfLE l₀).op).hom ((q₁.app ⊤).hom (scal T.G.hom w)) *
    ((pullback T.β C.α).presheaf.map (homOfLE (inf_le_right : V ≤ q₂ ⁻¹ᵁ Vα)).op).hom ((q₂.app Vα).hom (s.f fun _ => i))
  have ka : ∀ (Z₀ : Scheme.{0}) (r : Z₀ ⟶ pullback T.β C.α) (z₀ : Z₀) (J₀ : (Z₀ ⟶ C.G.left) → C.P.L.L.ι) (hr : r z₀ ∈ V),
      J₀ ((r ≫ q₁) ≫ T.β) = i → gs r z₀ V a = sval σ (r ≫ q₁) z₀ J₀ := by
    intro Z₀ r z₀ J₀ hr hJ₀
    rw [sval_of σ (r ≫ q₁) z₀ J₀ (fun _ => i) (fun _ => hJ₀)]
    exact (gs_res r z₀ _ hr _).trans (gs_pull r q₁ z₀ Vβ hr.1 _)
  have kb : ∀ (Z₀ : Scheme.{0}) (r : Z₀ ⟶ pullback T.β C.α) (z₀ : Z₀) (J₀ : (Z₀ ⟶ C.G.left) → C.P.L.L.ι) (hr : r z₀ ∈ V),
      J₀ ((r ≫ q₂) ≫ C.α) = i → gs r z₀ V b = gs (r ≫ q₁) z₀ ⊤ (scal T.G.hom w) * sval s (r ≫ q₂) z₀ J₀ := by
    intro Z₀ r z₀ J₀ hr hJ₀
    rw [sval_of s (r ≫ q₂) z₀ J₀ (fun _ => i) (fun _ => hJ₀)]
    exact (gs_mul r z₀ V hr _ _).trans (congrArg₂ (· * ·) ((gs_res r z₀ _ hr _).trans (gs_pull r q₁ z₀ ⊤ trivial _))
      ((gs_res r z₀ _ hr _).trans (gs_pull r q₂ z₀ Vα hr.2 _)))
  have hab : a = b := by
    apply hinj V
    refine fn_ext fun x hx => ?_
    rw [gs_pull (𝟙 _) d x V hx, gs_pull (𝟙 _) d x V hx, Category.id_comp]
    have hmem : ((d ≫ q₁) ≫ T.β) x ∈ C.P.L.L.U i := Set.mem_iInter.1 hx.1 0
    obtain ⟨J', hJ', eJ'⟩ := exists_good C.P.L.L hL x (fun _ : Fin 1 => (d ≫ q₁) ≫ T.β) (fun _ => i) (fun _ _ _ => rfl)
      (fun _ => hmem)
    have e₁ : J' ((d ≫ q₁) ≫ T.β) = i := eJ' 0
    have e₂ : J' ((d ≫ q₂) ≫ C.α) = i := by rw [Category.assoc, ← hq, ← Category.assoc]; exact e₁
    rw [ka _ d x J' hx e₁, kb _ d x J' hx e₂]
    have h₁ : (d ≫ q₁) ≫ T.β = ℓ.left ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α := by
      rw [← Category.assoc, hsnd, Category.assoc, Category.assoc, hq]
    have h₂ : (d ≫ q₁) ≫ T.G.hom = ℓ.left ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ρ := by
      rw [← Category.assoc, hfst, Category.assoc, hdt]
    have := H _ (d ≫ q₁) ℓ.left h₁ h₂ x J' hJ'
    rw [hsnd] at this
    exact this

  set u : Z ⟶ pullback T.β C.α := pullback.lift p p' hpp with hu
  have hu₁ : u ≫ q₁ = p := pullback.lift_fst _ _ _
  have hu₂ : u ≫ q₂ = p' := pullback.lift_snd _ _ _
  have hz : u z ∈ V := by
    refine ⟨Set.mem_iInter.2 fun _ => ?_, Set.mem_iInter.2 fun _ => ?_⟩
    · have h : (p ≫ T.β) z ∈ C.P.L.L.U i := hJ (p ≫ T.β)
      rw [← hu₁] at h
      exact h
    · have h : (p ≫ T.β) z ∈ C.P.L.L.U i := hJ (p ≫ T.β)
      rw [hpp, ← hu₂] at h
      exact h
  have A := ka Z u z J hz (by rw [hu₁])
  have B := kb Z u z J hz (by rw [hu₂, ← hpp])
  rw [hu₁] at A B
  rw [hu₂] at B
  rw [hab] at A
  exact A.symm.trans B

end GlobalTheory.Mum.ValDescent
