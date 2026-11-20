import Development.EtaleCohomology.CohomologicalPurity.LeafWCechPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ExcP.Chart

/- English proof (translation)
Apply `(mono_iff_injective (limitObjIsoLimitCompEvaluation F U).hom).1 inferInstance` to reduce the goal to its premises. Apply `Types.limit_ext` to reduce the goal to its premises. Introduce `j`. Establish `e` using `limitObjIsoLimitCompEvaluation_hom_π F j (k := U)`. Establish `e1` using `congrArg (fun f => f w) (congrArg ConcreteCategory.hom e)`.

Establish `e2` using `congrArg (fun f => f w') (congrArg ConcreteCategory.hom e)`. Simplify using `only [types_comp_apply] at e1 e2`. Rewrite using `[e1, e2]`. Conclude with `h j`.
-/
theorem psh_limit_ext {J : Type} [SmallCategory J] (F : J ⥤ PSh) (U : Scheme.{0}ᵒᵖ) (w w' : (limit F).obj U)
    (h : ∀ j, (limit.π F j).app U w = (limit.π F j).app U w') : w = w' := by
  apply (mono_iff_injective (limitObjIsoLimitCompEvaluation F U).hom).1 inferInstance
  apply Types.limit_ext
  intro j
  have e := limitObjIsoLimitCompEvaluation_hom_π F j (k := U)
  have e1 := congrArg (fun f => f w) (congrArg ConcreteCategory.hom e)
  have e2 := congrArg (fun f => f w') (congrArg ConcreteCategory.hom e)
  simp only [types_comp_apply] at e1 e2
  rw [e1, e2]; exact h j

/- English proof (translation)
Apply `psh_limit_ext _ U` to reduce the goal to its premises. Introduce and unpack `(_ | i)`. Establish `e` using `WidePullback.π_arrow (fun _ : Fin (n + 1) => φ) 0`. Establish `e1` using `congrArg (fun f => (f.app U) w) e`. Establish `e2` using `congrArg (fun f => (f.app U) w') e`.

Simplify using `only [NatTrans.comp_app, types_comp_apply] at e1 e2`. Express the relevant statement in the definitionally equal form `NatTrans.app (WidePullback.base (fun _ : Fin (n + 1) => φ)) U w = NatTrans.app (WidePullback.base (fun _ : Fin (n + 1) => φ)) U w'`. Rewrite using `[← e1, ← e2, h 0]`. Conclude with `h i`.
-/
theorem wpb_ext {B : PSh} {n : ℕ} {P : PSh} (φ : P ⟶ B) (U : Scheme.{0}ᵒᵖ)
    (w w' : (widePullback B (fun _ : Fin (n + 1) => P) fun _ => φ).obj U)
    (h : ∀ i, NatTrans.app (WidePullback.π (fun _ : Fin (n + 1) => φ) i) U w =
      NatTrans.app (WidePullback.π (fun _ : Fin (n + 1) => φ) i) U w') : w = w' := by
  apply psh_limit_ext _ U
  rintro (_ | i)
  · have e := WidePullback.π_arrow (fun _ : Fin (n + 1) => φ) 0
    have e1 := congrArg (fun f => (f.app U) w) e
    have e2 := congrArg (fun f => (f.app U) w') e
    simp only [NatTrans.comp_app, types_comp_apply] at e1 e2
    change NatTrans.app (WidePullback.base (fun _ : Fin (n + 1) => φ)) U w =
      NatTrans.app (WidePullback.base (fun _ : Fin (n + 1) => φ)) U w'
    rw [← e1, ← e2, h 0]
  · exact h i

/- English proof (translation)
Introduce `X P Z φ r g hg hinj hsurj`. Set `Xa : SimplicialObject.Augmented PSh` to `{ left := X, right := Z, hom := r }`. Set `G : SimplicialObject.Augmented.toArrow.obj Xa ⟶ Arrow.mk φ` to `Arrow.homMk g (𝟙 Z) (by change g ≫ φ = r.app _ ≫ 𝟙 Z; exact hg.trans (Category.comp_id _).symm)`. Set `Ψ` to `SimplicialObject.equivalenceLeftToRight Xa (Arrow.mk φ) G`. Establish `hπ : ∀ (m : ℕ) (U : Scheme.{0}ᵒᵖ) x (i : Fin (m + 1)), NatTrans.app (WidePullback.π (fun _ : Fin (m + 1) => φ) i) U (NatTrans.app (Ψ.left.app (op (SimplexCategory.mk m))) U x) = g.app U ((X.map (vtx m i).op).app U x)`.

Introduce `m U x i`. Establish `e : Ψ.left.app (op (SimplexCategory.mk m)) ≫ WidePullback.π (fun _ : Fin (m + 1) => φ) i = X.map (vtx m i).op ≫ g` using `WidePullback.lift_π _ _ _ _ _`. Use `ConcreteCategory.congr_hom (NatTrans.congr_app e U) x` as an intermediate fact. Conclude with `this`. Use `⟨Ψ.left, ?_, ?_⟩` and prove the remaining obligations.

Establish `: ∀ n, IsIso (Ψ.left.app n)`. Introduce `n`. Proceed by induction on `n using Opposite.rec with | op n => ?_`. Proceed by induction on `n using SimplexCategory.rec with | _ m => ?_`. Establish `: ∀ U, IsIso ((Ψ.left.app (op (SimplexCategory.mk m))).app U)`.

Introduce `U`. Rewrite using `[isIso_iff_bijective]`. Prove the components needed by the constructor for the conclusion. Introduce `x x' hx`. Apply `hinj m U x x'` to reduce the goal to its premises.

Introduce `i`. Rewrite using `[← hπ, ← hπ]`. Conclude with `congrArg _ hx`. Introduce `w`. Take `⟨x, hx⟩` from `hsurj m U (fun i => NatTrans.app (WidePullback.π (fun _ : Fin (m + 1) => φ) i) U w) (NatTrans.app (WidePullback.base (fun _ : Fin (m + 1) => φ)) U w) (fun i => by`.

Establish `e` using `WidePullback.π_arrow (fun _ : Fin (m + 1) => φ) i`. Use `ConcreteCategory.congr_hom (NatTrans.congr_app e U) w` as an intermediate fact. Conclude with `this)`. Use `⟨x, wpb_ext φ U _ _ fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[hπ]`.

Conclude with `hx i`. Conclude with `@NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ this`. Conclude with `@NatIso.isIso_of_isIso_app _ _ _ _ _ _ Ψ.left this`. Use `(Ψ.w : _).trans ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `r ≫ (SimplicialObject.const PSh).map (𝟙 Z) = r`.

Rewrite using `[CategoryTheory.Functor.map_id, Category.comp_id]`.
-/
theorem leafCechRec : LeafCechRec := by
  intro X P Z φ r g hg hinj hsurj
  let Xa : SimplicialObject.Augmented PSh := { left := X, right := Z, hom := r }
  let G : SimplicialObject.Augmented.toArrow.obj Xa ⟶ Arrow.mk φ :=
    Arrow.homMk g (𝟙 Z) (by change g ≫ φ = r.app _ ≫ 𝟙 Z; exact hg.trans (Category.comp_id _).symm)
  let Ψ := SimplicialObject.equivalenceLeftToRight Xa (Arrow.mk φ) G
  have hπ : ∀ (m : ℕ) (U : Scheme.{0}ᵒᵖ) x (i : Fin (m + 1)),
      NatTrans.app (WidePullback.π (fun _ : Fin (m + 1) => φ) i) U
        (NatTrans.app (Ψ.left.app (op (SimplexCategory.mk m))) U x) = g.app U ((X.map (vtx m i).op).app U x) := by
    intro m U x i
    have e : Ψ.left.app (op (SimplexCategory.mk m)) ≫ WidePullback.π (fun _ : Fin (m + 1) => φ) i =
        X.map (vtx m i).op ≫ g := WidePullback.lift_π _ _ _ _ _
    have := ConcreteCategory.congr_hom (NatTrans.congr_app e U) x
    exact this
  refine ⟨Ψ.left, ?_, ?_⟩
  · have : ∀ n, IsIso (Ψ.left.app n) := by
      intro n
      induction n using Opposite.rec with | op n => ?_
      induction n using SimplexCategory.rec with | _ m => ?_
      have : ∀ U, IsIso ((Ψ.left.app (op (SimplexCategory.mk m))).app U) := by
        intro U
        rw [isIso_iff_bijective]
        constructor
        · intro x x' hx
          apply hinj m U x x'
          intro i
          rw [← hπ, ← hπ]
          exact congrArg _ hx
        · intro w
          obtain ⟨x, hx⟩ := hsurj m U (fun i => NatTrans.app (WidePullback.π (fun _ : Fin (m + 1) => φ) i) U w)
            (NatTrans.app (WidePullback.base (fun _ : Fin (m + 1) => φ)) U w) (fun i => by
              have e := WidePullback.π_arrow (fun _ : Fin (m + 1) => φ) i
              have := ConcreteCategory.congr_hom (NatTrans.congr_app e U) w
              exact this)
          refine ⟨x, wpb_ext φ U _ _ fun i => ?_⟩
          rw [hπ]; exact hx i
      exact @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ this
    exact @NatIso.isIso_of_isIso_app _ _ _ _ _ _ Ψ.left this
  · refine (Ψ.w : _).trans ?_
    change r ≫ (SimplicialObject.const PSh).map (𝟙 Z) = r
    rw [CategoryTheory.Functor.map_id, Category.comp_id]

/- English proof (translation)
The claim follows from `LeafWCech_of leafCechRec hD`.
-/
theorem LeafWCech_of_data (hD : LeafWData) : LeafWCech := LeafWCech_of leafCechRec hD

end LateralTheory.CohomologicalPurity.Thom.ExcP.Chart
