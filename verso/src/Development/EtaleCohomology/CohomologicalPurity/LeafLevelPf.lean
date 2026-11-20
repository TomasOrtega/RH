import Development.EtaleCohomology.CohomologicalPurity.LeafTubeCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.LeafLevelPf
open LateralTheory.CohomologicalPurity.TubeCut

variable {J : Type} [SmallCategory J]

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem elt_eqToHom {F : J ⥤ Type} {a b : F.Elements} (h : a = b) :
    (eqToHom h).1 = eqToHom (congrArg Sigma.fst h) := by subst h; rfl

/- English proof (translation)
Express the relevant statement in the definitionally equal form `mkChn (F := D.flip.obj U) _ _ _ = chn x`. Use `fapply CategoryTheory.Functor.ext`. Introduce `i`. Use `Sigma.ext rfl (heq_of_eq ?_)` and prove the remaining obligations. Conclude with `((chn x).map (homOfLE (Fin.zero_le i))).2`.

Introduce `i k g`. Apply `CategoryOfElements.ext` to reduce the goal to its premises. Rewrite using `[CategoryOfElements.comp_val, CategoryOfElements.comp_val]`. Use `erw [elt_eqToHom, elt_eqToHom]`. Use `erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]`.

Both sides reduce to the same expression.
-/
theorem chn_eq (D : J ⥤ PSh) (n : SimplexCategoryᵒᵖ) (U : Scheme.{0}ᵒᵖ) (x : ((hoc D).obj n).obj U) :
    (inj D n (chn x ⋙ CategoryOfElements.π _)).app U (chn x |>.obj 0).2 = x := by
  change mkChn (F := D.flip.obj U) _ _ _ = chn x
  fapply CategoryTheory.Functor.ext
  · intro i
    refine Sigma.ext rfl (heq_of_eq ?_)
    exact ((chn x).map (homOfLE (Fin.zero_le i))).2
  · intro i k g
    apply CategoryOfElements.ext
    rw [CategoryOfElements.comp_val, CategoryOfElements.comp_val]
    erw [elt_eqToHom, elt_eqToHom]
    erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨σ, a⟩ ⟨σ', a'⟩ h`. Express the relevant statement in the definitionally equal form `(inj D n σ).app U a = (inj D n σ').app U a' at h`. Establish `e : σ = σ'` using `congrArg (fun F => F ⋙ CategoryOfElements.π (D.flip.obj U)) h`. Substitute `e` using the available equality.

Establish `h2` using `Sigma.ext_iff.1 (congrArg (fun F : Fin (n.unop.len + 1) ⥤ (D.flip.obj U).Elements => F.obj 0) h)`. Establish `h3` using `eq_of_heq h2.2`. Establish `hid : ∀ b : ((evaluation _ _).obj U).obj (D.obj (σ.obj 0)), (D.map (σ.map (homOfLE (Fin.zero_le 0)))).app U b = b`. Introduce `b`. Establish `: (homOfLE (Fin.zero_le (0 : Fin (n.unop.len + 1)))) = 𝟙 _` using `rfl`.

Rewrite using `[this, σ.map_id, D.map_id]`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `(D.map (σ.map (homOfLE (Fin.zero_le 0)))).app U a = (D.map (σ.map (homOfLE (Fin.zero_le 0)))).app U a' at h3`. Rewrite `h3` using `[hid, hid]`. Substitute `h3` using the available equality.

Both sides reduce to the same expression. Introduce `x`. Conclude with `⟨⟨chn x ⋙ CategoryOfElements.π _, (chn x |>.obj 0).2⟩, chn_eq D n U x⟩`.
-/
theorem bij (D : J ⥤ PSh) (n : SimplexCategoryᵒᵖ) (U : Scheme.{0}ᵒᵖ) :
    Function.Bijective (Cofan.mk (((hoc D).obj n).obj U) (fun σ => ((evaluation _ _).obj U).map (inj D n σ)) :
      Cofan fun σ : Fin (n.unop.len + 1) ⥤ J => ((evaluation _ _).obj U).obj (D.obj (σ.obj 0))).cofanTypes.fromSigma := by
  constructor
  · rintro ⟨σ, a⟩ ⟨σ', a'⟩ h
    change (inj D n σ).app U a = (inj D n σ').app U a' at h
    have e : σ = σ' := congrArg (fun F => F ⋙ CategoryOfElements.π (D.flip.obj U)) h
    subst e
    have h2 := Sigma.ext_iff.1 (congrArg (fun F : Fin (n.unop.len + 1) ⥤ (D.flip.obj U).Elements => F.obj 0) h)
    have h3 := eq_of_heq h2.2
    have hid : ∀ b : ((evaluation _ _).obj U).obj (D.obj (σ.obj 0)), (D.map (σ.map (homOfLE (Fin.zero_le 0)))).app U b = b := by
      intro b
      have : (homOfLE (Fin.zero_le (0 : Fin (n.unop.len + 1)))) = 𝟙 _ := rfl
      rw [this, σ.map_id, D.map_id]; rfl
    change (D.map (σ.map (homOfLE (Fin.zero_le 0)))).app U a = (D.map (σ.map (homOfLE (Fin.zero_le 0)))).app U a' at h3
    rw [hid, hid] at h3
    subst h3; rfl
  · intro x
    exact ⟨⟨chn x ⋙ CategoryOfElements.π _, (chn x |>.obj 0).2⟩, chn_eq D n U x⟩

/- English proof (translation)
Introduce `J _ D n`. Use `⟨evaluationJointlyReflectsColimits _ fun U => ?_⟩` and prove the remaining obligations. Use `(isColimitMapCoconeCofanMkEquiv ((evaluation _ _).obj U) _ _).symm ?_` and prove the remaining obligations. Conclude with `Classical.choice ((Cofan.nonempty_isColimit_iff_bijective_fromSigma _).2 (bij D n U))`.
-/
theorem LeafLevel_of : LeafLevel := by
  intro J _ D n
  refine ⟨evaluationJointlyReflectsColimits _ fun U => ?_⟩
  refine (isColimitMapCoconeCofanMkEquiv ((evaluation _ _).obj U) _ _).symm ?_
  exact Classical.choice ((Cofan.nonempty_isColimit_iff_bijective_fromSigma _).2 (bij D n U))

end LateralTheory.CohomologicalPurity.LeafLevelPf
