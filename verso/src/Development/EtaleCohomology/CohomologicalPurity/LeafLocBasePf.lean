import Development.EtaleCohomology.CohomologicalPurity.LeafLocCutAug

set_option linter.unusedSimpArgs false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut.LocBasePf

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isPullback_of_app {K C : Type*} [Category K] [Category C] [HasPullbacks C] {P X Y Z : K ⥤ C}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (w : fst ≫ f = snd ≫ g)
    (h : ∀ k, IsPullback (fst.app k) (snd.app k) (f.app k) (g.app k)) : IsPullback fst snd f g :=
  IsPullback.of_isLimit (c := PullbackCone.mk fst snd w)
    (evaluationJointlyReflectsLimits _ fun k =>
      (isLimitMapConePullbackConeEquiv ((evaluation K C).obj k) w).symm (h k).isLimit)

section
variable {J : Type} [Preorder J] (D : J ⥤ Scheme.{0}) {X : Scheme.{0}} (c : ∀ j, D.obj j ⟶ X)
  (hc : Coc (D ⋙ yoneda) fun j => yoneda.map (c j)) {Y : Scheme.{0}} (g : Y ⟶ X)

include hc in
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cw {j k : J} (f : j ⟶ k) : D.map f ≫ c k = c j :=
  yoneda.map_injective (by simpa using hc j k f)

def D' : J ⥤ Scheme.{0} where
  obj j := pullback (c j) g
  map {j k} f := pullback.map (c j) g (c k) g (D.map f) (𝟙 Y) (𝟙 X) (by simp [cw D c hc f]) (by simp)
  map_id j := by
    apply pullback.hom_ext <;> simp only [Category.assoc, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.id_comp, Functor.map_comp, Functor.map_id]
    exact (congrArg (pullback.fst (c j) g ≫ ·) (D.map_id j)).trans (Category.comp_id _)
  map_comp f f' := by apply pullback.hom_ext <;> simp only [Category.assoc, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.id_comp, Functor.map_comp, Functor.map_id]

def c' (j : J) : (D' D c hc g).obj j ⟶ Y := pullback.snd (c j) g

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. A detailed English derivation is pending.
-/
theorem hc' : Coc (D' D c hc g ⋙ yoneda) fun j => yoneda.map (c' D c hc g j) := by
  intro j k f
  rw [Functor.comp_map, ← yoneda.map_comp]
  congr 1
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

def α : D' D c hc g ⋙ yoneda ⟶ D ⋙ yoneda where
  app j := yoneda.map (pullback.fst (c j) g)
  naturality j k f := by
    have e : (D' D c hc g).map f ≫ pullback.fst (c k) g = pullback.fst (c j) g ≫ D.map f := pullback.lift_fst _ _ _
    exact (yoneda.map_comp _ _).symm.trans ((congrArg yoneda.map e).trans (yoneda.map_comp _ _))

/- English proof (translation)
By extensionality, compare the relevant components. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem sq : (hocF J).map (α D c hc g) ≫ aug _ hc = aug _ (hc' D c hc g) ≫ sch.map g := by
  ext n U x
  have key : ∀ j (a : unop U ⟶ pullback (c j) g), (a ≫ pullback.fst (c j) g) ≫ c j = (a ≫ pullback.snd (c j) g) ≫ g :=
    fun j a => by rw [Category.assoc, Category.assoc, pullback.condition]
  exact key _ _

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. A detailed English derivation is pending.
-/
theorem snd_map {j k : J} (f : j ⟶ k) {V : Scheme.{0}} (a : V ⟶ (D' D c hc g).obj j) :
    (a ≫ (D' D c hc g).map f) ≫ c' D c hc g k = a ≫ c' D c hc g j := by
  rw [Category.assoc]
  congr 1
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem snd_chain {n : ℕ} {U : Scheme.{0}ᵒᵖ} (z : Fin (n + 1) ⥤ ((D' D c hc g ⋙ yoneda).flip.obj U).Elements)
    (i : Fin (n + 1)) : (z.obj i).2 ≫ c' D c hc g (z.obj i).1 = (z.obj 0).2 ≫ c' D c hc g (z.obj 0).1 := by
  have m := (z.map (homOfLE (Fin.zero_le i))).2
  rw [← m]
  exact snd_map D c hc g _ _

include hc in
/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.
-/
theorem c_chain {n : ℕ} {U : Scheme.{0}ᵒᵖ} (z : Fin (n + 1) ⥤ ((D ⋙ yoneda).flip.obj U).Elements)
    (i : Fin (n + 1)) : (z.obj i).2 ≫ c (z.obj i).1 = (z.obj 0).2 ≫ c (z.obj 0).1 := by
  have m := (z.map (homOfLE (Fin.zero_le i))).2
  rw [← m]
  change ((z.obj 0).2 ≫ D.map _) ≫ _ = _
  rw [Category.assoc, cw D c hc]

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Reduce the equality to equality of the corresponding arguments. A detailed English derivation is pending.
-/
theorem pt_ext {U : Scheme.{0}ᵒᵖ} (p q : Σ j, unop U ⟶ pullback (c j) g)
    (h1 : (⟨p.1, p.2 ≫ pullback.fst (c p.1) g⟩ : Σ j, unop U ⟶ D.obj j) = ⟨q.1, q.2 ≫ pullback.fst (c q.1) g⟩)
    (h2 : p.2 ≫ pullback.snd (c p.1) g = q.2 ≫ pullback.snd (c q.1) g) : p = q := by
  obtain ⟨j, a⟩ := p
  obtain ⟨k, b⟩ := q
  simp only [Sigma.mk.injEq] at h1
  obtain ⟨rfl, h⟩ := h1
  have h' := eq_of_heq h
  congr 1
  exact pullback.hom_ext h' h2

include hc in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem lift_map {j k : J} (f : j ⟶ k) {V : Scheme.{0}} (a : V ⟶ D.obj j) (b : V ⟶ D.obj k) (y : V ⟶ Y)
    (ha : a ≫ c j = y ≫ g) (hb : b ≫ c k = y ≫ g) (hab : a ≫ D.map f = b) :
    (pullback.lift a y ha : V ⟶ (D' D c hc g).obj j) ≫ (D' D c hc g).map f = pullback.lift b y hb := by
  apply pullback.hom_ext <;> simp only [Category.assoc, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.id_comp, Functor.map_comp, Functor.map_id, D', hab]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Express the relevant assertion in an equivalent form by its definition. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Express the relevant assertion in an equivalent form by its definition. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition.

Express the relevant assertion in an equivalent form by its definition. A detailed English derivation is pending.
-/
theorem pb : IsPullback ((hocF J).map (α D c hc g)) (aug _ (hc' D c hc g)) (aug _ hc) (sch.map g) := by
  refine isPullback_of_app (sq D c hc g) fun n => isPullback_of_app ?_ fun U => ?_
  · exact NatTrans.congr_app (sq D c hc g) n
  refine (Types.isPullback_iff _ _ _ _).2 ⟨?_, ?_, ?_⟩
  · exact NatTrans.congr_app (NatTrans.congr_app (sq D c hc g) n) U
  · rintro x y ⟨h1, h2⟩
    change chn x = chn y
    refine CategoryTheory.Functor.ext ?_ (fun _ _ _ => Subtype.ext (Subsingleton.elim _ _))
    intro i
    refine pt_ext D c g _ _ ?_ ?_
    · exact congrArg (fun z => (chn z).obj i) h1
    · exact (snd_chain D c hc g (chn x) i).trans (h2.trans (snd_chain D c hc g (chn y) i).symm)
  · intro x₂ x₃ h
    have e : ∀ i, ((chn x₂).obj i).2 ≫ c ((chn x₂).obj i).1 = x₃ ≫ g := fun i =>
      (c_chain D c hc (chn x₂) i).trans h
    refine ⟨mkChn (F := (D' D c hc g ⋙ yoneda).flip.obj U) (chn x₂ ⋙ CategoryOfElements.π _)
      (fun i => pullback.lift ((chn x₂).obj i).2 x₃ (e i)) (fun i k f => ?_), ?_, ?_⟩
    · exact lift_map D c hc g _ _ _ x₃ _ _ ((chn x₂).map f).2
    · change chn _ = chn x₂
      refine CategoryTheory.Functor.ext ?_ (fun _ _ _ => Subtype.ext (Subsingleton.elim _ _))
      intro i
      refine Sigma.ext rfl (heq_of_eq ?_)
      change pullback.lift _ _ _ ≫ pullback.fst (c ((chn x₂).obj i).1) g = _
      exact pullback.lift_fst _ _ _
    · change pullback.lift _ _ _ ≫ pullback.snd _ _ = x₃
      exact pullback.lift_snd _ _ _

end

/- English proof (translation)
Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem hr {J : Type} [Preorder J] (D : J ⥤ Scheme.{0}) {X : Scheme.{0}} (c : ∀ j, D.obj j ⟶ X)
    (ho : ∀ j, IsOpenImmersion (c j)) (hc : Coc (D ⋙ yoneda) fun j => yoneda.map (c j)) {Y : Scheme.{0}} (g : Y ⟶ X)
    (j : J) (y : Y) : y ∈ Set.range (c' D c hc g j) ↔ g y ∈ Set.range (c j) := by
  have := ho j
  change y ∈ Set.range (pullback.snd (c j) g) ↔ _
  rw [IsOpenImmersion.range_pullbackSnd]
  rfl

end LateralTheory.CohomologicalPurity.TubeCut.LocBasePf

namespace LateralTheory.CohomologicalPurity.TubeCut
open LocBasePf

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem LeafLocBase_of : EtaleLocBase := by
  intro J _ D X c ho hcov hdir hc Y g
  refine ⟨D' D c hc g, c' D c hc g, ?_, ?_, ?_, hc' D c hc g, ⟨?_⟩⟩
  · intro j
    have := ho j
    change IsOpenImmersion (pullback.snd (c j) g)
    infer_instance
  · intro y
    obtain ⟨j, hj⟩ := hcov (g y)
    exact ⟨j, (hr D c ho hc g j y).2 hj⟩
  · intro y j k h1 h2
    obtain ⟨l, hl1, hl2, hl⟩ := hdir (g y) j k ((hr D c ho hc g j y).1 h1) ((hr D c ho hc g k y).1 h2)
    exact ⟨l, hl1, hl2, (hr D c ho hc g l y).2 hl⟩
  · exact Arrow.isoMk (pb D c hc g).isoPullback.symm (Iso.refl _)
      ((IsPullback.isoPullback_inv_snd _).trans (Category.comp_id _).symm)

end LateralTheory.CohomologicalPurity.TubeCut
