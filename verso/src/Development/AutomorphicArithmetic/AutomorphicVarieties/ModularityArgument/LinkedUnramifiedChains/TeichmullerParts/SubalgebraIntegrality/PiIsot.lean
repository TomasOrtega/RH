import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.UnramifiedTrivialInertialType
open UpperTheory.V.Z.J.D
open scoped TensorProduct

namespace UpperTheory.V.Z.J.D

section Ins

variable {I : Type} [DecidableEq I]

private def ins {β : I → Type} (i₀ : I) (a : β i₀) (b : ∀ j : {i // i ≠ i₀}, β j.1) : ∀ i, β i :=
  fun i => if h : i = i₀ then h ▸ a else b ⟨i, h⟩

/- English proof (translation)
Simplify using `[ins]`.
-/
private lemma ins_self {β : I → Type} (i₀ : I) (a : β i₀) (b : ∀ j : {i // i ≠ i₀}, β j.1) :
    ins i₀ a b i₀ = a := by
  simp [ins]

/- English proof (translation)
Simplify using `[ins, j.2]`.
-/
private lemma ins_ne {β : I → Type} (i₀ : I) (a : β i₀) (b : ∀ j : {i // i ≠ i₀}, β j.1)
    (j : {i // i ≠ i₀}) : ins i₀ a b j.1 = b j := by
  simp [ins, j.2]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Distinguish the cases in `h : i = i₀`. Substitute `h` using the available equality. Conclude with `ins_self _ _ _`. Conclude with `ins_ne i₀ _ _ ⟨i, h⟩`.
-/
private lemma ins_res {β : I → Type} (i₀ : I) (g : ∀ i, β i) :
    ins i₀ (g i₀) (fun j => g j.1) = g := by
  funext i
  by_cases h : i = i₀
  · subst h; exact ins_self _ _ _
  · exact ins_ne i₀ _ _ ⟨i, h⟩

private def insHom (Gi : I → Type) [∀ i, Group (Gi i)] (i₀ : I) :
    (Gi i₀ × ∀ j : {i // i ≠ i₀}, Gi j.1) →* ∀ i, Gi i where
  toFun p := ins i₀ p.1 p.2
  map_one' := by
    funext i
    by_cases h : i = i₀
    · subst h; exact ins_self _ _ _
    · exact ins_ne i₀ _ _ ⟨i, h⟩
  map_mul' p q := by
    funext i
    by_cases h : i = i₀
    · subst h
      simp only [Pi.mul_apply, ins_self, Prod.fst_mul]
    · have := fun (r : Gi i₀ × ∀ j : {i // i ≠ i₀}, Gi j.1) => ins_ne i₀ r.1 r.2 ⟨i, h⟩
      simp only [Pi.mul_apply] at this ⊢
      rw [this, this, this]
      rfl

/- English proof (translation)
The claim follows from `ins_res i₀ g`.
-/
private lemma insHom_res (Gi : I → Type) [∀ i, Group (Gi i)] (i₀ : I) (g : ∀ i, Gi i) :
    insHom Gi i₀ (g i₀, fun j => g j.1) = g :=
  ins_res i₀ g

/- English proof (translation)
Use extensionality with `a i`. Distinguish the cases in `h : i = i₀`. Substitute `h` using the available equality. Simplify using `only [MonoidHom.comp_apply, MonoidHom.inl_apply, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same]`. Conclude with `ins_self _ _ _`.

Simplify using `only [MonoidHom.comp_apply, MonoidHom.inl_apply, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne h]`. Conclude with `ins_ne i₀ _ _ ⟨i, h⟩`.
-/
private lemma insHom_inl (Gi : I → Type) [∀ i, Group (Gi i)] (i₀ : I) :
    (insHom Gi i₀).comp (MonoidHom.inl _ _) = MonoidHom.mulSingle Gi i₀ := by
  ext a i
  by_cases h : i = i₀
  · subst h
    simp only [MonoidHom.comp_apply, MonoidHom.inl_apply, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same]
    exact ins_self _ _ _
  · simp only [MonoidHom.comp_apply, MonoidHom.inl_apply, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne h]
    exact ins_ne i₀ _ _ ⟨i, h⟩

/- English proof (translation)
Use extensionality with `a i`. Distinguish the cases in `h : i = i₀`. Substitute `h` using the available equality. Simplify using `only [MonoidHom.comp_apply, MonoidHom.inr_apply, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne (Ne.symm j.2)]`. Conclude with `ins_self _ _ _`.

Simplify using `only [MonoidHom.comp_apply, MonoidHom.inr_apply, MonoidHom.mulSingle_apply]`. Use `(ins_ne i₀ _ _ ⟨i, h⟩).trans ?_` and prove the remaining obligations. Distinguish the cases in `hj : i = j.1`. Substitute `hj` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[Pi.mulSingle_eq_of_ne hj]`. Establish `e : (⟨i, h⟩ : {i // i ≠ i₀}) ≠ j` using `fun e => hj (congrArg Subtype.val e)`. Express the relevant statement in the definitionally equal form `(Pi.mulSingle j a : ∀ j : {i // i ≠ i₀}, Gi j.1) ⟨i, h⟩ = 1`. Rewrite using `[Pi.mulSingle_eq_of_ne e]`.
-/
private lemma insHom_inr (Gi : I → Type) [∀ i, Group (Gi i)] (i₀ : I) (j : {i // i ≠ i₀}) :
    ((insHom Gi i₀).comp (MonoidHom.inr _ _)).comp (MonoidHom.mulSingle (fun j : {i // i ≠ i₀} => Gi j.1) j) =
      MonoidHom.mulSingle Gi j.1 := by
  ext a i
  by_cases h : i = i₀
  · subst h
    simp only [MonoidHom.comp_apply, MonoidHom.inr_apply, MonoidHom.mulSingle_apply,
      Pi.mulSingle_eq_of_ne (Ne.symm j.2)]
    exact ins_self _ _ _
  · simp only [MonoidHom.comp_apply, MonoidHom.inr_apply, MonoidHom.mulSingle_apply]
    refine (ins_ne i₀ _ _ ⟨i, h⟩).trans ?_
    by_cases hj : i = j.1
    · subst hj
      simp
    · rw [Pi.mulSingle_eq_of_ne hj]
      have e : (⟨i, h⟩ : {i // i ≠ i₀}) ≠ j := fun e => hj (congrArg Subtype.val e)
      change (Pi.mulSingle j a : ∀ j : {i // i ≠ i₀}, Gi j.1) ⟨i, h⟩ = 1
      rw [Pi.mulSingle_eq_of_ne e]

/- English proof (translation)
Use function extensionality and compare the values at `j`. Distinguish the cases in `hj : j = ⟨i, h⟩`. Substitute `hj` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[Function.update_of_ne hj, Function.update_of_ne (fun e => hj (Subtype.ext e))]`.
-/
private lemma res_update {β : I → Type} (i₀ i : I) (h : i ≠ i₀) (m : ∀ i, β i) (x : β i)
    [DecidableEq {i // i ≠ i₀}] [DecidableEq I] :
    (fun j : {i // i ≠ i₀} => Function.update m i x j.1) =
      Function.update (fun j : {i // i ≠ i₀} => m j.1) ⟨i, h⟩ x := by
  funext j
  by_cases hj : j = ⟨i, h⟩
  · subst hj; simp
  · rw [Function.update_of_ne hj, Function.update_of_ne (fun e => hj (Subtype.ext e))]

/- English proof (translation)
The claim follows from `funext fun j : {i // i ≠ i₀} => Function.update_of_ne j.2 _ _`.
-/
private lemma res_update_self {β : I → Type} (i₀ : I) (m : ∀ i, β i) (x : β i₀) [DecidableEq I] :
    (fun j : {i // i ≠ i₀} => Function.update m i₀ x j.1) = fun j : {i // i ≠ i₀} => m j.1 :=
  funext fun j : {i // i ≠ i₀} => Function.update_of_ne j.2 _ _

private def split (Wi : I → Type) [∀ i, AddCommGroup (Wi i)] [∀ i, Module ℂ (Wi i)] (i₀ : I) :
    (⨂[ℂ] i, Wi i) →ₗ[ℂ] Wi i₀ ⊗[ℂ] (⨂[ℂ] j : {i // i ≠ i₀}, Wi j.1) :=
  PiTensorProduct.lift
    { toFun := fun m => m i₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (fun j : {i // i ≠ i₀} => m j.1)
      map_update_add' := by
        intro _ m i x y
        by_cases h : i = i₀
        · subst h
          simp only [Function.update_self, res_update_self, TensorProduct.add_tmul]
        · classical
          simp only [Function.update_of_ne (Ne.symm h), res_update i₀ i h,
            MultilinearMap.map_update_add, TensorProduct.tmul_add]
      map_update_smul' := by
        intro _ m i c x
        by_cases h : i = i₀
        · subst h
          simp only [Function.update_self, res_update_self, TensorProduct.smul_tmul']
        · classical
          simp only [Function.update_of_ne (Ne.symm h), res_update i₀ i h,
            MultilinearMap.map_update_smul, TensorProduct.tmul_smul] }

/- English proof (translation)
Simplify using `[split]`.
-/
private lemma split_tprod (Wi : I → Type) [∀ i, AddCommGroup (Wi i)] [∀ i, Module ℂ (Wi i)] (i₀ : I)
    (m : ∀ i, Wi i) :
    split Wi i₀ (PiTensorProduct.tprod ℂ m) =
      m i₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (fun j : {i // i ≠ i₀} => m j.1) := by
  simp [split]

/- English proof (translation)
Use `LinearMap.range_eq_top.2 fun t => ?_` and prove the remaining obligations. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, map_zero _⟩`. Consider the case `add a b ha hb`. Take `⟨x, rfl⟩` from `ha`.

Take `⟨y, rfl⟩` from `hb`. Conclude with `⟨x + y, map_add _ _ _⟩`. Consider the case `tmul w t`. Proceed by induction on `t using PiTensorProduct.induction_on with`. Consider the case `smul_tprod r m`.

Use `⟨r • PiTensorProduct.tprod ℂ (ins i₀ w m), ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, split_tprod, ins_self, TensorProduct.tmul_smul]`. Use `congr 3`. Use function extensionality and compare the values at `j`. Conclude with `ins_ne i₀ _ _ j`.

Consider the case `add a b ha hb`. Take `⟨x, hx⟩` from `ha`. Take `⟨y, hy⟩` from `hb`. Conclude with `⟨x + y, by rw [map_add, hx, hy, TensorProduct.tmul_add]⟩`.
-/
private lemma split_range (Wi : I → Type) [∀ i, AddCommGroup (Wi i)] [∀ i, Module ℂ (Wi i)] (i₀ : I) :
    LinearMap.range (split Wi i₀) = ⊤ := by
  refine LinearMap.range_eq_top.2 fun t => ?_
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | add a b ha hb =>
    obtain ⟨x, rfl⟩ := ha
    obtain ⟨y, rfl⟩ := hb
    exact ⟨x + y, map_add _ _ _⟩
  | tmul w t =>
    induction t using PiTensorProduct.induction_on with
    | smul_tprod r m =>
      refine ⟨r • PiTensorProduct.tprod ℂ (ins i₀ w m), ?_⟩
      rw [map_smul, split_tprod, ins_self, TensorProduct.tmul_smul]
      congr 3
      funext j
      exact ins_ne i₀ _ _ j
    | add a b ha hb =>
      obtain ⟨x, hx⟩ := ha
      obtain ⟨y, hy⟩ := hb
      exact ⟨x + y, by rw [map_add, hx, hy, TensorProduct.tmul_add]⟩

/- English proof (translation)
Simplify using `only [piRep, MonoidHom.comp_apply, PiTensorProduct.mapMonoidHom_apply, PiTensorProduct.map_tprod]`. Both sides reduce to the same expression.
-/
private lemma piRep_tprod {Gi Wi : I → Type} [∀ i, Group (Gi i)] [∀ i, AddCommGroup (Wi i)]
    [∀ i, Module ℂ (Wi i)] (τ : ∀ i, Representation ℂ (Gi i) (Wi i)) (g : ∀ i, Gi i) (m : ∀ i, Wi i) :
    piRep τ g (PiTensorProduct.tprod ℂ m) = PiTensorProduct.tprod ℂ fun i => τ i (g i) (m i) := by
  simp only [piRep, MonoidHom.comp_apply, PiTensorProduct.mapMonoidHom_apply, PiTensorProduct.map_tprod]
  rfl

/- English proof (translation)
Proceed by induction on `t using PiTensorProduct.induction_on with`. Consider the case `smul_tprod r m`. Rewrite using `[map_smul, map_smul, map_smul, map_smul, piRep_tprod, split_tprod, split_tprod]`. Simplify using `only [box, Representation.tprod_apply, TensorProduct.map_tmul, MonoidHom.comp_apply, MonoidHom.coe_fst, MonoidHom.coe_snd, piRep_tprod]`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`.
-/
private lemma split_intw [Fintype I] {Gi Wi : I → Type} [∀ i, Group (Gi i)] [∀ i, AddCommGroup (Wi i)]
    [∀ i, Module ℂ (Wi i)] (τ : ∀ i, Representation ℂ (Gi i) (Wi i)) (i₀ : I) (g : ∀ i, Gi i)
    (t : ⨂[ℂ] i, Wi i) :
    split Wi i₀ (piRep τ g t) =
      box (τ i₀) (piRep fun j : {i // i ≠ i₀} => τ j.1) (g i₀, fun j => g j.1) (split Wi i₀ t) := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    rw [map_smul, map_smul, map_smul, map_smul, piRep_tprod, split_tprod, split_tprod]
    simp only [box, Representation.tprod_apply, TensorProduct.map_tmul, MonoidHom.comp_apply,
      MonoidHom.coe_fst, MonoidHom.coe_snd, piRep_tprod]
  | add a b ha hb => simp only [map_add, ha, hb]

end Ins

/- English proof (translation)
Introduce `x _`. Set `f : (⨂[ℂ] i, Wi i) →ₗ[ℂ] X` to `(LinearMap.toSpanSingleton ℂ X x).comp (PiTensorProduct.isEmptyEquiv I).toLinearMap`. Establish `hf : Intw (piRep τ) κ f`. Introduce `g v`. Establish `hg : g = 1` using `Subsingleton.elim _ _`.

Substitute `hg` using the available equality. Simplify using the standard rewrite rules. Use `Submodule.mem_iSup_of_mem ⟨f, hf⟩ ⟨PiTensorProduct.tprod ℂ isEmptyElim, ?_⟩` and prove the remaining obligations. Simplify using `[f, PiTensorProduct.isEmptyEquiv_apply_tprod]`.
-/
private lemma piIsot_empty {I : Type} [Fintype I] [DecidableEq I] [IsEmpty I] (Gi Wi : I → Type)
    [∀ i, Group (Gi i)] [∀ i, AddCommGroup (Wi i)] [∀ i, Module ℂ (Wi i)]
    (τ : ∀ i, Representation ℂ (Gi i) (Wi i)) {X : Type} [AddCommGroup X] [Module ℂ X]
    (κ : Representation ℂ (∀ i, Gi i) X) : Isot κ (piRep τ) := by
  intro x _
  let f : (⨂[ℂ] i, Wi i) →ₗ[ℂ] X :=
    (LinearMap.toSpanSingleton ℂ X x).comp (PiTensorProduct.isEmptyEquiv I).toLinearMap
  have hf : Intw (piRep τ) κ f := by
    intro g v
    have hg : g = 1 := Subsingleton.elim _ _
    subst hg
    simp
  refine Submodule.mem_iSup_of_mem ⟨f, hf⟩ ⟨PiTensorProduct.tprod ℂ isEmptyElim, ?_⟩
  simp [f, PiTensorProduct.isEmptyEquiv_apply_tprod]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `I _ _ hc Gi Wi _ _ _ τ _ X _ _ κ _`. Use `haveI : IsEmpty I := Fintype.card_eq_zero_iff.1 hc`. Conclude with `piIsot_empty Gi Wi τ κ`.

Consider the case `succ n ih`. Introduce `I _ _ hc Gi Wi _ _ _ τ hτ X _ _ κ hκ`. Use `haveI : Nonempty I := Fintype.card_pos_iff.1 (by omega)`. Take `⟨i₀⟩` from `‹Nonempty I›`. Establish `hJ : Fintype.card {i // i ≠ i₀} = n`.

Simplify using `[Fintype.card_subtype_compl, hc]`. Set `J` to `{i // i ≠ i₀}`. Set `κ' : Representation ℂ (Gi i₀ × ∀ j : J, Gi j.1) X` to `κ.comp (insHom Gi i₀)`. Establish `h1 : Isot (κ'.comp (MonoidHom.inl _ _)) (τ i₀)`. Establish `: κ'.comp (MonoidHom.inl _ _) = κ.comp (MonoidHom.mulSingle Gi i₀)`.

Rewrite using `[← insHom_inl]`. Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `hκ i₀`. Establish `h2 : Isot (κ'.comp (MonoidHom.inr _ _)) (piRep fun j : J => τ j.1)`.

Use `ih J hJ (fun j => Gi j.1) (fun j => Wi j.1) (fun j => τ j.1) (fun j => hτ j.1) X (κ'.comp (MonoidHom.inr _ _)) fun j => ?_` and prove the remaining obligations. Establish `: (κ'.comp (MonoidHom.inr _ _)).comp (MonoidHom.mulSingle (fun j : J => Gi j.1) j) = κ.comp (MonoidHom.mulSingle Gi j.1)`. Rewrite using `[← insHom_inr]`. Both sides reduce to the same expression. Rewrite using `[this]`.

Conclude with `hκ j.1`. Establish `h3` using `hB _ _ _ _ (τ i₀) (piRep fun j : J => τ j.1) (hτ i₀) (hP J (fun j => Gi j.1) (fun j => Wi j.1) (fun j => τ j.1) fun j => hτ j.1) X κ' h1 h2`. Use `le_trans h3 (iSup_le fun f => ?_)` and prove the remaining obligations. Establish `hf : Intw (piRep τ) κ (f.1.comp (split Wi i₀))`. Introduce `g t`.

Use `f.2 (g i₀, fun j => g j.1) (split Wi i₀ t)` as an intermediate fact. Simplify using `only [LinearMap.comp_apply]`. Rewrite using `[split_intw, this]`. Express the relevant statement in the definitionally equal form `κ (insHom Gi i₀ _) _ = _`. Rewrite using `[insHom_res]`.

Use `le_iSup_of_le ⟨_, hf⟩ ?_` and prove the remaining obligations. Rewrite using `[LinearMap.range_comp_of_range_eq_top _ (split_range Wi i₀)]`.
-/
private lemma piIsot_card (hB : BoxIsot) (hP : PiIrr) (n : ℕ) :
    ∀ (I : Type) [Fintype I] [DecidableEq I], Fintype.card I = n → ∀ (Gi Wi : I → Type) [∀ i, Group (Gi i)]
      [∀ i, AddCommGroup (Wi i)] [∀ i, Module ℂ (Wi i)] (τ : ∀ i, Representation ℂ (Gi i) (Wi i)),
      (∀ i, AbsIrr (τ i)) → ∀ (X : Type) [AddCommGroup X] [Module ℂ X]
      (κ : Representation ℂ (∀ i, Gi i) X), (∀ i, Isot (κ.comp (MonoidHom.mulSingle Gi i)) (τ i)) →
      Isot κ (piRep τ) := by
  induction n with
  | zero =>
    intro I _ _ hc Gi Wi _ _ _ τ _ X _ _ κ _
    haveI : IsEmpty I := Fintype.card_eq_zero_iff.1 hc
    exact piIsot_empty Gi Wi τ κ
  | succ n ih =>
    intro I _ _ hc Gi Wi _ _ _ τ hτ X _ _ κ hκ
    haveI : Nonempty I := Fintype.card_pos_iff.1 (by omega)
    obtain ⟨i₀⟩ := ‹Nonempty I›
    have hJ : Fintype.card {i // i ≠ i₀} = n := by
      simp [Fintype.card_subtype_compl, hc]
    let J := {i // i ≠ i₀}
    let κ' : Representation ℂ (Gi i₀ × ∀ j : J, Gi j.1) X := κ.comp (insHom Gi i₀)
    have h1 : Isot (κ'.comp (MonoidHom.inl _ _)) (τ i₀) := by
      have : κ'.comp (MonoidHom.inl _ _) = κ.comp (MonoidHom.mulSingle Gi i₀) := by
        rw [← insHom_inl]; rfl
      rw [this]
      exact hκ i₀
    have h2 : Isot (κ'.comp (MonoidHom.inr _ _)) (piRep fun j : J => τ j.1) := by
      refine ih J hJ (fun j => Gi j.1) (fun j => Wi j.1) (fun j => τ j.1) (fun j => hτ j.1) X
        (κ'.comp (MonoidHom.inr _ _)) fun j => ?_
      have : (κ'.comp (MonoidHom.inr _ _)).comp (MonoidHom.mulSingle (fun j : J => Gi j.1) j) =
          κ.comp (MonoidHom.mulSingle Gi j.1) := by
        rw [← insHom_inr]; rfl
      rw [this]
      exact hκ j.1
    have h3 := hB _ _ _ _ (τ i₀) (piRep fun j : J => τ j.1) (hτ i₀)
      (hP J (fun j => Gi j.1) (fun j => Wi j.1) (fun j => τ j.1) fun j => hτ j.1) X κ' h1 h2
    refine le_trans h3 (iSup_le fun f => ?_)
    have hf : Intw (piRep τ) κ (f.1.comp (split Wi i₀)) := by
      intro g t
      have := f.2 (g i₀, fun j => g j.1) (split Wi i₀ t)
      simp only [LinearMap.comp_apply]
      rw [split_intw, this]
      change κ (insHom Gi i₀ _) _ = _
      rw [insHom_res]
    refine le_iSup_of_le ⟨_, hf⟩ ?_
    rw [LinearMap.range_comp_of_range_eq_top _ (split_range Wi i₀)]

/- English proof (translation)
Introduce `hB hP I _ _ Gi Wi _ _ _ τ hτ X _ _ κ hκ`. Conclude with `piIsot_card hB hP _ I rfl Gi Wi τ hτ X κ hκ`.
-/
theorem piIsot :
    BoxIsot → PiIrr → PiIsot := by
  intro hB hP I _ _ Gi Wi _ _ _ τ hτ X _ _ κ hκ
  exact piIsot_card hB hP _ I rfl Gi Wi τ hτ X κ hκ

end UpperTheory.V.Z.J.D
