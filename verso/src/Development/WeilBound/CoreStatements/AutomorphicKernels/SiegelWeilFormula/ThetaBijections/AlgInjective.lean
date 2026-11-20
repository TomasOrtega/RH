import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticChangeOfGoodModelsIntertwines

noncomputable section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp
open scoped Matrix TensorProduct

namespace PositivityTheory.SiegelWeilFormula.TBij

variable {F : Type} [Field F] [NumberField F]

instance nontrivAF : Nontrivial (AF F) := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial

/- English proof (translation)
The claim follows from `AdeleRing.algebraMap_injective (𝓞 F) F`.
-/
theorem alg_injective : Function.Injective (algebraMap F (AF F)) := AdeleRing.algebraMap_injective (𝓞 F) F

def om {R κ : Type} [CommRing R] [Fintype κ] (u u' : (κ → R) × (κ → R)) : R := u.1 ⬝ᵥ u'.2 - u'.1 ⬝ᵥ u.2

def jj (κ R : Type) [CommRing R] [DecidableEq κ] : Matrix (κ ⊕ κ) (κ ⊕ κ) R := Matrix.fromBlocks 0 1 (-1) 0

/- English proof (translation)
Simplify using `only [om, jj, Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.zero_mulVec, Matrix.one_mulVec, Matrix.neg_mulVec, zero_add, add_zero, sumElim_dotProduct_sumElim]`. Rewrite using `[dotProduct_neg, dotProduct_comm u.2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem om_eq {R κ : Type} [CommRing R] [Fintype κ] [DecidableEq κ] (u u' : (κ → R) × (κ → R)) :
    om u u' = Sum.elim u.1 u.2 ⬝ᵥ (jj κ R *ᵥ Sum.elim u'.1 u'.2) := by
  simp only [om, jj, Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.zero_mulVec,
    Matrix.one_mulVec, Matrix.neg_mulVec, zero_add, add_zero, sumElim_dotProduct_sumElim]
  rw [dotProduct_neg, dotProduct_comm u.2]
  ring

def ratV {κ : Type} (y z : κ → F) : (κ → AF F) × (κ → AF F) :=
  (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))

/- English proof (translation)
Set `S` to `LinearEquiv.sumArrowLequivProdArrow κ κ (AF F) (AF F)`. Establish `hS : ∀ u : (κ → AF F) × (κ → AF F), S.symm u = Sum.elim u.1 u.2` using `fun u => by`. Apply the tactic sequence `funext p; cases p <;> rfl`. Establish `hS' : ∀ V : κ ⊕ κ → AF F, S V = (V ∘ Sum.inl, V ∘ Sum.inr)` using `fun V => rfl`. Set `L : (κ ⊕ κ → AF F) →ₗ[AF F] (κ ⊕ κ → AF F)` to `S.symm.toLinearMap ∘ₗ e₂ ∘ₗ e₁.symm.toLinearMap ∘ₗ S.toLinearMap`.

Use `set A := LinearMap.toMatrix' L with hA`. Establish `hact : ∀ (M : Matrix (κ ⊕ κ) (κ ⊕ κ) (AF F)) u, act M u = S (M *ᵥ S.symm u)` using `fun M u => by`. Rewrite using `[hS, hS']`. Both sides reduce to the same expression. Establish `hL : ∀ w, e₂ w = act A (e₁ w)` using `fun w => by`.

Rewrite using `[hact, hA, LinearMap.toMatrix'_mulVec]`. Simplify using `[L]`. Establish `hr : ∀ p q, ∃ x : F, algebraMap F (AF F) x = A p q`. Introduce `p q`. Rewrite using `[hA, LinearMap.toMatrix'_apply]`.

Take `⟨y, z, h⟩` from `hrat (e₁.symm (S (Pi.single q 1))) ⟨fun i => (Pi.single q (1 : F) : κ ⊕ κ → F) (Sum.inl i), fun i => (Pi.single q (1 : F) : κ ⊕ κ → F) (Sum.inr i), by`. Rewrite using `[LinearEquiv.apply_symm_apply, hS', ratV]`. Use extensionality with `i`. Apply the tactic sequence `simp only [Function.comp_apply, Pi.single_apply]; split_ifs <;> simp`. Apply the tactic sequence `simp only [Function.comp_apply, Pi.single_apply]; split_ifs <;> simp⟩`.

Use `⟨Sum.elim y z p, ?_⟩` and prove the remaining obligations. Simplify using `only [L, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, h, hS, ratV]`. Apply the tactic sequence `cases p <;> rfl`. Use `choose a0 ha0 using hr`. Establish `hmap : (Matrix.of a0).map (algebraMap F (AF F)) = A`.

Use extensionality with `p q`. Simplify using `[ha0]`. Establish `hkey : ∀ V V' : κ ⊕ κ → AF F, (A *ᵥ V) ⬝ᵥ (jj κ (AF F) *ᵥ (A *ᵥ V')) = V ⬝ᵥ (jj κ (AF F) *ᵥ V')`. Introduce `V V'`. Establish `h1 : ∀ V : κ ⊕ κ → AF F, A *ᵥ V = S.symm (e₂ (e₁.symm (S V)))` using `fun V => by`.

Rewrite using `[hA, LinearMap.toMatrix'_mulVec]`. Both sides reduce to the same expression. Establish `h2 : ∀ V : κ ⊕ κ → AF F, V = S.symm (e₁ (e₁.symm (S V)))` using `fun V => by simp`. Rewrite using `[h1, h1, hS, hS, ← om_eq, hom, om_eq, ← hS, ← hS, ← h2, ← h2]`. Establish `hsymp : Aᵀ * jj κ (AF F) * A = jj κ (AF F)`.

Use extensionality with `p q`. Establish `e1 : ∀ (M : Matrix (κ ⊕ κ) (κ ⊕ κ) (AF F)) (i j : κ ⊕ κ), Pi.single i 1 ⬝ᵥ (M *ᵥ Pi.single j 1) = M i j` using `fun M i j => by`. Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]`.

Use `_ = Pi.single p 1 ⬝ᵥ (jj κ (AF F) *ᵥ Pi.single q 1) := hkey _ _`. Use `_ = jj κ (AF F) p q := e1 _ p q`. Establish `hjj : (jj κ F).map (algebraMap F (AF F)) = jj κ (AF F)`. Simplify using `only [jj, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _)]`. Use `congr 1`.

Use extensionality with `i j`. Simplify using `[Matrix.one_apply]`. Use `⟨Matrix.of a0, Matrix.map_injective alg_injective ?_, fun w => by rw [hmap]; exact hL w⟩` and prove the remaining obligations. Simplify using `only`. Rewrite using `[Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hmap, hjj, hsymp]`.
-/
theorem exists_symp {κ : Type} [Fintype κ] [DecidableEq κ] {W : Type} [AddCommGroup W] [Module (AF F) W]
    (e₁ : W ≃ₗ[AF F] (κ → AF F) × (κ → AF F)) (e₂ : W →ₗ[AF F] (κ → AF F) × (κ → AF F))
    (hom : ∀ w w', om (e₂ w) (e₂ w') = om (e₁ w) (e₁ w'))
    (hrat : ∀ w : W, (∃ y z : κ → F, e₁ w = ratV y z) → ∃ y z : κ → F, e₂ w = ratV y z) :
    ∃ a : Matrix (κ ⊕ κ) (κ ⊕ κ) F, aᵀ * jj κ F * a = jj κ F ∧
      ∀ w, e₂ w = act (a.map (algebraMap F (AF F))) (e₁ w) := by
  classical
  let S := LinearEquiv.sumArrowLequivProdArrow κ κ (AF F) (AF F)
  have hS : ∀ u : (κ → AF F) × (κ → AF F), S.symm u = Sum.elim u.1 u.2 := fun u => by
    funext p; cases p <;> rfl
  have hS' : ∀ V : κ ⊕ κ → AF F, S V = (V ∘ Sum.inl, V ∘ Sum.inr) := fun V => rfl
  let L : (κ ⊕ κ → AF F) →ₗ[AF F] (κ ⊕ κ → AF F) :=
    S.symm.toLinearMap ∘ₗ e₂ ∘ₗ e₁.symm.toLinearMap ∘ₗ S.toLinearMap
  set A := LinearMap.toMatrix' L with hA
  have hact : ∀ (M : Matrix (κ ⊕ κ) (κ ⊕ κ) (AF F)) u, act M u = S (M *ᵥ S.symm u) := fun M u => by
    rw [hS, hS']; rfl
  have hL : ∀ w, e₂ w = act A (e₁ w) := fun w => by
    rw [hact, hA, LinearMap.toMatrix'_mulVec]
    simp [L]
  have hr : ∀ p q, ∃ x : F, algebraMap F (AF F) x = A p q := by
    intro p q
    rw [hA, LinearMap.toMatrix'_apply]
    obtain ⟨y, z, h⟩ := hrat (e₁.symm (S (Pi.single q 1)))
      ⟨fun i => (Pi.single q (1 : F) : κ ⊕ κ → F) (Sum.inl i), fun i => (Pi.single q (1 : F) : κ ⊕ κ → F) (Sum.inr i), by
        rw [LinearEquiv.apply_symm_apply, hS', ratV]
        ext i
        · simp only [Function.comp_apply, Pi.single_apply]; split_ifs <;> simp
        · simp only [Function.comp_apply, Pi.single_apply]; split_ifs <;> simp⟩
    refine ⟨Sum.elim y z p, ?_⟩
    simp only [L, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, h, hS, ratV]
    cases p <;> rfl
  choose a0 ha0 using hr
  have hmap : (Matrix.of a0).map (algebraMap F (AF F)) = A := by
    ext p q; simp [ha0]
  have hkey : ∀ V V' : κ ⊕ κ → AF F, (A *ᵥ V) ⬝ᵥ (jj κ (AF F) *ᵥ (A *ᵥ V')) = V ⬝ᵥ (jj κ (AF F) *ᵥ V') := by
    intro V V'
    have h1 : ∀ V : κ ⊕ κ → AF F, A *ᵥ V = S.symm (e₂ (e₁.symm (S V))) := fun V => by
      rw [hA, LinearMap.toMatrix'_mulVec]; rfl
    have h2 : ∀ V : κ ⊕ κ → AF F, V = S.symm (e₁ (e₁.symm (S V))) := fun V => by simp
    rw [h1, h1, hS, hS, ← om_eq, hom, om_eq, ← hS, ← hS, ← h2, ← h2]
  have hsymp : Aᵀ * jj κ (AF F) * A = jj κ (AF F) := by
    ext p q
    have e1 : ∀ (M : Matrix (κ ⊕ κ) (κ ⊕ κ) (AF F)) (i j : κ ⊕ κ),
        Pi.single i 1 ⬝ᵥ (M *ᵥ Pi.single j 1) = M i j := fun M i j => by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    calc (Aᵀ * jj κ (AF F) * A) p q = Pi.single p 1 ⬝ᵥ ((Aᵀ * jj κ (AF F) * A) *ᵥ Pi.single q 1) := (e1 _ p q).symm
      _ = (A *ᵥ Pi.single p 1) ⬝ᵥ (jj κ (AF F) *ᵥ (A *ᵥ Pi.single q 1)) := by
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
      _ = Pi.single p 1 ⬝ᵥ (jj κ (AF F) *ᵥ Pi.single q 1) := hkey _ _
      _ = jj κ (AF F) p q := e1 _ p q
  have hjj : (jj κ F).map (algebraMap F (AF F)) = jj κ (AF F) := by
    simp only [jj, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _)]
    congr 1
    ext i j
    simp [Matrix.one_apply]
  refine ⟨Matrix.of a0, Matrix.map_injective alg_injective ?_, fun w => by rw [hmap]; exact hL w⟩
  dsimp only
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hmap, hjj, hsymp]

variable {E : Type} [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Establish `h` using `e.finrank_eq`. Rewrite `h` using `[Module.finrank_matrix, Module.finrank_baseChange, Module.finrank_eq_card_basis bs, Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem card_eq {κ α β : Type} [Fintype κ] [Fintype α] [Fintype β] (bs : Module.Basis (Fin 2) F E)
    (e : Matrix α β (AE F E) ≃ₗ[AF F] (κ → AF F) × (κ → AF F)) :
    Fintype.card κ = Fintype.card α * Fintype.card β := by
  have h := e.finrank_eq
  rw [Module.finrank_matrix, Module.finrank_baseChange, Module.finrank_eq_card_basis bs, Module.finrank_prod,
    Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
  linarith

/- English proof (translation)
Introduce `x x' h`. Use extensionality with `i j`. Establish `h1` using `congrFun (congrFun h i) j`. Conclude with `Algebra.TensorProduct.includeRight_injective (A := AF F) (R := F) (B := E) alg_injective h1`.
-/
theorem incM_injective {α β : Type} : Function.Injective (incM F : Matrix α β E → _) := by
  intro x x' h
  ext i j
  have h1 := congrFun (congrFun h i) j
  exact Algebra.TensorProduct.includeRight_injective (A := AF F) (R := F) (B := E) alg_injective h1

/- English proof (translation)
Use `choose fy fz hf using hr`. Establish `hinj : Function.Injective (algebraMap F (AF F))` using `alg_injective`. Establish `hadd : ∀ x x' : Matrix α β E, incM F (x + x') = incM F x + incM F x'` using `fun x x' => by`. Use extensionality with `i j`. Simplify using `[incM]`.

Establish `hsmul : ∀ (r : F) (x : Matrix α β E), incM F (r • x) = algebraMap F (AF F) r • incM F x` using `fun r x => by`. Use extensionality with `i j`. Simplify using `only [incM, Matrix.map_apply, Matrix.smul_apply]`. Rewrite using `[show inclR (F := F) (AF F) (r • x i j) = (1 : AF F) ⊗ₜ[F] (r • x i j) from rfl, show inclR (F := F) (AF F) (x i j) = (1 : AF F) ⊗ₜ[F] x i j from rfl, TensorProduct.tmul_smul, algebraMap_smul]`. Set `f : Matrix α β E →ₗ[F] (κ → F) × (κ → F)` to `{ toFun := fun x => (fy x, fz x) map_add' := fun x x' => by`.

Establish `h` using `congrArg e (hadd x x')`. Rewrite `h` using `[map_add, hf, hf, hf]`. Use extensionality with `i`. Conclude with `hinj (by simpa [ratV] using congrFun (congrArg Prod.fst h) i)`. Conclude with `hinj (by simpa [ratV] using congrFun (congrArg Prod.snd h) i)`.

Use the proof step `map_smul' := fun r x => by`. Establish `h` using `congrArg e (hsmul r x)`. Rewrite `h` using `[map_smul, hf, hf]`. Use extensionality with `i`. Conclude with `hinj (by simpa [ratV, Algebra.smul_def] using congrFun (congrArg Prod.fst h) i)`.

Conclude with `hinj (by simpa [ratV, Algebra.smul_def] using congrFun (congrArg Prod.snd h) i) }`. Establish `hfi : Function.Injective f`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `x hx`. Establish `h1 : e (incM F x) = 0`.

Rewrite using `[hf]`. Establish `h2 : fy x = 0` using `congrArg Prod.fst hx`. Establish `h3 : fz x = 0` using `congrArg Prod.snd hx`. Simplify using `[ratV, h2, h3]`. Both sides reduce to the same expression.

Conclude with `incM_injective (by rw [(LinearEquiv.map_eq_zero_iff e).1 h1]; ext i j; simp [incM])`. Establish `hdim : Module.finrank F (Matrix α β E) = Module.finrank F ((κ → F) × (κ → F))`. Rewrite using `[Module.finrank_matrix, Module.finrank_eq_card_basis bs, Module.finrank_prod, Module.finrank_fintype_fun_eq_card, card_eq bs e, Fintype.card_fin]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨x, hx⟩` from `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hfi (y, z)`.

Use `⟨x, ?_⟩` and prove the remaining obligations. Rewrite using `[hf]`. Establish `h2 : fy x = y` using `congrArg Prod.fst hx`. Establish `h3 : fz x = z` using `congrArg Prod.snd hx`. Rewrite using `[h2, h3]`.
-/
theorem rat_surj {κ α β : Type} [Fintype κ] [Fintype α] [Fintype β] (bs : Module.Basis (Fin 2) F E)
    (e : Matrix α β (AE F E) ≃ₗ[AF F] (κ → AF F) × (κ → AF F))
    (hr : ∀ x : Matrix α β E, ∃ y z : κ → F, e (incM F x) = ratV y z) (y z : κ → F) :
    ∃ x : Matrix α β E, e (incM F x) = ratV y z := by
  classical
  choose fy fz hf using hr
  have hinj : Function.Injective (algebraMap F (AF F)) := alg_injective
  have hadd : ∀ x x' : Matrix α β E, incM F (x + x') = incM F x + incM F x' := fun x x' => by
    ext i j; simp [incM]
  have hsmul : ∀ (r : F) (x : Matrix α β E), incM F (r • x) = algebraMap F (AF F) r • incM F x := fun r x => by
    ext i j
    simp only [incM, Matrix.map_apply, Matrix.smul_apply]
    rw [show inclR (F := F) (AF F) (r • x i j) = (1 : AF F) ⊗ₜ[F] (r • x i j) from rfl,
      show inclR (F := F) (AF F) (x i j) = (1 : AF F) ⊗ₜ[F] x i j from rfl, TensorProduct.tmul_smul,
      algebraMap_smul]
  let f : Matrix α β E →ₗ[F] (κ → F) × (κ → F) :=
    { toFun := fun x => (fy x, fz x)
      map_add' := fun x x' => by
        have h := congrArg e (hadd x x')
        rw [map_add, hf, hf, hf] at h
        ext i
        · exact hinj (by simpa [ratV] using congrFun (congrArg Prod.fst h) i)
        · exact hinj (by simpa [ratV] using congrFun (congrArg Prod.snd h) i)
      map_smul' := fun r x => by
        have h := congrArg e (hsmul r x)
        rw [map_smul, hf, hf] at h
        ext i
        · exact hinj (by simpa [ratV, Algebra.smul_def] using congrFun (congrArg Prod.fst h) i)
        · exact hinj (by simpa [ratV, Algebra.smul_def] using congrFun (congrArg Prod.snd h) i) }
  have hfi : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h1 : e (incM F x) = 0 := by
      rw [hf]
      have h2 : fy x = 0 := congrArg Prod.fst hx
      have h3 : fz x = 0 := congrArg Prod.snd hx
      simp [ratV, h2, h3]; rfl
    exact incM_injective (by rw [(LinearEquiv.map_eq_zero_iff e).1 h1]; ext i j; simp [incM])
  have hdim : Module.finrank F (Matrix α β E) = Module.finrank F ((κ → F) × (κ → F)) := by
    rw [Module.finrank_matrix, Module.finrank_eq_card_basis bs, Module.finrank_prod, Module.finrank_fintype_fun_eq_card,
      card_eq bs e, Fintype.card_fin]
    ring
  obtain ⟨x, hx⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hfi (y, z)
  refine ⟨x, ?_⟩
  rw [hf]
  have h2 : fy x = y := congrArg Prod.fst hx
  have h3 : fz x = z := congrArg Prod.snd hx
  rw [h2, h3]

end PositivityTheory.SiegelWeilFormula.TBij

end
