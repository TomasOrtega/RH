import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JpUnif

open Matrix GlobalTheory.CompanionTheory.Jp Module

namespace GlobalTheory.CompanionTheory.Jp.Dbl

variable {k : Type} [Field k]

/- English proof (translation)
Use `⟨(Submodule.prodEquivOfIsCompl Y₁ Z₁ h₁).symm ≪≫ₗ (u.prodCongr v) ≪≫ₗ Submodule.prodEquivOfIsCompl Y₂ Z₂ h₂, ?_, ?_⟩` and prove the remaining obligations. Introduce `y`. Simplify using the standard rewrite rules. Introduce `z`. Simplify using the standard rewrite rules.
-/
theorem glue {X₁ X₂ : Type} [AddCommGroup X₁] [Module k X₁] [AddCommGroup X₂] [Module k X₂]
    {Y₁ Z₁ : Submodule k X₁} {Y₂ Z₂ : Submodule k X₂} (h₁ : IsCompl Y₁ Z₁) (h₂ : IsCompl Y₂ Z₂)
    (u : Y₁ ≃ₗ[k] Y₂) (v : Z₁ ≃ₗ[k] Z₂) :
    ∃ e : X₁ ≃ₗ[k] X₂, (∀ y : Y₁, e y = u y) ∧ ∀ z : Z₁, e z = v z := by
  refine ⟨(Submodule.prodEquivOfIsCompl Y₁ Z₁ h₁).symm ≪≫ₗ (u.prodCongr v) ≪≫ₗ
    Submodule.prodEquivOfIsCompl Y₂ Z₂ h₂, ?_, ?_⟩
  · intro y; simp
  · intro z; simp

/- English proof (translation)
Take `⟨Z₁, h₁⟩` from `Submodule.exists_isCompl Y₁`. Take `⟨Z₂, h₂⟩` from `Submodule.exists_isCompl Y₂`. Establish `a₁` using `Submodule.finrank_add_eq_of_isCompl h₁`. Establish `a₂` using `Submodule.finrank_add_eq_of_isCompl h₂`. Take `⟨e, he, -⟩` from `glue h₁ h₂ (LinearEquiv.ofFinrankEq _ _ hY) (LinearEquiv.ofFinrankEq _ _ (by omega))`.

Use `⟨e, fun y hy => ?_⟩` and prove the remaining obligations. Use `he ⟨y, hy⟩` as an intermediate fact. Simplify using `only at this`. Rewrite using `[this]`. Conclude with `Subtype.property _`.
-/
theorem exists_equiv_pair {X₁ X₂ : Type} [AddCommGroup X₁] [Module k X₁] [AddCommGroup X₂] [Module k X₂]
    [FiniteDimensional k X₁] [FiniteDimensional k X₂] (hX : finrank k X₁ = finrank k X₂)
    (Y₁ : Submodule k X₁) (Y₂ : Submodule k X₂) (hY : finrank k Y₁ = finrank k Y₂) :
    ∃ e : X₁ ≃ₗ[k] X₂, ∀ y ∈ Y₁, e y ∈ Y₂ := by
  obtain ⟨Z₁, h₁⟩ := Submodule.exists_isCompl Y₁
  obtain ⟨Z₂, h₂⟩ := Submodule.exists_isCompl Y₂
  have a₁ := Submodule.finrank_add_eq_of_isCompl h₁
  have a₂ := Submodule.finrank_add_eq_of_isCompl h₂
  obtain ⟨e, he, -⟩ := glue h₁ h₂ (LinearEquiv.ofFinrankEq _ _ hY)
    (LinearEquiv.ofFinrankEq _ _ (by omega))
  refine ⟨e, fun y hy => ?_⟩
  have := he ⟨y, hy⟩
  simp only at this
  rw [this]
  exact Subtype.property _

variable {V : Type} [AddCommGroup V] [Module k V]

/- English proof (translation)
Take `⟨C, hC⟩` from `Submodule.exists_isCompl (S ⊓ T)`. Use `⟨C ⊓ T, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.disjoint_def]`. Introduce `x hS hx`. Establish `: x ∈ (S ⊓ T) ⊓ C` using `⟨⟨hS, hx.2⟩, hx.1⟩`.

Rewrite `this` using `[hC.inf_eq_bot]`. Simplify using `using this`. Rewrite using `[← sup_inf_assoc_of_le C (inf_le_right : S ⊓ T ≤ T), hC.sup_eq_top, top_inf_eq]`.
-/
theorem exists_rel_compl (S T : Submodule k V) :
    ∃ A : Submodule k V, Disjoint S A ∧ (S ⊓ T) ⊔ A = T := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (S ⊓ T)
  refine ⟨C ⊓ T, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro x hS hx
    have : x ∈ (S ⊓ T) ⊓ C := ⟨⟨hS, hx.2⟩, hx.1⟩
    rw [hC.inf_eq_bot] at this
    simpa using this
  · rw [← sup_inf_assoc_of_le C (inf_le_right : S ⊓ T ≤ T), hC.sup_eq_top, top_inf_eq]

/- English proof (translation)
Take `⟨Q, hQ⟩` from `Submodule.exists_isCompl (S ⊔ A)`. Use `⟨A ⊔ Q, ⟨?_, ?_⟩, le_sup_left⟩` and prove the remaining obligations. Rewrite using `[Submodule.disjoint_def]`. Introduce `x hS hx`. Take `⟨a, ha, q, hq, rfl⟩` from `Submodule.mem_sup.1 hx`.

Establish `hq' : q ∈ (S ⊔ A) ⊓ Q`. Use `⟨?_, hq⟩` and prove the remaining obligations. Establish `: q = (a + q) + (-a)` using `by abel`. Rewrite using `[this]`. Conclude with `Submodule.add_mem _ (Submodule.mem_sup_left hS) (Submodule.neg_mem _ (Submodule.mem_sup_right ha))`.

Rewrite `hq'` using `[hQ.inf_eq_bot, Submodule.mem_bot]`. Substitute `hq'` using the available equality. Rewrite `hS`, the goal using `[add_zero]`. Conclude with `(Submodule.disjoint_def.1 h) a hS ha`. Rewrite using `[codisjoint_iff, ← sup_assoc, hQ.sup_eq_top]`.
-/
theorem exists_compl_ge (S A : Submodule k V) (h : Disjoint S A) :
    ∃ R : Submodule k V, IsCompl S R ∧ A ≤ R := by
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl (S ⊔ A)
  refine ⟨A ⊔ Q, ⟨?_, ?_⟩, le_sup_left⟩
  · rw [Submodule.disjoint_def]
    intro x hS hx
    obtain ⟨a, ha, q, hq, rfl⟩ := Submodule.mem_sup.1 hx
    have hq' : q ∈ (S ⊔ A) ⊓ Q := by
      refine ⟨?_, hq⟩
      have : q = (a + q) + (-a) := by abel
      rw [this]
      exact Submodule.add_mem _ (Submodule.mem_sup_left hS)
        (Submodule.neg_mem _ (Submodule.mem_sup_right ha))
    rw [hQ.inf_eq_bot, Submodule.mem_bot] at hq'
    subst hq'
    rw [add_zero] at hS ⊢
    exact (Submodule.disjoint_def.1 h) a hS ha
  · rw [codisjoint_iff, ← sup_assoc, hQ.sup_eq_top]

/- English proof (translation)
Take `⟨A₁, d₁, s₁⟩` from `exists_rel_compl S T₁`. Take `⟨A₂, d₂, s₂⟩` from `exists_rel_compl S T₂`. Take `⟨R₁, c₁, l₁⟩` from `exists_compl_ge S A₁ d₁`. Take `⟨R₂, c₂, l₂⟩` from `exists_compl_ge S A₂ d₂`. Establish `dimA : ∀ (T A : Submodule k V), Disjoint S A → (S ⊓ T) ⊔ A = T → finrank k ↥(S ⊓ T) + finrank k A = finrank k T`.

Introduce `T A d s`. Use `Submodule.finrank_sup_add_finrank_inf_eq (S ⊓ T) A` as an intermediate fact. Establish `hb : (S ⊓ T) ⊓ A = ⊥` using `le_bot_iff.1 ((inf_le_inf_right A inf_le_left).trans d.le_bot)`. Rewrite `this` using `[s, hb, finrank_bot, add_zero]`. Conclude with `this.symm`.

Establish `a₁` using `dimA T₁ A₁ d₁ s₁`. Establish `a₂` using `dimA T₂ A₂ d₂ s₂`. Establish `r₁` using `Submodule.finrank_add_eq_of_isCompl c₁`. Establish `r₂` using `Submodule.finrank_add_eq_of_isCompl c₂`. Establish `cS : ∀ T : Submodule k V, finrank k (Submodule.comap S.subtype (S ⊓ T)) = finrank k ↥(S ⊓ T)` using `fun T => LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe inf_le_left)`.

Take `⟨eS, hS⟩` from `exists_equiv_pair (X₁ := S) (X₂ := S) rfl (Submodule.comap S.subtype (S ⊓ T₁)) (Submodule.comap S.subtype (S ⊓ T₂)) (by rw [cS, cS, hI])`. Establish `f₁ : finrank k (Submodule.comap R₁.subtype A₁) = finrank k A₁` using `LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe l₁)`. Establish `f₂ : finrank k (Submodule.comap R₂.subtype A₂) = finrank k A₂` using `LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe l₂)`. Take `⟨eR, hR⟩` from `exists_equiv_pair (X₁ := R₁) (X₂ := R₂) (by omega) (Submodule.comap R₁.subtype A₁) (Submodule.comap R₂.subtype A₂) (by omega)`. Take `⟨e, he₁, he₂⟩` from `glue c₁ c₂ eS eR`.

Use `⟨e, fun s hs => ?_, fun t ht => ?_⟩` and prove the remaining obligations. Establish `e₀ : e s = eS ⟨s, hs⟩` using `he₁ ⟨s, hs⟩`. Rewrite using `[e₀]`. Conclude with `Subtype.property _`. Rewrite `ht` using `[← s₁]`.

Take `⟨p, hp, a, ha, rfl⟩` from `Submodule.mem_sup.1 ht`. Rewrite using `[map_add]`. Establish `e₁ : e p = eS ⟨p, hp.1⟩` using `he₁ ⟨p, hp.1⟩`. Establish `e₂ : e a = eR ⟨a, l₁ ha⟩` using `he₂ ⟨a, l₁ ha⟩`. Establish `m₁ : (eS ⟨p, hp.1⟩ : V) ∈ S ⊓ T₂` using `hS ⟨p, hp.1⟩ hp`.

Establish `m₂ : (eR ⟨a, l₁ ha⟩ : V) ∈ A₂` using `hR ⟨a, l₁ ha⟩ ha`. Rewrite using `[e₁, e₂, ← s₂]`. Conclude with `Submodule.add_mem_sup m₁ m₂`.
-/
theorem exists_equiv_triple [FiniteDimensional k V] (S T₁ T₂ : Submodule k V)
    (hT : finrank k T₁ = finrank k T₂) (hI : finrank k ↥(S ⊓ T₁) = finrank k ↥(S ⊓ T₂)) :
    ∃ e : V ≃ₗ[k] V, (∀ s ∈ S, e s ∈ S) ∧ ∀ t ∈ T₁, e t ∈ T₂ := by
  obtain ⟨A₁, d₁, s₁⟩ := exists_rel_compl S T₁
  obtain ⟨A₂, d₂, s₂⟩ := exists_rel_compl S T₂
  obtain ⟨R₁, c₁, l₁⟩ := exists_compl_ge S A₁ d₁
  obtain ⟨R₂, c₂, l₂⟩ := exists_compl_ge S A₂ d₂
  have dimA : ∀ (T A : Submodule k V), Disjoint S A → (S ⊓ T) ⊔ A = T →
      finrank k ↥(S ⊓ T) + finrank k A = finrank k T := by
    intro T A d s
    have := Submodule.finrank_sup_add_finrank_inf_eq (S ⊓ T) A
    have hb : (S ⊓ T) ⊓ A = ⊥ :=
      le_bot_iff.1 ((inf_le_inf_right A inf_le_left).trans d.le_bot)
    rw [s, hb, finrank_bot, add_zero] at this
    exact this.symm
  have a₁ := dimA T₁ A₁ d₁ s₁
  have a₂ := dimA T₂ A₂ d₂ s₂
  have r₁ := Submodule.finrank_add_eq_of_isCompl c₁
  have r₂ := Submodule.finrank_add_eq_of_isCompl c₂
  have cS : ∀ T : Submodule k V, finrank k (Submodule.comap S.subtype (S ⊓ T)) = finrank k ↥(S ⊓ T) :=
    fun T => LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe inf_le_left)
  obtain ⟨eS, hS⟩ := exists_equiv_pair (X₁ := S) (X₂ := S) rfl
    (Submodule.comap S.subtype (S ⊓ T₁)) (Submodule.comap S.subtype (S ⊓ T₂))
    (by rw [cS, cS, hI])
  have f₁ : finrank k (Submodule.comap R₁.subtype A₁) = finrank k A₁ :=
    LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe l₁)
  have f₂ : finrank k (Submodule.comap R₂.subtype A₂) = finrank k A₂ :=
    LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe l₂)
  obtain ⟨eR, hR⟩ := exists_equiv_pair (X₁ := R₁) (X₂ := R₂) (by omega)
    (Submodule.comap R₁.subtype A₁) (Submodule.comap R₂.subtype A₂) (by omega)
  obtain ⟨e, he₁, he₂⟩ := glue c₁ c₂ eS eR
  refine ⟨e, fun s hs => ?_, fun t ht => ?_⟩
  · have e₀ : e s = eS ⟨s, hs⟩ := he₁ ⟨s, hs⟩
    rw [e₀]
    exact Subtype.property _
  · rw [← s₁] at ht
    obtain ⟨p, hp, a, ha, rfl⟩ := Submodule.mem_sup.1 ht
    rw [map_add]
    have e₁ : e p = eS ⟨p, hp.1⟩ := he₁ ⟨p, hp.1⟩
    have e₂ : e a = eR ⟨a, l₁ ha⟩ := he₂ ⟨a, l₁ ha⟩
    have m₁ : (eS ⟨p, hp.1⟩ : V) ∈ S ⊓ T₂ := hS ⟨p, hp.1⟩ hp
    have m₂ : (eR ⟨a, l₁ ha⟩ : V) ∈ A₂ := hR ⟨a, l₁ ha⟩ ha
    rw [e₁, e₂, ← s₂]
    exact Submodule.add_mem_sup m₁ m₂

variable {n : ℕ}

def incR : (Fin n → k) →ₗ[k] (Ix n → k) where
  toFun w := Sum.elim 0 w
  map_add' x y := by ext (i | i) <;> simp
  map_smul' c x := by ext (i | i) <;> simp

def sS : Submodule k (Ix n → k) := LinearMap.ker (LinearMap.funLeft k k (Sum.inr : Fin n → Ix n))

/- English proof (translation)
Simplify using `[sS, LinearMap.mem_ker, funext_iff, LinearMap.funLeft_apply]`.
-/
theorem mem_sS {v : Ix n → k} : v ∈ sS (k := k) (n := n) ↔ ∀ j, v (Sum.inr j) = 0 := by
  simp [sS, LinearMap.mem_ker, funext_iff, LinearMap.funLeft_apply]

def phi (g : GL (Ix n) k) : (Fin n → k) →ₗ[k] (Ix n → k) := g.1.mulVecLin ∘ₗ incR

/- English proof (translation)
Introduce `x y h`. Establish `h1 : g.1 *ᵥ incR x = g.1 *ᵥ incR y` using `h`. Establish `h2 : incR x = incR y`. Use `congrArg (fun v => (g⁻¹).1 *ᵥ v) h1` as an intermediate fact. Simplify `this` using `[Matrix.mulVec_mulVec]`.

Use extensionality with `i`. Conclude with `congrFun h2 (Sum.inr i)`.
-/
theorem phi_inj (g : GL (Ix n) k) : Function.Injective (phi g) := by
  intro x y h
  have h1 : g.1 *ᵥ incR x = g.1 *ᵥ incR y := h
  have h2 : incR x = incR y := by
    have := congrArg (fun v => (g⁻¹).1 *ᵥ v) h1
    simpa [Matrix.mulVec_mulVec] using this
  ext i
  exact congrFun h2 (Sum.inr i)

/- English proof (translation)
Simplify using `[phi, incR, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, dBlk, Matrix.toBlocks₂₂]`.
-/
theorem phi_inr (g : GL (Ix n) k) (w : Fin n → k) (j : Fin n) :
    phi g w (Sum.inr j) = ((dBlk g).mulVecLin w) j := by
  simp [phi, incR, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, dBlk, Matrix.toBlocks₂₂]

/- English proof (translation)
Rewrite using `[LinearMap.finrank_range_of_inj (phi_inj g)]`. Simplify using the standard rewrite rules.
-/
theorem hodgeTateLatticePoint_finrank_tateModule (g : GL (Ix n) k) : finrank k (LinearMap.range (phi g)) = n := by
  rw [LinearMap.finrank_range_of_inj (phi_inj g)]; simp

/- English proof (translation)
Establish `h : sS (k` using `k) (n := n) ⊓ LinearMap.range (phi g) = (LinearMap.ker (dBlk g).mulVecLin).map (phi g) := by`. Use extensionality with `v`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hs, w, rfl⟩`. Use `⟨w, ?_, rfl⟩` and prove the remaining obligations.

Rewrite using `[SetLike.mem_coe, LinearMap.mem_ker]`. Use extensionality with `j`. Rewrite using `[← phi_inr]`. Conclude with `mem_sS.1 hs j`. Introduce and unpack `⟨w, hw, rfl⟩`.

Use `⟨mem_sS.2 fun j => ?_, w, rfl⟩` and prove the remaining obligations. Rewrite using `[phi_inr, (LinearMap.mem_ker.1 hw)]`. Both sides reduce to the same expression. Rewrite using `[h, ← LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ (phi_inj g) _)]`. Use `LinearMap.finrank_range_add_finrank_ker (dBlk g).mulVecLin` as an intermediate fact.

Simplify using `only [finrank_fin_fun] at this`. Establish `hr : (dBlk g).rank = finrank k (LinearMap.range (dBlk g).mulVecLin)` using `rfl`. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_inf (g : GL (Ix n) k) :
    finrank k ↥(sS (k := k) (n := n) ⊓ LinearMap.range (phi g)) + (dBlk g).rank = n := by
  have h : sS (k := k) (n := n) ⊓ LinearMap.range (phi g) =
      (LinearMap.ker (dBlk g).mulVecLin).map (phi g) := by
    ext v
    constructor
    · rintro ⟨hs, w, rfl⟩
      refine ⟨w, ?_, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      ext j
      rw [← phi_inr]
      exact mem_sS.1 hs j
    · rintro ⟨w, hw, rfl⟩
      refine ⟨mem_sS.2 fun j => ?_, w, rfl⟩
      rw [phi_inr, (LinearMap.mem_ker.1 hw)]
      rfl
  rw [h, ← LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ (phi_inj g) _)]
  have := LinearMap.finrank_range_add_finrank_ker (dBlk g).mulVecLin
  simp only [finrank_fin_fun] at this
  have hr : (dBlk g).rank = finrank k (LinearMap.range (dBlk g).mulVecLin) := rfl
  omega

/- English proof (translation)
Establish `hE : E.1 = fromBlocks E.1.toBlocks₁₁ E.1.toBlocks₁₂ 0 E.1.toBlocks₂₂`. Rewrite using `[← h, fromBlocks_toBlocks]`. Establish `hdet : E.1.toBlocks₁₁.det * E.1.toBlocks₂₂.det ≠ 0`. Rewrite using `[← det_fromBlocks_zero₂₁ _ E.1.toBlocks₁₂, ← hE]`. Conclude with `(Matrix.isUnits_det_units E).ne_zero`.

Use `⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ (left_ne_zero_of_mul hdet), Matrix.GeneralLinearGroup.mkOfDetNeZero _ (right_ne_zero_of_mul hdet), E.1.toBlocks₁₂, ?_⟩` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises. Conclude with `hE`.
-/
theorem exists_pM (E : GL (Ix n) k) (h : E.1.toBlocks₂₁ = 0) :
    ∃ (a d : GL (Fin n) k) (b : Matrix (Fin n) (Fin n) k), E = pM a d b := by
  have hE : E.1 = fromBlocks E.1.toBlocks₁₁ E.1.toBlocks₁₂ 0 E.1.toBlocks₂₂ := by
    rw [← h, fromBlocks_toBlocks]
  have hdet : E.1.toBlocks₁₁.det * E.1.toBlocks₂₂.det ≠ 0 := by
    rw [← det_fromBlocks_zero₂₁ _ E.1.toBlocks₁₂, ← hE]
    exact (Matrix.isUnits_det_units E).ne_zero
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ (left_ne_zero_of_mul hdet),
    Matrix.GeneralLinearGroup.mkOfDetNeZero _ (right_ne_zero_of_mul hdet), E.1.toBlocks₁₂, ?_⟩
  apply Units.ext
  exact hE

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Both sides reduce to the same expression.
-/
theorem pM_inv (a d : GL (Fin n) k) (b : Matrix (Fin n) (Fin n) k) :
    (pM a d b)⁻¹ = pM a⁻¹ d⁻¹ (-((a⁻¹).1 * b * (d⁻¹).1)) := by
  apply Units.ext
  rfl

/- English proof (translation)
Introduce `k _ n g₁ g₂ h`. Establish `hr : (dBlk g₁).rank = (dBlk g₂).rank`. Establish `h1` using `(dBlk g₁).rank_le_height`. Establish `h2` using `(dBlk g₂).rank_le_height`. Unfold `iD at h`.

Use linear arithmetic over natural numbers and integers. Take `⟨e, heS, heT⟩` from `exists_equiv_triple (sS (k := k) (n := n)) (LinearMap.range (phi g₂)) (LinearMap.range (phi g₁)) (by rw [hodgeTateLatticePoint_finrank_tateModule, hodgeTateLatticePoint_finrank_tateModule]) (by have := finrank_inf g₁; have := finrank_inf g₂; omega)`. Set `E : GL (Ix n) k` to `⟨LinearMap.toMatrix' e.toLinearMap, LinearMap.toMatrix' e.symm.toLinearMap, by rw [← LinearMap.toMatrix'_comp]; simp, by rw [← LinearMap.toMatrix'_comp]; simp⟩`. Establish `hE : ∀ v, E.1 *ᵥ v = e v` using `fun v => LinearMap.toMatrix'_mulVec _ _`. Establish `h21 : E.1.toBlocks₂₁ = 0`.

Use extensionality with `i j`. Establish `hs : (Pi.single (Sum.inl j) 1 : Ix n → k) ∈ sS (k` using `k) (n := n) := mem_sS.2 fun l => by simp`. Use `mem_sS.1 (heS _ hs) i` as an intermediate fact. Rewrite `this` using `[← hE, Matrix.mulVec_single_one]`. Conclude with `this`.

Take `⟨a, d, b, hp⟩` from `exists_pM E h21`. Use `⟨a⁻¹, d⁻¹, -((a⁻¹).1 * b * (d⁻¹).1), g₁⁻¹ * E * g₂, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Establish `hw : ∀ w : Fin n → k, ∃ w', g₁.1 *ᵥ incR w' = E.1 *ᵥ (g₂.1 *ᵥ incR w)`. Introduce `w`.

Take `⟨w', hw'⟩` from `heT (phi g₂ w) ⟨w, rfl⟩`. Conclude with `⟨w', by rw [hE]; exact hw'⟩`. Take `⟨w', hw'⟩` from `hw (Pi.single j 1)`. Establish `hs : (incR (Pi.single j 1) : Ix n → k) = Pi.single (Sum.inr j) 1`. Apply the tactic sequence `ext (l | l) <;> simp [incR, Pi.single_apply]`.

Establish `hx : (g₁⁻¹ * E * g₂).1 *ᵥ (Pi.single (Sum.inr j) 1) = incR w'`. Rewrite using `[← hs]`. Establish `: (g₁⁻¹ * E * g₂).1 = (g₁⁻¹).1 * E.1 * g₂.1` using `rfl`. Rewrite using `[this, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hw', Matrix.mulVec_mulVec]`. Simplify using the standard rewrite rules.

Use `congrFun hx (Sum.inl i)` as an intermediate fact. Rewrite `this` using `[Matrix.mulVec_single_one]`. Simplify `this` using `[incR, Matrix.toBlocks₁₂]`. Rewrite using `[← pM_inv, ← hp] group`.
-/
theorem main : ∀ (k : Type) [Field k] (n : ℕ) (g₁ g₂ : GL (Ix n) k), iD g₁ = iD g₂ →
    ∃ (a d : GL (Fin n) k) (b : Matrix (Fin n) (Fin n) k) (x : GL (Ix n) k),
      x.1.toBlocks₁₂ = 0 ∧ g₂ = pM a d b * g₁ * x := by
  intro k _ n g₁ g₂ h
  have hr : (dBlk g₁).rank = (dBlk g₂).rank := by
    have h1 := (dBlk g₁).rank_le_height
    have h2 := (dBlk g₂).rank_le_height
    unfold iD at h
    omega
  obtain ⟨e, heS, heT⟩ := exists_equiv_triple (sS (k := k) (n := n))
    (LinearMap.range (phi g₂)) (LinearMap.range (phi g₁))
    (by rw [hodgeTateLatticePoint_finrank_tateModule, hodgeTateLatticePoint_finrank_tateModule])
    (by have := finrank_inf g₁; have := finrank_inf g₂; omega)
  let E : GL (Ix n) k :=
    ⟨LinearMap.toMatrix' e.toLinearMap, LinearMap.toMatrix' e.symm.toLinearMap,
      by rw [← LinearMap.toMatrix'_comp]; simp,
      by rw [← LinearMap.toMatrix'_comp]; simp⟩
  have hE : ∀ v, E.1 *ᵥ v = e v := fun v => LinearMap.toMatrix'_mulVec _ _
  have h21 : E.1.toBlocks₂₁ = 0 := by
    ext i j
    have hs : (Pi.single (Sum.inl j) 1 : Ix n → k) ∈ sS (k := k) (n := n) :=
      mem_sS.2 fun l => by simp
    have := mem_sS.1 (heS _ hs) i
    rw [← hE, Matrix.mulVec_single_one] at this
    exact this
  obtain ⟨a, d, b, hp⟩ := exists_pM E h21
  refine ⟨a⁻¹, d⁻¹, -((a⁻¹).1 * b * (d⁻¹).1), g₁⁻¹ * E * g₂, ?_, ?_⟩
  · ext i j
    have hw : ∀ w : Fin n → k, ∃ w', g₁.1 *ᵥ incR w' = E.1 *ᵥ (g₂.1 *ᵥ incR w) := by
      intro w
      obtain ⟨w', hw'⟩ := heT (phi g₂ w) ⟨w, rfl⟩
      exact ⟨w', by rw [hE]; exact hw'⟩
    obtain ⟨w', hw'⟩ := hw (Pi.single j 1)
    have hs : (incR (Pi.single j 1) : Ix n → k) = Pi.single (Sum.inr j) 1 := by
      ext (l | l) <;> simp [incR, Pi.single_apply]
    have hx : (g₁⁻¹ * E * g₂).1 *ᵥ (Pi.single (Sum.inr j) 1) = incR w' := by
      rw [← hs]
      have : (g₁⁻¹ * E * g₂).1 = (g₁⁻¹).1 * E.1 * g₂.1 := rfl
      rw [this, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hw', Matrix.mulVec_mulVec]
      simp
    have := congrFun hx (Sum.inl i)
    rw [Matrix.mulVec_single_one] at this
    simpa [incR, Matrix.toBlocks₁₂] using this
  · rw [← pM_inv, ← hp]
    group

end GlobalTheory.CompanionTheory.Jp.Dbl
