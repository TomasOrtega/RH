import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

namespace GlobalTheory.LocGL

/- English proof (translation)
Establish `hst : ∀ (U : Submodule ℂ V) (g : G) ⦃v : V⦄, v ∈ U → π g v ∈ U` using `fun U g v hv => by`. Rewrite using `[Subsingleton.elim g 1, map_one]`. Conclude with `hv`. Use `hi` as an intermediate fact. Choose the witnesses or unpack the hypotheses as in `⟨v, hv⟩ : ∃ v : V, v ≠ 0 := by`.

Assume the negation of the conclusion as `h`. Simplify using `only [ne_eq, not_exists, not_not] at h`. Apply `(bot_ne_top : (⊥ : Subrepresentation π) ≠ ⊤)` to reduce the goal to its premises. Apply `Subrepresentation.ext` to reduce the goal to its premises. Use extensionality with `w`.

Rewrite using `[h w]`. Conclude with `⟨fun _ => Submodule.zero_mem _, fun _ => Submodule.zero_mem _⟩`. Establish `htop : Submodule.span ℂ {v} = ⊤`. Break down `eq_bot_or_eq_top (⟨Submodule.span ℂ {v}, hst _⟩ : Subrepresentation π) with h | h` into its components or cases. Conclude with `absurd (Submodule.span_singleton_eq_bot.mp (congrArg Subrepresentation.toSubmodule h)) hv`.

Conclude with `congrArg Subrepresentation.toSubmodule h`. Conclude with `⟨((LinearEquiv.toSpanNonzeroSingleton ℂ V v hv).trans (LinearEquiv.ofTop _ htop)).symm⟩`.
-/
theorem exists_linearEquiv_of_subsingleton {G V : Type} [Group G] [Subsingleton G] [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ G V} (hi : π.IsIrreducible) : Nonempty (V ≃ₗ[ℂ] ℂ) := by
  have hst : ∀ (U : Submodule ℂ V) (g : G) ⦃v : V⦄, v ∈ U → π g v ∈ U := fun U g v hv => by
    rw [Subsingleton.elim g 1, map_one]
    exact hv
  have := hi
  obtain ⟨v, hv⟩ : ∃ v : V, v ≠ 0 := by
    by_contra h
    simp only [ne_eq, not_exists, not_not] at h
    apply (bot_ne_top : (⊥ : Subrepresentation π) ≠ ⊤)
    apply Subrepresentation.ext
    ext w
    rw [h w]
    exact ⟨fun _ => Submodule.zero_mem _, fun _ => Submodule.zero_mem _⟩
  have htop : Submodule.span ℂ {v} = ⊤ := by
    rcases eq_bot_or_eq_top (⟨Submodule.span ℂ {v}, hst _⟩ : Subrepresentation π) with h | h
    · exact absurd (Submodule.span_singleton_eq_bot.mp (congrArg Subrepresentation.toSubmodule h)) hv
    · exact congrArg Subrepresentation.toSubmodule h
  exact ⟨((LinearEquiv.toSpanNonzeroSingleton ℂ V v hv).trans (LinearEquiv.ofTop _ htop)).symm⟩

/- English proof (translation)
Set `b : ∀ a, X a` to `Pi.single 1 (f.symm 1)`. Establish `hb : b 1 = f.symm 1` using `Pi.single_eq_same _ _`. Set `μ : MultilinearMap ℂ X (X 0)` to `{ toFun := fun x => f (x 1) • x 0 map_update_add' := by`. Introduce `_ x i p q`. Use `fin_cases i`.

Simplify using `only [Fin.zero_eta, Function.update_self, ne_eq, one_ne_zero, not_false_eq_true, Function.update_of_ne, smul_add]`. Simplify using `only [Fin.mk_one, Function.update_self, ne_eq, zero_ne_one, not_false_eq_true, Function.update_of_ne, map_add, add_smul]`. Use the proof step `map_update_smul' := by`. Introduce `_ x i c p`. Use `fin_cases i`.

Simplify using `only [Fin.zero_eta, Function.update_self, ne_eq, one_ne_zero, not_false_eq_true, Function.update_of_ne, smul_comm (f (x 1)) c]`. Simplify using `only [Fin.mk_one, Function.update_self, ne_eq, zero_ne_one, not_false_eq_true, Function.update_of_ne, map_smul, smul_eq_mul, mul_smul] }`. Establish `hμ : ∀ x, μ x = f (x 1) • x 0` using `fun _ => rfl`. Set `φ : X 0 →ₗ[ℂ] PiTensorProduct ℂ X` to `(PiTensorProduct.tprod ℂ).toLinearMap b 0`. Establish `hφ : ∀ v, φ v = PiTensorProduct.tprod ℂ (Function.update b 0 v)` using `fun _ => rfl`.

Use `⟨b, LinearEquiv.ofLinearMap φ (PiTensorProduct.lift μ) ?_ ?_, hφ⟩` and prove the remaining obligations. Apply `PiTensorProduct.ext` to reduce the goal to its premises. Apply `MultilinearMap.ext` to reduce the goal to its premises. Introduce `x`. Simplify using `only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply, PiTensorProduct.lift.tprod, hμ, hφ, LinearMap.id_coe, id_eq]`.

Establish `hx : x = Function.update (Function.update b 0 (x 0)) 1 (f (x 1) • Function.update b 0 (x 0) 1)`. Use function extensionality and compare the values at `a`. Use `fin_cases a`. Simplify using the standard rewrite rules. Simplify using `only [Fin.mk_one, Function.update_self]`.

Rewrite using `[Function.update_of_ne (by decide), hb, ← map_smul, smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply]`. Use `conv_rhs => rw [hx]`. Rewrite using `[MultilinearMap.map_update_smul (PiTensorProduct.tprod ℂ) b 0, MultilinearMap.map_update_smul (PiTensorProduct.tprod ℂ) (Function.update b 0 (x 0)) 1, Function.update_eq_self]`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `v`.

Simplify using `only [LinearMap.coe_comp, Function.comp_apply, hφ, PiTensorProduct.lift.tprod, hμ, LinearMap.id_coe, id_eq, Function.update_self]`. Rewrite using `[Function.update_of_ne (by decide), hb, LinearEquiv.apply_symm_apply, one_smul]`.
-/
theorem exists_equiv_piTensor_two {X : Fin 2 → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (f : X 1 ≃ₗ[ℂ] ℂ) : ∃ (b : ∀ a, X a) (L : X 0 ≃ₗ[ℂ] PiTensorProduct ℂ X),
      ∀ v, L v = PiTensorProduct.tprod ℂ (Function.update b 0 v) := by
  classical
  let b : ∀ a, X a := Pi.single 1 (f.symm 1)
  have hb : b 1 = f.symm 1 := Pi.single_eq_same _ _
  let μ : MultilinearMap ℂ X (X 0) :=
    { toFun := fun x => f (x 1) • x 0
      map_update_add' := by
        intro _ x i p q
        fin_cases i
        · simp only [Fin.zero_eta, Function.update_self, ne_eq, one_ne_zero, not_false_eq_true,
            Function.update_of_ne, smul_add]
        · simp only [Fin.mk_one, Function.update_self, ne_eq, zero_ne_one, not_false_eq_true,
            Function.update_of_ne, map_add, add_smul]
      map_update_smul' := by
        intro _ x i c p
        fin_cases i
        · simp only [Fin.zero_eta, Function.update_self, ne_eq, one_ne_zero, not_false_eq_true,
            Function.update_of_ne, smul_comm (f (x 1)) c]
        · simp only [Fin.mk_one, Function.update_self, ne_eq, zero_ne_one, not_false_eq_true,
            Function.update_of_ne, map_smul, smul_eq_mul, mul_smul] }
  have hμ : ∀ x, μ x = f (x 1) • x 0 := fun _ => rfl
  let φ : X 0 →ₗ[ℂ] PiTensorProduct ℂ X := (PiTensorProduct.tprod ℂ).toLinearMap b 0
  have hφ : ∀ v, φ v = PiTensorProduct.tprod ℂ (Function.update b 0 v) := fun _ => rfl
  refine ⟨b, LinearEquiv.ofLinearMap φ (PiTensorProduct.lift μ) ?_ ?_, hφ⟩
  · apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply,
      PiTensorProduct.lift.tprod, hμ, hφ, LinearMap.id_coe, id_eq]
    have hx : x = Function.update (Function.update b 0 (x 0)) 1
        (f (x 1) • Function.update b 0 (x 0) 1) := by
      funext a
      fin_cases a
      · simp
      · simp only [Fin.mk_one, Function.update_self]
        rw [Function.update_of_ne (by decide), hb, ← map_smul, smul_eq_mul, mul_one,
          LinearEquiv.symm_apply_apply]
    conv_rhs => rw [hx]
    rw [MultilinearMap.map_update_smul (PiTensorProduct.tprod ℂ) b 0,
      MultilinearMap.map_update_smul (PiTensorProduct.tprod ℂ) (Function.update b 0 (x 0)) 1,
      Function.update_eq_self]
  · apply LinearMap.ext
    intro v
    simp only [LinearMap.coe_comp, Function.comp_apply, hφ, PiTensorProduct.lift.tprod, hμ,
      LinearMap.id_coe, id_eq, Function.update_self]
    rw [Function.update_of_ne (by decide), hb, LinearEquiv.apply_symm_apply, one_smul]

/- English proof (translation)
Establish `hb : ∀ x : m 0, blk e x = 0`. Introduce `x`. Unfold `blk`. Generalize the expression as in `e.symm x = s`. Take `⟨a, y⟩` from `s`.

Apply the tactic sequence `obtain rfl | rfl : a = 0 ∨ a = 1 := by fin_cases a <;> simp`. Both sides reduce to the same expression. Conclude with `isEmptyElim y`. Rewrite using `[mem_parab]`. Introduce `i j hij`.

Rewrite `hij` using `[hb i, hb j]`. Conclude with `absurd hij (lt_irrefl _)`.
-/
private theorem mem_parab_of_isEmpty_second_block {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : Fin 2 → Type} [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
    [IsEmpty (m 1)] (e : (Σ a, m a) ≃ m 0) (g : GL (m 0) k) : g ∈ parab k e := by
  have hb : ∀ x : m 0, blk e x = 0 := by
    intro x
    unfold blk
    generalize e.symm x = s
    obtain ⟨a, y⟩ := s
    obtain rfl | rfl : a = 0 ∨ a = 1 := by fin_cases a <;> simp
    · rfl
    · exact isEmptyElim y
  rw [mem_parab]
  intro i j hij
  rw [hb i, hb j] at hij
  exact absurd hij (lt_irrefl _)

/- English proof (translation)
The claim follows from `Units.ext (Matrix.ext fun i j => by rw [leviProj_apply, he, he])`.
-/
private theorem leviProj_zero_eq_coe {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : Fin 2 → Type} [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
    (e : (Σ a, m a) ≃ m 0) (he : ∀ i, e ⟨0, i⟩ = i) (p : parab k e) :
    leviProj k e p 0 = (p : GL (m 0) k) :=
  Units.ext (Matrix.ext fun i j => by rw [leviProj_apply, he, he])

/- English proof (translation)
Establish `: Subsingleton (GL (m 1) k)` using `⟨fun a b => Units.ext (Matrix.ext fun i => isEmptyElim i)⟩`. Establish `h0 : modExp m 0 = 0`. Simplify using `[modExp, Finset.sum_filter, Fin.sum_univ_two, Fintype.card_eq_zero]`. Establish `h1 : g 1 = 1` using `Subsingleton.elim _ _`. Rewrite using `[deltaHalf_apply, Fin.prod_univ_two, h0, h1, map_one, map_one, mul_one]`.

Simplify using `[absPow_zero]`.
-/
private theorem deltaHalf_eq_one_of_isEmpty_second_block {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : Fin 2 → Type} [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
    [IsEmpty (m 1)] (g : Levi k m) : deltaHalf k m g = 1 := by
  have : Subsingleton (GL (m 1) k) := ⟨fun a b => Units.ext (Matrix.ext fun i => isEmptyElim i)⟩
  have h0 : modExp m 0 = 0 := by
    simp [modExp, Finset.sum_filter, Fin.sum_univ_two, Fintype.card_eq_zero]
  have h1 : g 1 = 1 := Subsingleton.elim _ _
  rw [deltaHalf_apply, Fin.prod_univ_two, h0, h1, map_one, map_one, mul_one]
  simp [absPow_zero]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Establish `: Subsingleton (GL (m 1) k)` using `⟨fun a b => Units.ext (Matrix.ext fun i => isEmptyElim i)⟩`. Take `⟨f₁⟩` from `exists_linearEquiv_of_subsingleton hi`. Take `⟨b, L, hL⟩` from `exists_equiv_piTensor_two f₁`. Establish `hσ : ∀ (p : parab k e) (u : X 0), (twist (piTensor π) (deltaHalf k m)) (leviProj k e p) (L u) = L (π 0 (p : GL (m 0) k) u)`. Introduce `p u`.

Rewrite using `[twist_apply, deltaHalf_eq_one_of_isEmpty_second_block, Units.val_one, one_smul, hL, hL, piTensor_tprod]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Apply the tactic sequence `obtain rfl | rfl : a = 0 ∨ a = 1 := by fin_cases a <;> simp`. Rewrite using `[Function.update_self, Function.update_self, leviProj_zero_eq_coe e he]`.

Rewrite using `[Function.update_of_ne (by decide), Function.update_of_ne (by decide), Subsingleton.elim (leviProj k e p 1) 1, map_one, Module.End.one_apply]`. Establish `hval : ∀ (f : IndSp e (piTensor π)) (g : GL (m 0) k), f.1.1 g = L (π 0 g (L.symm (f.1.1 1)))`. Introduce `f g`. Establish `h` using `(f.1.2 : ∀ (h : parab k e) (x : GL (m 0) k), f.1.1 (h * x) = _) ⟨g, mem_parab_of_isEmpty_second_block e g⟩ 1`. Rewrite `h` using `[mul_one]`.

Establish `h'` using `hσ ⟨g, mem_parab_of_isEmpty_second_block e g⟩ (L.symm (f.1.1 1))`. Rewrite `h'` using `[LinearEquiv.apply_symm_apply]`. Rewrite using `[h]`. Conclude with `h'`. Set `G : IndSp e (piTensor π) →ₗ[ℂ] X 0` to `L.symm.toLinearMap ∘ₗ LinearMap.proj 1 ∘ₗ (indSpace _ _).subtype ∘ₗ (smoothPart _).subtype`.

Establish `hG : ∀ f, G f = L.symm (f.1.1 1)` using `fun _ => rfl`. Establish `hinj : Function.Injective G`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `f hf`. Rewrite `hf` using `[hG]`.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `g`. Rewrite using `[hval, hf, map_zero, map_zero]`. Both sides reduce to the same expression.

Establish `hsurj : Function.Surjective G`. Introduce `v`. Set `F : GL (m 0) k → PiTensorProduct ℂ X` to `fun g => L (π 0 g v)`. Establish `hF : F ∈ indSpace (parab k e) ((twist (piTensor π) (deltaHalf k m)).comp (leviProj k e))`. Introduce `p g`.

Use `show L (π 0 (p * g) v) = _`. Rewrite using `[map_mul, Module.End.mul_apply, MonoidHom.comp_apply, hσ]`. Establish `hS : (⟨F, hF⟩ : indSpace _ _) ∈ smoothPart (ind (parab k e) ((twist (piTensor π) (deltaHalf k m)).comp (leviProj k e)))`. Establish `hset : {g' : GL (m 0) k | ind (parab k e) ((twist (piTensor π) (deltaHalf k m)).comp (leviProj k e)) g' ⟨F, hF⟩ = ⟨F, hF⟩} = {g' | π 0 g' v = v}`. Use extensionality with `g'`.

Simplify using `only [Set.mem_ofPred_eq]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h1` using `congrArg (fun φ : indSpace _ _ => φ.1 1) h`. Establish `h2 : L (π 0 (1 * g') v) = L (π 0 1 v)` using `h1`.

Rewrite `h2` using `[one_mul, map_one, Module.End.one_apply]`. Conclude with `L.injective h2`. Introduce `h`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `x`.

Use `show L (π 0 (x * g') v) = L (π 0 x v)`. Rewrite using `[map_mul, Module.End.mul_apply, h]`. Establish `hopen : IsOpen {g' : GL (m 0) k | ind (parab k e) ((twist (piTensor π) (deltaHalf k m)).comp (leviProj k e)) g' ⟨F, hF⟩ = ⟨F, hF⟩}`. Rewrite using `[hset]`. Conclude with `hπ v`.

Conclude with `hopen`. Use `⟨⟨⟨F, hF⟩, hS⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hG]`. Use `show L.symm (L (π 0 1 v)) = v`. Rewrite using `[LinearEquiv.symm_apply_apply, map_one, Module.End.one_apply]`.

Use `⟨(Representation.Equiv.mk (LinearEquiv.ofBijective G ⟨hinj, hsurj⟩) fun g => ?_).symm⟩` and prove the remaining obligations. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `f`. Use `show G (multiProd e π g f) = π 0 g (G f)`. Rewrite using `[hG, hG]`.

Rewrite using `[show ((multiProd e π g f).1.1 1) = f.1.1 g from by`. Unfold `multiProd`. Rewrite using `[parInd_apply, one_mul]]`. Rewrite using `[hval, LinearEquiv.symm_apply_apply]`.
-/
theorem nonempty_equiv_multiProd_empty {m : Fin 2 → Type} [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
    [IsEmpty (m 1)] {X : Fin 2 → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    {π : ∀ a, Representation ℂ (GL (m a) k) (X a)} (hπ : IsSmooth (π 0)) (hi : (π 1).IsIrreducible)
    (e : (Σ a, m a) ≃ m 0) (he : ∀ i, e ⟨0, i⟩ = i) : Nonempty ((π 0).Equiv (multiProd e π)) := by
  have : Subsingleton (GL (m 1) k) := ⟨fun a b => Units.ext (Matrix.ext fun i => isEmptyElim i)⟩
  obtain ⟨f₁⟩ := exists_linearEquiv_of_subsingleton hi
  obtain ⟨b, L, hL⟩ := exists_equiv_piTensor_two f₁
  have hσ : ∀ (p : parab k e) (u : X 0),
      (twist (piTensor π) (deltaHalf k m)) (leviProj k e p) (L u) = L (π 0 (p : GL (m 0) k) u) := by
    intro p u
    rw [twist_apply, deltaHalf_eq_one_of_isEmpty_second_block, Units.val_one, one_smul, hL, hL, piTensor_tprod]
    congr 1
    funext a
    obtain rfl | rfl : a = 0 ∨ a = 1 := by fin_cases a <;> simp
    · rw [Function.update_self, Function.update_self, leviProj_zero_eq_coe e he]
    · rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Subsingleton.elim (leviProj k e p 1) 1, map_one, Module.End.one_apply]
  have hval : ∀ (f : IndSp e (piTensor π)) (g : GL (m 0) k),
      f.1.1 g = L (π 0 g (L.symm (f.1.1 1))) := by
    intro f g
    have h := (f.1.2 : ∀ (h : parab k e) (x : GL (m 0) k), f.1.1 (h * x) = _) ⟨g, mem_parab_of_isEmpty_second_block e g⟩ 1
    rw [mul_one] at h
    have h' := hσ ⟨g, mem_parab_of_isEmpty_second_block e g⟩ (L.symm (f.1.1 1))
    rw [LinearEquiv.apply_symm_apply] at h'
    rw [h]
    exact h'
  let G : IndSp e (piTensor π) →ₗ[ℂ] X 0 :=
    L.symm.toLinearMap ∘ₗ LinearMap.proj 1 ∘ₗ (indSpace _ _).subtype ∘ₗ (smoothPart _).subtype
  have hG : ∀ f, G f = L.symm (f.1.1 1) := fun _ => rfl
  have hinj : Function.Injective G := by
    rw [injective_iff_map_eq_zero]
    intro f hf
    rw [hG] at hf
    apply Subtype.ext
    apply Subtype.ext
    funext g
    rw [hval, hf, map_zero, map_zero]
    rfl
  have hsurj : Function.Surjective G := by
    intro v
    let F : GL (m 0) k → PiTensorProduct ℂ X := fun g => L (π 0 g v)
    have hF : F ∈ indSpace (parab k e) ((twist (piTensor π) (deltaHalf k m)).comp (leviProj k e)) := by
      intro p g
      show L (π 0 (p * g) v) = _
      rw [map_mul, Module.End.mul_apply, MonoidHom.comp_apply, hσ]
    have hS : (⟨F, hF⟩ : indSpace _ _) ∈ smoothPart (ind (parab k e)
        ((twist (piTensor π) (deltaHalf k m)).comp (leviProj k e))) := by
      have hset : {g' : GL (m 0) k | ind (parab k e) ((twist (piTensor π) (deltaHalf k m)).comp
          (leviProj k e)) g' ⟨F, hF⟩ = ⟨F, hF⟩} = {g' | π 0 g' v = v} := by
        ext g'
        simp only [Set.mem_ofPred_eq]
        constructor
        · intro h
          have h1 := congrArg (fun φ : indSpace _ _ => φ.1 1) h
          have h2 : L (π 0 (1 * g') v) = L (π 0 1 v) := h1
          rw [one_mul, map_one, Module.End.one_apply] at h2
          exact L.injective h2
        · intro h
          apply Subtype.ext
          funext x
          show L (π 0 (x * g') v) = L (π 0 x v)
          rw [map_mul, Module.End.mul_apply, h]
      have hopen : IsOpen {g' : GL (m 0) k | ind (parab k e) ((twist (piTensor π) (deltaHalf k m)).comp
          (leviProj k e)) g' ⟨F, hF⟩ = ⟨F, hF⟩} := by
        rw [hset]
        exact hπ v
      exact hopen
    refine ⟨⟨⟨F, hF⟩, hS⟩, ?_⟩
    rw [hG]
    show L.symm (L (π 0 1 v)) = v
    rw [LinearEquiv.symm_apply_apply, map_one, Module.End.one_apply]
  refine ⟨(Representation.Equiv.mk (LinearEquiv.ofBijective G ⟨hinj, hsurj⟩) fun g => ?_).symm⟩
  apply LinearMap.ext
  intro f
  show G (multiProd e π g f) = π 0 g (G f)
  rw [hG, hG]
  rw [show ((multiProd e π g f).1.1 1) = f.1.1 g from by
    unfold multiProd
    rw [parInd_apply, one_mul]]
  rw [hval, LinearEquiv.symm_apply_apply]

/- English proof (translation)
Establish `: IsEmpty (Fin (y 1).1)` using `by rw [hz]; infer_instance`. Use `nonempty_equiv_multiProd_empty (m := fun a => Fin (y a).1) (X := fun a => (y a).2.rep.V) (π := fun a => (y a).rep) (y 0).2.rep.smooth (y 1).2.rep.irr _ fun i => ?_` and prove the remaining obligations. Apply `Fin.ext` to reduce the goal to its premises. Rewrite using `[stdBlocks_val]`. Simplify using the standard rewrite rules.
-/
theorem nonempty_equiv_prodIrr_two_zero (y : Fin 2 → IrrGL k) (hz : (y 1).1 = 0) (hd : ∑ a, (y a).1 = (y 0).1) :
    Nonempty ((y 0).rep.Equiv (prodIrr y hd)) := by
  have : IsEmpty (Fin (y 1).1) := by rw [hz]; infer_instance
  refine nonempty_equiv_multiProd_empty (m := fun a => Fin (y a).1) (X := fun a => (y a).2.rep.V)
    (π := fun a => (y a).rep) (y 0).2.rep.smooth (y 1).2.rep.irr _ fun i => ?_
  apply Fin.ext
  rw [stdBlocks_val]
  simp

/- English proof (translation)
The claim follows from `nonempty_equiv_prodIrr_two_zero ![x, z] hz hd`.
-/
theorem nonempty_equiv_prodIrr_pair_zero (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (x z : IrrGL k) (hz : z.1 = 0) (hd : ∑ a, (![x, z] a).1 = x.1) :
    Nonempty (x.rep.Equiv (prodIrr ![x, z] hd)) := nonempty_equiv_prodIrr_two_zero ![x, z] hz hd

end GlobalTheory.LocGL
