import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchurAdmissibleAlt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionTensorProductHasFiniteLength

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc

namespace GlobalTheory.CompanionTheory.FrobJm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Establish `hKex : ∀ N : ℕ, ∃ K : Subgroup (GL (Fin N) k), IsOpen (K : Set (GL (Fin N) k)) ∧ IsCompact (K : Set (GL (Fin N) k))`. Introduce `N`. Establish `hT2 : T2Space k` using `inferInstance`. Set `O : Subring k` to `(ValuativeRel.valuation k).integer`. Establish `hOo : IsOpen (O : Set k)` using `(ValuativeRel.valuation k).isOpen_integer`.

Establish `hOc : IsCompact (O : Set k)` using `IsNonarchimedeanLocalField.isCompact_closedBall (K := k) 1`. Set `K : Subgroup (GL (Fin N) k)` to `{ carrier := {g | (∀ i j, (g : Matrix (Fin N) (Fin N) k) i j ∈ O) ∧ ∀ i j, ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j ∈ O} mul_mem' := by`. Introduce and unpack `a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩`. Use `⟨fun i j => ?_, fun i j => ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_mul, Matrix.mul_apply]`.

Conclude with `sum_mem fun l _ => mul_mem (ha1 i l) (hb1 l j)`. Rewrite using `[mul_inv_rev, Units.val_mul, Matrix.mul_apply]`. Conclude with `sum_mem fun l _ => mul_mem (hb2 i l) (ha2 l j)`. Use the proof step `one_mem' := by`. Use `⟨fun i j => ?_, fun i j => ?_⟩` and prove the remaining obligations.

Rewrite using `[Units.val_one, Matrix.one_apply] split_ifs exacts [one_mem _, zero_mem _]`. Rewrite using `[inv_one, Units.val_one, Matrix.one_apply] split_ifs exacts [one_mem _, zero_mem _]`. Use the proof step `inv_mem' := by`. Introduce and unpack `a ⟨ha1, ha2⟩`. Conclude with `⟨ha2, by rw [inv_inv]; exact ha1⟩ }`.

Establish `hKset : (K : Set (GL (Fin N) k)) = (⋂ i, ⋂ j, (fun g : GL (Fin N) k => (g : Matrix (Fin N) (Fin N) k) i j) ⁻¹' (O : Set k)) ∩ ⋂ i, ⋂ j, (fun g : GL (Fin N) k => ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j) ⁻¹' (O : Set k)`. Use extensionality with `g`. Simplify using `only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]`. Conclude with `Iff.rfl`. Use `⟨K, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hKset]`. Use `IsOpen.inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hOo.preimage ?_) (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hOo.preimage ?_)` and prove the remaining obligations. Conclude with `Units.continuous_val.matrix_elem i j`. Conclude with `Units.continuous_coe_inv.matrix_elem i j`. Rewrite using `[Units.isEmbedding_embedProduct.isInducing.isCompact_iff]`.

Set `S : Set (Matrix (Fin N) (Fin N) k)` to `{A | ∀ i j, A i j ∈ O}`. Establish `hS : IsCompact S`. Establish `h` using `isCompact_univ_pi (fun _ : Fin N => isCompact_univ_pi (fun _ : Fin N => hOc))`. Establish `hSe : S = Set.univ.pi (fun _ : Fin N => Set.univ.pi fun _ : Fin N => (O : Set k))`. Use extensionality with `A`.

Use `show (∀ i j, A i j ∈ O) ↔ ∀ i ∈ (Set.univ : Set (Fin N)), ∀ j ∈ (Set.univ : Set (Fin N)), A i j ∈ (O : Set k)`. Prove the components needed by the constructor for the conclusion. Introduce `hA i _ j _`. Conclude with `hA i j`. Introduce `hA i j`.

Conclude with `hA i (Set.mem_univ i) j (Set.mem_univ j)`. Rewrite using `[hSe]`. Conclude with `h`. Establish `hsub : Units.embedProduct (Matrix (Fin N) (Fin N) k) '' (K : Set (GL (Fin N) k)) = (S ×ˢ (MulOpposite.op '' S)) ∩ {p | p.1 * MulOpposite.unop p.2 = 1 ∧ MulOpposite.unop p.2 * p.1 = 1}`. Use extensionality with `p`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, ⟨hg1, hg2⟩, rfl⟩`. Conclude with `⟨⟨hg1, (g⁻¹ : GL (Fin N) k).val, hg2, rfl⟩, g.mul_inv, g.inv_mul⟩`. Introduce and unpack `⟨⟨hA, B, hB, hBp⟩, h1, h2⟩`. Use `⟨⟨p.1, MulOpposite.unop p.2, h1, h2⟩, ⟨hA, ?_⟩, rfl⟩` and prove the remaining obligations.

Use `show ∀ i j, (MulOpposite.unop p.2) i j ∈ O`. Rewrite using `[← hBp]`. Conclude with `hB`. Rewrite using `[hsub]`. Use `(hS.prod (hS.image MulOpposite.continuous_op)).inter_right ?_` and prove the remaining obligations.

Conclude with `(isClosed_eq (continuous_fst.mul (MulOpposite.continuous_unop.comp continuous_snd)) continuous_const).inter (isClosed_eq ((MulOpposite.continuous_unop.comp continuous_snd).mul continuous_fst) continuous_const)`. Use `GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _ (fun a => (x a).2.rep.irr) ?_` and prove the remaining obligations. Introduce `a φ hφ`. Take `⟨K, hKo, hKc⟩` from `hKex (x a).1`. Conclude with `GlobalTheory.SchurAdm.schur_admissible _ K hKo hKc _ _ (x a).2.rep.irr (hA k _ _ _ (x a).2.rep.smooth (x a).2.rep.irr) φ hφ`.
-/
theorem piTensor_rep_isIrreducible (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h : ℕ} (x : Fin h → IrrGL k) :
    (piTensor fun a => (x a).rep).IsIrreducible := by
  have hKex : ∀ N : ℕ, ∃ K : Subgroup (GL (Fin N) k),
      IsOpen (K : Set (GL (Fin N) k)) ∧ IsCompact (K : Set (GL (Fin N) k)) := by
    intro N
    have hT2 : T2Space k := inferInstance
    let O : Subring k := (ValuativeRel.valuation k).integer
    have hOo : IsOpen (O : Set k) := (ValuativeRel.valuation k).isOpen_integer
    have hOc : IsCompact (O : Set k) := IsNonarchimedeanLocalField.isCompact_closedBall (K := k) 1
    let K : Subgroup (GL (Fin N) k) :=
      { carrier := {g | (∀ i j, (g : Matrix (Fin N) (Fin N) k) i j ∈ O) ∧
            ∀ i j, ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j ∈ O}
        mul_mem' := by
          rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
          refine ⟨fun i j => ?_, fun i j => ?_⟩
          · rw [Units.val_mul, Matrix.mul_apply]
            exact sum_mem fun l _ => mul_mem (ha1 i l) (hb1 l j)
          · rw [mul_inv_rev, Units.val_mul, Matrix.mul_apply]
            exact sum_mem fun l _ => mul_mem (hb2 i l) (ha2 l j)
        one_mem' := by
          refine ⟨fun i j => ?_, fun i j => ?_⟩
          · rw [Units.val_one, Matrix.one_apply]
            split_ifs
            exacts [one_mem _, zero_mem _]
          · rw [inv_one, Units.val_one, Matrix.one_apply]
            split_ifs
            exacts [one_mem _, zero_mem _]
        inv_mem' := by
          rintro a ⟨ha1, ha2⟩
          exact ⟨ha2, by rw [inv_inv]; exact ha1⟩ }
    have hKset : (K : Set (GL (Fin N) k)) =
        (⋂ i, ⋂ j, (fun g : GL (Fin N) k => (g : Matrix (Fin N) (Fin N) k) i j) ⁻¹' (O : Set k)) ∩
          ⋂ i, ⋂ j, (fun g : GL (Fin N) k => ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j) ⁻¹' (O : Set k) := by
      ext g
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
      exact Iff.rfl
    refine ⟨K, ?_, ?_⟩
    · rw [hKset]
      refine IsOpen.inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hOo.preimage ?_)
        (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hOo.preimage ?_)
      · exact Units.continuous_val.matrix_elem i j
      · exact Units.continuous_coe_inv.matrix_elem i j
    · rw [Units.isEmbedding_embedProduct.isInducing.isCompact_iff]
      let S : Set (Matrix (Fin N) (Fin N) k) := {A | ∀ i j, A i j ∈ O}
      have hS : IsCompact S := by
        have h := isCompact_univ_pi (fun _ : Fin N => isCompact_univ_pi (fun _ : Fin N => hOc))
        have hSe : S = Set.univ.pi (fun _ : Fin N => Set.univ.pi fun _ : Fin N => (O : Set k)) := by
          ext A
          show (∀ i j, A i j ∈ O) ↔ ∀ i ∈ (Set.univ : Set (Fin N)), ∀ j ∈ (Set.univ : Set (Fin N)), A i j ∈ (O : Set k)
          constructor
          · intro hA i _ j _
            exact hA i j
          · intro hA i j
            exact hA i (Set.mem_univ i) j (Set.mem_univ j)
        rw [hSe]
        exact h
      have hsub : Units.embedProduct (Matrix (Fin N) (Fin N) k) '' (K : Set (GL (Fin N) k)) =
          (S ×ˢ (MulOpposite.op '' S)) ∩
            {p | p.1 * MulOpposite.unop p.2 = 1 ∧ MulOpposite.unop p.2 * p.1 = 1} := by
        ext p
        constructor
        · rintro ⟨g, ⟨hg1, hg2⟩, rfl⟩
          exact ⟨⟨hg1, (g⁻¹ : GL (Fin N) k).val, hg2, rfl⟩, g.mul_inv, g.inv_mul⟩
        · rintro ⟨⟨hA, B, hB, hBp⟩, h1, h2⟩
          refine ⟨⟨p.1, MulOpposite.unop p.2, h1, h2⟩, ⟨hA, ?_⟩, rfl⟩
          show ∀ i j, (MulOpposite.unop p.2) i j ∈ O
          rw [← hBp]
          exact hB
      rw [hsub]
      refine (hS.prod (hS.image MulOpposite.continuous_op)).inter_right ?_
      exact (isClosed_eq (continuous_fst.mul (MulOpposite.continuous_unop.comp continuous_snd))
        continuous_const).inter
        (isClosed_eq ((MulOpposite.continuous_unop.comp continuous_snd).mul continuous_fst) continuous_const)
  refine GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _ (fun a => (x a).2.rep.irr) ?_
  intro a φ hφ
  obtain ⟨K, hKo, hKc⟩ := hKex (x a).1
  exact GlobalTheory.SchurAdm.schur_admissible _ K hKo hKc _ _ (x a).2.rep.irr
    (hA k _ _ _ (x a).2.rep.smooth (x a).2.rep.irr) φ hφ

variable {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
  [Fintype n] [DecidableEq n] {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/- English proof (translation)
Establish `hf : f (τ g v) = parInd e ρ g (f v)`. Simplify `LinearMap.congr_fun (f.isIntertwining' g) v` using `[LinearMap.comp_apply]`. Rewrite using `[hf, parInd_apply, one_mul]`.
-/
theorem eval_map (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} {ρ : Representation ℂ (Levi k m) W}
    (f : τ.IntertwiningMap (parInd e ρ)) (g : GL n k) (v : V) :
    (f (τ g v)).1.1 1 = (f v).1.1 g := by
  have hf : f (τ g v) = parInd e ρ g (f v) := by
    simpa [LinearMap.comp_apply] using LinearMap.congr_fun (f.isIntertwining' g) v
  rw [hf, parInd_apply, one_mul]

/- English proof (translation)
Establish `hp : (u : GL n k) ∈ parab k e` using `unipRad_le_parab k e u.2`. Establish `hl : leviProj k e ⟨u, hp⟩ = 1` using `(coe_mem_unipRad k (e := e) ⟨(u : GL n k), hp⟩).1 u.2`. Establish `hφ` using `parInd_law e ρ φ ⟨u, hp⟩ 1`. Rewrite `hφ` using `[hl]`. Simplify using `using hφ`.
-/
theorem eval_unipRad (e : (Σ a, m a) ≃ n) {ρ : Representation ℂ (Levi k m) W} (φ : IndSp e ρ)
    (u : unipRad k e) : φ.1.1 (u : GL n k) = φ.1.1 1 := by
  have hp : (u : GL n k) ∈ parab k e := unipRad_le_parab k e u.2
  have hl : leviProj k e ⟨u, hp⟩ = 1 := (coe_mem_unipRad k (e := e) ⟨(u : GL n k), hp⟩).1 u.2
  have hφ := parInd_law e ρ φ ⟨u, hp⟩ 1
  rw [hl] at hφ
  simpa using hφ

def evalOne (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} {ρ : Representation ℂ (Levi k m) W}
    (f : τ.IntertwiningMap (parInd e ρ)) : V →ₗ[ℂ] W where
  toFun v := (f v).1.1 1
  map_add' v w := by simp
  map_smul' c v := by simp

/- English proof (translation)
Unfold `GlobalTheory.PRep.twKer`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `w ⟨u, v, rfl⟩`. Establish `hu : evalOne e f (τ (u : GL n k) v) = evalOne e f v` using `by show (f (τ (u : GL n k) v)).1.1 1 = (f v).1.1 1`. Rewrite using `[eval_map, eval_unipRad e (f v) u]`.

Simplify using `only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul, hu, MonoidHom.one_apply, Units.val_one, one_smul, sub_self]`.
-/
theorem twKer_le_ker_evalOne (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V}
    {ρ : Representation ℂ (Levi k m) W} (f : τ.IntertwiningMap (parInd e ρ)) :
    twKer τ (unipRad k e) 1 ≤ LinearMap.ker (evalOne e f) := by
  unfold GlobalTheory.PRep.twKer
  rw [Submodule.span_le]
  rintro w ⟨u, v, rfl⟩
  have hu : evalOne e f (τ (u : GL n k) v) = evalOne e f v := by
    show (f (τ (u : GL n k) v)).1.1 1 = (f v).1.1 1
    rw [eval_map, eval_unipRad e (f v) u]
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul, hu, MonoidHom.one_apply,
    Units.val_one, one_smul, sub_self]

def frobMap (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} {ρ : Representation ℂ (Levi k m) W}
    (f : τ.IntertwiningMap (parInd e ρ)) : (jac e τ).IntertwiningMap ρ where
  toLinearMap := (twKer τ (unipRad k e) 1).liftQ (evalOne e f) (twKer_le_ker_evalOne e f)
  isIntertwining' g := by
    refine LinearMap.ext fun y => ?_
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have h := parInd_law e ρ (f v) ⟨_, leviEmb_mem_parab k e g⟩ 1
    rw [mul_one] at h
    simp only [leviProj_leviEmb] at h
    have h2 : evalOne e f (τ (leviEmb k e g) v) =
        (deltaHalf k m g : ℂ) • ρ g (evalOne e f v) := (eval_map e f _ v).trans h
    show (twKer τ (unipRad k e) 1).liftQ (evalOne e f) (twKer_le_ker_evalOne e f)
        (jac e τ g (Submodule.Quotient.mk v)) = ρ g (evalOne e f v)
    rw [jac_mk, map_smul]
    change (((deltaHalf k m g)⁻¹ : ℂˣ) : ℂ) • evalOne e f (τ (leviEmb k e g) v) = _
    rw [h2, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem frobMap_mk (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} {ρ : Representation ℂ (Levi k m) W}
    (f : τ.IntertwiningMap (parInd e ρ)) (v : V) :
    frobMap e f (Submodule.Quotient.mk v) = (f v).1.1 1 := rfl

/- English proof (translation)
Take `⟨v, hv⟩` from `hf`. Assume the negation of the conclusion as `hcon`. Simplify using `only [not_exists, not_not] at hcon`. Apply `hv` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `g`. Establish `h1` using `frobMap_mk e f (τ g v)`. Rewrite `h1` using `[hcon, eval_map]`. Simplify using `using h1.symm`.
-/
theorem frobMap_ne_zero (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} {ρ : Representation ℂ (Levi k m) W}
    (f : τ.IntertwiningMap (parInd e ρ)) (hf : ∃ v, f v ≠ 0) : ∃ y, frobMap e f y ≠ 0 := by
  obtain ⟨v, hv⟩ := hf
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  apply hv
  apply Subtype.ext
  apply Subtype.ext
  funext g
  have h1 := frobMap_mk e f (τ g v)
  rw [hcon, eval_map] at h1
  simpa using h1.symm

/- English proof (translation)
Use `haveI := hσ`. Break down `Representation.IsIrreducible.surjective_or_eq_zero f with hs | hz` into its components or cases. Conclude with `hs`. Take `⟨y, hy⟩` from `hf`. Conclude with `(hy (by simp [hz])).elim`.
-/
theorem surjective_of_ne_zero {G : Type} [Group G] {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (hσ : σ.IsIrreducible) (f : ρ.IntertwiningMap σ) (hf : ∃ y, f y ≠ 0) : Function.Surjective f := by
  haveI := hσ
  rcases Representation.IsIrreducible.surjective_or_eq_zero f with hs | hz
  · exact hs
  · obtain ⟨y, hy⟩ := hf
    exact (hy (by simp [hz])).elim

/- English proof (translation)
Introduce `k _ _ _ _ hA h N x hd V _ _ τ _ f hf`. Set `f' : τ.IntertwiningMap (parInd (stdBlocks (fun a => (x a).1) hd) (piTensor fun a => (x a).rep))` to `f`. Take `⟨y, hy⟩` from `frobMap_ne_zero _ f' hf`. Establish `hs` using `surjective_of_ne_zero (piTensor_rep_isIrreducible hA x) (frobMap _ f') ⟨y, hy⟩`. Establish `hq` using `jhMult_ne_zero_iff.2 (IsSubquotient.of_surjective _ hs)`.

Conclude with `Order.one_le_iff_ne_zero.2 hq`.
-/
theorem one_le_jm : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ} (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N) {V : Type}
    [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (GL (Fin N) k) V), IsSmooth τ →
    ∀ f : τ.IntertwiningMap (prodIrr x hd), (∃ v, f v ≠ 0) → 1 ≤ jm x hd τ := by
  intro k _ _ _ _ hA h N x hd V _ _ τ _ f hf
  let f' : τ.IntertwiningMap (parInd (stdBlocks (fun a => (x a).1) hd) (piTensor fun a => (x a).rep)) := f
  obtain ⟨y, hy⟩ := frobMap_ne_zero _ f' hf
  have hs := surjective_of_ne_zero (piTensor_rep_isIrreducible hA x) (frobMap _ f') ⟨y, hy⟩
  have hq := jhMult_ne_zero_iff.2 (IsSubquotient.of_surjective _ hs)
  exact Order.one_le_iff_ne_zero.2 hq

end GlobalTheory.CompanionTheory.FrobJm
