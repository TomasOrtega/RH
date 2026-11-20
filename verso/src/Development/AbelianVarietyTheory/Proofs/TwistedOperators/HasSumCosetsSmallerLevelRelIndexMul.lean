import Mathlib

namespace GlobalTheory

open QuotientGroup

/- English proof (translation)
Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts.

Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts.
-/
theorem hasSum_comp_fst_card_mul_of_fintype {α β : Type} [Fintype β] (f : α → ℂ) (a : ℂ) (hf : HasSum f a) :
    HasSum (fun p : α × β => f p.1) ((Fintype.card β : ℂ) * a) := by
  classical
  have hdec : (fun p : α × β => f p.1) = fun p => ∑ b : β, (if p.2 = b then f p.1 else 0) := by
    funext p
    simp
  rw [hdec]
  have hterm : ∀ b ∈ (Finset.univ : Finset β),
      HasSum (fun p : α × β => if p.2 = b then f p.1 else 0) a := by
    intro b _
    have hinj : Function.Injective (fun x : α => (x, b)) := fun x y h => by
      simpa using congrArg Prod.fst h
    rw [← hinj.hasSum_iff]
    · simpa [Function.comp_def] using hf
    · intro p hp
      by_cases h : p.2 = b
      · exact absurd ⟨p.1, by ext <;> simp [h]⟩ hp
      · simp [h]
  have := hasSum_sum hterm
  simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using this

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules.

Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Proceed by induction.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Apply an available result and prove the equalities needed to match it to the conclusion. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Introduce a local definition for the expression. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Equip the data with the indicated structure. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Apply an available result and prove the equalities needed to match it to the conclusion. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact.

Both sides reduce to the same expression. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem hasSum_cosets_smaller_level_relIndex_mul : ∀ {G : Type} [Group G] (K J H Γ : Subgroup G), K ≤ J → J ≤ H → H ≤ Γ → K.relIndex J ≠ 0 → ∀ (Ψ : G → ℂ) (z : ℂ), (∀ g ∈ Γ, g ∉ H → Ψ g = 0) → (∀ g ∈ Γ, ∀ k ∈ J, Ψ (g * k) = Ψ g) → HasSum (fun y : H ⧸ J.subgroupOf H => Ψ (y.out : H)) z → HasSum (fun y : Γ ⧸ K.subgroupOf Γ => Ψ (y.out : Γ)) ((K.relIndex J : ℂ) * z) := by
  intro G _ K J H Γ hKJ hJH hHΓ hidx Ψ z hvan hinv hsum
  classical

  set f : Γ ⧸ J.subgroupOf Γ → ℂ := fun x => Ψ (x.out : Γ) with hf
  have hfmk : ∀ g : Γ, f (mk g) = Ψ (g : G) := by
    intro g
    obtain ⟨j, hj⟩ := QuotientGroup.mk_out_eq_mul (J.subgroupOf Γ) g
    simp only [hf, hj, Subgroup.coe_mul]
    exact hinv _ g.2 _ (Subgroup.mem_subgroupOf.mp j.2)

  let ι : H ⧸ J.subgroupOf H → Γ ⧸ J.subgroupOf Γ := fun y => mk (Subgroup.inclusion hHΓ y.out)
  have hιmk : ∀ a : H, ι (mk a) = mk (Subgroup.inclusion hHΓ a) := by
    intro a
    obtain ⟨j, hj⟩ := QuotientGroup.mk_out_eq_mul (J.subgroupOf H) a
    show (mk (Subgroup.inclusion hHΓ (mk a : H ⧸ J.subgroupOf H).out) : Γ ⧸ J.subgroupOf Γ) = _
    rw [hj, QuotientGroup.eq]
    simp [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_subgroupOf.mp j.2
  have hιinj : Function.Injective ι := by
    intro x y hxy
    induction x using QuotientGroup.induction_on with | H a => ?_
    induction y using QuotientGroup.induction_on with | H b => ?_
    rw [hιmk, hιmk, QuotientGroup.eq] at hxy
    rw [QuotientGroup.eq]
    simpa [Subgroup.mem_subgroupOf] using hxy
  have h1 : HasSum f z := by
    rw [← hιinj.hasSum_iff]
    · convert hsum using 1
      funext y
      show f (mk (Subgroup.inclusion hHΓ y.out)) = _
      rw [hfmk]
      rfl
    · intro x hx
      show Ψ (x.out : G) = 0
      apply hvan _ x.out.2
      intro hH
      apply hx
      refine ⟨mk ⟨(x.out : G), hH⟩, ?_⟩
      rw [hιmk]
      conv_rhs => rw [← QuotientGroup.out_eq' x]
      rfl

  have hle : K.subgroupOf Γ ≤ J.subgroupOf Γ := fun x hx => by
    simpa [Subgroup.mem_subgroupOf] using hKJ (Subgroup.mem_subgroupOf.mp hx)
  let e := Subgroup.quotientEquivProdOfLE hle
  have hJΓ : J ≤ Γ := hJH.trans hHΓ
  have hrel : (K.subgroupOf Γ).relIndex (J.subgroupOf Γ) = K.relIndex J :=
    Subgroup.relIndex_subgroupOf hJΓ
  haveI : (((K.subgroupOf Γ).subgroupOf (J.subgroupOf Γ))).FiniteIndex := ⟨by
    rw [← Subgroup.relIndex, hrel]; exact hidx⟩
  haveI : Finite (J.subgroupOf Γ ⧸ (K.subgroupOf Γ).subgroupOf (J.subgroupOf Γ)) :=
    Subgroup.finite_quotient_of_finiteIndex
  letI := Fintype.ofFinite (J.subgroupOf Γ ⧸ (K.subgroupOf Γ).subgroupOf (J.subgroupOf Γ))
  have hcard : (Fintype.card (J.subgroupOf Γ ⧸ (K.subgroupOf Γ).subgroupOf (J.subgroupOf Γ)) : ℂ)
      = (K.relIndex J : ℂ) := by
    rw [Fintype.card_eq_nat_card, ← Subgroup.index, ← Subgroup.relIndex, hrel]
  have h2 := hasSum_comp_fst_card_mul_of_fintype (β := J.subgroupOf Γ ⧸ (K.subgroupOf Γ).subgroupOf (J.subgroupOf Γ)) f z h1
  rw [hcard, ← e.hasSum_iff] at h2
  convert h2 using 1
  funext y
  have he1 : (e y).1 = mk y.out := by
    conv_lhs => rw [← QuotientGroup.out_eq' y]
    rfl
  simp only [Function.comp_apply, he1, hfmk]

end GlobalTheory
