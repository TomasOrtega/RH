import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.ModelIndexPairings.GenModelXiOf
import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.ModelIndexPairings.FourierTransformIdentityHolds

noncomputable section
open scoped BigOperators

namespace Formalism.L2.PairingIndexBounds.Mv

open Formalism.L2.Th1.H

section Pairing
variable {k : Type*} [Field k] {G G' : Type*} [AddCommGroup G] [AddCommGroup G']

/- English proof (translation)
Establish `: (M.addSubgroupOf N).FiniteIndex` using `⟨hfin⟩`. Establish `: Finite (N ⧸ M.addSubgroupOf N)` using `AddSubgroup.finite_quotient_of_finiteIndex`. Set `_` to `Fintype.ofFinite (N ⧸ M.addSubgroupOf N)`. Establish `hcl : ∀ y : N', ∀ n n' : N, (QuotientAddGroup.mk n : N ⧸ M.addSubgroupOf N) = QuotientAddGroup.mk n' → d y n = d y n'`. Introduce `y n n' h`.

Rewrite `h` using `[QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]`. Establish `h3` using `h1 y y.2 _ h (-n + n').2`. Establish `e : (n' : G) = (n : G) + ((-n + n' : N) : G)`. Simplify using the standard rewrite rules. Rewrite using `[e, hd.2.2, h3, mul_one]`.

Set `χ : (N' ⧸ M'.addSubgroupOf N') → (Multiplicative (N ⧸ M.addSubgroupOf N) →* k)` to `fun q' => { toFun := fun q => d ((Quotient.out q' : N') : G') ((Quotient.out (Multiplicative.toAdd q) : N) : G) map_one' := by`. Use `hcl (Quotient.out q') (Quotient.out (0 : N ⧸ M.addSubgroupOf N)) 0 (by rw [QuotientAddGroup.out_eq']; rfl)` as an intermediate fact. Simplify `this` using `[IsBichar.map_zero_right hd]`. Use the proof step `map_mul' := by`. Introduce `q₁ q₂`.

Use `hcl (Quotient.out q') (Quotient.out (Multiplicative.toAdd q₁ + Multiplicative.toAdd q₂)) (Quotient.out (Multiplicative.toAdd q₁) + Quotient.out (Multiplicative.toAdd q₂)) (by rw [QuotientAddGroup.mk_add]; simp only [QuotientAddGroup.out_eq'])` as an intermediate fact. Rewrite `this` using `[AddSubgroup.coe_add, hd.2.2]`. Conclude with `this }`. Establish `hχ : Function.Injective χ`. Introduce `q₁ q₂ h`.

Establish `hall : ∀ x ∈ N, d (((Quotient.out q₁ : N') - Quotient.out q₂ : N') : G') x = 1`. Introduce `x hx`. Establish `h3` using `DFunLike.congr_fun h (Multiplicative.ofAdd (QuotientAddGroup.mk (⟨x, hx⟩ : N)))`. Establish `e1` using `hcl (Quotient.out q₁) (Quotient.out (QuotientAddGroup.mk (⟨x, hx⟩ : N) : N ⧸ M.addSubgroupOf N)) ⟨x, hx⟩ (QuotientAddGroup.out_eq' _)`. Establish `e2` using `hcl (Quotient.out q₂) (Quotient.out (QuotientAddGroup.mk (⟨x, hx⟩ : N) : N ⧸ M.addSubgroupOf N)) ⟨x, hx⟩ (QuotientAddGroup.out_eq' _)`.

Establish `h4 : d ((Quotient.out q₁ : N') : G') x = d ((Quotient.out q₂ : N') : G') x`. Rewrite using `[← e1, ← e2]`. Conclude with `h3`. Rewrite using `[AddSubgroup.coe_sub, IsBichar.map_sub_left hd, h4, mul_inv_cancel₀ (hd.1 _ _)]`. Establish `hm` using `h2 _ ((Quotient.out q₁ : N') - Quotient.out q₂ : N').2 hall`.

Rewrite using `[← QuotientAddGroup.out_eq' q₁, ← QuotientAddGroup.out_eq' q₂]`. Use `symm`. Rewrite using `[QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]`. Use `hm using 1` and compare the differences between its conclusion and the goal. Simplify using `only [AddSubgroup.coe_add, AddSubgroup.coe_neg, AddSubgroup.coe_sub]`.

Normalize the expressions using the abelian group laws. Establish `hli : LinearIndependent k (fun q' => (χ q' : Multiplicative (N ⧸ M.addSubgroupOf N) → k))` using `(linearIndependent_monoidHom (Multiplicative (N ⧸ M.addSubgroupOf N)) k).comp χ hχ`. Establish `hF : Finite (N' ⧸ M'.addSubgroupOf N')` using `hli.finite`. Set `_` to `Fintype.ofFinite (N' ⧸ M'.addSubgroupOf N')`. Establish `hle` using `hli.fintype_card_le_finrank`.

Rewrite `hle` using `[Module.finrank_fintype_fun_eq_card, Fintype.card_multiplicative, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]`. Use `⟨?_, hle⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Nat.card (N' ⧸ M'.addSubgroupOf N') ≠ 0`. Conclude with `Nat.card_pos.ne'`.
-/
theorem relIndex_le_of_pairing (d : G' → G → k) (hd : IsBichar d) (M N : AddSubgroup G) (M' N' : AddSubgroup G')
    (h1 : ∀ y ∈ N', ∀ x ∈ M, x ∈ N → d y x = 1) (h2 : ∀ y ∈ N', (∀ x ∈ N, d y x = 1) → y ∈ M')
    (hfin : M.relIndex N ≠ 0) : M'.relIndex N' ≠ 0 ∧ M'.relIndex N' ≤ M.relIndex N := by
  classical
  have : (M.addSubgroupOf N).FiniteIndex := ⟨hfin⟩
  have : Finite (N ⧸ M.addSubgroupOf N) := AddSubgroup.finite_quotient_of_finiteIndex
  let _ := Fintype.ofFinite (N ⧸ M.addSubgroupOf N)

  have hcl : ∀ y : N', ∀ n n' : N, (QuotientAddGroup.mk n : N ⧸ M.addSubgroupOf N) = QuotientAddGroup.mk n' →
      d y n = d y n' := by
    intro y n n' h
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h
    have h3 := h1 y y.2 _ h (-n + n').2
    have e : (n' : G) = (n : G) + ((-n + n' : N) : G) := by
      simp
    rw [e, hd.2.2, h3, mul_one]
  let χ : (N' ⧸ M'.addSubgroupOf N') → (Multiplicative (N ⧸ M.addSubgroupOf N) →* k) := fun q' =>
    { toFun := fun q => d ((Quotient.out q' : N') : G') ((Quotient.out (Multiplicative.toAdd q) : N) : G)
      map_one' := by
        have := hcl (Quotient.out q') (Quotient.out (0 : N ⧸ M.addSubgroupOf N)) 0
          (by rw [QuotientAddGroup.out_eq']; rfl)
        simpa [IsBichar.map_zero_right hd] using this
      map_mul' := by
        intro q₁ q₂
        have := hcl (Quotient.out q') (Quotient.out (Multiplicative.toAdd q₁ + Multiplicative.toAdd q₂))
          (Quotient.out (Multiplicative.toAdd q₁) + Quotient.out (Multiplicative.toAdd q₂))
          (by rw [QuotientAddGroup.mk_add]; simp only [QuotientAddGroup.out_eq'])
        rw [AddSubgroup.coe_add, hd.2.2] at this
        exact this }
  have hχ : Function.Injective χ := by
    intro q₁ q₂ h
    have hall : ∀ x ∈ N, d (((Quotient.out q₁ : N') - Quotient.out q₂ : N') : G') x = 1 := by
      intro x hx
      have h3 := DFunLike.congr_fun h (Multiplicative.ofAdd (QuotientAddGroup.mk (⟨x, hx⟩ : N)))
      have e1 := hcl (Quotient.out q₁) (Quotient.out (QuotientAddGroup.mk (⟨x, hx⟩ : N) : N ⧸ M.addSubgroupOf N))
        ⟨x, hx⟩ (QuotientAddGroup.out_eq' _)
      have e2 := hcl (Quotient.out q₂) (Quotient.out (QuotientAddGroup.mk (⟨x, hx⟩ : N) : N ⧸ M.addSubgroupOf N))
        ⟨x, hx⟩ (QuotientAddGroup.out_eq' _)
      have h4 : d ((Quotient.out q₁ : N') : G') x = d ((Quotient.out q₂ : N') : G') x := by
        rw [← e1, ← e2]; exact h3
      rw [AddSubgroup.coe_sub, IsBichar.map_sub_left hd, h4, mul_inv_cancel₀ (hd.1 _ _)]
    have hm := h2 _ ((Quotient.out q₁ : N') - Quotient.out q₂ : N').2 hall
    rw [← QuotientAddGroup.out_eq' q₁, ← QuotientAddGroup.out_eq' q₂]
    symm
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    convert hm using 1
    simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg, AddSubgroup.coe_sub]
    abel
  have hli : LinearIndependent k (fun q' => (χ q' : Multiplicative (N ⧸ M.addSubgroupOf N) → k)) :=
    (linearIndependent_monoidHom (Multiplicative (N ⧸ M.addSubgroupOf N)) k).comp χ hχ
  have hF : Finite (N' ⧸ M'.addSubgroupOf N') := hli.finite
  let _ := Fintype.ofFinite (N' ⧸ M'.addSubgroupOf N')
  have hle := hli.fintype_card_le_finrank
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_multiplicative, ← Nat.card_eq_fintype_card,
    ← Nat.card_eq_fintype_card] at hle
  refine ⟨?_, hle⟩
  change Nat.card (N' ⧸ M'.addSubgroupOf N') ≠ 0
  exact Nat.card_pos.ne'

end Pairing

/- English proof (translation)
Introduce `k _ A B _ _ c hc A₀ A₁ B₀ B₁ h1 h2 h3 hfin`. Take `⟨hfinB, hle⟩` from `relIndex_le_of_pairing c hc A₁ A₀ B₀ B₁ (fun b hb a ha _ => h2 b hb a ha) (fun b _ h => (h1 b).2 h) hfin`. Take `⟨-, hge⟩` from `relIndex_le_of_pairing (fun a b => c b a) (bichar_swap hc) B₀ B₁ A₁ A₀ (fun a ha b hb _ => (h1 b).1 hb a ha) h3 hfinB`. Conclude with `le_antisymm hle hge`.
-/
theorem index_duality_holds : IndexDual := by
  intro k _ A B _ _ c hc A₀ A₁ B₀ B₁ h1 h2 h3 hfin
  obtain ⟨hfinB, hle⟩ := relIndex_le_of_pairing c hc A₁ A₀ B₀ B₁ (fun b hb a ha _ => h2 b hb a ha)
    (fun b _ h => (h1 b).2 h) hfin
  obtain ⟨-, hge⟩ := relIndex_le_of_pairing (fun a b => c b a) (bichar_swap hc) B₀ B₁ A₁ A₀
    (fun a ha b hb _ => (h1 b).1 hb a ha) h3 hfinB
  exact le_antisymm hle hge

section Vol
variable {G : Type*} [AddCommGroup G]

/- English proof (translation)
Establish `e1 : W.relIndex (X ⊓ Y) * X.relIndex Y = W.relIndex Y`. Rewrite using `[← AddSubgroup.inf_relIndex_right X Y]`. Conclude with `AddSubgroup.relIndex_mul_relIndex _ _ _ hW inf_le_right`. Establish `e2 : W.relIndex (X ⊓ Y) * Y.relIndex X = W.relIndex X`. Rewrite using `[← AddSubgroup.inf_relIndex_left X Y]`.

Conclude with `AddSubgroup.relIndex_mul_relIndex _ _ _ hW inf_le_left`. Rewrite using `[← e1, ← e2]`. Use `push_cast`. Establish `: ((W.relIndex (X ⊓ Y) : ℕ) : ℝ) ≠ 0` using `by exact_mod_cast hfin`. Rewrite using `[mul_div_mul_left _ _ this]`.
-/
theorem ratio_relIndex (X Y W : AddSubgroup G) (hW : W ≤ X ⊓ Y) (hfin : W.relIndex (X ⊓ Y) ≠ 0) :
    ((X.relIndex Y : ℕ) : ℝ) / ((Y.relIndex X : ℕ) : ℝ) = ((W.relIndex Y : ℕ) : ℝ) / ((W.relIndex X : ℕ) : ℝ) := by
  have e1 : W.relIndex (X ⊓ Y) * X.relIndex Y = W.relIndex Y := by
    rw [← AddSubgroup.inf_relIndex_right X Y]
    exact AddSubgroup.relIndex_mul_relIndex _ _ _ hW inf_le_right
  have e2 : W.relIndex (X ⊓ Y) * Y.relIndex X = W.relIndex X := by
    rw [← AddSubgroup.inf_relIndex_left X Y]
    exact AddSubgroup.relIndex_mul_relIndex _ _ _ hW inf_le_left
  rw [← e1, ← e2]
  push_cast
  have : ((W.relIndex (X ⊓ Y) : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hfin
  rw [mul_div_mul_left _ _ this]

/- English proof (translation)
Establish `aux : ∀ P Q R : AddSubgroup G, R.relIndex Q ≠ 0 → (X ⊓ Y ⊓ Z) = P ⊓ Q ⊓ R → (X ⊓ Y ⊓ Z).relIndex (P ⊓ Q) ≠ 0`. Introduce `P Q R h e`. Rewrite using `[e, AddSubgroup.inf_relIndex_left]`. Introduce `h0`. Conclude with `h (AddSubgroup.relIndex_eq_zero_of_le_right inf_le_right h0)`.

Establish `fXY : (X ⊓ Y ⊓ Z).relIndex (X ⊓ Y) ≠ 0` using `aux X Y Z hZY rfl`. Establish `fYZ : (X ⊓ Y ⊓ Z).relIndex (Y ⊓ Z) ≠ 0` using `aux Z Y X hXY (by`. Use extensionality with `x; simp only [AddSubgroup.mem_inf]; tauto) |> fun h => by rwa [inf_comm Z Y] at h`. Establish `wY : (X ⊓ Y ⊓ Z).relIndex Y ≠ 0`. Rewrite using `[← AddSubgroup.relIndex_mul_relIndex (X ⊓ Y ⊓ Z) (X ⊓ Y) Y inf_le_left inf_le_right, AddSubgroup.inf_relIndex_right X Y]`.

Conclude with `Nat.mul_ne_zero fXY hXY`. Establish `wX : (X ⊓ Y ⊓ Z).relIndex X ≠ 0`. Rewrite using `[← AddSubgroup.relIndex_mul_relIndex (X ⊓ Y ⊓ Z) (X ⊓ Y) X inf_le_left inf_le_left, AddSubgroup.inf_relIndex_left X Y]`. Conclude with `Nat.mul_ne_zero fXY hYX`. Establish `fXZ : (X ⊓ Y ⊓ Z).relIndex (X ⊓ Z) ≠ 0`.

Introduce `h0`. Conclude with `wX (AddSubgroup.relIndex_eq_zero_of_le_right inf_le_left h0)`. Rewrite using `[ratio_relIndex X Y (X ⊓ Y ⊓ Z) inf_le_left fXY, ratio_relIndex Y Z (X ⊓ Y ⊓ Z) (le_inf (inf_le_left.trans inf_le_right) inf_le_right) fYZ, ratio_relIndex X Z (X ⊓ Y ⊓ Z) (le_inf (inf_le_left.trans inf_le_left) inf_le_right) fXZ]`. Establish `: (((X ⊓ Y ⊓ Z).relIndex Y : ℕ) : ℝ) ≠ 0` using `by exact_mod_cast wY`. Clear the denominators using the available nonvanishing facts.
-/
theorem ratio_cocycle (X Y Z : AddSubgroup G) (hXY : X.relIndex Y ≠ 0) (hYX : Y.relIndex X ≠ 0)
    (hZY : Z.relIndex Y ≠ 0) :
    ((X.relIndex Y : ℕ) : ℝ) / ((Y.relIndex X : ℕ) : ℝ) * (((Y.relIndex Z : ℕ) : ℝ) / ((Z.relIndex Y : ℕ) : ℝ)) =
      ((X.relIndex Z : ℕ) : ℝ) / ((Z.relIndex X : ℕ) : ℝ) := by
  have aux : ∀ P Q R : AddSubgroup G, R.relIndex Q ≠ 0 → (X ⊓ Y ⊓ Z) = P ⊓ Q ⊓ R →
      (X ⊓ Y ⊓ Z).relIndex (P ⊓ Q) ≠ 0 := by
    intro P Q R h e
    rw [e, AddSubgroup.inf_relIndex_left]
    intro h0
    exact h (AddSubgroup.relIndex_eq_zero_of_le_right inf_le_right h0)
  have fXY : (X ⊓ Y ⊓ Z).relIndex (X ⊓ Y) ≠ 0 := aux X Y Z hZY rfl
  have fYZ : (X ⊓ Y ⊓ Z).relIndex (Y ⊓ Z) ≠ 0 := aux Z Y X hXY (by
    ext x; simp only [AddSubgroup.mem_inf]; tauto) |> fun h => by rwa [inf_comm Z Y] at h
  have wY : (X ⊓ Y ⊓ Z).relIndex Y ≠ 0 := by
    rw [← AddSubgroup.relIndex_mul_relIndex (X ⊓ Y ⊓ Z) (X ⊓ Y) Y inf_le_left inf_le_right,
      AddSubgroup.inf_relIndex_right X Y]
    exact Nat.mul_ne_zero fXY hXY
  have wX : (X ⊓ Y ⊓ Z).relIndex X ≠ 0 := by
    rw [← AddSubgroup.relIndex_mul_relIndex (X ⊓ Y ⊓ Z) (X ⊓ Y) X inf_le_left inf_le_left,
      AddSubgroup.inf_relIndex_left X Y]
    exact Nat.mul_ne_zero fXY hYX
  have fXZ : (X ⊓ Y ⊓ Z).relIndex (X ⊓ Z) ≠ 0 := by
    intro h0
    exact wX (AddSubgroup.relIndex_eq_zero_of_le_right inf_le_left h0)
  rw [ratio_relIndex X Y (X ⊓ Y ⊓ Z) inf_le_left fXY,
    ratio_relIndex Y Z (X ⊓ Y ⊓ Z) (le_inf (inf_le_left.trans inf_le_right) inf_le_right) fYZ,
    ratio_relIndex X Z (X ⊓ Y ⊓ Z) (le_inf (inf_le_left.trans inf_le_left) inf_le_right) fXZ]
  have : (((X ⊓ Y ⊓ Z).relIndex Y : ℕ) : ℝ) ≠ 0 := by exact_mod_cast wY
  field_simp

end Vol

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl`. Simplify using `at h`. Introduce and unpack `rfl`. Simplify using `at h`.
-/
theorem pos_div_ne {a b : ℕ} (h : 0 < (a : ℝ) / (b : ℝ)) : a ≠ 0 ∧ b ≠ 0 := by
  constructor
  · rintro rfl; simp at h
  · rintro rfl; simp at h

/- English proof (translation)
Introduce `V _ _ H α A B Λ₀ Λ₁ Λ₂ hH hA hB g0 g1 g2 h01 h12 h02 θ hθ`. Take `⟨hbc, hheis⟩` from `heisenberg_unitary_holds V H α A B hH hA hB`. Take `⟨hfa, hfb⟩` from `fixed_of_good H α A B Λ₀ g0 θ hθ`. Take `⟨Xi, hXi, -⟩` from `hXE ℂ A B (V → ℂ) (cU H A B) (wA H α A) (wB H α B) hbc hheis (Λ₀.addSubgroupOf A) θ hfa hfb`. Take `⟨Xi', hXi'⟩` from `LinearMap.exists_extend Xi`.

Establish `hext : ∀ (Φ : A → ℂ) (h : Φ ∈ Sch (cU H A B) (Λ₀.addSubgroupOf A)), Xi' Φ = Xi ⟨Φ, h⟩`. Introduce `Φ h`. Rewrite using `[← hXi']`. Both sides reduce to the same expression. Take `⟨m1, pos01, eq01⟩` from `hMU V H α A B Λ₀ Λ₁ hH hA hB g0 g1 h01 θ hθ Xi hXi`.

Take `⟨m2, pos02, eq02⟩` from `hMU V H α A B Λ₀ Λ₂ hH hA hB g0 g2 h02 θ hθ Xi hXi`. Establish `hθ1 : inter H α Λ₀ Λ₁ θ ∈ fixedBy H α Λ₁` using `interFixed V H hH Λ₀ Λ₁ α g1.1 h01 θ hθ`. Set `Xi1 : Sch (cU H A B) (Λ₁.addSubgroupOf A) →ₗ[ℂ] (V → ℂ)` to `(((Real.sqrt (volA A Λ₀ Λ₁))⁻¹ : ℝ) : ℂ) • (Xi' ∘ₗ (Sch (cU H A B) (Λ₁.addSubgroupOf A)).subtype)`. Establish `hXi1 : IsXi (cU H A B) (wA H α A) (wB H α B) (Λ₁.addSubgroupOf A) (inter H α Λ₀ Λ₁ θ) Xi1`. Introduce `a b`.

Take `⟨mb, eb⟩` from `(hXI ℂ A B (V → ℂ) (cU H A B) (wA H α A) (wB H α B) hbc hheis (Λ₀.addSubgroupOf A) θ Xi hXi _ m1).2 b`. Take `⟨ma, ea⟩` from `(hXI ℂ A B (V → ℂ) (cU H A B) (wA H α A) (wB H α B) hbc hheis (Λ₀.addSubgroupOf A) θ Xi hXi _ mb).1 a`. Express the relevant statement in the definitionally equal form `(((Real.sqrt (volA A Λ₀ Λ₁))⁻¹ : ℝ) : ℂ) • Xi' (gen (cU H A B) (Λ₁.addSubgroupOf A) a b) = _`. Rewrite using `[eq01, map_smul, map_smul, ← eb, ← ea]`. Use `congr 1`.

Conclude with `hext _ ma`. Take `⟨m12, pos12, eq12⟩` from `hMU V H α A B Λ₁ Λ₂ hH hA hB g1 g2 h12 _ hθ1 Xi1 hXi1`. Rewrite using `[eq12, eq02, ← hext _ m2]`. Express the relevant statement in the definitionally equal form `_ • ((((Real.sqrt (volA A Λ₀ Λ₁))⁻¹ : ℝ) : ℂ) • Xi' (ind ((Λ₂.addSubgroupOf A : AddSubgroup A) : Set A))) = _`. Rewrite using `[smul_smul, ← Complex.ofReal_mul]`.

Use `congr 2`. Establish `hc : volA A Λ₀ Λ₁ * volA A Λ₁ Λ₂ = volA A Λ₀ Λ₂`. Unfold `volA at pos01 pos12 ⊢`. Take `⟨n1, n2⟩` from `pos_div_ne pos01`. Take `⟨-, n4⟩` from `pos_div_ne pos12`.

Conclude with `ratio_cocycle (Λ₀ ⊓ A) (Λ₁ ⊓ A) (Λ₂ ⊓ A) n1 n2 n4`. Rewrite using `[← hc, Real.sqrt_mul pos01.le, mul_inv, mul_comm]`.
-/
theorem MovesComposeU_of (hMU : MovesU) (hXE : XiExists) (hXI : XiInter) : MovesComposeU := by
  intro V _ _ H α A B Λ₀ Λ₁ Λ₂ hH hA hB g0 g1 g2 h01 h12 h02 θ hθ
  classical
  obtain ⟨hbc, hheis⟩ := heisenberg_unitary_holds V H α A B hH hA hB
  obtain ⟨hfa, hfb⟩ := fixed_of_good H α A B Λ₀ g0 θ hθ
  obtain ⟨Xi, hXi, -⟩ := hXE ℂ A B (V → ℂ) (cU H A B) (wA H α A) (wB H α B) hbc hheis
    (Λ₀.addSubgroupOf A) θ hfa hfb
  obtain ⟨Xi', hXi'⟩ := LinearMap.exists_extend Xi
  have hext : ∀ (Φ : A → ℂ) (h : Φ ∈ Sch (cU H A B) (Λ₀.addSubgroupOf A)), Xi' Φ = Xi ⟨Φ, h⟩ := by
    intro Φ h
    rw [← hXi']; rfl
  obtain ⟨m1, pos01, eq01⟩ := hMU V H α A B Λ₀ Λ₁ hH hA hB g0 g1 h01 θ hθ Xi hXi
  obtain ⟨m2, pos02, eq02⟩ := hMU V H α A B Λ₀ Λ₂ hH hA hB g0 g2 h02 θ hθ Xi hXi
  have hθ1 : inter H α Λ₀ Λ₁ θ ∈ fixedBy H α Λ₁ := interFixed V H hH Λ₀ Λ₁ α g1.1 h01 θ hθ
  let Xi1 : Sch (cU H A B) (Λ₁.addSubgroupOf A) →ₗ[ℂ] (V → ℂ) :=
    (((Real.sqrt (volA A Λ₀ Λ₁))⁻¹ : ℝ) : ℂ) • (Xi' ∘ₗ (Sch (cU H A B) (Λ₁.addSubgroupOf A)).subtype)
  have hXi1 : IsXi (cU H A B) (wA H α A) (wB H α B) (Λ₁.addSubgroupOf A) (inter H α Λ₀ Λ₁ θ) Xi1 := by
    intro a b
    obtain ⟨mb, eb⟩ := (hXI ℂ A B (V → ℂ) (cU H A B) (wA H α A) (wB H α B) hbc hheis
      (Λ₀.addSubgroupOf A) θ Xi hXi _ m1).2 b
    obtain ⟨ma, ea⟩ := (hXI ℂ A B (V → ℂ) (cU H A B) (wA H α A) (wB H α B) hbc hheis
      (Λ₀.addSubgroupOf A) θ Xi hXi _ mb).1 a
    change (((Real.sqrt (volA A Λ₀ Λ₁))⁻¹ : ℝ) : ℂ) • Xi' (gen (cU H A B) (Λ₁.addSubgroupOf A) a b) = _
    rw [eq01, map_smul, map_smul, ← eb, ← ea]
    congr 1
    exact hext _ ma
  obtain ⟨m12, pos12, eq12⟩ := hMU V H α A B Λ₁ Λ₂ hH hA hB g1 g2 h12 _ hθ1 Xi1 hXi1
  rw [eq12, eq02, ← hext _ m2]
  change _ • ((((Real.sqrt (volA A Λ₀ Λ₁))⁻¹ : ℝ) : ℂ) • Xi' (ind ((Λ₂.addSubgroupOf A : AddSubgroup A) : Set A))) = _
  rw [smul_smul, ← Complex.ofReal_mul]
  congr 2
  have hc : volA A Λ₀ Λ₁ * volA A Λ₁ Λ₂ = volA A Λ₀ Λ₂ := by
    unfold volA at pos01 pos12 ⊢
    obtain ⟨n1, n2⟩ := pos_div_ne pos01
    obtain ⟨-, n4⟩ := pos_div_ne pos12
    exact ratio_cocycle (Λ₀ ⊓ A) (Λ₁ ⊓ A) (Λ₂ ⊓ A) n1 n2 n4
  rw [← hc, Real.sqrt_mul pos01.le, mul_inv, mul_comm]

end Formalism.L2.PairingIndexBounds.Mv

namespace Formalism.L2.PairingIndexBounds.Mv
end Formalism.L2.PairingIndexBounds.Mv
