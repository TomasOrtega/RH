import Formalism.LocalToGlobal.GlobalTheory.GL4.PLinks

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions NumberField Formalism.MainNotions.flipTwoThree

section Frames

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def mulDual (S : HSpace E) (M : ℕ) (L : Submodule (𝓞 E) S.V) : AddSubgroup S.V :=
  (dualSub S L).map (DistribSMul.toAddMonoidHom S.V (M : E))

def IsoLat (S : HSpace E) (L L' : Submodule (𝓞 E) S.V) : Prop :=
  ∃ γ : S.V ≃ₗ[E] S.V, (∀ x y, S.hT (γ x) (γ y) = S.hT x y) ∧ ∀ x, x ∈ L ↔ γ x ∈ L'

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_dualSub (S : HSpace E) (L : Submodule (𝓞 E) S.V) (x : S.V) :
    x ∈ dualSub S L ↔ ∀ y ∈ L, S.hT y x ∈ (algebraMap (𝓞 E) E).range := Iff.rfl

/- English proof (translation)
Rewrite `hx`, the goal using `[mem_dualSub]`. Introduce `y hy`. Establish `h1 : γ.symm y ∈ L` using `(hL _).2 (by simpa using hy)`. Establish `h2` using `hx _ h1`. Rewrite `h2` using `[← hγ, LinearEquiv.apply_symm_apply]`. Then use the resulting hypothesis.
-/
theorem dual_map_of_isom (S : HSpace E) {L L' : Submodule (𝓞 E) S.V} (γ : S.V ≃ₗ[E] S.V)
    (hγ : ∀ x y, S.hT (γ x) (γ y) = S.hT x y) (hL : ∀ x, x ∈ L ↔ γ x ∈ L') {x : S.V}
    (hx : x ∈ dualSub S L) : γ x ∈ dualSub S L' := by
  rw [mem_dualSub] at hx ⊢
  intro y hy
  have h1 : γ.symm y ∈ L := (hL _).2 (by simpa using hy)
  have h2 := hx _ h1
  rwa [← hγ, LinearEquiv.apply_symm_apply] at h2

/- English proof (translation)
Introduce `x y`. Rewrite using `[← hγ, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]`.
-/
theorem isom_symm (S : HSpace E) (γ : S.V ≃ₗ[E] S.V) (hγ : ∀ x y, S.hT (γ x) (γ y) = S.hT x y) :
    ∀ x y, S.hT (γ.symm x) (γ.symm y) = S.hT x y := by
  intro x y
  rw [← hγ, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/- English proof (translation)
Use `choose ρ hρR hρ using hR`. Use `choose γ hγi hγL using hρ`. Establish `hfib : ∀ r ∈ R, (Finset.univ.filter (fun c => ρ c = r)).card ≤ Q ^ n`. Introduce `r hr`. Take `⟨h0, hle⟩` from `hQ r hr`.

Use `set K := dualSub S (L r) with hK`. Use `set H := (mulDual S M (L r)).addSubgroupOf K with hH`. Establish `: H.FiniteIndex` using `⟨h0⟩`. Establish `: Finite (K ⧸ H)` using `AddSubgroup.finite_quotient_of_finiteIndex`. Establish `hm : ∀ (c : {c // ρ c = r}) (a : Fin n), γ c.1 (e c.1 a) ∈ K` using `fun c a => by`.

Use `dual_map_of_isom S (γ c.1) (hγi c.1) (hγL c.1) (he c.1 a)` as an intermediate fact. Rewrite `this` using `[c.2]`. Conclude with `this`. Set `g : {c // ρ c = r} → (Fin n → K ⧸ H)` to `fun c a => ((⟨γ c.1 (e c.1 a), hm c a⟩ : K) : K ⧸ H)`. Establish `hg : Function.Injective g`.

Introduce `c c' hcc`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `hsep c.1 c'.1` to reduce the goal to its premises. Use `⟨(γ c.1).trans (γ c'.1).symm, fun x y => ?_, fun x => ?_, fun a => ?_⟩` and prove the remaining obligations. Simplify using `only [LinearEquiv.trans_apply]`.

Rewrite using `[isom_symm S _ (hγi c'.1), hγi c.1]`. Rewrite using `[hγL c.1 x, hγL c'.1 (((γ c.1).trans (γ c'.1).symm) x), LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, c.2, c'.2]`. Establish `h1` using `congrFun hcc a`. Simplify using `only [g] at h1`. Rewrite `h1` using `[QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]`.

Take `⟨z0, hz0, hz⟩` from `AddSubgroup.mem_map.1 h1`. Simplify using `only [DistribSMul.toAddMonoidHom_apply, AddSubgroup.coe_add, AddSubgroup.coe_neg] at hz`. Establish `hLs : ∀ x, x ∈ L r ↔ (γ c'.1).symm x ∈ L c'.1` using `fun x => by`. Rewrite using `[hγL c'.1 ((γ c'.1).symm x), LinearEquiv.apply_symm_apply, c'.2]`. Use `⟨(γ c'.1).symm (-z0), dual_map_of_isom S (γ c'.1).symm (isom_symm S _ (hγi c'.1)) hLs (neg_mem hz0), ?_⟩` and prove the remaining obligations.

Establish `h2 : (M : E) • (-z0) = γ c.1 (e c.1 a) - γ c'.1 (e c'.1 a)`. Rewrite using `[smul_neg, hz]`. Normalize the expressions using the abelian group laws. Rewrite using `[← LinearEquiv.map_smul, h2, map_sub, LinearEquiv.symm_apply_apply, LinearEquiv.trans_apply]`. Establish `hc` using `Nat.card_le_card_of_injective g hg`.

Rewrite `hc` using `[Nat.card_fun, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin]`. Establish `hKH : Nat.card (K ⧸ H) ≤ Q` using `hle`. Establish `hpow : Nat.card (K ⧸ H) ^ n ≤ Q ^ n` using `Nat.pow_le_pow_left hKH n`. Rewrite `hc` using `[Nat.card_eq_fintype_card, Fintype.card_subtype]`. Conclude with `hc.trans hpow`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem card_le_of_frames (S : HSpace E) (M n : ℕ) {ι : Type} [Fintype ι]
    (L : ι → Submodule (𝓞 E) S.V) (e : ι → Fin n → S.V)
    (he : ∀ c a, e c a ∈ dualSub S (L c))
    (hsep : ∀ c c', SameCls S M (L c) (L c') (e c) (e c') → c = c')
    (R : Finset ι) (hR : ∀ c, ∃ r ∈ R, IsoLat S (L c) (L r)) (Q : ℕ)
    (hQ : ∀ r ∈ R, (mulDual S M (L r)).relIndex (dualSub S (L r)) ≠ 0 ∧
      (mulDual S M (L r)).relIndex (dualSub S (L r)) ≤ Q) :
    Fintype.card ι ≤ R.card * Q ^ n := by
  classical
  choose ρ hρR hρ using hR
  choose γ hγi hγL using hρ
  have hfib : ∀ r ∈ R, (Finset.univ.filter (fun c => ρ c = r)).card ≤ Q ^ n := by
    intro r hr
    obtain ⟨h0, hle⟩ := hQ r hr
    set K := dualSub S (L r) with hK
    set H := (mulDual S M (L r)).addSubgroupOf K with hH
    have : H.FiniteIndex := ⟨h0⟩
    have : Finite (K ⧸ H) := AddSubgroup.finite_quotient_of_finiteIndex
    have hm : ∀ (c : {c // ρ c = r}) (a : Fin n), γ c.1 (e c.1 a) ∈ K := fun c a => by
      have := dual_map_of_isom S (γ c.1) (hγi c.1) (hγL c.1) (he c.1 a)
      rw [c.2] at this
      exact this
    let g : {c // ρ c = r} → (Fin n → K ⧸ H) := fun c a => ((⟨γ c.1 (e c.1 a), hm c a⟩ : K) : K ⧸ H)
    have hg : Function.Injective g := by
      intro c c' hcc
      apply Subtype.ext
      apply hsep c.1 c'.1
      refine ⟨(γ c.1).trans (γ c'.1).symm, fun x y => ?_, fun x => ?_, fun a => ?_⟩
      · simp only [LinearEquiv.trans_apply]
        rw [isom_symm S _ (hγi c'.1), hγi c.1]
      · rw [hγL c.1 x, hγL c'.1 (((γ c.1).trans (γ c'.1).symm) x), LinearEquiv.trans_apply,
          LinearEquiv.apply_symm_apply, c.2, c'.2]
      · have h1 := congrFun hcc a
        simp only [g] at h1
        rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h1
        obtain ⟨z0, hz0, hz⟩ := AddSubgroup.mem_map.1 h1
        simp only [DistribSMul.toAddMonoidHom_apply, AddSubgroup.coe_add, AddSubgroup.coe_neg] at hz
        have hLs : ∀ x, x ∈ L r ↔ (γ c'.1).symm x ∈ L c'.1 := fun x => by
          rw [hγL c'.1 ((γ c'.1).symm x), LinearEquiv.apply_symm_apply, c'.2]
        refine ⟨(γ c'.1).symm (-z0), dual_map_of_isom S (γ c'.1).symm (isom_symm S _ (hγi c'.1)) hLs
          (neg_mem hz0), ?_⟩
        have h2 : (M : E) • (-z0) = γ c.1 (e c.1 a) - γ c'.1 (e c'.1 a) := by
          rw [smul_neg, hz]
          abel
        rw [← LinearEquiv.map_smul, h2, map_sub, LinearEquiv.symm_apply_apply,
          LinearEquiv.trans_apply]
    have hc := Nat.card_le_card_of_injective g hg
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin] at hc
    have hKH : Nat.card (K ⧸ H) ≤ Q := hle
    have hpow : Nat.card (K ⧸ H) ^ n ≤ Q ^ n := Nat.pow_le_pow_left hKH n
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hc
    exact hc.trans hpow
  calc Fintype.card ι = (Finset.univ : Finset ι).card := Finset.card_univ.symm
    _ = ∑ r ∈ R, (Finset.univ.filter (fun c => ρ c = r)).card :=
        Finset.card_eq_sum_card_fiberwise (fun c _ => hρR c)
    _ ≤ ∑ _r ∈ R, Q ^ n := Finset.sum_le_sum hfib
    _ = R.card * Q ^ n := by rw [Finset.sum_const, smul_eq_mul]

end Frames

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
