import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwoVarPolySubstMatrixBasicLawsStatement

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ.H3

/- English proof (translation)
Introduce `δ hδ`. Rewrite `hδ`, the goal using `[CongruenceSubgroup.Gamma_mem]`. Establish `key : ∀ x : ℤ, ((x : ZMod M) = ZMod.castHom h (ZMod M) (x : ZMod M'))` using `fun x => by`. Rewrite using `[map_intCast]`. Take `⟨h1, h2, h3, h4⟩` from `hδ`.

Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[key, h1, map_one]`. Rewrite using `[key, h2, map_zero]`. Rewrite using `[key, h3, map_zero]`. Rewrite using `[key, h4, map_one]`.
-/
theorem gamma_le_of_dvd {M M' : ℕ} (h : M ∣ M') :
    CongruenceSubgroup.Gamma M' ≤ CongruenceSubgroup.Gamma M := by
  intro δ hδ
  rw [CongruenceSubgroup.Gamma_mem] at hδ ⊢
  have key : ∀ x : ℤ, ((x : ZMod M) = ZMod.castHom h (ZMod M) (x : ZMod M')) := fun x => by
    rw [map_intCast]
  obtain ⟨h1, h2, h3, h4⟩ := hδ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [key, h1, map_one]
  · rw [key, h2, map_zero]
  · rw [key, h3, map_zero]
  · rw [key, h4, map_one]

/- English proof (translation)
Introduce `N l R _ Φ hN hl _ hinv`. Take `⟨hmul, hone, -, -, -, -, -⟩` from `GlobalTheory.T.twoVarPolySubstMatrix_basic_laws R`. Set `H : ℕ → Subgroup SL(2, ℤ)` to `fun M => { carrier := {γ | ∀ δ ∈ CongruenceSubgroup.Gamma M, slP (γ : Matrix (Fin 2) (Fin 2) ℤ) (Φ (γ * δ * γ⁻¹)) = Φ δ} mul_mem' := by`. Introduce `a b ha hb δ hδ`. Establish `hn : b * δ * b⁻¹ ∈ CongruenceSubgroup.Gamma M` using `(CongruenceSubgroup.Gamma_normal M).conj_mem δ hδ b`.

Establish `e : a * b * δ * (a * b)⁻¹ = a * (b * δ * b⁻¹) * a⁻¹` using `by group`. Use `show slP ((a * b : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (Φ (a * b * δ * (a * b)⁻¹)) = Φ δ`. Rewrite using `[e, Matrix.SpecialLinearGroup.coe_mul, hmul, ha _ hn, hb _ hδ]`. Use the proof step `one_mem' := by`. Introduce `δ _`.

Simplify using `only [one_mul, inv_one, mul_one, Matrix.SpecialLinearGroup.coe_one, hone]`. Use the proof step `inv_mem' := by`. Introduce `a ha δ hδ`. Establish `hn : a⁻¹ * δ * a⁻¹⁻¹ ∈ CongruenceSubgroup.Gamma M` using `(CongruenceSubgroup.Gamma_normal M).conj_mem δ hδ a⁻¹`. Establish `h1` using `ha _ hn`.

Establish `e : a * (a⁻¹ * δ * a⁻¹⁻¹) * a⁻¹ = δ` using `by group`. Rewrite `h1` using `[e]`. Use `show slP ((a⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (Φ (a⁻¹ * δ * a⁻¹⁻¹)) = Φ δ`. Rewrite using `[← h1, ← hmul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, hone] }`. Establish `Hmono : ∀ {M M' : ℕ}, M ∣ M' → H M ≤ H M'`.

Introduce `M M' hd γ hγ δ hδ`. Conclude with `hγ δ (gamma_le_of_dvd hd hδ)`. Use `haveI : NeZero N := ⟨hN.ne'⟩`. Use `haveI : NeZero l := ⟨hl.ne'⟩`. Use `haveI : Group.FG SL(2, ℤ) := by`.

Rewrite using `[Group.fg_iff]`. Conclude with `⟨{ModularGroup.S, ModularGroup.T}, SpecialLinearGroup.SL2Z_generators, Set.toFinite _⟩`. Use `haveI : (Gam N l).FiniteIndex := by unfold Gam; infer_instance`. Use `haveI : Group.FG (Gam N l) := Subgroup.fg_of_index_ne_zero _`. Take `⟨S, hS⟩` from `(Group.fg_def).1 this`.

Use `choose Mf hMf hMeq using fun s : Gam N l => hinv s.1 s.2`. Set `M` to `∏ s ∈ S, Mf s`. Establish `hMpos : 0 < M` using `Finset.prod_pos fun s _ => hMf s`. Use `⟨M, hMpos, ?_⟩` and prove the remaining obligations. Establish `hle : Subgroup.closure (S : Set (Gam N l)) ≤ (H M).comap (Gam N l).subtype`.

Rewrite using `[Subgroup.closure_le]`. Introduce `s hs`. Establish `hd : Mf s ∣ M` using `Finset.dvd_prod_of_mem _ hs`. Apply `Hmono hd` to reduce the goal to its premises. Introduce `δ hδ`.

Conclude with `hMeq s δ hδ`. Introduce `γ hγ δ hδ`. Establish `: (⟨γ, hγ⟩ : Gam N l) ∈ Subgroup.closure (S : Set (Gam N l))` using `by rw [hS]; trivial`. Conclude with `hle this δ hδ`.
-/
theorem unif_level : ∀ (N l : ℕ) (R : Type) [CommRing R] (Φ : SL(2, ℤ) → MvPolynomial (Fin 2) R), 0 < N → 0 < l →
    (∃ M : ℕ, 0 < M ∧ ∀ δ ∈ CongruenceSubgroup.Gamma M, ∀ δ' ∈ CongruenceSubgroup.Gamma M, Φ (δ * δ') = Φ δ + Φ δ') →
    (∀ γ ∈ Gam N l, Near (fun δ => slP (γ : Matrix (Fin 2) (Fin 2) ℤ) (Φ (γ * δ * γ⁻¹))) Φ) →
    ∃ M : ℕ, 0 < M ∧ ∀ γ ∈ Gam N l, ∀ δ ∈ CongruenceSubgroup.Gamma M,
      slP (γ : Matrix (Fin 2) (Fin 2) ℤ) (Φ (γ * δ * γ⁻¹)) = Φ δ := by
  intro N l R _ Φ hN hl _ hinv
  obtain ⟨hmul, hone, -, -, -, -, -⟩ := GlobalTheory.T.twoVarPolySubstMatrix_basic_laws R

  let H : ℕ → Subgroup SL(2, ℤ) := fun M =>
    { carrier := {γ | ∀ δ ∈ CongruenceSubgroup.Gamma M,
        slP (γ : Matrix (Fin 2) (Fin 2) ℤ) (Φ (γ * δ * γ⁻¹)) = Φ δ}
      mul_mem' := by
        intro a b ha hb δ hδ
        have hn : b * δ * b⁻¹ ∈ CongruenceSubgroup.Gamma M :=
          (CongruenceSubgroup.Gamma_normal M).conj_mem δ hδ b
        have e : a * b * δ * (a * b)⁻¹ = a * (b * δ * b⁻¹) * a⁻¹ := by group
        show slP ((a * b : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (Φ (a * b * δ * (a * b)⁻¹)) = Φ δ
        rw [e, Matrix.SpecialLinearGroup.coe_mul, hmul, ha _ hn, hb _ hδ]
      one_mem' := by
        intro δ _
        simp only [one_mul, inv_one, mul_one, Matrix.SpecialLinearGroup.coe_one, hone]
      inv_mem' := by
        intro a ha δ hδ
        have hn : a⁻¹ * δ * a⁻¹⁻¹ ∈ CongruenceSubgroup.Gamma M :=
          (CongruenceSubgroup.Gamma_normal M).conj_mem δ hδ a⁻¹
        have h1 := ha _ hn
        have e : a * (a⁻¹ * δ * a⁻¹⁻¹) * a⁻¹ = δ := by group
        rw [e] at h1
        show slP ((a⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (Φ (a⁻¹ * δ * a⁻¹⁻¹)) = Φ δ
        rw [← h1, ← hmul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
          Matrix.SpecialLinearGroup.coe_one, hone] }
  have Hmono : ∀ {M M' : ℕ}, M ∣ M' → H M ≤ H M' := by
    intro M M' hd γ hγ δ hδ
    exact hγ δ (gamma_le_of_dvd hd hδ)
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero l := ⟨hl.ne'⟩
  haveI : Group.FG SL(2, ℤ) := by
    rw [Group.fg_iff]
    exact ⟨{ModularGroup.S, ModularGroup.T}, SpecialLinearGroup.SL2Z_generators, Set.toFinite _⟩
  haveI : (Gam N l).FiniteIndex := by unfold Gam; infer_instance
  haveI : Group.FG (Gam N l) := Subgroup.fg_of_index_ne_zero _
  obtain ⟨S, hS⟩ := (Group.fg_def).1 this
  choose Mf hMf hMeq using fun s : Gam N l => hinv s.1 s.2
  let M := ∏ s ∈ S, Mf s
  have hMpos : 0 < M := Finset.prod_pos fun s _ => hMf s
  refine ⟨M, hMpos, ?_⟩
  have hle : Subgroup.closure (S : Set (Gam N l)) ≤ (H M).comap (Gam N l).subtype := by
    rw [Subgroup.closure_le]
    intro s hs
    have hd : Mf s ∣ M := Finset.dvd_prod_of_mem _ hs
    apply Hmono hd
    intro δ hδ
    exact hMeq s δ hδ
  intro γ hγ δ hδ
  have : (⟨γ, hγ⟩ : Gam N l) ∈ Subgroup.closure (S : Set (Gam N l)) := by rw [hS]; trivial
  exact hle this δ hδ

end GlobalTheory.KZ.H3
