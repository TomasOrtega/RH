import Mathlib
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds

open Finset
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.ChainHighest

open CompanionTheory.D.DSIC
open Formalism.REAL (KHighest IsWeight)
open PI.UpqRep (lowK)

/- English proof (translation)
Introduce `a b c d hab hcd`. Use `congrArg f (h a b c d hab hcd)` as an intermediate fact. Simplify using `only [map_sub, map_mul] at this`. Rewrite using `[this]`. Apply the tactic sequence `congr 1 <;> split_ifs <;> simp`.
-/
theorem kRel_map {n : ℕ} {A B : Type} [Ring A] [Ring B] (ε : Fin n → Bool) (f : A →+* B)
    (F : Fin n → Fin n → A) (h : KRel ε F) : KRel ε (fun a b => f (F a b)) := by
  intro a b c d hab hcd
  have := congrArg f (h a b c d hab hcd)
  simp only [map_sub, map_mul] at this
  rw [this]
  congr 1 <;> split_ifs <;> simp

/- English proof (translation)
Unfold `Fdual`. Rewrite using `[LinearMap.sub_apply, Pi.sub_apply, lift_apply, hg]`. Use `congr 1`. Distinguish the cases in `h : B = A`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[h]`. Rewrite using `[Finset.sum_eq_single A]`. Simplify using the standard rewrite rules. Introduce `C _ hC`.

Simplify using `[hC]`. Simplify using the standard rewrite rules.
-/
theorem fdual_single {n : ℕ} {ε : Fin n → Bool} {U : Type} [AddCommGroup U] [Module ℂ U]
    (EU : Fin n → Fin n → Module.End ℂ U) (g : Fin n → Fin n → Finset (NC ε) → Finset (NC ε) → ℝ)
    (hg : ∀ (c d : Fin n) (x : Ch ε U) (A : Finset (NC ε)), Gop ε c d x A = ∑ B, (g c d A B : ℂ) • x B)
    (a b : Fin n) (A B : Finset (NC ε)) (u : U) :
    Fdual ε EU a b (Pi.single A u) B =
      (Pi.single A (EU a b u) : Ch ε U) B - (g b a B A : ℂ) • u := by
  unfold Fdual
  rw [LinearMap.sub_apply, Pi.sub_apply, lift_apply, hg]
  congr 1
  · by_cases h : B = A
    · subst h; simp
    · simp [h]
  · rw [Finset.sum_eq_single A]
    · simp
    · intro C _ hC; simp [hC]
    · simp

/- English proof (translation)
Introduce `hF hG hγ hK hM n ε lam V _ _ E v S hlam hE hEu hv hS hSt hvS`. Take `⟨γ, hγ1, hγ2⟩` from `hγ n ε lam hlam`. Take `⟨U, _, _, _, EU, u, hU, hUu, hu0, hu⟩` from `hK n ε γ hγ2`. Take `⟨g, hg, hgs, hgc, hgd, hgl⟩` from `hG n ε`. Set `T : Type` to `PiLp 2 (fun _ : Finset (NC ε) => U)`.

Set `e : Ch ε U ≃ₗ[ℂ] T` to `(WithLp.linearEquiv 2 ℂ (Finset (NC ε) → U)).symm`. Establish `he : ∀ (x : Ch ε U) A, (e x).ofLp A = x A` using `fun _ _ => rfl`. Set `ET : Fin n → Fin n → Module.End ℂ T` to `fun a b => e.conjRingEquiv.toRingHom (Fdual ε EU a b)`. Establish `hET : ∀ a b x, ET a b (e x) = e (Fdual ε EU a b x)`. Introduce `a b x`.

Both sides reduce to the same expression. Establish `hTrel : KRel ε ET` using `kRel_map ε _ _ (hF n ε U EU hU).2`. Establish `hTu : KUnit ε ET`. Introduce `a b hab x y`. Take `⟨x, rfl⟩` from `e.surjective x`.

Take `⟨y, rfl⟩` from `e.surjective y`. Rewrite using `[hET, hET, PiLp.inner_apply, PiLp.inner_apply]`. Simplify using `only [he, Fdual, LinearMap.sub_apply, Pi.sub_apply, lift_apply, hg, inner_sub_left, inner_sub_right, Finset.sum_sub_distrib, sum_inner, inner_sum, inner_smul_left, inner_smul_right, Complex.conj_ofReal]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun A _ => hUu a b hab _ _`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun B _ => ?_` and prove the remaining obligations. Rewrite using `[hgs b a B A]`. Establish `ht0 : e (Pi.single (A1 ε) u) ≠ 0`. Introduce `h`.

Use `he (Pi.single (A1 ε) u) (A1 ε)` as an intermediate fact. Rewrite `this` using `[h]`. Apply `hu0` to reduce the goal to its premises. Simplify using `using this.symm`. Establish `ht : KHighest ε ET (lowK ε lam) (e (Pi.single (A1 ε) u))`.

Prove the components needed by the constructor for the conclusion. Introduce `a`. Rewrite using `[hET, ← map_smul]`. Use `congr 1`. Use function extensionality and compare the values at `B`.

Rewrite using `[fdual_single EU g (hg U), hu.1 a, hgd]`. Distinguish the cases in `h : B = A1 ε`. Substitute `h` using the available equality. Establish `h1` using `hγ1 a`. Simplify using `only [gam, Pi.add_apply] at h1`.

Simplify using `only [Pi.single_eq_same, if_true, Pi.smul_apply, ← sub_smul, ← h1]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using `[h]`.

Introduce `a b hab hε`. Rewrite using `[hET, map_eq_zero_iff _ e.injective]`. Use function extensionality and compare the values at `B`. Rewrite using `[fdual_single EU g (hg U), hu.2 a b hab hε, hgl b a B hab]`. Simplify using the standard rewrite rules.

Take `⟨φ, hφ1, hφ2⟩` from `hM n ε T V ET E (lowK ε lam) _ v S hTrel hTu hE hEu ht0 ht hv hS hSt hvS`. Set `c : Ch ε V` to `fun A => if A.card = (A1 ε).card then φ (e (Pi.single A u)) else 0`. Establish `key : ∀ a b, ε a = ε b → ∀ A, Fop ε E a b c A = if A.card = (A1 ε).card then φ (e (Pi.single A (EU a b u))) else 0`. Introduce `a b hab A`. Unfold `Fop`.

Rewrite using `[LinearMap.add_apply, Pi.add_apply, lift_apply, hg]`. Distinguish the cases in `hA : A.card = (A1 ε).card`. Establish `h1 : Fdual ε EU a b (Pi.single A u) = Pi.single A (EU a b u) - ∑ B, (g a b A B : ℂ) • (Pi.single B u : Ch ε U)`. Use function extensionality and compare the values at `B`. Rewrite using `[fdual_single EU g (hg U), Pi.sub_apply, Finset.sum_apply, Finset.sum_eq_single B, hgs b a B A]`.

Simplify using the standard rewrite rules. Introduce `C _ hC`. Simplify using `[hC.symm]`. Simplify using the standard rewrite rules. Establish `h2 : ∀ B, (g a b A B : ℂ) • c B = (g a b A B : ℂ) • φ (e (Pi.single B u))`.

Introduce `B`. Distinguish the cases in `h0 : g a b A B = 0`. Simplify using `[h0]`. Use `(hgc a b A B h0).1` as an intermediate fact. Simplify using `only [c, ← this, hA, if_true]`.

Simplify using `only [h2]`. Simplify using `only [c, hA, if_true]`. Rewrite using `[← hφ2 a b hab, hET, h1]`. Simplify using `only [map_sub, map_sum, map_smul]`. Normalize the expressions using the abelian group laws.

Establish `h2 : ∀ B, (g a b A B : ℂ) • c B = 0`. Introduce `B`. Distinguish the cases in `h0 : g a b A B = 0`. Simplify using `[h0]`. Use `(hgc a b A B h0).1` as an intermediate fact.

Simplify using `only [c, ← this, hA, if_false, smul_zero]`. Simplify using `only [h2]`. Simplify using `[c, hA]`. Use `⟨c, fun A hA => by simp [c, hA], ⟨fun a => ?_, fun a b hab hε => ?_⟩, by simp [c, hφ1]⟩` and prove the remaining obligations. Use function extensionality and compare the values at `A`.

Rewrite using `[key a a rfl, hu.1 a, Pi.smul_apply, hγ1 a]`. Distinguish the cases in `hA : A.card = (A1 ε).card`. Simplify using `only [c, hA, if_true]`. Rewrite using `[Pi.single_smul, map_smul, map_smul]`. Simplify using `[c, hA]`.

Use function extensionality and compare the values at `A`. Rewrite using `[key a b hε, hu.2 a b hab hε]`. Simplify using the standard rewrite rules.
-/
theorem aux₃ : FRel → GFacts → GamDom → KHWExists → HWMap → PRV := by
  intro hF hG hγ hK hM n ε lam V _ _ E v S hlam hE hEu hv hS hSt hvS
  obtain ⟨γ, hγ1, hγ2⟩ := hγ n ε lam hlam
  obtain ⟨U, _, _, _, EU, u, hU, hUu, hu0, hu⟩ := hK n ε γ hγ2
  obtain ⟨g, hg, hgs, hgc, hgd, hgl⟩ := hG n ε
  let T : Type := PiLp 2 (fun _ : Finset (NC ε) => U)
  let e : Ch ε U ≃ₗ[ℂ] T := (WithLp.linearEquiv 2 ℂ (Finset (NC ε) → U)).symm
  have he : ∀ (x : Ch ε U) A, (e x).ofLp A = x A := fun _ _ => rfl
  let ET : Fin n → Fin n → Module.End ℂ T := fun a b => e.conjRingEquiv.toRingHom (Fdual ε EU a b)
  have hET : ∀ a b x, ET a b (e x) = e (Fdual ε EU a b x) := by
    intro a b x
    rfl
  have hTrel : KRel ε ET := kRel_map ε _ _ (hF n ε U EU hU).2
  have hTu : KUnit ε ET := by
    intro a b hab x y
    obtain ⟨x, rfl⟩ := e.surjective x
    obtain ⟨y, rfl⟩ := e.surjective y
    rw [hET, hET, PiLp.inner_apply, PiLp.inner_apply]
    simp only [he, Fdual, LinearMap.sub_apply, Pi.sub_apply, lift_apply, hg, inner_sub_left,
      inner_sub_right, Finset.sum_sub_distrib, sum_inner, inner_sum, inner_smul_left,
      inner_smul_right, Complex.conj_ofReal]
    congr 1
    · exact Finset.sum_congr rfl fun A _ => hUu a b hab _ _
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun B _ => ?_
      rw [hgs b a B A]
  have ht0 : e (Pi.single (A1 ε) u) ≠ 0 := by
    intro h
    have := he (Pi.single (A1 ε) u) (A1 ε)
    rw [h] at this
    apply hu0
    simpa using this.symm
  have ht : KHighest ε ET (lowK ε lam) (e (Pi.single (A1 ε) u)) := by
    constructor
    · intro a
      rw [hET, ← map_smul]
      congr 1
      funext B
      rw [fdual_single EU g (hg U), hu.1 a, hgd]
      by_cases h : B = A1 ε
      · subst h
        have h1 := hγ1 a
        simp only [gam, Pi.add_apply] at h1
        simp only [Pi.single_eq_same, if_true, Pi.smul_apply, ← sub_smul, ← h1]
        congr 1
        push_cast
        ring
      · simp [h]
    · intro a b hab hε
      rw [hET, map_eq_zero_iff _ e.injective]
      funext B
      rw [fdual_single EU g (hg U), hu.2 a b hab hε, hgl b a B hab]
      simp
  obtain ⟨φ, hφ1, hφ2⟩ := hM n ε T V ET E (lowK ε lam) _ v S hTrel hTu hE hEu ht0 ht hv hS hSt hvS
  let c : Ch ε V := fun A => if A.card = (A1 ε).card then φ (e (Pi.single A u)) else 0
  have key : ∀ a b, ε a = ε b → ∀ A, Fop ε E a b c A =
      if A.card = (A1 ε).card then φ (e (Pi.single A (EU a b u))) else 0 := by
    intro a b hab A
    unfold Fop
    rw [LinearMap.add_apply, Pi.add_apply, lift_apply, hg]
    by_cases hA : A.card = (A1 ε).card
    · have h1 : Fdual ε EU a b (Pi.single A u) =
          Pi.single A (EU a b u) - ∑ B, (g a b A B : ℂ) • (Pi.single B u : Ch ε U) := by
        funext B
        rw [fdual_single EU g (hg U), Pi.sub_apply, Finset.sum_apply, Finset.sum_eq_single B, hgs b a B A]
        · simp
        · intro C _ hC; simp [hC.symm]
        · simp
      have h2 : ∀ B, (g a b A B : ℂ) • c B = (g a b A B : ℂ) • φ (e (Pi.single B u)) := by
        intro B
        by_cases h0 : g a b A B = 0
        · simp [h0]
        · have := (hgc a b A B h0).1
          simp only [c, ← this, hA, if_true]
      simp only [h2]
      simp only [c, hA, if_true]
      rw [← hφ2 a b hab, hET, h1]
      simp only [map_sub, map_sum, map_smul]
      abel
    · have h2 : ∀ B, (g a b A B : ℂ) • c B = 0 := by
        intro B
        by_cases h0 : g a b A B = 0
        · simp [h0]
        · have := (hgc a b A B h0).1
          simp only [c, ← this, hA, if_false, smul_zero]
      simp only [h2]
      simp [c, hA]
  refine ⟨c, fun A hA => by simp [c, hA], ⟨fun a => ?_, fun a b hab hε => ?_⟩, by simp [c, hφ1]⟩
  · funext A
    rw [key a a rfl, hu.1 a, Pi.smul_apply, hγ1 a]
    by_cases hA : A.card = (A1 ε).card
    · simp only [c, hA, if_true]
      rw [Pi.single_smul, map_smul, map_smul]
    · simp [c, hA]
  · funext A
    rw [key a b hε, hu.2 a b hab hε]
    simp

end GlobalTheory.CompanionTheory.ChainHighest
