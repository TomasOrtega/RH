import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.AffineCharacterGenerators.Generators
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.LiftSingleAlt

open MvPolynomial Filter Topology PositivityTheory.Rg.Fx

namespace UpperTheory.ConvolutionTheory.FX

/- English proof (translation)
Simplify using `[PositivityTheory.Rg.Fx.lift]`.
-/
private theorem kill_lift_single {ι A : Type} [CommRing A] [Algebra ℂ A] (x : ι → A)
    (τ : Multiplicative (ι → ℝ) →* A) (v : ι → ℝ) (p : MvPolynomial ι ℂ) :
    PositivityTheory.Rg.Fx.lift x τ (AddMonoidAlgebra.single v p) = aeval x p * τ (Multiplicative.ofAdd v) := by
  simp [PositivityTheory.Rg.Fx.lift]

/- English proof (translation)
Rewrite using `[ev, kill_lift_single]`. Simplify using the standard rewrite rules.
-/
private theorem kill_ev_X {ι : Type} [Fintype ι] (Λ : ι → ℂ) (i : ι) :
    ev Λ (AddMonoidAlgebra.single 0 (X i)) = Λ i := by
  rw [ev, kill_lift_single]
  simp

/- English proof (translation)
Establish `hx : ∀ p : MvPolynomial ι ℂ, aeval (fun i : ι => (AddMonoidAlgebra.single 0 (C ((0 : ι → ℂ) i) + lin ((1 : Matrix ι ι ℝ) i)) : EP ι)) p = AddMonoidAlgebra.single 0 p`. Introduce `p`. Establish `h1 : ∀ i : ι, C ((0 : ι → ℂ) i) + lin ((1 : Matrix ι ι ℝ) i) = (X i : MvPolynomial ι ℂ)`. Introduce `i`. Simplify using `[lin, Matrix.one_apply, apply_ite]`.

Simplify using `only [h1]`. Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a => simp`. Consider the case `add p q hp hq => rw [map_add, hp, hq, AddMonoidAlgebra.single_add]`. Consider the case `mul_X p i hp => rw [map_mul, hp, aeval_X, AddMonoidAlgebra.single_mul_single, add_zero]`.

Proceed by induction on `f using AddMonoidAlgebra.induction_linear with`. Consider the case `zero => simp`. Consider the case `add f g hf hg => rw [map_add, hf, hg]`. Consider the case `single v p`. Rewrite using `[aff, kill_lift_single, hx]`.

Simplify using `[affChar, expChar, AddMonoidAlgebra.single_mul_single]`.
-/
private theorem kill_aff_id {ι : Type} [Fintype ι] [DecidableEq ι] (f : EP ι) :
    aff (0 : ι → ℂ) (1 : Matrix ι ι ℝ) f = f := by
  have hx : ∀ p : MvPolynomial ι ℂ,
      aeval (fun i : ι => (AddMonoidAlgebra.single 0
        (C ((0 : ι → ℂ) i) + lin ((1 : Matrix ι ι ℝ) i)) : EP ι)) p = AddMonoidAlgebra.single 0 p := by
    intro p
    have h1 : ∀ i : ι, C ((0 : ι → ℂ) i) + lin ((1 : Matrix ι ι ℝ) i) = (X i : MvPolynomial ι ℂ) := by
      intro i
      simp [lin, Matrix.one_apply, apply_ite]
    simp only [h1]
    induction p using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => rw [map_add, hp, hq, AddMonoidAlgebra.single_add]
    | mul_X p i hp => rw [map_mul, hp, aeval_X, AddMonoidAlgebra.single_mul_single, add_zero]
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, hf, hg]
  | single v p =>
    rw [aff, kill_lift_single, hx]
    simp [affChar, expChar, AddMonoidAlgebra.single_mul_single]

/- English proof (translation)
Establish `: (Matrix.of fun i j : ι => if id i = j then (1 : ℝ) else 0) = 1`. Use extensionality with `i j`. Simplify using `[Matrix.one_apply]`. Rewrite using `[ren, this, kill_aff_id]`.
-/
private theorem kill_ren_id {ι : Type} [Fintype ι] [DecidableEq ι] (f : EP ι) :
    ren (id : ι → ι) f = f := by
  have : (Matrix.of fun i j : ι => if id i = j then (1 : ℝ) else 0) = 1 := by
    ext i j
    simp [Matrix.one_apply]
  rw [ren, this, kill_aff_id]

/- English proof (translation)
Rewrite using `[ren, ren, ren, (subst ι ι _ _ f).2]`. Use `congr 2`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Use extensionality with `i j`.

Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single (δ i)]`. Simplify using the standard rewrite rules. Introduce `l _ hl`. Simplify using `[Ne.symm hl]`. Simplify using the standard rewrite rules.
-/
private theorem kill_ren_ren {ι : Type} [Fintype ι] [DecidableEq ι] (δ δ' : ι → ι) (f : EP ι) :
    ren δ' (ren δ f) = ren (δ' ∘ δ) f := by
  rw [ren, ren, ren, (subst ι ι _ _ f).2]
  congr 2
  · funext i
    simp
  · ext i j
    rw [Matrix.mul_apply, Finset.sum_eq_single (δ i)]
    · simp
    · intro l _ hl
      simp [Ne.symm hl]
    · simp

/- English proof (translation)
Rewrite using `[ren, (subst ι ι _ _ f).1]`. Use `congr 2`. Use function extensionality and compare the values at `i`. Simplify using `[apply_ite]`.
-/
private theorem kill_ev_ren {ι : Type} [Fintype ι] [DecidableEq ι] (δ : ι → ι) (Λ : ι → ℂ) (f : EP ι) :
    ev Λ (ren δ f) = ev (Λ ∘ δ) f := by
  rw [ren, (subst ι ι _ _ f).1]
  congr 2
  funext i
  simp [apply_ite]

/- English proof (translation)
Establish `: (ev Λ).comp (ren δ) = ev (Λ ∘ δ)` using `RingHom.ext (kill_ev_ren δ Λ)`. Rewrite using `[evK, evK, coe_eval₂Hom, coe_eval₂Hom, eval₂_map, this]`.
-/
private theorem kill_evK_ren {ι κ : Type} [Fintype ι] [DecidableEq ι] (δ : ι → ι) (Λ : ι → ℂ) (h : κ → ℂ)
    (G : KF ι κ) : evK Λ h (map (ren δ) G) = evK (Λ ∘ δ) h G := by
  have : (ev Λ).comp (ren δ) = ev (Λ ∘ δ) := RingHom.ext (kill_ev_ren δ Λ)
  rw [evK, evK, coe_eval₂Hom, coe_eval₂Hom, eval₂_map, this]

/- English proof (translation)
Set `Λ₁ : Fin b.r → ℂ` to `fun j => - ∑ i, (b.pr j i : ℂ) * b.Λ i`. Set `lam : Fin b.r → ℂ` to `fun j => Λ₁ j + ∑ i, (b.pr j i : ℂ) * Λ i`. Establish `hret : ∀ y : EP (Fin b.r), aff b.Λ b.emb (aff Λ₁ b.pr y) = y`. Introduce `y`. Rewrite using `[(subst _ _ _ _ y).2, b.pr_emb]`.

Establish `: (fun j => Λ₁ j + ∑ i, (b.pr j i : ℂ) * b.Λ i) = 0`. Use function extensionality and compare the values at `j`. Simplify using `[Λ₁]`. Rewrite using `[this, kill_aff_id]`. Establish `key : ∀ F : KF ι κ, evK Λ h F = ev lam (b.sub F)`.

Introduce `F`. Establish `h1 : F - C (aff Λ₁ b.pr (b.sub F)) ∈ RingHom.ker b.sub`. Rewrite using `[RingHom.mem_ker, map_sub, sub_eq_zero]`. Generalize the expression as in `b.sub F = y`. Rewrite using `[Fam.sub, eval₂Hom_C, hret]`.

Establish `h2` using `H h1`. Rewrite `h2` using `[RingHom.mem_ker, map_sub, sub_eq_zero]`. Rewrite using `[h2, evK, eval₂Hom_C, (subst _ _ _ _ _).1]`. Use `⟨lam, fun i => ?_, fun k => ?_⟩` and prove the remaining obligations. Use `key (C (AddMonoidAlgebra.single 0 (X i)))` as an intermediate fact.

Rewrite `this` using `[evK, Fam.sub, eval₂Hom_C, eval₂Hom_C, (subst _ _ _ _ _).1, kill_ev_X, kill_ev_X]`. Conclude with `this`. Use `key (X k)` as an intermediate fact. Rewrite `this` using `[evK, Fam.sub, eval₂Hom_X', eval₂Hom_X']`. Conclude with `this`.
-/
private theorem kill_mem_of_ker {ι κ : Type} [Fintype ι] (b : Fam ι κ) (Λ : ι → ℂ) (h : κ → ℂ)
    (H : RingHom.ker b.sub ≤ RingHom.ker (evK Λ h)) : b.Mem Λ h := by
  classical
  let Λ₁ : Fin b.r → ℂ := fun j => - ∑ i, (b.pr j i : ℂ) * b.Λ i
  let lam : Fin b.r → ℂ := fun j => Λ₁ j + ∑ i, (b.pr j i : ℂ) * Λ i
  have hret : ∀ y : EP (Fin b.r), aff b.Λ b.emb (aff Λ₁ b.pr y) = y := by
    intro y
    rw [(subst _ _ _ _ y).2, b.pr_emb]
    have : (fun j => Λ₁ j + ∑ i, (b.pr j i : ℂ) * b.Λ i) = 0 := by
      funext j
      simp [Λ₁]
    rw [this, kill_aff_id]
  have key : ∀ F : KF ι κ, evK Λ h F = ev lam (b.sub F) := by
    intro F
    have h1 : F - C (aff Λ₁ b.pr (b.sub F)) ∈ RingHom.ker b.sub := by
      rw [RingHom.mem_ker, map_sub, sub_eq_zero]
      generalize b.sub F = y
      rw [Fam.sub, eval₂Hom_C, hret]
    have h2 := H h1
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at h2
    rw [h2, evK, eval₂Hom_C, (subst _ _ _ _ _).1]
  refine ⟨lam, fun i => ?_, fun k => ?_⟩
  · have := key (C (AddMonoidAlgebra.single 0 (X i)))
    rw [evK, Fam.sub, eval₂Hom_C, eval₂Hom_C, (subst _ _ _ _ _).1, kill_ev_X, kill_ev_X] at this
    exact this
  · have := key (X k)
    rw [evK, Fam.sub, eval₂Hom_X', eval₂Hom_X'] at this
    exact this

end UpperTheory.ConvolutionTheory.FX

open UpperTheory.ConvolutionTheory.FX in
/- English proof (translation)
Introduce `ι κ B _ _ _ W b Λ₀ h₀ hW`. Use `haveI : Fintype W := Fintype.ofFinite W`. Establish `hG : ∀ i, ∃ G : KF ι κ, (b i).sub G = 0 ∧ ∀ w : W, evK (Λ₀ ∘ (w : Equiv.Perm ι)) h₀ G ≠ 0`. Introduce `i`. Assume the negation of the conclusion as `hc`.

Use `push Not at hc`. Establish `hsub : ((RingHom.ker (b i).sub : Ideal (KF ι κ)) : Set (KF ι κ)) ⊆ ⋃ w ∈ (↑(Finset.univ : Finset W) : Set W), ((RingHom.ker (evK (Λ₀ ∘ (w : Equiv.Perm ι)) h₀) : Ideal (KF ι κ)) : Set (KF ι κ))`. Introduce `G hG`. Take `⟨w, hw⟩` from `hc G hG`. Conclude with `Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_univ w)) hw`.

Take `⟨w, -, hw⟩` from `(Ideal.subset_union_prime (1 : W) 1 (fun w _ _ _ => RingHom.ker_isPrime _)).1 hsub`. Conclude with `hW w w.2 i (kill_mem_of_ker _ _ _ hw)`. Use `choose G hG0 hG1 using hG`. Use `⟨∏ i, ∏ w : W, map (ren ((w : Equiv.Perm ι) : ι → ι)) (G i), ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `w' hw'`.

Rewrite using `[map_prod]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_prod]`. Use `Fintype.prod_equiv (Equiv.mulLeft (⟨w', hw'⟩ : W)) _ _ fun w => ?_` and prove the remaining obligations. Establish `hc : (ren (w' : ι → ι)).comp (ren ((w : Equiv.Perm ι) : ι → ι)) = ren (((w' * (w : Equiv.Perm ι) : Equiv.Perm ι)) : ι → ι)`.

Rewrite using `[Equiv.Perm.coe_mul]`. Conclude with `RingHom.ext fun f => by rw [RingHom.comp_apply, kill_ren_ren]`. Rewrite using `[MvPolynomial.map_map, hc, Equiv.coe_mulLeft, Subgroup.coe_mul]`. Introduce `i`. Rewrite using `[map_prod]`.

Use `Finset.prod_eq_zero (Finset.mem_univ i) ?_` and prove the remaining obligations. Rewrite using `[map_prod]`. Use `Finset.prod_eq_zero (Finset.mem_univ (1 : W)) ?_` and prove the remaining obligations. Establish `: ren (((1 : W) : Equiv.Perm ι) : ι → ι) = RingHom.id _`. Rewrite using `[Subgroup.coe_one, Equiv.Perm.coe_one]`.

Conclude with `RingHom.ext fun f => by rw [kill_ren_id, RingHom.id_apply]`. Rewrite using `[this, MvPolynomial.map_id, hG0]`. Rewrite using `[map_prod]`. Use `Finset.prod_ne_zero_iff.2 fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_prod]`.

Use `Finset.prod_ne_zero_iff.2 fun w _ => ?_` and prove the remaining obligations. Rewrite using `[kill_evK_ren]`. Conclude with `hG1 i w`.
-/
theorem UpperTheory.ConvolutionTheory.FX.killing0 :
    ∀ (ι κ B : Type) [Fintype ι] [DecidableEq ι] [Fintype B] (W : Subgroup (Equiv.Perm ι)) (b : B → Fam ι κ) (Λ₀ : ι → ℂ) (h₀ : κ → ℂ), (∀ w ∈ W, ∀ i, ¬ (b i).Mem (Λ₀ ∘ w) h₀) → ∃ F : KF ι κ, (∀ w ∈ W, map (ren (w : ι → ι)) F = F) ∧ (∀ i, (b i).sub F = 0) ∧ evK Λ₀ h₀ F ≠ 0 := by
  intro ι κ B _ _ _ W b Λ₀ h₀ hW
  classical
  haveI : Fintype W := Fintype.ofFinite W
  have hG : ∀ i, ∃ G : KF ι κ, (b i).sub G = 0 ∧ ∀ w : W, evK (Λ₀ ∘ (w : Equiv.Perm ι)) h₀ G ≠ 0 := by
    intro i
    by_contra hc
    push Not at hc
    have hsub : ((RingHom.ker (b i).sub : Ideal (KF ι κ)) : Set (KF ι κ)) ⊆
        ⋃ w ∈ (↑(Finset.univ : Finset W) : Set W),
          ((RingHom.ker (evK (Λ₀ ∘ (w : Equiv.Perm ι)) h₀) : Ideal (KF ι κ)) : Set (KF ι κ)) := by
      intro G hG
      obtain ⟨w, hw⟩ := hc G hG
      exact Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_univ w)) hw
    obtain ⟨w, -, hw⟩ := (Ideal.subset_union_prime (1 : W) 1
      (fun w _ _ _ => RingHom.ker_isPrime _)).1 hsub
    exact hW w w.2 i (kill_mem_of_ker _ _ _ hw)
  choose G hG0 hG1 using hG
  refine ⟨∏ i, ∏ w : W, map (ren ((w : Equiv.Perm ι) : ι → ι)) (G i), ?_, ?_, ?_⟩
  · intro w' hw'
    rw [map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_prod]
    refine Fintype.prod_equiv (Equiv.mulLeft (⟨w', hw'⟩ : W)) _ _ fun w => ?_
    have hc : (ren (w' : ι → ι)).comp (ren ((w : Equiv.Perm ι) : ι → ι)) =
        ren (((w' * (w : Equiv.Perm ι) : Equiv.Perm ι)) : ι → ι) := by
      rw [Equiv.Perm.coe_mul]
      exact RingHom.ext fun f => by rw [RingHom.comp_apply, kill_ren_ren]
    rw [MvPolynomial.map_map, hc, Equiv.coe_mulLeft, Subgroup.coe_mul]
  · intro i
    rw [map_prod]
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rw [map_prod]
    refine Finset.prod_eq_zero (Finset.mem_univ (1 : W)) ?_
    have : ren (((1 : W) : Equiv.Perm ι) : ι → ι) = RingHom.id _ := by
      rw [Subgroup.coe_one, Equiv.Perm.coe_one]
      exact RingHom.ext fun f => by rw [kill_ren_id, RingHom.id_apply]
    rw [this, MvPolynomial.map_id, hG0]
  · rw [map_prod]
    refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
    rw [map_prod]
    refine Finset.prod_ne_zero_iff.2 fun w _ => ?_
    rw [kill_evK_ren]
    exact hG1 i w
