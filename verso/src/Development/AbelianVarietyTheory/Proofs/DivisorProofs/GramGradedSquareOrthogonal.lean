import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LnStepFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameCombinationCoeffUnique
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj
open GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.LocM.Frm GlobalTheory.HeightParts
open GlobalTheory.GradedNorm GlobalTheory.LieHt
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LieSmooth

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieSmooth.BlockGr

open Matrix
open scoped ComplexOrder

variable {m r : ℕ}

/- English proof (translation)
Simplify using `only [dotProduct, mulVec, Function.comp_apply, submatrix_apply, Pi.star_apply]`. Use `symm`. Use `Fintype.sum_of_injective p hp _ _ (fun a ha => by simp [hv a ha]) fun i => ?_` and prove the remaining obligations. Use `congr 1`. Conclude with `Fintype.sum_of_injective p hp _ _ (fun a ha => by simp [hv a ha]) fun j => rfl`.
-/
theorem quad_sub (M : Matrix (Fin m) (Fin m) ℂ) {p : Fin r → Fin m} (hp : Function.Injective p) (v : Fin m → ℂ)
    (hv : ∀ a ∉ Set.range p, v a = 0) :
    star v ⬝ᵥ M *ᵥ v = star (v ∘ p) ⬝ᵥ M.submatrix p p *ᵥ (v ∘ p) := by
  simp only [dotProduct, mulVec, Function.comp_apply, submatrix_apply, Pi.star_apply]
  symm
  refine Fintype.sum_of_injective p hp _ _ (fun a ha => by simp [hv a ha]) fun i => ?_
  congr 1
  exact Fintype.sum_of_injective p hp _ _ (fun a ha => by simp [hv a ha]) fun j => rfl

/- English proof (translation)
Set `S : Fin m → ℂ` to `fun a => if a ∈ Set.range p then v a else 0`. Set `R : Fin m → ℂ` to `fun a => if a ∈ Set.range p then 0 else v a`. Establish `S1 : ∀ a ∈ Set.range p, S a = v a` using `fun a h => if_pos h`. Establish `S0 : ∀ a ∉ Set.range p, S a = 0` using `fun a h => if_neg h`. Establish `R1 : ∀ a ∉ Set.range p, R a = v a` using `fun a h => if_neg h`.

Establish `R0 : ∀ a ∈ Set.range p, R a = 0` using `fun a h => if_pos h`. Establish `hv : v = S + R` using `funext fun a => by`. Distinguish the cases in `h : a ∈ Set.range p`. Rewrite using `[Pi.add_apply, S1 a h, R0 a h, add_zero]`. Rewrite using `[Pi.add_apply, S0 a h, R1 a h, zero_add]`.

Establish `hSp : S ∘ p = v ∘ p` using `funext fun i => S1 _ ⟨i, rfl⟩`. Establish `c1 : star S ⬝ᵥ M *ᵥ R = 0`. Simplify using `only [dotProduct, mulVec]`. Use `Finset.sum_eq_zero fun a _ => ?_` and prove the remaining obligations. Distinguish the cases in `ha : a ∈ Set.range p`.

Use `mul_eq_zero_of_right _ (Finset.sum_eq_zero fun b _ => ?_)` and prove the remaining obligations. Distinguish the cases in `hb : b ∈ Set.range p`. Rewrite using `[R0 b hb, mul_zero]`. Rewrite using `[(ho a b ha hb).1, zero_mul]`. Rewrite using `[Pi.star_apply, S0 a ha, star_zero, zero_mul]`.

Establish `c2 : star R ⬝ᵥ M *ᵥ S = 0`. Simplify using `only [dotProduct, mulVec]`. Use `Finset.sum_eq_zero fun a _ => ?_` and prove the remaining obligations. Distinguish the cases in `ha : a ∈ Set.range p`. Rewrite using `[Pi.star_apply, R0 a ha, star_zero, zero_mul]`.

Use `mul_eq_zero_of_right _ (Finset.sum_eq_zero fun b _ => ?_)` and prove the remaining obligations. Distinguish the cases in `hb : b ∈ Set.range p`. Rewrite using `[(ho b a hb ha).2, zero_mul]`. Rewrite using `[S0 b hb, mul_zero]`. Establish `e : star v ⬝ᵥ M *ᵥ v = star S ⬝ᵥ M *ᵥ S + star R ⬝ᵥ M *ᵥ R`.

Rewrite using `[hv, star_add, mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, c1, c2]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, ← hSp, ← quad_sub M hp S S0, Complex.add_re]`. Use `hM.re_dotProduct_nonneg R` as an intermediate fact. Simplify using `only [RCLike.re_to_complex] at this`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem quad_sub_le {M : Matrix (Fin m) (Fin m) ℂ} (hM : M.PosSemidef) {p : Fin r → Fin m} (hp : Function.Injective p)
    (ho : ∀ a b, a ∈ Set.range p → b ∉ Set.range p → M a b = 0 ∧ M b a = 0) (v : Fin m → ℂ) :
    (star (v ∘ p) ⬝ᵥ M.submatrix p p *ᵥ (v ∘ p)).re ≤ (star v ⬝ᵥ M *ᵥ v).re := by
  classical
  let S : Fin m → ℂ := fun a => if a ∈ Set.range p then v a else 0
  let R : Fin m → ℂ := fun a => if a ∈ Set.range p then 0 else v a
  have S1 : ∀ a ∈ Set.range p, S a = v a := fun a h => if_pos h
  have S0 : ∀ a ∉ Set.range p, S a = 0 := fun a h => if_neg h
  have R1 : ∀ a ∉ Set.range p, R a = v a := fun a h => if_neg h
  have R0 : ∀ a ∈ Set.range p, R a = 0 := fun a h => if_pos h
  have hv : v = S + R := funext fun a => by
    by_cases h : a ∈ Set.range p
    · rw [Pi.add_apply, S1 a h, R0 a h, add_zero]
    · rw [Pi.add_apply, S0 a h, R1 a h, zero_add]
  have hSp : S ∘ p = v ∘ p := funext fun i => S1 _ ⟨i, rfl⟩
  have c1 : star S ⬝ᵥ M *ᵥ R = 0 := by
    simp only [dotProduct, mulVec]
    refine Finset.sum_eq_zero fun a _ => ?_
    by_cases ha : a ∈ Set.range p
    · refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun b _ => ?_)
      by_cases hb : b ∈ Set.range p
      · rw [R0 b hb, mul_zero]
      · rw [(ho a b ha hb).1, zero_mul]
    · rw [Pi.star_apply, S0 a ha, star_zero, zero_mul]
  have c2 : star R ⬝ᵥ M *ᵥ S = 0 := by
    simp only [dotProduct, mulVec]
    refine Finset.sum_eq_zero fun a _ => ?_
    by_cases ha : a ∈ Set.range p
    · rw [Pi.star_apply, R0 a ha, star_zero, zero_mul]
    · refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun b _ => ?_)
      by_cases hb : b ∈ Set.range p
      · rw [(ho b a hb ha).2, zero_mul]
      · rw [S0 b hb, mul_zero]
  have e : star v ⬝ᵥ M *ᵥ v = star S ⬝ᵥ M *ᵥ S + star R ⬝ᵥ M *ᵥ R := by
    rw [hv, star_add, mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, c1, c2]
    ring
  rw [e, ← hSp, ← quad_sub M hp S S0, Complex.add_re]
  have := hM.re_dotProduct_nonneg R
  simp only [RCLike.re_to_complex] at this
  linarith

end GlobalTheory.LieSmooth.BlockGr

namespace GlobalTheory.LieSmooth.BlockGr

open Matrix
open scoped ComplexOrder

variable {m r : ℕ}

/- English proof (translation)
Establish `hS : (M.submatrix p p).PosDef` using `hM.submatrix hp`. Use `le_antisymm ?_ ?_` and prove the remaining obligations. Take `⟨⟨w, hw1, hw2, hw⟩, -⟩` from `isLeast_grSq hS i`. Rewrite using `[hw]`. Use `(isLeast_grSq hM k).2 ⟨Function.extend p w 0, ?_, fun j hj => ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hk, hp.extend_apply, hw1]`. Distinguish the cases in `h : j ∈ Set.range p`. Take `⟨i', rfl⟩` from `h`. Rewrite using `[hp.extend_apply, hw2 _ (h2 _ hj)]`. Rewrite using `[Function.extend_apply' _ _ _ fun ⟨a, ha⟩ => h ⟨a, ha⟩, Pi.zero_apply]`.

Rewrite using `[quad_sub M hp _ fun a ha => by`. Rewrite using `[Function.extend_apply' _ _ _ fun ⟨b, hb⟩ => ha ⟨b, hb⟩, Pi.zero_apply]]`. Establish `e : Function.extend p w 0 ∘ p = w` using `funext fun a => hp.extend_apply _ _ _`. Rewrite using `[e]`. Take `⟨⟨v, hv1, hv2, hv⟩, -⟩` from `isLeast_grSq hM k`.

Rewrite using `[hv]`. Use `le_trans ((isLeast_grSq hS i).2 ⟨v ∘ p, ?_, fun i' hi' => hv2 _ (h1 _ hi'), rfl⟩) (quad_sub_le hM.posSemidef hp ho v)` and prove the remaining obligations. Rewrite using `[Function.comp_apply, hk, hv1]`.
-/
theorem grSq_block {M : Matrix (Fin m) (Fin m) ℂ} (hM : M.PosDef) {p : Fin r → Fin m} (hp : Function.Injective p)
    (ho : ∀ a b, a ∈ Set.range p → b ∉ Set.range p → M a b = 0 ∧ M b a = 0) {k : Fin m} {i : Fin r} (hk : p i = k)
    (h1 : ∀ i', i < i' → k < p i') (h2 : ∀ i', k < p i' → i < i') :
    grSq M k = grSq (M.submatrix p p) i := by
  have hS : (M.submatrix p p).PosDef := hM.submatrix hp
  refine le_antisymm ?_ ?_
  · obtain ⟨⟨w, hw1, hw2, hw⟩, -⟩ := isLeast_grSq hS i
    rw [hw]
    refine (isLeast_grSq hM k).2 ⟨Function.extend p w 0, ?_, fun j hj => ?_, ?_⟩
    · rw [← hk, hp.extend_apply, hw1]
    · by_cases h : j ∈ Set.range p
      · obtain ⟨i', rfl⟩ := h
        rw [hp.extend_apply, hw2 _ (h2 _ hj)]
      · rw [Function.extend_apply' _ _ _ fun ⟨a, ha⟩ => h ⟨a, ha⟩, Pi.zero_apply]
    · rw [quad_sub M hp _ fun a ha => by
        rw [Function.extend_apply' _ _ _ fun ⟨b, hb⟩ => ha ⟨b, hb⟩, Pi.zero_apply]]
      have e : Function.extend p w 0 ∘ p = w := funext fun a => hp.extend_apply _ _ _
      rw [e]
  · obtain ⟨⟨v, hv1, hv2, hv⟩, -⟩ := isLeast_grSq hM k
    rw [hv]
    refine le_trans ((isLeast_grSq hS i).2 ⟨v ∘ p, ?_, fun i' hi' => hv2 _ (h1 _ hi'), rfl⟩) (quad_sub_le hM.posSemidef hp ho v)
    rw [Function.comp_apply, hk, hv1]

end GlobalTheory.LieSmooth.BlockGr

namespace GlobalTheory.LieSmooth

open Matrix
open scoped ComplexOrder

/- English proof (translation)
Set `eq` to `Equiv.ofBijective _ (GlobalTheory.Proof.frame_combination_coeff_unique.get_bijective Dw)`. Establish `hpw` using `List.pairwise_iff_get.1 (GlobalTheory.Proof.frame_combination_coeff_unique.pairwise_letters Dw)`. Establish `hli : LinearIndependent K (allFr K e)`. Establish `: allFr K e = (Pi.basisFun K (Fin n)) ∘ (fun j => e.symm ((letters Dw).get j))`. Use function extensionality and compare the values at `fun j => (Pi.basisFun_apply K (Fin n) _).symm`.

Rewrite using `[this]`. Conclude with `(Pi.basisFun K (Fin n)).linearIndependent.comp _ (e.symm.injective.comp (GlobalTheory.Proof.frame_combination_coeff_unique.get_bijective Dw).1)`. Establish `hM : (h.gram σ (allFr K e)).PosDef` using `h.posDef σ _ _ hli`. Establish `hz : ∀ a b, ((letters Dw).get a).1 ≠ ((letters Dw).get b).1 → h.gram σ (allFr K e) a b = 0` using `fun a b hab => horth _ _ hab`. It suffices to establish `key : ∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) (k : Fin (letters Dw).length), (letters Dw).get k = ⟨τ, i⟩ → grSq (h.gram σ (allFr K e)) k = grSq (h.gram σ (tauFr K e τ)) i from fun k => key _ _ k rfl`.

Introduce `τ i k hk`. Set `p : Fin (Dw.mult τ) → Fin (letters Dw).length` to `fun i' => eq.symm ⟨τ, i'⟩`. Establish `hg : ∀ i', (letters Dw).get (p i') = ⟨τ, i'⟩` using `fun i' => eq.apply_symm_apply _`. Establish `hp : Function.Injective p` using `fun a b hab => by`. Use `congrArg (fun j => (letters Dw).get j) hab` as an intermediate fact.

Simplify using `only [hg] at this`. Conclude with `eq_of_heq (Sigma.mk.inj this).2`. Establish `hpk : p i = k` using `eq.symm_apply_eq.2 hk.symm`. Establish `hsub : h.gram σ (tauFr K e τ) = (h.gram σ (allFr K e)).submatrix p p`. Use extensionality with `a b`.

Simplify using `only [HermFam.gram, submatrix_apply, of_apply, allFr, tauFr, hg]`. Establish `hout : ∀ b, b ∉ Set.range p → ((letters Dw).get b).1 ≠ τ`. Introduce `b hb hτ`. Break down `hgb : (letters Dw).get b with ⟨τ', j⟩` into its components or cases. Rewrite `hτ` using `[hgb]`.

Substitute `hτ` using the available equality. Conclude with `hb ⟨j, eq.symm_apply_eq.2 hgb.symm⟩`. Establish `ho : ∀ a b, a ∈ Set.range p → b ∉ Set.range p → h.gram σ (allFr K e) a b = 0 ∧ h.gram σ (allFr K e) b a = 0`. Introduce and unpack `_ b ⟨a, rfl⟩ hb`. Establish `h1 : ((letters Dw).get (p a)).1 ≠ ((letters Dw).get b).1` using `by rw [hg]; exact (hout b hb).symm`.

Conclude with `⟨hz _ _ h1, hz _ _ h1.symm⟩`. Rewrite using `[hsub]`. Use `BlockGr.grSq_block hM hp ho hpk (fun i' hi' => ?_) (fun i' hi' => ?_)` and prove the remaining obligations. Assume the negation of the conclusion as `hle`. Establish `hlt : p i' < k` using `lt_of_le_of_ne (not_lt.1 hle) fun h' => hi'.ne (hp (hpk.trans h'.symm))`.

Use `hpw _ _ hlt` as an intermediate fact. Rewrite `this` using `[hg, hk]`. Conclude with `absurd (this rfl) (not_lt.2 hi'.le)`. Use `hpw _ _ hi'` as an intermediate fact. Rewrite `this` using `[hg, hk]`.

Conclude with `this rfl`.
-/
theorem grSq_allFr_tauFr {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {K : Type} [Field K] [NumberField K] {n : ℕ} (e : Fin n ≃ Letter Dw) (h : HermFam K (Fin n → K))
    (σ : K →+* ℂ)
    (horth : ∀ z z' : Letter Dw, z.1 ≠ z'.1 → h.form σ (tauFr K e z.1 z.2) (tauFr K e z'.1 z'.2) = 0) :
    ∀ k : Fin (letters Dw).length,
      grSq (h.gram σ (allFr K e)) k = grSq (h.gram σ (tauFr K e ((letters Dw).get k).1)) ((letters Dw).get k).2 := by
  classical
  let eq := Equiv.ofBijective _ (GlobalTheory.Proof.frame_combination_coeff_unique.get_bijective Dw)
  have hpw := List.pairwise_iff_get.1 (GlobalTheory.Proof.frame_combination_coeff_unique.pairwise_letters Dw)
  have hli : LinearIndependent K (allFr K e) := by
    have : allFr K e = (Pi.basisFun K (Fin n)) ∘ (fun j => e.symm ((letters Dw).get j)) :=
      funext fun j => (Pi.basisFun_apply K (Fin n) _).symm
    rw [this]
    exact (Pi.basisFun K (Fin n)).linearIndependent.comp _ (e.symm.injective.comp (GlobalTheory.Proof.frame_combination_coeff_unique.get_bijective Dw).1)
  have hM : (h.gram σ (allFr K e)).PosDef := h.posDef σ _ _ hli
  have hz : ∀ a b, ((letters Dw).get a).1 ≠ ((letters Dw).get b).1 → h.gram σ (allFr K e) a b = 0 :=
    fun a b hab => horth _ _ hab
  suffices key : ∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) (k : Fin (letters Dw).length), (letters Dw).get k = ⟨τ, i⟩ →
      grSq (h.gram σ (allFr K e)) k = grSq (h.gram σ (tauFr K e τ)) i from fun k => key _ _ k rfl
  intro τ i k hk
  let p : Fin (Dw.mult τ) → Fin (letters Dw).length := fun i' => eq.symm ⟨τ, i'⟩
  have hg : ∀ i', (letters Dw).get (p i') = ⟨τ, i'⟩ := fun i' => eq.apply_symm_apply _
  have hp : Function.Injective p := fun a b hab => by
    have := congrArg (fun j => (letters Dw).get j) hab
    simp only [hg] at this
    exact eq_of_heq (Sigma.mk.inj this).2
  have hpk : p i = k := eq.symm_apply_eq.2 hk.symm
  have hsub : h.gram σ (tauFr K e τ) = (h.gram σ (allFr K e)).submatrix p p := by
    ext a b
    simp only [HermFam.gram, submatrix_apply, of_apply, allFr, tauFr, hg]
  have hout : ∀ b, b ∉ Set.range p → ((letters Dw).get b).1 ≠ τ := by
    intro b hb hτ
    rcases hgb : (letters Dw).get b with ⟨τ', j⟩
    rw [hgb] at hτ
    subst hτ
    exact hb ⟨j, eq.symm_apply_eq.2 hgb.symm⟩
  have ho : ∀ a b, a ∈ Set.range p → b ∉ Set.range p →
      h.gram σ (allFr K e) a b = 0 ∧ h.gram σ (allFr K e) b a = 0 := by
    rintro _ b ⟨a, rfl⟩ hb
    have h1 : ((letters Dw).get (p a)).1 ≠ ((letters Dw).get b).1 := by rw [hg]; exact (hout b hb).symm
    exact ⟨hz _ _ h1, hz _ _ h1.symm⟩
  rw [hsub]
  refine BlockGr.grSq_block hM hp ho hpk (fun i' hi' => ?_) (fun i' hi' => ?_)
  · by_contra hle
    have hlt : p i' < k := lt_of_le_of_ne (not_lt.1 hle) fun h' => hi'.ne (hp (hpk.trans h'.symm))
    have := hpw _ _ hlt
    rw [hg, hk] at this
    exact absurd (this rfl) (not_lt.2 hi'.le)
  · have := hpw _ _ hi'
    rw [hg, hk] at this
    exact this rfl

end GlobalTheory.LieSmooth

/- English proof (translation)
The claim follows from `@GlobalTheory.LieSmooth.grSq_allFr_tauFr`.
-/
example : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {K : Type} [Field K] [NumberField K] {n : ℕ} (e : Fin n ≃ Letter Dw) (h : HermFam K (Fin n → K)) (σ : K →+* ℂ), (∀ z z' : Letter Dw, z.1 ≠ z'.1 → h.form σ (tauFr K e z.1 z.2) (tauFr K e z'.1 z'.2) = 0) → ∀ k : Fin (letters Dw).length, grSq (h.gram σ (allFr K e)) k = grSq (h.gram σ (tauFr K e ((letters Dw).get k).1)) ((letters Dw).get k).2 := @GlobalTheory.LieSmooth.grSq_allFr_tauFr

end
