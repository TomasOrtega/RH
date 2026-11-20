import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RowsExhaust
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin Formalism.DivisionValues

noncomputable section

namespace GlobalTheory.EtaJoin

section Gen

variable {K : Type} [Field K] [StarRing K] {n d : ℕ}

/- English proof (translation)
Simplify using `only [hform, Matrix.toLinearMapₛₗ₂'_apply, dotProduct, Matrix.mulVec, Finset.mul_sum, RingHom.id_apply]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[starRingEnd_apply, Pi.star_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hform_eq_dot (H : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
    hform H x y = star x ⬝ᵥ H.mulVec y := by
  simp only [hform, Matrix.toLinearMapₛₗ₂'_apply, dotProduct, Matrix.mulVec, Finset.mul_sum, RingHom.id_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [starRingEnd_apply, Pi.star_apply]; ring

/- English proof (translation)
Establish `e : x - E.mulVec (Pr.mulVec x) = (1 - E * Pr).mulVec x`. Rewrite using `[Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec]`. Rewrite using `[hform_eq_dot, e, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h.2, Matrix.zero_mulVec, dotProduct_zero]`.
-/
theorem hform_orthProj (H : Matrix (Fin n) (Fin n) K) (E : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K)
    (h : IsOrthProj H E Pr) (u : Fin d → K) (x : Fin n → K) :
    hform H (E.mulVec u) (x - E.mulVec (Pr.mulVec x)) = 0 := by
  have e : x - E.mulVec (Pr.mulVec x) = (1 - E * Pr).mulVec x := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec]
  rw [hform_eq_dot, e, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    h.2, Matrix.zero_mulVec, dotProduct_zero]

variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (σ : K →+* ℂ) (J : (Fin n → K) →ₛₗ[σ] W)

/- English proof (translation)
Use `conv_lhs => rw [← Finset.univ_sum_single y]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `: (Pi.single i (y i) : Fin n → K) = y i • Pi.single i 1`. Use extensionality with `k`.

Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, hk]`. Rewrite using `[this, LinearMap.map_smulₛₗ]`.
-/
theorem semi_expand (y : Fin n → K) : J y = ∑ i, σ (y i) • J (Pi.single i 1) := by
  conv_lhs => rw [← Finset.univ_sum_single y]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (Pi.single i (y i) : Fin n → K) = y i • Pi.single i 1 := by
    ext k; by_cases hk : k = i
    · subst hk; simp
    · simp [Pi.single_apply, hk]
  rw [this, LinearMap.map_smulₛₗ]

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `y hy`. Rewrite `hy` using `[semi_expand σ J y]`. Establish `h0` using `(Fintype.linearIndependent_iff.1 hli) (fun i => σ (y i)) hy`. Use function extensionality and compare the values at `i`.

Conclude with `σ.injective (by rw [h0 i]; simp)`.
-/
theorem semi_injective (hli : LinearIndependent ℂ fun i => J (Pi.single i 1)) : Function.Injective J := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  rw [semi_expand σ J y] at hy
  have h0 := (Fintype.linearIndependent_iff.1 hli) (fun i => σ (y i)) hy
  funext i
  exact σ.injective (by rw [h0 i]; simp)

/- English proof (translation)
Establish `e : E.mulVec c = ∑ k, c k • E.mulVec (Pi.single k 1)` using `by conv_lhs => rw [← Finset.univ_sum_single c]`. Rewrite using `[Matrix.mulVec_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← Matrix.mulVec_smul]`. Use `congr 1`.

Use extensionality with `a`. Distinguish the cases in `ha : a = k`. Substitute `ha` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, ha]`.

Rewrite using `[e, map_sum]`. Use `Submodule.sum_mem _ fun k _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.map_smulₛₗ]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)`.
-/
theorem semi_mulVec_mem (E : Matrix (Fin n) (Fin d) K) (c : Fin d → K) :
    J (E.mulVec c) ∈ Submodule.span ℂ (Set.range fun k => J (E.mulVec (Pi.single k 1))) := by
  have e : E.mulVec c = ∑ k, c k • E.mulVec (Pi.single k 1) := by
    conv_lhs => rw [← Finset.univ_sum_single c]
    rw [Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Matrix.mulVec_smul]
    congr 1
    ext a; by_cases ha : a = k
    · subst ha; simp
    · simp [Pi.single_apply, ha]
  rw [e, map_sum]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [LinearMap.map_smulₛₗ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

end Gen

end GlobalTheory.EtaJoin

namespace GlobalTheory.EtaJoin

section Gen2

variable {K : Type} [Field K] [NumberField K] [StarRing K] {n d : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  {σ : K →+* ℂ} {V : Type} [AddCommGroup V] [Module K V]

/- English proof (translation)
Establish `hin : ∀ x y, inner ℂ (jV (e x)) (jV (e y)) = σ (hform H x y)` using `hF.inner`. Establish `hJinj : Function.Injective fun x => jV (e x)` using `fun a b h => semi_injective σ (jV.comp e.toLinearMap) hF.li h`. Establish `hgen : ∀ c, jV (e (E.mulVec c)) ∈ Z`. Introduce `c`. Rewrite using `[hZ]`.

Conclude with `semi_mulVec_mem σ (jV.comp e.toLinearMap) E c`. Establish `horth : ∀ x, jV (e (x - E.mulVec (Pr.mulVec x))) ∈ Zᗮ`. Introduce `x`. Rewrite using `[Submodule.mem_orthogonal]`. Introduce `u hu`.

Rewrite `hu` using `[hZ]`. Proceed by induction on `hu using Submodule.span_induction with`. Consider the case `mem v hv`. Take `⟨k, rfl⟩` from `hv`. Use `show inner ℂ (jV (e (E.mulVec (Pi.single k 1)))) _ = 0`.

Rewrite using `[hin, hform_orthProj _ _ _ hP, map_zero]`. Consider the case `zero => exact inner_zero_left _`. Consider the case `add a b _ _ ha hb => rw [inner_add_left, ha, hb, add_zero]`. Consider the case `smul c a _ ha => rw [inner_smul_left, ha, mul_zero]`. Establish `hEinj : Function.Injective E.mulVec`.

Introduce `a b hab`. Use `congrArg Pr.mulVec hab` as an intermediate fact. Simplify using `only [Matrix.mulVec_mulVec, hP.1, Matrix.one_mulVec] at this`. Conclude with `this`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Conclude with `e.injective.comp hEinj`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce `hy`. Rewrite `hy` using `[Submodule.mem_comap]`.

Take `⟨x, rfl⟩` from `e.surjective y`. Establish `hw1 : jV (e (x - E.mulVec (Pr.mulVec x))) ∈ Z`. Rewrite using `[map_sub, map_sub]`. Conclude with `Submodule.sub_mem _ hy (hgen _)`. Establish `hw0 : jV (e (x - E.mulVec (Pr.mulVec x))) = 0` using `inner_self_eq_zero.1 ((Submodule.mem_orthogonal _ _).1 (horth x) _ hw1)`.

Establish `hw : x = E.mulVec (Pr.mulVec x)`. Use `sub_eq_zero.1 (hJinj ?_)` and prove the remaining obligations. Simplify using `only [map_zero]`. Conclude with `hw0`. Conclude with `⟨Pr.mulVec x, by simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply, LinearEquiv.coe_coe]; rw [← hw]⟩`.

Introduce and unpack `⟨c, rfl⟩`. Conclude with `hgen c`. Introduce `x`. Rewrite using `[Submodule.mem_comap]`. Establish `e1 : e x - (e.toLinearMap ∘ₗ E.mulVecLin) (Pr.mulVec x) = e (x - E.mulVec (Pr.mulVec x))`.

Simplify using `only [LinearMap.comp_apply, Matrix.mulVecLin_apply, LinearEquiv.coe_coe, map_sub]`. Rewrite using `[e1]`. Conclude with `horth x`.
-/
theorem tied_orthProj (e : (Fin n → K) ≃ₗ[K] V) (jV : V →ₛₗ[σ] W) (H Eop : Matrix (Fin n) (Fin n) K) (op : W →ₗ[ℂ] W)
    (E : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K) (hP : IsOrthProj H E Pr)
    (hF : FormsTie σ (jV.comp e.toLinearMap) H Eop op) (Z : Submodule ℂ W)
    (hZ : Z = Submodule.span ℂ (Set.range fun k => jV (e (E.mulVec (Pi.single k 1))))) :
    Function.Injective (e.toLinearMap ∘ₗ E.mulVecLin) ∧ Z.comap jV = LinearMap.range (e.toLinearMap ∘ₗ E.mulVecLin) ∧
      ∀ x, e x - (e.toLinearMap ∘ₗ E.mulVecLin) (Pr.mulVec x) ∈ (Zᗮ).comap jV := by
  have hin : ∀ x y, inner ℂ (jV (e x)) (jV (e y)) = σ (hform H x y) := hF.inner
  have hJinj : Function.Injective fun x => jV (e x) := fun a b h => semi_injective σ (jV.comp e.toLinearMap) hF.li h
  have hgen : ∀ c, jV (e (E.mulVec c)) ∈ Z := by
    intro c; rw [hZ]; exact semi_mulVec_mem σ (jV.comp e.toLinearMap) E c
  have horth : ∀ x, jV (e (x - E.mulVec (Pr.mulVec x))) ∈ Zᗮ := by
    intro x
    rw [Submodule.mem_orthogonal]
    intro u hu
    rw [hZ] at hu
    induction hu using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨k, rfl⟩ := hv
      show inner ℂ (jV (e (E.mulVec (Pi.single k 1)))) _ = 0
      rw [hin, hform_orthProj _ _ _ hP, map_zero]
    | zero => exact inner_zero_left _
    | add a b _ _ ha hb => rw [inner_add_left, ha, hb, add_zero]
    | smul c a _ ha => rw [inner_smul_left, ha, mul_zero]
  have hEinj : Function.Injective E.mulVec := by
    intro a b hab
    have := congrArg Pr.mulVec hab
    simp only [Matrix.mulVec_mulVec, hP.1, Matrix.one_mulVec] at this
    exact this
  refine ⟨?_, ?_, ?_⟩
  · exact e.injective.comp hEinj
  · ext y
    constructor
    · intro hy
      rw [Submodule.mem_comap] at hy
      obtain ⟨x, rfl⟩ := e.surjective y
      have hw1 : jV (e (x - E.mulVec (Pr.mulVec x))) ∈ Z := by
        rw [map_sub, map_sub]; exact Submodule.sub_mem _ hy (hgen _)
      have hw0 : jV (e (x - E.mulVec (Pr.mulVec x))) = 0 :=
        inner_self_eq_zero.1 ((Submodule.mem_orthogonal _ _).1 (horth x) _ hw1)
      have hw : x = E.mulVec (Pr.mulVec x) := by
        refine sub_eq_zero.1 (hJinj ?_)
        simp only [map_zero]; exact hw0
      exact ⟨Pr.mulVec x, by simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply, LinearEquiv.coe_coe]; rw [← hw]⟩
    · rintro ⟨c, rfl⟩
      exact hgen c
  · intro x
    rw [Submodule.mem_comap]
    have e1 : e x - (e.toLinearMap ∘ₗ E.mulVecLin) (Pr.mulVec x) = e (x - E.mulVec (Pr.mulVec x)) := by
      simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply, LinearEquiv.coe_coe, map_sub]
    rw [e1]; exact horth x

end Gen2

/- English proof (translation)
Introduce `D G _ _ Pl0 T m A P ψ Zs tup eMt s hOk i t hF hZ`. Establish `hB : BlockHyp (A.fam.L i t) (A.fam.lvlA P ψ) A.fam.v0 s` using `⟨hOk.conj, fun χ hχ => hOk.irr χ hχ, hOk.lifts i t⟩`. Establish `hP : IsOrthProj (lH D A P ψ i t) (lZ0 D A P ψ Zs i t) (lPrj D A P ψ Zs i t)` using `BlockDat.lf_l_proj (Z := Zs.Zl i t) hB`. Conclude with `tied_orthProj (eMt i t) (D.what₂.jMt (tup t) ((i : ℕ) + 1)) _ _ _ _ _ hP hF _ hZ`.
-/
theorem concreteProj_orth : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (m : ℕ) (A : FamIn D.what₂.LL G Pl0 T m) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (tup : T → D.what₂.Tup) (eMt : ∀ (i : Fin m) (t : T), (Fin (lDim D A P ψ i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1)) (s : ℕ), A.fam.Ok s → ∀ (i : Fin m) (t : T), FormsTie D.what₂.embLL ((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap) (lH D A P ψ i t) (lE D A P ψ i t) (D.what₂.eMt (tup t) ((i : ℕ) + 1)) → Idx.Z0 D (tup t) ((i : ℕ) + 1) = Submodule.span ℂ (Set.range fun k => (D.what₂.jMt (tup t) ((i : ℕ) + 1)) (eMt i t ((lZ0 D A P ψ Zs i t).mulVec (Pi.single k 1)))) → Function.Injective ((eMt i t).toLinearMap ∘ₗ (lZ0 D A P ψ Zs i t).mulVecLin) ∧ ratSub D (tup t) ((i : ℕ) + 1) (Idx.Z0 D (tup t) ((i : ℕ) + 1)) = LinearMap.range ((eMt i t).toLinearMap ∘ₗ (lZ0 D A P ψ Zs i t).mulVecLin) ∧ ∀ x, eMt i t x - ((eMt i t).toLinearMap ∘ₗ (lZ0 D A P ψ Zs i t).mulVecLin) ((lPrj D A P ψ Zs i t).mulVec x) ∈ ratSub D (tup t) ((i : ℕ) + 1) (Idx.Z0 D (tup t) ((i : ℕ) + 1))ᗮ := by
  intro D G _ _ Pl0 T m A P ψ Zs tup eMt s hOk i t hF hZ
  have hB : BlockHyp (A.fam.L i t) (A.fam.lvlA P ψ) A.fam.v0 s := ⟨hOk.conj, fun χ hχ => hOk.irr χ hχ, hOk.lifts i t⟩
  have hP : IsOrthProj (lH D A P ψ i t) (lZ0 D A P ψ Zs i t) (lPrj D A P ψ Zs i t) :=
    BlockDat.lf_l_proj (Z := Zs.Zl i t) hB
  exact tied_orthProj (eMt i t) (D.what₂.jMt (tup t) ((i : ℕ) + 1)) _ _ _ _ _ hP hF _ hZ

end GlobalTheory.EtaJoin
