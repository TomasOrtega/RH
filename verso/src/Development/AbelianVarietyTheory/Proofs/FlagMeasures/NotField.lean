import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GgNone

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.CoordExist

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

noncomputable def linL (H : HermSp M V) (y : V) : V →ₗ[E] E where
  toFun x := H.h x y
  map_add' a b := H.h_add_left a b y
  map_smul' a x := H.h_smul_left a x y

/- English proof (translation)
Use `show linL H y (∑ i, c i • b i) = _`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, smul_eq_mul]`. Both sides reduce to the same expression.
-/
lemma h_sum_left (H : HermSp M V) {n : ℕ} (c : Fin n → E) (b : Fin n → V) (y : V) :
    H.h (∑ i, c i • b i) y = ∑ i, c i * H.h (b i) y := by
  show linL H y (∑ i, c i • b i) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul]
  rfl

/- English proof (translation)
Establish `hr : ∀ (x : V) (d : Fin n → E), H.h x (∑ j, d j • b j) = ∑ j, M.L.cj (d j) * H.h x (b j)`. Introduce `x d`. Rewrite using `[H.h_herm, h_sum_left, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, ← H.h_herm]`.

Rewrite using `[h_sum_left]`. Unfold `GlobalTheory.HL.hf`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hr, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Simplify using `only [Matrix.of_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma hf_eq (H : HermSp M V) {n : ℕ} (b : Fin n → V) (c d : Fin n → E) :
    hf M.L (Matrix.of fun i j => H.h (b i) (b j)) c d = H.h (∑ i, c i • b i) (∑ j, d j • b j) := by

  have hr : ∀ (x : V) (d : Fin n → E), H.h x (∑ j, d j • b j) = ∑ j, M.L.cj (d j) * H.h x (b j) := by
    intro x d
    rw [H.h_herm, h_sum_left, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, ← H.h_herm]
  rw [h_sum_left]
  unfold GlobalTheory.HL.hf
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hr, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.of_apply]
  ring

/- English proof (translation)
Rewrite using `[hf_eq, b.sum_equivFun, b.sum_equivFun]`.
-/
lemma hf_basis (H : HermSp M V) {n : ℕ} (b : Module.Basis (Fin n) E V) (x y : V) :
    hf M.L (Matrix.of fun i j => H.h (b i) (b j)) (b.equivFun x) (b.equivFun y) = H.h x y := by
  rw [hf_eq, b.sum_equivFun, b.sum_equivFun]

/- English proof (translation)
The claim follows from `Module.nontrivial_of_finrank_pos (R := F) (by rw [L.rank]; norm_num)`.
-/
lemma nontriv (L : LocE F E) : Nontrivial E := Module.nontrivial_of_finrank_pos (R := F) (by rw [L.rank]; norm_num)

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Unfold `GlobalTheory.HL.IsHerm GlobalTheory.HL.cT`. Use extensionality with `i j`. Conclude with `(H.h_herm (b j) (b i)).symm`. Use `M.L.free` as an intermediate fact.

Establish `: Module.Finite F E` using `Module.finite_of_finrank_pos (by rw [M.L.rank]; norm_num)`. Use `set G : Matrix (Fin n) (Fin n) E := Matrix.of fun i j => H.h (b i) (b j) with hGdef`. Establish `hvec : ∀ (v : Fin n → E) j, (Matrix.vecMul v G) j = H.h (∑ i, v i • b i) (b j)`. Introduce `v j`. Rewrite using `[h_sum_left]`.

Simplify using `only [Matrix.vecMul, dotProduct, hGdef, Matrix.of_apply]`. Establish `hright : ∀ x y : V, H.h x y = ∑ j, M.L.cj (b.repr y j) * H.h x (b j)`. Introduce `x y`. Use `conv_lhs => rw [← b.sum_repr y]`. Rewrite using `[H.h_herm, h_sum_left, map_sum]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, ← H.h_herm]`. Establish `hinj : Function.Injective (Matrix.vecMulLinear G)`. Introduce `v v' hvv`. Establish `hvv' : Matrix.vecMul v G = Matrix.vecMul v' G` using `hvv`.

Establish `hd : ∀ j, (Matrix.vecMul (v - v') G) j = 0`. Introduce `j`. Rewrite using `[Matrix.sub_vecMul, hvv', sub_self]`. Both sides reduce to the same expression. Establish `hx : ∑ i, (v - v') i • b i = 0`.

Apply `H.nondeg` to reduce the goal to its premises. Introduce `y`. Rewrite using `[hright]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← hvec, hd, mul_zero]`.

Establish `h0` using `Fintype.linearIndependent_iff.mp b.linearIndependent (v - v') hx`. Use function extensionality and compare the values at `i`. Conclude with `sub_eq_zero.mp (h0 i)`. Establish `hsurj : Function.Surjective (Matrix.vecMulLinear G)`. Establish `h2 : Function.Injective ((Matrix.vecMulLinear G).restrictScalars F)` using `hinj`.

Conclude with `LinearMap.injective_iff_surjective.mp h2`. Conclude with `(Matrix.isUnit_iff_isUnit_det G).mp (Matrix.vecMul_surjective_iff_isUnit.mp hsurj)`.
-/
lemma hermND (H : HermSp M V) {n : ℕ} (b : Module.Basis (Fin n) E V) :
    IsHermND M.L (Matrix.of fun i j => H.h (b i) (b j)) := by
  refine ⟨?_, ?_⟩
  · unfold GlobalTheory.HL.IsHerm GlobalTheory.HL.cT
    ext i j
    exact (H.h_herm (b j) (b i)).symm
  · have := M.L.free
    have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [M.L.rank]; norm_num)
    set G : Matrix (Fin n) (Fin n) E := Matrix.of fun i j => H.h (b i) (b j) with hGdef
    have hvec : ∀ (v : Fin n → E) j, (Matrix.vecMul v G) j = H.h (∑ i, v i • b i) (b j) := by
      intro v j
      rw [h_sum_left]
      simp only [Matrix.vecMul, dotProduct, hGdef, Matrix.of_apply]
    have hright : ∀ x y : V, H.h x y = ∑ j, M.L.cj (b.repr y j) * H.h x (b j) := by
      intro x y
      conv_lhs => rw [← b.sum_repr y]
      rw [H.h_herm, h_sum_left, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, ← H.h_herm]

    have hinj : Function.Injective (Matrix.vecMulLinear G) := by
      intro v v' hvv
      have hvv' : Matrix.vecMul v G = Matrix.vecMul v' G := hvv
      have hd : ∀ j, (Matrix.vecMul (v - v') G) j = 0 := by
        intro j
        rw [Matrix.sub_vecMul, hvv', sub_self]
        rfl
      have hx : ∑ i, (v - v') i • b i = 0 := by
        apply H.nondeg
        intro y
        rw [hright]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [← hvec, hd, mul_zero]
      have h0 := Fintype.linearIndependent_iff.mp b.linearIndependent (v - v') hx
      funext i
      exact sub_eq_zero.mp (h0 i)

    have hsurj : Function.Surjective (Matrix.vecMulLinear G) := by
      have h2 : Function.Injective ((Matrix.vecMulLinear G).restrictScalars F) := hinj
      exact LinearMap.injective_iff_surjective.mp h2
    exact (Matrix.isUnit_iff_isUnit_det G).mp (Matrix.vecMul_surjective_iff_isUnit.mp hsurj)

/- English proof (translation)
Introduce `hE`. Establish `hx : g.e.symm (1, 0) ≠ 0`. Introduce `h0`. Establish `h1` using `congrArg g.e h0`. Simplify using `at h1`.

Take `⟨x', hx'⟩` from `hE.mul_inv_cancel hx`. Establish `hxy : g.e.symm (1, 0) * g.e.symm (0, 1) = 0`. Rewrite using `[← map_mul]`. Simplify using the standard rewrite rules. Establish `hy : g.e.symm (0, 1) = 0`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_comm x', hx', one_mul]`. Use `_ = 0 := by rw [mul_assoc, hxy, mul_zero]`. Establish `h1` using `congrArg g.e hy`. Simplify using `at h1`.
-/
lemma not_field (L : LocE F E) (g : SplitG L) : ¬ IsField E := by
  intro hE
  have hx : g.e.symm (1, 0) ≠ 0 := by
    intro h0
    have h1 := congrArg g.e h0
    simp at h1
  obtain ⟨x', hx'⟩ := hE.mul_inv_cancel hx
  have hxy : g.e.symm (1, 0) * g.e.symm (0, 1) = 0 := by
    rw [← map_mul]
    simp
  have hy : g.e.symm (0, 1) = 0 := by
    calc g.e.symm (0, 1) = (x' * g.e.symm (1, 0)) * g.e.symm (0, 1) := by
          rw [mul_comm x', hx', one_mul]
      _ = 0 := by rw [mul_assoc, hxy, mul_zero]
  have h1 := congrArg g.e hy
  simp at h1

/- English proof (translation)
Use `split_ifs with hab`. Rewrite using `[hab.1, hab.2]`. Conclude with `A.h_zz`. Conclude with `A.h_iso a b (not_and_or.mp hab)`.
-/
lemma gram_eq {H : HermSp M V} {r : ℕ} (A : LocNG.FrameD H r) (a b : Fin (r + 1)) :
    H.h (A.f a) (A.f b) = if a = Fin.last r ∧ b = Fin.last r then -algebraMap F E A.T else 0 := by
  split_ifs with hab
  · rw [hab.1, hab.2]
    exact A.h_zz
  · exact A.h_iso a b (not_and_or.mp hab)

/- English proof (translation)
Proceed by induction on `a using Fin.lastCases with`. Consider the case `last`. Rewrite using `[if_neg (Fin.castSucc_lt_last j).ne', H.h_herm, A.h_sz, map_zero]`. Consider the case `cast i`. Rewrite using `[A.h_es i j]`.

Simplify using `only [Fin.castSucc_inj]`.
-/
lemma dual_eq {H : HermSp M V} {r : ℕ} (A : LocNG.FrameD H r) (a : Fin (r + 1)) (j : Fin r) :
    H.h (A.f a) (A.es j) = if a = j.castSucc then 1 else 0 := by
  induction a using Fin.lastCases with
  | last =>
    rw [if_neg (Fin.castSucc_lt_last j).ne', H.h_herm, A.h_sz, map_zero]
  | cast i =>
    rw [A.h_es i j]
    simp only [Fin.castSucc_inj]

/- English proof (translation)
Use `⟨⟨⟨T, hT⟩, u, ?_, ?_⟩, rfl⟩` and prove the remaining obligations. Apply `Subtype.ext show T * (u : F) = 1` to reduce the goal to its premises. Rewrite using `[mul_comm]`. Conclude with `h`. Apply `Subtype.ext show (u : F) * T = 1` to reduce the goal to its premises.

Conclude with `h`.
-/
lemma unit_of {T : F} (hT : T ∈ 𝒪[F]) (u : 𝒪[F]) (h : (u : F) * T = 1) :
    ∃ v : (𝒪[F])ˣ, ((v : 𝒪[F]) : F) = T := by
  refine ⟨⟨⟨T, hT⟩, u, ?_, ?_⟩, rfl⟩
  · apply Subtype.ext
    show T * (u : F) = 1
    rw [mul_comm]
    exact h
  · apply Subtype.ext
    show (u : F) * T = 1
    exact h

end

/- English proof (translation)
Introduce `F _ _ _ E _ _ _ _ M hOK V _ _ H r k P hrank hrel`. Use `hOK.loc` as an intermediate fact. Establish `: Nontrivial E` using `nontriv M.L`. Use `H.free` as an intermediate fact. Use `H.fin` as an intermediate fact.

Unfold `LocNG.FPair.RelG LocNG.FPair.IsPoint LocNG.FPair.NormsOK at hrel`. Take `⟨-, -, hG, -, -, ⟨w, hw⟩, hAT, hA0, hBT, hB0, hsp⟩` from `hrel`. Choose the witnesses or unpack the hypotheses as in `⟨ϖ, hϖ, hϖs⟩ : ∃ ϖ : 𝒪[F], Irreducible ϖ ∧ ∀ g, M.split = some g → ϖ = g.q := by`. Consider the cases of `hs : M.split with`. Consider the case `none`.

Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible 𝒪[F]`. Conclude with `⟨ϖ, hϖ, fun g hg => by cases hg⟩`. Consider the case `some g`. Conclude with `⟨g.q, g.q_irr, fun g' hg => by cases hg; rfl⟩`. Set `bs : Module.Basis (Fin (k + 2 * r + 1)) E V` to `Module.finBasisOfFinrankEq E V hrank`.

Establish `hZ : (Matrix.of fun a c => hf M.L (Matrix.of fun i j => H.h (bs i) (bs j)) (bs.equivFun (P.B.f c)) (bs.equivFun (P.A.f a))) = H.Zhat P.A.f P.B.f`. Use extensionality with `a c`. Simplify using `only [Matrix.of_apply, hf_basis]`. Both sides reduce to the same expression. Establish `hD1 : lead (H.Zhat P.A.f P.B.f) (Fin.last (r + 1)) = H.Dl P.A.f P.B.f (r + 1)`.

Unfold `GlobalTheory.HL.lead HermSp.Dl`. Rewrite using `[dif_pos le_rfl]`. Establish `hD0 : lead (H.Zhat P.A.f P.B.f) (Fin.last r).castSucc = H.Dl P.A.f P.B.f r`. Unfold `GlobalTheory.HL.lead HermSp.Dl`. Rewrite using `[dif_pos (Nat.le_succ r)]`.

Establish `hG'` using `hG`. Unfold `LocNG.FPair.Gv HermSp.Gdet HermSp.normE at hG'`. Rewrite `hG'` using `[← hD1, ← hD0, ← hZ]`. Set `S : Frames M.L r k` to `{ ϖ := ϖ ϖ_irr := hϖ Hm := Matrix.of fun i j => H.h (bs i) (bs j) herm := hermND H bs T := Units.mk0 P.A.T hA0 T' := Units.mk0 P.B.T hB0 f := fun a => bs.equivFun (P.A.f a) f' := fun a => bs.equivFun (P.B.f a) es := fun j => bs.equivFun (P.A.es j) es' := fun j => bs.equivFun (P.B …`. Rewrite using `[hf_basis, gram_eq]`.

Both sides reduce to the same expression. Use the proof step `gram' := fun a c => by`. Rewrite using `[hf_basis, gram_eq]`. Both sides reduce to the same expression. Use `dual := fun a j => by rw [hf_basis, dual_eq]`.

Use the proof step `dual' := fun a j => by rw [hf_basis, dual_eq]`. Use `iso := fun i j => by rw [hf_basis, P.A.h_ss]`. Use the proof step `iso' := fun i j => by rw [hf_basis, P.B.h_ss]`. Use `w := w`. Use `relevant := fun a c => by`.

Rewrite using `[hf_basis, ← hw a c]`. Establish `hsq : ((-1 : E) ^ (r - (c : ℕ))) * (-1) ^ (r - (c : ℕ)) = 1`. Rewrite using `[← mul_pow]`. Simplify using the standard rewrite rules. Use `show H.h (P.B.f c) (P.A.f a) = (-1) ^ (r - (c : ℕ)) * H.h (P.B.f c) (P.A.f a) * (-1) ^ (r - (c : ℕ))`.

Take the linear combination `(-(H.h (P.B.f c) (P.A.f a))) * hsq`. Use `G_ne := hG'`. Use `gg := M.split.isSome`. Use `gg_ok := by`. Introduce `hgg`.

Take `⟨g, hg⟩` from `Option.isSome_iff_exists.mp hgg`. Take `⟨⟨u, v, hu, hv⟩, -⟩` from `hsp g hg`. Conclude with `⟨not_field M.L g, unit_of hAT u hu, unit_of hBT v hv⟩ }`. Use `⟨S, ⟨{ e := bs.equivFun h_eq := fun x y => hf_basis H bs x y f_eq := fun a => rfl f'_eq := fun a => rfl es_eq := fun a => rfl es'_eq := fun a => rfl T_eq := rfl T'_eq := rfl gg_none := fun h => ?_ gg_some := fun g hg => ⟨?_, hϖs g hg⟩ }⟩⟩` and prove the remaining obligations. Use `show M.split.isSome = false`.

Rewrite using `[h]`. Both sides reduce to the same expression. Use `show M.split.isSome = true`. Rewrite using `[hg]`. Both sides reduce to the same expression.
-/
theorem exists_coord : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∃ S : Frames M.L r k, Nonempty (Coord P S) := by
  intro F _ _ _ E _ _ _ _ M hOK V _ _ H r k P hrank hrel
  have := hOK.loc
  have : Nontrivial E := nontriv M.L
  have := H.free
  have := H.fin
  unfold LocNG.FPair.RelG LocNG.FPair.IsPoint LocNG.FPair.NormsOK at hrel
  obtain ⟨-, -, hG, -, -, ⟨w, hw⟩, hAT, hA0, hBT, hB0, hsp⟩ := hrel

  obtain ⟨ϖ, hϖ, hϖs⟩ : ∃ ϖ : 𝒪[F], Irreducible ϖ ∧ ∀ g, M.split = some g → ϖ = g.q := by
    cases hs : M.split with
    | none =>
      obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
      exact ⟨ϖ, hϖ, fun g hg => by cases hg⟩
    | some g =>
      exact ⟨g.q, g.q_irr, fun g' hg => by cases hg; rfl⟩
  let bs : Module.Basis (Fin (k + 2 * r + 1)) E V := Module.finBasisOfFinrankEq E V hrank
  have hZ : (Matrix.of fun a c => hf M.L (Matrix.of fun i j => H.h (bs i) (bs j))
      (bs.equivFun (P.B.f c)) (bs.equivFun (P.A.f a))) = H.Zhat P.A.f P.B.f := by
    ext a c
    simp only [Matrix.of_apply, hf_basis]
    rfl
  have hD1 : lead (H.Zhat P.A.f P.B.f) (Fin.last (r + 1)) = H.Dl P.A.f P.B.f (r + 1) := by
    unfold GlobalTheory.HL.lead HermSp.Dl
    rw [dif_pos le_rfl]
  have hD0 : lead (H.Zhat P.A.f P.B.f) (Fin.last r).castSucc = H.Dl P.A.f P.B.f r := by
    unfold GlobalTheory.HL.lead HermSp.Dl
    rw [dif_pos (Nat.le_succ r)]
  have hG' := hG
  unfold LocNG.FPair.Gv HermSp.Gdet HermSp.normE at hG'
  rw [← hD1, ← hD0, ← hZ] at hG'
  let S : Frames M.L r k :=
    { ϖ := ϖ
      ϖ_irr := hϖ
      Hm := Matrix.of fun i j => H.h (bs i) (bs j)
      herm := hermND H bs
      T := Units.mk0 P.A.T hA0
      T' := Units.mk0 P.B.T hB0
      f := fun a => bs.equivFun (P.A.f a)
      f' := fun a => bs.equivFun (P.B.f a)
      es := fun j => bs.equivFun (P.A.es j)
      es' := fun j => bs.equivFun (P.B.es j)
      gram := fun a c => by
        rw [hf_basis, gram_eq]
        rfl
      gram' := fun a c => by
        rw [hf_basis, gram_eq]
        rfl
      dual := fun a j => by rw [hf_basis, dual_eq]
      dual' := fun a j => by rw [hf_basis, dual_eq]
      iso := fun i j => by rw [hf_basis, P.A.h_ss]
      iso' := fun i j => by rw [hf_basis, P.B.h_ss]
      w := w
      relevant := fun a c => by
        rw [hf_basis, ← hw a c]
        have hsq : ((-1 : E) ^ (r - (c : ℕ))) * (-1) ^ (r - (c : ℕ)) = 1 := by
          rw [← mul_pow]
          simp
        show H.h (P.B.f c) (P.A.f a) =
          (-1) ^ (r - (c : ℕ)) * H.h (P.B.f c) (P.A.f a) * (-1) ^ (r - (c : ℕ))
        linear_combination (-(H.h (P.B.f c) (P.A.f a))) * hsq
      G_ne := hG'
      gg := M.split.isSome
      gg_ok := by
        intro hgg
        obtain ⟨g, hg⟩ := Option.isSome_iff_exists.mp hgg
        obtain ⟨⟨u, v, hu, hv⟩, -⟩ := hsp g hg
        exact ⟨not_field M.L g, unit_of hAT u hu, unit_of hBT v hv⟩ }
  refine ⟨S, ⟨{ e := bs.equivFun
                h_eq := fun x y => hf_basis H bs x y
                f_eq := fun a => rfl
                f'_eq := fun a => rfl
                es_eq := fun a => rfl
                es'_eq := fun a => rfl
                T_eq := rfl
                T'_eq := rfl
                gg_none := fun h => ?_
                gg_some := fun g hg => ⟨?_, hϖs g hg⟩ }⟩⟩
  · show M.split.isSome = false
    rw [h]
    rfl
  · show M.split.isSome = true
    rw [hg]
    rfl

end GlobalTheory.HL.CoordExist
