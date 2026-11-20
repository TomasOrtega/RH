import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistDecomp

local infixl:70 " ⬝ " => HMul.hMul

variable {D : D7}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem adj_eq' {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E) : adj D A = Aᴴ := rfl

/- English proof (translation)
Establish `hG : V.gramᴴ = V.gram` using `GlobalTheory.MixModel.gram_conjTranspose V`. Establish `hC : Cᴴ * V.gram * C = 0`. Establish `e : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C = Cᴴ` using `adj_eq' C`. Use `hs.frame.2.2` as an intermediate fact. Rewrite `this` using `[e]`. Then use the resulting hypothesis.

Establish `hB` using `hs.isom`. Establish `hCB` using `hs.orth`. Simplify using `only [adj_eq'] at hB hCB h1 h2 h3 ⊢`. Establish `hC'C : C'ᴴ * V.gram * C = 1`. Use `congrArg Matrix.conjTranspose h1` as an intermediate fact.

Simplify `this` using `[Matrix.conjTranspose_mul, hG, Matrix.mul_assoc]`. Establish `hBC : Bᴴ * V.gram * C = 0`. Use `congrArg Matrix.conjTranspose hCB` as an intermediate fact. Simplify `this` using `[Matrix.conjTranspose_mul, hG, Matrix.mul_assoc]`. Establish `hBC' : Bᴴ * V.gram * C' = 0`.

Use `congrArg Matrix.conjTranspose h3` as an intermediate fact. Simplify `this` using `[Matrix.conjTranspose_mul, hG, Matrix.mul_assoc]`. Establish `hG' : V'.gram⁻¹ * V'.gram = 1` using `Matrix.nonsing_inv_mul _ (GlobalTheory.MixModel.gram_isUnit_det V')`. Establish `hPC : V'.gram⁻¹ * Bᴴ * V.gram * C = 0`. Simplify using `only [Matrix.mul_assoc] at hBC ⊢`.

Rewrite using `[hBC, Matrix.mul_zero]`. Establish `hPC' : V'.gram⁻¹ * Bᴴ * V.gram * C' = 0`. Simplify using `only [Matrix.mul_assoc] at hBC' ⊢`. Rewrite using `[hBC', Matrix.mul_zero]`. Establish `hPB : V'.gram⁻¹ * Bᴴ * V.gram * B = 1`.

Simplify using `only [Matrix.mul_assoc] at hB ⊢`. Rewrite using `[hB, hG']`. Use `⟨hC'C, hPC, hPC', hPB, hC, ?_⟩` and prove the remaining obligations. Use `set P := V'.gram⁻¹ * Bᴴ * V.gram with hP`. Set `M : Matrix (Fin V.rank) (Fin r ⊕ (Fin V'.rank ⊕ Fin r)) D.host.E` to `Matrix.fromCols C (Matrix.fromCols B C')`.

Set `N : Matrix (Fin r ⊕ (Fin V'.rank ⊕ Fin r)) (Fin V.rank) D.host.E` to `Matrix.fromRows (C'ᴴ * V.gram) (Matrix.fromRows P (Cᴴ * V.gram))`. Establish `hNM : N * M = 1`. Simplify using `only [N, M, Matrix.fromRows_mul, Matrix.mul_fromCols]`. Apply the tactic sequence `ext (i | i | i) (j | j | j) <;>`. Simplify using `[hC'C, hPC, hPC', hPB, hC, h1, h2, h3, hCB, Matrix.one_apply]`.

Establish `hcard : Fintype.card (Fin r ⊕ (Fin V'.rank ⊕ Fin r)) = Fintype.card (Fin V.rank)`. Simplify using `only [Fintype.card_sum, Fintype.card_fin]`. Use `hs.rank` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hMN : M * N = 1` using `(Matrix.mul_eq_one_comm_of_equiv (Fintype.equivOfCardEq hcard)).mp hNM`.

Simplify `hMN` using `[M, N, Matrix.fromCols_mul_fromRows]`.
-/
theorem frame_relations {V V' : HSp D} {r : ℕ} {C C' : Matrix (Fin V.rank) (Fin r) D.host.E}
    {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E} (hs : IsIsoSplit V V' C B)
    (h1 : adj D C * V.gram * C' = 1) (h2 : adj D C' * V.gram * C' = 0) (h3 : adj D C' * V.gram * B = 0) :
    adj D C' * V.gram * C = 1 ∧ (V'.gram⁻¹ * adj D B * V.gram) * C = 0 ∧
    (V'.gram⁻¹ * adj D B * V.gram) * C' = 0 ∧ (V'.gram⁻¹ * adj D B * V.gram) * B = 1 ∧
    adj D C * V.gram * C = 0 ∧
    C * (adj D C' * V.gram) + (B * (V'.gram⁻¹ * adj D B * V.gram) + C' * (adj D C * V.gram)) = 1 := by
  have hG : V.gramᴴ = V.gram := GlobalTheory.MixModel.gram_conjTranspose V
  have hC : Cᴴ * V.gram * C = 0 := by
    have e : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C = Cᴴ := adj_eq' C
    have := hs.frame.2.2
    rwa [e] at this
  have hB := hs.isom
  have hCB := hs.orth
  simp only [adj_eq'] at hB hCB h1 h2 h3 ⊢

  have hC'C : C'ᴴ * V.gram * C = 1 := by
    have := congrArg Matrix.conjTranspose h1
    simpa [Matrix.conjTranspose_mul, hG, Matrix.mul_assoc] using this
  have hBC : Bᴴ * V.gram * C = 0 := by
    have := congrArg Matrix.conjTranspose hCB
    simpa [Matrix.conjTranspose_mul, hG, Matrix.mul_assoc] using this
  have hBC' : Bᴴ * V.gram * C' = 0 := by
    have := congrArg Matrix.conjTranspose h3
    simpa [Matrix.conjTranspose_mul, hG, Matrix.mul_assoc] using this
  have hG' : V'.gram⁻¹ * V'.gram = 1 := Matrix.nonsing_inv_mul _ (GlobalTheory.MixModel.gram_isUnit_det V')
  have hPC : V'.gram⁻¹ * Bᴴ * V.gram * C = 0 := by
    simp only [Matrix.mul_assoc] at hBC ⊢; rw [hBC, Matrix.mul_zero]
  have hPC' : V'.gram⁻¹ * Bᴴ * V.gram * C' = 0 := by
    simp only [Matrix.mul_assoc] at hBC' ⊢; rw [hBC', Matrix.mul_zero]
  have hPB : V'.gram⁻¹ * Bᴴ * V.gram * B = 1 := by
    simp only [Matrix.mul_assoc] at hB ⊢; rw [hB, hG']
  refine ⟨hC'C, hPC, hPC', hPB, hC, ?_⟩

  set P := V'.gram⁻¹ * Bᴴ * V.gram with hP
  let M : Matrix (Fin V.rank) (Fin r ⊕ (Fin V'.rank ⊕ Fin r)) D.host.E := Matrix.fromCols C (Matrix.fromCols B C')
  let N : Matrix (Fin r ⊕ (Fin V'.rank ⊕ Fin r)) (Fin V.rank) D.host.E :=
    Matrix.fromRows (C'ᴴ * V.gram) (Matrix.fromRows P (Cᴴ * V.gram))
  have hNM : N * M = 1 := by
    simp only [N, M, Matrix.fromRows_mul, Matrix.mul_fromCols]
    ext (i | i | i) (j | j | j) <;>
      simp [hC'C, hPC, hPC', hPB, hC, h1, h2, h3, hCB, Matrix.one_apply]
  have hcard : Fintype.card (Fin r ⊕ (Fin V'.rank ⊕ Fin r)) = Fintype.card (Fin V.rank) := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    have := hs.rank
    omega
  have hMN : M * N = 1 := (Matrix.mul_eq_one_comm_of_equiv (Fintype.equivOfCardEq hcard)).mp hNM
  simpa [M, N, Matrix.fromCols_mul_fromRows] using hMN

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D V V' W r C B hs C' h1 h2 h3`. Take `⟨hC'C, hPC, hPC', hPB, hCC, hid⟩` from `frame_relations hs h1 h2 h3`. Establish `hV'r` using `GlobalTheory.MixModel.ratL_eq W V'`. Establish `hVr` using `GlobalTheory.MixModel.ratL_eq W V`. Use `set f := incA D with hf`.

Use `set a := (adj D C' * V.gram).map f with ha`. Use `set c := (adj D C * V.gram).map f with hc`. Use `set p := (V'.gram⁻¹ * adj D B * V.gram).map f with hp`. Use `set u := C.map f with hu`. Use `set u' := C'.map f with hu'`.

Use `set b := B.map f with hb`. Establish `m1 : ∀ {k l m : ℕ} (X : Matrix (Fin k) (Fin l) D.host.E) (Y : Matrix (Fin l) (Fin m) D.host.E), X.map f * Y.map f = (X * Y).map f` using `fun X Y => (Matrix.map_mul).symm`. Establish `z0 : ∀ {k l : ℕ}, (0 : Matrix (Fin k) (Fin l) D.host.E).map f = 0` using `Matrix.map_zero _ (map_zero f)`. Establish `o1 : ∀ {k : ℕ}, (1 : Matrix (Fin k) (Fin k) D.host.E).map f = 1` using `Matrix.map_one _ (map_zero f) (map_one f)`. Establish `au : a * u = 1` using `by rw [ha, hu, m1, hC'C, o1]`.

Establish `cu : c * u = 0` using `by rw [hc, hu, m1, hCC, z0]`. Establish `pu : p * u = 0` using `by rw [hp, hu, m1, hPC, z0]`. Establish `au' : a * u' = 0` using `by rw [ha, hu', m1, h2, z0]`. Establish `cu' : c * u' = 1` using `by rw [hc, hu', m1, h1, o1]`. Establish `pu' : p * u' = 0` using `by rw [hp, hu', m1, hPC', z0]`.

Establish `ab : a * b = 0` using `by rw [ha, hb, m1, h3, z0]`. Establish `cb : c * b = 0` using `by rw [hc, hb, m1, hs.orth, z0]`. Establish `pb : p * b = 1` using `by rw [hp, hb, m1, hPB, o1]`. Establish `key : u * a + (b * p + u' * c) = 1`. Rewrite using `[ha, hc, hp, hu, hu', hb, m1, m1, m1, ← Matrix.map_add f (map_add f), ← Matrix.map_add f (map_add f), hid, o1]`.

Establish `fwd : ∀ (t : Mx D W.rank r) (y : Mx D W.rank r) (x : WO V' W), isoPart V W C' t + isoPart V W C y + midPart V V' W B x = t * a + y * c + x * p` using `fun _ _ _ => rfl`. Establish `back : ∀ (t : Mx D W.rank r) (y : Mx D W.rank r) (x : WO V' W), (t * a + y * c + x * p) * u = t ∧ (t * a + y * c + x * p) * u' = y ∧ (t * a + y * c + x * p) * b = x`. Introduce `t y x`. Apply the tactic sequence `refine ⟨?_, ?_, ?_⟩ <;>`. Simplify using `only [Matrix.add_mul, Matrix.mul_assoc, au, cu, pu, au', cu', pu', ab, cb, pb, Matrix.mul_one, Matrix.mul_zero, add_zero, zero_add]`.

Establish `cont : ∀ {k l m : ℕ} (Q : Mx D l m), Continuous fun z : Mx D k l => z * Q`. Introduce `k l m Q`. Use `(GlobalTheory.MixModel.continuous_sandwich (1 : Mx D k k) Q).congr fun z => ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.MixModel.sandwich_apply, Matrix.one_mul]`. Use `haveI := (GlobalTheory.MixModel.lattice_Mx D W.rank V.rank).1`.

Set `e : (Mx D W.rank r × Mx D W.rank r × WO V' W) ≃ₜ+ WO V W` to `{ toFun := fun q => isoPart V W C' q.1 + isoPart V W C q.2.1 + midPart V V' W B q.2.2 invFun := fun w => (w * u, w * u', w * b) left_inv := by`. Introduce and unpack `⟨t, y, x⟩`. Simplify using `only [fwd]`. Rewrite using `[(back t y x).1, (back t y x).2.1, (back t y x).2.2]`. Use `right_inv := by`.

Introduce `w`. Simplify using `only [fwd]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_add, Matrix.mul_assoc]`. Normalize the expressions using the abelian group laws.

Use `_ = w := by rw [key, Matrix.mul_one]`. Use the proof step `map_add' := by`. Introduce and unpack `⟨t, y, x⟩ ⟨t', y', x'⟩`. Simplify using `only [fwd, Prod.mk_add_mk, Matrix.add_mul]`. Normalize the expressions using the abelian group laws.

Use `continuous_toFun := by`. Simplify using `only [fwd]`. Conclude with `(((cont a).comp continuous_fst).add ((cont c).comp (continuous_fst.comp continuous_snd))).add ((cont p).comp (continuous_snd.comp continuous_snd))`. Use `continuous_invFun := ((cont u).prodMk ((cont u').prodMk (cont b))) }`. Use `⟨e, fun t y x => rfl, fun t y x => ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `isoPart V W C' t + isoPart V W C y + midPart V V' W B x ∈ ratL W V ↔ _`. Rewrite using `[fwd, hVr, hV'r]`. Establish `hr : ∀ {k l : ℕ} (X : Matrix (Fin k) (Fin l) D.host.E), X.map f ∈ GlobalTheory.MixModel.ratMx D k l` using `fun X => GlobalTheory.MixModel.rat_mem X`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Take `⟨b1, b2, b3⟩` from `back t y x`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← b1]`. Conclude with `GlobalTheory.MixModel.ratMx_mul h (hr C)`. Rewrite using `[← b2]`.

Conclude with `GlobalTheory.MixModel.ratMx_mul h (hr C')`. Rewrite using `[← b3]`. Conclude with `GlobalTheory.MixModel.ratMx_mul h (hr B)`. Introduce and unpack `⟨ht, hy, hx⟩`. Conclude with `add_mem (add_mem (GlobalTheory.MixModel.ratMx_mul ht (hr _)) (GlobalTheory.MixModel.ratMx_mul hy (hr _))) (GlobalTheory.MixModel.ratMx_mul hx (hr _))`.
-/
theorem decomp_exists : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∃ e : (Mx D W.rank r × Mx D W.rank r × WO V' W) ≃ₜ+ WO V W, (∀ t y x, e (t, y, x) = isoPart V W C' t + isoPart V W C y + midPart V V' W B x) ∧ ∀ t y x, e (t, y, x) ∈ ratL W V ↔ t ∈ ratMx D W.rank r ∧ y ∈ ratMx D W.rank r ∧ x ∈ ratL W V' := by
  intro D V V' W r C B hs C' h1 h2 h3
  obtain ⟨hC'C, hPC, hPC', hPB, hCC, hid⟩ := frame_relations hs h1 h2 h3
  have hV'r := GlobalTheory.MixModel.ratL_eq W V'
  have hVr := GlobalTheory.MixModel.ratL_eq W V

  set f := incA D with hf
  set a := (adj D C' * V.gram).map f with ha
  set c := (adj D C * V.gram).map f with hc
  set p := (V'.gram⁻¹ * adj D B * V.gram).map f with hp
  set u := C.map f with hu
  set u' := C'.map f with hu'
  set b := B.map f with hb
  have m1 : ∀ {k l m : ℕ} (X : Matrix (Fin k) (Fin l) D.host.E) (Y : Matrix (Fin l) (Fin m) D.host.E),
      X.map f * Y.map f = (X * Y).map f := fun X Y => (Matrix.map_mul).symm
  have z0 : ∀ {k l : ℕ}, (0 : Matrix (Fin k) (Fin l) D.host.E).map f = 0 := Matrix.map_zero _ (map_zero f)
  have o1 : ∀ {k : ℕ}, (1 : Matrix (Fin k) (Fin k) D.host.E).map f = 1 := Matrix.map_one _ (map_zero f) (map_one f)
  have au : a * u = 1 := by rw [ha, hu, m1, hC'C, o1]
  have cu : c * u = 0 := by rw [hc, hu, m1, hCC, z0]
  have pu : p * u = 0 := by rw [hp, hu, m1, hPC, z0]
  have au' : a * u' = 0 := by rw [ha, hu', m1, h2, z0]
  have cu' : c * u' = 1 := by rw [hc, hu', m1, h1, o1]
  have pu' : p * u' = 0 := by rw [hp, hu', m1, hPC', z0]
  have ab : a * b = 0 := by rw [ha, hb, m1, h3, z0]
  have cb : c * b = 0 := by rw [hc, hb, m1, hs.orth, z0]
  have pb : p * b = 1 := by rw [hp, hb, m1, hPB, o1]
  have key : u * a + (b * p + u' * c) = 1 := by
    rw [ha, hc, hp, hu, hu', hb, m1, m1, m1, ← Matrix.map_add f (map_add f), ← Matrix.map_add f (map_add f), hid, o1]

  have fwd : ∀ (t : Mx D W.rank r) (y : Mx D W.rank r) (x : WO V' W),
      isoPart V W C' t + isoPart V W C y + midPart V V' W B x = t * a + y * c + x * p := fun _ _ _ => rfl
  have back : ∀ (t : Mx D W.rank r) (y : Mx D W.rank r) (x : WO V' W),
      (t * a + y * c + x * p) * u = t ∧ (t * a + y * c + x * p) * u' = y ∧
        (t * a + y * c + x * p) * b = x := by
    intro t y x
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [Matrix.add_mul, Matrix.mul_assoc, au, cu, pu, au', cu', pu', ab, cb, pb, Matrix.mul_one,
        Matrix.mul_zero, add_zero, zero_add]
  have cont : ∀ {k l m : ℕ} (Q : Mx D l m), Continuous fun z : Mx D k l => z * Q := by
    intro k l m Q
    refine (GlobalTheory.MixModel.continuous_sandwich (1 : Mx D k k) Q).congr fun z => ?_
    rw [GlobalTheory.MixModel.sandwich_apply, Matrix.one_mul]
  haveI := (GlobalTheory.MixModel.lattice_Mx D W.rank V.rank).1
  let e : (Mx D W.rank r × Mx D W.rank r × WO V' W) ≃ₜ+ WO V W :=
    { toFun := fun q => isoPart V W C' q.1 + isoPart V W C q.2.1 + midPart V V' W B q.2.2
      invFun := fun w => (w * u, w * u', w * b)
      left_inv := by
        rintro ⟨t, y, x⟩
        simp only [fwd]
        rw [(back t y x).1, (back t y x).2.1, (back t y x).2.2]
      right_inv := by
        intro w
        simp only [fwd]
        calc w * u * a + w * u' * c + w * b * p = w * (u * a + (b * p + u' * c)) := by
              simp only [Matrix.mul_add, Matrix.mul_assoc]; abel
          _ = w := by rw [key, Matrix.mul_one]
      map_add' := by
        rintro ⟨t, y, x⟩ ⟨t', y', x'⟩
        simp only [fwd, Prod.mk_add_mk, Matrix.add_mul]
        abel
      continuous_toFun := by
        simp only [fwd]
        exact (((cont a).comp continuous_fst).add ((cont c).comp (continuous_fst.comp continuous_snd))).add
          ((cont p).comp (continuous_snd.comp continuous_snd))
      continuous_invFun := ((cont u).prodMk ((cont u').prodMk (cont b))) }
  refine ⟨e, fun t y x => rfl, fun t y x => ?_⟩
  change isoPart V W C' t + isoPart V W C y + midPart V V' W B x ∈ ratL W V ↔ _
  rw [fwd, hVr, hV'r]
  have hr : ∀ {k l : ℕ} (X : Matrix (Fin k) (Fin l) D.host.E), X.map f ∈ GlobalTheory.MixModel.ratMx D k l :=
    fun X => GlobalTheory.MixModel.rat_mem X
  constructor
  · intro h
    obtain ⟨b1, b2, b3⟩ := back t y x
    refine ⟨?_, ?_, ?_⟩
    · rw [← b1]; exact GlobalTheory.MixModel.ratMx_mul h (hr C)
    · rw [← b2]; exact GlobalTheory.MixModel.ratMx_mul h (hr C')
    · rw [← b3]; exact GlobalTheory.MixModel.ratMx_mul h (hr B)
  · rintro ⟨ht, hy, hx⟩
    exact add_mem (add_mem (GlobalTheory.MixModel.ratMx_mul ht (hr _)) (GlobalTheory.MixModel.ratMx_mul hy (hr _)))
      (GlobalTheory.MixModel.ratMx_mul hx (hr _))

end GlobalTheory.TwistDecomp

end
