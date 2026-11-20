import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordTieCompEquiv
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Adapted

open IsLocalRing

variable {K : Type} [Field K] (R : Subring K) [IsLocalRing R]

/- English proof (translation)
Set `Mb : Matrix (Fin r) ι (ResidueField R)` to `Matrix.of fun i a => residue R (v a i)`. Establish `hker : LinearMap.ker (Matrix.toLin' Mb) = ⊥`. Rewrite using `[LinearMap.ker_eq_bot']`. Introduce `m hm`. Rewrite `hm` using `[Matrix.toLin'_apply]`.

Establish `hsum : ∑ a, m a • (fun i => residue R (v a i)) = 0`. Use function extensionality and compare the values at `i`. Establish `hmi` using `congrFun hm i`. Simplify using `only [Matrix.mulVec, dotProduct, Mb, Matrix.of_apply, Pi.zero_apply] at hmi`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]`.

Combine the equalities or inequalities in the displayed calculation. Use function extensionality and compare the values at `a`. Conclude with `Fintype.linearIndependent_iff.mp h m hsum a`. Take `⟨g, hg⟩` from `LinearMap.exists_leftInverse_of_injective (Matrix.toLin' Mb) hker`. Establish `hQM : LinearMap.toMatrix' g * Mb = 1`.

Rewrite using `[← LinearMap.toMatrix'_toLin' Mb, ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]`. Use `choose Q hQ using fun a i => IsLocalRing.residue_surjective (LinearMap.toMatrix' g a i)`. Use `⟨Matrix.of Q, ?_⟩` and prove the remaining obligations. Rewrite using `[← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_mul]`. Establish `e1 : (Matrix.of Q).map (residue R) = LinearMap.toMatrix' g`.

Use extensionality with `a i`. Simplify using `[hQ]`. Establish `e2 : (Matrix.of fun i a => v a i).map (residue R) = Mb`. Use extensionality with `i a`. Simplify using `[Mb]`.

Rewrite using `[e1, e2, hQM, Matrix.det_one]`. Conclude with `one_ne_zero`.
-/
theorem exists_isUnit_det_mul {ι : Type} [Fintype ι] [DecidableEq ι] {r : ℕ} (v : ι → Fin r → R)
    (h : LinearIndependent (ResidueField R) (fun a i => residue R (v a i))) :
    ∃ Q : Matrix ι (Fin r) R, IsUnit (Q * Matrix.of (fun i a => v a i)).det := by
  classical
  let Mb : Matrix (Fin r) ι (ResidueField R) := Matrix.of fun i a => residue R (v a i)
  have hker : LinearMap.ker (Matrix.toLin' Mb) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro m hm
    rw [Matrix.toLin'_apply] at hm
    have hsum : ∑ a, m a • (fun i => residue R (v a i)) = 0 := by
      funext i
      have hmi := congrFun hm i
      simp only [Matrix.mulVec, dotProduct, Mb, Matrix.of_apply, Pi.zero_apply] at hmi
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      calc ∑ a, m a * residue R (v a i) = ∑ a, residue R (v a i) * m a :=
            Finset.sum_congr rfl fun a _ => mul_comm _ _
        _ = 0 := hmi
    funext a
    exact Fintype.linearIndependent_iff.mp h m hsum a
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' Mb) hker
  have hQM : LinearMap.toMatrix' g * Mb = 1 := by
    rw [← LinearMap.toMatrix'_toLin' Mb, ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]
  choose Q hQ using fun a i => IsLocalRing.residue_surjective (LinearMap.toMatrix' g a i)
  refine ⟨Matrix.of Q, ?_⟩
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_mul]
  have e1 : (Matrix.of Q).map (residue R) = LinearMap.toMatrix' g := by
    ext a i
    simp [hQ]
  have e2 : (Matrix.of fun i a => v a i).map (residue R) = Mb := by
    ext i a
    simp [Mb]
  rw [e1, e2, hQM, Matrix.det_one]
  exact one_ne_zero

/- English proof (translation)
Take `⟨Q, hQ⟩` from `exists_isUnit_det_mul R v h`. Set `MK : Matrix (Fin r) ι K` to `Matrix.of fun i a => (v a i : K)`. Set `QK : Matrix ι (Fin r) K` to `Q.map R.subtype`. Establish `hA : QK * MK = (Q * Matrix.of fun i a => v a i).map R.subtype`. Rewrite using `[Matrix.map_mul]`.

Both sides reduce to the same expression. Establish `hdet2 : (QK * MK).det = (((Q * Matrix.of fun i a => v a i).det : R) : K)`. Rewrite using `[hA]`. Conclude with `(RingHom.map_det R.subtype _).symm`. Establish `hne : (QK * MK).det ≠ 0`.

Rewrite using `[hdet2]`. Conclude with `hQ.ne_zero` after adjusting the coercions. Establish `hu : IsUnit (QK * MK).det` using `isUnit_iff_ne_zero.mpr hne`. Establish `hinj : Function.Injective MK.mulVec`. Introduce `x y hxy`.

Establish `h2 : (QK * MK).mulVec x = (QK * MK).mulVec y`. Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hxy]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]`. Use `_ = (QK * MK)⁻¹.mulVec ((QK * MK).mulVec x) := by rw [Matrix.mulVec_mulVec]`.

Use `_ = (QK * MK)⁻¹.mulVec ((QK * MK).mulVec y) := by rw [h2]`. Use `_ = y := by rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]`. Conclude with `Matrix.mulVec_injective_iff.mp hinj`.
-/
theorem linearIndependent_of_red {ι : Type} [Fintype ι] [DecidableEq ι] {r : ℕ} (v : ι → Fin r → R)
    (h : LinearIndependent (ResidueField R) (fun a i => residue R (v a i))) :
    LinearIndependent K (fun a i => (v a i : K)) := by
  obtain ⟨Q, hQ⟩ := exists_isUnit_det_mul R v h
  let MK : Matrix (Fin r) ι K := Matrix.of fun i a => (v a i : K)
  let QK : Matrix ι (Fin r) K := Q.map R.subtype
  have hA : QK * MK = (Q * Matrix.of fun i a => v a i).map R.subtype := by
    rw [Matrix.map_mul]
    rfl
  have hdet2 : (QK * MK).det = (((Q * Matrix.of fun i a => v a i).det : R) : K) := by
    rw [hA]
    exact (RingHom.map_det R.subtype _).symm
  have hne : (QK * MK).det ≠ 0 := by
    rw [hdet2]
    exact_mod_cast hQ.ne_zero
  have hu : IsUnit (QK * MK).det := isUnit_iff_ne_zero.mpr hne
  have hinj : Function.Injective MK.mulVec := by
    intro x y hxy
    have h2 : (QK * MK).mulVec x = (QK * MK).mulVec y := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hxy]
    calc x = ((QK * MK)⁻¹ * (QK * MK)).mulVec x := by
          rw [Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
      _ = (QK * MK)⁻¹.mulVec ((QK * MK).mulVec x) := by rw [Matrix.mulVec_mulVec]
      _ = (QK * MK)⁻¹.mulVec ((QK * MK).mulVec y) := by rw [h2]
      _ = y := by rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
  exact Matrix.mulVec_injective_iff.mp hinj

/- English proof (translation)
Take `⟨Q, hQ⟩` from `exists_isUnit_det_mul R v h`. Rewrite `hQ` using `[Matrix.det_mul]`. Conclude with `isUnit_of_mul_isUnit_right hQ`.
-/
theorem isUnit_det_of_red {r : ℕ} (v : Fin r → Fin r → R)
    (h : LinearIndependent (ResidueField R) (fun a i => residue R (v a i))) :
    IsUnit (Matrix.of (fun i a => v a i)).det := by
  obtain ⟨Q, hQ⟩ := exists_isUnit_det_mul R v h
  rw [Matrix.det_mul] at hQ
  exact isUnit_of_mul_isUnit_right hQ

/- English proof (translation)
Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `c hc l`. Establish `hi : ∀ i, ∑ l', c l' * residue R (D l' i) = 0`. Introduce `i`. Use `congrFun hc i` as an intermediate fact.

Simplify `this` using `[Finset.sum_apply]`. Establish `hδ : ∀ l', residue R (∑ i, Ee l i * D l' i) = if l = l' then 1 else 0`. Introduce `l'`. Rewrite using `[h l l']`. Apply the tactic sequence `split_ifs <;> simp`.

Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun l' _ => ?_` and prove the remaining obligations. Rewrite using `[← hδ l', map_sum]`. Simplify using `only [map_mul]`. Use `_ = ∑ i, residue R (Ee l i) * ∑ l', c l' * residue R (D l' i) := by`.

Simplify using `only [Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l' _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Use `_ = 0 := by simp [hi]`.
-/
theorem red_indep {ι : Type} [Fintype ι] [DecidableEq ι] {r : ℕ} (D Ee : ι → Fin r → R)
    (h : ∀ l l', ∑ i, Ee l i * D l' i = if l = l' then 1 else 0) :
    LinearIndependent (ResidueField R) (fun l i => residue R (D l i)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc l
  have hi : ∀ i, ∑ l', c l' * residue R (D l' i) = 0 := by
    intro i
    have := congrFun hc i
    simpa [Finset.sum_apply] using this
  have hδ : ∀ l', residue R (∑ i, Ee l i * D l' i) = if l = l' then 1 else 0 := by
    intro l'
    rw [h l l']
    split_ifs <;> simp
  calc c l = ∑ l', c l' * (if l = l' then 1 else 0) := by simp
    _ = ∑ l', c l' * ∑ i, residue R (Ee l i) * residue R (D l' i) := by
        refine Finset.sum_congr rfl fun l' _ => ?_
        rw [← hδ l', map_sum]
        simp only [map_mul]
    _ = ∑ i, residue R (Ee l i) * ∑ l', c l' * residue R (D l' i) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l' _ => ?_
        ring
    _ = 0 := by simp [hi]

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Set `q' : Fin k → M` to `fun j => if hj : (j : ℕ) < r then q ⟨j, hj⟩ else 0`. Establish `hS : Submodule.span F (q '' {a : Fin r | (a : ℕ) < k}) ≤ Submodule.span F (Set.range q')`. Apply `Submodule.span_le.mpr` to reduce the goal to its premises.

Introduce and unpack `_ ⟨a, ha, rfl⟩`. Apply `Submodule.subset_span` to reduce the goal to its premises. Use `⟨⟨a, ha⟩, ?_⟩` and prove the remaining obligations. Simplify using `[q', a.2]`. Establish `hW : Submodule.span F (Set.range w) ≤ Submodule.span F (Set.range q')`.

Apply `Submodule.span_le.mpr` to reduce the goal to its premises. Introduce and unpack `_ ⟨l, rfl⟩`. Conclude with `hS (hcon l)`. Establish `h2 : Module.finrank F (Submodule.span F (Set.range w)) = k + 1`. Rewrite using `[finrank_span_eq_card hw, Fintype.card_fin]`.

Establish `h3` using `Submodule.finrank_mono hW`. Establish `h4 : Module.finrank F (Submodule.span F (Set.range q')) ≤ k`. Use `finrank_range_le_card (R := F) q'` as an intermediate fact. Rewrite `this` using `[Fintype.card_fin]`. Conclude with `this`.

Use linear arithmetic over natural numbers and integers.
-/
theorem exists_notMem_span {F M : Type} [Field F] [AddCommGroup M] [Module F M] [FiniteDimensional F M]
    {r k : ℕ} (q : Fin r → M) (w : Fin (k + 1) → M) (hw : LinearIndependent F w) :
    ∃ l, w l ∉ Submodule.span F (q '' {a : Fin r | (a : ℕ) < k}) := by
  classical
  by_contra hcon
  push_neg at hcon
  let q' : Fin k → M := fun j => if hj : (j : ℕ) < r then q ⟨j, hj⟩ else 0
  have hS : Submodule.span F (q '' {a : Fin r | (a : ℕ) < k}) ≤ Submodule.span F (Set.range q') := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, rfl⟩
    apply Submodule.subset_span
    refine ⟨⟨a, ha⟩, ?_⟩
    simp [q', a.2]
  have hW : Submodule.span F (Set.range w) ≤ Submodule.span F (Set.range q') := by
    apply Submodule.span_le.mpr
    rintro _ ⟨l, rfl⟩
    exact hS (hcon l)
  have h2 : Module.finrank F (Submodule.span F (Set.range w)) = k + 1 := by
    rw [finrank_span_eq_card hw, Fintype.card_fin]
  have h3 := Submodule.finrank_mono hW
  have h4 : Module.finrank F (Submodule.span F (Set.range q')) ≤ k := by
    have := finrank_range_le_card (R := F) q'
    rw [Fintype.card_fin] at this
    exact this
  omega

/- English proof (translation)
Establish `hs : {a : Fin r | (a : ℕ) < i} = {a : Fin r | (a : ℕ) < r}`. Use extensionality with `a`. Simplify using `only [Set.mem_setOf_eq]`. Conclude with `⟨fun _ => a.2, fun _ => lt_of_lt_of_le a.2 h⟩`. Use `show Submodule.span K (b '' {a : Fin r | (a : ℕ) < i}) = Submodule.span K (b '' {a : Fin r | (a : ℕ) < r})`.

Rewrite using `[hs]`.
-/
theorem flagStep_of_le {E : Type} [AddCommGroup E] [Module K E] {r : ℕ} (b : Fin r → E) {i : ℕ} (h : r ≤ i) :
    flagStep K b i = flagStep K b r := by
  have hs : {a : Fin r | (a : ℕ) < i} = {a : Fin r | (a : ℕ) < r} := by
    ext a
    simp only [Set.mem_setOf_eq]
    exact ⟨fun _ => a.2, fun _ => lt_of_lt_of_le a.2 h⟩
  show Submodule.span K (b '' {a : Fin r | (a : ℕ) < i}) = Submodule.span K (b '' {a : Fin r | (a : ℕ) < r})
  rw [hs]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Establish `e : {a : Fin r | (a : ℕ) < 0} = ∅`. Use extensionality with `a`. Simplify using the standard rewrite rules.

Use `⟨fun _ _ => 0, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[e]`. Conclude with `linearIndepOn_empty _ _`. Introduce `i hi`. Take `rfl : i = 0` from `Nat.le_zero.mp hi`.

Use `show Submodule.span K (_ '' {a : Fin r | (a : ℕ) < 0}) = Submodule.span K (g '' {a : Fin r | (a : ℕ) < 0})`. Rewrite using `[e, Set.image_empty, Set.image_empty]`. Consider the case `succ k ih`. Establish `hkr : k < r` using `hk`. Establish `hk1 : k + 1 ≤ r` using `hk`.

Take `⟨p, hind, hfl⟩` from `ih hkr.le`. Take `⟨D, Ee, hD, hE, hDE, hspan⟩` from `H ⟨k, hkr⟩`. Set `D' : Fin (k + 1) → Fin r → R` to `fun l i => ⟨D l i, hD l i⟩`. Set `E' : Fin (k + 1) → Fin r → R` to `fun l i => ⟨Ee l i, hE l i⟩`. Establish `hDE' : ∀ l l', ∑ i, E' l i * D' l' i = if l = l' then 1 else 0`.

Introduce `l l'`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `hll` using `hDE l l'`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hll]`.

Apply the tactic sequence `split_ifs <;> simp`. Establish `hred : LinearIndependent (ResidueField R) (fun l i => residue R (D' l i))` using `red_indep R D' E' hDE'`. Take `⟨l, hl⟩` from `exists_notMem_span (fun a i => residue R (p a i)) (fun l i => residue R (D' l i)) hred`. Set `kk : Fin r` to `⟨k, hkr⟩`. Set `p' : Fin r → Fin r → R` to `Function.update p kk (D' l)`.

Establish `hold : ∀ a : Fin r, (a : ℕ) < k → p' a = p a`. Introduce `a ha`. Apply `Function.update_of_ne` to reduce the goal to its premises. Introduce `hak`. Rewrite `ha` using `[hak]`.

Conclude with `lt_irrefl k ha`. Establish `hnew : p' kk = D' l` using `Function.update_self kk (D' l) p`. Establish `heq : Set.EqOn (fun a i => residue R (p' a i)) (fun a i => residue R (p a i)) {a : Fin r | (a : ℕ) < k}`. Introduce `a ha`. Simplify using `only [hold a ha]`.

Establish `hset : {a : Fin r | (a : ℕ) < k + 1} = insert kk {a : Fin r | (a : ℕ) < k}`. Use extensionality with `a`. Simplify using `only [Set.mem_setOf_eq, Set.mem_insert_iff, kk, Fin.ext_iff]`. Use linear arithmetic over natural numbers and integers. Establish `hon : LinearIndepOn (ResidueField R) (fun a i => residue R (p' a i)) {a : Fin r | (a : ℕ) < k + 1}`.

Rewrite using `[hset]`. Apply `LinearIndepOn.insert` to reduce the goal to its premises. Conclude with `hind.congr heq.symm`. Rewrite using `[heq.image_eq] show (fun i => residue R (p' kk i)) ∉ _`. Rewrite using `[hnew]`.

Conclude with `hl`. Use `⟨p', hon, ?_⟩` and prove the remaining obligations. Introduce `i hi`. Break down `Nat.lt_or_eq_of_le hi with hi' | rfl` into its components or cases. Establish `hik : i ≤ k` using `Nat.lt_succ_iff.mp hi'`.

Rewrite using `[← hfl i hik]`. Use `show Submodule.span K ((fun a j => (p' a j : K)) '' {a : Fin r | (a : ℕ) < i}) = Submodule.span K ((fun a j => (p a j : K)) '' {a : Fin r | (a : ℕ) < i})`. Use `congr 1`. Apply `Set.EqOn.image_eq` to reduce the goal to its premises. Introduce `a ha`.

Establish `ha' : (a : ℕ) < k` using `lt_of_lt_of_le ha hik`. Simplify using `only [hold a ha']`. Establish `hsub : {x : Fin r | (x : ℕ) < k} ⊆ {x : Fin r | (x : ℕ) < k + 1}` using `fun x hx => Nat.lt_succ_of_lt hx`. Establish `hle : flagStep K (fun a j => (p' a j : K)) (k + 1) ≤ flagStep K g (k + 1)` using `by show Submodule.span K ((fun a j => (p' a j : K)) '' {a : Fin r | (a : ℕ) < k + 1}) ≤ _`. Apply `Submodule.span_le.mpr` to reduce the goal to its premises.

Introduce and unpack `_ ⟨a, ha, rfl⟩`. Establish `ha' : (a : ℕ) < k + 1` using `ha`. Break down `Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp ha') with hak | hak` into its components or cases. Establish `h1 : (fun j => (p' a j : K)) ∈ flagStep K (fun a j => (p a j : K)) k`. Rewrite using `[hold a hak]`.

Conclude with `Submodule.subset_span ⟨a, hak, rfl⟩`. Rewrite `h1` using `[hfl k le_rfl]`. Establish `himg : g '' {x : Fin r | (x : ℕ) < k} ⊆ g '' {x : Fin r | (x : ℕ) < k + 1}`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `⟨x, hsub hx, rfl⟩`.

Conclude with `Submodule.span_mono himg h1`. Establish `hakk : a = kk` using `Fin.ext hak`. Establish `hD` using `hspan l`. Use `show (fun j => (p' a j : K)) ∈ flagStep K g (k + 1)`. Rewrite using `[hakk, hnew]`.

Conclude with `hD`. Establish `hrg : g '' {a : Fin r | (a : ℕ) < k + 1} = Set.range (fun j : Fin (k + 1) => g ⟨j, lt_of_lt_of_le j.2 hk1⟩)`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha, rfl⟩`.

Conclude with `⟨⟨a, ha⟩, rfl⟩`. Introduce and unpack `⟨j, rfl⟩`. Conclude with `⟨_, j.2, rfl⟩`. Establish `hg_le : Module.finrank K (flagStep K g (k + 1)) ≤ k + 1`. Establish `hc` using `finrank_range_le_card (R := K) (fun j : Fin (k + 1) => g ⟨j, lt_of_lt_of_le j.2 hk1⟩)`.

Rewrite `hc` using `[Fintype.card_fin]`. Use `show Module.finrank K (Submodule.span K (g '' {a : Fin r | (a : ℕ) < k + 1})) ≤ k + 1`. Rewrite using `[hrg]`. Conclude with `hc`. Establish `hrp : (fun a j => (p' a j : K)) '' {a : Fin r | (a : ℕ) < k + 1} = Set.range (fun j : Fin (k + 1) => fun i => (p' ⟨j, lt_of_lt_of_le j.2 hk1⟩ i : K))`.

Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha, rfl⟩`. Conclude with `⟨⟨a, ha⟩, rfl⟩`. Introduce and unpack `⟨j, rfl⟩`.

Conclude with `⟨_, j.2, rfl⟩`. Establish `hindK : LinearIndependent K (fun j : Fin (k + 1) => fun i => (p' ⟨j, lt_of_lt_of_le j.2 hk1⟩ i : K))`. Apply `linearIndependent_of_red R (fun j : Fin (k + 1) => p' ⟨j, lt_of_lt_of_le j.2 hk1⟩)` to reduce the goal to its premises. Establish `hsubt` using `hon.linearIndependent`. Use `hsubt.comp (fun j : Fin (k + 1) => (⟨⟨j, lt_of_lt_of_le j.2 hk1⟩, j.2⟩ : {a : Fin r | (a : ℕ) < k + 1})) ?_` and prove the remaining obligations.

Introduce `x y hxy`. Conclude with `Fin.ext (congrArg (fun z : {a : Fin r | (a : ℕ) < k + 1} => ((z : Fin r) : ℕ)) hxy)`. Establish `hp_eq : Module.finrank K (flagStep K (fun a j => (p' a j : K)) (k + 1)) = k + 1` using `by show Module.finrank K (Submodule.span K ((fun a j => (p' a j : K)) '' {a : Fin r | (a : ℕ) < k + 1})) = k + 1`. Rewrite using `[hrp, finrank_span_eq_card hindK, Fintype.card_fin]`. Apply `Submodule.eq_of_le_of_finrank_le hle` to reduce the goal to its premises.

Rewrite using `[hp_eq]`. Conclude with `hg_le`.
-/
theorem exists_cols {r : ℕ} (g : Fin r → Fin r → K)
    (H : ∀ k : Fin r, ∃ D Ee : Fin ((k : ℕ) + 1) → Fin r → K, (∀ l i, D l i ∈ R) ∧ (∀ l i, Ee l i ∈ R) ∧
      (∀ l l', ∑ i, Ee l i * D l' i = if l = l' then 1 else 0) ∧ ∀ l, D l ∈ flagStep K g ((k : ℕ) + 1))
    (k : ℕ) (hk : k ≤ r) :
    ∃ p : Fin r → Fin r → R,
      LinearIndepOn (ResidueField R) (fun a i => residue R (p a i)) {a : Fin r | (a : ℕ) < k} ∧
      ∀ i ≤ k, flagStep K (fun a j => (p a j : K)) i = flagStep K g i := by
  induction k with
  | zero =>
    have e : {a : Fin r | (a : ℕ) < 0} = ∅ := by
      ext a
      simp
    refine ⟨fun _ _ => 0, ?_, ?_⟩
    · rw [e]
      exact linearIndepOn_empty _ _
    · intro i hi
      obtain rfl : i = 0 := Nat.le_zero.mp hi
      show Submodule.span K (_ '' {a : Fin r | (a : ℕ) < 0}) = Submodule.span K (g '' {a : Fin r | (a : ℕ) < 0})
      rw [e, Set.image_empty, Set.image_empty]
  | succ k ih =>
    have hkr : k < r := hk
    have hk1 : k + 1 ≤ r := hk
    obtain ⟨p, hind, hfl⟩ := ih hkr.le
    obtain ⟨D, Ee, hD, hE, hDE, hspan⟩ := H ⟨k, hkr⟩
    let D' : Fin (k + 1) → Fin r → R := fun l i => ⟨D l i, hD l i⟩
    let E' : Fin (k + 1) → Fin r → R := fun l i => ⟨Ee l i, hE l i⟩
    have hDE' : ∀ l l', ∑ i, E' l i * D' l' i = if l = l' then 1 else 0 := by
      intro l l'
      apply Subtype.ext
      have hll := hDE l l'
      calc ((∑ i, E' l i * D' l' i : R) : K) = ∑ i, Ee l i * D l' i := by simp [E', D']
        _ = _ := by
          rw [hll]
          split_ifs <;> simp
    have hred : LinearIndependent (ResidueField R) (fun l i => residue R (D' l i)) :=
      red_indep R D' E' hDE'
    obtain ⟨l, hl⟩ := exists_notMem_span (fun a i => residue R (p a i)) (fun l i => residue R (D' l i)) hred
    let kk : Fin r := ⟨k, hkr⟩
    let p' : Fin r → Fin r → R := Function.update p kk (D' l)
    have hold : ∀ a : Fin r, (a : ℕ) < k → p' a = p a := by
      intro a ha
      apply Function.update_of_ne
      intro hak
      rw [hak] at ha
      exact lt_irrefl k ha
    have hnew : p' kk = D' l := Function.update_self kk (D' l) p
    have heq : Set.EqOn (fun a i => residue R (p' a i)) (fun a i => residue R (p a i))
        {a : Fin r | (a : ℕ) < k} := by
      intro a ha
      simp only [hold a ha]
    have hset : {a : Fin r | (a : ℕ) < k + 1} = insert kk {a : Fin r | (a : ℕ) < k} := by
      ext a
      simp only [Set.mem_setOf_eq, Set.mem_insert_iff, kk, Fin.ext_iff]
      omega
    have hon : LinearIndepOn (ResidueField R) (fun a i => residue R (p' a i)) {a : Fin r | (a : ℕ) < k + 1} := by
      rw [hset]
      apply LinearIndepOn.insert
      · exact hind.congr heq.symm
      · rw [heq.image_eq]
        show (fun i => residue R (p' kk i)) ∉ _
        rw [hnew]
        exact hl
    refine ⟨p', hon, ?_⟩
    intro i hi
    rcases Nat.lt_or_eq_of_le hi with hi' | rfl
    · have hik : i ≤ k := Nat.lt_succ_iff.mp hi'
      rw [← hfl i hik]
      show Submodule.span K ((fun a j => (p' a j : K)) '' {a : Fin r | (a : ℕ) < i}) =
        Submodule.span K ((fun a j => (p a j : K)) '' {a : Fin r | (a : ℕ) < i})
      congr 1
      apply Set.EqOn.image_eq
      intro a ha
      have ha' : (a : ℕ) < k := lt_of_lt_of_le ha hik
      simp only [hold a ha']
    · have hsub : {x : Fin r | (x : ℕ) < k} ⊆ {x : Fin r | (x : ℕ) < k + 1} :=
        fun x hx => Nat.lt_succ_of_lt hx
      have hle : flagStep K (fun a j => (p' a j : K)) (k + 1) ≤ flagStep K g (k + 1) := by
        show Submodule.span K ((fun a j => (p' a j : K)) '' {a : Fin r | (a : ℕ) < k + 1}) ≤ _
        apply Submodule.span_le.mpr
        rintro _ ⟨a, ha, rfl⟩
        have ha' : (a : ℕ) < k + 1 := ha
        rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp ha') with hak | hak
        · have h1 : (fun j => (p' a j : K)) ∈ flagStep K (fun a j => (p a j : K)) k := by
            rw [hold a hak]
            exact Submodule.subset_span ⟨a, hak, rfl⟩
          rw [hfl k le_rfl] at h1
          have himg : g '' {x : Fin r | (x : ℕ) < k} ⊆ g '' {x : Fin r | (x : ℕ) < k + 1} :=
            by
              rintro _ ⟨x, hx, rfl⟩
              exact ⟨x, hsub hx, rfl⟩
          exact Submodule.span_mono himg h1
        · have hakk : a = kk := Fin.ext hak
          have hD := hspan l
          show (fun j => (p' a j : K)) ∈ flagStep K g (k + 1)
          rw [hakk, hnew]
          exact hD
      have hrg : g '' {a : Fin r | (a : ℕ) < k + 1} =
          Set.range (fun j : Fin (k + 1) => g ⟨j, lt_of_lt_of_le j.2 hk1⟩) := by
        ext x
        constructor
        · rintro ⟨a, ha, rfl⟩
          exact ⟨⟨a, ha⟩, rfl⟩
        · rintro ⟨j, rfl⟩
          exact ⟨_, j.2, rfl⟩
      have hg_le : Module.finrank K (flagStep K g (k + 1)) ≤ k + 1 := by
        have hc := finrank_range_le_card (R := K) (fun j : Fin (k + 1) => g ⟨j, lt_of_lt_of_le j.2 hk1⟩)
        rw [Fintype.card_fin] at hc
        show Module.finrank K (Submodule.span K (g '' {a : Fin r | (a : ℕ) < k + 1})) ≤ k + 1
        rw [hrg]
        exact hc
      have hrp : (fun a j => (p' a j : K)) '' {a : Fin r | (a : ℕ) < k + 1} =
          Set.range (fun j : Fin (k + 1) => fun i => (p' ⟨j, lt_of_lt_of_le j.2 hk1⟩ i : K)) := by
        ext x
        constructor
        · rintro ⟨a, ha, rfl⟩
          exact ⟨⟨a, ha⟩, rfl⟩
        · rintro ⟨j, rfl⟩
          exact ⟨_, j.2, rfl⟩
      have hindK : LinearIndependent K
          (fun j : Fin (k + 1) => fun i => (p' ⟨j, lt_of_lt_of_le j.2 hk1⟩ i : K)) := by
        apply linearIndependent_of_red R (fun j : Fin (k + 1) => p' ⟨j, lt_of_lt_of_le j.2 hk1⟩)
        have hsubt := hon.linearIndependent
        refine hsubt.comp (fun j : Fin (k + 1) =>
          (⟨⟨j, lt_of_lt_of_le j.2 hk1⟩, j.2⟩ : {a : Fin r | (a : ℕ) < k + 1})) ?_
        intro x y hxy
        exact Fin.ext (congrArg (fun z : {a : Fin r | (a : ℕ) < k + 1} => ((z : Fin r) : ℕ)) hxy)
      have hp_eq : Module.finrank K (flagStep K (fun a j => (p' a j : K)) (k + 1)) = k + 1 := by
        show Module.finrank K (Submodule.span K ((fun a j => (p' a j : K)) '' {a : Fin r | (a : ℕ) < k + 1})) = k + 1
        rw [hrp, finrank_span_eq_card hindK, Fintype.card_fin]
      apply Submodule.eq_of_le_of_finrank_le hle
      rw [hp_eq]
      exact hg_le

/- English proof (translation)
Introduce `K _ R _ r g H`. Take `⟨p, hind, hfl⟩` from `exists_cols R g H r le_rfl`. Establish `hS : {a : Fin r | (a : ℕ) < r} = Set.univ`. Use extensionality with `a`. Simplify using `[a.2]`.

Rewrite `hind` using `[hS, linearIndepOn_univ]`. Take `⟨u, hu⟩` from `isUnit_det_of_red R p hind`. Establish `hdet : (R.subtype.mapMatrix (Matrix.of fun i a => p a i)).det = (((Matrix.of fun i a => p a i).det : R) : K)` using `(RingHom.map_det R.subtype _).symm`. Use `⟨R.subtype.mapMatrix (Matrix.of fun i a => p a i), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `a b`.

Conclude with `(p b a).2`. Rewrite using `[hdet, ← hu]`. Conclude with `u.ne_zero` after adjusting the coercions. Rewrite using `[hdet, ← hu]`. Establish `hmul : ((u : R) : K) * (((u⁻¹ : Rˣ) : R) : K) = 1`.

Rewrite using `[← Subring.coe_mul, Units.mul_inv]`. Both sides reduce to the same expression. Rewrite using `[inv_eq_of_mul_eq_one_right hmul]`. Conclude with `((u⁻¹ : Rˣ) : R).2`. Introduce `i show flagStep K (fun a j => (p a j : K)) i = flagStep K g i`.

Distinguish the cases in `hi : i ≤ r`. Conclude with `hfl i hi`. Use `push_neg at hi`. Rewrite using `[flagStep_of_le _ hi.le, flagStep_of_le g hi.le]`. Conclude with `hfl r le_rfl`.
-/
theorem exists_adapted : ∀ (K : Type) [Field K] (R : Subring K) [IsLocalRing R] (r : ℕ) (g : Fin r → Fin r → K),
    (∀ k : Fin r, ∃ D Ee : Fin ((k : ℕ) + 1) → Fin r → K, (∀ l i, D l i ∈ R) ∧ (∀ l i, Ee l i ∈ R) ∧
      (∀ l l', ∑ i, Ee l i * D l' i = if l = l' then 1 else 0) ∧ ∀ l, D l ∈ flagStep K g ((k : ℕ) + 1)) →
    ∃ P : Matrix (Fin r) (Fin r) K, (∀ a b, P a b ∈ R) ∧ P.det ≠ 0 ∧ P.det⁻¹ ∈ R ∧
      ∀ i, flagStep K (fun k a => P a k) i = flagStep K g i := by
  intro K _ R _ r g H
  obtain ⟨p, hind, hfl⟩ := exists_cols R g H r le_rfl
  have hS : {a : Fin r | (a : ℕ) < r} = Set.univ := by
    ext a
    simp [a.2]
  rw [hS, linearIndepOn_univ] at hind
  obtain ⟨u, hu⟩ := isUnit_det_of_red R p hind
  have hdet : (R.subtype.mapMatrix (Matrix.of fun i a => p a i)).det =
      (((Matrix.of fun i a => p a i).det : R) : K) :=
    (RingHom.map_det R.subtype _).symm
  refine ⟨R.subtype.mapMatrix (Matrix.of fun i a => p a i), ?_, ?_, ?_, ?_⟩
  · intro a b
    exact (p b a).2
  · rw [hdet, ← hu]
    exact_mod_cast u.ne_zero
  · rw [hdet, ← hu]
    have hmul : ((u : R) : K) * (((u⁻¹ : Rˣ) : R) : K) = 1 := by
      rw [← Subring.coe_mul, Units.mul_inv]
      rfl
    rw [inv_eq_of_mul_eq_one_right hmul]
    exact ((u⁻¹ : Rˣ) : R).2
  · intro i
    show flagStep K (fun a j => (p a j : K)) i = flagStep K g i
    by_cases hi : i ≤ r
    · exact hfl i hi
    · push_neg at hi
      rw [flagStep_of_le _ hi.le, flagStep_of_le g hi.le]
      exact hfl r le_rfl

end GlobalTheory.CompanionTheory.Ar.FlagBun.Adapted
