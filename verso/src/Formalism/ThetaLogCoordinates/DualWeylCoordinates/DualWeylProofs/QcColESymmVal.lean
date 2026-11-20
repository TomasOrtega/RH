import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QcColHSuccLe

noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ} [NeZero n]

def qc_sh {n : ℕ} (mu : Fin n → ℤ) (ε : ℤ) : Fin n → ℤ := fun a => mu a + ε

/- English proof (translation)
Unfold `colH qc_sh`. Use `congr 1`. Use extensionality with `m`. Simplify using the standard rewrite rules.
-/
lemma qc_colH_sh {n : ℕ} (mu : Fin n → ℤ) (ε c : ℤ) : colH (qc_sh mu ε) (c + ε) = colH mu c := by
  unfold colH qc_sh
  congr 1
  ext m
  simp

/- English proof (translation)
Simplify using `[TCols, qc_sh]`.
-/
lemma qc_mem_sh (mu : Fin n → ℤ) (ε c : ℤ) : c + ε ∈ TCols (qc_sh mu ε) ↔ c ∈ TCols mu := by
  simp [TCols, qc_sh]

def qc_colE (mu : Fin n → ℤ) (ε : ℤ) : ↥(TCols mu) ≃ ↥(TCols (qc_sh mu ε)) where
  toFun c := ⟨c.1 + ε, (qc_mem_sh mu ε c.1).2 c.2⟩
  invFun c := ⟨c.1 - ε, (qc_mem_sh mu ε _).1 (by rw [sub_add_cancel]; exact c.2)⟩
  left_inv c := Subtype.ext (by simp)
  right_inv c := Subtype.ext (by simp)

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma qc_colE_val (mu : Fin n → ℤ) (ε : ℤ) (c : ↥(TCols mu)) : ((qc_colE mu ε c : ↥(TCols (qc_sh mu ε))) : ℤ) = c.1 + ε := rfl

def qc_idxE (mu : Fin n → ℤ) (ε : ℤ) : TIdx (qc_sh mu ε) ≃ TIdx mu where
  toFun I c := ⟨(I (qc_colE mu ε c)).1, (I (qc_colE mu ε c)).2.trans (qc_colH_sh mu ε c.1)⟩
  invFun I c := ⟨(I ((qc_colE mu ε).symm c)).1, (I ((qc_colE mu ε).symm c)).2.trans (by
    have := qc_colH_sh mu ε (c.1 - ε)
    rw [sub_add_cancel] at this
    exact this.symm)⟩
  left_inv I := by
    funext c
    apply Subtype.ext
    show (I (qc_colE mu ε ((qc_colE mu ε).symm c))).1 = (I c).1
    rw [Equiv.apply_symm_apply]
  right_inv I := by
    funext c
    apply Subtype.ext
    show (I ((qc_colE mu ε).symm (qc_colE mu ε c))).1 = (I c).1
    rw [Equiv.symm_apply_apply]

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma qc_idxE_val (mu : Fin n → ℤ) (ε : ℤ) (I : TIdx (qc_sh mu ε)) (c : ↥(TCols mu)) :
    (qc_idxE mu ε I c).1 = (I (qc_colE mu ε c)).1 := rfl

/- English proof (translation)
Substitute `e` using the available equality. Both sides reduce to the same expression.
-/
lemma qc_init_congr {n h h' : ℕ} (e : h = h') (hn : h ≤ n) (hn' : h' ≤ n) :
    (univ : Finset (Fin h)).map (Fin.castLEEmb hn) = (univ : Finset (Fin h')).map (Fin.castLEEmb hn') := by
  subst e; rfl

/- English proof (translation)
Use function extensionality and compare the values at `c`. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `qc_init_congr (qc_colH_sh mu ε c.1) _ _`.
-/
lemma qc_idxE_can (mu : Fin n → ℤ) (ε : ℤ) : qc_idxE mu ε (canT (qc_sh mu ε)) = canT mu := by
  funext c
  apply Subtype.ext
  exact qc_init_congr (qc_colH_sh mu ε c.1) _ _

/- English proof (translation)
The claim follows from `Subtype.ext (by show c.1 + 1 + ε = c.1 + ε + 1; ring)`.
-/
lemma qc_colE_succ (mu : Fin n → ℤ) (ε : ℤ) (c : ↥(TCols mu)) (hc : c.1 + 1 ∈ TCols mu)
    (hc' : (qc_colE mu ε c).1 + 1 ∈ TCols (qc_sh mu ε)) :
    qc_colE mu ε ⟨c.1 + 1, hc⟩ = ⟨(qc_colE mu ε c).1 + 1, hc'⟩ :=
  Subtype.ext (by show c.1 + 1 + ε = c.1 + ε + 1; ring)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h c hc t`. Establish `hc' : (qc_colE mu ε c).1 + 1 ∈ TCols (qc_sh mu ε)`. Use `(qc_mem_sh mu ε (c.1 + 1)).2 hc` as an intermediate fact. Rewrite using `[qc_colE_val]`.

Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Establish `h1` using `h (qc_colE mu ε c) hc' t`. Rewrite using `[qc_idxE_val, qc_idxE_val, qc_colE_succ mu ε c hc hc']`. Conclude with `h1`.

Introduce `h c' hc' t`. Take `⟨c, rfl⟩` from `(qc_colE mu ε).surjective c'`. Establish `hc : c.1 + 1 ∈ TCols mu`. Apply `(qc_mem_sh mu ε (c.1 + 1)).1` to reduce the goal to its premises. Rewrite `hc'` using `[qc_colE_val]`.

Use `hc' using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Establish `h1` using `h c hc t`. Rewrite `h1` using `[qc_idxE_val, qc_idxE_val, qc_colE_succ mu ε c hc hc']`. Conclude with `h1`.
-/
lemma qc_idxE_std (mu : Fin n → ℤ) (ε : ℤ) (I : TIdx (qc_sh mu ε)) : StdT I ↔ StdT (qc_idxE mu ε I) := by
  constructor
  · intro h c hc t
    have hc' : (qc_colE mu ε c).1 + 1 ∈ TCols (qc_sh mu ε) := by
      have := (qc_mem_sh mu ε (c.1 + 1)).2 hc
      rw [qc_colE_val]
      convert this using 1
      ring
    have h1 := h (qc_colE mu ε c) hc' t
    rw [qc_idxE_val, qc_idxE_val, qc_colE_succ mu ε c hc hc']
    exact h1
  · intro h c' hc' t
    obtain ⟨c, rfl⟩ := (qc_colE mu ε).surjective c'
    have hc : c.1 + 1 ∈ TCols mu := by
      apply (qc_mem_sh mu ε (c.1 + 1)).1
      rw [qc_colE_val] at hc'
      convert hc' using 1
      ring
    have h1 := h c hc t
    rw [qc_idxE_val, qc_idxE_val, qc_colE_succ mu ε c hc hc'] at h1
    exact h1

/- English proof (translation)
The claim follows from `Nat.card_congr ((qc_idxE mu ε).subtypeEquiv (qc_idxE_std mu ε))`.
-/
lemma qc_dMu_sh (mu : Fin n → ℤ) (ε : ℤ) : dMu (qc_sh mu ε) = dMu mu :=
  Nat.card_congr ((qc_idxE mu ε).subtypeEquiv (qc_idxE_std mu ε))

/- English proof (translation)
Substitute `e` using the available equality. Both sides reduce to the same expression.
-/
lemma qc_minorC_congr {n h h' : ℕ} (e : h = h') (J I : Finset (Fin n)) (hJ : J.card = h) (hI : I.card = h)
    (hJ' : J.card = h') (hI' : I.card = h') : minorC J I hJ hI = minorC J I hJ' hI' := by
  subst e; rfl

/- English proof (translation)
Unfold `TMat`. Rewrite using `[← Equiv.prod_comp (qc_colE mu ε)]`. Establish `h1 : qc_sh mu ε (lastIdx n) = ε + mu (lastIdx n)` using `add_comm _ _`. Rewrite using `[h1, zpow_add, Units.val_mul, mul_assoc]`. Use `congr 2`.

Use `Finset.prod_congr rfl fun c _ => ?_` and prove the remaining obligations. Conclude with `qc_minorC_congr (qc_colH_sh mu ε c.1) _ _ _ _ _ _`.
-/
lemma qc_TMat_sh (mu : Fin n → ℤ) (ε : ℤ) (J I : TIdx (qc_sh mu ε)) :
    TMat (qc_sh mu ε) J I =
      ((detU n ^ ε : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) * TMat mu (qc_idxE mu ε J) (qc_idxE mu ε I) := by
  unfold TMat
  rw [← Equiv.prod_comp (qc_colE mu ε)]
  have h1 : qc_sh mu ε (lastIdx n) = ε + mu (lastIdx n) := add_comm _ _
  rw [h1, zpow_add, Units.val_mul, mul_assoc]
  congr 2
  refine Finset.prod_congr rfl fun c _ => ?_
  exact qc_minorC_congr (qc_colH_sh mu ε c.1) _ _ _ _ _ _

/- English proof (translation)
Introduce `_ _ hab` and use `add_le_add_left (h hab) ε`.
-/
lemma qc_dom_sh {mu : Fin n → ℤ} (h : Dominant mu) (ε : ℤ) : Dominant (qc_sh mu ε) :=
  fun _ _ hab => add_le_add_left (h hab) ε

/- English proof (translation)
Establish `hj : ∀ j : {j : CF.J // qc_sh (CF.mu j) ε = nu}, CF.mu j.1 = qc_sh nu (-ε)`. Introduce `j`. Use function extensionality and compare the values at `a`. Use `congrFun j.2 a` as an intermediate fact. Simplify using `only [qc_sh] at this ⊢`.

Use linear arithmetic over natural numbers and integers. Establish `h1` using `((h (qc_sh nu (-ε))).map' (LinearEquiv.funCongrLeft K K e).toLinearMap (LinearEquiv.ker _)).comp (fun j : {j : CF.J // qc_sh (CF.mu j) ε = nu} => (⟨j.1, hj j⟩ : {j : CF.J // CF.mu j = qc_sh nu (-ε)})) (fun j j' hjj => Subtype.ext (congrArg (fun x => x.1) hjj))`. Establish `h2 : (fun j : {j : CF.J // qc_sh (CF.mu j) ε = nu} => fun i' : ι' => ((CF.ph j.1 (e i') (qc_idxE (CF.mu j.1) ε (canT (qc_sh (CF.mu j.1) ε))) : ℤ) : K)) = ((⇑(LinearEquiv.funCongrLeft K K e).toLinearMap ∘ fun (j : {j : CF.J // CF.mu j = qc_sh nu (-ε)}) i => ((CF.ph j.1 i (canT (CF …`. Use function extensionality and compare the values at `j i'`. Simplify using `only [qc_idxE_can]`.

Both sides reduce to the same expression. Rewrite using `[h2]`. Conclude with `h1`.
-/
lemma qc_indep_tw {K : Type} [CommRing K] {M : GLMod n} (CF : ColFam M) {ι' : Type} (e : ι' ≃ M.ι) (ε : ℤ)
    (h : ∀ nu : Fin n → ℤ, LinearIndependent K
      (fun j : {j : CF.J // CF.mu j = nu} => fun i => ((CF.ph j.1 i (canT (CF.mu j.1)) : ℤ) : K)))
    (nu : Fin n → ℤ) : LinearIndependent K
      (fun j : {j : CF.J // qc_sh (CF.mu j) ε = nu} => fun i' : ι' =>
        ((CF.ph j.1 (e i') (qc_idxE (CF.mu j.1) ε (canT (qc_sh (CF.mu j.1) ε))) : ℤ) : K)) := by
  have hj : ∀ j : {j : CF.J // qc_sh (CF.mu j) ε = nu}, CF.mu j.1 = qc_sh nu (-ε) := by
    intro j
    funext a
    have := congrFun j.2 a
    simp only [qc_sh] at this ⊢
    omega
  have h1 := ((h (qc_sh nu (-ε))).map' (LinearEquiv.funCongrLeft K K e).toLinearMap (LinearEquiv.ker _)).comp
    (fun j : {j : CF.J // qc_sh (CF.mu j) ε = nu} => (⟨j.1, hj j⟩ : {j : CF.J // CF.mu j = qc_sh nu (-ε)}))
    (fun j j' hjj => Subtype.ext (congrArg (fun x => x.1) hjj))
  have h2 : (fun j : {j : CF.J // qc_sh (CF.mu j) ε = nu} => fun i' : ι' =>
        ((CF.ph j.1 (e i') (qc_idxE (CF.mu j.1) ε (canT (qc_sh (CF.mu j.1) ε))) : ℤ) : K)) =
      ((⇑(LinearEquiv.funCongrLeft K K e).toLinearMap ∘
        fun (j : {j : CF.J // CF.mu j = qc_sh nu (-ε)}) i => ((CF.ph j.1 i (canT (CF.mu j.1)) : ℤ) : K)) ∘
        fun j : {j : CF.J // qc_sh (CF.mu j) ε = nu} => (⟨j.1, hj j⟩ : {j : CF.J // CF.mu j = qc_sh nu (-ε)})) := by
    funext j i'
    simp only [qc_idxE_can]
    rfl
  rw [h2]
  exact h1

/- English proof (translation)
Use `⟨{ J := CF.J, mu := fun j => qc_sh (CF.mu j) ε, dom := fun j => qc_dom_sh (CF.dom j) ε, ph := fun j => fun i' I' => CF.ph j (e i') (qc_idxE (CF.mu j) ε I'), equiv := ?_, indepP := ?_, indepQ := ?_, rank := ?_ }⟩` and prove the remaining obligations. Introduce `j`. Use extensionality with `i' I'`. Establish `h : ∑ k, M.A (e i') k * (Int.castRingHom (GLCoord ℤ n)) (CF.ph j k (qc_idxE (CF.mu j) ε I')) = ∑ K, (Int.castRingHom (GLCoord ℤ n)) (CF.ph j (e i') K) * TMat (CF.mu j) K (qc_idxE (CF.mu j) ε I')` using `congrFun (congrFun (CF.equiv j) (e i')) (qc_idxE (CF.mu j) ε I')`. Use `show ∑ k', M'.A i' k' * (Int.castRingHom (GLCoord ℤ n)) (CF.ph j (e k') (qc_idxE (CF.mu j) ε I')) = ∑ K', (Int.castRingHom (GLCoord ℤ n)) (CF.ph j (e i') (qc_idxE (CF.mu j) ε K')) * TMat (qc_sh (CF.mu j) ε) K' I'`.

Simplify using `only [hA, qc_TMat_sh]`. Rewrite using `[Equiv.sum_comp e (fun k => ((detU n ^ ε : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) * M.A (e i') k * (Int.castRingHom (GLCoord ℤ n)) (CF.ph j k (qc_idxE (CF.mu j) ε I'))), Equiv.sum_comp (qc_idxE (CF.mu j) ε) (fun K => (Int.castRingHom (GLCoord ℤ n)) (CF.ph j (e i') K) * (((detU n ^ ε : (G …`. Simplify using `only [mul_assoc, mul_left_comm _ ((detU n ^ ε : (GLCoord ℤ n)ˣ) : GLCoord ℤ n), ← Finset.mul_sum]`. Rewrite using `[h]`. Introduce `p hp nu`.

Conclude with `qc_indep_tw CF e ε (CF.indepP p hp) nu`. Introduce `nu`. Conclude with `qc_indep_tw CF e ε CF.indepQ nu`. Rewrite using `[Fintype.card_congr e, CF.rank]`. Conclude with `Finset.sum_congr rfl fun j _ => (qc_dMu_sh (CF.mu j) ε).symm`.
-/
theorem qc_colFam_tw (M M' : GLMod n) (ε : ℤ) (e : M'.ι ≃ M.ι)
    (hA : ∀ i j, M'.A i j = ((detU n ^ ε : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) * M.A (e i) (e j))
    (CF : ColFam M) : Nonempty (ColFam M') := by
  refine ⟨{ J := CF.J, mu := fun j => qc_sh (CF.mu j) ε, dom := fun j => qc_dom_sh (CF.dom j) ε,
            ph := fun j => fun i' I' => CF.ph j (e i') (qc_idxE (CF.mu j) ε I'),
            equiv := ?_, indepP := ?_, indepQ := ?_, rank := ?_ }⟩
  · intro j
    ext i' I'
    have h : ∑ k, M.A (e i') k * (Int.castRingHom (GLCoord ℤ n)) (CF.ph j k (qc_idxE (CF.mu j) ε I')) =
        ∑ K, (Int.castRingHom (GLCoord ℤ n)) (CF.ph j (e i') K) * TMat (CF.mu j) K (qc_idxE (CF.mu j) ε I') :=
      congrFun (congrFun (CF.equiv j) (e i')) (qc_idxE (CF.mu j) ε I')
    show ∑ k', M'.A i' k' * (Int.castRingHom (GLCoord ℤ n)) (CF.ph j (e k') (qc_idxE (CF.mu j) ε I')) =
      ∑ K', (Int.castRingHom (GLCoord ℤ n)) (CF.ph j (e i') (qc_idxE (CF.mu j) ε K')) *
        TMat (qc_sh (CF.mu j) ε) K' I'
    simp only [hA, qc_TMat_sh]
    rw [Equiv.sum_comp e (fun k => ((detU n ^ ε : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) * M.A (e i') k *
        (Int.castRingHom (GLCoord ℤ n)) (CF.ph j k (qc_idxE (CF.mu j) ε I'))),
      Equiv.sum_comp (qc_idxE (CF.mu j) ε) (fun K => (Int.castRingHom (GLCoord ℤ n)) (CF.ph j (e i') K) *
        (((detU n ^ ε : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) * TMat (CF.mu j) K (qc_idxE (CF.mu j) ε I')))]
    simp only [mul_assoc, mul_left_comm _ ((detU n ^ ε : (GLCoord ℤ n)ˣ) : GLCoord ℤ n), ← Finset.mul_sum]
    rw [h]
  · intro p hp nu
    exact qc_indep_tw CF e ε (CF.indepP p hp) nu
  · intro nu
    exact qc_indep_tw CF e ε CF.indepQ nu
  · rw [Fintype.card_congr e, CF.rank]
    exact Finset.sum_congr rfl fun j _ => (qc_dMu_sh (CF.mu j) ε).symm

end Formalism.InvariantFactorPaths.ColumnFamilies
