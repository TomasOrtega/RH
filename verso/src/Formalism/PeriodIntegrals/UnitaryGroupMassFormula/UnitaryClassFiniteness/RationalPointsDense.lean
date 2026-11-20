import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.IsIntegralOfIntOE

noncomputable section

open Matrix NumberField IsDedekindDomain
open scoped TensorProduct

namespace PI.UnitaryGroupMassFormula.UJClassFin

open PI.UJClassFin

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {M : ℕ}

/- English proof (translation)
Use function extensionality and compare the values at `i`. Distinguish the cases in `h : i = l`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, h]`.
-/
theorem single_tmul (l : Fin M) (a : Af F) (t : E) :
    Pi.single l (a ⊗ₜ[F] t) = fun i => a ⊗ₜ[F] ((Pi.single l t : Fin M → E) i) := by
  funext i
  by_cases h : i = l
  · subst h
    simp
  · simp [Pi.single_apply, h]

/- English proof (translation)
Use `first`. Consider the case `(rw [Nat.cast_smul_eq_nsmul, TensorProduct.tmul_smul])`. Consider the case `(induction N with`. Consider the case `zero => simp`. Consider the case `succ n ih => simp [succ_nsmul, ih, add_smul, TensorProduct.tmul_add])`.
-/
theorem nsmul_tmul_F (N : ℕ) (a : Af F) (e : E) : N • (a ⊗ₜ[F] e) = a ⊗ₜ[F] ((N : F) • e) := by
  first
  | (rw [Nat.cast_smul_eq_nsmul, TensorProduct.tmul_smul])
  | (induction N with
      | zero => simp
      | succ n ih => simp [succ_nsmul, ih, add_smul, TensorProduct.tmul_add])

/- English proof (translation)
Use function extensionality and compare the values at `l`. Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply]`.
-/
theorem mulVec_single' (g : Matrix (Fin M) (Fin M) (Af F ⊗[F] E)) (j : Fin M) (x : Af F ⊗[F] E) :
    g.mulVec (Pi.single j x) = fun l => g l j * x := by
  funext l
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

/- English proof (translation)
Unfold `latHat at hy ⊢`. Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨a', ha', x, hx, rfl⟩` from `hy`. Apply `AddSubgroup.subset_closure` to reduce the goal to its premises.

Establish `hmul : a * a' ∈ intAf F`. Unfold `intAf at ha ha' ⊢`. Introduce `v`. Rewrite using `[map_mul]`. Conclude with `mul_mem (ha v) (ha' v)`.

Use `⟨a * a', hmul, x, hx, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Simplify using `[Pi.smul_apply, Algebra.TensorProduct.tmul_mul_tmul]`. Consider the case `zero => rw [smul_zero]`. Conclude with `zero_mem _`.

Consider the case `add y1 y2 _ _ h1 h2 => rw [smul_add]`. Conclude with `add_mem h1 h2`. Consider the case `neg y _ h => rw [smul_neg]`. Conclude with `neg_mem h`.
-/
theorem latHat_smul (L : Set (Fin M → E)) {a : Af F} (ha : a ∈ intAf F) {y : Fin M → Af F ⊗[F] E}
    (hy : y ∈ latHat F E L) : (a ⊗ₜ[F] (1 : E)) • y ∈ latHat F E L := by
  unfold latHat at hy ⊢
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a', ha', x, hx, rfl⟩ := hy
    apply AddSubgroup.subset_closure
    have hmul : a * a' ∈ intAf F := by
      unfold intAf at ha ha' ⊢
      intro v
      rw [map_mul]
      exact mul_mem (ha v) (ha' v)
    refine ⟨a * a', hmul, x, hx, ?_⟩
    funext i
    simp [Pi.smul_apply, Algebra.TensorProduct.tmul_mul_tmul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add y1 y2 _ _ h1 h2 => rw [smul_add]; exact add_mem h1 h2
  | neg y _ h => rw [smul_neg]; exact neg_mem h

/- English proof (translation)
Set `S' : AddSubgroup (Af F ⊗[F] E)` to `{ carrier := {q | Pi.single l (k • q) ∈ latHat F E L} add_mem' := fun {a b} ha hb => by show Pi.single l (k • (a + b)) ∈ latHat F E L`. Rewrite using `[smul_add, Pi.single_add]`. Conclude with `add_mem ha hb`. Use the proof step `zero_mem' := by show Pi.single l (k • (0 : Af F ⊗[F] E)) ∈ latHat F E L`. Rewrite using `[smul_zero, Pi.single_zero]`.

Conclude with `zero_mem _`. Use the proof step `neg_mem' := fun {a} ha => by show Pi.single l (k • (-a)) ∈ latHat F E L`. Rewrite using `[smul_neg, Pi.single_neg]`. Conclude with `neg_mem ha }`. Establish `hsub : {r : Af F ⊗[F] E | ∃ a ∈ intAf F, ∃ e : E, IsIntegral ℤ e ∧ r = a ⊗ₜ[F] e} ⊆ (S' : Set _)`.

Introduce and unpack `r ⟨a, ha, e, he, rfl⟩`. Use `show Pi.single l (k • (a ⊗ₜ[F] e)) ∈ latHat F E L`. Rewrite using `[nsmul_tmul_F, single_tmul]`. Unfold `latHat`. Conclude with `AddSubgroup.subset_closure ⟨a, ha, Pi.single l ((k : F) • e), hk l e he, rfl⟩`.

Conclude with `(AddSubgroup.closure_le S').mpr hsub hp`.
-/
theorem single_mem (L : Set (Fin M → E)) {k : ℕ}
    (hk : ∀ i, ∀ e : E, IsIntegral ℤ e → Pi.single i ((k : F) • e) ∈ L)
    {p : Af F ⊗[F] E} (hp : p ∈ Oh F E) (l : Fin M) : Pi.single l (k • p) ∈ latHat F E L := by
  let S' : AddSubgroup (Af F ⊗[F] E) :=
    { carrier := {q | Pi.single l (k • q) ∈ latHat F E L}
      add_mem' := fun {a b} ha hb => by
        show Pi.single l (k • (a + b)) ∈ latHat F E L
        rw [smul_add, Pi.single_add]
        exact add_mem ha hb
      zero_mem' := by
        show Pi.single l (k • (0 : Af F ⊗[F] E)) ∈ latHat F E L
        rw [smul_zero, Pi.single_zero]
        exact zero_mem _
      neg_mem' := fun {a} ha => by
        show Pi.single l (k • (-a)) ∈ latHat F E L
        rw [smul_neg, Pi.single_neg]
        exact neg_mem ha }
  have hsub : {r : Af F ⊗[F] E | ∃ a ∈ intAf F, ∃ e : E, IsIntegral ℤ e ∧ r = a ⊗ₜ[F] e} ⊆
      (S' : Set _) := by
    rintro r ⟨a, ha, e, he, rfl⟩
    show Pi.single l (k • (a ⊗ₜ[F] e)) ∈ latHat F E L
    rw [nsmul_tmul_F, single_tmul]
    unfold latHat
    exact AddSubgroup.subset_closure ⟨a, ha, Pi.single l ((k : F) • e), hk l e he, rfl⟩
  exact (AddSubgroup.closure_le S').mpr hsub hp

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ M J L _h4 h5 h y`. Take `⟨k, hk, hkL⟩` from `low_nat L h5`. Use `set g' := finMat σ J h⁻¹ with hg'`. Establish `hden : ∃ m : ℕ, 0 < m ∧ ∀ l j, m • g' l j ∈ Oh F E` using `by choose mf hmf hmO using fun p : Fin M × Fin M => den (g' p.1 p.2)`. Use `⟨∏ p, mf p, Finset.prod_pos (fun p _ => hmf p), fun l j => ?_⟩` and prove the remaining obligations.

Take `⟨q, hq⟩` from `Finset.dvd_prod_of_mem mf (Finset.mem_univ (l, j))`. Rewrite using `[hq, mul_comm, mul_smul]`. Conclude with `AddSubgroup.nsmul_mem _ (hmO (l, j)) _`. Take `⟨m, hm, hmO⟩` from `hden`. Establish `K1 : ∀ o ∈ Oh F E, ∀ j, g'.mulVec (Pi.single j ((k * m) • o)) ∈ latHat F E L`.

Introduce `o ho j`. Rewrite using `[mulVec_single']`. Establish `: (fun l => g' l j * ((k * m) • o)) = ∑ l, Pi.single l (k • ((m • g' l j) * o))`. Rewrite using `[Finset.univ_sum_single (fun l => k • ((m • g' l j) * o))]`. Use function extensionality and compare the values at `l`.

Rewrite using `[mul_smul_comm, smul_mul_assoc, smul_smul]`. Rewrite using `[this]`. Conclude with `AddSubgroup.sum_mem _ (fun l _ => single_mem L hkL (Oh_mul (hmO l j) ho) l)`. Establish `SL : ∀ p ∈ Oh F E, ∀ j, Pi.single j ((k * m) • p) ∈ latHat F E (abelian₂ σ J L h)`. Introduce `p hp j`.

Proceed by induction on `hp using AddSubgroup.closure_induction with`. Consider the case `mem p hp`. Take `⟨a, ha, e, he, rfl⟩` from `hp`. Rewrite using `[nsmul_tmul_F, single_tmul]`. Use `AddSubgroup.subset_closure ⟨a, ha, _, ?_, rfl⟩` and prove the remaining obligations.

Use `show g'.mulVec (vinc (Pi.single j (((k * m : ℕ) : F) • e))) ∈ latHat F E L`. Establish `hv : vinc (F` using `F) (Pi.single j (((k * m : ℕ) : F) • e)) = Pi.single j ((k * m) • ((1 : Af F) ⊗ₜ[F] e)) := by`. Rewrite using `[nsmul_tmul_F, single_tmul]`. Both sides reduce to the same expression. Rewrite using `[hv]`.

Conclude with `K1 _ (tmul_mem_Oh intAf_one he) j`. Consider the case `zero => rw [smul_zero, Pi.single_zero]`. Conclude with `zero_mem _`. Consider the case `add p q _ _ h1 h2 => rw [smul_add, Pi.single_add]`. Conclude with `add_mem h1 h2`.

Consider the case `neg p _ h1 => rw [smul_neg, Pi.single_neg]`. Conclude with `neg_mem h1`. Prove the components needed by the constructor for the conclusion. Introduce `hy choose e o ho hyo using fun j => approx (F := F) (k * m) (Nat.mul_pos hk hm) (y j)`. Establish `hyw : y = vinc (F` using `F) e + ∑ j, Pi.single j ((k * m) • o j) := by`.

Rewrite using `[Finset.univ_sum_single (fun j => (k * m) • o j)]`. Use function extensionality and compare the values at `j`. Conclude with `hyo j`. Establish `hwsum : g'.mulVec (∑ j, Pi.single j ((k * m) • o j)) ∈ latHat F E L`. Rewrite using `[Matrix.mulVec_sum]`.

Conclude with `AddSubgroup.sum_mem _ (fun j _ => K1 _ (ho j) j)`. Establish `he : e ∈ abelian₂ σ J L h` using `by show g'.mulVec (vinc e) ∈ latHat F E L`. Establish `: vinc (F` using `F) e = y - ∑ j, Pi.single j ((k * m) • o j) := by conv_rhs => rw [hyw]`. Normalize the expressions using the abelian group laws. Rewrite using `[this, Matrix.mulVec_sub]`.

Conclude with `sub_mem hy hwsum`. Rewrite using `[hyw]`. Use `add_mem (AddSubgroup.subset_closure ⟨1, intAf_one, e, he, rfl⟩) ?_` and prove the remaining obligations. Conclude with `AddSubgroup.sum_mem _ (fun j _ => SL _ (ho j) j)`. Introduce `hy`.

Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨a, ha, x, hx, rfl⟩` from `hy`. Establish `hx' : g'.mulVec (vinc x) ∈ latHat F E L` using `hx`. Establish `: (fun i => a ⊗ₜ[F] x i) = (a ⊗ₜ[F] (1 : E)) • vinc (F` using `F) x := by`.

Use function extensionality and compare the values at `i`. Simplify using `[vinc, inclR, Algebra.TensorProduct.tmul_mul_tmul]`. Rewrite using `[this, Matrix.mulVec_smul]`. Conclude with `latHat_smul L ha hx'`. Consider the case `zero => rw [Matrix.mulVec_zero]`.

Conclude with `zero_mem _`. Consider the case `add y z _ _ h1 h2 => rw [Matrix.mulVec_add]`. Conclude with `add_mem h1 h2`. Consider the case `neg y _ h1 => rw [Matrix.mulVec_neg]`. Conclude with `neg_mem h1`.
-/
theorem rational_points_dense : RatDense := by
  intro F E _ _ _ _ _ σ M J L _h4 h5 h y
  classical
  obtain ⟨k, hk, hkL⟩ := low_nat L h5
  set g' := finMat σ J h⁻¹ with hg'
  have hden : ∃ m : ℕ, 0 < m ∧ ∀ l j, m • g' l j ∈ Oh F E := by
    choose mf hmf hmO using fun p : Fin M × Fin M => den (g' p.1 p.2)
    refine ⟨∏ p, mf p, Finset.prod_pos (fun p _ => hmf p), fun l j => ?_⟩
    obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem mf (Finset.mem_univ (l, j))
    rw [hq, mul_comm, mul_smul]
    exact AddSubgroup.nsmul_mem _ (hmO (l, j)) _
  obtain ⟨m, hm, hmO⟩ := hden
  have K1 : ∀ o ∈ Oh F E, ∀ j, g'.mulVec (Pi.single j ((k * m) • o)) ∈ latHat F E L := by
    intro o ho j
    rw [mulVec_single']
    have : (fun l => g' l j * ((k * m) • o)) = ∑ l, Pi.single l (k • ((m • g' l j) * o)) := by
      rw [Finset.univ_sum_single (fun l => k • ((m • g' l j) * o))]
      funext l
      rw [mul_smul_comm, smul_mul_assoc, smul_smul]
    rw [this]
    exact AddSubgroup.sum_mem _ (fun l _ => single_mem L hkL (Oh_mul (hmO l j) ho) l)
  have SL : ∀ p ∈ Oh F E, ∀ j, Pi.single j ((k * m) • p) ∈ latHat F E (abelian₂ σ J L h) := by
    intro p hp j
    induction hp using AddSubgroup.closure_induction with
    | mem p hp =>
      obtain ⟨a, ha, e, he, rfl⟩ := hp
      rw [nsmul_tmul_F, single_tmul]
      refine AddSubgroup.subset_closure ⟨a, ha, _, ?_, rfl⟩
      show g'.mulVec (vinc (Pi.single j (((k * m : ℕ) : F) • e))) ∈ latHat F E L
      have hv : vinc (F := F) (Pi.single j (((k * m : ℕ) : F) • e)) = Pi.single j ((k * m) • ((1 : Af F) ⊗ₜ[F] e)) := by
        rw [nsmul_tmul_F, single_tmul]
        rfl
      rw [hv]
      exact K1 _ (tmul_mem_Oh intAf_one he) j
    | zero => rw [smul_zero, Pi.single_zero]; exact zero_mem _
    | add p q _ _ h1 h2 => rw [smul_add, Pi.single_add]; exact add_mem h1 h2
    | neg p _ h1 => rw [smul_neg, Pi.single_neg]; exact neg_mem h1
  constructor
  · intro hy
    choose e o ho hyo using fun j => approx (F := F) (k * m) (Nat.mul_pos hk hm) (y j)
    have hyw : y = vinc (F := F) e + ∑ j, Pi.single j ((k * m) • o j) := by
      rw [Finset.univ_sum_single (fun j => (k * m) • o j)]
      funext j
      exact hyo j
    have hwsum : g'.mulVec (∑ j, Pi.single j ((k * m) • o j)) ∈ latHat F E L := by
      rw [Matrix.mulVec_sum]
      exact AddSubgroup.sum_mem _ (fun j _ => K1 _ (ho j) j)
    have he : e ∈ abelian₂ σ J L h := by
      show g'.mulVec (vinc e) ∈ latHat F E L
      have : vinc (F := F) e = y - ∑ j, Pi.single j ((k * m) • o j) := by
        conv_rhs => rw [hyw]
        abel
      rw [this, Matrix.mulVec_sub]
      exact sub_mem hy hwsum
    rw [hyw]
    refine add_mem (AddSubgroup.subset_closure ⟨1, intAf_one, e, he, rfl⟩) ?_
    exact AddSubgroup.sum_mem _ (fun j _ => SL _ (ho j) j)
  · intro hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hy
      have hx' : g'.mulVec (vinc x) ∈ latHat F E L := hx
      have : (fun i => a ⊗ₜ[F] x i) = (a ⊗ₜ[F] (1 : E)) • vinc (F := F) x := by
        funext i
        simp [vinc, inclR, Algebra.TensorProduct.tmul_mul_tmul]
      rw [this, Matrix.mulVec_smul]
      exact latHat_smul L ha hx'
    | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
    | add y z _ _ h1 h2 => rw [Matrix.mulVec_add]; exact add_mem h1 h2
    | neg y _ h1 => rw [Matrix.mulVec_neg]; exact neg_mem h1

end PI.UnitaryGroupMassFormula.UJClassFin
