import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.InV

open Matrix Filter ReciprocityTheory.Gal UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Introduce `i j _ hk`. Use `i.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Consider the case `succ k ih`. Introduce `i j hij hk`. Take `⟨B, B', hB, hB', heq, hdvd⟩` from `H i j hij`. Take `⟨c, hc⟩` from `hdvd`. Establish `key : d ^ k * (B * Z * B') i j = d ^ k * (B i i * Z i j * B' j j)`.

Simplify using `only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_eq_single j, Finset.sum_eq_single i]`. Introduce `a _ ha`. Break down `lt_or_gt_of_ne ha with h | h` into its components or cases. Simplify using `[hB i a h]`.

Establish `h1` using `Fin.lt_iff_val_lt_val.mp h`. Establish `h2` using `Fin.lt_iff_val_lt_val.mp hij`. Establish `hz` using `ih a j (lt_trans hij h) (by omega)`. Combine the equalities or inequalities in the displayed calculation. Simplify using the standard rewrite rules.

Introduce `b _ hb`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `a _`. Break down `lt_or_gt_of_ne hb with h | h` into its components or cases. Break down `lt_or_ge a i with ha | ha` into its components or cases.

Simplify using `[hB i a ha]`. Establish `hba : b < a` using `lt_of_lt_of_le (lt_trans h hij) ha`. Establish `h1` using `Fin.lt_iff_val_lt_val.mp h`. Establish `h2` using `Fin.le_iff_val_le_val.mp ha`. Establish `hz` using `ih a b hba (by omega)`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `[hB' b j h]`. Simplify using the standard rewrite rules. Rewrite `key` using `[heq]`. Take the linear combination `(d ^ k * Z i j) * hc - c * key`.
-/
private theorem kill_low {X : Type} [CommRing X] {n : ℕ} (Z : Matrix (Fin n) (Fin n) X) (d : X)
    (H : ∀ i j, j < i → ∃ B B' : Matrix (Fin n) (Fin n) X, (∀ i j, j < i → B i j = 0) ∧ (∀ i j, j < i → B' i j = 0) ∧
      (B * Z * B') i j = Z i j ∧ B i i * B' j j - 1 ∣ d) (k : ℕ) :
    ∀ i j : Fin n, j < i → n + (j : ℕ) ≤ k + i → d ^ k * Z i j = 0 := by
  induction k with
  | zero =>
    intro i j _ hk
    have := i.isLt
    omega
  | succ k ih =>
    intro i j hij hk
    obtain ⟨B, B', hB, hB', heq, hdvd⟩ := H i j hij
    obtain ⟨c, hc⟩ := hdvd
    have key : d ^ k * (B * Z * B') i j = d ^ k * (B i i * Z i j * B' j j) := by
      simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_eq_single j, Finset.sum_eq_single i]
      · intro a _ ha
        rcases lt_or_gt_of_ne ha with h | h
        · simp [hB i a h]
        · have h1 := Fin.lt_iff_val_lt_val.mp h
          have h2 := Fin.lt_iff_val_lt_val.mp hij
          have hz := ih a j (lt_trans hij h) (by omega)
          calc d ^ k * (B i a * Z a j * B' j j) = B i a * (d ^ k * Z a j) * B' j j := by ring
            _ = 0 := by rw [hz]; ring
      · simp
      · intro b _ hb
        apply Finset.sum_eq_zero
        intro a _
        rcases lt_or_gt_of_ne hb with h | h
        · rcases lt_or_ge a i with ha | ha
          · simp [hB i a ha]
          · have hba : b < a := lt_of_lt_of_le (lt_trans h hij) ha
            have h1 := Fin.lt_iff_val_lt_val.mp h
            have h2 := Fin.le_iff_val_le_val.mp ha
            have hz := ih a b hba (by omega)
            calc d ^ k * (B i a * Z a b * B' b j) = B i a * (d ^ k * Z a b) * B' b j := by ring
              _ = 0 := by rw [hz]; ring
        · simp [hB' b j h]
      · simp
    rw [heq] at key
    linear_combination (d ^ k * Z i j) * hc - c * key

/- English proof (translation)
Use `haveI : Finite (Polynomial.degreeLT K s) := Finite.of_equiv _ (Polynomial.degreeLTEquiv K s).toEquiv.symm`. Use `Finite.of_surjective (fun q : Polynomial.degreeLT K s => Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries K) ^ s}) ((q : Polynomial K) : PowerSeries K)) ?_` and prove the remaining obligations. Introduce `z`. Take `⟨p, rfl⟩` from `Ideal.Quotient.mk_surjective z`. Use `⟨⟨PowerSeries.trunc s p, Polynomial.mem_degreeLT.mpr (PowerSeries.degree_trunc_lt p s)⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[Ideal.Quotient.eq, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]`. Introduce `m hm`. Simplify using `[PowerSeries.coeff_trunc, hm]`.
-/
private theorem fin_quot (K : Type) [Field K] [Finite K] (s : ℕ) :
    Finite (PowerSeries K ⧸ Ideal.span {(PowerSeries.X : PowerSeries K) ^ s}) := by
  classical
  haveI : Finite (Polynomial.degreeLT K s) :=
    Finite.of_equiv _ (Polynomial.degreeLTEquiv K s).toEquiv.symm
  refine Finite.of_surjective (fun q : Polynomial.degreeLT K s =>
    Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries K) ^ s}) ((q : Polynomial K) : PowerSeries K)) ?_
  intro z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  refine ⟨⟨PowerSeries.trunc s p, Polynomial.mem_degreeLT.mpr (PowerSeries.degree_trunc_lt p s)⟩, ?_⟩
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]
  intro m hm
  simp [PowerSeries.coeff_trunc, hm]

/- English proof (translation)
Establish `hu : IsUnit (PowerSeries.divXPowOrder a)`. Rewrite using `[PowerSeries.isUnit_iff_constantCoeff]`. Conclude with `isUnit_iff_ne_zero.mpr (PowerSeries.constantCoeff_divXPowOrder_eq_zero_iff.not.mpr ha)`. Establish `hspan : Ideal.span {a} = Ideal.span {(PowerSeries.X : PowerSeries K) ^ a.order.toNat}`. Rewrite using `[Ideal.span_singleton_eq_span_singleton]`.

Establish `h` using `associated_mul_unit_left ((PowerSeries.X : PowerSeries K) ^ a.order.toNat) _ hu`. Rewrite `h` using `[PowerSeries.X_pow_order_mul_divXPowOrder]`. Then use the resulting hypothesis. Rewrite using `[hspan]`. Conclude with `fin_quot K _`.
-/
private theorem fin_quot' (K : Type) [Field K] [Finite K] (a : PowerSeries K) (ha : a ≠ 0) :
    Finite (PowerSeries K ⧸ Ideal.span {a}) := by
  have hu : IsUnit (PowerSeries.divXPowOrder a) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    exact isUnit_iff_ne_zero.mpr (PowerSeries.constantCoeff_divXPowOrder_eq_zero_iff.not.mpr ha)
  have hspan : Ideal.span {a} = Ideal.span {(PowerSeries.X : PowerSeries K) ^ a.order.toNat} := by
    rw [Ideal.span_singleton_eq_span_singleton]
    have h := associated_mul_unit_left ((PowerSeries.X : PowerSeries K) ^ a.order.toNat) _ hu
    rwa [PowerSeries.X_pow_order_mul_divXPowOrder] at h
  rw [hspan]
  exact fin_quot K _

/- English proof (translation)
Set `f : (A ⧸ I) →ₗ[A] (A ⧸ I)` to `LinearMap.lsmul A (A ⧸ I) a`. Establish `e1 : Nat.card {y : A ⧸ I // algebraMap A (A ⧸ I) a * y = 0} = Nat.card (LinearMap.ker f)` using `Nat.card_congr (Equiv.subtypeEquivRight fun y => by`. Simplify using `[f, LinearMap.mem_ker, Algebra.smul_def])`. Establish `h1` using `Submodule.card_eq_card_quotient_mul_card (LinearMap.ker f)`. Establish `h2` using `Submodule.card_eq_card_quotient_mul_card (LinearMap.range f)`.

Establish `h3 : Nat.card ((A ⧸ I) ⧸ LinearMap.ker f) = Nat.card (LinearMap.range f)` using `Nat.card_congr f.quotKerEquivRange.toEquiv`. Establish `hpos : 0 < Nat.card (LinearMap.range f)` using `Nat.card_pos`. Establish `h5 : Nat.card (LinearMap.ker f) = Nat.card ((A ⧸ I) ⧸ LinearMap.range f)`. Establish `h6` using `h1.symm.trans h2`. Rewrite `h6` using `[h3, mul_comm]`.

Conclude with `Nat.eq_of_mul_eq_mul_left hpos h6`. Set `g : A →ₗ[A] (A ⧸ I) ⧸ LinearMap.range f` to `(LinearMap.range f).mkQ ∘ₗ Algebra.linearMap A (A ⧸ I)`. Establish `hg : Ideal.span {a} ≤ LinearMap.ker g`. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker]`. Simplify using `only [g, LinearMap.comp_apply, Submodule.mkQ_apply, Algebra.linearMap_apply, Submodule.Quotient.mk_eq_zero]`.

Conclude with `⟨1, by simp [f, Algebra.smul_def]⟩`. Establish `hs : Function.Surjective ((Ideal.span {a}).liftQ g hg)`. Introduce `z`. Take `⟨m, rfl⟩` from `Submodule.Quotient.mk_surjective _ z`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective m`.

Conclude with `⟨Submodule.Quotient.mk b, by rw [Submodule.liftQ_apply]; rfl⟩`. Rewrite using `[e1, h5]`. Conclude with `Nat.card_le_card_of_surjective _ hs`.
-/
private theorem ann_card {A : Type} [CommRing A] (I : Ideal A) [Finite (A ⧸ I)] (a : A) [Finite (A ⧸ Ideal.span {a})] :
    Nat.card {y : A ⧸ I // algebraMap A (A ⧸ I) a * y = 0} ≤ Nat.card (A ⧸ Ideal.span {a}) := by
  classical
  let f : (A ⧸ I) →ₗ[A] (A ⧸ I) := LinearMap.lsmul A (A ⧸ I) a
  have e1 : Nat.card {y : A ⧸ I // algebraMap A (A ⧸ I) a * y = 0} = Nat.card (LinearMap.ker f) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun y => by
      simp [f, LinearMap.mem_ker, Algebra.smul_def])
  have h1 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker f)
  have h2 := Submodule.card_eq_card_quotient_mul_card (LinearMap.range f)
  have h3 : Nat.card ((A ⧸ I) ⧸ LinearMap.ker f) = Nat.card (LinearMap.range f) :=
    Nat.card_congr f.quotKerEquivRange.toEquiv
  have hpos : 0 < Nat.card (LinearMap.range f) := Nat.card_pos
  have h5 : Nat.card (LinearMap.ker f) = Nat.card ((A ⧸ I) ⧸ LinearMap.range f) := by
    have h6 := h1.symm.trans h2
    rw [h3, mul_comm] at h6
    exact Nat.eq_of_mul_eq_mul_left hpos h6
  let g : A →ₗ[A] (A ⧸ I) ⧸ LinearMap.range f :=
    (LinearMap.range f).mkQ ∘ₗ Algebra.linearMap A (A ⧸ I)
  have hg : Ideal.span {a} ≤ LinearMap.ker g := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker]
    simp only [g, LinearMap.comp_apply, Submodule.mkQ_apply, Algebra.linearMap_apply,
      Submodule.Quotient.mk_eq_zero]
    exact ⟨1, by simp [f, Algebra.smul_def]⟩
  have hs : Function.Surjective ((Ideal.span {a}).liftQ g hg) := by
    intro z
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective m
    exact ⟨Submodule.Quotient.mk b, by rw [Submodule.liftQ_apply]; rfl⟩
  rw [e1, h5]
  exact Nat.card_le_card_of_surjective _ hs

/- English proof (translation)
Establish `hne : ∀ (v : F.Vl) (i j : Fin n), i ≠ j → ∃ g : F.Gv v, x.ψ v i g ≠ x.ψ v j g`. Introduce `v i j hij`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `(x.N1 v).1 i j hij (MonoidHom.ext hc)`.

Set `fac : F.Vl → Fin n → Fin n → PowerSeries x.K` to `fun v i j => if h : i = j then 1 else ((x.ψ v i (Classical.choose (hne v i j h)) : PowerSeries x.K) * (x.ψ v j (Classical.choose (hne v i j h))⁻¹ : PowerSeries x.K) - 1)`. Establish `hfac : ∀ v i j, fac v i j ≠ 0`. Introduce `v i j`. Simplify using `only [fac]`. Use `split_ifs with hij`.

Conclude with `one_ne_zero`. Rewrite using `[sub_ne_zero]`. Introduce `h1`. Apply `Classical.choose_spec (hne v i j hij)` to reduce the goal to its premises. Establish `h2 : x.ψ v i (Classical.choose (hne v i j hij)) * (x.ψ v j (Classical.choose (hne v i j hij)))⁻¹ = 1`.

Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_mul, Units.val_one, ← map_inv]`. Conclude with `h1`. Conclude with `mul_inv_eq_one.mp h2`. Set `d0 : PowerSeries x.K` to `∏ v, ∏ i, ∏ j, fac v i j`.

Establish `hd0 : d0 ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun v _ => Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j _ => hfac v i j`. Use `⟨d0 ^ n, pow_ne_zero n hd0, ?_⟩` and prove the remaining obligations. Introduce `X _ _ v M hM i j hij`. Establish `hw : x.wX X v * x.wiX X v = 1` using `by show ((x.w v : Matrix (Fin n) (Fin n) (PowerSeries x.K))).map (algebraMap x.A X) * (((x.w v)⁻¹ : GL (Fin n) (PowerSeries x.K)) : Matrix (Fin n) (Fin n) (PowerSeries x.K)).map (algebraMap x.A X) = 1`. Rewrite using `[← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]`.

Simplify using the standard rewrite rules. Establish `hBeq : ∀ g : F.Gv v, x.wiX X v * x.ρX X (F.φ v g) * x.wX X v = ((((x.w v)⁻¹ * x.ρ (F.φ v g) * x.w v : GL (Fin n) (PowerSeries x.K)) : Matrix (Fin n) (Fin n) (PowerSeries x.K))).map (algebraMap x.A X)`. Introduce `g`. Rewrite using `[Units.val_mul, Units.val_mul, Matrix.map_mul, Matrix.map_mul]`. Both sides reduce to the same expression.

Establish `hup : ∀ (g : F.Gv v) (i' j' : Fin n), j' < i' → (x.wiX X v * x.ρX X (F.φ v g) * x.wX X v) i' j' = 0`. Introduce `g i' j' h`. Rewrite using `[hBeq g, Matrix.map_apply, (x.tri v g).1 i' j' h, map_zero]`. Establish `hdg : ∀ (g : F.Gv v) (i' : Fin n), (x.wiX X v * x.ρX X (F.φ v g) * x.wX X v) i' i' = algebraMap x.A X (x.ψ v i' g)`. Introduce `g i'`.

Rewrite using `[hBeq g, Matrix.map_apply, (x.tri v g).2 i']`. Establish `H : ∀ i j : Fin n, j < i → ∃ B B' : Matrix (Fin n) (Fin n) X, (∀ i j, j < i → B i j = 0) ∧ (∀ i j, j < i → B' i j = 0) ∧ (B * (x.wiX X v * M * x.wX X v) * B') i j = (x.wiX X v * M * x.wX X v) i j ∧ B i i * B' j j - 1 ∣ algebraMap x.A X d0`. Introduce `i j hij`. Establish `hij' : i ≠ j` using `ne_of_gt hij`. Use `set g := Classical.choose (hne v i j hij') with hg`.

Use `⟨x.wiX X v * x.ρX X (F.φ v g) * x.wX X v, x.wiX X v * x.ρX X (F.φ v g⁻¹) * x.wX X v, hup g, hup g⁻¹, ?_, ?_⟩` and prove the remaining obligations. Establish `hc : x.wiX X v * x.ρX X (F.φ v g) * x.wX X v * (x.wiX X v * M * x.wX X v) * (x.wiX X v * x.ρX X (F.φ v g⁻¹) * x.wX X v) = x.wiX X v * x.ρX X (F.φ v g) * (x.wX X v * x.wiX X v) * M * (x.wX X v * x.wiX X v) * x.ρX X (F.φ v g⁻¹) * x.wX X v`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[hc, hw]`. Establish `h3` using `hM g i j hij`.

Rewrite `h3` using `[← map_inv (F.φ v) g, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_apply, sub_eq_zero]`. Rewrite using `[← h3]`. Simplify using `only [Matrix.mul_one, Matrix.mul_assoc]`. Rewrite using `[hdg g i, hdg g⁻¹ j, ← map_mul, ← map_one (algebraMap x.A X), ← map_sub]`. Apply `map_dvd` to reduce the goal to its premises.

Establish `hf : fac v i j = (x.ψ v i g : PowerSeries x.K) * (x.ψ v j g⁻¹ : PowerSeries x.K) - 1`. Simplify using `only [fac, dif_neg hij']`. Both sides reduce to the same expression. Rewrite using `[← hf]`. Conclude with `(Finset.dvd_prod_of_mem (fun j => fac v i j) (Finset.mem_univ j)).trans ((Finset.dvd_prod_of_mem (fun i => ∏ j, fac v i j) (Finset.mem_univ i)).trans (Finset.dvd_prod_of_mem (fun v => ∏ i, ∏ j, fac v i j) (Finset.mem_univ v)))`.

Establish `hji` using `Fin.lt_iff_val_lt_val.mp hij`. Establish `key` using `kill_low (x.wiX X v * M * x.wX X v) (algebraMap x.A X d0) H n i j hij (by omega)`. Rewrite using `[map_pow]`. Conclude with `key`.
-/
private theorem low_ann {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) :
    ∃ a : x.A, a ≠ 0 ∧ ∀ (X : Type) [CommRing X] [Algebra x.A X] (v : F.Vl) (M : Matrix (Fin n) (Fin n) X),
      (∀ g i j, j < i → (x.wiX X v * (x.ρX X (F.φ v g) * M * x.ρX X (F.φ v g)⁻¹ - M) * x.wX X v) i j = 0) →
      ∀ i j, j < i → algebraMap x.A X a * (x.wiX X v * M * x.wX X v) i j = 0 := by
  classical
  have hne : ∀ (v : F.Vl) (i j : Fin n), i ≠ j → ∃ g : F.Gv v, x.ψ v i g ≠ x.ψ v j g := by
    intro v i j hij
    by_contra hc
    push_neg at hc
    exact (x.N1 v).1 i j hij (MonoidHom.ext hc)
  let fac : F.Vl → Fin n → Fin n → PowerSeries x.K := fun v i j =>
    if h : i = j then 1 else
      ((x.ψ v i (Classical.choose (hne v i j h)) : PowerSeries x.K) *
        (x.ψ v j (Classical.choose (hne v i j h))⁻¹ : PowerSeries x.K) - 1)
  have hfac : ∀ v i j, fac v i j ≠ 0 := by
    intro v i j
    simp only [fac]
    split_ifs with hij
    · exact one_ne_zero
    · rw [sub_ne_zero]
      intro h1
      apply Classical.choose_spec (hne v i j hij)
      have h2 : x.ψ v i (Classical.choose (hne v i j hij)) *
          (x.ψ v j (Classical.choose (hne v i j hij)))⁻¹ = 1 := by
        apply Units.ext
        rw [Units.val_mul, Units.val_one, ← map_inv]
        exact h1
      exact mul_inv_eq_one.mp h2
  let d0 : PowerSeries x.K := ∏ v, ∏ i, ∏ j, fac v i j
  have hd0 : d0 ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun v _ => Finset.prod_ne_zero_iff.mpr fun i _ =>
      Finset.prod_ne_zero_iff.mpr fun j _ => hfac v i j
  refine ⟨d0 ^ n, pow_ne_zero n hd0, ?_⟩
  intro X _ _ v M hM i j hij
  have hw : x.wX X v * x.wiX X v = 1 := by
    show ((x.w v : Matrix (Fin n) (Fin n) (PowerSeries x.K))).map (algebraMap x.A X) *
      (((x.w v)⁻¹ : GL (Fin n) (PowerSeries x.K)) : Matrix (Fin n) (Fin n) (PowerSeries x.K)).map
        (algebraMap x.A X) = 1
    rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    simp
  have hBeq : ∀ g : F.Gv v, x.wiX X v * x.ρX X (F.φ v g) * x.wX X v =
      ((((x.w v)⁻¹ * x.ρ (F.φ v g) * x.w v : GL (Fin n) (PowerSeries x.K)) :
        Matrix (Fin n) (Fin n) (PowerSeries x.K))).map (algebraMap x.A X) := by
    intro g
    rw [Units.val_mul, Units.val_mul, Matrix.map_mul, Matrix.map_mul]
    rfl
  have hup : ∀ (g : F.Gv v) (i' j' : Fin n), j' < i' →
      (x.wiX X v * x.ρX X (F.φ v g) * x.wX X v) i' j' = 0 := by
    intro g i' j' h
    rw [hBeq g, Matrix.map_apply, (x.tri v g).1 i' j' h, map_zero]
  have hdg : ∀ (g : F.Gv v) (i' : Fin n),
      (x.wiX X v * x.ρX X (F.φ v g) * x.wX X v) i' i' = algebraMap x.A X (x.ψ v i' g) := by
    intro g i'
    rw [hBeq g, Matrix.map_apply, (x.tri v g).2 i']
  have H : ∀ i j : Fin n, j < i → ∃ B B' : Matrix (Fin n) (Fin n) X,
      (∀ i j, j < i → B i j = 0) ∧ (∀ i j, j < i → B' i j = 0) ∧
      (B * (x.wiX X v * M * x.wX X v) * B') i j = (x.wiX X v * M * x.wX X v) i j ∧
      B i i * B' j j - 1 ∣ algebraMap x.A X d0 := by
    intro i j hij
    have hij' : i ≠ j := ne_of_gt hij
    set g := Classical.choose (hne v i j hij') with hg
    refine ⟨x.wiX X v * x.ρX X (F.φ v g) * x.wX X v, x.wiX X v * x.ρX X (F.φ v g⁻¹) * x.wX X v,
      hup g, hup g⁻¹, ?_, ?_⟩
    · have hc : x.wiX X v * x.ρX X (F.φ v g) * x.wX X v * (x.wiX X v * M * x.wX X v) *
          (x.wiX X v * x.ρX X (F.φ v g⁻¹) * x.wX X v) =
          x.wiX X v * x.ρX X (F.φ v g) * (x.wX X v * x.wiX X v) * M * (x.wX X v * x.wiX X v) *
            x.ρX X (F.φ v g⁻¹) * x.wX X v := by
        simp only [Matrix.mul_assoc]
      rw [hc, hw]
      have h3 := hM g i j hij
      rw [← map_inv (F.φ v) g, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_apply, sub_eq_zero] at h3
      rw [← h3]
      simp only [Matrix.mul_one, Matrix.mul_assoc]
    · rw [hdg g i, hdg g⁻¹ j, ← map_mul, ← map_one (algebraMap x.A X), ← map_sub]
      apply map_dvd
      have hf : fac v i j = (x.ψ v i g : PowerSeries x.K) * (x.ψ v j g⁻¹ : PowerSeries x.K) - 1 := by
        simp only [fac, dif_neg hij']
        rfl
      rw [← hf]
      exact (Finset.dvd_prod_of_mem (fun j => fac v i j) (Finset.mem_univ j)).trans
        ((Finset.dvd_prod_of_mem (fun i => ∏ j, fac v i j) (Finset.mem_univ i)).trans
          (Finset.dvd_prod_of_mem (fun v => ∏ i, ∏ j, fac v i j) (Finset.mem_univ v)))
  have hji := Fin.lt_iff_val_lt_val.mp hij
  have key := kill_low (x.wiX X v * M * x.wX X v) (algebraMap x.A X d0) H n i j hij (by omega)
  rw [map_pow]
  exact key

/- English proof (translation)
Introduce `l _ L G0 n x`. Take `⟨a, ha, hann⟩` from `low_ann x`. Use `haveI hfa : Finite (PowerSeries x.K ⧸ Ideal.span {(a : PowerSeries x.K)}) := fin_quot' x.K a ha`. Use `⟨Nat.card (PowerSeries x.K ⧸ Ideal.span {(a : PowerSeries x.K)}) ^ (n * n), ?_⟩` and prove the remaining obligations. Introduce `G h e D hD v`.

Use `haveI hfe : Finite (PowerSeries x.K ⧸ Ideal.span {(PowerSeries.X : PowerSeries x.K) ^ e}) := fin_quot x.K e`. Use `haveI hfe' : Finite (x.Am e) := hfe`. Set `w` to `inV G v`. Set `Zm : D.M.X → Matrix (Fin n) (Fin n) (x.Am e)` to `fun m => x.wiX (x.Am e) v * (hD.e m : Matrix (Fin n) (Fin n) (x.Am e)) * x.wX (x.Am e) v`. Establish `hker : ∀ m, D.π w m = 0 ↔ ∀ i j : Fin n, j < i → Zm m i j = 0` using `fun m => hD.kerV v m`.

Establish `hZsub : ∀ m1 m2, Zm (m1 - m2) = Zm m1 - Zm m2`. Introduce `m1 m2`. Simplify using `only [Zm, map_sub, Submodule.coe_sub, Matrix.mul_sub, Matrix.sub_mul]`. Establish `hannm : ∀ m, D.π w m ∈ ReciprocityTheory.Gal.H0 (D.Q w).ρ → ∀ i j : Fin n, j < i → algebraMap x.A (x.Am e) a * Zm m i j = 0`. Introduce `m hq i j hij`.

Apply `hann (x.Am e) v (hD.e m : Matrix (Fin n) (Fin n) (x.Am e)) _ i j hij` to reduce the goal to its premises. Introduce `g i' j' hij'`. Set `g' : G.G₀` to `G.φ v g`. Establish `hp : h.p₀ g' = G0.frame.φ v g` using `Subtype.ext (by exact h.φ v g)`. Establish `hinv : (G0.frame.φ v g)⁻¹ = h.p₀ g'⁻¹` using `by rw [map_inv, hp]`.

Establish `hzero : D.π w (D.M.ρ (g' : G.Γ) m - m) = 0`. Rewrite using `[map_sub, sub_eq_zero]`. Establish `h2` using `D.equiv w g m`. Conclude with `h2.trans ((ReciprocityTheory.Gal.mem_riemannRochSpace_iff_regularAt_everywhere _ _).mp hq g)`. Establish `h1` using `(hD.kerV v (D.M.ρ (g' : G.Γ) m - m)).mp hzero i' j' hij'`.

Rewrite `h1` using `[map_sub, Submodule.coe_sub, hD.act g' m]`. Rewrite using `[hinv, ← hp]`. Conclude with `h1`. Establish `hch : ∀ q : ReciprocityTheory.Gal.H0 (D.Q w).ρ, D.π w (Classical.choose (D.surj w q)) = q` using `fun q => Classical.choose_spec (D.surj w q)`. Set `S` to `{y : x.Am e // algebraMap x.A (x.Am e) a * y = 0}`.

Set `φ : ReciprocityTheory.Gal.H0 (D.Q w).ρ → (Fin n → Fin n → S)` to `fun q i j => if hij : j < i then ⟨Zm (Classical.choose (D.surj w q)) i j, hannm _ (by rw [hch q]; exact q.2) i j hij⟩ else ⟨0, by simp⟩`. Establish `hinj : Function.Injective φ`. Introduce `q1 q2 hq`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← hch q1, ← hch q2, ← sub_eq_zero, ← map_sub, hker, hZsub]`.

Introduce `i j hij`. Establish `h3` using `congrArg (fun f => ((f i j : S) : x.Am e)) hq`. Simplify using `only [φ, dif_pos hij] at h3`. Rewrite using `[Matrix.sub_apply, h3, sub_self]`. Establish `hK : 1 < Nat.card x.K` using `Finite.one_lt_card`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem UpperTheory.V.Pa.B2.H0_local_card_bounded_of_cls_ker_le_ker :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (n : ℕ) (x : NP G0.frame n), ∃ C : ℕ, ∀ (G : Glob l L) (h : G.Hom G0) (e : ℕ) (D : Dat x.A (plOf G)), IsOd h x (x.Am e) D → ∀ v, Nat.card (H0 (D.Q (inV G v)).ρ) ≤ Nat.card x.K ^ C := by
  intro l _ L G0 n x
  obtain ⟨a, ha, hann⟩ := low_ann x
  haveI hfa : Finite (PowerSeries x.K ⧸ Ideal.span {(a : PowerSeries x.K)}) := fin_quot' x.K a ha
  refine ⟨Nat.card (PowerSeries x.K ⧸ Ideal.span {(a : PowerSeries x.K)}) ^ (n * n), ?_⟩
  intro G h e D hD v
  haveI hfe : Finite (PowerSeries x.K ⧸ Ideal.span {(PowerSeries.X : PowerSeries x.K) ^ e}) :=
    fin_quot x.K e
  haveI hfe' : Finite (x.Am e) := hfe
  let w := inV G v
  let Zm : D.M.X → Matrix (Fin n) (Fin n) (x.Am e) := fun m =>
    x.wiX (x.Am e) v * (hD.e m : Matrix (Fin n) (Fin n) (x.Am e)) * x.wX (x.Am e) v
  have hker : ∀ m, D.π w m = 0 ↔ ∀ i j : Fin n, j < i → Zm m i j = 0 := fun m => hD.kerV v m
  have hZsub : ∀ m1 m2, Zm (m1 - m2) = Zm m1 - Zm m2 := by
    intro m1 m2
    simp only [Zm, map_sub, Submodule.coe_sub, Matrix.mul_sub, Matrix.sub_mul]
  have hannm : ∀ m, D.π w m ∈ ReciprocityTheory.Gal.H0 (D.Q w).ρ →
      ∀ i j : Fin n, j < i → algebraMap x.A (x.Am e) a * Zm m i j = 0 := by
    intro m hq i j hij
    apply hann (x.Am e) v (hD.e m : Matrix (Fin n) (Fin n) (x.Am e)) _ i j hij
    intro g i' j' hij'
    let g' : G.G₀ := G.φ v g
    have hp : h.p₀ g' = G0.frame.φ v g := Subtype.ext (by exact h.φ v g)
    have hinv : (G0.frame.φ v g)⁻¹ = h.p₀ g'⁻¹ := by rw [map_inv, hp]
    have hzero : D.π w (D.M.ρ (g' : G.Γ) m - m) = 0 := by
      rw [map_sub, sub_eq_zero]
      have h2 := D.equiv w g m
      exact h2.trans ((ReciprocityTheory.Gal.mem_riemannRochSpace_iff_regularAt_everywhere _ _).mp hq g)
    have h1 := (hD.kerV v (D.M.ρ (g' : G.Γ) m - m)).mp hzero i' j' hij'
    rw [map_sub, Submodule.coe_sub, hD.act g' m] at h1
    rw [hinv, ← hp]
    exact h1
  have hch : ∀ q : ReciprocityTheory.Gal.H0 (D.Q w).ρ, D.π w (Classical.choose (D.surj w q)) = q :=
    fun q => Classical.choose_spec (D.surj w q)
  let S := {y : x.Am e // algebraMap x.A (x.Am e) a * y = 0}
  let φ : ReciprocityTheory.Gal.H0 (D.Q w).ρ → (Fin n → Fin n → S) := fun q i j =>
    if hij : j < i then
      ⟨Zm (Classical.choose (D.surj w q)) i j,
        hannm _ (by rw [hch q]; exact q.2) i j hij⟩
    else ⟨0, by simp⟩
  have hinj : Function.Injective φ := by
    intro q1 q2 hq
    apply Subtype.ext
    rw [← hch q1, ← hch q2, ← sub_eq_zero, ← map_sub, hker, hZsub]
    intro i j hij
    have h3 := congrArg (fun f => ((f i j : S) : x.Am e)) hq
    simp only [φ, dif_pos hij] at h3
    rw [Matrix.sub_apply, h3, sub_self]
  have hK : 1 < Nat.card x.K := Finite.one_lt_card
  calc Nat.card (ReciprocityTheory.Gal.H0 (D.Q (inV G v)).ρ) ≤ Nat.card (Fin n → Fin n → S) :=
        Nat.card_le_card_of_injective φ hinj
    _ = Nat.card S ^ (n * n) := by simp [Nat.card_fun, ← pow_mul]
    _ ≤ Nat.card (PowerSeries x.K ⧸ Ideal.span {(a : PowerSeries x.K)}) ^ (n * n) :=
        Nat.pow_le_pow_left (ann_card (Ideal.span {(PowerSeries.X : PowerSeries x.K) ^ e}) a) _
    _ ≤ Nat.card x.K ^ (Nat.card (PowerSeries x.K ⧸ Ideal.span {(a : PowerSeries x.K)}) ^ (n * n)) :=
        (Nat.lt_pow_self hK).le
