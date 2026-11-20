import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.ContLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointMemSp4

open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

/- English proof (translation)
Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `s`. Establish `: ∀ᶠ t in nhds s, ∀ i j, f t i j = f s i j` using `Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => (h i j).eventually_eq s`. Conclude with `this.mono fun t ht => Matrix.ext ht`.
-/
private theorem lc_mat {S Q : Type} [TopologicalSpace S] {f : S → M4 Q}
    (h : ∀ i j, IsLocallyConstant fun s => f s i j) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro s
  have : ∀ᶠ t in nhds s, ∀ i j, f t i j = f s i j :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => (h i j).eventually_eq s
  exact this.mono fun t ht => Matrix.ext ht

private def corr {A : Type} [CommRing A] (c n : A) (y : M4 A) : M4 A := y * (1 - c • (adj y * y - n • 1))

/- English proof (translation)
Take `⟨-, -, -, -, -, hm, -⟩` from `grp A`. Rewrite using `[corr, corr, hm, ← Matrix.map_mul, Matrix.map_mul]`. Generalize the expression as in `adj y * y = w`. Use `congr 1`. Use extensionality with `i j`.

Apply the tactic sequence `by_cases e : i = j <;> simp [Matrix.one_apply, e]`.
-/
private theorem corr_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (c n : A) (y : M4 A) :
    (corr c n y).map f = corr (f c) (f n) (y.map f) := by
  obtain ⟨-, -, -, -, -, hm, -⟩ := grp A
  rw [corr, corr, hm, ← Matrix.map_mul, Matrix.map_mul]
  generalize adj y * y = w
  congr 1
  ext i j
  by_cases e : i = j <;> simp [Matrix.one_apply, e]

/- English proof (translation)
Take `⟨hmul, hadj, hadd, hsm, h1, -⟩` from `grp A`. Unfold `IsGSp corr`. Take `⟨E, hE'⟩ : ∃ E, E = adj y * y - n • 1` from `⟨_, rfl⟩`. Establish `a1 : adj E = E`. Rewrite using `[hE', sub_eq_add_neg, ← neg_smul, hadd, hsm, h1, hmul, hadj]`.

Establish `a2 : adj y * y = E + n • 1` using `by rw [hE', sub_add_cancel]`. Rewrite `hE`, the goal using `[← hE']`. Establish `a3 : adj (1 - c • E) = 1 - c • E`. Rewrite using `[sub_eq_add_neg, ← neg_smul, hadd, hsm, h1, a1]`. Rewrite using `[hmul, a3, mul_assoc, ← mul_assoc (adj y), a2]`.

Simplify using `only [mul_sub, sub_mul, add_mul, mul_add, mul_smul_comm, smul_mul_assoc, hE, one_mul, mul_one, smul_zero, smul_add, smul_sub, smul_smul, zero_add, sub_zero]`. Establish `: E = (2 * c * n) • E` using `by rw [hc, one_smul]`. Take the linear combination `(norm := module) this`.
-/
private theorem corr_gsp {A : Type} [CommRing A] (c n : A) (y : M4 A) (hc : 2 * c * n = 1)
    (hE : (adj y * y - n • 1) * (adj y * y - n • 1) = 0) : IsGSp n (corr c n y) := by
  obtain ⟨hmul, hadj, hadd, hsm, h1, -⟩ := grp A
  unfold IsGSp corr
  obtain ⟨E, hE'⟩ : ∃ E, E = adj y * y - n • 1 := ⟨_, rfl⟩
  have a1 : adj E = E := by
    rw [hE', sub_eq_add_neg, ← neg_smul, hadd, hsm, h1, hmul, hadj]
  have a2 : adj y * y = E + n • 1 := by rw [hE', sub_add_cancel]
  rw [← hE'] at hE ⊢
  have a3 : adj (1 - c • E) = 1 - c • E := by
    rw [sub_eq_add_neg, ← neg_smul, hadd, hsm, h1, a1]
  rw [hmul, a3, mul_assoc, ← mul_assoc (adj y), a2]
  simp only [mul_sub, sub_mul, add_mul, mul_add, mul_smul_comm, smul_mul_assoc, hE, one_mul, mul_one, smul_zero,
    smul_add, smul_sub, smul_smul, zero_add, sub_zero]
  have : E = (2 * c * n) • E := by rw [hc, one_smul]
  linear_combination (norm := module) this

/- English proof (translation)
Introduce `i j h`. Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Distinguish the cases in `e : k < i`. Rewrite using `[hX i k e, zero_mul]`.

Rewrite using `[hY k j (lt_of_lt_of_le h (not_lt.1 e)), mul_zero]`.
-/
private theorem up_mul {A : Type} [CommRing A] {X Y : M4 A} (hX : IsUp X) (hY : IsUp Y) : IsUp (X * Y) := by
  intro i j h
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases e : k < i
  · rw [hX i k e, zero_mul]
  · rw [hY k j (lt_of_lt_of_le h (not_lt.1 e)), mul_zero]

/- English proof (translation)
Establish `a : IsUp (adj y)` using `fun i j h => by`. Rewrite using `[adj_apply, hy _ _ (Fin.rev_lt_rev.2 h), smul_zero]`. Use `up_mul hy fun i j h => ?_` and prove the remaining obligations. Simplify using `[up_mul a hy i j h, Matrix.one_apply_ne h.ne']`.
-/
private theorem corr_up {A : Type} [CommRing A] (c n : A) {y : M4 A} (hy : IsUp y) : IsUp (corr c n y) := by
  have a : IsUp (adj y) := fun i j h => by
    rw [adj_apply, hy _ _ (Fin.rev_lt_rev.2 h), smul_zero]
  refine up_mul hy fun i j h => ?_
  simp [up_mul a hy i j h, Matrix.one_apply_ne h.ne']

/- English proof (translation)
Introduce `Λ _ _ _ _ h2 A R _ _ _ _ _ _ p hp hs S _ ν x hν hx hg`. Use `choose z z1 z2 using fun i j => (UpperTheory.V.Ws.X1.contLift p hp hs).1 S (fun s => x s i j) (hx i j)`. Set `y0 : S → M4 A` to `fun s => Matrix.of fun i j => if ∀ t, x t i j = 0 then 0 else z i j s`. Establish `b0 : ∀ i j, AdicCont (maximalIdeal A) fun s => y0 s i j` using `fun i j => by`. Distinguish the cases in `e : ∀ t, x t i j = 0`.

Simplify using `only [y0, Matrix.of_apply, if_pos e]`. Conclude with `fun _ => IsLocallyConstant.const _`. Simplify using `only [y0, Matrix.of_apply, if_neg e]`. Conclude with `z1 i j`. Establish `b1 : ∀ s, (y0 s).map p = x s` using `fun s => by`.

Use extensionality with `i j`. Distinguish the cases in `e : ∀ t, x t i j = 0`. Simplify using `only [y0, Matrix.map_apply, Matrix.of_apply, if_pos e, map_zero, e s]`. Simplify using `only [y0, Matrix.map_apply, Matrix.of_apply, if_neg e, z2]`. Take `⟨u, hu⟩` from `h2.exists_right_inv`.

Establish `hk : ∀ a b : A, p a = 0 → p b = 0 → a * b = 0` using `fun a b ha hb => by`. Establish `ha' : a ∈ maximalIdeal A` using `fun h => by`. Use `h.map p` as an intermediate fact. Rewrite `this` using `[ha]`. Conclude with `not_isUnit_zero this`.

Establish `: a * b ∈ maximalIdeal A * RingHom.ker p` using `Ideal.mul_mem_mul ha' hb`. Rewrite `this` using `[hs, Ideal.mem_bot]`. Then use the resulting hypothesis. Establish `hE : ∀ s i j, p ((adj (y0 s) * y0 s - algebraMap Λ A (ν s) • (1 : M4 A)) i j) = 0` using `fun s i j => by`. Take `⟨-, -, -, -, -, hm, -⟩` from `grp A`. Establish `e1 : (adj (y0 s) * y0 s).map p = algebraMap Λ R (ν s) • (1 : M4 R)`.

Use `hm R (p : A →+* R) (y0 s)` as an intermediate fact. Simplify using `only [RingHom.coe_coe] at this`. Rewrite using `[Matrix.map_mul, ← this, b1]`. Conclude with `hg s`. Establish `e2` using `congrFun (congrFun e1 i) j`.

Rewrite `e2` using `[Matrix.map_apply]`. Rewrite using `[Matrix.sub_apply, map_sub, e2]`. Apply the tactic sequence `by_cases e : i = j <;> simp [Matrix.one_apply, e]`. Use `⟨fun s => corr (algebraMap Λ A (u * ((ν s)⁻¹ : Λˣ))) (algebraMap Λ A (ν s)) (y0 s), fun i j N => ?_, fun s => corr_gsp _ _ _ ?_ ?_, fun s => ?_, fun h s => corr_up _ _ fun i j e => ?_⟩` and prove the remaining obligations. Set `q` to `Ideal.Quotient.mk (maximalIdeal A ^ N)`.

Establish `c1 : IsLocallyConstant fun s => (y0 s).map q` using `lc_mat fun i j => b0 i j N`. Establish `c2 : IsLocallyConstant fun s => q (algebraMap Λ A (ν s))`. Establish `hle : maximalIdeal Λ ^ N ≤ (maximalIdeal A ^ N).comap (algebraMap Λ A)` using `(Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.1 (map_maximalIdeal_le (algebraMap Λ A))) N).trans (Ideal.le_comap_pow _ N)`. Conclude with `(hν N).comp (Ideal.quotientMap _ _ hle)`. Establish `c3 : ∀ s, q (algebraMap Λ A (u * ((ν s)⁻¹ : Λˣ))) = q (algebraMap Λ A u) * Ring.inverse (q (algebraMap Λ A (ν s)))` using `fun s => by`.

Rewrite using `[map_mul, map_mul]`. Use `congr 1`. Conclude with `(Ring.inverse_unit (Units.map (q.comp (algebraMap Λ A)).toMonoidHom (ν s))).symm`. Establish `c4` using `(c1.prodMk c2).comp fun w => corr (q (algebraMap Λ A u) * Ring.inverse w.2) w.2 w.1 i j`. Use `c4 using 2 with s` and compare the differences between its conclusion and the goal.

Simplify using `only [Function.comp_apply]`. Rewrite using `[← c3, ← corr_map]`. Both sides reduce to the same expression. Rewrite using `[← map_ofNat (algebraMap Λ A) 2, ← map_mul, ← map_mul, ← mul_assoc, hu, one_mul, Units.inv_mul, map_one]`. Use extensionality with `i j`.

Rewrite using `[Matrix.mul_apply]`. Conclude with `Finset.sum_eq_zero fun k _ => hk _ _ (hE s i k) (hE s k j)`. Use `corr_map (p : A →+* R) (algebraMap Λ A (u * ((ν s)⁻¹ : Λˣ))) (algebraMap Λ A (ν s)) (y0 s)` as an intermediate fact. Simplify using `only [RingHom.coe_coe] at this`. Establish `g` using `hg s`.

Unfold `IsGSp at g`. Rewrite using `[this, b1, corr, g, p.commutes (ν s), sub_self, smul_zero, sub_zero, mul_one]`. Simplify using `only [y0, Matrix.of_apply, if_pos fun t => h t i j e]`.
-/
theorem UpperTheory.V.Ws.X1.gspLift :
    ∀ {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ], IsUnit (2 : Λ) → ∀ {A R : Type} [CommRing A] [Algebra Λ A] [IsCO Λ A] [CommRing R] [Algebra Λ R] [IsCO Λ R] (p : A →ₐ[Λ] R), Function.Surjective p → maximalIdeal A * RingHom.ker p = ⊥ → ∀ (S : Type) [TopologicalSpace S] (ν : S → Λˣ) (x : S → M4 R), AdicCont (maximalIdeal Λ) (fun s => (ν s : Λ)) → (∀ i j, AdicCont (maximalIdeal R) fun s => x s i j) → (∀ s, IsGSp (algebraMap Λ R (ν s)) (x s)) → ∃ y : S → M4 A, (∀ i j, AdicCont (maximalIdeal A) fun s => y s i j) ∧ (∀ s, IsGSp (algebraMap Λ A (ν s)) (y s)) ∧ (∀ s, (y s).map p = x s) ∧ ((∀ s, IsUp (x s)) → ∀ s, IsUp (y s)) := by
  intro Λ _ _ _ _ h2 A R _ _ _ _ _ _ p hp hs S _ ν x hν hx hg
  classical
  choose z z1 z2 using fun i j => (UpperTheory.V.Ws.X1.contLift p hp hs).1 S (fun s => x s i j) (hx i j)
  let y0 : S → M4 A := fun s => Matrix.of fun i j => if ∀ t, x t i j = 0 then 0 else z i j s
  have b0 : ∀ i j, AdicCont (maximalIdeal A) fun s => y0 s i j := fun i j => by
    by_cases e : ∀ t, x t i j = 0
    · simp only [y0, Matrix.of_apply, if_pos e]
      exact fun _ => IsLocallyConstant.const _
    · simp only [y0, Matrix.of_apply, if_neg e]
      exact z1 i j
  have b1 : ∀ s, (y0 s).map p = x s := fun s => by
    ext i j
    by_cases e : ∀ t, x t i j = 0
    · simp only [y0, Matrix.map_apply, Matrix.of_apply, if_pos e, map_zero, e s]
    · simp only [y0, Matrix.map_apply, Matrix.of_apply, if_neg e, z2]
  obtain ⟨u, hu⟩ := h2.exists_right_inv
  have hk : ∀ a b : A, p a = 0 → p b = 0 → a * b = 0 := fun a b ha hb => by
    have ha' : a ∈ maximalIdeal A := fun h => by
      have := h.map p
      rw [ha] at this
      exact not_isUnit_zero this
    have : a * b ∈ maximalIdeal A * RingHom.ker p := Ideal.mul_mem_mul ha' hb
    rwa [hs, Ideal.mem_bot] at this
  have hE : ∀ s i j, p ((adj (y0 s) * y0 s - algebraMap Λ A (ν s) • (1 : M4 A)) i j) = 0 := fun s i j => by
    obtain ⟨-, -, -, -, -, hm, -⟩ := grp A
    have e1 : (adj (y0 s) * y0 s).map p = algebraMap Λ R (ν s) • (1 : M4 R) := by
      have := hm R (p : A →+* R) (y0 s)
      simp only [RingHom.coe_coe] at this
      rw [Matrix.map_mul, ← this, b1]
      exact hg s
    have e2 := congrFun (congrFun e1 i) j
    rw [Matrix.map_apply] at e2
    rw [Matrix.sub_apply, map_sub, e2]
    by_cases e : i = j <;> simp [Matrix.one_apply, e]
  refine ⟨fun s => corr (algebraMap Λ A (u * ((ν s)⁻¹ : Λˣ))) (algebraMap Λ A (ν s)) (y0 s), fun i j N => ?_,
    fun s => corr_gsp _ _ _ ?_ ?_, fun s => ?_, fun h s => corr_up _ _ fun i j e => ?_⟩
  · let q := Ideal.Quotient.mk (maximalIdeal A ^ N)
    have c1 : IsLocallyConstant fun s => (y0 s).map q := lc_mat fun i j => b0 i j N
    have c2 : IsLocallyConstant fun s => q (algebraMap Λ A (ν s)) := by
      have hle : maximalIdeal Λ ^ N ≤ (maximalIdeal A ^ N).comap (algebraMap Λ A) :=
        (Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.1 (map_maximalIdeal_le (algebraMap Λ A))) N).trans
          (Ideal.le_comap_pow _ N)
      exact (hν N).comp (Ideal.quotientMap _ _ hle)
    have c3 : ∀ s, q (algebraMap Λ A (u * ((ν s)⁻¹ : Λˣ))) =
        q (algebraMap Λ A u) * Ring.inverse (q (algebraMap Λ A (ν s))) := fun s => by
      rw [map_mul, map_mul]
      congr 1
      exact (Ring.inverse_unit (Units.map (q.comp (algebraMap Λ A)).toMonoidHom (ν s))).symm
    have c4 := (c1.prodMk c2).comp fun w => corr (q (algebraMap Λ A u) * Ring.inverse w.2) w.2 w.1 i j
    convert c4 using 2 with s
    simp only [Function.comp_apply]
    rw [← c3, ← corr_map]
    rfl
  · rw [← map_ofNat (algebraMap Λ A) 2, ← map_mul, ← map_mul, ← mul_assoc, hu, one_mul, Units.inv_mul, map_one]
  · ext i j
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero fun k _ => hk _ _ (hE s i k) (hE s k j)
  · have := corr_map (p : A →+* R) (algebraMap Λ A (u * ((ν s)⁻¹ : Λˣ))) (algebraMap Λ A (ν s)) (y0 s)
    simp only [RingHom.coe_coe] at this
    have g := hg s
    unfold IsGSp at g
    rw [this, b1, corr, g, p.commutes (ν s), sub_self, smul_zero, sub_zero, mul_one]
  · simp only [y0, Matrix.of_apply, if_pos fun t => h t i j e]
