import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.TwoLe

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.ZK UpperTheory.V.ZK.Ct

/- English proof (translation)
Establish `key : ∀ j ∈ Finset.range D.n, ((D.a : ℤ) ^ j • D.g ^ (D.n - j + 1) - (D.a : ℤ) ^ (j + 1) • D.g ^ (D.n - j)) = (fun k => (D.a : ℤ) ^ k • D.g ^ (D.n - k + 1)) j - (fun k => (D.a : ℤ) ^ k • D.g ^ (D.n - k + 1)) (j + 1)`. Introduce `j hj`. Establish `hj' : j < D.n` using `Finset.mem_range.mp hj`. Establish `e : D.n - (j + 1) + 1 = D.n - j` using `by omega`. Simplify using `only [e]`.

Rewrite using `[Finset.sum_congr rfl key, Finset.sum_range_sub']`. Simplify using `only [pow_zero, one_smul, Nat.sub_zero, Nat.sub_self, zero_add, pow_one]`. Rewrite using `[pow_succ, D.g_pow, one_mul, sub_smul, one_smul]`.
-/
private theorem UpperTheory.V.ZK.Ct.kerF_tele {Y I : Type} [AddCommGroup Y] [AddCommGroup I] (D : Dat Y I) :
    ∑ j ∈ Finset.range D.n, (((D.a : ℤ) ^ j) • D.g ^ (D.n - j + 1) - ((D.a : ℤ) ^ (j + 1)) • D.g ^ (D.n - j))
      = (1 - (D.a : ℤ) ^ D.n) • D.g := by
  have key : ∀ j ∈ Finset.range D.n,
      ((D.a : ℤ) ^ j • D.g ^ (D.n - j + 1) - (D.a : ℤ) ^ (j + 1) • D.g ^ (D.n - j))
        = (fun k => (D.a : ℤ) ^ k • D.g ^ (D.n - k + 1)) j
          - (fun k => (D.a : ℤ) ^ k • D.g ^ (D.n - k + 1)) (j + 1) := by
    intro j hj
    have hj' : j < D.n := Finset.mem_range.mp hj
    have e : D.n - (j + 1) + 1 = D.n - j := by omega
    simp only [e]
  rw [Finset.sum_congr rfl key, Finset.sum_range_sub']
  simp only [pow_zero, one_smul, Nat.sub_zero, Nat.sub_self, zero_add, pow_one]
  rw [pow_succ, D.g_pow, one_mul, sub_smul, one_smul]

/- English proof (translation)
Rewrite using `[← kerF_tele D]`. Simplify using `only [Dat.nm, Dat.del, Finset.sum_mul]`. Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[smul_mul_assoc, mul_sub, mul_smul_comm, mul_one, smul_sub, smul_smul, ← pow_succ, ← pow_succ]`.
-/
private theorem UpperTheory.V.ZK.Ct.kerF_nm_del {Y I : Type} [AddCommGroup Y] [AddCommGroup I] (D : Dat Y I) :
    D.nm * D.del = (1 - (D.a : ℤ) ^ D.n) • D.g := by
  rw [← kerF_tele D]
  simp only [Dat.nm, Dat.del, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [smul_mul_assoc, mul_sub, mul_smul_comm, mul_one, smul_sub, smul_smul, ← pow_succ, ← pow_succ]

/- English proof (translation)
Rewrite using `[← kerF_tele D]`. Simplify using `only [Dat.nm, Dat.del, Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[mul_smul_comm, sub_mul, smul_mul_assoc, one_mul, smul_sub, smul_smul, ← pow_succ, ← pow_succ']`.
-/
private theorem UpperTheory.V.ZK.Ct.kerF_del_nm {Y I : Type} [AddCommGroup Y] [AddCommGroup I] (D : Dat Y I) :
    D.del * D.nm = (1 - (D.a : ℤ) ^ D.n) • D.g := by
  rw [← kerF_tele D]
  simp only [Dat.nm, Dat.del, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [mul_smul_comm, sub_mul, smul_mul_assoc, one_mul, smul_sub, smul_smul, ← pow_succ, ← pow_succ']

/- English proof (translation)
Take `⟨c, hc⟩` from `(Submodule.mem_torsion_iff t).mp ht`. Use `(Submodule.mem_torsion_iff _).mpr ⟨c, ?_⟩` and prove the remaining obligations. Rewrite `hc`, the goal using `[Submonoid.smul_def]`. Rewrite using `[← φ.map_smul, hc, map_zero]`.
-/
private theorem UpperTheory.V.ZK.Ct.kerF_tors {Y : Type} [AddCommGroup Y] (φ : Module.End ℤ Y) {t : Y}
    (ht : t ∈ Submodule.torsion ℤ Y) : φ t ∈ Submodule.torsion ℤ Y := by
  obtain ⟨c, hc⟩ := (Submodule.mem_torsion_iff t).mp ht
  refine (Submodule.mem_torsion_iff _).mpr ⟨c, ?_⟩
  rw [Submonoid.smul_def] at hc ⊢
  rw [← φ.map_smul, hc, map_zero]

/- English proof (translation)
Take `⟨c, hc⟩` from `(Submodule.mem_torsion_iff _).mp ht`. Rewrite `hc` using `[Submonoid.smul_def, smul_smul]`. Establish `hne : (c : ℤ) * q ≠ 0` using `mul_ne_zero (nonZeroDivisors.coe_ne_zero c) hq`. Conclude with `(Submodule.mem_torsion_iff _).mpr ⟨⟨(c : ℤ) * q, mem_nonZeroDivisors_of_ne_zero hne⟩, hc⟩`.
-/
private theorem UpperTheory.V.ZK.Ct.kerF_tors' {Y : Type} [AddCommGroup Y] {q : ℤ} (hq : q ≠ 0) {t : Y}
    (ht : q • t ∈ Submodule.torsion ℤ Y) : t ∈ Submodule.torsion ℤ Y := by
  obtain ⟨c, hc⟩ := (Submodule.mem_torsion_iff _).mp ht
  rw [Submonoid.smul_def, smul_smul] at hc
  have hne : (c : ℤ) * q ≠ 0 := mul_ne_zero (nonZeroDivisors.coe_ne_zero c) hq
  exact (Submodule.mem_torsion_iff _).mpr ⟨⟨(c : ℤ) * q, mem_nonZeroDivisors_of_ne_zero hne⟩, hc⟩

/- English proof (translation)
Introduce `Y I _ _ D q s u h`. Use `set R : Submodule ℤ Y := LinearMap.range D.del ⊔ Submodule.torsion ℤ Y with hRdef`. Establish `hq0 : (q : ℤ) ≠ 0`. Introduce `h0`. Rewrite `h` using `[h0, zero_mul, sub_eq_zero]`.

Establish `h2 : (2 : ℤ) ≤ (D.a : ℤ)` using `by exact_mod_cast D.two_le`. Establish `: (2 : ℤ) ≤ (D.a : ℤ) ^ D.n` using `le_trans h2 (le_self_pow₀ (by linarith) D.n_pos.ne')`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hnd : ∀ z : Y, D.nm (D.del z) = ((q : ℤ) * (-u)) • D.g z`. Introduce `z`.

Establish `e : ((q : ℤ) * (-u)) = 1 - (D.a : ℤ) ^ D.n` using `by linarith`. Rewrite using `[e, ← LinearMap.smul_apply, ← kerF_nm_del D, Module.End.mul_apply]`. Establish `hdn : ∀ z : Y, D.del (D.nm z) = ((q : ℤ) * (-u)) • D.g z`. Introduce `z`. Establish `e : ((q : ℤ) * (-u)) = 1 - (D.a : ℤ) ^ D.n` using `by linarith`.

Rewrite using `[e, ← LinearMap.smul_apply, ← kerF_del_nm D, Module.End.mul_apply]`. Set `φ : D.U →ₗ[ℤ] Y ⧸ mt Y q` to `(mt Y q).mkQ ∘ₗ ((s : ℤ) • D.nm) ∘ₗ D.U.subtype`. Establish `hker : R.submoduleOf D.U ≤ LinearMap.ker φ`. Establish `hle : R ≤ (mt Y q).comap ((s : ℤ) • D.nm)`. Use `sup_le ?_ ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨z, rfl⟩`. Rewrite using `[Submodule.mem_comap, LinearMap.smul_apply, hnd]`. Use `Submodule.mem_sup_left ⟨(s : ℤ) • (-u) • D.g z, ?_⟩` and prove the remaining obligations. Simplify using `only [LinearMap.smul_apply, LinearMap.id_apply, smul_smul]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Introduce `x hx`. Rewrite using `[Submodule.mem_comap, LinearMap.smul_apply]`. Conclude with `Submodule.mem_sup_right (Submodule.smul_mem _ _ (kerF_tors _ hx))`. Introduce `y hy`.

Rewrite using `[LinearMap.mem_ker]`. Use `hle hy` as an intermediate fact. Rewrite `this` using `[Submodule.mem_comap]`. Simplify using `only [φ, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Conclude with `this`.

Use `⟨(R.submoduleOf D.U).liftQ φ hker, ?_, ?_⟩` and prove the remaining obligations. Introduce `y`. Both sides reduce to the same expression. Introduce `w hw`. Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective _ w`.

Establish `hw' : (s : ℤ) • D.nm (y : Y) ∈ mt Y q`. Use `hw` as an intermediate fact. Simplify using `only [Submodule.liftQ_apply, φ, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, LinearMap.smul_apply, Submodule.coe_subtype] at this`. Conclude with `this`. Use `set v : Y := (s : ℤ) • (y : Y) with hv`.

Establish `hnv : D.nm v = (s : ℤ) • D.nm (y : Y)` using `by rw [hv, map_smul]`. Rewrite `hw'` using `[← hnv]`. Take `⟨a, ⟨z, rfl⟩, b, hb, hab⟩` from `Submodule.mem_sup.mp hw'`. Simplify using `only [LinearMap.smul_apply, LinearMap.id_apply] at hab`. Establish `hdel : (q : ℤ) • ((-u) • D.g v - D.del z) = D.del b`.

Establish `e1` using `congrArg D.del hab`. Rewrite `e1` using `[map_add, map_smul, hdn]`. Rewrite using `[smul_sub, smul_smul, ← e1]`. Normalize the expressions using the abelian group laws. Establish `htor : (-u) • D.g v - D.del z ∈ Submodule.torsion ℤ Y` using `kerF_tors' hq0 (by rw [hdel]; exact kerF_tors _ hb)`.

Establish `hR : (u : ℤ) • D.g v ∈ R`. Establish `e : (u : ℤ) • D.g v = -(D.del z + ((-u) • D.g v - D.del z))`. Rewrite using `[neg_smul]`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`.

Conclude with `R.neg_mem (R.add_mem (Submodule.mem_sup_left ⟨z, rfl⟩) (Submodule.mem_sup_right htor))`. Establish `hcomm : Commute (D.g ^ (D.n - 1)) D.del` using `by show Commute _ (D.g - (D.a : ℤ) • 1)`. Conclude with `((Commute.refl D.g).pow_left _).sub_right ((Commute.one_right _).smul_right _)`. Establish `hstab : ∀ x ∈ R, (D.g ^ (D.n - 1)) x ∈ R`. Introduce `x hx`.

Take `⟨c, ⟨z', rfl⟩, e, he, rfl⟩` from `Submodule.mem_sup.mp hx`. Rewrite using `[map_add, ← Module.End.mul_apply, hcomm.eq, Module.End.mul_apply]`. Conclude with `R.add_mem (Submodule.mem_sup_left ⟨_, rfl⟩) (Submodule.mem_sup_right (kerF_tors _ he))`. Establish `hgv : (D.g ^ (D.n - 1)) ((u : ℤ) • D.g v) = (u : ℤ) • v`. Rewrite using `[map_smul, ← Module.End.mul_apply, ← pow_succ, Nat.sub_add_cancel D.n_pos, D.g_pow, Module.End.one_apply]`.

Establish `hfin : ((u * s : ℤ) • (y : Y)) ∈ R`. Rewrite using `[mul_smul, ← hv, ← hgv]`. Conclude with `hstab _ hR`. Rewrite using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Conclude with `hfin`.
-/
theorem UpperTheory.V.ZK.Ct.kerF :
    ∀ (Y I : Type) [AddCommGroup Y] [AddCommGroup I] (D : Dat Y I), ∀ (q s : ℕ) (u : ℤ), (D.a : ℤ) ^ D.n - 1 = q * u → ∃ f : D.W →ₗ[ℤ] Y ⧸ mt Y q, (∀ y : D.U, f (Submodule.Quotient.mk y) = Submodule.Quotient.mk ((s : ℤ) • D.nm y)) ∧ ∀ w, f w = 0 → (u * s) • w = 0 := by
  intro Y I _ _ D q s u h
  set R : Submodule ℤ Y := LinearMap.range D.del ⊔ Submodule.torsion ℤ Y with hRdef
  have hq0 : (q : ℤ) ≠ 0 := by
    intro h0
    rw [h0, zero_mul, sub_eq_zero] at h
    have h2 : (2 : ℤ) ≤ (D.a : ℤ) := by exact_mod_cast D.two_le
    have : (2 : ℤ) ≤ (D.a : ℤ) ^ D.n := le_trans h2 (le_self_pow₀ (by linarith) D.n_pos.ne')
    linarith
  have hnd : ∀ z : Y, D.nm (D.del z) = ((q : ℤ) * (-u)) • D.g z := by
    intro z
    have e : ((q : ℤ) * (-u)) = 1 - (D.a : ℤ) ^ D.n := by linarith
    rw [e, ← LinearMap.smul_apply, ← kerF_nm_del D, Module.End.mul_apply]
  have hdn : ∀ z : Y, D.del (D.nm z) = ((q : ℤ) * (-u)) • D.g z := by
    intro z
    have e : ((q : ℤ) * (-u)) = 1 - (D.a : ℤ) ^ D.n := by linarith
    rw [e, ← LinearMap.smul_apply, ← kerF_del_nm D, Module.End.mul_apply]
  let φ : D.U →ₗ[ℤ] Y ⧸ mt Y q := (mt Y q).mkQ ∘ₗ ((s : ℤ) • D.nm) ∘ₗ D.U.subtype
  have hker : R.submoduleOf D.U ≤ LinearMap.ker φ := by
    have hle : R ≤ (mt Y q).comap ((s : ℤ) • D.nm) := by
      refine sup_le ?_ ?_
      · rintro _ ⟨z, rfl⟩
        rw [Submodule.mem_comap, LinearMap.smul_apply, hnd]
        refine Submodule.mem_sup_left ⟨(s : ℤ) • (-u) • D.g z, ?_⟩
        simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_smul]
        congr 1
        ring
      · intro x hx
        rw [Submodule.mem_comap, LinearMap.smul_apply]
        exact Submodule.mem_sup_right (Submodule.smul_mem _ _ (kerF_tors _ hx))
    intro y hy
    rw [LinearMap.mem_ker]
    have := hle hy
    rw [Submodule.mem_comap] at this
    simp only [φ, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact this
  refine ⟨(R.submoduleOf D.U).liftQ φ hker, ?_, ?_⟩
  · intro y
    rfl
  · intro w hw
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    have hw' : (s : ℤ) • D.nm (y : Y) ∈ mt Y q := by
      have := hw
      simp only [Submodule.liftQ_apply, φ, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, LinearMap.smul_apply, Submodule.coe_subtype] at this
      exact this
    set v : Y := (s : ℤ) • (y : Y) with hv
    have hnv : D.nm v = (s : ℤ) • D.nm (y : Y) := by rw [hv, map_smul]
    rw [← hnv] at hw'
    obtain ⟨a, ⟨z, rfl⟩, b, hb, hab⟩ := Submodule.mem_sup.mp hw'
    simp only [LinearMap.smul_apply, LinearMap.id_apply] at hab
    have hdel : (q : ℤ) • ((-u) • D.g v - D.del z) = D.del b := by
      have e1 := congrArg D.del hab
      rw [map_add, map_smul, hdn] at e1
      rw [smul_sub, smul_smul, ← e1]
      abel
    have htor : (-u) • D.g v - D.del z ∈ Submodule.torsion ℤ Y :=
      kerF_tors' hq0 (by rw [hdel]; exact kerF_tors _ hb)
    have hR : (u : ℤ) • D.g v ∈ R := by
      have e : (u : ℤ) • D.g v = -(D.del z + ((-u) • D.g v - D.del z)) := by
        rw [neg_smul]
        abel
      rw [e]
      exact R.neg_mem (R.add_mem (Submodule.mem_sup_left ⟨z, rfl⟩) (Submodule.mem_sup_right htor))
    have hcomm : Commute (D.g ^ (D.n - 1)) D.del := by
      show Commute _ (D.g - (D.a : ℤ) • 1)
      exact ((Commute.refl D.g).pow_left _).sub_right ((Commute.one_right _).smul_right _)
    have hstab : ∀ x ∈ R, (D.g ^ (D.n - 1)) x ∈ R := by
      intro x hx
      obtain ⟨c, ⟨z', rfl⟩, e, he, rfl⟩ := Submodule.mem_sup.mp hx
      rw [map_add, ← Module.End.mul_apply, hcomm.eq, Module.End.mul_apply]
      exact R.add_mem (Submodule.mem_sup_left ⟨_, rfl⟩) (Submodule.mem_sup_right (kerF_tors _ he))
    have hgv : (D.g ^ (D.n - 1)) ((u : ℤ) • D.g v) = (u : ℤ) • v := by
      rw [map_smul, ← Module.End.mul_apply, ← pow_succ, Nat.sub_add_cancel D.n_pos, D.g_pow,
        Module.End.one_apply]
    have hfin : ((u * s : ℤ) • (y : Y)) ∈ R := by
      rw [mul_smul, ← hv, ← hgv]
      exact hstab _ hR
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact hfin
