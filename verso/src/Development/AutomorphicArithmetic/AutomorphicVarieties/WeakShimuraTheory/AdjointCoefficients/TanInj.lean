import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointMemSp4

open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

section Dual

variable {k : Type} [CommRing k]

private def dm (A B : M4 k) : M4 (DualNumber k) :=
  Matrix.of fun i j => TrivSqZeroExt.inl (A i j) + TrivSqZeroExt.inr (B i j)

/- English proof (translation)
Simplify using `[dm]`.
-/
private theorem dm_fst (A B : M4 k) (i j : Fin 4) : (dm A B i j).fst = A i j := by simp [dm]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[dm, Matrix.mul_apply, TrivSqZeroExt.fst_sum]`. Simplify using `[dm, Matrix.mul_apply, TrivSqZeroExt.snd_sum, Finset.sum_add_distrib, mul_comm]`.
-/
private theorem dm_mul (A B C D : M4 k) : dm A B * dm C D = dm (A * C) (A * D + B * C) := by
  ext i j
  · simp [dm, Matrix.mul_apply, TrivSqZeroExt.fst_sum]
  · simp [dm, Matrix.mul_apply, TrivSqZeroExt.snd_sum, Finset.sum_add_distrib, mul_comm]

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `simp [dm, Matrix.one_apply] split_ifs <;> simp`. Apply the tactic sequence `simp [dm, Matrix.one_apply] split_ifs <;> simp`.
-/
private theorem dm_one : dm (1 : M4 k) 0 = 1 := by
  ext i j
  · simp [dm, Matrix.one_apply]
    split_ifs <;> simp
  · simp [dm, Matrix.one_apply]
    split_ifs <;> simp

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[dm, adj_apply]`. Simplify using `[dm, adj_apply, mul_comm]`.
-/
private theorem dm_adj (A B : M4 k) : adj (dm A B) = dm (adj A) (adj B) := by
  ext i j
  · simp [dm, adj_apply]
  · simp [dm, adj_apply, mul_comm]

/- English proof (translation)
Simplify using `[dm, hA, hB]`.
-/
private theorem dm_zero {A B : M4 k} {i j : Fin 4} (hA : A i j = 0) (hB : B i j = 0) : dm A B i j = 0 := by
  simp [dm, hA, hB]

/- English proof (translation)
Use extensionality with `i j`. Use `congrArg (fun M => (M i j).snd) h` as an intermediate fact. Simplify `this` using `[dm]`.
-/
private theorem dm_inj {A B A' B' : M4 k} (h : dm A B = dm A' B') : B = B' := by
  ext i j
  have := congrArg (fun M => (M i j).snd) h
  simpa [dm] using this

/- English proof (translation)
Establish `hXa : adj X = -X` using `hX`. Establish `hA' : adj A * A = ν • 1` using `hA`. Establish `hadj : adj (X * A) = -(adj A * X)` using `by rw [(grp k).1, hXa, mul_neg]`. Unfold `IsGSp`. Rewrite using `[dm_adj, dm_mul, hadj, hA']`.

Establish `h0 : adj A * (X * A) + -(adj A * X) * A = 0`. Rewrite using `[neg_mul, ← mul_assoc, add_neg_cancel]`. Rewrite using `[h0]`. Apply the tactic sequence `ext i j <;> by_cases hij : i = j <;> simp [dm, Matrix.one_apply, hij, h1, h2]`.
-/
private theorem dm_gsp {ν : k} {ν' : DualNumber k} (h1 : ν'.fst = ν) (h2 : ν'.snd = 0) {A X : M4 k}
    (hA : IsGSp ν A) (hX : X ∈ sp4 k) : IsGSp ν' (dm A (X * A)) := by
  have hXa : adj X = -X := hX
  have hA' : adj A * A = ν • 1 := hA
  have hadj : adj (X * A) = -(adj A * X) := by rw [(grp k).1, hXa, mul_neg]
  unfold IsGSp
  rw [dm_adj, dm_mul, hadj, hA']
  have h0 : adj A * (X * A) + -(adj A * X) * A = 0 := by
    rw [neg_mul, ← mul_assoc, add_neg_cancel]
  rw [h0]
  ext i j <;> by_cases hij : i = j <;> simp [dm, Matrix.one_apply, hij, h1, h2]

/- English proof (translation)
Introduce `i j h` and use `by rw [Matrix.mul_apply] refine Finset.sum_eq_zero fun m _ => ?_ rcases lt_or_ge m i with hm | hm · rw [hA i m hm, zero_mul] · rw [hB m j (lt_of_lt_of_le h hm), mul_zero]`.
-/
private theorem up_mul {A B : M4 k} (hA : IsUp A) (hB : IsUp B) : IsUp (A * B) := fun i j h => by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun m _ => ?_
  rcases lt_or_ge m i with hm | hm
  · rw [hA i m hm, zero_mul]
  · rw [hB m j (lt_of_lt_of_le h hm), mul_zero]

/- English proof (translation)
Establish `h' : adj n * n = 1` using `by simpa [IsGSp] using h`. Conclude with `mul_eq_one_comm.mp h'`.
-/
private theorem mul_adj {n : M4 k} (h : IsGSp 1 n) : n * adj n = 1 := by
  have h' : adj n * n = 1 := by simpa [IsGSp] using h
  exact mul_eq_one_comm.mp h'

/- English proof (translation)
Establish `key : ∀ i j, i ≤ j → (Y * n) i j = 0`. Introduce `i j hij`. Establish `e : Y * n = n * (adj n * Y * n)`. Rewrite using `[← mul_assoc, ← mul_assoc, mul_adj hn.1, one_mul]`. Rewrite using `[e, Matrix.mul_apply]`.

Use `Finset.sum_eq_zero fun l _ => ?_` and prove the remaining obligations. Break down `lt_or_ge i l with hl | hl` into its components or cases. Rewrite using `[hn.2.2 i l hl, zero_mul]`. Rewrite using `[h l j (le_trans hl hij), mul_zero]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Conclude with `dm_gsp (ν := 1) (ν' := 1) (by simp) (by simp) hn.1 (Submodule.neg_mem _ hY)`. Introduce `i`. Use `ext`. Simplify using `[dm, hn.2.1 i]`. Simplify using `[dm, neg_mul, key i i le_rfl]`.

Introduce `i j hij`. Use `ext`. Simplify using `[dm, hn.2.2 i j hij]`. Simplify using `[dm, neg_mul, key i j hij.le]`.
-/
private theorem dm_low {n Y : M4 k} (hn : IsLow n) (hY : Y ∈ sp4 k) (h : ∀ i j, i ≤ j → (adj n * Y * n) i j = 0) :
    IsLow (dm n (-Y * n)) := by
  have key : ∀ i j, i ≤ j → (Y * n) i j = 0 := by
    intro i j hij
    have e : Y * n = n * (adj n * Y * n) := by
      rw [← mul_assoc, ← mul_assoc, mul_adj hn.1, one_mul]
    rw [e, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rcases lt_or_ge i l with hl | hl
    · rw [hn.2.2 i l hl, zero_mul]
    · rw [h l j (le_trans hl hij), mul_zero]
  refine ⟨?_, ?_, ?_⟩
  · exact dm_gsp (ν := 1) (ν' := 1) (by simp) (by simp) hn.1 (Submodule.neg_mem _ hY)
  · intro i
    ext
    · simp [dm, hn.2.1 i]
    · simp [dm, neg_mul, key i i le_rfl]
  · intro i j hij
    ext
    · simp [dm, hn.2.2 i j hij]
    · simp [dm, neg_mul, key i j hij.le]

/- English proof (translation)
Establish `hnn : n * adj n = 1` using `mul_adj hn`. Establish `hY' : adj (-Y) = Y`. Establish `: adj (-Y) = - -Y` using `Submodule.neg_mem _ hY`. Rewrite using `[this, neg_neg]`. Establish `hadjY : adj (-Y * n) = adj n * Y` using `by rw [(grp k).1, hY']`.

Rewrite using `[dm_adj, hadjY, dm_mul, dm_mul]`. Establish `e1 : (adj n * (X - (r * Y * r' - Y)) * n) * (adj n * r * n) = adj n * ((X - (r * Y * r' - Y)) * r) * n`. Combine the equalities or inequalities in the displayed calculation. Establish `e2 : (X - (r * Y * r' - Y)) * r = X * r - r * Y * (r' * r) + Y * r` using `by noncomm_ring`. Rewrite `e1` using `[e2, hr, mul_one]`.

Establish `e : adj n * r * (-Y * n) + (adj n * (X * r) + adj n * Y * r) * n = (adj n * (X - (r * Y * r' - Y)) * n) * (adj n * r * n)`. Rewrite using `[e1]`. Use `noncomm_ring`. Introduce `i j hij`. Apply `dm_zero` to reduce the goal to its premises.

Conclude with `h1 i j hij`. Rewrite using `[e]`. Conclude with `up_mul h2 h1 i j hij`.
-/
private theorem dm_flag {n r r' X Y : M4 k} (hn : IsGSp 1 n) (hY : Y ∈ sp4 k) (hr : r' * r = 1)
    (h1 : IsUp (adj n * r * n)) (h2 : IsUp (adj n * (X - (r * Y * r' - Y)) * n)) :
    IsUp (adj (dm n (-Y * n)) * dm r (X * r) * dm n (-Y * n)) := by
  have hnn : n * adj n = 1 := mul_adj hn
  have hY' : adj (-Y) = Y := by
    have : adj (-Y) = - -Y := Submodule.neg_mem _ hY
    rw [this, neg_neg]
  have hadjY : adj (-Y * n) = adj n * Y := by rw [(grp k).1, hY']
  rw [dm_adj, hadjY, dm_mul, dm_mul]
  have e1 : (adj n * (X - (r * Y * r' - Y)) * n) * (adj n * r * n)
      = adj n * ((X - (r * Y * r' - Y)) * r) * n := by
    calc _ = adj n * (X - (r * Y * r' - Y)) * (n * adj n) * r * n := by simp only [mul_assoc]
      _ = _ := by rw [hnn, mul_one]; simp only [mul_assoc]
  have e2 : (X - (r * Y * r' - Y)) * r = X * r - r * Y * (r' * r) + Y * r := by noncomm_ring
  rw [e2, hr, mul_one] at e1
  have e : adj n * r * (-Y * n) + (adj n * (X * r) + adj n * Y * r) * n
      = (adj n * (X - (r * Y * r' - Y)) * n) * (adj n * r * n) := by
    rw [e1]; noncomm_ring
  intro i j hij
  apply dm_zero
  · exact h1 i j hij
  · rw [e]
    exact up_mul h2 h1 i j hij

private def dRep {Γ : Type} [Group Γ] (r : Γ →* M4 k) (X : Γ → M4 k)
    (h : ∀ s t, X (s * t) = X s + r s * X t * r s⁻¹) : Γ →* M4 (DualNumber k) where
  toFun g := dm (r g) (X g * r g)
  map_one' := by
    have := h 1 1
    simp only [mul_one, inv_one, map_one, one_mul, left_eq_add] at this
    rw [this, map_one, zero_mul, dm_one]
  map_mul' s t := by
    rw [dm_mul, h, map_mul, add_mul, mul_assoc (r s * X t), ← mul_assoc (r s⁻¹), ← map_mul r s⁻¹, inv_mul_cancel, map_one,
      one_mul, add_comm, mul_assoc, mul_assoc]

end Dual

/- English proof (translation)
Take `⟨a, ha⟩` from `IsLocalRing.residue_surjective x.fst`. Establish `hal : algebraMap Λ (DualNumber (ResidueField Λ)) a = TrivSqZeroExt.inl (IsLocalRing.residue Λ a)` using `rfl`. Establish `hx : x = algebraMap Λ (DualNumber (ResidueField Λ)) a + TrivSqZeroExt.inr x.snd`. Rewrite using `[hal]`. Use `ext`.

Simplify using `[ha]`. Simplify using the standard rewrite rules. Establish `hn : res Λ (DualNumber (ResidueField Λ)) (TrivSqZeroExt.inr x.snd) = 0`. Rewrite using `[res_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, TrivSqZeroExt.isUnit_iff_isUnit_fst]`. Simplify using the standard rewrite rules.

Rewrite using `[hx, map_add, hn, add_zero, AlgHom.commutes, hal]`. Simplify using `[ha]`.
-/
private theorem res_dual (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [IsCO Λ (DualNumber (ResidueField Λ))]
    (x : DualNumber (ResidueField Λ)) : res Λ (DualNumber (ResidueField Λ)) x = x.fst := by
  obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective x.fst
  have hal : algebraMap Λ (DualNumber (ResidueField Λ)) a = TrivSqZeroExt.inl (IsLocalRing.residue Λ a) := rfl
  have hx : x = algebraMap Λ (DualNumber (ResidueField Λ)) a + TrivSqZeroExt.inr x.snd := by
    rw [hal]
    ext
    · simp [ha]
    · simp
  have hn : res Λ (DualNumber (ResidueField Λ)) (TrivSqZeroExt.inr x.snd) = 0 := by
    rw [res_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, TrivSqZeroExt.isUnit_iff_isUnit_fst]
    simp
  rw [hx, map_add, hn, add_zero, AlgHom.commutes, hal]
  simp [ha]

/- English proof (translation)
Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `x`. Establish `hev : ∀ᶠ y in nhds x, ∀ i j, f y i j = f x i j`. Simplify using `only [Filter.eventually_all]`. Introduce `i j`.

Conclude with `(IsLocallyConstant.iff_eventually_eq _).mp (h i j) x`. Use `filter_upwards [hev] with y hy`. Use extensionality with `i j`. Conclude with `hy i j`.
-/
private theorem lc_mat {Γ k : Type} [TopologicalSpace Γ] {f : Γ → M4 k} (h : ∀ i j, IsLocallyConstant fun g => f g i j) :
    IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hev : ∀ᶠ y in nhds x, ∀ i j, f y i j = f x i j := by
    simp only [Filter.eventually_all]
    intro i j
    exact (IsLocallyConstant.iff_eventually_eq _).mp (h i j) x
  filter_upwards [hev] with y hy
  ext i j
  exact hy i j

/- English proof (translation)
Introduce `O Γ _ _ _ _ _ _ Φ l _ Λ _ _ _ _ _ a hstd hmu Γb _ _ _ _ π hquo c hc R _ _ _ P hdef rb hb hrb`. Use `haveI : IsCO Λ (DualNumber (ResidueField Λ)) := (co_res Λ).2`. Establish `hrbg : ∀ g, rb (π g) = c.r g` using `fun g => by rw [← hrb]; rfl`. Use `set T := TanC (Φ.loc π) (adSp rb hb) (fun v => bor (c.n v)) (fun v => nil (c.n v)) (π Φ.g0) (tor (ResidueField Λ)) with hT`. Establish `memZ : ∀ x : T, x.1 ∈ UpperTheory.V.Fr.Z1C (Φ.loc π) (adSp rb hb) (fun v => bor (c.n v))` using `fun x => (Submodule.mem_inf.mp x.2).1`.

Establish `memP : ∀ x : T, x.1 ∈ (Submodule.comap (LinearMap.proj (π Φ.g0)) (tor (ResidueField Λ))).prod (Submodule.pi Set.univ (fun v => nil (c.n v)))` using `fun x => (Submodule.mem_inf.mp x.2).2`. Establish `hcoc : ∀ x : T, ∀ s t, (x.1.1 (s * t)).1 = (x.1.1 s).1 + rb s * (x.1.1 t).1 * rb s⁻¹` using `fun x s t => congrArg Subtype.val ((memZ x).2.1 s t)`. Set `P' : T → PD Φ.ι Γ (DualNumber (ResidueField Λ))` to `fun x => ⟨(dRep rb (fun g => (x.1.1 g).1) (hcoc x)).comp π, fun v => dm (c.n v) (-(x.1.2 v).1 * c.n v)⟩`. Establish `hr' : ∀ x g, (P' x).r g = dm (c.r g) ((x.1.1 (π g)).1 * c.r g)`. Introduce `x g`.

Use `show dm (rb (π g)) _ = _`. Rewrite using `[hrbg]`. Establish `hlift : ∀ x : T, Φ.Lifts a c (P' x)`. Introduce `x`. Establish `hZ` using `memZ x`.

Establish `hP` using `Submodule.mem_prod.mp (memP x)`. Use `⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `g`. Rewrite using `[hr']`. Conclude with `dm_gsp rfl rfl (hc.pair.mult g) (x.1.1 (π g)).2`.

Introduce `g hg`. Establish `hπ : π g = 1`. Rewrite using `[← MonoidHom.mem_ker, hquo.ker]`. Conclude with `Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure hg)`. Establish `h0 : (x.1.1 1).1 = 0`.

Establish `h11` using `hcoc x 1 1`. Simplify using `only [mul_one, inv_one, map_one, one_mul, left_eq_add] at h11`. Conclude with `h11`. Rewrite using `[hr', ← hrbg, hπ, h0, zero_mul, map_one, dm_one]`. Rewrite using `[hr']`.

Introduce `i j hij`. Apply `dm_zero` to reduce the goal to its premises. Conclude with `hc.pair.nrm hij`. Establish `hX : Matrix.IsDiag (x.1.1 (π Φ.g0)).1` using `hP.1`. Rewrite using `[Matrix.mul_apply]`.

Use `Finset.sum_eq_zero fun m _ => ?_` and prove the remaining obligations. Distinguish the cases in `hm : i = m`. Substitute `hm` using the available equality. Rewrite using `[hc.pair.nrm hij, mul_zero]`. Rewrite using `[hX hm, zero_mul]`.

Introduce `v`. Conclude with `dm_low (hc.pair.low v) (x.1.2 v).2 (Submodule.mem_pi.mp hP.2 v (Set.mem_univ v))`. Introduce `v s hs`. Rewrite using `[hr']`. Establish `hZ3` using `hZ.2.2 v ⟨s, hs⟩`.

Establish `hr1 : rb (π s)⁻¹ * c.r s = 1` using `by rw [← hrbg, ← map_mul, inv_mul_cancel, map_one]`. Establish `h2 : IsUp (adj (c.n v) * ((x.1.1 (π s)).1 - (c.r s * (x.1.2 v).1 * rb (π s)⁻¹ - (x.1.2 v).1)) * c.n v)`. Rewrite using `[← hrbg s]`. Conclude with `hZ3`. Conclude with `dm_flag (hc.pair.low v).1 (x.1.2 v).2 hr1 (hc.pair.flag v s hs) h2`.

Introduce `v s hs`. Rewrite `hs` using `[hmu v]`. Conclude with `absurd hs (Set.notMem_empty s)`. Introduce `i j N`. Establish `hinj : Function.Injective (Ideal.Quotient.mk ((⊥ : Ideal (ResidueField Λ)) ^ 1))`.

Introduce `u w huw`. Rewrite `huw` using `[Ideal.Quotient.eq, pow_one, Ideal.mem_bot, sub_eq_zero]`. Then use the resulting hypothesis. Establish `hcr : IsLocallyConstant fun g => c.r g` using `lc_mat fun i j => IsLocallyConstant.desc _ _ (hc.cont i j 1) hinj`. Establish `hX : IsLocallyConstant fun g => (x.1.1 (π g)).1` using `(hZ.1.comp Subtype.val).comp_continuous hquo.cont`. Establish `hall` using `IsLocallyConstant.comp₂ hcr hX (fun A B => Ideal.Quotient.mk ((maximalIdeal (DualNumber (ResidueField Λ))) ^ N) (dm A (B * A) i j))`.

Use `show IsLocallyConstant fun g => Ideal.Quotient.mk _ ((P' x).r g i j)`. Simplify using `only [hr']`. Conclude with `hall`. Apply `PD.ext` to reduce the goal to its premises. Use extensionality with `g i j show res Λ _ ((P' x).r g i j) = c.r g i j`.

Rewrite using `[hr', res_dual, dm_fst]`. Use function extensionality and compare the values at `v`. Use extensionality with `i j`. Use `show res Λ _ (dm _ _ i j) = c.n v i j`. Rewrite using `[res_dual, dm_fst]`.

Use `choose f hf using fun x => (hdef.2 _ (P' x) (hlift x)).exists`. Use `⟨f, fun x y hxy => ?_⟩` and prove the remaining obligations. Establish `hP : P' x = P' y` using `by rw [← hf x, ← hf y, hxy]`. Establish `hr` using `congrArg PD.r hP`. Establish `hn` using `congrArg PD.n hP`.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `Prod.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `g'`. Take `⟨g, rfl⟩` from `hquo.onto g'`. Apply `Subtype.ext` to reduce the goal to its premises.

Establish `e1 : (P' x).r g = (P' y).r g` using `DFunLike.congr_fun hr g`. Rewrite `e1` using `[hr', hr']`. Establish `e2` using `dm_inj e1`. Establish `hinv : c.r g * rb (π g)⁻¹ = 1` using `by rw [← hrbg, ← map_mul, mul_inv_cancel, map_one]`. Combine the equalities or inequalities in the displayed calculation.

Use function extensionality and compare the values at `v`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `e2` using `dm_inj (congrFun hn v)`. Establish `hinv : c.n v * adj (c.n v) = 1` using `mul_adj (hc.pair.low v).1`. Establish `e3 : (x.1.2 v).1 * c.n v = (y.1.2 v).1 * c.n v`.

Simplify `e2` using `only [neg_mul, neg_inj]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem UpperTheory.V.Ws.X1.tanInj :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (Φ : Fr O Γ) (l : ℕ) [Fact l.Prime] {Λ : Type} [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] (a : O →+* Λ), Φ.Std l a → (∀ v, Φ.Mu v = ∅) → ∀ {Γb : Type} [Group Γb] [TopologicalSpace Γb] [IsTopologicalGroup Γb] [T2Space Γb] (π : Γ →* Γb), Φ.Quo π → ∀ c : PD Φ.ι Γ (ResidueField Λ), Φ.IsRes ((residue Λ).comp a) c → ∀ (R : Type) [CommRing R] [Algebra Λ R] [IsCO Λ R] (P : PD Φ.ι Γ R), Φ.IsDef a c P → ∀ (rb : Γb →* M4 (ResidueField Λ)) (hb : ∀ g, ∃ x, IsGSp x (rb g)), rb.comp π = c.r → ∃ f : TanC (Φ.loc π) (adSp rb hb) (fun v => bor (c.n v)) (fun v => nil (c.n v)) (π Φ.g0) (tor (ResidueField Λ)) → (R →ₐ[Λ] DualNumber (ResidueField Λ)), Function.Injective f := by
  intro O Γ _ _ _ _ _ _ Φ l _ Λ _ _ _ _ _ a hstd hmu Γb _ _ _ _ π hquo c hc R _ _ _ P hdef rb hb hrb
  haveI : IsCO Λ (DualNumber (ResidueField Λ)) := (co_res Λ).2
  have hrbg : ∀ g, rb (π g) = c.r g := fun g => by rw [← hrb]; rfl
  set T := TanC (Φ.loc π) (adSp rb hb) (fun v => bor (c.n v)) (fun v => nil (c.n v)) (π Φ.g0)
    (tor (ResidueField Λ)) with hT
  have memZ : ∀ x : T, x.1 ∈ UpperTheory.V.Fr.Z1C (Φ.loc π) (adSp rb hb) (fun v => bor (c.n v)) :=
    fun x => (Submodule.mem_inf.mp x.2).1
  have memP : ∀ x : T, x.1 ∈ (Submodule.comap (LinearMap.proj (π Φ.g0)) (tor (ResidueField Λ))).prod
      (Submodule.pi Set.univ (fun v => nil (c.n v))) :=
    fun x => (Submodule.mem_inf.mp x.2).2
  have hcoc : ∀ x : T, ∀ s t, (x.1.1 (s * t)).1 = (x.1.1 s).1 + rb s * (x.1.1 t).1 * rb s⁻¹ :=
    fun x s t => congrArg Subtype.val ((memZ x).2.1 s t)
  let P' : T → PD Φ.ι Γ (DualNumber (ResidueField Λ)) := fun x =>
    ⟨(dRep rb (fun g => (x.1.1 g).1) (hcoc x)).comp π, fun v => dm (c.n v) (-(x.1.2 v).1 * c.n v)⟩
  have hr' : ∀ x g, (P' x).r g = dm (c.r g) ((x.1.1 (π g)).1 * c.r g) := by
    intro x g
    show dm (rb (π g)) _ = _
    rw [hrbg]
  have hlift : ∀ x : T, Φ.Lifts a c (P' x) := by
    intro x
    have hZ := memZ x
    have hP := Submodule.mem_prod.mp (memP x)
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · intro g
      rw [hr']
      exact dm_gsp rfl rfl (hc.pair.mult g) (x.1.1 (π g)).2
    · intro g hg
      have hπ : π g = 1 := by
        rw [← MonoidHom.mem_ker, hquo.ker]
        exact Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure hg)
      have h0 : (x.1.1 1).1 = 0 := by
        have h11 := hcoc x 1 1
        simp only [mul_one, inv_one, map_one, one_mul, left_eq_add] at h11
        exact h11
      rw [hr', ← hrbg, hπ, h0, zero_mul, map_one, dm_one]
    · rw [hr']
      intro i j hij
      apply dm_zero
      · exact hc.pair.nrm hij
      · have hX : Matrix.IsDiag (x.1.1 (π Φ.g0)).1 := hP.1
        rw [Matrix.mul_apply]
        refine Finset.sum_eq_zero fun m _ => ?_
        by_cases hm : i = m
        · subst hm
          rw [hc.pair.nrm hij, mul_zero]
        · rw [hX hm, zero_mul]
    · intro v
      exact dm_low (hc.pair.low v) (x.1.2 v).2 (Submodule.mem_pi.mp hP.2 v (Set.mem_univ v))
    · intro v s hs
      rw [hr']
      have hZ3 := hZ.2.2 v ⟨s, hs⟩
      have hr1 : rb (π s)⁻¹ * c.r s = 1 := by rw [← hrbg, ← map_mul, inv_mul_cancel, map_one]
      have h2 : IsUp (adj (c.n v) * ((x.1.1 (π s)).1 - (c.r s * (x.1.2 v).1 * rb (π s)⁻¹ - (x.1.2 v).1)) * c.n v) := by
        rw [← hrbg s]
        exact hZ3
      exact dm_flag (hc.pair.low v).1 (x.1.2 v).2 hr1 (hc.pair.flag v s hs) h2
    · intro v s hs
      rw [hmu v] at hs
      exact absurd hs (Set.notMem_empty s)
    · intro i j N
      have hinj : Function.Injective (Ideal.Quotient.mk ((⊥ : Ideal (ResidueField Λ)) ^ 1)) := by
        intro u w huw
        rwa [Ideal.Quotient.eq, pow_one, Ideal.mem_bot, sub_eq_zero] at huw
      have hcr : IsLocallyConstant fun g => c.r g :=
        lc_mat fun i j => IsLocallyConstant.desc _ _ (hc.cont i j 1) hinj
      have hX : IsLocallyConstant fun g => (x.1.1 (π g)).1 :=
        (hZ.1.comp Subtype.val).comp_continuous hquo.cont
      have hall := IsLocallyConstant.comp₂ hcr hX
        (fun A B => Ideal.Quotient.mk ((maximalIdeal (DualNumber (ResidueField Λ))) ^ N) (dm A (B * A) i j))
      show IsLocallyConstant fun g => Ideal.Quotient.mk _ ((P' x).r g i j)
      simp only [hr']
      exact hall
    · apply PD.ext
      · ext g i j
        show res Λ _ ((P' x).r g i j) = c.r g i j
        rw [hr', res_dual, dm_fst]
      · funext v
        ext i j
        show res Λ _ (dm _ _ i j) = c.n v i j
        rw [res_dual, dm_fst]
  choose f hf using fun x => (hdef.2 _ (P' x) (hlift x)).exists
  refine ⟨f, fun x y hxy => ?_⟩
  have hP : P' x = P' y := by rw [← hf x, ← hf y, hxy]
  have hr := congrArg PD.r hP
  have hn := congrArg PD.n hP
  apply Subtype.ext
  apply Prod.ext
  · funext g'
    obtain ⟨g, rfl⟩ := hquo.onto g'
    apply Subtype.ext
    have e1 : (P' x).r g = (P' y).r g := DFunLike.congr_fun hr g
    rw [hr', hr'] at e1
    have e2 := dm_inj e1
    have hinv : c.r g * rb (π g)⁻¹ = 1 := by rw [← hrbg, ← map_mul, mul_inv_cancel, map_one]
    calc (x.1.1 (π g)).1 = (x.1.1 (π g)).1 * c.r g * rb (π g)⁻¹ := by rw [mul_assoc, hinv, mul_one]
      _ = (y.1.1 (π g)).1 * c.r g * rb (π g)⁻¹ := by rw [e2]
      _ = (y.1.1 (π g)).1 := by rw [mul_assoc, hinv, mul_one]
  · funext v
    apply Subtype.ext
    have e2 := dm_inj (congrFun hn v)
    have hinv : c.n v * adj (c.n v) = 1 := mul_adj (hc.pair.low v).1
    have e3 : (x.1.2 v).1 * c.n v = (y.1.2 v).1 * c.n v := by
      simpa only [neg_mul, neg_inj] using e2
    calc (x.1.2 v).1 = (x.1.2 v).1 * c.n v * adj (c.n v) := by rw [mul_assoc, hinv, mul_one]
      _ = (y.1.2 v).1 * c.n v * adj (c.n v) := by rw [e3]
      _ = (y.1.2 v).1 := by rw [mul_assoc, hinv, mul_one]
