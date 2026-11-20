import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.OrdFlagU
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LocCharDR

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
section Phi
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.WeilDeligne GlobalTheory.Pst Polynomial Module Matrix UpperTheory.V.W UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
/- English proof (translation)
Establish `h1 : ∃ j : ℕ, (∑ i ∈ Finset.range n, φ ^ i * m (t 0 ^ j)) x ≠ 0`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Use `letI : Module U D := Module.compHom D m`. Use `hx ((Module.forall_dual_apply_eq_zero_iff U x).mp fun f => ?_)` and prove the remaining obligations.

Establish `h2` using `Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero (f := fun i : Fin n => t i) (v := fun i : Fin n => f ((φ ^ (i : ℕ)) x)) ht (fun j => by`. Establish `h3` using `congrArg f (hc j)`. Rewrite `h3` using `[map_zero, LinearMap.sum_apply, map_sum, Finset.sum_range]`. Rewrite using `[← h3]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[hφ, mul_comm, ← smul_eq_mul, ← map_smul]`. Use the proof step `rfl)`. Simplify using `using congrFun h2 ⟨0, hn⟩`. Take `⟨j, hj⟩` from `h1`. Use `⟨j, hj, ?_⟩` and prove the remaining obligations.

Establish `h4 : (φ ^ n * m (t 0 ^ j)) x = (φ ^ 0 * m (t 0 ^ j)) x`. Rewrite using `[hφ, htn, End.mul_apply, hp, pow_zero, one_mul]`. Establish `h5` using `Finset.sum_range_succ (fun i => (φ ^ i * m (t 0 ^ j)) x) n`. Rewrite `h5` using `[Finset.sum_range_succ', h4, add_left_inj]`. Rewrite using `[LinearMap.sum_apply, map_sum, ← h5]`.

Use `conv_rhs => rw [h5, ← h5]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[pow_succ', mul_assoc, End.mul_apply φ]`.
-/
private theorem exists_trace {k U D : Type} [Field k] [Field U] [AddCommGroup D] [Module k D]
    (m : U →+* End k D) (φ : End k D) (n : ℕ) (hn : 0 < n) (t : ℕ → U)
    (ht : ∀ i j : Fin n, t i = t j → i = j) (htn : t n = t 0)
    (hφ : ∀ i j : ℕ, φ ^ i * m (t 0 ^ j) = m (t i ^ j) * φ ^ i) (x : D) (hx : x ≠ 0) (hp : (φ ^ n) x = x) :
    ∃ j : ℕ, (∑ i ∈ Finset.range n, φ ^ i * m (t 0 ^ j)) x ≠ 0 ∧
      φ ((∑ i ∈ Finset.range n, φ ^ i * m (t 0 ^ j)) x) = (∑ i ∈ Finset.range n, φ ^ i * m (t 0 ^ j)) x := by
  have h1 : ∃ j : ℕ, (∑ i ∈ Finset.range n, φ ^ i * m (t 0 ^ j)) x ≠ 0 := by
    by_contra hc
    push Not at hc
    letI : Module U D := Module.compHom D m
    refine hx ((Module.forall_dual_apply_eq_zero_iff U x).mp fun f => ?_)
    have h2 := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero (f := fun i : Fin n => t i)
      (v := fun i : Fin n => f ((φ ^ (i : ℕ)) x)) ht (fun j => by
        have h3 := congrArg f (hc j)
        rw [map_zero, LinearMap.sum_apply, map_sum, Finset.sum_range] at h3
        rw [← h3]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hφ, mul_comm, ← smul_eq_mul, ← map_smul]
        rfl)
    simpa using congrFun h2 ⟨0, hn⟩
  obtain ⟨j, hj⟩ := h1
  refine ⟨j, hj, ?_⟩
  have h4 : (φ ^ n * m (t 0 ^ j)) x = (φ ^ 0 * m (t 0 ^ j)) x := by
    rw [hφ, htn, End.mul_apply, hp, pow_zero, one_mul]
  have h5 := Finset.sum_range_succ (fun i => (φ ^ i * m (t 0 ^ j)) x) n
  rw [Finset.sum_range_succ', h4, add_left_inj] at h5
  rw [LinearMap.sum_apply, map_sum, ← h5]
  conv_rhs => rw [h5, ← h5]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pow_succ', mul_assoc, End.mul_apply φ]
/- English proof (translation)
Establish `h2` using `hl.out.two_le`. Establish `hlt : ∀ i, i < n → l ^ i < l ^ n - 1`. Introduce `i hi`. Take `⟨r, rfl⟩ : ∃ r, n = r + 1` from `⟨n - 1, by omega⟩`. Establish `h3 : l ^ i ≤ l ^ r` using `Nat.pow_le_pow_right (by omega) (by omega)`.

Establish `h4 : 1 < l ^ r` using `Nat.one_lt_pow (by omega) (by omega)`. Establish `h5 : l ^ r * 2 ≤ l ^ r * l` using `Nat.mul_le_mul_left _ h2`. Rewrite using `[pow_succ]`. Use linear arithmetic over natural numbers and integers. Establish `h0 : 0 < l ^ n - 1` using `lt_of_le_of_lt (Nat.zero_le _) (hlt 0 (by omega))`.

Establish `hd : ¬ l ∣ l ^ n - 1` using `fun h => hl.out.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_sub_iff_right (by omega) (dvd_pow_self l (by omega))).mp h))`. Use `haveI : NeZero (l ^ n - 1) := ⟨h0.ne'⟩`. Take `⟨z, hz⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) (l ^ n - 1)`. Establish `hmem : z ∈ MaximalUnramifiedExtension l` using `IntermediateField.subset_adjoin _ _ ⟨_, h0, hd, hz.pow_eq_one⟩`. Establish `h1 : (⟨z, hmem⟩ : ↥(MaximalUnramifiedExtension l)) ^ (l ^ n - 1) = 1` using `Subtype.ext hz.pow_eq_one`.

Use `⟨⟨z, hmem⟩, ?_, fun i j hij => ?_⟩` and prove the remaining obligations. Rewrite using `[frobUr_pow_root _ _ _ h0 hd h1, show l ^ n = (l ^ n - 1) + 1 by omega, pow_succ, h1, one_mul]`. Rewrite `hij` using `[frobUr_pow_root _ _ _ h0 hd h1, frobUr_pow_root _ _ _ h0 hd h1]`. Establish `h6 : z ^ l ^ (i : ℕ) = z ^ l ^ (j : ℕ)` using `congrArg Subtype.val hij`. Conclude with `Fin.ext (Nat.pow_right_injective h2 (hz.pow_inj (hlt _ i.2) (hlt _ j.2) h6))`.
-/
private theorem exists_orbit (l : ℕ) [hl : Fact l.Prime] (n : ℕ) (hn : 2 ≤ n) :
    ∃ c : ↥(MaximalUnramifiedExtension l), (frobUr l ^ n) c = c ∧
      ∀ i j : Fin n, (frobUr l ^ (i : ℕ)) c = (frobUr l ^ (j : ℕ)) c → i = j := by
  have h2 := hl.out.two_le
  have hlt : ∀ i, i < n → l ^ i < l ^ n - 1 := by
    intro i hi
    obtain ⟨r, rfl⟩ : ∃ r, n = r + 1 := ⟨n - 1, by omega⟩
    have h3 : l ^ i ≤ l ^ r := Nat.pow_le_pow_right (by omega) (by omega)
    have h4 : 1 < l ^ r := Nat.one_lt_pow (by omega) (by omega)
    have h5 : l ^ r * 2 ≤ l ^ r * l := Nat.mul_le_mul_left _ h2
    rw [pow_succ]; omega
  have h0 : 0 < l ^ n - 1 := lt_of_le_of_lt (Nat.zero_le _) (hlt 0 (by omega))
  have hd : ¬ l ∣ l ^ n - 1 := fun h => hl.out.one_lt.ne' (Nat.dvd_one.mp
    ((Nat.dvd_sub_iff_right (by omega) (dvd_pow_self l (by omega))).mp h))
  haveI : NeZero (l ^ n - 1) := ⟨h0.ne'⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) (l ^ n - 1)
  have hmem : z ∈ MaximalUnramifiedExtension l := IntermediateField.subset_adjoin _ _ ⟨_, h0, hd, hz.pow_eq_one⟩
  have h1 : (⟨z, hmem⟩ : ↥(MaximalUnramifiedExtension l)) ^ (l ^ n - 1) = 1 := Subtype.ext hz.pow_eq_one
  refine ⟨⟨z, hmem⟩, ?_, fun i j hij => ?_⟩
  · rw [frobUr_pow_root _ _ _ h0 hd h1, show l ^ n = (l ^ n - 1) + 1 by omega, pow_succ, h1, one_mul]
  · rw [frobUr_pow_root _ _ _ h0 hd h1, frobUr_pow_root _ _ _ h0 hd h1] at hij
    have h6 : z ^ l ^ (i : ℕ) = z ^ l ^ (j : ℕ) := congrArg Subtype.val hij
    exact Fin.ext (Nat.pow_right_injective h2 (hz.pow_inj (hlt _ i.2) (hlt _ j.2) h6))
/- English proof (translation)
The claim follows from `(GlobalTheory.PstLaws.vecStab (Units.coeHom (End k D)) y).zpow_mem hy n`.
-/
private theorem zpow_fix {k D : Type} [Field k] [AddCommGroup D] [Module k D] (u : (End k D)ˣ) (y : D)
    (hy : (u : End k D) y = y) (n : ℤ) : ((u ^ n : (End k D)ˣ) : End k D) y = y :=
  (GlobalTheory.PstLaws.vecStab (Units.coeHom (End k D)) y).zpow_mem hy n
/- English proof (translation)
Rewrite `hy` using `[hc.eq, End.mul_apply, ha, zpow_natCast, Units.val_pow_eq_pow_val]`. Then use the resulting hypothesis.
-/
private theorem pow_fix {k D : Type} [Field k] [AddCommGroup D] [Module k D] (u : (End k D)ˣ) (a : End k D) (y : D)
    (n : ℕ) (hc : Commute a ((u ^ (n : ℤ) : (End k D)ˣ) : End k D)) (ha : a y = y)
    (hy : (a * ((u ^ (n : ℤ) : (End k D)ˣ) : End k D)) y = y) : ((u : End k D) ^ n) y = y := by
  rwa [hc.eq, End.mul_apply, ha, zpow_natCast, Units.val_pow_eq_pow_val] at hy
section
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A w) {O : Type} [CommRing O]
  [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : GlobalTheory.Pst.Induces Bw)
  (P : LocPrime l) {LL : Type} [Field LL] [Algebra ℚ_[l] LL] {V : Type} [AddCommGroup V] [Module LL V]
  [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
/- English proof (translation)
Take `⟨K', hK'⟩` from `(mem_Dpst P ρ).mp y.2`. Conclude with `⟨K', fun g hg => Subtype.ext (hK' g hg)⟩`.
-/
private theorem exists_stab {K : FinExt l} (ρ : Representation LL ↥(GK K) V) (y : ↥(Dpst P ρ)) :
    ∃ K' : FinExt l, ∀ g : ↥(GK K), (g : GQ l) ∈ GK K' → g ∈ GlobalTheory.PstLaws.vecStab (actD P ρ) y := by
  obtain ⟨K', hK'⟩ := (mem_Dpst P ρ).mp y.2
  exact ⟨K', fun g hg => Subtype.ext (hK' g hg)⟩
/- English proof (translation)
Proceed by induction on `s with`. Consider the case `zero => simp`. Consider the case `succ s ih`. Establish `h1` using `deg_mul ((frob h)⁻¹ ^ (s + 1)) (frob h)`. Rewrite `h1` using `[pow_succ, inv_mul_cancel_right, ih, deg_frob]`.

Rewrite using `[pow_succ]`. Use `push_cast`. Use linear arithmetic over natural numbers and integers.
-/
private theorem deg_frob_inv_pow (s : ℕ) : deg ((frob h)⁻¹ ^ s) = -(s : ℤ) := by
  induction s with
  | zero => simp
  | succ s ih =>
    have h1 := deg_mul ((frob h)⁻¹ ^ (s + 1)) (frob h)
    rw [pow_succ, inv_mul_cancel_right, ih, deg_frob] at h1
    rw [pow_succ]; push_cast; omega
variable (ρ : Representation LL ↥(GK Bw.Kw) V)
/- English proof (translation)
Take `⟨K', hK'⟩` from `exists_stab P ρ z`. Use `haveI := K'.2`. Set `S` to `(GlobalTheory.PstLaws.vecStab (actD P ρ) z).comap Bw.e.toMonoidHom`. Establish `hS : IsOpen (S : Set ↥(Dec (F` using `F) A)) := by`. Use `Subgroup.isOpen_mono (H₁ := ((GK K').subgroupOf (GK Bw.Kw)).comap Bw.e.toMonoidHom) (fun τ hτ => hK' _ hτ) ?_` and prove the remaining obligations.

Conclude with `(IntermediateField.fixingSubgroup_isOpen K'.1).preimage (continuous_subtype_val.comp Bw.e_cont)`. Establish `hd` using `UpperTheory.weil_group_dense_in_galois_group F Ω w A h`. Take `⟨τ, rfl⟩` from `Bw.e.surjective g`. Conclude with `hd.induction_on (p := fun τ => τ ∈ S) τ (S.isClosed_of_isOpen hS) hz`.
-/
private theorem fix_of_weil (z : ↥(Dpst P ρ)) (hz : ∀ σ, actD P ρ (weilToGK Bw h σ) z = z)
    (g : ↥(GK Bw.Kw)) : actD P ρ g z = z := by
  obtain ⟨K', hK'⟩ := exists_stab P ρ z
  haveI := K'.2
  let S := (GlobalTheory.PstLaws.vecStab (actD P ρ) z).comap Bw.e.toMonoidHom
  have hS : IsOpen (S : Set ↥(Dec (F := F) A)) := by
    refine Subgroup.isOpen_mono (H₁ := ((GK K').subgroupOf (GK Bw.Kw)).comap Bw.e.toMonoidHom)
      (fun τ hτ => hK' _ hτ) ?_
    exact (IntermediateField.fixingSubgroup_isOpen K'.1).preimage (continuous_subtype_val.comp Bw.e_cont)
  have hd := UpperTheory.weil_group_dense_in_galois_group F Ω w A h
  obtain ⟨τ, rfl⟩ := Bw.e.surjective g
  exact hd.induction_on (p := fun τ => τ ∈ S) τ (S.isClosed_of_isOpen hS) hz
variable [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)]
include hj in
/- English proof (translation)
Establish `hf : resDeg l w ≠ 0`. Introduce `h0`. Establish `hq1` using `GlobalTheory.WeilDeligne.one_lt_normV w`. Rewrite `hq1` using `[normV_eq_pow (hj.mem_placesOver h), h0, pow_zero]`. Conclude with `lt_irrefl _ hq1`.

Take `⟨K', hK'⟩` from `exists_stab P ρ x`. Use `haveI := GlobalTheory.PstLaws.finite_quotient K' _ hK'`. Use `haveI : (GlobalTheory.PstLaws.vecStab (actD P ρ) x).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient`. Take `⟨r, hr0, -, hr⟩` from `Subgroup.exists_pow_mem_of_index_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := GlobalTheory.PstLaws.vecStab (actD P ρ) x)) (weilToGK Bw h (frob h)⁻¹)`. Establish `hr2 : weilToGK Bw h ((frob h)⁻¹ ^ (r * 2)) ∈ GlobalTheory.PstLaws.vecStab (actD P ρ) x`.

Rewrite using `[map_pow (weilToGK Bw h), pow_mul]`. Conclude with `(GlobalTheory.PstLaws.vecStab (actD P ρ) x).pow_mem hr 2`. Establish `h2` using `hx ((frob h)⁻¹ ^ (r * 2))`. Establish `e : -alpha l ((frob h)⁻¹ ^ (r * 2)) = ((resDeg l w * (r * 2) : ℕ) : ℤ)`. Rewrite using `[alpha, deg_frob_inv_pow]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h2` using `[weilD_apply, e]`. Use `⟨_, ?_, pow_fix (phiU P ρ) _ x _ (commute_actD_phiU P ρ _ _) hr2 h2⟩` and prove the remaining obligations. Establish `: 0 < resDeg l w * r` using `Nat.mul_pos (Nat.pos_of_ne_zero hf) hr0`.

Rewrite using `[← mul_assoc]`. Use linear arithmetic over natural numbers and integers.
-/
private theorem exists_period (x : ↥(Dpst P ρ)) (hx : ∀ σ, weilD Bw h P ρ σ x = x) :
    ∃ n : ℕ, 2 ≤ n ∧ (phiD P ρ ^ n) x = x := by
  have hf : resDeg l w ≠ 0 := by
    intro h0
    have hq1 := GlobalTheory.WeilDeligne.one_lt_normV w
    rw [normV_eq_pow (hj.mem_placesOver h), h0, pow_zero] at hq1
    exact lt_irrefl _ hq1
  obtain ⟨K', hK'⟩ := exists_stab P ρ x
  haveI := GlobalTheory.PstLaws.finite_quotient K' _ hK'
  haveI : (GlobalTheory.PstLaws.vecStab (actD P ρ) x).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  obtain ⟨r, hr0, -, hr⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
    (Subgroup.FiniteIndex.index_ne_zero (H := GlobalTheory.PstLaws.vecStab (actD P ρ) x)) (weilToGK Bw h (frob h)⁻¹)
  have hr2 : weilToGK Bw h ((frob h)⁻¹ ^ (r * 2)) ∈ GlobalTheory.PstLaws.vecStab (actD P ρ) x := by
    rw [map_pow (weilToGK Bw h), pow_mul]
    exact (GlobalTheory.PstLaws.vecStab (actD P ρ) x).pow_mem hr 2
  have h2 := hx ((frob h)⁻¹ ^ (r * 2))
  have e : -alpha l ((frob h)⁻¹ ^ (r * 2)) = ((resDeg l w * (r * 2) : ℕ) : ℤ) := by
    rw [alpha, deg_frob_inv_pow]; push_cast; ring
  rw [weilD_apply, e] at h2
  refine ⟨_, ?_, pow_fix (phiU P ρ) _ x _ (commute_actD_phiU P ρ _ _) hr2 h2⟩
  have : 0 < resDeg l w * r := Nat.mul_pos (Nat.pos_of_ne_zero hf) hr0
  rw [← mul_assoc]; omega
include hj in
/- English proof (translation)
Take `⟨n, hn, hp⟩` from `exists_period h Bw hj P ρ x hW`. Take `⟨c, hc1, hc2⟩` from `exists_orbit l n hn`. Take `⟨j, hz0, hz1⟩` from `exists_trace (mulD P ρ) (phiD P ρ) n (by omega) (fun i => (frobUr l ^ i) c) hc2 (by simpa using hc1) (fun i j => by rw [phiD_pow_mulD, pow_zero, AlgHom.one_apply, map_pow]) x hx0 hp`. Use `⟨_, hz0, hz1, fix_of_weil h Bw P ρ _ fun σ => ?_⟩` and prove the remaining obligations. Use `(congrArg (actD P ρ (weilToGK Bw h σ)) (zpow_fix (phiU P ρ) _ hz1 (-alpha l σ))).symm.trans ?_` and prove the remaining obligations.

Establish `hcm : Commute (weilD Bw h P ρ σ) (∑ i ∈ Finset.range n, phiD P ρ ^ i * mulD P ρ ((frobUr l ^ 0) c ^ j))`. Use `Commute.sum_right _ _ _ fun i _ => Commute.mul_right (Commute.pow_right ?_ i) (weilD_mulD Bw h P ρ hj _ _)` and prove the remaining obligations. Rewrite using `[weilD_apply]`. Conclude with `(Commute.mul_right (phiD_actD P ρ _) (Commute.units_zpow_right (u := phiU P ρ) (Commute.refl _) _)).symm`. Conclude with `(LinearMap.congr_fun hcm.eq x).trans (congrArg _ (hW σ))`.
-/
private theorem phiMain (x : ↥(Dpst P ρ)) (hx0 : x ≠ 0) (hW : ∀ σ, weilD Bw h P ρ σ x = x) :
    ∃ z : ↥(Dpst P ρ), z ≠ 0 ∧ phiD P ρ z = z ∧ ∀ g, actD P ρ g z = z := by
  obtain ⟨n, hn, hp⟩ := exists_period h Bw hj P ρ x hW
  obtain ⟨c, hc1, hc2⟩ := exists_orbit l n hn
  obtain ⟨j, hz0, hz1⟩ := exists_trace (mulD P ρ) (phiD P ρ) n (by omega) (fun i => (frobUr l ^ i) c) hc2
    (by simpa using hc1) (fun i j => by rw [phiD_pow_mulD, pow_zero, AlgHom.one_apply, map_pow]) x hx0 hp
  refine ⟨_, hz0, hz1, fix_of_weil h Bw P ρ _ fun σ => ?_⟩
  refine (congrArg (actD P ρ (weilToGK Bw h σ)) (zpow_fix (phiU P ρ) _ hz1 (-alpha l σ))).symm.trans ?_
  have hcm : Commute (weilD Bw h P ρ σ) (∑ i ∈ Finset.range n, phiD P ρ ^ i *
      mulD P ρ ((frobUr l ^ 0) c ^ j)) := by
    refine Commute.sum_right _ _ _ fun i _ => Commute.mul_right (Commute.pow_right ?_ i)
      (weilD_mulD Bw h P ρ hj _ _)
    rw [weilD_apply]
    exact (Commute.mul_right (phiD_actD P ρ _)
      (Commute.units_zpow_right (u := phiU P ρ) (Commute.refl _) _)).symm
  exact (LinearMap.congr_fun hcm.eq x).trans (congrArg _ (hW σ))
end
/- English proof (translation)
Introduce `F Ω _ _ _ _ _ l hl A w h O _ _ _ Bw hj P L V _ _ _ _ _ ρ _ ⟨x, hx0, hW⟩`. Conclude with `phiMain h Bw hj P ρ x hx0 hW`.
-/
private theorem ordPhiU :
    ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (_hj : GlobalTheory.Pst.Induces Bw) (P : LocPrime l) {L : FinExt l} {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V] [FiniteDimensional ↥L.1 V] (ρ : Representation ↥L.1 ↥(GK Bw.Kw) V) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)], (∃ x : ↥(Dpst P ρ), x ≠ 0 ∧ ∀ σ, weilD Bw h P ρ σ x = x) → ∃ z : ↥(Dpst P ρ), z ≠ 0 ∧ GlobalTheory.Pst.phiD P ρ z = z ∧ ∀ g, GlobalTheory.Pst.actD P ρ g z = z := by
  intro F Ω _ _ _ _ _ l hl A w h O _ _ _ Bw hj P L V _ _ _ _ _ ρ _ ⟨x, hx0, hW⟩
  exact phiMain h Bw hj P ρ x hx0 hW
end Phi
section Priv
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
section SlopeTestRemainingChoices
open GlobalTheory.Pst Polynomial Module Matrix Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
  (ι : Qbar l ≃+* ℂ) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A w)
/- English proof (translation)
Establish `: deg (σ * ineIncl h s * σ⁻¹) = 0` using `by simp`. Use `⟨⟨_, deg_eq_zero_iff.1 this⟩, ?_⟩` and prove the remaining obligations. Establish `e : ineIncl h ⟨_, deg_eq_zero_iff.1 this⟩ = σ * ineIncl h s * σ⁻¹` using `rfl`. Rewrite using `[e, inv_mul_cancel_right]`.
-/
private theorem ine_normal (σ : ↥(Weil h)) (s : ↥(Ine (F := F) A)) : ∃ t, σ * ineIncl h s = ineIncl h t * σ := by
  have : deg (σ * ineIncl h s * σ⁻¹) = 0 := by simp
  refine ⟨⟨_, deg_eq_zero_iff.1 this⟩, ?_⟩
  have e : ineIncl h ⟨_, deg_eq_zero_iff.1 this⟩ = σ * ineIncl h s * σ⁻¹ := rfl
  rw [e, inv_mul_cancel_right]
/- English proof (translation)
Use `haveI := hV.finite`. Establish `hc : ∀ σ, (wdRho P ι Bw h hj ρ σ).charpoly = ∏ j, (X - C (μ j σ : ℂ))` using `fun σ => (DpstMap.charPol_wdPst P ι Bw h hj ρ hV σ).symm.trans (hP σ)`. Establish `hL` using `UpperTheory.exists_common_eigenvector_of_charpoly_split_characters (ineIncl h) (frob h) (wdRho P ι Bw h hj ρ) μ (ine_normal h) (fun σ => ⟨deg σ, exists_eq_zpow_mul deg_frob σ⟩) (isSmooth_wdRho P ι Bw h hj ρ).finite_range hc`. Establish `hq : ((qPow w 1 : ℂˣ) : ℂ) = ((normV w : ℕ) : ℂ)` using `by simp`. Establish `hdim : finrank ℂ (WDSpace P ι ρ) = n`.

Rewrite using `[← LinearMap.charpoly_natDegree (wdRho P ι Bw h hj ρ 1), hc, natDegree_prod_of_monic _ _ fun j _ => monic_X_sub_C _]`. Simplify using `only [natDegree_X_sub_C, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]`. Use `⟨UpperTheory.eq_zero_of_twisted_commute_of_distinct_characters (wdRho P ι Bw h hj ρ) μ (unrChar h (qPow w 1)) _ hdim hL (fun j k e => by_contra fun hjk => (hμ j k hjk).1 e) (fun j k e => ?_) fun σ => ?_, fun j hj1 => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hjk : j = k`. Substitute `hjk` using the available equality.

Establish `h1` using `congrArg (fun x : ℂˣ => (x : ℂ)) (left_eq_mul.1 (DFunLike.congr_fun e (frob h)))`. Simplify using `only [unrChar_apply, deg_frob, zpow_one, hq, Units.val_one, Nat.cast_eq_one] at h1`. Conclude with `(one_lt_normV w).ne' h1`. Conclude with `(hμ j k hjk).2 e`. Rewrite using `[unrChar_apply, Units.val_zpow_eq_zpow_val, hq]`.

Conclude with `wdRho_wdN P ι Bw h hj ρ σ`. Establish `h1` using `hL j`. Simplify using `only [hj1, MonoidHom.one_apply, Units.val_one, one_smul] at h1`. Conclude with `ordPhiU h Bw hj P ρ (UpperTheory.exists_weil_invariant_in_Dpst_of_weilDeligne_invariant ι h Bw hj P ρ h1)`.
-/
private theorem core0 {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : GlobalTheory.Pst.Induces Bw) (P : LocPrime l) {L : FinExt l} {V : Type}
    [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V] [FiniteDimensional ↥L.1 V]
    (ρ : Representation ↥L.1 ↥(GK Bw.Kw) V) (hV : IsPst P ρ) {n : ℕ} (μ : Fin n → ↥(Weil h) →* ℂˣ)
    (hμ : ∀ j k, j ≠ k → μ j ≠ μ k ∧ μ j ≠ μ k * unrChar h (qPow w 1))
    (hP : ∀ σ, (wdPst P ι Bw h hj ρ).charPol σ = ∏ j, (X - C (μ j σ : ℂ))) :
    wdN P ι ρ = 0 ∧ ∀ j, μ j = 1 → ∃ z : ↥(Dpst P ρ), z ≠ 0 ∧ phiD P ρ z = z ∧ ∀ g, actD P ρ g z = z := by
  haveI := hV.finite
  have hc : ∀ σ, (wdRho P ι Bw h hj ρ σ).charpoly = ∏ j, (X - C (μ j σ : ℂ)) :=
    fun σ => (DpstMap.charPol_wdPst P ι Bw h hj ρ hV σ).symm.trans (hP σ)
  have hL := UpperTheory.exists_common_eigenvector_of_charpoly_split_characters (ineIncl h) (frob h) (wdRho P ι Bw h hj ρ) μ (ine_normal h)
    (fun σ => ⟨deg σ, exists_eq_zpow_mul deg_frob σ⟩) (isSmooth_wdRho P ι Bw h hj ρ).finite_range hc
  have hq : ((qPow w 1 : ℂˣ) : ℂ) = ((normV w : ℕ) : ℂ) := by simp
  have hdim : finrank ℂ (WDSpace P ι ρ) = n := by
    rw [← LinearMap.charpoly_natDegree (wdRho P ι Bw h hj ρ 1), hc, natDegree_prod_of_monic _ _ fun j _ => monic_X_sub_C _]
    simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  refine ⟨UpperTheory.eq_zero_of_twisted_commute_of_distinct_characters (wdRho P ι Bw h hj ρ) μ (unrChar h (qPow w 1)) _ hdim hL
    (fun j k e => by_contra fun hjk => (hμ j k hjk).1 e) (fun j k e => ?_) fun σ => ?_, fun j hj1 => ?_⟩
  · by_cases hjk : j = k
    · subst hjk
      have h1 := congrArg (fun x : ℂˣ => (x : ℂ)) (left_eq_mul.1 (DFunLike.congr_fun e (frob h)))
      simp only [unrChar_apply, deg_frob, zpow_one, hq, Units.val_one, Nat.cast_eq_one] at h1
      exact (one_lt_normV w).ne' h1
    · exact (hμ j k hjk).2 e
  · rw [unrChar_apply, Units.val_zpow_eq_zpow_val, hq]
    exact wdRho_wdN P ι Bw h hj ρ σ
  have h1 := hL j
  simp only [hj1, MonoidHom.one_apply, Units.val_one, one_smul] at h1
  exact ordPhiU h Bw hj P ρ (UpperTheory.exists_weil_invariant_in_Dpst_of_weilDeligne_invariant ι h Bw hj P ρ h1)
/- English proof (translation)
Take `⟨T⟩` from `UpperTheory.V.Loc.tiedP l`. Take `⟨hd, hJ, hP⟩` from `hD O Bw hj`. Establish `hp` using `hB.isPstAt T Bw r (Units.continuous_val.comp hr) hd`. Take `⟨L, r', hm, hV, e⟩` from `wdAt_of_isPstAt ι Bw h hj hp`. Take `⟨hN0, hz⟩` from `core0 ι h Bw hj (UpperTheory.V.Loc.PP l) (Bw.repE L r') hV μ hμ fun σ => (congrArg (fun x => WD.charPol x σ) e).symm.trans (hP σ)`.

Use `⟨(GlobalTheory.PstLaws.wdParameterAt_monodromy_zero_iff_potCrystalline Bw h hj _ ι r hp).1 ?_, fun j hj1 hHT => ?_⟩` and prove the remaining obligations. Rewrite using `[e]`. Conclude with `(mono0_wdPst ι Bw h hj hV).2 hN0`. Take `⟨z, z0, z1, z2⟩` from `hz j hj1`. Establish `hd'` using `(hm.isdRAt_iff _).1 hd`.

Establish `hM` using `(GlobalTheory.PstLaws.wdN_eq_zero_iff (UpperTheory.V.Loc.PP l) (Bw.repE L r') ι).1 hN0`. Establish `hmult : ∀ (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥L.1) (c : ℤ), c < 0 → Bw.multE (UpperTheory.V.Loc.PP l) L r' τ' c = 0`. Introduce `τ' c hc0`. Set `τ : F →+* Qbar l` to `((algebraMap ↥L.1 (Om l)).comp τ'.toRingHom).comp ((Bw.j.comp (algebraMap F Ω)).codRestrict Bw.Kw.1 Bw.j_E)`. Establish `hτ : IsInduced Bw τ τ'` using `fun _ => rfl`.

Use `IsJumpsAt.count_eq _ hm hτ (hJ τ L τ' hτ) c` as an intermediate fact. Rewrite `this` using `[Multiset.count_eq_zero.2 fun hc' => absurd (hHT τ c hc') (not_le.2 hc0)]`. Conclude with `this.symm`. Take `⟨v, v0, hv⟩` from `UpperTheory.exists_invariant_of_dpst_phi_fixed_of_nonneg_weights (fun τ x => hm.1 (Bw.LL_split τ x)) (Bw.repE L r') (finiteDimensional_DdR _ _ hd') hmult z z0 (LinearMap.congr_fun hM z) z1 z2`. Use `⟨fun i => (v i : Om l), fun h0 => v0 (funext fun i => Subtype.ext (congrFun h0 i)), fun g => ?_⟩` and prove the remaining obligations.

Establish `h5 : (r' g : Matrix (Fin n) (Fin n) ↥L.1) *ᵥ v = v`. Use `hv (Bw.e g)` as an intermediate fact. Rewrite using `[← Bw.e.symm_apply_apply g]`. Conclude with `this`. Use function extensionality and compare the values at `i`.

Establish `h6` using `congrArg (algebraMap ↥L.1 (Om l)) (congrFun h5 i)`. Rewrite `h6` using `[RingHom.map_mulVec]`. Rewrite using `[← hm.2]`. Conclude with `h6`.
-/
private theorem core (hB : DeRhamPotSemistable) {n : ℕ} (r : ↥(Dec (F := F) A) →* GL (Fin n) (Qbar l))
    (hr : Continuous r) (HT : (F →+* Qbar l) → Multiset ℤ) (μ : Fin n → ↥(Weil h) →* ℂˣ)
    (hμ : ∀ j k, j ≠ k → μ j ≠ μ k ∧ μ j ≠ μ k * unrChar h (qPow w 1))
    (hD : DRat ι h r HT fun s => ∏ j, (X - C (μ j s : ℂ)))
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O)
    (hj : GlobalTheory.Pst.Induces Bw) :
    IsPotCrysAt (UpperTheory.V.Loc.PP l) Bw r ∧ ∀ j, μ j = 1 → (∀ τ, ∀ c ∈ HT τ, 0 ≤ c) →
      ∃ v : Fin n → Qbar l, v ≠ 0 ∧ ∀ g, (r g : Matrix (Fin n) (Fin n) (Qbar l)) *ᵥ v = v := by
  obtain ⟨T⟩ := UpperTheory.V.Loc.tiedP l
  obtain ⟨hd, hJ, hP⟩ := hD O Bw hj
  have hp := hB.isPstAt T Bw r (Units.continuous_val.comp hr) hd
  obtain ⟨L, r', hm, hV, e⟩ := wdAt_of_isPstAt ι Bw h hj hp
  obtain ⟨hN0, hz⟩ := core0 ι h Bw hj (UpperTheory.V.Loc.PP l) (Bw.repE L r') hV μ hμ fun σ =>
    (congrArg (fun x => WD.charPol x σ) e).symm.trans (hP σ)
  refine ⟨(GlobalTheory.PstLaws.wdParameterAt_monodromy_zero_iff_potCrystalline Bw h hj _ ι r hp).1 ?_, fun j hj1 hHT => ?_⟩
  · rw [e]
    exact (mono0_wdPst ι Bw h hj hV).2 hN0
  obtain ⟨z, z0, z1, z2⟩ := hz j hj1
  have hd' := (hm.isdRAt_iff _).1 hd
  have hM := (GlobalTheory.PstLaws.wdN_eq_zero_iff (UpperTheory.V.Loc.PP l) (Bw.repE L r') ι).1 hN0
  have hmult : ∀ (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥L.1) (c : ℤ), c < 0 → Bw.multE (UpperTheory.V.Loc.PP l) L r' τ' c = 0 := by
    intro τ' c hc0
    let τ : F →+* Qbar l := ((algebraMap ↥L.1 (Om l)).comp τ'.toRingHom).comp
      ((Bw.j.comp (algebraMap F Ω)).codRestrict Bw.Kw.1 Bw.j_E)
    have hτ : IsInduced Bw τ τ' := fun _ => rfl
    have := IsJumpsAt.count_eq _ hm hτ (hJ τ L τ' hτ) c
    rw [Multiset.count_eq_zero.2 fun hc' => absurd (hHT τ c hc') (not_le.2 hc0)] at this
    exact this.symm
  obtain ⟨v, v0, hv⟩ := UpperTheory.exists_invariant_of_dpst_phi_fixed_of_nonneg_weights (fun τ x => hm.1 (Bw.LL_split τ x)) (Bw.repE L r')
    (finiteDimensional_DdR _ _ hd') hmult z z0 (LinearMap.congr_fun hM z) z1 z2
  refine ⟨fun i => (v i : Om l), fun h0 => v0 (funext fun i => Subtype.ext (congrFun h0 i)), fun g => ?_⟩
  have h5 : (r' g : Matrix (Fin n) (Fin n) ↥L.1) *ᵥ v = v := by
    have := hv (Bw.e g)
    rw [← Bw.e.symm_apply_apply g]
    exact this
  funext i
  have h6 := congrArg (algebraMap ↥L.1 (Om l)) (congrFun h5 i)
  rw [RingHom.map_mulVec] at h6
  rw [← hm.2]
  exact h6
omit [IsAlgClosure F Ω] in
/- English proof (translation)
Use `H.smooth` as an intermediate fact. Unfold `GlobalTheory.SmGL.IsSmoothChar at this ⊢`. Use `this using 1` and compare the differences between its conclusion and the goal. Use extensionality with `x`. Simplify using the standard rewrite rules.

Use `cont := H.cont.inv`. Use `val := fun s g hg hs => by`. Use `H.val s g hg hs` as an intermediate fact. Simplify using `only [MonoidHom.comp_apply, Units.coeHom_apply, MonoidHom.inv_apply, Units.val_inv_eq_inv_val] at this ⊢`. Rewrite using `[this, mul_inv, map_inv₀]`.

Use `congr 1`. Unfold `algPow`. Rewrite using `[← finprod_inv_distrib]`. Simplify using the standard rewrite rules.
-/
private theorem ordChar_inv {a : ↥(Weil h) →* (w.adicCompletion F)ˣ} {ω : (w.adicCompletion F)ˣ →* ℂˣ}
    {hh : (F →+* Qbar l) → ℤ} {ψ : ↥(Dec (F := F) A) →* (Qbar l)ˣ} (H : OrdChar ι a ω hh ψ) :
    OrdChar ι a ω⁻¹ (-hh) ψ⁻¹ where
  smooth := by
    have := H.smooth
    unfold GlobalTheory.SmGL.IsSmoothChar at this ⊢
    convert this using 1
    ext x
    simp
  cont := H.cont.inv
  val := fun s g hg hs => by
    have := H.val s g hg hs
    simp only [MonoidHom.comp_apply, Units.coeHom_apply, MonoidHom.inv_apply, Units.val_inv_eq_inv_val] at this ⊢
    rw [this, mul_inv, map_inv₀]
    congr 1
    unfold algPow
    rw [← finprod_inv_distrib]
    simp
end SlopeTestRemainingChoices
section Main
open GlobalTheory.Pst Polynomial Module Matrix Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
  (ι : Qbar l ≃+* ℂ) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A w)
private noncomputable def twR {H k : Type} [Group H] [Field k] {n : ℕ} (μ : H →* kˣ) (r : H →* GL (Fin n) k) : H →* GL (Fin n) k where
  toFun g := ⟨(μ g : k) • (r g : Matrix (Fin n) (Fin n) k), (μ g⁻¹ : k) • (r g⁻¹ : Matrix (Fin n) (Fin n) k),
    by rw [smul_mul_smul_comm, ← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul]; simp,
    by rw [smul_mul_smul_comm, ← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul]; simp⟩
  map_one' := Units.ext (by simp)
  map_mul' g g' := Units.ext (by simp [smul_smul, mul_comm])
/- English proof (translation)
The claim follows from `Units.continuous_iff.2 ⟨(Units.continuous_val.comp hμ).smul (Units.continuous_val.comp hr), ((Units.continuous_val.comp hμ).smul (Units.continuous_val.comp hr)).comp continuous_inv⟩`.
-/
private theorem twR_cont {H k : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [Field k]
    [TopologicalSpace k] [IsTopologicalRing k] {n : ℕ} {μ : H →* kˣ} {r : H →* GL (Fin n) k}
    (hμ : Continuous μ) (hr : Continuous r) : Continuous (twR μ r) :=
  Units.continuous_iff.2 ⟨(Units.continuous_val.comp hμ).smul (Units.continuous_val.comp hr),
    ((Units.continuous_val.comp hμ).smul (Units.continuous_val.comp hr)).comp continuous_inv⟩
/- English proof (translation)
Introduce `j k hjk`. Use `⟨fun e => (hne j k hjk).1 ((MonoidHom.cancel_right ha.surj).1 e), fun e => (hne j k hjk).2 ((MonoidHom.cancel_right ha.surj).1 ?_)⟩` and prove the remaining obligations. Rewrite using `[e, MonoidHom.mul_comp, ← ha.absPow_comp, Complex.ofReal_one]`.
-/
private theorem good_comp {a : ↥(Weil h) →* (w.adicCompletion F)ˣ} (ha : IsLocalArtin h a) {n : ℕ}
    {ω : Fin n → (w.adicCompletion F)ˣ →* ℂˣ}
    (hne : ∀ i j, i ≠ j → ω i ≠ ω j ∧ ω i ≠ ω j * GlobalTheory.SmGL.absPow (w.adicCompletion F) 1) :
    ∀ j k, j ≠ k → (ω j).comp a ≠ (ω k).comp a ∧ (ω j).comp a ≠ (ω k).comp a * unrChar h (qPow w 1) := by
  intro j k hjk
  refine ⟨fun e => (hne j k hjk).1 ((MonoidHom.cancel_right ha.surj).1 e), fun e => (hne j k hjk).2
    ((MonoidHom.cancel_right ha.surj).1 ?_)⟩
  rw [e, MonoidHom.mul_comp, ← ha.absPow_comp, Complex.ofReal_one]
/- English proof (translation)
Establish `hB` using `hL.aut.berger`. Proceed by induction on `n with`. Consider the case `zero => exact fun r _ _ _ _ _ _ _ _ => ⟨1, fun _ => ⟨fun i => i.elim0, fun i => i.elim0⟩⟩`. Consider the case `succ n ih`. Introduce `r hr hh hmono ω ψ hO hne hD`.

Establish `hO'` using `ordChar_inv ι h (hO 0)`. Establish `hc` using `twR_cont hO'.cont hr`. Establish `h1` using `UpperTheory.deRham_rational_twist_by_character hB ι h r (twR (ψ 0)⁻¹ r) (ψ 0)⁻¹ hr hc hO'.cont (fun _ => rfl) _ _ _ _ hD (_root_.UpperTheory.V.Loc.hecke_char_de_rham_of_local_artin_above_l hL h hw ι a ha _ _ _ hO').1`. Take `⟨LL, Bw, hj⟩` from `GlobalTheory.Pst.Test.exists_induces (l := l) (E := F) (Ω := Ω) hw h`. Take `⟨v, v0, hv⟩` from `(core ι h hB _ hc _ (fun j => (ω j * (ω 0)⁻¹).comp a) (good_comp h ha fun j k hjk => ⟨fun e => (hne j k hjk).1 (mul_right_cancel e), fun e => (hne j k hjk).2 (mul_right_cancel (e.trans (mul_right_comm _ _ _)))⟩) (by simpa only [MonoidHom.comp_apply, MonoidHom.mul_apply, Units.val …`.

Simplify using `only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and, Pi.neg_apply] at hc`. Take `⟨_, ⟨j, rfl⟩, rfl⟩` from `hc`. Use `(hmono τ).monotone (Fin.zero_le j)` as an intermediate fact. Use the proof step `omega)`. Establish `hv' : ∀ g, (r g : Matrix (Fin (n + 1)) (Fin (n + 1)) (Qbar l)) *ᵥ v = (ψ 0 g : Qbar l) • v` using `fun g => by`.

Use `hv g` as an intermediate fact. Express the relevant statement in the definitionally equal form `((((ψ 0 g)⁻¹ : (Qbar l)ˣ) : Qbar l) • (r g : Matrix (Fin (n + 1)) (Fin (n + 1)) (Qbar l))) *ᵥ v = v at this`. Rewrite `this` using `[Matrix.smul_mulVec]`. Rewrite using `[← congrArg (fun x => (ψ 0 g : Qbar l) • x) this, smul_smul, Units.mul_inv, one_smul]`. Take `⟨p, r₁, r', e₁, c₁, c', b1, b2, b3, hfl⟩` from `UpperTheory.exists_common_eigenline r ψ v hr v0 hv'`.

Establish `h2` using `UpperTheory.deRhamRational_of_conj hB ι h r r₁ p hr e₁ _ _ hD`. Use `hfl (ih r' c' (fun j => hh j.succ) (fun τ => (hmono τ).comp Fin.strictMono_succ) (fun j => ω j.succ) _ (fun j => hO j.succ) (fun i j hij => hne _ _ fun e => hij (Fin.succ_injective _ e)) ?_)` and prove the remaining obligations. Use `UpperTheory.deRham_rational_of_extension_by_character hB ι h r₁ r' (ψ 0) c₁ b1 b2 b3 (hh 0) _ _ _ ?_ (_root_.UpperTheory.V.Loc.hecke_char_de_rham_of_local_artin_above_l hL h hw ι a ha _ _ _ (hO 0)).1` and prove the remaining obligations. Use `h2 using 2` and compare the differences between its conclusion and the goal. Rewrite using `[Fin.univ_val_map, Fin.univ_val_map, List.ofFn_succ, Multiset.cons_coe]`.

Rewrite using `[Fin.prod_univ_succ]`.
-/
private theorem flag (hL : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (hw : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal)
    {a : ↥(Weil h) →* (w.adicCompletion F)ˣ} (ha : IsLocalArtin h a) (n : ℕ) :
    ∀ (r : ↥(Dec (F := F) A) →* GL (Fin n) (Qbar l)), Continuous r →
    ∀ (hh : Fin n → (F →+* Qbar l) → ℤ), (∀ τ, StrictMono fun j => hh j τ) →
    ∀ (ω : Fin n → (w.adicCompletion F)ˣ →* ℂˣ) (ψ : Fin n → ↥(Dec (F := F) A) →* (Qbar l)ˣ),
      (∀ j, OrdChar ι a (ω j) (hh j) (ψ j)) →
      (∀ i j, i ≠ j → ω i ≠ ω j ∧ ω i ≠ ω j * GlobalTheory.SmGL.absPow (w.adicCompletion F) 1) →
      DRat ι h r (fun τ => Finset.univ.val.map fun j => hh j τ) (fun s => ∏ j, (X - C (ω j (a s) : ℂ))) →
      HasFlag r ψ := by
  have hB := hL.aut.berger
  induction n with
  | zero => exact fun r _ _ _ _ _ _ _ _ => ⟨1, fun _ => ⟨fun i => i.elim0, fun i => i.elim0⟩⟩
  | succ n ih =>
    intro r hr hh hmono ω ψ hO hne hD
    have hO' := ordChar_inv ι h (hO 0)
    have hc := twR_cont hO'.cont hr
    have h1 := UpperTheory.deRham_rational_twist_by_character hB ι h r (twR (ψ 0)⁻¹ r) (ψ 0)⁻¹ hr hc hO'.cont (fun _ => rfl) _ _ _ _ hD
      (_root_.UpperTheory.V.Loc.hecke_char_de_rham_of_local_artin_above_l hL h hw ι a ha _ _ _ hO').1
    obtain ⟨LL, Bw, hj⟩ := GlobalTheory.Pst.Test.exists_induces (l := l) (E := F) (Ω := Ω) hw h
    obtain ⟨v, v0, hv⟩ := (core ι h hB _ hc _ (fun j => (ω j * (ω 0)⁻¹).comp a)
      (good_comp h ha fun j k hjk => ⟨fun e => (hne j k hjk).1 (mul_right_cancel e),
        fun e => (hne j k hjk).2 (mul_right_cancel (e.trans (mul_right_comm _ _ _)))⟩)
      (by simpa only [MonoidHom.comp_apply, MonoidHom.mul_apply, Units.val_mul] using h1) Bw hj).2 0
      (by rw [mul_inv_cancel]; rfl) (fun τ c hc => by
        simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and, Pi.neg_apply] at hc
        obtain ⟨_, ⟨j, rfl⟩, rfl⟩ := hc
        have := (hmono τ).monotone (Fin.zero_le j)
        omega)
    have hv' : ∀ g, (r g : Matrix (Fin (n + 1)) (Fin (n + 1)) (Qbar l)) *ᵥ v = (ψ 0 g : Qbar l) • v := fun g => by
      have := hv g
      change ((((ψ 0 g)⁻¹ : (Qbar l)ˣ) : Qbar l) • (r g : Matrix (Fin (n + 1)) (Fin (n + 1)) (Qbar l))) *ᵥ v = v at this
      rw [Matrix.smul_mulVec] at this
      rw [← congrArg (fun x => (ψ 0 g : Qbar l) • x) this, smul_smul, Units.mul_inv, one_smul]
    obtain ⟨p, r₁, r', e₁, c₁, c', b1, b2, b3, hfl⟩ := UpperTheory.exists_common_eigenline r ψ v hr v0 hv'
    have h2 := UpperTheory.deRhamRational_of_conj hB ι h r r₁ p hr e₁ _ _ hD
    refine hfl (ih r' c' (fun j => hh j.succ) (fun τ => (hmono τ).comp Fin.strictMono_succ) (fun j => ω j.succ) _
      (fun j => hO j.succ) (fun i j hij => hne _ _ fun e => hij (Fin.succ_injective _ e)) ?_)
    refine UpperTheory.deRham_rational_of_extension_by_character hB ι h r₁ r' (ψ 0) c₁ b1 b2 b3 (hh 0) _ _ _ ?_
      (_root_.UpperTheory.V.Loc.hecke_char_de_rham_of_local_artin_above_l hL h hw ι a ha _ _ _ (hO 0)).1
    convert h2 using 2
    · rw [Fin.univ_val_map, Fin.univ_val_map, List.ofFn_succ, Multiset.cons_coe]
    · rw [Fin.prod_univ_succ]
end Main
end Priv
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
/- English proof (translation)
Introduce `hL F Ω _ _ _ _ _ l _ _ ι n w hw A h a ha r hr hh hmono ω ψ hO hne hD`. Conclude with `⟨flag ι h hL hw ha n r hr hh hmono ω ψ hO hne hD, fun O _ _ _ Bw hj => (core ι h hL.aut.berger r hr _ (fun j => (ω j).comp a) (good_comp h ha hne) hD Bw hj).1⟩`.
-/
theorem UpperTheory.V.Loc.ordFlagU_alt :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (ι : Qbar l ≃+* ℂ) (n : ℕ) (w : HeightOneSpectrum (𝓞 L)), ((l : ℕ) : 𝓞 L) ∈ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion L)ˣ), IsLocalArtin h a → ∀ (r : Dec (F := L) A →* GL (Fin n) (Qbar l)), Continuous r → ∀ (hh : Fin n → (L →+* Qbar l) → ℤ), (∀ τ, StrictMono fun j => hh j τ) → ∀ (ω : Fin n → (w.adicCompletion L)ˣ →* ℂˣ) (ψ : Fin n → Dec (F := L) A →* (Qbar l)ˣ), (∀ j, OrdChar ι a (ω j) (hh j) (ψ j)) → (∀ i j, i ≠ j → ω i ≠ ω j ∧ ω i ≠ ω j * absPow (w.adicCompletion L) 1) → DRat ι h r (fun τ => Finset.univ.val.map fun j => hh j τ) (fun s => ∏ j, (X - C (ω j (a s) : ℂ))) → W.HasFlag r ψ ∧ PotCrys A r := by
  intro hL F Ω _ _ _ _ _ l _ _ ι n w hw A h a ha r hr hh hmono ω ψ hO hne hD
  exact ⟨flag ι h hL hw ha n r hr hh hmono ω ψ hO hne hD, fun O _ _ _ Bw hj =>
    (core ι h hL.aut.berger r hr _ (fun j => (ω j).comp a) (good_comp h ha hne) hD Bw hj).1⟩
end
