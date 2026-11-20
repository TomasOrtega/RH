import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.WdDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharAbove
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.WeilGroupDenseInGaloisGroup
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
Take `⟨n, hn, hp⟩` from `exists_period h Bw hj P ρ x (hW x hxI)`. Take `⟨c, hc1, hc2⟩` from `exists_orbit l n hn`. Take `⟨j, hz0, hz1⟩` from `exists_trace (mulD P ρ) (phiD P ρ) n (by omega) (fun i => (frobUr l ^ i) c) hc2 (by simpa using hc1) (fun i j => by rw [phiD_pow_mulD, pow_zero, AlgHom.one_apply, map_pow]) x hx0 hp`. Use `⟨_, hz0, hz1, fix_of_weil h Bw P ρ _ fun σ => ?_⟩` and prove the remaining obligations. Use `(congrArg (actD P ρ (weilToGK Bw h σ)) (zpow_fix (phiU P ρ) _ hz1 (-alpha l σ))).symm.trans (hW _ (fun s => ?_) σ)` and prove the remaining obligations.

Establish `hcm : Commute (weilD Bw h P ρ (ineIncl h s)) (∑ i ∈ Finset.range n, phiD P ρ ^ i * mulD P ρ ((frobUr l ^ 0) c ^ j))`. Use `Commute.sum_right _ _ _ fun i _ => Commute.mul_right (Commute.pow_right ?_ i) (weilD_mulD Bw h P ρ hj _ _)` and prove the remaining obligations. Rewrite using `[weilD_ineIncl]`. Conclude with `(phiD_actD P ρ _).symm`. Conclude with `(LinearMap.congr_fun hcm.eq x).trans (congrArg _ (hxI s))`.
-/
private theorem main (x : ↥(Dpst P ρ)) (hx0 : x ≠ 0) (hxI : ∀ s, weilD Bw h P ρ (ineIncl h s) x = x)
    (hW : ∀ x : ↥(Dpst P ρ), (∀ s, weilD Bw h P ρ (ineIncl h s) x = x) → ∀ σ, weilD Bw h P ρ σ x = x) :
    ∃ z : ↥(Dpst P ρ), z ≠ 0 ∧ phiD P ρ z = z ∧ ∀ g, actD P ρ g z = z := by
  obtain ⟨n, hn, hp⟩ := exists_period h Bw hj P ρ x (hW x hxI)
  obtain ⟨c, hc1, hc2⟩ := exists_orbit l n hn
  obtain ⟨j, hz0, hz1⟩ := exists_trace (mulD P ρ) (phiD P ρ) n (by omega) (fun i => (frobUr l ^ i) c) hc2
    (by simpa using hc1) (fun i j => by rw [phiD_pow_mulD, pow_zero, AlgHom.one_apply, map_pow]) x hx0 hp
  refine ⟨_, hz0, hz1, fix_of_weil h Bw P ρ _ fun σ => ?_⟩
  refine (congrArg (actD P ρ (weilToGK Bw h σ)) (zpow_fix (phiU P ρ) _ hz1 (-alpha l σ))).symm.trans
    (hW _ (fun s => ?_) σ)
  have hcm : Commute (weilD Bw h P ρ (ineIncl h s)) (∑ i ∈ Finset.range n, phiD P ρ ^ i *
      mulD P ρ ((frobUr l ^ 0) c ^ j)) := by
    refine Commute.sum_right _ _ _ fun i _ => Commute.mul_right (Commute.pow_right ?_ i)
      (weilD_mulD Bw h P ρ hj _ _)
    rw [weilD_ineIncl]
    exact (phiD_actD P ρ _).symm
  exact (LinearMap.congr_fun hcm.eq x).trans (congrArg _ (hxI s))

end

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ l hl A w h O _ _ _ Bw hj P L V _ _ _ _ _ ρ _ ⟨x, hx0, hxI⟩ hW`. Conclude with `main h Bw hj P ρ x hx0 hxI hW`.
-/
theorem UpperTheory.exists_frobenius_fixed_period :
    ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (_hj : GlobalTheory.Pst.Induces Bw) (P : LocPrime l) {L : FinExt l} {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V] [FiniteDimensional ↥L.1 V] (ρ : Representation ↥L.1 ↥(GK Bw.Kw) V) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)], (∃ x : ↥(Dpst P ρ), x ≠ 0 ∧ ∀ s, weilD Bw h P ρ (ineIncl h s) x = x) → (∀ x : ↥(Dpst P ρ), (∀ s, weilD Bw h P ρ (ineIncl h s) x = x) → ∀ σ, weilD Bw h P ρ σ x = x) → ∃ z : ↥(Dpst P ρ), z ≠ 0 ∧ phiD P ρ z = z ∧ ∀ g, actD P ρ g z = z := by
  intro F Ω _ _ _ _ _ l hl A w h O _ _ _ Bw hj P L V _ _ _ _ _ ρ _ ⟨x, hx0, hxI⟩ hW
  exact main h Bw hj P ρ x hx0 hxI hW
