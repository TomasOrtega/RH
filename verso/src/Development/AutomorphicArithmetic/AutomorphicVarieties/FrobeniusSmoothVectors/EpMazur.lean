import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpresGr
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.SgWeight
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpNosec
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrDualb
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

/- English proof (translation)
Use `fin_cases j`. Conclude with `Or.inl rfl`. Conclude with `Or.inr rfl`.
-/
private theorem zcases (j : ZMod 2) : j = 0 ∨ j = 1 := by
  fin_cases j
  · exact Or.inl rfl
  · exact Or.inr rfl

/- English proof (translation)
Simplify using `[sg]`.
-/
private theorem sg0 (K : Type) [CommRing K] : sg K 0 = 1 := by simp [sg]

/- English proof (translation)
Rewrite using `[sg]`. Conclude with `pow_one (-1 : K)`.
-/
private theorem sg1 (K : Type) [CommRing K] : sg K 1 = -1 := by
  rw [sg]
  exact pow_one (-1 : K)

/- English proof (translation)
Break down `zcases j with rfl | rfl` into its components or cases. Rewrite using `[sg0, sg0, one_mul, one_smul]`. Rewrite using `[sg1, sg1, neg_one_mul, neg_one_smul]`.
-/
private theorem sg_smul {O C : Type} [CommRing O] [CommRing C] [Algebra O C] (j : ZMod 2) (y : C) :
    sg C j * y = sg O j • y := by
  rcases zcases j with rfl | rfl
  · rw [sg0, sg0, one_mul, one_smul]
  · rw [sg1, sg1, neg_one_mul, neg_one_smul]

/- English proof (translation)
Apply the tactic sequence `rcases zcases i with rfl | rfl <;> rcases zcases j with rfl | rfl`. Conclude with `absurd rfl h`. Rewrite using `[sg0, sg1, show (-1 - 1 : O) = -2 by ring]; exact h2.neg`. Rewrite using `[sg0, sg1, show (1 - -1 : O) = 2 by ring]; exact h2`. Conclude with `absurd rfl h`.
-/
private theorem sg_unit {O : Type} [CommRing O] (h2 : IsUnit (2 : O)) {i j : ZMod 2} (h : i ≠ j) :
    IsUnit (sg O j - sg O i) := by
  rcases zcases i with rfl | rfl <;> rcases zcases j with rfl | rfl
  · exact absurd rfl h
  · rw [sg0, sg1, show (-1 - 1 : O) = -2 by ring]; exact h2.neg
  · rw [sg0, sg1, show (1 - -1 : O) = 2 by ring]; exact h2
  · exact absurd rfl h

/- English proof (translation)
Unfold `UpperTheory.V.Fr.HasObsG at hobs`. Take `⟨ob, hob⟩` from `hobs C p τ hp hm hτ hpτ`. Take `⟨co, hco⟩` from `UpperTheory.V.Fr.pr_dualb O C (RingHom.ker p) κ ε hm hk hind`. Establish `hεK : ∀ u, ε u ∈ RingHom.ker p` using `fun u => hk ▸ Ideal.subset_span ⟨u, rfl⟩`. Establish `hεe : ∀ u, τ (ε u) = sg C (wf u) * ε u` using `fun u => hε u`.

Establish `hτsum : ∀ a : κ → O, τ (∑ u, a u • ε u) = ∑ u, (a u * sg O (wf u)) • ε u`. Introduce `a`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun u _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, hεe, sg_smul (O := O), smul_smul]`.

Establish `hzero : ∀ (y : ↥(RingHom.ker p)) (i : ZMod 2), τ (y : C) = sg C i * y → ∀ u, wf u ≠ i → co u y = 0`. Introduce `y i hy u hu`. Take `⟨a, ha, hya⟩` from `hco y`. Establish `h0 : ∑ w, (a w * (sg O (wf w) - sg O i)) • ε w = 0`. Establish `h1` using `hy`.

Rewrite `h1` using `[hya, hτsum, sg_smul (O := O), Finset.smul_sum]`. Simplify using `only [smul_smul] at h1`. Rewrite `h1` using `[← sub_eq_zero, ← Finset.sum_sub_distrib]`. Rewrite using `[← h1]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations.

Rewrite using `[← sub_smul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hmem` using `hind _ h0 u`. Establish `hU : IsUnit (sg O (wf u) - sg O i)` using `sg_unit h2 (fun e => hu e.symm)`.

Establish `hmem2` using `Ideal.mul_mem_right (↑hU.unit⁻¹ : O) _ hmem`. Rewrite `hmem2` using `[mul_assoc, IsUnit.mul_val_inv, mul_one]`. Rewrite using `[← ha u]`. Conclude with `(IsLocalRing.residue_eq_zero_iff _).2 hmem2`. Establish `hδ : ∀ u v, co u ⟨ε v, hεK v⟩ = if u = v then 1 else 0`.

Introduce `u v`. Take `⟨a, ha, hya⟩` from `hco ⟨ε v, hεK v⟩`. Establish `h0 : ∑ w, (a w - if w = v then 1 else 0) • ε w = 0`. Simplify using `only [sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Rewrite using `[← hya]`.

Conclude with `sub_self _`. Establish `hmem` using `hind _ h0 u`. Establish `h3 : residue O (a u - if u = v then 1 else 0) = 0` using `(IsLocalRing.residue_eq_zero_iff _).2 hmem`. Rewrite `h3` using `[map_sub, sub_eq_zero]`. Rewrite using `[← ha u, h3]`.

Apply the tactic sequence `split_ifs <;> simp`. Establish `hform : ∀ u, wf u = j → co u ∈ formp τ (RingHom.ker p) j`. Introduce `u hu`. Use `show ∀ i, i ≠ j → ∀ y : ↥(RingHom.ker p), ↑y ∈ evp τ i → co u y = 0`. Introduce `i hij y hy`.

Conclude with `hzero y i hy u (by rw [hu]; exact fun e => hij e.symm)`. Establish `hinj : Function.Injective ob`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `u hu`. Set `I : Ideal C` to `{ carrier := {y | ∃ h : y ∈ RingHom.ker p, (u : ↥(RingHom.ker p) →ₗ[O] ResidueField O) ⟨y, h⟩ = 0} add_mem' := by`.

Introduce and unpack `y z ⟨hy, hy'⟩ ⟨hz, hz'⟩`. Use `⟨Ideal.add_mem _ hy hz, ?_⟩` and prove the remaining obligations. Establish `: (⟨y + z, Ideal.add_mem _ hy hz⟩ : ↥(RingHom.ker p)) = ⟨y, hy⟩ + ⟨z, hz⟩` using `rfl`. Rewrite using `[this, map_add, hy', hz', add_zero]`. Use the proof step `zero_mem' := ⟨Ideal.zero_mem _, by`.

Establish `: (⟨0, Ideal.zero_mem _⟩ : ↥(RingHom.ker p)) = 0` using `rfl`. Rewrite using `[this, map_zero]⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `c y ⟨hy, hy'⟩`. Take `⟨a, ha⟩` from `IsCO.res_surj (O := O) c`.

Establish `hmul : (c - algebraMap O C a) * y = 0`. Use `Ideal.mul_mem_mul ha hy` as an intermediate fact. Rewrite `this` using `[hm]`. Conclude with `Ideal.mem_bot.1 this`. Use `⟨Ideal.mul_mem_left _ c hy, ?_⟩` and prove the remaining obligations.

Establish `: (⟨c • y, Ideal.mul_mem_left _ c hy⟩ : ↥(RingHom.ker p)) = a • ⟨y, hy⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show c * y = a • y`. Rewrite using `[Algebra.smul_def]`. Conclude with `sub_eq_zero.1 (by rw [← sub_mul]; exact hmul)`.

Rewrite using `[this, map_smul, hy', smul_zero] }`. Establish `hIK : I ≤ RingHom.ker p` using `fun y hy => hy.1`. Establish `hI1 : I ≠ ⊤`. Introduce `h`. Establish `h1 : (1 : C) ∈ RingHom.ker p` using `hIK (h ▸ Submodule.mem_top)`.

Rewrite `h1` using `[RingHom.mem_ker, map_one]`. Conclude with `one_ne_zero h1`. Use `haveI : Nontrivial (C ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI1`. Use `haveI : IsCO O (C ⧸ I) := co_quot O C (C ⧸ I) (Ideal.Quotient.mkₐ O I) (Ideal.Quotient.mkₐ_surjective O I)`. Set `q : C →ₐ[O] C ⧸ I` to `Ideal.Quotient.mkₐ O I`.

Set `p'' : C ⧸ I →ₐ[O] R` to `Ideal.Quotient.liftₐ I p (fun y hy => hIK hy)`. Establish `hcomp : p''.comp q = p`. Use extensionality with `y`. Both sides reduce to the same expression. Establish `hqs : Function.Surjective q` using `Ideal.Quotient.mkₐ_surjective O I`.

Establish `hq : ∀ y : ↥(RingHom.ker p), (u : ↥(RingHom.ker p) →ₗ[O] ResidueField O) y = 0 → q y = 0`. Introduce `y hy`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 ⟨y.2, hy⟩`. Take `⟨s, hs⟩` from `hob u hu (C ⧸ I) q p'' hcomp hqs hq`. Establish `hinj'` using `hno (C ⧸ I) q p'' s hcomp hqs hs`.

Apply `Subtype.ext` to reduce the goal to its premises. Use `LinearMap.ext fun y => ?_` and prove the remaining obligations. Establish `hqy : q (y : C) = 0` using `hinj' (by rw [map_zero]; exact RingHom.mem_ker.1 y.2)`. Take `⟨_, h'⟩` from `Ideal.Quotient.eq_zero_iff_mem.1 hqy`. Use `show _ = (0 : ResidueField O)`.

Conclude with `h'`. Set `w : {u // wf u = j} → ↥(formp τ (RingHom.ker p) j)` to `fun u => ⟨co u.1, hform u.1 u.2⟩`. Establish `hli : LinearIndependent (ResidueField O) w`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg v`.

Establish `hv` using `congrArg (fun f : ↥(formp τ (RingHom.ker p) j) => (f : ↥(RingHom.ker p) →ₗ[O] ResidueField O) ⟨ε v.1, hεK v.1⟩) hg`. Simplify `hv` using `[w, hδ, Subtype.val_inj]`. Establish `hli2` using `hli.map' ob (LinearMap.ker_eq_bot.2 hinj)`. Rewrite using `[Nat.card_eq_fintype_card]`. Conclude with `hli2.fintype_card_le_finrank`.
-/
private theorem small {O : Type} [CommRing O] [IsLocalRing O] (h2 : IsUnit (2 : O)) {R : Type} [CommRing R]
    [Algebra O R] [IsCO O R] (σ : R →ₐ[O] R) (j : ZMod 2) (H : Type) [AddCommGroup H] [Module (ResidueField O) H]
    [Module.Finite (ResidueField O) H] (hobs : HasObsG O σ j H) (C : Type) [CommRing C] [Algebra O C] [IsCO O C]
    (p : C →ₐ[O] R) (τ : C →ₐ[O] C) (hp : Function.Surjective p) (hm : maximalIdeal C * RingHom.ker p = ⊥)
    (hτ : ∀ y, τ (τ y) = y) (hpτ : ∀ y, p (τ y) = σ (p y)) (κ : Type) [Fintype κ] (ε : κ → C) (wf : κ → ZMod 2)
    (hε : ∀ u, ε u ∈ evp τ (wf u)) (hk : RingHom.ker p = Ideal.span (Set.range ε))
    (hind : ∀ c : κ → O, ∑ u, c u • ε u = 0 → ∀ u, c u ∈ maximalIdeal O)
    (hno : ∀ (C' : Type) [CommRing C'] [Algebra O C'] [IsCO O C'] (q : C →ₐ[O] C') (p' : C' →ₐ[O] R)
      (s : R →ₐ[O] C'), p'.comp q = p → Function.Surjective q → p'.comp s = AlgHom.id O R → Function.Injective p') :
    Nat.card {u // wf u = j} ≤ Module.finrank (ResidueField O) H := by
  classical
  unfold UpperTheory.V.Fr.HasObsG at hobs
  obtain ⟨ob, hob⟩ := hobs C p τ hp hm hτ hpτ
  obtain ⟨co, hco⟩ := UpperTheory.V.Fr.pr_dualb O C (RingHom.ker p) κ ε hm hk hind
  have hεK : ∀ u, ε u ∈ RingHom.ker p := fun u => hk ▸ Ideal.subset_span ⟨u, rfl⟩
  have hεe : ∀ u, τ (ε u) = sg C (wf u) * ε u := fun u => hε u
  have hτsum : ∀ a : κ → O, τ (∑ u, a u • ε u) = ∑ u, (a u * sg O (wf u)) • ε u := by
    intro a
    rw [map_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [map_smul, hεe, sg_smul (O := O), smul_smul]
  have hzero : ∀ (y : ↥(RingHom.ker p)) (i : ZMod 2), τ (y : C) = sg C i * y → ∀ u, wf u ≠ i → co u y = 0 := by
    intro y i hy u hu
    obtain ⟨a, ha, hya⟩ := hco y
    have h0 : ∑ w, (a w * (sg O (wf w) - sg O i)) • ε w = 0 := by
      have h1 := hy
      rw [hya, hτsum, sg_smul (O := O), Finset.smul_sum] at h1
      simp only [smul_smul] at h1
      rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at h1
      rw [← h1]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [← sub_smul]
      congr 1
      ring
    have hmem := hind _ h0 u
    have hU : IsUnit (sg O (wf u) - sg O i) := sg_unit h2 (fun e => hu e.symm)
    have hmem2 := Ideal.mul_mem_right (↑hU.unit⁻¹ : O) _ hmem
    rw [mul_assoc, IsUnit.mul_val_inv, mul_one] at hmem2
    rw [← ha u]
    exact (IsLocalRing.residue_eq_zero_iff _).2 hmem2
  have hδ : ∀ u v, co u ⟨ε v, hεK v⟩ = if u = v then 1 else 0 := by
    intro u v
    obtain ⟨a, ha, hya⟩ := hco ⟨ε v, hεK v⟩
    have h0 : ∑ w, (a w - if w = v then 1 else 0) • ε w = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [← hya]
      exact sub_self _
    have hmem := hind _ h0 u
    have h3 : residue O (a u - if u = v then 1 else 0) = 0 := (IsLocalRing.residue_eq_zero_iff _).2 hmem
    rw [map_sub, sub_eq_zero] at h3
    rw [← ha u, h3]
    split_ifs <;> simp
  have hform : ∀ u, wf u = j → co u ∈ formp τ (RingHom.ker p) j := by
    intro u hu
    show ∀ i, i ≠ j → ∀ y : ↥(RingHom.ker p), ↑y ∈ evp τ i → co u y = 0
    intro i hij y hy
    exact hzero y i hy u (by rw [hu]; exact fun e => hij e.symm)
  have hinj : Function.Injective ob := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    let I : Ideal C :=
      { carrier := {y | ∃ h : y ∈ RingHom.ker p, (u : ↥(RingHom.ker p) →ₗ[O] ResidueField O) ⟨y, h⟩ = 0}
        add_mem' := by
          rintro y z ⟨hy, hy'⟩ ⟨hz, hz'⟩
          refine ⟨Ideal.add_mem _ hy hz, ?_⟩
          have : (⟨y + z, Ideal.add_mem _ hy hz⟩ : ↥(RingHom.ker p)) = ⟨y, hy⟩ + ⟨z, hz⟩ := rfl
          rw [this, map_add, hy', hz', add_zero]
        zero_mem' := ⟨Ideal.zero_mem _, by
          have : (⟨0, Ideal.zero_mem _⟩ : ↥(RingHom.ker p)) = 0 := rfl
          rw [this, map_zero]⟩
        smul_mem' := by
          rintro c y ⟨hy, hy'⟩
          obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) c
          have hmul : (c - algebraMap O C a) * y = 0 := by
            have := Ideal.mul_mem_mul ha hy
            rw [hm] at this
            exact Ideal.mem_bot.1 this
          refine ⟨Ideal.mul_mem_left _ c hy, ?_⟩
          have : (⟨c • y, Ideal.mul_mem_left _ c hy⟩ : ↥(RingHom.ker p)) = a • ⟨y, hy⟩ := by
            apply Subtype.ext
            show c * y = a • y
            rw [Algebra.smul_def]
            exact sub_eq_zero.1 (by rw [← sub_mul]; exact hmul)
          rw [this, map_smul, hy', smul_zero] }
    have hIK : I ≤ RingHom.ker p := fun y hy => hy.1
    have hI1 : I ≠ ⊤ := by
      intro h
      have h1 : (1 : C) ∈ RingHom.ker p := hIK (h ▸ Submodule.mem_top)
      rw [RingHom.mem_ker, map_one] at h1
      exact one_ne_zero h1
    haveI : Nontrivial (C ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI1
    haveI : IsCO O (C ⧸ I) := co_quot O C (C ⧸ I) (Ideal.Quotient.mkₐ O I) (Ideal.Quotient.mkₐ_surjective O I)
    let q : C →ₐ[O] C ⧸ I := Ideal.Quotient.mkₐ O I
    let p'' : C ⧸ I →ₐ[O] R := Ideal.Quotient.liftₐ I p (fun y hy => hIK hy)
    have hcomp : p''.comp q = p := by
      ext y
      rfl
    have hqs : Function.Surjective q := Ideal.Quotient.mkₐ_surjective O I
    have hq : ∀ y : ↥(RingHom.ker p), (u : ↥(RingHom.ker p) →ₗ[O] ResidueField O) y = 0 → q y = 0 := by
      intro y hy
      exact Ideal.Quotient.eq_zero_iff_mem.2 ⟨y.2, hy⟩
    obtain ⟨s, hs⟩ := hob u hu (C ⧸ I) q p'' hcomp hqs hq
    have hinj' := hno (C ⧸ I) q p'' s hcomp hqs hs
    apply Subtype.ext
    refine LinearMap.ext fun y => ?_
    have hqy : q (y : C) = 0 := hinj' (by rw [map_zero]; exact RingHom.mem_ker.1 y.2)
    obtain ⟨_, h'⟩ := Ideal.Quotient.eq_zero_iff_mem.1 hqy
    show _ = (0 : ResidueField O)
    exact h'
  let w : {u // wf u = j} → ↥(formp τ (RingHom.ker p) j) := fun u => ⟨co u.1, hform u.1 u.2⟩
  have hli : LinearIndependent (ResidueField O) w := by
    rw [Fintype.linearIndependent_iff]
    intro g hg v
    have hv := congrArg (fun f : ↥(formp τ (RingHom.ker p) j) => (f : ↥(RingHom.ker p) →ₗ[O] ResidueField O) ⟨ε v.1, hεK v.1⟩) hg
    simpa [w, hδ, Subtype.val_inj] using hv
  have hli2 := hli.map' ob (LinearMap.ker_eq_bot.2 hinj)
  rw [Nat.card_eq_fintype_card]
  exact hli2.fintype_card_le_finrank

/- English proof (translation)
Introduce `O _ _ _ _ h2 R _ _ _ σ hσ P j H _ _ _ hobs`. Use `haveI hA : IsCO O (MvPowerSeries (Fin P.a ⊕ Fin P.g) O) := co_mvps O O (Fin P.a ⊕ Fin P.g)`. Take `⟨τ0, hτ0, hev, hdec⟩` from `ep_ps O h2 (Fin P.a ⊕ Fin P.g) (Space.Loc.par P.a P.g)`. Establish `hwp : ∀ i (y : MvPowerSeries (Fin P.a ⊕ Fin P.g) O), y ∈ wtPart O (Space.Loc.par P.a P.g) i → σ (P.p y) = sg R i * P.p y`. Introduce `i y hy`.

Establish `hmem : P.p y ∈ evp σ i`. Rewrite using `[← P.part i]`. Conclude with `Submodule.mem_map_of_mem hy`. Conclude with `hmem`. Establish `hu2 : IsUnit (2 : MvPowerSeries (Fin P.a ⊕ Fin P.g) O)`.

Establish `h2'` using `h2.map (algebraMap O (MvPowerSeries (Fin P.a ⊕ Fin P.g) O))`. Rewrite `h2'` using `[map_ofNat]`. Conclude with `h2'`. Establish `hpτ0 : ∀ y, P.p (τ0 y) = σ (P.p y)`. Introduce `y`.

Establish `ha` using `hdec 0 y`. Establish `hb` using `hdec 1 y`. Rewrite `ha` using `[sg0]`. Rewrite `hb` using `[sg1]`. Establish `hy : y = wcomp O (Space.Loc.par P.a P.g) 0 y + wcomp O (Space.Loc.par P.a P.g) 1 y` using `hu2.mul_left_cancel (by rw [mul_add, ha, hb]; ring)`.

Establish `hty : τ0 y = wcomp O (Space.Loc.par P.a P.g) 0 y - wcomp O (Space.Loc.par P.a P.g) 1 y` using `hu2.mul_left_cancel (by rw [mul_sub, ha, hb]; ring)`. Establish `hpa` using `hwp 0 _ (wcomp_mem O (Space.Loc.par P.a P.g) 0 y)`. Establish `hpb` using `hwp 1 _ (wcomp_mem O (Space.Loc.par P.a P.g) 1 y)`. Rewrite `hpa` using `[sg0, one_mul]`. Rewrite `hpb` using `[sg1, neg_one_mul]`.

Rewrite using `[hty, map_sub]`. Use `conv_rhs => rw [hy]`. Rewrite using `[map_add, map_add, hpa, hpb, sub_eq_add_neg]`. Establish `hτk : ∀ y ∈ RingHom.ker P.p, τ0 y ∈ RingHom.ker P.p`. Introduce `y hy`.

Rewrite `hy`, the goal using `[RingHom.mem_ker]`. Use `show P.p (τ0 y) = 0`. Rewrite using `[hpτ0]`. Rewrite using `[show P.p y = 0 from hy, map_zero]`. Establish `hτm : ∀ y ∈ maximalIdeal (MvPowerSeries (Fin P.a ⊕ Fin P.g) O), τ0 y ∈ maximalIdeal (MvPowerSeries (Fin P.a ⊕ Fin P.g) O)`.

Introduce `y hy`. Rewrite `hy`, the goal using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Introduce `hu`. Apply `hy` to reduce the goal to its premises. Establish `h'` using `hu.map τ0`.

Rewrite `h'` using `[hτ0]`. Then use the resulting hypothesis. Set `J : Ideal (MvPowerSeries (Fin P.a ⊕ Fin P.g) O)` to `maximalIdeal (MvPowerSeries (Fin P.a ⊕ Fin P.g) O) * RingHom.ker P.p`. Establish `hJ : J ≤ J.comap τ0`. Rewrite using `[Ideal.mul_le]`. Introduce `r hr s hs`.

Use `show τ0 (r * s) ∈ J`. Rewrite using `[map_mul]`. Conclude with `Ideal.mul_mem_mul (hτm r hr) (hτk s hs)`. Establish `hJk : J ≤ RingHom.ker P.p` using `Ideal.mul_le.2 (fun r _ s hs => Ideal.mul_mem_left _ r hs)`. Establish `hJtop : J ≠ ⊤`.

Introduce `h`. Establish `h1 : (1 : MvPowerSeries (Fin P.a ⊕ Fin P.g) O) ∈ RingHom.ker P.p` using `hJk (h ▸ Submodule.mem_top)`. Rewrite `h1` using `[RingHom.mem_ker, map_one]`. Conclude with `one_ne_zero h1`. Use `haveI : Nontrivial (MvPowerSeries (Fin P.a ⊕ Fin P.g) O ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJtop`.

Use `haveI : IsCO O (MvPowerSeries (Fin P.a ⊕ Fin P.g) O ⧸ J) := co_quot O _ _ (Ideal.Quotient.mkₐ O J) (Ideal.Quotient.mkₐ_surjective O J)`. Establish `hsurj` using `Ideal.Quotient.mkₐ_surjective O J`. Set `pC : (MvPowerSeries (Fin P.a ⊕ Fin P.g) O ⧸ J) →ₐ[O] R` to `Ideal.Quotient.liftₐ J P.p (fun y hy => RingHom.mem_ker.1 (hJk hy))`. Set `τC : (MvPowerSeries (Fin P.a ⊕ Fin P.g) O ⧸ J) →ₐ[O] (MvPowerSeries (Fin P.a ⊕ Fin P.g) O ⧸ J)` to `Ideal.quotientMapₐ J τ0 hJ`. Use `small h2 σ j H hobs (MvPowerSeries (Fin P.a ⊕ Fin P.g) O ⧸ J) pC τC ?_ ?_ ?_ ?_ P.κ (fun u => Ideal.Quotient.mkₐ O J (P.f u)) P.wf ?_ ?_ ?_ ?_` and prove the remaining obligations.

Introduce `r`. Take `⟨y, rfl⟩` from `P.surj r`. Conclude with `⟨Ideal.Quotient.mkₐ O J y, rfl⟩`. Rewrite using `[eq_bot_iff, Ideal.mul_le]`. Introduce `r hr s hs`.

Take `⟨r', rfl⟩` from `hsurj r`. Take `⟨s', rfl⟩` from `hsurj s`. Rewrite using `[Ideal.mem_bot, ← map_mul]`. Use `show Ideal.Quotient.mk J (r' * s') = 0`. Apply `Ideal.Quotient.eq_zero_iff_mem.2` to reduce the goal to its premises.

Use `Ideal.mul_mem_mul ?_ ?_` and prove the remaining obligations. Rewrite `hr`, the goal using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Conclude with `fun hu => hr (hu.map (Ideal.Quotient.mkₐ O J))`. Conclude with `hs`. Introduce `y`.

Take `⟨y', rfl⟩` from `hsurj y`. Use `show Ideal.Quotient.mkₐ O J (τ0 (τ0 y')) = Ideal.Quotient.mkₐ O J y'`. Rewrite using `[hτ0]`. Introduce `y`. Take `⟨y', rfl⟩` from `hsurj y`.

Conclude with `hpτ0 y'`. Introduce `u`. Establish `hf : τ0 (P.f u) = sg (MvPowerSeries (Fin P.a ⊕ Fin P.g) O) (P.wf u) * P.f u`. Establish `h'` using `P.hf u`. Rewrite `h'` using `[← hev]`.

Conclude with `h'`. Use `show Ideal.Quotient.mkₐ O J (τ0 (P.f u)) = _`. Rewrite using `[hf, sg_smul (O := O), map_smul, ← sg_smul (O := O)]`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `y hy`.

Take `⟨y', rfl⟩` from `hsurj y`. Establish `hy' : y' ∈ RingHom.ker P.p` using `hy`. Rewrite `hy'` using `[P.ker]`. Establish `h'` using `Ideal.mem_map_of_mem (Ideal.Quotient.mk J) hy'`. Rewrite `h'` using `[Ideal.map_span, ← Set.range_comp]`.

Conclude with `h'`. Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨u, rfl⟩`. Establish `h' : P.f u ∈ RingHom.ker P.p` using `P.ker ▸ Ideal.subset_span ⟨u, rfl⟩`. Conclude with `h'`.

Introduce `c hc`. Apply `P.indep c` to reduce the goal to its premises. Establish `h' : Ideal.Quotient.mkₐ O J (∑ u, c u • P.f u) = 0`. Rewrite using `[map_sum]`. Simplify using `only [map_smul]`.

Conclude with `hc`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.1 h'`. Introduce `C' _ _ _ q p' s hcomp hq hs`. Establish `hc2 : p'.comp (q.comp (Ideal.Quotient.mkₐ O J)) = P.p`. Rewrite using `[← AlgHom.comp_assoc, hcomp]`.

Conclude with `AlgHom.ext fun y => rfl`. Use `ep_nosec O (Fin P.a ⊕ Fin P.g) R C' (q.comp (Ideal.Quotient.mkₐ O J)) p' s (hq.comp hsurj) ?_ ?_ hs` and prove the remaining obligations. Rewrite using `[hc2]`. Conclude with `⟨P.surj, P.min⟩`. Introduce `i`.

Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Introduce `hu`. Establish `e : p' ((q.comp (Ideal.Quotient.mkₐ O J)) (MvPowerSeries.X i)) = P.p (MvPowerSeries.X i)`. Rewrite using `[← AlgHom.comp_apply, hc2]`. Establish `h1 : IsUnit (P.p (MvPowerSeries.X i))`.

Rewrite using `[← e]`. Conclude with `hu.map p'`. Establish `hv` using `P.var i`. Rewrite `hv` using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Conclude with `hv h1`.
-/
theorem UpperTheory.V.Fr.ep_mazur :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O], IsUnit (2 : O) → ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (σ : R →ₐ[O] R), (∀ y, σ (σ y) = y) → ∀ (P : GPres O σ) (j : ZMod 2) (H : Type) [AddCommGroup H] [Module (ResidueField O) H] [Module.Finite (ResidueField O) H], HasObsG O σ j H → Nat.card {u // P.wf u = j} ≤ Module.finrank (ResidueField O) H := by
  intro O _ _ _ _ h2 R _ _ _ σ hσ P j H _ _ _ hobs
  classical
  haveI hA : IsCO O (MvPowerSeries (Fin P.a ⊕ Fin P.g) O) := co_mvps O O (Fin P.a ⊕ Fin P.g)
  obtain ⟨τ0, hτ0, hev, hdec⟩ := ep_ps O h2 (Fin P.a ⊕ Fin P.g) (Space.Loc.par P.a P.g)
  have hwp : ∀ i (y : MvPowerSeries (Fin P.a ⊕ Fin P.g) O), y ∈ wtPart O (Space.Loc.par P.a P.g) i → σ (P.p y) = sg R i * P.p y := by
    intro i y hy
    have hmem : P.p y ∈ evp σ i := by
      rw [← P.part i]
      exact Submodule.mem_map_of_mem hy
    exact hmem
  have hu2 : IsUnit (2 : MvPowerSeries (Fin P.a ⊕ Fin P.g) O) := by
    have h2' := h2.map (algebraMap O (MvPowerSeries (Fin P.a ⊕ Fin P.g) O))
    rw [map_ofNat] at h2'
    exact h2'
  have hpτ0 : ∀ y, P.p (τ0 y) = σ (P.p y) := by
    intro y
    have ha := hdec 0 y
    have hb := hdec 1 y
    rw [sg0] at ha
    rw [sg1] at hb
    have hy : y = wcomp O (Space.Loc.par P.a P.g) 0 y + wcomp O (Space.Loc.par P.a P.g) 1 y :=
      hu2.mul_left_cancel (by rw [mul_add, ha, hb]; ring)
    have hty : τ0 y = wcomp O (Space.Loc.par P.a P.g) 0 y - wcomp O (Space.Loc.par P.a P.g) 1 y :=
      hu2.mul_left_cancel (by rw [mul_sub, ha, hb]; ring)
    have hpa := hwp 0 _ (wcomp_mem O (Space.Loc.par P.a P.g) 0 y)
    have hpb := hwp 1 _ (wcomp_mem O (Space.Loc.par P.a P.g) 1 y)
    rw [sg0, one_mul] at hpa
    rw [sg1, neg_one_mul] at hpb
    rw [hty, map_sub]
    conv_rhs => rw [hy]
    rw [map_add, map_add, hpa, hpb, sub_eq_add_neg]
  have hτk : ∀ y ∈ RingHom.ker P.p, τ0 y ∈ RingHom.ker P.p := by
    intro y hy
    rw [RingHom.mem_ker] at hy ⊢
    show P.p (τ0 y) = 0
    rw [hpτ0]
    rw [show P.p y = 0 from hy, map_zero]
  have hτm : ∀ y ∈ maximalIdeal (MvPowerSeries (Fin P.a ⊕ Fin P.g) O), τ0 y ∈ maximalIdeal (MvPowerSeries (Fin P.a ⊕ Fin P.g) O) := by
    intro y hy
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hy ⊢
    intro hu
    apply hy
    have h' := hu.map τ0
    rwa [hτ0] at h'
  let J : Ideal (MvPowerSeries (Fin P.a ⊕ Fin P.g) O) := maximalIdeal (MvPowerSeries (Fin P.a ⊕ Fin P.g) O) * RingHom.ker P.p
  have hJ : J ≤ J.comap τ0 := by
    rw [Ideal.mul_le]
    intro r hr s hs
    show τ0 (r * s) ∈ J
    rw [map_mul]
    exact Ideal.mul_mem_mul (hτm r hr) (hτk s hs)
  have hJk : J ≤ RingHom.ker P.p := Ideal.mul_le.2 (fun r _ s hs => Ideal.mul_mem_left _ r hs)
  have hJtop : J ≠ ⊤ := by
    intro h
    have h1 : (1 : MvPowerSeries (Fin P.a ⊕ Fin P.g) O) ∈ RingHom.ker P.p := hJk (h ▸ Submodule.mem_top)
    rw [RingHom.mem_ker, map_one] at h1
    exact one_ne_zero h1
  haveI : Nontrivial (MvPowerSeries (Fin P.a ⊕ Fin P.g) O ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJtop
  haveI : IsCO O (MvPowerSeries (Fin P.a ⊕ Fin P.g) O ⧸ J) := co_quot O _ _ (Ideal.Quotient.mkₐ O J) (Ideal.Quotient.mkₐ_surjective O J)
  have hsurj := Ideal.Quotient.mkₐ_surjective O J
  let pC : (MvPowerSeries (Fin P.a ⊕ Fin P.g) O ⧸ J) →ₐ[O] R := Ideal.Quotient.liftₐ J P.p (fun y hy => RingHom.mem_ker.1 (hJk hy))
  let τC : (MvPowerSeries (Fin P.a ⊕ Fin P.g) O ⧸ J) →ₐ[O] (MvPowerSeries (Fin P.a ⊕ Fin P.g) O ⧸ J) := Ideal.quotientMapₐ J τ0 hJ
  refine small h2 σ j H hobs (MvPowerSeries (Fin P.a ⊕ Fin P.g) O ⧸ J) pC τC ?_ ?_ ?_ ?_ P.κ (fun u => Ideal.Quotient.mkₐ O J (P.f u)) P.wf ?_ ?_ ?_ ?_
  · intro r
    obtain ⟨y, rfl⟩ := P.surj r
    exact ⟨Ideal.Quotient.mkₐ O J y, rfl⟩
  · rw [eq_bot_iff, Ideal.mul_le]
    intro r hr s hs
    obtain ⟨r', rfl⟩ := hsurj r
    obtain ⟨s', rfl⟩ := hsurj s
    rw [Ideal.mem_bot, ← map_mul]
    show Ideal.Quotient.mk J (r' * s') = 0
    apply Ideal.Quotient.eq_zero_iff_mem.2
    refine Ideal.mul_mem_mul ?_ ?_
    · rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hr ⊢
      exact fun hu => hr (hu.map (Ideal.Quotient.mkₐ O J))
    · exact hs
  · intro y
    obtain ⟨y', rfl⟩ := hsurj y
    show Ideal.Quotient.mkₐ O J (τ0 (τ0 y')) = Ideal.Quotient.mkₐ O J y'
    rw [hτ0]
  · intro y
    obtain ⟨y', rfl⟩ := hsurj y
    exact hpτ0 y'
  · intro u
    have hf : τ0 (P.f u) = sg (MvPowerSeries (Fin P.a ⊕ Fin P.g) O) (P.wf u) * P.f u := by
      have h' := P.hf u
      rw [← hev] at h'
      exact h'
    show Ideal.Quotient.mkₐ O J (τ0 (P.f u)) = _
    rw [hf, sg_smul (O := O), map_smul, ← sg_smul (O := O)]
  · apply le_antisymm
    · intro y hy
      obtain ⟨y', rfl⟩ := hsurj y
      have hy' : y' ∈ RingHom.ker P.p := hy
      rw [P.ker] at hy'
      have h' := Ideal.mem_map_of_mem (Ideal.Quotient.mk J) hy'
      rw [Ideal.map_span, ← Set.range_comp] at h'
      exact h'
    · rw [Ideal.span_le]
      rintro _ ⟨u, rfl⟩
      have h' : P.f u ∈ RingHom.ker P.p := P.ker ▸ Ideal.subset_span ⟨u, rfl⟩
      exact h'
  · intro c hc
    apply P.indep c
    have h' : Ideal.Quotient.mkₐ O J (∑ u, c u • P.f u) = 0 := by
      rw [map_sum]
      simp only [map_smul]
      exact hc
    exact Ideal.Quotient.eq_zero_iff_mem.1 h'
  · intro C' _ _ _ q p' s hcomp hq hs
    have hc2 : p'.comp (q.comp (Ideal.Quotient.mkₐ O J)) = P.p := by
      rw [← AlgHom.comp_assoc, hcomp]
      exact AlgHom.ext fun y => rfl
    refine ep_nosec O (Fin P.a ⊕ Fin P.g) R C' (q.comp (Ideal.Quotient.mkₐ O J)) p' s (hq.comp hsurj) ?_ ?_ hs
    · rw [hc2]
      exact ⟨P.surj, P.min⟩
    · intro i
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have e : p' ((q.comp (Ideal.Quotient.mkₐ O J)) (MvPowerSeries.X i)) = P.p (MvPowerSeries.X i) := by
        rw [← AlgHom.comp_apply, hc2]
      have h1 : IsUnit (P.p (MvPowerSeries.X i)) := by
        rw [← e]
        exact hu.map p'
      have hv := P.var i
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hv
      exact hv h1
