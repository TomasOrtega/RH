import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.PartClosed

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

/- English proof (translation)
Establish `hT : Module.IsTorsionBySet R K (maximalIdeal R : Set R)`. Introduce `x a`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `h1 : (a : R) * (x : R) ∈ maximalIdeal R * K` using `Ideal.mul_mem_mul a.2 x.2`. Rewrite `h1` using `[hK]`.

Simplify using `using h1`. Use `letI : Module (R ⧸ maximalIdeal R) K := hT.module`. Use `haveI : IsScalarTower R (R ⧸ maximalIdeal R) K := hT.isScalarTower`. Use `haveI : Module.Finite R K := Module.Finite.iff_fg.mpr (IsNoetherian.noetherian K)`. Use `haveI : Module.Finite (R ⧸ maximalIdeal R) K := Module.Finite.of_restrictScalars_finite R _ _`.

Use `letI : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _`. Use `haveI : IsArtinianRing (R ⧸ maximalIdeal R) := inferInstance`. Use `haveI : IsArtinian (R ⧸ maximalIdeal R) K := isArtinian_of_fg_of_artinian'`. Use `haveI : IsArtinian R K := isArtinian_of_surjective_algebraMap (R := R ⧸ maximalIdeal R) (Ideal.Quotient.mk_surjective (I := maximalIdeal R))`. Set `G : ℕ → Submodule R K` to `fun n => Submodule.comap (Submodule.subtype K) (F n)`.

Establish `hG : Antitone G` using `fun a b h => Submodule.comap_mono (hF h)`. Take `⟨_, ⟨N, rfl⟩, hmin⟩` from `(wellFounded_lt (α := Submodule R K)).has_min (Set.range G) ⟨_, 0, rfl⟩`. Use `⟨N, fun n => ?_⟩` and prove the remaining obligations. Establish `hle2 : G (max N n) ≤ G N` using `hG (le_max_left _ _)`. Establish `heq : G (max N n) = G N`.

Assume the negation of the conclusion as `hne`. Conclude with `hmin _ ⟨_, rfl⟩ (lt_of_le_of_ne hle2 hne)`. Introduce `x hx`. Establish `hxK : x ∈ K` using `hle N hx`. Establish `h2 : (⟨x, hxK⟩ : K) ∈ G N` using `hx`.

Rewrite `h2` using `[← heq]`. Conclude with `hF (le_max_right N n) h2`.
-/
private theorem chain_stab {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (K : Ideal R)
    (hK : maximalIdeal R * K = ⊥) (F : ℕ → Ideal R) (hF : Antitone F) (hle : ∀ n, F n ≤ K) :
    ∃ N, ∀ n, F N ≤ F n := by
  classical
  have hT : Module.IsTorsionBySet R K (maximalIdeal R : Set R) := by
    intro x a
    apply Subtype.ext
    have h1 : (a : R) * (x : R) ∈ maximalIdeal R * K := Ideal.mul_mem_mul a.2 x.2
    rw [hK] at h1
    simpa using h1
  letI : Module (R ⧸ maximalIdeal R) K := hT.module
  haveI : IsScalarTower R (R ⧸ maximalIdeal R) K := hT.isScalarTower
  haveI : Module.Finite R K := Module.Finite.iff_fg.mpr (IsNoetherian.noetherian K)
  haveI : Module.Finite (R ⧸ maximalIdeal R) K :=
    Module.Finite.of_restrictScalars_finite R _ _
  letI : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  haveI : IsArtinianRing (R ⧸ maximalIdeal R) := inferInstance
  haveI : IsArtinian (R ⧸ maximalIdeal R) K := isArtinian_of_fg_of_artinian'
  haveI : IsArtinian R K := isArtinian_of_surjective_algebraMap (R := R ⧸ maximalIdeal R)
    (Ideal.Quotient.mk_surjective (I := maximalIdeal R))
  let G : ℕ → Submodule R K := fun n => Submodule.comap (Submodule.subtype K) (F n)
  have hG : Antitone G := fun a b h => Submodule.comap_mono (hF h)
  obtain ⟨_, ⟨N, rfl⟩, hmin⟩ :=
    (wellFounded_lt (α := Submodule R K)).has_min (Set.range G) ⟨_, 0, rfl⟩
  refine ⟨N, fun n => ?_⟩
  have hle2 : G (max N n) ≤ G N := hG (le_max_left _ _)
  have heq : G (max N n) = G N := by
    by_contra hne
    exact hmin _ ⟨_, rfl⟩ (lt_of_le_of_ne hle2 hne)
  intro x hx
  have hxK : x ∈ K := hle N hx
  have h2 : (⟨x, hxK⟩ : K) ∈ G N := hx
  rw [← heq] at h2
  exact hF (le_max_right N n) h2

/- English proof (translation)
Take `⟨a, ha⟩` from `IsCO.res_surj (O := O) r`. Establish `h0 : (r - algebraMap O R a) * k = 0`. Establish `h1` using `Ideal.mul_mem_mul ha hk`. Rewrite `h1` using `[hJ]`. Conclude with `(Ideal.mem_bot).1 h1`.

Establish `h2 : r * k = a • k`. Rewrite using `[Algebra.smul_def]`. Take the linear combination `h0`. Rewrite using `[h2]`. Conclude with `S.smul_mem a hS`.
-/
private theorem mul_mem_of_mem_ideal_killed_by_maximalIdeal {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R]
    [IsCO O R] (J : Ideal R) (hJ : maximalIdeal R * J = ⊥) (S : Submodule O R) (r k : R)
    (hk : k ∈ J) (hS : k ∈ S) : r * k ∈ S := by
  obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) r
  have h0 : (r - algebraMap O R a) * k = 0 := by
    have h1 := Ideal.mul_mem_mul ha hk
    rw [hJ] at h1
    exact (Ideal.mem_bot).1 h1
  have h2 : r * k = a • k := by
    rw [Algebra.smul_def]
    linear_combination h0
  rw [h2]
  exact S.smul_mem a hS

/- English proof (translation)
Introduce `O _ _ _ _ X _ _ _ R _ _ _ R' _ _ _ p hp hker W hz Γ _ j x hxc hxp`. Establish `hmem : ∀ r : R, p r ∈ maximalIdeal R' ↔ r ∈ maximalIdeal R`. Introduce `r`. Rewrite using `[← res_eq_zero_iff O R', ← res_eq_zero_iff O R, res_map]`. Establish `hmapm : Ideal.map p (maximalIdeal R) = maximalIdeal R'`.

Use extensionality with `a`. Rewrite using `[Ideal.mem_map_iff_of_surjective p hp]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨r, hr, rfl⟩`. Conclude with `(hmem r).2 hr`.

Introduce `ha`. Take `⟨r, rfl⟩` from `hp a`. Conclude with `⟨r, (hmem r).1 ha, rfl⟩`. Establish `hlift : ∀ n (a : R'), a ∈ maximalIdeal R' ^ n → ∃ w, w ∈ maximalIdeal R ^ n ∧ p w = a`. Introduce `n a ha`.

Rewrite `ha` using `[← hmapm, ← Ideal.map_pow]`. Conclude with `(Ideal.mem_map_iff_of_surjective p hp).1 ha`. Take `⟨N0, hN0⟩` from `chain_stab (RingHom.ker p) hker (fun n => maximalIdeal R ^ n ⊓ RingHom.ker p) (fun a b h => inf_le_inf_right _ (Ideal.pow_le_pow_right h)) (fun n => inf_le_right)`. Establish `hinj : ∀ u v : R, u ∈ maximalIdeal R ^ N0 → v ∈ maximalIdeal R ^ N0 → p u = p v → u = v`. Introduce `u v hu hv huv`.

Establish `hk : u - v ∈ maximalIdeal R ^ N0 ⊓ RingHom.ker p` using `⟨Ideal.sub_mem _ hu hv, (RingHom.mem_ker).2 (by rw [map_sub, huv, sub_self])⟩`. Establish `hall : u - v ∈ ⨅ n, maximalIdeal R ^ n` using `Ideal.mem_iInf.2 fun n => (hN0 n hk).1`. Rewrite `hall` using `[Ideal.iInf_pow_eq_bot_of_isLocalRing (I := maximalIdeal R) (IsLocalRing.maximalIdeal.isMaximal R).ne_top]`. Conclude with `sub_eq_zero.1 ((Ideal.mem_bot).1 hall)`. Set `F : ℕ → Ideal R` to `fun n => { carrier := {k | k ∈ RingHom.ker p ∧ k ∈ W.part j ⊔ (maximalIdeal R ^ n).restrictScalars O} add_mem' := fun ha hb => ⟨Ideal.add_mem _ ha.1 hb.1, Submodule.add_mem _ ha.2 hb.2⟩ zero_mem' := ⟨Ideal.zero_mem _, Submodule.zero_mem _⟩ smul_mem' := fun r k hk => ⟨Ideal.mul_me …`.

Establish `hFanti : Antitone F`. Introduce `a b h k hk`. Establish `H : (maximalIdeal R ^ b).restrictScalars O ≤ (maximalIdeal R ^ a).restrictScalars O` using `fun z hz => Ideal.pow_le_pow_right h hz`. Conclude with `⟨hk.1, SetLike.le_def.1 (sup_le_sup_left H (W.part j)) hk.2⟩`. Take `⟨N1, hN1⟩` from `chain_stab (RingHom.ker p) hker F hFanti (fun n k hk => hk.1)`.

Establish `hclosed : ∀ k, k ∈ RingHom.ker p → k ∈ W.part j ⊔ (maximalIdeal R ^ N1).restrictScalars O → k ∈ W.part j`. Introduce `k hk1 hk2`. Establish `hkF : k ∈ F N1` using `⟨hk1, hk2⟩`. Apply `part_closed O X R W hz j k` to reduce the goal to its premises. Introduce `N`.

Take `⟨y, hy, z, hz2, hyz⟩` from `Submodule.mem_sup.1 (hN1 N hkF).2`. Use `⟨y, hy, ?_⟩` and prove the remaining obligations. Rewrite using `[← hyz, add_sub_cancel_left]`. Conclude with `hz2`. Establish `hL : ∀ a, a ∈ (W.part j).map p.toLinearMap → a ∈ maximalIdeal R' ^ (max N0 N1) → ∃ w, w ∈ W.part j ∧ w ∈ maximalIdeal R ^ (max N0 N1) ∧ p w = a`.

Introduce `a ha haM`. Take `⟨e, he, rfl⟩` from `Submodule.mem_map.1 ha`. Take `⟨w, hw, hpw⟩` from `hlift _ _ haM`. Establish `hk1 : e - w ∈ RingHom.ker p`. Rewrite using `[RingHom.mem_ker, map_sub, hpw, AlgHom.toLinearMap_apply, sub_self]`.

Establish `hk2 : e - w ∈ W.part j ⊔ (maximalIdeal R ^ N1).restrictScalars O`. Rewrite using `[sub_eq_add_neg]`. Conclude with `Submodule.add_mem_sup he (Submodule.neg_mem _ (Ideal.pow_le_pow_right (le_max_right _ _) hw))`. Establish `hk` using `hclosed _ hk1 hk2`. Use `⟨w, ?_, hw, hpw⟩` and prove the remaining obligations.

Establish `h3` using `Submodule.sub_mem _ he hk`. Rewrite `h3` using `[sub_sub_cancel]`. Then use the resulting hypothesis. Set `base : (R' ⧸ maximalIdeal R' ^ (max N0 N1)) → R` to `fun c => if h : ∃ e, e ∈ W.part j ∧ Ideal.Quotient.mk (maximalIdeal R' ^ (max N0 N1)) (p e) = c then h.choose else 0`. Establish `hbase : ∀ g, base (Ideal.Quotient.mk _ (x g)) ∈ W.part j ∧ x g - p (base (Ideal.Quotient.mk _ (x g))) ∈ maximalIdeal R' ^ (max N0 N1)`. Introduce `g`.

Take `⟨e, he, hpe⟩` from `Submodule.mem_map.1 (hxp g)`. Establish `h : ∃ e, e ∈ W.part j ∧ Ideal.Quotient.mk (maximalIdeal R' ^ (max N0 N1)) (p e) = Ideal.Quotient.mk _ (x g)` using `⟨e, he, by rw [← hpe]; rfl⟩`. Simplify using `only [base]`. Rewrite using `[dif_pos h]`. Use `⟨h.choose_spec.1, ?_⟩` and prove the remaining obligations.

Rewrite using `[← Ideal.Quotient.eq]`. Conclude with `h.choose_spec.2.symm`. Establish `hw : ∀ g, ∃ w, w ∈ W.part j ∧ w ∈ maximalIdeal R ^ (max N0 N1) ∧ p w = x g - p (base (Ideal.Quotient.mk _ (x g)))`. Introduce `g`. Apply `hL` to reduce the goal to its premises.

Conclude with `Submodule.sub_mem _ (hxp g) (Submodule.mem_map_of_mem (hbase g).1)`. Conclude with `(hbase g).2`. Use `choose w hwP hwM hwp using hw`. Use `⟨fun g => base (Ideal.Quotient.mk _ (x g)) + w g, ?_, fun g => Submodule.add_mem _ (hbase g).1 (hwP g), fun g => ?_⟩` and prove the remaining obligations. Unfold `AdicCont at hxc ⊢`.

Introduce `N`. Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `g0`. Establish `hx0` using `(IsLocallyConstant.iff_eventually_eq _).1 (hxc (max N (max N0 N1))) g0`. Use `filter_upwards [hx0] with g hg`.

Establish `hd : x g - x g0 ∈ maximalIdeal R' ^ max N (max N0 N1)` using `Ideal.Quotient.eq.1 hg`. Establish `hcls : Ideal.Quotient.mk (maximalIdeal R' ^ (max N0 N1)) (x g) = Ideal.Quotient.mk _ (x g0)` using `Ideal.Quotient.eq.2 (Ideal.pow_le_pow_right (le_max_right _ _) hd)`. Take `⟨v, hv, hpv⟩` from `hlift _ _ hd`. Establish `hM0 : maximalIdeal R ^ (max N0 N1) ≤ maximalIdeal R ^ N0` using `Ideal.pow_le_pow_right (le_max_left _ _)`. Establish `heq : w g - w g0 = v`.

Apply `hinj` to reduce the goal to its premises. Conclude with `Ideal.sub_mem _ (hM0 (hwM g)) (hM0 (hwM g0))`. Conclude with `Ideal.pow_le_pow_right (le_trans (le_max_left _ _) (le_max_right _ _)) hv`. Rewrite using `[map_sub, hwp, hwp, hpv, hcls]`. Expand and normalize the polynomial expressions, which then agree.

Apply `Ideal.Quotient.eq.2` to reduce the goal to its premises. Use `show base (Ideal.Quotient.mk _ (x g)) + w g - (base (Ideal.Quotient.mk _ (x g0)) + w g0) ∈ _`. Rewrite using `[hcls]`. Establish `h4 : base (Ideal.Quotient.mk _ (x g0)) + w g - (base (Ideal.Quotient.mk _ (x g0)) + w g0) = v`. Rewrite using `[← heq]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h4]`. Conclude with `Ideal.pow_le_pow_right (le_max_left _ _) hv`. Use `show p (base _ + w g) = x g`. Rewrite using `[map_add, hwp]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.V.Alg.cont_section :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (p : R →ₐ[O] R'), Function.Surjective p → maximalIdeal R * RingHom.ker p = ⊥ → ∀ (W : WPres O X R), (∀ s, W.z s ∈ maximalIdeal R) →
      ∀ (Γ : Type) [TopologicalSpace Γ] (j : X) (x : Γ → R'), AdicCont (maximalIdeal R') x → (∀ g, x g ∈ (W.part j).map p.toLinearMap) →
      ∃ y : Γ → R, AdicCont (maximalIdeal R) y ∧ (∀ g, y g ∈ W.part j) ∧ ∀ g, p (y g) = x g := by
  intro O _ _ _ _ X _ _ _ R _ _ _ R' _ _ _ p hp hker W hz Γ _ j x hxc hxp
  classical
  have hmem : ∀ r : R, p r ∈ maximalIdeal R' ↔ r ∈ maximalIdeal R := by
    intro r
    rw [← res_eq_zero_iff O R', ← res_eq_zero_iff O R, res_map]
  have hmapm : Ideal.map p (maximalIdeal R) = maximalIdeal R' := by
    ext a
    rw [Ideal.mem_map_iff_of_surjective p hp]
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact (hmem r).2 hr
    · intro ha
      obtain ⟨r, rfl⟩ := hp a
      exact ⟨r, (hmem r).1 ha, rfl⟩
  have hlift : ∀ n (a : R'), a ∈ maximalIdeal R' ^ n → ∃ w, w ∈ maximalIdeal R ^ n ∧ p w = a := by
    intro n a ha
    rw [← hmapm, ← Ideal.map_pow] at ha
    exact (Ideal.mem_map_iff_of_surjective p hp).1 ha
  obtain ⟨N0, hN0⟩ := chain_stab (RingHom.ker p) hker (fun n => maximalIdeal R ^ n ⊓ RingHom.ker p)
    (fun a b h => inf_le_inf_right _ (Ideal.pow_le_pow_right h)) (fun n => inf_le_right)
  have hinj : ∀ u v : R, u ∈ maximalIdeal R ^ N0 → v ∈ maximalIdeal R ^ N0 → p u = p v → u = v := by
    intro u v hu hv huv
    have hk : u - v ∈ maximalIdeal R ^ N0 ⊓ RingHom.ker p :=
      ⟨Ideal.sub_mem _ hu hv, (RingHom.mem_ker).2 (by rw [map_sub, huv, sub_self])⟩
    have hall : u - v ∈ ⨅ n, maximalIdeal R ^ n := Ideal.mem_iInf.2 fun n => (hN0 n hk).1
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing (I := maximalIdeal R)
      (IsLocalRing.maximalIdeal.isMaximal R).ne_top] at hall
    exact sub_eq_zero.1 ((Ideal.mem_bot).1 hall)
  let F : ℕ → Ideal R := fun n =>
    { carrier := {k | k ∈ RingHom.ker p ∧ k ∈ W.part j ⊔ (maximalIdeal R ^ n).restrictScalars O}
      add_mem' := fun ha hb => ⟨Ideal.add_mem _ ha.1 hb.1, Submodule.add_mem _ ha.2 hb.2⟩
      zero_mem' := ⟨Ideal.zero_mem _, Submodule.zero_mem _⟩
      smul_mem' := fun r k hk =>
        ⟨Ideal.mul_mem_left _ r hk.1, mul_mem_of_mem_ideal_killed_by_maximalIdeal (O := O) _ hker _ r k hk.1 hk.2⟩ }
  have hFanti : Antitone F := by
    intro a b h k hk
    have H : (maximalIdeal R ^ b).restrictScalars O ≤ (maximalIdeal R ^ a).restrictScalars O :=
      fun z hz => Ideal.pow_le_pow_right h hz
    exact ⟨hk.1, SetLike.le_def.1 (sup_le_sup_left H (W.part j)) hk.2⟩
  obtain ⟨N1, hN1⟩ := chain_stab (RingHom.ker p) hker F hFanti (fun n k hk => hk.1)
  have hclosed : ∀ k, k ∈ RingHom.ker p →
      k ∈ W.part j ⊔ (maximalIdeal R ^ N1).restrictScalars O → k ∈ W.part j := by
    intro k hk1 hk2
    have hkF : k ∈ F N1 := ⟨hk1, hk2⟩
    apply part_closed O X R W hz j k
    intro N
    obtain ⟨y, hy, z, hz2, hyz⟩ := Submodule.mem_sup.1 (hN1 N hkF).2
    refine ⟨y, hy, ?_⟩
    rw [← hyz, add_sub_cancel_left]
    exact hz2
  have hL : ∀ a, a ∈ (W.part j).map p.toLinearMap → a ∈ maximalIdeal R' ^ (max N0 N1) →
      ∃ w, w ∈ W.part j ∧ w ∈ maximalIdeal R ^ (max N0 N1) ∧ p w = a := by
    intro a ha haM
    obtain ⟨e, he, rfl⟩ := Submodule.mem_map.1 ha
    obtain ⟨w, hw, hpw⟩ := hlift _ _ haM
    have hk1 : e - w ∈ RingHom.ker p := by
      rw [RingHom.mem_ker, map_sub, hpw, AlgHom.toLinearMap_apply, sub_self]
    have hk2 : e - w ∈ W.part j ⊔ (maximalIdeal R ^ N1).restrictScalars O := by
      rw [sub_eq_add_neg]
      exact Submodule.add_mem_sup he
        (Submodule.neg_mem _ (Ideal.pow_le_pow_right (le_max_right _ _) hw))
    have hk := hclosed _ hk1 hk2
    refine ⟨w, ?_, hw, hpw⟩
    have h3 := Submodule.sub_mem _ he hk
    rwa [sub_sub_cancel] at h3
  let base : (R' ⧸ maximalIdeal R' ^ (max N0 N1)) → R := fun c =>
    if h : ∃ e, e ∈ W.part j ∧ Ideal.Quotient.mk (maximalIdeal R' ^ (max N0 N1)) (p e) = c
    then h.choose else 0
  have hbase : ∀ g, base (Ideal.Quotient.mk _ (x g)) ∈ W.part j ∧
      x g - p (base (Ideal.Quotient.mk _ (x g))) ∈ maximalIdeal R' ^ (max N0 N1) := by
    intro g
    obtain ⟨e, he, hpe⟩ := Submodule.mem_map.1 (hxp g)
    have h : ∃ e, e ∈ W.part j ∧ Ideal.Quotient.mk (maximalIdeal R' ^ (max N0 N1)) (p e) =
        Ideal.Quotient.mk _ (x g) := ⟨e, he, by rw [← hpe]; rfl⟩
    simp only [base]
    rw [dif_pos h]
    refine ⟨h.choose_spec.1, ?_⟩
    rw [← Ideal.Quotient.eq]
    exact h.choose_spec.2.symm
  have hw : ∀ g, ∃ w, w ∈ W.part j ∧ w ∈ maximalIdeal R ^ (max N0 N1) ∧
      p w = x g - p (base (Ideal.Quotient.mk _ (x g))) := by
    intro g
    apply hL
    · exact Submodule.sub_mem _ (hxp g) (Submodule.mem_map_of_mem (hbase g).1)
    · exact (hbase g).2
  choose w hwP hwM hwp using hw
  refine ⟨fun g => base (Ideal.Quotient.mk _ (x g)) + w g, ?_,
    fun g => Submodule.add_mem _ (hbase g).1 (hwP g), fun g => ?_⟩
  · unfold AdicCont at hxc ⊢
    intro N
    rw [IsLocallyConstant.iff_eventually_eq]
    intro g0
    have hx0 := (IsLocallyConstant.iff_eventually_eq _).1 (hxc (max N (max N0 N1))) g0
    filter_upwards [hx0] with g hg
    have hd : x g - x g0 ∈ maximalIdeal R' ^ max N (max N0 N1) := Ideal.Quotient.eq.1 hg
    have hcls : Ideal.Quotient.mk (maximalIdeal R' ^ (max N0 N1)) (x g) =
        Ideal.Quotient.mk _ (x g0) :=
      Ideal.Quotient.eq.2 (Ideal.pow_le_pow_right (le_max_right _ _) hd)
    obtain ⟨v, hv, hpv⟩ := hlift _ _ hd
    have hM0 : maximalIdeal R ^ (max N0 N1) ≤ maximalIdeal R ^ N0 :=
      Ideal.pow_le_pow_right (le_max_left _ _)
    have heq : w g - w g0 = v := by
      apply hinj
      · exact Ideal.sub_mem _ (hM0 (hwM g)) (hM0 (hwM g0))
      · exact Ideal.pow_le_pow_right (le_trans (le_max_left _ _) (le_max_right _ _)) hv
      · rw [map_sub, hwp, hwp, hpv, hcls]
        ring
    apply Ideal.Quotient.eq.2
    show base (Ideal.Quotient.mk _ (x g)) + w g - (base (Ideal.Quotient.mk _ (x g0)) + w g0) ∈ _
    rw [hcls]
    have h4 : base (Ideal.Quotient.mk _ (x g0)) + w g -
        (base (Ideal.Quotient.mk _ (x g0)) + w g0) = v := by
      rw [← heq]
      ring
    rw [h4]
    exact Ideal.pow_le_pow_right (le_max_left _ _) hv
  · show p (base _ + w g) = x g
    rw [map_add, hwp]
    ring
