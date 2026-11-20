import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.BdMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.IsOpenKc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.LevelTorusLeTorus
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.HodgeTateFromSandwich

noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

/- English proof (translation)
Establish `hq : ∀ u, P u → ∃ t, t ∈ C ∧ P t ∧ (QuotientGroup.mk t : G ⧸ K) = QuotientGroup.mk u`. Introduce `u hu`. Take `⟨t, ht, hPt, hut⟩` from `hC u hu`. Use `⟨t, ht, hPt, ?_⟩` and prove the remaining obligations. Rewrite using `[QuotientGroup.eq, mul_comm, ← div_eq_mul_inv]`.

Conclude with `hut`. Set `f : G ⧸ K → G` to `fun q => if h : ∃ t, t ∈ C ∧ P t ∧ (QuotientGroup.mk t : G ⧸ K) = q then h.choose else 1`. Establish `hf : ∀ t, t ∈ C → P t → f (QuotientGroup.mk t) ∈ C ∧ P (f (QuotientGroup.mk t)) ∧ (QuotientGroup.mk (f (QuotientGroup.mk t)) : G ⧸ K) = QuotientGroup.mk t`. Introduce `t ht hPt`. Establish `h : ∃ s, s ∈ C ∧ P s ∧ (QuotientGroup.mk s : G ⧸ K) = QuotientGroup.mk t` using `⟨t, ht, hPt, rfl⟩`.

Simplify using `only [f, dif_pos h]`. Conclude with `h.choose_spec`. Use `⟨(C.filter P).image (fun t : G => f (QuotientGroup.mk t)), ?_, ?_⟩` and prove the remaining obligations. Introduce `e he`. Rewrite `he` using `[Finset.mem_image]`.

Take `⟨t, ht, rfl⟩` from `he`. Rewrite `ht` using `[Finset.mem_filter]`. Conclude with `⟨(hf t ht.1 ht.2).1, (hf t ht.1 ht.2).2.1⟩`. Introduce `u hu`. Take `⟨t0, ht0, hPt0, ht0u⟩` from `hq u hu`.

Use `⟨f (QuotientGroup.mk t0), ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.mem_image]`. Conclude with `⟨t0, Finset.mem_filter.mpr ⟨ht0, hPt0⟩, rfl⟩`. Establish `h3` using `(hf t0 ht0 hPt0).2.2.trans ht0u`. Rewrite `h3` using `[QuotientGroup.eq]`.

Rewrite using `[div_eq_mul_inv, mul_comm]`. Conclude with `h3`. Introduce and unpack `e ⟨he, heu⟩`. Rewrite `he` using `[Finset.mem_image]`. Take `⟨t, ht, rfl⟩` from `he`.

Rewrite `ht` using `[Finset.mem_filter]`. Establish `h3` using `(hf t ht.1 ht.2).2.2`. Establish `htu : (QuotientGroup.mk t : G ⧸ K) = QuotientGroup.mk t0`. Rewrite using `[← h3, ht0u, QuotientGroup.eq, mul_comm, ← div_eq_mul_inv]`. Conclude with `heu`.

Rewrite using `[htu]`.
-/
private theorem exists_finite_residue_reps_mod_natCast {G : Type} [CommGroup G] (K : Subgroup G) (P : G → Prop) (C : Finset G)
    (hC : ∀ u, P u → ∃ t ∈ C, P t ∧ u / t ∈ K) :
    ∃ R : Finset G, (∀ e ∈ R, e ∈ C ∧ P e) ∧ ∀ u, P u → ∃! e, e ∈ R ∧ u / e ∈ K := by
  classical
  have hq : ∀ u, P u → ∃ t, t ∈ C ∧ P t ∧ (QuotientGroup.mk t : G ⧸ K) = QuotientGroup.mk u := by
    intro u hu
    obtain ⟨t, ht, hPt, hut⟩ := hC u hu
    refine ⟨t, ht, hPt, ?_⟩
    rw [QuotientGroup.eq, mul_comm, ← div_eq_mul_inv]
    exact hut
  let f : G ⧸ K → G := fun q => if h : ∃ t, t ∈ C ∧ P t ∧ (QuotientGroup.mk t : G ⧸ K) = q then h.choose else 1
  have hf : ∀ t, t ∈ C → P t → f (QuotientGroup.mk t) ∈ C ∧ P (f (QuotientGroup.mk t)) ∧
      (QuotientGroup.mk (f (QuotientGroup.mk t)) : G ⧸ K) = QuotientGroup.mk t := by
    intro t ht hPt
    have h : ∃ s, s ∈ C ∧ P s ∧ (QuotientGroup.mk s : G ⧸ K) = QuotientGroup.mk t := ⟨t, ht, hPt, rfl⟩
    simp only [f, dif_pos h]
    exact h.choose_spec
  refine ⟨(C.filter P).image (fun t : G => f (QuotientGroup.mk t)), ?_, ?_⟩
  · intro e he
    rw [Finset.mem_image] at he
    obtain ⟨t, ht, rfl⟩ := he
    rw [Finset.mem_filter] at ht
    exact ⟨(hf t ht.1 ht.2).1, (hf t ht.1 ht.2).2.1⟩
  · intro u hu
    obtain ⟨t0, ht0, hPt0, ht0u⟩ := hq u hu
    refine ⟨f (QuotientGroup.mk t0), ⟨?_, ?_⟩, ?_⟩
    · rw [Finset.mem_image]
      exact ⟨t0, Finset.mem_filter.mpr ⟨ht0, hPt0⟩, rfl⟩
    · have h3 := (hf t0 ht0 hPt0).2.2.trans ht0u
      rw [QuotientGroup.eq] at h3
      rw [div_eq_mul_inv, mul_comm]
      exact h3
    · rintro e ⟨he, heu⟩
      rw [Finset.mem_image] at he
      obtain ⟨t, ht, rfl⟩ := he
      rw [Finset.mem_filter] at ht
      have h3 := (hf t ht.1 ht.2).2.2
      have htu : (QuotientGroup.mk t : G ⧸ K) = QuotientGroup.mk t0 := by
        rw [← h3, ht0u, QuotientGroup.eq, mul_comm, ← div_eq_mul_inv]
        exact heu
      rw [htu]

/- English proof (translation)
Introduce `k _ _ _ _ V`. Set `φ : kˣ →* GL (Fin 1) k` to `(diagT k (Fin 1)).comp { toFun := fun u _ => u, map_one' := rfl, map_mul' := fun _ _ => rfl }`. Establish `hφc : Subgroup.comap φ (Kc k 1 (V.c + 1)) = Uc k (V.c + 1)`. Use extensionality with `u`. Rewrite using `[Subgroup.mem_comap]`.

Conclude with `(dg_mem_Kc (k := k) (n := 1) (c := V.c + 1) (s := fun _ => u)).trans (by simp)`. Establish `hidx : (Uc k (V.c + 1)).relIndex (Uo k) ≠ 0`. Rewrite using `[← hφc, Subgroup.relIndex_comap]`. Apply `GlAx.Kc_index` to reduce the goal to its premises. Rewrite using `[Subgroup.map_le_iff_le_comap]`.

Introduce `u hu`. Rewrite using `[Subgroup.mem_comap]`. Conclude with `dg_mem_KO (k := k) (n := 1) (s := fun _ => u) (fun _ => hu)`. Establish `hH : V.H.relIndex (Uo k) ≠ 0` using `ne_zero_of_dvd_ne_zero hidx (Subgroup.relIndex_dvd_of_le_left _ V.le)`. Establish `hH2 : V.H2 ≤ Uo k`.

Introduce `u hu`. Establish `h2 : u ^ 2 ∈ Uo k` using `V.H_le hu`. Establish `h2' : valuation k (u : k) * valuation k (u : k) = 1`. Establish `: valuation k ((u ^ 2 : kˣ) : k) = 1` using `h2`. Rewrite `this` using `[Units.val_pow_eq_pow_val, map_pow, sq]`.

Conclude with `this`. Use `show valuation k (u : k) = 1`. Break down `lt_trichotomy (valuation k (u : k)) 1 with h | h | h` into its components or cases. Conclude with `absurd h2' (ne_of_lt (mul_lt_one_of_lt_of_le h h.le))`. Conclude with `h`.

Conclude with `absurd h2' (ne_of_gt (one_lt_mul_of_lt_of_le h h.le))`. Establish `hHH2 : V.H ≤ V.H2`. Introduce `u hu`. Use `show u ^ 2 ∈ V.H`. Conclude with `V.H.pow_mem hu 2`.

Take `⟨T, hTU, hT⟩ : ∃ T : Finset kˣ, (∀ t ∈ T, t ∈ Uo k) ∧ ∀ u ∈ Uo k, ∃ t ∈ T, u / t ∈ V.H` from `by classical haveI : (V.H.subgroupOf (Uo k)).FiniteIndex := ⟨hH⟩ haveI := Fintype.ofFinite (Uo k ⧸ V.H.subgroupOf (Uo k))`. Use `⟨Finset.univ.image (fun q : Uo k ⧸ V.H.subgroupOf (Uo k) => ((Quotient.out q : Uo k) : kˣ)), ?_, ?_⟩` and prove the remaining obligations. Introduce `t ht`. Take `⟨q, -, rfl⟩` from `Finset.mem_image.mp ht`. Conclude with `(Quotient.out q).2`.

Introduce `u hu`. Use `⟨((Quotient.out (QuotientGroup.mk ⟨u, hu⟩ : Uo k ⧸ V.H.subgroupOf (Uo k)) : Uo k) : kˣ), Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩` and prove the remaining obligations. Establish `h` using `QuotientGroup.out_eq' (QuotientGroup.mk ⟨u, hu⟩ : Uo k ⧸ V.H.subgroupOf (Uo k))`. Rewrite `h` using `[QuotientGroup.eq, Subgroup.mem_subgroupOf]`. Rewrite using `[div_eq_mul_inv, mul_comm]`.

Simplify using `using h`. Use `⟨hH, hH2, hHH2, ?_, ?_, ?_⟩` and prove the remaining obligations. Take `⟨R, hR1, hR2⟩` from `exists_finite_residue_reps_mod_natCast V.H (· ∈ V.H2) T (by`. Introduce `u hu`. Take `⟨t, ht, hut⟩` from `hT u (hH2 hu)`.

Use `⟨t, ht, ?_, hut⟩` and prove the remaining obligations. Rewrite using `[← div_div_cancel u t]`. Conclude with `V.H2.div_mem hu (hHH2 hut))`. Conclude with `⟨R, fun e he => (hR1 e he).2, hR2⟩`. Set `S : Subgroup kˣ` to `V.H ⊔ (powMonoidHom 2 : kˣ →* kˣ).range`.

Establish `hS : ∀ u y : kˣ, u / y ∈ S ↔ ∃ s, u / (y * s ^ 2) ∈ V.H`. Introduce `u y`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨a, ha, b, ⟨s, rfl⟩, hab⟩` from `Subgroup.mem_sup.mp h`.

Use `⟨s, ?_⟩` and prove the remaining obligations. Rewrite using `[← div_div, ← hab]`. Simplify using `using ha`. Introduce and unpack `⟨s, hs⟩`. Use `Subgroup.mem_sup.mpr ⟨_, hs, s ^ 2, ⟨s, rfl⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[← div_div, div_mul_cancel]`. Establish `hcov : ∀ u : kˣ, ∃ t ∈ T ∪ T.image (fun t => unif k * t), True ∧ u / t ∈ S`. Introduce `u`. Use `set m := ord k u`. Use `set w := u / unif k ^ m`.

Establish `hw : w ∈ Uo k` using `GlAx.val_div_ord u`. Take `⟨t0, ht0, hwt⟩` from `hT w hw`. Use `set s := unif k ^ (m / 2)`. Establish `hu_eq : u = w * unif k ^ (m % 2) * s ^ 2`. Establish `: unif k ^ m = unif k ^ (m % 2) * s ^ 2`.

Rewrite using `[← zpow_natCast s 2, ← _root_.zpow_mul, ← _root_.zpow_add]`. Use `congr 1`. Use `push_cast`. Use linear arithmetic over natural numbers and integers. Rewrite using `[mul_assoc, ← this, div_mul_cancel]`.

Break down `Int.emod_two_eq_zero_or_one m with hr | hr` into its components or cases. Use `⟨t0, Finset.mem_union_left _ ht0, trivial, (hS u t0).mpr ⟨s, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[hu_eq, hr, zpow_zero, mul_one, mul_div_mul_right_eq_div]`. Conclude with `hwt`. Use `⟨unif k * t0, Finset.mem_union_right _ (Finset.mem_image.mpr ⟨t0, ht0, rfl⟩), trivial, (hS u _).mpr ⟨s, ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[hu_eq, hr, zpow_one, mul_div_mul_right_eq_div, mul_comm (unif k) t0, mul_div_mul_right_eq_div]`. Conclude with `hwt`. Take `⟨R, hR1, hR2⟩` from `exists_finite_residue_reps_mod_natCast S (fun _ => True) (T ∪ T.image (fun t => unif k * t)) (fun u _ => hcov u)`. Use `⟨R, ?_, ?_⟩` and prove the remaining obligations. Introduce `y hy`.

Establish `hyC` using `(hR1 y hy).1`. Establish `hu1 : valuation k ((unif k : kˣ) : k) ≤ 1`. Rewrite using `[GlAx.unif_spec]`. Conclude with `ValuativeRel.uniformizer_lt_one.le`. Break down `Finset.mem_union.mp hyC with hyT | hyT` into its components or cases.

Establish `: valuation k (y : k) = 1` using `hTU y hyT`. Rewrite using `[this]`. Conclude with `⟨hu1, le_rfl⟩`. Take `⟨t, ht, rfl⟩` from `Finset.mem_image.mp hyT`. Establish `: valuation k (t : k) = 1` using `hTU t ht`.

Rewrite using `[Units.val_mul, map_mul, this, mul_one]`. Conclude with `⟨le_rfl, hu1⟩`. Introduce `u`. Take `⟨e, ⟨he, heu⟩, huniq⟩` from `hR2 u trivial`. Use `⟨e, ⟨he, (hS u e).mp heu⟩, ?_⟩` and prove the remaining obligations.

Introduce and unpack `y ⟨hy, hyu⟩`. Conclude with `huniq y ⟨hy, (hS u y).mpr hyu⟩`. Introduce `n`. Establish `hopen : IsOpen (V.J n : Set (GL (Fin n) k))` using `Subgroup.isOpen_mono (kc_le V) (isOpen_Kc _)`. Establish `hcpt : IsCompact (V.J n : Set (GL (Fin n) k))` using `GlobalTheory.SplitFlip.isCompact_KO.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hopen) V.J_le_KO`.

Use `⟨?_, hopen, hcpt, V.J_le_KO⟩` and prove the remaining obligations. Introduce `x`. Use `show (MulAction.orbit (V.J n) (x : GL (Fin n) k ⧸ V.J n)).Finite`. Use `haveI := QuotientGroup.discreteTopology hopen`. Use `((hcpt.image (f := fun g => ((g * x : GL (Fin n) k) : GL (Fin n) k ⧸ V.J n)) (QuotientGroup.continuous_mk.comp (continuous_mul_right x))).finite_of_discrete).subset ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨j, rfl⟩`. Conclude with `⟨j, j.2, rfl⟩`.
-/
theorem UpperTheory.V.Z.Sym.Sig.finFacts : UpperTheory.V.Z.Sym.Sig.FinFacts := by
  intro k _ _ _ _ V
  let φ : kˣ →* GL (Fin 1) k := (diagT k (Fin 1)).comp
    { toFun := fun u _ => u, map_one' := rfl, map_mul' := fun _ _ => rfl }
  have hφc : Subgroup.comap φ (Kc k 1 (V.c + 1)) = Uc k (V.c + 1) := by
    ext u
    rw [Subgroup.mem_comap]
    exact (dg_mem_Kc (k := k) (n := 1) (c := V.c + 1) (s := fun _ => u)).trans (by simp)
  have hidx : (Uc k (V.c + 1)).relIndex (Uo k) ≠ 0 := by
    rw [← hφc, Subgroup.relIndex_comap]
    apply GlAx.Kc_index
    rw [Subgroup.map_le_iff_le_comap]
    intro u hu
    rw [Subgroup.mem_comap]
    exact dg_mem_KO (k := k) (n := 1) (s := fun _ => u) (fun _ => hu)
  have hH : V.H.relIndex (Uo k) ≠ 0 :=
    ne_zero_of_dvd_ne_zero hidx (Subgroup.relIndex_dvd_of_le_left _ V.le)
  have hH2 : V.H2 ≤ Uo k := by
    intro u hu
    have h2 : u ^ 2 ∈ Uo k := V.H_le hu
    have h2' : valuation k (u : k) * valuation k (u : k) = 1 := by
      have : valuation k ((u ^ 2 : kˣ) : k) = 1 := h2
      rw [Units.val_pow_eq_pow_val, map_pow, sq] at this
      exact this
    show valuation k (u : k) = 1
    rcases lt_trichotomy (valuation k (u : k)) 1 with h | h | h
    · exact absurd h2' (ne_of_lt (mul_lt_one_of_lt_of_le h h.le))
    · exact h
    · exact absurd h2' (ne_of_gt (one_lt_mul_of_lt_of_le h h.le))
  have hHH2 : V.H ≤ V.H2 := by
    intro u hu
    show u ^ 2 ∈ V.H
    exact V.H.pow_mem hu 2
  obtain ⟨T, hTU, hT⟩ : ∃ T : Finset kˣ, (∀ t ∈ T, t ∈ Uo k) ∧ ∀ u ∈ Uo k, ∃ t ∈ T, u / t ∈ V.H := by
    classical
    haveI : (V.H.subgroupOf (Uo k)).FiniteIndex := ⟨hH⟩
    haveI := Fintype.ofFinite (Uo k ⧸ V.H.subgroupOf (Uo k))
    refine ⟨Finset.univ.image (fun q : Uo k ⧸ V.H.subgroupOf (Uo k) => ((Quotient.out q : Uo k) : kˣ)), ?_, ?_⟩
    · intro t ht
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp ht
      exact (Quotient.out q).2
    · intro u hu
      refine ⟨((Quotient.out (QuotientGroup.mk ⟨u, hu⟩ : Uo k ⧸ V.H.subgroupOf (Uo k)) : Uo k) : kˣ),
        Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩
      have h := QuotientGroup.out_eq' (QuotientGroup.mk ⟨u, hu⟩ : Uo k ⧸ V.H.subgroupOf (Uo k))
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
      rw [div_eq_mul_inv, mul_comm]
      simpa using h
  refine ⟨hH, hH2, hHH2, ?_, ?_, ?_⟩
  · obtain ⟨R, hR1, hR2⟩ := exists_finite_residue_reps_mod_natCast V.H (· ∈ V.H2) T (by
      intro u hu
      obtain ⟨t, ht, hut⟩ := hT u (hH2 hu)
      refine ⟨t, ht, ?_, hut⟩
      rw [← div_div_cancel u t]
      exact V.H2.div_mem hu (hHH2 hut))
    exact ⟨R, fun e he => (hR1 e he).2, hR2⟩
  · classical
    let S : Subgroup kˣ := V.H ⊔ (powMonoidHom 2 : kˣ →* kˣ).range
    have hS : ∀ u y : kˣ, u / y ∈ S ↔ ∃ s, u / (y * s ^ 2) ∈ V.H := by
      intro u y
      constructor
      · intro h
        obtain ⟨a, ha, b, ⟨s, rfl⟩, hab⟩ := Subgroup.mem_sup.mp h
        refine ⟨s, ?_⟩
        rw [← div_div, ← hab]
        simpa using ha
      · rintro ⟨s, hs⟩
        refine Subgroup.mem_sup.mpr ⟨_, hs, s ^ 2, ⟨s, rfl⟩, ?_⟩
        rw [← div_div, div_mul_cancel]
    have hcov : ∀ u : kˣ, ∃ t ∈ T ∪ T.image (fun t => unif k * t), True ∧ u / t ∈ S := by
      intro u
      set m := ord k u
      set w := u / unif k ^ m
      have hw : w ∈ Uo k := GlAx.val_div_ord u
      obtain ⟨t0, ht0, hwt⟩ := hT w hw
      set s := unif k ^ (m / 2)
      have hu_eq : u = w * unif k ^ (m % 2) * s ^ 2 := by
        have : unif k ^ m = unif k ^ (m % 2) * s ^ 2 := by
          rw [← zpow_natCast s 2, ← _root_.zpow_mul, ← _root_.zpow_add]
          congr 1
          push_cast
          omega
        rw [mul_assoc, ← this, div_mul_cancel]
      rcases Int.emod_two_eq_zero_or_one m with hr | hr
      · refine ⟨t0, Finset.mem_union_left _ ht0, trivial, (hS u t0).mpr ⟨s, ?_⟩⟩
        rw [hu_eq, hr, zpow_zero, mul_one, mul_div_mul_right_eq_div]
        exact hwt
      · refine ⟨unif k * t0, Finset.mem_union_right _ (Finset.mem_image.mpr ⟨t0, ht0, rfl⟩), trivial,
          (hS u _).mpr ⟨s, ?_⟩⟩
        rw [hu_eq, hr, zpow_one, mul_div_mul_right_eq_div, mul_comm (unif k) t0, mul_div_mul_right_eq_div]
        exact hwt
    obtain ⟨R, hR1, hR2⟩ := exists_finite_residue_reps_mod_natCast S (fun _ => True) (T ∪ T.image (fun t => unif k * t))
      (fun u _ => hcov u)
    refine ⟨R, ?_, ?_⟩
    · intro y hy
      have hyC := (hR1 y hy).1
      have hu1 : valuation k ((unif k : kˣ) : k) ≤ 1 := by
        rw [GlAx.unif_spec]
        exact ValuativeRel.uniformizer_lt_one.le
      rcases Finset.mem_union.mp hyC with hyT | hyT
      · have : valuation k (y : k) = 1 := hTU y hyT
        rw [this]
        exact ⟨hu1, le_rfl⟩
      · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hyT
        have : valuation k (t : k) = 1 := hTU t ht
        rw [Units.val_mul, map_mul, this, mul_one]
        exact ⟨le_rfl, hu1⟩
    · intro u
      obtain ⟨e, ⟨he, heu⟩, huniq⟩ := hR2 u trivial
      refine ⟨e, ⟨he, (hS u e).mp heu⟩, ?_⟩
      rintro y ⟨hy, hyu⟩
      exact huniq y ⟨hy, (hS u y).mpr hyu⟩
  · intro n
    have hopen : IsOpen (V.J n : Set (GL (Fin n) k)) := Subgroup.isOpen_mono (kc_le V) (isOpen_Kc _)
    have hcpt : IsCompact (V.J n : Set (GL (Fin n) k)) :=
      GlobalTheory.SplitFlip.isCompact_KO.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hopen) V.J_le_KO
    refine ⟨?_, hopen, hcpt, V.J_le_KO⟩
    intro x
    show (MulAction.orbit (V.J n) (x : GL (Fin n) k ⧸ V.J n)).Finite
    haveI := QuotientGroup.discreteTopology hopen
    refine ((hcpt.image (f := fun g => ((g * x : GL (Fin n) k) : GL (Fin n) k ⧸ V.J n))
      (QuotientGroup.continuous_mk.comp (continuous_mul_right x))).finite_of_discrete).subset ?_
    rintro _ ⟨j, rfl⟩
    exact ⟨j, j.2, rfl⟩

end
