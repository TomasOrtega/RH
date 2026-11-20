import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AlgebraMapOLInjective

namespace ReciprocityTheory.ChartRestriction.G.T0

namespace ValPl

open IsDedekindDomain WithZero IsLocalRing

variable {O F L : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F]
  [Algebra O F] [IsFractionRing O F] [Field L] [Algebra F L] [FiniteDimensional F L]
  [Algebra.IsSeparable F L] [Algebra O L] [IsScalarTower O F L]
  [IsDedekindDomain (integralClosure O L)] [IsFractionRing (integralClosure O L) L]

variable (F) in

/- English proof (translation)
Use `set w := addv L v with hw_def`. Use `letI : Algebra (ResidueField ((vRing w).comap (algebraMap F L))) (ResidueField (vRing w)) := resAlg (F := F) w`. Establish `hunit : ∀ x : vRing w, IsUnit x ↔ w (x : L) = 0`. Introduce `x`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨u, rfl⟩`. Establish `hm : ((u : vRing w) : L) * ((↑u⁻¹ : vRing w) : L) = 1` using `congrArg Subtype.val u.mul_inv`. Establish `h1 : w ((u : vRing w) : L) + w ((↑u⁻¹ : vRing w) : L) = 0`. Rewrite using `[← AddValuation.map_mul, hm, AddValuation.map_one]`. Conclude with `wt_add_eq_zero (u : vRing w).2 (↑u⁻¹ : vRing w).2 h1`.

Introduce `h0`. Establish `hx0 : (x : L) ≠ 0` using `fun h => by`. Rewrite `h0` using `[h, AddValuation.map_zero]`. Conclude with `WithTop.top_ne_zero h0`. Establish `hinv : (x : L)⁻¹ ∈ vRing w` using `by show 0 ≤ w (x : L)⁻¹`.

Establish `h2 : w (x : L) + w (x : L)⁻¹ = 0`. Rewrite using `[← AddValuation.map_mul, mul_inv_cancel₀ hx0, AddValuation.map_one]`. Rewrite `h2` using `[h0, zero_add]`. Rewrite using `[h2]`. Conclude with `⟨⟨x, ⟨_, hinv⟩, Subtype.ext (by simp [mul_inv_cancel₀ hx0]), Subtype.ext (by simp [inv_mul_cancel₀ hx0])⟩, rfl⟩`.

Establish `hmaxV : ∀ x : vRing w, x ∈ maximalIdeal (vRing w) ↔ 0 < w (x : L)`. Introduce `x`. Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hunit]`. Conclude with `⟨fun h => lt_of_le_of_ne x.2 (Ne.symm h), fun h => h.ne'⟩`. Set `φB : integralClosure O L →+* vRing w` to `(algebraMap (integralClosure O L) L).codRestrict (vRing w) (fun b => addv_nonneg v b)`.

Set `ψB : integralClosure O L →+* ResidueField (vRing w)` to `(residue (vRing w)).comp φB`. Establish `hψB : ∀ b, ψB b = residue (vRing w) (φB b)` using `fun _ => rfl`. Establish `hkerB : RingHom.ker ψB = v.asIdeal`. Use extensionality with `b`. Rewrite using `[RingHom.mem_ker, hψB, IsLocalRing.residue_eq_zero_iff, hmaxV]`.

Conclude with `addv_pos_iff v b`. Use `haveI := v.isMaximal`. Establish `hsurjB : Function.Surjective ψB`. Introduce `z`. Take `⟨x, rfl⟩` from `IsLocalRing.residue_surjective z`.

Establish `hxv : v.valuation L (x : L) ≤ 1`. Distinguish the cases in `hx0 : (x : L) = 0`. Rewrite using `[hx0, map_zero]`. Conclude with `zero_le`. Establish `h` using `x.2`.

Express the relevant statement in the definitionally equal form `0 ≤ addv L v (x : L) at h`. Rewrite `h` using `[addv_apply v hx0]`. Establish `h' : 0 ≤ -log (v.valuation L (x : L))` using `by exact_mod_cast h`. Establish `hne : v.valuation L (x : L) ≠ 0` using `by simpa using hx0`. Rewrite using `[← exp_log hne, ← exp_zero, exp_le_exp]`.

Use linear arithmetic over natural numbers and integers. Take `⟨n, d, hnd⟩` from `HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer v (x : L) hxv`. Take `⟨d', i, hi, hdi⟩` from `Ideal.IsMaximal.exists_inv v.isMaximal d.2`. Use `⟨n * d', ?_⟩` and prove the remaining obligations. Establish `hd1 : ψB d * ψB d' = 1`.

Establish `: d' * d - 1 ∈ RingHom.ker ψB`. Rewrite using `[hkerB]`. Establish `: d' * d - 1 = -i` using `by linear_combination hdi`. Rewrite using `[this]`. Conclude with `v.asIdeal.neg_mem hi`.

Rewrite `this` using `[RingHom.mem_ker, map_sub, map_mul, map_one, sub_eq_zero]`. Rewrite using `[mul_comm]`. Conclude with `this`. Establish `hxd : x * φB d = φB n` using `Subtype.ext (by`. Express the relevant statement in the definitionally equal form `(x : L) * algebraMap (integralClosure O L) L d = algebraMap (integralClosure O L) L n`.

Conclude with `hnd)`. Establish `hres` using `congrArg (residue (vRing w)) hxd`. Rewrite `hres` using `[map_mul]`. Rewrite using `[map_mul, hψB n, ← hres, mul_assoc, ← hψB, hd1, mul_one]`. Set `jB : (integralClosure O L ⧸ v.asIdeal) ≃+* ResidueField (vRing w)` to `(Ideal.quotEquivOfEq hkerB.symm).trans (RingHom.quotientKerEquivOfSurjective hsurjB)`.

Establish `hOw : ∀ a : O, algebraMap O F a ∈ (vRing w).comap (algebraMap F L)` using `fun a => by`. Rewrite using `[ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply]`. Conclude with `((addv_mem_placesOver v).2 a).1`. Set `φO : O →+* (vRing w).comap (algebraMap F L)` to `(algebraMap O F).codRestrict _ hOw`. Set `ψO : O →+* ResidueField ((vRing w).comap (algebraMap F L))` to `(residue _).comp φO`.

Establish `hψO : ∀ a, ψO a = residue _ (φO a)` using `fun _ => rfl`. Establish `hmaxV0 : ∀ x : (vRing w).comap (algebraMap F L), x ∈ maximalIdeal ((vRing w).comap (algebraMap F L)) ↔ 0 < w (algebraMap F L x)`. Introduce `x`. Establish `h` using `hmaxV (comapIncl (vRing w) (algebraMap F L) x)`. Establish `e : ((comapIncl (vRing w) (algebraMap F L) x : vRing w) : L) = algebraMap F L x` using `rfl`.

Rewrite `h` using `[e]`. Rewrite using `[← h, IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff]`. Conclude with `⟨fun hx hu => hx (isUnit_of_map_unit _ _ hu), fun hx hu => hx (hu.map _)⟩`. Establish `hkerO : RingHom.ker ψO = maximalIdeal O`. Use extensionality with `a`.

Rewrite using `[RingHom.mem_ker, hψO, IsLocalRing.residue_eq_zero_iff, hmaxV0]`. Express the relevant statement in the definitionally equal form `0 < w (algebraMap F L (algebraMap O F a)) ↔ _`. Rewrite using `[← IsScalarTower.algebraMap_apply]`. Conclude with `((addv_mem_placesOver v).2 a).2`. Establish `hsurjO : Function.Surjective ψO`.

Introduce `z`. Take `⟨x, rfl⟩` from `IsLocalRing.residue_surjective z`. Distinguish the cases in `hx0 : (x : F) = 0`. Use `⟨0, ?_⟩` and prove the remaining obligations. Rewrite using `[map_zero]`.

Establish `: x = 0` using `Subtype.ext hx0`. Rewrite using `[this, map_zero]`. Break down `ValuationRing.isInteger_or_isInteger O (x : F) with ⟨a, ha⟩ | ⟨a, ha⟩` into its components or cases. Conclude with `⟨a, by rw [hψO]; congr 1; exact Subtype.ext ha⟩`. Distinguish the cases in `hau : IsUnit a`.

Take `⟨u, rfl⟩` from `hau`. Use `⟨↑u⁻¹, ?_⟩` and prove the remaining obligations. Rewrite using `[hψO]`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `algebraMap O F ↑u⁻¹ = (x : F)`. Establish `h1 : algebraMap O F (u : O) * algebraMap O F ↑u⁻¹ = 1`. Rewrite using `[← map_mul, Units.mul_inv, map_one]`. Establish `h2 : algebraMap O F (u : O) = (x : F)⁻¹` using `ha`. Rewrite `h1` using `[h2]`.

Clear denominators, using `at h1` for the nonvanishing conditions. Take the linear combination `h1`. It suffices to derive a contradiction. Establish `ham : a ∈ maximalIdeal O` using `hau`. Establish `hpos` using `(((addv_mem_placesOver v).2 a).2).2 ham`.

Rewrite `hpos` using `[IsScalarTower.algebraMap_apply O F L, ha, map_inv₀]`. Establish `hxnn : 0 ≤ w (algebraMap F L (x : F))` using `x.2`. Establish `hxL : algebraMap F L (x : F) ≠ 0`. Rewrite using `[Ne, map_eq_zero_iff _ (algebraMap F L).injective]`. Conclude with `hx0`.

Establish `hs : w (algebraMap F L (x : F)) + w (algebraMap F L (x : F))⁻¹ = 0`. Rewrite using `[← AddValuation.map_mul, mul_inv_cancel₀ hxL, AddValuation.map_one]`. Use `wt_add_eq_zero hxnn hpos.le hs` as an intermediate fact. Rewrite `hs` using `[this, zero_add]`. Rewrite `hpos` using `[hs]`.

Conclude with `lt_irrefl _ hpos`. Set `jO : (O ⧸ maximalIdeal O) ≃+* ResidueField ((vRing w).comap (algebraMap F L))` to `(Ideal.quotEquivOfEq hkerO.symm).trans (RingHom.quotientKerEquivOfSurjective hsurjO)`. Establish `hmax : (v.asIdeal.comap (algebraMap O (integralClosure O L))).IsMaximal` using `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal v.asIdeal`. Use `haveI : v.asIdeal.LiesOver (maximalIdeal O) := ⟨(IsLocalRing.eq_maximalIdeal hmax).symm⟩`. Establish `hc : (algebraMap (ResidueField ((vRing w).comap (algebraMap F L))) (ResidueField (vRing w))).comp jO.toRingHom = jB.toRingHom.comp (algebraMap (O ⧸ maximalIdeal O) (integralClosure O L ⧸ v.asIdeal))`.

Apply `Ideal.Quotient.ringHom_ext` to reduce the goal to its premises. Use extensionality with `a`. Simplify using `only [RingHom.comp_apply, Ideal.Quotient.algebraMap_mk_of_liesOver]`. Express the relevant statement in the definitionally equal form `ResidueField.map (comapIncl (vRing w) (algebraMap F L)) (jO _) = jB _`. Simplify using `only [jO, jB, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk, hψO, hψB, ResidueField.map_residue]`.

Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `algebraMap F L (algebraMap O F a) = algebraMap (integralClosure O L) L (algebraMap O _ a)`. Rewrite using `[← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]`. Rewrite using `[Ideal.inertiaDeg_eq_of_isMaximal (maximalIdeal O) v.asIdeal]`.

Conclude with `(Algebra.finrank_eq_of_equiv_equiv jO jB hc).symm`.
-/
theorem resDeg_addv (v : HeightOneSpectrum (integralClosure O L)) :
    letI := resAlg (F := F) (addv L v)
    Module.finrank (ResidueField ((vRing (addv L v)).comap (algebraMap F L)))
      (ResidueField (vRing (addv L v))) = v.asIdeal.inertiaDeg O := by
  classical
  set w := addv L v with hw_def
  letI : Algebra (ResidueField ((vRing w).comap (algebraMap F L))) (ResidueField (vRing w)) :=
    resAlg (F := F) w
  have hunit : ∀ x : vRing w, IsUnit x ↔ w (x : L) = 0 := by
    intro x
    constructor
    · rintro ⟨u, rfl⟩
      have hm : ((u : vRing w) : L) * ((↑u⁻¹ : vRing w) : L) = 1 :=
        congrArg Subtype.val u.mul_inv
      have h1 : w ((u : vRing w) : L) + w ((↑u⁻¹ : vRing w) : L) = 0 := by
        rw [← AddValuation.map_mul, hm, AddValuation.map_one]
      exact wt_add_eq_zero (u : vRing w).2 (↑u⁻¹ : vRing w).2 h1
    · intro h0
      have hx0 : (x : L) ≠ 0 := fun h => by
        rw [h, AddValuation.map_zero] at h0; exact WithTop.top_ne_zero h0
      have hinv : (x : L)⁻¹ ∈ vRing w := by
        show 0 ≤ w (x : L)⁻¹
        have h2 : w (x : L) + w (x : L)⁻¹ = 0 := by
          rw [← AddValuation.map_mul, mul_inv_cancel₀ hx0, AddValuation.map_one]
        rw [h0, zero_add] at h2
        rw [h2]
      exact ⟨⟨x, ⟨_, hinv⟩, Subtype.ext (by simp [mul_inv_cancel₀ hx0]),
        Subtype.ext (by simp [inv_mul_cancel₀ hx0])⟩, rfl⟩
  have hmaxV : ∀ x : vRing w, x ∈ maximalIdeal (vRing w) ↔ 0 < w (x : L) := by
    intro x
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hunit]
    exact ⟨fun h => lt_of_le_of_ne x.2 (Ne.symm h), fun h => h.ne'⟩

  let φB : integralClosure O L →+* vRing w :=
    (algebraMap (integralClosure O L) L).codRestrict (vRing w) (fun b => addv_nonneg v b)
  let ψB : integralClosure O L →+* ResidueField (vRing w) := (residue (vRing w)).comp φB
  have hψB : ∀ b, ψB b = residue (vRing w) (φB b) := fun _ => rfl
  have hkerB : RingHom.ker ψB = v.asIdeal := by
    ext b
    rw [RingHom.mem_ker, hψB, IsLocalRing.residue_eq_zero_iff, hmaxV]
    exact addv_pos_iff v b
  haveI := v.isMaximal
  have hsurjB : Function.Surjective ψB := by
    intro z
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
    have hxv : v.valuation L (x : L) ≤ 1 := by
      by_cases hx0 : (x : L) = 0
      · rw [hx0, map_zero]; exact zero_le
      have h := x.2
      change 0 ≤ addv L v (x : L) at h
      rw [addv_apply v hx0] at h
      have h' : 0 ≤ -log (v.valuation L (x : L)) := by exact_mod_cast h
      have hne : v.valuation L (x : L) ≠ 0 := by simpa using hx0
      rw [← exp_log hne, ← exp_zero, exp_le_exp]
      omega
    obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer v (x : L) hxv
    obtain ⟨d', i, hi, hdi⟩ := Ideal.IsMaximal.exists_inv v.isMaximal d.2
    refine ⟨n * d', ?_⟩
    have hd1 : ψB d * ψB d' = 1 := by
      have : d' * d - 1 ∈ RingHom.ker ψB := by
        rw [hkerB]
        have : d' * d - 1 = -i := by linear_combination hdi
        rw [this]; exact v.asIdeal.neg_mem hi
      rw [RingHom.mem_ker, map_sub, map_mul, map_one, sub_eq_zero] at this
      rw [mul_comm]; exact this
    have hxd : x * φB d = φB n := Subtype.ext (by
      change (x : L) * algebraMap (integralClosure O L) L d = algebraMap (integralClosure O L) L n
      exact hnd)
    have hres := congrArg (residue (vRing w)) hxd
    rw [map_mul] at hres
    rw [map_mul, hψB n, ← hres, mul_assoc, ← hψB, hd1, mul_one]
  let jB : (integralClosure O L ⧸ v.asIdeal) ≃+* ResidueField (vRing w) :=
    (Ideal.quotEquivOfEq hkerB.symm).trans (RingHom.quotientKerEquivOfSurjective hsurjB)

  have hOw : ∀ a : O, algebraMap O F a ∈ (vRing w).comap (algebraMap F L) := fun a => by
    rw [ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply]
    exact ((addv_mem_placesOver v).2 a).1
  let φO : O →+* (vRing w).comap (algebraMap F L) := (algebraMap O F).codRestrict _ hOw
  let ψO : O →+* ResidueField ((vRing w).comap (algebraMap F L)) := (residue _).comp φO
  have hψO : ∀ a, ψO a = residue _ (φO a) := fun _ => rfl
  have hmaxV0 : ∀ x : (vRing w).comap (algebraMap F L),
      x ∈ maximalIdeal ((vRing w).comap (algebraMap F L)) ↔ 0 < w (algebraMap F L x) := by
    intro x
    have h := hmaxV (comapIncl (vRing w) (algebraMap F L) x)
    have e : ((comapIncl (vRing w) (algebraMap F L) x : vRing w) : L) = algebraMap F L x := rfl
    rw [e] at h
    rw [← h, IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      mem_nonunits_iff]
    exact ⟨fun hx hu => hx (isUnit_of_map_unit _ _ hu), fun hx hu => hx (hu.map _)⟩
  have hkerO : RingHom.ker ψO = maximalIdeal O := by
    ext a
    rw [RingHom.mem_ker, hψO, IsLocalRing.residue_eq_zero_iff, hmaxV0]
    change 0 < w (algebraMap F L (algebraMap O F a)) ↔ _
    rw [← IsScalarTower.algebraMap_apply]
    exact ((addv_mem_placesOver v).2 a).2
  have hsurjO : Function.Surjective ψO := by
    intro z
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
    by_cases hx0 : (x : F) = 0
    · refine ⟨0, ?_⟩
      rw [map_zero]
      have : x = 0 := Subtype.ext hx0
      rw [this, map_zero]
    rcases ValuationRing.isInteger_or_isInteger O (x : F) with ⟨a, ha⟩ | ⟨a, ha⟩
    · exact ⟨a, by rw [hψO]; congr 1; exact Subtype.ext ha⟩
    · by_cases hau : IsUnit a
      · obtain ⟨u, rfl⟩ := hau
        refine ⟨↑u⁻¹, ?_⟩
        rw [hψO]; congr 1
        apply Subtype.ext
        change algebraMap O F ↑u⁻¹ = (x : F)
        have h1 : algebraMap O F (u : O) * algebraMap O F ↑u⁻¹ = 1 := by
          rw [← map_mul, Units.mul_inv, map_one]
        have h2 : algebraMap O F (u : O) = (x : F)⁻¹ := ha
        rw [h2] at h1
        field_simp at h1
        linear_combination h1
      · exfalso
        have ham : a ∈ maximalIdeal O := hau
        have hpos := (((addv_mem_placesOver v).2 a).2).2 ham
        rw [IsScalarTower.algebraMap_apply O F L, ha, map_inv₀] at hpos
        have hxnn : 0 ≤ w (algebraMap F L (x : F)) := x.2
        have hxL : algebraMap F L (x : F) ≠ 0 := by
          rw [Ne, map_eq_zero_iff _ (algebraMap F L).injective]; exact hx0
        have hs : w (algebraMap F L (x : F)) + w (algebraMap F L (x : F))⁻¹ = 0 := by
          rw [← AddValuation.map_mul, mul_inv_cancel₀ hxL, AddValuation.map_one]
        have := wt_add_eq_zero hxnn hpos.le hs
        rw [this, zero_add] at hs
        rw [hs] at hpos
        exact lt_irrefl _ hpos
  let jO : (O ⧸ maximalIdeal O) ≃+* ResidueField ((vRing w).comap (algebraMap F L)) :=
    (Ideal.quotEquivOfEq hkerO.symm).trans (RingHom.quotientKerEquivOfSurjective hsurjO)
  have hmax : (v.asIdeal.comap (algebraMap O (integralClosure O L))).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal v.asIdeal
  haveI : v.asIdeal.LiesOver (maximalIdeal O) := ⟨(IsLocalRing.eq_maximalIdeal hmax).symm⟩
  have hc : (algebraMap (ResidueField ((vRing w).comap (algebraMap F L)))
      (ResidueField (vRing w))).comp jO.toRingHom =
      jB.toRingHom.comp (algebraMap (O ⧸ maximalIdeal O) (integralClosure O L ⧸ v.asIdeal)) := by
    apply Ideal.Quotient.ringHom_ext
    ext a
    simp only [RingHom.comp_apply, Ideal.Quotient.algebraMap_mk_of_liesOver]
    change ResidueField.map (comapIncl (vRing w) (algebraMap F L)) (jO _) = jB _
    simp only [jO, jB, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
      RingHom.quotientKerEquivOfSurjective_apply_mk, hψO, hψB, ResidueField.map_residue]
    congr 1
    apply Subtype.ext
    change algebraMap F L (algebraMap O F a) = algebraMap (integralClosure O L) L (algebraMap O _ a)
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  rw [Ideal.inertiaDeg_eq_of_isMaximal (maximalIdeal O) v.asIdeal]
  exact (Algebra.finrank_eq_of_equiv_equiv jO jB hc).symm

end ValPl

end ReciprocityTheory.ChartRestriction.G.T0
