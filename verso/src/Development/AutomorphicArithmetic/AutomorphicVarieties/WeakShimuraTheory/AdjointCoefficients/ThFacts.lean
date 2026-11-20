import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointMemSp4
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.GLinkQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop
import Mathlib.NumberTheory.Multiplicity

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

/- English proof (translation)
Establish `hpr : l.Prime` using `Fact.out`. Establish `hp : Prime (l : ℤ_[l])` using `PadicInt.prime_p`. Establish `hodd : Odd l` using `hpr.odd_of_ne_two h2`. Establish `hx : ¬ (l : ℤ_[l]) ∣ u`. Introduce `hd`.

Establish `h1 : (l : ℤ_[l]) ∣ u ^ l` using `dvd_pow hd hpr.ne_zero`. Rewrite `h1` using `[h]`. Conclude with `hp.not_dvd_one h1`. Establish `hxy : (l : ℤ_[l]) ∣ u - 1`. Establish `hk : u - 1 ∈ RingHom.ker (PadicInt.toZMod : ℤ_[l] →+* ZMod l)`.

Rewrite using `[RingHom.mem_ker, map_sub, map_one]`. Establish `h3` using `congrArg (PadicInt.toZMod : ℤ_[l] →+* ZMod l) h`. Rewrite `h3` using `[map_pow, map_one, ZMod.pow_card]`. Rewrite using `[h3, sub_self]`. Rewrite `hk` using `[PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]`.

Conclude with `hk`. Establish `hg` using `emultiplicity_geom_sum₂_eq_one hp hodd hxy hx`. Establish `hne : (∑ i ∈ Finset.range l, u ^ i * 1 ^ (l - 1 - i)) ≠ 0`. Introduce `h0`. Rewrite `hg` using `[h0, emultiplicity_zero]`.

Simplify using `at hg`. Establish `hmul` using `geom_sum₂_mul u 1 l`. Rewrite `hmul` using `[h, one_pow, sub_self]`. Conclude with `sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hne)`.
-/
private theorem no_tors1 {l : ℕ} [hl : Fact l.Prime] (h2 : l ≠ 2) {u : ℤ_[l]} (h : u ^ l = 1) : u = 1 := by
  have hpr : l.Prime := Fact.out
  have hp : Prime (l : ℤ_[l]) := PadicInt.prime_p
  have hodd : Odd l := hpr.odd_of_ne_two h2
  have hx : ¬ (l : ℤ_[l]) ∣ u := by
    intro hd
    have h1 : (l : ℤ_[l]) ∣ u ^ l := dvd_pow hd hpr.ne_zero
    rw [h] at h1
    exact hp.not_dvd_one h1
  have hxy : (l : ℤ_[l]) ∣ u - 1 := by
    have hk : u - 1 ∈ RingHom.ker (PadicInt.toZMod : ℤ_[l] →+* ZMod l) := by
      rw [RingHom.mem_ker, map_sub, map_one]
      have h3 := congrArg (PadicInt.toZMod : ℤ_[l] →+* ZMod l) h
      rw [map_pow, map_one, ZMod.pow_card] at h3
      rw [h3, sub_self]
    rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hk
    exact hk
  have hg := emultiplicity_geom_sum₂_eq_one hp hodd hxy hx
  have hne : (∑ i ∈ Finset.range l, u ^ i * 1 ^ (l - 1 - i)) ≠ 0 := by
    intro h0
    rw [h0, emultiplicity_zero] at hg
    simp at hg
  have hmul := geom_sum₂_mul u 1 l
  rw [h, one_pow, sub_self] at hmul
  exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hne)

/- English proof (translation)
Proceed by induction on `a generalizing u with`. Consider the case `zero => simpa using h`. Consider the case `succ a ih`. Establish `hu : u ^ l = 1`. Apply `ih` to reduce the goal to its premises.

Rewrite using `[← pow_mul, ← pow_succ']`. Conclude with `h`. Establish `hv : (u : ℤ_[l]) ^ l = 1`. Rewrite using `[← Units.val_pow_eq_pow_val, hu, Units.val_one]`. Conclude with `Units.ext (by rw [no_tors1 h2 hv, Units.val_one])`.
-/
private theorem no_tors {l : ℕ} [Fact l.Prime] (h2 : l ≠ 2) {u : ℤ_[l]ˣ} {a : ℕ} (h : u ^ l ^ a = 1) : u = 1 := by
  induction a generalizing u with
  | zero => simpa using h
  | succ a ih =>
    have hu : u ^ l = 1 := by
      apply ih
      rw [← pow_mul, ← pow_succ']
      exact h
    have hv : (u : ℤ_[l]) ^ l = 1 := by
      rw [← Units.val_pow_eq_pow_val, hu, Units.val_one]
    exact Units.ext (by rw [no_tors1 h2 hv, Units.val_one])

/- English proof (translation)
Establish `d1` using `orderOf_dvd_of_pow_eq_one h1`. Establish `d2` using `orderOf_dvd_of_pow_eq_one h2`. Establish `hc : (l ^ a).Coprime m` using `Nat.Coprime.pow_left a hm`. Establish `hd : orderOf x ∣ 1`. Rewrite using `[← hc.gcd_eq_one]`.

Conclude with `Nat.dvd_gcd d1 d2`. Conclude with `orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)`.
-/
private theorem one_of_cop {M : Type} [Group M] {x : M} {l m a : ℕ} (hm : l.Coprime m) (h1 : x ^ l ^ a = 1)
    (h2 : x ^ m = 1) : x = 1 := by
  have d1 := orderOf_dvd_of_pow_eq_one h1
  have d2 := orderOf_dvd_of_pow_eq_one h2
  have hc : (l ^ a).Coprime m := Nat.Coprime.pow_left a hm
  have hd : orderOf x ∣ 1 := by
    rw [← hc.gcd_eq_one]
    exact Nat.dvd_gcd d1 d2
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)

/- English proof (translation)
Establish `hc : (⁅H, H⁆ : Subgroup Γ) ≤ γ.ker` using `le_trans (Subgroup.commutator_mono le_top le_top) (Abelianization.commutator_subset_ker γ)`. Establish `hcl` using `Subgroup.topologicalClosure_minimal _ hc hγ`. Establish `hm` using `hcl hs`. Rewrite `hm` using `[MonoidHom.mem_ker, map_pow]`. Conclude with `hm`.
-/
private theorem mu_pow {Γ M : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CommGroup M] (γ : Γ →* M)
    (hγ : IsClosed (γ.ker : Set Γ)) {H : Subgroup Γ} {s : Γ} {n : ℕ}
    (hs : s ^ n ∈ (⁅H, H⁆ : Subgroup Γ).topologicalClosure) : γ s ^ n = 1 := by
  have hc : (⁅H, H⁆ : Subgroup Γ) ≤ γ.ker :=
    le_trans (Subgroup.commutator_mono le_top le_top) (Abelianization.commutator_subset_ker γ)
  have hcl := Subgroup.topologicalClosure_minimal _ hc hγ
  have hm := hcl hs
  rw [MonoidHom.mem_ker, map_pow] at hm
  exact hm

section

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]

variable {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c}

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem ap_th (g : G ℚ Ω) :
    D.th g = chiO ℚ Ω l c.O g * (D.om g)⁻¹ * D.ξ g * (chiO ℚ Ω l c.O g ^ (D.e : ℤ) * D.ψ g) := rfl

/- English proof (translation)
Establish `: chiO ℚ Ω l c.O g = 1` using `by rw [chiO, MonoidHom.comp_apply, h0, map_one]`. Rewrite using `[ap_th, this, h1, h2, h3]`. Simplify using the standard rewrite rules.
-/
private theorem th_one {g : G ℚ Ω} (h0 : cycZ ℚ Ω l g = 1) (h1 : D.om g = 1) (h2 : D.ξ g = 1) (h3 : D.ψ g = 1) :
    D.th g = 1 := by
  have : chiO ℚ Ω l c.O g = 1 := by rw [chiO, MonoidHom.comp_apply, h0, map_one]
  rw [ap_th, this, h1, h2, h3]; simp

end

/- English proof (translation)
Establish `hpr : l.Prime` using `Fact.out`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_one]`. Use `PadicInt.ext_of_toZModPow.mp (fun n => ?_)` and prove the remaining obligations.

Use `haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hpr.ne_zero⟩`. Establish `hAn : ¬ A.valuation ((l ^ n : ℕ) : Ω) < 1`. Rewrite using `[Nat.cast_pow, map_pow]`. Use `push_neg at hA ⊢`. Conclude with `one_le_pow₀ hA`.

Establish `hk : Chr.cls F Ω (l ^ n) g = 1` using `((Chr.clsFacts F Ω (l ^ n)).2.2.2.2 A hAn) hg`. Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)`. Establish `h1` using `Chr.cls_spec (l ^ n) g ζ hζ.pow_eq_one`. Rewrite `h1` using `[hk]`. Establish `h2` using `cyclotomicCharacter.spec l (n := n) (MulSemiringAction.toRingAut (G F Ω) Ω g) ζ hζ.pow_eq_one`.

Establish `h3 : ζ ^ (PadicInt.toZModPow n (cycZ F Ω l g : ℤ_[l])).val = ζ ^ ((1 : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)).val`. Rewrite using `[← h1]`. Conclude with `h2.symm`. Establish `h4` using `hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h3`. Rewrite using `[map_one]`.

Conclude with `ZMod.val_injective _ (by rw [h4, Units.val_one])`.
-/
private theorem cycZ_eq_one_of_mem_ine_of_not_valuation_lt {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]
    (F : IntermediateField ℚ Ω) [NumberField F] (A : ValuationSubring Ω) (hA : ¬ A.valuation (l : Ω) < 1)
    (g : G F Ω) (hg : g ∈ Ine A) : cycZ F Ω l g = 1 := by
  have hpr : l.Prime := Fact.out
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  apply Units.ext
  rw [Units.val_one]
  refine PadicInt.ext_of_toZModPow.mp (fun n => ?_)
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hpr.ne_zero⟩
  have hAn : ¬ A.valuation ((l ^ n : ℕ) : Ω) < 1 := by
    rw [Nat.cast_pow, map_pow]
    push_neg at hA ⊢
    exact one_le_pow₀ hA
  have hk : Chr.cls F Ω (l ^ n) g = 1 := ((Chr.clsFacts F Ω (l ^ n)).2.2.2.2 A hAn) hg
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)
  have h1 := Chr.cls_spec (l ^ n) g ζ hζ.pow_eq_one
  rw [hk] at h1
  have h2 := cyclotomicCharacter.spec l (n := n) (MulSemiringAction.toRingAut (G F Ω) Ω g) ζ hζ.pow_eq_one
  have h3 : ζ ^ (PadicInt.toZModPow n (cycZ F Ω l g : ℤ_[l])).val = ζ ^ ((1 : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)).val := by
    rw [← h1]
    exact h2.symm
  have h4 := hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h3
  rw [map_one]
  exact ZMod.val_injective _ (by rw [h4, Units.val_one])

/- English proof (translation)
Simplify using `only [cycZ, MonoidHom.comp_apply]`. Both sides reduce to the same expression.
-/
private theorem cycZ_resQ_eq_cycZ {Ω : Type} [Field Ω] [CharZero Ω] {l : ℕ} [Fact l.Prime]
    (F : IntermediateField ℚ Ω) (g : G F Ω) : cycZ ℚ Ω l (resQ F g) = cycZ F Ω l g := by
  simp only [cycZ, MonoidHom.comp_apply]
  rfl

/- English proof (translation)
Introduce `g hg`. Take `⟨A, hAw, hgI, hrb⟩` from `hg`. Establish `hpr : l.Prime` using `Fact.out`. Establish `hA : ¬ A.valuation (l : Ω) < 1` using `hAw l (by simp)`. Establish `hcyc : cycZ ℚ Ω l (resQ T.F g) = 1`.

Rewrite using `[cycZ_resQ_eq_cycZ]`. Conclude with `cycZ_eq_one_of_mem_ine_of_not_valuation_lt T.F A hA g hgI`. Establish `hchi : chiO ℚ Ω l c.O (resQ T.F g) = 1`. Simplify using `only [chiO, MonoidHom.comp_apply, hcyc, map_one]`. Establish `hres : ∀ i, residue c.O (↑(D.ps i (resQ T.F g))) = 1`.

Introduce `i`. Establish `h` using `congrFun (congrFun hrb i) i`. Simplify `h` using `[Raw.rbar, mapRep, diagRep, Raw.r0, Matrix.one_apply]`. Establish `hps : D.ψ (resQ T.F g) = 1` using `hOk.kb A (fun p hp => hAw p (by simpa using hp)) g hgI hrb`. Establish `hcf` using `(congrFacts Ω l c).2.2.2.1`.

Establish `hom : D.om (resQ T.F g) = 1`. Apply `hcf _ 1 (l - 1)` to reduce the goal to its premises. Introduce `hd`. Use `Nat.le_of_dvd (by have := hpr.two_le; omega) hd` as an intermediate fact. Use `hpr.two_le` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `h` using `congrArg (fun f => f (resQ T.F g)) hG.om_pow`. Simplify using `using h`. Conclude with `one_pow _`. Rewrite using `[← IsLocalRing.residue_eq_zero_iff, map_sub]`.

Establish `h` using `hG.om_bar (resQ T.F g)`. Simplify using `only [Raw.bar] at h`. Rewrite using `[h, hchi, Units.val_one, sub_self]`. Take `⟨m, hm, hxm⟩` from `hG.xi_ord`. Establish `hxi : D.ξ (resQ T.F g) = 1`.

Apply `hcf _ 1 m` to reduce the goal to its premises. Conclude with `(Nat.Prime.coprime_iff_not_dvd hpr).mp hm`. Establish `h` using `congrArg (fun f => f (resQ T.F g)) hxm`. Simplify using `using h`. Conclude with `one_pow _`.

Rewrite using `[← IsLocalRing.residue_eq_zero_iff, map_sub]`. Establish `h` using `hres 2`. Simplify using `only [Raw.ps, Raw.al, Matrix.cons_val, MonoidHom.mul_apply, hchi, one_mul] at h`. Rewrite `h` using `[MonoidHom.inv_apply, hom, inv_one, one_mul]`. Rewrite using `[h, Units.val_one, map_one, sub_self]`.

Conclude with `th_one hcyc hom hxi hps`.
-/
private theorem nu_eq_one_of_mem_n_of_good_of_ok {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D) (hG : D.Good) (hOk : T.Ok) :
    ∀ g ∈ (T.fr ∅).N, (T.fr ∅).ν g = 1 := by
  intro g hg
  obtain ⟨A, hAw, hgI, hrb⟩ := hg
  have hpr : l.Prime := Fact.out
  have hA : ¬ A.valuation (l : Ω) < 1 := hAw l (by simp)
  have hcyc : cycZ ℚ Ω l (resQ T.F g) = 1 := by
    rw [cycZ_resQ_eq_cycZ]
    exact cycZ_eq_one_of_mem_ine_of_not_valuation_lt T.F A hA g hgI
  have hchi : chiO ℚ Ω l c.O (resQ T.F g) = 1 := by
    simp only [chiO, MonoidHom.comp_apply, hcyc, map_one]
  have hres : ∀ i, residue c.O (↑(D.ps i (resQ T.F g))) = 1 := by
    intro i
    have h := congrFun (congrFun hrb i) i
    simpa [Raw.rbar, mapRep, diagRep, Raw.r0, Matrix.one_apply] using h
  have hps : D.ψ (resQ T.F g) = 1 :=
    hOk.kb A (fun p hp => hAw p (by simpa using hp)) g hgI hrb
  have hcf := (congrFacts Ω l c).2.2.2.1
  have hom : D.om (resQ T.F g) = 1 := by
    apply hcf _ 1 (l - 1)
    · intro hd
      have := Nat.le_of_dvd (by have := hpr.two_le; omega) hd
      have := hpr.two_le
      omega
    · have h := congrArg (fun f => f (resQ T.F g)) hG.om_pow
      simpa using h
    · exact one_pow _
    · rw [← IsLocalRing.residue_eq_zero_iff, map_sub]
      have h := hG.om_bar (resQ T.F g)
      simp only [Raw.bar] at h
      rw [h, hchi, Units.val_one, sub_self]
  obtain ⟨m, hm, hxm⟩ := hG.xi_ord
  have hxi : D.ξ (resQ T.F g) = 1 := by
    apply hcf _ 1 m
    · exact (Nat.Prime.coprime_iff_not_dvd hpr).mp hm
    · have h := congrArg (fun f => f (resQ T.F g)) hxm
      simpa using h
    · exact one_pow _
    · rw [← IsLocalRing.residue_eq_zero_iff, map_sub]
      have h := hres 2
      simp only [Raw.ps, Raw.al, Matrix.cons_val, MonoidHom.mul_apply, hchi, one_mul] at h
      rw [MonoidHom.inv_apply, hom, inv_one, one_mul] at h
      rw [h, Units.val_one, map_one, sub_self]
  exact th_one hcyc hom hxi hps

/- English proof (translation)
Take `⟨k, rfl⟩ : ∃ k, n = k + 1` from `⟨n - 1, by omega⟩`. Rewrite using `[Nat.add_sub_cancel, add_comm]`. Conclude with `Nat.coprime_add_self_left.mpr (Nat.coprime_one_left k)`.
-/
private theorem coprime_sub_one_of_one_le (n : ℕ) (h : 1 ≤ n) : n.Coprime (n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel, add_comm]
  exact Nat.coprime_add_self_left.mpr (Nat.coprime_one_left k)

/- English proof (translation)
Take `⟨k, rfl⟩` from `hd`. Rewrite using `[pow_mul, h, one_pow]`.
-/
private theorem pow_eq_one_of_pow_eq_one_of_dvd {M : Type} [Monoid M] {x : M} {n N : ℕ} (h : x ^ n = 1) (hd : n ∣ N) : x ^ N = 1 := by
  obtain ⟨k, rfl⟩ := hd
  rw [pow_mul, h, one_pow]

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem cycZ_resQ_eq_cycZ_of_charZero {Ω : Type} [Field Ω] [CharZero Ω] (F : IntermediateField ℚ Ω) {l : ℕ} [Fact l.Prime] (g : G F Ω) :
    cycZ ℚ Ω l (resQ F g) = cycZ F Ω l g := rfl

/- English proof (translation)
Introduce `v s hs`. Express the relevant statement in the definitionally equal form `s ∈ muOf l (Dec (T.pl v)) at hs`. Take `⟨-, a, ha⟩` from `hs`. Establish `hcont : Continuous (resQ T.F)` using `(galEmbTop ℚ T.F Ω).1.continuous`. Establish `hkc : IsClosed ((cycZ T.F Ω l).ker : Set (G T.F Ω))`.

Establish `e : ((cycZ T.F Ω l).ker : Set (G T.F Ω)) = (cycZ T.F Ω l) ⁻¹' {1}`. Use extensionality with `x`. Simplify using the standard rewrite rules. Rewrite using `[e]`. Conclude with `isClosed_singleton.preimage (continuous_cycZ _ _ _)`.

Establish `hc1 : cycZ T.F Ω l s = 1` using `no_tors hG.l_odd (mu_pow _ hkc ha)`. Establish `hc2 : chiO ℚ Ω l c.O (resQ T.F s) = 1`. Simplify using `only [chiO, MonoidHom.comp_apply, cycZ_resQ_eq_cycZ_of_charZero, hc1, map_one]`. Establish `hom : IsOpen (D.om.ker : Set (G ℚ Ω))` using `(GradeZeroInterpolatingElement.facts D hG).2.2.2.2.2.2.2.2.2.2.2.2.1`. Establish `hop : IsOpen ((D.om⁻¹ * D.ξ * D.ψ).ker : Set (G ℚ Ω))`.

Use `Subgroup.isOpen_mono (H₁ := D.om.ker ⊓ D.ξ.ker ⊓ D.ψ.ker) ?_ ?_` and prove the remaining obligations. Introduce `x hx`. Simplify using `only [Subgroup.mem_inf, MonoidHom.mem_ker] at hx`. Rewrite using `[MonoidHom.mem_ker, MonoidHom.mul_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, hx.1.1, hx.1.2, hx.2]`. Simplify using the standard rewrite rules.

Simplify using `only [Subgroup.coe_inf]`. Conclude with `(hom.inter hG.xi_open).inter hG.psi_open`. Use `set χ : G T.F Ω →* c.Oˣ := (D.om⁻¹ * D.ξ * D.ψ).comp (resQ T.F) with hχ`. Establish `hχc : IsClosed (χ.ker : Set (G T.F Ω))`. Apply `Subgroup.isClosed_of_isOpen` to reduce the goal to its premises.

Conclude with `hop.preimage hcont`. Establish `hl : χ s ^ l ^ a = 1` using `mu_pow χ hχc ha`. Establish `hν : (T.fr ∅).ν s = χ s`. Express the relevant statement in the definitionally equal form `D.th (resQ T.F s) = _`. Rewrite using `[ap_th, hc2]`.

Simplify using `[hχ]`. Rewrite using `[hν]`. Take `⟨m1, hm1, hξ⟩` from `hG.xi_ord`. Take `⟨m2, hm2, hψ⟩` from `hDeep`. Establish `e1 : D.om (resQ T.F s) ^ (l - 1) = 1`.

Establish `h` using `congrArg (fun f => f (resQ T.F s)) hG.om_pow`. Simplify using `using h`. Establish `e2 : D.ξ (resQ T.F s) ^ m1 = 1`. Establish `h` using `congrArg (fun f => f (resQ T.F s)) hξ`. Simplify using `using h`.

Establish `e3 : D.ψ (resQ T.F s) ^ m2 = 1` using `hψ s`. Establish `hco : l.Coprime ((l - 1) * m1 * m2)` using `Nat.Coprime.mul_right (Nat.Coprime.mul_right (coprime_sub_one_of_one_le l (Fact.out : l.Prime).one_lt.le) hm1) hm2`. Establish `hM : χ s ^ ((l - 1) * m1 * m2) = 1`. Rewrite using `[hχ, MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, mul_pow, mul_pow, inv_pow, pow_eq_one_of_pow_eq_one_of_dvd e1 ⟨m1 * m2, by ring⟩, pow_eq_one_of_pow_eq_one_of_dvd e2 ⟨(l - 1) * m2, by ring⟩, pow_eq_one_of_pow_eq_one_of_dvd e3 (dvd_mul_left …`. Simplify using the standard rewrite rules.

Conclude with `one_of_cop hco hl hM`.
-/
private theorem nu_eq_one_of_mem_mu_of_good_of_deep {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D) (hG : D.Good) (hDeep : T.Deep) :
    ∀ v, ∀ s ∈ (T.fr ∅).Mu v, (T.fr ∅).ν s = 1 := by
  intro v s hs
  change s ∈ muOf l (Dec (T.pl v)) at hs
  obtain ⟨-, a, ha⟩ := hs
  have hcont : Continuous (resQ T.F) := (galEmbTop ℚ T.F Ω).1.continuous
  have hkc : IsClosed ((cycZ T.F Ω l).ker : Set (G T.F Ω)) := by
    have e : ((cycZ T.F Ω l).ker : Set (G T.F Ω)) = (cycZ T.F Ω l) ⁻¹' {1} := by
      ext x
      simp
    rw [e]
    exact isClosed_singleton.preimage (continuous_cycZ _ _ _)
  have hc1 : cycZ T.F Ω l s = 1 := no_tors hG.l_odd (mu_pow _ hkc ha)
  have hc2 : chiO ℚ Ω l c.O (resQ T.F s) = 1 := by
    simp only [chiO, MonoidHom.comp_apply, cycZ_resQ_eq_cycZ_of_charZero, hc1, map_one]
  have hom : IsOpen (D.om.ker : Set (G ℚ Ω)) := (GradeZeroInterpolatingElement.facts D hG).2.2.2.2.2.2.2.2.2.2.2.2.1
  have hop : IsOpen ((D.om⁻¹ * D.ξ * D.ψ).ker : Set (G ℚ Ω)) := by
    refine Subgroup.isOpen_mono (H₁ := D.om.ker ⊓ D.ξ.ker ⊓ D.ψ.ker) ?_ ?_
    · intro x hx
      simp only [Subgroup.mem_inf, MonoidHom.mem_ker] at hx
      rw [MonoidHom.mem_ker, MonoidHom.mul_apply, MonoidHom.mul_apply, MonoidHom.inv_apply,
        hx.1.1, hx.1.2, hx.2]
      simp
    · simp only [Subgroup.coe_inf]
      exact (hom.inter hG.xi_open).inter hG.psi_open
  set χ : G T.F Ω →* c.Oˣ := (D.om⁻¹ * D.ξ * D.ψ).comp (resQ T.F) with hχ
  have hχc : IsClosed (χ.ker : Set (G T.F Ω)) := by
    apply Subgroup.isClosed_of_isOpen
    exact hop.preimage hcont
  have hl : χ s ^ l ^ a = 1 := mu_pow χ hχc ha
  have hν : (T.fr ∅).ν s = χ s := by
    change D.th (resQ T.F s) = _
    rw [ap_th, hc2]
    simp [hχ]
  rw [hν]
  obtain ⟨m1, hm1, hξ⟩ := hG.xi_ord
  obtain ⟨m2, hm2, hψ⟩ := hDeep
  have e1 : D.om (resQ T.F s) ^ (l - 1) = 1 := by
    have h := congrArg (fun f => f (resQ T.F s)) hG.om_pow
    simpa using h
  have e2 : D.ξ (resQ T.F s) ^ m1 = 1 := by
    have h := congrArg (fun f => f (resQ T.F s)) hξ
    simpa using h
  have e3 : D.ψ (resQ T.F s) ^ m2 = 1 := hψ s
  have hco : l.Coprime ((l - 1) * m1 * m2) :=
    Nat.Coprime.mul_right (Nat.Coprime.mul_right
      (coprime_sub_one_of_one_le l (Fact.out : l.Prime).one_lt.le) hm1) hm2
  have hM : χ s ^ ((l - 1) * m1 * m2) = 1 := by
    rw [hχ, MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.mul_apply, MonoidHom.inv_apply,
      mul_pow, mul_pow, inv_pow,
      pow_eq_one_of_pow_eq_one_of_dvd e1 ⟨m1 * m2, by ring⟩,
      pow_eq_one_of_pow_eq_one_of_dvd e2 ⟨(l - 1) * m2, by ring⟩,
      pow_eq_one_of_pow_eq_one_of_dvd e3 (dvd_mul_left _ _)]
    simp
  exact one_of_cop hco hl hM

/- English proof (translation)
Take `⟨j, hj⟩` from `hσ`. Take `⟨k, hk⟩` from `hτ`. Take `⟨g, hg⟩` from `NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := ℚ) j k (Subsingleton.elim _ _)`. Establish `e : ∀ x, g.symm (τ x) = σ (g.symm x)`. Introduce `x`.

Apply `j.injective` to reduce the goal to its premises. Establish `h1` using `hk x`. Rewrite `h1` using `[← hg]`. Simplify using `only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply] at h1`. Rewrite using `[h1, hj]`.

Establish `ht : τ = g * σ * g⁻¹`. Use extensionality with `x`. Rewrite using `[AlgEquiv.mul_apply, AlgEquiv.mul_apply, AlgEquiv.aut_inv, ← e, AlgEquiv.apply_symm_apply]`. Rewrite using `[ht, map_mul, map_mul, map_inv, mul_inv_cancel_comm]`.
-/
private theorem hom_eq_of_isCC_of_isCC {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {M : Type} [CommGroup M] (γ : G ℚ Ω →* M) {σ τ : G ℚ Ω}
    (hσ : IsCC σ) (hτ : IsCC τ) : γ σ = γ τ := by
  obtain ⟨j, hj⟩ := hσ
  obtain ⟨k, hk⟩ := hτ
  obtain ⟨g, hg⟩ := NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := ℚ) j k
    (Subsingleton.elim _ _)
  have e : ∀ x, g.symm (τ x) = σ (g.symm x) := by
    intro x
    apply j.injective
    have h1 := hk x
    rw [← hg] at h1
    simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply] at h1
    rw [h1, hj]
  have ht : τ = g * σ * g⁻¹ := by
    ext x
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, AlgEquiv.aut_inv, ← e, AlgEquiv.apply_symm_apply]
  rw [ht, map_mul, map_mul, map_inv, mul_inv_cancel_comm]

/- English proof (translation)
Introduce `g hg`. Take `⟨j, hj⟩` from `hg`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Apply `j.injective` to reduce the goal to its premises.

Rewrite using `[AlgEquiv.mul_apply, hj, hj, Complex.conj_conj, AlgEquiv.one_apply]`. Establish `hq : IsCC (resQ T.F g)` using `⟨j, fun x => hj x⟩`. Establish `hf` using `(GradeZeroInterpolatingElement.facts D hG).2.2.2.2.2.2.2.1.2.2`. Express the relevant statement in the definitionally equal form `D.th (resQ T.F g) = -1`. Rewrite using `[hom_eq_of_isCC_of_isCC D.th hq hG.isCC, hf]`.
-/
private theorem mul_self_eq_one_and_nu_neg_one_of_isCC {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D) (hG : D.Good) :
    ∀ g : G T.F Ω, IsCC g → g * g = 1 ∧ (T.fr ∅).ν g = -1 := by
  intro g hg
  obtain ⟨j, hj⟩ := hg
  refine ⟨?_, ?_⟩
  · ext x
    apply j.injective
    rw [AlgEquiv.mul_apply, hj, hj, Complex.conj_conj, AlgEquiv.one_apply]
  · have hq : IsCC (resQ T.F g) := ⟨j, fun x => hj x⟩
    have hf := (GradeZeroInterpolatingElement.facts D hG).2.2.2.2.2.2.2.1.2.2
    change D.th (resQ T.F g) = -1
    rw [hom_eq_of_isCC_of_isCC D.th hq hG.isCC, hf]

/- English proof (translation)
Establish `hpos : 0 < l ^ 1`. Use `(Fact.out : l.Prime).pos` as an intermediate fact. Check the signs of the components of the expression. Use `haveI : NeZero (l ^ 1) := ⟨hpos.ne'⟩`. Use `set z := PadicInt.toZModPow 1 x with hz`.

Establish `hk : x - ((z.val : ℕ) : ℤ_[l]) ∈ RingHom.ker (PadicInt.toZModPow 1 : ℤ_[l] →+* ZMod (l ^ 1))`. Rewrite using `[RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, hz, sub_self]`. Rewrite `hk` using `[PadicInt.ker_toZModPow, Ideal.mem_span_singleton]`. Take `⟨y, hy⟩` from `hk`. Establish `h1 : f x - f ((z.val : ℕ) : ℤ_[l]) = 0`.

Rewrite using `[← map_sub, hy, map_mul, map_pow, map_natCast, CharP.cast_eq_zero, zero_pow one_ne_zero, zero_mul]`. Rewrite `h1` using `[sub_eq_zero, map_natCast]`. Rewrite using `[h1, ZMod.castHom_apply, ZMod.cast_eq_val]`.
-/
private theorem ringHom_padicInt_eq_castHom_toZModPow_one {l : ℕ} [Fact l.Prime] (k : Type) [Field k] [CharP k l] (f : ℤ_[l] →+* k) (h : l ∣ l ^ 1) (x : ℤ_[l]) :
    f x = ZMod.castHom h k (PadicInt.toZModPow 1 x) := by
  have hpos : 0 < l ^ 1 := by
    have := (Fact.out : l.Prime).pos
    positivity
  haveI : NeZero (l ^ 1) := ⟨hpos.ne'⟩
  set z := PadicInt.toZModPow 1 x with hz
  have hk : x - ((z.val : ℕ) : ℤ_[l]) ∈ RingHom.ker (PadicInt.toZModPow 1 : ℤ_[l] →+* ZMod (l ^ 1)) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, hz, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hk
  obtain ⟨y, hy⟩ := hk
  have h1 : f x - f ((z.val : ℕ) : ℤ_[l]) = 0 := by
    rw [← map_sub, hy, map_mul, map_pow, map_natCast, CharP.cast_eq_zero, zero_pow one_ne_zero, zero_mul]
  rw [sub_eq_zero, map_natCast] at h1
  rw [h1, ZMod.castHom_apply, ZMod.cast_eq_val]

/- English proof (translation)
Introduce `k _ _ a ha w`. Use `haveI : IsDiscreteValuationRing c.O := c.dvr`. Take `⟨g, -, hg⟩` from `hOk.g2 w`. Use `⟨g, fun heq => hg ?_⟩` and prove the remaining obligations. Rewrite using `[hG.om_bar]`.

Establish `e1 : ∀ y : c.O, Ideal.Quotient.lift (maximalIdeal c.O) a ha (residue c.O y) = a y` using `fun y => Ideal.Quotient.lift_mk _ _ _`. Establish `hinj : Function.Injective (Ideal.Quotient.lift (maximalIdeal c.O) a ha)`. Use `letI := Ideal.Quotient.field (maximalIdeal c.O)`. Conclude with `RingHom.injective _`. Apply `hinj` to reduce the goal to its premises.

Use `show Ideal.Quotient.lift (maximalIdeal c.O) a ha (residue c.O ↑(((T.fr ∅).rt w) g)) = Ideal.Quotient.lift (maximalIdeal c.O) a ha (residue c.O ↑(chiO ℚ Ω l c.O (resQ T.F g)))`. Rewrite using `[e1, e1, heq]`. Establish `h2` using `ringHom_padicInt_eq_castHom_toZModPow_one k (a.comp (algebraMap ℤ_[l] c.O)) (by simp) (cycZ ℚ Ω l (resQ T.F g) : ℤ_[l])`. Rewrite `h2` using `[RingHom.comp_apply]`. Conclude with `h2.symm`.
-/
private theorem exists_rt_ne_cycF_of_good_of_ok {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D) (hG : D.Good) (hOk : T.Ok) :
    ∀ (k : Type) [Field k] [CharP k l] (a : c.O →+* k), (∀ x ∈ maximalIdeal c.O, a x = 0) → ∀ w, ∃ g, a ((T.fr ∅).rt w g) ≠ (GC.cycF T.F Ω l k g : k) := by
  intro k _ _ a ha w
  haveI : IsDiscreteValuationRing c.O := c.dvr
  obtain ⟨g, -, hg⟩ := hOk.g2 w
  refine ⟨g, fun heq => hg ?_⟩
  rw [hG.om_bar]
  have e1 : ∀ y : c.O, Ideal.Quotient.lift (maximalIdeal c.O) a ha (residue c.O y) = a y :=
    fun y => Ideal.Quotient.lift_mk _ _ _
  have hinj : Function.Injective (Ideal.Quotient.lift (maximalIdeal c.O) a ha) := by
    letI := Ideal.Quotient.field (maximalIdeal c.O)
    exact RingHom.injective _
  apply hinj
  show Ideal.Quotient.lift (maximalIdeal c.O) a ha (residue c.O ↑(((T.fr ∅).rt w) g)) =
    Ideal.Quotient.lift (maximalIdeal c.O) a ha (residue c.O ↑(chiO ℚ Ω l c.O (resQ T.F g)))
  rw [e1, e1, heq]
  have h2 := ringHom_padicInt_eq_castHom_toZModPow_one k (a.comp (algebraMap ℤ_[l] c.O)) (by simp) (cycZ ℚ Ω l (resQ T.F g) : ℤ_[l])
  rw [RingHom.comp_apply] at h2
  exact h2.symm

/- English proof (translation)
Introduce `Ω _ _ _ l _ c D T hFit hDeep`. Establish `hG : D.Good`. Break down `hFit.2 with h | h` into its components or cases. Conclude with `h.1.1`. Conclude with `h.1.1`.

Conclude with `⟨nu_eq_one_of_mem_n_of_good_of_ok D T hG hFit.1, nu_eq_one_of_mem_mu_of_good_of_deep D T hG hDeep, mul_self_eq_one_and_nu_neg_one_of_isCC D T hG, exists_rt_ne_cycF_of_good_of_ok D T hG hFit.1⟩`.
-/
theorem UpperTheory.V.Ws.X1.thFacts :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → (∀ g ∈ (T.fr ∅).N, (T.fr ∅).ν g = 1) ∧ (∀ v, ∀ s ∈ (T.fr ∅).Mu v, (T.fr ∅).ν s = 1) ∧ (∀ g : G T.F Ω, IsCC g → g * g = 1 ∧ (T.fr ∅).ν g = -1) ∧ ∀ (k : Type) [Field k] [CharP k l] (a : c.O →+* k), (∀ x ∈ maximalIdeal c.O, a x = 0) → ∀ w, ∃ g, a ((T.fr ∅).rt w g) ≠ (GC.cycF T.F Ω l k g : k) := by
  intro Ω _ _ _ l _ c D T hFit hDeep
  have hG : D.Good := by
    rcases hFit.2 with h | h
    · exact h.1.1
    · exact h.1.1
  exact ⟨nu_eq_one_of_mem_n_of_good_of_ok D T hG hFit.1, nu_eq_one_of_mem_mu_of_good_of_deep D T hG hDeep, mul_self_eq_one_and_nu_neg_one_of_isCC D T hG,
    exists_rt_ne_cycF_of_good_of_ok D T hG hFit.1⟩
