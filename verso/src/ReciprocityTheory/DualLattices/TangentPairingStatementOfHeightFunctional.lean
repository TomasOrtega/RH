import ReciprocityTheory.DualLattices.TotalFibreMapTotalFibreNsmulSnd

noncomputable section

open TensorProduct

namespace ReciprocityTheory.PGsh

universe u

variable {R₀ : Type u} [CommRing R₀]

namespace BX

variable (B : BX R₀)

/- English proof (translation)
Introduce `R' R π ξ Dp N hsurj hker hsq _ hN sh th Vs Vt hs ht zh z hsV htV hhs hht hpair hz`. Establish `hπ : π.SqZero` using `π.sqZero_of_span ξ hsurj hker hsq`. Take `⟨O, hOsw, hO⟩` from `B.step1 π Dp ξ hsurj hker hsq hB2 N hN`. Take `⟨hsN, htN, u0, l1, l2, h1, h2, hz'⟩` from `hpair`. Take `⟨l⟩` from `B.nonempty R' sh th`.

Take `⟨μ, hμ⟩` from `B.exists_smul (B.pmap π l) u0`. Take `⟨μ', hμ'⟩` from `π.exists_unit_lift hsurj μ`. Take `⟨a1, ha1⟩` from `π.exists_unit_lift hsurj l1`. Take `⟨a2, ha2⟩` from `π.exists_unit_lift hsurj l2`. Take `⟨l', hl⟩ : ∃ l' : B.P R' sh th, B.pmap π l' = u0` from `⟨B.smul μ' l, by rw [B.pmap_smul, hμ', hμ]⟩`.

Establish `htg0 : ∀ V, B.map π (B.tg π hπ V) = 0` using `fun V => (B.tg_ker π hπ _).2 ⟨V, rfl⟩`. Establish `hinv1 : Units.map (π.1 : (R' : Type u) →* (R : Type u)) a1⁻¹ * l1 = 1`. Rewrite using `[map_inv, ha1, inv_mul_cancel]`. Establish `hinv2 : Units.map (π.1 : (R' : Type u) →* (R : Type u)) a2⁻¹ * l2 = 1`. Rewrite using `[map_inv, ha2, inv_mul_cancel]`.

Establish `hu : HEq (B.pmap π (B.smul a1⁻¹ (B.tr1 hsV (B.nsmul1 l' N)))) (B.zero1 (B.map π th))`. Rewrite using `[B.pmap_smul]`. Establish `e : HEq (B.pmap π (B.tr1 hsV (B.nsmul1 l' N))) (B.smul l1 (B.zero1 (B.map π th)))`. Use `(B.pmap_hcongr π hsV.symm rfl (B.castFst_heq hsV _)).trans ?_` and prove the remaining obligations. Use `(B.pmap_nsmul1 π _ N).trans ?_` and prove the remaining obligations.

Rewrite using `[hl, ← h1]`. Conclude with `(B.castFst_heq hsN _).symm`. Use `(B.smul_hcongr (htg0 Vs) rfl _ e).trans ?_` and prove the remaining obligations. Rewrite using `[← B.mul_smul, hinv1, B.one_smul]`. Establish `hu'0 : HEq (B.pmap π (B.smul a2⁻¹ (B.tr2 htV (B.nsmul2 l' N)))) (B.zero2 (B.map π sh))`.

Rewrite using `[B.pmap_smul]`. Establish `e : HEq (B.pmap π (B.tr2 htV (B.nsmul2 l' N))) (B.smul l2 (B.zero2 (B.map π sh)))`. Use `(B.pmap_hcongr π rfl htV.symm (B.castSnd_heq htV _)).trans ?_` and prove the remaining obligations. Use `(B.pmap_nsmul2 π _ N).trans ?_` and prove the remaining obligations. Rewrite using `[hl, ← h2]`.

Conclude with `(B.castSnd_heq htN _).symm`. Use `(B.smul_hcongr rfl (htg0 Vt) _ e).trans ?_` and prove the remaining obligations. Rewrite using `[← B.mul_smul, hinv2, B.one_smul]`. Establish `hu' : HEq (B.pmap π (B.sw (B.smul a2⁻¹ (B.tr2 htV (B.nsmul2 l' N))))) (B.zero1 (B.map π sh))`. Rewrite using `[← B.sw_nat]`.

Use `(B.sw_hcongr rfl (htg0 Vt) hu'0).trans ?_` and prove the remaining obligations. Rewrite using `[B.sw_zero2]`. Take `⟨ct, hct, hNt⟩` from `hO Vs Vt th ht htV hht _ hu`. Take `⟨cs, hcs, hNs⟩` from `hO Vt Vs sh hs hsV hhs _ hu'`. Establish `k1 : HEq (B.smul (a1⁻¹ ^ N) (B.nsmul2 (B.nsmul1 l' N) N)) (B.smul ct (O Vs Vt))`.

Use `HEq.trans ?_ ((B.castSnd_heq htV _).symm.trans (heq_of_eq hNt))` and prove the remaining obligations. Rewrite using `[B.nsmul2_smul]`. Conclude with `B.smul_hcongr hsV rfl _ (B.nsmul2_hcongr hsV rfl N (B.castFst_heq hsV _).symm)`. Establish `k2 : HEq (B.smul (a2⁻¹ ^ N) (B.nsmul2 (B.nsmul1 l' N) N)) (B.smul cs (O Vs Vt))`. Establish `s1 : HEq (B.sw (B.nsmul1 (B.smul a2⁻¹ (B.tr2 htV (B.nsmul2 l' N))) N)) (B.smul cs (O Vt Vs))`.

Rewrite using `[B.sw_nsmul1]`. Conclude with `(B.castSnd_heq hsV _).symm.trans (heq_of_eq hNs)`. Establish `s2` using `B.sw_hcongr rfl hsV s1`. Rewrite `s2` using `[B.sw_sw, B.sw_smul, hOsw]`. Use `HEq.trans ?_ s2` and prove the remaining obligations.

Rewrite using `[B.nsmul1_smul, B.nsmul_comm]`. Conclude with `B.smul_hcongr rfl htV _ (B.nsmul1_hcongr rfl htV N (B.castSnd_heq htV _).symm)`. Take `⟨X₀, hX₀⟩` from `B.exists_cast hsV htV (B.nsmul2 (B.nsmul1 l' N) N)`. Establish `e1 : B.smul (a1⁻¹ ^ N) X₀ = B.smul ct (O Vs Vt)` using `eq_of_heq ((B.smul_hcongr hsV.symm htV.symm _ hX₀).trans k1)`. Establish `e2 : B.smul (a2⁻¹ ^ N) X₀ = B.smul cs (O Vs Vt)` using `eq_of_heq ((B.smul_hcongr hsV.symm htV.symm _ hX₀).trans k2)`.

Establish `hX1 : X₀ = B.smul (a1 ^ N * ct) (O Vs Vt)`. Rewrite using `[B.mul_smul, ← e1, ← B.mul_smul, ← mul_pow, mul_inv_cancel, one_pow, B.one_smul]`. Establish `hX2 : X₀ = B.smul (a2 ^ N * cs) (O Vs Vt)`. Rewrite using `[B.mul_smul, ← e2, ← B.mul_smul, ← mul_pow, mul_inv_cancel, one_pow, B.one_smul]`. Establish `key : a1 ^ N * ct = a2 ^ N * cs` using `B.smul_inj (hX1.symm.trans hX2)`.

Establish `hν : Units.map (π.1 : (R' : Type u) →* (R : Type u)) (zh * a2 * a1⁻¹) = 1`. Rewrite using `[map_mul, map_mul, map_inv, hz, ha1, ha2, hz', div_mul_cancel, mul_inv_cancel]`. Establish `hνN` using `LHom.pow_eq_one hπ hN (zh * a2 * a1⁻¹) (by have := congrArg Units.val hν; simpa using this)`. Establish `hz1 : zh ^ N * a2 ^ N = a1 ^ N`. Rewrite `hνN` using `[mul_pow, mul_pow, inv_pow]`.

Conclude with `mul_inv_eq_one.1 hνN`. Establish `hz2 : zh ^ N * ct = cs`. Establish `h3 : a2 ^ N * (zh ^ N * ct) = a2 ^ N * cs`. Rewrite using `[← key, ← hz1]`. The two sides agree by associativity and commutativity.

Conclude with `mul_left_cancel h3`. Establish `hA : π.1 (B.evK π ht Vs) = 0` using `(RingHom.mem_ker).1 (evalT_mem ht (RingHom.ker π.1) Vs)`. Establish `hB : π.1 (B.evK π hs Vt) = 0` using `(RingHom.mem_ker).1 (evalT_mem hs (RingHom.ker π.1) Vt)`. Establish `hAA` using `LHom.mul_eq_zero hπ hA hA`. Establish `hAB` using `LHom.mul_eq_zero hπ hA hB`.

Establish `h4` using `congrArg Units.val hz2`. Rewrite `h4` using `[Units.val_mul, Units.val_pow_eq_pow_val, hct, hcs]`. Take the linear combination `(1 + B.evK π ht Vs) * h4 + (zh : (R' : Type u)) ^ N * hAA - hAB`.
-/
theorem tangentPairingStatement_of_heightFunctional (hB2 : HighestWeightVectorUniformBounds B) : TangentPairingStatement B := by
  intro R' R π ξ Dp N hsurj hker hsq _ hN sh th Vs Vt hs ht zh z hsV htV hhs hht hpair hz
  have hπ : π.SqZero := π.sqZero_of_span ξ hsurj hker hsq
  obtain ⟨O, hOsw, hO⟩ := B.step1 π Dp ξ hsurj hker hsq hB2 N hN
  obtain ⟨hsN, htN, u0, l1, l2, h1, h2, hz'⟩ := hpair
  obtain ⟨l⟩ := B.nonempty R' sh th
  obtain ⟨μ, hμ⟩ := B.exists_smul (B.pmap π l) u0
  obtain ⟨μ', hμ'⟩ := π.exists_unit_lift hsurj μ
  obtain ⟨a1, ha1⟩ := π.exists_unit_lift hsurj l1
  obtain ⟨a2, ha2⟩ := π.exists_unit_lift hsurj l2
  obtain ⟨l', hl⟩ : ∃ l' : B.P R' sh th, B.pmap π l' = u0 :=
    ⟨B.smul μ' l, by rw [B.pmap_smul, hμ', hμ]⟩
  have htg0 : ∀ V, B.map π (B.tg π hπ V) = 0 := fun V => (B.tg_ker π hπ _).2 ⟨V, rfl⟩
  have hinv1 : Units.map (π.1 : (R' : Type u) →* (R : Type u)) a1⁻¹ * l1 = 1 := by
    rw [map_inv, ha1, inv_mul_cancel]
  have hinv2 : Units.map (π.1 : (R' : Type u) →* (R : Type u)) a2⁻¹ * l2 = 1 := by
    rw [map_inv, ha2, inv_mul_cancel]

  have hu : HEq (B.pmap π (B.smul a1⁻¹ (B.tr1 hsV (B.nsmul1 l' N))))
      (B.zero1 (B.map π th)) := by
    rw [B.pmap_smul]
    have e : HEq (B.pmap π (B.tr1 hsV (B.nsmul1 l' N))) (B.smul l1 (B.zero1 (B.map π th))) := by
      refine (B.pmap_hcongr π hsV.symm rfl (B.castFst_heq hsV _)).trans ?_
      refine (B.pmap_nsmul1 π _ N).trans ?_
      rw [hl, ← h1]
      exact (B.castFst_heq hsN _).symm
    refine (B.smul_hcongr (htg0 Vs) rfl _ e).trans ?_
    rw [← B.mul_smul, hinv1, B.one_smul]
  have hu'0 : HEq (B.pmap π (B.smul a2⁻¹ (B.tr2 htV (B.nsmul2 l' N))))
      (B.zero2 (B.map π sh)) := by
    rw [B.pmap_smul]
    have e : HEq (B.pmap π (B.tr2 htV (B.nsmul2 l' N))) (B.smul l2 (B.zero2 (B.map π sh))) := by
      refine (B.pmap_hcongr π rfl htV.symm (B.castSnd_heq htV _)).trans ?_
      refine (B.pmap_nsmul2 π _ N).trans ?_
      rw [hl, ← h2]
      exact (B.castSnd_heq htN _).symm
    refine (B.smul_hcongr rfl (htg0 Vt) _ e).trans ?_
    rw [← B.mul_smul, hinv2, B.one_smul]
  have hu' : HEq (B.pmap π (B.sw (B.smul a2⁻¹ (B.tr2 htV (B.nsmul2 l' N)))))
      (B.zero1 (B.map π sh)) := by
    rw [← B.sw_nat]
    refine (B.sw_hcongr rfl (htg0 Vt) hu'0).trans ?_
    rw [B.sw_zero2]
  obtain ⟨ct, hct, hNt⟩ := hO Vs Vt th ht htV hht _ hu
  obtain ⟨cs, hcs, hNs⟩ := hO Vt Vs sh hs hsV hhs _ hu'

  have k1 : HEq (B.smul (a1⁻¹ ^ N) (B.nsmul2 (B.nsmul1 l' N) N)) (B.smul ct (O Vs Vt)) := by
    refine HEq.trans ?_ ((B.castSnd_heq htV _).symm.trans (heq_of_eq hNt))
    rw [B.nsmul2_smul]
    exact B.smul_hcongr hsV rfl _ (B.nsmul2_hcongr hsV rfl N (B.castFst_heq hsV _).symm)
  have k2 : HEq (B.smul (a2⁻¹ ^ N) (B.nsmul2 (B.nsmul1 l' N) N)) (B.smul cs (O Vs Vt)) := by
    have s1 : HEq (B.sw (B.nsmul1 (B.smul a2⁻¹ (B.tr2 htV (B.nsmul2 l' N))) N))
        (B.smul cs (O Vt Vs)) := by
      rw [B.sw_nsmul1]; exact (B.castSnd_heq hsV _).symm.trans (heq_of_eq hNs)
    have s2 := B.sw_hcongr rfl hsV s1
    rw [B.sw_sw, B.sw_smul, hOsw] at s2
    refine HEq.trans ?_ s2
    rw [B.nsmul1_smul, B.nsmul_comm]
    exact B.smul_hcongr rfl htV _ (B.nsmul1_hcongr rfl htV N (B.castSnd_heq htV _).symm)
  obtain ⟨X₀, hX₀⟩ := B.exists_cast hsV htV (B.nsmul2 (B.nsmul1 l' N) N)
  have e1 : B.smul (a1⁻¹ ^ N) X₀ = B.smul ct (O Vs Vt) :=
    eq_of_heq ((B.smul_hcongr hsV.symm htV.symm _ hX₀).trans k1)
  have e2 : B.smul (a2⁻¹ ^ N) X₀ = B.smul cs (O Vs Vt) :=
    eq_of_heq ((B.smul_hcongr hsV.symm htV.symm _ hX₀).trans k2)
  have hX1 : X₀ = B.smul (a1 ^ N * ct) (O Vs Vt) := by
    rw [B.mul_smul, ← e1, ← B.mul_smul, ← mul_pow, mul_inv_cancel, one_pow, B.one_smul]
  have hX2 : X₀ = B.smul (a2 ^ N * cs) (O Vs Vt) := by
    rw [B.mul_smul, ← e2, ← B.mul_smul, ← mul_pow, mul_inv_cancel, one_pow, B.one_smul]
  have key : a1 ^ N * ct = a2 ^ N * cs := B.smul_inj (hX1.symm.trans hX2)

  have hν : Units.map (π.1 : (R' : Type u) →* (R : Type u)) (zh * a2 * a1⁻¹) = 1 := by
    rw [map_mul, map_mul, map_inv, hz, ha1, ha2, hz', div_mul_cancel, mul_inv_cancel]
  have hνN := LHom.pow_eq_one hπ hN (zh * a2 * a1⁻¹)
    (by have := congrArg Units.val hν; simpa using this)
  have hz1 : zh ^ N * a2 ^ N = a1 ^ N := by
    rw [mul_pow, mul_pow, inv_pow] at hνN
    exact mul_inv_eq_one.1 hνN
  have hz2 : zh ^ N * ct = cs := by
    have h3 : a2 ^ N * (zh ^ N * ct) = a2 ^ N * cs := by
      rw [← key, ← hz1]; ac_rfl
    exact mul_left_cancel h3
  have hA : π.1 (B.evK π ht Vs) = 0 := (RingHom.mem_ker).1 (evalT_mem ht (RingHom.ker π.1) Vs)
  have hB : π.1 (B.evK π hs Vt) = 0 := (RingHom.mem_ker).1 (evalT_mem hs (RingHom.ker π.1) Vt)
  have hAA := LHom.mul_eq_zero hπ hA hA
  have hAB := LHom.mul_eq_zero hπ hA hB
  have h4 := congrArg Units.val hz2
  rw [Units.val_mul, Units.val_pow_eq_pow_val, hct, hcs] at h4
  linear_combination (1 + B.evK π ht Vs) * h4 + (zh : (R' : Type u)) ^ N * hAA - hAB

end BX

end ReciprocityTheory.PGsh
