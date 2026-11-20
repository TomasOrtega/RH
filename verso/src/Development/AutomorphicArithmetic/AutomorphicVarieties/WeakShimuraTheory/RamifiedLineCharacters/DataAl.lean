import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.MemRamLine

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

/- English proof (translation)
Introduce `O Γ R _ _ _ _ Φ a p hp hs`. Establish `h12 : ∀ g, p.r g 1 2 = 0` using `fun g => hs g 1 2 (by decide) (by decide)`. Establish `h13 : ∀ g, p.r g 1 3 = 0` using `fun g => hs g 1 3 (by decide) (by decide)`. Establish `hd` using `hp.res.diag`. Establish `hu : ∀ g, a (((Φ.χ 0 g)⁻¹ : Oˣ) : O) * a (Φ.χ 0 g) = 1` using `fun g => by`.

Rewrite using `[← map_mul, Units.inv_mul, map_one]`. Establish `hrt : ∀ g, a (Φ.rt (-wAl) g) = a (Φ.χ 1 g) * a (((Φ.χ 0 g)⁻¹ : Oˣ) : O)` using `fun g => by`. Rewrite using `[← map_mul, ← Units.val_mul]`. Use `congr 2`. Simplify using `[Fr.rt, wAl]`.

Establish `hlc : ∀ i j, IsLocallyConstant fun g => p.r g i j` using `fun i j => by`. Use `IsLocallyConstant.desc _ (Ideal.Quotient.mk ((⊥ : Ideal R) ^ 1)) (hp.cont i j 1) ?_` and prove the remaining obligations. Rewrite using `[RingHom.injective_iff_ker_eq_bot, Ideal.mk_ker, pow_one]`. Use `⟨fun g => p.r g 1 0 * a (((Φ.χ 0 g)⁻¹ : Oˣ) : O), ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `(hlc 1 0).mul ?_` and prove the remaining obligations.

Establish `e : (fun g => a (((Φ.χ 0 g)⁻¹ : Oˣ) : O)) = Ring.inverse ∘ fun g => p.r g 0 0`. Use function extensionality and compare the values at `g`. Simplify using `only [Function.comp, hd]`. Conclude with `(Ring.inverse_unit (Units.map (a : O →* R) (Φ.χ 0 g))).symm`. Rewrite using `[e]`.

Conclude with `(hlc 0 0).comp _`. Introduce `g h`. Establish `e : p.r (g * h) 1 0 = p.r g 1 0 * a (Φ.χ 0 h) + a (Φ.χ 1 g) * p.r h 1 0`. Rewrite using `[map_mul, Matrix.mul_apply, Fin.sum_univ_four, h12, h13, hd, hd]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e, hrt, map_mul, mul_inv, Units.val_mul, map_mul]`. Take the linear combination `(p.r g 1 0 * a (((Φ.χ 0 g)⁻¹ : Oˣ) : O)) * hu h`. Introduce `g hg`. Simplify using `[hp.pair.kill g hg]`. Establish `: p.r Φ.g0 1 0 = 0` using `hp.pair.nrm (by decide)`.

Simplify using `[this]`. Introduce `v s hsv`. Take `⟨l1, l2, l3⟩` from `hp.pair.low v`. Establish `hinv : p.n v * adj (p.n v) = 1`. Rewrite `l1` using `[IsGSp, one_smul]`.

Conclude with `mul_eq_one_comm.mp l1`. Establish `hU` using `hp.pair.flag v s hsv`. Establish `hc` using `hp.res.char v s hsv 0`. Unfold `PD.ψ at hc`. Establish `key : p.n v * (adj (p.n v) * p.r s * p.n v) = p.r s * p.n v`.

Rewrite using `[← mul_assoc, ← mul_assoc, hinv, one_mul]`. Generalize the expression as in `adj (p.n v) * p.r s * p.n v = U at hU hc key`. Establish `k` using `congrFun (congrFun key 1) 0`. Rewrite `k` using `[Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_four, hU 1 0 (by decide), hU 2 0 (by decide), hU 3 0 (by decide), hc, h12, h13, hd, l2, l2]`. Rewrite using `[hrt]`.

Use `beta_reduce`. Take the linear combination `(-a (((Φ.χ 0 s)⁻¹ : Oˣ) : O)) * k + p.n v 1 0 * hu s`. Introduce `g beta_reduce`. Rewrite using `[mul_assoc, hu, mul_one]`.
-/
theorem UpperTheory.V.Ws.Gys.dataAl :
    ∀ {O Γ R : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [CommRing R] (Φ : Fr O Γ) (a : O →+* R) (p : PD Φ.ι Γ R), Φ.IsRes a p → Supp nM p.r →
      ∃ x : Γ → R, Φ.Coc a (-wAl) x ∧ x Φ.g0 = 0 ∧ Φ.LocTriv a (-wAl) x (fun v => p.n v 1 0) ∧ ∀ g, p.r g 1 0 = x g * a (Φ.χ 0 g) := by
  intro O Γ R _ _ _ _ Φ a p hp hs
  have h12 : ∀ g, p.r g 1 2 = 0 := fun g => hs g 1 2 (by decide) (by decide)
  have h13 : ∀ g, p.r g 1 3 = 0 := fun g => hs g 1 3 (by decide) (by decide)
  have hd := hp.res.diag
  have hu : ∀ g, a (((Φ.χ 0 g)⁻¹ : Oˣ) : O) * a (Φ.χ 0 g) = 1 := fun g => by
    rw [← map_mul, Units.inv_mul, map_one]
  have hrt : ∀ g, a (Φ.rt (-wAl) g) = a (Φ.χ 1 g) * a (((Φ.χ 0 g)⁻¹ : Oˣ) : O) := fun g => by
    rw [← map_mul, ← Units.val_mul]
    congr 2
    simp [Fr.rt, wAl]
  have hlc : ∀ i j, IsLocallyConstant fun g => p.r g i j := fun i j => by
    refine IsLocallyConstant.desc _ (Ideal.Quotient.mk ((⊥ : Ideal R) ^ 1)) (hp.cont i j 1) ?_
    rw [RingHom.injective_iff_ker_eq_bot, Ideal.mk_ker, pow_one]
  refine ⟨fun g => p.r g 1 0 * a (((Φ.χ 0 g)⁻¹ : Oˣ) : O), ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · refine (hlc 1 0).mul ?_
    have e : (fun g => a (((Φ.χ 0 g)⁻¹ : Oˣ) : O)) = Ring.inverse ∘ fun g => p.r g 0 0 := by
      funext g
      simp only [Function.comp, hd]
      exact (Ring.inverse_unit (Units.map (a : O →* R) (Φ.χ 0 g))).symm
    rw [e]
    exact (hlc 0 0).comp _
  · intro g h
    have e : p.r (g * h) 1 0 = p.r g 1 0 * a (Φ.χ 0 h) + a (Φ.χ 1 g) * p.r h 1 0 := by
      rw [map_mul, Matrix.mul_apply, Fin.sum_univ_four, h12, h13, hd, hd]; ring
    rw [e, hrt, map_mul, mul_inv, Units.val_mul, map_mul]
    linear_combination (p.r g 1 0 * a (((Φ.χ 0 g)⁻¹ : Oˣ) : O)) * hu h
  · intro g hg
    simp [hp.pair.kill g hg]
  · have : p.r Φ.g0 1 0 = 0 := hp.pair.nrm (by decide)
    simp [this]
  · intro v s hsv
    obtain ⟨l1, l2, l3⟩ := hp.pair.low v
    have hinv : p.n v * adj (p.n v) = 1 := by
      rw [IsGSp, one_smul] at l1
      exact mul_eq_one_comm.mp l1
    have hU := hp.pair.flag v s hsv
    have hc := hp.res.char v s hsv 0
    unfold PD.ψ at hc
    have key : p.n v * (adj (p.n v) * p.r s * p.n v) = p.r s * p.n v := by
      rw [← mul_assoc, ← mul_assoc, hinv, one_mul]
    generalize adj (p.n v) * p.r s * p.n v = U at hU hc key
    have k := congrFun (congrFun key 1) 0
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_four, hU 1 0 (by decide), hU 2 0 (by decide),
      hU 3 0 (by decide), hc, h12, h13, hd, l2, l2] at k
    rw [hrt]
    beta_reduce
    linear_combination (-a (((Φ.χ 0 s)⁻¹ : Oˣ) : O)) * k + p.n v 1 0 * hu s
  · intro g
    beta_reduce
    rw [mul_assoc, hu, mul_one]
