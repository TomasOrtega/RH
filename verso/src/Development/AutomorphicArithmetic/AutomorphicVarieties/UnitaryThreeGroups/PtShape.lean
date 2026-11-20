import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Rigid0
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsCoordOfNotMatIrr
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.FreeEtaleSheafZmodExistsHomSendingGenerator
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ZetaReducibleRepEqSubInvAndIsUnit

open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV

/- English proof (translation)
Simplify using `only [zmat, Matrix.sub_apply, MonoidHom.comp_apply, GG.map_mat, Matrix.map_apply, map_sub]`.
-/
private theorem zmat_map {G R S : Type} [Group G] [CommRing R] [CommRing S] (f : R →+* S) (c g₁ : G)
    (r : G →* GG 3 R) (i j : Fin 3) : zmat c g₁ ((GG.map f).comp r) i j = f (zmat c g₁ r i j) := by
  simp only [zmat, Matrix.sub_apply, MonoidHom.comp_apply, GG.map_mat, Matrix.map_apply, map_sub]

/- English proof (translation)
Rewrite using `[MonoidHom.comp_apply, GG.map_mat, h.atc]`. Conclude with `Matrix.map_one _ (map_zero f) (map_one f)`. Use `z12 := by rw [zmat_map, h.z12, map_zero]`. Use `z21 := by rw [zmat_map, h.z21, map_zero]`.
-/
private theorem normalised_map {G R S : Type} [Group G] [CommRing R] [CommRing S] (f : R →+* S) {c g₁ : G}
    {r : G →* GG 3 R} (h : Normalised c g₁ r) : Normalised c g₁ ((GG.map f).comp r) where
  atc := by
    rw [MonoidHom.comp_apply, GG.map_mat, h.atc]
    exact Matrix.map_one _ (map_zero f) (map_one f)
  z12 := by rw [zmat_map, h.z12, map_zero]
  z21 := by rw [zmat_map, h.z21, map_zero]

/- English proof (translation)
Use extensionality with `g : 1`. Use `SemidirectProduct.ext ?_ ?_` and prove the remaining obligations. Use extensionality with `i j`. Simplify using `[r0, GG.map, tor_val, Matrix.diagonal_apply]`. Use `split_ifs`.

Simplify using `only [← map_zpow, ← map_pow, Units.coe_map]`. Both sides reduce to the same expression. Conclude with `map_zero f`. Simplify using `[r0, GG.map]`.
-/
private theorem map_reducible_three_dim {G R S : Type} [Group G] [CommRing R] [CommRing S] (f : R →+* S) (η : G →* ℤˣ)
    (Ψ : G →* Rˣ) : (GG.map f).comp (r0 η Ψ) = r0 η ((Units.map f.toMonoidHom).comp Ψ) := by
  ext g : 1
  refine SemidirectProduct.ext ?_ ?_
  · ext i j
    simp [r0, GG.map, tor_val, Matrix.diagonal_apply]
    split_ifs
    · simp only [← map_zpow, ← map_pow, Units.coe_map]
      rfl
    · exact map_zero f
  · simp [r0, GG.map]

/- English proof (translation)
Rewrite using `[← res_eq_zero_iff O R, map_sub, sub_eq_zero]`. Establish `h1 : (res O R) (zeta c g₁ r.hom) = zeta c g₁ ((GG.map (res O R : R →+* ResidueField O)).comp r.hom)` using `(zmat_map (res O R : R →+* ResidueField O) c g₁ r.hom 0 0).symm`. Establish `h2 : (GG.map (res O R : R →+* ResidueField O)).comp r.hom = r0 η (barChar O Ψ)` using `by ext1 g`. Conclude with `r.red g`. Establish `h3 : r0 η (barChar O Ψ) = (GG.map (residue O)).comp (r0 η Ψ)`.

Rewrite using `[map_reducible_three_dim]`. Both sides reduce to the same expression. Rewrite using `[h1, h2, h3]`. Use `show zmat c g₁ ((GG.map (residue O)).comp (r0 η Ψ)) 0 0 = _`. Rewrite using `[zmat_map]`.

Simplify using `[zeta]`.
-/
private theorem zeta_sub_mem {O Γ R : Type} [CommRing O] [IsLocalRing O] [Group Γ] [TopologicalSpace Γ]
    {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ} [CommRing R] [Algebra O R] [IsCO O R] (r : GLift O η Ψ R) (c g₁ : Γ) :
    zeta c g₁ r.hom - algebraMap O R (zeta c g₁ (r0 η Ψ)) ∈ maximalIdeal R := by
  rw [← res_eq_zero_iff O R, map_sub, sub_eq_zero]
  have h1 : (res O R) (zeta c g₁ r.hom) =
      zeta c g₁ ((GG.map (res O R : R →+* ResidueField O)).comp r.hom) :=
    (zmat_map (res O R : R →+* ResidueField O) c g₁ r.hom 0 0).symm
  have h2 : (GG.map (res O R : R →+* ResidueField O)).comp r.hom = r0 η (barChar O Ψ) := by
    ext1 g
    exact r.red g
  have h3 : r0 η (barChar O Ψ) = (GG.map (residue O)).comp (r0 η Ψ) := by
    rw [map_reducible_three_dim]
    rfl
  rw [h1, h2, h3]
  show zmat c g₁ ((GG.map (residue O)).comp (r0 η Ψ)) 0 0 = _
  rw [zmat_map]
  simp [zeta]

/- English proof (translation)
Use `haveI := c.fin`. Establish `hint : IsIntegral ℤ_[l] (x : PadicAlgCl l)`. Establish `hx : IsIntegral ℤ_[l] x` using `Algebra.IsIntegral.isIntegral x`. Conclude with `hx.map c.O.val`. Take `⟨p, hmon, hp⟩` from `hint`.

Assume the negation of the conclusion as `hgt`. Use `push_neg at hgt`. Rewrite `hp` using `[hmon.as_sum, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finset_sum]`. Establish `hcoef : ∀ i ∈ Finset.range p.natDegree, ‖Polynomial.eval₂ (algebraMap ℤ_[l] (PadicAlgCl l)) (x : PadicAlgCl l) (Polynomial.C (p.coeff i) * Polynomial.X ^ i)‖ ≤ ‖(x : PadicAlgCl l)‖ ^ i`. Introduce `i _`.

Rewrite using `[Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, norm_mul, norm_pow]`. Establish `hc : ‖algebraMap ℤ_[l] (PadicAlgCl l) (p.coeff i)‖ ≤ 1`. Rewrite using `[IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), PadicAlgCl.norm_extends]`. Conclude with `PadicInt.norm_le_one _`. Combine the equalities or inequalities in the displayed calculation.

Establish `hlt : ‖∑ i ∈ Finset.range p.natDegree, Polynomial.eval₂ (algebraMap ℤ_[l] (PadicAlgCl l)) (x : PadicAlgCl l) (Polynomial.C (p.coeff i) * Polynomial.X ^ i)‖ < ‖(x : PadicAlgCl l)‖ ^ p.natDegree`. Break down `Nat.eq_zero_or_pos p.natDegree with hn | hn` into its components or cases. Rewrite using `[hn]`. Simplify using the standard rewrite rules. Take `⟨i, hi, hle⟩` from `IsUltrametricDist.exists_norm_finset_sum_le_of_nonempty (Finset.nonempty_range_iff.mpr hn.ne') (fun i => Polynomial.eval₂ (algebraMap ℤ_[l] (PadicAlgCl l)) (x : PadicAlgCl l) (Polynomial.C (p.coeff i) * Polynomial.X ^ i))`.

Conclude with `lt_of_le_of_lt (hle.trans (hcoef i hi)) (pow_lt_pow_right₀ hgt (Finset.mem_range.mp hi))`. Establish `heq` using `eq_neg_of_add_eq_zero_left hp`. Establish `hn` using `congrArg norm heq`. Rewrite `hn` using `[norm_neg, norm_pow]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem norm_coe_coefO_le_one {l : ℕ} [Fact l.Prime] (c : Coef l) (x : c.O) :
    ‖(x : PadicAlgCl l)‖ ≤ 1 := by
  haveI := c.fin
  have hint : IsIntegral ℤ_[l] (x : PadicAlgCl l) := by
    have hx : IsIntegral ℤ_[l] x := Algebra.IsIntegral.isIntegral x
    exact hx.map c.O.val
  obtain ⟨p, hmon, hp⟩ := hint
  by_contra hgt
  push_neg at hgt
  rw [hmon.as_sum, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finset_sum] at hp
  have hcoef : ∀ i ∈ Finset.range p.natDegree,
      ‖Polynomial.eval₂ (algebraMap ℤ_[l] (PadicAlgCl l)) (x : PadicAlgCl l)
        (Polynomial.C (p.coeff i) * Polynomial.X ^ i)‖ ≤ ‖(x : PadicAlgCl l)‖ ^ i := by
    intro i _
    rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, norm_mul, norm_pow]
    have hc : ‖algebraMap ℤ_[l] (PadicAlgCl l) (p.coeff i)‖ ≤ 1 := by
      rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), PadicAlgCl.norm_extends]
      exact PadicInt.norm_le_one _
    calc _ ≤ 1 * ‖(x : PadicAlgCl l)‖ ^ i := by gcongr
      _ = _ := one_mul _
  have hlt : ‖∑ i ∈ Finset.range p.natDegree, Polynomial.eval₂ (algebraMap ℤ_[l] (PadicAlgCl l))
      (x : PadicAlgCl l) (Polynomial.C (p.coeff i) * Polynomial.X ^ i)‖ <
      ‖(x : PadicAlgCl l)‖ ^ p.natDegree := by
    rcases Nat.eq_zero_or_pos p.natDegree with hn | hn
    · rw [hn]
      simp
    · obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finset_sum_le_of_nonempty
        (Finset.nonempty_range_iff.mpr hn.ne') (fun i => Polynomial.eval₂
          (algebraMap ℤ_[l] (PadicAlgCl l)) (x : PadicAlgCl l) (Polynomial.C (p.coeff i) * Polynomial.X ^ i))
      exact lt_of_le_of_lt (hle.trans (hcoef i hi)) (pow_lt_pow_right₀ hgt (Finset.mem_range.mp hi))
  have heq := eq_neg_of_add_eq_zero_left hp
  have hn := congrArg norm heq
  rw [norm_neg, norm_pow] at hn
  linarith

/- English proof (translation)
Introduce `l _ c Γ H _ _ _ _ _ _ η Ψ N ι hι U I cc g₁ S hl2 hmk f htwo`. Establish `hid : (GLift.map (AlgHom.id c.O S.R) S.r).hom = S.r.hom`. Use extensionality with `g : 1`. Use `SemidirectProduct.ext ?_ ?_` and prove the remaining obligations. Use extensionality with `i j`.

Simplify using `[GLift.map, GG.map]`. Simplify using `[GLift.map, GG.map]`. Establish `hN : Normalised cc g₁ S.r.hom`. Establish `h` using `((S.rep S.R).1 (AlgHom.id c.O S.R)).1`. Rewrite `h` using `[hid]`. Then use the resulting hypothesis.

Establish `hmult : ∀ g : S.R →ₐ[c.O] PadicAlgCl l, HasMult η (push g S.r.hom)`. Introduce `g x`. Simplify `S.r.hasMult x` using `[push, GG.map]`. Establish `hnorm_g : ∀ g : S.R →ₐ[c.O] PadicAlgCl l, Normalised cc g₁ (push g S.r.hom)` using `fun g => normalised_map (g : S.R →+* PadicAlgCl l) hN`. Establish `hzeta_g : ∀ g : S.R →ₐ[c.O] PadicAlgCl l, zeta cc g₁ (push g S.r.hom) = g (zeta cc g₁ S.r.hom)` using `fun g => zmat_map (g : S.R →+* PadicAlgCl l) cc g₁ S.r.hom 0 0`.

Take `⟨_, hz0u⟩` from `zeta_reducible_rep_eq_sub_inv_and_isUnit η Ψ cc g₁ hmk`. Establish `hmem` using `zeta_sub_mem S.r cc g₁`. Establish `ha : ‖algebraMap c.O (PadicAlgCl l) (zeta cc g₁ (r0 η Ψ))‖ = 1`. Take `⟨u, hu⟩` from `hz0u`. Establish `h1` using `norm_coe_coefO_le_one c (zeta cc g₁ (r0 η Ψ))`.

Establish `h2` using `norm_coe_coefO_le_one c (↑u⁻¹ : c.O)`. Establish `hprod : algebraMap c.O (PadicAlgCl l) (zeta cc g₁ (r0 η Ψ)) * algebraMap c.O (PadicAlgCl l) (↑u⁻¹ : c.O) = 1`. Rewrite using `[← map_mul, ← hu, Units.mul_inv, map_one]`. Establish `hn` using `congrArg norm hprod`. Rewrite `hn` using `[norm_mul, norm_one]`.

Express the relevant statement in the definitionally equal form `‖((zeta cc g₁ (r0 η Ψ) : c.O) : PadicAlgCl l)‖ * ‖((↑u⁻¹ : c.O) : PadicAlgCl l)‖ = 1 at hn`. Express the relevant statement in the definitionally equal form `‖((zeta cc g₁ (r0 η Ψ) : c.O) : PadicAlgCl l)‖ = 1`. Establish `key` using `mul_le_mul_of_nonneg_left h2 (norm_nonneg ((zeta cc g₁ (r0 η Ψ) : c.O) : PadicAlgCl l))`. Rewrite `key` using `[mul_one]`. Conclude with `le_antisymm h1 (by linarith)`.

Establish `hdec : ∀ g : S.R →ₐ[c.O] PadicAlgCl l, IsLocPt g → ‖zeta cc g₁ (push g S.r.hom) - algebraMap c.O (PadicAlgCl l) (zeta cc g₁ (r0 η Ψ))‖ < 1`. Introduce `g hg`. Rewrite using `[hzeta_g, ← AlgHom.commutes g, ← map_sub]`. Conclude with `hg _ hmem`. Establish `hne0 : ∀ g : S.R →ₐ[c.O] PadicAlgCl l, IsLocPt g → zeta cc g₁ (push g S.r.hom) ≠ 0`.

Introduce `g hg h0`. Establish `h` using `hdec g hg`. Rewrite `h` using `[h0, zero_sub, norm_neg, ha]`. Conclude with `lt_irrefl _ h`. Establish `h2 : ‖(2 : PadicAlgCl l)‖ = 1`.

Establish `h2e : (2 : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) ((2 : ℕ) : ℚ_[l])`. Rewrite using `[Nat.cast_ofNat, map_ofNat]`. Rewrite using `[h2e, PadicAlgCl.norm_extends, Padic.norm_natCast_eq_one_iff]`. Conclude with `(Nat.coprime_primes (Fact.out) Nat.prime_two).mpr hl2`. Establish `hnn : ∀ g g' : S.R →ₐ[c.O] PadicAlgCl l, IsLocPt g → IsLocPt g' → zeta cc g₁ (push g' S.r.hom) ≠ -zeta cc g₁ (push g S.r.hom)`.

Introduce `g g' hg hg' heq`. Establish `e1` using `hdec g hg`. Establish `e2` using `hdec g' hg'`. Establish `hsum : (2 : PadicAlgCl l) * algebraMap c.O (PadicAlgCl l) (zeta cc g₁ (r0 η Ψ)) = -((zeta cc g₁ (push g S.r.hom) - algebraMap c.O (PadicAlgCl l) (zeta cc g₁ (r0 η Ψ))) + (zeta cc g₁ (push g' S.r.hom) - algebraMap c.O (PadicAlgCl l) (zeta cc g₁ (r0 η Ψ))))`. Rewrite using `[heq]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hle` using `IsUltrametricDist.norm_add_le_max (zeta cc g₁ (push g S.r.hom) - algebraMap c.O (PadicAlgCl l) (zeta cc g₁ (r0 η Ψ))) (zeta cc g₁ (push g' S.r.hom) - algebraMap c.O (PadicAlgCl l) (zeta cc g₁ (r0 η Ψ)))`. Establish `hn` using `congrArg norm hsum`. Rewrite `hn` using `[norm_neg, norm_mul, h2, ha, one_mul]`. Establish `hm` using `max_lt e1 e2`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hf` using `htwo.1`. Establish `hcases` using `shape_cases η (push f S.r.hom) cc g₁ two_ne_zero (hmult f) hmk.ηc hmk.ηg (hnorm_g f) (hne0 f hf)`. Establish `htype : TypeI η (push f S.r.hom) ∨ TypeII η (push f S.r.hom)`. Break down `hcases with h | h | h | h` into its components or cases.

Conclude with `Or.inl h`. Conclude with `absurd h htwo.2.1`. Conclude with `absurd h htwo.2.2`. Conclude with `Or.inr h`. Use `⟨htype, ?_⟩` and prove the remaining obligations.

Introduce `f' hf' hiso`. Conclude with `conjBy_tor_of_iso η (push f S.r.hom) (push f' S.r.hom) cc g₁ two_ne_zero (hmult f) (hmult f') hmk.ηc hmk.ηg (hnorm_g f) (hnorm_g f') (hne0 f hf) (hne0 f' hf') (hnn f f' hf hf') htype hiso`.
-/
theorem UpperTheory.V.U3.twoPt_shape :
    ∀ {l : ℕ} [Fact l.Prime] {c : Coef l} {Γ H : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
      {η : Γ →* ℤˣ} {Ψ : Γ →* (c.O)ˣ} {N : Set Γ} {ι : H →* Γ} {hι : Continuous ι}
      {U : Univ (GCond.noCondition c.O (η.comp ι) (Ψ.comp ι))} {I : Ideal U.R} {cc g₁ : Γ} (S : SRing N hι U I cc g₁), l ≠ 2 → Marks η Ψ cc g₁ →
      ∀ f : S.R →ₐ[c.O] PadicAlgCl l, TwoPt η S.r.hom f →
        (TypeI η (push f S.r.hom) ∨ TypeII η (push f S.r.hom)) ∧
        ∀ f' : S.R →ₐ[c.O] PadicAlgCl l, IsLocPt f' → MatIso η.ker (mats (push f S.r.hom)) (mats (push f' S.r.hom)) →
          ∃ t : (PadicAlgCl l)ˣ, push f' S.r.hom = conjBy (tor _ t) (push f S.r.hom) := by
  intro l _ c Γ H _ _ _ _ _ _ η Ψ N ι hι U I cc g₁ S hl2 hmk f htwo
  have hid : (GLift.map (AlgHom.id c.O S.R) S.r).hom = S.r.hom := by
    ext g : 1
    refine SemidirectProduct.ext ?_ ?_
    · ext i j
      simp [GLift.map, GG.map]
    · simp [GLift.map, GG.map]
  have hN : Normalised cc g₁ S.r.hom := by
    have h := ((S.rep S.R).1 (AlgHom.id c.O S.R)).1
    rwa [hid] at h
  have hmult : ∀ g : S.R →ₐ[c.O] PadicAlgCl l, HasMult η (push g S.r.hom) := by
    intro g x
    simpa [push, GG.map] using S.r.hasMult x
  have hnorm_g : ∀ g : S.R →ₐ[c.O] PadicAlgCl l, Normalised cc g₁ (push g S.r.hom) :=
    fun g => normalised_map (g : S.R →+* PadicAlgCl l) hN
  have hzeta_g : ∀ g : S.R →ₐ[c.O] PadicAlgCl l,
      zeta cc g₁ (push g S.r.hom) = g (zeta cc g₁ S.r.hom) :=
    fun g => zmat_map (g : S.R →+* PadicAlgCl l) cc g₁ S.r.hom 0 0
  obtain ⟨_, hz0u⟩ := zeta_reducible_rep_eq_sub_inv_and_isUnit η Ψ cc g₁ hmk
  have hmem := zeta_sub_mem S.r cc g₁
  have ha : ‖algebraMap c.O (PadicAlgCl l) (zeta cc g₁ (r0 η Ψ))‖ = 1 := by
    obtain ⟨u, hu⟩ := hz0u
    have h1 := norm_coe_coefO_le_one c (zeta cc g₁ (r0 η Ψ))
    have h2 := norm_coe_coefO_le_one c (↑u⁻¹ : c.O)
    have hprod : algebraMap c.O (PadicAlgCl l) (zeta cc g₁ (r0 η Ψ)) *
        algebraMap c.O (PadicAlgCl l) (↑u⁻¹ : c.O) = 1 := by
      rw [← map_mul, ← hu, Units.mul_inv, map_one]
    have hn := congrArg norm hprod
    rw [norm_mul, norm_one] at hn
    change ‖((zeta cc g₁ (r0 η Ψ) : c.O) : PadicAlgCl l)‖ * ‖((↑u⁻¹ : c.O) : PadicAlgCl l)‖ = 1 at hn
    change ‖((zeta cc g₁ (r0 η Ψ) : c.O) : PadicAlgCl l)‖ = 1
    have key := mul_le_mul_of_nonneg_left h2 (norm_nonneg ((zeta cc g₁ (r0 η Ψ) : c.O) : PadicAlgCl l))
    rw [mul_one] at key
    exact le_antisymm h1 (by linarith)
  have hdec : ∀ g : S.R →ₐ[c.O] PadicAlgCl l, IsLocPt g →
      ‖zeta cc g₁ (push g S.r.hom) - algebraMap c.O (PadicAlgCl l) (zeta cc g₁ (r0 η Ψ))‖ < 1 := by
    intro g hg
    rw [hzeta_g, ← AlgHom.commutes g, ← map_sub]
    exact hg _ hmem
  have hne0 : ∀ g : S.R →ₐ[c.O] PadicAlgCl l, IsLocPt g → zeta cc g₁ (push g S.r.hom) ≠ 0 := by
    intro g hg h0
    have h := hdec g hg
    rw [h0, zero_sub, norm_neg, ha] at h
    exact lt_irrefl _ h
  have h2 : ‖(2 : PadicAlgCl l)‖ = 1 := by
    have h2e : (2 : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) ((2 : ℕ) : ℚ_[l]) := by
      rw [Nat.cast_ofNat, map_ofNat]
    rw [h2e, PadicAlgCl.norm_extends, Padic.norm_natCast_eq_one_iff]
    exact (Nat.coprime_primes (Fact.out) Nat.prime_two).mpr hl2
  have hnn : ∀ g g' : S.R →ₐ[c.O] PadicAlgCl l, IsLocPt g → IsLocPt g' →
      zeta cc g₁ (push g' S.r.hom) ≠ -zeta cc g₁ (push g S.r.hom) := by
    intro g g' hg hg' heq
    have e1 := hdec g hg
    have e2 := hdec g' hg'
    have hsum : (2 : PadicAlgCl l) * algebraMap c.O (PadicAlgCl l) (zeta cc g₁ (r0 η Ψ)) =
        -((zeta cc g₁ (push g S.r.hom) - algebraMap c.O (PadicAlgCl l) (zeta cc g₁ (r0 η Ψ))) +
          (zeta cc g₁ (push g' S.r.hom) - algebraMap c.O (PadicAlgCl l) (zeta cc g₁ (r0 η Ψ)))) := by
      rw [heq]
      ring
    have hle := IsUltrametricDist.norm_add_le_max
      (zeta cc g₁ (push g S.r.hom) - algebraMap c.O (PadicAlgCl l) (zeta cc g₁ (r0 η Ψ)))
      (zeta cc g₁ (push g' S.r.hom) - algebraMap c.O (PadicAlgCl l) (zeta cc g₁ (r0 η Ψ)))
    have hn := congrArg norm hsum
    rw [norm_neg, norm_mul, h2, ha, one_mul] at hn
    have hm := max_lt e1 e2
    linarith
  have hf := htwo.1
  have hcases := shape_cases η (push f S.r.hom) cc g₁ two_ne_zero (hmult f) hmk.ηc hmk.ηg
    (hnorm_g f) (hne0 f hf)
  have htype : TypeI η (push f S.r.hom) ∨ TypeII η (push f S.r.hom) := by
    rcases hcases with h | h | h | h
    · exact Or.inl h
    · exact absurd h htwo.2.1
    · exact absurd h htwo.2.2
    · exact Or.inr h
  refine ⟨htype, ?_⟩
  intro f' hf' hiso
  exact conjBy_tor_of_iso η (push f S.r.hom) (push f' S.r.hom) cc g₁ two_ne_zero (hmult f) (hmult f')
    hmk.ηc hmk.ηg (hnorm_g f) (hnorm_g f') (hne0 f hf) (hne0 f' hf') (hnn f f' hf hf') htype hiso
