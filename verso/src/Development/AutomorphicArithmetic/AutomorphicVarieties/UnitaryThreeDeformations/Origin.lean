import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.MapDiagonalRepMatrixEq

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

/- English proof (translation)
Establish `hsupp : ∀ n : σ →₀ ℕ, n ≠ 0 → n.support.Nonempty` using `fun n hn => Finsupp.support_nonempty_iff.mpr hn`. Set `sel : (σ →₀ ℕ) → σ → Prop` to `fun n i => ∃ h : n ≠ 0, (hsupp n h).choose = i`. Set `q : σ → MvPowerSeries σ O` to `fun i m => if sel (m + Finsupp.single i 1) i then MvPowerSeries.coeff (m + Finsupp.single i 1) p else 0`. Establish `hX : ∀ (n : σ →₀ ℕ) (i : σ) (f : MvPowerSeries σ O), MvPowerSeries.coeff n (MvPowerSeries.X i * f) = if Finsupp.single i 1 ≤ n then MvPowerSeries.coeff (n - Finsupp.single i 1) f else 0`. Introduce `n i f`.

Rewrite using `[show (MvPowerSeries.X i : MvPowerSeries σ O) = MvPowerSeries.monomial (Finsupp.single i 1) 1 from rfl, MvPowerSeries.coeff_monomial_mul, one_mul]`. Establish `hq : ∀ (i : σ) (m : σ →₀ ℕ), MvPowerSeries.coeff m (q i) = if sel (m + Finsupp.single i 1) i then MvPowerSeries.coeff (m + Finsupp.single i 1) p else 0` using `fun i m => rfl`. Establish `hdec : p = ∑ i, MvPowerSeries.X i * q i`. Use extensionality with `n`. Rewrite using `[map_sum]`.

Repeatedly rewrite using `[hX, hq]`. Distinguish the cases in `hn : n = 0`. Substitute `hn` using the available equality. Rewrite using `[MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hp]`. Use `symm`.

Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `i _`. Rewrite using `[if_neg]`. Introduce `hle`. Use `hle i` as an intermediate fact.

Simplify using `at this`. Use `set j := (hsupp n hn).choose with hj`. Establish `hjmem : j ∈ n.support` using `(hsupp n hn).choose_spec`. Establish `hjle : Finsupp.single j 1 ≤ n`. Rewrite using `[Finsupp.single_le_iff]`.

Conclude with `Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hjmem)`. Rewrite using `[Finset.sum_eq_single j]`. Rewrite using `[if_pos hjle, tsub_add_cancel_of_le hjle, if_pos ⟨hn, rfl⟩]`. Introduce `b _ hb`. Distinguish the cases in `hble : Finsupp.single b 1 ≤ n`.

Rewrite using `[if_pos hble, tsub_add_cancel_of_le hble, if_neg]`. Introduce and unpack `⟨_, hb'⟩`. Conclude with `hb hb'.symm`. Rewrite using `[if_neg hble]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ j) h`. Rewrite using `[hdec, map_sum]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `i _`. Rewrite using `[map_mul, hφ, zero_mul]`.
-/
private theorem UpperTheory.V.UnitaryThreeInertia.map_eq_zero_of_cc {O A σ : Type} [CommRing O] [CommRing A] [Fintype σ]
    (φ : MvPowerSeries σ O →+* A) (hφ : ∀ i, φ (MvPowerSeries.X i) = 0) (p : MvPowerSeries σ O)
    (hp : MvPowerSeries.constantCoeff p = 0) : φ p = 0 := by
  classical
  have hsupp : ∀ n : σ →₀ ℕ, n ≠ 0 → n.support.Nonempty :=
    fun n hn => Finsupp.support_nonempty_iff.mpr hn
  let sel : (σ →₀ ℕ) → σ → Prop := fun n i => ∃ h : n ≠ 0, (hsupp n h).choose = i
  let q : σ → MvPowerSeries σ O := fun i m =>
    if sel (m + Finsupp.single i 1) i then MvPowerSeries.coeff (m + Finsupp.single i 1) p else 0
  have hX : ∀ (n : σ →₀ ℕ) (i : σ) (f : MvPowerSeries σ O),
      MvPowerSeries.coeff n (MvPowerSeries.X i * f)
        = if Finsupp.single i 1 ≤ n then MvPowerSeries.coeff (n - Finsupp.single i 1) f else 0 := by
    intro n i f
    rw [show (MvPowerSeries.X i : MvPowerSeries σ O) = MvPowerSeries.monomial (Finsupp.single i 1) 1
      from rfl, MvPowerSeries.coeff_monomial_mul, one_mul]
  have hq : ∀ (i : σ) (m : σ →₀ ℕ), MvPowerSeries.coeff m (q i)
      = if sel (m + Finsupp.single i 1) i then MvPowerSeries.coeff (m + Finsupp.single i 1) p else 0 :=
    fun i m => rfl
  have hdec : p = ∑ i, MvPowerSeries.X i * q i := by
    ext n
    rw [map_sum]
    simp_rw [hX, hq]
    by_cases hn : n = 0
    · subst hn
      rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hp]
      symm
      apply Finset.sum_eq_zero
      intro i _
      rw [if_neg]
      intro hle
      have := hle i
      simp at this
    · set j := (hsupp n hn).choose with hj
      have hjmem : j ∈ n.support := (hsupp n hn).choose_spec
      have hjle : Finsupp.single j 1 ≤ n := by
        rw [Finsupp.single_le_iff]
        exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hjmem)
      rw [Finset.sum_eq_single j]
      · rw [if_pos hjle, tsub_add_cancel_of_le hjle, if_pos ⟨hn, rfl⟩]
      · intro b _ hb
        by_cases hble : Finsupp.single b 1 ≤ n
        · rw [if_pos hble, tsub_add_cancel_of_le hble, if_neg]
          rintro ⟨_, hb'⟩
          exact hb hb'.symm
        · rw [if_neg hble]
      · intro h
        exact absurd (Finset.mem_univ j) h
  rw [hdec, map_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [map_mul, hφ, zero_mul]

/- English proof (translation)
Establish `h0 : MvPowerSeries.constantCoeff (p - algebraMap O (MvPowerSeries σ O) (MvPowerSeries.constantCoeff p)) = 0`. Rewrite using `[map_sub]`. Conclude with `sub_eq_zero.mpr rfl`. Establish `h` using `UpperTheory.V.UnitaryThreeInertia.map_eq_zero_of_cc (φ : MvPowerSeries σ O →+* O) (fun i => hφ i) _ h0`. Rewrite `h` using `[map_sub, sub_eq_zero]`.

Establish `h2 : φ (algebraMap O (MvPowerSeries σ O) (MvPowerSeries.constantCoeff p)) = MvPowerSeries.constantCoeff p`. Rewrite using `[AlgHom.commutes]`. Both sides reduce to the same expression. Conclude with `h.trans h2`.
-/
private theorem UpperTheory.V.UnitaryThreeInertia.map_eq_cc {O σ : Type} [CommRing O] [Fintype σ]
    (φ : MvPowerSeries σ O →ₐ[O] O) (hφ : ∀ i, φ (MvPowerSeries.X i) = 0) (p : MvPowerSeries σ O) :
    φ p = MvPowerSeries.constantCoeff p := by
  have h0 : MvPowerSeries.constantCoeff
      (p - algebraMap O (MvPowerSeries σ O) (MvPowerSeries.constantCoeff p)) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr rfl
  have h := UpperTheory.V.UnitaryThreeInertia.map_eq_zero_of_cc (φ : MvPowerSeries σ O →+* O) (fun i => hφ i) _ h0
  rw [map_sub, sub_eq_zero] at h
  have h2 : φ (algebraMap O (MvPowerSeries σ O) (MvPowerSeries.constantCoeff p))
      = MvPowerSeries.constantCoeff p := by
    rw [AlgHom.commutes]
    rfl
  exact h.trans h2

/- English proof (translation)
Introduce `O _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hF g₁ hg₁ R _ _ _ u hu W hW`. Take `⟨f, hf, -⟩` from `hu.univ O (F.rz O) (UpperTheory.V.UnitaryThreeInertia.isPt_rz F hF g₁)`. Establish `hz : ∀ i, f (W.z i) = 0`. Introduce `i`. Take `⟨g, a, b, -, -, hzi⟩` from `hW.var i`.

Rewrite using `[hzi, map_sub]`. Establish `h1 : f ((u g).mat a b) = ((F.rz O) g).mat a b`. Rewrite using `[← hf]`. Both sides reduce to the same expression. Establish `h2 : f (((F.rz R) g).mat a b) = ((F.rz O) g).mat a b` using `by show f (algebraMap O R _) = _`.

Rewrite using `[AlgHom.commutes]`. Both sides reduce to the same expression. Rewrite using `[h1, h2, sub_self]`. Use `haveI := W.fin`. Set `ψ : MvPowerSeries W.σ O →ₐ[O] O` to `f.comp W.π`.

Establish `hψ : ∀ p, ψ p = MvPowerSeries.constantCoeff p` using `UpperTheory.V.UnitaryThreeInertia.map_eq_cc ψ (fun i => hz i)`. Establish `hO : W.HasOrigin`. Introduce `p hp`. Rewrite using `[← hψ]`. Use `show f (W.π p) = 0`.

Rewrite using `[hp, map_zero]`. Use `⟨hO, ?_⟩` and prove the remaining obligations. Establish `heq : W.origin hO = f`. Use extensionality with `x`. Take `⟨p, rfl⟩` from `W.surj x`.

Rewrite using `[UpperTheory.V.Alg.WPres.origin_π, ← hψ]`. Both sides reduce to the same expression. Rewrite using `[heq, hf]`. Conclude with `MonoidHom.ext fun g => rfl`.
-/
theorem UpperTheory.V.UnitaryThreeInertia.hasOrigin :
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    ∀ (g₁ : Γ), F.Marked g₁ → ∀ {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (u : Γ →* GG 3 R), F.IsUniv g₁ u →
    ∀ (W : WPres O ℤ R), F.Adapted u W → ∃ h : W.HasOrigin, push (W.origin h) u = r0 F.η F.Ψ := by
  intro O _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hF g₁ hg₁ R _ _ _ u hu W hW
  obtain ⟨f, hf, -⟩ := hu.univ O (F.rz O) (UpperTheory.V.UnitaryThreeInertia.isPt_rz F hF g₁)
  have hz : ∀ i, f (W.z i) = 0 := by
    intro i
    obtain ⟨g, a, b, -, -, hzi⟩ := hW.var i
    rw [hzi, map_sub]
    have h1 : f ((u g).mat a b) = ((F.rz O) g).mat a b := by
      rw [← hf]
      rfl
    have h2 : f (((F.rz R) g).mat a b) = ((F.rz O) g).mat a b := by
      show f (algebraMap O R _) = _
      rw [AlgHom.commutes]
      rfl
    rw [h1, h2, sub_self]
  haveI := W.fin
  let ψ : MvPowerSeries W.σ O →ₐ[O] O := f.comp W.π
  have hψ : ∀ p, ψ p = MvPowerSeries.constantCoeff p :=
    UpperTheory.V.UnitaryThreeInertia.map_eq_cc ψ (fun i => hz i)
  have hO : W.HasOrigin := by
    intro p hp
    rw [← hψ]
    show f (W.π p) = 0
    rw [hp, map_zero]
  refine ⟨hO, ?_⟩
  have heq : W.origin hO = f := by
    ext x
    obtain ⟨p, rfl⟩ := W.surj x
    rw [UpperTheory.V.Alg.WPres.origin_π, ← hψ]
    rfl
  rw [heq, hf]
  exact MonoidHom.ext fun g => rfl
