import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.BlockDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.SmallCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.WtChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.FrobIn
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.PureDet

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private def blockChar {H K : Type} [Group H] [CommRing K] (r : H →* M4 K) (h : ∀ g, IsBlock (r g)) (ix : Fin 2 → Fin 4)
    (hix : ix = ixA ∨ ix = ixB) : H →* K where
  toFun g := ((r g).submatrix ix ix).det
  map_one' := by
    rw [map_one, Matrix.submatrix_one ix (by rcases hix with rfl | rfl <;> decide), Matrix.det_one]
  map_mul' a b := by
    rw [← Matrix.det_mul, map_mul]
    congr 1
    have ha := h a
    ext i j
    rcases hix with rfl | rfl
    · have h1 : ∀ i, r a (ixA i) 1 = 0 := fun i => ha _ _ (by revert i; decide)
      have h3 : ∀ i, r a (ixA i) 3 = 0 := fun i => ha _ _ (by revert i; decide)
      simp only [Matrix.submatrix_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two, h1, h3, zero_mul, add_zero]
      rfl
    · have h1 : ∀ i, r a (ixB i) 0 = 0 := fun i => ha _ _ (by revert i; decide)
      have h3 : ∀ i, r a (ixB i) 2 = 0 := fun i => ha _ _ (by revert i; decide)
      simp only [Matrix.submatrix_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two, h1, h3, zero_mul, add_zero,
        zero_add]
      rfl

/- English proof (translation)
Introduce `Ω _ _ _ l hl c D hD ι 𝔞 e he r u hp hb ⟨H, M, hH, hM, hP⟩`. Take `⟨-, f2, -, f4, -⟩` from `facts D hD`. Take `⟨a1, -, a3⟩` from `f2 l (Finset.mem_insert_self _ _)`. Use `set φ : 𝔞.V →+* PadicAlgCl l := (e : 𝔞.K →+* PadicAlgCl l).comp 𝔞.toK with hφ`. Use `set ρ := mapRep φ r with hρ`.

Establish `hb' : ∀ g, IsBlock (ρ g)` using `fun g i j h => by rw [hρ, mapRep_apply, hb g i j h, map_zero]`. Establish `hc : Continuous ρ` using `smallCont 𝔞 e he _ hp.small`. Use `haveI : CharZero 𝔞.V := φ.charZero`. Establish `hu : adj u * u = 1` using `by simpa [IsGSp] using hp.sp`. Establish `hdet : ∀ s ∈ D.Ip l, ((r s).submatrix ixA ixA).det = 𝔞.a c (D.ps 0 s) * 𝔞.a c (D.ps 2 s) ∧ ((r s).submatrix ixB ixB).det = 𝔞.a c (D.ps 1 s) * 𝔞.a c (D.ps 3 s)` using `fun s hs => by`.

Establish `h` using `blockDet (maximalIdeal 𝔞.V) (fun i => 𝔞.a c (D.ps i (D.sg l))) u (adj u) (r (D.sg l)) (r s) hu (fun i j hij hm => a3 i j hij (by`. Rewrite `hm` using `[← map_sub, mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff]`. Conclude with `Ideal.Quotient.eq.2 hm))`. Use the proof step `(hb _) (fun i j => by`. Establish `h1` using `hp.red (D.sg l) i j`.

Establish `h2 : 𝔞.a c (D.r0 (D.sg l) i j) = Matrix.diagonal (fun i => 𝔞.a c (D.ps i (D.sg l))) i j` using `by show 𝔞.a c (Matrix.diagonal (fun i => (D.ps i (D.sg l) : c.O)) i j) = _`. Rewrite using `[Matrix.diagonal_apply, Matrix.diagonal_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[h2] at h1)` and apply the resulting hypothesis. Use the proof step `(hp.flag _ a1) (hp.char _ a1) (hb _) (hp.flag s (Ine_le_Dec _ hs))`.

Simplify `h` using `only [hp.inert s hs]`. Establish `hps : ∀ i, ∀ s ∈ D.Ip l ⊓ D.ψ.ker ⊓ D.om.ker, φ (𝔞.a c (D.ps i s)) = algebraMap ℤ_[l] (PadicAlgCl l) (cycZ ℚ Ω l s : ℤ_[l]) ^ D.wts4 i` using `fun i s hs => by`. Rewrite using `[f4 i s hs, Units.val_pow_eq_pow_val, map_pow, map_pow]`. Conclude with `congrArg (· ^ _) (he.1 c _)`. Establish `key : ∀ (ix : Fin 2 → Fin 4) (hix : ix = ixA ∨ ix = ixB) (i j : Fin 4), (∀ s ∈ D.Ip l, ((r s).submatrix ix ix).det = 𝔞.a c (D.ps i s) * 𝔞.a c (D.ps j s)) → ∃ U : Subgroup (G ℚ Ω), IsOpen (U : Set (G ℚ Ω)) ∧ ∀ g ∈ U, ((ρ g).submatrix ix ix).det = algebraMap ℤ_[l] (PadicAlgCl l) (c …` using `fun ix hix i j h => by`.

Establish `h1 : ∀ g, r g = 1 → blockChar ρ hb' ix hix g = 1` using `fun g hg => by`. Establish `: ρ g = ρ 1`. Use extensionality with `i j`. Rewrite using `[hρ, mapRep_apply, mapRep_apply, hg, map_one r]`. Rewrite using `[← map_one (blockChar ρ hb' ix hix)]`.

Conclude with `congrArg (fun X : M4 _ => (X.submatrix ix ix).det) this`. Use `wtChar D hD (blockChar ρ hb' ix hix) _ (hc.matrix_submatrix ix ix).matrix_det (fun A hA g hg h2 => h1 g (hp.unr A hA g hg h2)) (fun p h2 g hg => h1 g (hp.atP p h2 g hg)) fun s hs => ?_` and prove the remaining obligations. Rewrite using `[pow_add, ← hps i s hs, ← hps j s hs, ← map_mul, ← h s hs.1.1, RingHom.map_det]`. Both sides reduce to the same expression. Take `⟨U, hU, hU'⟩` from `key ixA (Or.inl rfl) 0 2 fun s hs => (hdet s hs).1`.

Take `⟨W, hW, hW'⟩` from `key ixB (Or.inr rfl) 1 3 fun s hs => (hdet s hs).2`. Take `⟨p, A, f, σ, h1, h2, h3, h4, h5, h6, h7⟩` from `frobIn Ω l (H ⊓ (U ⊓ W)) M (hH.inter (hU.inter hW)) hM`. Establish `h8` using `pureDet (ι : PadicAlgCl l →+* ℂ) (ρ σ) (hb' σ) (hP p h1 h2 A h3 f σ h4 h5.1 h6)`. Rewrite `h8` using `[hU' σ h5.2.1, hW' σ h5.2.2, h7]`. Simplify using `only [map_pow, map_natCast, norm_pow, Complex.norm_natCast] at h8`.

Establish `h9 : (1 : ℝ) < (p : ℝ) ^ f` using `one_lt_pow₀ (by exact_mod_cast h1.one_lt) h4.ne'`. Establish `h10 : D.e + 1 + 1 = D.e + 0` using `pow_right_injective₀ (zero_lt_one.trans h9) h9.ne' h8`. Use linear arithmetic over natural numbers and integers.
-/
theorem UpperTheory.V.Ws.nePure :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (ι : PadicAlgCl l ≃+* ℂ) (𝔞 : Amb l) (e : 𝔞.K ≃+* PadicAlgCl l), 𝔞.IsZero e → ∀ r u, KPair D 𝔞 r u → (∀ g, IsBlock (r g)) →
      ¬ Pure ι (mapRep ((e : 𝔞.K →+* PadicAlgCl l).comp 𝔞.toK) r) := by
  intro Ω _ _ _ l hl c D hD ι 𝔞 e he r u hp hb ⟨H, M, hH, hM, hP⟩
  obtain ⟨-, f2, -, f4, -⟩ := facts D hD
  obtain ⟨a1, -, a3⟩ := f2 l (Finset.mem_insert_self _ _)
  set φ : 𝔞.V →+* PadicAlgCl l := (e : 𝔞.K →+* PadicAlgCl l).comp 𝔞.toK with hφ
  set ρ := mapRep φ r with hρ
  have hb' : ∀ g, IsBlock (ρ g) := fun g i j h => by rw [hρ, mapRep_apply, hb g i j h, map_zero]
  have hc : Continuous ρ := smallCont 𝔞 e he _ hp.small
  haveI : CharZero 𝔞.V := φ.charZero
  have hu : adj u * u = 1 := by simpa [IsGSp] using hp.sp
  have hdet : ∀ s ∈ D.Ip l, ((r s).submatrix ixA ixA).det = 𝔞.a c (D.ps 0 s) * 𝔞.a c (D.ps 2 s) ∧
      ((r s).submatrix ixB ixB).det = 𝔞.a c (D.ps 1 s) * 𝔞.a c (D.ps 3 s) := fun s hs => by
    have h := blockDet (maximalIdeal 𝔞.V) (fun i => 𝔞.a c (D.ps i (D.sg l))) u (adj u) (r (D.sg l)) (r s) hu
      (fun i j hij hm => a3 i j hij (by
        rw [← map_sub, mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff] at hm
        exact Ideal.Quotient.eq.2 hm))
      (hb _) (fun i j => by
        have h1 := hp.red (D.sg l) i j
        have h2 : 𝔞.a c (D.r0 (D.sg l) i j) = Matrix.diagonal (fun i => 𝔞.a c (D.ps i (D.sg l))) i j := by
          show 𝔞.a c (Matrix.diagonal (fun i => (D.ps i (D.sg l) : c.O)) i j) = _
          rw [Matrix.diagonal_apply, Matrix.diagonal_apply]
          split_ifs <;> simp
        rwa [h2] at h1)
      (hp.flag _ a1) (hp.char _ a1) (hb _) (hp.flag s (Ine_le_Dec _ hs))
    simpa only [hp.inert s hs] using h
  have hps : ∀ i, ∀ s ∈ D.Ip l ⊓ D.ψ.ker ⊓ D.om.ker, φ (𝔞.a c (D.ps i s)) =
      algebraMap ℤ_[l] (PadicAlgCl l) (cycZ ℚ Ω l s : ℤ_[l]) ^ D.wts4 i := fun i s hs => by
    rw [f4 i s hs, Units.val_pow_eq_pow_val, map_pow, map_pow]
    exact congrArg (· ^ _) (he.1 c _)
  have key : ∀ (ix : Fin 2 → Fin 4) (hix : ix = ixA ∨ ix = ixB) (i j : Fin 4),
      (∀ s ∈ D.Ip l, ((r s).submatrix ix ix).det = 𝔞.a c (D.ps i s) * 𝔞.a c (D.ps j s)) →
      ∃ U : Subgroup (G ℚ Ω), IsOpen (U : Set (G ℚ Ω)) ∧ ∀ g ∈ U, ((ρ g).submatrix ix ix).det =
        algebraMap ℤ_[l] (PadicAlgCl l) (cycZ ℚ Ω l g : ℤ_[l]) ^ (D.wts4 i + D.wts4 j) := fun ix hix i j h => by
    have h1 : ∀ g, r g = 1 → blockChar ρ hb' ix hix g = 1 := fun g hg => by
      have : ρ g = ρ 1 := by
        ext i j
        rw [hρ, mapRep_apply, mapRep_apply, hg, map_one r]
      rw [← map_one (blockChar ρ hb' ix hix)]
      exact congrArg (fun X : M4 _ => (X.submatrix ix ix).det) this
    refine wtChar D hD (blockChar ρ hb' ix hix) _ (hc.matrix_submatrix ix ix).matrix_det
      (fun A hA g hg h2 => h1 g (hp.unr A hA g hg h2)) (fun p h2 g hg => h1 g (hp.atP p h2 g hg)) fun s hs => ?_
    rw [pow_add, ← hps i s hs, ← hps j s hs, ← map_mul, ← h s hs.1.1, RingHom.map_det]
    rfl
  obtain ⟨U, hU, hU'⟩ := key ixA (Or.inl rfl) 0 2 fun s hs => (hdet s hs).1
  obtain ⟨W, hW, hW'⟩ := key ixB (Or.inr rfl) 1 3 fun s hs => (hdet s hs).2
  obtain ⟨p, A, f, σ, h1, h2, h3, h4, h5, h6, h7⟩ := frobIn Ω l (H ⊓ (U ⊓ W)) M (hH.inter (hU.inter hW)) hM
  have h8 := pureDet (ι : PadicAlgCl l →+* ℂ) (ρ σ) (hb' σ) (hP p h1 h2 A h3 f σ h4 h5.1 h6)
  rw [hU' σ h5.2.1, hW' σ h5.2.2, h7] at h8
  simp only [map_pow, map_natCast, norm_pow, Complex.norm_natCast] at h8
  have h9 : (1 : ℝ) < (p : ℝ) ^ f := one_lt_pow₀ (by exact_mod_cast h1.one_lt) h4.ne'
  have h10 : D.e + 1 + 1 = D.e + 0 := pow_right_injective₀ (zero_lt_one.trans h9) h9.ne' h8
  omega
