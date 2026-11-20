import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Definitions.Foundations.AbsCharNotUnitary

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host

namespace GlobalTheory.HeckeGal.Model

variable (E : Type) [Field E] [NumberField E]

def absPow (s : ℝ) : HChar E :=
  ⟨GlobalTheory.Mem.Chr.CharModel.absHom E s, (GlobalTheory.Mem.Chr.CharModel.absChar E s).2⟩

/- English proof (translation)
The claim follows from `GlobalTheory.Mem.Chr.CharModel.absChar_isAbsPow (F := E) s`.
-/
theorem absPow_isAbsPow (s : ℝ) : (absPow E s).IsAbsPow s :=
  GlobalTheory.Mem.Chr.CharModel.absChar_isAbsPow (F := E) s

/- English proof (translation)
Use `⟨Algebra.norm ℚ k, ?_⟩` and prove the remaining obligations. Establish `h` using `Algebra.norm_eq_prod_embeddings ℚ ℂ k`. Rewrite `h` using `[← Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ) (fun φ : E →+* ℂ => φ k) (fun σ : E →ₐ[ℚ] ℂ => σ k) (fun _ => rfl)]`. Rewrite using `[← h]`. Simplify using the standard rewrite rules.
-/
theorem prod_emb_real (k : E) : ∃ q : ℚ, ∏ φ : E →+* ℂ, φ k = (q : ℂ) := by
  refine ⟨Algebra.norm ℚ k, ?_⟩
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ k
  rw [← Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ) (fun φ : E →+* ℂ => φ k)
    (fun σ : E →ₐ[ℚ] ℂ => σ k) (fun _ => rfl)] at h
  rw [← h]; simp

/- English proof (translation)
Introduce `k`. Rewrite using `[(absPow_isAbsPow E 2).2.2 k]`. Take `⟨q, hq⟩` from `prod_emb_real E (k : E)`. Establish `h1 : ∏ φ : E →+* ℂ, ((‖φ (k : E)‖ : ℝ) : ℂ) = ((|(q : ℝ)| : ℝ) : ℂ)`. Rewrite using `[← Complex.ofReal_prod, ← norm_prod, hq]`.

Use `congr 1`. Conclude with `Complex.norm_ratCast q`. Establish `e2 : ((2 : ℝ) : ℂ) = ((2 : ℕ) : ℂ)` using `by norm_num`. Simplify using `only [e2, Complex.cpow_natCast, zpow_ofNat]`. Rewrite using `[Finset.prod_pow, Finset.prod_pow, h1, hq, ← Complex.ofReal_pow, sq_abs]`.

Use `push_cast`. Both sides reduce to the same expression.
-/
theorem absPow_two_isAlg : (absPow E 2).IsAlg (fun _ => 2) := by
  intro k
  rw [(absPow_isAbsPow E 2).2.2 k]
  obtain ⟨q, hq⟩ := prod_emb_real E (k : E)
  have h1 : ∏ φ : E →+* ℂ, ((‖φ (k : E)‖ : ℝ) : ℂ) = ((|(q : ℝ)| : ℝ) : ℂ) := by
    rw [← Complex.ofReal_prod, ← norm_prod, hq]
    congr 1
    exact Complex.norm_ratCast q
  have e2 : ((2 : ℝ) : ℂ) = ((2 : ℕ) : ℂ) := by norm_num
  simp only [e2, Complex.cpow_natCast, zpow_ofNat]
  rw [Finset.prod_pow, Finset.prod_pow, h1, hq, ← Complex.ofReal_pow, sq_abs]
  push_cast; rfl

/- English proof (translation)
The claim follows from `isAlgPos_of_isAlg (absPow_two_isAlg E)`.
-/
theorem absPow_two_isAlgPos : IsAlgPos (absPow E 2) (fun _ => 2) := isAlgPos_of_isAlg (absPow_two_isAlg E)

/- English proof (translation)
Introduce `k hk`. Rewrite using `[(absPow_isAbsPow ℚ 1).2.2 k]`. Use `Finset.prod_congr rfl fun φ _ => ?_` and prove the remaining obligations. Establish `h` using `hk (Rat.castHom ℝ)`. Simplify using `only [eq_ratCast] at h`.

Simplify using `only [eq_ratCast, Complex.ofReal_one, Complex.cpow_one, zpow_one, Complex.norm_ratCast, abs_of_pos h]`. Simplify using the standard rewrite rules.
-/
theorem absPow_one_isAlgPos_rat : IsAlgPos (absPow ℚ 1) (fun _ => 1) := by
  intro k hk
  rw [(absPow_isAbsPow ℚ 1).2.2 k]
  refine Finset.prod_congr rfl fun φ _ => ?_
  have h := hk (Rat.castHom ℝ)
  simp only [eq_ratCast] at h
  simp only [eq_ratCast, Complex.ofReal_one, Complex.cpow_one, zpow_one, Complex.norm_ratCast, abs_of_pos h]
  simp

/- English proof (translation)
Introduce `h`. Establish `h1` using `h (-1)`. Rewrite `h1` using `[(absPow_isAbsPow ℚ 1).2.2]`. Simplify using `at h1`. Rewrite `h1` using `[Embeddings.card, Module.finrank_self]`.

Evaluate the numerical expressions using `at h1`.
-/
theorem absPow_one_not_isAlg_rat : ¬ (absPow ℚ 1).IsAlg (fun _ => 1) := by
  intro h
  have h1 := h (-1)
  rw [(absPow_isAbsPow ℚ 1).2.2] at h1
  simp at h1
  rw [Embeddings.card, Module.finrank_self] at h1
  norm_num at h1

/- English proof (translation)
Rewrite using `[h.frob_unr ha (Or.inl hv) ((absPow_isAbsPow E m).1 v) hA hσ, (absPow_isAbsPow E m).2.1 v, Complex.cpow_neg, Complex.ofReal_natCast, Complex.cpow_natCast, map_inv₀, inv_inv, map_pow, map_natCast]`. Both sides reduce to the same expression.
-/
theorem frob_abs {Ω : Type} [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {art : Ideles E →* Gab E Ω}
    (ha : IsGlobalArtin art) {ι : Qbar l ≃+* ℂ} {m : ℕ} {n : (E →+* ℂ) → ℤ} {r : G E Ω →* (Qbar l)ˣ}
    (h : IsLAdicOf art ι (absPow E m) n r) {v : HeightOneSpectrum (𝓞 E)} (hv : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal)
    {A : ValuationSubring Ω} (hA : IsPlaceOver A v) {σ : G E Ω} (hσ : IsFrob (F := E) A (normV v) σ) :
    ((r σ : (Qbar l)ˣ) : Qbar l) = (normV v : Qbar l) ^ m := by
  rw [h.frob_unr ha (Or.inl hv) ((absPow_isAbsPow E m).1 v) hA hσ, (absPow_isAbsPow E m).2.1 v,
    Complex.cpow_neg, Complex.ofReal_natCast, Complex.cpow_natCast, map_inv₀, inv_inv, map_pow, map_natCast]
  rfl

/- English proof (translation)
Unfold `infPow`. Rewrite using `[Fintype.prod_unique]`. Use `set w : InfinitePlace ℚ := default`. Establish `hs : Subsingleton {i : w.Completion →+* ℂ // Continuous i}`. Use `⟨fun a b => Subtype.ext (DFunLike.coe_injective ?_)⟩` and prove the remaining obligations.

Establish `hd : DenseRange (algebraMap ℚ w.Completion)`. Use `Dense.mono ?_ (InfinitePlace.Completion.denseRange_coe w)` and prove the remaining obligations. Introduce and unpack `_ ⟨a, rfl⟩`. Conclude with `⟨WithAbs.equiv w.1 a, rfl⟩`. Use `hd.equalizer a.2 b.2 ?_` and prove the remaining obligations.

Use function extensionality and compare the values at `x`. Conclude with `DFunLike.congr_fun (Subsingleton.elim (a.1.comp (algebraMap ℚ _)) (b.1.comp (algebraMap ℚ _))) x`. Set `i0 : {i : w.Completion →+* ℂ // Continuous i}` to `⟨InfinitePlace.Completion.extensionEmbedding w, (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous⟩`. Rewrite using `[finprod_eq_single _ i0 fun j hj => absurd (Subsingleton.elim j i0) hj, Subsingleton.elim (i0.1.comp (algebraMap ℚ w.Completion)) (Rat.castHom ℂ)]`. Use `congr 1`.

Conclude with `eq_ratCast (i0.1.comp (algebraMap ℚ w.Completion)) (k : ℚ)`.
-/
theorem infPow_diag_rat (n : (ℚ →+* ℂ) → ℤ) (k : ℚˣ) :
    infPow n (diagUnits ℚ k) = ((k : ℚ) : ℂ) ^ n (Rat.castHom ℂ) := by
  unfold infPow
  rw [Fintype.prod_unique]
  set w : InfinitePlace ℚ := default
  have hs : Subsingleton {i : w.Completion →+* ℂ // Continuous i} := by
    refine ⟨fun a b => Subtype.ext (DFunLike.coe_injective ?_)⟩
    have hd : DenseRange (algebraMap ℚ w.Completion) := by
      refine Dense.mono ?_ (InfinitePlace.Completion.denseRange_coe w)
      rintro _ ⟨a, rfl⟩
      exact ⟨WithAbs.equiv w.1 a, rfl⟩
    refine hd.equalizer a.2 b.2 ?_
    funext x
    exact DFunLike.congr_fun (Subsingleton.elim (a.1.comp (algebraMap ℚ _)) (b.1.comp (algebraMap ℚ _))) x
  let i0 : {i : w.Completion →+* ℂ // Continuous i} :=
    ⟨InfinitePlace.Completion.extensionEmbedding w, (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous⟩
  rw [finprod_eq_single _ i0 fun j hj => absurd (Subsingleton.elim j i0) hj,
    Subsingleton.elim (i0.1.comp (algebraMap ℚ w.Completion)) (Rat.castHom ℂ)]
  congr 1
  exact eq_ratCast (i0.1.comp (algebraMap ℚ w.Completion)) (k : ℚ)

/- English proof (translation)
Unfold `lPow`. Set `p : Nat.Primes` to `⟨l, hl.out⟩`. Set `v : HeightOneSpectrum (𝓞 ℚ)` to `(Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p`. Rewrite using `[finprod_eq_single _ v]`. Establish `hs : Subsingleton {j : v.adicCompletion ℚ →+* Qbar l // Continuous j}`.

Use `⟨fun a b => Subtype.ext (DFunLike.coe_injective ?_)⟩` and prove the remaining obligations. Use `(HeightOneSpectrum.denseRange_algebraMap ℚ v).equalizer a.2 b.2 ?_` and prove the remaining obligations. Use function extensionality and compare the values at `x`. Conclude with `DFunLike.congr_fun (Subsingleton.elim (a.1.comp (algebraMap ℚ _)) (b.1.comp (algebraMap ℚ _))) x`. Set `e : ℚ_[l] ≃A[ℚ] v.adicCompletion ℚ` to `Padic.adicCompletionEquiv (𝓞 ℚ) p`.

Set `j0 : {j : v.adicCompletion ℚ →+* Qbar l // Continuous j}` to `⟨(algebraMap ℚ_[l] (Qbar l)).comp e.symm.toAlgEquiv.toRingEquiv.toRingHom, (continuous_algebraMap ℚ_[l] (Qbar l)).comp e.symm.continuous⟩`. Unfold `locPow`. Rewrite using `[finprod_eq_single _ j0 fun j hj => absurd (Subsingleton.elim j j0) hj, Subsingleton.elim ((ι.toRingHom.comp j0.1).comp (algebraMap ℚ (v.adicCompletion ℚ))) (Rat.castHom ℂ)]`. Use `congr 1`. Conclude with `eq_ratCast (j0.1.comp (algebraMap ℚ (v.adicCompletion ℚ))) (k : ℚ)`.

Introduce `u hu`. Use `locPow_of_notMem ι n (fun hm => hu ?_) _` and prove the remaining obligations. Establish `h1 : Rat.HeightOneSpectrum.natGenerator u ∣ l`. Rewrite using `[Rat.HeightOneSpectrum.natGenerator_dvd_iff, ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ))]`. Conclude with `Ideal.mem_map_of_mem _ hm`.

Establish `h2` using `(Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator u) hl.out).1 h1`. Rewrite using `[Equiv.eq_symm_apply]`. Conclude with `Subtype.ext h2`.
-/
theorem lPow_diag_rat {l : ℕ} [hl : Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : (ℚ →+* ℂ) → ℤ) (k : ℚˣ) :
    lPow ι n (diagUnits ℚ k) = ((k : ℚ) : Qbar l) ^ n (Rat.castHom ℂ) := by
  unfold lPow
  let p : Nat.Primes := ⟨l, hl.out⟩
  let v : HeightOneSpectrum (𝓞 ℚ) := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p
  rw [finprod_eq_single _ v]
  · have hs : Subsingleton {j : v.adicCompletion ℚ →+* Qbar l // Continuous j} := by
      refine ⟨fun a b => Subtype.ext (DFunLike.coe_injective ?_)⟩
      refine (HeightOneSpectrum.denseRange_algebraMap ℚ v).equalizer a.2 b.2 ?_
      funext x
      exact DFunLike.congr_fun (Subsingleton.elim (a.1.comp (algebraMap ℚ _)) (b.1.comp (algebraMap ℚ _))) x
    let e : ℚ_[l] ≃A[ℚ] v.adicCompletion ℚ := Padic.adicCompletionEquiv (𝓞 ℚ) p
    let j0 : {j : v.adicCompletion ℚ →+* Qbar l // Continuous j} :=
      ⟨(algebraMap ℚ_[l] (Qbar l)).comp e.symm.toAlgEquiv.toRingEquiv.toRingHom,
        (continuous_algebraMap ℚ_[l] (Qbar l)).comp e.symm.continuous⟩
    unfold locPow
    rw [finprod_eq_single _ j0 fun j hj => absurd (Subsingleton.elim j j0) hj,
      Subsingleton.elim ((ι.toRingHom.comp j0.1).comp (algebraMap ℚ (v.adicCompletion ℚ))) (Rat.castHom ℂ)]
    congr 1
    exact eq_ratCast (j0.1.comp (algebraMap ℚ (v.adicCompletion ℚ))) (k : ℚ)
  · intro u hu
    refine locPow_of_notMem ι n (fun hm => hu ?_) _
    have h1 : Rat.HeightOneSpectrum.natGenerator u ∣ l := by
      rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff, ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ))]
      exact Ideal.mem_map_of_mem _ hm
    have h2 := (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator u) hl.out).1 h1
    rw [Equiv.eq_symm_apply]
    exact Subtype.ext h2

/- English proof (translation)
Rewrite using `[χ.2.2 k, infPow_diag_rat, lPow_diag_rat, Units.val_one, one_mul, map_inv₀, map_zpow₀, map_ratCast]`. Conclude with `inv_mul_cancel₀ (zpow_ne_zero _ (by exact_mod_cast k.ne_zero))`.
-/
theorem formula_diag_rat {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (χ : HChar ℚ) (n : (ℚ →+* ℂ) → ℤ) (k : ℚˣ) :
    ι.symm (((χ.1 (diagUnits ℚ k) : ℂˣ) : ℂ) * (infPow n (diagUnits ℚ k))⁻¹) * lPow ι n (diagUnits ℚ k) = 1 := by
  rw [χ.2.2 k, infPow_diag_rat, lPow_diag_rat, Units.val_one, one_mul, map_inv₀, map_zpow₀, map_ratCast]
  exact inv_mul_cancel₀ (zpow_ne_zero _ (by exact_mod_cast k.ne_zero))

/- English proof (translation)
Introduce `x σ _`. Rewrite using `[infPow_zero, lPow_zero]`. Simplify using the standard rewrite rules.
-/
theorem isLAdicOf_one {Ω : Type} [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] (art : Ideles E →* Gab E Ω)
    (ι : Qbar l ≃+* ℂ) : IsLAdicOf art ι (1 : HChar E) 0 1 := by
  intro x σ _
  rw [infPow_zero, lPow_zero]
  simp

end GlobalTheory.HeckeGal.Model

end
