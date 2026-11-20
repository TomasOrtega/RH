import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC
import Formalism.SharpRestriction.CuspSpanNormBounds.KappaEndpoints
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilySeparationBoundOfNorms

noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace GlobalTheory.TypeAsm.HostArith

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

/- English proof (translation)
Use `D.host.toHostAx.isCMField_hostE` as an intermediate fact. Establish `: IsGalois ℚ D.host.E` using `D.host.toHostAx.hostE_isGalois`. Establish `hcc : ∀ g : D.R.GG, (D.R.toFrame.cc * g).1.2 = - g.1.2`. Introduce `g`. Simplify using `[Formalism.HC.Frame.cc, Formalism.FrobeniusOrbits.c0]`.

Establish `hemb : ∀ (τ : D.what₂.Tau) (x : D.host.E), embS D τ x = D.host.φ₀ (D.host.gal.symm (D.eTau τ : D.R.GG) x)` using `fun _ _ => rfl`. Establish `hconj : ∀ y : D.host.E, D.host.φ₀ (D.host.conj y) = starRingEnd ℂ (D.host.φ₀ y)` using `fun y => D.host.toHostAx.conjE_apply _ y`. Use `⟨fun τ a => D.sp.cm.cmUnram.2.1 _ a, fun w => ?_⟩` and prove the remaining obligations. Establish `key : ∀ τ₁ τ₂ : D.what₂.Tau, NumberField.InfinitePlace.mk (embS D τ₁) = NumberField.InfinitePlace.mk (embS D τ₂) → τ₁ = τ₂`. Introduce `τ₁ τ₂ h`.

Rewrite `h` using `[NumberField.InfinitePlace.mk_eq_iff]`. Establish `h1` using `(D.eTau τ₁).2`. Establish `h2` using `(D.eTau τ₂).2`. Rewrite `h1`, `h2` using `[Formalism.HC.Frame.mem_Psi_iff]`. Apply `D.eTau.injective` to reduce the goal to its premises.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `D.host.gal.symm.injective` to reduce the goal to its premises. Break down `h with h | h` into its components or cases. Use extensionality with `x`. Apply `D.host.φ₀.injective` to reduce the goal to its premises.

Use `DFunLike.congr_fun h x` as an intermediate fact. Rewrite `this` using `[hemb, hemb]`. Then use the resulting hypothesis. It suffices to derive a contradiction. Establish `heq : D.host.conj * D.host.gal.symm (D.eTau τ₁ : D.R.GG) = D.host.gal.symm (D.eTau τ₂ : D.R.GG)`. Use extensionality with `x`.

Apply `D.host.φ₀.injective` to reduce the goal to its premises. Use `DFunLike.congr_fun h x` as an intermediate fact. Rewrite `this` using `[NumberField.ComplexEmbedding.conjugate_coe_eq, hemb, hemb]`. Rewrite using `[AlgEquiv.mul_apply, hconj]`. Conclude with `this`.

Establish `h3` using `congrArg (fun g : D.R.GG => g.1.2) (congrArg D.host.gal heq)`. Simplify using `only [map_mul, MulEquiv.apply_symm_apply] at h3`. Rewrite `h3` using `[show D.host.gal D.host.conj = D.R.toFrame.cc from D.host.gal.apply_symm_apply _, hcc, h1, h2]`. Conclude with `absurd h3 (by decide)`. Take `⟨σ, hσ⟩` from `NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := ℚ) D.host.φ₀ w.embedding (Subsingleton.elim _ _)`.

Establish `hwρ : ∀ x, D.host.φ₀ (σ.symm x) = w.embedding x` using `fun x => by rw [← hσ]; rfl`. Establish `hex : ∃ τ : D.what₂.Tau, NumberField.InfinitePlace.mk (embS D τ) = w`. Distinguish the cases in `hgP : D.host.gal σ.symm ∈ D.R.Psi`. Use `⟨D.eTau.symm ⟨_, hgP⟩, ?_⟩` and prove the remaining obligations. Establish `: embS D (D.eTau.symm ⟨_, hgP⟩) = w.embedding`.

Use extensionality with `x`. Rewrite using `[hemb, Equiv.apply_symm_apply]`. Simplify using `only [MulEquiv.symm_apply_apply]`. Conclude with `hwρ x`. Rewrite using `[this, NumberField.InfinitePlace.mk_embedding]`.

Establish `hg' : D.R.toFrame.cc * D.host.gal σ.symm ∈ D.R.Psi`. Rewrite `hgP`, the goal using `[Formalism.HC.Frame.mem_Psi_iff]`. Rewrite using `[hcc]`. Break down `Int.units_eq_one_or (D.host.gal σ.symm).1.2 with h | h` into its components or cases. Conclude with `absurd h hgP`.

Rewrite using `[h, neg_neg]`. Use `⟨D.eTau.symm ⟨_, hg'⟩, ?_⟩` and prove the remaining obligations. Establish `: embS D (D.eTau.symm ⟨_, hg'⟩) = NumberField.ComplexEmbedding.conjugate w.embedding`. Use extensionality with `x`. Rewrite using `[hemb, Equiv.apply_symm_apply, NumberField.ComplexEmbedding.conjugate_coe_eq]`.

Simplify using `only [map_mul, MulEquiv.symm_apply_apply, AlgEquiv.mul_apply]`. Rewrite using `[show D.host.gal.symm D.R.toFrame.cc = D.host.conj from rfl, hconj, hwρ]`. Rewrite using `[this, NumberField.InfinitePlace.mk_conjugate_eq, NumberField.InfinitePlace.mk_embedding]`. Take `⟨τ, hτ⟩` from `hex`. Conclude with `⟨τ, hτ, fun τ' hτ' => key τ' τ (hτ'.trans hτ.symm)⟩`.
-/
theorem places : GlobalTheory.DegVol.IsPlaces (embS D) := by
  have := D.host.toHostAx.isCMField_hostE
  have : IsGalois ℚ D.host.E := D.host.toHostAx.hostE_isGalois
  have hcc : ∀ g : D.R.GG, (D.R.toFrame.cc * g).1.2 = - g.1.2 := by
    intro g
    simp [Formalism.HC.Frame.cc, Formalism.FrobeniusOrbits.c0]
  have hemb : ∀ (τ : D.what₂.Tau) (x : D.host.E),
      embS D τ x = D.host.φ₀ (D.host.gal.symm (D.eTau τ : D.R.GG) x) := fun _ _ => rfl
  have hconj : ∀ y : D.host.E, D.host.φ₀ (D.host.conj y) = starRingEnd ℂ (D.host.φ₀ y) :=
    fun y => D.host.toHostAx.conjE_apply _ y
  refine ⟨fun τ a => D.sp.cm.cmUnram.2.1 _ a, fun w => ?_⟩

  have key : ∀ τ₁ τ₂ : D.what₂.Tau, NumberField.InfinitePlace.mk (embS D τ₁) =
      NumberField.InfinitePlace.mk (embS D τ₂) → τ₁ = τ₂ := by
    intro τ₁ τ₂ h
    rw [NumberField.InfinitePlace.mk_eq_iff] at h
    have h1 := (D.eTau τ₁).2
    have h2 := (D.eTau τ₂).2
    rw [Formalism.HC.Frame.mem_Psi_iff] at h1 h2
    apply D.eTau.injective
    apply Subtype.ext
    apply D.host.gal.symm.injective
    rcases h with h | h
    · ext x
      apply D.host.φ₀.injective
      have := DFunLike.congr_fun h x
      rwa [hemb, hemb] at this
    · exfalso
      have heq : D.host.conj * D.host.gal.symm (D.eTau τ₁ : D.R.GG) =
          D.host.gal.symm (D.eTau τ₂ : D.R.GG) := by
        ext x
        apply D.host.φ₀.injective
        have := DFunLike.congr_fun h x
        rw [NumberField.ComplexEmbedding.conjugate_coe_eq, hemb, hemb] at this
        rw [AlgEquiv.mul_apply, hconj]
        exact this
      have h3 := congrArg (fun g : D.R.GG => g.1.2) (congrArg D.host.gal heq)
      simp only [map_mul, MulEquiv.apply_symm_apply] at h3
      rw [show D.host.gal D.host.conj = D.R.toFrame.cc from D.host.gal.apply_symm_apply _,
        hcc, h1, h2] at h3
      exact absurd h3 (by decide)

  obtain ⟨σ, hσ⟩ := NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := ℚ)
    D.host.φ₀ w.embedding (Subsingleton.elim _ _)
  have hwρ : ∀ x, D.host.φ₀ (σ.symm x) = w.embedding x := fun x => by rw [← hσ]; rfl
  have hex : ∃ τ : D.what₂.Tau, NumberField.InfinitePlace.mk (embS D τ) = w := by
    by_cases hgP : D.host.gal σ.symm ∈ D.R.Psi
    · refine ⟨D.eTau.symm ⟨_, hgP⟩, ?_⟩
      have : embS D (D.eTau.symm ⟨_, hgP⟩) = w.embedding := by
        ext x
        rw [hemb, Equiv.apply_symm_apply]
        simp only [MulEquiv.symm_apply_apply]
        exact hwρ x
      rw [this, NumberField.InfinitePlace.mk_embedding]
    · have hg' : D.R.toFrame.cc * D.host.gal σ.symm ∈ D.R.Psi := by
        rw [Formalism.HC.Frame.mem_Psi_iff] at hgP ⊢
        rw [hcc]
        rcases Int.units_eq_one_or (D.host.gal σ.symm).1.2 with h | h
        · exact absurd h hgP
        · rw [h, neg_neg]
      refine ⟨D.eTau.symm ⟨_, hg'⟩, ?_⟩
      have : embS D (D.eTau.symm ⟨_, hg'⟩) = NumberField.ComplexEmbedding.conjugate w.embedding := by
        ext x
        rw [hemb, Equiv.apply_symm_apply, NumberField.ComplexEmbedding.conjugate_coe_eq]
        simp only [map_mul, MulEquiv.symm_apply_apply, AlgEquiv.mul_apply]
        rw [show D.host.gal.symm D.R.toFrame.cc = D.host.conj from rfl, hconj, hwρ]
      rw [this, NumberField.InfinitePlace.mk_conjugate_eq, NumberField.InfinitePlace.mk_embedding]
  obtain ⟨τ, hτ⟩ := hex
  exact ⟨τ, hτ, fun τ' hτ' => key τ' τ (hτ'.trans hτ.symm)⟩

/- English proof (translation)
Rewrite using `[D.host.toHostAx.finrank_cmField]`. Simplify using `only [Formalism.BasicNotions.Ranks.f, Formalism.BasicNotions.Ranks.n]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem finrank_eq : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  rw [D.host.toHostAx.finrank_cmField]
  simp only [Formalism.BasicNotions.Ranks.f, Formalism.BasicNotions.Ranks.n]
  ring

/- English proof (translation)
Use `D.host.toHostAx.isCMField_hostE` as an intermediate fact. Establish `h1` using `NumberField.IsTotallyComplex.finrank (K := D.host.E)`. Establish `h2` using `GlobalTheory.TypeAsm.HostArith.finrank_eq D`. Unfold `Formalism.HermitianLatticesTheory.fDeg`. Rewrite using `[NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, NumberField.IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem fDeg_eq : Formalism.HermitianLatticesTheory.fDeg D.host.E = D.R.f := by
  have := D.host.toHostAx.isCMField_hostE
  have h1 := NumberField.IsTotallyComplex.finrank (K := D.host.E)
  have h2 := GlobalTheory.TypeAsm.HostArith.finrank_eq D
  unfold Formalism.HermitianLatticesTheory.fDeg
  rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    NumberField.IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
  omega

end GlobalTheory.TypeAsm.HostArith

namespace GlobalTheory.TypeAsm.HostArith

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

/- English proof (translation)
Establish `h1` using `GlobalTheory.TypeAsm.HostArith.fDeg_eq D`. Establish `h2` using `GlobalTheory.TypeAsm.HostArith.finrank_eq D`. Unfold `Formalism.HermitianLatticesTheory.vInv Formalism.BasicNotions.Host.v Formalism.BasicNotions.Host.rdE`. Rewrite using `[h1, h2]`. Use `push_cast`.

Both sides reduce to the same expression.
-/
theorem vInv_eq : Formalism.HermitianLatticesTheory.vInv D.host.E = D.host.v := by
  have h1 := GlobalTheory.TypeAsm.HostArith.fDeg_eq D
  have h2 := GlobalTheory.TypeAsm.HostArith.finrank_eq D
  unfold Formalism.HermitianLatticesTheory.vInv Formalism.BasicNotions.Host.v Formalism.BasicNotions.Host.rdE
  rw [h1, h2]
  push_cast
  rfl

/- English proof (translation)
Use `D.host.toHostAx.isCMField_hostE` as an intermediate fact. Rewrite using `[← IsFractionRing.finrank_eq (𝓞 D.host.F) D.host.F (𝓞 D.host.E) D.host.E]`. Conclude with `Algebra.IsQuadraticExtension.finrank_eq_two _ _`.
-/
theorem finrank_O : Module.finrank (𝓞 D.host.F) (𝓞 D.host.E) = 2 := by
  have := D.host.toHostAx.isCMField_hostE
  rw [← IsFractionRing.finrank_eq (𝓞 D.host.F) D.host.F (𝓞 D.host.E) D.host.E]
  exact Algebra.IsQuadraticExtension.finrank_eq_two _ _

/- English proof (translation)
Use `D.host.toHostAx.isCMField_hostE` as an intermediate fact. Unfold `dI`. Rewrite using `[Ideal.absNorm_algebraMap, GlobalTheory.TypeAsm.HostArith.finrank_O, NumberField.absNorm_differentIdeal D.host.F (𝓞 D.host.F), hd]`. Use `push_cast`. Rewrite using `[abs_pow, Nat.cast_natAbs, Int.cast_abs]`.
-/
private theorem absNorm_dI_eq_abs_discr_of_discr_eq_sq (hd : NumberField.discr D.host.E = NumberField.discr D.host.F ^ 2) :
    (Ideal.absNorm (dI D) : ℝ) = |(NumberField.discr D.host.E : ℝ)| := by
  have := D.host.toHostAx.isCMField_hostE
  unfold dI
  rw [Ideal.absNorm_algebraMap, GlobalTheory.TypeAsm.HostArith.finrank_O,
    NumberField.absNorm_differentIdeal D.host.F (𝓞 D.host.F), hd]
  push_cast
  rw [abs_pow, Nat.cast_natAbs, Int.cast_abs]

/- English proof (translation)
Establish `h` using `D.host.toHostAx.der.rd_sq_ge`. Establish `ho : (1 : ℝ) ≤ D.R.toFrame.ord` using `by exact_mod_cast D.R.toFrame.ord_pos`. Establish `hrd : D.host.rdE = D.host.toHostRaw.rd` using `rfl`. Establish `hnn : 0 ≤ D.host.rdE` using `by unfold Formalism.BasicNotions.Host.rdE; positivity`. Rewrite `h` using `[← hrd]`.

Unfold `Formalism.BasicNotions.Host.v`. Use the polynomial consequences of the given equalities and inequalities.
-/
private theorem one_le_host_v : 1 ≤ D.host.v := by
  have h := D.host.toHostAx.der.rd_sq_ge
  have ho : (1 : ℝ) ≤ D.R.toFrame.ord := by exact_mod_cast D.R.toFrame.ord_pos
  have hrd : D.host.rdE = D.host.toHostRaw.rd := rfl
  have hnn : 0 ≤ D.host.rdE := by unfold Formalism.BasicNotions.Host.rdE; positivity
  rw [← hrd] at h
  unfold Formalism.BasicNotions.Host.v
  nlinarith

/- English proof (translation)
Rewrite using `[absNorm_dI_eq_abs_discr_of_discr_eq_sq D hd]`. Establish `h2` using `GlobalTheory.TypeAsm.HostArith.finrank_eq D`. Establish `hf : (0 : ℝ) < ((2 * D.R.f : ℕ) : ℝ)`. Rewrite using `[← h2]`. Conclude with `Module.finrank_pos` after adjusting the coercions.

Establish `hv : 2 * D.host.v = D.host.rdE` using `by unfold Formalism.BasicNotions.Host.v; ring`. Rewrite using `[hv]`. Unfold `Formalism.BasicNotions.Host.rdE`. Rewrite using `[h2, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _), one_div, inv_mul_cancel₀ hf.ne', Real.rpow_one]`.
-/
theorem absNorm_dI (hd : NumberField.discr D.host.E = NumberField.discr D.host.F ^ 2) :
    (Ideal.absNorm (dI D) : ℝ) = (2 * D.host.v) ^ (2 * D.R.f) := by
  rw [absNorm_dI_eq_abs_discr_of_discr_eq_sq D hd]
  have h2 := GlobalTheory.TypeAsm.HostArith.finrank_eq D
  have hf : (0 : ℝ) < ((2 * D.R.f : ℕ) : ℝ) := by
    rw [← h2]; exact_mod_cast Module.finrank_pos
  have hv : 2 * D.host.v = D.host.rdE := by unfold Formalism.BasicNotions.Host.v; ring
  rw [hv]
  unfold Formalism.BasicNotions.Host.rdE
  rw [h2, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _), one_div,
    inv_mul_cancel₀ hf.ne', Real.rpow_one]

/- English proof (translation)
Use `D.host.toHostAx.isCMField_hostE` as an intermediate fact. Introduce `x hx`. Establish `key : dI D ≤ Ideal.comap (NumberField.IsCMField.ringOfIntegersComplexConj D.host.E) (dI D)` using `by show Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) _ ≤ _`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `i hi`.

Simplify using `only [Ideal.mem_comap]`. Rewrite using `[AlgEquiv.commutes]`. Conclude with `Ideal.mem_map_of_mem _ hi`. Conclude with `⟨NumberField.IsCMField.ringOfIntegersComplexConj D.host.E x, key hx, rfl⟩`.
-/
theorem dI_star : ∀ x ∈ dI D, ∃ y ∈ dI D, (y : D.host.E) = star (x : D.host.E) := by
  have := D.host.toHostAx.isCMField_hostE
  intro x hx

  have key : dI D ≤ Ideal.comap (NumberField.IsCMField.ringOfIntegersComplexConj D.host.E) (dI D) := by
    show Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) _ ≤ _
    rw [Ideal.map_le_iff_le_comap]
    intro i hi
    simp only [Ideal.mem_comap]
    rw [AlgEquiv.commutes]
    exact Ideal.mem_map_of_mem _ hi
  exact ⟨NumberField.IsCMField.ringOfIntegersComplexConj D.host.E x, key hx, rfl⟩

/- English proof (translation)
Introduce `h`. Establish `h1` using `absNorm_dI D hd`. Rewrite `h1` using `[h, Ideal.absNorm_bot, Nat.cast_zero]`. Establish `hv` using `one_le_host_v D`. Establish `: (0 : ℝ) < (2 * D.host.v) ^ (2 * D.R.f)` using `pow_pos (by linarith) _`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem dI_ne_bot (hd : NumberField.discr D.host.E = NumberField.discr D.host.F ^ 2) : dI D ≠ ⊥ := by
  intro h
  have h1 := absNorm_dI D hd
  rw [h, Ideal.absNorm_bot, Nat.cast_zero] at h1
  have hv := one_le_host_v D
  have : (0 : ℝ) < (2 * D.host.v) ^ (2 * D.R.f) := pow_pos (by linarith) _
  linarith

/- English proof (translation)
Rewrite using `[(VS D).rank_eq]`. Establish `h` using `D.sp.Y_rank 0 (Nat.zero_le _)`. Take `⟨j, hj⟩` from `D.R.m_even`. Establish `hm2` using `D.R.two_le_m`. Simplify using `only [Formalism.BasicNotions.Ranks.rankY, Formalism.BasicNotions.Ranks.r, Formalism.BasicNotions.Ranks.rS] at h ⊢`.

Use `show (D.sp.Y 0).rank = _`. Rewrite using `[h]`. Use linear arithmetic over natural numbers and integers.
-/
theorem rank_VS : Module.finrank D.host.E (VS D).V = 2 * D.R.rS + D.R.k + 1 := by
  rw [(VS D).rank_eq]
  have h := D.sp.Y_rank 0 (Nat.zero_le _)
  obtain ⟨j, hj⟩ := D.R.m_even
  have hm2 := D.R.two_le_m
  simp only [Formalism.BasicNotions.Ranks.rankY, Formalism.BasicNotions.Ranks.r, Formalism.BasicNotions.Ranks.rS] at h ⊢
  show (D.sp.Y 0).rank = _
  rw [h]
  omega

/- English proof (translation)
Establish `h0` using `(D.host.g_prime 0).two_le`. Establish `h1` using `(D.host.g_prime 1).two_le`. Use `show 2 ≤ D.host.g 0 * D.host.g 1`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem two_le_gS : 2 ≤ gS D := by
  have h0 := (D.host.g_prime 0).two_le
  have h1 := (D.host.g_prime 1).two_le
  show 2 ≤ D.host.g 0 * D.host.g 1
  nlinarith

/- English proof (translation)
Establish `hP` using `(HostArith.places D).2`. Establish `hb : Function.Bijective (fun τ => NumberField.InfinitePlace.mk (embS D τ))` using `⟨fun a b h => (hP _).unique h rfl, fun w => (hP w).exists⟩`. Rewrite using `[Fintype.card_of_bijective hb]`. Conclude with `HostArith.fDeg_eq D`.
-/
private theorem card_Tau_eq_f : Fintype.card D.what₂.Tau = D.R.f := by
  have hP := (HostArith.places D).2
  have hb : Function.Bijective (fun τ => NumberField.InfinitePlace.mk (embS D τ)) :=
    ⟨fun a b h => (hP _).unique h rfl, fun w => (hP w).exists⟩
  rw [Fintype.card_of_bijective hb]
  exact HostArith.fDeg_eq D

end GlobalTheory.TypeAsm.HostArith

namespace GlobalTheory.TypeAsm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `D large₂ hStd`. Take `⟨C', Cl, Cg, cb, Cw, cT, CT, C0, hK⟩` from `hStd`. Take `⟨⟨-, hD0, -⟩, -⟩` from `hK`. Take `⟨-, -, -, -, -, -, -, -, hsplit, -⟩` from `hD0`. Establish `hd : NumberField.discr D.host.E = NumberField.discr D.host.F ^ 2` using `D.host.toHostAx.der.discr_sq`.

Conclude with `⟨D.sp.cm.cmUnram, HostArith.places D, HostArith.vInv_eq D, HostArith.one_le_host_v D, HostArith.fDeg_eq D, HostArith.card_Tau_eq_f D, HostArith.finrank_eq D, HostArith.dI_ne_bot D hd, HostArith.dI_star D, HostArith.absNorm_dI D hd, HostArith.rank_VS D, HostArith.two_le_gS D, fun …`.
-/
theorem hostC : HostC := by
  intro D large₂ hStd
  obtain ⟨C', Cl, Cg, cb, Cw, cT, CT, C0, hK⟩ := hStd
  obtain ⟨⟨-, hD0, -⟩, -⟩ := hK
  obtain ⟨-, -, -, -, -, -, -, -, hsplit, -⟩ := hD0
  have hd : NumberField.discr D.host.E = NumberField.discr D.host.F ^ 2 := D.host.toHostAx.der.discr_sq
  exact ⟨D.sp.cm.cmUnram, HostArith.places D, HostArith.vInv_eq D, HostArith.one_le_host_v D,
    HostArith.fDeg_eq D, HostArith.card_Tau_eq_f D, HostArith.finrank_eq D, HostArith.dI_ne_bot D hd,
    HostArith.dI_star D, HostArith.absNorm_dI D hd, HostArith.rank_VS D, HostArith.two_le_gS D,
    fun u => ⟨(D.mem u).A.T_prime, (hsplit u).1⟩⟩

end GlobalTheory.TypeAsm
