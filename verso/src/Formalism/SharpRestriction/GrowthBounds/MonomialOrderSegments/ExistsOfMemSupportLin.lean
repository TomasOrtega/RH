import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.TestBoundOfRhoAndNormSets
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.SegDefs

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

variable {K : Type} [Field K]

/- English proof (translation)
Use `conv_lhs => rw [Z.as_sum]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun ζ _ => ?_` and prove the remaining obligations. Rewrite using `[show monomial ζ (Z.coeff ζ) = Z.coeff ζ • monomial ζ (1 : K) by rw [smul_monomial, smul_eq_mul, mul_one], map_smul]`.
-/
theorem lin_eq_sum {σ τ : Type} (T : MvPolynomial σ K →ₗ[K] MvPolynomial τ K) (Z : MvPolynomial σ K) :
    T Z = ∑ ζ ∈ Z.support, Z.coeff ζ • T (monomial ζ 1) := by
  conv_lhs => rw [Z.as_sum]
  rw [map_sum]
  refine Finset.sum_congr rfl fun ζ _ => ?_
  rw [show monomial ζ (Z.coeff ζ) = Z.coeff ζ • monomial ζ (1 : K) by rw [smul_monomial, smul_eq_mul, mul_one], map_smul]

/- English proof (translation)
Rewrite `h` using `[lin_eq_sum T Z]`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Rewrite `h` using `[mem_support_iff, coeff_sum]`. Apply `h` to reduce the goal to its premises.

Use `Finset.sum_eq_zero fun ζ hζ => ?_` and prove the remaining obligations. Establish `hz` using `hc ζ hζ`. Rewrite `hz` using `[mem_support_iff, not_not]`. Rewrite using `[coeff_smul, hz, smul_zero]`.
-/
theorem exists_of_mem_support_lin {σ τ : Type} (T : MvPolynomial σ K →ₗ[K] MvPolynomial τ K)
    (Z : MvPolynomial σ K) {ζ' : τ →₀ ℕ} (h : ζ' ∈ (T Z).support) :
    ∃ ζ ∈ Z.support, ζ' ∈ (T (monomial ζ 1)).support := by
  rw [lin_eq_sum T Z] at h
  by_contra hc
  push_neg at hc
  rw [mem_support_iff, coeff_sum] at h
  apply h
  refine Finset.sum_eq_zero fun ζ hζ => ?_
  have hz := hc ζ hζ
  rw [mem_support_iff, not_not] at hz
  rw [coeff_smul, hz, smul_zero]

namespace TwistData

variable (D : TwistData K)

/- English proof (translation)
The claim follows from `lin_eq_sum (D.ph p).toLinearMap Z`.
-/
theorem ph_lin_sum (p : ℕ) (Z : MvPolynomial (D.ML × Fin D.r) K) :
    D.ph p Z = ∑ ζ ∈ Z.support, Z.coeff ζ • D.ph p (monomial ζ 1) :=
  lin_eq_sum (D.ph p).toLinearMap Z

def iotaL : D.OL → D.ML := Sum.elim D.mb D.mlab

/- English proof (translation)
Apply the tactic sequence `rintro (a | a) (b | b) h <;> simp_all [iotaL, mb, mlab]`.
-/
theorem iotaL_injective : Function.Injective D.iotaL := by
  rintro (a | a) (b | b) h <;> simp_all [iotaL, mb, mlab]

/- English proof (translation)
The claim follows from `D.iotaL_injective.prodMap Function.injective_id`.
-/
theorem localizationToLaurent_injective : Function.Injective (Prod.map D.iotaL (id : Fin D.r → Fin D.r)) :=
  D.iotaL_injective.prodMap Function.injective_id

/- English proof (translation)
Use function extensionality and compare the values at `x`. Apply the tactic sequence `rcases x with b | t <;> rfl`.
-/
theorem msg_comp_iotaL : D.msg ∘ D.iotaL = D.osg := by
  funext x
  rcases x with b | t <;> rfl

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[Finset.mem_preimage]`. Break down `x with b | t` into its components or cases. Simplify using `[iotaL, TLset, Tset, mb, mlab]`. Simplify using `[iotaL, TLset, Tset, mb, mlab]`.
-/
theorem preimage_TLset (j : Fin D.J) (m : Fin D.r) :
    (D.TLset j m).preimage D.iotaL D.iotaL_injective.injOn = D.Tset j m := by
  ext x
  rw [Finset.mem_preimage]
  rcases x with b | t
  · simp [iotaL, TLset, Tset, mb, mlab]
  · simp [iotaL, TLset, Tset, mb, mlab]

/- English proof (translation)
Establish `hc : (D.ph p).comp (rename (Prod.map D.iotaL id)) = AlgHom.id K _`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Apply the tactic sequence `rintro ⟨b | t, a⟩ <;> simp [ph, iotaL, mb, mlab]`. Simplify using `using DFunLike.congr_fun hc G`.
-/
theorem ph_rename_iotaL (p : ℕ) (G : MvPolynomial (D.OL × Fin D.r) K) :
    D.ph p (rename (Prod.map D.iotaL id) G) = G := by
  have hc : (D.ph p).comp (rename (Prod.map D.iotaL id)) = AlgHom.id K _ := by
    apply MvPolynomial.algHom_ext
    rintro ⟨b | t, a⟩ <;> simp [ph, iotaL, mb, mlab]
  simpa using DFunLike.congr_fun hc G

/- English proof (translation)
The claim follows from `Finsupp.mapDomain_apply D.localizationToLaurent_injective α (Sum.inl b, a)`.
-/
theorem mapDomain_mb (α : D.EA) (b : D.Lb) (a : Fin D.r) :
    (α.mapDomain (Prod.map D.iotaL id)) (D.mb b, a) = α (Sum.inl b, a) :=
  Finsupp.mapDomain_apply D.localizationToLaurent_injective α (Sum.inl b, a)

/- English proof (translation)
The claim follows from `Finsupp.mapDomain_apply D.localizationToLaurent_injective α (Sum.inr t, a)`.
-/
theorem mapDomain_mlab (α : D.EA) (t : D.Tau) (a : Fin D.r) :
    (α.mapDomain (Prod.map D.iotaL id)) (D.mlab t, a) = α (Sum.inr t, a) :=
  Finsupp.mapDomain_apply D.localizationToLaurent_injective α (Sum.inr t, a)

/- English proof (translation)
Apply `Finsupp.mapDomain_notin_range` to reduce the goal to its premises. Introduce and unpack `⟨⟨i, a'⟩, h⟩`. Apply the tactic sequence `rcases i with b | t' <;> simp [iotaL, mb, mlab, mw] at h`.
-/
theorem mapDomain_mw (α : D.EA) (t : D.Tau) (a : Fin D.r) :
    (α.mapDomain (Prod.map D.iotaL id)) (D.mw t, a) = 0 := by
  apply Finsupp.mapDomain_notin_range
  rintro ⟨⟨i, a'⟩, h⟩
  rcases i with b | t' <;> simp [iotaL, mb, mlab, mw] at h

/- English proof (translation)
Apply `Finsupp.mapDomain_notin_range` to reduce the goal to its premises. Introduce and unpack `⟨⟨i, a'⟩, h⟩`. Apply the tactic sequence `rcases i with b | t' <;> simp [iotaL, mb, mlab, mtp] at h`.
-/
theorem mapDomain_mtp (α : D.EA) (t : D.Tau) (a : Fin D.r) :
    (α.mapDomain (Prod.map D.iotaL id)) (D.mtp t, a) = 0 := by
  apply Finsupp.mapDomain_notin_range
  rintro ⟨⟨i, a'⟩, h⟩
  rcases i with b | t' <;> simp [iotaL, mb, mlab, mtp] at h

/- English proof (translation)
Introduce and unpack `(⟨b', h1, e⟩ | ⟨m, e⟩ | ⟨m, e⟩)`. Simplify using `only [mb, Sum.inl.injEq] at e`. Conclude with `h (e ▸ h1)`. Simplify using `[mb, mlab] at e`. Simplify using `[mb, mtp] at e`.
-/
theorem notSegL_mb {j : Fin D.J} {b : D.Lb} (h : D.seg b ≠ j) : ¬ D.SegL j (D.mb b) := by
  rintro (⟨b', h1, e⟩ | ⟨m, e⟩ | ⟨m, e⟩)
  · simp only [mb, Sum.inl.injEq] at e
    exact h (e ▸ h1)
  · simp [mb, mlab] at e
  · simp [mb, mtp] at e

/- English proof (translation)
Introduce and unpack `(⟨b', h1, e⟩ | ⟨m', e⟩ | ⟨m', e⟩)`. Simplify using `[mb, mlab] at e`. Simplify using `only [mlab, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq] at e`. Conclude with `h e.1`. Simplify using `[mlab, mtp] at e`.
-/
theorem notSegL_mlab {j j' : Fin D.J} (m : Fin D.r) (h : j' ≠ j) : ¬ D.SegL j (D.mlab (j', m)) := by
  rintro (⟨b', h1, e⟩ | ⟨m', e⟩ | ⟨m', e⟩)
  · simp [mb, mlab] at e
  · simp only [mlab, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq] at e
    exact h e.1
  · simp [mlab, mtp] at e

/- English proof (translation)
Introduce and unpack `(⟨b', h1, e⟩ | ⟨m', e⟩ | ⟨m', e⟩)`. Simplify using `[mb, mtp] at e`. Simplify using `[mlab, mtp] at e`. Simplify using `only [mtp, Sum.inr.injEq, Prod.mk.injEq] at e`. Conclude with `h e.1`.
-/
theorem notSegL_mtp {j j' : Fin D.J} (m : Fin D.r) (h : j' ≠ j) : ¬ D.SegL j (D.mtp (j', m)) := by
  rintro (⟨b', h1, e⟩ | ⟨m', e⟩ | ⟨m', e⟩)
  · simp [mb, mtp] at e
  · simp [mlab, mtp] at e
  · simp only [mtp, Sum.inr.injEq, Prod.mk.injEq] at e
    exact h e.1

/- English proof (translation)
Introduce and unpack `(⟨b', h1, e⟩ | ⟨m', e⟩ | ⟨m', e⟩)`. Simplify using `[mb, mw] at e`. Simplify using `[mlab, mw] at e`. Simplify using `[mtp, mw] at e`.
-/
theorem notSegL_mw (j : Fin D.J) (t : D.Tau) : ¬ D.SegL j (D.mw t) := by
  rintro (⟨b', h1, e⟩ | ⟨m', e⟩ | ⟨m', e⟩)
  · simp [mb, mw] at e
  · simp [mlab, mw] at e
  · simp [mtp, mw] at e

/- English proof (translation)
Simplify using `only [TLset, Finset.mem_union, Finset.mem_image] at hi`. Break down `hi with ⟨b, hb, rfl⟩ | ⟨m', _, rfl⟩` into its components or cases. Simplify using `[LLj] at hb`. Conclude with `D.notSegL_mb (by rw [hb]; exact h)`. Conclude with `D.notSegL_mlab m' h`.
-/
theorem notSegL_of_mem_TLset {j j' : Fin D.J} (h : j' ≠ j) (m : Fin D.r) {i : D.ML}
    (hi : i ∈ D.TLset j' m) : ¬ D.SegL j i := by
  simp only [TLset, Finset.mem_union, Finset.mem_image] at hi
  rcases hi with ⟨b, hb, rfl⟩ | ⟨m', _, rfl⟩
  · simp [LLj] at hb
    exact D.notSegL_mb (by rw [hb]; exact h)
  · exact D.notSegL_mlab m' h

/- English proof (translation)
Simplify using `only [YPset, Finset.mem_union, Finset.mem_image] at hi`. Break down `hi with ⟨b, hb, rfl⟩ | ⟨m', _, rfl⟩` into its components or cases. Simplify using `[LLj] at hb`. Conclude with `D.notSegL_mb (by rw [hb]; exact h)`. Conclude with `D.notSegL_mtp m' h`.
-/
theorem notSegL_of_mem_YPset {j j' : Fin D.J} (h : j' ≠ j) (m : Fin D.r) {i : D.ML}
    (hi : i ∈ D.YPset j' m) : ¬ D.SegL j i := by
  simp only [YPset, Finset.mem_union, Finset.mem_image] at hi
  rcases hi with ⟨b, hb, rfl⟩ | ⟨m', _, rfl⟩
  · simp [LLj] at hb
    exact D.notSegL_mb (by rw [hb]; exact h)
  · exact D.notSegL_mtp m' h

/- English proof (translation)
Unfold `ldeg`. Conclude with `Finset.sum_congr rfl fun a _ => h a`.
-/
theorem ldeg_congr' {ζ ζ' : D.EM} {i : D.ML} (h : ∀ a, ζ' (i, a) = ζ (i, a)) : ldeg ζ' i = ldeg ζ i := by
  unfold ldeg; exact Finset.sum_congr rfl fun a _ => h a

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `hζ`. Use `⟨fun b hb => ?_, fun m => ?_, fun m a => ?_⟩` and prove the remaining obligations. Rewrite using `[D.ldeg_congr' (hag _ (D.notSegL_mb (by rw [hb]; exact h)))]`. Conclude with `h1 b hb`. Rewrite using `[D.ldeg_congr' (hag _ (D.notSegL_mlab m h))]`.

Conclude with `h2 m`. Rewrite using `[hag _ (D.notSegL_mtp m h)]`. Conclude with `h3 m a`.
-/
theorem PreE.of_agree {j j' : Fin D.J} (h : j' ≠ j) {ζ ζ' : D.EM} (hζ : D.PreE j' ζ)
    (hag : ∀ i, ¬ D.SegL j i → ∀ a, ζ' (i, a) = ζ (i, a)) : D.PreE j' ζ' := by
  obtain ⟨h1, h2, h3⟩ := hζ
  refine ⟨fun b hb => ?_, fun m => ?_, fun m a => ?_⟩
  · rw [D.ldeg_congr' (hag _ (D.notSegL_mb (by rw [hb]; exact h)))]
    exact h1 b hb
  · rw [D.ldeg_congr' (hag _ (D.notSegL_mlab m h))]
    exact h2 m
  · rw [hag _ (D.notSegL_mtp m h)]
    exact h3 m a

/- English proof (translation)
Take `⟨h1, h2, h3, h4⟩` from `hζ`. Use `⟨fun b hb => ?_, fun m => ?_, fun m => ?_, fun m hm a => ?_⟩` and prove the remaining obligations. Rewrite using `[D.ldeg_congr' (hag _ (D.notSegL_mb (by rw [hb]; exact h)))]`. Conclude with `h1 b hb`. Rewrite using `[D.ldeg_congr' (hag _ (D.notSegL_mlab m h)), D.ldeg_congr' (hag _ (D.notSegL_mtp m h))]`.

Conclude with `h2 m`. Rewrite using `[D.ldeg_congr' (hag _ (D.notSegL_mtp m h))]`. Conclude with `h3 m`. Rewrite using `[hag _ (D.notSegL_mtp m h)]`. Conclude with `h4 m hm a`.
-/
theorem PostE.of_agree {j j' : Fin D.J} (h : j' ≠ j) {ζ ζ' : D.EM} (hζ : D.PostE j' ζ)
    (hag : ∀ i, ¬ D.SegL j i → ∀ a, ζ' (i, a) = ζ (i, a)) : D.PostE j' ζ' := by
  obtain ⟨h1, h2, h3, h4⟩ := hζ
  refine ⟨fun b hb => ?_, fun m => ?_, fun m => ?_, fun m hm a => ?_⟩
  · rw [D.ldeg_congr' (hag _ (D.notSegL_mb (by rw [hb]; exact h)))]
    exact h1 b hb
  · rw [D.ldeg_congr' (hag _ (D.notSegL_mlab m h)), D.ldeg_congr' (hag _ (D.notSegL_mtp m h))]
    exact h2 m
  · rw [D.ldeg_congr' (hag _ (D.notSegL_mtp m h))]
    exact h3 m
  · rw [hag _ (D.notSegL_mtp m h)]
    exact h4 m hm a

def Inv (v : AddValuation K (WithTop ℚ)) (p : ℕ) (θ : Fin D.J → Fin D.r → ℝ)
    (Gt : MvPolynomial (D.OL × Fin D.r) K) (s : Finset (Fin D.J))
    (Z : MvPolynomial (D.ML × Fin D.r) K) : Prop :=
  Integral v Z ∧ D.ph p Z = Gt ∧
  (∀ ζ ∈ Z.support, (∀ t a, ζ (D.mw t, a) = 0) ∧ (∀ j ∈ s, D.PostE j ζ) ∧ (∀ j, j ∉ s → D.PreE j ζ)) ∧
  (∀ j ∈ s, ∀ m : Fin D.r, m.val + 2 ≤ D.r → vala D.msg (D.YPset j m) (θ j m) Z) ∧
  (∀ j, j ∉ s → ∀ m : Fin D.r, m.val + 2 ≤ D.r → vala D.msg (D.TLset j m) (θ j m) Z)

/- English proof (translation)
Use `⟨?_, D.ph_rename_iotaL p Gt, ?_, fun j hj => by simp at hj, ?_⟩` and prove the remaining obligations. Introduce `α`. Distinguish the cases in `hα : ∃ u, Finsupp.mapDomain (Prod.map D.iotaL id) u = α`. Take `⟨u, rfl⟩` from `hα`. Rewrite using `[coeff_rename_mapDomain _ D.localizationToLaurent_injective]`.

Conclude with `hGt.2 u`. Rewrite using `[coeff_rename_eq_zero _ _ _ (fun u hu => absurd ⟨u, hu⟩ hα), AddValuation.map_zero]`. Conclude with `le_top`. Introduce `ζ hζ`. Establish `hex : ∃ u ∈ Gt.support, Finsupp.mapDomain (Prod.map D.iotaL id) u = ζ`.

Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Rewrite `hζ` using `[mem_support_iff]`. Apply `hζ` to reduce the goal to its premises. Apply `coeff_rename_eq_zero` to reduce the goal to its premises.

Introduce `u hu`. Assume the negation of the conclusion as `hne`. Conclude with `hc u (mem_support_iff.mpr hne) hu`. Take `⟨u, hu, rfl⟩` from `hex`. Establish `hdeg` using `(mem_PolK_iff _ _).mp hGt.1 u hu`.

Use `⟨fun t a => D.mapDomain_mw u t a, fun j hj => by simp at hj, fun j _ => ⟨fun b _ => ?_, fun m => ?_, fun m a => D.mapDomain_mtp u _ a⟩⟩` and prove the remaining obligations. Establish `h1` using `hdeg (Sum.inl b)`. Unfold `ldeg at h1 ⊢`. Simplify using `only [mapDomain_mb]`. Conclude with `h1`.

Establish `h1` using `hdeg (Sum.inr (j, m))`. Unfold `ldeg at h1 ⊢`. Simplify using `only [mapDomain_mlab]`. Conclude with `h1`. Introduce `j _ m hm`.

Rewrite using `[vala_rename_iff D.iotaL D.iotaL_injective, msg_comp_iotaL, preimage_TLset]`. Conclude with `hval j m hm`.
-/
theorem inv_start (v : AddValuation K (WithTop ℚ)) (p : ℕ) (θ : Fin D.J → Fin D.r → ℝ)
    (Gt : MvPolynomial (D.OL × Fin D.r) K) (hGt : Gt ∈ PolO v D.r D.dO)
    (hval : ∀ (j : Fin D.J) (m : Fin D.r), m.val + 2 ≤ D.r → vala D.osg (D.Tset j m) (θ j m) Gt) :
    D.Inv v p θ Gt ∅ (rename (Prod.map D.iotaL id) Gt) := by
  refine ⟨?_, D.ph_rename_iotaL p Gt, ?_, fun j hj => by simp at hj, ?_⟩
  · intro α
    by_cases hα : ∃ u, Finsupp.mapDomain (Prod.map D.iotaL id) u = α
    · obtain ⟨u, rfl⟩ := hα
      rw [coeff_rename_mapDomain _ D.localizationToLaurent_injective]
      exact hGt.2 u
    · rw [coeff_rename_eq_zero _ _ _ (fun u hu => absurd ⟨u, hu⟩ hα), AddValuation.map_zero]
      exact le_top
  · intro ζ hζ
    have hex : ∃ u ∈ Gt.support, Finsupp.mapDomain (Prod.map D.iotaL id) u = ζ := by
      by_contra hc
      push_neg at hc
      rw [mem_support_iff] at hζ
      apply hζ
      apply coeff_rename_eq_zero
      intro u hu
      by_contra hne
      exact hc u (mem_support_iff.mpr hne) hu
    obtain ⟨u, hu, rfl⟩ := hex
    have hdeg := (mem_PolK_iff _ _).mp hGt.1 u hu
    refine ⟨fun t a => D.mapDomain_mw u t a, fun j hj => by simp at hj,
      fun j _ => ⟨fun b _ => ?_, fun m => ?_, fun m a => D.mapDomain_mtp u _ a⟩⟩
    · have h1 := hdeg (Sum.inl b)
      unfold ldeg at h1 ⊢
      simp only [mapDomain_mb]
      exact h1
    · have h1 := hdeg (Sum.inr (j, m))
      unfold ldeg at h1 ⊢
      simp only [mapDomain_mlab]
      exact h1
  · intro j _ m hm
    rw [vala_rename_iff D.iotaL D.iotaL_injective, msg_comp_iotaL, preimage_TLset]
    exact hval j m hm

/- English proof (translation)
Take `⟨hInt, hph, hsupp, hYP, hTL⟩` from `hZ`. Take `⟨Th, tI, tph, tsupp, tval, tS⟩` from `hSeg hD D hr hJ j`. Establish `hpre : ∀ ζ ∈ Z.support, D.PreE j ζ` using `fun ζ hζ => (hsupp ζ hζ).2.2 j hj`. Establish `hne : ∀ j', j' ∈ s → j' ≠ j` using `fun j' hj' he => hj (he ▸ hj')`. Use `⟨Th Z, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `α`. Rewrite using `[lin_eq_sum Th Z, coeff_sum]`. Apply `AddValuation.map_le_sum` to reduce the goal to its premises. Introduce `ζ hζ`. Rewrite using `[coeff_smul, smul_eq_mul, AddValuation.map_mul]`.

Conclude with `add_nonneg (hInt ζ) (tI ζ (hpre ζ hζ) α)`. Rewrite using `[lin_eq_sum Th Z, map_sum, ← hph, D.ph_lin_sum p Z]`. Use `Finset.sum_congr rfl fun ζ hζ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, tph ζ (hpre ζ hζ)]`. Introduce `ζ' hζ'`.

Take `⟨ζ, hζ, hζ'1⟩` from `exists_of_mem_support_lin Th Z hζ'`. Take `⟨hpost, hag⟩` from `tsupp ζ (hpre ζ hζ) ζ' hζ'1`. Take `⟨hw, hs, hns⟩` from `hsupp ζ hζ`. Use `⟨fun t a => ?_, fun j' hj' => ?_, fun j' hj' => ?_⟩` and prove the remaining obligations. Rewrite using `[hag _ (D.notSegL_mw j t) a]`.

Conclude with `hw t a`. Break down `Finset.mem_insert.mp hj' with h | hj's` into its components or cases. Rewrite using `[h]`. Conclude with `hpost`. Conclude with `PostE.of_agree D (hne j' hj's) (hs j' hj's) hag`.

Establish `hj's : j' ∉ s` using `fun h => hj' (Finset.mem_insert_of_mem h)`. Establish `hne' : j' ≠ j` using `fun he => hj' (he ▸ Finset.mem_insert_self j s)`. Conclude with `PreE.of_agree D hne' (hns j' hj's) hag`. Introduce `j' hj' m hm`. Break down `Finset.mem_insert.mp hj' with h | hj's` into its components or cases.

Substitute `h` using the available equality. Conclude with `tval Z hInt hpre m _ hm (hTL _ hj m hm)`. Conclude with `vala_of_le (tS _ (fun i hi => D.notSegL_of_mem_YPset (hne j' hj's) m hi) Z) (hYP j' hj's m hm)`. Introduce `j' hj' m hm`. Establish `hj's : j' ∉ s` using `fun h => hj' (Finset.mem_insert_of_mem h)`.

Establish `hne' : j' ≠ j` using `fun he => hj' (he ▸ Finset.mem_insert_self j s)`. Conclude with `vala_of_le (tS _ (fun i hi => D.notSegL_of_mem_TLset hne' m hi) Z) (hTL j' hj's m hm)`.
-/
theorem inv_step [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ} (hSeg : SegStep K v p) (hD : DVRHyp v p)
    (hr : 0 < D.r) (hJ : 0 < D.J) (θ : Fin D.J → Fin D.r → ℝ) (Gt : MvPolynomial (D.OL × Fin D.r) K)
    (s : Finset (Fin D.J)) (j : Fin D.J) (hj : j ∉ s) (Z : MvPolynomial (D.ML × Fin D.r) K)
    (hZ : D.Inv v p θ Gt s Z) : ∃ Z', D.Inv v p θ Gt (insert j s) Z' := by
  obtain ⟨hInt, hph, hsupp, hYP, hTL⟩ := hZ
  obtain ⟨Th, tI, tph, tsupp, tval, tS⟩ := hSeg hD D hr hJ j
  have hpre : ∀ ζ ∈ Z.support, D.PreE j ζ := fun ζ hζ => (hsupp ζ hζ).2.2 j hj
  have hne : ∀ j', j' ∈ s → j' ≠ j := fun j' hj' he => hj (he ▸ hj')
  refine ⟨Th Z, ?_, ?_, ?_, ?_, ?_⟩
  · intro α
    rw [lin_eq_sum Th Z, coeff_sum]
    apply AddValuation.map_le_sum
    intro ζ hζ
    rw [coeff_smul, smul_eq_mul, AddValuation.map_mul]
    exact add_nonneg (hInt ζ) (tI ζ (hpre ζ hζ) α)
  · rw [lin_eq_sum Th Z, map_sum, ← hph, D.ph_lin_sum p Z]
    refine Finset.sum_congr rfl fun ζ hζ => ?_
    rw [map_smul, tph ζ (hpre ζ hζ)]
  · intro ζ' hζ'
    obtain ⟨ζ, hζ, hζ'1⟩ := exists_of_mem_support_lin Th Z hζ'
    obtain ⟨hpost, hag⟩ := tsupp ζ (hpre ζ hζ) ζ' hζ'1
    obtain ⟨hw, hs, hns⟩ := hsupp ζ hζ
    refine ⟨fun t a => ?_, fun j' hj' => ?_, fun j' hj' => ?_⟩
    · rw [hag _ (D.notSegL_mw j t) a]
      exact hw t a
    · rcases Finset.mem_insert.mp hj' with h | hj's
      · rw [h]
        exact hpost
      · exact PostE.of_agree D (hne j' hj's) (hs j' hj's) hag
    · have hj's : j' ∉ s := fun h => hj' (Finset.mem_insert_of_mem h)
      have hne' : j' ≠ j := fun he => hj' (he ▸ Finset.mem_insert_self j s)
      exact PreE.of_agree D hne' (hns j' hj's) hag
  · intro j' hj' m hm
    rcases Finset.mem_insert.mp hj' with h | hj's
    · subst h
      exact tval Z hInt hpre m _ hm (hTL _ hj m hm)
    · exact vala_of_le (tS _ (fun i hi => D.notSegL_of_mem_YPset (hne j' hj's) m hi) Z) (hYP j' hj's m hm)
  · intro j' hj' m hm
    have hj's : j' ∉ s := fun h => hj' (Finset.mem_insert_of_mem h)
    have hne' : j' ≠ j := fun he => hj' (he ▸ Finset.mem_insert_self j s)
    exact vala_of_le (tS _ (fun i hi => D.notSegL_of_mem_TLset hne' m hi) Z) (hTL j' hj's m hm)

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact ⟨_, D.inv_start v p θ Gt hGt hval⟩`. Consider the case `insert j s hj ih`. Take `⟨Z, hZ⟩` from `ih`. Conclude with `D.inv_step hSeg hD hr hJ θ Gt s j hj Z hZ`.
-/
theorem inv_all [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ} (hSeg : SegStep K v p) (hD : DVRHyp v p)
    (hr : 0 < D.r) (hJ : 0 < D.J) (θ : Fin D.J → Fin D.r → ℝ) (Gt : MvPolynomial (D.OL × Fin D.r) K)
    (hGt : Gt ∈ PolO v D.r D.dO)
    (hval : ∀ (j : Fin D.J) (m : Fin D.r), m.val + 2 ≤ D.r → vala D.osg (D.Tset j m) (θ j m) Gt)
    (s : Finset (Fin D.J)) : ∃ Z, D.Inv v p θ Gt s Z := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨_, D.inv_start v p θ Gt hGt hval⟩
  | insert j s hj ih =>
    obtain ⟨Z, hZ⟩ := ih
    exact D.inv_step hSeg hD hr hJ θ Gt s j hj Z hZ

def splitE (p : ℕ) (ζ : D.EM) : D.EM :=
  Finsupp.equivFunOnFinite.symm fun x => Sum.elim (fun b => ζ (D.mb b, x.2))
    (Sum.elim (fun t => ζ (D.mlab t, x.2) % D.P p t)
      (Sum.elim (fun t => ζ (D.mw t, x.2) + ζ (D.mlab t, x.2) / D.P p t)
        (fun t => ζ (D.mtp t, x.2)))) x.1

/- English proof (translation)
Simplify using `[splitE, mb]`.
-/
theorem splitE_mb (p : ℕ) (ζ : D.EM) (b : D.Lb) (a : Fin D.r) :
    D.splitE p ζ (D.mb b, a) = ζ (D.mb b, a) := by simp [splitE, mb]

/- English proof (translation)
Simplify using `[splitE, mlab]`.
-/
theorem splitE_mlab (p : ℕ) (ζ : D.EM) (t : D.Tau) (a : Fin D.r) :
    D.splitE p ζ (D.mlab t, a) = ζ (D.mlab t, a) % D.P p t := by simp [splitE, mlab]

/- English proof (translation)
Simplify using `[splitE, mw]`.
-/
theorem splitE_mw (p : ℕ) (ζ : D.EM) (t : D.Tau) (a : Fin D.r) :
    D.splitE p ζ (D.mw t, a) = ζ (D.mw t, a) + ζ (D.mlab t, a) / D.P p t := by
  simp [splitE, mw]

/- English proof (translation)
Simplify using `[splitE, mtp]`.
-/
theorem splitE_mtp (p : ℕ) (ζ : D.EM) (t : D.Tau) (a : Fin D.r) :
    D.splitE p ζ (D.mtp t, a) = ζ (D.mtp t, a) := by simp [splitE, mtp]

/- English proof (translation)
Use extensionality with `⟨i, a⟩`. Break down `i with b | t` into its components or cases. Rewrite using `[phE_apply_inl, phE_apply_inl, splitE_mb]`. Rewrite using `[phE_apply_inr, phE_apply_inr, splitE_mlab, splitE_mw, splitE_mtp, mul_add]`. Use `Nat.mod_add_div (ζ (D.mlab t, a)) (D.P p t)` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem phE_splitE (p : ℕ) (ζ : D.EM) : D.phE p (D.splitE p ζ) = D.phE p ζ := by
  ext ⟨i, a⟩
  rcases i with b | t
  · rw [phE_apply_inl, phE_apply_inl, splitE_mb]
  · rw [phE_apply_inr, phE_apply_inr, splitE_mlab, splitE_mw, splitE_mtp, mul_add]
    have := Nat.mod_add_div (ζ (D.mlab t, a)) (D.P p t)
    linarith

def Sp (p : ℕ) : MvPolynomial (D.ML × Fin D.r) K →ₗ[K] MvPolynomial (D.ML × Fin D.r) K :=
  lsup fun ζ => monomial (D.splitE p ζ) 1

/- English proof (translation)
Rewrite using `[Sp, lsup_monomial, one_smul]`.
-/
theorem Sp_monomial (p : ℕ) (ζ : D.EM) : D.Sp p (monomial ζ (1 : K)) = monomial (D.splitE p ζ) 1 := by
  rw [Sp, lsup_monomial, one_smul]

/- English proof (translation)
Rewrite using `[Sp, lsup_apply, map_sum, ph_eq_sum]`. Use `Finset.sum_congr rfl fun ζ _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, ph_monomial, phE_splitE, smul_monomial, smul_eq_mul, mul_one]`.
-/
theorem ph_Sp (p : ℕ) (Z : MvPolynomial (D.ML × Fin D.r) K) : D.ph p (D.Sp p Z) = D.ph p Z := by
  rw [Sp, lsup_apply, map_sum, ph_eq_sum]
  refine Finset.sum_congr rfl fun ζ _ => ?_
  rw [map_smul, ph_monomial, phE_splitE, smul_monomial, smul_eq_mul, mul_one]

/- English proof (translation)
Introduce `α`. Rewrite using `[Sp, lsup_apply, coeff_sum]`. Apply `AddValuation.map_le_sum` to reduce the goal to its premises. Introduce `ζ _`. Rewrite using `[coeff_smul, coeff_monomial]`.

Use `split_ifs`. Rewrite using `[smul_eq_mul, mul_one]`. Conclude with `hZ ζ`. Rewrite using `[smul_zero, AddValuation.map_zero]`. Conclude with `le_top`.
-/
theorem integral_Sp (v : AddValuation K (WithTop ℚ)) (p : ℕ) {Z : MvPolynomial (D.ML × Fin D.r) K}
    (hZ : Integral v Z) : Integral v (D.Sp p Z) := by
  classical
  intro α
  rw [Sp, lsup_apply, coeff_sum]
  apply AddValuation.map_le_sum
  intro ζ _
  rw [coeff_smul, coeff_monomial]
  split_ifs
  · rw [smul_eq_mul, mul_one]
    exact hZ ζ
  · rw [smul_zero, AddValuation.map_zero]
    exact le_top

/- English proof (translation)
Establish `hP : ∀ t, 0 < D.P p t` using `fun t => by`. Unfold `P`. Conclude with `pow_pos hp _`. Use `⟨fun t a => ?_, fun j m hm a => ?_, fun b => ?_, fun t => ?_, fun t => ?_⟩` and prove the remaining obligations. Rewrite using `[splitE_mlab]`.

Conclude with `Nat.mod_lt _ (hP t)`. Rewrite using `[splitE_mtp]`. Conclude with `(hpost j).2.2.2 m hm a`. Rewrite using `[D.ldeg_congr' (fun a => D.splitE_mb p ζ b a)]`. Conclude with `(hpost (D.seg b)).1 b rfl`.

Take `⟨j, m⟩` from `t`. Establish `e1 : ldeg (D.splitE p ζ) (D.mlab (j, m)) + D.P p (j, m) * ldeg (D.splitE p ζ) (D.mw (j, m)) = ldeg ζ (D.mlab (j, m))`. Unfold `ldeg`. Simplify using `only [splitE_mlab, splitE_mw, hw, zero_add]`. Rewrite using `[Finset.mul_sum, ← Finset.sum_add_distrib]`.

Conclude with `Finset.sum_congr rfl fun a _ => Nat.mod_add_div _ _`. Rewrite using `[e1, D.ldeg_congr' (fun a => D.splitE_mtp p ζ (j, m) a)]`. Conclude with `(hpost j).2.1 m`. Take `⟨j, m⟩` from `t`. Rewrite using `[D.ldeg_congr' (fun a => D.splitE_mtp p ζ (j, m) a)]`.

Conclude with `(hpost j).2.2.1 m`.
-/
theorem goodE_splitE {p : ℕ} (hp : 0 < p) {ζ : D.EM} (hw : ∀ t a, ζ (D.mw t, a) = 0)
    (hpost : ∀ j, D.PostE j ζ) : D.GoodE p (D.splitE p ζ) := by
  have hP : ∀ t, 0 < D.P p t := fun t => by
    unfold P
    exact pow_pos hp _
  refine ⟨fun t a => ?_, fun j m hm a => ?_, fun b => ?_, fun t => ?_, fun t => ?_⟩
  · rw [splitE_mlab]
    exact Nat.mod_lt _ (hP t)
  · rw [splitE_mtp]
    exact (hpost j).2.2.2 m hm a
  · rw [D.ldeg_congr' (fun a => D.splitE_mb p ζ b a)]
    exact (hpost (D.seg b)).1 b rfl
  · obtain ⟨j, m⟩ := t
    have e1 : ldeg (D.splitE p ζ) (D.mlab (j, m)) + D.P p (j, m) * ldeg (D.splitE p ζ) (D.mw (j, m))
        = ldeg ζ (D.mlab (j, m)) := by
      unfold ldeg
      simp only [splitE_mlab, splitE_mw, hw, zero_add]
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a _ => Nat.mod_add_div _ _
    rw [e1, D.ldeg_congr' (fun a => D.splitE_mtp p ζ (j, m) a)]
    exact (hpost j).2.1 m
  · obtain ⟨j, m⟩ := t
    rw [D.ldeg_congr' (fun a => D.splitE_mtp p ζ (j, m) a)]
    exact (hpost j).2.2.1 m

def labB : D.ML → Bool := Sum.elim (fun _ => false) (Sum.elim (fun _ => true) (fun _ => false))

/- English proof (translation)
Use extensionality with `⟨i, a⟩`. Rewrite using `[Finsupp.add_apply]`. Break down `i with b | t | t | t` into its components or cases. Use `show D.splitE p α (D.mb b, a) = eIn _ α (D.mb b, a) + D.splitE p (eOut _ α) (D.mb b, a)`. Rewrite using `[splitE_mb, splitE_mb, eIn_apply, eOut_apply]`.

Simplify using `[labB, mb]`. Use `show D.splitE p α (D.mlab t, a) = eIn _ α (D.mlab t, a) + D.splitE p (eOut _ α) (D.mlab t, a)`. Rewrite using `[splitE_mlab, splitE_mlab, eIn_apply, eOut_apply]`. Simplify using `[labB, mlab]`. Use `show D.splitE p α (D.mw t, a) = eIn _ α (D.mw t, a) + D.splitE p (eOut _ α) (D.mw t, a)`.

Rewrite using `[splitE_mw, splitE_mw, eIn_apply, eOut_apply, eOut_apply]`. Simplify using `[labB, mw, mlab]`. Use `show D.splitE p α (D.mtp t, a) = eIn _ α (D.mtp t, a) + D.splitE p (eOut _ α) (D.mtp t, a)`. Rewrite using `[splitE_mtp, splitE_mtp, eIn_apply, eOut_apply]`. Simplify using `[labB, mtp]`.
-/
theorem splitE_eq (p : ℕ) (α : D.EM) :
    D.splitE p α = eIn (fun i => D.labB i = true) α + D.splitE p (eOut (fun i => D.labB i = true) α) := by
  ext ⟨i, a⟩
  rw [Finsupp.add_apply]
  rcases i with b | t | t | t
  · show D.splitE p α (D.mb b, a) = eIn _ α (D.mb b, a) + D.splitE p (eOut _ α) (D.mb b, a)
    rw [splitE_mb, splitE_mb, eIn_apply, eOut_apply]
    simp [labB, mb]
  · show D.splitE p α (D.mlab t, a) = eIn _ α (D.mlab t, a) + D.splitE p (eOut _ α) (D.mlab t, a)
    rw [splitE_mlab, splitE_mlab, eIn_apply, eOut_apply]
    simp [labB, mlab]
  · show D.splitE p α (D.mw t, a) = eIn _ α (D.mw t, a) + D.splitE p (eOut _ α) (D.mw t, a)
    rw [splitE_mw, splitE_mw, eIn_apply, eOut_apply, eOut_apply]
    simp [labB, mw, mlab]
  · show D.splitE p α (D.mtp t, a) = eIn _ α (D.mtp t, a) + D.splitE p (eOut _ α) (D.mtp t, a)
    rw [splitE_mtp, splitE_mtp, eIn_apply, eOut_apply]
    simp [labB, mtp]

/- English proof (translation)
Simplify using `only [Yset, wSet, Finset.mem_union, Finset.mem_image] at hi`. Apply the tactic sequence `rcases hi with (⟨m', _, rfl⟩ | ⟨b, _, rfl⟩) | ⟨m', _, rfl⟩ <;> simp [labB, mw, mb, mtp]`.
-/
theorem not_labB_of_mem_Yset {j : Fin D.J} {m : Fin D.r} {i : D.ML} (hi : i ∈ D.Yset j m) :
    ¬ D.labB i = true := by
  simp only [Yset, wSet, Finset.mem_union, Finset.mem_image] at hi
  rcases hi with (⟨m', _, rfl⟩ | ⟨b, _, rfl⟩) | ⟨m', _, rfl⟩ <;> simp [labB, mw, mb, mtp]

/- English proof (translation)
Establish `key : D.Sp p Z = ∑ μ ∈ Z.support.image (eOut (fun i => D.labB i = true)), coefOut (fun i => D.labB i = true) μ Z * monomial (D.splitE p μ) 1`. Simplify using `only [coefOut, Finset.sum_mul, ite_mul, zero_mul]`. Rewrite using `[Finset.sum_comm, Sp, lsup_apply]`. Use `Finset.sum_congr rfl fun α hα => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_ite_eq, if_pos (Finset.mem_image_of_mem _ hα), monomial_mul, mul_one, ← splitE_eq, smul_monomial, smul_eq_mul, mul_one]`.

Establish `hle : valS D.msg (D.Yset j m) Z ≤ valS D.msg (D.Yset j m) (D.Sp p Z)`. Rewrite using `[key]`. Use `Finset.sum_induction _ (fun F => valS D.msg (D.Yset j m) Z ≤ valS D.msg (D.Yset j m) F) (fun F G hF hG => le_trans (le_min hF hG) (valS_add_le _ _ _ _)) ?_ ?_` and prove the remaining obligations. Simplify using `[valS]`. Introduce `μ hμ`.

Establish `h1` using `valS_coefOut_le (K := K) (r := D.r) (fun i => D.labB i = true) D.msg (D.Yset j m) (fun i hi => D.not_labB_of_mem_Yset hi) μ Z`. Establish `h2 : 0 ≤ valS D.msg (D.Yset j m) (monomial (D.splitE p μ) (1 : K))`. Apply `valS_monomial_nonneg_of_vec` to reduce the goal to its premises. Introduce `i a h`. Break down `i with b | t` into its components or cases.

It suffices to derive a contradiction. Apply `h` to reduce the goal to its premises. Take `⟨α, _, rfl⟩` from `Finset.mem_image.mp hμ`. Use `show D.splitE p (eOut _ α) (D.mb b, a) = 0`. Rewrite using `[splitE_mb, eOut_apply]`.

Simplify using `[labB, mb]`. Both sides reduce to the same expression. Combine the equalities or inequalities in the displayed calculation. Conclude with `le_trans hZ (toR_mono hle)`.
-/
theorem vala_Sp (p : ℕ) (j : Fin D.J) (m : Fin D.r) {θ : ℝ} {Z : MvPolynomial (D.ML × Fin D.r) K}
    (hZ : vala D.msg (D.Yset j m) θ Z) : vala D.msg (D.Yset j m) θ (D.Sp p Z) := by
  have key : D.Sp p Z = ∑ μ ∈ Z.support.image (eOut (fun i => D.labB i = true)),
      coefOut (fun i => D.labB i = true) μ Z * monomial (D.splitE p μ) 1 := by
    simp only [coefOut, Finset.sum_mul, ite_mul, zero_mul]
    rw [Finset.sum_comm, Sp, lsup_apply]
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_image_of_mem _ hα), monomial_mul, mul_one,
      ← splitE_eq, smul_monomial, smul_eq_mul, mul_one]
  have hle : valS D.msg (D.Yset j m) Z ≤ valS D.msg (D.Yset j m) (D.Sp p Z) := by
    rw [key]
    refine Finset.sum_induction _ (fun F => valS D.msg (D.Yset j m) Z ≤ valS D.msg (D.Yset j m) F)
      (fun F G hF hG => le_trans (le_min hF hG) (valS_add_le _ _ _ _)) ?_ ?_
    · simp [valS]
    · intro μ hμ
      have h1 := valS_coefOut_le (K := K) (r := D.r) (fun i => D.labB i = true) D.msg (D.Yset j m)
        (fun i hi => D.not_labB_of_mem_Yset hi) μ Z
      have h2 : 0 ≤ valS D.msg (D.Yset j m) (monomial (D.splitE p μ) (1 : K)) := by
        apply valS_monomial_nonneg_of_vec
        intro i a h
        rcases i with b | t
        · exfalso
          apply h
          obtain ⟨α, _, rfl⟩ := Finset.mem_image.mp hμ
          show D.splitE p (eOut _ α) (D.mb b, a) = 0
          rw [splitE_mb, eOut_apply]
          simp [labB, mb]
        · rfl
      calc valS D.msg (D.Yset j m) Z = valS D.msg (D.Yset j m) Z + 0 := (add_zero _).symm
        _ ≤ _ := add_le_add h1 h2
        _ ≤ _ := valS_mul_le _ _ _ _
  exact le_trans hZ (toR_mono hle)

/- English proof (translation)
Introduce `i hi`. Simplify using `only [YPset, Yset, Finset.mem_union] at hi ⊢`. The claim follows by propositional logic.
-/
theorem YPset_subset_Yset (j : Fin D.J) (m : Fin D.r) : D.YPset j m ⊆ D.Yset j m := by
  intro i hi
  simp only [YPset, Yset, Finset.mem_union] at hi ⊢
  tauto

/- English proof (translation)
Simplify using `only [Yset, YPset, Finset.mem_union] at hi hn`. Break down `hi with (hw | hb) | ht` into its components or cases. Simplify using `only [wSet, Finset.mem_image] at hw`. Take `⟨m', _, rfl⟩` from `hw`. Both sides reduce to the same expression.

Conclude with `absurd (Or.inl hb) hn`. Conclude with `absurd (Or.inr ht) hn`.
-/
theorem msg_of_mem_Yset {j : Fin D.J} {m : Fin D.r} {i : D.ML} (hi : i ∈ D.Yset j m)
    (hn : i ∉ D.YPset j m) : D.msg i = true := by
  simp only [Yset, YPset, Finset.mem_union] at hi hn
  rcases hi with (hw | hb) | ht
  · simp only [wSet, Finset.mem_image] at hw
    obtain ⟨m', _, rfl⟩ := hw
    rfl
  · exact absurd (Or.inl hb) hn
  · exact absurd (Or.inr ht) hn

end TwistData

/- English proof (translation)
Introduce `hD D hr hJ θ Gt hGt hval`. Use `haveI : NeZero D.r := ⟨by omega⟩`. Take `⟨Z, hi, hph, hsup, hY, -⟩` from `D.inv_all hSeg hD hr hJ θ Gt hGt hval Finset.univ`. Establish `hp : 0 < p` using `hD.prime.pos`. Use `⟨D.Sp p Z, D.integral_Sp v p hi, ?_, by rw [D.ph_Sp, hph], ?_⟩` and prove the remaining obligations.

Introduce `ζ' hζ'`. Take `⟨ζ, hζ, h2⟩` from `exists_of_mem_support_lin (D.Sp p) Z hζ'`. Rewrite `h2` using `[D.Sp_monomial]`. Establish `h3` using `support_monomial_subset h2`. Rewrite `h3` using `[Finset.mem_singleton]`.

Rewrite using `[h3]`. Conclude with `D.goodE_splitE hp (hsup ζ hζ).1 fun j => (hsup ζ hζ).2.1 j (Finset.mem_univ j)`. Introduce `j m hm`. Use `D.vala_Sp p j m ?_` and prove the remaining obligations. Conclude with `vala_superset_vec hV2 (D.YPset_subset_Yset j m) (fun i hi hn => D.msg_of_mem_Yset hi hn) (hY j (Finset.mem_univ j) m hm)`.
-/
theorem stepC_of [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ} (hV2 : V2 K)
    (hSeg : SegStep K v p) : StepC K v p := by
  intro hD D hr hJ θ Gt hGt hval
  haveI : NeZero D.r := ⟨by omega⟩
  obtain ⟨Z, hi, hph, hsup, hY, -⟩ := D.inv_all hSeg hD hr hJ θ Gt hGt hval Finset.univ
  have hp : 0 < p := hD.prime.pos
  refine ⟨D.Sp p Z, D.integral_Sp v p hi, ?_, by rw [D.ph_Sp, hph], ?_⟩
  · intro ζ' hζ'
    obtain ⟨ζ, hζ, h2⟩ := exists_of_mem_support_lin (D.Sp p) Z hζ'
    rw [D.Sp_monomial] at h2
    have h3 := support_monomial_subset h2
    rw [Finset.mem_singleton] at h3
    rw [h3]
    exact D.goodE_splitE hp (hsup ζ hζ).1 fun j => (hsup ζ hζ).2.1 j (Finset.mem_univ j)
  · intro j m hm
    refine D.vala_Sp p j m ?_
    exact vala_superset_vec hV2 (D.YPset_subset_Yset j m) (fun i hi hn => D.msg_of_mem_Yset hi hn)
      (hY j (Finset.mem_univ j) m hm)

end Formalism.MainNotions.PlaneGram
