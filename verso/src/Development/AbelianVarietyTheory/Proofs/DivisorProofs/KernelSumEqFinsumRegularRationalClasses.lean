import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumEqFinsumConjugacyClassesCentraliserCosetsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldDoubleCosetClassSumToSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteUnitaryFinitePartMulInjectiveRangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDoubleCosetRationalProductOfLocalLevelsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDefiniteUnitaryRationalInfConjLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteRationalPointsSupportDefiniteUnitaryTestFuStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeparableCharpolyOfTestFunctionNeZeroRegularPlacStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.Regroup

/- English proof (translation)
The claim follows from `GlobalTheory.T.finsum_eq_finsum_conjugacyClasses_centraliserCosets a ha`.
-/
theorem finsum_classes {H : Type} [Group H] (a : H → ℂ) (ha : (Function.support a).Finite) :
    ∑ᶠ γ, a γ = ∑ᶠ c : TwCl (MonoidHom.id H),
      ∑ᶠ δ : H ⧸ twCent (MonoidHom.id H) c.rep, a (Quotient.out δ * c.rep * (Quotient.out δ)⁻¹) :=
  GlobalTheory.T.finsum_eq_finsum_conjugacyClasses_centraliserCosets a ha

/- English proof (translation)
The claim follows from `GlobalTheory.T.unfold_doubleCoset_classSum_to_subgroup ι hι Γ hΓ T Γ' hΓ' K u hu h1 h2 h3`.
-/
theorem unfold {G H : Type} [Group G] [Group H] (ι : H →* G) (hι : Function.Injective ι) (Γ : Subgroup G)
    (hΓ : ∀ g, g ∈ Γ ↔ ∃ h, ι h = g) (T : Subgroup H) (Γ' : Subgroup G) (hΓ' : ∀ g, g ∈ Γ' ↔ ∃ t ∈ T, ι t = g)
    (K : Subgroup G) (u : G → ℂ) (hu : ∀ t ∈ T, ∀ k ∈ K, ∀ g, u (ι t * g * k) = u g)
    (h1 : Finite (DoubleCoset.Quotient (Γ : Set G) (K : Set G)))
    (h2 : ∀ x : G, Finite ↥(Γ ⊓ K.map (MulAut.conj x).toMonoidHom))
    (h3 : ∀ x : G, {δ : H ⧸ T | u ((ι (Quotient.out δ))⁻¹ * x) ≠ 0}.Finite) :
    ∑ᶠ q : DoubleCoset.Quotient (Γ : Set G) (K : Set G),
      ((Nat.card ↥(Γ ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom) : ℂ))⁻¹ *
        ∑ᶠ δ : H ⧸ T, u ((ι (Quotient.out δ))⁻¹ * Quotient.out q) =
    ∑ᶠ q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G),
      ((Nat.card ↥(Γ' ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom) : ℂ))⁻¹ * u (Quotient.out q) :=
  GlobalTheory.T.unfold_doubleCoset_classSum_to_subgroup ι hι Γ hΓ T Γ' hΓ' K u hu h1 h2 h3

/- English proof (translation)
The claim follows from `GlobalTheory.T.definiteUnitaryFinitePart_mul_injective_range`.
-/
theorem finPt_props : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), (∀ a b : UE E n, finPt (a * b) = finPt a * finPt b) ∧ Function.Injective (finPt : UE E n → finU E n) ∧ ∀ x : finU E n, x ∈ ratFinU E n ↔ ∃ γ : UE E n, finPt γ = x :=
  GlobalTheory.T.definiteUnitaryFinitePart_mul_injective_range

/- English proof (translation)
The claim follows from `GlobalTheory.T.finite_doubleCoset_rational_productOfLocalLevels`.
-/
theorem finite_classes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → Finite (DoubleCoset.Quotient (ratFinU E n : Set (finU E n)) (globLev S K' : Set (finU E n))) :=
  GlobalTheory.T.finite_doubleCoset_rational_productOfLocalLevels

/- English proof (translation)
The claim follows from `GlobalTheory.T.finite_definiteUnitaryRational_inf_conj_level`.
-/
theorem finite_stab : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ x : finU E n, Finite ↥(ratFinU E n ⊓ (globLev S K').map (MulAut.conj x).toMonoidHom) :=
  GlobalTheory.T.finite_definiteUnitaryRational_inf_conj_level

/- English proof (translation)
The claim follows from `GlobalTheory.T.finite_rationalPoints_support_definiteUnitary_testFunction`.
-/
theorem finite_supp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → ∀ x : finU E n, {γ : UE E n | globFn S f (x⁻¹ * finPt γ * x) ≠ 0}.Finite :=
  GlobalTheory.T.finite_rationalPoints_support_definiteUnitary_testFunction

/- English proof (translation)
The claim follows from `GlobalTheory.T.separable_charpoly_of_testFunction_ne_zero_regularPlace`.
-/
theorem separable_of_globFn_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)) (f : ∀ w : Pl E, UL n w → ℂ), IsTest (KL n) K' f → ∀ w ∈ S, (∀ y, f w y ≠ 0 → y.1.val.charpoly.Separable) → ∀ (x : finU E n) (γ : UE E n), globFn S f (x⁻¹ * finPt γ * x) ≠ 0 → γ.1.val.charpoly.Separable :=
  GlobalTheory.T.separable_charpoly_of_testFunction_ne_zero_regularPlace

end GlobalTheory.BCT.Regroup

namespace GlobalTheory.BCT.Regroup

/- English proof (translation)
Use `Set.Finite.of_finite_image (f := fun δ : H ⧸ twCent (MonoidHom.id H) c => Quotient.out δ * c * (Quotient.out δ)⁻¹) (h4.subset ?_) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨δ, hδ, rfl⟩ show Φ (x⁻¹ * ι (Quotient.out δ * c * (Quotient.out δ)⁻¹) * x) ≠ 0`. Establish `hδ' : Φ (((ι (Quotient.out δ))⁻¹ * x)⁻¹ * ι c * ((ι (Quotient.out δ))⁻¹ * x)) ≠ 0` using `hδ`. Use `hδ' using 2` and compare the differences between its conclusion and the goal. Simplify using `only [map_mul, map_inv, _root_.mul_inv_rev, inv_inv]`.

Use `group`. Introduce `δ₁ _ δ₂ _ e`. Simplify using `only at e`. Rewrite using `[← Quotient.out_eq δ₁, ← Quotient.out_eq δ₂]`. Apply `QuotientGroup.eq.2` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `(Quotient.out δ₁)⁻¹ * Quotient.out δ₂ * c = c * ((Quotient.out δ₁)⁻¹ * Quotient.out δ₂)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem support_conj_finite {G H : Type} [Group G] [Group H] (ι : H →* G) (Φ : G → ℂ) (x : G)
    (h4 : {γ : H | Φ (x⁻¹ * ι γ * x) ≠ 0}.Finite) (c : H) :
    {δ : H ⧸ twCent (MonoidHom.id H) c | (fun g : G => Φ (g⁻¹ * ι c * g)) ((ι (Quotient.out δ))⁻¹ * x) ≠ 0}.Finite := by
  refine Set.Finite.of_finite_image (f := fun δ : H ⧸ twCent (MonoidHom.id H) c => Quotient.out δ * c * (Quotient.out δ)⁻¹)
    (h4.subset ?_) ?_
  · rintro _ ⟨δ, hδ, rfl⟩
    show Φ (x⁻¹ * ι (Quotient.out δ * c * (Quotient.out δ)⁻¹) * x) ≠ 0
    have hδ' : Φ (((ι (Quotient.out δ))⁻¹ * x)⁻¹ * ι c * ((ι (Quotient.out δ))⁻¹ * x)) ≠ 0 := hδ
    convert hδ' using 2
    simp only [map_mul, map_inv, _root_.mul_inv_rev, inv_inv]
    group
  · intro δ₁ _ δ₂ _ e
    simp only at e
    rw [← Quotient.out_eq δ₁, ← Quotient.out_eq δ₂]
    apply QuotientGroup.eq.2
    change (Quotient.out δ₁)⁻¹ * Quotient.out δ₂ * c = c * ((Quotient.out δ₁)⁻¹ * Quotient.out δ₂)
    calc (Quotient.out δ₁)⁻¹ * Quotient.out δ₂ * c
        = (Quotient.out δ₁)⁻¹ * (Quotient.out δ₂ * c * (Quotient.out δ₂)⁻¹) * Quotient.out δ₂ := by group
      _ = (Quotient.out δ₁)⁻¹ * (Quotient.out δ₁ * c * (Quotient.out δ₁)⁻¹) * Quotient.out δ₂ := by rw [e]
      _ = c * ((Quotient.out δ₁)⁻¹ * Quotient.out δ₂) := by group

/- English proof (translation)
Use `haveI := Fintype.ofFinite (DoubleCoset.Quotient (Γ : Set G) (K : Set G))`. Use `set D : DoubleCoset.Quotient (Γ : Set G) (K : Set G) → TwCl (MonoidHom.id H) → ℂ := fun q c => ∑ᶠ δ : H ⧸ twCent (MonoidHom.id H) c.rep, Φ ((Quotient.out q)⁻¹ * ι (Quotient.out δ * c.rep * (Quotient.out δ)⁻¹) * Quotient.out q) with hD`. Establish `s1 : ∀ q : DoubleCoset.Quotient (Γ : Set G) (K : Set G), ∑ᶠ γ : H, Φ ((Quotient.out q)⁻¹ * ι γ * Quotient.out q) * ψ γ = ∑ᶠ c : TwCl (MonoidHom.id H), ψ c.rep * D q c`. Introduce `q`. Rewrite using `[finsum_classes _ ((h4 (Quotient.out q)).subset fun γ hγ => left_ne_zero_of_mul hγ)]`.

Use `finsum_congr fun c => ?_` and prove the remaining obligations. Rewrite using `[hD, mul_finsum]`. Use `finsum_congr fun δ => ?_` and prove the remaining obligations. Establish `: ψ (Quotient.out δ * c.rep * (Quotient.out δ)⁻¹) = ψ c.rep`. Simplify using `using hψ c.rep (Quotient.out δ)⁻¹`.

Rewrite using `[this, mul_comm]`. Establish `hsupp : ∀ q : DoubleCoset.Quotient (Γ : Set G) (K : Set G), (Function.support fun c : TwCl (MonoidHom.id H) => ψ c.rep * D q c).Finite`. Introduce `q`. Use `((h4 (Quotient.out q)).image (fun γ => (Quot.mk _ γ : TwCl (MonoidHom.id H)))).subset ?_` and prove the remaining obligations. Introduce `(c : TwCl (MonoidHom.id H)) hc`.

Establish `hc' : D q c ≠ 0` using `right_ne_zero_of_mul hc`. Choose the witnesses or unpack the hypotheses as in `⟨δ, hδ⟩ : ∃ δ : H ⧸ twCent (MonoidHom.id H) c.rep, Φ ((Quotient.out q)⁻¹ * ι (Quotient.out δ * c.rep * (Quotient.out δ)⁻¹) * Quotient.out q) ≠ 0 := by`. Assume the negation of the conclusion as `hn`. Use `push_neg at hn`. Conclude with `hc' (by rw [hD]; simp only; rw [finsum_congr hn]; simp)`.

Use `⟨_, hδ, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Quot.mk _ (Quotient.out δ * c.rep * (Quotient.out δ)⁻¹) = c`. Conclude with `(Quot.sound ⟨Quotient.out δ, by simp [mul_assoc]; rfl⟩).trans (Quot.out_eq c)`. Repeatedly rewrite using `[s1]`. Rewrite using `[finsum_eq_sum_of_fintype]`.

Repeatedly rewrite using `[mul_finsum]`. Rewrite using `[← finsum_sum_comm]`. Use `finsum_congr fun c => ?_` and prove the remaining obligations. Establish `e2` using `unfold ι hι Γ hΓ (twCent (MonoidHom.id H) c.rep) (Γ ⊓ twCent (MonoidHom.id G) (ι c.rep)) (fun g => by`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨hg, hc⟩`. Take `⟨h, rfl⟩` from `(hΓ g).1 hg`. Use `⟨h, hι ?_, rfl⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `ι h * ι c.rep = ι c.rep * ι h at hc`. Express the relevant statement in the definitionally equal form `ι (h * c.rep) = ι (c.rep * h)`.

Rewrite using `[map_mul, map_mul, hc]`. Introduce and unpack `⟨t, ht, rfl⟩`. Use `⟨(hΓ _).2 ⟨t, rfl⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `ι t * ι c.rep = ι c.rep * ι t`. Establish `ht' : t * c.rep = c.rep * t` using `ht`.

Rewrite using `[← map_mul, ht', map_mul])`. Use `K (fun g => Φ (g⁻¹ * ι c.rep * g))`. Use the proof step `(fun t ht k hk g => by`. Establish `ht' : t * c.rep = c.rep * t` using `ht`. Simplify using `only [_root_.mul_inv_rev]`.

Establish `: (k⁻¹ * (g⁻¹ * (ι t)⁻¹) * ι c.rep * (ι t * g * k)) = k⁻¹ * (g⁻¹ * ι c.rep * g) * k`. Establish `: (ι t)⁻¹ * ι c.rep * ι t = ι c.rep`. Rewrite using `[← map_inv, ← map_mul, ← map_mul, mul_assoc, ← ht', inv_mul_cancel_left]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[this, hΦ k hk])`.

Use `h1 h2 (fun x => support_conj_finite ι Φ x (h4 x) c.rep)`. Rewrite using `[← mul_finsum, ← e2, finsum_eq_sum_of_fintype, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[hD]`. Simplify using `only`.

Rewrite using `[mul_left_comm]`. Use `congr 2`. Use `finsum_congr fun δ => ?_` and prove the remaining obligations. Use `congr 1`. Simplify using `only [map_mul, map_inv, _root_.mul_inv_rev, inv_inv]`.

Use `group`. Introduce `q _`. Conclude with `(hsupp q).subset fun c hc => right_ne_zero_of_mul hc`.
-/
theorem regroup_abstract {G H : Type} [Group G] [Group H] (ι : H →* G) (hι : Function.Injective ι) (Γ : Subgroup G)
    (hΓ : ∀ g, g ∈ Γ ↔ ∃ h, ι h = g) (K : Subgroup G) (Φ : G → ℂ) (ψ : H → ℂ)
    (hΦ : ∀ k ∈ K, ∀ g, Φ (k⁻¹ * g * k) = Φ g) (hψ : ∀ a b, ψ (b⁻¹ * a * b) = ψ a)
    (h1 : Finite (DoubleCoset.Quotient (Γ : Set G) (K : Set G)))
    (h2 : ∀ x : G, Finite ↥(Γ ⊓ K.map (MulAut.conj x).toMonoidHom))
    (h4 : ∀ x : G, {γ : H | Φ (x⁻¹ * ι γ * x) ≠ 0}.Finite) :
    ∑ᶠ q : DoubleCoset.Quotient (Γ : Set G) (K : Set G),
      ((Nat.card ↥(Γ ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom) : ℂ))⁻¹ *
        ∑ᶠ γ : H, Φ ((Quotient.out q)⁻¹ * ι γ * Quotient.out q) * ψ γ =
    ∑ᶠ c : TwCl (MonoidHom.id H), ψ c.rep *
      ∑ᶠ q : DoubleCoset.Quotient ((Γ ⊓ twCent (MonoidHom.id G) (ι c.rep) : Subgroup G) : Set G) (K : Set G),
        ((Nat.card ↥((Γ ⊓ twCent (MonoidHom.id G) (ι c.rep)) ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom) : ℂ))⁻¹ *
          Φ ((Quotient.out q)⁻¹ * ι c.rep * Quotient.out q) := by
  classical
  haveI := Fintype.ofFinite (DoubleCoset.Quotient (Γ : Set G) (K : Set G))
  set D : DoubleCoset.Quotient (Γ : Set G) (K : Set G) → TwCl (MonoidHom.id H) → ℂ := fun q c =>
    ∑ᶠ δ : H ⧸ twCent (MonoidHom.id H) c.rep,
      Φ ((Quotient.out q)⁻¹ * ι (Quotient.out δ * c.rep * (Quotient.out δ)⁻¹) * Quotient.out q) with hD

  have s1 : ∀ q : DoubleCoset.Quotient (Γ : Set G) (K : Set G),
      ∑ᶠ γ : H, Φ ((Quotient.out q)⁻¹ * ι γ * Quotient.out q) * ψ γ = ∑ᶠ c : TwCl (MonoidHom.id H), ψ c.rep * D q c := by
    intro q
    rw [finsum_classes _ ((h4 (Quotient.out q)).subset fun γ hγ => left_ne_zero_of_mul hγ)]
    refine finsum_congr fun c => ?_
    rw [hD, mul_finsum]
    refine finsum_congr fun δ => ?_
    have : ψ (Quotient.out δ * c.rep * (Quotient.out δ)⁻¹) = ψ c.rep := by
      simpa using hψ c.rep (Quotient.out δ)⁻¹
    rw [this, mul_comm]

  have hsupp : ∀ q : DoubleCoset.Quotient (Γ : Set G) (K : Set G),
      (Function.support fun c : TwCl (MonoidHom.id H) => ψ c.rep * D q c).Finite := by
    intro q
    refine ((h4 (Quotient.out q)).image (fun γ => (Quot.mk _ γ : TwCl (MonoidHom.id H)))).subset ?_
    intro (c : TwCl (MonoidHom.id H)) hc
    have hc' : D q c ≠ 0 := right_ne_zero_of_mul hc
    obtain ⟨δ, hδ⟩ : ∃ δ : H ⧸ twCent (MonoidHom.id H) c.rep,
        Φ ((Quotient.out q)⁻¹ * ι (Quotient.out δ * c.rep * (Quotient.out δ)⁻¹) * Quotient.out q) ≠ 0 := by
      by_contra hn
      push_neg at hn
      exact hc' (by rw [hD]; simp only; rw [finsum_congr hn]; simp)
    refine ⟨_, hδ, ?_⟩
    change Quot.mk _ (Quotient.out δ * c.rep * (Quotient.out δ)⁻¹) = c
    exact (Quot.sound ⟨Quotient.out δ, by simp [mul_assoc]; rfl⟩).trans (Quot.out_eq c)
  simp_rw [s1]
  rw [finsum_eq_sum_of_fintype]
  simp_rw [mul_finsum]
  rw [← finsum_sum_comm]
  · refine finsum_congr fun c => ?_
    have e2 := unfold ι hι Γ hΓ (twCent (MonoidHom.id H) c.rep) (Γ ⊓ twCent (MonoidHom.id G) (ι c.rep))
      (fun g => by
        constructor
        · rintro ⟨hg, hc⟩
          obtain ⟨h, rfl⟩ := (hΓ g).1 hg
          refine ⟨h, hι ?_, rfl⟩
          change ι h * ι c.rep = ι c.rep * ι h at hc
          change ι (h * c.rep) = ι (c.rep * h)
          rw [map_mul, map_mul, hc]
        · rintro ⟨t, ht, rfl⟩
          refine ⟨(hΓ _).2 ⟨t, rfl⟩, ?_⟩
          change ι t * ι c.rep = ι c.rep * ι t
          have ht' : t * c.rep = c.rep * t := ht
          rw [← map_mul, ht', map_mul])
      K (fun g => Φ (g⁻¹ * ι c.rep * g))
      (fun t ht k hk g => by
        have ht' : t * c.rep = c.rep * t := ht
        simp only [_root_.mul_inv_rev]
        have : (k⁻¹ * (g⁻¹ * (ι t)⁻¹) * ι c.rep * (ι t * g * k)) = k⁻¹ * (g⁻¹ * ι c.rep * g) * k := by
          have : (ι t)⁻¹ * ι c.rep * ι t = ι c.rep := by
            rw [← map_inv, ← map_mul, ← map_mul, mul_assoc, ← ht', inv_mul_cancel_left]
          calc _ = k⁻¹ * (g⁻¹ * ((ι t)⁻¹ * ι c.rep * ι t) * g) * k := by group
            _ = _ := by rw [this]
        rw [this, hΦ k hk])
      h1 h2 (fun x => support_conj_finite ι Φ x (h4 x) c.rep)
    rw [← mul_finsum, ← e2, finsum_eq_sum_of_fintype, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hD]
    simp only
    rw [mul_left_comm]
    congr 2
    refine finsum_congr fun δ => ?_
    congr 1
    simp only [map_mul, map_inv, _root_.mul_inv_rev, inv_inv]
    group
  · intro q _
    exact (hsupp q).subset fun c hc => right_ne_zero_of_mul hc

end GlobalTheory.BCT.Regroup

namespace GlobalTheory.BCT.Regroup

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

/- English proof (translation)
Unfold `toSub`. Distinguish the cases in `hy : y ∈ U`. Rewrite using `[dif_pos hy, dif_pos (mul_mem (mul_mem (inv_mem k.2) hy) k.2)]`. Use `ext`. Simplify using the standard rewrite rules.

Rewrite using `[dif_neg hy, dif_neg]`. Simplify using the standard rewrite rules. Introduce `h`. Apply `hy` to reduce the goal to its premises. Use `mul_mem (mul_mem k.2 h) (inv_mem k.2)` as an intermediate fact.

Simplify `this` using `[mul_assoc]`.
-/
theorem toSub_conj {G : Type} [Group G] (U : Subgroup G) (k : U) (y : G) :
    toSub U ((k : G)⁻¹ * y * k) = k⁻¹ * toSub U y * k := by
  unfold toSub
  by_cases hy : y ∈ U
  · rw [dif_pos hy, dif_pos (mul_mem (mul_mem (inv_mem k.2) hy) k.2)]
    ext
    simp
  · rw [dif_neg hy, dif_neg]
    · simp
    · intro h
      apply hy
      have := mul_mem (mul_mem k.2 h) (inv_mem k.2)
      simpa [mul_assoc] using this

/- English proof (translation)
Unfold `globFn`. Use `finprod_mem_congr rfl fun w hw => ?_` and prove the remaining obligations. Establish `hkw : cLoc w k.1 ∈ (K' w).map (UL n w).subtype`. Establish `h1` using `Subgroup.mem_iInf.1 hk w`. Conclude with `Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 h1 hw)`.

Take `⟨k', hk', e⟩` from `Subgroup.mem_map.1 hkw`. Establish `e2 : cLoc w (k⁻¹ * g * k).1 = ((k' : UL n w) : GLw n w)⁻¹ * cLoc w g.1 * (k' : GLw n w)`. Establish `e' : (k' : GLw n w) = cLoc w k.1` using `e`. Rewrite using `[e']`. Simplify using the standard rewrite rules.

Rewrite using `[e2, toSub_conj, ((hf w).2 k' hk' _).2, ((hf w).2 k'⁻¹ (inv_mem hk') _).1]`.
-/
theorem globFn_conj (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)) (f : ∀ w : Pl E, UL n w → ℂ)
    (hf : ∀ w, IsHecke (K' w) (f w)) (k : finU E n) (hk : k ∈ globLev S K') (g : finU E n) :
    globFn S f (k⁻¹ * g * k) = globFn S f g := by
  unfold globFn
  refine finprod_mem_congr rfl fun w hw => ?_
  have hkw : cLoc w k.1 ∈ (K' w).map (UL n w).subtype := by
    have h1 := Subgroup.mem_iInf.1 hk w
    exact Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 h1 hw)
  obtain ⟨k', hk', e⟩ := Subgroup.mem_map.1 hkw
  have e2 : cLoc w (k⁻¹ * g * k).1 = ((k' : UL n w) : GLw n w)⁻¹ * cLoc w g.1 * (k' : GLw n w) := by
    have e' : (k' : GLw n w) = cLoc w k.1 := e
    rw [e']
    simp
  rw [e2, toSub_conj, ((hf w).2 k' hk' _).2, ((hf w).2 k'⁻¹ (inv_mem hk') _).1]

/- English proof (translation)
Use `congr 1`. Establish `: (b⁻¹ * a * b).1.val = (b.1.val)⁻¹ * a.1.val * b.1.val`. Simplify using `[Matrix.coe_units_inv]`. Rewrite using `[this]`. Establish `h` using `Matrix.charpoly_units_conj (b.1)⁻¹ a.1.val`.

Simplify `h` using `[Matrix.coe_units_inv]`.
-/
theorem chW_conj (lam : InfinitePlace E → DomWeight n) (a b : UE E n) :
    chW lam (b⁻¹ * a * b).1.val.charpoly = chW lam a.1.val.charpoly := by
  congr 1
  have : (b⁻¹ * a * b).1.val = (b.1.val)⁻¹ * a.1.val * b.1.val := by
    simp [Matrix.coe_units_inv]
  rw [this]
  have h := Matrix.charpoly_units_conj (b.1)⁻¹ a.1.val
  simpa [Matrix.coe_units_inv] using h

/- English proof (translation)
Introduce `E _ _ _ hU n hn S hS lam K' hK f hf hreg`. Take `⟨hmul, hinj, hmem⟩` from `finPt_props E n`. Set `ι : UE E n →* finU E n` to `MonoidHom.mk' finPt hmul`. Establish `key : ∑ᶠ q : DoubleCoset.Quotient (ratFinU E n : Set (finU E n)) (globLev S K' : Set (finU E n)), ((Nat.card (ratFinU E n ⊓ (globLev S K').map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup (finU E n)) : ℂ))⁻¹ * ∑ᶠ γ : UE E n, globFn S f ((Quotient.out q)⁻¹ * finPt γ * Quo …` using `regroup_abstract ι hinj (ratFinU E n) hmem (globLev S K') (globFn S f) (fun γ => chW lam γ.1.val.charpoly) (globFn_conj S K' f hf.1) (chW_conj lam) (finite_classes E hU n hn S hS K' hK) (finite_stab E hU n hn S hS K' hK) (finite_supp E hU n hn S hS K' hK f hf)`. Take `⟨w, hw, hsep⟩` from `hreg`.

Unfold `kernSum`. Rewrite using `[key, mul_finsum]`. Use `finsum_congr fun c => ?_` and prove the remaining obligations. Use `split_ifs with hc`. Rewrite using `[clsSum]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h0 : ∀ q : DoubleCoset.Quotient ((ratFinU E n ⊓ twCent (MonoidHom.id _) (finPt c.rep) : Subgroup (finU E n)) : Set (finU E n)) (globLev S K' : Set (finU E n)), globFn S f ((Quotient.out q)⁻¹ * finPt c.rep * Quotient.out q) = 0` using `fun q => by`. Assume the negation of the conclusion as `h`. Conclude with `hc (separable_of_globFn_ne_zero E n S K' f hf w hw hsep _ _ h)`. Simplify using `[h0]`.
-/
theorem kernSum_eq_finsum_classes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → (∃ w ∈ S, ∀ y, f w y ≠ 0 → y.1.val.charpoly.Separable) → kernSum S lam K' f = ∑ᶠ c : TwCl (MonoidHom.id (UE E n)), if c.rep.1.val.charpoly.Separable then chW lam c.rep.1.val.charpoly * clsSum S K' f c.rep else 0 := by
  intro E _ _ _ hU n hn S hS lam K' hK f hf hreg
  obtain ⟨hmul, hinj, hmem⟩ := finPt_props E n
  let ι : UE E n →* finU E n := MonoidHom.mk' finPt hmul
  have key : ∑ᶠ q : DoubleCoset.Quotient (ratFinU E n : Set (finU E n)) (globLev S K' : Set (finU E n)),
      ((Nat.card (ratFinU E n ⊓ (globLev S K').map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup (finU E n)) :
        ℂ))⁻¹ *
      ∑ᶠ γ : UE E n, globFn S f ((Quotient.out q)⁻¹ * finPt γ * Quotient.out q) * chW lam γ.1.val.charpoly =
    ∑ᶠ c : TwCl (MonoidHom.id (UE E n)), chW lam c.rep.1.val.charpoly *
      ∑ᶠ q : DoubleCoset.Quotient ((ratFinU E n ⊓ twCent (MonoidHom.id _) (finPt c.rep) : Subgroup (finU E n)) : Set (finU E n))
        (globLev S K' : Set (finU E n)),
      ((Nat.card ((ratFinU E n ⊓ twCent (MonoidHom.id _) (finPt c.rep)) ⊓
          (globLev S K').map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup (finU E n)) : ℂ))⁻¹ *
        globFn S f ((Quotient.out q)⁻¹ * finPt c.rep * Quotient.out q) :=
    regroup_abstract ι hinj (ratFinU E n) hmem (globLev S K') (globFn S f) (fun γ => chW lam γ.1.val.charpoly)
      (globFn_conj S K' f hf.1) (chW_conj lam) (finite_classes E hU n hn S hS K' hK) (finite_stab E hU n hn S hS K' hK)
      (finite_supp E hU n hn S hS K' hK f hf)
  obtain ⟨w, hw, hsep⟩ := hreg
  unfold kernSum
  rw [key, mul_finsum]
  refine finsum_congr fun c => ?_
  split_ifs with hc
  · rw [clsSum]
    ring
  · have h0 : ∀ q : DoubleCoset.Quotient ((ratFinU E n ⊓ twCent (MonoidHom.id _) (finPt c.rep) : Subgroup (finU E n)) :
        Set (finU E n)) (globLev S K' : Set (finU E n)),
        globFn S f ((Quotient.out q)⁻¹ * finPt c.rep * Quotient.out q) = 0 := fun q => by
      by_contra h
      exact hc (separable_of_globFn_ne_zero E n S K' f hf w hw hsep _ _ h)
    simp [h0]

end GlobalTheory.BCT.Regroup
