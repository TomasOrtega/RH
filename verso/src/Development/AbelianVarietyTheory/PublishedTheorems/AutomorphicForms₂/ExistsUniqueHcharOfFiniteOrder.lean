import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.GaloisValuations.Global

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host

namespace GlobalTheory.HeckeGal

section Defs

variable (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

abbrev Gab : Type := TopologicalAbelianization (G E Ω)

def toAb : G E Ω →* Gab E Ω := QuotientGroup.mk' _

def infConn : Subgroup (Ideles E) :=
  (Subgroup.connectedComponentOfOne (InfiniteAdeleRing E)ˣ).map
    (Units.map (MonoidHom.inl (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E)))

variable {E Ω}

structure IsGlobalArtin (art : Ideles E →* Gab E Ω) : Prop where

  quot : IsOpenQuotientMap art

  ker : art.ker = ((diagUnits E).range ⊔ infConn E).topologicalClosure

  ine : ∀ (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A v → ∀ g : Gab E Ω,
    (∃ x, IsUnitAt v x ∧ art (localIdele E v x) = g) ↔ ∃ σ ∈ Ine (F := E) A, toAb E Ω σ = g

  frob : ∀ (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A v → ∀ g : Gab E Ω,
    (∃ x, IsUnifAt v x ∧ art (localIdele E v x) = g) ↔
      ∃ σ : G E Ω, IsFrob (F := E) A (normV v) σ ∧ toAb E Ω σ⁻¹ = g

  dec : ∀ (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A v →
    (art.comp (localIdele E v)).range.topologicalClosure = (Dec (F := E) A).map (toAb E Ω)

def IsAlgPos (χ : HChar E) (n : (E →+* ℂ) → ℤ) : Prop :=
  ∀ k : Eˣ, (∀ φ : E →+* ℝ, 0 < φ (k : E)) → ((χ.inf k : ℂˣ) : ℂ) = ∏ φ : E →+* ℂ, φ (k : E) ^ n φ

def infPow (n : (E →+* ℂ) → ℤ) (x : Ideles E) : ℂ :=
  ∏ w : InfinitePlace E, ∏ᶠ i : {i : w.Completion →+* ℂ // Continuous i},
    i.1 ((x : AdeleRing (𝓞 E) E).1 w) ^ n (i.1.comp (algebraMap E w.Completion))

variable {l : ℕ} [Fact l.Prime]

def locPow (ι : Qbar l ≃+* ℂ) (n : (E →+* ℂ) → ℤ) (v : HeightOneSpectrum (𝓞 E)) (y : v.adicCompletion E) : Qbar l :=
  ∏ᶠ j : {j : v.adicCompletion E →+* Qbar l // Continuous j},
    j.1 y ^ n ((ι.toRingHom.comp j.1).comp (algebraMap E (v.adicCompletion E)))

def lPow (ι : Qbar l ≃+* ℂ) (n : (E →+* ℂ) → ℤ) (x : Ideles E) : Qbar l :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 E), locPow ι n v ((x : AdeleRing (𝓞 E) E).2 v)

def IsLAdicOf (art : Ideles E →* Gab E Ω) (ι : Qbar l ≃+* ℂ) (χ : HChar E) (n : (E →+* ℂ) → ℤ)
    (r : G E Ω →* (Qbar l)ˣ) : Prop :=
  ∀ (x : Ideles E) (σ : G E Ω), art x = toAb E Ω σ →
    ((r σ : (Qbar l)ˣ) : Qbar l) = ι.symm (((χ.1 x : ℂˣ) : ℂ) * (infPow n x)⁻¹) * lPow ι n x

end Defs

end GlobalTheory.HeckeGal

namespace GlobalTheory.Published

open GlobalTheory.HeckeGal

def GlobalArtinReciprocity : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω],
    ∃ art : Ideles E →* Gab E Ω, IsGlobalArtin art

def HeckeLAdicCharacter : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω],
    ∃ art : Ideles E →* Gab E Ω, IsGlobalArtin art ∧
      ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (χ : HChar E) (n : (E →+* ℂ) → ℤ), IsAlgPos χ n →
        ∃! r : G E Ω →* (Qbar l)ˣ, Continuous r ∧ IsLAdicOf art ι χ n r

end GlobalTheory.Published

namespace GlobalTheory.HeckeGal

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem isAlgPos_of_isAlg {χ : HChar E} {n : (E →+* ℂ) → ℤ} (h : χ.IsAlg n) : IsAlgPos χ n :=
  fun k _ => h k

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument.

A detailed English derivation is pending.
-/
theorem finite_contEmb (v : HeightOneSpectrum (𝓞 E)) :
    Finite {j : v.adicCompletion E →+* Qbar l // Continuous j} := by
  refine Finite.of_injective
    (fun j : {j : v.adicCompletion E →+* Qbar l // Continuous j} =>
      j.1.comp (algebraMap E (v.adicCompletion E))) fun a b h => ?_
  apply Subtype.ext
  apply DFunLike.coe_injective
  refine (HeightOneSpectrum.denseRange_algebraMap E v).equalizer a.2 b.2 ?_
  funext k
  exact DFunLike.congr_fun h k

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Assume the hypotheses and unpack their components. Supply the required witnesses or components. Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument. A detailed English derivation is pending.
-/
theorem finite_contEmbInf (w : InfinitePlace E) :
    Finite {i : w.Completion →+* ℂ // Continuous i} := by
  refine Finite.of_injective
    (fun j : {i : w.Completion →+* ℂ // Continuous i} =>
      j.1.comp (algebraMap E w.Completion)) fun a b h => ?_
  apply Subtype.ext
  apply DFunLike.coe_injective
  have hd : DenseRange (algebraMap E w.Completion) := by
    refine Dense.mono ?_ (InfinitePlace.Completion.denseRange_coe w)
    rintro _ ⟨a, rfl⟩
    exact ⟨WithAbs.equiv w.1 a, rfl⟩
  refine hd.equalizer a.2 b.2 ?_
  funext k
  exact DFunLike.congr_fun h k

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem isEmpty_contEmb {v : HeightOneSpectrum (𝓞 E)} (hv : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal) :
    IsEmpty {j : v.adicCompletion E →+* Qbar l // Continuous j} := by
  refine ⟨fun j => ?_⟩
  have hl : l.Prime := Fact.out
  have hN : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  obtain ⟨a, M, hM, hNM⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN l hl.ne_one
  have hmem : ((M : ℕ) : 𝓞 E) ∈ v.asIdeal := by
    have h := Ideal.absNorm_mem v.asIdeal
    rw [hNM, Nat.cast_mul, Nat.cast_pow] at h
    exact (v.isPrime.mem_or_mem h).resolve_left fun h' => hv (v.isPrime.mem_of_pow_mem a h')
  have hlt : Valued.v ((M : ℕ) : v.adicCompletion E) < 1 := by
    have h : Valued.v (((algebraMap (𝓞 E) E (M : 𝓞 E) : E)) : v.adicCompletion E) =
        v.valuation E (algebraMap (𝓞 E) E (M : 𝓞 E)) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
    have h2 : v.valuation E (algebraMap (𝓞 E) E (M : 𝓞 E)) < 1 :=
      (HeightOneSpectrum.valuation_lt_one_iff_mem v _).mpr hmem
    rw [← h] at h2
    have e : (((algebraMap (𝓞 E) E (M : 𝓞 E) : E)) : v.adicCompletion E) = ((M : ℕ) : v.adicCompletion E) := by
      rw [map_natCast]
      exact map_natCast (algebraMap E (v.adicCompletion E)) M
    rwa [e] at h2
  have ht : Filter.Tendsto (fun k : ℕ => ((M : ℕ) : v.adicCompletion E) ^ k) Filter.atTop (nhds 0) :=
    Valued.tendsto_zero_pow_of_v_lt_one hlt
  have ht2 := ((j.2.tendsto 0).comp ht).norm
  have hn : ‖((M : ℕ) : Qbar l)‖ = 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends]
    exact Padic.norm_natCast_eq_one_iff.mpr ((Nat.Prime.coprime_iff_not_dvd hl).mpr hM)
  have e : (fun k : ℕ => ‖((j.1 : _ → _) ∘ fun k : ℕ => ((M : ℕ) : v.adicCompletion E) ^ k) k‖) = fun _ => (1 : ℝ) := by
    funext k
    simp [hn]
  rw [e, map_zero, norm_zero] at ht2
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds ht2)

/- English proof (translation)
Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem locPow_of_notMem (ι : Qbar l ≃+* ℂ) (n : (E →+* ℂ) → ℤ) {v : HeightOneSpectrum (𝓞 E)}
    (hv : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal) (y : v.adicCompletion E) : locPow ι n v y = 1 := by
  have := isEmpty_contEmb (l := l) hv
  exact finprod_of_isEmpty _

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Assume the negation of the conclusion and derive a contradiction.

Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem finite_support_lPow (ι : Qbar l ≃+* ℂ) (n : (E →+* ℂ) → ℤ) (x : Ideles E) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 E) =>
      locPow ι n v ((x : AdeleRing (𝓞 E) E).2 v)).Finite := by
  have hl : l.Prime := Fact.out
  have h0 : Ideal.span {((l : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hl.ne_zero
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  by_contra h
  refine hv (locPow_of_notMem ι n (fun hm => h ?_) _)
  exact Ideal.dvd_span_singleton.mpr hm

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem locPow_one (ι : Qbar l ≃+* ℂ) (n : (E →+* ℂ) → ℤ) (v : HeightOneSpectrum (𝓞 E)) :
    locPow ι n v 1 = 1 := by
  simp [locPow]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem locPow_zero (ι : Qbar l ≃+* ℂ) (v : HeightOneSpectrum (𝓞 E)) (y : v.adicCompletion E) :
    locPow ι (0 : (E →+* ℂ) → ℤ) v y = 1 := by
  simp [locPow]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify using the standard rewrite rules.
-/
theorem infPow_localIdele (n : (E →+* ℂ) → ℤ) (v : HeightOneSpectrum (𝓞 E)) (x : (v.adicCompletion E)ˣ) :
    infPow n (localIdele E v x) = 1 := by
  refine Finset.prod_eq_one fun w _ => ?_
  have : ((localIdele E v x : Ideles E) : AdeleRing (𝓞 E) E).1 w = 1 := rfl
  simp [this]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem lPow_localIdele (ι : Qbar l ≃+* ℂ) (n : (E →+* ℂ) → ℤ) (v : HeightOneSpectrum (𝓞 E))
    (x : (v.adicCompletion E)ˣ) : lPow ι n (localIdele E v x) = locPow ι n v x := by
  classical
  unfold lPow
  rw [finprod_eq_single _ v]
  · congr 1
    exact Function.update_self v (x : v.adicCompletion E) (fun w : HeightOneSpectrum (𝓞 E) => (1 : w.adicCompletion E))
  · intro w hw
    have : ((localIdele E v x : Ideles E) : AdeleRing (𝓞 E) E).2 w = 1 :=
      Function.update_of_ne hw (x : v.adicCompletion E) (fun w : HeightOneSpectrum (𝓞 E) => (1 : w.adicCompletion E))
    rw [this, locPow_one]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem infPow_zero (x : Ideles E) : infPow (0 : (E →+* ℂ) → ℤ) x = 1 := by
  simp [infPow]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem lPow_zero (ι : Qbar l ≃+* ℂ) (x : Ideles E) : lPow ι (0 : (E →+* ℂ) → ℤ) x = 1 := by
  simp [lPow, locPow_zero]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem infPow_add (n n' : (E →+* ℂ) → ℤ) (x : Ideles E) : infPow (n + n') x = infPow n x * infPow n' x := by
  unfold infPow
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  have := finite_contEmbInf w
  have h0 : (x : AdeleRing (𝓞 E) E).1 w ≠ 0 :=
    left_ne_zero_of_mul_eq_one (congrArg (fun y : AdeleRing (𝓞 E) E => y.1 w) x.mul_inv)
  rw [← finprod_mul_distrib (Set.toFinite _) (Set.toFinite _)]
  exact finprod_congr fun i => zpow_add₀ ((map_ne_zero i.1).mpr h0) _ _

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem infPow_neg (n : (E →+* ℂ) → ℤ) (x : Ideles E) : infPow (-n) x = (infPow n x)⁻¹ := by
  unfold infPow
  rw [← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [← finprod_inv_distrib]
  exact finprod_congr fun i => zpow_neg _ _

/- English proof (translation)
Replace the relevant objects with their definitions. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem locPow_add (ι : Qbar l ≃+* ℂ) (n n' : (E →+* ℂ) → ℤ) (v : HeightOneSpectrum (𝓞 E))
    {y : v.adicCompletion E} (hy : y ≠ 0) : locPow ι (n + n') v y = locPow ι n v y * locPow ι n' v y := by
  unfold locPow
  have := finite_contEmb (l := l) v
  rw [← finprod_mul_distrib (Set.toFinite _) (Set.toFinite _)]
  exact finprod_congr fun j => zpow_add₀ ((map_ne_zero j.1).mpr hy) _ _

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem lPow_add (ι : Qbar l ≃+* ℂ) (n n' : (E →+* ℂ) → ℤ) (x : Ideles E) :
    lPow ι (n + n') x = lPow ι n x * lPow ι n' x := by
  unfold lPow
  rw [← finprod_mul_distrib (finite_support_lPow ι n x) (finite_support_lPow ι n' x)]
  exact finprod_congr fun v => locPow_add ι n n' v
    (left_ne_zero_of_mul_eq_one (congrArg (fun y : AdeleRing (𝓞 E) E => y.2 v) x.mul_inv))

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem lPow_neg (ι : Qbar l ≃+* ℂ) (n : (E →+* ℂ) → ℤ) (x : Ideles E) : lPow ι (-n) x = (lPow ι n x)⁻¹ := by
  unfold lPow locPow
  rw [← finprod_inv_distrib]
  refine finprod_congr fun v => ?_
  rw [← finprod_inv_distrib]
  exact finprod_congr fun j => zpow_neg _ _

omit [NumberField E] in
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem toAb_surjective : Function.Surjective (toAb E Ω) := QuotientGroup.mk'_surjective _

section Local

variable {art : Ideles E →* Gab E Ω} {ι : Qbar l ≃+* ℂ} {χ : HChar E} {n : (E →+* ℂ) → ℤ}
  {r : G E Ω →* (Qbar l)ˣ} {v : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}

/- English proof (translation)
By extensionality, compare the relevant components. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.
-/
theorem IsLAdicOf.unique (hs : Function.Surjective art) {r' : G E Ω →* (Qbar l)ˣ}
    (h : IsLAdicOf art ι χ n r) (h' : IsLAdicOf art ι χ n r') : r = r' := by
  ext σ
  obtain ⟨x, hx⟩ := hs (toAb E Ω σ)
  rw [h x σ hx, h' x σ hx]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem IsLAdicOf.loc (h : IsLAdicOf art ι χ n r) (x : (v.adicCompletion E)ˣ) (σ : G E Ω)
    (hx : art (localIdele E v x) = toAb E Ω σ) :
    ((r σ : (Qbar l)ˣ) : Qbar l) = ι.symm ((χ.loc v x : ℂˣ) : ℂ) * locPow ι n v x := by
  rw [h _ σ hx, infPow_localIdele, inv_one, mul_one, lPow_localIdele]
  rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem IsLAdicOf.loc_away (h : IsLAdicOf art ι χ n r) (hv : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal ∨ n = 0)
    (x : (v.adicCompletion E)ˣ) (σ : G E Ω) (hx : art (localIdele E v x) = toAb E Ω σ) :
    ((r σ : (Qbar l)ˣ) : Qbar l) = ι.symm ((χ.loc v x : ℂˣ) : ℂ) := by
  rw [h.loc x σ hx]
  rcases hv with hv | rfl
  · rw [locPow_of_notMem ι n hv, mul_one]
  · rw [locPow_zero, mul_one]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Assume the hypotheses and unpack their components.

Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem IsLAdicOf.ine_image (ha : IsGlobalArtin art) (h : IsLAdicOf art ι χ n r)
    (hv : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal ∨ n = 0) (hA : IsPlaceOver A v) (z : Qbar l) :
    (∃ σ ∈ Ine (F := E) A, ((r σ : (Qbar l)ˣ) : Qbar l) = z) ↔
      ∃ x, IsUnitAt v x ∧ ι.symm ((χ.loc v x : ℂˣ) : ℂ) = z := by
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    obtain ⟨x, hx, e⟩ := (ha.ine v A hA _).mpr ⟨σ, hσ, rfl⟩
    exact ⟨x, hx, (h.loc_away hv x σ e).symm⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨σ, hσ, e⟩ := (ha.ine v A hA _).mp ⟨x, hx, rfl⟩
    exact ⟨σ, hσ, h.loc_away hv x σ e.symm⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem IsLAdicOf.unr_iff (ha : IsGlobalArtin art) (h : IsLAdicOf art ι χ n r)
    (hv : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal ∨ n = 0) (hA : IsPlaceOver A v) :
    (∀ σ ∈ Ine (F := E) A, r σ = 1) ↔ χ.UnrAt v := by
  constructor
  · intro H x hx
    obtain ⟨σ, hσ, e⟩ := (h.ine_image ha hv hA _).mpr ⟨x, hx, rfl⟩
    rw [H σ hσ, Units.val_one, eq_comm, map_eq_one_iff _ ι.symm.injective] at e
    exact Units.ext e
  · intro H σ hσ
    obtain ⟨x, hx, e⟩ := (h.ine_image ha hv hA _).mp ⟨σ, hσ, rfl⟩
    rw [H x hx, Units.val_one, map_one] at e
    exact Units.ext e.symm

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem IsLAdicOf.frob (ha : IsGlobalArtin art) (h : IsLAdicOf art ι χ n r)
    (hv : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal ∨ n = 0) (hA : IsPlaceOver A v) {σ : G E Ω}
    (hσ : IsFrob (F := E) A (normV v) σ) :
    ∃ x, IsUnifAt v x ∧ ((r σ : (Qbar l)ˣ) : Qbar l) = (ι.symm ((χ.loc v x : ℂˣ) : ℂ))⁻¹ := by
  obtain ⟨x, hx, e⟩ := (ha.frob v A hA _).mpr ⟨σ, hσ, rfl⟩
  refine ⟨x, hx, ?_⟩
  rw [← h.loc_away hv x _ e, map_inv, Units.val_inv_eq_inv_val, inv_inv]

/- English proof (translation)
Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.
-/
theorem IsLAdicOf.frob_unr (ha : IsGlobalArtin art) (h : IsLAdicOf art ι χ n r)
    (hv : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal ∨ n = 0) (hu : χ.UnrAt v) (hA : IsPlaceOver A v) {σ : G E Ω}
    (hσ : IsFrob (F := E) A (normV v) σ) :
    ((r σ : (Qbar l)ˣ) : Qbar l) = (ι.symm ((χ.val v : ℂˣ) : ℂ))⁻¹ := by
  obtain ⟨x, hx, e⟩ := h.frob ha hv hA hσ
  rw [e, χ.val_eq hu x hx]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem IsLAdicOf.mul {χ' : HChar E} {n' : (E →+* ℂ) → ℤ} {r' : G E Ω →* (Qbar l)ˣ}
    (h : IsLAdicOf art ι χ n r) (h' : IsLAdicOf art ι χ' n' r') : IsLAdicOf art ι (χ * χ') (n + n') (r * r') := by
  intro x σ hx
  rw [MonoidHom.mul_apply, Units.val_mul, h x σ hx, h' x σ hx, infPow_add, lPow_add]
  show _ = ι.symm (((χ.1 x * χ'.1 x : ℂˣ) : ℂ) * _) * _
  simp only [Units.val_mul, mul_inv, map_mul]
  ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem IsLAdicOf.inv (h : IsLAdicOf art ι χ n r) : IsLAdicOf art ι χ⁻¹ (-n) r⁻¹ := by
  intro x σ hx
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, h x σ hx, infPow_neg, lPow_neg]
  show _ = ι.symm ((((χ.1 x)⁻¹ : ℂˣ) : ℂ) * _) * _
  simp only [Units.val_inv_eq_inv_val, mul_inv, map_mul, map_inv₀]

end Local

def liftAb {B : Type} [CommGroup B] [TopologicalSpace B] [T1Space B] (φ : G E Ω →* B) (hφ : Continuous φ) :
    Gab E Ω →* B :=
  QuotientGroup.lift _ φ fun _ hσ =>
    Subgroup.topologicalClosure_minimal _ (Abelianization.commutator_subset_ker φ)
      (isClosed_singleton.preimage hφ) hσ

omit [NumberField E] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem liftAb_toAb {B : Type} [CommGroup B] [TopologicalSpace B] [T1Space B] (φ : G E Ω →* B) (hφ : Continuous φ)
    (σ : G E Ω) : liftAb φ hφ (toAb E Ω σ) = φ σ := rfl

omit [NumberField E] in
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem continuous_liftAb {B : Type} [CommGroup B] [TopologicalSpace B] [T1Space B] (φ : G E Ω →* B)
    (hφ : Continuous φ) : Continuous (liftAb φ hφ) :=
  (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr hφ

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. Establish an intermediate fact. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem IsLAdicOf.dec_triv {art : Ideles E →* Gab E Ω} {ι : Qbar l ≃+* ℂ} {χ : HChar E} {n : (E →+* ℂ) → ℤ}
    {r : G E Ω →* (Qbar l)ˣ} {v : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}
    (ha : IsGlobalArtin art) (h : IsLAdicOf art ι χ n r) (hr : Continuous r)
    (hv : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal ∨ n = 0) (hA : IsPlaceOver A v) :
    (∀ σ ∈ Dec (F := E) A, r σ = 1) ↔ χ.loc v = 1 := by
  constructor
  · intro H
    ext x
    have hm : art (localIdele E v x) ∈ (Dec (F := E) A).map (toAb E Ω) := by
      rw [← ha.dec v A hA]
      exact Subgroup.le_topologicalClosure _ ⟨x, rfl⟩
    obtain ⟨σ, hσ, e⟩ := hm
    have e2 := h.loc_away hv x σ e.symm
    rw [H σ hσ, Units.val_one, eq_comm, map_eq_one_iff _ ι.symm.injective] at e2
    exact e2
  · intro H σ hσ
    have hm : toAb E Ω σ ∈ (art.comp (localIdele E v)).range.topologicalClosure := by
      rw [ha.dec v A hA]
      exact ⟨σ, hσ, rfl⟩
    have hle : (art.comp (localIdele E v)).range ≤ (liftAb r hr).ker := by
      rintro _ ⟨x, rfl⟩
      obtain ⟨τ, hτ⟩ := toAb_surjective (art (localIdele E v x))
      have e2 := h.loc_away hv x τ hτ.symm
      rw [H, MonoidHom.one_apply, Units.val_one, map_one] at e2
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← hτ, liftAb_toAb]
      exact Units.ext e2
    exact Subgroup.topologicalClosure_minimal _ hle
      (isClosed_singleton.preimage (continuous_liftAb r hr)) hm

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isOpen_ker_of_pow {Γ K : Type} [Group Γ] [TopologicalSpace Γ] [Field K] [TopologicalSpace K] [T1Space Kˣ]
    (φ : Γ →* Kˣ) (hφ : Continuous φ) {m : ℕ} (hm : 0 < m) (h : ∀ g, φ g ^ m = 1) : IsOpen (φ.ker : Set Γ) := by
  have : NeZero m := ⟨hm.ne'⟩
  have hfin : ((rootsOfUnity m K : Set Kˣ) \ {1}).Finite :=
    (Set.finite_coe_iff.mp (inferInstanceAs (Finite (rootsOfUnity m K)))).sdiff
  have e : (φ.ker : Set Γ) = (φ ⁻¹' ((rootsOfUnity m K : Set Kˣ) \ {1}))ᶜ := by
    ext g
    simp [MonoidHom.mem_ker, mem_rootsOfUnity, h g]
  rw [e]
  exact (hfin.isClosed.preimage hφ).isOpen_compl

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem continuous_of_isOpen_ker' {Γ B : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group B]
    [TopologicalSpace B] [IsTopologicalGroup B] (φ : Γ →* B) (h : IsOpen (φ.ker : Set Γ)) : Continuous φ := by
  refine continuous_of_continuousAt_one φ ?_
  refine (continuousAt_const (y := (1 : B))).congr ?_
  filter_upwards [h.mem_nhds φ.ker.one_mem] with g hg
  exact (MonoidHom.mem_ker.mp hg).symm

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Assume the hypotheses and unpack their components. Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_unique_hchar_of_finite_order {art : Ideles E →* Gab E Ω} (ha : IsGlobalArtin art) (ι : Qbar l ≃+* ℂ)
    (r : G E Ω →* (Qbar l)ˣ) (hr : Continuous r) {m : ℕ} (hm : 0 < m) (h : r ^ m = 1) :
    ∃! χ : HChar E, χ.OrderDvd m ∧ IsLAdicOf art ι χ 0 r := by
  let ψ : Ideles E →* (Qbar l)ˣ := (liftAb r hr).comp art
  have hψ : Continuous ψ := (continuous_liftAb r hr).comp ha.quot.continuous
  have hψm : ∀ x, ψ x ^ m = 1 := fun x => by
    obtain ⟨τ, hτ⟩ := toAb_surjective (art x)
    show liftAb r hr (art x) ^ m = 1
    rw [← hτ, liftAb_toAb]
    exact DFunLike.congr_fun h τ
  let χ0 : Ideles E →* ℂˣ := (Units.map ι.toRingHom.toMonoidHom).comp ψ
  have hopen : IsOpen (χ0.ker : Set (Ideles E)) :=
    Subgroup.isOpen_mono (fun x hx => by
      rw [MonoidHom.mem_ker] at hx ⊢
      rw [MonoidHom.comp_apply, hx, map_one]) (isOpen_ker_of_pow ψ hψ hm hψm)
  have htriv : ∀ k : Eˣ, χ0 (diagUnits E k) = 1 := fun k => by
    have hk : diagUnits E k ∈ art.ker := by
      rw [ha.ker]
      exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_left ⟨k, rfl⟩)
    show Units.map _ (liftAb r hr (art (diagUnits E k))) = 1
    rw [MonoidHom.mem_ker.mp hk, map_one, map_one]
  refine ⟨⟨χ0, continuous_of_isOpen_ker' χ0 hopen, htriv⟩, ⟨?_, ?_⟩, ?_⟩
  · apply Subtype.ext
    refine MonoidHom.ext fun x => ?_
    show (Units.map _ (ψ x)) ^ m = 1
    rw [← map_pow, hψm, map_one]
  · intro x σ hx
    rw [infPow_zero, lPow_zero, inv_one, mul_one, mul_one]
    show _ = ι.symm (ι ((liftAb r hr (art x) : (Qbar l)ˣ) : Qbar l))
    rw [hx, liftAb_toAb, ι.symm_apply_apply]
  · rintro χ ⟨-, hχ⟩
    apply Subtype.ext
    refine MonoidHom.ext fun x => Units.ext ?_
    obtain ⟨τ, hτ⟩ := toAb_surjective (art x)
    have e := hχ x τ hτ.symm
    rw [infPow_zero, lPow_zero, inv_one, mul_one, mul_one] at e
    show _ = ι ((liftAb r hr (art x) : (Qbar l)ˣ) : Qbar l)
    rw [← hτ, liftAb_toAb, e, ι.apply_symm_apply]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Introduce a local definition for the expression.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Assume the hypotheses and unpack their components. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem isAlgPos_zero_of_orderDvd {χ : HChar E} {m : ℕ} (hm : 0 < m) (h : χ.OrderDvd m) : IsAlgPos χ 0 := by
  intro k hk
  have h1 : ∀ x, χ.1 x ^ m = 1 := fun x => congrArg (fun ξ : HChar E => ξ.1 x) h
  have h2 : ∀ w : InfinitePlace E, ∃ y : w.Completion, y ^ m = algebraMap E w.Completion (k : E) := fun w => by
    rcases w.isReal_or_isComplex with hw | hw
    · let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
      have he : e (algebraMap E w.Completion (k : E)) = InfinitePlace.embedding_of_isReal hw (k : E) :=
        InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hw ((WithAbs.equiv w.1).symm (k : E))
      refine ⟨e.symm ((InfinitePlace.embedding_of_isReal hw (k : E)) ^ ((m : ℝ)⁻¹)), e.injective ?_⟩
      rw [map_pow, e.apply_symm_apply, he, Real.rpow_inv_natCast_pow (hk _).le hm.ne']
    · let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
      obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e (algebraMap E w.Completion (k : E))) hm
      exact ⟨e.symm z, e.injective (by rw [map_pow, e.apply_symm_apply, hz])⟩
  have h3 : χ.inf k = 1 := by
    show χ.1 (infDiag k) = 1
    rw [infDiag, MonoidHom.finsetProd_apply, map_prod]
    refine Finset.prod_eq_one fun w _ => ?_
    obtain ⟨y, hy⟩ := h2 w
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [zero_pow hm.ne', eq_comm, map_eq_zero] at hy
      exact k.ne_zero hy
    have e : atInf w k = Units.mk0 y hy0 ^ m := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hy.symm)
    rw [MonoidHom.comp_apply, e, map_pow, map_pow, h1]
  simp [h3]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem IsLAdicOf.pow_eq_one {art : Ideles E →* Gab E Ω} (hs : Function.Surjective art) {ι : Qbar l ≃+* ℂ}
    {χ : HChar E} {r : G E Ω →* (Qbar l)ˣ} (h : IsLAdicOf art ι χ 0 r) {m : ℕ} (hχ : χ.OrderDvd m) :
    r ^ m = 1 := by
  refine MonoidHom.ext fun σ => Units.ext ?_
  obtain ⟨x, hx⟩ := hs (toAb E Ω σ)
  have h1 : χ.1 x ^ m = 1 := congrArg (fun ξ : HChar E => ξ.1 x) hχ
  rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, h x σ hx, infPow_zero, lPow_zero, inv_one, mul_one, mul_one,
    ← map_pow, ← Units.val_pow_eq_pow_val, h1]
  simp

end GlobalTheory.HeckeGal

namespace GlobalTheory.Published

open GlobalTheory.HeckeGal

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem HeckeLAdicCharacter.globalArtin (H : HeckeLAdicCharacter) : GlobalArtinReciprocity := fun E Ω _ _ _ _ _ =>
  let ⟨art, ha, _⟩ := H E Ω
  ⟨art, ha⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Extract witnesses or component facts from the available result.

Supply the required witnesses or components.
-/
theorem HeckeLAdicCharacter.full (H : HeckeLAdicCharacter) (E Ω : Type) [Field E] [NumberField E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] :
    ∃ art : Ideles E →* Gab E Ω, IsGlobalArtin art ∧ ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ),
      (∀ (χ : HChar E) (n : (E →+* ℂ) → ℤ), χ.IsAlg n →
        ∃ r : G E Ω →* (Qbar l)ˣ, Continuous r ∧ IsLAdicOf art ι χ n r ∧
          (∀ r', IsLAdicOf art ι χ n r' → r' = r) ∧
          ∀ v : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∉ v.asIdeal → ∀ A : ValuationSubring Ω, IsPlaceOver A v →
            (∀ z : Qbar l, (∃ σ ∈ Ine (F := E) A, ((r σ : (Qbar l)ˣ) : Qbar l) = z) ↔
              ∃ x, IsUnitAt v x ∧ ι.symm ((χ.loc v x : ℂˣ) : ℂ) = z) ∧
            ((∀ σ ∈ Ine (F := E) A, r σ = 1) ↔ χ.UnrAt v) ∧
            (χ.UnrAt v → ∀ σ : G E Ω, IsFrob (F := E) A (normV v) σ →
              ((r σ : (Qbar l)ˣ) : Qbar l) = (ι.symm ((χ.val v : ℂˣ) : ℂ))⁻¹)) ∧
      (∀ m : ℕ, 0 < m → ∀ χ : HChar E, χ.OrderDvd m →
        ∃! r : G E Ω →* (Qbar l)ˣ, Continuous r ∧ r ^ m = 1 ∧ IsLAdicOf art ι χ 0 r) ∧
      (∀ m : ℕ, 0 < m → ∀ r : G E Ω →* (Qbar l)ˣ, Continuous r → r ^ m = 1 →
        ∃! χ : HChar E, χ.OrderDvd m ∧ IsLAdicOf art ι χ 0 r) := by
  obtain ⟨art, ha, h⟩ := H E Ω
  refine ⟨art, ha, fun l _ ι => ⟨fun χ n hn => ?_, fun m hm χ hχ => ?_,
    fun m hm r hr hrm => exists_unique_hchar_of_finite_order ha ι r hr hm hrm⟩⟩
  · obtain ⟨r, ⟨hr, hf⟩, -⟩ := h l ι χ n (isAlgPos_of_isAlg hn)
    exact ⟨r, hr, hf, fun r' h' => h'.unique ha.quot.surjective hf, fun v hv A hA =>
      ⟨hf.ine_image ha (Or.inl hv) hA, hf.unr_iff ha (Or.inl hv) hA,
        fun hu σ hσ => hf.frob_unr ha (Or.inl hv) hu hA hσ⟩⟩
  · obtain ⟨r, ⟨hr, hf⟩, -⟩ := h l ι χ 0 (isAlgPos_zero_of_orderDvd hm hχ)
    exact ⟨r, ⟨hr, hf.pow_eq_one ha.quot.surjective hχ, hf⟩,
      fun r' h' => h'.2.2.unique ha.quot.surjective hf⟩

end GlobalTheory.Published

end
