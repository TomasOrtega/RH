import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AssembleLattice
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.RecCond
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParPinsOfRec
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Formalism.LocalToGlobal.UnitaryNorms.MemFIffReal

noncomputable section

namespace GlobalTheory.Mem.TypeNormPin

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.L2.Pj

section Push

variable {K F : Type} [Field K] [Field F] (φ : K →+* F)

/- English proof (translation)
Use `le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono (Set.image_mono Submodule.subset_span))` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩`. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul b x _ hx`. Establish `: φ (b • x) = RingOfIntegers.mapRingHom φ b • φ x`. Express the relevant statement in the definitionally equal form `φ ((b : K) * x) = _`.

Rewrite using `[map_mul]`. Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem span_image_span (S : Set K) :
    Submodule.span (𝓞 F) (φ '' (Submodule.span (𝓞 K) S : Set K)) = Submodule.span (𝓞 F) (φ '' S) := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono (Set.image_mono Submodule.subset_span))
  rintro _ ⟨x, hx, rfl⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul b x _ hx =>
    have : φ (b • x) = RingOfIntegers.mapRingHom φ b • φ x := by
      change φ ((b : K) * x) = _
      rw [map_mul]; rfl
    rw [this]; exact Submodule.smul_mem _ _ hx

def extend : Submodule (𝓞 K) K →* Submodule (𝓞 F) F where
  toFun M := Submodule.span (𝓞 F) (φ '' M)
  map_one' := by rw [Submodule.one_eq_span, span_image_span, Set.image_singleton, map_one, Submodule.one_eq_span]
  map_mul' M N := by
    rw [Submodule.mul_eq_span_mul_set, span_image_span, Set.image_mul, Submodule.span_mul_span]

/- English proof (translation)
The claim follows from `span_image_span φ S`.
-/
theorem extend_span (S : Set K) : extend φ (Submodule.span (𝓞 K) S) = Submodule.span (𝓞 F) (φ '' S) :=
  span_image_span φ S

end Push

section Host

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

/- English proof (translation)
The claim follows from `(factEmb R H).2 g`.
-/
theorem emb_sqrt_iff (g : R.GG) :
    H.emb g H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ) ↔ g ∈ R.Psi :=
  (factEmb R H).2 g

/- English proof (translation)
The claim follows from `H.φ₀_mem`.
-/
theorem cmHostBaseEmbedding_sqrtMinusD : H.φ₀ H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ) := H.φ₀_mem

/- English proof (translation)
Introduce `h`. Establish `h1` using `congrArg Complex.im h`. Establish `: 0 < Real.sqrt H.d` using `Real.sqrt_pos.2 (by exact_mod_cast H.hyp.2.1.pos)`. Simplify using `at h1`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem conj_ne : starRingEnd ℂ (Complex.I * (Real.sqrt H.d : ℂ)) ≠ Complex.I * (Real.sqrt H.d : ℂ) := by
  intro h
  have h1 := congrArg Complex.im h
  have : 0 < Real.sqrt H.d := Real.sqrt_pos.2 (by exact_mod_cast H.hyp.2.1.pos)
  simp at h1
  linarith

/- English proof (translation)
Establish `h0 : (Complex.I * (Real.sqrt H.d : ℂ)) ^ 2 = -(H.d : ℂ)`. Rewrite using `[mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]`. Simplify using the standard rewrite rules. Establish `h : H.sqrtMinusD ^ 2 = -(H.d : H.E)`. Apply `H.φ₀.injective` to reduce the goal to its premises.

Rewrite using `[map_pow, cmHostBaseEmbedding_sqrtMinusD, h0]`. Simplify using the standard rewrite rules. Establish `h1 : σ H.sqrtMinusD ^ 2 = (Complex.I * (Real.sqrt H.d : ℂ)) ^ 2`. Rewrite using `[← map_pow, h, h0]`. Simplify using the standard rewrite rules.

Break down `sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h2 | h2` into its components or cases. Conclude with `Or.inl h2`. Use `right`. Rewrite using `[h2]`. Simplify using the standard rewrite rules.
-/
theorem emb_sqrt_cases (σ : H.E →+* ℂ) : σ H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ) ∨
    starRingEnd ℂ (σ H.sqrtMinusD) = Complex.I * (Real.sqrt H.d : ℂ) := by
  have h0 : (Complex.I * (Real.sqrt H.d : ℂ)) ^ 2 = -(H.d : ℂ) := by
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    simp
  have h : H.sqrtMinusD ^ 2 = -(H.d : H.E) := by
    apply H.φ₀.injective
    rw [map_pow, cmHostBaseEmbedding_sqrtMinusD, h0]
    simp
  have h1 : σ H.sqrtMinusD ^ 2 = (Complex.I * (Real.sqrt H.d : ℂ)) ^ 2 := by
    rw [← map_pow, h, h0]; simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h2 | h2
  · exact Or.inl h2
  · right; rw [h2]; simp

def embSum : Tau R ⊕ Tau R → (H.E →+* ℂ) :=
  Sum.elim (fun g => H.emb g) (fun g => (starRingEnd ℂ).comp (H.emb g))

/- English proof (translation)
Use `⟨?_, fun σ => ?_⟩` and prove the remaining obligations. Establish `hne : ∀ a b : Tau R, H.emb a ≠ (starRingEnd ℂ).comp (H.emb b)` using `fun a b h => by`. Establish `h1` using `DFunLike.congr_fun h H.sqrtMinusD`. Rewrite `h1` using `[RingHom.comp_apply, (emb_sqrt_iff H _).2 a.2, (emb_sqrt_iff H _).2 b.2]`. Conclude with `conj_ne H h1.symm`.

Introduce and unpack `(a | a) (b | b) hab`. Conclude with `congrArg _ (Subtype.ext ((factEmb R H).1.1 hab))`. Conclude with `absurd hab (hne a b)`. Conclude with `absurd hab.symm (hne b a)`. Use `congrArg _ (Subtype.ext ((factEmb R H).1.1 (RingHom.ext fun x => ?_)))` and prove the remaining obligations.

Conclude with `(starRingEnd ℂ).injective (DFunLike.congr_fun hab x)`. Break down `emb_sqrt_cases H σ with h | h` into its components or cases. Take `⟨g, rfl⟩` from `(factEmb R H).1.2 σ`. Conclude with `⟨Sum.inl ⟨g, (emb_sqrt_iff H g).1 h⟩, rfl⟩`. Take `⟨g, hg⟩` from `(factEmb R H).1.2 ((starRingEnd ℂ).comp σ)`.

Use `⟨Sum.inr ⟨g, (emb_sqrt_iff H g).1 (by rw [hg]; exact h)⟩, RingHom.ext fun x => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `starRingEnd ℂ (H.emb g x) = _`. Rewrite using `[hg]`. Simplify using the standard rewrite rules.
-/
theorem embSum_bij : Function.Bijective (embSum H) := by
  refine ⟨?_, fun σ => ?_⟩
  · have hne : ∀ a b : Tau R, H.emb a ≠ (starRingEnd ℂ).comp (H.emb b) := fun a b h => by
      have h1 := DFunLike.congr_fun h H.sqrtMinusD
      rw [RingHom.comp_apply, (emb_sqrt_iff H _).2 a.2, (emb_sqrt_iff H _).2 b.2] at h1
      exact conj_ne H h1.symm
    rintro (a | a) (b | b) hab
    · exact congrArg _ (Subtype.ext ((factEmb R H).1.1 hab))
    · exact absurd hab (hne a b)
    · exact absurd hab.symm (hne b a)
    · refine congrArg _ (Subtype.ext ((factEmb R H).1.1 (RingHom.ext fun x => ?_)))
      exact (starRingEnd ℂ).injective (DFunLike.congr_fun hab x)
  · rcases emb_sqrt_cases H σ with h | h
    · obtain ⟨g, rfl⟩ := (factEmb R H).1.2 σ
      exact ⟨Sum.inl ⟨g, (emb_sqrt_iff H g).1 h⟩, rfl⟩
    · obtain ⟨g, hg⟩ := (factEmb R H).1.2 ((starRingEnd ℂ).comp σ)
      refine ⟨Sum.inr ⟨g, (emb_sqrt_iff H g).1 (by rw [hg]; exact h)⟩, RingHom.ext fun x => ?_⟩
      change starRingEnd ℂ (H.emb g x) = _
      rw [hg]; simp

/- English proof (translation)
The claim follows from `H.conjE_apply _ x`.
-/
theorem emb_conj (g : R.GG) (x : H.E) : H.emb g (H.conj x) = starRingEnd ℂ (H.emb g x) :=
  H.conjE_apply _ x

end Host

/- English proof (translation)
Set `e : 𝓞 Q.c.F ≃+* 𝓞 X.B.Ks` to `Q.eO`. Establish `he : ∀ y : 𝓞 Q.c.F, X.B.embLL ((e y : X.B.Ks) : X.B.LL) = ((y : Q.c.F) : ℂ)` using `h`. Set `φ : X.B.Ks ≃+* Q.c.F` to `IsFractionRing.ringEquivOfRingEquiv e.symm`. Establish `hφ : ∀ y : 𝓞 X.B.Ks, ((φ (algebraMap _ X.B.Ks y) : Q.c.F) : ℂ) = X.B.embLL ((algebraMap _ X.B.Ks y : X.B.Ks) : X.B.LL)` using `fun y => by`. Rewrite using `[IsFractionRing.ringEquivOfRingEquiv_algebraMap]`.

Use `he (e.symm y)` as an intermediate fact. Rewrite `this` using `[e.apply_symm_apply]`. Conclude with `this.symm`. Use `⟨φ.toRingHom, fun x => ?_⟩` and prove the remaining obligations. Take `⟨a, b, -, rfl⟩` from `IsFractionRing.div_surjective (A := 𝓞 X.B.Ks) x`.

Express the relevant statement in the definitionally equal form `((φ (_ / _) : Q.c.F) : ℂ) = _`. Rewrite using `[map_div₀, IntermediateField.coe_div, hφ, hφ, IntermediateField.coe_div, map_div₀]`.
-/
theorem exists_hom (X : Stages) (Q : Par X.toD7) (h : Q.PinField) :
    ∃ φ : X.B.Ks →+* Q.c.F, ∀ x : X.B.Ks, ((φ x : Q.c.F) : ℂ) = X.B.embLL x := by
  let e : 𝓞 Q.c.F ≃+* 𝓞 X.B.Ks := Q.eO
  have he : ∀ y : 𝓞 Q.c.F, X.B.embLL ((e y : X.B.Ks) : X.B.LL) = ((y : Q.c.F) : ℂ) := h
  let φ : X.B.Ks ≃+* Q.c.F := IsFractionRing.ringEquivOfRingEquiv e.symm
  have hφ : ∀ y : 𝓞 X.B.Ks, ((φ (algebraMap _ X.B.Ks y) : Q.c.F) : ℂ) =
      X.B.embLL ((algebraMap _ X.B.Ks y : X.B.Ks) : X.B.LL) := fun y => by
    rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
    have := he (e.symm y)
    rw [e.apply_symm_apply] at this
    exact this.symm
  refine ⟨φ.toRingHom, fun x => ?_⟩
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 X.B.Ks) x
  change ((φ (_ / _) : Q.c.F) : ℂ) = _
  rw [map_div₀, IntermediateField.coe_div, hφ, hφ, IntermediateField.coe_div, map_div₀]

/- English proof (translation)
Introduce `𝔞 h𝔞`. Take `⟨β, hβ0, hβ, habs⟩` from `B.kPsi j hj1 hj2 𝔞 h𝔞`. Establish `hE : ∀ y, B.embLL (B.embE y) = B.host.φ₀ y` using `fun y => RingHom.congr_fun B.embE_φ₀ y`. Establish `himg : ∀ (τ : B.host.E →+* ℂ) (f : B.host.E → B.host.E), (∀ a, B.host.φ₀ (f a) = τ a) → φ '' {x : B.Ks | ∃ a ∈ 𝔞, (x : B.LL) = B.embE (f (a : B.host.E))} = (embK c τ) '' (𝔞 : Set (𝓞 B.host.E))`. Introduce `τ f hf`.

Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, ⟨a, ha, hx⟩, rfl⟩`. Use `⟨a, ha, Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite using `[embK_coe, hφ, hx, hE, hf]`.

Introduce and unpack `⟨a, ha, rfl⟩`. Use `⟨⟨_, B.E_le_Ks (f a)⟩, ⟨a, ha, rfl⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite using `[embK_coe, hφ, hE, hf]`. Use `⟨φ β, (map_ne_zero φ).2 hβ0, ?_, fun σ => ?_⟩` and prove the remaining obligations. Use `congrArg (extend φ) hβ` as an intermediate fact.

Rewrite `this` using `[extend_span, Set.image_singleton, map_prod]`. Rewrite using `[this, ← (embSum_bij B.host).prod_comp fun τ => Submodule.span (𝓞 c.F) ((embK c τ) '' (𝔞 : Set (𝓞 B.host.E))) ^ Dw.mult τ, Fintype.prod_sum_type, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun g _ => ?_` and prove the remaining obligations. Establish `hs : B.host.emb g B.host.sqrtMinusD = Complex.I * (Real.sqrt B.host.d : ℂ)` using `(emb_sqrt_iff B.host _).2 g.2`. Establish `h0 : Hh.rt0 = Complex.I * (Real.sqrt B.host.d : ℂ)` using `h2.trans (cmHostBaseEmbedding_sqrtMinusD B.host)`.

Establish `m1 : Dw.mult (embSum B.host (Sum.inl g)) = (B.R.sigW j).1`. Rewrite using `[ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult, if_pos (by rw [h1, h0]; exact hs)]`. Conclude with `hp`. Establish `m2 : Dw.mult (embSum B.host (Sum.inr g)) = (B.R.sigW j).2`. Rewrite using `[ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult, if_neg]`.

Conclude with `hq`. Rewrite using `[h1, h0]`. Express the relevant statement in the definitionally equal form `¬ starRingEnd ℂ (B.host.emb g B.host.sqrtMinusD) = _`. Rewrite using `[hs]`. Conclude with `conj_ne B.host`.

Rewrite using `[map_mul, map_pow, map_pow, extend_span, extend_span, m1, m2, himg (embSum B.host (Sum.inl g)) (B.host.sigmaOf g) (fun _ => rfl), himg (embSum B.host (Sum.inr g)) (fun a => B.host.sigmaOf g (B.host.conj a)) (fun a => emb_conj B.host g a)]`. Rewrite using `[hp, hq]`. Conclude with `habs (σ.comp φ)`.
-/
theorem kPsiIn_of_hom (B : Base) [IsCMField B.host.E] {Hh : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host B.host.E}
    {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level Hh} (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum Hh)
    {j : ℕ} (hj1 : 1 ≤ j) (hj2 : j ≤ B.R.m) (hp : Dw.p = (B.R.sigW j).1) (hq : Dw.q = (B.R.sigW j).2)
    (h1 : (Hh.rt : B.host.E) = B.host.sqrtMinusD) (h2 : Hh.rt0 = B.host.φ₀ B.host.sqrtMinusD)
    (φ : B.Ks →+* c.F) (hφ : ∀ x : B.Ks, ((φ x : c.F) : ℂ) = B.embLL x) : KPsiIn (Dw := Dw) c := by
  intro 𝔞 h𝔞
  obtain ⟨β, hβ0, hβ, habs⟩ := B.kPsi j hj1 hj2 𝔞 h𝔞
  have hE : ∀ y, B.embLL (B.embE y) = B.host.φ₀ y := fun y => RingHom.congr_fun B.embE_φ₀ y
  have himg : ∀ (τ : B.host.E →+* ℂ) (f : B.host.E → B.host.E), (∀ a, B.host.φ₀ (f a) = τ a) →
      φ '' {x : B.Ks | ∃ a ∈ 𝔞, (x : B.LL) = B.embE (f (a : B.host.E))} =
        (embK c τ) '' (𝔞 : Set (𝓞 B.host.E)) := by
    intro τ f hf
    ext z
    constructor
    · rintro ⟨x, ⟨a, ha, hx⟩, rfl⟩
      refine ⟨a, ha, Subtype.ext ?_⟩
      rw [embK_coe, hφ, hx, hE, hf]
    · rintro ⟨a, ha, rfl⟩
      refine ⟨⟨_, B.E_le_Ks (f a)⟩, ⟨a, ha, rfl⟩, Subtype.ext ?_⟩
      rw [embK_coe, hφ, hE, hf]
  refine ⟨φ β, (map_ne_zero φ).2 hβ0, ?_, fun σ => ?_⟩
  · have := congrArg (extend φ) hβ
    rw [extend_span, Set.image_singleton, map_prod] at this
    rw [this, ← (embSum_bij B.host).prod_comp fun τ =>
      Submodule.span (𝓞 c.F) ((embK c τ) '' (𝔞 : Set (𝓞 B.host.E))) ^ Dw.mult τ,
      Fintype.prod_sum_type, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun g _ => ?_
    have hs : B.host.emb g B.host.sqrtMinusD = Complex.I * (Real.sqrt B.host.d : ℂ) :=
      (emb_sqrt_iff B.host _).2 g.2
    have h0 : Hh.rt0 = Complex.I * (Real.sqrt B.host.d : ℂ) := h2.trans (cmHostBaseEmbedding_sqrtMinusD B.host)
    have m1 : Dw.mult (embSum B.host (Sum.inl g)) = (B.R.sigW j).1 := by
      rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult, if_pos (by rw [h1, h0]; exact hs)]
      exact hp
    have m2 : Dw.mult (embSum B.host (Sum.inr g)) = (B.R.sigW j).2 := by
      rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult, if_neg]
      · exact hq
      · rw [h1, h0]
        change ¬ starRingEnd ℂ (B.host.emb g B.host.sqrtMinusD) = _
        rw [hs]
        exact conj_ne B.host
    rw [map_mul, map_pow, map_pow, extend_span, extend_span, m1, m2,
      himg (embSum B.host (Sum.inl g)) (B.host.sigmaOf g) (fun _ => rfl),
      himg (embSum B.host (Sum.inr g)) (fun a => B.host.sigmaOf g (B.host.conj a))
        (fun a => emb_conj B.host g a)]
  · rw [hp, hq]
    exact habs (σ.comp φ)

/- English proof (translation)
Introduce `X Q hQ j hj`. Take `⟨φ, hφ⟩` from `exists_hom X Q hQ.2.2.1`. Take `⟨hp, hq, -⟩` from `hQ.2.2.2 j hj`. Take `⟨-, h1, h2, -⟩` from `hQ.1`. Conclude with `@kPsiIn_of_hom X.B (instCMHost X.toD7) Q.H Q.l Q.c (Q.Dw j) j hj.1 hj.2 hp hq h1 h2 φ hφ`.
-/
theorem hermitianCodeWordStages_typeNorms_principal : ∀ X : Stages, OKPsi X.toD7 := by
  intro X Q hQ j hj
  obtain ⟨φ, hφ⟩ := exists_hom X Q hQ.2.2.1
  obtain ⟨hp, hq, -⟩ := hQ.2.2.2 j hj
  obtain ⟨-, h1, h2, -⟩ := hQ.1
  exact @kPsiIn_of_hom X.B (instCMHost X.toD7) Q.H Q.l Q.c (Q.Dw j) j hj.1 hj.2 hp hq h1 h2 φ hφ

end GlobalTheory.Mem.TypeNormPin

end
