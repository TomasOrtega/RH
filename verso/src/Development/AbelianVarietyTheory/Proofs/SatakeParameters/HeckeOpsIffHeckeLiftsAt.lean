import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.LocalTransferIntertwiners
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.LocalizationParts
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSplitProdRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ForallExistsTransfer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePlacesNotPairwiseConjugate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankWeightComponentEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassPresExtMemExtBijIsom

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult

namespace GlobalTheory.HeckeLiftsCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section General

/- English proof (translation)
Establish `hj : ∀ f, j f = ∑ i, σ (b.repr f i) • j (b i)` using `fun f => by conv_lhs => rw [← b.sum_repr f]`. Simplify using `only [map_sum, map_smulₛₗ]`. Establish `hsp' : ⊤ ≤ Submodule.span L (Set.range fun i => j (b i))`. Rewrite using `[← hsp, Submodule.span_le]`. Introduce and unpack `_ ⟨f, rfl⟩`.

Rewrite using `[hj]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Use `⟨(Module.Basis.mk hli hsp').constr L fun i => j (T (b i)), fun f => ?_⟩` and prove the remaining obligations. Establish `h1 : ∀ i, (Module.Basis.mk hli hsp').constr L (fun i => j (T (b i))) (j (b i)) = j (T (b i))` using `fun i => by`. Use `(Module.Basis.mk hli hsp').constr_basis L (fun i => j (T (b i))) i` as an intermediate fact.

Rewrite `this` using `[Module.Basis.mk_apply]`. Then use the resulting hypothesis. Rewrite using `[hj f]`. Use `conv_rhs => rw [← b.sum_repr f]`. Simplify using `only [map_sum, map_smulₛₗ, h1, RingHom.id_apply]`.
-/
theorem exists_extend {K L M H ι : Type} [Field K] [Field L] [AddCommGroup M] [Module K M] [AddCommGroup H] [Module L H]
    [Fintype ι] {σ : K →+* L} (j : M →ₛₗ[σ] H) (b : Module.Basis ι K M) (hli : LinearIndependent L fun i => j (b i))
    (hsp : Submodule.span L (Set.range j) = ⊤) (T : Module.End K M) :
    ∃ T' : Module.End L H, ∀ f, T' (j f) = j (T f) := by
  have hj : ∀ f, j f = ∑ i, σ (b.repr f i) • j (b i) := fun f => by
    conv_lhs => rw [← b.sum_repr f]
    simp only [map_sum, map_smulₛₗ]
  have hsp' : ⊤ ≤ Submodule.span L (Set.range fun i => j (b i)) := by
    rw [← hsp, Submodule.span_le]
    rintro _ ⟨f, rfl⟩
    rw [hj]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨(Module.Basis.mk hli hsp').constr L fun i => j (T (b i)), fun f => ?_⟩
  have h1 : ∀ i, (Module.Basis.mk hli hsp').constr L (fun i => j (T (b i))) (j (b i)) = j (T (b i)) := fun i => by
    have := (Module.Basis.mk hli hsp').constr_basis L (fun i => j (T (b i))) i
    rwa [Module.Basis.mk_apply] at this
  rw [hj f]
  conv_rhs => rw [← b.sum_repr f]
  simp only [map_sum, map_smulₛₗ, h1, RingHom.id_apply]

/- English proof (translation)
Use `⟨fun a ha => ?_, ?_⟩` and prove the remaining obligations. Take `⟨a', ha', rfl⟩` from `Finset.mem_image.1 ha`. Take `⟨k₁, k₂, rfl⟩` from `h.1 a' ha'`. Conclude with `⟨⟨φ k₁, (hJ _ (hJN _ k₁.2)).2 k₁.2⟩, ⟨φ k₂, (hJ _ (hJN _ k₂.2)).2 k₂.2⟩, by simp only [map_mul]⟩`. Introduce and unpack `_ ⟨⟨k₁, h₁⟩, ⟨k₂, h₂⟩, rfl⟩`.

Take `⟨g₁, n₁, rfl⟩` from `hs k₁`. Take `⟨g₂, n₂, rfl⟩` from `hs k₂`. Take `⟨a, ⟨ha, haJ⟩, hu⟩` from `h.2 (g₁ * α * g₂) ⟨⟨g₁, (hJ _ n₁).1 h₁⟩, ⟨g₂, (hJ _ n₂).1 h₂⟩, rfl⟩`. Establish `key : ∀ c ∈ R, (φ c)⁻¹ * (φ g₁ * φ α * φ g₂) ∈ J ↔ c⁻¹ * (g₁ * α * g₂) ∈ J₀` using `fun c hc => by`. Rewrite using `[← hJ _ (N.mul_mem (N.inv_mem (hR c hc)) (N.mul_mem (N.mul_mem n₁ hα) n₂))]`.

Simplify using `only [map_mul, map_inv]`. Use `⟨φ a, ⟨Finset.mem_image_of_mem _ ha, (key a ha).2 haJ⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨hc, hcJ⟩`. Take `⟨c, hc', rfl⟩` from `Finset.mem_image.1 hc`. Rewrite using `[hu c ⟨hc', (key c hc').1 hcJ⟩]`.
-/
theorem isDC_image {H G : Type} [Group H] [Group G] [DecidableEq G] (φ : H →* G) (N J₀ : Subgroup H) (J : Subgroup G)
    (hs : ∀ x, ∃ g ∈ N, φ g = x) (hJ : ∀ g, g ∈ N → (φ g ∈ J ↔ g ∈ J₀)) (hJN : ∀ g ∈ J₀, g ∈ N)
    {α : H} (hα : α ∈ N) {R : Finset H} (hR : ∀ a ∈ R, a ∈ N) (h : Bridge.IsDC J₀ α R) :
    Bridge.IsDC J (φ α) (R.image φ) := by
  refine ⟨fun a ha => ?_, ?_⟩
  · obtain ⟨a', ha', rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨k₁, k₂, rfl⟩ := h.1 a' ha'
    exact ⟨⟨φ k₁, (hJ _ (hJN _ k₁.2)).2 k₁.2⟩, ⟨φ k₂, (hJ _ (hJN _ k₂.2)).2 k₂.2⟩, by simp only [map_mul]⟩
  · rintro _ ⟨⟨k₁, h₁⟩, ⟨k₂, h₂⟩, rfl⟩
    obtain ⟨g₁, n₁, rfl⟩ := hs k₁
    obtain ⟨g₂, n₂, rfl⟩ := hs k₂
    obtain ⟨a, ⟨ha, haJ⟩, hu⟩ := h.2 (g₁ * α * g₂) ⟨⟨g₁, (hJ _ n₁).1 h₁⟩, ⟨g₂, (hJ _ n₂).1 h₂⟩, rfl⟩
    have key : ∀ c ∈ R, (φ c)⁻¹ * (φ g₁ * φ α * φ g₂) ∈ J ↔ c⁻¹ * (g₁ * α * g₂) ∈ J₀ := fun c hc => by
      rw [← hJ _ (N.mul_mem (N.inv_mem (hR c hc)) (N.mul_mem (N.mul_mem n₁ hα) n₂))]
      simp only [map_mul, map_inv]
    refine ⟨φ a, ⟨Finset.mem_image_of_mem _ ha, (key a ha).2 haJ⟩, ?_⟩
    rintro _ ⟨hc, hcJ⟩
    obtain ⟨c, hc', rfl⟩ := Finset.mem_image.1 hc
    rw [hu c ⟨hc', (key c hc').1 hcJ⟩]

/- English proof (translation)
Use `⟨fun k hk => ?_, ?_, ?_⟩` and prove the remaining obligations. Take `⟨g, hg, rfl⟩` from `hs k`. Take `⟨k₁, h₁, k₂, h₂, s₁, s₂, rfl⟩` from `hsp g ((hJ g hg).1 hk)`. Use `⟨φ k₁, (hJ _ (hJN _ h₁)).2 h₁, φ k₂, (hJ _ (hJN _ h₂)).2 h₂, ⟨k₁, s₁, rfl⟩, map_mul _ _ _, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨l, hl, rfl⟩`.

Conclude with `(hc l k₂ hl s₂).symm.map φ`. Introduce and unpack `⟨k, hk⟩ ⟨g, hg, hgk⟩`. Take `rfl : φ g = k` from `hgk`. Rewrite using `[hχe, hχ g ((hJ g (hLN g hg)).1 hk) hg]`. Introduce and unpack `_ ⟨α, hα, rfl⟩`.

Take `⟨Rr, r0, r1, r2⟩` from `hR α hα`. Establish `hdc : Bridge.IsDC J₀ α Rr`. Use `HeckeParts.isDC_of_local hα r0 (fun k hk => ?_) r1 r2` and prove the remaining obligations. Take `⟨k₁, h₁, k₂, h₂, s₁, s₂, rfl⟩` from `hsp k hk`. Conclude with `⟨k₁, h₁, k₂, h₂, s₁, hc α k₂ hα s₂, rfl⟩`.

Use `⟨Rr.image φ, fun a ha => ?_, isDC_image φ N J₀ J hs hJ hJN (hLN α hα) (fun a ha => hLN a (r0 a ha)) hdc⟩` and prove the remaining obligations. Take `⟨a', ha', rfl⟩` from `Finset.mem_image.1 ha`. Conclude with `⟨a', r0 a' ha', rfl⟩`.
-/
theorem transport_local {H G : Type} [Group H] [Group G] (φ : H →* G) (N J₀ L₀ : Subgroup H) (J : Subgroup G)
    (q : H → Prop) (χ : J → ℂ) (χ₀ : H → ℂ)
    (hs : ∀ x, ∃ g ∈ N, φ g = x) (hJ : ∀ g, g ∈ N → (φ g ∈ J ↔ g ∈ J₀)) (hJN : ∀ g ∈ J₀, g ∈ N) (hLN : ∀ g ∈ L₀, g ∈ N)
    (hc : ∀ g g', g ∈ L₀ → q g' → Commute g g') (hχe : ∀ g (h : φ g ∈ J), χ ⟨φ g, h⟩ = χ₀ g)
    (hχ : ∀ g ∈ J₀, g ∈ L₀ → χ₀ g = 1)
    (hsp : ∀ k ∈ J₀, ∃ k₁ ∈ J₀, ∃ k₂ ∈ J₀, k₁ ∈ L₀ ∧ q k₂ ∧ k = k₁ * k₂)
    (hR : ∀ α ∈ L₀, ∃ R : Finset H, (∀ γ ∈ R, γ ∈ L₀) ∧ (∀ γ ∈ R, ∃ k₁ ∈ J₀ ⊓ L₀, ∃ k₂ ∈ J₀ ⊓ L₀, γ = k₁ * α * k₂) ∧
      ∀ y, (∃ k₁ ∈ J₀ ⊓ L₀, ∃ k₂ ∈ J₀ ⊓ L₀, y = k₁ * α * k₂) → ∃! γ, γ ∈ R ∧ γ⁻¹ * y ∈ J₀ ⊓ L₀) :
    HkB.LocSplit J (L₀.map φ) ∧ (∀ k : J, (k : G) ∈ L₀.map φ → χ k = 1) ∧
      ∀ x ∈ L₀.map φ, ∃ B : Finset G, (∀ a ∈ B, a ∈ L₀.map φ) ∧ Bridge.IsDC J x B := by
  classical
  refine ⟨fun k hk => ?_, ?_, ?_⟩
  · obtain ⟨g, hg, rfl⟩ := hs k
    obtain ⟨k₁, h₁, k₂, h₂, s₁, s₂, rfl⟩ := hsp g ((hJ g hg).1 hk)
    refine ⟨φ k₁, (hJ _ (hJN _ h₁)).2 h₁, φ k₂, (hJ _ (hJN _ h₂)).2 h₂, ⟨k₁, s₁, rfl⟩, map_mul _ _ _, ?_⟩
    rintro _ ⟨l, hl, rfl⟩
    exact (hc l k₂ hl s₂).symm.map φ
  · rintro ⟨k, hk⟩ ⟨g, hg, hgk⟩
    obtain rfl : φ g = k := hgk
    rw [hχe, hχ g ((hJ g (hLN g hg)).1 hk) hg]
  · rintro _ ⟨α, hα, rfl⟩
    obtain ⟨Rr, r0, r1, r2⟩ := hR α hα
    have hdc : Bridge.IsDC J₀ α Rr := by
      refine HeckeParts.isDC_of_local hα r0 (fun k hk => ?_) r1 r2
      obtain ⟨k₁, h₁, k₂, h₂, s₁, s₂, rfl⟩ := hsp k hk
      exact ⟨k₁, h₁, k₂, h₂, s₁, hc α k₂ hα s₂, rfl⟩
    refine ⟨Rr.image φ, fun a ha => ?_, isDC_image φ N J₀ J hs hJ hJN (hLN α hα) (fun a ha => hLN a (r0 a ha)) hdc⟩
    obtain ⟨a', ha', rfl⟩ := Finset.mem_image.1 ha
    exact ⟨a', r0 a' ha', rfl⟩

end General

variable {D : D7}

/- English proof (translation)
Unfold `IndefiniteRowSideFullHecke.InertSphericalIndices.IsInertPl`. Rewrite using `[Formalism.DivisionValues.GluingInclusion.conjIdeal_eq]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `SplitHeckeAdj.isConjPl_conj P` as an intermediate fact.

Rewrite `this` using `[HeightOneSpectrum.ext h]`. Then use the resulting hypothesis. Introduce `h`. Rewrite using `[← SplitHeckeAdj.eq_conj_of_isConjPl h]`.
-/
theorem isInertPl_iff (P : Pl D.host.E) : IndefiniteRowSideFullHecke.InertSphericalIndices.IsInertPl P ↔ IsConjPl P P := by
  unfold IndefiniteRowSideFullHecke.InertSphericalIndices.IsInertPl
  rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq]
  constructor
  · intro h
    have := SplitHeckeAdj.isConjPl_conj P
    rwa [HeightOneSpectrum.ext h] at this
  · intro h
    rw [← SplitHeckeAdj.eq_conj_of_isConjPl h]

/- English proof (translation)
Take `⟨Φ, hΦ⟩` from `IdemSupport.exists_comp D`. Take `⟨ε, hε⟩` from `IdemSupport.exists_placeIdem (D := D) (P.under (𝓞 D.host.F))`. Take `⟨h0, h1, h2⟩` from `IdemSupport.place_comp hΦ hε`. Establish `hc : P = IdemSupport.cP P` using `(IdemSupport.isConjPl_iff P P).1 hP`. Establish `hd : IdemSupport.IsDelta Φ P (algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) ε)` using `⟨h0, h1 P rfl, fun Q hQ => h2 Q fun h => (IdemSupport.eq_or_eq_cP h).elim hQ fun h => hQ (h.trans hc.symm)⟩`.

Establish `hi` using `IdemSupport.place_idem hΦ hε`. Establish `ht` using `(IdemSupport.tie_iff hΦ hi h0 P).2 hd`. Use `⟨_, Or.inr ⟨rfl, ⟨_, ε, hε, rfl⟩, ht⟩, fun f => ⟨fun hf => ?_, ?_⟩, fun f => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Take `⟨k1, ⟨v, ε', hε', k2⟩, kt⟩` from `hf`. Use `IdemSupport.delta_unique hΦ ((IdemSupport.tie_iff hΦ k1 ?_ P).1 kt) hd` and prove the remaining obligations.

Break down `k2 with ⟨k2, k3⟩ | k2` into its components or cases. Establish `: f = (f + cA D f) * f` using `by linear_combination -k1 - k2`. Rewrite using `[this, k3, RingHom.map_mul, (IdemSupport.place_comp hΦ hε').1, zero_mul]`. Rewrite using `[k2, (IdemSupport.place_comp hΦ hε').1]`. Introduce and unpack `rfl`.

Conclude with `⟨hi, ⟨_, ε, hε, Or.inr rfl⟩, ht⟩`. Introduce and unpack `⟨ε', hε', rfl⟩`. Rewrite using `[IdemSupport.placeIdem_unique hε' hε]`. Introduce and unpack `rfl`. Conclude with `⟨ε, hε, rfl⟩`.
-/
theorem exists_idem {P : Pl D.host.E} (hP : IsConjPl P P) :
    ∃ e : Formalism.L2.Theta.AE D, IsPrimeIdem P e e ∧ (∀ f, Formalism.L2.JoinChr.IsPlIdem D f P ↔ f = e) ∧
      ∀ f, (∃ ε, IsPlaceIdem D (P.under (𝓞 D.host.F)) ε ∧ f = algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) ε) ↔ f = e := by
  obtain ⟨Φ, hΦ⟩ := IdemSupport.exists_comp D
  obtain ⟨ε, hε⟩ := IdemSupport.exists_placeIdem (D := D) (P.under (𝓞 D.host.F))
  obtain ⟨h0, h1, h2⟩ := IdemSupport.place_comp hΦ hε
  have hc : P = IdemSupport.cP P := (IdemSupport.isConjPl_iff P P).1 hP
  have hd : IdemSupport.IsDelta Φ P (algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) ε) :=
    ⟨h0, h1 P rfl, fun Q hQ => h2 Q fun h => (IdemSupport.eq_or_eq_cP h).elim hQ fun h => hQ (h.trans hc.symm)⟩
  have hi := IdemSupport.place_idem hΦ hε
  have ht := (IdemSupport.tie_iff hΦ hi h0 P).2 hd
  refine ⟨_, Or.inr ⟨rfl, ⟨_, ε, hε, rfl⟩, ht⟩, fun f => ⟨fun hf => ?_, ?_⟩, fun f => ⟨?_, ?_⟩⟩
  · obtain ⟨k1, ⟨v, ε', hε', k2⟩, kt⟩ := hf
    refine IdemSupport.delta_unique hΦ ((IdemSupport.tie_iff hΦ k1 ?_ P).1 kt) hd
    rcases k2 with ⟨k2, k3⟩ | k2
    · have : f = (f + cA D f) * f := by linear_combination -k1 - k2
      rw [this, k3, RingHom.map_mul, (IdemSupport.place_comp hΦ hε').1, zero_mul]
    · rw [k2, (IdemSupport.place_comp hΦ hε').1]
  · rintro rfl
    exact ⟨hi, ⟨_, ε, hε, Or.inr rfl⟩, ht⟩
  · rintro ⟨ε', hε', rfl⟩
    rw [IdemSupport.placeIdem_unique hε' hε]
  · rintro rfl
    exact ⟨ε, hε, rfl⟩

/- English proof (translation)
Take `⟨e, -, h1, h2⟩` from `exists_idem hP`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨α, ⟨hα, ε, hε, hs⟩, hx⟩`. Conclude with `⟨_, α, (h1 _).2 ((h2 _).1 ⟨ε, hε, rfl⟩), hα, hs, hx⟩`. Introduce and unpack `⟨f, α, hf, hα, hs, hx⟩`.

Take `⟨ε, hε, rfl⟩` from `(h2 f).2 ((h1 f).1 hf)`. Conclude with `⟨α, ⟨hα, ε, hε, hs⟩, hx⟩`.
-/
theorem isLocF_iff (V : HSp D) {P : Pl D.host.E} (hP : IsConjPl P P) (x : Bridge.Gf V) :
    IndefiniteRowSideFullHecke.InertSphericalIndices.IsLocF V P x ↔ IndefiniteRowSideFullHecke.LocalHeckeLifts.IsLocAt V P x := by
  obtain ⟨e, -, h1, h2⟩ := exists_idem hP
  constructor
  · rintro ⟨α, ⟨hα, ε, hε, hs⟩, hx⟩
    exact ⟨_, α, (h1 _).2 ((h2 _).1 ⟨ε, hε, rfl⟩), hα, hs, hx⟩
  · rintro ⟨f, α, hf, hα, hs, hx⟩
    obtain ⟨ε, hε, rfl⟩ := (h2 f).2 ((h1 f).1 hf)
    exact ⟨α, ⟨hα, ε, hε, hs⟩, hx⟩

set_option maxHeartbeats 800000 in

/- English proof (translation)
Take `⟨e, he, h1, -⟩` from `exists_idem hP`. Take `⟨hff, hcf, hG, -⟩` from `(GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e e he`. Establish `hone : ((1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal`. Rewrite using `[Nat.cast_one]`. Conclude with `(Ideal.ne_top_iff_one _).1 P.isPrime.ne_top`.

Establish `hoff' : ∀ PP, PP ∈ (flag1L L).Pg ∨ PP ∈ (flag1L L).Q → PP ≠ P ∧ ¬ IsConjPl PP P` using `fun PP h => by`. Use `⟨fun e => hoff PP h (e ▸ hP), fun hc => hoff PP h ?_⟩` and prove the remaining obligations. Establish `e1` using `SplitHeckeAdj.eq_conj_of_isConjPl hc`. Establish `e2` using `SplitHeckeAdj.eq_conj_of_isConjPl hP`. Establish `e3 : PP = P` using `by rw [e2, e1, Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl]`.

Conclude with `e3 ▸ hP`. Take `⟨-, hχ, hsp⟩` from `(GlobalTheory.T.level_hyperspecial_trivialCharacter_splits_off_places V β Λ 1 (flag1L L) hβ).2 P e e he hone hoff'`. Establish `h5` using `transport_local (SplitHeckeAdj.fin V) (GfC V) (levG V β (flag1L L)) (IdemSupport.suppGroup V e) (levEnv V β L).J (SuppF V (1 - e)) (fun k => ((levEnv V β L).χ k : ℂ)) (levChi V β (flag1L L)) (SplitHeckeAdj.fin_lift V) (fun g => SplitHeckeAdj.mem_J V β L) (fun g hg => hg.1) hG (fu …`. Establish `h6` using `HeckeLabels.exists_isCosetRep V β (flag1L L) he hα`. Conclude with `h6.imp fun Rr h => ⟨h.1, fun γ hγ => (h.2.1 γ hγ).2, h.2.2⟩`.

Use `⟨(IdemSupport.suppGroup V e).map (SplitHeckeAdj.fin V), fun x => ⟨fun hx => ?_, fun hx => ?_⟩, h5.1, fun k hk => Units.ext (h5.2.1 k hk), h5.2.2⟩` and prove the remaining obligations. Conclude with `hx.elim fun g hg => ⟨e, g, (h1 e).2 rfl, hG g hg.1, hg.1, (congrArg Subtype.val hg.2).symm⟩`. Conclude with `hx.elim fun f hf => hf.elim fun g hg => ⟨g, (h1 f).1 hg.1 ▸ hg.2.2.1, Subtype.ext hg.2.2.2.symm⟩`.
-/
theorem exists_local (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (L : LevDat D.host.E ℂ V.rank) (hβ : IsBaseFrame V β Λ 1) {P : Pl D.host.E} (hP : IsConjPl P P)
    (hoff : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → ¬ IsConjPl PP PP) :
    ∃ Lc : Subgroup (Bridge.Gf V), (∀ x, x ∈ Lc ↔ IndefiniteRowSideFullHecke.LocalHeckeLifts.IsLocAt V P x) ∧ HkB.LocSplit (levEnv V β L).J Lc ∧
      (∀ k : (levEnv V β L).J, (k : Bridge.Gf V) ∈ Lc → (levEnv V β L).χ k = 1) ∧
      ∀ x ∈ Lc, ∃ B : Finset (Bridge.Gf V), (∀ a ∈ B, a ∈ Lc) ∧ Bridge.IsDC (levEnv V β L).J x B := by
  classical
  obtain ⟨e, he, h1, -⟩ := exists_idem hP
  obtain ⟨hff, hcf, hG, -⟩ := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e e he
  have hone : ((1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    rw [Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top
  have hoff' : ∀ PP, PP ∈ (flag1L L).Pg ∨ PP ∈ (flag1L L).Q → PP ≠ P ∧ ¬ IsConjPl PP P := fun PP h => by
    refine ⟨fun e => hoff PP h (e ▸ hP), fun hc => hoff PP h ?_⟩
    have e1 := SplitHeckeAdj.eq_conj_of_isConjPl hc
    have e2 := SplitHeckeAdj.eq_conj_of_isConjPl hP
    have e3 : PP = P := by rw [e2, e1, Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl]
    exact e3 ▸ hP
  obtain ⟨-, hχ, hsp⟩ := (GlobalTheory.T.level_hyperspecial_trivialCharacter_splits_off_places V β Λ 1 (flag1L L) hβ).2 P e e he hone hoff'
  have h5 := transport_local (SplitHeckeAdj.fin V) (GfC V) (levG V β (flag1L L)) (IdemSupport.suppGroup V e) (levEnv V β L).J
    (SuppF V (1 - e)) (fun k => ((levEnv V β L).χ k : ℂ)) (levChi V β (flag1L L)) (SplitHeckeAdj.fin_lift V)
    (fun g => SplitHeckeAdj.mem_J V β L) (fun g hg => hg.1) hG (fun g g' => SplitHeckeAdj.commute_compl V e hff hcf)
    (fun g => SplitHeckeAdj.chi_eq V β L) hχ hsp fun α hα => by
      have h6 := HeckeLabels.exists_isCosetRep V β (flag1L L) he hα
      exact h6.imp fun Rr h => ⟨h.1, fun γ hγ => (h.2.1 γ hγ).2, h.2.2⟩
  refine ⟨(IdemSupport.suppGroup V e).map (SplitHeckeAdj.fin V), fun x => ⟨fun hx => ?_, fun hx => ?_⟩, h5.1,
    fun k hk => Units.ext (h5.2.1 k hk), h5.2.2⟩
  · exact hx.elim fun g hg => ⟨e, g, (h1 e).2 rfl, hG g hg.1, hg.1, (congrArg Subtype.val hg.2).symm⟩
  · exact hx.elim fun f hf => hf.elim fun g hg => ⟨g, (h1 f).1 hg.1 ▸ hg.2.2.1, Subtype.ext hg.2.2.2.symm⟩

section At

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

/- English proof (translation)
The claim follows from `h.elim (fun h => TypePlaces.not_isConjPl R.C.P R.Pg hC.lev.Pg PP h PP h) fun h => (hC.lev.Q_pl t PP h).2 PP h`.
-/
theorem level_split (hC : R.Char F) (t : T) (PP : Pl D.host.E) (h : PP ∈ R.Pg ∨ PP ∈ R.Q t) : ¬ IsConjPl PP PP :=
  h.elim (fun h => TypePlaces.not_isConjPl R.C.P R.Pg hC.lev.Pg PP h PP h) fun h => (hC.lev.Q_pl t PP h).2 PP h

def forget (R : RealDat D A Ks) (j : Fin D.R.m) (t : T) : IndefiniteRowSideFullHecke.LocalHeckeLifts.SphOp R j t → IndefiniteRowSideFullHecke.InertSphericalIndices.SphIx A j t :=
  Sum.map id fun a => ⟨(a.1.1, a.1.2.1), (isInertPl_iff _).2 a.2.1, (isLocF_iff _ a.2.1 _).2 a.2.2.2.2.1⟩

open Classical in

def dropInert (R : RealDat D A Ks) : RealDat D A Ks := { R with Sb := R.Sb.filter fun P => ¬ IsConjPl P P }

end At

end GlobalTheory.HeckeLiftsCompare

end
