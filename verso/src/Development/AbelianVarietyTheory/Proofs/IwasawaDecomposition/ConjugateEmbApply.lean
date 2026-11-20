import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGaloisSubfieldConjStable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinsetTypeNormPrincipal
import Development.AbelianVarietyTheory.Definitions.Foundations.AuxiliaryFrameNormalizedSpaces
import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem

namespace GlobalTheory.Mem.BaseExt

section ext

variable {K K' : Type} [Field K] [Field K'] (f : K →+* K')

/- English proof (translation)
Use `le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono (Set.image_mono Submodule.subset_span))` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩`. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul a x _ hx`. Establish `: f (a • x) = RingOfIntegers.mapRingHom f a • f x`. Rewrite using `[Algebra.smul_def, Algebra.smul_def, map_mul]`.

Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem span_image_span (s : Set K) :
    Submodule.span (𝓞 K') (f '' (Submodule.span (𝓞 K) s : Set K)) = Submodule.span (𝓞 K') (f '' s) := by
  refine le_antisymm (Submodule.span_le.2 ?_)
    (Submodule.span_mono (Set.image_mono Submodule.subset_span))
  rintro _ ⟨x, hx, rfl⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    have : f (a • x) = RingOfIntegers.mapRingHom f a • f x := by
      rw [Algebra.smul_def, Algebra.smul_def, map_mul]; rfl
    rw [this]
    exact Submodule.smul_mem _ _ hx

def extend : Submodule (𝓞 K) K →* Submodule (𝓞 K') K' where
  toFun M := Submodule.span (𝓞 K') (f '' (M : Set K))
  map_one' := by
    rw [Submodule.one_eq_span, span_image_span, Submodule.one_eq_span]; simp
  map_mul' M N := by
    conv_lhs => rw [← M.span_eq, ← N.span_eq, Submodule.span_mul_span, span_image_span]
    rw [Submodule.span_mul_span, Set.image_mul]

/- English proof (translation)
The claim follows from `span_image_span f s`.
-/
theorem extend_span (s : Set K) :
    extend f (Submodule.span (𝓞 K) s) = Submodule.span (𝓞 K') (f '' s) := span_image_span f s

end ext

section host

variable {R : Ranks} (H : Host R)

/- English proof (translation)
Rewrite using `[Formalism.L2.Geo.emb_mul_cc_comp]`. Use `RingHom.ext fun x => ?_` and prove the remaining obligations. Establish `hcm` using `H.isCMField_hostE`. Establish `h : IsCMField.complexConj H.E x = H.conj x`. Apply `H.φ₀.injective` to reduce the goal to its premises.

Rewrite using `[IsCMField.complexEmbedding_complexConj, H.conjE_apply]`. Use `show starRingEnd ℂ (H.emb g x) = H.emb g (H.conj x)`. Rewrite using `[← h, IsCMField.complexEmbedding_complexConj]`.
-/
theorem conjugate_emb (g : R.GG) :
    ComplexEmbedding.conjugate (H.emb g) = H.emb (g * R.cc) := by
  rw [Formalism.L2.Geo.emb_mul_cc_comp]
  refine RingHom.ext fun x => ?_
  have hcm := H.isCMField_hostE
  have h : IsCMField.complexConj H.E x = H.conj x := by
    apply H.φ₀.injective
    rw [IsCMField.complexEmbedding_complexConj, H.conjE_apply]
  show starRingEnd ℂ (H.emb g x) = H.emb g (H.conj x)
  rw [← h, IsCMField.complexEmbedding_complexConj]

/- English proof (translation)
Rewrite using `[conjugate_emb, Formalism.L2.Geo.emb_mul_cc_comp]`. Both sides reduce to the same expression.
-/
theorem conjugate_emb_apply (g : R.GG) (x : H.E) :
    ComplexEmbedding.conjugate (H.emb g) x = H.emb g (H.conj x) := by
  rw [conjugate_emb, Formalism.L2.Geo.emb_mul_cc_comp]; rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun ⟨t, ht⟩ => (factEmb R H).1.1 ht ▸ t.2, fun h => ⟨⟨g, h⟩, rfl⟩⟩`.
-/
theorem ex_emb_iff (g : R.GG) :
    (∃ t : Tau R, H.emb t = H.emb g) ↔ g ∈ R.Psi :=
  ⟨fun ⟨t, ht⟩ => (factEmb R H).1.1 ht ▸ t.2, fun h => ⟨⟨g, h⟩, rfl⟩⟩

/- English proof (translation)
Take `⟨g, rfl⟩` from `(factEmb R H).1.2 σ`. Rewrite using `[conjugate_emb, ex_emb_iff, ex_emb_iff]`. Conclude with `Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem g`.
-/
theorem emb_cm (σ : H.E →+* ℂ) :
    (∃ t : Tau R, H.emb t = σ) ↔ ¬ ∃ t : Tau R, H.emb t = ComplexEmbedding.conjugate σ := by
  obtain ⟨g, rfl⟩ := (factEmb R H).1.2 σ
  rw [conjugate_emb, ex_emb_iff, ex_emb_iff]
  exact Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem g

/- English proof (translation)
Establish `hc : ∀ σ : H.E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ` using `fun σ => star_star σ`. Establish `hi : ∀ {a b : Tau R}, H.emb a = H.emb b → a = b` using `fun h => Subtype.ext ((factEmb R H).1.1 h)`. Prove the components needed by the constructor for the conclusion. Apply the tactic sequence `rintro (a | a) (b | b) h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h`. Rewrite using `[hi h]`.

Conclude with `absurd ⟨a, h⟩ ((emb_cm H (H.emb b)).1 ⟨b, rfl⟩)`. Conclude with `absurd ⟨b, h.symm⟩ ((emb_cm H (H.emb a)).1 ⟨a, rfl⟩)`. Use `congrArg ComplexEmbedding.conjugate h` as an intermediate fact. Rewrite `this` using `[hc, hc]`. Rewrite using `[hi this]`.

Introduce `σ`. Distinguish the cases in `h : ∃ t : Tau R, H.emb t = ComplexEmbedding.conjugate σ`. Take `⟨t, ht⟩` from `h`. Conclude with `⟨Sum.inr t, by simp only [Sum.elim_inr]; rw [ht, hc]⟩`. Take `⟨t, ht⟩` from `(emb_cm H σ).2 h`.

Conclude with `⟨Sum.inl t, ht⟩`.
-/
theorem sum_emb_bijective : Function.Bijective
    (Sum.elim (fun t : Tau R => H.emb t) fun t : Tau R => ComplexEmbedding.conjugate (H.emb t)) := by
  have hc : ∀ σ : H.E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ :=
    fun σ => star_star σ
  have hi : ∀ {a b : Tau R}, H.emb a = H.emb b → a = b := fun h => Subtype.ext ((factEmb R H).1.1 h)
  constructor
  · rintro (a | a) (b | b) h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
    · rw [hi h]
    · exact absurd ⟨a, h⟩ ((emb_cm H (H.emb b)).1 ⟨b, rfl⟩)
    · exact absurd ⟨b, h.symm⟩ ((emb_cm H (H.emb a)).1 ⟨a, rfl⟩)
    · have := congrArg ComplexEmbedding.conjugate h
      rw [hc, hc] at this
      rw [hi this]
  · intro σ
    by_cases h : ∃ t : Tau R, H.emb t = ComplexEmbedding.conjugate σ
    · obtain ⟨t, ht⟩ := h
      exact ⟨Sum.inr t, by simp only [Sum.elim_inr]; rw [ht, hc]⟩
    · obtain ⟨t, ht⟩ := (emb_cm H σ).2 h
      exact ⟨Sum.inl t, ht⟩

open Classical in

def typeExp (p q : ℕ) (σ : H.E →+* ℂ) : ℕ := if ∃ t : Tau R, H.emb t = σ then p else q

/- English proof (translation)
The claim follows from `if_pos ⟨t, rfl⟩`.
-/
theorem typeExp_emb (p q : ℕ) (t : Tau R) : typeExp H p q (H.emb t) = p := if_pos ⟨t, rfl⟩

/- English proof (translation)
The claim follows from `if_neg ((emb_cm H _).1 ⟨t, rfl⟩)`.
-/
theorem typeExp_conj (p q : ℕ) (t : Tau R) :
    typeExp H p q (ComplexEmbedding.conjugate (H.emb t)) = q := if_neg ((emb_cm H _).1 ⟨t, rfl⟩)

/- English proof (translation)
Unfold `typeExp`. Distinguish the cases in `h : ∃ t : Tau R, H.emb t = σ`. Rewrite using `[if_pos h, if_neg ((emb_cm H σ).1 h)]`. Rewrite using `[if_neg h, if_pos (not_not.1 (fun h' => h ((emb_cm H σ).2 h'))), add_comm]`.
-/
theorem typeExp_add (p q : ℕ) (σ : H.E →+* ℂ) :
    typeExp H p q σ + typeExp H p q (ComplexEmbedding.conjugate σ) = p + q := by
  unfold typeExp
  by_cases h : ∃ t : Tau R, H.emb t = σ
  · rw [if_pos h, if_neg ((emb_cm H σ).1 h)]
  · rw [if_neg h, if_pos (not_not.1 (fun h' => h ((emb_cm H σ).2 h'))), add_comm]

/- English proof (translation)
Rewrite using `[← (sum_emb_bijective H).prod_comp, Fintype.prod_sum_type, Finset.prod_mul_distrib]`. Simplify using `only [Sum.elim_inl, Sum.elim_inr, typeExp_emb, typeExp_conj]`.
-/
theorem prod_typeExp {M : Type} [CommMonoid M] (p q : ℕ) (F : (H.E →+* ℂ) → M) :
    ∏ σ, F σ ^ typeExp H p q σ =
      ∏ t : Tau R, (F (H.emb t) ^ p * F (ComplexEmbedding.conjugate (H.emb t)) ^ q) := by
  rw [← (sum_emb_bijective H).prod_comp, Fintype.prod_sum_type, Finset.prod_mul_distrib]
  simp only [Sum.elim_inl, Sum.elim_inr, typeExp_emb, typeExp_conj]

end host

/- English proof (translation)
Break down `Nat.eq_zero_or_pos N with rfl | h` into its components or cases. Simplify using `using isAlgebraic_one`. Conclude with `((Complex.isPrimitiveRoot_exp N h.ne').isIntegral h).tower_top.isAlgebraic`.
-/
theorem isAlgebraic_exp (N : ℕ) : IsAlgebraic ℚ (Complex.exp (2 * Real.pi * Complex.I / N)) := by
  rcases Nat.eq_zero_or_pos N with rfl | h
  · simpa using isAlgebraic_one
  · exact ((Complex.isPrimitiveRoot_exp N h.ne').isIntegral h).tower_top.isAlgebraic

/- English proof (translation)
Set `b` to `Module.finBasis ℚ E`. Use `⟨Finset.univ.image fun p : (E →+* ℂ) × Fin (Module.finrank ℚ E) => p.1 (b p.2), ?_, ?_⟩` and prove the remaining obligations. Introduce `z hz`. Take `⟨p, -, rfl⟩` from `Finset.mem_image.1 hz`. Conclude with `(Algebra.IsAlgebraic.isAlgebraic (b p.2)).algHom p.1.toRatAlgHom`.

Introduce `K hK τ x`. Rewrite using `[← b.sum_repr x, map_sum]`. Use `sum_mem fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_rat_smul]`. Conclude with `K.smul_mem (hK _ (Finset.mem_image.2 ⟨(τ, i), Finset.mem_univ _, rfl⟩))`.
-/
theorem exists_gens (E : Type) [Field E] [NumberField E] : ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧
    ∀ K : IntermediateField ℚ ℂ, (∀ z ∈ S, z ∈ K) → ∀ (τ : E →+* ℂ) x, τ x ∈ K := by
  classical
  let b := Module.finBasis ℚ E
  refine ⟨Finset.univ.image fun p : (E →+* ℂ) × Fin (Module.finrank ℚ E) => p.1 (b p.2), ?_, ?_⟩
  · intro z hz
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hz
    exact (Algebra.IsAlgebraic.isAlgebraic (b p.2)).algHom p.1.toRatAlgHom
  · intro K hK τ x
    rw [← b.sum_repr x, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_rat_smul]
    exact K.smul_mem (hK _ (Finset.mem_image.2 ⟨(τ, i), Finset.mem_univ _, rfl⟩))

@[instance_reducible] def starOf (K : IntermediateField ℚ ℂ) (h : ∀ z ∈ K, starRingEnd ℂ z ∈ K) : StarRing K where
  star x := ⟨starRingEnd ℂ x, h _ x.2⟩
  star_involutive x := Subtype.ext (Complex.conj_conj _)
  star_mul x y := Subtype.ext (by
    show starRingEnd ℂ ((x : ℂ) * y) = starRingEnd ℂ y * starRingEnd ℂ x
    rw [map_mul, mul_comm])
  star_add x y := Subtype.ext (map_add (starRingEnd ℂ) (x : ℂ) (y : ℂ))

def toTop (K : IntermediateField ℚ ℂ) : K →+* (⊤ : IntermediateField ℚ K) :=
  (IntermediateField.topEquiv (F := ℚ) (E := K)).symm

/- English proof (translation)
Rewrite using `[extend_span]`. Use `congr 1`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, ⟨a, ha, hy⟩, rfl⟩`.

Conclude with `⟨a, ha, Subtype.ext (hy.trans (he _).symm)⟩`. Introduce and unpack `⟨a, ha, hx⟩`. Conclude with `⟨x.1, ⟨a, ha, (congrArg Subtype.val hx).trans (he _)⟩, rfl⟩`.
-/
theorem image_top {E : Type} [Field E] (K : IntermediateField ℚ ℂ) (𝔞 : Ideal (𝓞 E)) (τ : E →+* ℂ) (e : E → K)
    (he : ∀ a, (e a : ℂ) = τ a) :
    extend (toTop K) (Submodule.span (𝓞 K) {x : K | ∃ a ∈ 𝔞, (x : ℂ) = τ (a : E)}) =
      Submodule.span (𝓞 (⊤ : IntermediateField ℚ K))
        {x : (⊤ : IntermediateField ℚ K) | ∃ a ∈ 𝔞, (x : K) = e (a : E)} := by
  rw [extend_span]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨a, ha, hy⟩, rfl⟩
    exact ⟨a, ha, Subtype.ext (hy.trans (he _).symm)⟩
  · rintro ⟨a, ha, hx⟩
    exact ⟨x.1, ⟨a, ha, (congrArg Subtype.val hx).trans (he _)⟩, rfl⟩

/- English proof (translation)
Introduce `B S₀ S₁ S₂ h₀ h₁ h₂`. Establish `hcm : IsCMField B.host.E` using `B.host.isCMField_hostE`. Establish `hgal : IsGalois ℚ B.host.E` using `B.host.hostE_isGalois`. Take `⟨SE, hSE, hE⟩` from `exists_gens B.host.E`. Use `choose MainNotions hSK hK using fun j : ℕ => GlobalTheory.Mem.exists_finset_typeNorm_principal B.host.E (typeExp B.host (B.R.sigW j).1 (B.R.sigW j).2) _ (typeExp_add B.host _ _)`.

Take `⟨SC, hSC, hC⟩` from `GlobalTheory.Mem.exists_finset_capitulation B.host.E B.host.φ₀`. Set `l : List ℕ` to `[B.restRowsFiniteGroupCard, B.host.g 0 * (B.host.g 0 - 1), B.host.g 1 * (B.host.g 1 - 1), 3 ^ 4, 5 ^ 4]`. Set `l' : List ℕ` to `[B.host.pde, B.host.pde', classNumber B.host.E]`. Set `A : Finset ℕ` to `l.toFinset ∪ l'.toFinset ∪ {B.ramOrder} ∪ Finset.univ.image B.T`. Set `SR : Finset ℂ` to `A.image fun N : ℕ => Complex.exp (2 * Real.pi * Complex.I / N)`.

Take `⟨K, hfd, hKgal, hS, -, hconj⟩` from `GlobalTheory.exists_galois_subfield_conj_stable (S₀ ∪ S₁ ∪ S₂ ∪ SE ∪ SC ∪ SR ∪ (Finset.range (B.R.m + 1)).biUnion MainNotions) (by`. Introduce `z hz`. Simplify using `only [Finset.mem_union, Finset.mem_biUnion] at hz`. Break down `hz with (((((hz | hz) | hz) | hz) | hz) | hz) | ⟨j, -, hz⟩` into its components or cases. Use `exacts [h₀ z hz, h₁ z hz, h₂ z hz, hSE z hz, hSC z hz, by`.

Take `⟨N, -, rfl⟩` from `Finset.mem_image.1 hz`. Conclude with `isAlgebraic_exp N, hSK j z hz])`. Simplify using `only [Finset.mem_union, Finset.mem_biUnion] at hS`. Establish `hEK` using `hE K fun z hz => hS z (by tauto)`. Establish `hR : ∀ N ∈ A, Complex.exp (2 * Real.pi * Complex.I / (N : ℕ)) ∈ K` using `fun N hN => by`.

Establish `hz : Complex.exp (2 * Real.pi * Complex.I / N) ∈ SR` using `Finset.mem_image.2 ⟨N, hN, rfl⟩`. Conclude with `hS _ (by tauto)`. Establish `: NumberField K` using `{}`. Set `f` to `toTop K`. Use `⟨{ toPre := B LL := K starLL := starOf K hconj embLL := K.val starLL_cx := fun _ => rfl embE := B.host.φ₀.codRestrict K (hEK _) embE_φ₀ := rfl LL0 := ⊤ coeffGaloisSubfield_isGalois := IsGalois.of_algEquiv IntermediateField.topEquiv.symm Ks := ⊤ Ks_le := le_rfl E_le_Ks := fun _ => …` and prove the remaining obligations.

Introduce `N hN`. Conclude with `⟨⟨_, hR N (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (List.mem_toFinset.2 hN))))⟩, trivial, rfl⟩`. Introduce `N hN`. Conclude with `⟨⟨_, hR N (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (List.mem_toFinset.2 hN))))⟩, trivial, rfl⟩`. Introduce `𝔞`.

Take `⟨β, hsp⟩` from `hC K (fun z hz => hS z (by tauto)) (hEK _) 𝔞`. Use `⟨f β, ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg (extend f) hsp`. Rewrite `h` using `[extend_span, Set.image_singleton]`. Conclude with `h.trans (image_top K 𝔞 B.host.φ₀ (B.host.φ₀.codRestrict K (hEK _)) fun _ => rfl)`.

Introduce `j _ hj 𝔞 h𝔞`. Take `⟨β, hβ, hsp, hn⟩` from `hK j K (fun z hz => hS z (Or.inr ⟨j, Finset.mem_range.2 (by omega), hz⟩)) hEK 𝔞 h𝔞`. Use `⟨f β, (map_ne_zero f).2 hβ, ?_, fun σ => hn (σ.comp f)⟩` and prove the remaining obligations. Establish `h` using `congrArg (extend f) hsp`. Rewrite `h` using `[prod_typeExp, extend_span, Set.image_singleton, map_prod]`.

Rewrite using `[h]`. Use `Finset.prod_congr rfl fun g _ => ?_` and prove the remaining obligations. Establish `e1` using `image_top K 𝔞 (B.host.emb g) (fun a => B.host.φ₀.codRestrict K (hEK _) (B.host.sigmaOf g a)) fun _ => rfl`. Establish `e2` using `image_top K 𝔞 (ComplexEmbedding.conjugate (B.host.emb g)) (fun a => B.host.φ₀.codRestrict K (hEK _) (B.host.sigmaOf g (B.host.conj a))) fun a => (conjugate_emb_apply B.host g a).symm`. Rewrite using `[map_mul, map_pow, map_pow]`.

Conclude with `congrArg₂ (· * ·) (congrArg (· ^ (B.R.sigW j).1) e1) (congrArg (· ^ (B.R.sigW j).2) e2)`. Conclude with `fun z hz => ⟨⟨z, hS z (by tauto)⟩, trivial, rfl⟩`. Conclude with `fun z hz => ⟨⟨z, hS z (by tauto)⟩, trivial, rfl⟩`. Conclude with `fun z hz => ⟨⟨z, hS z (by tauto)⟩, rfl⟩`.
-/
theorem exists_base : ∀ (B : Pre) (S₀ S₁ S₂ : Finset ℂ), (∀ z ∈ S₀, IsAlgebraic ℚ z) → (∀ z ∈ S₁, IsAlgebraic ℚ z) → (∀ z ∈ S₂, IsAlgebraic ℚ z) → ∃ B' : Base, B'.toPre = B ∧ (∀ z ∈ S₀, ∃ x ∈ B'.Ks, B'.embLL x = z) ∧ (∀ z ∈ S₁, ∃ x ∈ B'.LL0, B'.embLL x = z) ∧ ∀ z ∈ S₂, ∃ x : B'.LL, B'.embLL x = z := by
  classical
  intro B S₀ S₁ S₂ h₀ h₁ h₂
  have hcm : IsCMField B.host.E := B.host.isCMField_hostE
  have hgal : IsGalois ℚ B.host.E := B.host.hostE_isGalois
  obtain ⟨SE, hSE, hE⟩ := exists_gens B.host.E
  choose MainNotions hSK hK using fun j : ℕ => GlobalTheory.Mem.exists_finset_typeNorm_principal B.host.E
    (typeExp B.host (B.R.sigW j).1 (B.R.sigW j).2) _ (typeExp_add B.host _ _)
  obtain ⟨SC, hSC, hC⟩ := GlobalTheory.Mem.exists_finset_capitulation B.host.E B.host.φ₀
  let l : List ℕ := [B.restRowsFiniteGroupCard, B.host.g 0 * (B.host.g 0 - 1), B.host.g 1 * (B.host.g 1 - 1), 3 ^ 4, 5 ^ 4]
  let l' : List ℕ := [B.host.pde, B.host.pde', classNumber B.host.E]
  let A : Finset ℕ := l.toFinset ∪ l'.toFinset ∪ {B.ramOrder} ∪ Finset.univ.image B.T
  let SR : Finset ℂ := A.image fun N : ℕ => Complex.exp (2 * Real.pi * Complex.I / N)
  obtain ⟨K, hfd, hKgal, hS, -, hconj⟩ := GlobalTheory.exists_galois_subfield_conj_stable
    (S₀ ∪ S₁ ∪ S₂ ∪ SE ∪ SC ∪ SR ∪ (Finset.range (B.R.m + 1)).biUnion MainNotions) (by
      intro z hz
      simp only [Finset.mem_union, Finset.mem_biUnion] at hz
      rcases hz with (((((hz | hz) | hz) | hz) | hz) | hz) | ⟨j, -, hz⟩
      exacts [h₀ z hz, h₁ z hz, h₂ z hz, hSE z hz, hSC z hz, by
        obtain ⟨N, -, rfl⟩ := Finset.mem_image.1 hz
        exact isAlgebraic_exp N, hSK j z hz])
  simp only [Finset.mem_union, Finset.mem_biUnion] at hS
  have hEK := hE K fun z hz => hS z (by tauto)
  have hR : ∀ N ∈ A, Complex.exp (2 * Real.pi * Complex.I / (N : ℕ)) ∈ K := fun N hN => by
    have hz : Complex.exp (2 * Real.pi * Complex.I / N) ∈ SR := Finset.mem_image.2 ⟨N, hN, rfl⟩
    exact hS _ (by tauto)
  have : NumberField K := {}
  let f := toTop K
  refine ⟨{ toPre := B
            LL := K
            starLL := starOf K hconj
            embLL := K.val
            starLL_cx := fun _ => rfl
            embE := B.host.φ₀.codRestrict K (hEK _)
            embE_φ₀ := rfl
            LL0 := ⊤
            coeffGaloisSubfield_isGalois := IsGalois.of_algEquiv IntermediateField.topEquiv.symm
            Ks := ⊤
            Ks_le := le_rfl
            E_le_Ks := fun _ => trivial
            roots_Ks := ?_
            roots_Ks' := ?_
            capit := ?_
            kPsi := ?_
            rootOfUnity_eightQ_mem_coeffGaloisSubfield := ⟨⟨_, hR B.ramOrder (Finset.mem_union_left _ (Finset.mem_union_right _
              (Finset.mem_singleton_self _)))⟩, trivial, rfl⟩
            roots_LL := fun u => ⟨⟨_, hR (B.T u) (Finset.mem_union_right _
              (Finset.mem_image_of_mem _ (Finset.mem_univ u)))⟩, rfl⟩ }, rfl, ?_, ?_, ?_⟩
  · intro N hN
    exact ⟨⟨_, hR N (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (List.mem_toFinset.2 hN))))⟩, trivial, rfl⟩
  · intro N hN
    exact ⟨⟨_, hR N (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
      (List.mem_toFinset.2 hN))))⟩, trivial, rfl⟩
  · intro 𝔞
    obtain ⟨β, hsp⟩ := hC K (fun z hz => hS z (by tauto)) (hEK _) 𝔞
    refine ⟨f β, ?_⟩
    have h := congrArg (extend f) hsp
    rw [extend_span, Set.image_singleton] at h
    exact h.trans (image_top K 𝔞 B.host.φ₀ (B.host.φ₀.codRestrict K (hEK _)) fun _ => rfl)
  · intro j _ hj 𝔞 h𝔞
    obtain ⟨β, hβ, hsp, hn⟩ := hK j K
      (fun z hz => hS z (Or.inr ⟨j, Finset.mem_range.2 (by omega), hz⟩)) hEK 𝔞 h𝔞
    refine ⟨f β, (map_ne_zero f).2 hβ, ?_, fun σ => hn (σ.comp f)⟩
    have h := congrArg (extend f) hsp
    rw [prod_typeExp, extend_span, Set.image_singleton, map_prod] at h
    rw [h]
    refine Finset.prod_congr rfl fun g _ => ?_
    have e1 := image_top K 𝔞 (B.host.emb g)
      (fun a => B.host.φ₀.codRestrict K (hEK _) (B.host.sigmaOf g a)) fun _ => rfl
    have e2 := image_top K 𝔞 (ComplexEmbedding.conjugate (B.host.emb g))
      (fun a => B.host.φ₀.codRestrict K (hEK _) (B.host.sigmaOf g (B.host.conj a)))
      fun a => (conjugate_emb_apply B.host g a).symm
    rw [map_mul, map_pow, map_pow]
    exact congrArg₂ (· * ·) (congrArg (· ^ (B.R.sigW j).1) e1) (congrArg (· ^ (B.R.sigW j).2) e2)
  · exact fun z hz => ⟨⟨z, hS z (by tauto)⟩, trivial, rfl⟩
  · exact fun z hz => ⟨⟨z, hS z (by tauto)⟩, trivial, rfl⟩
  · exact fun z hz => ⟨⟨z, hS z (by tauto)⟩, rfl⟩

end GlobalTheory.Mem.BaseExt

end
