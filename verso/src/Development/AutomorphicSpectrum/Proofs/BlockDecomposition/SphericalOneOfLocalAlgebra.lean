import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SetupEig
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CommutativeHeckeActsByScalarOnFixedVectors
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CayleyRuleOfBiInvariantVacuumCoefficient
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmFieldStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryIwahoriFacts
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.CommensuratedOfIsOpenIsCompact

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG GlobalTheory.PRep
open PositivityTheory.Rg.BcB.F.Eig
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.SphLine

section Abstract

open GlobalTheory.LFun GlobalTheory.LFun.SatCompare GlobalTheory.LocGL

variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Take `⟨x₀, hx₀, h0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hne`. Establish `key : ∀ g, ∃ c : ℂ, idem hπ.1 hc (π g x₀) = c • x₀` using `fun g => by`. Take `⟨N, hN, e⟩` from `HeckeScalar.heckeVec_dosetInd_eq_idem hπ hc hK g hx₀`. Take `⟨c, hc'⟩` from `HeckeScalar.exists_scalar G V π K hc hK hcomm hπ hfd _ (Final.DosetIndMem G K ℂ g)`. Establish `h1` using `hc' x₀ hx₀`.

Rewrite `h1` using `[e]`. Use `⟨N⁻¹ * c, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_smul, ← h1, smul_smul, inv_mul_cancel₀ hN, one_smul]`. Establish `all : ∀ a : MonoidAlgebra ℂ G, ∃ c : ℂ, idem hπ.1 hc (orbitMap π x₀ a) = c • x₀` using `fun a => by`. Proceed by induction on `a using MonoidAlgebra.induction_on with`.

Consider the case `of g`. Establish `: orbitMap π x₀ (MonoidAlgebra.of ℂ G g) = π g x₀` using `by show π.asAlgebraHom (MonoidAlgebra.of ℂ G g) x₀ = _`. Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `key g`.

Consider the case `add a b ha hb`. Take `⟨c, hc₁⟩` from `ha`. Take `⟨d, hd⟩` from `hb`. Establish `: orbitMap π x₀ (a + b) = orbitMap π x₀ a + orbitMap π x₀ b` using `map_add _ _ _`. Conclude with `⟨c + d, by rw [this, map_add, hc₁, hd, add_smul]⟩`.

Consider the case `smul r a ha`. Take `⟨c, hc₁⟩` from `ha`. Establish `: orbitMap π x₀ (r • a) = r • orbitMap π x₀ a` using `map_smul _ _ _`. Conclude with `⟨r * c, by rw [this, map_smul, hc₁, smul_smul]⟩`. Use `(finrank_eq_one_iff_of_nonzero' (⟨x₀, hx₀⟩ : fixed π K) fun e => h0 (congrArg Subtype.val e)).2 ?_` and prove the remaining obligations.

Introduce and unpack `⟨x, hx⟩`. Take `⟨a, ha⟩` from `orbitMap_surjective hπ.2 h0 x`. Take `⟨c, hc₁⟩` from `all a`. Use `⟨c, Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite `hc₁` using `[ha, idem_of_mem hπ.1 hc hx]`.

Conclude with `hc₁.symm`.
-/
theorem finrank_fixed_eq_one (π : Representation ℂ G V) (K : Subgroup G) (hc : IsCompact (K : Set G))
    (hK : IsCommensurated K) (hcomm : ∀ f₁ ∈ Hecke ℂ K, ∀ f₂ ∈ Hecke ℂ K, conv K f₁ f₂ = conv K f₂ f₁)
    (hπ : GlobalTheory.LGrp.IsIrrSmooth π) (hfd : FiniteDimensional ℂ (fixed π K)) (hne : fixed π K ≠ ⊥) :
    Module.finrank ℂ (fixed π K) = 1 := by
  obtain ⟨x₀, hx₀, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have key : ∀ g, ∃ c : ℂ, idem hπ.1 hc (π g x₀) = c • x₀ := fun g => by
    obtain ⟨N, hN, e⟩ := HeckeScalar.heckeVec_dosetInd_eq_idem hπ hc hK g hx₀
    obtain ⟨c, hc'⟩ := HeckeScalar.exists_scalar G V π K hc hK hcomm hπ hfd _ (Final.DosetIndMem G K ℂ g)
    have h1 := hc' x₀ hx₀
    rw [e] at h1
    refine ⟨N⁻¹ * c, ?_⟩
    rw [mul_smul, ← h1, smul_smul, inv_mul_cancel₀ hN, one_smul]
  have all : ∀ a : MonoidAlgebra ℂ G, ∃ c : ℂ, idem hπ.1 hc (orbitMap π x₀ a) = c • x₀ := fun a => by
    induction a using MonoidAlgebra.induction_on with
    | of g =>
      have : orbitMap π x₀ (MonoidAlgebra.of ℂ G g) = π g x₀ := by
        show π.asAlgebraHom (MonoidAlgebra.of ℂ G g) x₀ = _
        simp
      rw [this]; exact key g
    | add a b ha hb =>
      obtain ⟨c, hc₁⟩ := ha
      obtain ⟨d, hd⟩ := hb
      have : orbitMap π x₀ (a + b) = orbitMap π x₀ a + orbitMap π x₀ b := map_add _ _ _
      exact ⟨c + d, by rw [this, map_add, hc₁, hd, add_smul]⟩
    | smul r a ha =>
      obtain ⟨c, hc₁⟩ := ha
      have : orbitMap π x₀ (r • a) = r • orbitMap π x₀ a := map_smul _ _ _
      exact ⟨r * c, by rw [this, map_smul, hc₁, smul_smul]⟩
  refine (finrank_eq_one_iff_of_nonzero' (⟨x₀, hx₀⟩ : fixed π K) fun e => h0 (congrArg Subtype.val e)).2 ?_
  rintro ⟨x, hx⟩
  obtain ⟨a, ha⟩ := orbitMap_surjective hπ.2 h0 x
  obtain ⟨c, hc₁⟩ := all a
  refine ⟨c, Subtype.ext ?_⟩
  rw [ha, idem_of_mem hπ.1 hc hx] at hc₁
  exact hc₁.symm

end Abstract

section Gelfand

/- English proof (translation)
The claim follows from `Formalism.UG.P.heckecomm_gelfand K (fun x : H => (⟨θ x, hH _ x.2⟩ : H)) (fun x y => Subtype.ext (hm _ _)) (fun x => Subtype.ext (hi _)) hK hdc f₁ f₂ hf₁ hf₂`.
-/
theorem conv_comm_sub {A : Type} [Group A] (H : Subgroup A) (K : Subgroup H) (θ : A → A)
    (hm : ∀ x y, θ (x * y) = θ y * θ x) (hi : ∀ x, θ (θ x) = x) (hH : ∀ x ∈ H, θ x ∈ H)
    (hK : ∀ x : H, x ∈ K → (⟨θ x, hH _ x.2⟩ : H) ∈ K)
    (hdc : ∀ g : H, ∃ a b : K, (⟨θ g, hH _ g.2⟩ : H) = (a : H) * g * b)
    (f₁ f₂ : H → ℂ) (hf₁ : IsBiInv K f₁) (hf₂ : IsBiInv K f₂) : conv K f₁ f₂ = conv K f₂ f₁ :=
  Formalism.UG.P.heckecomm_gelfand K (fun x : H => (⟨θ x, hH _ x.2⟩ : H)) (fun x y => Subtype.ext (hm _ _))
    (fun x => Subtype.ext (hi _)) hK hdc f₁ f₂ hf₁ hf₂

/- English proof (translation)
Establish `hm' : ∀ x y : H, (⟨θ (x * y : H), hH _ (x * y).2⟩ : H) = ⟨θ y, hH _ y.2⟩ * ⟨θ x, hH _ x.2⟩` using `fun x y => Subtype.ext (hm _ _)`. Establish `ht' : (⟨θ t, hH _ t.2⟩ : H) = t` using `Subtype.ext ht`. Use `⟨⟨_, K.mul_mem (hK _ h₂) (K.inv_mem h₁)⟩, ⟨_, K.mul_mem (K.inv_mem h₂) (hK _ h₁)⟩, ?_⟩` and prove the remaining obligations. Substitute `e` using the available equality. Simplify using `only [hm', ht']`.

Use `group`.
-/
theorem dc_of_decomp {A : Type} [Group A] (H : Subgroup A) (K : Subgroup H) (θ : A → A)
    (hm : ∀ x y, θ (x * y) = θ y * θ x) (hH : ∀ x ∈ H, θ x ∈ H)
    (hK : ∀ x : H, x ∈ K → (⟨θ x, hH _ x.2⟩ : H) ∈ K) {g k₁ k₂ t : H} (h₁ : k₁ ∈ K) (h₂ : k₂ ∈ K)
    (ht : θ t = t) (e : g = k₁ * t * k₂) : ∃ a b : K, (⟨θ g, hH _ g.2⟩ : H) = (a : H) * g * b := by
  have hm' : ∀ x y : H, (⟨θ (x * y : H), hH _ (x * y).2⟩ : H) = ⟨θ y, hH _ y.2⟩ * ⟨θ x, hH _ x.2⟩ :=
    fun x y => Subtype.ext (hm _ _)
  have ht' : (⟨θ t, hH _ t.2⟩ : H) = t := Subtype.ext ht
  refine ⟨⟨_, K.mul_mem (hK _ h₂) (K.inv_mem h₁)⟩, ⟨_, K.mul_mem (K.inv_mem h₂) (hK _ h₁)⟩, ?_⟩
  subst e
  simp only [hm', ht']
  group

end Gelfand

section Transpose

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

/- English proof (translation)
Establish `hJ : antiJ L n * antiJ L n = 1` using `GlobalTheory.UnitarySwap.antiJ_mul_self`. Establish `hJσ : (antiJ L n).map σ = antiJ L n`. Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, antiJ]`. Apply the tactic sequence `split_ifs <;> simp`.

Establish `h0 : cT σ h.val * antiJ L n * h.val = antiJ L n` using `hh`. Establish `hmm : ((h.val.map σ)ᵀ).map σ = h.valᵀ`. Use extensionality with `i j`. Simplify using `[hσ]`. Establish `h1 : h.valᵀ * antiJ L n * h.val.map σ = antiJ L n`.

Use `congrArg (fun M : Matrix (Fin n) (Fin n) L => M.map σ) h0` as an intermediate fact. Simplify using `only [cT, Matrix.map_mul, hJσ, hmm] at this`. Conclude with `this`. Establish `h2 : h.valᵀ * (antiJ L n * h.val.map σ * antiJ L n) = 1`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, hJ]`.

Establish `h3 : (antiJ L n * h.val.map σ * antiJ L n) * h.valᵀ = 1` using `mul_eq_one_comm.1 h2`. Express the relevant statement in the definitionally equal form `cT σ (Formalism.UG.P.heckecomm_tr h).val * antiJ L n * (Formalism.UG.P.heckecomm_tr h).val = antiJ L n`. Establish `hc : cT σ (Formalism.UG.P.heckecomm_tr h).val = h.val.map σ`. Use extensionality with `i j`. Simplify using `[cT, Formalism.UG.P.heckecomm_tr_val]`.

Rewrite using `[hc, Formalism.UG.P.heckecomm_tr_val]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [← Matrix.mul_assoc, hJ, Matrix.one_mul]`. Use `_ = antiJ L n := by rw [h3, Matrix.mul_one]`.
-/
theorem tr_mem_UJ (σ : L →+* L) (hσ : ∀ x, σ (σ x) = x) {h : GL (Fin n) L} (hh : h ∈ UJ σ (antiJ L n)) :
    Formalism.UG.P.heckecomm_tr h ∈ UJ σ (antiJ L n) := by
  have hJ : antiJ L n * antiJ L n = 1 := GlobalTheory.UnitarySwap.antiJ_mul_self
  have hJσ : (antiJ L n).map σ = antiJ L n := by
    ext i j
    simp only [Matrix.map_apply, antiJ]
    split_ifs <;> simp
  have h0 : cT σ h.val * antiJ L n * h.val = antiJ L n := hh
  have hmm : ((h.val.map σ)ᵀ).map σ = h.valᵀ := by
    ext i j
    simp [hσ]
  have h1 : h.valᵀ * antiJ L n * h.val.map σ = antiJ L n := by
    have := congrArg (fun M : Matrix (Fin n) (Fin n) L => M.map σ) h0
    simp only [cT, Matrix.map_mul, hJσ, hmm] at this
    exact this
  have h2 : h.valᵀ * (antiJ L n * h.val.map σ * antiJ L n) = 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, hJ]
  have h3 : (antiJ L n * h.val.map σ * antiJ L n) * h.valᵀ = 1 := mul_eq_one_comm.1 h2
  change cT σ (Formalism.UG.P.heckecomm_tr h).val * antiJ L n * (Formalism.UG.P.heckecomm_tr h).val = antiJ L n
  have hc : cT σ (Formalism.UG.P.heckecomm_tr h).val = h.val.map σ := by
    ext i j
    simp [cT, Formalism.UG.P.heckecomm_tr_val]
  rw [hc, Formalism.UG.P.heckecomm_tr_val]
  calc h.val.map σ * antiJ L n * h.valᵀ
      = antiJ L n * ((antiJ L n * h.val.map σ * antiJ L n) * h.valᵀ) := by
        simp only [← Matrix.mul_assoc, hJ, Matrix.one_mul]
    _ = antiJ L n := by rw [h3, Matrix.mul_one]

def thb (b x : GL (Fin n) L) : GL (Fin n) L := b * Formalism.UG.P.heckecomm_tr (b⁻¹ * x * b) * b⁻¹

/- English proof (translation)
Unfold `thb`. Rewrite using `[show b⁻¹ * (x * y) * b = (b⁻¹ * x * b) * (b⁻¹ * y * b) by group, Formalism.UG.P.heckecomm_tr_mul]`. Use `group`.
-/
theorem thb_mul (b x y : GL (Fin n) L) : thb b (x * y) = thb b y * thb b x := by
  unfold thb
  rw [show b⁻¹ * (x * y) * b = (b⁻¹ * x * b) * (b⁻¹ * y * b) by group, Formalism.UG.P.heckecomm_tr_mul]
  group

/- English proof (translation)
Unfold `thb`. Rewrite using `[show b⁻¹ * (b * Formalism.UG.P.heckecomm_tr (b⁻¹ * x * b) * b⁻¹) * b = Formalism.UG.P.heckecomm_tr (b⁻¹ * x * b) by group, Formalism.UG.P.heckecomm_tr_tr]`. Use `group`.
-/
theorem thb_thb (b x : GL (Fin n) L) : thb b (thb b x) = x := by
  unfold thb
  rw [show b⁻¹ * (b * Formalism.UG.P.heckecomm_tr (b⁻¹ * x * b) * b⁻¹) * b = Formalism.UG.P.heckecomm_tr (b⁻¹ * x * b) by group,
    Formalism.UG.P.heckecomm_tr_tr]
  group

end Transpose

section Local

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Distinguish the cases in `hw : IsSplitAt w`. Establish `h : UL n w = ⊤` using `if_pos hw`. Rewrite using `[h]`. Conclude with `isClosed_univ`. Rewrite using `[GlobalTheory.CompanionTheory.UnitaryWitt.UL_eq_of_not_split hw]`.

Conclude with `GlobalTheory.CompanionTheory.UnitaryWitt.isClosed_UJ_one n (GlobalTheory.T.placeConjugation_properties_cmField E hU w).1`.
-/
theorem isClosed_UL (hU : Unr E) (n : ℕ) (w : Pl E) : IsClosed (UL n w : Set (GLw n w)) := by
  by_cases hw : IsSplitAt w
  · have h : UL n w = ⊤ := if_pos hw
    rw [h]
    exact isClosed_univ
  · rw [GlobalTheory.CompanionTheory.UnitaryWitt.UL_eq_of_not_split hw]
    exact GlobalTheory.CompanionTheory.UnitaryWitt.isClosed_UJ_one n (GlobalTheory.T.placeConjugation_properties_cmField E hU w).1

/- English proof (translation)
Use extensionality with `x`. Conclude with `Subgroup.mem_subgroupOf`.
-/
theorem coe_KL (n : ℕ) (w : Pl E) :
    (KL n w : Set (UL n w)) = Subtype.val ⁻¹' (GlobalTheory.LFun.KGL w n : Set (GLw n w)) := by
  ext x
  exact Subgroup.mem_subgroupOf

/- English proof (translation)
Rewrite using `[coe_KL]`. Conclude with `(GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).1.preimage continuous_subtype_val`.
-/
theorem isOpen_KL (n : ℕ) (w : Pl E) : IsOpen (KL n w : Set (UL n w)) := by
  rw [coe_KL]
  exact (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).1.preimage continuous_subtype_val

/- English proof (translation)
Rewrite using `[coe_KL]`. Conclude with `(isClosed_UL hU n w).isClosedEmbedding_subtypeVal.isCompact_preimage (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).2`.
-/
theorem isCompact_KL (hU : Unr E) (n : ℕ) (w : Pl E) : IsCompact (KL n w : Set (UL n w)) := by
  rw [coe_KL]
  exact (isClosed_UL hU n w).isClosedEmbedding_subtypeVal.isCompact_preimage
    (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).2

/- English proof (translation)
Establish `hT : UL n w = ⊤` using `if_pos hw`. Establish `hmem : ∀ x : GLw n w, x ∈ UL n w` using `fun x => by`. Rewrite using `[hT]`. Discharge the goal by the elementary cases of `trivial`. Use `conv_comm_sub (UL n w) (KL n w) Formalism.UG.P.heckecomm_tr Formalism.UG.P.heckecomm_tr_mul Formalism.UG.P.heckecomm_tr_tr (fun x _ => hmem _) (fun x hx => ?_) (fun g => ?_) f₁ f₂ hf₁ hf₂` and prove the remaining obligations.

Conclude with `Subgroup.mem_subgroupOf.2 (Formalism.UG.P.heckecomm_tr_mem (Ov E w) _ (Subgroup.mem_subgroupOf.1 hx))`. Take `⟨a, b, e⟩` from `Formalism.UG.P.heckecomm_tr_dc Formalism.UG.Final.CartanDecomp E w n g.1`. Conclude with `⟨⟨⟨a.1, hmem _⟩, Subgroup.mem_subgroupOf.2 a.2⟩, ⟨⟨b.1, hmem _⟩, Subgroup.mem_subgroupOf.2 b.2⟩, Subtype.ext e⟩`.
-/
theorem conv_comm_split {n : ℕ} {w : Pl E} (hw : IsSplitAt w) (f₁ f₂ : UL n w → ℂ)
    (hf₁ : IsBiInv (KL n w) f₁) (hf₂ : IsBiInv (KL n w) f₂) : conv (KL n w) f₁ f₂ = conv (KL n w) f₂ f₁ := by
  have hT : UL n w = ⊤ := if_pos hw
  have hmem : ∀ x : GLw n w, x ∈ UL n w := fun x => by
    rw [hT]
    trivial
  refine conv_comm_sub (UL n w) (KL n w) Formalism.UG.P.heckecomm_tr Formalism.UG.P.heckecomm_tr_mul
    Formalism.UG.P.heckecomm_tr_tr (fun x _ => hmem _) (fun x hx => ?_) (fun g => ?_) f₁ f₂ hf₁ hf₂
  · exact Subgroup.mem_subgroupOf.2 (Formalism.UG.P.heckecomm_tr_mem (Ov E w) _ (Subgroup.mem_subgroupOf.1 hx))
  · obtain ⟨a, b, e⟩ := Formalism.UG.P.heckecomm_tr_dc Formalism.UG.Final.CartanDecomp E w n g.1
    exact ⟨⟨⟨a.1, hmem _⟩, Subgroup.mem_subgroupOf.2 a.2⟩, ⟨⟨b.1, hmem _⟩, Subgroup.mem_subgroupOf.2 b.2⟩,
      Subtype.ext e⟩

/- English proof (translation)
Take `⟨-, hcc, -, hns, -⟩` from `GlobalTheory.T.placeConjugation_properties_cmField E hU w`. Take `⟨-, ⟨ϖ, q, hUI, -⟩, -⟩` from `hns hw`. Take `⟨b, hbK, hb⟩` from `GlobalTheory.LFun.InertChart.exists_congr_antiJ (n := n) hUI (B := 1) (one_mem _) (cT_one _)`. Establish `hb' : cT (cj w) b.val * b.val = antiJ _ n` using `by simpa using hb`. Establish `hconj : ∀ g : GLw n w, b * g * b⁻¹ ∈ UL n w ↔ g ∈ UJ (cj w) (antiJ _ n)` using `fun g => by`.

Rewrite using `[GlobalTheory.CompanionTheory.UnitaryWitt.UL_eq_of_not_split hw]`. Conclude with `GlobalTheory.CompanionTheory.UnitaryWitt.conj_mem_UJ_one_iff _ b g hb'`. Establish `hback : ∀ x ∈ UL n w, b⁻¹ * x * b ∈ UJ (cj w) (antiJ _ n)` using `fun x hx => (hconj _).1 (by rwa [show b * (b⁻¹ * x * b) * b⁻¹ = x by group])`. Establish `hH : ∀ x ∈ UL n w, thb b x ∈ UL n w` using `fun x hx => (hconj _).2 (tr_mem_UJ _ hcc (hback x hx))`. Establish `hbi` using `(GlobalTheory.LFun.KGL w n).inv_mem hbK`.

Establish `hK : ∀ x : UL n w, x ∈ KL n w → (⟨thb b x, hH _ x.2⟩ : UL n w) ∈ KL n w` using `fun x hx => Subgroup.mem_subgroupOf.2 (mul_mem (mul_mem hbK (Formalism.UG.P.heckecomm_tr_mem (Ov E w) _ (mul_mem (mul_mem hbi (Subgroup.mem_subgroupOf.1 hx)) hbK))) hbi)`. Establish `hO : Ov E w = intL (w.adicCompletion E)` using `Subring.ext fun _ => Iff.rfl`. Establish `hKU : ∀ k ∈ KU (cj w) n, (k.1 : GLw n w) ∈ GlobalTheory.LFun.KGL w n` using `fun k hk => by`. Establish `h : k.1 ∈ intPts (intL (w.adicCompletion E)).subtype (GU (cj w) n)` using `Subgroup.mem_subgroupOf.1 hk`. Use `show k.1 ∈ (bc (Ov E w).subtype).range`.

Rewrite using `[hO]`. Conclude with `(Subgroup.mem_inf.1 h).2`. Use `conv_comm_sub (UL n w) (KL n w) (thb b) (thb_mul b) (thb_thb b) hH hK (fun g => ?_) f₁ f₂ hf₁ hf₂` and prove the remaining obligations. Take `⟨d, t, ht, k₁, hk₁, k₂, hk₂, e⟩` from `GlobalTheory.ChainOnto.CayleyVac.exists_cartanU hUI ⟨_, hback g.1 g.2⟩`. Establish `e' : b⁻¹ * g.1 * b = k₁.1 * t.1 * k₂.1` using `congrArg Subtype.val e`.

Establish `hk : ∀ k ∈ KU (cj w) n, (⟨b * k.1 * b⁻¹, (hconj _).2 k.2⟩ : UL n w) ∈ KL n w` using `fun k hk => Subgroup.mem_subgroupOf.2 (mul_mem (mul_mem hbK (hKU k hk)) hbi)`. Use `dc_of_decomp (UL n w) (KL n w) (thb b) (thb_mul b) hH hK (hk k₁ hk₁) (hk k₂ hk₂) (t := ⟨b * t.1 * b⁻¹, (hconj _).2 t.2⟩) ?_ (Subtype.ext ?_)` and prove the remaining obligations. Establish `h1 : Formalism.UG.P.heckecomm_tr (t.1 : GLw n w) = t.1` using `Units.ext (by`. Rewrite using `[Formalism.UG.P.heckecomm_tr_val, ht]`. Conclude with `Matrix.diagonal_transpose _)`.

Use `show thb b (b * t.1 * b⁻¹) = b * t.1 * b⁻¹`. Unfold `thb`. Rewrite using `[show b⁻¹ * (b * t.1 * b⁻¹) * b = t.1 by group, h1]`. Use `show g.1 = b * k₁.1 * b⁻¹ * (b * t.1 * b⁻¹) * (b * k₂.1 * b⁻¹)`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[e']`. Use `group`.
-/
theorem conv_comm_inert (hU : Unr E) {n : ℕ} {w : Pl E} (hw : ¬ IsSplitAt w) (f₁ f₂ : UL n w → ℂ)
    (hf₁ : IsBiInv (KL n w) f₁) (hf₂ : IsBiInv (KL n w) f₂) : conv (KL n w) f₁ f₂ = conv (KL n w) f₂ f₁ := by
  obtain ⟨-, hcc, -, hns, -⟩ := GlobalTheory.T.placeConjugation_properties_cmField E hU w
  obtain ⟨-, ⟨ϖ, q, hUI, -⟩, -⟩ := hns hw
  obtain ⟨b, hbK, hb⟩ := GlobalTheory.LFun.InertChart.exists_congr_antiJ (n := n) hUI (B := 1) (one_mem _) (cT_one _)
  have hb' : cT (cj w) b.val * b.val = antiJ _ n := by simpa using hb
  have hconj : ∀ g : GLw n w, b * g * b⁻¹ ∈ UL n w ↔ g ∈ UJ (cj w) (antiJ _ n) := fun g => by
    rw [GlobalTheory.CompanionTheory.UnitaryWitt.UL_eq_of_not_split hw]
    exact GlobalTheory.CompanionTheory.UnitaryWitt.conj_mem_UJ_one_iff _ b g hb'
  have hback : ∀ x ∈ UL n w, b⁻¹ * x * b ∈ UJ (cj w) (antiJ _ n) := fun x hx =>
    (hconj _).1 (by rwa [show b * (b⁻¹ * x * b) * b⁻¹ = x by group])
  have hH : ∀ x ∈ UL n w, thb b x ∈ UL n w := fun x hx =>
    (hconj _).2 (tr_mem_UJ _ hcc (hback x hx))
  have hbi := (GlobalTheory.LFun.KGL w n).inv_mem hbK
  have hK : ∀ x : UL n w, x ∈ KL n w → (⟨thb b x, hH _ x.2⟩ : UL n w) ∈ KL n w := fun x hx =>
    Subgroup.mem_subgroupOf.2 (mul_mem (mul_mem hbK (Formalism.UG.P.heckecomm_tr_mem (Ov E w) _
      (mul_mem (mul_mem hbi (Subgroup.mem_subgroupOf.1 hx)) hbK))) hbi)
  have hO : Ov E w = intL (w.adicCompletion E) := Subring.ext fun _ => Iff.rfl
  have hKU : ∀ k ∈ KU (cj w) n, (k.1 : GLw n w) ∈ GlobalTheory.LFun.KGL w n := fun k hk => by
    have h : k.1 ∈ intPts (intL (w.adicCompletion E)).subtype (GU (cj w) n) := Subgroup.mem_subgroupOf.1 hk
    show k.1 ∈ (bc (Ov E w).subtype).range
    rw [hO]
    exact (Subgroup.mem_inf.1 h).2
  refine conv_comm_sub (UL n w) (KL n w) (thb b) (thb_mul b) (thb_thb b) hH hK (fun g => ?_) f₁ f₂ hf₁ hf₂
  obtain ⟨d, t, ht, k₁, hk₁, k₂, hk₂, e⟩ := GlobalTheory.ChainOnto.CayleyVac.exists_cartanU hUI ⟨_, hback g.1 g.2⟩
  have e' : b⁻¹ * g.1 * b = k₁.1 * t.1 * k₂.1 := congrArg Subtype.val e
  have hk : ∀ k ∈ KU (cj w) n, (⟨b * k.1 * b⁻¹, (hconj _).2 k.2⟩ : UL n w) ∈ KL n w := fun k hk =>
    Subgroup.mem_subgroupOf.2 (mul_mem (mul_mem hbK (hKU k hk)) hbi)
  refine dc_of_decomp (UL n w) (KL n w) (thb b) (thb_mul b) hH hK (hk k₁ hk₁) (hk k₂ hk₂)
    (t := ⟨b * t.1 * b⁻¹, (hconj _).2 t.2⟩) ?_ (Subtype.ext ?_)
  · have h1 : Formalism.UG.P.heckecomm_tr (t.1 : GLw n w) = t.1 := Units.ext (by
      rw [Formalism.UG.P.heckecomm_tr_val, ht]
      exact Matrix.diagonal_transpose _)
    show thb b (b * t.1 * b⁻¹) = b * t.1 * b⁻¹
    unfold thb
    rw [show b⁻¹ * (b * t.1 * b⁻¹) * b = t.1 by group, h1]
  · show g.1 = b * k₁.1 * b⁻¹ * (b * t.1 * b⁻¹) * (b * k₂.1 * b⁻¹)
    calc g.1 = b * (b⁻¹ * g.1 * b) * b⁻¹ := by group
      _ = _ := by
        rw [e']
        group

/- English proof (translation)
Introduce `E _ _ _ hU n w σ hne hfd`. Establish `hcomm : ∀ f₁ ∈ Hecke ℂ (KL n w), ∀ f₂ ∈ Hecke ℂ (KL n w), conv (KL n w) f₁ f₂ = conv (KL n w) f₂ f₁` using `fun f₁ h₁ f₂ h₂ => by`. Distinguish the cases in `hw : IsSplitAt w`. Conclude with `conv_comm_split hw f₁ f₂ h₁.1 h₂.1`. Conclude with `conv_comm_inert hU hw f₁ f₂ h₁.1 h₂.1`.

Conclude with `finrank_fixed_eq_one σ.ρ (KL n w) (isCompact_KL hU n w) (PI.UnitaryGroupMassFormula.AdIndexEq.commensurated_of_isOpen_isCompact _ (isOpen_KL n w) (isCompact_KL hU n w)) hcomm ⟨σ.smooth, σ.irred⟩ hfd hne`.
-/
theorem sphOne : SphOne := by
  intro E _ _ _ hU n w σ hne hfd
  have hcomm : ∀ f₁ ∈ Hecke ℂ (KL n w), ∀ f₂ ∈ Hecke ℂ (KL n w),
      conv (KL n w) f₁ f₂ = conv (KL n w) f₂ f₁ := fun f₁ h₁ f₂ h₂ => by
    by_cases hw : IsSplitAt w
    · exact conv_comm_split hw f₁ f₂ h₁.1 h₂.1
    · exact conv_comm_inert hU hw f₁ f₂ h₁.1 h₂.1
  exact finrank_fixed_eq_one σ.ρ (KL n w) (isCompact_KL hU n w)
    (PI.UnitaryGroupMassFormula.AdIndexEq.commensurated_of_isOpen_isCompact _ (isOpen_KL n w) (isCompact_KL hU n w)) hcomm
    ⟨σ.smooth, σ.irred⟩ hfd hne

/- English proof (translation)
Introduce `_` and use `sphOne`.
-/
theorem locAlg_sphOne : LocAlg → SphOne := fun _ => sphOne

end Local

end GlobalTheory.CompanionTheory.SphLine
