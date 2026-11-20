import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralLeviConstantTermStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralTwistedConjInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralProductGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableTwistedOrbitalIntegralIntegralNormCongruen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjGLOfCharpolyEqOfSeparable
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.SplitCtMatch

/- English proof (translation)
Introduce `k _ a x y h hs` and use `GlobalTheory.SepConj.conj_of_charpoly_eq_of_separable k a x y h hs`.
-/
theorem conjOfCharpoly : ∀ (k : Type) [Field k] (a : ℕ) (x y : GL (Fin a) k), x.val.charpoly = y.val.charpoly →
    x.val.charpoly.Separable → ∃ g : GL (Fin a) k, y = g⁻¹ * x * g :=
  fun k _ a x y h hs => GlobalTheory.SepConj.conj_of_charpoly_eq_of_separable k a x y h hs

/- English proof (translation)
Introduce `k _ a Q hm hn h0`. Choose the witnesses or unpack the hypotheses as in `⟨N, hN⟩ : ∃ N : Matrix (Fin a) (Fin a) k, N.charpoly = Q := by`. Substitute `hn` using the available equality. Conclude with `⟨_, (charpoly_leftMulMatrix (AdjoinRoot.powerBasis hm.ne_zero)).trans (AdjoinRoot.minpoly_powerBasis_gen_of_monic hm)⟩`. Establish `hd : IsUnit N.det`.

Rewrite using `[Matrix.det_eq_sign_charpoly_coeff, hN]`. Conclude with `isUnit_iff_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) h0)`. Conclude with `⟨((Matrix.isUnit_iff_isUnit_det N).mpr hd).unit, hN⟩`.
-/
theorem existsOfCharpoly : ∀ (k : Type) [Field k] (a : ℕ) (Q : k[X]), Q.Monic → Q.natDegree = a → Q.coeff 0 ≠ 0 →
    ∃ x : GL (Fin a) k, x.val.charpoly = Q := by
  intro k _ a Q hm hn h0
  obtain ⟨N, hN⟩ : ∃ N : Matrix (Fin a) (Fin a) k, N.charpoly = Q := by
    subst hn
    exact ⟨_, (charpoly_leftMulMatrix (AdjoinRoot.powerBasis hm.ne_zero)).trans
      (AdjoinRoot.minpoly_powerBasis_gen_of_monic hm)⟩
  have hd : IsUnit N.det := by
    rw [Matrix.det_eq_sign_charpoly_coeff, hN]
    exact isUnit_iff_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) h0)
  exact ⟨((Matrix.isUnit_iff_isUnit_det N).mpr hd).unit, hN⟩

/- English proof (translation)
Introduce `G _ _ _ θ K δ g f`. Rewrite using `[GlobalTheory.TwOrbConj.twOrb_eq, GlobalTheory.TwOrbConj.twOrb_eq]`. Combine the equalities or inequalities in the displayed calculation. Use `finsum_congr fun q => ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.TwOrbConj.summand_twist]`.

Take `⟨t, ht, k, hk, he⟩` from `(DoubleCoset.eq _ _ _ _).1 (DoubleCoset.out_eq' (twCent θ δ) K (DoubleCoset.mk _ K (g * Quotient.out q))).symm`. Use `show _ = GlobalTheory.TwOrbConj.summand θ K δ f (Quotient.out (DoubleCoset.mk (twCent θ δ) K (g * Quotient.out q)))`. Rewrite using `[he, GlobalTheory.TwOrbConj.summand_rep θ K δ f _ ht hk]`. Use `_ = ∑ᶠ q, GlobalTheory.TwOrbConj.summand θ K δ f (Quotient.out q) := finsum_comp_equiv (f := fun q : DoubleCoset.Quotient (twCent θ δ : Set G) (K : Set G) => GlobalTheory.TwOrbConj.summand θ K δ f (Quotient.out q)) (GlobalTheory.TwOrbConj.dcEquiv θ K δ g)`.
-/
theorem twOrb_twConj : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (θ : G →* G) (K : Subgroup G)
    (δ g : G) (f : G → ℂ), twOrb θ K (g⁻¹ * δ * θ g) f = twOrb θ K δ f := by
  intro G _ _ _ θ K δ g f
  rw [GlobalTheory.TwOrbConj.twOrb_eq, GlobalTheory.TwOrbConj.twOrb_eq]
  calc ∑ᶠ q, GlobalTheory.TwOrbConj.summand θ K (g⁻¹ * δ * θ g) f (Quotient.out q)
      = ∑ᶠ q, GlobalTheory.TwOrbConj.summand θ K δ f (Quotient.out (GlobalTheory.TwOrbConj.dcEquiv θ K δ g q)) := by
        refine finsum_congr fun q => ?_
        rw [GlobalTheory.TwOrbConj.summand_twist]
        obtain ⟨t, ht, k, hk, he⟩ := (DoubleCoset.eq _ _ _ _).1
          (DoubleCoset.out_eq' (twCent θ δ) K (DoubleCoset.mk _ K (g * Quotient.out q))).symm
        show _ = GlobalTheory.TwOrbConj.summand θ K δ f (Quotient.out (DoubleCoset.mk (twCent θ δ) K (g * Quotient.out q)))
        rw [he, GlobalTheory.TwOrbConj.summand_rep θ K δ f _ ht hk]
    _ = ∑ᶠ q, GlobalTheory.TwOrbConj.summand θ K δ f (Quotient.out q) :=
        finsum_comp_equiv (f := fun q : DoubleCoset.Quotient (twCent θ δ : Set G) (K : Set G) =>
          GlobalTheory.TwOrbConj.summand θ K δ f (Quotient.out q)) (GlobalTheory.TwOrbConj.dcEquiv θ K δ g)

/- English proof (translation)
Introduce `G _ _ θ K δ f c hc`. Rewrite using `[← GlobalTheory.BCT.StTwLevel.twOrb_const_mul]`. Unfold `twOrb`. Use `finsum_congr fun q => ?_` and prove the remaining obligations. Use `congr 2`.

Use function extensionality and compare the values at `k`. Conclude with `congrArg (fun z => z * f _) (hc _)`.
-/
theorem twOrb_mulConst : ∀ {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (δ : G) (f c : G → ℂ),
    (∀ x, c (x⁻¹ * δ * θ x) = c δ) → twOrb θ K δ (fun y => c y * f y) = c δ * twOrb θ K δ f := by
  intro G _ _ θ K δ f c hc
  rw [← GlobalTheory.BCT.StTwLevel.twOrb_const_mul]
  unfold twOrb
  refine finsum_congr fun q => ?_
  congr 2
  funext k
  exact congrArg (fun z => z * f _) (hc _)

/- English proof (translation)
Introduce `G _ _ θ K S wt f δ _ hS hS' hwt horb`. Establish `heqv : Equivalence (fun x y : G => ∃ g, y = g⁻¹ * x * θ g)`. Use `⟨fun x => ⟨1, by simp⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `x y ⟨g, rfl⟩`. Conclude with `⟨g⁻¹, by simp [mul_assoc]⟩`.

Introduce and unpack `x y z ⟨g, rfl⟩ ⟨h, rfl⟩`. Conclude with `⟨g * h, by simp [mul_assoc]⟩`. Take `⟨c₀, hc₀⟩ : ∃ c₀ : TwCl θ, c₀ = Quot.mk _ δ` from `⟨_, rfl⟩`. Unfold `clSum`. Rewrite using `[finsum_eq_single _ c₀]`.

Choose the witnesses or unpack the hypotheses as in `⟨g, hg⟩ : ∃ g, c₀.rep = g⁻¹ * δ * θ g := by`. Establish `h1 : (Quot.mk _ c₀.rep : TwCl θ) = Quot.mk _ δ` using `(Quot.out_eq c₀).trans hc₀`. Conclude with `heqv.eqvGen_iff.mp (Quot.eqvGen_exact h1.symm)`. Rewrite using `[hg, if_pos (hS' g), hwt, horb]`. Introduce `c hc`.

Rewrite using `[if_neg]`. Introduce `hmem`. Apply `hc` to reduce the goal to its premises. Take `⟨g, hg⟩` from `hS _ hmem`. Rewrite using `[hc₀]`.

Conclude with `(Quot.out_eq c).symm.trans (Quot.sound ⟨g, hg⟩).symm`.
-/
theorem clSum_oneClass : ∀ {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (S : Set G)
    (wt f : G → ℂ) (δ : G), δ ∈ S → (∀ y ∈ S, ∃ g, y = g⁻¹ * δ * θ g) → (∀ g, g⁻¹ * δ * θ g ∈ S) →
    (∀ g, wt (g⁻¹ * δ * θ g) = wt δ) → (∀ g, twOrb θ K (g⁻¹ * δ * θ g) f = twOrb θ K δ f) →
    clSum θ K S wt f = wt δ * twOrb θ K δ f := by
  intro G _ _ θ K S wt f δ _ hS hS' hwt horb
  have heqv : Equivalence (fun x y : G => ∃ g, y = g⁻¹ * x * θ g) := by
    refine ⟨fun x => ⟨1, by simp⟩, ?_, ?_⟩
    · rintro x y ⟨g, rfl⟩
      exact ⟨g⁻¹, by simp [mul_assoc]⟩
    · rintro x y z ⟨g, rfl⟩ ⟨h, rfl⟩
      exact ⟨g * h, by simp [mul_assoc]⟩
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : TwCl θ, c₀ = Quot.mk _ δ := ⟨_, rfl⟩
  unfold clSum
  rw [finsum_eq_single _ c₀]
  · obtain ⟨g, hg⟩ : ∃ g, c₀.rep = g⁻¹ * δ * θ g := by
      have h1 : (Quot.mk _ c₀.rep : TwCl θ) = Quot.mk _ δ := (Quot.out_eq c₀).trans hc₀
      exact heqv.eqvGen_iff.mp (Quot.eqvGen_exact h1.symm)
    rw [hg, if_pos (hS' g), hwt, horb]
  · intro c hc
    rw [if_neg]
    intro hmem
    apply hc
    obtain ⟨g, hg⟩ := hS _ hmem
    rw [hc₀]
    exact (Quot.out_eq c).symm.trans (Quot.sound ⟨g, hg⟩).symm

end GlobalTheory.BCT.SplitCtMatch

namespace GlobalTheory.BCT.SplitCtMatch

section Transport

open GlobalTheory.TwOrbConj

variable {G H : Type} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]

/- English proof (translation)
Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce `hy`. Use `⟨e.symm y, (h _).2 (by simpa using hy), by simp⟩` and prove the remaining obligations. Introduce and unpack `⟨g, hg, rfl⟩`.

Conclude with `(h g).1 hg`.
-/
theorem map_eq_of_mem' (e : G ≃ₜ* H) (A : Subgroup G) (A' : Subgroup H) (h : ∀ g, g ∈ A ↔ e g ∈ A') :
    A' = A.map (e : G →* H) := by
  ext y
  constructor
  · intro hy
    refine ⟨e.symm y, (h _).2 (by simpa using hy), by simp⟩
  · rintro ⟨g, hg, rfl⟩
    exact (h g).1 hg

/- English proof (translation)
Unfold `cptPart`. Rewrite using `[MonoidHom.map_closure]`. Use `congr 1`. Establish `hz : ∀ t, (Subgroup.zpowers ((e : G →* H) t) : Set H) = e.toHomeomorph '' (Subgroup.zpowers t : Set G)`. Introduce `t`.

Rewrite using `[← MonoidHom.map_zpowers, Subgroup.coe_map]`. Both sides reduce to the same expression. Establish `hk : ∀ t, IsCompact (closure (Subgroup.zpowers ((e : G →* H) t) : Set H)) ↔ IsCompact (closure (Subgroup.zpowers t : Set G))`. Introduce `t`. Rewrite using `[hz, ← Homeomorph.image_closure, Homeomorph.isCompact_image]`.

Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨t, ht, rfl⟩, hc⟩`. Conclude with `⟨t, ⟨ht, (hk t).1 hc⟩, rfl⟩`. Introduce and unpack `⟨t, ⟨ht, hc⟩, rfl⟩`.

Conclude with `⟨⟨t, ht, rfl⟩, (hk t).2 hc⟩`.
-/
theorem cptPart_map_equiv' (e : G ≃ₜ* H) (T : Subgroup G) :
    cptPart (T.map (e : G →* H)) = (cptPart T).map (e : G →* H) := by
  unfold cptPart
  rw [MonoidHom.map_closure]
  congr 1
  have hz : ∀ t, (Subgroup.zpowers ((e : G →* H) t) : Set H) = e.toHomeomorph '' (Subgroup.zpowers t : Set G) := by
    intro t
    rw [← MonoidHom.map_zpowers, Subgroup.coe_map]
    rfl
  have hk : ∀ t, IsCompact (closure (Subgroup.zpowers ((e : G →* H) t) : Set H)) ↔
      IsCompact (closure (Subgroup.zpowers t : Set G)) := by
    intro t
    rw [hz, ← Homeomorph.image_closure, Homeomorph.isCompact_image]
  ext x
  constructor
  · rintro ⟨⟨t, ht, rfl⟩, hc⟩
    exact ⟨t, ⟨ht, (hk t).1 hc⟩, rfl⟩
  · rintro ⟨t, ⟨ht, hc⟩, rfl⟩
    exact ⟨⟨t, ht, rfl⟩, (hk t).2 hc⟩

/- English proof (translation)
Rewrite using `[mem_twCent, mem_twCent, ← he, ← map_mul, ← map_mul]`. Conclude with `e.injective.eq_iff.symm`.
-/
theorem twCent_mem' (e : G ≃ₜ* H) (θ : G →* G) (θ' : H →* H) (he : ∀ g, e (θ g) = θ' (e g)) (δ g : G) :
    g ∈ twCent θ δ ↔ e g ∈ twCent θ' (e δ) := by
  rw [mem_twCent, mem_twCent, ← he, ← map_mul, ← map_mul]
  exact e.injective.eq_iff.symm

/- English proof (translation)
Establish `hT : twCent θ' (e δ) = (twCent θ δ).map (e : G →* H)` using `map_eq_of_mem' e _ _ (twCent_mem' e θ θ' he δ)`. Establish `hK' : K' = K.map (e : G →* H)` using `map_eq_of_mem' e _ _ hK`. Substitute `hK'` using the available equality. Unfold `summand`. Use `congr 1`.

Establish `h1 : (K.map (e : G →* H)).map (MulAut.conj (e y)).toMonoidHom = (K.map (MulAut.conj y).toMonoidHom).map (e : G →* H)`. Rewrite using `[Subgroup.map_map, Subgroup.map_map]`. Use `congr 1`. Use extensionality with `x`. Simplify using `[MulAut.conj_apply]`.

Rewrite using `[h1, hT, ← Subgroup.map_inf_eq _ _ _ e.injective, cptPart_map_equiv', Subgroup.relIndex_map_map_of_injective _ _ e.injective]`. Set `ψ : K ≃* (K.map (e : G →* H))` to `e.toMulEquiv.subgroupMap K`. Rewrite using `[← GlobalTheory.BCT.OrbProd.avg_comp_equiv ψ]`. Use `congr 1`. Use function extensionality and compare the values at `k`.

Simplify using `only [Function.comp_apply]`. Rewrite using `[← hf]`. Use `congr 1`. Use `show (e y * e k.1)⁻¹ * e δ * θ' (e y * e k.1) = _`. Rewrite using `[← map_mul, ← he, ← map_inv, ← map_mul, ← map_mul]`.
-/
theorem summand_map' (e : G ≃ₜ* H) (θ : G →* G) (θ' : H →* H) (K : Subgroup G) (K' : Subgroup H) (δ : G)
    (f : G → ℂ) (f' : H → ℂ) (he : ∀ g, e (θ g) = θ' (e g)) (hK : ∀ g, g ∈ K ↔ e g ∈ K')
    (hf : ∀ g, f' (e g) = f g) (y : G) :
    summand θ' K' (e δ) f' (e y) = summand θ K δ f y := by
  have hT : twCent θ' (e δ) = (twCent θ δ).map (e : G →* H) :=
    map_eq_of_mem' e _ _ (twCent_mem' e θ θ' he δ)
  have hK' : K' = K.map (e : G →* H) := map_eq_of_mem' e _ _ hK
  subst hK'
  unfold summand
  congr 1
  · have h1 : (K.map (e : G →* H)).map (MulAut.conj (e y)).toMonoidHom =
        (K.map (MulAut.conj y).toMonoidHom).map (e : G →* H) := by
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext x
      simp [MulAut.conj_apply]
    rw [h1, hT, ← Subgroup.map_inf_eq _ _ _ e.injective, cptPart_map_equiv',
      Subgroup.relIndex_map_map_of_injective _ _ e.injective]
  · let ψ : K ≃* (K.map (e : G →* H)) := e.toMulEquiv.subgroupMap K
    rw [← GlobalTheory.BCT.OrbProd.avg_comp_equiv ψ]
    congr 1
    funext k
    simp only [Function.comp_apply]
    rw [← hf]
    congr 1
    show (e y * e k.1)⁻¹ * e δ * θ' (e y * e k.1) = _
    rw [← map_mul, ← he, ← map_inv, ← map_mul, ← map_mul]

def dcMap' (e : G ≃ₜ* H) (T K : Subgroup G) (T' K' : Subgroup H) :
    DoubleCoset.Quotient (T : Set G) (K : Set G) → DoubleCoset.Quotient (T' : Set H) (K' : Set H) :=
  fun q => DoubleCoset.mk T' K' (e (Quotient.out q))

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `q1 q2 h`. Take `⟨a, ha, b, hb, hab⟩` from `(DoubleCoset.eq _ _ _ _).1 h`. Rewrite using `[← DoubleCoset.out_eq' T K q1, ← DoubleCoset.out_eq' T K q2, DoubleCoset.eq]`. Use `⟨e.symm a, (hT _).2 (by simpa using ha), e.symm b, (hK _).2 (by simpa using hb), ?_⟩` and prove the remaining obligations.

Apply `e.injective` to reduce the goal to its premises. Simplify using `only [map_mul, ContinuousMulEquiv.apply_symm_apply]`. Conclude with `hab`. Introduce `q'`. Use `⟨DoubleCoset.mk T K (e.symm (Quotient.out q')), ?_⟩` and prove the remaining obligations.

Take `⟨a, b, ha, hb, hab⟩` from `DoubleCoset.mk_out_eq_mul T K (e.symm (Quotient.out q'))`. Unfold `dcMap'`. Rewrite using `[hab]`. Use `conv_rhs => rw [← DoubleCoset.out_eq' T' K' q']`. Rewrite using `[DoubleCoset.eq]`.

Use `⟨(e a)⁻¹, T'.inv_mem ((hT a).1 ha), (e b)⁻¹, K'.inv_mem ((hK b).1 hb), ?_⟩` and prove the remaining obligations. Simplify using `only [map_mul, ContinuousMulEquiv.apply_symm_apply]`. Use `group`.
-/
theorem dcMap_bij' (e : G ≃ₜ* H) (T K : Subgroup G) (T' K' : Subgroup H) (hT : ∀ g, g ∈ T ↔ e g ∈ T')
    (hK : ∀ g, g ∈ K ↔ e g ∈ K') : Function.Bijective (dcMap' e T K T' K') := by
  constructor
  · intro q1 q2 h
    obtain ⟨a, ha, b, hb, hab⟩ := (DoubleCoset.eq _ _ _ _).1 h
    rw [← DoubleCoset.out_eq' T K q1, ← DoubleCoset.out_eq' T K q2, DoubleCoset.eq]
    refine ⟨e.symm a, (hT _).2 (by simpa using ha), e.symm b, (hK _).2 (by simpa using hb), ?_⟩
    apply e.injective
    simp only [map_mul, ContinuousMulEquiv.apply_symm_apply]
    exact hab
  · intro q'
    refine ⟨DoubleCoset.mk T K (e.symm (Quotient.out q')), ?_⟩
    obtain ⟨a, b, ha, hb, hab⟩ := DoubleCoset.mk_out_eq_mul T K (e.symm (Quotient.out q'))
    unfold dcMap'
    rw [hab]
    conv_rhs => rw [← DoubleCoset.out_eq' T' K' q']
    rw [DoubleCoset.eq]
    refine ⟨(e a)⁻¹, T'.inv_mem ((hT a).1 ha), (e b)⁻¹, K'.inv_mem ((hK b).1 hb), ?_⟩
    simp only [map_mul, ContinuousMulEquiv.apply_symm_apply]
    group

/- English proof (translation)
Establish `hT` using `twCent_mem' e θ θ' he δ`. Rewrite using `[twOrb_eq, twOrb_eq, ← finsum_comp_equiv (Equiv.ofBijective _ (dcMap_bij' e (twCent θ δ) K (twCent θ' (e δ)) K' hT hK))]`. Use `finsum_congr fun q => ?_` and prove the remaining obligations. Take `⟨a, b, ha, hb, hab⟩` from `DoubleCoset.mk_out_eq_mul (twCent θ' (e δ)) K' (e (Quotient.out q))`. Establish `e2 : Quotient.out (Equiv.ofBijective _ (dcMap_bij' e (twCent θ δ) K (twCent θ' (e δ)) K' hT hK) q) = a * e (Quotient.out q) * b` using `hab`.

Rewrite using `[e2, summand_rep θ' K' (e δ) f' _ ha hb, summand_map' e θ θ' K K' δ f f' he hK hf]`.
-/
theorem twOrb_transport' [IsTopologicalGroup G] [IsTopologicalGroup H] (e : G ≃ₜ* H) (θ : G →* G) (θ' : H →* H)
    (K : Subgroup G) (K' : Subgroup H) (δ : G) (f : G → ℂ) (f' : H → ℂ) (he : ∀ g, e (θ g) = θ' (e g))
    (hK : ∀ g, g ∈ K ↔ e g ∈ K') (hf : ∀ g, f' (e g) = f g) : twOrb θ K δ f = twOrb θ' K' (e δ) f' := by
  have hT := twCent_mem' e θ θ' he δ
  rw [twOrb_eq, twOrb_eq,
    ← finsum_comp_equiv (Equiv.ofBijective _ (dcMap_bij' e (twCent θ δ) K (twCent θ' (e δ)) K' hT hK))]
  refine finsum_congr fun q => ?_
  obtain ⟨a, b, ha, hb, hab⟩ := DoubleCoset.mk_out_eq_mul (twCent θ' (e δ)) K' (e (Quotient.out q))
  have e2 : Quotient.out (Equiv.ofBijective _ (dcMap_bij' e (twCent θ δ) K (twCent θ' (e δ)) K' hT hK) q) =
      a * e (Quotient.out q) * b := hab
  rw [e2, summand_rep θ' K' (e δ) f' _ ha hb, summand_map' e θ θ' K K' δ f f' he hK hf]

end Transport

def topEquivC {G : Type} [Group G] [TopologicalSpace G] (H : Subgroup G) (hH : H = ⊤) : H ≃ₜ* G where
  toMulEquiv := (MulEquiv.subgroupCongr hH).trans Subgroup.topEquiv
  continuous_toFun := continuous_subtype_val
  continuous_invFun := Continuous.subtype_mk continuous_id _

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem topEquivC_apply {G : Type} [Group G] [TopologicalSpace G] (H : Subgroup G) (hH : H = ⊤) (x : H) :
    topEquivC H hH x = (x : G) := rfl

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[toSub, dif_pos x.2]`.
-/
theorem toSub_top {G : Type} [Group G] (H : Subgroup G) (hH : H = ⊤) (x : H) : toSub H (x : G) = x := by
  apply Subtype.ext
  rw [toSub, dif_pos x.2]

/- English proof (translation)
Introduce `G _ _ _ H hH K δ f`. Use `twOrb_transport' (topEquivC H hH) _ _ K _ δ f _ (fun g => rfl) (fun g => ?_) (fun g => ?_)` and prove the remaining obligations. Rewrite using `[topEquivC_apply]`. Conclude with `(Subgroup.mem_map_iff_mem H.subtype_injective).symm`. Use `show f (toSub H (g : G)) = f g`.

Rewrite using `[toSub_top H hH]`.
-/
theorem twOrb_top : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H : Subgroup G), H = ⊤ →
    ∀ (K : Subgroup H) (δ : H) (f : H → ℂ),
    twOrb (MonoidHom.id H) K δ f = twOrb (MonoidHom.id G) (K.map H.subtype) (δ : G) (fun y => f (toSub H y)) := by
  intro G _ _ _ H hH K δ f
  refine twOrb_transport' (topEquivC H hH) _ _ K _ δ f _ (fun g => rfl) (fun g => ?_) (fun g => ?_)
  · rw [topEquivC_apply]
    exact (Subgroup.mem_map_iff_mem H.subtype_injective).symm
  · show f (toSub H (g : G)) = f g
    rw [toSub_top H hH]

/- English proof (translation)
Introduce `G _ _ _ H hH K' f hK' hf`. Set `e` to `topEquivC H hH`. Establish `hall : ∀ g : G, g ∈ H` using `fun g => hH ▸ Subgroup.mem_top g`. Establish `hfe : (fun y => f (toSub H y)) = f ∘ e.toHomeomorph.symm`. Use function extensionality and compare the values at `y`.

Simplify using `only [Function.comp_apply]`. Use `congr 1`. Apply `e.injective` to reduce the goal to its premises. Use `show ((toSub H y : H) : G) = e (e.symm y)`. Rewrite using `[ContinuousMulEquiv.apply_symm_apply, toSub, dif_pos (hall _)]`.

Establish `hmap : ((K'.map H.subtype : Subgroup G) : Set G) = e.toHomeomorph '' (K' : Set H)`. Rewrite using `[Subgroup.coe_map]`. Both sides reduce to the same expression. Establish `hmul : ∀ (k : H) (y : G), toSub H ((k : G) * y) = k * toSub H y`. Introduce `k y`.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[Subgroup.coe_mul, toSub, toSub, dif_pos (hall _), dif_pos (hall _)]`. Establish `hmul' : ∀ (k : H) (y : G), toSub H (y * (k : G)) = toSub H y * k`. Introduce `k y`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[Subgroup.coe_mul, toSub, toSub, dif_pos (hall _), dif_pos (hall _)]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hmap]`. Conclude with `e.toHomeomorph.isOpenMap _ hK'`. Rewrite using `[hfe]`.

Conclude with `hf.1.comp_homeomorph _`. Introduce and unpack `k ⟨k', hk', rfl⟩ x`. Simplify using `only [Subgroup.coe_subtype]`. Rewrite using `[hmul, hmul']`. Conclude with `⟨(hf.2 k' hk' _).1, (hf.2 k' hk' _).2⟩`.
-/
theorem isHecke_top : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H : Subgroup G), H = ⊤ →
    ∀ (K' : Subgroup H) (f : H → ℂ), IsOpen (K' : Set H) → IsHecke K' f →
    IsOpen (K'.map H.subtype : Set G) ∧ IsHecke (K'.map H.subtype) (fun y => f (toSub H y)) := by
  intro G _ _ _ H hH K' f hK' hf
  let e := topEquivC H hH
  have hall : ∀ g : G, g ∈ H := fun g => hH ▸ Subgroup.mem_top g
  have hfe : (fun y => f (toSub H y)) = f ∘ e.toHomeomorph.symm := by
    funext y
    simp only [Function.comp_apply]
    congr 1
    apply e.injective
    show ((toSub H y : H) : G) = e (e.symm y)
    rw [ContinuousMulEquiv.apply_symm_apply, toSub, dif_pos (hall _)]
  have hmap : ((K'.map H.subtype : Subgroup G) : Set G) = e.toHomeomorph '' (K' : Set H) := by
    rw [Subgroup.coe_map]
    rfl
  have hmul : ∀ (k : H) (y : G), toSub H ((k : G) * y) = k * toSub H y := by
    intro k y
    apply Subtype.ext
    rw [Subgroup.coe_mul, toSub, toSub, dif_pos (hall _), dif_pos (hall _)]
  have hmul' : ∀ (k : H) (y : G), toSub H (y * (k : G)) = toSub H y * k := by
    intro k y
    apply Subtype.ext
    rw [Subgroup.coe_mul, toSub, toSub, dif_pos (hall _), dif_pos (hall _)]
  refine ⟨?_, ?_, ?_⟩
  · rw [hmap]
    exact e.toHomeomorph.isOpenMap _ hK'
  · rw [hfe]
    exact hf.1.comp_homeomorph _
  · rintro k ⟨k', hk', rfl⟩ x
    simp only [Subgroup.coe_subtype]
    rw [hmul, hmul']
    exact ⟨(hf.2 k' hk' _).1, (hf.2 k' hk' _).2⟩

end GlobalTheory.BCT.SplitCtMatch

namespace GlobalTheory.BCT.SplitCtMatch

/- English proof (translation)
Establish `hU : IsUnit (Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h)) (Matrix.fromBlocks m.1.val (m.1.val * (0 : Matrix (Fin a) (Fin b) (w.adicCompletion E))) 0 m.2.val))`. Rewrite using `[Matrix.isUnit_iff_isUnit_det, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]`. Conclude with `((Matrix.isUnit_iff_isUnit_det _).mp m.1.isUnit).mul ((Matrix.isUnit_iff_isUnit_det _).mp m.2.isUnit)`. Unfold `blk`. Simplify using `only []`.

Rewrite using `[dif_pos hU, IsUnit.unit_spec, Matrix.charpoly_reindex, Matrix.mul_zero, Matrix.charpoly_fromBlocks_zero₁₂]`.
-/
theorem blk_zero_charpoly (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E)
    (m : GLw a w × GLw b w) : (blk h w m 0).val.charpoly = m.1.val.charpoly * m.2.val.charpoly := by
  have hU : IsUnit (Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
      (Matrix.fromBlocks m.1.val (m.1.val * (0 : Matrix (Fin a) (Fin b) (w.adicCompletion E))) 0 m.2.val)) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp m.1.isUnit).mul ((Matrix.isUnit_iff_isUnit_det _).mp m.2.isUnit)
  unfold blk
  simp only []
  rw [dif_pos hU, IsUnit.unit_spec, Matrix.charpoly_reindex, Matrix.mul_zero, Matrix.charpoly_fromBlocks_zero₁₂]

/- English proof (translation)
Rewrite using `[Matrix.det_eq_sign_charpoly_coeff, h, Fintype.card_fin]`.
-/
theorem det_of_charpoly {k : Type} [Field k] {a : ℕ} (x : GL (Fin a) k) {Q : k[X]} (h : x.val.charpoly = Q) :
    x.val.det = (-1) ^ a * Q.coeff 0 := by
  rw [Matrix.det_eq_sign_charpoly_coeff, h, Fintype.card_fin]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem prodMap_id_id {A B : Type} [Group A] [Group B] :
    (MonoidHom.id A).prodMap (MonoidHom.id B) = MonoidHom.id (A × B) := rfl

end GlobalTheory.BCT.SplitCtMatch

namespace GlobalTheory.BCT.SplitCtMatch

/- English proof (translation)
Rewrite using `[Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj']`.
-/
theorem charpoly_conj' {k : Type} [Field k] {a : ℕ} (g x : GL (Fin a) k) :
    (g⁻¹ * x * g).val.charpoly = x.val.charpoly := by
  rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj']

/- English proof (translation)
Rewrite using `[toSub, dif_pos h]`.
-/
theorem toSub_val {G : Type} [Group G] {H : Subgroup G} {g : G} (h : g ∈ H) : (toSub H g : G) = g := by
  rw [toSub, dif_pos h]

/- English proof (translation)
Rewrite using `[map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul]`.
-/
theorem det_conj' {k : Type} [Field k] {a : ℕ} (u v : GL (Fin a) k) :
    GeneralLinearGroup.det (u⁻¹ * v * u) = GeneralLinearGroup.det v := by
  rw [map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul]

/- English proof (translation)
Introduce `E _ _ _ n a ha w hw μ K' hK' f hf Q₁ Q₂ hm₁ hm₂ hd₁ hd₂ hsep _ _`. Establish `hth : ∀ k, thL k w = MonoidHom.id _` using `fun k => by simp only [thL, if_pos hw]`. Establish `hnr : ∀ k (y : GLw k w), nrmL k w y = y` using `fun k y => by simp only [nrmL, if_pos hw]`. Establish `hUL : UL n w = ⊤` using `by simp only [UL, if_pos hw]`. Establish `hks : ∀ γ, kapSign n w Q₁ γ = 1` using `fun γ => by simp only [kapSign, if_pos hw]`.

Establish `hKL : (KL n w).map (UL n w).subtype = GlobalTheory.LFun.KGL w n`. Rewrite using `[KL, Subgroup.subgroupOf_map_subtype, hUL, inf_top_eq]`. Establish `hmem : ∀ g : GLw n w, g ∈ UL n w` using `fun g => by rw [hUL]; trivial`. Unfold `stTw2 kapOrb`. Simplify using `only [hth, hnr, hks, prodMap_id_id]`.

Distinguish the cases in `h0 : Q₁.coeff 0 = 0 ∨ Q₂.coeff 0 = 0`. Establish `hR : ∀ γ : UL n w, ¬ (γ.1.val.charpoly = Q₁ * Q₂)`. Introduce `γ h1`. Establish `h3` using `det_of_charpoly γ.1 h1`. Rewrite `h3` using `[Polynomial.mul_coeff_zero]`.

Apply the tactic sequence `rcases h0 with h0 | h0 <;> rw [h0] at h3 <;> simp only [zero_mul, mul_zero] at h3 <;>`. Conclude with `((Matrix.isUnit_iff_isUnit_det _).mp γ.1.isUnit).ne_zero h3`. Establish `hL : ∀ y : GLw a w × GLw (n - a) w, ¬ (y.1.val.charpoly = Q₁ ∧ y.2.val.charpoly = Q₂)`. Introduce and unpack `y ⟨h1, h2⟩`. Break down `h0 with h0 | h0` into its components or cases.

Establish `h3` using `det_of_charpoly y.1 h1`. Rewrite `h3` using `[h0, mul_zero]`. Conclude with `((Matrix.isUnit_iff_isUnit_det _).mp y.1.isUnit).ne_zero h3`. Establish `h3` using `det_of_charpoly y.2 h2`. Rewrite `h3` using `[h0, mul_zero]`.

Conclude with `((Matrix.isUnit_iff_isUnit_det _).mp y.2.isUnit).ne_zero h3`. Establish `hz : ∀ {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (S : Set G) (wt g : G → ℂ), (∀ y, y ∉ S) → clSum θ K S wt g = 0`. Introduce `G _ _ θ K S wt g hS`. Unfold `clSum`. Apply `finsum_eq_zero_of_forall_eq_zero` to reduce the goal to its premises.

Introduce `c`. Rewrite using `[if_neg (hS c.rep)]`. Rewrite using `[hz _ _ {y : GLw a w × GLw (n - a) w | y.1.val.charpoly = Q₁ ∧ y.2.val.charpoly = Q₂} _ _ hL, hz _ _ {γ : UL n w | γ.1.val.charpoly = Q₁ * Q₂} _ _ hR, mul_zero]`. Use `push_neg at h0`. Take `⟨x₁, hx₁⟩` from `existsOfCharpoly _ a Q₁ hm₁ hd₁ h0.1`.

Take `⟨x₂, hx₂⟩` from `existsOfCharpoly _ (n - a) Q₂ hm₂ hd₂ h0.2`. Establish `hs₁ : Q₁.Separable` using `hsep.of_mul_left`. Establish `hs₂ : Q₂.Separable` using `hsep.of_mul_right`. Establish `hLHS : clSum (MonoidHom.id _) ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w (n - a))) {y : GLw a w × GLw (n - a) w | y.1.val.charpoly = Q₁ ∧ y.2.val.charpoly = Q₂} 1 (ctMu (Nat.add_sub_cancel' ha) w μ f) = twOrb (MonoidHom.id _) ((GlobalTheory.LFun.KGL w a).prod (Glo …`. Rewrite using `[clSum_oneClass _ _ _ _ _ (x₁, x₂) ?_ ?_ ?_ ?_ (fun g => twOrb_twConj _ _ _ _ _)]`.

Simplify using the standard rewrite rules. Conclude with `⟨hx₁, hx₂⟩`. Introduce and unpack `y ⟨h1, h2⟩`. Take `⟨g₁, hg₁⟩` from `conjOfCharpoly _ a x₁ y.1 (hx₁.trans h1.symm) (hx₁ ▸ hs₁)`. Take `⟨g₂, hg₂⟩` from `conjOfCharpoly _ (n - a) x₂ y.2 (hx₂.trans h2.symm) (hx₂ ▸ hs₂)`.

Conclude with `⟨(g₁, g₂), Prod.ext hg₁ hg₂⟩`. Introduce `g`. Conclude with `⟨(charpoly_conj' g.1 x₁).trans hx₁, (charpoly_conj' g.2 x₂).trans hx₂⟩`. Introduce `g`. Both sides reduce to the same expression.

Take `⟨γ₀, hv⟩ : ∃ γ₀ : UL n w, (γ₀ : GLw n w) = blk (Nat.add_sub_cancel' ha) w (x₁, x₂) 0` from `⟨_, toSub_val (hmem _)⟩`. Establish `hcp : (γ₀ : GLw n w).val.charpoly = Q₁ * Q₂`. Rewrite using `[hv, blk_zero_charpoly, hx₁, hx₂]`. Establish `hRHS : clSum (MonoidHom.id (UL n w)) (KL n w) {γ : UL n w | γ.1.val.charpoly = Q₁ * Q₂} (fun _ => 1) f = twOrb (MonoidHom.id _) (GlobalTheory.LFun.KGL w n) (blk (Nat.add_sub_cancel' ha) w (x₁, x₂) 0) (fun y => f (toSub (UL n w) y))`. Rewrite using `[clSum_oneClass _ _ _ _ _ γ₀ hcp ?_ ?_ ?_ (fun g => twOrb_twConj _ _ _ _ _), one_mul, twOrb_top _ hUL, hKL, hv]`.

Introduce `γ hγ`. Take `⟨g, hg⟩` from `conjOfCharpoly _ n (γ₀ : GLw n w) γ.1 (hcp.trans hγ.symm) (hcp ▸ hsep)`. Use `⟨toSub (UL n w) g, Subtype.ext ?_⟩` and prove the remaining obligations. Simplify using `only [MonoidHom.id_apply, Subgroup.coe_mul, Subgroup.coe_inv, toSub_val (hmem g)]`. Conclude with `hg`.

Introduce `g show ((g⁻¹ * γ₀ * g : UL n w) : GLw n w).val.charpoly = _`. Simplify using `only [Subgroup.coe_mul, Subgroup.coe_inv]`. Rewrite using `[charpoly_conj', hcp]`. Introduce `g`. Both sides reduce to the same expression.

Rewrite using `[hLHS, hRHS]`. Establish `hisH` using `isHecke_top (UL n w) hUL K' f hK'.1 hf`. Establish `hdet₁` using `det_of_charpoly x₁ hx₁`. Establish `hdet₂` using `det_of_charpoly x₂ hx₂`. Establish `hdd : ((-1) ^ Q₁.natDegree * Q₁.coeff 0) ^ Q₂.natDegree * ((-1) ^ Q₂.natDegree * Q₂.coeff 0) ^ Q₁.natDegree = x₁.val.det ^ (n - a) * x₂.val.det ^ a`.

Rewrite using `[hd₁, hd₂, hdet₁, hdet₂]`. Establish `hne : (-1) ^ (Q₁.natDegree * Q₂.natDegree) * (((-1) ^ Q₁.natDegree * Q₁.coeff 0) ^ Q₂.natDegree * ((-1) ^ Q₂.natDegree * Q₂.coeff 0) ^ Q₁.natDegree) ≠ 0`. Rewrite using `[hdd]`. Establish `h1` using `(Matrix.isUnit_iff_isUnit_det _).mp x₁.isUnit`. Establish `h2` using `(Matrix.isUnit_iff_isUnit_det _).mp x₂.isUnit`.

Conclude with `mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (mul_ne_zero (pow_ne_zero _ h1.ne_zero) (pow_ne_zero _ h2.ne_zero))`. Establish `hu : Units.mk0 _ hne = (-1) ^ (a * (n - a)) * GeneralLinearGroup.det x₁ ^ (n - a) * GeneralLinearGroup.det x₂ ^ a`. Use `ext`. Rewrite using `[Units.val_mk0, hdd, hd₁, hd₂]`. Simplify using `[GeneralLinearGroup.val_det_apply, mul_assoc]`.

Establish `hδ : delta w μ Q₁ Q₂ = (μ ((-1) ^ (a * (n - a)) * GeneralLinearGroup.det x₁ ^ (n - a) * GeneralLinearGroup.det x₂ ^ a) : ℂ) * absHalf w (resultant Q₁ Q₂ ^ 2 / (x₁.val.det ^ (n - a) * x₂.val.det ^ a))`. Unfold `delta`. Simplify using `only [if_pos hw]`. Rewrite using `[dif_pos hne, hu, hdd]`. Establish `hct : ctMu (Nat.add_sub_cancel' ha) w μ f = fun y => (μ ((-1) ^ (a * (n - a)) * GeneralLinearGroup.det y.1 ^ (n - a) * GeneralLinearGroup.det y.2 ^ a) : ℂ) * ct (Nat.add_sub_cancel' ha) w (fun y => f (toSub (UL n w) y)) y` using `rfl`.

Rewrite using `[hct, twOrb_mulConst _ _ _ _ _ ?_, GlobalTheory.T.twisted_orbital_integral_levi_constant_term E n a ha w _ (Or.inr ⟨_, hisH.1, hisH.2⟩) (x₁, x₂) (by rw [hx₁, hx₂]; exact hsep), hδ]`. Simplify using `only`. Rewrite using `[hx₁, hx₂]`. Expand and normalize the polynomial expressions, which then agree. Introduce `x`.

Simplify using `only [MonoidHom.id_apply, Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv, det_conj']`.
-/
theorem match_ctMu_of_isSplitAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∀ (n a : ℕ) (ha : a ≤ n) (w : Pl E),
    IsSplitAt w → ∀ (μ : (w.adicCompletion E)ˣ →* ℂˣ), ∀ K' : Subgroup (UL n w), IsLevel (MonoidHom.id _) (KL n w) K' →
    ∀ f, IsHecke K' f → Match n a (n - a) w μ f (ctMu (Nat.add_sub_cancel' ha) w μ f) := by
  intro E _ _ _ n a ha w hw μ K' hK' f hf Q₁ Q₂ hm₁ hm₂ hd₁ hd₂ hsep _ _
  have hth : ∀ k, thL k w = MonoidHom.id _ := fun k => by simp only [thL, if_pos hw]
  have hnr : ∀ k (y : GLw k w), nrmL k w y = y := fun k y => by simp only [nrmL, if_pos hw]
  have hUL : UL n w = ⊤ := by simp only [UL, if_pos hw]
  have hks : ∀ γ, kapSign n w Q₁ γ = 1 := fun γ => by simp only [kapSign, if_pos hw]
  have hKL : (KL n w).map (UL n w).subtype = GlobalTheory.LFun.KGL w n := by
    rw [KL, Subgroup.subgroupOf_map_subtype, hUL, inf_top_eq]
  have hmem : ∀ g : GLw n w, g ∈ UL n w := fun g => by rw [hUL]; trivial
  unfold stTw2 kapOrb
  simp only [hth, hnr, hks, prodMap_id_id]
  by_cases h0 : Q₁.coeff 0 = 0 ∨ Q₂.coeff 0 = 0
  · have hR : ∀ γ : UL n w, ¬ (γ.1.val.charpoly = Q₁ * Q₂) := by
      intro γ h1
      have h3 := det_of_charpoly γ.1 h1
      rw [Polynomial.mul_coeff_zero] at h3
      rcases h0 with h0 | h0 <;> rw [h0] at h3 <;> simp only [zero_mul, mul_zero] at h3 <;>
        exact ((Matrix.isUnit_iff_isUnit_det _).mp γ.1.isUnit).ne_zero h3
    have hL : ∀ y : GLw a w × GLw (n - a) w, ¬ (y.1.val.charpoly = Q₁ ∧ y.2.val.charpoly = Q₂) := by
      rintro y ⟨h1, h2⟩
      rcases h0 with h0 | h0
      · have h3 := det_of_charpoly y.1 h1
        rw [h0, mul_zero] at h3
        exact ((Matrix.isUnit_iff_isUnit_det _).mp y.1.isUnit).ne_zero h3
      · have h3 := det_of_charpoly y.2 h2
        rw [h0, mul_zero] at h3
        exact ((Matrix.isUnit_iff_isUnit_det _).mp y.2.isUnit).ne_zero h3
    have hz : ∀ {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (S : Set G) (wt g : G → ℂ),
        (∀ y, y ∉ S) → clSum θ K S wt g = 0 := by
      intro G _ _ θ K S wt g hS
      unfold clSum
      apply finsum_eq_zero_of_forall_eq_zero
      intro c
      rw [if_neg (hS c.rep)]
    rw [hz _ _ {y : GLw a w × GLw (n - a) w | y.1.val.charpoly = Q₁ ∧ y.2.val.charpoly = Q₂} _ _ hL,
      hz _ _ {γ : UL n w | γ.1.val.charpoly = Q₁ * Q₂} _ _ hR, mul_zero]
  · push_neg at h0
    obtain ⟨x₁, hx₁⟩ := existsOfCharpoly _ a Q₁ hm₁ hd₁ h0.1
    obtain ⟨x₂, hx₂⟩ := existsOfCharpoly _ (n - a) Q₂ hm₂ hd₂ h0.2
    have hs₁ : Q₁.Separable := hsep.of_mul_left
    have hs₂ : Q₂.Separable := hsep.of_mul_right
    have hLHS : clSum (MonoidHom.id _) ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w (n - a)))
        {y : GLw a w × GLw (n - a) w | y.1.val.charpoly = Q₁ ∧ y.2.val.charpoly = Q₂} 1
        (ctMu (Nat.add_sub_cancel' ha) w μ f) = twOrb (MonoidHom.id _)
        ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w (n - a))) (x₁, x₂) (ctMu (Nat.add_sub_cancel' ha) w μ f) := by
      rw [clSum_oneClass _ _ _ _ _ (x₁, x₂) ?_ ?_ ?_ ?_ (fun g => twOrb_twConj _ _ _ _ _)]
      · simp
      · exact ⟨hx₁, hx₂⟩
      · rintro y ⟨h1, h2⟩
        obtain ⟨g₁, hg₁⟩ := conjOfCharpoly _ a x₁ y.1 (hx₁.trans h1.symm) (hx₁ ▸ hs₁)
        obtain ⟨g₂, hg₂⟩ := conjOfCharpoly _ (n - a) x₂ y.2 (hx₂.trans h2.symm) (hx₂ ▸ hs₂)
        exact ⟨(g₁, g₂), Prod.ext hg₁ hg₂⟩
      · intro g
        exact ⟨(charpoly_conj' g.1 x₁).trans hx₁, (charpoly_conj' g.2 x₂).trans hx₂⟩
      · intro g; rfl
    obtain ⟨γ₀, hv⟩ : ∃ γ₀ : UL n w, (γ₀ : GLw n w) = blk (Nat.add_sub_cancel' ha) w (x₁, x₂) 0 :=
      ⟨_, toSub_val (hmem _)⟩
    have hcp : (γ₀ : GLw n w).val.charpoly = Q₁ * Q₂ := by
      rw [hv, blk_zero_charpoly, hx₁, hx₂]
    have hRHS : clSum (MonoidHom.id (UL n w)) (KL n w) {γ : UL n w | γ.1.val.charpoly = Q₁ * Q₂} (fun _ => 1) f =
        twOrb (MonoidHom.id _) (GlobalTheory.LFun.KGL w n) (blk (Nat.add_sub_cancel' ha) w (x₁, x₂) 0)
          (fun y => f (toSub (UL n w) y)) := by
      rw [clSum_oneClass _ _ _ _ _ γ₀ hcp ?_ ?_ ?_ (fun g => twOrb_twConj _ _ _ _ _), one_mul, twOrb_top _ hUL, hKL, hv]
      · intro γ hγ
        obtain ⟨g, hg⟩ := conjOfCharpoly _ n (γ₀ : GLw n w) γ.1 (hcp.trans hγ.symm) (hcp ▸ hsep)
        refine ⟨toSub (UL n w) g, Subtype.ext ?_⟩
        simp only [MonoidHom.id_apply, Subgroup.coe_mul, Subgroup.coe_inv, toSub_val (hmem g)]
        exact hg
      · intro g
        show ((g⁻¹ * γ₀ * g : UL n w) : GLw n w).val.charpoly = _
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [charpoly_conj', hcp]
      · intro g; rfl
    rw [hLHS, hRHS]

    have hisH := isHecke_top (UL n w) hUL K' f hK'.1 hf
    have hdet₁ := det_of_charpoly x₁ hx₁
    have hdet₂ := det_of_charpoly x₂ hx₂
    have hdd : ((-1) ^ Q₁.natDegree * Q₁.coeff 0) ^ Q₂.natDegree * ((-1) ^ Q₂.natDegree * Q₂.coeff 0) ^ Q₁.natDegree =
        x₁.val.det ^ (n - a) * x₂.val.det ^ a := by
      rw [hd₁, hd₂, hdet₁, hdet₂]
    have hne : (-1) ^ (Q₁.natDegree * Q₂.natDegree) * (((-1) ^ Q₁.natDegree * Q₁.coeff 0) ^ Q₂.natDegree *
        ((-1) ^ Q₂.natDegree * Q₂.coeff 0) ^ Q₁.natDegree) ≠ 0 := by
      rw [hdd]
      have h1 := (Matrix.isUnit_iff_isUnit_det _).mp x₁.isUnit
      have h2 := (Matrix.isUnit_iff_isUnit_det _).mp x₂.isUnit
      exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
        (mul_ne_zero (pow_ne_zero _ h1.ne_zero) (pow_ne_zero _ h2.ne_zero))
    have hu : Units.mk0 _ hne = (-1) ^ (a * (n - a)) * GeneralLinearGroup.det x₁ ^ (n - a) *
        GeneralLinearGroup.det x₂ ^ a := by
      ext
      rw [Units.val_mk0, hdd, hd₁, hd₂]
      simp [GeneralLinearGroup.val_det_apply, mul_assoc]
    have hδ : delta w μ Q₁ Q₂ = (μ ((-1) ^ (a * (n - a)) * GeneralLinearGroup.det x₁ ^ (n - a) *
        GeneralLinearGroup.det x₂ ^ a) : ℂ) * absHalf w (resultant Q₁ Q₂ ^ 2 / (x₁.val.det ^ (n - a) * x₂.val.det ^ a)) := by
      unfold delta
      simp only [if_pos hw]
      rw [dif_pos hne, hu, hdd]
    have hct : ctMu (Nat.add_sub_cancel' ha) w μ f = fun y =>
        (μ ((-1) ^ (a * (n - a)) * GeneralLinearGroup.det y.1 ^ (n - a) * GeneralLinearGroup.det y.2 ^ a) : ℂ) *
          ct (Nat.add_sub_cancel' ha) w (fun y => f (toSub (UL n w) y)) y := rfl
    rw [hct, twOrb_mulConst _ _ _ _ _ ?_, GlobalTheory.T.twisted_orbital_integral_levi_constant_term E n a ha w _ (Or.inr ⟨_, hisH.1, hisH.2⟩) (x₁, x₂)
      (by rw [hx₁, hx₂]; exact hsep), hδ]
    · dsimp only
      rw [hx₁, hx₂]
      ring
    · intro x
      simp only [MonoidHom.id_apply, Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv, det_conj']

end GlobalTheory.BCT.SplitCtMatch
