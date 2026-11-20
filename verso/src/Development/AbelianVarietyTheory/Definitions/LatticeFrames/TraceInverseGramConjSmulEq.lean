import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmHostImaginaryGeneratorNeZero

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unf.Model

variable {D : D7}

open GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule

variable {ρ : ℕ} {B : BesLev D ρ} {L' : HSp D} {ζ' : Fin L'.rank → D.host.E} (l : Link B L' ζ')

/- English proof (translation)
Rewrite using `[zEll, Matrix.mul_vecMulVec, ← ratV_mulVec, l.map, yZero, zEll, ← Matrix.neg_vecMulVec]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Conclude with `map_neg (incA D) _`.
-/
theorem tau_zEll (σ : ℕ) : (rat l.τ : Mx D B.L.rank L'.rank) ⬝ zEll L' σ ζ' = yZero B.L σ B.ζ := by
  rw [zEll, Matrix.mul_vecMulVec, ← ratV_mulVec, l.map, yZero, zEll, ← Matrix.neg_vecMulVec]
  congr 1
  funext i
  exact map_neg (incA D) _

/- English proof (translation)
Rewrite using `[Link.κ, Link.κ, ofAdj, ofAdj, mt_inv, ← Matrix.mul_assoc (rat l.τ), adj_mul, Matrix.mul_smul]`. Simplify using `only [Matrix.mul_assoc, gA_giA_cancel]`.
-/
theorem kappa_mul (S : HSp D) (w : WO S L') (g : GA D S) : l.κ S (w ⬝ mt S g) = mt S g⁻¹ ⬝ l.κ S w := by
  rw [Link.κ, Link.κ, ofAdj, ofAdj, mt_inv, ← Matrix.mul_assoc (rat l.τ), adj_mul, Matrix.mul_smul]
  simp only [Matrix.mul_assoc, gA_giA_cancel]

/- English proof (translation)
Rewrite using `[Link.κ, Link.κ, ofAdj, ofAdj, d.p0_eq, ← Matrix.mul_assoc (rat l.τ), adj_mul, Matrix.mul_smul]`. Simplify using `only [Matrix.mul_assoc, gA_giA_cancel]`.
-/
theorem kappa_mul_jacobiEmbedding {W W₀ : HSp D} {σ : ℕ} (d : HypDec W W₀ σ) (x : WO W L') : l.κ W₀ (x ⬝ d.j0) = d.p0 ⬝ l.κ W x := by
  rw [Link.κ, Link.κ, ofAdj, ofAdj, d.p0_eq, ← Matrix.mul_assoc (rat l.τ), adj_mul, Matrix.mul_smul]
  simp only [Matrix.mul_assoc, gA_giA_cancel]

/- English proof (translation)
Rewrite using `[Link.κ, ofAdj, d.extX_apply, d.incAdj_apply, d.incY_apply, ← Matrix.mul_assoc (rat l.τ), tau_zEll, d.pX_eq, adj_mul, adj_mul, adj_adj, adj_gA, Matrix.mul_smul]`. Simplify using `only [Matrix.mul_assoc, giA_gA_cancel]`.
-/
theorem kappa_extX {W W₀ : HSp D} {σ : ℕ} (d : HypDec W W₀ σ) :
    l.κ W (d.extX L' (zEll L' σ ζ')) = d.incAdj B.L (yZero B.L σ B.ζ) := by
  rw [Link.κ, ofAdj, d.extX_apply, d.incAdj_apply, d.incY_apply, ← Matrix.mul_assoc (rat l.τ), tau_zEll, d.pX_eq, adj_mul,
    adj_mul, adj_adj, adj_gA, Matrix.mul_smul]
  simp only [Matrix.mul_assoc, giA_gA_cancel]

/- English proof (translation)
Rewrite using `[ptS, kappa_mul_jacobiEmbedding, kappa_mul, kappa_extX, ptT]`.
-/
theorem ptT_eq {W W₀ : HSp D} {σ : ℕ} (d : HypDec W W₀ σ) (n : GA D W) :
    ptT d B.L (yZero B.L σ B.ζ) n = l.κ W₀ (ptS d L' (zEll L' σ ζ') n) := by
  rw [ptS, kappa_mul_jacobiEmbedding, kappa_mul, kappa_extX, ptT]

include l in
/- English proof (translation)
Establish `: Unique (Fin L'.rank)` using `by rw [h.1]; infer_instance`. Establish `hn` using `l.norm`. Establish `hm : B.ζ = -(l.τ *ᵥ ζ')` using `by rw [l.map, neg_neg]`. Establish `h0` using `h.2`. Rewrite `hn` using `[hm, star_neg, Matrix.mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg, Matrix.star_mulVec, ← dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]`.

Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Take `rfl` from `Subsingleton.elim i default`. Take `rfl` from `Subsingleton.elim j default`. Generalize the expression as in `l.τᴴ * (B.L.gram * l.τ) = M at hn ⊢`. Simplify using `only [dotProduct, Matrix.mulVec, Fintype.sum_unique, Pi.star_apply] at hn h0`.

Establish `hz : ζ' default ≠ 0` using `fun e => h0 (by rw [e]; simp)`. Establish `hz' : star (ζ' default) ≠ 0` using `star_ne_zero.2 hz`. Rewrite using `[Matrix.smul_apply, smul_eq_mul]`. Apply `mul_right_cancel₀ hz` to reduce the goal to its premises. Apply `mul_left_cancel₀ hz'` to reduce the goal to its premises.

Rewrite using `[hn]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tau_gram (h : IsLineVec L' ζ') :
    l.τᴴ * (B.L.gram * l.τ) = (D.host.xi0 * star D.host.xi0) • L'.gram := by
  have : Unique (Fin L'.rank) := by rw [h.1]; infer_instance
  have hn := l.norm
  have hm : B.ζ = -(l.τ *ᵥ ζ') := by rw [l.map, neg_neg]
  have h0 := h.2
  rw [hm, star_neg, Matrix.mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg, Matrix.star_mulVec, ← dotProduct_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc] at hn
  refine Matrix.ext fun i j => ?_
  obtain rfl := Subsingleton.elim i default
  obtain rfl := Subsingleton.elim j default
  generalize l.τᴴ * (B.L.gram * l.τ) = M at hn ⊢
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_unique, Pi.star_apply] at hn h0
  have hz : ζ' default ≠ 0 := fun e => h0 (by rw [e]; simp)
  have hz' : star (ζ' default) ≠ 0 := star_ne_zero.2 hz
  rw [Matrix.smul_apply, smul_eq_mul]
  apply mul_right_cancel₀ hz
  apply mul_left_cancel₀ hz'
  rw [hn]; ring

/- English proof (translation)
Establish `h : (τ * (x * (g * (y * (σ * k))))).trace = (g * (y * ((σ * (k * τ)) * x))).trace`. Rewrite using `[← Matrix.mul_assoc, trace_mul_comm]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[h, e, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, trace_smul, smul_smul, smul_smul, show r * s * t = 1 by rw [← e1]; ring, one_smul]`.
-/
theorem trace_inverseGram_conj_smul_eq {R : Type} [CommRing R] {a b c : ℕ} (τ : Matrix (Fin a) (Fin b) R) (x : Matrix (Fin b) (Fin c) R)
    (g : Matrix (Fin c) (Fin c) R) (y : Matrix (Fin c) (Fin b) R) (σ : Matrix (Fin b) (Fin a) R)
    (k : Matrix (Fin a) (Fin a) R) (k' : Matrix (Fin b) (Fin b) R) {r s t : R} (e : σ * (k * τ) = t • k')
    (e1 : s * (r * t) = 1) :
    r • s • (τ * (x * (g * (y * (σ * k))))).trace = (g * (y * (k' * x))).trace := by
  have h : (τ * (x * (g * (y * (σ * k))))).trace = (g * (y * ((σ * (k * τ)) * x))).trace := by
    rw [← Matrix.mul_assoc, trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [h, e, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, trace_smul, smul_smul, smul_smul,
    show r * s * t = 1 by rw [← e1]; ring, one_smul]

/- English proof (translation)
Establish `e : adj (rat l.τ : Mx D B.L.rank L'.rank) ⬝ (gA B.L ⬝ rat l.τ) = incA D (D.host.xi0 * star D.host.xi0) • gA L'`. Rewrite using `[← rat_conjTranspose, gA, ← rat_mul, ← rat_mul, tau_gram l h]`. Conclude with `Matrix.ext fun i j => map_mul (incA D) _ _`. Establish `e1 : cA D (incA D (-D.host.xi0⁻¹)) * (incA D (-D.host.xi0⁻¹) * incA D (D.host.xi0 * star D.host.xi0)) = 1`. Establish `h0` using `GlobalTheory.Unf.Inhab.cmHost_imaginaryGenerator_ne_zero D`.

Establish `h1 : star D.host.xi0 ≠ 0` using `star_ne_zero.2 h0`. Express the relevant statement in the definitionally equal form `incA D (star (-D.host.xi0⁻¹)) * _ = 1`. Rewrite using `[← map_mul, ← map_mul, ← map_one (incA D), star_neg, star_inv₀]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[← symplOH_skew, symplOH_eq, symplOH_eq, hO_eq_trace, hO_eq_trace, Link.κ, Link.κ, ofAdj, ofAdj]`. Use `congr 1`. Simplify using `only [adj_smul, adj_mul, adj_adj, adj_gA, adj_giA, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, gA_giA_cancel, giA_gA_cancel, trace_smul]`. Conclude with `trace_inverseGram_conj_smul_eq _ _ _ _ _ _ _ e e1`.
-/
theorem symplOH_kappa (h : IsLineVec L' ζ') (S : HSp D) (w w' : WO S L') :
    symplOH B.L S (l.κ S w) (l.κ S w') = -symplOH S L' w w' := by
  have e : adj (rat l.τ : Mx D B.L.rank L'.rank) ⬝ (gA B.L ⬝ rat l.τ) = incA D (D.host.xi0 * star D.host.xi0) • gA L' := by
    rw [← rat_conjTranspose, gA, ← rat_mul, ← rat_mul, tau_gram l h]
    exact Matrix.ext fun i j => map_mul (incA D) _ _
  have e1 : cA D (incA D (-D.host.xi0⁻¹)) * (incA D (-D.host.xi0⁻¹) * incA D (D.host.xi0 * star D.host.xi0)) = 1 := by
    have h0 := GlobalTheory.Unf.Inhab.cmHost_imaginaryGenerator_ne_zero D
    have h1 : star D.host.xi0 ≠ 0 := star_ne_zero.2 h0
    change incA D (star (-D.host.xi0⁻¹)) * _ = 1
    rw [← map_mul, ← map_mul, ← map_one (incA D), star_neg, star_inv₀]
    congr 1
    field_simp
  rw [← symplOH_skew, symplOH_eq, symplOH_eq, hO_eq_trace, hO_eq_trace, Link.κ, Link.κ, ofAdj, ofAdj]
  congr 1
  simp only [adj_smul, adj_mul, adj_adj, adj_gA, adj_giA, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, gA_giA_cancel,
    giA_gA_cancel, trace_smul]
  exact trace_inverseGram_conj_smul_eq _ _ _ _ _ _ _ e e1

include l in

/- English proof (translation)
Rewrite using `[cenT, cenS, ← symplOH_kappa l h, kappa_mul, kappa_extX]`.
-/
theorem cenT_eq (h : IsLineVec L' ζ') {W W₀ : HSp D} {σ : ℕ} (d : HypDec W W₀ σ) (n : GA D W) :
    cenT d B.L (yZero B.L σ B.ζ) n = -cenS d L' (zEll L' σ ζ') n := by
  rw [cenT, cenS, ← symplOH_kappa l h, kappa_mul, kappa_extX]

/- English proof (translation)
Proceed by induction on `c with`. Consider the case `last t => rfl`. Consider the case `step J B' s₁ s₂ l vL c ih => exact ⟨0, 0, IsQuotIntL1.zero, fun _ => ⟨IsQuotIntL1.zero, fun _ => ih⟩⟩`.
-/
theorem iter_zero {ψ : AddChar (AF D.host.F) ℂ} {T : HSp D} {σ : ℕ} {B₁ : BesLev D σ} (c : Chain ψ T σ B₁) :
    c.Iter (fun _ => 0) 0 := by
  induction c with
  | last t => rfl
  | step J B' s₁ s₂ l vL c ih => exact ⟨0, 0, IsQuotIntL1.zero, fun _ => ⟨IsQuotIntL1.zero, fun _ => ih⟩⟩

/- English proof (translation)
Proceed by induction on `c with`. Consider the case `last t => intro q z h`. Conclude with `congrArg (a * ·) h`. Consider the case `step J B' s₁ s₂ l vL c ih`. Introduce and unpack `q z ⟨f₁, f₂, h1, h2⟩`.

Conclude with `⟨a • f₁, a • f₂, h1.smul a, fun h₁ => ⟨(h2 h₁).1.smul a, fun h₂ => ih _ _ ((h2 h₁).2 h₂)⟩⟩`.
-/
theorem iter_smul {ψ : AddChar (AF D.host.F) ℂ} {T : HSp D} {σ : ℕ} {B₁ : BesLev D σ} (c : Chain ψ T σ B₁) (a : ℂ) :
    ∀ q z, c.Iter q z → c.Iter (fun h => a * q h) (a * z) := by
  induction c with
  | last t => intro q z h; exact congrArg (a * ·) h
  | step J B' s₁ s₂ l vL c ih =>
    rintro q z ⟨f₁, f₂, h1, h2⟩
    exact ⟨a • f₁, a • f₂, h1.smul a, fun h₁ => ⟨(h2 h₁).1.smul a, fun h₂ => ih _ _ ((h2 h₁).2 h₂)⟩⟩

/- English proof (translation)
Take `⟨⟨ψ, hψ⟩, h⟩` from `GlobalTheory.Unf.Inhab.exists_chain D`. Take `⟨T, B, c, h1, h2, -, h3⟩` from `(h ψ hψ).1`. Conclude with `⟨ψ, T, B, c, h1, h2, h3⟩`.
-/
theorem chain_inhabited (D : D7) : ∃ (ψ : AddChar (AF D.host.F) ℂ) (T : HSp D) (B : BesLev D 1) (c : Chain ψ T 1 B),
    0 < B.A.rank ∧ 0 < T.rank ∧ ∃ Φ : c.Data, c.IsTheta Φ ∧ GlobalTheory.Unf.Inhab.AllNonzero c Φ := by
  obtain ⟨⟨ψ, hψ⟩, h⟩ := GlobalTheory.Unf.Inhab.exists_chain D
  obtain ⟨T, B, c, h1, h2, -, h3⟩ := (h ψ hψ).1
  exact ⟨ψ, T, B, c, h1, h2, h3⟩

/- English proof (translation)
Simplify using `only [jacS, jacT, heisO, Pi.smul_apply, smul_eq_mul, symplOH_zero_left, AddChar.map_zero_eq_one, one_mul, zero_add]`. Rewrite using `[cenT_eq l h, ptT_eq l, hψ, star_mul', star_star]`.
-/
theorem jac_link {ψ : AddChar (AF D.host.F) ℂ} (hψ : ∀ a, ψ (-a) = star (ψ a)) (h : IsLineVec L' ζ') {W W₀ : HSp D} {σ : ℕ}
    (d : HypDec W W₀ σ) (n : GA D W) (f : WO B.L W₀ → ℂ) :
    star (jacS ψ d L' (zEll L' σ ζ') n (fun w => star (f (l.κ W₀ w))) 0) = jacT ψ d B.L (yZero B.L σ B.ζ) n f 0 := by
  simp only [jacS, jacT, heisO, Pi.smul_apply, smul_eq_mul, symplOH_zero_left, AddChar.map_zero_eq_one, one_mul, zero_add]
  rw [cenT_eq l h, ptT_eq l, hψ, star_mul', star_star]

/- English proof (translation)
Establish `hm : Measurable fun p : H × N => (p.2.1 * s p.1 : G)` using `(measurable_subtype_coe.comp measurable_snd).mul (hs.comp measurable_fst)`. Introduce `h`. Establish `h1 : μ.prod ν = 0` using `(Measure.map_eq_zero_iff (hm.subtype_mk).aemeasurable).1 h`. Establish `h2` using `congrArg (fun m : Measure (H × N) => m (Set.univ ×ˢ Set.univ)) h1`. Simplify using `only [Measure.prod_prod, Measure.coe_zero, Pi.zero_apply, mul_eq_zero, Measure.measure_univ_eq_zero] at h2`.

Conclude with `h2.elim hμ hν`.
-/
theorem semiMeas_ne_zero {G H : Type} [Group G] [Group H] [MeasurableSpace G] [MeasurableSpace H] [MeasurableMul₂ G]
    (N : Subgroup G) (s : H →* G) (hs : Measurable s) (μ : Measure H) (ν : Measure N) [SFinite ν] (hμ : μ ≠ 0) (hν : ν ≠ 0) :
    semiMeas N s μ ν ≠ 0 := by
  have hm : Measurable fun p : H × N => (p.2.1 * s p.1 : G) :=
    (measurable_subtype_coe.comp measurable_snd).mul (hs.comp measurable_fst)
  intro h
  have h1 : μ.prod ν = 0 := (Measure.map_eq_zero_iff (hm.subtype_mk).aemeasurable).1 h
  have h2 := congrArg (fun m : Measure (H × N) => m (Set.univ ×ˢ Set.univ)) h1
  simp only [Measure.prod_prod, Measure.coe_zero, Pi.zero_apply, mul_eq_zero, Measure.measure_univ_eq_zero] at h2
  exact h2.elim hμ hν

/- English proof (translation)
Take `⟨i1, i2, i3, i4, i5, i6, i7⟩` from `GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D S`. Use `v.unit.1` as an intermediate fact. Use `⟨?_, fun h => ?_⟩` and prove the remaining obligations. Establish `: SecondCountableTopology (flagN d)` using `TopologicalSpace.Subtype.secondCountableTopology (flagN d : Set (GA D S))`. Take `⟨K, hK, h⟩` from `(GlobalTheory.Mem.UnipCocompact.radicals_cocompact D S σ d.e (isIsoSub_e d)).1`.

Establish `hcl : IsClosed (NFlag S d.e : Set (GA D S))`. Establish `: DiscreteTopology (GQ S ⊓ NFlag S d.e : Subgroup (GA D S))` using `DiscreteTopology.of_subset (s := (GQ S : Set (GA D S))) i6 (fun x hx => hx.1)`. Establish `h1 : IsClosed ((GQ S ⊓ NFlag S d.e : Subgroup (GA D S)) : Set (GA D S))` using `Subgroup.isClosed_of_discrete`. Establish `h2` using `h1.mul_right_of_isCompact (hK.image continuous_subtype_val)`. Use `h2 using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Take `⟨γ, hγ, k, hk, e⟩` from `h ⟨x, hx⟩`. Conclude with `⟨γ, ⟨hγ, γ.2⟩, k, ⟨k, hk, rfl⟩, (congrArg Subtype.val e).symm⟩`.

Introduce and unpack `⟨γ, hγ, _, ⟨k, -, rfl⟩, rfl⟩`. Conclude with `mul_mem hγ.2 k.2`. Establish `: LocallyCompactSpace (flagN d)` using `hcl.locallyCompactSpace`. Use `infer_instance`. Use `v.unit.2.2` as an intermediate fact.

Rewrite `this` using `[h]`. Simplify using `at this`.
-/
theorem sFinite_volN {S S₀ : HSp D} {σ : ℕ} {d : HypDec S S₀ σ} (v : VolN d) : SFinite v.ν ∧ v.ν ≠ 0 := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D S
  have := v.unit.1
  refine ⟨?_, fun h => ?_⟩
  · have : SecondCountableTopology (flagN d) := TopologicalSpace.Subtype.secondCountableTopology (flagN d : Set (GA D S))
    obtain ⟨K, hK, h⟩ := (GlobalTheory.Mem.UnipCocompact.radicals_cocompact D S σ d.e (isIsoSub_e d)).1
    have hcl : IsClosed (NFlag S d.e : Set (GA D S)) := by
      have : DiscreteTopology (GQ S ⊓ NFlag S d.e : Subgroup (GA D S)) :=
        DiscreteTopology.of_subset (s := (GQ S : Set (GA D S))) i6 (fun x hx => hx.1)
      have h1 : IsClosed ((GQ S ⊓ NFlag S d.e : Subgroup (GA D S)) : Set (GA D S)) := Subgroup.isClosed_of_discrete
      have h2 := h1.mul_right_of_isCompact (hK.image continuous_subtype_val)
      convert h2 using 1
      ext x
      constructor
      · intro hx
        obtain ⟨γ, hγ, k, hk, e⟩ := h ⟨x, hx⟩
        exact ⟨γ, ⟨hγ, γ.2⟩, k, ⟨k, hk, rfl⟩, (congrArg Subtype.val e).symm⟩
      · rintro ⟨γ, hγ, _, ⟨k, -, rfl⟩, rfl⟩
        exact mul_mem hγ.2 k.2
    have : LocallyCompactSpace (flagN d) := hcl.locallyCompactSpace
    infer_instance
  · have := v.unit.2.2
    rw [h] at this
    simp at this

/- English proof (translation)
Take `⟨i1, i2, i3, i4, i5, i6, i7⟩` from `GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D J.W`. Take `⟨j1, j2, j3, j4, j5, j6, j7⟩` from `GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D J.W₀`. Use `J.v0.haar` as an intermediate fact. Take `⟨h1, h2⟩` from `sFinite_volN J.vN`. Conclude with `semiMeas_ne_zero _ _ J.d.continuous_embed.measurable _ _ (NeZero.ne _) h2`.
-/
theorem jac_muR_ne_zero (J : JacLev D ρ) : J.μR ≠ 0 := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D J.W
  obtain ⟨j1, j2, j3, j4, j5, j6, j7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D J.W₀
  have := J.v0.haar
  obtain ⟨h1, h2⟩ := sFinite_volN J.vN
  exact semiMeas_ne_zero _ _ J.d.continuous_embed.measurable _ _ (NeZero.ne _) h2

/- English proof (translation)
Take `⟨i1, i2, i3, i4, i5, i6, i7⟩` from `GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.V`. Take `⟨j1, j2, j3, j4, j5, j6, j7⟩` from `GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.A`. Use `B.vA.haar` as an intermediate fact. Take `⟨h1, h2⟩` from `sFinite_volN B.vN`. Establish `hc : Continuous (embA B.d B.o)` using `B.d.continuous_embed.comp (B.o.continuous_emb.comp (continuous_id.prodMk continuous_const))`.

Conclude with `semiMeas_ne_zero _ _ hc.measurable _ _ (NeZero.ne _) h2`.
-/
theorem bes_muR_ne_zero (B : BesLev D ρ) : B.μR ≠ 0 := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.V
  obtain ⟨j1, j2, j3, j4, j5, j6, j7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.A
  have := B.vA.haar
  obtain ⟨h1, h2⟩ := sFinite_volN B.vN
  have hc : Continuous (embA B.d B.o) :=
    B.d.continuous_embed.comp (B.o.continuous_emb.comp (continuous_id.prodMk continuous_const))
  exact semiMeas_ne_zero _ _ hc.measurable _ _ (NeZero.ne _) h2

end GlobalTheory.Unf.Model

end
