import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterTrivialOfLocal
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HermitianDarbouxSplitProductStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CmAlgebraSplitInvolution

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct
open Filter Topology

noncomputable section

namespace PositivityTheory.ThKF0.Sg

section Split

variable {F A R₁ R₂ : Type} (E : Type) [Field F] [CommRing A] [Algebra F A] [CommRing R₁] [Algebra F R₁] [CommRing R₂]
  [Algebra F R₂] [CommRing E] [Algebra F E]

def split (s : A ≃ₐ[F] R₁ × R₂) : A ⊗[F] E ≃ₐ[F] (R₁ ⊗[F] E) × (R₂ ⊗[F] E) :=
  (Algebra.TensorProduct.congr s AlgEquiv.refl).trans
    (((Algebra.TensorProduct.comm F (R₁ × R₂) E).trans (Algebra.TensorProduct.prodRight F F E R₁ R₂)).trans
      (AlgEquiv.prodCongr (Algebra.TensorProduct.comm F E R₁) (Algebra.TensorProduct.comm F E R₂)))

variable {E}

/- English proof (translation)
Establish `h : (Algebra.TensorProduct.comm F (R₁ × R₂) E) (s a ⊗ₜ[F] e) = e ⊗ₜ[F] s a` using `rfl`. Establish `h0 : Algebra.TensorProduct.congr s (AlgEquiv.refl : E ≃ₐ[F] E) (a ⊗ₜ[F] e) = s a ⊗ₜ[F] e` using `rfl`. Simplify using `only [split, AlgEquiv.trans_apply, h0, h, Algebra.TensorProduct.prodRight_tmul]`. Both sides reduce to the same expression.
-/
theorem split_tmul (s : A ≃ₐ[F] R₁ × R₂) (a : A) (e : E) :
    split E s (a ⊗ₜ[F] e) = ((s a).1 ⊗ₜ[F] e, (s a).2 ⊗ₜ[F] e) := by
  have h : (Algebra.TensorProduct.comm F (R₁ × R₂) E) (s a ⊗ₜ[F] e) = e ⊗ₜ[F] s a := rfl
  have h0 : Algebra.TensorProduct.congr s (AlgEquiv.refl : E ≃ₐ[F] E) (a ⊗ₜ[F] e) = s a ⊗ₜ[F] e := rfl
  simp only [split, AlgEquiv.trans_apply, h0, h, Algebra.TensorProduct.prodRight_tmul]
  rfl

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Both sides reduce to the same expression. Consider the case `tmul a e`. Rewrite using `[Algebra.TensorProduct.map_tmul, split_tmul, split_tmul]`.

Both sides reduce to the same expression. Consider the case `add x y hx hy`. Rewrite using `[map_add, map_add, hx, hy, map_add]`. Simplify using the standard rewrite rules.
-/
theorem split_conj (s : A ≃ₐ[F] R₁ × R₂) (σ : E →ₐ[F] E) (x : A ⊗[F] E) :
    split E s (Algebra.TensorProduct.map (AlgHom.id A A) σ x) =
      (Algebra.TensorProduct.map (AlgHom.id F R₁) σ (split E s x).1,
        Algebra.TensorProduct.map (AlgHom.id F R₂) σ (split E s x).2) := by
  induction x using TensorProduct.induction_on with
  | zero => simp; rfl
  | tmul a e =>
    rw [Algebra.TensorProduct.map_tmul, split_tmul, split_tmul]
    rfl
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, map_add]
    simp

end Split

section Piece

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] {c : S →ₐ[R] S} {ι : Type} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Establish `h1 : f * (1 - f) = 0` using `by linear_combination -hf`. Establish `h2 : (1 - f) * f = 0` using `by linear_combination -hf`. Establish `h3 : (1 - f) * (1 - f) = 1 - f` using `by linear_combination hf`. Simplify using `only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, hf, h1, h2, h3, zero_smul, add_zero, zero_add]`.
-/
theorem mix_mul {f : S} (hf : f * f = f) (A B C D : Matrix ι ι S) :
    (f • A + (1 - f) • B) * (f • C + (1 - f) • D) = f • (A * C) + (1 - f) • (B * D) := by
  have h1 : f * (1 - f) = 0 := by linear_combination -hf
  have h2 : (1 - f) * f = 0 := by linear_combination -hf
  have h3 : (1 - f) * (1 - f) = 1 - f := by linear_combination hf
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, hf, h1, h2, h3,
    zero_smul, add_zero, zero_add]

/- English proof (translation)
Rewrite using `[← add_smul, add_sub_cancel, one_smul]`.
-/
theorem mix_self (f : S) (A : Matrix ι ι S) : f • A + (1 - f) • A = A := by
  rw [← add_smul, add_sub_cancel, one_smul]

def piece {J : Matrix ι ι S} {f : S} (hf : f * f = f) (hc : c f = f) (g : UG c J) : UG c J :=
  ⟨⟨f • g.1.1 + (1 - f) • 1, f • (g.1⁻¹).1 + (1 - f) • 1, by rw [mix_mul hf, Units.mul_inv, mul_one, mix_self],
    by rw [mix_mul hf, Units.inv_mul, mul_one, mix_self]⟩, by
    have hg : (g.1.1)ᵀ * J * (g.1.1).map c = J := g.2
    change (f • g.1.1 + (1 - f) • 1)ᵀ * J * (f • g.1.1 + (1 - f) • (1 : Matrix ι ι S)).map c = J
    have e : (f • g.1.1 + (1 - f) • (1 : Matrix ι ι S)).map c = f • (g.1.1).map c + (1 - f) • 1 := by
      ext i j
      by_cases h : i = j <;> simp [hc, Matrix.one_apply, h]
    rw [e, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul, Matrix.transpose_one]
    have k : ∀ A B : Matrix ι ι S, (f • A + (1 - f) • 1) * J * (f • B + (1 - f) • 1) = f • (A * J * B) + (1 - f) • J :=
      fun A B => by
        conv_lhs => rw [← mix_self f J]
        rw [mix_mul hf, mix_mul hf, one_mul, mul_one]
    rw [k, hg, mix_self]⟩

end Piece

variable {F : Type} [Field F] [NumberField F]

open GlobalTheory.LocalGlobalChar

variable (F) in

abbrev RS (S : Finset (HeightOneSpectrum (𝓞 F))) : Type := Ainf F × ((v : S) → Fv F v.1)

def toRS (S : Finset (HeightOneSpectrum (𝓞 F))) : AF F →ₐ[F] RS F S :=
  (AlgHom.fst F (Ainf F) (Af F)).prod (Pi.algHom F _ fun v : S => (evalV F v.1).comp (AlgHom.snd F (Ainf F) (Af F)))

/- English proof (translation)
Use `Prod.ext rfl (funext fun v => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `evalV F v.1 (ind S) = 1`. Rewrite using `[ev_ind, if_pos v.2]`.
-/
theorem toRS_eps (S : Finset (HeightOneSpectrum (𝓞 F))) : toRS S (eps S) = 1 := by
  refine Prod.ext rfl (funext fun v => ?_)
  change evalV F v.1 (ind S) = 1
  rw [ev_ind, if_pos v.2]

/- English proof (translation)
Establish `h1 : a.1 = 0` using `congrArg Prod.fst h`. Use `Prod.ext ?_ (fin_ext fun u => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `1 * a.1 = 0`. Rewrite using `[h1, mul_zero]`. Express the relevant statement in the definitionally equal form `evalV F u (ind S * a.2) = evalV F u 0`.

Rewrite using `[map_mul, ev_ind, map_zero]`. Use `split_ifs with hu`. Establish `h2 : evalV F u a.2 = 0` using `congrFun (congrArg Prod.snd h) ⟨u, hu⟩`. Rewrite using `[h2, mul_zero]`. Rewrite using `[zero_mul]`.
-/
theorem eps_mul_of (S : Finset (HeightOneSpectrum (𝓞 F))) {a : AF F} (h : toRS S a = 0) : eps S * a = 0 := by
  have h1 : a.1 = 0 := congrArg Prod.fst h
  refine Prod.ext ?_ (fin_ext fun u => ?_)
  · change 1 * a.1 = 0
    rw [h1, mul_zero]
  · change evalV F u (ind S * a.2) = evalV F u 0
    rw [map_mul, ev_ind, map_zero]
    split_ifs with hu
    · have h2 : evalV F u a.2 = 0 := congrFun (congrArg Prod.snd h) ⟨u, hu⟩
      rw [h2, mul_zero]
    · rw [zero_mul]

/- English proof (translation)
Introduce `r`. Set `y : Af F` to `⟨fun u => if h : u ∈ S then r.2 ⟨u, h⟩ else 0, by`. Use `Filter.eventually_cofinite.mpr (S.finite_toSet.subset fun v hv => ?_)` and prove the remaining obligations. Assume the negation of the conclusion as `hvS`. Apply `hv` to reduce the goal to its premises.

Establish `hvS' : v ∉ S` using `fun h => hvS (Finset.mem_coe.mpr h)`. Use `beta_reduce`. Rewrite using `[dif_neg hvS']`. Conclude with `zero_mem (v.adicCompletionIntegers F)⟩`. Use `⟨pairA F r.1 y, Prod.ext rfl (funext fun v => ?_)⟩` and prove the remaining obligations.

Conclude with `dif_pos v.2`.
-/
theorem toRS_surj (S : Finset (HeightOneSpectrum (𝓞 F))) : Function.Surjective (toRS S) := by
  classical
  intro r
  let y : Af F := ⟨fun u => if h : u ∈ S then r.2 ⟨u, h⟩ else 0, by
    refine Filter.eventually_cofinite.mpr (S.finite_toSet.subset fun v hv => ?_)
    by_contra hvS
    apply hv
    have hvS' : v ∉ S := fun h => hvS (Finset.mem_coe.mpr h)
    beta_reduce
    rw [dif_neg hvS']
    exact zero_mem (v.adicCompletionIntegers F)⟩
  refine ⟨pairA F r.1 y, Prod.ext rfl (funext fun v => ?_)⟩
  exact dif_pos v.2

def splitS (S : Finset (HeightOneSpectrum (𝓞 F))) : AF F ≃ₐ[F] RS F S × (AF F ⧸ Ideal.span {eps S}) :=
  AlgEquiv.ofBijective ((toRS S).prod (Ideal.Quotient.mkₐ F _)) ⟨by
    refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
    have h1 : toRS S a = 0 := congrArg Prod.fst ha
    have h2 : Ideal.Quotient.mk (Ideal.span {eps S}) a = 0 := congrArg Prod.snd ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 h2)
    have h3 := eps_mul_of S h1
    rwa [mul_left_comm, eps_mul_self] at h3, by
    rintro ⟨r, q⟩
    obtain ⟨a, rfl⟩ := toRS_surj S r
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
    have h0 : Ideal.Quotient.mk (Ideal.span {eps S}) (eps S) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
    refine ⟨eps S * a + (1 - eps S) * b, Prod.ext ?_ ?_⟩
    · change toRS S _ = toRS S a
      rw [map_add, map_mul, map_mul, map_sub, map_one, toRS_eps]
      ring
    · change Ideal.Quotient.mk (Ideal.span {eps S}) _ = Ideal.Quotient.mk (Ideal.span {eps S}) b
      rw [map_add, map_mul, map_mul, map_sub, map_one, h0]
      ring⟩

/- English proof (translation)
The claim follows from `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)`.
-/
theorem splitS_eps (S : Finset (HeightOneSpectrum (𝓞 F))) : (splitS S (eps S)).2 = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Take `⟨x, hx⟩` from `GlobalTheory.CompanionTheory.Ar.RT.ArchRing.exists_moved hσ`. Establish `hi` using `GlobalTheory.CompanionTheory.Ar.RT.ArchRing.sigma_invol hσ`. Establish `hξ : x - σ x ≠ 0` using `sub_ne_zero.mpr (Ne.symm hx)`. Establish `: Module.Finite F E` using `Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; omega)`. Establish `: IsArtinianRing (Ainf F)` using `GlobalTheory.CompanionTheory.Ar.RT.ArchRing.isArtinian_inf`.

Establish `: IsArtinianRing (RS F S ⊗[F] E)` using `IsArtinianRing.of_finite (RS F S) _`. Use `GlobalTheory.T.hermitian_darboux_split_product F (AF F) (AE F E) (RS F S ⊗[F] E) ((AF F ⧸ Ideal.span {eps S}) ⊗[F] E) (cA σ) (Algebra.TensorProduct.map (AlgHom.id F _) σ) (Algebra.TensorProduct.map (AlgHom.id F _) σ).toRingHom (1 ⊗ₜ[F] (x - σ x)) (split E (splitS S)).toRingEquiv …` and prove the remaining obligations. Use `IsUnit.of_mul_eq_one ((1 : RS F S) ⊗ₜ[F] (x - σ x)⁻¹) ?_` and prove the remaining obligations. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_inv_cancel₀ hξ]`. Both sides reduce to the same expression.

Rewrite using `[Algebra.TensorProduct.map_tmul, map_sub, hi, ← TensorProduct.tmul_neg, neg_sub]`. Both sides reduce to the same expression. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a e => simp [hi]`.

Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`. Take `⟨y, hy⟩` from `hg i j`. Express the relevant statement in the definitionally equal form `(split E (splitS S) ((g.1.1 - 1 : Matrix _ _ (AE F E)) i j)).2 = 0`. Establish `e : algebraMap (AF F) (AE F E) (eps S) = eps S ⊗ₜ[F] (1 : E)` using `rfl`. Rewrite using `[hy, map_mul, Prod.snd_mul, e, split_tmul, splitS_eps, TensorProduct.zero_tmul, zero_mul]`.
-/
theorem triv_piece (hσ : IsCMExt F E σ) {β : Type} [Fintype β] [DecidableEq β] (J : Matrix β β (AE F E)) (hJ : IsUnit J.det)
    (lam : UG (cA σ) (dbl J) →* ℂˣ)
    (h : ∀ (p : UG (cA σ) (dbl J)) (t : GL β (AE F E)), (p.1.1 : Matrix _ _ (AE F E)) * diagCols β = diagCols β * t.1 → lam p = 1)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (g : UG (cA σ) (dbl J))
    (hg : ∀ i j, ∃ y, (g.1.1 - 1 : Matrix _ _ (AE F E)) i j = algebraMap (AF F) (AE F E) (eps S) * y) : lam g = 1 := by
  obtain ⟨x, hx⟩ := GlobalTheory.CompanionTheory.Ar.RT.ArchRing.exists_moved hσ
  have hi := GlobalTheory.CompanionTheory.Ar.RT.ArchRing.sigma_invol hσ
  have hξ : x - σ x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; omega)
  have : IsArtinianRing (Ainf F) := GlobalTheory.CompanionTheory.Ar.RT.ArchRing.isArtinian_inf
  have : IsArtinianRing (RS F S ⊗[F] E) := IsArtinianRing.of_finite (RS F S) _
  refine GlobalTheory.T.hermitian_darboux_split_product F (AF F) (AE F E) (RS F S ⊗[F] E) ((AF F ⧸ Ideal.span {eps S}) ⊗[F] E) (cA σ)
    (Algebra.TensorProduct.map (AlgHom.id F _) σ) (Algebra.TensorProduct.map (AlgHom.id F _) σ).toRingHom
    (1 ⊗ₜ[F] (x - σ x)) (split E (splitS S)).toRingEquiv ?_ ?_ (fun z => ?_)
    (fun z => congrArg Prod.fst (split_conj (splitS S) σ z)) (fun z => congrArg Prod.snd (split_conj (splitS S) σ z))
    β J hJ lam (fun p t _ _ hpt => h p t hpt) g fun i j => ?_
  · refine IsUnit.of_mul_eq_one ((1 : RS F S) ⊗ₜ[F] (x - σ x)⁻¹) ?_
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_inv_cancel₀ hξ]
    rfl
  · rw [Algebra.TensorProduct.map_tmul, map_sub, hi, ← TensorProduct.tmul_neg, neg_sub]
    rfl
  · induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [hi]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  · obtain ⟨y, hy⟩ := hg i j
    change (split E (splitS S) ((g.1.1 - 1 : Matrix _ _ (AE F E)) i j)).2 = 0
    have e : algebraMap (AF F) (AE F E) (eps S) = eps S ⊗ₜ[F] (1 : E) := rfl
    rw [hy, map_mul, Prod.snd_mul, e, split_tmul, splitS_eps, TensorProduct.zero_tmul, zero_mul]

/- English proof (translation)
Establish `: ContinuousAdd (AE F E)` using `IsModuleTopology.toContinuousAdd (AF F) _`. Use `tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_` and prove the remaining obligations. Establish `h` using `(tendsto_eps_tens ((M - 1) i j)).add_const ((1 : Matrix ι ι (AE F E)) i j)`. Rewrite `h` using `[Matrix.sub_apply, sub_add_cancel]`. Use `h.congr fun S => ?_` and prove the remaining obligations.

Simplify using `only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tendsto_mix' {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι (AE F E)) :
    Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 F)) => algebraMap (AF F) (AE F E) (eps S) • M +
      (1 - algebraMap (AF F) (AE F E) (eps S)) • (1 : Matrix ι ι (AE F E))) atTop (𝓝 M) := by
  have : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) _
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  have h := (tendsto_eps_tens ((M - 1) i j)).add_const ((1 : Matrix ι ι (AE F E)) i j)
  rw [Matrix.sub_apply, sub_add_cancel] at h
  refine h.congr fun S => ?_
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

end PositivityTheory.ThKF0.Sg

open PositivityTheory.ThKF0.Sg GlobalTheory.LocalGlobalChar in
/- English proof (translation)
Introduce `F E _ _ _ _ _ σ ι _ _ J₀ g`. Establish `he : ∀ S : Finset (HeightOneSpectrum (𝓞 F)), algebraMap (AF F) (AE F E) (eps S) * algebraMap (AF F) (AE F E) (eps S) = algebraMap (AF F) (AE F E) (eps S)` using `fun S => by rw [← map_mul, eps_mul_self]`. Use `⟨fun S => piece (he S) ((cA σ).commutes _) g, fun S => rfl, ?_⟩` and prove the remaining obligations. Use `(IsEmbedding.subtypeVal.tendsto_nhds_iff).2 ?_` and prove the remaining obligations. Use `(Units.isEmbedding_embedProduct.tendsto_nhds_iff).2 ?_` and prove the remaining obligations.

Conclude with `(tendsto_mix' g.1.1).prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp (tendsto_mix' (g.1⁻¹).1))`.
-/
theorem PositivityTheory.ThKF0.local_global_character_interpolation : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {ι : Type} [Fintype ι] [DecidableEq ι] (J₀ : Matrix ι ι (AE F E)) (g : UG (cA σ) J₀), ∃ q : Finset (HeightOneSpectrum (𝓞 F)) → UG (cA σ) J₀, (∀ S, ((q S).1.1 : Matrix ι ι (AE F E)) = algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S) • (g.1.1 : Matrix ι ι (AE F E)) + (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S)) • (1 : Matrix ι ι (AE F E))) ∧ Tendsto q atTop (𝓝 g) := by
  intro F E _ _ _ _ _ σ ι _ _ J₀ g
  have he : ∀ S : Finset (HeightOneSpectrum (𝓞 F)), algebraMap (AF F) (AE F E) (eps S) * algebraMap (AF F) (AE F E) (eps S) =
      algebraMap (AF F) (AE F E) (eps S) := fun S => by rw [← map_mul, eps_mul_self]
  refine ⟨fun S => piece (he S) ((cA σ).commutes _) g, fun S => rfl, ?_⟩
  refine (IsEmbedding.subtypeVal.tendsto_nhds_iff).2 ?_
  refine (Units.isEmbedding_embedProduct.tendsto_nhds_iff).2 ?_
  exact (tendsto_mix' g.1.1).prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp (tendsto_mix' (g.1⁻¹).1))

open PositivityTheory.ThKF0.Sg GlobalTheory.LocalGlobalChar in
/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ n J ε _ hdet c hc hP`. Establish `hJ : IsUnit (incM F J).det`. Establish `h` using `(isUnit_iff_ne_zero.mpr hdet).map (inclR (F := F) (AF F))`. Rewrite `h` using `[RingHom.map_det]`. Then use the resulting hypothesis. Use `MonoidHom.ext fun g => ?_` and prove the remaining obligations.

Take `⟨q, hq, hlim⟩` from `PositivityTheory.ThKF0.local_global_character_interpolation F E σ (dbl (incM F J)) g`. Establish `h1 : ∀ S, c (q S) = 1` using `fun S => triv_piece hσ _ hJ c hP S (q S) fun i j => ⟨(g.1.1 - 1 : Matrix _ _ (AE F E)) i j, by`. Rewrite using `[hq S]`. Simplify using `only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]`. Use the proof step `ring⟩`.

Establish `h2 : Tendsto (fun S => c (q S)) atTop (𝓝 (c g))` using `(hc.tendsto g).comp hlim`. Simplify using `only [h1] at h2`. Conclude with `(tendsto_nhds_unique tendsto_const_nhds h2).symm`.
-/
theorem PositivityTheory.ThKF0.parabolic_character_trivial_on_diagonal : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (ε : ℤˣ), (∀ i j, σ (J j i) = ((ε : ℤ) : E) * J i j) → J.det ≠ 0 → ∀ c : UG (cA σ) (dbl (incM F J)) →* ℂˣ, Continuous c → (∀ (p : UG (cA σ) (dbl (incM F J))) (t : GL (Fin n) (AE F E)), (p.1.1 : Matrix _ _ (AE F E)) * diagCols (Fin n) = diagCols (Fin n) * t.1 → c p = 1) → c = 1 := by
  intro F E _ _ _ _ _ σ hσ n J ε _ hdet c hc hP
  have hJ : IsUnit (incM F J).det := by
    have h := (isUnit_iff_ne_zero.mpr hdet).map (inclR (F := F) (AF F))
    rwa [RingHom.map_det] at h
  refine MonoidHom.ext fun g => ?_
  obtain ⟨q, hq, hlim⟩ := PositivityTheory.ThKF0.local_global_character_interpolation F E σ (dbl (incM F J)) g
  have h1 : ∀ S, c (q S) = 1 := fun S => triv_piece hσ _ hJ c hP S (q S) fun i j =>
    ⟨(g.1.1 - 1 : Matrix _ _ (AE F E)) i j, by
      rw [hq S]
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      ring⟩
  have h2 : Tendsto (fun S => c (q S)) atTop (𝓝 (c g)) := (hc.tendsto g).comp hlim
  simp only [h1] at h2
  exact (tendsto_nhds_unique tendsto_const_nhds h2).symm

end
