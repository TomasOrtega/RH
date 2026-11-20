import Development.WeilBound.ThetaLifts.LeviDeterminants.LagrangianUniqueness.RealTest
import Development.WeilBound.ThetaLifts.LeviDeterminants.LagrangianUniqueness.Imports
import Development.WeilBound.ThetaLifts.LeviDeterminants.LagrangianUniqueness.LagAlg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.AdelicCharacterRationalDual
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaDistributionHeisenbergInvariantStatement

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.HeisSchA

noncomputable section

namespace PositivityTheory.ThKF0.LineCore

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ}

def q : AF F →+* mixedEmbedding.mixedSpace F := (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp p1

def upI (m : mixedEmbedding.mixedSpace F) : AF F := mk ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm m) 0

/- English proof (translation)
The claim follows from `(InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply m`.
-/
theorem q_upI (m : mixedEmbedding.mixedSpace F) : q (upI m) = m :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply m

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem p2_upI (m : mixedEmbedding.mixedSpace F) : p2 (upI m) = 0 := rfl

/- English proof (translation)
The claim follows from `map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)`.
-/
theorem q_upF (z : Af F) : q (mk 0 z : AF F) = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem p2_upF (z : Af F) : p2 (mk 0 z : AF F) = z := rfl

abbrev tr : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ := Algebra.trace ℝ (mixedEmbedding.mixedSpace F)

/- English proof (translation)
Rewrite using `[map_eq_mul ψ, hψ.2.2 _ (at_mk _)]`. Use `congr 2`. Express the relevant statement in the definitionally equal form `_ * ((tr (q a) : ℝ) : ℂ) = _`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem psi_split (hψ : IsStd ψ) (a : AF F) :
    ψ a = Complex.exp (2 * Real.pi * Complex.I * ((-tr (q a) : ℝ) : ℂ)) * finChar ψ (p2 a) := by
  rw [map_eq_mul ψ, hψ.2.2 _ (at_mk _)]
  congr 2
  change _ * ((tr (q a) : ℝ) : ℂ) = _
  push_cast
  ring

/- English proof (translation)
Introduce `h`. Establish `hn : (Module.finrank ℝ (mixedEmbedding.mixedSpace F) : ℝ) ≠ 0`. Rewrite using `[mixedEmbedding.finrank]`. Conclude with `Nat.cast_ne_zero.2 Module.finrank_pos.ne'`. Establish `h1` using `psi_split hψ (upI (algebraMap ℝ _ (-(1 / 2) / Module.finrank ℝ (mixedEmbedding.mixedSpace F))))`.

Rewrite `h1` using `[q_upI, p2_upI, AddChar.map_zero_eq_one, Algebra.trace_algebraMap, h, nsmul_eq_mul, mul_div_cancel₀ _ hn, show 2 * (Real.pi : ℂ) * Complex.I * ((- -(1 / 2) : ℝ) : ℂ) = Real.pi * Complex.I by push_cast; ring, Complex.exp_pi_mul_I]`. Evaluate the numerical expressions using `at h1`.
-/
theorem ne_one (hψ : IsStd ψ) : ψ ≠ 1 := by
  intro h
  have hn : (Module.finrank ℝ (mixedEmbedding.mixedSpace F) : ℝ) ≠ 0 := by
    rw [mixedEmbedding.finrank]
    exact Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have h1 := psi_split hψ (upI (algebraMap ℝ _ (-(1 / 2) / Module.finrank ℝ (mixedEmbedding.mixedSpace F))))
  rw [q_upI, p2_upI, AddChar.map_zero_eq_one, Algebra.trace_algebraMap, h, nsmul_eq_mul, mul_div_cancel₀ _ hn,
    show 2 * (Real.pi : ℂ) * Complex.I * ((- -(1 / 2) : ℝ) : ℂ) = Real.pi * Complex.I by push_cast; ring,
    Complex.exp_pi_mul_I] at h1
  norm_num at h1

/- English proof (translation)
Establish `h : q (⅟(2 : AF F)) + q (⅟(2 : AF F)) = 1` using `by rw [← map_add, invOf_two_add_invOf_two, map_one]`. Establish `: tr a = tr (q (⅟(2 : AF F)) * a) + tr (q (⅟(2 : AF F)) * a)` using `by rw [← map_add, ← add_mul, h, one_mul]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem tr_half (a : mixedEmbedding.mixedSpace F) : tr (q (⅟(2 : AF F)) * a) = tr a / 2 := by
  have h : q (⅟(2 : AF F)) + q (⅟(2 : AF F)) = 1 := by rw [← map_add, invOf_two_add_invOf_two, map_one]
  have : tr a = tr (q (⅟(2 : AF F)) * a) + tr (q (⅟(2 : AF F)) * a) := by rw [← map_add, ← add_mul, h, one_mul]
  linarith

/- English proof (translation)
Use function extensionality and compare the values at `x`. Establish `h1 : (fun i => q ((x + w.1) i)) = (fun i => q (x i)) + q ∘ w.1` using `funext fun i => map_add q (x i) (w.1 i)`. Establish `h2 : (fun i => p2 ((x + w.1) i)) = (fun i => p2 (x i)) + p2 ∘ w.1` using `funext fun i => map_add p2 (x i) (w.1 i)`. Express the relevant statement in the definitionally equal form `ψ _ * (f (fun i => q ((x + w.1) i)) * g (fun i => p2 ((x + w.1) i))) = (Complex.exp (2 * Real.pi * Complex.I * ((-tr ((q ∘ x) ⬝ᵥ (q ∘ w.2)) + -tr ((q ∘ w.1) ⬝ᵥ (q ∘ w.2)) / 2 : ℝ) : ℂ)) * f ((fun i => q (x i)) + q ∘ w.1)) * (finChar ψ ((p2 ∘ x) ⬝ᵥ (p2 ∘ w.2) + p2 (⅟(2 : AF F)) * …`. Rewrite using `[h1, h2, psi_split hψ]`.

Simplify using `only [map_add, map_mul, RingHom.map_dotProduct, tr_half, neg_add, neg_div]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem schr_pure (hψ : IsStd ψ) (w : (κ → AF F) × (κ → AF F)) (f : (κ → mixedEmbedding.mixedSpace F) → ℂ)
    (g : (κ → Af F) → ℂ) : schr ψ w (pureA F f g) =
    pureA F (fun y => Complex.exp (2 * Real.pi * Complex.I *
        ((-tr (y ⬝ᵥ (q ∘ w.2)) + -tr ((q ∘ w.1) ⬝ᵥ (q ∘ w.2)) / 2 : ℝ) : ℂ)) * f (y + q ∘ w.1))
      (fun z => finChar ψ (z ⬝ᵥ (p2 ∘ w.2) + p2 (⅟(2 : AF F)) * ((p2 ∘ w.1) ⬝ᵥ (p2 ∘ w.2))) * g (z + p2 ∘ w.1)) := by
  funext x
  have h1 : (fun i => q ((x + w.1) i)) = (fun i => q (x i)) + q ∘ w.1 := funext fun i => map_add q (x i) (w.1 i)
  have h2 : (fun i => p2 ((x + w.1) i)) = (fun i => p2 (x i)) + p2 ∘ w.1 := funext fun i => map_add p2 (x i) (w.1 i)
  change ψ _ * (f (fun i => q ((x + w.1) i)) * g (fun i => p2 ((x + w.1) i))) =
    (Complex.exp (2 * Real.pi * Complex.I * ((-tr ((q ∘ x) ⬝ᵥ (q ∘ w.2)) + -tr ((q ∘ w.1) ⬝ᵥ (q ∘ w.2)) / 2 : ℝ) : ℂ)) *
      f ((fun i => q (x i)) + q ∘ w.1)) *
    (finChar ψ ((p2 ∘ x) ⬝ᵥ (p2 ∘ w.2) + p2 (⅟(2 : AF F)) * ((p2 ∘ w.1) ⬝ᵥ (p2 ∘ w.2))) * g ((fun i => p2 (x i)) + p2 ∘ w.1))
  rw [h1, h2, psi_split hψ]
  simp only [map_add, map_mul, RingHom.map_dotProduct, tr_half, neg_add, neg_div]
  ring

/- English proof (translation)
Take `⟨b, rfl⟩` from `(GlobalTheory.T.adelic_character_rational_dual F ψ hψ.1 (ne_one hψ) hψ.2.1).2 x h`. Establish `: b = 0`. Break down `hx with hx | hx` into its components or cases. Conclude with `(map_eq_zero_iff (q.comp (algebraMap F (AF F))) (RingHom.injective _)).1 hx`. Take `⟨p, hp0, hp⟩` from `Ring.not_isField_iff_exists_prime.1 (RingOfIntegers.not_isField F) haveI : Nontrivial (Af F) := (evalV F ⟨p, hp, hp0⟩).domain_nontrivial`.

Conclude with `(map_eq_zero_iff (p2.comp (algebraMap F (AF F))) (RingHom.injective _)).1 hx`. Rewrite using `[this, map_zero]`.
-/
theorem nondeg (hψ : IsStd ψ) (x : AF F) (hx : q x = 0 ∨ p2 x = 0)
    (h : ∀ a : F, ψ (x * algebraMap F (AF F) a) = 1) : x = 0 := by
  obtain ⟨b, rfl⟩ := (GlobalTheory.T.adelic_character_rational_dual F ψ hψ.1 (ne_one hψ) hψ.2.1).2 x h
  have : b = 0 := by
    rcases hx with hx | hx
    · exact (map_eq_zero_iff (q.comp (algebraMap F (AF F))) (RingHom.injective _)).1 hx
    · obtain ⟨p, hp0, hp⟩ := Ring.not_isField_iff_exists_prime.1 (RingOfIntegers.not_isField F)
      haveI : Nontrivial (Af F) := (evalV F ⟨p, hp, hp0⟩).domain_nontrivial
      exact (map_eq_zero_iff (p2.comp (algebraMap F (AF F))) (RingHom.injective _)).1 hx
  rw [this, map_zero]

/- English proof (translation)
Set `B : LinearMap.BilinForm ℝ (κ → mixedEmbedding.mixedSpace F)` to `LinearMap.mk₂ ℝ (fun y x => -tr (x ⬝ᵥ y)) (fun _ _ _ => by rw [dotProduct_add, map_add, neg_add]) (fun _ _ _ => by rw [dotProduct_smul, map_smul, smul_neg]) (fun _ _ _ => by rw [add_dotProduct, map_add, neg_add]) (fun _ _ _ => by rw [smul_dotProduct, map_smul, smul_neg])`. Establish `hinj : Function.Injective (B : _ →ₗ[ℝ] Module.Dual ℝ _)`. Use `(injective_iff_map_eq_zero _).2 fun y hy => funext fun i => ?_` and prove the remaining obligations. Establish `h0 : upI (y i) = 0` using `nondeg hψ _ (Or.inr rfl) fun a => by`. Use `LinearMap.congr_fun hy (Pi.single i (q (algebraMap F (AF F) a)))` as an intermediate fact.

Express the relevant statement in the definitionally equal form `-tr _ = 0 at this`. Rewrite `this` using `[single_dotProduct, mul_comm]`. Rewrite using `[psi_split hψ, map_mul q, map_mul p2, q_upI, p2_upI, this]`. Simplify using the standard rewrite rules. Rewrite using `[← q_upI (y i), h0, map_zero, Pi.zero_apply]`.

Take `⟨y, hy⟩` from `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank Subspace.dual_finrank_eq.symm).1 hinj l`. Conclude with `⟨y, fun x => by rw [← hy]; rfl⟩`.
-/
theorem exists_tr (hψ : IsStd ψ) (l : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ) : ∃ y, ∀ x, l x = -tr (x ⬝ᵥ y) := by
  let B : LinearMap.BilinForm ℝ (κ → mixedEmbedding.mixedSpace F) :=
    LinearMap.mk₂ ℝ (fun y x => -tr (x ⬝ᵥ y))
      (fun _ _ _ => by rw [dotProduct_add, map_add, neg_add]) (fun _ _ _ => by rw [dotProduct_smul, map_smul, smul_neg])
      (fun _ _ _ => by rw [add_dotProduct, map_add, neg_add]) (fun _ _ _ => by rw [smul_dotProduct, map_smul, smul_neg])
  have hinj : Function.Injective (B : _ →ₗ[ℝ] Module.Dual ℝ _) := by
    refine (injective_iff_map_eq_zero _).2 fun y hy => funext fun i => ?_
    have h0 : upI (y i) = 0 := nondeg hψ _ (Or.inr rfl) fun a => by
      have := LinearMap.congr_fun hy (Pi.single i (q (algebraMap F (AF F) a)))
      change -tr _ = 0 at this
      rw [single_dotProduct, mul_comm] at this
      rw [psi_split hψ, map_mul q, map_mul p2, q_upI, p2_upI, this]
      simp
    rw [← q_upI (y i), h0, map_zero, Pi.zero_apply]
  obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank Subspace.dual_finrank_eq.symm).1 hinj l
  exact ⟨y, fun x => by rw [← hy]; rfl⟩

/- English proof (translation)
The claim follows from `funext fun i => RingHom.map_mulVec f A x i`.
-/
theorem comp_mulVec {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (A : Matrix κ κ R) (x : κ → R) :
    f ∘ (A *ᵥ x) = A.map f *ᵥ (f ∘ x) := funext fun i => RingHom.map_mulVec f A x i

variable {P b : Matrix κ κ (AF F)}

/- English proof (translation)
Establish `hsym : ∀ {S : Type} [CommRing S] (f : AF F →+* S) (x y : κ → S), x ⬝ᵥ b.map f *ᵥ y = y ⬝ᵥ b.map f *ᵥ x`. Introduce `S _ f x y`. Rewrite using `[dotProduct_mulVec, ← mulVec_transpose, ← transpose_map, hb, dotProduct_comm]`. Set `Pi' : Submodule ℝ (κ → mixedEmbedding.mixedSpace F)` to `{ carrier := {p | P.map q *ᵥ p = p} zero_mem' := mulVec_zero _ add_mem' := fun {x y} hx hy => by`. Express the relevant statement in the definitionally equal form `_ = _ at hx hy ⊢`.

Rewrite using `[mulVec_add, hx, hy]`. Use the proof step `smul_mem' := fun r x hx => by`. Express the relevant statement in the definitionally equal form `_ = _ at hx ⊢`. Rewrite using `[mulVec_smul, hx] }`. Set `bi : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ` to `LinearMap.mk₂ ℝ (fun x y => -tr (x ⬝ᵥ b.map q *ᵥ y)) (fun _ _ _ => by rw [add_dotProduct, map_add, neg_add]) (fun _ _ _ => by rw [smul_dotProduct, map_smul, smul_neg]) (fun _ _ _ => by rw [mulVec_add, dotProduct_add, map_add, neg_add]) (fun _ _ _ => by rw [mulVec_smul, dotProduct …`.

Take `⟨f₀, hf₀⟩` from `hR _ Pi' bi fun x y => congrArg (fun t => -tr t) (hsym q x y)`. Use `haveI := nonarch_finiteAdeleRing (F := F)`. Use `haveI : NonarchimedeanAddGroup (κ → Af F) := nonarch_pi`. Set `U₀ : OpenAddSubgroup (κ → Af F)` to `⟨GlobalTheory.CompanionTheory.ThetaUniq.levelSub F κ 1, GlobalTheory.CompanionTheory.ThetaUniq.levelSub_isOpen F κ one_pos⟩`. Establish `hU₀ : IsCompact (U₀ : Set (κ → Af F))` using `GlobalTheory.CompanionTheory.ThetaUniq.levelSub_isCompact F κ 1`.

Set `h : Af F` to `p2 (⅟(2 : AF F))`. Establish `hh : h + h = 1` using `by rw [← map_add, invOf_two_add_invOf_two, map_one]`. Set `Q : (κ → Af F) → Af F` to `fun z => h * (z ⬝ᵥ b.map p2 *ᵥ z)`. Establish `hQ : Continuous Q` using `continuous_const.mul (continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id))`. Establish `hlc` using `finChar_isLocallyConstant ψ hψ.1`.

Establish `hmul : ∀ χ : (κ → Af F) → ℂ, IsLocallyConstant χ → ∀ g ∈ SB (κ → Af F), (fun z => χ z * g z) ∈ SB (κ → Af F)` using `fun χ hχ g hg => ⟨hχ.mul hg.1, hg.2.mul_left⟩`. Establish `hc : ∀ g ∈ SB (κ → Af F), (fun z => finChar ψ (-Q z) * g z) ∈ SB (κ → Af F)` using `hmul _ (hlc.comp_continuous hQ.neg)`. Establish `hmem : ∀ (f : SInf F κ), ∀ g ∈ SB (κ → Af F), pureA F f g ∈ schA F κ` using `fun f g hg => Submodule.subset_span ⟨f, g, hg, rfl⟩`. Use `⟨_, hmem f₀ _ (hc _ (FinLine.ind_mem hU₀ le_rfl 0)), fun l hl h1 h2 h0 => ?_⟩` and prove the remaining obligations. Set `m : ((κ → Af F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)` to `{ toFun := fun g => pureA F f₀ fun z => finChar ψ (-Q z) * g z map_add' := fun g g' => funext fun x => by simp only [pureA, Pi.add_apply]; ring map_smul' := fun a g => funext fun x => by`.

Simplify using `only [pureA, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]`. Use `ring }`. Establish `hm : ∀ g, m g = pureA F f₀ fun z => finChar ψ (-Q z) * g z` using `fun _ => rfl`. Establish `hF : ∀ g ∈ SB (κ → Af F), (l ∘ₗ m) g = 0` using `fun g hg => by`. Use `FinLine.test hU₀ (P := {p | P.map p2 *ᵥ p = p}) (mulVec_zero _) (fun p hp φ hφ => ?_) (fun a ha => ?_) h0 hg` and prove the remaining obligations.

Establish `hp : P.map p2 *ᵥ p = p` using `hp`. Establish `e1 : (q (F` using `F)) ∘ (fun i => mk 0 (p i)) = 0 := funext fun i => q_upF _`. Establish `e2 : (p2 (F` using `F)) ∘ (fun i => mk 0 (p i)) = p := rfl`. Use `Eq.trans (congrArg l (Eq.trans ?_ (schr_pure hψ _ _ _).symm)) (h1 (fun i => mk 0 (p i)) _ (hmem f₀ _ (hc φ hφ)))` and prove the remaining obligations. Simplify using `only [comp_mulVec, e1, e2, Matrix.map_mul, ← mulVec_mulVec, hp, mulVec_zero, dotProduct_zero, map_zero]`.

Rewrite using `[hm]`. Use `congr 1`. Use function extensionality and compare the values at `y`. Simplify using the standard rewrite rules. Use function extensionality and compare the values at `z`.

Rewrite using `[← mul_assoc, ← AddChar.map_add_eq_mul]`. Use `congr 2`. Simplify using `only [Q, mulVec_add, add_dotProduct, dotProduct_add, hsym p2 p z]`. Take the linear combination `(z ⬝ᵥ b.map p2 *ᵥ p) * hh`. Establish `h3 : (1 - P).map p2 *ᵥ a ≠ 0` using `fun h3 => ha (by`.

Rewrite `h3` using `[Matrix.map_sub _ (map_sub p2), Matrix.map_one _ (map_zero p2) (map_one p2), sub_mulVec, one_mulVec, sub_eq_zero]`. Conclude with `h3.symm)`. Take `⟨i, hi⟩` from `Function.ne_iff.1 h3`. Choose the witnesses or unpack the hypotheses as in `⟨t, ht⟩ : ∃ t : F, ψ (mk 0 (((1 - P).map p2 *ᵥ a) i) * algebraMap F (AF F) t) ≠ 1 := by`. Assume the negation of the conclusion as `hcon`.

Use `push Not at hcon`. Conclude with `hi (congrArg p2 (nondeg hψ _ (Or.inl (q_upF _)) hcon))`. Set `y : κ → Af F` to `Pi.single i (p2 (algebraMap F (AF F) t))`. Use `⟨fun z => finChar ψ (z ⬝ᵥ ((1 - P)ᵀ).map p2 *ᵥ y), hlc.comp_continuous (continuous_id.dotProduct continuous_const), ?_, fun φ hφ => ?_⟩` and prove the remaining obligations. Rewrite `ht`, `beta_reduce` using `[psi_split hψ, map_mul q, q_upF, map_mul p2, p2_upF]`.

Rewrite using `[dotProduct_mulVec, transpose_map, vecMul_transpose, dotProduct_single]`. Simplify using `using ht`. Establish `e1 : (q (F` using `F)) ∘ (fun i => mk 0 (y i)) = 0 := funext fun i => q_upF _`. Establish `e2 : (p2 (F` using `F)) ∘ (fun i => mk 0 (y i)) = y := rfl`. Establish `e3 : (q (F` using `F)) ∘ (0 : κ → AF F) = 0 := funext fun i => map_zero _`.

Establish `e4 : (p2 (F` using `F)) ∘ (0 : κ → AF F) = 0 := funext fun i => map_zero _`. Use `Eq.trans (congrArg l (Eq.trans ?_ (schr_pure hψ _ _ _).symm)) (h2 (fun i => mk 0 (y i)) _ (hmem f₀ _ (hc φ hφ)))` and prove the remaining obligations. Simplify using `only [comp_mulVec, e1, e2, e3, e4, mulVec_zero, dotProduct_zero, map_zero, zero_dotProduct, add_zero, mul_zero]`. Rewrite using `[hm]`. Use `congr 1`.

Use function extensionality and compare the values at `y`. Simplify using the standard rewrite rules. Use function extensionality and compare the values at `z`. Expand and normalize the polynomial expressions, which then agree. Establish `hF' : ∀ g ∈ SB (κ → Af F), l (pureA F f₀ g) = 0` using `fun g hg => by`.

Rewrite using `[← hF _ (hmul _ (hlc.comp_continuous hQ) g hg), LinearMap.comp_apply, hm]`. Use `congrArg (fun t => l (pureA F f₀ t)) (funext fun z => ?_)` and prove the remaining obligations. Rewrite using `[← mul_assoc, Function.comp_apply, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]`. Establish `hI : ∀ (f : SInf F κ), ∀ g ∈ SB (κ → Af F), l (pureA F f g) = 0` using `fun f g hg => by`. Take `⟨T, hT⟩` from `hl g hg`.

Establish `e3 : (q (F` using `F)) ∘ (0 : κ → AF F) = 0 := funext fun i => map_zero _`. Establish `e4 : (p2 (F` using `F)) ∘ (0 : κ → AF F) = 0 := funext fun i => map_zero _`. Establish `e1 : ∀ p : κ → mixedEmbedding.mixedSpace F, (q (F` using `F)) ∘ (fun i => upI (p i)) = p := fun p => funext fun i => q_upI _`. Establish `e2 : ∀ p : κ → mixedEmbedding.mixedSpace F, (p2 (F` using `F)) ∘ (fun i => upI (p i)) = 0 := fun p => rfl`. Rewrite using `[hT, hf₀ T (fun p hp f f' hf => ?_) (fun lam hlam f f' hf => ?_) (by rw [← hT, hF' g hg])]`.

Both sides reduce to the same expression. Establish `hp : P.map q *ᵥ p = p` using `hp`. Rewrite using `[← hT, ← hT]`. Use `Eq.trans (congrArg l ?_) (h1 (fun i => upI (p i)) _ (hmem f _ hg))` and prove the remaining obligations. Rewrite using `[schr_pure hψ]`.

Simplify using `only [comp_mulVec, e1, e2, Matrix.map_mul, ← mulVec_mulVec, hp, mulVec_zero, dotProduct_zero, map_zero]`. Use `congr 1`. Conclude with `funext hf`. Use function extensionality and compare the values at `z`. Simplify using the standard rewrite rules.

Take `⟨y, hy⟩` from `exists_tr hψ lam`. Establish `hy' : ∀ x, lam x = -tr (x ⬝ᵥ ((1 - P)ᵀ).map q *ᵥ y)` using `fun x => by`. Establish `: lam (P.map q *ᵥ x) = 0` using `hlam _ (by`. Express the relevant statement in the definitionally equal form `_ = _`. Rewrite using `[mulVec_mulVec, ← Matrix.map_mul, hP])`.

Rewrite using `[dotProduct_mulVec, transpose_map, vecMul_transpose, ← hy, Matrix.map_sub _ (map_sub q), Matrix.map_one _ (map_zero q) (map_one q), sub_mulVec, one_mulVec, map_sub, this, sub_zero]`. Rewrite using `[← hT, ← hT]`. Use `Eq.trans (congrArg l ?_) (h2 (fun i => upI (y i)) _ (hmem f _ hg))` and prove the remaining obligations. Rewrite using `[schr_pure hψ]`. Simplify using `only [comp_mulVec, e1, e2, e3, e4, mulVec_zero, dotProduct_zero, map_zero, zero_dotProduct, add_zero, mul_zero, neg_zero, zero_div, ← hy']`.

Use `congr 1`. Conclude with `funext hf`. Use function extensionality and compare the values at `z`. Simplify using the standard rewrite rules. Introduce `φ hφ`.

Establish `: schA F κ ≤ LinearMap.ker l` using `Submodule.span_le.2 (by rintro _ ⟨f, g, hg, rfl⟩; exact hI f g hg)`. Conclude with `this hφ`.
-/
theorem test (hR : RealTest) (hψ : IsStd ψ) (hP : P * P = P) (hb : bᵀ = b) :
    ∃ Φ₀ ∈ schA F κ, ∀ l ∈ (adeleClass F).adm κ,
      (∀ x, ∀ φ ∈ schA F κ, l (schr ψ (P *ᵥ x, (b * P) *ᵥ x) φ) = l φ) →
      (∀ y, ∀ φ ∈ schA F κ, l (schr ψ (0, (1 - P)ᵀ *ᵥ y) φ) = l φ) → l Φ₀ = 0 → ∀ φ ∈ schA F κ, l φ = 0 := by
  have hsym : ∀ {S : Type} [CommRing S] (f : AF F →+* S) (x y : κ → S), x ⬝ᵥ b.map f *ᵥ y = y ⬝ᵥ b.map f *ᵥ x := by
    intro S _ f x y
    rw [dotProduct_mulVec, ← mulVec_transpose, ← transpose_map, hb, dotProduct_comm]
  let Pi' : Submodule ℝ (κ → mixedEmbedding.mixedSpace F) :=
    { carrier := {p | P.map q *ᵥ p = p}
      zero_mem' := mulVec_zero _
      add_mem' := fun {x y} hx hy => by
        change _ = _ at hx hy ⊢
        rw [mulVec_add, hx, hy]
      smul_mem' := fun r x hx => by
        change _ = _ at hx ⊢
        rw [mulVec_smul, hx] }
  let bi : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun x y => -tr (x ⬝ᵥ b.map q *ᵥ y))
      (fun _ _ _ => by rw [add_dotProduct, map_add, neg_add]) (fun _ _ _ => by rw [smul_dotProduct, map_smul, smul_neg])
      (fun _ _ _ => by rw [mulVec_add, dotProduct_add, map_add, neg_add])
      (fun _ _ _ => by rw [mulVec_smul, dotProduct_smul, map_smul, smul_neg])
  obtain ⟨f₀, hf₀⟩ := hR _ Pi' bi fun x y => congrArg (fun t => -tr t) (hsym q x y)
  haveI := nonarch_finiteAdeleRing (F := F)
  haveI : NonarchimedeanAddGroup (κ → Af F) := nonarch_pi
  let U₀ : OpenAddSubgroup (κ → Af F) :=
    ⟨GlobalTheory.CompanionTheory.ThetaUniq.levelSub F κ 1, GlobalTheory.CompanionTheory.ThetaUniq.levelSub_isOpen F κ one_pos⟩
  have hU₀ : IsCompact (U₀ : Set (κ → Af F)) := GlobalTheory.CompanionTheory.ThetaUniq.levelSub_isCompact F κ 1
  let h : Af F := p2 (⅟(2 : AF F))
  have hh : h + h = 1 := by rw [← map_add, invOf_two_add_invOf_two, map_one]
  let Q : (κ → Af F) → Af F := fun z => h * (z ⬝ᵥ b.map p2 *ᵥ z)
  have hQ : Continuous Q := continuous_const.mul (continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id))
  have hlc := finChar_isLocallyConstant ψ hψ.1
  have hmul : ∀ χ : (κ → Af F) → ℂ, IsLocallyConstant χ → ∀ g ∈ SB (κ → Af F), (fun z => χ z * g z) ∈ SB (κ → Af F) :=
    fun χ hχ g hg => ⟨hχ.mul hg.1, hg.2.mul_left⟩
  have hc : ∀ g ∈ SB (κ → Af F), (fun z => finChar ψ (-Q z) * g z) ∈ SB (κ → Af F) :=
    hmul _ (hlc.comp_continuous hQ.neg)
  have hmem : ∀ (f : SInf F κ), ∀ g ∈ SB (κ → Af F), pureA F f g ∈ schA F κ :=
    fun f g hg => Submodule.subset_span ⟨f, g, hg, rfl⟩
  refine ⟨_, hmem f₀ _ (hc _ (FinLine.ind_mem hU₀ le_rfl 0)), fun l hl h1 h2 h0 => ?_⟩
  let m : ((κ → Af F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) :=
    { toFun := fun g => pureA F f₀ fun z => finChar ψ (-Q z) * g z
      map_add' := fun g g' => funext fun x => by simp only [pureA, Pi.add_apply]; ring
      map_smul' := fun a g => funext fun x => by
        simp only [pureA, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  have hm : ∀ g, m g = pureA F f₀ fun z => finChar ψ (-Q z) * g z := fun _ => rfl
  have hF : ∀ g ∈ SB (κ → Af F), (l ∘ₗ m) g = 0 := fun g hg => by
    refine FinLine.test hU₀ (P := {p | P.map p2 *ᵥ p = p}) (mulVec_zero _) (fun p hp φ hφ => ?_) (fun a ha => ?_) h0 hg
    · have hp : P.map p2 *ᵥ p = p := hp
      have e1 : (q (F := F)) ∘ (fun i => mk 0 (p i)) = 0 := funext fun i => q_upF _
      have e2 : (p2 (F := F)) ∘ (fun i => mk 0 (p i)) = p := rfl
      refine Eq.trans (congrArg l (Eq.trans ?_ (schr_pure hψ _ _ _).symm)) (h1 (fun i => mk 0 (p i)) _ (hmem f₀ _ (hc φ hφ)))
      simp only [comp_mulVec, e1, e2, Matrix.map_mul, ← mulVec_mulVec, hp, mulVec_zero, dotProduct_zero, map_zero]
      rw [hm]
      congr 1
      · funext y; simp
      · funext z
        rw [← mul_assoc, ← AddChar.map_add_eq_mul]
        congr 2
        simp only [Q, mulVec_add, add_dotProduct, dotProduct_add, hsym p2 p z]
        linear_combination (z ⬝ᵥ b.map p2 *ᵥ p) * hh
    · have h3 : (1 - P).map p2 *ᵥ a ≠ 0 := fun h3 => ha (by
        rw [Matrix.map_sub _ (map_sub p2), Matrix.map_one _ (map_zero p2) (map_one p2), sub_mulVec, one_mulVec,
          sub_eq_zero] at h3
        exact h3.symm)
      obtain ⟨i, hi⟩ := Function.ne_iff.1 h3
      obtain ⟨t, ht⟩ : ∃ t : F, ψ (mk 0 (((1 - P).map p2 *ᵥ a) i) * algebraMap F (AF F) t) ≠ 1 := by
        by_contra hcon
        push Not at hcon
        exact hi (congrArg p2 (nondeg hψ _ (Or.inl (q_upF _)) hcon))
      let y : κ → Af F := Pi.single i (p2 (algebraMap F (AF F) t))
      refine ⟨fun z => finChar ψ (z ⬝ᵥ ((1 - P)ᵀ).map p2 *ᵥ y),
        hlc.comp_continuous (continuous_id.dotProduct continuous_const), ?_, fun φ hφ => ?_⟩
      · rw [psi_split hψ, map_mul q, q_upF, map_mul p2, p2_upF] at ht
        beta_reduce
        rw [dotProduct_mulVec, transpose_map, vecMul_transpose, dotProduct_single]
        simpa using ht
      · have e1 : (q (F := F)) ∘ (fun i => mk 0 (y i)) = 0 := funext fun i => q_upF _
        have e2 : (p2 (F := F)) ∘ (fun i => mk 0 (y i)) = y := rfl
        have e3 : (q (F := F)) ∘ (0 : κ → AF F) = 0 := funext fun i => map_zero _
        have e4 : (p2 (F := F)) ∘ (0 : κ → AF F) = 0 := funext fun i => map_zero _
        refine Eq.trans (congrArg l (Eq.trans ?_ (schr_pure hψ _ _ _).symm)) (h2 (fun i => mk 0 (y i)) _ (hmem f₀ _ (hc φ hφ)))
        simp only [comp_mulVec, e1, e2, e3, e4, mulVec_zero, dotProduct_zero, map_zero, zero_dotProduct, add_zero, mul_zero]
        rw [hm]
        congr 1
        · funext y; simp
        · funext z; ring
  have hF' : ∀ g ∈ SB (κ → Af F), l (pureA F f₀ g) = 0 := fun g hg => by
    rw [← hF _ (hmul _ (hlc.comp_continuous hQ) g hg), LinearMap.comp_apply, hm]
    refine congrArg (fun t => l (pureA F f₀ t)) (funext fun z => ?_)
    rw [← mul_assoc, Function.comp_apply, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]
  have hI : ∀ (f : SInf F κ), ∀ g ∈ SB (κ → Af F), l (pureA F f g) = 0 := fun f g hg => by
    obtain ⟨T, hT⟩ := hl g hg
    have e3 : (q (F := F)) ∘ (0 : κ → AF F) = 0 := funext fun i => map_zero _
    have e4 : (p2 (F := F)) ∘ (0 : κ → AF F) = 0 := funext fun i => map_zero _
    have e1 : ∀ p : κ → mixedEmbedding.mixedSpace F, (q (F := F)) ∘ (fun i => upI (p i)) = p :=
      fun p => funext fun i => q_upI _
    have e2 : ∀ p : κ → mixedEmbedding.mixedSpace F, (p2 (F := F)) ∘ (fun i => upI (p i)) = 0 := fun p => rfl
    rw [hT, hf₀ T (fun p hp f f' hf => ?_) (fun lam hlam f f' hf => ?_) (by rw [← hT, hF' g hg])]
    · rfl
    · have hp : P.map q *ᵥ p = p := hp
      rw [← hT, ← hT]
      refine Eq.trans (congrArg l ?_) (h1 (fun i => upI (p i)) _ (hmem f _ hg))
      rw [schr_pure hψ]
      simp only [comp_mulVec, e1, e2, Matrix.map_mul, ← mulVec_mulVec, hp, mulVec_zero, dotProduct_zero, map_zero]
      congr 1
      · exact funext hf
      · funext z; simp
    · obtain ⟨y, hy⟩ := exists_tr hψ lam
      have hy' : ∀ x, lam x = -tr (x ⬝ᵥ ((1 - P)ᵀ).map q *ᵥ y) := fun x => by
        have : lam (P.map q *ᵥ x) = 0 := hlam _ (by
          change _ = _
          rw [mulVec_mulVec, ← Matrix.map_mul, hP])
        rw [dotProduct_mulVec, transpose_map, vecMul_transpose, ← hy, Matrix.map_sub _ (map_sub q),
          Matrix.map_one _ (map_zero q) (map_one q), sub_mulVec, one_mulVec, map_sub, this, sub_zero]
      rw [← hT, ← hT]
      refine Eq.trans (congrArg l ?_) (h2 (fun i => upI (y i)) _ (hmem f _ hg))
      rw [schr_pure hψ]
      simp only [comp_mulVec, e1, e2, e3, e4, mulVec_zero, dotProduct_zero, map_zero, zero_dotProduct, add_zero, mul_zero,
        neg_zero, zero_div, ← hy']
      congr 1
      · exact funext hf
      · funext z; simp
  intro φ hφ
  have : schA F κ ≤ LinearMap.ker l := Submodule.span_le.2 (by rintro _ ⟨f, g, hg, rfl⟩; exact hI f g hg)
  exact this hφ

/- English proof (translation)
Introduce `F _ _ ψ hψ κ _ L hL l₁ h₁ l₂ h₂ i₁ i₂ ⟨φ₂, hφ₂, hne⟩`. Take `⟨P, b, hP, hb, hA, hB⟩` from `LagAlg.exists_mats L hL`. Take `⟨Φ₀, hΦ₀, hT⟩` from `test (κ := κ) (P := P.map (algebraMap F (AF F))) (b := b.map (algebraMap F (AF F))) hR hψ (by rw [← Matrix.map_mul, hP]) (by rw [← transpose_map, hb])`. Establish `key : ∀ l ∈ (adeleClass F).adm κ, (∀ (t : AF F), ∀ w ∈ L, ∀ φ ∈ schA F κ, l (schr ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ) = l φ) → l Φ₀ = 0 → ∀ φ ∈ schA F κ, l φ = 0` using `fun l hl hi => by`. Establish `h` using `LagAlg.inv_of_mem ψ (schA F κ) (schr_mem_schA ψ hψ) l L (fun a ha => (hL a).1 ha) hi`.

Use `hT l hl (fun x => ?_) fun y => ?_` and prove the remaining obligations. Use `h _ _ hA x` as an intermediate fact. Rewrite `this` using `[Matrix.map_mul]`. Then use the resulting hypothesis. Use `h _ _ hB y` as an intermediate fact. Rewrite `this` using `[Matrix.map_zero _ (map_zero _), zero_mulVec, transpose_map, Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]`. Then use the resulting hypothesis.

Establish `h0 : l₂ Φ₀ ≠ 0` using `fun h => hne (key l₂ h₂ i₂ h φ₂ hφ₂)`. Use `⟨l₁ Φ₀ / l₂ Φ₀, fun φ hφ => sub_eq_zero.1 (key (l₁ - (l₁ Φ₀ / l₂ Φ₀) • l₂) (fun g hg => ?_) (fun t w hw φ hφ => ?_) ?_ φ hφ)⟩` and prove the remaining obligations. Take `⟨T₁, e₁⟩` from `h₁ g hg`. Take `⟨T₂, e₂⟩` from `h₂ g hg`. Conclude with `⟨T₁ - (l₁ Φ₀ / l₂ Φ₀) • T₂, fun f => by simp [e₁, e₂]⟩`.

Simplify using `only [LinearMap.sub_apply, LinearMap.smul_apply, i₁ t w hw φ hφ, i₂ t w hw φ hφ]`. Simplify using `[h0]`.
-/
theorem lagLine_of (hR : RealTest) : LagLine := by
  intro F _ _ ψ hψ κ _ L hL l₁ h₁ l₂ h₂ i₁ i₂ ⟨φ₂, hφ₂, hne⟩
  obtain ⟨P, b, hP, hb, hA, hB⟩ := LagAlg.exists_mats L hL
  obtain ⟨Φ₀, hΦ₀, hT⟩ := test (κ := κ) (P := P.map (algebraMap F (AF F))) (b := b.map (algebraMap F (AF F))) hR hψ
    (by rw [← Matrix.map_mul, hP]) (by rw [← transpose_map, hb])
  have key : ∀ l ∈ (adeleClass F).adm κ, (∀ (t : AF F), ∀ w ∈ L, ∀ φ ∈ schA F κ,
      l (schr ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ) = l φ) →
      l Φ₀ = 0 → ∀ φ ∈ schA F κ, l φ = 0 := fun l hl hi => by
    have h := LagAlg.inv_of_mem ψ (schA F κ) (schr_mem_schA ψ hψ) l L (fun a ha => (hL a).1 ha) hi
    refine hT l hl (fun x => ?_) fun y => ?_
    · have := h _ _ hA x
      rwa [Matrix.map_mul] at this
    · have := h _ _ hB y
      rwa [Matrix.map_zero _ (map_zero _), zero_mulVec, transpose_map, Matrix.map_sub _ (map_sub _),
        Matrix.map_one _ (map_zero _) (map_one _)] at this
  have h0 : l₂ Φ₀ ≠ 0 := fun h => hne (key l₂ h₂ i₂ h φ₂ hφ₂)
  refine ⟨l₁ Φ₀ / l₂ Φ₀, fun φ hφ => sub_eq_zero.1 (key (l₁ - (l₁ Φ₀ / l₂ Φ₀) • l₂) (fun g hg => ?_)
    (fun t w hw φ hφ => ?_) ?_ φ hφ)⟩
  · obtain ⟨T₁, e₁⟩ := h₁ g hg
    obtain ⟨T₂, e₂⟩ := h₂ g hg
    exact ⟨T₁ - (l₁ Φ₀ / l₂ Φ₀) • T₂, fun f => by simp [e₁, e₂]⟩
  · simp only [LinearMap.sub_apply, LinearMap.smul_apply, i₁ t w hw φ hφ, i₂ t w hw φ hφ]
  · simp [h0]

end PositivityTheory.ThKF0.LineCore
