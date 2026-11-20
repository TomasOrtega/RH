import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagLevelCharacterEqPsiDivN
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicHatMulOfMulClosed
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GramFrame

section Gen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.AdelicLatticeClosure.adelic_hat_one_mul_mem`. Consider the case `exact _root_.GlobalTheory.AdelicLatticeClosure.adelic_hat_one_mul_mem`. Consider the case `(apply _root_.GlobalTheory.AdelicLatticeClosure.adelic_hat_one_mul_mem <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.AdelicLatticeClosure.adelic_hat_one_mul_mem <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.AdelicLatticeClosure.adelic_hat_one_mul_mem <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.AdelicLatticeClosure.adelic_hat_one_mul_mem ..)`.
-/
theorem integral_adelic_lattice_mul_mem {z w : GlobalTheory.AdLat.RA F E}
    (hz : z ∈ GlobalTheory.AdLat.hat1 F ((1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E))
    (hw : w ∈ GlobalTheory.AdLat.hat1 F ((1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E)) :
    z * w ∈ GlobalTheory.AdLat.hat1 F ((1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E) := by
  first
  | exact @_root_.GlobalTheory.AdelicLatticeClosure.adelic_hat_one_mul_mem
  | exact _root_.GlobalTheory.AdelicLatticeClosure.adelic_hat_one_mul_mem
  | (apply _root_.GlobalTheory.AdelicLatticeClosure.adelic_hat_one_mul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.AdelicLatticeClosure.adelic_hat_one_mul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AdelicLatticeClosure.adelic_hat_one_mul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AdelicLatticeClosure.adelic_hat_one_mul_mem ..)

/- English proof (translation)
Introduce `v` and use `by show (1 : v.adicCompletion F) ∈ _ exact one_mem _`.
-/
theorem one_int_af : ∀ v : HeightOneSpectrum (𝓞 F),
    (1 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F := fun v => by
  show (1 : v.adicCompletion F) ∈ _
  exact one_mem _

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hz`. Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨a, ha, x, hx, rfl⟩` from `hz`.

Take `⟨x', rfl⟩` from `(FractionalIdeal.mem_one_iff _).1 hx`. Rewrite using `[GlobalTheory.LevSplit.swp_tmul]`. Establish `e : (algebraMap (𝓞 E) E x') ⊗ₜ[F] a = ((algebraMap (𝓞 E) E x') ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) * ((1 : E) ⊗ₜ[F] a)`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]`. Rewrite using `[e]`.

Use `mul_mem (Subring.subset_closure (Or.inl ⟨⟨_, x', rfl⟩, rfl⟩)) (Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩))` and prove the remaining obligations. Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`. Consider the case `add u u' _ _ hu hu' => rw [map_add]`. Conclude with `add_mem hu hu'`.

Consider the case `neg u _ hu => rw [map_neg]`. Conclude with `neg_mem hu`. Introduce `hz`. Establish `key : ∀ s ∈ Formalism.L2.Herm.intAf F E, ∃ t ∈ GlobalTheory.AdLat.hat1 F ((1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E), GlobalTheory.LevSplit.swp F E t = s`. Introduce `s hs`.

Proceed by induction on `hs using Subring.closure_induction with`. Consider the case `mem s hs`. Break down `hs with ⟨⟨_, c, rfl⟩, rfl⟩ | ⟨⟨b, hb⟩, rfl⟩` into its components or cases. Conclude with `⟨(1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (algebraMap (𝓞 E) E c), AddSubgroup.subset_closure ⟨1, one_int_af, _, (FractionalIdeal.mem_one_iff _).2 ⟨c, rfl⟩, rfl⟩, rfl⟩`. Conclude with `⟨b ⊗ₜ[F] (1 : E), AddSubgroup.subset_closure ⟨b, hb, 1, (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩, rfl⟩, rfl⟩`.

Consider the case `zero => exact ⟨0, zero_mem _, map_zero _⟩`. Consider the case `one => exact ⟨1, AddSubgroup.subset_closure ⟨1, one_int_af, 1, (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩, rfl⟩, map_one _⟩`. Consider the case `add a b _ _ ha hb`. Take `⟨t, ht, rfl⟩` from `ha`. Take `⟨t', ht', rfl⟩` from `hb`.

Conclude with `⟨t + t', add_mem ht ht', map_add _ _ _⟩`. Consider the case `neg a _ ha`. Take `⟨t, ht, rfl⟩` from `ha`. Conclude with `⟨-t, neg_mem ht, map_neg _ _⟩`. Consider the case `mul a b _ _ ha hb`.

Take `⟨t, ht, rfl⟩` from `ha`. Take `⟨t', ht', rfl⟩` from `hb`. Conclude with `⟨t * t', integral_adelic_lattice_mul_mem ht ht', map_mul _ _ _⟩`. Take `⟨t, ht, e⟩` from `key _ hz`. Rewrite `ht` using `[GlobalTheory.LevSplit.swp_bij.1 e]`. Then use the resulting hypothesis.
-/
theorem mem_integral_adelic_lattice_iff (z : GlobalTheory.AdLat.RA F E) :
    z ∈ GlobalTheory.AdLat.hat1 F ((1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E) ↔
      GlobalTheory.LevSplit.swp F E z ∈ Formalism.L2.Herm.intAf F E := by
  constructor
  · intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hz
      obtain ⟨x', rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
      rw [GlobalTheory.LevSplit.swp_tmul]
      have e : (algebraMap (𝓞 E) E x') ⊗ₜ[F] a =
          ((algebraMap (𝓞 E) E x') ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) * ((1 : E) ⊗ₜ[F] a) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      rw [e]
      refine mul_mem (Subring.subset_closure (Or.inl ⟨⟨_, x', rfl⟩, rfl⟩))
        (Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩))
    | zero => rw [map_zero]; exact zero_mem _
    | add u u' _ _ hu hu' => rw [map_add]; exact add_mem hu hu'
    | neg u _ hu => rw [map_neg]; exact neg_mem hu
  · intro hz
    have key : ∀ s ∈ Formalism.L2.Herm.intAf F E, ∃ t ∈ GlobalTheory.AdLat.hat1 F
        ((1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E), GlobalTheory.LevSplit.swp F E t = s := by
      intro s hs
      induction hs using Subring.closure_induction with
      | mem s hs =>
        rcases hs with ⟨⟨_, c, rfl⟩, rfl⟩ | ⟨⟨b, hb⟩, rfl⟩
        · exact ⟨(1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (algebraMap (𝓞 E) E c),
            AddSubgroup.subset_closure ⟨1, one_int_af, _, (FractionalIdeal.mem_one_iff _).2 ⟨c, rfl⟩, rfl⟩, rfl⟩
        · exact ⟨b ⊗ₜ[F] (1 : E), AddSubgroup.subset_closure ⟨b, hb, 1,
            (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩, rfl⟩, rfl⟩
      | zero => exact ⟨0, zero_mem _, map_zero _⟩
      | one => exact ⟨1, AddSubgroup.subset_closure ⟨1, one_int_af, 1,
            (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩, rfl⟩, map_one _⟩
      | add a b _ _ ha hb =>
        obtain ⟨t, ht, rfl⟩ := ha
        obtain ⟨t', ht', rfl⟩ := hb
        exact ⟨t + t', add_mem ht ht', map_add _ _ _⟩
      | neg a _ ha =>
        obtain ⟨t, ht, rfl⟩ := ha
        exact ⟨-t, neg_mem ht, map_neg _ _⟩
      | mul a b _ _ ha hb =>
        obtain ⟨t, ht, rfl⟩ := ha
        obtain ⟨t', ht', rfl⟩ := hb
        exact ⟨t * t', integral_adelic_lattice_mul_mem ht ht', map_mul _ _ _⟩
    obtain ⟨t, ht, e⟩ := key _ hz
    rwa [GlobalTheory.LevSplit.swp_bij.1 e] at ht

end Gen
end GlobalTheory.GramFrame

namespace GlobalTheory.GramFrame

def conjEquiv (I : AutInst) : Gal(I.E/I.F) :=
  AlgEquiv.ofAlgHom I.cm.sig I.cm.sig
    (AlgHom.ext fun x => by show star (star x) = x; exact star_star x)
    (AlgHom.ext fun x => by show star (star x) = x; exact star_star x)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem conjEquiv_apply (I : AutInst) (x : I.E) : conjEquiv I x = I.cm.sig x := rfl

/- English proof (translation)
Establish `hJ : ∀ a b, I.cm.sig (I.J b a) = I.J a b` using `fun a b => by`. Use `congrFun (congrFun I.J_herm a) b` as an intermediate fact. Conclude with `(by simpa [Formalism.UG.cT] using this : starRingEnd I.E (I.J b a) = I.J a b)`. Use `GlobalTheory.ParahoricLift.hatL_selfDual_gen (conjEquiv I) I.cm.sig (fun _ => rfl) I.J I.L I.L_fg I.L_span (fun x => by show star (star x) = x; exact star_star x) (fun a b => ?_) (by rw [Matrix.det_transpose]; exact I.J_det) (fun v => ?_) (fun s hs => Formalism.UG.P.csDual_sig_me …` and prove the remaining obligations. Simplify using `only [Matrix.transpose_apply, conjEquiv_apply]`.

Conclude with `hJ a b`. Rewrite using `[I.L_dual v]`. Use `forall₂_congr fun y _ => ?_` and prove the remaining obligations. Rewrite using `[FractionalIdeal.mem_one_iff]`. Establish `e : (∑ a, ∑ b, v a * I.Jᵀ a b * conjEquiv I (y b)) = Formalism.UG.hform (starRingEnd I.E) I.J y v`.

Unfold `Formalism.UG.hform`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Simplify using `only [Matrix.transpose_apply, conjEquiv_apply]`. Use `show _ = star (y a) * _ * _`.

Establish `: I.cm.sig (y a) = star (y a)` using `rfl`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Both sides reduce to the same expression.
-/
theorem hatL_selfDual (I : AutInst) : GlobalTheory.ParahoricLift.HatSelfDual I.cm.sig I.J I.L := by
  have hJ : ∀ a b, I.cm.sig (I.J b a) = I.J a b := fun a b => by
    have := congrFun (congrFun I.J_herm a) b
    exact (by simpa [Formalism.UG.cT] using this : starRingEnd I.E (I.J b a) = I.J a b)
  refine GlobalTheory.ParahoricLift.hatL_selfDual_gen (conjEquiv I) I.cm.sig (fun _ => rfl) I.J I.L I.L_fg I.L_span
    (fun x => by show star (star x) = x; exact star_star x) (fun a b => ?_) (by rw [Matrix.det_transpose]; exact I.J_det)
    (fun v => ?_) (fun s hs => Formalism.UG.P.csDual_sig_mem I.cm.sig hs) mem_integral_adelic_lattice_iff
  · simp only [Matrix.transpose_apply, conjEquiv_apply]
    exact hJ a b
  · rw [I.L_dual v]
    refine forall₂_congr fun y _ => ?_
    rw [FractionalIdeal.mem_one_iff]
    have e : (∑ a, ∑ b, v a * I.Jᵀ a b * conjEquiv I (y b)) =
        Formalism.UG.hform (starRingEnd I.E) I.J y v := by
      unfold Formalism.UG.hform
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      simp only [Matrix.transpose_apply, conjEquiv_apply]
      show _ = star (y a) * _ * _
      have : I.cm.sig (y a) = star (y a) := rfl
      rw [this]; ring
    rw [e]
    rfl

end GlobalTheory.GramFrame

namespace GlobalTheory.GramFrame

/- English proof (translation)
Introduce `I β hβ`. Use `set σ := sigA I with hσ`. Use `set JA : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) := I.J.map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) with hJA`. Use `set B : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) := (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) with hB`. Use `set Gm := Formalism.UG.cT σ B * JA * B with hGm`.

Establish `hSD` using `hatL_selfDual I`. Establish `hmem : ∀ a : Fin I.n → I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F, (∀ i, a i ∈ Formalism.L2.Herm.intAf I.F I.E) → B *ᵥ a ∈ Formalism.L2.Herm.hatL (F` using `I.F) I.L := fun a ha => by`. Use `(hβ _).2 fun i => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_mulVec, hB, Units.inv_mul, Matrix.one_mulVec]`. Conclude with `ha i`.

Establish `hsingle : ∀ k, ∀ i, (Pi.single k (1 : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) : Fin I.n → _) i ∈ Formalism.L2.Herm.intAf I.F I.E` using `fun k i => by`. Rewrite using `[Pi.single_apply]`. Use `split_ifs`. Conclude with `one_mem _`. Conclude with `zero_mem _`.

Establish `hG : ∀ i j, Gm i j ∈ Formalism.L2.Herm.intAf I.F I.E` using `fun i j => by`. Rewrite using `[← Formalism.UG.P.hform_single σ Gm i j, hGm, ← Formalism.UG.P.hform_mulVec]`. Conclude with `(hSD _).1 (hmem _ (hsingle j)) _ (hmem _ (hsingle i))`. Establish `hdet : IsUnit Gm.det`. Establish `h1 : IsUnit B.det` using `(Matrix.isUnit_iff_isUnit_det B).1 β.isUnit`.

Establish `h2 : IsUnit (Formalism.UG.cT σ B).det`. Rewrite using `[Formalism.UG.cT, Matrix.det_transpose, show B.map σ = σ.mapMatrix B from rfl, ← RingHom.map_det]`. Conclude with `h1.map σ`. Establish `h3 : IsUnit JA.det`. Rewrite using `[hJA, show I.J.map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) = (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)).mapMatrix I.J from rfl, ← RingHom.map_det]`.

Conclude with `(isUnit_iff_ne_zero.2 I.J_det).map _`. Rewrite using `[hGm, Matrix.det_mul, Matrix.det_mul]`. Conclude with `(h2.mul h3).mul h1`. Establish `hGi : Gm * Gm⁻¹ = 1` using `Matrix.mul_nonsing_inv Gm hdet`. Establish `hiG : Gm⁻¹ * Gm = 1` using `Matrix.nonsing_inv_mul Gm hdet`.

Establish `hG' : ∀ i j, (Gm⁻¹) i j ∈ Formalism.L2.Herm.intAf I.F I.E` using `fun i j => by set c : Fin I.n → I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F := fun l => (Gm⁻¹) l j with hc`. Establish `hx : B *ᵥ c ∈ Formalism.L2.Herm.hatL (F` using `I.F) I.L := by`. Use `(hSD _).2 fun z hz => ?_` and prove the remaining obligations. Establish `hz'` using `(hβ z).1 hz`. Use `set a := ((β⁻¹ : GL (Fin I.n) _) : Matrix (Fin I.n) (Fin I.n) _) *ᵥ z with ha`.

Establish `hza : z = B *ᵥ a`. Rewrite using `[ha, Matrix.mulVec_mulVec, hB, Units.mul_inv, Matrix.one_mulVec]`. Rewrite using `[hza, Formalism.UG.P.hform_mulVec, ← hGm, Formalism.UG.P.hform_eq_dot]`. Establish `e : Gm *ᵥ c = Pi.single j 1`. Use function extensionality and compare the values at `k`.

Use `congrFun (congrFun hGi k) j` as an intermediate fact. Rewrite `this` using `[Matrix.mul_apply]`. Simplify using `only [Matrix.mulVec, dotProduct, hc, this, Pi.single_apply, Matrix.one_apply]`. Rewrite using `[e]`. Simplify using `only [dotProduct, Function.comp_apply, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.

Conclude with `Formalism.L2.SG.Pf.unitaryCongruence.sigA_mem I (hz' j)`. Use `(hβ _).1 hx i` as an intermediate fact. Rewrite `this` using `[Matrix.mulVec_mulVec, hB, Units.inv_mul, Matrix.one_mulVec]`. Then use the resulting hypothesis. Set `S` to `Formalism.L2.Herm.intAf I.F I.E`. Establish `inj : Function.Injective fun M : Matrix (Fin I.n) (Fin I.n) S => M.map S.subtype` using `Matrix.map_injective S.subtype_injective`.

Use `⟨⟨Matrix.of fun i j => ⟨Gm i j, hG i j⟩, Matrix.of fun i j => ⟨(Gm⁻¹) i j, hG' i j⟩, inj ?_, inj ?_⟩, ?_⟩` and prove the remaining obligations. Use `show Matrix.map _ S.subtype = Matrix.map _ S.subtype`. Rewrite using `[Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]`. Conclude with `hGi`. Use `show Matrix.map _ S.subtype = Matrix.map _ S.subtype`.

Rewrite using `[Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]`. Conclude with `hiG`. Both sides reduce to the same expression.
-/
theorem gram_frame_int : ∀ (I : AutInst) (β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)), IsFrame β I.L → ∃ G : GL (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E), ((Formalism.UG.bc (Formalism.L2.Herm.intAf I.F I.E).subtype G : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) = Formalism.UG.cT (sigA I) (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) * I.J.map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) * (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) := by
  intro I β hβ
  set σ := sigA I with hσ
  set JA : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) :=
    I.J.map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) with hJA
  set B : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) := (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) with hB
  set Gm := Formalism.UG.cT σ B * JA * B with hGm
  have hSD := hatL_selfDual I

  have hmem : ∀ a : Fin I.n → I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F, (∀ i, a i ∈ Formalism.L2.Herm.intAf I.F I.E) →
      B *ᵥ a ∈ Formalism.L2.Herm.hatL (F := I.F) I.L := fun a ha => by
    refine (hβ _).2 fun i => ?_
    rw [Matrix.mulVec_mulVec, hB, Units.inv_mul, Matrix.one_mulVec]
    exact ha i
  have hsingle : ∀ k, ∀ i, (Pi.single k (1 : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) : Fin I.n → _) i ∈
      Formalism.L2.Herm.intAf I.F I.E := fun k i => by
    rw [Pi.single_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _

  have hG : ∀ i j, Gm i j ∈ Formalism.L2.Herm.intAf I.F I.E := fun i j => by
    rw [← Formalism.UG.P.hform_single σ Gm i j, hGm, ← Formalism.UG.P.hform_mulVec]
    exact (hSD _).1 (hmem _ (hsingle j)) _ (hmem _ (hsingle i))

  have hdet : IsUnit Gm.det := by
    have h1 : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).1 β.isUnit
    have h2 : IsUnit (Formalism.UG.cT σ B).det := by
      rw [Formalism.UG.cT, Matrix.det_transpose, show B.map σ = σ.mapMatrix B from rfl, ← RingHom.map_det]
      exact h1.map σ
    have h3 : IsUnit JA.det := by
      rw [hJA, show I.J.map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) = (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)).mapMatrix I.J from rfl, ← RingHom.map_det]
      exact (isUnit_iff_ne_zero.2 I.J_det).map _
    rw [hGm, Matrix.det_mul, Matrix.det_mul]
    exact (h2.mul h3).mul h1
  have hGi : Gm * Gm⁻¹ = 1 := Matrix.mul_nonsing_inv Gm hdet
  have hiG : Gm⁻¹ * Gm = 1 := Matrix.nonsing_inv_mul Gm hdet

  have hG' : ∀ i j, (Gm⁻¹) i j ∈ Formalism.L2.Herm.intAf I.F I.E := fun i j => by
    set c : Fin I.n → I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F := fun l => (Gm⁻¹) l j with hc
    have hx : B *ᵥ c ∈ Formalism.L2.Herm.hatL (F := I.F) I.L := by
      refine (hSD _).2 fun z hz => ?_
      have hz' := (hβ z).1 hz
      set a := ((β⁻¹ : GL (Fin I.n) _) : Matrix (Fin I.n) (Fin I.n) _) *ᵥ z with ha
      have hza : z = B *ᵥ a := by
        rw [ha, Matrix.mulVec_mulVec, hB, Units.mul_inv, Matrix.one_mulVec]
      rw [hza, Formalism.UG.P.hform_mulVec, ← hGm, Formalism.UG.P.hform_eq_dot]
      have e : Gm *ᵥ c = Pi.single j 1 := by
        funext k
        have := congrFun (congrFun hGi k) j
        rw [Matrix.mul_apply] at this
        simp only [Matrix.mulVec, dotProduct, hc, this, Pi.single_apply, Matrix.one_apply]
      rw [e]
      simp only [dotProduct, Function.comp_apply, Pi.single_apply, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      exact Formalism.L2.SG.Pf.unitaryCongruence.sigA_mem I (hz' j)
    have := (hβ _).1 hx i
    rwa [Matrix.mulVec_mulVec, hB, Units.inv_mul, Matrix.one_mulVec] at this

  let S := Formalism.L2.Herm.intAf I.F I.E
  have inj : Function.Injective fun M : Matrix (Fin I.n) (Fin I.n) S => M.map S.subtype :=
    Matrix.map_injective S.subtype_injective
  refine ⟨⟨Matrix.of fun i j => ⟨Gm i j, hG i j⟩, Matrix.of fun i j => ⟨(Gm⁻¹) i j, hG' i j⟩, inj ?_, inj ?_⟩, ?_⟩
  · show Matrix.map _ S.subtype = Matrix.map _ S.subtype
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact hGi
  · show Matrix.map _ S.subtype = Matrix.map _ S.subtype
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact hiG
  · rfl

end GlobalTheory.GramFrame
