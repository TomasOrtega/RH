import Development.WeilBound.ThetaLifts.LatticeBasics.FrameConj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.BaseKnownTheoremsE
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseFrameB
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsIntAddConjEqOneOfBaseGoodK

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ThK.Dbl.Frame
open scoped Matrix TensorProduct
open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Doubling
open Formalism.UG (bc)
section Generic
variable {S R β : Type} [CommRing S] [CommRing R] [Fintype β] [DecidableEq β]
end Generic
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}
end GlobalTheory.ThK.Dbl.Frame
namespace GlobalTheory.ThK.Dbl
open scoped Matrix TensorProduct
open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Doubling GlobalTheory.ThK.Dbl.Frame
open Formalism.UG (bc)
/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n Y r s hB hY K hK`. Establish `hc` using `hB.cm`. Establish `hσ` using `cm_conj_conj hc`. Establish `hL : Y.L.IsLattice E` using `hY.elim (·.lat) (·.lat)`. Establish `hJ` using `Frame.det_ne hY`.

Choose the witnesses or unpack the hypotheses as in `⟨ε, hε, c, c1, c2⟩ : ∃ ε : ℤˣ, (Y.J.map σ)ᵀ = ((ε : ℤ) : E) • Y.J ∧ ∃ c : ℂ, star c * c = 1 ∧ ∀ w, (c • Y.J.map (B.emb w).1)ᴴ = c • Y.J.map (B.emb w).1 ∧ IsCartan (c • Y.J.map (B.emb w).1) (Y.θ w) := by`. Break down `hY with h | h` into its components or cases. Use `⟨1, Matrix.ext fun i j => by simpa using h.herm i j, 1, by simp, fun w => ?_⟩` and prove the remaining obligations. Rewrite using `[one_smul]`. Conclude with `⟨Matrix.ext fun i j => (hc.2.2.2 _ _).symm.trans (congrArg _ (h.herm i j)), h.cartan w⟩`.

Use `⟨-1, Matrix.ext fun i j => by simpa using h.skew i j, Complex.I, by simp, fun w => ⟨Matrix.ext fun i j => ?_, h.cartan w⟩⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `star (Complex.I * (B.emb w).1 (Y.J j i)) = Complex.I * (B.emb w).1 (Y.J i j)`. Rewrite using `[star_mul', ← hc.2.2.2, h.skew]`. Simplify using the standard rewrite rules. Establish `ee : ∀ (S : Type) [CommRing S], ((ε : ℤ) : S) * (ε : ℤ) = 1` using `fun S _ => by`.

Rewrite using `[← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]`. Simplify using the standard rewrite rules. Use `choose gw hw using fun w => Frame.exists_arch c1 (c2 w).1 (Frame.isUnit_of_cartan (c2 w).2) (c2 w).2`. Take `⟨a, g, ha, hg, hg'⟩` from `_root_.GlobalTheory.ThK.Dbl.Frame.exists_ad_k hB hY hJ gw`. Take `⟨t, ht⟩` from `_root_.GlobalTheory.exists_int_add_conj_eq_one_of_base_good_k B hB`.

Set `ι` to `inclR (F := F) (E := E) (AF F)`. Set `cc : AE F E →+* AE F E` to `cA σ`. Establish `hι : ∀ z, ι (σ z) = cc (ι z)` using `fun z => rfl`. Establish `hcc : ∀ z, cc (cc z) = z` using `fun z => by`. Express the relevant statement in the definitionally equal form `cA σ (cA σ z) = z`.

Rewrite using `[cA_eq]`. Conclude with `sigR_invol hσ z`. Establish `hf : ∀ v z, compFin F E v (cc z) = sigR _ σ (compFin F E v z)` using `fun v z => by`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero]`.

Consider the case `tmul a x => rfl`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Establish `hi : ∀ w z, piInf (B.emb w) (cc z) = star (piInf (B.emb w) z)` using `fun w z => by`. Use `Eq.trans (congrArg (infEmb (B.emb w)) ?_) (infEmb_sigR hc (B.emb w) (compInf F E w z)).symm` and prove the remaining obligations. Proceed by induction on `z using TensorProduct.induction_on with`.

Consider the case `zero => simp only [map_zero]`. Consider the case `tmul a x => rfl`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Establish `jf : ∀ v, (incM F Y.J).map (compFin F E v) = Y.J.map (inclR (F` using `F) (Fv F v)) := fun v => Matrix.ext fun i j => congrArg (· ⊗ₜ[F] Y.J i j) (map_one (evFin F v))`. Establish `ii : ∀ w z, piInf (B.emb w) (ι z) = (B.emb w).1 z` using `fun w z => by`.

Express the relevant statement in the definitionally equal form `InfinitePlace.Completion.extensionEmbedding w 1 * (B.emb w).1 z = _`. Rewrite using `[map_one, one_mul]`. Establish `ji : ∀ w, (incM F Y.J).map (piInf (B.emb w)) = Y.J.map (B.emb w).1` using `fun w => Matrix.ext fun i j => ii w _`. Establish `h2 : (2⁻¹ : E) + σ 2⁻¹ = 1` using `by rw [map_inv₀, map_ofNat]; norm_num`. Set `α : AE F E` to `ι 2⁻¹ + eF F • ι (t - 2⁻¹)`.

Establish `α0 : α + cc α = 1`. Establish `: cc α = ι (σ 2⁻¹) + eF F • ι (σ (t - 2⁻¹))`. Rewrite using `[hι, hι, map_add]`. Conclude with `congrArg _ (map_smul (cA σ) _ _)`. Rewrite using `[this, add_add_add_comm, ← smul_add, ← map_add, ← map_add, h2, map_sub σ, sub_add_sub_comm, ht, h2, sub_self]`.

Simplify using the standard rewrite rules. Establish `α1 : ∀ v, compFin F E v α ∈ intLoc F E v` using `fun v => by`. Rewrite using `[map_add, comp_eF, ← map_add, ← map_add, add_sub_cancel]`. Conclude with `tmul_mem_intLoc (a := evFin F v 1) (by rw [map_one]; exact one_mem _) t`. Establish `α2 : ∀ w, piInf (B.emb w) α = 2⁻¹` using `fun w => by`.

Establish `: piInf (B.emb w) (algebraMap (AF F) (AE F E) (eF F)) = 0`. Express the relevant statement in the definitionally equal form `InfinitePlace.Completion.extensionEmbedding w 0 * (B.emb w).1 1 = _`. Rewrite using `[map_zero, zero_mul]`. Rewrite using `[map_add, Algebra.smul_def, map_mul, this, zero_mul, add_zero, ii, map_inv₀, map_ofNat]`. Establish `uJ : IsUnit Y.J` using `(Matrix.isUnit_iff_isUnit_det _).2 hJ.isUnit`.

Take `⟨T₀, hT₀⟩` from `exists_dual (σ : E →+* E) hσ uJ 1`. Take `⟨T, hT⟩` from `exists_dual cc hcc (J := incM F Y.J) (uJ.map ι.mapMatrix) g`. Establish `g0` using `frame_gram (σ : E →+* E) hσ (ee E) h2 hε 1 T₀ hT₀`. Establish `g1` using `frame_gram cc hcc (ee _) α0 (J := incM F Y.J) (Matrix.ext fun i j => by`. Use `congrArg ι (congrFun (congrFun hε i) j)` as an intermediate fact.

Rewrite `this` using `[Matrix.smul_apply, smul_eq_mul, map_mul, map_intCast]`. Conclude with `this) g T hT`. Establish `d0` using `frame_diag 1 T₀ (2⁻¹ : E)`. Use `set b := two 1 * wit (2⁻¹ : E) T₀`. Establish `d1` using `frame_diag g T α`.

Use `set b' := two g * wit α T with hb'`. Establish `g2 : (bc ι b).1ᵀ * dbl (incM F Y.J) * (bc ι b).1.map cc = b'.1ᵀ * dbl (incM F Y.J) * b'.1.map cc`. Use `(map_gram ι hι b.1 (dbl Y.J)).symm.trans (congrArg (·.map ι) g0)` as an intermediate fact. Rewrite `this` using `[map_dbl]`. Rewrite using `[g1]`.

Use `this.trans ?_` and prove the remaining obligations. Apply the tactic sequence `ext (i | i) (j | j) <;> simp [Matrix.one_apply, apply_ite ι]`. Set `p : G2 σ Y` to `⟨b' * (bc ι b)⁻¹, by`. Express the relevant statement in the definitionally equal form `(b'.1 * ((bc ι b)⁻¹).1)ᵀ * _ * (b'.1 * ((bc ι b)⁻¹).1).map cc = _`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc]`. Use `_ = ((bc ι b).1 * ((bc ι b)⁻¹).1)ᵀ * dbl (incM F Y.J) * ((bc ι b).1 * ((bc ι b)⁻¹).1).map cc := by`. Simplify using `only [← g2, Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc]`. Use `_ = _ := by rw [Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]⟩`. Establish `fr : ∀ k : G2 σ Y, inFrame b k = (b'⁻¹ * (p * k * p⁻¹).1 * b').1` using `fun k => by`.

Rewrite using `[show b'⁻¹ * (p * k * p⁻¹).1 * b' = bc ι b⁻¹ * k.1 * bc ι b by`. Express the relevant statement in the definitionally equal form `b'⁻¹ * (b' * (bc ι b)⁻¹ * k.1 * (b' * (bc ι b)⁻¹)⁻¹) * b' = _`. Rewrite using `[map_inv]`. Use the proof step `group]`. Both sides reduce to the same expression.

Establish `fin : ∀ k : G2 σ Y, Keeps (p * k * p⁻¹) ↔ ∀ i j, eF F • inFrame b k i j ∈ intHat F E` using `fun k => by`. Simplify using `only [keeps_iff hL.fg ha, mem_intHat, fr]`. Use `(forall_congr' fun v => ?_).trans (forall_comm.trans (forall_congr' fun i => forall_comm))` and prove the remaining obligations. Take `⟨⟨l, hl⟩, u1, G', u2, u3⟩` from `hg v`. Take `⟨q1, q2⟩` from `int_dual (T := bc (compFin F E v) T) (sigR_invol hσ) (fun z => sigR_mem_intLoc σ) u1 u2 u3 (by`.

Use `congrArg (·.map (compFin F E v)) hT` as an intermediate fact. Simplify using `only [Matrix.map_mul (M := T.1.map cc), map_gram _ (hf v), jf, Matrix.map_one _ (map_zero _) (map_one _)] at this`. Rewrite using `[← this]`. Use `congr 1`. Conclude with `Matrix.ext fun i j => (hf v _).symm)`.

Take `⟨q3, q4⟩` from `int_wit (α1 v) q1 q2`. Use `int_conj hl q3 q4 (bc (compFin F E v) (p * k * p⁻¹).1)` as an intermediate fact. Simplify using `only [← bc_wit, ← bc_two, ← map_mul (bc (compFin F E v)), ← map_inv (bc (compFin F E v))] at this`. Conclude with `this`. Use `⟨b, K.comap (MulAut.conj p).toMonoidHom, p, g, ⟨⟨ε, g0⟩, 1, ?_⟩, fun k => ?_, ?_, fun k => ?_⟩` and prove the remaining obligations.

Rewrite using `[← d0, ← Matrix.fromCols_toCols b.1, Matrix.fromCols_mul_fromRows]`. Simplify using the standard rewrite rules. Use `(hK (p * k * p⁻¹)).trans (and_congr (forall_congr' fun w => ?_) ?_)` and prove the remaining obligations. Use `hw w (bc (piInf (B.emb w)) T) (by` as an intermediate fact. Use `congrArg (·.map (piInf (B.emb w))) hT` as an intermediate fact.

Simplify using `only [Matrix.map_mul (M := T.1.map cc), map_gram _ (hi w), ji, Matrix.map_one _ (map_zero _) (map_one _)] at this`. Rewrite using `[← this, ← hg']`. Use `congr 1`. Conclude with `Matrix.ext fun i j => (hi w _).symm) (bc (piInf (B.emb w)) (p * k * p⁻¹).1) (by`. Use `(map_gram _ (hi w) _ _).symm.trans (congrArg (·.map (piInf (B.emb w))) (show _ = _ from (p * k * p⁻¹).2))` as an intermediate fact.

Simplify using `only [map_dbl, ji] at this`. Conclude with `this)`. Rewrite `this` using `[← hg', ← α2 w, ← bc_wit, ← bc_two, ← map_mul, ← map_inv, ← map_mul, ← map_mul]`. Rewrite using `[fr]`. Conclude with `this.symm`.

Simplify using `only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, forall_and]`. Use `Iff.trans ?_ (and_congr (fin k) (fin k⁻¹))` and prove the remaining obligations. Rewrite using `[show p * k⁻¹ * p⁻¹ = (p * k * p⁻¹)⁻¹ by group]`. Simplify using `only [Keeps, forall_and]`. Conclude with `and_and_and_comm`.

Conclude with `par_of ι (d0.trans (Matrix.mul_one _)) d1`. Express the relevant statement in the definitionally equal form `_ ↔ p * (p⁻¹ * k * p) * p⁻¹ ∈ K`. Rewrite using `[show p * (p⁻¹ * k * p) * p⁻¹ = k by group]`.
-/
theorem frameConj_k : _root_.GlobalTheory.ThK.Dbl.FrameConj_k := by
  intro F E _ _ _ _ _ σ B n Y r s hB hY K hK
  have hc := hB.cm
  have hσ := cm_conj_conj hc
  have hL : Y.L.IsLattice E := hY.elim (·.lat) (·.lat)
  have hJ := Frame.det_ne hY
  obtain ⟨ε, hε, c, c1, c2⟩ : ∃ ε : ℤˣ, (Y.J.map σ)ᵀ = ((ε : ℤ) : E) • Y.J ∧ ∃ c : ℂ, star c * c = 1 ∧
      ∀ w, (c • Y.J.map (B.emb w).1)ᴴ = c • Y.J.map (B.emb w).1 ∧ IsCartan (c • Y.J.map (B.emb w).1) (Y.θ w) := by
    rcases hY with h | h
    · refine ⟨1, Matrix.ext fun i j => by simpa using h.herm i j, 1, by simp, fun w => ?_⟩
      rw [one_smul]
      exact ⟨Matrix.ext fun i j => (hc.2.2.2 _ _).symm.trans (congrArg _ (h.herm i j)), h.cartan w⟩
    · refine ⟨-1, Matrix.ext fun i j => by simpa using h.skew i j, Complex.I, by simp, fun w => ⟨Matrix.ext fun i j => ?_, h.cartan w⟩⟩
      change star (Complex.I * (B.emb w).1 (Y.J j i)) = Complex.I * (B.emb w).1 (Y.J i j)
      rw [star_mul', ← hc.2.2.2, h.skew]; simp
  have ee : ∀ (S : Type) [CommRing S], ((ε : ℤ) : S) * (ε : ℤ) = 1 := fun S _ => by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]; simp
  choose gw hw using fun w => Frame.exists_arch c1 (c2 w).1 (Frame.isUnit_of_cartan (c2 w).2) (c2 w).2
  obtain ⟨a, g, ha, hg, hg'⟩ := _root_.GlobalTheory.ThK.Dbl.Frame.exists_ad_k hB hY hJ gw
  obtain ⟨t, ht⟩ := _root_.GlobalTheory.exists_int_add_conj_eq_one_of_base_good_k B hB
  let ι := inclR (F := F) (E := E) (AF F)
  let cc : AE F E →+* AE F E := cA σ
  have hι : ∀ z, ι (σ z) = cc (ι z) := fun z => rfl
  have hcc : ∀ z, cc (cc z) = z := fun z => by
    change cA σ (cA σ z) = z
    rw [cA_eq]; exact sigR_invol hσ z
  have hf : ∀ v z, compFin F E v (cc z) = sigR _ σ (compFin F E v z) := fun v z => by
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a x => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have hi : ∀ w z, piInf (B.emb w) (cc z) = star (piInf (B.emb w) z) := fun w z => by
    refine Eq.trans (congrArg (infEmb (B.emb w)) ?_) (infEmb_sigR hc (B.emb w) (compInf F E w z)).symm
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a x => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have jf : ∀ v, (incM F Y.J).map (compFin F E v) = Y.J.map (inclR (F := F) (Fv F v)) := fun v =>
    Matrix.ext fun i j => congrArg (· ⊗ₜ[F] Y.J i j) (map_one (evFin F v))
  have ii : ∀ w z, piInf (B.emb w) (ι z) = (B.emb w).1 z := fun w z => by
    change InfinitePlace.Completion.extensionEmbedding w 1 * (B.emb w).1 z = _
    rw [map_one, one_mul]
  have ji : ∀ w, (incM F Y.J).map (piInf (B.emb w)) = Y.J.map (B.emb w).1 := fun w => Matrix.ext fun i j => ii w _
  have h2 : (2⁻¹ : E) + σ 2⁻¹ = 1 := by rw [map_inv₀, map_ofNat]; norm_num
  let α : AE F E := ι 2⁻¹ + eF F • ι (t - 2⁻¹)
  have α0 : α + cc α = 1 := by
    have : cc α = ι (σ 2⁻¹) + eF F • ι (σ (t - 2⁻¹)) := by
      rw [hι, hι, map_add]; exact congrArg _ (map_smul (cA σ) _ _)
    rw [this, add_add_add_comm, ← smul_add, ← map_add, ← map_add, h2, map_sub σ, sub_add_sub_comm, ht, h2, sub_self]
    simp
  have α1 : ∀ v, compFin F E v α ∈ intLoc F E v := fun v => by
    rw [map_add, comp_eF, ← map_add, ← map_add, add_sub_cancel]
    exact tmul_mem_intLoc (a := evFin F v 1) (by rw [map_one]; exact one_mem _) t
  have α2 : ∀ w, piInf (B.emb w) α = 2⁻¹ := fun w => by
    have : piInf (B.emb w) (algebraMap (AF F) (AE F E) (eF F)) = 0 := by
      change InfinitePlace.Completion.extensionEmbedding w 0 * (B.emb w).1 1 = _
      rw [map_zero, zero_mul]
    rw [map_add, Algebra.smul_def, map_mul, this, zero_mul, add_zero, ii, map_inv₀, map_ofNat]
  have uJ : IsUnit Y.J := (Matrix.isUnit_iff_isUnit_det _).2 hJ.isUnit
  obtain ⟨T₀, hT₀⟩ := exists_dual (σ : E →+* E) hσ uJ 1
  obtain ⟨T, hT⟩ := exists_dual cc hcc (J := incM F Y.J) (uJ.map ι.mapMatrix) g
  have g0 := frame_gram (σ : E →+* E) hσ (ee E) h2 hε 1 T₀ hT₀
  have g1 := frame_gram cc hcc (ee _) α0 (J := incM F Y.J) (Matrix.ext fun i j => by
    have := congrArg ι (congrFun (congrFun hε i) j)
    rw [Matrix.smul_apply, smul_eq_mul, map_mul, map_intCast] at this
    exact this) g T hT
  have d0 := frame_diag 1 T₀ (2⁻¹ : E)
  set b := two 1 * wit (2⁻¹ : E) T₀
  have d1 := frame_diag g T α
  set b' := two g * wit α T with hb'
  have g2 : (bc ι b).1ᵀ * dbl (incM F Y.J) * (bc ι b).1.map cc = b'.1ᵀ * dbl (incM F Y.J) * b'.1.map cc := by
    have := (map_gram ι hι b.1 (dbl Y.J)).symm.trans (congrArg (·.map ι) g0)
    rw [map_dbl] at this
    rw [g1]
    refine this.trans ?_
    ext (i | i) (j | j) <;> simp [Matrix.one_apply, apply_ite ι]
  let p : G2 σ Y := ⟨b' * (bc ι b)⁻¹, by
    change (b'.1 * ((bc ι b)⁻¹).1)ᵀ * _ * (b'.1 * ((bc ι b)⁻¹).1).map cc = _
    calc _ = ((bc ι b)⁻¹).1ᵀ * (b'.1ᵀ * dbl (incM F Y.J) * b'.1.map cc) * ((bc ι b)⁻¹).1.map cc := by
          simp only [Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc]
      _ = ((bc ι b).1 * ((bc ι b)⁻¹).1)ᵀ * dbl (incM F Y.J) * ((bc ι b).1 * ((bc ι b)⁻¹).1).map cc := by
          simp only [← g2, Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc]
      _ = _ := by rw [Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]⟩
  have fr : ∀ k : G2 σ Y, inFrame b k = (b'⁻¹ * (p * k * p⁻¹).1 * b').1 := fun k => by
    rw [show b'⁻¹ * (p * k * p⁻¹).1 * b' = bc ι b⁻¹ * k.1 * bc ι b by
      change b'⁻¹ * (b' * (bc ι b)⁻¹ * k.1 * (b' * (bc ι b)⁻¹)⁻¹) * b' = _
      rw [map_inv]; group]
    rfl
  have fin : ∀ k : G2 σ Y, Keeps (p * k * p⁻¹) ↔ ∀ i j, eF F • inFrame b k i j ∈ intHat F E := fun k => by
    simp only [keeps_iff hL.fg ha, mem_intHat, fr]
    refine (forall_congr' fun v => ?_).trans (forall_comm.trans (forall_congr' fun i => forall_comm))
    obtain ⟨⟨l, hl⟩, u1, G', u2, u3⟩ := hg v
    obtain ⟨q1, q2⟩ := int_dual (T := bc (compFin F E v) T) (sigR_invol hσ) (fun z => sigR_mem_intLoc σ) u1 u2 u3 (by
      have := congrArg (·.map (compFin F E v)) hT
      simp only [Matrix.map_mul (M := T.1.map cc), map_gram _ (hf v), jf, Matrix.map_one _ (map_zero _) (map_one _)] at this
      rw [← this]
      congr 1
      exact Matrix.ext fun i j => (hf v _).symm)
    obtain ⟨q3, q4⟩ := int_wit (α1 v) q1 q2
    have := int_conj hl q3 q4 (bc (compFin F E v) (p * k * p⁻¹).1)
    simp only [← bc_wit, ← bc_two, ← map_mul (bc (compFin F E v)), ← map_inv (bc (compFin F E v))] at this
    exact this
  refine ⟨b, K.comap (MulAut.conj p).toMonoidHom, p, g, ⟨⟨ε, g0⟩, 1, ?_⟩, fun k => ?_, ?_, fun k => ?_⟩
  · rw [← d0, ← Matrix.fromCols_toCols b.1, Matrix.fromCols_mul_fromRows]; simp
  · refine (hK (p * k * p⁻¹)).trans (and_congr (forall_congr' fun w => ?_) ?_)
    · have := hw w (bc (piInf (B.emb w)) T) (by
        have := congrArg (·.map (piInf (B.emb w))) hT
        simp only [Matrix.map_mul (M := T.1.map cc), map_gram _ (hi w), ji, Matrix.map_one _ (map_zero _) (map_one _)] at this
        rw [← this, ← hg']
        congr 1
        exact Matrix.ext fun i j => (hi w _).symm) (bc (piInf (B.emb w)) (p * k * p⁻¹).1) (by
        have := (map_gram _ (hi w) _ _).symm.trans (congrArg (·.map (piInf (B.emb w))) (show _ = _ from (p * k * p⁻¹).2))
        simp only [map_dbl, ji] at this
        exact this)
      rw [← hg', ← α2 w, ← bc_wit, ← bc_two, ← map_mul, ← map_inv, ← map_mul, ← map_mul] at this
      rw [fr]
      exact this.symm
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, forall_and]
      refine Iff.trans ?_ (and_congr (fin k) (fin k⁻¹))
      rw [show p * k⁻¹ * p⁻¹ = (p * k * p⁻¹)⁻¹ by group]
      simp only [Keeps, forall_and]
      exact and_and_and_comm
  · exact par_of ι (d0.trans (Matrix.mul_one _)) d1
  · change _ ↔ p * (p⁻¹ * k * p) * p⁻¹ ∈ K
    rw [show p * (p⁻¹ * k * p) * p⁻¹ = k by group]
end GlobalTheory.ThK.Dbl
end
end
