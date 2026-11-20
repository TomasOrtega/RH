import Mathlib
import Development.WeilBound.ThetaLifts.LatticeBasics.HgtWitt
import Development.WeilBound.CoreStatements.LocalThetaKernels.IwasFrame
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.MemKFinOfFrameIntegral
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.HasSatOfFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceSplitOrInert
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntAddConjEqOneOfBaseGood

noncomputable section

namespace GlobalTheory.ThK.Dbl.Hgt

open scoped Matrix TensorProduct nonZeroDivisors
open NumberField IsDedekindDomain GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.Doubling GlobalTheory.CompanionTheory.IwaDbl
open PositivityTheory.ThKH.Iwas

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {v : Pl F}

def LocInt (v : Pl F) (z : E) : Prop := ∃ s : 𝓞 F, s ∉ v.asIdeal ∧ ∃ o : 𝓞 E, algebraMap F E s * z = o

omit [NumberField E] in
/- English proof (translation)
Take `⟨s, hs, o, ho⟩` from `h`. Conclude with `mem_latLoc_stdLattice.1 (Frames.incl_mem_latLoc (L := stdLattice E 1) hs (x := fun _ => z) fun i _ => ⟨o, ho.symm⟩) 0`.
-/
theorem LocInt.mem {z : E} (h : LocInt v z) : inclR (F := F) (Fv F v) z ∈ intLoc F E v := by
  obtain ⟨s, hs, o, ho⟩ := h
  exact mem_latLoc_stdLattice.1 (Frames.incl_mem_latLoc (L := stdLattice E 1) hs (x := fun _ => z)
    fun i _ => ⟨o, ho.symm⟩) 0

omit [NumberField F] [NumberField E] in
/- English proof (translation)
Take `⟨t, ht, o, ho⟩` from `h`. Use `⟨t * s, fun h => (v.isPrime.mem_or_mem h).elim ht hs, o, ?_⟩` and prove the remaining obligations. Rewrite using `[← ho, ← mul_assoc, ← map_mul]`. Both sides reduce to the same expression.
-/
theorem LocInt.of_mul {z : E} {s : 𝓞 F} (hs : s ∉ v.asIdeal) (h : LocInt v (algebraMap F E s * z)) : LocInt v z := by
  obtain ⟨t, ht, o, ho⟩ := h
  refine ⟨t * s, fun h => (v.isPrime.mem_or_mem h).elim ht hs, o, ?_⟩
  rw [← ho, ← mul_assoc, ← map_mul]; rfl

/- English proof (translation)
Use `set I := FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E)`. Set `e` to `(LinearEquiv.funUnique (Fin 1) (𝓞 E) E).symm`. Set `L : Submodule (𝓞 E) (Fin 1 → E)` to `(I : Submodule (𝓞 E) E).map e.toLinearMap`. Establish `hL : ∀ x, x ∈ L ↔ InD (x 0)` using `fun x => by`. Rewrite using `[inD_iff]`.

Conclude with `⟨by rintro ⟨y, hy, rfl⟩; exact hy, fun h => ⟨x 0, h, funext fun i => by rw [Subsingleton.elim i 0]; rfl⟩⟩`. Establish `: L.IsLattice E` using `⟨(FractionalIdeal.fg_of_isNoetherianRing le_rfl I).map _, by`. Use `eq_top_iff.2 fun x _ => ?_` and prove the remaining obligations. Establish `: x = x 0 • fun _ => (1 : E)` using `funext fun i => by rw [Subsingleton.elim i 0]; simp`. Rewrite using `[this]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ((hL _).2 ((inD_iff _).2 (FractionalIdeal.one_le_dual_one ℤ ℚ (FractionalIdeal.one_mem_one _)))))⟩`. Take `⟨P, h1, h2⟩` from `Frames.exists_rational_frame L v`. Take `⟨s, hs, hs'⟩` from `h1 0`. Establish `hP : P.1 0 0 * (P⁻¹).1 0 0 = 1`. Simplify `congrFun (congrFun P.mul_inv 0) 0` using `[Matrix.mul_apply]`.

Establish `hs0 : algebraMap F E s ≠ 0` using `fun h => hs (by`. Rewrite using `[show s = 0 from RingOfIntegers.coe_injective (by simpa using h)]; exact zero_mem _)`. Use `⟨algebraMap F E s * P.1 0 0, mul_ne_zero hs0 (left_ne_zero_of_mul_eq_one hP), (hL _).1 hs', fun z hz => ?_⟩` and prove the remaining obligations. Take `⟨t, ht, ht'⟩` from `h2 (fun _ => z) ((hL _).2 hz)`. Take `⟨o, ho⟩` from `ht' 0 trivial`.

Use `LocInt.of_mul hs ⟨t, ht, o, Eq.trans ?_ ho.symm⟩` and prove the remaining obligations. Rewrite using `[mul_inv, mul_assoc, mul_inv_cancel_left₀ hs0, ← eq_inv_of_mul_eq_one_right hP]`. Simplify using `[Matrix.mulVec, dotProduct]`.
-/
theorem exists_locGen (v : Pl F) : ∃ δ : E, δ ≠ 0 ∧ InD δ ∧ ∀ z, InD z → LocInt v (δ⁻¹ * z) := by
  set I := FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E)
  let e := (LinearEquiv.funUnique (Fin 1) (𝓞 E) E).symm
  let L : Submodule (𝓞 E) (Fin 1 → E) := (I : Submodule (𝓞 E) E).map e.toLinearMap
  have hL : ∀ x, x ∈ L ↔ InD (x 0) := fun x => by
    rw [inD_iff]
    exact ⟨by rintro ⟨y, hy, rfl⟩; exact hy, fun h => ⟨x 0, h, funext fun i => by rw [Subsingleton.elim i 0]; rfl⟩⟩
  have : L.IsLattice E := ⟨(FractionalIdeal.fg_of_isNoetherianRing le_rfl I).map _, by
    refine eq_top_iff.2 fun x _ => ?_
    have : x = x 0 • fun _ => (1 : E) := funext fun i => by rw [Subsingleton.elim i 0]; simp
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ((hL _).2 ((inD_iff _).2
      (FractionalIdeal.one_le_dual_one ℤ ℚ (FractionalIdeal.one_mem_one _)))))⟩
  obtain ⟨P, h1, h2⟩ := Frames.exists_rational_frame L v
  obtain ⟨s, hs, hs'⟩ := h1 0
  have hP : P.1 0 0 * (P⁻¹).1 0 0 = 1 := by
    simpa [Matrix.mul_apply] using congrFun (congrFun P.mul_inv 0) 0
  have hs0 : algebraMap F E s ≠ 0 := fun h => hs (by
    rw [show s = 0 from RingOfIntegers.coe_injective (by simpa using h)]; exact zero_mem _)
  refine ⟨algebraMap F E s * P.1 0 0, mul_ne_zero hs0 (left_ne_zero_of_mul_eq_one hP), (hL _).1 hs', fun z hz => ?_⟩
  obtain ⟨t, ht, ht'⟩ := h2 (fun _ => z) ((hL _).2 hz)
  obtain ⟨o, ho⟩ := ht' 0 trivial
  refine LocInt.of_mul hs ⟨t, ht, o, Eq.trans ?_ ho.symm⟩
  rw [mul_inv, mul_assoc, mul_inv_cancel_left₀ hs0, ← eq_inv_of_mul_eq_one_right hP]
  simp [Matrix.mulVec, dotProduct]

omit [NumberField F] in

/- English proof (translation)
Use `set G := P.1ᵀ * J * P.1.map σ with hG`. Establish `hGu : IsUnit G.det`. Rewrite using `[hG, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]`. Establish `a1 : IsUnit P.1.det` using `(Matrix.isUnit_iff_isUnit_det _).1 P.isUnit`. Establish `a2 : (P.1.map σ).det = σ P.1.det` using `(RingHom.map_det (σ : E →+* E) _).symm`.

Rewrite using `[a2]`. Conclude with `(a1.mul hJ.isUnit).mul (a1.map σ)`. Establish `hG' : G⁻¹ * G = 1` using `Matrix.nonsing_inv_mul _ hGu`. Use `⟨G⁻¹, hG', fun i j => ?_, fun i j => ?_⟩` and prove the remaining obligations. Take `⟨a, ha, ha'⟩` from `h1 i`.

Take `⟨b, hb, hb'⟩` from `h1 j`. Establish `e : ∀ (t : E) (k : Fin n), t • (fun i => P.1 i k) = P.1 *ᵥ Pi.single k t` using `fun t k => by`. Use extensionality with `l`. Simplify using `[mul_comm]`. Use `hmax _ ((hd _).1 ha' _ hb')` as an intermediate fact.

Rewrite using `[e, e, form_mulVec, ← hG, show (fun l => σ (Pi.single (M := fun _ => E) j (algebraMap F E b) l)) = Pi.single j (algebraMap F E b) from funext fun l => by`. Distinguish the cases in `el : l = j`. Substitute `el` using the available equality. Simplify using the standard rewrite rules. Simplify using `[el]] at this`.

Rewrite `this` using `[single_dotProduct, Matrix.mulVec_single]`. Express the relevant statement in the definitionally equal form `LocInt v (δ⁻¹ * (algebraMap F E a * (G i j * algebraMap F E b))) at this`. Use `LocInt.of_mul hb (LocInt.of_mul ha ?_)` and prove the remaining obligations. Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.

Take `⟨S, hS⟩` from `hL choose! f hf hf' using h2`. Establish `hmemS : ∀ x ∈ S, x ∈ L` using `fun x hx => hS ▸ Submodule.subset_span hx`. Use `v.isPrime` as an intermediate fact. Set `t : 𝓞 F` to `∏ x ∈ S, f x`. Establish `ht : t ∉ v.asIdeal`.

Introduce `hmem`. Take `⟨x, hx, hx'⟩` from `Ideal.IsPrime.prod_mem_iff.1 hmem`. Conclude with `hf x (hmemS x hx) hx'`. Establish `ht' : ∀ x ∈ L, algebraMap F E t • ((P⁻¹).1 *ᵥ x) ∈ stdLattice E n` using `fun x hx => by`. Rewrite `hx` using `[← hS]`.

Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Establish `e : t = (∏ y ∈ S.erase x, f y) * f x` using `(Finset.prod_erase_mul _ _ hx).symm`. Establish `e' : algebraMap F E t = algebraMap F E (∏ y ∈ S.erase x, f y : 𝓞 F) * algebraMap F E (f x)`. Rewrite using `[e, ← map_mul]`.

Both sides reduce to the same expression. Rewrite using `[e', mul_smul]`. Conclude with `(stdLattice E n).smul_mem (algebraMap (𝓞 F) (𝓞 E) (∏ y ∈ S.erase x, f y)) (hf' x (hmemS x hx))`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [Matrix.mulVec_add, smul_add]`.

Conclude with `add_mem hx hy`. Consider the case `smul a x _ hx => rw [Matrix.mulVec_smul, smul_comm]`. Conclude with `(stdLattice E n).smul_mem a hx`. Set `u : Fin n → E` to `(algebraMap F E t * δ) • G⁻¹ i`. Establish `hy : P.1 *ᵥ u ∈ L` using `(hd _).2 fun x hx => by`.

Take `⟨o, ho⟩` from `ht' x hx i trivial`. Establish `ex : x = P.1 *ᵥ ((P⁻¹).1 *ᵥ x)` using `by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]`. Establish `e : form σ J (P.1 *ᵥ u) x = δ * ((RingOfIntegers.mapRingHom (σ : E →+* E) o : 𝓞 E) : E)`. Rewrite using `[ex, form_mulVec, ← hG, Matrix.dotProduct_mulVec, Matrix.smul_vecMul, show G⁻¹ i ᵥ* G = Pi.single i 1 from funext fun l => by`. Rewrite using `[← Matrix.mul_apply_eq_vecMul, hG', Matrix.one_apply, Pi.single_apply]`.

Conclude with `if_congr eq_comm rfl rfl,`. Use the proof step `smul_dotProduct, single_dotProduct, one_mul, smul_eq_mul]`. Express the relevant statement in the definitionally equal form `_ = δ * σ (Algebra.linearMap (𝓞 E) E o)`. Rewrite using `[ho, Pi.smul_apply, smul_eq_mul, map_mul, σ.commutes]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Conclude with `hI _ hδ _`. Take `⟨o, ho⟩` from `hf' _ hy j trivial`. Rewrite `ho` using `[Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]`. Use `LocInt.of_mul ht ⟨f _, hf _ hy, o, Eq.trans ?_ ho.symm⟩` and prove the remaining obligations.

Simplify using `[u, mul_assoc]`.
-/
theorem gram_loc {J : Matrix (Fin n) (Fin n) E} (hJ : J.det ≠ 0) {L : Submodule (𝓞 E) (Fin n → E)} (hL : L.FG)
    {I : E → Prop} (hI : ∀ z, I z → ∀ b : 𝓞 E, I (z * b)) (hd : ∀ y, y ∈ L ↔ ∀ x ∈ L, I (form σ J y x))
    {δ : E} (hδ : I δ) (hmax : ∀ z, I z → LocInt v (δ⁻¹ * z))
    (P : GL (Fin n) E) (h1 : ∀ j, ∃ s : 𝓞 F, s ∉ v.asIdeal ∧ algebraMap F E s • (fun i => P.1 i j) ∈ L)
    (h2 : ∀ x ∈ L, ∃ s : 𝓞 F, s ∉ v.asIdeal ∧ algebraMap F E s • ((P⁻¹).1 *ᵥ x) ∈ stdLattice E n) :
    ∃ G' : Matrix (Fin n) (Fin n) E, G' * (P.1ᵀ * J * P.1.map σ) = 1 ∧
      (∀ i j, LocInt v (δ⁻¹ * (P.1ᵀ * J * P.1.map σ) i j)) ∧ ∀ i j, LocInt v (δ * G' i j) := by
  classical
  set G := P.1ᵀ * J * P.1.map σ with hG
  have hGu : IsUnit G.det := by
    rw [hG, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    have a1 : IsUnit P.1.det := (Matrix.isUnit_iff_isUnit_det _).1 P.isUnit
    have a2 : (P.1.map σ).det = σ P.1.det := (RingHom.map_det (σ : E →+* E) _).symm
    rw [a2]
    exact (a1.mul hJ.isUnit).mul (a1.map σ)
  have hG' : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul _ hGu
  refine ⟨G⁻¹, hG', fun i j => ?_, fun i j => ?_⟩
  · obtain ⟨a, ha, ha'⟩ := h1 i
    obtain ⟨b, hb, hb'⟩ := h1 j
    have e : ∀ (t : E) (k : Fin n), t • (fun i => P.1 i k) = P.1 *ᵥ Pi.single k t := fun t k => by
      ext l; simp [mul_comm]
    have := hmax _ ((hd _).1 ha' _ hb')
    rw [e, e, form_mulVec, ← hG, show (fun l => σ (Pi.single (M := fun _ => E) j (algebraMap F E b) l)) =
      Pi.single j (algebraMap F E b) from funext fun l => by
        by_cases el : l = j
        · subst el; simp
        · simp [el]] at this
    rw [single_dotProduct, Matrix.mulVec_single] at this
    change LocInt v (δ⁻¹ * (algebraMap F E a * (G i j * algebraMap F E b))) at this
    refine LocInt.of_mul hb (LocInt.of_mul ha ?_)
    convert this using 1
    ring
  · obtain ⟨S, hS⟩ := hL
    choose! f hf hf' using h2
    have hmemS : ∀ x ∈ S, x ∈ L := fun x hx => hS ▸ Submodule.subset_span hx
    have := v.isPrime
    let t : 𝓞 F := ∏ x ∈ S, f x
    have ht : t ∉ v.asIdeal := by
      intro hmem
      obtain ⟨x, hx, hx'⟩ := Ideal.IsPrime.prod_mem_iff.1 hmem
      exact hf x (hmemS x hx) hx'
    have ht' : ∀ x ∈ L, algebraMap F E t • ((P⁻¹).1 *ᵥ x) ∈ stdLattice E n := fun x hx => by
      rw [← hS] at hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        have e : t = (∏ y ∈ S.erase x, f y) * f x := (Finset.prod_erase_mul _ _ hx).symm
        have e' : algebraMap F E t = algebraMap F E (∏ y ∈ S.erase x, f y : 𝓞 F) * algebraMap F E (f x) := by
          rw [e, ← map_mul]; rfl
        rw [e', mul_smul]
        exact (stdLattice E n).smul_mem (algebraMap (𝓞 F) (𝓞 E) (∏ y ∈ S.erase x, f y)) (hf' x (hmemS x hx))
      | zero => simp
      | add x y _ _ hx hy => rw [Matrix.mulVec_add, smul_add]; exact add_mem hx hy
      | smul a x _ hx => rw [Matrix.mulVec_smul, smul_comm]; exact (stdLattice E n).smul_mem a hx
    let u : Fin n → E := (algebraMap F E t * δ) • G⁻¹ i
    have hy : P.1 *ᵥ u ∈ L := (hd _).2 fun x hx => by
      obtain ⟨o, ho⟩ := ht' x hx i trivial
      have ex : x = P.1 *ᵥ ((P⁻¹).1 *ᵥ x) := by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      have e : form σ J (P.1 *ᵥ u) x = δ * ((RingOfIntegers.mapRingHom (σ : E →+* E) o : 𝓞 E) : E) := by
        rw [ex, form_mulVec, ← hG, Matrix.dotProduct_mulVec, Matrix.smul_vecMul,
          show G⁻¹ i ᵥ* G = Pi.single i 1 from funext fun l => by
            rw [← Matrix.mul_apply_eq_vecMul, hG', Matrix.one_apply, Pi.single_apply]; exact if_congr eq_comm rfl rfl,
          smul_dotProduct, single_dotProduct, one_mul, smul_eq_mul]
        change _ = δ * σ (Algebra.linearMap (𝓞 E) E o)
        rw [ho, Pi.smul_apply, smul_eq_mul, map_mul, σ.commutes]
        ring
      rw [e]
      exact hI _ hδ _
    obtain ⟨o, ho⟩ := hf' _ hy j trivial
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at ho
    refine LocInt.of_mul ht ⟨f _, hf _ hy, o, Eq.trans ?_ ho.symm⟩
    simp [u, mul_assoc]

/- English proof (translation)
Establish `e : ∀ (K : Type) [Field K] [NumberField K] (u : Pl K) (a : Fv K u), a ∈ (algebraMap (u.adicCompletionIntegers K) (Fv K u)).range ↔ a ∈ u.adicCompletionIntegers K` using `fun _ _ _ _ a => ⟨by rintro ⟨x, rfl⟩; exact x.2, fun h => ⟨⟨a, h⟩, rfl⟩⟩`. Establish `hc` using `hB.cm`. Break down `GlobalTheory.KFinLoc.split_or_inert F E σ B hB v with ⟨⟨τ⟩⟩ | ⟨w, hw⟩` into its components or cases. Use `hasSat_of_family (O := v.adicCompletionIntegers F) (I := Bool) (fun i => cond i (splitProj τ : Fv F v ⊗[F] E →+* Fv F v) (splitProj (τ.comp σ) : Fv F v ⊗[F] E →+* Fv F v)) (fun y z h => split_ext hc τ (h true) (h false)) (fun f => ⟨(splitAlgEquiv hc τ).symm (f true, f false), fun …` and prove the remaining obligations. Consider the cases of `i`.

Conclude with `splitProj_comp_symm hc τ _`. Conclude with `splitProj_symm hc τ _`. Rewrite using `[mem_intLoc_iff_split hc τ, Bool.forall_bool]`. Simplify using `only [cond_false, cond_true, e]`. Conclude with `and_comm`.

Establish `h : w.under (𝓞 F) = v` using `(InertChart.under_eq_iff hw w).2 rfl`. Use `hasSat_of_family (O := w.adicCompletionIntegers E) (I := Unit) (fun _ => toCompl h) (fun y z e => (InertChart.toCompl_bijective hw h).1 (e ())) (fun f => ?_) _ (fun y => ?_) _` and prove the remaining obligations. Take `⟨y, hy⟩` from `(InertChart.toCompl_bijective hw h).2 (f ())`. Conclude with `⟨y, fun _ => hy⟩`. Rewrite using `[InertChart.mem_intLoc_iff hw h]`.

Conclude with `⟨fun hy _ => ⟨⟨_, hy⟩, rfl⟩, fun hy => by obtain ⟨x, hx⟩ := hy (); rw [← hx]; exact x.2⟩`.
-/
theorem hasSat_good {B : Base F E} (hB : B.IsGood σ) (v : Pl F) : HasSat (intLoc F E v) (Fin n) := by
  have e : ∀ (K : Type) [Field K] [NumberField K] (u : Pl K) (a : Fv K u),
      a ∈ (algebraMap (u.adicCompletionIntegers K) (Fv K u)).range ↔ a ∈ u.adicCompletionIntegers K :=
    fun _ _ _ _ a => ⟨by rintro ⟨x, rfl⟩; exact x.2, fun h => ⟨⟨a, h⟩, rfl⟩⟩
  have hc := hB.cm
  rcases GlobalTheory.KFinLoc.split_or_inert F E σ B hB v with ⟨⟨τ⟩⟩ | ⟨w, hw⟩
  · refine hasSat_of_family (O := v.adicCompletionIntegers F) (I := Bool)
      (fun i => cond i (splitProj τ : Fv F v ⊗[F] E →+* Fv F v) (splitProj (τ.comp σ) : Fv F v ⊗[F] E →+* Fv F v))
      (fun y z h => split_ext hc τ (h true) (h false))
      (fun f => ⟨(splitAlgEquiv hc τ).symm (f true, f false), fun i => ?_⟩) _ (fun y => ?_) _
    · cases i
      · exact splitProj_comp_symm hc τ _
      · exact splitProj_symm hc τ _
    · rw [mem_intLoc_iff_split hc τ, Bool.forall_bool]
      simp only [cond_false, cond_true, e]
      exact and_comm
  · have h : w.under (𝓞 F) = v := (InertChart.under_eq_iff hw w).2 rfl
    refine hasSat_of_family (O := w.adicCompletionIntegers E) (I := Unit) (fun _ => toCompl h)
      (fun y z e => (InertChart.toCompl_bijective hw h).1 (e ())) (fun f => ?_) _ (fun y => ?_) _
    · obtain ⟨y, hy⟩ := (InertChart.toCompl_bijective hw h).2 (f ())
      exact ⟨y, fun _ => hy⟩
    · rw [InertChart.mem_intLoc_iff hw h]
      exact ⟨fun hy _ => ⟨⟨_, hy⟩, rfl⟩, fun hy => by obtain ⟨x, hx⟩ := hy (); rw [← hx]; exact x.2⟩

/- English proof (translation)
Establish `hσ` using `cm_conj_conj hB.cm`. Establish `hL : Y.L.IsLattice E` using `hY.elim (·.lat) (·.lat)`. Take `⟨P, h1, h2⟩` from `Frames.exists_rational_frame Y.L v`. Choose the witnesses or unpack the hypotheses as in `⟨δ, h0, G', hG', b1, b2⟩ : ∃ δ : E, δ ≠ 0 ∧ ∃ G' : Matrix (Fin n) (Fin n) E, G' * (P.1ᵀ * Y.J * P.1.map σ) = 1 ∧ (∀ i j, LocInt v (δ⁻¹ * (P.1ᵀ * Y.J * P.1.map σ) i j)) ∧ ∀ i j, LocInt v (δ * G' i j) := by`. Break down `hY with h | h` into its components or cases.

Conclude with `⟨1, one_ne_zero, gram_loc hJ hL.fg (I := IsIntegral ℤ) (fun z hz b => hz.mul b.2) h.dual isIntegral_one (fun z hz => ⟨1, (Ideal.ne_top_iff_one _).1 v.isPrime.ne_top, ⟨z, hz⟩, by simp; rfl⟩) P h1 h2⟩`. Take `⟨δ, d0, d1, d2⟩` from `exists_locGen (E := E) v`. Conclude with `⟨δ, d0, gram_loc hJ hL.fg (I := InD) (fun z hz b => hz.mul b) h.dual d1 d2 P h1 h2⟩`. Take `⟨t, ht⟩` from `GlobalTheory.exists_int_add_conj_eq_one_of_base_good B hB`. Use `set G := P.1ᵀ * Y.J * P.1.map σ with hG`.

Set `ι` to `inclR (F := F) (E := E) (Fv F v)`. Set `l : (Fv F v ⊗[F] E)ˣ` to `Units.map ι.toMonoidHom (Units.mk0 (δ * ξ) (mul_ne_zero h0 hξ))⁻¹`. Establish `e : l.1 • locGram σ (ξ • Y.Jᵀ) (bc ι P) = (δ⁻¹ • Gᵀ).map ι`. Establish `e1 : locGram σ (ξ • Y.Jᵀ) (bc ι P) = (ξ • Gᵀ).map ι`. Rewrite using `[hG, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_smul, ← Matrix.smul_mul, ← Matrix.mul_assoc, Matrix.map_mul, Matrix.map_mul]`.

Both sides reduce to the same expression. Rewrite using `[e1]`. Use extensionality with `i j`. Express the relevant statement in the definitionally equal form `ι (δ * ξ)⁻¹ * ι (ξ * G j i) = ι (δ⁻¹ * G j i)`. Rewrite using `[← map_mul]`.

Use `congr 1`. Clear the denominators using the available nonvanishing facts. Use `hasIwasawa_of_frame' σ hσ rfl hh (intLoc F E v) ((1 : Fv F v) ⊗ₜ[F] (t : E)) (tmul_mem_intLoc (one_mem _) t) ?_ (fun z hz => sigR_mem_intLoc σ hz) (bc ι P) l (fun i j => ?_) ⟨(δ • G'ᵀ).map ι, fun i j => (b2 j i).mem, ?_⟩ (hasSat_good hB v) _ fun k => mem_KFin_of_frame_integral σ …` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(1 : Fv F v) ⊗ₜ[F] (t : E) + (1 : Fv F v) ⊗ₜ[F] (σ t) = 1`. Rewrite using `[← TensorProduct.tmul_add, ht]`.

Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `(l.1 • locGram σ (ξ • Y.Jᵀ) (bc ι P)) i j ∈ _`. Rewrite using `[e]`. Conclude with `(b1 j i).mem`. Rewrite using `[e, ← Matrix.map_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ h0, one_smul, ← Matrix.transpose_mul, mul_eq_one_comm.1 hG', Matrix.transpose_one, Matrix.map_one _ (map_zero _) (map_one _)]`.
-/
theorem hasIwasawa_fin' {B : Base F E} (hB : B.IsGood σ) {Y : Spc F E n} {r s : ℕ} (hY : Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s)
    (hJ : Y.J.det ≠ 0) {ξ : E} (hξ : ξ ≠ 0) (hh : ∀ i j, σ ((ξ • Y.Jᵀ) j i) = (ξ • Y.Jᵀ) i j) (v : Pl F) :
    HasIwasawa σ (dblGram finSumFinEquiv (ξ • Y.Jᵀ)) (GlobalTheory.Doubling.KFin σ _ Y.L v) := by
  have hσ := cm_conj_conj hB.cm
  have hL : Y.L.IsLattice E := hY.elim (·.lat) (·.lat)
  obtain ⟨P, h1, h2⟩ := Frames.exists_rational_frame Y.L v
  obtain ⟨δ, h0, G', hG', b1, b2⟩ : ∃ δ : E, δ ≠ 0 ∧ ∃ G' : Matrix (Fin n) (Fin n) E, G' * (P.1ᵀ * Y.J * P.1.map σ) = 1 ∧
      (∀ i j, LocInt v (δ⁻¹ * (P.1ᵀ * Y.J * P.1.map σ) i j)) ∧ ∀ i j, LocInt v (δ * G' i j) := by
    rcases hY with h | h
    · exact ⟨1, one_ne_zero, gram_loc hJ hL.fg (I := IsIntegral ℤ) (fun z hz b => hz.mul b.2) h.dual
        isIntegral_one (fun z hz => ⟨1, (Ideal.ne_top_iff_one _).1 v.isPrime.ne_top, ⟨z, hz⟩, by simp; rfl⟩) P h1 h2⟩
    · obtain ⟨δ, d0, d1, d2⟩ := exists_locGen (E := E) v
      exact ⟨δ, d0, gram_loc hJ hL.fg (I := InD) (fun z hz b => hz.mul b) h.dual d1 d2 P h1 h2⟩
  obtain ⟨t, ht⟩ := GlobalTheory.exists_int_add_conj_eq_one_of_base_good B hB
  set G := P.1ᵀ * Y.J * P.1.map σ with hG
  let ι := inclR (F := F) (E := E) (Fv F v)
  let l : (Fv F v ⊗[F] E)ˣ := Units.map ι.toMonoidHom (Units.mk0 (δ * ξ) (mul_ne_zero h0 hξ))⁻¹
  have e : l.1 • locGram σ (ξ • Y.Jᵀ) (bc ι P) = (δ⁻¹ • Gᵀ).map ι := by
    have e1 : locGram σ (ξ • Y.Jᵀ) (bc ι P) = (ξ • Gᵀ).map ι := by
      rw [hG, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_smul, ← Matrix.smul_mul,
        ← Matrix.mul_assoc, Matrix.map_mul, Matrix.map_mul]
      rfl
    rw [e1]
    ext i j
    change ι (δ * ξ)⁻¹ * ι (ξ * G j i) = ι (δ⁻¹ * G j i)
    rw [← map_mul]; congr 1; field_simp
  refine hasIwasawa_of_frame' σ hσ rfl hh (intLoc F E v) ((1 : Fv F v) ⊗ₜ[F] (t : E)) (tmul_mem_intLoc (one_mem _) t) ?_
    (fun z hz => sigR_mem_intLoc σ hz) (bc ι P) l (fun i j => ?_) ⟨(δ • G'ᵀ).map ι, fun i j => (b2 j i).mem, ?_⟩
    (hasSat_good hB v) _ fun k => mem_KFin_of_frame_integral σ _ (Frames.frame_of_rational P h1 h2) k
  · change (1 : Fv F v) ⊗ₜ[F] (t : E) + (1 : Fv F v) ⊗ₜ[F] (σ t) = 1
    rw [← TensorProduct.tmul_add, ht]
    rfl
  · change (l.1 • locGram σ (ξ • Y.Jᵀ) (bc ι P)) i j ∈ _
    rw [e]
    exact (b1 j i).mem
  · rw [e, ← Matrix.map_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ h0, one_smul, ← Matrix.transpose_mul,
      mul_eq_one_comm.1 hG', Matrix.transpose_one, Matrix.map_one _ (map_zero _) (map_one _)]

end GlobalTheory.ThK.Dbl.Hgt

end
