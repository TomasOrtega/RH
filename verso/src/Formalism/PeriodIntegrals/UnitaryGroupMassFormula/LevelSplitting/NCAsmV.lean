import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.NCDefs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.SemiAlg

noncomputable section

namespace PI.LevelKSplit.W.NCA

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory Topology
open PI.LevelKSplit PI.LevelKSplit.W.NC PI.LevelKSplit.W.SemiA
open scoped TensorProduct

section Gen

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]
  [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]

/- English proof (translation)
Use `haveI := hμ`. Use `set U : AddSubgroup V := p.ker with hUdef`. Establish `hWc : IsClosed (W : Set V)`. Establish `e : (W : Set V) = {v | p v = v}` using `Set.ext fun v => hW v`. Rewrite using `[e]`.

Conclude with `isClosed_eq hp continuous_id`. Establish `hUc : IsClosed (U : Set V)`. Establish `e : (U : Set V) = {v | p v = 0}` using `Set.ext fun v => by simp [hUdef, AddMonoidHom.mem_ker]`. Rewrite using `[e]`. Conclude with `isClosed_eq hp continuous_const`.

Use `haveI : LocallyCompactSpace W := hWc.locallyCompactSpace`. Use `haveI : LocallyCompactSpace U := hUc.locallyCompactSpace`. Use `haveI : BorelSpace W := Subtype.borelSpace (W : Set V)`. Use `haveI : BorelSpace U := Subtype.borelSpace (U : Set V)`. Use `haveI : SecondCountableTopology W := TopologicalSpace.Subtype.secondCountableTopology (W : Set V)`.

Use `haveI : SecondCountableTopology U := TopologicalSpace.Subtype.secondCountableTopology (U : Set V)`. Use `haveI : BorelSpace (W × U) := Prod.borelSpace`. Establish `hpW : ∀ w : W, p w = w` using `fun w => (hW w).1 w.2`. Establish `hfc : Continuous f`. Apply `continuous_induced_rng.2` to reduce the goal to its premises.

Establish `e : (Subtype.val ∘ f : W → V) = fun w : W => g (w : V)` using `funext hf`. Rewrite using `[e]`. Conclude with `hg.comp continuous_subtype_val`. Set `Φ : W × U →+ V` to `W.subtype.comp (AddMonoidHom.fst W U) + U.subtype.comp (AddMonoidHom.snd W U)`. Establish `hΦ : ∀ x : W × U, Φ x = (x.1 : V) + (x.2 : V)` using `fun x => rfl`.

Establish `hΦc : Continuous Φ`. Establish `e : (Φ : W × U → V) = fun x => (x.1 : V) + (x.2 : V)` using `funext hΦ`. Rewrite using `[e]`. Conclude with `(continuous_subtype_val.comp continuous_fst).add (continuous_subtype_val.comp continuous_snd)`. Set `Ψ : V → W × U` to `fun v => (⟨p v, (hW _).2 (hpp v)⟩, ⟨v - p v, by simp [hUdef, AddMonoidHom.mem_ker, map_sub, hpp]⟩)`.

Establish `hΨc : Continuous Ψ` using `(hp.subtype_mk fun v => (hW _).2 (hpp v)).prodMk ((continuous_id.sub hp).subtype_mk fun v => by`. Simplify using `[hUdef, AddMonoidHom.mem_ker, map_sub, hpp])`. Establish `hΦΨ : ∀ v, Φ (Ψ v) = v` using `fun v => by`. Rewrite using `[hΦ]`. Simplify using `[Ψ]`.

Establish `hΨΦ : ∀ x, Ψ (Φ x) = x`. Introduce and unpack `⟨w, u⟩`. Establish `hu : p u = 0` using `u.2`. Establish `hpx : p (Φ (w, u)) = w` using `by rw [hΦ, map_add, hpW, hu, add_zero]`. Apply `Prod.ext` to reduce the goal to its premises.

Apply `Subtype.ext show p (Φ (w, u)) = w` to reduce the goal to its premises. Conclude with `hpx`. Apply `Subtype.ext show Φ (w, u) - p (Φ (w, u)) = u` to reduce the goal to its premises. Rewrite using `[hpx, hΦ]`. Simplify using the standard rewrite rules.

Establish `hΦs : Function.Surjective Φ` using `fun v => ⟨Ψ v, hΦΨ v⟩`. Set `e : (W × U) ≃ₜ V` to `{ toFun := Φ, invFun := Ψ, left_inv := hΨΦ, right_inv := hΦΨ, continuous_toFun := hΦc, continuous_invFun := hΨc }`. Set `ν : Measure U` to `Measure.addHaar`. Use `set P : Measure (W × U) := μ.prod ν with hP`. Use `haveI hPH : P.IsAddHaarMeasure := by rw [hP]; infer_instance`.

Establish `hHaar : (P.map Φ).IsAddHaarMeasure` using `Measure.isAddHaarMeasure_map P Φ hΦc hΦs e.isClosedEmbedding.tendsto_cocompact`. Establish `hmap` using `hV _ hHaar`. Establish `hgΦ : (g : V → V) ∘ Φ = Φ ∘ Prod.map f id`. Use function extensionality and compare the values at `x`. Take `⟨w, u⟩` from `x`.

Simplify using `only [Function.comp, Prod.map, id, hΦ, map_add, hgU u u.2, hf]`. Establish `hfm : Measurable f` using `hfc.measurable`. Establish `hPm : Measurable (Prod.map f (id : U → U))` using `hfm.prodMap measurable_id`. Rewrite `hmap` using `[Measure.map_map hg.measurable hΦc.measurable, hgΦ, ← Measure.map_map hΦc.measurable hPm]`. Establish `hinv : ∀ Q : Measure (W × U), (Q.map Φ).map Ψ = Q`.

Introduce `Q`. Rewrite using `[Measure.map_map hΨc.measurable hΦc.measurable]`. Establish `e2 : Ψ ∘ Φ = id` using `funext hΨΦ`. Rewrite using `[e2, Measure.map_id]`. Establish `hP' : P.map (Prod.map f id) = P`.

Establish `h2` using `congrArg (fun Q => Q.map Ψ) hmap`. Simplify `h2` using `only [hinv]`. Take `⟨K, hKc, hKn⟩` from `exists_compact_mem_nhds (0 : U)`. Establish `hK0 : ν K ≠ 0` using `(Measure.measure_pos_of_mem_nhds ν hKn).ne'`. Establish `hKt : ν K ≠ ⊤` using `hKc.measure_lt_top.ne`.

Use extensionality with `A hA`. Rewrite using `[Measure.map_apply hfm hA]`. Establish `h1 : (P.map (Prod.map f id)) (A ×ˢ K) = P (A ×ˢ K)` using `by rw [hP']`. Rewrite `h1` using `[Measure.map_apply hPm (hA.prod hKc.measurableSet)]`. Establish `hpre : Prod.map f id ⁻¹' (A ×ˢ K) = (f ⁻¹' A) ×ˢ K`.

Use extensionality with `x`. Simplify using the standard rewrite rules. Rewrite `h1` using `[hpre, hP, Measure.prod_prod, Measure.prod_prod]`. Establish `h2` using `congrArg (fun t => t / ν K) h1`. Simplify using `only [ENNReal.mul_div_cancel_right hK0 hKt] at h2`.

Conclude with `h2`.
-/
theorem map_eq_of_split (p : V →+ V) (hp : Continuous p) (hpp : ∀ v, p (p v) = p v)
    (W : AddSubgroup V) (hW : ∀ v, v ∈ W ↔ p v = v)
    (g : V →+ V) (hg : Continuous g) (hgU : ∀ u, p u = 0 → g u = u)
    (hV : ∀ μ : Measure V, μ.IsAddHaarMeasure → μ.map g = μ)
    (f : W → W) (hf : ∀ w, (f w : V) = g w) (μ : Measure W) (hμ : μ.IsAddHaarMeasure) :
    μ.map f = μ := by
  classical
  haveI := hμ
  set U : AddSubgroup V := p.ker with hUdef
  have hWc : IsClosed (W : Set V) := by
    have e : (W : Set V) = {v | p v = v} := Set.ext fun v => hW v
    rw [e]
    exact isClosed_eq hp continuous_id
  have hUc : IsClosed (U : Set V) := by
    have e : (U : Set V) = {v | p v = 0} := Set.ext fun v => by simp [hUdef, AddMonoidHom.mem_ker]
    rw [e]
    exact isClosed_eq hp continuous_const
  haveI : LocallyCompactSpace W := hWc.locallyCompactSpace
  haveI : LocallyCompactSpace U := hUc.locallyCompactSpace
  haveI : BorelSpace W := Subtype.borelSpace (W : Set V)
  haveI : BorelSpace U := Subtype.borelSpace (U : Set V)
  haveI : SecondCountableTopology W := TopologicalSpace.Subtype.secondCountableTopology (W : Set V)
  haveI : SecondCountableTopology U := TopologicalSpace.Subtype.secondCountableTopology (U : Set V)
  haveI : BorelSpace (W × U) := Prod.borelSpace
  have hpW : ∀ w : W, p w = w := fun w => (hW w).1 w.2
  have hfc : Continuous f := by
    apply continuous_induced_rng.2
    have e : (Subtype.val ∘ f : W → V) = fun w : W => g (w : V) := funext hf
    rw [e]
    exact hg.comp continuous_subtype_val
  let Φ : W × U →+ V := W.subtype.comp (AddMonoidHom.fst W U) + U.subtype.comp (AddMonoidHom.snd W U)
  have hΦ : ∀ x : W × U, Φ x = (x.1 : V) + (x.2 : V) := fun x => rfl
  have hΦc : Continuous Φ := by
    have e : (Φ : W × U → V) = fun x => (x.1 : V) + (x.2 : V) := funext hΦ
    rw [e]
    exact (continuous_subtype_val.comp continuous_fst).add (continuous_subtype_val.comp continuous_snd)
  let Ψ : V → W × U := fun v => (⟨p v, (hW _).2 (hpp v)⟩,
    ⟨v - p v, by simp [hUdef, AddMonoidHom.mem_ker, map_sub, hpp]⟩)
  have hΨc : Continuous Ψ :=
    (hp.subtype_mk fun v => (hW _).2 (hpp v)).prodMk ((continuous_id.sub hp).subtype_mk fun v => by
      simp [hUdef, AddMonoidHom.mem_ker, map_sub, hpp])
  have hΦΨ : ∀ v, Φ (Ψ v) = v := fun v => by
    rw [hΦ]
    simp [Ψ]
  have hΨΦ : ∀ x, Ψ (Φ x) = x := by
    rintro ⟨w, u⟩
    have hu : p u = 0 := u.2
    have hpx : p (Φ (w, u)) = w := by rw [hΦ, map_add, hpW, hu, add_zero]
    apply Prod.ext
    · apply Subtype.ext
      show p (Φ (w, u)) = w
      exact hpx
    · apply Subtype.ext
      show Φ (w, u) - p (Φ (w, u)) = u
      rw [hpx, hΦ]
      simp
  have hΦs : Function.Surjective Φ := fun v => ⟨Ψ v, hΦΨ v⟩
  let e : (W × U) ≃ₜ V :=
    { toFun := Φ, invFun := Ψ, left_inv := hΨΦ, right_inv := hΦΨ,
      continuous_toFun := hΦc, continuous_invFun := hΨc }
  let ν : Measure U := Measure.addHaar
  set P : Measure (W × U) := μ.prod ν with hP
  haveI hPH : P.IsAddHaarMeasure := by rw [hP]; infer_instance
  have hHaar : (P.map Φ).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map P Φ hΦc hΦs e.isClosedEmbedding.tendsto_cocompact
  have hmap := hV _ hHaar
  have hgΦ : (g : V → V) ∘ Φ = Φ ∘ Prod.map f id := by
    funext x
    obtain ⟨w, u⟩ := x
    simp only [Function.comp, Prod.map, id, hΦ, map_add, hgU u u.2, hf]
  have hfm : Measurable f := hfc.measurable
  have hPm : Measurable (Prod.map f (id : U → U)) := hfm.prodMap measurable_id
  rw [Measure.map_map hg.measurable hΦc.measurable, hgΦ,
    ← Measure.map_map hΦc.measurable hPm] at hmap
  have hinv : ∀ Q : Measure (W × U), (Q.map Φ).map Ψ = Q := by
    intro Q
    rw [Measure.map_map hΨc.measurable hΦc.measurable]
    have e2 : Ψ ∘ Φ = id := funext hΨΦ
    rw [e2, Measure.map_id]
  have hP' : P.map (Prod.map f id) = P := by
    have h2 := congrArg (fun Q => Q.map Ψ) hmap
    simpa only [hinv] using h2
  obtain ⟨K, hKc, hKn⟩ := exists_compact_mem_nhds (0 : U)
  have hK0 : ν K ≠ 0 := (Measure.measure_pos_of_mem_nhds ν hKn).ne'
  have hKt : ν K ≠ ⊤ := hKc.measure_lt_top.ne
  ext A hA
  rw [Measure.map_apply hfm hA]
  have h1 : (P.map (Prod.map f id)) (A ×ˢ K) = P (A ×ˢ K) := by rw [hP']
  rw [Measure.map_apply hPm (hA.prod hKc.measurableSet)] at h1
  have hpre : Prod.map f id ⁻¹' (A ×ˢ K) = (f ⁻¹' A) ×ˢ K := by
    ext x
    simp
  rw [hpre, hP, Measure.prod_prod, Measure.prod_prod] at h1
  have h2 := congrArg (fun t => t / ν K) h1
  simp only [ENNReal.mul_div_cancel_right hK0 hKt] at h2
  exact h2

end Gen

namespace DatL

open PI.LevelKSplit.W.SemiG PI.LevelKSplit.W.SemiG.Dat

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
  {D : PI.LevelKSplit.W.SemiG.Dat A n r}

/- English proof (translation)
Rewrite using `[← Dat.hL_apply, Dat.pXv, LinearMap.sum_apply, map_sum]`. Simplify using `only [LinearMap.smulRight_apply, map_smul, smul_eq_mul, Dat.hL_apply, H.ef, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]`.
-/
theorem h_e_pXv (H : D.Hyp) (b : Fin r) (v : n → A) : D.h (D.e b) (D.pXv v) = D.h (D.e b) v := by
  rw [← Dat.hL_apply, Dat.pXv, LinearMap.sum_apply, map_sum]
  simp only [LinearMap.smulRight_apply, map_smul, smul_eq_mul, Dat.hL_apply, H.ef, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/- English proof (translation)
Establish `hfe : ∀ a, D.h (D.f b) (D.e a) = if b = a then 1 else 0`. Introduce `a`. Rewrite using `[Dat.h_symm H (D.e a) (D.f b), H.ef]`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality.

Simplify using the standard rewrite rules. Rewrite using `[if_neg hab, if_neg (Ne.symm hab), map_zero]`. Rewrite using `[← Dat.hL_apply, Dat.pX, LinearMap.sum_apply, map_sum]`. Simplify using `only [LinearMap.smulRight_apply, map_smul, smul_eq_mul, Dat.hL_apply, hfe, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]`.
-/
theorem h_f_pX (H : D.Hyp) (b : Fin r) (v : n → A) : D.h (D.f b) (D.pX v) = D.h (D.f b) v := by
  have hfe : ∀ a, D.h (D.f b) (D.e a) = if b = a then 1 else 0 := by
    intro a
    rw [Dat.h_symm H (D.e a) (D.f b), H.ef]
    by_cases hab : a = b
    · subst hab; simp
    · rw [if_neg hab, if_neg (Ne.symm hab), map_zero]
  rw [← Dat.hL_apply, Dat.pX, LinearMap.sum_apply, map_sum]
  simp only [LinearMap.smulRight_apply, map_smul, smul_eq_mul, Dat.hL_apply, hfe, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/- English proof (translation)
Rewrite using `[← Dat.hL_apply, Dat.pXv, LinearMap.sum_apply, map_sum]`. Simplify using `only [LinearMap.smulRight_apply, map_smul, smul_eq_mul, Dat.hL_apply, H.ff, mul_zero, Finset.sum_const_zero]`.
-/
theorem h_f_pXv (H : D.Hyp) (b : Fin r) (v : n → A) : D.h (D.f b) (D.pXv v) = 0 := by
  rw [← Dat.hL_apply, Dat.pXv, LinearMap.sum_apply, map_sum]
  simp only [LinearMap.smulRight_apply, map_smul, smul_eq_mul, Dat.hL_apply, H.ff, mul_zero,
    Finset.sum_const_zero]

variable (D) in

def pL : (n → A) →ₗ[A] (n → A) := LinearMap.id - D.pX - D.pXv

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pL_apply (v : n → A) : pL D v = v - D.pX v - D.pXv v := rfl

/- English proof (translation)
Establish `h0 : D.h (D.e b) (D.pX v) = 0`. Rewrite using `[← Dat.hL_apply, Dat.pX, LinearMap.sum_apply, map_sum]`. Simplify using `only [LinearMap.smulRight_apply, map_smul, smul_eq_mul, Dat.hL_apply, H.ee, mul_zero, Finset.sum_const_zero]`. Rewrite using `[pL_apply, ← Dat.hL_apply, map_sub, map_sub]`. Simplify using `only [Dat.hL_apply]`.

Rewrite using `[h0, h_e_pXv H]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem h_e_pL (H : D.Hyp) (b : Fin r) (v : n → A) : D.h (D.e b) (pL D v) = 0 := by
  have h0 : D.h (D.e b) (D.pX v) = 0 := by
    rw [← Dat.hL_apply, Dat.pX, LinearMap.sum_apply, map_sum]
    simp only [LinearMap.smulRight_apply, map_smul, smul_eq_mul, Dat.hL_apply, H.ee, mul_zero,
      Finset.sum_const_zero]
  rw [pL_apply, ← Dat.hL_apply, map_sub, map_sub]
  simp only [Dat.hL_apply]
  rw [h0, h_e_pXv H]
  ring

/- English proof (translation)
Rewrite using `[pL_apply, ← Dat.hL_apply, map_sub, map_sub]`. Simplify using `only [Dat.hL_apply]`. Rewrite using `[h_f_pX H, h_f_pXv H]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem h_f_pL (H : D.Hyp) (b : Fin r) (v : n → A) : D.h (D.f b) (pL D v) = 0 := by
  rw [pL_apply, ← Dat.hL_apply, map_sub, map_sub]
  simp only [Dat.hL_apply]
  rw [h_f_pX H, h_f_pXv H]
  ring

/- English proof (translation)
Establish `h1 : D.pX v = 0`. Simplify using `only [Dat.pX, LinearMap.sum_apply, LinearMap.smulRight_apply, Dat.hL_apply, hf, zero_smul, Finset.sum_const_zero]`. Establish `h2 : D.pXv v = 0`. Simplify using `only [Dat.pXv, LinearMap.sum_apply, LinearMap.smulRight_apply, Dat.hL_apply, he, zero_smul, Finset.sum_const_zero]`. Rewrite using `[pL_apply, h1, h2, sub_zero, sub_zero]`.
-/
theorem pL_of {v : n → A} (he : ∀ a, D.h (D.e a) v = 0) (hf : ∀ a, D.h (D.f a) v = 0) :
    pL D v = v := by
  have h1 : D.pX v = 0 := by
    simp only [Dat.pX, LinearMap.sum_apply, LinearMap.smulRight_apply, Dat.hL_apply, hf, zero_smul,
      Finset.sum_const_zero]
  have h2 : D.pXv v = 0 := by
    simp only [Dat.pXv, LinearMap.sum_apply, LinearMap.smulRight_apply, Dat.hL_apply, he, zero_smul,
      Finset.sum_const_zero]
  rw [pL_apply, h1, h2, sub_zero, sub_zero]

/- English proof (translation)
The claim follows from `pL_of (fun a => h_e_pL H a v) (fun a => h_f_pL H a v)`.
-/
theorem pL_pL (H : D.Hyp) (v : n → A) : pL D (pL D v) = pL D v :=
  pL_of (fun a => h_e_pL H a v) (fun a => h_f_pL H a v)

/- English proof (translation)
Establish `hu' : u = D.pX u + D.pXv u`. Rewrite `hu` using `[pL_apply, sub_sub, sub_eq_zero]`. Conclude with `hu`. Rewrite using `[hu', map_add]`. Use `congr 1`.

Simplify using `only [Dat.pX, LinearMap.sum_apply, LinearMap.smulRight_apply, map_sum, map_smul, hSe]`. Simplify using `only [Dat.pXv, LinearMap.sum_apply, LinearMap.smulRight_apply, map_sum, map_smul, hSf]`.
-/
theorem fix_of_pL_zero {S : (n → A) →ₗ[A] (n → A)} (hSe : ∀ a, S (D.e a) = D.e a)
    (hSf : ∀ a, S (D.f a) = D.f a) {u : n → A} (hu : pL D u = 0) : S u = u := by
  have hu' : u = D.pX u + D.pXv u := by
    rw [pL_apply, sub_sub, sub_eq_zero] at hu
    exact hu
  rw [hu', map_add]
  congr 1
  · simp only [Dat.pX, LinearMap.sum_apply, LinearMap.smulRight_apply, map_sum, map_smul, hSe]
  · simp only [Dat.pXv, LinearMap.sum_apply, LinearMap.smulRight_apply, map_sum, map_smul, hSf]

end DatL

section Wp

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ} {P : Frame E M r} {T : F}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨he, hf⟩`. Conclude with `DatL.pL_of (fun a => he a) (fun a => hf a)`. Introduce `h`. Express the relevant statement in the definitionally equal form `(∀ a, _) ∧ (∀ a, _)`.

Use `⟨fun a => ?_, fun a => ?_⟩` and prove the remaining obligations. Establish `h1` using `DatL.h_e_pL H a v`. Rewrite `h1` using `[h]`. Conclude with `h1`. Establish `h1` using `DatL.h_f_pL H a v`.

Rewrite `h1` using `[h]`. Conclude with `h1`.
-/
theorem mem_Wp_iff (H : (datR R σ J P T).Hyp) (v : Fin M → R ⊗[F] E) :
    v ∈ Wp R σ J P ↔ DatL.pL (datR R σ J P T) v = v := by
  constructor
  · rintro ⟨he, hf⟩
    exact DatL.pL_of (fun a => he a) (fun a => hf a)
  · intro h
    change (∀ a, _) ∧ (∀ a, _)
    refine ⟨fun a => ?_, fun a => ?_⟩
    · have h1 := DatL.h_e_pL H a v
      rw [h] at h1
      exact h1
    · have h1 := DatL.h_f_pL H a v
      rw [h] at h1
      exact h1

/- English proof (translation)
Take `⟨he, hf⟩` from `hw`. Establish `hfix : ∀ i, lin R σ J h (ratV (F` using `F) R (tupH P i)) = ratV (F := F) R (tupH P i) := fun i => congrFun (MulAction.mem_stabilizer_iff.mp hh) i`. Express the relevant statement in the definitionally equal form `(∀ a, _) ∧ (∀ a, _)`. Use `⟨fun a => ?_, fun a => ?_⟩` and prove the remaining obligations. Establish `h1` using `hfix (Fin.castAdd r (Fin.castSucc a))`.

Simplify using `only [tupH, F0, Fin.append_left, Fin.snoc_castSucc] at h1`. Rewrite using `[← h1, hR_lin]`. Conclude with `he a`. Establish `h1` using `hfix (Fin.natAdd (r + 1) a)`. Simplify using `only [tupH, Fin.append_right] at h1`.

Rewrite using `[← h1, hR_lin]`. Conclude with `hf a`.
-/
theorem lin_mem_Wp {h : HA R σ J} (hh : h ∈ Hsub R σ J P) {w : Fin M → R ⊗[F] E}
    (hw : w ∈ Wp R σ J P) : lin R σ J h w ∈ Wp R σ J P := by
  obtain ⟨he, hf⟩ := hw
  have hfix : ∀ i, lin R σ J h (ratV (F := F) R (tupH P i)) = ratV (F := F) R (tupH P i) :=
    fun i => congrFun (MulAction.mem_stabilizer_iff.mp hh) i
  change (∀ a, _) ∧ (∀ a, _)
  refine ⟨fun a => ?_, fun a => ?_⟩
  · have h1 := hfix (Fin.castAdd r (Fin.castSucc a))
    simp only [tupH, F0, Fin.append_left, Fin.snoc_castSucc] at h1
    rw [← h1, hR_lin]
    exact he a
  · have h1 := hfix (Fin.natAdd (r + 1) a)
    simp only [tupH, Fin.append_right] at h1
    rw [← h1, hR_lin]
    exact hf a

def linWp {h : HA R σ J} (hh : h ∈ Hsub R σ J P) (w : Wp R σ J P) : Wp R σ J P :=
  ⟨lin R σ J h w, lin_mem_Wp hh w.2⟩

end Wp

section Af

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ} {P : Frame E M r} {T : F}

/- English proof (translation)
Use `haveI := PI.LevelKSplit.W.SC.finite_adeles_secondCountable F`. Use `infer_instance`.
-/
theorem sc_tens : SecondCountableTopology (Af F ⊗[F] E) := by
  haveI := PI.LevelKSplit.W.SC.finite_adeles_secondCountable F
  infer_instance

/- English proof (translation)
Use `haveI := sc_tens (F := F) (E := E)`. Establish `H` using `datR_hyp (R := Af F) hσσ hJ hP`. Establish `hfix : ∀ i, lin (Af F) σ J h (ratV (F` using `F) (Af F) (tupH P i)) = ratV (F := F) (Af F) (tupH P i) := fun i => congrFun (MulAction.mem_stabilizer_iff.mp hh) i`. Establish `hSe : ∀ a, lin (Af F) σ J h ((datR (Af F) σ J P T).e a) = (datR (Af F) σ J P T).e a`. Introduce `a`.

Establish `h1` using `hfix (Fin.castAdd r (Fin.castSucc a))`. Simplify using `only [tupH, F0, Fin.append_left, Fin.snoc_castSucc] at h1`. Conclude with `h1`. Establish `hSf : ∀ a, lin (Af F) σ J h ((datR (Af F) σ J P T).f a) = (datR (Af F) σ J P T).f a`. Introduce `a`.

Establish `h1` using `hfix (Fin.natAdd (r + 1) a)`. Simplify using `only [tupH, Fin.append_right] at h1`. Conclude with `h1`. Use `map_eq_of_split (DatL.pL (datR (Af F) σ J P T)).toAddMonoidHom ?_ (fun v => DatL.pL_pL H v) (Wp (Af F) σ J P) (fun v => mem_Wp_iff H v) (lin (Af F) σ J h).toAddMonoidHom ?_ (fun u hu => DatL.fix_of_pL_zero hSe hSf hu) (fun ν hν => hV hJ hσσ h ν hν) (linWp hh) (fun w => rfl) μ hμ` and prove the remaining obligations. Conclude with `LinearMap.continuous_on_pi _`.

Conclude with `LinearMap.continuous_on_pi _`.
-/
theorem wp_map (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hP : P.IsStd σ J T)
    (hV : PI.LevelKSplit.W.CD.ModV F E σ M J) {h : HA (Af F) σ J} (hh : h ∈ Hsub (Af F) σ J P)
    (μ : Measure (Wp (Af F) σ J P)) (hμ : μ.IsAddHaarMeasure) : μ.map (linWp hh) = μ := by
  haveI := sc_tens (F := F) (E := E)
  have H := datR_hyp (R := Af F) hσσ hJ hP
  have hfix : ∀ i, lin (Af F) σ J h (ratV (F := F) (Af F) (tupH P i)) = ratV (F := F) (Af F) (tupH P i) :=
    fun i => congrFun (MulAction.mem_stabilizer_iff.mp hh) i
  have hSe : ∀ a, lin (Af F) σ J h ((datR (Af F) σ J P T).e a) = (datR (Af F) σ J P T).e a := by
    intro a
    have h1 := hfix (Fin.castAdd r (Fin.castSucc a))
    simp only [tupH, F0, Fin.append_left, Fin.snoc_castSucc] at h1
    exact h1
  have hSf : ∀ a, lin (Af F) σ J h ((datR (Af F) σ J P T).f a) = (datR (Af F) σ J P T).f a := by
    intro a
    have h1 := hfix (Fin.natAdd (r + 1) a)
    simp only [tupH, Fin.append_right] at h1
    exact h1
  refine map_eq_of_split (DatL.pL (datR (Af F) σ J P T)).toAddMonoidHom ?_
    (fun v => DatL.pL_pL H v) (Wp (Af F) σ J P) (fun v => mem_Wp_iff H v)
    (lin (Af F) σ J h).toAddMonoidHom ?_ (fun u hu => DatL.fix_of_pL_zero hSe hSf hu)
    (fun ν hν => hV hJ hσσ h ν hν) (linWp hh) (fun w => rfl) μ hμ
  · exact LinearMap.continuous_on_pi _
  · exact LinearMap.continuous_on_pi _

end Af

end PI.LevelKSplit.W.NCA
