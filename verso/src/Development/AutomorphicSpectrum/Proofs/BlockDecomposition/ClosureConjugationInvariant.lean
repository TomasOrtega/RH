import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

noncomputable section

namespace GlobalTheory.CompanionTheory.PlaneSA.MemConj

variable {F : Type} [Field F] [NumberField F] {d β : F}

/- English proof (translation)
Consider the cases of `u with`. Consider the case `inl w`. Conclude with `(Function.surjective_eval w).denseRange.comp (InfiniteAdeleRing.denseRange_algebraMap F) (continuous_apply w)`. Consider the case `inr v => exact HeightOneSpectrum.denseRange_algebraMap (K := F) v`.
-/
theorem denseRange_algebraMap_Kp (u : Pl F) : DenseRange (algebraMap F (Kp u)) := by
  cases u with
  | inl w =>
    exact (Function.surjective_eval w).denseRange.comp (InfiniteAdeleRing.denseRange_algebraMap F)
      (continuous_apply w)
  | inr v => exact HeightOneSpectrum.denseRange_algebraMap (K := F) v

def qinv {K : Type} [Field K] [Algebra F K] (e : Q d β K) : Q d β K :=
  algebraMap K (Q d β K) (qn e)⁻¹ * star e

/- English proof (translation)
Establish `h1 : e * algebraMap K (Q d β K) (qn e)⁻¹ = algebraMap K (Q d β K) (qn e)⁻¹ * e` using `(Algebra.commutes _ _).symm`. Rewrite using `[qinv, ← mul_assoc, h1, mul_assoc, mul_star_eq, ← map_mul, inv_mul_cancel₀ h, map_one]`.
-/
theorem mul_qinv {K : Type} [Field K] [Algebra F K] {e : Q d β K} (h : qn e ≠ 0) :
    e * qinv e = 1 := by
  have h1 : e * algebraMap K (Q d β K) (qn e)⁻¹ = algebraMap K (Q d β K) (qn e)⁻¹ * e :=
    (Algebra.commutes _ _).symm
  rw [qinv, ← mul_assoc, h1, mul_assoc, mul_star_eq, ← map_mul, inv_mul_cancel₀ h, map_one]

/- English proof (translation)
Rewrite using `[qinv, mul_assoc, star_mul_eq, ← map_mul, inv_mul_cancel₀ h, map_one]`.
-/
theorem qinv_mul {K : Type} [Field K] [Algebra F K] {e : Q d β K} (h : qn e ≠ 0) :
    qinv e * e = 1 := by
  rw [qinv, mul_assoc, star_mul_eq, ← map_mul, inv_mul_cancel₀ h, map_one]

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
theorem qinv_unique {K : Type} [Field K] [Algebra F K] {e e' : Q d β K} (h : qn e ≠ 0)
    (h' : e' * e = 1) : qinv e = e' := by
  calc qinv e = (e' * e) * qinv e := by rw [h', one_mul]
    _ = e' := by rw [mul_assoc, mul_qinv h, mul_one]

/- English proof (translation)
Use `⟨?_, fun u hu => ?_⟩` and prove the remaining obligations. Rewrite using `[qn_mul, qn_mul, hh.1, mul_one, ← qn_mul, hpq, qn_one]`. Rewrite using `[map_mul, map_mul, hh.2 u hu, mul_one, ← map_mul, hpq, map_one]`.
-/
theorem conj_mem_SuppAt {T : Set (Pl F)} {p q h : Q d β (AF F)} (hpq : p * q = 1)
    (hh : h ∈ SuppAt d β T) : p * h * q ∈ SuppAt d β T := by
  refine ⟨?_, fun u hu => ?_⟩
  · rw [qn_mul, qn_mul, hh.1, mul_one, ← qn_mul, hpq, qn_one]
  · rw [map_mul, map_mul, hh.2 u hu, mul_one, ← map_mul, hpq, map_one]

/- English proof (translation)
Take `⟨γ, hγ, h, hh, rfl⟩` from `hx`. Establish `r1 : (rat δ : Q d β (AF F)) * rat δ' = 1` using `by rw [← map_mul, h1, map_one]`. Establish `r2 : (rat δ' : Q d β (AF F)) * rat δ = 1` using `by rw [← map_mul, h2, map_one]`. Use `⟨δ * γ * δ', ?_, rat δ * h * rat δ', conj_mem_SuppAt r1 hh, ?_⟩` and prove the remaining obligations. Rewrite using `[qn_mul, qn_mul, hγ, mul_one, ← qn_mul, h1, qn_one]`.

Rewrite using `[map_mul, map_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[r2, mul_one]`. Simplify using `only [mul_assoc]`. Use `_ = rat δ * rat γ * rat δ' * (rat δ * h * rat δ') := by simp only [mul_assoc]`.
-/
theorem conj_mem_SAQ (s : Pl F) {δ δ' : Q d β F} (h1 : δ * δ' = 1) (h2 : δ' * δ = 1)
    {x : Q d β (AF F)} (hx : x ∈ SAQ d β s) :
    (rat δ : Q d β (AF F)) * x * rat δ' ∈ SAQ d β s := by
  obtain ⟨γ, hγ, h, hh, rfl⟩ := hx
  have r1 : (rat δ : Q d β (AF F)) * rat δ' = 1 := by rw [← map_mul, h1, map_one]
  have r2 : (rat δ' : Q d β (AF F)) * rat δ = 1 := by rw [← map_mul, h2, map_one]
  refine ⟨δ * γ * δ', ?_, rat δ * h * rat δ', conj_mem_SuppAt r1 hh, ?_⟩
  · rw [qn_mul, qn_mul, hγ, mul_one, ← qn_mul, h1, qn_one]
  · rw [map_mul, map_mul]
    calc (rat δ : Q d β (AF F)) * (rat γ * h) * rat δ'
        = rat δ * rat γ * (rat δ' * rat δ) * h * rat δ' := by
          rw [r2, mul_one]; simp only [mul_assoc]
      _ = rat δ * rat γ * rat δ' * (rat δ * h * rat δ') := by simp only [mul_assoc]

/- English proof (translation)
Establish `hc : Continuous fun y : Q d β (AF F) => (rat δ : Q d β (AF F)) * y * rat δ'` using `(continuous_const.mul continuous_id).mul continuous_const`. Establish `hsub : closure (SAQ d β s) ⊆ (fun y : Q d β (AF F) => (rat δ : Q d β (AF F)) * y * rat δ') ⁻¹' closure (SAQ d β s)`. Use `closure_minimal (fun y hy => subset_closure ?_) (isClosed_closure.preimage hc)` and prove the remaining obligations. Conclude with `conj_mem_SAQ s h1 h2 hy`. Conclude with `hsub hx`.
-/
theorem conj_mem_closure (s : Pl F) {δ δ' : Q d β F} (h1 : δ * δ' = 1) (h2 : δ' * δ = 1)
    {x : Q d β (AF F)} (hx : x ∈ closure (SAQ d β s)) :
    (rat δ : Q d β (AF F)) * x * rat δ' ∈ closure (SAQ d β s) := by
  have hc : Continuous fun y : Q d β (AF F) => (rat δ : Q d β (AF F)) * y * rat δ' :=
    (continuous_const.mul continuous_id).mul continuous_const
  have hsub : closure (SAQ d β s) ⊆
      (fun y : Q d β (AF F) => (rat δ : Q d β (AF F)) * y * rat δ') ⁻¹' closure (SAQ d β s) := by
    refine closure_minimal (fun y hy => subset_closure ?_) (isClosed_closure.preimage hc)
    exact conj_mem_SAQ s h1 h2 hy
  exact hsub hx

def psi (w : Pl F) (y : Q d β (Kp w)) : Q d β (AF F) :=
  ⟨1 + inc w (y.re - 1), inc w y.imI, inc w y.imJ, inc w y.imK⟩

/- English proof (translation)
Rewrite using `[continuous_q_iff]`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `continuous_const.add ((continuous_inc w).comp (continuous_re.sub continuous_const))`. Conclude with `(continuous_inc w).comp continuous_imI`. Conclude with `(continuous_inc w).comp continuous_imJ`.

Conclude with `(continuous_inc w).comp continuous_imK`.
-/
theorem continuous_psi (w : Pl F) : Continuous (psi (d := d) (β := β) w) := by
  rw [continuous_q_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact continuous_const.add ((continuous_inc w).comp (continuous_re.sub continuous_const))
  · exact (continuous_inc w).comp continuous_imI
  · exact (continuous_inc w).comp continuous_imJ
  · exact (continuous_inc w).comp continuous_imK

/- English proof (translation)
Establish `key : ∀ u, u ≠ w → qmap (proj u) x = 1` using `fun u hu => hx.2 u (by simpa using hu)`. Use `ext`. Use `adele_ext fun u => ?_` and prove the remaining obligations. Distinguish the cases in `h : u = w`. Substitute `h` using the available equality.

Simplify using `[psi, qmap, proj_inc_same]`. Use `congrArg (fun z => z.re) (key u h)` as an intermediate fact. Simplify using `only [qmap] at this`. Simplify `this.symm` using `[psi, qmap, proj_inc_ne h]`. Use `adele_ext fun u => ?_` and prove the remaining obligations.

Distinguish the cases in `h : u = w`. Substitute `h` using the available equality. Simplify using `[psi, qmap, proj_inc_same]`. Use `congrArg (fun z => z.imI) (key u h)` as an intermediate fact. Simplify using `only [qmap] at this`.

Simplify `this.symm` using `[psi, qmap, proj_inc_ne h]`. Use `adele_ext fun u => ?_` and prove the remaining obligations. Distinguish the cases in `h : u = w`. Substitute `h` using the available equality. Simplify using `[psi, qmap, proj_inc_same]`.

Use `congrArg (fun z => z.imJ) (key u h)` as an intermediate fact. Simplify using `only [qmap] at this`. Simplify `this.symm` using `[psi, qmap, proj_inc_ne h]`. Use `adele_ext fun u => ?_` and prove the remaining obligations. Distinguish the cases in `h : u = w`.

Substitute `h` using the available equality. Simplify using `[psi, qmap, proj_inc_same]`. Use `congrArg (fun z => z.imK) (key u h)` as an intermediate fact. Simplify using `only [qmap] at this`. Simplify `this.symm` using `[psi, qmap, proj_inc_ne h]`.
-/
theorem psi_proj {w : Pl F} {x : Q d β (AF F)} (hx : x ∈ SuppAt d β {w}) :
    psi w (qmap (proj w) x) = x := by
  have key : ∀ u, u ≠ w → qmap (proj u) x = 1 := fun u hu => hx.2 u (by simpa using hu)
  ext
  · refine adele_ext fun u => ?_
    by_cases h : u = w
    · subst h; simp [psi, qmap, proj_inc_same]
    · have := congrArg (fun z => z.re) (key u h)
      simp only [qmap] at this
      simpa [psi, qmap, proj_inc_ne h] using this.symm
  · refine adele_ext fun u => ?_
    by_cases h : u = w
    · subst h; simp [psi, qmap, proj_inc_same]
    · have := congrArg (fun z => z.imI) (key u h)
      simp only [qmap] at this
      simpa [psi, qmap, proj_inc_ne h] using this.symm
  · refine adele_ext fun u => ?_
    by_cases h : u = w
    · subst h; simp [psi, qmap, proj_inc_same]
    · have := congrArg (fun z => z.imJ) (key u h)
      simp only [qmap] at this
      simpa [psi, qmap, proj_inc_ne h] using this.symm
  · refine adele_ext fun u => ?_
    by_cases h : u = w
    · subst h; simp [psi, qmap, proj_inc_same]
    · have := congrArg (fun z => z.imK) (key u h)
      simp only [qmap] at this
      simpa [psi, qmap, proj_inc_ne h] using this.symm

/- English proof (translation)
Apply the tactic sequence `ext <;> simp [rat, qmap]`.
-/
theorem qmap_proj_rat (w : Pl F) (δ : Q d β F) :
    qmap (proj w) (rat δ : Q d β (AF F)) = rat δ := by
  ext <;> simp [rat, qmap]

/- English proof (translation)
Establish `h1` using `continuous_re (d := d) (β := β) (R := K)`. Establish `h2` using `continuous_imI (d := d) (β := β) (R := K)`. Establish `h3` using `continuous_imJ (d := d) (β := β) (R := K)`. Establish `h4` using `continuous_imK (d := d) (β := β) (R := K)`. Unfold `qn`.

Use `fun_prop`.
-/
theorem continuous_qn {K : Type} [CommRing K] [Algebra F K] [TopologicalSpace K]
    [IsTopologicalRing K] : Continuous (qn : Q d β K → K) := by
  have h1 := continuous_re (d := d) (β := β) (R := K)
  have h2 := continuous_imI (d := d) (β := β) (R := K)
  have h3 := continuous_imJ (d := d) (β := β) (R := K)
  have h4 := continuous_imK (d := d) (β := β) (R := K)
  unfold qn
  fun_prop

/- English proof (translation)
Rewrite using `[continuous_q_iff]`. Simplify using `only [QuaternionAlgebra.re_star, QuaternionAlgebra.imI_star, QuaternionAlgebra.imJ_star, QuaternionAlgebra.imK_star]`. Establish `h1` using `continuous_re (d := d) (β := β) (R := K)`. Establish `h2` using `continuous_imI (d := d) (β := β) (R := K)`. Establish `h3` using `continuous_imJ (d := d) (β := β) (R := K)`.

Establish `h4` using `continuous_imK (d := d) (β := β) (R := K)`. Conclude with `⟨h1.add (continuous_const.mul h2), h2.neg, h3.neg, h4.neg⟩`.
-/
theorem continuous_star_q {K : Type} [CommRing K] [Algebra F K] [TopologicalSpace K]
    [IsTopologicalRing K] : Continuous (star : Q d β K → Q d β K) := by
  rw [continuous_q_iff]
  simp only [QuaternionAlgebra.re_star, QuaternionAlgebra.imI_star, QuaternionAlgebra.imJ_star,
    QuaternionAlgebra.imK_star]
  have h1 := continuous_re (d := d) (β := β) (R := K)
  have h2 := continuous_imI (d := d) (β := β) (R := K)
  have h3 := continuous_imJ (d := d) (β := β) (R := K)
  have h4 := continuous_imK (d := d) (β := β) (R := K)
  exact ⟨h1.add (continuous_const.mul h2), h2.neg, h3.neg, h4.neg⟩

/- English proof (translation)
Rewrite using `[continuous_q_iff]`. Simplify using `only [QuaternionAlgebra.algebraMap_eq]`. Conclude with `⟨continuous_id, continuous_const, continuous_const, continuous_const⟩`.
-/
theorem continuous_algebraMap_q {K : Type} [CommRing K] [Algebra F K] [TopologicalSpace K]
    [IsTopologicalRing K] : Continuous (algebraMap K (Q d β K)) := by
  rw [continuous_q_iff]
  simp only [QuaternionAlgebra.algebraMap_eq]
  exact ⟨continuous_id, continuous_const, continuous_const, continuous_const⟩

/- English proof (translation)
Establish `h1 : ContinuousAt (fun x : Q d β K => (qn x)⁻¹) e` using `continuous_qn.continuousAt.inv₀ h`. Establish `h2 : ContinuousAt (fun x : Q d β K => algebraMap K (Q d β K) (qn x)⁻¹) e` using `continuous_algebraMap_q.continuousAt.comp h1`. Conclude with `h2.mul continuous_star_q.continuousAt`.
-/
theorem continuousAt_qinv {K : Type} [Field K] [Algebra F K] [TopologicalSpace K]
    [IsTopologicalDivisionRing K] {e : Q d β K} (h : qn e ≠ 0) : ContinuousAt qinv e := by
  have h1 : ContinuousAt (fun x : Q d β K => (qn x)⁻¹) e :=
    continuous_qn.continuousAt.inv₀ h
  have h2 : ContinuousAt (fun x : Q d β K => algebraMap K (Q d β K) (qn x)⁻¹) e :=
    continuous_algebraMap_q.continuousAt.comp h1
  exact h2.mul continuous_star_q.continuousAt

/- English proof (translation)
Establish `D` using `denseRange_algebraMap_Kp (F := F) w`. Establish `h` using `D.prodMap (D.prodMap (D.prodMap D))`. Establish `h2` using `((qHomeo (d := d) (β := β) (R := Kp w)).symm.surjective.denseRange).comp h (qHomeo (d := d) (β := β) (R := Kp w)).symm.continuous`. Use `Dense.mono ?_ h2` and prove the remaining obligations. Introduce and unpack `_ ⟨⟨a, b, c, e⟩, rfl⟩`.

Conclude with `⟨⟨a, b, c, e⟩, rfl⟩`.
-/
theorem denseRange_rat (w : Pl F) : DenseRange (rat : Q d β F → Q d β (Kp w)) := by
  have D := denseRange_algebraMap_Kp (F := F) w
  have h := D.prodMap (D.prodMap (D.prodMap D))
  have h2 := ((qHomeo (d := d) (β := β) (R := Kp w)).symm.surjective.denseRange).comp h
    (qHomeo (d := d) (β := β) (R := Kp w)).symm.continuous
  refine Dense.mono ?_ h2
  rintro _ ⟨⟨a, b, c, e⟩, rfl⟩
  exact ⟨⟨a, b, c, e⟩, rfl⟩

/- English proof (translation)
Introduce `F _ _ d β _ s w a ha c hc`. Establish `ha' : ((c⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F)) * a * (c : Q d β (AF F)) ∈ SuppAt d β {w}` using `conj_mem_SuppAt c.inv_mul ha`. Take `⟨a', ea'⟩ : ∃ a' : Q d β (AF F), a' = ((c⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F)) * a * (c : Q d β (AF F))` from `⟨_, rfl⟩`. Rewrite `ha'`, `hc` using `[← ea']`. Take `⟨y, ey⟩ : ∃ y : Q d β (Kp w), y = qmap (proj w) a'` from `⟨_, rfl⟩`.

Take `⟨cw, ecw⟩ : ∃ cw : Q d β (Kp w), cw = qmap (proj w) (c : Q d β (AF F))` from `⟨_, rfl⟩`. Take `⟨cw', ecw'⟩ : ∃ cw' : Q d β (Kp w), cw' = qmap (proj w) ((c⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F))` from `⟨_, rfl⟩`. Establish `h1 : cw * cw' = 1` using `by rw [ecw, ecw', ← map_mul, c.mul_inv, map_one]`. Establish `h2 : cw' * cw = 1` using `by rw [ecw, ecw', ← map_mul, c.inv_mul, map_one]`. Establish `hq : qn cw ≠ 0`.

Introduce `h0`. Use `congrArg qn h1` as an intermediate fact. Rewrite `this` using `[qn_mul, h0, zero_mul, qn_one]`. Conclude with `zero_ne_one this`. Establish `hinv : qinv cw = cw'` using `qinv_unique hq h2`.

Establish `hy : y = cw' * qmap (proj w) a * cw` using `by rw [ey, ea', map_mul, map_mul, ecw, ecw']`. Establish `hga : psi w (cw * y * qinv cw) = a`. Establish `: cw * y * qinv cw = qmap (proj w) a`. Rewrite using `[hinv, hy]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[this, psi_proj ha]`. Establish `hcont : ContinuousAt (fun e : Q d β (Kp w) => psi w (e * y * qinv e)) cw` using `(continuous_psi w).continuousAt.comp ((continuousAt_id.mul continuousAt_const).mul (continuousAt_qinv hq))`. Establish `hcl : cw ∈ closure (Set.range (rat : Q d β F → Q d β (Kp w)))` using `denseRange_rat w cw`. Use `haveI : (𝓝[Set.range (rat : Q d β F → Q d β (Kp w))] cw).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hcl`. Establish `htend : Filter.Tendsto (fun e : Q d β (Kp w) => psi w (e * y * qinv e)) (𝓝[Set.range (rat : Q d β F → Q d β (Kp w))] cw) (𝓝 a)`.

Use `hcont.tendsto` as an intermediate fact. Rewrite `this` using `[hga]`. Conclude with `this.mono_left nhdsWithin_le_nhds`. Establish `hopen : IsOpen {e : Q d β (Kp w) | qn e ≠ 0}` using `isOpen_ne.preimage continuous_qn`. Rewrite using `[← closure_closure]`.

Use `mem_closure_of_tendsto htend ?_` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hopen.mem_nhds hq)] with e he he0`. Take `⟨δ, rfl⟩` from `he`. Establish `hδ : qn δ ≠ 0`. Introduce `h0`.

Apply `he0` to reduce the goal to its premises. Rewrite using `[rat, qn_qmap, h0, map_zero]`. Establish `i1 : δ * qinv δ = 1` using `mul_qinv hδ`. Establish `i2 : qinv δ * δ = 1` using `qinv_mul hδ`. Establish `r1 : (rat δ : Q d β (AF F)) * rat (qinv δ) = 1` using `by rw [← map_mul, i1, map_one]`.

Establish `hmem` using `conj_mem_closure s i1 i2 hc`. Establish `hsupp` using `conj_mem_SuppAt r1 ha'`. Establish `hw : (qinv (rat δ : Q d β (Kp w))) = rat (qinv δ)` using `qinv_unique he0 (by rw [← map_mul, i2, map_one])`. Establish `: psi w ((rat δ : Q d β (Kp w)) * y * qinv (rat δ : Q d β (Kp w))) = (rat δ : Q d β (AF F)) * a' * rat (qinv δ)`. Rewrite using `[hw, ey, ← qmap_proj_rat w δ, ← qmap_proj_rat w (qinv δ), ← map_mul, ← map_mul]`.

Conclude with `psi_proj hsupp`. Rewrite using `[this]`. Conclude with `hmem`.
-/
theorem mem_closure_of_conj_mem : ∀ {F : Type} [Field F] [NumberField F] (d β : F), (∀ x : Q d β F, qn x = 0 → x = 0) →
    ∀ s w : Pl F, ∀ a ∈ SuppAt d β {w}, ∀ c : (Q d β (AF F))ˣ,
      ((c⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F)) * a * (c : Q d β (AF F)) ∈ closure (SAQ d β s) →
      a ∈ closure (SAQ d β s) := by
  intro F _ _ d β _ s w a ha c hc
  have ha' : ((c⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F)) * a * (c : Q d β (AF F)) ∈ SuppAt d β {w} :=
    conj_mem_SuppAt c.inv_mul ha
  obtain ⟨a', ea'⟩ : ∃ a' : Q d β (AF F),
      a' = ((c⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F)) * a * (c : Q d β (AF F)) := ⟨_, rfl⟩
  rw [← ea'] at ha' hc
  obtain ⟨y, ey⟩ : ∃ y : Q d β (Kp w), y = qmap (proj w) a' := ⟨_, rfl⟩
  obtain ⟨cw, ecw⟩ : ∃ cw : Q d β (Kp w), cw = qmap (proj w) (c : Q d β (AF F)) := ⟨_, rfl⟩
  obtain ⟨cw', ecw'⟩ : ∃ cw' : Q d β (Kp w),
      cw' = qmap (proj w) ((c⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F)) := ⟨_, rfl⟩
  have h1 : cw * cw' = 1 := by rw [ecw, ecw', ← map_mul, c.mul_inv, map_one]
  have h2 : cw' * cw = 1 := by rw [ecw, ecw', ← map_mul, c.inv_mul, map_one]
  have hq : qn cw ≠ 0 := by
    intro h0
    have := congrArg qn h1
    rw [qn_mul, h0, zero_mul, qn_one] at this
    exact zero_ne_one this
  have hinv : qinv cw = cw' := qinv_unique hq h2
  have hy : y = cw' * qmap (proj w) a * cw := by rw [ey, ea', map_mul, map_mul, ecw, ecw']
  have hga : psi w (cw * y * qinv cw) = a := by
    have : cw * y * qinv cw = qmap (proj w) a := by
      rw [hinv, hy]
      calc cw * (cw' * qmap (proj w) a * cw) * cw'
          = (cw * cw') * qmap (proj w) a * (cw * cw') := by simp only [mul_assoc]
        _ = qmap (proj w) a := by rw [h1, one_mul, mul_one]
    rw [this, psi_proj ha]
  have hcont : ContinuousAt (fun e : Q d β (Kp w) => psi w (e * y * qinv e)) cw :=
    (continuous_psi w).continuousAt.comp
      ((continuousAt_id.mul continuousAt_const).mul (continuousAt_qinv hq))
  have hcl : cw ∈ closure (Set.range (rat : Q d β F → Q d β (Kp w))) := denseRange_rat w cw
  haveI : (𝓝[Set.range (rat : Q d β F → Q d β (Kp w))] cw).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.1 hcl
  have htend : Filter.Tendsto (fun e : Q d β (Kp w) => psi w (e * y * qinv e))
      (𝓝[Set.range (rat : Q d β F → Q d β (Kp w))] cw) (𝓝 a) := by
    have := hcont.tendsto
    rw [hga] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hopen : IsOpen {e : Q d β (Kp w) | qn e ≠ 0} :=
    isOpen_ne.preimage continuous_qn
  rw [← closure_closure]
  refine mem_closure_of_tendsto htend ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hopen.mem_nhds hq)] with e he he0
  obtain ⟨δ, rfl⟩ := he
  have hδ : qn δ ≠ 0 := by
    intro h0
    apply he0
    rw [rat, qn_qmap, h0, map_zero]
  have i1 : δ * qinv δ = 1 := mul_qinv hδ
  have i2 : qinv δ * δ = 1 := qinv_mul hδ
  have r1 : (rat δ : Q d β (AF F)) * rat (qinv δ) = 1 := by rw [← map_mul, i1, map_one]
  have hmem := conj_mem_closure s i1 i2 hc
  have hsupp := conj_mem_SuppAt r1 ha'
  have hw : (qinv (rat δ : Q d β (Kp w))) = rat (qinv δ) :=
    qinv_unique he0 (by rw [← map_mul, i2, map_one])
  have : psi w ((rat δ : Q d β (Kp w)) * y * qinv (rat δ : Q d β (Kp w))) =
      (rat δ : Q d β (AF F)) * a' * rat (qinv δ) := by
    rw [hw, ey, ← qmap_proj_rat w δ, ← qmap_proj_rat w (qinv δ), ← map_mul, ← map_mul]
    exact psi_proj hsupp
  rw [this]
  exact hmem

end GlobalTheory.CompanionTheory.PlaneSA.MemConj
