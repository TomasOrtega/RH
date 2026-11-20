import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicQuaternionNeighbourhoodStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuaternionRamifiedPlacesFiniteStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuaternionIntegralTraceAlmostAllStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuaternionRegularDenseStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuaternionTraceOpenStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSquareRootsNearOneStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeakApproximationIntegralStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuaternionAnisotropicTraceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HassePrincipleNormTraceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuaternionNormOneConjugateStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicQuaternionLocalUnitsStatement
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

namespace GlobalTheory.CompanionTheory.PlaneSA.KeyApprox

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Establish `: CharZero (Kp u)` using `charZero_of_injective_algebraMap (algebraMap F (Kp u)).injective`. Conclude with `two_ne_zero`.
-/
theorem two_ne_zero_Kp (u : Pl F) : (2 : Kp u) ≠ 0 := by
  have : CharZero (Kp u) := charZero_of_injective_algebraMap (algebraMap F (Kp u)).injective
  exact two_ne_zero

/- English proof (translation)
Consider the cases of `u with`. Consider the case `inl w`. Use `letI : NontriviallyNormedField w.Completion := { (inferInstance : NormedField w.Completion) with non_trivial := ⟨2, by`. Rewrite using `[← (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _), map_ofNat]`. Use the proof step `simp⟩ }`.

Conclude with `NormedField.nhdsNE_neBot (0 : w.Completion)`. Consider the case `inr v`. Use `letI : NontriviallyNormedField (v.adicCompletion F) := Valued.toNontriviallyNormedField _ _`. Conclude with `NormedField.nhdsNE_neBot (0 : v.adicCompletion F)`.
-/
theorem neBot_Kp (u : Pl F) : (𝓝[≠] (0 : Kp u)).NeBot := by
  cases u with
  | inl w =>
    letI : NontriviallyNormedField w.Completion :=
      { (inferInstance : NormedField w.Completion) with
        non_trivial := ⟨2, by
          rw [← (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _),
            map_ofNat]
          simp⟩ }
    exact NormedField.nhdsNE_neBot (0 : w.Completion)
  | inr v =>
    letI : NontriviallyNormedField (v.adicCompletion F) := Valued.toNontriviallyNormedField _ _
    exact NormedField.nhdsNE_neBot (0 : v.adicCompletion F)

def IntAt {d β : F} : (u : Pl F) → Q d β (Kp u) → Prop
  | .inl _, _ => True
  | .inr v, x => IntQ v x

/- English proof (translation)
Consider the cases of `u with`. Consider the case `inl w => exact Filter.univ_mem' fun _ => trivial`. Consider the case `inr v`. Establish `hO : IsOpen (Ov v : Set (Kp (Sum.inr v : Pl F)))` using `show IsOpen ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) from Valued.isOpen_valuationSubring _`. Establish `h1 : (1 : Kp (Sum.inr v : Pl F)) ∈ Ov v` using `one_mem (v.adicCompletionIntegers F)`.

Establish `h0 : (0 : Kp (Sum.inr v : Pl F)) ∈ Ov v` using `zero_mem (v.adicCompletionIntegers F)`. Establish `m1 : {q : Q d β (Kp (Sum.inr v : Pl F)) | q.re ∈ Ov v} ∈ 𝓝 (1 : Q d β (Kp (Sum.inr v : Pl F)))` using `(hO.preimage continuous_re).mem_nhds (by simpa using h1)`. Establish `m2 : {q : Q d β (Kp (Sum.inr v : Pl F)) | q.imI ∈ Ov v} ∈ 𝓝 (1 : Q d β (Kp (Sum.inr v : Pl F)))` using `(hO.preimage continuous_imI).mem_nhds (by simpa using h0)`. Establish `m3 : {q : Q d β (Kp (Sum.inr v : Pl F)) | q.imJ ∈ Ov v} ∈ 𝓝 (1 : Q d β (Kp (Sum.inr v : Pl F)))` using `(hO.preimage continuous_imJ).mem_nhds (by simpa using h0)`. Establish `m4 : {q : Q d β (Kp (Sum.inr v : Pl F)) | q.imK ∈ Ov v} ∈ 𝓝 (1 : Q d β (Kp (Sum.inr v : Pl F)))` using `(hO.preimage continuous_imK).mem_nhds (by simpa using h0)`.

Use `filter_upwards [m1, m2, m3, m4] with q q1 q2 q3 q4 using ⟨q1, q2, q3, q4⟩`.
-/
theorem intAt_mem_nhds (d β : F) (u : Pl F) : {x : Q d β (Kp u) | IntAt u x} ∈ 𝓝 (1 : Q d β (Kp u)) := by
  cases u with
  | inl w => exact Filter.univ_mem' fun _ => trivial
  | inr v =>
    have hO : IsOpen (Ov v : Set (Kp (Sum.inr v : Pl F))) :=
      show IsOpen ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) from Valued.isOpen_valuationSubring _
    have h1 : (1 : Kp (Sum.inr v : Pl F)) ∈ Ov v := one_mem (v.adicCompletionIntegers F)
    have h0 : (0 : Kp (Sum.inr v : Pl F)) ∈ Ov v := zero_mem (v.adicCompletionIntegers F)
    have m1 : {q : Q d β (Kp (Sum.inr v : Pl F)) | q.re ∈ Ov v} ∈ 𝓝 (1 : Q d β (Kp (Sum.inr v : Pl F))) :=
      (hO.preimage continuous_re).mem_nhds (by simpa using h1)
    have m2 : {q : Q d β (Kp (Sum.inr v : Pl F)) | q.imI ∈ Ov v} ∈ 𝓝 (1 : Q d β (Kp (Sum.inr v : Pl F))) :=
      (hO.preimage continuous_imI).mem_nhds (by simpa using h0)
    have m3 : {q : Q d β (Kp (Sum.inr v : Pl F)) | q.imJ ∈ Ov v} ∈ 𝓝 (1 : Q d β (Kp (Sum.inr v : Pl F))) :=
      (hO.preimage continuous_imJ).mem_nhds (by simpa using h0)
    have m4 : {q : Q d β (Kp (Sum.inr v : Pl F)) | q.imK ∈ Ov v} ∈ 𝓝 (1 : Q d β (Kp (Sum.inr v : Pl F))) :=
      (hO.preimage continuous_imK).mem_nhds (by simpa using h0)
    filter_upwards [m1, m2, m3, m4] with q q1 q2 q3 q4 using ⟨q1, q2, q3, q4⟩

/- English proof (translation)
Establish `h2` using `two_ne_zero_Kp u`. Take `⟨r, hr, hr1, hr2⟩` from `GlobalTheory.T.quaternion_regular_dense d β h2 hd hβ (neBot_Kp u) c hc (interior W) (interior_mem_nhds.2 hW)`. Establish `hWr : W ∈ 𝓝 r` using `mem_interior_iff_mem_nhds.1 hr`. Establish `ev` using `GlobalTheory.T.quaternion_trace_open d β r hr1 hr2 (GlobalTheory.T.local_square_roots_near_one u) W hWr`. Establish `ht : Filter.Tendsto (fun x : Kp u => x / 2) (𝓝 (2 * r.re)) (𝓝 r.re)`.

Establish `hcont : Continuous fun x : Kp u => x * 2⁻¹` using `continuous_id.mul continuous_const`. Use `hcont.tendsto (2 * r.re)` as an intermediate fact. Simplify `this` using `[div_eq_mul_inv, mul_comm, mul_left_comm, h2]`. Establish `ev2` using `ht.eventually ev`. Establish `ne : ∀ᶠ x in 𝓝 (2 * r.re), x ^ 2 ≠ (4 : Kp u)`.

Use `(isOpen_ne_fun (continuous_pow 2) continuous_const).mem_nhds ?_` and prove the remaining obligations. Introduce `h`. Apply `hr2` to reduce the goal to its premises. Establish `h4 : (4 : Kp u) ≠ 0`. Establish `: (4 : Kp u) = 2 * 2` using `by norm_num`.

Rewrite using `[this]`. Conclude with `mul_ne_zero h2 h2`. Apply `mul_left_cancel₀ h4` to reduce the goal to its premises. Take the linear combination `h`. Use `⟨interior {x | x ^ 2 ≠ (4 : Kp u) ∧ ∃ b ∈ W, qn b = 1 ∧ 2 * b.re = x}, isOpen_interior, ⟨2 * r.re, mem_interior_iff_mem_nhds.2 ?_⟩, fun x hx => by` and prove the remaining obligations.

Establish `h` using `interior_subset hx`. Conclude with `h⟩`. Use `filter_upwards [ev2, ne] with x hx1 hx2`. Take `⟨b, hb, hb1, hb2⟩` from `hx1`. Conclude with `⟨hx2, b, hb, hb1, by rw [hb2]; field_simp⟩`.
-/
theorem local_trace_open (u : Pl F) (d β : F) (hd : d ≠ 0) (hβ : β ≠ 0) (c : Q d β (Kp u)) (hc : qn c = 1)
    (W : Set (Q d β (Kp u))) (hW : W ∈ 𝓝 c) :
    ∃ O : Set (Kp u), IsOpen O ∧ O.Nonempty ∧ ∀ x ∈ O, x ^ 2 ≠ 4 ∧ ∃ b ∈ W, qn b = 1 ∧ 2 * b.re = x := by
  have h2 := two_ne_zero_Kp u
  obtain ⟨r, hr, hr1, hr2⟩ := GlobalTheory.T.quaternion_regular_dense d β h2 hd hβ (neBot_Kp u) c hc (interior W) (interior_mem_nhds.2 hW)
  have hWr : W ∈ 𝓝 r := mem_interior_iff_mem_nhds.1 hr
  have ev := GlobalTheory.T.quaternion_trace_open d β r hr1 hr2 (GlobalTheory.T.local_square_roots_near_one u) W hWr
  have ht : Filter.Tendsto (fun x : Kp u => x / 2) (𝓝 (2 * r.re)) (𝓝 r.re) := by
    have hcont : Continuous fun x : Kp u => x * 2⁻¹ := continuous_id.mul continuous_const
    have := hcont.tendsto (2 * r.re)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, h2] using this
  have ev2 := ht.eventually ev
  have ne : ∀ᶠ x in 𝓝 (2 * r.re), x ^ 2 ≠ (4 : Kp u) := by
    refine (isOpen_ne_fun (continuous_pow 2) continuous_const).mem_nhds ?_
    intro h
    apply hr2
    have h4 : (4 : Kp u) ≠ 0 := by
      have : (4 : Kp u) = 2 * 2 := by norm_num
      rw [this]; exact mul_ne_zero h2 h2
    apply mul_left_cancel₀ h4
    linear_combination h
  refine ⟨interior {x | x ^ 2 ≠ (4 : Kp u) ∧ ∃ b ∈ W, qn b = 1 ∧ 2 * b.re = x}, isOpen_interior,
    ⟨2 * r.re, mem_interior_iff_mem_nhds.2 ?_⟩, fun x hx => by
      have h := interior_subset hx
      exact h⟩
  filter_upwards [ev2, ne] with x hx1 hx2
  obtain ⟨b, hb, hb1, hb2⟩ := hx1
  exact ⟨hx2, b, hb, hb1, by rw [hb2]; field_simp⟩

/- English proof (translation)
The claim follows from `(proj u).commutes c`.
-/
theorem proj_algebraMap (u : Pl F) (c : F) : proj u (algebraMap F (AF F) c) = algebraMap F (Kp u) c :=
  (proj u).commutes c

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem rat_re {d β : F} {R : Type} [CommRing R] [Algebra F R] (x : Q d β F) :
    (rat x : Q d β R).re = algebraMap F R x.re := rfl

/- English proof (translation)
Apply the tactic sequence `ext <;> simp [rat, qmap, Algebra.ofId_apply]`.
-/
theorem qmap_proj_rat {d β : F} (u : Pl F) (x : Q d β F) :
    qmap (proj u) (rat x : Q d β (AF F)) = (rat x : Q d β (Kp u)) := by
  ext <;> simp [rat, qmap, Algebra.ofId_apply]

/- English proof (translation)
Use `qn_qmap (Algebra.ofId F R) x` as an intermediate fact. Rewrite `this` using `[hx, map_one]`. Conclude with `this`.
-/
theorem qn_rat {d β : F} {R : Type} [CommRing R] [Algebra F R] (x : Q d β F) (hx : qn x = 1) :
    qn (rat x : Q d β R) = 1 := by
  have := qn_qmap (Algebra.ofId F R) x
  rw [hx, map_one] at this
  exact this

/- English proof (translation)
Establish `h` using `(algebraMap F (AF F) c).2.2`. Use `filter_upwards [h] with v hv`. Rewrite using `[← proj_algebraMap]`. Conclude with `hv`.
-/
theorem eventually_int (c : F) :
    ∀ᶠ v in Filter.cofinite (α := HeightOneSpectrum (𝓞 F)),
      algebraMap F (Kp (Sum.inr v : Pl F)) c ∈ Ov v := by
  have h := (algebraMap F (AF F) c).2.2
  filter_upwards [h] with v hv
  rw [← proj_algebraMap]
  exact hv

/- English proof (translation)
Use `filter_upwards [eventually_int x.re, eventually_int x.imI, eventually_int x.imJ, eventually_int x.imK] with v h1 h2 h3 h4 using ⟨h1, h2, h3, h4⟩`.
-/
theorem eventually_int_rat (d β : F) (x : Q d β F) :
    ∀ᶠ v in Filter.cofinite (α := HeightOneSpectrum (𝓞 F)),
      IntQ v (rat x : Q d β (Kp (Sum.inr v : Pl F))) := by
  filter_upwards [eventually_int x.re, eventually_int x.imI, eventually_int x.imJ, eventually_int x.imK]
    with v h1 h2 h3 h4 using ⟨h1, h2, h3, h4⟩

/- English proof (translation)
Establish `h1 : f Z * f ((Z⁻¹ : Aˣ) : A) = 1` using `by rw [← map_mul, Units.mul_inv, map_one]`. Rewrite `h1` using `[h]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_assoc, Units.inv_mul, one_mul]`. Use `_ = ((z⁻¹ : Bˣ) : B) := by rw [h1, mul_one]`.
-/
theorem map_inv_of_eq {A B : Type} [Ring A] [Ring B] (f : A →+* B) (Z : Aˣ) (z : Bˣ) (h : f Z = z) :
    f ((Z⁻¹ : Aˣ) : A) = ((z⁻¹ : Bˣ) : B) := by
  have h1 : f Z * f ((Z⁻¹ : Aˣ) : A) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
  rw [h] at h1
  calc f ((Z⁻¹ : Aˣ) : A) = ((z⁻¹ : Bˣ) : B) * ((z : B) * f ((Z⁻¹ : Aˣ) : A)) := by
        rw [← mul_assoc, Units.inv_mul, one_mul]
    _ = ((z⁻¹ : Bˣ) : B) := by rw [h1, mul_one]

/- English proof (translation)
Establish `hxu : ∀ u : Pl F, qn (rat x : Q d β (Kp u)) = 1` using `fun u => qn_rat x hx`. Set `xu : ∀ u : Pl F, (Q d β (Kp u))ˣ` to `fun u => ⟨rat x, star (rat x), by rw [mul_star_eq, hxu, map_one], by rw [star_mul_eq, hxu, map_one]⟩`. Establish `hconj : ∀ u, u ∈ T → ∃ y : (Q d β (Kp u))ˣ, (y : Q d β (Kp u)) * rat x * ((y⁻¹ : (Q d β (Kp u))ˣ) : Q d β (Kp u)) = b u`. Introduce `u hu`. Take `⟨q1, q2, -⟩` from `hb u hu`.

Use `GlobalTheory.T.quaternion_norm_one_conjugate d β (two_ne_zero_Kp u) hd hβ _ _ (hxu u) q1 q2.symm ?_` and prove the remaining obligations. Rewrite using `[rat_re]`. Introduce `h`. Apply `hreg` to reduce the goal to its premises. Apply `(algebraMap F (Kp u)).injective` to reduce the goal to its premises.

Rewrite using `[map_pow, h, map_one]`. Use `choose y hy using hconj`. Set `y' : ∀ u : Pl F, (Q d β (Kp u))ˣ` to `fun u => if h : u ∈ T then y u h else 1`. Take `⟨Y, hY1, hY2⟩` from `GlobalTheory.T.adelic_quaternion_local_units d β T y'`. Take `⟨H, hH1, hH2⟩` from `GlobalTheory.T.adelic_quaternion_local_units d β {s} xu`.

Establish `hHs : ∀ u, u ≠ s → qmap (proj u) (H : Q d β (AF F)) = 1` using `fun u hu => hH2 u (by simpa using hu)`. Use `⟨(Y : Q d β (AF F)) * rat x * ((Y⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F)) * ((H⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F)), ?_, Y, (H : Q d β (AF F)), ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `u`. Simplify using `only [map_mul, qmap_proj_rat]`. Distinguish the cases in `hu : u ∈ T`.

Establish `hus : u ≠ s` using `fun e => hs (e ▸ hu)`. Establish `e1 : qmap (proj u) (Y : Q d β (AF F)) = ((y u hu : (Q d β (Kp u))ˣ) : Q d β (Kp u))`. Rewrite using `[hY1 u hu]`. Simplify using `[y', hu]`. Establish `e2` using `map_inv_of_eq (qmap (proj u)) Y (y u hu) e1`.

Establish `e3` using `map_inv_of_eq (qmap (proj u)) H 1 (by simpa using hHs u hus)`. Rewrite using `[e1, e2, e3, hy u hu]`. Simplify using `using (hb u hu).2.2`. Establish `e1 : qmap (proj u) (Y : Q d β (AF F)) = ((1 : (Q d β (Kp u))ˣ) : Q d β (Kp u))`. Simplify using `using hY2 u hu`.

Establish `e2` using `map_inv_of_eq (qmap (proj u)) Y 1 e1`. Rewrite using `[e1, e2]`. Distinguish the cases in `hus : u = s`. Substitute `hus` using the available equality. Establish `e3` using `map_inv_of_eq (qmap (proj u)) H (xu u) (hH1 u (by simp))`.

Rewrite using `[e3]`. Establish `: (rat x : Q d β (Kp u)) * (((xu u)⁻¹ : (Q d β (Kp u))ˣ) : Q d β (Kp u)) = 1` using `Units.mul_inv (xu u)`. Simplify `h1` using `[this]`. Establish `e3` using `map_inv_of_eq (qmap (proj u)) H 1 (by simpa using hHs u hus)`. Rewrite using `[e3]`.

Simplify using `using hrest u hu hus`. Use `adele_ext fun u => ?_` and prove the remaining obligations. Rewrite using `[map_one, ← qn_qmap]`. Distinguish the cases in `hus : u = s`. Substitute `hus` using the available equality.

Rewrite using `[hH1 u (by simp)]`. Conclude with `hxu u`. Rewrite using `[hHs u hus, qn_one]`. Introduce `u hu`. Conclude with `hHs u hu`.

Rewrite using `[mul_assoc _ _ (H : Q d β (AF F)), Units.inv_mul, mul_one]`.
-/
theorem assemble (d β : F) (hd : d ≠ 0) (hβ : β ≠ 0) (G : ∀ u, Set (Q d β (Kp u))) (s : Pl F)
    (h1 : (1 : Q d β (Kp s)) ∈ G s) (x : Q d β F) (hx : qn x = 1) (hreg : x.re ^ 2 ≠ 1)
    (T : Finset (Pl F)) (hs : s ∉ T) (b : ∀ u, Q d β (Kp u))
    (hb : ∀ u ∈ T, qn (b u) = 1 ∧ (b u).re = algebraMap F (Kp u) x.re ∧ b u ∈ G u)
    (hrest : ∀ u, u ∉ T → u ≠ s → (rat x : Q d β (Kp u)) ∈ G u) :
    ∃ c : Q d β (AF F), (∀ u, qmap (proj u) c ∈ G u) ∧ ∃ y : (Q d β (AF F))ˣ, ∃ h ∈ SuppAt d β {s},
      (y : Q d β (AF F)) * rat x * ((y⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F)) = c * h := by
  classical
  have hxu : ∀ u : Pl F, qn (rat x : Q d β (Kp u)) = 1 := fun u => qn_rat x hx
  let xu : ∀ u : Pl F, (Q d β (Kp u))ˣ := fun u =>
    ⟨rat x, star (rat x), by rw [mul_star_eq, hxu, map_one], by rw [star_mul_eq, hxu, map_one]⟩
  have hconj : ∀ u, u ∈ T → ∃ y : (Q d β (Kp u))ˣ,
      (y : Q d β (Kp u)) * rat x * ((y⁻¹ : (Q d β (Kp u))ˣ) : Q d β (Kp u)) = b u := by
    intro u hu
    obtain ⟨q1, q2, -⟩ := hb u hu
    refine GlobalTheory.T.quaternion_norm_one_conjugate d β (two_ne_zero_Kp u) hd hβ _ _ (hxu u) q1 q2.symm ?_
    rw [rat_re]
    intro h
    apply hreg
    apply (algebraMap F (Kp u)).injective
    rw [map_pow, h, map_one]
  choose y hy using hconj
  let y' : ∀ u : Pl F, (Q d β (Kp u))ˣ := fun u => if h : u ∈ T then y u h else 1
  obtain ⟨Y, hY1, hY2⟩ := GlobalTheory.T.adelic_quaternion_local_units d β T y'
  obtain ⟨H, hH1, hH2⟩ := GlobalTheory.T.adelic_quaternion_local_units d β {s} xu
  have hHs : ∀ u, u ≠ s → qmap (proj u) (H : Q d β (AF F)) = 1 := fun u hu =>
    hH2 u (by simpa using hu)
  refine ⟨(Y : Q d β (AF F)) * rat x * ((Y⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F)) *
      ((H⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F)), ?_, Y, (H : Q d β (AF F)), ⟨?_, ?_⟩, ?_⟩
  · intro u
    simp only [map_mul, qmap_proj_rat]
    by_cases hu : u ∈ T
    · have hus : u ≠ s := fun e => hs (e ▸ hu)
      have e1 : qmap (proj u) (Y : Q d β (AF F)) = ((y u hu : (Q d β (Kp u))ˣ) : Q d β (Kp u)) := by
        rw [hY1 u hu]; simp [y', hu]
      have e2 := map_inv_of_eq (qmap (proj u)) Y (y u hu) e1
      have e3 := map_inv_of_eq (qmap (proj u)) H 1 (by simpa using hHs u hus)
      rw [e1, e2, e3, hy u hu]
      simpa using (hb u hu).2.2
    · have e1 : qmap (proj u) (Y : Q d β (AF F)) = ((1 : (Q d β (Kp u))ˣ) : Q d β (Kp u)) := by
        simpa using hY2 u hu
      have e2 := map_inv_of_eq (qmap (proj u)) Y 1 e1
      rw [e1, e2]
      by_cases hus : u = s
      · subst hus
        have e3 := map_inv_of_eq (qmap (proj u)) H (xu u) (hH1 u (by simp))
        rw [e3]
        have : (rat x : Q d β (Kp u)) * (((xu u)⁻¹ : (Q d β (Kp u))ˣ) : Q d β (Kp u)) = 1 :=
          Units.mul_inv (xu u)
        simpa [this] using h1
      · have e3 := map_inv_of_eq (qmap (proj u)) H 1 (by simpa using hHs u hus)
        rw [e3]
        simpa using hrest u hu hus
  · refine adele_ext fun u => ?_
    rw [map_one, ← qn_qmap]
    by_cases hus : u = s
    · subst hus
      rw [hH1 u (by simp)]
      exact hxu u
    · rw [hHs u hus, qn_one]
  · intro u hu
    exact hHs u hu
  · rw [mul_assoc _ _ (H : Q d β (AF F)), Units.inv_mul, mul_one]

/- English proof (translation)
Introduce `F _ _ d β hani s w hs hws a ha hreg V hV`. Establish `hdns : ∀ r : F, r ^ 2 ≠ d`. Introduce `r hr`. Establish `h` using `hani ⟨r, 1, 0, 0⟩ (by simp [qn, hr])`. Use `congrArg (fun q : Q d β F => q.imI) h` as an intermediate fact.

Simplify using `at this`. Establish `hβ : β ≠ 0`. Introduce `hb`. Establish `h` using `hani ⟨0, 0, 1, 0⟩ (by simp [qn, hb])`. Use `congrArg (fun q : Q d β F => q.imJ) h` as an intermediate fact.

Simplify using `at this`. Establish `hd : d ≠ 0` using `fun h => hdns 0 (by simp [h])`. Take `⟨T₀, U, hU, hinf, hbox⟩` from `GlobalTheory.T.adelic_quaternion_neighbourhood d β a V hV`. Establish `hAfin` using `GlobalTheory.T.quaternion_ramified_places_finite d β hdns hβ`. Establish `hE` using `GlobalTheory.T.quaternion_integral_trace_almost_all d β hd hβ`.

Establish `hEfin` using `Filter.eventually_cofinite.1 hE`. Set `Tp : Finset (Pl F)` to `(T₀ ∪ {w} ∪ hAfin.toFinset ∪ hEfin.toFinset.map Function.Embedding.inr).erase s`. Establish `mem_Tp : ∀ u, u ≠ s → (u ∈ T₀ ∨ u = w ∨ (∀ x : Q d β (Kp u), qn x = 0 → x = 0) ∨ ∃ v ∈ hEfin.toFinset, (Sum.inr v : Pl F) = u) → u ∈ Tp`. Introduce `u hus h`. Use `Finset.mem_erase.2 ⟨hus, ?_⟩` and prove the remaining obligations.

Break down `h with h | h | h | ⟨v, hv, e⟩` into its components or cases. Simplify using `[h]`. Simplify using `[h]`. Conclude with `Finset.mem_union_left _ (Finset.mem_union_right _ (by simpa using h))`. Conclude with `Finset.mem_union_right _ (Finset.mem_map.2 ⟨v, hv, e⟩)`.

Set `G : ∀ u, Set (Q d β (Kp u))` to `fun u => if u ∈ T₀ then U u else {x | IntAt u x}`. Establish `hGn : ∀ u, u ∉ T₀ → G u = {x | IntAt u x}` using `fun u h => if_neg h`. Establish `hGc : ∀ u, ∃ c : Q d β (Kp u), qn c = 1 ∧ G u ∈ 𝓝 c`. Introduce `u`. Distinguish the cases in `hu : u ∈ T₀`.

Use `⟨qmap (proj u) a, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[qn_qmap, ha.1, map_one]`. Simplify `hU u` using `[G, hu]`. Use `⟨1, qn_one, ?_⟩` and prove the remaining obligations. Simplify `intAt_mem_nhds d β u` using `[G, hu]`.

Use `choose c hc1 hc2 using hGc`. Establish `hO` using `fun u => local_trace_open u d β hd hβ (c u) (hc1 u) (G u) (hc2 u)`. Use `choose O hOo hOn hOG using hO`. Take `⟨t, ht, hint⟩` from `GlobalTheory.T.weak_approximation_integral s Tp (by simp [Tp]) O (fun u _ => ⟨hOo u, hOn u⟩)`. Establish `hwT : w ∈ Tp` using `mem_Tp w hws (Or.inr (Or.inl rfl))`.

Establish `ht4 : t ^ 2 ≠ 4`. Introduce `h`. Use `(hOG w _ (ht w hwT)).1 ?_` and prove the remaining obligations. Rewrite using `[← map_pow, h, map_ofNat]`. Establish `hanis : ∀ u, (∀ x : Q d β (Kp u), qn x = 0 → x = 0) → u ≠ s`.

Introduce and unpack `u hu rfl`. Take `⟨x, hx0, hx⟩` from `hs`. Conclude with `hx0 (hu x hx)`. Establish `hbsq : ∀ (u : Pl F) (b : Q d β (Kp u)), 2 * b.re = algebraMap F (Kp u) t → b.re ^ 2 ≠ 1`. Introduce `u b hb h`.

Apply `ht4` to reduce the goal to its premises. Apply `(algebraMap F (Kp u)).injective` to reduce the goal to its premises. Rewrite using `[map_pow, ← hb, map_ofNat]`. Take the linear combination `4 * h`. Take `⟨x, hx1, hx2⟩` from `GlobalTheory.T.hasse_principle_norm_trace d β t hani (by`.

Introduce `u hu r hr`. Establish `huT : u ∈ Tp` using `mem_Tp u (hanis u hu) (Or.inr (Or.inr (Or.inl hu)))`. Take `⟨-, b, -, hb1, hb2⟩` from `hOG u _ (ht u huT)`. Use `GlobalTheory.T.quaternion_anisotropic_trace d β (two_ne_zero_Kp u) hu b hb1 (hbsq u b hb2) r ?_` and prove the remaining obligations. Rewrite using `[hr, hb2, map_sub, map_pow, map_ofNat])`.

Establish `hxreg : x.re ^ 2 ≠ 1` using `fun h => ht4 (by rw [← hx2]; linear_combination 4 * h)`. Establish `hE2` using `Filter.eventually_cofinite.1 (eventually_int_rat d β x)`. Set `T₁ : Finset (Pl F)` to `(Tp ∪ hE2.toFinset.map Function.Embedding.inr).erase s`. Establish `hre : ∀ (u : Pl F) (b : Q d β (Kp u)), 2 * b.re = algebraMap F (Kp u) t → b.re = algebraMap F (Kp u) x.re`. Introduce `u b hb`.

Apply `mul_left_cancel₀ (two_ne_zero_Kp u)` to reduce the goal to its premises. Rewrite using `[hb, ← hx2, map_mul, map_ofNat]`. Establish `hb : ∀ u, ∃ b : Q d β (Kp u), u ∈ T₁ → qn b = 1 ∧ b.re = algebraMap F (Kp u) x.re ∧ b ∈ G u`. Introduce `u`. Distinguish the cases in `hu : u ∈ Tp`.

Take `⟨-, b, hb0, hb1, hb2⟩` from `hOG u _ (ht u hu)`. Conclude with `⟨b, fun _ => ⟨hb1, hre u b hb2, hb0⟩⟩`. Distinguish the cases in `hu1 : u ∈ T₁`. Establish `hus : u ≠ s` using `(Finset.mem_erase.1 hu1).1`. Establish `hu2` using `(Finset.mem_erase.1 hu1).2`.

Break down `Finset.mem_union.1 hu2 with h | h` into its components or cases. Conclude with `absurd h hu`. Take `⟨v, -, rfl⟩` from `Finset.mem_map.1 h`. Establish `hvE : v ∉ hEfin.toFinset` using `fun hv => hu (mem_Tp _ hus (Or.inr (Or.inr (Or.inr ⟨v, hv, rfl⟩))))`. Establish `hvE' : ∀ t ∈ Ov v, ∃ b : Q d β (Kp (Sum.inr v : Pl F)), qn b = 1 ∧ 2 * b.re = t ∧ IntQ v b`.

Assume the negation of the conclusion as `hcon`. Conclude with `hvE (by simpa using hcon)`. Establish `hnT : (Sum.inr v : Pl F) ∉ T₀` using `fun h0 => hu (mem_Tp _ hus (Or.inl h0))`. Take `⟨b, hb1, hb2, hb3⟩` from `hvE' _ (hint v hu hus)`. Use `⟨b, fun _ => ⟨hb1, hre _ b hb2, ?_⟩⟩` and prove the remaining obligations.

Establish `h3 : b ∈ G (Sum.inr v)`. Rewrite using `[hGn _ hnT]`. Conclude with `hb3`. Conclude with `h3`. Conclude with `⟨1, fun h => absurd h hu1⟩`.

Use `choose b hb using hb`. Establish `hG1 : (1 : Q d β (Kp s)) ∈ G s`. Distinguish the cases in `h : s ∈ T₀`. Establish `e : qmap (proj s) a = 1` using `ha.2 s (by simpa using fun e : s = w => hws e.symm)`. Use `mem_of_mem_nhds (hU s)` as an intermediate fact.

Rewrite `this` using `[e]`. Simplify `this` using `[G, h]`. Simplify `mem_of_mem_nhds (intAt_mem_nhds d β s)` using `[G, h]`. Establish `hrest : ∀ u, u ∉ T₁ → u ≠ s → (rat x : Q d β (Kp u)) ∈ G u`. Introduce `u hu hus`.

Establish `hnT : u ∉ T₀` using `fun h0 => hu (Finset.mem_erase.2 ⟨hus, Finset.mem_union_left _ (mem_Tp u hus (Or.inl h0))⟩)`. Consider the cases of `u with`. Consider the case `inl w' => exact absurd (hinf w') hnT`. Consider the case `inr v`. Establish `hv : IntQ v (rat x : Q d β (Kp (Sum.inr v : Pl F)))`.

Assume the negation of the conclusion as `hcon`. Conclude with `hu (Finset.mem_erase.2 ⟨hus, Finset.mem_union_right _ (Finset.mem_map.2 ⟨v, by simpa using hcon, rfl⟩)⟩)`. Rewrite using `[hGn _ hnT]`. Conclude with `hv`. Take `⟨e, he, y, h, hh, hy⟩` from `assemble d β hd hβ G s hG1 x hx1 hxreg T₁ (by simp [T₁]) b (fun u hu => hb u hu) hrest`.

Use `⟨e, hbox e (fun u hu => ?_) (fun v hv => ?_), y, x, hx1, h, hh, hy⟩` and prove the remaining obligations. Simplify `he u` using `[G, hu]`. Establish `h2` using `he (Sum.inr v)`. Rewrite `h2` using `[hGn _ hv]`. Conclude with `h2`.
-/
theorem keyapprox : ∀ {F : Type} [Field F] [NumberField F] (d β : F), (∀ x : Q d β F, qn x = 0 → x = 0) →
  ∀ s w : Pl F, (∃ x : Q d β (Kp s), x ≠ 0 ∧ qn x = 0) → w ≠ s →
  ∀ a ∈ SuppAt d β {w}, (qmap (proj w) a).re ^ 2 ≠ 1 → ∀ V ∈ 𝓝 a,
    ∃ b ∈ V, ∃ y : (Q d β (AF F))ˣ, ∃ x : Q d β F, qn x = 1 ∧ ∃ h ∈ SuppAt d β {s},
      (y : Q d β (AF F)) * rat x * ((y⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F)) = b * h := by
  classical
  intro F _ _ d β hani s w hs hws a ha hreg V hV
  have hdns : ∀ r : F, r ^ 2 ≠ d := by
    intro r hr
    have h := hani ⟨r, 1, 0, 0⟩ (by simp [qn, hr])
    have := congrArg (fun q : Q d β F => q.imI) h
    simp at this
  have hβ : β ≠ 0 := by
    intro hb
    have h := hani ⟨0, 0, 1, 0⟩ (by simp [qn, hb])
    have := congrArg (fun q : Q d β F => q.imJ) h
    simp at this
  have hd : d ≠ 0 := fun h => hdns 0 (by simp [h])
  obtain ⟨T₀, U, hU, hinf, hbox⟩ := GlobalTheory.T.adelic_quaternion_neighbourhood d β a V hV
  have hAfin := GlobalTheory.T.quaternion_ramified_places_finite d β hdns hβ
  have hE := GlobalTheory.T.quaternion_integral_trace_almost_all d β hd hβ
  have hEfin := Filter.eventually_cofinite.1 hE
  let Tp : Finset (Pl F) :=
    (T₀ ∪ {w} ∪ hAfin.toFinset ∪ hEfin.toFinset.map Function.Embedding.inr).erase s
  have mem_Tp : ∀ u, u ≠ s → (u ∈ T₀ ∨ u = w ∨ (∀ x : Q d β (Kp u), qn x = 0 → x = 0) ∨
      ∃ v ∈ hEfin.toFinset, (Sum.inr v : Pl F) = u) → u ∈ Tp := by
    intro u hus h
    refine Finset.mem_erase.2 ⟨hus, ?_⟩
    rcases h with h | h | h | ⟨v, hv, e⟩
    · simp [h]
    · simp [h]
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (by simpa using h))
    · exact Finset.mem_union_right _ (Finset.mem_map.2 ⟨v, hv, e⟩)
  let G : ∀ u, Set (Q d β (Kp u)) := fun u => if u ∈ T₀ then U u else {x | IntAt u x}
  have hGn : ∀ u, u ∉ T₀ → G u = {x | IntAt u x} := fun u h => if_neg h
  have hGc : ∀ u, ∃ c : Q d β (Kp u), qn c = 1 ∧ G u ∈ 𝓝 c := by
    intro u
    by_cases hu : u ∈ T₀
    · refine ⟨qmap (proj u) a, ?_, ?_⟩
      · rw [qn_qmap, ha.1, map_one]
      · simpa [G, hu] using hU u
    · refine ⟨1, qn_one, ?_⟩
      simpa [G, hu] using intAt_mem_nhds d β u
  choose c hc1 hc2 using hGc
  have hO := fun u => local_trace_open u d β hd hβ (c u) (hc1 u) (G u) (hc2 u)
  choose O hOo hOn hOG using hO
  obtain ⟨t, ht, hint⟩ := GlobalTheory.T.weak_approximation_integral s Tp (by simp [Tp]) O (fun u _ => ⟨hOo u, hOn u⟩)
  have hwT : w ∈ Tp := mem_Tp w hws (Or.inr (Or.inl rfl))
  have ht4 : t ^ 2 ≠ 4 := by
    intro h
    refine (hOG w _ (ht w hwT)).1 ?_
    rw [← map_pow, h, map_ofNat]
  have hanis : ∀ u, (∀ x : Q d β (Kp u), qn x = 0 → x = 0) → u ≠ s := by
    rintro u hu rfl
    obtain ⟨x, hx0, hx⟩ := hs
    exact hx0 (hu x hx)
  have hbsq : ∀ (u : Pl F) (b : Q d β (Kp u)), 2 * b.re = algebraMap F (Kp u) t → b.re ^ 2 ≠ 1 := by
    intro u b hb h
    apply ht4
    apply (algebraMap F (Kp u)).injective
    rw [map_pow, ← hb, map_ofNat]
    linear_combination 4 * h
  obtain ⟨x, hx1, hx2⟩ := GlobalTheory.T.hasse_principle_norm_trace d β t hani (by
    intro u hu r hr
    have huT : u ∈ Tp := mem_Tp u (hanis u hu) (Or.inr (Or.inr (Or.inl hu)))
    obtain ⟨-, b, -, hb1, hb2⟩ := hOG u _ (ht u huT)
    refine GlobalTheory.T.quaternion_anisotropic_trace d β (two_ne_zero_Kp u) hu b hb1 (hbsq u b hb2) r ?_
    rw [hr, hb2, map_sub, map_pow, map_ofNat])
  have hxreg : x.re ^ 2 ≠ 1 := fun h => ht4 (by rw [← hx2]; linear_combination 4 * h)
  have hE2 := Filter.eventually_cofinite.1 (eventually_int_rat d β x)
  let T₁ : Finset (Pl F) := (Tp ∪ hE2.toFinset.map Function.Embedding.inr).erase s
  have hre : ∀ (u : Pl F) (b : Q d β (Kp u)), 2 * b.re = algebraMap F (Kp u) t →
      b.re = algebraMap F (Kp u) x.re := by
    intro u b hb
    apply mul_left_cancel₀ (two_ne_zero_Kp u)
    rw [hb, ← hx2, map_mul, map_ofNat]
  have hb : ∀ u, ∃ b : Q d β (Kp u), u ∈ T₁ →
      qn b = 1 ∧ b.re = algebraMap F (Kp u) x.re ∧ b ∈ G u := by
    intro u
    by_cases hu : u ∈ Tp
    · obtain ⟨-, b, hb0, hb1, hb2⟩ := hOG u _ (ht u hu)
      exact ⟨b, fun _ => ⟨hb1, hre u b hb2, hb0⟩⟩
    · by_cases hu1 : u ∈ T₁
      · have hus : u ≠ s := (Finset.mem_erase.1 hu1).1
        have hu2 := (Finset.mem_erase.1 hu1).2
        rcases Finset.mem_union.1 hu2 with h | h
        · exact absurd h hu
        · obtain ⟨v, -, rfl⟩ := Finset.mem_map.1 h
          have hvE : v ∉ hEfin.toFinset := fun hv => hu (mem_Tp _ hus (Or.inr (Or.inr (Or.inr ⟨v, hv, rfl⟩))))
          have hvE' : ∀ t ∈ Ov v, ∃ b : Q d β (Kp (Sum.inr v : Pl F)), qn b = 1 ∧ 2 * b.re = t ∧ IntQ v b := by
            by_contra hcon
            exact hvE (by simpa using hcon)
          have hnT : (Sum.inr v : Pl F) ∉ T₀ := fun h0 => hu (mem_Tp _ hus (Or.inl h0))
          obtain ⟨b, hb1, hb2, hb3⟩ := hvE' _ (hint v hu hus)
          refine ⟨b, fun _ => ⟨hb1, hre _ b hb2, ?_⟩⟩
          have h3 : b ∈ G (Sum.inr v) := by
            rw [hGn _ hnT]
            exact hb3
          exact h3
      · exact ⟨1, fun h => absurd h hu1⟩
  choose b hb using hb
  have hG1 : (1 : Q d β (Kp s)) ∈ G s := by
    by_cases h : s ∈ T₀
    · have e : qmap (proj s) a = 1 := ha.2 s (by simpa using fun e : s = w => hws e.symm)
      have := mem_of_mem_nhds (hU s)
      rw [e] at this
      simpa [G, h] using this
    · simpa [G, h] using mem_of_mem_nhds (intAt_mem_nhds d β s)
  have hrest : ∀ u, u ∉ T₁ → u ≠ s → (rat x : Q d β (Kp u)) ∈ G u := by
    intro u hu hus
    have hnT : u ∉ T₀ := fun h0 => hu (Finset.mem_erase.2 ⟨hus, Finset.mem_union_left _ (mem_Tp u hus (Or.inl h0))⟩)
    cases u with
    | inl w' => exact absurd (hinf w') hnT
    | inr v =>
      have hv : IntQ v (rat x : Q d β (Kp (Sum.inr v : Pl F))) := by
        by_contra hcon
        exact hu (Finset.mem_erase.2 ⟨hus, Finset.mem_union_right _
          (Finset.mem_map.2 ⟨v, by simpa using hcon, rfl⟩)⟩)
      rw [hGn _ hnT]
      exact hv
  obtain ⟨e, he, y, h, hh, hy⟩ := assemble d β hd hβ G s hG1 x hx1 hxreg T₁ (by simp [T₁]) b
    (fun u hu => hb u hu) hrest
  refine ⟨e, hbox e (fun u hu => ?_) (fun v hv => ?_), y, x, hx1, h, hh, hy⟩
  · simpa [G, hu] using he u
  · have h2 := he (Sum.inr v)
    rw [hGn _ hv] at h2
    exact h2

end GlobalTheory.CompanionTheory.PlaneSA.KeyApprox
