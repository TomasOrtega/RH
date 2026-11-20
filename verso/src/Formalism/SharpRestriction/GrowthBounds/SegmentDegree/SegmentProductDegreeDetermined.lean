import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.StrictMonoIntExists
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.AllowedLettersOfLateRows

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section Img

variable {ι ι' : Type} {n : ℕ}

/- English proof (translation)
Unfold `multideg imgMon`. Simplify using `only [Finsupp.sum_apply]`. Unfold `Finsupp.sum`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations.

Simplify using `only [Finsupp.single_apply, Prod.mk.injEq]`. Distinguish the cases in `h : ga v.1 = t`. Simplify using `[h]`. Simplify using `[h]`.
-/
theorem multideg_imgMon [DecidableEq ι'] (ga : ι → ι') (ep : ι → ℕ) (m : ι × Fin n →₀ ℕ) (t : ι') :
    multideg (imgMon (fun v : ι × Fin n => (ga v.1, v.2)) (fun v => ep v.1) m) t =
      m.sum fun v k => (if ga v.1 = t then ep v.1 else 0) * k := by
  classical
  unfold multideg imgMon
  simp only [Finsupp.sum_apply]
  unfold Finsupp.sum
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [Finsupp.single_apply, Prod.mk.injEq]
  by_cases h : ga v.1 = t
  · simp [h]
  · simp [h]

/- English proof (translation)
Establish `hsub : m.support ⊆ T ×ˢ (Finset.univ : Finset (Fin n))`. Introduce `v hv`. Rewrite using `[Finset.mem_product]`. Conclude with `⟨hT v hv, Finset.mem_univ _⟩`. Rewrite using `[Finsupp.sum_of_support_subset m hsub _ (fun _ _ => mul_zero _), Finset.sum_product]`.

Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Unfold `multideg`. Rewrite using `[Finset.mul_sum]`.
-/
theorem sum_eq_multideg (h : ι → ℕ) (m : ι × Fin n →₀ ℕ) (T : Finset ι) (hT : ∀ v ∈ m.support, v.1 ∈ T) :
    (m.sum fun v k => h v.1 * k) = ∑ x ∈ T, h x * multideg m x := by
  classical
  have hsub : m.support ⊆ T ×ˢ (Finset.univ : Finset (Fin n)) := by
    intro v hv
    rw [Finset.mem_product]
    exact ⟨hT v hv, Finset.mem_univ _⟩
  rw [Finsupp.sum_of_support_subset m hsub _ (fun _ _ => mul_zero _), Finset.sum_product]
  refine Finset.sum_congr rfl fun x _ => ?_
  unfold multideg
  rw [Finset.mul_sum]

/- English proof (translation)
Rewrite using `[multideg_imgMon, multideg_imgMon]`. Set `T : Finset ι` to `m.support.image Prod.fst ∪ m'.support.image Prod.fst`. Rewrite using `[sum_eq_multideg (fun x => if ga x = t then ep x else 0) m T (fun v hv => Finset.mem_union_left _ (Finset.mem_image_of_mem _ hv)), sum_eq_multideg (fun x => if ga x = t then ep x else 0) m' T (fun v hv => Finset.mem_union_right _ (Finset.mem_image_of_mem _ hv))]`. Conclude with `Finset.sum_congr rfl fun x _ => by rw [h x]`.
-/
theorem multideg_imgMon_congr (ga : ι → ι') (ep : ι → ℕ) (m m' : ι × Fin n →₀ ℕ)
    (h : ∀ x, multideg m x = multideg m' x) (t : ι') :
    multideg (imgMon (fun v : ι × Fin n => (ga v.1, v.2)) (fun v => ep v.1) m) t =
      multideg (imgMon (fun v : ι × Fin n => (ga v.1, v.2)) (fun v => ep v.1) m') t := by
  classical
  rw [multideg_imgMon, multideg_imgMon]
  let T : Finset ι := m.support.image Prod.fst ∪ m'.support.image Prod.fst
  rw [sum_eq_multideg (fun x => if ga x = t then ep x else 0) m T
      (fun v hv => Finset.mem_union_left _ (Finset.mem_image_of_mem _ hv)),
    sum_eq_multideg (fun x => if ga x = t then ep x else 0) m' T
      (fun v hv => Finset.mem_union_right _ (Finset.mem_image_of_mem _ hv))]
  exact Finset.sum_congr rfl fun x _ => by rw [h x]

/- English proof (translation)
Take `⟨m0, hm0⟩` from `MvPolynomial.ne_zero_iff.mp hQ0`. Establish `hm0' : m0 ∈ Q.support` using `MvPolynomial.mem_support_iff.mpr hm0`. Use `⟨fun t => multideg (imgMon (fun v : ι × Fin n => (ga v.1, v.2)) (fun v => ep v.1) m0) t, fun t m' hm' => ?_, fun t m' hm' => ?_⟩` and prove the remaining obligations. Take `⟨m, hm, rfl⟩` from `supp_aeval_pow (fun v : ι × Fin n => (ga v.1, v.2)) (fun v => ep v.1) P hm'`. Conclude with `multideg_imgMon_congr ga ep m m0 (fun x => (mem_Pol_iff.mp hP m hm x).trans (mem_Pol_iff.mp hQ m0 hm0' x).symm) t`.

Take `⟨m, hm, rfl⟩` from `supp_aeval_pow (fun v : ι × Fin n => (ga v.1, v.2)) (fun v => ep v.1) Q hm'`. Conclude with `multideg_imgMon_congr ga ep m m0 (fun x => (mem_Pol_iff.mp hQ m hm x).trans (mem_Pol_iff.mp hQ m0 hm0' x).symm) t`.
-/
theorem degAt_aeval {R : Type} [CommRing R] (ga : ι → ι') (ep : ι → ℕ) {β : ι → ℕ}
    {P Q : MvPolynomial (ι × Fin n) R} (hP : P ∈ Pol R n β) (hQ : Q ∈ Pol R n β) (hQ0 : Q ≠ 0) :
    ∃ δ : ι' → ℕ, (∀ t, DegAt t (δ t)
        (aeval (fun v : ι × Fin n => (X (ga v.1, v.2) : MvPolynomial (ι' × Fin n) R) ^ ep v.1) P)) ∧
      ∀ t, DegAt t (δ t)
        (aeval (fun v : ι × Fin n => (X (ga v.1, v.2) : MvPolynomial (ι' × Fin n) R) ^ ep v.1) Q) := by
  obtain ⟨m0, hm0⟩ := MvPolynomial.ne_zero_iff.mp hQ0
  have hm0' : m0 ∈ Q.support := MvPolynomial.mem_support_iff.mpr hm0
  refine ⟨fun t => multideg (imgMon (fun v : ι × Fin n => (ga v.1, v.2)) (fun v => ep v.1) m0) t,
    fun t m' hm' => ?_, fun t m' hm' => ?_⟩
  · obtain ⟨m, hm, rfl⟩ := supp_aeval_pow (fun v : ι × Fin n => (ga v.1, v.2)) (fun v => ep v.1) P hm'
    exact multideg_imgMon_congr ga ep m m0
      (fun x => (mem_Pol_iff.mp hP m hm x).trans (mem_Pol_iff.mp hQ m0 hm0' x).symm) t
  · obtain ⟨m, hm, rfl⟩ := supp_aeval_pow (fun v : ι × Fin n => (ga v.1, v.2)) (fun v => ep v.1) Q hm'
    exact multideg_imgMon_congr ga ep m m0
      (fun x => (mem_Pol_iff.mp hQ m hm x).trans (mem_Pol_iff.mp hQ m0 hm0' x).symm) t

end Img

/- English proof (translation)
Introduce `m hm`. Use `support_monomial_subset hm` as an intermediate fact. Rewrite `this` using `[Finset.mem_singleton]`. Rewrite using `[this]`.
-/
theorem degAt_monomial {R : Type} [CommRing R] {ι : Type} {n : ℕ} (l : ι × Fin n →₀ ℕ) (c : R) (t : ι) :
    DegAt t (multideg l t) (monomial l c : MvPolynomial (ι × Fin n) R) := by
  classical
  intro m hm
  have := support_monomial_subset hm
  rw [Finset.mem_singleton] at this
  rw [this]

/- English proof (translation)
The claim follows from `mem_Pol_iff.mpr fun m hm t => h t m hm`.
-/
theorem mem_Pol_of_degAt {R : Type} [CommRing R] {ι : Type} {n : ℕ} {d : ι → ℕ} {P : MvPolynomial (ι × Fin n) R}
    (h : ∀ t, DegAt t (d t) P) : P ∈ Pol R n d := mem_Pol_iff.mpr fun m hm t => h t m hm

/- English proof (translation)
Introduce `p n' r K _ F O _ x z β l0 d hx hz hdeg hne`. Establish `hz0 : ∀ j ∈ Finset.range F.J, z (j : ℤ) ≠ 0`. Introduce `j hj h0`. Apply `hne` to reduce the goal to its premises. Rewrite using `[Finset.prod_eq_zero hj (by rw [h0, map_zero]), zero_mul]`.

Establish `key : ∀ j : ℕ, ∃ δ : Fin n' → ℕ, j ∈ Finset.range F.J → (∀ t, DegAt t (δ t) (phSeg O K p F (j : ℤ) (x j))) ∧ ∀ t, DegAt t (δ t) (phSeg O K p F (j : ℤ) (z j))`. Introduce `j`. Distinguish the cases in `hj : j ∈ Finset.range F.J`. Take `⟨δ, h1, h2⟩` from `degAt_aeval (R := O) (n := r + K) (fun y : ℤ => posOf n' y) (fun y : ℤ => p ^ F.dist (j : ℤ) y) (hx j) (hz j) (hz0 j hj)`. Conclude with `⟨δ, fun _ => ⟨h1, h2⟩⟩`.

Conclude with `⟨0, fun h => absurd h hj⟩`. Use `choose δ hδ using key`. Establish `hX : ∀ t, DegAt t (∑ j ∈ Finset.range F.J, δ j t + multideg l0 t) ((∏ j ∈ Finset.range F.J, phSeg O K p F (j : ℤ) (x j)) * monomial l0 1)` using `fun t => degAt_mul (degAt_prod _ _ _ fun j hj => (hδ j hj).1 t) (degAt_monomial l0 1 t)`. Establish `hZ : ∀ t, DegAt t (∑ j ∈ Finset.range F.J, δ j t + multideg l0 t) ((∏ j ∈ Finset.range F.J, phSeg O K p F (j : ℤ) (z j)) * monomial l0 1)` using `fun t => degAt_mul (degAt_prod _ _ _ fun j hj => (hδ j hj).2 t) (degAt_monomial l0 1 t)`. Take `⟨m0, hm0⟩` from `MvPolynomial.ne_zero_iff.mp hne`.

Establish `hm0'` using `MvPolynomial.mem_support_iff.mpr hm0`. Rewrite `hdeg`, the goal using `[RRdeg_eq_Pol]`. Use `mem_Pol_of_degAt fun t => ?_` and prove the remaining obligations. Establish `e : d t = ∑ j ∈ Finset.range F.J, δ j t + multideg l0 t` using `(mem_Pol_iff.mp hdeg m0 hm0' t).symm.trans (hZ t m0 hm0')`. Rewrite using `[e]`.

Conclude with `hX t`.
-/
theorem segment_product_degree_determined : SegmentProductDegreeDetermined := by
  intro p n' r K _ F O _ x z β l0 d hx hz hdeg hne
  classical
  have hz0 : ∀ j ∈ Finset.range F.J, z (j : ℤ) ≠ 0 := by
    intro j hj h0
    apply hne
    rw [Finset.prod_eq_zero hj (by rw [h0, map_zero]), zero_mul]
  have key : ∀ j : ℕ, ∃ δ : Fin n' → ℕ, j ∈ Finset.range F.J →
      (∀ t, DegAt t (δ t) (phSeg O K p F (j : ℤ) (x j))) ∧ ∀ t, DegAt t (δ t) (phSeg O K p F (j : ℤ) (z j)) := by
    intro j
    by_cases hj : j ∈ Finset.range F.J
    · obtain ⟨δ, h1, h2⟩ := degAt_aeval (R := O) (n := r + K) (fun y : ℤ => posOf n' y)
        (fun y : ℤ => p ^ F.dist (j : ℤ) y) (hx j) (hz j) (hz0 j hj)
      exact ⟨δ, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose δ hδ using key
  have hX : ∀ t, DegAt t (∑ j ∈ Finset.range F.J, δ j t + multideg l0 t)
      ((∏ j ∈ Finset.range F.J, phSeg O K p F (j : ℤ) (x j)) * monomial l0 1) := fun t =>
    degAt_mul (degAt_prod _ _ _ fun j hj => (hδ j hj).1 t) (degAt_monomial l0 1 t)
  have hZ : ∀ t, DegAt t (∑ j ∈ Finset.range F.J, δ j t + multideg l0 t)
      ((∏ j ∈ Finset.range F.J, phSeg O K p F (j : ℤ) (z j)) * monomial l0 1) := fun t =>
    degAt_mul (degAt_prod _ _ _ fun j hj => (hδ j hj).2 t) (degAt_monomial l0 1 t)
  obtain ⟨m0, hm0⟩ := MvPolynomial.ne_zero_iff.mp hne
  have hm0' := MvPolynomial.mem_support_iff.mpr hm0
  rw [RRdeg_eq_Pol] at hdeg ⊢
  refine mem_Pol_of_degAt fun t => ?_
  have e : d t = ∑ j ∈ Finset.range F.J, δ j t + multideg l0 t :=
    (mem_Pol_iff.mp hdeg m0 hm0' t).symm.trans (hZ t m0 hm0')
  rw [e]
  exact hX t

/- English proof (translation)
Introduce `m hm`. Take `⟨i, hi, hmi⟩` from `Finset.mem_biUnion.mp (support_sum hm)`. Conclude with `h i hi m hmi`.
-/
theorem degAt_sum {R : Type} [CommRing R] {ι : Type} {n : ℕ} {x : ι} {d : ℕ} {κ : Type} (s : Finset κ)
    (f : κ → MvPolynomial (ι × Fin n) R) (h : ∀ i ∈ s, DegAt x d (f i)) : DegAt x d (∑ i ∈ s, f i) := by
  classical
  intro m hm
  obtain ⟨i, hi, hmi⟩ := Finset.mem_biUnion.mp (support_sum hm)
  exact h i hi m hmi

/- English proof (translation)
Introduce `m hm`. Use `h m ?_` and prove the remaining obligations. Rewrite `hm`, the goal using `[mem_support_iff]`. Introduce `h0`. Conclude with `hm (by rw [coeff_C_mul, h0, mul_zero])`.
-/
theorem degAt_C_mul {R : Type} [CommRing R] {ι : Type} {n : ℕ} {x : ι} {d : ℕ} (c : R)
    {P : MvPolynomial (ι × Fin n) R} (h : DegAt x d P) : DegAt x d (C c * P) := by
  intro m hm
  refine h m ?_
  rw [mem_support_iff] at hm ⊢
  intro h0
  exact hm (by rw [coeff_C_mul, h0, mul_zero])

/- English proof (translation)
Unfold `Dat.detPl`. Rewrite using `[Matrix.det_apply]`. Use `degAt_sum _ _ fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[Units.smul_def, zsmul_eq_mul]`. Establish `h1 : (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : MvPolynomial (ℤ × Fin r) R) = C (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : R)`.

Simplify using the standard rewrite rules. Rewrite using `[h1]`. Use `degAt_C_mul _ ?_` and prove the remaining obligations. Establish `h2` using `degAt_prod (R := R) (x := t) Finset.univ (fun i : Fin r => (Matrix.of fun a b : Fin r => (MvPolynomial.X (X.row j x a, b) : MvPolynomial (ℤ × Fin r) R)) (σ i) i) (fun i => if X.row j x (σ i) = t then 1 else 0) (fun i _ => degAt_X (x := t) (X.row j x (σ i), i))`. Rewrite `h2` using `[Equiv.sum_comp σ (fun a => if X.row j x a = t then 1 else 0)]`.

Conclude with `h2`.
-/
theorem degAt_detPl {R : Type} [CommRing R] {n' r : ℕ} [NeZero n'] (X : Dat n' r) (j x t : ℤ) :
    DegAt t (∑ a : Fin r, if X.row j x a = t then 1 else 0) (X.detPl R j x) := by
  classical
  unfold Dat.detPl
  rw [Matrix.det_apply]
  refine degAt_sum _ _ fun σ _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]
  have h1 : (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : MvPolynomial (ℤ × Fin r) R) = C (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : R) := by
    simp
  rw [h1]
  refine degAt_C_mul _ ?_
  have h2 := degAt_prod (R := R) (x := t) Finset.univ
    (fun i : Fin r => (Matrix.of fun a b : Fin r => (MvPolynomial.X (X.row j x a, b) : MvPolynomial (ℤ × Fin r) R)) (σ i) i)
    (fun i => if X.row j x (σ i) = t then 1 else 0) (fun i _ => degAt_X (x := t) (X.row j x (σ i), i))
  rw [Equiv.sum_comp σ (fun a => if X.row j x a = t then 1 else 0)] at h2
  exact h2

/- English proof (translation)
Introduce `p n' r K _ _ _ X O _ j b y e hy`. Distinguish the cases in `hy0 : y = 0`. Conclude with `⟨0, by rw [hy0]; simp [Dat.zSeg]⟩`. Establish `hexp : ∀ P : SegRing O r K, expand (p ^ X.Rj p K j) P = aeval (fun v : ℤ × Fin (r + K) => (MvPolynomial.X ((fun z : ℤ => z) v.1, v.2) : SegRing O r K) ^ (fun _ : ℤ => p ^ X.Rj p K j) v.1) P`. Introduce `P`.

Establish `: expand (p ^ X.Rj p K j) = aeval (fun v : ℤ × Fin (r + K) => (MvPolynomial.X ((fun z : ℤ => z) v.1, v.2) : SegRing O r K) ^ (fun _ : ℤ => p ^ X.Rj p K j) v.1)`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `v`. Simplify using the standard rewrite rules. Rewrite using `[this]`.

Take `⟨δ, h1, -⟩` from `degAt_aeval (R := O) (n := r + K) (fun z : ℤ => z) (fun _ : ℤ => p ^ X.Rj p K j) hy hy hy0`. Establish `hD : X.DlSeg p K O j ∈ Pol O r (fun t => ∑ x ∈ X.toLate j, X.sg p K j x * ∑ a : Fin r, if X.row j x a = t then 1 else 0)`. Use `mem_Pol_of_degAt fun t => ?_` and prove the remaining obligations. Unfold `Dat.DlSeg`. Conclude with `degAt_prod _ _ _ fun x _ => degAt_pow (degAt_detPl X j x t) _`.

Establish `h` using `hom_Pol_mul O (hom_Pol_mul O (plEmb_Pol r K hD) (mem_Pol_of_degAt h1)) (mem_Pol_of_degAt fun t => degAt_monomial e (1 : O) t)`. Unfold `Dat.zSeg`. Rewrite using `[hexp]`. Conclude with `⟨_, h⟩`.
-/
theorem segment_image_multihomogeneous : SegmentImageMultihomogeneous := by
  intro p n' r K _ _ _ X O _ j b y e hy
  classical
  by_cases hy0 : y = 0
  · exact ⟨0, by rw [hy0]; simp [Dat.zSeg]⟩
  have hexp : ∀ P : SegRing O r K, expand (p ^ X.Rj p K j) P =
      aeval (fun v : ℤ × Fin (r + K) => (MvPolynomial.X ((fun z : ℤ => z) v.1, v.2) : SegRing O r K) ^
        (fun _ : ℤ => p ^ X.Rj p K j) v.1) P := by
    intro P
    have : expand (p ^ X.Rj p K j) = aeval (fun v : ℤ × Fin (r + K) =>
        (MvPolynomial.X ((fun z : ℤ => z) v.1, v.2) : SegRing O r K) ^ (fun _ : ℤ => p ^ X.Rj p K j) v.1) := by
      apply MvPolynomial.algHom_ext
      intro v
      simp
    rw [this]
  obtain ⟨δ, h1, -⟩ := degAt_aeval (R := O) (n := r + K) (fun z : ℤ => z) (fun _ : ℤ => p ^ X.Rj p K j) hy hy hy0
  have hD : X.DlSeg p K O j ∈ Pol O r (fun t => ∑ x ∈ X.toLate j, X.sg p K j x *
      ∑ a : Fin r, if X.row j x a = t then 1 else 0) := by
    refine mem_Pol_of_degAt fun t => ?_
    unfold Dat.DlSeg
    exact degAt_prod _ _ _ fun x _ => degAt_pow (degAt_detPl X j x t) _
  have h := hom_Pol_mul O (hom_Pol_mul O (plEmb_Pol r K hD) (mem_Pol_of_degAt h1))
    (mem_Pol_of_degAt fun t => degAt_monomial e (1 : O) t)
  unfold Dat.zSeg
  rw [hexp]
  exact ⟨_, h⟩

end Formalism.MainNotions.SelectionLemmas.Pf
