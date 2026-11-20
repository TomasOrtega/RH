import Mathlib
import Formalism.UnipotentAdelicQuotients.SWXSDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

open Matrix HeckeCharacterZeroLocus.SiegelWeilU

namespace GlobalTheory.CompanionTheory.SW.UnitRep

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

/- English proof (translation)
Simplify using `only [hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]`.
-/
theorem hform_add_left (σ : A →+* A) (J : Matrix n n A) (x x' y : n → A) :
    hform σ J (x + x') y = hform σ J x y + hform σ J x' y := by
  simp only [hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]`.
-/
theorem hform_add_right (σ : A →+* A) (J : Matrix n n A) (x y y' : n → A) :
    hform σ J x (y + y') = hform σ J x y + hform σ J x y' := by
  simp only [hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]`.
-/
theorem hform_smul_left' (σ : A →+* A) (J : Matrix n n A) (a : A) (x y : n → A) :
    hform σ J (a • x) y = σ a * hform σ J x y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Simplify using `only [hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem hform_smul_right' (σ : A →+* A) (J : Matrix n n A) (a : A) (x y : n → A) :
    hform σ J x (a • y) = a * hform σ J x y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Rewrite using `[hform, Finset.sum_eq_single i, Finset.sum_eq_single j]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[Pi.single_eq_of_ne hb]`. Simplify using the standard rewrite rules.

Introduce `b _ hb`. Simplify using `[Pi.single_eq_of_ne hb]`. Simplify using the standard rewrite rules.
-/
theorem hform_single_single (σ : A →+* A) (J : Matrix n n A) (i j : n) :
    hform σ J (Pi.single i 1) (Pi.single j 1) = J i j := by
  rw [hform, Finset.sum_eq_single i, Finset.sum_eq_single j]
  · simp
  · intro b _ hb; simp [Pi.single_eq_of_ne hb]
  · simp
  · intro b _ hb; simp [Pi.single_eq_of_ne hb]
  · simp

/- English proof (translation)
Simplify using `only [hform, map_sum, map_mul, hσ]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hJ i j]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hform_self_fixed (σ : A →+* A) (hσ : ∀ y, σ (σ y) = y) (J : Matrix n n A)
    (hJ : ∀ i j, σ (J j i) = J i j) (x : n → A) : σ (hform σ J x x) = hform σ J x x := by
  simp only [hform, map_sum, map_mul, hσ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ i j]; ring

/- English proof (translation)
Establish `e₁ : ∀ i, Ideal.Quotient.mk P (z i) = Ideal.Quotient.mk P (x i)` using `fun i => Ideal.Quotient.eq.2 (h₁ i)`. Establish `e₂ : ∀ i, Ideal.Quotient.mk P (σ (z i)) = Ideal.Quotient.mk P (σ (x i))` using `fun i => Ideal.Quotient.eq.2 (by simpa only [map_sub] using h₂ i)`. Use `Ideal.Quotient.eq.1 ?_` and prove the remaining obligations. Simplify using `only [hform, map_sum, map_mul, e₁, e₂]`.
-/
theorem hform_self_congr (σ : A →+* A) (J : Matrix n n A) (P : Ideal A) (x z : n → A)
    (h₁ : ∀ i, z i - x i ∈ P) (h₂ : ∀ i, σ (z i - x i) ∈ P) :
    hform σ J z z - hform σ J x x ∈ P := by
  have e₁ : ∀ i, Ideal.Quotient.mk P (z i) = Ideal.Quotient.mk P (x i) := fun i =>
    Ideal.Quotient.eq.2 (h₁ i)
  have e₂ : ∀ i, Ideal.Quotient.mk P (σ (z i)) = Ideal.Quotient.mk P (σ (x i)) := fun i =>
    Ideal.Quotient.eq.2 (by simpa only [map_sub] using h₂ i)
  refine Ideal.Quotient.eq.1 ?_
  simp only [hform, map_sum, map_mul, e₁, e₂]

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Take `⟨δ, hδu, hδσ⟩` from `hδ`. Establish `hpol : ∀ x y, hform σ J x y + hform σ J y x ∈ P` using `fun x y => by`. Establish `h` using `hcon (x + y)`.

Rewrite `h` using `[hform_add_left, hform_add_right, hform_add_right]`. Establish `h'` using `P.sub_mem (P.sub_mem h (hcon x)) (hcon y)`. Use `h' using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Establish `hpol' : ∀ x y, δ * (hform σ J x y - hform σ J y x) ∈ P` using `fun x y => by`.

Establish `h` using `hpol x (δ • y)`. Rewrite `h` using `[hform_smul_right', hform_smul_left', hδσ]`. Use `h using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Establish `hall : ∀ x y, hform σ J x y ∈ P` using `fun x y => by`.

Establish `h₁ : hform σ J x y - hform σ J y x ∈ P` using `(Ideal.unit_mul_mem_iff_mem P hδu).1 (hpol' x y)`. Establish `h₂ : 2 * hform σ J x y ∈ P`. Use `P.add_mem (hpol x y) h₁ using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Conclude with `(Ideal.unit_mul_mem_iff_mem P h2).1 h₂`.

Establish `hJ0 : (Ideal.Quotient.mk P).mapMatrix J = 0`. Use extensionality with `i j`. Establish `h` using `hall (Pi.single i 1) (Pi.single j 1)`. Rewrite `h` using `[hform_single_single]`. Simplify using `using Ideal.Quotient.eq_zero_iff_mem.2 h`.

Establish `hd : J.det ∈ P`. Use `Ideal.Quotient.eq_zero_iff_mem.1 ?_` and prove the remaining obligations. Rewrite using `[RingHom.map_det, hJ0, Matrix.det_zero]`. Conclude with `hP.ne_top (Ideal.eq_top_of_isUnit_mem P hd hdet)`.
-/
theorem exists_hform_not_mem (σ : A →+* A) (hσ : ∀ y, σ (σ y) = y) (h2 : IsUnit (2 : A))
    (hδ : ∃ δ : A, IsUnit δ ∧ σ δ = -δ) (m : ℕ) (J : Matrix (Fin (m + 1)) (Fin (m + 1)) A)
    (hdet : IsUnit J.det) (P : Ideal A) (hP : P.IsMaximal) :
    ∃ y, hform σ J y y ∉ P := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨δ, hδu, hδσ⟩ := hδ
  have hpol : ∀ x y, hform σ J x y + hform σ J y x ∈ P := fun x y => by
    have h := hcon (x + y)
    rw [hform_add_left, hform_add_right, hform_add_right] at h
    have h' := P.sub_mem (P.sub_mem h (hcon x)) (hcon y)
    convert h' using 1
    ring
  have hpol' : ∀ x y, δ * (hform σ J x y - hform σ J y x) ∈ P := fun x y => by
    have h := hpol x (δ • y)
    rw [hform_smul_right', hform_smul_left', hδσ] at h
    convert h using 1
    ring
  have hall : ∀ x y, hform σ J x y ∈ P := fun x y => by
    have h₁ : hform σ J x y - hform σ J y x ∈ P :=
      (Ideal.unit_mul_mem_iff_mem P hδu).1 (hpol' x y)
    have h₂ : 2 * hform σ J x y ∈ P := by
      convert P.add_mem (hpol x y) h₁ using 1
      ring
    exact (Ideal.unit_mul_mem_iff_mem P h2).1 h₂
  have hJ0 : (Ideal.Quotient.mk P).mapMatrix J = 0 := by
    ext i j
    have h := hall (Pi.single i 1) (Pi.single j 1)
    rw [hform_single_single] at h
    simpa using Ideal.Quotient.eq_zero_iff_mem.2 h
  have hd : J.det ∈ P := by
    refine Ideal.Quotient.eq_zero_iff_mem.1 ?_
    rw [RingHom.map_det, hJ0, Matrix.det_zero]
  exact hP.ne_top (Ideal.eq_top_of_isUnit_mem P hd hdet)

/- English proof (translation)
The claim follows from `Ideal.comap_isMaximal_of_surjective σ (fun y => ⟨σ y, hσ y⟩)`.
-/
theorem comap_isMaximal (σ : A →+* A) (hσ : ∀ y, σ (σ y) = y) (P : Ideal A) (hP : P.IsMaximal) :
    (P.comap σ).IsMaximal :=
  Ideal.comap_isMaximal_of_surjective σ (fun y => ⟨σ y, hσ y⟩)

/- English proof (translation)
Rewrite using `[Ideal.isCoprime_iff_sup_eq]`. Use `hP.coprime_of_ne hQ ?_` and prove the remaining obligations. Introduce and unpack `rfl`. Conclude with `ha' ha`.
-/
theorem isCoprime_of_mem_not_mem {P Q : Ideal A} (hP : P.IsMaximal) (hQ : Q.IsMaximal) {a : A}
    (ha : a ∈ P) (ha' : a ∉ Q) : IsCoprime P Q := by
  rw [Ideal.isCoprime_iff_sup_eq]
  refine hP.coprime_of_ne hQ ?_
  rintro rfl
  exact ha' ha

/- English proof (translation)
Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty => exact ⟨0, by simp⟩`. Consider the case `insert q T _ ih`. Take `⟨x, hx⟩` from `ih`. Distinguish the cases in `hxq : hform σ J x x ∈ q.asIdeal`.

Use `swap`. Use `⟨x, fun p hp => ?_⟩` and prove the remaining obligations. Break down `Finset.mem_insert.1 hp with rfl | hp` into its components or cases. Conclude with `hxq`. Conclude with `hx p hp`.

Take `⟨y, hy⟩` from `exists_hform_not_mem σ hσ h2 hδ m J hdet q.asIdeal q.isMaximal`. Establish `hfix` using `hform_self_fixed σ hσ J hJ x`. Establish `hmemc : ∀ {P : Ideal A}, hform σ J x x ∈ P → hform σ J x x ∈ P.comap σ` using `fun h => by`. Rewrite using `[Ideal.mem_comap, hfix]`. Conclude with `h`.

Establish `hnotc : ∀ {P : Ideal A}, hform σ J x x ∉ P → hform σ J x x ∉ P.comap σ` using `fun h h' => by`. Rewrite `h'` using `[Ideal.mem_comap, hfix]`. Conclude with `h h'`. Establish `hqm` using `q.isMaximal`. Establish `hqc` using `comap_isMaximal σ hσ q.asIdeal q.isMaximal`.

Establish `hL : ∀ {Q : Ideal A}, Q.IsMaximal → hform σ J x x ∉ Q → IsCoprime (q.asIdeal * q.asIdeal.comap σ) Q` using `fun hQ hn => IsCoprime.mul_left (isCoprime_of_mem_not_mem hqm hQ hxq hn) (isCoprime_of_mem_not_mem hqc hQ (hmemc hxq) hn)`. Establish `hK₁ : IsCoprime (q.asIdeal * q.asIdeal.comap σ) (⨅ p ∈ T, p.asIdeal)` using `Ideal.isCoprime_biInf fun p hp => hL p.isMaximal (hx p hp)`. Establish `hK₂ : IsCoprime (q.asIdeal * q.asIdeal.comap σ) (⨅ p ∈ T, p.asIdeal.comap σ)` using `Ideal.isCoprime_biInf fun p hp => hL (comap_isMaximal σ hσ _ p.isMaximal) (hnotc (hx p hp))`. Take `⟨u, hu, c, hc, huc⟩` from `Ideal.isCoprime_iff_exists.1 (hK₁.mul_right hK₂)`. Establish `hc₁ : ∀ p ∈ T, c ∈ p.asIdeal` using `fun p hp => (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 (Ideal.mul_le_left hc) p) hp`.

Establish `hc₂ : ∀ p ∈ T, σ c ∈ p.asIdeal` using `fun p hp => Ideal.mem_comap.1 ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 (Ideal.mul_le_right hc) p) hp)`. Establish `hu₁ : u ∈ q.asIdeal` using `Ideal.mul_le_right (I := q.asIdeal.comap σ) (by rwa [mul_comm] at hu)`. Establish `hu₂ : σ u ∈ q.asIdeal` using `Ideal.mem_comap.1 (Ideal.mul_le_left (J := q.asIdeal) (by rwa [mul_comm] at hu))`. Use `⟨u • x + c • y, fun p hp => ?_⟩` and prove the remaining obligations. Establish `hu' : u = 1 - c` using `by rw [← huc]; ring`.

Break down `Finset.mem_insert.1 hp with rfl | hp` into its components or cases. Introduce `hz`. Use `hy ?_` and prove the remaining obligations. Establish `h` using `hform_self_congr σ J p.asIdeal y (u • x + c • y) (fun i => ?_) (fun i => ?_)`. Simplify using `using p.asIdeal.sub_mem hz h`.

Establish `: (u • x + c • y) i - y i = u * (x i - y i)`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hu']`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `p.asIdeal.mul_mem_right _ hu₁`.

Establish `: (u • x + c • y) i - y i = u * (x i - y i)`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hu']`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, map_mul]`. Conclude with `p.asIdeal.mul_mem_right _ hu₂`.

Introduce `hz`. Use `hx p hp ?_` and prove the remaining obligations. Establish `h` using `hform_self_congr σ J p.asIdeal x (u • x + c • y) (fun i => ?_) (fun i => ?_)`. Simplify using `using p.asIdeal.sub_mem hz h`. Establish `: (u • x + c • y) i - x i = c * (y i - x i)`.

Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hu']`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `p.asIdeal.mul_mem_right _ (hc₁ p hp)`. Establish `: (u • x + c • y) i - x i = c * (y i - x i)`.

Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hu']`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, map_mul]`. Conclude with `p.asIdeal.mul_mem_right _ (hc₂ p hp)`.
-/
theorem exists_good_on_finset [Finite (MaximalSpectrum A)] (σ : A →+* A) (hσ : ∀ y, σ (σ y) = y)
    (h2 : IsUnit (2 : A)) (hδ : ∃ δ : A, IsUnit δ ∧ σ δ = -δ) (m : ℕ)
    (J : Matrix (Fin (m + 1)) (Fin (m + 1)) A) (hJ : ∀ i j, σ (J j i) = J i j)
    (hdet : IsUnit J.det) (T : Finset (MaximalSpectrum A)) :
    ∃ x, ∀ p ∈ T, hform σ J x x ∉ p.asIdeal := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert q T _ ih =>
    obtain ⟨x, hx⟩ := ih
    by_cases hxq : hform σ J x x ∈ q.asIdeal
    swap
    · refine ⟨x, fun p hp => ?_⟩
      rcases Finset.mem_insert.1 hp with rfl | hp
      · exact hxq
      · exact hx p hp
    obtain ⟨y, hy⟩ := exists_hform_not_mem σ hσ h2 hδ m J hdet q.asIdeal q.isMaximal
    have hfix := hform_self_fixed σ hσ J hJ x
    have hmemc : ∀ {P : Ideal A}, hform σ J x x ∈ P → hform σ J x x ∈ P.comap σ := fun h => by
      rw [Ideal.mem_comap, hfix]; exact h
    have hnotc : ∀ {P : Ideal A}, hform σ J x x ∉ P → hform σ J x x ∉ P.comap σ := fun h h' => by
      rw [Ideal.mem_comap, hfix] at h'; exact h h'
    have hqm := q.isMaximal
    have hqc := comap_isMaximal σ hσ q.asIdeal q.isMaximal
    have hL : ∀ {Q : Ideal A}, Q.IsMaximal → hform σ J x x ∉ Q →
        IsCoprime (q.asIdeal * q.asIdeal.comap σ) Q := fun hQ hn =>
      IsCoprime.mul_left (isCoprime_of_mem_not_mem hqm hQ hxq hn)
        (isCoprime_of_mem_not_mem hqc hQ (hmemc hxq) hn)
    have hK₁ : IsCoprime (q.asIdeal * q.asIdeal.comap σ) (⨅ p ∈ T, p.asIdeal) :=
      Ideal.isCoprime_biInf fun p hp => hL p.isMaximal (hx p hp)
    have hK₂ : IsCoprime (q.asIdeal * q.asIdeal.comap σ) (⨅ p ∈ T, p.asIdeal.comap σ) :=
      Ideal.isCoprime_biInf fun p hp =>
        hL (comap_isMaximal σ hσ _ p.isMaximal) (hnotc (hx p hp))
    obtain ⟨u, hu, c, hc, huc⟩ := Ideal.isCoprime_iff_exists.1 (hK₁.mul_right hK₂)
    have hc₁ : ∀ p ∈ T, c ∈ p.asIdeal := fun p hp =>
      (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 (Ideal.mul_le_left hc) p) hp
    have hc₂ : ∀ p ∈ T, σ c ∈ p.asIdeal := fun p hp =>
      Ideal.mem_comap.1 ((Submodule.mem_iInf _).1
        ((Submodule.mem_iInf _).1 (Ideal.mul_le_right hc) p) hp)
    have hu₁ : u ∈ q.asIdeal := Ideal.mul_le_right (I := q.asIdeal.comap σ) (by rwa [mul_comm] at hu)
    have hu₂ : σ u ∈ q.asIdeal := Ideal.mem_comap.1 (Ideal.mul_le_left (J := q.asIdeal) (by rwa [mul_comm] at hu))
    refine ⟨u • x + c • y, fun p hp => ?_⟩
    have hu' : u = 1 - c := by rw [← huc]; ring
    rcases Finset.mem_insert.1 hp with rfl | hp
    · intro hz
      refine hy ?_
      have h := hform_self_congr σ J p.asIdeal y (u • x + c • y)
        (fun i => ?_) (fun i => ?_)
      · simpa using p.asIdeal.sub_mem hz h
      · have : (u • x + c • y) i - y i = u * (x i - y i) := by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hu']; ring
        rw [this]
        exact p.asIdeal.mul_mem_right _ hu₁
      · have : (u • x + c • y) i - y i = u * (x i - y i) := by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hu']; ring
        rw [this, map_mul]
        exact p.asIdeal.mul_mem_right _ hu₂
    · intro hz
      refine hx p hp ?_
      have h := hform_self_congr σ J p.asIdeal x (u • x + c • y)
        (fun i => ?_) (fun i => ?_)
      · simpa using p.asIdeal.sub_mem hz h
      · have : (u • x + c • y) i - x i = c * (y i - x i) := by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hu']; ring
        rw [this]
        exact p.asIdeal.mul_mem_right _ (hc₁ p hp)
      · have : (u • x + c • y) i - x i = c * (y i - x i) := by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hu']; ring
        rw [this, map_mul]
        exact p.asIdeal.mul_mem_right _ (hc₂ p hp)

/- English proof (translation)
Introduce `A _ _ σ hσ h2 hδ m J hJ hdet`. Use `Fintype.ofFinite (MaximalSpectrum A)` as an intermediate fact. Take `⟨x, hx⟩` from `exists_good_on_finset σ hσ h2 hδ m J hJ hdet Finset.univ`. Use `⟨x, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hnu`.

Take `⟨P, hP, hmem⟩` from `exists_max_ideal_of_mem_nonunits hnu`. Conclude with `hx ⟨P, hP⟩ (Finset.mem_univ _) hmem`.
-/
theorem exists_isUnit_hform : ∀ (A : Type) [CommRing A] [Finite (MaximalSpectrum A)] (σ : A →+* A),
    (∀ y, σ (σ y) = y) → IsUnit (2 : A) → (∃ δ : A, IsUnit δ ∧ σ δ = -δ) →
    ∀ (m : ℕ) (J : Matrix (Fin (m + 1)) (Fin (m + 1)) A), (∀ i j, σ (J j i) = J i j) →
    IsUnit J.det → ∃ x, IsUnit (HeckeCharacterZeroLocus.SiegelWeilU.hform σ J x x) := by
  intro A _ _ σ hσ h2 hδ m J hJ hdet
  have := Fintype.ofFinite (MaximalSpectrum A)
  obtain ⟨x, hx⟩ := exists_good_on_finset σ hσ h2 hδ m J hJ hdet Finset.univ
  refine ⟨x, ?_⟩
  by_contra hnu
  obtain ⟨P, hP, hmem⟩ := exists_max_ideal_of_mem_nonunits hnu
  exact hx ⟨P, hP⟩ (Finset.mem_univ _) hmem

end GlobalTheory.CompanionTheory.SW.UnitRep
