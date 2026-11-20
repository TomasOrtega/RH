import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardNonempty
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

namespace GlobalTheory.CechPoset

variable {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R)

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem mn_ne (s : Finset κ) (h : s.Nonempty) : mn (ne s h) = s.min' h := rfl

/- English proof (translation)
The claim follows from `le_antisymm (Finset.min'_le _ _ hm) (Finset.le_min' _ _ _ hle)`.
-/
private theorem min'_eq_of {s : Finset κ} (h : s.Nonempty) {m : κ} (hm : m ∈ s) (hle : ∀ x ∈ s, m ≤ x) :
    s.min' h = m :=
  le_antisymm (Finset.min'_le _ _ hm) (Finset.le_min' _ _ _ hle)

/- English proof (translation)
The claim follows from `le_antisymm (Finset.max'_le _ _ _ hle) (Finset.le_max' _ _ hm)`.
-/
private theorem max'_eq_of {s : Finset κ} (h : s.Nonempty) {m : κ} (hm : m ∈ s) (hle : ∀ x ∈ s, x ≤ m) :
    s.max' h = m :=
  le_antisymm (Finset.max'_le _ _ _ hle) (Finset.le_max' _ _ hm)

/- English proof (translation)
Take `⟨s, hs⟩` from `s`. Take `⟨t, ht⟩` from `t`. Simplify using `only at e`. Substitute `e` using the available equality. Conclude with `mp_id F _ _`.
-/
private theorem mp_homOf_eq {p : ℕ} (y : CC F p) (s t : {s : Finset κ // s.card = p + 1}) (e : s.1 = t.1)
    (h : s.1 ⊆ t.1) :
    mp F (homOf (a := ne s.1 (card_nonempty s)) (b := ne t.1 (card_nonempty t)) h) (y s) = y t := by
  obtain ⟨s, hs⟩ := s
  obtain ⟨t, ht⟩ := t
  simp only at e
  subst e
  exact mp_id F _ _

/- English proof (translation)
Simplify using `[e2, h]`.
-/
private theorem e2_of_not (y : CC F 2) {a b d : (NE κ)ᵒᵖ} (φ : a ⟶ b) (ψ : b ⟶ d)
    (h : ¬ (mn d < mn b ∧ mn b < mn a)) : e2 F y a b d φ ψ = 0 := by
  simp [e2, h]

/- English proof (translation)
Simplify using `only [e2, LinearMap.pi_apply, dif_pos (And.intro h₁ h₂), LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.proj_apply, AlgHom.toLinearMap_apply]`. Use `congr 1`. Conclude with `mp_homOf_eq F y ⟨_, card_three h₁ h₂⟩ t (Finset.eq_of_subset_of_card_le (triple_subset φ ψ) (by rw [t.2, card_three h₁ h₂])) (triple_subset φ ψ)`.
-/
private theorem e2_of_lt (y : CC F 2) (t : {s : Finset κ // s.card = 2 + 1}) {a b : (NE κ)ᵒᵖ} (φ : a ⟶ b)
    (ψ : b ⟶ ne t.1 (card_nonempty t)) (h₁ : mn (ne t.1 (card_nonempty t)) < mn b) (h₂ : mn b < mn a) :
    e2 F y a b _ φ ψ = - y t := by
  simp only [e2, LinearMap.pi_apply, dif_pos (And.intro h₁ h₂), LinearMap.neg_apply,
    LinearMap.comp_apply, LinearMap.proj_apply, AlgHom.toLinearMap_apply]
  congr 1
  exact mp_homOf_eq F y ⟨_, card_three h₁ h₂⟩ t
    (Finset.eq_of_subset_of_card_le (triple_subset φ ψ) (by rw [t.2, card_three h₁ h₂]))
    (triple_subset φ ψ)

/- English proof (translation)
Substitute `e` using the available equality. Both sides reduce to the same expression.
-/
private theorem f_single (f : C1 F) {m x : κ} (e : m = x) {T : (NE κ)ᵒᵖ}
    (φ : ne {m} (Finset.singleton_nonempty m) ⟶ T) (hx : ({x} : Finset κ) ⊆ sub T) :
    f _ T φ = f (ne {x} (Finset.singleton_nonempty x)) T (homOf hx) := by
  subst e; rfl

def cechOfPosetOne (f : C1 F) : CC F 1 := fun P =>
  f (ne {P.1.min' (card_nonempty P)} (Finset.singleton_nonempty _)) (ne P.1 (card_nonempty P))
      (homOf (Finset.singleton_subset_iff.2 (Finset.min'_mem _ _))) -
    f (ne {P.1.max' (card_nonempty P)} (Finset.singleton_nonempty _)) (ne P.1 (card_nonempty P))
      (homOf (Finset.singleton_subset_iff.2 (Finset.max'_mem _ _)))

variable {F}

/- English proof (translation)
Use `congrFun (congrFun (congrFun (congrFun (congrFun hf a) P) T) φ) ψ` as an intermediate fact. Rewrite `this` using `[d1_apply]`. Rewrite using `[this]`. Normalize the expressions using the abelian group laws.
-/
private theorem restrict_of_d1 {y : CC F 2} {f : C1 F} (hf : e2 F y = d1 F f) {a P T : (NE κ)ᵒᵖ}
    (φ : a ⟶ P) (ψ : P ⟶ T) :
    mp F ψ (f a P φ) = f a T (φ ≫ ψ) - f P T ψ + e2 F y a P T φ ψ := by
  have := congrFun (congrFun (congrFun (congrFun (congrFun hf a) P) T) φ) ψ
  rw [d1_apply] at this
  rw [this]; abel

/- English proof (translation)
Simplify using `only [cechOfPosetOne, map_sub]`. Rewrite using `[restrict_of_d1 hf, restrict_of_d1 hf]`. Normalize the expressions using the abelian group laws.
-/
theorem restrict_cechOfPosetOne {y : CC F 2} {f : C1 F} (hf : e2 F y = d1 F f)
    (P : {s : Finset κ // s.card = 1 + 1}) (T : (NE κ)ᵒᵖ) (h : P.1 ⊆ sub T) :
    mp F (homOf (a := ne P.1 (card_nonempty P)) (b := T) h) (cechOfPosetOne F f P) =
      f (ne {P.1.min' (card_nonempty P)} (Finset.singleton_nonempty _)) T
        (homOf (b := ne P.1 (card_nonempty P)) (Finset.singleton_subset_iff.2 (Finset.min'_mem _ _)) ≫ homOf h) -
      f (ne {P.1.max' (card_nonempty P)} (Finset.singleton_nonempty _)) T
        (homOf (b := ne P.1 (card_nonempty P)) (Finset.singleton_subset_iff.2 (Finset.max'_mem _ _)) ≫ homOf h) +
      e2 F y (ne {P.1.min' (card_nonempty P)} (Finset.singleton_nonempty _)) (ne P.1 (card_nonempty P)) T
        (homOf (Finset.singleton_subset_iff.2 (Finset.min'_mem _ _))) (homOf h) -
      e2 F y (ne {P.1.max' (card_nonempty P)} (Finset.singleton_nonempty _)) (ne P.1 (card_nonempty P)) T
        (homOf (Finset.singleton_subset_iff.2 (Finset.max'_mem _ _))) (homOf h) := by
  simp only [cechOfPosetOne, map_sub]
  rw [restrict_of_d1 hf, restrict_of_d1 hf]
  abel

/- English proof (translation)
The claim follows from `e2_of_not F y φ ψ (fun h => (lt_irrefl _) (h.2.trans_eq (Finset.min'_singleton _).symm))`.
-/
private theorem e2_min_single (y : CC F 2) (P : {s : Finset κ // s.card = 1 + 1}) (T : (NE κ)ᵒᵖ)
    (φ : ne {P.1.min' (card_nonempty P)} (Finset.singleton_nonempty _) ⟶ ne P.1 (card_nonempty P))
    (ψ : ne P.1 (card_nonempty P) ⟶ T) :
    e2 F y _ _ T φ ψ = 0 :=
  e2_of_not F y φ ψ (fun h => (lt_irrefl _) (h.2.trans_eq (Finset.min'_singleton _).symm))

/- English proof (translation)
The claim follows from `e2_of_not F y φ ψ (fun h' => h h'.1)`.
-/
private theorem e2_max_single_of_le (y : CC F 2) (P : {s : Finset κ // s.card = 1 + 1}) (T : (NE κ)ᵒᵖ)
    (φ : ne {P.1.max' (card_nonempty P)} (Finset.singleton_nonempty _) ⟶ ne P.1 (card_nonempty P))
    (ψ : ne P.1 (card_nonempty P) ⟶ T) (h : ¬ mn T < P.1.min' (card_nonempty P)) :
    e2 F y _ _ T φ ψ = 0 :=
  e2_of_not F y φ ψ (fun h' => h h'.1)

/- English proof (translation)
The claim follows from `e2_of_lt F y t φ ψ h (by rw [mn_ne, mn_ne, Finset.min'_singleton] exact Finset.min'_lt_max'_of_card _ (by rw [P.2]; omega))`.
-/
private theorem e2_max_single_of_lt (y : CC F 2) (P : {s : Finset κ // s.card = 1 + 1})
    (t : {s : Finset κ // s.card = 2 + 1})
    (φ : ne {P.1.max' (card_nonempty P)} (Finset.singleton_nonempty _) ⟶ ne P.1 (card_nonempty P))
    (ψ : ne P.1 (card_nonempty P) ⟶ ne t.1 (card_nonempty t))
    (h : mn (ne t.1 (card_nonempty t)) < P.1.min' (card_nonempty P)) :
    e2 F y _ _ _ φ ψ = - y t :=
  e2_of_lt F y t φ ψ h (by
    rw [mn_ne, mn_ne, Finset.min'_singleton]
    exact Finset.min'_lt_max'_of_card _ (by rw [P.2]; omega))

/- English proof (translation)
Establish `hik` using `hij.trans hjk`. Establish `hi : i ∈ t.1` using `by rw [ht]; simp`. Establish `hj : j ∈ t.1` using `by rw [ht]; simp`. Establish `hk : k ∈ t.1` using `by rw [ht]; simp`. Establish `huniv : (Finset.univ : Finset t.1) = {⟨i, hi⟩, ⟨j, hj⟩, ⟨k, hk⟩}`.

Use extensionality with `⟨x, hx⟩`. Establish `hx'` using `hx`. Rewrite `hx'` using `[ht]`. Simplify using `only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq, true_iff]`. Simplify using `using hx'`.

Rewrite using `[δ_apply, huniv, Finset.sum_insert (by simp [hij.ne, hik.ne]), Finset.sum_insert (by simp [hjk.ne]), Finset.sum_singleton]`. Use `erw [restrict_cechOfPosetOne hf, restrict_cechOfPosetOne hf, restrict_cechOfPosetOne hf]`. Apply the tactic sequence `all_goals first | exact Finset.erase_subset _ _ | skip`. Establish `hle : ∀ x ∈ t.1, i ≤ x`. Introduce `x hx`.

Rewrite `hx` using `[ht]`. Simplify using `only [Finset.mem_insert, Finset.mem_singleton] at hx`. Break down `hx with rfl | rfl | rfl` into its components or cases. Use `exacts [le_rfl, hij.le, hik.le]`. Establish `tmin : mn (ne t.1 (card_nonempty t)) = i` using `min'_eq_of _ hi hle`.

Establish `mem3 : ∀ {x z : κ}, z ∈ t.1.erase x ↔ z ≠ x ∧ (z = i ∨ z = j ∨ z = k)`. Introduce `x z`. Rewrite using `[ht]`. Simplify using the standard rewrite rules. Establish `iMin : ∀ h, (Cube.eraseIdx t ⟨i, hi⟩).1.min' h = j` using `fun h => min'_eq_of h (mem3.2 ⟨hij.ne', by simp⟩) (fun z hz => by`.

Take `⟨hne, rfl | rfl | rfl⟩` from `mem3.1 hz`. Use `exacts [absurd rfl hne, le_rfl, hjk.le])`. Establish `iMax : ∀ h, (Cube.eraseIdx t ⟨i, hi⟩).1.max' h = k` using `fun h => max'_eq_of h (mem3.2 ⟨hik.ne', by simp⟩) (fun z hz => by`. Take `⟨hne, rfl | rfl | rfl⟩` from `mem3.1 hz`. Use `exacts [absurd rfl hne, hjk.le, le_rfl])`.

Establish `jMin : ∀ h, (Cube.eraseIdx t ⟨j, hj⟩).1.min' h = i` using `fun h => min'_eq_of h (mem3.2 ⟨hij.ne, by simp⟩) (fun z hz => by`. Take `⟨hne, rfl | rfl | rfl⟩` from `mem3.1 hz`. Use `exacts [le_rfl, absurd rfl hne, hik.le])`. Establish `jMax : ∀ h, (Cube.eraseIdx t ⟨j, hj⟩).1.max' h = k` using `fun h => max'_eq_of h (mem3.2 ⟨hjk.ne', by simp⟩) (fun z hz => by`. Take `⟨hne, rfl | rfl | rfl⟩` from `mem3.1 hz`.

Use `exacts [hik.le, absurd rfl hne, le_rfl])`. Establish `kMin : ∀ h, (Cube.eraseIdx t ⟨k, hk⟩).1.min' h = i` using `fun h => min'_eq_of h (mem3.2 ⟨hik.ne, by simp⟩) (fun z hz => by`. Take `⟨hne, rfl | rfl | rfl⟩` from `mem3.1 hz`. Use `exacts [le_rfl, hij.le, absurd rfl hne])`. Establish `kMax : ∀ h, (Cube.eraseIdx t ⟨k, hk⟩).1.max' h = j` using `fun h => max'_eq_of h (mem3.2 ⟨hjk.ne, by simp⟩) (fun z hz => by`.

Take `⟨hne, rfl | rfl | rfl⟩` from `mem3.1 hz`. Use `exacts [hij.le, le_rfl, absurd rfl hne])`. Establish `hiT : ({i} : Finset κ) ⊆ sub (ne t.1 (card_nonempty t))` using `Finset.singleton_subset_iff.2 hi`. Establish `hjT : ({j} : Finset κ) ⊆ sub (ne t.1 (card_nonempty t))` using `Finset.singleton_subset_iff.2 hj`. Establish `hkT : ({k} : Finset κ) ⊆ sub (ne t.1 (card_nonempty t))` using `Finset.singleton_subset_iff.2 hk`.

Establish `lI : mn (ne t.1 (card_nonempty t)) < (Cube.eraseIdx t ⟨i, hi⟩).1.min' (card_nonempty (Cube.eraseIdx t ⟨i, hi⟩))`. Rewrite using `[tmin, iMin]`. Conclude with `hij`. Establish `lJ : ¬ mn (ne t.1 (card_nonempty t)) < (Cube.eraseIdx t ⟨j, hj⟩).1.min' (card_nonempty (Cube.eraseIdx t ⟨j, hj⟩))`. Rewrite using `[tmin, jMin]`.

Conclude with `lt_irrefl _`. Establish `lK : ¬ mn (ne t.1 (card_nonempty t)) < (Cube.eraseIdx t ⟨k, hk⟩).1.min' (card_nonempty (Cube.eraseIdx t ⟨k, hk⟩))`. Rewrite using `[tmin, kMin]`. Conclude with `lt_irrefl _`. Establish `sI : cubeSign t.1 i = 1` using `cubeSign_eq_one_of_forall_le hle`.

Establish `sJ : cubeSign t.1 j = -1`. Rewrite using `[cubeSign, ht, Finset.filter_insert, Finset.filter_insert, Finset.filter_singleton]`. Simplify using `[hij, hjk.not_gt, lt_irrefl]`. Establish `sK : cubeSign t.1 k = 1`. Rewrite using `[cubeSign, ht, Finset.filter_insert, Finset.filter_insert, Finset.filter_singleton]`.

Simplify using `[hik, hjk, lt_irrefl, Finset.card_pair hij.ne]`. Use `erw [e2_min_single y (Cube.eraseIdx t ⟨i, hi⟩) (ne t.1 (card_nonempty t)), e2_min_single y (Cube.eraseIdx t ⟨j, hj⟩) (ne t.1 (card_nonempty t)), e2_min_single y (Cube.eraseIdx t ⟨k, hk⟩) (ne t.1 (card_nonempty t)), e2_max_single_of_lt y (Cube.eraseIdx t ⟨i, hi⟩) t _ _ lI, e2_max_ …`. Use `erw [sI, sJ, sK]`. Simplify using `only [one_smul, neg_smul, sub_zero, add_zero, sub_neg_eq_add]`. Normalize the expressions using the abelian group laws.
-/
theorem delta_cechOfPosetOne_of_eq {y : CC F 2} {f : C1 F} (hf : e2 F y = d1 F f)
    (t : {s : Finset κ // s.card = 2 + 1}) {i j k : κ} (hij : i < j) (hjk : j < k)
    (ht : t.1 = {i, j, k}) : δ F 1 (cechOfPosetOne F f) t = y t := by
  have hik := hij.trans hjk
  have hi : i ∈ t.1 := by rw [ht]; simp
  have hj : j ∈ t.1 := by rw [ht]; simp
  have hk : k ∈ t.1 := by rw [ht]; simp
  have huniv : (Finset.univ : Finset t.1) = {⟨i, hi⟩, ⟨j, hj⟩, ⟨k, hk⟩} := by
    ext ⟨x, hx⟩
    have hx' := hx
    rw [ht] at hx'
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq, true_iff]
    simpa using hx'
  rw [δ_apply, huniv, Finset.sum_insert (by simp [hij.ne, hik.ne]), Finset.sum_insert (by simp [hjk.ne]),
    Finset.sum_singleton]
  erw [restrict_cechOfPosetOne hf, restrict_cechOfPosetOne hf, restrict_cechOfPosetOne hf]
  all_goals first | exact Finset.erase_subset _ _ | skip
  have hle : ∀ x ∈ t.1, i ≤ x := by
    intro x hx
    rw [ht] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    exacts [le_rfl, hij.le, hik.le]
  have tmin : mn (ne t.1 (card_nonempty t)) = i := min'_eq_of _ hi hle
  have mem3 : ∀ {x z : κ}, z ∈ t.1.erase x ↔ z ≠ x ∧ (z = i ∨ z = j ∨ z = k) := by
    intro x z; rw [ht]; simp
  have iMin : ∀ h, (Cube.eraseIdx t ⟨i, hi⟩).1.min' h = j := fun h =>
    min'_eq_of h (mem3.2 ⟨hij.ne', by simp⟩) (fun z hz => by
      obtain ⟨hne, rfl | rfl | rfl⟩ := mem3.1 hz
      exacts [absurd rfl hne, le_rfl, hjk.le])
  have iMax : ∀ h, (Cube.eraseIdx t ⟨i, hi⟩).1.max' h = k := fun h =>
    max'_eq_of h (mem3.2 ⟨hik.ne', by simp⟩) (fun z hz => by
      obtain ⟨hne, rfl | rfl | rfl⟩ := mem3.1 hz
      exacts [absurd rfl hne, hjk.le, le_rfl])
  have jMin : ∀ h, (Cube.eraseIdx t ⟨j, hj⟩).1.min' h = i := fun h =>
    min'_eq_of h (mem3.2 ⟨hij.ne, by simp⟩) (fun z hz => by
      obtain ⟨hne, rfl | rfl | rfl⟩ := mem3.1 hz
      exacts [le_rfl, absurd rfl hne, hik.le])
  have jMax : ∀ h, (Cube.eraseIdx t ⟨j, hj⟩).1.max' h = k := fun h =>
    max'_eq_of h (mem3.2 ⟨hjk.ne', by simp⟩) (fun z hz => by
      obtain ⟨hne, rfl | rfl | rfl⟩ := mem3.1 hz
      exacts [hik.le, absurd rfl hne, le_rfl])
  have kMin : ∀ h, (Cube.eraseIdx t ⟨k, hk⟩).1.min' h = i := fun h =>
    min'_eq_of h (mem3.2 ⟨hik.ne, by simp⟩) (fun z hz => by
      obtain ⟨hne, rfl | rfl | rfl⟩ := mem3.1 hz
      exacts [le_rfl, hij.le, absurd rfl hne])
  have kMax : ∀ h, (Cube.eraseIdx t ⟨k, hk⟩).1.max' h = j := fun h =>
    max'_eq_of h (mem3.2 ⟨hjk.ne, by simp⟩) (fun z hz => by
      obtain ⟨hne, rfl | rfl | rfl⟩ := mem3.1 hz
      exacts [hij.le, le_rfl, absurd rfl hne])
  have hiT : ({i} : Finset κ) ⊆ sub (ne t.1 (card_nonempty t)) := Finset.singleton_subset_iff.2 hi
  have hjT : ({j} : Finset κ) ⊆ sub (ne t.1 (card_nonempty t)) := Finset.singleton_subset_iff.2 hj
  have hkT : ({k} : Finset κ) ⊆ sub (ne t.1 (card_nonempty t)) := Finset.singleton_subset_iff.2 hk
  have lI : mn (ne t.1 (card_nonempty t)) <
      (Cube.eraseIdx t ⟨i, hi⟩).1.min' (card_nonempty (Cube.eraseIdx t ⟨i, hi⟩)) := by
    rw [tmin, iMin]; exact hij
  have lJ : ¬ mn (ne t.1 (card_nonempty t)) <
      (Cube.eraseIdx t ⟨j, hj⟩).1.min' (card_nonempty (Cube.eraseIdx t ⟨j, hj⟩)) := by
    rw [tmin, jMin]; exact lt_irrefl _
  have lK : ¬ mn (ne t.1 (card_nonempty t)) <
      (Cube.eraseIdx t ⟨k, hk⟩).1.min' (card_nonempty (Cube.eraseIdx t ⟨k, hk⟩)) := by
    rw [tmin, kMin]; exact lt_irrefl _
  have sI : cubeSign t.1 i = 1 := cubeSign_eq_one_of_forall_le hle
  have sJ : cubeSign t.1 j = -1 := by
    rw [cubeSign, ht, Finset.filter_insert, Finset.filter_insert, Finset.filter_singleton]
    simp [hij, hjk.not_gt, lt_irrefl]
  have sK : cubeSign t.1 k = 1 := by
    rw [cubeSign, ht, Finset.filter_insert, Finset.filter_insert, Finset.filter_singleton]
    simp [hik, hjk, lt_irrefl, Finset.card_pair hij.ne]
  erw [e2_min_single y (Cube.eraseIdx t ⟨i, hi⟩) (ne t.1 (card_nonempty t)),
    e2_min_single y (Cube.eraseIdx t ⟨j, hj⟩) (ne t.1 (card_nonempty t)),
    e2_min_single y (Cube.eraseIdx t ⟨k, hk⟩) (ne t.1 (card_nonempty t)),
    e2_max_single_of_lt y (Cube.eraseIdx t ⟨i, hi⟩) t _ _ lI,
    e2_max_single_of_le y (Cube.eraseIdx t ⟨j, hj⟩) _ _ _ lJ,
    e2_max_single_of_le y (Cube.eraseIdx t ⟨k, hk⟩) _ _ _ lK,
    f_single F f (iMin _) _ hjT, f_single F f (iMax _) _ hkT,
    f_single F f (jMin _) _ hiT, f_single F f (jMax _) _ hkT,
    f_single F f (kMin _) _ hiT, f_single F f (kMax _) _ hjT]
  erw [sI, sJ, sK]
  simp only [one_smul, neg_smul, sub_zero, add_zero, sub_neg_eq_add]
  abel

end GlobalTheory.CechPoset

namespace GlobalTheory.CechPoset

/- English proof (translation)
Introduce `κ _ R _ F y _ f hf`. Use `⟨cechOfPosetOne F f, funext fun (t : {s : Finset κ // s.card = 2 + 1}) => ?_⟩` and prove the remaining obligations. Take `⟨a, b, d, hab, had, hbd, ht⟩` from `Finset.card_eq_three.1 t.2`. Apply the tactic sequence `rcases lt_or_gt_of_ne hab with h₁ | h₁ <;> rcases lt_or_gt_of_ne had with h₂ | h₂ <;>`. Break down `lt_or_gt_of_ne hbd with h₃ | h₃` into its components or cases.

Apply the tactic sequence `all_goals first`. Consider the case `exact delta_cechOfPosetOne_of_eq hf t (by assumption : a < b) (by assumption : b < d) (ht.trans (by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; try tauto))`. Consider the case `exact delta_cechOfPosetOne_of_eq hf t (by assumption : a < d) (by assumption : d < b) (ht.trans (by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; try tauto))`. Consider the case `exact delta_cechOfPosetOne_of_eq hf t (by assumption : b < a) (by assumption : a < d) (ht.trans (by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; try tauto))`. Consider the case `exact delta_cechOfPosetOne_of_eq hf t (by assumption : b < d) (by assumption : d < a) (ht.trans (by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; try tauto))`.

Consider the case `exact delta_cechOfPosetOne_of_eq hf t (by assumption : d < a) (by assumption : a < b) (ht.trans (by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; try tauto))`. Consider the case `exact delta_cechOfPosetOne_of_eq hf t (by assumption : d < b) (by assumption : b < a) (ht.trans (by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; try tauto))`. Consider the case `exact (lt_irrefl _ ((h₁.trans h₃).trans h₂)).elim`. Consider the case `exact (lt_irrefl _ ((h₁.trans h₂).trans h₃)).elim`.
-/
theorem exists_cech_coboundary_of_degreeTwo_image_coboundary : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R]
    (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (y : CC F 2), δ F 2 y = 0 → ∀ f : C1 F, e2 F y = d1 F f →
      ∃ c : CC F 1, δ F 1 c = y := by
  intro κ _ R _ F y _ f hf
  refine ⟨cechOfPosetOne F f, funext fun (t : {s : Finset κ // s.card = 2 + 1}) => ?_⟩
  obtain ⟨a, b, d, hab, had, hbd, ht⟩ := Finset.card_eq_three.1 t.2
  rcases lt_or_gt_of_ne hab with h₁ | h₁ <;> rcases lt_or_gt_of_ne had with h₂ | h₂ <;>
    rcases lt_or_gt_of_ne hbd with h₃ | h₃
  all_goals first
    | exact delta_cechOfPosetOne_of_eq hf t (by assumption : a < b) (by assumption : b < d)
        (ht.trans (by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; try tauto))
    | exact delta_cechOfPosetOne_of_eq hf t (by assumption : a < d) (by assumption : d < b)
        (ht.trans (by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; try tauto))
    | exact delta_cechOfPosetOne_of_eq hf t (by assumption : b < a) (by assumption : a < d)
        (ht.trans (by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; try tauto))
    | exact delta_cechOfPosetOne_of_eq hf t (by assumption : b < d) (by assumption : d < a)
        (ht.trans (by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; try tauto))
    | exact delta_cechOfPosetOne_of_eq hf t (by assumption : d < a) (by assumption : a < b)
        (ht.trans (by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; try tauto))
    | exact delta_cechOfPosetOne_of_eq hf t (by assumption : d < b) (by assumption : b < a)
        (ht.trans (by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; try tauto))
    | exact (lt_irrefl _ ((h₁.trans h₃).trans h₂)).elim
    | exact (lt_irrefl _ ((h₁.trans h₂).trans h₃)).elim

end GlobalTheory.CechPoset
