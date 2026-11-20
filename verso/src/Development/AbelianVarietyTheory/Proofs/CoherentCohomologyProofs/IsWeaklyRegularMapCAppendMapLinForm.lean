import Mathlib

open MvPolynomial RingTheory.Sequence

noncomputable section

namespace GlobalTheory

section Variables

variable {R : Type*} [CommRing R] {σ : Type*}

def killVars (R : Type*) [CommRing R] (S : Set σ) :
    MvPolynomial σ R →ₐ[R] MvPolynomial {x : σ // x ∉ S} R :=
  killCompl (f := (Subtype.val : {x : σ // x ∉ S} → σ)) Subtype.val_injective

/- English proof (translation)
The claim follows from `killCompl_rename_app _ p`.
-/
theorem killVars_rename (S : Set σ) (p : MvPolynomial {x : σ // x ∉ S} R) :
    killVars R S (rename Subtype.val p) = p :=
  killCompl_rename_app _ p

/- English proof (translation)
Rewrite using `[← killVars_rename S (X ⟨x, hx⟩), rename_X]`.
-/
theorem killVars_X_of_notMem {S : Set σ} {x : σ} (hx : x ∉ S) :
    killVars R S (X x) = X ⟨x, hx⟩ := by
  rw [← killVars_rename S (X ⟨x, hx⟩), rename_X]

/- English proof (translation)
Establish `: x ∉ Set.range (Subtype.val : {x : σ // x ∉ S} → σ)` using `by simpa using hx`. Simplify using `only [killVars, killCompl, aeval_X]`. Rewrite using `[dif_neg this]`.
-/
theorem killVars_X_of_mem {S : Set σ} {x : σ} (hx : x ∈ S) :
    killVars R S (X x) = 0 := by
  have : x ∉ Set.range (Subtype.val : {x : σ // x ∉ S} → σ) := by simpa using hx
  simp only [killVars, killCompl, aeval_X]
  rw [dif_neg this]

/- English proof (translation)
The claim follows from `(killVars R S).commutes r`.
-/
theorem killVars_C (S : Set σ) (r : R) : killVars R S (C r) = C r :=
  (killVars R S).commutes r

/- English proof (translation)
Introduce `p` and use `⟨_, killVars_rename S p⟩`.
-/
theorem killVars_surjective (S : Set σ) : Function.Surjective (killVars R S) :=
  fun p => ⟨_, killVars_rename S p⟩

/- English proof (translation)
Rewrite using `[← Ideal.Quotient.eq]`. Establish `: (Ideal.Quotient.mkₐ R (Ideal.span (X '' S : Set (MvPolynomial σ R)))) = (Ideal.Quotient.mkₐ R (Ideal.span (X '' S : Set (MvPolynomial σ R)))).comp ((rename Subtype.val).comp (killVars R S))`. Use extensionality with `x`. Distinguish the cases in `hx : x ∈ S`. Simplify using `only [Ideal.Quotient.mkₐ_eq_mk, AlgHom.comp_apply, killVars_X_of_mem hx, map_zero]`.

Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨x, hx, rfl⟩)`. Simplify using `[killVars_X_of_notMem hx]`. Conclude with `DFunLike.congr_fun this p`.
-/
theorem sub_rename_killVars_mem (S : Set σ) (p : MvPolynomial σ R) :
    p - rename Subtype.val (killVars R S p) ∈ Ideal.span (X '' S : Set (MvPolynomial σ R)) := by
  rw [← Ideal.Quotient.eq]
  have : (Ideal.Quotient.mkₐ R (Ideal.span (X '' S : Set (MvPolynomial σ R)))) =
      (Ideal.Quotient.mkₐ R (Ideal.span (X '' S : Set (MvPolynomial σ R)))).comp
        ((rename Subtype.val).comp (killVars R S)) := by
    ext x
    by_cases hx : x ∈ S
    · simp only [Ideal.Quotient.mkₐ_eq_mk, AlgHom.comp_apply, killVars_X_of_mem hx, map_zero]
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨x, hx, rfl⟩)
    · simp [killVars_X_of_notMem hx]
  exact DFunLike.congr_fun this p

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce `p hp`. Rewrite `hp` using `[Ideal.mem_comap]`. Establish `h1 : rename Subtype.val (killVars R S p) ∈ I.map (C : R →+* MvPolynomial σ R)`. Establish `h2` using `Ideal.mem_map_of_mem (rename (Subtype.val : {x : σ // x ∉ S} → σ) : _ →ₐ[R] _).toRingHom hp`.

Rewrite `h2` using `[Ideal.map_map]`. Establish `h3 : (rename (Subtype.val : {x : σ // x ∉ S} → σ) : _ →ₐ[R] _).toRingHom.comp C = (C : R →+* MvPolynomial σ R)`. Use extensionality with `r : 1`. Simplify using the standard rewrite rules. Rewrite `h2` using `[h3]`. Then use the resulting hypothesis.

Use `Ideal.add_mem _ (Ideal.mem_sup_left h1) (Ideal.mem_sup_right (sub_rename_killVars_mem S p))` as an intermediate fact. Simplify using `using this`. Use `sup_le ?_ ?_` and prove the remaining obligations. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `r hr`.

Simplify using `only [Ideal.mem_comap, killVars_C]`. Conclude with `Ideal.mem_map_of_mem _ hr`. Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Simplify using `[killVars_X_of_mem hx]`.
-/
theorem comap_killVars_map_C (S : Set σ) (I : Ideal R) :
    (I.map (C : R →+* MvPolynomial {x : σ // x ∉ S} R)).comap (killVars R S) =
      I.map (C : R →+* MvPolynomial σ R) ⊔ Ideal.span (X '' S) := by
  apply le_antisymm
  · intro p hp
    rw [Ideal.mem_comap] at hp
    have h1 : rename Subtype.val (killVars R S p) ∈ I.map (C : R →+* MvPolynomial σ R) := by
      have h2 := Ideal.mem_map_of_mem
        (rename (Subtype.val : {x : σ // x ∉ S} → σ) : _ →ₐ[R] _).toRingHom hp
      rw [Ideal.map_map] at h2
      have h3 : (rename (Subtype.val : {x : σ // x ∉ S} → σ) : _ →ₐ[R] _).toRingHom.comp C
          = (C : R →+* MvPolynomial σ R) := by
        ext r : 1; simp
      rwa [h3] at h2
    have := Ideal.add_mem _ (Ideal.mem_sup_left h1)
      (Ideal.mem_sup_right (sub_rename_killVars_mem S p))
    simpa using this
  · refine sup_le ?_ ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro r hr
      simp only [Ideal.mem_comap, killVars_C]
      exact Ideal.mem_map_of_mem _ hr
    · rw [Ideal.span_le]
      rintro _ ⟨x, hx, rfl⟩
      simp [killVars_X_of_mem hx]

/- English proof (translation)
Use `comap_killVars_map_C (R := R) S ⊥` as an intermediate fact. Simplify `this` using `[RingHom.ker_eq_comap_bot]`.
-/
theorem ker_killVars (S : Set σ) :
    RingHom.ker (killVars R S) = Ideal.span (X '' S) := by
  have := comap_killVars_map_C (R := R) S ⊥
  simpa [RingHom.ker_eq_comap_bot] using this

/- English proof (translation)
Rewrite using `[← RingHom.comap_ker, MvPolynomial.ker_map, Ideal.mk_ker, ← comap_killVars_map_C]`. Both sides reduce to the same expression.
-/
theorem ker_map_comp_killVars (S : Set σ) (I : Ideal R) :
    RingHom.ker ((MvPolynomial.map (Ideal.Quotient.mk I)).comp (killVars R S).toRingHom) =
      I.map (C : R →+* MvPolynomial σ R) ⊔ Ideal.span (X '' S) := by
  rw [← RingHom.comap_ker, MvPolynomial.ker_map, Ideal.mk_ker, ← comap_killVars_map_C]
  rfl

def quotientSpanXEquiv (R : Type*) [CommRing R] (S : Set σ) :
    (MvPolynomial σ R ⧸ Ideal.span (X '' S : Set (MvPolynomial σ R))) ≃ₐ[R]
      MvPolynomial {x : σ // x ∉ S} R :=
  (Ideal.quotientEquivAlgOfEq R (ker_killVars S).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (killVars_surjective S))

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem quotientSpanXEquiv_mk (S : Set σ) (p : MvPolynomial σ R) :
    quotientSpanXEquiv R S (Ideal.Quotient.mk _ p) = killVars R S p := rfl

/- English proof (translation)
Rewrite `hp`, the goal using `[MvPolynomial.mem_map_C_iff]`. Introduce `m`. Use `hp (Finsupp.single x 1 + m)` as an intermediate fact. Rewrite `this` using `[coeff_X_mul]`. Then use the resulting hypothesis.
-/
theorem mem_map_C_of_X_mul_mem (x : σ) (I : Ideal R) {p : MvPolynomial σ R}
    (hp : X x * p ∈ I.map (C : R →+* MvPolynomial σ R)) :
    p ∈ I.map (C : R →+* MvPolynomial σ R) := by
  rw [MvPolynomial.mem_map_C_iff] at hp ⊢
  intro m
  have := hp (Finsupp.single x 1 + m)
  rwa [coeff_X_mul] at this

/- English proof (translation)
Rewrite `hp`, the goal using `[← comap_killVars_map_C, Ideal.mem_comap]`. Rewrite `hp` using `[map_mul, killVars_X_of_notMem hx]`. Conclude with `mem_map_C_of_X_mul_mem _ I hp`.
-/
theorem mem_of_X_mul_mem {S : Set σ} {x : σ} (hx : x ∉ S) (I : Ideal R) {p : MvPolynomial σ R}
    (hp : X x * p ∈ I.map (C : R →+* MvPolynomial σ R) ⊔ Ideal.span (X '' S)) :
    p ∈ I.map (C : R →+* MvPolynomial σ R) ⊔ Ideal.span (X '' S) := by
  rw [← comap_killVars_map_C, Ideal.mem_comap] at hp ⊢
  rw [map_mul, killVars_X_of_notMem hx] at hp
  exact mem_map_C_of_X_mul_mem _ I hp

/- English proof (translation)
Rewrite using `[Ideal.ofList_append, Ideal.map_ofList]`. Use `congr 1`. Unfold `Ideal.ofList`. Use `congr 1`. Use extensionality with `p`.

Simplify using the standard rewrite rules.
-/
theorem ofList_map_C_append_map_X (rs : List R) (l : List σ) :
    Ideal.ofList (rs.map (C : R →+* MvPolynomial σ R) ++ l.map X) =
      (Ideal.ofList rs).map C ⊔ Ideal.span (X '' {x | x ∈ l}) := by
  rw [Ideal.ofList_append, Ideal.map_ofList]
  congr 1
  unfold Ideal.ofList
  congr 1
  ext p
  simp

/- English proof (translation)
Proceed by induction on `l using List.reverseRecOn with`. Consider the case `nil => simpa using hrs.of_flat (S := MvPolynomial σ R)`. Consider the case `append_singleton l x ih`. Rewrite `hl` using `[List.nodup_append]`. Establish `hx : x ∉ {x | x ∈ l}` using `fun h => hl.2.2 x h x (by simp) rfl`.

Rewrite using `[List.map_append, ← List.append_assoc, isWeaklyRegular_append_iff]`. Use `⟨ih hl.1, ?_⟩` and prove the remaining obligations. Rewrite using `[List.map_singleton, isWeaklyRegular_singleton_iff, isSMulRegular_quotient_iff_mem_of_smul_mem, smul_eq_mul, Ideal.mul_top, ofList_map_C_append_map_X]`. Introduce `p hp`. Conclude with `mem_of_X_mul_mem hx _ hp`.
-/
theorem isWeaklyRegular_map_C_append_map_X {rs : List R} (hrs : IsWeaklyRegular R rs)
    {l : List σ} (hl : l.Nodup) :
    IsWeaklyRegular (MvPolynomial σ R) (rs.map (C : R →+* MvPolynomial σ R) ++ l.map X) := by
  induction l using List.reverseRecOn with
  | nil => simpa using hrs.of_flat (S := MvPolynomial σ R)
  | append_singleton l x ih =>
    rw [List.nodup_append] at hl
    have hx : x ∉ {x | x ∈ l} := fun h => hl.2.2 x h x (by simp) rfl
    rw [List.map_append, ← List.append_assoc, isWeaklyRegular_append_iff]
    refine ⟨ih hl.1, ?_⟩
    rw [List.map_singleton, isWeaklyRegular_singleton_iff, isSMulRegular_quotient_iff_mem_of_smul_mem,
      smul_eq_mul, Ideal.mul_top, ofList_map_C_append_map_X]
    intro p hp
    exact mem_of_X_mul_mem hx _ hp

/- English proof (translation)
Use `⟨isWeaklyRegular_map_C_append_map_X hrs.1 hl, ?_⟩` and prove the remaining obligations. Establish `h` using `hrs.2`. Rewrite `h`, the goal using `[smul_eq_mul, Ideal.mul_top]`. Rewrite using `[ofList_map_C_append_map_X, ← ker_map_comp_killVars]`. Use `haveI : Nontrivial (R ⧸ Ideal.ofList rs) := Ideal.Quotient.nontrivial_iff.2 h.symm`.

Conclude with `(RingHom.ker_ne_top _).symm`.
-/
theorem isRegular_map_C_append_map_X {rs : List R} (hrs : RingTheory.Sequence.IsRegular R rs)
    {l : List σ} (hl : l.Nodup) :
    RingTheory.Sequence.IsRegular (MvPolynomial σ R) (rs.map (C : R →+* MvPolynomial σ R) ++ l.map X) := by
  refine ⟨isWeaklyRegular_map_C_append_map_X hrs.1 hl, ?_⟩
  have h := hrs.2
  rw [smul_eq_mul, Ideal.mul_top] at h ⊢
  rw [ofList_map_C_append_map_X, ← ker_map_comp_killVars]
  haveI : Nontrivial (R ⧸ Ideal.ofList rs) := Ideal.Quotient.nontrivial_iff.2 h.symm
  exact (RingHom.ker_ne_top _).symm

/- English proof (translation)
Simplify using `using isWeaklyRegular_map_C_append_map_X (IsWeaklyRegular.nil R R) hl`.
-/
theorem isWeaklyRegular_map_X {l : List σ} (hl : l.Nodup) :
    IsWeaklyRegular (MvPolynomial σ R) (l.map X : List (MvPolynomial σ R)) := by
  simpa using isWeaklyRegular_map_C_append_map_X (IsWeaklyRegular.nil R R) hl

/- English proof (translation)
Simplify using `using isRegular_map_C_append_map_X (RingTheory.Sequence.IsRegular.nil R R) hl`.
-/
theorem isRegular_map_X [Nontrivial R] {l : List σ} (hl : l.Nodup) :
    RingTheory.Sequence.IsRegular (MvPolynomial σ R) (l.map X : List (MvPolynomial σ R)) := by
  simpa using isRegular_map_C_append_map_X (RingTheory.Sequence.IsRegular.nil R R) hl

/- English proof (translation)
Use `isWeaklyRegular_map_X (R := R) (List.nodup_ofFn.2 he)` as an intermediate fact. Rewrite `this` using `[List.map_ofFn]`. Then use the resulting hypothesis.
-/
theorem isWeaklyRegular_ofFn_X {n : ℕ} {e : Fin n → σ} (he : Function.Injective e) :
    IsWeaklyRegular (MvPolynomial σ R) (List.ofFn fun k => (X (e k) : MvPolynomial σ R)) := by
  have := isWeaklyRegular_map_X (R := R) (List.nodup_ofFn.2 he)
  rwa [List.map_ofFn] at this

/- English proof (translation)
Use `isRegular_map_X (R := R) (List.nodup_ofFn.2 he)` as an intermediate fact. Rewrite `this` using `[List.map_ofFn]`. Then use the resulting hypothesis.
-/
theorem isRegular_ofFn_X [Nontrivial R] {n : ℕ} {e : Fin n → σ} (he : Function.Injective e) :
    RingTheory.Sequence.IsRegular (MvPolynomial σ R) (List.ofFn fun k => (X (e k) : MvPolynomial σ R)) := by
  have := isRegular_map_X (R := R) (List.nodup_ofFn.2 he)
  rwa [List.map_ofFn] at this

/- English proof (translation)
Rewrite using `[← ker_map_comp_killVars]`. Conclude with `RingHom.ker_isPrime _`.
-/
theorem isPrime_map_C_sup_span_X (S : Set σ) (I : Ideal R) [I.IsPrime] :
    (I.map (C : R →+* MvPolynomial σ R) ⊔ Ideal.span (X '' S)).IsPrime := by
  rw [← ker_map_comp_killVars]
  exact RingHom.ker_isPrime _

end Variables

section LinearForms

variable {R : Type*} [CommRing R] {ι J : Type*} [Fintype J]

def linForm (u : J → R) (i : ι) : MvPolynomial (ι × J) R :=
  ∑ j, C (u j) * X (i, j)

def elimIndices (S : Set ι) (j₀ : J) : Set (ι × J) := {x | x.1 ∈ S ∧ x.2 = j₀}

omit [Fintype J] in
/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
@[simp] theorem mem_elimIndices {S : Set ι} {j₀ : J} {x : ι × J} :
    x ∈ elimIndices S j₀ ↔ x.1 ∈ S ∧ x.2 = j₀ := Iff.rfl

/- English proof (translation)
The claim follows from `(Finset.add_sum_erase _ (fun j => (C (u j) * X (i, j) : MvPolynomial (ι × J) R)) (Finset.mem_univ j₀)).symm`.
-/
theorem linForm_eq [DecidableEq J] (u : J → R) (i : ι) (j₀ : J) :
    linForm u i = C (u j₀) * X (i, j₀) + ∑ j ∈ Finset.univ.erase j₀, C (u j) * X (i, j) :=
  (Finset.add_sum_erase _ (fun j => (C (u j) * X (i, j) : MvPolynomial (ι × J) R))
    (Finset.mem_univ j₀)).symm

open Classical in

def linFormHom (u : J → R) (S : Set ι) (j₀ : J) :
    MvPolynomial (ι × J) R →ₐ[R] MvPolynomial (ι × J) R :=
  aeval fun x => if x ∈ elimIndices S j₀ then linForm u x.1 else X x

/- English proof (translation)
Rewrite using `[linFormHom, aeval_X, if_pos (by exact ⟨hi, rfl⟩)]`.
-/
theorem linFormHom_X_of_mem (u : J → R) {S : Set ι} (j₀ : J) {i : ι} (hi : i ∈ S) :
    linFormHom u S j₀ (X (i, j₀)) = linForm u i := by
  rw [linFormHom, aeval_X, if_pos (by exact ⟨hi, rfl⟩)]

/- English proof (translation)
Rewrite using `[linFormHom, aeval_X, if_neg hx]`.
-/
theorem linFormHom_X_of_notMem (u : J → R) {S : Set ι} {j₀ : J} {x : ι × J}
    (hx : x ∉ elimIndices S j₀) : linFormHom u S j₀ (X x) = X x := by
  rw [linFormHom, aeval_X, if_neg hx]

/- English proof (translation)
Rewrite using `[linForm_eq v i j₀, map_add, map_mul, linFormHom_X_of_mem u j₀ hi, map_sum, linForm_eq u i j₀, linForm_eq _ i j₀, if_pos rfl, algHom_C, algebraMap_eq, mul_add, Finset.mul_sum, add_assoc, ← Finset.sum_add_distrib, C_mul, mul_assoc]`. Use `congr 1`. Use `Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations. Establish `hj'` using `Finset.ne_of_mem_erase hj`. Rewrite using `[map_mul, linFormHom_X_of_notMem u (by simp [hj']), if_neg hj', algHom_C, algebraMap_eq, C_add, C_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem linFormHom_linForm [DecidableEq J] (u v : J → R) {S : Set ι} (j₀ : J) {i : ι}
    (hi : i ∈ S) : linFormHom u S j₀ (linForm v i) =
      linForm (fun j => if j = j₀ then v j₀ * u j₀ else v j₀ * u j + v j) i := by
  rw [linForm_eq v i j₀, map_add, map_mul, linFormHom_X_of_mem u j₀ hi, map_sum,
    linForm_eq u i j₀, linForm_eq _ i j₀, if_pos rfl, algHom_C, algebraMap_eq, mul_add,
    Finset.mul_sum, add_assoc, ← Finset.sum_add_distrib, C_mul, mul_assoc]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.ne_of_mem_erase hj
  rw [map_mul, linFormHom_X_of_notMem u (by simp [hj']), if_neg hj', algHom_C, algebraMap_eq,
    C_add, C_mul]
  ring

/- English proof (translation)
Use `MvPolynomial.algHom_ext fun x => ?_` and prove the remaining obligations. Distinguish the cases in `hx : x ∈ elimIndices S j₀`. Take `⟨i, j⟩` from `x`. Take `⟨hi, rfl⟩ : i ∈ S ∧ j = j₀` from `hx`. Rewrite using `[AlgHom.comp_apply, linFormHom_X_of_mem v j hi, linFormHom_linForm u v j hi, linForm_eq _ i j, if_pos rfl, h₀, Finset.sum_eq_zero]`.

Simplify using the standard rewrite rules. Introduce `k hk`. Establish `hk'` using `Finset.ne_of_mem_erase hk`. Rewrite using `[if_neg hk', h k hk', C_0, zero_mul]`. Simplify using `[linFormHom_X_of_notMem _ hx]`.
-/
theorem linFormHom_comp_eq_id {u v : J → R} (S : Set ι) {j₀ : J} (h₀ : v j₀ * u j₀ = 1)
    (h : ∀ j, j ≠ j₀ → v j₀ * u j + v j = 0) :
    (linFormHom u S j₀).comp (linFormHom v S j₀) = AlgHom.id R _ := by
  classical
  refine MvPolynomial.algHom_ext fun x => ?_
  by_cases hx : x ∈ elimIndices S j₀
  · obtain ⟨i, j⟩ := x
    obtain ⟨hi, rfl⟩ : i ∈ S ∧ j = j₀ := hx
    rw [AlgHom.comp_apply, linFormHom_X_of_mem v j hi, linFormHom_linForm u v j hi,
      linForm_eq _ i j, if_pos rfl, h₀, Finset.sum_eq_zero]
    · simp
    · intro k hk
      have hk' := Finset.ne_of_mem_erase hk
      rw [if_neg hk', h k hk', C_0, zero_mul]
  · simp [linFormHom_X_of_notMem _ hx]

open Classical in

def linFormInvCoeff (u : J → R) (j₀ : J) (hu : IsUnit (u j₀)) (j : J) : R :=
  if j = j₀ then (↑hu.unit⁻¹ : R) else -((↑hu.unit⁻¹ : R) * u j)

def linFormEquiv (u : J → R) (S : Set ι) (j₀ : J) (hu : IsUnit (u j₀)) :
    MvPolynomial (ι × J) R ≃ₐ[R] MvPolynomial (ι × J) R :=
  AlgEquiv.ofAlgHom (linFormHom u S j₀) (linFormHom (linFormInvCoeff u j₀ hu) S j₀)
    (linFormHom_comp_eq_id S (by simp [linFormInvCoeff])
      (fun j hj => by simp [linFormInvCoeff, hj]))
    (linFormHom_comp_eq_id S (by simp [linFormInvCoeff])
      (fun j hj => by simp [linFormInvCoeff, hj, ← mul_assoc]))

variable (u : J → R) {j₀ : J} (hu : IsUnit (u j₀))

/- English proof (translation)
The claim follows from `linFormHom_X_of_mem u j₀ hi`.
-/
theorem linFormEquiv_X_of_mem {S : Set ι} {i : ι} (hi : i ∈ S) :
    linFormEquiv u S j₀ hu (X (i, j₀)) = linForm u i :=
  linFormHom_X_of_mem u j₀ hi

/- English proof (translation)
The claim follows from `linFormHom_X_of_notMem u hx`.
-/
theorem linFormEquiv_X_of_notMem {S : Set ι} {x : ι × J} (hx : x ∉ elimIndices S j₀) :
    linFormEquiv u S j₀ hu (X x) = X x :=
  linFormHom_X_of_notMem u hx

/- English proof (translation)
The claim follows from `(linFormEquiv u S j₀ hu).commutes r`.
-/
theorem linFormEquiv_C (S : Set ι) (r : R) : linFormEquiv u S j₀ hu (C r) = C r :=
  (linFormEquiv u S j₀ hu).commutes r

/- English proof (translation)
Rewrite using `[AlgEquiv.symm_apply_eq, linFormEquiv_X_of_mem u hu hi]`.
-/
theorem linFormEquiv_symm_linForm {S : Set ι} {i : ι} (hi : i ∈ S) :
    (linFormEquiv u S j₀ hu).symm (linForm u i) = X (i, j₀) := by
  rw [AlgEquiv.symm_apply_eq, linFormEquiv_X_of_mem u hu hi]

/- English proof (translation)
The claim follows from `linFormHom_X_of_notMem _ hx`.
-/
theorem linFormEquiv_symm_X_of_notMem {S : Set ι} {x : ι × J} (hx : x ∉ elimIndices S j₀) :
    (linFormEquiv u S j₀ hu).symm (X x) = X x :=
  linFormHom_X_of_notMem _ hx

/- English proof (translation)
The claim follows from `linFormHom_X_of_mem _ j₀ hi`.
-/
theorem linFormEquiv_symm_X_of_mem {S : Set ι} {i : ι} (hi : i ∈ S) :
    (linFormEquiv u S j₀ hu).symm (X (i, j₀)) = linForm (linFormInvCoeff u j₀ hu) i :=
  linFormHom_X_of_mem _ j₀ hi

/- English proof (translation)
Use extensionality with `p`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨⟨i, j⟩, ⟨hi, rfl⟩, rfl⟩, rfl⟩`. Conclude with `⟨i, hi, (linFormEquiv_X_of_mem u hu hi).symm⟩`. Introduce and unpack `⟨i, hi, rfl⟩`.

Conclude with `⟨_, ⟨(i, j₀), ⟨hi, rfl⟩, rfl⟩, linFormEquiv_X_of_mem u hu hi⟩`.
-/
theorem image_linFormEquiv_X (S : Set ι) :
    linFormEquiv u S j₀ hu '' (X '' elimIndices S j₀) = linForm u '' S := by
  ext p
  constructor
  · rintro ⟨_, ⟨⟨i, j⟩, ⟨hi, rfl⟩, rfl⟩, rfl⟩
    exact ⟨i, hi, (linFormEquiv_X_of_mem u hu hi).symm⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨_, ⟨(i, j₀), ⟨hi, rfl⟩, rfl⟩, linFormEquiv_X_of_mem u hu hi⟩

def linFormElim (S : Set ι) :
    MvPolynomial (ι × J) R →ₐ[R] MvPolynomial {x : ι × J // x ∉ elimIndices S j₀} R :=
  (killVars R (elimIndices S j₀)).comp (linFormEquiv u S j₀ hu).symm.toAlgHom

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem linFormElim_apply (S : Set ι) (p : MvPolynomial (ι × J) R) :
    linFormElim u hu S p = killVars R (elimIndices S j₀) ((linFormEquiv u S j₀ hu).symm p) := rfl

/- English proof (translation)
Rewrite using `[linFormElim_apply, linFormEquiv_symm_X_of_notMem u hu hx, killVars_X_of_notMem hx]`.
-/
theorem linFormElim_X_of_notMem {S : Set ι} {x : ι × J} (hx : x ∉ elimIndices S j₀) :
    linFormElim u hu S (X x) = X ⟨x, hx⟩ := by
  rw [linFormElim_apply, linFormEquiv_symm_X_of_notMem u hu hx, killVars_X_of_notMem hx]

/- English proof (translation)
Rewrite using `[linFormElim_apply, linFormEquiv_symm_X_of_mem u hu hi, linForm_eq _ i j₀, map_add, map_mul, killVars_X_of_mem (by exact ⟨hi, rfl⟩), mul_zero, zero_add, map_sum, Finset.sum_subtype (p := fun j => j ≠ j₀) _ (by simp), ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, killVars_C, killVars_X_of_notMem (fun h => j.2 h.2), linFormInvCoeff, if_neg j.2, C_neg, neg_mul]`.
-/
theorem linFormElim_X_of_mem {S : Set ι} {i : ι} (hi : i ∈ S) [DecidableEq J] :
    linFormElim u hu S (X (i, j₀)) = -∑ j : {j : J // j ≠ j₀},
      C ((↑hu.unit⁻¹ : R) * u j) * X ⟨(i, j.1), fun h => j.2 h.2⟩ := by
  rw [linFormElim_apply, linFormEquiv_symm_X_of_mem u hu hi, linForm_eq _ i j₀, map_add, map_mul,
    killVars_X_of_mem (by exact ⟨hi, rfl⟩), mul_zero, zero_add, map_sum,
    Finset.sum_subtype (p := fun j => j ≠ j₀) _ (by simp), ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, killVars_C, killVars_X_of_notMem (fun h => j.2 h.2), linFormInvCoeff, if_neg j.2,
    C_neg, neg_mul]

/- English proof (translation)
Rewrite using `[linFormElim_apply, linFormEquiv_symm_linForm u hu hi, killVars_X_of_mem (by exact ⟨hi, rfl⟩)]`.
-/
theorem linFormElim_linForm {S : Set ι} {i : ι} (hi : i ∈ S) :
    linFormElim u hu S (linForm u i) = 0 := by
  rw [linFormElim_apply, linFormEquiv_symm_linForm u hu hi, killVars_X_of_mem (by exact ⟨hi, rfl⟩)]

/- English proof (translation)
Establish `: (linFormElim u hu S).comp (rename Subtype.val) = AlgHom.id R _`. Use `MvPolynomial.algHom_ext fun x => ?_` and prove the remaining obligations. Simplify using `[linFormElim_X_of_notMem u hu x.2]`. Conclude with `DFunLike.congr_fun this p`.
-/
theorem linFormElim_rename (S : Set ι)
    (p : MvPolynomial {x : ι × J // x ∉ elimIndices S j₀} R) :
    linFormElim u hu S (rename Subtype.val p) = p := by
  have : (linFormElim u hu S).comp (rename Subtype.val) = AlgHom.id R _ := by
    refine MvPolynomial.algHom_ext fun x => ?_
    simp [linFormElim_X_of_notMem u hu x.2]
  exact DFunLike.congr_fun this p

/- English proof (translation)
Introduce `p` and use `⟨_, linFormElim_rename u hu S p⟩`.
-/
theorem linFormElim_surjective (S : Set ι) : Function.Surjective (linFormElim u hu S) :=
  fun p => ⟨_, linFormElim_rename u hu S p⟩

/- English proof (translation)
Rewrite using `[Ideal.map_sup, Ideal.map_span, image_linFormEquiv_X]`. Use `congr 1`. Establish `h : (linFormEquiv u S j₀ hu).toRingEquiv.toRingHom.comp C = (C : R →+* MvPolynomial (ι × J) R)` using `RingHom.ext (linFormEquiv_C u hu S)`. Use `conv_rhs => rw [← h, ← Ideal.map_map]`. Both sides reduce to the same expression.
-/
theorem map_linFormEquiv_map_C_sup_span_X (S : Set ι) (I : Ideal R) :
    (I.map (C : R →+* MvPolynomial (ι × J) R) ⊔ Ideal.span (X '' elimIndices S j₀)).map
      (linFormEquiv u S j₀ hu) = I.map C ⊔ Ideal.span (linForm u '' S) := by
  rw [Ideal.map_sup, Ideal.map_span, image_linFormEquiv_X]
  congr 1
  have h : (linFormEquiv u S j₀ hu).toRingEquiv.toRingHom.comp C =
      (C : R →+* MvPolynomial (ι × J) R) := RingHom.ext (linFormEquiv_C u hu S)
  conv_rhs => rw [← h, ← Ideal.map_map]
  rfl

/- English proof (translation)
Rewrite using `[← map_linFormEquiv_map_C_sup_span_X u hu, ← comap_killVars_map_C]`. Use extensionality with `p`. Rewrite using `[Ideal.mem_comap, linFormElim_apply, Ideal.mem_map_of_equiv]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Conclude with `⟨_, h, AlgEquiv.apply_symm_apply _ p⟩`. Introduce and unpack `⟨x, hx, rfl⟩`. Rewrite using `[AlgEquiv.symm_apply_apply]` and apply the resulting hypothesis.
-/
theorem comap_linFormElim_map_C (S : Set ι) (I : Ideal R) :
    (I.map (C : R →+* MvPolynomial {x : ι × J // x ∉ elimIndices S j₀} R)).comap
      (linFormElim u hu S) = I.map C ⊔ Ideal.span (linForm u '' S) := by
  rw [← map_linFormEquiv_map_C_sup_span_X u hu, ← comap_killVars_map_C]
  ext p
  rw [Ideal.mem_comap, linFormElim_apply, Ideal.mem_map_of_equiv]
  constructor
  · intro h
    exact ⟨_, h, AlgEquiv.apply_symm_apply _ p⟩
  · rintro ⟨x, hx, rfl⟩
    rwa [AlgEquiv.symm_apply_apply]

/- English proof (translation)
Use `comap_linFormElim_map_C u hu S ⊥` as an intermediate fact. Simplify `this` using `[RingHom.ker_eq_comap_bot]`.
-/
theorem ker_linFormElim (S : Set ι) :
    RingHom.ker (linFormElim u hu S) = Ideal.span (linForm u '' S) := by
  have := comap_linFormElim_map_C u hu S ⊥
  simpa [RingHom.ker_eq_comap_bot] using this

/- English proof (translation)
Rewrite using `[← RingHom.comap_ker, MvPolynomial.ker_map, Ideal.mk_ker, ← comap_linFormElim_map_C u hu]`. Both sides reduce to the same expression.
-/
theorem ker_map_comp_linFormElim (S : Set ι) (I : Ideal R) :
    RingHom.ker ((MvPolynomial.map (Ideal.Quotient.mk I)).comp (linFormElim u hu S).toRingHom) =
      I.map C ⊔ Ideal.span (linForm u '' S) := by
  rw [← RingHom.comap_ker, MvPolynomial.ker_map, Ideal.mk_ker, ← comap_linFormElim_map_C u hu]
  rfl

def quotientSpanLinFormEquiv (S : Set ι) :
    (MvPolynomial (ι × J) R ⧸ Ideal.span (linForm u '' S)) ≃ₐ[R]
      MvPolynomial {x : ι × J // x ∉ elimIndices S j₀} R :=
  (Ideal.quotientEquivAlgOfEq R (ker_linFormElim u hu S).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (linFormElim_surjective u hu S))

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem quotientSpanLinFormEquiv_mk (S : Set ι) (p : MvPolynomial (ι × J) R) :
    quotientSpanLinFormEquiv u hu S (Ideal.Quotient.mk _ p) = linFormElim u hu S p := rfl

/- English proof (translation)
Rewrite using `[AlgEquiv.symm_apply_eq, quotientSpanLinFormEquiv_mk, linFormElim_rename]`.
-/
theorem quotientSpanLinFormEquiv_symm_apply (S : Set ι)
    (p : MvPolynomial {x : ι × J // x ∉ elimIndices S j₀} R) :
    (quotientSpanLinFormEquiv u hu S).symm p = Ideal.Quotient.mk _ (rename Subtype.val p) := by
  rw [AlgEquiv.symm_apply_eq, quotientSpanLinFormEquiv_mk, linFormElim_rename]

def quotientMapCSupSpanLinFormEquiv (S : Set ι) (I : Ideal R) :
    (MvPolynomial (ι × J) R ⧸
      (I.map (C : R →+* MvPolynomial (ι × J) R) ⊔ Ideal.span (linForm u '' S))) ≃+*
      MvPolynomial {x : ι × J // x ∉ elimIndices S j₀} (R ⧸ I) :=
  (Ideal.quotEquivOfEq (ker_map_comp_linFormElim u hu S I).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      ((MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective).comp
        (linFormElim_surjective u hu S)))

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem quotientMapCSupSpanLinFormEquiv_mk (S : Set ι) (I : Ideal R)
    (p : MvPolynomial (ι × J) R) :
    quotientMapCSupSpanLinFormEquiv u hu S I (Ideal.Quotient.mk _ p) =
      MvPolynomial.map (Ideal.Quotient.mk I) (linFormElim u hu S p) := rfl

/- English proof (translation)
The claim follows from `Set.range_comp (linForm u) e`.
-/
theorem range_linForm_comp {κ : Type*} (e : κ → ι) :
    Set.range (fun k => linForm u (e k)) = linForm u '' Set.range e :=
  Set.range_comp (linForm u) e

include hu

/- English proof (translation)
Rewrite using `[← ker_map_comp_linFormElim u hu]`. Conclude with `RingHom.ker_isPrime _`.
-/
theorem isPrime_map_C_sup_span_linForm (S : Set ι) (I : Ideal R) [I.IsPrime] :
    (I.map (C : R →+* MvPolynomial (ι × J) R) ⊔ Ideal.span (linForm u '' S)).IsPrime := by
  rw [← ker_map_comp_linFormElim u hu]
  exact RingHom.ker_isPrime _

/- English proof (translation)
Rewrite using `[← ker_linFormElim u hu]`. Conclude with `RingHom.ker_isPrime _`.
-/
theorem isPrime_span_linForm [IsDomain R] (S : Set ι) :
    (Ideal.span (linForm u '' S)).IsPrime := by
  rw [← ker_linFormElim u hu]
  exact RingHom.ker_isPrime _

/- English proof (translation)
Establish `h : (rs.map C ++ l.map (linForm u) : List (MvPolynomial (ι × J) R)) = (rs.map C ++ (l.map fun i => (i, j₀)).map X).map (linFormEquiv u Set.univ j₀ hu)`. Simplify using `only [List.map_append, List.map_map]`. Use `congr 1`. Conclude with `List.map_congr_left fun r _ => (linFormEquiv_C u hu _ r).symm`. Conclude with `List.map_congr_left fun i _ => (linFormEquiv_X_of_mem u hu (Set.mem_univ i)).symm`.

Rewrite using `[h, List.forall₂_map_right_iff, List.forall₂_same]`. Introduce `r _ x`. Conclude with `map_mul (linFormEquiv u Set.univ j₀ hu) r x`.
-/
private theorem forall₂_linFormEquiv (rs : List R) (l : List ι) :
    List.Forall₂ (fun (r s : MvPolynomial (ι × J) R) => ∀ x : MvPolynomial (ι × J) R,
      (linFormEquiv u Set.univ j₀ hu).toAddEquiv (r • x) =
        s • (linFormEquiv u Set.univ j₀ hu).toAddEquiv x)
      (rs.map C ++ (l.map fun i => (i, j₀)).map X) (rs.map C ++ l.map (linForm u)) := by
  have h : (rs.map C ++ l.map (linForm u) : List (MvPolynomial (ι × J) R)) =
      (rs.map C ++ (l.map fun i => (i, j₀)).map X).map (linFormEquiv u Set.univ j₀ hu) := by
    simp only [List.map_append, List.map_map]
    congr 1
    · exact List.map_congr_left fun r _ => (linFormEquiv_C u hu _ r).symm
    · exact List.map_congr_left fun i _ => (linFormEquiv_X_of_mem u hu (Set.mem_univ i)).symm
  rw [h, List.forall₂_map_right_iff, List.forall₂_same]
  intro r _ x
  exact map_mul (linFormEquiv u Set.univ j₀ hu) r x

/- English proof (translation)
The claim follows from `(AddEquiv.isWeaklyRegular_congr (forall₂_linFormEquiv u hu rs l)).1 (isWeaklyRegular_map_C_append_map_X hrs (hl.map fun _ _ h => (Prod.ext_iff.1 h).1))`.
-/
theorem isWeaklyRegular_map_C_append_map_linForm {rs : List R} (hrs : IsWeaklyRegular R rs)
    {l : List ι} (hl : l.Nodup) :
    IsWeaklyRegular (MvPolynomial (ι × J) R)
      (rs.map (C : R →+* MvPolynomial (ι × J) R) ++ l.map (linForm u)) :=
  (AddEquiv.isWeaklyRegular_congr (forall₂_linFormEquiv u hu rs l)).1
    (isWeaklyRegular_map_C_append_map_X hrs (hl.map fun _ _ h => (Prod.ext_iff.1 h).1))

/- English proof (translation)
The claim follows from `(AddEquiv.isRegular_congr (forall₂_linFormEquiv u hu rs l)).1 (isRegular_map_C_append_map_X hrs (hl.map fun _ _ h => (Prod.ext_iff.1 h).1))`.
-/
theorem isRegular_map_C_append_map_linForm {rs : List R}
    (hrs : RingTheory.Sequence.IsRegular R rs) {l : List ι} (hl : l.Nodup) :
    RingTheory.Sequence.IsRegular (MvPolynomial (ι × J) R)
      (rs.map (C : R →+* MvPolynomial (ι × J) R) ++ l.map (linForm u)) :=
  (AddEquiv.isRegular_congr (forall₂_linFormEquiv u hu rs l)).1
    (isRegular_map_C_append_map_X hrs (hl.map fun _ _ h => (Prod.ext_iff.1 h).1))

/- English proof (translation)
Simplify using `using isWeaklyRegular_map_C_append_map_linForm u hu (IsWeaklyRegular.nil R R) hl`.
-/
theorem isWeaklyRegular_map_linForm {l : List ι} (hl : l.Nodup) :
    IsWeaklyRegular (MvPolynomial (ι × J) R) (l.map (linForm u)) := by
  simpa using isWeaklyRegular_map_C_append_map_linForm u hu (IsWeaklyRegular.nil R R) hl

/- English proof (translation)
Simplify using `using isRegular_map_C_append_map_linForm u hu (RingTheory.Sequence.IsRegular.nil R R) hl`.
-/
theorem isRegular_map_linForm [Nontrivial R] {l : List ι} (hl : l.Nodup) :
    RingTheory.Sequence.IsRegular (MvPolynomial (ι × J) R) (l.map (linForm u)) := by
  simpa using isRegular_map_C_append_map_linForm u hu (RingTheory.Sequence.IsRegular.nil R R) hl

/- English proof (translation)
Establish `h : IsWeaklyRegular R [r]` using `(isWeaklyRegular_singleton_iff R r).2 (isRegular_iff_mem_nonZeroDivisors.2 hr).left`. Simplify using `using isWeaklyRegular_map_C_append_map_linForm u hu h hl`.
-/
theorem isWeaklyRegular_C_cons_map_linForm {r : R} (hr : r ∈ nonZeroDivisors R)
    {l : List ι} (hl : l.Nodup) :
    IsWeaklyRegular (MvPolynomial (ι × J) R) (C r :: l.map (linForm u)) := by
  have h : IsWeaklyRegular R [r] :=
    (isWeaklyRegular_singleton_iff R r).2 (isRegular_iff_mem_nonZeroDivisors.2 hr).left
  simpa using isWeaklyRegular_map_C_append_map_linForm u hu h hl

/- English proof (translation)
Establish `h : RingTheory.Sequence.IsRegular R [r]`. Use `⟨(isWeaklyRegular_singleton_iff R r).2 (isRegular_iff_mem_nonZeroDivisors.2 hr).left, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_eq_mul, Ideal.mul_top, Ideal.ofList_singleton, ne_comm, ne_eq, Ideal.span_singleton_eq_top]`. Conclude with `hr'`. Simplify using `using isRegular_map_C_append_map_linForm u hu h hl`.
-/
theorem isRegular_C_cons_map_linForm {r : R} (hr : r ∈ nonZeroDivisors R) (hr' : ¬ IsUnit r)
    {l : List ι} (hl : l.Nodup) :
    RingTheory.Sequence.IsRegular (MvPolynomial (ι × J) R) (C r :: l.map (linForm u)) := by
  have h : RingTheory.Sequence.IsRegular R [r] := by
    refine ⟨(isWeaklyRegular_singleton_iff R r).2
      (isRegular_iff_mem_nonZeroDivisors.2 hr).left, ?_⟩
    rw [smul_eq_mul, Ideal.mul_top, Ideal.ofList_singleton, ne_comm, ne_eq,
      Ideal.span_singleton_eq_top]
    exact hr'
  simpa using isRegular_map_C_append_map_linForm u hu h hl

/- English proof (translation)
Use `isWeaklyRegular_map_linForm u hu (List.nodup_ofFn.2 he)` as an intermediate fact. Rewrite `this` using `[List.map_ofFn]`. Then use the resulting hypothesis.
-/
theorem isWeaklyRegular_ofFn_linForm {n : ℕ} {e : Fin n → ι} (he : Function.Injective e) :
    IsWeaklyRegular (MvPolynomial (ι × J) R) (List.ofFn fun k => linForm u (e k)) := by
  have := isWeaklyRegular_map_linForm u hu (List.nodup_ofFn.2 he)
  rwa [List.map_ofFn] at this

/- English proof (translation)
Use `isWeaklyRegular_C_cons_map_linForm u hu hr (List.nodup_ofFn.2 he)` as an intermediate fact. Rewrite `this` using `[List.map_ofFn]`. Then use the resulting hypothesis.
-/
theorem isWeaklyRegular_C_cons_ofFn_linForm {r : R} (hr : r ∈ nonZeroDivisors R)
    {n : ℕ} {e : Fin n → ι} (he : Function.Injective e) :
    IsWeaklyRegular (MvPolynomial (ι × J) R) (C r :: List.ofFn fun k => linForm u (e k)) := by
  have := isWeaklyRegular_C_cons_map_linForm u hu hr (List.nodup_ofFn.2 he)
  rwa [List.map_ofFn] at this

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨linFormEquiv u S j₀ hu, fun _ hi => linFormEquiv_X_of_mem u hu hi, fun _ hx => linFormEquiv_X_of_notMem u hu hx⟩, ⟨quotientSpanLinFormEquiv u hu S, fun x => linFormElim_X_of_notMem u hu x.2⟩, fun _ hl => ⟨isWeaklyRegular_map_linForm u hu hl, fun _ => isRegular_map_linForm u hu …`.
-/
theorem linForm_elimination (S : Set ι) (σ : Type*) :
    (∃ φ : MvPolynomial (ι × J) R ≃ₐ[R] MvPolynomial (ι × J) R,
      (∀ i ∈ S, φ (X (i, j₀)) = ∑ j, C (u j) * X (i, j)) ∧
      ∀ x : ι × J, ¬ (x.1 ∈ S ∧ x.2 = j₀) → φ (X x) = X x) ∧
    (∃ ψ : (MvPolynomial (ι × J) R ⧸ Ideal.span (linForm u '' S)) ≃ₐ[R]
        MvPolynomial {x : ι × J // x ∉ elimIndices S j₀} R,
      ∀ x : {x : ι × J // x ∉ elimIndices S j₀}, ψ (Ideal.Quotient.mk _ (X x.1)) = X x) ∧
    (∀ l : List ι, l.Nodup →
      IsWeaklyRegular (MvPolynomial (ι × J) R) (l.map (linForm u)) ∧
      (Nontrivial R →
        RingTheory.Sequence.IsRegular (MvPolynomial (ι × J) R) (l.map (linForm u))) ∧
      ∀ r ∈ nonZeroDivisors R,
        IsWeaklyRegular (MvPolynomial (ι × J) R) (C r :: l.map (linForm u)) ∧
        (¬ IsUnit r →
          RingTheory.Sequence.IsRegular (MvPolynomial (ι × J) R) (C r :: l.map (linForm u)))) ∧
    (∀ l : List σ, l.Nodup →
      IsWeaklyRegular (MvPolynomial σ R) (l.map X : List (MvPolynomial σ R)) ∧
      (Nontrivial R →
        RingTheory.Sequence.IsRegular (MvPolynomial σ R) (l.map X : List (MvPolynomial σ R)))) :=
  ⟨⟨linFormEquiv u S j₀ hu, fun _ hi => linFormEquiv_X_of_mem u hu hi,
      fun _ hx => linFormEquiv_X_of_notMem u hu hx⟩,
    ⟨quotientSpanLinFormEquiv u hu S, fun x => linFormElim_X_of_notMem u hu x.2⟩,
    fun _ hl => ⟨isWeaklyRegular_map_linForm u hu hl, fun _ => isRegular_map_linForm u hu hl,
      fun _ hr => ⟨isWeaklyRegular_C_cons_map_linForm u hu hr hl,
        fun hr' => isRegular_C_cons_map_linForm u hu hr hr' hl⟩⟩,
    fun _ hl => ⟨isWeaklyRegular_map_X hl, fun _ => isRegular_map_X hl⟩⟩

end LinearForms

end GlobalTheory
