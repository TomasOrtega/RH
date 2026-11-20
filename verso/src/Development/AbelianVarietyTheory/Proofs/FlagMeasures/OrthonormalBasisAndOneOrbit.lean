import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EichlerIsometry

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.SelfDual

open Matrix GlobalTheory.HL.Eichler GlobalTheory.UnramOrder

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => intro N`. Conclude with `⟨fun _ => 0, Subsingleton.elim _ _⟩`. Consider the case `succ n ih`. Introduce `N`.

Apply the tactic sequence `let ι : (Fin n → R) →ₗ[R] (Fin (n + 1) → R) := { toFun := fun v => Fin.cons 0 v map_add' := fun v w => by ext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp map_smul' := fun c v => by ext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp }`. Take `⟨b, hb⟩` from `ih (N.comap ι)`. Take `⟨g, hg⟩` from `IsPrincipalIdealRing.principal (N.map (LinearMap.proj (R := R) (φ := fun _ : Fin (n + 1) => R) 0))`. Take `⟨x, hx, hxg⟩ : g ∈ N.map (LinearMap.proj (R` from `R) (φ := fun _ : Fin (n + 1) => R) 0) := hg ▸ Submodule.mem_span_singleton_self g`. Use `⟨Fin.cons x fun i => ι (b i), le_antisymm (fun y hy => ?_) ?_⟩` and prove the remaining obligations.

Take `⟨a, ha⟩` from `Submodule.mem_span_singleton.1 (hg ▸ Submodule.mem_map_of_mem hy)`. Establish `h0 : (y - a • x) 0 = 0`. Establish `h1 : x 0 = g` using `hxg`. Establish `h2 : a * g = y 0` using `ha`. Simplify using `[h1, h2]`.

Establish `h1 : ι (Fin.tail (y - a • x)) = y - a • x` using `by show Fin.cons 0 (Fin.tail (y - a • x)) = _`. Rewrite using `[← h0, Fin.cons_self_tail]`. Establish `h2 : Fin.tail (y - a • x) ∈ N.comap ι`. Rewrite using `[Submodule.mem_comap, h1]`. Conclude with `N.sub_mem hy (N.smul_mem a hx)`.

Rewrite `h2` using `[hb]`. Take `⟨d, hd⟩` from `(Submodule.mem_span_range_iff_exists_fun R).1 h2`. Use `(Submodule.mem_span_range_iff_exists_fun R).2 ⟨Fin.cons a d, ?_⟩` and prove the remaining obligations. Rewrite `h1` using `[← hd, map_sum]`. Simplify using `only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, ← map_smul, h1]`.

Normalize the expressions using the abelian group laws. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Use `Fin.cases hx (fun i => ?_) i` and prove the remaining obligations. Establish `: b i ∈ N.comap ι` using `hb ▸ Submodule.subset_span ⟨i, rfl⟩`.

Conclude with `this`.
-/
theorem exists_eq_span_range {R : Type*} [CommRing R] [IsPrincipalIdealRing R] (n : ℕ) :
    ∀ N : Submodule R (Fin n → R), ∃ b : Fin n → Fin n → R,
      N = Submodule.span R (Set.range b) := by
  induction n with
  | zero => intro N; exact ⟨fun _ => 0, Subsingleton.elim _ _⟩
  | succ n ih =>
    intro N
    let ι : (Fin n → R) →ₗ[R] (Fin (n + 1) → R) :=
      { toFun := fun v => Fin.cons 0 v
        map_add' := fun v w => by ext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp
        map_smul' := fun c v => by ext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp }
    obtain ⟨b, hb⟩ := ih (N.comap ι)
    obtain ⟨g, hg⟩ := IsPrincipalIdealRing.principal
      (N.map (LinearMap.proj (R := R) (φ := fun _ : Fin (n + 1) => R) 0))
    obtain ⟨x, hx, hxg⟩ : g ∈ N.map (LinearMap.proj (R := R) (φ := fun _ : Fin (n + 1) => R) 0) :=
      hg ▸ Submodule.mem_span_singleton_self g
    refine ⟨Fin.cons x fun i => ι (b i), le_antisymm (fun y hy => ?_) ?_⟩
    · obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 (hg ▸ Submodule.mem_map_of_mem hy)
      have h0 : (y - a • x) 0 = 0 := by
        have h1 : x 0 = g := hxg
        have h2 : a * g = y 0 := ha
        simp [h1, h2]
      have h1 : ι (Fin.tail (y - a • x)) = y - a • x := by
        show Fin.cons 0 (Fin.tail (y - a • x)) = _
        rw [← h0, Fin.cons_self_tail]
      have h2 : Fin.tail (y - a • x) ∈ N.comap ι := by
        rw [Submodule.mem_comap, h1]; exact N.sub_mem hy (N.smul_mem a hx)
      rw [hb] at h2
      obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 h2
      refine (Submodule.mem_span_range_iff_exists_fun R).2 ⟨Fin.cons a d, ?_⟩
      rw [← hd, map_sum] at h1
      simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, ← map_smul, h1]
      abel
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      refine Fin.cases hx (fun i => ?_) i
      have : b i ∈ N.comap ι := hb ▸ Submodule.subset_span ⟨i, rfl⟩
      exact this

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

/- English proof (translation)
Establish `: Module.Finite F E` using `Module.finite_of_finrank_pos (by rw [L.rank]; omega)`. Take `⟨m, hm⟩` from `IsIntegral.exists_multiple_integral_of_isLocalization (nonZeroDivisors 𝒪[F]) (Rₘ := F) x (Algebra.IsIntegral.isIntegral x)`. Use `⟨m, nonZeroDivisors.coe_ne_zero m, (L.O_def _).2 ?_⟩` and prove the remaining obligations. Use `hm using 1` and compare the differences between its conclusion and the goal. Rewrite using `[Submonoid.smul_def, Algebra.smul_def]`.

Both sides reduce to the same expression.
-/
theorem exists_mul_mem (L : LocE F E) (x : E) :
    ∃ c : 𝒪[F], c ≠ 0 ∧ algebraMap F E c * x ∈ L.O := by
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; omega)
  obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
    (nonZeroDivisors 𝒪[F]) (Rₘ := F) x (Algebra.IsIntegral.isIntegral x)
  refine ⟨m, nonZeroDivisors.coe_ne_zero m, (L.O_def _).2 ?_⟩
  convert hm using 1
  rw [Submonoid.smul_def, Algebra.smul_def]
  rfl

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact ⟨1, one_ne_zero, by simp⟩`. Consider the case `insert x s _ ih`. Take `⟨c, hc, h⟩` from `ih`. Take `⟨d, hd, h'⟩` from `exists_mul_mem L x`.

Use `⟨c * d, mul_ne_zero hc hd, fun y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[Subring.coe_mul, map_mul]`. Break down `Finset.mem_insert.1 hy with rfl | hy` into its components or cases. Rewrite using `[mul_assoc]`. Conclude with `L.O.mul_mem ((algebraMap_mem_iff L _).2 c.2) h'`.

Rewrite using `[mul_right_comm]`. Conclude with `L.O.mul_mem (h y hy) ((algebraMap_mem_iff L _).2 d.2)`.
-/
theorem exists_mul_mem_finset (L : LocE F E) (s : Finset E) :
    ∃ c : 𝒪[F], c ≠ 0 ∧ ∀ x ∈ s, algebraMap F E c * x ∈ L.O := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp⟩
  | insert x s _ ih =>
    obtain ⟨c, hc, h⟩ := ih
    obtain ⟨d, hd, h'⟩ := exists_mul_mem L x
    refine ⟨c * d, mul_ne_zero hc hd, fun y hy => ?_⟩
    rw [Subring.coe_mul, map_mul]
    rcases Finset.mem_insert.1 hy with rfl | hy
    · rw [mul_assoc]
      exact L.O.mul_mem ((algebraMap_mem_iff L _).2 c.2) h'
    · rw [mul_right_comm]
      exact L.O.mul_mem (h y hy) ((algebraMap_mem_iff L _).2 d.2)

/- English proof (translation)
Take `⟨s, rfl⟩` from `h`. Take `⟨c, hc, hs⟩` from `exists_mul_mem_finset L (s.biUnion fun x => Finset.univ.image fun i => x i)`. Establish `hc' : (c : F) ≠ 0` using `fun h => hc (Subtype.ext h)`. Establish `h1 : algebraMap F E (c : F)⁻¹ * algebraMap F E c = 1`. Rewrite using `[← map_mul, inv_mul_cancel₀ hc', map_one]`.

Set `f : (Fin n → L.O) →ₗ[L.O] (Fin n → E)` to `{ toFun := fun v i => algebraMap F E (c : F)⁻¹ * v i map_add' := fun v w => by ext i; simp [mul_add] map_smul' := fun a v => by`. Use extensionality with `i`. Use `show _ * ((a : E) * v i) = (a : E) * (_ * _)`. Use `ring }`. Establish `hle : Submodule.span L.O (s : Set (Fin n → E)) ≤ LinearMap.range f`.

Rewrite using `[Submodule.span_le]`. Introduce `x hx`. Use `⟨fun i => ⟨algebraMap F E c * x i, hs _ ?_⟩, ?_⟩` and prove the remaining obligations. Conclude with `Finset.mem_biUnion.2 ⟨x, hx, Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩`. Use extensionality with `i show algebraMap F E (c : F)⁻¹ * (algebraMap F E c * x i) = _`.

Rewrite using `[← mul_assoc, h1, one_mul]`. Take `⟨b, hb⟩` from `exists_eq_span_range n ((Submodule.span L.O (s : Set (Fin n → E))).comap f)`. Use `⟨fun i => f (b i), ?_⟩` and prove the remaining obligations. Rewrite using `[← Submodule.map_comap_eq_of_le hle, hb, Submodule.map_span, ← Set.range_comp]`. Both sides reduce to the same expression.
-/
theorem exists_eq_span_of_fg (L : LocE F E) [IsPrincipalIdealRing L.O] {n : ℕ}
    {Λ : Submodule L.O (Fin n → E)} (h : Λ.FG) :
    ∃ b : Fin n → Fin n → E, Λ = Submodule.span L.O (Set.range b) := by
  obtain ⟨s, rfl⟩ := h
  obtain ⟨c, hc, hs⟩ := exists_mul_mem_finset L
    (s.biUnion fun x => Finset.univ.image fun i => x i)
  have hc' : (c : F) ≠ 0 := fun h => hc (Subtype.ext h)
  have h1 : algebraMap F E (c : F)⁻¹ * algebraMap F E c = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hc', map_one]
  let f : (Fin n → L.O) →ₗ[L.O] (Fin n → E) :=
    { toFun := fun v i => algebraMap F E (c : F)⁻¹ * v i
      map_add' := fun v w => by ext i; simp [mul_add]
      map_smul' := fun a v => by
        ext i
        show _ * ((a : E) * v i) = (a : E) * (_ * _)
        ring }
  have hle : Submodule.span L.O (s : Set (Fin n → E)) ≤ LinearMap.range f := by
    rw [Submodule.span_le]
    intro x hx
    refine ⟨fun i => ⟨algebraMap F E c * x i, hs _ ?_⟩, ?_⟩
    · exact Finset.mem_biUnion.2 ⟨x, hx, Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩
    · ext i
      show algebraMap F E (c : F)⁻¹ * (algebraMap F E c * x i) = _
      rw [← mul_assoc, h1, one_mul]
  obtain ⟨b, hb⟩ := exists_eq_span_range n
    ((Submodule.span L.O (s : Set (Fin n → E))).comap f)
  refine ⟨fun i => f (b i), ?_⟩
  rw [← Submodule.map_comap_eq_of_le hle, hb, Submodule.map_span, ← Set.range_comp]
  rfl

/- English proof (translation)
Proceed by induction on `(Finset.univ : Finset ι) using Finset.induction_on with`. Consider the case `empty => simp [hf]`. Consider the case `insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, hf_add_l, hf_smul_l, ih]`.
-/
theorem hf_sum_l (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) {ι : Type*} [Fintype ι]
    (a : ι → E) (b : ι → Fin n → E) (y : Fin n → E) :
    hf L Hm (∑ k, a k • b k) y = ∑ k, a k * hf L Hm (b k) y := by
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp [hf]
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, hf_add_l, hf_smul_l, ih]

/- English proof (translation)
Proceed by induction on `(Finset.univ : Finset ι) using Finset.induction_on with`. Consider the case `empty => simp [hf]`. Consider the case `insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, hf_add_r, hf_smul_r, ih]`.
-/
theorem hf_sum_r (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) {ι : Type*} [Fintype ι]
    (a : ι → E) (b : ι → Fin n → E) (y : Fin n → E) :
    hf L Hm y (∑ k, a k • b k) = ∑ k, L.cj (a k) * hf L Hm y (b k) := by
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp [hf]
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, hf_add_r, hf_smul_r, ih]

/- English proof (translation)
Rewrite using `[← h.2, Submodule.span_span_of_tower]`.
-/
theorem span_range_eq_top (L : LocE F E) {n : ℕ} {ι : Type*} {b : ι → Fin n → E}
    (h : IsLat L (Submodule.span L.O (Set.range b))) : Submodule.span E (Set.range b) = ⊤ := by
  rw [← h.2, Submodule.span_span_of_tower]

/- English proof (translation)
Establish `h1 : ∀ i, ∃ a : Fin n → E, ∑ k, a k • b k = Pi.single i 1` using `fun i => (Submodule.mem_span_range_iff_exists_fun E).1 (hb ▸ Submodule.mem_top)`. Use `choose C hC using h1`. Establish `h2 : Matrix.of C * Matrix.of b = 1`. Use extensionality with `i j`. Use `congrFun (hC i) j` as an intermediate fact.

Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this`. Rewrite using `[Matrix.mul_apply, Matrix.one_apply]`. Simplify using `only [Matrix.of_apply, this, Pi.single_apply, eq_comm]`. Establish `h3 : Matrix.of b * Hm * (Hm⁻¹ * Matrix.of C) = 1`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hH, mul_eq_one_comm.1 h2]`.

Use `⟨fun j k => L.cj ((Hm⁻¹ * Matrix.of C) k j), fun i j => ?_⟩` and prove the remaining obligations. Rewrite using `[← Matrix.one_apply, ← h3, Matrix.mul_apply]`. Simplify using `only [hf, L.cj_cj]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[Matrix.mul_apply (M := Matrix.of b), Finset.sum_mul]`. Both sides reduce to the same expression.
-/
theorem exists_dual (L : LocE F E) {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E} (hH : IsUnit Hm.det)
    {b : Fin n → Fin n → E} (hb : Submodule.span E (Set.range b) = ⊤) :
    ∃ y : Fin n → Fin n → E, ∀ i j, hf L Hm (b i) (y j) = if i = j then 1 else 0 := by
  have h1 : ∀ i, ∃ a : Fin n → E, ∑ k, a k • b k = Pi.single i 1 := fun i =>
    (Submodule.mem_span_range_iff_exists_fun E).1 (hb ▸ Submodule.mem_top)
  choose C hC using h1
  have h2 : Matrix.of C * Matrix.of b = 1 := by
    ext i j
    have := congrFun (hC i) j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.of_apply, this, Pi.single_apply, eq_comm]
  have h3 : Matrix.of b * Hm * (Hm⁻¹ * Matrix.of C) = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hH, mul_eq_one_comm.1 h2]
  refine ⟨fun j k => L.cj ((Hm⁻¹ * Matrix.of C) k j), fun i j => ?_⟩
  rw [← Matrix.one_apply, ← h3, Matrix.mul_apply]
  simp only [hf, L.cj_cj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_apply (M := Matrix.of b), Finset.sum_mul]
  rfl

/- English proof (translation)
Take `⟨a, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun E).1 (hb ▸ Submodule.mem_top : x ∈ Submodule.span E (Set.range b))`. Simplify using `[hf_sum_l, ho]`.
-/
theorem sum_hf_smul (L : LocE F E) {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E}
    {b : Fin n → Fin n → E} (hb : Submodule.span E (Set.range b) = ⊤)
    (ho : ∀ i j, hf L Hm (b i) (b j) = if i = j then 1 else 0) (x : Fin n → E) :
    ∑ i, hf L Hm x (b i) • b i = x := by
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1
    (hb ▸ Submodule.mem_top : x ∈ Submodule.span E (Set.range b))
  simp [hf_sum_l, ho]

noncomputable def transfer (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (b b' : Fin n → Fin n → E) : (Fin n → E) →ₗ[E] (Fin n → E) where
  toFun x := ∑ i, hf L Hm x (b i) • b' i
  map_add' x y := by simp [hf_add_l, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [hf_smul_l, Finset.smul_sum, mul_smul]

/- English proof (translation)
Establish `key : ∀ {b b' : Fin n → Fin n → E}, Submodule.span E (Set.range b) = ⊤ → (∀ i j, hf L Hm (b i) (b j) = if i = j then 1 else 0) → (∀ i j, hf L Hm (b' i) (b' j) = if i = j then 1 else 0) → (transfer L Hm b' b).comp (transfer L Hm b b') = LinearMap.id`. Introduce `b b' hb ho ho'`. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Use `show ∑ j, hf L Hm (∑ i, hf L Hm x (b i) • b' i) (b' j) • b j = x`. Simplify using `[hf_sum_l, ho', sum_hf_smul L hb ho]`.

Use `⟨LinearEquiv.ofLinear (transfer L Hm b b') (transfer L Hm b' b) (key hb' ho' ho) (key hb ho ho'), fun x y => ?_, fun i => ?_⟩` and prove the remaining obligations. Use `show hf L Hm (∑ i, hf L Hm x (b i) • b' i) (∑ i, hf L Hm y (b i) • b' i) = _ conv_rhs => rw [← sum_hf_smul L hb ho x, ← sum_hf_smul L hb ho y]`. Simplify using `only [hf_sum_l L Hm (fun i => hf L Hm x (b i)), hf_sum_r L Hm (fun i => hf L Hm y (b i)), ho, ho']`. Use `show ∑ j, hf L Hm (b i) (b j) • b' j = _`. Simplify using `[ho]`.
-/
theorem exists_isom (L : LocE F E) {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E}
    {b b' : Fin n → Fin n → E} (hb : Submodule.span E (Set.range b) = ⊤)
    (hb' : Submodule.span E (Set.range b') = ⊤)
    (ho : ∀ i j, hf L Hm (b i) (b j) = if i = j then 1 else 0)
    (ho' : ∀ i j, hf L Hm (b' i) (b' j) = if i = j then 1 else 0) :
    ∃ g ∈ isomG L Hm, ∀ i, g (b i) = b' i := by
  have key : ∀ {b b' : Fin n → Fin n → E}, Submodule.span E (Set.range b) = ⊤ →
      (∀ i j, hf L Hm (b i) (b j) = if i = j then 1 else 0) →
      (∀ i j, hf L Hm (b' i) (b' j) = if i = j then 1 else 0) →
      (transfer L Hm b' b).comp (transfer L Hm b b') = LinearMap.id := by
    intro b b' hb ho ho'
    refine LinearMap.ext fun x => ?_
    show ∑ j, hf L Hm (∑ i, hf L Hm x (b i) • b' i) (b' j) • b j = x
    simp [hf_sum_l, ho', sum_hf_smul L hb ho]
  refine ⟨LinearEquiv.ofLinear (transfer L Hm b b') (transfer L Hm b' b) (key hb' ho' ho)
    (key hb ho ho'), fun x y => ?_, fun i => ?_⟩
  · show hf L Hm (∑ i, hf L Hm x (b i) • b' i) (∑ i, hf L Hm y (b i) • b' i) = _
    conv_rhs => rw [← sum_hf_smul L hb ho x, ← sum_hf_smul L hb ho y]
    simp only [hf_sum_l L Hm (fun i => hf L Hm x (b i)), hf_sum_r L Hm (fun i => hf L Hm y (b i)),
      ho, ho']
  · show ∑ j, hf L Hm (b i) (b j) • b' j = _
    simp [ho]

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible 𝒪[F]`. Take `⟨htr, -, -, hpir, -, -, -, hnorm⟩` from `order_facts L ϖ hϖ`. Take `⟨b, rfl⟩` from `exists_eq_span_of_fg L hΛ.1.1`. Establish `hmem : ∀ i, b i ∈ Submodule.span L.O (Set.range b)` using `fun i => Submodule.subset_span ⟨i, rfl⟩`. Take `⟨y, hy⟩` from `exists_dual L hH.2 (span_range_eq_top L hΛ.1)`.

Establish `hsm : ∀ (a : L.O) (v : Fin n → E), a • v = (a : E) • v` using `fun _ _ => rfl`. Establish `hy' : ∀ j, ∃ a : Fin n → L.O, ∑ k, a k • b k = y j` using `fun j => by`. Use `(Submodule.mem_span_range_iff_exists_fun L.O).1 ((hΛ.2 _).1 fun x hx => ?_)` and prove the remaining obligations. Take `⟨a, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun L.O).1 hx`. Simplify using `[hsm, hf_sum_l, hy]`.

Use `choose A hA using hy'`. Set `c : L.O →+* L.O` to `(L.cj : E →+* E).restrict L.O L.O fun x hx => cj_mem L hx`. Establish `hcv : ∀ x : L.O, ((c x : L.O) : E) = L.cj x` using `fun _ => rfl`. Establish `hc : ∀ x, c (c x) = x` using `fun x => Subtype.ext (L.cj_cj x)`. Set `G : Matrix (Fin n) (Fin n) L.O` to `fun i j => ⟨hf L Hm (b i) (b j), (hΛ.2 _).2 (hmem j) _ (hmem i)⟩`.

Establish `hGv : ∀ i j, (G i j : E) = hf L Hm (b i) (b j)` using `fun _ _ => rfl`. Establish `hG : ∀ i j, c (G i j) = G j i` using `fun i j => Subtype.ext (hf_cj L hH.1 _ _)`. Establish `hGA : G * (Matrix.of fun k j => c (A j k)) = 1`. Use extensionality with `i j`. Establish `h` using `hy i j`.

Rewrite `h` using `[← hA j]`. Simplify using `only [hsm, hf_sum_r] at h`. Rewrite using `[Matrix.mul_apply, Matrix.one_apply, apply_ite Subtype.val, OneMemClass.coe_one, ZeroMemClass.coe_zero, ← h, AddSubmonoidClass.coe_finset_sum]`. Conclude with `Finset.sum_congr rfl fun k _ => mul_comm _ _`. Establish `hint : ∀ a : 𝒪[F], algebraMap F E a ∈ L.O` using `fun a => (algebraMap_mem_iff L a).2 a.2`.

Set `i : 𝒪[F] →+* L.O` to `(algebraMap 𝒪[F] E).codRestrict L.O hint`. Set `: Algebra 𝒪[F] L.O` to `i.toAlgebra`. Establish `hfix : ∀ x, c x = x → x ∈ (algebraMap 𝒪[F] L.O).range` using `fun x hx => by`. Take `⟨a, ha⟩` from `exists_int_of_fixed L x.2 (congrArg Subtype.val hx)`. Conclude with `⟨a, Subtype.ext ha.symm⟩`.

Establish `hinj : Function.Injective (algebraMap 𝒪[F] L.O)` using `fun a b h => Subtype.ext (algebraMap_inj L (congrArg Subtype.val h))`. Take `⟨P, hP, hGP⟩` from `GlobalTheory.UnramifiedHermitian.exists_eq_transpose_mul_map (R₀ := 𝒪[F]) c hc hfix (by`. Take `⟨w, hw, h⟩` from `htr 1`. Conclude with `⟨⟨w, hw⟩, Subtype.ext (by simpa [hcv] using h)⟩)`. Use the proof step `(fun u hu hu' => by`.

Take `⟨v, hv⟩` from `hu'.exists_right_inv`. Establish `hv'` using `congrArg c hv`. Rewrite `hv'` using `[map_mul, hu, map_one]`. Take `⟨s, rfl⟩` from `hfix v (by linear_combination v * hv' - c v * hv)`. Take `⟨r, rfl⟩` from `hfix u hu`.

Establish `hr : IsUnit r` using `IsUnit.of_mul_eq_one s (hinj (by rw [map_mul, hv, map_one]))`. Take `⟨x, hx, h⟩` from `hnorm hr.unit`. Conclude with `⟨⟨x, hx⟩, Subtype.ext h⟩)`. Use `hG (Matrix.isUnit_det_of_right_inverse hGA)`. Establish `hQ : (P⁻¹)ᵀ * G * (P⁻¹).map c = 1`.

Rewrite using `[hGP, ← Matrix.mul_assoc, ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hP, Matrix.transpose_one, Matrix.one_mul, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hP, Matrix.map_one _ (map_zero c) (map_one c)]`. Use `⟨fun i => ∑ k, P⁻¹ k i • b k, fun i j => ?_, le_antisymm ?_ ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg Subtype.val (congrFun (congrFun hQ i) j)`. Rewrite `h` using `[Matrix.one_apply, apply_ite Subtype.val, OneMemClass.coe_one, ZeroMemClass.coe_zero]`. Rewrite using `[← h]`.

Simplify using `only [hsm, hf_sum_l, hf_sum_r, Matrix.mul_apply, AddSubmonoidClass.coe_finset_sum, Subring.coe_mul, Matrix.transpose_apply, Matrix.map_apply, hcv, hGv]`. Conclude with `Finset.sum_congr rfl fun k _ => mul_comm _ _`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨k, rfl⟩`. Use `(Submodule.mem_span_range_iff_exists_fun L.O).2 ⟨fun i => P i k, ?_⟩` and prove the remaining obligations.

Simplify using `only [Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm]`. Establish `h : ∀ l, ∑ i, P i k * P⁻¹ l i = if l = k then 1 else 0` using `fun l => by`. Rewrite using `[← Matrix.one_apply, ← Matrix.nonsing_inv_mul _ hP, Matrix.mul_apply]`. Conclude with `Finset.sum_congr rfl fun i _ => mul_comm _ _`.

Simplify using `[← Finset.sum_smul, h]`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨k, rfl⟩`. Conclude with `Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (hmem l)`.
-/
theorem exists_orthonormal [IsNonarchimedeanLocalField F] [CharZero F] (L : LocE F E) {n : ℕ}
    {Hm : Matrix (Fin n) (Fin n) E} (hH : IsHermND L Hm) {Λ : Submodule L.O (Fin n → E)}
    (hΛ : IsSD L Hm Λ) : ∃ b : Fin n → Fin n → E,
      (∀ i j, hf L Hm (b i) (b j) = if i = j then 1 else 0) ∧
      Λ = Submodule.span L.O (Set.range b) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨htr, -, -, hpir, -, -, -, hnorm⟩ := order_facts L ϖ hϖ
  obtain ⟨b, rfl⟩ := exists_eq_span_of_fg L hΛ.1.1
  have hmem : ∀ i, b i ∈ Submodule.span L.O (Set.range b) := fun i =>
    Submodule.subset_span ⟨i, rfl⟩
  obtain ⟨y, hy⟩ := exists_dual L hH.2 (span_range_eq_top L hΛ.1)
  have hsm : ∀ (a : L.O) (v : Fin n → E), a • v = (a : E) • v := fun _ _ => rfl
  have hy' : ∀ j, ∃ a : Fin n → L.O, ∑ k, a k • b k = y j := fun j => by
    refine (Submodule.mem_span_range_iff_exists_fun L.O).1 ((hΛ.2 _).1 fun x hx => ?_)
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun L.O).1 hx
    simp [hsm, hf_sum_l, hy]
  choose A hA using hy'
  let c : L.O →+* L.O := (L.cj : E →+* E).restrict L.O L.O fun x hx => cj_mem L hx
  have hcv : ∀ x : L.O, ((c x : L.O) : E) = L.cj x := fun _ => rfl
  have hc : ∀ x, c (c x) = x := fun x => Subtype.ext (L.cj_cj x)
  let G : Matrix (Fin n) (Fin n) L.O :=
    fun i j => ⟨hf L Hm (b i) (b j), (hΛ.2 _).2 (hmem j) _ (hmem i)⟩
  have hGv : ∀ i j, (G i j : E) = hf L Hm (b i) (b j) := fun _ _ => rfl
  have hG : ∀ i j, c (G i j) = G j i := fun i j => Subtype.ext (hf_cj L hH.1 _ _)
  have hGA : G * (Matrix.of fun k j => c (A j k)) = 1 := by
    ext i j
    have h := hy i j
    rw [← hA j] at h
    simp only [hsm, hf_sum_r] at h
    rw [Matrix.mul_apply, Matrix.one_apply, apply_ite Subtype.val, OneMemClass.coe_one,
      ZeroMemClass.coe_zero, ← h, AddSubmonoidClass.coe_finset_sum]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hint : ∀ a : 𝒪[F], algebraMap F E a ∈ L.O := fun a => (algebraMap_mem_iff L a).2 a.2
  let i : 𝒪[F] →+* L.O := (algebraMap 𝒪[F] E).codRestrict L.O hint
  let : Algebra 𝒪[F] L.O := i.toAlgebra
  have hfix : ∀ x, c x = x → x ∈ (algebraMap 𝒪[F] L.O).range := fun x hx => by
    obtain ⟨a, ha⟩ := exists_int_of_fixed L x.2 (congrArg Subtype.val hx)
    exact ⟨a, Subtype.ext ha.symm⟩
  have hinj : Function.Injective (algebraMap 𝒪[F] L.O) := fun a b h =>
    Subtype.ext (algebraMap_inj L (congrArg Subtype.val h))
  obtain ⟨P, hP, hGP⟩ := GlobalTheory.UnramifiedHermitian.exists_eq_transpose_mul_map (R₀ := 𝒪[F]) c hc hfix
    (by
      obtain ⟨w, hw, h⟩ := htr 1
      exact ⟨⟨w, hw⟩, Subtype.ext (by simpa [hcv] using h)⟩)
    (fun u hu hu' => by
      obtain ⟨v, hv⟩ := hu'.exists_right_inv
      have hv' := congrArg c hv
      rw [map_mul, hu, map_one] at hv'
      obtain ⟨s, rfl⟩ := hfix v (by linear_combination v * hv' - c v * hv)
      obtain ⟨r, rfl⟩ := hfix u hu
      have hr : IsUnit r := IsUnit.of_mul_eq_one s (hinj (by rw [map_mul, hv, map_one]))
      obtain ⟨x, hx, h⟩ := hnorm hr.unit
      exact ⟨⟨x, hx⟩, Subtype.ext h⟩)
    hG (Matrix.isUnit_det_of_right_inverse hGA)
  have hQ : (P⁻¹)ᵀ * G * (P⁻¹).map c = 1 := by
    rw [hGP, ← Matrix.mul_assoc, ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hP,
      Matrix.transpose_one, Matrix.one_mul, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hP,
      Matrix.map_one _ (map_zero c) (map_one c)]
  refine ⟨fun i => ∑ k, P⁻¹ k i • b k, fun i j => ?_, le_antisymm ?_ ?_⟩
  · have h := congrArg Subtype.val (congrFun (congrFun hQ i) j)
    rw [Matrix.one_apply, apply_ite Subtype.val, OneMemClass.coe_one, ZeroMemClass.coe_zero] at h
    rw [← h]
    simp only [hsm, hf_sum_l, hf_sum_r, Matrix.mul_apply, AddSubmonoidClass.coe_finset_sum,
      Subring.coe_mul, Matrix.transpose_apply, Matrix.map_apply, hcv, hGv]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    refine (Submodule.mem_span_range_iff_exists_fun L.O).2 ⟨fun i => P i k, ?_⟩
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    have h : ∀ l, ∑ i, P i k * P⁻¹ l i = if l = k then 1 else 0 := fun l => by
      rw [← Matrix.one_apply, ← Matrix.nonsing_inv_mul _ hP, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    simp [← Finset.sum_smul, h]
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (hmem l)

end GlobalTheory.HL.SelfDual

/- English proof (translation)
Introduce `F _ _ _ _ _ E _ _ _ L n Hm hH`. Use `⟨fun Λ hΛ => exists_orthonormal L hH hΛ, fun Λ Λ' hΛ hΛ' => ?_⟩` and prove the remaining obligations. Take `⟨b, ho, rfl⟩` from `exists_orthonormal L hH hΛ`. Take `⟨b', ho', rfl⟩` from `exists_orthonormal L hH hΛ'`. Take `⟨g, hg, h⟩` from `exists_isom L (span_range_eq_top L hΛ.1) (span_range_eq_top L hΛ'.1) ho ho'`.

Use `⟨g, hg, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.smul_span, Set.smul_set_range]`. Simplify using `only [LinearEquiv.smul_def, h]`.
-/
theorem GlobalTheory.HL.SelfDual.orthonormal_basis_and_one_orbit : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → (∀ Λ, IsSD L Hm Λ → ∃ b : Fin n → Fin n → E, (∀ i j, hf L Hm (b i) (b j) = if i = j then 1 else 0) ∧ Λ = Submodule.span L.O (Set.range b)) ∧ ∀ Λ Λ', IsSD L Hm Λ → IsSD L Hm Λ' → ∃ g ∈ isomG L Hm, g • Λ = Λ' := by
  intro F _ _ _ _ _ E _ _ _ L n Hm hH
  refine ⟨fun Λ hΛ => exists_orthonormal L hH hΛ, fun Λ Λ' hΛ hΛ' => ?_⟩
  obtain ⟨b, ho, rfl⟩ := exists_orthonormal L hH hΛ
  obtain ⟨b', ho', rfl⟩ := exists_orthonormal L hH hΛ'
  obtain ⟨g, hg, h⟩ := exists_isom L (span_range_eq_top L hΛ.1) (span_range_eq_top L hΛ'.1) ho ho'
  refine ⟨g, hg, ?_⟩
  rw [Submodule.smul_span, Set.smul_set_range]
  simp only [LinearEquiv.smul_def, h]
