import Development.EtaleCohomology.EtaleSheaves.LeafModelCurveCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

namespace LateralTheory.E.LeafNormalModelPf

def intCl (Ω : Type) {L : Type} [Field Ω] [Field L] [Algebra Ω L] (u : L) : Subalgebra Ω L :=
  (integralClosure (Algebra.adjoin Ω {u}) L).restrictScalars Ω

/- English proof (translation)
Introduce `x hx`. Set `V' : Subalgebra Ω L` to `{ V.toSubring with algebraMap_mem' := hΩ }`. Establish `hle : Algebra.adjoin Ω {u} ≤ V'` using `Algebra.adjoin_le (Set.singleton_subset_iff.2 hu)`. Take `⟨p, hp, hpx⟩` from `(hx : IsIntegral (Algebra.adjoin Ω {u}) x)`. Set `f : Algebra.adjoin Ω {u} →+* V` to `{ toFun := fun y => ⟨y.1, hle y.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl, map_add' := fun _ _ => rfl }`.

Establish `hint : IsIntegral V x` using `⟨p.map f, hp.map f, by rw [Polynomial.eval₂_map]; exact hpx⟩`. Take `⟨y, rfl⟩` from `(IsIntegrallyClosed.isIntegral_iff (R := V) (K := L)).1 hint`. Conclude with `y.2`.
-/
theorem intCl_subset {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] {u : L} (V : ValuationSubring L)
    (hΩ : ∀ a : Ω, algebraMap Ω L a ∈ V) (hu : u ∈ V) : (intCl Ω u : Set L) ⊆ V := by
  intro x hx
  let V' : Subalgebra Ω L := { V.toSubring with algebraMap_mem' := hΩ }
  have hle : Algebra.adjoin Ω {u} ≤ V' := Algebra.adjoin_le (Set.singleton_subset_iff.2 hu)
  obtain ⟨p, hp, hpx⟩ := (hx : IsIntegral (Algebra.adjoin Ω {u}) x)
  let f : Algebra.adjoin Ω {u} →+* V :=
    { toFun := fun y => ⟨y.1, hle y.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
      map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hint : IsIntegral V x := ⟨p.map f, hp.map f, by rw [Polynomial.eval₂_map]; exact hpx⟩
  obtain ⟨y, rfl⟩ := (IsIntegrallyClosed.isIntegral_iff (R := V) (K := L)).1 hint
  exact y.2

/- English proof (translation)
Break down `V.mem_or_inv_mem u with h | h` into its components or cases. Conclude with `Or.inl (intCl_subset V hΩ h)`. Conclude with `Or.inr (intCl_subset V hΩ h)`.
-/
theorem valuation_covers {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (u : L) (V : ValuationSubring L)
    (hΩ : ∀ a : Ω, algebraMap Ω L a ∈ V) : (intCl Ω u : Set L) ⊆ V ∨ (intCl Ω u⁻¹ : Set L) ⊆ V := by
  rcases V.mem_or_inv_mem u with h | h
  · exact Or.inl (intCl_subset V hΩ h)
  · exact Or.inr (intCl_subset V hΩ h)

/- English proof (translation)
Introduce `h`. Apply `hu` to reduce the goal to its premises. Simplify using `using h.inv`.
-/
theorem transcendental_inv {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] {u : L}
    (hu : Transcendental Ω u) : Transcendental Ω u⁻¹ := by
  intro h
  apply hu
  simpa using h.inv

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[IntermediateField.adjoin_simple_le_iff]`. Conclude with `inv_mem (IntermediateField.mem_adjoin_simple_self Ω u)`. Rewrite using `[IntermediateField.adjoin_simple_le_iff]`. Simplify using `using inv_mem (IntermediateField.mem_adjoin_simple_self Ω u⁻¹)`.
-/
theorem adjoin_inv_eq {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (u : L) :
    IntermediateField.adjoin Ω {u⁻¹} = IntermediateField.adjoin Ω {u} := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact inv_mem (IntermediateField.mem_adjoin_simple_self Ω u)
  · rw [IntermediateField.adjoin_simple_le_iff]
    simpa using inv_mem (IntermediateField.mem_adjoin_simple_self Ω u⁻¹)

/- English proof (translation)
Introduce and unpack `rfl`. Conclude with `hu isAlgebraic_zero`.
-/
theorem ne_zero_of_transcendental {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] {u : L}
    (hu : Transcendental Ω u) : u ≠ 0 := by
  rintro rfl
  exact hu isAlgebraic_zero

/- English proof (translation)
The claim follows from `isIntegral_algebraMap (x := (⟨u, Algebra.subset_adjoin (Set.mem_singleton u)⟩ : Algebra.adjoin Ω {u}))`.
-/
theorem self_mem_intCl {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (u : L) : u ∈ intCl Ω u :=
  isIntegral_algebraMap (x := (⟨u, Algebra.subset_adjoin (Set.mem_singleton u)⟩ : Algebra.adjoin Ω {u}))

def LeafIntClosureAlg : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (u : L),
  Transcendental Ω u → FiniteDimensional (IntermediateField.adjoin Ω {u}) L →
    Algebra.FiniteType Ω (intCl Ω u) ∧ IsIntegrallyClosed (intCl Ω u) ∧ ringKrullDim (intCl Ω u) = 1 ∧
      IsFractionRing (intCl Ω u) L

def LeafIntClosureLoc : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (u : L),
  Transcendental Ω u → FiniteDimensional (IntermediateField.adjoin Ω {u}) L →
    Algebra.adjoin Ω ((intCl Ω u : Set L) ∪ {u⁻¹}) = Algebra.adjoin Ω ((intCl Ω u⁻¹ : Set L) ∪ {u})

def LeafGlueProper : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (A B : Subalgebra Ω L) (u : L),
  u ≠ 0 → u ∈ A → u⁻¹ ∈ B → Algebra.FiniteType Ω A → Algebra.FiniteType Ω B →
  IsIntegrallyClosed A → IsIntegrallyClosed B → ringKrullDim A = 1 → ringKrullDim B = 1 →
  IsFractionRing A L → IsFractionRing B L →
  Algebra.adjoin Ω ((A : Set L) ∪ {u⁻¹}) = Algebra.adjoin Ω ((B : Set L) ∪ {u}) →
  (∀ V : ValuationSubring L, (∀ a : Ω, algebraMap Ω L a ∈ V) → (A : Set L) ⊆ V ∨ (B : Set L) ⊆ V) →
    ∃ (C0 : Scheme.{0}) (c0 : C0 ⟶ Sp Ω) (x : C0) (ψ : Spec (C0.presheaf.stalk x) ⟶ Sp L),
      IsIntegral C0 ∧ IsProper c0 ∧ (∀ y : C0, IsIntegrallyClosed (C0.presheaf.stalk y)) ∧
      topologicalKrullDim C0 = 1 ∧ IsGenericPoint x (⊤ : Set C0) ∧
      ψ ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω L)) = C0.fromSpecStalk x ≫ c0

/- English proof (translation)
Rewrite using `[Algebra.adjoin_le_iff]`. Introduce and unpack `x (hx | hx)`. Take `⟨n, hn⟩` from `h x hx`. Establish `: x = x * u⁻¹ ^ n * u ^ n`. Rewrite using `[mul_assoc, ← mul_pow, inv_mul_cancel₀ hu, one_pow, mul_one]`.

Rewrite using `[this]`. Establish `h1 : x * u⁻¹ ^ n ∈ Algebra.adjoin Ω ((intCl Ω u⁻¹ : Set L) ∪ {u})` using `Algebra.subset_adjoin (Set.mem_union_left _ hn)`. Establish `h2 : u ∈ Algebra.adjoin Ω ((intCl Ω u⁻¹ : Set L) ∪ {u})` using `Algebra.subset_adjoin (Set.mem_union_right _ rfl)`. Conclude with `mul_mem h1 (pow_mem h2 n)`. Rewrite using `[Set.mem_singleton_iff.1 hx]`.

Conclude with `Algebra.subset_adjoin (Set.mem_union_left _ (self_mem_intCl u⁻¹))`.
-/
theorem adjoin_le_of_shift {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] {u : L} (hu : u ≠ 0)
    (h : ∀ x ∈ intCl Ω u, ∃ n : ℕ, x * u⁻¹ ^ n ∈ intCl Ω u⁻¹) :
    Algebra.adjoin Ω ((intCl Ω u : Set L) ∪ {u⁻¹}) ≤ Algebra.adjoin Ω ((intCl Ω u⁻¹ : Set L) ∪ {u}) := by
  rw [Algebra.adjoin_le_iff]
  rintro x (hx | hx)
  · obtain ⟨n, hn⟩ := h x hx
    have : x = x * u⁻¹ ^ n * u ^ n := by
      rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ hu, one_pow, mul_one]
    rw [this]
    have h1 : x * u⁻¹ ^ n ∈ Algebra.adjoin Ω ((intCl Ω u⁻¹ : Set L) ∪ {u}) :=
      Algebra.subset_adjoin (Set.mem_union_left _ hn)
    have h2 : u ∈ Algebra.adjoin Ω ((intCl Ω u⁻¹ : Set L) ∪ {u}) :=
      Algebra.subset_adjoin (Set.mem_union_right _ rfl)
    exact mul_mem h1 (pow_mem h2 n)
  · rw [Set.mem_singleton_iff.1 hx]
    exact Algebra.subset_adjoin (Set.mem_union_left _ (self_mem_intCl u⁻¹))

def LeafIntShift : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (u : L), u ≠ 0 →
  ∀ x ∈ intCl Ω u, ∃ n : ℕ, x * u⁻¹ ^ n ∈ intCl Ω u⁻¹

/- English proof (translation)
Introduce `Ω L _ _ _ u hu _`. Establish `hu0` using `ne_zero_of_transcendental hu`. Apply `le_antisymm (adjoin_le_of_shift hu0 (h Ω L u hu0))` to reduce the goal to its premises. Establish `h'` using `adjoin_le_of_shift (inv_ne_zero hu0) (by simpa using h Ω L u⁻¹ (inv_ne_zero hu0))`. Simplify using `using h'`.
-/
theorem LeafIntClosureLoc_of (h : LeafIntShift) : LeafIntClosureLoc := by
  intro Ω L _ _ _ u hu _
  have hu0 := ne_zero_of_transcendental hu
  apply le_antisymm (adjoin_le_of_shift hu0 (h Ω L u hu0))
  have h' := adjoin_le_of_shift (inv_ne_zero hu0) (by simpa using h Ω L u⁻¹ (inv_ne_zero hu0))
  simpa using h'

/- English proof (translation)
Establish `hinv : u⁻¹ ∈ Algebra.adjoin Ω {u⁻¹}` using `Algebra.subset_adjoin (Set.mem_singleton _)`. Proceed by induction on `hc using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Rewrite using `[Set.mem_singleton_iff.1 hx]`. Use `⟨1, fun m hm => ?_⟩` and prove the remaining obligations.

Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le hm`. Rewrite using `[pow_add, pow_one, ← mul_assoc, mul_inv_cancel₀ hu, one_mul]`. Conclude with `pow_mem hinv k`. Consider the case `algebraMap a`. Conclude with `⟨0, fun m _ => mul_mem (Subalgebra.algebraMap_mem _ a) (pow_mem hinv m)⟩`.

Consider the case `add x y _ _ ihx ihy`. Take `⟨N1, h1⟩` from `ihx`. Take `⟨N2, h2⟩` from `ihy`. Use `⟨max N1 N2, fun m hm => ?_⟩` and prove the remaining obligations. Rewrite using `[add_mul]`.

Conclude with `add_mem (h1 m (le_trans (le_max_left _ _) hm)) (h2 m (le_trans (le_max_right _ _) hm))`. Consider the case `mul x y _ _ ihx ihy`. Take `⟨N1, h1⟩` from `ihx`. Take `⟨N2, h2⟩` from `ihy`. Use `⟨N1 + N2, fun m hm => ?_⟩` and prove the remaining obligations.

Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le hm`. Establish `: x * y * u⁻¹ ^ (N1 + N2 + k) = (x * u⁻¹ ^ N1) * (y * u⁻¹ ^ (N2 + k))` using `by ring`. Rewrite using `[this]`. Conclude with `mul_mem (h1 N1 le_rfl) (h2 _ (Nat.le_add_right _ _))`.
-/
theorem shift_mem {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] {u : L} (hu : u ≠ 0) (c : L)
    (hc : c ∈ Algebra.adjoin Ω {u}) : ∃ N : ℕ, ∀ m, N ≤ m → c * u⁻¹ ^ m ∈ Algebra.adjoin Ω {u⁻¹} := by
  have hinv : u⁻¹ ∈ Algebra.adjoin Ω {u⁻¹} := Algebra.subset_adjoin (Set.mem_singleton _)
  induction hc using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff.1 hx]
    refine ⟨1, fun m hm => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    rw [pow_add, pow_one, ← mul_assoc, mul_inv_cancel₀ hu, one_mul]
    exact pow_mem hinv k
  | algebraMap a =>
    exact ⟨0, fun m _ => mul_mem (Subalgebra.algebraMap_mem _ a) (pow_mem hinv m)⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨N1, h1⟩ := ihx
    obtain ⟨N2, h2⟩ := ihy
    refine ⟨max N1 N2, fun m hm => ?_⟩
    rw [add_mul]
    exact add_mem (h1 m (le_trans (le_max_left _ _) hm)) (h2 m (le_trans (le_max_right _ _) hm))
  | mul x y _ _ ihx ihy =>
    obtain ⟨N1, h1⟩ := ihx
    obtain ⟨N2, h2⟩ := ihy
    refine ⟨N1 + N2, fun m hm => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    have : x * y * u⁻¹ ^ (N1 + N2 + k) = (x * u⁻¹ ^ N1) * (y * u⁻¹ ^ (N2 + k)) := by ring
    rw [this]
    exact mul_mem (h1 N1 le_rfl) (h2 _ (Nat.le_add_right _ _))

/- English proof (translation)
Introduce `Ω L _ _ _ u hu x hx`. Take `⟨p, hpm, hpx⟩` from `(hx : IsIntegral (Algebra.adjoin Ω {u}) x)`. Establish `hN : ∀ c : Algebra.adjoin Ω {u}, ∃ N : ℕ, ∀ m, N ≤ m → (c : L) * u⁻¹ ^ m ∈ Algebra.adjoin Ω {u⁻¹}` using `fun c => shift_mem hu c c.2`. Use `choose Nf hNf using hN`. Use `set p' := p.map (algebraMap (Algebra.adjoin Ω {u}) L) with hp'`.

Establish `hpm' : p'.Monic` using `hpm.map _`. Establish `hdeg : p'.natDegree = p.natDegree` using `hpm.natDegree_map _`. Use `set N := (Finset.range (p.natDegree + 1)).sup (fun i => Nf (p.coeff i)) with hNdef`. Use `set r : L := u⁻¹ ^ N`. Use `⟨N, ?_⟩` and prove the remaining obligations.

Use `show IsIntegral (Algebra.adjoin Ω {u⁻¹}) (x * u⁻¹ ^ N)`. Establish `hroot : (p'.scaleRoots r).eval (r * x) = 0`. Establish `h0 : p'.eval₂ (RingHom.id L) x = 0`. Rewrite using `[hp', Polynomial.eval₂_map]`. Conclude with `hpx`.

Establish `h` using `Polynomial.scaleRoots_eval₂_mul (p := p') (RingHom.id L) x r`. Rewrite `h` using `[h0, mul_zero]`. Conclude with `h`. Establish `hmon : (p'.scaleRoots r).Monic` using `(Polynomial.monic_scaleRoots_iff r).2 hpm'`. Establish `hlift : p'.scaleRoots r ∈ Polynomial.lifts (algebraMap (Algebra.adjoin Ω {u⁻¹}) L)`.

Rewrite using `[Polynomial.lifts_iff_coeff_lifts]`. Introduce `i`. Rewrite using `[Polynomial.coeff_scaleRoots, hp', Polynomial.coeff_map]`. Break down `lt_or_ge i p.natDegree with hi | hi` into its components or cases. Establish `hle : Nf (p.coeff i) ≤ N * (p'.natDegree - i)`.

Establish `h1 : Nf (p.coeff i) ≤ N` using `Finset.le_sup (f := fun i => Nf (p.coeff i)) (Finset.mem_range.2 (by omega))`. Establish `h2 : 1 ≤ p'.natDegree - i` using `by omega`. Use the polynomial consequences of the given equalities and inequalities. Use `hNf (p.coeff i) _ hle` as an intermediate fact. Rewrite `*` using `[← pow_mul]`.

Conclude with `⟨⟨_, this⟩, rfl⟩`. Establish `he : p'.natDegree - i = 0` using `by omega`. Rewrite using `[he, pow_zero, mul_one]`. Break down `eq_or_lt_of_le hi with h | h` into its components or cases. Rewrite using `[← h, hpm.coeff_natDegree, map_one]`.

Conclude with `⟨1, map_one _⟩`. Rewrite using `[Polynomial.coeff_eq_zero_of_natDegree_lt h, map_zero]`. Conclude with `⟨0, map_zero _⟩`. Take `⟨q, hq, -, hqm⟩` from `Polynomial.lifts_and_natDegree_eq_and_monic hlift hmon`. Use `⟨q, hqm, ?_⟩` and prove the remaining obligations.

Rewrite using `[← Polynomial.eval_map, hq, mul_comm]`. Conclude with `hroot`.
-/
theorem integral_closure_polynomial_elem_mul_inv_pow_mem_inv_closure : LeafIntShift := by
  intro Ω L _ _ _ u hu x hx
  classical
  obtain ⟨p, hpm, hpx⟩ := (hx : IsIntegral (Algebra.adjoin Ω {u}) x)
  have hN : ∀ c : Algebra.adjoin Ω {u}, ∃ N : ℕ, ∀ m, N ≤ m → (c : L) * u⁻¹ ^ m ∈ Algebra.adjoin Ω {u⁻¹} :=
    fun c => shift_mem hu c c.2
  choose Nf hNf using hN
  set p' := p.map (algebraMap (Algebra.adjoin Ω {u}) L) with hp'
  have hpm' : p'.Monic := hpm.map _
  have hdeg : p'.natDegree = p.natDegree := hpm.natDegree_map _
  set N := (Finset.range (p.natDegree + 1)).sup (fun i => Nf (p.coeff i)) with hNdef
  set r : L := u⁻¹ ^ N
  refine ⟨N, ?_⟩
  show IsIntegral (Algebra.adjoin Ω {u⁻¹}) (x * u⁻¹ ^ N)
  have hroot : (p'.scaleRoots r).eval (r * x) = 0 := by
    have h0 : p'.eval₂ (RingHom.id L) x = 0 := by
      rw [hp', Polynomial.eval₂_map]; exact hpx
    have h := Polynomial.scaleRoots_eval₂_mul (p := p') (RingHom.id L) x r
    rw [h0, mul_zero] at h
    exact h
  have hmon : (p'.scaleRoots r).Monic := (Polynomial.monic_scaleRoots_iff r).2 hpm'
  have hlift : p'.scaleRoots r ∈ Polynomial.lifts (algebraMap (Algebra.adjoin Ω {u⁻¹}) L) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    rw [Polynomial.coeff_scaleRoots, hp', Polynomial.coeff_map]
    rcases lt_or_ge i p.natDegree with hi | hi
    · have hle : Nf (p.coeff i) ≤ N * (p'.natDegree - i) := by
        have h1 : Nf (p.coeff i) ≤ N :=
          Finset.le_sup (f := fun i => Nf (p.coeff i)) (Finset.mem_range.2 (by omega))
        have h2 : 1 ≤ p'.natDegree - i := by omega
        nlinarith
      have := hNf (p.coeff i) _ hle
      rw [← pow_mul] at *
      exact ⟨⟨_, this⟩, rfl⟩
    · have he : p'.natDegree - i = 0 := by omega
      rw [he, pow_zero, mul_one]
      rcases eq_or_lt_of_le hi with h | h
      · rw [← h, hpm.coeff_natDegree, map_one]; exact ⟨1, map_one _⟩
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt h, map_zero]; exact ⟨0, map_zero _⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hmon
  refine ⟨q, hqm, ?_⟩
  rw [← Polynomial.eval_map, hq, mul_comm]
  exact hroot

/- English proof (translation)
Introduce `Ω L _ _ _ u hu hfin`. Establish `hu'` using `transcendental_inv hu`. Establish `hfin' : FiniteDimensional (IntermediateField.adjoin Ω {u⁻¹}) L`. Rewrite using `[adjoin_inv_eq (Ω := Ω) u]`. Conclude with `hfin`.

Take `⟨a1, a2, a3, a4⟩` from `hA Ω L u hu hfin`. Take `⟨b1, b2, b3, b4⟩` from `hA Ω L u⁻¹ hu' hfin'`. Conclude with `hC Ω L (intCl Ω u) (intCl Ω u⁻¹) u (ne_zero_of_transcendental hu) (self_mem_intCl u) (self_mem_intCl u⁻¹) a1 b1 a2 b2 a3 b3 a4 b4 (LeafIntClosureLoc_of integral_closure_polynomial_elem_mul_inv_pow_mem_inv_closure Ω L u hu hfin) (fun V hΩ => valuation_covers u V hΩ)`.
-/
theorem LeafNormalModel_of (hA : LeafIntClosureAlg) (hC : LeafGlueProper) :
    LateralTheory.E.LeafModelCurveCut.ExistsNormalProperCurveModel := by
  intro Ω L _ _ _ u hu hfin
  have hu' := transcendental_inv hu
  have hfin' : FiniteDimensional (IntermediateField.adjoin Ω {u⁻¹}) L := by
    rw [adjoin_inv_eq (Ω := Ω) u]; exact hfin
  obtain ⟨a1, a2, a3, a4⟩ := hA Ω L u hu hfin
  obtain ⟨b1, b2, b3, b4⟩ := hA Ω L u⁻¹ hu' hfin'
  exact hC Ω L (intCl Ω u) (intCl Ω u⁻¹) u (ne_zero_of_transcendental hu) (self_mem_intCl u)
    (self_mem_intCl u⁻¹) a1 b1 a2 b2 a3 b3 a4 b4
    (LeafIntClosureLoc_of integral_closure_polynomial_elem_mul_inv_pow_mem_inv_closure Ω L u hu hfin) (fun V hΩ => valuation_covers u V hΩ)

end LateralTheory.E.LeafNormalModelPf
