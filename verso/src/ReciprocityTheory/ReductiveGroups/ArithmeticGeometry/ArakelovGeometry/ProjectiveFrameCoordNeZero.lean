import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsBisFurther

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Polynomial Module

variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} {D : ℕ}

/- English proof (translation)
Unfold `fnField`. Rewrite using `[IntermediateField.adjoin_le_iff]`. Introduce and unpack `t ⟨i, j, rfl⟩`. Conclude with `IntermediateField.subset_adjoin _ _ ⟨e i, e j, rfl⟩`.
-/
theorem fnField_comp_le' (x : κ → Ω) (e : Fin (D + 1) → κ) : fnField (x ∘ e) ≤ fnField x := by
  unfold fnField
  rw [IntermediateField.adjoin_le_iff]
  rintro t ⟨i, j, rfl⟩
  exact IntermediateField.subset_adjoin _ _ ⟨e i, e j, rfl⟩

/- English proof (translation)
Introduce `hk`. Establish `: (MvPolynomial.X k : MvPolynomial ι o) ∈ coordIdeal o y`. Simplify using `[coordIdeal, coneMap, RingHom.mem_ker, hk]`. Rewrite `this` using `[h, Ideal.mem_bot]`. Conclude with `MvPolynomial.X_ne_zero k this`.
-/
theorem coord_ne_zero {o : Type*} [CommRing o] [Algebra o Ω] [Nontrivial o] {ι : Type*}
    (y : ι → Ω) (h : coordIdeal o y = ⊥) (k : ι) : y k ≠ 0 := by
  intro hk
  have : (MvPolynomial.X k : MvPolynomial ι o) ∈ coordIdeal o y := by
    simp [coordIdeal, coneMap, RingHom.mem_ker, hk]
  rw [h, Ideal.mem_bot] at this
  exact MvPolynomial.X_ne_zero k this

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a => simpa using hc a`. Consider the case `add p q hp hq => simpa using F.add_mem hp hq`. Consider the case `mul_X p k hp => simpa using F.mul_mem hp (hv k)`.
-/
theorem aeval_mem_subring {o σ : Type*} [CommRing o] [Algebra o Ω] (F : Subring Ω)
    (hc : ∀ a : o, algebraMap o Ω a ∈ F) (v : σ → Ω) (hv : ∀ k, v k ∈ F)
    (f : MvPolynomial σ o) : MvPolynomial.aeval v f ∈ F := by
  induction f using MvPolynomial.induction_on with
  | C a => simpa using hc a
  | add p q hp hq => simpa using F.add_mem hp hq
  | mul_X p k hp => simpa using F.mul_mem hp (hv k)

/- English proof (translation)
The claim follows from `aeval_mem_subring F.toSubfield.toSubring hc v hv f`.
-/
theorem aeval_mem_field {o σ : Type*} [CommRing o] [Algebra o Ω] (F : IntermediateField ℚ Ω)
    (hc : ∀ a : o, algebraMap o Ω a ∈ F) (v : σ → Ω) (hv : ∀ k, v k ∈ F)
    (f : MvPolynomial σ o) : MvPolynomial.aeval v f ∈ F :=
  aeval_mem_subring F.toSubfield.toSubring hc v hv f

/- English proof (translation)
The claim follows from `IntermediateField.subset_adjoin _ _ ⟨i, j, rfl⟩`.
-/
theorem div_mem_fnField (x : κ → Ω) (i j : κ) : x i / x j ∈ fnField x :=
  IntermediateField.subset_adjoin _ _ ⟨i, j, rfl⟩

/- English proof (translation)
Use `set y := x ∘ e with hy`. Set `ψ : Polynomial Ω →+* Ω` to `Polynomial.evalRingHom (y 0)⁻¹`. Express the relevant statement in the definitionally equal form `IsIntegral _ (x i / y 0)`. Establish `hev : ∀ f : MvPolynomial (Fin (D + 1)) ℚ, ψ (coneMap ℚ y f) = MvPolynomial.aeval (fun k => y k * (y 0)⁻¹) f`. Introduce `f`.

Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a => simp [coneMap, ψ]`. Consider the case `add p q hp hq => rw [map_add, map_add, map_add, hp, hq]`. Consider the case `mul_X p k hp => rw [map_mul, map_mul, map_mul, hp]`. Simplify using `[coneMap, ψ]`.

Establish `hmem : ∀ r : coneRing ℚ y, ψ r ∈ fnField y`. Introduce `r`. Take `⟨f, hf⟩` from `r.2`. Rewrite using `[← hf]`. Express the relevant statement in the definitionally equal form `ψ (coneMap ℚ y f) ∈ _`.

Rewrite using `[hev]`. Use `aeval_mem_field _ (fun a => IntermediateField.algebraMap_mem _ a) _ (fun k => ?_) f` and prove the remaining obligations. Simplify `div_mem_fnField y k 0` using `[div_eq_mul_inv]`. Set `φ : coneRing ℚ y →+* fnField y` to `(ψ.comp (coneRing ℚ y).val.toRingHom).codRestrict (fnField y).toSubfield.toSubring hmem`. Use `IsIntegral.map_of_comp_eq φ ψ (by ext r; rfl) (h.integral i)` as an intermediate fact.

Simplify `this` using `[ψ, div_eq_mul_inv]`.
-/
theorem div_isIntegral (x : κ → Ω) (e : Fin (D + 1) → κ) (h : IsRatProjFrame x e) (i : κ) :
    IsIntegral (fnField (x ∘ e)) (x i / x (e 0)) := by
  set y := x ∘ e with hy
  let ψ : Polynomial Ω →+* Ω := Polynomial.evalRingHom (y 0)⁻¹
  change IsIntegral _ (x i / y 0)
  have hev : ∀ f : MvPolynomial (Fin (D + 1)) ℚ,
      ψ (coneMap ℚ y f) = MvPolynomial.aeval (fun k => y k * (y 0)⁻¹) f := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp [coneMap, ψ]
    | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
    | mul_X p k hp => rw [map_mul, map_mul, map_mul, hp]; simp [coneMap, ψ]
  have hmem : ∀ r : coneRing ℚ y, ψ r ∈ fnField y := by
    intro r
    obtain ⟨f, hf⟩ := r.2
    rw [← hf]
    change ψ (coneMap ℚ y f) ∈ _
    rw [hev]
    refine aeval_mem_field _ (fun a => IntermediateField.algebraMap_mem _ a) _ (fun k => ?_) f
    simpa [div_eq_mul_inv] using div_mem_fnField y k 0
  let φ : coneRing ℚ y →+* fnField y :=
    (ψ.comp (coneRing ℚ y).val.toRingHom).codRestrict (fnField y).toSubfield.toSubring hmem
  have := IsIntegral.map_of_comp_eq φ ψ (by ext r; rfl) (h.integral i)
  simpa [ψ, div_eq_mul_inv] using this

/- English proof (translation)
The claim follows from `coord_ne_zero (x ∘ e) h.free 0`.
-/
theorem projective_frame_coord_ne_zero (x : κ → Ω) (e : Fin (D + 1) → κ) (h : IsRatProjFrame x e) : x (e 0) ≠ 0 :=
  coord_ne_zero (x ∘ e) h.free 0

/- English proof (translation)
Simplify using `[sec, Submodule.mem_map, MvPolynomial.mem_homogeneousSubmodule]`.
-/
theorem mem_sec_iff {o : Type*} [CommRing o] [Algebra o Ω] {ι : Type*} (x : ι → Ω) (d : ℕ) (s : Ω) :
    s ∈ sec o x d ↔ ∃ f : MvPolynomial ι o, f.IsHomogeneous d ∧ MvPolynomial.aeval x f = s := by
  simp [sec, Submodule.mem_map, MvPolynomial.mem_homogeneousSubmodule]

/- English proof (translation)
Take `⟨f, hf, rfl⟩` from `(mem_sec_iff x d s).1 hs`. Take `⟨g, hg, rfl⟩` from `(mem_sec_iff x d' t).1 ht`. Conclude with `(mem_sec_iff x _ _).2 ⟨f * g, hf.mul hg, by simp⟩`.
-/
theorem mul_mem_sec {o : Type*} [CommRing o] [Algebra o Ω] {ι : Type*} (x : ι → Ω) {d d' : ℕ}
    {s t : Ω} (hs : s ∈ sec o x d) (ht : t ∈ sec o x d') : s * t ∈ sec o x (d + d') := by
  obtain ⟨f, hf, rfl⟩ := (mem_sec_iff x d s).1 hs
  obtain ⟨g, hg, rfl⟩ := (mem_sec_iff x d' t).1 ht
  exact (mem_sec_iff x _ _).2 ⟨f * g, hf.mul hg, by simp⟩

/- English proof (translation)
Rewrite using `[MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq', MvPolynomial.eval₂_eq', Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Establish `hd : ∑ i, m i = d`. Use `hf (MvPolynomial.mem_support_iff.mp hm)` as an intermediate fact. Rewrite using `[← this, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]`.

Simplify using the standard rewrite rules. Simplify using `only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem aeval_smul_homog {o ι : Type*} [Fintype ι] [CommRing o] [Algebra o Ω]
    {f : MvPolynomial ι o} {d : ℕ} (hf : f.IsHomogeneous d) (c : Ω) (v : ι → Ω) :
    MvPolynomial.aeval (fun i => c * v i) f = c ^ d * MvPolynomial.aeval v f := by
  classical
  rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq', MvPolynomial.eval₂_eq',
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : ∑ i, m i = d := by
    have := hf (MvPolynomial.mem_support_iff.mp hm)
    rw [← this, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring

/- English proof (translation)
Take `⟨f, hf, rfl⟩` from `(mem_sec_iff x d s).1 hs`. Establish `: MvPolynomial.aeval x f / x j ^ d = MvPolynomial.aeval (fun i => (x j)⁻¹ * x i) f`. Rewrite using `[aeval_smul_homog hf, inv_pow, div_eq_mul_inv, mul_comm]`. Rewrite using `[this]`. Use `aeval_mem_field _ (fun a => ?_) _ (fun i => ?_) f` and prove the remaining obligations.

Simplify using `using IntermediateField.intCast_mem (fnField x) a`. Simplify `div_mem_fnField x i j` using `[div_eq_inv_mul]`.
-/
theorem sec_div_mem [Fintype κ] (x : κ → Ω) (j : κ) {d : ℕ} {s : Ω}
    (hs : s ∈ sec ℤ x d) : s / x j ^ d ∈ fnField x := by
  obtain ⟨f, hf, rfl⟩ := (mem_sec_iff x d s).1 hs
  have : MvPolynomial.aeval x f / x j ^ d = MvPolynomial.aeval (fun i => (x j)⁻¹ * x i) f := by
    rw [aeval_smul_homog hf, inv_pow, div_eq_mul_inv, mul_comm]
  rw [this]
  refine aeval_mem_field _ (fun a => ?_) _ (fun i => ?_) f
  · simpa using IntermediateField.intCast_mem (fnField x) a
  · simpa [div_eq_inv_mul] using div_mem_fnField x i j

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[IntermediateField.extendScalars_le_iff]`. Express the relevant statement in the definitionally equal form `IntermediateField.adjoin ℚ {t | ∃ i j, t = x i / x j} ≤ _`. Rewrite using `[IntermediateField.adjoin_le_iff]`. Introduce and unpack `t ⟨i, j, rfl⟩`.

Establish `hi : x i / x (e 0) ∈ IntermediateField.adjoin (fnField (x ∘ e)) (Set.range fun i => x i / x (e 0))` using `IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩`. Establish `hj : x j / x (e 0) ∈ IntermediateField.adjoin (fnField (x ∘ e)) (Set.range fun i => x i / x (e 0))` using `IntermediateField.subset_adjoin _ _ ⟨j, rfl⟩`. Establish `: x i / x j = (x i / x (e 0)) / (x j / x (e 0))`. Rewrite using `[div_div_div_cancel_right₀ hy0]`. Rewrite using `[this]`.

Conclude with `div_mem hi hj`. Rewrite using `[IntermediateField.adjoin_le_iff]`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `div_mem_fnField x i (e 0)`.
-/
theorem fnField_eq_adjoin (x : κ → Ω) (e : Fin (D + 1) → κ) (hy0 : x (e 0) ≠ 0) :
    IntermediateField.extendScalars (fnField_comp_le' x e) =
      IntermediateField.adjoin (fnField (x ∘ e)) (Set.range fun i => x i / x (e 0)) := by
  apply le_antisymm
  · rw [IntermediateField.extendScalars_le_iff]
    change IntermediateField.adjoin ℚ {t | ∃ i j, t = x i / x j} ≤ _
    rw [IntermediateField.adjoin_le_iff]
    rintro t ⟨i, j, rfl⟩
    have hi : x i / x (e 0) ∈ IntermediateField.adjoin (fnField (x ∘ e))
        (Set.range fun i => x i / x (e 0)) := IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩
    have hj : x j / x (e 0) ∈ IntermediateField.adjoin (fnField (x ∘ e))
        (Set.range fun i => x i / x (e 0)) := IntermediateField.subset_adjoin _ _ ⟨j, rfl⟩
    have : x i / x j = (x i / x (e 0)) / (x j / x (e 0)) := by
      rw [div_div_div_cancel_right₀ hy0]
    rw [this]
    exact div_mem hi hj
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨i, rfl⟩
    exact div_mem_fnField x i (e 0)

/- English proof (translation)
Rewrite using `[fnField_eq_adjoin x e (projective_frame_coord_ne_zero x e h)]`. Establish `: Finite (Set.range fun i => x i / x (e 0))` using `Set.finite_range _ |>.to_subtype`. Conclude with `IntermediateField.finiteDimensional_adjoin (by rintro _ ⟨i, rfl⟩; exact div_isIntegral x e h i)`.
-/
theorem finiteDimensional_ext [Finite κ] (x : κ → Ω) (e : Fin (D + 1) → κ) (h : IsRatProjFrame x e) :
    FiniteDimensional (fnField (x ∘ e)) (IntermediateField.extendScalars (fnField_comp_le' x e)) := by
  rw [fnField_eq_adjoin x e (projective_frame_coord_ne_zero x e h)]
  have : Finite (Set.range fun i => x i / x (e 0)) := Set.finite_range _ |>.to_subtype
  exact IntermediateField.finiteDimensional_adjoin (by rintro _ ⟨i, rfl⟩; exact div_isIntegral x e h i)

/- English proof (translation)
The claim follows from `IntermediateField.relfinrank_eq_finrank_of_le _`.
-/
theorem projDeg_eq (x : κ → Ω) (e : Fin (D + 1) → κ) :
    projDeg x e = finrank (fnField (x ∘ e)) (IntermediateField.extendScalars (fnField_comp_le' x e)) :=
  IntermediateField.relfinrank_eq_finrank_of_le _

/- English proof (translation)
Use `finiteDimensional_ext x e h` as an intermediate fact. Rewrite using `[projDeg_eq]`. Conclude with `Module.finrank_pos`.
-/
theorem projDeg_pos' [Finite κ] (x : κ → Ω) (e : Fin (D + 1) → κ) (h : IsRatProjFrame x e) :
    0 < projDeg x e := by
  have := finiteDimensional_ext x e h
  rw [projDeg_eq]
  exact Module.finrank_pos

def homogz {σ : Type*} (j : σ → Fin (D + 1)) (l : Fin (D + 1)) (N : ℕ) (g : MvPolynomial σ ℤ) :
    MvPolynomial (Fin (D + 1)) ℤ :=
  ∑ d ∈ Finset.range (N + 1), MvPolynomial.X l ^ (N - d) *
    MvPolynomial.rename j (MvPolynomial.homogeneousComponent d g)

def dehom (l : Fin (D + 1)) : MvPolynomial (Fin (D + 1)) ℤ →ₐ[ℤ] MvPolynomial {k // k ≠ l} ℤ :=
  MvPolynomial.aeval fun k => if h : k = l then 1 else MvPolynomial.X ⟨k, h⟩

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
