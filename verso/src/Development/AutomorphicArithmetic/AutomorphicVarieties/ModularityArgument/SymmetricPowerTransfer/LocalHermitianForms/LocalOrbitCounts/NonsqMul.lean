import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.NormOneIsCoboundaryUnramifiedQuadratic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.SqrtO
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.NormEx

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

namespace UpperTheory.V.Z.Sym.Loc.admissible_trace_regular

variable {K : Type} [Field K]

private def Nm (D x : K) : Prop := ∃ a b : K, a ^ 2 - D * b ^ 2 = x

/- English proof (translation)
Take `⟨a, b, rfl⟩` from `hx`. Take `⟨c, d, rfl⟩` from `hy`. Conclude with `⟨a * c + D * b * d, a * d + b * c, by ring⟩`.
-/
private theorem Nm.mul {D x y : K} (hx : Nm D x) (hy : Nm D y) : Nm D (x * y) := by
  obtain ⟨a, b, rfl⟩ := hx
  obtain ⟨c, d, rfl⟩ := hy
  exact ⟨a * c + D * b * d, a * d + b * c, by ring⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨s, 0, by ring⟩`.
-/
private theorem Nm.sq (D s : K) : Nm D (s ^ 2) := ⟨s, 0, by ring⟩

/- English proof (translation)
Establish `h` using `(hx.mul hxy).mul (Nm.sq D x⁻¹)`. Establish `e : x * (x * y) * x⁻¹ ^ 2 = y` using `by field_simp`. Rewrite `h` using `[e]`. Then use the resulting hypothesis.
-/
private theorem Nm.cancel {D x y : K} (h0 : x ≠ 0) (hx : Nm D x) (hxy : Nm D (x * y)) : Nm D y := by
  have h := (hx.mul hxy).mul (Nm.sq D x⁻¹)
  have e : x * (x * y) * x⁻¹ ^ 2 = y := by field_simp
  rwa [e] at h

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O K]

/- English proof (translation)
Use `haveI := h.frac`. Establish `hp0 : algebraMap O K p ≠ 0` using `fun e => hp.ne_zero ((IsFractionRing.injective O K) (e.trans (map_zero _).symm))`. Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := O) x`. Establish `hb0 : b ≠ 0` using `nonZeroDivisors.ne_zero hb`. Establish `hbK : algebraMap O K b ≠ 0` using `fun e => hb0 ((IsFractionRing.injective O K) (e.trans (map_zero _).symm))`.

Establish `ha0 : a ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hx`. Take `⟨n, u, hu⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (mul_ne_zero ha0 hb0) hp`. Establish `hu' : algebraMap O K a * algebraMap O K b = algebraMap O K u * algebraMap O K p ^ n`.

Rewrite using `[← map_mul, hu, map_mul, map_pow]`. Establish `e : algebraMap O K a / algebraMap O K b = algebraMap O K u * algebraMap O K p ^ n / algebraMap O K b ^ 2`. Rewrite using `[← hu']`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`.

Take `⟨k, rfl | rfl⟩` from `Nat.even_or_odd' n`. Conclude with `Or.inl ⟨u, algebraMap O K p ^ k / algebraMap O K b, div_ne_zero (pow_ne_zero _ hp0) hbK, by ring⟩`. Conclude with `Or.inr ⟨u, algebraMap O K p ^ (k + 1) / algebraMap O K b, div_ne_zero (pow_ne_zero _ hp0) hbK, by ring⟩`.
-/
private theorem even_im_hermitian_sub {Δ : K} (h : IsLoc O Δ) {p : O} (hp : Irreducible p) {x : K} (hx : x ≠ 0) :
    EvenVal O x ∨ EvenVal O (x * algebraMap O K p) := by
  haveI := h.frac
  have hp0 : algebraMap O K p ≠ 0 := fun e =>
    hp.ne_zero ((IsFractionRing.injective O K) (e.trans (map_zero _).symm))
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : algebraMap O K b ≠ 0 := fun e =>
    hb0 ((IsFractionRing.injective O K) (e.trans (map_zero _).symm))
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hx
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (mul_ne_zero ha0 hb0) hp
  have hu' : algebraMap O K a * algebraMap O K b = algebraMap O K u * algebraMap O K p ^ n := by
    rw [← map_mul, hu, map_mul, map_pow]
  have e : algebraMap O K a / algebraMap O K b
      = algebraMap O K u * algebraMap O K p ^ n / algebraMap O K b ^ 2 := by
    rw [← hu']; field_simp
  rw [e]
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · exact Or.inl ⟨u, algebraMap O K p ^ k / algebraMap O K b, div_ne_zero (pow_ne_zero _ hp0) hbK, by ring⟩
  · exact Or.inr ⟨u, algebraMap O K p ^ (k + 1) / algebraMap O K b, div_ne_zero (pow_ne_zero _ hp0) hbK, by ring⟩

/- English proof (translation)
Take `⟨r, hr⟩` from `hu`. Take `⟨r₀, rfl⟩` from `IsLocalRing.residue_surjective r`. Establish `h0 : IsLocalRing.residue O r₀ ≠ 0`. Introduce `e`. Rewrite `hr` using `[e, mul_zero]`.

Conclude with `(u.isUnit.map (IsLocalRing.residue O)).ne_zero hr`. Take `⟨r, hr', -⟩` from `sqrtO O K Δ h u r₀ ((IsLocalRing.residue_ne_zero_iff_isUnit _).1 h0) (by`. Rewrite using `[← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, hr, sq, sub_self])`. Conclude with `⟨r, by rw [← hr', sq]⟩`.
-/
private theorem sq_lift {Δ : K} (h : IsLoc O Δ) (u : Oˣ)
    (hu : IsSquare (IsLocalRing.residue O (u : O))) : IsSquare (u : O) := by
  obtain ⟨r, hr⟩ := hu
  obtain ⟨r₀, rfl⟩ := IsLocalRing.residue_surjective r
  have h0 : IsLocalRing.residue O r₀ ≠ 0 := by
    intro e
    rw [e, mul_zero] at hr
    exact (u.isUnit.map (IsLocalRing.residue O)).ne_zero hr
  obtain ⟨r, hr', -⟩ := sqrtO O K Δ h u r₀ ((IsLocalRing.residue_ne_zero_iff_isUnit _).1 h0) (by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, hr, sq, sub_self])
  exact ⟨r, by rw [← hr', sq]⟩

/- English proof (translation)
Use `haveI := h.fin`. Use `haveI := Fintype.ofFinite (IsLocalRing.ResidueField O)`. Apply `sq_lift h` to reduce the goal to its premises. Establish `a` using `quadraticChar_neg_one_iff_not_isSquare.2 (fun e => hu (sq_lift h u e))`. Establish `b` using `quadraticChar_neg_one_iff_not_isSquare.2 (fun e => hv (sq_lift h v e))`.

Rewrite using `[← quadraticChar_one_iff_isSquare (((u * v).isUnit.map (IsLocalRing.residue O)).ne_zero), Units.val_mul, map_mul, map_mul, a, b]`. Evaluate the numerical expressions.
-/
private theorem nonsq_mul {Δ : K} (h : IsLoc O Δ) (u v : Oˣ) (hu : ¬ IsSquare (u : O))
    (hv : ¬ IsSquare (v : O)) : IsSquare ((u * v : Oˣ) : O) := by
  classical
  haveI := h.fin
  haveI := Fintype.ofFinite (IsLocalRing.ResidueField O)
  apply sq_lift h
  have a := quadraticChar_neg_one_iff_not_isSquare.2 (fun e => hu (sq_lift h u e))
  have b := quadraticChar_neg_one_iff_not_isSquare.2 (fun e => hv (sq_lift h v e))
  rw [← quadraticChar_one_iff_isSquare (((u * v).isUnit.map (IsLocalRing.residue O)).ne_zero),
    Units.val_mul, map_mul, map_mul, a, b]
  norm_num

/- English proof (translation)
Take `⟨r, rfl⟩` from `hu`. Conclude with `⟨algebraMap O K r, 0, by rw [map_mul]; ring⟩`.
-/
private theorem Nm.ofSq (D : K) {u : O} (hu : IsSquare u) : Nm D (algebraMap O K u) := by
  obtain ⟨r, rfl⟩ := hu
  exact ⟨algebraMap O K r, 0, by rw [map_mul]; ring⟩

/- English proof (translation)
Use `haveI := h.frac`. Take `⟨p, hp⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Establish `hp0 : algebraMap O K p ≠ 0` using `fun e => hp.ne_zero ((IsFractionRing.injective O K) (e.trans (map_zero _).symm))`. Break down `even_im_hermitian_sub h hp hD with hD' | ⟨w, s, hs, hw⟩` into its components or cases. Establish `ev : ∀ z : K, EvenVal O z → Nm D z`.

Introduce and unpack `z ⟨u, t, -, rfl⟩`. Take `⟨ν, -, hν⟩` from `normEx O K D ⟨h.frac, h.compl, h.fin, h.two, hD'⟩ u`. Use `Nm.mul ⟨ν.re, ν.im, ?_⟩ (Nm.sq D t)` and prove the remaining obligations. Rewrite using `[← hν, QuadraticAlgebra.norm_def]`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨u, s, hs, e1⟩` from `(even_im_hermitian_sub h hp hx).resolve_left (fun e => nx (ev _ e))`. Take `⟨v, t, ht, e2⟩` from `(even_im_hermitian_sub h hp hy).resolve_left (fun e => ny (ev _ e))`. Use `ev _ ⟨u * v, s * t / algebraMap O K p, div_ne_zero (mul_ne_zero hs ht) hp0, ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_mul, map_mul]`. Clear the denominators using the available nonvanishing facts.

Take the linear combination `(y * algebraMap O K p) * e1 + (algebraMap O K u * s ^ 2) * e2`. Establish `dec : ∀ z : K, z ≠ 0 → ∃ (u : Oˣ) (n : K), Nm D n ∧ z = algebraMap O K u * n`. Introduce `z hz`. Break down `even_im_hermitian_sub h hp hz with ⟨u, t, -, e⟩ | ⟨u, t, ht, e⟩` into its components or cases. Conclude with `⟨u, t ^ 2, Nm.sq D t, e⟩`.

Use `⟨-(u * w⁻¹), (-D) * (t / s) ^ 2, Nm.mul ⟨0, 1, by ring⟩ (Nm.sq D _), ?_⟩` and prove the remaining obligations. Establish `e3 : algebraMap O K ((w⁻¹ : Oˣ) : O) * algebraMap O K w = 1`. Rewrite using `[← map_mul, Units.inv_mul, map_one]`. Rewrite using `[Units.val_neg, Units.val_mul, map_neg, map_mul]`. Establish `hs2 : (t / s) ^ 2 * s ^ 2 = t ^ 2` using `by field_simp`.

Apply `mul_right_cancel₀ (mul_ne_zero hp0 (pow_ne_zero 2 hs))` to reduce the goal to its premises. Take the linear combination `s ^ 2 * e - (algebraMap O K u * algebraMap O K ((w⁻¹ : Oˣ) : O) * t ^ 2) * hw - (algebraMap O K u * s ^ 2 * t ^ 2) * e3 - (algebraMap O K u * algebraMap O K ((w⁻¹ : Oˣ) : O) * D * algebraMap O K p) * hs2`. Take `⟨u, n, hn, rfl⟩` from `dec x hx`. Take `⟨v, m, hm, rfl⟩` from `dec y hy`. Use `Nm.ofSq D (nonsq_mul h u v (fun e => nx ((Nm.ofSq D e).mul hn)) (fun e => ny ((Nm.ofSq D e).mul hm)))` as an intermediate fact.

Establish `h2` using `(this.mul hn).mul hm`. Rewrite `h2` using `[Units.val_mul, map_mul]`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem key {Δ : K} (h : IsLoc O Δ) {D x y : K} (hD : D ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0)
    (nx : ¬ Nm D x) (ny : ¬ Nm D y) : Nm D (x * y) := by
  haveI := h.frac
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hp0 : algebraMap O K p ≠ 0 := fun e =>
    hp.ne_zero ((IsFractionRing.injective O K) (e.trans (map_zero _).symm))
  rcases even_im_hermitian_sub h hp hD with hD' | ⟨w, s, hs, hw⟩
  · have ev : ∀ z : K, EvenVal O z → Nm D z := by
      rintro z ⟨u, t, -, rfl⟩
      obtain ⟨ν, -, hν⟩ := normEx O K D ⟨h.frac, h.compl, h.fin, h.two, hD'⟩ u
      refine Nm.mul ⟨ν.re, ν.im, ?_⟩ (Nm.sq D t)
      rw [← hν, QuadraticAlgebra.norm_def]; ring
    obtain ⟨u, s, hs, e1⟩ := (even_im_hermitian_sub h hp hx).resolve_left (fun e => nx (ev _ e))
    obtain ⟨v, t, ht, e2⟩ := (even_im_hermitian_sub h hp hy).resolve_left (fun e => ny (ev _ e))
    refine ev _ ⟨u * v, s * t / algebraMap O K p, div_ne_zero (mul_ne_zero hs ht) hp0, ?_⟩
    rw [Units.val_mul, map_mul]
    field_simp
    linear_combination (y * algebraMap O K p) * e1 + (algebraMap O K u * s ^ 2) * e2
  · have dec : ∀ z : K, z ≠ 0 → ∃ (u : Oˣ) (n : K), Nm D n ∧ z = algebraMap O K u * n := by
      intro z hz
      rcases even_im_hermitian_sub h hp hz with ⟨u, t, -, e⟩ | ⟨u, t, ht, e⟩
      · exact ⟨u, t ^ 2, Nm.sq D t, e⟩
      · refine ⟨-(u * w⁻¹), (-D) * (t / s) ^ 2, Nm.mul ⟨0, 1, by ring⟩ (Nm.sq D _), ?_⟩
        have e3 : algebraMap O K ((w⁻¹ : Oˣ) : O) * algebraMap O K w = 1 := by
          rw [← map_mul, Units.inv_mul, map_one]
        rw [Units.val_neg, Units.val_mul, map_neg, map_mul]
        have hs2 : (t / s) ^ 2 * s ^ 2 = t ^ 2 := by field_simp
        apply mul_right_cancel₀ (mul_ne_zero hp0 (pow_ne_zero 2 hs))
        linear_combination s ^ 2 * e - (algebraMap O K u * algebraMap O K ((w⁻¹ : Oˣ) : O) * t ^ 2) * hw
          - (algebraMap O K u * s ^ 2 * t ^ 2) * e3
          - (algebraMap O K u * algebraMap O K ((w⁻¹ : Oˣ) : O) * D * algebraMap O K p) * hs2
    obtain ⟨u, n, hn, rfl⟩ := dec x hx
    obtain ⟨v, m, hm, rfl⟩ := dec y hy
    have := Nm.ofSq D (nonsq_mul h u v (fun e => nx ((Nm.ofSq D e).mul hn)) (fun e => ny ((Nm.ofSq D e).mul hm)))
    have h2 := (this.mul hn).mul hm
    rw [Units.val_mul, map_mul] at h2
    convert h2 using 1
    ring

/- English proof (translation)
The claim follows from `if_pos h`.
-/
private theorem hs_pos {D x : K} (h : Nm D x) : hs D x = 1 := if_pos h
/- English proof (translation)
The claim follows from `if_neg h`.
-/
private theorem hs_neg {D x : K} (h : ¬ Nm D x) : hs D x = -1 := if_neg h

end UpperTheory.V.Z.Sym.Loc.admissible_trace_regular

open UpperTheory.V.Z.Sym.Loc.admissible_trace_regular in
/- English proof (translation)
Introduce `O K _ _ _ _ _ Δ h D x y hD hx hy`. Apply the tactic sequence `by_cases nx : Nm D x <;> by_cases ny : Nm D y`. Rewrite using `[hs_pos nx, hs_pos ny, hs_pos (nx.mul ny), one_mul]`. Rewrite using `[hs_pos nx, hs_neg ny, hs_neg (fun e => ny (nx.cancel hx e)), one_mul]`. Rewrite using `[hs_neg nx, hs_pos ny, hs_neg (fun e => nx (ny.cancel hy (mul_comm x y ▸ e))), mul_one]`.

Rewrite using `[hs_neg nx, hs_neg ny, hs_pos (key h hD hx hy nx ny)]`. Evaluate the numerical expressions.
-/
theorem UpperTheory.V.Z.Sym.Loc.hsMul :
    UpperTheory.V.Z.Sym.Loc.HsMul := by
  intro O K _ _ _ _ _ Δ h D x y hD hx hy
  by_cases nx : Nm D x <;> by_cases ny : Nm D y
  · rw [hs_pos nx, hs_pos ny, hs_pos (nx.mul ny), one_mul]
  · rw [hs_pos nx, hs_neg ny, hs_neg (fun e => ny (nx.cancel hx e)), one_mul]
  · rw [hs_neg nx, hs_pos ny, hs_neg (fun e => nx (ny.cancel hy (mul_comm x y ▸ e))), mul_one]
  · rw [hs_neg nx, hs_neg ny, hs_pos (key h hD hx hy nx ny)]
    norm_num
