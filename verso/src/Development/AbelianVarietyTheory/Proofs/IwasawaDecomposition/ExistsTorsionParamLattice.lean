import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EllipticTorsionPointCoordinatesFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAlgebraicOfEllipticTorsionCoordinatesFinite

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.TorsionDegree

/- English proof (translation)
Establish `hn' : (n : ℂ) ≠ 0` using `by exact_mod_cast NeZero.ne n`. Set `f : ℂ → ℤ →+ (latticeCurve L).toAffine.Point` to `fun ω => (latticePointHom L).comp (zmultiplesHom ℂ (ω / n))`. Establish `hf : ∀ ω (a : ℤ), f ω a = latticePoint L (a * (ω / n))` using `fun ω a => by`. Simplify using `[f]`. Establish `h0 : ∀ ω ∈ L.lattice, f ω n = 0` using `fun ω hω => by`.

Rewrite using `[hf, latticePoint_eq_zero_iff]`. Use `hω using 1` and compare the differences between its conclusion and the goal. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Set `t : (Fin 2 → ZMod n) →+ (latticeCurve L).toAffine.Point` to `(ZMod.lift n ⟨f L.ω₁, h0 _ L.ω₁_mem_lattice⟩).comp (Pi.evalAddMonoidHom (fun _ => ZMod n) 0) + (ZMod.lift n ⟨f L.ω₂, h0 _ L.ω₂_mem_lattice⟩).comp (Pi.evalAddMonoidHom (fun _ => ZMod n) 1)`.

Establish `ht : ∀ a b : ℤ, t ![(a : ZMod n), (b : ZMod n)] = latticePoint L ((a * L.ω₁ + b * L.ω₂) / n)`. Introduce `a b`. Simplify using `only [t, AddMonoidHom.add_apply, AddMonoidHom.comp_apply, Pi.evalAddMonoidHom_apply, Matrix.cons_val_zero, Matrix.cons_val_one, ZMod.lift_coe, hf]`. Rewrite using `[← latticePoint_add]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Use `⟨t, (injective_iff_map_eq_zero t).2 fun v hv => ?_, fun P hP => ?_⟩` and prove the remaining obligations. Take `⟨a, ha⟩` from `ZMod.intCast_surjective (v 0)`. Take `⟨b, hb⟩` from `ZMod.intCast_surjective (v 1)`. Establish `e : v = ![(a : ZMod n), (b : ZMod n)]`.

Apply the tactic sequence `ext i; fin_cases i <;> simp [ha, hb]`. Rewrite `hv` using `[e, ht, latticePoint_eq_zero_iff, PeriodPair.mem_lattice]`. Take `⟨c, d, hcd⟩` from `hv`. Establish `h1 : ((a - n * c : ℤ) : ℝ) • L.ω₁ + ((b - n * d : ℤ) : ℝ) • L.ω₂ = 0`. Rewrite `hcd` using `[eq_div_iff hn']`.

Simplify using `only [Complex.real_smul]`. Use `push_cast`. Take the linear combination `-hcd`. Take `⟨h2, h3⟩` from `LinearIndependent.pair_iff.1 L.indep _ _ h1`. Establish `h2' : a = n * c`.

Establish `: a - n * c = 0` using `by exact_mod_cast h2`. Use linear arithmetic over natural numbers and integers. Establish `h3' : b = n * d`. Establish `: b - n * d = 0` using `by exact_mod_cast h3`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[e, h2', h3']`. Apply the tactic sequence `ext i; fin_cases i <;> simp`. Take `⟨z, rfl⟩` from `latticePoint_surjective L P`. Establish `h1 : latticePoint L (n • z) = 0`. Rewrite using `[← latticePointHom_apply, map_nsmul, latticePointHom_apply]`.

Conclude with `hP`. Rewrite `h1` using `[latticePoint_eq_zero_iff]`. Take `⟨a, b, hab⟩` from `PeriodPair.mem_lattice.1 h1`. Use `⟨_, (ht a b).trans ?_⟩` and prove the remaining obligations. Rewrite using `[hab, nsmul_eq_mul, mul_div_cancel_left₀ _ hn']`.
-/
theorem exists_torsion_param_lattice (L : PeriodPair) (n : ℕ) [NeZero n] :
    ∃ t : (Fin 2 → ZMod n) →+ (latticeCurve L).toAffine.Point, Function.Injective t ∧
      ∀ P, n • P = 0 → ∃ v, t v = P := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
  let f : ℂ → ℤ →+ (latticeCurve L).toAffine.Point := fun ω =>
    (latticePointHom L).comp (zmultiplesHom ℂ (ω / n))
  have hf : ∀ ω (a : ℤ), f ω a = latticePoint L (a * (ω / n)) := fun ω a => by
    simp [f]
  have h0 : ∀ ω ∈ L.lattice, f ω n = 0 := fun ω hω => by
    rw [hf, latticePoint_eq_zero_iff]
    convert hω using 1
    push_cast
    field_simp
  let t : (Fin 2 → ZMod n) →+ (latticeCurve L).toAffine.Point :=
    (ZMod.lift n ⟨f L.ω₁, h0 _ L.ω₁_mem_lattice⟩).comp (Pi.evalAddMonoidHom (fun _ => ZMod n) 0) +
    (ZMod.lift n ⟨f L.ω₂, h0 _ L.ω₂_mem_lattice⟩).comp (Pi.evalAddMonoidHom (fun _ => ZMod n) 1)
  have ht : ∀ a b : ℤ, t ![(a : ZMod n), (b : ZMod n)] = latticePoint L ((a * L.ω₁ + b * L.ω₂) / n) := by
    intro a b
    simp only [t, AddMonoidHom.add_apply, AddMonoidHom.comp_apply, Pi.evalAddMonoidHom_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, ZMod.lift_coe, hf]
    rw [← latticePoint_add]
    congr 1
    ring
  refine ⟨t, (injective_iff_map_eq_zero t).2 fun v hv => ?_, fun P hP => ?_⟩
  · obtain ⟨a, ha⟩ := ZMod.intCast_surjective (v 0)
    obtain ⟨b, hb⟩ := ZMod.intCast_surjective (v 1)
    have e : v = ![(a : ZMod n), (b : ZMod n)] := by
      ext i; fin_cases i <;> simp [ha, hb]
    rw [e, ht, latticePoint_eq_zero_iff, PeriodPair.mem_lattice] at hv
    obtain ⟨c, d, hcd⟩ := hv
    have h1 : ((a - n * c : ℤ) : ℝ) • L.ω₁ + ((b - n * d : ℤ) : ℝ) • L.ω₂ = 0 := by
      rw [eq_div_iff hn'] at hcd
      simp only [Complex.real_smul]
      push_cast
      linear_combination -hcd
    obtain ⟨h2, h3⟩ := LinearIndependent.pair_iff.1 L.indep _ _ h1
    have h2' : a = n * c := by
      have : a - n * c = 0 := by exact_mod_cast h2
      omega
    have h3' : b = n * d := by
      have : b - n * d = 0 := by exact_mod_cast h3
      omega
    rw [e, h2', h3']
    ext i; fin_cases i <;> simp
  · obtain ⟨z, rfl⟩ := latticePoint_surjective L P
    have h1 : latticePoint L (n • z) = 0 := by
      rw [← latticePointHom_apply, map_nsmul, latticePointHom_apply]; exact hP
    rw [latticePoint_eq_zero_iff] at h1
    obtain ⟨a, b, hab⟩ := PeriodPair.mem_lattice.1 h1
    refine ⟨_, (ht a b).trans ?_⟩
    rw [hab, nsmul_eq_mul, mul_div_cancel_left₀ _ hn']

/- English proof (translation)
Take `⟨L, C, hC⟩` from `exists_variableChange_eq_latticeCurve W`. Set `e` to `variableChangePointEquiv C hC`. Take `⟨t, hi, hs⟩` from `exists_torsion_param_lattice L n`. Use `⟨e.toAddMonoidHom.comp t, e.injective.comp hi, fun P hP => ?_⟩` and prove the remaining obligations. Take `⟨v, hv⟩` from `hs (e.symm P) (by rw [← map_nsmul, hP, map_zero])`.

Conclude with `⟨v, by simp [hv]⟩`.
-/
theorem exists_torsion_param (W : WeierstrassCurve ℂ) [W.IsElliptic] (n : ℕ) [NeZero n] :
    ∃ t : (Fin 2 → ZMod n) →+ W.toAffine.Point, Function.Injective t ∧
      ∀ P, n • P = 0 → ∃ v, t v = P := by
  obtain ⟨L, C, hC⟩ := exists_variableChange_eq_latticeCurve W
  let e := variableChangePointEquiv C hC
  obtain ⟨t, hi, hs⟩ := exists_torsion_param_lattice L n
  refine ⟨e.toAddMonoidHom.comp t, e.injective.comp hi, fun P hP => ?_⟩
  obtain ⟨v, hv⟩ := hs (e.symm P) (by rw [← map_nsmul, hP, map_zero])
  exact ⟨v, by simp [hv]⟩

/- English proof (translation)
Establish `hv : ∀ v : Fin 2 → ZMod n, n • v = 0` using `fun v => by`. Use extensionality with `i`. Simplify using the standard rewrite rules. Establish `h1 : ∀ v, ∃ Q, ι Q = t v` using `fun v => hr _ (by rw [← map_nsmul, hv, map_zero])`. Use `choose s hs' using h1`.

Establish `h2 : ∀ v, ∃ w, t w = φ (s v)` using `fun v => hs _ (by`. Establish `: n • s v = 0` using `hι (by rw [map_nsmul, hs', ← map_nsmul, hv, map_zero, map_zero])`. Rewrite using `[← map_nsmul, this, map_zero])`. Use `choose u hu using h2`. Establish `hadd : ∀ v w, u (v + w) = u v + u w` using `fun v w => hi (by`.

Rewrite using `[map_add, hu, hu, hu, ← map_add]`. Use `congr 1`. Conclude with `hι (by rw [map_add, hs', hs', hs', map_add]))`. Set `U` to `(AddMonoidHom.mk' u hadd).toZModLinearMap n`. Establish `hU : Function.Injective U` using `fun v w h => hi (by`.

Establish `h' : u v = u w` using `h`. Rewrite using `[← hs', ← hs', hφ ((hu v).symm.trans (h' ▸ hu w))])`. Use `⟨LinearEquiv.ofBijective U ⟨hU, Finite.surjective_of_injective hU⟩, fun v Q hQ => ?_⟩` and prove the remaining obligations. Rewrite using `[hι (hQ.trans (hs' v).symm), ← hu]`. Both sides reduce to the same expression.
-/
theorem exists_linearEquiv {G G' : Type} [AddCommGroup G] [AddCommGroup G'] (n : ℕ) [NeZero n]
    (t : (Fin 2 → ZMod n) →+ G') (hi : Function.Injective t) (hs : ∀ P, n • P = 0 → ∃ v, t v = P)
    (ι φ : G →+ G') (hι : Function.Injective ι) (hφ : Function.Injective φ)
    (hr : ∀ P, n • P = 0 → ∃ Q, ι Q = P) :
    ∃ g : (Fin 2 → ZMod n) ≃ₗ[ZMod n] (Fin 2 → ZMod n), ∀ v Q, ι Q = t v → φ Q = t (g v) := by
  have hv : ∀ v : Fin 2 → ZMod n, n • v = 0 := fun v => by
    ext i; simp
  have h1 : ∀ v, ∃ Q, ι Q = t v := fun v => hr _ (by rw [← map_nsmul, hv, map_zero])
  choose s hs' using h1
  have h2 : ∀ v, ∃ w, t w = φ (s v) := fun v => hs _ (by
    have : n • s v = 0 := hι (by rw [map_nsmul, hs', ← map_nsmul, hv, map_zero, map_zero])
    rw [← map_nsmul, this, map_zero])
  choose u hu using h2
  have hadd : ∀ v w, u (v + w) = u v + u w := fun v w => hi (by
    rw [map_add, hu, hu, hu, ← map_add]
    congr 1
    exact hι (by rw [map_add, hs', hs', hs', map_add]))
  let U := (AddMonoidHom.mk' u hadd).toZModLinearMap n
  have hU : Function.Injective U := fun v w h => hi (by
    have h' : u v = u w := h
    rw [← hs', ← hs', hφ ((hu v).symm.trans (h' ▸ hu w))])
  refine ⟨LinearEquiv.ofBijective U ⟨hU, Finite.surjective_of_injective hU⟩, fun v Q hQ => ?_⟩
  rw [hι (hQ.trans (hs' v).symm), ← hu]
  rfl

/- English proof (translation)
The claim follows from `Nat.card_congr (Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv _ _)).symm.toEquiv`.
-/
theorem card_linearEquiv (n : ℕ) :
    Nat.card ((Fin 2 → ZMod n) ≃ₗ[ZMod n] (Fin 2 → ZMod n)) = Nat.card (GL (Fin 2) (ZMod n)) :=
  Nat.card_congr (Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv _ _)).symm.toEquiv

/- English proof (translation)
Use `set S := torsionCoords (A.baseChange ℂ) n with hS`. Use `set M := IntermediateField.adjoin k S with hM`. Establish `: (A.baseChange ℂ).IsElliptic` using `inferInstanceAs (A.map _).IsElliptic`. Take `⟨t, hi, hs⟩` from `exists_torsion_param (A.baseChange ℂ) n`. Set `m : (M →ₐ[k] ℂ) → (A.baseChange M).toAffine.Point →+ (A.baseChange ℂ).toAffine.Point` to `fun φ => WeierstrassCurve.Affine.Point.map (W' := A.toAffine) φ`.

Establish `hm : ∀ φ, Function.Injective (m φ)` using `fun φ => WeierstrassCurve.Affine.Point.map_injective φ`. Establish `hpt : ∀ (x y : ℂ) (h : (A.baseChange ℂ).toAffine.Nonsingular x y) (hx : x ∈ M) (hy : y ∈ M), (A.baseChange M).toAffine.Nonsingular ⟨x, hx⟩ ⟨y, hy⟩` using `fun x y h hx hy => (A.toAffine.baseChange_nonsingular (f := M.val) M.val.injective ⟨x, hx⟩ ⟨y, hy⟩).mp h`. Establish `hr : ∀ P, n • P = 0 → ∃ Q, m M.val Q = P`. Introduce and unpack `(_ | ⟨x, y, h⟩) hP`. Conclude with `⟨0, rfl⟩`.

Conclude with `⟨.some _ _ (hpt x y h (IntermediateField.subset_adjoin k S ⟨x, y, h, hP, Or.inl rfl⟩) (IntermediateField.subset_adjoin k S ⟨x, y, h, hP, Or.inr rfl⟩)), rfl⟩`. Use `choose g hg using fun φ => exists_linearEquiv n t hi hs (m M.val) (m φ) (hm _) (hm φ) hr`. Establish `hginj : Function.Injective g`. Introduce `φ ψ h`. Use `IntermediateField.algHom_ext_of_eq_adjoin k hM ?_` and prove the remaining obligations.

Introduce and unpack `z ⟨x, y, hxy, h0, hz⟩`. Take `⟨v, hv⟩` from `hs _ h0`. Establish `hx` using `IntermediateField.subset_adjoin k S ⟨x, y, hxy, h0, Or.inl rfl⟩`. Establish `hy` using `IntermediateField.subset_adjoin k S ⟨x, y, hxy, h0, Or.inr rfl⟩`. Establish `e : m φ (.some _ _ (hpt x y hxy hx hy)) = m ψ (.some _ _ (hpt x y hxy hx hy))`.

Rewrite using `[hg φ v _ hv.symm, hg ψ v _ hv.symm, h]`. Establish `e'` using `WeierstrassCurve.Affine.Point.some.inj e`. Break down `hz with rfl | rfl` into its components or cases. Conclude with `e'.1`. Conclude with `e'.2`.

Rewrite using `[← card_linearEquiv, ← AlgHom.card k M ℂ, ← Nat.card_eq_fintype_card]`. Establish `: Finite ((Fin 2 → ZMod n) ≃ₗ[ZMod n] (Fin 2 → ZMod n))` using `Finite.of_injective _ (DFunLike.coe_injective (F := (Fin 2 → ZMod n) ≃ₗ[ZMod n] (Fin 2 → ZMod n)))`. Conclude with `Nat.card_le_card_of_injective g hginj`.
-/
theorem finrank_adjoin_le {k : Type} [Field k] [CharZero k] [Algebra k ℂ] (A : WeierstrassCurve k) [A.IsElliptic]
    (n : ℕ) [NeZero n] [FiniteDimensional k (IntermediateField.adjoin k (torsionCoords (A.baseChange ℂ) n))] :
    Module.finrank k (IntermediateField.adjoin k (torsionCoords (A.baseChange ℂ) n)) ≤
      Nat.card (GL (Fin 2) (ZMod n)) := by
  classical
  set S := torsionCoords (A.baseChange ℂ) n with hS
  set M := IntermediateField.adjoin k S with hM
  have : (A.baseChange ℂ).IsElliptic := inferInstanceAs (A.map _).IsElliptic
  obtain ⟨t, hi, hs⟩ := exists_torsion_param (A.baseChange ℂ) n
  let m : (M →ₐ[k] ℂ) → (A.baseChange M).toAffine.Point →+ (A.baseChange ℂ).toAffine.Point :=
    fun φ => WeierstrassCurve.Affine.Point.map (W' := A.toAffine) φ
  have hm : ∀ φ, Function.Injective (m φ) := fun φ => WeierstrassCurve.Affine.Point.map_injective φ
  have hpt : ∀ (x y : ℂ) (h : (A.baseChange ℂ).toAffine.Nonsingular x y) (hx : x ∈ M) (hy : y ∈ M),
      (A.baseChange M).toAffine.Nonsingular ⟨x, hx⟩ ⟨y, hy⟩ := fun x y h hx hy =>
    (A.toAffine.baseChange_nonsingular (f := M.val) M.val.injective ⟨x, hx⟩ ⟨y, hy⟩).mp h
  have hr : ∀ P, n • P = 0 → ∃ Q, m M.val Q = P := by
    rintro (_ | ⟨x, y, h⟩) hP
    · exact ⟨0, rfl⟩
    · exact ⟨.some _ _ (hpt x y h (IntermediateField.subset_adjoin k S ⟨x, y, h, hP, Or.inl rfl⟩)
        (IntermediateField.subset_adjoin k S ⟨x, y, h, hP, Or.inr rfl⟩)), rfl⟩
  choose g hg using fun φ => exists_linearEquiv n t hi hs (m M.val) (m φ) (hm _) (hm φ) hr
  have hginj : Function.Injective g := by
    intro φ ψ h
    refine IntermediateField.algHom_ext_of_eq_adjoin k hM ?_
    rintro z ⟨x, y, hxy, h0, hz⟩
    obtain ⟨v, hv⟩ := hs _ h0
    have hx := IntermediateField.subset_adjoin k S ⟨x, y, hxy, h0, Or.inl rfl⟩
    have hy := IntermediateField.subset_adjoin k S ⟨x, y, hxy, h0, Or.inr rfl⟩
    have e : m φ (.some _ _ (hpt x y hxy hx hy)) = m ψ (.some _ _ (hpt x y hxy hx hy)) := by
      rw [hg φ v _ hv.symm, hg ψ v _ hv.symm, h]
    have e' := WeierstrassCurve.Affine.Point.some.inj e
    rcases hz with rfl | rfl
    · exact e'.1
    · exact e'.2
  rw [← card_linearEquiv, ← AlgHom.card k M ℂ, ← Nat.card_eq_fintype_card]
  have : Finite ((Fin 2 → ZMod n) ≃ₗ[ZMod n] (Fin 2 → ZMod n)) :=
    Finite.of_injective _ (DFunLike.coe_injective (F := (Fin 2 → ZMod n) ≃ₗ[ZMod n] (Fin 2 → ZMod n)))
  exact Nat.card_le_card_of_injective g hginj

/- English proof (translation)
Rewrite using `[← IntermediateField.restrictScalars_adjoin_eq_sup]`. Establish `: IsScalarTower K H (IntermediateField.adjoin H S)` using `IsScalarTower.of_algebraMap_eq fun _ => rfl`. Establish `: Module.Free H (IntermediateField.adjoin H S)` using `Module.Free.of_divisionRing _ _`. Establish `: Module.Free K H` using `Module.Free.of_divisionRing _ _`. Establish `h : FiniteDimensional K (IntermediateField.adjoin H S)` using `Module.Finite.trans H _`.

Conclude with `⟨h, (Module.finrank_mul_finrank K H (IntermediateField.adjoin H S)).symm⟩`.
-/
theorem finrank_sup_adjoin {K L : Type} [Field K] [Field L] [Algebra K L] (H : IntermediateField K L) (S : Set L)
    [FiniteDimensional K H] [FiniteDimensional H (IntermediateField.adjoin H S)] :
    FiniteDimensional K (H ⊔ IntermediateField.adjoin K S : IntermediateField K L) ∧
      Module.finrank K (H ⊔ IntermediateField.adjoin K S : IntermediateField K L) =
        Module.finrank K H * Module.finrank H (IntermediateField.adjoin H S) := by
  rw [← IntermediateField.restrictScalars_adjoin_eq_sup]
  have : IsScalarTower K H (IntermediateField.adjoin H S) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.Free H (IntermediateField.adjoin H S) := Module.Free.of_divisionRing _ _
  have : Module.Free K H := Module.Free.of_divisionRing _ _
  have h : FiniteDimensional K (IntermediateField.adjoin H S) := Module.Finite.trans H _
  exact ⟨h,
    (Module.finrank_mul_finrank K H (IntermediateField.adjoin H S)).symm⟩

/- English proof (translation)
Introduce `d F _ A _`. Establish `hint : IsIntegral ℚ (sqrtNegNat d)` using `IsIntegral.of_pow (n := 2) (by norm_num) (by`. Rewrite using `[sqrtNegNat_sq]`. Conclude with `(isIntegral_natCast d).neg)`. Establish `: FiniteDimensional ℚ ℚ⟮sqrtNegNat d⟯` using `IntermediateField.adjoin.finiteDimensional hint`.

Establish `hH : FiniteDimensional ℚ (hilbertField d F)`. Unfold `hilbertField`. Use `infer_instance`. Use `set H := hilbertField d F with hHdef`. Set `A' : WeierstrassCurve H` to `A.map (IntermediateField.inclusion (le_sup_right : F ≤ H)).toRingHom`.

Establish `hA : A'.baseChange ℂ = A.baseChange ℂ`. Simplify using `only [A', WeierstrassCurve.baseChange, WeierstrassCurve.map_map]`. Both sides reduce to the same expression. Establish `: (A.baseChange ℂ).IsElliptic` using `inferInstanceAs (A.map _).IsElliptic`. Establish `: A'.IsElliptic`.

Simplify using `only [A']`. Conclude with `WeierstrassCurve.instIsEllipticMap _ _`. Establish `hfin` using `finite_torsionCoords (A.baseChange ℂ) 12 (by norm_num)`. Establish `halg` using `FieldsEx.isAlgebraic_of_torsionCoords_finite F A 12 hfin`. Establish `: Finite (torsionCoords (A'.baseChange ℂ) 12)` using `hA ▸ hfin.to_subtype`.

Establish `hM : FiniteDimensional H (IntermediateField.adjoin H (torsionCoords (A'.baseChange ℂ) 12))` using `IntermediateField.finiteDimensional_adjoin fun z hz => (halg z (hA ▸ hz)).isIntegral.tower_top`. Establish `hle` using `finrank_adjoin_le A' 12`. Take `⟨h1, h2⟩` from `finrank_sup_adjoin H (torsionCoords (A'.baseChange ℂ) 12)`. Establish `e : torsionField d A = H ⊔ IntermediateField.adjoin ℚ (torsionCoords (A'.baseChange ℂ) 12)`. Rewrite using `[hA]`.

Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `⟨h1, h2.le.trans (Nat.mul_le_mul_left _ hle)⟩`.
-/
theorem finrank_torsionField_le : ∀ (d : ℕ) (F : IntermediateField ℚ ℂ) [FiniteDimensional ℚ F] (A : WeierstrassCurve F) [A.IsElliptic], FiniteDimensional ℚ (torsionField d A) ∧ Module.finrank ℚ (torsionField d A) ≤ Module.finrank ℚ (hilbertField d F) * Nat.card (GL (Fin 2) (ZMod 12)) := by
  intro d F _ A _
  have hint : IsIntegral ℚ (sqrtNegNat d) :=
    IsIntegral.of_pow (n := 2) (by norm_num) (by
      rw [sqrtNegNat_sq]
      exact (isIntegral_natCast d).neg)
  have : FiniteDimensional ℚ ℚ⟮sqrtNegNat d⟯ := IntermediateField.adjoin.finiteDimensional hint
  have hH : FiniteDimensional ℚ (hilbertField d F) := by
    unfold hilbertField; infer_instance
  set H := hilbertField d F with hHdef
  let A' : WeierstrassCurve H := A.map (IntermediateField.inclusion (le_sup_right : F ≤ H)).toRingHom
  have hA : A'.baseChange ℂ = A.baseChange ℂ := by
    simp only [A', WeierstrassCurve.baseChange, WeierstrassCurve.map_map]
    rfl
  have : (A.baseChange ℂ).IsElliptic := inferInstanceAs (A.map _).IsElliptic
  have : A'.IsElliptic := by
    simp only [A']
    exact WeierstrassCurve.instIsEllipticMap _ _
  have hfin := finite_torsionCoords (A.baseChange ℂ) 12 (by norm_num)
  have halg := FieldsEx.isAlgebraic_of_torsionCoords_finite F A 12 hfin
  have : Finite (torsionCoords (A'.baseChange ℂ) 12) := hA ▸ hfin.to_subtype
  have hM : FiniteDimensional H (IntermediateField.adjoin H (torsionCoords (A'.baseChange ℂ) 12)) :=
    IntermediateField.finiteDimensional_adjoin fun z hz => (halg z (hA ▸ hz)).isIntegral.tower_top
  have hle := finrank_adjoin_le A' 12
  obtain ⟨h1, h2⟩ := finrank_sup_adjoin H (torsionCoords (A'.baseChange ℂ) 12)
  have e : torsionField d A = H ⊔ IntermediateField.adjoin ℚ (torsionCoords (A'.baseChange ℂ) 12) := by
    rw [hA]
    rfl
  rw [e]
  exact ⟨h1, h2.le.trans (Nat.mul_le_mul_left _ hle)⟩

end GlobalTheory.Mem.TorsionDegree
