import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviEmbMulSingle
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Cartan

noncomputable section

open GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel Matrix

namespace GlobalTheory.LocalCartan

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]

open ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] in

/- English proof (translation)
Rewrite using `[_root_.GlobalTheory.SplitFlip.mem_KO_iff]`. Use `⟨fun i j => ?_, fun i j => ?_⟩` and prove the remaining obligations. Rewrite using `[_root_.GlobalTheory.SmGL.val_diagT, diagonal_apply] split_ifs with h`. Substitute `h` using the available equality. Conclude with `(Valuation.mem_integer_iff _ _).mpr (ht i).le`.

Conclude with `zero_mem _`. Rewrite using `[← map_inv, _root_.GlobalTheory.SmGL.val_diagT, diagonal_apply] split_ifs with h`. Substitute `h` using the available equality. Use `(Valuation.mem_integer_iff _ _).mpr (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[Pi.inv_apply, Units.val_inv_eq_inv_val, map_inv₀, ht i, inv_one]`.

Conclude with `zero_mem _`.
-/
theorem _root_.GlobalTheory.LocalCartan.diagT_mem_KO {t : n → kˣ} (ht : ∀ i, valuation k (t i : k) = 1) :
    _root_.GlobalTheory.SmGL.diagT k n t ∈ _root_.GlobalTheory.SplitWeil.KO k n := by
  rw [_root_.GlobalTheory.SplitFlip.mem_KO_iff]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [_root_.GlobalTheory.SmGL.val_diagT, diagonal_apply]
    split_ifs with h
    · subst h
      exact (Valuation.mem_integer_iff _ _).mpr (ht i).le
    · exact zero_mem _
  · rw [← map_inv, _root_.GlobalTheory.SmGL.val_diagT, diagonal_apply]
    split_ifs with h
    · subst h
      refine (Valuation.mem_integer_iff _ _).mpr (le_of_eq ?_)
      rw [Pi.inv_apply, Units.val_inv_eq_inv_val, map_inv₀, ht i, inv_one]
    · exact zero_mem _

open ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] in

/- English proof (translation)
Take `⟨b, hb⟩` from `IsLocalization.exist_integer_multiples (nonZeroDivisors 𝒪[k]) (Finset.univ : Finset (n × n)) (fun p => (g : Matrix n n k) p.1 p.2)`. Use `choose G hG using fun i j => RingHom.mem_rangeS.mp (hb (i, j) (Finset.mem_univ _))`. Use `set f := algebraMap 𝒪[k] k with hf`. Use `set c : k := f b with hc_def`. Establish `hc : c ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2`.

Establish `hGg : f.mapMatrix (Matrix.of G) = c • (g : Matrix n n k)`. Use extensionality with `i j`. Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]`. Rewrite using `[hG i j, Algebra.smul_def]`. Establish `hdet : (Matrix.of G).det ≠ 0`.

Introduce `h0`. Establish `h1` using `congrArg f h0`. Rewrite `h1` using `[RingHom.map_det, hGg, map_zero, Matrix.det_smul]`. Conclude with `mul_ne_zero (pow_ne_zero _ hc) ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero h1`. Take `⟨P, C, hP, hC, a, ha, hPC⟩` from `_root_.Formalism.UG.P.cartan_smith (Matrix.of G) hdet`.

Establish `hinj : Function.Injective f` using `IsFractionRing.injective _ _`. Establish `hmap : ∀ A : GL n 𝒪[k], ((GeneralLinearGroup.map f A : GL n k) : Matrix n n k) = f.mapMatrix (A : Matrix n n 𝒪[k])` using `fun A => by ext i j; rw [GeneralLinearGroup.map_apply]; rfl`. Establish `hmem : ∀ A : GL n 𝒪[k], GeneralLinearGroup.map f A ∈ _root_.GlobalTheory.SplitWeil.KO k n` using `fun A => by unfold _root_.GlobalTheory.SplitWeil.KO; exact ⟨A, rfl⟩`. Establish `hne : ∀ i, f (a i) / c ≠ 0` using `fun i => div_ne_zero ((map_ne_zero_iff f hinj).mpr (ha i)) hc`. Use `⟨_, hmem (GeneralLinearGroup.mk'' P hP), _, hmem (GeneralLinearGroup.mk'' C hC), fun i => Units.mk0 (f (a i) / c) (hne i), ?_⟩` and prove the remaining obligations.

Establish `key : f.mapMatrix P * diagonal (fun i => f (a i)) * f.mapMatrix C = c • (g : Matrix n n k)`. Establish `hd : f.mapMatrix (diagonal a) = diagonal (fun i => f (a i))`. Rewrite using `[RingHom.mapMatrix_apply]`. Conclude with `Matrix.diagonal_map (map_zero f)`. Rewrite using `[← hGg, hPC, map_mul, map_mul, hd]`.

Establish `hdiag : diagonal (fun i => ((Units.mk0 (f (a i) / c) (hne i) : kˣ) : k)) = c⁻¹ • diagonal (fun i => f (a i))`. Use extensionality with `i j`. Apply the tactic sequence `by_cases h : i = j <;> simp [diagonal_apply, h, div_eq_inv_mul]`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_mul, Units.val_mul, hmap, hmap, _root_.GlobalTheory.SmGL.val_diagT]`.

Express the relevant statement in the definitionally equal form `(g : Matrix n n k) = f.mapMatrix P * _ * f.mapMatrix C`. Rewrite using `[hdiag, Matrix.mul_smul, Matrix.smul_mul, key, smul_smul, inv_mul_cancel₀ hc, one_smul]`.
-/
theorem _root_.GlobalTheory.LocalCartan.exists_diagT (g : GL n k) :
    ∃ x ∈ _root_.GlobalTheory.SplitWeil.KO k n, ∃ y ∈ _root_.GlobalTheory.SplitWeil.KO k n,
      ∃ t : n → kˣ, g = x * _root_.GlobalTheory.SmGL.diagT k n t * y := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors 𝒪[k])
    (Finset.univ : Finset (n × n)) (fun p => (g : Matrix n n k) p.1 p.2)
  choose G hG using fun i j => RingHom.mem_rangeS.mp (hb (i, j) (Finset.mem_univ _))
  set f := algebraMap 𝒪[k] k with hf
  set c : k := f b with hc_def
  have hc : c ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  have hGg : f.mapMatrix (Matrix.of G) = c • (g : Matrix n n k) := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply,
      smul_eq_mul]
    rw [hG i j, Algebra.smul_def]
  have hdet : (Matrix.of G).det ≠ 0 := by
    intro h0
    have h1 := congrArg f h0
    rw [RingHom.map_det, hGg, map_zero, Matrix.det_smul] at h1
    exact mul_ne_zero (pow_ne_zero _ hc) ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero h1
  obtain ⟨P, C, hP, hC, a, ha, hPC⟩ := _root_.Formalism.UG.P.cartan_smith (Matrix.of G) hdet
  have hinj : Function.Injective f := IsFractionRing.injective _ _
  have hmap : ∀ A : GL n 𝒪[k],
      ((GeneralLinearGroup.map f A : GL n k) : Matrix n n k) = f.mapMatrix (A : Matrix n n 𝒪[k]) :=
    fun A => by ext i j; rw [GeneralLinearGroup.map_apply]; rfl
  have hmem : ∀ A : GL n 𝒪[k], GeneralLinearGroup.map f A ∈ _root_.GlobalTheory.SplitWeil.KO k n :=
    fun A => by unfold _root_.GlobalTheory.SplitWeil.KO; exact ⟨A, rfl⟩
  have hne : ∀ i, f (a i) / c ≠ 0 := fun i =>
    div_ne_zero ((map_ne_zero_iff f hinj).mpr (ha i)) hc
  refine ⟨_, hmem (GeneralLinearGroup.mk'' P hP), _, hmem (GeneralLinearGroup.mk'' C hC),
    fun i => Units.mk0 (f (a i) / c) (hne i), ?_⟩
  have key : f.mapMatrix P * diagonal (fun i => f (a i)) * f.mapMatrix C = c • (g : Matrix n n k) := by
    have hd : f.mapMatrix (diagonal a) = diagonal (fun i => f (a i)) := by
      rw [RingHom.mapMatrix_apply]
      exact Matrix.diagonal_map (map_zero f)
    rw [← hGg, hPC, map_mul, map_mul, hd]
  have hdiag : diagonal (fun i => ((Units.mk0 (f (a i) / c) (hne i) : kˣ) : k)) =
      c⁻¹ • diagonal (fun i => f (a i)) := by
    ext i j
    by_cases h : i = j <;> simp [diagonal_apply, h, div_eq_inv_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hmap, hmap, _root_.GlobalTheory.SmGL.val_diagT]
  change (g : Matrix n n k) = f.mapMatrix P * _ * f.mapMatrix C
  rw [hdiag, Matrix.mul_smul, Matrix.smul_mul, key, smul_smul, inv_mul_cancel₀ hc, one_smul]

open ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] in
/- English proof (translation)
The claim follows from `_root_.GlobalTheory.SmGL.ord_eq_zero_iff.mpr (by simp)`.
-/
private lemma ord_one_twisted_operators : _root_.GlobalTheory.SmGL.ord k 1 = 0 :=
  _root_.GlobalTheory.SmGL.ord_eq_zero_iff.mpr (by simp)

open ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] in
/- English proof (translation)
Establish `h` using `_root_.GlobalTheory.SmGL.ord_mul k y y⁻¹`. Rewrite `h` using `[mul_inv_cancel, ord_one_twisted_operators]`. Use linear arithmetic over natural numbers and integers.
-/
private lemma ord_inv_twisted_operators (y : kˣ) :
    _root_.GlobalTheory.SmGL.ord k y⁻¹ = -_root_.GlobalTheory.SmGL.ord k y := by
  have h := _root_.GlobalTheory.SmGL.ord_mul k y y⁻¹
  rw [mul_inv_cancel, ord_one_twisted_operators] at h
  omega

open ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] in
/- English proof (translation)
Establish `h1` using `_root_.GlobalTheory.SmGL.ord_eq_one hϖ`. Proceed by induction on `m using Int.induction_on with`. Consider the case `zero => simpa using ord_one_twisted_operators`. Consider the case `succ i ih => rw [_root_.zpow_add_one, _root_.GlobalTheory.SmGL.ord_mul, ih, h1]`. Consider the case `pred i ih`.

Rewrite using `[_root_.zpow_sub_one, _root_.GlobalTheory.SmGL.ord_mul, ih, ord_inv_twisted_operators, h1]`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma ord_zpow_uniformizer' {ϖ : kˣ}
    (hϖ : valuation k (ϖ : k) = uniformizer k) (m : ℤ) :
    _root_.GlobalTheory.SmGL.ord k (ϖ ^ m) = m := by
  have h1 := _root_.GlobalTheory.SmGL.ord_eq_one hϖ
  induction m using Int.induction_on with
  | zero => simpa using ord_one_twisted_operators
  | succ i ih => rw [_root_.zpow_add_one, _root_.GlobalTheory.SmGL.ord_mul, ih, h1]
  | pred i ih =>
    rw [_root_.zpow_sub_one, _root_.GlobalTheory.SmGL.ord_mul, ih, ord_inv_twisted_operators, h1]
    ring

open ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] in
/- English proof (translation)
Use `⟨x * (ϖ ^ _root_.GlobalTheory.SmGL.ord k x)⁻¹, _root_.GlobalTheory.SmGL.ord k x, ?_, by simp⟩` and prove the remaining obligations. Apply `_root_.GlobalTheory.SmGL.ord_eq_zero_iff.mp` to reduce the goal to its premises. Rewrite using `[_root_.GlobalTheory.SmGL.ord_mul, ord_inv_twisted_operators, ord_zpow_uniformizer' hϖ]`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma exists_unit_mul_zpow_uniformizer {ϖ : kˣ}
    (hϖ : valuation k (ϖ : k) = uniformizer k) (x : kˣ) :
    ∃ u : kˣ, ∃ m : ℤ, valuation k (u : k) = 1 ∧ x = u * ϖ ^ m := by
  refine ⟨x * (ϖ ^ _root_.GlobalTheory.SmGL.ord k x)⁻¹, _root_.GlobalTheory.SmGL.ord k x, ?_, by simp⟩
  apply _root_.GlobalTheory.SmGL.ord_eq_zero_iff.mp
  rw [_root_.GlobalTheory.SmGL.ord_mul, ord_inv_twisted_operators,
    ord_zpow_uniformizer' hϖ]
  ring

open ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] in

/- English proof (translation)
Take `⟨x, hx, y, hy, t, rfl⟩` from `_root_.GlobalTheory.LocalCartan.exists_diagT g`. Use `choose u m hu htu using fun i => exists_unit_mul_zpow_uniformizer hϖ (t i)`. Use `⟨x * _root_.GlobalTheory.SmGL.diagT k n u, mul_mem hx (_root_.GlobalTheory.LocalCartan.diagT_mem_KO hu), y, hy, m, ?_⟩` and prove the remaining obligations. Establish `ht : t = u * fun i => ϖ ^ m i` using `funext htu`. Rewrite using `[ht, map_mul]`.

Simplify using `only [mul_assoc]`.
-/
theorem _root_.GlobalTheory.LocalCartan.cartan_decomposition (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n]
    (ϖ : kˣ) (g : GL n k) (hϖ : valuation k (ϖ : k) = uniformizer k) :
    ∃ x ∈ _root_.GlobalTheory.SplitWeil.KO k n, ∃ y ∈ _root_.GlobalTheory.SplitWeil.KO k n,
      ∃ m : n → ℤ, g = x * _root_.GlobalTheory.SmGL.diagT k n (fun i => ϖ ^ m i) * y := by
  obtain ⟨x, hx, y, hy, t, rfl⟩ := _root_.GlobalTheory.LocalCartan.exists_diagT g
  choose u m hu htu using fun i => exists_unit_mul_zpow_uniformizer hϖ (t i)
  refine ⟨x * _root_.GlobalTheory.SmGL.diagT k n u,
    mul_mem hx (_root_.GlobalTheory.LocalCartan.diagT_mem_KO hu), y, hy, m, ?_⟩
  have ht : t = u * fun i => ϖ ^ m i := funext htu
  rw [ht, map_mul]
  simp only [mul_assoc]

end GlobalTheory.LocalCartan
