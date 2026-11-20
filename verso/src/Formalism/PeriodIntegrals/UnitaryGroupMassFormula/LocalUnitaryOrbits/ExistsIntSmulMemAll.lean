import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.ExistsIntBasis

noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory
  PI.VolStabSW PI.VolStabSW.PositiveNearLattice PI.VolStabSW.SdDualW
open scoped TensorProduct

section TopWs

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

/- English proof (translation)
Establish `hx : x ∈ Submodule.span E (L : Set (Fin n → E))` using `hL ▸ Submodule.mem_top`. Take `⟨m, f, g, rfl⟩` from `Submodule.mem_span_set'.1 hx`. Take `⟨y, hy, hint⟩` from `exists_integral_multiples ℤ ℚ (Finset.univ.image f)`. Use `⟨y, hy, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.smul_sum]`.

Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Establish `hi : IsIntegral ℤ (y • f i)` using `hint _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))`. Use `L.smul_mem (⟨y • f i, hi⟩ : 𝓞 E) (g i).2 using 1` and compare the differences between its conclusion and the goal. Rewrite using `[← smul_assoc]`. Both sides reduce to the same expression.
-/
theorem sdc_exists_int_smul_mem (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (x : Fin n → E) :
    ∃ y : ℤ, y ≠ 0 ∧ y • x ∈ L := by
  classical
  have hx : x ∈ Submodule.span E (L : Set (Fin n → E)) := hL ▸ Submodule.mem_top
  obtain ⟨m, f, g, rfl⟩ := Submodule.mem_span_set'.1 hx
  obtain ⟨y, hy, hint⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image f)
  refine ⟨y, hy, ?_⟩
  rw [Finset.smul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hi : IsIntegral ℤ (y • f i) := hint _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  convert L.smul_mem (⟨y • f i, hi⟩ : 𝓞 E) (g i).2 using 1
  rw [← smul_assoc]
  rfl

/- English proof (translation)
Use `choose y hy hw using fun j => sdc_exists_int_smul_mem L hL (w j)`. Use `⟨∏ j, y j, Finset.prod_ne_zero_iff.2 fun j _ => hy j, fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[← Finset.prod_erase_mul _ _ (Finset.mem_univ j), mul_smul]`. Conclude with `zsmul_mem (hw j) _`.
-/
theorem exists_int_smul_mem_all (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) {ι : Type} [Fintype ι] (w : ι → Fin n → E) :
    ∃ y : ℤ, y ≠ 0 ∧ ∀ j, y • w j ∈ L := by
  classical
  choose y hy hw using fun j => sdc_exists_int_smul_mem L hL (w j)
  refine ⟨∏ j, y j, Finset.prod_ne_zero_iff.2 fun j _ => hy j, fun j => ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j), mul_smul]
  exact zsmul_mem (hw j) _

/- English proof (translation)
Use function extensionality and compare the values at `j`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Simplify using `[ratV]`. Simplify using `[ratV, Pi.single_eq_of_ne h]`.
-/
theorem ratV_single (i : Fin n) (e : E) :
    ratV (F := F) (Fv F v) (Pi.single i e : Fin n → E) =
      (Pi.single i (inclR (F := F) (Fv F v) e) : Fin n → Fv F v ⊗[F] E) := by
  funext j
  by_cases h : j = i
  · subst h
    simp [ratV]
  · simp [ratV, Pi.single_eq_of_ne h]

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨x, hx, rfl⟩`.
-/
theorem ratV_mem_latLoc {Λ : Set (Fin n → E)} {x : Fin n → E} (hx : x ∈ Λ) :
    ratV (F := F) (Fv F v) x ∈ latLoc (E := E) v Λ :=
  Submodule.subset_span ⟨x, hx, rfl⟩

/- English proof (translation)
Establish `: FiniteDimensional F E` using `Module.Finite.of_restrictScalars_finite ℚ F E`. Take `⟨L, hLat, rfl⟩` from `hL`. Take `⟨d, b, hb⟩` from `exists_int_basis (F := F) (E := E)`. Take `⟨N, hN, hNw⟩` from `exists_int_smul_mem_all L hLat.span_eq_top (fun p : Fin n × Fin d => (Pi.single p.1 (b p.2) : Fin n → E))`. Establish `hNF : IsUnit ((N : F))`.

Rewrite using `[isUnit_iff_ne_zero]`. Conclude with `hN` after adjusting the coercions. Use `set b2 := b.isUnitSMul (fun _ => hNF) with hb2`. Establish `hb2L : ∀ i k, (Pi.single i (b2 k) : Fin n → E) ∈ L`. Introduce `i k`.

Establish `e : (Pi.single i (b2 k) : Fin n → E) = N • (Pi.single i (b k) : Fin n → E)`. Rewrite using `[hb2, Module.Basis.isUnitSMul_apply, Int.cast_smul_eq_zsmul]`. Use function extensionality and compare the values at `j`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Pi.single_eq_of_ne h]`. Rewrite using `[e]`. Conclude with `hNw (i, k)`. Set `H : AddSubgroup (Fin n → Fv F v ⊗[F] E)` to `AddSubgroup.pi Set.univ (fun _ => latA v b2)`.

Establish `hHo : IsOpen (H : Set (Fin n → Fv F v ⊗[F] E))`. Rewrite using `[AddSubgroup.coe_pi]`. Conclude with `isOpen_set_pi Set.finite_univ fun _ _ => isOpen_latA v b2`. Establish `hle : H ≤ (latLoc (E` using `E) v (L : Set (Fin n → E))).toAddSubgroup := by`. Introduce `X hX`.

Rewrite `hX` using `[AddSubgroup.mem_pi]`. Rewrite using `[Submodule.mem_toAddSubgroup, ← Finset.univ_sum_single X]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Establish `hXi : ∀ k, crd b2 (Fv F v) (X i) k ∈ v.adicCompletionIntegers F` using `hX i (Set.mem_univ _)`. Establish `e : Pi.single i (X i) = ∑ k, crd b2 (Fv F v) (X i) k • ratV (F` using `F) (Fv F v) (Pi.single i (b2 k) : Fin n → E) := by`.

Establish `hr` using `(Algebra.TensorProduct.basis (Fv F v) b2).sum_repr (X i)`. Simplify using `only [Algebra.TensorProduct.basis_apply] at hr`. Use function extensionality and compare the values at `j`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality.

Simplify using `only [ratV_single, Finset.sum_apply, Pi.smul_apply, Pi.single_eq_same]`. Use `conv_lhs => rw [← hr]`. Both sides reduce to the same expression. Simplify using `[ratV_single, Finset.sum_apply, Pi.single_eq_of_ne h]`. Rewrite using `[e]`.

Conclude with `Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ (⟨_, hXi k⟩ : v.adicCompletionIntegers F) (ratV_mem_latLoc v (hb2L i k))`. Conclude with `AddSubgroup.isOpen_mono hle hHo`.
-/
theorem sdc_isOpen_latLoc (Λ : Set (Fin n → E))
    (hL : ∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) :
    IsOpen (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E)) := by
  classical
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨L, hLat, rfl⟩ := hL
  obtain ⟨d, b, hb⟩ := exists_int_basis (F := F) (E := E)
  obtain ⟨N, hN, hNw⟩ := exists_int_smul_mem_all L hLat.span_eq_top
    (fun p : Fin n × Fin d => (Pi.single p.1 (b p.2) : Fin n → E))
  have hNF : IsUnit ((N : F)) := by
    rw [isUnit_iff_ne_zero]
    exact_mod_cast hN
  set b2 := b.isUnitSMul (fun _ => hNF) with hb2
  have hb2L : ∀ i k, (Pi.single i (b2 k) : Fin n → E) ∈ L := by
    intro i k
    have e : (Pi.single i (b2 k) : Fin n → E) = N • (Pi.single i (b k) : Fin n → E) := by
      rw [hb2, Module.Basis.isUnitSMul_apply, Int.cast_smul_eq_zsmul]
      funext j
      by_cases h : j = i
      · subst h
        simp
      · simp [Pi.single_eq_of_ne h]
    rw [e]
    exact hNw (i, k)
  let H : AddSubgroup (Fin n → Fv F v ⊗[F] E) := AddSubgroup.pi Set.univ (fun _ => latA v b2)
  have hHo : IsOpen (H : Set (Fin n → Fv F v ⊗[F] E)) := by
    rw [AddSubgroup.coe_pi]
    exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_latA v b2
  have hle : H ≤ (latLoc (E := E) v (L : Set (Fin n → E))).toAddSubgroup := by
    intro X hX
    rw [AddSubgroup.mem_pi] at hX
    rw [Submodule.mem_toAddSubgroup, ← Finset.univ_sum_single X]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hXi : ∀ k, crd b2 (Fv F v) (X i) k ∈ v.adicCompletionIntegers F := hX i (Set.mem_univ _)
    have e : Pi.single i (X i) = ∑ k, crd b2 (Fv F v) (X i) k •
        ratV (F := F) (Fv F v) (Pi.single i (b2 k) : Fin n → E) := by
      have hr := (Algebra.TensorProduct.basis (Fv F v) b2).sum_repr (X i)
      simp only [Algebra.TensorProduct.basis_apply] at hr
      funext j
      by_cases h : j = i
      · subst h
        simp only [ratV_single, Finset.sum_apply, Pi.smul_apply, Pi.single_eq_same]
        conv_lhs => rw [← hr]
        rfl
      · simp [ratV_single, Finset.sum_apply, Pi.single_eq_of_ne h]
    rw [e]
    exact Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ (⟨_, hXi k⟩ : v.adicCompletionIntegers F) (ratV_mem_latLoc v (hb2L i k))
  exact AddSubgroup.isOpen_mono hle hHo

/- English proof (translation)
Establish `: FiniteDimensional F E` using `Module.Finite.of_restrictScalars_finite ℚ F E`. Take `⟨L, hLat, rfl⟩` from `hL`. Establish `: Module.Finite (𝓞 E) L` using `Submodule.IsLattice.finite (A := E) L`. Establish `: Module.Finite ℤ L` using `Module.Finite.trans (𝓞 E) L`. Take `⟨m, s, hs⟩` from `Module.Finite.exists_fin (R := ℤ) (M := L)`.

Use `set g : Fin m → Fin n → Fv F v ⊗[F] E := fun i => ratV (F := F) (Fv F v) ((s i : L) : Fin n → E) with hg`. Establish `hadd : ∀ p q : Fin n → E, ratV (F` using `F) (Fv F v) (p + q) = ratV (F := F) (Fv F v) p + ratV (F := F) (Fv F v) q := by`. Introduce `p q`. Use function extensionality and compare the values at `j`. Simplify using `[ratV]`.

Establish `hzs : ∀ (r : ℤ) (p : Fin n → E), ratV (F` using `F) (Fv F v) (r • p) = r • ratV (F := F) (Fv F v) p := by`. Introduce `r p`. Use function extensionality and compare the values at `j`. Simplify using `[ratV]`. Establish `e : (latLoc (E` using `E) v (L : Set (Fin n → E)) : Set (Fin n → Fv F v ⊗[F] E)) = (fun c : Fin m → Fv F v => ∑ i, c i • g i) '' Set.pi Set.univ (fun _ => (v.adicCompletionIntegers F : Set (Fv F v))) := by`.

Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce `hz`. Establish `h1 : z ∈ Submodule.span (v.adicCompletionIntegers F) (Set.range g)`. Use `(Submodule.span_le.2 ?_) hz` and prove the remaining obligations.

Introduce and unpack `_ ⟨x, hx, rfl⟩`. Establish `hx' : (⟨x, hx⟩ : L) ∈ Submodule.span ℤ (Set.range s)` using `by rw [hs]; exact Submodule.mem_top`. Establish `key : ∀ y : L, y ∈ Submodule.span ℤ (Set.range s) → ratV (F` using `F) (Fv F v) (y : Fin n → E) ∈ Submodule.span (v.adicCompletionIntegers F) (Set.range g) := by`. Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`.

Consider the case `mem y hy`. Take `⟨i, rfl⟩` from `hy`. Conclude with `Submodule.subset_span ⟨i, rfl⟩`. Consider the case `zero`. Establish `: ratV (F` using `F) (Fv F v) (0 : Fin n → E) = 0 := by`.

Use function extensionality and compare the values at `j`. Simplify using `[ratV]`. Simplify `Submodule.zero_mem _` using `[this]`. Consider the case `add p q _ _ hp hq`. Rewrite using `[Submodule.coe_add, hadd]`.

Conclude with `Submodule.add_mem _ hp hq`. Consider the case `smul r p _ hp`. Rewrite using `[show ((r • p : L) : Fin n → E) = r • (p : Fin n → E) from rfl, hzs]`. Conclude with `zsmul_mem hp r`. Conclude with `key _ hx'`.

Rewrite `h1` using `[Submodule.mem_span_range_iff_exists_fun]`. Take `⟨c, rfl⟩` from `h1`. Conclude with `⟨fun i => (c i : Fv F v), fun i _ => (c i).2, rfl⟩`. Introduce and unpack `⟨c, hc, rfl⟩`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ (⟨c i, hc i (Set.mem_univ _)⟩ : v.adicCompletionIntegers F) (ratV_mem_latLoc v (s i).2)`.

Rewrite using `[e]`. Conclude with `(isCompact_univ_pi fun _ => PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v).image (continuous_finsetSum _ fun i _ => by fun_prop)`.
-/
theorem sdc_isCompact_latLoc (Λ : Set (Fin n → E))
    (hL : ∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) :
    IsCompact (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E)) := by
  classical
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨L, hLat, rfl⟩ := hL
  have : Module.Finite (𝓞 E) L := Submodule.IsLattice.finite (A := E) L
  have : Module.Finite ℤ L := Module.Finite.trans (𝓞 E) L
  obtain ⟨m, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := L)
  set g : Fin m → Fin n → Fv F v ⊗[F] E := fun i => ratV (F := F) (Fv F v) ((s i : L) : Fin n → E)
    with hg
  have hadd : ∀ p q : Fin n → E, ratV (F := F) (Fv F v) (p + q) =
      ratV (F := F) (Fv F v) p + ratV (F := F) (Fv F v) q := by
    intro p q
    funext j
    simp [ratV]
  have hzs : ∀ (r : ℤ) (p : Fin n → E), ratV (F := F) (Fv F v) (r • p) = r • ratV (F := F) (Fv F v) p := by
    intro r p
    funext j
    simp [ratV]
  have e : (latLoc (E := E) v (L : Set (Fin n → E)) : Set (Fin n → Fv F v ⊗[F] E)) =
      (fun c : Fin m → Fv F v => ∑ i, c i • g i) ''
        Set.pi Set.univ (fun _ => (v.adicCompletionIntegers F : Set (Fv F v))) := by
    ext z
    constructor
    · intro hz
      have h1 : z ∈ Submodule.span (v.adicCompletionIntegers F) (Set.range g) := by
        refine (Submodule.span_le.2 ?_) hz
        rintro _ ⟨x, hx, rfl⟩
        have hx' : (⟨x, hx⟩ : L) ∈ Submodule.span ℤ (Set.range s) := by rw [hs]; exact Submodule.mem_top
        have key : ∀ y : L, y ∈ Submodule.span ℤ (Set.range s) →
            ratV (F := F) (Fv F v) (y : Fin n → E) ∈
              Submodule.span (v.adicCompletionIntegers F) (Set.range g) := by
          intro y hy
          induction hy using Submodule.span_induction with
          | mem y hy =>
            obtain ⟨i, rfl⟩ := hy
            exact Submodule.subset_span ⟨i, rfl⟩
          | zero =>
            have : ratV (F := F) (Fv F v) (0 : Fin n → E) = 0 := by
              funext j
              simp [ratV]
            simpa [this] using Submodule.zero_mem _
          | add p q _ _ hp hq =>
            rw [Submodule.coe_add, hadd]
            exact Submodule.add_mem _ hp hq
          | smul r p _ hp =>
            rw [show ((r • p : L) : Fin n → E) = r • (p : Fin n → E) from rfl, hzs]
            exact zsmul_mem hp r
        exact key _ hx'
      rw [Submodule.mem_span_range_iff_exists_fun] at h1
      obtain ⟨c, rfl⟩ := h1
      exact ⟨fun i => (c i : Fv F v), fun i _ => (c i).2, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ (⟨c i, hc i (Set.mem_univ _)⟩ : v.adicCompletionIntegers F)
          (ratV_mem_latLoc v (s i).2)
  rw [e]
  exact (isCompact_univ_pi fun _ => PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v).image
    (continuous_finsetSum _ fun i _ => by fun_prop)

/- English proof (translation)
Introduce `hL`. Establish `e : LamT (E` using `E) v Λ a = Set.pi Set.univ (fun _ : Fin a => (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E))) := by`. Use extensionality with `X`. Simplify using `[LamT, Set.mem_pi]`. Rewrite using `[e]`.

Conclude with `⟨isCompact_univ_pi fun _ => sdc_isCompact_latLoc v Λ hL, isOpen_set_pi Set.finite_univ fun _ _ => sdc_isOpen_latLoc v Λ hL⟩`.
-/
theorem topW_holds (Λ : Set (Fin n → E)) (a : ℕ) : TopW v Λ a := by
  intro hL
  have e : LamT (E := E) v Λ a =
      Set.pi Set.univ (fun _ : Fin a => (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E))) := by
    ext X
    simp [LamT, Set.mem_pi]
  rw [e]
  exact ⟨isCompact_univ_pi fun _ => sdc_isCompact_latLoc v Λ hL,
    isOpen_set_pi Set.finite_univ fun _ _ => sdc_isOpen_latLoc v Λ hL⟩

end TopWs

end PI.OmLocU
