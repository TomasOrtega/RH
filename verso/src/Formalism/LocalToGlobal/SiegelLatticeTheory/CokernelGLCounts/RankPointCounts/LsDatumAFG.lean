import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumATools
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocOProj

noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section FG

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

/- English proof (translation)
Use `haveI : IsReduced E := L.reduced`. Use `haveI : Module.Free F E := L.free`. Use `haveI : Module.Finite F E := Module.finite_of_finrank_eq_succ L.rank`. Use `haveI : Nontrivial E := Module.nontrivial_of_finrank_eq_succ L.rank`. Establish `hA : ∀ a : 𝒪[F], algebraMap 𝒪[F] E a = algebraMap F E (a : F)` using `fun a => IsScalarTower.algebraMap_apply 𝒪[F] F E a`.

Establish `hcjA : ∀ (a : F) (w : E), L.cj (algebraMap F E a * w) = algebraMap F E a * L.cj w`. Introduce `a w`. Rewrite using `[map_mul, L.cj.commutes]`. Establish `hcjO : ∀ x ∈ L.O, L.cj x ∈ L.O`. Introduce `x hx`.

Rewrite `hx`, the goal using `[L.O_def]`. Conclude with `hx.map ((L.cj : E →ₐ[F] E).restrictScalars 𝒪[F])`. Establish `htr : ∀ z ∈ L.O, ∃ a : 𝒪[F], algebraMap 𝒪[F] E a = z + L.cj z`. Introduce `z hz`. Establish `hmem : z + L.cj z ∈ L.O` using `L.O.add_mem hz (hcjO z hz)`.

Take `⟨a, ha⟩` from `(L.cj_fix (z + L.cj z)).1 (by rw [map_add, L.cj_cj, add_comm])`. Establish `hint : IsIntegral 𝒪[F] (algebraMap F E a)` using `ha ▸ (L.O_def _).1 hmem`. Establish `hint' : IsIntegral 𝒪[F] a` using `(isIntegral_algHom_iff (IsScalarTower.toAlgHom 𝒪[F] F E) (algebraMap F E).injective).1 hint`. Take `⟨y, hy⟩` from `IsIntegrallyClosed.isIntegral_iff.1 hint'`. Conclude with `⟨y, by rw [hA, ← ha, ← hy]; rfl⟩`.

Establish `hnd : ∀ x : E, (∀ y : E, x * y + L.cj (x * y) = 0) → x = 0`. Introduce `x hx`. Establish `h1 : L.cj x = -x`. Establish `h` using `hx 1`. Rewrite `h` using `[mul_one]`.

Conclude with `eq_neg_of_add_eq_zero_right h`. Establish `h2` using `hx x`. Rewrite `h2` using `[map_mul, h1, neg_mul_neg, ← two_mul]`. Establish `hu : IsUnit (2 : E)`. Establish `h3 : (2 : E) = algebraMap F E 2` using `(map_ofNat (algebraMap F E) 2).symm`.

Rewrite using `[h3]`. Conclude with `(IsUnit.mk0 (2 : F) two_ne_zero).map _`. Establish `hxx : x * x = 0` using `hu.mul_right_eq_zero.1 h2`. Conclude with `IsReduced.eq_zero x ⟨2, by rw [pow_two, hxx]⟩`. Set `b` to `Module.finBasisOfFinrankEq F E L.rank`.

Establish `hsc : ∀ i, ∃ c : F, c ≠ 0 ∧ algebraMap F E c * b i ∈ L.O`. Introduce `i`. Use `haveI : Algebra.IsAlgebraic 𝒪[F] F := IsLocalization.isAlgebraic F (nonZeroDivisors 𝒪[F])`. Use `haveI : Algebra.IsAlgebraic 𝒪[F] E := Algebra.IsAlgebraic.trans 𝒪[F] F E`. Take `⟨c, hc, hci⟩` from `(Algebra.IsAlgebraic.isAlgebraic (R := 𝒪[F]) (b i)).exists_integral_multiple`.

Use `⟨(c : F), by exact_mod_cast hc, (L.O_def _).2 ?_⟩` and prove the remaining obligations. Rewrite `hci` using `[Algebra.smul_def, hA]`. Then use the resulting hypothesis. Use `choose c hc0 hcO using hsc`. Set `φ : 𝒪[F] →+* L.O` to `(algebraMap 𝒪[F] E).codRestrict L.O (fun a => (L.O_def _).2 isIntegral_algebraMap)`. Use `letI : Algebra 𝒪[F] L.O := φ.toAlgebra`.

Establish `hsm : ∀ (a : 𝒪[F]) (x : L.O), ((a • x : L.O) : E) = algebraMap F E (a : F) * x`. Introduce `a x`. Rewrite using `[Algebra.smul_def, Subring.coe_mul, ← hA]`. Both sides reduce to the same expression. Set `B : Fin 2 → E` to `fun i => algebraMap F E (c i) * b i`.

Set `g : L.O →ₗ[𝒪[F]] (Fin 2 → E)` to `{ toFun := fun x i => (x : E) * B i + L.cj ((x : E) * B i) map_add' := by`. Introduce `x y`. Use function extensionality and compare the values at `i`. Simplify using `only [Subring.coe_add, add_mul, map_add, Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree.

Use the proof step `map_smul' := by`. Introduce `a x`. Use function extensionality and compare the values at `i`. Simplify using `only [RingHom.id_apply, Pi.smul_apply]`. Rewrite using `[hsm, Algebra.smul_def, hA]`.

Simplify using `only [mul_assoc, hcjA, mul_add] }`. Set `N : Submodule 𝒪[F] (Fin 2 → E)` to `Submodule.span 𝒪[F] (Set.range fun i : Fin 2 => Pi.single i (1 : E))`. Use `haveI : IsNoetherian 𝒪[F] N := isNoetherian_span_of_finite 𝒪[F] (Set.finite_range _)`. Establish `hgN : ∀ x, g x ∈ N`. Introduce `x`.

Establish `hx : ∀ i, ∃ a : 𝒪[F], algebraMap 𝒪[F] E a = (x : E) * B i + L.cj ((x : E) * B i)` using `fun i => htr _ (L.O.mul_mem x.2 (hcO i))`. Use `choose a ha using hx`. Rewrite using `[Submodule.mem_span_range_iff_exists_fun]`. Use `⟨a, ?_⟩` and prove the remaining obligations. Use `show _ = fun j => (x : E) * B j + L.cj ((x : E) * B j)`.

Use function extensionality and compare the values at `j`. Simplify using `[Finset.sum_apply, Pi.single_apply, Algebra.smul_def, ha]`. Establish `hinj : Function.Injective (g.codRestrict N hgN)`. Introduce `x y hxy`. Establish `h0 : g x = g y` using `congrArg Subtype.val hxy`.

Establish `hd : ∀ i, ((x : E) - y) * B i + L.cj (((x : E) - y) * B i) = 0`. Introduce `i`. Establish `h` using `congrFun h0 i`. Simplify using `only [g, LinearMap.coe_mk, AddHom.coe_mk] at h`. Rewrite using `[sub_mul, map_sub]`.

Take the linear combination `h`. Establish `hb : ∀ i, ((x : E) - y) * b i + L.cj (((x : E) - y) * b i) = 0`. Introduce `i`. Establish `h` using `hd i`. Simplify using `only [B] at h`.

Rewrite `h` using `[mul_left_comm, hcjA, ← mul_add]`. Conclude with `((IsUnit.mk0 _ (hc0 i)).map (algebraMap F E)).mul_right_eq_zero.1 h`. Establish `hall : ∀ w, ((x : E) - y) * w + L.cj (((x : E) - y) * w) = 0`. Introduce `w`. Set `τ : E →ₗ[F] E` to `LinearMap.mulLeft F ((x : E) - y) + (L.cj.toLinearMap).comp (LinearMap.mulLeft F ((x : E) - y))`.

Establish `hτ : τ = 0` using `b.ext (fun i => by simpa [τ] using hb i)`. Simplify `LinearMap.congr_fun hτ w` using `[τ]`. Conclude with `Subtype.ext (sub_eq_zero.1 (hnd _ hall))`. Use `haveI : IsNoetherian 𝒪[F] L.O := isNoetherian_of_injective (g.codRestrict N hgN) hinj`. Conclude with `isNoetherianRing_iff.2 (isNoetherian_of_tower 𝒪[F] this)`.
-/
private theorem isNoetherianRing_locE_O' (L : LocE F E) [IsNonarchimedeanLocalField F] [CharZero F] :
    IsNoetherianRing L.O := by
  classical
  haveI : IsReduced E := L.reduced
  haveI : Module.Free F E := L.free
  haveI : Module.Finite F E := Module.finite_of_finrank_eq_succ L.rank
  haveI : Nontrivial E := Module.nontrivial_of_finrank_eq_succ L.rank
  have hA : ∀ a : 𝒪[F], algebraMap 𝒪[F] E a = algebraMap F E (a : F) := fun a =>
    IsScalarTower.algebraMap_apply 𝒪[F] F E a
  have hcjA : ∀ (a : F) (w : E), L.cj (algebraMap F E a * w) = algebraMap F E a * L.cj w := by
    intro a w
    rw [map_mul, L.cj.commutes]
  have hcjO : ∀ x ∈ L.O, L.cj x ∈ L.O := by
    intro x hx
    rw [L.O_def] at hx ⊢
    exact hx.map ((L.cj : E →ₐ[F] E).restrictScalars 𝒪[F])
  have htr : ∀ z ∈ L.O, ∃ a : 𝒪[F], algebraMap 𝒪[F] E a = z + L.cj z := by
    intro z hz
    have hmem : z + L.cj z ∈ L.O := L.O.add_mem hz (hcjO z hz)
    obtain ⟨a, ha⟩ := (L.cj_fix (z + L.cj z)).1 (by rw [map_add, L.cj_cj, add_comm])
    have hint : IsIntegral 𝒪[F] (algebraMap F E a) := ha ▸ (L.O_def _).1 hmem
    have hint' : IsIntegral 𝒪[F] a :=
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom 𝒪[F] F E) (algebraMap F E).injective).1 hint
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint'
    exact ⟨y, by rw [hA, ← ha, ← hy]; rfl⟩
  have hnd : ∀ x : E, (∀ y : E, x * y + L.cj (x * y) = 0) → x = 0 := by
    intro x hx
    have h1 : L.cj x = -x := by
      have h := hx 1
      rw [mul_one] at h
      exact eq_neg_of_add_eq_zero_right h
    have h2 := hx x
    rw [map_mul, h1, neg_mul_neg, ← two_mul] at h2
    have hu : IsUnit (2 : E) := by
      have h3 : (2 : E) = algebraMap F E 2 := (map_ofNat (algebraMap F E) 2).symm
      rw [h3]
      exact (IsUnit.mk0 (2 : F) two_ne_zero).map _
    have hxx : x * x = 0 := hu.mul_right_eq_zero.1 h2
    exact IsReduced.eq_zero x ⟨2, by rw [pow_two, hxx]⟩
  let b := Module.finBasisOfFinrankEq F E L.rank
  have hsc : ∀ i, ∃ c : F, c ≠ 0 ∧ algebraMap F E c * b i ∈ L.O := by
    intro i
    haveI : Algebra.IsAlgebraic 𝒪[F] F := IsLocalization.isAlgebraic F (nonZeroDivisors 𝒪[F])
    haveI : Algebra.IsAlgebraic 𝒪[F] E := Algebra.IsAlgebraic.trans 𝒪[F] F E
    obtain ⟨c, hc, hci⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := 𝒪[F]) (b i)).exists_integral_multiple
    refine ⟨(c : F), by exact_mod_cast hc, (L.O_def _).2 ?_⟩
    rwa [Algebra.smul_def, hA] at hci
  choose c hc0 hcO using hsc
  let φ : 𝒪[F] →+* L.O :=
    (algebraMap 𝒪[F] E).codRestrict L.O (fun a => (L.O_def _).2 isIntegral_algebraMap)
  letI : Algebra 𝒪[F] L.O := φ.toAlgebra
  have hsm : ∀ (a : 𝒪[F]) (x : L.O), ((a • x : L.O) : E) = algebraMap F E (a : F) * x := by
    intro a x
    rw [Algebra.smul_def, Subring.coe_mul, ← hA]
    rfl
  let B : Fin 2 → E := fun i => algebraMap F E (c i) * b i
  let g : L.O →ₗ[𝒪[F]] (Fin 2 → E) :=
    { toFun := fun x i => (x : E) * B i + L.cj ((x : E) * B i)
      map_add' := by
        intro x y
        funext i
        simp only [Subring.coe_add, add_mul, map_add, Pi.add_apply]
        ring
      map_smul' := by
        intro a x
        funext i
        simp only [RingHom.id_apply, Pi.smul_apply]
        rw [hsm, Algebra.smul_def, hA]
        simp only [mul_assoc, hcjA, mul_add] }
  let N : Submodule 𝒪[F] (Fin 2 → E) :=
    Submodule.span 𝒪[F] (Set.range fun i : Fin 2 => Pi.single i (1 : E))
  haveI : IsNoetherian 𝒪[F] N := isNoetherian_span_of_finite 𝒪[F] (Set.finite_range _)
  have hgN : ∀ x, g x ∈ N := by
    intro x
    have hx : ∀ i, ∃ a : 𝒪[F], algebraMap 𝒪[F] E a = (x : E) * B i + L.cj ((x : E) * B i) :=
      fun i => htr _ (L.O.mul_mem x.2 (hcO i))
    choose a ha using hx
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨a, ?_⟩
    show _ = fun j => (x : E) * B j + L.cj ((x : E) * B j)
    funext j
    simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def, ha]
  have hinj : Function.Injective (g.codRestrict N hgN) := by
    intro x y hxy
    have h0 : g x = g y := congrArg Subtype.val hxy
    have hd : ∀ i, ((x : E) - y) * B i + L.cj (((x : E) - y) * B i) = 0 := by
      intro i
      have h := congrFun h0 i
      simp only [g, LinearMap.coe_mk, AddHom.coe_mk] at h
      rw [sub_mul, map_sub]
      linear_combination h
    have hb : ∀ i, ((x : E) - y) * b i + L.cj (((x : E) - y) * b i) = 0 := by
      intro i
      have h := hd i
      simp only [B] at h
      rw [mul_left_comm, hcjA, ← mul_add] at h
      exact ((IsUnit.mk0 _ (hc0 i)).map (algebraMap F E)).mul_right_eq_zero.1 h
    have hall : ∀ w, ((x : E) - y) * w + L.cj (((x : E) - y) * w) = 0 := by
      intro w
      let τ : E →ₗ[F] E := LinearMap.mulLeft F ((x : E) - y) +
        (L.cj.toLinearMap).comp (LinearMap.mulLeft F ((x : E) - y))
      have hτ : τ = 0 := b.ext (fun i => by simpa [τ] using hb i)
      simpa [τ] using LinearMap.congr_fun hτ w
    exact Subtype.ext (sub_eq_zero.1 (hnd _ hall))
  haveI : IsNoetherian 𝒪[F] L.O := isNoetherian_of_injective (g.codRestrict N hgN) hinj
  exact isNoetherianRing_iff.2 (isNoetherian_of_tower 𝒪[F] this)

/- English proof (translation)
Introduce `V _ _ H t ht`. Use `haveI := hM.loc`. Use `haveI := hM.char0`. Use `haveI : IsNoetherianRing M.L.O := isNoetherianRing_locE_O' M.L`. Establish `hfg : t.abelian₂.FG` using `ht.1.1.1`.

Use `haveI : IsNoetherian M.L.O t.abelian₂ := isNoetherian_of_fg_of_noetherian _ hfg`. Establish `hle : ThL H t ≤ t.abelian₂` using `inf_le_left`. Use `haveI := isNoetherian_of_le hle`. Conclude with `Module.Finite.iff_fg.1 inferInstance`.
-/
theorem thFG_at (M : Model F E) (r : ℕ) (hM : M.OK) : ThFG M r := by
  intro V _ _ H t ht
  haveI := hM.loc
  haveI := hM.char0
  haveI : IsNoetherianRing M.L.O := isNoetherianRing_locE_O' M.L
  have hfg : t.abelian₂.FG := ht.1.1.1
  haveI : IsNoetherian M.L.O t.abelian₂ := isNoetherian_of_fg_of_noetherian _ hfg
  have hle : ThL H t ≤ t.abelian₂ := inf_le_left
  haveI := isNoetherian_of_le hle
  exact Module.Finite.iff_fg.1 inferInstance

end FG

end Formalism.L2.SG.LsDatumA
