import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.FamUnif
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodsExistAffineZeroSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodsOfDeRhamClassesUniqueStatement

set_option autoImplicit false

noncomputable section

open TopologicalSpace Filter Topology
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CatCoh GlobalTheory.PeriodFamily

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer

/- English proof (translation)
Unfold `Charts.perCl`. Rewrite using `[← map_add]`. Use `congr 1`. Use `Subtype.ext ?_` and prove the remaining obligations. Use function extensionality and compare the values at `T T' f`.

Express the relevant statement in the definitionally equal form `algebraMap (Hol F.V) T'.C (r f.deg) = algebraMap (Hol F.V) T'.C (p f.deg) + algebraMap (Hol F.V) T'.C (q f.deg)`. Rewrite using `[h, map_add]`.
-/
theorem perCl_add' {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F)
    (p q r : Λ →+ Hol F.V) (h : ∀ l, r l = p l + q l) : K.perCl r = K.perCl p + K.perCl q := by
  unfold Charts.perCl
  rw [← map_add]
  congr 1
  refine Subtype.ext ?_
  funext T T' f
  change algebraMap (Hol F.V) T'.C (r f.deg) = algebraMap (Hol F.V) T'.C (p f.deg) + algebraMap (Hol F.V) T'.C (q f.deg)
  rw [h, map_add]

/- English proof (translation)
Use `Eq.trans ?_ ((H1.mk K.Oc).map_smul a (K.perZ p))` and prove the remaining obligations. Use `congrArg (H1.mk K.Oc) (Subtype.ext ?_)` and prove the remaining obligations. Use function extensionality and compare the values at `T T' f`. Express the relevant statement in the definitionally equal form `algebraMap (Hol F.V) T'.C (r f.deg) = a • algebraMap (Hol F.V) T'.C (p f.deg)`. Rewrite using `[h, map_mul, Algebra.smul_def]`.
-/
theorem perCl_smul' {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F)
    (a : Hol F.V) (p r : Λ →+ Hol F.V) (h : ∀ l, r l = a * p l) : K.perCl r = a • K.perCl p := by
  refine Eq.trans ?_ ((H1.mk K.Oc).map_smul a (K.perZ p))
  refine congrArg (H1.mk K.Oc) (Subtype.ext ?_)
  funext T T' f
  change algebraMap (Hol F.V) T'.C (r f.deg) = a • algebraMap (Hol F.V) T'.C (p f.deg)
  rw [h, map_mul, Algebra.smul_def]

/- English proof (translation)
The claim follows from `Hol.ext_fn fun p hp ↦ by rw [Hol.fn_algebraMap _ hp, Subsingleton.elim p 0]`.
-/
theorem hol_point (f : Hol (⊤ : Opens (Empty → ℂ))) : algebraMap ℂ _ (f.fn 0) = f :=
  Hol.ext_fn fun p hp ↦ by rw [Hol.fn_algebraMap _ hp, Subsingleton.elim p 0]

/- English proof (translation)
Introduce `A _ g hA L u`. Establish `: IsProper A.hom` using `hA.proper`. Establish `: IsSeparated (A.hom ≫ 𝟙 _)` using `inferInstance`. Establish `hB : (fibUnif u).Based`. Set `f : Sp ℂ ⟶ A.left` to `(u.ex 0).left`.

Establish `hs : Subsingleton (Sp ℂ)` using `inferInstanceAs (Subsingleton (PrimeSpectrum ℂ))`. Set `pt : Sp ℂ` to `(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)`. Take `⟨_, ⟨U, hU, rfl⟩, hx, -⟩` from `(A.left.isBasis_affineOpens).exists_subset_of_mem_open (Set.mem_univ (f pt)) isOpen_univ`. Use `⟨U, hU, fun z _ q _ ↦ ?_⟩` and prove the remaining obligations. Rewrite using `[Subsingleton.elim q pt]`.

Conclude with `hx`. Use `choose per hper using fun c : primDR A ↦ hE _ _ _ _ _ _ _ _ (fibUnif u) hB c.1`. Establish `hadd : ∀ c c' : primDR A, per (c + c') = per c + per c'` using `fun c c' ↦ hU _ _ _ _ _ _ _ _ (fibUnif u) _ _ _ (hper (c + c')) fun K r hr ↦ by`. Rewrite using `[perCl_add' K (per c) (per c') _ fun _ ↦ rfl, ← hper c K r hr, ← hper c' K r hr, ← map_add]`. Both sides reduce to the same expression.

Establish `hsmul : ∀ (a : ℂ) (c : primDR A), per (a • c) = (AddMonoidHom.mulLeft (algebraMap ℂ (Hol (fibFam u).V) a)).comp (per c)` using `fun a c ↦ hU _ _ _ _ _ _ _ _ (fibUnif u) _ _ _ (hper (a • c)) fun K r hr ↦ by`. Rewrite using `[perCl_smul' K (algebraMap ℂ (Hol (fibFam u).V) a) (per c) _ fun _ ↦ rfl, ← hper c K r hr, ← map_smulₛₗ]`. Both sides reduce to the same expression. Set `ev : Hol (fibFam u).V →ₐ[ℂ] ℂ` to `Hol.ev 0 trivial`. Use `⟨{ toFun x := { toFun c := ev (per c x) map_add' c c' := by rw [hadd, AddMonoidHom.add_apply, map_add] map_smul' a c := by` and prove the remaining obligations.

Rewrite using `[hsmul]`. Express the relevant statement in the definitionally equal form `ev (algebraMap ℂ _ a * per c x) = a * _`. Rewrite using `[map_mul, AlgHom.commutes]`. Use `rfl }`. Use the proof step `map_zero' := LinearMap.ext fun c ↦ by`.

Express the relevant statement in the definitionally equal form `ev (per c 0) = 0`. Rewrite using `[map_zero, map_zero]`. Use the proof step `map_add' x y := LinearMap.ext fun c ↦ by`. Express the relevant statement in the definitionally equal form `ev (per c (x + y)) = ev (per c x) + ev (per c y)`. Rewrite using `[map_add, map_add] }, fun c ↦ ?_⟩`.

Use `hper c using 1` and compare the differences between its conclusion and the goal. Use `AddMonoidHom.ext fun x ↦ ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `algebraMap ℂ (Hol (fibFam u).V) (ev (per c x)) = per c x`. Conclude with `(congrArg _ (Hol.ev_apply (W := (fibFam u).V) 0 trivial (per c x))).trans (hol_point _)`.
-/
theorem pHom_of (hE : PExist) (hU : PUniq) : PHom := by
  intro A _ g hA L u
  have : IsProper A.hom := hA.proper
  have : IsSeparated (A.hom ≫ 𝟙 _) := inferInstance
  have hB : (fibUnif u).Based := by
    let f : Sp ℂ ⟶ A.left := (u.ex 0).left
    have hs : Subsingleton (Sp ℂ) := inferInstanceAs (Subsingleton (PrimeSpectrum ℂ))
    let pt : Sp ℂ := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
    obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ := (A.left.isBasis_affineOpens).exists_subset_of_mem_open
      (Set.mem_univ (f pt)) isOpen_univ
    refine ⟨U, hU, fun z _ q _ ↦ ?_⟩
    rw [Subsingleton.elim q pt]
    exact hx
  choose per hper using fun c : primDR A ↦ hE _ _ _ _ _ _ _ _ (fibUnif u) hB c.1
  have hadd : ∀ c c' : primDR A, per (c + c') = per c + per c' := fun c c' ↦
    hU _ _ _ _ _ _ _ _ (fibUnif u) _ _ _ (hper (c + c')) fun K r hr ↦ by
      rw [perCl_add' K (per c) (per c') _ fun _ ↦ rfl, ← hper c K r hr, ← hper c' K r hr, ← map_add]
      rfl
  have hsmul : ∀ (a : ℂ) (c : primDR A), per (a • c) =
      (AddMonoidHom.mulLeft (algebraMap ℂ (Hol (fibFam u).V) a)).comp (per c) := fun a c ↦
    hU _ _ _ _ _ _ _ _ (fibUnif u) _ _ _ (hper (a • c)) fun K r hr ↦ by
      rw [perCl_smul' K (algebraMap ℂ (Hol (fibFam u).V) a) (per c) _ fun _ ↦ rfl, ← hper c K r hr, ← map_smulₛₗ]
      rfl
  let ev : Hol (fibFam u).V →ₐ[ℂ] ℂ := Hol.ev 0 trivial
  refine ⟨{ toFun x :=
              { toFun c := ev (per c x)
                map_add' c c' := by rw [hadd, AddMonoidHom.add_apply, map_add]
                map_smul' a c := by
                  rw [hsmul]
                  change ev (algebraMap ℂ _ a * per c x) = a * _
                  rw [map_mul, AlgHom.commutes]; rfl }
            map_zero' := LinearMap.ext fun c ↦ by
              change ev (per c 0) = 0
              rw [map_zero, map_zero]
            map_add' x y := LinearMap.ext fun c ↦ by
              change ev (per c (x + y)) = ev (per c x) + ev (per c y)
              rw [map_add, map_add] }, fun c ↦ ?_⟩
  convert hper c using 1
  refine AddMonoidHom.ext fun x ↦ ?_
  change algebraMap ℂ (Hol (fibFam u).V) (ev (per c x)) = per c x
  exact (congrArg _ (Hol.ev_apply (W := (fibFam u).V) 0 trivial (per c x))).trans (hol_point _)

/- English proof (translation)
The claim follows from `pHom_of GlobalTheory.T.periods_exist_affine_zero_section GlobalTheory.T.periods_of_deRham_classes_unique`.
-/
theorem pHom : PHom := pHom_of GlobalTheory.T.periods_exist_affine_zero_section GlobalTheory.T.periods_of_deRham_classes_unique

end GlobalTheory.AnPer
