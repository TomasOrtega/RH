import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkStepMono
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchubertCellOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPointInSomeCell
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMulApplyEqZeroOfMinor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqFlagPtOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionCellFlAlt
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.FlagZ
set_option autoImplicit false

noncomputable section

open TopologicalSpace Opposite
open GlobalTheory.LB (exists_fun_of_cover)
open GlobalTheory.Twist (resM resM_resM resM_smul app_resM sec_ext_of_cover)

namespace GlobalTheory.VB

variable {X : Scheme.{0}}

/- English proof (translation)
Use `fun V h => ⟨inj V h, fun s => ?_⟩` and prove the remaining obligations. Use `choose W hW hx a ha using fun x : V => loc V h s x x.2`. Establish `hc : V ≤ iSup W` using `fun x hxV => Opens.mem_iSup.2 ⟨⟨x, hxV⟩, hx _⟩`. Establish `key (x y : V) : (fun i => resG X (inf_le_left : W x ⊓ W y ≤ W x) (a x i)) = fun i => resG X (inf_le_right : W x ⊓ W y ≤ W y) (a y i)`. Apply `inj _ (inf_le_left.trans ((hW x).trans h))` to reduce the goal to its premises.

Rewrite using `[← resM_linearCombination e ((hW x).trans h), ← resM_linearCombination e ((hW y).trans h), ha, ha, resM_resM, resM_resM]`. Use `choose b hb' using fun i => exists_fun_of_cover W hW hc (fun x => a x i) fun x y => congrFun (key x y) i`. Use `⟨b, sec_ext_of_cover W hW hc fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[resM_linearCombination, ← ha x]`. Conclude with `congrArg _ (funext fun i => hb' i x)`.
-/
theorem isFrame_of_injective_of_local {F : X.Modules} {U : X.Opens} {ι : Type} [Fintype ι]
    {e : ι → Γ(F, U)}
    (inj : ∀ (V : X.Opens) (h : V ≤ U),
      Function.Injective (Fintype.linearCombination Γ(X, V) fun i => resM F h (e i)))
    (loc : ∀ (V : X.Opens) (h : V ≤ U) (s : Γ(F, V)) (x : X), x ∈ V →
      ∃ (W : X.Opens) (h' : W ≤ V), x ∈ W ∧ ∃ a : ι → Γ(X, W),
        Fintype.linearCombination Γ(X, W) (fun i => resM F (h'.trans h) (e i)) a = resM F h' s) :
    IsFrame e := by
  refine fun V h => ⟨inj V h, fun s => ?_⟩
  choose W hW hx a ha using fun x : V => loc V h s x x.2
  have hc : V ≤ iSup W := fun x hxV => Opens.mem_iSup.2 ⟨⟨x, hxV⟩, hx _⟩
  have key (x y : V) : (fun i => resG X (inf_le_left : W x ⊓ W y ≤ W x) (a x i)) =
      fun i => resG X (inf_le_right : W x ⊓ W y ≤ W y) (a y i) := by
    apply inj _ (inf_le_left.trans ((hW x).trans h))
    rw [← resM_linearCombination e ((hW x).trans h), ← resM_linearCombination e ((hW y).trans h),
      ha, ha, resM_resM, resM_resM]
  choose b hb' using fun i => exists_fun_of_cover W hW hc (fun x => a x i)
    fun x y => congrFun (key x y) i
  refine ⟨b, sec_ext_of_cover W hW hc fun x => ?_⟩
  rw [resM_linearCombination, ← ha x]
  exact congrArg _ (funext fun i => hb' i x)

/- English proof (translation)
Establish `hex (V : X.Opens)` using `GlobalTheory.QCoh.exact_app_of_exact_of_mono (ShortComplex.exact_cokernel i) V`. Establish `hzero (V : X.Opens) (h : V ≤ U) (j : Fin l) : (cokernel.π i).app V (resM E h (e (Fin.castAdd m j))) = 0`. Rewrite using `[← hi, ← app_resM]`. Conclude with `(hex V _).2 ⟨_, rfl⟩`. Use `isFrame_of_injective_of_local (fun V h => ?_) (fun V h s x hx => ?_)` and prove the remaining obligations.

Use `(injective_iff_map_eq_zero _).2 fun a ha => ?_` and prove the remaining obligations. Simplify using `only [Fintype.linearCombination_apply, ← app_resM, ← Scheme.Modules.Hom.app_smul, ← map_sum] at ha`. Take `⟨g, hg⟩` from `((hex V _).1 ha)`. Take `⟨b, rfl⟩` from `(hf V h).2 g`. Simplify using `only [Fintype.linearCombination_apply, map_sum, Scheme.Modules.Hom.app_smul, app_resM, hi] at hg`.

Establish `h0 : Fintype.linearCombination Γ(X, V) (fun j => resM E h (e j)) (Fin.append (-b) a) = 0`. Rewrite using `[Fintype.linearCombination_apply, Fin.sum_univ_add]`. Simplify using `only [Fin.append_left, Fin.append_right, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, hg, neg_add_cancel]`. Establish `h1` using `(he V h).1 (h0.trans (map_zero _).symm)`. Use function extensionality and compare the values at `k`.

Use `congrFun h1 (Fin.natAdd l k)` as an intermediate fact. Rewrite `this` using `[Fin.append_right]`. Then use the resulting hypothesis. Take `⟨W, hWV, hxW, t, ht⟩` from `exists_app_eq_of_epi (cokernel.π i) s hx`. Take `⟨a, rfl⟩` from `(he W (hWV.trans h)).2 t`. Use `⟨W, hWV, hxW, fun k => a (Fin.natAdd l k), ?_⟩` and prove the remaining obligations.

Rewrite using `[← ht, Fintype.linearCombination_apply, Fintype.linearCombination_apply, Fin.sum_univ_add, map_add, map_sum, map_sum]`. Simplify using `only [Scheme.Modules.Hom.app_smul, hzero, smul_zero, Finset.sum_const_zero, zero_add, app_resM]`.
-/
theorem isFrame_cokernel_π {G E : X.Modules} (i : G ⟶ E) [Mono i] {U : X.Opens} {l m : ℕ}
    {e : Fin (l + m) → Γ(E, U)} {f : Fin l → Γ(G, U)} (he : IsFrame e) (hf : IsFrame f)
    (hi : ∀ j, i.app U (f j) = e (Fin.castAdd m j)) :
    IsFrame fun k : Fin m => (cokernel.π i).app U (e (Fin.natAdd l k)) := by
  have hex (V : X.Opens) := GlobalTheory.QCoh.exact_app_of_exact_of_mono (ShortComplex.exact_cokernel i) V

  have hzero (V : X.Opens) (h : V ≤ U) (j : Fin l) :
      (cokernel.π i).app V (resM E h (e (Fin.castAdd m j))) = 0 := by
    rw [← hi, ← app_resM]
    exact (hex V _).2 ⟨_, rfl⟩
  refine isFrame_of_injective_of_local (fun V h => ?_) (fun V h s x hx => ?_)
  · refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
    simp only [Fintype.linearCombination_apply, ← app_resM, ← Scheme.Modules.Hom.app_smul,
      ← map_sum] at ha
    obtain ⟨g, hg⟩ := ((hex V _).1 ha)
    obtain ⟨b, rfl⟩ := (hf V h).2 g
    simp only [Fintype.linearCombination_apply, map_sum, Scheme.Modules.Hom.app_smul,
      app_resM, hi] at hg
    have h0 : Fintype.linearCombination Γ(X, V) (fun j => resM E h (e j))
        (Fin.append (-b) a) = 0 := by
      rw [Fintype.linearCombination_apply, Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, Pi.neg_apply, neg_smul,
        Finset.sum_neg_distrib, hg, neg_add_cancel]
    have h1 := (he V h).1 (h0.trans (map_zero _).symm)
    funext k
    have := congrFun h1 (Fin.natAdd l k)
    rwa [Fin.append_right] at this
  · obtain ⟨W, hWV, hxW, t, ht⟩ := exists_app_eq_of_epi (cokernel.π i) s hx
    obtain ⟨a, rfl⟩ := (he W (hWV.trans h)).2 t
    refine ⟨W, hWV, hxW, fun k => a (Fin.natAdd l k), ?_⟩
    rw [← ht, Fintype.linearCombination_apply, Fintype.linearCombination_apply, Fin.sum_univ_add,
      map_add, map_sum, map_sum]
    simp only [Scheme.Modules.Hom.app_smul, hzero, smul_zero, Finset.sum_const_zero, zero_add,
      app_resM]

/- English proof (translation)
Introduce `X G E i n l hl _ H`. Take `⟨m, rfl⟩` from `Nat.exists_eq_add_of_le hl`. Rewrite using `[Nat.add_sub_cancel_left]`. Introduce `x`. Take `⟨U, e, f, hx, he, hf, hi⟩` from `H x`.

Conclude with `⟨U, _, hx, isFrame_cokernel_π i he hf fun j => (hi j).trans (congrArg e (Fin.ext rfl))⟩`.
-/
theorem isVB_cokernel_of_frames : ∀ (X : Scheme.{0}) (G E : X.Modules) (i : G ⟶ E) (n l : ℕ)
    (hl : l ≤ n), Mono i → (∀ x : X, ∃ (U : X.Opens) (e : Fin n → Γ(E, U)) (f : Fin l → Γ(G, U)),
      x ∈ U ∧ GlobalTheory.VB.IsFrame e ∧ GlobalTheory.VB.IsFrame f ∧ ∀ j, i.app U (f j) = e (Fin.castLE hl j)) →
    GlobalTheory.VB.IsVB (cokernel i) (n - l) := by
  intro X G E i n l hl _ H
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hl
  rw [Nat.add_sub_cancel_left]
  intro x
  obtain ⟨U, e, f, hx, he, hf, hi⟩ := H x
  exact ⟨U, _, hx, isFrame_cokernel_π i he hf fun j => (hi j).trans (congrArg e (Fin.ext rfl))⟩

end GlobalTheory.VB
