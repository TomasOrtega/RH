import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrLink
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WittExtensionTheorem
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.TermTiesEmptyOfLargeIndex

noncomputable section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.St.WittT

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Witt

variable {D : D7}

abbrev Ix (D : D7) : Type := Fin D.R.rS ⊕ (Fin D.R.rS ⊕ Unit)

def mkFr (e f : Fin D.R.rS → (VS D).V) (z : (VS D).V) : Ix D → (VS D).V
  | Sum.inl a => e a
  | Sum.inr (Sum.inl a) => f a
  | Sum.inr (Sum.inr _) => z

def gstd (T : D.host.E) : Ix D → Ix D → D.host.E
  | Sum.inl a, Sum.inr (Sum.inl b) => if a = b then 1 else 0
  | Sum.inr (Sum.inl a), Sum.inl b => if a = b then 1 else 0
  | Sum.inr (Sum.inr _), Sum.inr (Sum.inr _) => -T
  | _, _ => 0

def swp : Ix D → Ix D
  | Sum.inl a => Sum.inr (Sum.inl a)
  | Sum.inr (Sum.inl a) => Sum.inl a
  | Sum.inr (Sum.inr t) => Sum.inr (Sum.inr t)

def cstd (T : D.host.E) : Ix D → D.host.E
  | Sum.inr (Sum.inr _) => -T
  | _ => 1

/- English proof (translation)
Introduce and unpack `(a | a | ⟨⟩) (b | b | ⟨⟩)`. Conclude with `hee a b`. Conclude with `hef a b`. Conclude with `hez a`. Use `show (VS D).hT (f a) (e b) = if a = b then 1 else 0`.

Rewrite using `[← (VS D).herm.eq (e b) (f a), hef b a]`. Distinguish the cases in `h : a = b`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h, Ne.symm h]`.

Conclude with `hff a b`. Conclude with `hfz a`. Use `show (VS D).hT z (e b) = 0`. Rewrite using `[← (VS D).herm.eq (e b) z, hez b, map_zero]`. Use `show (VS D).hT z (f b) = 0`.

Rewrite using `[← (VS D).herm.eq (f b) z, hfz b, map_zero]`. Conclude with `hzz`.
-/
theorem gram_mkFr (e f : Fin D.R.rS → (VS D).V) (z : (VS D).V) (T : D.host.E)
    (hee : ∀ a b, (VS D).hT (e a) (e b) = 0) (hff : ∀ a b, (VS D).hT (f a) (f b) = 0)
    (hef : ∀ a b, (VS D).hT (e a) (f b) = if a = b then 1 else 0)
    (hez : ∀ a, (VS D).hT (e a) z = 0) (hfz : ∀ a, (VS D).hT (f a) z = 0) (hzz : (VS D).hT z z = -T) :
    ∀ i j, (VS D).hT (mkFr e f z i) (mkFr e f z j) = gstd T i j := by
  rintro (a | a | ⟨⟩) (b | b | ⟨⟩)
  · exact hee a b
  · exact hef a b
  · exact hez a
  · show (VS D).hT (f a) (e b) = if a = b then 1 else 0
    rw [← (VS D).herm.eq (e b) (f a), hef b a]
    by_cases h : a = b
    · subst h; simp
    · simp [h, Ne.symm h]
  · exact hff a b
  · exact hfz a
  · show (VS D).hT z (e b) = 0
    rw [← (VS D).herm.eq (e b) z, hez b, map_zero]
  · show (VS D).hT z (f b) = 0
    rw [← (VS D).herm.eq (f b) z, hfz b, map_zero]
  · exact hzz

/- English proof (translation)
Apply the tactic sequence `rcases i with a | a | ⟨⟩ <;> rcases j with b | b | ⟨⟩ <;>`. Simplify using `[gstd, swp, cstd, eq_comm]`.
-/
theorem gstd_swp (T : D.host.E) (i j : Ix D) : gstd T (swp j) i = if i = j then cstd T j else 0 := by
  rcases i with a | a | ⟨⟩ <;> rcases j with b | b | ⟨⟩ <;>
    simp [gstd, swp, cstd, eq_comm]

/- English proof (translation)
Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg j`. Establish `h` using `congrArg ((VS D).hT (d j)) hg`. Simplify using `only [map_sum, map_smul, map_zero, hd, smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h`. Conclude with `(mul_eq_zero.1 h).resolve_right (hc j)`.
-/
theorem indep_of_dual {ι : Type} [Fintype ι] [DecidableEq ι] (v d : ι → (VS D).V) (c : ι → D.host.E)
    (hc : ∀ j, c j ≠ 0) (hd : ∀ i j, (VS D).hT (d j) (v i) = if i = j then c j else 0) :
    LinearIndependent D.host.E v := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have h := congrArg ((VS D).hT (d j)) hg
  simp only [map_sum, map_smul, map_zero, hd, smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at h
  exact (mul_eq_zero.1 h).resolve_right (hc j)

/- English proof (translation)
Use `indep_of_dual (mkFr e f z) (fun j => mkFr e f z (swp j)) (cstd T) ?_ ?_` and prove the remaining obligations. Apply the tactic sequence `rintro (a | a | ⟨⟩) <;> simp [cstd, hT]`. Introduce `i j`. Rewrite using `[hG, gstd_swp]`.
-/
theorem indep_mkFr (e f : Fin D.R.rS → (VS D).V) (z : (VS D).V) (T : D.host.E) (hT : T ≠ 0)
    (hG : ∀ i j, (VS D).hT (mkFr e f z i) (mkFr e f z j) = gstd T i j) :
    LinearIndependent D.host.E (mkFr e f z) := by
  refine indep_of_dual (mkFr e f z) (fun j => mkFr e f z (swp j)) (cstd T) ?_ ?_
  · rintro (a | a | ⟨⟩) <;> simp [cstd, hT]
  · intro i j
    rw [hG, gstd_swp]

/- English proof (translation)
Use `set U := Submodule.span D.host.E (Set.range v) with hU`. Set `b : Module.Basis ι D.host.E U` to `Module.Basis.span hv`. Set `f : U →ₗ[D.host.E] (VS D).V` to `Finsupp.linearCombination D.host.E w ∘ₗ (b.repr : U →ₗ[D.host.E] (ι →₀ D.host.E))`. Establish `hfb : ∀ i, f (b i) = w i`. Introduce `i`.

Simplify using `[f, Module.Basis.repr_self, Finsupp.linearCombination_single]`. Establish `hbv : ∀ i, ((b i : U) : (VS D).V) = v i`. Introduce `i`. Conclude with `congrArg Subtype.val (Module.Basis.span_apply hv i)`. Establish `hinj : Function.Injective f`.

Establish `h2 : Function.Injective (Finsupp.linearCombination D.host.E w)` using `hw`. Conclude with `h2.comp b.repr.injective`. Establish `hB : ((VS D).hT.comp f).compl₂ f = ((VS D).hT.comp U.subtype).compl₂ U.subtype`. Use `LinearMap.ext_basis b b fun i j => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.compl₂_apply, LinearMap.comp_apply, hfb, Submodule.subtype_apply, hbv]`.

Conclude with `(hG i j).symm`. Establish `hiso : ∀ x y : U, (VS D).hT (f x) (f y) = (VS D).hT x y`. Introduce `x y`. Establish `h` using `congrArg (fun B => B x y) hB`. Simplify `h` using `only [LinearMap.compl₂_apply, LinearMap.comp_apply, Submodule.subtype_apply]`.

Take `⟨g, hg, hgf⟩` from `_root_.witt_extension_theorem D.host.E (VS D).V (VS D).hT (fun x y => (VS D).herm.eq x y) (fun x hx => (VS D).nondeg.1 x hx) U f hinj hiso`. Use `⟨g, hg, fun i => ?_⟩` and prove the remaining obligations. Establish `h` using `hgf (b i)`. Rewrite `h` using `[hbv, hfb]`. Conclude with `h`.
-/
theorem witt_family {ι : Type} [Fintype ι] [DecidableEq ι] (v w : ι → (VS D).V)
    (hv : LinearIndependent D.host.E v) (hw : LinearIndependent D.host.E w)
    (hG : ∀ i j, (VS D).hT (v i) (v j) = (VS D).hT (w i) (w j)) :
    ∃ g : (VS D).V ≃ₗ[D.host.E] (VS D).V, (∀ x y, (VS D).hT (g x) (g y) = (VS D).hT x y) ∧ ∀ i, g (v i) = w i := by
  set U := Submodule.span D.host.E (Set.range v) with hU
  let b : Module.Basis ι D.host.E U := Module.Basis.span hv
  let f : U →ₗ[D.host.E] (VS D).V :=
    Finsupp.linearCombination D.host.E w ∘ₗ (b.repr : U →ₗ[D.host.E] (ι →₀ D.host.E))
  have hfb : ∀ i, f (b i) = w i := by
    intro i
    simp [f, Module.Basis.repr_self, Finsupp.linearCombination_single]
  have hbv : ∀ i, ((b i : U) : (VS D).V) = v i := by
    intro i
    exact congrArg Subtype.val (Module.Basis.span_apply hv i)
  have hinj : Function.Injective f := by
    have h2 : Function.Injective (Finsupp.linearCombination D.host.E w) := hw
    exact h2.comp b.repr.injective
  have hB : ((VS D).hT.comp f).compl₂ f = ((VS D).hT.comp U.subtype).compl₂ U.subtype := by
    refine LinearMap.ext_basis b b fun i j => ?_
    simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, hfb, Submodule.subtype_apply, hbv]
    exact (hG i j).symm
  have hiso : ∀ x y : U, (VS D).hT (f x) (f y) = (VS D).hT x y := by
    intro x y
    have h := congrArg (fun B => B x y) hB
    simpa only [LinearMap.compl₂_apply, LinearMap.comp_apply, Submodule.subtype_apply] using h
  obtain ⟨g, hg, hgf⟩ := _root_.witt_extension_theorem D.host.E (VS D).V (VS D).hT
    (fun x y => (VS D).herm.eq x y) (fun x hx => (VS D).nondeg.1 x hx) U f hinj hiso
  refine ⟨g, hg, fun i => ?_⟩
  have h := hgf (b i)
  rw [hbv, hfb] at h
  exact h

/- English proof (translation)
Unfold `D7.zmOf`. Rewrite using `[map_smul, ← (VS D).herm.eq D.sp.zm (D.sp.hypF a), (D.sp.hyp_orthz a).2, map_zero, smul_zero]`.
-/
theorem hypF_zmOf (u : D.what₂.Word) (a : Fin D.R.rS) : (VS D).hT (D.sp.hypF a) (D.zmOf u) = 0 := by
  unfold D7.zmOf
  rw [map_smul, ← (VS D).herm.eq D.sp.zm (D.sp.hypF a), (D.sp.hyp_orthz a).2, map_zero, smul_zero]

/- English proof (translation)
Introduce `X u`. Establish `hT : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0` using `Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero`. Establish `hGX` using `gram_mkFr X.eX X.fY (X.zu u) (((D.mem u).A.T : ℕ) : D.host.E) X.ee X.ff X.ef (fun a => (X.zu_orth u a).1) (fun a => (X.zu_orth u a).2) (X.zu_norm u)`. Establish `hGR` using `gram_mkFr D.sp.hypE D.sp.hypF (D.zmOf u) (((D.mem u).A.T : ℕ) : D.host.E) D.sp.hyp_ee D.sp.hyp_ff D.sp.hyp_ef (fun a => (Formalism.MainNotions.S.Inh.tie_flag0 D u).z_orth a) (hypF_zmOf u) (Formalism.MainNotions.S.Inh.tie_zmOf_norm D u)`. Take `⟨g, hg, hgi⟩` from `witt_family (mkFr X.eX X.fY (X.zu u)) (mkFr D.sp.hypE D.sp.hypF (D.zmOf u)) (indep_mkFr _ _ _ _ hT hGX) (indep_mkFr _ _ _ _ hT hGR) (fun i j => by rw [hGX, hGR])`.

Conclude with `⟨g, hg, fun a => hgi (Sum.inl a), fun a => hgi (Sum.inr (Sum.inl a)), hgi (Sum.inr (Sum.inr ()))⟩`.
-/
theorem wittExists_holds (D : D7) : WittExists D := by
  intro X u
  have hT : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero
  have hGX := gram_mkFr X.eX X.fY (X.zu u) (((D.mem u).A.T : ℕ) : D.host.E) X.ee X.ff X.ef
    (fun a => (X.zu_orth u a).1) (fun a => (X.zu_orth u a).2) (X.zu_norm u)
  have hGR := gram_mkFr D.sp.hypE D.sp.hypF (D.zmOf u) (((D.mem u).A.T : ℕ) : D.host.E) D.sp.hyp_ee D.sp.hyp_ff
    D.sp.hyp_ef (fun a => (Formalism.MainNotions.S.Inh.tie_flag0 D u).z_orth a) (hypF_zmOf u) (Formalism.MainNotions.S.Inh.tie_zmOf_norm D u)
  obtain ⟨g, hg, hgi⟩ := witt_family (mkFr X.eX X.fY (X.zu u)) (mkFr D.sp.hypE D.sp.hypF (D.zmOf u))
    (indep_mkFr _ _ _ _ hT hGX) (indep_mkFr _ _ _ _ hT hGR) (fun i j => by rw [hGX, hGR])
  exact ⟨g, hg, fun a => hgi (Sum.inl a), fun a => hgi (Sum.inr (Sum.inl a)), hgi (Sum.inr (Sum.inr ()))⟩

end Witt

/- English proof (translation)
The claim follows from `wittExists_holds`.
-/
theorem wittExists : ∀ D : D7, WittExists D := wittExists_holds

end GlobalTheory.St.WittT

end
