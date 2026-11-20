import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.WtPart

section Alg
variable {A R X : Type} [CommRing A] [CommRing R] [AddCommGroup X]
  {f : A →+* R} {m : Multiplicative X →* R}
  (hb : Function.Bijective (AddMonoidAlgebra.liftNCRingHom f m (fun _ _ => Commute.all _ _)))

def cf (χ : X) (s : R) : A := ((Equiv.ofBijective _ hb).symm s).coeff χ

/- English proof (translation)
The claim follows from `congrArg (fun a : AddMonoidAlgebra A X => a.coeff χ) ((Equiv.ofBijective _ hb).symm_apply_apply a)`.
-/
theorem cf_apply (χ : X) (a : AddMonoidAlgebra A X) :
    cf hb χ (AddMonoidAlgebra.liftNCRingHom f m (fun _ _ => Commute.all _ _) a) = a.coeff χ :=
  congrArg (fun a : AddMonoidAlgebra A X => a.coeff χ) ((Equiv.ofBijective _ hb).symm_apply_apply a)

/- English proof (translation)
Use `cf_apply hb χ 0` as an intermediate fact. Rewrite `this` using `[map_zero]`. Then use the resulting hypothesis.
-/
theorem cf_zero (χ : X) : cf hb χ 0 = 0 := by
  have := cf_apply hb χ 0
  rwa [map_zero] at this

/- English proof (translation)
Take `⟨a, rfl⟩` from `hb.2 s`. Take `⟨b, rfl⟩` from `hb.2 t`. Rewrite using `[← map_add, cf_apply, cf_apply, cf_apply, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]`.
-/
theorem cf_add (χ : X) (s t : R) : cf hb χ (s + t) = cf hb χ s + cf hb χ t := by
  obtain ⟨a, rfl⟩ := hb.2 s
  obtain ⟨b, rfl⟩ := hb.2 t
  rw [← map_add, cf_apply, cf_apply, cf_apply, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]

/- English proof (translation)
The claim follows from `map_sum (AddMonoidHom.mk' (cf hb χ) (cf_add hb χ)) s T`.
-/
theorem cf_sum {K : Type} (χ : X) (T : Finset K) (s : K → R) :
    cf hb χ (∑ i ∈ T, s i) = ∑ i ∈ T, cf hb χ (s i) :=
  map_sum (AddMonoidHom.mk' (cf hb χ) (cf_add hb χ)) s T

open Classical in
/- English proof (translation)
Rewrite using `[← AddMonoidAlgebra.liftNCRingHom_single f m (fun _ _ => Commute.all _ _), cf_apply, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]`.
-/
theorem cf_mono (χ ψ : X) (b : A) :
    cf hb χ (f b * m (Multiplicative.ofAdd ψ)) = if ψ = χ then b else 0 := by
  rw [← AddMonoidAlgebra.liftNCRingHom_single f m (fun _ _ => Commute.all _ _), cf_apply,
    AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

/- English proof (translation)
The claim follows from `(Equiv.ofBijective _ hb).symm.injective (AddMonoidAlgebra.ext (Finsupp.ext h))`.
-/
theorem cf_ext {s t : R} (h : ∀ χ, cf hb χ s = cf hb χ t) : s = t :=
  (Equiv.ofBijective _ hb).symm.injective (AddMonoidAlgebra.ext (Finsupp.ext h))

/- English proof (translation)
The claim follows from `((Equiv.ofBijective _ hb).symm s).coeff.support.finite_toSet.subset fun _ h => Finsupp.mem_support_iff.2 h`.
-/
theorem cf_finite (s : R) : {χ | cf hb χ s ≠ 0}.Finite :=
  ((Equiv.ofBijective _ hb).symm s).coeff.support.finite_toSet.subset
    fun _ h => Finsupp.mem_support_iff.2 h

def part (χ : X) (s : R) : R := f (cf hb χ s) * m (Multiplicative.ofAdd χ)

/- English proof (translation)
Rewrite using `[part, h, map_zero, zero_mul]`.
-/
theorem part_eq_zero {χ : X} {s : R} (h : cf hb χ s = 0) : part hb χ s = 0 := by
  rw [part, h, map_zero, zero_mul]

open Classical in
/- English proof (translation)
Rewrite using `[part, cf_mono]`. Use `split_ifs with h`. Rewrite using `[h]`. Rewrite using `[map_zero, zero_mul]`.
-/
theorem part_mono (χ ψ : X) (b : A) :
    part hb χ (f b * m (Multiplicative.ofAdd ψ)) =
      if ψ = χ then f b * m (Multiplicative.ofAdd ψ) else 0 := by
  rw [part, cf_mono]
  split_ifs with h
  · rw [h]
  · rw [map_zero, zero_mul]

/- English proof (translation)
Take `⟨a, rfl⟩` from `hb.2 s`. Proceed by induction on `a using AddMonoidAlgebra.induction_linear with`. Consider the case `zero => simp only [map_zero, part, cf_zero, zero_mul]`. Consider the case `add x y hx hy`. Simplify using `only [part] at hx hy`.

Simplify using `only [map_add, part, cf_add, add_mul, hx, hy]`. Consider the case `single ψ b`. Take `⟨b', e⟩` from `hσ b ψ`. Rewrite using `[AddMonoidAlgebra.liftNCRingHom_single, e, part_mono, part_mono]`. Use `split_ifs`.

Conclude with `e`. Conclude with `map_zero σ`.
-/
theorem part_map {A' R' : Type} [CommRing A'] [CommRing R'] {f' : A' →+* R'}
    {m' : Multiplicative X →* R'}
    (hb' : Function.Bijective (AddMonoidAlgebra.liftNCRingHom f' m' (fun _ _ => Commute.all _ _)))
    (σ : R →+ R')
    (hσ : ∀ b ψ, ∃ b', σ (f b * m (Multiplicative.ofAdd ψ)) = f' b' * m' (Multiplicative.ofAdd ψ))
    (χ : X) (s : R) : σ (part hb χ s) = part hb' χ (σ s) := by
  obtain ⟨a, rfl⟩ := hb.2 s
  induction a using AddMonoidAlgebra.induction_linear with
  | zero => simp only [map_zero, part, cf_zero, zero_mul]
  | add x y hx hy =>
    simp only [part] at hx hy
    simp only [map_add, part, cf_add, add_mul, hx, hy]
  | single ψ b =>
    obtain ⟨b', e⟩ := hσ b ψ
    rw [AddMonoidAlgebra.liftNCRingHom_single, e, part_mono, part_mono]
    split_ifs
    · exact e
    · exact map_zero σ

/- English proof (translation)
Simplify using `only [Module.Basis.constr_apply, Finsupp.sum, toMul_sum, toMul_zsmul, toMul_ofMul, map_prod, map_zpow, h, mul_zpow, Finset.prod_mul_distrib]`.
-/
theorem constr_rel {K M M' N : Type} [CommGroup M] [CommGroup M'] [CommGroup N]
    (b : Module.Basis K ℤ X) (u : K → M) (u' : K → M') (c : K → N) (σ : M →* M') (τ : N →* M')
    (h : ∀ k, σ (u k) = τ (c k) * u' k) (ψ : X) :
    σ (Additive.toMul (b.constr ℤ (fun k => Additive.ofMul (u k)) ψ)) =
      τ (Additive.toMul (b.constr ℤ (fun k => Additive.ofMul (c k)) ψ)) *
        Additive.toMul (b.constr ℤ (fun k => Additive.ofMul (u' k)) ψ) := by
  simp only [Module.Basis.constr_apply, Finsupp.sum, toMul_sum, toMul_zsmul, toMul_ofMul, map_prod,
    map_zpow, h, mul_zpow, Finset.prod_mul_distrib]

end Alg

/- English proof (translation)
Rewrite using `[← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]`. Both sides reduce to the same expression.
-/
theorem rr {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (a : Γ(X, U)) :
    resG X h₂ (resG X h₁ a) = resG X (h₂.trans h₁) a := by
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
  rfl

/- English proof (translation)
Rewrite using `[← RingHom.comp_apply, ← CommRingCat.hom_comp, ← RingHom.comp_apply, ← CommRingCat.hom_comp, q.naturality]`. Both sides reduce to the same expression.
-/
theorem rapp {X Y : Scheme.{0}} (q : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)) :
    resG Y (q.preimage_mono h) ((q.app U).hom a) = (q.app V).hom (resG X h a) := by
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← RingHom.comp_apply, ← CommRingCat.hom_comp,
    q.naturality]
  rfl

section Datum
variable {S : Scheme.{0}} {E : SplitExt S} {G : Over S} [GrpObj G] (D : E.GtDatum G)

abbrev mono (j : E.ChartIdx) (V : E.B.left.Opens) (h : V ≤ E.chart j) :
    Multiplicative E.X →* Γ(G.left, D.q.left ⁻¹ᵁ V) :=
  (Units.coeHom _).comp (AddMonoidHom.toMultiplicativeLeft
    (E.basis.constr ℤ (fun k => Additive.ofMul
      (res (Scheme.Hom.preimage_mono D.q.left h) (D.u j k)))).toAddMonoidHom)

/- English proof (translation)
Establish `hW' : W ≤ E.chart j ⊓ E.chart j'` using `le_inf hW (h.trans hV)`. Use `⟨_, congrArg Units.val (constr_rel E.basis (fun k => res (Scheme.Hom.preimage_mono D.q.left hV) (D.u j' k)) (fun k => res (Scheme.Hom.preimage_mono D.q.left hW) (D.u j k)) (fun k => res hW' (res (le_inf (inf_le_left.trans (E.chart_le j k)) (inf_le_right.trans (E.chart_le j' k))) …` and prove the remaining obligations. Establish `e` using `congrArg (resG _ (D.q.left.preimage_mono hW')) (congrArg Units.val (D.trans j j' k))`. Rewrite `e` using `[Units.val_mul, map_mul]`. Conclude with `(rr _ _ _).trans ((rr _ _ _).symm.trans (e.trans (congrArg₂ (· * ·) (rapp _ _ _) (rr _ _ _))))`.
-/
theorem res_mono {j j' : E.ChartIdx} {V W : E.B.left.Opens} (hV : V ≤ E.chart j')
    (hW : W ≤ E.chart j) (h : W ≤ V) (ψ : E.X) :
    ∃ c : Γ(E.B.left, W), resG _ (D.q.left.preimage_mono h) (mono D j' V hV (Multiplicative.ofAdd ψ)) =
      (D.q.left.app W).hom c * mono D j W hW (Multiplicative.ofAdd ψ) := by
  have hW' : W ≤ E.chart j ⊓ E.chart j' := le_inf hW (h.trans hV)
  refine ⟨_, congrArg Units.val (constr_rel E.basis
    (fun k => res (Scheme.Hom.preimage_mono D.q.left hV) (D.u j' k))
    (fun k => res (Scheme.Hom.preimage_mono D.q.left hW) (D.u j k))
    (fun k => res hW' (res (le_inf (inf_le_left.trans (E.chart_le j k))
      (inf_le_right.trans (E.chart_le j' k))) ((E.O (E.basis k)).L.g (j k) (j' k))))
    (res (D.q.left.preimage_mono h)) (pullU D.q.left W) (fun k => Units.ext ?_) ψ)⟩
  have e := congrArg (resG _ (D.q.left.preimage_mono hW')) (congrArg Units.val (D.trans j j' k))
  rw [Units.val_mul, map_mul] at e
  exact (rr _ _ _).trans ((rr _ _ _).symm.trans (e.trans (congrArg₂ (· * ·) (rapp _ _ _) (rr _ _ _))))

end Datum

variable {k : Type} [Field k] (Φ : FibPre k) {d : ℕ}

def partSec (φ : (Φ.H d).Sec) (α : Φ.E.X) : (Φ.H d).Sec where
  f l := part (Φ.D.coord (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l)) α (φ.f l)
  compat l l' := by
    let q := Φ.D.q.left
    let I := {W : Φ.E.B.left.affineOpens // W.1 ≤ Φ.N₀.U l ⊓ Φ.N₀.U l'}
    refine Φ.G.left.sheaf.eq_of_locally_eq' (fun W : I => q ⁻¹ᵁ W.1.1) _
      (fun W => homOfLE (q.preimage_mono W.2)) (fun x hx => ?_) _ _ fun W => ?_
    · obtain ⟨W, hW, hxW, hle⟩ := exists_isAffineOpen_mem_and_subset (X := Φ.E.B.left) (x := q x)
        (U := Φ.N₀.U l ⊓ Φ.N₀.U l') hx
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨W, hW⟩, hle⟩, hxW⟩
    have h₁ : W.1.1 ≤ Φ.N₀.U l := W.2.trans inf_le_left
    have h₂ : W.1.1 ≤ Φ.N₀.U l' := W.2.trans inf_le_right
    have hW : W.1.1 ≤ Φ.E.chart (Φ.ch l) := h₁.trans (Φ.le l)
    let w : Γ(Φ.E.B.left, W.1.1) := resG _ W.2 (Φ.N₀.g l l').1 ^ d
    have hw : resG _ (q.preimage_mono W.2) ((Φ.H d).g l l').1 = (q.app W.1.1).hom w := by
      change resG _ (q.preimage_mono W.2) (((pullU q _ (Φ.N₀.g l l')) ^ d).1) = _
      rw [Units.val_pow_eq_pow_val, map_pow, map_pow]
      exact congrArg (· ^ d) (rapp _ _ _)
    have e₁ := part_map (Φ.D.coord (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l))
      (Φ.D.coord (Φ.ch l) W.1.1 W.1.2 hW) (resG _ (q.preimage_mono h₁)).toAddMonoidHom
      (fun b ψ => by
        obtain ⟨c, hc⟩ := res_mono Φ.D (Φ.le l) hW h₁ ψ
        refine ⟨resG _ h₁ b * c, (map_mul (resG _ (q.preimage_mono h₁)) _ _).trans ?_⟩
        rw [hc, rapp, map_mul, _root_.mul_assoc]) α (φ.f l)
    have e₂ := part_map (Φ.D.coord (Φ.ch l') (Φ.N₀.U l') (Φ.aff l') (Φ.le l'))
      (Φ.D.coord (Φ.ch l) W.1.1 W.1.2 hW)
      ((AddMonoidHom.mulLeft ((q.app W.1.1).hom w)).comp (resG _ (q.preimage_mono h₂)).toAddMonoidHom)
      (fun b ψ => by
        obtain ⟨c, hc⟩ := res_mono Φ.D (Φ.le l') hW h₂ ψ
        refine ⟨w * (resG _ h₂ b * c), (congrArg (_ * ·)
          (map_mul (resG _ (q.preimage_mono h₂)) _ _)).trans ?_⟩
        rw [hc, rapp, map_mul, map_mul, _root_.mul_assoc, _root_.mul_assoc]) α (φ.f l')
    have e₃ := congrArg (resG _ (q.preimage_mono W.2)) (φ.compat l l')
    have e₄ : resG _ (q.preimage_mono h₁) (φ.f l) =
        (q.app W.1.1).hom w * resG _ (q.preimage_mono h₂) (φ.f l') :=
      (rr _ _ _).symm.trans (e₃.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) hw (rr _ _ _))))
    refine (rr _ _ _).trans (e₁.trans ((congrArg _ e₄).trans (e₂.symm.trans ?_)))
    exact ((map_mul (resG _ (q.preimage_mono W.2)) _ _).trans (congrArg₂ (· * ·) hw (rr _ _ _))).symm

open Classical in
/- English proof (translation)
The claim follows from `cf_mono (Φ.D.coord (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l)) β α _`.
-/
theorem wt_partSec (φ : (Φ.H d).Sec) (α β : Φ.E.X) (l : Φ.N₀.ι) :
    Φ.wt (partSec Φ φ α) β l = if α = β then Φ.wt φ α l else 0 :=
  cf_mono (Φ.D.coord (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l)) β α _

/- English proof (translation)
Use `⟨?_, fun l => by rw [wt_partSec, if_pos rfl]⟩` and prove the remaining obligations. Introduce and unpack `β ⟨l, hl⟩`. Assume the negation of the conclusion as `h`. Conclude with `hl (by rw [wt_partSec, if_neg (fun e => h e.symm)])`.
-/
theorem isPart_partSec (φ : (Φ.H d).Sec) (α : Φ.E.X) : Φ.IsPart α φ (partSec Φ φ α) := by
  refine ⟨?_, fun l => by rw [wt_partSec, if_pos rfl]⟩
  rintro β ⟨l, hl⟩
  by_contra h
  exact hl (by rw [wt_partSec, if_neg (fun e => h e.symm)])

/- English proof (translation)
Use `Φ.E.isAbelian.proper` as an intermediate fact. Establish `: CompactSpace Φ.E.B.left` using `QuasiCompact.compactSpace_of_compactSpace Φ.E.B.hom`. Take `⟨T, hT⟩` from `isCompact_univ.elim_finite_subcover (fun l => (Φ.N₀.U l : Set Φ.E.B.left)) (fun l => (Φ.N₀.U l).isOpen) (fun x _ => Set.mem_iUnion.2 (TopologicalSpace.Opens.mem_iSup.1 (Φ.isLB.cover.ge (show x ∈ ⊤ from trivial))))`. Use `(T.finite_toSet.biUnion fun l _ => cf_finite (Φ.D.coord (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l)) (φ.f l)).subset ?_` and prove the remaining obligations. Introduce and unpack `α ⟨l', hl'⟩`.

Assume the negation of the conclusion as `hn`. Establish `h0 : ∀ l ∈ T, (partSec Φ φ α).f l = 0` using `fun l hl => by`. Establish `: cf (Φ.D.coord (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l)) α (φ.f l) = 0`. Assume the negation of the conclusion as `h`. Conclude with `hn (Set.mem_biUnion hl h)`.

Conclude with `part_eq_zero _ this`. Establish `h1 : (partSec Φ φ α).f l' = 0`. Use `Φ.G.left.sheaf.eq_of_locally_eq' (fun l : T => (Φ.H d).U l' ⊓ (Φ.H d).U l.1) _ (fun l => homOfLE inf_le_left) (fun x hx => ?_) _ _ fun l => ?_` and prove the remaining obligations. Take `⟨l, hl, hx'⟩` from `Set.mem_iUnion₂.1 (hT (Set.mem_univ (Φ.D.q.left x)))`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨⟨l, hl⟩, hx, hx'⟩`.

Use `((partSec Φ φ α).compat l' l.1).trans ?_` and prove the remaining obligations. Rewrite using `[h0 l.1 l.2, map_zero, mul_zero]`. Conclude with `(map_zero (resG _ _)).symm`. Apply `hl'` to reduce the goal to its premises. Rewrite using `[← (isPart_partSec Φ φ α).2 l', FibPre.wt, h1]`.

Conclude with `cf_zero (Φ.D.coord (Φ.ch l') (Φ.N₀.U l') (Φ.aff l') (Φ.le l')) α`.
-/
theorem supp_finite (φ : (Φ.H d).Sec) : (Φ.supp φ).Finite := by
  have := Φ.E.isAbelian.proper
  have : CompactSpace Φ.E.B.left := QuasiCompact.compactSpace_of_compactSpace Φ.E.B.hom
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun l => (Φ.N₀.U l : Set Φ.E.B.left))
    (fun l => (Φ.N₀.U l).isOpen) (fun x _ => Set.mem_iUnion.2
      (TopologicalSpace.Opens.mem_iSup.1 (Φ.isLB.cover.ge (show x ∈ ⊤ from trivial))))
  refine (T.finite_toSet.biUnion fun l _ =>
    cf_finite (Φ.D.coord (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l)) (φ.f l)).subset ?_
  rintro α ⟨l', hl'⟩
  by_contra hn
  have h0 : ∀ l ∈ T, (partSec Φ φ α).f l = 0 := fun l hl => by
    have : cf (Φ.D.coord (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l)) α (φ.f l) = 0 := by
      by_contra h
      exact hn (Set.mem_biUnion hl h)
    exact part_eq_zero _ this
  have h1 : (partSec Φ φ α).f l' = 0 := by
    refine Φ.G.left.sheaf.eq_of_locally_eq' (fun l : T => (Φ.H d).U l' ⊓ (Φ.H d).U l.1) _
      (fun l => homOfLE inf_le_left) (fun x hx => ?_) _ _ fun l => ?_
    · obtain ⟨l, hl, hx'⟩ := Set.mem_iUnion₂.1 (hT (Set.mem_univ (Φ.D.q.left x)))
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨l, hl⟩, hx, hx'⟩
    · refine ((partSec Φ φ α).compat l' l.1).trans ?_
      rw [h0 l.1 l.2, map_zero, mul_zero]
      exact (map_zero (resG _ _)).symm
  apply hl'
  rw [← (isPart_partSec Φ φ α).2 l', FibPre.wt, h1]
  exact cf_zero (Φ.D.coord (Φ.ch l') (Φ.N₀.U l') (Φ.aff l') (Φ.le l')) α

/- English proof (translation)
Establish `: φ.f = ψ.f` using `funext fun l => cf_ext (Φ.D.coord (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l)) fun α => h α l`. Consider the cases of `φ`. Consider the cases of `ψ`. Reduce the equality to equality of the corresponding arguments.
-/
theorem sec_ext (φ ψ : (Φ.H d).Sec) (h : ∀ α l, Φ.wt φ α l = Φ.wt ψ α l) : φ = ψ := by
  have : φ.f = ψ.f := funext fun l =>
    cf_ext (Φ.D.coord (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l)) fun α => h α l
  cases φ
  cases ψ
  congr

/- English proof (translation)
Use `cf_ext (Φ.D.coord (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l)) fun β => Eq.symm ?_` and prove the remaining obligations. Use `(cf_sum (Φ.D.coord (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l)) β A _).trans ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `∑ α ∈ A, Φ.wt (ψ α) β l = Φ.wt φ β l`. Establish `h0 : ∀ α ∈ A, α ≠ β → Φ.wt (ψ α) β l = 0` using `fun α hα hne => by`. Assume the negation of the conclusion as `h`.

Conclude with `hne ((hψ α hα).1 ⟨l, h⟩).symm`. Distinguish the cases in `hβ : β ∈ A`. Rewrite using `[Finset.sum_eq_single_of_mem β hβ h0, (hψ β hβ).2 l]`. Rewrite using `[Finset.sum_eq_zero fun α hα => h0 α hα fun e => hβ (e ▸ hα)]`. Assume the negation of the conclusion as `h`.

Conclude with `hβ (hA ⟨l, fun e => h e.symm⟩)`.
-/
theorem eq_sum_parts (φ : (Φ.H d).Sec) (A : Finset Φ.E.X) (ψ : Φ.E.X → (Φ.H d).Sec)
    (hA : Φ.supp φ ⊆ A) (hψ : ∀ α ∈ A, Φ.IsPart α φ (ψ α)) (l : Φ.N₀.ι) :
    φ.f l = ∑ α ∈ A, (ψ α).f l := by
  refine cf_ext (Φ.D.coord (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l)) fun β => Eq.symm ?_
  refine (cf_sum (Φ.D.coord (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l)) β A _).trans ?_
  change ∑ α ∈ A, Φ.wt (ψ α) β l = Φ.wt φ β l
  have h0 : ∀ α ∈ A, α ≠ β → Φ.wt (ψ α) β l = 0 := fun α hα hne => by
    by_contra h
    exact hne ((hψ α hα).1 ⟨l, h⟩).symm
  by_cases hβ : β ∈ A
  · rw [Finset.sum_eq_single_of_mem β hβ h0, (hψ β hβ).2 l]
  · rw [Finset.sum_eq_zero fun α hα => h0 α hα fun e => hβ (e ▸ hα)]
    by_contra h
    exact hβ (hA ⟨l, fun e => h e.symm⟩)

/- English proof (translation)
Introduce `_ _ Φ _` and use `⟨fun φ α => ⟨_, isPart_partSec Φ φ α⟩, supp_finite Φ, sec_ext Φ, eq_sum_parts Φ⟩`.
-/
theorem weight_parts : (∀ (k : Type) [Field k] (Φ : FibPre k) (d : ℕ), (∀ (φ : (Φ.H d).Sec) (α : Φ.E.X), ∃ ψ, Φ.IsPart α φ ψ) ∧ (∀ φ : (Φ.H d).Sec, (Φ.supp φ).Finite) ∧ (∀ φ ψ : (Φ.H d).Sec, (∀ α l, Φ.wt φ α l = Φ.wt ψ α l) → φ = ψ) ∧ ∀ (φ : (Φ.H d).Sec) (A : Finset Φ.E.X) (ψ : Φ.E.X → (Φ.H d).Sec), Φ.supp φ ⊆ A → (∀ α ∈ A, Φ.IsPart α φ (ψ α)) → ∀ l, φ.f l = ∑ α ∈ A, (ψ α).f l) :=
  fun _ _ Φ _ => ⟨fun φ α => ⟨_, isPart_partSec Φ φ α⟩, supp_finite Φ, sec_ext Φ, eq_sum_parts Φ⟩

end GlobalTheory.ZH.WtPart
end
