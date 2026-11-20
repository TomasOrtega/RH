import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.H1DimGeAbelianDim
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CechHOneVanishesOnOpenOfIsAffineOpen
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMulTrInv

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.FewEq
open GlobalTheory.AbLaw (rs)

namespace GlobalTheory.CompanionTheory.FewEq.Dep

open GlobalTheory.AbLaw (rs_rs rs_self)

variable {Y : Scheme.{0}}

/- English proof (translation)
The claim follows from `Y.sheaf.existsUnique_gluing' O W (fun a => homOfLE (hO a)) hc s h`.
-/
theorem existsUnique_glue {I : Type} (O : I → Y.Opens) {W : Y.Opens} (hO : ∀ a, O a ≤ W)
    (hc : W ≤ ⨆ a, O a) (s : ∀ a, Γ(Y, O a))
    (h : ∀ a b, rs Y (inf_le_left : O a ⊓ O b ≤ O a) (s a) = rs Y inf_le_right (s b)) :
    ∃! t : Γ(Y, W), ∀ a, rs Y (hO a) t = s a :=
  Y.sheaf.existsUnique_gluing' O W (fun a => homOfLE (hO a)) hc s h

/- English proof (translation)
Establish `hM` using `ReciprocityTheory.ChartRestriction.G.Out.Inh.trivLB_isLB Y`. Set `ch : ∀ W : Y.Opens, GlobalTheory.AbLaw.SecOn (ReciprocityTheory.ChartRestriction.G.Out.Inh.trivLB Y) W ≃ₗ[Γ(Y, W)] Γ(Y, W)` to `fun W => GlobalTheory.AbLaw.SecOn.chart hM PUnit.unit le_top`. Establish `hr : ∀ {W W' : Y.Opens} (h : W' ≤ W) (s : GlobalTheory.AbLaw.SecOn (ReciprocityTheory.ChartRestriction.G.Out.Inh.trivLB Y) W), ch W' (GlobalTheory.AbLaw.SecOn.restrict _ h s) = rs Y h (ch W s)` using `fun {W W'} h s => GlobalTheory.AbLaw.SecOn.chart_restrict hM PUnit.unit le_top h s`. Take `⟨ψ, hψ⟩` from `GlobalTheory.AbLaw.CechOne.cechHOneVanishesOnOpen_of_isAffineOpen hM hU I O hO hc (fun a b => (ch _).symm (φ a b)) (by`. Introduce `a b d W ha hb hd`.

Apply `(ch W).injective` to reduce the goal to its premises. Rewrite using `[map_add, hr, hr, hr]`. Simplify `hφ a b d W ha hb hd)` using `only [LinearEquiv.apply_symm_apply]`. Use `⟨fun a => ch _ (ψ a), fun a b => ?_⟩` and prove the remaining obligations. Establish `h` using `(LinearEquiv.symm_apply_eq _).1 (hψ a b)`.

Rewrite using `[h, map_sub, hr, hr]`.
-/
theorem exists_split {U : Y.Opens} (hU : IsAffineOpen U) {I : Type} (O : I → Y.Opens)
    (hO : ∀ a, O a ≤ U) (hc : U ≤ ⨆ a, O a) (φ : ∀ a b, Γ(Y, O a ⊓ O b))
    (hφ : ∀ a b d (W : Y.Opens) (ha : W ≤ O a) (hb : W ≤ O b) (hd : W ≤ O d),
      rs Y (le_inf ha hb) (φ a b) + rs Y (le_inf hb hd) (φ b d) = rs Y (le_inf ha hd) (φ a d)) :
    ∃ ψ : ∀ a, Γ(Y, O a), ∀ a b,
      φ a b = rs Y inf_le_left (ψ a) - rs Y inf_le_right (ψ b) := by
  have hM := ReciprocityTheory.ChartRestriction.G.Out.Inh.trivLB_isLB Y
  let ch : ∀ W : Y.Opens, GlobalTheory.AbLaw.SecOn (ReciprocityTheory.ChartRestriction.G.Out.Inh.trivLB Y) W ≃ₗ[Γ(Y, W)] Γ(Y, W) :=
    fun W => GlobalTheory.AbLaw.SecOn.chart hM PUnit.unit le_top
  have hr : ∀ {W W' : Y.Opens} (h : W' ≤ W) (s : GlobalTheory.AbLaw.SecOn (ReciprocityTheory.ChartRestriction.G.Out.Inh.trivLB Y) W),
      ch W' (GlobalTheory.AbLaw.SecOn.restrict _ h s) = rs Y h (ch W s) := fun {W W'} h s =>
    GlobalTheory.AbLaw.SecOn.chart_restrict hM PUnit.unit le_top h s
  obtain ⟨ψ, hψ⟩ := GlobalTheory.AbLaw.CechOne.cechHOneVanishesOnOpen_of_isAffineOpen hM hU I O hO hc
    (fun a b => (ch _).symm (φ a b)) (by
      intro a b d W ha hb hd
      apply (ch W).injective
      rw [map_add, hr, hr, hr]
      simpa only [LinearEquiv.apply_symm_apply] using hφ a b d W ha hb hd)
  refine ⟨fun a => ch _ (ψ a), fun a b => ?_⟩
  have h := (LinearEquiv.symm_apply_eq _).1 (hψ a b)
  rw [h, map_sub, hr, hr]

section Pot

variable {A : Type} (V : A → Y.Opens)

/- English proof (translation)
Establish `h` using `congrArg (rs Y (le_inf (le_inf ha hb) hd)) (hα a b d)`. Simplify `h` using `only [map_add, rs_rs]`.
-/
theorem cocycle_on {α : ∀ a b, Γ(Y, V a ⊓ V b)}
    (hα : ∀ a b d, rs Y (le₁₂ V a b d) (α a b) + rs Y (le₂₃ V a b d) (α b d) =
      rs Y (le₁₃ V a b d) (α a d))
    (a b d : A) (W : Y.Opens) (ha : W ≤ V a) (hb : W ≤ V b) (hd : W ≤ V d) :
    rs Y (le_inf ha hb) (α a b) + rs Y (le_inf hb hd) (α b d) = rs Y (le_inf ha hd) (α a d) := by
  have h := congrArg (rs Y (le_inf (le_inf ha hb) hd)) (hα a b d)
  simpa only [map_add, rs_rs] using h

def IsPot (α : ∀ a b, Γ(Y, V a ⊓ V b)) (U : Y.Opens) (p : ∀ a, Γ(Y, U ⊓ V a)) : Prop :=
  ∀ a b (W : Y.Opens) (h : W ≤ U) (ha : W ≤ V a) (hb : W ≤ V b),
    rs Y (le_inf h ha) (p a) - rs Y (le_inf h hb) (p b) = rs Y (le_inf ha hb) (α a b)

/- English proof (translation)
Take `⟨ψ, hψ⟩` from `exists_split hU (fun a => U ⊓ V a) (fun _ => inf_le_left) (GlobalTheory.AbLaw.CechOne.le_iSup_inf (hV.ge.trans' le_top)) (fun a b => rs Y (inf_le_inf inf_le_right inf_le_right) (α a b)) (by`. Introduce `a b d W ha hb hd`. Simplify using `only [rs_rs]`. Conclude with `cocycle_on V hα a b d W (ha.trans inf_le_right) (hb.trans inf_le_right) (hd.trans inf_le_right))`. Use `⟨ψ, fun a b W h ha hb => ?_⟩` and prove the remaining obligations.

Establish `e` using `congrArg (rs Y (le_inf (le_inf h ha) (le_inf h hb))) (hψ a b)`. Simplify using `only [map_sub, rs_rs] at e`. Conclude with `e.symm`.
-/
theorem exists_isPot (hV : ⨆ a, V a = ⊤) {α : ∀ a b, Γ(Y, V a ⊓ V b)}
    (hα : ∀ a b d, rs Y (le₁₂ V a b d) (α a b) + rs Y (le₂₃ V a b d) (α b d) =
      rs Y (le₁₃ V a b d) (α a d))
    {U : Y.Opens} (hU : IsAffineOpen U) : ∃ p, IsPot V α U p := by
  obtain ⟨ψ, hψ⟩ := exists_split hU (fun a => U ⊓ V a) (fun _ => inf_le_left)
    (GlobalTheory.AbLaw.CechOne.le_iSup_inf (hV.ge.trans' le_top))
    (fun a b => rs Y (inf_le_inf inf_le_right inf_le_right) (α a b)) (by
      intro a b d W ha hb hd
      simp only [rs_rs]
      exact cocycle_on V hα a b d W (ha.trans inf_le_right) (hb.trans inf_le_right)
        (hd.trans inf_le_right))
  refine ⟨ψ, fun a b W h ha hb => ?_⟩
  have e := congrArg (rs Y (le_inf (le_inf h ha) (le_inf h hb))) (hψ a b)
  simp only [map_sub, rs_rs] at e
  exact e.symm

variable {V}

/- English proof (translation)
Use `existsUnique_glue (fun a => W ⊓ V a) (fun _ => inf_le_left) (GlobalTheory.AbLaw.CechOne.le_iSup_inf (hV.ge.trans' le_top)) _ fun a b => ?_` and prove the remaining obligations. Establish `hW : W ⊓ V a ⊓ (W ⊓ V b) ≤ W` using `inf_le_left.trans inf_le_left`. Establish `ha : W ⊓ V a ⊓ (W ⊓ V b) ≤ V a` using `inf_le_left.trans inf_le_right`. Establish `hb : W ⊓ V a ⊓ (W ⊓ V b) ≤ V b` using `inf_le_right.trans inf_le_right`. Establish `e1` using `hp a b _ (hW.trans h) ha hb`.

Establish `e2` using `hq a b _ hW ha hb`. Simplify using `only [map_sub, rs_rs]`. Rewrite using `[sub_eq_sub_iff_sub_eq_sub]`. Conclude with `e1.trans e2.symm`.
-/
theorem existsUnique_diff (hV : ⨆ a, V a = ⊤) {α : ∀ a b, Γ(Y, V a ⊓ V b)} {U W : Y.Opens}
    (h : W ≤ U) {p : ∀ a, Γ(Y, U ⊓ V a)} {q : ∀ a, Γ(Y, W ⊓ V a)} (hp : IsPot V α U p)
    (hq : IsPot V α W q) :
    ∃! f : Γ(Y, W), ∀ a, rs Y (inf_le_left : W ⊓ V a ≤ W) f =
      rs Y (inf_le_inf_right _ h) (p a) - q a := by
  refine existsUnique_glue (fun a => W ⊓ V a) (fun _ => inf_le_left)
    (GlobalTheory.AbLaw.CechOne.le_iSup_inf (hV.ge.trans' le_top)) _ fun a b => ?_
  have hW : W ⊓ V a ⊓ (W ⊓ V b) ≤ W := inf_le_left.trans inf_le_left
  have ha : W ⊓ V a ⊓ (W ⊓ V b) ≤ V a := inf_le_left.trans inf_le_right
  have hb : W ⊓ V a ⊓ (W ⊓ V b) ≤ V b := inf_le_right.trans inf_le_right
  have e1 := hp a b _ (hW.trans h) ha hb
  have e2 := hq a b _ hW ha hb
  simp only [map_sub, rs_rs]
  rw [sub_eq_sub_iff_sub_eq_sub]
  exact e1.trans e2.symm

end Pot

section Coh

variable {k : Type} [Field k] (s : Y ⟶ Sp k) {A : Type} {V : A → Y.Opens}

/- English proof (translation)
The claim follows from `(Sec.res s h).commutes c`.
-/
theorem rs_cst {U W : Y.Opens} (h : W ≤ U) (c : k) :
    rs Y h (GlobalTheory.SmallExtLift.cst s U c) = GlobalTheory.SmallExtLift.cst s W c :=
  (Sec.res s h).commutes c

/- English proof (translation)
The claim follows from `Algebra.smul_def (A := Sec s U) c x`.
-/
theorem smul_eq {U : Y.Opens} (c : k) (x : Γ(Y, U)) :
    @HSMul.hSMul k (Sec s U) (Sec s U) _ c x = GlobalTheory.SmallExtLift.cst s U c * x :=
  Algebra.smul_def (A := Sec s U) c x

variable {α : ∀ a b, Γ(Y, V a ⊓ V b)} (hV : ⨆ a, V a = ⊤)
  {P : ∀ T : Y.affineOpens, ∀ a, Γ(Y, T.1 ⊓ V a)} (hP : ∀ T, IsPot V α T.1 (P T))

def diffF (T T' : Y.affineOpens) (h : T'.1 ≤ T.1) : Γ(Y, T'.1) :=
  (existsUnique_diff hV h (hP T) (hP T')).choose

/- English proof (translation)
The claim follows from `(existsUnique_diff hV h (hP T) (hP T')).choose_spec.1 a`.
-/
theorem diffF_spec (T T' : Y.affineOpens) (h : T'.1 ≤ T.1) (a : A) :
    rs Y (inf_le_left : T'.1 ⊓ V a ≤ T'.1) (diffF hV hP T T' h) =
      rs Y (inf_le_inf_right _ h) (P T a) - P T' a :=
  (existsUnique_diff hV h (hP T) (hP T')).choose_spec.1 a

/- English proof (translation)
Use `(existsUnique_diff hV (h'.trans h) (hP T) (hP T'')).unique (existsUnique_diff hV (h'.trans h) (hP T) (hP T'')).choose_spec.1 fun a => ?_` and prove the remaining obligations. Establish `e1` using `congrArg (rs Y (inf_le_inf_right (V a) h')) (diffF_spec hV hP T T' h a)`. Establish `e2` using `diffF_spec hV hP T' T'' h' a`. Simplify using `only [map_sub, rs_rs] at e1`. Rewrite using `[map_add, rs_rs, e2]`.

Rewrite using `[show rs Y _ (diffF hV hP T T' h) = _ from e1]`. Normalize the expressions using the abelian group laws.
-/
theorem diffF_comp (T T' T'' : Y.affineOpens) (h : T'.1 ≤ T.1) (h' : T''.1 ≤ T'.1) :
    diffF hV hP T T'' (h'.trans h) = rs Y h' (diffF hV hP T T' h) + diffF hV hP T' T'' h' := by
  refine (existsUnique_diff hV (h'.trans h) (hP T) (hP T'')).unique
    (existsUnique_diff hV (h'.trans h) (hP T) (hP T'')).choose_spec.1 fun a => ?_
  have e1 := congrArg (rs Y (inf_le_inf_right (V a) h')) (diffF_spec hV hP T T' h a)
  have e2 := diffF_spec hV hP T' T'' h' a
  simp only [map_sub, rs_rs] at e1
  rw [map_add, rs_rs, e2]
  rw [show rs Y _ (diffF hV hP T T' h) = _ from e1]
  abel

def diffZ : CatCoh.Z1 (OAff s) :=
  ⟨fun T T' φ => diffF hV hP T.unop T'.unop (leOfHom φ.unop), fun _ _ _ φ ψ =>
    diffF_comp hV hP _ _ _ (leOfHom φ.unop) (leOfHom ψ.unop)⟩

end Coh

end GlobalTheory.CompanionTheory.FewEq.Dep

namespace GlobalTheory.CompanionTheory.FewEq

open Dep
open GlobalTheory.AbLaw (rs_rs rs_self)

/- English proof (translation)
Introduce `k _ Y s₀ hsep n r hfin hle hnr A V hV hVa α hα`. Establish `hex` using `fun (i : Fin r) (T : Y.affineOpens) => exists_isPot V hV (hα i) T.2`. Use `choose p hp using hex`. Set `f : Fin r → CatCoh.Z1 (OAff s₀)` to `fun i => diffZ s₀ hV (hp i)`. Establish `hnot : ¬ LinearIndependent k (fun i => CatCoh.H1.mk (OAff s₀) (f i))` using `fun hli => by`.

Establish `: r ≤ Module.finrank k (HO1 s₀)` using `(Fintype.card_fin r).symm.le.trans hli.fintype_card_le_finrank`. Use linear arithmetic over natural numbers and integers. Take `⟨c, hc, i₀, hi₀⟩` from `Fintype.not_linearIndependent_iff.1 hnot`. Establish `h0 : CatCoh.H1.mk (OAff s₀) (∑ i, c i • f i) = 0`. Rewrite using `[map_sum]`.

Simplify `hc` using `only [map_smul]`. Take `⟨g, hg⟩` from `CatCoh.H1.mk_eq_zero.1 h0`. Choose the witnesses or unpack the hypotheses as in `⟨G, hG⟩ : ∃ G : ∀ T : Y.affineOpens, Γ(Y, T.1), ∀ (T T' : Y.affineOpens) (h : T'.1 ≤ T.1), G T' - rs Y h (G T) = ∑ i, GlobalTheory.SmallExtLift.cst s₀ _ (c i) * diffF hV (hp i) T T' h := by`. Use `⟨fun T => g (Opposite.op T), fun T T' h => ?_⟩` and prove the remaining obligations. Establish `e` using `congrFun (congrFun (congrFun hg (Opposite.op T)) (Opposite.op T')) (homOfLE (show T' ≤ T from h)).op`.

Set `ev : CatCoh.Z1 (OAff s₀) →+ Γ(Y, T'.1)` to `{ toFun := fun z => z.1 (Opposite.op T) (Opposite.op T') (homOfLE (show T' ≤ T from h)).op map_zero' := rfl map_add' := fun _ _ => rfl }`. Conclude with `e.trans ((map_sum ev (fun i => c i • f i) Finset.univ).trans (Finset.sum_congr rfl fun i _ => smul_eq s₀ (c i) _))`. Set `P : ∀ T : Y.affineOpens, ∀ a, Γ(Y, T.1 ⊓ V a)` to `fun T a => ∑ i, GlobalTheory.SmallExtLift.cst s₀ _ (c i) * p i T a + rs Y inf_le_left (G T)`. Establish `hPot : ∀ (T : Y.affineOpens) (a b : A) (W : Y.Opens) (h : W ≤ T.1) (ha : W ≤ V a) (hb : W ≤ V b), rs Y (le_inf h ha) (P T a) - rs Y (le_inf h hb) (P T b) = rs Y (le_inf ha hb) (∑ i, GlobalTheory.SmallExtLift.cst s₀ _ (c i) * α i a b)`. Introduce `T a b W h ha hb`.

Simplify using `only [P, map_add, map_sum, map_mul, rs_rs, rs_cst]`. Simplify using `only [← hp _ T a b W h ha hb, mul_sub, Finset.sum_sub_distrib]`. Expand and normalize the polynomial expressions, which then agree. Establish `hPres : ∀ (T T' : Y.affineOpens) (h : T'.1 ≤ T.1) (a : A), rs Y (inf_le_inf_right _ h) (P T a) = P T' a`. Introduce `T T' h a`.

Establish `e` using `congrArg (rs Y (inf_le_left : T'.1 ⊓ V a ≤ T'.1)) (hG T T' h)`. Simplify using `only [map_sub, map_sum, map_mul, rs_rs, rs_cst, diffF_spec, mul_sub, Finset.sum_sub_distrib] at e`. Simplify using `only [P, map_add, map_sum, map_mul, rs_rs, rs_cst]`. Take the linear combination `-e`. Use `⟨c, fun a => rs Y (le_inf le_rfl le_rfl) (P ⟨V a, hVa a⟩ a), fun h => hi₀ (by rw [h]; rfl), fun a b => ?_⟩` and prove the remaining obligations.

Set `T' : Y.affineOpens` to `⟨V a ⊓ V b, IsAffineOpen.inf (hVa a) (hVa b)⟩`. Establish `e` using `hPot T' a b T'.1 le_rfl inf_le_left inf_le_right`. Rewrite `e` using `[← hPres ⟨V a, hVa a⟩ T' inf_le_left a, ← hPres ⟨V b, hVa b⟩ T' inf_le_right b]`. Simplify using `only [rs_rs] at e ⊢`. Rewrite `e` using `[rs_self]`.

Conclude with `e.symm`.
-/
theorem depSt : DepSt := by
  intro k _ Y s₀ hsep n r hfin hle hnr A V hV hVa α hα
  have hex := fun (i : Fin r) (T : Y.affineOpens) => exists_isPot V hV (hα i) T.2
  choose p hp using hex
  let f : Fin r → CatCoh.Z1 (OAff s₀) := fun i => diffZ s₀ hV (hp i)
  have hnot : ¬ LinearIndependent k (fun i => CatCoh.H1.mk (OAff s₀) (f i)) := fun hli => by
    have : r ≤ Module.finrank k (HO1 s₀) :=
      (Fintype.card_fin r).symm.le.trans hli.fintype_card_le_finrank
    omega
  obtain ⟨c, hc, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.1 hnot
  have h0 : CatCoh.H1.mk (OAff s₀) (∑ i, c i • f i) = 0 := by
    rw [map_sum]
    simpa only [map_smul] using hc
  obtain ⟨g, hg⟩ := CatCoh.H1.mk_eq_zero.1 h0
  obtain ⟨G, hG⟩ : ∃ G : ∀ T : Y.affineOpens, Γ(Y, T.1), ∀ (T T' : Y.affineOpens) (h : T'.1 ≤ T.1),
      G T' - rs Y h (G T) = ∑ i, GlobalTheory.SmallExtLift.cst s₀ _ (c i) * diffF hV (hp i) T T' h := by
    refine ⟨fun T => g (Opposite.op T), fun T T' h => ?_⟩
    have e := congrFun (congrFun (congrFun hg (Opposite.op T)) (Opposite.op T'))
      (homOfLE (show T' ≤ T from h)).op
    let ev : CatCoh.Z1 (OAff s₀) →+ Γ(Y, T'.1) :=
      { toFun := fun z => z.1 (Opposite.op T) (Opposite.op T') (homOfLE (show T' ≤ T from h)).op
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    exact e.trans ((map_sum ev (fun i => c i • f i) Finset.univ).trans
      (Finset.sum_congr rfl fun i _ => smul_eq s₀ (c i) _))
  let P : ∀ T : Y.affineOpens, ∀ a, Γ(Y, T.1 ⊓ V a) := fun T a =>
    ∑ i, GlobalTheory.SmallExtLift.cst s₀ _ (c i) * p i T a + rs Y inf_le_left (G T)
  have hPot : ∀ (T : Y.affineOpens) (a b : A) (W : Y.Opens) (h : W ≤ T.1) (ha : W ≤ V a)
      (hb : W ≤ V b), rs Y (le_inf h ha) (P T a) - rs Y (le_inf h hb) (P T b) =
        rs Y (le_inf ha hb) (∑ i, GlobalTheory.SmallExtLift.cst s₀ _ (c i) * α i a b) := by
    intro T a b W h ha hb
    simp only [P, map_add, map_sum, map_mul, rs_rs, rs_cst]
    simp only [← hp _ T a b W h ha hb, mul_sub, Finset.sum_sub_distrib]
    ring
  have hPres : ∀ (T T' : Y.affineOpens) (h : T'.1 ≤ T.1) (a : A),
      rs Y (inf_le_inf_right _ h) (P T a) = P T' a := by
    intro T T' h a
    have e := congrArg (rs Y (inf_le_left : T'.1 ⊓ V a ≤ T'.1)) (hG T T' h)
    simp only [map_sub, map_sum, map_mul, rs_rs, rs_cst, diffF_spec, mul_sub,
      Finset.sum_sub_distrib] at e
    simp only [P, map_add, map_sum, map_mul, rs_rs, rs_cst]
    linear_combination -e
  refine ⟨c, fun a => rs Y (le_inf le_rfl le_rfl) (P ⟨V a, hVa a⟩ a),
    fun h => hi₀ (by rw [h]; rfl), fun a b => ?_⟩
  let T' : Y.affineOpens := ⟨V a ⊓ V b, IsAffineOpen.inf (hVa a) (hVa b)⟩
  have e := hPot T' a b T'.1 le_rfl inf_le_left inf_le_right
  rw [← hPres ⟨V a, hVa a⟩ T' inf_le_left a, ← hPres ⟨V b, hVa b⟩ T' inf_le_right b] at e
  simp only [rs_rs] at e ⊢
  rw [rs_self] at e
  exact e.symm

end GlobalTheory.CompanionTheory.FewEq
