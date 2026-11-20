import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfRingHom
import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVBAndClsDetOfShortExact
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.VB GlobalTheory.Conormal GlobalTheory.LieVB GlobalTheory.SiegelTor
open GlobalTheory.Twist (resM)

namespace GlobalTheory.GtHodge

section Algebra

variable {R A C X : Type} [CommRing R] [CommRing A] [CommRing C] [AddCommGroup X]
  (φ : A →+* C) (v : Multiplicative X →* C)

/- English proof (translation)
Set `e` to `RingEquiv.ofBijective _ hb`. Establish `he (x : X) (a : A) : e (.single x a) = φ a * v (.ofAdd x)` using `AddMonoidAlgebra.liftNCRingHom_single φ v (fun _ _ => Commute.all _ _) x a`. Set `σ` to `AddMonoidAlgebra.liftNCRingHom (RingHom.id A) ((s.comp εC).toMonoidHom.comp v) fun _ _ => Commute.all _ _`. Establish `hσ (x : X) (a : A) : σ (.single x a) = a * s (εC (v (.ofAdd x)))` using `AddMonoidAlgebra.liftNCRingHom_single _ _ (fun _ _ => Commute.all _ _) x a`. Use `⟨σ.comp e.symm.toRingHom, fun a => ?_, fun c => ?_⟩` and prove the remaining obligations.

Establish `: φ a = e (.single 0 a)` using `by simp [he]`. Rewrite using `[this]`. Simplify using `[hσ]`. Take `⟨c, rfl⟩` from `e.surjective c`. Express the relevant statement in the definitionally equal form `εA (σ (e.symm (e c))) = _`.

Rewrite using `[e.symm_apply_apply]`. Proceed by induction on `c using AddMonoidAlgebra.induction_linear with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Consider the case `single x a => rw [hσ, he, map_mul, map_mul, hs, hε]`.
-/
theorem exists_retraction (hb : Function.Bijective
      (AddMonoidAlgebra.liftNCRingHom φ v fun _ _ => Commute.all _ _))
    (s : R →+* A) (εA : A →+* R) (εC : C →+* R) (hs : ∀ r, εA (s r) = r) (hε : ∀ a, εC (φ a) = εA a) :
    ∃ ρ : C →+* A, (∀ a, ρ (φ a) = a) ∧ ∀ c, εA (ρ c) = εC c := by
  let e := RingEquiv.ofBijective _ hb
  have he (x : X) (a : A) : e (.single x a) = φ a * v (.ofAdd x) :=
    AddMonoidAlgebra.liftNCRingHom_single φ v (fun _ _ => Commute.all _ _) x a
  let σ := AddMonoidAlgebra.liftNCRingHom (RingHom.id A)
    ((s.comp εC).toMonoidHom.comp v) fun _ _ => Commute.all _ _
  have hσ (x : X) (a : A) : σ (.single x a) = a * s (εC (v (.ofAdd x))) :=
    AddMonoidAlgebra.liftNCRingHom_single _ _ (fun _ _ => Commute.all _ _) x a
  refine ⟨σ.comp e.symm.toRingHom, fun a => ?_, fun c => ?_⟩
  · have : φ a = e (.single 0 a) := by simp [he]
    rw [this]
    simp [hσ]
  · obtain ⟨c, rfl⟩ := e.surjective c
    change εA (σ (e.symm (e c))) = _
    rw [e.symm_apply_apply]
    induction c using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | single x a => rw [hσ, he, map_mul, map_mul, hs, hε]

/- English proof (translation)
Set `δ : X →+ N` to `AddMonoidHom.mk' (fun x => ε (v (.ofAdd (-x))) • D (v (.ofAdd x))) fun x y => by`. Rewrite using `[ofAdd_add, map_mul v, hD]`. Simplify using `only [smul_add, smul_smul, ← map_mul, ← ofAdd_add]`. Rewrite using `[add_comm (_ • D _)]`. Apply the tactic sequence `congr 5 <;> abel`.

Establish `hδ (x : X) : δ x ∈ p`. Rewrite using `[← b.sum_repr x, map_sum]`. Conclude with `p.sum_mem fun k _ => by`. Rewrite using `[map_zsmul]`. Conclude with `zsmul_mem (p.smul_mem _ (hv k)) _`.

Establish `hx (x : X) : D (v (.ofAdd x)) ∈ p`. Use `p.smul_mem (ε (v (.ofAdd x))) (hδ x)` as an intermediate fact. Simplify `this` using `[δ, smul_smul, ← map_mul]`. Take `⟨c, rfl⟩` from `hb c`. Proceed by induction on `c using AddMonoidAlgebra.induction_linear with`.

Consider the case `zero => simp`. Consider the case `add a b ha hb => rw [map_add, map_add]`. Conclude with `p.add_mem ha hb`. Consider the case `single x a`. Rewrite using `[AddMonoidAlgebra.liftNCRingHom_single, hD]`.

Conclude with `p.add_mem (p.smul_mem _ (hx x)) (p.smul_mem _ (hA a))`.
-/
theorem mem_of_derivation {N κ : Type} [AddCommGroup N] [Module R N] [Fintype κ]
    (b : Module.Basis κ ℤ X) (hb : Function.Surjective
      (AddMonoidAlgebra.liftNCRingHom φ v fun _ _ => Commute.all _ _))
    (ε : C →+* R) (D : C →+ N) (hD : ∀ a c, D (a * c) = ε a • D c + ε c • D a)
    (p : Submodule R N) (hA : ∀ a, D (φ a) ∈ p) (hv : ∀ k, D (v (.ofAdd (b k))) ∈ p) (c : C) :
    D c ∈ p := by
  let δ : X →+ N := AddMonoidHom.mk' (fun x => ε (v (.ofAdd (-x))) • D (v (.ofAdd x))) fun x y => by
    rw [ofAdd_add, map_mul v, hD]
    simp only [smul_add, smul_smul, ← map_mul, ← ofAdd_add]
    rw [add_comm (_ • D _)]
    congr 5 <;> abel
  have hδ (x : X) : δ x ∈ p := by
    rw [← b.sum_repr x, map_sum]
    exact p.sum_mem fun k _ => by
      rw [map_zsmul]
      exact zsmul_mem (p.smul_mem _ (hv k)) _
  have hx (x : X) : D (v (.ofAdd x)) ∈ p := by
    have := p.smul_mem (ε (v (.ofAdd x))) (hδ x)
    simpa [δ, smul_smul, ← map_mul] using this
  obtain ⟨c, rfl⟩ := hb c
  induction c using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add]; exact p.add_mem ha hb
  | single x a =>
    rw [AddMonoidAlgebra.liftNCRingHom_single, hD]
    exact p.add_mem (p.smul_mem _ (hx x)) (p.smul_mem _ (hA a))

/- English proof (translation)
Establish `ht' (k : κ) : g (t k) = c.unitsSMul w k` using `by rw [ht, Module.Basis.unitsSMul_apply]; rfl`. Prove the components needed by the constructor for the conclusion. Introduce `y`. Use `⟨fun hy => ?_, by rintro ⟨x, rfl⟩; exact hfg x⟩` and prove the remaining obligations. Take `⟨_, ⟨x, rfl⟩, z, hz, rfl⟩` from `Submodule.mem_sup.1 (hs y)`.

Take `⟨a, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun R).1 hz`. Use `Fintype.linearIndependent_iff.1 (c.unitsSMul w).linearIndependent a (by simpa [hfg, ht'] using hy)` as an intermediate fact. Conclude with `⟨x, by simp [this]⟩`. Introduce `z`. Use `⟨∑ k, (c.unitsSMul w).repr z k • t k, ?_⟩` and prove the remaining obligations.

Simplify using `only [map_sum, map_smul, ht']`. Conclude with `(c.unitsSMul w).sum_repr z`.
-/
theorem exact_of_span {M N P κ : Type} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P] [Fintype κ] (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hfg : ∀ x, g (f x) = 0) (c : Module.Basis κ R P) (t : κ → N) (w : κ → Rˣ)
    (ht : ∀ k, g (t k) = (w k : R) • c k)
    (hs : ∀ y, y ∈ LinearMap.range f ⊔ Submodule.span R (Set.range t)) :
    Function.Exact f g ∧ Function.Surjective g := by
  have ht' (k : κ) : g (t k) = c.unitsSMul w k := by rw [ht, Module.Basis.unitsSMul_apply]; rfl
  constructor
  · intro y
    refine ⟨fun hy => ?_, by rintro ⟨x, rfl⟩; exact hfg x⟩
    obtain ⟨_, ⟨x, rfl⟩, z, hz, rfl⟩ := Submodule.mem_sup.1 (hs y)
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hz
    have := Fintype.linearIndependent_iff.1 (c.unitsSMul w).linearIndependent a
      (by simpa [hfg, ht'] using hy)
    exact ⟨x, by simp [this]⟩
  · intro z
    refine ⟨∑ k, (c.unitsSMul w).repr z k • t k, ?_⟩
    simp only [map_sum, map_smul, ht']
    exact (c.unitsSMul w).sum_repr z

end Algebra

attribute [local instance] SplitExt.free SplitExt.finite

variable {S : Scheme.{0}}

/- English proof (translation)
The claim follows from `congrArg (·.left) (IsMonHom.one_hom q)`.
-/
theorem unitSec_comp_left {G H : Over S} [GrpObj G] [GrpObj H] (q : G ⟶ H) [IsMonHom q] :
    unitSec G ≫ q.left = unitSec H := congrArg (·.left) (IsMonHom.one_hom q)

/- English proof (translation)
Establish `he` using `sec_hom η[G]`. Use `letI := cG.algebra`. Set `D : Γ(G.left, W) →ₗ[Γ(S, U)] Γ(omega B, U)` to `{ toFun := fun c => dUnit B cB.le (ρ c) map_add' := fun a c => by rw [map_add, map_add] map_smul' := fun r c => by`. Establish `e : ρ (G.hom.appLE U W cG.le_base r) = B.hom.appLE U V cB.le_base r`. Rewrite using `[← appLE_appLE (Over.w q) cB.le_base k, h₁]`.

Express the relevant statement in the definitionally equal form `dUnit B cB.le (ρ (G.hom.appLE U W cG.le_base r * c)) = r • _`. Rewrite using `[map_mul, e, dUnit_mul, dUnit_base, smul_zero, add_zero, appLE_base (sec_hom η[B]) _ _ le_rfl, LB.resG_self] }`. Set `l` to `AugCot.lift (cG.aug he) D (fun a c => by`. Express the relevant statement in the definitionally equal form `dUnit B cB.le (ρ (a * c)) = _`. Rewrite using `[map_mul, dUnit_mul, h₂, h₂]`.

Use the proof step `rfl) ∘ₗ (cG.augCotEquiv he).symm.toLinearMap`. Establish `hl (c : Γ(G.left, W)) : l (dUnit G cG.le c) = dUnit B cB.le (ρ c)`. Use `(congrArg l (cG.augCotEquiv_d he c).symm).trans ?_` and prove the remaining obligations. Simplify using `only [l, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]`. Conclude with `AugCot.lift_d _ _ _ _`.

Use `Function.LeftInverse.injective (g := l) fun x => ?_` and prove the remaining obligations. Take `⟨a, rfl⟩` from `cB.d_surjective (sec_hom η[B]) x`. Conclude with `(congrArg l (omegaMap_dUnit q cB.le cG.le k a)).trans ((hl _).trans (congrArg _ (h₁ a)))`.
-/
theorem injective_omegaMap {G B : Over S} [GrpObj G] [GrpObj B] [QuasiSeparated G.hom]
    [QuasiSeparated B.hom] (q : G ⟶ B) [IsMonHom q] {U : S.Opens} {V : B.left.Opens}
    {W : G.left.Opens} (cB : IsChart B.hom (unitSec B) U V) (cG : IsChart G.hom (unitSec G) U W)
    (k : W ≤ q.left ⁻¹ᵁ V) (ρ : Γ(G.left, W) →+* Γ(B.left, V))
    (h₁ : ∀ a, ρ (q.left.appLE V W k a) = a)
    (h₂ : ∀ c, (unitSec B).appLE V U cB.le (ρ c) = (unitSec G).appLE W U cG.le c) :
    Function.Injective ((omegaMap q).app U) := by
  have he := sec_hom η[G]
  letI := cG.algebra
  let D : Γ(G.left, W) →ₗ[Γ(S, U)] Γ(omega B, U) :=
    { toFun := fun c => dUnit B cB.le (ρ c)
      map_add' := fun a c => by rw [map_add, map_add]
      map_smul' := fun r c => by
        have e : ρ (G.hom.appLE U W cG.le_base r) = B.hom.appLE U V cB.le_base r := by
          rw [← appLE_appLE (Over.w q) cB.le_base k, h₁]
        change dUnit B cB.le (ρ (G.hom.appLE U W cG.le_base r * c)) = r • _
        rw [map_mul, e, dUnit_mul, dUnit_base, smul_zero, add_zero,
          appLE_base (sec_hom η[B]) _ _ le_rfl, LB.resG_self] }
  let l := AugCot.lift (cG.aug he) D (fun a c => by
    change dUnit B cB.le (ρ (a * c)) = _
    rw [map_mul, dUnit_mul, h₂, h₂]; rfl) ∘ₗ (cG.augCotEquiv he).symm.toLinearMap
  have hl (c : Γ(G.left, W)) : l (dUnit G cG.le c) = dUnit B cB.le (ρ c) := by
    refine (congrArg l (cG.augCotEquiv_d he c).symm).trans ?_
    simp only [l, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    exact AugCot.lift_d _ _ _ _
  refine Function.LeftInverse.injective (g := l) fun x => ?_
  obtain ⟨a, rfl⟩ := cB.d_surjective (sec_hom η[B]) x
  exact (congrArg l (omegaMap_dUnit q cB.le cG.le k a)).trans ((hl _).trans (congrArg _ (h₁ a)))

variable {E : SplitExt S} {G : Over S} [GrpObj G] (d : E.GtDatum G)

/- English proof (translation)
Set `T` to `splitTorus S E.X`. Set `m : T ⟶ T ⊗ G` to `lift (𝟙 T) (toUnit T ≫ η)`. Establish `e1 : m.left ≫ (fst T G).left = 𝟙 _` using `by rw [← Over.comp_left, lift_fst]; rfl`. Establish `e2 : m.left ≫ (snd T G).left = T.hom ≫ unitSec G`. Rewrite using `[← Over.comp_left, lift_snd]`.

Both sides reduce to the same expression. Establish `e3 : m.left ≫ (lift (fst T G ≫ d.i) (snd T G) ≫ μ[G]).left = d.i.left`. Rewrite using `[← Over.comp_left, ← Category.assoc, comp_lift, lift_fst_assoc, lift_snd, lift_comp_one_right, Category.id_comp]`. Establish `h₃ : W ≤ (T.hom ≫ unitSec G) ⁻¹ᵁ d.q.left ⁻¹ᵁ E.chart j` using `h₁.trans (T.hom.preimage_mono h₀)`. Establish `hm` using `(le_preimage_of_comp e2).2 h₃`.

Establish `h₂` using `(le_preimage_of_comp e3).1 (hm.trans (m.left.preimage_mono (d.act_le j)))`. Use `⟨h₂, ?_⟩` and prove the remaining obligations. Establish `key` using `congrArg (m.left.appLE _ W hm) (congrArg Units.val (d.equiv j k))`. Rewrite `key` using `[Units.val_mul, map_mul]`. Use `(appLE_appLE e3 (d.act_le j) hm h₂ _).symm.trans (key.trans ?_)` and prove the remaining obligations.

Use `congr 1`. Conclude with `(appLE_appLE e1 (le_preimage_top _ _) hm le_top _).trans (congrArg (resG _ le_top) (SplitTorus.charUnit_val _))`. Use `Eq.trans ?_ ((appLE_appLE e2 le_rfl hm h₃ _).trans (appLE_appLE rfl h₀ h₁ h₃ _).symm)` and prove the remaining obligations. Rewrite using `[Scheme.Hom.appLE_eq_app]`. Both sides reduce to the same expression.
-/
theorem appLE_coord (j : E.ChartIdx) (k : Module.Free.ChooseBasisIndex ℤ E.X) {U : S.Opens}
    {W : (splitTorus S E.X).left.Opens} (h₀ : U ≤ unitSec G ⁻¹ᵁ d.q.left ⁻¹ᵁ E.chart j)
    (h₁ : W ≤ (splitTorus S E.X).hom ⁻¹ᵁ U) :
    ∃ h₂ : W ≤ d.i.left ⁻¹ᵁ d.q.left ⁻¹ᵁ E.chart j, d.i.left.appLE _ W h₂ (d.u j k).val =
      resG _ le_top (Rosenlicht.chi E.X (E.basis k)) *
        (splitTorus S E.X).hom.appLE U W h₁ ((unitSec G).appLE _ U h₀ (d.u j k).val) := by
  let T := splitTorus S E.X
  let m : T ⟶ T ⊗ G := lift (𝟙 T) (toUnit T ≫ η)
  have e1 : m.left ≫ (fst T G).left = 𝟙 _ := by rw [← Over.comp_left, lift_fst]; rfl
  have e2 : m.left ≫ (snd T G).left = T.hom ≫ unitSec G := by
    rw [← Over.comp_left, lift_snd]; rfl
  have e3 : m.left ≫ (lift (fst T G ≫ d.i) (snd T G) ≫ μ[G]).left = d.i.left := by
    rw [← Over.comp_left, ← Category.assoc, comp_lift, lift_fst_assoc, lift_snd,
      lift_comp_one_right, Category.id_comp]
  have h₃ : W ≤ (T.hom ≫ unitSec G) ⁻¹ᵁ d.q.left ⁻¹ᵁ E.chart j := h₁.trans (T.hom.preimage_mono h₀)
  have hm := (le_preimage_of_comp e2).2 h₃
  have h₂ := (le_preimage_of_comp e3).1 (hm.trans (m.left.preimage_mono (d.act_le j)))
  refine ⟨h₂, ?_⟩
  have key := congrArg (m.left.appLE _ W hm) (congrArg Units.val (d.equiv j k))
  rw [Units.val_mul, map_mul] at key
  refine (appLE_appLE e3 (d.act_le j) hm h₂ _).symm.trans (key.trans ?_)
  congr 1
  · exact (appLE_appLE e1 (le_preimage_top _ _) hm le_top _).trans
      (congrArg (resG _ le_top) (SplitTorus.charUnit_val _))
  · refine Eq.trans ?_ ((appLE_appLE e2 le_rfl hm h₃ _).trans (appLE_appLE rfl h₀ h₁ h₃ _).symm)
    rw [Scheme.Hom.appLE_eq_app]
    rfl

/- English proof (translation)
The claim follows from `d.i_hom (omegaMap d.i).app U (dUnit G h₀ (d.u j k).val) = (unitSec G).appLE _ U h₀ (d.u j k).val • resM _ le_top (dlogChar S E.X (E.basis k)) := by haveI := d.i_hom have he := sec_hom η[splitTorus S E.X] obtain ⟨h₂, e⟩ := appLE_coord d j k h₀ le_rfl rw [omegaMap_dUnit d.i h₀ ((le …`.
-/
theorem omegaMap_dUnit_coord (j : E.ChartIdx) (k : Module.Free.ChooseBasisIndex ℤ E.X) {U : S.Opens}
    (h₀ : U ≤ unitSec G ⁻¹ᵁ d.q.left ⁻¹ᵁ E.chart j) :
    haveI := d.i_hom
    (omegaMap d.i).app U (dUnit G h₀ (d.u j k).val) = (unitSec G).appLE _ U h₀ (d.u j k).val •
      resM _ le_top (dlogChar S E.X (E.basis k)) := by
  haveI := d.i_hom
  have he := sec_hom η[splitTorus S E.X]
  obtain ⟨h₂, e⟩ := appLE_coord d j k h₀ le_rfl
  rw [omegaMap_dUnit d.i h₀ ((le_preimage_iff he).2 le_rfl) h₂, e, dUnit_mul, dUnit_base, smul_zero,
    zero_add, appLE_base he _ _ le_rfl, LB.resG_self, dUnit_resG, dlogChar_apply, resM_dUnit]

/- English proof (translation)
The claim follows from `d.i_hom; haveI := d.q_hom; omegaMap d.q ≫ omegaMap d.i = 0 := by haveI := d.i_hom haveI := d.q_hom rw [← omegaMap_comp] exact cotMap_eq_zero d.isKernel.w.symm _`.
-/
theorem omegaMap_q_i : haveI := d.i_hom; haveI := d.q_hom; omegaMap d.q ≫ omegaMap d.i = 0 := by
  haveI := d.i_hom
  haveI := d.q_hom
  rw [← omegaMap_comp]
  exact cotMap_eq_zero d.isKernel.w.symm _

abbrev omegaSeq : ShortComplex S.Modules :=
  haveI := d.i_hom
  haveI := d.q_hom
  .mk (omegaMap d.q) (omegaMap d.i) (omegaMap_q_i d)

/- English proof (translation)
Use `haveI := d.i_hom`. Use `haveI := d.q_hom`. Use `haveI := d.q_affine`. Use `haveI := E.isAbelian.proper`. Establish `heB` using `sec_hom η[E.B]`.

Establish `H (x : S) : ∃ (U : S.Opens) (V : E.B.left.Opens) (j : E.ChartIdx), x ∈ U ∧ V ≤ E.chart j ∧ IsChart E.B.hom (unitSec E.B) U V`. Take `⟨j, hj⟩` from `UU.exists_mem_commonChart E (unitSec E.B x)`. Take `⟨U, hU, hx, -⟩` from `QCoh.exists_affine_mem_le (U := ⊤) x trivial`. Take `⟨V, hV, hx', k⟩` from `QCoh.exists_affine_mem_le (U := E.B.hom ⁻¹ᵁ U ⊓ E.chart j) (unitSec E.B x) ⟨(le_preimage_iff heB).2 le_rfl hx, hj⟩`. Take `⟨U', h₁, -, -, c⟩` from `exists_isChart_inf heB hU hV (k.trans inf_le_left) hx' hx`.

Conclude with `⟨U', _, j, h₁, inf_le_left.trans (k.trans inf_le_right), c⟩`. Use `choose U V j hx hV c using H`. Use `haveI : (omegaSeq d).X₁.IsQuasicoherent := isQuasicoherent_omega E.B`. Use `haveI : (omegaSeq d).X₂.IsQuasicoherent := isQuasicoherent_omega G`. Use `haveI : (omegaSeq d).X₃.IsQuasicoherent := isQuasicoherent_omega (splitTorus S E.X)`.

Use `(QCoh.shortExact_iff_affineCover U (top_le_iff.1 fun x _ => Opens.mem_iSup.2 ⟨x, hx x⟩) (fun x => (c x).affine_base) (omegaSeq d)).2 fun x => ?_` and prove the remaining obligations. Establish `cB` using `c x`. Establish `cG : IsChart G.hom (unitSec G) (U x) (d.q.left ⁻¹ᵁ V x)` using `⟨cB.affine_base, cB.affine.preimage _, (le_preimage_of_comp (unitSec_comp_left d.q)).2 cB.le, (le_preimage_of_comp (Over.w d.q)).1 (d.q.left.preimage_mono cB.le_base)⟩`. Establish `hb` using `d.coord (j x) (V x) cB.affine (hV x)`. Establish `happ (a : Γ(E.B.left, V x)) : d.q.left.app (V x) a = d.q.left.appLE _ _ le_rfl a`.

Rewrite using `[Scheme.Hom.appLE_eq_app]`. Establish `hk` using `d.q.left.preimage_mono (hV x)`. Establish `h₀` using `cG.le.trans ((unitSec G).preimage_mono hk)`. Use `⟨?_, exact_of_span (QCoh.appLinear (omegaMap d.q) (U x)) (QCoh.appLinear (omegaMap d.i) (U x)) (fun y => congr(($(omegaMap_q_i d)).app (U x) y)) ((isFrame_dlogChar S E.basis).basis le_top) (fun k => dUnit G h₀ (d.u (j x) k).val) (fun k => Units.map ((unitSec G).appLE _ _ h₀).hom. …` and prove the remaining obligations. Take `⟨ρ, h₁, h₂⟩` from `exists_retraction _ _ hb (E.B.hom.appLE _ _ cB.le_base).hom ((unitSec E.B).appLE _ _ cB.le).hom ((unitSec G).appLE _ _ cG.le).hom (fun r => (appLE_base heB _ _ le_rfl r).trans (LB.resG_self _ _)) (fun a => (congrArg _ (happ a)).trans (appLE_appLE (unitSec_comp_left d.q) _ _ _ a))`.

Conclude with `injective_omegaMap d.q cB cG le_rfl ρ (fun a => (congrArg ρ (happ a).symm).trans (h₁ a)) h₂`. Rewrite using `[IsFrame.basis_apply]`. Conclude with `omegaMap_dUnit_coord d (j x) k h₀`. Take `⟨a, rfl⟩` from `cG.d_surjective (sec_hom η[G]) y`. Use `mem_of_derivation _ _ E.basis hb.2 ((unitSec G).appLE _ _ cG.le).hom (dUnit G cG.le) (dUnit_mul G cG.le) _ (fun a => Submodule.mem_sup_left (LinearMap.mem_range.2 ⟨dUnit E.B cB.le a, ?_⟩)) (fun k => Submodule.mem_sup_right (Submodule.subset_span (Set.mem_range.2 ⟨k, ?_⟩))) a` and prove the remaining obligations.

Conclude with `(omegaMap_dUnit d.q cB.le cG.le le_rfl a).trans (congrArg _ (happ a).symm)`. Use `(dUnit_resG G cG.le hk _).symm.trans (congrArg _ ?_)` and prove the remaining obligations. Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
theorem shortExact_omegaSeq [QuasiSeparated G.hom] : (omegaSeq d).ShortExact := by
  haveI := d.i_hom
  haveI := d.q_hom
  haveI := d.q_affine
  haveI := E.isAbelian.proper
  have heB := sec_hom η[E.B]
  have H (x : S) : ∃ (U : S.Opens) (V : E.B.left.Opens) (j : E.ChartIdx), x ∈ U ∧ V ≤ E.chart j ∧
      IsChart E.B.hom (unitSec E.B) U V := by
    obtain ⟨j, hj⟩ := UU.exists_mem_commonChart E (unitSec E.B x)
    obtain ⟨U, hU, hx, -⟩ := QCoh.exists_affine_mem_le (U := ⊤) x trivial
    obtain ⟨V, hV, hx', k⟩ := QCoh.exists_affine_mem_le (U := E.B.hom ⁻¹ᵁ U ⊓ E.chart j)
      (unitSec E.B x) ⟨(le_preimage_iff heB).2 le_rfl hx, hj⟩
    obtain ⟨U', h₁, -, -, c⟩ := exists_isChart_inf heB hU hV (k.trans inf_le_left) hx' hx
    exact ⟨U', _, j, h₁, inf_le_left.trans (k.trans inf_le_right), c⟩
  choose U V j hx hV c using H
  haveI : (omegaSeq d).X₁.IsQuasicoherent := isQuasicoherent_omega E.B
  haveI : (omegaSeq d).X₂.IsQuasicoherent := isQuasicoherent_omega G
  haveI : (omegaSeq d).X₃.IsQuasicoherent := isQuasicoherent_omega (splitTorus S E.X)
  refine (QCoh.shortExact_iff_affineCover U (top_le_iff.1 fun x _ => Opens.mem_iSup.2 ⟨x, hx x⟩)
    (fun x => (c x).affine_base) (omegaSeq d)).2 fun x => ?_
  have cB := c x
  have cG : IsChart G.hom (unitSec G) (U x) (d.q.left ⁻¹ᵁ V x) :=
    ⟨cB.affine_base, cB.affine.preimage _, (le_preimage_of_comp (unitSec_comp_left d.q)).2 cB.le,
      (le_preimage_of_comp (Over.w d.q)).1 (d.q.left.preimage_mono cB.le_base)⟩
  have hb := d.coord (j x) (V x) cB.affine (hV x)
  have happ (a : Γ(E.B.left, V x)) : d.q.left.app (V x) a = d.q.left.appLE _ _ le_rfl a := by
    rw [Scheme.Hom.appLE_eq_app]
  have hk := d.q.left.preimage_mono (hV x)
  have h₀ := cG.le.trans ((unitSec G).preimage_mono hk)
  refine ⟨?_, exact_of_span (QCoh.appLinear (omegaMap d.q) (U x)) (QCoh.appLinear (omegaMap d.i) (U x))
    (fun y => congr(($(omegaMap_q_i d)).app (U x) y)) ((isFrame_dlogChar S E.basis).basis le_top)
    (fun k => dUnit G h₀ (d.u (j x) k).val)
    (fun k => Units.map ((unitSec G).appLE _ _ h₀).hom.toMonoidHom (d.u (j x) k))
    (fun k => ?_) fun y => ?_⟩
  · obtain ⟨ρ, h₁, h₂⟩ := exists_retraction _ _ hb (E.B.hom.appLE _ _ cB.le_base).hom
      ((unitSec E.B).appLE _ _ cB.le).hom ((unitSec G).appLE _ _ cG.le).hom
      (fun r => (appLE_base heB _ _ le_rfl r).trans (LB.resG_self _ _))
      (fun a => (congrArg _ (happ a)).trans (appLE_appLE (unitSec_comp_left d.q) _ _ _ a))
    exact injective_omegaMap d.q cB cG le_rfl ρ (fun a => (congrArg ρ (happ a).symm).trans (h₁ a)) h₂
  · rw [IsFrame.basis_apply]
    exact omegaMap_dUnit_coord d (j x) k h₀
  · obtain ⟨a, rfl⟩ := cG.d_surjective (sec_hom η[G]) y
    refine mem_of_derivation _ _ E.basis hb.2 ((unitSec G).appLE _ _ cG.le).hom (dUnit G cG.le)
      (dUnit_mul G cG.le) _ (fun a => Submodule.mem_sup_left (LinearMap.mem_range.2 ⟨dUnit E.B cB.le a, ?_⟩))
      (fun k => Submodule.mem_sup_right (Submodule.subset_span (Set.mem_range.2 ⟨k, ?_⟩))) a
    · exact (omegaMap_dUnit d.q cB.le cG.le le_rfl a).trans (congrArg _ (happ a).symm)
    · refine (dUnit_resG G cG.le hk _).symm.trans (congrArg _ ?_)
      simp
      rfl

/- English proof (translation)
Introduce `S E G _ h hG ⟨d⟩ hB`. Establish `fr` using `isFrame_dlogChar S (Module.finBasis ℤ E.X)`. Establish `hT : IsVB (omega (splitTorus S E.X)) (Module.finrank ℤ E.X)` using `by simpa using fr.isVB`. Take `⟨h₂, e⟩` from `VBExt.isVB_and_cls_det_of_shortExact S _ _ _ (shortExact_omegaSeq d) hB hT`. Use `⟨h₂, (CechPic.cls_eq_iff h₂.isLB_det hB.isLB_det).1 (e.trans ?_)⟩` and prove the remaining obligations.

Rewrite using `[fr.cls_det_eq_zero hT.isLB_det, add_zero]`.
-/
theorem isVB_omega_and_lbIso_hodge : ∀ (S : Scheme.{0}) (E : SplitExt S) (G : Over S) [GrpObj G] (h : ℕ),
    IsSemiAbelian G → E.IsGt G → IsVB (omega E.B) h →
      IsVB (omega G) (h + Module.finrank ℤ E.X) ∧
        LBIso (hodge G (h + Module.finrank ℤ E.X)) (hodge E.B h) := by
  intro S E G _ h hG ⟨d⟩ hB
  have fr := isFrame_dlogChar S (Module.finBasis ℤ E.X)
  have hT : IsVB (omega (splitTorus S E.X)) (Module.finrank ℤ E.X) := by simpa using fr.isVB
  obtain ⟨h₂, e⟩ := VBExt.isVB_and_cls_det_of_shortExact S _ _ _ (shortExact_omegaSeq d) hB hT
  refine ⟨h₂, (CechPic.cls_eq_iff h₂.isLB_det hB.isLB_det).1 (e.trans ?_)⟩
  rw [fr.cls_det_eq_zero hT.isLB_det, add_zero]

end GlobalTheory.GtHodge
