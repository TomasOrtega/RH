import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.ExpNegGlue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermFiniteOfSmaller
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.WeilBound.RepresentationTheoryGL.ConstantTermFiniteness.LieInvariants.InvariantOfLieOneLEqZero
import GroundTheory.PAdicHodge.NormalizedTrace

noncomputable section

open NumberField IsDedekindDomain MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Affgl GlobalTheory.PRep GlobalTheory.CuspRep.LocEx

namespace PositivityTheory.Rg.Rs.JFinTr

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [chart, mul_assoc]`.
-/
theorem chart_left {a : ℕ} (φ : GA E a → ℂ) (h g : GA E a) :
    chart (fun x => φ (h * x)) g = chart φ (h * g) := by
  funext x
  simp only [chart, mul_assoc]

def ltr {a : ℕ} (h : GA E a) : Module.End ℂ (Sm E a) where
  toFun φ := ⟨fun g => φ.1 (h * g), fun g => by
    rw [chart_left]
    exact φ.2 _⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/- English proof (translation)
The claim follows from `LinearMap.ext fun φ => Subtype.ext <| funext fun g => by change lieD X φ.1 (h * g) = fderiv ℝ (chart (fun x => φ.1 (h * x)) g) (oneL E a) X rw [chart_left] rfl`.
-/
theorem ltr_lie {a : ℕ} (h : GA E a) (X : Lie E a) : Commute (ltr h) (lie E a X) :=
  LinearMap.ext fun φ => Subtype.ext <| funext fun g => by
    change lieD X φ.1 (h * g) = fderiv ℝ (chart (fun x => φ.1 (h * x)) g) (oneL E a) X
    rw [chart_left]
    rfl

/- English proof (translation)
Set `S : Subalgebra ℂ (Module.End ℂ (Sm E a))` to `Subalgebra.centralizer ℂ {T}`. Establish `hS : ∀ {z}, z ∈ S ↔ Commute T z`. Introduce `z`. Simplify using `[S, Subalgebra.mem_centralizer_iff, Commute, SemiconjBy]`. Establish `hV : ∀ X, lie E a X ∈ S` using `fun X => hS.2 (hT X)`.

Establish `hE : ∀ τ i j, Eop τ i j ∈ S` using `fun τ i j => S.smul_mem (S.sub_mem (hV _) (S.smul_mem (hV _) _)) _`. Use `hS.1 ((Algebra.adjoin_le (S := S) ?_) hz)` and prove the remaining obligations. Introduce and unpack `_ ⟨τ, u, rfl⟩`. Use `S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)` and prove the remaining obligations. Take `⟨k, rfl⟩` from `List.mem_ofFn.1 hx`.

Use `S.add_mem ?_ (hE _ _ _)` and prove the remaining obligations. Use `split_ifs`. Conclude with `S.algebraMap_mem _`. Conclude with `S.zero_mem`.
-/
theorem commute_zalg {a : ℕ} {T : Module.End ℂ (Sm E a)} (hT : ∀ X, Commute T (lie E a X))
    {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) : Commute T z := by
  let S : Subalgebra ℂ (Module.End ℂ (Sm E a)) := Subalgebra.centralizer ℂ {T}
  have hS : ∀ {z}, z ∈ S ↔ Commute T z := by
    intro z
    simp [S, Subalgebra.mem_centralizer_iff, Commute, SemiconjBy]
  have hV : ∀ X, lie E a X ∈ S := fun X => hS.2 (hT X)
  have hE : ∀ τ i j, Eop τ i j ∈ S := fun τ i j =>
    S.smul_mem (S.sub_mem (hV _) (S.smul_mem (hV _) _)) _
  refine hS.1 ((Algebra.adjoin_le (S := S) ?_) hz)
  rintro _ ⟨τ, u, rfl⟩
  refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
  refine S.add_mem ?_ (hE _ _ _)
  split_ifs
  · exact S.algebraMap_mem _
  · exact S.zero_mem

/- English proof (translation)
Use extensionality with `i j`. Express the relevant statement in the definitionally equal form `(1 : Matrix (Fin a) (Fin a) (Ad E)) i j - sInf E ((1 : Matrix (Fin a) (Fin a) (Cinf E)) i j) + sInf E ((y : Matrix (Fin a) (Fin a) (Cinf E)) i j) = _`. Rewrite using `[hy]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality.

Rewrite using `[Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, Matrix.one_apply_eq, Matrix.one_apply_eq]`. Rewrite using `[Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, map_zero, sub_zero, add_zero]`.
-/
theorem infGL_val_diag {a : ℕ} (y : GL (Fin a) (Cinf E)) (d : Fin a → Cinf E) (hy : y.val = Matrix.diagonal d) :
    (infGL E a y).val = Matrix.diagonal fun i => 1 - sInf E 1 + sInf E (d i) := by
  ext i j
  change (1 : Matrix (Fin a) (Fin a) (Ad E)) i j - sInf E ((1 : Matrix (Fin a) (Fin a) (Cinf E)) i j) +
    sInf E ((y : Matrix (Fin a) (Fin a) (Cinf E)) i j) = _
  rw [hy]
  by_cases hij : i = j
  · subst hij
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, Matrix.one_apply_eq, Matrix.one_apply_eq]
  · rw [Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij,
      Matrix.one_apply_ne hij, map_zero, sub_zero, add_zero]

/- English proof (translation)
The claim follows from `infGL_val_diag _ _ rfl`.
-/
theorem aT_val (N r : ℕ) (t : ℝ) : (aT E N r t).val = Matrix.diagonal fun i : Fin N =>
    1 - sInf E 1 + sInf E (fun _ : InfinitePlace E => Complex.exp (if (i : ℕ) < r then (t : ℂ) else 0)) :=
  infGL_val_diag _ _ rfl

/- English proof (translation)
Rewrite using `[aT, ← map_inv]`. Conclude with `infGL_val_diag _ _ rfl`.
-/
theorem aT_inv_val (N r : ℕ) (t : ℝ) : ((aT E N r t)⁻¹).val = Matrix.diagonal fun i : Fin N =>
    1 - sInf E 1 + sInf E (fun _ : InfinitePlace E => Complex.exp (-(if (i : ℕ) < r then (t : ℂ) else 0))) := by
  rw [aT, ← map_inv]
  exact infGL_val_diag _ _ rfl

/- English proof (translation)
Set `Z : Matrix (Fin a) (Fin a) R` to `g.val * nilM y * (g⁻¹).val`. Use `⟨fun q => Z q.1.1 q.1.2, ?_⟩` and prove the remaining obligations. Establish `hZ : nilM (fun q : BlockIx a r => Z q.1.1 q.1.2) = Z`. Use extensionality with `i j`. Simplify using `only [nilM, Matrix.of_apply]`.

Use `split_ifs with hij`. Both sides reduce to the same expression. Use `symm`. Simplify using `only [Z, hg, hg', Matrix.mul_diagonal, Matrix.diagonal_mul, nilM, Matrix.of_apply, dif_neg hij, mul_zero, zero_mul]`. Apply `Units.ext` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `g.val * (1 + nilM y) = (1 + nilM fun q : BlockIx a r => Z q.1.1 q.1.2) * g.val`. Rewrite using `[hZ]`. Simplify using `only [Z, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]`. Rewrite using `[← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]`.
-/
theorem diag_mul_unip {a r : ℕ} {R : Type} [CommRing R] (g : GL (Fin a) R) (d d' : Fin a → R)
    (hg : g.val = Matrix.diagonal d) (hg' : (g⁻¹).val = Matrix.diagonal d') (y : BlockIx a r → R) :
    ∃ y' : BlockIx a r → R, g * unip y = unip y' * g := by
  let Z : Matrix (Fin a) (Fin a) R := g.val * nilM y * (g⁻¹).val
  refine ⟨fun q => Z q.1.1 q.1.2, ?_⟩
  have hZ : nilM (fun q : BlockIx a r => Z q.1.1 q.1.2) = Z := by
    ext i j
    simp only [nilM, Matrix.of_apply]
    split_ifs with hij
    · rfl
    · symm
      simp only [Z, hg, hg', Matrix.mul_diagonal, Matrix.diagonal_mul, nilM, Matrix.of_apply, dif_neg hij, mul_zero,
        zero_mul]
  apply Units.ext
  change g.val * (1 + nilM y) = (1 + nilM fun q : BlockIx a r => Z q.1.1 q.1.2) * g.val
  rw [hZ]
  simp only [Z, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_mul, Units.val_mul, aT_val, GlobalTheory.SmGL.val_emb₂]`. Use extensionality with `i j`. Rewrite using `[Matrix.diagonal_mul, Matrix.mul_diagonal]`. Take `⟨i, rfl⟩` from `(GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective i`.

Take `⟨j, rfl⟩` from `(GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective j`. Simplify using `only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]`. Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j <;> simp [GlobalTheory.SmGL.stdSum_inl, GlobalTheory.SmGL.stdSum_inr, mul_comm]`.
-/
theorem aT_comm_lev {r s : ℕ} (t : ℝ) (p : GA E r × GA E s) :
    aT E (r + s) r t * lev (Ad E) r s p = lev (Ad E) r s p * aT E (r + s) r t := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, aT_val, GlobalTheory.SmGL.val_emb₂]
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  obtain ⟨i, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective i
  obtain ⟨j, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases i with i | i <;> rcases j with j | j <;> simp [GlobalTheory.SmGL.stdSum_inl, GlobalTheory.SmGL.stdSum_inr, mul_comm]

/- English proof (translation)
Take `⟨a1, a2, a3, a4, a5, a6⟩` from `hF`. Use `⟨fun x g => ?_, fun γ g => ?_, fun k hk => ?_, fun g => ?_, fun g => ?_, fun z hz => ?_⟩` and prove the remaining obligations. Take `⟨y, hy⟩` from `diag_mul_unip (aT E (r + s) r t) _ _ (aT_val (r + s) r t) (aT_inv_val (r + s) r t) x`. Express the relevant statement in the definitionally equal form `F.1 (aT E (r + s) r t * (unip x * g)) = F.1 (aT E (r + s) r t * g)`. Rewrite using `[← mul_assoc, hy, mul_assoc, a1]`.

Express the relevant statement in the definitionally equal form `F.1 (aT E (r + s) r t * (lev (Ad E) r s (ratGL E r γ.1, ratGL E s γ.2) * g)) = F.1 (aT E (r + s) r t * g)`. Rewrite using `[← mul_assoc, aT_comm_lev, mul_assoc, a2]`. Use `Subtype.ext (funext fun g => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `F.1 (aT E (r + s) r t * (g * finGL E (r + s) k)) = F.1 (aT E (r + s) r t * g)`. Rewrite using `[← mul_assoc]`.

Conclude with `congrFun (congrArg Subtype.val (a3 k hk)) (aT E (r + s) r t * g)`. Use `a4 (aT E (r + s) r t * g) using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`. Express the relevant statement in the definitionally equal form `F.1 (aT E (r + s) r t * (g * infGL E (r + s) (Unitary.toUnits k))) = F.1 (aT E (r + s) r t * g * infGL E (r + s) (Unitary.toUnits k))`. Rewrite using `[mul_assoc]`.

Take `⟨C, n, hC⟩` from `a5 (aT E (r + s) r t * g)`. Use `⟨C, n, fun y => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `‖F.1 (aT E (r + s) r t * (g * infGL E (r + s) y))‖ ≤ _`. Rewrite using `[← mul_assoc]`. Conclude with `hC y`.

Rewrite using `[← Module.End.mul_apply, ← (commute_zalg (ltr_lie (aT E (r + s) r t)) (hJ hz)).eq, Module.End.mul_apply, a6 z hz, map_zero]`.
-/
theorem ltr_mem_goodCT {r s : ℕ} {L : Subgroup (GL (Fin (r + s)) (Af E))} {W : Type} [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (Kinf E (r + s)) W} {J : Set (Module.End ℂ (Sm E (r + s)))} (hJ : J ⊆ Zalg E (r + s))
    (t : ℝ) {F : Sm E (r + s)} (hF : F ∈ goodCT L ρ J) : ltr (aT E (r + s) r t) F ∈ goodCT L ρ J := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hF
  refine ⟨fun x g => ?_, fun γ g => ?_, fun k hk => ?_, fun g => ?_, fun g => ?_, fun z hz => ?_⟩
  · obtain ⟨y, hy⟩ := diag_mul_unip (aT E (r + s) r t) _ _ (aT_val (r + s) r t) (aT_inv_val (r + s) r t) x
    change F.1 (aT E (r + s) r t * (unip x * g)) = F.1 (aT E (r + s) r t * g)
    rw [← mul_assoc, hy, mul_assoc, a1]
  · change F.1 (aT E (r + s) r t * (lev (Ad E) r s (ratGL E r γ.1, ratGL E s γ.2) * g)) = F.1 (aT E (r + s) r t * g)
    rw [← mul_assoc, aT_comm_lev, mul_assoc, a2]
  · refine Subtype.ext (funext fun g => ?_)
    change F.1 (aT E (r + s) r t * (g * finGL E (r + s) k)) = F.1 (aT E (r + s) r t * g)
    rw [← mul_assoc]
    exact congrFun (congrArg Subtype.val (a3 k hk)) (aT E (r + s) r t * g)
  · convert a4 (aT E (r + s) r t * g) using 1
    funext k
    change F.1 (aT E (r + s) r t * (g * infGL E (r + s) (Unitary.toUnits k))) =
      F.1 (aT E (r + s) r t * g * infGL E (r + s) (Unitary.toUnits k))
    rw [mul_assoc]
  · obtain ⟨C, n, hC⟩ := a5 (aT E (r + s) r t * g)
    refine ⟨C, n, fun y => ?_⟩
    change ‖F.1 (aT E (r + s) r t * (g * infGL E (r + s) y))‖ ≤ _
    rw [← mul_assoc]
    exact hC y
  · rw [← Module.End.mul_apply, ← (commute_zalg (ltr_lie (aT E (r + s) r t)) (hJ hz)).eq, Module.End.mul_apply,
      a6 z hz, map_zero]

def stabFin {a : ℕ} (φ : Sm E a) : Subgroup (GL (Fin a) (Af E)) where
  carrier := {k | finRep E a k φ = φ}
  mul_mem' := fun {x y} hx hy => by
    change finRep E a (x * y) φ = φ
    have hx' : finRep E a x φ = φ := hx
    have hy' : finRep E a y φ = φ := hy
    rw [map_mul, Module.End.mul_apply, hy', hx']
  one_mem' := by
    change finRep E a 1 φ = φ
    rw [map_one]; rfl
  inv_mem' := fun {x} hx => by
    change finRep E a x⁻¹ φ = φ
    have hx' : finRep E a x φ = φ := hx
    conv_lhs => rw [← hx']
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl

set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Use `set Z := Subalgebra.toSubmodule (Zalg E a) with hZ`. Use `set S := Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a) with hS`. Set `ev : Z →ₗ[ℂ] S` to `{ toFun := fun z => ⟨z.1 φ, Submodule.subset_span ⟨z.1, z.2, rfl⟩⟩ map_add' := fun x y => Subtype.ext (LinearMap.add_apply _ _ _) map_smul' := fun c x => Subtype.ext (LinearMap.smul_apply _ _ _) }`. Take `⟨V', hV'⟩` from `Submodule.exists_isCompl (LinearMap.ker ev)`. Use `haveI : FiniteDimensional ℂ V' := by`.

Use `FiniteDimensional.of_injective (ev.comp V'.subtype) ?_` and prove the remaining obligations. Introduce `x y hxy`. Establish `hxy' : ev x = ev y` using `hxy`. Establish `hx : ((x : Z) - y) ∈ LinearMap.ker ev`. Rewrite using `[LinearMap.mem_ker, map_sub]`.

Conclude with `sub_eq_zero.2 hxy'`. Establish `h0` using `Submodule.disjoint_def.1 hV'.disjoint _ hx (V'.sub_mem x.2 y.2)`. Conclude with `Subtype.ext (sub_eq_zero.1 h0)`. Use `⟨fun z hz => hz.1, V'.map Z.subtype, inferInstance, fun z hz => ?_⟩` and prove the remaining obligations. Establish `hz' : (⟨z, hz⟩ : Z) ∈ LinearMap.ker ev ⊔ V'` using `hV'.sup_eq_top ▸ Submodule.mem_top`.

Take `⟨w, hw, v, hv, e⟩` from `Submodule.mem_sup.1 hz'`. Establish `hw0 : w.1 φ = 0` using `congrArg Subtype.val (LinearMap.mem_ker.1 hw)`. Use `Submodule.mem_sup.2 ⟨v.1, ⟨v, hv, rfl⟩, w.1, Submodule.subset_span ⟨1, Subalgebra.one_mem _, w.1, ⟨w.2, hw0⟩, (one_mul _).symm⟩, ?_⟩` and prove the remaining obligations. Establish `e' : (w : Module.End ℂ (Sm E a)) + v = z` using `congrArg Subtype.val e`. Rewrite using `[← e', add_comm]`.
-/
theorem cofin_ann {a : ℕ} (φ : Sm E a)
    [hφ : FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a))] :
    Cofin {z : Module.End ℂ (Sm E a) | z ∈ Zalg E a ∧ z φ = 0} := by
  set Z := Subalgebra.toSubmodule (Zalg E a) with hZ
  set S := Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a) with hS
  let ev : Z →ₗ[ℂ] S :=
    { toFun := fun z => ⟨z.1 φ, Submodule.subset_span ⟨z.1, z.2, rfl⟩⟩
      map_add' := fun x y => Subtype.ext (LinearMap.add_apply _ _ _)
      map_smul' := fun c x => Subtype.ext (LinearMap.smul_apply _ _ _) }
  obtain ⟨V', hV'⟩ := Submodule.exists_isCompl (LinearMap.ker ev)
  haveI : FiniteDimensional ℂ V' := by
    refine FiniteDimensional.of_injective (ev.comp V'.subtype) ?_
    intro x y hxy
    have hxy' : ev x = ev y := hxy
    have hx : ((x : Z) - y) ∈ LinearMap.ker ev := by
      rw [LinearMap.mem_ker, map_sub]
      exact sub_eq_zero.2 hxy'
    have h0 := Submodule.disjoint_def.1 hV'.disjoint _ hx (V'.sub_mem x.2 y.2)
    exact Subtype.ext (sub_eq_zero.1 h0)
  refine ⟨fun z hz => hz.1, V'.map Z.subtype, inferInstance, fun z hz => ?_⟩
  have hz' : (⟨z, hz⟩ : Z) ∈ LinearMap.ker ev ⊔ V' := hV'.sup_eq_top ▸ Submodule.mem_top
  obtain ⟨w, hw, v, hv, e⟩ := Submodule.mem_sup.1 hz'
  have hw0 : w.1 φ = 0 := congrArg Subtype.val (LinearMap.mem_ker.1 hw)
  refine Submodule.mem_sup.2 ⟨v.1, ⟨v, hv, rfl⟩, w.1,
    Submodule.subset_span ⟨1, Subalgebra.one_mem _, w.1, ⟨w.2, hw0⟩, (one_mul _).symm⟩, ?_⟩
  have e' : (w : Module.End ℂ (Sm E a)) + v = z := congrArg Subtype.val e
  rw [← e', add_comm]

/- English proof (translation)
Introduce `E _ _ _ N φ hφ r hr0 hrN F hF`. Take `⟨s, rfl⟩ : ∃ s, N = r + s` from `⟨N - r, by omega⟩`. Use `letI : MeasurableSpace (BlockIx (r + s) r → Ad E) := borel _`. Use `haveI : BorelSpace (BlockIx (r + s) r → Ad E) := ⟨rfl⟩`. Take `⟨μ, 𝓕, hμ, h𝓕, rfl⟩` from `hF`.

Use `haveI : FiniteDimensional ℂ (orbSpan φ) := hφ.kfin`. Use `haveI := hφ.zfin`. Set `ρ` to `sub (cptRep E (r + s)) (orbSpan φ) (orbSpan_stable φ)`. Establish `hρ : GlobalTheory.Published.AutFin.IsContRep ρ` using `isContRep_sub _ _`. Establish `hL : IsOpen ((stabFin φ : Subgroup (GL (Fin (r + s)) (Af E))) : Set (GL (Fin (r + s)) (Af E)))` using `hφ.level`.

Set `J : Set (Module.End ℂ (Sm E (r + s)))` to `{z | z ∈ Zalg E (r + s) ∧ z φ = 0}`. Establish `hJ : Cofin J` using `cofin_ann φ`. Establish `hφg : φ ∈ genSpace (stabFin φ) ρ J` using `⟨hφ, fun k hk => hk, fun g => GlobalTheory.Published.AutFinGL.type_of_map ρ (orbSpan φ).subtype (fun _ _ => rfl) ⟨φ, Submodule.subset_span ⟨1, by simp⟩⟩ g, fun z hz => hz.2⟩`. Take `⟨G, hG, hGe⟩` from `exists_mem_goodCT (stabFin φ) ρ J hJ φ hφg μ 𝓕 hμ h𝓕`. Use `haveI := finiteDimensional_goodCT (PositivityTheory.Rg.HF.GL.genFin E r) (PositivityTheory.Rg.HF.GL.genFin E s) (stabFin φ) hL ρ hρ J hJ`.

Use `Submodule.finiteDimensional_of_le (S₂ := (goodCT (stabFin φ) ρ J).map (Sm E (r + s)).subtype) (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨t, rfl⟩`. Conclude with `⟨ltr (aT E (r + s) r t) G, ltr_mem_goodCT hJ.1 t hG, funext fun g => hGe _⟩`.
-/
theorem finTr : FinTr := by
  intro E _ _ _ N φ hφ r hr0 hrN F hF
  obtain ⟨s, rfl⟩ : ∃ s, N = r + s := ⟨N - r, by omega⟩
  letI : MeasurableSpace (BlockIx (r + s) r → Ad E) := borel _
  haveI : BorelSpace (BlockIx (r + s) r → Ad E) := ⟨rfl⟩
  obtain ⟨μ, 𝓕, hμ, h𝓕, rfl⟩ := hF
  haveI : FiniteDimensional ℂ (orbSpan φ) := hφ.kfin
  haveI := hφ.zfin
  let ρ := sub (cptRep E (r + s)) (orbSpan φ) (orbSpan_stable φ)
  have hρ : GlobalTheory.Published.AutFin.IsContRep ρ := isContRep_sub _ _
  have hL : IsOpen ((stabFin φ : Subgroup (GL (Fin (r + s)) (Af E))) : Set (GL (Fin (r + s)) (Af E))) := hφ.level
  let J : Set (Module.End ℂ (Sm E (r + s))) := {z | z ∈ Zalg E (r + s) ∧ z φ = 0}
  have hJ : Cofin J := cofin_ann φ
  have hφg : φ ∈ genSpace (stabFin φ) ρ J :=
    ⟨hφ, fun k hk => hk, fun g => GlobalTheory.Published.AutFinGL.type_of_map ρ (orbSpan φ).subtype (fun _ _ => rfl)
      ⟨φ, Submodule.subset_span ⟨1, by simp⟩⟩ g, fun z hz => hz.2⟩
  obtain ⟨G, hG, hGe⟩ := exists_mem_goodCT (stabFin φ) ρ J hJ φ hφg μ 𝓕 hμ h𝓕
  haveI := finiteDimensional_goodCT (PositivityTheory.Rg.HF.GL.genFin E r) (PositivityTheory.Rg.HF.GL.genFin E s) (stabFin φ) hL ρ hρ J hJ
  refine Submodule.finiteDimensional_of_le (S₂ := (goodCT (stabFin φ) ρ J).map (Sm E (r + s)).subtype)
    (Submodule.span_le.2 ?_)
  rintro _ ⟨t, rfl⟩
  exact ⟨ltr (aT E (r + s) r t) G, ltr_mem_goodCT hJ.1 t hG, funext fun g => hGe _⟩

end PositivityTheory.Rg.Rs.JFinTr

namespace PositivityTheory.Rg.Rs

/- English proof (translation)
The claim follows from `JFinTr.finTr`.
-/
theorem finTr_holds : FinTr := JFinTr.finTr

end PositivityTheory.Rg.Rs

end
