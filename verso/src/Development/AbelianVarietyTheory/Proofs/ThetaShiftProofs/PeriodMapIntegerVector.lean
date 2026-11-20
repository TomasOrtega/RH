import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ToMatrixTrFormBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SmulPeriodMapMkZeroFstEqNegForm
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSplitOfCoisotropicKer
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceEqFinrankMulSum
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Imports
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpPiIInt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TwoMulEqOfIsTypeFn

noncomputable section

namespace GlobalTheory.OfPeriod

open ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField
open Complex

section Model

variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)

/- English proof (translation)
Apply the tactic sequence `ext <;> simp`.
-/
theorem period_map_integer_vector (n : A.X →+ ℤ) : A.P0 (AnArc.La.mk 0 n 0) = ((Int.castAddHom ℂ).comp n, 0) := by
  ext <;> simp

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hv`. Establish `: v.1 ∈ (Submodule.span ℂ (Set.range fun n => A.P0 (AnArc.La.mk 0 n 0))).comap (LinearMap.inl ℂ _ _)`. Use `(Submodule.span_le.2 ?_) (span_intHom.ge (Submodule.mem_top (x := v.1)))` and prove the remaining obligations. Introduce and unpack `_ ⟨n, rfl⟩`.

Conclude with `Submodule.subset_span ⟨n, period_map_integer_vector A n⟩`. Establish `h : v = LinearMap.inl ℂ _ _ v.1` using `Prod.ext rfl hv`. Rewrite using `[h]` and apply the resulting hypothesis. Introduce `hv`. Use `LinearMap.eqOn_span (f := LinearMap.snd ℂ _ _) (g := 0) ?_ hv` and prove the remaining obligations.

Introduce and unpack `_ ⟨n, rfl⟩`. Simplify using the standard rewrite rules.
-/
theorem snd_eq_zero_iff (v : A.V) :
    v.2 = 0 ↔ v ∈ Submodule.span ℂ (Set.range fun n => A.P0 (AnArc.La.mk 0 n 0)) := by
  constructor
  · intro hv
    have : v.1 ∈ (Submodule.span ℂ (Set.range fun n => A.P0 (AnArc.La.mk 0 n 0))).comap (LinearMap.inl ℂ _ _) := by
      refine (Submodule.span_le.2 ?_) (span_intHom.ge (Submodule.mem_top (x := v.1)))
      rintro _ ⟨n, rfl⟩
      exact Submodule.subset_span ⟨n, period_map_integer_vector A n⟩
    have h : v = LinearMap.inl ℂ _ _ v.1 := Prod.ext rfl hv
    rwa [h]
  · intro hv
    refine LinearMap.eqOn_span (f := LinearMap.snd ℂ _ _) (g := 0) ?_ hv
    rintro _ ⟨n, rfl⟩
    simp

/- English proof (translation)
Establish `h1 : ∀ n, A.Hw w v (A.P0 (AnArc.La.mk 0 n 0)) = A.dualForm w (A.torusProj v) ((Int.castAddHom ℂ).comp n)` using `fun n => by rw [period_map_integer_vector, A.Hw_apply]; simp [AnArc.torusProj_def]`. Simplify using `only [h1]`. Use `⟨fun h n => by simp [h], fun h => ?_⟩` and prove the remaining obligations. Establish `h2 : A.dualForm w (A.torusProj v) = 0` using `LinearMap.ext_on_range span_intHom h`. Assume the negation of the conclusion as `hne`.

Use `A.dualForm_pos hw hne` as an intermediate fact. Simplify using `[h2] at this`.
-/
theorem torusProj_eq_zero_iff {w : ℂ} (hw : (A.BwMat w).PosDef) (v : A.V) :
    A.torusProj v = 0 ↔ ∀ n, A.Hw w v (A.P0 (AnArc.La.mk 0 n 0)) = 0 := by
  have h1 : ∀ n, A.Hw w v (A.P0 (AnArc.La.mk 0 n 0)) = A.dualForm w (A.torusProj v) ((Int.castAddHom ℂ).comp n) :=
    fun n => by rw [period_map_integer_vector, A.Hw_apply]; simp [AnArc.torusProj_def]
  simp only [h1]
  refine ⟨fun h n => by simp [h], fun h => ?_⟩
  have h2 : A.dualForm w (A.torusProj v) = 0 := LinearMap.ext_on_range span_intHom h
  by_contra hne
  have := A.dualForm_pos hw hne
  simp [h2] at this

/- English proof (translation)
Set `f : (A.X →+ ℂ) →ₗ[ℂ] (A.X →+ ℂ)` to `LinearMap.fst ℂ _ _ ∘ₗ A.actV a ∘ₗ LinearMap.inl ℂ _ _`. Establish `h1 : A.actV a = f.prodMap (A.F a)` using `LinearMap.ext fun v => rfl`. Establish `h2 : A.F a = Matrix.toLin' (Matrix.diagonal fun i => ty i (a : E))` using `LinearMap.ext fun z => funext fun i => by simp [hF, Matrix.mulVec_diagonal]`. Rewrite using `[h1, LinearMap.trace_prodMap', HomTrace.trace_eq_finrank_mul_sum E A.X (star a) f fun _ _ => rfl, h2]`. Simplify using the standard rewrite rules.
-/
theorem trace_actV {E : Type} [Field E] [NumberField E] [StarRing (𝓞 E)] (A : AnArc (𝓞 E))
    {ty : Fin A.gB → (E →+* ℂ)} (hF : ∀ a z i, A.F a z i = ty i (a : E) * z i) (a : 𝓞 E) :
    LinearMap.trace ℂ A.V (A.actV a) =
      (Module.finrank (𝓞 E) A.X : ℂ) * ∑ τ : E →+* ℂ, τ ((star a : 𝓞 E) : E) + ∑ i, ty i (a : E) := by
  let f : (A.X →+ ℂ) →ₗ[ℂ] (A.X →+ ℂ) := LinearMap.fst ℂ _ _ ∘ₗ A.actV a ∘ₗ LinearMap.inl ℂ _ _
  have h1 : A.actV a = f.prodMap (A.F a) := LinearMap.ext fun v => rfl
  have h2 : A.F a = Matrix.toLin' (Matrix.diagonal fun i => ty i (a : E)) :=
    LinearMap.ext fun z => funext fun i => by simp [hF, Matrix.mulVec_diagonal]
  rw [h1, LinearMap.trace_prodMap', HomTrace.trace_eq_finrank_mul_sum E A.X (star a) f fun _ _ => rfl, h2]
  simp

abbrev moduleLam : Module O A.abelian₂ where
  smul := A.FLam
  one_smul l := Subtype.ext (by show A.F 1 l = l; simp)
  mul_smul a b l := Subtype.ext (by show A.F (a * b) l = A.F a (A.F b l); simp)
  smul_zero a := Subtype.ext (map_zero (A.F a))
  smul_add a l m := Subtype.ext (map_add (A.F a) _ _)
  add_smul a b l := Subtype.ext (by show A.F (a + b) l = A.F a l + A.F b l; simp)
  zero_smul l := Subtype.ext (by show A.F 0 l = 0; simp)

end Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def perp (D : Datum H) (Hh : Submodule (𝓞 E) D.La) : Submodule (𝓞 E) D.La where
  carrier := {v | ∀ t ∈ Hh, D.EF t v = 0}
  zero_mem' t _ := map_zero _
  add_mem' {v v'} hv hv' t ht := by rw [map_add, hv t ht, hv' t ht, add_zero]
  smul_mem' a v hv t ht := by
    have h := D.adj (H.bar a) t v
    rw [hv _ (Hh.smul_mem _ ht)] at h
    have h2 : H.bar (H.bar a) = a := H.starRing.star_involutive a
    rw [h2] at h
    exact h.symm

/- English proof (translation)
Set `_` to `H.starRing`. Introduce `A p q ty hty hF`. Set `_` to `moduleLam A`. Establish `hr : Set.range A.abelian₂.subtype.toAddMonoidHom = A.abelian₂` using `Subtype.range_coe`. Establish `hd : ∀ G : AddSubgroup (Fin A.gB → ℂ), (G : Set (Fin A.gB → ℂ)) = A.abelian₂ → DiscreteTopology G` using `fun G hG => by`.

Establish `: G = A.abelian₂.toAddSubgroup` using `SetLike.coe_injective hG`. Rewrite using `[this]`. Conclude with `A.discrete`. Take `⟨DB, e, hp, hq, he⟩` from `PeriodDatum.exists_datum E H A.abelian₂ A.Ef p q A.gB ty A.abelian₂.subtype.toAddMonoidHom A.Hm hty A.Ef_bij A.Ef_FLam (fun a x i => hF a x i) Subtype.val_injective (hd _ hr) (hr ▸ A.full) A.Hm_herm A.Hm_pos fun x y => (A.Ef_eq x y).symm`. Establish `hr' : Set.range (A.abelian₂.subtype.toAddMonoidHom.comp e.toAddEquiv.toAddMonoidHom) = A.abelian₂` using `(e.surjective.range_comp A.abelian₂.subtype.toAddMonoidHom).trans hr`.

Use `⟨DB, e.toAddEquiv, hp, hq, e.map_smul, he, fun a x i => ?_, Subtype.val_injective.comp e.injective, hd _ hr', hr' ▸ A.full, A.Hm, A.Hm_herm, A.Hm_pos, fun x y => ?_⟩` and prove the remaining obligations. Conclude with `(congrArg (fun l : A.abelian₂ => l.1 i) (e.map_smul a x)).trans (hF a _ i)`. Rewrite using `[he]`. Conclude with `(A.Ef_eq _ _).symm`.
-/
theorem exists_datum_Lam : letI := H.starRing
    ∀ (A : AnArc (𝓞 E)) (p q : ℕ) (ty : Fin A.gB → (E →+* ℂ)), IsTypeFn H p q ty →
      (∀ a z i, A.F a z i = ty i (a : E) * z i) →
      ∃ (DB : Datum H) (e : DB.La ≃+ A.abelian₂), DB.p = p ∧ DB.q = q ∧ (∀ (a : 𝓞 E) x, e (a • x) = A.FLam a (e x)) ∧
        (∀ x x', DB.EF x x' = A.Ef (e x) (e x')) ∧
        IsPeriod DB ty (A.abelian₂.subtype.toAddMonoidHom.comp e.toAddMonoidHom) := by
  let _ := H.starRing
  intro A p q ty hty hF
  let _ := moduleLam A
  have hr : Set.range A.abelian₂.subtype.toAddMonoidHom = A.abelian₂ := Subtype.range_coe
  have hd : ∀ G : AddSubgroup (Fin A.gB → ℂ), (G : Set (Fin A.gB → ℂ)) = A.abelian₂ → DiscreteTopology G := fun G hG => by
    have : G = A.abelian₂.toAddSubgroup := SetLike.coe_injective hG
    rw [this]; exact A.discrete
  obtain ⟨DB, e, hp, hq, he⟩ := PeriodDatum.exists_datum E H A.abelian₂ A.Ef p q A.gB ty A.abelian₂.subtype.toAddMonoidHom A.Hm hty
    A.Ef_bij A.Ef_FLam (fun a x i => hF a x i) Subtype.val_injective (hd _ hr) (hr ▸ A.full) A.Hm_herm A.Hm_pos
    fun x y => (A.Ef_eq x y).symm
  have hr' : Set.range (A.abelian₂.subtype.toAddMonoidHom.comp e.toAddEquiv.toAddMonoidHom) = A.abelian₂ :=
    (e.surjective.range_comp A.abelian₂.subtype.toAddMonoidHom).trans hr
  refine ⟨DB, e.toAddEquiv, hp, hq, e.map_smul, he, fun a x i => ?_, Subtype.val_injective.comp e.injective, hd _ hr',
    hr' ▸ A.full, A.Hm, A.Hm_herm, A.Hm_pos, fun x y => ?_⟩
  · exact (congrArg (fun l : A.abelian₂ => l.1 i) (e.map_smul a x)).trans (hF a _ i)
  · rw [he]; exact (A.Ef_eq _ _).symm

/- English proof (translation)
Set `_` to `H.starRing`. Take `⟨hlin, hinj, hdisc, hspan, Hm', hherm, hpos', hHm'⟩` from `hP`. Establish `hS : ∀ z z', sesq Hm z z' = sesq Hm' z z'` using `sesq_ext hspan fun i k => (hHm i k).trans (hHm' i k).symm`. Establish `hconj : ∀ z z', starRingEnd ℂ (sesq Hm z z') = sesq Hm z' z` using `fun z z' => by`. Rewrite using `[hS, hS, sesq_conj hherm]`.

Establish `hpos : ∀ z, z ≠ 0 → 0 < (sesq Hm z z).re` using `fun z hz => by rw [hS]; exact hpos' z hz`. Establish `hw : H.w0 + star H.w0 = 1` using `by show H.w0 + H.bar H.w0 = 1`. Rewrite using `[HostModel.cmHost_bar_halfIntegerGenerator, add_sub_cancel]`. Establish `hadj : ∀ (a : 𝓞 E) x x', D.EF (a • x) x' = D.EF x (star a • x')` using `D.adj`. Establish `halt : D.EF.IsAlt` using `D.alt`.

Take `⟨hfin, hrk, -⟩` from `PeriodDatum.lattice_equiv P hinj hdisc hspan`. Establish `: Module.IsTorsionFree ℤ D.La` using `hinj.moduleIsTorsionFree _ (map_zsmul P)`. Establish `: Module.Finite ℤ Y` using `Module.Finite.of_surjective y.toAddMonoidHom.toIntLinearMap hy`. Establish `: Module.IsTorsionFree ℤ Y` using `Module.IsTorsionFree.of_smul_eq_zero fun k x hx => by`. Take `⟨v, rfl⟩` from `hy x`.

Use `or_iff_not_imp_left.2 fun hk => (hker v).2 fun t ht => ?_` and prove the remaining obligations. Simplify `(hker (k • v)).1 (by rw [map_zsmul, hx]) t ht` using `[hk]`. Establish `: Module.Free ℤ Y` using `Module.free_of_finite_type_torsion_free'`. Use `Forms.projective_of_int (𝓞 E) Y` as an intermediate fact. Establish `hHh : ∀ t, t ∈ Hh ↔ ∀ v, y v = 0 → D.EF t v = 0` using `fun t => by`.

Establish `: Module.Finite ℤ (D.La ⧸ Hh)` using `Module.Finite.of_surjective Hh.mkQ.toAddMonoidHom.toIntLinearMap Hh.mkQ_surjective`. Establish `: Module.IsTorsionFree ℤ (D.La ⧸ Hh)` using `Module.IsTorsionFree.of_smul_eq_zero fun k x hx => by`. Take `⟨v, rfl⟩` from `Hh.mkQ_surjective x`. Use `or_iff_not_imp_left.2 fun hk => (Submodule.Quotient.mk_eq_zero _).2 (hsat k v hk ?_)` and prove the remaining obligations. Conclude with `(Submodule.Quotient.mk_eq_zero _).1 ((map_zsmul Hh.mkQ k v).trans hx)`.

Establish `: Module.Free ℤ (D.La ⧸ Hh)` using `Module.free_of_finite_type_torsion_free'`. Use `⟨fun ht v hv => (hker v).1 hv t ht, fun ht => (Submodule.Quotient.mk_eq_zero _).1 ?_⟩` and prove the remaining obligations. Use `(KerPerp.ker_iff (hadj := hadj) (y := Hh.mkQ) D.unimod.2 t).2 fun v hv => ?_` and prove the remaining obligations. Conclude with `halt.eq_iff.1 (ht v ((hker v).2 fun t' ht' => halt.eq_iff.1 (hv t' ((Submodule.Quotient.mk_eq_zero _).2 ht'))))`. Take `⟨M, _, _, EM, e₀, hEM, he₁, he₂, he₃, hE⟩` from `exists_split_of_coisotropic_ker (𝓞 E) D.La Y H.w0 D.EF y hw D.alt D.unimod hadj hy fun t ht => (hker t).2 fun t' ht' => hiso t' ht' t ((hHh t).2 ht)`.

Establish `: Module.Finite ℤ M` using `Module.Finite.of_surjective ((AddMonoidHom.snd _ _).comp ((AddMonoidHom.snd _ _).comp e₀.toAddMonoidHom)).toIntLinearMap fun m => ⟨e₀.symm (0, 0, m), by simp⟩`. Establish `: Module.IsTorsionFree ℤ M` using `Function.Injective.moduleIsTorsionFree (fun m : M => e₀.symm (0, 0, m)) (fun m m' hm => by simpa using hm) fun k m => by rw [← map_zsmul]; simp`. Establish `: Module.Free ℤ M` using `Module.free_of_finite_type_torsion_free'`. Establish `hrk' : 2 * Module.finrank ℤ Y + Module.finrank ℤ M = 2 * Module.finrank ℂ (Fin g → ℂ)`. Establish `: Module.Finite ℤ (Y →+ ℤ)` using `Module.Finite.equiv (addMonoidHomLequivInt ℤ (A := Y) (B := ℤ)).symm`.

Establish `: Module.Free ℤ (Y →+ ℤ)` using `Module.Free.of_equiv (addMonoidHomLequivInt ℤ (A := Y) (B := ℤ)).symm`. Rewrite `hrk` using `[e₀.toIntLinearEquiv.finrank_eq, Module.finrank_prod, Module.finrank_prod, finrank_hom_int]`. Rewrite using `[Module.finrank_fin_fun]`. Use linear arithmetic over natural numbers and integers. Set `ρ : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)` to `{ toFun := fun a => LinearMap.pi fun i => ty i (a : E) • LinearMap.proj i map_one' := by ext; simp map_mul' := fun _ _ => LinearMap.ext fun z => funext fun i => by simp [mul_assoc] map_zero' := by ext; simp map_add' := fun _ _ => LinearMap.ext fun z => funext fun i => by simp [ad …`.

Establish `hρ : ∀ a z, ρ a z = fun i => ty i (a : E) * z i` using `fun _ _ => rfl`. Establish `hPρ : ∀ a v, P (a • v) = ρ a (P v)` using `fun a v => funext (hlin a v)`. Establish `hρS : ∀ a z z', sesq Hm (ρ a z) z' = sesq Hm z (ρ (star a) z')` using `fun a => sesq_ext (S := sesq Hm ∘ₗ ρ a) (S' := (sesq Hm).compl₂ (ρ (star a))) hspan fun v v' => by show (hermForm Hm (ρ a (P v)) (P v')).im = (hermForm Hm (P v) (ρ (star a) (P v'))).im`. Rewrite using `[← hPρ, ← hPρ, hHm, hHm, hadj]`. Establish `he : ∀ (a : 𝓞 E) v, e₀ (a • v) = (a • (e₀ v).1, (e₀ v).2.1.comp (DistribSMul.toAddMonoidHom Y (star a)), a • (e₀ v).2.2)` using `fun a v => Prod.ext (by rw [he₁, he₁, map_smul]) (Prod.ext (AddMonoidHom.ext (he₂ a v)) (he₃ a v))`.

Take `⟨A, e, f, h, hbe, hchi, hpsi, ⟨tyB, hF⟩, hfF, hEf, hact, hh, hB⟩` from `exists_arc hw EM hEM (P.comp e₀.symm.toAddMonoidHom) ((congrArg _ (e₀.symm.surjective.range_comp P)).trans hspan) hrk' hconj hpos (fun v v' => by show (hermForm Hm (P (e₀.symm v)) (P (e₀.symm v'))).im = _`. Rewrite using `[hHm, hE, e₀.apply_symm_apply, e₀.apply_symm_apply]) ρ hρS`. Use the proof step `(fun a v => by`. Take `⟨v, rfl⟩` from `e₀.surjective v`. Rewrite using `[← he]`.

Simplify using `[hPρ]) be be_symm be_pos be_adj be_even`. Use the proof step `(fun n F => ∃ ty : Fin n → (E →+* ℂ), ∀ a z i, F a z i = ty i (a : E) * z i) exists_diag`. Apply the tactic sequence `let gam : D.La ≃ₗ[𝓞 E] A.La := { toFun := fun v => AnArc.La.mk (e.symm (e₀ v).1) ((e₀ v).2.1.comp e.toAddEquiv.toAddMonoidHom) (f (e₀ v).2.2) invFun := fun v => e₀.symm (e v.y, v.n.comp e.symm.toAddEquiv.toAddMonoidHom, f.symm v.l) map_add' := fun v v' => by ext <;> simp map_smul …`. Establish `hgam : ∀ v, gam v = AnArc.La.mk (e.symm (e₀ v).1) ((e₀ v).2.1.comp e.toAddEquiv.toAddMonoidHom) (f (e₀ v).2.2)` using `fun _ => rfl`. Establish `hiso' : ∀ v v', A.EF (gam v) (gam v') = D.EF v v'` using `fun v v' => by`.

Simplify using `[hgam, AnArc.EF_apply, hEf, hE]`. Establish `hgy : ∀ v, e (gam v).y = y v` using `fun v => by simp [hgam, he₁]`. Establish `hgy0 : ∀ v, (gam v).y = 0 ↔ y v = 0` using `fun v => by rw [← hgy, e.map_eq_zero_iff]`. Establish `hgH : ∀ v, v ∈ Hh ↔ ∃ n, gam v = AnArc.La.mk 0 n 0` using `fun v => by`. Rewrite using `[hHh, ← A.orth_ker_iff_exists, gam.surjective.forall]`.

Simplify using `only [hgy0, hiso']`. Establish `hhP : ∀ v, h (P v) = A.P0 (gam v)` using `fun v => by simpa [hgam] using hh (e₀ v)`. Establish `hP0 : ∀ v, A.Pw 0 v = A.P0 v` using `fun v => by simp [AnArc.Pw_apply]`. Establish `hHw : ∀ z z', A.Hw 0 (h z) (h z') = hermForm Hm z z'` using `sesq_ext (S := (A.Hw 0 ∘ₗ h.toLinearMap).compl₂ h.toLinearMap) (S' := sesq Hm) hspan fun v v' => by show (A.Hw 0 (h (P v)) (h (P v'))).im = (hermForm Hm (P v) (P v')).im`. Rewrite using `[hhP, hhP, ← hP0, ← hP0, A.im_Hw_Pw hB, hiso', hHm]`.

Establish `himg : h '' (P '' Hh) = Set.range fun n => A.P0 (AnArc.La.mk 0 n 0)`. Use extensionality with `v`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨t, ht, rfl⟩, rfl⟩`. Take `⟨n, hn⟩` from `(hgH t).1 ht`.

Conclude with `⟨n, by rw [hhP, hn]⟩`. Introduce and unpack `⟨n, rfl⟩`. Conclude with `⟨_, ⟨gam.symm (AnArc.La.mk 0 n 0), (hgH _).2 ⟨n, by simp⟩, rfl⟩, by simp [hhP]⟩`. Establish `hU : ∀ z, A.torusProj (h z) = 0 ↔ ∀ t ∈ Hh, hermForm Hm z (P t) = 0` using `fun z => by`. Rewrite using `[torusProj_eq_zero_iff A hB, ← Set.forall_mem_range (p := fun v => A.Hw 0 (h z) v = 0), ← himg]`.

Simplify using `only [Set.forall_mem_image, hHw, SetLike.mem_coe]`. Establish `hRind : ∀ z, (∀ t ∈ Hh, (sesq Hm z (P t)).im = 0) → ∀ r ∈ Submodule.span ℝ (P '' Hh), (sesq Hm z r).im = 0` using `fun z hz r hr => LinearMap.eqOn_span (f := imForm (sesq Hm) z) (g := 0) (by rintro _ ⟨t, ht, rfl⟩; exact hz t ht) hr`. Establish `him : ∀ z z', (sesq Hm z z').im = -(sesq Hm z' z).im` using `fun z z' => by rw [← hconj z z', conj_im, neg_neg]`. Establish `hperp : ∀ v, y v = 0 → ∀ t ∈ Hh, (sesq Hm (P v) (P t)).im = 0` using `fun v hv t ht => by`. Rewrite using `[him, sesq_apply, hHm, (hker v).1 hv t ht]`.

Simplify using the standard rewrite rules. Establish `hex : ∀ v, y v = 0 → ∃! a, a ∈ Submodule.span ℝ (P '' Hh) ∧ ∀ t ∈ Hh, hermForm Hm (P v - a) (P t) = 0`. Take `⟨b, hb, hb'⟩` from `exists_imPart hpos (R := Submodule.span ℝ (P '' Hh)) fun r hr => hRind r fun t ht => by`. Rewrite using `[him, hRind _ (hperp t ((hker t).2 fun t' ht' => hiso t' ht' t ht)) r hr, neg_zero]`. Use `fun v hv => ⟨b (I • P v), ⟨hb _, fun t ht => ?_⟩, fun a ha => Eq.symm ?_⟩` and prove the remaining obligations.

Rewrite using `[← sesq_apply, map_sub, LinearMap.sub_apply, hb' _ _ (Submodule.subset_span ⟨t, ht, rfl⟩)]`. Apply the tactic sequence `apply Complex.ext <;> simp [hperp v hv t ht]`. Use `imPart_eq hpos hb hb' ha.1 fun r hr => ?_` and prove the remaining obligations. Use `LinearMap.eqOn_span (f := reForm (sesq Hm) (P v - a)) (g := 0) (by rintro _ ⟨t, ht, rfl⟩; exact congrArg Complex.re (ha.2 t ht)) hr` as an intermediate fact. Simplify using `at this ⊢`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hrank : Module.finrank (𝓞 E) A.X = Module.finrank (𝓞 E) Hh`. Establish `h1 : KerPerp.kerPerp hadj y = Hh` using `Submodule.ext fun t => (hHh t).symm`. Establish `h2` using `KerPerp.finrank_kerPerp hadj D.unimod hy`. Use `D.fin` as an intermediate fact.

Establish `: Module.Finite (𝓞 E) Y` using `Module.Finite.of_surjective y hy`. Rewrite `h2` using `[h1, finrank_int_eq_mul_of_finite (O := 𝓞 E), finrank_int_eq_mul_of_finite (O := 𝓞 E) (M := Y)]`. Rewrite using `[e.finrank_eq, Nat.eq_of_mul_eq_mul_left Module.finrank_pos h2]`. Use `⟨A, e, gam, h, hbe, hchi, hpsi, hiso', hgy, hgH, hact, hhP, hB, hHw, fun z => ?_, hU, fun u u' hu => ?_, fun l => ⟨fun hl => ?_, ?_⟩, hex, fun k hk x => ?_, hrank, tyB, hF, fun hty => ?_⟩` and prove the remaining obligations. Rewrite using `[snd_eq_zero_iff, ← himg]`.

Conclude with `Submodule.apply_mem_span_image_iff_mem_span (f := h.toLinearMap) h.injective`. Rewrite using `[← hHw, A.Hw_apply, (hU u).2 hu]`. Simplify using the standard rewrite rules. Conclude with `⟨gam.symm (AnArc.La.mk 0 0 ⟨l, hl⟩), (hgy0 _).1 (by simp), by simp [hhP]⟩`. Introduce and unpack `⟨v, hv, rfl⟩`.

Simplify using `[hhP, (hgy0 v).2 hv]`. Use `zsmul_mem_Lam A k _ fun l => ?_` and prove the remaining obligations. Take `⟨v, hv⟩` from `gam.surjective (AnArc.La.mk 0 0 l)`. Establish `hv0 : y v = 0` using `(hgy0 v).1 (by simp [hv])`. Take `⟨a, ⟨ha, ha'⟩, -⟩` from `hex v hv0`.

Take `⟨t, ht, hta⟩` from `hk v hv0 a ha ha'`. Take `⟨n, hn⟩` from `(hgH t).1 ht`. Establish `h1` using `congrArg (fun z => A.torusProj (h z) x) hta`. Establish `h2` using `congrArg (fun r => r x) ((hU _).2 ha')`. Simplify using `only [map_sub, map_zsmul, hhP, hv, hn, AddMonoidHom.sub_apply, AddMonoidHom.smul_apply, AnArc.torusProj_periodZero_eq_real, AddMonoidHom.zero_apply] at h1 h2`.

Rewrite `h1` using `[← sub_eq_zero.1 h2]`. Use `⟨n x, ?_⟩` and prove the remaining obligations. Simplify using `using (congrArg Complex.re h1).symm`. Take `⟨h1, h2, h3⟩` from `ComplementTypes.types E H D.p D.q (Module.finrank (𝓞 E) Hh) g A.gB ty tyB hty fun a => by`. Establish `h4 : A.actV a = h.conj (ρ a)` using `LinearMap.ext fun v => by simp [LinearEquiv.conj_apply, hact]`.

Establish `h5 : ρ a = Matrix.toLin' (Matrix.diagonal fun i => ty i (a : E))` using `LinearMap.ext fun z => funext fun i => by simp [hρ, Matrix.mulVec_diagonal]`. Establish `h6` using `trace_actV A hF a`. Rewrite `h6` using `[h4, LinearMap.trace_conj', h5, hrank]`. Use `Eq.trans ?_ h6` and prove the remaining obligations. Simplify using the standard rewrite rules.

Conclude with `⟨h1, h2, h3, exists_datum_Lam A _ _ tyB h3 hF⟩`.
-/
theorem exists_anArc_of_period (D : Datum H) {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)}
    (hP : IsPeriod D ty P) {Hm : Matrix (Fin g) (Fin g) ℂ} (hHm : ∀ x y, (hermForm Hm (P x) (P y)).im = D.EF x y)
    (Hh : Submodule (𝓞 E) D.La) (hsat : ∀ (k : ℤ) (t : D.La), k ≠ 0 → k • t ∈ Hh → t ∈ Hh)
    (hiso : ∀ t ∈ Hh, ∀ t' ∈ Hh, D.EF t t' = 0)
    {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y] (y : D.La →ₗ[𝓞 E] Y) (hy : Function.Surjective y)
    (hker : ∀ v, y v = 0 ↔ ∀ t ∈ Hh, D.EF t v = 0)
    (be : LinearMap.BilinForm ℤ Y) (be_symm : ∀ x x', be x x' = be x' x) (be_pos : ∀ x, x ≠ 0 → 0 < be x x)
    (be_adj : ∀ (a : 𝓞 E) x x', be (a • x) x' = be x (H.bar a • x')) (be_even : ∀ x, (2 : ℤ) ∣ be x x) :
    letI := H.starRing
    ∃ (A : AnArc (𝓞 E)) (e : A.X ≃ₗ[𝓞 E] Y) (gam : D.La ≃ₗ[𝓞 E] A.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] A.V),
      (∀ x x', A.be x x' = be (e x) (e x')) ∧
      (∀ l, A.chi l = (-1) ^ A.Ef (A.FLam H.w0 l) l) ∧
      (∀ x, (A.psi x : ℂ) = eTwoPi (A.T x (H.w0 • x))) ∧
      (∀ v v', A.EF (gam v) (gam v') = D.EF v v') ∧
      (∀ v, e (gam v).y = y v) ∧
      (∀ v, v ∈ Hh ↔ ∃ n, gam v = AnArc.La.mk 0 n 0) ∧
      (∀ (a : 𝓞 E) z, h (fun i => ty i (a : E) * z i) = A.actV a (h z)) ∧
      (∀ v, h (P v) = A.P0 (gam v)) ∧
      (A.BwMat 0).PosDef ∧
      (∀ z z', A.Hw 0 (h z) (h z') = hermForm Hm z z') ∧
      (∀ z, (h z).2 = 0 ↔ z ∈ Submodule.span ℂ (P '' Hh)) ∧
      (∀ z, A.torusProj (h z) = 0 ↔ ∀ t ∈ Hh, hermForm Hm z (P t) = 0) ∧
      (∀ u u', (∀ t ∈ Hh, hermForm Hm u (P t) = 0) → A.H (h u).2 (h u').2 = hermForm Hm u u') ∧
      (∀ l, l ∈ A.abelian₂ ↔ ∃ v, y v = 0 ∧ (h (P v)).2 = l) ∧
      (∀ v, y v = 0 → ∃! a, a ∈ Submodule.span ℝ (P '' Hh) ∧ ∀ t ∈ Hh, hermForm Hm (P v - a) (P t) = 0) ∧
      (∀ k : ℤ, (∀ v, y v = 0 → ∀ a ∈ Submodule.span ℝ (P '' Hh), (∀ t ∈ Hh, hermForm Hm (P v - a) (P t) = 0) →
        k • a ∈ P '' Hh) → ∀ x, k • A.ct x ∈ A.abelian₂) ∧
      Module.finrank (𝓞 E) A.X = Module.finrank (𝓞 E) Hh ∧
      ∃ tyB : Fin A.gB → (E →+* ℂ), (∀ a z i, A.F a z i = tyB i (a : E) * z i) ∧
        (IsTypeFn H D.p D.q ty → Module.finrank (𝓞 E) Hh ≤ D.p ∧ Module.finrank (𝓞 E) Hh ≤ D.q ∧
          IsTypeFn H (D.p - Module.finrank (𝓞 E) Hh) (D.q - Module.finrank (𝓞 E) Hh) tyB ∧
          ∃ (DB : Datum H) (eB : DB.La ≃+ A.abelian₂), DB.p = D.p - Module.finrank (𝓞 E) Hh ∧
            DB.q = D.q - Module.finrank (𝓞 E) Hh ∧ (∀ (a : 𝓞 E) x, eB (a • x) = A.FLam a (eB x)) ∧
            (∀ x x', DB.EF x x' = A.Ef (eB x) (eB x')) ∧
            IsPeriod DB tyB (A.abelian₂.subtype.toAddMonoidHom.comp eB.toAddMonoidHom)) := by
  let _ := H.starRing
  obtain ⟨hlin, hinj, hdisc, hspan, Hm', hherm, hpos', hHm'⟩ := hP
  have hS : ∀ z z', sesq Hm z z' = sesq Hm' z z' := sesq_ext hspan fun i k => (hHm i k).trans (hHm' i k).symm
  have hconj : ∀ z z', starRingEnd ℂ (sesq Hm z z') = sesq Hm z' z := fun z z' => by
    rw [hS, hS, sesq_conj hherm]
  have hpos : ∀ z, z ≠ 0 → 0 < (sesq Hm z z).re := fun z hz => by rw [hS]; exact hpos' z hz
  have hw : H.w0 + star H.w0 = 1 := by
    show H.w0 + H.bar H.w0 = 1
    rw [HostModel.cmHost_bar_halfIntegerGenerator, add_sub_cancel]
  have hadj : ∀ (a : 𝓞 E) x x', D.EF (a • x) x' = D.EF x (star a • x') := D.adj
  have halt : D.EF.IsAlt := D.alt
  obtain ⟨hfin, hrk, -⟩ := PeriodDatum.lattice_equiv P hinj hdisc hspan
  have : Module.IsTorsionFree ℤ D.La := hinj.moduleIsTorsionFree _ (map_zsmul P)
  have : Module.Finite ℤ Y := Module.Finite.of_surjective y.toAddMonoidHom.toIntLinearMap hy
  have : Module.IsTorsionFree ℤ Y := Module.IsTorsionFree.of_smul_eq_zero fun k x hx => by
    obtain ⟨v, rfl⟩ := hy x
    refine or_iff_not_imp_left.2 fun hk => (hker v).2 fun t ht => ?_
    simpa [hk] using (hker (k • v)).1 (by rw [map_zsmul, hx]) t ht
  have : Module.Free ℤ Y := Module.free_of_finite_type_torsion_free'
  have := Forms.projective_of_int (𝓞 E) Y
  have hHh : ∀ t, t ∈ Hh ↔ ∀ v, y v = 0 → D.EF t v = 0 := fun t => by
    have : Module.Finite ℤ (D.La ⧸ Hh) :=
      Module.Finite.of_surjective Hh.mkQ.toAddMonoidHom.toIntLinearMap Hh.mkQ_surjective
    have : Module.IsTorsionFree ℤ (D.La ⧸ Hh) := Module.IsTorsionFree.of_smul_eq_zero fun k x hx => by
      obtain ⟨v, rfl⟩ := Hh.mkQ_surjective x
      refine or_iff_not_imp_left.2 fun hk => (Submodule.Quotient.mk_eq_zero _).2 (hsat k v hk ?_)
      exact (Submodule.Quotient.mk_eq_zero _).1 ((map_zsmul Hh.mkQ k v).trans hx)
    have : Module.Free ℤ (D.La ⧸ Hh) := Module.free_of_finite_type_torsion_free'
    refine ⟨fun ht v hv => (hker v).1 hv t ht, fun ht => (Submodule.Quotient.mk_eq_zero _).1 ?_⟩
    refine (KerPerp.ker_iff (hadj := hadj) (y := Hh.mkQ) D.unimod.2 t).2 fun v hv => ?_
    exact halt.eq_iff.1 (ht v ((hker v).2 fun t' ht' =>
      halt.eq_iff.1 (hv t' ((Submodule.Quotient.mk_eq_zero _).2 ht'))))
  obtain ⟨M, _, _, EM, e₀, hEM, he₁, he₂, he₃, hE⟩ := exists_split_of_coisotropic_ker (𝓞 E) D.La Y H.w0 D.EF y hw D.alt
    D.unimod hadj hy fun t ht => (hker t).2 fun t' ht' => hiso t' ht' t ((hHh t).2 ht)
  have : Module.Finite ℤ M := Module.Finite.of_surjective
    ((AddMonoidHom.snd _ _).comp ((AddMonoidHom.snd _ _).comp e₀.toAddMonoidHom)).toIntLinearMap
    fun m => ⟨e₀.symm (0, 0, m), by simp⟩
  have : Module.IsTorsionFree ℤ M := Function.Injective.moduleIsTorsionFree (fun m : M => e₀.symm (0, 0, m))
    (fun m m' hm => by simpa using hm) fun k m => by rw [← map_zsmul]; simp
  have : Module.Free ℤ M := Module.free_of_finite_type_torsion_free'
  have hrk' : 2 * Module.finrank ℤ Y + Module.finrank ℤ M = 2 * Module.finrank ℂ (Fin g → ℂ) := by
    have : Module.Finite ℤ (Y →+ ℤ) := Module.Finite.equiv (addMonoidHomLequivInt ℤ (A := Y) (B := ℤ)).symm
    have : Module.Free ℤ (Y →+ ℤ) := Module.Free.of_equiv (addMonoidHomLequivInt ℤ (A := Y) (B := ℤ)).symm
    rw [e₀.toIntLinearEquiv.finrank_eq, Module.finrank_prod, Module.finrank_prod, finrank_hom_int] at hrk
    rw [Module.finrank_fin_fun]
    omega
  let ρ : 𝓞 E →+* Module.End ℂ (Fin g → ℂ) :=
    { toFun := fun a => LinearMap.pi fun i => ty i (a : E) • LinearMap.proj i
      map_one' := by ext; simp
      map_mul' := fun _ _ => LinearMap.ext fun z => funext fun i => by simp [mul_assoc]
      map_zero' := by ext; simp
      map_add' := fun _ _ => LinearMap.ext fun z => funext fun i => by simp [add_mul] }
  have hρ : ∀ a z, ρ a z = fun i => ty i (a : E) * z i := fun _ _ => rfl
  have hPρ : ∀ a v, P (a • v) = ρ a (P v) := fun a v => funext (hlin a v)
  have hρS : ∀ a z z', sesq Hm (ρ a z) z' = sesq Hm z (ρ (star a) z') := fun a =>
    sesq_ext (S := sesq Hm ∘ₗ ρ a) (S' := (sesq Hm).compl₂ (ρ (star a))) hspan fun v v' => by
      show (hermForm Hm (ρ a (P v)) (P v')).im = (hermForm Hm (P v) (ρ (star a) (P v'))).im
      rw [← hPρ, ← hPρ, hHm, hHm, hadj]
  have he : ∀ (a : 𝓞 E) v, e₀ (a • v) =
      (a • (e₀ v).1, (e₀ v).2.1.comp (DistribSMul.toAddMonoidHom Y (star a)), a • (e₀ v).2.2) := fun a v =>
    Prod.ext (by rw [he₁, he₁, map_smul]) (Prod.ext (AddMonoidHom.ext (he₂ a v)) (he₃ a v))
  obtain ⟨A, e, f, h, hbe, hchi, hpsi, ⟨tyB, hF⟩, hfF, hEf, hact, hh, hB⟩ := exists_arc hw EM hEM
    (P.comp e₀.symm.toAddMonoidHom)
    ((congrArg _ (e₀.symm.surjective.range_comp P)).trans hspan) hrk' hconj hpos
    (fun v v' => by
      show (hermForm Hm (P (e₀.symm v)) (P (e₀.symm v'))).im = _
      rw [hHm, hE, e₀.apply_symm_apply, e₀.apply_symm_apply]) ρ hρS
    (fun a v => by
      obtain ⟨v, rfl⟩ := e₀.surjective v
      rw [← he]
      simp [hPρ]) be be_symm be_pos be_adj be_even
    (fun n F => ∃ ty : Fin n → (E →+* ℂ), ∀ a z i, F a z i = ty i (a : E) * z i) exists_diag
  let gam : D.La ≃ₗ[𝓞 E] A.La :=
    { toFun := fun v => AnArc.La.mk (e.symm (e₀ v).1) ((e₀ v).2.1.comp e.toAddEquiv.toAddMonoidHom) (f (e₀ v).2.2)
      invFun := fun v => e₀.symm (e v.y, v.n.comp e.symm.toAddEquiv.toAddMonoidHom, f.symm v.l)
      map_add' := fun v v' => by ext <;> simp
      map_smul' := fun a v => by ext <;> simp [he, hfF]
      left_inv := fun v => e₀.injective (by ext <;> simp)
      right_inv := fun v => by ext <;> simp }
  have hgam : ∀ v, gam v =
      AnArc.La.mk (e.symm (e₀ v).1) ((e₀ v).2.1.comp e.toAddEquiv.toAddMonoidHom) (f (e₀ v).2.2) := fun _ => rfl
  have hiso' : ∀ v v', A.EF (gam v) (gam v') = D.EF v v' := fun v v' => by
    simp [hgam, AnArc.EF_apply, hEf, hE]
  have hgy : ∀ v, e (gam v).y = y v := fun v => by simp [hgam, he₁]
  have hgy0 : ∀ v, (gam v).y = 0 ↔ y v = 0 := fun v => by rw [← hgy, e.map_eq_zero_iff]
  have hgH : ∀ v, v ∈ Hh ↔ ∃ n, gam v = AnArc.La.mk 0 n 0 := fun v => by
    rw [hHh, ← A.orth_ker_iff_exists, gam.surjective.forall]
    simp only [hgy0, hiso']
  have hhP : ∀ v, h (P v) = A.P0 (gam v) := fun v => by simpa [hgam] using hh (e₀ v)
  have hP0 : ∀ v, A.Pw 0 v = A.P0 v := fun v => by simp [AnArc.Pw_apply]
  have hHw : ∀ z z', A.Hw 0 (h z) (h z') = hermForm Hm z z' :=
    sesq_ext (S := (A.Hw 0 ∘ₗ h.toLinearMap).compl₂ h.toLinearMap) (S' := sesq Hm) hspan fun v v' => by
      show (A.Hw 0 (h (P v)) (h (P v'))).im = (hermForm Hm (P v) (P v')).im
      rw [hhP, hhP, ← hP0, ← hP0, A.im_Hw_Pw hB, hiso', hHm]
  have himg : h '' (P '' Hh) = Set.range fun n => A.P0 (AnArc.La.mk 0 n 0) := by
    ext v
    constructor
    · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
      obtain ⟨n, hn⟩ := (hgH t).1 ht
      exact ⟨n, by rw [hhP, hn]⟩
    · rintro ⟨n, rfl⟩
      exact ⟨_, ⟨gam.symm (AnArc.La.mk 0 n 0), (hgH _).2 ⟨n, by simp⟩, rfl⟩, by simp [hhP]⟩
  have hU : ∀ z, A.torusProj (h z) = 0 ↔ ∀ t ∈ Hh, hermForm Hm z (P t) = 0 := fun z => by
    rw [torusProj_eq_zero_iff A hB, ← Set.forall_mem_range (p := fun v => A.Hw 0 (h z) v = 0), ← himg]
    simp only [Set.forall_mem_image, hHw, SetLike.mem_coe]
  have hRind : ∀ z, (∀ t ∈ Hh, (sesq Hm z (P t)).im = 0) → ∀ r ∈ Submodule.span ℝ (P '' Hh), (sesq Hm z r).im = 0 :=
    fun z hz r hr => LinearMap.eqOn_span (f := imForm (sesq Hm) z) (g := 0) (by rintro _ ⟨t, ht, rfl⟩; exact hz t ht) hr
  have him : ∀ z z', (sesq Hm z z').im = -(sesq Hm z' z).im := fun z z' => by rw [← hconj z z', conj_im, neg_neg]
  have hperp : ∀ v, y v = 0 → ∀ t ∈ Hh, (sesq Hm (P v) (P t)).im = 0 := fun v hv t ht => by
    rw [him, sesq_apply, hHm, (hker v).1 hv t ht]; simp
  have hex : ∀ v, y v = 0 → ∃! a, a ∈ Submodule.span ℝ (P '' Hh) ∧ ∀ t ∈ Hh, hermForm Hm (P v - a) (P t) = 0 := by
    obtain ⟨b, hb, hb'⟩ := exists_imPart hpos (R := Submodule.span ℝ (P '' Hh)) fun r hr => hRind r fun t ht => by
      rw [him, hRind _ (hperp t ((hker t).2 fun t' ht' => hiso t' ht' t ht)) r hr, neg_zero]
    refine fun v hv => ⟨b (I • P v), ⟨hb _, fun t ht => ?_⟩, fun a ha => Eq.symm ?_⟩
    · rw [← sesq_apply, map_sub, LinearMap.sub_apply, hb' _ _ (Submodule.subset_span ⟨t, ht, rfl⟩)]
      apply Complex.ext <;> simp [hperp v hv t ht]
    · refine imPart_eq hpos hb hb' ha.1 fun r hr => ?_
      have := LinearMap.eqOn_span (f := reForm (sesq Hm) (P v - a)) (g := 0)
        (by rintro _ ⟨t, ht, rfl⟩; exact congrArg Complex.re (ha.2 t ht)) hr
      simp at this ⊢
      linarith
  have hrank : Module.finrank (𝓞 E) A.X = Module.finrank (𝓞 E) Hh := by
    have h1 : KerPerp.kerPerp hadj y = Hh := Submodule.ext fun t => (hHh t).symm
    have h2 := KerPerp.finrank_kerPerp hadj D.unimod hy
    have := D.fin
    have : Module.Finite (𝓞 E) Y := Module.Finite.of_surjective y hy
    rw [h1, finrank_int_eq_mul_of_finite (O := 𝓞 E), finrank_int_eq_mul_of_finite (O := 𝓞 E) (M := Y)] at h2
    rw [e.finrank_eq, Nat.eq_of_mul_eq_mul_left Module.finrank_pos h2]
  refine ⟨A, e, gam, h, hbe, hchi, hpsi, hiso', hgy, hgH, hact, hhP, hB, hHw, fun z => ?_, hU, fun u u' hu => ?_,
    fun l => ⟨fun hl => ?_, ?_⟩, hex, fun k hk x => ?_, hrank, tyB, hF, fun hty => ?_⟩
  · rw [snd_eq_zero_iff, ← himg]
    exact Submodule.apply_mem_span_image_iff_mem_span (f := h.toLinearMap) h.injective
  · rw [← hHw, A.Hw_apply, (hU u).2 hu]; simp
  · exact ⟨gam.symm (AnArc.La.mk 0 0 ⟨l, hl⟩), (hgy0 _).1 (by simp), by simp [hhP]⟩
  · rintro ⟨v, hv, rfl⟩
    simp [hhP, (hgy0 v).2 hv]
  · refine zsmul_mem_Lam A k _ fun l => ?_
    obtain ⟨v, hv⟩ := gam.surjective (AnArc.La.mk 0 0 l)
    have hv0 : y v = 0 := (hgy0 v).1 (by simp [hv])
    obtain ⟨a, ⟨ha, ha'⟩, -⟩ := hex v hv0
    obtain ⟨t, ht, hta⟩ := hk v hv0 a ha ha'
    obtain ⟨n, hn⟩ := (hgH t).1 ht
    have h1 := congrArg (fun z => A.torusProj (h z) x) hta
    have h2 := congrArg (fun r => r x) ((hU _).2 ha')
    simp only [map_sub, map_zsmul, hhP, hv, hn, AddMonoidHom.sub_apply, AddMonoidHom.smul_apply,
      AnArc.torusProj_periodZero_eq_real, AddMonoidHom.zero_apply] at h1 h2
    rw [← sub_eq_zero.1 h2] at h1
    refine ⟨n x, ?_⟩
    simpa using (congrArg Complex.re h1).symm
  · obtain ⟨h1, h2, h3⟩ := ComplementTypes.types E H D.p D.q (Module.finrank (𝓞 E) Hh) g A.gB ty tyB hty fun a => by
      have h4 : A.actV a = h.conj (ρ a) := LinearMap.ext fun v => by simp [LinearEquiv.conj_apply, hact]
      have h5 : ρ a = Matrix.toLin' (Matrix.diagonal fun i => ty i (a : E)) :=
        LinearMap.ext fun z => funext fun i => by simp [hρ, Matrix.mulVec_diagonal]
      have h6 := trace_actV A hF a
      rw [h4, LinearMap.trace_conj', h5, hrank] at h6
      refine Eq.trans ?_ h6
      simp
    exact ⟨h1, h2, h3, exists_datum_Lam A _ _ tyB h3 hF⟩

open HostModel in

/- English proof (translation)
Take `⟨P, hP⟩` from `PeriodNonempty.exists_isPeriod E H (hypDatum H) g ty hty`. Take `⟨Hm, -, -, hHm⟩` from `hP.2.2.2.2`. Take `⟨A, e, gam, h, -, -, -, -, -, -, -, hh, -⟩` from `exists_anArc_of_period (hypDatum H) hP hHm (LinearMap.ker (LinearMap.fst _ _ _)) (fun k t hk ht => by simpa [hk] using ht) (fun t ht t' ht' => by simp [show t.1 = 0 from ht, show t'.1 = 0 from ht']) (LinearMap.fst _ _ _) LinearMap.fst_surjective (fun v => ⟨fun hv t ht => by simp …`. Simplify using `using hv (0, (ConjDual.toDual H).symm φ) rfl⟩)`. Use the proof step `((2 : ℤ) • trForm H) (fun x x' => congrArg (2 * ·) (trForm_symm H x x'))`.

Use the proof step `(fun x hx => mul_pos two_pos (trForm_pos H hx)) (fun a x x' => congrArg (2 * ·) (trForm_adj H a x x'))`. Use `fun x => ⟨_, rfl⟩`. Conclude with `⟨P, A, e, gam, h, hP, hh⟩`.
-/
example (H : Host E) {g : ℕ} {ty : Fin g → (E →+* ℂ)} (hty : IsTypeFn H 1 1 ty) : letI := H.starRing
    ∃ (P : (hypDatum H).La →+ (Fin g → ℂ)) (A : AnArc (𝓞 E)) (_ : A.X ≃ₗ[𝓞 E] 𝓞 E)
      (gam : (hypDatum H).La ≃ₗ[𝓞 E] A.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] A.V),
      IsPeriod (hypDatum H) ty P ∧ ∀ v, h (P v) = A.P0 (gam v) := by
  obtain ⟨P, hP⟩ := PeriodNonempty.exists_isPeriod E H (hypDatum H) g ty hty
  obtain ⟨Hm, -, -, hHm⟩ := hP.2.2.2.2
  obtain ⟨A, e, gam, h, -, -, -, -, -, -, -, hh, -⟩ := exists_anArc_of_period (hypDatum H) hP hHm
    (LinearMap.ker (LinearMap.fst _ _ _)) (fun k t hk ht => by simpa [hk] using ht)
    (fun t ht t' ht' => by simp [show t.1 = 0 from ht, show t'.1 = 0 from ht'])
    (LinearMap.fst _ _ _) LinearMap.fst_surjective
    (fun v => ⟨fun hv t ht => by simp [show t.1 = 0 from ht, show v.1 = 0 from hv],
      fun hv => (Module.forall_dual_apply_eq_zero_iff ℤ v.1).1 fun φ => by
        simpa using hv (0, (ConjDual.toDual H).symm φ) rfl⟩)
    ((2 : ℤ) • trForm H) (fun x x' => congrArg (2 * ·) (trForm_symm H x x'))
    (fun x hx => mul_pos two_pos (trForm_pos H hx)) (fun a x x' => congrArg (2 * ·) (trForm_adj H a x x'))
    fun x => ⟨_, rfl⟩
  exact ⟨P, A, e, gam, h, hP, hh⟩

end GlobalTheory.OfPeriod
