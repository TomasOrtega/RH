import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.OrthXflagMaps

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.Pf.FibreCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Rel

variable {D : D7} {X : HidaSetting D} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
  {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)} {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V}

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, Formalism.L2.SG.TermDef.one_mem_NLam _ _, 1, Formalism.L2.SG.TermDef.one_mem_NLam _ _, by simp⟩ symm := by rintro p q ⟨n, hn, n', hn', h⟩ exact ⟨n⁻¹, Formalism.L2.SG.Pf.nlamPf_inv hn, n'⁻¹, Formalism.L2.SG.Pf.nlamPf_inv hn', by rw [h]; group⟩ trans := by rintro p q w ⟨n, hn, …`.
-/
theorem grel_equiv : Equivalence (GRel X u u' F0 F0' Λ Λ') where
  refl _ := ⟨1, Formalism.L2.SG.TermDef.one_mem_NLam _ _, 1, Formalism.L2.SG.TermDef.one_mem_NLam _ _, by simp⟩
  symm := by
    rintro p q ⟨n, hn, n', hn', h⟩
    exact ⟨n⁻¹, Formalism.L2.SG.Pf.nlamPf_inv hn, n'⁻¹, Formalism.L2.SG.Pf.nlamPf_inv hn', by rw [h]; group⟩
  trans := by
    rintro p q w ⟨n, hn, n', hn', h⟩ ⟨m, hm, m', hm', h'⟩
    exact ⟨m * n, Formalism.L2.SG.Pf.nlamPf_mul hm hn, n' * m', Formalism.L2.SG.Pf.nlamPf_mul hn' hm', by rw [h', h]; group⟩

/- English proof (translation)
Establish `e : Quot.mk (GRel X u u' F0 F0' s.lam s.lam') p = Quot.mk _ (Quot.out s.cls)` using `h.symm.trans (Quot.out_eq _).symm`. Conclude with `grel_equiv.eqvGen_iff.1 (Quot.eqvGen_exact e)`.
-/
theorem lin_of_cls {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (s : GTerm X u u' F0 F0' what₂ rows')
    (p : GCar X u u' F0 F0' s.lam s.lam') (h : s.cls = Quot.mk _ p) :
    ∃ n ∈ NLam s.lam (lf D F0), ∃ n' ∈ NLam s.lam' (lf D F0'), s.lin = n * p.1.2 * n' := by
  have e : Quot.mk (GRel X u u' F0 F0' s.lam s.lam') p = Quot.mk _ (Quot.out s.cls) :=
    h.symm.trans (Quot.out_eq _).symm
  exact grel_equiv.eqvGen_iff.1 (Quot.eqvGen_exact e)

end Rel

section WD

variable {D : D7} {T T' : D.host.E} {F : FlagG (VS D) D.R.rS T} (F0' : FlagG (VS D) D.R.rS T')

/- English proof (translation)
Rewrite using `[Formalism.L2.SG.Pf.mem_orth_iff_td]`. Both sides reduce to the same expression.
-/
theorem perp_iff_orth {y : (VS D).V} : y ∈ perpS (VS D) F0'.X ↔ y ∈ orth (VS D) (Xsp (lf D F0')) := by
  rw [Formalism.L2.SG.Pf.mem_orth_iff_td]; rfl

variable {F0'}

/- English proof (translation)
Introduce `y hy`. Establish `h` using `Formalism.L2.SG.Pf.nlam_mapsTo hν D.R.rS y (by rw [Formalism.L2.SG.Pf.xflag_r]; exact hy)`. Rewrite `h` using `[Formalism.L2.SG.Pf.xflag_r]`. Then use the resulting hypothesis.
-/
theorem nlam_X {Λ₀ : Submodule (𝓞 D.host.E) (VS D).V} {ν : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hν : ν ∈ NLam Λ₀ (lf D F0')) : ∀ y ∈ F0'.X, ν y ∈ F0'.X := by
  intro y hy
  have h := Formalism.L2.SG.Pf.nlam_mapsTo hν D.R.rS y (by rw [Formalism.L2.SG.Pf.xflag_r]; exact hy)
  rwa [Formalism.L2.SG.Pf.xflag_r] at h

/- English proof (translation)
Introduce `y hy`. Rewrite `hy`, the goal using `[perp_iff_orth]`. Conclude with `Formalism.L2.SG.Pf.nlam_orth_mapsTo hν y hy`.
-/
theorem nlam_P {Λ₀ : Submodule (𝓞 D.host.E) (VS D).V} {ν : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hν : ν ∈ NLam Λ₀ (lf D F0')) : ∀ y ∈ perpS (VS D) F0'.X, ν y ∈ perpS (VS D) F0'.X := by
  intro y hy
  rw [perp_iff_orth] at hy ⊢
  exact Formalism.L2.SG.Pf.nlam_orth_mapsTo hν y hy

/- English proof (translation)
Introduce `y hy` and use `hν.2.2 y ((perp_iff_orth F0').1 hy)`.
-/
theorem nlam_triv {Λ₀ : Submodule (𝓞 D.host.E) (VS D).V} {ν : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hν : ν ∈ NLam Λ₀ (lf D F0')) : ∀ y ∈ perpS (VS D) F0'.X, ν y - y ∈ F0'.X :=
  fun y hy => hν.2.2 y ((perp_iff_orth F0').1 hy)

/- English proof (translation)
Use `LinearMap.ext fun w => ?_` and prove the remaining obligations. Proceed by induction on `w using Submodule.Quotient.induction_on with`. Consider the case `H x`. Rewrite using `[indL_mk, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero]`. Use `show f x ∈ F0'.X`.

Rewrite using `[h]`. Conclude with `zero_mem _`.
-/
theorem indL_zero (f : (VS D).V →ₗ[D.host.E] (VS D).V) (hP : ∀ y ∈ perpS (VS D) F0'.X, f y ∈ perpS (VS D) F0'.X)
    (hX : ∀ y ∈ F0'.X, f y ∈ F0'.X) (h : ∀ y, f y = 0) : indL F0' f hP hX = 0 := by
  refine LinearMap.ext fun w => ?_
  induction w using Submodule.Quotient.induction_on with
  | H x =>
    rw [indL_mk, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero]
    show f x ∈ F0'.X
    rw [h]; exact zero_mem _

/- English proof (translation)
Use `set d := c' * c⁻¹ with hddef`. Establish `hd : d ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT` using `Subgroup.mul_mem _ hc' (Subgroup.inv_mem _ hc)`. Establish `hdfix : ∀ a, d (F0'.fvec a) = F0'.fvec a`. Introduce `a`. Use `show c' (c⁻¹ _) = _`.

Rewrite using `[inv_fix F0' hfix a, hfix' a]`. Establish `hdg : Formalism.HermitianLatticesTheory.gmap d Λ₀ = Λ₀`. Rewrite using `[hddef, Formalism.L2.SG.Pf.gmap_mul_sat, gmap_inv_of hg, hg']`. Use `set g := γ₀⁻¹ * (n'⁻¹ * n) * γ₀ with hgdef`. Establish `hgd : g = ν' * d * ν⁻¹`.

Combine the equalities or inequalities in the displayed calculation. Establish `hnil : ((g : (VS D).V →ₗ[D.host.E] (VS D).V) - 1) ^ (2 * D.R.rS + 1) = 0` using `conj_nilp (Formalism.L2.SG.Pf.nlamPf_mul (Formalism.L2.SG.Pf.nlamPf_inv hn') hn) γ₀`. Establish `hdP` using `perp_maps F0' hd hdfix`. Establish `hdX : ∀ y ∈ F0'.X, d y ∈ F0'.X` using `fun y hy => by rw [fix_X F0' hdfix y hy]; exact hy`. Establish `hνi` using `Formalism.L2.SG.Pf.nlamPf_inv hν`.

Establish `hgapp : ∀ y, g y = ν' (d (ν⁻¹ y))` using `fun y => by rw [hgd]; rfl`. Establish `hgP : ∀ y ∈ perpS (VS D) F0'.X, g y ∈ perpS (VS D) F0'.X` using `fun y hy => by`. Rewrite using `[hgapp]`. Conclude with `nlam_P hν' _ (hdP _ (nlam_P hνi _ hy))`. Establish `hgX : ∀ y ∈ F0'.X, g y ∈ F0'.X` using `fun y hy => by`.

Rewrite using `[hgapp]`. Conclude with `nlam_X hν' _ (hdX _ (nlam_X hνi _ hy))`. Establish `hgdX : ∀ y ∈ perpS (VS D) F0'.X, g y - d y ∈ F0'.X`. Introduce `y hy`. Establish `ha` using `nlam_triv hνi y hy`.

Establish `e1 : d (ν⁻¹ y) = d y + (ν⁻¹ y - y)`. Establish `: ν⁻¹ y = y + (ν⁻¹ y - y)` using `by abel`. Use `conv_lhs => rw [this]`. Rewrite using `[map_add, fix_X F0' hdfix _ ha]`. Establish `e2 : g y - d y = (ν' (d y) - d y) + ν' (ν⁻¹ y - y)`.

Rewrite using `[hgapp, e1, map_add]`. Normalize the expressions using the abelian group laws. Rewrite using `[e2]`. Conclude with `add_mem (nlam_triv hν' _ (hdP y hy)) (nlam_X hν' _ ha)`. Establish `hg1P : ∀ y ∈ perpS (VS D) F0'.X, ((g : (VS D).V →ₗ[D.host.E] (VS D).V) - 1) y ∈ perpS (VS D) F0'.X` using `fun y hy => by`.

Rewrite using `[LinearMap.sub_apply, Module.End.one_apply]`. Conclude with `sub_mem (hgP y hy) hy`. Establish `hg1X : ∀ y ∈ F0'.X, ((g : (VS D).V →ₗ[D.host.E] (VS D).V) - 1) y ∈ F0'.X` using `fun y hy => by`. Rewrite using `[LinearMap.sub_apply, Module.End.one_apply]`. Conclude with `sub_mem (hgX y hy) hy`.

Use `set TD := indL F0' (d : (VS D).V →ₗ[D.host.E] (VS D).V) hdP hdX with hTD`. Establish `hTD1 : TD - 1 = indL F0' ((g : (VS D).V →ₗ[D.host.E] (VS D).V) - 1) hg1P hg1X`. Use `LinearMap.ext fun w => ?_` and prove the remaining obligations. Proceed by induction on `w using Submodule.Quotient.induction_on with`. Consider the case `H x`.

Rewrite using `[LinearMap.sub_apply, Module.End.one_apply, hTD, indL_mk, indL_mk, ← Submodule.Quotient.mk_sub, Submodule.Quotient.eq]`. Use `show (d x - x) - (g x - x) ∈ F0'.X`. Establish `: (d x - x) - (g x - x) = -(g x - d x)` using `by abel`. Rewrite using `[this]`. Conclude with `neg_mem (hgdX x x.2)`.

Establish `hTDnil : (TD - 1) ^ (2 * D.R.rS + 1) = 0`. Rewrite using `[hTD1, indL_pow]`. Conclude with `indL_zero _ _ _ (fun y => by rw [hnil]; rfl)`. Establish `hdpow : ∀ i : ℕ, d ^ i ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧ (∀ a, (d ^ i) (F0'.fvec a) = F0'.fvec a) ∧ Formalism.HermitianLatticesTheory.gmap (d ^ i) Λ₀ = Λ₀`. Introduce `i`.

Proceed by induction on `i with`. Consider the case `zero => exact ⟨Subgroup.one_mem _, fun a => rfl, Formalism.L2.SG.Pf.gmap_one_sat _⟩`. Consider the case `succ i ih`. Use `⟨by rw [pow_succ]; exact Subgroup.mul_mem _ ih.1 hd, fun a => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_succ, LinearEquiv.mul_apply, hdfix, ih.2.1]`.

Rewrite using `[pow_succ, Formalism.L2.SG.Pf.gmap_mul_sat, hdg, ih.2.2]`. Establish `hTDpow : ∀ (i : ℕ) (x : perpS (VS D) F0'.X), (TD ^ i) (Submodule.Quotient.mk x) = Submodule.Quotient.mk ⟨(d ^ i) x, perp_maps F0' (hdpow i).1 (hdpow i).2.1 _ x.2⟩`. Introduce `i`. Proceed by induction on `i with`. Consider the case `zero => intro x`.

Both sides reduce to the same expression. Consider the case `succ i ih`. Introduce `x`. Rewrite using `[pow_succ, Module.End.mul_apply, hTD, indL_mk, ← hTD, ih]`. Both sides reduce to the same expression.

Establish `hmem : ∀ i : ℕ, ⇑(TD ^ i) ∈ autLz D F0' Λ₀` using `fun i => ⟨d ^ i, stabF_of_fix F0' (hdpow i).1 (hdpow i).2.1, (hdpow i).2.2, fun x _ => hTDpow i x⟩`. Take `⟨i, j, hij, hφ⟩` from `Finite.exists_ne_map_eq_of_infinite (fun i : ℕ => (⟨⇑(TD ^ i), hmem i⟩ : autLz D F0' Λ₀))`. Establish `hpow : TD ^ i = TD ^ j` using `LinearMap.coe_injective (congrArg Subtype.val hφ)`. Establish `hunit : IsUnit TD`. Establish `hdiP` using `perp_maps F0' (Subgroup.inv_mem _ hd) (inv_fix F0' hdfix)`.

Establish `hdiX : ∀ y ∈ F0'.X, d⁻¹ y ∈ F0'.X` using `fun y hy => by rw [fix_X F0' (inv_fix F0' hdfix) y hy]; exact hy`. Apply the tactic sequence `refine ⟨⟨TD, indL F0' ((d⁻¹ : (VS D).V ≃ₗ[D.host.E] (VS D).V) : (VS D).V →ₗ[D.host.E] (VS D).V) hdiP hdiX, ?_, ?_⟩, rfl⟩ <;>`. Use `LinearMap.ext fun w => ?_` and prove the remaining obligations. Proceed by induction on `w using Submodule.Quotient.induction_on with`. Consider the case `H x`.

Rewrite using `[Module.End.mul_apply, hTD, indL_mk, indL_mk, Module.End.one_apply]`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[LinearEquiv.coe_inv]`. Establish `hfin : ∃ k, 0 < k ∧ TD ^ k = 1`.

Break down `lt_or_gt_of_ne hij with h | h` into its components or cases. Use `⟨j - i, by omega, ?_⟩` and prove the remaining obligations. Establish `e : TD ^ i * TD ^ (j - i) = TD ^ i * 1` using `by rw [← pow_add, Nat.add_sub_cancel' h.le, mul_one, hpow]`. Conclude with `(hunit.pow i).mul_left_cancel e`. Use `⟨i - j, by omega, ?_⟩` and prove the remaining obligations.

Establish `e : TD ^ j * TD ^ (i - j) = TD ^ j * 1` using `by rw [← pow_add, Nat.add_sub_cancel' h.le, mul_one, hpow]`. Conclude with `(hunit.pow j).mul_left_cancel e`. Take `⟨k, hk, hk1⟩` from `hfin`. Establish `hTD : TD = 1` using `unip_fin TD hk hk1 hTDnil`. Introduce `y hy`.

Establish `hcy` using `perp_maps F0' hc hfix y hy`. Establish `e` using `congrArg (fun A : Module.End D.host.E (WbQ D F0') => A (Submodule.Quotient.mk ⟨c y, hcy⟩)) hTD`. Simplify using `only [Module.End.one_apply] at e`. Rewrite `e` using `[indL_mk, Submodule.Quotient.eq]`. Establish `e3 : c' y = (d : (VS D).V →ₗ[D.host.E] (VS D).V) (c y)`.

Rewrite using `[hddef]`. Simplify using `[LinearEquiv.coe_inv]`. Establish `h3 : c' y - c y ∈ F0'.X`. Use `e` as an intermediate fact. Simplify using `only [Submodule.mem_comap, Submodule.coe_subtype, AddSubgroupClass.coe_sub] at this`.

Rewrite using `[e3]`. Conclude with `this`. Rewrite using `[← neg_sub]`. Conclude with `neg_mem h3`.
-/
theorem wd {Λ Λ₀ : Submodule (𝓞 D.host.E) (VS D).V} {γ₀ n n' ν ν' c c' : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hn : n ∈ NLam Λ (lf D F)) (hn' : n' ∈ NLam Λ (lf D F))
    (hν : ν ∈ NLam Λ₀ (lf D F0')) (hν' : ν' ∈ NLam Λ₀ (lf D F0'))
    (hc : c ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (hc' : c' ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (hg : Formalism.HermitianLatticesTheory.gmap c Λ₀ = Λ₀) (hg' : Formalism.HermitianLatticesTheory.gmap c' Λ₀ = Λ₀)
    (hfix : ∀ a, c (F0'.fvec a) = F0'.fvec a) (hfix' : ∀ a, c' (F0'.fvec a) = F0'.fvec a)
    (he : n * γ₀ * ν * c = n' * γ₀ * ν' * c') [Finite (autLz D F0' Λ₀)] :
    ∀ y ∈ perpS (VS D) F0'.X, c y - c' y ∈ F0'.X := by
  set d := c' * c⁻¹ with hddef
  have hd : d ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := Subgroup.mul_mem _ hc' (Subgroup.inv_mem _ hc)
  have hdfix : ∀ a, d (F0'.fvec a) = F0'.fvec a := by
    intro a; show c' (c⁻¹ _) = _; rw [inv_fix F0' hfix a, hfix' a]
  have hdg : Formalism.HermitianLatticesTheory.gmap d Λ₀ = Λ₀ := by
    rw [hddef, Formalism.L2.SG.Pf.gmap_mul_sat, gmap_inv_of hg, hg']
  set g := γ₀⁻¹ * (n'⁻¹ * n) * γ₀ with hgdef
  have hgd : g = ν' * d * ν⁻¹ := by
    calc g = γ₀⁻¹ * n'⁻¹ * (n * γ₀ * ν * c) * c⁻¹ * ν⁻¹ := by rw [hgdef]; group
      _ = γ₀⁻¹ * n'⁻¹ * (n' * γ₀ * ν' * c') * c⁻¹ * ν⁻¹ := by rw [he]
      _ = ν' * d * ν⁻¹ := by rw [hddef]; group
  have hnil : ((g : (VS D).V →ₗ[D.host.E] (VS D).V) - 1) ^ (2 * D.R.rS + 1) = 0 :=
    conj_nilp (Formalism.L2.SG.Pf.nlamPf_mul (Formalism.L2.SG.Pf.nlamPf_inv hn') hn) γ₀
  have hdP := perp_maps F0' hd hdfix
  have hdX : ∀ y ∈ F0'.X, d y ∈ F0'.X := fun y hy => by rw [fix_X F0' hdfix y hy]; exact hy
  have hνi := Formalism.L2.SG.Pf.nlamPf_inv hν
  have hgapp : ∀ y, g y = ν' (d (ν⁻¹ y)) := fun y => by rw [hgd]; rfl
  have hgP : ∀ y ∈ perpS (VS D) F0'.X, g y ∈ perpS (VS D) F0'.X := fun y hy => by
    rw [hgapp]; exact nlam_P hν' _ (hdP _ (nlam_P hνi _ hy))
  have hgX : ∀ y ∈ F0'.X, g y ∈ F0'.X := fun y hy => by
    rw [hgapp]; exact nlam_X hν' _ (hdX _ (nlam_X hνi _ hy))

  have hgdX : ∀ y ∈ perpS (VS D) F0'.X, g y - d y ∈ F0'.X := by
    intro y hy
    have ha := nlam_triv hνi y hy
    have e1 : d (ν⁻¹ y) = d y + (ν⁻¹ y - y) := by
      have : ν⁻¹ y = y + (ν⁻¹ y - y) := by abel
      conv_lhs => rw [this]
      rw [map_add, fix_X F0' hdfix _ ha]
    have e2 : g y - d y = (ν' (d y) - d y) + ν' (ν⁻¹ y - y) := by
      rw [hgapp, e1, map_add]; abel
    rw [e2]
    exact add_mem (nlam_triv hν' _ (hdP y hy)) (nlam_X hν' _ ha)
  have hg1P : ∀ y ∈ perpS (VS D) F0'.X, ((g : (VS D).V →ₗ[D.host.E] (VS D).V) - 1) y ∈ perpS (VS D) F0'.X :=
    fun y hy => by
      rw [LinearMap.sub_apply, Module.End.one_apply]; exact sub_mem (hgP y hy) hy
  have hg1X : ∀ y ∈ F0'.X, ((g : (VS D).V →ₗ[D.host.E] (VS D).V) - 1) y ∈ F0'.X := fun y hy => by
    rw [LinearMap.sub_apply, Module.End.one_apply]; exact sub_mem (hgX y hy) hy
  set TD := indL F0' (d : (VS D).V →ₗ[D.host.E] (VS D).V) hdP hdX with hTD
  have hTD1 : TD - 1 = indL F0' ((g : (VS D).V →ₗ[D.host.E] (VS D).V) - 1) hg1P hg1X := by
    refine LinearMap.ext fun w => ?_
    induction w using Submodule.Quotient.induction_on with
    | H x =>
      rw [LinearMap.sub_apply, Module.End.one_apply, hTD, indL_mk, indL_mk, ← Submodule.Quotient.mk_sub,
        Submodule.Quotient.eq]
      show (d x - x) - (g x - x) ∈ F0'.X
      have : (d x - x) - (g x - x) = -(g x - d x) := by abel
      rw [this]
      exact neg_mem (hgdX x x.2)
  have hTDnil : (TD - 1) ^ (2 * D.R.rS + 1) = 0 := by
    rw [hTD1, indL_pow]
    exact indL_zero _ _ _ (fun y => by rw [hnil]; rfl)

  have hdpow : ∀ i : ℕ, d ^ i ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧ (∀ a, (d ^ i) (F0'.fvec a) = F0'.fvec a) ∧
      Formalism.HermitianLatticesTheory.gmap (d ^ i) Λ₀ = Λ₀ := by
    intro i
    induction i with
    | zero => exact ⟨Subgroup.one_mem _, fun a => rfl, Formalism.L2.SG.Pf.gmap_one_sat _⟩
    | succ i ih =>
      refine ⟨by rw [pow_succ]; exact Subgroup.mul_mem _ ih.1 hd, fun a => ?_, ?_⟩
      · rw [pow_succ, LinearEquiv.mul_apply, hdfix, ih.2.1]
      · rw [pow_succ, Formalism.L2.SG.Pf.gmap_mul_sat, hdg, ih.2.2]
  have hTDpow : ∀ (i : ℕ) (x : perpS (VS D) F0'.X), (TD ^ i) (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨(d ^ i) x, perp_maps F0' (hdpow i).1 (hdpow i).2.1 _ x.2⟩ := by
    intro i
    induction i with
    | zero => intro x; rfl
    | succ i ih =>
      intro x
      rw [pow_succ, Module.End.mul_apply, hTD, indL_mk, ← hTD, ih]
      rfl
  have hmem : ∀ i : ℕ, ⇑(TD ^ i) ∈ autLz D F0' Λ₀ := fun i =>
    ⟨d ^ i, stabF_of_fix F0' (hdpow i).1 (hdpow i).2.1, (hdpow i).2.2, fun x _ => hTDpow i x⟩
  obtain ⟨i, j, hij, hφ⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun i : ℕ => (⟨⇑(TD ^ i), hmem i⟩ : autLz D F0' Λ₀))
  have hpow : TD ^ i = TD ^ j := LinearMap.coe_injective (congrArg Subtype.val hφ)
  have hunit : IsUnit TD := by
    have hdiP := perp_maps F0' (Subgroup.inv_mem _ hd) (inv_fix F0' hdfix)
    have hdiX : ∀ y ∈ F0'.X, d⁻¹ y ∈ F0'.X := fun y hy => by rw [fix_X F0' (inv_fix F0' hdfix) y hy]; exact hy
    refine ⟨⟨TD, indL F0' ((d⁻¹ : (VS D).V ≃ₗ[D.host.E] (VS D).V) : (VS D).V →ₗ[D.host.E] (VS D).V) hdiP hdiX,
      ?_, ?_⟩, rfl⟩ <;>
    · refine LinearMap.ext fun w => ?_
      induction w using Submodule.Quotient.induction_on with
      | H x =>
        rw [Module.End.mul_apply, hTD, indL_mk, indL_mk, Module.End.one_apply]
        congr 1
        apply Subtype.ext
        simp [LinearEquiv.coe_inv]
  have hfin : ∃ k, 0 < k ∧ TD ^ k = 1 := by
    rcases lt_or_gt_of_ne hij with h | h
    · refine ⟨j - i, by omega, ?_⟩
      have e : TD ^ i * TD ^ (j - i) = TD ^ i * 1 := by rw [← pow_add, Nat.add_sub_cancel' h.le, mul_one, hpow]
      exact (hunit.pow i).mul_left_cancel e
    · refine ⟨i - j, by omega, ?_⟩
      have e : TD ^ j * TD ^ (i - j) = TD ^ j * 1 := by rw [← pow_add, Nat.add_sub_cancel' h.le, mul_one, hpow]
      exact (hunit.pow j).mul_left_cancel e
  obtain ⟨k, hk, hk1⟩ := hfin
  have hTD : TD = 1 := unip_fin TD hk hk1 hTDnil
  intro y hy
  have hcy := perp_maps F0' hc hfix y hy
  have e := congrArg (fun A : Module.End D.host.E (WbQ D F0') => A (Submodule.Quotient.mk ⟨c y, hcy⟩)) hTD
  simp only [Module.End.one_apply] at e
  rw [indL_mk, Submodule.Quotient.eq] at e
  have e3 : c' y = (d : (VS D).V →ₗ[D.host.E] (VS D).V) (c y) := by
    rw [hddef]; simp [LinearEquiv.coe_inv]
  have h3 : c' y - c y ∈ F0'.X := by
    have := e
    simp only [Submodule.mem_comap, Submodule.coe_subtype, AddSubgroupClass.coe_sub] at this
    rw [e3]; exact this
  rw [← neg_sub]
  exact neg_mem h3

end WD

end Formalism.L2.SG.Pf.FibreCounting
